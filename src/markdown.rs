use std::borrow::Cow::Owned;
use std::collections::HashMap;

use pulldown_cmark as cmark;
use self::cmark::{Parser, Event, Tag};
use regex::Regex;
use syntect::dumps::from_binary;
use syntect::easy::HighlightLines;
use syntect::parsing::SyntaxSet;
use syntect::highlighting::ThemeSet;
use syntect::html::{start_coloured_html_snippet, styles_to_coloured_html, IncludeBackground};

use config::Config;


// We need to put those in a struct to impl Send and sync
pub struct Setup {
    syntax_set: SyntaxSet,
    pub theme_set: ThemeSet,
}

unsafe impl Send for Setup {}
unsafe impl Sync for Setup {}

lazy_static!{
    static ref SIMPLE_SHORTCODE_RE: Regex = Regex::new(r#"\{\{\s+([[:alnum:]]+?)\(([[:alnum:]]+?="?.+?"?)\)\s+\}\}"#).unwrap();
    pub static ref SETUP: Setup = Setup {
        syntax_set: SyntaxSet::load_defaults_newlines(),
        theme_set: from_binary(include_bytes!("../sublime_themes/all.themedump"))
    };
}

#[derive(Debug)]
struct ShortCode {
    name: String,
    args: HashMap<String, String>,
    body: Option<String>,
}

impl ShortCode {
    pub fn new(name: &str, args: HashMap<String, String>) -> ShortCode {
        ShortCode {
            name: name.to_string(),
            args: args,
            body: None,
        }
    }
}

/// Parse a shortcode without a body
fn parse_simple_shortcode<'a>(input: &'a str) -> (String, HashMap<String, String>) {
    let mut args = HashMap::new();
    let caps = SIMPLE_SHORTCODE_RE.captures(input).unwrap();
    // caps[0] is the full match
    let name = &caps[1];
    let arg_list = &caps[2];
    println!("{:?}", arg_list);
    for arg in arg_list.split(',') {
        let bits = arg.split('=').collect::<Vec<_>>();
        println!("{:?}", bits);
        args.insert(bits[0].trim().to_string(), bits[1].replace("\"", ""));
    }

    (name.to_string(), args)
}

/// A parser that can do both code highlighting and shortcode expansion
struct AugmentedParser<'a> {
    /// The CommonMark parser itself
    parser: Parser<'a>,
    /// The block we're currently highlighting
    highlighter: Option<HighlightLines<'a>>,
    /// The theme used, NA if code highlighting is not enabled
    theme: &'a str,
    /// The shortcode currently being rendered
    shortcode: Option<&'a ShortCode>,
}

impl<'a> AugmentedParser<'a> {
    pub fn new(parser: Parser<'a>, theme: &'a str) -> AugmentedParser<'a> {
        AugmentedParser {
            highlighter: None,
            shortcode: None,
            parser: parser,
            theme: theme,
        }
    }

    #[inline]
    fn should_highlight(&self) -> bool {
        self.theme != "NA"
    }
}

impl<'a> Iterator for AugmentedParser<'a> {
    type Item = Event<'a>;

    fn next(&mut self) -> Option<Event<'a>> {
        // Not using pattern matching to reduce indentation levels
        let next_opt = self.parser.next();
        if next_opt.is_none() {
            return None;
        }

        let item = next_opt.unwrap();
        // Below we just look for the start of a code block and highlight everything
        // until we see the end of a code block.
        // Everything else happens as normal in pulldown_cmark
        match item {
            Event::Text(text) => {
                // if we are in the middle of a code block
                if let Some(ref mut highlighter) = self.highlighter {
                    let highlighted = &highlighter.highlight(&text);
                    let html = styles_to_coloured_html(highlighted, IncludeBackground::Yes);
                    return Some(Event::Html(Owned(html)));
                }

                // Shortcode without body
                if text.starts_with("{{") && text.ends_with("}}") {
                    if SIMPLE_SHORTCODE_RE.is_match(&text) {

                    }
                    // non-matching will be returned normally below
                }
                Some(Event::Text(text))
            },
            Event::Start(Tag::CodeBlock(ref info)) => {
                if !self.should_highlight() {
                    println!("{}", info);
                    return Some(Event::Html(Owned("<pre><code>".to_owned())))
                }
                let theme = &SETUP.theme_set.themes[self.theme];
                let syntax = info
                    .split(' ')
                    .next()
                    .and_then(|lang| SETUP.syntax_set.find_syntax_by_token(lang))
                    .unwrap_or_else(|| SETUP.syntax_set.find_syntax_plain_text());
                self.highlighter = Some(
                    HighlightLines::new(syntax, theme)
                );
                let snippet = start_coloured_html_snippet(theme);
                Some(Event::Html(Owned(snippet)))
            },
            Event::End(Tag::CodeBlock(_)) => {
                if !self.should_highlight() {
                    return Some(Event::Html(Owned("</code></pre>\n".to_owned())))
                }
                // reset highlight and close the code block
                self.highlighter = None;
                Some(Event::Html(Owned("</pre>".to_owned())))
            },
            _ => {
                Some(item)
            }
        }

    }
}

pub fn markdown_to_html(content: &str, config: &Config) -> String {
    // We try to be smart about highlighting code as it can be time-consuming
    // If the global config disables it, then we do nothing. However,
    // if we see a code block in the content, we assume that this page needs
    // to be highlighted. It could potentially have false positive if the content
    // has ``` in it but that seems kind of unlikely
    let should_highlight = if config.highlight_code.unwrap() {
        content.contains("```")
    } else {
        false
    };


    let mut html = String::new();
    let highlight_theme = if should_highlight {
        config.highlight_theme.clone().unwrap()
    } else {
        "NA".to_string()
    };

    let parser = AugmentedParser::new(Parser::new(content), &highlight_theme);
    cmark::html::push_html(&mut html, parser);
    html
}


#[cfg(test)]
mod tests {
    use config::Config;
    use super::{markdown_to_html, parse_simple_shortcode};

    #[test]
    fn test_parse_simple_shortcode_one_arg() {
        let (name, args) = parse_simple_shortcode(r#"{{ youtube(id="w7Ft2ymGmfc") }}"#);
        assert_eq!(name, "youtube");
        assert_eq!(args["id"], "w7Ft2ymGmfc");
    }

    #[test]
    fn test_parse_simple_shortcode_several_arg() {
        let (name, args) = parse_simple_shortcode(r#"{{ youtube(id="w7Ft2ymGmfc", autoplay=true) }}"#);
        assert_eq!(name, "youtube");
        assert_eq!(args["id"], "w7Ft2ymGmfc");
        assert_eq!(args["autoplay"], "true");
    }

    #[test]
    fn test_markdown_to_html_simple() {
        let res = markdown_to_html("# hello", &Config::default());
        assert_eq!(res, "<h1>hello</h1>\n");
    }

    #[test]
    fn test_markdown_to_html_code_block_highlighting_off() {
        let mut config = Config::default();
        config.highlight_code = Some(false);
        let res = markdown_to_html("```\n$ gutenberg server\n```", &config);
        assert_eq!(
            res,
            "<pre><code>$ gutenberg server\n</code></pre>\n"
        );
    }

    #[test]
    fn test_markdown_to_html_code_block_no_lang() {
        let res = markdown_to_html("```\n$ gutenberg server\n$ ping\n```", &Config::default());
        assert_eq!(
            res,
            "<pre style=\"background-color:#2b303b\">\n<span style=\"background-color:#2b303b;color:#c0c5ce;\">$ gutenberg server\n</span><span style=\"background-color:#2b303b;color:#c0c5ce;\">$ ping\n</span></pre>"
        );
    }

    #[test]
    fn test_markdown_to_html_code_block_with_lang() {
        let res = markdown_to_html("```python\nlist.append(1)\n```", &Config::default());
        assert_eq!(
            res,
            "<pre style=\"background-color:#2b303b\">\n<span style=\"background-color:#2b303b;color:#c0c5ce;\">list</span><span style=\"background-color:#2b303b;color:#c0c5ce;\">.</span><span style=\"background-color:#2b303b;color:#bf616a;\">append</span><span style=\"background-color:#2b303b;color:#c0c5ce;\">(</span><span style=\"background-color:#2b303b;color:#d08770;\">1</span><span style=\"background-color:#2b303b;color:#c0c5ce;\">)</span><span style=\"background-color:#2b303b;color:#c0c5ce;\">\n</span></pre>"
        );
    }

    #[test]
    fn test_markdown_to_html_code_block_with_unknown_lang() {
        let res = markdown_to_html("```yolo\nlist.append(1)\n```", &Config::default());
        // defaults to plain text
        assert_eq!(
            res,
            "<pre style=\"background-color:#2b303b\">\n<span style=\"background-color:#2b303b;color:#c0c5ce;\">list.append(1)\n</span></pre>"
        );
    }

    #[test]
    fn test_markdown_to_html_shortcode() {
        let res = markdown_to_html(r#"
Hello
{{ youtube(id="w7Ft2ymGmfc") }}
        "#, &Config::default());
        // defaults to plain text
        assert_eq!(
            res,
            ""
        );
    }
}
