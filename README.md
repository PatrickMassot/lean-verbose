# Lean verbose

This project provides tactics for
[Lean](https://leanprover-community.github.io/) in a very controlled
natural language. The original version of those tactics were written in
French for teaching purposes at 
[Université Paris-Saclay](https://www.universite-paris-saclay.fr/) in
Orsay. The goal is not to make Lean code easier to write, the goal is to
make Lean code easier to transfer to a traditional paper proof.

The best way to have a quick look is to read the 
[sample file](https://github.com/PatrickMassot/lean-verbose/blob/master/test/sample.lean).
More "documentation" can be found in the other files in the test folder.

The current state of this project is a pretty rough translation of the
French version. Feel free to propose improvements.

If you use those tactics for teaching, I'd be very interested to hear about it, and would gladly add your name and the name of your university in this file.

## How to install?

You can add these tactics to your Lean project using 
```
leanpkg add https://github.com/PatrickMassot/lean-verbose.git
```
and then access the tactics using `import verbose_tactics`.

Note: in my teaching I use a modified version of the 
[Lean VSCode extension](https://github.com/leanprover/vscode-lean/)
to get syntax highlighting for all the keywords added by those tactics.
This is extremely useful because there are lots of them and it's easy to mistype them. If you know a less hackish way to get such highlighting, I'd be extremely interested to know.

## How does it work?

These tactics (ab)use the standard Lean 3 meta-programming framework. 
For each "sentence" in a proof, the first word is the tactic name. Later 
words are all registered as extra tokens, see the list at the
beginning of the `parsers.lean` file. Hence those words become unavailable 
for anything else. In particular, trying to mix regular Lean/mathlib tactics
with verbose tactics is unlikely to work (for instance `apply` becomes
a reserved token as soon as you want verbose tactics). This is also why the
word `a` does not appear in those "sentences": it is too useful as a variable
name.

Because the first word in any sentence is the tactic name and there are many
sentences starting with the same word, we have to do a lot of dispatching
when parsing. The unfortunate side effect is that error messages can be very
confusing. If you misspell a word, the parser will give up on the relevant
branch, try something else, and issue an error message only when the last branch
will have been tried. If that last branch has nothing to do with what you had
in mind then the error message will be confusing. 

The same kind of issue also appears (but in somewhat less severe form) after
parsing. Some tactics try several things and only the last try rises an error
message.

## How to translate to another language?

You can fork this project and mostly edit `parsers.lean`, as well as some error
message in `verbose_tactics.lean`. This is assuming you keep the same grouping
of sentences by first words. Otherwise you will also need to edit `types.lean`
which prepares the inductive types which mediate between the parsers and
tactics, and then propagate those changes. Note however that grouping is not
random, so you probably want to keep it anyway. If you do translate these tactics into another language then I'd be very interested to learn about it.
