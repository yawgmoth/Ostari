# A macro system and runtime environment to write actions in Baltag's Dynamic Epistemic Logic

## Synopsis

This repository contains a runtime system that can execute actions in Baltag's variant of Dynamic Epistemic Logic[1]. Because writing the actions in this logic directly is cumbersome for any non-trivial application,
macros are provided that make writing them much easier. For more details see our paper about the system[2].

## Usage

You will need the Haskell compiler ghc to compile the system (I recommend Haskell Platform[3] because it comes with cabal to install packages you might need). 

Dependencies: mtl, text, parsec, split, and parallel

Compile using:

```ghc --make -rtsopts -XFlexibleContexts rungame.hs```

The `-rtsopts` option will allow you to provide GHC runtime options to the executable. You should end up with an executable called rungame.exe (on Windows) or just rungame (*NIX systems). Run with

```rungame.exe <inputfile>```
or
```./rungame <inputfile>```

A few demo input files are provided, as described below. If you run out of stack space, pass e.g. `+RTS -K 100M` as additional parameters to increase the stack to 100 MB.

## Examples

* [logicians.cfg](logicians.cfg) contains a folk joke encoded as DEL actions. The joke goes as follows: Three logicians walk into a bar. The bar tender asks them: "Do all of you want a beer?", to which the first logician answers "I don't know".  Then the second logicians says "I don't know", after which the third logician says "yes". The encoding of this joke can be used as an explanation: If the first logician did not want a beer, they would know that not all of them wanted one, therefore they must want a beer. Likewise for the second logician. The third logician can therefore take the two answers as confirmations that the other two each want a beer, and since the third logician also wants one, they can answer in the affirmative. 

* [detective.cfg](detective.cfg) contains a small domain for a detective story, in which the murderer (Moriarty) wants Sherlock to believe that Watson is the murderer. It makes use of the planning capabilities of the system to find a story in 
which Moriarty achieves this goal. The application of our system to story planning is described in more detail in an upcoming paper [4]

* [minihanabi.cfg](minihanabi.cfg) contains some actions inspired by the cooperative card game Hanabi, in which players can not see their own hands and have to give hints to the other players about the cards in their hand. There is currently a known issue with the initial state generated for this example, which may result in misleading results. 

* [onuw.cfg](onuw.cfg) is an encoding of some actions from the board game One Night Ultimate Werewolf, which is a social deduction game in which some players are secretly assigned Werewolf cards and the other players, belonging to a village, have to deduce which players are Werewolves. This is mostly intended to demonstrate the syntax and other features of Ostari, rather than as a complete or completely correct encoding of the game.

## License

See [the license file](CRAPL-LICENSE.txt). The TL;DR is, in the words of Donald E. Knuth: "Beware of bugs in the above code; I have only proved it correct, not tried it."

## References

[1] Baltag, Alexandru. "A Logic for Suspicious Players: Epistemic Actions and Belief–Updates in Games." Bulletin of Economic Research 54.1 (2002): 1-45. [PDF](http://www.vub.ac.be/CLWF/SS/BER.pdf)

[2] Markus Eger and Chris Martens. "Practical specification of belief manipulation in games." Proceedings of the 13th AAAI International Conference on Artificial Intelligence and Interactive Digital Entertainment (2017). (PDF coming soon)

[3] [Haskell Platform](https://www.haskell.org/platform)

[4] Markus Eger and Chris Martens. "Character beliefs in story generation." Working Notes of the AIIDE 2017 Workshop on Intelligent Narrative Technologies (2017). (PDF coming soon)