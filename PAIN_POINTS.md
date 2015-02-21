This document contains the pain points that I have identified whilst using HOL. It's mostly either things that I now see as obvious that I haven't identified using the docs (i.e. they aren't in HOL-interaction or might be buried deep in the tutorial).

1. THEN applies the second tactic to *all* of the subgoals. This makes things much simpler - if for example we have a goal which after RW_TAC std_ss [] has 10 subgoals of which eight can be solved with FULL_SIMP_TAC std_ss [] then we can write
    RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [] THEN1 SOME_TACTICS THEN1 SOME_TACTICS2
to solve all but the eight goals, and not be forced to do
    RW_TAC std_ss [] THENL [FULL_SIMP_TAC std_ss [], FULL_SIMP_TAC std_ss [], FULL_SIMP_TAC std_ss [], FULL_SIMP_TAC std_ss [], SOME_TACTICS, FULL_SIMP_TAC std_ss [], FULL_SIMP_TAC std_ss [], cont]
This has really saved me a lot of time since I've done that - my proofs go about 90% faster because it gives a much greater intuition as to whether a proof is going to work, almost immediately. Before, I had no idea whether I'd immediately hit a brick wall.

2. When you open HOL, it creates a .HOLMK directory. This is usually fine, and you never notice it, but if you're on (say) the Emacs scratch page, or are in some directory where you have no permission to create a directory, you get an error which is somewhat unclear and initially nondeterministic.

3. The HOL manual and HOL-interaction indicate that it's acceptable to use mosml with HOL. It's not. It's really slow.

4. When building HOL on OS X with Poly and Homebrew, there's a quirk since poly requires a custom compiler flag. This could be put in the build instructions explicitly?

5. A link to Tactic in HOL-interaction would be really useful. I've only just found it.

6. Hol-interaction gives a few basic tactics. It would be useful for there to be some examples of goal manipulation - uses of Q.SPECL to avoid expanding variables, and really just a list of things that are found useful in everyday life. Almost all of my pain has been with manipulating theorems, not actually the core proving of them.

7. I just discovered `Q.EXISTS_TAC`. I'm actually baffled that I got so far in without working out what Q is or does. It works much better than vanilla `EXISTS_TAC` (in particular it doesn't require type to be provided. This is another thing I only discovered today!) That *really* needs to be in HOL-interaction. I've never successfully used Q until today - so much garbage!
