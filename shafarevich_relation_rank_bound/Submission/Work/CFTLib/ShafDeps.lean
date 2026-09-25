import ChallengeDeps
import Submission.CFTLib.Interfaces

/-!
# Shared imports for the `Work.CFTLib` lemmas

This module is a bare re-export of the trusted definitions the `Work.CFTLib` lemmas talk about:

* `ChallengeDeps` — the definitions of the problem statement (`IsEverywhereUnramified`,
  `maximalUnramifiedProPF`, `MaxUnramifiedProPGaloisGroup`, `generatorRank`, `relationRank`,
  `H2Finite`, `trivialZModpRep`);
* `Submission.CFTLib.Interfaces` — the class-field-theory hypotheses `CFTLib.RelShafBound`,
  `CFTLib.UnramifiedAbelianDegreeLe`, and the predicate `CFTLib.IsUnramified`.

It exists so that delegated lemmas can `depends_on ["CFTLib/ShafDeps"]` and have the vocabulary of
the problem available.
-/
