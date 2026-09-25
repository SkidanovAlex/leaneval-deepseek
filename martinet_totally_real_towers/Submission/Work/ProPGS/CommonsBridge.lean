/-
Bridge module: everything the `Work.ProPGS` chapter needs from outside its own directory, in one
import.  Not part of the mathematical content -- it exists so that the dependencies of the area are
one module.
-/
import Submission.Commons.GroupTheory.ProPGroup.golod_shafarevich_presentation_card_lt
import Submission.Work.HopfGaschutz.All
import Submission.Work.RelatorRank.CohomologyH2
import Submission.Work.ProPDeficiency.Basic
import Submission.GroupTheory.GolodShafarevichFromCommons
import Submission.GroupTheory.GolodShafarevichCriterion
import Submission.Work.ShafarevichKoch.Gaschutz.exists_words_spanning_of_relFrattiniIn_card
import Submission.Work.ShafarevichKoch.Gaschutz.exists_mulEquiv_pi_zmodTwo_of_natCard_le
import Submission.Work.ShafarevichKoch.Gaschutz.natCard_relFrattiniQuotient_eq_two_pow_of_spanning
