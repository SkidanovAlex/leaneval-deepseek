/-
# ZeroFreeTables/P3/Imports

Single import surface for the `P₃` engine: the Commons material that the engine's
analytic lemmas need (the partial-fraction expansion of `Λ'/Λ`, HB Lemma 3.1, the
zero-counting and inverse-square zero-sum bounds for the completed L-function).
-/
import Submission.Commons.NumberTheory.Linnik.completedL_pf_identity_rect
import Submission.Commons.NumberTheory.Linnik.completedL_zeroCount
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.Linnik.zeroSum_invSq_bound
import Submission.Commons.NumberTheory.Linnik.nearSum_bound
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.P3.Defs
import Submission.Work.ZeroFreeTables.P3.pfCofactor
