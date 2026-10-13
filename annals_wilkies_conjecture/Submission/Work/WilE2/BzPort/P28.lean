/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.Algebra.Polynomial.le_natDegree_of_eventually_le_eval` (piece 0).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Data.Sym.NatCard
import Mathlib.GroupTheory.CosetCover
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Submission.Work.WilE2.BzPort.P27

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.Algebra.Polynomial.le_natDegree_of_eventually_le_eval ====
section

namespace Commons.Algebra.Polynomial

theorem le_natDegree_of_eventually_le_eval {P : Polynomial ℚ} {k : ℕ} {C : ℚ} {N : ℕ}
    (hC : 0 < C) (h : ∀ n : ℕ, N ≤ n → C * (n : ℚ) ^ k ≤ P.eval (n : ℚ)) :
    k ≤ P.natDegree := by
  by_contra hcon
  rw [not_le] at hcon
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hcon
  set Q : Polynomial ℚ := Polynomial.X ^ k with hQ
  have hQeval : ∀ x : ℚ, Q.eval x = x ^ k := by
    intro x; rw [hQ, Polynomial.eval_pow, Polynomial.eval_X]
  have hdeg : P.degree < Q.degree := by
    rw [hQ, Polynomial.degree_X_pow]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (WithBot.coe_lt_coe.mpr hcon)
  have htend : Filter.Tendsto (fun x : ℚ => P.eval x / Q.eval x) Filter.atTop (nhds 0) :=
    Polynomial.div_tendsto_atTop_zero_of_degree_lt P Q hdeg
  have hevQ : ∀ᶠ x : ℚ in Filter.atTop, P.eval x / Q.eval x < C :=
    htend.eventually (eventually_lt_nhds hC)
  have hevN : ∀ᶠ n : ℕ in Filter.atTop, P.eval (n : ℚ) / Q.eval (n : ℚ) < C :=
    Filter.Eventually.natCast_atTop hevQ
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hevN
  set n : ℕ := max M (max N 1) with hn
  have hnM : M ≤ n := le_max_left _ _
  have hnN : N ≤ n := le_trans (le_max_left N 1) (le_max_right M (max N 1))
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) (le_max_right M (max N 1))
  have hltC : P.eval (n : ℚ) / (n : ℚ) ^ k < C := by
    simpa only [hQeval] using hM n hnM
  have hpos : (0 : ℚ) < (n : ℚ) ^ k :=
    pow_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)) k
  have hle : C ≤ P.eval (n : ℚ) / (n : ℚ) ^ k := by
    rw [le_div_iff₀ hpos]
    exact h n hnN
  linarith

end Commons.Algebra.Polynomial
end


