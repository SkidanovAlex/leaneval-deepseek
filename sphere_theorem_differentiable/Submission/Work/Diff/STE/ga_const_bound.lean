import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.GardingConst
import Submission.Work.Diff.STE.garding_estimate
import Submission.Work.Diff.STE.garding_base
import Submission.Work.Diff.STE.elliptic_lower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Gårding estimate with the explicit, uniform constant

`Work.Diff.STE.garding_estimate` gives the elliptic Gårding estimate with an *existential*
constant `C`.  Here we run the same computation with the constant made explicit: the constant
produced by that proof is exactly

  `gardingConst (card ι) lam K₁ = max K₁ 0 * n² * (max K₁ 0 * n + 1) / (2 lam)`,  `n = card ι`,

which is recorded in `Submission/Work/Diff/STE/GardingConst.lean`.  Making it explicit is what
allows the estimate to be *uniform* in the coefficient matrix, as needed by the Layer A9
multi-index estimates.

Note that the estimate is not an immediate consequence of `garding_estimate` (whose witness `C`
is hidden behind an existential); the argument is re-run verbatim with the constant fixed.
-/

namespace Work.Diff.STE

open MeasureTheory BigOperators

theorem ga_const_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → (ι → ℝ) → ℝ)
    (hA : ∀ c d, ContDiff ℝ (⊤ : ℕ∞) (A c d))
    (hAper : ∀ c d, Work.Diff.STE.Periodic1 (A c d))
    (hsym : ∀ c d x, A c d x = A d c x)
    (lam : ℝ) (hlam : 0 < lam)
    (hpos : ∀ x (ξ : ι → ℝ), lam * ∑ i, (ξ i) ^ 2 ≤ ∑ c, ∑ d, A c d x * ξ c * ξ d)
    (K₁ : ℝ) (hK₁ : ∀ c d i x, |Work.Diff.STE.pdR i (A c d) x| ≤ K₁) :
    ∀ u : (ι → ℝ) → ℂ, ContDiff ℝ 2 u → Work.Diff.STE.Periodic1 u →
      Work.Diff.STE.L2re
          (fun x => ∑ c, ∑ d, A c d x * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) x) u
        ≤ -((lam / 2) * ∑ i,
              ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pd i u x‖ ^ 2)
          + Work.Diff.STE.gardingConst (Fintype.card ι) lam K₁
            * ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖u x‖ ^ 2 := by
  have hA1 : ∀ c d, ContDiff ℝ 1 (A c d) := fun c d => (hA c d).of_le (by simp)
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hnn : 0 ≤ n := by rw [hn]; exact Nat.cast_nonneg _
  set K : ℝ := max K₁ 0 with hKdef
  have hK : 0 ≤ K := by rw [hKdef]; exact le_max_right _ _
  have hK' : ∀ c d i x, |pdR i (A c d) x| ≤ K := by
    intro c d i x; rw [hKdef]; exact le_trans (hK₁ c d i x) (le_max_left _ _)
  set D : ℝ := K * n + 1 with hDdef
  have hD : 0 < D := by rw [hDdef]; nlinarith [hK, hnn]
  set ε : ℝ := lam / D with hεdef
  have hε : 0 < ε := by rw [hεdef]; exact div_pos hlam hD
  set C : ℝ := K * n ^ 2 * D / (2 * lam) with hCdef
  have hCval : gardingConst (Fintype.card ι) lam K₁ = C := by
    rw [gardingConst, ← hn, ← hKdef, ← hDdef]
  intro u hu hup
  rw [hCval]
  have hop := ga_operator_identity A hA1 (fun c d => hAper c d) u hu hup
  have hell := elliptic_lower A hA lam hpos u hu
  have hfo := ga_first_order_bound A hA1 K hK hK' u hu ε hε
  set S : ℝ := ∑ i, ∫ x in unitCube, ‖pd i u x‖ ^ 2 with hS
  set T : ℝ := ∫ x in unitCube, ‖u x‖ ^ 2 with hT
  set J1 : ℝ := ∑ c : ι, ∑ d : ι,
    ∫ x in unitCube, (pdR c (A c d) x) * Complex.re (pd d u x * star (u x)) with hJ1
  set J2 : ℝ := ∑ c : ι, ∑ d : ι,
    ∫ x in unitCube, (A c d x) * Complex.re (pd d u x * star (pd c u x)) with hJ2
  rw [← hn] at hfo
  have hSnn : 0 ≤ S := by
    rw [hS]; exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => by positivity))
  have hTnn : 0 ≤ T := by
    rw [hT]; exact integral_nonneg (fun x => by positivity)
  have ha_eq : K * n * ε / 2 = lam / 2 - lam / (2 * D) := by
    have hDne : D ≠ 0 := ne_of_gt hD
    rw [hεdef]
    field_simp
    ring
  have ha_le : K * n * ε / 2 ≤ lam / 2 := by
    rw [ha_eq]
    have h0 : 0 ≤ lam / (2 * D) := div_nonneg (le_of_lt hlam) (by linarith)
    linarith
  have hb_eq : K * n ^ 2 / (2 * ε) = C := by
    have hDne : D ≠ 0 := ne_of_gt hD
    have hlne : lam ≠ 0 := ne_of_gt hlam
    rw [hεdef, hCdef]
    field_simp
  have hb_le : K * n ^ 2 / (2 * ε) ≤ C := le_of_eq hb_eq
  have hJ1' : -(lam / 2) * S - C * T ≤ J1 := by
    have ha' : -(lam / 2) * S ≤ -(K * n * ε / 2) * S :=
      mul_le_mul_of_nonneg_right (neg_le_neg ha_le) hSnn
    have hb' : -C * T ≤ -(K * n ^ 2 / (2 * ε)) * T :=
      mul_le_mul_of_nonneg_right (neg_le_neg hb_le) hTnn
    linarith [hfo, ha', hb']
  rw [hop]
  linarith [hJ1', hell]

end Work.Diff.STE
