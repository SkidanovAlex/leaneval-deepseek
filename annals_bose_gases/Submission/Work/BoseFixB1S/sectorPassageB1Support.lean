import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.rPsiB_nonneg
import Submission.Work.BoseFixB1B.RsbSide_sq_le_holds
import Submission.Work.BoseFixB1B.integratedOfPointwise
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.sectorPassageB1Support` — support of the smooth box cutoff

`chiSmallB M ℓ d u z ≠ 0` forces `z ∈ dlBox ℓ d u` (the product cutoff is supported in the small
box): the `ℓ`-scale factor `chiScale ℓ = χ(·/ℓ)` (a radial bump) confines `z` to `acube ℓ`, and
the `ℓd`-scale cosine factor confines `z − (ℓd)•u` to `acube (ℓd)`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1S

set_option autoImplicit false
set_option linter.unusedVariables false

theorem chiSmallB_mem_dlBox_B1S {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u z : EuclideanSpace ℝ (Fin 3))
    (hz : Submission.BoseGases.chiSmallB M ℓ d u z ≠ 0) :
    z ∈ Submission.BoseGases.dlBox ℓ d u := by
  rw [Submission.BoseGases.mem_dlBox_iff]
  refine ⟨?_, ?_⟩
  · rw [Submission.BoseGases.mem_acube_iff]
    intro j
    have h := Submission.BoseGases.chiSmallB_support_big_box hM hℓ hz j
    rw [abs_le] at h
    exact ⟨by linarith [h.1], h.2⟩
  · rw [Submission.BoseGases.mem_acube_iff]
    intro j
    have h := Submission.BoseGases.chiSmallB_support_small_box hM hz j
    have hld : 0 < ℓ * d := mul_pos hℓ hd
    have hco : ((ℓ * d)⁻¹ • z - u).ofLp j = (z - (ℓ * d) • u).ofLp j / (ℓ * d) := by
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp
    rw [hco] at h
    rw [abs_div, abs_of_pos hld, div_le_iff₀ hld, abs_le] at h
    exact ⟨by nlinarith [h.1], by nlinarith [h.2]⟩

/-- The localised two-body kernel `wSmallPair M ℓ d u h` vanishes as soon as either argument
leaves the small box `dlBox ℓ d u`. -/
theorem wSmallPair_eq_zero_of_notMem_B1S {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) (h : EuclideanSpace ℝ (Fin 3) → ℝ)
    {x y : EuclideanSpace ℝ (Fin 3)} (hx : x ∉ Submission.BoseGases.dlBox ℓ d u) :
    Submission.BoseGases.wSmallPair M ℓ d u h x y = 0 := by
  have hxz : Submission.BoseGases.chiSmallB M ℓ d u x = 0 := by
    by_contra hne
    exact hx (chiSmallB_mem_dlBox_B1S hM hℓ hd u x hne)
  simp only [Submission.BoseGases.wSmallPair, hxz, zero_mul]

/-- `χ_{B(u)}(z) ≤ chiSupAbs · chiSmallDecay M =: ν` (the universal sup bound). -/
lemma chiSmallB_le_sup_B1S {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    (u z : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.chiSmallB M ℓ d u z
      ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
  have hb2 : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z - u)
      ≤ Submission.BoseGases.chiSmallDecay M := by
    have hb' := Submission.BoseGases.chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • z - u)
    rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at hb'
  calc Submission.BoseGases.chiSmallB M ℓ d u z
      ≤ |Submission.BoseGases.chiSmallB M ℓ d u z| := le_abs_self _
    _ ≤ Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z - u) :=
        Work.SmallBoxSliding.abs_chiSmallB_le (M := M) (ℓ := ℓ) (d := d) hM u z
    _ ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
        mul_le_mul_of_nonneg_left hb2 Submission.BoseGases.chiSupAbs_nonneg

/-- **The local count is dominated by the `χ_{B(u)}`-sum**: `nCountB = Σ χ² ≤ ν·Σ χ` with
`ν := chiSupAbs · chiSmallDecay M` (pointwise, from `0 ≤ χ ≤ ν`).  This is what lets the fibre term
of the word (which is `≥ −μ K (av) Σ χ`, `wSmall1Pair_fibre_le_chiB`) pay the Lipschitz remainder
`F(N/χ) ≤ F(s) + 5μ(N/χ + s)`. -/
theorem nCountB_le_nu_mul_sum_chiSmallB {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (x : Submission.BoseGases.X n) :
    Work.BoseFixB1.nCountB M ℓ d u x
      ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) := by
  have hν : 0 ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg M)
  rw [Work.BoseFixB1.nCountB, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : Submission.BoseGases.chiSmallB M ℓ d u (x i)
      ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
    chiSmallB_le_sup_B1S hM u (x i)
  have h2 : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u (x i) :=
    Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u (x i)
  nlinarith [h1, h2, hν]

end Work.BoseFixB1S
