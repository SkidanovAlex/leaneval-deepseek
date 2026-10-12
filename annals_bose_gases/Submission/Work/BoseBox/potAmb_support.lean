import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBox.potAmbAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.potAmb_support` — the localisation region of the `C2` node

The sliding kernel of `potAmb` carries the two window factors `χ_u(x)`, `χ_u(y)`
(`chiU ℓ u ·`), and `χ` is supported in the closed unit cube; consequently

* `χ_u(y) ≠ 0` forces `y ∈ Λ(u) = bigBox ℓ u`
  (`chiU_ne_zero_imp_mem_acube`);
* if moreover `x ∈ Ω = ombox L` then `u` lies in the localisation region
  `coverU ℓ L` (`chiU_ne_zero_mem_coverU`);
* therefore the one-body fibre integral over `Λ(u)` equals the integral over all
  of `ℝ³` (`integral_bigBox_wLoc`), and the bracket of `potAmb` agrees with its
  full-space form `potBracketG` (`potBracket_eq_G`);
* for `x ∈ box N L` the whole bracket vanishes off `coverU ℓ L`
  (`potBracket_eq_zero_of_notMem_coverU`) — the statement that the `u`-integrand
  is supported in the localisation region.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators

namespace Work.BoseBox


open _root_.BoseGases
open Submission.BoseGases
open Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `χ_u(y) ≠ 0` forces `y ∈ Λ(u) = ℓu + [−ℓ/2,ℓ/2]³`. -/
lemma chiU_ne_zero_imp_mem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {u y : ℝ³}
    (hy : chiU ℓ u y ≠ 0) : y - ℓ • u ∈ acube ℓ := by
  have hz : ‖(ℓ⁻¹) • y - u‖ ≤ 1 / 2 := by
    by_contra h
    push_neg at h
    exact hy (chi_eq_zero_of_norm_gt ((ℓ⁻¹) • y - u) h)
  have heq : y - ℓ • u = ℓ • ((ℓ⁻¹) • y - u) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ (ne_of_gt hℓ), one_smul]
  have hnorm : ‖y - ℓ • u‖ ≤ ℓ / 2 := by
    rw [heq, norm_smul, Real.norm_of_nonneg (le_of_lt hℓ)]
    calc
      ℓ * ‖(ℓ⁻¹) • y - u‖ ≤ ℓ * (1 / 2) :=
        mul_le_mul_of_nonneg_left hz (le_of_lt hℓ)
      _ = ℓ / 2 := by ring
  intro m
  have hcoord : |(y - ℓ • u) m| ≤ ‖y - ℓ • u‖ := by
    simpa using PiLp.norm_apply_le (y - ℓ • u) m
  have hle : |(y - ℓ • u) m| ≤ ℓ / 2 := le_trans hcoord hnorm
  refine Set.mem_Icc.mpr ⟨?_, ?_⟩
  · have := (abs_le.mp hle).1; linarith
  · exact (abs_le.mp hle).2

/-- If `χ_u(x) ≠ 0` and `x` lies in the big box `Ω = [0,L]³`, then `u` belongs to the
localisation region `coverU ℓ L`. -/
lemma chiU_ne_zero_mem_coverU {ℓ L : ℝ} (hℓ : 0 < ℓ) {x : ℝ³} (hx : x ∈ ombox L)
    {u : ℝ³} (hu : chiU ℓ u x ≠ 0) : u ∈ coverU ℓ L :=
  ⟨x, hx, chiU_ne_zero_imp_mem_acube hℓ hu⟩

/-- `wLoc ℓ gK u a y` vanishes when `y ∉ bigBox ℓ u` (the `χ_u(y)` factor dies). -/
lemma wLoc_eq_zero_of_notMem_bigBox {ℓ : ℝ} (hℓ : 0 < ℓ) (gK : ℝ³ → ℝ) (u a : ℝ³)
    {y : ℝ³} (hy : y ∉ bigBox ℓ u) : wLoc ℓ gK u a y = 0 := by
  have hchi : chiU ℓ u y = 0 := by
    by_contra hne
    exact hy (chiU_ne_zero_imp_mem_acube hℓ hne)
  simp [wLoc, hchi]

/-- The one-body fibre integral over the sliding box `Λ(u)` equals the integral over all
of `ℝ³`: the localising window `χ_u(y)` confines the integrand to `Λ(u)`. -/
lemma integral_bigBox_wLoc {ℓ : ℝ} (hℓ : 0 < ℓ) (gK : ℝ³ → ℝ) (u a : ℝ³) :
    (∫ y in bigBox ℓ u, wLoc ℓ gK u a y) = potBr ℓ gK u a := by
  rw [potBr]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun y hy => wLoc_eq_zero_of_notMem_bigBox hℓ gK u a hy)

/-- The bracket of `potAmb` (fibre integrals over the sliding box) agrees with the
full-space bracket `potBracketG`. -/
lemma potBracket_eq_G {N : ℕ} {ℓ μ : ℝ} {v : ℝ³ → ℝ} {h : ScatSol v} (hℓ : 0 < ℓ)
    (u : ℝ³) (x : X N) :
    potBracket N ℓ μ v h u x = potBracketG N ℓ μ v (g0 v h) u x := by
  have hsum : (∑ i : Fin N, ∫ y in bigBox ℓ u, wLoc ℓ (g0 v h) u (x i) y)
      = ∑ i : Fin N, ∫ y : ℝ³, wLoc ℓ (g0 v h) u (x i) y :=
    Finset.sum_congr rfl fun i _ => integral_bigBox_wLoc hℓ (g0 v h) u (x i)
  simp only [potBracket, potBracketG, potBr, hsum]

/-- For `x` in the big box, the bracket vanishes whenever `u` is outside the
localisation region `coverU ℓ L`. -/
lemma potBracket_eq_zero_of_notMem_coverU {N : ℕ} {ℓ L μ : ℝ} {v : ℝ³ → ℝ}
    {h : ScatSol v} (hℓ : 0 < ℓ) {x : X N} (hx : x ∈ box N L) {u : ℝ³}
    (hu : u ∉ coverU ℓ L) : potBracket N ℓ μ v h u x = 0 := by
  have hxi : ∀ i : Fin N, chiU ℓ u (x i) = 0 := by
    intro i
    by_contra hne
    exact hu (chiU_ne_zero_mem_coverU hℓ (hx i) hne)
  have h1 : (∑ i : Fin N, ∫ y in bigBox ℓ u, wLoc ℓ (g0 v h) u (x i) y) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hzero : (fun y : ℝ³ => wLoc ℓ (g0 v h) u (x i) y) = fun _ : ℝ³ => (0 : ℝ) := by
      funext y
      simp [wLoc, hxi i]
    rw [hzero]
    simp
  have h2 : (∑ p ∈ pairSet N, wLoc ℓ v u (x p.1) (x p.2)) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    simp [wLoc, hxi p.1]
  simp only [potBracket, h1, h2]
  ring

end Work.BoseBox
