/-
Copyright: work module for the Elgindi finite-time singularity project.

# Radial integration by parts against the weight `w(z)²`

For the radial variable `z` and the weight `w z = (1+z)²/z²` we prove the identity

  `∫_{z>0} w(z)² φ(z) (z ψ'(z)) dz
      = ∫_{z>0} w(z)² (-(z φ'(z)) - ((z-3)/(1+z)) φ(z)) ψ(z) dz`

for `C¹` functions `φ, ψ` on `(0,∞)` which vanish on `(0,δ)` and for `z > R`
(`0 < δ < R`).  The identity is the integration by parts

  `(z w(z)²)' = w(z)² (z-3)/(1+z)`

of the paper's radial weight algebra
(`Work.FTS.EllipticEst.weight_algebra_fts`, §'Elliptic Regularity Estimates' of
Elgindi, Annals 194 (3) 2021), together with the vanishing of the boundary terms:
the product `z w(z)² φ(z) ψ(z)` vanishes near `0` and near `∞`.

The proof is split into two reusable pieces:

* `setIntegral_Ici_eq_intervalIntegral_of_support`: the integral over `[0,∞)` of a
  function vanishing outside a compact interval `[a,b] ⊂ (0,∞)` equals its
  `intervalIntegral` over `[a,b]`;
* `radial_ibp_interval`: the same integration by parts on a compact interval
  `[a,b] ⊂ (0,∞)`, with the boundary terms `φ a`, `φ b` vanishing.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.weight_algebra_fts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.RPFresh

/-- If `f` vanishes at `0` and off `[a,b]` (with `0 < a ≤ b`), then its integral over
`[0,∞)` equals its `intervalIntegral` over `[a,b]`. -/
theorem setIntegral_Ici_eq_intervalIntegral_of_support {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (h0 : f 0 = 0) (hf : ∀ z, 0 < z → (z < a ∨ b < z) → f z = 0) :
    (∫ z in Set.Ici 0, f z) = ∫ z in a..b, f z := by
  have h1 : (∫ z in Set.Ici 0, f z) = ∫ z in Set.Icc a b, f z :=
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (s := Set.Icc a b) (t := Set.Ici 0) measurableSet_Ici
      (fun x hx => by simp only [Set.mem_Ici]; linarith [hx.1, ha])
      (fun x hx => by
        have hxa : x < a ∨ b < x := by
          simpa only [Set.mem_Icc, not_and_or, not_le] using hx.2
        have hx0 : (0 : ℝ) ≤ x := hx.1
        rcases eq_or_lt_of_le hx0 with h | h
        · rw [← h]; exact h0
        · exact hf x h hxa)
  rw [h1, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

/-- **Integration by parts against the weight `w²` on a compact interval.**

For `0 < a ≤ b` and `C¹` functions `φ, ψ` on `(0,∞)` with `φ a = φ b = 0`, the boundary terms
of the integration by parts disappear and

  `∫_a^b w(z)² φ(z) (z ψ'(z)) = ∫_a^b w(z)² (-(z φ'(z)) - ((z-3)/(1+z)) φ(z)) ψ(z) dz`.

The key point is `(z w(z)²)' = w(z)² (z-3)/(1+z)` (`Work.FTS.EllipticEst.weight_algebra_fts`),
so that `u = z ↦ z w(z)² φ(z)`, `v = ψ` give `∫ u v' = [u v] - ∫ u' v = -∫ u' v`. -/
theorem radial_ibp_interval {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {φ ψ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 1 φ (Set.Ioi 0)) (hψ : ContDiffOn ℝ 1 ψ (Set.Ioi 0))
    (hφa : φ a = 0) (hφb : φ b = 0) :
    (∫ z in a..b, (Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z))
      = ∫ z in a..b, (Work.Spaces.w z) ^ 2
          * (-(z * deriv φ z) - (z - 3) / (1 + z) * φ z) * ψ z := by
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun x hx => by
    simp only [Set.mem_Ioi]; linarith [hx.1, ha]
  -- differentiability of `φ`, `ψ` and of the weight factor
  have hphid : ∀ z, 0 < z → HasDerivAt φ (deriv φ z) z := fun z hz =>
    ((hφ.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have hpsid : ∀ z, 0 < z → HasDerivAt ψ (deriv ψ z) z := fun z hz =>
    ((hψ.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have hwu : ∀ z, 0 < z → HasDerivAt (fun y : ℝ => y * (Work.Spaces.w y) ^ 2)
      ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))) z := by
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    have hdiff : DifferentiableAt ℝ (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z := by
      have hw : DifferentiableAt ℝ (fun y : ℝ => Work.Spaces.w y) z := by
        have h1 : DifferentiableAt ℝ (fun y : ℝ => (1 + y) ^ 2 / y ^ 2) z := by
          apply DifferentiableAt.div <;> try fun_prop
          exact pow_ne_zero 2 hz0
        simpa only [Work.Spaces.w] using h1
      exact differentiableAt_id.mul (hw.pow 2)
    have hdv : deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z
        = (Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) := by
      rw [Work.FTS.EllipticEst.weight_algebra_fts.2.2.2.1 z hz0, Work.Spaces.w]
      field_simp
    rw [← hdv]
    exact hdiff.hasDerivAt
  -- continuity of everything on `[a,b] ⊂ (0,∞)`
  have hwcont : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Icc a b) := by
    have h1 : ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) := by
      apply ContinuousOn.div <;> try fun_prop
      intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)
    simpa only [Work.Spaces.w] using h1.mono hsub
  have hdφcont : ContinuousOn (deriv φ) (Set.Icc a b) :=
    (hφ.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub
  have hdψcont : ContinuousOn (deriv ψ) (Set.Icc a b) :=
    (hψ.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub
  have hφcont : ContinuousOn φ (Set.Icc a b) := hφ.continuousOn.mono hsub
  have hu'cont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) * φ z
      + (z * (Work.Spaces.w z) ^ 2) * deriv φ z) (Set.Icc a b) := by
    have hdiv : ContinuousOn (fun z : ℝ => (z - 3) / (1 + z)) (Set.Icc a b) := by
      apply ContinuousOn.div <;> try fun_prop
      intro z hz
      exact ne_of_gt (by linarith [hz.1, ha] : (0 : ℝ) < 1 + z)
    exact (((hwcont.pow 2).mul hdiv).mul hφcont).add
      ((continuousOn_id.mul (hwcont.pow 2)).mul hdφcont)
  have hu'int : IntervalIntegrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) * φ z
      + (z * (Work.Spaces.w z) ^ 2) * deriv φ z) volume a b :=
    hu'cont.intervalIntegrable_of_Icc hab
  have hψ'int : IntervalIntegrable (deriv ψ) volume a b :=
    hdψcont.intervalIntegrable_of_Icc hab
  -- the integration by parts
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun y : ℝ => y * (Work.Spaces.w y) ^ 2 * φ y) (v := ψ)
      (u' := fun z : ℝ => (Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) * φ z
        + (z * (Work.Spaces.w z) ^ 2) * deriv φ z)
      (v' := deriv ψ)
      (fun x hx => by
        have hxab : a ≤ x ∧ x ≤ b := by
          rw [Set.uIcc_of_le hab] at hx; exact hx
        exact (hwu x (by linarith [hxab.1, ha])).mul (hphid x (by linarith [hxab.1, ha])))
      (fun x hx => by
        have hxab : a ≤ x ∧ x ≤ b := by
          rw [Set.uIcc_of_le hab] at hx; exact hx
        exact hpsid x (by linarith [hxab.1, ha]))
      hu'int hψ'int
  -- the two sides, in terms of the integration by parts
  have h1 : (∫ z in a..b, (Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z))
      = - ∫ z in a..b, ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) * φ z
          + (z * (Work.Spaces.w z) ^ 2) * deriv φ z) * ψ z := by
    rw [intervalIntegral.integral_congr
      (g := fun z => (z * (Work.Spaces.w z) ^ 2 * φ z) * deriv ψ z) (fun z _ => by ring)]
    rw [hIBP]
    simp [hφa, hφb]
  have h2 : (∫ z in a..b, (Work.Spaces.w z) ^ 2
        * (-(z * deriv φ z) - (z - 3) / (1 + z) * φ z) * ψ z)
      = - ∫ z in a..b, ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) * φ z
          + (z * (Work.Spaces.w z) ^ 2) * deriv φ z) * ψ z := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro z _
    ring
  rw [h1, h2]

theorem RadialIBP {δ R : ℝ} (hδ : 0 < δ) (hδR : δ < R) {φ ψ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 1 φ (Set.Ioi 0)) (hψ : ContDiffOn ℝ 1 ψ (Set.Ioi 0))
    (hsφ : ∀ z, (0 < z ∧ z < δ) ∨ R < z → φ z = 0)
    (hsψ : ∀ z, (0 < z ∧ z < δ) ∨ R < z → ψ z = 0) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z))
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (-(z * deriv φ z) - (z - 3) / (1 + z) * φ z) * ψ z := by
  have ha : 0 < δ / 2 := by linarith
  have hab : δ / 2 ≤ R + 1 := by linarith
  -- both integrands vanish off the compact interval `[δ/2, R+1] ⊂ (0,∞)`
  have hfL : ∀ z, 0 < z → (z < δ / 2 ∨ R + 1 < z) →
      (Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z) = 0 := by
    intro z hz hc
    rcases hc with h | h
    · rw [hsφ z (Or.inl ⟨hz, by linarith⟩)]; ring
    · rw [hsφ z (Or.inr (by linarith))]; ring
  have hfR : ∀ z, 0 < z → (z < δ / 2 ∨ R + 1 < z) →
      (Work.Spaces.w z) ^ 2 * (-(z * deriv φ z) - (z - 3) / (1 + z) * φ z) * ψ z = 0 := by
    intro z hz hc
    rcases hc with h | h
    · rw [hsψ z (Or.inl ⟨hz, by linarith⟩)]; ring
    · rw [hsψ z (Or.inr (by linarith))]; ring
  have h0L : (Work.Spaces.w 0) ^ 2 * φ 0 * (0 * deriv ψ 0) = 0 := by simp [Work.Spaces.w]
  have h0R : (Work.Spaces.w 0) ^ 2 * (-(0 * deriv φ 0) - (0 - 3) / (1 + 0) * φ 0) * ψ 0 = 0 := by
    simp [Work.Spaces.w]
  rw [Work.Spaces.Iz,
    setIntegral_Ici_eq_intervalIntegral_of_support (a := δ / 2) (b := R + 1) ha hab h0L hfL,
    setIntegral_Ici_eq_intervalIntegral_of_support (a := δ / 2) (b := R + 1) ha hab h0R hfR]
  exact radial_ibp_interval ha hab hφ hψ
    (hsφ (δ / 2) (Or.inl ⟨ha, by linarith⟩)) (hsφ (R + 1) (Or.inr (by linarith)))

end Work.FTS.EllipticEst.RPFresh
