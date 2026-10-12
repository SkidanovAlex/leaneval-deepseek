import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseSWE.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSWE

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **F2 of the `BoseSWE` route**: the normalised node with the slack gives piece C with the slack.
Recipe (see `Submission/Work/BoseSWE/BRIEF.md` §5): copy `Work.BoseB1Cube.nomRowLinWindowRow_of_normNode`
(`Submission/Work/BoseB1Cube/nomRowLinWindowRow.lean`): homogeneity of `sbWordCube`
(`Work.BoseFixB1S.sbWordCube_smul`) with `c = (√I)⁻¹`, `I = ∫Ψ²`, `c²·I = 1`, plus the a.e.-null
case (`sbWordCube_eq_zero_of_ae_eq_zero`).  The slack carries through unchanged: `NormNodeE` at
`c·Ψ` gives `Dem − ErrE ≤ c²·sbWordCube(Ψ)`, hence `(Dem − ErrE)·I ≤ sbWordCube(Ψ)`. -/
theorem nomRowLinWindowRowE_of_normNodeE {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hN : Work.BoseSWE.NormNodeE v h) :
    Work.BoseSWE.NomRowLinWindowRowE v h R := by
  intro Cn hCn
  obtain ⟨ε, C, hε, hC, hrow⟩ := hN Cn hCn
  refine ⟨ε, C, hε, hC, ?_⟩
  intro μ hAdm n Ψ u hu hΨ hsupp hn1 hn2
  simp only [Work.BoseB1Cube.nomV, Work.BoseB1Cube.nomW, Work.BoseFixB1.bV, Work.BoseFixB1.bW,
    Work.BoseFixB1.bSide, Work.BoseFixB1.bD, Work.BoseFixB1.bM, Work.BoseFixB1.bA] at hu hn1 hn2 ⊢
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  set I : ℝ := ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Ψ x) ^ 2 with hIdef
  have hInn : 0 ≤ I := by
    rw [hIdef]; exact integral_nonneg (fun x => sq_nonneg _)
  rcases eq_or_lt_of_le hInn with hI0 | hIpos
  · -- the a.e.-null case
    have hnn : 0 ≤ᵐ[(volume : Measure (X n)).restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))]
        (fun x : X n => (Ψ x) ^ 2) := Filter.Eventually.of_forall (fun x => sq_nonneg _)
    obtain ⟨Bdd, hBdd⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
      (s := Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
      (f := Ψ) (ContDiff.continuous hΨ).continuousOn
    have hint : Integrable (fun x : X n => (Ψ x) ^ 2)
        ((volume : Measure (X n)).restrict
          (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))) :=
      Work.BoseFixB1S.integrableOn_sq_of_bound (N := n) hℓ (ContDiff.continuous hΨ).measurable
        (fun x hx => by simpa [Real.norm_eq_abs] using hBdd x hx)
    have hzero : (fun x : X n => (Ψ x) ^ 2) =ᵐ[(volume : Measure (X n)).restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp (by rw [hIdef] at hI0; exact hI0.symm)
    have hΨ0 : Ψ =ᵐ[(volume : Measure (X n)).restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))] 0 :=
      hzero.mono (fun x hx => by
        have hx' : (Ψ x) ^ 2 = 0 := hx
        exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp hx')
    have hnpos : 0 < n := by
      by_contra hcon
      have : n = 0 := Nat.eq_zero_of_not_pos hcon
      subst this
      have hV' : 0 < Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
        Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ hu
      have hprod : 0 < Cn * μ * Work.SmallBoxSliding.boxMass
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
        mul_pos (mul_pos (by linarith) hμ) hV'
      have hn1' : Cn * μ * Work.SmallBoxSliding.boxMass
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u ≤ ((0 : ℕ) : ℝ) := hn1
      push_cast at hn1'
      linarith [hprod, hn1']
    have hsw : Work.BoseFixB1B.sbWordCube v h μ u Ψ = 0 :=
      Work.BoseB1Cube.sbWordCube_eq_zero_of_ae_eq_zero (v := v) (h := h) (μ := μ) (u := u)
        (N := n)
        (by simpa only [Work.BoseFixB1.bSide] using hℓ)
        (by simpa only [Work.BoseFixB1.bD] using hd) hnpos (ContDiff.continuous hΨ).measurable hΨ0
    rw [hsw]
    refine le_of_eq ?_
    rw [hI0.symm, mul_zero]
  · -- the homogeneous case
    set c : ℝ := (Real.sqrt I)⁻¹ with hcdef
    have hc2 : c ^ 2 = I⁻¹ := by
      rw [hcdef, inv_pow, Real.sq_sqrt hIpos.le]
    have hΦint : (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        (c * Ψ x) ^ 2) = 1 := by
      have h1 : (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          (c * Ψ x) ^ 2)
          = c ^ 2 * ∫ x in Submission.BoseGases.abox n
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (Ψ x) ^ 2 := by
        rw [← MeasureTheory.integral_const_mul]
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
      rw [h1, ← hIdef, hc2, inv_mul_cancel₀ (ne_of_gt hIpos)]
    have hΦsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict
          (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
        (c * Ψ x) ≠ 0 → ∀ i : Fin n,
          x i ∈ Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u := by
      filter_upwards [hsupp] with x hx hne i
      exact hx (fun h0 => hne (by rw [h0, mul_zero])) i
    have hrow' := hrow μ hAdm n (fun x => c * Ψ x) u hu
      (by simpa only [smul_eq_mul, mul_comm] using hΨ.smul_const c) hΦsupp hΦint hn1 hn2
    simp only [Work.BoseSWE.Dem, Work.BoseFixB1.bV, Work.BoseFixB1.bW] at hrow'
    rw [Work.BoseFixB1S.sbWordCube_smul (v := v) h (μ := μ) u Ψ c] at hrow'
    have h2 : (c ^ 2 * Work.BoseFixB1B.sbWordCube v h μ u Ψ) * I
        = Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
      rw [hc2]
      field_simp
    exact le_trans (mul_le_mul_of_nonneg_right hrow' hIpos.le) (le_of_eq h2)

end

end Work.BoseSWE
