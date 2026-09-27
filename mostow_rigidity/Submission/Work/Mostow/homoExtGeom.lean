import Mathlib
import Submission.Work.Mostow.visualDefs
import Submission.Work.Mostow.coneImage

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- The boundary action `bd g` is injective on the boundary sphere. -/
lemma bd_injOn (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (g : LeanEval.Geometry.MostowRigidity.PO n 1) :
    Set.InjOn (Submission.Mostow.bd g) (Submission.Mostow.Sph n) := by
  have hbd_one := hA.2.2.2.2.2.2.2.2.1
  have hbd_mul := hA.2.2.2.2.2.2.2.2.2.1
  intro u hu v hv huv
  have h1 : Submission.Mostow.bd (g⁻¹ * g) u =
      Submission.Mostow.bd g⁻¹ (Submission.Mostow.bd g u) := hbd_mul g⁻¹ g u hu
  rw [inv_mul_cancel, hbd_one u hu] at h1
  have h2 : Submission.Mostow.bd (g⁻¹ * g) v =
      Submission.Mostow.bd g⁻¹ (Submission.Mostow.bd g v) := hbd_mul g⁻¹ g v hv
  rw [inv_mul_cancel, hbd_one v hv] at h2
  rw [h1, huv]
  exact h2.symm

theorem homoExtGeom (n : ℕ) (hn : 1 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (g : LeanEval.Geometry.MostowRigidity.PO n 1) :
    (∀ x : Submission.Mostow.E n, x ≠ 0 → ‖Work.Mostow.homoExt g x‖ = ‖x‖) ∧
    (∀ x : Submission.Mostow.E n, x ≠ 0 →
        ‖x‖⁻¹ • Work.Mostow.homoExt g x = Submission.Mostow.bd g (‖x‖⁻¹ • x)) ∧
    Set.InjOn (Work.Mostow.homoExt g) {x : Submission.Mostow.E n | x ≠ 0} := by
  have hbd_mem := hA.2.2.2.2.2.2.2.1
  -- `homoExt g` is the degree-one homogeneous extension of `bd g`.
  have hkey : ∀ x : Submission.Mostow.E n,
      Work.Mostow.homoExt g x = ‖x‖ • Submission.Mostow.bd g (‖x‖⁻¹ • x) := by
    intro x
    unfold Work.Mostow.homoExt
    rw [Work.Mostow.phiFun_eq_bd]
  have hmemb : ∀ x : Submission.Mostow.E n, x ≠ 0 →
      ‖x‖⁻¹ • x ∈ Submission.Mostow.Sph n := by
    intro x hx
    rw [mem_Sph_iff, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  have hnorm_eq : ∀ x : Submission.Mostow.E n, x ≠ 0 →
      ‖Work.Mostow.homoExt g x‖ = ‖x‖ := by
    intro x hx
    have hbdnorm : ‖Submission.Mostow.bd g (‖x‖⁻¹ • x)‖ = 1 := by
      have h := hbd_mem g (‖x‖⁻¹ • x) (hmemb x hx)
      rwa [mem_Sph_iff] at h
    rw [hkey x, norm_smul, hbdnorm, mul_one, norm_norm]
  have hbd_eq : ∀ x : Submission.Mostow.E n, x ≠ 0 →
      ‖x‖⁻¹ • Work.Mostow.homoExt g x = Submission.Mostow.bd g (‖x‖⁻¹ • x) := by
    intro x hx
    rw [hkey x, smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
  refine ⟨hnorm_eq, hbd_eq, ?_⟩
  intro x hx y hy heq
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hy0 : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hn : ‖x‖ = ‖y‖ := by rw [← hnorm_eq x hx, ← hnorm_eq y hy, heq]
  have hbdeq : Submission.Mostow.bd g (‖x‖⁻¹ • x) =
      Submission.Mostow.bd g (‖y‖⁻¹ • y) := by
    rw [← hbd_eq x hx, ← hbd_eq y hy, hn, heq]
  have huv : ‖x‖⁻¹ • x = ‖y‖⁻¹ • y :=
    bd_injOn n hA g (hmemb x hx) (hmemb y hy) hbdeq
  calc x = ‖x‖ • (‖x‖⁻¹ • x) := by
        rw [smul_smul, mul_inv_cancel₀ hx0, one_smul]
    _ = ‖x‖ • (‖y‖⁻¹ • y) := by rw [huv]
    _ = y := by rw [smul_smul, hn, mul_inv_cancel₀ hy0, one_smul]

end

end Work.Mostow
