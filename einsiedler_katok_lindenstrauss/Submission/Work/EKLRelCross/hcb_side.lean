import Mathlib
import Submission.Work.EKLContract.All

open Work.EKLContract Work.EKLContract.Lemmas
open Filter Topology

namespace Work.EKLRelCross

/-- Conjugation of `u_ac(t)` by `u_cb(r)`: since `E_cb · E_ac = 0`, `E_ac · E_cb = E_ab` and
`E_cb · E_cb = 0`, one has
`u_cb(r) · u_ac(t) · u_cb(r)⁻¹ = u_ab(-(t r)) · u_ac(t)`. -/
lemma ucb_conj_uac {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) (r t : ℝ) :
    uij hcb r * uij hac t * (uij hcb r)⁻¹ = uij hab (-(t * r)) * uij hac t := by
  have hinv : (uij hcb r : SL3)⁻¹ = uij hcb (-r) := by
    rw [uij, uij, Matrix.SpecialLinearGroup.transvection_inv]
  apply ext_toMat
  rw [toMat_mul, toMat_mul, hinv, horoUij_toMat, horoUij_toMat, horoUij_toMat,
      toMat_mul, horoUij_toMat, horoUij_toMat]
  have h1 : (1 + Matrix.single c b r : Matrix (Fin 3) (Fin 3) ℝ) = shapeMat a b c 0 r 0 := by
    simp [shapeMat]
  have h2 : (1 + Matrix.single a c t : Matrix (Fin 3) (Fin 3) ℝ) = shapeMat a b c t 0 0 := by
    simp [shapeMat]
  have h3 : (1 + Matrix.single c b (-r) : Matrix (Fin 3) (Fin 3) ℝ) = shapeMat a b c 0 (-r) 0 := by
    simp [shapeMat]
  have h4 : (1 + Matrix.single a b (-(t * r)) : Matrix (Fin 3) (Fin 3) ℝ)
      = shapeMat a b c 0 0 (-(t * r)) := by
    simp [shapeMat]
  rw [h1, h2, h3, h4, shapeMat_mul hab hac hcb, shapeMat_mul hab hac hcb,
    shapeMat_mul hab hac hcb]
  simp only [zero_add, add_zero, mul_zero, add_neg_cancel, mul_neg]

/-- `u_cb(r)` commutes with `u_ab(s)` (both have target column `b`). -/
lemma ucb_conj_uab {a b c : Fin 3} (hab : a ≠ b) (hcb : c ≠ b) (r s : ℝ) :
    uij hcb r * uij hab s * (uij hcb r)⁻¹ = uij hab s := by
  rw [uij_mul_comm_same_target hcb hab r s]
  group

/-- The `U_ij`-root `u_cb(r)` meets `U_ab ⊔ U_ac` only at the identity: the `(c,b)` entry of any
element of `U_ab ⊔ U_ac` is `0`, while that entry of `u_cb(r)` is `r`. -/
lemma ucb_srcU_eq_zero {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    (r : ℝ) (h : uij hcb r ∈ (Uij hab ⊔ Uij hac : Subgroup SL3)) : r = 0 := by
  rw [srcU_sup_eq_sub hab hac] at h
  have h' : uij hcb r ∈ srcU_set a b c := by
    have hc := h
    change uij hcb r ∈ ((srcU_sub hab hac : Subgroup SL3) : Set SL3) at hc
    rwa [srcU_sub_eq_set hab hac (Ne.symm hcb)] at hc
  have hkey : toMat (uij hcb r) c b = 0 := by
    have h'' := h' c b ?_
    · simpa [Matrix.one_apply, hcb] using h''
    · rintro (⟨hca, _⟩ | ⟨hca, _⟩) <;> exact hac hca.symm
  rw [horoUij_toMat] at hkey
  simpa [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, hcb] using hkey

/-- `aDiag (srcU_exp a b c)` centralises `u_cb(r)`: the exponent vector `srcU_exp a b c` takes
the same value `1` at `b` and at `c`. -/
lemma aDiag_srcU_exp_comm_ucb {a b c : Fin 3} (hcb : c ≠ b) (r : ℝ) :
    aDiag (srcU_exp a b c) * uij hcb r = uij hcb r * aDiag (srcU_exp a b c) := by
  rw [horoUij_aDiag_mul (srcU_exp a b c) hcb r]
  rw [srcU_exp_k (Ne.symm hcb), srcU_exp_j a b c, sub_self, Real.exp_zero, one_mul]

theorem hcb_side (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) :
    (∀ g ∈ Work.EKLContract.Uij hcb,
      ∀ u ∈ (Work.EKLContract.Uij hab ⊔ Work.EKLContract.Uij hac : Subgroup Work.EKLContract.SL3),
        g * u * g⁻¹ ∈ (Work.EKLContract.Uij hab ⊔ Work.EKLContract.Uij hac : Subgroup Work.EKLContract.SL3)) ∧
    (∀ g ∈ Work.EKLContract.Uij hcb,
      g ∈ (Work.EKLContract.Uij hab ⊔ Work.EKLContract.Uij hac : Subgroup Work.EKLContract.SL3) → g = 1) ∧
    (∃ t : Fin 3 → ℝ,
      (∀ g ∈ Work.EKLContract.Uij hcb, Work.EKLContract.aDiag t * g = g * Work.EKLContract.aDiag t) ∧
      ∀ u ∈ (Work.EKLContract.Uij hab ⊔ Work.EKLContract.Uij hac : Subgroup Work.EKLContract.SL3),
        Filter.Tendsto
          (fun n : ℕ => (Work.EKLContract.aDiag t) ^ n * u * ((Work.EKLContract.aDiag t) ^ n)⁻¹)
          Filter.atTop (nhds (1 : Work.EKLContract.SL3))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg u hu
    obtain ⟨r, hr⟩ := (horoUij_mem_iff hcb g).mp hg
    rw [srcU_sup_eq_sub hab hac] at hu ⊢
    rw [srcU_mem_sub] at hu ⊢
    obtain ⟨s, t, rfl⟩ := hu
    refine ⟨s - t * r, t, ?_⟩
    rw [← hr]
    unfold srcU_shape
    rw [show uij hcb r * (uij hab s * uij hac t) * (uij hcb r)⁻¹
        = (uij hcb r * uij hab s * (uij hcb r)⁻¹)
            * (uij hcb r * uij hac t * (uij hcb r)⁻¹) from by group]
    rw [ucb_conj_uab hab hcb r s, ucb_conj_uac hab hac hcb r t]
    rw [← mul_assoc, ← uij_add' hab s (-(t * r))]
    rw [show s + -(t * r) = s - t * r from by ring]
  · intro g hg hgH
    obtain ⟨r, hr⟩ := (horoUij_mem_iff hcb g).mp hg
    rw [← hr] at hgH
    have hr0 : r = 0 := ucb_srcU_eq_zero hab hac hcb r hgH
    rw [← hr, hr0, horoUij_zero hcb]
  · refine ⟨srcU_exp a b c, ?_, ?_⟩
    · intro g hg
      obtain ⟨r, hr⟩ := (horoUij_mem_iff hcb g).mp hg
      rw [← hr]
      exact aDiag_srcU_exp_comm_ucb hcb r
    · intro u hu
      rw [srcU_sup_eq_sub hab hac] at hu
      rw [srcU_mem_sub] at hu
      obtain ⟨s, t, rfl⟩ := hu
      exact srcU_contraction hab hac (Ne.symm hcb) s t

end Work.EKLRelCross
