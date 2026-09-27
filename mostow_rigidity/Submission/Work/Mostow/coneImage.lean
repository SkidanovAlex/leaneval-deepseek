import Mathlib
import Submission.Work.Mostow.visualDefs
import Submission.Work.Mostow.poAux

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix
open scoped Pointwise

noncomputable section

variable {n : ℕ}

/-- `hvec` and `theta` are the same vector. -/
lemma hvec_eq_theta (ξ : E n) : hvec ξ = theta ξ := rfl

/-- Rewriting the homogeneous-coordinate vector of the boundary formula. -/
lemma wvec_eq (g : PO n 1) (ξ : E n) :
    wvec_visualDefs g ξ = tsign (rep g) • (mat (rep g) *ᵥ theta ξ) := by
  rw [wvec_visualDefs, hvec_eq_theta, sMat, Matrix.smul_mulVec]

/-- The explicit formula `phiFun` agrees with `bd` (the two differ by the sign `tsign (rep g)`). -/
lemma phiFun_eq_bd (g : PO n 1) (ξ : E n) : phiFun g ξ = bd g ξ := by
  have hts : tsign (rep g) ≠ 0 := tsign_ne_zero (rep g)
  show WithLp.toLp 2 (fun i => wvec_visualDefs g ξ (Sum.inl i) / dfun g ξ)
      = WithLp.toLp 2 (fun i => (mat (rep g) *ᵥ theta ξ) (Sum.inl i)
                                  / (mat (rep g) *ᵥ theta ξ) (Sum.inr 0))
  congr 1
  funext i
  rw [dfun, wvec_eq]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ hts]

/-- `homoExt g` restricted to a ray through the origin is `r • bd g ξ`. -/
lemma homoExt_smul_sph (g : PO n 1) (ξ : E n) (hξ : ξ ∈ Sph n) {r : ℝ} (hr : 0 < r) :
    homoExt g (r • ξ) = r • bd g ξ := by
  have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).1 hξ
  have hnorm : ‖r • ξ‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hξn, mul_one]
  rw [homoExt, hnorm, smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul,
    phiFun_eq_bd g ξ]

theorem coneImage (n : ℕ) (hn : 1 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (g : LeanEval.Geometry.MostowRigidity.PO n 1) (B : Set (Submission.Mostow.E n))
    (hBs : B ⊆ Submission.Mostow.Sph n) :
    Work.Mostow.homoExt g '' Work.Mostow.cone B
      = Work.Mostow.cone (Submission.Mostow.bd g '' B) := by
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    subst hyx
    rw [cone, Set.mem_smul] at hy
    obtain ⟨r, hr, ξ, hξB, hry⟩ := hy
    subst hry
    rw [cone, Set.mem_smul]
    refine ⟨r, hr, bd g ξ, ?_, ?_⟩
    · rw [Set.mem_image]
      exact ⟨ξ, hξB, rfl⟩
    · exact (homoExt_smul_sph g ξ (hBs hξB) hr.1).symm
  · intro hx
    rw [cone, Set.mem_smul] at hx
    obtain ⟨r, hr, η, hη, hrx⟩ := hx
    obtain ⟨ξ, hξB, hξη⟩ := hη
    rw [cone, Set.mem_image]
    refine ⟨r • ξ, ?_, ?_⟩
    · rw [Set.mem_smul]
      exact ⟨r, hr, ξ, hξB, rfl⟩
    · rw [homoExt_smul_sph g ξ (hBs hξB) hr.1, hξη, hrx]

end

end Work.Mostow
