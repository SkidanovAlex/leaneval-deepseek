import Mathlib
import Submission.Work.WilC4aU.ClusterDefs

set_option autoImplicit false
noncomputable section

namespace Work.WilC4aU

open Work.WilC0

/-- The half-space `{z : BB1 k → ℝ | 0 < z (eps)}` is existentially definable: `eps > 0` holds
if and only if there is `t` with `t ^ 2 * eps = 1`. -/
theorem posEps_rexExist {k : ℕ} :
    RExpExistI {z : BB1 k → ℝ | 0 < z (Sum.inr (0 : Fin 1))} := by
  have heval : ∀ (w : BB1 k → ℝ) (t : ℝ),
      rexpEval (Sum.elim w (fun _ : Fin 1 => t))
        (MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 1))) ^ 2
          * MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr (0 : Fin 1)))) - 1)
        = t ^ 2 * w (Sum.inr (0 : Fin 1)) - 1 := by
    intro w t
    simp only [rexpEval_sub, rexpEval_mul, rexpEval_pow, rexpEval_X_inl, rexpEval_one,
      Sum.elim_inl, Sum.elim_inr]
  refine ⟨Fin 1, inferInstance,
    MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 1))) ^ 2
      * MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr (0 : Fin 1)))) - 1, ?_⟩
  ext z
  rw [mem_RExZero]
  constructor
  · intro hz
    have hz' : 0 < z (Sum.inr (0 : Fin 1)) := hz
    refine ⟨fun _ : Fin 1 => Real.sqrt ((z (Sum.inr (0 : Fin 1)))⁻¹), ?_⟩
    have h1 : 0 ≤ (z (Sum.inr (0 : Fin 1)))⁻¹ := inv_nonneg.mpr hz'.le
    rw [heval z (Real.sqrt ((z (Sum.inr (0 : Fin 1)))⁻¹)), Real.sq_sqrt h1,
      inv_mul_cancel₀ (ne_of_gt hz')]
    ring
  · rintro ⟨y, hy⟩
    have key : (y 0) ^ 2 * z (Sum.inr (0 : Fin 1)) = 1 := by
      have h := hy
      simp only [rexpEval_sub, rexpEval_mul, rexpEval_pow, rexpEval_X_inl, rexpEval_one,
        Sum.elim_inl, Sum.elim_inr] at h
      linarith
    have hgoal : 0 < z (Sum.inr (0 : Fin 1)) := by
      by_contra hcon
      have hcon' : z (Sum.inr (0 : Fin 1)) ≤ 0 := le_of_not_gt hcon
      have hle := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (y 0)) hcon'
      linarith
    exact hgoal

theorem Eset_rexExist {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hD : Work.WilC0.RExpExistI (Work.WilC4aU.Dset k Y)) :
    Work.WilC0.RExpExistI {z : Work.WilC4aU.BB0 k → ℝ | ∀ e : ℝ, 0 < e →
      Sum.elim z (fun _ : Fin 1 => e) ∈ Work.WilC4aU.Dset k Y} := by
  have hAc : RExpExistI (Dset k Y)ᶜ := RExpExistI.compl hR hD
  have hG : RExpExistI ({z : BB1 k → ℝ | 0 < z (Sum.inr (0 : Fin 1))} ∩ (Dset k Y)ᶜ) :=
    posEps_rexExist.inter hAc
  have hProj : RExpExistI {z : BB0 k → ℝ | ∃ a : ℝ,
      Sum.elim z (fun _ : Fin 1 => a) ∈
        ({z : BB1 k → ℝ | 0 < z (Sum.inr (0 : Fin 1))} ∩ (Dset k Y)ᶜ)} :=
    hG.projLast
  refine (RExpExistI.compl hR hProj).of_eq ?_
  ext z
  constructor
  · intro hz e he
    by_contra hmem
    exact hz ⟨e, he, hmem⟩
  · rintro hz ⟨a, ha, hna⟩
    exact hna (hz a ha)

end Work.WilC4aU
