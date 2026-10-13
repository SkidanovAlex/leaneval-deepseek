import Mathlib
import Submission.Work.WilE7.FrontierCS.exists_end_bij_range_sub_le

/-!
  `Work.WilE7.FrontierCS.exists_real_det_ne_zero`.

  Given `P : Matrix (Fin j) (Fin d) ℝ` and `Q : Matrix (Fin j) (Fin j) ℝ` such that the affine
  map `(t, e) ↦ P.mulVec t + Q.mulVec e` is surjective onto `ℝ^j`, we must exhibit a matrix `Λ`
  with `(P * Λ + Q).det ≠ 0`.

  The argument is the following.  Write `V := P.mulVecLin.range`, so `V` is the column space of `P`;
  the hypothesis says `V ⊔ Q.mulVecLin.range = ⊤`.  The abstract linear-algebra lemma
  `exists_end_bij_range_sub_le` then produces a *bijective* linear endomorphism `M` of `ℝ^j` with
  `(M - Q.mulVecLin).range ≤ V`.  Since `V = range P.mulVecLin`, the difference `M - Q.mulVecLin`
  is `P.mulVecLin ∘ Λ.mulVecLin` for a matrix `Λ` (build `Λ` column by column: the `i`-th column of
  `P * Λ` is a preimage of `(M - Q.mulVecLin) (Pi.single i 1)` under `P.mulVec`).  Hence
  `(P * Λ + Q).mulVecLin = M` is bijective, `P * Λ + Q` is invertible, and so its determinant is
  nonzero.
-/

set_option autoImplicit false
noncomputable section

namespace Work.WilE7.FrontierCS

/-- **Matrix form of the crux.**  If `M` is a bijective endomorphism of `ℝ^j` whose difference
with `Q.mulVecLin` takes values in the column space of `P`, then some `Λ` makes `P * Λ + Q`
invertible (so its determinant is nonzero).

Concretely, `Λ` is built column by column: the `i`-th column of `P * Λ` is chosen as a preimage
under `P.mulVec` of `(M - Q.mulVecLin) (Pi.single i 1)`; linearity and agreement on the standard
basis give `(P * Λ).mulVecLin = M - Q.mulVecLin`, whence `(P * Λ + Q).mulVecLin = M` is bijective
and the matrix `P * Λ + Q` is a unit. -/
private lemma exists_det_ne_zero_of_bij {d j : ℕ}
    (P : Matrix (Fin j) (Fin d) ℝ) (Q : Matrix (Fin j) (Fin j) ℝ)
    (M : (Fin j → ℝ) →ₗ[ℝ] (Fin j → ℝ)) (hM : Function.Bijective M)
    (hrange : (M - Q.mulVecLin).range ≤ P.mulVecLin.range) :
    ∃ Lam : Matrix (Fin d) (Fin j) ℝ, (P * Lam + Q).det ≠ 0 := by
  classical
  -- Each column of `M - Q.mulVecLin` lies in `range P.mulVec`.
  have hpre : ∀ i : Fin j, ∃ w : Fin d → ℝ,
      P.mulVec w = (M - Q.mulVecLin) (Pi.single i 1) := by
    intro i
    have hmem : (M - Q.mulVecLin) (Pi.single i 1) ∈ P.mulVecLin.range :=
      hrange (LinearMap.mem_range.mpr ⟨Pi.single i 1, rfl⟩)
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hmem
    exact ⟨v, by rw [← Matrix.mulVecLin_apply]; exact hv⟩
  let Lam : Matrix (Fin d) (Fin j) ℝ := Matrix.of (fun k i => (Classical.choose (hpre i)) k)
  have hcol : ∀ i : Fin j, Lam.col i = Classical.choose (hpre i) := by
    intro i; funext k; rfl
  -- The two linear maps agree on the standard basis, hence everywhere.
  have hPL : (P * Lam).mulVecLin = M - Q.mulVecLin := by
    refine (Pi.basisFun ℝ (Fin j)).ext (fun i => ?_)
    rw [Pi.basisFun_apply, Matrix.mulVecLin_mul]
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
    rw [hcol i]
    exact Classical.choose_spec (hpre i)
  have hfinal : (P * Lam + Q).mulVecLin = M := by
    rw [Matrix.mulVecLin_add, hPL]
    abel
  refine ⟨Lam, ?_⟩
  -- `M` bijective, so `(P * Lam + Q).mulVec` is surjective, so the matrix is a unit.
  have hsurj : Function.Surjective (P * Lam + Q).mulVec := by
    intro y
    obtain ⟨x, hx⟩ := hM.2 y
    exact ⟨x, by rw [← Matrix.mulVecLin_apply, hfinal]; exact hx⟩
  have hU : IsUnit (P * Lam + Q) := Matrix.mulVec_surjective_iff_isUnit.mp hsurj
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hU)

/-- The hypothesis `hsurj` says precisely that the range of the block map `[P | Q]` is everything,
i.e. `range P + range Q = ⊤`. -/
private lemma range_sup_eq_top_of_surj {d j : ℕ} (P : Matrix (Fin j) (Fin d) ℝ)
    (Q : Matrix (Fin j) (Fin j) ℝ)
    (hsurj : ∀ y : Fin j → ℝ, ∃ t e, P.mulVec t + Q.mulVec e = y) :
    P.mulVecLin.range ⊔ Q.mulVecLin.range = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨t, e, hte⟩ := hsurj y
  rw [← hte]
  exact Submodule.add_mem_sup
    (by rw [← Matrix.mulVecLin_apply]; exact LinearMap.mem_range.mpr ⟨t, rfl⟩)
    (by rw [← Matrix.mulVecLin_apply]; exact LinearMap.mem_range.mpr ⟨e, rfl⟩)

theorem exists_real_det_ne_zero {d j : ℕ} (P : Matrix (Fin j) (Fin d) ℝ)
    (Q : Matrix (Fin j) (Fin j) ℝ)
    (hsurj : ∀ y : Fin j → ℝ, ∃ t e, P.mulVec t + Q.mulVec e = y) :
    ∃ Λ : Matrix (Fin d) (Fin j) ℝ, (P * Λ + Q).det ≠ 0 := by
  classical
  have hsup : P.mulVecLin.range ⊔ Q.mulVecLin.range = ⊤ := range_sup_eq_top_of_surj P Q hsurj
  obtain ⟨M, hMbij, hMrange⟩ :=
    exists_end_bij_range_sub_le (E := Fin j → ℝ) P.mulVecLin.range Q.mulVecLin hsup
  exact exists_det_ne_zero_of_bij P Q M hMbij hMrange

end Work.WilE7.FrontierCS
