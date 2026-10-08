import Mathlib

namespace Work.L2F.Props.oddsub

theorem mk_eq_mk_of_eigen (F : Type*) [Field F] (m : Matrix (Fin 2) (Fin 2) F)
    (hm : ∀ c : F, m ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    {u v : Fin 2 → F} (hu : u ≠ 0) (hv : v ≠ 0) {c : F}
    (hu' : Matrix.mulVec m u = c • u) (hv' : Matrix.mulVec m v = c • v) :
    Projectivization.mk F u hu = Projectivization.mk F v hv := by
  -- Two non-zero eigenvectors of a non-scalar `2 × 2` matrix for the same eigenvalue `c`
  -- span the same line: the `c`-eigenspace is `ker (m - c • 1)`, which is a proper subspace
  -- of the 2-dimensional space `F²`, hence at most 1-dimensional (a line, not a plane).
  rw [Projectivization.mk_eq_mk_iff]
  by_cases hlin : LinearIndependent F ![u, v]
  · -- If `u` and `v` were linearly independent they would form a basis; since `m` acts on both
    -- by the scalar `c`, it would be the scalar matrix `c • 1`, contradicting `hm`.
    exfalso
    have hcard : Fintype.card (Fin 2) = Module.finrank F (Fin 2 → F) := by
      rw [Fintype.card_fin, Module.finrank_fin_fun]
    let b : Module.Basis (Fin 2) F (Fin 2 → F) :=
      basisOfLinearIndependentOfCardEqFinrank hlin hcard
    have hb : ⇑b = ![u, v] := coe_basisOfLinearIndependentOfCardEqFinrank hlin hcard
    have hmap : m.mulVecLin = c • (LinearMap.id : (Fin 2 → F) →ₗ[F] (Fin 2 → F)) := by
      apply Module.Basis.ext b
      intro i
      have hbi : b i = ![u, v] i := by rw [hb]
      rw [hbi]
      fin_cases i <;> simp [hu', hv']
    have hfun : m.mulVec = (c • (1 : Matrix (Fin 2) (Fin 2) F)).mulVec := by
      funext x
      have hx := DFunLike.congr_fun hmap x
      simpa [Matrix.smul_mulVec, Matrix.one_mulVec] using hx
    exact hm c (Matrix.mulVec_injective hfun)
  · -- Otherwise `v` is a scalar multiple of `u`; the scalar is non-zero because `u ≠ 0`.
    obtain ⟨a, ha⟩ : ∃ a : F, a • v = u := by
      by_contra hc
      exact hlin ((linearIndependent_fin2).mpr ⟨by simpa using hv, fun a h => hc ⟨a, h⟩⟩)
    have ha0 : a ≠ 0 := by
      intro h0
      exact hu (by rw [← ha, h0, zero_smul])
    exact ⟨Units.mk0 a ha0, by rw [Units.smul_def, Units.val_mk0, ha]⟩

end Work.L2F.Props.oddsub
