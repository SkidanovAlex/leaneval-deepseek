import Mathlib.Analysis.InnerProductSpace.PiL2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open scoped InnerProductSpace

/-- A finite-dimensional complex subspace `W ≤ E` of dimension at least `k` contains an
orthonormal family of `k` vectors (the first `k` vectors of an orthonormal basis of `W`). -/
theorem orthonormalComplex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (W : Submodule ℂ E) {k : ℕ} (hk : k ≤ Module.finrank ℂ ↥W) :
    ∃ e : Fin k → E, Orthonormal ℂ e ∧ ∀ j, e j ∈ W := by
  classical
  -- `↥W` is a finite-dimensional complex inner product space, so it has an orthonormal basis.
  let b := stdOrthonormalBasis ℂ ↥W
  refine ⟨fun j => (b (Fin.castLE hk j) : E), ?_, fun j => (b (Fin.castLE hk j)).2⟩
  rw [orthonormal_iff_ite]
  intro i j
  have h := (orthonormal_iff_ite.mp b.orthonormal) (Fin.castLE hk i) (Fin.castLE hk j)
  rw [Submodule.coe_inner] at h
  rw [h]
  simp only [Fin.castLE_inj]

end Work.BoseBoxFock
