import Mathlib
import Submission.Commons.Lattice.Minkowski.bounded_basis_of_bounded_realizers

open Module MeasureTheory Metric Set Submodule
open scoped ENNReal BigOperators
noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Commons.Lattice.Minkowski

/-! # A bounded `ℤ`-basis from bounded realisers (general inner product space)

A generalisation of `bounded_basis_of_bounded_realizers` from lattices in
`EuclideanSpace ℝ (Fin m)` to lattices in an arbitrary finite-dimensional real inner product
space `E`.  The proof transports the lattice to `EuclideanSpace ℝ (Fin m)` along the linear
isometry supplied by an orthonormal basis of `E` (all norms are preserved), applies the
Euclidean-space version of the theorem, and transports the resulting basis back.
-/

abbrev bbbrEu (m : ℕ) := EuclideanSpace ℝ (Fin m)

theorem bounded_basis_of_bounded_realizers_innerProductSpace {m : ℕ}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hfin : Module.finrank ℤ L = m) (v : Fin m → L)
    (hv : LinearIndependent ℝ (fun j : Fin m => (v j : E)))
    (R : ℝ) (hR0 : 0 ≤ R) (hvR : ∀ j : Fin m, ‖(v j : E)‖ ≤ R) :
    ∃ b : Module.Basis (Fin m) ℤ L,
      ∀ i : Fin m, ‖((b i : L) : E)‖ ≤ (2 * (m : ℝ) + 1) * R := by
  classical
  -- The ambient space has ℝ-dimension `m` because `L` is a full-rank `ℤ`-lattice.
  let hfinE : Module.finrank ℝ E = m := (ZLattice.rank ℝ L).symm.trans hfin
  -- An isometric linear equivalence `E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)` from an
  -- orthonormal basis of `E`.
  let isoE : E ≃ₗᵢ[ℝ] bbbrEu m := (stdOrthonormalBasis ℝ E).reindex (finCongr hfinE) |>.repr
  -- The transported lattice `L' = isoE(L)` in `EuclideanSpace ℝ (Fin m)`; as a pullback
  -- of `L` along the inverse isometry, it is again discrete and a `ℤ`-lattice.
  let eC : bbbrEu m ≃L[ℝ] E := isoE.symm.toContinuousLinearEquiv
  let L' : Submodule ℤ (bbbrEu m) := ZLattice.comap ℝ L eC.toLinearMap
  letI : DiscreteTopology L' := by
    dsimp [L']
    infer_instance
  letI : IsZLattice ℝ L' := by
    dsimp [L']
    infer_instance
  -- The `ℤ`-linear equivalence `L ≃ₗ[ℤ] L'` induced by the isometry (`x ↦ isoE x`).
  let φ : L ≃ₗ[ℤ] L' := ZLattice.comap_equiv ℝ L eC.toLinearEquiv
  -- The transported realisers.
  let v' : Fin m → L' := fun j => φ (v j)
  have hfin' : Module.finrank ℤ L' = m := by
    rw [ZLattice.rank ℝ L']
    have hb : Module.Basis (Fin m) ℝ (bbbrEu m) := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    rw [Module.finrank_eq_card_basis hb]
    simp
  -- Forward value formula for `φ`.
  have hφval (x : L) : ((φ x : L') : bbbrEu m) = isoE ((x : L) : E) := by
    dsimp [φ]
    rw [ZLattice.comap_equiv_apply]
    change isoE ((x : L) : E) = isoE ((x : L) : E)
    rfl
  have hval_v' (j : Fin m) : ((v' j : L') : bbbrEu m) = isoE ((v j : E)) := by
    dsimp [v']
    exact hφval (v j)
  -- The transported realisers remain `ℝ`-linearly independent.
  have hv' : LinearIndependent ℝ (fun j : Fin m => ((v' j : L') : bbbrEu m)) := by
    let f : E →ₗ[ℝ] bbbrEu m := isoE.toLinearEquiv.toLinearMap
    have hf : LinearMap.ker f = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      apply isoE.injective
      simpa [f] using hxy
    have hlin : LinearIndependent ℝ (fun j : Fin m => f ((v j : E))) := by
      simpa [Function.comp_def] using hv.map' f hf
    have hfam : (fun j : Fin m => ((v' j : L') : bbbrEu m)) =
        (fun j : Fin m => f ((v j : E))) := by
      funext j
      rw [hval_v' j]
      rfl
    rwa [hfam]
  -- The transported realisers are bounded by `R` (norms preserved by the isometry).
  have hvR' : ∀ j : Fin m, ‖((v' j : L') : bbbrEu m)‖ ≤ R := by
    intro j
    calc
      ‖((v' j : L') : bbbrEu m)‖ = ‖isoE ((v j : E))‖ := by rw [hval_v' j]
      _ = ‖((v j : L) : E)‖ := by simp
      _ ≤ R := hvR j
  -- The Euclidean-space version of the theorem provides a bounded basis of `L'`.
  obtain ⟨b', hb'⟩ := Commons.Lattice.Minkowski.bounded_basis_of_bounded_realizers (m := m) L'
    hfin' v' hv' R hR0 hvR'
  -- Value formula for the inverse equivalence.
  have hφsymmval (y : L') : ((φ.symm y : L) : E) = isoE.symm ((y : L') : bbbrEu m) := by
    have hy : φ (φ.symm y) = y := by simp
    have hvaleq : isoE ((φ.symm y : L) : E) = ((y : L') : bbbrEu m) := by
      rw [← hφval (φ.symm y)]
      exact congrArg (fun z : L' => (z : bbbrEu m)) hy
    have hh := congrArg (isoE.symm) hvaleq
    simpa using hh
  -- Transport the basis back to `L`.
  let b : Module.Basis (Fin m) ℤ L := b'.map φ.symm
  refine ⟨b, ?_⟩
  intro i
  have hb_map : (b i : L) = φ.symm (b' i) := by
    dsimp [b]
  have hval_b : ((b i : L) : E) = isoE.symm ((b' i : L') : bbbrEu m) := by
    rw [hb_map]
    exact hφsymmval (b' i)
  calc
    ‖((b i : L) : E)‖ = ‖isoE.symm ((b' i : L') : bbbrEu m)‖ := by rw [hval_b]
    _ = ‖((b' i : L') : bbbrEu m)‖ := by
      exact isoE.symm.norm_map ((b' i : L') : bbbrEu m)
    _ ≤ (2 * (m : ℝ) + 1) * R := hb' i

end Commons.Lattice.Minkowski
