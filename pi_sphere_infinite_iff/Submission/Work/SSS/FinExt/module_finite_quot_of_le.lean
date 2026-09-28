import Mathlib
import Submission.Work.SSS.FgQuotBasic

namespace Work.SSS.FinExt

attribute [-instance] AddCommGroup.toIntModule

/-- If `A ≤ B` are submodules of a `ℤ`-module `M` and both `B/A` and `M/B` are finitely generated,
then so is `M/A`.  (The `attribute` line above is required for this statement to elaborate: for
`ℤ`-modules there are two definitionally distinct `Module ℤ` structures on subtypes and quotients.) -/
theorem module_finite_quot_of_le
    {M : Type*} [AddCommGroup M] [Module ℤ M] (A B : Submodule ℤ M) (h : A ≤ B)
    (hk : Module.Finite ℤ (↥B ⧸ Submodule.comap B.subtype A))
    (hMB : Module.Finite ℤ (M ⧸ B)) : Module.Finite ℤ (M ⧸ A) := by
  -- The hypothesis `hk` says precisely that `B / (B ⊓ A)` is finitely generated; the composite
  -- `φ : B → M ⧸ A` realises `B / (B ⊓ A) ≅ B.A` where `B.A` is the image of `B` in `M ⧸ A`.
  have hAB : Work.SSS.FgQuot A B := by
    let φ : ↥B →ₗ[ℤ] (M ⧸ A) := (Submodule.mkQ A).comp B.subtype
    have hker : LinearMap.ker φ = Submodule.comap B.subtype A := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    have hrange : φ.range = B.map (Submodule.mkQ A) := by
      ext x
      rw [LinearMap.mem_range, Submodule.mem_map]
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨y, y.2, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
    have hk' : Module.Finite ℤ (↥B ⧸ LinearMap.ker φ) := by
      rw [hker]
      exact hk
    have hfin : Module.Finite ℤ ↥(φ.range) :=
      (Module.Finite.equiv_iff (LinearMap.quotKerEquivRange φ)).mp hk'
    have h1 : (φ.range).FG := Module.Finite.iff_fg.mp hfin
    show (B.map (Submodule.mkQ A)).FG
    rwa [← hrange]
  -- `M ⧸ B` finitely generated is `FgQuot B ⊤`.
  have hBM : Work.SSS.FgQuot B ⊤ := by
    show ((⊤ : Submodule ℤ M).map (Submodule.mkQ B)).FG
    rw [Submodule.map_top, Submodule.range_mkQ]
    exact Module.finite_def.mp hMB
  -- Extension of finitely generated quotients.
  have hA : Work.SSS.FgQuot A ⊤ :=
    Work.SSS.FgQuot.of_le_of_le (le_top : B ≤ ⊤) hAB hBM
  rw [Module.finite_def]
  have htop : (⊤ : Submodule ℤ (M ⧸ A)) = (⊤ : Submodule ℤ M).map (Submodule.mkQ A) := by
    rw [Submodule.map_top, Submodule.range_mkQ]
  rw [htop]
  exact hA

end Work.SSS.FinExt
