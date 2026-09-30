import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.SSS.singularCoeffFG
import Submission.Work.SSS.serreE2Defs
import Submission.Work.Cohomology.kronH_bijective_field
import Submission.Work.StemsB.sphRatHomology
import Submission.Work.StemsB.FieldDualUCT
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Finite type integral homology implies finite dimensional mod-`𝕜` cohomology

The target `Work.Pi6.EMODD.finDimField` is the finiteness input that the multiplicative Serre
spectral sequence (`Work.Pi6.MSSHolds`) asks of its two spaces: over a field `𝕜`, a space whose
integral homology is finitely generated in a range has finite dimensional `𝕜`-cohomology in that
range.

The mathematical content is assembled from three ingredients, each of which is a statement about
the singular (co)chain complex `C_*(X; R) = (TopCat.toSSet.obj X).chainComplex R`:

* **Coefficients.** If `H_i(X;ℤ)` is finitely generated for `i ≤ N`, the universal coefficient
  theorem in finiteness form (`Work.SSS.singularCoeffFG`, whose coefficient module here is `𝕜`
  regarded as a `ℤ`-module via `ModuleCat.of ℤ 𝕜`) makes `H_q(X; 𝕜)`, computed with `𝕜` as an
  *abelian group*, finitely generated as a `ℤ`-module.
* **Base change.** The `𝕜`-coefficient chain complex `C_*(X; 𝕜)`, viewed as a complex of abelian
  groups by restriction of scalars along `ℤ → 𝕜`, is the same complex
  (`Work.StemsB.SphRat.chainComplexBaseChange` for the functor `ModuleCat.restrictScalars`, plus
  `Work.StemsB.SphRat.chainCoeffIso` to change the coefficient object
  `(restrictScalars).obj 𝕜` into the canonical `ℤ`-module `𝕜`), so its homology is the same
  abelian group.  Every `ℤ`-module structure on a fixed additive group is the same one, so the
  finite generation of the previous step is exactly finite generation of the underlying abelian
  group of the `𝕜`-module `H_q(X; 𝕜)`; a generating set over `ℤ` then generates over `𝕜`.
* **Duality.** Over a field no finiteness hypothesis is needed for the universal coefficient
  theorem (`Work.StemsB.fieldDualUCT`): `H^q(X;𝕜) ≅ Hom_𝕜(H_q(X;𝕜), 𝕜)`.  The dual of a finitely
  generated `𝕜`-module is finitely generated (`Module.Finite.linearMap`), whence the result.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.EMODD

noncomputable section

/-! ## Changing the coefficient object of the restrict-of-scalars functor

`ModuleCat.restrictScalars (Int.castRingHom 𝕜) : ModuleCat 𝕜 ⥤ ModuleCat ℤ` carries the coefficient
object `ModuleCat.of 𝕜 𝕜` to the abelian group `𝕜` equipped with the `ℤ`-module structure
`z • x = (z : 𝕜) • x`, which is not *definitionally* the canonical `ℤ`-module structure of
`AddCommGroup.uniqueIntModule` that `ModuleCat.of ℤ 𝕜` carries.  The two structures coincide, and
below is the isomorphism of `ℤ`-modules between the two objects, together with the induced
isomorphism of chain complexes. -/

/-- The coefficient object of `ModuleCat.restrictScalars (Int.castRingHom 𝕜)` at `𝕜` is the
canonical `ℤ`-module `𝕜`.  Since every `ℤ`-module structure on a fixed additive group is the
canonical one, the underlying map of the isomorphism is the identity. -/
def restrictScalarsObjIntIso (𝕜 : Type) [Field 𝕜] :
    (ModuleCat.restrictScalars (Int.castRingHom 𝕜)).obj (ModuleCat.of 𝕜 𝕜) ≅
      ModuleCat.of ℤ 𝕜 :=
  LinearEquiv.toModuleIso <|
    @AddEquiv.toLinearEquiv _ _ _ _ _ _
      (((ModuleCat.restrictScalars (Int.castRingHom 𝕜)).obj (ModuleCat.of 𝕜 𝕜)).isModule) _
      (by rfl) (fun r x => by
        show ((r : 𝕜) • x : 𝕜) = r • x
        exact Int.cast_smul_eq_zsmul 𝕜 r x)

/-- **Base change for the singular chain complex.**  The `𝕜`-coefficient singular chain complex of
a simplicial set `X`, viewed as a complex of `ℤ`-modules by restriction of scalars along `ℤ → 𝕜`,
has the same homology as the complex with coefficients in the `ℤ`-module `𝕜` — because it literally
is that complex, up to the identification of the coefficient objects
`restrictScalarsObjIntIso`. -/
theorem chainBaseChangeHomology (𝕜 : Type) [Field 𝕜] (X : SSet) (q : ℕ) :
    Nonempty (((X.chainComplex (ModuleCat.of ℤ 𝕜)).homology q) ≅
      (ModuleCat.restrictScalars (Int.castRingHom 𝕜)).obj
        ((X.chainComplex (ModuleCat.of 𝕜 𝕜)).homology q)) := by
  let F : ModuleCat 𝕜 ⥤ ModuleCat ℤ := ModuleCat.restrictScalars (Int.castRingHom 𝕜)
  haveI h1 : ∀ (S : Type), PreservesColimitsOfShape (Discrete S) F := fun _ => inferInstance
  haveI h2 : F.Additive := inferInstance
  haveI h3 : F.PreservesHomology := inferInstance
  let K : ChainComplex (ModuleCat 𝕜) ℕ := X.chainComplex (ModuleCat.of 𝕜 𝕜)
  have cb : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ≅
      X.chainComplex (F.obj (ModuleCat.of 𝕜 𝕜)) :=
    Work.StemsB.SphRat.chainComplexBaseChange F X (ModuleCat.of 𝕜 𝕜)
  have cc : X.chainComplex (F.obj (ModuleCat.of 𝕜 𝕜)) ≅ X.chainComplex (ModuleCat.of ℤ 𝕜) :=
    Work.StemsB.SphRat.chainComplexCoeffIso X (restrictScalarsObjIntIso 𝕜)
  have hmi : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homology q ≅ F.obj (K.homology q) :=
    (Work.StemsB.SphRat.homologyMapBaseChange F K q).some
  exact ⟨(HomologicalComplex.homologyMapIso (cc.symm ≪≫ cb.symm) q) ≪≫ hmi⟩

/-! ## Finite generation over `ℤ` gives finite generation over `𝕜` -/

/-- **A finitely generated abelian group carrying a `𝕜`-module structure is a finitely generated
`𝕜`-module.**  A generating set over `ℤ` is a generating set over `𝕜`: every `ℤ`-multiple of an
element is the corresponding `𝕜`-multiple, because the two `ℤ`-module structures on a fixed
additive group coincide (`AddCommGroup.uniqueIntModule`). -/
theorem moduleFinite_of_restrictScalars (𝕜 : Type) [Field 𝕜] (N : ModuleCat 𝕜)
    (h : Module.Finite ℤ ↥((ModuleCat.restrictScalars (Int.castRingHom 𝕜)).obj N)) :
    Module.Finite 𝕜 ↥N := by
  have hmod : ((ModuleCat.restrictScalars (Int.castRingHom 𝕜)).obj N).isModule
      = AddCommGroup.toIntModule ↥N := Subsingleton.elim _ _
  rw [hmod] at h
  have hfg : (⊤ : Submodule ℤ ↥N).FG := h.fg_top
  rw [Submodule.fg_def] at hfg
  obtain ⟨s, hsfin, hs⟩ := hfg
  have key : ∀ y : ↥N, y ∈ Submodule.span ℤ s → y ∈ Submodule.span 𝕜 s := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span hz
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul z a _ ha =>
        show z • a ∈ Submodule.span 𝕜 s
        rw [(Int.cast_smul_eq_zsmul 𝕜 z a).symm]
        exact Submodule.smul_mem _ _ ha
  refine Module.Finite.of_fg_top (Submodule.fg_def.mpr ⟨s, hsfin, ?_⟩)
  apply le_antisymm le_top
  intro x _
  exact key x (by rw [hs]; trivial)

/-! ## The main theorem -/

/-- **Finitely generated integral homology gives finite dimensional mod-`𝕜` cohomology.** (Route: `Work.SSS.singularCoeffFG` with `M = 𝕜` makes `H_q(X;𝕜)` finitely generated over `ℤ`, hence over `𝕜`; the field universal coefficient theorem (`Work.StemsB.fieldDualUCT`, or `Work.Cohomology.kronH_bijective_field`) identifies `H^q(X;𝕜)` with the `𝕜`-dual of `H_q(X;𝕜)`.) -/
theorem finDimField (𝕜 : Type) [Field 𝕜] (h𝕜 : Module.Finite ℤ 𝕜) (X : Type) [TopologicalSpace X]
    (N : ℕ) (h : ∀ i : ℕ, i ≤ N → Module.Finite ℤ (Work.PiS.HZ X i)) :
    ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 X q) := by
  intro q hq
  let Y : TopCat := TopCat.of X
  let K : ChainComplex (ModuleCat 𝕜) ℕ := Work.Cohomology.singularChains 𝕜 Y
  -- `H_q(X; 𝕜)` with `𝕜` as an abelian group is finitely generated over `ℤ`.
  have hfg : Module.Finite ℤ (Work.SSS.HZCoeff X (ModuleCat.of ℤ 𝕜) q) :=
    Work.SSS.singularCoeffFG (ModuleCat.of ℤ 𝕜) q (h q hq) (h (q - 1) (by omega)) h𝕜
  -- ... hence so is the underlying abelian group of the `𝕜`-module `H_q(X; 𝕜)`.
  obtain ⟨eBC⟩ := chainBaseChangeHomology 𝕜 (TopCat.toSSet.obj Y) q
  have hfgA : Module.Finite ℤ
      ↥(((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℤ 𝕜)).homology q) := hfg
  have hfg' : Module.Finite ℤ
      ↥((ModuleCat.restrictScalars (Int.castRingHom 𝕜)).obj (K.homology q)) := by
    haveI := hfgA
    exact Module.Finite.equiv (Iso.toLinearEquiv eBC)
  have hfin : Module.Finite 𝕜 ↥(K.homology q) :=
    moduleFinite_of_restrictScalars 𝕜 (K.homology q) hfg'
  -- the `𝕜`-dual of a finitely generated module is finitely generated
  haveI := hfin
  have hdual : Module.Finite 𝕜 (↥(K.homology q) →ₗ[𝕜] 𝕜) :=
    Module.Finite.linearMap 𝕜 𝕜 ↥(K.homology q) 𝕜
  -- the field universal coefficient theorem
  obtain ⟨eUCT⟩ := Work.StemsB.fieldDualUCT 𝕜 K q
  have hcoh : Module.Finite 𝕜 ↥((Work.Cohomology.dualComplex 𝕜 K).homology q) :=
    Module.Finite.equiv (Iso.toLinearEquiv eUCT).symm
  exact hcoh

end

end Work.Pi6.EMODD
