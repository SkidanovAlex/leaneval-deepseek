import Mathlib
import Submission.Work.Pi6.EMZ.Defs
import Submission.Work.SSS.ExpTensLES
import Submission.Work.SSS.singularCoeffFG
import Submission.Work.StemsB.sphRatHomology
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-!
# AREA EMZ — the coefficient vocabulary of the integral-table argument

This file fixes the objects of the mod-`p` Bockstein long exact sequence
(`Work.Pi6.EMZ.BocksteinLES`, proved in `Submission/Work/Pi6/EMZ/bocksteinLES.lean`):

* the coefficient modules `zZ = ℤ` and `Mp p = ℤ/p` (as `ℤ`-modules) and the coefficient short
  complex `coeffSES p : 0 → ℤ --·p--> ℤ --red--> ℤ/p → 0`;
* the singular chain complexes of a space and the chain complex short complex
  `expTensShort (chZ X) (coeffSES p) : 0 → C_*(X;ℤ) --·p--> C_*(X;ℤ) --red--> C_*(X;ℤ/p) → 0`
  (with `C_*(X;ℤ/p)` read over `ℤ`);
* the two identifications of the homology of the terms of this short complex with the homology of
  the space: `expTensUnitHomologyIso` (the `ℤ`-coefficient term) and `expTensCoeffAddEquiv`
  (the `ℤ/p`-coefficient term, using restriction of scalars along `ℤ → ℤ/p`).

The long exact sequence itself is assembled in `bocksteinLES.lean` from
`Work.SSS.expTensShort_shortExact` (short exactness, chains being degreewise free),
`ShortComplex.ShortExact.homology_exact₁/₂/₃` (the homology sequence) and the two identifications
above.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

namespace Work.Pi6.EMZ

noncomputable section

/-! ## The coefficient modules and the coefficient short complex -/

/-- `ℤ` as a `ℤ`-module (the unit of the monoidal structure on `ModuleCat ℤ`). -/
abbrev zZ : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-- `ℤ/p` as a `ℤ`-module. -/
abbrev Mp (p : ℕ) : ModuleCat ℤ := ModuleCat.of ℤ (ZMod p)

/-- `ℤ/p` as a `ℤ/p`-module. -/
abbrev RpI (p : ℕ) : ModuleCat (ZMod p) := ModuleCat.of (ZMod p) (ZMod p)

/-- Multiplication by `p` on `ℤ`, as an endomorphism of the coefficient module. -/
def mulP (p : ℕ) : zZ ⟶ zZ := (p : ℤ) • 𝟙 zZ

/-- The reduction `ℤ → ℤ/p`, `x ↦ x · 1`. -/
def redP (p : ℕ) : zZ ⟶ Mp p :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (ZMod p) (1 : ZMod p))

@[simp]
lemma mulP_hom_apply (p : ℕ) (x : zZ) : (mulP p).hom x = (p : ℤ) • x := rfl

@[simp]
lemma redP_hom_apply (p : ℕ) (x : zZ) :
    (redP p).hom x = ((x : ℤ) : ZMod p) := by
  rw [show (redP p).hom x = (LinearMap.toSpanSingleton ℤ (ZMod p) (1 : ZMod p)) x from rfl,
    LinearMap.toSpanSingleton_apply]
  simp [zsmul_eq_mul]

lemma mulP_comp_redP (p : ℕ) : mulP p ≫ redP p = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply, LinearMap.zero_apply,
    mulP_hom_apply, map_zsmul, redP_hom_apply]
  simp

/-- The mod-`p` coefficient short complex `0 → ℤ --·p--> ℤ --red--> ℤ/p → 0`. -/
def coeffSES (p : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (mulP p) (redP p) (mulP_comp_redP p)

/-! ## The singular chains and the short complex of chain complexes -/

/-- The singular simplicial set of a space. -/
abbrev sing (X : Type) [TopologicalSpace X] : SSet := TopCat.toSSet.obj (TopCat.of X)

/-- The integral singular chain complex of a space. -/
abbrev chZ (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat ℤ) ℕ :=
  (sing X).chainComplex zZ

/-- The integral singular chain complex is degreewise free, hence flat. -/
theorem chZ_flat (X : Type) [TopologicalSpace X] (n : ℕ) :
    Module.Flat ℤ ((chZ X).X n) := by
  haveI : Module.Free ℤ ↥((chZ X).X n) := Work.SSS.sChains_free (sing X) n
  exact Module.Flat.of_free

/-- The mod-`p` coefficient short complex of singular chain complexes
`0 → C_*(X;ℤ) --·p--> C_*(X;ℤ) --red--> C_*(X;ℤ/p) → 0`, the last term read over `ℤ`.

The objects are given explicitly so that `X₁` and `X₂` are the *same* term
`expTens (chZ X) zZ`; the morphisms are then definitionally those of
`expTensShort (chZ X) (coeffSES p)`, from which the short exactness is taken. -/
abbrev bockSES (p : ℕ) (X : Type) [TopologicalSpace X] :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (X₁ := Work.SSS.expTens (chZ X) zZ) (X₂ := Work.SSS.expTens (chZ X) zZ)
    (X₃ := Work.SSS.expTens (chZ X) (Mp p))
    (Work.SSS.expTensHom (chZ X) (mulP p)) (Work.SSS.expTensHom (chZ X) (redP p))
    (Work.SSS.expTensShort (chZ X) (coeffSES p)).zero

/-- The morphisms of `bockSES` are those of `expTensShort (chZ X) (coeffSES p)`. -/
theorem bockSES_shortExact (p : ℕ) (hp : p.Prime) (X : Type) [TopologicalSpace X]
    (h : (coeffSES p).ShortExact) : (bockSES p X).ShortExact :=
  Work.SSS.expTensShort_shortExact (K := chZ X) (coeffSES p) h (chZ_flat X)

/-- Multiplication by an integer on the identity morphism of a `ℤ`-module, evaluated. -/
theorem smul_id_hom_apply (c : ℤ) (M : ModuleCat ℤ) (y : ↥M) :
    ((c • 𝟙 M).hom) y = c • y := by
  simp [ModuleCat.hom_smul]

/-! ## The `ℤ`-coefficient identification

`expTens K ℤ ≅ K` is `Work.SSS.expTensUnitIso`; on homology this identifies the first term of the
Bockstein sequence with `H_n(X;ℤ)`. -/

/-- The homology of the `ℤ`-coefficient term of the Bockstein short complex is `H_n(X;ℤ)`. -/
def expTensUnitHomologyIso (X : Type) [TopologicalSpace X] (n : ℕ) :
    (Work.SSS.expTens (chZ X) zZ).homology n ≅ Work.Pi6.HR ℤ X n :=
  HomologicalComplex.homologyMapIso (Work.SSS.expTensUnitIso (chZ X)) n

/-! ## The `ℤ/p`-coefficient identification

`H_n(X;ℤ/p)`, computed with `ℤ/p` as an abelian group (`Work.SSS.HZCoeff`), is the same as the
homology of the `ℤ/p`-coefficient chain complex read as a complex of `ℤ`-modules by restriction of
scalars (`Work.StemsB.SphRat.chainBaseChange`-style), because restriction of scalars does not
change the underlying complex. -/

/-- The coefficient object of `ModuleCat.restrictScalars (Int.castRingHom 𝕜)` at `𝕜` is the
canonical `ℤ`-module `𝕜`: every `ℤ`-module structure on a fixed additive group is the same one. -/
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
a simplicial set `X`, read over `ℤ` by restriction of scalars along `ℤ → 𝕜`, has the same homology
as the complex with coefficients in the `ℤ`-module `𝕜`. -/
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
  have hmi : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homology q ≅
      F.obj (K.homology q) :=
    (Work.StemsB.SphRat.homologyMapBaseChange F K q).some
  exact ⟨(HomologicalComplex.homologyMapIso (cc.symm ≪≫ cb.symm) q) ≪≫ hmi⟩

/-- **The mod-`p` coefficient identification**: the homology of the last term of the Bockstein short
complex, with coefficients `ℤ/p` read over `ℤ`, is the mod-`p` homology `H_n(X;ℤ/p)`. -/
def expTensCoeffAddEquiv (p : ℕ) (hp : p.Prime) (X : Type) [TopologicalSpace X] (n : ℕ) :
    (Work.SSS.expTens (chZ X) (Mp p)).homology n ≃+ ↥(Work.Pi6.HR (ZMod p) X n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hca : ((sing X).chainComplex (Mp p)).homology n ≅
      (Work.SSS.expTens (chZ X) (Mp p)).homology n :=
    HomologicalComplex.homologyMapIso (Work.SSS.chainCoeffExpIso (sing X) (Mp p)) n
  let bc := (chainBaseChangeHomology (ZMod p) (sing X) n).some
  exact (Iso.toLinearEquiv (hca.symm ≪≫ bc)).toAddEquiv

end

end Work.Pi6.EMZ
