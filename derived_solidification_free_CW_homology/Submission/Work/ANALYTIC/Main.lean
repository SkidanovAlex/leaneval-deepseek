import Mathlib
import ChallengeDeps
import Submission.Work.ANALYTIC.Basic
import Submission.Work.ANALYTIC.RealCond
import Submission.Work.ANALYTIC.Bounded
import Submission.Work.ANALYTIC.boundedSeq_sheaf
import Submission.Work.ANALYTIC.BoundedSeqC
import Submission.Work.ANALYTIC.cBounded_solidEquiv
import Submission.Work.ANALYTIC.scheme_bijective
import Submission.Work.ANALYTIC.solidNull_of_unit_action
import Submission.Work.ANALYTIC.exists_realNullSeq
import Submission.Work.ANALYTIC.preSolid_all
import Submission.Work.ANALYTIC.flat_P
import Submission.Work.FLAT.Main

/-!
# AREA ANALYTIC — homotopy invariance of `ℤ[-]` up to solid-equivalence

The deliverable of this area is `hi_prop : Submission.Blueprint.HIProp`, i.e. for every Hausdorff
space `Y` the map `ℤ[Y] ⟶ ℤ[Y × [0,1]]` (at `t = 0`) is a solid-equivalence.  This file collects
what is currently available of the area, in the shape in which the later steps use it.

## What is available

* `Work.ANALYTIC.scheme_bijective` (module `Submission.Work.ANALYTIC.scheme_bijective`) — the
  abstract *null-sequence scheme* of REFS/03 §1, together with the `SolidEquiv` form
  `Work.ANALYTIC.solidEquiv_of_scheme` below.  This is the engine of AN1/AN2/AN3.
* `Work.ANALYTIC.flat_P` — `tensorLeft P` preserves finite limits, from `FlatProp` (needed to build
  `(tensorLeft P).mapDerivedCategory`).
* `Work.ANALYTIC.realCond` — the light condensed abelian group `ℝ` (`S ↦ C(S,ℝ)`) with
  `realCond_obj_obj : realCond.obj.obj (op S) = C(S,ℝ)` and the free-Yoneda equivalence
  `freeHomEquiv : (ℤ[S] ⟶ M) ≃ M(S)`.
* `Work.ANALYTIC.solidNull_of_unit_action` — `Hom_D(V, ι N) = 0` for all `N : DSolid`, for a light
  condensed abelian group `V` carrying an action `R ⊗ V ⟶ V` with a unit along a null sequence
  `f : P ⟶ R` (REFS/03 §3, RC Thm 3.2.4(4)).
* `Work.ANALYTIC.solidNull_of_realModule` below — the same statement for an action of `ℝ`, in the
  exact form in which the applications (AN2 second half, AN3) use it.

## What is missing (the rest of the area)

The remaining steps, in dependency order, are

* **`preSolid_all`** (module `Submission.Work.ANALYTIC.preSolid_all`, dispatched):
  `PreSolid X` — precomposition with `(1-S) ⊗ id_X` is bijective on `Hom_D(P ⊗ X, ι N)` for all
  `N : DSolid` (REFS/01 F6–F7).  This is the only analytic input of the null-sequence tricks.  Once
  it is available, `PreSolid` hypotheses of the statements below can be discharged.
* **AN1** (REFS/03 §2): `c : P ⟶ ∏^bnd ℤ`, `e_n ↦ δ_n`, is a solid-equivalence.  Needs the object
  `∏^bnd ℤ` (uniformly bounded sequences) and the null-sequence scheme `solidEquiv_of_scheme` with
  `g = c`, `G = (x_k e_k)` (this is where boundedness of the sequences is used), and the maps
  `F = π_{≥k}`, `s = (0,-)`, `T = (1-S) ⊗ id`.
* **AN2 second half** (REFS/03 §3): `∏^bnd ℤ ⟶ ∏ℤ` is a solid-equivalence.  Route: the quotient
  `Q = ∏ℤ/∏^bnd ℤ` is isomorphic to `∏ℝ/∏^bnd ℝ` (from the exact sequences
  `0 → ∏ℤ → ∏ℝ → ∏ℝ/ℤ → 0` and `0 → ∏^bnd ℤ → ∏^bnd ℝ → ∏ℝ/ℤ → 0`), which is an `ℝ`-module
  object; `solidNull_of_realModule` then gives `Hom_D(Q, ι N) = 0`, and the long exact sequence
  together with `ToolkitProp` gives the solid-equivalence.
* **AN3** (REFS/03 §4): for light profinite `T`, `μ_T : ℤ[T] ⟶ ℤ■[T] = ihom(C(T,ℤ)_disc, ℤ)` is a
  solid-equivalence.  Route: the Haar/Schauder basis of `C(T,ℤ)` gives `ℤ■[T] ≅ ∏ℤ` with
  `μ_T ∘ g = ` the standard map `e_j ↦ δ_j`, so AN1 + AN2 (2-out-of-3, `ToolkitProp.comp`) finish.
* **AN4** (REFS/04 §1): exactness of the augmented Čech complex `0 → ℤ → C(C_0,ℤ) → C(C_1,ℤ) → ⋯`
  of the Cantor cover `C = {0,1}^ℕ → [0,1]`, via the dyadic nerves `N_n^{(p)}` and filtered colimits;
  Künneth `C(S × C_p, ℤ) = C(S,ℤ) ⊗ C(C_p,ℤ)` gives contractibility for free groups.
* **AN5** (REFS/04 §2): `ℤ[S × [0,1]] ⟶ ℤ[S]` is a solid-equivalence for light profinite `S`,
  using the Čech resolution `R_•`, the naturality of `μ` and `ToolkitProp.levelwise`.
* **AN6** (REFS/04 §3): the same for Hausdorff `Y`, using the Čech nerve of `⊔_{S ∈ 𝒮, S → Y} S → Y`
  (disjoint unions of light profinite sets, using that `Y` is Hausdorff), `ToolkitProp.sigma` and
  `ToolkitProp.levelwise`, and finally 2-out-of-3 (`pr ∘ i₀ = id`) to get `HIProp`.

## The deliverable `hi_prop`

`Work.ANALYTIC.hi_prop : Submission.Blueprint.HIProp` lives in the module
`Submission.Work.ANALYTIC.hi_prop` (file `Submission/Work/ANALYTIC/hi_prop.lean`) — **import that
module** (or `Submission.Work.ANALYTIC.Main` plus it).  It cannot be re-exported from this file
because its proof uses `Work.ANALYTIC.toolkitProp` and `solidNull_of_realModule'` etc. through
`MuT`/`Unconditional`, which themselves import this module; there is no circularity in importing
`Submission.Work.ANALYTIC.hi_prop` directly.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-! ## The `SolidEquiv` form of the null-sequence scheme -/

/-- The null-sequence scheme of REFS/03 §1 in the form used by the areas of this project:
given precomposition bijectivities for `T` and `T'` (i.e. `SolidEquiv T`, `SolidEquiv T'`) and the
seven identities of the scheme, precomposition with `g` is a solid-equivalence. -/
theorem solidEquiv_of_scheme {A A' B X : DLightCondAb}
    (g : B ⟶ X) (F : A ⟶ X) (s : X ⟶ A) (G : A ⟶ B) (T : A ⟶ A)
    (F' : A' ⟶ B) (s' : B ⟶ A') (T' : A' ⟶ A') (m : A' ⟶ A)
    (h₁ : T ≫ F = G ≫ g) (h₂ : s ≫ F = 𝟙 X) (h₃ : m ≫ F = F' ≫ g)
    (h₄ : m ≫ G = T' ≫ F') (h₅ : g ≫ s = s' ≫ m) (h₆ : m ≫ T = T' ≫ m)
    (h₇ : s' ≫ F' = 𝟙 B)
    (hT : Submission.Blueprint.SolidEquiv T) (hT' : Submission.Blueprint.SolidEquiv T') :
    Submission.Blueprint.SolidEquiv g :=
  fun N => scheme_bijective g F s G T F' s' T' m h₁ h₂ h₃ h₄ h₅ h₆ h₇ (hT N) (hT' N)

/-! ## AN1: the null sequence `c : P ⟶ ∏^bnd ℤ` is a solid-equivalence -/

/-- **AN1 (REFS/03 §2)**, in the form in which the rest of the area uses it: the map
`cBounded : P ⟶ ∏^bnd ℤ`, `e_n ↦ δ_n` (`Submission/Work/ANALYTIC/BoundedSeqC.lean`) induces a
bijection on `Hom(-, derivedInclusion.obj N)` for every `N : DSolid`. -/
theorem solidEquiv_cBounded [PreservesFiniteLimits (tensorLeft _root_.LightCondensed.P)] :
    Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map cBounded) :=
  cBounded_solidEquiv

/-! ## ℝ-module objects are solid-null

(AN2, the inclusion `∏^bnd ℤ ⟶ ∏ℤ`, is proved in `Submission/Work/ANALYTIC/boundedSeqIncl_solidEquiv.lean`,
whose proof uses `solidNull_of_realModule'` below; import that module directly for AN2.) -/

/-- **ℝ-module objects are solid-null** (REFS/03 §3, RC Thm 3.2.4(4)): if a light condensed abelian
group `V` carries an action of `ℝ` which is unital for the unit map `u` (i.e. `(u ▷ V) ≫ act` is
the unitor), and if the parametrised null sequence of REFS/03 §3 realises `u` as `e₀ ≫ f`, then
`Hom_D(V, ι N) = 0` for every complex `N` of solid objects.

The existence of the null-sequence data with `e₀ ≫ f = u` is
`Work.ANALYTIC.exists_realNullSeq` (module `Submission.Work.ANALYTIC.exists_realNullSeq`), and the
`PreSolid V` hypothesis is discharged by `Work.ANALYTIC.preSolid_all` (module
`Submission.Work.ANALYTIC.preSolid_all`) together with `Work.ANALYTIC.flat_P`. -/
theorem solidNull_of_realModule (V : LightCondAb) (act : realCond ⊗ V ⟶ V)
    (u : 𝟙_ LightCondAb ⟶ realCond)
    (hu : (u ▷ V) ≫ act = (λ_ V).hom)
    (h : ∃ (f : P ⟶ realCond) (F G : P ⟶ P) (e₀ e₁ : 𝟙_ LightCondAb ⟶ P),
      (F ≫ f = f) ∧ (F ≫ oneMinusShift = oneMinusShift ≫ G) ∧ (e₀ ≫ G = e₁) ∧
      (e₀ ≫ oneMinusShift = e₀ - e₁) ∧ (e₀ ≫ f = u))
    (hpre : PreSolid V) :
    SolidNull ((DerivedCategory.singleFunctor LightCondAb 0).obj V) := by
  obtain ⟨f, F, G, e₀, e₁, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine solidNull_of_unit_action realCond V act f F G e₀ e₁ h₁ h₂ h₃ h₄ ?_ hpre
  rw [← Category.assoc, ← comp_whiskerRight, h₅, hu]

/-- **ℝ-module objects are solid-null**, unconditional form: the `PreSolid` input is discharged
using `Work.ANALYTIC.preSolid_all` and `Work.ANALYTIC.flat_P` (from `FlatProp`), and the null
sequence with `e₀ ≫ f = u` is provided by `Work.ANALYTIC.exists_realNullSeq`. -/
theorem solidNull_of_realModule' (hflat : Submission.Blueprint.FlatProp) (V : LightCondAb)
    (act : realCond ⊗ V ⟶ V) (u : 𝟙_ LightCondAb ⟶ realCond)
    (hu : (u ▷ V) ≫ act = (λ_ V).hom)
    (h : ∃ (f : P ⟶ realCond) (F G : P ⟶ P) (e₀ e₁ : 𝟙_ LightCondAb ⟶ P),
      (F ≫ f = f) ∧ (F ≫ oneMinusShift = oneMinusShift ≫ G) ∧ (e₀ ≫ G = e₁) ∧
      (e₀ ≫ oneMinusShift = e₀ - e₁) ∧ (e₀ ≫ f = u)) :
    SolidNull ((DerivedCategory.singleFunctor LightCondAb 0).obj V) := by
  haveI : PreservesFiniteLimits (tensorLeft P) := flat_P hflat
  exact solidNull_of_realModule V act u hu h (preSolid_all V)

/-! ## Unconditional forms (area FLAT supplies `FlatProp`) -/

/-- **`FlatProp` holds**, proved in area FLAT. -/
theorem flatProp : Submission.Blueprint.FlatProp := _root_.Work.FLAT.flat_prop

/-- `tensorLeft P` preserves finite limits, unconditionally. -/
theorem flat_P_unconditional :
    PreservesFiniteLimits (tensorLeft _root_.LightCondensed.P) :=
  flat_P flatProp

/-- **The F7 input (REFS/01 F6–F7), unconditionally.** -/
theorem preSolid (X : LightCondAb) : PreSolid X :=
  haveI := flat_P_unconditional
  preSolid_all X

/-- **AN1, unconditionally.** -/
theorem solidEquiv_cBounded' :
    Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map cBounded) :=
  haveI := flat_P_unconditional
  solidEquiv_cBounded

/-- **ℝ-module objects are solid-null, unconditionally** (given the null-sequence data). -/
theorem solidNull_of_realModule_uncond (V : LightCondAb) (act : realCond ⊗ V ⟶ V)
    (u : 𝟙_ LightCondAb ⟶ realCond)
    (hu : (u ▷ V) ≫ act = (λ_ V).hom)
    (h : ∃ (f : P ⟶ realCond) (F G : P ⟶ P) (e₀ e₁ : 𝟙_ LightCondAb ⟶ P),
      (F ≫ f = f) ∧ (F ≫ oneMinusShift = oneMinusShift ≫ G) ∧ (e₀ ≫ G = e₁) ∧
      (e₀ ≫ oneMinusShift = e₀ - e₁) ∧ (e₀ ≫ f = u)) :
    SolidNull ((DerivedCategory.singleFunctor LightCondAb 0).obj V) :=
  solidNull_of_realModule' flatProp V act u hu h

end Work.ANALYTIC
