import Mathlib
import Submission.Work.ANALYTIC.BoundedSeqC
import Submission.Work.ANALYTIC.scheme_bijective
import Submission.Work.ANALYTIC.preSolid_all
import Submission.Work.ANALYTIC.boundedSeq_sheaf
import Submission.Work.ATOM.Toolkit.EA
import Submission.Work.ATOM.zfreeTensorIso_natural
import Submission.Work.DISC.sections_disc
import Submission.Work.DISC.Defs
import Submission.Work.REFL.Basic
import Submission.Work.REFL.pre_app_points
import Submission.Work.ATOM.Toolkit.PS_desc
import Submission.Work.ATOM.Toolkit.PP_desc
import Submission.Work.ANALYTIC.EA_natural
import Submission.Work.ANALYTIC.EA_shift
import Submission.Work.ANALYTIC.exists_pairMor
import Submission.Work.ANALYTIC.whiskerRight_sub_lightCondMod
import Submission.Work.ANALYTIC.primedFamily
import Submission.Work.ANALYTIC.exists_tower_F_EAdata
import Submission.Work.ANALYTIC.gSetup
import Submission.Work.ANALYTIC.qElem_cBounded
import Submission.Work.ANALYTIC.genPointsExt
import Submission.Work.ANALYTIC.h3_identity
import Submission.Work.ANALYTIC.exists_Gtower_h1_h4

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open Opposite
open OnePoint

set_option backward.isDefEq.respectTransparency false

noncomputable section

open _root_.LightCondensed _root_.LightCondensed.Solid

/-! ## The maps of the null-sequence scheme of REFS/03 §2 (AN1)

We record here the *cheap* part of the data of REFS/03 §2: the point `e₀ : 𝟙_ ⟶ P`, the sections
`s : ∏^bnd ℤ ⟶ P ⊗ ∏^bnd ℤ` and `s' : P ⟶ P ⊗ P` (both `e₀ ⊗ -`), and the map
`m = id_P ⊗ cBounded`, together with the two identities `h₅`, `h₆` of the scheme, which are formal
consequences of `whisker_exchange`.  The remaining data (`F`, `G`, `F'`) are the null families of
REFS/03 §2 and are built from the explicit sections of `∏^bnd ℤ` below. -/

/-- The point `e_k : 𝟙_ ⟶ P`, the class of the point `k` of `ℕ∪∞` (so `e_k ≫ cBounded = δ_k`). -/
noncomputable def ePoint (k : ℕ) : 𝟙_ LightCondAb ⟶ P :=
  Work.ATOM.unitIso.hom ≫ (Work.ATOM.zmap (Work.ATOM.ptAt (OnePoint.some k)) ≫ P_proj)

/-- The section `s : ∏^bnd ℤ ⟶ P ⊗ ∏^bnd ℤ` of REFS/03 §2, `x ↦ e₀ ⊗ x`. -/
noncomputable def sBounded : boundedSeq ⟶ P ⊗ boundedSeq :=
  (λ_ boundedSeq).inv ≫ (ePoint 0 ▷ boundedSeq)

/-- The section `s' : P ⟶ P ⊗ P` (the primed analogue of `s`), `z ↦ e₀ ⊗ z`. -/
noncomputable def sPrime : P ⟶ P ⊗ P :=
  (λ_ P).inv ≫ (ePoint 0 ▷ P)

/-- The map `m = id_P ⊗ cBounded : P ⊗ P ⟶ P ⊗ ∏^bnd ℤ`. -/
noncomputable def mMap : P ⊗ P ⟶ P ⊗ boundedSeq :=
  P ◁ cBounded

/-- The section `s` is compatible with `g` and `s'`, `m`: this is identity `h₅` of REFS/03 §1. -/
theorem h5_scheme : cBounded ≫ sBounded = sPrime ≫ mMap := by
  have h1 : cBounded ≫ (λ_ boundedSeq).inv = (λ_ P).inv ≫ (𝟙_ LightCondAb ◁ cBounded) := by
    rw [id_whiskerLeft]
    simp
  show cBounded ≫ ((λ_ boundedSeq).inv ≫ (ePoint 0 ▷ boundedSeq)) =
    ((λ_ P).inv ≫ (ePoint 0 ▷ P)) ≫ (P ◁ cBounded)
  rw [← Category.assoc, h1, Category.assoc, whisker_exchange, Category.assoc]

/-- The map `m` intertwines `(1 - S) ⊗ id` on the two factors: identity `h₆` of REFS/03 §1. -/
theorem h6_scheme :
    mMap ≫ tensorOneMinusShift boundedSeq = tensorOneMinusShift P ≫ mMap :=
  whisker_exchange oneMinusShift cBounded

/-! ## The elementary endomorphisms of `∏^bnd ℤ`

Because the sections of `boundedSeq` are *definitionally* the uniformly bounded families
(`boundedSeq_obj_obj`), a morphism `∏^bnd ℤ ⟶ ∏^bnd ℤ` can be written down on sections and its
naturality is typically `rfl`.  This is the cheapest way to produce the maps of REFS/03 §2 on the
`∏^bnd ℤ` side. -/

/-- The `k`-th truncation `π_{≥k}` of a bounded family: `(π_{≥k}x)_n = x_n·[n ≥ k]`. -/
def truncEnd (k : ℕ) : boundedSeq ⟶ boundedSeq :=
  ObjectProperty.homMk
    { app := fun S => ModuleCat.ofHom
        { toFun := fun x =>
            ⟨fun n => ⟨fun s => x.1 n s * (if k ≤ n then (1 : ℤ) else 0), by
                refine Continuous.mul (x.1 n).continuous continuous_const ⟩,
             ⟨Classical.choose x.2, fun n s => by
                have h := Classical.choose_spec x.2 n s
                have hle : (if k ≤ n then (1 : ℤ) else 0) ≤ 1 := by split <;> norm_num
                have hnn : (0 : ℤ) ≤ (if k ≤ n then (1 : ℤ) else 0) := by split <;> norm_num
                calc |x.1 n s * (if k ≤ n then (1 : ℤ) else 0)|
                    = |x.1 n s| * |(if k ≤ n then (1 : ℤ) else 0)| := abs_mul _ _
                  _ ≤ |x.1 n s| * 1 := by
                        exact mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg hnn]; exact hle)
                          (abs_nonneg _)
                  _ = |x.1 n s| := mul_one _
                  _ ≤ Classical.choose x.2 := h ⟩⟩
          map_add' := by
            intro a b
            apply Subtype.ext
            funext n
            apply ContinuousMap.ext
            intro s
            simp only [Submodule.coe_add, Pi.add_apply, ContinuousMap.coe_mk,
              ContinuousMap.add_apply]
            ring
          map_smul' := by
            intro c a
            apply Subtype.ext
            funext n
            apply ContinuousMap.ext
            intro s
            simp only [Submodule.coe_smul, Pi.smul_apply, ContinuousMap.coe_mk,
              ContinuousMap.smul_apply, RingHom.id_apply, smul_eq_mul]
            ring }
      naturality := by
        intro S T f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        funext n
        apply ContinuousMap.ext
        intro s
        rfl }

/-- The value of the `k`-th truncation on sections (by definition). -/
theorem truncEnd_apply (k : ℕ) (S : (LightProfinite.{0})ᵒᵖ)
    (x : ↥(boundedSeq.obj.obj S)) (n : ℕ) (s : ↥(S.unop.toTop)) :
    ((truncEnd k).hom.app S x).1 n s = x.1 n s * (if k ≤ n then (1 : ℤ) else 0) := rfl

/-- **The assembly of AN1 from the two null-sequence towers of REFS/03 §2.**  If `F`, `G`, `F'`
satisfy the five non-formal identities of the scheme of REFS/03 §1 (the other two are
`h5_scheme` and `h6_scheme`), then `cBounded` is a solid-equivalence: this is
`scheme_bijective` with the two null-sequence hypotheses discharged by `preSolid_all`. -/
theorem solidEquiv_of_towerData
    [PreservesFiniteLimits (tensorLeft P)]
    (F : P ⊗ boundedSeq ⟶ boundedSeq) (G : P ⊗ boundedSeq ⟶ P) (F' : P ⊗ P ⟶ P)
    (h₁ : tensorOneMinusShift boundedSeq ≫ F = G ≫ cBounded)
    (h₂ : sBounded ≫ F = 𝟙 boundedSeq)
    (h₃ : mMap ≫ F = F' ≫ cBounded)
    (h₄ : mMap ≫ G = tensorOneMinusShift P ≫ F')
    (h₇ : sPrime ≫ F' = 𝟙 P) :
    IsBoundedSeqSolidEquiv boundedSeq cBounded := by
  intro N
  exact scheme_bijective (C := DLightCondAb)
    ((DerivedCategory.singleFunctor LightCondAb 0).map cBounded)
    ((DerivedCategory.singleFunctor LightCondAb 0).map F)
    ((DerivedCategory.singleFunctor LightCondAb 0).map sBounded)
    ((DerivedCategory.singleFunctor LightCondAb 0).map G)
    ((DerivedCategory.singleFunctor LightCondAb 0).map (tensorOneMinusShift boundedSeq))
    ((DerivedCategory.singleFunctor LightCondAb 0).map F')
    ((DerivedCategory.singleFunctor LightCondAb 0).map sPrime)
    ((DerivedCategory.singleFunctor LightCondAb 0).map (tensorOneMinusShift P))
    ((DerivedCategory.singleFunctor LightCondAb 0).map mMap)
    (by
      have h := congrArg ((DerivedCategory.singleFunctor LightCondAb 0).map) h₁
      simpa only [Functor.map_comp] using h)
    (by rw [← Functor.map_comp, h₂]; simp)
    (by
      have h := congrArg ((DerivedCategory.singleFunctor LightCondAb 0).map) h₃
      simpa only [Functor.map_comp] using h)
    (by
      have h := congrArg ((DerivedCategory.singleFunctor LightCondAb 0).map) h₄
      simpa only [Functor.map_comp] using h)
    (by
      have h := congrArg ((DerivedCategory.singleFunctor LightCondAb 0).map) h5_scheme
      simpa only [Functor.map_comp] using h)
    (by
      have h := congrArg ((DerivedCategory.singleFunctor LightCondAb 0).map) h6_scheme
      simpa only [Functor.map_comp] using h)
    (by rw [← Functor.map_comp, h₇]; simp)
    (preSolid_all boundedSeq N) (preSolid_all P N)

/-- **AN1 (REFS/03 §2).**  The null sequence `cBounded : P ⟶ ∏^bnd ℤ`, `e_n ↦ δ_n`
(`Submission/Work/ANALYTIC/BoundedSeqC.lean`) is a solid-equivalence.

Use the abstract scheme `Work.ANALYTIC.scheme_bijective` (module
`Submission.Work.ANALYTIC.scheme_bijective`) with
`C := boundedSeq` (`Bd`), `B := P`, `A := P ⊗ Bd`, `A' := P ⊗ P`, `g := cBounded`,
`T := tensorOneMinusShift Bd`, `T' := tensorOneMinusShift P`,
`m := (tensorLeft P).map cBounded : P ⊗ P ⟶ P ⊗ Bd`, and the following maps, each described by its
transpose "null family of endomorphisms" (a map `P ⊗ X ⟶ Y` is the same as a map `X ⟶ ihom P Y`,
whose `S`-points are elements of `Y((ℕ∪∞) × S)` vanishing on `{∞} × S`, cf. REFS/01 F10):

* `F : P ⊗ Bd ⟶ Bd`: the family of *truncations* `π_{≥k}` of uniformly bounded sequences,
  `(π_{≥k} x)_n = x_n · [n ≥ k]` for `k ∈ ℕ`, and `π_{≥∞} = 0`.  (Do **not** use the shift
  `x_{n+k}`.)
* `s : Bd ⟶ P ⊗ Bd`: the family `k ↦ x` for `k ∈ ℕ` and `k = ∞ ↦ 0`, i.e. `x ↦ e_0 ⊗ x` up to the
  identification — the section of `F` (`F(s x) = π_{≥0}x = x`).
* `G : P ⊗ Bd ⟶ P`: `(k, x) ↦ x_k e_k` (the `k`-th coordinate of the bounded family `x`, times the
  basis vector `e_k ∈ P`); boundedness of the sequences is used exactly here.
* `F' : P ⊗ P ⟶ P`: the family `(k, e_j) ↦ e_j` if `j ≥ k` and `0` otherwise;
  `s' : P ⟶ P ⊗ P` with `F' ∘ s' = 𝟙 P`.

The seven identities of `scheme_bijective` are exactly those of REFS/03 §1 and should be checked on
the generators `e_k ⊗ x` (resp. `e_k ⊗ e_j`):
`T ≫ F = G ≫ g`, `s ≫ F = 𝟙 Bd`, `m ≫ F = F' ≫ g`, `m ≫ G = T' ≫ F'`,
`g ≫ s = s' ≫ m`, `m ≫ T = T' ≫ m`, `s' ≫ F' = 𝟙 P`.
The two hypotheses on `T` and `T'` are `PreSolid Bd` and `PreSolid P`, available from
`Work.ANALYTIC.preSolid_all` (module `Submission.Work.ANALYTIC.preSolid_all`) given the instance
`PreservesFiniteLimits (tensorLeft P)` (from `Work.ANALYTIC.flat_P` plus `FlatProp`; it is part of
this statement).  Here `PreSolid X` is by definition `SolidEquiv ((single 0).map (tensorOneMinusShift X))`.
The conclusion `IsBoundedSeqSolidEquiv boundedSeq cBounded` is definitionally
`SolidEquiv ((single 0).map cBounded)`, i.e. exactly `scheme_bijective` with
`D := derivedInclusion.obj N` for each `N : DSolid`. -/
theorem cBounded_solidEquiv
    [PreservesFiniteLimits (tensorLeft _root_.LightCondensed.P)] :
    IsBoundedSeqSolidEquiv boundedSeq cBounded := by
  obtain ⟨G, h1, h4⟩ := exists_Gtower_h1_h4
  have h2 : sBounded ≫ truncF = 𝟙 boundedSeq := by
    rw [show sBounded = sBoundedZ from rfl]
    apply hom_eq_of_zfree_comp_eq
    intro S g
    simpa only [Category.comp_id] using comp_sBoundedZ_truncF S g
  exact solidEquiv_of_towerData truncF G FP h1 h2 h3_identity h4 h7_scheme

end

end Work.ANALYTIC
