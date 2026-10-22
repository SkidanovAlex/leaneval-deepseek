import Mathlib
import Submission.Work.ANALYTIC.CechPt.Setup

/-!
# The binary expansion `C = {0,1}^ℕ ⟶ [0,1]` is an epimorphism of light condensed sets

This file contains the proof of `Work.ANALYTIC.CechPt.binaryExp_epi`, the first input to the
Čech argument for the base case of homotopy invariance (see `CechPt/Setup.lean`).

The route is:

* the Cantor set `C = ∏ᶜ {0,1}` has coordinate projections `coord n : C ⟶ {0,1}`, and every
  digit sequence is realised by a point of `C` (`exists_coord_eq`);
* `Real.ofDigits` is continuous and surjective onto `[0,1]`
  (`Real.continuous_ofDigits`, `Real.ofDigits_SurjOn`), so the binary expansion
  `binExp : C ⟶ [0,1]`, `x ↦ ofDigits (fun n ↦ coord n x)` is a continuous surjection
  (`binExp_surjective`), i.e. an epimorphism in `TopCat` (`binExpHom_surjective`);
* the induced map `beta = ofDigits ∘ coord` is a morphism of light condensed sets
  `C ⟶ [0,1]` (where `C` is the representable sheaf of the site `LightProfinite` and `[0,1]`
  is the sheaf of continuous maps into `[0,1]`);
* it is an epimorphism because it is locally surjective: over any light profinite `S` and any
  continuous `y : S ⟶ [0,1]`, the fibre product `S ×_[0,1] C` is a light profinite set mapping
  onto `S`, and the tautological map to `C` lifts `y`.  Local surjectivity is
  `LightCondSet.epi_iff_locallySurjective_on_lightProfinite`.
-/

open CategoryTheory Limits LightProfinite LightCondensed
open scoped unitInterval

noncomputable section

namespace Work.ANALYTIC.CechPt

/-! ## The binary expansion as a continuous surjection -/

/-- `{0,1}` as a light profinite set. -/
abbrev two : LightProfinite := FintypeCat.toLightProfinite.obj (FintypeCat.of (Fin 2))

/-- `cantor` is the product of the constant family `{0,1}`. -/
abbrev twoFam : ℕ → LightProfinite := fun _ => two

/-- The `n`-th coordinate projection `C ⟶ {0,1}`. -/
abbrev coord (n : ℕ) : cantor ⟶ two := Pi.π twoFam n

/-- A one point light profinite set, used as cone point for the product structure of `cantor`. -/
abbrev pt : LightProfinite.{0} := ↧(Fin 1)

/-- Every digit sequence is realised by a point of the Cantor set: `cantor` is the limit of the
constant discrete diagram `{0,1}`. -/
lemma exists_coord_eq (d : ℕ → ↥two) : ∃ x : ↥cantor, ∀ n, (coord n).hom.hom x = d n := by
  classical
  let p : ∀ n, pt ⟶ two := fun n =>
    CompHausLike.ofHom _ (⟨fun _ => d n, continuous_const⟩ : C(↥pt, ↥two))
  let l : pt ⟶ cantor := Fan.IsLimit.lift (productIsProduct twoFam) p
  refine ⟨(l : ↥pt → ↥cantor) 0, fun n => ?_⟩
  have h2 : (ConcreteCategory.hom (l ≫ coord n) : C(↥pt, ↥two)) 0 = d n := by
    have h := Fan.IsLimit.fac (productIsProduct twoFam) p n
    have h3 : l ≫ coord n = p n := h
    rw [h3]
    rfl
  exact h2

/-- The binary expansion of a point of the Cantor set, as a function to `ℝ`, is continuous. -/
lemma continuous_ofDigits_coord :
    Continuous fun x : ↥cantor => Real.ofDigits (fun n => (coord n).hom.hom x) := by
  apply Real.continuous_ofDigits.comp
  exact continuous_pi fun n => (coord n).hom.hom.continuous

/-- The binary expansion `C ⟶ [0,1]`, `x ↦ Σ_n x_n / 2^{n+1}`. -/
def binExp (x : ↥cantor) : ↥unitInterval :=
  ⟨Real.ofDigits (fun n => (coord n).hom.hom x),
   ⟨Real.ofDigits_nonneg _, Real.ofDigits_le_one _⟩⟩

lemma binExp_continuous : Continuous binExp := by
  apply Continuous.subtype_mk
  exact continuous_ofDigits_coord

/-- The binary expansion is surjective: every `y ∈ [0,1]` has a binary expansion. -/
lemma binExp_surjective : Function.Surjective binExp := by
  intro y
  obtain ⟨d, -, hd⟩ := Real.ofDigits_SurjOn (b := 2) (by norm_num) y.2
  obtain ⟨x, hx⟩ := exists_coord_eq d
  refine ⟨x, Subtype.ext ?_⟩
  show Real.ofDigits (fun n => (coord n).hom.hom x) = y.1
  rw [funext hx, hd]

/-- The binary expansion as a morphism of topological spaces. -/
def binExpHom : cantor.toTop ⟶ TopCat.of unitInterval :=
  TopCat.ofHom ⟨binExp, binExp_continuous⟩

lemma binExpHom_surjective : Function.Surjective (binExpHom : ↥cantor.toTop → ↥unitInterval) :=
  fun y => binExp_surjective y

/-! ## The binary expansion as a morphism of light condensed sets -/

/-- The binary expansion as a natural transformation of presheaves: a morphism `S ⟶ C` (i.e. a
point of `C` parametrised by `S`) is sent to the composite `S ⟶ C ⟶ [0,1]`. -/
def betaNat : (LightProfinite.toCondensed cantor).obj ⟶ intervalCond.obj where
  app S := ↾fun x => binExpHom.hom.comp x.hom.hom
  naturality S T f := by
    ext x
    exact ContinuousMap.ext fun z => rfl

/-- The binary expansion map as a morphism of light condensed sets, `C ⟶ [0,1]`. -/
def beta : LightProfinite.toCondensed cantor ⟶ intervalCond :=
  ⟨betaNat⟩

/-! ## The Čech covering

Over a test object `S` and a continuous map `y : S ⟶ [0,1]`, the fibre product `S ×_[0,1] C`
is a light profinite set (it is a closed subspace of the compact, Hausdorff, totally
disconnected, second countable space `S × C`), it maps onto `S` because `C ⟶ [0,1]` is
surjective, and its tautological map to `C` lifts `y` by construction. -/

variable (S : LightProfinite) (yc : C(↥S, ↥unitInterval))

/-- The fibre product `S ×_[0,1] {0,1}^ℕ`, as a light profinite set. -/
def pullbackObj : LightProfinite :=
  let T : Type := { p : ↥S × ↥cantor // yc p.1 = binExpHom.hom p.2 }
  haveI : CompactSpace T :=
    isCompact_iff_compactSpace.mp
      (isClosed_eq (yc.continuous.comp continuous_fst)
        (binExpHom.hom.continuous.comp continuous_snd)).isCompact
  haveI : TotallyDisconnectedSpace T := Subtype.totallyDisconnectedSpace
  haveI : SecondCountableTopology T := Topology.IsInducing.subtypeVal.secondCountableTopology
  ↧T

/-- First projection of the fibre product. -/
def pullbackFst : pullbackObj S yc ⟶ S :=
  ConcreteCategory.ofHom
    (⟨fun p => p.1.1, continuous_fst.comp continuous_subtype_val⟩ : C(↥(pullbackObj S yc), ↥S))

/-- Second projection of the fibre product. -/
def pullbackSnd : pullbackObj S yc ⟶ cantor :=
  ConcreteCategory.ofHom
    (⟨fun p => p.1.2, continuous_snd.comp continuous_subtype_val⟩ : C(↥(pullbackObj S yc), ↥cantor))

/-- The first projection of the fibre product is surjective, since the binary expansion is. -/
lemma pullbackFst_surjective : Function.Surjective (pullbackFst S yc) := by
  intro s
  obtain ⟨c, hc⟩ := binExpHom_surjective (yc s)
  exact ⟨⟨⟨s, c⟩, hc.symm⟩, rfl⟩

/-- The defining relation of the fibre product: the second projection lifts `y` along the first
projection, i.e. `pullbackSnd` is a section of the cover `pullbackFst` over `y`. -/
lemma pullbackSnd_spec :
    (ConcreteCategory.hom (beta.hom.app (Opposite.op (pullbackObj S yc)))) (pullbackSnd S yc)
      = (ConcreteCategory.hom (intervalCond.obj.map (Opposite.op (pullbackFst S yc)))) yc := by
  change binExpHom.hom.comp (pullbackSnd S yc).hom.hom = yc.comp (pullbackFst S yc).hom.hom
  refine ContinuousMap.ext fun p => Subtype.ext ?_
  simp only [ContinuousMap.comp_apply]
  exact congrArg Subtype.val p.2.symm

/-! ## The main result -/

lemma beta_epi : Epi beta := by
  rw [LightCondSet.epi_iff_locallySurjective_on_lightProfinite]
  intro S y
  exact ⟨pullbackObj S y, pullbackFst S y, pullbackFst_surjective S y, pullbackSnd S y,
    pullbackSnd_spec S y⟩

/-- The binary-expansion map `C = {0,1}^ℕ ⟶ [0,1]`, `x ↦ Σ_n x_n / 2^{n+1}`, is a surjection of
light condensed sets, hence an epimorphism.  (This is the cover whose Čech nerve is used in
`Work.ANALYTIC.profinite_HI_pt`; the intended witness is the binary expansion, which one obtains
from the level-`n` projections `C ⟶ {0,1}^{n+1}` and the finite dyadic maps
`{0,1}^{n+1} ⟶ [0,1]`, or directly from the topological map via
`lightProfiniteToLightCondSetIsoTopCatToLightCondSet`.) -/
theorem binaryExp_epi :
    ∃ β : LightProfinite.toCondensed Work.ANALYTIC.CechPt.cantor ⟶
      Work.ANALYTIC.CechPt.intervalCond,
      Epi β :=
  ⟨beta, beta_epi⟩

end Work.ANALYTIC.CechPt
