import Mathlib
import Submission.Work.K3.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3.BaseChange` — base change of schemes along a field extension

The descent step of Theorem `thm:K3` of Lin–Shinder (*Motivic invariants of birational maps*,
Annals **199** (1), 2024, § *K3 surfaces of degree 12*) is a statement about **fields of
definition**: the Hassett–Lai construction is carried out over `ℚ` (`lem:HL-admis-pencil` +
Terasoma), so its output is defined over `ℚ`; since every subfield `𝕜 ⊆ ℂ` contains `ℚ`, the
output is defined over `𝕜` as well, and the *geometry* of the link over `𝕜` is the base change of
the geometry over `ℚ`.

This module builds the formal content of that sentence:

* `specMap K L : Spec L ⟶ Spec K` — the structure morphism of a field extension;
* `baseChange K L X` — the base change (= fibred product `X ×_{Spec K} Spec L`) of a `K`-scheme
  along `K → L`, with its canonical `L`-structure `baseChangeOver` and projection
  `baseChangeProj`;
* `baseChangeMap K L f` — the base change of a `K`-morphism;
* the field-arithmetic facts (`IsScalarTower`, `ℚ ≤ 𝕜`) used to compare the successive base
  changes.

The two theorems which make the descent work are proved in the companion files
`Submission/Work/K3/baseChange_isoOver.lean` (base change preserves isomorphisms over the base)
and `Submission/Work/K3/baseChange_comp.lean` (transitivity of base change: base changing first
from `K` to `L` and then from `L` to `M` is base changing directly from `K` to `M`); together with
the `Subfield`-level facts of `Work.K3.Descent` they turn "defined over `ℚ`" into "defined over
`𝕜`" — the monotonicity of the field of definition in the lattice of subfields of `ℂ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.K3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

variable (K L : Type) [Field K] [Field L] [Algebra K L]

/-- The structure morphism `Spec L ⟶ Spec K` of a field extension `K → L`. -/
noncomputable abbrev specMap : Spec (.of L) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

/-- **Base change of a `K`-scheme to `L`**: the fibred product `X ×_{Spec K} Spec L`. -/
noncomputable def baseChange (X : Scheme.{0}) [X.Over (Spec (.of K))] : Scheme.{0} :=
  pullback (specMap K L) (X ↘ Spec (.of K))

/-- The base change of a `K`-scheme is an `L`-scheme, via the first projection of the fibred
product. -/
noncomputable instance baseChangeOver (X : Scheme.{0}) [X.Over (Spec (.of K))] :
    (baseChange K L X).Over (Spec (.of L)) :=
  ⟨pullback.fst _ _⟩

/-- The projection `X ×_{Spec K} Spec L ⟶ X` of the base change of `X`. -/
noncomputable def baseChangeProj (X : Scheme.{0}) [X.Over (Spec (.of K))] :
    baseChange K L X ⟶ X :=
  pullback.snd _ _

/-- A base change is also a `K`-scheme, via the composite
`X ×_{Spec K} Spec L ⟶ Spec L ⟶ Spec K`. -/
noncomputable instance baseChangeOverK (X : Scheme.{0}) [X.Over (Spec (.of K))] :
    (baseChange K L X).Over (Spec (.of K)) :=
  ⟨baseChangeProj K L X ≫ (X ↘ Spec (.of K))⟩

/-- The projection of a base change is a morphism of schemes over `K`. -/
instance baseChangeProj_isOver (X : Scheme.{0}) [X.Over (Spec (.of K))] :
    (baseChangeProj K L X).IsOver (Spec (.of K)) :=
  ⟨rfl⟩

/-- The defining square of the base change is cartesian. -/
theorem baseChange_isPullback (X : Scheme.{0}) [X.Over (Spec (.of K))] :
    IsPullback (pullback.fst (specMap K L) (X ↘ Spec (.of K)))
      (pullback.snd (specMap K L) (X ↘ Spec (.of K)))
      (specMap K L) (X ↘ Spec (.of K)) :=
  .of_hasPullback _ _

/-- **Base change of a morphism over the base**: the induced morphism
`baseChange K L X ⟶ baseChange K L Y`. -/
noncomputable def baseChangeMap {X Y : Scheme.{0}} [X.Over (Spec (.of K))]
    [Y.Over (Spec (.of K))] (f : X ⟶ Y) [hf : f.IsOver (Spec (.of K))] :
    baseChange K L X ⟶ baseChange K L Y :=
  pullback.map (specMap K L) (X ↘ Spec (.of K)) (specMap K L) (Y ↘ Spec (.of K))
    (𝟙 _) f (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by
      rw [Category.comp_id]
      exact ((Hom.isOver_iff (S := Spec (.of K))).mp hf).symm)

/-! ## Integrality of a base change along a field extension -/

/-- **Base change of a geometrically integral scheme along a field extension is integral.**  This
is the geometric half of "the `𝕜`-model of the link is a `𝕜`-variety": the K3 surfaces, the model
of `ℙ⁴` and the models of `S × ℙ¹` of the `ℚ`-model are geometrically integral, so their base
changes are integral.  (The remaining `Variety` components — `IsSeparated`,
`LocallyOfFiniteType`, `QuasiCompact` of the structure morphism — are Mathlib instances, since
the structure morphism of `baseChange K L X` is the base change of `X ↘ Spec K`.) -/
theorem isIntegral_baseChange (K L : Type) [Field K] [Field L] [Algebra K L] (X : Scheme.{0})
    [X.Over (Spec (.of K))] [GeometricallyIntegral (X ↘ Spec (.of K))] :
    IsIntegral (baseChange K L X) :=
  pullback_of_geometrically' (GeometricallyIntegral.geometrically_isIntegral (f := X ↘ Spec (.of K)))
    L (specMap K L)

end Work.K3
