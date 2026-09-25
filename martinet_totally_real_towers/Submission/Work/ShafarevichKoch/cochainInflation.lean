import Mathlib
import Submission.Work.ConCohomology.All

/-!
# `Work.ShafarevichKoch.cochainInflation` -- the inflation of cochains along a quotient

For a topological group `Γ` and an open normal subgroup `U : OpenNormalSubgroup Γ`, the quotient map
`Γ → Γ ⧸ U` induces a map on *cochains* going **the other way** (the inflation): a locally constant
function on `(Γ ⧸ U) × (Γ ⧸ U)` pulls back to one on `Γ × Γ`.

NOTE (README §33.5): this is **not** `Work.ConCohomology.H2Res`, which is the *restriction*
`H²(G,M) → H²(H,M)` along a homomorphism `ψ : G →* H`; the inflation along a surjection needs a
pullback construction (a continuous section does not exist in general).

## Main declarations

* `Work.ShafarevichKoch.proj2CM`, `proj1CM`, `proj3CM` -- the projections `Γ → Γ ⧸ U`,
  `Γ × Γ → (Γ ⧸ U) × (Γ ⧸ U)`, `Γ × Γ × Γ → (Γ ⧸ U)³` as `ContinuousMap`s;
* `Work.ShafarevichKoch.cochain1Infl`, `cochain2Infl`, `cochain3Infl` -- the pullback of cochains;
* `Work.ShafarevichKoch.cochain1Infl_apply`, ... -- their defining equations.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open Work.ConCohomology

namespace Work.ShafarevichKoch

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
variable {M : Type*} [AddCommGroup M] [DistribMulAction Γ M] [IsDiscreteGModule Γ M]

/-- The quotient map `Γ → Γ ⧸ U`, as a continuous map. -/
def proj1CM (U : OpenNormalSubgroup Γ) : C(Γ, Γ ⧸ U.toSubgroup) where
  toFun := QuotientGroup.mk' U.toSubgroup
  continuous_toFun := continuous_quotient_mk'

@[simp] lemma proj1CM_apply (U : OpenNormalSubgroup Γ) (σ : Γ) :
    proj1CM U σ = QuotientGroup.mk' U.toSubgroup σ := rfl

/-- The projection `Γ × Γ → (Γ ⧸ U) × (Γ ⧸ U)`, as a continuous map. -/
def proj2CM (U : OpenNormalSubgroup Γ) :
    C(Γ × Γ, (Γ ⧸ U.toSubgroup) × (Γ ⧸ U.toSubgroup)) where
  toFun p := (QuotientGroup.mk' U.toSubgroup p.1, QuotientGroup.mk' U.toSubgroup p.2)
  continuous_toFun :=
    ((proj1CM U).continuous.comp continuous_fst).prodMk
      ((proj1CM U).continuous.comp continuous_snd)

@[simp] lemma proj2CM_apply (U : OpenNormalSubgroup Γ) (p : Γ × Γ) :
    proj2CM U p = (QuotientGroup.mk' U.toSubgroup p.1, QuotientGroup.mk' U.toSubgroup p.2) := rfl

/-- The projection `Γ × Γ × Γ → (Γ ⧸ U) × (Γ ⧸ U) × (Γ ⧸ U)`, as a continuous map. -/
def proj3CM (U : OpenNormalSubgroup Γ) :
    C(Γ × Γ × Γ, (Γ ⧸ U.toSubgroup) × (Γ ⧸ U.toSubgroup) × (Γ ⧸ U.toSubgroup)) where
  toFun p := (QuotientGroup.mk' U.toSubgroup p.1, QuotientGroup.mk' U.toSubgroup p.2.1,
    QuotientGroup.mk' U.toSubgroup p.2.2)
  continuous_toFun := by
    have h2 : Continuous fun p : Γ × Γ × Γ =>
        (QuotientGroup.mk' U.toSubgroup p.2.1, QuotientGroup.mk' U.toSubgroup p.2.2) :=
      ((proj1CM U).continuous.comp (continuous_fst.comp continuous_snd)).prodMk
        ((proj1CM U).continuous.comp (continuous_snd.comp continuous_snd))
    exact ((proj1CM U).continuous.comp continuous_fst).prodMk h2

@[simp] lemma proj3CM_apply (U : OpenNormalSubgroup Γ) (p : Γ × Γ × Γ) :
    proj3CM U p = (QuotientGroup.mk' U.toSubgroup p.1, QuotientGroup.mk' U.toSubgroup p.2.1,
      QuotientGroup.mk' U.toSubgroup p.2.2) := rfl

/-- The inflation of a `1`-cochain along the quotient map. -/
def cochain1Infl (U : OpenNormalSubgroup Γ) (f : Cochain1 (Γ ⧸ U.toSubgroup) M) : Cochain1 Γ M :=
  LocallyConstant.comap (proj1CM U) f

/-- The inflation of a `2`-cochain along the quotient map. -/
def cochain2Infl (U : OpenNormalSubgroup Γ) (f : Cochain2 (Γ ⧸ U.toSubgroup) M) : Cochain2 Γ M :=
  LocallyConstant.comap (proj2CM U) f

/-- The inflation of a `3`-cochain along the quotient map. -/
def cochain3Infl (U : OpenNormalSubgroup Γ) (f : Cochain3 (Γ ⧸ U.toSubgroup) M) : Cochain3 Γ M :=
  LocallyConstant.comap (proj3CM U) f

@[simp] lemma cochain1Infl_apply (U : OpenNormalSubgroup Γ) (f : Cochain1 (Γ ⧸ U.toSubgroup) M)
    (σ : Γ) : cochain1Infl U f σ = f (QuotientGroup.mk' U.toSubgroup σ) := rfl

@[simp] lemma cochain2Infl_apply (U : OpenNormalSubgroup Γ) (f : Cochain2 (Γ ⧸ U.toSubgroup) M)
    (p : Γ × Γ) :
    cochain2Infl U f p = f (QuotientGroup.mk' U.toSubgroup p.1, QuotientGroup.mk' U.toSubgroup p.2) :=
  rfl

@[simp] lemma cochain3Infl_apply (U : OpenNormalSubgroup Γ) (f : Cochain3 (Γ ⧸ U.toSubgroup) M)
    (p : Γ × Γ × Γ) :
    cochain3Infl U f p =
      f (QuotientGroup.mk' U.toSubgroup p.1, QuotientGroup.mk' U.toSubgroup p.2.1,
        QuotientGroup.mk' U.toSubgroup p.2.2) := rfl

/-! ## Additivity of the cochain inflation -/

section Additive

variable (U : OpenNormalSubgroup Γ)

@[simp] lemma cochain1Infl_zero : cochain1Infl U (0 : Cochain1 (Γ ⧸ U.toSubgroup) M) = 0 := rfl
@[simp] lemma cochain2Infl_zero : cochain2Infl U (0 : Cochain2 (Γ ⧸ U.toSubgroup) M) = 0 := rfl
@[simp] lemma cochain3Infl_zero : cochain3Infl U (0 : Cochain3 (Γ ⧸ U.toSubgroup) M) = 0 := rfl

lemma cochain1Infl_add (f g : Cochain1 (Γ ⧸ U.toSubgroup) M) :
    cochain1Infl U (f + g) = cochain1Infl U f + cochain1Infl U g := by
  ext σ; rfl

lemma cochain2Infl_add (f g : Cochain2 (Γ ⧸ U.toSubgroup) M) :
    cochain2Infl U (f + g) = cochain2Infl U f + cochain2Infl U g := by
  ext p; rfl

lemma cochain3Infl_add (f g : Cochain3 (Γ ⧸ U.toSubgroup) M) :
    cochain3Infl U (f + g) = cochain3Infl U f + cochain3Infl U g := by
  ext p; rfl

/-- The inflation of `1`-cochains as an additive homomorphism. -/
def cochain1InflHom : Cochain1 (Γ ⧸ U.toSubgroup) M →+ Cochain1 Γ M where
  toFun := cochain1Infl U
  map_zero' := cochain1Infl_zero U
  map_add' := cochain1Infl_add U

/-- The inflation of `2`-cochains as an additive homomorphism. -/
def cochain2InflHom : Cochain2 (Γ ⧸ U.toSubgroup) M →+ Cochain2 Γ M where
  toFun := cochain2Infl U
  map_zero' := cochain2Infl_zero U
  map_add' := cochain2Infl_add U

end Additive

section Differentials

variable (U : OpenNormalSubgroup Γ) [DistribMulAction (Γ ⧸ U.toSubgroup) M]
  [IsDiscreteGModule (Γ ⧸ U.toSubgroup) M]

/-- **The inflation commutes with `d¹`.** -/
lemma d1Hom_cochain1Infl
    (hcomp : ∀ (σ : Γ) (m : M), σ • m = (QuotientGroup.mk' U.toSubgroup σ) • m)
    (f : Cochain1 (Γ ⧸ U.toSubgroup) M) :
    cochain2Infl U (d1Hom (Γ ⧸ U.toSubgroup) M f) = d1Hom Γ M (cochain1Infl U f) := by
  refine LocallyConstant.ext fun p => ?_
  obtain ⟨σ, τ⟩ := p
  simp only [cochain2Infl_apply, cochain1Infl_apply, d1Hom_apply, map_mul]
  rw [hcomp]

/-- **The inflation commutes with `d²`.** -/
lemma d2Hom_cochain2Infl
    (hcomp : ∀ (σ : Γ) (m : M), σ • m = (QuotientGroup.mk' U.toSubgroup σ) • m)
    (f : Cochain2 (Γ ⧸ U.toSubgroup) M) :
    cochain3Infl U (d2Hom (Γ ⧸ U.toSubgroup) M f) = d2Hom Γ M (cochain2Infl U f) := by
  refine LocallyConstant.ext fun p => ?_
  obtain ⟨σ, τ, ρ⟩ := p
  simp only [cochain3Infl_apply, cochain2Infl_apply, d2Hom_apply, map_mul]
  rw [hcomp]

end Differentials

end Work.ShafarevichKoch
