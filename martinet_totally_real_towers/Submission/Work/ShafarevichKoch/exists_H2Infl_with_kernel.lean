import Mathlib
import Submission.Work.ShafarevichKoch.cochainInflation

/-!
# The inflation `H²(Γ ⧸ U, M) → H²(Γ, M)` for an open normal subgroup

For a topological group `Γ`, an open normal subgroup `U : OpenNormalSubgroup Γ` and a discrete
`Γ`-module `M` whose action factors through `Γ ⧸ U` (this is the hypothesis `hcomp`), the quotient
map `Γ → Γ ⧸ U` induces the **inflation** on continuous cohomology
`inf : H²(Γ ⧸ U, M) → H²(Γ, M)`.

Since there is no continuous section of `Γ → Γ ⧸ U` in general, the map is built on *cochains* by
pullback (`Work.ShafarevichKoch.cochain2Infl`, the definitional base of this file's import), and one
checks that it commutes with the differentials (`Work.ShafarevichKoch.d2Hom_cochain2Infl`).

The main result `Work.ShafarevichKoch.exists_H2Infl_with_kernel` records the two defining
properties of the inflation:

* it is induced by the cochain pullback: for every `2`-cocycle `z` of `Γ ⧸ U` there is a
  `2`-cocycle `w` of `Γ` in the corresponding class whose value at `(σ, τ)` is
  `z (σ̄, τ̄)`;
* its kernel consists of the classes whose pullback is a coboundary, i.e. the classes of the
  cocycles `z` for which there is `f : C¹(Γ, M)` with
  `z (σ̄, τ̄) = d¹f (σ, τ)` for all `σ τ` — the **inflation–restriction five term sequence**'s
  identification of `ker inf`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open Work.ConCohomology

namespace Work.ShafarevichKoch

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
variable {M : Type*} [AddCommGroup M] [DistribMulAction Γ M] [IsDiscreteGModule Γ M]

/-- **The inflation of a `2`-cocycle is a `2`-cocycle.**  The cocycle identity for `cochain2Infl U f`
at `(σ, τ, ρ)` is the cocycle identity for `f` at the images of `σ, τ, ρ` in `Γ ⧸ U`, transported
along `hcomp`. -/
lemma isCocycle2_cochain2Infl (U : OpenNormalSubgroup Γ) [DistribMulAction (Γ ⧸ U.toSubgroup) M]
    [IsDiscreteGModule (Γ ⧸ U.toSubgroup) M]
    (hcomp : ∀ (σ : Γ) (m : M), σ • m = (QuotientGroup.mk' U.toSubgroup σ) • m)
    {f : Cochain2 (Γ ⧸ U.toSubgroup) M}
    (hf : IsCocycle2 (f : (Γ ⧸ U.toSubgroup) × (Γ ⧸ U.toSubgroup) → M)) :
    IsCocycle2 (cochain2Infl U f : Γ × Γ → M) := by
  intro σ τ ρ
  have h := hf (QuotientGroup.mk' U.toSubgroup σ) (QuotientGroup.mk' U.toSubgroup τ)
    (QuotientGroup.mk' U.toSubgroup ρ)
  simp only [cochain2Infl_apply, map_mul] at h ⊢
  rw [hcomp σ (f (QuotientGroup.mk' U.toSubgroup τ, QuotientGroup.mk' U.toSubgroup ρ))]
  exact h

/-- The inflation of `2`-cocycles, as an additive homomorphism `Z²(Γ ⧸ U, M) →+ Z²(Γ, M)`. -/
noncomputable def Z2Infl (U : OpenNormalSubgroup Γ) [DistribMulAction (Γ ⧸ U.toSubgroup) M]
    [IsDiscreteGModule (Γ ⧸ U.toSubgroup) M]
    (hcomp : ∀ (σ : Γ) (m : M), σ • m = (QuotientGroup.mk' U.toSubgroup σ) • m) :
    Z2 (Γ ⧸ U.toSubgroup) M →+ Z2 Γ M :=
  AddMonoidHom.codRestrict ((cochain2InflHom U).comp (Z2 (Γ ⧸ U.toSubgroup) M).subtype)
    (Z2 Γ M) fun z => by
      rw [mem_Z2]
      exact isCocycle2_cochain2Infl U hcomp (mem_Z2.mp z.2)

@[simp] lemma Z2Infl_coe (U : OpenNormalSubgroup Γ) [DistribMulAction (Γ ⧸ U.toSubgroup) M]
    [IsDiscreteGModule (Γ ⧸ U.toSubgroup) M]
    (hcomp : ∀ (σ : Γ) (m : M), σ • m = (QuotientGroup.mk' U.toSubgroup σ) • m)
    (z : Z2 (Γ ⧸ U.toSubgroup) M) :
    ((Z2Infl U hcomp z : Z2 Γ M) : Cochain2 Γ M) =
      cochain2Infl U (z : Cochain2 (Γ ⧸ U.toSubgroup) M) := rfl

/-- The inflation of `2`-coboundaries is contained in the `2`-coboundaries: this is what makes the
inflation descend to cohomology. -/
lemma coe_Z2Infl_mem_B2 (U : OpenNormalSubgroup Γ) [DistribMulAction (Γ ⧸ U.toSubgroup) M]
    [IsDiscreteGModule (Γ ⧸ U.toSubgroup) M]
    (hcomp : ∀ (σ : Γ) (m : M), σ • m = (QuotientGroup.mk' U.toSubgroup σ) • m)
    {z : Z2 (Γ ⧸ U.toSubgroup) M}
    (hz : (z : Cochain2 (Γ ⧸ U.toSubgroup) M) ∈ B2 (Γ ⧸ U.toSubgroup) M) :
    (Z2Infl U hcomp z : Cochain2 Γ M) ∈ B2 Γ M := by
  obtain ⟨g, hg⟩ := hz
  refine ⟨cochain1Infl U g, ?_⟩
  rw [Z2Infl_coe, ← hg, d1Hom_cochain1Infl U hcomp]

/-- **The inflation** `H²(Γ ⧸ U, M) →+ H²(Γ, M)`. -/
noncomputable def H2Infl (U : OpenNormalSubgroup Γ) [DistribMulAction (Γ ⧸ U.toSubgroup) M]
    [IsDiscreteGModule (Γ ⧸ U.toSubgroup) M]
    (hcomp : ∀ (σ : Γ) (m : M), σ • m = (QuotientGroup.mk' U.toSubgroup σ) • m) :
    H2 (Γ ⧸ U.toSubgroup) M →+ H2 Γ M :=
  QuotientAddGroup.map (B2' (Γ ⧸ U.toSubgroup) M) (B2' Γ M) (Z2Infl U hcomp) fun z hz => by
    rw [mem_B2'] at hz
    rw [AddSubgroup.mem_comap, mem_B2']
    exact coe_Z2Infl_mem_B2 U hcomp hz

@[simp] lemma H2Infl_mk (U : OpenNormalSubgroup Γ) [DistribMulAction (Γ ⧸ U.toSubgroup) M]
    [IsDiscreteGModule (Γ ⧸ U.toSubgroup) M]
    (hcomp : ∀ (σ : Γ) (m : M), σ • m = (QuotientGroup.mk' U.toSubgroup σ) • m)
    (z : Z2 (Γ ⧸ U.toSubgroup) M) :
    H2Infl U hcomp (H2.mk z) = H2.mk (Z2Infl U hcomp z) := rfl

/-- The kernel description at the level of cochains: a cocycle of `Γ ⧸ U` becomes a coboundary
after pullback to `Γ` if and only if it is given by the differential of a (locally constant)
`1`-cochain of `Γ`. -/
lemma exists_d1Hom_eq_cochain2Infl_iff (U : OpenNormalSubgroup Γ)
    [DistribMulAction (Γ ⧸ U.toSubgroup) M] [IsDiscreteGModule (Γ ⧸ U.toSubgroup) M]
    (z : Z2 (Γ ⧸ U.toSubgroup) M) :
    (∃ g : Cochain1 Γ M, d1Hom Γ M g = cochain2Infl U (z : Cochain2 (Γ ⧸ U.toSubgroup) M)) ↔
      ∃ f : Cochain1 Γ M, ∀ p : Γ × Γ,
        (z : Cochain2 (Γ ⧸ U.toSubgroup) M)
            (QuotientGroup.mk' U.toSubgroup p.1, QuotientGroup.mk' U.toSubgroup p.2)
          = d1Fun (f : Γ → M) p := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, fun p => ?_⟩
    obtain ⟨σ, τ⟩ := p
    have h := DFunLike.congr_fun hg (σ, τ)
    simp only [d1Hom_apply, cochain2Infl_apply] at h
    rw [← h, d1Fun_apply]
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    refine LocallyConstant.ext fun p => ?_
    obtain ⟨σ, τ⟩ := p
    simp only [d1Hom_apply, cochain2Infl_apply]
    exact (hf (σ, τ)).symm

theorem exists_H2Infl_with_kernel
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {M : Type*} [AddCommGroup M] [DistribMulAction Γ M]
    [Work.ConCohomology.IsDiscreteGModule Γ M]
    (U : OpenNormalSubgroup Γ) [DistribMulAction (Γ ⧸ U.toSubgroup) M]
    [Work.ConCohomology.IsDiscreteGModule (Γ ⧸ U.toSubgroup) M]
    (hcomp : ∀ (σ : Γ) (m : M), σ • m = (QuotientGroup.mk' U.toSubgroup σ) • m) :
    ∃ Φ : Work.ConCohomology.H2 (Γ ⧸ U.toSubgroup) M →+ Work.ConCohomology.H2 Γ M,
      (∀ z : Work.ConCohomology.Z2 (Γ ⧸ U.toSubgroup) M, ∃ w : Work.ConCohomology.Z2 Γ M,
          Φ (Work.ConCohomology.H2.mk z) = Work.ConCohomology.H2.mk w ∧
          ∀ p : Γ × Γ, (w : Work.ConCohomology.Cochain2 Γ M) p =
            (z : Work.ConCohomology.Cochain2 (Γ ⧸ U.toSubgroup) M)
              (QuotientGroup.mk' U.toSubgroup p.1, QuotientGroup.mk' U.toSubgroup p.2)) ∧
      (∀ z : Work.ConCohomology.Z2 (Γ ⧸ U.toSubgroup) M,
        Φ (Work.ConCohomology.H2.mk z) = 0 ↔
          ∃ f : Work.ConCohomology.Cochain1 Γ M, ∀ p : Γ × Γ,
            (z : Work.ConCohomology.Cochain2 (Γ ⧸ U.toSubgroup) M)
                (QuotientGroup.mk' U.toSubgroup p.1, QuotientGroup.mk' U.toSubgroup p.2)
              = Work.ConCohomology.d1Fun (G := Γ) (f : Γ → M) p) := by
  refine ⟨H2Infl U hcomp, ?_, ?_⟩
  · intro z
    refine ⟨Z2Infl U hcomp z, H2Infl_mk U hcomp z, ?_⟩
    intro p
    simp only [Z2Infl_coe, cochain2Infl_apply]
  · intro z
    rw [H2Infl_mk, H2.mk_eq_zero_iff, mem_B2', mem_B2, Z2Infl_coe]
    exact exists_d1Hom_eq_cochain2Infl_iff U z

end Work.ShafarevichKoch
