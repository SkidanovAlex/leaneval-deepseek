/-
# Auxiliary lemmas for `Work.NormalComplement.sec3_step2`

This `sorry`-free module holds the general facts used both by `sec3_step2` itself and by the
lemmas delegated for it:

* `fitSub_le` : `F(X) ≤ X`;
* `fitSub_le_normalizer` : `X ≤ N_G(F(X))` (the Fitting subgroup is characteristic in `X`);
* `not_dvd_card_of_fpf_pgroup` : if a `p`-group `X` acts by conjugation on a subgroup `A`
  (`X ≤ N_G(A)`) with no nontrivial fixed point, then `p ∤ |A|`
  (`IsPGroup.card_modEq_card_fixedPoints`).
-/
import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.centralizer_fitting_le
import Submission.Work.Fitting.fitting_eq_sInf_chiefFactor_centralizer
import Submission.Work.Fitting.fitting_isNilpotent
import Submission.Work.Fitting.fitting_le_fitting_of_normal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.style.haveILetI false

open Classical
open scoped Pointwise commutatorElement

namespace Work.NormalComplement

variable {G : Type*} [Group G]

/-- `F(X) ≤ X`: the Fitting subgroup of a subgroup is a subgroup of it. -/
theorem fitSub_le (X : Subgroup G) : Work.NormalComplement.Design.fitSub X ≤ X := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

/-- `X` normalises its Fitting subgroup `F(X)`: the Fitting subgroup is characteristic in `X`,
hence invariant under conjugation by the elements of `X`. -/
theorem fitSub_le_normalizer (X : Subgroup G) :
    X ≤ Subgroup.normalizer (Work.NormalComplement.Design.fitSub X : Set G) := by
  haveI hnorm : (Work.Fitting.fitting ↥X).Normal := Work.Fitting.fitting_normal' ↥X
  have hconj : ∀ u : G, u ∈ X → ∀ h ∈ Work.NormalComplement.Design.fitSub X,
      u * h * u⁻¹ ∈ Work.NormalComplement.Design.fitSub X := by
    intro u hu h hh
    obtain ⟨f, hf, rfl⟩ := hh
    refine ⟨⟨u, hu⟩ * f * ⟨u, hu⟩⁻¹, ?_, ?_⟩
    · exact Subgroup.Normal.conj_mem hnorm f hf ⟨u, hu⟩
    · show X.subtype (⟨u, hu⟩ * f * ⟨u, hu⟩⁻¹) = u * X.subtype f * u⁻¹
      simp
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  refine fun h => ⟨fun hh => hconj g hg h hh, fun hh => ?_⟩
  have h1 : g⁻¹ * (g * h * g⁻¹) * (g⁻¹)⁻¹ ∈ Work.NormalComplement.Design.fitSub X :=
    hconj g⁻¹ (X.inv_mem hg) (g * h * g⁻¹) hh
  have key : g⁻¹ * (g * h * g⁻¹) * (g⁻¹)⁻¹ = h := by group
  rwa [key] at h1

/-- **Orbit counting for a `p`-group acting with trivial fixed points.**  If a `p`-group `X`
normalises `A` and the only element of `A` fixed by all of `X` (under conjugation) is `1`, then
`p ∤ |A|`.

Proof: `X` acts on `A` by conjugation; `IsPGroup.card_modEq_card_fixedPoints` gives
`|A| ≡ |FixedPoints| = 1 (mod p)`. -/
theorem not_dvd_card_of_fpf_pgroup {p : ℕ} (hp : p.Prime) {X A : Subgroup G} [Finite G]
    (hXN : X ≤ Subgroup.normalizer (A : Set G)) (hXp : IsPGroup p X)
    (hf : ∀ a ∈ A, (∀ x ∈ X, x * a * x⁻¹ = a) → a = 1) :
    ¬ p ∣ Nat.card A := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hsmul : ∀ (d : X) (x : A), (d : G) * (x : G) * (d : G)⁻¹ ∈ A := fun d x =>
    (Subgroup.mem_normalizer_iff.mp (hXN d.2) (x : G)).mp x.2
  letI : MulAction X A :=
    { smul := fun d x => ⟨(d : G) * (x : G) * (d : G)⁻¹, hsmul d x⟩
      one_smul := fun x => by
        apply Subtype.ext
        show (1 : G) * (x : G) * (1 : G)⁻¹ = (x : G)
        simp
      mul_smul := fun d e x => by
        apply Subtype.ext
        show ((d : G) * (e : G)) * (x : G) * ((d : G) * (e : G))⁻¹
          = (d : G) * ((e : G) * (x : G) * (e : G)⁻¹) * (d : G)⁻¹
        group }
  have hfix : MulAction.fixedPoints X A = {1} := by
    ext a
    rw [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro ha
      apply Subtype.ext
      exact hf (a : G) a.2 fun x hx => congrArg Subtype.val (ha ⟨x, hx⟩)
    · rintro rfl
      intro x
      apply Subtype.ext
      show (x : G) * (1 : G) * (x : G)⁻¹ = 1
      simp
  have hcard : Nat.card (MulAction.fixedPoints X A) = 1 := by simp [hfix]
  have hmod : Nat.card A ≡ 1 [MOD p] := by
    have h := hXp.card_modEq_card_fixedPoints A
    rwa [hcard] at h
  intro hdvd
  have hzero : Nat.card A % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
  rw [Nat.ModEq, hzero, Nat.mod_eq_of_lt hp.one_lt] at hmod
  exact zero_ne_one hmod

section FittingMonotone

variable {G' : Type*} [Group G']

/-- The Fitting subgroup is preserved by a group isomorphism:
`F(G).map e = F(G')`. -/
theorem fitting_map_mulEquiv [Finite G] (e : G ≃* G') :
    (Work.Fitting.fitting G).map e.toMonoidHom = Work.Fitting.fitting G' := by
  haveI : Finite G' := Finite.of_equiv G e
  haveI hFG : Group.IsNilpotent ↥(Work.Fitting.fitting G) := Work.Fitting.fitting_isNilpotent G
  haveI hFG' : Group.IsNilpotent ↥(Work.Fitting.fitting G') := Work.Fitting.fitting_isNilpotent G'
  have hle : ((Work.Fitting.fitting G).map e.toMonoidHom) ≤ Work.Fitting.fitting G' :=
    Work.Fitting.le_fitting
      ((Work.Fitting.fitting_normal' G).map e.toMonoidHom e.surjective)
      (Group.nilpotent_of_mulEquiv
        (Subgroup.equivMapOfInjective (Work.Fitting.fitting G) e.toMonoidHom e.injective))
  have hle' : ((Work.Fitting.fitting G').map e.symm.toMonoidHom) ≤ Work.Fitting.fitting G :=
    Work.Fitting.le_fitting
      ((Work.Fitting.fitting_normal' G').map e.symm.toMonoidHom e.symm.surjective)
      (Group.nilpotent_of_mulEquiv
        (Subgroup.equivMapOfInjective (Work.Fitting.fitting G') e.symm.toMonoidHom
          e.symm.injective))
  refine le_antisymm hle ?_
  calc Work.Fitting.fitting G'
      = ((Work.Fitting.fitting G').map e.symm.toMonoidHom).map e.toMonoidHom := by
        rw [Subgroup.map_map]
        have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G' := by ext x; simp
        rw [this, Subgroup.map_id]
    _ ≤ (Work.Fitting.fitting G).map e.toMonoidHom := Subgroup.map_mono hle'

end FittingMonotone

/-- **`F(T) ≤ F(V)` for `T ⊴ V`.**  The Fitting subgroup is monotone in a normal subgroup: if
`T` is normal in `V`, then `F(T)`, being characteristic in `T`, is normal in `V`, and it is
nilpotent, so it is contained in the largest normal nilpotent subgroup `F(V)` of `V`. -/
theorem fitSub_le_fitSub_of_normal [Finite G] {T V : Subgroup G} (hTV : T ≤ V)
    (hNV : V ≤ Subgroup.normalizer (T : Set G)) :
    Work.NormalComplement.Design.fitSub T ≤ Work.NormalComplement.Design.fitSub V := by
  haveI : (T.subgroupOf V).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hTV).mpr hNV
  -- Fitting's monotonicity inside the group `↥V`: `F(T') ≤ F(V)`
  have h1 : ((Work.Fitting.fitting ↥(T.subgroupOf V)).map (T.subgroupOf V).subtype) ≤
      Work.Fitting.fitting ↥V := Work.Fitting.fitting_le_fitting_of_normal
  have h2 : ((Work.Fitting.fitting ↥(T.subgroupOf V)).map
        (V.subtype.comp (T.subgroupOf V).subtype)) ≤
      Work.NormalComplement.Design.fitSub V := by
    have h3 := Subgroup.map_mono (f := V.subtype) h1
    rw [Subgroup.map_map] at h3
    exact h3
  -- identify `(Fitting ↥T').map (V.subtype ∘ T'.subtype)` with `F(T)`
  have hcomp : V.subtype.comp (T.subgroupOf V).subtype =
      T.subtype.comp (Subgroup.subgroupOfEquivOfLe hTV).toMonoidHom := by
    ext x
    rfl
  have key : (Work.Fitting.fitting ↥(T.subgroupOf V)).map
        (V.subtype.comp (T.subgroupOf V).subtype) =
      Work.NormalComplement.Design.fitSub T := by
    rw [hcomp]
    show Subgroup.map (T.subtype.comp (Subgroup.subgroupOfEquivOfLe hTV).toMonoidHom)
        (Work.Fitting.fitting ↥(T.subgroupOf V)) =
      Subgroup.map T.subtype (Work.Fitting.fitting ↥T)
    rw [← Subgroup.map_map, fitting_map_mulEquiv (Subgroup.subgroupOfEquivOfLe hTV)]
  rwa [key] at h2

end Work.NormalComplement
