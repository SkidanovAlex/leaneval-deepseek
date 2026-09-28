import Mathlib
import Submission.Work.RatHurewicz.cupBijectiveOverPiece
import Submission.Work.RatHurewicz.cupBijective_cylPre_iUnion
import Submission.Work.Serre.bijective_mixedCup_of_openCover
import Submission.Work.Serre.mvDeltaCupMixedAux
import Submission.Work.Serre.DiscPair.cylPreimageHomeoOpen
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.RatHurewicz.Cofibre.ConeContract

/-!
# The local cup-bijectivity predicate and the two-piece gluing (for `SphereThom`)

* `Work.RatHurewicz.CupBij A n₀ U₀ S m` — the mixed cup product with the restriction of `U₀` to a
  piece `S` of the ambient space `X` is bijective in degree `m`;
* `Work.RatHurewicz.cupBij_union` — the two-piece Mayer–Vietoris gluing (degrees `m ≥ 1`);
* `Work.RatHurewicz.cupBij_union_subset` — the same gluing with the conclusion over the
  sub-ambient `↥(Uc ∪ Vc)`;
* `Work.RatHurewicz.subsingleton_relCoh_zero_cylPre` — the degree-`0` relative vanishing over the
  cylinder of a nonempty piece;
* `Work.RatHurewicz.cupBij_zero_union_subset` — the degree-`0` gluing over a sub-ambient;
* `Work.RatHurewicz.coneSphereContractible` — the contractibility of the unit sphere of a convex
  cone.
-/

namespace Work.RatHurewicz

open CategoryTheory CategoryTheory.Limits
open scoped Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **The local cup-bijectivity condition.** -/
def CupBij {X : Type} [TopologicalSpace X] (A : Set X) (n₀ : ℕ)
    (U₀ : Work.Thom.RelCoh ℚ n₀ X A) (S : Set X) (m : ℕ) : Prop :=
  Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥S =>
    (Work.Thom.mixedCupC ℚ {y : ↥S | (y : X) ∈ A} m n₀) x
      ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥S, X))
        {y : ↥S | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀))

/-- **The three local properties of a piece** used by the local-to-global argument for the
sphere: the mixed cup product with `U₀` is bijective over the piece in every degree `m ≥ 1` of the
range, it is bijective in degree `0`, and the relative cohomology of the pair over the piece
vanishes in degrees `≤ n₀ - 1`. -/
def CvGood {X : Type} [TopologicalSpace X] (A : Set X) (n₀ K : ℕ)
    (U₀ : Work.Thom.RelCoh ℚ n₀ X A) (S : Set X) : Prop :=
  (∀ m : ℕ, 1 ≤ m → m + n₀ ≤ K → CupBij A n₀ U₀ S m) ∧
    CupBij A n₀ U₀ S 0 ∧
      (∀ k : ℕ, k ≤ n₀ - 1 →
        Subsingleton ↥(Work.Thom.RelCoh ℚ k ↥S {y : ↥S | (y : X) ∈ A}))

/-- **`CupBij` only depends on the piece through its set.** -/
theorem CupBij_congr_set {X : Type} [TopologicalSpace X] {A : Set X} {n₀ : ℕ}
    {U₀ : Work.Thom.RelCoh ℚ n₀ X A} {S S' : Set X} (h : S = S') {m : ℕ}
    (hh : CupBij A n₀ U₀ S m) : CupBij A n₀ U₀ S' m :=
  h ▸ hh

/-- **The two-piece gluing of the cup bijectivity**, in the `CupBij` vocabulary. -/
theorem cupBij_union {X : Type} [TopologicalSpace X] (A : Set X) (Uc Vc : Set X)
    (hUo : IsOpen Uc) (hVo : IsOpen Vc) (hcov : Uc ∪ Vc = Set.univ)
    (n₀ K : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ X A)
    (hU : ∀ m : ℕ, m + n₀ ≤ K → CupBij A n₀ U₀ Uc m)
    (hV : ∀ m : ℕ, m + n₀ ≤ K → CupBij A n₀ U₀ Vc m)
    (hUV : ∀ m : ℕ, m + n₀ ≤ K → CupBij A n₀ U₀ (Uc ∩ Vc) m) :
    ∀ m : ℕ, 1 ≤ m → m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m X =>
      (Work.Thom.mixedCupC ℚ A m n₀) x U₀) :=
  Work.Serre.bijective_mixedCup_of_openCover_aux A Uc Vc hUo hVo hcov n₀ K U₀
    (fun m hmK => hU m hmK) (fun m hmK => hV m hmK) (fun m hmK => hUV m hmK)
    (fun m => Work.Serre.mvDeltaCupMixed (TopCat.of X) A Uc Vc hUo hVo hcov n₀ U₀ m)

/-- **The two-piece gluing over a sub-ambient.** -/
theorem cupBij_union_subset {X : Type} [TopologicalSpace X] (A : Set X) (Uc Vc : Set X)
    (hUo : IsOpen Uc) (hVo : IsOpen Vc)
    (n₀ K : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ X A)
    (hU : ∀ m : ℕ, m + n₀ ≤ K → CupBij A n₀ U₀ Uc m)
    (hV : ∀ m : ℕ, m + n₀ ≤ K → CupBij A n₀ U₀ Vc m)
    (hUV : ∀ m : ℕ, m + n₀ ≤ K → CupBij A n₀ U₀ (Uc ∩ Vc) m) :
    ∀ m : ℕ, 1 ≤ m → m + n₀ ≤ K → CupBij A n₀ U₀ (Uc ∪ Vc) m := by
  intro m hm hmK
  change Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥(Uc ∪ Vc) =>
    (Work.Thom.mixedCupC ℚ {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} m n₀) x
      ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(Uc ∪ Vc), X))
        {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀))
  have hUo' : IsOpen {y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc} :=
    hUo.preimage continuous_subtype_val
  have hVo' : IsOpen {y : ↥(Uc ∪ Vc) | (y : X) ∈ Vc} :=
    hVo.preimage continuous_subtype_val
  have hcov' : {y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc} ∪ {y : ↥(Uc ∪ Vc) | (y : X) ∈ Vc}
      = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      rcases y.2 with hy | hy
      · exact Or.inl hy
      · exact Or.inr hy
  have hU'' : ∀ m' : ℕ, m' + n₀ ≤ K →
      CupBij {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} n₀
        ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(Uc ∪ Vc), X))
          {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀)
        {y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc} m' := by
    intro m' hmK'
    have h := bijective_cup_subSet A Uc (Uc ∪ Vc) (Set.subset_union_left) n₀ K U₀
      (fun m'' hmK'' => hU m'' hmK'') m' hmK'
    simpa only [CupBij, subSet, subInclST, subInclT] using h
  have hV'' : ∀ m' : ℕ, m' + n₀ ≤ K →
      CupBij {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} n₀
        ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(Uc ∪ Vc), X))
          {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀)
        {y : ↥(Uc ∪ Vc) | (y : X) ∈ Vc} m' := by
    intro m' hmK'
    have h := bijective_cup_subSet A Vc (Uc ∪ Vc) (Set.subset_union_right) n₀ K U₀
      (fun m'' hmK'' => hV m'' hmK'') m' hmK'
    simpa only [CupBij, subSet, subInclST, subInclT] using h
  have hUV'' : ∀ m' : ℕ, m' + n₀ ≤ K →
      CupBij {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} n₀
        ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(Uc ∪ Vc), X))
          {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀)
        ({y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc} ∩ {y : ↥(Uc ∪ Vc) | (y : X) ∈ Vc}) m' := by
    intro m' hmK'
    have h := bijective_cup_subSet A (Uc ∩ Vc) (Uc ∪ Vc)
      (Set.inter_subset_left.trans Set.subset_union_left) n₀ K U₀
      (fun m'' hmK'' => hUV m'' hmK'') m' hmK'
    have hset : (subSet (Uc ∩ Vc) (Uc ∪ Vc) : Set ↥(Uc ∪ Vc))
        = subSet Uc (Uc ∪ Vc) ∩ subSet Vc (Uc ∪ Vc) := rfl
    refine CupBij_congr_set hset ?_
    simpa only [CupBij, subSet, subInclST, subInclT] using h
  exact Work.Serre.bijective_mixedCup_of_openCover_aux
    {y : ↥(Uc ∪ Vc) | (y : X) ∈ A}
    {y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc} {y : ↥(Uc ∪ Vc) | (y : X) ∈ Vc}
    hUo' hVo' hcov' n₀ K
    ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(Uc ∪ Vc), X))
      {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀)
    hU'' hV'' hUV''
    (fun m' => Work.Serre.mvDeltaCupMixed (TopCat.of ↥(Uc ∪ Vc))
      {y : ↥(Uc ∪ Vc) | (y : X) ∈ A}
      {y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc} {y : ↥(Uc ∪ Vc) | (y : X) ∈ Vc}
      hUo' hVo' hcov' n₀ _ m')
    m hm hmK





end

end Work.RatHurewicz
