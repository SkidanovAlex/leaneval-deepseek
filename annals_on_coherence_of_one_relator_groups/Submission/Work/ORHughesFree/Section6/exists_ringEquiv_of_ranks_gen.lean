/-
# Uniqueness of the `∗`-regular envelope, generalised base ring

This is `exists_ringEquiv_of_ranks` with the base ring of the skew Laurent polynomial ring
abstracted: instead of `θ, f : U[t^{±1};τ] →+* U', P` one has two `∗`-homomorphisms
`θ, f : A[t^{±1};τ] →+* U, P` out of an arbitrary skew Laurent polynomial ring `A[t^{±1};τ]`
(with `A` a `∗`-ring carrying a `ℤ`-action compatible with `∗`) into `∗`-regular `∗`-rings `U`, `P`,
whose *faithful* Sylvester rank functions agree on all matrices over `A[t^{±1};τ]`.

The argument is *literally* the one of `exists_ringEquiv_of_ranks`: it never uses the fact that the
coefficient ring is the target of the maps, only that `S := A[t^{±1};τ]` is a `∗`-ring, that the two
maps are `∗`-homomorphisms into `∗`-regular rings, and the rank agreement hypothesis.  Both
`NaturalExtension.closureCorestrict` and `Section3.envelopeUniqueness_aux` are stated for an
arbitrary source ring, so the proof transcribes verbatim.
-/
import Mathlib
import Submission.Work.ORHughesFree.Section6.StarSkewL
import Submission.Work.ORHughesFree.Section6.exists_ringEquiv_of_ranks
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.Epic
import Submission.Work.ORHughesFree.NaturalExtension.isEpic_of_starRegularClosure

set_option linter.style.haveILetI false

namespace Work.ORHughesFree.Section6

theorem exists_ringEquiv_of_ranks_gen {A U P : Type} [Ring A] [StarRing A]
    [MulSemiringAction (Multiplicative ℤ) A] [Work.ORHughesFree.NaturalExtension.StarAction A]
    [Ring U] [StarRing U] [Work.ORHughesFree.IsStarRegular U]
    [Ring P] [StarRing P] [Work.ORHughesFree.IsStarRegular P]
    (rkU : Work.ORHughesFree.SylvesterRank U) (hfaithU : rkU.IsFaithful)
    (rkP : Work.ORHughesFree.SylvesterRank P) (hfaithP : rkP.IsFaithful)
    (θ : SkewMonoidAlgebra A (Multiplicative ℤ) →+* U)
    (hθ : ∀ p : SkewMonoidAlgebra A (Multiplicative ℤ),
      θ (Work.ORHughesFree.NaturalExtension.starSkewL p) = star (θ p))
    (f : SkewMonoidAlgebra A (Multiplicative ℤ) →+* P)
    (hf : ∀ p : SkewMonoidAlgebra A (Multiplicative ℤ),
      f (Work.ORHughesFree.NaturalExtension.starSkewL p) = star (f p))
    (hrank : ∀ (n m : ℕ) (B : Matrix (Fin n) (Fin m) (SkewMonoidAlgebra A (Multiplicative ℤ))),
      rkU.rk n m (B.map θ) = rkP.rk n m (B.map f)) :
    ∃ e : ↥(Work.ORHughesFree.starRegularClosure
            (Work.ORHughesFree.starSubringClosure (Set.range θ))) ≃+*
          ↥(Work.ORHughesFree.starRegularClosure
            (Work.ORHughesFree.starSubringClosure (Set.range f))),
      (∀ p : SkewMonoidAlgebra A (Multiplicative ℤ),
        e ⟨θ p, Work.ORHughesFree.subset_starRegularClosure _
            (Work.ORHughesFree.subset_starSubringClosure _ (Set.mem_range_self p))⟩ =
          ⟨f p, Work.ORHughesFree.subset_starRegularClosure _
            (Work.ORHughesFree.subset_starSubringClosure _ (Set.mem_range_self p))⟩) ∧
      (∀ x : ↥(Work.ORHughesFree.starRegularClosure
            (Work.ORHughesFree.starSubringClosure (Set.range θ))),
        rkP.rk 1 1 (Work.ORHughesFree.oneByOne (e x)) =
          rkU.rk 1 1 (Work.ORHughesFree.oneByOne (x : U))) := by
  classical
  -- The two `∗`-regular closures, abbreviated
  let A₁ : StarSubring U := starRegularClosure (starSubringClosure (Set.range θ))
  let A₂ : StarSubring P := starRegularClosure (starSubringClosure (Set.range f))
  haveI hSR₁ : IsStarRegular ↥A₁ := StarRegular.starRegularClosure_isStarRegular _
  haveI hSR₂ : IsStarRegular ↥A₂ := StarRegular.starRegularClosure_isStarRegular _
  -- The co-restrictions are `∗`-homomorphisms
  have hθ' : ∀ p : SkewMonoidAlgebra A (Multiplicative ℤ),
      NaturalExtension.closureCorestrict θ (star p) =
        star (NaturalExtension.closureCorestrict θ p) := by
    intro p
    apply Subtype.ext
    exact hθ p
  have hf' : ∀ p : SkewMonoidAlgebra A (Multiplicative ℤ),
      NaturalExtension.closureCorestrict f (star p) =
        star (NaturalExtension.closureCorestrict f p) := by
    intro p
    apply Subtype.ext
    exact hf p
  -- ... hence epic: the `∗`-regular closure of the image of the co-restriction is the closure
  -- itself (via `starRegularClosure_codRestrict_top`, packaged as `isEpic_closureCorestrict`)
  have hepic₁ : IsEpic (NaturalExtension.closureCorestrict θ) :=
    NaturalExtension.isEpic_closureCorestrict θ hθ
  have hepic₂ : IsEpic (NaturalExtension.closureCorestrict f) :=
    NaturalExtension.isEpic_closureCorestrict f hf
  -- The rank functions on the two closures, pulled back along the inclusions
  let rk₁ : SylvesterRank ↥A₁ := SylvesterRank.pullback (Subring.subtype A₁.toSubring) rkU
  let rk₂ : SylvesterRank ↥A₂ := SylvesterRank.pullback (Subring.subtype A₂.toSubring) rkP
  -- ... which are faithful because `rkU`, `rkP` are
  have hfaith₁ : rk₁.IsFaithful := by
    intro a ha
    have h1 : rkU.rk 1 1 (oneByOne (a : U)) = 0 := by
      have h2 := ha
      change rkU.rk 1 1 ((oneByOne a).map (Subring.subtype A₁.toSubring)) = 0 at h2
      rwa [show (oneByOne a).map (Subring.subtype A₁.toSubring) =
        oneByOne ((Subring.subtype A₁.toSubring) a) from rfl] at h2
    exact Subtype.ext (hfaithU _ h1)
  have hfaith₂ : rk₂.IsFaithful := by
    intro a ha
    have h1 : rkP.rk 1 1 (oneByOne (a : P)) = 0 := by
      have h2 := ha
      change rkP.rk 1 1 ((oneByOne a).map (Subring.subtype A₂.toSubring)) = 0 at h2
      rwa [show (oneByOne a).map (Subring.subtype A₂.toSubring) =
        oneByOne ((Subring.subtype A₂.toSubring) a) from rfl] at h2
    exact Subtype.ext (hfaithP _ h1)
  -- ... and agree on matrices over `A[t^{±1};τ]`
  have hmat : ∀ (n m : ℕ)
      (B : Matrix (Fin n) (Fin m) (SkewMonoidAlgebra A (Multiplicative ℤ))),
      rk₁.rk n m (B.map (NaturalExtension.closureCorestrict θ)) =
        rk₂.rk n m (B.map (NaturalExtension.closureCorestrict f)) := by
    intro n m B
    have h1 : rk₁.rk n m (B.map (NaturalExtension.closureCorestrict θ)) =
        rkU.rk n m (B.map θ) := by
      show rkU.rk n m ((B.map (NaturalExtension.closureCorestrict θ)).map
        (Subring.subtype A₁.toSubring)) = rkU.rk n m (B.map θ)
      congr 1
    have h2 : rk₂.rk n m (B.map (NaturalExtension.closureCorestrict f)) =
        rkP.rk n m (B.map f) := by
      show rkP.rk n m ((B.map (NaturalExtension.closureCorestrict f)).map
        (Subring.subtype A₂.toSubring)) = rkP.rk n m (B.map f)
      congr 1
    rw [h1, h2]
    exact hrank n m B
  -- Uniqueness of the epic `∗`-regular envelope
  obtain ⟨e, he1, he2⟩ := Section3.envelopeUniqueness_aux
    (NaturalExtension.closureCorestrict θ) (NaturalExtension.closureCorestrict f)
    rk₁ rk₂ hθ' hf' hepic₁ hepic₂ hfaith₁ hfaith₂ hmat
  refine ⟨e, ?_, ?_⟩
  · intro p
    exact he1 p
  · intro x
    have h := he2 x
    have h₁ : rk₁.rk 1 1 (oneByOne x) = rkU.rk 1 1 (oneByOne (x : U)) := rfl
    have h₂ : rk₂.rk 1 1 (oneByOne (e x)) = rkP.rk 1 1 (oneByOne (e x)) := rfl
    rw [← h₁, ← h₂]
    exact h

end Work.ORHughesFree.Section6
