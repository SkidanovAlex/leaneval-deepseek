/-
# Uniqueness of the `∗`-regular envelope on the two sides of a rank-preserving pair of maps

Let `θ : U[t^{±1};τ] →+* U` and `f : U[t^{±1};τ] →+* P` be two `∗`-homomorphisms into
`∗`-regular `∗`-rings `U`, `P`, and let `rkU`, `rkP` be *faithful* Sylvester rank functions on
`U`, `P` which agree on all matrices over `U[t^{±1};τ]` (mapped along `θ`, resp. `f`).

Then the `∗`-regular closures of the images of `θ` and `f` are isomorphic by a `∗`-ring
isomorphism compatible with `θ` and `f`, and the isomorphism preserves the rank of `1 × 1`
matrices.  This is [JZLA20, Theorem 2.9] (= [Jaikin, GAFA 2019, Theorem 6.3]) applied to the
*epic* `∗`-regular envelopes `(closure of im θ, θ, rkU)` and `(closure of im f, f, rkP)`: the
co-restriction of `θ` (resp. `f`) to the `∗`-regular closure of its image is epic by
[JZLA20, Proposition 2.7] (`isEpic_of_starRegularClosure`), and the pulled-back rank functions are
faithful because `rkU`, `rkP` are.

The proof is the assembly:

* `closureCorestrict θ`, `closureCorestrict f` are the co-restricted maps
  (`NaturalExtension.envelopeDefs`);
* they are `∗`-homomorphisms and epic (`isEpic_closureCorestrict`, whose content is the generation
  statement `starRegularClosure_codRestrict_top`);
* the pullbacks of `rkU`, `rkP` along the inclusions of the closures are faithful;
* the rank agreement hypothesis transports to the closures, since mapping a matrix along the
  co-restriction and then along the inclusion is mapping it along `θ`, resp. `f`;
* `Section3.envelopeUniqueness_aux` produces the isomorphism and its rank preservation.
-/
import Mathlib
import Submission.Work.ORHughesFree.Section6.StarSkewL
import Submission.Work.ORHughesFree.Section3.envelopeUniqueness_star
import Submission.Work.ORHughesFree.NaturalExtension.envelopeDefs
import Submission.Work.ORHughesFree.NaturalExtension.isEpic_closureCorestrict
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.Epic
import Submission.Work.ORHughesFree.Instances

set_option linter.style.haveILetI false

namespace Work.ORHughesFree.Section6

theorem exists_ringEquiv_of_ranks {U P : Type} [Ring U] [StarRing U] [IsStarRegular U]
    [Ring P] [StarRing P] [IsStarRegular P]
    [MulSemiringAction (Multiplicative ℤ) U] [Work.ORHughesFree.NaturalExtension.StarAction U]
    (rkU : Work.ORHughesFree.SylvesterRank U) (hfaithU : rkU.IsFaithful)
    (rkP : Work.ORHughesFree.SylvesterRank P) (hfaithP : rkP.IsFaithful)
    (θ : SkewMonoidAlgebra U (Multiplicative ℤ) →+* U)
    (hθ : ∀ p : SkewMonoidAlgebra U (Multiplicative ℤ),
      θ (Work.ORHughesFree.NaturalExtension.starSkewL p) = star (θ p))
    (f : SkewMonoidAlgebra U (Multiplicative ℤ) →+* P)
    (hf : ∀ p : SkewMonoidAlgebra U (Multiplicative ℤ),
      f (Work.ORHughesFree.NaturalExtension.starSkewL p) = star (f p))
    (hrank : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (SkewMonoidAlgebra U (Multiplicative ℤ))),
      rkU.rk n m (A.map θ) = rkP.rk n m (A.map f)) :
    ∃ e : ↥(Work.ORHughesFree.starRegularClosure
            (Work.ORHughesFree.starSubringClosure (Set.range θ))) ≃+*
          ↥(Work.ORHughesFree.starRegularClosure
            (Work.ORHughesFree.starSubringClosure (Set.range f))),
      (∀ p : SkewMonoidAlgebra U (Multiplicative ℤ),
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
  have hθ' : ∀ p : SkewMonoidAlgebra U (Multiplicative ℤ),
      NaturalExtension.closureCorestrict θ (star p) =
        star (NaturalExtension.closureCorestrict θ p) := by
    intro p
    apply Subtype.ext
    exact hθ p
  have hf' : ∀ p : SkewMonoidAlgebra U (Multiplicative ℤ),
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
  -- ... and agree on matrices over `U[t^{±1};τ]`
  have hmat : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (SkewMonoidAlgebra U (Multiplicative ℤ))),
      rk₁.rk n m (A.map (NaturalExtension.closureCorestrict θ)) =
        rk₂.rk n m (A.map (NaturalExtension.closureCorestrict f)) := by
    intro n m A
    have h1 : rk₁.rk n m (A.map (NaturalExtension.closureCorestrict θ)) = rkU.rk n m (A.map θ) := by
      show rkU.rk n m ((A.map (NaturalExtension.closureCorestrict θ)).map
        (Subring.subtype A₁.toSubring)) = rkU.rk n m (A.map θ)
      congr 1
    have h2 : rk₂.rk n m (A.map (NaturalExtension.closureCorestrict f)) = rkP.rk n m (A.map f) := by
      show rkP.rk n m ((A.map (NaturalExtension.closureCorestrict f)).map
        (Subring.subtype A₂.toSubring)) = rkP.rk n m (A.map f)
      congr 1
    rw [h1, h2]
    exact hrank n m A
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
