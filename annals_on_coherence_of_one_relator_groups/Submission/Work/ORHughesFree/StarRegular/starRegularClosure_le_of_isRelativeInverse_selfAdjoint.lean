import Mathlib
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.isRelativeInverse_unique
import Submission.Work.ORHughesFree.StarRegular.exists_isRelativeInverse
import Submission.Work.ORHughesFree.StarRegular.isProperStar_starSubring
import Submission.Work.ORHughesFree.StarRegular.starRegularClosure_le
import Submission.Work.ORHughesFree.NaturalExtension.relativeInverse_selfAdjoint

namespace Work.ORHughesFree.StarRegular

open Work.ORHughesFree

/-- If a set `A` and its `star`-image are contained in a subring `E`, then so is the `∗`-subring
that `A` generates. -/
private theorem starSubringClosure_subset_of_subset {U : Type*} [Ring U] [StarRing U]
    (A : Set U) (E : Subring U) (hA : A ⊆ (E : Set U)) (hAs : star '' A ⊆ (E : Set U)) :
    ((starSubringClosure A : StarSubring U) : Set U) ⊆ (E : Set U) := by
  show (Subring.closure (A ∪ star '' A) : Set U) ⊆ (E : Set U)
  refine Subring.closure_le.mpr ?_
  rintro x (hx | hx)
  · exact hA hx
  · obtain ⟨a, ha, hax⟩ := hx
    rw [← hax]
    exact hAs ⟨a, ha, rfl⟩

/-- If a set `A` is contained in `E` and every element of `A` has its `star` in `E`, then the
relative inverses of elements of `A` all lie in `E`, provided `E` is closed under relative
inverses of its *self-adjoint* elements.

The point is that the relative inverse of `a` is `(a∗ a)^{[-1]} a∗`: here `a∗ a` is self-adjoint
and hence its relative inverse lies in `E`, and `a∗` is assumed to lie in `E`. -/
private theorem relativeInverses_subset_of_star_mem {U : Type*} [Ring U] [StarRing U]
    [IsStarRegular U] (E : Subring U)
    (hE : ∀ x : U, x ∈ (E : Set U) → star x = x →
      ∀ y : U, IsRelativeInverse x y → y ∈ (E : Set U))
    {A : Set U} (hA : A ⊆ (E : Set U)) (hAs : star '' A ⊆ (E : Set U)) :
    relativeInverses A ⊆ (E : Set U) := by
  rintro y ⟨a, ha, hay⟩
  have haE : a ∈ (E : Set U) := hA ha
  have hsaE : star a ∈ (E : Set U) := hAs ⟨a, ha, rfl⟩
  have hself : star (star a * a) = star a * a := by rw [star_mul, star_star]
  have hsE : star a * a ∈ (E : Set U) := E.mul_mem hsaE haE
  obtain ⟨v, hv⟩ := exists_isRelativeInverse (star a * a)
  have hvE : v ∈ (E : Set U) := hE (star a * a) hsE hself v hv
  have hrel : IsRelativeInverse a (v * star a) :=
    NaturalExtension.isRelativeInverse_mul_star hv
  have hxa : v * star a = y := isRelativeInverse_unique hrel hay
  rw [← hxa]
  exact E.mul_mem hvE hsaE

theorem starRegularClosure_le_of_isRelativeInverse_selfAdjoint {U : Type*} [Ring U] [StarRing U]
    [Work.ORHughesFree.IsStarRegular U] (R : Work.ORHughesFree.StarSubring U) (E : Subring U)
    (hRE : (R : Set U) ⊆ (E : Set U))
    (hE : ∀ x : U, x ∈ (E : Set U) → star x = x → ∀ y : U, Work.ORHughesFree.IsRelativeInverse x y → y ∈ (E : Set U)) :
    (Work.ORHughesFree.starRegularClosure R : Set U) ⊆ (E : Set U) := by
  -- The chain hypothesis: each `starRegularChain R n` is contained in `E`.
  have hchain : ∀ n, (starRegularChain R n : Set U) ⊆ (E : Set U) := by
    intro n
    induction n with
    | zero => exact hRE
    | succ n ih =>
      have hAst : star '' (starRegularChain R n : Set U) ⊆ (E : Set U) := by
        rintro z hz
        obtain ⟨a, ha, haz⟩ := hz
        rw [← haz]
        exact ih ((starRegularChain R n).star_mem' ha)
      have hA : ((starRegularChain R n : Set U) ∪
          relativeInverses (starRegularChain R n : Set U)) ⊆ (E : Set U) := by
        rintro x (hx | hx)
        · exact ih hx
        · exact relativeInverses_subset_of_star_mem E hE ih hAst hx
      have hAs : (star '' ((starRegularChain R n : Set U) ∪
          relativeInverses (starRegularChain R n : Set U))) ⊆ (E : Set U) := by
        rintro z hz
        obtain ⟨y, hy, hyz⟩ := hz
        rw [← hyz]
        rcases hy with hy | hy
        · exact ih ((starRegularChain R n).star_mem' hy)
        · obtain ⟨a, ha, hay⟩ := hy
          have hsa : star a ∈ (starRegularChain R n : Set U) :=
            (starRegularChain R n).star_mem' ha
          exact hA (Or.inr ⟨star a, hsa, NaturalExtension.isRelativeInverse_star_of hay⟩)
      show ((starSubringClosure ((starRegularChain R n : Set U) ∪
          relativeInverses (starRegularChain R n : Set U)) : StarSubring U) : Set U)
        ⊆ (E : Set U)
      exact starSubringClosure_subset_of_subset _ E hA hAs
  have hUnion : (⋃ n, (starRegularChain R n : Set U)) ⊆ (E : Set U) := by
    rintro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact hchain n hn
  have hUnionStar : star '' (⋃ n, (starRegularChain R n : Set U)) ⊆ (E : Set U) := by
    rintro z hz
    obtain ⟨y, hy, hyz⟩ := hz
    rw [← hyz]
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
    exact hchain n ((starRegularChain R n).star_mem' hn)
  show ((starSubringClosure (⋃ n, (starRegularChain R n : Set U)) : StarSubring U) : Set U)
    ⊆ (E : Set U)
  exact starSubringClosure_subset_of_subset _ E hUnion hUnionStar

end Work.ORHughesFree.StarRegular
