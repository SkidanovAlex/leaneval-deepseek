import Mathlib
import Submission.Work.PiS.Interfaces
import Submission.Work.ThomBordism.homologyFinite_of_isRetract
import Submission.Work.EMFG.piSubtypeHomeo
import Submission.Work.EMFG.contractibleSpace_pi

/-!
# A product of spaces with finite good covers has finitely generated homology

If each factor `X i` of a **finite** product `∏ i, X i` carries a finite good family `U i` covering it
(open sets with contractible nonempty finite intersections), then so does the product: the basic
products `∏ i, U i (f i)` indexed by `f : ∀ i, κ i` are open, their nonempty finite intersections are
basic products of the contractible intersections `⋂ j, U i (g j i)`, and they cover.  Feeding that
family to `Work.ThomBordism.fgch_finiteHomology_of_goodFam_fintype` yields
`Work.EMFG.piGoodFamFG`: the product has finitely generated integral singular homology in every
degree.

This is the product form of the good-cover finiteness theorem, used to build finite-type models of
products of Eilenberg–MacLane range models (`Work.EMFG.isEMSpaceUpTo_pi` is its homotopy-theoretic
companion).
-/

set_option linter.style.haveILetI false

namespace Work.EMFG

noncomputable section

/-- The *product good family*: for families `U i : κ i → Set (X i)`, the family of basic open
products indexed by `∀ i, κ i`. -/
def piGoodFamily {ι : Type} {X : ι → Type} {κ : ι → Type} (U : ∀ i, κ i → Set (X i)) :
    (∀ i, κ i) → Set ((i : ι) → X i) :=
  fun f => Set.pi Set.univ fun i => U i (f i)

/-- Unfolding lemma for `Work.EMFG.piGoodFamily`. -/
@[simp] theorem piGoodFamily_apply {ι : Type} {X : ι → Type} {κ : ι → Type}
    (U : ∀ i, κ i → Set (X i)) (f : ∀ i, κ i) :
    piGoodFamily U f = Set.pi Set.univ (fun i => U i (f i)) := rfl

/-- `Work.EMFG.piGoodFamily` is a good family whenever each `U i` is. -/
theorem isGoodFam_piGoodFamily {ι : Type} [Fintype ι] {X : ι → Type}
    [∀ i, TopologicalSpace (X i)] {κ : ι → Type} [∀ i, Fintype (κ i)]
    (U : ∀ i, κ i → Set (X i)) (hgood : ∀ i, Work.ThomBordism.IsGoodFam (U i)) :
    Work.ThomBordism.IsGoodFam (piGoodFamily U) := by
  classical
  refine ⟨fun f => isOpen_set_pi Set.finite_univ (fun i _ => (hgood i).1 (f i)), ?_⟩
  intro β _ g b hne
  have hEq : (⋂ j : β, piGoodFamily U (g j))
      = Set.pi Set.univ (fun i => ⋂ j : β, U i (g j i)) := by
    ext x
    simp only [piGoodFamily_apply, Set.mem_iInter, Set.mem_pi, Set.mem_univ, true_implies]
    exact forall_comm
  rw [hEq]
  have hc : ∀ i, ContractibleSpace ↥(⋂ j : β, U i (g j i)) := by
    intro i
    obtain ⟨x, hx⟩ := hne
    refine (hgood i).2 β (fun j => g j i) b ⟨x i, ?_⟩
    rw [Set.mem_iInter]
    intro j
    have h1 : x ∈ piGoodFamily U (g j) := Set.mem_iInter.mp hx j
    simpa only [piGoodFamily_apply, Set.mem_pi, Set.mem_univ, true_implies] using h1 i
  haveI : ContractibleSpace ((i : ι) → ↥(⋂ j : β, U i (g j i))) := contractibleSpace_pi hc
  exact (piSubtypeHomeo (fun i => ⋂ j : β, U i (g j i))).some.contractibleSpace

/-- `Work.EMFG.piGoodFamily` covers the product whenever each `U i` covers `X i`. -/
theorem iUnion_piGoodFamily {ι : Type} [Fintype ι] {X : ι → Type}
    [∀ i, TopologicalSpace (X i)] {κ : ι → Type} [∀ i, Fintype (κ i)]
    (U : ∀ i, κ i → Set (X i)) (hcov : ∀ i, (⋃ j, U i j) = Set.univ) :
    (⋃ f, piGoodFamily U f) = Set.univ := by
  classical
  ext x
  constructor
  · intro _; exact Set.mem_univ x
  · intro _
    have hx : ∀ i, ∃ j, x i ∈ U i j := fun i => by
      have h : x i ∈ (⋃ j, U i j) := by rw [hcov i]; exact Set.mem_univ _
      exact Set.mem_iUnion.mp h
    choose f hf using hx
    exact Set.mem_iUnion.mpr ⟨f, by
      simpa only [piGoodFamily_apply, Set.mem_pi, Set.mem_univ, true_implies] using hf⟩

theorem piGoodFamFG {ι : Type} [Fintype ι] {X : ι → Type} [∀ i, TopologicalSpace (X i)]
    {κ : ι → Type} [∀ i, Fintype (κ i)] (U : ∀ i, κ i → Set (X i))
    (hgood : ∀ i, Work.ThomBordism.IsGoodFam (U i))
    (hcov : ∀ i, (⋃ j, U i j) = Set.univ) (k : ℕ) :
    Module.Finite ℤ (Work.PiS.HZ ((i : ι) → X i) k) := by
  classical
  exact Work.ThomBordism.fgch_finiteHomology_of_goodFam_fintype (Z := (i : ι) → X i)
    (piGoodFamily U) (isGoodFam_piGoodFamily U hgood) (iUnion_piGoodFamily U hcov) k

end

end Work.EMFG
