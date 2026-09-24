import Mathlib
import Submission.Work.SimplyConnected.Defs

namespace Work.SimplyConnected.ABS

open Set
open scoped Topology
open Classical

variable {X : Type*} [TopologicalSpace X]

/-- An **exhaustion piece** of the ABS exhaustion: an open, connected, simply connected set with
compact closure and connected frontier.  (The frontier connectivity is needed for the "disc lemma"
for the pieces.) -/
def IsExhaustionPiece (Ω : Set X) : Prop :=
  IsOpen Ω ∧ IsConnected Ω ∧ IsSimplyConnected Ω ∧ IsCompact (closure Ω) ∧
    IsConnected (frontier Ω)

section Reduction

variable [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]

/-- The **one-step growth statement**: every compact subset of `X` is contained in an exhaustion
piece.  This is the geometric content of the ABS exhaustion (Theorem 12 of
Anghel–Bruin–Stan), isolated here. -/
def HasGrowth (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ K : Set X, IsCompact K → ∃ Ω : Set X, IsExhaustionPiece Ω ∧ K ⊆ Ω

/-- A choice of an exhaustion piece containing a given compact set. -/
noncomputable def pieceOf (hg : HasGrowth X) (K : Set X) : Set X :=
  if h : IsCompact K then Classical.choose (hg K h) else ∅

theorem pieceOf_spec (hg : HasGrowth X) {K : Set X} (hK : IsCompact K) :
    IsExhaustionPiece (pieceOf hg K) ∧ K ⊆ pieceOf hg K := by
  have h : (pieceOf hg K) = Classical.choose (hg K hK) := by
    rw [pieceOf, dif_pos hK]
  rw [h]
  exact (Classical.choose_spec (hg K hK))

/-- The exhaustion constructed from the one-step growth statement, along a fixed compact
exhaustion of `X`. -/
noncomputable def growthExhaustion (K : CompactExhaustion X) (hg : HasGrowth X) (x₀ : X) :
    ℕ → Set X
  | 0 => pieceOf hg (K 0 ∪ {x₀})
  | (n + 1) => pieceOf hg (K (n + 1) ∪ closure (growthExhaustion K hg x₀ n))

theorem growthExhaustion_isExhaustionPiece (K : CompactExhaustion X) (hg : HasGrowth X) (x₀ : X) :
    ∀ n, IsExhaustionPiece (growthExhaustion K hg x₀ n) := by
  intro n
  induction n with
  | zero => exact (pieceOf_spec hg (K.isCompact 0 |>.union isCompact_singleton)).1
  | succ k ih =>
    refine (pieceOf_spec hg ?_).1
    exact (K.isCompact (k+1)).union ih.2.2.2.1

/-- **The reduction**: the one-step growth statement implies the exhaustion of `X` by exhaustion
pieces nested with `closure (Ω n) ⊆ Ω (n+1)`, containing `x₀` and covering `X`. -/
theorem exists_exhaustion_of_growth (K : CompactExhaustion X) (hg : HasGrowth X) (x₀ : X) :
    ∃ Ω : ℕ → Set X, (∀ n, IsOpen (Ω n)) ∧ (∀ n, IsConnected (Ω n)) ∧
      (∀ n, IsSimplyConnected (Ω n)) ∧ (∀ n, IsCompact (closure (Ω n))) ∧
      (∀ n, IsConnected (frontier (Ω n))) ∧
      (∀ n, closure (Ω n) ⊆ Ω (n + 1)) ∧ x₀ ∈ Ω 0 ∧ (⋃ n, Ω n) = Set.univ := by
  refine ⟨growthExhaustion K hg x₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n; exact (growthExhaustion_isExhaustionPiece K hg x₀ n).1
  · intro n; exact (growthExhaustion_isExhaustionPiece K hg x₀ n).2.1
  · intro n; exact (growthExhaustion_isExhaustionPiece K hg x₀ n).2.2.1
  · intro n; exact (growthExhaustion_isExhaustionPiece K hg x₀ n).2.2.2.1
  · intro n; exact (growthExhaustion_isExhaustionPiece K hg x₀ n).2.2.2.2
  · intro n
    have h := (pieceOf_spec hg ((K.isCompact (n+1)).union
      (growthExhaustion_isExhaustionPiece K hg x₀ n).2.2.2.1)).2
    exact fun x hx => h (mem_union_right _ hx)
  · exact (pieceOf_spec hg (K.isCompact 0 |>.union isCompact_singleton)).2 (mem_union_right _ rfl)
  · refine eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn⟩ := K.exists_mem x
    have hsub : K n ⊆ growthExhaustion K hg x₀ n := by
      induction n with
      | zero => exact fun y hy => (pieceOf_spec hg (K.isCompact 0 |>.union
          isCompact_singleton)).2 (mem_union_left _ hy)
      | succ k _ =>
        exact fun y hy => (pieceOf_spec hg ((K.isCompact (k+1)).union
          (growthExhaustion_isExhaustionPiece K hg x₀ k).2.2.2.1)).2 (mem_union_left _ hy)
    exact mem_iUnion.mpr ⟨n, hsub hn⟩

end Reduction

variable [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [SimplyConnectedSpace X]

/-- **Exhaustion of a simply connected non-compact Riemann surface by compact pieces with connected
frontier** (Anghel–Bruin–Stan, *Uniformization of Riemann surfaces revisited*, arXiv:2008.12189,
step 12; the exhaustion step of the ABS proof of uniformization).

`X` is simply connected and non-compact, `x₀ ∈ X`.  Then there are open connected simply connected
sets `Ω n` with compact closure, nested with `closure (Ω n) ⊆ Ω (n + 1)`, whose frontiers
`frontier (Ω n)` are connected, with `x₀ ∈ Ω 0` and `⋃ n, Ω n = univ`.

This is the space-level form, and it asks for connectivity of `frontier (Ω n)` rather than of
`frontier (closure (Ω n))`: that is exactly the hypothesis shape required by the "disc lemma" for
the pieces (biholomorphism `Ω n ≅ ball (0, r n)`), whose Dirichlet problem is solved with boundary
data on `frontier (Ω n)`.  In the ABS construction (a proper smooth function `g`, a regular value
`a`, and filling the relatively compact components of the complement) the pieces are `Ω n = K nᵒ`
for compact sub-surfaces `K n` with connected smooth boundary, so `frontier (Ω n) = ∂K n` is
connected and `Ω n` is regular open. -/
theorem exists_exhaustion_of_simplyConnectedSpace (hX : ¬ CompactSpace X) (x₀ : X) :
    ∃ Ω : ℕ → Set X, (∀ n, IsOpen (Ω n)) ∧ (∀ n, IsConnected (Ω n)) ∧
      (∀ n, IsSimplyConnected (Ω n)) ∧ (∀ n, IsCompact (closure (Ω n))) ∧
      (∀ n, IsConnected (frontier (Ω n))) ∧
      (∀ n, closure (Ω n) ⊆ Ω (n + 1)) ∧ x₀ ∈ Ω 0 ∧ (⋃ n, Ω n) = Set.univ := by
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  exact exists_exhaustion_of_growth (CompactExhaustion.choice X) (X := X) (by sorry) x₀

end Work.SimplyConnected.ABS
