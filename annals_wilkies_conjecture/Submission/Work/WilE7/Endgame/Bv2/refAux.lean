/-
  Area E7 / the `CoreLT_succ` endgame, node **E2S**: plumbing for the per-base-cell refinement.
-/
import Mathlib
import Submission.Work.WilE7.Endgame.Bv2.Data
import Submission.Work.WilE7.Endgame.Bv2.Env
import Submission.Work.WilE7.Endgame.Bv2.Aux2
import Submission.Work.WilE7.DimAPI.cylDecomp_fiber
import Submission.Work.WilE7.DimAPI.isCylDecompOn_liftFam

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7.Endgame.Bv2

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt vertCoord)
open Work.WilE7.CoreLTSuccPlan (absPairSet2 pairBaseRank)
open Work.CoreStep (frontierSet pairSubBaseFst pairFrontierBaseFst pairBase)

/-! ## §1. The structural facts about a cylindrical decomposition -/

/-- Every member of a cylindrical decomposition of `A` is a subset of `A`. -/
theorem mem_decomp_subset {n : ℕ} {A : Set (Fin n → ℝ)} {C : Finset (Set (Fin n → ℝ))}
    (h : IsCylDecompOn n A C) {c : Set (Fin n → ℝ)} (hc : c ∈ C) : c ⊆ A := by
  cases n with
  | zero =>
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [Finset.mem_singleton] at hc; subst hc; exact Set.subset_univ _
      · simp at hc
  | succ n =>
      intro z hz
      rw [← h.2.2.1]
      exact Set.mem_sUnion.mpr ⟨c, hc, hz⟩

/-- Every member of a cylindrical decomposition is a nonempty cylindrical cell. -/
theorem isCell_nonempty_of_mem_decomp {n : ℕ} {A : Set (Fin n → ℝ)}
    {C : Finset (Set (Fin n → ℝ))} (h : IsCylDecompOn n A C)
    {c : Set (Fin n → ℝ)} (hc : c ∈ C) : IsCell n c ∧ c.Nonempty := by
  cases n with
  | zero =>
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [Finset.mem_singleton] at hc; subst hc
        exact ⟨IsCell.zero, ⟨fun i => i.elim0, Set.mem_univ _⟩⟩
      · simp at hc
  | succ n => exact h.1 c hc

/-- The drop of the base cell: `b ∈ B.image (Fin.init ·)` is a nonempty cell of `cubeC n`. -/
theorem base_cell_data {n : ℕ} {B : Finset (Set (Fin (n + 1) → ℝ))}
    (hB : IsCylDecompOn (n + 1) (cubeC (n + 1)) B) {b : Set (Fin n → ℝ)}
    (hb : b ∈ B.image (fun κ => Fin.init '' κ)) :
    IsCell n b ∧ b.Nonempty ∧ b ⊆ cubeC n := by
  have hB' : IsCylDecompOn n (cubeC n) (B.image (fun κ => Fin.init '' κ)) := by
    have h := hB.2.2.2
    rwa [Work.WilE7.DimAPI.liftFamAux_init_image_cubeC n] at h
  exact ⟨(isCell_nonempty_of_mem_decomp hB' hb).1,
    (isCell_nonempty_of_mem_decomp hB' hb).2, mem_decomp_subset hB' hb⟩

/-- The cylinder over a base set inside the cube is a slice of the cube. -/
theorem cyl_eq_cubeC {n : ℕ} {b : Set (Fin n → ℝ)} (hb : b ⊆ cubeC n) :
    Work.WilE7.cyl b = cubeC (n + 1) ∩ {z | Fin.init z ∈ b} := by
  ext z
  constructor
  · rintro ⟨hz, hlast⟩
    refine ⟨?_, hz⟩
    intro i
    refine Fin.lastCases ?_ ?_ i
    · rw [Fin.last] at hlast ⊢
      exact hlast
    · intro j
      exact hb hz j
  · rintro ⟨hz, hzb⟩
    exact ⟨hzb, hz (Fin.last n)⟩

/-! ## §2. Compatibility with a finite union -/

/-- Compatibility transfers to a union indexed by a `Finset`. -/
theorem compat_of_iUnion_finset {X ι : Type*} {s : Finset ι} {f : ι → Set X} {S κ : Set X}
    (hS : S = ⋃ i ∈ s, f i) (h : ∀ i ∈ s, κ ⊆ f i ∨ Disjoint κ (f i)) :
    κ ⊆ S ∨ Disjoint κ S := by
  by_cases hsome : ∃ i ∈ s, κ ⊆ f i
  · obtain ⟨i, hi, hsub⟩ := hsome
    left
    intro x hx
    rw [hS]
    exact Set.mem_iUnion₂.mpr ⟨i, hi, hsub hx⟩
  · right
    rw [Set.disjoint_left]
    intro x hx hxS
    rw [hS, Set.mem_iUnion₂] at hxS
    obtain ⟨i, hi, hxi⟩ := hxS
    by_cases hsub : κ ⊆ f i
    · exact hsome ⟨i, hi, hsub⟩
    · exact Set.disjoint_left.mp ((h i hi).resolve_left hsub) hx hxi

/-- Compatibility transfers to a union indexed by a `List` (image form). -/
theorem compat_of_iUnion_list_map {X Y : Type*} {l : List Y} {f : Y → Set X} {S κ : Set X}
    (hS : S = ⋃ B ∈ l, f B) (h : ∀ B ∈ l, κ ⊆ f B ∨ Disjoint κ (f B)) :
    κ ⊆ S ∨ Disjoint κ S := by
  by_cases hsome : ∃ B ∈ l, κ ⊆ f B
  · obtain ⟨B, hB, hsub⟩ := hsome
    left
    intro x hx
    rw [hS]
    exact Set.mem_iUnion₂.mpr ⟨B, hB, hsub hx⟩
  · right
    rw [Set.disjoint_left]
    intro x hx hxS
    rw [hS, Set.mem_iUnion₂] at hxS
    obtain ⟨B, hB, hxB⟩ := hxS
    by_cases hsub : κ ⊆ f B
    · exact hsome ⟨B, hB, hsub⟩
    · exact Set.disjoint_left.mp ((h B hB).resolve_left hsub) hx hxB

/-! ## §3. The `B`-subfamily branch of the refinement -/

/-- **The `B`-subfamily branch.**  If the cells of `B` lying over `b` are already compatible with
all the outer pieces `π_{n+1}(X i)`, then `B' := B.filter (Fin.init · = b)` is a valid refinement. -/
theorem refFilter {hFC : HypFC} {hE2 : HypE2} {hE5 : HypE5} {hE6 : HypE6}
    {h0 : FrontierRestrat} {h1 : SigmaVPairs} {hV : GCaseVertical} {n K F : ℕ}
    (E : E2Env hFC hE2 hE5 hE6 h0 h1 hV n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    (E2 : E2Env2 E Fq Qq)
    {D k l m m' : ℕ} {X : Fin k → SemiPf ((n + 1) + m)} {Y : Fin l → SemiPf (n + m')}
    (d : E2Data E Fq Qq D k l m m' X Y)
    (B : Finset (Set (Fin (n + 1) → ℝ)))
    (hB : IsCylDecompOn (n + 1) (cubeC (n + 1)) B)
    {b : Set (Fin n → ℝ)} (hb : b ∈ B.image (fun κ => Fin.init '' κ))
    (hcompat : ∀ i, ∀ κ ∈ B.filter (fun κ => Fin.init '' κ = b),
      κ ⊆ projFirst (n + 1) m '' (X i).set ∨
        Disjoint κ (projFirst (n + 1) m '' (X i).set)) :
    ∃ B' : Finset (Set (Fin (n + 1) → ℝ)),
      ((∀ κ ∈ B', κ ∈ B) ∨
        ((∀ κ ∈ B', (∃ P₀ : StarPiece (n + 1), P₀.set = κ ∧ P₀.X.fmt ≤ E2.AB ∧
            P₀.X.deg ≤ E2.CB.eval D) ∧ SubPf (n + 1) κ) ∧
          B'.card ≤ MvPolynomial.eval ![D, k, l] E.Ng)) ∧
      IsCylDecompOn (n + 1) (cubeC (n + 1) ∩ {z | Fin.init z ∈ b}) B' ∧
      (∀ κ ∈ B', Fin.init '' κ = b) ∧
      (∀ i, ∀ κ ∈ B', κ ⊆ projFirst (n + 1) m '' (X i).set ∨
        Disjoint κ (projFirst (n + 1) m '' (X i).set)) :=
  ⟨B.filter (fun κ => Fin.init '' κ = b),
    Or.inl (fun κ hκ => (Finset.mem_filter.mp hκ).1),
    Work.WilE7.DimAPI.cylDecomp_fiber (cubeC (n + 1)) B hB b hb,
    (fun κ hκ => (Finset.mem_filter.mp hκ).2),
    hcompat⟩

end Work.WilE7.Endgame.Bv2
