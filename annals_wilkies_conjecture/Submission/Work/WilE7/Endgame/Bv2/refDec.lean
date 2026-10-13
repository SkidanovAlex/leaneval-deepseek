/-
  Area E7 / the `CoreLT_succ` endgame, node **E2S**: the active/inactive decisions over a base cell.
-/
import Mathlib
import Submission.Work.WilE7.Endgame.Bv2.refAux

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

variable {hFC : HypFC} {hE2 : HypE2} {hE5 : HypE5} {hE6 : HypE6}
  {h0 : FrontierRestrat} {h1 : SigmaVPairs} {hV : GCaseVertical} {n K F : ℕ}
  {Fq : ℕ} {Qq : Polynomial ℕ}
  {D k l m m' : ℕ} {X : Fin k → SemiPf ((n + 1) + m)} {Y : Fin l → SemiPf (n + m')}

/-- The cell of `B` over `b`, from the membership hypothesis. -/
theorem exists_cell_over {n : ℕ} {B : Finset (Set (Fin (n + 1) → ℝ))} {b : Set (Fin n → ℝ)}
    (hb : b ∈ B.image (fun κ => Fin.init '' κ)) :
    ∃ κ₀ ∈ B, Fin.init '' κ₀ = b := Finset.mem_image.mp hb

/-- **The `Σ`-decision.**  Every member of `SigAll` is either met by `b` in its `π_n`-image or
disjoint from it, by compatibility of `B` with the packed family `Y'`. -/
theorem dec_sigAll {hFC : HypFC} {hE2 : HypE2} {hE5 : HypE5} {hE6 : HypE6}
    {h0 : FrontierRestrat} {h1 : SigmaVPairs} {hV : GCaseVertical} {n K F : ℕ}
    (E : E2Env hFC hE2 hE5 hE6 h0 h1 hV n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    (E2 : E2Env2 E Fq Qq)
    {D k l m m' : ℕ} {X : Fin k → SemiPf ((n + 1) + m)} {Y : Fin l → SemiPf (n + m')}
    (d : E2Data E Fq Qq D k l m m' X Y)
    {B : Finset (Set (Fin (n + 1) → ℝ))} {b : Set (Fin n → ℝ)}
    (hb : b ∈ B.image (fun κ => Fin.init '' κ))
    (hBY' : ∀ i, ∀ κ ∈ B, Fin.init '' κ ⊆ projFirst n d.m₂ '' (d.Y' i).set ∨
      Disjoint (Fin.init '' κ) (projFirst n d.m₂ '' (d.Y' i).set)) :
    ∀ S ∈ d.SigAll, b ⊆ projFirst n (pPair n m) '' S.set ∨
      Disjoint b (projFirst n (pPair n m) '' S.set) := by
  intro S hS
  obtain ⟨j, hj⟩ := d.hYall S hS
  obtain ⟨κ₀, hκ₀, hκ₀b⟩ := exists_cell_over hb
  have h := hBY' j κ₀ hκ₀
  rw [hκ₀b, hj] at h
  exact h

/-- **The candidate decision.** -/
theorem dec_cand {hFC : HypFC} {hE2 : HypE2} {hE5 : HypE5} {hE6 : HypE6}
    {h0 : FrontierRestrat} {h1 : SigmaVPairs} {hV : GCaseVertical} {n K F : ℕ}
    (E : E2Env hFC hE2 hE5 hE6 h0 h1 hV n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    (E2 : E2Env2 E Fq Qq)
    {D k l m m' : ℕ} {X : Fin k → SemiPf ((n + 1) + m)} {Y : Fin l → SemiPf (n + m')}
    (d : E2Data E Fq Qq D k l m m' X Y)
    {B : Finset (Set (Fin (n + 1) → ℝ))} {b : Set (Fin n → ℝ)}
    (hb : b ∈ B.image (fun κ => Fin.init '' κ))
    (hBY' : ∀ i, ∀ κ ∈ B, Fin.init '' κ ⊆ projFirst n d.m₂ '' (d.Y' i).set ∨
      Disjoint (Fin.init '' κ) (projFirst n d.m₂ '' (d.Y' i).set)) :
    ∀ S ∈ d.Cand, b ⊆ projFirst n (m + 1) '' absSet S ∨
      Disjoint b (projFirst n (m + 1) '' absSet S) := by
  intro S hS
  obtain ⟨j, hj⟩ := d.hYcand S hS
  obtain ⟨κ₀, hκ₀, hκ₀b⟩ := exists_cell_over hb
  have h := hBY' j κ₀ hκ₀
  rw [hκ₀b, hj] at h
  exact h

/-- **The piece decision.** -/
theorem dec_pie {hFC : HypFC} {hE2 : HypE2} {hE5 : HypE5} {hE6 : HypE6}
    {h0 : FrontierRestrat} {h1 : SigmaVPairs} {hV : GCaseVertical} {n K F : ℕ}
    (E : E2Env hFC hE2 hE5 hE6 h0 h1 hV n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    (E2 : E2Env2 E Fq Qq)
    {D k l m m' : ℕ} {X : Fin k → SemiPf ((n + 1) + m)} {Y : Fin l → SemiPf (n + m')}
    (d : E2Data E Fq Qq D k l m m' X Y)
    {B : Finset (Set (Fin (n + 1) → ℝ))} {b : Set (Fin n → ℝ)}
    (hb : b ∈ B.image (fun κ => Fin.init '' κ))
    (hBY' : ∀ i, ∀ κ ∈ B, Fin.init '' κ ⊆ projFirst n d.m₂ '' (d.Y' i).set ∨
      Disjoint (Fin.init '' κ) (projFirst n d.m₂ '' (d.Y' i).set)) :
    ∀ p ∈ d.Pie, b ⊆ projFirst n (m + 1) '' absSet (Work.WilE7.Endgame.E2.swapStratum p.2) ∨
      Disjoint b (projFirst n (m + 1) '' absSet (Work.WilE7.Endgame.E2.swapStratum p.2)) := by
  intro p hp
  obtain ⟨j, hj⟩ := d.hYpiece p hp
  obtain ⟨κ₀, hκ₀, hκ₀b⟩ := exists_cell_over hb
  have h := hBY' j κ₀ hκ₀
  rw [hκ₀b, hj] at h
  exact h

/-- **The `±1` slice decision.** -/
theorem dec_slice {hFC : HypFC} {hE2 : HypE2} {hE5 : HypE5} {hE6 : HypE6}
    {h0 : FrontierRestrat} {h1 : SigmaVPairs} {hV : GCaseVertical} {n K F : ℕ}
    (E : E2Env hFC hE2 hE5 hE6 h0 h1 hV n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    (E2 : E2Env2 E Fq Qq)
    {D k l m m' : ℕ} {X : Fin k → SemiPf ((n + 1) + m)} {Y : Fin l → SemiPf (n + m')}
    (d : E2Data E Fq Qq D k l m m' X Y)
    {B : Finset (Set (Fin (n + 1) → ℝ))} {b : Set (Fin n → ℝ)}
    (hb : b ∈ B.image (fun κ => Fin.init '' κ))
    (hBY' : ∀ i, ∀ κ ∈ B, Fin.init '' κ ⊆ projFirst n d.m₂ '' (d.Y' i).set ∨
      Disjoint (Fin.init '' κ) (projFirst n d.m₂ '' (d.Y' i).set)) :
    ∀ S ∈ d.Cand, ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      (b ∩ projFirst n (m + 1) '' {z | z ∈ absSet S ∧
          vertCoord (projSnd n (m + 1) z) = σ} = ∅) ∨
      (b ⊆ projFirst n (m + 1) '' {z | z ∈ absSet S ∧
          vertCoord (projSnd n (m + 1) z) = σ}) := by
  intro S hS σ hσ
  have hstep : ∃ j, projFirst n d.m₂ '' (d.Y' j).set =
      projFirst n (m + 1) '' (Work.WilE7.Endgame.E2.sliceSemiPf S σ).set := by
    rcases hσ with rfl | rfl
    · exact d.hYslice1 S hS
    · exact d.hYslice2 S hS
  obtain ⟨j, hj⟩ := hstep
  obtain ⟨κ₀, hκ₀, hκ₀b⟩ := exists_cell_over hb
  have h := hBY' j κ₀ hκ₀
  rw [hκ₀b, hj, Work.WilE7.Endgame.E2.sliceSemiPf_set] at h
  rcases h with hsub | hdis
  · exact Or.inr hsub
  · exact Or.inl (Set.disjoint_iff_inter_eq_empty.mp hdis)

end Work.WilE7.Endgame.Bv2
