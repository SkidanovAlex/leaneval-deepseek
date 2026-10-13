/-
  Area E7 / the `CoreLT_succ` endgame, node **E2S**: the degenerate branches of the refinement,
  where the cells of `B` over `b` already do the job.
-/
import Mathlib
import Submission.Work.WilE7.Endgame.Bv2.refAux
import Submission.Work.WilE7.Endgame.Bv2.refDec
import Submission.Work.WilE7.Endgame.E2_swapStratum_projFirst

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

/-- A member of `B` projecting onto `b` is contained in the cube slice over `b`. -/
theorem filter_subset_slice {n : ℕ} {B : Finset (Set (Fin (n + 1) → ℝ))}
    {b : Set (Fin n → ℝ)} {κ : Set (Fin (n + 1) → ℝ)}
    (hκ : κ ∈ B.filter (fun κ => Fin.init '' κ = b)) : κ ⊆ {z | Fin.init z ∈ b} := by
  intro z hz
  have : Fin.init z ∈ Fin.init '' κ := ⟨z, hz, rfl⟩
  rw [(Finset.mem_filter.mp hκ).2] at this
  exact this

/-- `Fin.init` of a `π_{n+1}`-image is the base projection. -/
theorem init_image_projFirst {n m : ℕ} (S : Set (Fin ((n + 1) + m) → ℝ)) :
    Fin.init '' (projFirst (n + 1) m '' S) = basePr n m '' S := by
  ext y
  constructor
  · rintro ⟨w, ⟨z, hz, rfl⟩, hwy⟩
    exact ⟨z, hz, by rw [← E2.init_projFirst]; exact hwy⟩
  · rintro ⟨z, hz, hzy⟩
    exact ⟨projFirst (n + 1) m z, ⟨z, hz, rfl⟩, by rw [E2.init_projFirst]; exact hzy⟩

/-- **The empty-piece branch.**  If `Pie` is empty then the images of the outer family `X` are
empty over the whole cube, so the cells of `B` over `b` are trivially compatible. -/
theorem refTriv_empty {hFC : HypFC} {hE2 : HypE2} {hE5 : HypE5} {hE6 : HypE6}
    {h0 : FrontierRestrat} {h1 : SigmaVPairs} {hV : GCaseVertical} {n K F : ℕ}
    (E : E2Env hFC hE2 hE5 hE6 h0 h1 hV n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    (E2 : E2Env2 E Fq Qq)
    {D k l m m' : ℕ} {X : Fin k → SemiPf ((n + 1) + m)} {Y : Fin l → SemiPf (n + m')}
    (d : E2Data E Fq Qq D k l m m' X Y)
    (B : Finset (Set (Fin (n + 1) → ℝ)))
    (hB : IsCylDecompOn (n + 1) (cubeC (n + 1)) B)
    {b : Set (Fin n → ℝ)} (hb : b ∈ B.image (fun κ => Fin.init '' κ))
    (hPie : d.Pie = []) :
    ∃ B' : Finset (Set (Fin (n + 1) → ℝ)),
      ((∀ κ ∈ B', κ ∈ B) ∨
        ((∀ κ ∈ B', (∃ P₀ : StarPiece (n + 1), P₀.set = κ ∧ P₀.X.fmt ≤ E2.AB ∧
            P₀.X.deg ≤ E2.CB.eval D) ∧ SubPf (n + 1) κ) ∧
          B'.card ≤ MvPolynomial.eval ![D, k, l] E.Ng)) ∧
      IsCylDecompOn (n + 1) (cubeC (n + 1) ∩ {z | Fin.init z ∈ b}) B' ∧
      (∀ κ ∈ B', Fin.init '' κ = b) ∧
      (∀ i, ∀ κ ∈ B', κ ⊆ projFirst (n + 1) m '' (X i).set ∨
        Disjoint κ (projFirst (n + 1) m '' (X i).set)) := by
  refine refFilter E E2 d B hB hb ?_
  intro i κ _
  have he : projFirst (n + 1) m '' (X i).set = ∅ := by
    rw [d.hPieCov i, hPie]
    simp
  rw [he]
  exact Or.inr (by rw [Set.disjoint_left]; intro x _ hx; exact hx)

/-- **The no-active-cut branch.**  If `b` misses the `π_n`-image of every member of the `π_n`-cut
`Cut`, then it misses the image of the whole outer family, and the cells of `B` over `b` are
disjoint from every `π_{n+1}(X i)`. -/
theorem refTriv_noCut {hFC : HypFC} {hE2 : HypE2} {hE5 : HypE5} {hE6 : HypE6}
    {h0 : FrontierRestrat} {h1 : SigmaVPairs} {hV : GCaseVertical} {n K F : ℕ}
    (E : E2Env hFC hE2 hE5 hE6 h0 h1 hV n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    (E2 : E2Env2 E Fq Qq)
    {D k l m m' : ℕ} {X : Fin k → SemiPf ((n + 1) + m)} {Y : Fin l → SemiPf (n + m')}
    (d : E2Data E Fq Qq D k l m m' X Y)
    (B : Finset (Set (Fin (n + 1) → ℝ)))
    (hB : IsCylDecompOn (n + 1) (cubeC (n + 1)) B)
    {b : Set (Fin n → ℝ)} (hb : b ∈ B.image (fun κ => Fin.init '' κ))
    (hno : ∀ R ∈ d.Cut, Disjoint b (projFirst n (m + 1) '' absSet R)) :
    ∃ B' : Finset (Set (Fin (n + 1) → ℝ)),
      ((∀ κ ∈ B', κ ∈ B) ∨
        ((∀ κ ∈ B', (∃ P₀ : StarPiece (n + 1), P₀.set = κ ∧ P₀.X.fmt ≤ E2.AB ∧
            P₀.X.deg ≤ E2.CB.eval D) ∧ SubPf (n + 1) κ) ∧
          B'.card ≤ MvPolynomial.eval ![D, k, l] E.Ng)) ∧
      IsCylDecompOn (n + 1) (cubeC (n + 1) ∩ {z | Fin.init z ∈ b}) B' ∧
      (∀ κ ∈ B', Fin.init '' κ = b) ∧
      (∀ i, ∀ κ ∈ B', κ ⊆ projFirst (n + 1) m '' (X i).set ∨
        Disjoint κ (projFirst (n + 1) m '' (X i).set)) := by
  classical
  have hall : Disjoint b (⋃ i : Fin k, basePr n m '' (X i).set) := by
    rw [d.hCutCov]
    rw [Set.disjoint_iUnion_right]
    intro R
    rw [Set.disjoint_iUnion_right]
    intro hR
    exact hno R hR
  have hdisj_base : ∀ i : Fin k, Disjoint b (basePr n m '' (X i).set) := fun i =>
    hall.mono_right (Set.subset_iUnion (fun i : Fin k => basePr n m '' (X i).set) i)
  refine refFilter E E2 d B hB hb ?_
  intro i κ hκ
  right
  rw [Set.disjoint_left]
  intro z hzκ hzX
  have hzb : Fin.init z ∈ b := filter_subset_slice hκ hzκ
  have hzbase : Fin.init z ∈ basePr n m '' (X i).set := by
    rw [← init_image_projFirst (n := n) (m := m) (X i).set]
    exact ⟨z, hzX, rfl⟩
  exact (Set.disjoint_left.mp (hdisj_base i)) hzb hzbase

end Work.WilE7.Endgame.Bv2
