/-
  Area E7 / E2B, node `gcaseRefineP2`: **the level data of the sheet family of the `G`-branch**.

  `GSheets` supplies, over the base cell `b`, an active family of candidates `S t` (`Good`,
  of full `π_n`-rank `n + (m + 1) - (S t).j`) together with continuous sheet families
  `sc t j : b → (Fin (m + 1) → ℝ)` whose graphs fill `absSet (S t)` over `b`.  This module
  produces the *level data* of those sheets: writing `lev t j x = (sc t j x) (Fin.last m)`,

  (1) `|lev t j x| ≤ 1` on `b` (`Work.WilE7.CoreStep.gcase_sheets`);
  (2) the trichotomy `lev t j ≡ 1` / `lev t j ≡ -1` / `|lev t j| < 1` on `b`;
  (3) the level dichotomy: if two sheets agree at one point of `b`, they agree on all of `b`.

  All the inputs of `Work.WilE7.CoreStep.gcase_sheets` that are not field of `GSheets` are read off
  the data package `E2Pkg`:

  * `b` is preconnected, being the `Fin.init`-image of a cell of the decomposition `B`
    (`Work.WilE7.Endgame.Bv2.base_cell_data`);
  * the fibres of `absSet (S t)` over `b` are finite, because `G.hcard` computes their `ncard`
    as `kc t > 0` (an infinite fibre would have `ncard = 0`);
  * the `±1`-slice condition `hsl` comes from `P.specY` (which represents the `σ = ±1` slices
    `E2.sliceSemiPf S σ` among the `Yl`-family) together with the compatibility `hB.2.2.1` of the
    decomposition `B` with `Yl`;
  * the pair data `Wl i j` on `absLevelPairSet (S i) (S j)`, with the `Σ`-coverage clauses, is
    `P.specSig`'s level-pair clause for the two candidates;
  * the pointwise pair avoidance `havoid` follows from `GHyp` (the `Σ`-avoidance of `b`) and the
    `Σ`-coverage clauses, through `Work.WilE7.Endgame.havoid_of_sigma_cross`.
-/
import Mathlib
import Submission.Work.WilE7.Endgame.E2B.GSheets
import Submission.Work.WilE7.Endgame.havoid_of_sigma_cross
import Submission.Work.WilE7.Endgame.projRank_ge_of_avoid
import Submission.Work.WilE7.CoreStep.gcase_sheets
import Submission.Work.WilE7.Endgame.E2_activeFamily
import Submission.Work.WilE7.Endgame.Bv2.refAux

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt vertCoord)
open Work.CoreStep (frontierSet pairSubBaseFst pairFrontierBaseFst pairBase)

namespace Work.WilE7.Endgame.E2B

theorem gcaseTrichotomyData {n K F : ℕ} (c : E2Const n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    (c2 : E2Const2 c Fq Qq) {D k l m m' : ℕ} {X : Fin k → WilkiesDesign.E.SemiPf ((n + 1) + m)}
    {Y : Fin l → WilkiesDesign.E.SemiPf (n + m')} (P : E2Pkg c c2 D k l m m' X Y)
    (B : Finset (Set (Fin (n + 1) → ℝ))) (hB : CompatHyp c c2 P B)
    {b : Set (Fin n → ℝ)} (hb : b ∈ B.image (fun κ => Fin.init '' κ))
    (hG : GHyp c c2 P b) (G : GSheets c c2 P b) :
    (∀ t j x, x ∈ b → |(G.sc t j x) (Fin.last m)| ≤ 1) ∧
    (∀ t j, (∀ x ∈ b, (G.sc t j x) (Fin.last m) = 1) ∨
      (∀ x ∈ b, (G.sc t j x) (Fin.last m) = -1) ∨
      (∀ x ∈ b, |(G.sc t j x) (Fin.last m)| < 1)) ∧
    (∀ t t' j j', (∃ x ∈ b, (G.sc t j x) (Fin.last m) = (G.sc t' j' x) (Fin.last m)) →
      ∀ x ∈ b, (G.sc t j x) (Fin.last m) = (G.sc t' j' x) (Fin.last m)) := by
  classical
  obtain ⟨hBdec, hBZl, hBYl, hBpce⟩ := hB
  -- `b` is a cell of the decomposition, hence preconnected.
  obtain ⟨hcell, hbne, hbcube⟩ := Work.WilE7.Endgame.Bv2.base_cell_data hBdec hb
  -- The fibres of `absSet (S t)` over `b` are finite (`hcard` computes their `ncard` as `kc t > 0`).
  have hfin : ∀ (t : Fin G.r) (x : Fin n → ℝ), x ∈ b →
      (WilkiesDesign.E.fiber (absSet (G.S t)) x).Finite := by
    intro t x hx
    by_contra hne
    have hinf : (WilkiesDesign.E.fiber (absSet (G.S t)) x).Infinite := hne
    have h0 : G.kc t = 0 := by rw [← G.hcard t x hx, hinf.ncard]
    exact absurd h0 (Nat.pos_iff_ne_zero.mp (G.hkpos t))
  -- The `±1`-slice decision, from the compatibility of `B` with the `Yl`-family.
  have hsl : ∀ (t : Fin G.r) (σ : ℝ), (σ = 1 ∨ σ = -1) →
      (b ∩ projFirst n (m + 1) '' {z | z ∈ absSet (G.S t) ∧
          vertCoord (projSnd n (m + 1) z) = σ} = ∅) ∨
      (b ⊆ projFirst n (m + 1) '' {z | z ∈ absSet (G.S t) ∧
          vertCoord (projSnd n (m + 1) z) = σ}) := by
    intro t σ hσ
    obtain ⟨hyFmt, hyCand, hySig, hySloR, hyLy, hyS1, hyS2, hyY, hyPiece⟩ := P.specY
    have hstep : ∃ i : Fin P.Yl.length,
        projFirst n c.M2 '' (P.Yl.get i).set =
          projFirst n (m + 1) '' (E2.sliceSemiPf (G.S t) σ).set := by
      rcases hσ with rfl | rfl
      · exact hyS1 (G.S t) (G.hScand t)
      · exact hyS2 (G.S t) (G.hScand t)
    obtain ⟨i, hi⟩ := hstep
    obtain ⟨κ₀, hκ₀B, hκ₀b⟩ := Finset.mem_image.mp hb
    have h := hBYl i κ₀ hκ₀B
    rw [hκ₀b, hi, E2.sliceSemiPf_set] at h
    rcases h with hsub | hdis
    · exact Or.inr hsub
    · exact Or.inl (Set.disjoint_iff_inter_eq_empty.mp hdis)
  -- The level-pair family of two candidates and its `Σ`-coverage, from `specSig`.
  obtain ⟨-, -, -, hSigPair, hSigLev, -, -⟩ := P.specSig
  choose Wl hWl using fun (i j : Fin G.r) => hSigLev (G.S i) (G.hScand i) (G.S j) (G.hScand j)
  have hWgood : ∀ (i j : Fin G.r), ∀ W ∈ Wl i j, W.Good :=
    fun i j W hW => ((hWl i j).1 W hW).1
  have hWsub : ∀ (i j : Fin G.r), ∀ W ∈ Wl i j,
      W.X.set ⊆ (absLevelPairSet (G.S i) (G.S j)).set :=
    fun i j W hW => ((hWl i j).1 W hW).2
  have hWcov : ∀ (i j : Fin G.r),
      (absLevelPairSet (G.S i) (G.S j)).set = ⋃ W ∈ Wl i j, W.X.set :=
    fun i j => (hWl i j).2.1
  -- The `Σ`-avoidance of `b` (`GHyp`).
  have hdisjSig : ∀ Z ∈ P.Sig, Disjoint b (projFirst n (pPair n m) '' Z.set) := hG.1
  -- The pointwise pair avoidance, from the `Σ`-coverage of the pair-sub-base and the pair-frontier.
  have havoid : ∀ (i j : Fin G.r) (a : Fin (G.kc i)) (bb : Fin (G.kc j)) (x₀ : Fin n → ℝ),
      x₀ ∈ b → (G.sc i a x₀) (Fin.last m) = (G.sc j bb x₀) (Fin.last m) →
      (∀ W ∈ Wl i j, pPair n m - W.j < n + (m + 1) - (G.S i).j →
        pairPtUp (absPtUp (Fin.append x₀ (G.sc i a x₀)))
          (absPtUp (Fin.append x₀ (G.sc j bb x₀))) ∉ W.X.set) ∧
      (∀ W ∈ Wl i j, pPair n m - W.j = n + (m + 1) - (G.S i).j →
        pairPtUp (absPtUp (Fin.append x₀ (G.sc i a x₀)))
          (absPtUp (Fin.append x₀ (G.sc j bb x₀))) ∉ closure W.X.set \ W.X.set) := by
    intro i j a bb x₀ hx₀ _
    have hu : absPtUp (Fin.append x₀ (G.sc i a x₀)) ∈ (G.S i).X.set :=
      (Work.CoreStep.mem_absSet_iff (G.S i) _).mp (G.hsub i a x₀ hx₀)
    have hv : absPtUp (Fin.append x₀ (G.sc j bb x₀)) ∈ (G.S j).X.set :=
      (Work.CoreStep.mem_absSet_iff (G.S j) _).mp (G.hsub j bb x₀ hx₀)
    have hau := Work.WilE7.CoreStep.absPtInv_absPtUp (Fin.append x₀ (G.sc i a x₀))
    have hav := Work.WilE7.CoreStep.absPtInv_absPtUp (Fin.append x₀ (G.sc j bb x₀))
    have hpf : ∀ w : Fin (m + 1) → ℝ, projFirst n (m + 1) (Fin.append x₀ w) = x₀ := by
      intro w; funext i'; simp [WilkiesDesign.E.projFirst, Fin.append_left]
    have h := Work.WilE7.Endgame.havoid_of_sigma_cross (G.S i) (G.S j) P.Sig (Wl i j)
      (fun W hW => (hWl i j).2.2.1 W hW) (fun W hW => (hWl i j).2.2.2 W hW) b hdisjSig
    have hres := h _ _ x₀ hu hv (by rw [hau]; exact hpf _) (by rw [hav]; exact hpf _) hx₀
    refine ⟨fun W hW hlt => ?_, fun W hW heq => ?_⟩
    · intro hmem
      exact absurd (hres.1 W hW hmem) (not_le.mpr hlt)
    · exact fun hmem => hres.2 W hW hmem heq
  -- The level data of the sheet family.
  exact Work.WilE7.CoreStep.gcase_sheets (G.S) b (Work.WilE7.isPreconnected_of_isCell hcell)
    (fun t => G.hSgood t) (fun t => G.hSrank t) hfin G.kc G.hkpos G.sc G.hcont G.hinj
    G.hsub G.hcov hsl Wl hWgood hWsub hWcov havoid

end Work.WilE7.Endgame.E2B
