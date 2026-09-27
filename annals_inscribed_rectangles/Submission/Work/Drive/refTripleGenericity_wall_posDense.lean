import Mathlib
import Submission.Work.Drive.hn2RefParityDefs
import Submission.Work.Drive.hn2Clause6Sard

/-!
# The `PosBlocks`-dense form of the reference-triple genericity

`Work.Drive.exists_refTripleGenericity_wall_dep` (`Drive/hn2Clause6Sard.lean`) produces the reference
triple genericity at a parameter lying in a prescribed *open, ball-dense* condition set `A`.  The
class-parity producer of the `hn2` node (`Work.Drive.RefParityFamily`, `Drive/hn2RefParityDefs.lean`)
supplies a condition set carrying the class parity whose density is only claimed at points of the closed
unit ball with **positive blocks** (`PosBlocks`).  This module proves the wall statement in that weaker
form, which is what the class-parity producer can deliver.

The mathematics is unchanged: the enrichment `A ∩ HGen0 ∩ HGen1 ∩ MixedGP` is built by the three-block
argument, whose output point `s` always lies in a ball `ball (t • vBlk) (t/2)` on which **all** blocks
are positive; the weak density of `A` at `s` then supplies the wanted point of `A`.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ## 1. The three-block point with positive blocks -/

/-- The vector of `ℝ¹²` whose every block (`k = 0, 1, 2`) is the constant-one vector of `ℝ⁴`.
(A private copy of the vector of `Work.Drive.threeBlock_dense_point`.) -/
private def vBlk : EuclideanSpace ℝ (Fin 12) :=
  WithLp.toLp 2 (fun i : Fin 12 => if i.val % 4 = 0 then (1 : ℝ) else 0)

private lemma blk_vBlk_zero (k : Fin 3) : (blk k vBlk) 0 = 1 := by
  rw [blk_apply]
  show (if (blkIdx k 0).val % 4 = 0 then (1 : ℝ) else 0) = 1
  have h : (blkIdx k 0).val = 4 * k.val := rfl
  rw [h, Nat.mul_mod_right]
  norm_num

/-- Positivity of the `k`-th block on the ball `ball (t • vBlk) (t/2)` (`t > 0`). -/
private lemma blk_pos_of_mem_ball (k : Fin 3) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin 12)) (hx : ‖x - t • vBlk‖ < t / 2) : 0 < (blk k x) 0 := by
  have hsplit : x = t • vBlk + (x - t • vBlk) := by abel
  have hdecomp : (blk k x) 0 = (blk k (t • vBlk)) 0 + (blk k (x - t • vBlk)) 0 := by
    conv_lhs => rw [hsplit]
    rw [map_add]; rfl
  have hk : (blk k (t • vBlk)) 0 = t := by
    rw [map_smul]
    simp [blk_vBlk_zero k]
  have hbound : -(t / 2) < (blk k (x - t • vBlk)) 0 := by
    have h1 : |(blk k (x - t • vBlk)) 0| ≤ ‖x - t • vBlk‖ := by
      have h2 := PiLp.norm_apply_le (blk k (x - t • vBlk)) 0
      calc |(blk k (x - t • vBlk)) 0| = ‖(blk k (x - t • vBlk)).ofLp 0‖ := by
            rw [Real.norm_eq_abs]
        _ ≤ ‖blk k (x - t • vBlk)‖ := h2
        _ ≤ ‖x - t • vBlk‖ := norm_blk_le k _
    have h3 := neg_abs_le ((blk k (x - t • vBlk)) 0)
    linarith
  rw [hdecomp, hk]
  linarith

/-- Smallness of the norm on the ball `ball (t • vBlk) (t/2)` (`t > 0`). -/
private lemma norm_lt_of_mem_ball {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin 12))
    (hx : ‖x - t • vBlk‖ < t / 2) : ‖x‖ < t * (‖vBlk‖ + 1) := by
  have hsum : ‖x‖ ≤ ‖t • vBlk‖ + ‖x - t • vBlk‖ := by
    have heq : t • vBlk + (x - t • vBlk) = x := by abel
    calc ‖x‖ = ‖t • vBlk + (x - t • vBlk)‖ := by rw [heq]
      _ ≤ ‖t • vBlk‖ + ‖x - t • vBlk‖ := norm_add_le _ _
  have hsm : ‖t • vBlk‖ = t * ‖vBlk‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  rw [hsm] at hsum
  nlinarith [norm_nonneg vBlk]

/-- Three open sets, each dense in a common open ball, meet in that ball. -/
private lemma dense_at_of_three
    (A : Fin 3 → Set (EuclideanSpace ℝ (Fin 12)))
    {B : Set (EuclideanSpace ℝ (Fin 12))} (hB : IsOpen B) (hBne : B.Nonempty)
    (hopen : ∀ k : Fin 3, IsOpen (A k))
    (h : ∀ x ∈ B, ∀ k : Fin 3, ∀ δ : ℝ, 0 < δ → ∃ y, y ∈ A k ∧ ‖y - x‖ < δ) :
    ∃ s ∈ B, ∀ k : Fin 3, s ∈ A k := by
  obtain ⟨x, hx⟩ := hBne
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.mp hB x hx
  obtain ⟨y0, hy0A, hy0d⟩ := h x hx 0 ε hε
  have hy0B : y0 ∈ B := hεB (by rw [Metric.mem_ball, dist_eq_norm]; exact hy0d)
  obtain ⟨ε0, hε0, hε0sub⟩ := Metric.isOpen_iff.mp ((hopen 0).inter Metric.isOpen_ball) y0
    ⟨hy0A, by rw [Metric.mem_ball, dist_eq_norm]; exact hy0d⟩
  obtain ⟨y1, hy1A, hy1d⟩ := h y0 hy0B 1 ε0 hε0
  have hy1mem : y1 ∈ A 0 ∩ Metric.ball x ε :=
    hε0sub (by rw [Metric.mem_ball, dist_eq_norm]; exact hy1d)
  have hy1B : y1 ∈ B := hεB hy1mem.2
  obtain ⟨ε1, hε1, hε1sub⟩ := Metric.isOpen_iff.mp ((hopen 1).inter Metric.isOpen_ball) y1
    ⟨hy1A, by rw [Metric.mem_ball, dist_eq_norm]; exact hy1d⟩
  obtain ⟨y2, hy2A, hy2d⟩ := h y1 hy1B 2 ε1 hε1
  have hy2mem : y2 ∈ A 1 ∩ Metric.ball y0 ε0 :=
    hε1sub (by rw [Metric.mem_ball, dist_eq_norm]; exact hy2d)
  have hy2A0 : y2 ∈ A 0 := (hε0sub hy2mem.2).1
  have hy2B : y2 ∈ B := hεB (hε0sub hy2mem.2).2
  refine ⟨y2, hy2B, fun k => ?_⟩
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk with h | h | h
  · rw [h]; exact hy2A0
  · rw [h]; exact hy2mem.1
  · rw [h]; exact hy2A

/-- **`Work.Drive.threeBlock_dense_point` with the positivity of the blocks of the output.**  The
three-block argument produces its point `s` inside the ball `ball (t • vBlk) (t/2)`; hence
`PosBlocks s` (and `‖s‖ ≤ 1`) hold as well. -/
theorem threeBlock_dense_point_posBlocks
    (A : Fin 3 → Set (EuclideanSpace ℝ (Fin 12)))
    (hopen : ∀ k : Fin 3, IsOpen (A k))
    (hdense : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 12)), ‖x‖ ≤ 1 → 0 ≤ (blk k x) 0 →
      ∀ δ : ℝ, 0 < δ → ∃ y, y ∈ A k ∧ ‖y - x‖ < δ)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ s : EuclideanSpace ℝ (Fin 12), ‖s‖ < ρ ∧ PosBlocks s ∧ ‖s‖ ≤ 1 ∧ ∀ k : Fin 3, s ∈ A k := by
  obtain ⟨t, htpos, ht⟩ : ∃ t : ℝ, 0 < t ∧ t * (‖vBlk‖ + 1) < min 1 ρ := by
    refine ⟨min 1 ρ / (2 * (‖vBlk‖ + 1)), ?_, ?_⟩
    · have : (0 : ℝ) < min 1 ρ := lt_min one_pos hρ
      positivity
    · have hmul : min 1 ρ / (2 * (‖vBlk‖ + 1)) * (‖vBlk‖ + 1) = min 1 ρ / 2 := by
        field_simp
      rw [hmul]
      have : (0 : ℝ) < min 1 ρ := lt_min one_pos hρ
      linarith
  have hr : 0 < t / 2 := by linarith
  have hball : ∀ x ∈ Metric.ball (t • vBlk) (t / 2), ‖x‖ < min 1 ρ := by
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    have h1 := norm_lt_of_mem_ball htpos x hx
    linarith
  have hdens : ∀ x ∈ Metric.ball (t • vBlk) (t / 2), ∀ k : Fin 3, ∀ δ : ℝ, 0 < δ →
      ∃ y, y ∈ A k ∧ ‖y - x‖ < δ := by
    intro x hx k δ hδ
    have hxd : ‖x - t • vBlk‖ < t / 2 := by
      rw [Metric.mem_ball, dist_eq_norm] at hx
      exact hx
    refine hdense k x ?_ ?_ δ hδ
    · exact le_of_lt (lt_of_lt_of_le (hball x hx) (min_le_left 1 ρ))
    · exact le_of_lt (blk_pos_of_mem_ball k htpos x hxd)
  obtain ⟨s, hsB, hsA⟩ := dense_at_of_three A Metric.isOpen_ball
    ⟨t • vBlk, by rw [Metric.mem_ball, dist_self]; exact hr⟩ hopen hdens
  have hsd : ‖s - t • vBlk‖ < t / 2 := by
    rw [Metric.mem_ball, dist_eq_norm] at hsB
    exact hsB
  exact ⟨s, lt_of_lt_of_le (hball s hsB) (min_le_right 1 ρ),
    fun k => blk_pos_of_mem_ball k htpos s hsd,
    le_of_lt (lt_of_lt_of_le (hball s hsB) (min_le_left 1 ρ)), hsA⟩

/-! ## 2. The `PosBlocks`-dense fourfold intersection -/

/-- **The intersection of an open `A` (dense at the positive-block points of the closed unit ball)
with three open sets, each dense in its own block half-space, accumulates at `0`.**

The three-block argument gives a point `s` of norm `< ρ` lying in all three of `A0`, `A1`, `A2` whose
blocks are all positive; the weak density of `A` at `s` then gives a point `t ∈ A` in the open
neighbourhood `A0 ∩ A1 ∩ A2` of `s`, with `‖t‖ < ρ`. -/
theorem exists_inter_of_posBlocks_dense {A A0 A1 A2 : Set (EuclideanSpace ℝ (Fin 12))}
    (hAopen : IsOpen A) (h0 : IsOpen A0) (h1 : IsOpen A1) (h2 : IsOpen A2)
    (hAdense : ∀ s : EuclideanSpace ℝ (Fin 12), ‖s‖ ≤ 1 → PosBlocks s →
      ∀ δ : ℝ, 0 < δ → ∃ t ∈ A, ‖t - s‖ < δ)
    (hd0 : ∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → 0 ≤ (blk 0 x) 0 →
      ∀ δ : ℝ, 0 < δ → ∃ y, y ∈ A0 ∧ ‖y - x‖ < δ)
    (hd1 : ∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → 0 ≤ (blk 1 x) 0 →
      ∀ δ : ℝ, 0 < δ → ∃ y, y ∈ A1 ∧ ‖y - x‖ < δ)
    (hd2 : ∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → 0 ≤ (blk 2 x) 0 →
      ∀ δ : ℝ, 0 < δ → ∃ y, y ∈ A2 ∧ ‖y - x‖ < δ)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ s : EuclideanSpace ℝ (Fin 12), ‖s‖ < ρ ∧ s ∈ A ∧ s ∈ A0 ∧ s ∈ A1 ∧ s ∈ A2 := by
  let A3 : Fin 3 → Set (EuclideanSpace ℝ (Fin 12)) := ![A0, A1, A2]
  have hA3open : ∀ k : Fin 3, IsOpen (A3 k) := by
    intro k
    fin_cases k <;> simp only [A3]
    · exact h0
    · exact h1
    · exact h2
  have hA3dense : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 12)), ‖x‖ ≤ 1 →
      0 ≤ (blk k x) 0 → ∀ δ : ℝ, 0 < δ → ∃ y, y ∈ A3 k ∧ ‖y - x‖ < δ := by
    intro k x hx hxk δ hδ
    fin_cases k <;> simp only [A3]
    · exact hd0 x hx (by simpa using hxk) δ hδ
    · exact hd1 x hx (by simpa using hxk) δ hδ
    · exact hd2 x hx (by simpa using hxk) δ hδ
  obtain ⟨s, hsρ, hsPos, hs1, hsA3⟩ :=
    threeBlock_dense_point_posBlocks A3 hA3open hA3dense (min ρ 1) (lt_min hρ one_pos)
  have hs0 : s ∈ A0 := hsA3 0
  have hs1' : s ∈ A1 := hsA3 1
  have hs2 : s ∈ A2 := hsA3 2
  have hsρ' : ‖s‖ < ρ := lt_of_lt_of_le hsρ (min_le_left _ _)
  -- an open neighbourhood of `s` contained in `A0 ∩ A1 ∩ A2`
  have hopen3 : IsOpen (A0 ∩ A1 ∩ A2) := (h0.inter h1).inter h2
  have hmem3 : s ∈ A0 ∩ A1 ∩ A2 := ⟨⟨hs0, hs1'⟩, hs2⟩
  obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp (hopen3.mem_nhds hmem3)
  -- the weak density of `A` at `s`
  have hδ : 0 < min (r / 2) ((ρ - ‖s‖) / 2) := lt_min (by linarith) (by linarith)
  obtain ⟨t, htA, ht⟩ := hAdense s hs1 hsPos (min (r / 2) ((ρ - ‖s‖) / 2)) hδ
  have htρ : ‖t‖ < ρ := by
    have h1 : ‖t - s‖ < (ρ - ‖s‖) / 2 := lt_of_lt_of_le ht (min_le_right _ _)
    have h2 : ‖t‖ ≤ ‖t - s‖ + ‖s‖ := by
      have heq : t - s + s = t := by abel
      calc ‖t‖ = ‖t - s + s‖ := by rw [heq]
        _ ≤ ‖t - s‖ + ‖s‖ := norm_add_le _ _
    linarith
  have ht3 : t ∈ A0 ∩ A1 ∩ A2 := by
    refine hrsub ?_
    rw [Metric.mem_ball, dist_eq_norm]
    have h2 : ‖t - s‖ < r := lt_of_lt_of_le ht (le_trans (min_le_left _ _) (by linarith))
    exact h2
  exact ⟨t, htρ, htA, ht3.1.1, ht3.1.2, ht3.2⟩



/-! ## 3. The producer chain in the `PosBlocks`-dense form -/

theorem exists_sweepGenericity_clause6_of_posDense {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (c : ℝ) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (u v : UnitAddCircle) (lam : ℝ) (hlam : 0 < lam) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3)
    (habove : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) < lam)
    (hopen1 : IsOpen (HGen1Set Q (linPlaneChart (φ 2) lam hlam) u v ![c / 2, c / 3, c / 4]))
    (hdense1 : ∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → 0 ≤ (blk 1 x) 0 →
      ∀ ε : ℝ, 0 < ε →
        ∃ t : EuclideanSpace ℝ (Fin 12), ‖t - x‖ < ε ∧
          t ∈ HGen1Set Q (linPlaneChart (φ 2) lam hlam) u v ![c / 2, c / 3, c / 4])
    (A : Set (EuclideanSpace ℝ (Fin 12))) (hAopen : IsOpen A)
    (hAdense : ∀ s : EuclideanSpace ℝ (Fin 12), ‖s‖ ≤ 1 → PosBlocks s →
      ∀ δ : ℝ, 0 < δ → ∃ t ∈ A, ‖t - s‖ < δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε ∧ t ∈ A ∧
      (∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
        (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 0
          < levelOf (chartPert (blk k t)
              (refTriple Q (refPlanePres φ lam hlam) u v k y))) ∧
      Meet3Hyp CappingSpace
        (sweepChartFam (refTriple Q (refPlanePres φ lam hlam) u v)
          (fun s p => chartPert s p) (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) t) ∧
      GoodAt (fun s p => chartPert s p) Q ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 1) (v - u)
        (blk 0 t, blk 1 t) ∧
      GoodAt (fun s p => chartPert s p) Q ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 0) (u - v)
        (blk 1 t, blk 0 t) ∧
      HGen0Set Q (linPlaneChart (φ 2) lam hlam) u v (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) t ∧
      HGen1Set Q (linPlaneChart (φ 2) lam hlam) u v (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) t ∧
      MixedGPSet Q (linPlaneChart (φ 2) lam hlam) u v
        ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2) t := by
  classical
  obtain ⟨εl, hεl, hlvl⟩ := exists_levelBound_at_one hQ c hc hcbot u v lam hlam φ habove
  -- ## the data of the reference plane chart
  have hQRsm : IsSmoothChart (linPlaneChart (φ 2) lam hlam) := linPlaneChart_contMDiff (φ 2) lam hlam
  have hQRseam : ∀ z : ℂ, ‖z‖ = 1 → linPlaneChart (φ 2) lam hlam (-z)
      = linPlaneChart (φ 2) lam hlam z := fun z hz => linPlaneChart_neg (φ 2) lam hlam hz
  have hQc : IsChartData Q := IsChartData_of_isPlaneChart hQ
  have hQsm : IsSmoothChart Q := IsSmoothChart_of_isPlaneChart hQ
  have hcpos : ∀ k : Fin 3, 0 < (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k := dblk_pos hc
  have hcdist : ∀ k k' : Fin 3, (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k
      = (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k' → k = k' := dblk_distinct hc
  have hlevc : ∀ z : ℂ, ‖z‖ ≤ 1 →
      (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2 < levelOf (Q z) := by
    intro z hz
    have h := hcbot (Q z) ⟨z, by rwa [Metric.mem_closedBall, dist_zero_right], rfl⟩
    have h2 : (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2 = c / 4 := rfl
    rw [h2]; linarith
  have hlevR : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (linPlaneChart (φ 2) lam hlam z)
      > (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2 := by
    intro z hz
    have hL : levelOf (linPlaneChart (φ 2) lam hlam z) = lam :=
      level_linPlaneChart (φ 2) lam hlam z
    have hcl : c < lam := c_lt_lam hcbot habove
    have h2 : (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2 = c / 4 := rfl
    rw [hL, h2]; linarith
  -- ## the three sets are open
  have h0open : IsOpen (HGen0Set Q (linPlaneChart (φ 2) lam hlam) u v
      (![c / 2, c / 3, c / 4] : Fin 3 → ℝ)) :=
    isOpen_HGen0Set hQc hQRsm hQRseam u v _ hcpos
  have hgpopen : IsOpen (MixedGPSet Q (linPlaneChart (φ 2) lam hlam) u v
      ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2)) :=
    isOpen_MixedGPSet hQsm hQRsm u v _
  -- ## the enriched set, open and accumulating at `0`
  set A' : Set (EuclideanSpace ℝ (Fin 12)) :=
    A ∩ HGen0Set Q (linPlaneChart (φ 2) lam hlam) u v (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) ∩
      HGen1Set Q (linPlaneChart (φ 2) lam hlam) u v (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) ∩
      MixedGPSet Q (linPlaneChart (φ 2) lam hlam) u v
        ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2) with hA'
  have hA'open : IsOpen A' := ((hAopen.inter h0open).inter hopen1).inter hgpopen
  have hA'0 : ∀ δ : ℝ, 0 < δ → ∃ t ∈ A', ‖t‖ < δ := by
    intro δ hδ
    obtain ⟨s, hsρ, hsA, hs0, hs1, hs2⟩ := exists_inter_of_posBlocks_dense hAopen h0open hopen1
      hgpopen hAdense
      (fun x hx hx0 δ' hδ' => by
        obtain ⟨y, hy, hymem⟩ :=
          dense_HGen0Set hQc hQRsm hQRseam u v _ hcpos hlevc hlevR x hx hx0 δ' hδ'
        exact ⟨y, hymem, hy⟩)
      (fun x hx hx0 δ' hδ' => by
        obtain ⟨y, hy, hymem⟩ := hdense1 x hx hx0 δ' hδ'
        exact ⟨y, hymem, hy⟩)
      (fun x hx hx0 δ' hδ' => by
        obtain ⟨y, hy, hymem⟩ := dense_MixedGPSet hQsm hQRsm u v _ x δ' hδ'
        exact ⟨y, hymem, hy⟩)
      δ hδ
    exact ⟨s, ⟨⟨⟨hsA, hs0⟩, hs1⟩, hs2⟩, hsρ⟩
  -- ## the enriched Sard
  obtain ⟨t, ht, htA', hM, hg01, hg10⟩ :=
    exists_meet3Hyp_opens_near_zero (Q := Q) hQc (fun s p => chartPert s p)
      (isChartPert_chartPert Q) (![c / 2, c / 3, c / 4]) hcpos hcdist u v
      (refPlanePres φ lam hlam) (refPlanePres_contMDiff φ lam hlam)
      (refPlanePres_seam φ lam hlam)
      (richness_sweepChartFam (Q := Q) (refTriple Q (refPlanePres φ lam hlam) u v)
        (fun s p => chartPert s p) (![c / 2, c / 3, c / 4]) (isChartPert_chartPert Q) hcpos hcdist
        (refTriple_contMDiff Q hQsm φ lam hlam u v))
      A' hA'open hA'0 (min ε εl) (lt_min hε hεl)
  refine ⟨t, lt_of_lt_of_le ht (min_le_left _ _), htA'.1.1.1,
    hlvl t (lt_of_lt_of_le ht (min_le_right _ _)), hM, hg01, hg10,
    htA'.1.1.2, htA'.1.2, htA'.2⟩



theorem exists_refTripleGenericity_posDense {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ)
    (c : ℝ) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Zc γ →
      Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q))
    (u v : UnitAddCircle) (huv : v - u ∈ Zc γ)
    {β : ℝ} (hβpos : 0 < β) (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam) (hβlam : β < lam)
    (habove : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) < lam)
    {δF : ℝ} (hδF : 0 < δF)
    (hF1 : ∀ τ₀ τ₁ τ₂ : Eucl 3, ‖τ₀‖ < δF → ‖τ₁‖ < δF → ‖τ₂‖ < δF →
        GoodPair (fun z : ℂ => chartPert τ₀ (rotCapping u (Q z)))
            (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z))
            ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2) →
        GoodPair (fun z : ℂ => chartPert τ₁ (rotCapping v (Q z)))
            (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z))
            ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2) →
        Odd (coreSideCount (fun z : ℂ => chartPert τ₀ (rotCapping u (Q z)))
            ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2)
            (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z)))) ∧
        Odd (coreSideCount (fun z : ℂ => chartPert τ₁ (rotCapping v (Q z)))
            ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2)
            (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z)))))
    (hopen1 : IsOpen (HGen1Set Q (linPlaneChart (φ 2) lam hlam) u v ![c / 2, c / 3, c / 4]))
    (hdense1 : ∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → 0 ≤ (blk 1 x) 0 →
      ∀ ε : ℝ, 0 < ε →
        ∃ t : EuclideanSpace ℝ (Fin 12), ‖t - x‖ < ε ∧
          t ∈ HGen1Set Q (linPlaneChart (φ 2) lam hlam) u v ![c / 2, c / 3, c / 4])
    (A : Set (EuclideanSpace ℝ (Fin 12))) (hAopen : IsOpen A)
    (hAdense : ∀ s : EuclideanSpace ℝ (Fin 12), ‖s‖ ≤ 1 → PosBlocks s →
      ∀ δ : ℝ, 0 < δ → ∃ t ∈ A, ‖t - s‖ < δ) :
    ∀ ε : ℝ, 0 < ε → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε ∧ t ∈ A ∧
      RefTripleGenericity Q (refPlanePres φ lam hlam) u v
        (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) t := by
  classical
  intro ε hε
  have hcblkpos : ∀ k : Fin 3, 0 < (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k := dblk_pos hc
  have hcblk2 : (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2 = c / 4 := rfl
  have hcbot' : ∀ z : ℂ, ‖z‖ ≤ 1 → c < levelOf (Q z) := fun z hz =>
    hcbot (Q z) ⟨z, by rwa [Metric.mem_closedBall, dist_zero_right], rfl⟩
  -- ## the small-`t` data of the two configuration blocks
  obtain ⟨r₁, hr₁, h₁⟩ := transport_disins_reference_block0 (hγne := hγne) (Q := Q)
    hQ.1.continuous hβpos hβ
    φ lam hlam hβlam hdisjZc huv c hc hcbot' hcblk2
  obtain ⟨r₂, hr₂, h₂⟩ := transport_disins_reference_block' (hγne := hγne) (Q := Q)
    hQ.1.continuous hβpos hβ
    φ lam hlam hβlam hdisjZc huv c hc hcbot' hcblk2
  -- ## the budget
  set εs : ℝ := min ε (min r₁ (min r₂ (min (Real.log 2) (min δF (Real.log (lam / β) / 4)))))
    with hεs
  have hlogpos : 0 < Real.log (lam / β) := by
    have h1 : 1 < lam / β := (one_lt_div hβpos).mpr hβlam
    exact Real.log_pos h1
  have hεs' : 0 < εs := by
    rw [hεs]
    exact lt_min hε (lt_min hr₁ (lt_min hr₂ (lt_min (Real.log_pos (by norm_num))
      (lt_min hδF (by linarith)))))
  obtain ⟨t, ht, htA, hlev, hM, hg01, hg10, hgen0, hgen1, hgp0, hgp1⟩ :=
    exists_sweepGenericity_clause6_of_posDense hQ c hc hcbot u v lam hlam φ habove hopen1 hdense1
      A hAopen hAdense εs hεs'
  have htε : ‖t‖ < ε := lt_of_lt_of_le ht (by rw [hεs]; exact min_le_left _ _)
  have htr₁ : ‖t‖ < r₁ :=
    lt_of_lt_of_le ht (by rw [hεs]; exact le_trans (min_le_right _ _) (min_le_left _ _))
  have htr₂ : ‖t‖ < r₂ :=
    lt_of_lt_of_le ht (by
      rw [hεs]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have htlog2 : ‖t‖ < Real.log 2 :=
    lt_of_lt_of_le ht (by
      rw [hεs]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _))))
  have htlog3 : ‖t‖ < Real.log 3 :=
    lt_trans htlog2 (Real.log_lt_log (by norm_num) (by norm_num))
  have htδF : ‖t‖ < δF :=
    lt_of_lt_of_le ht (by
      rw [hεs]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))))
  have htloglam : 2 * ‖t‖ < Real.log (lam / β) := by
    have h : ‖t‖ < Real.log (lam / β) / 4 :=
      lt_of_lt_of_le ht (by
        rw [hεs]
        exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))))
    linarith
  -- ## the data at `t`
  obtain ⟨hdisj01, hdisj02, hdisj012', _⟩ := h₁ t htr₁
  obtain ⟨hdisj10, hdisj12, hdisj102', _⟩ := h₂ t htr₂
  have hdisj012 : ∀ y y' : EuclideanSpace ℝ (Fin 2),
      refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 1 y
        ≠ refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2 y' := by
    intro y y' h
    exact (Set.disjoint_left.mp hdisj012' ⟨y, rfl⟩) ⟨y', h.symm⟩
  have hdisj102 : ∀ y y' : EuclideanSpace ℝ (Fin 2),
      refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 0 y
        ≠ refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2 y' := by
    intro y y' h
    exact (Set.disjoint_left.mp hdisj102' ⟨y, rfl⟩) ⟨y', h.symm⟩
  have hlev01 : ∀ z : ℂ, ‖z‖ ≤ 1 →
      (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 1
        < levelOf (chartPert (blk 0 t) (rotCapping u (Q z))) :=
    fun z hz => (levelOf_chartPert_rotCapping_gt_cblk c hc hcbot' u rfl rfl htlog3 0 z hz).1
  have hlev02 : ∀ z : ℂ, ‖z‖ ≤ 1 →
      (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2
        < levelOf (chartPert (blk 0 t) (rotCapping u (Q z))) :=
    fun z hz => (levelOf_chartPert_rotCapping_gt_cblk c hc hcbot' u rfl rfl htlog3 0 z hz).2
  have hlev10 : ∀ z : ℂ, ‖z‖ ≤ 1 →
      (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 0
        < levelOf (chartPert (blk 1 t) (rotCapping v (Q z))) :=
    fun z hz => levelOf_chartPert_rotCapping_gt_cblk0 c hc hcbot' v rfl htlog2 1 z hz
  have hlev12 : ∀ z : ℂ, ‖z‖ ≤ 1 →
      (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2
        < levelOf (chartPert (blk 1 t) (rotCapping v (Q z))) :=
    fun z hz => (levelOf_chartPert_rotCapping_gt_cblk c hc hcbot' v rfl rfl htlog3 1 z hz).2
  have hsmall0 : ‖blk 0 t‖ < δF := lt_of_le_of_lt (norm_blk_le 0 t) htδF
  have hsmall1 : ‖blk 1 t‖ < δF := lt_of_le_of_lt (norm_blk_le 1 t) htδF
  have hsmall2 : ‖blk 2 t‖ < δF := lt_of_le_of_lt (norm_blk_le 2 t) htδF
  -- ## the transport at the two blocks
  obtain ⟨hT6₀, hT6₁, hid01, hid10, hmix0, hmix1⟩ :=
    refTripleAt_blockT6At_of_data hQ hγ u v φ lam hlam (![c / 2, c / 3, c / 4]) hcblkpos t
      hM hgen0 hgen1 hdisj01 hdisj02 hdisj012 hlev01 hlev02 hdisj10 hdisj12 hdisj102 hlev10 hlev12
      hδF hF1 hsmall0 hsmall1 hsmall2 hgp0 hgp1
  have hlow : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k
        ≤ levelOf (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t k y) := by
    intro k y
    refine le_trans ?_ (le_of_lt (hlev k y))
    fin_cases k
    · exact le_rfl
    · show c / 3 ≤ c / 2
      linarith
    · show c / 4 ≤ c / 2
      linarith
  have hT2 : topBdryMeet CappingSpace
      (sweepChartFam (refTriple Q (refPlanePres φ lam hlam) u v)
        (fun s p => chartPert s p) (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) t) 2 = ∅ :=
    refTriple_topBdryMeet_two_eq_empty hβpos hβ (φ := φ) (lam := lam) hlam hβlam u v
      (cblk := ![c / 2, c / 3, c / 4]) hcblkpos htloglam hlow
  -- ## the block factors
  obtain ⟨g, hg01', hg10', hblock, h20, h21, h02', h12'⟩ :=
    exists_blockFactors_of_T6 (Ξ := fun s p => chartPert s p) (Q := Q)
      (refPlanePres φ lam hlam) u v (![c / 2, c / 3, c / 4]) t
      (fun z : ℂ => chartPert (blk 0 t) (rotCapping u (Q z)))
      (fun z : ℂ => chartPert (blk 1 t) (rotCapping v (Q z)))
      hT6₀ hT6₁ hT2 hid01 hid10 hmix0 hmix1
  exact ⟨t, htε, htA, hlev, hM, hg01, hg10, g, hg01', hg10', hblock, h20, h21, h02', h12'⟩



theorem exists_refTripleGenericity_noAux_posDense {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ)
    (c : ℝ) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Zc γ →
      Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q))
    (u v : UnitAddCircle) (huv : v - u ∈ Zc γ)
    {β : ℝ} (hβpos : 0 < β) (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam) (hβlam : β < lam)
    (habove : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) < lam)
    {δF : ℝ} (hδF : 0 < δF)
    (hF1 : ∀ τ₀ τ₁ τ₂ : Eucl 3, ‖τ₀‖ < δF → ‖τ₁‖ < δF → ‖τ₂‖ < δF →
        GoodPair (fun z : ℂ => chartPert τ₀ (rotCapping u (Q z)))
            (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z))
            ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2) →
        GoodPair (fun z : ℂ => chartPert τ₁ (rotCapping v (Q z)))
            (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z))
            ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2) →
        Odd (coreSideCount (fun z : ℂ => chartPert τ₀ (rotCapping u (Q z)))
            ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2)
            (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z)))) ∧
        Odd (coreSideCount (fun z : ℂ => chartPert τ₁ (rotCapping v (Q z)))
            ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2)
            (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z)))))
    (A : Set (EuclideanSpace ℝ (Fin 12))) (hAopen : IsOpen A)
    (hAdense : ∀ s : EuclideanSpace ℝ (Fin 12), ‖s‖ ≤ 1 → PosBlocks s →
      ∀ δ : ℝ, 0 < δ → ∃ t ∈ A, ‖t - s‖ < δ) :
    ∀ ε : ℝ, 0 < ε → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε ∧ t ∈ A ∧
      RefTripleGenericity Q (refPlanePres φ lam hlam) u v
        (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) t := by
  have hcblkpos : ∀ k : Fin 3, 0 < (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k := dblk_pos hc
  have hlevc : ∀ z : ℂ, ‖z‖ ≤ 1 →
      (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2 < levelOf (Q z) := by
    intro z hz
    have h := hcbot (Q z) ⟨z, by rwa [Metric.mem_closedBall, dist_zero_right], rfl⟩
    have h2 : (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2 = c / 4 := rfl
    rw [h2]; linarith
  have hlevR : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (linPlaneChart (φ 2) lam hlam z)
      > (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2 := by
    intro z hz
    have hL : levelOf (linPlaneChart (φ 2) lam hlam z) = lam :=
      level_linPlaneChart (φ 2) lam hlam z
    have hcl : c < lam := c_lt_lam hcbot habove
    have h2 : (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2 = c / 4 := rfl
    rw [hL, h2]; linarith
  obtain ⟨hopen1, hdense1⟩ := t6GenAtDBox_refTriple_block1_bundles (Q := Q)
    (IsChartData_of_isPlaneChart hQ) (linPlaneChart_contMDiff (φ 2) lam hlam)
    (fun z hz => linPlaneChart_neg (φ 2) lam hlam hz) u v (![c / 2, c / 3, c / 4]) hcblkpos
    hlevc hlevR
  exact exists_refTripleGenericity_posDense hQ hγ c hc hcbot hdisjZc u v huv hβpos hβ φ lam hlam hβlam
    habove hδF hF1 hopen1 hdense1 A hAopen hAdense



theorem refTripleGenericity_wall_posDense {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (c : ℝ) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Zc γ →
      Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q))
    (u v : UnitAddCircle) (huv : v - u ∈ Zc γ)
    (A : (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) → (lam : ℝ) → 0 < lam →
      Set (EuclideanSpace ℝ (Fin 12)))
    (hAopen : ∀ (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam),
      IsOpen (A φ lam hlam))
    (hAdense : ∀ (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
      (s : EuclideanSpace ℝ (Fin 12)), ‖s‖ ≤ 1 → PosBlocks s →
      ∀ δ : ℝ, 0 < δ → ∃ t ∈ A φ lam hlam, ‖t - s‖ < δ) :
    ∃ (β lam : ℝ) (hβpos : 0 < β) (hlam : 0 < lam) (hβlam : β < lam)
      (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3),
      (∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) < lam) ∧
      ∀ ε : ℝ, 0 < ε → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε ∧ t ∈ A φ lam hlam ∧
        RefTripleGenericity Q (refPlanePres φ lam hlam) u v
          (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) t := by
  obtain ⟨β, lam, hβpos, hlam, hβlam, φ₀, hβ, habove, hrank, hgen⟩ := exists_refPlane_charts hQ
  have hcbot' : ∀ z : ℂ, ‖z‖ ≤ 1 → c < levelOf (Q z) := fun z hz =>
    hcbot (Q z) ⟨z, by rwa [Metric.mem_closedBall, dist_zero_right], rfl⟩
  have hclow : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z) := fun z hz => (hcbot' z hz).le
  have hclam : c < lam := c_lt_lam hcbot habove
  obtain ⟨φ₂, δF₀, hδF₀, hF1'⟩ := refTriple_mixedFactors (hγ := hγ) (hγne := hγne) (Q := Q)
    hQ u v (c := c) (β := β) (lam := lam) (c₂ := c / 4) hc hβpos hlam
    (show (0 : ℝ) < c / 4 by linarith) (show c / 4 < c by linarith) hβlam
    (show c / 4 < lam / 2 by linarith) hclow hβ
  obtain ⟨φ, hφ2, hrank', hgen'⟩ := exists_triple_chart_of_middle φ₂ lam hlam
  have hδF : 0 < min δF₀ (Real.log 2) := lt_min hδF₀ (Real.log_pos (by norm_num))
  have hF1 : ∀ τ₀ τ₁ τ₂ : Eucl 3, ‖τ₀‖ < min δF₀ (Real.log 2) → ‖τ₁‖ < min δF₀ (Real.log 2) →
      ‖τ₂‖ < min δF₀ (Real.log 2) →
      GoodPair (fun z : ℂ => chartPert τ₀ (rotCapping u (Q z)))
          (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z))
          ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2) →
      GoodPair (fun z : ℂ => chartPert τ₁ (rotCapping v (Q z)))
          (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z))
          ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2) →
      Odd (coreSideCount (fun z : ℂ => chartPert τ₀ (rotCapping u (Q z)))
          ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2)
          (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z)))) ∧
      Odd (coreSideCount (fun z : ℂ => chartPert τ₁ (rotCapping v (Q z)))
          ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2)
          (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z)))) := by
    intro τ₀ τ₁ τ₂ h0 h1 h2 hgp0 hgp1
    rw [hφ2] at hgp0 hgp1 ⊢
    exact hF1' τ₀ τ₁ τ₂ (lt_of_lt_of_le h0 (min_le_left _ _)) (lt_of_lt_of_le h1 (min_le_left _ _))
      (lt_of_lt_of_le h2 (min_le_left _ _)) (lt_of_lt_of_le h2 (min_le_right _ _)) hgp0 hgp1
  exact ⟨β, lam, hβpos, hlam, hβlam, φ, habove,
    exists_refTripleGenericity_noAux_posDense hQ hγ c hc hcbot hdisjZc u v huv hβpos hβ φ lam hlam hβlam
      habove hδF hF1 (A φ lam hlam) (hAopen φ lam hlam) (hAdense φ lam hlam)⟩
end

end Work.Drive
