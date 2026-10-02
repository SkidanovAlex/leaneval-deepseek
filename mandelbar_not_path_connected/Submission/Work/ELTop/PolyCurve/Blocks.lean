/-
# The blocks of the polygon parametrization

This module develops the two facts about the blocks `cycBlock D R k` of the polygon
parametrization which are needed to see that `cycParam` is injective on `[0,1)`:

* two blocks with different indices `k ≠ k'` in the range `1 - m ≤ k ≤ 0` are disjoint
  (`cycBlock_injOn` with `k ≠ k'`);
* at the level of the pair (external angle, potential level) the parametrization of a single
  block is injective (`blkAng_blkLev_eq`).

The proof is a congruence argument in the "window" `[B 0 - 1, A 0]` of length `< 1`: all the
angles occurring on the polygon, and all the angles of the equipotential arcs, lie in this
window, and two angles in the window which are congruent modulo `1` are equal.
-/
import Mathlib
import Submission.Work.ELTop.rayPt_add_int
import Submission.Work.ELTop.PolyCurve.Defs
import Submission.Work.ELTop.rayPiece_eq_image
import Submission.Work.Top.continuousOn_rayPt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELTop

variable {c : ℂ} {φ : ℂ → ℂ}

/-! ## Generalities on the ray points -/

/-- Two ray points of the dynamical plane are equal if and only if their levels are equal and
their angles are congruent modulo `1`. -/
theorem rayPt_eq_iff (hN : Work.EL.DynB c φ) {θ θ' t t' : ℝ} (ht : 1 < t) (ht' : 1 < t') :
    (Work.EL.rayPt hN θ t = Work.EL.rayPt hN θ' t') ↔ t = t' ∧ ∃ k : ℤ, θ' = θ + k := by
  have hlog : ∀ {t t' : ℝ}, 1 < t → 1 < t' → Real.log t = Real.log t' → t = t' := by
    intro t t' ht ht' h
    have h' := congrArg Real.exp h
    rwa [Real.exp_log (by linarith), Real.exp_log (by linarith)] at h'
  constructor
  · intro h
    have h1 : Work.EL.pot hN (Work.EL.rayPt hN θ t) = Real.log t := Work.EL.pot_rayPt hN ht
    have h2 : Work.EL.pot hN (Work.EL.rayPt hN θ' t') = Real.log t' := Work.EL.pot_rayPt hN ht'
    rw [h] at h1
    have htt' : t = t' := hlog ht ht' (by linarith [h1, h2])
    refine ⟨htt', ?_⟩
    subst htt'
    exact Work.ELTop.rayPt_inj hN ht h
  · rintro ⟨rfl, ⟨k, rfl⟩⟩
    exact (Work.ELTop.rayPt_add_int hN θ t k).symm

/-- A ray of angle `θ` lands at `y` iff its angle shifted by an integer does. -/
theorem LandsN_add_int (hN : Work.EL.DynB c φ) {θ : ℝ} {y : ℂ} (h : Work.EL.LandsN hN θ y)
    (k : ℤ) : Work.EL.LandsN hN (θ + k) y := by
  have hfun : (fun t : ℝ => Work.EL.rayPt hN (θ + k) t) = fun t : ℝ => Work.EL.rayPt hN θ t :=
    funext fun t => Work.ELTop.rayPt_add_int hN θ t k
  rw [Work.EL.LandsN, hfun]
  exact h

/-- A ray piece only depends on the angle modulo `1`. -/
theorem rayPiece_add_int (hN : Work.EL.DynB c φ) {R : ℝ} (hR : 1 < R) (θ : ℝ) (k : ℤ) :
    Work.EL.rayPiece hN (θ + k) 0 R = Work.EL.rayPiece hN θ 0 R := by
  have h1 : Work.EL.rayPiece hN (θ + k) 0 R =
      (fun t : ℝ => Work.EL.rayPt hN (θ + k) t) '' Set.Ioc 1 R :=
    Work.ELTop.rayPiece_eq_image hN hR
  have h2 : Work.EL.rayPiece hN θ 0 R =
      (fun t : ℝ => Work.EL.rayPt hN θ t) '' Set.Ioc 1 R :=
    Work.ELTop.rayPiece_eq_image hN hR
  rw [h1, h2]
  apply Set.image_congr
  intro t _
  exact Work.ELTop.rayPt_add_int hN θ t k

/-! ## The range of the block index -/

variable {hN : Work.EL.DynB c φ}

/-- Two pairs with indices in the range `[1-m, 0]` whose landing points agree have equal
indices. -/
theorem CycLift.Y_eq_of_range (D : CycLift hN) {k k' : ℤ} (hk1 : 1 - (D.m : ℤ) ≤ k) (hk2 : k ≤ 0)
    (hk1' : 1 - (D.m : ℤ) ≤ k') (hk2' : k' ≤ 0) (h : D.Y k = D.Y k') : k = k' := by
  obtain ⟨q, hq⟩ := D.Y_inj k k' h
  have hsub : k' - k = (D.m : ℤ) * q := by linarith
  have hq0 : q = 0 := by
    by_contra hqne
    have h1 : (1 : ℤ) ≤ |q| := by
      have := abs_pos.mpr hqne
      omega
    have h2 : (D.m : ℤ) ≤ |k' - k| := by
      rw [hsub, abs_mul, abs_of_pos D.m_pos]
      calc (D.m : ℤ) = (D.m : ℤ) * 1 := by ring
        _ ≤ (D.m : ℤ) * |q| := by exact mul_le_mul_of_nonneg_left h1 (le_of_lt D.m_pos)
    have h3 : |k' - k| < (D.m : ℤ) := by
      rw [abs_sub_lt_iff]
      constructor <;> linarith
    linarith
  subst hq0
  simpa using hq.symm

/-- An angle of the pair `k` with `k ∈ [1-m, 0]` lies in the window `[B 0 - 1, A 0]`. -/
theorem CycLift.A_mem_window (D : CycLift hN) {k : ℤ} (hk1 : 1 - (D.m : ℤ) ≤ k) (hk2 : k ≤ 0) :
    D.B 0 - 1 < D.A k ∧ D.A k ≤ D.A 0 := by
  have hk : D.A (1 - (D.m : ℤ)) ≤ D.A k := D.A_le_of_le hk1
  have hgt : D.B 0 < D.A 1 := D.B_lt_A 0
  rw [D.A_one_sub_m] at hk
  exact ⟨by linarith, D.A_le_of_le hk2⟩

theorem CycLift.B_mem_window (D : CycLift hN) {k : ℤ} (hk1 : 1 - (D.m : ℤ) ≤ k) (hk2 : k ≤ 0) :
    D.B 0 - 1 ≤ D.B (k - 1) ∧ D.B (k - 1) < D.B 0 := by
  have h1 : -(D.m : ℤ) ≤ k - 1 := by linarith
  have h2 : k - 1 ≤ -1 := by linarith
  exact D.B_window h1 h2

/-- An angle lying in an equipotential interval `[B (k-1), A k]` with `k ∈ [1-m, 0]` lies in
the window `[B 0 - 1, A 0]`. -/
theorem CycLift.mem_window_of_eqArc (D : CycLift hN) {k : ℤ} (hk1 : 1 - (D.m : ℤ) ≤ k)
    (hk2 : k ≤ 0) {θ : ℝ} (hθ : θ ∈ Set.Icc (D.B (k - 1)) (D.A k)) :
    D.B 0 - 1 ≤ θ ∧ θ ≤ D.A 0 := by
  obtain ⟨hb, _⟩ := D.B_mem_window hk1 hk2
  obtain ⟨_, ha⟩ := D.A_mem_window hk1 hk2
  exact ⟨le_trans hb hθ.1, le_trans hθ.2 ha⟩

/-- Two angles in the windows of two blocks with indices in `[1-m, 0]` which are congruent
modulo `1` are equal. -/
theorem CycLift.angle_eq_of_congr_window (D : CycLift hN) {k k' : ℤ}
    (hk1 : 1 - (D.m : ℤ) ≤ k) (hk2 : k ≤ 0) (hk1' : 1 - (D.m : ℤ) ≤ k') (hk2' : k' ≤ 0)
    {θ θ' : ℝ} (hθ : θ ∈ Set.Icc (D.B (k - 1)) (D.A k))
    (hθ' : θ' ∈ Set.Icc (D.B (k' - 1)) (D.A k')) (h : ∃ n : ℤ, θ' = θ + n) : θ' = θ := by
  obtain ⟨hx, hx'⟩ := D.mem_window_of_eqArc hk1 hk2 hθ
  obtain ⟨hy, hy'⟩ := D.mem_window_of_eqArc hk1' hk2' hθ'
  exact D.angle_eq_of_int_sub hx hx' hy hy' h

/-- Two points of the equipotential arcs of the blocks `k` and `k'`, with indices in
`[1-m, 0]`, which agree have equal indices: the equipotential intervals of different blocks
are disjoint. -/
theorem CycLift.eqArc_index_eq (D : CycLift hN) {k k' : ℤ} (hk1 : 1 - (D.m : ℤ) ≤ k) (hk2 : k ≤ 0)
    (hk1' : 1 - (D.m : ℤ) ≤ k') (hk2' : k' ≤ 0) {θ θ' : ℝ}
    (hθ : θ ∈ Set.Icc (D.B (k - 1)) (D.A k)) (hθ' : θ' ∈ Set.Icc (D.B (k' - 1)) (D.A k'))
    (h : θ' = θ) : k = k' := by
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · exfalso
    have h1 : k ≤ k' - 1 := by omega
    have h2 : D.A k ≤ D.A (k' - 1) := D.A_le_of_le h1
    have h3 : D.A (k' - 1) < D.B (k' - 1) := D.A_lt_B _
    linarith [hθ.2, hθ'.1, h]
  · exact heq
  · exfalso
    have h1 : k' ≤ k - 1 := by omega
    have h2 : D.A k' ≤ D.A (k - 1) := D.A_le_of_le h1
    have h3 : D.A (k - 1) < D.B (k - 1) := D.A_lt_B _
    linarith [hθ.1, hθ'.2, h]

/-- An angle `A k` of a block `k ∈ [1-m, 0]` is never congruent to an angle `B (k'-1)`. -/
theorem CycLift.A_not_congr_B (D : CycLift hN) {k k' : ℤ} (hk1 : 1 - (D.m : ℤ) ≤ k) (hk2 : k ≤ 0)
    (hk1' : 1 - (D.m : ℤ) ≤ k') (hk2' : k' ≤ 0) : ¬ ∃ n : ℤ, D.B (k' - 1) = D.A k + n := by
  have hAB : D.B (k - 1) < D.A k := by simpa using D.B_lt_A (k - 1)
  have hAB' : D.B (k' - 1) < D.A k' := by simpa using D.B_lt_A (k' - 1)
  rintro ⟨n, hn⟩
  have h3 : D.B (k' - 1) = D.A k :=
    D.angle_eq_of_congr_window hk1 hk2 hk1' hk2' ⟨le_of_lt hAB, le_refl _⟩
      ⟨le_refl _, le_of_lt hAB'⟩ ⟨n, hn⟩
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · have h4 : D.A k < D.B (k' - 1) := by
      have h5 : k ≤ k' - 1 := by omega
      have h6 : D.A k ≤ D.A (k' - 1) := D.A_le_of_le h5
      linarith [D.A_lt_B (k' - 1)]
    linarith
  · rw [← heq] at h3
    linarith [D.A_lt_B k]
  · have h4 : D.B (k' - 1) < D.A k := by
      have h5 : k' ≤ k := le_of_lt hgt
      have h7 : D.B (k' - 1) < D.A k' := by simpa using D.B_lt_A (k' - 1)
      have h8 : D.A k' ≤ D.A k := D.A_le_of_le h5
      linarith
    linarith


/-! ## The parameter is determined by the external angle and the potential level -/

/-- Equal angles and levels on the first third force equal parameters. -/
theorem lev_b1_eq_b1 {R σ σ' : ℝ} (hR : 1 < R)
    (h : 1 + 3 * σ * (R - 1) = 1 + 3 * σ' * (R - 1)) : σ = σ' := by
  have h1 : σ * (R - 1) = σ' * (R - 1) := by linarith
  have h2 : (σ - σ') * (R - 1) = 0 := by nlinarith [h1]
  have h3 : σ - σ' = 0 := by
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact h'
    · linarith
  linarith

/-- Equal levels on the last third force equal parameters. -/
theorem lev_b3_eq_b3 {R σ σ' : ℝ} (hR : 1 < R)
    (h : 1 + (3 - 3 * σ) * (R - 1) = 1 + (3 - 3 * σ') * (R - 1)) : σ = σ' := by
  have h1 : σ * (R - 1) = σ' * (R - 1) := by linarith
  have h2 : (σ - σ') * (R - 1) = 0 := by nlinarith [h1]
  have h3 : σ - σ' = 0 := by
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact h'
    · linarith
  linarith

/-- The level of the first third is `R` only at `σ = 1/3`. -/
theorem lev_b1_eq {R σ : ℝ} (hR : 1 < R) (h : 1 + 3 * σ * (R - 1) = R) : σ = 1 / 3 := by
  have h1 : σ * (R - 1) = (1 / 3) * (R - 1) := by linarith
  have h2 : (σ - 1 / 3) * (R - 1) = 0 := by nlinarith [h1]
  have h3 : σ - 1 / 3 = 0 := by
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact h'
    · linarith
  linarith

/-- The level of the last third is `R` only at `σ = 2/3`. -/
theorem lev_b3_eq {R σ : ℝ} (hR : 1 < R) (h : 1 + (3 - 3 * σ) * (R - 1) = R) : σ = 2 / 3 := by
  have h1 : σ * (R - 1) = (2 / 3) * (R - 1) := by linarith
  have h2 : (σ - 2 / 3) * (R - 1) = 0 := by nlinarith [h1]
  have h3 : σ - 2 / 3 = 0 := by
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact h'
    · linarith
  linarith

/-- The angle of the middle third is `A` only at the left end `σ = 1/3`. -/
theorem ang_b2_eq_left {A B σ : ℝ} (hAB : B - A ≠ 0)
    (h : A + (3 * σ - 1) * (B - A) = A) : σ = 1 / 3 := by
  have h1 : (3 * σ - 1) * (B - A) = 0 := by linarith
  have h2 : 3 * σ - 1 = 0 := by
    rcases mul_eq_zero.mp h1 with h' | h'
    · exact h'
    · exact absurd h' hAB
  linarith

/-- The angle of the middle third is `B` only at the right end `σ = 2/3`. -/
theorem ang_b2_eq_right {A B σ : ℝ} (hAB : B - A ≠ 0)
    (h : A + (3 * σ - 1) * (B - A) = B) : σ = 2 / 3 := by
  have h1 : (3 * σ - 2) * (B - A) = 0 := by nlinarith [h]
  have h2 : 3 * σ - 2 = 0 := by
    rcases mul_eq_zero.mp h1 with h' | h'
    · exact h'
    · exact absurd h' hAB
  linarith

/-- Equal angles on the middle third force equal parameters. -/
theorem ang_b2_eq_b2 {A B σ σ' : ℝ} (hAB : B - A ≠ 0)
    (h : A + (3 * σ - 1) * (B - A) = A + (3 * σ' - 1) * (B - A)) : σ = σ' := by
  have h1 : (3 * σ - 3 * σ') * (B - A) = 0 := by nlinarith [h]
  have h2 : 3 * σ - 3 * σ' = 0 := by
    rcases mul_eq_zero.mp h1 with h' | h'
    · exact h'
    · exact absurd h' hAB
  linarith

/-- On `(0,1)` the pair (external angle, potential level) determines the parameter of a block:
the block is a simple arc. -/
theorem CycLift.blkAng_blkLev_eq (D : CycLift hN) {R : ℝ} (hR : 1 < R) {k : ℤ}
    {σ σ' : ℝ} (hσ : σ ∈ Set.Ico 0 1) (hσ' : σ' ∈ Set.Ico 0 1) (h0 : σ ≠ 0) (h0' : σ' ≠ 0)
    (ha : blkAng D k σ = blkAng D k σ') (hl : blkLev R σ = blkLev R σ') : σ = σ' := by
  have hAB : D.B (k - 1) - D.A k ≠ 0 := by
    have h := D.B_lt_A (k - 1)
    have h' : D.B (k - 1) < D.A k := by simpa using h
    linarith
  by_cases h1 : σ ≤ 1 / 3
  · by_cases h1' : σ' ≤ 1 / 3
    · rw [blkLev_branch1 h1, blkLev_branch1 h1'] at hl
      exact lev_b1_eq_b1 hR hl
    · by_cases h2' : σ' ≤ 2 / 3
      · rw [blkLev_branch1 h1, blkLev_branch2 h1' h2'] at hl
        rw [blkAng_branch1 h1, blkAng_branch2 h1' h2'] at ha
        have hσv : σ = 1 / 3 := lev_b1_eq hR hl
        have hσv' : σ' = 1 / 3 := ang_b2_eq_left hAB ha.symm
        rw [hσv, hσv']
      · rw [blkLev_branch1 h1, blkLev_branch3 h1' h2'] at hl
        rw [blkAng_branch1 h1, blkAng_branch3 h1' h2'] at ha
        exact absurd (by linarith : D.B (k - 1) - D.A k = 0) hAB
  · by_cases h2 : σ ≤ 2 / 3
    · by_cases h1' : σ' ≤ 1 / 3
      · rw [blkLev_branch2 h1 h2, blkLev_branch1 h1'] at hl
        rw [blkAng_branch2 h1 h2, blkAng_branch1 h1'] at ha
        have hσv : σ = 1 / 3 := ang_b2_eq_left hAB ha
        have hσv' : σ' = 1 / 3 := lev_b1_eq hR hl.symm
        rw [hσv, hσv']
      · by_cases h2' : σ' ≤ 2 / 3
        · rw [blkAng_branch2 h1 h2, blkAng_branch2 h1' h2'] at ha
          exact ang_b2_eq_b2 hAB ha
        · rw [blkLev_branch2 h1 h2, blkLev_branch3 h1' h2'] at hl
          rw [blkAng_branch2 h1 h2, blkAng_branch3 h1' h2'] at ha
          have hσv : σ = 2 / 3 := ang_b2_eq_right hAB ha
          have hσv' : σ' = 2 / 3 := lev_b3_eq hR hl.symm
          rw [hσv, hσv']
    · by_cases h1' : σ' ≤ 1 / 3
      · rw [blkLev_branch3 h1 h2, blkLev_branch1 h1'] at hl
        rw [blkAng_branch3 h1 h2, blkAng_branch1 h1'] at ha
        exact absurd (by linarith : D.B (k - 1) - D.A k = 0) hAB
      · by_cases h2' : σ' ≤ 2 / 3
        · rw [blkLev_branch3 h1 h2, blkLev_branch2 h1' h2'] at hl
          rw [blkAng_branch3 h1 h2, blkAng_branch2 h1' h2'] at ha
          have hσv : σ = 2 / 3 := lev_b3_eq hR hl
          have hσv' : σ' = 2 / 3 := ang_b2_eq_right hAB ha.symm
          rw [hσv, hσv']
        · rw [blkLev_branch3 h1 h2, blkLev_branch3 h1' h2'] at hl
          exact lev_b3_eq_b3 hR hl

/-- **The blocks are simple and pairwise disjoint.**  Two blocks with indices in the range
`[1-m, 0]` take the same value at the parameters `σ, σ' ∈ [0,1)` only for equal indices and
equal parameters. -/
theorem CycLift.cycBlock_injOn (D : CycLift hN) {R : ℝ} (hR : 1 < R) {k k' : ℤ}
    (hk1 : 1 - (D.m : ℤ) ≤ k) (hk2 : k ≤ 0) (hk1' : 1 - (D.m : ℤ) ≤ k') (hk2' : k' ≤ 0)
    {σ σ' : ℝ} (hσ : σ ∈ Set.Ico 0 1) (hσ' : σ' ∈ Set.Ico 0 1)
    (h : cycBlock D R k σ = cycBlock D R k' σ') : k = k' ∧ σ = σ' := by
  rw [cycBlock_eq_blk D hR hσ, cycBlock_eq_blk D hR hσ'] at h
  by_cases h0 : σ = 0
  · rw [if_pos h0] at h
    by_cases h0' : σ' = 0
    · rw [if_pos h0'] at h
      have hkk := D.Y_eq_of_range hk1 hk2 hk1' hk2' h
      exact ⟨hkk, by rw [h0, h0']⟩
    · rw [if_neg h0'] at h
      have hlev := blkLev_mem hR hσ' h0'
      exact absurd (h ▸ D.Y_mem_K k) (Work.EL.rayPt_notMem_K hN hlev.1)
  · rw [if_neg h0] at h
    by_cases h0' : σ' = 0
    · rw [if_pos h0'] at h
      have hlev := blkLev_mem hR hσ h0
      exact absurd (h.symm ▸ D.Y_mem_K k') (Work.EL.rayPt_notMem_K hN hlev.1)
    · rw [if_neg h0'] at h
      have hlev := blkLev_mem hR hσ h0
      have hlev' := blkLev_mem hR hσ' h0'
      obtain ⟨ht, n, hn⟩ := (rayPt_eq_iff hN hlev.1 hlev'.1).mp h
      have hθ : blkAng D k σ ∈ Set.Icc (D.B (k - 1)) (D.A k) :=
        blkAng_mem D ⟨hσ.1, le_of_lt hσ.2⟩
      have hθ' : blkAng D k' σ' ∈ Set.Icc (D.B (k' - 1)) (D.A k') :=
        blkAng_mem D ⟨hσ'.1, le_of_lt hσ'.2⟩
      have hang' : blkAng D k' σ' = blkAng D k σ :=
        D.angle_eq_of_congr_window (k := k) (k' := k') hk1 hk2 hk1' hk2' hθ hθ' ⟨n, hn⟩
      have hkk : k = k' := D.eqArc_index_eq (k := k) (k' := k') hk1 hk2 hk1' hk2' hθ hθ' hang'
      refine ⟨hkk, ?_⟩
      subst hkk
      exact D.blkAng_blkLev_eq hR hσ hσ' h0 h0' hang'.symm ht

end Work.ELTop

