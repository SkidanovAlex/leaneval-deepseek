import Mathlib
import Submission.Work.Drive.EpsForm.SweepGenericity

namespace Work.Drive.EpsForm

open LeanEval.KnotTheory.PardonDistortion
open Set

/-- A loop off a slightly tilted slab lies on one definite side of the untitled cutting plane, and each of its points is its own epsilon-witness for the corresponding half-box. -/
theorem tilted_endgame (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    {v : R3} {h ε R : ℝ} (hε : 0 < ε) (hv1 : ‖v‖ = 1)
    (hv : ‖v - Work.BoxShrink.shiftVσ σ 1‖ ≤ ε)
    (hR : ∀ y ∈ Submission.PBox s c σ, ‖y - c‖ ≤ R)
    (hsize : ε * R < h)
    (γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ))
    (hγ : ∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ \
      Work.Drive.EpsForm.tiltedSlab (inner ℝ v c + u) v h) :
    (∀ t : ℝ, ∃ x : R3, x ∈ Submission.PBox s c σ ∧ x (σ 2) < c (σ 2) + u ∧ dist (γ t) x < ε) ∨
      (∀ t : ℝ, ∃ x : R3, x ∈ Submission.PBox s c σ ∧ c (σ 2) + u < x (σ 2) ∧
        dist (γ t) x < ε) := by
  -- the curve lies in the box
  have hP : ∀ t, γ t ∈ Submission.PBox s c σ := by
    intro t
    have h := hγ t
    rw [Set.mem_sdiff, Work.BoxShrink.Core.boxRegion, Set.mem_inter_iff] at h
    exact h.1.2
  -- and off the slab, i.e. at `v`-height at least `h` from the cutting plane
  have hslab : ∀ t, h ≤ |inner ℝ v (γ t) - (inner ℝ v c + u)| := by
    intro t
    have h := hγ t
    rw [Set.mem_sdiff] at h
    exact not_lt.mp h.2
  have hRnn : 0 ≤ R := le_trans (norm_nonneg _) (hR (γ 0) (hP 0))
  have hh : 0 < h := lt_of_le_of_lt (mul_nonneg (le_of_lt hε) hRnn) hsize
  have hcont : Continuous fun t : ℝ => inner ℝ v (γ t) - (inner ℝ v c + u) :=
    (continuous_const.inner γ.cont).sub continuous_const
  have hne : ∀ t : ℝ, inner ℝ v (γ t) - (inner ℝ v c + u) ≠ 0 := by
    intro t h0
    have := hslab t
    rw [h0, abs_zero] at this
    linarith
  -- the sign of the `v`-height relative to the cutting plane is constant on the (connected) curve
  have hsign : (∀ t : ℝ, 0 < inner ℝ v (γ t) - (inner ℝ v c + u)) ∨
      (∀ t : ℝ, inner ℝ v (γ t) - (inner ℝ v c + u) < 0) := by
    have himg : IsPreconnected
        ((fun t : ℝ => inner ℝ v (γ t) - (inner ℝ v c + u)) '' Set.univ) :=
      isPreconnected_univ.image _ hcont.continuousOn
    by_contra hcon
    push Not at hcon
    obtain ⟨t1, ht1⟩ := hcon.1
    obtain ⟨t2, ht2⟩ := hcon.2
    have hlt1 : inner ℝ v (γ t1) - (inner ℝ v c + u) < 0 := lt_of_le_of_ne ht1 (hne t1)
    have hlt2 : 0 < inner ℝ v (γ t2) - (inner ℝ v c + u) :=
      lt_of_le_of_ne ht2 (Ne.symm (hne t2))
    have hm1 : (inner ℝ v (γ t1) - (inner ℝ v c + u)) ∈
        (fun t : ℝ => inner ℝ v (γ t) - (inner ℝ v c + u)) '' Set.univ :=
      ⟨t1, trivial, rfl⟩
    have hm2 : (inner ℝ v (γ t2) - (inner ℝ v c + u)) ∈
        (fun t : ℝ => inner ℝ v (γ t) - (inner ℝ v c + u)) '' Set.univ :=
      ⟨t2, trivial, rfl⟩
    have hzero : (0 : ℝ) ∈ Set.Icc (inner ℝ v (γ t1) - (inner ℝ v c + u))
        (inner ℝ v (γ t2) - (inner ℝ v c + u)) := ⟨le_of_lt hlt1, le_of_lt hlt2⟩
    obtain ⟨t, _ht, ht⟩ := himg.ordConnected.out hm1 hm2 hzero
    exact hne t ht
  -- `shiftVσ σ 1` is the unit vector in the `σ 2`-coordinate direction
  have he : ∀ y : R3, inner ℝ (Work.BoxShrink.shiftVσ σ 1) y = y (σ 2) := by
    intro y
    rw [PiLp.inner_apply, Finset.sum_eq_single (σ 2)]
    · simp
    · intro b _ hb; simp [Work.BoxShrink.shiftVσ, hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- tilting `v` back to `e_{σ 2}` changes the height by at most `ε * R` on the box
  have hcoord : ∀ t : ℝ, (γ t) (σ 2) - (c (σ 2) + u) =
      (inner ℝ v (γ t) - (inner ℝ v c + u)) -
        inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (γ t - c) := by
    intro t
    have h1 : inner ℝ v (γ t) - inner ℝ v c = inner ℝ v (γ t - c) :=
      (inner_sub_right v (γ t) c).symm
    have h2 : inner ℝ v (γ t - c) = inner ℝ (Work.BoxShrink.shiftVσ σ 1) (γ t - c)
        + inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (γ t - c) := by
      rw [← inner_add_left]
      congr 1
      abel
    have h3 : inner ℝ (Work.BoxShrink.shiftVσ σ 1) (γ t - c) = (γ t) (σ 2) - c (σ 2) := by
      rw [he]
      rfl
    linarith
  have hbound : ∀ t : ℝ, |inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (γ t - c)| ≤ ε * R := by
    intro t
    calc |inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (γ t - c)|
        ≤ ‖v - Work.BoxShrink.shiftVσ σ 1‖ * ‖γ t - c‖ := abs_real_inner_le_norm _ _
      _ ≤ ε * R := mul_le_mul hv (hR (γ t) (hP t)) (norm_nonneg _) (le_of_lt hε)
  rcases hsign with hpos | hneg
  · -- above the slab: every point of the curve is strictly above the cutting plane
    right
    intro t
    refine ⟨γ t, hP t, ?_, ?_⟩
    · have hft : h ≤ inner ℝ v (γ t) - (inner ℝ v c + u) := by
        have hhslab := hslab t
        rwa [abs_of_pos (hpos t)] at hhslab
      have hb : inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (γ t - c) ≤ ε * R :=
        (abs_le.mp (hbound t)).2
      linarith [hcoord t, hft, hb, hsize]
    · simpa using hε
  · -- below the slab: every point of the curve is strictly below the cutting plane
    left
    intro t
    refine ⟨γ t, hP t, ?_, ?_⟩
    · have hft : inner ℝ v (γ t) - (inner ℝ v c + u) ≤ -h := by
        have hhslab := hslab t
        rw [abs_of_neg (hneg t)] at hhslab
        linarith
      have hb : -(ε * R) ≤ inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (γ t - c) :=
        (abs_le.mp (hbound t)).1
      linarith [hcoord t, hft, hb, hsize]
    · simpa using hε

end Work.Drive.EpsForm
