import Mathlib
import Submission.Work.NAKANE2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE2.Surgery

open Classical Filter Set Function MeasureTheory

/-!
# Admissibility of the invariant coefficient `glueMuW`

The coefficient `Work.NAKANE2.glueMuW F W` is the pull-back of `0` along the `F`-orbit until
the first *entrance* into the forward-invariant conformal region `W`.  This file proves that,
under the dilatation bound `‖∂F‖ ≤ κ ‖∂̄F‖` (`κ < 1`) and the hypothesis that every point with
`∂F ≠ 0` already maps into `W`, the coefficient is `Admissible` in the sense of
`Work.MRMT.Found.Admissible`: measurable, bounded a.e. by `κ`, and boundedly supported (its
support is contained in the closed ball carrying `Wᶜ`).

The measurability is the only delicate part: `glueMuW` is defined through a `Nat.find`, so we
first show that the first entrance time

`hitTimeW F W z = Nat.find (…)` (and `0` if there is no entrance)

has Borel level sets, whence is measurable, and then write
`glueMuW F W z = pullIter F (hitTimeW F W z) z`.
-/

/-! ## The first entrance time into `W` -/

/-- The first time the orbit of `z` under `F` enters `W` (`0` if it never does). -/
private noncomputable def hitTimeW (F : ℂ → ℂ) (W : Set ℂ) (z : ℂ) : ℕ :=
  if h : ∃ n : ℕ, (F^[n]) z ∈ W then Nat.find h else 0

/-- `glueMuW` is the pull-back of `0` along `hitTimeW F W z` steps. -/
private theorem glueMuW_eq_pullIter_hitTimeW {F : ℂ → ℂ} {W : Set ℂ} (z : ℂ) :
    Work.NAKANE2.glueMuW F W z = Work.FBif.pullIter F (hitTimeW F W z) z := by
  unfold Work.NAKANE2.glueMuW hitTimeW
  by_cases h : ∃ n : ℕ, (F^[n]) z ∈ W
  · simp only [h, dif_pos]
  · simp only [h, dif_neg, not_false_eq_true]
    rfl

/-- The first entrance time is `0` exactly when the orbit never enters `W`, or when `z` itself
lies in `W`. -/
private theorem hitTimeW_eq_zero_iff {F : ℂ → ℂ} {W : Set ℂ} {z : ℂ} :
    hitTimeW F W z = 0 ↔ (¬ ∃ m : ℕ, (F^[m]) z ∈ W) ∨ z ∈ W := by
  constructor
  · intro h
    by_cases hz : ∃ m : ℕ, (F^[m]) z ∈ W
    · right
      have h0 : Nat.find hz = 0 := by simpa only [hitTimeW, dite_eq_left hz] using h
      have := (Nat.find_eq_zero hz).mp h0
      simpa using this
    · left; exact hz
  · intro h
    rcases h with h | h
    · simp only [hitTimeW, dite_eq_right h]
    · have hz : ∃ m : ℕ, (F^[m]) z ∈ W := ⟨0, by simpa using h⟩
      simp only [hitTimeW, dite_eq_left hz]
      exact (Nat.find_eq_zero hz).mpr (by simpa using h)

/-- The first entrance time equals `k + 1` exactly when time `k + 1` is an entrance time and no
earlier time is. -/
private theorem hitTimeW_eq_succ_iff {F : ℂ → ℂ} {W : Set ℂ} {z : ℂ} {k : ℕ} :
    hitTimeW F W z = k + 1 ↔
      (F^[k + 1]) z ∈ W ∧ ∀ j : ℕ, j < k + 1 → (F^[j]) z ∉ W := by
  constructor
  · intro h
    have hz : ∃ m : ℕ, (F^[m]) z ∈ W := by
      by_contra hc
      rw [hitTimeW, dite_eq_right hc] at h
      exact Nat.succ_ne_zero k h.symm
    have hfind : Nat.find hz = k + 1 := by
      rw [hitTimeW, dite_eq_left hz] at h; exact h
    constructor
    · have hspec := Nat.find_spec hz
      rwa [hfind] at hspec
    · intro j hj
      exact Nat.find_min hz (by rw [hfind]; exact hj)
  · intro h1
    obtain ⟨h1, h2⟩ := h1
    have hz : ∃ m : ℕ, (F^[m]) z ∈ W := ⟨k + 1, h1⟩
    rw [hitTimeW, dite_eq_left hz]
    exact (Nat.find_eq_iff hz).mpr ⟨h1, fun n hn => h2 n hn⟩

/-- Every level set of the first entrance time into `W` is Borel. -/
private theorem measurableSet_hitTimeW_eq {F : ℂ → ℂ} {W : Set ℂ} (hF : Measurable F)
    (hW : MeasurableSet W) (n : ℕ) :
    MeasurableSet {z : ℂ | hitTimeW F W z = n} := by
  have hC : ∀ k : ℕ, MeasurableSet {z : ℂ | (F^[k]) z ∈ W} := fun k =>
    hW.preimage (hF.iterate k)
  rcases n with _ | k
  · have h1 : MeasurableSet {z : ℂ | ¬ ∃ m : ℕ, (F^[m]) z ∈ W} := by
      rw [show {z : ℂ | ¬ ∃ m : ℕ, (F^[m]) z ∈ W}
          = (⋃ m, {z : ℂ | (F^[m]) z ∈ W})ᶜ from by
        ext z; simp]
      exact (MeasurableSet.iUnion fun m => hC m).compl
    have hset : {z : ℂ | hitTimeW F W z = 0} =
        {z : ℂ | ¬ ∃ m : ℕ, (F^[m]) z ∈ W} ∪ W := by
      ext z; simp only [Set.mem_ofPred_eq, Set.mem_union]; exact hitTimeW_eq_zero_iff
    rw [hset]
    exact h1.union hW
  · have h2 : MeasurableSet {z : ℂ | ∀ j : ℕ, j < k + 1 → (F^[j]) z ∉ W} := by
      rw [show {z : ℂ | ∀ j : ℕ, j < k + 1 → (F^[j]) z ∉ W}
          = ⋂ j, ⋂ (_ : j < k + 1), ({z : ℂ | (F^[j]) z ∈ W})ᶜ from by
        ext z; simp [Set.mem_iInter]]
      exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hC j).compl
    have hset : {z : ℂ | hitTimeW F W z = k + 1} =
        {z : ℂ | (F^[k + 1]) z ∈ W} ∩
          {z : ℂ | ∀ j : ℕ, j < k + 1 → (F^[j]) z ∉ W} := by
      ext z; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]; exact hitTimeW_eq_succ_iff
    rw [hset]
    exact (hC (k + 1)).inter h2

/-- The first entrance time into `W` is measurable. -/
private theorem measurable_hitTimeW {F : ℂ → ℂ} {W : Set ℂ} (hF : Measurable F)
    (hW : MeasurableSet W) : Measurable (hitTimeW F W) :=
  measurable_to_nat fun z => measurableSet_hitTimeW_eq hF hW (hitTimeW F W z)

/-- **Measurability of `glueMuW`.** -/
private theorem measurable_glueMuW {F : ℂ → ℂ} {W : Set ℂ} (hF : Measurable F)
    (hW : MeasurableSet W) : Measurable (Work.NAKANE2.glueMuW F W) := by
  have hhit : Measurable (hitTimeW F W) := measurable_hitTimeW hF hW
  have hpair : Measurable (fun z : ℂ => (z, hitTimeW F W z)) := measurable_id.prodMk hhit
  have hG : Measurable (fun p : ℂ × ℕ => Work.FBif.pullIter F p.2 p.1) :=
    measurable_from_prod_countable_left fun n => Work.FBif.measurable_pullIter hF n
  have hcomp := hG.comp hpair
  have heq : ((fun p : ℂ × ℕ => Work.FBif.pullIter F p.2 p.1) ∘ fun z => (z, hitTimeW F W z))
      = Work.NAKANE2.glueMuW F W := by
    funext z; simp only [Function.comp_apply]
    exact (glueMuW_eq_pullIter_hitTimeW z).symm
  rwa [heq] at hcomp

/-! ## The a.e. bound -/

/-- Along a finite orbit whose first entrance into `W` happens at time `n`, the `n`-fold
pull-back of `0` has norm at most `κ`.  This is the exact analogue of
`Work.FBif.norm_glueMu_le` for the region `W`. -/
private theorem pullIter_norm_le_of_hit {F : ℂ → ℂ} {W : Set ℂ} {κ : ℝ}
    (hratio : ∀ z : ℂ, ‖Work.MRMT.dz F z‖ ≤ κ * ‖Work.MRMT.dzbar F z‖)
    (hκ : 0 ≤ κ)
    (hone : ∀ z : ℂ, Work.MRMT.dz F z ≠ 0 → F z ∈ W) :
    ∀ (n : ℕ) (z : ℂ), (∀ j < n, (F^[j]) z ∉ W) → (F^[n]) z ∈ W →
      ‖Work.FBif.pullIter F n z‖ ≤ κ := by
  intro n
  induction n with
  | zero =>
    intro z _ _
    rw [Work.FBif.pullIter_zero, norm_zero]
    exact hκ
  | succ n ih =>
    intro z hmin hhit
    have hmin' : ∀ j < n, (F^[j]) (F z) ∉ W := by
      intro j hj
      have h := hmin (j + 1) (by omega)
      rwa [Function.iterate_succ_apply] at h
    have hhit' : (F^[n]) (F z) ∈ W := by
      have h := hhit
      rwa [Function.iterate_succ_apply] at h
    have hIH : ‖Work.FBif.pullIter F n (F z)‖ ≤ κ := ih (F z) hmin' hhit'
    have hstep : Work.FBif.pullIter F (n + 1) z =
        Work.MRMT.Found.pullRev (Function.const ℂ (Work.FBif.pullIter F n (F z))) F z := by
      rw [Work.FBif.pullIter_succ]
      exact Work.FBif.pullRev_congr (by rw [Function.const_apply])
    rw [hstep]
    have hcond : Work.MRMT.dz F z = 0 ∨ Work.FBif.pullIter F n (F z) = 0 := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · right
        rw [h0]
        exact Work.FBif.pullIter_zero F (F z)
      · left
        by_contra hne
        have hFzW : F z ∈ W := hone z hne
        have hnotW : (F^[1]) z ∉ W := hmin 1 (by omega)
        rw [Function.iterate_one] at hnotW
        exact hnotW hFzW
    exact Work.FBif.norm_pullRev_const_le (hratio z) hκ hcond hIH

/-- **The a.e. bound.**  Under the dilatation bound `‖∂F‖ ≤ κ ‖∂̄F‖`, with `0 ≤ κ`, and the
hypothesis that every point with `∂F ≠ 0` already maps into the conformal region `W`, the
invariant coefficient `glueMuW F W` is everywhere bounded by `κ`. -/
private theorem norm_glueMuW_le {F : ℂ → ℂ} {W : Set ℂ} {κ : ℝ}
    (hratio : ∀ z : ℂ, ‖Work.MRMT.dz F z‖ ≤ κ * ‖Work.MRMT.dzbar F z‖)
    (hκ : 0 ≤ κ)
    (hone : ∀ z : ℂ, Work.MRMT.dz F z ≠ 0 → F z ∈ W) :
    ∀ z : ℂ, ‖Work.NAKANE2.glueMuW F W z‖ ≤ κ := by
  intro z
  by_cases hz : ∃ n : ℕ, (F^[n]) z ∈ W
  · rw [Work.NAKANE2.glueMuW_of_hit hz]
    exact pullIter_norm_le_of_hit hratio hκ hone (Nat.find hz) z
      (fun j hj => Nat.find_min hz hj) (Nat.find_spec hz)
  · rw [Work.NAKANE2.glueMuW_of_not_hit hz, norm_zero]
    exact hκ

/-! ## Bounded support -/

/-- The support of `glueMuW F W` is contained in the closed ball carrying `Wᶜ`: a point outside
that ball lies in `W`, where the coefficient vanishes. -/
private theorem support_glueMuW_subset {F : ℂ → ℂ} {W : Set ℂ} {R : ℝ}
    (hzero : ∀ z ∈ W, Work.NAKANE2.glueMuW F W z = 0)
    (hsub : Wᶜ ⊆ Metric.closedBall 0 R) :
    Function.support (Work.NAKANE2.glueMuW F W) ⊆ Metric.closedBall 0 R := by
  intro z hz
  by_contra h
  have hzW : z ∈ W := by
    by_contra hzW
    exact h (hsub hzW)
  exact (Function.mem_support.mp hz) (hzero z hzW)

/-! ## The target lemma -/

theorem admissible_glueMuW {F : ℂ → ℂ} {W : Set ℂ} {κ R : ℝ}
    (hκ : 0 ≤ κ) (hκ1 : κ < 1) (hmF : Measurable F) (hWm : MeasurableSet W)
    (hratio : ∀ z : ℂ, ‖Work.MRMT.dz F z‖ ≤ κ * ‖Work.MRMT.dzbar F z‖)
    (hone : ∀ z : ℂ, Work.MRMT.dz F z ≠ 0 → F z ∈ W)
    (hzero : ∀ z ∈ W, Work.NAKANE2.glueMuW F W z = 0)
    (hsub : Wᶜ ⊆ Metric.closedBall 0 R) :
    Work.MRMT.Found.Admissible (Work.NAKANE2.glueMuW F W) := by
  have hmeas : Measurable (Work.NAKANE2.glueMuW F W) := measurable_glueMuW hmF hWm
  have hbound : ∀ z : ℂ, ‖Work.NAKANE2.glueMuW F W z‖ ≤ κ :=
    norm_glueMuW_le hratio hκ hone
  have hsupp : Function.support (Work.NAKANE2.glueMuW F W) ⊆ Metric.closedBall 0 R :=
    support_glueMuW_subset hzero hsub
  exact ⟨hmeas.aestronglyMeasurable, ⟨κ, hκ1, Filter.Eventually.of_forall hbound⟩,
    Metric.isBounded_closedBall.subset hsupp⟩

end Work.NAKANE2.Surgery
