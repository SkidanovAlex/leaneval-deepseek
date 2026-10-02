/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.LavaursA.Tools` — generic tools for the lock-step assembly

Three elementary tools used by `Submission/Work/PARIMPL2/Lavaurs/lockstep_complex.lean`:

* `psi_shift_iter` — the iterated shift `Ψ (w + n) = F^n (Ψ w)` of the repelling coordinate;
* `psi_unif` — uniform continuity of `Ψ` on the compact rectangle of levels that occur in the
  lock-step;
* `ft_iter_unif` — uniform (in `m ≤ M`, in the parameter `c` near `c₀` and in `q ∈ Kq`) continuity
  of `q ↦ (Ft c)^[m] q` at `c₀`.
-/
import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.PARIMPL.Transit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.Lavaurs

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- **The iterated shift of the repelling coordinate**: `Ψ (w + n) = (Ft c₀)^[n] (Ψ w)`. -/
theorem psi_shift_iter
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁)
    (n : ℕ) (w : ℂ) :
    fl.Ψ (w + (n : ℂ)) = (Work.PARIMPL.Ft c₀)^[n] (fl.Ψ w) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : w + ((k + 1 : ℕ) : ℂ) = (w + (k : ℂ)) + 1 := by push_cast; ring
    rw [h1, fl.Ψ_shift, ih, Function.iterate_succ_apply']

/-- **Uniform continuity of `Ψ` on the compact rectangle** `[-Xo-3, 0] × [-Hu, Hu]`. -/
theorem psi_unif
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁)
    (Xo Hu : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u u' : ℂ,
      u.re ∈ Set.Icc (-Xo - 3) 0 → |u.im| ≤ Hu →
      u'.re ∈ Set.Icc (-Xo - 3) 0 → |u'.im| ≤ Hu →
      ‖u - u'‖ ≤ δ → ‖fl.Ψ u - fl.Ψ u'‖ ≤ ε := by
  set K : Set ℂ := {w : ℂ | w.re ∈ Set.Icc (-Xo - 3) 0 ∧ w.im ∈ Set.Icc (-Hu) Hu} with hKdef
  have hKcomp : IsCompact K := by
    rw [hKdef]
    have hclosed : IsClosed {w : ℂ | w.re ∈ Set.Icc (-Xo - 3) 0 ∧ w.im ∈ Set.Icc (-Hu) Hu} :=
      (isClosed_Icc.preimage Complex.continuous_re).inter
        (isClosed_Icc.preimage Complex.continuous_im)
    refine (isCompact_closedBall (0 : ℂ) (|(-Xo - 3)| + |0| + |Hu| + 1)).of_isClosed_subset hclosed ?_
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right]
    have h4 := Complex.norm_le_abs_re_add_abs_im w
    have h5 : |w.re| ≤ max |(-Xo - 3)| |0| := by
      rw [abs_le]
      exact ⟨by linarith [hw.1.1, neg_abs_le (-Xo - 3), le_max_left |(-Xo - 3)| |0|],
             by linarith [hw.1.2, le_max_right |(-Xo - 3)| |0|, abs_nonneg (0:ℝ)]⟩
    have h6 : |w.im| ≤ |Hu| := by
      rw [abs_le]
      exact ⟨by linarith [hw.2.1, le_abs_self Hu],
             by linarith [hw.2.2, le_abs_self Hu]⟩
    have h7 : max |(-Xo - 3)| |0| ≤ |(-Xo - 3)| + |0| := by
      exact max_le (le_add_of_nonneg_right (abs_nonneg (0:ℝ))) (le_add_of_nonneg_left (abs_nonneg (-Xo - 3)))
    linarith [h4, h5, h6, h7, abs_nonneg Hu]
  have hcont : ContinuousOn fl.Ψ K := fl.Ψ_diff.continuous.continuousOn
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ :=
    (Metric.uniformContinuousOn_iff.mp (hKcomp.uniformContinuousOn_of_continuous hcont)) ε hε
  refine ⟨δ₁ / 2, by positivity, fun u u' hu1 hu2 hu3 hu4 hd => ?_⟩
  have hlt : dist u u' < δ₁ := by
    rw [dist_eq_norm]; linarith
  have hmem1 : u ∈ K := by
    rw [hKdef]; exact ⟨hu1, by rw [abs_le] at hu2; exact hu2⟩
  have hmem2 : u' ∈ K := by
    rw [hKdef]; exact ⟨hu3, by rw [abs_le] at hu4; exact hu4⟩
  have := hδ₁' u hmem1 u' hmem2 hlt
  exact le_of_lt (by simpa [dist_eq_norm] using this)

/-- **Uniform continuity of the iterates `q ↦ (Ft c)^[m] q` in `(c, q)`, for `m ≤ M`, at the
diagonal `c = c₀`.** -/
theorem ft_iter_unif {Kq : Set ℂ} (hKq : IsCompact Kq) (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c : ℂ, ‖c - c₀‖ < ρ → ∀ m : ℕ, m ≤ M → ∀ q ∈ Kq,
      ‖(Work.PARIMPL.Ft c)^[m] q - (Work.PARIMPL.Ft c₀)^[m] q‖ ≤ ε := by
  induction M with
  | zero =>
    refine ⟨1, one_pos, fun c hc m hm q hq => ?_⟩
    have hm0 : m = 0 := Nat.le_zero.mp hm
    subst hm0
    simp only [Function.iterate_zero, id_eq, sub_self, norm_zero]
    exact hε.le
  | succ M ih =>
    obtain ⟨ρ₁, hρ₁, h₁⟩ := ih
    -- the (M+1)-st iterate is uniformly continuous on a compact rectangle
    have hKc : IsCompact (Metric.closedBall c₀ 1) := isCompact_closedBall c₀ 1
    have hK : IsCompact (Metric.closedBall c₀ 1 ×ˢ Kq) := hKc.prod hKq
    have hcont : ContinuousOn (fun p : ℂ × ℂ => (Work.PARIMPL.Ft p.1)^[M + 1] p.2)
        (Metric.closedBall c₀ 1 ×ˢ Kq) :=
      (Work.PARIMPL.continuous_orbit_pair (M + 1)).continuousOn
    obtain ⟨δ, hδ, hδ'⟩ :=
      (Metric.uniformContinuousOn_iff.mp (hK.uniformContinuousOn_of_continuous hcont)) ε hε
    refine ⟨min ρ₁ (min δ 1), lt_min hρ₁ (lt_min hδ one_pos), fun c hc m hm q hq => ?_⟩
    have hcρ : ‖c - c₀‖ < ρ₁ := lt_of_lt_of_le hc (min_le_left _ _)
    have hcδ : ‖c - c₀‖ < δ := lt_of_lt_of_le hc (le_trans (min_le_right _ _) (min_le_left _ _))
    have hc1 : ‖c - c₀‖ < 1 := lt_of_lt_of_le hc (le_trans (min_le_right _ _) (min_le_right _ _))
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hm) with hlt | heq
    · exact h₁ c hcρ m (Nat.le_of_lt_succ hlt) q hq
    · subst heq
      have hmem1 : (c, q) ∈ Metric.closedBall c₀ 1 ×ˢ Kq := by
        refine ⟨?_, hq⟩
        rw [Metric.mem_closedBall, dist_eq_norm]; exact le_of_lt hc1
      have hmem2 : (c₀, q) ∈ Metric.closedBall c₀ 1 ×ˢ Kq := by
        refine ⟨?_, hq⟩
        rw [Metric.mem_closedBall, dist_eq_norm]; simp
      have hdist : dist (c, q) (c₀, q) < δ := by
        simpa [Prod.dist_eq, dist_eq_norm] using hcδ
      have hd := hδ' (c, q) hmem1 (c₀, q) hmem2 hdist
      exact le_of_lt (by simpa [dist_eq_norm] using hd)

/-- **Uniform continuity of the iterates `q ↦ (Ft c₀)^[j] q` for `j ≤ M`** on a compact set. -/
theorem ft_same_iter_unif {Kq : Set ℂ} (hKq : IsCompact Kq) (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ j : ℕ, j ≤ M → ∀ a ∈ Kq, ∀ b ∈ Kq, ‖a - b‖ ≤ δ →
      ‖(Work.PARIMPL.Ft c₀)^[j] a - (Work.PARIMPL.Ft c₀)^[j] b‖ ≤ ε := by
  induction M with
  | zero =>
    refine ⟨ε, hε, fun j hj a ha b hb hab => ?_⟩
    have hj0 : j = 0 := Nat.le_zero.mp hj
    subst hj0
    simpa using hab
  | succ M ih =>
    obtain ⟨δ₁, hδ₁, h₁⟩ := ih
    have hK : IsCompact (({c₀} : Set ℂ) ×ˢ Kq) := isCompact_singleton.prod hKq
    have hcont : ContinuousOn (fun p : ℂ × ℂ => (Work.PARIMPL.Ft p.1)^[M + 1] p.2)
        (({c₀} : Set ℂ) ×ˢ Kq) := by
      rw [Set.singleton_prod]
      exact ((Work.PARIMPL.continuous_orbit_pair (M + 1)).continuousOn).mono (Set.subset_univ _)
    obtain ⟨δ₂, hδ₂, hδ₂'⟩ :=
      (Metric.uniformContinuousOn_iff.mp (hK.uniformContinuousOn_of_continuous hcont)) ε hε
    refine ⟨min δ₁ (δ₂ / 2), lt_min hδ₁ (by linarith), fun j hj a ha b hb hab => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hj) with hlt | heq
    · exact h₁ j (Nat.le_of_lt_succ hlt) a ha b hb (le_trans hab (min_le_left _ _))
    · subst heq
      have hmem1 : (c₀, a) ∈ ({c₀} : Set ℂ) ×ˢ Kq := ⟨rfl, ha⟩
      have hmem2 : (c₀, b) ∈ ({c₀} : Set ℂ) ×ˢ Kq := ⟨rfl, hb⟩
      have hd : dist (c₀, a) (c₀, b) < δ₂ := by
        rw [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg), dist_eq_norm]
        exact lt_of_le_of_lt (le_trans hab (min_le_right _ _)) (by linarith)
      have h := hδ₂' (c₀, a) hmem1 (c₀, b) hmem2 hd
      simpa [dist_eq_norm] using le_of_lt h

end Work.PARIMPL2.Lavaurs
