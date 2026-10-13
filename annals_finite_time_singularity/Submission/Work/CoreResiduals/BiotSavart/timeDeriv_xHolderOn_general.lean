import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.CoreResiduals.Defs
import Submission.Work.CoreResiduals.BiotSavart.timeDeriv_xHolderOn_of_stripBundle

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- **The `∂ₜ`-slices of a bundled strip vorticity are Hölder in `x`.**  This is the statement of
the already-proved `Work.CoreResiduals.BiotSavart.timeDeriv_xHolderOn_of_stripBundle`
(`Submission/Work/CoreResiduals/BiotSavart/timeDeriv_xHolderOn_of_stripBundle.lean`) with the
hypothesis `hα1 : (α : ℝ) < 1` deleted: that hypothesis is never used in the existing proof
(grep `hα1` in that file: only the signature line mentions it), so the same proof establishes the
statement below verbatim with `hα1` removed.  Do NOT re-derive the mathematics: copy the existing
proof body and drop the hypothesis (both reviewers confirmed this by compiling the copy). -/
theorem timeDeriv_xHolderOn_general {α : NNReal} (hα : 0 < (α : ℝ))
    {ω : Work.LWP.R3 → ℝ → Work.LWP.R3} {R S : ℝ} (hS : 0 < S)
    (hbun : Work.CoreResiduals.BSAdmissibleStripFull α ω R S) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : Work.LWP.R3, ∀ t ∈ Set.Icc (0:ℝ) S,
      ‖FiniteTimeSingularity.timeDeriv ω a t - FiniteTimeSingularity.timeDeriv ω b t‖
        ≤ C * ‖a - b‖ ^ c := by
  obtain ⟨⟨_, _, ⟨_, _⟩, ⟨H, hH⟩, ⟨_, _⟩, _⟩,
    ⟨hdc, ⟨M₁, hM₁⟩, _⟩, ⟨N₁, hN₁⟩⟩ := hbun
  -- `A = α` as a real, `k = α/(1+α)`, and the Hölder exponent `c = α²/(1+α) = A * k`.
  set A : ℝ := (α : ℝ) with hAdef
  have hApos : 0 < A := by rw [hAdef]; exact hα
  set H₀ : ℝ := (H : ℝ) with hH₀def
  have hH₀nn : 0 ≤ H₀ := by rw [hH₀def]; positivity
  -- the positive parts of the two real bounds
  set N₀ : ℝ := max N₁ 0 with hN₀def
  have hN₀nn : 0 ≤ N₀ := by rw [hN₀def]; exact le_max_right _ _
  set M₀ : ℝ := max M₁ 0 with hM₀def
  have hM₀nn : 0 ≤ M₀ := by rw [hM₀def]; exact le_max_right _ _
  set k : ℝ := A / (1 + A) with hkdef
  have hkpos : 0 < k := by rw [hkdef]; exact div_pos hApos (by linarith)
  have h1A : k * (1 + A) = A := by rw [hkdef]; field_simp
  have hS2 : 0 < S / 2 := by linarith
  have hSpow : 0 < (S / 2) ^ A := Real.rpow_pos_of_pos hS2 A
  set C₀ : ℝ := max (2 * (N₀ + H₀)) (2 * M₀ / (S / 2) ^ A) with hC₀def
  have hC₀nn : 0 ≤ C₀ := by
    rw [hC₀def]; exact le_trans (by linarith) (le_max_left _ _)
  refine ⟨A * k, mul_pos hApos hkpos, C₀, hC₀nn, ?_⟩
  intro a b t ht
  by_cases hab : a = b
  · subst hab
    have hcne : A * k ≠ 0 := (mul_pos hApos hkpos).ne'
    simp [Real.zero_rpow hcne]
  · -- the generic case: `a ≠ b`
    set ψ : ℝ → Work.LWP.R3 := fun s => ω a s - ω b s with hψdef
    set ψ' : ℝ → Work.LWP.R3 := fun s =>
      FiniteTimeSingularity.timeDeriv ω a s - FiniteTimeSingularity.timeDeriv ω b s with hψ'def
    have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hnormpos : 0 < ‖a - b‖ := norm_pos_iff.mpr hne
    -- the step size `hh = ‖a-b‖^k`
    set hh : ℝ := ‖a - b‖ ^ k with hhdef
    have hhpos : 0 < hh := by rw [hhdef]; exact Real.rpow_pos_of_pos hnormpos k
    have hhA : hh ^ A = ‖a - b‖ ^ (A * k) := by
      rw [hhdef, ← Real.rpow_mul hnormpos.le k A, mul_comm k A]
    have hh1A : hh ^ (1 + A) = ‖a - b‖ ^ A := by
      rw [hhdef, ← Real.rpow_mul hnormpos.le k (1 + A), h1A]
    -- the `x`-Hölder bound on the slices of `ψ`
    have hψ_bound : ∀ s ∈ Set.Icc (0:ℝ) S, ‖ψ s‖ ≤ H₀ * ‖a - b‖ ^ A := by
      intro s hs
      rw [hψdef]
      have h2 := (hH s hs).dist_le a b
      rw [dist_eq_norm, dist_eq_norm] at h2
      calc ‖ω a s - ω b s‖ ≤ (H:ℝ) * ‖a - b‖ ^ (α:ℝ) := h2
        _ = H₀ * ‖a - b‖ ^ A := by rw [hH₀def, hAdef]
    -- `ψ` is differentiable in `t` on the strip, with derivative `ψ'`
    have hψderiv : ∀ x ∈ Set.Icc (0:ℝ) S, HasDerivAt ψ (ψ' x) x := by
      intro x hx
      exact (hdc x hx a).sub (hdc x hx b)
    -- the `α`-Hölder bound on `∂ₜω` with the nonnegative constant `N₀`
    have key₁ : ∀ y : Work.LWP.R3, ∀ s ∈ Set.Icc (0:ℝ) S, ∀ s' ∈ Set.Icc (0:ℝ) S,
        ‖FiniteTimeSingularity.timeDeriv ω y s - FiniteTimeSingularity.timeDeriv ω y s'‖
          ≤ N₀ * |s - s'| ^ A := by
      intro y s hs s' hs'
      have h1 := hN₁ y s hs s' hs'
      rcases le_total 0 N₁ with h | h
      · rw [hN₀def, max_eq_left h, hAdef]
        exact h1
      · rw [hN₀def, max_eq_right h, hAdef, zero_mul]
        have hr : 0 ≤ |s - s'| ^ A := Real.rpow_nonneg (abs_nonneg _) _
        have h2 : N₁ * |s - s'| ^ A ≤ 0 := by nlinarith
        exact le_trans h1 h2
    have key₂ : ∀ s ∈ Set.Icc (0:ℝ) S, ∀ s' ∈ Set.Icc (0:ℝ) S,
        ‖ψ' s - ψ' s'‖ ≤ 2 * N₀ * |s - s'| ^ A := by
      intro s hs s' hs'
      have h1 := key₁ a s hs s' hs'
      have h2 := key₁ b s hs s' hs'
      rw [hψ'def]
      calc ‖(FiniteTimeSingularity.timeDeriv ω a s - FiniteTimeSingularity.timeDeriv ω b s)
              - (FiniteTimeSingularity.timeDeriv ω a s' - FiniteTimeSingularity.timeDeriv ω b s')‖
          ≤ ‖FiniteTimeSingularity.timeDeriv ω a s - FiniteTimeSingularity.timeDeriv ω a s'‖
            + ‖FiniteTimeSingularity.timeDeriv ω b s - FiniteTimeSingularity.timeDeriv ω b s'‖ := by
            rw [sub_sub_sub_comm]
            exact norm_sub_le _ _
        _ ≤ N₀ * |s - s'| ^ A + N₀ * |s - s'| ^ A := add_le_add h1 h2
        _ = 2 * N₀ * |s - s'| ^ A := by ring
    -- the mean value step on a small interval around `t` of length `hh`
    have core : ∀ u ∈ Set.Icc (0:ℝ) S, |u - t| = hh →
        (∀ x ∈ Set.uIcc t u, |x - t| ≤ hh) →
        hh * ‖ψ' t‖ ≤ 2 * (N₀ + H₀) * hh ^ (1 + A) := by
      intro u hu hueq hwin
      set f : ℝ → Work.LWP.R3 := fun s => ψ s - (s - t) • ψ' t with hfdef
      have hseg : Set.uIcc t u ⊆ Set.Icc (0:ℝ) S := by
        intro x hx
        exact ⟨le_trans (le_min ht.1 hu.1) hx.1, le_trans hx.2 (max_le ht.2 hu.2)⟩
      have hfd : ∀ x ∈ Set.uIcc t u, HasDerivAt f (ψ' x - ψ' t) x := by
        intro x hx
        have hxS := hseg hx
        have h2 : HasDerivAt (fun s : ℝ => (s - t) • ψ' t) (ψ' t) x := by
          have hh2 := ((hasDerivAt_id x).sub_const t).smul_const (ψ' t)
          rw [one_smul] at hh2
          exact hh2
        exact (hψderiv x hxS).sub h2
      have hdiff : ∀ x ∈ Set.uIcc t u, DifferentiableAt ℝ f x :=
        fun x hx => (hfd x hx).differentiableAt
      have hbound : ∀ x ∈ Set.uIcc t u, ‖deriv f x‖ ≤ 2 * N₀ * hh ^ A := by
        intro x hx
        rw [(hfd x hx).deriv]
        have hxS := hseg hx
        have hk := key₂ x hxS t ht
        have hr : |x - t| ^ A ≤ hh ^ A :=
          Real.rpow_le_rpow (abs_nonneg _) (hwin x hx) hApos.le
        calc ‖ψ' x - ψ' t‖ ≤ 2 * N₀ * |x - t| ^ A := hk
          _ ≤ 2 * N₀ * hh ^ A := mul_le_mul_of_nonneg_left hr (by linarith)
      have hmvt : ‖f u - f t‖ ≤ 2 * N₀ * hh ^ A * ‖u - t‖ :=
        Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_uIcc t u)
          Set.left_mem_uIcc Set.right_mem_uIcc
      have hmvt' : ‖f u - f t‖ ≤ 2 * N₀ * (hh ^ A * hh) := by
        have hnorm : ‖u - t‖ = hh := by rw [Real.norm_eq_abs, hueq]
        calc ‖f u - f t‖ ≤ 2 * N₀ * hh ^ A * ‖u - t‖ := hmvt
          _ = 2 * N₀ * (hh ^ A * hh) := by rw [hnorm, mul_assoc]
      have hkey : (u - t) • ψ' t = (ψ u - ψ t) - (f u - f t) := by
        simp only [hfdef]
        rw [sub_self, zero_smul, sub_zero]
        abel
      have htri : ‖(u - t) • ψ' t‖ ≤ ‖ψ u - ψ t‖ + ‖f u - f t‖ := by
        rw [hkey]; exact norm_sub_le _ _
      have hLHS : ‖(u - t) • ψ' t‖ = hh * ‖ψ' t‖ := by
        rw [norm_smul, Real.norm_eq_abs, hueq]
      have h1 : ‖ψ u - ψ t‖ ≤ 2 * H₀ * ‖a - b‖ ^ A := by
        have hψu := hψ_bound u hu
        have hψt := hψ_bound t ht
        calc ‖ψ u - ψ t‖ ≤ ‖ψ u‖ + ‖ψ t‖ := norm_sub_le _ _
          _ ≤ H₀ * ‖a - b‖ ^ A + H₀ * ‖a - b‖ ^ A := add_le_add hψu hψt
          _ = 2 * H₀ * ‖a - b‖ ^ A := by ring
      calc hh * ‖ψ' t‖ = ‖(u - t) • ψ' t‖ := hLHS.symm
        _ ≤ ‖ψ u - ψ t‖ + ‖f u - f t‖ := htri
        _ ≤ 2 * H₀ * ‖a - b‖ ^ A + 2 * N₀ * (hh ^ A * hh) := add_le_add h1 hmvt'
        _ = 2 * (N₀ + H₀) * hh ^ (1 + A) := by
            have h3 : hh ^ A * hh = hh ^ (1 + A) := by
              rw [Real.rpow_add hhpos 1 A, Real.rpow_one]; ring
            rw [hh1A.symm, h3]; ring
    by_cases hle : hh ≤ S / 2
    · -- a full interval of length `hh` fits inside the strip around `t`
      have hmain : hh * ‖ψ' t‖ ≤ 2 * (N₀ + H₀) * hh ^ (1 + A) := by
        rcases le_total hh t with hhle | hhle
        · -- the interval `[t-hh, t]`
          have hu : t - hh ∈ Set.Icc (0:ℝ) S := ⟨by linarith, by linarith [ht.2]⟩
          have hueq : |(t - hh) - t| = hh := by
            have h4 : (t - hh) - t = -hh := by ring
            rw [h4, abs_neg, abs_of_pos hhpos]
          have hwin : ∀ x ∈ Set.uIcc t (t - hh), |x - t| ≤ hh := by
            intro x hx
            rw [Set.uIcc_of_ge (by linarith : t - hh ≤ t)] at hx
            rw [abs_le]
            exact ⟨by linarith [hx.1], by linarith [hx.2, hhpos.le]⟩
          exact core (t - hh) hu hueq hwin
        · -- the interval `[t, t+hh]`
          have hu : t + hh ∈ Set.Icc (0:ℝ) S :=
            ⟨by linarith [ht.1], by linarith [hhle, hle]⟩
          have hueq : |(t + hh) - t| = hh := by
            have h4 : (t + hh) - t = hh := by ring
            rw [h4, abs_of_pos hhpos]
          have hwin : ∀ x ∈ Set.uIcc t (t + hh), |x - t| ≤ hh := by
            intro x hx
            rw [Set.uIcc_of_le (by linarith : t ≤ t + hh)] at hx
            rw [abs_le]
            exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
          exact core (t + hh) hu hueq hwin
      have hfinal : ‖ψ' t‖ ≤ 2 * (N₀ + H₀) * ‖a - b‖ ^ (A * k) := by
        have h4 : 2 * (N₀ + H₀) * hh ^ (1 + A) = hh * (2 * (N₀ + H₀) * hh ^ A) := by
          rw [Real.rpow_add hhpos 1 A, Real.rpow_one]; ring
        have h5 := h4 ▸ hmain
        have h6 : ‖ψ' t‖ ≤ 2 * (N₀ + H₀) * hh ^ A := le_of_mul_le_mul_left h5 hhpos
        rwa [hhA] at h6
      calc ‖ψ' t‖ ≤ 2 * (N₀ + H₀) * ‖a - b‖ ^ (A * k) := hfinal
        _ ≤ C₀ * ‖a - b‖ ^ (A * k) :=
            mul_le_mul_of_nonneg_right (by rw [hC₀def]; exact le_max_left _ _)
              (Real.rpow_nonneg (norm_nonneg _) _)
    · -- the step size is large: crudely bound `‖ψ' t‖` by `2 M₀`
      have hcrude : ‖ψ' t‖ ≤ 2 * M₀ := by
        have h1 : ‖FiniteTimeSingularity.timeDeriv ω a t‖ ≤ M₀ := by
          rw [hM₀def]; exact le_trans (hM₁ t ht a) (le_max_left _ _)
        have h2 : ‖FiniteTimeSingularity.timeDeriv ω b t‖ ≤ M₀ := by
          rw [hM₀def]; exact le_trans (hM₁ t ht b) (le_max_left _ _)
        calc ‖ψ' t‖ = ‖FiniteTimeSingularity.timeDeriv ω a t
            - FiniteTimeSingularity.timeDeriv ω b t‖ := rfl
          _ ≤ ‖FiniteTimeSingularity.timeDeriv ω a t‖
              + ‖FiniteTimeSingularity.timeDeriv ω b t‖ := norm_sub_le _ _
          _ ≤ M₀ + M₀ := add_le_add h1 h2
          _ = 2 * M₀ := by ring
      have hb : (S / 2) ^ A ≤ ‖a - b‖ ^ (A * k) := by
        have hlt : S / 2 < hh := lt_of_not_ge hle
        have hrp : (S / 2) ^ A < hh ^ A := Real.rpow_lt_rpow hS2.le hlt hApos
        calc (S / 2) ^ A ≤ hh ^ A := le_of_lt hrp
          _ = ‖a - b‖ ^ (A * k) := hhA
      calc ‖ψ' t‖ ≤ 2 * M₀ := hcrude
        _ = 2 * M₀ / (S / 2) ^ A * (S / 2) ^ A := (div_mul_cancel₀ (2 * M₀) hSpow.ne').symm
        _ ≤ C₀ * ‖a - b‖ ^ (A * k) := by
            rw [hC₀def]
            exact mul_le_mul (le_max_right _ _) hb hSpow.le hC₀nn


end Work.CoreResiduals.BiotSavart
