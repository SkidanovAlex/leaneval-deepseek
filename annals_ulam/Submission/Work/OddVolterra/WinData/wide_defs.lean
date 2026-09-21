import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.Window.KvecDefs

/-!
# The *wide* slope box of the odd window construction

The window construction of `Submission/Work/OddVolterra/WinData/` produces the state solution on
the slope interval `[1/4, 19/20]` (`win_data.wLo`, `win_data.wHi`), whereas the uniform estimates
of the manifest odd kernels proved so far (`Window.KJet_mem_box_deriv`,
`Window.KJet_state_lipschitz_window`, `Window.KvecMStateData`, `Work.Window.fedKvecMData`, ...)
are stated on the *narrow* square `[7/10, 19/20]²`.

This file fixes the analogous data on the full square `[1/4, 19/20]²`:

* the *wide* compact box `KJboxW n Bz` for the jet curve `u ↦ Window.KJet n h σ z u`, whose
  `aa`- and `sg`-ranges are `[1/4, 19/20]` (the narrow box `Window.KJbox` has
  `aa ∈ [9/20, 1]`, `sg ∈ [7/10, 1]`);
* `KvecMDataW n M C`, the uniform (in `h`) bound `C` and state-Lipschitz constant `M` of the
  manifest Abel kernel vector `KernelExt.KvecM` *and* of its first-slot derivative on the wide
  square and on the state ball of radius `1/2`;
* `ThetaMDataW n M B`, the same for the manifest odd `Θ`-datum `KernelExt.ThetaM` on the wide
  square and the state ball of radius `9/20` (the radius of the paper's state ball).

The elementary inputs of the jet machinery on the wide box are the radicand bounds
(`krad ∈ [1/100, 10]`, `|∂_a krad| ≤ 5`) and the radicand-jet bound `2 ^ (n+2) * 100`; both hold
on the wide box with the *same* constants, because `σ, a ∈ [1/4, 19/20]` still gives
`(σ + a) * |t| ≥ (1/2) * (1/5) = 1/10` for `|t| ≥ 1/5`.
-/

namespace Work.OddVolterra.WinData

open Work.OddVolterra
open scoped Topology ContDiff

noncomputable section

/-! ## The wide box -/

/-- The lower corner of the wide compact box of the jet curve. -/
def KJLoW (n : ℕ) (Bz : ℝ) : Window.KJIx n → ℝ
  | .aa => 1 / 4
  | .sg => 1 / 4
  | .t1 => -2
  | .t2 => 1 / 5
  | .kd1 => 1 / 100
  | .kd2 => 1 / 100
  | .c2 => -2
  | .c3 => -2
  | .Z1 _ => -Bz
  | .Z2 _ => -Bz
  | .w _ => -1 / 100

/-- The upper corner of the wide compact box of the jet curve. -/
def KJHiW (n : ℕ) (Bz : ℝ) : Window.KJIx n → ℝ
  | .aa => 19 / 20
  | .sg => 19 / 20
  | .t1 => -(1 / 5)
  | .t2 => 2
  | .kd1 => 20
  | .kd2 => 20
  | .c2 => 2
  | .c3 => 2
  | .Z1 _ => Bz
  | .Z2 _ => Bz
  | .w _ => 1 / 100

/-- The wide compact box of the jet-curve lemma. -/
def KJboxW (n : ℕ) (Bz : ℝ) : Set (Window.KJIx n → ℝ) :=
  Set.Icc (KJLoW n Bz) (KJHiW n Bz)

lemma isCompact_KJboxW (n : ℕ) (Bz : ℝ) : IsCompact (KJboxW n Bz) := isCompact_Icc
lemma convex_KJboxW (n : ℕ) (Bz : ℝ) : Convex ℝ (KJboxW n Bz) := convex_Icc _ _

lemma KJboxW_subset_KJopen (n : ℕ) (Bz : ℝ) : KJboxW n Bz ⊆ Window.KJopen n := by
  intro v hv
  have h1 : KJLoW n Bz .kd1 ≤ v .kd1 := hv.1 .kd1
  have h2 : KJLoW n Bz .kd2 ≤ v .kd2 := hv.1 .kd2
  simp only [KJLoW] at h1 h2
  exact ⟨by linarith, by linarith⟩

/-- The sharp radicand-jet constant `2 ^ (n+6) + 40` of
`Work.OddExistence.Manifest.ZS.Zrad_jet_bounds_sharp` fits under the jet bound `KJbz n`. -/
lemma sharp_le_KJbz (n : ℕ) : (2 : ℝ) ^ (n + 6) + 40 ≤ Window.KJbz n := by
  have h : (2 : ℝ) ^ (n + 6) = 16 * 2 ^ (n + 2) := by
    rw [show n + 6 = (n + 2) + 4 by omega, pow_add]
    ring
  rw [h, Window.KJbz]
  have h2 : (1 : ℝ) ≤ 2 ^ (n + 2) := one_le_pow₀ (by norm_num)
  nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 2 ^ (n + 2)) (by norm_num : (0:ℝ) ≤ 84)]

/-! ## The wide state data of the manifest kernels -/

/-- Uniform (in `h`) value, state-Lipschitz, first-slot-derivative and derivative-state-Lipschitz
data of `KernelExt.KvecM` on the *wide* square `a, σ ∈ [1/4, 19/20]` and the state ball of radius
`1/2` around `baseState σ`. -/
def KvecMDataW (n : ℕ) (M C : ℝ) : Prop :=
  ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
    Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
    (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) →
    ∀ a ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), ∀ σ ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
    ∀ z ∈ Metric.closedBall (baseState σ) (1 / 2),
    ∀ z' ∈ Metric.closedBall (baseState σ) (1 / 2),
      ‖KernelExt.KvecM n h a σ (z 0) (z 1) (z 2) (z 3)‖ ≤ C ∧
      ‖KernelExt.KvecM n h a σ (z 0) (z 1) (z 2) (z 3) -
        KernelExt.KvecM n h a σ (z' 0) (z' 1) (z' 2) (z' 3)‖ ≤ M * ‖z - z'‖ ∧
      ‖deriv (fun u : ℝ => KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) a‖ ≤ C ∧
      ‖deriv (fun u : ℝ => KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) a -
        deriv (fun u : ℝ => KernelExt.KvecM n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) a‖
        ≤ M * ‖z - z'‖ ∧
      (∀ j : Fin 2,
        ‖deriv (fun u : ℝ =>
            (KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) j) a‖ ≤ C) ∧
      (∀ j : Fin 2,
        ‖deriv (fun u : ℝ =>
            (KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) j) a -
          deriv (fun u : ℝ =>
            (KernelExt.KvecM n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) j) a‖
        ≤ M * ‖z - z'‖)

/-- Uniform (in `h`) bound and state-Lipschitz data of `KernelExt.ThetaM` on the *wide* square
`s, σ ∈ [1/4, 19/20]` and the state ball of radius `9/20` around `baseState σ`. -/
def ThetaMDataW (n : ℕ) (M B : ℝ) : Prop :=
  ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
    Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
    (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) →
    ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), ∀ σ ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
    ∀ z ∈ Metric.closedBall (baseState σ) (9 / 20),
      ‖KernelExt.ThetaM n h s σ z‖ ≤ B ∧
      ∀ z' ∈ Metric.closedBall (baseState σ) (9 / 20),
        ‖KernelExt.ThetaM n h s σ z - KernelExt.ThetaM n h s σ z'‖ ≤ M * ‖z - z'‖

end

end Work.OddVolterra.WinData
