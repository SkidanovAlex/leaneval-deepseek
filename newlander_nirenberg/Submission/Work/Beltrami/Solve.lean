/-
# Solving the Beltrami equation by the contraction argument

This file proves that the Beltrami equation `∂̄v = μ (1 + ∂v)` has a smooth solution `v` on `ℂ`,
with `‖∂v‖` and `‖∂̄v‖` small, whenever `μ` is smooth, compactly supported, supported in a ball
of radius `R` and small in the `C^{0,α}` norm (`α ∈ (0,1)`).

The proof is the classical contraction argument: writing the equation for `F := μ (1 + ∂v)` as an
integral equation `F = μ + μ · B F` (`B` the Beurling transform), one solves it by successive
approximations in the `C^{0,α}` norm and sets `v := T F`.  The analytic properties of `T` and `B`
are collected in the structure `CauchyEstimates`; they are proved in the sibling modules.
-/
import Mathlib
import Submission.Work.Beltrami.Cauchy

set_option maxHeartbeats 2000000

noncomputable section

namespace Work.Beltrami

open MeasureTheory Filter
open scoped Topology
open scoped ContDiff

/-- The analytic estimates about the Cauchy transform `cauchyT` and the Beurling transform
`beurling` that the `n = 1` Newlander--Nirenberg proof needs.  Each estimate carries a uniform
constant, independent of the function it is applied to. -/
structure CauchyEstimates where
  /-- uniform constant in the potential bound -/
  potConst : ℝ
  potConst_pos : 0 < potConst
  /-- potential bound: `‖T f z‖ ≤ potConst * M * (1+R)` for `‖f‖ ≤ M` supported in `‖z‖ ≤ R` -/
  potential : ∀ (f : ℂ → ℂ) (M R : ℝ), Continuous f → 0 ≤ R → (∀ z, ‖f z‖ ≤ M) →
      (∀ z, R < ‖z‖ → f z = 0) → ∀ z, ‖cauchyT f z‖ ≤ potConst * M * (1 + R)
  /-- uniform constant in the Schauder (Calderon--Zygmund) estimates -/
  schConst : ℝ → ℝ
  schConst_pos : ∀ α, 0 < schConst α
  /-- Schauder estimates for the Beurling transform on `C^{0,α}` -/
  schauder : ∀ (α : ℝ), 0 < α → α < 1 → ∀ (f : ℂ → ℂ) (M K R : ℝ), 0 ≤ R →
      (∀ z, ‖f z‖ ≤ M) → (∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α) →
      (∀ z, R < ‖z‖ → f z = 0) →
      (∀ z, ‖beurling f z‖ ≤ schConst α * (M + K) * (1 + R)) ∧
      (∀ x y : ℂ, ‖beurling f x - beurling f y‖ ≤
        schConst α * (M + K) * (1 + R) * ‖x - y‖ ^ α)
  /-- linearity of the Beurling transform on bounded Hölder functions with compact support -/
  beurling_sub : ∀ (α : ℝ), 0 < α → α < 1 → ∀ (f g : ℂ → ℂ) (M K R : ℝ), 0 ≤ R →
      (∀ z, ‖f z‖ ≤ M) → (∀ z, ‖g z‖ ≤ M) →
      (∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α) →
      (∀ x y : ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) →
      (∀ z, R < ‖z‖ → f z = 0) → (∀ z, R < ‖z‖ → g z = 0) →
      beurling (f - g) = beurling f - beurling g
  /-- Pompeiu formula on smooth compactly supported functions -/
  pompeiu : ∀ (f : ℂ → ℂ), ContDiff ℝ ∞ f → HasCompactSupport f → ∀ z, dbarW (cauchyT f) z = f z
  /-- `∂` of the Cauchy transform is the Beurling transform -/
  beurlingDeriv : ∀ (f : ℂ → ℂ), ContDiff ℝ ∞ f → HasCompactSupport f →
      ∀ z, dW (cauchyT f) z = beurling f z
  /-- smoothness of the Cauchy transform -/
  contDiffT : ∀ (f : ℂ → ℂ), ContDiff ℝ ∞ f → HasCompactSupport f → ContDiff ℝ ∞ (cauchyT f)
  /-- size of the smallness window for the smoothness of the fixed point, as a function of the
  four parameters `R` (bound on `u` and on `f`), `α` (the Hölder exponent), `K` (the Hölder
  constant) and `R'` (the radius outside which `u` vanishes) -/
  smoothDelta : ℝ → ℝ → ℝ → ℝ → ℝ
  smoothDelta_pos : ∀ R α K R', 0 < smoothDelta R α K R' 
  /-- smoothness of the fixed point of `u = f + μ · B u` for small `μ` (the solution is assumed
  Hölder and compactly supported, as it is in the application, so that `beurling u` is a genuine
  integral) -/
  smoothFixed : ∀ (R α K R' : ℝ), 0 < α → α < 1 → ∀ (μ f u : ℂ → ℂ),
      ContDiff ℝ ∞ μ → HasCompactSupport μ → (∀ z, ‖μ z‖ ≤ smoothDelta R α K R') →
      ContDiff ℝ ∞ f → HasCompactSupport f → (∀ z, ‖f z‖ ≤ R) → (∀ z, ‖u z‖ ≤ R) →
      (∀ x y : ℂ, ‖u x - u y‖ ≤ K * ‖x - y‖ ^ α) → (∀ z, R' < ‖z‖ → u z = 0) →
      (∀ z, u z = f z + μ z * beurling u z) → ContDiff ℝ ∞ u

/-- The smallness condition under which the contraction argument converges.  With
`q := (max potConst (schConst α) + 1) * (1+R) * (2ε+κ)` the first conjunct makes the successive
approximations contract; the second makes the solution small enough for the smoothness bootstrap. -/
def SmallEnough (H : CauchyEstimates) (α ε κ R : ℝ) : Prop :=
  (max H.potConst (H.schConst α) + 1) * (1 + R) * (2 * ε + κ) ≤ 1 / 16 ∧
  ε ≤ H.smoothDelta (2 * (2 * ε + κ)) α (2 * (2 * ε + κ)) R

variable {H : CauchyEstimates}

/-- **Existence of a smooth solution of the Beltrami equation.** -/
theorem beltrami_solve {μ : ℂ → ℂ} {α ε κ R : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hR : 1 ≤ R) (hε : 0 < ε) (hκ : 0 < κ)
    (hμs : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (hμsupp : ∀ z, R < ‖z‖ → μ z = 0)
    (hμb : ∀ z, ‖μ z‖ ≤ ε) (hμK : ∀ x y : ℂ, ‖μ x - μ y‖ ≤ κ * ‖x - y‖ ^ α)
    (hsmall : SmallEnough H α ε κ R) :
    ∃ v : ℂ → ℂ, ContDiff ℝ ∞ v ∧ (∀ z, dbarW v z = μ z * (1 + dW v z)) ∧
      (∀ z, ‖dW v z‖ ≤ 1 / 4) ∧ (∀ z, ‖dbarW v z‖ ≤ 1 / 4) := by
  classical
  set C₀ : ℝ := max H.potConst (H.schConst α) + 1 with hC₀
  have hC₀pos : 0 < C₀ := by
    have h1 := H.potConst_pos; have h2 := H.schConst_pos α
    rw [hC₀]; linarith [le_max_left H.potConst (H.schConst α),
      le_max_right H.potConst (H.schConst α)]
  have hschle : H.schConst α ≤ C₀ := by
    rw [hC₀]; linarith [le_max_right H.potConst (H.schConst α)]
  set δ : ℝ := 2 * ε + κ with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hεδ : ε ≤ δ := by rw [hδ]; linarith
  have hκδ : κ ≤ δ := by rw [hδ]; linarith
  set C : ℝ := C₀ * (1 + R) with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  have hC₀ge1 : 1 ≤ C₀ := by
    have h1 := H.potConst_pos
    rw [hC₀]; linarith [le_max_left H.potConst (H.schConst α)]
  have hCge1 : 1 ≤ C := by
    rw [hC]; nlinarith [hC₀ge1, hR]
  set q : ℝ := C * δ with hq
  have hqpos : 0 < q := by rw [hq]; positivity
  have hqδ : δ * C = q := by rw [hq]; ring
  have hq8 : q ≤ 1 / 16 := by
    have h := hsmall.1
    have hqeq : q = (max H.potConst (H.schConst α) + 1) * (1 + R) * (2 * ε + κ) := by
      rw [hq, hC, hC₀, hδ]
    rw [hqeq]; exact h
  have hq2 : q ≤ 1 / 2 := by linarith
  have hq1 : q < 1 := by linarith
  have hsmoothμ : ε ≤ H.smoothDelta (2 * δ) α (2 * δ) R := by
    have h := hsmall.2
    have h2 : (2 : ℝ) * δ = 2 * (2 * ε + κ) := by rw [hδ]
    rw [h2]; exact h
  -- the iterates
  let F : ℕ → ℂ → ℂ := fun n => Nat.rec μ (fun _ Fk => fun z => μ z * (1 + beurling Fk z)) n
  have hFrec : ∀ n, F (n + 1) = fun z => μ z * (1 + beurling (F n) z) := fun _ => rfl
  have hFzero : F 0 = μ := rfl
  have hFsupp : ∀ n z, R < ‖z‖ → F n z = 0 := by
    intro n
    induction n with
    | zero => intro z hz; rw [hFzero]; exact hμsupp z hz
    | succ k ih => intro z hz; rw [hFrec k]; simp [hμsupp z hz]
  -- uniform bounds for the iterates
  have hFbound : ∀ n, (∀ z, ‖F n z‖ ≤ 2 * δ) ∧
      (∀ x y : ℂ, ‖F n x - F n y‖ ≤ (2 * δ) * ‖x - y‖ ^ α) := by
    intro n
    induction n with
    | zero =>
      constructor
      · intro z; rw [hFzero]; linarith [hμb z, hεδ]
      · intro x y; rw [hFzero]
        have h0 : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
        have := hμK x y
        nlinarith [h0, hκδ]
    | succ k ih =>
      obtain ⟨ihM, ihK⟩ := ih
      obtain ⟨hBM, hBK⟩ := H.schauder α hα hα1 (F k) (2 * δ) (2 * δ) R (by linarith) ihM ihK
        (fun z hz => hFsupp k z hz)
      have hBbound : H.schConst α * ((2 * δ) + (2 * δ)) * (1 + R) ≤ 4 * q := by
        have heq : 4 * q = C₀ * ((2 * δ) + (2 * δ)) * (1 + R) := by
          rw [hq, hC]; ring
        rw [heq]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hschle (by positivity)) (by linarith)
      have hBM' : ∀ z, ‖beurling (F k) z‖ ≤ 4 * q := fun z => le_trans (hBM z) hBbound
      have hBK' : ∀ x y, ‖beurling (F k) x - beurling (F k) y‖ ≤ 4 * q * ‖x - y‖ ^ α := by
        intro x y
        refine le_trans (hBK x y) ?_
        exact mul_le_mul_of_nonneg_right hBbound (Real.rpow_nonneg (norm_nonneg _) α)
      have hB12 : ∀ z, ‖beurling (F k) z‖ ≤ 1 / 2 := fun z =>
        le_trans (hBM' z) (by linarith)
      constructor
      · intro z
        rw [hFrec k]
        have h1 : ‖μ z * (1 + beurling (F k) z)‖ ≤ ε * (3 / 2) := by
          rw [norm_mul]
          refine mul_le_mul (hμb z) ?_ (by positivity) (le_of_lt hε)
          calc ‖1 + beurling (F k) z‖ ≤ ‖(1 : ℂ)‖ + ‖beurling (F k) z‖ := norm_add_le _ _
            _ ≤ 1 + 1 / 2 := by rw [norm_one]; linarith [hB12 z]
            _ = 3 / 2 := by norm_num
        nlinarith [h1, hεδ, hκδ, hδpos, hε]
      · intro x y
        rw [hFrec k]
        have h0 : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
        have hsplit : μ x * (1 + beurling (F k) x) - μ y * (1 + beurling (F k) y)
            = (μ x - μ y) * (1 + beurling (F k) x)
              + μ y * (beurling (F k) x - beurling (F k) y) := by ring
        rw [hsplit]
        refine le_trans (norm_add_le _ _) ?_
        have hb1 : ‖(1 : ℂ) + beurling (F k) x‖ ≤ 3 / 2 := by
          calc ‖(1 : ℂ) + beurling (F k) x‖ ≤ ‖(1 : ℂ)‖ + ‖beurling (F k) x‖ :=
                norm_add_le _ _
            _ ≤ 1 + 1 / 2 := by rw [norm_one]; linarith [hB12 x]
            _ = 3 / 2 := by norm_num
        have h1 : ‖(μ x - μ y) * (1 + beurling (F k) x)‖ ≤ (3 / 2) * κ * ‖x - y‖ ^ α := by
          rw [norm_mul]
          calc ‖μ x - μ y‖ * ‖1 + beurling (F k) x‖
              ≤ (κ * ‖x - y‖ ^ α) * (3 / 2) :=
                mul_le_mul (hμK x y) hb1 (by positivity) (by positivity)
            _ = (3 / 2) * κ * ‖x - y‖ ^ α := by ring
        have h2 : ‖μ y * (beurling (F k) x - beurling (F k) y)‖ ≤
            (4 * ε * q) * ‖x - y‖ ^ α := by
          rw [norm_mul]
          calc ‖μ y‖ * ‖beurling (F k) x - beurling (F k) y‖
              ≤ ε * ((4 * q) * ‖x - y‖ ^ α) := by
                refine mul_le_mul (hμb y) (hBK' x y) (by positivity) (le_of_lt hε)
            _ = (4 * ε * q) * ‖x - y‖ ^ α := by ring
        calc ‖(μ x - μ y) * (1 + beurling (F k) x)‖
              + ‖μ y * (beurling (F k) x - beurling (F k) y)‖
            ≤ (3 / 2) * κ * ‖x - y‖ ^ α + (4 * ε * q) * ‖x - y‖ ^ α := add_le_add h1 h2
          _ ≤ (2 * δ) * ‖x - y‖ ^ α := by
              have h3 : (3 / 2) * κ + 4 * ε * q ≤ 2 * δ := by
                rw [hδ]; nlinarith [hε, hκ, hq8]
              nlinarith [h0, mul_le_mul_of_nonneg_right h3 h0]
  -- differences of consecutive iterates
  let Δ : ℕ → ℂ → ℂ := fun n => fun z => F (n + 1) z - F n z
  have hΔrec : ∀ n z, Δ (n + 1) z = μ z * beurling (Δ n) z := by
    intro n z
    have hlin := H.beurling_sub α hα hα1 (F (n + 1)) (F n) (2 * δ) (2 * δ) R (by linarith)
      (hFbound (n + 1)).1 (hFbound n).1 (hFbound (n + 1)).2 (hFbound n).2
      (fun w hw => hFsupp (n + 1) w hw) (fun w hw => hFsupp n w hw)
    simp only [Δ]
    rw [hFrec (n + 1), hFrec n]
    have hz : beurling (fun w => F (n + 1) w - F n w) z
        = beurling (F (n + 1)) z - beurling (F n) z := by
      exact congrFun hlin z
    rw [hz]
    ring
  have hΔbound : ∀ n, (∀ z, ‖Δ n z‖ ≤ ε * C * (ε + κ) * q ^ n) ∧
      (∀ x y, ‖Δ n x - Δ n y‖ ≤ (κ + ε) * C * (ε + κ) * q ^ n * ‖x - y‖ ^ α) := by
    intro n
    induction n with
    | zero =>
      obtain ⟨hBM, hBK⟩ := H.schauder α hα hα1 μ ε κ R (by linarith) hμb hμK hμsupp
      have hQ : H.schConst α * (ε + κ) * (1 + R) ≤ C * (ε + κ) := by
        have heq : C * (ε + κ) = C₀ * (ε + κ) * (1 + R) := by rw [hC]; ring
        rw [heq]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hschle (by linarith)) (by linarith)
      have hb : ∀ w, ‖beurling μ w‖ ≤ C * (ε + κ) := fun w => le_trans (hBM w) hQ
      have hΔ0 : ∀ w, Δ 0 w = μ w * beurling μ w := by
        intro w; simp only [Δ]; rw [hFrec 0, hFzero]; ring
      constructor
      · intro z
        rw [hΔ0 z]
        calc ‖μ z * beurling μ z‖ = ‖μ z‖ * ‖beurling μ z‖ := norm_mul _ _
          _ ≤ ε * (C * (ε + κ)) :=
              mul_le_mul (hμb z) (hb z) (by positivity) (le_of_lt hε)
          _ = ε * C * (ε + κ) * q ^ 0 := by ring
      · intro x y
        rw [hΔ0 x, hΔ0 y]
        have h0 : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
        have hsplit : μ x * beurling μ x - μ y * beurling μ y
            = (μ x - μ y) * beurling μ x + μ y * (beurling μ x - beurling μ y) := by ring
        rw [hsplit]
        refine le_trans (norm_add_le _ _) ?_
        have h1 : ‖(μ x - μ y) * beurling μ x‖ ≤ κ * (C * (ε + κ)) * ‖x - y‖ ^ α := by
          rw [norm_mul]
          calc ‖μ x - μ y‖ * ‖beurling μ x‖ ≤ (κ * ‖x - y‖ ^ α) * (C * (ε + κ)) :=
                mul_le_mul (hμK x y) (hb x) (by positivity) (by positivity)
            _ = κ * (C * (ε + κ)) * ‖x - y‖ ^ α := by ring
        have h2 : ‖μ y * (beurling μ x - beurling μ y)‖ ≤
            ε * (C * (ε + κ)) * ‖x - y‖ ^ α := by
          rw [norm_mul]
          calc ‖μ y‖ * ‖beurling μ x - beurling μ y‖
              ≤ ε * ((C * (ε + κ)) * ‖x - y‖ ^ α) := by
                refine mul_le_mul (hμb y) ?_ (by positivity) (le_of_lt hε)
                exact le_trans (hBK x y) (mul_le_mul_of_nonneg_right hQ h0)
            _ = ε * (C * (ε + κ)) * ‖x - y‖ ^ α := by ring
        calc ‖(μ x - μ y) * beurling μ x‖ + ‖μ y * (beurling μ x - beurling μ y)‖
            ≤ κ * (C * (ε + κ)) * ‖x - y‖ ^ α + ε * (C * (ε + κ)) * ‖x - y‖ ^ α :=
              add_le_add h1 h2
          _ = (κ + ε) * C * (ε + κ) * q ^ 0 * ‖x - y‖ ^ α := by ring
    | succ k ih =>
      obtain ⟨ihM, ihK⟩ := ih
      obtain ⟨hBM, hBK⟩ := H.schauder α hα hα1 (Δ k) (ε * C * (ε + κ) * q ^ k)
        ((κ + ε) * C * (ε + κ) * q ^ k) R (by linarith) ihM ihK
        (fun w hw => by simp only [Δ]; rw [hFsupp (k + 1) w hw, hFsupp k w hw]; ring)
      have hAq : ε * C * (ε + κ) * q ^ k + (κ + ε) * C * (ε + κ) * q ^ k
          = q * (ε + κ) * q ^ k := by
        rw [hq, hδ]; ring
      have hBd : ∀ w, ‖beurling (Δ k) w‖ ≤ C * (q * (ε + κ) * q ^ k) := by
        intro w
        refine le_trans (hBM w) ?_
        have heq : C * (q * (ε + κ) * q ^ k)
            = C₀ * (ε * C * (ε + κ) * q ^ k + (κ + ε) * C * (ε + κ) * q ^ k) * (1 + R) := by
          rw [hAq, hC]; ring
        rw [heq]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hschle (by
            have := pow_nonneg (le_of_lt hqpos) k; positivity)) (by linarith)
      have hBdK : ∀ x y, ‖beurling (Δ k) x - beurling (Δ k) y‖ ≤
          C * (q * (ε + κ) * q ^ k) * ‖x - y‖ ^ α := by
        intro x y
        refine le_trans (hBK x y) ?_
        have heq : C * (q * (ε + κ) * q ^ k) * ‖x - y‖ ^ α
            = C₀ * (ε * C * (ε + κ) * q ^ k + (κ + ε) * C * (ε + κ) * q ^ k)
                * (1 + R) * ‖x - y‖ ^ α := by
          rw [hAq, hC]; ring
        rw [heq]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hschle (by
              have := pow_nonneg (le_of_lt hqpos) k; positivity)) (by linarith))
          (Real.rpow_nonneg (norm_nonneg _) α)
      constructor
      · intro z
        rw [hΔrec k z]
        calc ‖μ z * beurling (Δ k) z‖ = ‖μ z‖ * ‖beurling (Δ k) z‖ := norm_mul _ _
          _ ≤ ε * (C * (q * (ε + κ) * q ^ k)) :=
              mul_le_mul (hμb z) (hBd z) (by positivity) (le_of_lt hε)
          _ = ε * C * (ε + κ) * q ^ (k + 1) := by ring
      · intro x y
        rw [hΔrec k x, hΔrec k y]
        have h0 : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
        have hsplit : μ x * beurling (Δ k) x - μ y * beurling (Δ k) y
            = (μ x - μ y) * beurling (Δ k) x
              + μ y * (beurling (Δ k) x - beurling (Δ k) y) := by ring
        rw [hsplit]
        refine le_trans (norm_add_le _ _) ?_
        have h1 : ‖(μ x - μ y) * beurling (Δ k) x‖ ≤
            κ * (C * (q * (ε + κ) * q ^ k)) * ‖x - y‖ ^ α := by
          rw [norm_mul]
          calc ‖μ x - μ y‖ * ‖beurling (Δ k) x‖
              ≤ (κ * ‖x - y‖ ^ α) * (C * (q * (ε + κ) * q ^ k)) :=
                mul_le_mul (hμK x y) (hBd x) (by positivity) (by positivity)
            _ = κ * (C * (q * (ε + κ) * q ^ k)) * ‖x - y‖ ^ α := by ring
        have h2 : ‖μ y * (beurling (Δ k) x - beurling (Δ k) y)‖ ≤
            ε * (C * (q * (ε + κ) * q ^ k)) * ‖x - y‖ ^ α := by
          rw [norm_mul]
          calc ‖μ y‖ * ‖beurling (Δ k) x - beurling (Δ k) y‖
              ≤ ε * ((C * (q * (ε + κ) * q ^ k)) * ‖x - y‖ ^ α) :=
                mul_le_mul (hμb y) (hBdK x y) (by positivity) (le_of_lt hε)
            _ = ε * (C * (q * (ε + κ) * q ^ k)) * ‖x - y‖ ^ α := by ring
        calc ‖(μ x - μ y) * beurling (Δ k) x‖
              + ‖μ y * (beurling (Δ k) x - beurling (Δ k) y)‖
            ≤ κ * (C * (q * (ε + κ) * q ^ k)) * ‖x - y‖ ^ α
              + ε * (C * (q * (ε + κ) * q ^ k)) * ‖x - y‖ ^ α := add_le_add h1 h2
          _ = (κ + ε) * C * (ε + κ) * q ^ (k + 1) * ‖x - y‖ ^ α := by ring
  -- the tail estimate
  have htail : ∀ n m z, n ≤ m → ‖F m z - F n z‖ ≤
      ε * C * (ε + κ) * (q ^ n - q ^ m) / (1 - q) := by
    intro n m z hm
    have hq1' : (1 - q) ≠ 0 := by linarith
    have hP : ∀ m (_ : n ≤ m), ‖F m z - F n z‖ ≤
        ε * C * (ε + κ) * (q ^ n - q ^ m) / (1 - q) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => simp
      | succ k hk ih =>
        have h2 : ‖F (k + 1) z - F k z‖ ≤ ε * C * (ε + κ) * q ^ k := by
          have := (hΔbound k).1 z
          simpa only [Δ] using this
        have h3 : F (k + 1) z - F n z = (F (k + 1) z - F k z) + (F k z - F n z) := by ring
        rw [h3]
        refine le_trans (norm_add_le _ _) ?_
        have hgeom : ε * C * (ε + κ) * q ^ k
              + ε * C * (ε + κ) * (q ^ n - q ^ k) / (1 - q)
            = ε * C * (ε + κ) * (q ^ n - q ^ (k + 1)) / (1 - q) := by
          field_simp
          ring
        rw [← hgeom]
        exact add_le_add h2 ih
    exact hP m hm
  -- the sequence is Cauchy
  have hcauchy : ∀ z, CauchySeq (fun n => F n z) := by
    intro z
    rw [Metric.cauchySeq_iff']
    intro ε' hε'
    have hq1' : 0 < 1 - q := by linarith
    have hden : 0 < ε' * (1 - q) / (ε * C * (ε + κ) + 1) := by positivity
    have htend : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hqpos) hq1
    obtain ⟨N, hN⟩ := ((tendsto_order.1 htend).2 _ hden).exists
    refine ⟨N, fun n hn => ?_⟩
    rw [Complex.dist_eq]
    have h1 := htail N n z hn
    have h2 : ε * C * (ε + κ) * (q ^ N - q ^ n) / (1 - q)
        ≤ ε * C * (ε + κ) * q ^ N / (1 - q) := by
      have h3 : q ^ n ≤ q ^ N := pow_le_pow_of_le_one (le_of_lt hqpos) (le_of_lt hq1) hn
      have h4 : 0 ≤ ε * C * (ε + κ) / (1 - q) := by positivity
      have h5 : q ^ N - q ^ n ≤ q ^ N := by
        have h6 : 0 ≤ q ^ n := pow_nonneg (le_of_lt hqpos) n
        linarith
      calc ε * C * (ε + κ) * (q ^ N - q ^ n) / (1 - q)
          = (ε * C * (ε + κ) / (1 - q)) * (q ^ N - q ^ n) := by ring
        _ ≤ (ε * C * (ε + κ) / (1 - q)) * q ^ N := mul_le_mul_of_nonneg_left h5 h4
        _ = ε * C * (ε + κ) * q ^ N / (1 - q) := by ring
    have h6 : ε * C * (ε + κ) * q ^ N / (1 - q) < ε' := by
      have hcoef : 0 < ε * C * (ε + κ) :=
        mul_pos (mul_pos hε hCpos) (by linarith)
      have hden : 0 < ε * C * (ε + κ) + 1 := by linarith
      have h7 : ε * C * (ε + κ) * q ^ N < ε' * (1 - q) := by
        have h8 := mul_lt_mul_of_pos_left hN hcoef
        have h9 : ε * C * (ε + κ) * (ε' * (1 - q) / (ε * C * (ε + κ) + 1))
            ≤ ε' * (1 - q) := by
          calc ε * C * (ε + κ) * (ε' * (1 - q) / (ε * C * (ε + κ) + 1))
              = (ε * C * (ε + κ) / (ε * C * (ε + κ) + 1)) * (ε' * (1 - q)) := by ring
            _ ≤ 1 * (ε' * (1 - q)) := by
                refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (le_of_lt hε') (by linarith))
                rw [div_le_one hden]; linarith
            _ = ε' * (1 - q) := by ring
        linarith
      rw [div_lt_iff₀ hq1']
      linarith
    linarith [h1, h2, h6]
  -- tail estimate for the Hölder seminorm
  have htailK : ∀ n m x y, n ≤ m → ‖(F m x - F n x) - (F m y - F n y)‖ ≤
      (κ + ε) * C * (ε + κ) * (q ^ n - q ^ m) / (1 - q) * ‖x - y‖ ^ α := by
    intro n m x y hm
    have hq1' : (1 - q) ≠ 0 := by linarith
    have hP : ∀ m (_ : n ≤ m), ‖(F m x - F n x) - (F m y - F n y)‖ ≤
        (κ + ε) * C * (ε + κ) * (q ^ n - q ^ m) / (1 - q) * ‖x - y‖ ^ α := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => simp
      | succ k hk ih =>
        have h2 : ‖(F (k + 1) x - F k x) - (F (k + 1) y - F k y)‖ ≤
            (κ + ε) * C * (ε + κ) * q ^ k * ‖x - y‖ ^ α := by
          have := (hΔbound k).2 x y
          simpa only [Δ] using this
        have h3 : (F (k + 1) x - F n x) - (F (k + 1) y - F n y)
            = ((F (k + 1) x - F k x) - (F (k + 1) y - F k y))
              + ((F k x - F n x) - (F k y - F n y)) := by ring
        rw [h3]
        refine le_trans (norm_add_le _ _) ?_
        have hgeom : (κ + ε) * C * (ε + κ) * q ^ k * ‖x - y‖ ^ α
              + (κ + ε) * C * (ε + κ) * (q ^ n - q ^ k) / (1 - q) * ‖x - y‖ ^ α
            = (κ + ε) * C * (ε + κ) * (q ^ n - q ^ (k + 1)) / (1 - q) * ‖x - y‖ ^ α := by
          field_simp
          ring
        rw [← hgeom]
        exact add_le_add h2 ih
    exact hP m hm
  -- the limit
  choose Flim hFlimtend using fun z => cauchySeq_tendsto_of_complete (hcauchy z)
  have hFlimM : ∀ z, ‖Flim z‖ ≤ 2 * δ := by
    intro z
    have h1 : Tendsto (fun n => ‖F n z‖) atTop (𝓝 ‖Flim z‖) := (hFlimtend z).norm
    exact le_of_tendsto h1 (eventually_atTop.2 ⟨0, fun n _ => (hFbound n).1 z⟩)
  have hFlimK : ∀ x y, ‖Flim x - Flim y‖ ≤ (2 * δ) * ‖x - y‖ ^ α := by
    intro x y
    have h1 : Tendsto (fun n => ‖F n x - F n y‖) atTop (𝓝 ‖Flim x - Flim y‖) :=
      ((hFlimtend x).sub (hFlimtend y)).norm
    exact le_of_tendsto h1 (eventually_atTop.2 ⟨0, fun n _ => (hFbound n).2 x y⟩)
  have hlimM : ∀ n w, ‖Flim w - F n w‖ ≤ ε * C * (ε + κ) * q ^ n / (1 - q) := by
    intro n w
    have h1 : Tendsto (fun m => ‖F m w - F n w‖) atTop (𝓝 ‖Flim w - F n w‖) :=
      ((hFlimtend w).sub tendsto_const_nhds).norm
    refine le_of_tendsto h1 ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    refine le_trans (htail n m w hm) ?_
    have h3 : q ^ m ≤ q ^ n := pow_le_pow_of_le_one (le_of_lt hqpos) (le_of_lt hq1) hm
    have h4 : 0 ≤ ε * C * (ε + κ) / (1 - q) := by positivity
    have h5 : q ^ n - q ^ m ≤ q ^ n := by
      have h6 : 0 ≤ q ^ m := pow_nonneg (le_of_lt hqpos) m
      linarith
    calc ε * C * (ε + κ) * (q ^ n - q ^ m) / (1 - q)
        = (ε * C * (ε + κ) / (1 - q)) * (q ^ n - q ^ m) := by ring
      _ ≤ (ε * C * (ε + κ) / (1 - q)) * q ^ n := mul_le_mul_of_nonneg_left h5 h4
      _ = ε * C * (ε + κ) * q ^ n / (1 - q) := by ring
  have hlimK : ∀ n x y, ‖(Flim x - F n x) - (Flim y - F n y)‖ ≤
      (κ + ε) * C * (ε + κ) * q ^ n / (1 - q) * ‖x - y‖ ^ α := by
    intro n x y
    have h1 : Tendsto (fun m => ‖(F m x - F n x) - (F m y - F n y)‖) atTop
        (𝓝 ‖(Flim x - F n x) - (Flim y - F n y)‖) :=
      (((hFlimtend x).sub tendsto_const_nhds).sub
        ((hFlimtend y).sub tendsto_const_nhds)).norm
    refine le_of_tendsto h1 ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    refine le_trans (htailK n m x y hm) ?_
    have h3 : q ^ m ≤ q ^ n := pow_le_pow_of_le_one (le_of_lt hqpos) (le_of_lt hq1) hm
    have h4 : 0 ≤ (κ + ε) * C * (ε + κ) / (1 - q) * ‖x - y‖ ^ α := by positivity
    have h5 : q ^ n - q ^ m ≤ q ^ n := by
      have h6 : 0 ≤ q ^ m := pow_nonneg (le_of_lt hqpos) m
      linarith
    calc (κ + ε) * C * (ε + κ) * (q ^ n - q ^ m) / (1 - q) * ‖x - y‖ ^ α
        = ((κ + ε) * C * (ε + κ) / (1 - q) * ‖x - y‖ ^ α) * (q ^ n - q ^ m) := by ring
      _ ≤ ((κ + ε) * C * (ε + κ) / (1 - q) * ‖x - y‖ ^ α) * q ^ n :=
          mul_le_mul_of_nonneg_left h5 h4
      _ = (κ + ε) * C * (ε + κ) * q ^ n / (1 - q) * ‖x - y‖ ^ α := by ring
  have hFlimsupp : ∀ z, R < ‖z‖ → Flim z = 0 := by
    intro z hz
    have h1 : Tendsto (fun n => F n z) atTop (𝓝 (Flim z)) := hFlimtend z
    have h2 : (fun n => F n z) = fun _ => (0 : ℂ) := funext fun n => hFsupp n z hz
    have h3 : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (Flim z)) := by
      rw [← h2]; exact h1
    exact (tendsto_nhds_unique tendsto_const_nhds h3).symm
  -- Flim satisfies the integral equation
  have hFlim_eq : ∀ z, Flim z = μ z * (1 + beurling Flim z) := by
    intro z
    have h1 : Tendsto (fun n => F (n + 1) z) atTop (𝓝 (Flim z)) := by
      have h := (hFlimtend z).comp (tendsto_add_atTop_nat 1)
      have h' : (fun n => F (n + 1) z) = (fun n => F n z) ∘ (fun a => a + 1) := rfl
      rw [h']
      exact h
    have h2 : ∀ n, F (n + 1) z = μ z * (1 + beurling (F n) z) := fun n => by rw [hFrec n]
    simp only [h2] at h1
    have h3 : Tendsto (fun n => beurling (F n) z) atTop (𝓝 (beurling Flim z)) := by
      refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
      have hbound : ∀ n, ‖beurling (F n) z - beurling Flim z‖ ≤
          2 * C * (((κ + ε) * C * (ε + κ) / (1 - q)) * q ^ n) := by
        intro n
        have hlin := H.beurling_sub α hα hα1 (F n) Flim (2 * δ) (2 * δ) R (by linarith)
          (hFbound n).1 hFlimM (hFbound n).2 hFlimK (fun w hw => hFsupp n w hw) hFlimsupp
        have hz : beurling (F n - Flim) z = beurling (F n) z - beurling Flim z := by
          simpa only [Pi.sub_apply] using congrFun hlin z
        rw [← hz]
        have hsubM : ∀ w, ‖(F n - Flim) w‖ ≤ (κ + ε) * C * (ε + κ) * q ^ n / (1 - q) := by
          intro w
          have h := hlimM n w
          have h2 : ε * C * (ε + κ) * q ^ n / (1 - q)
              ≤ (κ + ε) * C * (ε + κ) * q ^ n / (1 - q) := by
            have h3 : ε ≤ κ + ε := by linarith
            have h4 : 0 ≤ C * (ε + κ) * q ^ n / (1 - q) := by positivity
            calc ε * C * (ε + κ) * q ^ n / (1 - q)
                = ε * (C * (ε + κ) * q ^ n / (1 - q)) := by ring
              _ ≤ (κ + ε) * (C * (ε + κ) * q ^ n / (1 - q)) :=
                  mul_le_mul_of_nonneg_right h3 h4
              _ = (κ + ε) * C * (ε + κ) * q ^ n / (1 - q) := by ring
          calc ‖(F n - Flim) w‖ = ‖Flim w - F n w‖ := by
                simp only [Pi.sub_apply, norm_sub_rev]
            _ ≤ ε * C * (ε + κ) * q ^ n / (1 - q) := h
            _ ≤ (κ + ε) * C * (ε + κ) * q ^ n / (1 - q) := h2
        have hsubK : ∀ x y, ‖(F n - Flim) x - (F n - Flim) y‖ ≤
            (κ + ε) * C * (ε + κ) * q ^ n / (1 - q) * ‖x - y‖ ^ α := by
          intro x y
          have heq : (F n - Flim) x - (F n - Flim) y
              = -((Flim x - F n x) - (Flim y - F n y)) := by
            simp only [Pi.sub_apply]; ring
          rw [heq, norm_neg]
          exact hlimK n x y
        have hsupp : ∀ w, R < ‖w‖ → (F n - Flim) w = 0 := by
          intro w hw; simp only [Pi.sub_apply]; rw [hFsupp n w hw, hFlimsupp w hw]; ring
        obtain ⟨hBM, _⟩ := H.schauder α hα hα1 (F n - Flim)
          ((κ + ε) * C * (ε + κ) * q ^ n / (1 - q))
          ((κ + ε) * C * (ε + κ) * q ^ n / (1 - q)) R (by linarith) hsubM hsubK hsupp
        refine le_trans (hBM z) ?_
        calc H.schConst α * (((κ + ε) * C * (ε + κ) * q ^ n / (1 - q))
                + ((κ + ε) * C * (ε + κ) * q ^ n / (1 - q))) * (1 + R)
            ≤ C₀ * (((κ + ε) * C * (ε + κ) * q ^ n / (1 - q))
                + ((κ + ε) * C * (ε + κ) * q ^ n / (1 - q))) * (1 + R) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hschle (by positivity)) (by linarith)
          _ = 2 * C * (((κ + ε) * C * (ε + κ) / (1 - q)) * q ^ n) := by
              rw [hC]; ring
      refine squeeze_zero (fun n => norm_nonneg _) hbound ?_
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hqpos) hq1).const_mul
        ((κ + ε) * C * (ε + κ) / (1 - q))
      have h4 : Tendsto (fun n => 2 * C * (((κ + ε) * C * (ε + κ) / (1 - q)) * q ^ n))
          atTop (𝓝 0) := by
        have h5 := h.const_mul (2 * C)
        simpa using h5
      exact h4
    have h4 : Tendsto (fun n => μ z * (1 + beurling (F n) z)) atTop
        (𝓝 (μ z * (1 + beurling Flim z))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.add h3)
    exact tendsto_nhds_unique h1 h4
  -- Flim is compactly supported
  have hFlimc : HasCompactSupport Flim := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) R) fun w hw => ?_
    have hw' : R < ‖w‖ := by
      by_contra h
      exact hw (by rw [Metric.mem_closedBall, dist_zero_right]; linarith)
    exact hFlimsupp w hw'
  -- Flim is smooth
  have hFlimsm : ContDiff ℝ ∞ Flim := by
    refine H.smoothFixed (2 * δ) α (2 * δ) R hα hα1 μ μ Flim hμs hμc ?_ hμs hμc ?_
      hFlimM hFlimK (fun z hz => hFlimsupp z hz) ?_
    · intro z; exact le_trans (hμb z) hsmoothμ
    · intro z; exact le_trans (hμb z) (by linarith [hεδ, hδpos])
    · intro z; rw [hFlim_eq z]; ring
  -- the solution
  refine ⟨cauchyT Flim, H.contDiffT Flim hFlimsm hFlimc, ?_, ?_, ?_⟩
  · intro z
    rw [H.pompeiu Flim hFlimsm hFlimc z, hFlim_eq z,
      H.beurlingDeriv Flim hFlimsm hFlimc z]
  · intro z
    rw [H.beurlingDeriv Flim hFlimsm hFlimc z]
    obtain ⟨hBM, _⟩ := H.schauder α hα hα1 Flim (2 * δ) (2 * δ) R (by linarith) hFlimM hFlimK
      hFlimsupp
    refine le_trans (hBM z) ?_
    have h2 : 0 ≤ (2 * δ) + (2 * δ) := by linarith
    calc H.schConst α * ((2 * δ) + (2 * δ)) * (1 + R) ≤ C₀ * ((2 * δ) + (2 * δ)) * (1 + R) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hschle h2) (by linarith)
      _ = 4 * q := by rw [hq, hC]; ring
      _ ≤ 1 / 4 := by linarith
  · intro z
    rw [H.pompeiu Flim hFlimsm hFlimc z]
    have h1 : δ ≤ q := by
      rw [hq, hC]
      nlinarith [hC₀ge1, hR, hδpos]
    linarith [hFlimM z, h1, hq8]

end Work.Beltrami
