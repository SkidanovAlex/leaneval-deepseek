import Mathlib
import Submission.Work.OddVolterra.WinData.J12M
import Submission.Work.OddExistence.Manifest.aw_toolkit

/-!
# The extended-box estimates for the manifest numerators `J1M`, `J2M`

This file proves `Work.OddVolterra.WinData.J12M_est_ext`: the value/derivative estimates of
`WinData/J12M.lean` (`J12M_jet_bound_box`) extended to the first slope slot running up to `3/2`
(instead of `1`), which is what `thetaM_close_box` needs when it differentiates the Abel average
`s ↦ ∫₀¹ KvecM (s + τ(σ − s))` in `s ∈ [a,b] ⊆ (0,1]`.

The proof splits on the position of the first slot `x`:

* `x ≤ 1`: the box estimate `J12M_jet_bound_box` applies with box `[a/2, 1]`.
* `x ≥ 91/100`: the bump `h` is supported in `[4/5, 9/10]`, hence `h ≡ 0` (and `h^{(k)} ≡ 0`) on
  `[91/100, 3/2]`; there the `a`-section of the radicand is the parabola
  `(line h σ t)² − (a t)²`, whose jets are explicit, and the recursion bound
  `AW.rnu_jet_bound` finishes.
-/

namespace Work.OddVolterra.WinData

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Work.OddExistence.Manifest
open Work.OddVolterra
open Work.OddVolterra.KernelExt

noncomputable section

/-! ## Vanishing of the bump above the window -/

/-- The bump is identically zero above `9/10 = 1 - τ`. -/
lemma h_eq_zero_of_gt {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) {y : ℝ}
    (hy : 9 / 10 < y) : h y = 0 := by
  by_contra hne
  have hmem := hsupp (Function.mem_support.mpr hne)
  have h1 : (1 : ℝ) - 2 * tau = 4 / 5 := by rw [tau]; norm_num
  have h2 : (1 : ℝ) - tau = 9 / 10 := by rw [tau]; norm_num
  rw [h1, h2] at hmem
  linarith [hmem.2]

/-! ## Jets of a downward parabola `y ↦ C - (y t)²` -/

/-- Jets of `y ↦ (t y)²` (a rescaled square). -/
lemma iteratedDeriv_sq_mul (t a : ℝ) (k : ℕ) :
    iteratedDeriv k (fun y : ℝ => (t * y) ^ 2) a
      = t ^ k * ((2).descFactorial k * (t * a) ^ (2 - k)) := by
  have hf : ContDiff ℝ k (fun z : ℝ => z ^ 2) := by fun_prop
  have h := iteratedDeriv_comp_const_mul (𝕜 := ℝ) (f := fun z : ℝ => z ^ 2) (n := k) hf t
  rw [show (fun y : ℝ => (t * y) ^ 2) = (fun y => (fun z : ℝ => z ^ 2) (t * y)) from rfl, h]
  simp

/-- **The jets of the parabola `y ↦ C - (y t)²`.** -/
lemma iteratedDeriv_const_sub_sq (C t a : ℝ) (k : ℕ) :
    iteratedDeriv k (fun y : ℝ => C - (y * t) ^ 2) a =
      (if k = 0 then C - (a * t) ^ 2 else if k = 1 then -(2 * (a * t) * t)
        else if k = 2 then -(2 * t ^ 2) else 0) := by
  have hfun : (fun y : ℝ => C - (y * t) ^ 2) = fun y : ℝ => C - (t * y) ^ 2 := by
    funext y; ring
  rw [hfun]
  have hsplit : (fun y : ℝ => C - (t * y) ^ 2) =
      (fun _ : ℝ => C) - (fun y : ℝ => (t * y) ^ 2) := rfl
  rw [hsplit, iteratedDeriv_sub (by fun_prop : ContDiffAt ℝ (k : ℕ) (fun _ : ℝ => C) a)
        (by fun_prop : ContDiffAt ℝ (k : ℕ) (fun y : ℝ => (t * y) ^ 2) a)]
  rw [iteratedDeriv_const, iteratedDeriv_sq_mul]
  rcases k with _ | _ | _ | k
  · simp
    ring
  · norm_num
    ring
  · norm_num
    ring
  · have h3 : ¬ (k + 1 + 1 + 1 = 0) := by omega
    have h4 : ¬ (k + 1 + 1 + 1 = 1) := by omega
    have h5 : ¬ (k + 1 + 1 + 1 = 2) := by omega
    have h7 : ((2).descFactorial (k + 1 + 1 + 1) : ℝ) = 0 := by
      have : (2).descFactorial (k + 1 + 1 + 1) = 0 := by
        rw [Nat.descFactorial_eq_zero_iff_lt]; omega
      exact_mod_cast this
    simp only [h3, h4, h5, if_false]
    rw [h7]
    ring

/-- Uniform bound for the jets of the parabola when `|C| ≤ 5`, `|a| ≤ 3/2`, `|t| ≤ 2`. -/
lemma abs_iteratedDeriv_const_sub_sq_le {C t a : ℝ} (hC : |C| ≤ 5) (ha : |a| ≤ 3 / 2)
    (ht : |t| ≤ 2) : ∀ k : ℕ, |iteratedDeriv k (fun y : ℝ => C - (y * t) ^ 2) a| ≤ 14 := by
  intro k
  rw [iteratedDeriv_const_sub_sq]
  have hat : |a * t| ≤ 3 := by rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg t]
  rcases k with _ | _ | _ | k
  · simp only [if_true]
    have h1 : |(a * t) ^ 2| ≤ 9 := by
      rw [abs_pow]
      nlinarith [abs_nonneg (a * t)]
    calc |C - (a * t) ^ 2| ≤ |C| + |(a * t) ^ 2| := abs_sub _ _
      _ ≤ 5 + 9 := add_le_add hC h1
      _ ≤ 14 := by norm_num
  · simp only [if_neg (by norm_num : ¬ ((1 : ℕ) = 0)), if_true]
    have h3 : |-(2 * (a * t) * t)| = 2 * |a * t| * |t| := by
      rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h3]
    nlinarith [abs_nonneg (a * t), abs_nonneg t]
  · simp only [if_neg (by norm_num : ¬ ((2 : ℕ) = 0)), if_neg (by norm_num : ¬ ((2 : ℕ) = 1)),
      if_true]
    have h4 : |-(2 * t ^ 2)| = 2 * |t| ^ 2 := by
      rw [abs_neg, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h4]
    nlinarith [abs_nonneg t]
  · have h3 : ¬ (k + 1 + 1 + 1 = 0) := by omega
    have h4 : ¬ (k + 1 + 1 + 1 = 1) := by omega
    have h5 : ¬ (k + 1 + 1 + 1 = 2) := by omega
    simp only [h3, h4, h5, if_false]
    norm_num

/-- Difference bound for the jets of two parabolas with close constants. -/
lemma abs_iteratedDeriv_const_sub_sq_sub_le {C1 C2 t a e : ℝ} (h : |C1 - C2| ≤ e) (k : ℕ) :
    |iteratedDeriv k (fun y : ℝ => C1 - (y * t) ^ 2) a -
      iteratedDeriv k (fun y : ℝ => C2 - (y * t) ^ 2) a| ≤ e := by
  have he : 0 ≤ e := le_trans (abs_nonneg _) h
  rw [← iteratedDeriv_sub (by fun_prop : ContDiffAt ℝ (k : ℕ) (fun y : ℝ => C1 - (y * t) ^ 2) a)
    (by fun_prop : ContDiffAt ℝ (k : ℕ) (fun y : ℝ => C2 - (y * t) ^ 2) a)]
  have hfun : (fun y : ℝ => C1 - (y * t) ^ 2) - (fun y : ℝ => C2 - (y * t) ^ 2) =
      fun _ : ℝ => C1 - C2 := by
    funext y; simp only [Pi.sub_apply]; ring
  rw [hfun, iteratedDeriv_const]
  split_ifs with hk
  · exact h
  · simpa using he

/-! ## The radicand section above the window -/

/-- Above `9/10` the `a`-section of the radicand is the parabola `(line h σ t)² - (a t)²`. -/
lemma Zrad_section_eventuallyEq {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) (σ t : ℝ) {a : ℝ}
    (ha : 9 / 10 < a) :
    (fun y : ℝ => Zrad h (y, σ, t)) =ᶠ[𝓝 a] (fun y : ℝ => (line h σ t) ^ 2 - (y * t) ^ 2) := by
  refine Filter.eventuallyEq_of_mem (Ioi_mem_nhds ha) (fun y hy => ?_)
  have hzy : h y = 0 := h_eq_zero_of_gt hsupp hy
  simp only [Zrad, line]
  rw [hzy]
  ring

/-- The unperturbed `a`-section of the radicand. -/
lemma Zrad_zero_section_eq (σ t : ℝ) :
    (fun y : ℝ => Zrad (0 : ℝ → ℝ) (y, σ, t)) = fun y : ℝ => (σ * t) ^ 2 - (y * t) ^ 2 := by
  funext y; simp [Zrad, line]

/-! ## Lifting the estimate block to a larger constant -/

/-- The estimate block is monotone in its constant (for `δ ≥ 0`). -/
lemma est_block_mono {C C' δ A B A' B' D E D' E' : ℝ} (hδ0 : 0 ≤ δ) (hCC' : C ≤ C')
    (h : (|A - B| ≤ C * δ ∧ |A' - B'| ≤ C * δ ∧ |B| ≤ C ∧ |B'| ≤ C) ∧
         (|D - E| ≤ C * δ ∧ |D' - E'| ≤ C * δ ∧ |E| ≤ C ∧ |E'| ≤ C)) :
    (|A - B| ≤ C' * δ ∧ |A' - B'| ≤ C' * δ ∧ |B| ≤ C' ∧ |B'| ≤ C') ∧
      (|D - E| ≤ C' * δ ∧ |D' - E'| ≤ C' * δ ∧ |E| ≤ C' ∧ |E'| ≤ C') := by
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7, h8⟩⟩ := h
  have hm : C * δ ≤ C' * δ := mul_le_mul_of_nonneg_right hCC' hδ0
  exact ⟨⟨le_trans h1 hm, le_trans h2 hm, le_trans h3 hCC', le_trans h4 hCC'⟩,
    ⟨le_trans h5 hm, le_trans h6 hm, le_trans h7 hCC', le_trans h8 hCC'⟩⟩


/-! ## The high-slope case `x ≥ 91/100` -/

set_option maxHeartbeats 2000000 in
/-- **The extended estimates for first slots `x ≥ 91/100`.**  There the bump vanishes, so the
`a`-section of the radicand is an explicit parabola. -/
lemma J12M_est_hi (n : ℕ) (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      ∀ x : ℝ, 91 / 100 ≤ x → x ≤ 3 / 2 → ∀ σ : ℝ, a ≤ σ → σ ≤ 1 →
      ∀ t : ℝ, 1 / 5 ≤ |t| → |t| ≤ 2 →
      ((|J1M n h x σ t - J1M n 0 x σ t| ≤ C * δ ∧
        |deriv (fun y : ℝ => J1M n h y σ t) x -
         deriv (fun y : ℝ => J1M n 0 y σ t) x| ≤ C * δ ∧
        |J1M n 0 x σ t| ≤ C ∧
        |deriv (fun y : ℝ => J1M n 0 y σ t) x| ≤ C) ∧
       (|J2M n h x σ t - J2M n 0 x σ t| ≤ C * δ ∧
        |deriv (fun y : ℝ => J2M n h y σ t) x -
         deriv (fun y : ℝ => J2M n 0 y σ t) x| ≤ C * δ ∧
        |J2M n 0 x σ t| ≤ C ∧
        |deriv (fun y : ℝ => J2M n 0 y σ t) x| ≤ C)) := by
  set MZ : ℕ → ℝ := fun _ => 14 with hMZ
  set KZ : ℕ → ℝ := fun _ => 5 with hKZ
  have hMZn : ∀ i, 0 ≤ MZ i := fun i => by rw [hMZ]; norm_num
  have hKZn : ∀ i, 0 ≤ KZ i := fun i => by rw [hKZ]; norm_num
  set C1 : ℝ := AW.jetC ((n : ℝ) + 1 / 2) MZ KZ (fun _ => 0) (fun _ => 1) (n + 1) 0 with hC1
  set C2 : ℝ := AW.jetC ((n : ℝ) + 1 / 2) MZ KZ (fun _ => 0) (fun _ => 1) (n + 1) 1 with hC2
  set C3 : ℝ := AW.jetC ((n : ℝ) - 1 / 2) MZ KZ (fun _ => 1) (fun _ => 2) n 0 with hC3
  set C4 : ℝ := AW.jetC ((n : ℝ) - 1 / 2) MZ KZ (fun _ => 1) (fun _ => 2) n 1 with hC4
  have hC1n : 0 ≤ C1 := by
    rw [hC1]
    exact AW.jetC_nonneg ((n : ℝ) + 1 / 2) MZ KZ (fun _ => 0) (fun _ => 1) hMZn hKZn
      (fun _ => le_refl 0) (fun _ => zero_le_one) (n + 1) 0
  have hC2n : 0 ≤ C2 := by
    rw [hC2]
    exact AW.jetC_nonneg ((n : ℝ) + 1 / 2) MZ KZ (fun _ => 0) (fun _ => 1) hMZn hKZn
      (fun _ => le_refl 0) (fun _ => zero_le_one) (n + 1) 1
  have hC3n : 0 ≤ C3 := by
    rw [hC3]
    exact AW.jetC_nonneg ((n : ℝ) - 1 / 2) MZ KZ (fun _ => 1) (fun _ => 2) hMZn hKZn
      (fun _ => zero_le_one) (fun _ => by norm_num) n 0
  have hC4n : 0 ≤ C4 := by
    rw [hC4]
    exact AW.jetC_nonneg ((n : ℝ) - 1 / 2) MZ KZ (fun _ => 1) (fun _ => 2) hMZn hKZn
      (fun _ => zero_le_one) (fun _ => by norm_num) n 1
  refine ⟨max (max C1 C2) (max C3 C4) + 1, ?_, ?_⟩
  · have : (0 : ℝ) ≤ max (max C1 C2) (max C3 C4) :=
      le_trans hC1n (le_max_of_le_left (le_max_left _ _))
    linarith
  · intro h δ hh hδ hδ100 hjet hsupp x hx_hi hx2 σ hσ1 hσ2 t ht1 ht2
    have hδ0 : 0 ≤ δ := le_of_lt hδ
    have hδ1' : δ ≤ 1 := le_trans hδ100 (by norm_num)
    have hσ0 : 0 < σ := lt_of_lt_of_le ha hσ1
    have hσabs : |σ| ≤ 1 := by rw [abs_of_nonneg hσ0.le]; exact hσ2
    have hh0 : |h σ| ≤ δ := by simpa using hjet 0 (by omega) σ
    have hσt : |σ * t| ≤ 2 := by rw [abs_mul]; nlinarith [abs_nonneg σ, abs_nonneg t]
    have hline : |line h σ t| ≤ 21 / 10 := by
      calc |line h σ t| = |σ * t + h σ| := rfl
        _ ≤ |σ * t| + |h σ| := abs_add_le _ _
        _ ≤ 2 + 1 / 100 := add_le_add hσt (le_trans hh0 hδ100)
        _ ≤ 21 / 10 := by norm_num
    have hC1f : |(line h σ t) ^ 2| ≤ 5 := by
      rw [abs_pow]
      nlinarith [abs_nonneg (line h σ t)]
    have hC2f : |(σ * t) ^ 2| ≤ 5 := by
      rw [abs_pow]
      nlinarith [abs_nonneg (σ * t)]
    have hxmem : x ∈ Set.Icc (91 / 100 : ℝ) (3 / 2) := ⟨hx_hi, hx2⟩
    have hamin : ∀ a' ∈ Set.Icc (91 / 100 : ℝ) (3 / 2), |a'| ≤ 3 / 2 ∧ 9 / 10 < a' := by
      intro a' ha'
      exact ⟨by rw [abs_of_nonneg (by linarith [ha'.1])]; exact ha'.2, by linarith [ha'.1]⟩
    have hZh : ∀ i, i ≤ n + 2 → ∀ a' ∈ Set.Icc (91 / 100 : ℝ) (3 / 2),
        |iteratedDeriv i (fun y : ℝ => Zrad h (y, σ, t)) a'| ≤ MZ i + 2 * KZ i := by
      intro i hi a' ha'
      obtain ⟨ha'abs, ha'90⟩ := hamin a' ha'
      rw [(Zrad_section_eventuallyEq hsupp σ t ha'90).iteratedDeriv_eq i]
      have h1 := abs_iteratedDeriv_const_sub_sq_le hC1f ha'abs ht2 i
      rw [hMZ, hKZ]
      dsimp only
      linarith
    have hZd : ∀ i, i ≤ n + 2 → ∀ a' ∈ Set.Icc (91 / 100 : ℝ) (3 / 2),
        |iteratedDeriv i (fun y : ℝ => Zrad h (y, σ, t)) a' -
         iteratedDeriv i (fun y : ℝ => Zrad 0 (y, σ, t)) a'| ≤ KZ i * δ := by
      intro i hi a' ha'
      obtain ⟨ha'abs, ha'90⟩ := hamin a' ha'
      rw [(Zrad_section_eventuallyEq hsupp σ t ha'90).iteratedDeriv_eq i, Zrad_zero_section_eq σ t]
      have hkey : |(line h σ t) ^ 2 - (σ * t) ^ 2| ≤ 5 * δ := by
        have hfac : (line h σ t) ^ 2 - (σ * t) ^ 2 = h σ * (line h σ t + σ * t) := by
          unfold line; ring
        rw [hfac, abs_mul]
        have hsum : |line h σ t + σ * t| ≤ 21 / 10 + 2 :=
          le_trans (abs_add_le _ _) (add_le_add hline hσt)
        calc |h σ| * |line h σ t + σ * t| ≤ δ * 5 :=
              mul_le_mul hh0 (by linarith) (abs_nonneg _) hδ0
          _ = 5 * δ := by ring
      have h2 := abs_iteratedDeriv_const_sub_sq_sub_le (t := t) (a := a') hkey i
      rw [hKZ]
      dsimp only
      exact h2
    have hZ0 : ∀ i, i ≤ n + 2 → ∀ a' ∈ Set.Icc (91 / 100 : ℝ) (3 / 2),
        |iteratedDeriv i (fun y : ℝ => Zrad 0 (y, σ, t)) a'| ≤ MZ i := by
      intro i hi a' ha'
      obtain ⟨ha'abs, ha'90⟩ := hamin a' ha'
      rw [Zrad_zero_section_eq σ t]
      have h1 := abs_iteratedDeriv_const_sub_sq_le hC2f ha'abs ht2 i
      rw [hMZ]
      dsimp only
      linarith
    have hI1d : ∀ j, j ≤ n + 2 → ∀ a' ∈ Set.Icc (91 / 100 : ℝ) (3 / 2),
        |iteratedDeriv j (fun a : ℝ => (fun _ : ℝ × ℝ × ℝ => (1 : ℝ)) (a, σ, t)) a' -
         iteratedDeriv j (fun a : ℝ => (fun _ : ℝ × ℝ × ℝ => (1 : ℝ)) (a, σ, t)) a'|
          ≤ (0 : ℝ) * δ := fun j hj a' ha' => by simp
    have hI10 : ∀ j, j ≤ n + 2 → ∀ a' ∈ Set.Icc (91 / 100 : ℝ) (3 / 2),
        |iteratedDeriv j (fun a : ℝ => (fun _ : ℝ × ℝ × ℝ => (1 : ℝ)) (a, σ, t)) a'| ≤ (1 : ℝ) := by
      intro j hj a' ha'
      rw [show (fun a : ℝ => (fun _ : ℝ × ℝ × ℝ => (1 : ℝ)) (a, σ, t)) = fun _ : ℝ => (1 : ℝ)
        from rfl, iteratedDeriv_const]
      split_ifs <;> norm_num
    have hlin1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2) := by
      unfold lineSlope; fun_prop
    have hlin0 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × ℝ => lineSlope (0 : ℝ → ℝ) p.1 p.2.2) := by
      have hzero : (fun p : ℝ × ℝ × ℝ => lineSlope (0 : ℝ → ℝ) p.1 p.2.2) = fun p => p.2.2 := by
        funext p; simp [lineSlope]
      rw [hzero]; fun_prop
    have hls1 : ContDiff ℝ (⊤ : ℕ∞) (fun a : ℝ => lineSlope h a t) := by
      unfold lineSlope; fun_prop
    have hls0 : ContDiff ℝ (⊤ : ℕ∞) (fun a : ℝ => lineSlope (0 : ℝ → ℝ) a t) := by
      have hzero : (fun a : ℝ => lineSlope (0 : ℝ → ℝ) a t) = fun _ : ℝ => t := by
        funext a; simp [lineSlope]
      rw [hzero]; fun_prop
    have hI2d : ∀ j, j ≤ n + 1 → ∀ a' ∈ Set.Icc (91 / 100 : ℝ) (3 / 2),
        |iteratedDeriv j (fun a : ℝ => lineSlope h a t) a' -
         iteratedDeriv j (fun a : ℝ => lineSlope (0 : ℝ → ℝ) a t) a'| ≤ (1 : ℝ) * δ := by
      intro j hj a' ha'
      have he : (fun a : ℝ => lineSlope h a t) - (fun a : ℝ => lineSlope (0 : ℝ → ℝ) a t)
          = fun a : ℝ => deriv h a := by
        funext y; simp [lineSlope]
      rw [← iteratedDeriv_sub (hls1.contDiffAt.of_le (AW.natCast_le_top_enat j))
          (hls0.contDiffAt.of_le (AW.natCast_le_top_enat j)), he]
      rw [← iteratedDeriv_succ' (f := h) (n := j)]
      have h1 := hjet (j + 1) (by omega) a'
      linarith
    have hI20 : ∀ j, j ≤ n + 1 → ∀ a' ∈ Set.Icc (91 / 100 : ℝ) (3 / 2),
        |iteratedDeriv j (fun a : ℝ => lineSlope (0 : ℝ → ℝ) a t) a'| ≤ (2 : ℝ) := by
      intro j hj a' ha'
      have heq : (fun a : ℝ => lineSlope (0 : ℝ → ℝ) a t) = fun _ : ℝ => t := by
        funext a; simp [lineSlope]
      rw [heq, iteratedDeriv_const]
      split_ifs with h0
      · simpa using ht2
      · norm_num
    have hJ1_0 := AW.rnu_jet_bound ((n : ℝ) + 1 / 2) (n + 1) (91 / 100) (3 / 2) KZ MZ
        (fun _ => 0) (fun _ => 1) hKZn hMZn (fun _ => le_refl 0) (fun _ => zero_le_one)
        h (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) hh contDiff_const contDiff_const
        σ t δ hδ0 hδ1' hZh hZd hZ0 hI1d hI10 (n + 1) 0 (by omega) x hxmem
    have hJ1_1 := AW.rnu_jet_bound ((n : ℝ) + 1 / 2) (n + 1) (91 / 100) (3 / 2) KZ MZ
        (fun _ => 0) (fun _ => 1) hKZn hMZn (fun _ => le_refl 0) (fun _ => zero_le_one)
        h (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) hh contDiff_const contDiff_const
        σ t δ hδ0 hδ1' hZh hZd hZ0 hI1d hI10 (n + 1) 1 (by omega) x hxmem
    have hJ2_0 := AW.rnu_jet_bound ((n : ℝ) - 1 / 2) n (91 / 100) (3 / 2) KZ MZ
        (fun _ => 1) (fun _ => 2) hKZn hMZn (fun _ => zero_le_one) (fun _ => by norm_num)
        h (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2)
        (fun p : ℝ × ℝ × ℝ => lineSlope (0 : ℝ → ℝ) p.1 p.2.2) hh hlin1 hlin0
        σ t δ hδ0 hδ1'
        (fun i hi a' ha' => hZh i (by omega) a' ha') (fun i hi a' ha' => hZd i (by omega) a' ha')
        (fun i hi a' ha' => hZ0 i (by omega) a' ha')
        (fun j hj a' ha' => hI2d j (by omega) a' ha') (fun j hj a' ha' => hI20 j (by omega) a' ha')
        n 0 (by omega) x hxmem
    have hJ2_1 := AW.rnu_jet_bound ((n : ℝ) - 1 / 2) n (91 / 100) (3 / 2) KZ MZ
        (fun _ => 1) (fun _ => 2) hKZn hMZn (fun _ => zero_le_one) (fun _ => by norm_num)
        h (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2)
        (fun p : ℝ × ℝ × ℝ => lineSlope (0 : ℝ → ℝ) p.1 p.2.2) hh hlin1 hlin0
        σ t δ hδ0 hδ1'
        (fun i hi a' ha' => hZh i (by omega) a' ha') (fun i hi a' ha' => hZd i (by omega) a' ha')
        (fun i hi a' ha' => hZ0 i (by omega) a' ha')
        (fun j hj a' ha' => hI2d j (by omega) a' ha') (fun j hj a' ha' => hI20 j (by omega) a' ha')
        n 1 (by omega) x hxmem
    have hJ1M_h (y : ℝ) : J1M n h y σ t = iteratedDeriv 0
        (fun a : ℝ => Rnu ((n : ℝ) + 1 / 2) h (fun _ => (1 : ℝ)) (n + 1) (a, σ, t)) y := rfl
    have hJ1M_0 (y : ℝ) : J1M n 0 y σ t = iteratedDeriv 0
        (fun a : ℝ => Rnu ((n : ℝ) + 1 / 2) 0 (fun _ => (1 : ℝ)) (n + 1) (a, σ, t)) y := rfl
    have hJ2M_h (y : ℝ) : J2M n h y σ t = iteratedDeriv 0
        (fun a : ℝ => Rnu ((n : ℝ) - 1 / 2) h (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2) n
          (a, σ, t)) y := rfl
    have hJ2M_0 (y : ℝ) : J2M n 0 y σ t = iteratedDeriv 0
        (fun a : ℝ => Rnu ((n : ℝ) - 1 / 2) 0 (fun p : ℝ × ℝ × ℝ => lineSlope (0 : ℝ → ℝ) p.1 p.2.2) n
          (a, σ, t)) y := rfl
    have hd1 : deriv (fun y : ℝ => J1M n h y σ t) x = iteratedDeriv 1
        (fun a : ℝ => Rnu ((n : ℝ) + 1 / 2) h (fun _ => (1 : ℝ)) (n + 1) (a, σ, t)) x := by
      rw [iteratedDeriv_one]; simp only [J1M]
    have hd2 : deriv (fun y : ℝ => J1M n 0 y σ t) x = iteratedDeriv 1
        (fun a : ℝ => Rnu ((n : ℝ) + 1 / 2) 0 (fun _ => (1 : ℝ)) (n + 1) (a, σ, t)) x := by
      rw [iteratedDeriv_one]; simp only [J1M]
    have hd3 : deriv (fun y : ℝ => J2M n h y σ t) x = iteratedDeriv 1
        (fun a : ℝ => Rnu ((n : ℝ) - 1 / 2) h (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2) n
          (a, σ, t)) x := by
      rw [iteratedDeriv_one]; simp only [J2M]
    have hd4 : deriv (fun y : ℝ => J2M n 0 y σ t) x = iteratedDeriv 1
        (fun a : ℝ => Rnu ((n : ℝ) - 1 / 2) 0 (fun p : ℝ × ℝ × ℝ => lineSlope (0 : ℝ → ℝ) p.1 p.2.2) n
          (a, σ, t)) x := by
      rw [iteratedDeriv_one]; simp only [J2M]
    have hC1le : C1 ≤ max (max C1 C2) (max C3 C4) + 1 := by
      have h : C1 ≤ max (max C1 C2) (max C3 C4) :=
        le_trans (le_max_left C1 C2) (le_max_left (max C1 C2) (max C3 C4))
      linarith
    have hC2le : C2 ≤ max (max C1 C2) (max C3 C4) + 1 := by
      have h : C2 ≤ max (max C1 C2) (max C3 C4) :=
        le_trans (le_max_right C1 C2) (le_max_left (max C1 C2) (max C3 C4))
      linarith
    have hC3le : C3 ≤ max (max C1 C2) (max C3 C4) + 1 := by
      have h : C3 ≤ max (max C1 C2) (max C3 C4) :=
        le_trans (le_max_left C3 C4) (le_max_right (max C1 C2) (max C3 C4))
      linarith
    have hC4le : C4 ≤ max (max C1 C2) (max C3 C4) + 1 := by
      have h : C4 ≤ max (max C1 C2) (max C3 C4) :=
        le_trans (le_max_right C3 C4) (le_max_right (max C1 C2) (max C3 C4))
      linarith
    have hb1 : AW.jetC ((n : ℝ) + 1 / 2) MZ KZ (fun _ => 0) (fun _ => 1) (n + 1) 0 * δ
        ≤ (max (max C1 C2) (max C3 C4) + 1) * δ := by
      rw [← hC1]; exact mul_le_mul_of_nonneg_right hC1le hδ0
    have hb2 : AW.jetC ((n : ℝ) + 1 / 2) MZ KZ (fun _ => 0) (fun _ => 1) (n + 1) 1 * δ
        ≤ (max (max C1 C2) (max C3 C4) + 1) * δ := by
      rw [← hC2]; exact mul_le_mul_of_nonneg_right hC2le hδ0
    have hb3 : AW.jetC ((n : ℝ) - 1 / 2) MZ KZ (fun _ => 1) (fun _ => 2) n 0 * δ
        ≤ (max (max C1 C2) (max C3 C4) + 1) * δ := by
      rw [← hC3]; exact mul_le_mul_of_nonneg_right hC3le hδ0
    have hb4 : AW.jetC ((n : ℝ) - 1 / 2) MZ KZ (fun _ => 1) (fun _ => 2) n 1 * δ
        ≤ (max (max C1 C2) (max C3 C4) + 1) * δ := by
      rw [← hC4]; exact mul_le_mul_of_nonneg_right hC4le hδ0
    have hv1 : AW.jetC ((n : ℝ) + 1 / 2) MZ KZ (fun _ => 0) (fun _ => 1) (n + 1) 0
        ≤ max (max C1 C2) (max C3 C4) + 1 := by rw [← hC1]; exact hC1le
    have hv2 : AW.jetC ((n : ℝ) + 1 / 2) MZ KZ (fun _ => 0) (fun _ => 1) (n + 1) 1
        ≤ max (max C1 C2) (max C3 C4) + 1 := by rw [← hC2]; exact hC2le
    have hv3 : AW.jetC ((n : ℝ) - 1 / 2) MZ KZ (fun _ => 1) (fun _ => 2) n 0
        ≤ max (max C1 C2) (max C3 C4) + 1 := by rw [← hC3]; exact hC3le
    have hv4 : AW.jetC ((n : ℝ) - 1 / 2) MZ KZ (fun _ => 1) (fun _ => 2) n 1
        ≤ max (max C1 C2) (max C3 C4) + 1 := by rw [← hC4]; exact hC4le
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [hJ1M_h x, hJ1M_0 x]; exact le_trans hJ1_0.1 hb1
    · rw [hd1, hd2]; exact le_trans hJ1_1.1 hb2
    · rw [hJ1M_0 x]; exact le_trans hJ1_0.2 hv1
    · rw [hd2]; exact le_trans hJ1_1.2 hv2
    · rw [hJ2M_h x, hJ2M_0 x]; exact le_trans hJ2_0.1 hb3
    · rw [hd3, hd4]; exact le_trans hJ2_1.1 hb4
    · rw [hJ2M_0 x]; exact le_trans hJ2_0.2 hv3
    · rw [hd4]; exact le_trans hJ2_1.2 hv4


/-! ## The target estimate -/

theorem J12M_est_ext (n : ℕ) (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      ∀ x : ℝ, 3 * a / 4 ≤ x → x ≤ 3 / 2 → ∀ σ : ℝ, a ≤ σ → σ ≤ 1 →
      ∀ t : ℝ, 1 / 5 ≤ |t| → |t| ≤ 2 →
      ((|Work.OddVolterra.KernelExt.J1M n h x σ t - Work.OddVolterra.KernelExt.J1M n 0 x σ t| ≤ C * δ ∧
        |deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J1M n h y σ t) x -
         deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J1M n 0 y σ t) x| ≤ C * δ ∧
        |Work.OddVolterra.KernelExt.J1M n 0 x σ t| ≤ C ∧
        |deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J1M n 0 y σ t) x| ≤ C) ∧
       (|Work.OddVolterra.KernelExt.J2M n h x σ t - Work.OddVolterra.KernelExt.J2M n 0 x σ t| ≤ C * δ ∧
        |deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J2M n h y σ t) x -
         deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J2M n 0 y σ t) x| ≤ C * δ ∧
        |Work.OddVolterra.KernelExt.J2M n 0 x σ t| ≤ C ∧
        |deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J2M n 0 y σ t) x| ≤ C)) := by
  by_cases ha2 : a ≤ 2
  · obtain ⟨K1, hK1pos, hK1⟩ := J12M_jet_bound_box n hn (a := a / 2) (b := 1)
      (by linarith) (by linarith) le_rfl
    obtain ⟨K2, hK2pos, hK2⟩ := J12M_est_hi n hn ha
    refine ⟨max K1 K2, lt_max_of_lt_left hK1pos, ?_⟩
    intro h δ hh hδ hδ100 hjet hsupp x hx1 hx2 σ hσ1 hσ2 t ht1 ht2
    rcases le_or_gt x 1 with hxle | hxgt
    · have hxm : x ∈ Set.Icc (a / 2) 1 := ⟨by linarith, hxle⟩
      have hσm : σ ∈ Set.Icc (a / 2) 1 := ⟨by linarith, hσ2⟩
      exact est_block_mono hδ.le (le_max_left _ _)
        (hK1 h δ hh hδ hδ100 hjet x hxm σ hσm t ht1 ht2)
    · exact est_block_mono hδ.le (le_max_right _ _)
        (hK2 h δ hh hδ hδ100 hjet hsupp x (by linarith) hx2 σ hσ1 hσ2 t ht1 ht2)
  · refine ⟨1, one_pos, ?_⟩
    intro h δ hh hδ hδ100 hjet hsupp x hx1 hx2 σ hσ1 hσ2 t ht1 ht2
    exfalso
    have ha3 : 2 < a := not_le.mp ha2
    linarith

end

end Work.OddVolterra.WinData
