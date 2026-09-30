import Mathlib
import Submission.Work.BMF.mr_direct.halasz_twisted
import Submission.Work.BMF.mr_direct.abel_inv_bound
import Submission.Work.BMF.mr_direct.twist_dist
import Submission.Work.BMF.mr_direct.window_abel_prefix
import Submission.Work.BMF.mr_direct.window_M_le
import Submission.Work.BMF.mr_direct.window_arith
import Submission.Work.BMF.mr_direct.window_reindex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The twisted Halász bound on the window `[X, 2X]`

`Work.BMF.mr_direct.halasz_window_twist`: there is a constant `C > 0` such that for every
`1`-bounded multiplicative `f` with `f 1 = 1`, every `X ≥ 16`, `M₀ > 0`, `T₀ ≥ 1` and `|t| ≤ 2T₀`,
if `f` is `M₀`-far from every twist `n ↦ n^{iw}`, `|w| ≤ 4T₀`, at every scale
`y ∈ [X/4, 4X]`, then

`‖Σ_{X ≤ m ≤ 2X} f m · m^{-(1+it)}‖ ≤ C ((1+M₀) e^{-M₀} + 1/√T₀)`.

**Route.**  The twisted Halász theorem (`halasz_twisted`) bounds the *prefix* sums
`Σ_{n ≤ y} f n · n^{-it}` by `C_h y ((1+M_y) e^{-M_y} + 1/√T₀)`, where
`M_y = ⨅_{|u| ≤ 2T₀} 𝔻(f, n ↦ n^{i(t+u)}; y)²`.  The hypothesis that `f` is `M₀`-far from every
twist with `|w| ≤ 4T₀` gives `M_y ≥ M₀` for every scale of interest (since
`|t+u| ≤ |t| + |u| ≤ 4T₀`), and `x ↦ (1+x)e^{-x}` is antitone on `[0,∞)`, so the bracket may be
replaced by `(1+M₀)e^{-M₀}` (`window_M_le`).  Abel summation with the weight `1/n`
(`window_abel_prefix`, a corollary of `abel_inv_bound`) then converts the prefix bounds on
`[⌈X⌉-1, ⌊2X⌋]` into the weighted window bound with a factor `K(M+N)(1/M + 1/(N+1))`, which is at
most `6K` (`window_arith`); finally `window_reindex` identifies
`Σ_{m ∈ natIcc X (2X)} f m · m^{-(1+it)}` with the Abel sum, using
`m^{-(1+it)} = m^{-1} · m^{-it}`.
-/

namespace Work.BMF.mr_direct

open BoundedMultiplicativeFunctions
open scoped BigOperators

theorem halasz_window_twist :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ) (X M₀ T₀ t : ℝ),
      f 1 = 1 → (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) →
      (∀ n, ‖f n‖ ≤ 1) → 16 ≤ X → 0 < M₀ → 1 ≤ T₀ → |t| ≤ 2 * T₀ →
      (∀ y : ℝ, X / 4 ≤ y → y ≤ 4 * X → ∀ w : ℝ, |w| ≤ 4 * T₀ →
        M₀ ≤ BoundedMultiplicativeFunctions.𝔻 f (fun n ↦ (n : ℂ) ^ (Complex.I * w)) y ^ 2) →
      ‖∑ m ∈ Work.BMF.natIcc X (2 * X), f m * (m : ℂ) ^ (-(1 + Complex.I * t))‖
        ≤ C * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀) := by
  obtain ⟨Ch, hChpos, hH⟩ := halasz_twisted
  refine ⟨6 * Ch, by positivity, ?_⟩
  intro f X M₀ T₀ t hf1 hfmult hfb hX hM₀ hT₀ ht hD
  have hXpos : 0 < X := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  -- the constant `K` multiplying the prefix bounds
  set K : ℝ := Ch * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀) with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    have h1 : 0 < Real.exp (-M₀) := Real.exp_pos _
    have h2 : 0 < 1 + M₀ := by linarith
    have h3 : 0 < Real.sqrt T₀ := Real.sqrt_pos.mpr (by linarith)
    positivity
  -- the window `Ioc N M` is `ℕ ∩ [X, 2X]`
  set N : ℕ := ⌈X⌉₊ - 1 with hNdef
  set M : ℕ := ⌊2 * X⌋₊ with hMdef
  have hceilge : 16 ≤ ⌈X⌉₊ := by
    have h : ((16 : ℕ) : ℝ) ≤ ((⌈X⌉₊ : ℕ) : ℝ) := le_trans hX (Nat.le_ceil X)
    exact_mod_cast h
  have hceil1 : 1 ≤ ⌈X⌉₊ := le_trans (by norm_num) hceilge
  have hN1 : 1 ≤ N := by rw [hNdef]; omega
  have hNcast : ((N : ℕ) : ℝ) = ((⌈X⌉₊ : ℕ) : ℝ) - 1 := by
    rw [hNdef, Nat.cast_sub hceil1, Nat.cast_one]
  have hNsuc : N + 1 = ⌈X⌉₊ := by rw [hNdef]; omega
  have hceilR : ((⌈X⌉₊ : ℕ) : ℝ) < X + 1 := Nat.ceil_lt_add_one (le_of_lt hXpos)
  have hfloorR : 2 * X < ((⌊2 * X⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one (2 * X)
  have hfloorLe : ((⌊2 * X⌋₊ : ℕ) : ℝ) ≤ 2 * X := Nat.floor_le (by linarith)
  have hle_ceil_floor : ⌈X⌉₊ ≤ ⌊2 * X⌋₊ := by
    have h : ((⌈X⌉₊ : ℕ) : ℝ) < ((⌊2 * X⌋₊ : ℕ) : ℝ) := by linarith
    exact_mod_cast le_of_lt h
  have hNM : N < M := by
    rw [hNdef, hMdef]
    calc ⌈X⌉₊ - 1 < ⌈X⌉₊ := Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one hceil1) (by norm_num)
      _ ≤ ⌊2 * X⌋₊ := hle_ceil_floor
  -- Halász on every prefix in the window
  have hpref : ∀ k : ℕ, N ≤ k → k ≤ M →
      ‖∑ j ∈ Finset.Icc 1 k, f j * (j : ℂ) ^ (-(Complex.I * t))‖ ≤ K * (k : ℝ) := by
    intro k hNk hkM
    have hkR : ((N : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hNk
    have hkMR : (k : ℝ) ≤ ((M : ℕ) : ℝ) := by exact_mod_cast hkM
    have hkX4 : X / 4 ≤ (k : ℝ) := by
      rw [hNcast] at hkR
      have hc : X ≤ ((⌈X⌉₊ : ℕ) : ℝ) := Nat.le_ceil X
      linarith
    have hk4X : (k : ℝ) ≤ 4 * X := by
      rw [hMdef] at hkMR
      linarith [hfloorLe]
    have hk2 : 2 ≤ (k : ℝ) := by
      have hk1 : 1 ≤ k := le_trans hN1 hNk
      have h : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      linarith
    have hhal := hH f hf1 hfmult hfb (k : ℝ) T₀ t hk2 hT₀
    dsimp only at hhal
    rw [Nat.floor_natCast] at hhal
    -- the infimum occurring in Halász's bound
    set Mk : ℝ := ⨅ (u : {u : ℝ // |u| ≤ 2 * T₀}),
        BoundedMultiplicativeFunctions.𝔻 f
          (fun n ↦ (n : ℂ) ^ (Complex.I * (t + u.1))) (k : ℝ) ^ 2 with hMkdef
    have hb : (1 + Mk) * Real.exp (-Mk) ≤ (1 + M₀) * Real.exp (-M₀) := by
      rw [hMkdef]
      exact window_M_le f M₀ T₀ t (k : ℝ) hM₀ ht (fun w hw => hD (k : ℝ) hkX4 hk4X w hw)
    calc ‖∑ j ∈ Finset.Icc 1 k, f j * (j : ℂ) ^ (-(Complex.I * t))‖
        ≤ Ch * (k : ℝ) * ((1 + Mk) * Real.exp (-Mk) + 1 / Real.sqrt T₀) := hhal
      _ ≤ Ch * (k : ℝ) * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ = K * (k : ℝ) := by rw [hKdef]; ring
  have habel := window_abel_prefix (fun j : ℕ => f j * (j : ℂ) ^ (-(Complex.I * t)))
    K N M hKnn hN1 hNM hpref
  calc ‖∑ m ∈ Work.BMF.natIcc X (2 * X), f m * (m : ℂ) ^ (-(1 + Complex.I * t))‖
      = ‖∑ n ∈ Finset.Ioc N M,
            (((n : ℝ))⁻¹ : ℂ) * (f n * (n : ℂ) ^ (-(Complex.I * t)))‖ := by
        rw [window_reindex f X t hX, hNdef, hMdef]
    _ ≤ K * ((M : ℝ) + (N : ℝ)) * (1 / (M : ℝ) + 1 / ((N + 1 : ℕ) : ℝ)) := habel
    _ = K * (((⌊2 * X⌋₊ : ℕ) : ℝ) + (((⌈X⌉₊ : ℕ) : ℝ) - 1)) *
          (1 / (((⌊2 * X⌋₊ : ℕ) : ℝ)) + 1 / (((⌈X⌉₊ : ℕ) : ℝ))) := by
        rw [hNcast, hMdef, hNsuc]
    _ ≤ 6 * K := window_arith X K hX hKnn
    _ = 6 * Ch * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀) := by rw [hKdef]; ring

end Work.BMF.mr_direct
