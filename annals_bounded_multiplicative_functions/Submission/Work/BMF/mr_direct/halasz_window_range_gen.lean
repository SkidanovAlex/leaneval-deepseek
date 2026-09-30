import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.mr_direct.halasz_window_twist
import Submission.Work.BMF.mr_direct.halasz_twisted
import Submission.Work.BMF.mr_direct.window_abel_prefix
import Submission.Work.BMF.mr_direct.window_M_le
import Submission.Work.BMF.mr_direct.window_arith_ratio

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- **Reindexing identity for a general integer window.**  The sum over `ℕ ∩ [X₁, X₂]` of
`f m * m^{-(1+it)}` equals the sum over `Ioc (⌈X₁⌉₊ - 1) ⌊X₂⌋₊` of `n^{-1} * (f n * n^{-it})`.
This is the range variant of `Work.BMF.mr_direct.window_reindex` with `2 * X ↦ X₂`; the two
index sets agree because `1 ≤ ⌈X₁⌉₊` for `X₁ ≥ 16` (so `⌈X₁⌉₊ - 1 < n ↔ ⌈X₁⌉₊ ≤ n`), and the
summands agree because `n^{-(1+it)} = n^{-1} * n^{-it}` for `n ≠ 0`.  No hypothesis relating
`X₁` and `X₂` is needed: when `⌈X₁⌉₊ > ⌊X₂⌋₊` both sides are the empty sum. -/
theorem window_reindex_range_gen_aux (f : ℕ → ℂ) (X₁ X₂ t : ℝ) (hX : 16 ≤ X₁) :
    ∑ m ∈ Work.BMF.natIcc X₁ X₂, f m * (m : ℂ) ^ (-(1 + Complex.I * t))
      = ∑ n ∈ Finset.Ioc (⌈X₁⌉₊ - 1) ⌊X₂⌋₊,
          (((n : ℝ))⁻¹ : ℂ) * (f n * (n : ℂ) ^ (-(Complex.I * t))) := by
  have hXpos : (0 : ℝ) < X₁ := by linarith
  have hceil : 1 ≤ ⌈X₁⌉₊ := Nat.ceil_pos.mpr hXpos
  rw [Work.BMF.natIcc]
  refine Finset.sum_congr ?_ ?_
  · ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  · intro n hn
    have hnne : n ≠ 0 := by
      simp only [Finset.mem_Ioc] at hn
      omega
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hnne
    have hsplit : (n : ℂ) ^ (-(1 + Complex.I * t))
        = (n : ℂ) ^ (-1 : ℂ) * (n : ℂ) ^ (-(Complex.I * t)) := by
      rw [show -(1 + Complex.I * t) = (-1 : ℂ) + (-(Complex.I * t)) by ring]
      exact Complex.cpow_add _ _ hn0
    rw [hsplit, Complex.cpow_neg_one]
    push_cast
    ring

/-- **Halász's result on an arbitrary integer window `[X₁,X₂]`.** General-range form of `Work.BMF.mr_direct.halasz_window_twist` (there `X₁ = X`, `X₂ = 2X`): the bound carries the factor `X₂/X₁`, so no bound on the ratio is needed.

For a `1`-bounded multiplicative `f` with `f 1 = 1`, `16 ≤ X₁ ≤ X₂`, `M₀ > 0`, `T₀ ≥ 1` and `|t| ≤ 2 T₀`: if `f` is `M₀`-far from every twist `n ↦ n^{iw}`, `|w| ≤ 4T₀`, at every scale `y ∈ [X₁/4, X₂]`, then
`‖Σ_{m ∈ ℕ∩[X₁,X₂]} f m · m^{-(1+it)}‖ ≤ C (X₂/X₁) ((1+M₀) e^{-M₀} + 1/√T₀)`.

Route to follow (mirror `Submission/Work/BMF/mr_direct/halasz_window_twist.lean`, whose proof is the special case `X₁ = X`, `X₂ = 2X`): `halasz_twisted` gives the prefix bound `‖Σ_{n ≤ k} f n n^{-it}‖ ≤ C_h k φ` for every `k ∈ [⌈X₁⌉₊-1, ⌊X₂⌋]` (with `M_k = ⨅_{|u| ≤ 2T₀} 𝔻(f, n ↦ n^{i(t+u)}; k)² ≥ M₀` by the hypothesis since `|t+u| ≤ 4T₀`, then `window_M_le` replaces the bracket by `(1+M₀)e^{-M₀}`); every such `k` satisfies `X₁/4 ≤ k ≤ X₂` because `⌈X₁⌉₊ - 1 ≥ X₁ - 1 ≥ X₁/4` for `X₁ ≥ 16` and `⌊X₂⌋ ≤ X₂`, so the tight hypothesis range `[X₁/4, X₂]` is exactly what is used. Abel summation with weight `1/n` (`window_abel_prefix` with `N = ⌈X₁⌉₊ - 1`, `M = ⌊X₂⌋₊`) gives `K (M+N)(1/M + 1/(N+1))` with `K = C_h φ`, and with `R = X₂/X₁ ≥ 1`, `b = ⌈X₁⌉₊`, `a = ⌊X₂⌋₊` one has `(a + b - 1)(1/a + 1/b) = 2 + (b-1)/a + (a-1)/b ≤ 2 + 2/R + R ≤ 5R` (using `b-1 ≤ X₁`, `a ≥ X₂ - 1 ≥ X₂/2`, `a-1 < X₂`, `b ≥ X₁`), so `C = 6 C_h` works. The reindexing `Σ_{m ∈ Icc ⌈X₁⌉₊ ⌊X₂⌋₊} f m m^{-(1+it)} = Σ_{n ∈ Ioc (⌈X₁⌉₊-1) ⌊X₂⌋₊} n^{-1}(f n n^{-it})` is an easy range variant of `window_reindex` (copy its proof with `2*X ↦ X₂`). If `⌈X₁⌉₊ > ⌊X₂⌋₊` (i.e. `N ≥ M`) the window `natIcc X₁ X₂` is empty and the bound is `0 ≤ C (X₂/X₁) φ` (the right side is positive since `C > 0`, `X₂/X₁ > 0`, `φ > 0`). -/
theorem halasz_window_range_gen :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ) (X₁ X₂ M₀ T₀ t : ℝ),
      f 1 = 1 → (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) →
      (∀ n, ‖f n‖ ≤ 1) → 16 ≤ X₁ → X₁ ≤ X₂ → 0 < M₀ → 1 ≤ T₀ → |t| ≤ 2 * T₀ →
      (∀ y : ℝ, X₁ / 4 ≤ y → y ≤ X₂ → ∀ w : ℝ, |w| ≤ 4 * T₀ →
        M₀ ≤ BoundedMultiplicativeFunctions.𝔻 f (fun n ↦ (n : ℂ) ^ (Complex.I * w)) y ^ 2) →
      ‖∑ m ∈ Work.BMF.natIcc X₁ X₂, f m * (m : ℂ) ^ (-(1 + Complex.I * t))‖
        ≤ C * (X₂ / X₁) * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀) := by
  obtain ⟨Ch, hChpos, hH⟩ := halasz_twisted
  refine ⟨6 * Ch, by positivity, ?_⟩
  intro f X₁ X₂ M₀ T₀ t hf1 hfmult hfb hX₁ hX₁₂ hM₀ hT₀ ht hD
  have hX₁pos : 0 < X₁ := by linarith
  have hX₂pos : 0 < X₂ := by linarith
  set φ : ℝ := (1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀ with hφdef
  have hφpos : 0 < φ := by
    rw [hφdef]
    have h1 : 0 < Real.exp (-M₀) := Real.exp_pos _
    have h2 : 0 < 1 + M₀ := by linarith
    have h3 : 0 < Real.sqrt T₀ := Real.sqrt_pos.mpr (by linarith)
    positivity
  by_cases hcase : ⌈X₁⌉₊ ≤ ⌊X₂⌋₊
  · -- nonempty window: Abel summation plus Halász on every prefix
    set K : ℝ := Ch * φ with hKdef
    have hKnn : 0 ≤ K := by
      rw [hKdef]
      exact mul_nonneg (le_of_lt hChpos) (le_of_lt hφpos)
    set N : ℕ := ⌈X₁⌉₊ - 1 with hNdef
    set M : ℕ := ⌊X₂⌋₊ with hMdef
    have hceilge : 16 ≤ ⌈X₁⌉₊ := by
      have h : ((16 : ℕ) : ℝ) ≤ ((⌈X₁⌉₊ : ℕ) : ℝ) := le_trans hX₁ (Nat.le_ceil X₁)
      exact_mod_cast h
    have hceil1 : 1 ≤ ⌈X₁⌉₊ := le_trans (by norm_num) hceilge
    have hN1 : 1 ≤ N := by rw [hNdef]; omega
    have hNcast : ((N : ℕ) : ℝ) = ((⌈X₁⌉₊ : ℕ) : ℝ) - 1 := by
      rw [hNdef, Nat.cast_sub hceil1, Nat.cast_one]
    have hNsuc : N + 1 = ⌈X₁⌉₊ := by rw [hNdef]; omega
    have hfloorLe : ((⌊X₂⌋₊ : ℕ) : ℝ) ≤ X₂ := Nat.floor_le (le_of_lt hX₂pos)
    have hNM : N < M := by
      rw [hNdef, hMdef]
      calc ⌈X₁⌉₊ - 1 < ⌈X₁⌉₊ := Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one hceil1) (by norm_num)
        _ ≤ ⌊X₂⌋₊ := hcase
    -- Halász on every prefix in the window
    have hpref : ∀ k : ℕ, N ≤ k → k ≤ M →
        ‖∑ j ∈ Finset.Icc 1 k, f j * (j : ℂ) ^ (-(Complex.I * t))‖ ≤ K * (k : ℝ) := by
      intro k hNk hkM
      have hkR : ((N : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hNk
      have hkMR : (k : ℝ) ≤ ((M : ℕ) : ℝ) := by exact_mod_cast hkM
      have hkX4 : X₁ / 4 ≤ (k : ℝ) := by
        rw [hNcast] at hkR
        have hc : X₁ ≤ ((⌈X₁⌉₊ : ℕ) : ℝ) := Nat.le_ceil X₁
        linarith
      have hkX2 : (k : ℝ) ≤ X₂ := by
        rw [hMdef] at hkMR
        linarith
      have hk2 : 2 ≤ (k : ℝ) := by
        have hN15 : 15 ≤ N := by rw [hNdef]; omega
        have h1 : (15 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN15
        have h2 : ((N : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hNk
        linarith
      have hhal := hH f hf1 hfmult hfb (k : ℝ) T₀ t hk2 hT₀
      dsimp only at hhal
      rw [Nat.floor_natCast] at hhal
      set Mk : ℝ := ⨅ (u : {u : ℝ // |u| ≤ 2 * T₀}),
          BoundedMultiplicativeFunctions.𝔻 f
            (fun n ↦ (n : ℂ) ^ (Complex.I * (t + u.1))) (k : ℝ) ^ 2 with hMkdef
      have hb : (1 + Mk) * Real.exp (-Mk) ≤ (1 + M₀) * Real.exp (-M₀) := by
        rw [hMkdef]
        exact window_M_le f M₀ T₀ t (k : ℝ) hM₀ ht (fun w hw => hD (k : ℝ) hkX4 hkX2 w hw)
      calc ‖∑ j ∈ Finset.Icc 1 k, f j * (j : ℂ) ^ (-(Complex.I * t))‖
          ≤ Ch * (k : ℝ) * ((1 + Mk) * Real.exp (-Mk) + 1 / Real.sqrt T₀) := hhal
        _ ≤ Ch * (k : ℝ) * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith
        _ = K * (k : ℝ) := by rw [hKdef, hφdef]; ring
    have habel := window_abel_prefix (fun j : ℕ => f j * (j : ℂ) ^ (-(Complex.I * t)))
      K N M hKnn hN1 hNM hpref
    calc ‖∑ m ∈ Work.BMF.natIcc X₁ X₂, f m * (m : ℂ) ^ (-(1 + Complex.I * t))‖
        = ‖∑ n ∈ Finset.Ioc N M,
              (((n : ℝ))⁻¹ : ℂ) * (f n * (n : ℂ) ^ (-(Complex.I * t)))‖ := by
          rw [window_reindex_range_gen_aux f X₁ X₂ t hX₁, hNdef, hMdef]
      _ ≤ K * ((M : ℝ) + (N : ℝ)) * (1 / (M : ℝ) + 1 / ((N + 1 : ℕ) : ℝ)) := habel
      _ = K * (((⌊X₂⌋₊ : ℕ) : ℝ) + (((⌈X₁⌉₊ : ℕ) : ℝ) - 1)) *
            (1 / (((⌊X₂⌋₊ : ℕ) : ℝ)) + 1 / (((⌈X₁⌉₊ : ℕ) : ℝ))) := by
          rw [hNcast, hMdef, hNsuc]
      _ ≤ 6 * K * (X₂ / X₁) := window_arith_ratio X₁ X₂ K hX₁ hX₁₂ hKnn
      _ = 6 * Ch * (X₂ / X₁) * φ := by rw [hKdef]; ring
  · -- degenerate window: both sides of the reindexing are empty, the bound is trivial
    have hlt : ⌊X₂⌋₊ < ⌈X₁⌉₊ := not_le.mp hcase
    have hempty : Work.BMF.natIcc X₁ X₂ = ∅ := by
      rw [Work.BMF.natIcc]
      exact Finset.Icc_eq_empty_iff.mpr (not_le.mpr hlt)
    rw [hempty, Finset.sum_empty, norm_zero]
    have hR : 0 < X₂ / X₁ := div_pos hX₂pos hX₁pos
    positivity

end Work.BMF.mr_direct
