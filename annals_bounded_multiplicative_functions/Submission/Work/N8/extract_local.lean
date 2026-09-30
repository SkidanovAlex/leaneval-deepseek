import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.n8_defs
import Submission.Work.N8.shift_avg_lower
import Submission.Work.N8.phase_lipschitz
import Submission.Work.N8.window_transfer_phase
import Submission.Work.N8.window_norm_intervalIntegrable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.N8.extract_local`

The local extraction step (Step 7 of the N8 design, last page of §3 of MRTTZ): a large
correlation `|Σ_{n ∈ [x,x+L]} f(n) e(-P(n))| ≥ cA·L` together with the local decomposition
`P = ε + (T/2π) log + γ` (with `|ε'| ≤ c₁/L`) yields a lower bound for the *shift average* of the
short twisted sums of length `c*·L`:

`cdbl·cA·L·(c*·L) ≤ ∫_x^{x+L} ‖Σ_{n ∈ [y, y+c*L]} f(n) e(-γ(n)) n^{-iT₀}‖ dy`.

The three analytic ingredients are delegated:
* `Work.N8.shift_avg_lower`  : the shift-average identity;
* `Work.N8.window_transfer_phase` : the phase change `e(-P) → e(-γ)n^{-iT₀}` on short windows;
* `Work.N8.phase_lipschitz`  : Lipschitz bound for the phase `t ↦ T₀ log t - 2π(P - γ)(t)`;
* `Work.N8.window_norm_intervalIntegrable` : integrability of the window sums.
-/

namespace Work.N8

open Polynomial BoundedMultiplicativeFunctions MeasureTheory
open scoped BigOperators

/-- `‖e(t)‖ = 1` for the additive character `e(t) = exp(2πit)`. -/
theorem eC_norm (t : ℝ) : ‖Work.BMF.eC t‖ = 1 := by
  unfold Work.BMF.eC
  rw [show (2 * ↑Real.pi * Complex.I * ↑t) = (((2*Real.pi*t : ℝ)) : ℂ) * Complex.I by
        push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `‖n^{-iT}‖ = 1` for `1 ≤ n`. -/
theorem cpow_neg_norm (n : ℕ) (hn : 1 ≤ n) (T₀ : ℝ) : ‖(n:ℂ)^(-(Complex.I * T₀))‖ = 1 := by
  rw [Complex.cpow_neg, norm_inv]
  have h1 : ‖(n:ℂ)^(Complex.I * T₀)‖ = 1 := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]
    simp [Complex.mul_re]
  rw [h1, inv_one]

/-- `‖n^{-iT}‖ ≤ 1` for every `n`. -/
theorem cpow_neg_norm_le (n : ℕ) (T₀ : ℝ) : ‖(n:ℂ)^(-(Complex.I * T₀))‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [Complex.cpow_def]
    split_ifs <;> simp
  · rw [cpow_neg_norm n h T₀]

theorem ofReal_natCast_log (n : ℕ) : ((Real.log n : ℝ) : ℂ) = Complex.log ((n:ℝ):ℂ) :=
  Complex.ofReal_log (by positivity)

/-- The twist identity: on the window summands, `e(-P(n)) = e(-γ(n)) n^{-iT₀} · e^{iψ(n)}` with
the phase `ψ(t) = T₀ log t - 2π(P - γ)(t)`. -/
theorem twist_unit (P γ : Polynomial ℝ) (T₀ : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    Work.BMF.eC (-(γ.eval (n:ℝ))) * (n:ℂ)^(-(Complex.I * T₀))
      * Complex.exp (Complex.I * ((T₀ * Real.log n - (2:ℝ)*Real.pi*(P.eval (n:ℝ) - γ.eval (n:ℝ))) : ℝ))
    = Work.BMF.eC (-(P.eval (n:ℝ))) := by
  have hn0 : (n:ℂ) ≠ 0 := by
    have : (0:ℝ) < n := by exact_mod_cast hn
    exact_mod_cast ne_of_gt this
  have hcn : Complex.log (n:ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast]; exact (ofReal_natCast_log n).symm
  simp only [Work.BMF.eC]
  rw [Complex.cpow_def, if_neg hn0, hcn]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem extract_local (k : ℕ) :
    ∀ (cA c₁ cT : ℝ), 0 < cA → 0 < c₁ → 0 < cT →
    ∃ cstar cdbl : ℝ, 0 < cstar ∧ cstar ≤ 1 ∧ 0 < cdbl ∧
    ∀ (f : ℕ → ℂ) (T T₀ x L : ℝ) (P γ : Polynomial ℝ),
      BoundedMultiplicativeFunctions.IsOneBounded f → 1 ≤ L → 1 ≤ x → 8 ≤ cA * L →
      |T - T₀| ≤ cT * (x / L) →
      (∀ t ∈ Set.Icc x (x + L),
        |deriv (fun s ↦ P.eval s - T / (2 * Real.pi) * Real.log s - γ.eval s) t| ≤ c₁ / L) →
      cA * L ≤ ‖Work.BMF.corr f P x L‖ →
      Work.BMF.LocalTwist f (fun n ↦ Work.BMF.eC (-(γ.eval (n : ℝ)))) T₀ x L (cstar * L) (cdbl * cA)
:= by
  intro cA c₁ cT hcA hc₁ hcT
  refine ⟨min (1/2) (3 * cA / (8 * (4 + (2 * Real.pi * c₁ + cT)))), 1/4, ?_, ?_, ?_, ?_⟩
  · exact lt_min (by norm_num) (div_pos (by positivity) (by positivity))
  · exact (min_le_left _ _).trans (by norm_num)
  · norm_num
  · intro f T T₀ x L P γ hf hL hx h8 hTT hderiv hcorr
    set K : ℝ := 2 * Real.pi * c₁ + cT with hKdef
    set α : ℝ := min (1/2) (3 * cA / (8 * (4 + K))) with hαdef
    set H' : ℝ := α * L with hH'def
    have hαpos : 0 < α := by
      rw [hαdef]; exact lt_min (by norm_num) (div_pos (by positivity) (by positivity))
    have hαhalf : α ≤ 1/2 := by rw [hαdef]; exact min_le_left _ _
    have hαK : α * (8 * (4 + K)) ≤ 3 * cA := by
      rw [hαdef]
      have hsign : (0:ℝ) ≤ 8 * (4 + K) := by positivity
      calc min (1/2) (3 * cA / (8 * (4 + K))) * (8 * (4 + K))
          ≤ (3 * cA / (8 * (4 + K))) * (8 * (4 + K)) :=
            mul_le_mul_of_nonneg_right (min_le_right (1/2) (3*cA/(8*(4+K)))) hsign
        _ = 3 * cA := by
            have hne : (8 * (4 + K)) ≠ 0 := by positivity
            rw [div_mul_cancel₀ _ hne]
    have hKpos : 0 < K := by rw [hKdef]; positivity
    have hLpos : 0 < L := by linarith
    have hxpos : 0 < x := by linarith
    have hH'pos : 0 < H' := by rw [hH'def]; positivity
    have hH'leL : H' ≤ L := by
      rw [hH'def]
      have : α * L ≤ (1/2) * L := mul_le_mul_of_nonneg_right hαhalf (le_of_lt hLpos)
      linarith
    -- the two summands: `g` is the twisted summand of the conclusion, `h` the correlation summand
    set g : ℕ → ℂ := fun n => f n * Work.BMF.eC (-(γ.eval (n:ℝ))) * (n:ℂ)^(-(Complex.I * T₀))
      with hgdef
    set h : ℕ → ℂ := fun n => f n * Work.BMF.eC (-(P.eval (n:ℝ))) with hhdef
    set Ψ : ℝ → ℝ := fun t => T₀ * Real.log t - (2:ℝ)*Real.pi*(P.eval t - γ.eval t) with hΨdef
    unfold Work.BMF.LocalTwist
    change (1/4 * cA) * L * H' ≤ ∫ y in x..(x+L), ‖∑ n ∈ Work.BMF.natIcc y (y+H'), g n‖
    -- basic bounds
    have hh_le_one : ∀ n, ‖h n‖ ≤ 1 := by
      intro n
      rw [hhdef]; simp only []
      rw [norm_mul, eC_norm, mul_one]
      exact hf n
    have hg_le_one : ∀ n, ‖g n‖ ≤ 1 := by
      intro n
      rw [hgdef]; simp only []
      rw [norm_mul, norm_mul, eC_norm, mul_one]
      have hb := cpow_neg_norm_le n T₀
      nlinarith [hb, hf n, norm_nonneg (f n), norm_nonneg ((n:ℂ)^(-(Complex.I * T₀)))]
    -- the correlation, written with `h`
    have hcorr' : cA * L ≤ ‖∑ n ∈ Work.BMF.natIcc x (x+L), h n‖ := by
      have hc1 : Work.BMF.corr f P x L = ∑ n ∈ Work.BMF.natIcc x (x+L), h n := by
        simp only [Work.BMF.corr, hhdef]
      rwa [hc1] at hcorr
    -- the phases agree on each window
    have hh_transfer : ∀ y : ℝ, 1 ≤ y →
        ∑ n ∈ Work.BMF.natIcc y (y+H'), h n
          = ∑ n ∈ Work.BMF.natIcc y (y+H'), g n * Complex.exp (Complex.I * (Ψ n)) := by
      intro y hy
      apply Finset.sum_congr rfl
      intro n hnmem
      have hyc : (1:ℕ) ≤ ⌈y⌉₊ := by
        have h1 : ⌈(1:ℝ)⌉₊ ≤ ⌈y⌉₊ := Nat.ceil_mono hy
        simpa using h1
      have hn1 : 1 ≤ n := le_trans hyc (Finset.mem_Icc.mp (show n ∈ Finset.Icc ⌈y⌉₊ ⌊y+H'⌋₊ from hnmem)).1
      have hkey := twist_unit P γ T₀ n hn1
      have hexp : Complex.exp (Complex.I * (Ψ n))
          = Complex.exp (Complex.I * ((T₀ * Real.log n
              - (2:ℝ)*Real.pi*(P.eval (n:ℝ) - γ.eval (n:ℝ))) : ℝ)) := by
        rw [hΨdef]
      rw [hhdef, hgdef]; simp only []
      rw [hexp, ← hkey]
      ring
    -- Lipschitz bound for the phase
    have hψ_lip : ∀ a ∈ Set.Icc x (x+L), ∀ b ∈ Set.Icc x (x+L),
        |Ψ a - Ψ b| ≤ (K/L) * |a - b| := by
      intro a ha b hb
      have hpl := phase_lipschitz (P := P) (γ := γ) (T := T) (T₀ := T₀) (x := x) (L := L)
        (c₁ := c₁) (cT := cT) hxpos hLpos hTT hderiv a ha b hb
      rw [hΨdef]; simp only []
      rw [hKdef]
      exact hpl
    -- the three integral ingredients
    have hWg_int : IntervalIntegrable
        (fun y : ℝ => ‖∑ n ∈ Work.BMF.natIcc y (y+H'), g n‖) volume x (x+L) :=
      window_norm_intervalIntegrable (g := g) (x := x) (L := L) (H' := H') (a := x) (b := x+L)
        hx (le_of_lt hH'pos) ⟨le_refl x, by linarith⟩ ⟨by linarith, le_refl _⟩
    have hmono : ∫ y in x..(x+L-H'), ‖∑ n ∈ Work.BMF.natIcc y (y+H'), g n‖
        ≤ ∫ y in x..(x+L), ‖∑ n ∈ Work.BMF.natIcc y (y+H'), g n‖ :=
      intervalIntegral.integral_mono_interval (le_refl x) (by linarith) (by linarith)
        (Filter.Eventually.of_forall (fun y => norm_nonneg _)) hWg_int
    have hA := shift_avg_lower (g := h) (x := x) (L := L) (H' := H') hx hH'pos hH'leL hh_le_one
    have hD := window_transfer_phase (g := g) (ψ := Ψ) (K := K) (x := x) (L := L) (H' := H')
      hx hH'pos hH'leL (le_of_lt hKpos) hg_le_one hψ_lip
    have hJ : (∫ y in x..(x+L-H'), ‖∑ n ∈ Work.BMF.natIcc y (y+H'), h n‖)
        = (∫ y in x..(x+L-H'),
            ‖∑ n ∈ Work.BMF.natIcc y (y+H'), g n * Complex.exp (Complex.I * (Ψ n))‖) := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hmin : min x (x+L-H') = x := min_eq_left (by linarith)
      have hxyle : x ≤ y := by rw [← hmin]; exact hy.1
      have hy1 : 1 ≤ y := le_trans hx hxyle
      show ‖∑ n ∈ Work.BMF.natIcc y (y+H'), h n‖
        = ‖∑ n ∈ Work.BMF.natIcc y (y+H'), g n * Complex.exp (Complex.I * (Ψ n))‖
      rw [hh_transfer y hy1]
    -- combine
    have hmain : H' * (cA*L) - (4*H'*((⌊H'⌋₊:ℝ)+1) + K*((⌊H'⌋₊:ℝ)*((⌊H'⌋₊:ℝ)+1)))
        ≤ ∫ y in x..(x+L), ‖∑ n ∈ Work.BMF.natIcc y (y+H'), g n‖ := by
      have h1 : H' * (cA*L) - 4*H'*((⌊H'⌋₊:ℝ)+1)
          ≤ (∫ y in x..(x+L-H'), ‖∑ n ∈ Work.BMF.natIcc y (y+H'), h n‖) := by
        have h2 : H' * (cA*L) ≤ H' * ‖∑ n ∈ Work.BMF.natIcc x (x+L), h n‖ :=
          mul_le_mul_of_nonneg_left hcorr' (le_of_lt hH'pos)
        linarith [hA, h2]
      have h3 : (∫ y in x..(x+L-H'), ‖∑ n ∈ Work.BMF.natIcc y (y+H'), h n‖)
          ≤ (∫ y in x..(x+L), ‖∑ n ∈ Work.BMF.natIcc y (y+H'), g n‖)
            + K*((⌊H'⌋₊:ℝ)*((⌊H'⌋₊:ℝ)+1)) := by
        rw [hJ]
        linarith [hD, hmono]
      linarith [h1, h3]
    -- the arithmetic
    have harith : 4*H'*((⌊H'⌋₊:ℝ)+1) + K*((⌊H'⌋₊:ℝ)*((⌊H'⌋₊:ℝ)+1)) ≤ (3/4)*H'*(cA*L) := by
      by_cases hm : (⌊H'⌋₊ : ℝ) = 0
      · rw [hm]
        nlinarith [hH'pos, h8]
      · have hm1 : (1:ℝ) ≤ (⌊H'⌋₊:ℝ) := by
          have hnn : ⌊H'⌋₊ ≠ 0 := by
            intro h
            exact hm (by rw [h]; simp)
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hnn
        have hmH : (⌊H'⌋₊:ℝ) ≤ H' := Nat.floor_le (le_of_lt hH'pos)
        have hH'1 : 1 ≤ H' := by linarith
        have hK' : (8 + 2*K)*H' ≤ (3/4)*cA*L := by
          rw [hH'def]
          have hα' : (8 + 2*K)*α ≤ 3*cA/4 := by linarith [hαK]
          nlinarith [hα', hαpos, hKpos, hLpos, hcA]
        calc 4*H'*((⌊H'⌋₊:ℝ)+1) + K*((⌊H'⌋₊:ℝ)*((⌊H'⌋₊:ℝ)+1))
            ≤ 8*H'^2 + 2*K*H'^2 := by
              have e1 : 4*H'*((⌊H'⌋₊:ℝ)+1) ≤ 8*H'^2 := by
                have h2 : (⌊H'⌋₊:ℝ)+1 ≤ 2*H' := by linarith
                nlinarith [hH'pos, hmH]
              have e2 : K*((⌊H'⌋₊:ℝ)*((⌊H'⌋₊:ℝ)+1)) ≤ 2*K*H'^2 := by
                have h2 : (⌊H'⌋₊:ℝ)+1 ≤ 2*H' := by linarith
                have hmm : (⌊H'⌋₊:ℝ) * ((⌊H'⌋₊:ℝ)+1) ≤ 2*H'^2 := by
                  have : (⌊H'⌋₊:ℝ) * ((⌊H'⌋₊:ℝ)+1) ≤ H' * (2*H') :=
                    mul_le_mul hmH h2 (by positivity) (le_of_lt hH'pos)
                  linarith [this]
                nlinarith [hmm, hKpos]
              linarith
          _ = (8+2*K)*H'^2 := by ring
          _ ≤ (3/4)*H'*(cA*L) := by
              rw [show (8+2*K)*H'^2 = ((8+2*K)*H')*H' by ring]
              nlinarith [hK', hH'pos]
    have hfin : (1/4*cA)*L*H'
        ≤ H' * (cA*L) - (4*H'*((⌊H'⌋₊:ℝ)+1) + K*((⌊H'⌋₊:ℝ)*((⌊H'⌋₊:ℝ)+1))) := by
      linarith [harith]
    exact le_trans hfin hmain

end Work.N8
