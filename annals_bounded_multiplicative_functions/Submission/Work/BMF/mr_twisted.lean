import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.H6_imports
import Submission.Work.BMF.mr_core_window
import Submission.Work.BMF.twist_reduction
import Submission.Work.BMF.D_twist_char
import Submission.Work.BMF.D_scale_transfer
import Submission.Work.BMF.CS_shortint
import Submission.Work.BMF.twisted_mult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/BMF/DESIGN.md (the lead's design for MRTTZ; your node's section has exact formulas). Shared definitions: Submission/Work/BMF/Defs.lean (do NOT edit). Owned library assets are being installed now (see Submission/Work/BMF/ASSETS.md once it exists, and DESIGN.md §8); import them instead of re-proving. Sibling nodes you import are proved in parallel; build against their statements.

# N9 `mr_twisted`: Matomäki–Radziwiłł with a periodic twist, polynomial range

**Sources.**
- `papers/mr_note/main.tex`: the one-scale Ramaré argument for `H = X^δ` and its appendix for
  general `f`.
- `papers/mr_annals/ShorterIntervals55.tex`:
  - §2 Halász-type pointwise bounds;
  - §3 large values, including the "Halász inequality for primes";
  - §4 the decomposition lemma `lem:decomp`;
  - §6 the Parseval bound.
- `papers/mrt_chowla/Chowla.tex` Appendix A: the complex-valued case, with the separate treatment
  near the minimiser `t₁` by Halász + the Granville–Soundararajan Lipschitz estimate.

**Imports.** `Submission.Work.BMF.Defs`, `Submission.Work.BMF.vk_prime_sums` (N10).

**Owned assets (v4.34, no port).**

LVE, `Commons/NumberTheory/DirichletPolynomial/`:
- `dirichlet_mean_value`, `mv_integral_separated_frequencies` (mean value theorem);
- `halasz_bound` (Halász–Montgomery);
- `large_values_halasz_huxley`, `mv_large_values`;
- `large_sieve_block_sampled`.

LVE, `Commons/Analysis/DirichletPolynomial/`: `well_spaced_block_mean_value`.

chen:
- Mertens: `primeRecips_sub_loglog_powLog`;
- Perron: `exists_perron_formula_bound`;
- characters: `sum_char_mul_conj`.

**Missing everywhere** (must be built here):
- Halász's mean-value theorem for multiplicative functions;
- the GS Lipschitz lemma;
- the Ramaré identity;
- short-interval Turán–Kubilius.

## Route

**A. Reduce the periodic twist to a character.**
- Expand the `r`-periodic `ψ` as a combination of `1_{d | n} χ(n/d)`, with `d | r` and `χ`
  mod `r/d`. Coefficients are `O_r(1)`.
- Write `n = d e m'` with `e | d^∞` and `(m', r) = 1`.
- Truncate `e ≤ E(η, r)`, using `Σ_{e | d^∞} 1/e ≪_r 1`.
- Then `f(dem') = f(de) f(m')`, and pigeonhole one `(d, e, χ)`.

Result: `∫_{Y'}^{2Y'} |Σ_{y ≤ m ≤ y+H''} g(m)| ≥ η' H'' Y'`. Here
`g(m) = f(m) χ'(m) m^{-iT₀}` is multiplicative, `1`-bounded, `χ'` is mod `r`, and
`Y' = Y/(de)`, `H'' = H'/(de)`.

At the end, `𝔻(g, n^{iu}; Y') = 𝔻(f, χ̄' n^{i(T₀+u)}; Y')` exactly: both have `1/p` at `p | r`.
The change of scale `Y' → Y` costs `O(log(de)/log Y)` by Mertens.

**B. Core: `Y^θ ≤ H ≤ Y`, `∫ |Σ_{[y,y+H]} g| ≥ ηHY` ⇒ `∃ |u| ≤ CY/H`, `𝔻(g, n^{iu}; Y) ≤ B`.**
Prove the contrapositive with `C := C(η)`.

1. **Parseval** (MR §6, or the note's Lemma 3 with the Saffari–Vaughan trick). Alternatively,
   use exact Plancherel on multiplicative intervals `(x, xe^{h}]` and compare with `[x, x+H]`.
   `(1/Y) ∫ |H⁻¹ Σ_{[y,y+H]} g|² ≪ ∫_{|t| ≤ CY/H} |G(1+it)|² dt + (tail)`, where
   `G(s) = Σ_{Y≤n≤3Y} g(n) n^{-s}`. The mean value theorem gives `tail ≪ 1/C`.
2. Let `u₁` minimise `𝔻(g, n^{iu}; Y)²` over `|u| ≤ 2CY/H`, with minimum `M₀ > B²`.
   **Near region** `|t − u₁| ≤ (log Y)^{1/16}`:
   - If `M₀ ≤ (1/8) log log Y`: GS Lipschitz gives
     `|G(1+it)| ≪ |G(1+iu₁)|/(1+|t−u₁|) + (log Y)^{-1/2+o(1)}`, and Halász gives
     `|G(1+iu₁)| ≪ (1+M₀)e^{-M₀}`. Integrate.
   - Otherwise use Halász directly.
3. **Far region.** Triangle inequality plus N10:
   `𝔻(1, n^{iv}; Y)² ≥ (1/4) log log Y − O(1)` for `(log Y)^{1/20} ≤ |v| ≤ 4CY/H`. Hence
   `𝔻(g, n^{it}; Y)² ≥ c log log Y` there, and Halász gives power-of-log savings for the Ramaré
   factor `F_j`.
   - Run the note's appendix argument with `P = exp((log Y)^{1−1/48})`,
     `Q = exp(log Y/log log Y)` and fine parameter `H₀ = (log Y)^{1/48}`.
   - Exceptional `n` (no prime factor in `[P, Q]`): Turán–Kubilius / Chebyshev gives density
     `≪ 1/log(log Q/log P)`. A sieve is not needed.
   - Small `Q_j`: mean value theorem.
   - Large `Q_j`: moments give `|𝒯| ≤ exp((log Y)^{1/48+o(1)})`, then the "Halász inequality for
     primes" (MR §3, off-diagonal via N10 prime sums), times `sup |F_j| ≪ (log Y)^{-c}`.
4. Total `≤ η²/4` for `B` large, giving the contradiction.

**C. Constants.** `B`, `C`, `Q := max R 1` (the character is mod `r ≤ R`), and `X₀` depend on
`(θ, η, R)`.

## Size and risk

Size 12–25k. **Risk high** (long, but well trodden).

Suggested sub-nodes:
- `parseval_short`
- `halasz_complex` (Granville–Soundararajan / GHS form with window `T₀`)
- `gs_lipschitz`
- `ramare_decomp`
- `prime_poly_large_values`
- `mr_core`
- `twist_reduction`
-/

namespace Work.BMF

open Polynomial BoundedMultiplicativeFunctions

/-- For every `n : ℕ` and `t : ℝ`, the complex power `n ^ (I * t)` has norm at most `1`. -/
lemma norm_nat_cpow_I_le_one (n : ℕ) (t : ℝ) : ‖(n : ℂ) ^ (Complex.I * (t : ℂ))‖ ≤ 1 := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    rw [show (((0 : ℕ)) : ℂ) = 0 by norm_num]
    rcases eq_or_ne t 0 with ht | ht
    · subst ht; simp
    · rw [Complex.zero_cpow (x := Complex.I * (t : ℂ))]
      · simp
      · exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast ht)
  · have hz : ((n : ℂ)) ≠ 0 := by simpa using hn
    rw [Complex.norm_cpow_of_ne_zero hz]
    have hre : (Complex.I * (t : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    have him : (Complex.I * (t : ℂ)).im = t := by
      simp [Complex.mul_im, Complex.I_re, Complex.I_im]
    have harg : Complex.arg ((n : ℂ)) = 0 := by
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp]
      exact Complex.arg_ofReal_of_nonneg (by positivity)
    rw [hre, him, harg]
    simp

/-- A complex Dirichlet character has norm at most one at every natural number. -/
lemma norm_char_apply_le_one {r : ℕ} (χ : DirichletCharacter ℂ r) (n : ℕ) : ‖χ n‖ ≤ 1 := by
  simpa using DirichletCharacter.norm_le_one χ (n : ZMod r)

/-- **N9. Matomäki–Radziwiłł with a periodic twist and an archimedean shift**
(MR Annals 2016, MR "note" 1502.02374, MRT Appendix A, polynomial range `H' ≥ Y^θ`).
If `∫_Y^{2Y} |Σ_{y ≤ n ≤ y+H'} f(n) ψ(n) n^{-iT₀}| dy ≥ η H' Y` with `ψ` periodic of period
`≤ R`, then `f` pretends to be `χ(n) n^{it}` with `|t - T₀| ≤ C Y/H'` and conductor `≤ Q`. -/
theorem mr_twisted (θ η : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hη : 0 < η) (R : ℕ) :
    ∃ B C X₀ : ℝ, 0 ≤ C ∧ ∃ Q : ℕ, 0 < Q ∧
      ∀ (f : ArithmeticFunction ℂ), f.IsMultiplicative → IsOneBounded f →
      ∀ (r : ℕ) (ψ : ℕ → ℂ), r ≤ R → IsPeriodicBdd r ψ →
      ∀ (T₀ Y H' : ℝ), X₀ ≤ Y → Y ^ θ ≤ H' → H' ≤ Y → TwistCorr f ψ T₀ Y H' η →
        ∃ t : ℝ, |t - T₀| ≤ C * Y / H' ∧ PretendsTo f Q B Y t := by
  have hθ'₀ : (0 : ℝ) < θ / 2 := by linarith
  have hθ'₁ : θ / 2 < θ := by linarith
  have hθ'₁' : θ / 2 < 1 := by linarith
  obtain ⟨X₁, η', K, hX₁, hη'pos, hK1, htw⟩ :=
    twist_reduction θ (θ / 2) η hθ₀ hθ₁ hθ'₀ hθ'₁ hη R
  obtain ⟨B₀, C₀, X₀₀, hB₀pos, hC₀pos, hX₀₀, hcore⟩ :=
    mr_core_window (θ / 2) hθ'₀ hθ'₁' η' hη'pos
  obtain ⟨Cst, hCst, hscale⟩ := D_scale_transfer K hK1
  refine ⟨B₀ + Cst, C₀, max (max X₁ (K * X₀₀)) (K * 11), le_of_lt hC₀pos, max R 1, ?_, ?_⟩
  · positivity
  intro f hf hfb r ψ hrR hψ T₀ Y H' hX₀Y hYθ hH'Y hcorr
  obtain ⟨hrpos, hψper, hψbdd⟩ := hψ
  -- largeness consequences of `X₀ ≤ Y`
  have hX₁Y : X₁ ≤ Y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX₀Y
  have hKY : K * X₀₀ ≤ Y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX₀Y
  have hK11 : K * 11 ≤ Y := le_trans (le_max_right _ _) hX₀Y
  have hYge1 : 1 ≤ Y := le_trans hX₁ hX₁Y
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hYge1
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hH'pos : 0 < H' :=
    lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one (Real.one_le_rpow hYge1 (le_of_lt hθ₀))) hYθ
  -- Step 1: the twist reduction to a multiplicative short-interval mean
  obtain ⟨χ, Y', H'', hY'lo, hY'le, hH''lo, hH''le, hratio, hθ'Y', htc⟩ :=
    htw f hf hfb r ψ hrpos hrR hψper hψbdd T₀ Y H' hX₁Y hYθ hH'Y hcorr
  have hY'pos : 0 < Y' := lt_of_lt_of_le (div_pos hYpos hKpos) hY'lo
  have hH''pos : 0 < H'' := lt_of_lt_of_le (div_pos hH'pos hKpos) hH''lo
  have hY'X₀₀ : X₀₀ ≤ Y' := by
    have : X₀₀ ≤ Y / K := (le_div_iff₀ hKpos).mpr (by rw [mul_comm]; exact hKY)
    exact le_trans this hY'lo
  have h11Y' : 11 ≤ Y' := by
    have : 11 ≤ Y / K := (le_div_iff₀ hKpos).mpr (by rw [mul_comm]; exact hK11)
    exact le_trans this hY'lo
  have hH''Y' : H'' ≤ Y' := by
    have h1 : 1 ≤ Y' / H'' := by
      rw [hratio]
      exact (one_le_div hH'pos).mpr hH'Y
    simpa using (le_div_iff₀ hH''pos).mp h1
  -- Step 2: the multiplicative, `1`-bounded function `g(n) = f(n) χ(n) n^{-i T₀}`
  set g : ℕ → ℂ := fun n ↦ (f n) * (χ n) * ((n : ℂ) ^ (-(Complex.I * T₀))) with hgdef
  obtain ⟨hg1raw, hgmulraw, hgbraw⟩ :=
    twisted_mult (f : ℕ → ℂ) (fun m n h => hf.2 h) hf.1 hfb r χ T₀
  have hg1 : g 1 = 1 := by rw [hgdef]; simpa using hg1raw
  have hgmul : ∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n := by
    intro m n h
    rw [hgdef]
    simpa using hgmulraw m n h
  have hgb : ∀ n : ℕ, ‖g n‖ ≤ 1 := by
    intro n
    rw [hgdef]
    simpa using hgbraw n
  have htc' : η' * H'' * Y' ≤ ∫ y in Y'..(2 * Y'), ‖∑ n ∈ natIcc y (y + H''), g n‖ := by
    rw [hgdef]
    unfold TwistCorr at htc
    simpa only [mul_one] using htc
  have hCS := CS_shortint g Y' H'' η' hH''pos hY'pos (le_of_lt hη'pos) htc'
  -- Step 3: contrapositive of the core and final packaging
  by_contra hno
  have hcorehyp : ∀ u : ℝ, |u| ≤ C₀ * Y' / H'' →
      B₀ ≤ 𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y' := by
    intro u hu
    by_contra hlt
    have hlt' : 𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y' < B₀ := lt_of_not_ge hlt
    have key : 𝔻 (fun n ↦ (f n) * (χ n) * ((n : ℂ) ^ (-(Complex.I * T₀))))
        (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y'
        = 𝔻 (f : ℕ → ℂ)
          (fun n ↦ ((χ⁻¹ : DirichletCharacter ℂ r) n) *
            ((n : ℂ) ^ (Complex.I * (T₀ + u)))) Y' :=
      D_twist_char r χ (f : ℕ → ℂ) T₀ u Y'
    rw [← hgdef] at key
    have hb2 : ∀ n : ℕ, ‖((χ⁻¹ : DirichletCharacter ℂ r) n) *
        ((n : ℂ) ^ (Complex.I * (T₀ + u)))‖ ≤ 1 := by
      intro n
      have h1 : ‖((χ⁻¹ : DirichletCharacter ℂ r) n)‖ ≤ 1 := norm_char_apply_le_one (χ⁻¹) n
      have h2 : ‖((n : ℂ) ^ (Complex.I * (T₀ + u)))‖ ≤ 1 := by
        simpa [Complex.ofReal_add] using norm_nat_cpow_I_le_one n (T₀ + u)
      calc ‖((χ⁻¹ : DirichletCharacter ℂ r) n) * ((n : ℂ) ^ (Complex.I * (T₀ + u)))‖
          = ‖((χ⁻¹ : DirichletCharacter ℂ r) n)‖ *
              ‖((n : ℂ) ^ (Complex.I * (T₀ + u)))‖ := norm_mul _ _
        _ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have htr := hscale (f : ℕ → ℂ)
      (fun n ↦ ((χ⁻¹ : DirichletCharacter ℂ r) n) * ((n : ℂ) ^ (Complex.I * (T₀ + u))))
      hfb hb2 Y Y' h11Y' hY'lo hY'le
    have hBle : 𝔻 (f : ℕ → ℂ)
        (fun n ↦ ((χ⁻¹ : DirichletCharacter ℂ r) n) *
          ((n : ℂ) ^ (Complex.I * (T₀ + u)))) Y' ≤ B₀ := by
      rw [← key]
      exact le_of_lt hlt'
    have hfin : 𝔻 (f : ℕ → ℂ)
        (fun n ↦ ((χ⁻¹ : DirichletCharacter ℂ r) n) *
          ((n : ℂ) ^ (Complex.I * (T₀ + u)))) Y ≤ B₀ + Cst := by
      linarith
    refine absurd ?_ hno
    refine ⟨T₀ + u, ?_, ?_⟩
    · have hu' : |u| ≤ C₀ * Y / H' := by
        calc |u| ≤ C₀ * Y' / H'' := hu
          _ = C₀ * (Y' / H'') := by ring
          _ = C₀ * (Y / H') := by rw [hratio]
          _ = C₀ * Y / H' := by ring
      simpa using hu'
    · exact ⟨r, hrpos, le_trans hrR (le_max_left _ _), χ⁻¹, by simpa using hfin⟩
  have hcoreconcl := hcore g hg1 hgmul hgb Y' H'' hY'X₀₀ hθ'Y' hH''Y' hcorehyp
  have hη2 : (0 : ℝ) < η' ^ 2 := pow_pos hη'pos 2
  linarith [hCS, hcoreconcl, hη2]

end Work.BMF
