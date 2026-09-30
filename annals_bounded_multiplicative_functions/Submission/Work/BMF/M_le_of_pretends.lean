import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.N1.loglog_le
import Submission.Work.BMF.N1.primeRecips_diff_le
import Submission.Work.BMF.N1.D_split_le
import Submission.Work.BMF.N1.D_le_small
import Submission.Work.BMF.N1.M_le_D
import Submission.Work.BMF.N1.twistCorr_of_wgu

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/BMF/DESIGN.md (the lead's design for MRTTZ; your node's section has exact formulas). Shared definitions: Submission/Work/BMF/Defs.lean (do NOT edit). Owned library assets (chen_theorem Mertens/PNT/Siegel–Walfisz/zero-free regions, annals_large_value_estimates mean-value theorems + halasz_bound, bourgain Weyl differencing, and a v4.34 port of the Vinogradov mean value theorem) are being copied into Submission/Commons/ and Submission/Vinogradov/ now. See DESIGN.md §8 for exact module names, and import them once they exist instead of re-proving. Siblings run in parallel.

# N1 `M_le_of_pretends`: glue (pretentious transfer, small `X`, the `k = 0` conversion)

**Imports.** `Submission.Work.BMF.Defs`.

**Owned assets (v4.34).**
- chen `Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound`:
  `|Σ_{p≤x} 1/p − log log x| ≤ C` for `x ≥ 11`.
- Or `PrimeReciprocals/prime_recip_sum_le_log_log`.

## Route

**Preliminaries.**
- `0 ≤ 𝔻 f g Y` always. For a negative base, `rpow (1/2)` equals `exp(..)·cos(π/2) = 0`. But
  when `|f|, |g| ≤ 1` at primes each summand is `≥ 0` anyway.
- `M f Y Q` is `BddBelow` by `0`. For `Y ≥ 0` the index types are nonempty: `t = 0`, `q = 1`,
  and `χ = 1`.
- `M f Y Q ≤ 𝔻 f (χ · n^{it}) Y` for any admissible `(t, q, χ)`, by `ciInf_le` three times.
  Build `q` as `⟨⟨q, hq⟩, hqQ⟩`.

**(a) `X ≤ X₀`.** `Y_M ≤ C₀ max(X₀,1)^{k+1}`, because `H ≥ X^θ ≥ 1`. Then
`M ≤ 𝔻(f, 1; Y_M) ≤ (2 Σ_{p ≤ C₀max(X₀,1)^{k+1}} 1/p)^{1/2}`. For `q = 1`, `χ n = 1` and
`n^{I·0} = 1`.

**(b) Transfer.**
- If `Y_M ≤ Y`: `𝔻(·; Y_M) ≤ 𝔻(·; Y)` by monotonicity (summands `≥ 0`).
- Otherwise: `𝔻(·; Y_M)² ≤ 𝔻(·; Y)² + 2 Σ_{Y < p ≤ Y_M} 1/p`. Also
  `Y_M ≤ C₀ X^{(k+1)(1−θ)} ≤ C₀ Y^{2(k+1)}`, since `Y ≥ X^{1/2}`. Mertens gives the bound
  `2 log(2(k+1) + log C₀/log 2) + 4C`.
- Small `X`, where `Y < 11`: everything is bounded as in (a).
- Take `B` to be the max of all these bounds and `B₀`.

**(c) `k = 0`.**
- Degree-`≤ 0` polynomials are constants, and `|e(−c)| = 1`. So
  `weakGowersUniformityNorm 0 x H g = H⁻¹‖Σ_{Icc ⌈x⌉ ⌊x+H⌋} g‖` via `ciSup` on
  `{P ∈ degreeLE 0}`; the other `P` contribute `0`.
- For `x ≥ 1`, the `ℤ`-sum of `f ⌊z⌋₊` equals the `ℕ`-sum over `natIcc x (x+H)`.
- `(n:ℂ)^(-(I*0)) = 1`.
- Multiply by `H > 0`.

## Size and risk

Size 0.8–1.5k. Risk low.
-/

namespace Work.BMF

open Polynomial Finset Real Complex BoundedMultiplicativeFunctions
open scoped ComplexConjugate
open Work.BMF

set_option linter.unusedVariables false

/-- The summand of `𝔻` is nonnegative when `f` and `g` are `1`-bounded at the primes. -/
private lemma D_term_nonneg {f g : ℕ → ℂ} (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1)
    (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) {p : ℕ} (hp : p.Prime) :
    0 ≤ (1 - (f p * conj (g p)).re) / p := by
  have h1 : (f p * conj (g p)).re ≤ 1 := by
    calc (f p * conj (g p)).re ≤ ‖f p * conj (g p)‖ := Complex.re_le_norm _
      _ = ‖f p‖ * ‖g p‖ := by rw [Complex.norm_mul, Complex.norm_conj]
      _ ≤ 1 * 1 := by
          exact mul_le_mul (hf p hp) (hg p hp) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  exact div_nonneg (by linarith) (by positivity)

/-- `𝔻 f g X ≥ 0` for `1`-bounded `f`, `g`. -/
private lemma D_nonneg_of_bounded {f g : ℕ → ℂ} (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1)
    (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (X : ℝ) : 0 ≤ 𝔻 f g X := by
  rw [𝔻]
  apply Real.rpow_nonneg
  apply Finset.sum_nonneg
  intro p hp
  exact D_term_nonneg hf hg (Nat.mem_primesLE.mp hp).2

/-- `𝔻 f g ·` is monotone in the truncation scale, for `1`-bounded `f`, `g`. -/
private lemma D_mono {f g : ℕ → ℂ} (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1)
    (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) {Y Z : ℝ} (hYZ : Y ≤ Z) : 𝔻 f g Y ≤ 𝔻 f g Z := by
  rw [𝔻, 𝔻]
  refine Real.rpow_le_rpow (Finset.sum_nonneg ?_)
    (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (by norm_num)
  · intro p hp
    exact D_term_nonneg hf hg (Nat.mem_primesLE.mp hp).2
  · exact Nat.primesLE_mono (Nat.floor_mono hYZ)
  · intro p hp _
    exact D_term_nonneg hf hg (Nat.mem_primesLE.mp hp).2

/-- `C₀ X^{k+1}/H^{k+1} ≤ C₀ Bnd^{k+1}` when `X ≤ Bnd` and `1 ≤ H`, `C₀ ≥ 0`. -/
private lemma YM_le_bound (k : ℕ) {C₀ X H Bnd : ℝ} (hC₀ : 0 ≤ C₀) (hX : 0 ≤ X) (hH : 1 ≤ H)
    (hXH : X ≤ Bnd) (hBnd : 0 ≤ Bnd) :
    C₀ * X ^ (k + 1) / H ^ (k + 1) ≤ C₀ * Bnd ^ (k + 1) := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have h : C₀ * X ^ (k + 1) / H ^ (k + 1) = C₀ * (X / H) ^ (k + 1) := by
    rw [mul_div_assoc, div_pow]
  rw [h]
  apply mul_le_mul_of_nonneg_left _ hC₀
  apply pow_le_pow_left₀ (div_nonneg hX (le_of_lt hHpos)) _ (k + 1)
  rw [div_le_iff₀ hHpos]
  nlinarith [hXH, hBnd, hH]

/-- `C₀ X^{k+1}/H^{k+1} ≤ C₀ Y^{2(k+1)}` when `X ≤ Y²` and `1 ≤ H`, `C₀ ≥ 0`. -/
private lemma YM_le_pow (k : ℕ) {C₀ X Y H : ℝ} (hC₀ : 0 ≤ C₀) (hX : 0 ≤ X) (hH : 1 ≤ H)
    (hXY : X ≤ Y ^ 2) : C₀ * X ^ (k + 1) / H ^ (k + 1) ≤ C₀ * Y ^ (2 * (k + 1)) := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have h : C₀ * X ^ (k + 1) / H ^ (k + 1) = C₀ * (X / H) ^ (k + 1) := by
    rw [mul_div_assoc, div_pow]
  rw [h]
  apply mul_le_mul_of_nonneg_left _ hC₀
  have hXH : X / H ≤ Y ^ 2 := by
    rw [div_le_iff₀ hHpos]
    nlinarith [hXY, hH, sq_nonneg Y, hX]
  calc (X / H) ^ (k + 1) ≤ (Y ^ 2) ^ (k + 1) :=
        pow_le_pow_left₀ (div_nonneg hX (le_of_lt hHpos)) hXH (k + 1)
    _ = Y ^ (2 * (k + 1)) := by rw [← pow_mul]

/-- **N1. Glue: pretentious-distance transfer, the small-`X` bound, and `k = 0`.**
With `Y_M := C₀ X^{k+1}/H^{k+1}` (the scale of the Challenge target 1.3) and `X^θ ≤ H ≤ X^{1-θ}`:
(a) for `X ≤ X₀` the quantity `M(f; Y_M, Q)` is bounded by `B` (take `t = 0`, `q = 1`);
(b) if `f` pretends to be `χ(n) n^{it}` within `B₀` at a scale `Y ∈ [X^{1/2}, X]`, with
`|t| ≤ Y_M` and modulus `≤ Q`, then `M(f; Y_M, Q) ≤ B` (Mertens: moving the prime cut-off
between two scales `X^{Θ(1)}` changes `𝔻²` by `O_{k,θ}(1)`);
(c) the `k = 0` conversion: `‖g‖_{u¹[x,x+H]} = H⁻¹ |Σ_{x ≤ n ≤ x+H} g(n)|`, so the `k = 0`
hypothesis is the Matomäki–Radziwiłł hypothesis `TwistCorr f 1 0 X H η`. -/
theorem M_le_of_pretends (k : ℕ) (θ B₀ C₀ X₀ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1 / 2)
    (hC₀ : 0 < C₀) :
    ∃ B : ℝ, ∀ (f : ℕ → ℂ), IsOneBounded f → ∀ (Q : ℕ+) (X H : ℝ), 1 ≤ X →
      X ^ θ ≤ H → H ≤ X ^ (1 - θ) →
      (X ≤ X₀ → M f (C₀ * X ^ (k + 1) / H ^ (k + 1)) Q ≤ B) ∧
      (∀ Y t : ℝ, X ^ (1 / 2 : ℝ) ≤ Y → Y ≤ X → |t| ≤ C₀ * X ^ (k + 1) / H ^ (k + 1) →
        PretendsTo f Q B₀ Y t → M f (C₀ * X ^ (k + 1) / H ^ (k + 1)) Q ≤ B) ∧
      (∀ η : ℝ, ∫ x in X..(2 * X), weakGowersUniformityNorm 0 x H (fun z : ℤ ↦ f ⌊z⌋₊) ≥ η * X →
        TwistCorr f (fun _ ↦ 1) 0 X H η) := by
  obtain ⟨K, hKpos, hK⟩ := Work.BMF.N1.primeRecips_diff_le k C₀ hC₀
  set Zs : ℝ := C₀ * (max X₀ 121) ^ (k + 1) with hZsdef
  set Bs : ℝ := Real.sqrt (2 * (Zs + 1)) with hBsdef
  set cst : ℝ := Real.log ((2 * (k + 1) : ℝ) + |Real.log C₀|) with hcstdef
  set Bl : ℝ := Real.sqrt (max 0 (B₀ ^ 2 + 2 * (cst + K))) with hBldef
  refine ⟨max (max B₀ Bs) Bl, ?_⟩
  intro f hf Q X H hX hXH hHX
  have hf' : ∀ p, p.Prime → ‖f p‖ ≤ 1 := fun p _ => hf p
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hXnn : 0 ≤ X := le_of_lt hXpos
  have hH1 : 1 ≤ H := le_trans (Real.one_le_rpow hX (le_of_lt hθ₀)) hXH
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  have hYMnn : 0 ≤ C₀ * X ^ (k + 1) / H ^ (k + 1) := by positivity
  have hZsnn : 0 ≤ Zs := by rw [hZsdef]; positivity
  have hQ1 : 1 ≤ (Q : ℕ) := Q.2
  refine ⟨?_, ?_, ?_⟩
  · -- (a) small `X`
    intro hXX₀
    have hYMle : C₀ * X ^ (k + 1) / H ^ (k + 1) ≤ Zs := by
      rw [hZsdef]
      exact YM_le_bound k (le_of_lt hC₀) hXnn hH1 (le_trans hXX₀ (le_max_left X₀ 121))
        (by positivity)
    have hgnorm : ∀ p : ℕ, p.Prime →
        ‖(default : DirichletCharacter ℂ 1) (p : ZMod 1) * (p : ℂ) ^ (Complex.I * 0)‖ ≤ 1 := by
      intro p hp
      rw [Complex.norm_mul]
      have h1 : ‖(default : DirichletCharacter ℂ 1) (p : ZMod 1)‖ ≤ 1 :=
        DirichletCharacter.norm_le_one _ _
      have h2 : ‖(p : ℂ) ^ (Complex.I * 0)‖ = 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hp.pos]
        simp
      rw [h2]
      linarith
    calc M f (C₀ * X ^ (k + 1) / H ^ (k + 1)) Q
        ≤ 𝔻 f (fun n ↦ (default : DirichletCharacter ℂ 1) (n : ZMod 1) *
              (n : ℂ) ^ (Complex.I * 0))
            (C₀ * X ^ (k + 1) / H ^ (k + 1)) :=
          Work.BMF.N1.M_le_D f _ Q 1 one_pos hQ1 (default : DirichletCharacter ℂ 1) 0
            (by rw [abs_zero]; exact hYMnn)
      _ ≤ Real.sqrt (2 * (Zs + 1)) := Work.BMF.N1.D_le_small hf' hgnorm hYMle hZsnn
      _ = Bs := by rw [hBsdef]
      _ ≤ max (max B₀ Bs) Bl := le_trans (le_max_right B₀ Bs) (le_max_left (max B₀ Bs) Bl)
  · -- (b) transfer
    intro Y t hYX hYleX ht hpret
    obtain ⟨q, hq, hqQ, χ, hχB⟩ := hpret
    have hgnorm : ∀ p : ℕ, p.Prime → ‖χ (p : ZMod q) * (p : ℂ) ^ (Complex.I * t)‖ ≤ 1 := by
      intro p hp
      rw [Complex.norm_mul]
      have h1 : ‖χ (p : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
      have h2 : ‖(p : ℂ) ^ (Complex.I * t)‖ = 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hp.pos]
        simp
      rw [h2]
      linarith
    have hM := Work.BMF.N1.M_le_D f (C₀ * X ^ (k + 1) / H ^ (k + 1)) Q q hq hqQ χ t ht
    have hYnn : 0 ≤ Y := le_trans (Real.rpow_nonneg hXnn _) hYX
    by_cases hcase : C₀ * X ^ (k + 1) / H ^ (k + 1) ≤ Y
    · -- `Y_M ≤ Y`: monotonicity
      calc M f (C₀ * X ^ (k + 1) / H ^ (k + 1)) Q
          ≤ 𝔻 f (fun n ↦ χ n * (n : ℂ) ^ (Complex.I * t))
              (C₀ * X ^ (k + 1) / H ^ (k + 1)) := hM
        _ ≤ 𝔻 f (fun n ↦ χ n * (n : ℂ) ^ (Complex.I * t)) Y := D_mono hf' hgnorm hcase
        _ ≤ B₀ := hχB
        _ ≤ max (max B₀ Bs) Bl := le_trans (le_max_left B₀ Bs) (le_max_left (max B₀ Bs) Bl)
    · have hlt : Y < C₀ * X ^ (k + 1) / H ^ (k + 1) := lt_of_not_ge hcase
      have hY2 : X ≤ Y ^ 2 := by
        have h1 : (X ^ (1 / 2 : ℝ)) ^ 2 ≤ Y ^ 2 :=
          pow_le_pow_left₀ (Real.rpow_nonneg hXnn _) hYX 2
        have h2 : (X ^ (1 / 2 : ℝ)) ^ 2 = X := by
          rw [← Real.sqrt_eq_rpow]; exact Real.sq_sqrt hXnn
        linarith
      by_cases hY11 : Y < 11
      · -- small `Y`, hence bounded `X`: crude bound
        have hX121 : X ≤ max X₀ 121 := by
          have h121 : X < 121 := by nlinarith [hY2, hY11, hYnn, sq_nonneg Y]
          exact le_trans (le_of_lt h121) (le_max_right X₀ 121)
        have hYMle : C₀ * X ^ (k + 1) / H ^ (k + 1) ≤ Zs := by
          rw [hZsdef]
          exact YM_le_bound k (le_of_lt hC₀) hXnn hH1 hX121 (by positivity)
        calc M f (C₀ * X ^ (k + 1) / H ^ (k + 1)) Q
            ≤ 𝔻 f (fun n ↦ χ n * (n : ℂ) ^ (Complex.I * t))
                (C₀ * X ^ (k + 1) / H ^ (k + 1)) := hM
          _ ≤ Real.sqrt (2 * (Zs + 1)) := Work.BMF.N1.D_le_small hf' hgnorm hYMle hZsnn
          _ = Bs := by rw [hBsdef]
          _ ≤ max (max B₀ Bs) Bl := le_trans (le_max_right B₀ Bs) (le_max_left (max B₀ Bs) Bl)
      · -- `Y ≥ 11`: split the prime sum and use Mertens
        have hY11' : 11 ≤ Y := le_of_not_gt hY11
        have hYMpow : C₀ * X ^ (k + 1) / H ^ (k + 1) ≤ C₀ * Y ^ (2 * (k + 1)) :=
          YM_le_pow k (le_of_lt hC₀) hXnn hH1 hY2
        have hdiff := hK Y (C₀ * X ^ (k + 1) / H ^ (k + 1)) hY11' hlt.le hYMpow
        have hdiff' : (∑ p ∈ (⌊C₀ * X ^ (k + 1) / H ^ (k + 1)⌋₊).primesLE, (1 : ℝ) / p) -
            (∑ p ∈ (⌊Y⌋₊).primesLE, (1 : ℝ) / p) ≤ cst + K := by
          rw [hcstdef]; exact hdiff
        have hsplit := Work.BMF.N1.D_split_le hf' hgnorm hlt.le
        have hsq : 𝔻 f (fun n ↦ χ n * (n : ℂ) ^ (Complex.I * t)) Y ^ 2 ≤ B₀ ^ 2 :=
          pow_le_pow_left₀ (D_nonneg_of_bounded hf' hgnorm Y) hχB 2
        calc M f (C₀ * X ^ (k + 1) / H ^ (k + 1)) Q
            ≤ 𝔻 f (fun n ↦ χ n * (n : ℂ) ^ (Complex.I * t))
                (C₀ * X ^ (k + 1) / H ^ (k + 1)) := hM
          _ ≤ Real.sqrt (𝔻 f (fun n ↦ χ n * (n : ℂ) ^ (Complex.I * t)) Y ^ 2 +
                2 * ((∑ p ∈ (⌊C₀ * X ^ (k + 1) / H ^ (k + 1)⌋₊).primesLE, (1 : ℝ) / p) -
                  (∑ p ∈ (⌊Y⌋₊).primesLE, (1 : ℝ) / p))) := hsplit
          _ ≤ Real.sqrt (B₀ ^ 2 + 2 * (cst + K)) := Real.sqrt_le_sqrt (by linarith)
          _ ≤ Real.sqrt (max 0 (B₀ ^ 2 + 2 * (cst + K))) :=
              Real.sqrt_le_sqrt (le_max_right 0 _)
          _ = Bl := by rw [hBldef]
          _ ≤ max (max B₀ Bs) Bl := le_max_right _ _
  · -- (c) the `k = 0` conversion
    intro η hη
    exact Work.BMF.N1.twistCorr_of_wgu f X H η hX hHpos hη


end Work.BMF
