/-
# Proposition `propdual-second` from Corollary `struct-dual`

This module proves the implication

  `StructDecompClaim P ⟹ PropdualSecondClaim P`

of Krause--Mirek--Tao §5.2: from the structural decomposition of the second dual function
`Ã_N^{**}(f,h)` (Corollary `struct-dual`) one deduces the `ℓ²` bound

  `‖(1 - Π_{≤l,≤d(l-Log N)}) Ã_N^{**}(f,h)‖_{ℓ²} ≲ 2^{-cl} N^{d/2}`   (`propdual-second`)

for `1`-bounded `f, h` supported in `[-N₀,N₀]`, `N₀ ~ N^d`, on good major arcs.

The argument is the paper's.  The decomposition

  `Ã_N^{**}(f,h) = ∑_{i ≤ s} w_i · λ_i φ_i + E₁ + E₂`

with `φ_i` Fourier supported in `majorArc ρ l_i k_i`, `2^{l_i} ≤ C₁δ^{-K₁}`,
`2^{k_i} ≤ C₁δ^{-K₁}/N^d`, and the errors `‖E₁‖_{ℓ¹} ≤ δN^d`, `‖E₂‖_{ℓ²} ≤ δ`, is applied with the
*specific* choice `δ = 2^{-8cl}`.  Choosing the rate `c` so small that `8cK₁ = 1/4`, every piece
`φ_i` has its frequency support far below the threshold of the projection: for `l` above a
threshold depending only on the constants one has `l_i ≤ l` and `k_i ≤ d(l-Log N) - 1`, so that
`Π_{≤l,≤d(l-Log N)}φ_i = φ_i` (the projection fixes its own major arcs,
`A4.kmtProjEqSelf`).  Hence

  `(1 - Π) Ã_N^{**}(f,h) = (1 - Π)(E₁ + E₂)`.

The `ℓ²`-error is handled with the `ℓ²`-boundedness of the projection; the `ℓ¹`-error is handled by
interpolation: the `ℓ^p`-bound (`p < 2` close to `1`) comes from the `ℓ¹`-ball together with the
pointwise bound on `E₁` (which itself comes from the decomposition), while the `ℓ^{p'}`-bound
comes from the `ℓ^{p'}`-bound of `Ã_N^{**}(f,h)`, i.e. from the spatial support of the second dual
function.  Riesz--Thorin interpolation at exponent `2` gives `δ^{1/4} N^{d/2}`, and the remaining
factor `⟨l⟩ ≤ 2^{cl}` is absorbed by the decay of `δ`.  For `l` below the threshold the trivial
bound `‖(1-Π)u‖₂ ≤ ‖u‖₂ + ‖Πu‖₂ ≲ ⟨l⟩N^{d/2}` suffices.

## Main result

* `Work.KMTAreas.A4Z.propdualSecondClaim_of_structDecompClaim`

## Auxiliary results (delegated, in `Submission/Work/KMTAreas/A4Z/`)

* `supportIn_eLpNorm_le` — the `ℓ^r` norm of a `1`-bounded function supported in `[-M,M]` is at
  most `(2M+1)^{1/r}`;
* `exists_threshold_two_pow_le` — the threshold above which the major arcs of the decomposition
  sit below the arcs of the projection;
* `rpow_prod_le` — the elementary `rpow` bookkeeping of the `ℓ^p`-`ℓ^∞` interpolation of `E₁`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.supportIn_eLpNorm_le
import Submission.Work.KMTAreas.A4Z.exists_threshold_two_pow_le
import Submission.Work.KMTAreas.A4Z.rpow_prod_le
import Submission.Work.KMTAreas.A4.kmtProjEqSelf
import Submission.Work.KMTAreas.A4.kmtProjSelfAdjoint
import Submission.Work.A3.abs_eval_le_coeff_sum
import Submission.Work.KMTAreas.A4.eLpNorm_le_of_l1_and_bounded
import Submission.Work.KMTAreas.A4.eLpNorm_two_le_of_interp
import Submission.Work.KMTAreas.A4.eLpNorm_count_le_of_two_le
import Submission.Work.KMTAreas.A4.eLpNorm_count_eq_lp_norm
import Submission.Work.KMTAreas.A4.rpowHalf_mul_rpow_rpowHalf
import Submission.Work.KMTAreas.A4.eventually_max_le_two_rpow
import Submission.Work.KMTAreas.A4.p_choice_facts
import Submission.Work.KMTAreas.A4.two_pow_logN_le
import Submission.Work.KMTAreas.A5.Endpoints

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.Analysis.InverseTheory
open Work.Analysis.EndVar
open Work.KMTAreas.A5 (BoundedZ boundedZ_add kmtProj_add_bounded kmtProj_smul_bounded)
open Work.KMTContract (kmtProj)
open Work.Analysis.IWMultiplier (angleBracket)

namespace Work.KMTAreas.A4Z

/-! ## Elementary facts about the scale `⟨l⟩` and about `eLpNorm` over `(ℤ, count)` -/

theorem angleBracket_coe_le_succ (l : ℕ) : (angleBracket l : ℝ) ≤ (l : ℝ) + 1 := by
  rw [angleBracket, NNReal.coe_max, NNReal.coe_one, NNReal.coe_natCast]
  have h : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
  exact max_le (by linarith) (by linarith)

theorem one_le_angleBracket_coe (l : ℕ) : (1 : ℝ) ≤ (angleBracket l : ℝ) := by
  rw [angleBracket, NNReal.coe_max, NNReal.coe_one, NNReal.coe_natCast]
  exact le_max_left _ _

/-- The triangle inequality for `eLpNorm` over the counting measure on `ℤ`. -/
theorem eLpNorm_sub_le_count {u v : ℤ → ℂ} {q : ℝ≥0∞} (hq : 1 ≤ q) :
    eLpNorm (fun x : ℤ => u x - v x) q Measure.count
      ≤ eLpNorm u q Measure.count + eLpNorm v q Measure.count :=
  eLpNorm_sub_le hq

/-- The triangle inequality for `eLpNorm` over the counting measure on `ℤ`, additive form. -/
theorem eLpNorm_add_le_count {u v : ℤ → ℂ} {q : ℝ≥0∞} (hq : 1 ≤ q) :
    eLpNorm (fun x : ℤ => u x + v x) q Measure.count
      ≤ eLpNorm u q Measure.count + eLpNorm v q Measure.count :=
  eLpNorm_add_le hq


/-! ## The second dual function: pointwise bound, support, and the polynomial-shift bound -/

/-- The second dual function `Ã**_N(f,h)` is bounded by `1` when `f` and `h` are. -/
theorem norm_AhalfTranspose₂_le_one {N : ℕ} (hN : 1 ≤ N) (P : Polynomial ℤ) {f h : ℤ → ℂ}
    (hf : ∀ x, ‖f x‖ ≤ 1) (hh : ∀ x, ‖h x‖ ≤ 1) (x : ℤ) :
    ‖AhalfTranspose₂ N P f h x‖ ≤ 1 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [AhalfTranspose₂]
  have hnorm : ‖(((N : ℝ)⁻¹ : ℝ) : ℂ)‖ = (N : ℝ)⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc ‖(((N : ℝ)⁻¹ : ℝ) : ℂ) * ∑ n ∈ Finset.Ioc (N / 2) N,
        f (x + (n : ℤ) - P.eval (n : ℤ)) * h (x - P.eval (n : ℤ))‖
      = (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.Ioc (N / 2) N,
        f (x + (n : ℤ) - P.eval (n : ℤ)) * h (x - P.eval (n : ℤ))‖ := by
        rw [norm_mul, hnorm]
    _ ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
        ‖f (x + (n : ℤ) - P.eval (n : ℤ)) * h (x - P.eval (n : ℤ))‖ := by
        gcongr; exact norm_sum_le _ _
    _ ≤ (N : ℝ)⁻¹ * ∑ _n ∈ Finset.Ioc (N / 2) N, (1 : ℝ) := by
        gcongr with n hn
        rw [norm_mul]
        exact mul_le_one₀ (hf _) (norm_nonneg _) (hh _)
    _ = (N : ℝ)⁻¹ * ((Finset.Ioc (N / 2) N).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 1 := by
        have hcard : ((Finset.Ioc (N / 2) N).card : ℝ) ≤ (N : ℝ) := by
          rw [Nat.card_Ioc]; push_cast; exact_mod_cast Nat.sub_le N (N / 2)
        calc (N : ℝ)⁻¹ * ((Finset.Ioc (N / 2) N).card : ℝ)
            ≤ (N : ℝ)⁻¹ * (N : ℝ) := by gcongr
          _ = 1 := inv_mul_cancel₀ hNpos.ne'

/-- The polynomial shift bound used for the support of the second dual function. -/
theorem eval_le_coeff_sum_of_mem_Icc (P : Polynomial ℤ) {N : ℕ} (hN : 1 ≤ N) {n : ℤ}
    (hn : n ∈ Finset.Icc (1 : ℤ) (N : ℤ)) :
    |P.eval n| ≤ (((∑ j ∈ P.support, |P.coeff j|).natAbs : ℤ)) * (N : ℤ) ^ P.natDegree := by
  have h := Work.A3.abs_eval_le_coeff_sum P hN hn
  have hsum : (0 : ℤ) ≤ ∑ j ∈ P.support, |P.coeff j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg (P.coeff j)
  have hcast : (((∑ j ∈ P.support, |P.coeff j|).natAbs : ℤ)) = ∑ j ∈ P.support, |P.coeff j| :=
    Int.natAbs_of_nonneg hsum
  rw [hcast]
  exact h

/-- Support of the second dual function: it satisfies the support bound `N₀ + Mp N^d`, where
`Mp` bounds the polynomial shifts `P(n)`, `n ≤ N`. -/
theorem supportIn_AhalfTranspose₂ {N N₀ Mp : ℕ} (P : Polynomial ℤ) {f h : ℤ → ℂ}
    (hh : SupportIn h N₀)
    (hMp : ∀ n : ℤ, n ∈ Finset.Icc (1 : ℤ) (N : ℤ) →
      |P.eval n| ≤ (Mp : ℤ) * (N : ℤ) ^ P.natDegree) :
    SupportIn (AhalfTranspose₂ N P f h) (N₀ + Mp * N ^ P.natDegree) := by
  intro x hx
  rw [AhalfTranspose₂]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun n hn => ?_)
  rw [Finset.mem_Ioc] at hn
  have hnI : (n : ℤ) ∈ Finset.Icc (1 : ℤ) (N : ℤ) := by
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hhn : h (x - P.eval (n : ℤ)) = 0 := by
    apply hh
    have hxZ : ((N₀ : ℤ) + (Mp : ℤ) * (N : ℤ) ^ P.natDegree) < |x| := by
      have h1 : ((N₀ + Mp * N ^ P.natDegree : ℕ) : ℤ) < ((x.natAbs : ℕ) : ℤ) := by
        exact_mod_cast hx
      rw [Int.natCast_natAbs] at h1
      push_cast at h1
      exact h1
    have hMpZ : |P.eval (n : ℤ)| ≤ (Mp : ℤ) * (N : ℤ) ^ P.natDegree := hMp (n : ℤ) hnI
    have htri : |x| - |P.eval (n : ℤ)| ≤ |x - P.eval (n : ℤ)| :=
      abs_sub_abs_le_abs_sub x (P.eval (n : ℤ))
    have hkey : (N₀ : ℤ) < |x - P.eval (n : ℤ)| := by linarith
    have hkey' : ((N₀ : ℤ)) < (((x - P.eval (n : ℤ)).natAbs : ℤ)) := by
      rwa [Int.natCast_natAbs]
    exact (Nat.cast_lt (α := ℤ)).mp hkey'
  rw [hhn, mul_zero]

/-! ## The elementary arithmetic of the proof -/

/-- The coefficient `1 + Cp·⟨l⟩` of the `ℓ^p`-piece times `4C₁+3` is dominated by `Y·⟨l⟩`. -/
theorem coefY_p {Cp Cp' C1 CP l : ℝ} (hCp : 0 ≤ Cp) (hCp' : 0 ≤ Cp') (hC1 : 0 < C1)
    (hCP : 1 ≤ CP) (hl : 1 ≤ l) :
    (1 + Cp * l) * (4 * C1 + 3) ≤ (1 + Cp) * (1 + Cp') * (4 * C1 + 20) * (CP + 1) * l := by
  have h1 : 1 + Cp * l ≤ (1 + Cp) * l := by nlinarith [hCp, hl]
  have h2 : (4 * C1 + 3 : ℝ) ≤ 4 * C1 + 20 := by linarith
  have h3 : (1 : ℝ) ≤ (1 + Cp') * (CP + 1) := by nlinarith [hCp', hCP]
  calc (1 + Cp * l) * (4 * C1 + 3)
      ≤ ((1 + Cp) * l) * (4 * C1 + 20) := by
        refine mul_le_mul h1 h2 (by linarith) (by positivity)
    _ ≤ ((1 + Cp) * l) * (4 * C1 + 20) * ((1 + Cp') * (CP + 1)) :=
        le_mul_of_one_le_right (by positivity) h3
    _ = (1 + Cp) * (1 + Cp') * (4 * C1 + 20) * (CP + 1) * l := by ring

/-- The coefficient `1 + Cp'·⟨l⟩` of the `ℓ^{p'}`-piece times `CP+1` is dominated by `Y·⟨l⟩`. -/
theorem coefY_p' {Cp Cp' C1 CP l : ℝ} (hCp : 0 ≤ Cp) (hCp' : 0 ≤ Cp') (hC1 : 0 < C1)
    (hCP : 1 ≤ CP) (hl : 1 ≤ l) :
    (1 + Cp' * l) * (CP + 1) ≤ (1 + Cp) * (1 + Cp') * (4 * C1 + 20) * (CP + 1) * l := by
  have h1 : 1 + Cp' * l ≤ (1 + Cp') * l := by nlinarith [hCp', hl]
  have h3 : (1 : ℝ) ≤ (1 + Cp) * (4 * C1 + 20) := by nlinarith [hCp, hC1]
  calc (1 + Cp' * l) * (CP + 1)
      ≤ ((1 + Cp') * l) * (CP + 1) :=
        mul_le_mul_of_nonneg_right h1 (by linarith)
    _ ≤ ((1 + Cp') * l) * (CP + 1) * ((1 + Cp) * (4 * C1 + 20)) :=
        le_mul_of_one_le_right (by positivity) h3
    _ = (1 + Cp) * (1 + Cp') * (4 * C1 + 20) * (CP + 1) * l := by ring

/-- The final comparison of the two error contributions with the factor `Y·(2+C2)`. -/
theorem add_two_le {Y C2 ς Nd : ℝ} (hY : 1 ≤ Y) (hNd : 1 ≤ Nd) (hς : 0 ≤ ς) (hC2 : 0 ≤ C2) :
    Y * (ς * Nd ^ (1 / 2 : ℝ)) + (1 + C2) * ς ≤ Y * (2 + C2) * (ς * Nd ^ (1 / 2 : ℝ)) := by
  have hNd12 : (1 : ℝ) ≤ Nd ^ (1 / 2 : ℝ) := Real.one_le_rpow hNd (by norm_num)
  have hYN : (1 : ℝ) ≤ Y * Nd ^ (1 / 2 : ℝ) := by nlinarith [hY, hNd12]
  have hstep : (1 + C2) * ς ≤ (1 + C2) * (Y * (ς * Nd ^ (1 / 2 : ℝ))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    calc ς = 1 * ς := by ring
      _ ≤ (Y * Nd ^ (1 / 2 : ℝ)) * ς := mul_le_mul_of_nonneg_right hYN hς
      _ = Y * (ς * Nd ^ (1 / 2 : ℝ)) := by ring
  calc Y * (ς * Nd ^ (1 / 2 : ℝ)) + (1 + C2) * ς
      ≤ Y * (ς * Nd ^ (1 / 2 : ℝ)) + (1 + C2) * (Y * (ς * Nd ^ (1 / 2 : ℝ))) :=
        add_le_add le_rfl hstep
    _ = Y * (2 + C2) * (ς * Nd ^ (1 / 2 : ℝ)) := by ring

/-- **The Riesz--Thorin interpolation of the `ℓ^p` and `ℓ^{p'}` bounds of `(1-Π)E₁` at the
exponent `2`**, with the simplification of the constant. -/
theorem interp_le {w : ℤ → ℂ} {Y δ Nd p q : ℝ} (hp : 1 < p) (hq : 1 < q)
    (hrel : 1 / p + 1 / q = 1) (hY : 0 ≤ Y) (hδ : 0 ≤ δ) (hNd : 0 ≤ Nd)
    (h₁ : eLpNorm w (ENNReal.ofReal p) Measure.count
            ≤ ENNReal.ofReal (Y * δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p)))
    (h₂ : eLpNorm w (ENNReal.ofReal q) Measure.count
            ≤ ENNReal.ofReal (Y * Nd ^ (1 / q))) :
    eLpNorm w 2 Measure.count ≤ ENNReal.ofReal (Y * δ ^ (1 / 4 : ℝ) * Nd ^ (1 / 2 : ℝ)) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hrel' : (1 : ℝ) / 2 = (1 - 1 / 2) / p + (1 / 2) / q := by
    have h2 : (1 - 1 / 2 : ℝ) / p + (1 / 2) / q = (1 / 2) * (1 / p + 1 / q) := by ring
    rw [h2, hrel, mul_one]
  have hint := Work.KMTAreas.A4.eLpNorm_two_le_of_interp (w := w) hp hq
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1) hrel'
    (M₁ := Y * δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p)) (M₂ := Y * Nd ^ (1 / q))
    (by positivity) (by positivity) h₁ h₂
  refine hint.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  exact le_of_eq (Work.KMTAreas.A4.rpowHalf_mul_rpow_rpowHalf (X := Y) hY hδ hNd hp0 hq0 hrel)

theorem propdualSecondClaim_of_structDecompClaim (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (h : Work.KMTAreas.A4Z.StructDecompClaim P) :
    Work.KMTAreas.A4Z.PropdualSecondClaim P := by
  classical
  obtain ⟨C₁, K₁, hC₁pos, hK₁pos, hStruct⟩ := h
  -- the rate `c`, chosen so that `8cK₁ = 1/4`
  set c : ℝ := 1 / (32 * K₁) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have h8cK : 8 * c * K₁ = 1 / 4 := by rw [hcdef]; field_simp; ring
  -- the exponents of the interpolation
  set K₂ : ℝ := max (2 * K₁ - 1) 1 with hK₂def
  have hK₂ge1 : 1 ≤ K₂ := le_max_right _ _
  obtain ⟨hp1, hp2, hpexp⟩ := Work.KMTAreas.A4.p_choice_facts (K := K₂) hK₂ge1
  set p : ℝ := 1 + 1 / (4 * K₂ + 2) with hpdef
  have hp1' : 1 < p := by rw [hpdef]; exact hp1
  have hp2' : p < 2 := by rw [hpdef]; exact hp2
  have hpexp' : 1 / 2 ≤ (1 + K₂) / p - K₂ := by rw [hpdef]; exact hpexp
  set p' : ℝ := p / (p - 1) with hp'def
  have hp'm1 : 1 < p' := by
    rw [hp'def, lt_div_iff₀ (by linarith : (0 : ℝ) < p - 1)]
    linarith
  have hp'0 : 0 < p' := by linarith
  have hp'm2 : 2 < p' := by
    rw [hp'def, lt_div_iff₀ (by linarith : (0 : ℝ) < p - 1)]
    linarith [hp2']
  have hpp' : 1 / p + 1 / p' = 1 := by rw [hp'def]; field_simp; ring
  have hrel : (1 : ℝ) / 2 = (1 - 1 / 2) / p + (1 / 2) / p' := by
    have h2 : (1 - 1 / 2 : ℝ) / p + (1 / 2) / p' = (1 / 2) * (1 / p + 1 / p') := by ring
    rw [h2, hpp', mul_one]
  -- the window constants of the second dual function
  set Mp : ℕ := (∑ j ∈ P.support, |P.coeff j|).natAbs with hMpdef
  set KP : ℝ := 3 * (1 + (Mp : ℝ)) with hKPdef
  have hKPge1 : 1 ≤ KP := by
    rw [hKPdef]
    have h : (0 : ℝ) ≤ (Mp : ℝ) := Nat.cast_nonneg _
    linarith
  set CP : ℝ := KP + 1 with hCPdef
  have hCPge1 : 1 ≤ CP := by rw [hCPdef]; linarith
  -- the threshold of the major-arc comparison
  obtain ⟨Lth, hLth⟩ := exists_threshold_two_pow_le C₁ hC₁pos P.natDegree hP
  refine ⟨c, hcpos, fun ρ hρ0 hρ1 => ?_⟩
  -- the constants of the Ionescu--Wainger projection bounds
  obtain ⟨Cρ2, hCρ2pos, C2, hC2pos, hpr2⟩ :=
    Work.KMTAreas.A5.kmtProj_lp_bound_A1 hA1 (p := 2) hρ0 hρ1 (by norm_num)
  obtain ⟨Cρp, hCρppos, Cp, hCppos, hprp⟩ :=
    Work.KMTAreas.A5.kmtProj_lp_bound_A1 hA1 (p := p) hρ0 hρ1 hp1'
  obtain ⟨Cρp', hCρp'pos, Cp', hCp'pos, hprp'⟩ :=
    Work.KMTAreas.A5.kmtProj_lp_bound_A1 hA1 (p := p') hρ0 hρ1 hp'm1
  obtain ⟨CρNA, hCρNApos, hNA0⟩ :=
    Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing hρ0
  set Cρ : ℝ := max 2 (max CρNA (max Cρ2 (max Cρp Cρp'))) with hCρdef
  have h2Cρ : 2 ≤ Cρ := le_max_left _ _
  have hCρNAle : CρNA ≤ Cρ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCρ2le : Cρ2 ≤ Cρ :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hCρple : Cρp ≤ Cρ :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hCρp'le : Cρp' ≤ Cρ :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hCρpos : 0 < Cρ := lt_of_lt_of_le (by norm_num) h2Cρ
  have hNonAl : ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k →
      NonAliasing k (iwArithFreqs ρ l) :=
    fun l k hk => hNA0 l k (Work.KMTAreas.A5.goodMajorArcs_mono hCρNAle hk)
  -- the threshold separating the small from the large case in `l`
  have hev1 : ∀ᶠ l : ℕ in Filter.atTop, 2 * Real.logb 2 (4 * C₁) ≤ (l : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have hev2 : ∀ᶠ l : ℕ in Filter.atTop,
      max (2 * Real.logb 2 (4 * C₁)) ((l : ℝ) + 1) ≤ (2 : ℝ) ^ (c * (l : ℝ)) :=
    Work.KMTAreas.A4.eventually_max_le_two_rpow c (2 * Real.logb 2 (4 * C₁)) hcpos
  have hev3 : ∀ᶠ l : ℕ in Filter.atTop, Lth ≤ l := Filter.eventually_ge_atTop Lth
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1 (hev1.and (hev2.and hev3))
  have hL₀₁ : ∀ l : ℕ, L₀ ≤ l → 2 * Real.logb 2 (4 * C₁) ≤ (l : ℝ) := fun l hl => (hL₀ l hl).1
  have hL₀₂ : ∀ l : ℕ, L₀ ≤ l →
      max (2 * Real.logb 2 (4 * C₁)) ((l : ℝ) + 1) ≤ (2 : ℝ) ^ (c * (l : ℝ)) :=
    fun l hl => (hL₀ l hl).2.1
  have hL₀₃ : ∀ l : ℕ, L₀ ≤ l → Lth ≤ l := fun l hl => (hL₀ l hl).2.2
  -- the final constants
  set Y : ℝ := (1 + (Cp : ℝ)) * (1 + (Cp' : ℝ)) * (4 * C₁ + 20) * (CP + 1) with hYdef
  have hYge1 : 1 ≤ Y := by
    rw [hYdef]
    have h1 : (1 : ℝ) ≤ 1 + (Cp : ℝ) := by linarith [hCppos.le]
    have h2 : (1 : ℝ) ≤ 1 + (Cp' : ℝ) := by linarith [hCp'pos.le]
    have h3 : (1 : ℝ) ≤ 4 * C₁ + 20 := by linarith [hC₁pos.le]
    have h4 : (1 : ℝ) ≤ CP + 1 := by linarith [hCPge1]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le h1 h2) h3) h4
  have hYpos : 0 < Y := lt_of_lt_of_le one_pos hYge1
  set Cf : ℝ := max (max ((1 + (C2 : ℝ) * ((L₀ : ℝ) + 1)) * CP * 3 * (2 : ℝ) ^ (c * (L₀ : ℝ)))
    (Y * (2 + (C2 : ℝ)))) 1 with hCfdef
  have hCf1 : 1 ≤ Cf := le_max_right _ _
  have hCfpos : 0 < Cf := lt_of_lt_of_le one_pos hCf1
  have hCfsmall : (1 + (C2 : ℝ) * ((L₀ : ℝ) + 1)) * CP * 3 * (2 : ℝ) ^ (c * (L₀ : ℝ)) ≤ Cf :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hCflarge : Y * (2 + (C2 : ℝ)) ≤ Cf := le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨Cρ, hCρpos, ⟨Cf.toNNReal, ?_, ?_⟩⟩
  · rw [← NNReal.coe_pos, Real.coe_toNNReal Cf hCfpos.le]; exact hCfpos
  intro N N₀ l f h₂ hN hN0lo hN0hi hfs hhs hf1 hh1 hgood
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  set Nd : ℝ := (N : ℝ) ^ P.natDegree with hNddef
  have hNdpos : 0 < Nd := by rw [hNddef]; positivity
  have hNd1 : 1 ≤ Nd := by rw [hNddef]; exact one_le_pow₀ (by exact_mod_cast hN)
  have hN0leNd : (N₀ : ℝ) ≤ Nd := by rw [hNddef]; exact hN0hi
  set kk : ℤ := (P.natDegree : ℤ) * ((l : ℤ) - logN N) with hkkdef
  have hgood' : GoodMajorArcs ρ Cρ l kk := by rw [hkkdef]; exact hgood
  -- rewrite the goal in the local notation
  change eLpNorm (fun x : ℤ => AhalfTranspose₂ N P f h₂ x
      - kmtProj ρ l kk (fun y : ℤ => AhalfTranspose₂ N P f h₂ y) x) 2 Measure.count
    ≤ ((Cf.toNNReal : ℝ≥0) : ℝ≥0∞)
        * ENNReal.ofReal (2 ^ (-(c * (l : ℝ))) * ((N : ℝ) ^ P.natDegree) ^ (1 / 2 : ℝ))
  rw [← hNddef]
  -- spatial support and pointwise bound of the second dual function
  have hMp : ∀ n : ℤ, n ∈ Finset.Icc (1 : ℤ) (N : ℤ) →
      |P.eval n| ≤ (Mp : ℤ) * (N : ℤ) ^ P.natDegree := by
    intro n hn
    rw [hMpdef]
    exact eval_le_coeff_sum_of_mem_Icc P hN hn
  have hAsupp : SupportIn (AhalfTranspose₂ N P f h₂) (N₀ + Mp * N ^ P.natDegree) :=
    supportIn_AhalfTranspose₂ P hhs hMp
  have hApt : ∀ x : ℤ, ‖AhalfTranspose₂ N P f h₂ x‖ ≤ 1 :=
    fun x => norm_AhalfTranspose₂_le_one hN P hf1 hh1 x
  -- the `ℓ^r` bound of the second dual function
  have hwin : ∀ {r : ℝ}, 1 ≤ r →
      eLpNorm (fun x : ℤ => AhalfTranspose₂ N P f h₂ x) (ENNReal.ofReal r) Measure.count
        ≤ ENNReal.ofReal (CP * Nd ^ (1 / r)) := by
    intro r hr
    refine (supportIn_eLpNorm_le hAsupp hApt hr).trans (ENNReal.ofReal_le_ofReal ?_)
    have hMcast : (((2 * (N₀ + Mp * N ^ P.natDegree) + 1 : ℕ)) : ℝ)
        = 2 * (N₀ : ℝ) + 2 * (Mp : ℝ) * Nd + 1 := by
      rw [hNddef]; push_cast; ring
    have hMle : (((2 * (N₀ + Mp * N ^ P.natDegree) + 1 : ℕ)) : ℝ) ≤ KP * Nd := by
      rw [hMcast, hKPdef]
      have h1 : (N₀ : ℝ) ≤ Nd := hN0leNd
      have h2 : (1 : ℝ) ≤ Nd := hNd1
      have h3 : (0 : ℝ) ≤ (Mp : ℝ) := Nat.cast_nonneg _
      nlinarith [h1, h2, h3]
    have hKPr : KP ^ (1 / r) ≤ CP := by
      have hle1 : 1 / r ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      calc KP ^ (1 / r) ≤ KP ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hKPge1 hle1
        _ = KP := Real.rpow_one KP
        _ ≤ CP := by rw [hCPdef]; linarith
    calc (((2 * (N₀ + Mp * N ^ P.natDegree) + 1 : ℕ)) : ℝ) ^ (1 / r)
        ≤ (KP * Nd) ^ (1 / r) := Real.rpow_le_rpow (by positivity) hMle (by positivity)
      _ = KP ^ (1 / r) * Nd ^ (1 / r) := Real.mul_rpow (by positivity) hNdpos.le
      _ ≤ CP * Nd ^ (1 / r) := mul_le_mul_of_nonneg_right hKPr (by positivity)
  -- the `ℓ²` bound of the Ionescu--Wainger projection
  have hproj_2 : ∀ u : ℤ → ℂ, eLpNorm (kmtProj ρ l kk u) 2 Measure.count
      ≤ ENNReal.ofReal (C2 : ℝ) * ENNReal.ofReal (angleBracket l : ℝ)
          * eLpNorm u 2 Measure.count := by
    intro u
    have hh := hpr2 l kk (Work.KMTAreas.A5.goodMajorArcs_mono hCρ2le hgood') u
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num] at hh
    exact hh
  -- the goal in the normalised form
  have hConvert : ((Cf.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal Cf := by
    rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal Cf hCfpos.le]
  suffices hmain : eLpNorm (fun x : ℤ => AhalfTranspose₂ N P f h₂ x
        - kmtProj ρ l kk (fun y : ℤ => AhalfTranspose₂ N P f h₂ y) x) 2 Measure.count
      ≤ ENNReal.ofReal (Cf * ((2 : ℝ) ^ (-(c * (l : ℝ))) * Nd ^ (1 / 2 : ℝ))) by
    rw [hConvert, ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ Cf from hCfpos.le)]
    exact hmain
  by_cases hsl : l < L₀
  · -- ## small `l`: the trivial bound
    have hA2 := hwin (r := 2) (by norm_num : (1 : ℝ) ≤ 2)
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num] at hA2
    have hangle_le : (angleBracket l : ℝ) ≤ (L₀ : ℝ) + 1 :=
      (angleBracket_coe_le_succ l).trans (by exact_mod_cast (Nat.add_le_add_right hsl.le 1))
    have hprojAst : eLpNorm (fun x : ℤ => kmtProj ρ l kk (fun y : ℤ => AhalfTranspose₂ N P f h₂ y) x)
          2 Measure.count
        ≤ ENNReal.ofReal (C2 : ℝ) * ENNReal.ofReal (angleBracket l : ℝ)
            * ENNReal.ofReal (CP * Nd ^ (1 / 2 : ℝ)) :=
      (hproj_2 _).trans (mul_le_mul_of_nonneg_left hA2 (by positivity))
    have hsmall : eLpNorm (fun x : ℤ => AhalfTranspose₂ N P f h₂ x
          - kmtProj ρ l kk (fun y : ℤ => AhalfTranspose₂ N P f h₂ y) x) 2 Measure.count
        ≤ ENNReal.ofReal ((1 + (C2 : ℝ) * (angleBracket l : ℝ)) * (CP * Nd ^ (1 / 2 : ℝ))) := by
      refine (eLpNorm_sub_le_count (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans ?_
      refine (add_le_add hA2 hprojAst).trans ?_
      rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (C2 : ℝ) from hC2pos.le),
        ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (C2 : ℝ) * (angleBracket l : ℝ) from by positivity),
        ← ENNReal.ofReal_add (by positivity)
          (by positivity : (0 : ℝ) ≤ (C2 : ℝ) * (angleBracket l : ℝ) * (CP * Nd ^ (1 / 2 : ℝ)))]
      exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
    refine hsmall.trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : (1 : ℝ) ≤ 3 * (2 : ℝ) ^ (c * (L₀ : ℝ)) * (2 : ℝ) ^ (-(c * (l : ℝ))) := by
      have hlr : (l : ℝ) ≤ (L₀ : ℝ) := by exact_mod_cast hsl.le
      have h3 : 3 * (2 : ℝ) ^ (c * (L₀ : ℝ)) * (2 : ℝ) ^ (-(c * (l : ℝ)))
          = 3 * (2 : ℝ) ^ (c * ((L₀ : ℝ) - (l : ℝ))) := by
        rw [show 3 * (2 : ℝ) ^ (c * (L₀ : ℝ)) * (2 : ℝ) ^ (-(c * (l : ℝ)))
              = 3 * ((2 : ℝ) ^ (c * (L₀ : ℝ)) * (2 : ℝ) ^ (-(c * (l : ℝ)))) by ring,
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1; ring
      rw [h3]
      have h4 : (1 : ℝ) ≤ (2 : ℝ) ^ (c * ((L₀ : ℝ) - (l : ℝ))) :=
        Real.one_le_rpow (by norm_num) (by nlinarith [hcpos, hlr])
      nlinarith [h4]
    have hkey : (1 + (C2 : ℝ) * (angleBracket l : ℝ)) * CP ≤ Cf * (2 : ℝ) ^ (-(c * (l : ℝ))) := by
      calc (1 + (C2 : ℝ) * (angleBracket l : ℝ)) * CP
          ≤ (1 + (C2 : ℝ) * ((L₀ : ℝ) + 1)) * CP := by
            have hle : 1 + (C2 : ℝ) * (angleBracket l : ℝ)
                ≤ 1 + (C2 : ℝ) * ((L₀ : ℝ) + 1) :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_left hangle_le hC2pos.le)
            exact mul_le_mul_of_nonneg_right hle (by linarith)
        _ ≤ (1 + (C2 : ℝ) * ((L₀ : ℝ) + 1)) * CP
              * (3 * (2 : ℝ) ^ (c * (L₀ : ℝ)) * (2 : ℝ) ^ (-(c * (l : ℝ)))) := by
            have hpos : (0 : ℝ) ≤ (1 + (C2 : ℝ) * ((L₀ : ℝ) + 1)) * CP := by positivity
            calc (1 + (C2 : ℝ) * ((L₀ : ℝ) + 1)) * CP
                = (1 + (C2 : ℝ) * ((L₀ : ℝ) + 1)) * CP * 1 := by ring
              _ ≤ (1 + (C2 : ℝ) * ((L₀ : ℝ) + 1)) * CP
                    * (3 * (2 : ℝ) ^ (c * (L₀ : ℝ)) * (2 : ℝ) ^ (-(c * (l : ℝ)))) :=
                  mul_le_mul_of_nonneg_left h2 hpos
        _ = ((1 + (C2 : ℝ) * ((L₀ : ℝ) + 1)) * CP * 3 * (2 : ℝ) ^ (c * (L₀ : ℝ)))
              * (2 : ℝ) ^ (-(c * (l : ℝ))) := by ring
        _ ≤ Cf * (2 : ℝ) ^ (-(c * (l : ℝ))) :=
            mul_le_mul_of_nonneg_right hCfsmall (by positivity)
    calc (1 + (C2 : ℝ) * (angleBracket l : ℝ)) * (CP * Nd ^ (1 / 2 : ℝ))
        = ((1 + (C2 : ℝ) * (angleBracket l : ℝ)) * CP) * Nd ^ (1 / 2 : ℝ) := by ring
      _ ≤ (Cf * (2 : ℝ) ^ (-(c * (l : ℝ)))) * Nd ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = Cf * ((2 : ℝ) ^ (-(c * (l : ℝ))) * Nd ^ (1 / 2 : ℝ)) := by ring
  · -- ## large `l`: the structure theorem
    have hlL : L₀ ≤ l := not_lt.mp hsl
    have hmax := max_le_iff.mp (hL₀₂ l hlL)
    have hangleL : (angleBracket l : ℝ) ≤ (2 : ℝ) ^ (c * (l : ℝ)) :=
      (angleBracket_coe_le_succ l).trans hmax.2
    have hLthL : Lth ≤ l := hL₀₃ l hlL
    set δ : ℝ := (2 : ℝ) ^ (-(8 * c * (l : ℝ))) with hδdef
    have hδpos : 0 < δ := by rw [hδdef]; positivity
    have hδ1 : δ ≤ 1 := by
      rw [hδdef]
      refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
      have : (0 : ℝ) ≤ 8 * c * (l : ℝ) := by
        have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
        positivity
      linarith
    have hδinv_pos : (0 : ℝ) < δ⁻¹ := inv_pos.mpr hδpos
    have hδinv_ge : (1 : ℝ) ≤ δ⁻¹ := (one_le_inv₀ hδpos).mpr hδ1
    have hδinv : δ⁻¹ = (2 : ℝ) ^ (8 * c * (l : ℝ)) := by
      rw [hδdef, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1; ring
    have hδinvK : δ⁻¹ ^ K₁ = (2 : ℝ) ^ ((l : ℝ) / 4) := by
      rw [hδinv, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      rw [show 8 * c * (l : ℝ) * K₁ = (8 * c * K₁) * (l : ℝ) by ring, h8cK]
      ring
    have hδquarter : δ ^ (1 / 4 : ℝ) = (2 : ℝ) ^ (-(2 * c * (l : ℝ))) := by
      rw [hδdef, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1; ring
    -- the structure theorem
    obtain ⟨ι, hι, s, φ, lam, w, E₁, E₂, hφmem, hlam, hw0, hwsum, hE1, hE2, hpt⟩ :=
      hStruct ρ hρ0 hρ1 N N₀ δ f h₂ hN hδpos hδ1 hN0lo hN0hi hfs hhs hf1 hh1
    have hE1sum : Summable (fun x : ℤ => ‖E₁ x‖) := hE1.1
    have hE1le : ∑' x : ℤ, ‖E₁ x‖ ≤ δ * Nd := by
      have h := hE1.2; rwa [← hNddef] at h
    have hE2pt : ∀ x : ℤ, ‖E₂ x‖ ≤ δ :=
      fun x => (lp.norm_apply_le_norm (p := 2) (by norm_num) E₂ x).trans hE2
    have hE2norm : eLpNorm (fun x : ℤ => E₂ x) 2 Measure.count ≤ ENNReal.ofReal δ := by
      rw [Work.KMTAreas.A4.eLpNorm_count_eq_lp_norm E₂]
      exact ENNReal.ofReal_le_ofReal hE2
    -- every structure function is fixed by the projection
    have hkill : ∀ i ∈ s, kmtProj ρ l kk (fun x : ℤ => φ i x) = fun x : ℤ => φ i x := by
      intro i hi
      obtain ⟨-, hφsum, -, li, ki, hφsupp, hφli, hφki⟩ := hφmem i hi
      have hli' : (2 : ℝ) ^ li ≤ C₁ * (2 : ℝ) ^ ((l : ℝ) / 4) := by
        have hh := hφli; rwa [hδinvK] at hh
      have hki' : (2 : ℝ) ^ ki ≤ C₁ * (2 : ℝ) ^ ((l : ℝ) / 4) / Nd := by
        have hh := hφki; rw [hδinvK] at hh; rwa [← hNddef] at hh
      obtain ⟨hli_le, hki_le⟩ := hLth l li ki N hLthL hN hli' hki'
      have hsupp' : FourierSupportIn (fun x : ℤ => φ i x) (majorArc ρ l (kk - 1)) :=
        FourierSupportIn.mono
          (majorArc_mono_of_subset (iwArithFreqs_mono hρ0 hρ1 hli_le)
            (by rw [hkkdef]; exact hki_le)) hφsupp
      exact Work.KMTAreas.A4.kmtProjEqSelf hρ0 hρ1 h2Cρ hNonAl hgood' hφsum hsupp'
    have hφBpt : ∀ i ∈ s, ∀ x : ℤ, ‖φ i x‖ ≤ C₁ * δ⁻¹ ^ K₁ :=
      fun i hi x => (hφmem i hi).1 x
    have hφB : ∀ i ∈ s, BoundedZ (fun x : ℤ => φ i x) :=
      fun i hi => ⟨C₁ * δ⁻¹ ^ K₁, hφBpt i hi⟩
    have hkillw : ∀ i ∈ s,
        kmtProj ρ l kk (fun x : ℤ => (w i : ℂ) * ((lam i) * φ i x))
          = fun x : ℤ => (w i : ℂ) * ((lam i) * φ i x) := by
      intro i hi
      have hb2 : BoundedZ (fun x : ℤ => (lam i) * φ i x) :=
        ⟨‖lam i‖ * (C₁ * δ⁻¹ ^ K₁), fun x => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hφBpt i hi x) (norm_nonneg _)⟩
      have h1 : kmtProj ρ l kk (fun x : ℤ => (lam i) * φ i x)
          = fun x : ℤ => (lam i) * φ i x := by
        have hh := kmtProj_smul_bounded ρ l kk (lam i) (hφB i hi)
        rw [hkill i hi] at hh
        exact hh
      have h2 := kmtProj_smul_bounded ρ l kk (((w i : ℝ)) : ℂ) hb2
      rw [h1] at h2
      exact h2
    -- the pointwise bound of the structure sum
    set BndS : ℝ := 4 * C₁ * δ ^ (-(2 * K₁ - 1)) with hBndSdef
    have hBndSeq : 4 * δ⁻¹ ^ (K₁ - 1) * (C₁ * δ⁻¹ ^ K₁) = BndS := by
      rw [hBndSdef]
      rw [show 4 * δ⁻¹ ^ (K₁ - 1) * (C₁ * δ⁻¹ ^ K₁)
          = 4 * C₁ * (δ⁻¹ ^ (K₁ - 1) * δ⁻¹ ^ K₁) by ring]
      rw [← Real.rpow_add hδinv_pos, show K₁ - 1 + K₁ = 2 * K₁ - 1 by ring]
      rw [Real.inv_rpow hδpos.le, Real.rpow_neg hδpos.le]
    have hSumBound : ∀ t : Finset ι, t ⊆ s → ∀ x : ℤ,
        ‖∑ i ∈ t, (w i : ℂ) * ((lam i) * φ i x)‖ ≤ BndS := by
      intro t ht x
      have hterm : ∀ i ∈ t, ‖(w i : ℂ) * ((lam i) * φ i x)‖
          ≤ w i * (4 * δ⁻¹ ^ (K₁ - 1) * (C₁ * δ⁻¹ ^ K₁)) := by
        intro i hi
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw0 i)]
        refine mul_le_mul_of_nonneg_left ?_ (hw0 i)
        exact mul_le_mul (hlam i (ht hi)) ((hφmem i (ht hi)).1 x) (norm_nonneg _)
          (by positivity)
      calc ‖∑ i ∈ t, (w i : ℂ) * ((lam i) * φ i x)‖
          ≤ ∑ i ∈ t, ‖(w i : ℂ) * ((lam i) * φ i x)‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ t, w i * (4 * δ⁻¹ ^ (K₁ - 1) * (C₁ * δ⁻¹ ^ K₁)) := Finset.sum_le_sum hterm
        _ = (∑ i ∈ t, w i) * (4 * δ⁻¹ ^ (K₁ - 1) * (C₁ * δ⁻¹ ^ K₁)) := (Finset.sum_mul ..).symm
        _ ≤ 1 * BndS := by
            refine mul_le_mul ?_ (le_of_eq hBndSeq) (by positivity) (by norm_num)
            exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ t)
              (fun i _ _ => hw0 i)).trans hwsum
        _ = BndS := one_mul _
    have hSfix : ∀ t : Finset ι, t ⊆ s →
        kmtProj ρ l kk (fun x : ℤ => ∑ i ∈ t, (w i : ℂ) * ((lam i) * φ i x))
          = fun x : ℤ => ∑ i ∈ t, (w i : ℂ) * ((lam i) * φ i x) := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · intro _
        have h0 : (fun x : ℤ => ∑ i ∈ (∅ : Finset ι), (w i : ℂ) * ((lam i) * φ i x)) = 0 := by
          funext x; simp
        rw [h0, Work.KMTContract.kmtProj_zero]
      · intro a t hat ih ht
        have hts : t ⊆ s := fun i hi => ht (Finset.mem_insert_of_mem hi)
        have has : a ∈ s := ht (Finset.mem_insert_self a t)
        have hwa1 : w a ≤ 1 :=
          (Finset.single_le_sum (fun i _ => hw0 i) (Finset.mem_univ a)).trans hwsum
        have hsplit : (fun x : ℤ => ∑ i ∈ insert a t, (w i : ℂ) * ((lam i) * φ i x))
            = (fun x : ℤ => (w a : ℂ) * ((lam a) * φ a x))
              + (fun x : ℤ => ∑ i ∈ t, (w i : ℂ) * ((lam i) * φ i x)) := by
          funext x
          rw [Pi.add_apply, Finset.sum_insert hat]
        have hbhead : BoundedZ (fun x : ℤ => (w a : ℂ) * ((lam a) * φ a x)) := by
          refine ⟨BndS, fun x => ?_⟩
          calc ‖(w a : ℂ) * ((lam a) * φ a x)‖
              = w a * (‖lam a‖ * ‖φ a x‖) := by
                rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw0 a)]
            _ ≤ 1 * ((4 * δ⁻¹ ^ (K₁ - 1)) * (C₁ * δ⁻¹ ^ K₁)) := by
                refine mul_le_mul hwa1 (mul_le_mul (hlam a has) ((hφmem a has).1 x)
                  (norm_nonneg _) ?_) (by positivity) (by norm_num)
                exact (by positivity)
            _ = BndS := by rw [one_mul, hBndSeq]
        rw [hsplit]
        rw [kmtProj_add_bounded ρ l kk hbhead ⟨BndS, hSumBound t hts⟩]
        rw [hkillw a has, ih hts]
    have hS : kmtProj ρ l kk (fun x : ℤ => ∑ i ∈ s, (w i : ℂ) * ((lam i) * φ i x))
        = fun x : ℤ => ∑ i ∈ s, (w i : ℂ) * ((lam i) * φ i x) := hSfix s (fun i hi => hi)
    -- the pointwise decomposition
    have hdecomp : (fun x : ℤ => AhalfTranspose₂ N P f h₂ x)
        = (fun x : ℤ => ∑ i ∈ s, (w i : ℂ) * ((lam i) * φ i x))
          + (fun x : ℤ => E₁ x) + (fun x : ℤ => E₂ x) := by
      funext x
      have h := hpt x
      have h1 : ((∑ i ∈ s, w i • (lam i • φ i) : L2Z) : ℤ → ℂ) x
          = ∑ i ∈ s, (w i : ℂ) * ((lam i) * (φ i : ℤ → ℂ) x) := by
        rw [lp.coeFn_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lp.coeFn_smul, Pi.smul_apply, lp.coeFn_smul, Pi.smul_apply, Complex.real_smul]
        ring
      rw [h1] at h
      simpa only [Pi.add_apply] using h
    have hE2B : BoundedZ (fun x : ℤ => E₂ x) := ⟨δ, hE2pt⟩
    have hSfB : BoundedZ (fun x : ℤ => ∑ i ∈ s, (w i : ℂ) * ((lam i) * φ i x)) :=
      ⟨BndS, hSumBound s (fun i hi => hi)⟩
    have hE1ptB : ∀ x : ℤ, ‖E₁ x‖ ≤ 1 + BndS + δ := by
      intro x
      have hx : E₁ x = AhalfTranspose₂ N P f h₂ x
          - (∑ i ∈ s, (w i : ℂ) * ((lam i) * φ i x)) - E₂ x := by
        have h := congrFun hdecomp x
        simp only [Pi.add_apply] at h
        rw [h]; ring
      rw [hx]
      calc ‖AhalfTranspose₂ N P f h₂ x - (∑ i ∈ s, (w i : ℂ) * ((lam i) * φ i x)) - E₂ x‖
          ≤ ‖AhalfTranspose₂ N P f h₂ x‖ + ‖∑ i ∈ s, (w i : ℂ) * ((lam i) * φ i x)‖ + ‖E₂ x‖ :=
            (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
        _ ≤ 1 + BndS + δ :=
            add_le_add (add_le_add (hApt x) (hSumBound s (fun i hi => hi) x)) (hE2pt x)
    have hE1B : BoundedZ (fun x : ℤ => E₁ x) := ⟨1 + BndS + δ, hE1ptB⟩
    have hPAsplit : kmtProj ρ l kk (fun x : ℤ => AhalfTranspose₂ N P f h₂ x)
        = (fun x : ℤ => ∑ i ∈ s, (w i : ℂ) * ((lam i) * φ i x))
          + (fun x : ℤ => kmtProj ρ l kk (fun y : ℤ => E₁ y) x)
          + (fun x : ℤ => kmtProj ρ l kk (fun y : ℤ => E₂ y) x) := by
      rw [hdecomp, kmtProj_add_bounded ρ l kk (boundedZ_add hSfB hE1B) hE2B,
        kmtProj_add_bounded ρ l kk hSfB hE1B, hS]
    have hdiff : (fun x : ℤ => AhalfTranspose₂ N P f h₂ x
          - kmtProj ρ l kk (fun x : ℤ => AhalfTranspose₂ N P f h₂ x) x)
        = (fun x : ℤ => E₁ x - kmtProj ρ l kk (fun y : ℤ => E₁ y) x)
          + (fun x : ℤ => E₂ x - kmtProj ρ l kk (fun y : ℤ => E₂ y) x) := by
      funext x
      have h1 := congrFun hdecomp x
      have h2 := congrFun hPAsplit x
      simp only [Pi.add_apply] at h1 h2 ⊢
      rw [h1, h2]; ring
    -- the `ℓ²` bound of the `ℓ²`-error
    have hE2part : eLpNorm (fun x : ℤ => E₂ x - kmtProj ρ l kk (fun y : ℤ => E₂ y) x)
          2 Measure.count
        ≤ ENNReal.ofReal ((1 + (C2 : ℝ)) * (angleBracket l : ℝ) * δ) := by
      have hsub := eLpNorm_sub_le_count (u := fun x : ℤ => E₂ x)
        (v := fun x : ℤ => kmtProj ρ l kk (fun y : ℤ => E₂ y) x) (q := 2) (by norm_num)
      have hprojE2 : eLpNorm (fun x : ℤ => kmtProj ρ l kk (fun y : ℤ => E₂ y) x) 2 Measure.count
          ≤ ENNReal.ofReal (C2 : ℝ) * ENNReal.ofReal (angleBracket l : ℝ) * ENNReal.ofReal δ :=
        (hproj_2 _).trans (mul_le_mul_of_nonneg_left hE2norm (by positivity))
      refine (hsub.trans (add_le_add hE2norm hprojE2)).trans ?_
      rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (C2 : ℝ) from hC2pos.le),
        ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (C2 : ℝ) * (angleBracket l : ℝ) from by positivity),
        ← ENNReal.ofReal_add hδpos.le (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : (1 : ℝ) ≤ (angleBracket l : ℝ) := one_le_angleBracket_coe l
      have hfac : (1 + (C2 : ℝ) * (angleBracket l : ℝ)) ≤ (1 + (C2 : ℝ)) * (angleBracket l : ℝ) := by
        rw [add_mul, one_mul]; exact add_le_add_left h1 _
      calc δ + (C2 : ℝ) * (angleBracket l : ℝ) * δ
          = (1 + (C2 : ℝ) * (angleBracket l : ℝ)) * δ := by ring
        _ ≤ ((1 + (C2 : ℝ)) * (angleBracket l : ℝ)) * δ :=
            mul_le_mul_of_nonneg_right hfac hδpos.le
        _ = (1 + (C2 : ℝ)) * (angleBracket l : ℝ) * δ := by ring
    -- the `ℓ^p` bound of `E₁`
    have hE1p : eLpNorm (fun x : ℤ => E₁ x) (ENNReal.ofReal p) Measure.count
        ≤ ENNReal.ofReal ((4 * C₁ + 3) * δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p)) := by
      refine (Work.KMTAreas.A4.eLpNorm_le_of_l1_and_bounded (f := fun x : ℤ => E₁ x)
        (A := δ * Nd) (B := (4 * C₁ + 2) * δ ^ (-K₂)) (r := p) (by positivity) (by positivity)
        hp1'.le hE1sum hE1le ?_).trans (ENNReal.ofReal_le_ofReal ?_)
      · intro x
        have hBndSle : BndS ≤ 4 * C₁ * δ ^ (-K₂) := by
          rw [hBndSdef]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [show δ ^ (-(2 * K₁ - 1)) = δ⁻¹ ^ (2 * K₁ - 1) by
                rw [Real.inv_rpow hδpos.le, Real.rpow_neg hδpos.le],
            show δ ^ (-K₂) = δ⁻¹ ^ K₂ by
                rw [Real.inv_rpow hδpos.le, Real.rpow_neg hδpos.le]]
          exact Real.rpow_le_rpow_of_exponent_le hδinv_ge (le_max_left _ _)
        have hδK : (1 : ℝ) ≤ δ ^ (-K₂) := by
          rw [show δ ^ (-K₂) = δ⁻¹ ^ K₂ by rw [Real.inv_rpow hδpos.le, Real.rpow_neg hδpos.le]]
          exact Real.one_le_rpow hδinv_ge (le_trans zero_le_one hK₂ge1)
        have hδle : δ ≤ δ ^ (-K₂) := le_trans hδ1 hδK
        calc ‖E₁ x‖ ≤ 1 + BndS + δ := hE1ptB x
          _ ≤ 1 + 4 * C₁ * δ ^ (-K₂) + δ := by linarith [hBndSle]
          _ ≤ 2 * δ ^ (-K₂) + 4 * C₁ * δ ^ (-K₂) := by linarith [hδK, hδle]
          _ = (4 * C₁ + 2) * δ ^ (-K₂) := by ring
      · exact rpow_prod_le hδpos hNdpos hC₁pos hp1' hpexp' hδ1
    -- the `ℓ^p` bound of `(1 - Π)E₁`
    have hE1pX : eLpNorm (fun x : ℤ => E₁ x - kmtProj ρ l kk (fun y : ℤ => E₁ y) x)
          (ENNReal.ofReal p) Measure.count
        ≤ ENNReal.ofReal (Y * (angleBracket l : ℝ) * δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p)) := by
      have hprojE1 : eLpNorm (fun x : ℤ => kmtProj ρ l kk (fun y : ℤ => E₁ y) x)
            (ENNReal.ofReal p) Measure.count
          ≤ ENNReal.ofReal (Cp : ℝ) * ENNReal.ofReal (angleBracket l : ℝ)
              * ENNReal.ofReal ((4 * C₁ + 3) * δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p)) :=
        (hprp l kk (Work.KMTAreas.A5.goodMajorArcs_mono hCρple hgood')
          (fun y : ℤ => E₁ y)).trans (mul_le_mul_of_nonneg_left hE1p (by positivity))
      refine (eLpNorm_sub_le_count (u := fun x : ℤ => E₁ x)
        (v := fun x : ℤ => kmtProj ρ l kk (fun y : ℤ => E₁ y) x)
        (q := ENNReal.ofReal p) ?_).trans ?_
      · rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1'.le
      · refine (add_le_add hE1p hprojE1).trans ?_
        rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (Cp : ℝ) from hCppos.le),
          ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (Cp : ℝ) * (angleBracket l : ℝ) from by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : (1 : ℝ) ≤ (angleBracket l : ℝ) := one_le_angleBracket_coe l
        have hcoef := coefY_p (Cp := (Cp : ℝ)) (Cp' := (Cp' : ℝ)) (C1 := C₁) (CP := CP)
          (l := (angleBracket l : ℝ)) hCppos.le hCp'pos.le hC₁pos (by linarith [hCPge1]) h1
        have hZ : (0 : ℝ) ≤ δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p) := by positivity
        calc (4 * C₁ + 3) * δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p)
              + (Cp : ℝ) * (angleBracket l : ℝ) * ((4 * C₁ + 3) * δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p))
            = ((1 + (Cp : ℝ) * (angleBracket l : ℝ)) * (4 * C₁ + 3)) * (δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p)) := by
              ring
          _ ≤ Y * (angleBracket l : ℝ) * δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p) := by
              have h := mul_le_mul_of_nonneg_right hcoef hZ
              calc ((1 + (Cp : ℝ) * (angleBracket l : ℝ)) * (4 * C₁ + 3)) * (δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p))
                  ≤ ((1 + (Cp : ℝ)) * (1 + (Cp' : ℝ)) * (4 * C₁ + 20) * (CP + 1) * (angleBracket l : ℝ))
                    * (δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p)) := h
                _ = Y * (angleBracket l : ℝ) * δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p) := by
                    rw [hYdef]; ring
    -- the `ℓ^{p'}` bound of `(1 - Π)E₁`
    have hE1p'X : eLpNorm (fun x : ℤ => E₁ x - kmtProj ρ l kk (fun y : ℤ => E₁ y) x)
          (ENNReal.ofReal p') Measure.count
        ≤ ENNReal.ofReal (Y * (angleBracket l : ℝ) * Nd ^ (1 / p')) := by
      have hA2p' : eLpNorm (fun x : ℤ => AhalfTranspose₂ N P f h₂ x) (ENNReal.ofReal p')
          Measure.count ≤ ENNReal.ofReal (CP * Nd ^ (1 / p')) := hwin (le_of_lt hp'm1)
      have hnd' : (1 : ℝ) ≤ Nd ^ (1 / p') := Real.one_le_rpow hNd1 (by positivity)
      have hA2diff : eLpNorm (fun x : ℤ => AhalfTranspose₂ N P f h₂ x
            - kmtProj ρ l kk (fun y : ℤ => AhalfTranspose₂ N P f h₂ y) x)
            (ENNReal.ofReal p') Measure.count
          ≤ ENNReal.ofReal ((1 + (Cp' : ℝ) * (angleBracket l : ℝ)) * (CP * Nd ^ (1 / p'))) := by
        refine (eLpNorm_sub_le_count (q := ENNReal.ofReal p') ?_).trans ?_
        · rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp'm1.le
        · have hproj := (hprp' l kk (Work.KMTAreas.A5.goodMajorArcs_mono hCρp'le hgood')
              (fun y : ℤ => AhalfTranspose₂ N P f h₂ y)).trans
              (mul_le_mul_of_nonneg_left hA2p' (by positivity))
          refine (add_le_add hA2p' hproj).trans ?_
          rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (Cp' : ℝ) from hCp'pos.le),
              ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (Cp' : ℝ) * (angleBracket l : ℝ) from by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
      have hE2diff : eLpNorm (fun x : ℤ => E₂ x - kmtProj ρ l kk (fun y : ℤ => E₂ y) x)
            (ENNReal.ofReal p') Measure.count
          ≤ ENNReal.ofReal ((1 + (Cp' : ℝ) * (angleBracket l : ℝ)) * δ) := by
        have hE2p' : eLpNorm (fun x : ℤ => E₂ x) (ENNReal.ofReal p') Measure.count
            ≤ ENNReal.ofReal δ :=
          (Work.KMTAreas.A4.eLpNorm_count_le_of_two_le
            (f := fun x : ℤ => E₂ x) hp'm2.le).trans hE2norm
        refine (eLpNorm_sub_le_count (q := ENNReal.ofReal p') ?_).trans ?_
        · rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp'm1.le
        · have hproj := (hprp' l kk (Work.KMTAreas.A5.goodMajorArcs_mono hCρp'le hgood')
              (fun y : ℤ => E₂ y)).trans (mul_le_mul_of_nonneg_left hE2p' (by positivity))
          refine (add_le_add hE2p' hproj).trans ?_
          rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (Cp' : ℝ) from hCp'pos.le),
              ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (Cp' : ℝ) * (angleBracket l : ℝ) from by positivity),
              ← ENNReal.ofReal_add hδpos.le (by positivity)]
          exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
      have hrew : (fun x : ℤ => E₁ x - kmtProj ρ l kk (fun y : ℤ => E₁ y) x)
          = (fun x : ℤ => AhalfTranspose₂ N P f h₂ x
              - kmtProj ρ l kk (fun y : ℤ => AhalfTranspose₂ N P f h₂ y) x)
            - (fun x : ℤ => E₂ x - kmtProj ρ l kk (fun y : ℤ => E₂ y) x) := by
        funext x
        have h := congrFun hdiff x
        simp only [Pi.sub_apply, Pi.add_apply] at h ⊢
        rw [h]; ring
      rw [hrew]
      have hsub := eLpNorm_sub_le_count
        (u := fun x : ℤ => AhalfTranspose₂ N P f h₂ x
          - kmtProj ρ l kk (fun y : ℤ => AhalfTranspose₂ N P f h₂ y) x)
        (v := fun x : ℤ => E₂ x - kmtProj ρ l kk (fun y : ℤ => E₂ y) x)
        (q := ENNReal.ofReal p') (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp'm1.le)
      refine (hsub.trans (add_le_add hA2diff hE2diff)).trans ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : (1 : ℝ) ≤ (angleBracket l : ℝ) := one_le_angleBracket_coe l
      have hcoef := coefY_p' (Cp := (Cp : ℝ)) (Cp' := (Cp' : ℝ)) (C1 := C₁) (CP := CP)
        (l := (angleBracket l : ℝ)) hCppos.le hCp'pos.le hC₁pos (by linarith [hCPge1]) h1
      have hnd' : (1 : ℝ) ≤ Nd ^ (1 / p') := Real.one_le_rpow hNd1 (by positivity)
      have hZ : (0 : ℝ) ≤ Nd ^ (1 / p') := by positivity
      have hstep : CP * Nd ^ (1 / p') + δ ≤ (CP + 1) * Nd ^ (1 / p') := by
        have hd : δ ≤ Nd ^ (1 / p') := le_trans hδ1 hnd'
        calc CP * Nd ^ (1 / p') + δ ≤ CP * Nd ^ (1 / p') + Nd ^ (1 / p') := add_le_add le_rfl hd
          _ = (CP + 1) * Nd ^ (1 / p') := by ring
      calc (1 + (Cp' : ℝ) * (angleBracket l : ℝ)) * (CP * Nd ^ (1 / p'))
            + (1 + (Cp' : ℝ) * (angleBracket l : ℝ)) * δ
          = (1 + (Cp' : ℝ) * (angleBracket l : ℝ)) * (CP * Nd ^ (1 / p') + δ) := by ring
        _ ≤ (1 + (Cp' : ℝ) * (angleBracket l : ℝ)) * ((CP + 1) * Nd ^ (1 / p')) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = ((1 + (Cp' : ℝ) * (angleBracket l : ℝ)) * (CP + 1)) * Nd ^ (1 / p') := by ring
        _ ≤ ((1 + (Cp : ℝ)) * (1 + (Cp' : ℝ)) * (4 * C₁ + 20) * (CP + 1) * (angleBracket l : ℝ))
              * Nd ^ (1 / p') := mul_le_mul_of_nonneg_right hcoef (by positivity)
        _ = Y * (angleBracket l : ℝ) * Nd ^ (1 / p') := by rw [hYdef]
    -- the interpolation step
    have hE1part : eLpNorm (fun x : ℤ => E₁ x - kmtProj ρ l kk (fun y : ℤ => E₁ y) x)
          2 Measure.count
        ≤ ENNReal.ofReal (Y * (angleBracket l : ℝ) * δ ^ (1 / 4 : ℝ) * Nd ^ (1 / 2 : ℝ)) :=
      interp_le (w := fun x : ℤ => E₁ x - kmtProj ρ l kk (fun y : ℤ => E₁ y) x)
        hp1' hp'm1 hpp' (by positivity) hδpos.le hNdpos.le hE1pX hE1p'X
    -- the final arithmetic
    have hreal : Y * (angleBracket l : ℝ) * δ ^ (1 / 4 : ℝ) * Nd ^ (1 / 2 : ℝ)
          + (1 + (C2 : ℝ)) * (angleBracket l : ℝ) * δ
        ≤ Cf * ((2 : ℝ) ^ (-(c * (l : ℝ))) * Nd ^ (1 / 2 : ℝ)) := by
      set ς : ℝ := (2 : ℝ) ^ (-(c * (l : ℝ))) with hςdef
      have hς0 : 0 ≤ ς := by rw [hςdef]; positivity
      have hangleδ : (angleBracket l : ℝ) * δ ^ (1 / 4 : ℝ) ≤ ς := by
        rw [hδquarter, hςdef]
        calc (angleBracket l : ℝ) * (2 : ℝ) ^ (-(2 * c * (l : ℝ)))
            ≤ (2 : ℝ) ^ (c * (l : ℝ)) * (2 : ℝ) ^ (-(2 * c * (l : ℝ))) :=
              mul_le_mul_of_nonneg_right hangleL (by positivity)
          _ = (2 : ℝ) ^ (-(c * (l : ℝ))) := by
              rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
      have hangleδ2 : (angleBracket l : ℝ) * δ ≤ ς := by
        rw [hδdef, hςdef]
        calc (angleBracket l : ℝ) * (2 : ℝ) ^ (-(8 * c * (l : ℝ)))
            ≤ (2 : ℝ) ^ (c * (l : ℝ)) * (2 : ℝ) ^ (-(8 * c * (l : ℝ))) :=
              mul_le_mul_of_nonneg_right hangleL (by positivity)
          _ ≤ (2 : ℝ) ^ (-(c * (l : ℝ))) := by
              rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
              refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
              have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
              nlinarith [hcpos, hl0]
      have hterm1 : Y * (angleBracket l : ℝ) * δ ^ (1 / 4 : ℝ) * Nd ^ (1 / 2 : ℝ)
          ≤ Y * (ς * Nd ^ (1 / 2 : ℝ)) := by
        have h := mul_le_mul_of_nonneg_left hangleδ hYpos.le
        calc Y * (angleBracket l : ℝ) * δ ^ (1 / 4 : ℝ) * Nd ^ (1 / 2 : ℝ)
            = Y * ((angleBracket l : ℝ) * δ ^ (1 / 4 : ℝ)) * Nd ^ (1 / 2 : ℝ) := by ring
          _ ≤ Y * ς * Nd ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_right h (by positivity)
          _ = Y * (ς * Nd ^ (1 / 2 : ℝ)) := by ring
      have hterm2 : (1 + (C2 : ℝ)) * (angleBracket l : ℝ) * δ ≤ (1 + (C2 : ℝ)) * ς := by
        have h := mul_le_mul_of_nonneg_left hangleδ2 (by positivity : (0 : ℝ) ≤ 1 + (C2 : ℝ))
        calc (1 + (C2 : ℝ)) * (angleBracket l : ℝ) * δ
            = (1 + (C2 : ℝ)) * ((angleBracket l : ℝ) * δ) := by ring
          _ ≤ (1 + (C2 : ℝ)) * ς := h
      calc Y * (angleBracket l : ℝ) * δ ^ (1 / 4 : ℝ) * Nd ^ (1 / 2 : ℝ)
            + (1 + (C2 : ℝ)) * (angleBracket l : ℝ) * δ
          ≤ Y * (ς * Nd ^ (1 / 2 : ℝ)) + (1 + (C2 : ℝ)) * ς := add_le_add hterm1 hterm2
        _ ≤ Y * (2 + (C2 : ℝ)) * (ς * Nd ^ (1 / 2 : ℝ)) :=
            add_two_le hYge1 hNd1 hς0 hC2pos.le
        _ ≤ Cf * (ς * Nd ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hCflarge (by positivity)
        _ = Cf * ((2 : ℝ) ^ (-(c * (l : ℝ))) * Nd ^ (1 / 2 : ℝ)) := by rw [hςdef]
    rw [hdiff]
    refine (eLpNorm_add_le_count (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans ?_
    refine (add_le_add hE1part hE2part).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal

end Work.KMTAreas.A4Z
