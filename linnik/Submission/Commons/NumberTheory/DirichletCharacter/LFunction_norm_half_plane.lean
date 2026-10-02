import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Submission.Commons.NumberTheory.DirichletCharacter.interval_sum_bound

open Complex DirichletCharacter Filter MeasureTheory Set intervalIntegral
open scoped Real BigOperators Interval Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Commons.NumberTheory.DirichletCharacter


variable {N : ℕ} [NeZero N]

/-- Partial sums of `χ` over `1..k` are bounded by `2N`. -/
private lemma char_partial_sum_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) (hk : 1 ≤ k) :
    ‖∑ n ∈ Finset.Icc 1 k, (χ (n : ZMod N) : ℂ)‖ ≤ 2 * (N : ℝ) := by
  simpa using Commons.NumberTheory.DirichletCharacter.interval_sum_bound χ hχ hk

/-- Coefficients of a Dirichlet character have norm at most one. -/
private lemma char_coeff_le_one (χ : DirichletCharacter ℂ N) (n : ℕ) :
    ‖(χ (n : ZMod N) : ℂ)‖ ≤ 1 := by
  simpa using χ.norm_le_one (n : ZMod N)

private lemma re_neg_sub_one (s : ℂ) : (-s - 1).re = -s.re - 1 := by
  simp [Complex.neg_re, Complex.sub_re, Complex.one_re]

private lemma norm_cpow_sub_integrand (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-s.re - 1) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx (-s - 1)]
  rw [re_neg_sub_one]

private lemma integral_norm_cpow_sub (k : ℕ) (hk : 1 ≤ k) (s : ℂ) (hs : 0 < s.re) :
    (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), ‖(x : ℂ) ^ (-s - 1)‖)
      = (((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) / s.re := by
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  calc
    (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), ‖(x : ℂ) ^ (-s - 1)‖)
        = ∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), x ^ (-(s.re) - 1) := by
            apply intervalIntegral.integral_congr
            intro x hx
            have hx' : x ∈ Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
              simpa [Set.uIcc_of_le hkle] using hx
            have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast (by omega : 0 < k)) hx'.1
            exact norm_cpow_sub_integrand s hx0
    _ = (((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) / s.re := by
      have hnot0 : 0 ∉ Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
        intro hx
        have hx' : (0 : ℝ) ∈ Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
          simpa [Set.uIcc_of_le hkle] using hx
        linarith only [hx'.1, show (0 : ℝ) < (k : ℝ) by exact_mod_cast (by omega : 0 < k), hx', hk]
      have hne : -s.re - 1 ≠ (-1 : ℝ) := by linarith only [hs]
      have hint := integral_rpow (r := -s.re - 1) (a := (k : ℝ)) (b := ((k + 1 : ℕ) : ℝ))
        (Or.inr ⟨hne, hnot0⟩)
      rw [hint]
      have hD : -s.re - 1 + 1 = -s.re := by ring
      rw [hD]
      have hσ : s.re ≠ 0 := ne_of_gt hs
      field_simp [hσ]
      ring

/-- `(n)^(-s) - (n+1)^(-s) = s * ∫_n^{n+1} x^(-s-1) dx` (complex-valued integrand). -/
private lemma cpow_sub_eq_smul_integral (k : ℕ) (hk : 1 ≤ k) (s : ℂ) (hs : 0 < s.re) :
    ((k : ℂ) ^ (-s) - (((k + 1 : ℕ) : ℂ) ^ (-s)))
      = s * (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x : ℂ) ^ (-s - 1)) := by
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hnot0 : 0 ∉ Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    intro hx
    have hx' : (0 : ℝ) ∈ Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
      simpa [Set.uIcc_of_le hkle] using hx
    linarith only [hx'.1, show (0 : ℝ) < (k : ℝ) by exact_mod_cast (by omega : 0 < k), hx', hk]
  have hne : -s - 1 ≠ (-1 : ℂ) := by
    intro h
    apply ne_of_gt hs
    have hre := congrArg Complex.re h
    simpa using hre
  have hint := integral_cpow (r := -s - 1) (a := (k : ℝ)) (b := ((k + 1 : ℕ) : ℝ))
    (Or.inr ⟨hne, hnot0⟩)
  have hD : -s - 1 + 1 = -s := by ring
  have hinteq : (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x : ℂ) ^ (-s - 1))
      = ((((k + 1 : ℕ) : ℂ) ^ (-s)) - ((k : ℂ) ^ (-s))) / (-s) := by
    rw [hint]
    rw [hD]
    simp
  have hsnz : s ≠ 0 := by
    intro h
    exact (ne_of_gt hs) (by simpa [h] : s.re = 0)
  have hmain : s * (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x : ℂ) ^ (-s - 1))
      = (k : ℂ) ^ (-s) - (((k + 1 : ℕ) : ℂ) ^ (-s)) := by
    calc
      s * (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x : ℂ) ^ (-s - 1))
          = s * (((((k + 1 : ℕ) : ℂ) ^ (-s)) - ((k : ℂ) ^ (-s))) / (-s)) := by
              rw [hinteq]
      _ = (k : ℂ) ^ (-s) - (((k + 1 : ℕ) : ℂ) ^ (-s)) := by
              have : -s ≠ 0 := by
                intro h
                apply hsnz
                exact neg_eq_zero.mp h
              field_simp [this]
              ring
  exact hmain.symm

/-- Difference of successive `n^{-s}` is bounded by the telescoping rpow difference. -/
private lemma norm_cpow_sub_le (k : ℕ) (hk : 1 ≤ k) (s : ℂ) (hs : 0 < s.re) :
    ‖((k : ℂ) ^ (-s)) - (((k + 1 : ℕ) : ℂ) ^ (-s))‖
      ≤ (‖s‖ / s.re) * (((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) := by
  have hsub := cpow_sub_eq_smul_integral k hk s hs
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  calc
    ‖((k : ℂ) ^ (-s)) - (((k + 1 : ℕ) : ℂ) ^ (-s))‖
        = ‖s * (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x : ℂ) ^ (-s - 1))‖ := by
            rw [hsub]
    _ ≤ ‖s‖ * ‖(∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x : ℂ) ^ (-s - 1))‖ := norm_mul_le _ _
    _ ≤ ‖s‖ * (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), ‖(x : ℂ) ^ (-s - 1)‖) := by
            exact mul_le_mul_of_nonneg_left
              (intervalIntegral.norm_integral_le_integral_norm hkle) (norm_nonneg s)
    _ = ‖s‖ * ((((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) / s.re) := by
            rw [integral_norm_cpow_sub k hk s hs]
    _ = (‖s‖ / s.re) * (((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) := by
            field_simp [ne_of_gt hs]


private lemma antitoneOn_rpow_neg {a : ℝ} (ha : a ≤ 0) :
    AntitoneOn (fun x : ℝ => x ^ a) (Set.Ioi (0 : ℝ)) := by
  exact Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (r := a) ha

private lemma sum_Icc1_eq_sum_range_succ (X : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 X, f n) = ∑ m ∈ Finset.range X, f (m + 1) := by
  induction X with
  | zero => simp
  | succ X ih =>
      by_cases h0 : X = 0
      · subst X
        simp
      · have hX : 1 ≤ X := by omega
        rw [Finset.sum_range_succ]
        rw [Finset.sum_Icc_succ_top (a := 1) (b := X) (by omega)]
        rw [ih]

private lemma range_eq_insert_Ico (X : ℕ) (hX : 1 ≤ X) :
    Finset.range X = insert 0 (Finset.Ico 1 X) := by
  ext m
  simp only [Finset.mem_range, Finset.mem_Ico, Finset.mem_insert]
  constructor <;> omega

private lemma sum_rpow_neg_le (X : ℕ) (hX : 1 ≤ X) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    (∑ n ∈ Finset.Icc 1 X, (n : ℝ) ^ (-σ)) ≤ (1 + (1 - σ)⁻¹) * (X : ℝ) ^ (1 - σ) := by
  let f : ℝ → ℝ := fun x => x ^ (-σ)
  have hanti0 : AntitoneOn f (Set.Ioi (0 : ℝ)) := antitoneOn_rpow_neg (by linarith only [hσ0] : -σ ≤ 0)
  have hanti : AntitoneOn f (Set.Icc ((1 : ℕ) : ℝ) (X : ℝ)) := hanti0.mono (by
    intro x hx
    have h1 : (1 : ℝ) ≤ x := by exact_mod_cast (Set.mem_Icc.mp hx).1
    exact Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one h1))
  have hXle : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have h_int : (∫ x : ℝ in (((1 : ℕ) : ℝ))..(X : ℝ), x ^ (-σ)) = ((X : ℝ) ^ (1 - σ) - 1) / (1 - σ) := by
    have hne : -σ ≠ (-1 : ℝ) := by linarith only [hσ1]
    have hnot0 : 0 ∉ Set.uIcc (((1 : ℕ) : ℝ)) (X : ℝ) := by
      intro hx
      have hx' : (0 : ℝ) ∈ Set.Icc (1 : ℝ) (X : ℝ) := by
        simpa [Set.uIcc_of_le hXle] using hx
      have h01 : (1 : ℝ) ≤ (0 : ℝ) := (Set.mem_Icc.mp hx').1
      linarith only [hσ0, hσ1, h01]
    have hint := integral_rpow (r := -σ) (a := (((1 : ℕ) : ℝ))) (b := (X : ℝ)) (Or.inr ⟨hne, hnot0⟩)
    rw [hint]
    have hD : -σ + 1 = 1 - σ := by ring
    rw [hD]
    simp
  have h_int_le : (∫ x : ℝ in (((1 : ℕ) : ℝ))..(X : ℝ), f x) ≤ (1 - σ)⁻¹ * (X : ℝ) ^ (1 - σ) := by
    rw [h_int]
    have hpos : 0 < 1 - σ := sub_pos.mpr hσ1
    calc
      ((X : ℝ) ^ (1 - σ) - 1) / (1 - σ) ≤ (X : ℝ) ^ (1 - σ) / (1 - σ) := by
        exact div_le_div_of_nonneg_right (by linarith only [hσ0, hσ1]) (le_of_lt hpos)
      _ = (1 - σ)⁻¹ * (X : ℝ) ^ (1 - σ) := by
            field_simp [ne_of_gt hpos]
  have hint_b : (∑ i ∈ Finset.Ico 1 X, f ((i + 1 : ℕ) : ℝ)) ≤ ∫ x : ℝ in (((1 : ℕ) : ℝ))..(X : ℝ), f x := by
    exact AntitoneOn.sum_le_integral_Ico (f := f) (a := 1) (b := X) hX hanti
  have hge1 : (1 : ℝ) ≤ (X : ℝ) ^ (1 - σ) := by
    exact Real.one_le_rpow hXle (by linarith only [hσ1] : 0 ≤ 1 - σ)
  calc
    (∑ n ∈ Finset.Icc 1 X, (n : ℝ) ^ (-σ))
        = ∑ m ∈ Finset.range X, f ((m + 1 : ℕ) : ℝ) := by
            rw [sum_Icc1_eq_sum_range_succ]
    _ = f 1 + ∑ i ∈ Finset.Ico 1 X, f ((i + 1 : ℕ) : ℝ) := by
            rw [range_eq_insert_Ico X hX, Finset.sum_insert]
            · simp
            · rw [Finset.mem_Ico]; omega
    _ ≤ f 1 + ∫ x : ℝ in (((1 : ℕ) : ℝ))..(X : ℝ), f x := by
            exact add_le_add le_rfl hint_b
    _ ≤ f 1 + (1 - σ)⁻¹ * (X : ℝ) ^ (1 - σ) := by
            exact add_le_add le_rfl h_int_le
    _ ≤ (1 + (1 - σ)⁻¹) * (X : ℝ) ^ (1 - σ) := by
            have hf1 : f 1 = 1 := by
              dsimp [f]
              simp
            rw [hf1]
            linarith only [hge1]

/-- Partial sums `∑_{1 ≤ m ≤ k} χ(m)`. -/
private noncomputable def partSum (χ : DirichletCharacter ℂ N) : ℕ → ℂ :=
  fun k => ∑ m ∈ Finset.Icc 1 k, (χ (m : ZMod N) : ℂ)

private lemma partSum_zero (χ : DirichletCharacter ℂ N) : partSum χ 0 = 0 := by
  dsimp [partSum]
  simp

/-- Boundedness of the partial sums of a non-trivial character. -/
private lemma partSum_bound (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) (hk : 1 ≤ k) :
    ‖partSum χ k‖ ≤ 2 * (N : ℝ) := by
  dsimp [partSum]
  exact char_partial_sum_le χ hχ k hk

/-- The `k`-th summand of the Abel continuation series. -/
private noncomputable def abelTerm (χ : DirichletCharacter ℂ N) (s : ℂ) (k : ℕ) : ℂ :=
  partSum χ k * ((k : ℂ) ^ (-s) - (((k + 1 : ℕ) : ℂ) ^ (-s)))

/-- The `k`-th summand vanishes at `k = 0`. -/
private lemma abelTerm_zero (χ : DirichletCharacter ℂ N) (s : ℂ) : abelTerm χ s 0 = 0 := by
  dsimp [abelTerm]
  rw [partSum_zero]
  ring

private lemma abelTerm_bound (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖abelTerm χ s k‖ ≤ (2 * (N : ℝ)) * (‖s‖ / s.re) *
      (((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) := by
  have hS := partSum_bound χ hχ k hk
  have hD := norm_cpow_sub_le k hk s hs
  calc
    ‖abelTerm χ s k‖ = ‖partSum χ k‖ * ‖((k : ℂ) ^ (-s)) - (((k + 1 : ℕ) : ℂ) ^ (-s))‖ := by
      dsimp [abelTerm]
      rw [norm_mul]
    _ ≤ (2 * (N : ℝ)) * (((‖s‖ / s.re) * (((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))))) := by
      exact mul_le_mul hS hD (norm_nonneg _) (by positivity)
    _ = (2 * (N : ℝ)) * (‖s‖ / s.re) *
      (((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) := by ring


 

/-- Telescoping `HasSum` for the difference sequence `(X+m)^{-β} - (X+m+1)^{-β}`. -/
private lemma hasSum_telescope_rpow (X : ℕ) (hX : 1 ≤ X) {β : ℝ} (hβ : 0 < β) :
    HasSum (fun m : ℕ => (((X + m : ℕ) : ℝ) ^ (-β)) - (((X + m + 1 : ℕ) : ℝ) ^ (-β)))
      ((X : ℝ) ^ (-β)) := by
  have h_nonneg : ∀ m : ℕ, 0 ≤ (((X + m : ℕ) : ℝ) ^ (-β)) - (((X + m + 1 : ℕ) : ℝ) ^ (-β)) := by
    intro m
    have hbase1 : (0 : ℝ) < ((X + m : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have hle : ((X + m : ℕ) : ℝ) ≤ ((X + m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have hpow : (((X + m + 1 : ℕ) : ℝ) ^ (-β)) ≤ (((X + m : ℕ) : ℝ) ^ (-β)) := by
      exact Real.rpow_le_rpow_of_nonpos hbase1 hle (by linarith only [hβ] : -β ≤ 0)
    exact sub_nonneg.mpr hpow
  have hto : Tendsto (fun N : ℕ => ((X + N : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_atTop_mono (f := fun N : ℕ => (N : ℝ)) (g := fun N : ℕ => ((X + N : ℕ) : ℝ))
      (fun N => by exact_mod_cast (by omega : N ≤ X + N)) tendsto_natCast_atTop_atTop
  have hdec : Tendsto (fun t : ℝ => t ^ (-β)) atTop (𝓝 0) := by
    have hmain : Tendsto (fun t : ℝ => (t ^ β)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop hβ)
    refine hmain.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [Real.rpow_neg (by linarith only [ht] : 0 ≤ t) β]
  have hN0 : Tendsto (fun N : ℕ => ((X + N : ℕ) : ℝ) ^ (-β)) atTop (𝓝 0) := hdec.comp hto
  have hmain_t : Tendsto (fun N : ℕ => (X : ℝ) ^ (-β) - ((X + N : ℕ) : ℝ) ^ (-β)) atTop (𝓝 ((X : ℝ) ^ (-β))) := by
    simpa using (tendsto_const_nhds.sub hN0 : Tendsto (fun N : ℕ => (X : ℝ) ^ (-β) - ((X + N : ℕ) : ℝ) ^ (-β)) atTop (𝓝 ((X : ℝ) ^ (-β) - 0)))
  have hsumN : ∀ N : ℕ, (∑ m ∈ Finset.range N, ((((X + m : ℕ) : ℝ) ^ (-β)) - (((X + m + 1 : ℕ) : ℝ) ^ (-β)))) = (X : ℝ) ^ (-β) - (((X + N : ℕ) : ℝ) ^ (-β)) := by
    intro N
    simpa [Nat.add_assoc] using (Finset.sum_range_sub' (fun j : ℕ => ((X + j : ℕ) : ℝ) ^ (-β)) N)
  have hpartial : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, ((((X + m : ℕ) : ℝ) ^ (-β)) - (((X + m + 1 : ℕ) : ℝ) ^ (-β)))) atTop (𝓝 ((X : ℝ) ^ (-β))) := by
    exact hmain_t.congr (fun N => (hsumN N).symm)
  exact (hasSum_iff_tendsto_nat_of_nonneg h_nonneg ((X : ℝ) ^ (-β))).2 hpartial

/-- The real telescoping difference sequence has sum `(X)⁻ᵝ`. -/
private lemma tsum_telescope_rpow (X : ℕ) (hX : 1 ≤ X) {β : ℝ} (hβ : 0 < β) :
    (∑' m : ℕ, ((((X + m : ℕ) : ℝ) ^ (-β)) - (((X + m + 1 : ℕ) : ℝ) ^ (-β))))
      = (X : ℝ) ^ (-β) := by
  exact (hasSum_telescope_rpow X hX hβ).tsum_eq

/-- The Abel continuation series is (absolutely) summable for `0 < re s`. -/
private lemma abelTerm_summable (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ)
    (hs : 0 < s.re) : Summable (fun n : ℕ => abelTerm χ s n) := by
  let C : ℝ := (2 * (N : ℝ)) * (‖s‖ / s.re)
  have htelesc : Summable (fun m : ℕ => ((((1 + m : ℕ) : ℝ) ^ (-s.re)) - (((1 + m + 1 : ℕ) : ℝ) ^ (-s.re)))) := by
    exact (hasSum_telescope_rpow 1 (by norm_num) hs).summable
  have ht : Summable (fun m : ℕ => ((((m + 1 : ℕ) : ℝ) ^ (-s.re)) - (((m + 2 : ℕ) : ℝ) ^ (-s.re)))) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htelesc
  have hshift : Summable (fun n : ℕ => abelTerm χ s (n + 1)) := by
    refine Summable.of_norm_bounded (f := fun n : ℕ => abelTerm χ s (n + 1))
      (g := fun n : ℕ => C * ((((n + 1 : ℕ) : ℝ) ^ (-s.re)) - (((n + 2 : ℕ) : ℝ) ^ (-s.re)))) ?_ ?_
    · simpa [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using ht.mul_left C
    · intro n
      have hb := abelTerm_bound χ hχ s hs (n + 1) (by omega)
      dsimp [C] at hb ⊢
      exact hb
  exact (summable_nat_add_iff 1).1 hshift


/-- The Abel continuation of the Dirichlet L-series: `∑ S(n)·(n^{-s} − (n+1)^{-s})`. -/
private noncomputable def abelCont (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑' n : ℕ, abelTerm χ s n

 

/-- Summation-by-parts: the head of the Abel series is a truncated Dirichlet sum minus a boundary term. -/
private lemma abelTerm_head_eq (χ : DirichletCharacter ℂ N) (s : ℂ) (X : ℕ) (hX : 1 ≤ X) :
    (∑ n ∈ Finset.range X, abelTerm χ s n) + partSum χ X * (X : ℂ) ^ (-s)
      = ∑ n ∈ Finset.Icc 1 X, (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-s) := by
  induction X with
  | zero => omega
  | succ X ih =>
      by_cases h0 : X = 0
      · subst X
        simp [abelTerm_zero, partSum]
      · have hX1 : 1 ≤ X := by omega
        have hrec := ih hX1
        have hP : (∑ n ∈ Finset.Icc 1 (X + 1), (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-s))
            = (∑ n ∈ Finset.Icc 1 X, (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-s))
              + (χ ((X + 1 : ℕ) : ZMod N) : ℂ) * (((X + 1 : ℕ) : ℂ) ^ (-s)) := by
            rw [Finset.sum_Icc_succ_top (a := 1) (b := X) (by omega : 1 ≤ X + 1)]
        have hS : partSum χ (X + 1) = partSum χ X + (χ ((X + 1 : ℕ) : ZMod N) : ℂ) := by
            dsimp [partSum]
            rw [Finset.sum_Icc_succ_top (a := 1) (b := X) (by omega : 1 ≤ X + 1)]
        have hR : (∑ n ∈ Finset.range (X + 1), abelTerm χ s n)
            = (∑ n ∈ Finset.range X, abelTerm χ s n) + abelTerm χ s X := by
            rw [Finset.sum_range_succ]
        calc
          (∑ n ∈ Finset.range (X + 1), abelTerm χ s n) + partSum χ (X + 1) * (((X + 1 : ℕ) : ℂ) ^ (-s))
              = ((∑ n ∈ Finset.range X, abelTerm χ s n) + abelTerm χ s X)
                  + (partSum χ X + (χ ((X + 1 : ℕ) : ZMod N) : ℂ)) * (((X + 1 : ℕ) : ℂ) ^ (-s)) := by
                  rw [hR, hS]
          _ = (∑ n ∈ Finset.range X, abelTerm χ s n) + partSum χ X * (X : ℂ) ^ (-s)
              + (χ ((X + 1 : ℕ) : ZMod N) : ℂ) * (((X + 1 : ℕ) : ℂ) ^ (-s)) := by
                  dsimp [abelTerm]
                  ring
          _ = (∑ n ∈ Finset.Icc 1 X, (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-s))
              + (χ ((X + 1 : ℕ) : ZMod N) : ℂ) * (((X + 1 : ℕ) : ℂ) ^ (-s)) := by
                  rw [hrec]
          _ = ∑ n ∈ Finset.Icc 1 (X + 1), (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-s) := hP.symm

/-- Norm bound for the head of the Abel series (before choosing the balance point). -/
private lemma abelTerm_head_norm_bound (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ)
    (hs : 0 < s.re) (hs1 : s.re < 1) (X : ℕ) (hX : 1 ≤ X) :
    ‖∑ n ∈ Finset.range X, abelTerm χ s n‖
      ≤ ((1 + (1 - s.re)⁻¹) * (X : ℝ) ^ (1 - s.re)) + 2 * (N : ℝ) * (X : ℝ) ^ (-s.re) := by
  have hP : ‖∑ n ∈ Finset.Icc 1 X, (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-s)‖
      ≤ (1 + (1 - s.re)⁻¹) * (X : ℝ) ^ (1 - s.re) := by
    calc
      ‖∑ n ∈ Finset.Icc 1 X, (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-s)‖
          ≤ ∑ n ∈ Finset.Icc 1 X, ‖(χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-s)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 X, (n : ℝ) ^ (-s.re) := by
            apply Finset.sum_le_sum
            intro n hn
            have hn0 : (0 : ℝ) < (n : ℝ) := by
              have h1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
              exact_mod_cast (by omega : 0 < n)
            calc
              ‖(χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-s)‖
                  = ‖(χ (n : ZMod N) : ℂ)‖ * ‖(n : ℂ) ^ (-s)‖ := by rw [norm_mul]
              _ ≤ 1 * ‖(n : ℂ) ^ (-s)‖ := mul_le_mul_of_nonneg_right (char_coeff_le_one χ n) (norm_nonneg _)
              _ = ‖(n : ℂ) ^ (-s)‖ := by rw [one_mul]
              _ = (n : ℝ) ^ (-s.re) := by
                    have hb : ((n : ℕ) : ℂ) = ((((n : ℕ) : ℝ) : ℂ)) := by norm_num
                    rw [hb]
                    have h := Complex.norm_cpow_eq_rpow_re_of_pos hn0 (-s)
                    rw [h]
                    rw [Complex.neg_re]
      _ ≤ (1 + (1 - s.re)⁻¹) * (X : ℝ) ^ (1 - s.re) := by
            exact sum_rpow_neg_le X hX hs hs1
  have hc : ‖partSum χ X * (X : ℂ) ^ (-s)‖ ≤ 2 * (N : ℝ) * (X : ℝ) ^ (-s.re) := by
    have hS := partSum_bound χ hχ X hX
    have hx0 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
    have hXp : ‖(X : ℂ) ^ (-s)‖ = (X : ℝ) ^ (-s.re) := by
      have hb : ((X : ℕ) : ℂ) = ((((X : ℕ) : ℝ) : ℂ)) := by norm_num
      rw [hb]
      have h := Complex.norm_cpow_eq_rpow_re_of_pos hx0 (-s)
      rw [h]
      rw [Complex.neg_re]
    calc
      ‖partSum χ X * (X : ℂ) ^ (-s)‖ ≤ ‖partSum χ X‖ * ‖(X : ℂ) ^ (-s)‖ := norm_mul_le _ _
      _ ≤ (2 * (N : ℝ)) * ‖(X : ℂ) ^ (-s)‖ := mul_le_mul_of_nonneg_right hS (norm_nonneg _)
      _ = (2 * (N : ℝ)) * (X : ℝ) ^ (-s.re) := by rw [hXp]
      _ = 2 * (N : ℝ) * (X : ℝ) ^ (-s.re) := by ring
  have hSumc : ‖(∑ n ∈ Finset.range X, abelTerm χ s n) + partSum χ X * (X : ℂ) ^ (-s)‖
      ≤ (1 + (1 - s.re)⁻¹) * (X : ℝ) ^ (1 - s.re) := by
    have hmain := abelTerm_head_eq χ s X hX
    rw [hmain]
    exact hP
  calc
    ‖∑ n ∈ Finset.range X, abelTerm χ s n‖
        = ‖((∑ n ∈ Finset.range X, abelTerm χ s n) + partSum χ X * (X : ℂ) ^ (-s))
            - partSum χ X * (X : ℂ) ^ (-s)‖ := by ring_nf
    _ ≤ ‖(∑ n ∈ Finset.range X, abelTerm χ s n) + partSum χ X * (X : ℂ) ^ (-s)‖
          + ‖partSum χ X * (X : ℂ) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ ((1 + (1 - s.re)⁻¹) * (X : ℝ) ^ (1 - s.re)) + 2 * (N : ℝ) * (X : ℝ) ^ (-s.re) := by
          exact add_le_add hSumc hc




/-- Tail of the Abel series is bounded by `C·X^{-σ}`. -/
private lemma abelTerm_tail_bound (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ)
    (hs : 0 < s.re) (X : ℕ) (hX : 1 ≤ X) :
    ‖∑' m : ℕ, abelTerm χ s (X + m)‖
      ≤ (2 * (N : ℝ)) * (‖s‖ / s.re) * (X : ℝ) ^ (-s.re) := by
  let C : ℝ := (2 * (N : ℝ)) * (‖s‖ / s.re)
  have ht : Summable (fun m : ℕ => C * ((((X + m : ℕ) : ℝ) ^ (-s.re)) - (((X + m + 1 : ℕ) : ℝ) ^ (-s.re)))) := by
    exact (hasSum_telescope_rpow X hX hs).summable.mul_left C
  have hnorm : Summable (fun m : ℕ => ‖abelTerm χ s (X + m)‖) := by
    refine Summable.of_nonneg_of_le ?_ ?_ ht
    · intro m
      exact norm_nonneg _
    · intro m
      have hb := abelTerm_bound χ hχ s hs (X + m) (by omega)
      dsimp [C]
      exact hb
  have htsum : (∑' m : ℕ, C * ((((X + m : ℕ) : ℝ) ^ (-s.re)) - (((X + m + 1 : ℕ) : ℝ) ^ (-s.re))))
      = C * (X : ℝ) ^ (-s.re) := by
    have hmain : HasSum (fun m : ℕ =>
        C * ((((X + m : ℕ) : ℝ) ^ (-s.re)) - (((X + m + 1 : ℕ) : ℝ) ^ (-s.re)))) (C * (X : ℝ) ^ (-s.re)) := by
      exact (hasSum_telescope_rpow X hX hs).mul_left C
    exact hmain.tsum_eq
  have hle' : (∑' m : ℕ, ‖abelTerm χ s (X + m)‖)
      ≤ ∑' m : ℕ, C * ((((X + m : ℕ) : ℝ) ^ (-s.re)) - (((X + m + 1 : ℕ) : ℝ) ^ (-s.re))) := by
    refine hnorm.tsum_le_tsum ?_ ht
    intro m
    have hb := abelTerm_bound χ hχ s hs (X + m) (by omega)
    dsimp [C]
    exact hb
  calc
    ‖∑' m : ℕ, abelTerm χ s (X + m)‖ ≤ ∑' m : ℕ, ‖abelTerm χ s (X + m)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' m : ℕ, C * ((((X + m : ℕ) : ℝ) ^ (-s.re)) - (((X + m + 1 : ℕ) : ℝ) ^ (-s.re))) := hle'
    _ = C * (X : ℝ) ^ (-s.re) := htsum
    _ = (2 * (N : ℝ)) * (‖s‖ / s.re) * (X : ℝ) ^ (-s.re) := by rfl

/-- Decompose the Abel series into head and tail. -/
private lemma abelCont_eq_head_add_tail (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ)
    (hs : 0 < s.re) (X : ℕ) :
    abelCont χ s = (∑ n ∈ Finset.range X, abelTerm χ s n) + ∑' m : ℕ, abelTerm χ s (X + m) := by
  have hsum := abelTerm_summable χ hχ s hs
  dsimp [abelCont]
  simpa [Nat.add_comm] using (hsum.sum_add_tsum_nat_add X).symm

/-- Pointwise polynomial bound for the Abel continuation. -/
private lemma abelCont_bound (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ)
    (hs : 0 < s.re) (hs1 : s.re < 1) :
    ‖abelCont χ s‖ ≤
      ((2 + (1 - s.re)⁻¹) * (8 / s.re)) * (1 + ‖s‖) ^ (1 - s.re) * (N : ℝ) ^ (1 - s.re) := by
  set σ : ℝ := s.re
  let A : ℝ := 2 * (N : ℝ) * (1 + ‖s‖ / σ)
  let X : ℕ := Nat.ceil A
  have hσ0 : 0 < σ := hs
  have hσ1 : σ < 1 := hs1
  have hσne : σ ≠ 0 := ne_of_gt hσ0
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt (NeZero.pos N))
  have hNs0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hsp : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
  have h1 : (1 : ℝ) ≤ 1 + ‖s‖ / σ := by
    have hdiv : 0 ≤ ‖s‖ / σ := div_nonneg hsp (le_of_lt hσ0)
    linarith only [hdiv]
  have h2 : (2 : ℝ) ≤ A := by
    dsimp [A]
    have hN2 : 2 ≤ 2 * (N : ℝ) := by linarith only [hN1]
    calc
      (2 : ℝ) ≤ 2 * (N : ℝ) * 1 := by linarith only [hN1]
      _ ≤ 2 * (N : ℝ) * (1 + ‖s‖ / σ) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hA1 : 1 ≤ A := by linarith only [hs, hs1, h2]
  have hAX : A ≤ (X : ℝ) := by
    dsimp [X]
    exact Nat.le_ceil A
  have hX1 : 1 ≤ X := by
    dsimp [X]
    have : (1 : ℝ) ≤ (X : ℝ) := by linarith only [hs, hs1, h2, hAX]
    exact_mod_cast this
  have hXle : (X : ℝ) ≤ 2 * A := by
    dsimp [X]
    have hceil : (Nat.ceil A : ℝ) < A + 1 := Nat.ceil_lt_add_one (by linarith only [hs, hs1, h2] : 0 ≤ A)
    linarith only [hs, hs1, h2, hceil]
  have hrel : 1 + ‖s‖ / σ ≤ (1 + ‖s‖) * (2 / σ) := by
    have h12 : 1 + 1 / σ ≤ 2 / σ := by
      have hmain : (1 + 1 / σ) * σ ≤ (2 / σ) * σ := by
        field_simp [hσne]
        have hσm : σ ≤ 1 := le_of_lt hσ1
        linarith only [hs1]
      have hσp : 0 < σ := hσ0
      exact (le_of_mul_le_mul_right hmain hσp)
    have hstep1 : 1 + ‖s‖ / σ ≤ (1 + ‖s‖) * (1 + 1 / σ) := by
      have hmain : (1 + ‖s‖ / σ) * σ ≤ (1 + ‖s‖) * (1 + 1 / σ) * σ := by
        field_simp [hσne]
        nlinarith only [hsp, hs1, hs]
      exact (le_of_mul_le_mul_right hmain hσ0)
    calc
      1 + ‖s‖ / σ ≤ (1 + ‖s‖) * (1 + 1 / σ) := hstep1
      _ ≤ (1 + ‖s‖) * (2 / σ) := mul_le_mul_of_nonneg_left h12 (by linarith only [hsp, hs, hs1])
  have hA2 : 2 * A ≤ 8 * (N : ℝ) * (1 + ‖s‖) / σ := by
    dsimp [A]
    have hmain' : 2 * (2 * (N : ℝ) * (1 + ‖s‖ / σ)) * σ ≤ (8 * (N : ℝ) * (1 + ‖s‖) / σ) * σ := by
      field_simp [hσne]
      linarith only [hσ1, hsp, hs, hs1]
    exact (le_of_mul_le_mul_right hmain' hσ0)
  have hX2 : (X : ℝ) ≤ 8 * (N : ℝ) * (1 + ‖s‖) / σ := le_trans hXle hA2
  have hpow_apply : ((8 * (N : ℝ) * (1 + ‖s‖)) / σ) ^ (1 - σ)
      ≤ (8 / σ) * (N : ℝ) ^ (1 - σ) * (1 + ‖s‖) ^ (1 - σ) := by
    have h8 : (0 : ℝ) ≤ 8 / σ := by positivity
    have hN : (0 : ℝ) ≤ (N : ℝ) := hNs0
    have hsu : 0 ≤ 1 + ‖s‖ := by positivity
    have hprod : (8 * (N : ℝ) * (1 + ‖s‖)) / σ = (8 / σ) * (N : ℝ) * (1 + ‖s‖) := by
      field_simp [hσne]
    rw [hprod]
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ (8 / σ) * (N : ℝ)) hsu]
    rw [Real.mul_rpow h8 hN]
    calc
      (8 / σ) ^ (1 - σ) * (N : ℝ) ^ (1 - σ) * (1 + ‖s‖) ^ (1 - σ)
          ≤ (8 / σ) * (N : ℝ) ^ (1 - σ) * (1 + ‖s‖) ^ (1 - σ) := by
            have hge : (1 : ℝ) ≤ 8 / σ := by
              have h1σ : 1 ≤ 1 / σ := by
                have hm : (1 : ℝ) * σ ≤ (1 / σ) * σ := by
                  field_simp [hσne]
                  linarith only [hs1]
                exact (le_of_mul_le_mul_right hm hσ0)
              have h8d : 8 / σ = 8 * (1 / σ) := by field_simp [hσne]
              rw [h8d]
              have hposinv : 0 ≤ 1 / σ := by positivity
              linarith only [hs, hs1, h1σ]
            gcongr
            exact Real.rpow_le_self_of_one_le hge (by linarith only [hs] : 1 - σ ≤ 1)
      _ = (8 / σ) * (N : ℝ) ^ (1 - σ) * (1 + ‖s‖) ^ (1 - σ) := rfl
  have hXpow : (X : ℝ) ^ (1 - σ) ≤ (8 / σ) * (N : ℝ) ^ (1 - σ) * (1 + ‖s‖) ^ (1 - σ) := by
    have hmain : (X : ℝ) ^ (1 - σ) ≤ ((8 * (N : ℝ) * (1 + ‖s‖)) / σ) ^ (1 - σ) := by
      have hX0 : 0 ≤ (X : ℝ) := by positivity
      have hBase : (X : ℝ) ≤ (8 * (N : ℝ) * (1 + ‖s‖)) / σ := by
        simpa [div_eq_mul_inv, mul_assoc] using hX2
      exact Real.rpow_le_rpow hX0 hBase (by linarith only [hs1] : 0 ≤ 1 - σ)
    exact hmain.trans hpow_apply
  have hhead := abelTerm_head_norm_bound χ hχ s hs hs1 X hX1
  have htail := abelTerm_tail_bound χ hχ s hs X hX1
  have hsplit := abelCont_eq_head_add_tail χ hχ s hs X
  have hcomb : ‖abelCont χ s‖ ≤ (2 + (1 - σ)⁻¹) * (X : ℝ) ^ (1 - σ) := by
    calc
      ‖abelCont χ s‖
          = ‖(∑ n ∈ Finset.range X, abelTerm χ s n) + ∑' m : ℕ, abelTerm χ s (X + m)‖ := by rw [hsplit]
      _ ≤ ‖∑ n ∈ Finset.range X, abelTerm χ s n‖ + ‖∑' m : ℕ, abelTerm χ s (X + m)‖ := norm_add_le _ _
      _ ≤ (((1 + (1 - σ)⁻¹) * (X : ℝ) ^ (1 - σ)) + 2 * (N : ℝ) * (X : ℝ) ^ (-σ))
            + (2 * (N : ℝ)) * (‖s‖ / σ) * (X : ℝ) ^ (-σ) := by
            exact add_le_add hhead htail
      _ ≤ (2 + (1 - σ)⁻¹) * (X : ℝ) ^ (1 - σ) := by
            have hcoef : 2 * (N : ℝ) + (2 * (N : ℝ)) * (‖s‖ / σ) ≤ (X : ℝ) := by
              have : 2 * (N : ℝ) + (2 * (N : ℝ)) * (‖s‖ / σ) ≤ A := by
                dsimp [A]
                have hN : 0 ≤ 2 * (N : ℝ) := by positivity
                have hA : 1 + ‖s‖ / σ ≤ 1 + ‖s‖ / σ := le_rfl
                linarith only []
              linarith only [hAX]
            have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
            have hcanc : (((1 + (1 - σ)⁻¹) * (X : ℝ) ^ (1 - σ)) + 2 * (N : ℝ) * (X : ℝ) ^ (-σ))
                  + (2 * (N : ℝ)) * (‖s‖ / σ) * (X : ℝ) ^ (-σ)
                = ((1 + (1 - σ)⁻¹) * (X : ℝ) ^ (1 - σ))
                  + (2 * (N : ℝ) + (2 * (N : ℝ)) * (‖s‖ / σ)) * (X : ℝ) ^ (-σ) := by ring
            rw [hcanc]
            have htailb : (2 * (N : ℝ) + (2 * (N : ℝ)) * (‖s‖ / σ)) * (X : ℝ) ^ (-σ)
                ≤ (1 : ℝ) * (X : ℝ) ^ (1 - σ) := by
              calc
                (2 * (N : ℝ) + (2 * (N : ℝ)) * (‖s‖ / σ)) * (X : ℝ) ^ (-σ)
                    ≤ (X : ℝ) * (X : ℝ) ^ (-σ) := mul_le_mul_of_nonneg_right hcoef (by positivity)
                _ = (X : ℝ) ^ (1 - σ) := by
                      have h : (X : ℝ) ^ (1 - σ) = (X : ℝ) * (X : ℝ) ^ (-σ) := by
                        have hsum : (1 : ℝ) + (-σ) = 1 - σ := by ring
                        rw [← hsum]
                        rw [Real.rpow_add hXpos 1 (-σ)]
                        rw [Real.rpow_one]
                      rw [h]
                _ ≤ (1 : ℝ) * (X : ℝ) ^ (1 - σ) := by rw [one_mul]
            linarith only [htailb]
  calc
    ‖abelCont χ s‖ ≤ (2 + (1 - σ)⁻¹) * (X : ℝ) ^ (1 - σ) := hcomb
    _ ≤ (2 + (1 - σ)⁻¹) * ((8 / σ) * (N : ℝ) ^ (1 - σ) * (1 + ‖s‖) ^ (1 - σ)) := by
          exact mul_le_mul_of_nonneg_left hXpow (by positivity)
    _ = ((2 + (1 - σ)⁻¹) * (8 / σ)) * (1 + ‖s‖) ^ (1 - σ) * (N : ℝ) ^ (1 - σ) := by ring



/-- The Abel terms are differentiable functions of `s`. -/
private lemma abelTerm_differentiableOn (χ : DirichletCharacter ℂ N) {U : Set ℂ}
    (k : ℕ) : DifferentiableOn ℂ (fun s : ℂ => abelTerm χ s k) U := by
  by_cases hk : k = 0
  · subst k
    have hfun : (fun s : ℂ => abelTerm χ s 0) = 0 := by
      funext s
      exact abelTerm_zero χ s
    rw [hfun]
    intro z hz
    exact (differentiableAt_const (0 : ℂ)).differentiableWithinAt
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hbase : ((k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hkpos)
    refine DifferentiableOn.mul ?_ ?_
    · intro z hz
      exact (differentiableAt_const (partSum χ k)).differentiableWithinAt
    · have h1 : DifferentiableOn ℂ (fun s : ℂ => (k : ℂ) ^ (-s)) U := by
        intro z hz
        exact (DifferentiableAt.const_cpow differentiableAt_id.neg (Or.inl hbase)).differentiableWithinAt
      have h2 : DifferentiableOn ℂ (fun s : ℂ => ((k + 1 : ℕ) : ℂ) ^ (-s)) U := by
        intro z hz
        have hb : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : (k + 1 : ℕ) ≠ 0)
        exact (DifferentiableAt.const_cpow differentiableAt_id.neg (Or.inl hb)).differentiableWithinAt
      exact h1.sub h2

/-- Integral identity for the real rpow. -/
private lemma integral_real_rpow_sub (k : ℕ) (hk : 1 ≤ k) (σ : ℝ) (hσ : 0 < σ) :
    (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), x ^ (-σ - 1))
      = (((k : ℝ) ^ (-σ)) - (((k + 1 : ℕ) : ℝ) ^ (-σ))) / σ := by
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hnot0 : 0 ∉ Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    intro hx
    have hx' : (0 : ℝ) ∈ Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
      simpa [Set.uIcc_of_le hkle] using hx
    linarith only [hx'.1, show (0 : ℝ) < (k : ℝ) by exact_mod_cast (by omega : 0 < k), hx', hk]
  have hne : -σ - 1 ≠ (-1 : ℝ) := by linarith only [hσ]
  have hint := integral_rpow (r := -σ - 1) (a := (k : ℝ)) (b := ((k + 1 : ℕ) : ℝ))
    (Or.inr ⟨hne, hnot0⟩)
  rw [hint]
  have hD : -σ - 1 + 1 = -σ := by ring
  rw [hD]
  field_simp [ne_of_gt hσ]
  ring

/-- The rpow function is integrable and bounded on the interval `[k, k+1]`. -/
private lemma interval_rpow_bound (k : ℕ) (hk : 1 ≤ k) (σ : ℝ) (hσ : 0 < σ) :
    (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), x ^ (-σ - 1)) ≤ (k : ℝ) ^ (-σ - 1) := by
  let f : ℝ → ℝ := fun x => x ^ (-σ - 1)
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hanti0 : AntitoneOn f (Set.Ioi (0 : ℝ)) := by
    dsimp [f]
    exact Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (r := -σ - 1) (by linarith only [hσ])
  have hanti : AntitoneOn f (Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ)) := by
    rw [Set.uIcc_of_le hkle]
    exact hanti0.mono (by
      intro x hx
      exact Set.mem_Ioi.mpr (lt_of_lt_of_le hk0 (Set.mem_Icc.mp hx).1))
  have hintf : IntervalIntegrable f volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := hanti.intervalIntegrable
  have hmono : ∀ x ∈ Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ), f x ≤ f (k : ℝ) := by
    intro x hx
    dsimp [f]
    have hkx : (k : ℝ) ≤ x := (Set.mem_Icc.mp hx).1
    exact Real.rpow_le_rpow_of_nonpos hk0 hkx (by linarith only [hσ] : -σ - 1 ≤ 0)
  let g : ℝ → ℝ := fun _ => f (k : ℝ)
  have hintg : IntervalIntegrable g volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    dsimp [g]
    exact intervalIntegrable_const
  have hmain : (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), f x)
      ≤ ∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), g x := by
    exact intervalIntegral.integral_mono_on hkle hintf hintg (by simpa [g] using hmono)
  calc
    (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), f x) ≤ (k : ℝ) ^ (-σ - 1) := by
      have hg : (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), g x) = f (k : ℝ) := by
        dsimp [g]
        simp
      calc
        (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), f x) ≤ ∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), g x := hmain
        _ = f (k : ℝ) := hg
        _ = (k : ℝ) ^ (-σ - 1) := rfl

/-- Coarse `k^{-σ-1}` bound for the difference of consecutive powers. -/
private lemma norm_cpow_sub_le_pow (k : ℕ) (hk : 1 ≤ k) (s : ℂ) (hs : 0 < s.re) :
    ‖((k : ℂ) ^ (-s)) - (((k + 1 : ℕ) : ℂ) ^ (-s))‖ ≤ ‖s‖ * (k : ℝ) ^ (-s.re - 1) := by
  have hInt : (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), x ^ (-s.re - 1))
      = (((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) / s.re := integral_real_rpow_sub k hk s.re hs
  have hbnd : (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), x ^ (-s.re - 1)) ≤ (k : ℝ) ^ (-s.re - 1) := interval_rpow_bound k hk s.re hs
  have hdiff : ((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re)) ≤ s.re * (k : ℝ) ^ (-s.re - 1) := by
    have hpos : 0 ≤ s.re := le_of_lt hs
    calc
      ((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))
          = s.re * (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), x ^ (-s.re - 1)) := by
            rw [hInt]
            field_simp [ne_of_gt hs]
      _ ≤ s.re * (k : ℝ) ^ (-s.re - 1) := mul_le_mul_of_nonneg_left hbnd hpos
  have hb := norm_cpow_sub_le k hk s hs
  calc
    ‖((k : ℂ) ^ (-s)) - (((k + 1 : ℕ) : ℂ) ^ (-s))‖ ≤ (‖s‖ / s.re) * (((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) := hb
    _ ≤ (‖s‖ / s.re) * (s.re * (k : ℝ) ^ (-s.re - 1)) := by
          exact mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ = ‖s‖ * (k : ℝ) ^ (-s.re - 1) := by
          field_simp [ne_of_gt hs]




/-- Pointwise bound of Abel terms on a small ball (uniform in the parameter). -/
private lemma abelTerm_bound_on_ball (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z0 : ℂ)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ2 : 2 * ρ ≤ z0.re) {z : ℂ} (hz : z ∈ Metric.ball z0 ρ) (k : ℕ) :
    ‖abelTerm χ z k‖ ≤ (2 * (N : ℝ)) * (‖z0‖ + ρ) * ((k : ℝ) ^ (-ρ - 1)) := by
  have hdz : ‖z - z0‖ < ρ := by
    simpa [dist_eq_norm] using Metric.mem_ball.mp hz
  have hzre : ρ ≤ z.re := by
    have hre : -‖z - z0‖ ≤ (z - z0).re := by
      have h := abs_re_le_norm (z - z0)
      exact (abs_le.mp h).1
    have h3 : (z - z0).re = z.re - z0.re := by simp
    rw [h3] at hre
    have hlow : z0.re - ‖z - z0‖ ≤ z.re := by linarith only [hre]
    calc
      ρ ≤ z0.re - ρ := by linarith only [hρ2]
      _ ≤ z0.re - ‖z - z0‖ := by linarith only [hdz]
      _ ≤ z.re := hlow
  have hznorm : ‖z‖ ≤ ‖z0‖ + ρ := by
    calc
      ‖z‖ = ‖z0 + (z - z0)‖ := congrArg norm (by ring)
      _ ≤ ‖z0‖ + ‖z - z0‖ := norm_add_le _ _
      _ ≤ ‖z0‖ + ρ := by linarith only [hdz]
  by_cases hk : k = 0
  · subst k
    rw [abelTerm_zero]
    rw [norm_zero]
    have hpowpos : 0 ≤ (((0 : ℕ) : ℝ)) ^ (-ρ - 1) := Real.rpow_nonneg (by norm_num) (-ρ - 1)
    exact mul_nonneg (by positivity) hpowpos
  · have hk1 : 1 ≤ k := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hk)
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hkbase : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hpowle : (k : ℝ) ^ (-z.re - 1) ≤ (k : ℝ) ^ (-ρ - 1) := by
      have hexp : -z.re - 1 ≤ -ρ - 1 := by linarith only [hzre]
      exact Real.rpow_le_rpow_of_exponent_le hkbase hexp
    have hzpos : 0 < z.re := lt_of_lt_of_le hρ0 hzre
    have hb := norm_cpow_sub_le_pow k hk1 z hzpos
    have hS := partSum_bound χ hχ k hk1
    calc
      ‖abelTerm χ z k‖ = ‖partSum χ k‖ * ‖((k : ℂ) ^ (-z)) - (((k + 1 : ℕ) : ℂ) ^ (-z))‖ := by
        dsimp [abelTerm]
        rw [norm_mul]
      _ ≤ (2 * (N : ℝ)) * ‖((k : ℂ) ^ (-z)) - (((k + 1 : ℕ) : ℂ) ^ (-z))‖ := by
        exact mul_le_mul_of_nonneg_right hS (norm_nonneg _)
      _ ≤ (2 * (N : ℝ)) * (‖z‖ * (k : ℝ) ^ (-z.re - 1)) := by
        exact mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ (2 * (N : ℝ)) * ((‖z0‖ + ρ) * (k : ℝ) ^ (-z.re - 1)) := by
        have hpowpos : 0 ≤ (k : ℝ) ^ (-z.re - 1) := by positivity
        have hmul : ‖z‖ * (k : ℝ) ^ (-z.re - 1) ≤ (‖z0‖ + ρ) * (k : ℝ) ^ (-z.re - 1) := by
          exact mul_le_mul_of_nonneg_right hznorm hpowpos
        exact mul_le_mul_of_nonneg_left hmul (by positivity)
      _ ≤ (2 * (N : ℝ)) * ((‖z0‖ + ρ) * (k : ℝ) ^ (-ρ - 1)) := by
        have hzadd : (‖z0‖ + ρ) * (k : ℝ) ^ (-z.re - 1) ≤ (‖z0‖ + ρ) * (k : ℝ) ^ (-ρ - 1) := by
          exact mul_le_mul_of_nonneg_left hpowle (by positivity : 0 ≤ ‖z0‖ + ρ)
        exact mul_le_mul_of_nonneg_left hzadd (by positivity)
      _ = (2 * (N : ℝ)) * (‖z0‖ + ρ) * (k : ℝ) ^ (-ρ - 1) := by ac_rfl



/-- `abelCont` is differentiable on a ball around any point with positive real part. -/
private lemma abelCont_differentiableOn_ball (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z0 : ℂ)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ2 : 2 * ρ ≤ z0.re) :
    DifferentiableOn ℂ (abelCont χ) (Metric.ball z0 ρ) := by
  let u : ℕ → ℝ := fun k => if k = 0 then 0 else
    (2 * (N : ℝ)) * (‖z0‖ + ρ) * ((k : ℝ) ^ (-ρ - 1))
  have hu_add : Summable (fun k : ℕ => u (k + 1)) := by
    have hfun : (fun k : ℕ => u (k + 1)) = fun k : ℕ =>
        (2 * (N : ℝ)) * (‖z0‖ + ρ) * (((k + 1 : ℕ) : ℝ) ^ (-ρ - 1)) := by
      funext k
      simp [u]
    rw [hfun]
    have hp : -ρ - 1 < -1 := by linarith only [hρ0]
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-ρ - 1)) := (Real.summable_nat_rpow).mpr hp
    have hshift : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-ρ - 1)) := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-ρ - 1)) 1).2 hbase
    exact hshift.mul_left ((2 * (N : ℝ)) * (‖z0‖ + ρ))
  have hu : Summable u := (summable_nat_add_iff 1).1 hu_add
  refine differentiableOn_tsum_of_summable_norm hu ?_ ?_ ?_
  · intro k
    exact abelTerm_differentiableOn χ k
  · exact Metric.isOpen_ball
  · intro k w hw
    by_cases hk : k = 0
    · subst k
      dsimp [u]
      rw [abelTerm_zero]
      norm_num
    · have hk1 : 1 ≤ k := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hk)
      have hb := abelTerm_bound_on_ball χ hχ z0 (ρ := ρ) hρ0 hρ2 hw k
      dsimp [u]
      simp [hk]
      exact hb

/-- `abelCont` is differentiable on the right half-plane. -/
private lemma abelCont_differentiableOn_re_pos (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (abelCont χ) {z : ℂ | 0 < z.re} := by
  intro z0 hz0
  let ρ : ℝ := z0.re / 2
  have hρ0 : 0 < ρ := by dsimp [ρ]; exact div_pos hz0 (by norm_num)
  have hρ2 : 2 * ρ ≤ z0.re := by dsimp [ρ]; field_simp; exact le_rfl
  have hb := abelCont_differentiableOn_ball χ hχ z0 (ρ := ρ) hρ0 hρ2
  have hdz : DifferentiableAt ℂ (abelCont χ) z0 :=
    hb.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ0))
  exact hdz.differentiableWithinAt

/-- `abelCont` is holomorphic on the right half-plane. -/
private lemma abelCont_analyticOn_re_pos (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    AnalyticOnNhd ℂ (abelCont χ) {z : ℂ | 0 < z.re} := by
  exact (abelCont_differentiableOn_re_pos χ hχ).analyticOnNhd (isOpen_lt continuous_const continuous_re)




/-- For `Re s > 1` the Abel continuation agrees with the actual L-function. -/
private lemma LFunction_eq_abelCont_of_one_lt_re (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : 1 < s.re) : LFunction χ s = abelCont χ s := by
  let f : ℕ → ℂ := fun n => (χ (n : ZMod N) : ℂ)
  have hs0 : 0 < s.re := by linarith only [hs]
  have hterm_sum : Summable (fun n : ℕ => LSeries.term f s n) := by
    refine Summable.of_norm_bounded_eventually (f := fun n : ℕ => LSeries.term f s n)
      (g := fun n : ℕ => (n : ℝ) ^ (-s.re)) ?_ ?_
    · have hp : -s.re < -1 := by linarith only [hs]
      exact (Real.summable_nat_rpow).mpr hp
    · filter_upwards [eventually_cofinite_ne (0 : ℕ)] with n hn
      rw [LSeries.norm_term_eq]
      rw [if_neg hn]
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hc : ‖f n‖ ≤ 1 := by
        dsimp [f]
        exact char_coeff_le_one χ n
      have hp : 0 < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos hnpos s.re
      calc
        ‖f n‖ / (n : ℝ) ^ s.re ≤ 1 / (n : ℝ) ^ s.re := by
          exact div_le_div_of_nonneg_right hc (le_of_lt hp)
        _ = (n : ℝ) ^ (-s.re) := by
          have hinv : (1 : ℝ) / (n : ℝ) ^ s.re = (n : ℝ) ^ (-s.re) := by
            rw [Real.rpow_neg (le_of_lt hnpos)]
            rw [one_div]
          exact hinv

  have hpart_L : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M, LSeries.term f s n) atTop (𝓝 (LSeries f s)) := by
    exact hterm_sum.hasSum.tendsto_sum_nat
  have hA_sum := abelTerm_summable χ hχ s hs0
  have hpart_A : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M, abelTerm χ s n) atTop (𝓝 (abelCont χ s)) := by
    dsimp [abelCont]
    exact hA_sum.hasSum.tendsto_sum_nat
  have hNpow0 : Tendsto (fun M : ℕ => ((M : ℕ) : ℝ) ^ (-s.re)) atTop (𝓝 0) := by
    have hto : Tendsto (fun M : ℕ => ((M : ℕ) : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hdec : Tendsto (fun t : ℝ => t ^ (-s.re)) atTop (𝓝 0) := by
      have hmain : Tendsto (fun t : ℝ => (t ^ s.re)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop (by linarith only [hs] : 0 < s.re))
      refine hmain.congr' ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      rw [Real.rpow_neg (by linarith only [ht] : 0 ≤ t) s.re]
    exact hdec.comp hto
  have hc_bound : ∀ M : ℕ, ‖partSum χ M * (M : ℂ) ^ (-s)‖ ≤ (2 * (N : ℝ)) * ((M : ℕ) : ℝ) ^ (-s.re) := by
    intro M
    by_cases hM0 : M = 0
    · subst M
      simp [partSum]
      positivity
    · have hM1 : 1 ≤ M := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hM0)
      have hS := partSum_bound χ hχ M hM1
      have hx0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
      have hpow : ‖(M : ℂ) ^ (-s)‖ = (M : ℝ) ^ (-s.re) := by
        have hb : ((M : ℕ) : ℂ) = ((((M : ℕ) : ℝ) : ℂ)) := by norm_num
        rw [hb]
        have h := Complex.norm_cpow_eq_rpow_re_of_pos hx0 (-s)
        rw [h]
        rw [Complex.neg_re]
      calc
        ‖partSum χ M * (M : ℂ) ^ (-s)‖ ≤ ‖partSum χ M‖ * ‖(M : ℂ) ^ (-s)‖ := norm_mul_le _ _
        _ ≤ (2 * (N : ℝ)) * ‖(M : ℂ) ^ (-s)‖ := mul_le_mul_of_nonneg_right hS (norm_nonneg _)
        _ = (2 * (N : ℝ)) * ((M : ℝ) ^ (-s.re)) := by rw [hpow]
  have hc0 : Tendsto (fun M : ℕ => partSum χ M * (M : ℂ) ^ (-s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (f := fun M : ℕ => ‖partSum χ M * (M : ℂ) ^ (-s)‖)
      (g := fun M : ℕ => (2 * (N : ℝ)) * ((M : ℕ) : ℝ) ^ (-s.re)) ?_ ?_ ?_
    · intro M
      exact norm_nonneg _
    · intro M
      exact hc_bound M
    · have hb : Tendsto (fun M : ℕ => (2 * (N : ℝ)) * ((M : ℕ) : ℝ) ^ (-s.re)) atTop (𝓝 0) := by
        have hzero : Tendsto (fun M : ℕ => (2 * (N : ℝ)) * ((M : ℕ) : ℝ) ^ (-s.re)) atTop (𝓝 ((2 * (N : ℝ)) * 0)) := tendsto_const_nhds.mul hNpow0
        simpa using hzero
      exact hb
  have hshift_lemma : Tendsto (fun M : ℕ => M + 1) atTop atTop := by
    exact tendsto_atTop_mono (f := fun M : ℕ => M) (g := fun M : ℕ => M + 1) (fun M => by omega) tendsto_id
  have hpart_L' : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range (M + 1), LSeries.term f s n) atTop (𝓝 (LSeries f s)) := hpart_L.comp hshift_lemma
  have hrhs (M : ℕ) : (∑ n ∈ Finset.Icc 1 M, (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-s))
      = ∑ n ∈ Finset.range (M + 1), LSeries.term f s n := by
    -- range (M+1) = insert 0 (Icc 1 M)
    have hrange : Finset.range (M + 1) = insert 0 (Finset.Icc 1 M) := by
      ext n
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      constructor
      · intro h
        by_cases hn : n = 0
        · exact Or.inl hn
        · exact Or.inr ⟨Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn), by omega⟩
      · intro h
        rcases h with hn | hn
        · subst n
          omega
        · omega
    rw [hrange, Finset.sum_insert]
    · have h0 : LSeries.term f s 0 = 0 := LSeries.term_zero f s
      rw [h0, zero_add]
      apply Finset.sum_congr rfl
      intro n hn
      have hn1' : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn0 : n ≠ 0 := by omega
      have hterm := LSeries.term_of_ne_zero hn0
      rw [hterm]
      dsimp [f]
      have hdiv : ((χ (n : ZMod N) : ℂ)) / (n : ℂ) ^ s = ((χ (n : ZMod N) : ℂ)) * (n : ℂ) ^ (-s) := by
        have hnz : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
        rw [div_eq_mul_inv]
        rw [← cpow_neg]
      rw [hdiv]
    · have h0mem : 0 ∉ Finset.Icc 1 M := by
        rw [Finset.mem_Icc]
        omega
      exact h0mem
  have hrel (M : ℕ) : (∑ n ∈ Finset.range M, abelTerm χ s n)
      = (∑ n ∈ Finset.range (M + 1), LSeries.term f s n) - partSum χ M * (M : ℂ) ^ (-s) := by
    by_cases hM : M = 0
    · subst M
      simp [abelTerm_zero, partSum, LSeries.term_zero]
    · have hM1 : 1 ≤ M := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hM)
      have hh := abelTerm_head_eq χ s M hM1
      rw [hrhs M] at hh
      calc
        (∑ n ∈ Finset.range M, abelTerm χ s n)
            = ((∑ n ∈ Finset.range M, abelTerm χ s n) + partSum χ M * (M : ℂ) ^ (-s)) - partSum χ M * (M : ℂ) ^ (-s) := by ring
        _ = (∑ n ∈ Finset.range (M + 1), LSeries.term f s n) - partSum χ M * (M : ℂ) ^ (-s) := by rw [hh]
  have hpart_A2 : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M, abelTerm χ s n) atTop (𝓝 (LSeries f s)) := by
    -- partialA M = partialL(M+1) − c M: tendsto of RHS is LSeries − 0:
    have hsub : Tendsto (fun M : ℕ => (∑ n ∈ Finset.range (M + 1), LSeries.term f s n) - partSum χ M * (M : ℂ) ^ (-s))
        atTop (𝓝 (LSeries f s - 0)) := hpart_L'.sub hc0
    have hval : (LSeries f s - 0) = LSeries f s := by ring
    rw [hval] at hsub
    exact hsub.congr (fun M => (hrel M).symm)
  have heq : abelCont χ s = LSeries f s := tendsto_nhds_unique hpart_A hpart_A2
  have hL := LFunction_eq_LSeries χ hs
  rw [hL, heq]




/-- `LFunction` and the Abel continuation agree on the right half-plane. -/
private lemma LFunction_eq_abelCont_on_re_pos (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    Set.EqOn (LFunction χ) (abelCont χ) {z : ℂ | 0 < z.re} := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hL : AnalyticOnNhd ℂ (LFunction χ) U := by
    refine (DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const continuous_re))
    intro z hz
    exact (differentiable_LFunction hχ z).differentiableWithinAt
  have hA : AnalyticOnNhd ℂ (abelCont χ) U := abelCont_analyticOn_re_pos χ hχ
  have hpc : IsPreconnected U := by
    dsimp [U]
    apply Convex.isPreconnected
    intro x hx y hy a b ha hb hab
    have hx0 : 0 < x.re := hx
    have hy0 : 0 < y.re := hy
    have hre : ((a • x + b • y) : ℂ).re = a * x.re + b * y.re := by
      simp [smul_eq_mul, Complex.mul_re]
    change 0 < (a • x + b • y).re
    rw [hre]
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith only [hab, ha0, ha]
      rw [ha0, hb1]
      simpa using hy0
    · have hb1 : 0 < a := lt_of_le_of_ne ha (by intro h; exact ha0 h.symm)
      have h : 0 ≤ b * y.re := mul_nonneg hb (le_of_lt hy0)
      have h2 : 0 < a * x.re := mul_pos hb1 hx0
      linarith only [h, h2]
  have hz2 : (2 : ℂ) ∈ U := by dsimp [U]; norm_num
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hL hA hpc hz2 ?_
  filter_upwards [(show {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) from
    (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re))] with z hz
  exact LFunction_eq_abelCont_of_one_lt_re χ hχ hz






/-- **Uniform polynomial bound for the Dirichlet L-function in the right half-plane.**
For a non-trivial character `χ mod N` and every `s` with `0 < Re s`,
`‖LFunction χ s‖ ≤ 2·(N:ℝ)·‖s‖/Re s`. -/
theorem LFunction_norm_half_plane {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖LFunction χ s‖ ≤ 2 * (N : ℝ) * ‖s‖ / s.re := by
  have hmem : s ∈ ({z : ℂ | 0 < z.re} : Set ℂ) := by simpa using hs
  have hL : LFunction χ s = abelCont χ s := LFunction_eq_abelCont_on_re_pos χ hχ hmem
  have hsplit := abelCont_eq_head_add_tail χ hχ s hs 1
  have htail := abelTerm_tail_bound χ hχ s hs 1 (by norm_num : 1 ≤ (1 : ℕ))
  have habel : abelCont χ s = ∑' m : ℕ, abelTerm χ s (1 + m) := by
    rw [hsplit]
    simp [abelTerm_zero]
  have htail' : ‖∑' m : ℕ, abelTerm χ s (1 + m)‖ ≤ 2 * (N : ℝ) * ‖s‖ / s.re := by
    calc
      ‖∑' m : ℕ, abelTerm χ s (1 + m)‖
          ≤ (2 * (N : ℝ)) * (‖s‖ / s.re) * (((1 : ℕ) : ℝ) ^ (-s.re)) := htail
      _ = (2 * (N : ℝ)) * (‖s‖ / s.re) := by
            have hpow : (((1 : ℕ) : ℝ) ^ (-s.re)) = 1 := by norm_num
            rw [hpow, mul_one]
      _ = 2 * (N : ℝ) * ‖s‖ / s.re := by
            field_simp [ne_of_gt hs]
  calc
    ‖LFunction χ s‖ = ‖abelCont χ s‖ := by rw [hL]
    _ = ‖∑' m : ℕ, abelTerm χ s (1 + m)‖ := by rw [habel]
    _ ≤ 2 * (N : ℝ) * ‖s‖ / s.re := htail'

end Commons.NumberTheory.DirichletCharacter
