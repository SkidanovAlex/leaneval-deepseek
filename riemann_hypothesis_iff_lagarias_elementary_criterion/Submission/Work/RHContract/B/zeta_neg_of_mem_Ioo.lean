import Mathlib
import Submission.Commons.NumberTheory.Zeta.isPreconnected_re_gt_sdiff

namespace Work.RHContract.B

open Complex Filter Topology Set MeasureTheory
open scoped Real BigOperators Interval

noncomputable section

/-!
# `ζ(t) < 0` for `0 < t < 1`

Classical *Abel-regularised* Dirichlet-eta argument.  Writing `A_k = Σ_{j=1}^k (-1)^{j-1} ∈ {0,1}`
and `η(s) = Σ (-1)^{n-1} n^{-s}`, Abel summation gives

  `η(s) = Σ_{k≥1} A_k (k^{-s} - (k+1)^{-s})`   (`= abelEta s`),

absolutely convergent (hence analytic) for `re s > 0`.  For `re s > 1` it agrees with
`(1 - 2^{1-s}) ζ(s)`, and by analytic continuation this persists on `{re s > 0} \ {1}`.
Since every summand `A_k (k^{-t} - (k+1)^{-t})` is a nonnegative real for real `t > 0`,
`0 < abelEta t = (1 - 2^{1-t}) ζ(t)` and therefore `ζ(t) < 0`.
-/

/-- The `n`-th partial sum `A_n = 1 - 1 + 1 - ⋯` (n terms) of the alternating series.
It equals `1` for odd `n` and `0` for even `n`. -/
def altR (n : ℕ) : ℂ := (1 - (-1 : ℂ) ^ n) / 2

lemma altR_zero : altR 0 = 0 := by simp [altR]

lemma altR_one : altR 1 = 1 := by norm_num [altR]

lemma altR_succ (n : ℕ) : altR (n + 1) = altR n + (-1 : ℂ) ^ n := by
  have h : (-1 : ℂ) ^ (n + 1) = -(-1 : ℂ) ^ n := by rw [pow_succ]; ring
  simp only [altR, h]
  ring

lemma altR_norm_le (n : ℕ) : ‖altR n‖ ≤ 1 := by
  rcases Nat.even_or_odd n with h | h
  · rw [altR, h.neg_one_pow]; norm_num
  · rw [altR, h.neg_one_pow]; norm_num

/-- The `n`-th term of the Abel-regularised eta series (`k = n+1`). -/
def etaTerm (s : ℂ) (n : ℕ) : ℂ :=
  altR (n + 1) * (((n + 1 : ℕ) : ℂ) ^ (-s) - (((n + 1 + 1 : ℕ)) : ℂ) ^ (-s))

/-- The Abel regularisation of the Dirichlet eta function: an *absolutely convergent* series
for `0 < re s`. -/
def abelEta (s : ℂ) : ℂ := ∑' n : ℕ, etaTerm s n

/-! ## Elementary calculus lemmas for `cpow` differences -/

private lemma re_neg_sub_one (s : ℂ) : (-s - 1).re = -s.re - 1 := by
  simp [Complex.neg_re, Complex.sub_re, Complex.one_re]

private lemma norm_cpow_sub_integrand (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-s.re - 1) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx (-s - 1), re_neg_sub_one]

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
        linarith [hx'.1, show (0 : ℝ) < (k : ℝ) by exact_mod_cast (by omega : 0 < k)]
      have hne : -s.re - 1 ≠ (-1 : ℝ) := by linarith
      have hint := integral_rpow (r := -s.re - 1) (a := (k : ℝ)) (b := ((k + 1 : ℕ) : ℝ))
        (Or.inr ⟨hne, hnot0⟩)
      rw [hint]
      have hD : -s.re - 1 + 1 = -s.re := by ring
      rw [hD]
      have hσ : s.re ≠ 0 := ne_of_gt hs
      field_simp [hσ]
      ring

private lemma cpow_sub_eq_smul_integral (k : ℕ) (hk : 1 ≤ k) (s : ℂ) (hs : 0 < s.re) :
    ((k : ℂ) ^ (-s) - (((k + 1 : ℕ) : ℂ) ^ (-s)))
      = s * (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x : ℂ) ^ (-s - 1)) := by
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hnot0 : 0 ∉ Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    intro hx
    have hx' : (0 : ℝ) ∈ Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
      simpa [Set.uIcc_of_le hkle] using hx
    linarith [hx'.1, show (0 : ℝ) < (k : ℝ) by exact_mod_cast (by omega : 0 < k)]
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
    rw [hint, hD]
    simp
  have hsnz : s ≠ 0 := by
    intro h
    exact (ne_of_gt hs) (by simpa [h] : s.re = 0)
  rw [hinteq]
  field_simp
  ring

private lemma norm_cpow_sub_le (k : ℕ) (hk : 1 ≤ k) (s : ℂ) (hs : 0 < s.re) :
    ‖((k : ℂ) ^ (-s)) - (((k + 1 : ℕ) : ℂ) ^ (-s))‖
      ≤ (‖s‖ / s.re) * (((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) := by
  have hsub := cpow_sub_eq_smul_integral k hk s hs
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  calc
    ‖((k : ℂ) ^ (-s)) - (((k + 1 : ℕ) : ℂ) ^ (-s))‖
        = ‖s * (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x : ℂ) ^ (-s - 1))‖ := by rw [hsub]
    _ ≤ ‖s‖ * ‖(∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x : ℂ) ^ (-s - 1))‖ := norm_mul_le _ _
    _ ≤ ‖s‖ * (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), ‖(x : ℂ) ^ (-s - 1)‖) := by
            exact mul_le_mul_of_nonneg_left
              (intervalIntegral.norm_integral_le_integral_norm hkle) (norm_nonneg s)
    _ = ‖s‖ * ((((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) / s.re) := by
            rw [integral_norm_cpow_sub k hk s hs]
    _ = (‖s‖ / s.re) * (((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) := by
            field_simp [ne_of_gt hs]

/-- Telescoping `HasSum` for the difference sequence `(X+m)^{-β} - (X+m+1)^{-β}`. -/
private lemma hasSum_telescope_rpow (X : ℕ) (hX : 1 ≤ X) {β : ℝ} (hβ : 0 < β) :
    HasSum (fun m : ℕ => (((X + m : ℕ) : ℝ) ^ (-β)) - (((X + m + 1 : ℕ) : ℝ) ^ (-β)))
      ((X : ℝ) ^ (-β)) := by
  have h_nonneg : ∀ m : ℕ, 0 ≤ (((X + m : ℕ) : ℝ) ^ (-β)) - (((X + m + 1 : ℕ) : ℝ) ^ (-β)) := by
    intro m
    have hbase1 : (0 : ℝ) < ((X + m : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have hle : ((X + m : ℕ) : ℝ) ≤ ((X + m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have hpow : (((X + m + 1 : ℕ) : ℝ) ^ (-β)) ≤ (((X + m : ℕ) : ℝ) ^ (-β)) := by
      exact Real.rpow_le_rpow_of_nonpos hbase1 hle (by linarith : -β ≤ 0)
    exact sub_nonneg.mpr hpow
  have hto : Tendsto (fun N : ℕ => ((X + N : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_atTop_mono (f := fun N : ℕ => (N : ℝ)) (g := fun N : ℕ => ((X + N : ℕ) : ℝ))
      (fun N => by exact_mod_cast (by omega : N ≤ X + N)) tendsto_natCast_atTop_atTop
  have hdec : Tendsto (fun t : ℝ => t ^ (-β)) atTop (𝓝 0) := by
    have hmain : Tendsto (fun t : ℝ => (t ^ β)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop hβ)
    refine hmain.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [Real.rpow_neg (by linarith : 0 ≤ t) β]
  have hN0 : Tendsto (fun N : ℕ => ((X + N : ℕ) : ℝ) ^ (-β)) atTop (𝓝 0) := hdec.comp hto
  have hmain_t : Tendsto (fun N : ℕ => (X : ℝ) ^ (-β) - ((X + N : ℕ) : ℝ) ^ (-β)) atTop
      (𝓝 ((X : ℝ) ^ (-β))) := by
    simpa using (tendsto_const_nhds.sub hN0 :
      Tendsto (fun N : ℕ => (X : ℝ) ^ (-β) - ((X + N : ℕ) : ℝ) ^ (-β)) atTop
        (𝓝 ((X : ℝ) ^ (-β) - 0)))
  have hsumN : ∀ N : ℕ,
      (∑ m ∈ Finset.range N, ((((X + m : ℕ) : ℝ) ^ (-β)) - (((X + m + 1 : ℕ) : ℝ) ^ (-β))))
        = (X : ℝ) ^ (-β) - (((X + N : ℕ) : ℝ) ^ (-β)) := by
    intro N
    simpa [Nat.add_assoc] using (Finset.sum_range_sub' (fun j : ℕ => ((X + j : ℕ) : ℝ) ^ (-β)) N)
  have hpartial : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N,
      ((((X + m : ℕ) : ℝ) ^ (-β)) - (((X + m + 1 : ℕ) : ℝ) ^ (-β)))) atTop (𝓝 ((X : ℝ) ^ (-β))) :=
    hmain_t.congr (fun N => (hsumN N).symm)
  exact (hasSum_iff_tendsto_nat_of_nonneg h_nonneg ((X : ℝ) ^ (-β))).2 hpartial

/-- The Abel-regularised eta series is absolutely summable for `0 < re s`. -/
lemma etaTerm_summable (s : ℂ) (hs : 0 < s.re) : Summable (fun n : ℕ => etaTerm s n) := by
  have htelesc : Summable (fun m : ℕ =>
      (((1 + m : ℕ) : ℝ) ^ (-s.re)) - (((1 + m + 1 : ℕ) : ℝ) ^ (-s.re))) :=
    (hasSum_telescope_rpow 1 (by norm_num) hs).summable
  have ht : Summable (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ) ^ (-s.re)) - (((n + 1 + 1 : ℕ) : ℝ) ^ (-s.re))) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htelesc
  refine Summable.of_norm_bounded (g := fun n : ℕ =>
    (‖s‖ / s.re) * ((((n + 1 : ℕ) : ℝ) ^ (-s.re)) - (((n + 1 + 1 : ℕ) : ℝ) ^ (-s.re)))) ?_ ?_
  · exact ht.mul_left _
  · intro n
    have hb := norm_cpow_sub_le (n + 1) (by omega) s hs
    calc ‖etaTerm s n‖
        = ‖altR (n + 1)‖ * ‖(((n + 1 : ℕ) : ℂ) ^ (-s)) - (((n + 1 + 1 : ℕ) : ℂ) ^ (-s))‖ := by
          rw [etaTerm, norm_mul]
      _ ≤ 1 * ‖(((n + 1 : ℕ) : ℂ) ^ (-s)) - (((n + 1 + 1 : ℕ) : ℂ) ^ (-s))‖ := by
          exact mul_le_mul_of_nonneg_right (altR_norm_le _) (norm_nonneg _)
      _ ≤ (‖s‖ / s.re) * ((((n + 1 : ℕ) : ℝ) ^ (-s.re)) - (((n + 1 + 1 : ℕ) : ℝ) ^ (-s.re))) := by
          rw [one_mul]; exact hb

/-! ## Analyticity of the Abel-regularised eta series on `{re s > 0}` -/

/-- Integral identity for the real rpow. -/
private lemma integral_real_rpow_sub (k : ℕ) (hk : 1 ≤ k) (σ : ℝ) (hσ : 0 < σ) :
    (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), x ^ (-σ - 1))
      = (((k : ℝ) ^ (-σ)) - (((k + 1 : ℕ) : ℝ) ^ (-σ))) / σ := by
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hnot0 : 0 ∉ Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    intro hx
    have hx' : (0 : ℝ) ∈ Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
      simpa [Set.uIcc_of_le hkle] using hx
    linarith [hx'.1, show (0 : ℝ) < (k : ℝ) by exact_mod_cast (by omega : 0 < k)]
  have hne : -σ - 1 ≠ (-1 : ℝ) := by linarith
  have hint := integral_rpow (r := -σ - 1) (a := (k : ℝ)) (b := ((k + 1 : ℕ) : ℝ))
    (Or.inr ⟨hne, hnot0⟩)
  rw [hint]
  have hD : -σ - 1 + 1 = -σ := by ring
  rw [hD]
  field_simp [ne_of_gt hσ]
  ring

/-- The rpow function is bounded on the interval `[k, k+1]` by its value at `k`. -/
private lemma interval_rpow_bound (k : ℕ) (hk : 1 ≤ k) (σ : ℝ) (hσ : 0 < σ) :
    (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), x ^ (-σ - 1)) ≤ (k : ℝ) ^ (-σ - 1) := by
  let f : ℝ → ℝ := fun x => x ^ (-σ - 1)
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hanti0 : AntitoneOn f (Set.Ioi (0 : ℝ)) := by
    dsimp [f]
    exact Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (r := -σ - 1) (by linarith)
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
    exact Real.rpow_le_rpow_of_nonpos hk0 hkx (by linarith : -σ - 1 ≤ 0)
  let g : ℝ → ℝ := fun _ => f (k : ℝ)
  have hintg : IntervalIntegrable g volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    dsimp [g]; exact intervalIntegrable_const
  have hmain : (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), f x)
      ≤ ∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), g x :=
    intervalIntegral.integral_mono_on hkle hintf hintg (by simpa [g] using hmono)
  calc
    (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), f x) ≤ (k : ℝ) ^ (-σ - 1) := by
      calc
        (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), f x)
            ≤ ∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), g x := hmain
        _ = f (k : ℝ) := by dsimp [g]; simp
        _ = (k : ℝ) ^ (-σ - 1) := rfl

/-- Coarse bound for the difference of consecutive complex powers. -/
private lemma norm_cpow_sub_le_pow (k : ℕ) (hk : 1 ≤ k) (s : ℂ) (hs : 0 < s.re) :
    ‖((k : ℂ) ^ (-s)) - (((k + 1 : ℕ) : ℂ) ^ (-s))‖ ≤ ‖s‖ * (k : ℝ) ^ (-s.re - 1) := by
  have hInt : (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), x ^ (-s.re - 1))
      = (((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) / s.re :=
    integral_real_rpow_sub k hk s.re hs
  have hbnd : (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), x ^ (-s.re - 1))
      ≤ (k : ℝ) ^ (-s.re - 1) := interval_rpow_bound k hk s.re hs
  have hdiff : ((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))
      ≤ s.re * (k : ℝ) ^ (-s.re - 1) := by
    have hpos : 0 ≤ s.re := le_of_lt hs
    calc
      ((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))
          = s.re * (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), x ^ (-s.re - 1)) := by
            rw [hInt]; field_simp [ne_of_gt hs]
      _ ≤ s.re * (k : ℝ) ^ (-s.re - 1) := mul_le_mul_of_nonneg_left hbnd hpos
  have hb := norm_cpow_sub_le k hk s hs
  calc
    ‖((k : ℂ) ^ (-s)) - (((k + 1 : ℕ) : ℂ) ^ (-s))‖
        ≤ (‖s‖ / s.re) * (((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) := hb
    _ ≤ (‖s‖ / s.re) * (s.re * (k : ℝ) ^ (-s.re - 1)) :=
          mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ = ‖s‖ * (k : ℝ) ^ (-s.re - 1) := by field_simp [ne_of_gt hs]

/-- Each `etaTerm` is a differentiable function of `s`. -/
private lemma etaTerm_differentiableOn (k : ℕ) {U : Set ℂ} :
    DifferentiableOn ℂ (fun s : ℂ => etaTerm s k) U := by
  have hbase1 : (((k + 1 : ℕ)) : ℂ) ≠ 0 := by exact_mod_cast (by omega : (k + 1 : ℕ) ≠ 0)
  have hbase2 : (((k + 1 + 1 : ℕ)) : ℂ) ≠ 0 := by exact_mod_cast (by omega : (k + 1 + 1 : ℕ) ≠ 0)
  refine DifferentiableOn.mul ?_ ?_
  · intro z hz; exact (differentiableAt_const _).differentiableWithinAt
  · refine DifferentiableOn.sub ?_ ?_
    · intro z hz
      exact (DifferentiableAt.const_cpow differentiableAt_id.neg (Or.inl hbase1)).differentiableWithinAt
    · intro z hz
      exact (DifferentiableAt.const_cpow differentiableAt_id.neg (Or.inl hbase2)).differentiableWithinAt

/-- Pointwise bound of the eta terms on a small ball (uniform in `s`). -/
private lemma etaTerm_bound_on_ball (z0 : ℂ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ2 : 2 * ρ ≤ z0.re)
    {z : ℂ} (hz : z ∈ Metric.ball z0 ρ) (k : ℕ) :
    ‖etaTerm z k‖ ≤ (‖z0‖ + ρ) * (((k + 1 : ℕ) : ℝ) ^ (-ρ - 1)) := by
  have hdz : ‖z - z0‖ < ρ := by simpa [dist_eq_norm] using Metric.mem_ball.mp hz
  have hzre : ρ ≤ z.re := by
    have hre : -‖z - z0‖ ≤ (z - z0).re := (abs_le.mp (abs_re_le_norm (z - z0))).1
    have h3 : (z - z0).re = z.re - z0.re := by simp
    rw [h3] at hre
    have hlow : z0.re - ‖z - z0‖ ≤ z.re := by linarith
    calc
      ρ ≤ z0.re - ρ := by linarith
      _ ≤ z0.re - ‖z - z0‖ := by linarith
      _ ≤ z.re := hlow
  have hznorm : ‖z‖ ≤ ‖z0‖ + ρ := by
    calc
      ‖z‖ = ‖z0 + (z - z0)‖ := congrArg norm (by ring)
      _ ≤ ‖z0‖ + ‖z - z0‖ := norm_add_le _ _
      _ ≤ ‖z0‖ + ρ := by linarith
  have hzpos : 0 < z.re := lt_of_lt_of_le hρ0 hzre
  have hk1 : 1 ≤ k + 1 := by omega
  have hkbase : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hk1
  have hpowle : (((k + 1 : ℕ) : ℝ)) ^ (-z.re - 1) ≤ (((k + 1 : ℕ) : ℝ)) ^ (-ρ - 1) :=
    Real.rpow_le_rpow_of_exponent_le hkbase (by linarith)
  have hb := norm_cpow_sub_le_pow (k + 1) hk1 z hzpos
  calc
    ‖etaTerm z k‖
        = ‖altR (k + 1)‖
            * ‖(((k + 1 : ℕ) : ℂ) ^ (-z)) - (((k + 1 + 1 : ℕ) : ℂ) ^ (-z))‖ := by
          rw [etaTerm, norm_mul]
    _ ≤ 1 * ‖(((k + 1 : ℕ) : ℂ) ^ (-z)) - (((k + 1 + 1 : ℕ) : ℂ) ^ (-z))‖ :=
          mul_le_mul_of_nonneg_right (altR_norm_le _) (norm_nonneg _)
    _ ≤ ‖z‖ * (((k + 1 : ℕ) : ℝ) ^ (-z.re - 1)) := by rw [one_mul]; exact hb
    _ ≤ (‖z0‖ + ρ) * (((k + 1 : ℕ) : ℝ) ^ (-z.re - 1)) :=
          mul_le_mul_of_nonneg_right hznorm (by positivity)
    _ ≤ (‖z0‖ + ρ) * (((k + 1 : ℕ) : ℝ) ^ (-ρ - 1)) :=
          mul_le_mul_of_nonneg_left hpowle (by positivity)

/-- `abelEta` is differentiable on a ball around any point with positive real part. -/
private lemma abelEta_differentiableOn_ball (z0 : ℂ) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ2 : 2 * ρ ≤ z0.re) : DifferentiableOn ℂ abelEta (Metric.ball z0 ρ) := by
  let u : ℕ → ℝ := fun k => (‖z0‖ + ρ) * (((k + 1 : ℕ) : ℝ) ^ (-ρ - 1))
  have hu : Summable u := by
    have hp : -ρ - 1 < -1 := by linarith
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-ρ - 1)) := (Real.summable_nat_rpow).mpr hp
    have hshift : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-ρ - 1)) :=
      (summable_nat_add_iff 1).2 hbase
    exact hshift.mul_left (‖z0‖ + ρ)
  refine differentiableOn_tsum_of_summable_norm hu (fun k => etaTerm_differentiableOn k)
    Metric.isOpen_ball (fun k w hw => etaTerm_bound_on_ball z0 hρ0 hρ2 hw k)

/-- `abelEta` is differentiable on the right half-plane. -/
private lemma abelEta_differentiableOn_re_pos :
    DifferentiableOn ℂ abelEta {z : ℂ | 0 < z.re} := by
  intro z0 hz0
  let ρ : ℝ := z0.re / 2
  have hρ0 : 0 < ρ := by dsimp [ρ]; exact div_pos hz0 (by norm_num)
  have hρ2 : 2 * ρ ≤ z0.re := by dsimp [ρ]; field_simp; exact le_rfl
  have hb := abelEta_differentiableOn_ball z0 (ρ := ρ) hρ0 hρ2
  have hdz : DifferentiableAt ℂ abelEta z0 :=
    hb.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ0))
  exact hdz.differentiableWithinAt

/-- `abelEta` is holomorphic on the right half-plane. -/
lemma abelEta_analyticOn_re_pos : AnalyticOnNhd ℂ abelEta {z : ℂ | 0 < z.re} :=
  abelEta_differentiableOn_re_pos.analyticOnNhd (isOpen_lt continuous_const continuous_re)

/-! ## Abel summation and the alternating series -/

/-- Reindexing `∑_{k=1}^{X} g k = ∑_{j<X} g (j+1)`. -/
private lemma sum_Icc_one_eq_sum_range (X : ℕ) (g : ℕ → ℂ) :
    (∑ k ∈ Finset.Icc 1 X, g k) = ∑ j ∈ Finset.range X, g (j + 1) := by
  induction X with
  | zero => simp
  | succ X ih =>
      rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega : 1 ≤ X + 1), ih]

/-- Abel summation: the partial sums of the Abel series differ from those of the alternating
Dirichlet series by a boundary term. -/
lemma etaTerm_head_eq (s : ℂ) (X : ℕ) :
    (∑ n ∈ Finset.range X, etaTerm s n) + altR X * (((X + 1 : ℕ)) : ℂ) ^ (-s)
      = ∑ k ∈ Finset.Icc 1 X, (-1 : ℂ) ^ (k - 1) * ((k : ℕ) : ℂ) ^ (-s) := by
  induction X with
  | zero => simp [altR_zero]
  | succ X ih =>
      rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega : 1 ≤ X + 1), ← ih]
      simp only [etaTerm, altR_succ, Nat.add_sub_cancel]
      ring

/-- `((X+1)^{-β})` tends to `0` for `β > 0`. -/
private lemma tendsto_natCast_succ_rpow_neg (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun X : ℕ => (((X + 1 : ℕ)) : ℝ) ^ (-β)) atTop (𝓝 0) := by
  have hto : Tendsto (fun X : ℕ => (((X + 1 : ℕ)) : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono (f := fun N : ℕ => (N : ℝ))
      (g := fun N : ℕ => ((N + 1 : ℕ) : ℝ)) (fun N => by exact_mod_cast (by omega : N ≤ N + 1))
      tendsto_natCast_atTop_atTop
  have hdec : Tendsto (fun t : ℝ => t ^ (-β)) atTop (𝓝 0) := by
    have hmain : Tendsto (fun t : ℝ => (t ^ β)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop hβ)
    refine hmain.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [Real.rpow_neg (by linarith : 0 ≤ t) β]
  exact hdec.comp hto

/-- The boundary term of Abel summation tends to `0` for `re s > 1`. -/
private lemma tendsto_altR_mul_cpow (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun X : ℕ => altR X * (((X + 1 : ℕ)) : ℂ) ^ (-s)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun X => norm_nonneg _) (fun X => ?_)
    (tendsto_natCast_succ_rpow_neg s.re (by linarith))
  rw [norm_mul]
  have hbase : ((((X + 1 : ℕ)) : ℝ) : ℂ) = (((X + 1 : ℕ)) : ℂ) := by norm_num
  have h : ‖((((X + 1 : ℕ)) : ℂ)) ^ (-s)‖ = (((X + 1 : ℕ)) : ℝ) ^ (-s.re) := by
    rw [← hbase, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0:ℝ) < _), Complex.neg_re]
  rw [h]
  calc ‖altR X‖ * (((X + 1 : ℕ)) : ℝ) ^ (-s.re)
      ≤ 1 * (((X + 1 : ℕ)) : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (altR_norm_le X) (by positivity)
    _ = (((X + 1 : ℕ)) : ℝ) ^ (-s.re) := one_mul _

/-- Norm of the `ζ`-summand. -/
private lemma norm_cpow_zetaTerm (s : ℂ) (n : ℕ) :
    ‖((((n + 1 : ℕ)) : ℂ)) ^ (-s)‖ = (((n + 1 : ℕ)) : ℝ) ^ (-s.re) := by
  have hb : ((((n + 1 : ℕ)) : ℝ) : ℂ) = (((n + 1 : ℕ)) : ℂ) := by norm_num
  rw [← hb, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0:ℝ) < ((n+1:ℕ):ℝ)),
    Complex.neg_re]

/-- The `ζ`-summand is summable for `re s > 1`. -/
private lemma summable_zetaTerm (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : ℕ => (((n + 1 : ℕ)) : ℂ) ^ (-s)) := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => (((n + 1 : ℕ)) : ℝ) ^ (-s.re)) ?_ ?_
  · exact (summable_nat_add_iff 1).2 ((Real.summable_nat_rpow).mpr (by linarith))
  · intro n; rw [norm_cpow_zetaTerm]

/-- The alternating summand is summable for `re s > 1`. -/
private lemma summable_altTerm (s : ℂ) (hs : 1 < s.re) :
    Summable (fun k : ℕ => (-1 : ℂ) ^ k * (((k + 1 : ℕ)) : ℂ) ^ (-s)) := by
  refine Summable.of_norm_bounded (g := fun k : ℕ => (((k + 1 : ℕ)) : ℝ) ^ (-s.re)) ?_ ?_
  · exact (summable_nat_add_iff 1).2 ((Real.summable_nat_rpow).mpr (by linarith))
  · intro k
    rw [norm_mul, norm_cpow_zetaTerm, show ‖(-1 : ℂ) ^ k‖ = 1 from by simp, one_mul]

private lemma injective_two_mul : Function.Injective (fun k : ℕ => 2 * k) := by
  intro a b h
  dsimp only at h
  omega

private lemma injective_two_mul_add_one : Function.Injective (fun k : ℕ => 2 * k + 1) := by
  intro a b h
  dsimp only at h
  omega

/-- For `re s > 1` the Abel-regularised eta series equals the alternating Dirichlet series. -/
lemma abelEta_eq_altSeries (s : ℂ) (hs : 1 < s.re) :
    abelEta s = ∑' k : ℕ, (-1 : ℂ) ^ k * (((k + 1 : ℕ)) : ℂ) ^ (-s) := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hsum := etaTerm_summable s hs0
  have hL : Tendsto (fun X : ℕ => ∑ n ∈ Finset.range X, etaTerm s n) atTop (𝓝 (abelEta s)) := by
    simpa [abelEta] using hsum.hasSum.tendsto_sum_nat
  have hsumAlt := summable_altTerm s hs
  have hlimAlt : Tendsto (fun X : ℕ => ∑ k ∈ Finset.Icc 1 X,
      (-1 : ℂ) ^ (k - 1) * ((k : ℕ) : ℂ) ^ (-s)) atTop
      (𝓝 (∑' k : ℕ, (-1 : ℂ) ^ k * (((k + 1 : ℕ)) : ℂ) ^ (-s))) := by
    refine hsumAlt.hasSum.tendsto_sum_nat.congr' (Eventually.of_forall (fun X => ?_))
    dsimp only
    rw [sum_Icc_one_eq_sum_range X (fun k => (-1 : ℂ) ^ (k - 1) * ((k : ℕ) : ℂ) ^ (-s))]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show (j + 1 - 1 : ℕ) = j from Nat.add_sub_cancel j 1]
  have hlimB := tendsto_altR_mul_cpow s hs
  have hkey : abelEta s = (∑' k : ℕ, (-1 : ℂ) ^ k * (((k + 1 : ℕ)) : ℂ) ^ (-s)) - 0 := by
    refine tendsto_nhds_unique hL ?_
    refine (hlimAlt.sub hlimB).congr' (Eventually.of_forall (fun X => ?_))
    have h := etaTerm_head_eq s X
    rw [← h]
    ring
  simpa using hkey

/-! ## The alternating series equals `(1 - 2^{1-s}) ζ(s)` -/

/-- The Dirichlet eta function equals `(1 - 2^{1-s}) ζ(s)` in the half-plane `re s > 1`. -/
lemma altSeries_zeta_aux (s : ℂ) (hs : 1 < s.re) :
    (∑' k : ℕ, (-1 : ℂ) ^ k * (((k + 1 : ℕ)) : ℂ) ^ (-s))
      = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  set p : ℕ → ℂ := fun n => (((n + 1 : ℕ)) : ℂ) ^ (-s) with hpdef
  set f : ℕ → ℂ := fun k => (-1 : ℂ) ^ k * (((k + 1 : ℕ)) : ℂ) ^ (-s) with hfdef
  have hsp : Summable p := by rw [hpdef]; exact summable_zetaTerm s hs
  have hsf : Summable f := by rw [hfdef]; exact summable_altTerm s hs
  have hf0' : Summable (fun k : ℕ => f (2 * k)) :=
    hsf.comp_injective injective_two_mul
  have hf1' : Summable (fun k : ℕ => f (2 * k + 1)) :=
    hsf.comp_injective injective_two_mul_add_one
  have hp0 : Summable (fun k : ℕ => p (2 * k)) :=
    hsp.comp_injective injective_two_mul
  have hp1 : Summable (fun k : ℕ => p (2 * k + 1)) :=
    hsp.comp_injective injective_two_mul_add_one
  have ep := tsum_even_add_odd hp0 hp1
  have ef := tsum_even_add_odd hf0' hf1'
  have hf_even : (∑' k : ℕ, f (2 * k)) = ∑' k : ℕ, p (2 * k) := by
    apply tsum_congr; intro k
    rw [hfdef, hpdef]; simp only []
    rw [show (-1 : ℂ) ^ (2 * k) = 1 from Even.neg_one_pow ⟨k, by ring⟩, one_mul]
  have hf_odd : (∑' k : ℕ, f (2 * k + 1)) = - ∑' k : ℕ, p (2 * k + 1) := by
    rw [← tsum_neg]
    apply tsum_congr; intro k
    rw [hfdef, hpdef]; simp only []
    rw [show (-1 : ℂ) ^ (2 * k + 1) = -1 from Odd.neg_one_pow ⟨k, by ring⟩]
    ring
  have hp_odd : (∑' k : ℕ, p (2 * k + 1)) = (2 : ℂ) ^ (-s) * ∑' k : ℕ, p k := by
    rw [← tsum_mul_left]
    apply tsum_congr; intro k
    rw [hpdef]; simp only []
    have hcast : (((2 * k + 2 : ℕ)) : ℂ) = (((2 : ℝ)) : ℂ) * ((((k + 1 : ℕ)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
    simp only [Complex.ofReal_ofNat, Complex.ofReal_natCast]
  have hsum_p : (∑' k : ℕ, p k) = riemannZeta s := by
    rw [hpdef]; simp only []
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    apply tsum_congr; intro k
    have hb : (((k + 1 : ℕ)) : ℂ) = ((k : ℂ) + 1) := by push_cast; ring
    rw [hb, cpow_neg, inv_eq_one_div]
  have h2 : (2 : ℂ) * (2 : ℂ) ^ (-s) = (2 : ℂ) ^ (1 - s) := by
    have h := cpow_add (1 : ℂ) (-s) (x := (2 : ℂ)) (by norm_num)
    rw [show (1 : ℂ) + (-s) = 1 - s from by ring, cpow_one] at h
    exact h.symm
  rw [ef.symm, hf_even, hf_odd, ← sub_eq_add_neg,
    show (∑' k : ℕ, p (2 * k)) = (∑' k : ℕ, p k) - (∑' k : ℕ, p (2 * k + 1)) from
      eq_sub_iff_add_eq.mpr ep, hp_odd, hsum_p]
  linear_combination (-(riemannZeta s)) * h2

/-! ## Analytic continuation to `{re s > 0} \ {1}` -/

/-- Both sides agree on `{re s > 1}`. -/
private lemma abelEta_eq_zeta_of_one_lt (s : ℂ) (hs : 1 < s.re) :
    abelEta s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  rw [abelEta_eq_altSeries s hs, altSeries_zeta_aux s hs]

/-- The analytic-continuation identity on `{re s > 0} \ {1}`. -/
lemma abelEta_eq_zeta (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    abelEta s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  let U : Set ℂ := {z : ℂ | 0 < z.re ∧ z ≠ 1}
  have hpc : IsPreconnected U :=
    Commons.NumberTheory.Zeta.isPreconnected_re_gt_sdiff (θ := 0) (by norm_num)
  have hUopen : IsOpen U := by
    have h1 : IsOpen ({z : ℂ | 0 < z.re} \ {1}) :=
      (isOpen_lt continuous_const continuous_re).sdiff isClosed_singleton
    convert h1 using 1
    ext z; simp [U, Set.mem_sdiff, Set.mem_singleton_iff]
  have hf : AnalyticOnNhd ℂ abelEta U :=
    abelEta_analyticOn_re_pos.mono (fun _ hz => hz.1)
  have hg : AnalyticOnNhd ℂ (fun z => (1 - (2 : ℂ) ^ (1 - z)) * riemannZeta z) U := by
    refine (DifferentiableOn.analyticOnNhd ?_ hUopen)
    intro z hz
    have hz1 : z ≠ 1 := hz.2
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.mul ?_ (differentiableAt_riemannZeta hz1)
    refine DifferentiableAt.sub (differentiableAt_const (1 : ℂ)) ?_
    exact ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).const_cpow
      (Or.inl (by norm_num))
  have h2U : (2 : ℂ) ∈ U := ⟨by norm_num, by norm_num⟩
  have hev : abelEta =ᶠ[𝓝 (2 : ℂ)]
      (fun z => (1 - (2 : ℂ) ^ (1 - z)) * riemannZeta z) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact abelEta_eq_zeta_of_one_lt z hz
  have hEqOn := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hf hg hpc h2U hev
  exact hEqOn ⟨hs, hs1⟩

/-! ## Positivity of `abelEta` at positive real arguments -/

private lemma altR_re_nonneg (n : ℕ) : 0 ≤ (altR n).re := by
  rcases Nat.even_or_odd n with h | h <;> rw [altR, h.neg_one_pow] <;> norm_num

private lemma altR_re_le_one (n : ℕ) : (altR n).re ≤ 1 := by
  rcases Nat.even_or_odd n with h | h <;> rw [altR, h.neg_one_pow] <;> norm_num

private lemma altR_eq_re (n : ℕ) : altR n = ((altR n).re : ℂ) := by
  rcases Nat.even_or_odd n with h | h <;> rw [altR, h.neg_one_pow] <;> norm_num

/-- The Abel terms at a real argument are nonnegative reals. -/
private lemma etaTerm_ofReal (t : ℝ) (n : ℕ) :
    etaTerm (t : ℂ) n
      = (((altR (n + 1)).re
          * ((((n + 1 : ℕ)) : ℝ) ^ (-t) - (((n + 1 + 1 : ℕ)) : ℝ) ^ (-t)) : ℝ) : ℂ) := by
  have h1 : (((n + 1 : ℕ)) : ℂ) ^ (-(t : ℂ))
      = (((((n + 1 : ℕ)) : ℝ) ^ (-t) : ℝ) : ℂ) := by
    rw [show (-(t : ℂ)) = ((-t : ℝ) : ℂ) from by simp]
    rw [← Complex.ofReal_natCast (n + 1),
      Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ ((n + 1 : ℕ) : ℝ)) (-t)]
  have h2 : (((n + 1 + 1 : ℕ)) : ℂ) ^ (-(t : ℂ))
      = (((((n + 1 + 1 : ℕ)) : ℝ) ^ (-t) : ℝ) : ℂ) := by
    rw [show (-(t : ℂ)) = ((-t : ℝ) : ℂ) from by simp]
    rw [← Complex.ofReal_natCast (n + 1 + 1),
      Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ ((n + 1 + 1 : ℕ) : ℝ)) (-t)]
  rw [etaTerm, altR_eq_re (n + 1), h1, h2, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_re]

/-- The Abel-regularised eta function is a positive real at a positive real argument. -/
private lemma abelEta_ofReal_pos (t : ℝ) (ht : 0 < t) :
    ∃ x : ℝ, 0 < x ∧ abelEta (t : ℂ) = (x : ℂ) := by
  set F : ℕ → ℝ := fun n =>
    (altR (n + 1)).re * ((((n + 1 : ℕ)) : ℝ) ^ (-t) - (((n + 1 + 1 : ℕ)) : ℝ) ^ (-t)) with hF
  have hterm : ∀ n, etaTerm (t : ℂ) n = (F n : ℂ) := by
    intro n
    rw [hF]; exact etaTerm_ofReal t n
  have hFnn : ∀ n, 0 ≤ F n := by
    intro n
    rw [hF]
    refine mul_nonneg (altR_re_nonneg _) ?_
    have h1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have h2 : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have := Real.rpow_le_rpow_of_nonpos h1 h2 (by linarith : -t ≤ 0)
    linarith
  have hF0 : 0 < F 0 := by
    rw [hF]
    dsimp only
    have h1 : (altR (0 + 1)).re = 1 := by
      rw [show (0 + 1 : ℕ) = 1 from rfl, altR_one]; norm_num
    rw [h1, one_mul, show (((0 + 1 : ℕ)) : ℝ) = 1 from by norm_num,
      show (((0 + 1 + 1 : ℕ)) : ℝ) = 2 from by norm_num, Real.one_rpow]
    have h2t : 1 < (2 : ℝ) ^ t := Real.one_lt_rpow (by norm_num) ht
    have h2 : (2 : ℝ) ^ (-t) < 1 := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      exact inv_lt_one_of_one_lt₀ h2t
    linarith
  have hFtelesc : Summable (fun n : ℕ => (((n + 1 : ℕ)) : ℝ) ^ (-t)
      - (((n + 1 + 1 : ℕ)) : ℝ) ^ (-t)) := by
    have h := (hasSum_telescope_rpow 1 (by norm_num) ht).summable
    have hfun : (fun m : ℕ => (((1 + m : ℕ)) : ℝ) ^ (-t) - (((1 + m + 1 : ℕ)) : ℝ) ^ (-t))
        = (fun n : ℕ => (((n + 1 : ℕ)) : ℝ) ^ (-t) - (((n + 1 + 1 : ℕ)) : ℝ) ^ (-t)) := by
      funext n
      rw [Nat.add_comm 1 n]
    rwa [hfun] at h
  have hFsum : Summable F := by
    refine Summable.of_nonneg_of_le hFnn (fun n => ?_) hFtelesc
    rw [hF]
    have hdiff : 0 ≤ (((n + 1 : ℕ)) : ℝ) ^ (-t) - (((n + 1 + 1 : ℕ)) : ℝ) ^ (-t) := by
      have h1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have h2 : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : n + 1 ≤ n + 1 + 1)
      have := Real.rpow_le_rpow_of_nonpos h1 h2 (by linarith : -t ≤ 0)
      linarith
    calc (altR (n + 1)).re * ((((n + 1 : ℕ)) : ℝ) ^ (-t) - (((n + 1 + 1 : ℕ)) : ℝ) ^ (-t))
        ≤ 1 * ((((n + 1 : ℕ)) : ℝ) ^ (-t) - (((n + 1 + 1 : ℕ)) : ℝ) ^ (-t)) :=
          mul_le_mul_of_nonneg_right (altR_re_le_one _) hdiff
      _ = _ := one_mul _
  refine ⟨∑' n, F n, ?_, ?_⟩
  · exact lt_of_lt_of_le hF0 (hFsum.le_tsum 0 (fun j _ => hFnn j))
  · rw [abelEta]
    rw [Complex.ofReal_tsum F]
    exact tsum_congr (fun n => hterm n)

/-- **`ζ(t) < 0` for real `0 < t < 1`.** -/
theorem zeta_neg_of_mem_Ioo (t : ℝ) (h0 : 0 < t) (h1 : t < 1) :
    (riemannZeta (t : ℂ)).re < 0 ∧ (riemannZeta (t : ℂ)).im = 0 := by
  have htz : (t : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  obtain ⟨x, hxpos, hxeq⟩ := abelEta_ofReal_pos t h0
  have hkey := abelEta_eq_zeta (t : ℂ) (by simpa using h0) htz
  have hy : (1 : ℂ) - (2 : ℂ) ^ (1 - (t : ℂ))
      = ((1 - (2 : ℝ) ^ (1 - t) : ℝ) : ℂ) := by
    have h1t : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by simp
    rw [h1t, ← Complex.ofReal_ofNat 2,
      ← Complex.ofReal_cpow (by norm_num : (0:ℝ) ≤ 2)]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
  have hyneg : (1 : ℝ) - (2 : ℝ) ^ (1 - t) < 0 := by
    have : 1 < (2 : ℝ) ^ (1 - t) := Real.one_lt_rpow (by norm_num) (by linarith)
    linarith
  have hyne : ((1 - (2 : ℝ) ^ (1 - t) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hζ : riemannZeta (t : ℂ) = (((x / (1 - (2 : ℝ) ^ (1 - t))) : ℝ) : ℂ) := by
    have hmul : (((1 - (2 : ℝ) ^ (1 - t) : ℝ)) : ℂ) * riemannZeta (t : ℂ)
        = ((x : ℝ) : ℂ) := by
      rw [← hy, ← hxeq]
      exact hkey.symm
    have h2 := congrArg (fun z : ℂ => z / (((1 - (2 : ℝ) ^ (1 - t) : ℝ)) : ℂ)) hmul
    rw [mul_div_cancel_left₀ _ hyne, ← Complex.ofReal_div] at h2
    exact h2
  constructor
  · rw [hζ, Complex.ofReal_re]
    exact div_neg_of_pos_of_neg hxpos hyneg
  · rw [hζ, Complex.ofReal_im]

end

end Work.RHContract.B
