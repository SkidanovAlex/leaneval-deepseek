import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeries

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex Filter Set intervalIntegral MeasureTheory
open scoped Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.Zeta

private lemma re_neg_sub_one (s : ℂ) : (-s - 1).re = -s.re - 1 := by
  simp [Complex.neg_re, Complex.sub_re, Complex.one_re]

private lemma norm_cpow_of_real_neg_sub_one (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-s.re - 1) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx (-s - 1)]
  rw [re_neg_sub_one]

private lemma norm_cpow_of_real_neg (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (-s)‖ = x ^ (-s.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx (-s)]
  rw [Complex.neg_re]

private lemma integral_norm_cpow_sub_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (s : ℂ)
    (hs : 0 < s.re) :
    (∫ x : ℝ in a..b, ‖(x : ℂ) ^ (-s - 1)‖) = (a ^ (-s.re) - b ^ (-s.re)) / s.re := by
  have hnot0 : (0 : ℝ) ∉ Set.uIcc a b := by
    intro hx
    have hx' : (0 : ℝ) ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using hx
    linarith [hx'.1, ha]
  have hne : -s.re - 1 ≠ (-1 : ℝ) := by linarith
  calc
    (∫ x : ℝ in a..b, ‖(x : ℂ) ^ (-s - 1)‖)
        = ∫ x : ℝ in a..b, x ^ (-s.re - 1) := by
            apply intervalIntegral.integral_congr
            intro x hx
            have hx' : x ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using hx
            have hx0 : 0 < x := lt_of_lt_of_le ha hx'.1
            exact norm_cpow_of_real_neg_sub_one s hx0
    _ = (b ^ (-s.re) - a ^ (-s.re)) / (-s.re) := by
      have hint := integral_rpow (r := -s.re - 1) (a := a) (b := b) (Or.inr ⟨hne, hnot0⟩)
      rw [hint]
      have hD : -s.re - 1 + 1 = -s.re := by ring
      rw [hD]
    _ = (a ^ (-s.re) - b ^ (-s.re)) / s.re := by
      field_simp [ne_of_gt hs]
      ring

private lemma cpow_sub_eq_smul_integral_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (s : ℂ)
    (hs : 0 < s.re) :
    (a : ℂ) ^ (-s) - (b : ℂ) ^ (-s) = s * (∫ x : ℝ in a..b, (x : ℂ) ^ (-s - 1)) := by
  have hnot0 : (0 : ℝ) ∉ Set.uIcc a b := by
    intro hx
    have hx' : (0 : ℝ) ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using hx
    linarith [hx'.1, ha]
  have hne : -s - 1 ≠ (-1 : ℂ) := by
    intro h
    apply ne_of_gt hs
    have hre := congrArg Complex.re h
    simpa using hre
  have hint := integral_cpow (r := -s - 1) (a := a) (b := b) (Or.inr ⟨hne, hnot0⟩)
  have hD : -s - 1 + 1 = -s := by ring
  have hinteq : (∫ x : ℝ in a..b, (x : ℂ) ^ (-s - 1)) = ((b : ℂ) ^ (-s) - (a : ℂ) ^ (-s)) / (-s) := by
    rw [hint]
    rw [hD]
  have hsnz : s ≠ 0 := by
    intro h
    exact (ne_of_gt hs) (by simpa [h] : s.re = 0)
  have hneg_ne : -s ≠ 0 := by
    intro h
    apply hsnz
    exact neg_eq_zero.mp h
  calc
    (a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)
        = s * (((b : ℂ) ^ (-s) - (a : ℂ) ^ (-s)) / (-s)) := by
            field_simp [hneg_ne]
            ring
    _ = s * (∫ x : ℝ in a..b, (x : ℂ) ^ (-s - 1)) := by
            rw [← hinteq]

private lemma norm_cpow_sub_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (s : ℂ)
    (hs : 0 < s.re) :
    ‖(b : ℂ) ^ (-s) - (a : ℂ) ^ (-s)‖ ≤
      (‖s‖ / s.re) * (a ^ (-s.re) - b ^ (-s.re)) := by
  have hsub := cpow_sub_eq_smul_integral_of_le ha hab s hs
  calc
    ‖(b : ℂ) ^ (-s) - (a : ℂ) ^ (-s)‖
        = ‖(a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)‖ := by
            rw [← neg_sub]
            rw [norm_neg]
    _ = ‖s * (∫ x : ℝ in a..b, (x : ℂ) ^ (-s - 1))‖ := by rw [hsub]
    _ ≤ ‖s‖ * ‖(∫ x : ℝ in a..b, (x : ℂ) ^ (-s - 1))‖ := norm_mul_le _ _
    _ ≤ ‖s‖ * (∫ x : ℝ in a..b, ‖(x : ℂ) ^ (-s - 1)‖) := by
      exact mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm hab) (norm_nonneg s)
    _ = (‖s‖ / s.re) * (a ^ (-s.re) - b ^ (-s.re)) := by
      rw [integral_norm_cpow_sub_of_le ha hab s hs]
      field_simp [ne_of_gt hs]

def emTerm (k : ℕ) (s : ℂ) : ℂ :=
  (((k + 1 : ℕ) : ℂ) ^ (-s)) - (((((k + 1 : ℕ) : ℂ) ^ (1 - s)) - ((k : ℂ) ^ (1 - s))) / (1 - s))

/-- `x ↦ x^{-s}` is continuous on `(0, ∞)`. -/
private lemma continuousOn_cpow_neg (s : ℂ) (hs : s ≠ 0) :
    ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Set.Ioi (0 : ℝ)) := by
  intro x hx
  have hder : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) ((-s) * (x : ℂ) ^ (-s - 1)) x := by
    exact hasDerivAt_ofReal_cpow_const (ne_of_gt hx) (by
      intro h
      exact hs (neg_eq_zero.mp h))
  exact hder.continuousAt.continuousWithinAt

/-- `x ↦ x^q` is continuous on `(0,∞)`. -/
private lemma continuousOn_rpow_of_pos (q : ℝ) :
    ContinuousOn (fun x : ℝ => x ^ q) (Set.Ioi (0 : ℝ)) := by
  intro x hx
  exact (Real.continuousAt_rpow_const x q (Or.inl (ne_of_gt hx))).continuousWithinAt

/-- interval integrability of the cpow integrand on `[k,k+1]` for `k ≥ 1`. -/
private lemma intervalIntegrable_cpow_neg (k : ℕ) (hk1 : 1 ≤ k) (s : ℂ) (hs : s ≠ 0) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  refine ContinuousOn.intervalIntegrable_of_Icc hkle ?_
  have hmono : Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ) ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact lt_of_lt_of_le hkpos hx.1
  exact (continuousOn_cpow_neg s hs).mono hmono

private lemma emTerm_eq_sub_integral (k : ℕ) (hk1 : 1 ≤ k) (s : ℂ) (hs1 : s ≠ 1) :
    emTerm k s = ((k + 1 : ℂ) ^ (-s)) -
      (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x : ℂ) ^ (-s)) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hnot0 : (0 : ℝ) ∉ Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    intro hx
    have hx' : (0 : ℝ) ∈ Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
      simpa [Set.uIcc_of_le hkle] using hx
    linarith [hx'.1, hkpos]
  have hne : -s ≠ (-1 : ℂ) := by
    intro h
    exact hs1 (neg_injective h)
  have hint := integral_cpow (r := -s) (a := (k : ℝ)) (b := ((k + 1 : ℕ) : ℝ)) (Or.inr ⟨hne, hnot0⟩)
  have hD : -s + 1 = 1 - s := by ring
  have hinteq : (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x : ℂ) ^ (-s))
      = (((k + 1 : ℕ) : ℂ) ^ (1 - s) - (k : ℂ) ^ (1 - s)) / (1 - s) := by
    rw [hint]
    rw [hD]
    norm_num
  unfold emTerm
  rw [hinteq]
  simp

private lemma norm_emTerm_le (k : ℕ) (hk1 : 1 ≤ k) (s : ℂ) (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    ‖emTerm k s‖ ≤ (‖s‖ / s.re) * (((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) := by
  have hsne : s ≠ 0 := by
    intro h
    exact (ne_of_gt hs0) (by simpa [h] : s.re = 0)
  have heq := emTerm_eq_sub_integral k hk1 s hs1
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  let c : ℂ := (k + 1 : ℂ) ^ (-s)
  let f : ℝ → ℂ := fun x : ℝ => (x : ℂ) ^ (-s)
  have hc_int : IntervalIntegrable (fun _ : ℝ => c) volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    exact intervalIntegrable_const
  have hf_int : IntervalIntegrable f volume (k : ℝ) ((k + 1 : ℕ) : ℝ) :=
    intervalIntegrable_cpow_neg k hk1 s hsne
  have hsub_int : IntervalIntegrable (fun x : ℝ => c - f x) volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
    simpa [f] using hc_int.sub hf_int
  have hconst : (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), c) = c := by
    rw [intervalIntegral.integral_const]
    norm_num
  have hpull : (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (c - f x)) = c - ∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), f x := by
    rw [intervalIntegral.integral_sub hc_int hf_int]
    rw [hconst]
  have hdiff_nonneg : 0 ≤ (k : ℝ) ^ (-s.re) - (((k + 1 : ℕ) : ℝ) ^ (-s.re)) := by
    have hdec : (((k + 1 : ℕ) : ℝ) ^ (-s.re)) ≤ (k : ℝ) ^ (-s.re) := by
      exact Real.rpow_le_rpow_of_nonpos hkpos hkle (by linarith : -s.re ≤ 0)
    linarith
  calc
    ‖emTerm k s‖ = ‖c - ∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), f x‖ := by
      unfold c f
      rw [heq]
    _ = ‖∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (c - f x)‖ := by rw [hpull]
    _ ≤ ∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), ‖c - f x‖ :=
      intervalIntegral.norm_integral_le_integral_norm hkle
    _ ≤ ∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (‖s‖ / s.re) * (x ^ (-s.re) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) := by
      apply intervalIntegral.integral_mono_on hkle
      · exact IntervalIntegrable.norm hsub_int
      · have hcont : ContinuousOn (fun x : ℝ => (‖s‖ / s.re) * (x ^ (-s.re) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))))
            (Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ)) := by
          have hsub : Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ) ⊆ Set.Ioi (0 : ℝ) := by
            intro x hx
            exact lt_of_lt_of_le hkpos hx.1
          have hcont0 : ContinuousOn (fun x : ℝ => (x ^ (-s.re) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))))
              (Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ)) := by
            refine (ContinuousOn.sub (continuousOn_rpow_of_pos (-s.re)) continuousOn_const).mono hsub
          exact (continuousOn_const.mul hcont0)
        exact ContinuousOn.intervalIntegrable_of_Icc hkle hcont
      · intro x hx
        have hx' : x ∈ Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by simpa [Set.uIcc_of_le hkle] using hx
        have hx0 : 0 < x := lt_of_lt_of_le hkpos hx'.1
        have hb := norm_cpow_sub_of_le (a := x) (b := ((k + 1 : ℕ) : ℝ)) hx0 hx'.2 s hs0
        unfold c f
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, norm_neg] using hb
    _ = (‖s‖ / s.re) * (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x ^ (-s.re) - (((k + 1 : ℕ) : ℝ) ^ (-s.re)))) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (‖s‖ / s.re) * (((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) := by
      have hg : (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x ^ (-s.re) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))))
          ≤ ((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re)) := by
        have hbnd : (k : ℝ) ^ (-s.re) - (((k + 1 : ℕ) : ℝ) ^ (-s.re)) = (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), ((k : ℝ) ^ (-s.re) - (((k + 1 : ℕ) : ℝ) ^ (-s.re)))) := by
          rw [intervalIntegral.integral_const]
          have hlen : (((k + 1 : ℕ) : ℝ) - (k : ℝ)) = 1 := by norm_num
          simp [hlen]
        rw [hbnd]
        apply intervalIntegral.integral_mono_on hkle
        · have hcont : ContinuousOn (fun x : ℝ => (x ^ (-s.re) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))))
              (Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ)) := by
            have hsub : Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ) ⊆ Set.Ioi (0 : ℝ) := by
              intro x hx
              exact lt_of_lt_of_le hkpos hx.1
            refine (ContinuousOn.sub (continuousOn_rpow_of_pos (-s.re)) continuousOn_const).mono hsub
          exact ContinuousOn.intervalIntegrable_of_Icc hkle hcont
        · exact intervalIntegrable_const
        · intro x hx
          have hx' : x ∈ Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by simpa [Set.uIcc_of_le hkle] using hx
          have hx0 : 0 < x := lt_of_lt_of_le hkpos hx'.1
          have hdec : x ^ (-s.re) ≤ (k : ℝ) ^ (-s.re) := by
            exact Real.rpow_le_rpow_of_nonpos hkpos hx'.1 (by linarith : -s.re ≤ 0)
          have hb2 : (((k + 1 : ℕ) : ℝ) ^ (-s.re)) ≤ x ^ (-s.re) := by
            exact Real.rpow_le_rpow_of_nonpos hx0 hx'.2 (by linarith : -s.re ≤ 0)
          linarith
      exact mul_le_mul_of_nonneg_left hg (by positivity)

/-- Telescoping HasSum over `(X+m)^{-β}` differences. -/
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
    have hmain : Tendsto (fun t : ℝ => (t ^ β)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop hβ)
    refine hmain.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [Real.rpow_neg (by linarith : 0 ≤ t) β]
  have hN0 : Tendsto (fun N : ℕ => ((X + N : ℕ) : ℝ) ^ (-β)) atTop (𝓝 0) := hdec.comp hto
  have hmain_t : Tendsto (fun N : ℕ => (X : ℝ) ^ (-β) - ((X + N : ℕ) : ℝ) ^ (-β)) atTop (𝓝 ((X : ℝ) ^ (-β))) := by
    simpa using (tendsto_const_nhds.sub hN0 : Tendsto (fun N : ℕ => (X : ℝ) ^ (-β) - ((X + N : ℕ) : ℝ) ^ (-β)) atTop (𝓝 ((X : ℝ) ^ (-β) - 0)))
  have hsumN : ∀ N : ℕ, (∑ m ∈ Finset.range N, ((((X + m : ℕ) : ℝ) ^ (-β)) - (((X + m + 1 : ℕ) : ℝ) ^ (-β)))) = (X : ℝ) ^ (-β) - (((X + N : ℕ) : ℝ) ^ (-β)) := by
    intro N
    simpa [Nat.add_assoc] using (Finset.sum_range_sub' (fun j : ℕ => ((X + j : ℕ) : ℝ) ^ (-β)) N)
  have hpartial : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, ((((X + m : ℕ) : ℝ) ^ (-β)) - (((X + m + 1 : ℕ) : ℝ) ^ (-β)))) atTop (𝓝 ((X : ℝ) ^ (-β))) := by
    exact hmain_t.congr (fun N => (hsumN N).symm)
  exact (hasSum_iff_tendsto_nat_of_nonneg h_nonneg ((X : ℝ) ^ (-β))).2 hpartial

/-- Summability of the `emTerm` series and the telescoping tail bound. -/
private lemma emTerm_tsum_le (N : ℕ) (hN : 1 ≤ N) (s : ℂ) (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    Summable (fun m : ℕ => emTerm (N + m) s) ∧
      (∑' m : ℕ, ‖emTerm (N + m) s‖) ≤ (‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by
  let u : ℕ → ℝ := fun m => (‖s‖ / s.re) * ((((N + m : ℕ) : ℝ) ^ (-s.re)) - (((N + m + 1 : ℕ) : ℝ) ^ (-s.re)))
  have hu : Summable u := by
    refine (hasSum_telescope_rpow N hN (β := s.re) hs0).summable.mul_left (‖s‖ / s.re)
  have hle : ∀ m : ℕ, ‖emTerm (N + m) s‖ ≤ u m := by
    intro m
    have hN1 : 1 ≤ N + m := by omega
    have hb := norm_emTerm_le (N + m) hN1 s hs0 hs1
    dsimp [u]
    exact hb
  have hnorm : Summable (fun m : ℕ => ‖emTerm (N + m) s‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hle hu
  have hsumm : Summable (fun m : ℕ => emTerm (N + m) s) := Summable.of_norm hnorm
  have htsum : (∑' m : ℕ, u m) = (‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by
    have hmain : HasSum (fun m : ℕ => ((((N + m : ℕ) : ℝ) ^ (-s.re)) - (((N + m + 1 : ℕ) : ℝ) ^ (-s.re)))) ((N : ℝ) ^ (-s.re)) :=
      hasSum_telescope_rpow N hN hs0
    calc
      (∑' m : ℕ, u m) = ∑' m : ℕ, (‖s‖ / s.re) * ((((N + m : ℕ) : ℝ) ^ (-s.re)) - (((N + m + 1 : ℕ) : ℝ) ^ (-s.re))) := rfl
      _ = (‖s‖ / s.re) * (∑' m : ℕ, ((((N + m : ℕ) : ℝ) ^ (-s.re)) - (((N + m + 1 : ℕ) : ℝ) ^ (-s.re)))) := by
        rw [tsum_mul_left]
      _ = (‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by rw [hmain.tsum_eq]
  constructor
  · exact hsumm
  · calc
      (∑' m : ℕ, ‖emTerm (N + m) s‖) ≤ ∑' m : ℕ, u m := hnorm.tsum_le_tsum hle hu
      _ = (‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := htsum

/-- `k^{-σ} - (k+1)^{-σ} ≤ σ * k^{-σ-1}` for `k ≥ 1`, `σ > 0`. -/

private lemma rpow_sub_pow_le (k : ℕ) (hk1 : 1 ≤ k) {σ : ℝ} (hσ : 0 < σ) :
    ((k : ℝ) ^ (-σ)) - (((k + 1 : ℕ) : ℝ) ^ (-σ)) ≤ σ * ((k : ℝ) ^ (-σ - 1)) := by
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hnot0 : (0 : ℝ) ∉ Set.uIcc (k : ℝ) (((k + 1 : ℕ) : ℝ)) := by
    intro hx
    have hx' : (0 : ℝ) ∈ Set.Icc (k : ℝ) (((k + 1 : ℕ) : ℝ)) := by
      simpa [Set.uIcc_of_le hkle] using hx
    linarith [hx'.1, hk0]
  have hne : -σ - 1 ≠ (-1 : ℝ) := by linarith
  have hint := integral_rpow (r := -σ - 1) (a := (k : ℝ)) (b := ((k + 1 : ℕ) : ℝ)) (Or.inr ⟨hne, hnot0⟩)
  have hmain : σ * (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), x ^ (-σ - 1)) =
      ((k : ℝ) ^ (-σ)) - (((k + 1 : ℕ) : ℝ) ^ (-σ)) := by
    rw [hint]
    have hD : -σ - 1 + 1 = -σ := by ring
    rw [hD]
    field_simp [ne_of_gt hσ]
    ring
  have hconst : (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), ((k : ℝ) ^ (-σ - 1)))
      = (k : ℝ) ^ (-σ - 1) := by
    rw [intervalIntegral.integral_const]
    simp
  have hmono : (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), x ^ (-σ - 1))
      ≤ (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), ((k : ℝ) ^ (-σ - 1))) := by
    apply intervalIntegral.integral_mono_on hkle
    · refine ContinuousOn.intervalIntegrable_of_Icc hkle ?_
      refine (continuousOn_rpow_of_pos (-σ - 1)).mono ?_
      intro x hx
      exact lt_of_lt_of_le hk0 hx.1
    · exact ContinuousOn.intervalIntegrable_of_Icc hkle continuousOn_const
    · intro x hx
      have hx' : x ∈ Set.Icc (k : ℝ) (((k + 1 : ℕ) : ℝ)) := by simpa [Set.uIcc_of_le hkle] using hx
      exact Real.rpow_le_rpow_of_nonpos hk0 hx'.1 (by linarith : -σ - 1 ≤ 0)
  calc
    ((k : ℝ) ^ (-σ)) - (((k + 1 : ℕ) : ℝ) ^ (-σ))
        = σ * (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), x ^ (-σ - 1)) := hmain.symm
    _ ≤ σ * (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), ((k : ℝ) ^ (-σ - 1))) := by
      exact mul_le_mul_of_nonneg_left hmono (le_of_lt hσ)
    _ = σ * ((k : ℝ) ^ (-σ - 1)) := by rw [hconst]

/-- Each `emTerm k` term is complex-differentiable away from `s = 1` (for `k ≥ 1`). -/
private lemma differentiableAt_emTerm (k : ℕ) (hk1 : 1 ≤ k) (s0 : ℂ) (hs1 : s0 ≠ 1) :
    DifferentiableAt ℂ (fun s : ℂ => emTerm k s) s0 := by
  have hc1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (show (k + 1 : ℕ) ≠ 0 by omega)
  have hc2 : ((k : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (show (k : ℕ) ≠ 0 by omega)
  have hlin1 : DifferentiableAt ℂ (fun s : ℂ => 1 - s) s0 := by
    exact (differentiableAt_const (1 : ℂ)).sub (differentiableAt_id (x := s0))
  have hlin2 : DifferentiableAt ℂ (fun s : ℂ => -s) s0 :=
    (differentiableAt_id (x := s0)).neg
  have hA : DifferentiableAt ℂ (fun s : ℂ => ((k + 1 : ℕ) : ℂ) ^ (-s)) s0 := by
    exact DifferentiableAt.const_cpow (c := ((k + 1 : ℕ) : ℂ)) (f := fun s : ℂ => -s) hlin2 (Or.inl hc1)
  have hB1 : DifferentiableAt ℂ (fun s : ℂ => ((k + 1 : ℕ) : ℂ) ^ (1 - s)) s0 := by
    exact DifferentiableAt.const_cpow (c := ((k + 1 : ℕ) : ℂ)) (f := fun s : ℂ => 1 - s) hlin1 (Or.inl hc1)
  have hB2 : DifferentiableAt ℂ (fun s : ℂ => ((k : ℕ) : ℂ) ^ (1 - s)) s0 := by
    exact DifferentiableAt.const_cpow (c := ((k : ℕ) : ℂ)) (f := fun s : ℂ => 1 - s) hlin1 (Or.inl hc2)
  have hnum : DifferentiableAt ℂ
      (fun s : ℂ => ((k + 1 : ℕ) : ℂ) ^ (1 - s) - ((k : ℕ) : ℂ) ^ (1 - s)) s0 := hB1.sub hB2
  have hden_nz : (fun s : ℂ => 1 - s) s0 ≠ 0 := by
    dsimp
    exact sub_ne_zero.mpr (Ne.symm hs1)
  have hquot : DifferentiableAt ℂ
      (fun s : ℂ => ((((k + 1 : ℕ) : ℂ) ^ (1 - s)) - (((k : ℕ) : ℂ) ^ (1 - s))) / (1 - s)) s0 := by
    exact hnum.div hlin1 hden_nz
  have hsub : DifferentiableAt ℂ
      ((fun s : ℂ => ((k + 1 : ℕ) : ℂ) ^ (-s)) - (fun s : ℂ => ((((k + 1 : ℕ) : ℂ) ^ (1 - s)) - ((k : ℕ) : ℂ) ^ (1 - s)) / (1 - s))) s0 :=
    hA.sub hquot
  exact hsub.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => by
    dsimp [emTerm]))

private lemma differentiableOn_emTerm_of_ne_one (k : ℕ) (hk1 : 1 ≤ k) :
    DifferentiableOn ℂ (fun s : ℂ => emTerm k s) ({s : ℂ | s ≠ 1} : Set ℂ) := by
  intro s0 hs0
  exact (differentiableAt_emTerm k hk1 s0 hs0).differentiableWithinAt

/-- On a region with `ε < Re w`, `‖w‖ < R`, `w ≠ 1`, the emTerm series terms decay like a
p-series (uniformly in `w`). -/
private lemma emTerm_bound_on (N : ℕ) (hN : 1 ≤ N) {ε R : ℝ} (hε : 0 < ε) {w : ℂ}
    (hεw : ε < w.re) (hwR : ‖w‖ < R) (hw1 : w ≠ 1) (m : ℕ) :
    ‖emTerm (N + m) w‖ ≤ R * (((N + m : ℕ) : ℝ) ^ (-(ε + 1))) := by
  let k : ℕ := N + m
  let σ : ℝ := w.re
  have hσ0 : 0 < σ := lt_trans hε hεw
  have hk1 : 1 ≤ k := by
    dsimp [k]
    omega
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hNm_ge0 : (0 : ℝ) ≤ ‖w‖ / σ := div_nonneg (norm_nonneg w) (le_of_lt hσ0)
  have hb1 := norm_emTerm_le k hk1 w hσ0 hw1
  have hb2 := rpow_sub_pow_le k hk1 hσ0
  have hk0 : (0 : ℝ) ≤ (k : ℝ) ^ (-σ - 1) := Real.rpow_nonneg (by positivity) _
  have hexp : -σ - 1 ≤ -(ε + 1) := by
    linarith
  have hpow : (k : ℝ) ^ (-σ - 1) ≤ (k : ℝ) ^ (-(ε + 1)) :=
    Real.rpow_le_rpow_of_exponent_le hk1' hexp
  calc
    ‖emTerm (N + m) w‖ = ‖emTerm k w‖ := by dsimp [k]
    _ ≤ (‖w‖ / σ) * ((k : ℝ) ^ (-σ) - ((k + 1 : ℕ) : ℝ) ^ (-σ)) := by
      dsimp [σ]
      exact hb1
    _ ≤ (‖w‖ / σ) * (σ * (k : ℝ) ^ (-σ - 1)) := by
      exact mul_le_mul_of_nonneg_left hb2 hNm_ge0
    _ = ‖w‖ * ((k : ℝ) ^ (-σ - 1)) := by
      field_simp [ne_of_gt hσ0]
    _ ≤ R * ((k : ℝ) ^ (-σ - 1)) := by
      exact mul_le_mul_of_nonneg_right (le_of_lt hwR) hk0
    _ ≤ R * ((k : ℝ) ^ (-(ε + 1))) := by
      exact mul_le_mul_of_nonneg_left hpow (le_of_lt (lt_of_le_of_lt (norm_nonneg w) hwR))
    _ = R * (((N + m : ℕ) : ℝ) ^ (-(ε + 1))) := by dsimp [k]

/-- Summability of the uniform p-series bound. -/
private lemma summable_uniform_bound (N : ℕ) (hN : 1 ≤ N) {ε R : ℝ} (hε : 0 < ε) :
    Summable (fun m : ℕ => R * (((N + m : ℕ) : ℝ) ^ (-(ε + 1)))) := by
  have hS : Summable (fun m : ℕ => 1 / |(m : ℝ) + (N : ℝ)| ^ (ε + 1)) :=
    (Real.summable_one_div_nat_add_rpow (N : ℝ) (ε + 1)).2 (by linarith)
  have hcong : ∀ m : ℕ, ((N + m : ℕ) : ℝ) ^ (-(ε + 1)) = 1 / |(m : ℝ) + (N : ℝ)| ^ (ε + 1) := by
    intro m
    have hcast : ((N + m : ℕ) : ℝ) = (m : ℝ) + (N : ℝ) := by
      rw [Nat.cast_add]
      ring
    have hpos : 0 < (m : ℝ) + (N : ℝ) := by exact_mod_cast (by omega : 0 < m + N)
    calc
      ((N + m : ℕ) : ℝ) ^ (-(ε + 1)) = ((m : ℝ) + (N : ℝ)) ^ (-(ε + 1)) := by rw [hcast]
      _ = 1 / ((m : ℝ) + (N : ℝ)) ^ (ε + 1) := by
        rw [Real.rpow_neg (le_of_lt hpos) (ε + 1)]
        rw [inv_eq_one_div]
      _ = 1 / |(m : ℝ) + (N : ℝ)| ^ (ε + 1) := by rw [abs_of_pos hpos]
  have hsum : Summable (fun m : ℕ => ((N + m : ℕ) : ℝ) ^ (-(ε + 1))) := hS.congr (fun m => (hcong m).symm)
  exact hsum.mul_left R


theorem emTerm_tsum_analyticOn (N : ℕ) (hN : 1 ≤ N) :
    AnalyticOnNhd ℂ
      (fun s : ℂ => ∑' m : ℕ,
        ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))))
      {z : ℂ | 0 < z.re ∧ z ≠ 1} := by
  intro z0 hz0
  rcases hz0 with ⟨hz0pos, hz0ne⟩
  let ε : ℝ := z0.re / 2
  let R : ℝ := ‖z0‖ + 1
  let U : Set ℂ := {w : ℂ | ε < w.re ∧ ‖w‖ < R ∧ w ≠ 1}
  have hε : 0 < ε := by
    dsimp [ε]
    nlinarith
  have hz0U : z0 ∈ U := by
    dsimp [U, ε, R]
    constructor
    · nlinarith
    · constructor
      · linarith
      · exact hz0ne
  have hUopen : IsOpen U := by
    dsimp [U]
    have hA : IsOpen {w : ℂ | ε < w.re} := by
      exact isOpen_lt (f := fun _ : ℂ => ε) (g := fun w : ℂ => w.re) continuous_const Complex.continuous_re
    have hB : IsOpen {w : ℂ | ‖w‖ < R} := by
      simpa [Metric.ball, dist_eq_norm, norm_zero] using (Metric.isOpen_ball (x := (0 : ℂ)) (ε := R))
    have hC : IsOpen {w : ℂ | w ≠ 1} := by
      simpa [Set.compl_singleton_eq] using (isOpen_compl_singleton (x := (1 : ℂ)))
    have hEq : {w : ℂ | ε < w.re ∧ ‖w‖ < R ∧ w ≠ 1} =
        (({w : ℂ | ε < w.re} ∩ {w : ℂ | ‖w‖ < R}) ∩ {w : ℂ | w ≠ 1}) := by
      ext w
      simp [and_assoc]
    rw [hEq]
    exact (hA.inter hB).inter hC
  have hFdiff : DifferentiableOn ℂ (fun s : ℂ => ∑' m : ℕ, emTerm (N + m) s) U := by
    refine differentiableOn_tsum_of_summable_norm (F := fun (m : ℕ) (s : ℂ) => emTerm (N + m) s)
      (u := fun m : ℕ => R * (((N + m : ℕ) : ℝ) ^ (-(ε + 1)))) ?hu ?hf hUopen ?hle
    · exact summable_uniform_bound N hN hε
    · intro m
      refine (differentiableOn_emTerm_of_ne_one (N + m) (by omega)).mono ?_
      intro w hw
      exact hw.2.2
    · intro m w hw
      exact emTerm_bound_on N hN hε hw.1 hw.2.1 hw.2.2 m
  have hAnU : AnalyticOnNhd ℂ (fun s : ℂ => ∑' m : ℕ, emTerm (N + m) s) U :=
    hFdiff.analyticOnNhd hUopen
  have hAn : AnalyticAt ℂ (fun s : ℂ => ∑' m : ℕ, emTerm (N + m) s) z0 := hAnU z0 hz0U
  -- convert to the raw function
  refine hAn.congr ?_
  refine Filter.Eventually.of_forall (fun s => ?_)
  apply tsum_congr
  intro m
  rfl


end Commons.NumberTheory.Zeta
