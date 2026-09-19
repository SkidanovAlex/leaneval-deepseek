import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section
open Filter Set
open scoped Topology BigOperators

namespace Commons.NumberTheory.Zeta

private def emTerm (k : ℕ) (s : ℂ) : ℂ :=
  ((((k + 1 : ℕ) : ℂ) ^ (-s)) -
    (((((k + 1 : ℕ) : ℂ) ^ (1 - s)) - (((k : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))

private lemma hne_of_hs1 (s : ℂ) (hs1 : s ≠ 1) : (-s : ℂ) ≠ (-1 : ℂ) := by
  intro h
  apply hs1
  have hre : s.re = 1 := by
    have hr := congrArg Complex.re h
    simpa using hr
  have him : s.im = 0 := by
    have hi := congrArg Complex.im h
    simpa using hi
  exact Complex.ext (by simpa using hre) (by simpa using him)

private lemma hnot0_of_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : (0 : ℝ) ∉ Set.uIcc a b := by
  intro hx
  rcases (Set.mem_uIcc.mp hx) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · linarith
  · linarith

private lemma emTerm_eq_sub_integral (k : ℕ) (s : ℂ) (hk : 1 ≤ k) (hs1 : s ≠ 1) :
    emTerm k s = ((k + 1 : ℕ) : ℂ) ^ (-s) -
      (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (x : ℂ) ^ (-s)) := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_one) hk)
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hnot0 : (0 : ℝ) ∉ Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ) := hnot0_of_pos hk0 hkle
  have hne : (-s : ℂ) ≠ (-1 : ℂ) := hne_of_hs1 s hs1
  unfold emTerm
  have hint := integral_cpow (r := -s) (a := (k : ℝ)) (b := ((k + 1 : ℕ) : ℝ)) (Or.inr ⟨hne, hnot0⟩)
  rw [hint]
  rw [show (-s + 1 : ℂ) = 1 - s by ring]
  norm_num

private lemma rpow_neg_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (σ : ℝ) (hσ : 0 < σ) :
    b ^ (-σ) ≤ a ^ (-σ) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hpow : a ^ σ ≤ b ^ σ := Real.rpow_le_rpow (le_of_lt ha) hab (le_of_lt hσ)
  have haσ : 0 < a ^ σ := Real.rpow_pos_of_pos ha σ
  have hbσ : 0 < b ^ σ := Real.rpow_pos_of_pos hb σ
  calc
    b ^ (-σ) = (b ^ σ)⁻¹ := by rw [Real.rpow_neg (le_of_lt hb)]
    _ ≤ (a ^ σ)⁻¹ := (inv_le_inv₀ hbσ haσ).2 hpow
    _ = a ^ (-σ) := by rw [Real.rpow_neg (le_of_lt ha)]

private lemma re_neg_sub_one (s : ℂ) : (-s - 1).re = -s.re - 1 := by
  simp [Complex.neg_re, Complex.sub_re, Complex.one_re]

private lemma norm_cpow_of_real_neg_sub_one (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-s.re - 1) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx (-s - 1)]
  rw [re_neg_sub_one]

private lemma integral_norm_cpow_sub_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (s : ℂ)
    (hs : 0 < s.re) :
    (∫ x : ℝ in a..b, ‖(x : ℂ) ^ (-s - 1)‖) = (a ^ (-s.re) - b ^ (-s.re)) / s.re := by
  have hnot0 : (0 : ℝ) ∉ Set.uIcc a b := hnot0_of_pos ha hab
  have hne : -s.re - 1 ≠ (-1 : ℝ) := by linarith
  calc
    (∫ x : ℝ in a..b, ‖(x : ℂ) ^ (-s - 1)‖)
        = ∫ x : ℝ in a..b, x ^ (-s.re - 1) := by
            apply intervalIntegral.integral_congr
            intro x hx
            have hx0 : 0 < x := by
              have hx' : x ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using hx
              linarith [hx'.1, ha]
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
  have hnot0 : (0 : ℝ) ∉ Set.uIcc a b := hnot0_of_pos ha hab
  have hsnz : s ≠ 0 := by
    intro h
    exact (ne_of_gt hs) (by simpa [h])
  have hne : (-s - 1 : ℂ) ≠ (-1 : ℂ) := by
    intro h
    apply hsnz
    have h' := congrArg Complex.re h
    have : -s.re - 1 = -1 := by simpa [re_neg_sub_one] using h'
    linarith
  have hint := integral_cpow (r := -s - 1) (a := a) (b := b) (Or.inr ⟨hne, hnot0⟩)
  rw [hint]
  have hsneg : (-s : ℂ) ≠ 0 := by
    intro h
    apply hsnz
    exact neg_eq_zero.mp h
  field_simp [hsneg]
  ring

private lemma norm_cpow_sub_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (s : ℂ)
    (hs : 0 < s.re) :
    ‖(b : ℂ) ^ (-s) - (a : ℂ) ^ (-s)‖ ≤
      (‖s‖ / s.re) * (a ^ (-s.re) - b ^ (-s.re)) := by
  have hsub := cpow_sub_eq_smul_integral_of_le ha hab s hs
  calc
    ‖(b : ℂ) ^ (-s) - (a : ℂ) ^ (-s)‖
        = ‖(a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)‖ := by
            rw [← norm_neg]
            congr 1
            ring
    _ = ‖s * (∫ x : ℝ in a..b, (x : ℂ) ^ (-s - 1))‖ := by rw [← hsub]
    _ ≤ ‖s‖ * ‖(∫ x : ℝ in a..b, (x : ℂ) ^ (-s - 1))‖ := norm_mul_le _ _
    _ ≤ ‖s‖ * (∫ x : ℝ in a..b, ‖(x : ℂ) ^ (-s - 1)‖) := by
      exact mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm hab) (norm_nonneg s)
    _ = (‖s‖ / s.re) * (a ^ (-s.re) - b ^ (-s.re)) := by
      rw [integral_norm_cpow_sub_of_le ha hab s hs]
      field_simp [ne_of_gt hs]

private lemma pos_of_mem_uIcc {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b) (hx : x ∈ Set.uIcc a b) : 0 < x := by
  rcases (Set.mem_uIcc.mp hx) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · linarith
  · linarith

private lemma emTerm_norm_le (k : ℕ) (s : ℂ) (hk : 1 ≤ k) (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    ‖emTerm k s‖ ≤ (‖s‖ / s.re) * (((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) := by
  let c : ℝ := ‖s‖ / s.re
  let C : ℂ := (((k + 1 : ℕ) : ℂ) ^ (-s))
  let f : ℝ → ℂ := fun x : ℝ => (x : ℂ) ^ (-s)
  let g : ℝ → ℂ := fun x : ℝ => C - f x
  let D : ℝ := c * (((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re)))
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_one) hk)
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hlen : ((k + 1 : ℕ) : ℝ) - (k : ℝ) = 1 := by push_cast; ring
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (norm_nonneg s) (le_of_lt hs0)
  have hf_cont : ContinuousOn f (Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ)) := by
    intro x hx
    have hxne : x ≠ 0 := (pos_of_mem_uIcc hk0 hkle hx).ne'
    exact (Complex.continuousAt_ofReal_cpow_const x (-s) (Or.inr hxne)).continuousWithinAt
  have hf_int : IntervalIntegrable f MeasureTheory.volume (k : ℝ) ((k + 1 : ℕ) : ℝ) :=
    ContinuousOn.intervalIntegrable hf_cont
  have hC_int : IntervalIntegrable (fun _ : ℝ => C) MeasureTheory.volume (k : ℝ) ((k + 1 : ℕ) : ℝ) :=
    Continuous.intervalIntegrable continuous_const (k : ℝ) ((k + 1 : ℕ) : ℝ)
  have hg_cont : ContinuousOn g (Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ)) := by
    intro x hx
    exact (continuousWithinAt_const.sub (hf_cont x hx))
  have hg_norm_cont : ContinuousOn (fun x : ℝ => ‖g x‖) (Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ)) := hg_cont.norm
  have hnorm_int : IntervalIntegrable (fun x : ℝ => ‖g x‖) MeasureTheory.volume (k : ℝ) ((k + 1 : ℕ) : ℝ) :=
    ContinuousOn.intervalIntegrable hg_norm_cont
  have heq_int : C - (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), f x) =
      (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), g x) := by
    calc
      C - (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), f x)
          = (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (fun _ : ℝ => C) x)
              - (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), f x) := by
              rw [intervalIntegral.integral_const]
              rw [hlen]
              simp
      _ = (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (fun _ : ℝ => C) x - f x) :=
              (intervalIntegral.integral_sub hC_int hf_int).symm
      _ = (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), g x) := rfl
  have heq : emTerm k s = (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), g x) := by
    calc
      emTerm k s = C - (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), f x) := by
        simpa [C, f] using emTerm_eq_sub_integral k s hk hs1
      _ = (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), g x) := heq_int
  have hpoint : ∀ x ∈ Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ), ‖g x‖ ≤ D := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hk0 hx.1
    have hbnd := norm_cpow_sub_of_le (a := x) (b := ((k + 1 : ℕ) : ℝ)) hxpos hx.2 s hs0
    have hdec := rpow_neg_antitone (a := (k : ℝ)) (b := x) hk0 hx.1 s.re hs0
    have hstep : c * (x ^ (-s.re) - ((k + 1 : ℕ) : ℝ) ^ (-s.re)) ≤ D := by
      dsimp [D, c]
      have hmul : (x ^ (-s.re) - ((k + 1 : ℕ) : ℝ) ^ (-s.re)) ≤
          ((k : ℝ) ^ (-s.re) - ((k + 1 : ℕ) : ℝ) ^ (-s.re)) := by linarith
      exact mul_le_mul_of_nonneg_left hmul hc0
    calc
      ‖g x‖ = ‖(((((k + 1 : ℕ) : ℝ) : ℂ) ^ (-s)) - ((x : ℂ) ^ (-s)))‖ := rfl
      _ ≤ c * (x ^ (-s.re) - ((k + 1 : ℕ) : ℝ) ^ (-s.re)) := by simpa [g, C, f, c] using hbnd
      _ ≤ D := hstep
  calc
    ‖emTerm k s‖ = ‖(∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), g x)‖ := by rw [heq]
    _ ≤ (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), ‖g x‖) :=
        intervalIntegral.norm_integral_le_integral_norm hkle
    _ ≤ (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (fun _ : ℝ => D) x) := by
      exact intervalIntegral.integral_mono_on hkle hnorm_int
        (Continuous.intervalIntegrable continuous_const (k : ℝ) ((k + 1 : ℕ) : ℝ)) hpoint
    _ = D := by
      rw [intervalIntegral.integral_const]
      rw [hlen]
      simp
    _ = (‖s‖ / s.re) * (((k : ℝ) ^ (-s.re)) - (((k + 1 : ℕ) : ℝ) ^ (-s.re))) := by
      dsimp [D, c]

/-- telescoping shifted differences, `HasSum` value u N -/
private lemma hasSum_telescoping_shift {u : ℕ → ℝ} (N : ℕ)
    (hmono : ∀ m : ℕ, u (N + m + 1) ≤ u (N + m))
    (htend : Tendsto (fun m : ℕ => u (N + m)) atTop (𝓝 0)) :
    HasSum (fun m : ℕ => u (N + m) - u (N + m + 1)) (u N) := by
  have hnonneg : ∀ m : ℕ, 0 ≤ u (N + m) - u (N + m + 1) := fun m => sub_nonneg.mpr (hmono m)
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg (u N)).2
  -- partial sums equal u N - u (N + M), then take limit
  have hsum : ∀ M : ℕ, (∑ i ∈ Finset.range M, (u (N + i) - u (N + i + 1))) = u N - u (N + M) := by
    intro M
    calc
      (∑ i ∈ Finset.range M, (u (N + i) - u (N + i + 1)))
          = (∑ i ∈ Finset.range M, (u (N + i) - u (N + (i + 1)))) := rfl
      _ = u (N + 0) - u (N + M) := Finset.sum_range_sub' (fun j : ℕ => u (N + j)) M
      _ = u N - u (N + M) := rfl
  have hlim : Tendsto (fun M : ℕ => u N - u (N + M)) atTop (𝓝 (u N - 0)) :=
    tendsto_const_nhds.sub htend
  simpa using hlim.congr' (Filter.Eventually.of_forall (fun M => (hsum M).symm))

private lemma tel_summable_tsum {u : ℕ → ℝ} (N : ℕ) (c : ℝ)
    (hmono : ∀ m : ℕ, u (N + m + 1) ≤ u (N + m))
    (htend : Tendsto (fun m : ℕ => u (N + m)) atTop (𝓝 0)) :
    Summable (fun m : ℕ => c * (u (N + m) - u (N + m + 1))) ∧
      (∑' m : ℕ, c * (u (N + m) - u (N + m + 1))) = c * u N := by
  have h := hasSum_telescoping_shift N hmono htend
  have hmul : HasSum (fun m : ℕ => c * (u (N + m) - u (N + m + 1))) (c * u N) :=
    h.mul_left c
  exact ⟨hmul.summable, hmul.tsum_eq⟩

private lemma shifted_rpow_antitone (N : ℕ) (hN : 1 ≤ N) (σ : ℝ) (hσ : 0 < σ) (m : ℕ) :
    (((N + m + 1 : ℕ) : ℝ) ^ (-σ)) ≤ (((N + m : ℕ) : ℝ) ^ (-σ)) := by
  have hpos : 0 < ((N + m : ℕ) : ℝ) := by
    have h1 : 1 ≤ N + m := by omega
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h1)
  have hle : ((N + m : ℕ) : ℝ) ≤ ((N + m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  exact rpow_neg_antitone hpos hle σ hσ

private lemma u_shift_tendsto_zero (N : ℕ) (σ : ℝ) (hσ : 0 < σ) :
    Tendsto (fun m : ℕ => (((N + m : ℕ) : ℝ) ^ (-σ))) atTop (𝓝 0) := by
  have hcast : Tendsto (fun m : ℕ => ((N + m : ℕ) : ℝ)) atTop atTop := by
    have hnat : Tendsto (fun m : ℕ => N + m) atTop atTop := by
      simpa [Nat.add_comm] using (tendsto_add_atTop_nat N : Tendsto (fun m : ℕ => m + N) atTop atTop)
    simpa [Function.comp_def] using
      (tendsto_natCast_atTop_atTop : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop).comp hnat
  exact (tendsto_rpow_neg_atTop hσ).comp hcast

private lemma tel_main (N : ℕ) (hN : 1 ≤ N) (s : ℂ) (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    Summable (fun m : ℕ => emTerm (N + m) s) ∧
      (∑' m : ℕ, ‖emTerm (N + m) s‖) ≤
        (‖s‖ / s.re) * (((N : ℕ) : ℝ) ^ (-s.re)) := by
  let σ : ℝ := s.re
  let u : ℕ → ℝ := fun n : ℕ => (n : ℝ) ^ (-σ)
  let c : ℝ := ‖s‖ / s.re
  let h : ℕ → ℝ := fun m : ℕ => c * (u (N + m) - u (N + m + 1))
  have hσ0 : 0 < σ := by dsimp [σ]; exact hs0
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (norm_nonneg s) (le_of_lt hs0)
  have hmono : ∀ m : ℕ, u (N + m + 1) ≤ u (N + m) := by
    intro m
    dsimp [u, σ]
    exact shifted_rpow_antitone N hN s.re hs0 m
  have htend : Tendsto (fun m : ℕ => u (N + m)) atTop (𝓝 0) := by
    dsimp [u, σ]
    exact u_shift_tendsto_zero N s.re hs0
  have htel := tel_summable_tsum (u := u) N c hmono htend
  have hsum_h : Summable h := by simpa [h] using htel.1
  have hts_h : (∑' m : ℕ, h m) = c * u N := by simpa [h] using htel.2
  -- pointwise domination of the emTerm norms by h
  have hle : ∀ m : ℕ, ‖emTerm (N + m) s‖ ≤ h m := by
    intro m
    have hk : 1 ≤ N + m := by omega
    have hb := emTerm_norm_le (N + m) s hk hs0 hs1
    dsimp [h, u, σ, c]
    exact hb
  have hh0 : ∀ m : ℕ, 0 ≤ h m := fun m => le_trans (norm_nonneg _) (hle m)
  -- summability of the norm series, and of the complex series
  have hsum_norm : Summable (fun m : ℕ => ‖emTerm (N + m) s‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hle hsum_h
  have hsum_complex : Summable (fun m : ℕ => emTerm (N + m) s) :=
    Summable.of_norm_bounded hsum_h hle
  have htsum : (∑' m : ℕ, ‖emTerm (N + m) s‖) ≤ ∑' m : ℕ, h m :=
    hsum_norm.tsum_le_tsum hle hsum_h
  exact ⟨hsum_complex, by
    have ht := htsum
    rw [hts_h] at ht
    dsimp [u, c, σ] at ht
    exact ht⟩

/-- the exact requested statement -/
theorem emTerm_tsum_le (N : ℕ) (hN : 1 ≤ N) (s : ℂ) (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    Summable (fun m : ℕ =>
        ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))) ∧
      (∑' m : ℕ, ‖((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))‖) ≤
        (‖s‖ / s.re) * (((N : ℕ) : ℝ) ^ (-s.re)) := by
  have hmain := tel_main N hN s hs0 hs1
  have heq : ∀ m : ℕ,
      emTerm (N + m) s =
        ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))) := by
    intro m
    rfl
  constructor
  · exact hmain.1.congr heq
  · calc
      (∑' m : ℕ, ‖((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))‖)
          = (∑' m : ℕ, ‖emTerm (N + m) s‖) := by
            apply tsum_congr
            intro m
            rw [heq m]
      _ ≤ (‖s‖ / s.re) * (((N : ℕ) : ℝ) ^ (-s.re)) := hmain.2

end Commons.NumberTheory.Zeta
