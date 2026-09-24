import Mathlib
import Submission.Work.GM.Energy.Defs
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.R_l2
import Submission.Work.GM.Energy.EnergyCore.ratio_inj_gcd
import Submission.Work.GM.Energy.EnergyCore.integral_cube_le
import Submission.Work.GM.Energy.EnergyCore.integral_comp_inv_half_one
import Submission.Work.GM.Energy.EnergyCore.integral_indicator_Icc
import Submission.Work.GM.S3.integral_mul_le_sqrt_mul_sqrt
import Submission.Work.GM.Energy.EnergyCore.sum_window_le
import Submission.Work.GM.Energy.EnergyCore.energy_ge_card_pow_four

/-!
# The fractions `n₁/n₂` with `gcd n₁ n₂ = d` (GM Lemma 11.8)

For `N, d : ℕ`, `fracSet N d` is the finite set of real numbers `n₁/n₂` with
`n₁, n₂ ∈ [N, 2N]` and `Nat.gcd n₁ n₂ = d`.  We record the facts used in the proof of GM Lemma
11.8: the elements lie in `[1/2,2]`, distinct elements are `d²/(4N²)`-separated, and hence a
window of length `ℓ` contains at most `1 + ℓ·4N²/d²` of them.
-/

namespace Work.GM.Energy.EnergyCore

open Complex Finset
open scoped BigOperators
set_option autoImplicit false

/-- The fractions `n₁/n₂` with `n₁, n₂ ∈ [N, 2N]` and `Nat.gcd n₁ n₂ = d`. -/
noncomputable def fracSet (N d : ℕ) : Finset ℝ :=
  (((Finset.Icc N (2 * N)).product (Finset.Icc N (2 * N))).filter
      (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 = d)).image (fun p : ℕ × ℕ => (p.1 : ℝ) / (p.2 : ℝ))

lemma mem_fracSet {N d : ℕ} {f : ℝ} :
    f ∈ fracSet N d ↔ ∃ n1 ∈ Finset.Icc N (2 * N), ∃ n2 ∈ Finset.Icc N (2 * N),
      Nat.gcd n1 n2 = d ∧ f = (n1 : ℝ) / (n2 : ℝ) := by
  classical
  rw [fracSet, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [Finset.mem_filter] at hp
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hpa, hpb⟩ := Finset.mem_product.mp hp1
    exact ⟨p.1, hpa, p.2, hpb, hp2, rfl⟩
  · rintro ⟨n1, h1, n2, h2, hg, rfl⟩
    exact ⟨(n1, n2), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1, h2⟩, hg⟩, rfl⟩

/-- If `N ≥ 1` and `fracSet N d` is nonempty then `d > 0`. -/
lemma fracSet_d_pos {N d : ℕ} (hN : 1 ≤ N) {f : ℝ} (hf : f ∈ fracSet N d) : 0 < d := by
  obtain ⟨n1, h1, n2, h2, hg, -⟩ := mem_fracSet.mp hf
  rw [Finset.mem_Icc] at h1 h2
  rw [← hg]
  exact Nat.gcd_pos_of_pos_left n2 (by omega)

lemma fracSet_bounds {N d : ℕ} (hN : 1 ≤ N) {f : ℝ} (hf : f ∈ fracSet N d) :
    (1 : ℝ) / 2 ≤ f ∧ f ≤ 2 := by
  obtain ⟨n1, h1, n2, h2, -, rfl⟩ := mem_fracSet.mp hf
  rw [Finset.mem_Icc] at h1 h2
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn1l : (N : ℝ) ≤ (n1 : ℝ) := by exact_mod_cast h1.1
  have hn2l : (N : ℝ) ≤ (n2 : ℝ) := by exact_mod_cast h2.1
  have hn1u : (n1 : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast h1.2
  have hn2u : (n2 : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast h2.2
  have hn2pos : (0 : ℝ) < (n2 : ℝ) := by linarith
  constructor
  · rw [le_div_iff₀ hn2pos]; nlinarith
  · rw [div_le_iff₀ hn2pos]; nlinarith

/-- A fraction of `fracSet N d` can be written in lowest terms `a/b` with `b·d ≤ 2N`. -/
lemma fracSet_reduced {N d : ℕ} (hN : 1 ≤ N) {f : ℝ} (hf : f ∈ fracSet N d) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ f = (a : ℝ) / (b : ℝ) ∧
      (b : ℝ) ≤ 2 * (N : ℝ) / (d : ℝ) := by
  obtain ⟨n1, h1, n2, h2, hg, rfl⟩ := mem_fracSet.mp hf
  rw [Finset.mem_Icc] at h1 h2
  have hn1pos : 0 < n1 := by omega
  have hn2pos : 0 < n2 := by omega
  have hdpos : 0 < d := by rw [← hg]; exact Nat.gcd_pos_of_pos_left n2 hn1pos
  have hdvd1 : d ∣ n1 := by rw [← hg]; exact Nat.gcd_dvd_left n1 n2
  have hdvd2 : d ∣ n2 := by rw [← hg]; exact Nat.gcd_dvd_right n1 n2
  have hdne : (d : ℝ) ≠ 0 := by positivity
  have hApos : 0 < n1 / d := Nat.div_pos (Nat.le_of_dvd hn1pos hdvd1) hdpos
  have hBpos : 0 < n2 / d := Nat.div_pos (Nat.le_of_dvd hn2pos hdvd2) hdpos
  refine ⟨n1 / d, n2 / d, hApos, hBpos, ?_, ?_, ?_⟩
  · have hh := Nat.coprime_div_gcd_div_gcd (m := n1) (n := n2) (by rw [hg]; exact hdpos)
    rwa [hg] at hh
  · have e1 : d * (n1 / d) = n1 := Nat.mul_div_cancel' hdvd1
    have e2 : d * (n2 / d) = n2 := Nat.mul_div_cancel' hdvd2
    have h1' : (n1 : ℝ) = (d : ℝ) * ((n1 / d : ℕ) : ℝ) := by
      have := congrArg (fun m : ℕ => (m : ℝ)) e1
      push_cast at this
      exact this.symm
    have h2' : (n2 : ℝ) = (d : ℝ) * ((n2 / d : ℕ) : ℝ) := by
      have := congrArg (fun m : ℕ => (m : ℝ)) e2
      push_cast at this
      exact this.symm
    rw [h1', h2', mul_div_mul_left _ _ hdne]
  · have e2 : d * (n2 / d) = n2 := Nat.mul_div_cancel' hdvd2
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
    have hn2u : (n2 : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast h2.2
    have hcast : ((n2 / d : ℕ) : ℝ) = (n2 : ℝ) / (d : ℝ) :=
      Nat.cast_div hdvd2 hdne
    rw [hcast]
    exact div_le_div_of_nonneg_right hn2u (le_of_lt hdR)

/-- Distinct elements of `fracSet N d` are `d²/(4N²)`-separated. -/
lemma fracSet_sep {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) {f f' : ℝ} (hf : f ∈ fracSet N d)
    (hf' : f' ∈ fracSet N d) (hne : f ≠ f') :
    (d : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2) ≤ |f - f'| := by
  obtain ⟨a, b, ha, hb, hcop, hfeq, hble⟩ := fracSet_reduced hN hf
  obtain ⟨c, e, hc, he, hcop2, hf'eq, hele⟩ := fracSet_reduced hN hf'
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hdR : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  have hne' : (a : ℝ) / (b : ℝ) ≠ (c : ℝ) / (e : ℝ) := by
    rw [← hfeq, ← hf'eq]; exact hne
  have hcross : (a : ℝ) * e - (c : ℝ) * b ≠ 0 := by
    intro h0
    apply hne'
    rw [div_eq_div_iff (ne_of_gt hbR) (ne_of_gt heR)]
    linarith [h0]
  have hint : (1 : ℝ) ≤ |(a : ℝ) * e - (c : ℝ) * b| := by
    have hz : ((a : ℤ) * (e : ℤ) - (c : ℤ) * (b : ℤ)) ≠ 0 := by
      intro hz0
      apply hcross
      have hcast := congrArg (fun z : ℤ => ((z : ℝ))) hz0
      push_cast at hcast
      simpa using hcast
    have h1 : (1 : ℤ) ≤ |(a : ℤ) * (e : ℤ) - (c : ℤ) * (b : ℤ)| := Int.one_le_abs hz
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|(a : ℤ) * (e : ℤ) - (c : ℤ) * (b : ℤ)| : ℤ) : ℝ) := by
      exact_mod_cast h1
    rw [Int.cast_abs] at h2
    push_cast at h2
    linarith [h2]
  have hdist : |f - f'| = |(a : ℝ) * e - (c : ℝ) * b| / ((b : ℝ) * e) := by
    have h1 : f - f' = ((a : ℝ) * e - (b : ℝ) * c) / ((b : ℝ) * e) := by
      rw [hfeq, hf'eq, div_sub_div _ _ (ne_of_gt hbR) (ne_of_gt heR)]
    rw [h1, abs_div, abs_of_pos (mul_pos hbR heR),
      show (a : ℝ) * e - (b : ℝ) * c = (a : ℝ) * e - (c : ℝ) * b by ring]
  have hbe : (b : ℝ) * e ≤ (2 * (N : ℝ) / (d : ℝ)) ^ 2 := by
    have h1 : 0 ≤ 2 * (N : ℝ) / (d : ℝ) := by positivity
    nlinarith [hble, hele, hbR, heR]
  have hden : 0 < (b : ℝ) * e := mul_pos hbR heR
  calc (d : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)
      = 1 / ((2 * (N : ℝ) / (d : ℝ)) ^ 2) := by
        field_simp
        ring
    _ ≤ 1 / ((b : ℝ) * e) := one_div_le_one_div_of_le hden hbe
    _ ≤ |(a : ℝ) * e - (c : ℝ) * b| / ((b : ℝ) * e) :=
        div_le_div_of_nonneg_right hint (le_of_lt hden)
    _ = |f - f'| := hdist.symm

/-- Counting: a window of length `v - u` contains at most `(v-u)·4N²/d² + 1` elements of
`fracSet N d`. -/
lemma fracSet_window_card {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) {u v : ℝ} (huv : u ≤ v) :
    (((fracSet N d).filter (fun f => u ≤ f ∧ f ≤ v)).card : ℝ)
      ≤ (v - u) / ((d : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)) + 1 := by
  have hδ : 0 < (d : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2) := by
    have hdR : (0 : ℝ) < (d : ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
    positivity
  refine Work.GM.S3.card_le_of_separated hδ huv ?_ ?_
  · intro w hw
    exact (Finset.mem_filter.mp hw).2
  · intro t ht s hs hts
    exact fracSet_sep hN hd (Finset.mem_of_mem_filter t ht) (Finset.mem_of_mem_filter s hs) hts

/-- The elements of `fracSet N d` within `κ ≥ 0` of a point `x`. -/
lemma fracSet_ball_card {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) {κ x : ℝ} (hκ : 0 ≤ κ) :
    (((fracSet N d).filter (fun f => |x - f| ≤ κ)).card : ℝ)
      ≤ 2 * κ / ((d : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)) + 1 := by
  have hsub : ∀ f ∈ (fracSet N d).filter (fun f => |x - f| ≤ κ), x - κ ≤ f ∧ f ≤ x + κ := by
    intro f hf
    have h1 : |x - f| ≤ κ := (Finset.mem_filter.mp hf).2
    rw [abs_le] at h1
    exact ⟨by linarith [h1.2], by linarith [h1.1]⟩
  have hset : (fracSet N d).filter (fun f => |x - f| ≤ κ)
      ⊆ (fracSet N d).filter (fun f => x - κ ≤ f ∧ f ≤ x + κ) := by
    intro f hf
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hf).1, hsub f hf⟩
  calc (((fracSet N d).filter (fun f => |x - f| ≤ κ)).card : ℝ)
      ≤ (((fracSet N d).filter (fun f => x - κ ≤ f ∧ f ≤ x + κ)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hset
    _ ≤ ((x + κ) - (x - κ)) / ((d : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)) + 1 :=
        fracSet_window_card hN hd (by linarith)
    _ = 2 * κ / ((d : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)) + 1 := by ring_nf

/-- `(x+y)³ ≤ 8x³ + 8y³` for `x, y ≥ 0`. -/
lemma add_cube_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) ^ 3 ≤ 8 * x ^ 3 + 8 * y ^ 3 := by
  rcases le_total y x with h | h
  · have h1 : x + y ≤ 2 * x := by linarith
    have h0 : 0 ≤ x + y := by linarith
    have h2 : (x + y) ^ 3 ≤ (2 * x) ^ 3 := pow_le_pow_left₀ h0 h1 3
    nlinarith [pow_nonneg hy 3, h2]
  · have h1 : x + y ≤ 2 * y := by linarith
    have h0 : 0 ≤ x + y := by linarith
    have h2 : (x + y) ^ 3 ≤ (2 * y) ^ 3 := pow_le_pow_left₀ h0 h1 3
    nlinarith [pow_nonneg hx 3, h2]

/-- `‖Rfun W ·‖` is continuous on `[1/2, 2]`. -/
lemma continuousOn_norm_Rfun (W : Finset ℝ) :
    ContinuousOn (fun v : ℝ => ‖Submission.GM.Rfun W v‖) (Set.Icc (1 / 2 : ℝ) 2) := by
  intro x hx
  have hx0 : x ≠ 0 := by
    have : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx.1
    exact ne_of_gt this
  exact ((Work.GM.S3.continuousAt_Rfun W hx0).norm).continuousWithinAt

/-- The `L³` integral of `‖Rfun W‖` over `[1/2,2]` is controlled by the `L²` and `L⁴` integrals
over `[1,2]` (substitution `v ↦ 1/v` plus Hölder). -/
lemma integral_half_two_cube_le (W : Finset ℝ) {M2 M4 : ℝ}
    (h2 : ∫ v in (1 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 2 ≤ M2)
    (h4 : ∫ v in (1 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 4 ≤ M4) :
    ∫ v in (1 / 2 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 3 ≤ 2 * Real.sqrt (M2 * M4) := by
  set g : ℝ → ℝ := fun v => ‖Submission.GM.Rfun W v‖ with hg
  have hgcont : ContinuousOn g (Set.Icc (1 / 2 : ℝ) 2) := continuousOn_norm_Rfun W
  have hg3 : ContinuousOn (fun v => g v ^ 3) (Set.Icc (1 / 2 : ℝ) 2) := hgcont.pow 3
  have hg12 : ContinuousOn (fun v => g v ^ 3) (Set.Icc (1 : ℝ) 2) :=
    hg3.mono (Set.Icc_subset_Icc (by norm_num) le_rfl)
  have hg0 : ∀ v, 0 ≤ g v := fun v => norm_nonneg _
  have hsplit : ∫ v in (1 / 2 : ℝ)..2, g v ^ 3
      = (∫ v in (1 / 2 : ℝ)..1, g v ^ 3) + ∫ v in (1 : ℝ)..2, g v ^ 3 := by
    have i1 : IntervalIntegrable (fun v => g v ^ 3) MeasureTheory.volume (1 / 2 : ℝ) 1 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
      exact hg3.mono (Set.Icc_subset_Icc le_rfl (by norm_num))
    have i2 : IntervalIntegrable (fun v => g v ^ 3) MeasureTheory.volume (1 : ℝ) 2 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
      exact hg12
    exact (intervalIntegral.integral_add_adjacent_intervals i1 i2).symm
  have hlow : ∫ v in (1 / 2 : ℝ)..1, g v ^ 3 ≤ ∫ v in (1 : ℝ)..2, g v ^ 3 := by
    have hsubst : ∫ v in (1 / 2 : ℝ)..1, g v ^ 3
        = ∫ u in (1 : ℝ)..2, g u ^ 3 / u ^ 2 := by
      have hpt : ∀ v ∈ Set.uIcc (1 / 2 : ℝ) 1, g v ^ 3 = g (1 / v) ^ 3 := by
        intro v hv
        rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hv
        have hv0 : v ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hv.1)
        simp only [hg]
        rw [Work.GM.S3.Rfun_norm_one_div W hv0]
      rw [intervalIntegral.integral_congr hpt]
      exact Work.GM.Energy.EnergyCore.integral_comp_inv_half_one hg3
    rw [hsubst]
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ (fun u hu => ?_)
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
      exact hg12.div (continuousOn_id.pow 2) (fun u hu =>
        pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le (by norm_num) hu.1)))
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
      exact hg12
    · have hu0 : (0 : ℝ) < u := lt_of_lt_of_le (by norm_num) hu.1
      have hu2 : (1 : ℝ) ≤ u ^ 2 := by nlinarith [hu.1]
      have h3 : 0 ≤ g u ^ 3 := by positivity
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < u ^ 2)]
      nlinarith [hu2, h3]
  have hholder : ∫ u in (1 : ℝ)..2, g u ^ 3
      ≤ Real.sqrt (∫ u in (1 : ℝ)..2, g u ^ 2) * Real.sqrt (∫ u in (1 : ℝ)..2, g u ^ 4) := by
    have hg12' : ContinuousOn g (Set.Icc (1 : ℝ) 2) :=
      hgcont.mono (Set.Icc_subset_Icc (by norm_num) le_rfl)
    have h := Work.GM.S3.integral_mul_le_sqrt_mul_sqrt (a := (1 : ℝ)) (b := 2) (by norm_num)
      (f := g) (g := fun u : ℝ => g u ^ 2) hg12' (hg12'.pow 2)
      (fun u _ => hg0 u) (fun u _ => by positivity)
    have h1 : (∫ u in (1 : ℝ)..2, g u * g u ^ 2) = ∫ u in (1 : ℝ)..2, g u ^ 3 := by
      refine intervalIntegral.integral_congr fun u _ => ?_
      ring
    have h2 : (∫ u in (1 : ℝ)..2, (fun u : ℝ => g u ^ 2) u ^ 2)
        = ∫ u in (1 : ℝ)..2, g u ^ 4 := by
      refine intervalIntegral.integral_congr fun u _ => ?_
      ring
    rw [h1, h2] at h
    exact h
  have hM2 : 0 ≤ ∫ u in (1 : ℝ)..2, g u ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun u _ => by positivity)
  have hM4 : 0 ≤ ∫ u in (1 : ℝ)..2, g u ^ 4 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun u _ => by positivity)
  have h2' : ∫ u in (1 : ℝ)..2, g u ^ 2 ≤ M2 := by rw [hg]; exact h2
  have h4' : ∫ u in (1 : ℝ)..2, g u ^ 4 ≤ M4 := by rw [hg]; exact h4
  calc ∫ v in (1 / 2 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 3
      = (∫ v in (1 / 2 : ℝ)..1, g v ^ 3) + ∫ v in (1 : ℝ)..2, g v ^ 3 := hsplit
    _ ≤ 2 * ∫ v in (1 : ℝ)..2, g v ^ 3 := by linarith
    _ ≤ 2 * (Real.sqrt (∫ u in (1 : ℝ)..2, g u ^ 2)
          * Real.sqrt (∫ u in (1 : ℝ)..2, g u ^ 4)) := by linarith
    _ ≤ 2 * (Real.sqrt M2 * Real.sqrt M4) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul (Real.sqrt_le_sqrt h2') (Real.sqrt_le_sqrt h4') (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (M2 * M4) := by
        rw [Real.sqrt_mul (le_trans hM2 h2')]

/-- The number of elements of `fracSet N d` whose window `[f-κ,f+κ]` leaves `[1/2,2]`. -/
lemma fracSet_boundary_card {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) {κ : ℝ} (hκ : 0 ≤ κ) :
    (((fracSet N d).filter (fun f => ¬ ((1 / 2 : ℝ) ≤ f - κ ∧ f + κ ≤ 2))).card : ℝ)
      ≤ 2 * (1 + κ / ((d : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2))) := by
  classical
  have hsub1 : (fracSet N d).filter (fun f => f < 1 / 2 + κ)
      ⊆ (fracSet N d).filter (fun f => (1 / 2 : ℝ) ≤ f ∧ f ≤ 1 / 2 + κ) := by
    intro f hf
    obtain ⟨hfr, hflt⟩ := Finset.mem_filter.mp hf
    exact Finset.mem_filter.mpr ⟨hfr, (fracSet_bounds hN hfr).1, le_of_lt hflt⟩
  have hsub2 : (fracSet N d).filter (fun f => 2 - κ < f)
      ⊆ (fracSet N d).filter (fun f => 2 - κ ≤ f ∧ f ≤ 2) := by
    intro f hf
    obtain ⟨hfr, hflt⟩ := Finset.mem_filter.mp hf
    exact Finset.mem_filter.mpr ⟨hfr, le_of_lt hflt, (fracSet_bounds hN hfr).2⟩
  have hc1 : (((fracSet N d).filter (fun f => f < 1 / 2 + κ)).card : ℝ)
      ≤ κ / ((d : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)) + 1 := by
    calc (((fracSet N d).filter (fun f => f < 1 / 2 + κ)).card : ℝ)
        ≤ (((fracSet N d).filter (fun f => (1 / 2 : ℝ) ≤ f ∧ f ≤ 1 / 2 + κ)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub1
      _ ≤ ((1 / 2 + κ) - 1 / 2) / ((d : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)) + 1 :=
          fracSet_window_card hN hd (by linarith)
      _ = κ / ((d : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)) + 1 := by ring
  have hc2 : (((fracSet N d).filter (fun f => 2 - κ < f)).card : ℝ)
      ≤ κ / ((d : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)) + 1 := by
    calc (((fracSet N d).filter (fun f => 2 - κ < f)).card : ℝ)
        ≤ (((fracSet N d).filter (fun f => 2 - κ ≤ f ∧ f ≤ 2)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub2
      _ ≤ (2 - (2 - κ)) / ((d : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)) + 1 :=
          fracSet_window_card hN hd (by linarith)
      _ = κ / ((d : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)) + 1 := by ring
  have hsub : (fracSet N d).filter (fun f => ¬ ((1 / 2 : ℝ) ≤ f - κ ∧ f + κ ≤ 2))
      ⊆ (fracSet N d).filter (fun f => f < 1 / 2 + κ)
        ∪ (fracSet N d).filter (fun f => 2 - κ < f) := by
    intro f hf
    obtain ⟨hfr, hfn⟩ := Finset.mem_filter.mp hf
    simp only [not_and_or, not_le] at hfn
    rcases hfn with h | h
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hfr, by linarith⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hfr, by linarith⟩))
  calc (((fracSet N d).filter (fun f => ¬ ((1 / 2 : ℝ) ≤ f - κ ∧ f + κ ≤ 2))).card : ℝ)
      ≤ ((((fracSet N d).filter (fun f => f < 1 / 2 + κ))
          ∪ ((fracSet N d).filter (fun f => 2 - κ < f))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (((fracSet N d).filter (fun f => f < 1 / 2 + κ)).card : ℝ)
          + (((fracSet N d).filter (fun f => 2 - κ < f)).card : ℝ) := by
        have := Finset.card_union_le ((fracSet N d).filter (fun f => f < 1 / 2 + κ))
          ((fracSet N d).filter (fun f => 2 - κ < f))
        push_cast
        exact_mod_cast this
    _ ≤ 2 * (1 + κ / ((d : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2))) := by linarith

/-- `|W| ≤ T + 1` for a `1`-separated `W ⊆ [0,T]`. -/
lemma card_le_add_one {W : Finset ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hW : ∀ t ∈ W, t ∈ Set.Icc 0 T) (hsep : ∀ t ∈ W, ∀ s ∈ W, t ≠ s → 1 ≤ |t - s|) :
    (W.card : ℝ) ≤ T + 1 := by
  have h := Work.GM.S3.card_le_of_separated (W := W) (a := 0) (b := T) (δ := 1)
    (by norm_num) hT hW hsep
  simpa using h

/-- `|W|³ ≤ (2T+3)·|W|^{1/2} E(W)^{1/2}` for `W ⊆ [0,T]` (`1`-separated, `T ≥ 1`). -/
lemma card_pow_three_le (W : Finset ℝ) {T : ℝ} (hT : 1 ≤ T)
    (hW : ∀ t ∈ W, t ∈ Set.Icc 0 T) (hsep : ∀ t ∈ W, ∀ s ∈ W, t ≠ s → 1 ≤ |t - s|) :
    (W.card : ℝ) ^ 3 ≤ (2 * T + 3) *
      ((W.card : ℝ) ^ ((1 : ℝ) / 2) * (Submission.GM.energy W : ℝ) ^ ((1 : ℝ) / 2)) := by
  have key : (W.card : ℝ) ^ 3 ≤ (2 * T + 3) *
      (Real.sqrt (W.card : ℝ) * Real.sqrt (Submission.GM.energy W : ℝ)) := by
    rcases Finset.eq_empty_or_nonempty W with hem | hne
    · rw [hem]; simp
    · have hcW1 : 1 ≤ (W.card : ℝ) := by
        have : 1 ≤ W.card := Finset.card_pos.mpr hne
        exact_mod_cast this
      have hcW0 : 0 ≤ (W.card : ℝ) := by linarith
      have hE0 : 0 ≤ (Submission.GM.energy W : ℝ) := by positivity
      have h1 : (W.card : ℝ) ^ 4 ≤ (2 * T + 3) * (Submission.GM.energy W : ℝ) :=
        energy_ge_card_pow_four W (by linarith) hW
      have h2 : (W.card : ℝ) ≤ T + 1 := card_le_add_one (by linarith) hW hsep
      have h4 : (W.card : ℝ) ^ 2 ≤ (W.card : ℝ) * (2 * T + 3) := by nlinarith
      have h3 : (W.card : ℝ) ^ 6 ≤ (2 * T + 3) ^ 2
          * ((W.card : ℝ) * (Submission.GM.energy W : ℝ)) := by
        have h5 : (W.card : ℝ) ^ 4 * (W.card : ℝ) ^ 2
            ≤ ((2 * T + 3) * (Submission.GM.energy W : ℝ)) * ((W.card : ℝ) * (2 * T + 3)) :=
          mul_le_mul h1 h4 (by positivity) (by positivity)
        nlinarith [h5]
      have h6 : ((2 * T + 3) * (Real.sqrt (W.card : ℝ) * Real.sqrt (Submission.GM.energy W : ℝ)))
          ^ 2 = (2 * T + 3) ^ 2 * ((W.card : ℝ) * (Submission.GM.energy W : ℝ)) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hcW0, Real.sq_sqrt hE0]
      have h5 : ((W.card : ℝ) ^ 3) ^ 2
          ≤ ((2 * T + 3) * (Real.sqrt (W.card : ℝ)
              * Real.sqrt (Submission.GM.energy W : ℝ))) ^ 2 := by
        rw [h6, show ((W.card : ℝ) ^ 3) ^ 2 = (W.card : ℝ) ^ 6 by ring]
        exact h3
      have h7 := sq_le_sq.mp h5
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at h7
      exact h7
  calc (W.card : ℝ) ^ 3
      ≤ (2 * T + 3) * (Real.sqrt (W.card : ℝ) * Real.sqrt (Submission.GM.energy W : ℝ)) := key
    _ = (2 * T + 3) * ((W.card : ℝ) ^ ((1 : ℝ) / 2)
          * (Submission.GM.energy W : ℝ) ^ ((1 : ℝ) / 2)) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-- The `L³` bound `∫_{1/2}^2 ‖Rfun W‖³ ≤ 2CR·|W|^{1/2}E(W)^{1/2}` from the `L²` and `L⁴`
hypotheses. -/
lemma integral_bound {W : Finset ℝ} {CR : ℝ} (hCR : 0 < CR)
    (h2 : ∫ v in (1 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 2 ≤ CR * (W.card : ℝ))
    (h4 : ∫ v in (1 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 4
      ≤ CR * (Submission.GM.energy W : ℝ)) :
    ∫ v in (1 / 2 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 3
      ≤ 2 * CR * ((W.card : ℝ) ^ ((1 : ℝ) / 2)
          * (Submission.GM.energy W : ℝ) ^ ((1 : ℝ) / 2)) := by
  have hcW0 : 0 ≤ (W.card : ℝ) := by positivity
  have h := integral_half_two_cube_le W (M2 := CR * (W.card : ℝ))
    (M4 := CR * (Submission.GM.energy W : ℝ)) h2 h4
  have hsq : Real.sqrt ((CR * (W.card : ℝ)) * (CR * (Submission.GM.energy W : ℝ)))
      = CR * (Real.sqrt (W.card : ℝ) * Real.sqrt (Submission.GM.energy W : ℝ)) := by
    rw [show CR * (W.card : ℝ) * (CR * (Submission.GM.energy W : ℝ))
        = CR ^ 2 * ((W.card : ℝ) * (Submission.GM.energy W : ℝ)) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (le_of_lt hCR), Real.sqrt_mul hcW0]
  rw [hsq] at h
  calc ∫ v in (1 / 2 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 3
      ≤ 2 * (CR * (Real.sqrt (W.card : ℝ) * Real.sqrt (Submission.GM.energy W : ℝ))) := h
    _ = 2 * CR * ((W.card : ℝ) ^ ((1 : ℝ) / 2)
          * (Submission.GM.energy W : ℝ) ^ ((1 : ℝ) / 2)) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]; ring

/-- The core window estimate: the sum over `f ∈ fracSet N d` of the cube of the integral of
`‖Rfun W‖` over `[f-κ, f+κ]` (`κ = K/T`) is bounded by `(2κ)²(1+2κ/δ)` times the `L³` mass on
`[1/2,2]`, plus a boundary contribution `2(1+κ/δ)(2κ|W|)³` for the fractions whose window leaves
`[1/2,2]` (here `δ = d²/(4N²)`). -/
lemma sum_window_pow3_le {N dd : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ dd) {W : Finset ℝ} {T K : ℝ}
    (hT : 1 ≤ T) (hK : 1 ≤ K) :
    (∑ f ∈ fracSet N dd, (∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖) ^ 3)
      ≤ (2 * (K / T)) ^ 2 * (1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))
            * (∫ v in (1 / 2 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 3)
        + 2 * (1 + (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))
            * (2 * (K / T) * (W.card : ℝ)) ^ 3 := by
  classical
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hκ0 : 0 ≤ K / T := div_nonneg (by linarith) (le_of_lt hTpos)
  have hgcont : ContinuousOn (fun v : ℝ => ‖Submission.GM.Rfun W v‖) (Set.Icc (1 / 2 : ℝ) 2) :=
    continuousOn_norm_Rfun W
  have hg3cont : ContinuousOn (fun v : ℝ => ‖Submission.GM.Rfun W v‖ ^ 3)
      (Set.Icc (1 / 2 : ℝ) 2) := hgcont.pow 3
  set cW : ℝ := (W.card : ℝ) with hcW
  have hnorm_le : ∀ v : ℝ, ‖Submission.GM.Rfun W v‖ ≤ cW := by
    intro v; rw [hcW]; exact Work.GM.S3.Rfun_norm_le_card W v
  have hsplit : (∑ f ∈ fracSet N dd,
        (∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖) ^ 3)
      = (∑ f ∈ (fracSet N dd).filter
            (fun f : ℝ => (1 / 2 : ℝ) ≤ f - K / T ∧ f + K / T ≤ 2),
            (∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖) ^ 3)
        + (∑ f ∈ (fracSet N dd).filter
            (fun f : ℝ => ¬ ((1 / 2 : ℝ) ≤ f - K / T ∧ f + K / T ≤ 2)),
            (∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖) ^ 3) := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun f hf => ?_
    by_cases hab : (1 / 2 : ℝ) ≤ f - K / T ∧ f + K / T ≤ 2
    · rw [if_pos hab, if_neg (not_not_intro hab)]; ring
    · rw [if_neg hab, if_pos hab]; ring
  have hmain : (∑ f ∈ (fracSet N dd).filter
        (fun f : ℝ => (1 / 2 : ℝ) ≤ f - K / T ∧ f + K / T ≤ 2),
        (∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖) ^ 3)
      ≤ (2 * (K / T)) ^ 2 * (1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))
          * (∫ v in (1 / 2 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 3) := by
    have h1 : ∀ f ∈ (fracSet N dd).filter
          (fun f : ℝ => (1 / 2 : ℝ) ≤ f - K / T ∧ f + K / T ≤ 2),
        (∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖) ^ 3
          ≤ (2 * (K / T)) ^ 2 * ∫ x in (1 / 2 : ℝ)..2,
              (if |x - f| ≤ K / T then ‖Submission.GM.Rfun W x‖ ^ 3 else 0) := by
      intro f hf
      obtain ⟨-, hP1, hP2⟩ := Finset.mem_filter.mp hf
      have hcube := Work.GM.Energy.EnergyCore.integral_cube_le
        (a := f - K / T) (b := f + K / T) (by linarith)
        (hgcont.mono (Set.Icc_subset_Icc hP1 hP2)) (fun x _ => norm_nonneg _)
      have hid : (∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖ ^ 3)
          = ∫ x in (1 / 2 : ℝ)..2,
              (if |x - f| ≤ K / T then ‖Submission.GM.Rfun W x‖ ^ 3 else 0) := by
        rw [← Work.GM.Energy.EnergyCore.integral_indicator_Icc (a := (1 / 2 : ℝ)) (b := 2)
          (c := f - K / T) (d := f + K / T) hP1 (by linarith) hP2 hg3cont]
        refine intervalIntegral.integral_congr fun x hx => ?_
        by_cases h : |x - f| ≤ K / T
        · have h' : f - K / T ≤ x ∧ x ≤ f + K / T := by
            rw [abs_le] at h; exact ⟨by linarith [h.1], by linarith [h.2]⟩
          rw [if_pos h', if_pos h]
        · have h' : ¬ (f - K / T ≤ x ∧ x ≤ f + K / T) := by
            intro hc; exact h (by rw [abs_le]; exact ⟨by linarith [hc.1], by linarith [hc.2]⟩)
          rw [if_neg h', if_neg h]
      calc (∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖) ^ 3
          ≤ ((f + K / T) - (f - K / T)) ^ 2
              * ∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖ ^ 3 := hcube
        _ = (2 * (K / T)) ^ 2
              * ∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖ ^ 3 := by ring_nf
        _ = (2 * (K / T)) ^ 2 * ∫ x in (1 / 2 : ℝ)..2,
              (if |x - f| ≤ K / T then ‖Submission.GM.Rfun W x‖ ^ 3 else 0) := by rw [hid]
    calc (∑ f ∈ (fracSet N dd).filter
          (fun f : ℝ => (1 / 2 : ℝ) ≤ f - K / T ∧ f + K / T ≤ 2),
          (∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖) ^ 3)
        ≤ ∑ f ∈ (fracSet N dd).filter
            (fun f : ℝ => (1 / 2 : ℝ) ≤ f - K / T ∧ f + K / T ≤ 2),
            (2 * (K / T)) ^ 2 * ∫ x in (1 / 2 : ℝ)..2,
              (if |x - f| ≤ K / T then ‖Submission.GM.Rfun W x‖ ^ 3 else 0) :=
          Finset.sum_le_sum h1
      _ = (2 * (K / T)) ^ 2 * ∑ f ∈ (fracSet N dd).filter
            (fun f : ℝ => (1 / 2 : ℝ) ≤ f - K / T ∧ f + K / T ≤ 2),
            ∫ x in (1 / 2 : ℝ)..2,
              (if |x - f| ≤ K / T then ‖Submission.GM.Rfun W x‖ ^ 3 else 0) := by
          rw [Finset.mul_sum]
      _ ≤ (2 * (K / T)) ^ 2 * (1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))
          * (∫ v in (1 / 2 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 3) := by
          have hstep : (∑ f ∈ fracSet N dd, ∫ x in (1 / 2 : ℝ)..2,
                (if |x - f| ≤ K / T then ‖Submission.GM.Rfun W x‖ ^ 3 else 0))
              ≤ (1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))
                  * (∫ v in (1 / 2 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 3) := by
            exact Work.GM.Energy.EnergyCore.sum_window_le
              (Fr := fracSet N dd) (c := (1 / 2 : ℝ)) (d := 2)
              (C := 1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))
              (κ := K / T) (h := fun x : ℝ => ‖Submission.GM.Rfun W x‖ ^ 3)
              (by norm_num) (by positivity) hg3cont (fun x _ => by positivity) (fun x hx => by
                have hbd := fracSet_ball_card (N := N) (d := dd) hN hd (κ := K / T) hκ0 (x := x)
                rw [show (1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))
                    = 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)) + 1 from by ring]
                exact hbd)
          calc (2 * (K / T)) ^ 2 * (∑ f ∈ (fracSet N dd).filter
                (fun f : ℝ => (1 / 2 : ℝ) ≤ f - K / T ∧ f + K / T ≤ 2),
                ∫ x in (1 / 2 : ℝ)..2,
                  (if |x - f| ≤ K / T then ‖Submission.GM.Rfun W x‖ ^ 3 else 0))
              ≤ (2 * (K / T)) ^ 2 * (∑ f ∈ fracSet N dd, ∫ x in (1 / 2 : ℝ)..2,
                  (if |x - f| ≤ K / T then ‖Submission.GM.Rfun W x‖ ^ 3 else 0)) :=
                mul_le_mul_of_nonneg_left
                  (Finset.sum_le_sum_of_subset_of_nonneg
                    (fun f hf => Finset.mem_of_mem_filter f hf)
                    (fun f hf _ => intervalIntegral.integral_nonneg (by norm_num)
                      (fun x _ => by positivity)))
                  (by positivity)
            _ ≤ (2 * (K / T)) ^ 2 * ((1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))
                  * (∫ v in (1 / 2 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 3)) :=
                mul_le_mul_of_nonneg_left hstep (by positivity)
            _ = (2 * (K / T)) ^ 2 * (1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))
                  * (∫ v in (1 / 2 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 3) := by ring
  have hbnd : (∑ f ∈ (fracSet N dd).filter
        (fun f : ℝ => ¬ ((1 / 2 : ℝ) ≤ f - K / T ∧ f + K / T ≤ 2)),
        (∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖) ^ 3)
      ≤ 2 * (1 + (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2))) * (2 * (K / T) * cW) ^ 3 := by
    have h1 : ∀ f ∈ (fracSet N dd).filter
          (fun f : ℝ => ¬ ((1 / 2 : ℝ) ≤ f - K / T ∧ f + K / T ≤ 2)),
        (∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖) ^ 3
          ≤ (2 * (K / T) * cW) ^ 3 := by
      intro f hf
      have hint : ‖∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖‖
          ≤ cW * |(f + K / T) - (f - K / T)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (C := cW) (fun x _ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
          exact hnorm_le x)
      have hge : (∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖)
          ≤ 2 * (K / T) * cW := by
        have h2 : cW * |(f + K / T) - (f - K / T)| = cW * (2 * (K / T)) := by
          rw [show (f + K / T) - (f - K / T) = 2 * (K / T) by ring,
            abs_of_nonneg (by positivity)]
        rw [h2] at hint
        have habs : |∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖|
            ≤ cW * (2 * (K / T)) := by
          rw [← Real.norm_eq_abs]; exact hint
        linarith [le_abs_self (∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖), habs]
      have h3 : 0 ≤ ∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖ :=
        intervalIntegral.integral_nonneg (by linarith) (fun x _ => norm_nonneg _)
      exact pow_le_pow_left₀ h3 hge 3
    calc (∑ f ∈ (fracSet N dd).filter
          (fun f : ℝ => ¬ ((1 / 2 : ℝ) ≤ f - K / T ∧ f + K / T ≤ 2)),
          (∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖) ^ 3)
        ≤ ∑ f ∈ (fracSet N dd).filter
            (fun f : ℝ => ¬ ((1 / 2 : ℝ) ≤ f - K / T ∧ f + K / T ≤ 2)),
            (2 * (K / T) * cW) ^ 3 := Finset.sum_le_sum h1
      _ = (((fracSet N dd).filter
            (fun f : ℝ => ¬ ((1 / 2 : ℝ) ≤ f - K / T ∧ f + K / T ≤ 2))).card : ℝ)
            * (2 * (K / T) * cW) ^ 3 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (1 + (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2))) * (2 * (K / T) * cW) ^ 3 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact fracSet_boundary_card (N := N) (d := dd) hN hd (κ := K / T) hκ0
  rw [hsplit]
  linarith [hmain, hbnd]

section Reindex

/-- The gcd-decomposition of the double sum over `[N,2N]²`: summing over the pairs with
`gcd n₁ n₂ ≤ D` is the same as summing over `d ≤ D` the fractions with `gcd = d`. -/
theorem gcd_sum_reindex {N : ℕ} (hN : 1 ≤ N) (D : ℝ) (hD : 1 ≤ D) (g : ℝ → ℝ) :
    (∑ n1 ∈ Finset.Icc N (2 * N),
        ∑ n2 ∈ (Finset.Icc N (2 * N)).filter (fun n2 => (Nat.gcd n1 n2 : ℝ) ≤ D),
          g ((n1 : ℝ) / (n2 : ℝ)))
      = ∑ d ∈ Finset.Icc 1 ⌊D⌋₊, ∑ f ∈ fracSet N d, g f := by
  classical
  have hmem : ∀ n ∈ Finset.Icc N (2 * N), 1 ≤ n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    omega
  have h1 : (∑ n1 ∈ Finset.Icc N (2 * N),
        ∑ n2 ∈ (Finset.Icc N (2 * N)).filter (fun n2 => (Nat.gcd n1 n2 : ℝ) ≤ D),
          g ((n1 : ℝ) / (n2 : ℝ)))
      = ∑ p ∈ ((Finset.Icc N (2 * N)).product (Finset.Icc N (2 * N))).filter
            (fun p : ℕ × ℕ => (Nat.gcd p.1 p.2 : ℝ) ≤ D),
          g ((p.1 : ℝ) / (p.2 : ℝ)) := by
    have hl : (∑ n1 ∈ Finset.Icc N (2 * N),
          ∑ n2 ∈ (Finset.Icc N (2 * N)).filter (fun n2 => (Nat.gcd n1 n2 : ℝ) ≤ D),
            g ((n1 : ℝ) / (n2 : ℝ)))
        = ∑ n1 ∈ Finset.Icc N (2 * N), ∑ n2 ∈ Finset.Icc N (2 * N),
            (if (Nat.gcd n1 n2 : ℝ) ≤ D then g ((n1 : ℝ) / (n2 : ℝ)) else 0) := by
      refine Finset.sum_congr rfl fun n1 hn1 => ?_
      rw [Finset.sum_filter]
    have hr : (∑ p ∈ ((Finset.Icc N (2 * N)).product (Finset.Icc N (2 * N))).filter
            (fun p : ℕ × ℕ => (Nat.gcd p.1 p.2 : ℝ) ≤ D),
          g ((p.1 : ℝ) / (p.2 : ℝ)))
        = ∑ n1 ∈ Finset.Icc N (2 * N), ∑ n2 ∈ Finset.Icc N (2 * N),
            (if (Nat.gcd n1 n2 : ℝ) ≤ D then g ((n1 : ℝ) / (n2 : ℝ)) else 0) := by
      rw [Finset.sum_filter]
      exact Finset.sum_product _ _ _
    rw [hl, hr]
  rw [h1]
  have hmapsto : ∀ p ∈ ((Finset.Icc N (2 * N)).product (Finset.Icc N (2 * N))).filter
        (fun p : ℕ × ℕ => (Nat.gcd p.1 p.2 : ℝ) ≤ D),
      Nat.gcd p.1 p.2 ∈ Finset.Icc 1 ⌊D⌋₊ := by
    intro p hp
    obtain ⟨hp1, hple⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpa, hpb⟩ := Finset.mem_product.mp hp1
    refine Finset.mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left p.2 ?_, Nat.le_floor hple⟩
    have := hmem p.1 hpa
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmapsto
    (fun p : ℕ × ℕ => g ((p.1 : ℝ) / (p.2 : ℝ)))]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hfloor : ((⌊D⌋₊ : ℕ) : ℝ) ≤ D := Nat.floor_le (le_trans zero_le_one hD)
  have hdD : (d : ℝ) ≤ D := by
    have : d ≤ ⌊D⌋₊ := (Finset.mem_Icc.mp hd).2
    exact le_trans (by exact_mod_cast this) hfloor
  have hfil : (((Finset.Icc N (2 * N)).product (Finset.Icc N (2 * N))).filter
          (fun p : ℕ × ℕ => (Nat.gcd p.1 p.2 : ℝ) ≤ D)).filter
        (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 = d)
      = ((Finset.Icc N (2 * N)).product (Finset.Icc N (2 * N))).filter
          (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 = d) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hp, -⟩, hpd⟩; exact ⟨hp, hpd⟩
    · rintro ⟨hp, hpd⟩
      exact ⟨⟨hp, by rw [hpd]; exact hdD⟩, hpd⟩
  rw [hfil]
  have hinj : Set.InjOn (fun p : ℕ × ℕ => (p.1 : ℝ) / (p.2 : ℝ))
      ↑(((Finset.Icc N (2 * N)).product (Finset.Icc N (2 * N))).filter
          (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 = d)) := by
    intro p hp q hq hpq
    have hp' : p ∈ ((Finset.Icc N (2 * N)).product (Finset.Icc N (2 * N))).filter
        (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 = d) := hp
    have hq' : q ∈ ((Finset.Icc N (2 * N)).product (Finset.Icc N (2 * N))).filter
        (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 = d) := hq
    obtain ⟨hp1, hpg⟩ := Finset.mem_filter.mp hp'
    obtain ⟨hq1, hqg⟩ := Finset.mem_filter.mp hq'
    obtain ⟨hpa, hpb⟩ := Finset.mem_product.mp hp1
    obtain ⟨hqa, hqb⟩ := Finset.mem_product.mp hq1
    have h1p : 0 < p.1 := by have := hmem p.1 hpa; omega
    have h2p : 0 < p.2 := by have := hmem p.2 hpb; omega
    have h1q : 0 < q.1 := by have := hmem q.1 hqa; omega
    have h2q : 0 < q.2 := by have := hmem q.2 hqb; omega
    obtain ⟨e1, e2⟩ := ratio_inj_gcd h1p h2p h1q h2q hpg hqg hpq
    exact Prod.ext e1 e2
  exact (Finset.sum_image hinj).symm

/-- The total number of fractions over all `d ≤ D` is at most `(N+1)²`. -/
theorem sum_fracSet_card_le {N : ℕ} (hN : 1 ≤ N) (D : ℝ) (hD : 1 ≤ D) :
    (∑ d ∈ Finset.Icc 1 ⌊D⌋₊, (fracSet N d).card) ≤ (N + 1) ^ 2 := by
  classical
  have hcardI : (Finset.Icc N (2 * N)).card = N + 1 := by
    rw [Nat.card_Icc]; omega
  have h := gcd_sum_reindex hN D hD (fun _ : ℝ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have hle : (∑ x ∈ Finset.Icc N (2 * N),
        ((Finset.Icc N (2 * N)).filter (fun n2 => (Nat.gcd x n2 : ℝ) ≤ D)).card)
      ≤ (N + 1) ^ 2 := by
    calc (∑ x ∈ Finset.Icc N (2 * N),
          ((Finset.Icc N (2 * N)).filter (fun n2 => (Nat.gcd x n2 : ℝ) ≤ D)).card)
        ≤ ∑ x ∈ Finset.Icc N (2 * N), (Finset.Icc N (2 * N)).card :=
          Finset.sum_le_sum fun x _ => Finset.card_filter_le _ _
      _ = (Finset.Icc N (2 * N)).card * (Finset.Icc N (2 * N)).card := by
          rw [Finset.sum_const, smul_eq_mul]
      _ = (N + 1) ^ 2 := by rw [hcardI]; ring
  have h2 : ((∑ d ∈ Finset.Icc 1 ⌊D⌋₊, (fracSet N d).card : ℕ) : ℝ) ≤ ((N : ℝ) + 1) ^ 2 := by
    rw [Nat.cast_sum]
    rw [← h]
    calc (∑ x ∈ Finset.Icc N (2 * N),
            ((↑((Finset.Icc N (2 * N)).filter (fun n2 => (Nat.gcd x n2 : ℝ) ≤ D)).card : ℕ) : ℝ))
        ≤ (((N + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hle
      _ = ((N : ℝ) + 1) ^ 2 := by push_cast; ring
  have h3 : ((∑ d ∈ Finset.Icc 1 ⌊D⌋₊, (fracSet N d).card : ℕ) : ℝ)
      ≤ (((N + 1) ^ 2 : ℕ) : ℝ) := by
    rw [show (((N + 1) ^ 2 : ℕ) : ℝ) = ((N : ℝ) + 1) ^ 2 by push_cast; ring]
    exact h2
  exact_mod_cast h3

end Reindex

end Work.GM.Energy.EnergyCore
