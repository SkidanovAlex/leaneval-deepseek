import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixR.LatGreen.MadelungDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.TailMajorant`

The long-time (Fourier) tail `rhoZ t = 2 Σ_{j≥1} e^{-4π²t j²}` of the Ewald splitting of the
`ℤ³` lattice Green's function.  For `t ≥ etaZ = 1/32` this tail is at most `3/4`, and the cubic
combination `3 ρ + 3 ρ² + ρ³` is integrable on `(1/32, ∞)` with integral at most `1/14`.

The estimates are deliberately coarse.  Since `π > 3.14`, the splitting parameter satisfies
`4π² etaZ = π²/8 > 6/5`, so the Gaussian series `SZ` is dominated by `Σ_j e^{-(6/5)(j+1)²}`, which
is bounded by the geometric majorant `e^{-c}/(1-e^{-3c})`; and
`rhoZ t ≤ e^{-4π²(t-etaZ)} rhoZ etaZ`, which is small enough that `rhoZ^k` has integrals
`rhoZ(etaZ)^k / (k·4π²)`.
-/

set_option maxHeartbeats 1000000

noncomputable section

open scoped Real BigOperators
open MeasureTheory Set

namespace Work.BoseFixR.LatGreen

/-! ### Elementary estimates -/

/-- Elementary: `j ≤ (j+1)²` (as reals). -/
lemma nat_cast_le_succ_sq (j : ℕ) : (j : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by
  have h' : ((j * j : ℕ) : ℝ) = (j : ℝ) * (j : ℝ) := by push_cast; ring
  have h2 : (j : ℝ) ≤ ((j * j : ℕ) : ℝ) := by exact_mod_cast Nat.le_mul_self j
  have hjj : (j : ℝ) ≤ (j : ℝ) * (j : ℝ) := by rw [← h']; exact h2
  have hexp : ((j : ℝ) + 1) ^ 2 = (j : ℝ) * (j : ℝ) + 2 * (j : ℝ) + 1 := by ring
  rw [hexp]
  linarith [hjj]

/-- The Gaussian series defining `SZ` is summable for `t > 0`. -/
lemma summable_SZ_gauss {t : ℝ} (ht : 0 < t) :
    Summable fun j : ℕ => Real.exp (-(4 * Real.pi ^ 2 * t) * ((j : ℝ) + 1) ^ 2) := by
  have hc : -(4 * Real.pi ^ 2 * t) < 0 := by
    have : 0 < 4 * Real.pi ^ 2 * t := by positivity
    linarith
  refine Real.summable_exp_nat_mul_of_ge (c := -(4 * Real.pi ^ 2 * t)) hc
    (f := fun j : ℕ => ((j : ℝ) + 1) ^ 2) ?_
  intro j
  exact nat_cast_le_succ_sq j

/-- `rhoZ` is nonnegative. -/
lemma rhoZ_nonneg (t : ℝ) : 0 ≤ rhoZ t := by
  rw [rhoZ, SZ]
  exact mul_nonneg (by norm_num) (tsum_nonneg fun j => Real.exp_nonneg _)

/-- Geometric majorant for the Gaussian series `Σ_{j} e^{-c (j+1)²}`. -/
lemma exp_geom_majorant {c : ℝ} (hc : 0 < c) :
    (∑' j : ℕ, Real.exp (-c * ((j : ℝ) + 1) ^ 2))
      ≤ Real.exp (-c) / (1 - Real.exp (-3 * c)) := by
  set r : ℝ := Real.exp (-3 * c) with hr
  have hr1 : r < 1 := by rw [hr]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hr0 : 0 ≤ r := by rw [hr]; exact Real.exp_nonneg _
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hg : Summable fun j : ℕ => Real.exp (-c) * r ^ j :=
    Summable.mul_left _ (summable_geometric_of_norm_lt_one hnorm)
  have hle : ∀ j : ℕ, Real.exp (-c * ((j : ℝ) + 1) ^ 2) ≤ Real.exp (-c) * r ^ j := by
    intro j
    rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hj : (j : ℝ) ≤ (j : ℝ) ^ 2 := by
      have h : (j : ℝ) ≤ ((j * j : ℕ) : ℝ) := by exact_mod_cast Nat.le_mul_self j
      simpa [Nat.cast_mul, pow_two] using h
    have hcj : 0 ≤ c * ((j : ℝ) ^ 2 - (j : ℝ)) := mul_nonneg hc.le (by linarith)
    nlinarith [hcj]
  have hsum : Summable fun j : ℕ => Real.exp (-c * ((j : ℝ) + 1) ^ 2) :=
    Summable.of_nonneg_of_le (fun j => Real.exp_nonneg _) hle hg
  calc (∑' j : ℕ, Real.exp (-c * ((j : ℝ) + 1) ^ 2))
      ≤ ∑' j : ℕ, Real.exp (-c) * r ^ j := Summable.tsum_le_tsum hle hsum hg
    _ = Real.exp (-c) * (1 - r)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hnorm]
    _ = Real.exp (-c) / (1 - Real.exp (-3 * c)) := by rw [hr, div_eq_mul_inv]

/-- `e^{-6/5} ≤ 151/500` (with room to spare). -/
lemma exp_neg_six_fifths : Real.exp (-((6 : ℝ) / 5)) ≤ 151 / 500 := by
  have hkey : (500 : ℝ) / 151
      ≤ ∑ i ∈ Finset.range 6, ((6 : ℝ) / 5) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hsum := Real.sum_le_exp_of_nonneg (x := (6 : ℝ) / 5) (by norm_num) 6
  have h : (500 : ℝ) / 151 ≤ Real.exp ((6 : ℝ) / 5) := le_trans hkey hsum
  rw [Real.exp_neg]
  calc (Real.exp ((6 : ℝ) / 5))⁻¹ ≤ ((500 : ℝ) / 151)⁻¹ := by
        rw [inv_le_inv₀ (Real.exp_pos _) (by norm_num)]; exact h
    _ = 151 / 500 := by norm_num

/-- `e^{-18/5} ≤ 7/250` (with room to spare). -/
lemma exp_neg_eighteen_fifths : Real.exp (-((18 : ℝ) / 5)) ≤ 7 / 250 := by
  have hkey : (250 : ℝ) / 7
      ≤ ∑ i ∈ Finset.range 10, ((18 : ℝ) / 5) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hsum := Real.sum_le_exp_of_nonneg (x := (18 : ℝ) / 5) (by norm_num) 10
  have h : (250 : ℝ) / 7 ≤ Real.exp ((18 : ℝ) / 5) := le_trans hkey hsum
  rw [Real.exp_neg]
  calc (Real.exp ((18 : ℝ) / 5))⁻¹ ≤ ((250 : ℝ) / 7)⁻¹ := by
        rw [inv_le_inv₀ (Real.exp_pos _) (by norm_num)]; exact h
    _ = 7 / 250 := by norm_num

/-- `π²/8 ≥ 6/5`. -/
lemma pi_sq_div_eight_ge : ((6 : ℝ) / 5) ≤ Real.pi ^ 2 / 8 := by
  have h := Real.pi_gt_d2
  nlinarith [Real.pi_pos]

/-- `4 π² etaZ = π²/8`. -/
lemma four_pi_sq_etaZ : (4 : ℝ) * Real.pi ^ 2 * etaZ = Real.pi ^ 2 / 8 := by
  rw [etaZ]; ring

/-- The Fourier tail at the splitting time is small: `SZ etaZ ≤ 8/25`. -/
lemma SZ_etaZ_le : SZ etaZ ≤ 8 / 25 := by
  have hterm : ∀ j : ℕ,
      Real.exp (-(4 * Real.pi ^ 2 * etaZ) * ((j : ℝ) + 1) ^ 2)
        ≤ Real.exp (-((6 : ℝ) / 5) * ((j : ℝ) + 1) ^ 2) := by
    intro j
    rw [four_pi_sq_etaZ]
    apply Real.exp_le_exp.mpr
    have hx : (0 : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := sq_nonneg _
    have hprod : 0 ≤ (Real.pi ^ 2 / 8 - (6 : ℝ) / 5) * ((j : ℝ) + 1) ^ 2 :=
      mul_nonneg (by linarith [pi_sq_div_eight_ge]) hx
    nlinarith [hprod]
  have hsum6 : Summable fun j : ℕ => Real.exp (-((6 : ℝ) / 5) * ((j : ℝ) + 1) ^ 2) :=
    Real.summable_exp_nat_mul_of_ge (c := -((6 : ℝ) / 5)) (by norm_num)
      (f := fun j : ℕ => ((j : ℝ) + 1) ^ 2)
      (fun j => nat_cast_le_succ_sq j)
  have h2 := exp_geom_majorant (c := (6 : ℝ) / 5) (by norm_num)
  have h3 : Real.exp (-((6 : ℝ) / 5)) / (1 - Real.exp (-3 * ((6 : ℝ) / 5))) ≤ 8 / 25 := by
    have h1' := exp_neg_six_fifths
    have h2' := exp_neg_eighteen_fifths
    have hpos : 0 < 1 - Real.exp (-((18 : ℝ) / 5)) := by
      have hlt : Real.exp (-((18 : ℝ) / 5)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
      linarith
    rw [show -3 * ((6 : ℝ) / 5) = -((18 : ℝ) / 5) by ring]
    rw [div_le_iff₀ hpos]
    nlinarith [h1', h2']
  rw [SZ]
  exact le_trans
    (Summable.tsum_le_tsum hterm (summable_SZ_gauss (by norm_num [etaZ])) hsum6)
    (le_trans h2 h3)

/-- The Fourier tail at the splitting time: `rhoZ etaZ ≤ 16/25`. -/
lemma rhoZ_etaZ_le : rhoZ etaZ ≤ 16 / 25 := by
  rw [rhoZ]
  linarith [SZ_etaZ_le]

/-- The tail decays at least like `e^{-4π²(t-η)}`: for `0 < η ≤ t`,
`SZ t ≤ e^{-4π²(t-η)} SZ η`. -/
lemma SZDecay {t η : ℝ} (hη : 0 < η) (ht : η ≤ t) :
    SZ t ≤ Real.exp (-(4 * Real.pi ^ 2 * (t - η))) * SZ η := by
  have hterm : ∀ j : ℕ,
      Real.exp (-(4 * Real.pi ^ 2 * t) * ((j : ℝ) + 1) ^ 2)
        ≤ Real.exp (-(4 * Real.pi ^ 2 * (t - η)))
            * Real.exp (-(4 * Real.pi ^ 2 * η) * ((j : ℝ) + 1) ^ 2) := by
    intro j
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hx : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      nlinarith
    have hdiff : -(4 * Real.pi ^ 2 * t) * ((j : ℝ) + 1) ^ 2
        = -(4 * Real.pi ^ 2 * (t - η)) + (-(4 * Real.pi ^ 2 * η) * ((j : ℝ) + 1) ^ 2)
          - 4 * Real.pi ^ 2 * ((t - η) * (((j : ℝ) + 1) ^ 2 - 1)) := by
      ring
    have hnn : 0 ≤ 4 * Real.pi ^ 2 * ((t - η) * (((j : ℝ) + 1) ^ 2 - 1)) := by
      refine mul_nonneg (by positivity) (mul_nonneg (by linarith) ?_)
      linarith
    linarith [hdiff, hnn]
  have hsumη : Summable fun j : ℕ =>
      Real.exp (-(4 * Real.pi ^ 2 * η) * ((j : ℝ) + 1) ^ 2) := summable_SZ_gauss hη
  have hsum : Summable fun j : ℕ =>
      Real.exp (-(4 * Real.pi ^ 2 * (t - η)))
        * Real.exp (-(4 * Real.pi ^ 2 * η) * ((j : ℝ) + 1) ^ 2) :=
    Summable.mul_left _ hsumη
  rw [SZ]
  calc (∑' j : ℕ, Real.exp (-(4 * Real.pi ^ 2 * t) * ((j : ℝ) + 1) ^ 2))
      ≤ ∑' j : ℕ, Real.exp (-(4 * Real.pi ^ 2 * (t - η)))
            * Real.exp (-(4 * Real.pi ^ 2 * η) * ((j : ℝ) + 1) ^ 2) :=
        Summable.tsum_le_tsum hterm (summable_SZ_gauss (by linarith)) hsum
    _ = Real.exp (-(4 * Real.pi ^ 2 * (t - η))) * SZ η := by
        rw [tsum_mul_left, SZ]

/-- The shifted exponential is integrable on a half line. -/
lemma integrableOn_exp_shift {b η : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => Real.exp (-(b * (t - η)))) (Set.Ioi η) := by
  have h0 : IntegrableOn (fun t : ℝ => Real.exp ((-b) * t)) (Set.Ioi η) :=
    integrableOn_exp_mul_Ioi (show (-b) < 0 by linarith) η
  have h1 : Integrable (fun t : ℝ => Real.exp (b * η) * Real.exp ((-b) * t))
      (volume.restrict (Set.Ioi η)) :=
    h0.integrable.const_mul (Real.exp (b * η))
  refine h1.congr ?_
  filter_upwards with t
  rw [← Real.exp_add]
  congr 1
  ring

/-- `∫_{t > η} e^{-b (t-η)} = 1/b` for `b > 0`. -/
lemma integral_exp_shift {b η : ℝ} (hb : 0 < b) :
    ∫ t in Set.Ioi η, Real.exp (-(b * (t - η))) = 1 / b := by
  have hcongr : ∀ t : ℝ,
      Real.exp (-(b * (t - η))) = Real.exp (b * η) * Real.exp ((-b) * t) := by
    intro t
    rw [← Real.exp_add]
    congr 1
    ring
  calc ∫ t in Set.Ioi η, Real.exp (-(b * (t - η)))
      = ∫ t in Set.Ioi η, Real.exp (b * η) * Real.exp ((-b) * t) := by
        apply integral_congr_ae
        filter_upwards with t
        exact hcongr t
    _ = Real.exp (b * η) * ∫ t in Set.Ioi η, Real.exp ((-b) * t) := integral_const_mul _ _
    _ = Real.exp (b * η) * (-Real.exp ((-b) * η) / (-b)) := by
        rw [integral_exp_mul_Ioi (show (-b) < 0 by linarith) η]
    _ = 1 / b := by
        rw [neg_div_neg_eq, ← mul_div_assoc, ← Real.exp_add,
          show b * η + (-b) * η = 0 by ring, Real.exp_zero]

/-- The majorant of the cubic tail on `(etaZ, ∞)`. -/
noncomputable def tailMajor (a R η : ℝ) (t : ℝ) : ℝ :=
  3 * R * Real.exp (-(a * (t - η))) + 3 * R ^ 2 * Real.exp (-((2 * a) * (t - η)))
    + R ^ 3 * Real.exp (-((3 * a) * (t - η)))

theorem TailMajorant :
    (∀ t : ℝ, Work.BoseFixR.LatGreen.etaZ ≤ t → Work.BoseFixR.LatGreen.rhoZ t ≤ 3 / 4)
      ∧ MeasureTheory.IntegrableOn
          (fun t : ℝ => 3 * Work.BoseFixR.LatGreen.rhoZ t + 3 * (Work.BoseFixR.LatGreen.rhoZ t) ^ 2
            + (Work.BoseFixR.LatGreen.rhoZ t) ^ 3) (Set.Ioi Work.BoseFixR.LatGreen.etaZ)
      ∧ ∫ t in Set.Ioi Work.BoseFixR.LatGreen.etaZ,
          (3 * Work.BoseFixR.LatGreen.rhoZ t + 3 * (Work.BoseFixR.LatGreen.rhoZ t) ^ 2
            + (Work.BoseFixR.LatGreen.rhoZ t) ^ 3) ≤ 1 / 14 := by
  have hηpos : (0 : ℝ) < etaZ := by norm_num [etaZ]
  set a : ℝ := 4 * Real.pi ^ 2 with ha
  set R : ℝ := (16 / 25 : ℝ) with hRdef
  have ha_pos : 0 < a := by rw [ha]; positivity
  have hR0 : 0 ≤ R := by rw [hRdef]; norm_num
  have hRho : rhoZ etaZ ≤ R := by rw [hRdef]; exact rhoZ_etaZ_le
  have hSZdecay : ∀ t : ℝ, etaZ ≤ t → SZ t ≤ Real.exp (-(a * (t - etaZ))) * SZ etaZ := by
    intro t ht
    have h := SZDecay hηpos ht
    rwa [← ha] at h
  -- the pointwise decay of the tail
  have htail : ∀ t : ℝ, etaZ ≤ t → rhoZ t ≤ Real.exp (-(a * (t - etaZ))) * R := by
    intro t ht
    have h1 : rhoZ t ≤ Real.exp (-(a * (t - etaZ))) * rhoZ etaZ := by
      have hs := hSZdecay t ht
      rw [rhoZ]
      calc 2 * SZ t ≤ 2 * (Real.exp (-(a * (t - etaZ))) * SZ etaZ) := by nlinarith [hs]
        _ = Real.exp (-(a * (t - etaZ))) * (2 * SZ etaZ) := by ring
    calc rhoZ t ≤ Real.exp (-(a * (t - etaZ))) * rhoZ etaZ := h1
      _ ≤ Real.exp (-(a * (t - etaZ))) * R :=
          mul_le_mul_of_nonneg_left hRho (Real.exp_nonneg _)
  -- Part 1
  have hpart1 : ∀ t : ℝ, etaZ ≤ t → rhoZ t ≤ 3 / 4 := by
    intro t ht
    have hE1 : Real.exp (-(a * (t - etaZ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have h : 0 ≤ a * (t - etaZ) := mul_nonneg (le_of_lt ha_pos) (by linarith)
      linarith
    calc rhoZ t ≤ Real.exp (-(a * (t - etaZ))) * R := htail t ht
      _ ≤ 1 * R := mul_le_mul hE1 le_rfl hR0 (by norm_num)
      _ = R := one_mul R
      _ ≤ 3 / 4 := by rw [hRdef]; norm_num
  -- the pointwise cubic majorant
  have hbnd : ∀ t : ℝ, t ∈ Set.Ioi etaZ →
      3 * rhoZ t + 3 * (rhoZ t) ^ 2 + (rhoZ t) ^ 3 ≤ tailMajor a R etaZ t := by
    intro t ht
    have htge : etaZ ≤ t := le_of_lt ht
    have hr0 : 0 ≤ rhoZ t := rhoZ_nonneg t
    have hdec : rhoZ t ≤ Real.exp (-(a * (t - etaZ))) * R := htail t htge
    rw [tailMajor]
    have hE2 : (Real.exp (-(a * (t - etaZ)))) ^ 2 = Real.exp (-((2 * a) * (t - etaZ))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hE3 : (Real.exp (-(a * (t - etaZ)))) ^ 3 = Real.exp (-((3 * a) * (t - etaZ))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hp2 := pow_le_pow_left₀ hr0 hdec 2
    have hp3 := pow_le_pow_left₀ hr0 hdec 3
    rw [mul_pow, hE2] at hp2
    rw [mul_pow, hE3] at hp3
    nlinarith [hp2, hp3, hdec]
  -- integrability of the exponential pieces and of the majorant
  have hEint : ∀ b : ℝ, 0 < b →
      IntegrableOn (fun t : ℝ => Real.exp (-(b * (t - etaZ)))) (Set.Ioi etaZ) :=
    fun b hb => integrableOn_exp_shift hb
  have h1 : Integrable (fun t : ℝ => (3 * R) * Real.exp (-(a * (t - etaZ))))
      (volume.restrict (Set.Ioi etaZ)) :=
    (hEint a ha_pos).integrable.const_mul (3 * R)
  have h2 : Integrable (fun t : ℝ => (3 * R ^ 2) * Real.exp (-((2 * a) * (t - etaZ))))
      (volume.restrict (Set.Ioi etaZ)) :=
    (hEint (2 * a) (by linarith)).integrable.const_mul (3 * R ^ 2)
  have h3 : Integrable (fun t : ℝ => (R ^ 3) * Real.exp (-((3 * a) * (t - etaZ))))
      (volume.restrict (Set.Ioi etaZ)) :=
    (hEint (3 * a) (by linarith)).integrable.const_mul (R ^ 3)
  have hGint : IntegrableOn (fun t : ℝ => tailMajor a R etaZ t) (Set.Ioi etaZ) := by
    simp only [tailMajor]
    exact (h1.add h2).add h3
  -- the value of the majorant integral
  have hA : ∫ t in Set.Ioi etaZ, (3 * R) * Real.exp (-(a * (t - etaZ))) = 3 * R / a := by
    rw [integral_const_mul, integral_exp_shift ha_pos, one_div, div_eq_mul_inv]
  have hB : ∫ t in Set.Ioi etaZ, (3 * R ^ 2) * Real.exp (-((2 * a) * (t - etaZ)))
      = 3 * R ^ 2 / (2 * a) := by
    rw [integral_const_mul, integral_exp_shift (by linarith : (0 : ℝ) < 2 * a), one_div,
      div_eq_mul_inv]
  have hC : ∫ t in Set.Ioi etaZ, (R ^ 3) * Real.exp (-((3 * a) * (t - etaZ)))
      = R ^ 3 / (3 * a) := by
    rw [integral_const_mul, integral_exp_shift (by linarith : (0 : ℝ) < 3 * a), one_div,
      div_eq_mul_inv]
  have hsplit1 : ∫ t in Set.Ioi etaZ,
        ((3 * R) * Real.exp (-(a * (t - etaZ))) + (3 * R ^ 2) * Real.exp (-((2 * a) * (t - etaZ)))
          + (R ^ 3) * Real.exp (-((3 * a) * (t - etaZ))))
      = (∫ t in Set.Ioi etaZ, (3 * R) * Real.exp (-(a * (t - etaZ)))
          + (3 * R ^ 2) * Real.exp (-((2 * a) * (t - etaZ))))
        + ∫ t in Set.Ioi etaZ, (R ^ 3) * Real.exp (-((3 * a) * (t - etaZ))) :=
    integral_add (h1.add h2) h3
  have hsplit2 : ∫ t in Set.Ioi etaZ,
        ((3 * R) * Real.exp (-(a * (t - etaZ))) + (3 * R ^ 2) * Real.exp (-((2 * a) * (t - etaZ))))
      = (∫ t in Set.Ioi etaZ, (3 * R) * Real.exp (-(a * (t - etaZ))))
        + ∫ t in Set.Ioi etaZ, (3 * R ^ 2) * Real.exp (-((2 * a) * (t - etaZ))) :=
    integral_add h1 h2
  have hGval : ∫ t in Set.Ioi etaZ, tailMajor a R etaZ t
      = 3 * R / a + 3 * R ^ 2 / (2 * a) + R ^ 3 / (3 * a) := by
    simp only [tailMajor]
    rw [hsplit1, hsplit2, hA, hB, hC]
  -- measurability
  have hSZmeas : Measurable SZ := by
    have h : SZ = fun t : ℝ =>
        ∑' j : ℕ, Real.exp (-(4 * Real.pi ^ 2 * t) * ((j : ℝ) + 1) ^ 2) := by
      funext t
      rw [SZ]
    rw [h]
    apply Measurable.tsum
    intro j
    fun_prop
  have hRmeas : Measurable rhoZ := by
    have h : rhoZ = fun t : ℝ => 2 * SZ t := by
      funext t
      rw [rhoZ]
    rw [h]
    exact hSZmeas.const_mul 2
  have hfmeas : Measurable fun t : ℝ =>
      3 * rhoZ t + 3 * (rhoZ t) ^ 2 + (rhoZ t) ^ 3 := by
    fun_prop
  have hae_mem : ∀ᵐ t ∂(volume.restrict (Set.Ioi etaZ)), t ∈ Set.Ioi etaZ :=
    ae_restrict_mem measurableSet_Ioi
  have hle_ae : (fun t : ℝ => 3 * rhoZ t + 3 * (rhoZ t) ^ 2 + (rhoZ t) ^ 3)
      ≤ᵐ[volume.restrict (Set.Ioi etaZ)] (fun t : ℝ => tailMajor a R etaZ t) := by
    filter_upwards [hae_mem] with t ht
    exact hbnd t ht
  have hnorm_ae : ∀ᵐ t ∂(volume.restrict (Set.Ioi etaZ)),
      ‖3 * rhoZ t + 3 * (rhoZ t) ^ 2 + (rhoZ t) ^ 3‖ ≤ tailMajor a R etaZ t := by
    filter_upwards [hae_mem] with t ht
    have hr : 0 ≤ rhoZ t := rhoZ_nonneg t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbnd t ht
  have hfint : IntegrableOn
      (fun t : ℝ => 3 * rhoZ t + 3 * (rhoZ t) ^ 2 + (rhoZ t) ^ 3) (Set.Ioi etaZ) :=
    Integrable.mono' hGint hfmeas.aestronglyMeasurable hnorm_ae
  -- the numerical bound
  have hfin : 3 * R / a + 3 * R ^ 2 / (2 * a) + R ^ 3 / (3 * a) ≤ 1 / 14 := by
    have ha39 : (39 : ℝ) ≤ a := by rw [ha]; nlinarith [Real.pi_gt_d2, Real.pi_pos]
    rw [hRdef]
    have e1 : 3 * (16 / 25 : ℝ) / a ≤ 3 * (16 / 25 : ℝ) / 39 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) ha39
    have e2 : 3 * (16 / 25 : ℝ) ^ 2 / (2 * a) ≤ 3 * (16 / 25 : ℝ) ^ 2 / (2 * 39) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (by linarith : (2 : ℝ) * 39 ≤ 2 * a)
    have e3 : (16 / 25 : ℝ) ^ 3 / (3 * a) ≤ (16 / 25 : ℝ) ^ 3 / (3 * 39) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (by linarith : (3 : ℝ) * 39 ≤ 3 * a)
    have hsum : 3 * (16 / 25 : ℝ) / 39 + 3 * (16 / 25 : ℝ) ^ 2 / (2 * 39)
        + (16 / 25 : ℝ) ^ 3 / (3 * 39) ≤ 1 / 14 := by norm_num
    linarith [e1, e2, e3]
  have hval : ∫ t in Set.Ioi etaZ, (3 * rhoZ t + 3 * (rhoZ t) ^ 2 + (rhoZ t) ^ 3)
      ≤ 3 * R / a + 3 * R ^ 2 / (2 * a) + R ^ 3 / (3 * a) := by
    calc ∫ t in Set.Ioi etaZ, (3 * rhoZ t + 3 * (rhoZ t) ^ 2 + (rhoZ t) ^ 3)
        ≤ ∫ t in Set.Ioi etaZ, tailMajor a R etaZ t := integral_mono_ae hfint hGint hle_ae
      _ = 3 * R / a + 3 * R ^ 2 / (2 * a) + R ^ 3 / (3 * a) := hGval
  exact ⟨hpart1, hfint, by linarith [hval, hfin]⟩

end Work.BoseFixR.LatGreen
