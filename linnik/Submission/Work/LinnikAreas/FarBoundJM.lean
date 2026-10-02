import Mathlib
import Submission.Work.LinnikAreas.FarBoundOfJutilaMontgomery
import Submission.Work.LinnikAreas.JMAux.FarMassLeDoubleSum
import Submission.Work.LinnikAreas.JMAux.CellMultLeBoundJM
import Submission.Work.LinnikAreas.JMAux.MsumBranch1
import Submission.Work.LinnikAreas.JMAux.MsumBranch2
import Submission.Work.LinnikAreas.JMAuxSh.ShAux

/-!
# Assembly of the far-zero bound from Jutila's and Montgomery's theorems

This module contains the proofs of the two `sorry`-free reductions advertised in
`Work.LinnikAreas.FarBoundOfJutilaMontgomery`:

* `FarBoundHyp_of_jutila_and_montgomery : FamilyZeroDensityJutila → FamilyZeroDensityMontgomery
  → FarBoundHyp`;
* `area2_of_jutila_montgomery`, the corresponding form of `Work.LinnikContract.Area2`.

The proof replays the dyadic shell decomposition of `Work.LinnikAreas.FarBoundOfDensity` with the
shell-dependent exponent of `cellBoundJM`; see the module docstring of
`Work.LinnikAreas.FarBoundOfJutilaMontgomery` for the geometry.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 2000000

namespace Work.LinnikAreas

open Work.LinnikContract

/-- `(log y)^B ≤ (100B)^B·y^{1/100}` for `y ≥ 1`, `B > 0` (from `log y ≤ y^a/a` with
`a = 1/(100B)`). -/
lemma log_rpow_le_mul_rpow {B y : ℝ} (hB : 0 < B) (hy : 1 ≤ y) :
    (Real.log y) ^ B ≤ (100*B)^B * y ^ ((1:ℝ)/100) := by
  have ha : (0:ℝ) < 1/(100*B) := by positivity
  have hy0 : (0:ℝ) < y := lt_of_lt_of_le one_pos hy
  have h1 : Real.log y ≤ y ^ (1/(100*B)) / (1/(100*B)) :=
    Real.log_le_rpow_div (le_of_lt hy0) ha
  have h2 : y ^ (1/(100*B)) / (1/(100*B)) = 100*B * y ^ (1/(100*B)) := by
    field_simp
  rw [h2] at h1
  have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy
  have h3 : (Real.log y) ^ B ≤ (100*B * y ^ (1/(100*B)))^B :=
    Real.rpow_le_rpow hlog0 h1 (le_of_lt hB)
  refine le_trans h3 (le_of_eq ?_)
  have hy1 : (0:ℝ) ≤ y := le_of_lt hy0
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hy1 _)]
  congr 1
  rw [← Real.rpow_mul hy1]
  congr 1
  field_simp

/-- **The main reduction of the far-zero mass to the cell sums.**  This is steps 1–2 of the proof
of `FarBoundOfDensity.finset_bound`, abstracted: the weighted far-zero mass over an arbitrary
finite set `S` of pairs is bounded by `32` times the double `(m,k)`-sum of the *cell
multiplicities*. -/
lemma farMass_le_doubleSum {q : ℕ} [NeZero q] (R : ℕ) (hR : 1 ≤ R) {L : ℝ} (hL : 0 < L)
    (hLq : Real.log (q:ℝ) ≤ L)
    (K : ℕ) (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hK : ∀ z ∈ S, z.1 ≠ 1 → ¬ InBox q (R:ℝ) z.2 → zeroMult z.1 z.2 ≠ 0 →
      max (farM L z : ℝ) (farY L z) + 1 ≤ (2:ℝ)^K) :
    farMassSum R L S
      ≤ 32 * ∑ m ∈ Finset.range (Nat.ceil L + 1), Real.exp (-(49/10) * (m:ℝ))
          * ∑ k ∈ Finset.range (K+1), (1/4:ℝ)^k * cellLayer R m k
              * cellMult L (farPairs R S) m k :=
  JMAux.FarMassLeDoubleSum R hR hL hLq K S hK

/-- **The cell bound.**  Every cell's multiplicity sum is bounded by `cellBoundJM`. -/
lemma cellMult_le_boundJM {q : ℕ} [NeZero q] (hq : 2 ≤ q) {L : ℝ} (hLp : 0 < L) (hL1 : 1 ≤ L)
    {CJ CM c0 : ℝ} (hCJ : 0 < CJ) (hCM : 0 < CM) (hc0 : 0 < c0)
    (hfamJ : ∀ σ T : ℝ, (4:ℝ)/5 ≤ σ → σ ≤ 1 → 1 ≤ T →
      ∑ χ : DirichletCharacter ℂ q, zeroCountIn χ σ T
        ≤ CJ * ((q:ℝ) * T) ^ ((2 + 1/1000) * (1 - σ)))
    (hfamM : ∀ σ T : ℝ, 0 ≤ σ → σ ≤ 1 → 1 ≤ T →
      ∑ χ : DirichletCharacter ℂ q, zeroCountIn χ σ T
        ≤ CM * ((q:ℝ) * T) ^ ((2451/1000) * (1 - σ)))
    (hball : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ.IsPrimitive →
      ∀ (a : ℂ) (ρ : ℝ), 1 ≤ ρ →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ) : ℝ))
        ≤ c0 * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N:ℝ) + 2))
    {S : Finset (DirichletCharacter ℂ q × ℂ)}
    (hS : ∀ z ∈ S, z.1 ≠ 1 ∧ zeroMult z.1 z.2 ≠ 0) (m k : ℕ) :
    cellMult L S m k ≤ cellBoundJM q CJ CM c0 L m k :=
  JMAux.CellMultLeBoundJM hq hLp hL1 hCJ hCM hc0 hfamJ hfamM hball hS m k

/-- **Geometric tail of `e^{-(49/10)m}`** with a linear threshold `b·L - 1`. -/
lemma geom_exp_tail_gen {L b : ℝ} (hL : 0 < L) {s : Finset ℕ}
    (h : ∀ m ∈ s, b*L - 1 < (m:ℝ)) :
    (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))) ≤ 500 * Real.exp (-((49/10)*b*L)) := by
  set r : ℝ := Real.exp (-(49/10)) with hr
  have hr0 : 0 ≤ r := le_of_lt (Real.exp_pos _)
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hpow : ∀ m : ℕ, Real.exp (-(49/10) * (m:ℝ)) = r^m := by
    intro m
    rw [hr, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun m _ => hpow m)]
  set M : ℕ := Nat.ceil (b*L - 1) with hM
  have hmge : ∀ m ∈ s, M ≤ m := fun m hm => Nat.ceil_le.mpr (le_of_lt (h m hm))
  set N : ℕ := s.sup id + 1 with hN
  have hsub : s ⊆ Finset.Ico M N := by
    intro m hm
    rw [Finset.mem_Ico]
    exact ⟨hmge m hm, by rw [hN]; exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hm)⟩
  have hstep : ∑ m ∈ s, r^m ≤ ∑ m ∈ Finset.Ico M N, r^m :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => pow_nonneg hr0 k)
  have hIco : ∑ m ∈ Finset.Ico M N, r^m = r^M * ∑ j ∈ Finset.range (N - M), r^j := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_); rw [pow_add]
  have hgeom : ∑ j ∈ Finset.range (N - M), r^j ≤ 1/(1-r) :=
    Commons.Analysis.Asymptotics.geom_finset_le hr0 hr1 _
  have hgeom2 : 1/(1-r) ≤ 2 := by
    have h2 : r ≤ 1/2 := by
      rw [hr]
      have h1 : -((49:ℝ)/10) ≤ Real.log (1/2) := by
        have h2' : Real.log (1/2) = -Real.log 2 := by rw [one_div, Real.log_inv]
        rw [h2']
        have h3 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
        linarith
      calc Real.exp (-(49/10)) ≤ Real.exp (Real.log (1/2)) := Real.exp_le_exp.mpr h1
        _ = 1/2 := Real.exp_log (by norm_num)
    have h3 : (0:ℝ) < 1 - r := by linarith
    rw [div_le_iff₀ h3]; linarith
  have hMle : ((M:ℕ):ℝ) ≥ b*L - 1 := Nat.le_ceil _
  have hrM : r^M ≤ Real.exp (-(49/10) * (b*L - 1)) := by
    rw [show r^M = Real.exp (-(49/10) * (M:ℝ)) by
      rw [hr, ← Real.exp_nat_mul]; congr 1; ring]
    exact Real.exp_le_exp.mpr (by linarith)
  have hexp4 : Real.exp (-(49/10) * (b*L - 1)) = Real.exp (49/10) * Real.exp (-((49/10)*b*L)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp49 : Real.exp (49/10) ≤ 250 := by
    have h1 : (49:ℝ)/10 ≤ 5 := by norm_num
    calc Real.exp (49/10) ≤ Real.exp 5 := Real.exp_le_exp.mpr h1
      _ = (Real.exp 1)^5 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 3^5 := pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt Real.exp_one_lt_three) 5
      _ = 243 := by norm_num
      _ ≤ 250 := by norm_num
  calc ∑ m ∈ s, r^m ≤ ∑ m ∈ Finset.Ico M N, r^m := hstep
    _ = r^M * ∑ j ∈ Finset.range (N - M), r^j := hIco
    _ ≤ r^M * 2 := mul_le_mul_of_nonneg_left (le_trans hgeom hgeom2) (pow_nonneg hr0 M)
    _ ≤ Real.exp (-(49/10) * (b*L - 1)) * 2 := mul_le_mul_of_nonneg_right hrM (by norm_num)
    _ = 2 * Real.exp (49/10) * Real.exp (-((49/10)*b*L)) := by rw [hexp4]; ring
    _ ≤ 500 * Real.exp (-((49/10)*b*L)) := by
        have hpos : 0 ≤ Real.exp (-((49/10)*b*L)) := le_of_lt (Real.exp_pos _)
        nlinarith [hexp49, hpos]

/-- **Branch 3 of the `m`-sum**: the σ-blind shells `(m+1) > 5L/12`, i.e. `σ < 7/12`. -/
lemma msum_branch3 (q : ℕ) (hq2 : 2 ≤ q) {L : ℝ} (hLp : 0 < L) (hL1000 : 1000 ≤ L)
    (hLdef : L = Real.log (q:ℝ)) (R : ℕ) {c0 : ℝ} (hc0 : 0 ≤ c0) (N : ℕ) {s : Finset ℕ}
    (hs : ∀ m ∈ s, (5/12)*L - 1 < (m:ℝ)) :
    (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * ((q:ℝ) * c0 * (4 + (2:ℝ)^k) * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2)))
      ≤ 60000 * c0 / (q:ℝ) := by
  classical
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hq0 : (0:ℝ) < (q:ℝ) := by linarith
  have hlog7 : ∀ k : ℕ, 0 ≤ Real.log (7 + (2:ℝ)^k) := by
    intro k
    apply Real.log_nonneg
    have : (0:ℝ) ≤ (2:ℝ)^k := by positivity
    linarith
  have hstep : ∀ m : ℕ, m ∈ s →
      Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * ((q:ℝ) * c0 * (4 + (2:ℝ)^k) * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2))
      ≤ Real.exp (-(49/10) * (m:ℝ)) * ((q:ℝ) * c0 * (10 * Real.log (q:ℝ) + 100)) := by
    intro m _
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
    have hinner : (∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * ((q:ℝ) * c0 * (4 + (2:ℝ)^k) * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2)))
        ≤ (q:ℝ) * c0 * ∑ k ∈ Finset.range N, (1/4:ℝ)^k
            * ((4 + (2:ℝ)^k) * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun k _ => ?_)
      have hcell1 : cellLayer R m k ≤ 1 := by rw [cellLayer]; split <;> norm_num
      have hY0 : (0:ℝ) ≤ (1/4:ℝ)^k * ((q:ℝ) * c0 * (4 + (2:ℝ)^k)
          * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2)) := by
        have h4 : (0:ℝ) ≤ 4 + (2:ℝ)^k := by positivity
        have hl2 : 0 ≤ Real.log (q:ℝ) := Real.log_nonneg hq1
        have hqc : (0:ℝ) ≤ (q:ℝ) * c0 := mul_nonneg hq0.le hc0
        refine mul_nonneg (by positivity) ?_
        exact mul_nonneg (mul_nonneg hqc h4) (by linarith only [hlog7 k, hl2])
      calc (1/4:ℝ)^k * cellLayer R m k * ((q:ℝ) * c0 * (4 + (2:ℝ)^k)
              * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2))
          = ((1/4:ℝ)^k * ((q:ℝ) * c0 * (4 + (2:ℝ)^k)
              * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2))) * cellLayer R m k := by ring
        _ ≤ ((1/4:ℝ)^k * ((q:ℝ) * c0 * (4 + (2:ℝ)^k)
              * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2))) * 1 :=
              mul_le_mul_of_nonneg_left hcell1 (by positivity)
        _ = (q:ℝ) * c0 * ((1/4:ℝ)^k * ((4 + (2:ℝ)^k)
              * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2))) := by ring
    refine le_trans hinner ?_
    have h4 := sum_quarter_B_le hq1 N
    have hcc : (0:ℝ) ≤ (q:ℝ) * c0 := mul_nonneg hq0.le hc0
    exact mul_le_mul_of_nonneg_left h4 hcc
  have hsum : (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))) ≤ 500 * Real.exp (-((49/24)*L)) := by
    have h := geom_exp_tail_gen (L := L) (b := 5/12) hLp hs
    have heq : (49/10) * (5/12) * L = (49/24) * L := by ring
    rwa [heq] at h
  have hkey : 500 * (10*L + 100) ≤ 60000 * Real.exp (L/24) := by
    have hexp_lb : (L/24)^2/2 ≤ Real.exp (L/24) := by
      have h := Real.pow_div_factorial_le_exp (L/24) (by positivity) 2
      simpa using h
    have h1 : 500 * (10*L + 100) ≤ 52 * L^2 := by nlinarith [hL1000, sq_nonneg L]
    have h2 : 52 * L^2 ≤ 60000 * ((L/24)^2/2) := by linarith
    have h3 : 60000 * ((L/24)^2/2) ≤ 60000 * Real.exp (L/24) :=
      mul_le_mul_of_nonneg_left hexp_lb (by norm_num)
    linarith
  have hqexp : (q:ℝ) = Real.exp L := by rw [hLdef, Real.exp_log hq0]
  have hle : 500 * (10*L + 100) * Real.exp (-(L/24)) ≤ 60000 := by
    rw [Real.exp_neg, inv_eq_one_div, mul_one_div, div_le_iff₀ (Real.exp_pos _)]
    exact hkey
  calc (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * ((q:ℝ) * c0 * (4 + (2:ℝ)^k) * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2)))
      ≤ ∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
          * ((q:ℝ) * c0 * (10 * Real.log (q:ℝ) + 100)) := Finset.sum_le_sum hstep
    _ = ((q:ℝ) * c0 * (10 * Real.log (q:ℝ) + 100))
          * ∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ)) := by rw [← Finset.sum_mul]; ring
    _ = ((q:ℝ) * c0 * (10 * L + 100)) * ∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ)) := by
          rw [hLdef]
    _ ≤ ((q:ℝ) * c0 * (10 * L + 100)) * (500 * Real.exp (-((49/24)*L))) := by
          refine mul_le_mul_of_nonneg_left hsum ?_
          have hl2 : 0 ≤ Real.log (q:ℝ) := Real.log_nonneg hq1
          have hcc : (0:ℝ) ≤ (q:ℝ) * c0 := mul_nonneg hq0.le hc0
          positivity
    _ ≤ 60000 * c0 / (q:ℝ) := by
          have hE : Real.exp L * Real.exp (-((49:ℝ)/24*L))
              = Real.exp (-L) * Real.exp (-(L/24)) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
          have hkey2 : (500 * (10*L+100) * Real.exp (-(L/24))) * (c0 * Real.exp (-L))
              ≤ 60000 * (c0 * Real.exp (-L)) :=
            mul_le_mul_of_nonneg_right hle (mul_nonneg hc0 (Real.exp_nonneg _))
          have hrw : (q:ℝ) * c0 * (10*L + 100) * (500 * Real.exp (-((49:ℝ)/24*L)))
              = (500 * (10*L+100) * Real.exp (-(L/24))) * (c0 * Real.exp (-L)) := by
            rw [hqexp]
            rw [show Real.exp L * c0 * (10*L+100) * (500 * Real.exp (-((49:ℝ)/24*L)))
                = 500 * (10*L+100) * (Real.exp L * Real.exp (-((49:ℝ)/24*L))) * c0 by ring]
            rw [hE]; ring
          rw [hrw]
          refine le_trans hkey2 ?_
          rw [hqexp, Real.exp_neg, div_eq_mul_inv]
          exact le_of_eq (by ring)

/-- **The `m`-sum of the double sum**, in its three branches. -/
lemma msum_boundJM {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) {L : ℝ} (hLp : 0 < L)
    (hLdef : L = Real.log (q:ℝ)) (hL1000 : 1000 ≤ L) (R : ℕ) (hR1 : 1 ≤ R)
    {CJ CM c0 : ℝ} (hCJ : 0 < CJ) (hCM : 0 < CM) (hc0 : 0 < c0) (Mmax N : ℕ) :
    (∑ m ∈ Finset.range Mmax, Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * cellBoundJM q CJ CM c0 L m k)
      ≤ 100 * CJ / (R:ℝ)^(3/2:ℝ) + 30000 * CM / ((R:ℝ)^(9/10:ℝ) * (q:ℝ)^(19/40:ℝ))
        + 60000 * c0 / (q:ℝ) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range Mmax)
      (fun m : ℕ => ((m:ℝ)+1) ≤ (5/12)*L)
      (fun m => Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * cellBoundJM q CJ CM c0 L m k)]
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.range Mmax).filter
      (fun m : ℕ => ((m:ℝ)+1) ≤ (5/12)*L)) (fun m : ℕ => ((m:ℝ)+1) ≤ L/5)
      (fun m => Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * cellBoundJM q CJ CM c0 L m k)]
  have hA : (∑ m ∈ ((Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (5/12)*L)).filter
        (fun m : ℕ => ((m:ℝ)+1) ≤ L/5),
      Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
          * cellBoundJM q CJ CM c0 L m k)
      ≤ 100 * CJ / (R:ℝ)^(3/2:ℝ) := by
    have heq : (∑ m ∈ ((Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (5/12)*L)).filter
          (fun m : ℕ => ((m:ℝ)+1) ≤ L/5),
        Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * cellBoundJM q CJ CM c0 L m k)
        = (∑ m ∈ ((Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (5/12)*L)).filter
          (fun m : ℕ => ((m:ℝ)+1) ≤ L/5),
        Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * (CJ * ((q:ℝ) * (2:ℝ)^k) ^ ((2 + 1/1000) * (((m:ℝ) + 1)/L)))) := by
      refine Finset.sum_congr rfl (fun m hm => ?_)
      have hm1 : ((m:ℝ)+1) ≤ L/5 := (Finset.mem_filter.mp hm).2
      congr 1
      exact Finset.sum_congr rfl (fun k _ => by rw [cellBoundJM, if_pos hm1])
    rw [heq]
    exact JMAux.MsumBranch1 q hq2 hLp hLdef R hR1 hCJ Mmax N
      (fun m hm => (Finset.mem_filter.mp hm).2)
  have hB : (∑ m ∈ ((Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (5/12)*L)).filter
        (fun m : ℕ => ¬ (((m:ℝ)+1) ≤ L/5)),
      Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
          * cellBoundJM q CJ CM c0 L m k)
      ≤ 30000 * CM / ((R:ℝ)^(9/10:ℝ) * (q:ℝ)^(19/40:ℝ)) := by
    have heq : (∑ m ∈ ((Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (5/12)*L)).filter
          (fun m : ℕ => ¬ (((m:ℝ)+1) ≤ L/5)),
        Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * cellBoundJM q CJ CM c0 L m k)
        = (∑ m ∈ ((Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (5/12)*L)).filter
          (fun m : ℕ => ¬ (((m:ℝ)+1) ≤ L/5)),
        Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * (CM * ((q:ℝ) * (2:ℝ)^k) ^ ((2451/1000) * (((m:ℝ) + 1)/L)))) := by
      refine Finset.sum_congr rfl (fun m hm => ?_)
      have hm1 : ¬ (((m:ℝ)+1) ≤ L/5) := (Finset.mem_filter.mp hm).2
      have hm2 : ((m:ℝ)+1) ≤ (5/12)*L := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
      congr 1
      exact Finset.sum_congr rfl (fun k _ => by rw [cellBoundJM, if_neg hm1, if_pos hm2])
    rw [heq]
    refine JMAux.MsumBranch2 q hq2 hLp hLdef R hR1 hCM Mmax N ?_ ?_
    · intro m hm
      exact lt_of_not_ge (Finset.mem_filter.mp hm).2
    · intro m hm
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
  have hC : (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ¬ (((m:ℝ)+1) ≤ (5/12)*L)),
      Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
          * cellBoundJM q CJ CM c0 L m k)
      ≤ 60000 * c0 / (q:ℝ) := by
    have heq : (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ¬ (((m:ℝ)+1) ≤ (5/12)*L)),
        Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * cellBoundJM q CJ CM c0 L m k)
        = (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ¬ (((m:ℝ)+1) ≤ (5/12)*L)),
        Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * ((q:ℝ) * c0 * (4 + (2:ℝ)^k)
              * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2))) := by
      refine Finset.sum_congr rfl (fun m hm => ?_)
      have hm2 : ¬ (((m:ℝ)+1) ≤ (5/12)*L) := (Finset.mem_filter.mp hm).2
      have hm1 : ¬ (((m:ℝ)+1) ≤ L/5) := by
        intro h
        exact hm2 (le_trans h (by linarith))
      congr 1
      exact Finset.sum_congr rfl (fun k _ => by rw [cellBoundJM, if_neg hm1, if_neg hm2])
    rw [heq]
    refine msum_branch3 q hq2 hLp hL1000 hLdef R hc0.le N ?_
    intro m hm
    have h2 : (5/12)*L < (m:ℝ)+1 := lt_of_not_ge (Finset.mem_filter.mp hm).2
    linarith
  linarith only [hA, hB, hC]

/-- **The far-zero mass bound** under the pair of hypotheses (Jutila, Montgomery). -/
lemma finset_boundJM (q : ℕ) [NeZero q] (hq : 2 ≤ q) (R : ℕ) (hR : 1 ≤ R)
    (CJ CM c0 : ℝ) (hCJ : 0 < CJ) (hCM : 0 < CM) (hc0 : 0 < c0)
    (hfamJ : ∀ σ T : ℝ, (4:ℝ)/5 ≤ σ → σ ≤ 1 → 1 ≤ T →
      ∑ χ : DirichletCharacter ℂ q, zeroCountIn χ σ T
        ≤ CJ * ((q:ℝ) * T) ^ ((2 + 1/1000) * (1 - σ)))
    (hfamM : ∀ σ T : ℝ, 0 ≤ σ → σ ≤ 1 → 1 ≤ T →
      ∑ χ : DirichletCharacter ℂ q, zeroCountIn χ σ T
        ≤ CM * ((q:ℝ) * T) ^ ((2451/1000) * (1 - σ)))
    (hball : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ.IsPrimitive →
      ∀ (a : ℂ) (ρ : ℝ), 1 ≤ ρ →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ) : ℝ))
        ≤ c0 * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N:ℝ) + 2))
    (hL : 1000 ≤ Real.log (q:ℝ))
    (S : Finset (DirichletCharacter ℂ q × ℂ)) :
    farMassSum R (Real.log (q:ℝ)) S
      ≤ 3200 * CJ / ((R:ℝ)^(3/2:ℝ)) + 960000 * CM / ((R:ℝ)^(9/10:ℝ) * (q:ℝ)^(19/40:ℝ))
        + 1920000 * c0 / (q:ℝ) := by
  classical
  set L : ℝ := Real.log (q:ℝ) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hL1000 : 1000 ≤ L := by rw [hLdef]; exact hL
  have hL1 : (1:ℝ) ≤ L := by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ z ∈ S, z.1 ≠ 1 → ¬ InBox q (R:ℝ) z.2 → zeroMult z.1 z.2 ≠ 0 →
      max (farM L z : ℝ) (farY L z) + 1 ≤ (2:ℝ)^K := by
    refine ⟨S.sup (fun z => Nat.ceil (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))), ?_⟩
    intro z hz _ _ _
    have h1 : Nat.ceil (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))
        ≤ S.sup (fun z => Nat.ceil (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))) :=
      Finset.le_sup (f := fun z => Nat.ceil
        (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))) hz
    have h2 : Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1)
        ≤ ((S.sup (fun z => Nat.ceil
          (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))) : ℕ) : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
    have h3 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) h2
    have h4 : (2:ℝ) ^ (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))
        = (max (farM L z : ℝ) (farY L z) + 1 : ℝ) :=
      Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
    rw [h4, Real.rpow_natCast] at h3
    exact h3
  have h1 := farMass_le_doubleSum (q := q) R hR hLpos (le_of_eq hLdef.symm) K S hK
  have hcell0 : ∀ m k : ℕ, 0 ≤ (1/4:ℝ)^k * cellLayer R m k := by
    intro m k
    have : (0:ℝ) ≤ cellLayer R m k := by rw [cellLayer]; split <;> norm_num
    positivity
  have h2 : (∑ m ∈ Finset.range (Nat.ceil L + 1), Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range (K+1), (1/4:ℝ)^k * cellLayer R m k
            * cellMult L (farPairs R S) m k)
      ≤ (∑ m ∈ Finset.range (Nat.ceil L + 1), Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range (K+1), (1/4:ℝ)^k * cellLayer R m k
            * cellBoundJM q CJ CM c0 L m k) := by
    refine Finset.sum_le_sum (fun m _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
    refine Finset.sum_le_sum (fun k _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (hcell0 m k)
    refine cellMult_le_boundJM hq hLpos hL1 hCJ hCM hc0 hfamJ hfamM hball ?_ m k
    intro z hz
    rw [farPairs, Finset.mem_filter, Finset.mem_filter] at hz
    exact ⟨hz.1.2.1, hz.2⟩
  have h3 := msum_boundJM hq hLpos hLdef hL1000 R hR hCJ hCM hc0 (Nat.ceil L + 1) (K+1)
  have h23 : (∑ m ∈ Finset.range (Nat.ceil L + 1), Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range (K+1), (1/4:ℝ)^k * cellLayer R m k
            * cellMult L (farPairs R S) m k)
      ≤ 100 * CJ / (R:ℝ)^(3/2:ℝ) + 30000 * CM / ((R:ℝ)^(9/10:ℝ) * (q:ℝ)^(19/40:ℝ))
        + 60000 * c0 / (q:ℝ) := le_trans h2 h3
  refine le_trans h1 ?_
  have hmul : 32 * ((∑ m ∈ Finset.range (Nat.ceil L + 1), Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range (K+1), (1/4:ℝ)^k * cellLayer R m k
            * cellMult L (farPairs R S) m k))
      ≤ 32 * (100 * CJ / (R:ℝ)^(3/2:ℝ) + 30000 * CM / ((R:ℝ)^(9/10:ℝ) * (q:ℝ)^(19/40:ℝ))
        + 60000 * c0 / (q:ℝ)) := mul_le_mul_of_nonneg_left h23 (by norm_num)
  refine le_trans hmul (le_of_eq ?_)
  ring

/-- **Heath-Brown's Lemma 13.2 from Jutila's log-free bound and Montgomery's density theorem.**

**Warning (the hypothesis is not a theorem).**  This route consumes
`FamilyZeroDensityJutila`, i.e. the log-free bound summed over **all** characters mod `q`; at
`σ = 4/5` its `χ = 1` term is a density estimate for `ζ` with exponent `2`, which is **not known**
(see `Work.LinnikAreas.NOTE_area2_principal_character.md`).  Only the *non-principal* form
`FamilyZeroDensityJutilaNP` is a theorem of the literature, and the routes through
`FamilyZeroDensityMesh` (`FarBoundHyp_of_jutila_and_mesh`, `area2_of_jutila_mesh`) consume it.
This theorem is kept because it is proved and harmless, but it should not be used as a target. -/
theorem FarBoundHyp_of_jutila_and_montgomery
    (hj : FamilyZeroDensityJutila) (hm : FamilyZeroDensityMontgomery) :
    FarBoundHyp := by
  obtain ⟨CJ, hCJpos, hJ⟩ := hj (1/1000) (by norm_num)
  obtain ⟨CM₀, hCM₀pos, hM⟩ := hm (1/1000) (by norm_num) 1 (by norm_num)
  obtain ⟨c0, hc0pos, hball⟩ :=
    Commons.NumberTheory.DirichletCharacter.completedL_ballZeroCount_uniform
  set CM : ℝ := max (100 * CM₀) CJ with hCMdef
  have hCMpos : 0 < CM := lt_max_of_lt_left (by positivity)
  have hCM₀le : 100 * CM₀ ≤ CM := le_max_left _ _
  intro ε hε
  have hε4 : 0 < ε/4 := by linarith
  set A₁ : ℝ := (6400 * CJ / ε) ^ ((2:ℝ)/3) with hA₁def
  set A₂ : ℝ := (4 * (10:ℝ)^6 * CM / ε) ^ ((10:ℝ)/9) with hA₂def
  have hA₁pos : 0 < A₁ := by rw [hA₁def]; exact Real.rpow_pos_of_pos (by positivity) _
  have hA₂pos : 0 < A₂ := by rw [hA₂def]; exact Real.rpow_pos_of_pos (by positivity) _
  set R : ℕ := Nat.floor (max A₁ A₂) + 2 with hRdef
  have hR1 : 1 ≤ R := by rw [hRdef]; omega
  have hRpos : (0:ℝ) < (R:ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hRleA₁ : A₁ ≤ (R:ℝ) := by
    have h1 : A₁ ≤ max A₁ A₂ := le_max_left _ _
    have h2 : max A₁ A₂ < ((Nat.floor (max A₁ A₂) : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : ((Nat.floor (max A₁ A₂) : ℕ) : ℝ) + 1 ≤ (R:ℝ) := by
      rw [hRdef]; push_cast; linarith only []
    linarith only [h1, h2, h3]
  have hRleA₂ : A₂ ≤ (R:ℝ) := by
    have h1 : A₂ ≤ max A₁ A₂ := le_max_right _ _
    have h2 : max A₁ A₂ < ((Nat.floor (max A₁ A₂) : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : ((Nat.floor (max A₁ A₂) : ℕ) : ℝ) + 1 ≤ (R:ℝ) := by
      rw [hRdef]; push_cast; linarith only []
    linarith only [h1, h2, h3]
  have hA₁pow : A₁ ^ ((3:ℝ)/2) = 6400 * CJ / ε := by
    rw [hA₁def, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 6400 * CJ / ε)]
    norm_num
  have hA₂pow : A₂ ^ ((9:ℝ)/10) = 4 * (10:ℝ)^6 * CM / ε := by
    rw [hA₂def, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 4 * (10:ℝ)^6 * CM / ε)]
    norm_num
  have hfirst : 3200 * CJ / (R:ℝ)^(3/2:ℝ) ≤ ε/2 := by
    have hge : 6400 * CJ / ε ≤ (R:ℝ) ^ ((3:ℝ)/2) := by
      have h := Real.rpow_le_rpow hA₁pos.le hRleA₁ (by norm_num : (0:ℝ) ≤ 3/2)
      rwa [hA₁pow] at h
    have hquot : 3200 * CJ / (R:ℝ)^(3/2:ℝ) ≤ 3200 * CJ / (6400 * CJ / ε) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hge
    have hval : 3200 * CJ / (6400 * CJ / ε) = ε/2 := by
      field_simp
      ring
    linarith only [hquot, hval]
  set q₀ : ℕ := max (max (Nat.ceil (Real.exp 1000))
    (Nat.ceil (4 * (1920000:ℝ) * c0 / ε))) 2 with hq₀def
  have hq₀2 : 2 ≤ q₀ := by rw [hq₀def]; exact le_max_right _ _
  have hq₀exp : Nat.ceil (Real.exp 1000) ≤ q₀ := by
    rw [hq₀def]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hq₀c : Nat.ceil (4 * (1920000:ℝ) * c0 / ε) ≤ q₀ := by
    rw [hq₀def]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨(R:ℝ), hRpos, q₀, ?_⟩
  intro q hq hqN
  have hq2 : 2 ≤ q := le_trans hq₀2 hq
  have hqRpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hexpq : Real.exp 1000 ≤ (q:ℝ) := by
    have h1 : Real.exp 1000 ≤ ((Nat.ceil (Real.exp 1000) : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (Real.exp 1000) : ℕ) : ℝ) ≤ (q:ℝ) :=
      Nat.cast_le.mpr (le_trans hq₀exp hq)
    linarith only [h1, h2]
  have hL : 1000 ≤ Real.log (q:ℝ) := by
    rw [← Real.log_exp 1000]
    exact Real.log_le_log (Real.exp_pos 1000) hexpq
  have hqbig : 4 * (1920000:ℝ) * c0 / ε ≤ (q:ℝ) := by
    have h1 : 4 * (1920000:ℝ) * c0 / ε
        ≤ ((Nat.ceil (4 * (1920000:ℝ) * c0 / ε) : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (4 * (1920000:ℝ) * c0 / ε) : ℕ) : ℝ) ≤ (q:ℝ) :=
      Nat.cast_le.mpr (le_trans hq₀c hq)
    linarith only [h1, h2]
  have hthird : 1920000 * c0 / (q:ℝ) ≤ ε/4 := by
    have hh : 4 * (1920000:ℝ) * c0 ≤ ε * (q:ℝ) := by
      rw [div_le_iff₀ hε] at hqbig
      linarith only [hqbig]
    rw [div_le_iff₀ hqRpos]
    linarith only [hh]
  have hsecond : 960000 * CM / ((R:ℝ)^(9/10:ℝ) * (q:ℝ)^(19/40:ℝ)) ≤ ε/4 := by
    have hge : 4 * (10:ℝ)^6 * CM / ε ≤ (R:ℝ) ^ ((9:ℝ)/10) := by
      have h := Real.rpow_le_rpow hA₂pos.le hRleA₂ (by norm_num : (0:ℝ) ≤ 9/10)
      rwa [hA₂pow] at h
    have hqge1 : (1:ℝ) ≤ (q:ℝ)^(19/40:ℝ) :=
      Real.one_le_rpow hqR1 (by norm_num)
    have hb_le : 4 * (10:ℝ)^6 * CM / ε ≤ (R:ℝ)^(9/10:ℝ) * (q:ℝ)^(19/40:ℝ) := by
      calc 4 * (10:ℝ)^6 * CM / ε = (4 * (10:ℝ)^6 * CM / ε) * 1 := by ring
        _ ≤ (R:ℝ)^(9/10:ℝ) * (q:ℝ)^(19/40:ℝ) :=
            mul_le_mul hge hqge1 (by norm_num) (Real.rpow_nonneg hRpos.le _)
    have hquot : 960000 * CM / ((R:ℝ)^(9/10:ℝ) * (q:ℝ)^(19/40:ℝ))
        ≤ 960000 * CM / (4 * (10:ℝ)^6 * CM / ε) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hb_le
    have hval : 960000 * CM / (4 * (10:ℝ)^6 * CM / ε) = (24:ℝ)/100 * ε := by
      field_simp
      ring
    linarith only [hquot, hval, hε]
  -- the family hypotheses needed by `finset_boundJM`
  have hfamJ : ∀ σ T : ℝ, (4:ℝ)/5 ≤ σ → σ ≤ 1 → 1 ≤ T →
      ∑ χ : DirichletCharacter ℂ q, zeroCountIn χ σ T
        ≤ CJ * ((q:ℝ) * T) ^ ((2 + 1/1000) * (1 - σ)) :=
    fun σ T hσ hσ1 hT => hJ q hq2 σ T hσ hσ1 hT
  have hfamM : ∀ σ T : ℝ, 0 ≤ σ → σ ≤ 1 → 1 ≤ T →
      ∑ χ : DirichletCharacter ℂ q, zeroCountIn χ σ T
        ≤ CM * ((q:ℝ) * T) ^ ((2451/1000) * (1 - σ)) := by
    intro σ T hσ0 hσ1 hT
    have hb : (1:ℝ) ≤ (q:ℝ) * T := by
      have h2q : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq2
      nlinarith only [h2q, hT]
    have hbase0 : (0:ℝ) ≤ (q:ℝ) * T := le_of_lt (lt_of_lt_of_le one_pos hb)
    rcases le_total ((4:ℝ)/5) σ with hσ | hσ
    · have h1 := hJ q hq2 σ T hσ hσ1 hT
      refine le_trans h1 ?_
      have hmono : ((q:ℝ) * T) ^ ((2 + 1/1000) * (1 - σ))
          ≤ ((q:ℝ) * T) ^ ((2451/1000) * (1 - σ)) :=
        Real.rpow_le_rpow_of_exponent_le hb (by linarith only [hσ1])
      calc CJ * ((q:ℝ) * T) ^ ((2 + 1/1000) * (1 - σ))
          ≤ CM * ((q:ℝ) * T) ^ ((2 + 1/1000) * (1 - σ)) :=
            mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_of_eq hCMdef))
              (Real.rpow_nonneg hbase0 _)
        _ ≤ CM * ((q:ℝ) * T) ^ ((2451/1000) * (1 - σ)) :=
            mul_le_mul_of_nonneg_left hmono hCMpos.le
    · have h1 := hM q hq2 σ T hσ0 hσ hT
      rw [Real.rpow_one] at h1
      refine le_trans h1 ?_
      have hlog : Real.log ((q:ℝ) * T) ≤ 100 * ((q:ℝ) * T) ^ ((1:ℝ)/100) := by
        have h := log_rpow_le_mul_rpow (B := 1) (by norm_num) hb
        simpa using h
      have hstep1 : CM₀ * ((q:ℝ) * T) ^ (((12:ℝ)/5 + 1/1000) * (1 - σ))
            * Real.log ((q:ℝ) * T)
          ≤ CM₀ * ((q:ℝ) * T) ^ (((12:ℝ)/5 + 1/1000) * (1 - σ))
            * (100 * ((q:ℝ) * T) ^ ((1:ℝ)/100)) :=
        mul_le_mul_of_nonneg_left hlog
          (mul_nonneg hCM₀pos.le (Real.rpow_nonneg hbase0 _))
      refine le_trans hstep1 ?_
      have harg : (0:ℝ) < (q:ℝ) * T := lt_of_lt_of_le one_pos hb
      have hexpadd : ((q:ℝ) * T) ^ (((12:ℝ)/5 + 1/1000) * (1 - σ))
            * ((q:ℝ) * T) ^ ((1:ℝ)/100)
          = ((q:ℝ) * T) ^ (((12:ℝ)/5 + 1/1000) * (1 - σ) + 1/100) :=
        (Real.rpow_add harg _ _).symm
      rw [show CM₀ * ((q:ℝ) * T) ^ (((12:ℝ)/5 + 1/1000) * (1 - σ))
            * (100 * ((q:ℝ) * T) ^ ((1:ℝ)/100))
          = 100 * CM₀ * (((q:ℝ) * T) ^ (((12:ℝ)/5 + 1/1000) * (1 - σ))
            * ((q:ℝ) * T) ^ ((1:ℝ)/100)) by ring]
      rw [hexpadd]
      have hsumexp : ((12:ℝ)/5 + 1/1000) * (1 - σ) + 1/100 ≤ (2451/1000) * (1 - σ) := by
        linarith only [hσ]
      have hmono : ((q:ℝ) * T) ^ (((12:ℝ)/5 + 1/1000) * (1 - σ) + 1/100)
          ≤ ((q:ℝ) * T) ^ ((2451/1000) * (1 - σ)) :=
        Real.rpow_le_rpow_of_exponent_le hb hsumexp
      calc 100 * CM₀ * ((q:ℝ) * T) ^ (((12:ℝ)/5 + 1/1000) * (1 - σ) + 1/100)
          ≤ 100 * CM₀ * ((q:ℝ) * T) ^ ((2451/1000) * (1 - σ)) :=
            mul_le_mul_of_nonneg_left hmono (by positivity)
        _ ≤ CM * ((q:ℝ) * T) ^ ((2451/1000) * (1 - σ)) :=
            mul_le_mul_of_nonneg_right hCM₀le (Real.rpow_nonneg hbase0 _)
  -- the total far mass
  have hfin : ∀ u : Finset (DirichletCharacter ℂ q × ℂ), farMassSum R (Real.log (q:ℝ)) u ≤ ε := by
    intro u
    have hb := finset_boundJM q hq2 R hR1 CJ CM c0 hCJpos hCMpos hc0pos hfamJ hfamM hball hL u
    linarith only [hb, hfirst, hsecond, hthird]
  let F : DirichletCharacter ℂ q × ℂ → ℝ := fun z =>
    if z.1 = 1 then 0 else if InBox q (R:ℝ) z.2 then 0
      else (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * Real.log (q:ℝ))‖
  have hFbound : ∀ u : Finset (DirichletCharacter ℂ q × ℂ), ∑ z ∈ u, F z ≤ ε := fun u => hfin u
  have hFnn : 0 ≤ F := fun z => by
    show 0 ≤ (if z.1 = 1 then 0 else if InBox q (R:ℝ) z.2 then 0
      else (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * Real.log (q:ℝ))‖)
    split_ifs with h1 h2
    · exact le_refl 0
    · exact le_refl 0
    · exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hsumm : Summable F := summable_of_sum_le hFnn hFbound
  have htsum : ∑' z : DirichletCharacter ℂ q × ℂ, F z ≤ ε :=
    Real.tsum_le_of_sum_le hFnn hFbound
  rw [Summable.tsum_prod hsumm] at htsum
  rw [tsum_fintype] at htsum
  have hstep : (∑ χ : DirichletCharacter ℂ q, ∑' ρ : ℂ, F (χ, ρ))
      = ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          farSum q (11/2) (3/10) (R:ℝ) χ := by
    have h1z : (∑' ρ : ℂ, F ((1 : DirichletCharacter ℂ q), ρ)) = 0 := by
      rw [tsum_congr (fun ρ => ?_), tsum_zero]
      have hp : ((1 : DirichletCharacter ℂ q), ρ).1 = 1 := rfl
      show (if ((1 : DirichletCharacter ℂ q), ρ).1 = 1 then (0:ℝ) else _) = 0
      rw [if_pos hp]
    rw [← Finset.sum_erase_add _ (fun χ => ∑' ρ : ℂ, F (χ, ρ))
        (Finset.mem_univ (1 : DirichletCharacter ℂ q)), h1z, add_zero]
    refine Finset.sum_congr rfl (fun χ hχ => ?_)
    have hχ1 : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
    rw [farSum]
    refine tsum_congr (fun ρ => ?_)
    have hpt : (χ, ρ).1 ≠ 1 := by simpa using hχ1
    simp only [F]
    rw [if_neg hpt]
  rw [hstep] at htsum
  exact htsum

/-- **Area 2 from Jutila's log-free bound and Montgomery's density theorem.**

**Warning (the hypothesis is not a theorem).**  This route consumes
`FamilyZeroDensityJutila`, i.e. the log-free bound summed over **all** characters mod `q`; at
`σ = 4/5` its `χ = 1` term is a density estimate for `ζ` with exponent `2`, which is **not known**
(see `Work.LinnikAreas.NOTE_area2_principal_character.md`).  Only the *non-principal* form
`FamilyZeroDensityJutilaNP` is a theorem of the literature, and the routes through
`FamilyZeroDensityMesh` (`FarBoundHyp_of_jutila_and_mesh`, `area2_of_jutila_mesh`) consume it.
This theorem is kept because it is proved and harmless, but it should not be used as a target. -/
theorem area2_of_jutila_montgomery
    (hj : FamilyZeroDensityJutila) (hm : FamilyZeroDensityMontgomery) :
    Work.LinnikContract.Area2 :=
  area2_of_classIdentity ClassIdentity (FarBoundHyp_of_jutila_and_montgomery hj hm)

/-- **`FamilyZeroDensityMontgomery` from its middle range and the σ-blind count.** -/
theorem FamilyZeroDensityMontgomery_of_trivial_and_mid (htriv : TrivialFamilyCountForm)
    (hmid : FamilyZeroDensityMontgomeryMid) : FamilyZeroDensityMontgomery := by
  intro ε hε B hB
  obtain ⟨C₁, hC₁pos, h1⟩ := hmid ε hε B hB
  obtain ⟨C₂, hC₂pos, h2⟩ := htriv (5*ε/24) (by positivity)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2B : 0 < (Real.log 2) ^ B := Real.rpow_pos_of_pos hlog2pos B
  refine ⟨max C₁ (C₂ / (Real.log 2)^B), lt_max_of_lt_left hC₁pos, ?_⟩
  intro q hq _inst σ T hσ0 hσ4 hT
  have hq2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hbase : (1:ℝ) ≤ (q:ℝ) * T := by nlinarith
  have hbase0 : (0:ℝ) ≤ (q:ℝ) * T := by linarith
  have hlogq : (0:ℝ) ≤ Real.log ((q:ℝ) * T) := Real.log_nonneg hbase
  have hX : (0:ℝ) ≤ ((q:ℝ) * T) ^ (((12:ℝ)/5 + ε) * (1 - σ)) :=
    Real.rpow_nonneg hbase0 _
  have hY : (0:ℝ) ≤ (Real.log ((q:ℝ) * T)) ^ B := Real.rpow_nonneg hlogq _
  rcases le_total ((7:ℝ)/12) σ with hσ | hσ
  · have hb := h1 q hq σ T hσ hσ4 hT
    refine le_trans hb ?_
    have hC1le : C₁ ≤ max C₁ (C₂ / (Real.log 2)^B) := le_max_left _ _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC1le hX) hY
  · have hσ' : (5:ℝ)/12 ≤ 1 - σ := by linarith
    have hc : (0:ℝ) ≤ (12:ℝ)/5 + ε := by linarith
    have hmul := mul_le_mul_of_nonneg_left hσ' hc
    have hval : ((12:ℝ)/5 + ε) * (5/12) = 1 + 5*ε/12 := by ring
    have hexp : 1 + 5*ε/24 ≤ ((12:ℝ)/5 + ε) * (1 - σ) := by
      rw [hval] at hmul; linarith
    have hm : ((q:ℝ) * T) ^ (1 + 5*ε/24) ≤ ((q:ℝ) * T) ^ (((12:ℝ)/5 + ε) * (1 - σ)) :=
      Real.rpow_le_rpow_of_exponent_le hbase hexp
    have hlogge : Real.log 2 ≤ Real.log ((q:ℝ) * T) :=
      Real.log_le_log (by norm_num) (by nlinarith)
    have hlogpow : (Real.log 2) ^ B ≤ (Real.log ((q:ℝ) * T)) ^ B :=
      Real.rpow_le_rpow hlog2pos.le hlogge hB.le
    have hzero : (0:ℝ) ≤ ((q:ℝ) * T) ^ (1 + 5*ε/24) := Real.rpow_nonneg hbase0 _
    have h4 : (Real.log 2)^B * ((q:ℝ)*T)^(1 + 5*ε/24)
        ≤ ((q:ℝ) * T) ^ (((12:ℝ)/5 + ε) * (1 - σ)) * (Real.log ((q:ℝ) * T)) ^ B := by
      calc (Real.log 2)^B * ((q:ℝ)*T)^(1+5*ε/24)
          ≤ (Real.log ((q:ℝ)*T))^B * ((q:ℝ)*T)^(((12:ℝ)/5 + ε)*(1-σ)) :=
            mul_le_mul hlogpow hm hzero hY
        _ = ((q:ℝ)*T)^(((12:ℝ)/5 + ε)*(1-σ)) * (Real.log ((q:ℝ)*T))^B := by ring
    have h5 : C₂ * ((q:ℝ)*T)^(1+5*ε/24)
        ≤ (C₂ / (Real.log 2)^B)
          * (((q:ℝ) * T) ^ (((12:ℝ)/5 + ε) * (1 - σ)) * (Real.log ((q:ℝ) * T)) ^ B) := by
      have h6 := mul_le_mul_of_nonneg_left h4 (le_of_lt (div_pos hC₂pos hl2B))
      calc C₂ * ((q:ℝ)*T)^(1+5*ε/24)
          = (C₂ / (Real.log 2)^B) * ((Real.log 2)^B * ((q:ℝ)*T)^(1+5*ε/24)) := by
            rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hl2B)]
        _ ≤ (C₂ / (Real.log 2)^B)
              * (((q:ℝ) * T) ^ (((12:ℝ)/5 + ε) * (1 - σ)) * (Real.log ((q:ℝ) * T)) ^ B) := h6
    have h2b := h2 q hq σ T hσ0 (by linarith) hT
    refine le_trans (le_trans h2b h5) ?_
    have hmax : C₂ / (Real.log 2)^B ≤ max C₁ (C₂ / (Real.log 2)^B) := le_max_right _ _
    calc (C₂ / (Real.log 2)^B)
          * (((q:ℝ) * T) ^ (((12:ℝ)/5 + ε) * (1 - σ)) * (Real.log ((q:ℝ) * T)) ^ B)
        = ((C₂ / (Real.log 2)^B) * ((q:ℝ) * T) ^ (((12:ℝ)/5 + ε) * (1 - σ)))
            * (Real.log ((q:ℝ) * T)) ^ B := by ring
      _ ≤ (max C₁ (C₂ / (Real.log 2)^B) * ((q:ℝ) * T) ^ (((12:ℝ)/5 + ε) * (1 - σ)))
            * (Real.log ((q:ℝ) * T)) ^ B :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmax hX) hY

/-- **Area 2 from Jutila's bound, the middle range of Montgomery's theorem and the σ-blind
count.**

**Warning (the hypothesis is not a theorem).**  This route consumes
`FamilyZeroDensityJutila`, i.e. the log-free bound summed over **all** characters mod `q`; at
`σ = 4/5` its `χ = 1` term is a density estimate for `ζ` with exponent `2`, which is **not known**
(see `Work.LinnikAreas.NOTE_area2_principal_character.md`).  Only the *non-principal* form
`FamilyZeroDensityJutilaNP` is a theorem of the literature, and the routes through
`FamilyZeroDensityMesh` (`FarBoundHyp_of_jutila_and_mesh`, `area2_of_jutila_mesh`) consume it.
This theorem is kept because it is proved and harmless, but it should not be used as a target. -/
theorem area2_of_jutila_montgomery_mid (hj : FamilyZeroDensityJutila)
    (htriv : TrivialFamilyCountForm) (hmid : FamilyZeroDensityMontgomeryMid) :
    Work.LinnikContract.Area2 :=
  area2_of_jutila_montgomery hj (FamilyZeroDensityMontgomery_of_trivial_and_mid htriv hmid)



lemma msum_branch3sc (q : ℕ) (hq2 : 2 ≤ q) {L : ℝ} (hLp : 0 < L) (hL1 : 1 ≤ L)
    (hLdef : L = Real.log (q:ℝ)) (R : ℕ) {c0 : ℝ} (hc0 : 0 ≤ c0) (N : ℕ) {s : Finset ℕ}
    (hs : ∀ m ∈ s, (1021/5000)*L - 1 < (m:ℝ)) :
    (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * ((q:ℝ) * c0 * (4 + (2:ℝ)^k / L)
                * (Real.log (7 + (2:ℝ)^k / L) + Real.log (q:ℝ) + 2)))
      ≤ 60000 * c0 * L / (q:ℝ)^(29/50000:ℝ) := by
  classical
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hq0 : (0:ℝ) < (q:ℝ) := by linarith
  have hlogq0 : 0 ≤ Real.log (q:ℝ) := Real.log_nonneg hq1
  have hscale : ∀ k : ℕ, (2:ℝ)^k / L ≤ (2:ℝ)^k := by
    intro k
    rw [div_le_iff₀ hLp]
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) k]
  have hA_le : ∀ m k : ℕ,
      (q:ℝ) * c0 * (4 + (2:ℝ)^k / L) * (Real.log (7 + (2:ℝ)^k / L) + Real.log (q:ℝ) + 2)
        ≤ (q:ℝ) * c0 * (4 + (2:ℝ)^k) * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2) := by
    intro m k
    have hqc0 : (0:ℝ) ≤ (q:ℝ) * c0 := mul_nonneg hq0.le hc0
    have h1 : (0:ℝ) ≤ (4:ℝ) + (2:ℝ)^k / L := by positivity
    have h2 : (4:ℝ) + (2:ℝ)^k / L ≤ 4 + (2:ℝ)^k := by linarith only [hscale k]
    have h3 : (0:ℝ) ≤ Real.log (7 + (2:ℝ)^k / L) + Real.log (q:ℝ) + 2 := by
      have h5 : (0:ℝ) ≤ Real.log (7 + (2:ℝ)^k / L) := by
        apply Real.log_nonneg
        have : (0:ℝ) ≤ (2:ℝ)^k / L := by positivity
        linarith
      linarith [hlogq0]
    have h4 : Real.log (7 + (2:ℝ)^k / L) + Real.log (q:ℝ) + 2
        ≤ Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2 := by
      have h5 : Real.log (7 + (2:ℝ)^k / L) ≤ Real.log (7 + (2:ℝ)^k) := by
        apply Real.log_le_log (by positivity)
        linarith only [hscale k]
      linarith
    have h6 : (q:ℝ) * c0 * (4 + (2:ℝ)^k / L) ≤ (q:ℝ) * c0 * (4 + (2:ℝ)^k) :=
      mul_le_mul_of_nonneg_left h2 hqc0
    have hA1 : (0:ℝ) ≤ (q:ℝ) * c0 * (4 + (2:ℝ)^k / L) := mul_nonneg hqc0 h1
    have hB0 : (0:ℝ) ≤ Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2 := by
      have h5 : (0:ℝ) ≤ Real.log (7 + (2:ℝ)^k) := by
        apply Real.log_nonneg
        have : (0:ℝ) ≤ (2:ℝ)^k := by positivity
        linarith
      linarith [hlogq0]
    calc (q:ℝ) * c0 * (4 + (2:ℝ)^k / L) * (Real.log (7 + (2:ℝ)^k / L) + Real.log (q:ℝ) + 2)
        ≤ (q:ℝ) * c0 * (4 + (2:ℝ)^k / L) * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2) :=
          mul_le_mul_of_nonneg_left h4 hA1
      _ ≤ (q:ℝ) * c0 * (4 + (2:ℝ)^k) * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2) :=
          mul_le_mul_of_nonneg_right h6 hB0
  have hstep : ∀ m : ℕ, m ∈ s →
      Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * ((q:ℝ) * c0 * (4 + (2:ℝ)^k / L)
                * (Real.log (7 + (2:ℝ)^k / L) + Real.log (q:ℝ) + 2))
      ≤ Real.exp (-(49/10) * (m:ℝ)) * ((q:ℝ) * c0 * (10 * Real.log (q:ℝ) + 100)) := by
    intro m _
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
    have hdom : (∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
          * ((q:ℝ) * c0 * (4 + (2:ℝ)^k / L)
              * (Real.log (7 + (2:ℝ)^k / L) + Real.log (q:ℝ) + 2)))
        ≤ ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
          * ((q:ℝ) * c0 * (4 + (2:ℝ)^k)
              * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2)) :=
      Finset.sum_le_sum (fun k _ => by
        have hcell0 : (0:ℝ) ≤ cellLayer R m k := by rw [cellLayer]; split <;> norm_num
        exact mul_le_mul_of_nonneg_left (hA_le m k) (mul_nonneg (by positivity) hcell0))
    refine le_trans hdom ?_
    have hinner : (∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
          * ((q:ℝ) * c0 * (4 + (2:ℝ)^k)
              * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2)))
        ≤ (q:ℝ) * c0 * ∑ k ∈ Finset.range N, (1/4:ℝ)^k
            * ((4 + (2:ℝ)^k) * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun k _ => ?_)
      have hc1 : cellLayer R m k ≤ 1 := by rw [cellLayer]; split <;> norm_num
      have hqc0 : (0:ℝ) ≤ (q:ℝ) * c0 := mul_nonneg hq0.le hc0
      have h5 : (0:ℝ) ≤ Real.log (7 + (2:ℝ)^k) := by
        apply Real.log_nonneg
        have : (0:ℝ) ≤ (2:ℝ)^k := by positivity
        linarith
      have hAunn : (0:ℝ) ≤ (q:ℝ) * c0 * (4 + (2:ℝ)^k)
          * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2) :=
        mul_nonneg (mul_nonneg hqc0 (by positivity)) (by linarith only [h5, hlogq0])
      calc (1/4:ℝ)^k * cellLayer R m k
            * ((q:ℝ) * c0 * (4 + (2:ℝ)^k)
              * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2))
          ≤ (1/4:ℝ)^k * 1
            * ((q:ℝ) * c0 * (4 + (2:ℝ)^k)
              * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2)) := by
              refine mul_le_mul_of_nonneg_right ?_ hAunn
              exact mul_le_mul_of_nonneg_left hc1 (by positivity)
        _ = (q:ℝ) * c0 * ((1/4:ℝ)^k
              * ((4 + (2:ℝ)^k) * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2))) := by ring
    refine le_trans hinner ?_
    have h4 := sum_quarter_B_le hq1 N
    have hcc : (0:ℝ) ≤ (q:ℝ) * c0 := mul_nonneg hq0.le hc0
    exact mul_le_mul_of_nonneg_left h4 hcc
  have hsum : (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ)))
      ≤ 500 * Real.exp (-((50029/50000)*L)) := by
    have h := geom_exp_tail_gen (L := L) (b := 1021/5000) hLp hs
    have heq : (49/10) * (1021/5000) * L = (50029/50000) * L := by ring
    rwa [heq] at h
  have hqexp : (q:ℝ) = Real.exp L := by rw [hLdef, Real.exp_log hq0]
  have hqpow : Real.exp L * Real.exp (-((50029/50000)*L)) = (q:ℝ)^(-(29/50000:ℝ)) := by
    rw [← Real.exp_add, Real.rpow_def_of_pos hq0, ← hLdef]
    congr 1
    ring
  have hkey : 500 * (10*L + 100) ≤ 60000 * L := by linarith only [hL1]
  calc (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * ((q:ℝ) * c0 * (4 + (2:ℝ)^k / L)
                * (Real.log (7 + (2:ℝ)^k / L) + Real.log (q:ℝ) + 2)))
      ≤ ∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
          * ((q:ℝ) * c0 * (10 * Real.log (q:ℝ) + 100)) := Finset.sum_le_sum hstep
    _ = ((q:ℝ) * c0 * (10 * Real.log (q:ℝ) + 100)) * ∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ)) := by
          rw [← Finset.sum_mul]; ring
    _ = ((q:ℝ) * c0 * (10 * L + 100)) * ∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ)) := by rw [hLdef]
    _ ≤ ((q:ℝ) * c0 * (10 * L + 100)) * (500 * Real.exp (-((50029/50000)*L))) := by
          refine mul_le_mul_of_nonneg_left hsum ?_
          have hcc : (0:ℝ) ≤ (q:ℝ) * c0 := mul_nonneg hq0.le hc0
          positivity
    _ = 500 * (10*L + 100) * c0 * (Real.exp L * Real.exp (-((50029/50000)*L))) := by
          rw [hqexp]; ring
    _ = 500 * (10*L + 100) * c0 * (q:ℝ)^(-(29/50000:ℝ)) := by rw [hqpow]
    _ ≤ 60000 * c0 * L * (q:ℝ)^(-(29/50000:ℝ)) := by
          have hqnn : (0:ℝ) ≤ (q:ℝ)^(-(29/50000:ℝ)) := Real.rpow_nonneg hq0.le _
          have h1 : 500 * (10*L + 100) * c0 * (q:ℝ)^(-(29/50000:ℝ))
              ≤ 60000 * L * c0 * (q:ℝ)^(-(29/50000:ℝ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkey hc0) hqnn
          linarith only [h1]
    _ = 60000 * c0 * L / (q:ℝ)^(29/50000:ℝ) := by
          rw [Real.rpow_neg hq0.le]; ring

lemma msum_boundJMsh {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) {L : ℝ} (hLp : 0 < L)
    (hLdef : L = Real.log (q:ℝ)) (hL1 : 1 ≤ L) (R : ℕ) (hR1 : 1 ≤ R)
    {CJ CM c0 : ℝ} (hCJ : 0 < CJ) (hCM : 0 < CM) (hc0 : 0 < c0) (Mmax N : ℕ) :
    (∑ m ∈ Finset.range Mmax, Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * cellBoundJMsh q CJ CM c0 L m k)
      ≤ 100 * CJ / (R:ℝ)^(3/2:ℝ) + 30000 * CM / ((R:ℝ)^(9/10:ℝ) * (q:ℝ)^(23/50:ℝ))
        + 60000 * c0 * L / (q:ℝ)^(29/50000:ℝ) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range Mmax)
      (fun m : ℕ => ((m:ℝ)+1) ≤ (1021/5000)*L)
      (fun m => Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * cellBoundJMsh q CJ CM c0 L m k)]
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.range Mmax).filter
      (fun m : ℕ => ((m:ℝ)+1) ≤ (1021/5000)*L)) (fun m : ℕ => ((m:ℝ)+1) ≤ L/5)
      (fun m => Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * cellBoundJMsh q CJ CM c0 L m k)]
  have hA : (∑ m ∈ ((Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (1021/5000)*L)).filter
        (fun m : ℕ => ((m:ℝ)+1) ≤ L/5),
      Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
          * cellBoundJMsh q CJ CM c0 L m k)
      ≤ 100 * CJ / (R:ℝ)^(3/2:ℝ) := by
    have heq : (∑ m ∈ ((Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (1021/5000)*L)).filter
          (fun m : ℕ => ((m:ℝ)+1) ≤ L/5),
        Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * cellBoundJMsh q CJ CM c0 L m k)
        = (∑ m ∈ ((Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (1021/5000)*L)).filter
          (fun m : ℕ => ((m:ℝ)+1) ≤ L/5),
        Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * (CJ * ((q:ℝ) * (2:ℝ)^k) ^ ((2 + 1/1000) * (((m:ℝ) + 1)/L)))) := by
      refine Finset.sum_congr rfl (fun m hm => ?_)
      have hm1 : ((m:ℝ)+1) ≤ L/5 := (Finset.mem_filter.mp hm).2
      congr 1
      exact Finset.sum_congr rfl (fun k _ => by rw [cellBoundJMsh, if_pos hm1])
    rw [heq]
    exact JMAux.MsumBranch1 q hq2 hLp hLdef R hR1 hCJ Mmax N
      (fun m hm => (Finset.mem_filter.mp hm).2)
  have hB : (∑ m ∈ ((Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (1021/5000)*L)).filter
        (fun m : ℕ => ¬ (((m:ℝ)+1) ≤ L/5)),
      Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
          * cellBoundJMsh q CJ CM c0 L m k)
      ≤ 30000 * CM / ((R:ℝ)^(9/10:ℝ) * (q:ℝ)^(23/50:ℝ)) := by
    have heq : (∑ m ∈ ((Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (1021/5000)*L)).filter
          (fun m : ℕ => ¬ (((m:ℝ)+1) ≤ L/5)),
        Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * cellBoundJMsh q CJ CM c0 L m k)
        = (∑ m ∈ ((Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (1021/5000)*L)).filter
          (fun m : ℕ => ¬ (((m:ℝ)+1) ≤ L/5)),
        Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * (CM * ((q:ℝ) * (2:ℝ)^k) ^ ((2551/1000) * (((m:ℝ) + 1)/L)))) := by
      refine Finset.sum_congr rfl (fun m hm => ?_)
      have hm1 : ¬ (((m:ℝ)+1) ≤ L/5) := (Finset.mem_filter.mp hm).2
      have hm2 : ((m:ℝ)+1) ≤ (1021/5000)*L := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
      congr 1
      exact Finset.sum_congr rfl (fun k _ => by rw [cellBoundJMsh, if_neg hm1, if_pos hm2])
    rw [heq]
    refine JMAuxSh.MsumBranch2sh q hq2 hLp hLdef R hR1 hCM Mmax N ?_ ?_
    · intro m hm
      exact lt_of_not_ge (Finset.mem_filter.mp hm).2
    · intro m hm
      have h := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
      calc ((m:ℝ)+1) ≤ (1021/5000)*L := h
        _ ≤ (5/12)*L := by linarith
  have hC : (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ¬ (((m:ℝ)+1) ≤ (1021/5000)*L)),
      Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
          * cellBoundJMsh q CJ CM c0 L m k)
      ≤ 60000 * c0 * L / (q:ℝ)^(29/50000:ℝ) := by
    have heq : (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ¬ (((m:ℝ)+1) ≤ (1021/5000)*L)),
        Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * cellBoundJMsh q CJ CM c0 L m k)
        = (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ¬ (((m:ℝ)+1) ≤ (1021/5000)*L)),
        Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * cellLayer R m k
            * ((q:ℝ) * c0 * (4 + (2:ℝ)^k / L)
              * (Real.log (7 + (2:ℝ)^k / L) + Real.log (q:ℝ) + 2))) := by
      refine Finset.sum_congr rfl (fun m hm => ?_)
      have hm2 : ¬ (((m:ℝ)+1) ≤ (1021/5000)*L) := (Finset.mem_filter.mp hm).2
      have hm1 : ¬ (((m:ℝ)+1) ≤ L/5) := by
        intro h
        exact hm2 (le_trans h (by linarith))
      congr 1
      exact Finset.sum_congr rfl (fun k _ => by rw [cellBoundJMsh, if_neg hm1, if_neg hm2])
    rw [heq]
    refine msum_branch3sc q hq2 hLp hL1 hLdef R hc0.le N ?_
    intro m hm
    have h2 : (1021/5000)*L < (m:ℝ)+1 := lt_of_not_ge (Finset.mem_filter.mp hm).2
    linarith
  linarith only [hA, hB, hC]

/-- **The far-zero mass bound** under the pair of hypotheses (Jutila, Montgomery). -/

lemma finset_boundJMsh (q : ℕ) [NeZero q] (hq : 2 ≤ q) (R : ℕ) (hR : 1 ≤ R)
    (CJ CM c0 : ℝ) (hCJ : 0 < CJ) (hCM : 0 < CM) (hc0 : 0 < c0)
    (hfamJ : ∀ σ T : ℝ, (4:ℝ)/5 ≤ σ → σ ≤ 1 → 1 ≤ T →
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), zeroCountIn χ σ T
        ≤ CJ * ((q:ℝ) * T) ^ ((2 + 1/1000) * (1 - σ)))
    (hfams : ∀ σ T : ℝ, (1:ℝ) - 1021/5000 ≤ σ → σ ≤ (4:ℝ)/5 → 1 ≤ T →
      ∑ χ : DirichletCharacter ℂ q, zeroCountIn χ σ T
        ≤ CM * ((q:ℝ) * T) ^ ((2551/1000) * (1 - σ)))
    (hball : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ.IsPrimitive →
      ∀ (a : ℂ) (ρ : ℝ), 1 ≤ ρ →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ) : ℝ))
        ≤ c0 * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N:ℝ) + 2))
    (hL : 30000000 ≤ Real.log (q:ℝ))
    (S : Finset (DirichletCharacter ℂ q × ℂ)) :
    farMassSum R (Real.log (q:ℝ)) S
      ≤ 3200 * CJ / ((R:ℝ)^(3/2:ℝ)) + 960000 * CM / ((R:ℝ)^(9/10:ℝ) * (q:ℝ)^(23/50:ℝ))
        + 1920000 * c0 * Real.log (q:ℝ) / (q:ℝ)^(29/50000:ℝ) := by
  classical
  set L : ℝ := Real.log (q:ℝ) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith
  have hL1 : (1:ℝ) ≤ L := by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ z ∈ S, z.1 ≠ 1 → ¬ InBox q (R:ℝ) z.2 → zeroMult z.1 z.2 ≠ 0 →
      max (farM L z : ℝ) (farY L z) + 1 ≤ (2:ℝ)^K := by
    refine ⟨S.sup (fun z => Nat.ceil (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))), ?_⟩
    intro z hz _ _ _
    have h1 : Nat.ceil (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))
        ≤ S.sup (fun z => Nat.ceil (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))) :=
      Finset.le_sup (f := fun z => Nat.ceil
        (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))) hz
    have h2 : Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1)
        ≤ ((S.sup (fun z => Nat.ceil
          (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))) : ℕ) : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
    have h3 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) h2
    have h4 : (2:ℝ) ^ (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))
        = (max (farM L z : ℝ) (farY L z) + 1 : ℝ) :=
      Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
    rw [h4, Real.rpow_natCast] at h3
    exact h3
  have h1 := farMass_le_doubleSum (q := q) R hR hLpos (le_of_eq hLdef.symm) K S hK
  have hcell0 : ∀ m k : ℕ, 0 ≤ (1/4:ℝ)^k * cellLayer R m k := by
    intro m k
    have : (0:ℝ) ≤ cellLayer R m k := by rw [cellLayer]; split <;> norm_num
    positivity
  have h2 : (∑ m ∈ Finset.range (Nat.ceil L + 1), Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range (K+1), (1/4:ℝ)^k * cellLayer R m k
            * cellMult L (farPairs R S) m k)
      ≤ (∑ m ∈ Finset.range (Nat.ceil L + 1), Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range (K+1), (1/4:ℝ)^k * cellLayer R m k
            * cellBoundJMsh q CJ CM c0 L m k) := by
    refine Finset.sum_le_sum (fun m _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
    refine Finset.sum_le_sum (fun k _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (hcell0 m k)
    refine JMAuxSh.CellMultLeBoundJMsh hq hLpos hL1 hCJ hCM hc0 hfamJ hfams hball ?_ m k
    intro z hz
    rw [farPairs, Finset.mem_filter, Finset.mem_filter] at hz
    exact ⟨hz.1.2.1, hz.2⟩
  have h3 := msum_boundJMsh hq hLpos hLdef hL1 R hR hCJ hCM hc0 (Nat.ceil L + 1) (K+1)
  have h23 : (∑ m ∈ Finset.range (Nat.ceil L + 1), Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range (K+1), (1/4:ℝ)^k * cellLayer R m k
            * cellMult L (farPairs R S) m k)
      ≤ 100 * CJ / (R:ℝ)^(3/2:ℝ) + 30000 * CM / ((R:ℝ)^(9/10:ℝ) * (q:ℝ)^(23/50:ℝ))
        + 60000 * c0 * L / (q:ℝ)^(29/50000:ℝ) := le_trans h2 h3
  refine le_trans h1 ?_
  have hmul : 32 * ((∑ m ∈ Finset.range (Nat.ceil L + 1), Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range (K+1), (1/4:ℝ)^k * cellLayer R m k
            * cellMult L (farPairs R S) m k))
      ≤ 32 * (100 * CJ / (R:ℝ)^(3/2:ℝ) + 30000 * CM / ((R:ℝ)^(9/10:ℝ) * (q:ℝ)^(23/50:ℝ))
        + 60000 * c0 * L / (q:ℝ)^(29/50000:ℝ)) := mul_le_mul_of_nonneg_left h23 (by norm_num)
  refine le_trans hmul (le_of_eq ?_)
  ring


theorem FarBoundHyp_of_jutila_and_mesh
    (hj : FamilyZeroDensityJutilaNP) (hm : FamilyZeroDensityMesh) :
    FarBoundHyp := by
  obtain ⟨CJ, hCJpos, hJ⟩ := hj (1/1000) (by norm_num)
  obtain ⟨CMm, hCMmpos, hMm⟩ := hm (1/1000) (by norm_num)
  obtain ⟨c0, hc0pos, hball⟩ :=
    Commons.NumberTheory.DirichletCharacter.completedL_ballZeroCount_uniform
  set CM : ℝ := max CMm CJ with hCMdef
  have hCMpos : 0 < CM := lt_max_of_lt_left hCMmpos
  have hCMmle : CMm ≤ CM := le_max_left _ _
  intro ε hε
  have hε4 : 0 < ε/4 := by linarith
  set A₁ : ℝ := (6400 * CJ / ε) ^ ((2:ℝ)/3) with hA₁def
  set A₂ : ℝ := (4 * (10:ℝ)^6 * CM / ε) ^ ((10:ℝ)/9) with hA₂def
  have hA₁pos : 0 < A₁ := by rw [hA₁def]; exact Real.rpow_pos_of_pos (by positivity) _
  have hA₂pos : 0 < A₂ := by rw [hA₂def]; exact Real.rpow_pos_of_pos (by positivity) _
  set R : ℕ := Nat.floor (max A₁ A₂) + 2 with hRdef
  have hR1 : 1 ≤ R := by rw [hRdef]; omega
  have hRpos : (0:ℝ) < (R:ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hRleA₁ : A₁ ≤ (R:ℝ) := by
    have h1 : A₁ ≤ max A₁ A₂ := le_max_left _ _
    have h2 : max A₁ A₂ < ((Nat.floor (max A₁ A₂) : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : ((Nat.floor (max A₁ A₂) : ℕ) : ℝ) + 1 ≤ (R:ℝ) := by
      rw [hRdef]; push_cast; linarith only []
    linarith only [h1, h2, h3]
  have hRleA₂ : A₂ ≤ (R:ℝ) := by
    have h1 : A₂ ≤ max A₁ A₂ := le_max_right _ _
    have h2 : max A₁ A₂ < ((Nat.floor (max A₁ A₂) : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : ((Nat.floor (max A₁ A₂) : ℕ) : ℝ) + 1 ≤ (R:ℝ) := by
      rw [hRdef]; push_cast; linarith only []
    linarith only [h1, h2, h3]
  have hA₁pow : A₁ ^ ((3:ℝ)/2) = 6400 * CJ / ε := by
    rw [hA₁def, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 6400 * CJ / ε)]
    norm_num
  have hA₂pow : A₂ ^ ((9:ℝ)/10) = 4 * (10:ℝ)^6 * CM / ε := by
    rw [hA₂def, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 4 * (10:ℝ)^6 * CM / ε)]
    norm_num
  have hfirst : 3200 * CJ / (R:ℝ)^(3/2:ℝ) ≤ ε/2 := by
    have hge : 6400 * CJ / ε ≤ (R:ℝ) ^ ((3:ℝ)/2) := by
      have h := Real.rpow_le_rpow hA₁pos.le hRleA₁ (by norm_num : (0:ℝ) ≤ 3/2)
      rwa [hA₁pow] at h
    have hquot : 3200 * CJ / (R:ℝ)^(3/2:ℝ) ≤ 3200 * CJ / (6400 * CJ / ε) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hge
    have hval : 3200 * CJ / (6400 * CJ / ε) = ε/2 := by
      field_simp
      ring
    linarith only [hquot, hval]
  set B : ℝ := max 1 (7680000 * c0 / ε) with hBdef
  have hB1 : (1:ℝ) ≤ B := le_max_left _ _
  have hBge : 7680000 * c0 / ε ≤ B := le_max_right _ _
  set q₀ : ℕ := max (max (max (Nat.ceil (Real.exp 30000000))
    (Nat.ceil (4 * (1920000:ℝ) * c0 / ε))) (Nat.ceil (B ^ 3449))) 2 with hq₀def
  have hq₀2 : 2 ≤ q₀ := by rw [hq₀def]; exact le_max_right _ _
  have hq₀exp : Nat.ceil (Real.exp 30000000) ≤ q₀ := by
    rw [hq₀def]
    exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hq₀c : Nat.ceil (4 * (1920000:ℝ) * c0 / ε) ≤ q₀ := by
    rw [hq₀def]
    exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hq₀B : Nat.ceil (B ^ 3449) ≤ q₀ := by
    rw [hq₀def]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨(R:ℝ), hRpos, q₀, ?_⟩
  intro q hq hqN
  have hq2 : 2 ≤ q := le_trans hq₀2 hq
  have hqRpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hexpq : Real.exp 30000000 ≤ (q:ℝ) := by
    have h1 : Real.exp 30000000 ≤ ((Nat.ceil (Real.exp 30000000) : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (Real.exp 30000000) : ℕ) : ℝ) ≤ (q:ℝ) :=
      Nat.cast_le.mpr (le_trans hq₀exp hq)
    linarith only [h1, h2]
  have hL : 30000000 ≤ Real.log (q:ℝ) := by
    rw [← Real.log_exp 30000000]
    exact Real.log_le_log (Real.exp_pos 30000000) hexpq
  have hqbig : 4 * (1920000:ℝ) * c0 / ε ≤ (q:ℝ) := by
    have h1 : 4 * (1920000:ℝ) * c0 / ε
        ≤ ((Nat.ceil (4 * (1920000:ℝ) * c0 / ε) : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (4 * (1920000:ℝ) * c0 / ε) : ℕ) : ℝ) ≤ (q:ℝ) :=
      Nat.cast_le.mpr (le_trans hq₀c hq)
    linarith only [h1, h2]
  let P : ℝ := Real.exp ((29/100000) * Real.log (q:ℝ))
  have hPval : P = Real.exp ((29/100000) * Real.log (q:ℝ)) := rfl
  have hPpos : (0:ℝ) < P := by rw [hPval]; exact Real.exp_pos _
  have hqP : (q:ℝ)^((29:ℝ)/100000) = P := by
    rw [hPval, Real.rpow_def_of_pos hqRpos]
    congr 1
    ring
  have hqB : B ^ 3449 ≤ (q:ℝ) := by
    have h1 : B ^ 3449 ≤ ((Nat.ceil (B ^ 3449) : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (B ^ 3449) : ℕ) : ℝ) ≤ (q:ℝ) := Nat.cast_le.mpr (le_trans hq₀B hq)
    linarith
  have hBpos : (0:ℝ) < B := lt_of_lt_of_le zero_lt_one hB1
  have hBq : B ≤ P := by
    rw [← hqP]
    have h2 : (B ^ (3449:ℕ) : ℝ) ^ ((29:ℝ)/100000) ≤ (q:ℝ)^((29:ℝ)/100000) :=
      Real.rpow_le_rpow (by positivity) hqB (by norm_num)
    have h3 : (B ^ (3449:ℕ) : ℝ) ^ ((29:ℝ)/100000)
        = B ^ (((29:ℝ)/100000) * 3449) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hBpos)]
      congr 1
      ring
    have h1 : (1:ℝ) ≤ ((29:ℝ)/100000) * 3449 := by norm_num
    have h9 : B ≤ B ^ (((29:ℝ)/100000)*3449) := by
      have h10 := Real.rpow_le_rpow_of_exponent_le hB1 h1
      rwa [Real.rpow_one] at h10
    linarith only [h2, h3, h9]
  have hAg : 7680000 * c0 ≤ ε * P := by
    have h2 : 7680000 * c0 / ε ≤ P := le_trans hBge hBq
    rw [div_le_iff₀ hε] at h2
    linarith only [h2]
  have hLle : Real.log (q:ℝ) ≤ P := by
    rw [hPval]
    have hx : (0:ℝ) ≤ (29/100000) * Real.log (q:ℝ) := by
      have h1 : (0:ℝ) ≤ Real.log (q:ℝ) := by linarith only [hL]
      positivity
    have h2 := Real.pow_div_factorial_le_exp ((29/100000) * Real.log (q:ℝ)) hx 2
    have hbig : Real.log (q:ℝ) ≤ ((29/100000) * Real.log (q:ℝ))^2/2 := by
      have h3 : ((29:ℝ)/100000) = 0.00029 := by norm_num
      linarith only [mul_nonneg (by linarith only [hL] : (0:ℝ) ≤ Real.log (q:ℝ)) (sub_nonneg.2 hL), hL]
    linarith only [h2, hbig]
  have hthird : 1920000 * c0 * Real.log (q:ℝ) / (q:ℝ)^(29/50000:ℝ) ≤ ε/4 := by
    have hsplit : (q:ℝ)^(29/50000:ℝ) = P * P := by
      have hPQ : (q:ℝ)^((29:ℝ)/100000) = P := hqP
      rw [← hPQ, ← Real.rpow_add hqRpos]
      congr 1
      norm_num
    rw [hsplit, div_le_iff₀ (mul_pos hPpos hPpos)]
    have hc0 : (0:ℝ) ≤ c0 := le_of_lt hc0pos
    linarith only [mul_le_mul_of_nonneg_left hLle (mul_nonneg (by norm_num : (0:ℝ) ≤ 1920000) hc0), mul_le_mul_of_nonneg_right hAg hPpos.le]
  have hsecond : 960000 * CM / ((R:ℝ)^(9/10:ℝ) * (q:ℝ)^(23/50:ℝ)) ≤ ε/4 := by
    have hge : 4 * (10:ℝ)^6 * CM / ε ≤ (R:ℝ) ^ ((9:ℝ)/10) := by
      have h := Real.rpow_le_rpow hA₂pos.le hRleA₂ (by norm_num : (0:ℝ) ≤ 9/10)
      rwa [hA₂pow] at h
    have hqge1 : (1:ℝ) ≤ (q:ℝ)^(23/50:ℝ) :=
      Real.one_le_rpow hqR1 (by norm_num)
    have hb_le : 4 * (10:ℝ)^6 * CM / ε ≤ (R:ℝ)^(9/10:ℝ) * (q:ℝ)^(23/50:ℝ) := by
      calc 4 * (10:ℝ)^6 * CM / ε = (4 * (10:ℝ)^6 * CM / ε) * 1 := by ring
        _ ≤ (R:ℝ)^(9/10:ℝ) * (q:ℝ)^(23/50:ℝ) :=
            mul_le_mul hge hqge1 (by norm_num) (Real.rpow_nonneg hRpos.le _)
    have hquot : 960000 * CM / ((R:ℝ)^(9/10:ℝ) * (q:ℝ)^(23/50:ℝ))
        ≤ 960000 * CM / (4 * (10:ℝ)^6 * CM / ε) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hb_le
    have hval : 960000 * CM / (4 * (10:ℝ)^6 * CM / ε) = (24:ℝ)/100 * ε := by
      field_simp
      ring
    linarith only [hquot, hval, hε]
  -- the family hypotheses needed by `finset_boundJM`
  have hfamJ : ∀ σ T : ℝ, (4:ℝ)/5 ≤ σ → σ ≤ 1 → 1 ≤ T →
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), zeroCountIn χ σ T
        ≤ CJ * ((q:ℝ) * T) ^ ((2 + 1/1000) * (1 - σ)) :=
    fun σ T hσ hσ1 hT => hJ q hq2 σ T hσ hσ1 hT
  have hfams : ∀ σ T : ℝ, (1:ℝ) - 1021/5000 ≤ σ → σ ≤ (4:ℝ)/5 → 1 ≤ T →
      ∑ χ : DirichletCharacter ℂ q, zeroCountIn χ σ T
        ≤ CM * ((q:ℝ) * T) ^ ((2551/1000) * (1 - σ)) := by
    intro σ T hσ7 hσ45 hT
    have hb : (1:ℝ) ≤ (q:ℝ) * T := by
      have h2q : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq2
      nlinarith only [h2q, hT]
    have hbase0 : (0:ℝ) ≤ (q:ℝ) * T := le_of_lt (lt_of_lt_of_le one_pos hb)
    have h1 := hMm q hq2 σ T hσ7 hσ45 hT
    refine le_trans h1 ?_
    have hmono : ((q:ℝ) * T) ^ (((51:ℝ)/20 + 1/1000) * (1 - σ))
        ≤ ((q:ℝ) * T) ^ ((2551/1000) * (1 - σ)) := by
      refine Real.rpow_le_rpow_of_exponent_le hb ?_
      linarith
    calc CMm * ((q:ℝ) * T) ^ (((51:ℝ)/20 + 1/1000) * (1 - σ))
        ≤ CM * ((q:ℝ) * T) ^ (((51:ℝ)/20 + 1/1000) * (1 - σ)) :=
          mul_le_mul_of_nonneg_right (le_trans hCMmle (le_of_eq hCMdef)) (Real.rpow_nonneg hbase0 _)
      _ ≤ CM * ((q:ℝ) * T) ^ ((2551/1000) * (1 - σ)) :=
          mul_le_mul_of_nonneg_left hmono hCMpos.le
  -- the total far mass
  have hfin : ∀ u : Finset (DirichletCharacter ℂ q × ℂ), farMassSum R (Real.log (q:ℝ)) u ≤ ε := by
    intro u
    have hb := finset_boundJMsh q hq2 R hR1 CJ CM c0 hCJpos hCMpos hc0pos hfamJ hfams hball hL u
    linarith only [hb, hfirst, hsecond, hthird]
  let F : DirichletCharacter ℂ q × ℂ → ℝ := fun z =>
    if z.1 = 1 then 0 else if InBox q (R:ℝ) z.2 then 0
      else (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * Real.log (q:ℝ))‖
  have hFbound : ∀ u : Finset (DirichletCharacter ℂ q × ℂ), ∑ z ∈ u, F z ≤ ε := fun u => hfin u
  have hFnn : 0 ≤ F := fun z => by
    show 0 ≤ (if z.1 = 1 then 0 else if InBox q (R:ℝ) z.2 then 0
      else (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * Real.log (q:ℝ))‖)
    split_ifs with h1 h2
    · exact le_refl 0
    · exact le_refl 0
    · exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hsumm : Summable F := summable_of_sum_le hFnn hFbound
  have htsum : ∑' z : DirichletCharacter ℂ q × ℂ, F z ≤ ε :=
    Real.tsum_le_of_sum_le hFnn hFbound
  rw [Summable.tsum_prod hsumm] at htsum
  rw [tsum_fintype] at htsum
  have hstep : (∑ χ : DirichletCharacter ℂ q, ∑' ρ : ℂ, F (χ, ρ))
      = ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          farSum q (11/2) (3/10) (R:ℝ) χ := by
    have h1z : (∑' ρ : ℂ, F ((1 : DirichletCharacter ℂ q), ρ)) = 0 := by
      rw [tsum_congr (fun ρ => ?_), tsum_zero]
      have hp : ((1 : DirichletCharacter ℂ q), ρ).1 = 1 := rfl
      show (if ((1 : DirichletCharacter ℂ q), ρ).1 = 1 then (0:ℝ) else _) = 0
      rw [if_pos hp]
    rw [← Finset.sum_erase_add _ (fun χ => ∑' ρ : ℂ, F (χ, ρ))
        (Finset.mem_univ (1 : DirichletCharacter ℂ q)), h1z, add_zero]
    refine Finset.sum_congr rfl (fun χ hχ => ?_)
    have hχ1 : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
    rw [farSum]
    refine tsum_congr (fun ρ => ?_)
    have hpt : (χ, ρ).1 ≠ 1 := by simpa using hχ1
    simp only [F]
    rw [if_neg hpt]
  rw [hstep] at htsum
  exact htsum


/-- **Area 2 from Jutila's log-free bound and the log-free middle-range input.** -/
theorem area2_of_jutila_mesh (hj : FamilyZeroDensityJutilaNP) (hm : FamilyZeroDensityMesh) :
    Work.LinnikContract.Area2 :=
  area2_of_classIdentity ClassIdentity (FarBoundHyp_of_jutila_and_mesh hj hm)

/-- **Area 2 from Jutila's log-free bound and the *sharp* Montgomery exponent.**
This is the route that avoids Huxley's `12/5` estimate on the range `(3/4, 4/5]`. -/
theorem area2_of_jutila_montgomerySharp (hj : FamilyZeroDensityJutilaNP)
    (hm : FamilyZeroDensityMontgomerySharp) : Work.LinnikContract.Area2 :=
  area2_of_jutila_mesh hj (FamilyZeroDensityMesh_of_montgomerySharp hm)

end Work.LinnikAreas
