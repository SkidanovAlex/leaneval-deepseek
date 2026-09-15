import Submission.Work.GYFactor5

/-!
# The correlation system of Green–Tao §9 (their Proposition 9.6 / GY2)

For the correlation condition one must bound the average
`𝔼_x ∏_{i<m} Λ_R(W(x + h_i) + 1)²`
for the *degenerate* system of linear forms `x ↦ W(x + h_i) + 1` (`t = 1`, all linear parts equal to
`1`).  The existing §10 analysis (`GYFactor5`–`GYFactor10`) applies to systems whose linear parts are
pairwise non-proportional; here they coincide, so the local counts are different: for a prime `p`, the
system `θ_i(x) = 0` (`i ∈ Y`) has a solution mod `p` iff all the `h_i` (`i ∈ Y`) are congruent mod `p`,
and then the solution is unique.  Hence

* `vSys p σ = 1/p` when `σ.X ∪ σ.X'` is a single index,
* `vSys p σ = 0` when `|σ.X ∪ σ.X'| ≥ 2` and the `h_i` are pairwise DISTINCT mod `p`,
* `vSys p σ` can be `1/p` again when `|σ.X ∪ σ.X'| ≥ 2` and two of the `h_i` collide mod `p`.

The collisions happen only for primes dividing `Δ = ∏_{i<j} |h_i - h_j|`, which is exactly the
source of Green–Tao's extra factor `∏_{p | Δ}(1 + O_m(p^{-1/2}))`.

This file sets up the system and proves the basic local facts; the analytic estimates are in
`GYCorr2.lean`.
-/

open Finset
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj
namespace Corr

open Commons.NumberTheory.Sieve

variable {m : ℕ}

/-- The degenerate system: one variable, all linear coefficients `1`. -/
noncomputable def Ac (m : ℕ) : Fin m → Fin 1 → ℤ := fun _ _ => 1

@[simp] lemma Ac_apply (i : Fin m) (j : Fin 1) : Ac m i j = 1 := rfl

lemma Ac_ne_zero (m : ℕ) : ∀ i : Fin m, ∃ j : Fin 1, Ac m i j ≠ 0 := fun i => ⟨0, by simp⟩

lemma Ac_natAbs_le (m : ℕ) : ∀ i j, (Ac m i j).natAbs ≤ 1 := fun i j => by simp

/-- `θ_i(x) = W·(x_0 + h_i) + 1` for the degenerate system. -/
lemma theta_eq (W : ℕ) (h : Fin m → ℤ) (x : Fin 1 → ℤ) (i : Fin m) :
    GYMaj.BoxAvg.theta W (Ac m) h x i = (W : ℤ) * (x 0 + h i) + 1 := by
  simp [GYMaj.BoxAvg.theta, Ac]

/-- The natural number `Δ = ∏_{i < j} |h_i - h_j|` of Green–Tao's Proposition 9.6. -/
noncomputable def Delta (h : Fin m → ℤ) : ℕ :=
  ∏ i : Fin m, ∏ j ∈ Finset.univ.filter (fun j : Fin m => i < j), (h i - h j).natAbs

/-- A prime dividing a difference divides `Δ`. -/
lemma dvd_Delta_of_dvd {h : Fin m → ℤ} {p : ℕ} {i j : Fin m} (hij : i ≠ j)
    (hd : (p : ℤ) ∣ h i - h j) : p ∣ Delta h := by
  classical
  -- the inner product over the `j > i`
  have hinner : ∀ i j : Fin m, i < j →
      (h i - h j).natAbs ∣ ∏ j ∈ Finset.univ.filter (fun j : Fin m => i < j),
        (h i - h j).natAbs := by
    intro i j hij
    refine Finset.dvd_prod_of_mem _ ?_
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ j, hij⟩
  have houter : ∀ i : Fin m,
      (∏ j ∈ Finset.univ.filter (fun j : Fin m => i < j), (h i - h j).natAbs) ∣ Delta h := by
    intro i
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact dvd_trans (Int.natAbs_dvd_natAbs.mpr hd) (dvd_trans (hinner i j hlt) (houter i))
  · have hd' : (p : ℤ) ∣ h j - h i := by
      have := dvd_neg.mpr hd
      rwa [neg_sub] at this
    exact dvd_trans (Int.natAbs_dvd_natAbs.mpr hd') (dvd_trans (hinner j i hgt) (houter j))

/-- If `p` does not divide `Δ`, no difference `h_i - h_j` is divisible by `p`. -/
lemma not_dvd_sub_of_not_dvd_Delta {h : Fin m → ℤ} {p : ℕ} (hD : ¬ p ∣ Delta h) {i j : Fin m}
    (hij : i ≠ j) : ¬ (p : ℤ) ∣ h i - h j :=
  fun hd => hD (dvd_Delta_of_dvd hij hd)


/-- `θ_i` for the degenerate system, in `ZMod p`. -/
lemma thetaMod_eq (W : ℕ) (h : Fin m → ℤ) (p : ℕ) [NeZero p] (i : Fin m)
    (x : Fin 1 → ZMod p) :
    thetaMod W (Ac m) h p i x = (W : ZMod p) * (x 0 + ((h i : ℤ) : ZMod p)) + 1 := by
  rw [thetaMod]
  congr 2
  rw [Fin.sum_univ_one]
  simp [Ac]

/-- **The collision vanishing.**  If two indices of the subsystem indexed by `σ` have
non-congruent shifts mod `p` (and `p ∤ W`), the subsystem has no solution, so `vSys` vanishes. -/
lemma vSys_eq_zero_of_collision {W p : ℕ} {h : Fin m → ℤ} (hp : p.Prime) (hpW : ¬ p ∣ W)
    {i i' : Fin m} (hii' : i ≠ i') (hd : ¬ (p : ℤ) ∣ h i - h i') {σ : PrimeData m}
    (hi : i ∈ σ.X ∪ σ.X') (hi' : i' ∈ σ.X ∪ σ.X') :
    GYMaj.BoxAvg.vSys W (Ac m) h p σ = 0 := by
  classical
  haveI : NeZero p := NeZero.of_pos hp.pos
  haveI : Fact p.Prime := ⟨hp⟩
  have hWne : (W : ZMod p) ≠ 0 := by
    intro h0
    rw [show (W : ZMod p) = ((W : ℕ) : ZMod p) from rfl,
      CharP.cast_eq_zero_iff (ZMod p) p] at h0
    exact hpW h0
  have hempty : (Finset.univ : Finset (Fin 1 → ZMod p)).filter
      (fun x => ∀ i, p ∣ (if i ∈ σ.X ∪ σ.X' then p else 1) →
        thetaMod W (Ac m) h p i x = 0) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rw [Finset.mem_filter] at hx
    have h1 : thetaMod W (Ac m) h p i x = 0 :=
      hx.2 i (by rw [if_pos hi])
    have h2 : thetaMod W (Ac m) h p i' x = 0 :=
      hx.2 i' (by rw [if_pos hi'])
    rw [thetaMod_eq] at h1 h2
    have hA : (W : ZMod p) * (x 0 + ((h i : ℤ) : ZMod p)) = -1 :=
      eq_neg_of_add_eq_zero_left h1
    have hB : (W : ZMod p) * (x 0 + ((h i' : ℤ) : ZMod p)) = -1 :=
      eq_neg_of_add_eq_zero_left h2
    have hh : (W : ZMod p) * (x 0 + ((h i : ℤ) : ZMod p))
        = (W : ZMod p) * (x 0 + ((h i' : ℤ) : ZMod p)) := by rw [hA, hB]
    have h3 : (W : ZMod p) * (((h i : ℤ) : ZMod p) - ((h i' : ℤ) : ZMod p)) = 0 := by
      have hsub : (W : ZMod p) * (x 0 + ((h i : ℤ) : ZMod p))
          - (W : ZMod p) * (x 0 + ((h i' : ℤ) : ZMod p)) = 0 := sub_eq_zero.mpr hh
      linear_combination hsub
    have h4 : ((h i : ℤ) : ZMod p) - ((h i' : ℤ) : ZMod p) = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h hWne
      · exact h
    have h5 : ((h i - h i' : ℤ) : ZMod p) = 0 := by
      rw [Int.cast_sub]
      exact h4
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h5
    exact hd h5
  rw [GYMaj.BoxAvg.vSys, dif_pos hp]
  have hloc : locCount W (Ac m) h (fun i => if i ∈ σ.X ∪ σ.X' then p else 1) p = 0 := by
    rw [locCount, hempty, Finset.card_empty]
  rw [hloc]
  simp

/-- A set of size at least `2` contains two indices whose shifts are non-congruent mod `p`, as soon
as `p ∤ Δ`. -/
lemma exists_collision_free {h : Fin m → ℤ} {p : ℕ} (hD : ¬ p ∣ Delta h) {Y : Finset (Fin m)}
    (hY : 2 ≤ Y.card) : ∃ i ∈ Y, ∃ i' ∈ Y, i ≠ i' ∧ ¬ (p : ℤ) ∣ h i - h i' := by
  classical
  have hY' : 1 < Y.card := by omega
  rw [Finset.one_lt_card] at hY'
  obtain ⟨i, hi, i', hi', hne⟩ := hY'
  exact ⟨i, hi, i', hi', hne, not_dvd_sub_of_not_dvd_Delta hD hne⟩

/-- **The second-order local weight vanishes off the primes of `Δ`.** -/
theorem vSys_eq_zero_of_card_two {W p : ℕ} {h : Fin m → ℤ} (hp : p.Prime) (hpW : ¬ p ∣ W)
    (hD : ¬ p ∣ Delta h) {σ : PrimeData m} (hσ : 2 ≤ (σ.X ∪ σ.X').card) :
    GYMaj.BoxAvg.vSys W (Ac m) h p σ = 0 := by
  obtain ⟨i, hi, i', hi', hne, hd⟩ := exists_collision_free hD hσ
  exact vSys_eq_zero_of_collision hp hpW hne hd hi hi'


/-- A single active index gives the density `1/p`. -/
lemma vSys_eq_inv_of_card_one_corr {W p : ℕ} {h : Fin m → ℤ} (hp : p.Prime) (hpW : ¬ p ∣ W)
    (hW0 : 0 < W) {σ : PrimeData m} (hcard : (σ.X ∪ σ.X').card = 1) :
    GYMaj.BoxAvg.vSys W (Ac m) h p σ = ((p : ℂ))⁻¹ := by
  haveI : NeZero p := NeZero.of_pos hp.pos
  rw [GYMaj.BoxAvg.vSys, dif_pos hp,
    Commons.NumberTheory.Sieve.locCount_one_active hp W 1 (Ac m) h σ (le_refl 1)
      (Ac_natAbs_le m) (Ac_ne_zero m) hW0 hpW hp.one_lt hcard]
  rw [show (1 - 1) = 0 from rfl, pow_zero, Nat.cast_one, pow_one, one_div]

namespace CorrB

open GYMaj.BoxAvg

/-- The individual Euler-product summand (`Green–Tao`'s `E_p`, expanded). -/
noncomputable def eTerm (W : ℕ) (h : Fin m → ℤ) (z z' : Fin m → ℂ) (p : ℕ)
    (σ : PrimeData m) : ℂ :=
  GYMaj.BoxAvg.eTerm W (Ac m) h z z' p σ

lemma eulerFactor_eq_sum_eTerm (W : ℕ) (h : Fin m → ℤ) (z z' : Fin m → ℂ) (p : ℕ) :
    eulerFactor m (GYMaj.BoxAvg.vSys W (Ac m) h) z z' p
      = ∑ σ : PrimeData m, eTerm W h z z' p σ := rfl

lemma eTerm_zero (W : ℕ) (h : Fin m → ℤ) (z z' : Fin m → ℂ) (p : ℕ) :
    eTerm W h z z' p (0 : PrimeData m) = 1 := by
  have hX : (0 : PrimeData m).X = ∅ := rfl
  have hX' : (0 : PrimeData m).X' = ∅ := rfl
  rw [eTerm, GYMaj.BoxAvg.eTerm, GYMaj.BoxAvg.vSys_zero, hX, hX']
  simp

lemma eTerm_single_left {W p : ℕ} (h : Fin m → ℤ) (hp : p.Prime) (hpW : ¬ p ∣ W)
    (hW0 : 0 < W) (z z' : Fin m → ℂ) (j : Fin m) :
    eTerm W h z z' p ⟨{j}, ∅⟩ = -((p : ℂ) ^ (-(1 + z j))) := by
  have hcard : ((⟨{j}, ∅⟩ : PrimeData m).X ∪ (⟨{j}, ∅⟩ : PrimeData m).X').card = 1 := by simp
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  rw [eTerm, GYMaj.BoxAvg.eTerm, vSys_eq_inv_of_card_one_corr hp hpW hW0 hcard]
  simp only [Finset.card_singleton, Finset.card_empty, add_zero, Finset.prod_singleton,
    Finset.prod_empty, mul_one]
  rw [show (-1 : ℂ) ^ (1 + 0) = -1 by norm_num]
  rw [show (p : ℂ)⁻¹ * -1 * (p : ℂ) ^ (-(z j)) = -((p : ℂ)⁻¹ * (p : ℂ) ^ (-(z j))) by ring,
    GYMaj.BoxAvg.inv_mul_cpow p hp0 (z j)]

lemma eTerm_single_right {W p : ℕ} (h : Fin m → ℤ) (hp : p.Prime) (hpW : ¬ p ∣ W)
    (hW0 : 0 < W) (z z' : Fin m → ℂ) (j : Fin m) :
    eTerm W h z z' p ⟨∅, {j}⟩ = -((p : ℂ) ^ (-(1 + z' j))) := by
  have hcard : ((⟨∅, {j}⟩ : PrimeData m).X ∪ (⟨∅, {j}⟩ : PrimeData m).X').card = 1 := by simp
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  rw [eTerm, GYMaj.BoxAvg.eTerm, vSys_eq_inv_of_card_one_corr hp hpW hW0 hcard]
  simp only [Finset.card_singleton, Finset.card_empty, zero_add, Finset.prod_singleton,
    Finset.prod_empty, mul_one]
  rw [show (-1 : ℂ) ^ (0 + 1) = -1 by norm_num]
  rw [one_mul, show (p : ℂ)⁻¹ * -1 * (p : ℂ) ^ (-(z' j))
      = -((p : ℂ)⁻¹ * (p : ℂ) ^ (-(z' j))) by ring, GYMaj.BoxAvg.inv_mul_cpow p hp0 (z' j)]

lemma eTerm_single_both {W p : ℕ} (h : Fin m → ℤ) (hp : p.Prime) (hpW : ¬ p ∣ W)
    (hW0 : 0 < W) (z z' : Fin m → ℂ) (j : Fin m) :
    eTerm W h z z' p ⟨{j}, {j}⟩ = (p : ℂ) ^ (-(1 + z j + z' j)) := by
  have hcard : ((⟨{j}, {j}⟩ : PrimeData m).X ∪ (⟨{j}, {j}⟩ : PrimeData m).X').card = 1 := by
    simp
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  rw [eTerm, GYMaj.BoxAvg.eTerm, vSys_eq_inv_of_card_one_corr hp hpW hW0 hcard]
  simp only [Finset.card_singleton, Finset.prod_singleton]
  rw [show (-1 : ℂ) ^ (1 + 1) = 1 by norm_num, mul_one]
  rw [show ((p : ℂ))⁻¹ * ((p : ℂ) ^ (-(z j)) * (p : ℂ) ^ (-(z' j)))
      = ((p : ℂ))⁻¹ * (p : ℂ) ^ (-(z j)) * (p : ℂ) ^ (-(z' j)) by ring]
  rw [GYMaj.BoxAvg.inv_mul_cpow p hp0 (z j), ← Complex.cpow_add _ _ hp0]
  congr 1
  ring

/-- The sum over the data with `|σ.X ∪ σ.X'| = 1` is `-eLin`. -/
lemma sum_card_one_eTerm {W p : ℕ} (h : Fin m → ℤ) (hp : p.Prime) (hpW : ¬ p ∣ W)
    (hW0 : 0 < W) (z z' : Fin m → ℂ) :
    (∑ σ ∈ Finset.univ.filter (fun σ : PrimeData m => (σ.X ∪ σ.X').card = 1),
        eTerm W h z z' p σ) = - GYMaj.BoxAvg.eLin z z' p := by
  rw [Commons.NumberTheory.Sieve.sum_filter_card_one,
    Finset.sum_congr rfl (fun j _ => eTerm_single_left h hp hpW hW0 z z' j),
    Finset.sum_congr rfl (fun j _ => eTerm_single_right h hp hpW hW0 z z' j),
    Finset.sum_congr rfl (fun j _ => eTerm_single_both h hp hpW hW0 z z' j)]
  simp only [GYMaj.BoxAvg.eLin, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  ring

/-- **The exact expansion off the primes of `Δ`**: for `p ∤ W·Δ` the local factor is exactly
`1 - eLin`. -/
theorem eulerFactor_eq_one_sub_eLin {W p : ℕ} {h : Fin m → ℤ} (hp : p.Prime) (hpW : ¬ p ∣ W)
    (hW0 : 0 < W) (hD : ¬ p ∣ Delta h) (z z' : Fin m → ℂ) :
    eulerFactor m (GYMaj.BoxAvg.vSys W (Ac m) h) z z' p
      = 1 - GYMaj.BoxAvg.eLin z z' p := by
  have hhigh : (∑ σ ∈ Finset.univ.filter (fun σ : PrimeData m => 2 ≤ (σ.X ∪ σ.X').card),
      eTerm W h z z' p σ) = 0 := by
    refine Finset.sum_eq_zero (fun σ hσ => ?_)
    rw [Finset.mem_filter] at hσ
    rw [eTerm, GYMaj.BoxAvg.eTerm, vSys_eq_zero_of_card_two hp hpW hD hσ.2]
    simp
  rw [eulerFactor_eq_sum_eTerm, Commons.NumberTheory.Sieve.sum_univ_eq_sum_three,
    eTerm_zero, sum_card_one_eTerm h hp hpW hW0 z z', hhigh]
  ring

/-- **The `E^{(1)}` estimate for the correlation system**: for `p ∤ W·Δ` the first local factor of
the degenerate system `θ_i(x) = W(x + h_i) + 1` satisfies `E_p^{(1)} = 1 + O_m(p^{-2+2σ₀m} + p^{-2+4σ₀})`
on the strip (`p` prime, `p ∤ W·Δ`).  Proof: the second-order local weights vanish exactly
(`eulerFactor_eq_one_sub_eLin`), so the expansion of `E1p` has no remainder term. -/
theorem E1p_bound_corr {W p : ℕ} {h : Fin m → ℤ} (hm : 1 ≤ m) (hp : p.Prime) (hpW : ¬ p ∣ W)
    (hW0 : 0 < W) (hD : ¬ p ∣ Delta h)
    {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) (hσ₀1 : 4 * σ₀ ≤ 1) {z z' : Fin m → ℂ}
    (hz : ∀ j, -σ₀ ≤ (z j).re) (hz' : ∀ j, -σ₀ ≤ (z' j).re)
    (hsmall : (m : ℝ) * (2 * (p : ℝ) ^ (-1 + σ₀) + (p : ℝ) ^ (-1 + 2 * σ₀)) ≤ 1 / 2) :
    ‖E1p W (Ac m) h z z' p - 1‖ ≤ 100000 * ((m : ℝ) ^ 3 + 1) * (4 : ℝ) ^ m
      * ((p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀)) := by
  have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hp0R : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h4m0 : (0 : ℝ) ≤ (4 : ℝ) ^ m := by positivity
  obtain ⟨hca, hcb, hcc⟩ := cpow_bounds (m := m) (p := p) hp.one_le (σ₀ := σ₀) hz hz'
  have hA0 : (0 : ℝ) ≤ (p : ℝ) ^ (-1 + σ₀) := Real.rpow_nonneg (le_of_lt hp0R) _
  have hC0 : (0 : ℝ) ≤ (p : ℝ) ^ (-1 + 2 * σ₀) := Real.rpow_nonneg (le_of_lt hp0R) _
  have hA1 : (p : ℝ) ^ (-1 + σ₀) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le hp1R (show -1 + σ₀ ≤ 0 by linarith)
    rwa [Real.rpow_zero] at h
  have hC1 : (p : ℝ) ^ (-1 + 2 * σ₀) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le hp1R (show -1 + 2 * σ₀ ≤ 0 by linarith)
    rwa [Real.rpow_zero] at h
  obtain ⟨S, hS, hSeq⟩ := Commons.Analysis.Complex.inv_prod_three_expansion (m := m) z z'
    (A := (p : ℝ) ^ (-1 + σ₀)) (C := (p : ℝ) ^ (-1 + 2 * σ₀)) hA0 hC0 hA1 hC1 hsmall
    hca hcb hcc
  have hReq := eulerFactor_eq_one_sub_eLin hp hpW hW0 hD z z'
  have hE3def : E3p z z' p = ∏ j, ((1 - (p : ℂ) ^ (-(1 + z j)))
      * (1 - (p : ℂ) ^ (-(1 + z' j))) * (1 - (p : ℂ) ^ (-(1 + z j + z' j)))⁻¹) := by
    rw [E3p, if_pos hp]
  have hE3inv : (E3p z z' p)⁻¹ = 1 + eLin z z' p + S := by
    rw [hE3def, hSeq, eLin]
  have hE1def : E1p W (Ac m) h z z' p
      = eulerFactor m (GYMaj.BoxAvg.vSys W (Ac m) h) z z' p / E3p z z' p := by
    rw [GYMaj.BoxAvg.E1p, if_pos ⟨hp, hpW⟩]
  have hId : E1p W (Ac m) h z z' p - 1 = S - (eLin z z' p) ^ 2 - eLin z z' p * S := by
    rw [hE1def, div_eq_mul_inv, hE3inv, hReq]
    ring
  have htri : ‖E1p W (Ac m) h z z' p - 1‖ ≤ ‖S‖ + ‖eLin z z' p‖ ^ 2 + ‖eLin z z' p‖ * ‖S‖ := by
    rw [hId]
    have h1 : ‖S - (eLin z z' p) ^ 2 - eLin z z' p * S‖
        ≤ ‖S - (eLin z z' p) ^ 2‖ + ‖eLin z z' p * S‖ := norm_sub_le _ _
    have h2 : ‖S - (eLin z z' p) ^ 2‖ ≤ ‖S‖ + ‖(eLin z z' p) ^ 2‖ := norm_sub_le _ _
    have h3 : ‖(eLin z z' p) ^ 2‖ = ‖eLin z z' p‖ ^ 2 := norm_pow _ _
    have h4 : ‖eLin z z' p * S‖ = ‖eLin z z' p‖ * ‖S‖ := norm_mul _ _
    linarith [h1, h2, h3, h4]
  have hLhalf : ‖eLin z z' p‖ ≤ 1 / 2 := by
    have h := norm_eLin_le (m := m) (p := p) hp.one_le (σ₀ := σ₀) hz hz'
    linarith [h, hsmall]
  have hD0 : (0 : ℝ) ≤ (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀) :=
    add_nonneg (Real.rpow_nonneg (le_of_lt hp0R) _) (Real.rpow_nonneg (le_of_lt hp0R) _)
  have hD2le : (p : ℝ) ^ (-2 + 4 * σ₀)
      ≤ (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀) :=
    le_add_of_nonneg_left (Real.rpow_nonneg (le_of_lt hp0R) _)
  have hD1le : (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ))
      ≤ (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀) :=
    le_add_of_nonneg_right (Real.rpow_nonneg (le_of_lt hp0R) _)
  have hA2eq : ((p : ℝ) ^ (-1 + σ₀)) ^ 2 = (p : ℝ) ^ (-2 + 2 * σ₀) := by
    rw [sq, ← Real.rpow_add hp0R]; congr 1; ring
  have hACeq : (p : ℝ) ^ (-1 + σ₀) * (p : ℝ) ^ (-1 + 2 * σ₀) = (p : ℝ) ^ (-2 + 3 * σ₀) := by
    rw [← Real.rpow_add hp0R]; congr 1; ring
  have hC2eq : ((p : ℝ) ^ (-1 + 2 * σ₀)) ^ 2 = (p : ℝ) ^ (-2 + 4 * σ₀) := by
    rw [sq, ← Real.rpow_add hp0R]; congr 1; ring
  have hA2le : ((p : ℝ) ^ (-1 + σ₀)) ^ 2 ≤ (p : ℝ) ^ (-2 + 4 * σ₀) := by
    rw [hA2eq]; exact Real.rpow_le_rpow_of_exponent_le hp1R (by linarith)
  have hACle : (p : ℝ) ^ (-1 + σ₀) * (p : ℝ) ^ (-1 + 2 * σ₀) ≤ (p : ℝ) ^ (-2 + 4 * σ₀) := by
    rw [hACeq]; exact Real.rpow_le_rpow_of_exponent_le hp1R (by linarith)
  have hC2le : ((p : ℝ) ^ (-1 + 2 * σ₀)) ^ 2 ≤ (p : ℝ) ^ (-2 + 4 * σ₀) := by rw [hC2eq]
  have hS2 : ‖S‖ ≤ 30000 * ((m : ℝ) ^ 2 + m) * (p : ℝ) ^ (-2 + 4 * σ₀) := by
    have hsum : ((p : ℝ) ^ (-1 + σ₀)) ^ 2 + (p : ℝ) ^ (-1 + σ₀) * (p : ℝ) ^ (-1 + 2 * σ₀)
        + ((p : ℝ) ^ (-1 + 2 * σ₀)) ^ 2 ≤ 3 * (p : ℝ) ^ (-2 + 4 * σ₀) := by
      linarith [hA2le, hACle, hC2le]
    calc ‖S‖ ≤ 10000 * ((m : ℝ) ^ 2 + m)
          * (((p : ℝ) ^ (-1 + σ₀)) ^ 2 + (p : ℝ) ^ (-1 + σ₀) * (p : ℝ) ^ (-1 + 2 * σ₀)
              + ((p : ℝ) ^ (-1 + 2 * σ₀)) ^ 2) := hS
      _ ≤ 10000 * ((m : ℝ) ^ 2 + m) * (3 * (p : ℝ) ^ (-2 + 4 * σ₀)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 30000 * ((m : ℝ) ^ 2 + m) * (p : ℝ) ^ (-2 + 4 * σ₀) := by ring
  have hS1 : ‖S‖ ≤ 30000 * ((m : ℝ) ^ 2 + m)
      * ((p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀)) :=
    le_trans hS2 (mul_le_mul_of_nonneg_left hD2le (by positivity))
  have hLsq : ‖eLin z z' p‖ ^ 2 ≤ 9 * (m : ℝ) ^ 2
      * ((p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀)) := by
    have h1 : ‖eLin z z' p‖ ^ 2
        ≤ ((m : ℝ) * (2 * (p : ℝ) ^ (-1 + σ₀) + (p : ℝ) ^ (-1 + 2 * σ₀))) ^ 2 := by
      have h := norm_eLin_le (m := m) (p := p) hp.one_le (σ₀ := σ₀) hz hz'
      have h0 : (0 : ℝ) ≤ (m : ℝ) * (2 * (p : ℝ) ^ (-1 + σ₀) + (p : ℝ) ^ (-1 + 2 * σ₀)) :=
        mul_nonneg (by positivity) (by linarith [hA0, hC0])
      nlinarith [h, norm_nonneg (eLin z z' p), h0]
    have h4 : (2 * (p : ℝ) ^ (-1 + σ₀) + (p : ℝ) ^ (-1 + 2 * σ₀)) ^ 2
        ≤ 9 * (p : ℝ) ^ (-2 + 4 * σ₀) := by
      have hsq : (2 * (p : ℝ) ^ (-1 + σ₀) + (p : ℝ) ^ (-1 + 2 * σ₀)) ^ 2
          = 4 * ((p : ℝ) ^ (-1 + σ₀)) ^ 2
            + 4 * ((p : ℝ) ^ (-1 + σ₀) * (p : ℝ) ^ (-1 + 2 * σ₀))
            + ((p : ℝ) ^ (-1 + 2 * σ₀)) ^ 2 := by ring
      rw [hsq]; linarith [hA2le, hACle, hC2le]
    calc ‖eLin z z' p‖ ^ 2
        ≤ ((m : ℝ) * (2 * (p : ℝ) ^ (-1 + σ₀) + (p : ℝ) ^ (-1 + 2 * σ₀))) ^ 2 := h1
      _ = (m : ℝ) ^ 2 * (2 * (p : ℝ) ^ (-1 + σ₀) + (p : ℝ) ^ (-1 + 2 * σ₀)) ^ 2 := by ring
      _ ≤ (m : ℝ) ^ 2 * (9 * (p : ℝ) ^ (-2 + 4 * σ₀)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ 9 * (m : ℝ) ^ 2
            * ((p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀)) := by
          nlinarith [hD2le, sq_nonneg (m : ℝ)]
  have hLS : ‖eLin z z' p‖ * ‖S‖ ≤ 15000 * ((m : ℝ) ^ 2 + m)
      * ((p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀)) := by
    have h := mul_le_mul hLhalf hS2 (norm_nonneg S) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    refine le_trans h ?_
    have he : (1 / 2 : ℝ) * (30000 * ((m : ℝ) ^ 2 + m) * (p : ℝ) ^ (-2 + 4 * σ₀))
        = 15000 * ((m : ℝ) ^ 2 + m) * (p : ℝ) ^ (-2 + 4 * σ₀) := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hD2le (by positivity)
  have hsum : ‖S‖ + ‖eLin z z' p‖ ^ 2 + ‖eLin z z' p‖ * ‖S‖
      ≤ (30000 * ((m : ℝ) ^ 2 + m) + 9 * (m : ℝ) ^ 2 + 15000 * ((m : ℝ) ^ 2 + m))
        * ((p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀)) := by
    nlinarith [hS1, hLsq, hLS, hD0]
  have hsum2 : (30000 * ((m : ℝ) ^ 2 + m) + 9 * (m : ℝ) ^ 2 + 15000 * ((m : ℝ) ^ 2 + m))
        * ((p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀))
      ≤ (30000 * ((m : ℝ) ^ 2 + m) + 9 * (m : ℝ) ^ 2 + 15000 * ((m : ℝ) ^ 2 + m)
          + (4 : ℝ) ^ m + (4 : ℝ) ^ m + 30000 * (4 : ℝ) ^ m * ((m : ℝ) ^ 2 + m))
        * ((p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀)) := by
    refine mul_le_mul_of_nonneg_right ?_ hD0
    nlinarith [h4m0, mul_nonneg h4m0 (by positivity : (0 : ℝ) ≤ ((m : ℝ) ^ 2 + m))]
  have hconst : 30000 * ((m : ℝ) ^ 2 + m) + 9 * (m : ℝ) ^ 2 + 15000 * ((m : ℝ) ^ 2 + m)
      + (4 : ℝ) ^ m + (4 : ℝ) ^ m + 30000 * (4 : ℝ) ^ m * ((m : ℝ) ^ 2 + m)
      ≤ 100000 * ((m : ℝ) ^ 3 + 1) * (4 : ℝ) ^ m := by
    have h4m : (1 : ℝ) ≤ (4 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    have hkey : (m : ℝ) ^ 2 + m ≤ (m : ℝ) ^ 3 + 1 := by
      have h := mul_nonneg (sq_nonneg ((m : ℝ) - 1)) (show (0 : ℝ) ≤ (m : ℝ) + 1 by linarith)
      nlinarith [h]
    have hm2' : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 + 1 := by nlinarith [hkey, hm1R, sq_nonneg (m : ℝ)]
    have hP1 : (1 : ℝ) ≤ (m : ℝ) ^ 3 + 1 := by nlinarith [hm1R, sq_nonneg (m : ℝ)]
    nlinarith [h4m, hm1R, hkey, hm2', hP1, sq_nonneg (m : ℝ)]
  refine le_trans htri (le_trans hsum (le_trans hsum2 ?_))
  exact mul_le_mul_of_nonneg_right hconst hD0
end CorrB

end Corr
end GYMaj
