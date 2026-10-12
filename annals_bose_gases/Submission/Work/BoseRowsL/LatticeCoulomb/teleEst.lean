import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseRowsL.LatticeCoulomb.ballInvNormSq
import Submission.Work.BoseRowsL.LatticeCoulomb.block_sum_le
import Submission.Work.BoseRowsL.LatticeCoulomb.csiAux
import Submission.Work.BoseRowsL.LatticeCoulomb.maxAbs_cast_le_norm
import Submission.Work.BoseRowsL.LatticeCoulomb.sum_integral_ucell_eq_integral_iUnion
import Submission.Work.BoseRowsL.LatticeCoulomb.telescopeAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.teleEst`

The numerical estimates consumed by the telescoping proof of
`Work.BoseRowsL.LatticeCoulomb.telescopeInner`:

* `tele_one_le_norm` — a nonzero lattice vector has norm at least `1`;
* `teleH_le_one` — the Coulomb kernel is at most `1`;
* `teleErr_abs_le_three` — the crude uniform bound on the telescoping error;
* `tele_small_card` — at most `27` lattice vectors have norm `< 2`;
* `tele_fifth_sum` — the dyadic bound `∑ 1/(1+‖n‖⁵) ≤ 30` for `‖n‖ ≥ 2`;
* `teleErr_bound_big` — the decaying bound `|teleErr|(1+‖n‖⁵) ≤ 15` for `‖n‖ ≥ 2`;
* `teleErr_sum` — `∑_{n∈T}|teleErr j n| ≤ 700`;
* `tele_shell_sum` — the annulus/shell bound `∑_{m∈S}‖nvec m‖⁻² ≤ 300`;
* `tele_sigBullet_coord` — `|(sigBullet z)_j| ≤ 1/4`.
-/

noncomputable section

open scoped Real BigOperators Topology
open MeasureTheory Metric

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false

/-! ## Elementary bounds -/

/-- A nonzero lattice vector has norm at least `1`. -/
lemma tele_one_le_norm {n : Fin 3 → ℤ} (hn : n ≠ 0) : 1 ≤ ‖nvec n‖ := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, n i ≠ 0 := Function.ne_iff.mp hn
  have h3 : (1 : ℤ) ≤ |n i| := Int.one_le_abs hi
  have h4 : (1 : ℝ) ≤ |((n i : ℤ) : ℝ)| := by
    have h := Int.cast_abs (R := ℝ) (a := n i)
    rw [← h]
    exact_mod_cast h3
  have h2 : (1 : ℝ) ≤ (((n i : ℤ) : ℝ)) ^ 2 := by
    nlinarith [h4, abs_nonneg (((n i : ℤ) : ℝ)), sq_abs (((n i : ℤ) : ℝ))]
  have h5 : ‖nvec n‖ ^ 2 = ∑ j : Fin 3, (((n j : ℤ) : ℝ)) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [nvec_apply, Real.norm_eq_abs, sq_abs]
  have h6 : (1 : ℝ) ≤ ‖nvec n‖ ^ 2 := by
    rw [h5]
    exact le_trans h2 (Finset.single_le_sum
      (f := fun j : Fin 3 => (((n j : ℤ) : ℝ)) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i))
  nlinarith [norm_nonneg (nvec n), h6]

/-- The Coulomb kernel `‖nvec n‖⁻²` is at most `1`. -/
lemma teleH_le_one (n : Fin 3 → ℤ) : teleH n ≤ 1 := by
  rw [teleH]
  rcases eq_or_ne n 0 with h | h
  · subst h
    rw [nvec_zero, norm_zero]
    norm_num
  · have h1 : (1 : ℝ) ≤ ‖nvec n‖ := tele_one_le_norm h
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ‖nvec n‖ ^ 2)]
    nlinarith [h1, norm_nonneg (nvec n)]

/-- The crude uniform bound on the telescoping error. -/
lemma teleErr_abs_le_three (j : Fin 3) (n : Fin 3 → ℤ) (hn : n ≠ 0) :
    |teleErr j n| ≤ 3 := by
  have h1 : (1 : ℝ) ≤ ‖nvec n‖ := tele_one_le_norm hn
  have h2 : |(nvec n).ofLp j| ≤ ‖nvec n‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (nvec n) j
  have h4 : ‖nvec n‖ ≤ ‖nvec n‖ ^ 4 := by
    simpa using pow_le_pow_right₀ h1 (by norm_num : 1 ≤ 4)
  have hA : |(nvec n).ofLp j / ‖nvec n‖ ^ 4| ≤ 1 := by
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖nvec n‖ ^ 4),
      div_le_iff₀ (by positivity : (0 : ℝ) < ‖nvec n‖ ^ 4)]
    linarith
  have hB : |(1 / 2 : ℝ) * (teleH (n + teleE j) - teleH (n - teleE j))| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have h6 : |teleH (n + teleE j) - teleH (n - teleE j)| ≤ 1 := by
      have ha := teleH_nonneg (n + teleE j)
      have hb := teleH_nonneg (n - teleE j)
      have hc := teleH_le_one (n + teleE j)
      have hd := teleH_le_one (n - teleE j)
      rw [abs_le]
      constructor <;> linarith
    linarith
  have h7 : teleErr j n
      = -2 * ((nvec n).ofLp j / ‖nvec n‖ ^ 4)
        - (1 / 2) * (teleH (n + teleE j) - teleH (n - teleE j)) := by
    rw [teleErr]; ring
  have h8 : |-2 * ((nvec n).ofLp j / ‖nvec n‖ ^ 4)| ≤ 2 := by
    rw [show (-2 : ℝ) * ((nvec n).ofLp j / ‖nvec n‖ ^ 4)
        = -(2 * ((nvec n).ofLp j / ‖nvec n‖ ^ 4)) by ring, abs_neg, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [hA]
  have h9 : |-2 * ((nvec n).ofLp j / ‖nvec n‖ ^ 4)
      - (1 / 2) * (teleH (n + teleE j) - teleH (n - teleE j))|
      ≤ |-2 * ((nvec n).ofLp j / ‖nvec n‖ ^ 4)|
        + |(1 / 2) * (teleH (n + teleE j) - teleH (n - teleE j))| := by
    have h := abs_add_le (-2 * ((nvec n).ofLp j / ‖nvec n‖ ^ 4))
      (-((1 / 2) * (teleH (n + teleE j) - teleH (n - teleE j))))
    rw [abs_neg] at h
    simpa [sub_eq_add_neg] using h
  rw [h7]
  linarith [h8, h9, hB]

/-- At most `27` lattice vectors have norm `< 2`. -/
lemma tele_small_card (T : Finset (Fin 3 → ℤ)) (h : ∀ n ∈ T, ‖nvec n‖ < 2) :
    T.card ≤ 27 := by
  have hle : ∀ n ∈ T, maxAbs n ≤ 1 := by
    intro n hn
    have h1 : (maxAbs n : ℝ) ≤ ‖nvec n‖ := maxAbs_cast_le_norm n
    have h2 : (maxAbs n : ℝ) < 2 := lt_of_le_of_lt h1 (h n hn)
    have h3 : maxAbs n < 2 := by exact_mod_cast h2
    omega
  have h4 := block_card_le T 1 hle
  simpa using h4

/-! ## The decaying bound on the telescoping error -/

/-- The arithmetic of the deep case: for `r ≥ 2` one has `4(1+r⁵)/(r(r²-1)²) ≤ 15`. -/
private lemma tele_arith_four {r : ℝ} (hr : 2 ≤ r) :
    4 / (r * (r ^ 2 - 1) ^ 2) * (1 + r ^ 5) ≤ 15 := by
  have hrp : 0 < r := by linarith
  have hden : 0 < r * (r ^ 2 - 1) ^ 2 := mul_pos hrp (pow_pos (by nlinarith : (0 : ℝ) < r ^ 2 - 1) 2)
  have h1 : (9 / 16 : ℝ) * r ^ 4 ≤ (r ^ 2 - 1) ^ 2 := by nlinarith [sq_nonneg (r ^ 2 - 4)]
  have h2 : (1 : ℝ) + r ^ 5 ≤ (33 / 32 : ℝ) * r ^ 5 := by
    have h : (32 : ℝ) ≤ r ^ 5 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hr 5
      norm_num at hh
      exact hh
    linarith
  have hr5 : 0 < r ^ 5 := pow_pos hrp 5
  have h3 : (9 / 16 : ℝ) * r ^ 5 ≤ r * (r ^ 2 - 1) ^ 2 := by nlinarith [h1, hrp]
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith [h2, h3, hr5]

/-- The arithmetic of the shallow case: for `r ≥ 2` one has `5(1+r⁵)/(r(r²-1)²) ≤ 15`. -/
private lemma tele_arith_five {r : ℝ} (hr : 2 ≤ r) :
    5 / (r * (r ^ 2 - 1) ^ 2) * (1 + r ^ 5) ≤ 15 := by
  have hrp : 0 < r := by linarith
  have hden : 0 < r * (r ^ 2 - 1) ^ 2 := mul_pos hrp (pow_pos (by nlinarith : (0 : ℝ) < r ^ 2 - 1) 2)
  have h1 : (9 / 16 : ℝ) * r ^ 4 ≤ (r ^ 2 - 1) ^ 2 := by nlinarith [sq_nonneg (r ^ 2 - 4)]
  have h2 : (1 : ℝ) + r ^ 5 ≤ (33 / 32 : ℝ) * r ^ 5 := by
    have h : (32 : ℝ) ≤ r ^ 5 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hr 5
      norm_num at hh
      exact hh
    linarith
  have hr5 : 0 < r ^ 5 := pow_pos hrp 5
  have h3 : (9 / 16 : ℝ) * r ^ 5 ≤ r * (r ^ 2 - 1) ^ 2 := by nlinarith [h1, hrp]
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith [h2, h3, hr5]

/-- The decaying bound on the telescoping error for lattice vectors of norm at least `2`. -/
lemma teleErr_bound_big (j : Fin 3) (n : Fin 3 → ℤ) (hn : 2 ≤ ‖nvec n‖) :
    |teleErr j n| * (1 + ‖nvec n‖ ^ 5) ≤ 15 := by
  set r : ℝ := ‖nvec n‖ with hr
  set s : ℝ := (nvec n).ofLp j with hs
  have hrp : 0 < r := by rw [hr]; linarith
  have hsr : |s| ≤ r := by
    rw [hs, hr]
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (nvec n) j
  have hslow : -r ≤ s := (abs_le.mp hsr).1
  have hshigh : s ≤ r := (abs_le.mp hsr).2
  have hs2 : s ^ 2 ≤ r ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg s) hsr 2
    rwa [sq_abs] at h
  have hinner : inner ℝ (nvec n) (nvec (teleE j)) = s := by
    rw [hs, tele_inner_nvec_eq]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      simp [teleE_ne hi]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hnormsq : ‖nvec (teleE j)‖ ^ 2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ)]
    rw [Finset.sum_eq_single j]
    · simp [nvec_apply, teleE_self]
    · intro i _ hi
      simp [nvec_apply, teleE_ne hi]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hna : ‖nvec (n + teleE j)‖ ^ 2 = r ^ 2 + 2 * s + 1 := by
    rw [tele_nvec_add, norm_add_sq_real, ← hr, hinner, hnormsq]
  have hns : ‖nvec (n - teleE j)‖ ^ 2 = r ^ 2 - 2 * s + 1 := by
    rw [tele_nvec_sub, sub_eq_add_neg, norm_add_sq_real, norm_neg, ← hr]
    have hneg : inner ℝ (nvec n) (-(nvec (teleE j))) = -s := by
      rw [inner_neg_right, hinner]
    rw [hneg, hnormsq]
    ring
  have hne_add : n + teleE j ≠ 0 := by
    intro h0
    have h2 := hna
    rw [h0, nvec_zero, norm_zero] at h2
    nlinarith [h2, hslow, sq_nonneg (r - 1)]
  have hne_sub : n - teleE j ≠ 0 := by
    intro h0
    have h2 := hns
    rw [h0, nvec_zero, norm_zero] at h2
    nlinarith [h2, hshigh, sq_nonneg (r - 1)]
  have hApos : (0 : ℝ) < r ^ 2 + 2 * s + 1 := by
    have h := tele_one_le_norm hne_add
    nlinarith [h, norm_nonneg (nvec (n + teleE j)), hna]
  have hBpos : (0 : ℝ) < r ^ 2 - 2 * s + 1 := by
    have h := tele_one_le_norm hne_sub
    nlinarith [h, norm_nonneg (nvec (n - teleE j)), hns]
  have hPid : (r ^ 2 + 1) ^ 2 - 4 * s ^ 2 = (r ^ 2 + 2 * s + 1) * (r ^ 2 - 2 * s + 1) := by ring
  have hPpos : 0 < (r ^ 2 + 1) ^ 2 - 4 * s ^ 2 := by
    rw [hPid]
    exact mul_pos hApos hBpos
  have hPge : (r ^ 2 - 1) ^ 2 ≤ (r ^ 2 + 1) ^ 2 - 4 * s ^ 2 := by nlinarith [hs2]
  have hrsq : (4 : ℝ) ≤ r ^ 2 := by rw [hr]; nlinarith [hn, norm_nonneg (nvec n)]
  have hr4 : 0 < r ^ 4 := pow_pos hrp 4
  have hden2 : 0 < r * (r ^ 2 - 1) ^ 2 :=
    mul_pos hrp (pow_pos (by nlinarith [hrsq] : (0 : ℝ) < r ^ 2 - 1) 2)
  have key : teleErr j n
      = 2 * s * (4 * s ^ 2 - 2 * r ^ 2 - 1) / (r ^ 4 * ((r ^ 2 + 1) ^ 2 - 4 * s ^ 2)) := by
    rw [teleErr, teleH, teleH, hna, hns, ← hs, ← hr]
    rw [hPid, div_sub_div]
    · field_simp [ne_of_gt hApos, ne_of_gt hBpos]
      ring
    · exact ne_of_gt hApos
    · exact ne_of_gt hBpos
  have habs : |teleErr j n|
      = 2 * |s| * |4 * s ^ 2 - 2 * r ^ 2 - 1| / (r ^ 4 * ((r ^ 2 + 1) ^ 2 - 4 * s ^ 2)) := by
    rw [key, abs_div, abs_mul, abs_mul, abs_mul, abs_of_pos hr4, abs_of_pos hPpos,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rcases le_or_gt (2 * r ^ 2 + 1) (4 * s ^ 2) with hcase | hcase
  · have hnum : |4 * s ^ 2 - 2 * r ^ 2 - 1| ≤ 2 * r ^ 2 := by
      rw [abs_of_nonneg (by linarith)]
      nlinarith [hs2]
    have hstep : 2 * |s| * |4 * s ^ 2 - 2 * r ^ 2 - 1| ≤ 4 * r ^ 3 := by
      have h2 : 2 * |s| ≤ 2 * r := by linarith [hsr]
      have := mul_le_mul h2 hnum (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * r)
      nlinarith [this]
    have hle : |teleErr j n| ≤ 4 / (r * (r ^ 2 - 1) ^ 2) := by
      rw [habs, div_le_div_iff₀ (mul_pos hr4 hPpos) hden2]
      calc 2 * |s| * |4 * s ^ 2 - 2 * r ^ 2 - 1| * (r * (r ^ 2 - 1) ^ 2)
          ≤ (4 * r ^ 3) * (r * (r ^ 2 - 1) ^ 2) :=
            mul_le_mul_of_nonneg_right hstep (le_of_lt hden2)
        _ = 4 * (r ^ 4 * (r ^ 2 - 1) ^ 2) := by ring
        _ ≤ 4 * (r ^ 4 * ((r ^ 2 + 1) ^ 2 - 4 * s ^ 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPge (le_of_lt hr4))
              (by norm_num)
    calc |teleErr j n| * (1 + r ^ 5) ≤ 4 / (r * (r ^ 2 - 1) ^ 2) * (1 + r ^ 5) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ ≤ 15 := tele_arith_four (by rw [hr]; exact hn)
  · have hnum : |4 * s ^ 2 - 2 * r ^ 2 - 1| ≤ 2 * r ^ 2 + 1 := by
      rw [abs_of_nonpos (by linarith)]
      linarith [sq_nonneg s]
    have hstep : 2 * |s| * |4 * s ^ 2 - 2 * r ^ 2 - 1| ≤ 5 * r ^ 3 := by
      have h2 : 2 * |s| ≤ 2 * r := by linarith [hsr]
      have h3 := mul_le_mul h2 hnum (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * r)
      have h4 : (2 * r) * (2 * r ^ 2 + 1) ≤ 5 * r ^ 3 := by nlinarith [hrp, hrsq]
      linarith
    have hle : |teleErr j n| ≤ 5 / (r * (r ^ 2 - 1) ^ 2) := by
      rw [habs, div_le_div_iff₀ (mul_pos hr4 hPpos) hden2]
      calc 2 * |s| * |4 * s ^ 2 - 2 * r ^ 2 - 1| * (r * (r ^ 2 - 1) ^ 2)
          ≤ (5 * r ^ 3) * (r * (r ^ 2 - 1) ^ 2) :=
            mul_le_mul_of_nonneg_right hstep (le_of_lt hden2)
        _ = 5 * (r ^ 4 * (r ^ 2 - 1) ^ 2) := by ring
        _ ≤ 5 * (r ^ 4 * ((r ^ 2 + 1) ^ 2 - 4 * s ^ 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPge (le_of_lt hr4))
              (by norm_num)
    calc |teleErr j n| * (1 + r ^ 5) ≤ 5 / (r * (r ^ 2 - 1) ^ 2) * (1 + r ^ 5) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ ≤ 15 := tele_arith_five (by rw [hr]; exact hn)

/-! ## The fifth-power lattice sum -/

/-- The one-dimensional geometric sum `∑_{k<K} (1/4)^k = 4/3 - (4/3)(1/4)^K`. -/
private lemma geom_quarter (K : ℕ) :
    ∑ k ∈ Finset.range K, (1 / 4 : ℝ) ^ k = 4 / 3 - 4 / 3 * (1 / 4) ^ K := by
  induction K with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

/-- The one-dimensional geometric bound `∑_{k<K} (1/4)^k ≤ 4/3`. -/
private lemma geom_quarter_le (K : ℕ) :
    ∑ k ∈ Finset.range K, (1 / 4 : ℝ) ^ k ≤ 4 / 3 := by
  rw [geom_quarter K]
  have h : (0 : ℝ) ≤ 4 / 3 * (1 / 4) ^ K := by positivity
  linarith

/-- The block arithmetic: `(2^{k+2})³ (1/2)^{5k} = 64 (1/2)^{2k}`. -/
private lemma tele_block_arith (k : ℕ) :
    ((2 : ℝ) ^ (k + 2)) ^ 3 * (1 / 2 : ℝ) ^ (5 * k) = 64 * (1 / 2 : ℝ) ^ (2 * k) := by
  have h2 : ((2 : ℝ) ^ (3 * k)) * ((1 / 2 : ℝ) ^ (3 * k)) = 1 := by
    rw [← mul_pow]; norm_num
  have e1 : ((2 : ℝ) ^ (k + 2)) ^ 3 = 64 * (2 : ℝ) ^ (3 * k) := by
    rw [pow_add]; ring
  have e2 : (1 / 2 : ℝ) ^ (5 * k) = (1 / 2 : ℝ) ^ (3 * k) * (1 / 2 : ℝ) ^ (2 * k) := by
    rw [← pow_add]
    congr 1
    ring
  rw [e1, e2]
  calc (64 * (2 : ℝ) ^ (3 * k)) * ((1 / 2 : ℝ) ^ (3 * k) * (1 / 2 : ℝ) ^ (2 * k))
      = 64 * (((2 : ℝ) ^ (3 * k)) * ((1 / 2 : ℝ) ^ (3 * k))) * ((1 / 2 : ℝ) ^ (2 * k)) := by
        ring
    _ = 64 * 1 * ((1 / 2 : ℝ) ^ (2 * k)) := by rw [h2]
    _ = 64 * (1 / 2 : ℝ) ^ (2 * k) := by ring

/-- The pointwise weight bound on a dyadic block. -/
private lemma tele_fifth_term_le {n : Fin 3 → ℤ} (hn : 1 ≤ maxAbs n) {k : ℕ}
    (hk : Nat.log 2 (maxAbs n) = k) :
    1 / (1 + (maxAbs n : ℝ) ^ 5) ≤ (1 / 2 : ℝ) ^ (5 * k) := by
  have hge : 2 ^ k ≤ maxAbs n := by
    have h := Nat.pow_log_le_self 2 (by omega : maxAbs n ≠ 0)
    rwa [hk] at h
  have h1 : ((2 : ℝ) ^ k) ≤ (maxAbs n : ℝ) := by exact_mod_cast hge
  have h2 : ((2 : ℝ) ^ k) ^ 5 ≤ (maxAbs n : ℝ) ^ 5 := pow_le_pow_left₀ (by positivity) h1 5
  have hA : (0 : ℝ) < (maxAbs n : ℝ) ^ 5 := by
    have hpos : (0 : ℝ) < (maxAbs n : ℝ) := by
      have hk0 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      linarith
    positivity
  have h4 := one_div_le_one_div_of_le hA
    (show (maxAbs n : ℝ) ^ 5 ≤ 1 + (maxAbs n : ℝ) ^ 5 by linarith)
  have h5 := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < ((2 : ℝ) ^ k) ^ 5) h2
  have h6 : 1 / (((2 : ℝ) ^ k) ^ 5) = (1 / 2 : ℝ) ^ (5 * k) := by
    rw [one_div, ← pow_mul, ← inv_pow, mul_comm k 5]
    norm_num
  linarith [h4, h5, h6.le, h6.ge]

/-- The dyadic block bound for the fifth-power lattice sum. -/
private lemma tele_block_le (T : Finset (Fin 3 → ℤ)) (k : ℕ)
    (h : ∀ n ∈ T.filter (fun n => Nat.log 2 (maxAbs n) = k), 1 ≤ maxAbs n) :
    (∑ n ∈ T.filter (fun n => Nat.log 2 (maxAbs n) = k),
        1 / (1 + (maxAbs n : ℝ) ^ 5)) ≤ 64 * (1 / 2 : ℝ) ^ (2 * k) := by
  classical
  set S := T.filter (fun n => Nat.log 2 (maxAbs n) = k) with hS
  have hcard : S.card ≤ (2 ^ (k + 2)) ^ 3 := by
    have hsub : S ⊆ T.filter (fun n => maxAbs n ≤ 2 ^ (k + 1) - 1) := by
      intro n hn
      rw [Finset.mem_filter] at hn ⊢
      refine ⟨hn.1, Nat.le_sub_one_of_lt ?_⟩
      have hh := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (maxAbs n)
      rwa [hn.2] at hh
    have h1 : S.card ≤ (2 * (2 ^ (k + 1) - 1) + 1) ^ 3 :=
      le_trans (Finset.card_le_card hsub)
        (block_card_le _ (2 ^ (k + 1) - 1) (fun n hn => (Finset.mem_filter.mp hn).2))
    have h2 : 2 * (2 ^ (k + 1) - 1) + 1 = 2 ^ (k + 2) - 1 := by
      have h3 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
      have h4 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
        rw [show k + 2 = k + 1 + 1 by ring, pow_succ]
        ring
      omega
    rw [h2] at h1
    exact le_trans h1 (Nat.pow_le_pow_left (Nat.sub_le _ _) 3)
  have hsum : (∑ n ∈ S, 1 / (1 + (maxAbs n : ℝ) ^ 5)) ≤ (S.card : ℝ) * (1 / 2 : ℝ) ^ (5 * k) := by
    calc (∑ n ∈ S, 1 / (1 + (maxAbs n : ℝ) ^ 5)) ≤ ∑ _n ∈ S, (1 / 2 : ℝ) ^ (5 * k) :=
          Finset.sum_le_sum fun n hn => tele_fifth_term_le (h n hn) (Finset.mem_filter.mp hn).2
      _ = (S.card : ℝ) * (1 / 2 : ℝ) ^ (5 * k) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcast : (S.card : ℝ) ≤ (((2 ^ (k + 2)) ^ 3 : ℕ) : ℝ) := by exact_mod_cast hcard
  have hK : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (5 * k) := by positivity
  have harith : (((2 ^ (k + 2)) ^ 3 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (5 * k)
      = 64 * (1 / 2 : ℝ) ^ (2 * k) := by
    push_cast
    exact tele_block_arith k
  calc (∑ n ∈ S, 1 / (1 + (maxAbs n : ℝ) ^ 5))
      ≤ (S.card : ℝ) * (1 / 2 : ℝ) ^ (5 * k) := hsum
    _ ≤ (((2 ^ (k + 2)) ^ 3 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (5 * k) :=
        mul_le_mul_of_nonneg_right hcast hK
    _ = 64 * (1 / 2 : ℝ) ^ (2 * k) := harith

/-- The dyadic bound for the fifth-power lattice sum over vectors of norm at least `2`. -/
lemma tele_fifth_sum (T : Finset (Fin 3 → ℤ)) (h : ∀ n ∈ T, 2 ≤ ‖nvec n‖) :
    (∑ n ∈ T, 1 / (1 + ‖nvec n‖ ^ 5)) ≤ 30 := by
  have hstep : (∑ n ∈ T, 1 / (1 + ‖nvec n‖ ^ 5))
      ≤ ∑ n ∈ T, 1 / (1 + (maxAbs n : ℝ) ^ 5) := by
    refine Finset.sum_le_sum fun n _ => ?_
    have hle : (maxAbs n : ℝ) ≤ ‖nvec n‖ := maxAbs_cast_le_norm n
    have h5 : (maxAbs n : ℝ) ^ 5 ≤ ‖nvec n‖ ^ 5 := pow_le_pow_left₀ (Nat.cast_nonneg _) hle 5
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hmax : ∀ n ∈ T, 2 ≤ maxAbs n := by
    intro n hn
    have h2 : (2 : ℝ) ≤ ‖nvec n‖ := h n hn
    have h3 : ‖nvec n‖ ^ 2 ≤ 3 * (maxAbs n : ℝ) ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ)]
      calc ∑ i : Fin 3, ‖(nvec n).ofLp i‖ ^ 2 ≤ ∑ i : Fin 3, (maxAbs n : ℝ) ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hi : |((n i : ℤ) : ℝ)| ≤ (maxAbs n : ℝ) := by
              have h := le_maxAbs n i
              have h' : (((n i).natAbs : ℕ) : ℝ) ≤ (maxAbs n : ℝ) := by exact_mod_cast h
              rwa [Nat.cast_natAbs, Int.cast_abs] at h'
            rw [nvec_apply]
            calc ‖(((n i : ℤ) : ℝ))‖ ^ 2 = |((n i : ℤ) : ℝ)| ^ 2 := by
                  rw [Real.norm_eq_abs, sq_abs]
              _ ≤ (maxAbs n : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hi 2
        _ = 3 * (maxAbs n : ℝ) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    have h4 : (1 : ℝ) < (maxAbs n : ℝ) := by nlinarith [h2, h3]
    have h5 : 1 < maxAbs n := by exact_mod_cast h4
    omega
  have hsplit : (∑ n ∈ T, 1 / (1 + (maxAbs n : ℝ) ^ 5))
      = ∑ k ∈ Finset.range (Nat.log 2 (T.sup maxAbs) + 1),
          ∑ n ∈ T.filter (fun n => Nat.log 2 (maxAbs n) = k),
            1 / (1 + (maxAbs n : ℝ) ^ 5) := by
    have hmaps : ∀ i ∈ T,
        Nat.log 2 (maxAbs i) ∈ Finset.range (Nat.log 2 (T.sup maxAbs) + 1) := by
      intro n hn
      simp only [Finset.mem_range]
      exact Nat.lt_succ_of_le (Nat.log_mono_right (Finset.le_sup hn))
    exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  have hzero : (∑ n ∈ T.filter (fun n => Nat.log 2 (maxAbs n) = 0),
      1 / (1 + (maxAbs n : ℝ) ^ 5)) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [Finset.mem_filter] at hn
    have h1 := hmax n hn.1
    have h2 : maxAbs n < 2 := by
      have hh := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (maxAbs n)
      rw [hn.2] at hh
      simpa using hh
    omega
  have hgeo : ∑ k ∈ Finset.range (Nat.log 2 (T.sup maxAbs)), (1 / 4 : ℝ) ^ (k + 1) ≤ 1 / 3 := by
    have hq := geom_quarter_le (Nat.log 2 (T.sup maxAbs))
    calc ∑ k ∈ Finset.range (Nat.log 2 (T.sup maxAbs)), (1 / 4 : ℝ) ^ (k + 1)
        = (1 / 4) * ∑ k ∈ Finset.range (Nat.log 2 (T.sup maxAbs)), (1 / 4 : ℝ) ^ k := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [pow_succ]; ring
      _ ≤ (1 / 4) * (4 / 3) := mul_le_mul_of_nonneg_left hq (by norm_num)
      _ = 1 / 3 := by norm_num
  calc (∑ n ∈ T, 1 / (1 + ‖nvec n‖ ^ 5))
      ≤ ∑ n ∈ T, 1 / (1 + (maxAbs n : ℝ) ^ 5) := hstep
    _ = ∑ k ∈ Finset.range (Nat.log 2 (T.sup maxAbs) + 1),
          ∑ n ∈ T.filter (fun n => Nat.log 2 (maxAbs n) = k),
            1 / (1 + (maxAbs n : ℝ) ^ 5) := hsplit
    _ = (∑ k ∈ Finset.range (Nat.log 2 (T.sup maxAbs)),
          ∑ n ∈ T.filter (fun n => Nat.log 2 (maxAbs n) = k + 1),
            1 / (1 + (maxAbs n : ℝ) ^ 5))
        + (∑ n ∈ T.filter (fun n => Nat.log 2 (maxAbs n) = 0),
            1 / (1 + (maxAbs n : ℝ) ^ 5)) := by
        rw [Finset.sum_range_succ']
    _ = ∑ k ∈ Finset.range (Nat.log 2 (T.sup maxAbs)),
          ∑ n ∈ T.filter (fun n => Nat.log 2 (maxAbs n) = k + 1),
            1 / (1 + (maxAbs n : ℝ) ^ 5) := by rw [hzero]; ring
    _ ≤ ∑ k ∈ Finset.range (Nat.log 2 (T.sup maxAbs)),
          64 * (1 / 2 : ℝ) ^ (2 * (k + 1)) :=
        Finset.sum_le_sum fun k _ =>
          tele_block_le T (k + 1) (fun n hn =>
            le_trans (by norm_num : (1 : ℕ) ≤ 2) (hmax n (Finset.mem_of_mem_filter n hn)))
    _ = 64 * ∑ k ∈ Finset.range (Nat.log 2 (T.sup maxAbs)), (1 / 4 : ℝ) ^ (k + 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [pow_mul]
        norm_num
    _ ≤ 64 * (1 / 3) := mul_le_mul_of_nonneg_left hgeo (by norm_num)
    _ ≤ 30 := by norm_num

/-! ## The total size of the telescoping error -/

/-- The total size of the telescoping error over any finite set of nonzero lattice vectors. -/
lemma teleErr_sum (j : Fin 3) (T : Finset (Fin 3 → ℤ)) (h : ∀ n ∈ T, n ≠ 0) :
    (∑ n ∈ T, |teleErr j n|) ≤ 700 := by
  classical
  have hsplit : (∑ n ∈ T, |teleErr j n|)
      = (∑ n ∈ T.filter (fun n => ‖nvec n‖ < 2), |teleErr j n|)
        + (∑ n ∈ T.filter (fun n => ¬ ‖nvec n‖ < 2), |teleErr j n|) :=
    (Finset.sum_filter_add_sum_filter_not T (fun n => ‖nvec n‖ < 2) _).symm
  have h1 : (∑ n ∈ T.filter (fun n => ‖nvec n‖ < 2), |teleErr j n|) ≤ 81 := by
    have hcard : (T.filter (fun n => ‖nvec n‖ < 2)).card ≤ 27 :=
      tele_small_card _ (fun n hn => (Finset.mem_filter.mp hn).2)
    calc (∑ n ∈ T.filter (fun n => ‖nvec n‖ < 2), |teleErr j n|)
        ≤ ∑ _n ∈ T.filter (fun n => ‖nvec n‖ < 2), (3 : ℝ) :=
          Finset.sum_le_sum fun n hn =>
            teleErr_abs_le_three j n (h n (Finset.mem_of_mem_filter n hn))
      _ = ((T.filter (fun n => ‖nvec n‖ < 2)).card : ℝ) * 3 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 27 * 3 := by
          have hc : (((T.filter (fun n => ‖nvec n‖ < 2)).card : ℕ) : ℝ) ≤ 27 := by
            exact_mod_cast hcard
          linarith
      _ = 81 := by norm_num
  have h2 : (∑ n ∈ T.filter (fun n => ¬ ‖nvec n‖ < 2), |teleErr j n|) ≤ 450 := by
    have hbig : ∀ n ∈ T.filter (fun n => ¬ ‖nvec n‖ < 2), 2 ≤ ‖nvec n‖ := by
      intro n hn
      have hh := (Finset.mem_filter.mp hn).2
      push_neg at hh
      exact hh
    have hsum := tele_fifth_sum _ hbig
    have hterm : ∀ n ∈ T.filter (fun n => ¬ ‖nvec n‖ < 2),
        |teleErr j n| ≤ 15 / (1 + ‖nvec n‖ ^ 5) := by
      intro n hn
      have hb := teleErr_bound_big j n (hbig n hn)
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 1 + ‖nvec n‖ ^ 5)]
      linarith [hb]
    calc (∑ n ∈ T.filter (fun n => ¬ ‖nvec n‖ < 2), |teleErr j n|)
        ≤ ∑ n ∈ T.filter (fun n => ¬ ‖nvec n‖ < 2), 15 / (1 + ‖nvec n‖ ^ 5) :=
          Finset.sum_le_sum hterm
      _ = 15 * ∑ n ∈ T.filter (fun n => ¬ ‖nvec n‖ < 2), 1 / (1 + ‖nvec n‖ ^ 5) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun n _ => by ring
      _ ≤ 15 * 30 := mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = 450 := by norm_num
  rw [hsplit]
  linarith [h1, h2]

/-! ## The shell sum over an annulus -/

/-- The annulus bound: a finite set of nonzero lattice vectors whose norms lie in a shell of
width `2` at radius `R` carries total `teleH`-weight at most `210`. -/
private lemma tele_shell_big (R : ℝ) (S : Finset (Fin 3 → ℤ)) (hR : 1 ≤ R)
    (hone : ∀ m ∈ S, 1 ≤ ‖nvec m‖) (hlow : ∀ m ∈ S, R - 1 ≤ ‖nvec m‖)
    (hhigh : ∀ m ∈ S, ‖nvec m‖ ≤ R + 1) (hne : ∀ m ∈ S, m ≠ 0) :
    (∑ m ∈ S, 1 / ‖nvec m‖ ^ 2) ≤ 260 := by
  classical
  have hcell : ∀ m ∈ S, 1 / ‖nvec m‖ ^ 2 ≤ 4 * ∫ q in ucell m, 1 / ‖q‖ ^ 2 := by
    intro m hm
    have hmle : (1 : ℝ) ≤ ‖nvec m‖ := hone m hm
    have hpt : ∀ q ∈ ucell m, 1 / ‖nvec m‖ ^ 2 ≤ 4 * (1 / ‖q‖ ^ 2) := by
      intro q hq
      have hq1 : ‖q‖ ≤ ‖nvec m‖ + 1 := norm_le_of_mem_ucell hq
      have hq2 : ‖q‖ ≤ 2 * ‖nvec m‖ := by linarith
      have hq3 : (0 : ℝ) < ‖q‖ := by
        have := half_le_norm_of_mem_ucell hq (hne m hm)
        linarith
      rw [show (4 : ℝ) * (1 / ‖q‖ ^ 2) = 4 / ‖q‖ ^ 2 by ring,
        div_le_div_iff₀ (by positivity : (0 : ℝ) < ‖nvec m‖ ^ 2) (by positivity : (0 : ℝ) < ‖q‖ ^ 2)]
      nlinarith [hq2, norm_nonneg q, norm_nonneg (nvec m)]
    have hIntC : IntegrableOn (fun _ : E3 => 1 / ‖nvec m‖ ^ 2) (ucell m) volume := by
      refine IntegrableOn.of_bound (by rw [volume_ucell]; exact ENNReal.one_lt_top)
        aestronglyMeasurable_const (1 / ‖nvec m‖ ^ 2) ?_
      refine Filter.Eventually.of_forall fun q => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hInt4 : IntegrableOn (fun q : E3 => 4 * (1 / ‖q‖ ^ 2)) (ucell m) volume := by
      have hmeas : Measurable (fun q : E3 => 4 * (1 / ‖q‖ ^ 2)) := by
        have h1 : Measurable (fun q : E3 => (‖q‖ ^ 2)⁻¹) :=
          (continuous_norm.pow 2).measurable.inv
        have h2 : Measurable (fun q : E3 => 4 * (‖q‖ ^ 2)⁻¹) := h1.const_mul 4
        simpa [one_div] using h2
      refine IntegrableOn.of_bound (by rw [volume_ucell]; exact ENNReal.one_lt_top)
        hmeas.aestronglyMeasurable 16 ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict (ucell_measurableSet m)] with q hq
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      have hq3 : (1 / 2 : ℝ) ≤ ‖q‖ := half_le_norm_of_mem_ucell hq (hne m hm)
      have h4 : |1 / ‖q‖ ^ 2| ≤ 4 := by
        rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
        nlinarith [hq3]
      linarith
    calc 1 / ‖nvec m‖ ^ 2 = ∫ _q in ucell m, 1 / ‖nvec m‖ ^ 2 := by
          rw [setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def, volume_ucell,
            ENNReal.toReal_one, one_mul]
      _ ≤ ∫ q in ucell m, 4 * (1 / ‖q‖ ^ 2) :=
          setIntegral_mono_on hIntC hInt4 (ucell_measurableSet m) hpt
      _ = 4 * ∫ q in ucell m, 1 / ‖q‖ ^ 2 := by rw [integral_const_mul]
  have hsub : (⋃ m ∈ S, ucell m) ⊆ Metric.closedBall (0 : E3) (R + 2) \
      Metric.ball (0 : E3) (max 0 (R - 2)) := by
    intro q hq
    rw [Set.mem_iUnion₂] at hq
    obtain ⟨m, hm, hqm⟩ := hq
    rw [Set.mem_sdiff, Metric.mem_closedBall, dist_zero_right, Metric.mem_ball, dist_zero_right]
    refine ⟨?_, ?_⟩
    · have h := norm_le_of_mem_ucell hqm
      linarith [hhigh m hm]
    · have h1 : R - 1 ≤ ‖q‖ + 1 := by
        have hd := norm_sub_nvec_le_of_mem_ucell hqm
        have h2 : ‖nvec m‖ ≤ ‖q‖ + ‖q - nvec m‖ := by
          calc ‖nvec m‖ = ‖q - (q - nvec m)‖ := by congr 1; abel
            _ ≤ ‖q‖ + ‖q - nvec m‖ := norm_sub_le _ _
        linarith [hlow m hm, h2]
      have h3 : R - 2 ≤ ‖q‖ := by linarith
      rcases le_or_gt 0 (R - 2) with h0 | h0
      · rw [max_eq_right h0]; linarith
      · rw [max_eq_left (le_of_lt h0)]; linarith [norm_nonneg q]
  have hmono : (∫ q in (⋃ m ∈ S, ucell m), (‖q‖ ^ 2)⁻¹)
      ≤ ∫ q in (Metric.closedBall (0 : E3) (R + 2) \ Metric.ball (0 : E3) (max 0 (R - 2))),
          (‖q‖ ^ 2)⁻¹ := by
    refine setIntegral_mono_set ?_ ?_ ?_
    · exact ((ballInvNormSq (R + 2) (by linarith)).1).mono_set (Set.sdiff_subset)
    · filter_upwards with q
      simp only [Pi.zero_apply]
      positivity
    · filter_upwards with q hq
      exact hsub hq
  have hIntB : IntegrableOn (fun q : E3 => (‖q‖ ^ 2)⁻¹)
      (Metric.ball 0 (max 0 (R - 2))) volume :=
    ((ballInvNormSq (max 0 (R - 2)) (le_max_left _ _)).1).mono_set
      (Metric.ball_subset_closedBall)
  have hIntA : IntegrableOn (fun q : E3 => (‖q‖ ^ 2)⁻¹) (Metric.closedBall 0 (R + 2)) volume :=
    (ballInvNormSq (R + 2) (by linarith)).1
  have hdisj : Disjoint (Metric.closedBall (0 : E3) (R + 2) \ Metric.ball (0 : E3) (max 0 (R - 2)))
      (Metric.ball (0 : E3) (max 0 (R - 2))) := by
    rw [Set.disjoint_left]
    intro q hq1 hq2
    exact hq1.2 hq2
  have hmaxle : max 0 (R - 2) ≤ R + 2 := by
    rcases le_or_gt 0 (R - 2) with h0 | h0
    · rw [max_eq_right h0]; linarith
    · rw [max_eq_left (le_of_lt h0)]; linarith
  have hunion : (Metric.closedBall (0 : E3) (R + 2) \ Metric.ball (0 : E3) (max 0 (R - 2)))
      ∪ Metric.ball (0 : E3) (max 0 (R - 2)) = Metric.closedBall (0 : E3) (R + 2) := by
    rw [Set.sdiff_union_self]
    refine Set.union_eq_left.mpr ?_
    intro q hq
    rw [Metric.mem_ball, dist_zero_right] at hq
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hval := setIntegral_union hdisj (Metric.isOpen_ball.measurableSet)
    (hIntA.mono_set (Set.sdiff_subset)) hIntB
  rw [hunion] at hval
  have hvalA : (∫ q in Metric.closedBall (0 : E3) (R + 2), (‖q‖ ^ 2)⁻¹)
      = 4 * Real.pi * (R + 2) := (ballInvNormSq (R + 2) (by linarith)).2.1
  have hvalB : (∫ q in Metric.ball (0 : E3) (max 0 (R - 2)), (‖q‖ ^ 2)⁻¹)
      = 4 * Real.pi * max 0 (R - 2) := (ballInvNormSq (max 0 (R - 2)) (le_max_left _ _)).2.2
  have hdiff : (∫ q in (Metric.closedBall (0 : E3) (R + 2) \ Metric.ball (0 : E3) (max 0 (R - 2))),
      (‖q‖ ^ 2)⁻¹) = 4 * Real.pi * (R + 2) - 4 * Real.pi * max 0 (R - 2) := by
    rw [hvalA, hvalB] at hval
    linarith [hval]
  calc (∑ m ∈ S, 1 / ‖nvec m‖ ^ 2)
      ≤ ∑ m ∈ S, 4 * ∫ q in ucell m, 1 / ‖q‖ ^ 2 := Finset.sum_le_sum hcell
    _ = 4 * ∑ m ∈ S, ∫ q in ucell m, 1 / ‖q‖ ^ 2 := by rw [Finset.mul_sum]
    _ = 4 * ∑ m ∈ S, ∫ q in ucell m, (‖q‖ ^ 2)⁻¹ := by
        refine congrArg (fun x => 4 * x) (Finset.sum_congr rfl fun m _ => ?_)
        exact integral_congr_ae (Filter.Eventually.of_forall fun q => by simp [one_div])
    _ = 4 * ∫ q in (⋃ m ∈ S, ucell m), (‖q‖ ^ 2)⁻¹ := by
        have hcos : ∀ q : E3,
            Real.cos (2 * Real.pi * inner ℝ q (0 : E3)) / ‖q‖ ^ 2 = (‖q‖ ^ 2)⁻¹ := by
          intro q; simp [one_div]
        calc 4 * ∑ m ∈ S, ∫ q in ucell m, (‖q‖ ^ 2)⁻¹
            = 4 * ∑ m ∈ S, ∫ q in ucell m,
                Real.cos (2 * Real.pi * inner ℝ q (0 : E3)) / ‖q‖ ^ 2 := by
              refine congrArg (fun x => 4 * x) (Finset.sum_congr rfl fun m _ => ?_)
              exact integral_congr_ae (Filter.Eventually.of_forall fun q => (hcos q).symm)
          _ = 4 * ∫ q in (⋃ m ∈ S, ucell m),
                Real.cos (2 * Real.pi * inner ℝ q (0 : E3)) / ‖q‖ ^ 2 := by
              rw [sum_integral_ucell_eq_integral_iUnion S 0 hne]
          _ = 4 * ∫ q in (⋃ m ∈ S, ucell m), (‖q‖ ^ 2)⁻¹ := by
              refine congrArg (fun x => 4 * x) (integral_congr_ae ?_)
              filter_upwards with q
              exact hcos q
    _ ≤ 4 * (4 * Real.pi * (R + 2) - 4 * Real.pi * max 0 (R - 2)) := by
        rw [← hdiff]
        exact mul_le_mul_of_nonneg_left hmono (by norm_num)
    _ ≤ 260 := by
        have hpi : Real.pi < 4 := Real.pi_lt_four
        have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
        rcases le_or_gt 2 R with h2 | h2
        · rw [max_eq_right (by linarith : (0 : ℝ) ≤ R - 2)]
          nlinarith
        · rw [max_eq_left (by linarith : R - 2 ≤ 0)]
          nlinarith


/-- The shell sum of `teleInner`-type consumers: at most `300`. -/
lemma tele_shell_sum (R : ℝ) (S : Finset (Fin 3 → ℤ)) (hR : 1 ≤ R)
    (hlo : ∀ m ∈ S, R - 1 ≤ ‖nvec m‖ ∨ ‖nvec m‖ ≤ 1)
    (hhi : ∀ m ∈ S, ‖nvec m‖ ≤ R + 1) :
    (∑ m ∈ S, 1 / ‖nvec m‖ ^ 2) ≤ 300 := by
  classical
  have hsplit : (∑ m ∈ S, 1 / ‖nvec m‖ ^ 2)
      = (∑ m ∈ S.filter (fun m => 1 < ‖nvec m‖), 1 / ‖nvec m‖ ^ 2)
        + (∑ m ∈ S.filter (fun m => ¬ 1 < ‖nvec m‖), 1 / ‖nvec m‖ ^ 2) :=
    (Finset.sum_filter_add_sum_filter_not S (fun m => 1 < ‖nvec m‖) _).symm
  have h₁ : (∑ m ∈ S.filter (fun m => ¬ 1 < ‖nvec m‖), 1 / ‖nvec m‖ ^ 2) ≤ 27 := by
    have hcard : (S.filter (fun m => ¬ 1 < ‖nvec m‖)).card ≤ 27 := by
      refine tele_small_card _ (fun m hm => ?_)
      have hm1 : ¬ (1 < ‖nvec m‖) := (Finset.mem_filter.mp hm).2
      have hle : ‖nvec m‖ ≤ 1 := le_of_not_gt hm1
      linarith
    calc (∑ m ∈ S.filter (fun m => ¬ 1 < ‖nvec m‖), 1 / ‖nvec m‖ ^ 2)
        ≤ ∑ _m ∈ S.filter (fun m => ¬ 1 < ‖nvec m‖), (1 : ℝ) := by
          refine Finset.sum_le_sum fun m hm => ?_
          rcases eq_or_ne m 0 with h0 | h0
          · rw [h0, nvec_zero, norm_zero]; norm_num
          · have h1 := tele_one_le_norm h0
            rw [div_le_one (by positivity)]
            nlinarith [h1, norm_nonneg (nvec m)]
      _ = ((S.filter (fun m => ¬ 1 < ‖nvec m‖)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ 27 := by exact_mod_cast hcard
  have h₂ : (∑ m ∈ S.filter (fun m => 1 < ‖nvec m‖), 1 / ‖nvec m‖ ^ 2) ≤ 260 := by
    refine tele_shell_big R _ hR ?_ ?_ ?_ ?_
    · intro m hm
      exact le_of_lt ((Finset.mem_filter.mp hm).2)
    · intro m hm
      rcases hlo m (Finset.mem_of_mem_filter m hm) with h | h
      · exact h
      · exact absurd (Finset.mem_filter.mp hm).2 (not_lt.mpr h)
    · intro m hm
      exact hhi m (Finset.mem_of_mem_filter m hm)
    · intro m hm
      have hgt := (Finset.mem_filter.mp hm).2
      intro h0
      rw [h0, nvec_zero, norm_zero] at hgt
      exact absurd hgt (by norm_num)
  rw [hsplit]
  linarith [h₁, h₂]

/-! ## The coordinate bound for `sigBullet` -/

/-- The one-dimensional model integral `∫_{t ∈ [-1/2,1/2]} |t| dt = 1/4`. -/
private lemma tele_integral_abs_Icc_half :
    ∫ t in Set.Icc (-(1 / 2) : ℝ) (1 / 2), |t| = 1 / 4 := by
  have h1 : ∫ t in (-(1 / 2))..(0 : ℝ), |t| = 1 / 8 := by
    have hsub : ∫ t in (-(1 / 2))..(0 : ℝ), |t| = ∫ t in (-(1 / 2))..(0 : ℝ), -t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 0)] at ht
      exact abs_of_nonpos ht.2
    rw [hsub, intervalIntegral.integral_neg, integral_id]
    norm_num
  have h2 : ∫ t in (0 : ℝ)..(1 / 2), |t| = 1 / 8 := by
    have hsub : ∫ t in (0 : ℝ)..(1 / 2), |t| = ∫ t in (0 : ℝ)..(1 / 2), t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
      exact abs_of_nonneg ht.1
    rw [hsub, integral_id]
    norm_num
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2),
    ← intervalIntegral.integral_add_adjacent_intervals
      (Continuous.intervalIntegrable (continuous_abs) _ _)
      (Continuous.intervalIntegrable (continuous_abs) _ _), h1, h2]
  norm_num

/-- The coordinate integral of the unit cell: `∫_{ucell 0} |w_j| = 1/4`. -/
private lemma tele_integral_abs_coord (j : Fin 3) :
    ∫ w in ucell (0 : Fin 3 → ℤ), |w.ofLp j| = 1 / 4 := by
  set S : Set (Fin 3 → ℝ) :=
    Set.univ.pi (fun _ : Fin 3 => Set.Icc (-(1 / 2) : ℝ) (1 / 2)) with hS
  set ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) with hν
  have hucell : ucell (0 : Fin 3 → ℤ) = WithLp.ofLp ⁻¹' S := by
    rw [hS, ucell_eq_preimage]
    simp
  have hmp : MeasurePreserving (WithLp.ofLp : E3 → (Fin 3 → ℝ)) volume volume :=
    PiLp.volume_preserving_ofLp (Fin 3)
  have hemb : MeasurableEmbedding (WithLp.ofLp : E3 → (Fin 3 → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding
  have h0 := MeasurePreserving.setIntegral_preimage_emb hmp hemb
    (fun y : Fin 3 → ℝ => |y j|) S
  rw [← hucell] at h0
  have hpi : (volume : Measure (Fin 3 → ℝ)).restrict S = Measure.pi (fun _ : Fin 3 => ν) := by
    rw [hS, hν, volume_pi]
    exact Measure.restrict_pi_pi (fun _ : Fin 3 => (volume : Measure ℝ))
      (fun _ : Fin 3 => Set.Icc (-(1 / 2) : ℝ) (1 / 2))
  have hνprob : IsProbabilityMeasure ν := ⟨by
    rw [hν, Measure.restrict_apply_univ, Real.volume_Icc,
      show (1 / 2 : ℝ) - -(1 / 2) = 1 by norm_num, ENNReal.ofReal_one]⟩
  haveI := hνprob
  calc ∫ w in ucell (0 : Fin 3 → ℤ), |w.ofLp j|
      = ∫ y in S, |y j| := h0
    _ = ∫ y, |y j| ∂(volume.restrict S) := rfl
    _ = ∫ y, |y j| ∂(Measure.pi (fun _ : Fin 3 => ν)) := by rw [hpi]
    _ = ∫ t, |t| ∂ν := MeasureTheory.integral_comp_eval (μ := fun _ : Fin 3 => ν) (i := j)
          (f := fun t : ℝ => |t|) continuous_abs.aestronglyMeasurable
    _ = 1 / 4 := tele_integral_abs_Icc_half

/-- The coordinate bound for `sigBullet`: `|(sigBullet z)_j| ≤ 1/4`. -/
lemma tele_sigBullet_coord (z : E3) (j : Fin 3) : |(sigBullet z).ofLp j| ≤ 1 / 4 := by
  haveI hfin : IsFiniteMeasure (volume.restrict (ucell (0 : Fin 3 → ℤ))) :=
    ⟨by rw [Measure.restrict_apply_univ, volume_ucell]; exact ENNReal.one_lt_top⟩
  have hcoord : (sigBullet z).ofLp j
      = ∫ w in ucell (0 : Fin 3 → ℤ), Real.sin (2 * Real.pi * inner ℝ w z) * w.ofLp j := by
    have hint : Integrable (fun w : E3 => (Real.sin (2 * Real.pi * inner ℝ w z)) • w)
        (volume.restrict (ucell (0 : Fin 3 → ℤ))) := by
      refine Integrable.of_bound ?_ 1 ?_
      · exact (((Real.continuous_sin.comp (by fun_prop)).smul continuous_id)).aestronglyMeasurable
      · filter_upwards [MeasureTheory.self_mem_ae_restrict (ucell_measurableSet 0)] with w hw
        rw [norm_smul, Real.norm_eq_abs]
        have h1 : |Real.sin (2 * Real.pi * inner ℝ w z)| ≤ 1 := Real.abs_sin_le_one _
        have h2 : ‖w‖ ≤ 1 := by
          have := norm_le_of_mem_ucell (n := (0 : Fin 3 → ℤ)) hw
          simpa [nvec_zero] using this
        calc |Real.sin (2 * Real.pi * inner ℝ w z)| * ‖w‖ ≤ 1 * 1 :=
              mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
          _ ≤ 1 := by norm_num
    have hcomp := ContinuousLinearMap.integral_comp_comm
      (μ := volume.restrict (ucell (0 : Fin 3 → ℤ)))
      (L := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : E3 →L[ℝ] ℝ)) hint
    rw [sigBullet]
    refine hcomp.symm.trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [PiLp.proj_apply, PiLp.smul_apply, smul_eq_mul]
  have hInt1 : IntegrableOn (fun w : E3 =>
      |Real.sin (2 * Real.pi * inner ℝ w z) * w.ofLp j|) (ucell (0 : Fin 3 → ℤ)) volume := by
    refine IntegrableOn.of_bound (by rw [volume_ucell]; exact ENNReal.one_lt_top) ?_ 1 ?_
    · exact (Real.continuous_sin.comp (by fun_prop)).mul
        (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : E3 →L[ℝ] ℝ).continuous |>.abs.aestronglyMeasurable
    · filter_upwards [MeasureTheory.self_mem_ae_restrict (ucell_measurableSet 0)] with w hw
      rw [Real.norm_eq_abs, abs_abs, abs_mul]
      have h1 : |Real.sin (2 * Real.pi * inner ℝ w z)| ≤ 1 := Real.abs_sin_le_one _
      have h2 : |w.ofLp j| ≤ 1 := by
        have h3 : ‖w‖ ≤ 1 := by
          have := norm_le_of_mem_ucell (n := (0 : Fin 3 → ℤ)) hw
          simpa [nvec_zero] using this
        have h4 : ‖w.ofLp j‖ ≤ ‖w‖ := PiLp.norm_apply_le w j
        rw [Real.norm_eq_abs] at h4
        linarith
      calc |Real.sin (2 * Real.pi * inner ℝ w z)| * |w.ofLp j| ≤ 1 * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
        _ ≤ 1 := by norm_num
  have hInt2 : IntegrableOn (fun w : E3 => |w.ofLp j|) (ucell (0 : Fin 3 → ℤ)) volume := by
    refine IntegrableOn.of_bound (by rw [volume_ucell]; exact ENNReal.one_lt_top) ?_ 1 ?_
    · exact ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : E3 →L[ℝ] ℝ).continuous.abs).aestronglyMeasurable
    · filter_upwards [MeasureTheory.self_mem_ae_restrict (ucell_measurableSet 0)] with w hw
      rw [Real.norm_eq_abs, abs_abs]
      have h3 : ‖w‖ ≤ 1 := by
        have := norm_le_of_mem_ucell (n := (0 : Fin 3 → ℤ)) hw
        simpa [nvec_zero] using this
      have h4 : ‖w.ofLp j‖ ≤ ‖w‖ := PiLp.norm_apply_le w j
      rw [Real.norm_eq_abs] at h4
      linarith
  have hmono : (∫ w in ucell (0 : Fin 3 → ℤ),
        |Real.sin (2 * Real.pi * inner ℝ w z) * w.ofLp j|)
      ≤ ∫ w in ucell (0 : Fin 3 → ℤ), |w.ofLp j| := by
    refine setIntegral_mono_ae hInt1 hInt2 ?_
    filter_upwards with w
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)
  calc |(sigBullet z).ofLp j|
      = |∫ w in ucell (0 : Fin 3 → ℤ), Real.sin (2 * Real.pi * inner ℝ w z) * w.ofLp j| := by
        rw [hcoord]
    _ ≤ ∫ w in ucell (0 : Fin 3 → ℤ),
          |Real.sin (2 * Real.pi * inner ℝ w z) * w.ofLp j| := abs_integral_le_integral_abs
    _ ≤ ∫ w in ucell (0 : Fin 3 → ℤ), |w.ofLp j| := hmono
    _ = 1 / 4 := tele_integral_abs_coord j

end Work.BoseRowsL.LatticeCoulomb



