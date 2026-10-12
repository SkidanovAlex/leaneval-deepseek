import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7AK.K15R.Defs
import Submission.Work.BoseB7AK.K15R.inv2_low
import Submission.Work.BoseB7AK.K15R.inv3_annulus
import Submission.Work.BoseB7AK.K15R.inv4_high
import Submission.Work.BoseB7AK.K15R.inv6_high
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7AK.K15R.lattice_rows` — the four lattice rows of `lem:EstimateIntegral`

The four momentum sums of FS §10's `lem:EstimateIntegral` that the chapter consumes
as the fields `K15Input.low_sum`, `K15Input.sum_inv4`, `K15Input.sum_inv6` and
`K15Input.sum_inv3`: over the box modes `q` of side `ℓ` (momenta `ℓ⁻¹ • vec n`,
`vec n = 2πn` the dual-lattice points), with `K_H ≥ 1`, `a > 0`,

1. `ℓ⁻³ ∑_{‖k‖ < 1/(2K_Ha)} ‖k‖⁻² ≤ K₀/(K_Ha)`;
2. `ℓ⁻³ ∑_{1/(2K_Ha) ≤ ‖k‖} ‖k‖⁻⁴ ≤ K₀·K_Ha`;
3. `ℓ⁻³ ∑_{1/(2K_Ha) ≤ ‖k‖} ‖k‖⁻⁶ ≤ K₀·(K_Ha)³`;
4. `ℓ⁻³ ∑_{1/(2K_Ha) ≤ ‖k‖ ≤ 1/a} ‖k‖⁻³ ≤ K₀·(1 + log K_H)`.

These are exactly the `(2π)⁻³ ∫ k^{-p}` replacing-the-sum-by-the-integral rows of
FS's Lemma, and they are the *only* content of the four bundle fields: no χ, no
Fock space, no spectral data enters.

The proof has two halves, both independent of the chapter's physics:

* **the four pure lattice sums** (`Work.BoseB7AK.K15R.inv2_low`, `inv4_high`, `inv6_high`,
  `inv3_annulus`): for a finite set `S` of *nonzero* lattice indices,
  `∑ ‖vec n‖^{-2} ≲ R` on the ball `‖vec n‖ ≤ R`, and `∑ ‖vec n‖^{-4} ≲ R⁻¹`,
  `∑ ‖vec n‖^{-6} ≲ R⁻³`, `∑_{R ≤ ‖vec n‖ ≤ R'} ‖vec n‖^{-3} ≲ 1 + log(R'/R)`
  on the tails/annuli.  They are proved from the `ℓ^∞` level machinery of
  `LevelDefs` (shells of size `26 m²`) and the elementary reciprocal sums
  `SumInvPow`;
* **the mode/lattice transfer**: `OnDualLattice ℓ kmom` says the mode labels are
  *distinct* dual-lattice points `kmom q = ℓ⁻¹ • vec n_q` with `n_q = hlat.lift q`
  injective, so `1/‖kmom q‖^p = ℓ^p/‖vec n_q‖^p` and the mode sums become lattice
  sums over `S = (filter).image hlat.lift` (with the zero-momentum mode, whose
  contribution vanishes identically, removed).

`K₀` is chosen as the maximum of the four absolute constants and `1`; only
existence is used downstream (`K15Input`'s `K₀` is free).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7AK.K15R

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The mode/lattice transfer -/

/-- **A mode label's norm, read off its lattice index**: `kmom q = ℓ⁻¹ • vec n_q`
with `n_q = hlat.lift q`, so `‖kmom q‖ = ‖vec n_q‖ / ℓ`. -/
private lemma norm_lift_of_dualLattice {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {ℓ : ℝ} {kmom : Mode → ℝ³} (h : OnDualLattice ℓ kmom)
    (hℓ : 0 < ℓ) (q : Mode) :
    ‖kmom q‖ = ‖Work.BoseB4.vec (h.lift q)‖ / ℓ := by
  rw [h.lift_spec q, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
  ring

/-- The same identity in the direction needed for the *lower* bounds:
`‖vec n_q‖ = ℓ·‖kmom q‖`. -/
private lemma norm_vec_lift_of_dualLattice {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {ℓ : ℝ} {kmom : Mode → ℝ³} (h : OnDualLattice ℓ kmom)
    (hℓ : 0 < ℓ) (q : Mode) :
    ‖Work.BoseB4.vec (h.lift q)‖ = ℓ * ‖kmom q‖ := by
  rw [norm_lift_of_dualLattice h hℓ q]
  field_simp

/-- **The transfer identity** `1/‖kmom q‖^p = ℓ^p · 1/‖vec n_q‖^p`. -/
private lemma one_div_norm_lift_pow {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {ℓ : ℝ} {kmom : Mode → ℝ³} (h : OnDualLattice ℓ kmom)
    (hℓ : 0 < ℓ) (q : Mode) (p : ℕ) :
    1 / ‖kmom q‖ ^ p = ℓ ^ p * (1 / ‖Work.BoseB4.vec (h.lift q)‖ ^ p) := by
  rw [norm_lift_of_dualLattice h hℓ q, div_pow, one_div, one_div, inv_div, div_eq_mul_inv]

/-- **The mode sum over a filtered set of labels equals `ℓ^p` times the lattice sum
over the image of the lattice index.** -/
private lemma sum_eq_lattice_sum {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {ℓ : ℝ} {kmom : Mode → ℝ³} (h : OnDualLattice ℓ kmom)
    (hℓ : 0 < ℓ) (T : Finset Mode) (p : ℕ) :
    ∑ q ∈ T, 1 / ‖kmom q‖ ^ p
      = ℓ ^ p * ∑ n ∈ T.image h.lift, 1 / ‖Work.BoseB4.vec n‖ ^ p := by
  rw [Finset.sum_image (fun x _ y _ hxy => h.lift_injective hxy), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun q _ => one_div_norm_lift_pow h hℓ q p)

/-- `vec 0 = 0`. -/
private lemma vec_zero : Work.BoseB4.vec (0 : Fin 3 → ℤ) = 0 := by
  ext i
  simp [Work.BoseB4.vec]

/-- **A mode giving a lattice index `0` has zero momentum** (`vec 0 = 0`). -/
private lemma kmom_eq_zero_of_lift_eq_zero {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {ℓ : ℝ} {kmom : Mode → ℝ³} (h : OnDualLattice ℓ kmom)
    {q : Mode} (hq : h.lift q = 0) : kmom q = 0 := by
  rw [h.lift_spec q, hq, vec_zero, smul_zero]

/-- **The zero-momentum mode contributes nothing to the `‖kmom ·‖^{-p}` sums** (Lean's
`1/0 = 0`), so the sums may be taken over the labels with `kmom q ≠ 0` — which is what
makes their lattice indices nonzero. -/
private lemma sum_filter_ne_zero {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {kmom : Mode → ℝ³} (T : Finset Mode) (p : ℕ) (hp : 1 ≤ p) :
    ∑ q ∈ T, 1 / ‖kmom q‖ ^ p
      = ∑ q ∈ T.filter (fun q => kmom q ≠ 0), 1 / ‖kmom q‖ ^ p := by
  have h := Finset.sum_filter_add_sum_filter_not T (fun q => kmom q ≠ 0)
    (fun q => 1 / ‖kmom q‖ ^ p)
  have hzero : ∑ q ∈ T.filter (fun q => ¬ (kmom q ≠ 0)), 1 / ‖kmom q‖ ^ p = 0 := by
    refine Finset.sum_eq_zero (fun q hq => ?_)
    have hq0 : kmom q = 0 := by simpa using (Finset.mem_filter.mp hq).2
    rw [hq0, norm_zero, zero_pow (by omega : p ≠ 0), div_zero]
  linarith [h, hzero]

/-! ## 2. The four rows -/

theorem lattice_rows :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
      (ℓ : ℝ) (hℓ : 1 ≤ ℓ) (kmom : Mode → EuclideanSpace ℝ (Fin 3))
      (hlat : Work.BoseB7AK.K15R.OnDualLattice ℓ kmom)
      (KH a : ℝ) (hKH : 1 ≤ KH) (ha : 0 < a),
      (ℓ ^ (-(3 : ℝ)) *
          ∑ k ∈ (Work.BoseB7.excited Mode).filter (fun k => ¬ (1 / (2 * KH * a) ≤ ‖kmom k‖)),
            1 / ‖kmom k‖ ^ 2 ≤ K₀ / (KH * a)) ∧
      (ℓ ^ (-(3 : ℝ)) *
          ∑ k ∈ (Work.BoseB7.excited Mode).filter (fun k => 1 / (2 * KH * a) ≤ ‖kmom k‖),
            1 / ‖kmom k‖ ^ 4 ≤ K₀ * KH * a) ∧
      (ℓ ^ (-(3 : ℝ)) *
          ∑ k ∈ (Work.BoseB7.excited Mode).filter (fun k => 1 / (2 * KH * a) ≤ ‖kmom k‖),
            1 / ‖kmom k‖ ^ 6 ≤ K₀ * (KH * a) ^ 3) ∧
      (ℓ ^ (-(3 : ℝ)) *
          ∑ k ∈ ((Work.BoseB7.excited Mode).filter (fun k => 1 / (2 * KH * a) ≤ ‖kmom k‖)).filter
              (fun k => ‖kmom k‖ ≤ 1 / a),
            1 / ‖kmom k‖ ^ 3 ≤ K₀ * (1 + Real.log KH)) := by
  obtain ⟨C1, hC1nn, hC1⟩ := inv2_low
  obtain ⟨C2, hC2nn, hC2⟩ := inv4_high
  obtain ⟨C3, hC3nn, hC3⟩ := inv6_high
  obtain ⟨C4, hC4nn, hC4⟩ := inv3_annulus
  set K₀ : ℝ := max 1 (max (C1 / 2) (max (2 * C2) (max (8 * C3) C4))) with hK₀def
  refine ⟨K₀, ?_, ?_⟩
  · rw [hK₀def]; positivity
  · intro Mode _ _ _ ℓ hℓ kmom hlat KH a hKH ha
    have hℓpos : 0 < ℓ := lt_of_lt_of_le one_pos hℓ
    have hKHpos : 0 < KH := lt_of_lt_of_le one_pos hKH
    have h2pos : 0 < 2 * KH * a := by positivity
    set R : ℝ := ℓ / (2 * KH * a) with hRdef
    have hRpos : 0 < R := by rw [hRdef]; positivity
    have hK1 : C1 / 2 ≤ K₀ := by
      rw [hK₀def]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hK2 : 2 * C2 ≤ K₀ := by
      rw [hK₀def]
      exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    have hK3 : 8 * C3 ≤ K₀ := by
      rw [hK₀def]
      exact le_trans (le_max_left _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
    have hK4 : C4 ≤ K₀ := by
      rw [hK₀def]
      exact le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
    -- ### Row 1: the low-momentum `‖k‖^{-2}` sum
    have hrow1 : ℓ ^ (-(3 : ℝ)) *
        ∑ k ∈ (Work.BoseB7.excited Mode).filter (fun k => ¬ (1 / (2 * KH * a) ≤ ‖kmom k‖)),
          1 / ‖kmom k‖ ^ 2 ≤ K₀ / (KH * a) := by
      -- transfer to the lattice, dropping the (zero-contribution) zero momentum mode
      set T : Finset Mode := (Work.BoseB7.excited Mode).filter
        (fun k => ¬ (1 / (2 * KH * a) ≤ ‖kmom k‖)) with hT
      set T' : Finset Mode := T.filter (fun k => kmom k ≠ 0) with hT'
      have htrans : ∑ k ∈ T, 1 / ‖kmom k‖ ^ 2
          = ℓ ^ 2 * ∑ n ∈ T'.image hlat.lift, 1 / ‖Work.BoseB4.vec n‖ ^ 2 := by
        rw [sum_filter_ne_zero T 2 (by norm_num), hT']
        exact sum_eq_lattice_sum hlat hℓpos _ 2
      have hne' : ∀ n ∈ T'.image hlat.lift, n ≠ 0 := by
        intro n hn hzero
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
        have hk0 : kmom k ≠ 0 := (Finset.mem_filter.mp hk).2
        exact hk0 (kmom_eq_zero_of_lift_eq_zero hlat hzero)
      have hbd' : ∀ n ∈ T'.image hlat.lift, ‖Work.BoseB4.vec n‖ ≤ R := by
        intro n hn
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
        have hkT : k ∈ T := (Finset.mem_filter.mp hk).1
        have hlt : ‖kmom k‖ < 1 / (2 * KH * a) := lt_of_not_ge (Finset.mem_filter.mp hkT).2
        have h1 : ‖Work.BoseB4.vec (hlat.lift k)‖ / ℓ < 1 / (2 * KH * a) := by
          rw [← norm_lift_of_dualLattice hlat hℓpos k]
          exact hlt
        rw [div_lt_iff₀ hℓpos] at h1
        rw [hRdef]
        have h2 : ℓ * (1 / (2 * KH * a)) = ℓ / (2 * KH * a) := by ring
        linarith [h1, h2]
      have happ := hC1 (T'.image hlat.lift) R (le_of_lt hRpos) hne' hbd'
      have hpow : ℓ ^ (-(3 : ℝ)) * ℓ ^ (2 : ℕ) = ℓ ^ (-(1 : ℝ)) := by
        have h2 : ℓ ^ (2 : ℕ) = ℓ ^ (2 : ℝ) := (Real.rpow_natCast ℓ 2).symm
        rw [h2, ← Real.rpow_add hℓpos]
        norm_num
      have hone : ℓ ^ (-(1 : ℝ)) * ℓ = 1 := by
        rw [show (-(1 : ℝ)) = -1 by norm_num, Real.rpow_neg_one,
          inv_mul_cancel₀ (ne_of_gt hℓpos)]
      have hnonneg : 0 ≤ ℓ ^ (-(1 : ℝ)) := Real.rpow_nonneg hℓpos.le _
      calc ℓ ^ (-(3 : ℝ)) * ∑ k ∈ T, 1 / ‖kmom k‖ ^ 2
          = ℓ ^ (-(3 : ℝ)) * (ℓ ^ 2 * ∑ n ∈ T'.image hlat.lift,
              1 / ‖Work.BoseB4.vec n‖ ^ 2) := by rw [htrans]
        _ = (ℓ ^ (-(3 : ℝ)) * ℓ ^ (2 : ℕ)) * (∑ n ∈ T'.image hlat.lift,
              1 / ‖Work.BoseB4.vec n‖ ^ 2) := by ring
        _ = ℓ ^ (-(1 : ℝ)) * (∑ n ∈ T'.image hlat.lift,
              1 / ‖Work.BoseB4.vec n‖ ^ 2) := by rw [hpow]
        _ ≤ ℓ ^ (-(1 : ℝ)) * (C1 * R) := mul_le_mul_of_nonneg_left happ hnonneg
        _ = C1 / (2 * KH * a) := by
            rw [show R = ℓ / (2 * KH * a) from hRdef]
            rw [show ℓ ^ (-(1 : ℝ)) * (C1 * (ℓ / (2 * KH * a)))
                = C1 * (ℓ ^ (-(1 : ℝ)) * ℓ) / (2 * KH * a) from by ring]
            rw [hone]
            ring
        _ ≤ K₀ / (KH * a) := by
            rw [div_le_div_iff₀ h2pos (by positivity)]
            nlinarith [hK1]
    -- ### Row 2: the `‖k‖^{-4}` tail
    have hrow2 : ℓ ^ (-(3 : ℝ)) *
        ∑ k ∈ (Work.BoseB7.excited Mode).filter (fun k => 1 / (2 * KH * a) ≤ ‖kmom k‖),
          1 / ‖kmom k‖ ^ 4 ≤ K₀ * KH * a := by
      set T : Finset Mode := (Work.BoseB7.excited Mode).filter
        (fun k => 1 / (2 * KH * a) ≤ ‖kmom k‖) with hT
      have htrans : ∑ k ∈ T, 1 / ‖kmom k‖ ^ 4
          = ℓ ^ 4 * ∑ n ∈ T.image hlat.lift, 1 / ‖Work.BoseB4.vec n‖ ^ 4 :=
        sum_eq_lattice_sum hlat hℓpos T 4
      have hne' : ∀ n ∈ T.image hlat.lift, n ≠ 0 := by
        intro n hn hzero
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
        have hge : 1 / (2 * KH * a) ≤ ‖kmom k‖ := (Finset.mem_filter.mp hk).2
        have hk0 : kmom k = 0 := kmom_eq_zero_of_lift_eq_zero hlat hzero
        rw [hk0, norm_zero] at hge
        have hpos : 0 < 1 / (2 * KH * a) := by positivity
        linarith
      have hlow' : ∀ n ∈ T.image hlat.lift, R ≤ ‖Work.BoseB4.vec n‖ := by
        intro n hn
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
        have hge : 1 / (2 * KH * a) ≤ ‖kmom k‖ := (Finset.mem_filter.mp hk).2
        have h1 : ℓ * (1 / (2 * KH * a)) ≤ ℓ * ‖kmom k‖ :=
          mul_le_mul_of_nonneg_left hge hℓpos.le
        have h2 : ‖Work.BoseB4.vec (hlat.lift k)‖ = ℓ * ‖kmom k‖ :=
          norm_vec_lift_of_dualLattice hlat hℓpos k
        rw [h2, hRdef]
        have h3 : ℓ * (1 / (2 * KH * a)) = ℓ / (2 * KH * a) := by ring
        linarith [h1, h3]
      have happ := hC2 (T.image hlat.lift) R (le_of_lt hRpos) hne' hlow'
      have hpow : ℓ ^ (-(3 : ℝ)) * ℓ ^ (4 : ℕ) = ℓ := by
        have h4 : ℓ ^ (4 : ℕ) = ℓ ^ (4 : ℝ) := (Real.rpow_natCast ℓ 4).symm
        have h1 : ℓ ^ (1 : ℝ) = ℓ := Real.rpow_one ℓ
        rw [h4, ← Real.rpow_add hℓpos, show (-(3 : ℝ)) + 4 = (1 : ℝ) by norm_num, h1]
      calc ℓ ^ (-(3 : ℝ)) * ∑ k ∈ T, 1 / ‖kmom k‖ ^ 4
          = ℓ ^ (-(3 : ℝ)) * (ℓ ^ 4 * ∑ n ∈ T.image hlat.lift,
              1 / ‖Work.BoseB4.vec n‖ ^ 4) := by rw [htrans]
        _ = (ℓ ^ (-(3 : ℝ)) * ℓ ^ (4 : ℕ)) * (∑ n ∈ T.image hlat.lift,
              1 / ‖Work.BoseB4.vec n‖ ^ 4) := by ring
        _ = ℓ * (∑ n ∈ T.image hlat.lift, 1 / ‖Work.BoseB4.vec n‖ ^ 4) := by rw [hpow]
        _ ≤ ℓ * (C2 / (R + 1)) := mul_le_mul_of_nonneg_left happ hℓpos.le
        _ ≤ ℓ * (C2 / R) := by
            refine mul_le_mul_of_nonneg_left ?_ hℓpos.le
            refine div_le_div_of_nonneg_left hC2nn hRpos ?_
            linarith
        _ = 2 * C2 * KH * a := by
            rw [show R = ℓ / (2 * KH * a) from hRdef]
            field_simp
        _ ≤ K₀ * KH * a := by nlinarith [hK2, hKHpos, ha]
    -- ### Row 3: the `‖k‖^{-6}` tail
    have hrow3 : ℓ ^ (-(3 : ℝ)) *
        ∑ k ∈ (Work.BoseB7.excited Mode).filter (fun k => 1 / (2 * KH * a) ≤ ‖kmom k‖),
          1 / ‖kmom k‖ ^ 6 ≤ K₀ * (KH * a) ^ 3 := by
      set T : Finset Mode := (Work.BoseB7.excited Mode).filter
        (fun k => 1 / (2 * KH * a) ≤ ‖kmom k‖) with hT
      have htrans : ∑ k ∈ T, 1 / ‖kmom k‖ ^ 6
          = ℓ ^ 6 * ∑ n ∈ T.image hlat.lift, 1 / ‖Work.BoseB4.vec n‖ ^ 6 :=
        sum_eq_lattice_sum hlat hℓpos T 6
      have hne' : ∀ n ∈ T.image hlat.lift, n ≠ 0 := by
        intro n hn hzero
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
        have hge : 1 / (2 * KH * a) ≤ ‖kmom k‖ := (Finset.mem_filter.mp hk).2
        have hk0 : kmom k = 0 := kmom_eq_zero_of_lift_eq_zero hlat hzero
        rw [hk0, norm_zero] at hge
        have hpos : 0 < 1 / (2 * KH * a) := by positivity
        linarith
      have hlow' : ∀ n ∈ T.image hlat.lift, R ≤ ‖Work.BoseB4.vec n‖ := by
        intro n hn
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
        have hge : 1 / (2 * KH * a) ≤ ‖kmom k‖ := (Finset.mem_filter.mp hk).2
        have h1 : ℓ * (1 / (2 * KH * a)) ≤ ℓ * ‖kmom k‖ :=
          mul_le_mul_of_nonneg_left hge hℓpos.le
        have h2 : ‖Work.BoseB4.vec (hlat.lift k)‖ = ℓ * ‖kmom k‖ :=
          norm_vec_lift_of_dualLattice hlat hℓpos k
        rw [h2, hRdef]
        have h3 : ℓ * (1 / (2 * KH * a)) = ℓ / (2 * KH * a) := by ring
        linarith [h1, h3]
      have happ := hC3 (T.image hlat.lift) R (le_of_lt hRpos) hne' hlow'
      have hpow : ℓ ^ (-(3 : ℝ)) * ℓ ^ (6 : ℕ) = ℓ ^ 3 := by
        have h6 : ℓ ^ (6 : ℕ) = ℓ ^ (6 : ℝ) := (Real.rpow_natCast ℓ 6).symm
        have h3 : ℓ ^ (3 : ℝ) = ℓ ^ (3 : ℕ) := Real.rpow_natCast ℓ 3
        rw [h6, ← Real.rpow_add hℓpos, show (-(3 : ℝ)) + 6 = (3 : ℝ) by norm_num, h3]
      calc ℓ ^ (-(3 : ℝ)) * ∑ k ∈ T, 1 / ‖kmom k‖ ^ 6
          = ℓ ^ (-(3 : ℝ)) * (ℓ ^ 6 * ∑ n ∈ T.image hlat.lift,
              1 / ‖Work.BoseB4.vec n‖ ^ 6) := by rw [htrans]
        _ = (ℓ ^ (-(3 : ℝ)) * ℓ ^ (6 : ℕ)) * (∑ n ∈ T.image hlat.lift,
              1 / ‖Work.BoseB4.vec n‖ ^ 6) := by ring
        _ = ℓ ^ 3 * (∑ n ∈ T.image hlat.lift, 1 / ‖Work.BoseB4.vec n‖ ^ 6) := by rw [hpow]
        _ ≤ ℓ ^ 3 * (C3 / (R + 1) ^ 3) :=
            mul_le_mul_of_nonneg_left happ (by positivity)
        _ ≤ ℓ ^ 3 * (C3 / R ^ 3) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine div_le_div_of_nonneg_left hC3nn (by positivity) ?_
            exact pow_le_pow_left₀ (by linarith) (by linarith) 3
        _ = 8 * C3 * (KH * a) ^ 3 := by
            rw [show R = ℓ / (2 * KH * a) from hRdef]
            first | (field_simp; ring) | field_simp | ring
        _ ≤ K₀ * (KH * a) ^ 3 := by
            have h3 : (0 : ℝ) ≤ (KH * a) ^ 3 := by positivity
            nlinarith [hK3, h3]
    -- ### Row 4: the `‖k‖^{-3}` annulus
    have hrow4 : ℓ ^ (-(3 : ℝ)) *
        ∑ k ∈ ((Work.BoseB7.excited Mode).filter (fun k => 1 / (2 * KH * a) ≤ ‖kmom k‖)).filter
            (fun k => ‖kmom k‖ ≤ 1 / a),
          1 / ‖kmom k‖ ^ 3 ≤ K₀ * (1 + Real.log KH) := by
      set T : Finset Mode := ((Work.BoseB7.excited Mode).filter
        (fun k => 1 / (2 * KH * a) ≤ ‖kmom k‖)).filter (fun k => ‖kmom k‖ ≤ 1 / a) with hT
      have htrans : ∑ k ∈ T, 1 / ‖kmom k‖ ^ 3
          = ℓ ^ 3 * ∑ n ∈ T.image hlat.lift, 1 / ‖Work.BoseB4.vec n‖ ^ 3 :=
        sum_eq_lattice_sum hlat hℓpos T 3
      have hne' : ∀ n ∈ T.image hlat.lift, n ≠ 0 := by
        intro n hn hzero
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
        have hge : 1 / (2 * KH * a) ≤ ‖kmom k‖ :=
          (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
        have hk0 : kmom k = 0 := kmom_eq_zero_of_lift_eq_zero hlat hzero
        rw [hk0, norm_zero] at hge
        have hpos : 0 < 1 / (2 * KH * a) := by positivity
        linarith
      have hlow' : ∀ n ∈ T.image hlat.lift, R ≤ ‖Work.BoseB4.vec n‖ := by
        intro n hn
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
        have hge : 1 / (2 * KH * a) ≤ ‖kmom k‖ :=
          (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
        have h1 : ℓ * (1 / (2 * KH * a)) ≤ ℓ * ‖kmom k‖ :=
          mul_le_mul_of_nonneg_left hge hℓpos.le
        have h2 : ‖Work.BoseB4.vec (hlat.lift k)‖ = ℓ * ‖kmom k‖ :=
          norm_vec_lift_of_dualLattice hlat hℓpos k
        rw [h2, hRdef]
        have h3 : ℓ * (1 / (2 * KH * a)) = ℓ / (2 * KH * a) := by ring
        linarith [h1, h3]
      have hhigh' : ∀ n ∈ T.image hlat.lift, ‖Work.BoseB4.vec n‖ ≤ ℓ / a := by
        intro n hn
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
        have hle : ‖kmom k‖ ≤ 1 / a := (Finset.mem_filter.mp hk).2
        have h1 : ℓ * ‖kmom k‖ ≤ ℓ * (1 / a) := mul_le_mul_of_nonneg_left hle hℓpos.le
        have h2 : ‖Work.BoseB4.vec (hlat.lift k)‖ = ℓ * ‖kmom k‖ :=
          norm_vec_lift_of_dualLattice hlat hℓpos k
        rw [h2]
        have h3 : ℓ * (1 / a) = ℓ / a := by ring
        linarith [h1, h3]
      have hR' : ℓ / a ≤ 2 * KH * R := by
        have heq : 2 * KH * R = ℓ / a := by
          rw [hRdef]
          field_simp
        rw [heq]
      have happ := hC4 (T.image hlat.lift) R (ℓ / a) KH hKH hne' hlow' hhigh' hR'
      have hpow : ℓ ^ (-(3 : ℝ)) * ℓ ^ (3 : ℕ) = 1 := by
        have h3 : ℓ ^ (3 : ℕ) = ℓ ^ (3 : ℝ) := (Real.rpow_natCast ℓ 3).symm
        have h0 : ℓ ^ (0 : ℝ) = 1 := Real.rpow_zero ℓ
        rw [h3, ← Real.rpow_add hℓpos, show (-(3 : ℝ)) + 3 = (0 : ℝ) by norm_num, h0]
      calc ℓ ^ (-(3 : ℝ)) * ∑ k ∈ T, 1 / ‖kmom k‖ ^ 3
          = ℓ ^ (-(3 : ℝ)) * (ℓ ^ 3 * ∑ n ∈ T.image hlat.lift,
              1 / ‖Work.BoseB4.vec n‖ ^ 3) := by rw [htrans]
        _ = (ℓ ^ (-(3 : ℝ)) * ℓ ^ (3 : ℕ)) * (∑ n ∈ T.image hlat.lift,
              1 / ‖Work.BoseB4.vec n‖ ^ 3) := by ring
        _ = ∑ n ∈ T.image hlat.lift, 1 / ‖Work.BoseB4.vec n‖ ^ 3 := by rw [hpow, one_mul]
        _ ≤ C4 * (1 + Real.log KH) := happ
        _ ≤ K₀ * (1 + Real.log KH) := by
            refine mul_le_mul_of_nonneg_right hK4 ?_
            have := Real.log_nonneg hKH
            linarith
    exact ⟨hrow1, hrow2, hrow3, hrow4⟩

end Work.BoseB7AK.K15R
