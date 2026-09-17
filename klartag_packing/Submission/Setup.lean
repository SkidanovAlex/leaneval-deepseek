import Mathlib
import Submission.OmBound
import Submission.DriftGood
import Submission.LatticeGood
import Submission.LatticeGood2
import Submission.ContactFinal
import Submission.Rescale
import Submission.Commons.GeometryOfNumbers.Counting.sum_tailG_annulus_le_of_shell
import Submission.Commons.GeometryOfNumbers.Counting.card_int_points_ball_le_two_omega
import Submission.Commons.GeometryOfNumbers.Counting.exists_prime_radius_C_large
import Submission.Commons.Analysis.Gaussian.integral_shell_weight_le

/-!
# Parameters and the candidate box of the exploration process

This file fixes the numerical parameters of Klartag's construction and builds the finite
candidate box `BoxL` out of the q-ary lattice `(1/R)·ker a`.
-/

open Classical Matrix MeasureTheory ProbabilityTheory
open Submission.MatSpace
open Submission.GenProc
open Submission.Contact
open Submission.OpNorm
open Submission.Weight
open Submission.ContactFinal
open Commons.GeometryOfNumbers.Counting

namespace Submission.Main

noncomputable section

/-- The dimension threshold of the whole construction. -/
def D0 : ℕ := 10 ^ 20

/-- The covolume constant of the q-ary lattice. -/
def Cc : ℝ := 10 ^ 9

/-- The constant `C₀` in the final drift bound `log det A_K ≤ C₀ - 4 log d`. -/
def Cg : ℝ := 10 ^ 6

/-- `a₀ = (1 - 1/d)^{-2}`. -/
def a0 (d : ℕ) : ℝ := ((1 - 1/(d:ℝ))^2)⁻¹

/-- The step size `ε = d^{-2}`. -/
def eps (d : ℕ) : ℝ := 1 / (d:ℝ) ^ 2

/-- The number of steps `K = ⌈16 d² log d⌉`. -/
def KK (d : ℕ) : ℕ := ⌈16 * (d:ℝ)^2 * Real.log d⌉₊

/-- The band radius `r = 24 √(log d)/√d`. -/
def rr (d : ℕ) : ℝ := 24 * Real.sqrt (Real.log d) / Real.sqrt d

/-- The radius of the candidate box. -/
def Rb : ℝ := 2

/-- `ω_d`, the volume of the unit ball. -/
def om (d : ℕ) : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal

/-- The set of nonzero integer vectors in the kernel of `a` of squared norm at most `4R²`. -/
def candIdx (d : ℕ) (q : ℕ) (R : ℝ) (a : Fin d → ZMod q) : Finset (Fin d → ℤ) :=
  (intPoints (d := d) (2 * R)).filter (fun x => x ≠ 0 ∧ LatticeGood2.kerCond a x)

/-- The candidate box, as a family indexed by `Fin m`. -/
def BoxL (d : ℕ) (q : ℕ) (R : ℝ) (a : Fin d → ZMod q) :
    Fin (candIdx d q R a).card → Vec d :=
  fun i => (1 / R) • intVec ((candIdx d q R a).equivFin.symm i : Fin d → ℤ)

variable {d : ℕ} {q : ℕ} {R : ℝ} {a : Fin d → ZMod q}

/-! ## Elementary properties of `kerCond`, `intQ` and `intVec` -/

lemma intVec_neg (k : Fin d → ℤ) : intVec (-k) = -intVec k := by
  ext i
  simp [intVec, Pi.neg_apply]

lemma intQ_neg (k : Fin d → ℤ) : intQ (-k) = intQ k := by
  simp only [intQ, intVec_neg, norm_neg]

lemma kerCond_neg {k : Fin d → ℤ} (h : LatticeGood2.kerCond a k) :
    LatticeGood2.kerCond a (-k) := by
  simp only [LatticeGood2.kerCond] at h ⊢
  calc ∑ i, ((-k) i : ZMod q) * a i = ∑ i, -(((k i : ZMod q)) * a i) :=
        Finset.sum_congr rfl fun i _ => by simp [Pi.neg_apply]
    _ = -(∑ i, (k i : ZMod q) * a i) :=
          Finset.sum_neg_distrib (f := fun i => (k i : ZMod q) * a i)
    _ = 0 := by rw [h, neg_zero]

lemma smul_intVec_div (k : Fin d → ℤ) :
    (1 / R) • intVec k = WithLp.toLp 2 (fun i : Fin d => (k i : ℝ) / R) := by
  ext i
  simp [intVec, PiLp.smul_apply, div_eq_inv_mul]

lemma norm_smul_intVec (hR : 0 < R) (k : Fin d → ℤ) :
    ‖(1 / R) • intVec k‖ = ‖intVec k‖ / R := by
  rw [smul_intVec_div (d := d) k, Submission.LatticeGood.norm_toLp_div R hR k]
  simp only [intVec]

lemma intQ_of_smul (hR : 0 < R) (k : Fin d → ℤ) :
    intQ k = R ^ 2 * ‖(1 / R) • intVec k‖ ^ 2 := by
  rw [norm_smul_intVec hR, div_pow, intQ]
  field_simp

lemma intVec_injective : Function.Injective (intVec (d := d)) := by
  intro x y h
  ext i
  have h2 := congrArg (fun v : Vec d => v i) h
  simp only [intVec_apply] at h2
  exact_mod_cast h2

/-! ## The candidate box -/

lemma idx_mem {i : Fin (candIdx d q R a).card} :
    ((candIdx d q R a).equivFin.symm i : Fin d → ℤ) ∈ candIdx d q R a :=
  ((candIdx d q R a).equivFin.symm i).2

lemma idx_ne_zero {i : Fin (candIdx d q R a).card} :
    ((candIdx d q R a).equivFin.symm i : Fin d → ℤ) ≠ 0 := by
  have := idx_mem (d := d) (q := q) (R := R) (a := a) (i := i)
  simp only [candIdx, Finset.mem_filter, mem_intPoints] at this
  exact this.2.1

lemma idx_ker {i : Fin (candIdx d q R a).card} :
    LatticeGood2.kerCond a ((candIdx d q R a).equivFin.symm i : Fin d → ℤ) := by
  have := idx_mem (d := d) (q := q) (R := R) (a := a) (i := i)
  simp only [candIdx, Finset.mem_filter, mem_intPoints] at this
  exact this.2.2

lemma idx_quad {i : Fin (candIdx d q R a).card} :
    intQ ((candIdx d q R a).equivFin.symm i : Fin d → ℤ) ≤ 4 * R ^ 2 := by
  have := idx_mem (d := d) (q := q) (R := R) (a := a) (i := i)
  simp only [candIdx, Finset.mem_filter, mem_intPoints] at this
  have h : intQ ((candIdx d q R a).equivFin.symm i : Fin d → ℤ) ≤ (2 * R) ^ 2 := this.1
  rw [intQ] at h ⊢
  nlinarith [h]

lemma boxL_injective (hR : 0 < R) : Function.Injective (BoxL d q R a) := by
  intro i j hij
  have h1 : intVec ((candIdx d q R a).equivFin.symm i : Fin d → ℤ)
      = intVec ((candIdx d q R a).equivFin.symm j : Fin d → ℤ) := by
    have h2 := congrArg (fun v : Vec d => R • v) hij
    unfold BoxL at h2
    rw [smul_smul, smul_smul, mul_one_div, div_self (ne_of_gt hR), one_smul, one_smul] at h2
    exact h2
  have h3 : ((candIdx d q R a).equivFin.symm i : Fin d → ℤ)
      = ((candIdx d q R a).equivFin.symm j : Fin d → ℤ) := intVec_injective h1
  exact (candIdx d q R a).equivFin.symm.injective (Subtype.ext h3)

lemma boxL_ne_zero (hR : 0 < R) (i : Fin (candIdx d q R a).card) :
    BoxL d q R a i ≠ 0 := by
  intro h
  have h2 : intVec ((candIdx d q R a).equivFin.symm i : Fin d → ℤ) = 0 := by
    rcases smul_eq_zero.mp h with h' | h'
    · exact absurd h' (by positivity)
    · exact h'
  have := Weight.intQ_pos_of_ne_zero (idx_ne_zero (d := d) (q := q) (R := R) (a := a) (i := i))
  rw [intQ, h2, norm_zero] at this
  norm_num at this

lemma boxL_norm_le (hR : 0 < R) (i : Fin (candIdx d q R a).card) :
    ‖BoxL d q R a i‖ ≤ 2 := by
  have hle := idx_quad (d := d) (q := q) (R := R) (a := a) (i := i)
  rw [show BoxL d q R a i = (1 / R) • intVec ((candIdx d q R a).equivFin.symm
      i : Fin d → ℤ) from rfl, norm_smul_intVec hR]
  have h1 : ‖intVec ((candIdx d q R a).equivFin.symm i : Fin d → ℤ)‖ ^ 2 ≤ 4 * R ^ 2 := by
    rw [← intQ]; exact hle
  have h2 : ‖intVec ((candIdx d q R a).equivFin.symm i : Fin d → ℤ)‖ ≤ 2 * R := by
    nlinarith [norm_nonneg (intVec ((candIdx d q R a).equivFin.symm i : Fin d → ℤ)), hR, h1]
  rw [div_le_iff₀ hR]
  linarith

lemma one_lt_a0 (hd : 2 ≤ d) : 1 < a0 d := by
  have hd1 : (1:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 1 < d)
  have hpos : (0:ℝ) < (d:ℝ) := by linarith
  have hlt : 1/(d:ℝ) < 1 := by rw [div_lt_one hpos]; linarith
  have h2 : (1 - 1/(d:ℝ))^2 < 1 := by
    have h3 : 0 < 1/(d:ℝ) := by positivity
    nlinarith
  have h3 : 0 < (1 - 1/(d:ℝ))^2 := by
    have : 0 < 1 - 1/(d:ℝ) := by linarith
    positivity
  rw [a0]
  exact (one_lt_inv₀ h3).mpr h2

lemma boxL_min (hR : 0 < R) (hd : 2 ≤ d)
    (hmin : ∀ k : Fin d → ℤ, 0 < intQ k → intQ k ≤ R ^ 2 → ¬ LatticeGood2.kerCond a k)
    (i : Fin (candIdx d q R a).card) :
    1 < a0 d * ‖BoxL d q R a i‖ ^ 2 := by
  set k : Fin d → ℤ := ((candIdx d q R a).equivFin.symm i : Fin d → ℤ) with hk
  have hk0 : k ≠ 0 := idx_ne_zero (d := d) (q := q) (R := R) (a := a) (i := i)
  have hker : LatticeGood2.kerCond a k := idx_ker (d := d) (q := q) (R := R) (a := a) (i := i)
  have hpos : 0 < intQ k := Weight.intQ_pos_of_ne_zero hk0
  have hgt : R ^ 2 < intQ k := by
    by_contra hcon
    push Not at hcon
    exact hmin k hpos hcon hker
  have hQ : intQ k = R ^ 2 * ‖BoxL d q R a i‖ ^ 2 := by
    rw [show BoxL d q R a i = (1 / R) • intVec k from rfl]
    exact intQ_of_smul hR k
  have hsq : 1 < ‖BoxL d q R a i‖ ^ 2 := by
    have hR2 : (0:ℝ) < R ^ 2 := by positivity
    have h : R ^ 2 * 1 < R ^ 2 * ‖BoxL d q R a i‖ ^ 2 := by
      rw [← hQ, mul_one]; exact hgt
    exact lt_of_mul_lt_mul_left h (le_of_lt hR2)
  have ha0 := one_lt_a0 (d := d) hd
  nlinarith [ha0, hsq]

lemma boxL_negL (hR : 0 < R) (i : Fin (candIdx d q R a).card) :
    ∃ j : Fin (candIdx d q R a).card, BoxL d q R a j = -BoxL d q R a i := by
  classical
  set k : Fin d → ℤ := ((candIdx d q R a).equivFin.symm i : Fin d → ℤ) with hk
  have hker : LatticeGood2.kerCond a k := idx_ker (d := d) (q := q) (R := R) (a := a) (i := i)
  have hquad : ‖intVec k‖ ^ 2 ≤ 4 * R ^ 2 := by
    have h := idx_quad (d := d) (q := q) (R := R) (a := a) (i := i)
    rw [intQ] at h
    exact h
  have hk0 : k ≠ 0 := idx_ne_zero (d := d) (q := q) (R := R) (a := a) (i := i)
  have hmem : -k ∈ candIdx d q R a := by
    simp only [candIdx, Finset.mem_filter, mem_intPoints]
    exact ⟨by rw [intQ, intVec_neg, norm_neg]; nlinarith [hquad], by simpa using hk0,
      kerCond_neg hker⟩
  refine ⟨(candIdx d q R a).equivFin ⟨-k, hmem⟩, ?_⟩
  show (1 / R) • intVec ((candIdx d q R a).equivFin.symm
      ((candIdx d q R a).equivFin ⟨-k, hmem⟩) : Fin d → ℤ) = -((1 / R) • intVec k)
  rw [Equiv.symm_apply_apply, intVec_neg, smul_neg]

lemma boxL_hbox (hR : 0 < R) (Λ : Submodule ℤ (Vec d)) (hΛmem : ∀ x : Vec d, x ∈ Λ →
      ∃ k : Fin d → ℤ, LatticeGood2.kerCond a k ∧ x = (1 / R) • intVec k)
    {x : Vec d} (hx : x ∈ Λ) (hx0 : x ≠ 0) (hxn : ‖x‖ ≤ 2) :
    ∃ i : Fin (candIdx d q R a).card, BoxL d q R a i = x := by
  classical
  obtain ⟨k, hk, hkx⟩ := hΛmem x hx
  have hk0 : k ≠ 0 := by
    intro h0
    apply hx0
    have hz : intVec k = 0 := by
      rw [h0]; ext i; simp [intVec]
    rw [hkx, hz, smul_zero]
  have h4 : intQ k ≤ 4 * R ^ 2 := by
    have hQ : intQ k = R ^ 2 * ‖x‖ ^ 2 := by
      rw [hkx]; exact intQ_of_smul hR k
    rw [hQ]
    have hx2 : ‖x‖ ^ 2 ≤ 4 := by nlinarith [hxn, norm_nonneg x]
    nlinarith [hx2, sq_nonneg R]
  have hmem : k ∈ candIdx d q R a := by
    simp only [candIdx, Finset.mem_filter, mem_intPoints]
    exact ⟨by rw [intQ] at h4 ⊢; nlinarith [h4], hk0, hk⟩
  refine ⟨(candIdx d q R a).equivFin ⟨k, hmem⟩, ?_⟩
  show (1 / R) • intVec ((candIdx d q R a).equivFin.symm
      ((candIdx d q R a).equivFin ⟨k, hmem⟩) : Fin d → ℤ) = x
  rw [Equiv.symm_apply_apply]
  exact hkx.symm

lemma sum_BoxL (g : Vec d → ℝ) :
    ∑ i : Fin (candIdx d q R a).card, g (BoxL d q R a i)
      = ∑ k ∈ candIdx d q R a, g ((1 / R) • intVec k) := by
  classical
  have h1 : (∑ i : Fin (candIdx d q R a).card, g (BoxL d q R a i))
      = ∑ y : ↥(candIdx d q R a), g ((1 / R) • intVec (y : Fin d → ℤ)) := by
    rw [show (∑ i : Fin (candIdx d q R a).card, g (BoxL d q R a i))
        = ∑ i : Fin (candIdx d q R a).card,
            (fun y : ↥(candIdx d q R a) => g ((1 / R) • intVec (y : Fin d → ℤ)))
              ((candIdx d q R a).equivFin.symm i) from rfl]
    exact Equiv.sum_comp (candIdx d q R a).equivFin.symm
      (fun y : ↥(candIdx d q R a) => g ((1 / R) • intVec (y : Fin d → ℤ)))
  rw [h1]
  exact Finset.sum_attach (candIdx d q R a)
    (fun y : Fin d → ℤ => g ((1 / R) • intVec y))

lemma Wt_smul_intVec (hR : 0 < R) (K : ℕ) (A : ℝ) {k : Fin d → ℤ}
    (h1 : R ^ 2 < intQ k) (h2 : intQ k ≤ 4 * R ^ 2) :
    Wt (d := d) K A (eps d) ((1 / R) • intVec k) = wt (d := d) K A R k := by
  rw [wt_of_mem_annulus K A R h1 h2]
  simp only [Wt, eps]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hRne : R ≠ 0 := ne_of_gt hR
  have hQne : intQ k ≠ 0 := ne_of_gt (lt_trans (by positivity : (0:ℝ) < R ^ 2) h1)
  have hR2ne : R ^ 2 ≠ 0 := ne_of_gt (by positivity : (0:ℝ) < R ^ 2)
  have hnorm : ‖(1 / R) • intVec k‖ ^ 2 = intQ k / R ^ 2 := by
    rw [intQ_of_smul hR k]
    field_simp
  rw [hnorm]
  field_simp


lemma sum_filter_ne_zero_kerCond (g : (Fin d → ℤ) → ℝ) (hg : g 0 = 0) :
    ∑ k ∈ (intPoints (d := d) (2 * R)).filter (fun x => x ≠ 0 ∧ LatticeGood2.kerCond a x),
        g k
      = ∑ k ∈ (intPoints (d := d) (2 * R)).filter (fun x => LatticeGood2.kerCond a x), g k := by
  classical
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.2⟩
  · intro x hx hx'
    simp only [Finset.mem_filter] at hx hx'
    have hne : ¬ (x ≠ 0) := fun hc => hx' ⟨hx.1, hc, hx.2⟩
    rw [not_not] at hne
    rw [hne]; exact hg

/-- **The weighted mass of the candidate box.**  The sum of the per-candidate weights over the
box is at most the weighted lattice sum over the integers in the kernel of `a`. -/
theorem sum_Wt_BoxL {B : ℝ} (hR : 0 < R)
    (hmin : ∀ k : Fin d → ℤ, 0 < intQ k → intQ k ≤ R ^ 2 → ¬ LatticeGood2.kerCond a k)
    (K : ℕ) (A : ℝ)
    (hb : ∑ k ∈ (intPoints (d := d) (2 * R)).filter (fun x => LatticeGood2.kerCond a x),
        wt (d := d) K A R k ≤ B) :
    ∑ i : Fin (candIdx d q R a).card, Wt (d := d) K A (eps d) (BoxL d q R a i) ≤ B := by
  classical
  rw [sum_BoxL]
  have hpt : ∀ k ∈ candIdx d q R a,
      Wt (d := d) K A (eps d) ((1 / R) • intVec k) = wt (d := d) K A R k := by
    intro k hk
    have hk' : k ∈ (intPoints (d := d) (2 * R)).filter
        (fun x => x ≠ 0 ∧ LatticeGood2.kerCond a x) := by
      simpa only [candIdx] using hk
    obtain ⟨hmem, hk0, hker⟩ := Finset.mem_filter.mp hk'
    refine Wt_smul_intVec hR K A ?_ ?_
    · have hpos : 0 < intQ k := Weight.intQ_pos_of_ne_zero hk0
      by_contra hcon
      push Not at hcon
      exact hmin k hpos hcon hker
    · have h := (mem_intPoints (d := d) (R := 2 * R)).mp hmem
      rw [intQ] at h ⊢
      nlinarith [h]
  rw [Finset.sum_congr rfl hpt]
  show (∑ k ∈ (intPoints (d := d) (2 * R)).filter
      (fun x => x ≠ 0 ∧ LatticeGood2.kerCond a x), wt (d := d) K A R k) ≤ B
  have hzero : wt (d := d) K A R 0 = 0 := by
    rw [wt]
    have h0 : intQ (0 : Fin d → ℤ) = 0 := by
      rw [intQ, show intVec (0 : Fin d → ℤ) = 0 from by ext i; simp [intVec]]
      simp
    rw [h0]
    exact if_neg (by rintro ⟨h1, -⟩; linarith [sq_nonneg R])
  rw [sum_filter_ne_zero_kerCond (R := R) (a := a) (wt (d := d) K A R) hzero]
  exact hb


lemma eps_pos (d : ℕ) (hd : 0 < d) : 0 < eps d := by
  rw [eps]; positivity

lemma one_div_eps (d : ℕ) : 1 / eps d = (d:ℝ) ^ 2 := by
  rw [eps, one_div_one_div]

end

end Submission.Main
