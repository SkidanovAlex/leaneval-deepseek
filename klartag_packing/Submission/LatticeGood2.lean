import Mathlib
import Submission.Weight
import Submission.Commons.Lattice.Counting.exists_qary_weighted_sum_le_ne_zero
import Submission.Commons.Lattice.Counting.exists_qary_lattice_covolume_and_image

/-!
# The q-ary covector and the lattice `Λ_A = (1/R)·ker a`

Given the prime `q` and the radius `R` of
`Commons.GeometryOfNumbers.Counting.exists_prime_radius_C_large` (so that `C ω_d R^d = q`), this
file performs the single weighted first-moment argument that produces

* the *minimum-norm* property of `Λ_A`: `#{x ∈ ker a : 0 < Q(x) ≤ R²} = 0`, and
* the *weight bound* `∑_{x ∈ ker a} w(x) ≤ d⁴/2`,

for `a : Fin d → ZMod q` a suitable covector.  Both come from one application of
`Commons.Lattice.Counting.exists_qary_weighted_sum_le_ne_zero` with the combined weight
`f = 1_{Q ≤ R²} + δ·w`, `δ = 2/d⁴`, as in `PLAN_V11 §3`.
-/

namespace Submission.LatticeGood2

open Classical Matrix MeasureTheory
open Submission.Weight

noncomputable section

set_option linter.style.haveILetI false

variable {d : ℕ}

/-- The kernel condition `a · x = 0` in `ZMod q`. -/
def kerCond {q : ℕ} (a : Fin d → ZMod q) (x : Fin d → ℤ) : Prop :=
  ∑ i, (x i : ZMod q) * a i = 0

variable (q : ℕ)

/-- The weighted first-moment argument.  Given the prime `q`, the radius `R` with
`C ω R^d = q`, a bound for the number of integer points of the ball of radius `R` and a bound for
the total weight, this produces a covector `a` whose kernel has no short vectors and whose
weighted mass is at most `d⁴/2`. -/
theorem exists_covector {R C ω : ℝ} {K : ℕ} {a₀ : ℝ} (hd : 2 ≤ d) (hq : q.Prime)
    (hR : 0 < R) (hR1 : 1 ≤ R) (hRq : 2 * R < (q : ℝ)) (hω : 0 < ω) (hC : 4 ≤ C)
    (hqR : C * ω * R ^ d = (q : ℝ))
    (hcount : (((intPoints (d := d) R).filter (fun x => 0 < intQ x)).card : ℝ) ≤ 2 * ω * R ^ d)
    (hWsum : ∑ x ∈ intPoints (d := d) (2 * R), wt (d := d) K a₀ R x
        ≤ 10 ^ 7 * (d : ℝ) ^ 4 * ω * R ^ d)
    (hCge : 10 ^ 9 ≤ C) :
    ∃ a : Fin d → ZMod q, a ≠ 0 ∧
      (∀ x : Fin d → ℤ, 0 < intQ x → intQ x ≤ R ^ 2 → ¬ kerCond (d := d) a x) ∧
      (∑ x ∈ (intPoints (d := d) (2 * R)).filter (fun x => kerCond (d := d) a x),
          wt (d := d) K a₀ R x) ≤ (d : ℝ) ^ 4 / 2 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hd0 : 0 < d := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hRnonneg : 0 ≤ R := le_of_lt hR
  have hR2pos : (0 : ℝ) < R ^ 2 := by positivity
  -- the finset `S` of nonzero integer points of the ball of radius `2R`
  set S : Finset (Fin d → ℤ) := (intPoints (d := d) (2 * R)).filter (fun x => 0 < intQ x)
    with hS
  have hSsub : S ⊆ intPoints (d := d) (2 * R) := fun x hx => (Finset.mem_filter.mp hx).1
  have hSmem : ∀ x, x ∈ S ↔ intQ x ≤ 4 * R ^ 2 ∧ 0 < intQ x := by
    intro x
    rw [hS, Finset.mem_filter, mem_intPoints]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by nlinarith [h1], h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by nlinarith [h1], h2⟩
  -- every element of `S` is nonzero modulo `q`
  have hSne : ∀ x ∈ S, ∃ j, (x j : ZMod q) ≠ 0 := by
    intro x hx
    obtain ⟨-, hpos⟩ := (hSmem x).mp hx
    have hxne : x ≠ 0 := by
      intro h
      rw [h, intQ_eq_sum] at hpos
      simp at hpos
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hxne
    refine ⟨j, fun h0 => ?_⟩
    have hdvd : (q : ℤ) ∣ x j := (ZMod.intCast_zmod_eq_zero_iff_dvd (x j) q).mp h0
    have hle : (q : ℤ) ≤ |x j| := by
      rcases hdvd with ⟨k, hk⟩
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hk
        exact hj hk
      rw [hk, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (q : ℤ))]
      have hk1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
      nlinarith [hq0]
    have hxj : |((x j : ℤ) : ℝ)| ≤ ‖Commons.GeometryOfNumbers.Counting.intVec x‖ := by
      have := PiLp.norm_apply_le (p := 2) (β := fun _ : Fin d => ℝ)
        (x := Commons.GeometryOfNumbers.Counting.intVec x) j
      simpa [Real.norm_eq_abs, Commons.GeometryOfNumbers.Counting.intVec] using this
    have hnorm : ‖Commons.GeometryOfNumbers.Counting.intVec x‖ ≤ 2 * R := by
      have h2 : intQ x ≤ (2 * R) ^ 2 := by
        have := (hSmem x).mp hx |>.1
        nlinarith [this]
      rw [Submission.Weight.intQ] at h2
      nlinarith [norm_nonneg (Commons.GeometryOfNumbers.Counting.intVec x), hRnonneg]
    have hcast : (q : ℝ) ≤ |((x j : ℤ) : ℝ)| := by exact_mod_cast hle
    linarith [hRq, hxj, hnorm]
  -- the combined weight
  set δ : ℝ := 2 / (d : ℝ) ^ 4 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδd : δ * ((d : ℝ) ^ 4) = 2 := by rw [hδdef]; field_simp
  let f : (Fin d → ℤ) → ℝ := fun x =>
    (if intQ x ≤ R ^ 2 then 1 else 0) + δ * wt (d := d) K a₀ R x
  have hf : ∀ x, 0 ≤ f x := by
    intro x
    have h1 : (0 : ℝ) ≤ if intQ x ≤ R ^ 2 then 1 else 0 := by split <;> norm_num
    have h2 : 0 ≤ δ * wt (d := d) K a₀ R x :=
      mul_nonneg (le_of_lt hδpos) (wt_nonneg K a₀ R x)
    simp only [f]; linarith
  -- one application of the q-ary first-moment lemma
  obtain ⟨A, hA⟩ :=
    Commons.Lattice.Counting.exists_qary_weighted_sum_le_ne_zero (q := q) (m := 1) (d := d)
      S f hf hSne
  set a : Fin d → ZMod q := fun j => A 0 j with hadef
  have hker : ∀ x, (∀ i : Fin 1, ∑ j, (x j : ZMod q) * A i j = 0) ↔ kerCond (d := d) a x := by
    intro x
    rw [kerCond, hadef]
    exact Fin.forall_fin_one
  -- the bound on the total weight over `S`
  have hcount' : (∑ x ∈ S, if intQ x ≤ R ^ 2 then (1 : ℝ) else 0) ≤ 2 * ω * R ^ d := by
    rw [Finset.sum_boole]
    have hcard : {x ∈ S | intQ x ≤ R ^ 2} ⊆ {x ∈ intPoints (d := d) R | 0 < intQ x} := by
      intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨mem_intPoints.mpr (by nlinarith [hx.2, hRnonneg]), (hSmem x).mp hx.1 |>.2⟩
    exact le_trans (by exact_mod_cast Finset.card_le_card hcard) hcount
  have hsumS : ∑ x ∈ S, wt (d := d) K a₀ R x ≤ 10 ^ 7 * (d : ℝ) ^ 4 * ω * R ^ d :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hSsub
      (fun x _ _ => wt_nonneg K a₀ R x)) hWsum
  have hsumSf : ∑ x ∈ S, f x
      = (∑ x ∈ S, if intQ x ≤ R ^ 2 then (1 : ℝ) else 0)
        + δ * ∑ x ∈ S, wt (d := d) K a₀ R x := by
    simp only [f, Finset.sum_add_distrib, Finset.mul_sum]
  have hqinv : 0 ≤ 2 * ((q : ℝ) ^ 1)⁻¹ := by
    have : (0 : ℝ) < (q : ℝ) := hq0
    positivity
  have hbound : ∑ x ∈ S, (if (∀ i : Fin 1, ∑ j, (x j : ZMod q) * A i j = 0) then f x else 0)
      ≤ 2 * ((q : ℝ) ^ 1)⁻¹ * (2 * ω * R ^ d + δ * (10 ^ 7 * (d : ℝ) ^ 4 * ω * R ^ d)) := by
    refine le_trans hA ?_
    rw [hsumSf]
    exact mul_le_mul_of_nonneg_left
      (add_le_add hcount' (mul_le_mul_of_nonneg_left hsumS (le_of_lt hδpos))) hqinv
  -- the numerical bound `2 q⁻¹ (…) < 1`
  have hsmall : 2 * ((q : ℝ) ^ 1)⁻¹
      * (2 * ω * R ^ d + δ * (10 ^ 7 * (d : ℝ) ^ 4 * ω * R ^ d)) < 1 := by
    have hkey : 2 * ((q : ℝ) ^ 1)⁻¹
          * (2 * ω * R ^ d + δ * (10 ^ 7 * (d : ℝ) ^ 4 * ω * R ^ d))
        = (4 * ω * R ^ d + 2 * 10 ^ 7 * (δ * (d : ℝ) ^ 4) * ω * R ^ d) / (q : ℝ) := by
      rw [pow_one]
      field_simp
      ring
    rw [hkey, hδd]
    rw [show (q : ℝ) = C * ω * R ^ d from hqR.symm]
    have hprod : (0 : ℝ) < C * ω * R ^ d := by positivity
    rw [div_lt_one hprod]
    nlinarith [hCge, hprod, hω, pow_pos hR d]
  -- conclusion 1: the minimum-norm property
  have hmin : ∀ x : Fin d → ℤ, 0 < intQ x → intQ x ≤ R ^ 2 → ¬ kerCond (d := d) a x := by
    intro x hxpos hxle hkerx
    have hxS : x ∈ S := (hSmem x).mpr ⟨by nlinarith [hxle, hRnonneg], hxpos⟩
    have hxker : ∀ i : Fin 1, ∑ j, (x j : ZMod q) * A i j = 0 := (hker x).mpr hkerx
    have hfx : 1 ≤ f x := by
      have h1 : (if intQ x ≤ R ^ 2 then (1 : ℝ) else 0) = 1 := if_pos hxle
      have h2 : 0 ≤ δ * wt (d := d) K a₀ R x :=
        mul_nonneg (le_of_lt hδpos) (wt_nonneg K a₀ R x)
      simp only [f, h1]; linarith
    have hnn : 0 ≤ ∑ y ∈ S.erase x,
        (if (∀ i : Fin 1, ∑ j, (y j : ZMod q) * A i j = 0) then f y else 0) :=
      Finset.sum_nonneg fun y _ => by split <;> [exact hf y; norm_num]
    have hge : 1 ≤ ∑ y ∈ S,
        (if (∀ i : Fin 1, ∑ j, (y j : ZMod q) * A i j = 0) then f y else 0) := by
      rw [← Finset.sum_erase_add _ _ hxS, if_pos hxker]
      linarith
    linarith [hbound, hsmall, hge]
  -- conclusion 2: the weight bound
  have hweight : (∑ x ∈ (intPoints (d := d) (2 * R)).filter (fun x => kerCond (d := d) a x),
        wt (d := d) K a₀ R x) ≤ (d : ℝ) ^ 4 / 2 := by
    rw [Finset.sum_filter]
    have hzero : ∀ x ∈ intPoints (d := d) (2 * R), x ∉ S →
        (if kerCond (d := d) a x then wt (d := d) K a₀ R x else 0) = 0 := by
      intro x hx hxS
      have hle : intQ x ≤ 4 * R ^ 2 := by
        have := mem_intPoints.mp hx
        nlinarith [this]
      have hnotpos : ¬ (0 < intQ x) := fun hpos => hxS ((hSmem x).mpr ⟨hle, hpos⟩)
      have hz : intQ x = 0 := le_antisymm (not_lt.mp hnotpos) (intQ_nonneg x)
      have hwt : wt (d := d) K a₀ R x = 0 := by
        refine wt_eq_zero_of_not_annulus (d := d) K a₀ R fun hc => ?_
        exact absurd hz (ne_of_gt (lt_of_lt_of_le hR2pos (le_of_lt hc.1)))
      rw [hwt]
      by_cases hc : kerCond (d := d) a x <;> simp [hc]
    rw [← Finset.sum_subset hSsub hzero]
    have hF_le : δ * ∑ x ∈ S, (if kerCond (d := d) a x then wt (d := d) K a₀ R x else 0)
        ≤ ∑ x ∈ S, (if (∀ i : Fin 1, ∑ j, (x j : ZMod q) * A i j = 0) then f x else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [if_congr (hker x) rfl rfl]
      by_cases hc : kerCond (d := d) a x
      · rw [if_pos hc, if_pos hc]
        have h1 : (0 : ℝ) ≤ if intQ x ≤ R ^ 2 then 1 else 0 := by split <;> norm_num
        have h2 : 0 ≤ δ * wt (d := d) K a₀ R x :=
          mul_nonneg (le_of_lt hδpos) (wt_nonneg K a₀ R x)
        simp only [f]; linarith
      · rw [if_neg hc, if_neg hc]; norm_num
    have hlt : δ * (∑ x ∈ S, (if kerCond (d := d) a x then wt (d := d) K a₀ R x else 0)) < 1 :=
      lt_of_le_of_lt hF_le (lt_of_le_of_lt hbound hsmall)
    have hfin : (∑ x ∈ S, (if kerCond (d := d) a x then wt (d := d) K a₀ R x else 0))
        ≤ 1 / δ := by
      rw [le_div_iff₀ hδpos, mul_comm]
      exact le_of_lt hlt
    have h1δ : 1 / δ = (d : ℝ) ^ 4 / 2 := by rw [hδdef]; field_simp
    rwa [h1δ] at hfin
  -- `a ≠ 0`
  refine ⟨a, ?_, hmin, hweight⟩
  intro ha0
  exfalso
  let j0 : Fin d := ⟨0, hd0⟩
  let e : Fin d → ℤ := Pi.single j0 1
  have heQ : intQ e = 1 := by
    rw [intQ_eq_sum]
    have h : ∀ i : Fin d, (e i : ℝ) ^ 2 = if i = j0 then (1 : ℝ) else 0 := by
      intro i
      by_cases hi : i = j0
      · subst hi; simp [e]
      · rw [if_neg hi, show e i = 0 from Pi.single_eq_of_ne hi 1]
        norm_num
    rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_eq_single j0]
    · simp
    · intro b _ hb; rw [if_neg hb]
    · intro h; exact absurd (Finset.mem_univ j0) h
  have hker0 : kerCond (d := d) a e := by
    simp [kerCond, ha0]
  exact (hmin e (by rw [heQ]; norm_num) (by rw [heQ]; nlinarith)) hker0

end

end Submission.LatticeGood2
