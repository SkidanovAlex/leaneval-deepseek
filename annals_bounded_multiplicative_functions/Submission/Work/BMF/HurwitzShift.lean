import Mathlib
import Submission.Commons.NumberTheory.Zeta.isPreconnected_re_gt_sdiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The shift-difference decomposition of the Hurwitz zeta function

For `0 < a ≤ 1` and `s` in the half-plane `0 < re s` (with `s ≠ 1`):

  `ζ(s,a) - ζ(s) = ∑_{m≥0} ((m+a)^{-s} - (m+1)^{-s})`,

an identity valid for `1 < re s` by subtracting the two absolutely convergent Dirichlet
series, which extends to the whole half-plane by analytic continuation.  The series converges
absolutely for `0 < re s`, and its dyadic blocks are differences of sums of the form
`∑ (n+u)^{-it}` (so Vinogradov–Korobov savings apply).
-/

namespace Work.BMF

open Filter
open scoped Topology BigOperators

noncomputable section

/-- The `m`-th term of the shift-difference series: `(m+a)^{-s} - (m+1)^{-s}`. -/
def shiftTerm (a : ℝ) (m : ℕ) (s : ℂ) : ℂ :=
  ((((m : ℝ) + a : ℝ)) : ℂ) ^ (-s) - (((m + 1 : ℕ) : ℝ) : ℂ) ^ (-s)

/-! ## Elementary estimates -/

private lemma notMem_uIcc_of_pos {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (0 : ℝ) ∉ Set.uIcc x y := by
  intro h
  rcases Set.mem_uIcc.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
  · linarith
  · linarith

private lemma norm_cpow_neg_sub_eq {s : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-s.re - 1) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx (-s - 1)]
  simp [Complex.neg_re, Complex.sub_re, Complex.one_re]

private lemma integral_norm_cpow_neg_sub {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (s : ℂ)
    (hs : 0 < s.re) :
    (∫ t : ℝ in x..y, ‖(t : ℂ) ^ (-s - 1)‖) = (x ^ (-s.re) - y ^ (-s.re)) / s.re := by
  have hnot0 : (0 : ℝ) ∉ Set.uIcc x y := notMem_uIcc_of_pos hx hxy
  have hne : -s.re - 1 ≠ (-1 : ℝ) := by linarith
  calc
    (∫ t : ℝ in x..y, ‖(t : ℂ) ^ (-s - 1)‖)
        = ∫ t : ℝ in x..y, t ^ (-s.re - 1) := by
          apply intervalIntegral.integral_congr
          intro t ht
          have ht' : t ∈ Set.Icc x y := by simpa [Set.uIcc_of_le hxy] using ht
          exact norm_cpow_neg_sub_eq (lt_of_lt_of_le hx ht'.1)
    _ = (x ^ (-s.re) - y ^ (-s.re)) / s.re := by
          have hint := integral_rpow (r := -s.re - 1) (a := x) (b := y) (Or.inr ⟨hne, hnot0⟩)
          rw [hint]
          have hD : -s.re - 1 + 1 = -s.re := by ring
          rw [hD]
          field_simp [ne_of_gt hs]
          ring

private lemma cpow_neg_sub_eq_smul_integral {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (s : ℂ)
    (hs : 0 < s.re) :
    (x : ℂ) ^ (-s) - (y : ℂ) ^ (-s) = s * (∫ t : ℝ in x..y, (t : ℂ) ^ (-s - 1)) := by
  have hnot0 : (0 : ℝ) ∉ Set.uIcc x y := notMem_uIcc_of_pos hx hxy
  have hsnz : s ≠ 0 := fun h => (ne_of_gt hs) (by simpa [h])
  have hne : (-s - 1 : ℂ) ≠ (-1 : ℂ) := by
    intro h
    apply hsnz
    have h' := congrArg Complex.re h
    have : -s.re - 1 = -1 := by
      simpa [Complex.neg_re, Complex.sub_re, Complex.one_re] using h'
    linarith
  have hint := integral_cpow (r := -s - 1) (a := x) (b := y) (Or.inr ⟨hne, hnot0⟩)
  rw [hint]
  have hsneg : (-s : ℂ) ≠ 0 := fun h => hsnz (neg_eq_zero.mp h)
  field_simp [hsneg]
  ring

private lemma norm_cpow_neg_sub_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (s : ℂ)
    (hs : 0 < s.re) :
    ‖(y : ℂ) ^ (-s) - (x : ℂ) ^ (-s)‖ ≤ (‖s‖ / s.re) * (x ^ (-s.re) - y ^ (-s.re)) := by
  have hsub := cpow_neg_sub_eq_smul_integral hx hxy s hs
  calc
    ‖(y : ℂ) ^ (-s) - (x : ℂ) ^ (-s)‖
        = ‖(x : ℂ) ^ (-s) - (y : ℂ) ^ (-s)‖ := by
          rw [← norm_neg]; congr 1; ring
    _ = ‖s * (∫ t : ℝ in x..y, (t : ℂ) ^ (-s - 1))‖ := by rw [hsub]
    _ ≤ ‖s‖ * (∫ t : ℝ in x..y, ‖(t : ℂ) ^ (-s - 1)‖) :=
          le_trans (norm_mul_le _ _)
            (mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm hxy)
              (norm_nonneg s))
    _ = (‖s‖ / s.re) * (x ^ (-s.re) - y ^ (-s.re)) := by
          rw [integral_norm_cpow_neg_sub hx hxy s hs]
          field_simp [ne_of_gt hs]

private lemma rpow_neg_sub_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) {σ : ℝ} (hσ : 0 < σ) :
    x ^ (-σ) - y ^ (-σ) ≤ σ * x ^ (-σ - 1) * (y - x) := by
  have hnot0 : (0 : ℝ) ∉ Set.uIcc x y := notMem_uIcc_of_pos hx hxy
  have hne : -σ - 1 ≠ (-1 : ℝ) := by linarith
  have hint := integral_rpow (r := -σ - 1) (a := x) (b := y) (Or.inr ⟨hne, hnot0⟩)
  have hmain : σ * (∫ t : ℝ in x..y, t ^ (-σ - 1)) = x ^ (-σ) - y ^ (-σ) := by
    rw [hint]
    have hD : -σ - 1 + 1 = -σ := by ring
    rw [hD]
    field_simp [ne_of_gt hσ]
    ring
  have hconst : (∫ t : ℝ in x..y, x ^ (-σ - 1)) = x ^ (-σ - 1) * (y - x) := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
    ring
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-σ - 1)) (Set.Icc x y) := by
    intro t ht
    exact (Real.continuousAt_rpow_const t (-σ - 1)
      (Or.inl (ne_of_gt (lt_of_lt_of_le hx ht.1)))).continuousWithinAt
  have hmono : (∫ t : ℝ in x..y, t ^ (-σ - 1)) ≤ ∫ t : ℝ in x..y, x ^ (-σ - 1) := by
    refine intervalIntegral.integral_mono_on hxy (hcont.intervalIntegrable_of_Icc hxy)
      intervalIntegrable_const ?_
    intro t ht
    exact Real.rpow_le_rpow_of_nonpos hx ht.1 (by linarith)
  calc
    x ^ (-σ) - y ^ (-σ) = σ * (∫ t : ℝ in x..y, t ^ (-σ - 1)) := hmain.symm
    _ ≤ σ * (∫ t : ℝ in x..y, x ^ (-σ - 1)) := mul_le_mul_of_nonneg_left hmono hσ.le
    _ = σ * x ^ (-σ - 1) * (y - x) := by rw [hconst]; ring

/-- Pointwise bound for the shift-difference terms, in the form adapted to telescoping. -/
lemma norm_shiftTerm_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {s : ℂ} (hs : 0 < s.re)
    (m : ℕ) :
    ‖shiftTerm a m s‖ ≤
      (‖s‖ / s.re) * ((((m : ℝ) + a) ^ (-s.re)) - ((((m + 1 : ℕ) : ℝ) + a) ^ (-s.re))) := by
  have hx : 0 < (m : ℝ) + a := by positivity
  have hxy : (m : ℝ) + a ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hy0 : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  have hyz : ((m + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) + a := by linarith
  have hmono : ((((m + 1 : ℕ) : ℝ) + a) ^ (-s.re)) ≤ ((((m + 1 : ℕ) : ℝ)) ^ (-s.re)) :=
    Real.rpow_le_rpow_of_nonpos hy0 hyz (by linarith)
  have h := norm_cpow_neg_sub_le hx hxy s hs
  have hrev : shiftTerm a m s = - ((((((m + 1 : ℕ) : ℝ)) : ℂ) ^ (-s)) -
      ((((m : ℝ) + a : ℝ) : ℂ) ^ (-s))) := by
    rw [shiftTerm]; ring
  rw [hrev, norm_neg]
  calc ‖(((((m + 1 : ℕ) : ℝ)) : ℂ) ^ (-s)) - ((((m : ℝ) + a : ℝ) : ℂ) ^ (-s))‖
      ≤ (‖s‖ / s.re) * ((((m : ℝ) + a) ^ (-s.re)) - ((((m + 1 : ℕ) : ℝ)) ^ (-s.re))) := h
    _ ≤ (‖s‖ / s.re) * ((((m : ℝ) + a) ^ (-s.re)) - ((((m + 1 : ℕ) : ℝ) + a) ^ (-s.re))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith

/-- Summability of the telescoping differences `(m+A)^{-σ} - (m+1+A)^{-σ}`. -/
lemma summable_rpow_shift_diff {A : ℝ} (hA : 0 < A) {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun m : ℕ => ((((m : ℝ) + A) ^ (-σ)) - ((((m + 1 : ℕ) : ℝ) + A) ^ (-σ)))) := by
  refine Summable.of_nonneg_of_le (f := fun m : ℕ => σ * ((((m : ℝ) + A) ^ (-σ - 1))))
    (fun m => sub_nonneg.mpr ?_) (fun m => ?_) ?_
  · have hx : 0 < (m : ℝ) + A := by positivity
    have hxy : (m : ℝ) + A ≤ ((m + 1 : ℕ) : ℝ) + A := by push_cast; linarith
    have h := Real.rpow_le_rpow_of_nonpos hx hxy (by linarith : -σ ≤ 0)
    simpa only [Nat.cast_add, Nat.cast_one] using h
  · have hx : 0 < (m : ℝ) + A := by positivity
    have hxy : (m : ℝ) + A ≤ ((m + 1 : ℕ) : ℝ) + A := by push_cast; linarith
    have h := rpow_neg_sub_le hx hxy hσ
    have hyx : (((m + 1 : ℕ) : ℝ) + A) - ((m : ℝ) + A) = 1 := by push_cast; ring
    rwa [hyx, mul_one] at h
  · have h1 : Summable (fun m : ℕ => 1 / |(m : ℝ) + A| ^ (σ + 1)) :=
      (Real.summable_one_div_nat_add_rpow A (σ + 1)).mpr (by linarith)
    refine (h1.mul_left σ).congr (fun m => ?_)
    have hx : 0 < (m : ℝ) + A := by positivity
    rw [abs_of_pos hx, one_div, ← Real.rpow_neg (le_of_lt hx), neg_add_rev, add_comm]
    ring

/-- Telescoping: `∑_m ((m+A)^{-σ} - (m+1+A)^{-σ}) = A^{-σ}` for `A > 0`, `σ > 0`. -/
lemma tsum_rpow_shift_sub {A : ℝ} (hA : 0 < A) {σ : ℝ} (hσ : 0 < σ) :
    (∑' m : ℕ, ((((m : ℝ) + A) ^ (-σ)) - ((((m + 1 : ℕ) : ℝ) + A) ^ (-σ)))) = A ^ (-σ) := by
  have hsumm := summable_rpow_shift_diff hA hσ
  have hpartial : ∀ M : ℕ,
      (∑ m ∈ Finset.range M, ((((m : ℝ) + A) ^ (-σ)) - ((((m + 1 : ℕ) : ℝ) + A) ^ (-σ)))) =
      A ^ (-σ) - ((((M : ℝ) + A) ^ (-σ))) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
  have htend : Tendsto (fun M : ℕ => ((((M : ℝ) + A) ^ (-σ)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ (-σ)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hσ
    have h2 : Tendsto (fun M : ℕ => ((M : ℝ) + A)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    exact h1.comp h2
  have hlim : Tendsto (fun M : ℕ =>
      (∑ m ∈ Finset.range M, ((((m : ℝ) + A) ^ (-σ)) - ((((m + 1 : ℕ) : ℝ) + A) ^ (-σ)))))
      atTop (𝓝 (A ^ (-σ))) := by
    simp only [hpartial]
    have hconst : Tendsto (fun _ : ℕ => A ^ (-σ)) atTop (𝓝 (A ^ (-σ))) := tendsto_const_nhds
    have hh := hconst.sub htend
    simpa using hh
  exact HasSum.tsum_eq (hsumm.hasSum_iff_tendsto_nat.mpr hlim)

/-- Summability of the norms of the shift-difference terms. -/
lemma summable_norm_shiftTerm {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {s : ℂ} (hs : 0 < s.re)
    (M : ℕ) :
    Summable (fun m : ℕ => ‖shiftTerm a (M + m) s‖) := by
  have hle : ∀ m : ℕ, ‖shiftTerm a (M + m) s‖ ≤
      (‖s‖ / s.re) * ((((m : ℝ) + ((M : ℝ) + a)) ^ (-s.re)) -
        ((((m + 1 : ℕ) : ℝ) + ((M : ℝ) + a)) ^ (-s.re))) := by
    intro m
    have h := norm_shiftTerm_le ha ha1 hs (M + m)
    have e1 : (((M + m : ℕ) : ℝ) + a) = (m : ℝ) + ((M : ℝ) + a) := by push_cast; ring
    have e2 : ((((M + m + 1 : ℕ) : ℝ) + a)) = ((m + 1 : ℕ) : ℝ) + ((M : ℝ) + a) := by
      push_cast; ring
    rw [e1, e2] at h
    exact h
  have hmaj : Summable (fun m : ℕ => (‖s‖ / s.re) *
      ((((m : ℝ) + ((M : ℝ) + a)) ^ (-s.re)) - ((((m + 1 : ℕ) : ℝ) + ((M : ℝ) + a)) ^ (-s.re)))) :=
    (summable_rpow_shift_diff (A := (M : ℝ) + a) (by positivity) hs).mul_left _
  exact Summable.of_norm_bounded hmaj (fun m => by simpa using hle m)

/-- Tail bound: `‖∑_{m≥M} shiftTerm a m s‖ ≤ (‖s‖/σ) (M+a)^{-σ}`. -/
lemma norm_tsum_shiftTerm_tail_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {s : ℂ} (hs : 0 < s.re)
    (M : ℕ) :
    ‖∑' m : ℕ, shiftTerm a (M + m) s‖ ≤ (‖s‖ / s.re) * ((((M : ℝ) + a) ^ (-s.re))) := by
  have hsum := summable_norm_shiftTerm ha ha1 hs M
  have hle : ∀ m : ℕ, ‖shiftTerm a (M + m) s‖ ≤
      (‖s‖ / s.re) * ((((m : ℝ) + ((M : ℝ) + a)) ^ (-s.re)) -
        ((((m + 1 : ℕ) : ℝ) + ((M : ℝ) + a)) ^ (-s.re))) := by
    intro m
    have h := norm_shiftTerm_le ha ha1 hs (M + m)
    have e1 : (((M + m : ℕ) : ℝ) + a) = (m : ℝ) + ((M : ℝ) + a) := by push_cast; ring
    have e2 : ((((M + m + 1 : ℕ) : ℝ) + a)) = ((m + 1 : ℕ) : ℝ) + ((M : ℝ) + a) := by
      push_cast; ring
    rw [e1, e2] at h
    exact h
  have hmaj : Summable (fun m : ℕ => (‖s‖ / s.re) *
      ((((m : ℝ) + ((M : ℝ) + a)) ^ (-s.re)) - ((((m + 1 : ℕ) : ℝ) + ((M : ℝ) + a)) ^ (-s.re)))) :=
    (summable_rpow_shift_diff (A := (M : ℝ) + a) (by positivity) hs).mul_left _
  calc
    ‖∑' m : ℕ, shiftTerm a (M + m) s‖ ≤ ∑' m : ℕ, ‖shiftTerm a (M + m) s‖ :=
        norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' m : ℕ, (‖s‖ / s.re) * ((((m : ℝ) + ((M : ℝ) + a)) ^ (-s.re)) -
          ((((m + 1 : ℕ) : ℝ) + ((M : ℝ) + a)) ^ (-s.re))) :=
        Summable.tsum_le_tsum hle hsum hmaj
    _ = (‖s‖ / s.re) * (∑' m : ℕ, ((((m : ℝ) + ((M : ℝ) + a)) ^ (-s.re)) -
          ((((m + 1 : ℕ) : ℝ) + ((M : ℝ) + a)) ^ (-s.re)))) := tsum_mul_left
    _ = (‖s‖ / s.re) * ((((M : ℝ) + a) ^ (-s.re))) := by
        rw [tsum_rpow_shift_sub (A := (M : ℝ) + a) (by positivity) hs]

/-! ## Analyticity -/

private lemma differentiableOn_shiftTerm {a : ℝ} (ha : 0 < a) (U : Set ℂ) (m : ℕ) :
    DifferentiableOn ℂ (fun s : ℂ => shiftTerm a m s) U := by
  have hx : ((((m : ℝ) + a : ℝ)) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (m : ℝ) + a := by positivity
    exact_mod_cast (ne_of_gt this)
  have hy : ((((m + 1 : ℕ) : ℝ)) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    exact_mod_cast (ne_of_gt this)
  intro s _
  have h1 : DifferentiableAt ℂ (fun t : ℂ => ((((m : ℝ) + a : ℝ)) : ℂ) ^ (-t)) s :=
    (differentiableAt_id.neg).const_cpow (Or.inl hx)
  have h2 : DifferentiableAt ℂ (fun t : ℂ => ((((m + 1 : ℕ) : ℝ)) : ℂ) ^ (-t)) s :=
    (differentiableAt_id.neg).const_cpow (Or.inl hy)
  have hsub : DifferentiableAt ℂ
      ((fun t : ℂ => ((((m : ℝ) + a : ℝ)) : ℂ) ^ (-t)) -
        (fun t : ℂ => ((((m + 1 : ℕ) : ℝ)) : ℂ) ^ (-t))) s := h1.sub h2
  exact (hsub.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun y => by dsimp [shiftTerm]))).differentiableWithinAt

private lemma norm_shiftTerm_le_on {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {ε R : ℝ} (hε : 0 < ε) {w : ℂ} (hεw : ε < w.re) (hR : ‖w‖ < R) (m : ℕ) :
    ‖shiftTerm a m w‖ ≤ (R * max 1 (a ^ (ε - R))) * ((((m : ℝ) + a) ^ (-(ε + 1)))) := by
  have hx : 0 < (m : ℝ) + a := by positivity
  have hxy : (m : ℝ) + a ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hσ : 0 < w.re := lt_trans hε hεw
  have hσR : w.re < R := lt_of_le_of_lt (Complex.re_le_norm w) hR
  have hb := norm_shiftTerm_le ha ha1 hσ m
  have hdiff : (((m : ℝ) + a) ^ (-w.re)) - ((((m + 1 : ℕ) : ℝ) + a) ^ (-w.re)) ≤
      w.re * (((m : ℝ) + a) ^ (-w.re - 1)) := by
    have hxz : (m : ℝ) + a ≤ ((m + 1 : ℕ) : ℝ) + a := by push_cast; linarith
    have hd := rpow_neg_sub_le hx hxz hσ
    have hyx : (((m + 1 : ℕ) : ℝ) + a) - ((m : ℝ) + a) = 1 := by push_cast; ring
    calc (((m : ℝ) + a) ^ (-w.re)) - ((((m + 1 : ℕ) : ℝ) + a) ^ (-w.re))
        ≤ w.re * (((m : ℝ) + a) ^ (-w.re - 1)) * ((((m + 1 : ℕ) : ℝ) + a) - ((m : ℝ) + a)) := hd
      _ = w.re * (((m : ℝ) + a) ^ (-w.re - 1)) := by rw [hyx, mul_one]
  have hsplit : (((m : ℝ) + a) ^ (-w.re - 1)) =
      (((m : ℝ) + a) ^ (-(ε + 1))) * (((m : ℝ) + a) ^ (ε - w.re)) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hpow : (((m : ℝ) + a) ^ (ε - w.re)) ≤ max 1 (a ^ (ε - R)) := by
    by_cases h1 : (1 : ℝ) ≤ (m : ℝ) + a
    · have hexp : ε - w.re ≤ 0 := by linarith
      have hle1 : (((m : ℝ) + a) ^ (ε - w.re)) ≤ 1 := by
        have hh := Real.rpow_le_rpow_of_exponent_le h1 hexp
        rwa [Real.rpow_zero] at hh
      exact le_trans hle1 (le_max_left _ _)
    · have h1' : (m : ℝ) + a < 1 := lt_of_not_ge h1
      have h2 : a ≤ (m : ℝ) + a := by linarith [show (0:ℝ) ≤ (m:ℝ) by positivity]
      have hexp : ε - R ≤ ε - w.re := by linarith
      have hxs : (((m : ℝ) + a) ^ (ε - w.re)) ≤ (((m : ℝ) + a) ^ (ε - R)) := by
        have hsp : ε - w.re = (ε - R) + (R - w.re) := by ring
        calc (((m : ℝ) + a) ^ (ε - w.re))
            = (((m : ℝ) + a) ^ (ε - R)) * (((m : ℝ) + a) ^ (R - w.re)) := by
              rw [hsp, Real.rpow_add hx]
          _ ≤ (((m : ℝ) + a) ^ (ε - R)) * 1 :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_one (le_of_lt hx) (le_of_lt h1') (by linarith))
                (Real.rpow_nonneg (le_of_lt hx) _)
          _ = (((m : ℝ) + a) ^ (ε - R)) := mul_one _
      have hxs2 : (((m : ℝ) + a) ^ (ε - R)) ≤ a ^ (ε - R) :=
        Real.rpow_le_rpow_of_nonpos ha h2 (by linarith)
      exact le_trans hxs (le_trans hxs2 (le_max_right _ _))
  calc ‖shiftTerm a m w‖
      ≤ (‖w‖ / w.re) * ((((m : ℝ) + a) ^ (-w.re)) - ((((m + 1 : ℕ) : ℝ) + a) ^ (-w.re))) := hb
    _ ≤ (‖w‖ / w.re) * (w.re * (((m : ℝ) + a) ^ (-w.re - 1))) :=
          mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ = ‖w‖ * (((m : ℝ) + a) ^ (-w.re - 1)) := by field_simp [ne_of_gt hσ]
    _ ≤ ‖w‖ * ((((m : ℝ) + a) ^ (-(ε + 1))) * max 1 (a ^ (ε - R))) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg w)
          rw [hsplit]
          exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (le_of_lt hx) _)
    _ ≤ R * ((((m : ℝ) + a) ^ (-(ε + 1))) * max 1 (a ^ (ε - R))) :=
          mul_le_mul_of_nonneg_right (le_of_lt hR)
            (mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _)
              (le_trans zero_le_one (le_max_left _ _)))
    _ = (R * max 1 (a ^ (ε - R))) * ((((m : ℝ) + a) ^ (-(ε + 1)))) := by ring

private lemma summable_shiftTerm_majorant {a : ℝ} (ha : 0 < a) {ε R : ℝ} (hε : 0 < ε) :
    Summable (fun m : ℕ => (R * max 1 (a ^ (ε - R))) * ((((m : ℝ) + a) ^ (-(ε + 1))))) := by
  have h1 : Summable (fun m : ℕ => 1 / |(m : ℝ) + a| ^ (ε + 1)) :=
    (Real.summable_one_div_nat_add_rpow a (ε + 1)).mpr (by linarith)
  have hsum : Summable (fun m : ℕ => (((m : ℝ) + a) ^ (-(ε + 1)))) := by
    refine h1.congr (fun m => ?_)
    have hx : 0 < (m : ℝ) + a := by positivity
    rw [abs_of_pos hx, one_div, ← Real.rpow_neg (le_of_lt hx)]
  exact hsum.mul_left _

private lemma differentiableOn_shiftTerm_tsum {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    DifferentiableOn ℂ (fun s : ℂ => ∑' m : ℕ, shiftTerm a m s)
      {z : ℂ | 0 < z.re ∧ z ≠ 1} := by
  intro z0 hz0
  obtain ⟨hz0pos, _⟩ := hz0
  set ε : ℝ := z0.re / 2 with hεdef
  set R : ℝ := ‖z0‖ + 1 with hRdef
  set U : Set ℂ := {w : ℂ | ε < w.re ∧ ‖w‖ < R} with hUdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hz0U : z0 ∈ U := by
    rw [hUdef]
    exact ⟨by rw [hεdef]; linarith, by rw [hRdef]; linarith [norm_nonneg z0]⟩
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
  have hdiff : DifferentiableOn ℂ (fun s : ℂ => ∑' m : ℕ, shiftTerm a m s) U :=
    Complex.differentiableOn_tsum_of_summable_norm
      (F := fun m (s : ℂ) => shiftTerm a m s)
      (u := fun m : ℕ => (R * max 1 (a ^ (ε - R))) * ((((m : ℝ) + a) ^ (-(ε + 1)))))
      (summable_shiftTerm_majorant ha hε) (fun m => differentiableOn_shiftTerm ha U m) hUopen
      (fun m w hw => norm_shiftTerm_le_on ha ha1 hε hw.1 hw.2 m)
  exact (hdiff.differentiableAt (hUopen.mem_nhds hz0U)).differentiableWithinAt

/-! ## The identity -/

private lemma hasSum_shiftTerm_of_one_lt_re {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {z : ℂ}
    (hz : 1 < z.re) :
    HasSum (fun m : ℕ => shiftTerm a m z)
      (HurwitzZeta.hurwitzZeta (a : UnitAddCircle) z - riemannZeta z) := by
  have hA : HasSum (fun n : ℕ => ((((n : ℝ) + a : ℝ)) : ℂ) ^ (-z))
      (HurwitzZeta.hurwitzZeta (a : UnitAddCircle) z) := by
    have h := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re (a := a) ⟨ha.le, ha1⟩ (s := z) hz
    refine h.congr_fun (fun n => ?_)
    rw [Complex.cpow_neg, one_div]
    push_cast
    ring_nf
  have hzsumm : Summable (fun n : ℕ => 1 / ((n : ℂ)) ^ z) :=
    Complex.summable_one_div_nat_cpow.mpr hz
  have hznz : z ≠ 0 := by
    intro h
    have : z.re = 0 := by rw [h]; simp
    linarith
  have htsum : (∑' n : ℕ, 1 / ((n : ℂ)) ^ z) = riemannZeta z :=
    (zeta_eq_tsum_one_div_nat_cpow hz).symm
  have hsum1 : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℂ)) ^ z) :=
    (summable_nat_add_iff 1).mpr hzsumm
  have htsum1 : (∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ)) ^ z) = riemannZeta z := by
    have hsplit := Summable.sum_add_tsum_nat_add (k := 1)
      (f := fun n : ℕ => 1 / ((n : ℂ)) ^ z) hzsumm
    rw [htsum] at hsplit
    have h0 : (∑ i ∈ Finset.range 1, 1 / ((i : ℂ)) ^ z) = 0 := by
      rw [Finset.sum_range_one]
      simp only [Nat.cast_zero]
      rw [Complex.zero_cpow hznz]
      simp
    rw [h0, zero_add] at hsplit
    exact hsplit
  have hB1 : HasSum (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℂ)) ^ z) (riemannZeta z) := by
    rw [← htsum1]
    exact hsum1.hasSum
  have hB : HasSum (fun m : ℕ => ((((m + 1 : ℕ) : ℝ)) : ℂ) ^ (-z)) (riemannZeta z) := by
    refine hB1.congr_fun (fun n => ?_)
    rw [Complex.cpow_neg, one_div]
    push_cast
    ring_nf
  simpa only [shiftTerm] using hA.sub hB

/-- **The shift-difference decomposition of the Hurwitz zeta function.** -/
theorem hurwitzZeta_sub_riemannZeta_eq_tsum {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s - riemannZeta s =
      ∑' m : ℕ, shiftTerm a m s := by
  set D : Set ℂ := {z : ℂ | 0 < z.re ∧ z ≠ 1} with hD
  have hDopen : IsOpen D :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  have hL : AnalyticOnNhd ℂ
      (fun z : ℂ => HurwitzZeta.hurwitzZeta (a : UnitAddCircle) z - riemannZeta z) D := by
    have hdiff : Differentiable ℂ (fun z : ℂ =>
        HurwitzZeta.hurwitzZeta (a : UnitAddCircle) z -
          HurwitzZeta.hurwitzZeta (0 : UnitAddCircle) z) :=
      HurwitzZeta.differentiable_hurwitzZeta_sub_hurwitzZeta _ _
    have hEq : (fun z : ℂ => HurwitzZeta.hurwitzZeta (a : UnitAddCircle) z - riemannZeta z) =
        (fun z : ℂ => HurwitzZeta.hurwitzZeta (a : UnitAddCircle) z -
          HurwitzZeta.hurwitzZeta (0 : UnitAddCircle) z) := by
      funext z
      simp only [HurwitzZeta.hurwitzZeta_zero]
    rw [hEq]
    exact hdiff.differentiableOn.analyticOnNhd hDopen
  have hR : AnalyticOnNhd ℂ (fun z : ℂ => ∑' m : ℕ, shiftTerm a m z) D :=
    (differentiableOn_shiftTerm_tsum ha ha1).analyticOnNhd hDopen
  have hpre : IsPreconnected D := hD ▸
    Commons.NumberTheory.Zeta.isPreconnected_re_gt_sdiff (θ := 0) (by norm_num)
  have hz0 : (2 : ℂ) ∈ D := ⟨by norm_num, by norm_num⟩
  have hev : (fun z : ℂ => HurwitzZeta.hurwitzZeta (a : UnitAddCircle) z - riemannZeta z)
      =ᶠ[𝓝 (2 : ℂ)] (fun z : ℂ => ∑' m : ℕ, shiftTerm a m z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact (hasSum_shiftTerm_of_one_lt_re ha ha1 hz).tsum_eq.symm
  exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hL hR hpre hz0 hev) ⟨hs0, hs1⟩

end

end Work.BMF
