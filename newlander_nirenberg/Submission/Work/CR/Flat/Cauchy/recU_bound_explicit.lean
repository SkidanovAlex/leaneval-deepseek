/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The explicit `C^{0,α}` bound for the explicit solution `recU`

This module proves `Work.CR.Flat.Cauchy.recU_bound_explicit`: given the stage bounds
`‖recF f m k z‖ ≤ K ^ m * S` and `‖recF f m k x - recF f m k y‖ ≤ K ^ m * S * ‖x - y‖ ^ α`
on the tracked region `trackSet` (for every stage `m ≤ n`), the explicit solution

  `recU f = ∑ j, dbarTransform trRho j (cutF j · recF f j j)`

satisfies the uniform bound `‖recU f z‖ ≤ (2 * trRho * n * K ^ n * (2 + L) + 1) * S` and
the Hölder bound with the same constant on the polydisc of radius `eqRad`, where `L` is a
Lipschitz constant for the cutoff `openCut`.

The mathematical content is the fibre estimate for `cutF j * F` with the *sharp* constant
`2 + L`: `F` is `A`-bounded and `A`-Hölder on `trackSet`, and the transverse coordinates
(the coordinates `≠ j`) are below `trTrack`; then

  `‖cutF j a * F a - cutF j a' * F a'‖ ≤ (2 + L) * A * ‖a - a'‖ ^ α`.

Indeed `cutF j u = 0` as soon as `‖u j‖ ≥ cutOut < trTrack`, so on the fibres of
`dbarTransform_basic` the second factor is always controlled; the two regimes
`‖a - a'‖ ≤ 1` (where `‖a - a'‖ ≤ ‖a - a'‖ ^ α`) and `1 ≤ ‖a - a'‖` (where
`1 ≤ ‖a - a'‖ ^ α`, so the crude bound `2 A` suffices) give the constant `2 + L`.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.openSolRec
import Submission.Work.CR.Flat.Cauchy.dbarTransform_basic

noncomputable section

open scoped NNReal ENNReal ContDiff
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

lemma fibre_holder_two_add {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {j : Fin n} {L : ℝ} (hL0 : 0 ≤ L)
    (hLip : ∀ ζ ζ' : ℂ, ‖openCut ζ - openCut ζ'‖ ≤ L * ‖ζ - ζ'‖)
    {F : (Fin n → ℂ) → ℂ} {A : ℝ} (hA0 : 0 ≤ A)
    (hF : ∀ z : Fin n → ℂ, z ∈ trackSet → ‖F z‖ ≤ A)
    (hFh : ∀ x y : Fin n → ℂ, x ∈ trackSet → y ∈ trackSet →
      ‖F x - F y‖ ≤ A * ‖x - y‖ ^ α) :
    ∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → ‖a l‖ < trTrack) →
      (∀ l, l ≠ j → ‖a' l‖ < trTrack) →
      ‖cutF j a * F a - cutF j a' * F a'‖ ≤ (2 + L) * A * ‖a - a'‖ ^ α := by
  classical
  have hmemT : ∀ u : Fin n → ℂ, (∀ l, l ≠ j → ‖u l‖ < trTrack) → ‖u j‖ < trTrack →
      u ∈ trackSet := fun u hu huj l => by
    by_cases hl : l = j
    · subst hl; exact huj
    · exact hu l hl
  have hz_of_not : ∀ u : Fin n → ℂ, (∀ l, l ≠ j → ‖u l‖ < trTrack) → u ∉ trackSet →
      cutF j u = 0 := by
    intro u hu hnu
    refine cutF_eq_zero (le_trans (le_of_lt cutOut_lt_trTrack) ?_)
    by_contra hlt
    push Not at hlt
    exact hnu (hmemT u hu hlt)
  intro a a' ha ha'
  have hc_sub : ‖cutF j a - cutF j a'‖ ≤ 1 := by
    have hsplit : ‖cutF j a - cutF j a'‖
        = |openCutReal (Complex.normSq (a j)) - openCutReal (Complex.normSq (a' j))| := by
      rw [show cutF j a = ((openCutReal (Complex.normSq (a j)) : ℝ) : ℂ) from
            openCut_eq_openCutReal _,
          show cutF j a' = ((openCutReal (Complex.normSq (a' j)) : ℝ) : ℂ) from
            openCut_eq_openCutReal _,
          ← Complex.ofReal_sub]
      exact RCLike.norm_ofReal _
    rw [hsplit, abs_le]
    constructor
    · have h1 := openCutReal_nonneg (Complex.normSq (a j))
      have h4 := openCutReal_le_one (Complex.normSq (a' j))
      linarith
    · have h2 := openCutReal_le_one (Complex.normSq (a j))
      have h3 := openCutReal_nonneg (Complex.normSq (a' j))
      linarith
  have hmin : ‖cutF j a - cutF j a'‖ ≤ min 1 (L * ‖a - a'‖) :=
    le_min hc_sub (by simpa using norm_cutF_sub_le j hL0 hLip a a')
  have hd0 : 0 ≤ ‖a - a'‖ := norm_nonneg _
  have hdα0 : 0 ≤ ‖a - a'‖ ^ α := Real.rpow_nonneg hd0 α
  have hc1 : ‖cutF j a‖ ≤ 1 := norm_cutF_le_one j a
  have hcmin0 : 0 ≤ min 1 (L * ‖a - a'‖) := le_min zero_le_one (mul_nonneg hL0 hd0)
  have key : ‖cutF j a * F a - cutF j a' * F a'‖
      ≤ A * ‖a - a'‖ ^ α + min 1 (L * ‖a - a'‖) * A := by
    by_cases haT : a ∈ trackSet
    · by_cases ha'T : a' ∈ trackSet
      · have hsplit : cutF j a * F a - cutF j a' * F a'
            = cutF j a * (F a - F a') + (cutF j a - cutF j a') * F a' := by ring
        rw [hsplit]
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul, norm_mul]
        have h1 : ‖cutF j a‖ * ‖F a - F a'‖ ≤ A * ‖a - a'‖ ^ α := by
          calc ‖cutF j a‖ * ‖F a - F a'‖ ≤ 1 * (A * ‖a - a'‖ ^ α) :=
                mul_le_mul hc1 (hFh a a' haT ha'T) (norm_nonneg _) zero_le_one
            _ = A * ‖a - a'‖ ^ α := one_mul _
        have h2 : ‖cutF j a - cutF j a'‖ * ‖F a'‖ ≤ min 1 (L * ‖a - a'‖) * A :=
          mul_le_mul hmin (hF a' ha'T) (norm_nonneg _) hcmin0
        linarith
      · have hz : cutF j a' = 0 := hz_of_not a' ha' ha'T
        have hceq : ‖cutF j a‖ ≤ min 1 (L * ‖a - a'‖) := by
          have h := hmin
          rwa [hz, sub_zero] at h
        have hgoal : ‖cutF j a * F a - cutF j a' * F a'‖ = ‖cutF j a * F a‖ := by
          rw [hz, zero_mul, sub_zero]
        rw [hgoal, norm_mul]
        have h2 : ‖cutF j a‖ * ‖F a‖ ≤ min 1 (L * ‖a - a'‖) * A :=
          mul_le_mul hceq (hF a haT) (norm_nonneg _) hcmin0
        linarith [h2, mul_nonneg hA0 hdα0]
    · have hz : cutF j a = 0 := hz_of_not a ha haT
      by_cases ha'T : a' ∈ trackSet
      · have hceq : ‖cutF j a'‖ ≤ min 1 (L * ‖a - a'‖) := by
          have h := hmin
          rw [hz, zero_sub, norm_neg] at h
          exact h
        have hgoal : ‖cutF j a * F a - cutF j a' * F a'‖ = ‖cutF j a' * F a'‖ := by
          rw [hz, zero_mul, zero_sub, norm_neg]
        rw [hgoal, norm_mul]
        have h2 : ‖cutF j a'‖ * ‖F a'‖ ≤ min 1 (L * ‖a - a'‖) * A :=
          mul_le_mul hceq (hF a' ha'T) (norm_nonneg _) hcmin0
        linarith [h2, mul_nonneg hA0 hdα0]
      · have hz' : cutF j a' = 0 := hz_of_not a' ha' ha'T
        rw [hz, hz', zero_mul, zero_mul, sub_zero, norm_zero]
        linarith [mul_nonneg hA0 hdα0, mul_nonneg hcmin0 hA0]
  rcases le_or_gt ‖a - a'‖ 1 with hdle | hdgt
  · have hdα : ‖a - a'‖ ≤ ‖a - a'‖ ^ α := by
      rcases eq_or_lt_of_le hd0 with h | h
      · rw [← h, Real.zero_rpow (ne_of_gt hα)]
      · have h4 := Real.rpow_le_rpow_of_exponent_ge h hdle hα1.le
        rwa [Real.rpow_one] at h4
    have h2 : min 1 (L * ‖a - a'‖) * A ≤ (L * ‖a - a'‖ ^ α) * A :=
      mul_le_mul (le_trans (min_le_right _ _) (mul_le_mul_of_nonneg_left hdα hL0)) le_rfl
        hA0 (mul_nonneg hL0 hdα0)
    calc ‖cutF j a * F a - cutF j a' * F a'‖
        ≤ A * ‖a - a'‖ ^ α + min 1 (L * ‖a - a'‖) * A := key
      _ ≤ A * ‖a - a'‖ ^ α + (L * ‖a - a'‖ ^ α) * A := add_le_add le_rfl h2
      _ ≤ (2 + L) * A * ‖a - a'‖ ^ α := by nlinarith [hA0, hdα0]
  · have hdα1 : 1 ≤ ‖a - a'‖ ^ α := Real.one_le_rpow hdgt.le hα.le
    have h2 : min 1 (L * ‖a - a'‖) * A ≤ A * ‖a - a'‖ ^ α := by
      calc min 1 (L * ‖a - a'‖) * A ≤ 1 * A :=
            mul_le_mul (min_le_left _ _) le_rfl hA0 zero_le_one
        _ = A := one_mul A
        _ = A * 1 := (mul_one A).symm
        _ ≤ A * ‖a - a'‖ ^ α := mul_le_mul_of_nonneg_left hdα1 hA0
    calc ‖cutF j a * F a - cutF j a' * F a'‖
        ≤ A * ‖a - a'‖ ^ α + min 1 (L * ‖a - a'‖) * A := key
      _ ≤ A * ‖a - a'‖ ^ α + A * ‖a - a'‖ ^ α := add_le_add le_rfl h2
      _ = 2 * (A * ‖a - a'‖ ^ α) := by ring
      _ ≤ (2 + L) * A * ‖a - a'‖ ^ α := by
          have hLAd : (0 : ℝ) ≤ L * A * ‖a - a'‖ ^ α := by positivity
          nlinarith [hLAd]

/-- **The explicit bound for `recU`.**  From the stage bounds on `trackSet` for every stage
`m ≤ n`, the explicit solution `recU f` of the `∂̄`-problem on the polydisc satisfies the
uniform bound and the `C^{0,α}` bound with the explicit constant
`2 * trRho * n * K ^ n * (2 + L) + 1` on the polydisc of radius `eqRad`. -/
theorem recU_bound_explicit {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {f : Fin n → (Fin n → ℂ) → ℂ} {S K : ℝ} (hK1 : 1 ≤ K) {L : ℝ} (hL0 : 0 ≤ L)
    (hLip : ∀ ζ ζ' : ℂ, ‖openCut ζ - openCut ζ'‖ ≤ L * ‖ζ - ζ'‖)
    (hS0 : 0 ≤ S)
    (hcont : ∀ m, m ≤ n → ∀ k : Fin n, Continuous (recF f m k))
    (hstage : ∀ m, m ≤ n → ∀ k : Fin n,
      (∀ z, z ∈ trackSet → ‖recF f m k z‖ ≤ K ^ m * S) ∧
      (∀ x y, x ∈ trackSet → y ∈ trackSet →
        ‖recF f m k x - recF f m k y‖ ≤ K ^ m * S * ‖x - y‖ ^ α)) :
    (∀ z : Fin n → ℂ, (∀ l, ‖z l‖ < eqRad) →
      ‖recU f z‖ ≤ (2 * trRho * (n : ℝ) * K ^ n * (2 + L) + 1) * S) ∧
    (∀ x y : Fin n → ℂ, (∀ l, ‖x l‖ < eqRad) → (∀ l, ‖y l‖ < eqRad) →
      ‖recU f x - recU f y‖
        ≤ (2 * trRho * (n : ℝ) * K ^ n * (2 + L) + 1) * S * ‖x - y‖ ^ α) := by
  have hK0 : 0 ≤ K := le_trans zero_le_one hK1
  have htrRho : 0 ≤ trRho := le_of_lt trRho_pos
  have hcutOut0 : 0 ≤ cutOut := le_of_lt cutOut_pos
  have h2L0 : (0 : ℝ) ≤ 2 + L := by linarith
  have hX00 : 0 ≤ 2 * trRho * (n : ℝ) * K ^ n := by positivity
  have hXL : 0 ≤ 2 * trRho * (n : ℝ) * K ^ n * L := mul_nonneg hX00 hL0
  have hX2L : 0 ≤ 2 * trRho * (n : ℝ) * K ^ n * (2 + L) := mul_nonneg hX00 h2L0
  -- the arithmetic for the uniform bound
  have harith1 : (n : ℝ) * (2 * trRho * (K ^ n * S))
      ≤ (2 * trRho * (n : ℝ) * K ^ n * (2 + L) + 1) * S := by
    rw [show (n : ℝ) * (2 * trRho * (K ^ n * S))
        = (2 * trRho * (n : ℝ) * K ^ n) * S by ring]
    refine mul_le_mul_of_nonneg_right ?_ hS0
    nlinarith [hX00, hXL]
  -- the arithmetic for the Hölder bound
  have harith2 : ∀ {r : ℝ}, 0 ≤ r →
      (n : ℝ) * (2 * trRho * ((2 + L) * (K ^ n * S)) * r)
        ≤ (2 * trRho * (n : ℝ) * K ^ n * (2 + L) + 1) * S * r := by
    intro r hr
    rw [show (n : ℝ) * (2 * trRho * ((2 + L) * (K ^ n * S)) * r)
        = (2 * trRho * (n : ℝ) * K ^ n * (2 + L)) * S * r by ring]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hS0) hr
    linarith [hX2L]
  constructor
  · -- the uniform bound
    intro z hz
    have hzt : z ∈ trackSet := trackSet_of_solveSet hz
    have hterm : ∀ j : Fin n,
        ‖dbarTransform trRho j (fun y => cutF j y * recF f (j : ℕ) j y) z‖
          ≤ 2 * trRho * (K ^ n * S) := by
      intro j
      have hm : (j : ℕ) ≤ n := le_of_lt j.isLt
      obtain ⟨hb1, _⟩ := hstage (j : ℕ) hm j
      have hA0 : 0 ≤ K ^ (j : ℕ) * S := mul_nonneg (pow_nonneg hK0 _) hS0
      have hcontg : Continuous (fun y => cutF j y * recF f (j : ℕ) j y) :=
        (contDiff_cutF_of_le j 1).continuous.mul (hcont (j : ℕ) hm j)
      have hsupp : ∀ y : Fin n → ℂ, cutOut ≤ ‖y j‖ →
          cutF j y * recF f (j : ℕ) j y = 0 :=
        fun y hy => by rw [cutF_eq_zero hy, zero_mul]
      have hfib : ∀ y : Fin n → ℂ, (∀ l, l ≠ j → y l = z l) → ‖y j‖ ≤ cutOut →
          ‖cutF j y * recF f (j : ℕ) j y‖ ≤ K ^ (j : ℕ) * S := by
        intro y hyl hyj
        have hyt : y ∈ trackSet :=
          trackSet_update hzt hyl (lt_of_le_of_lt hyj cutOut_lt_trTrack)
        calc ‖cutF j y * recF f (j : ℕ) j y‖
            = ‖cutF j y‖ * ‖recF f (j : ℕ) j y‖ := norm_mul _ _
          _ ≤ 1 * (K ^ (j : ℕ) * S) :=
              mul_le_mul (norm_cutF_le_one j y) (hb1 y hyt) (norm_nonneg _) zero_le_one
          _ = K ^ (j : ℕ) * S := one_mul _
      calc ‖dbarTransform trRho j (fun y => cutF j y * recF f (j : ℕ) j y) z‖
          ≤ 2 * trRho * (K ^ (j : ℕ) * S) :=
            (dbarTransform_basic (ρ := trRho) (b := cutOut) trRho_pos hcutOut0).1
              hcontg hsupp (K ^ (j : ℕ) * S) z hfib
        _ ≤ 2 * trRho * (K ^ n * S) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK1 hm) hS0)
              (by linarith)
    rw [show recU f z = ∑ j : Fin n,
        dbarTransform trRho j (fun y => cutF j y * recF f (j : ℕ) j y) z from rfl]
    calc ‖∑ j : Fin n, dbarTransform trRho j (fun y => cutF j y * recF f (j : ℕ) j y) z‖
        ≤ ∑ j : Fin n, ‖dbarTransform trRho j
            (fun y => cutF j y * recF f (j : ℕ) j y) z‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin n, 2 * trRho * (K ^ n * S) := Finset.sum_le_sum (fun j _ => hterm j)
      _ = (n : ℝ) * (2 * trRho * (K ^ n * S)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ (2 * trRho * (n : ℝ) * K ^ n * (2 + L) + 1) * S := harith1
  · -- the Hölder bound
    intro x y hx hy
    have hxt : x ∈ trackSet := trackSet_of_solveSet hx
    have hyt : y ∈ trackSet := trackSet_of_solveSet hy
    have hterm : ∀ j : Fin n,
        ‖dbarTransform trRho j (fun y' => cutF j y' * recF f (j : ℕ) j y') x
          - dbarTransform trRho j (fun y' => cutF j y' * recF f (j : ℕ) j y') y‖
          ≤ 2 * trRho * ((2 + L) * (K ^ n * S)) * ‖x - y‖ ^ α := by
      intro j
      have hm : (j : ℕ) ≤ n := le_of_lt j.isLt
      obtain ⟨hb1, hb2⟩ := hstage (j : ℕ) hm j
      have hA0 : 0 ≤ K ^ (j : ℕ) * S := mul_nonneg (pow_nonneg hK0 _) hS0
      have hcontg : Continuous (fun y' => cutF j y' * recF f (j : ℕ) j y') :=
        (contDiff_cutF_of_le j 1).continuous.mul (hcont (j : ℕ) hm j)
      have hsupp : ∀ y' : Fin n → ℂ, cutOut ≤ ‖y' j‖ →
          cutF j y' * recF f (j : ℕ) j y' = 0 :=
        fun y' hy' => by rw [cutF_eq_zero hy', zero_mul]
      have hfib : ∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → a l = x l) →
          (∀ l, l ≠ j → a' l = y l) →
          ‖cutF j a * recF f (j : ℕ) j a - cutF j a' * recF f (j : ℕ) j a'‖
            ≤ ((2 + L) * (K ^ (j : ℕ) * S)) * ‖a - a'‖ ^ α := by
        intro a a' hal ha'l
        exact fibre_holder_two_add hα hα1 hL0 hLip hA0 hb1 hb2 a a'
          (fun l hl => by rw [hal l hl]; exact lt_trans (hx l) eqRad_lt_trTrack)
          (fun l hl => by rw [ha'l l hl]; exact lt_trans (hy l) eqRad_lt_trTrack)
      have hb := (dbarTransform_basic (ρ := trRho) (b := cutOut) trRho_pos hcutOut0).2.1
        hcontg hsupp α ((2 + L) * (K ^ (j : ℕ) * S)) x y hfib
      refine le_trans hb ?_
      have hmono : (2 + L) * (K ^ (j : ℕ) * S) ≤ (2 + L) * (K ^ n * S) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK1 hm) hS0) h2L0
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmono (by linarith : (0 : ℝ) ≤ 2 * trRho))
        (Real.rpow_nonneg (norm_nonneg _) α)
    rw [show recU f x = ∑ j : Fin n,
          dbarTransform trRho j (fun y' => cutF j y' * recF f (j : ℕ) j y') x from rfl,
        show recU f y = ∑ j : Fin n,
          dbarTransform trRho j (fun y' => cutF j y' * recF f (j : ℕ) j y') y from rfl,
        ← Finset.sum_sub_distrib]
    calc ‖∑ j : Fin n, (dbarTransform trRho j
            (fun y' => cutF j y' * recF f (j : ℕ) j y') x
          - dbarTransform trRho j (fun y' => cutF j y' * recF f (j : ℕ) j y') y)‖
        ≤ ∑ j : Fin n, ‖dbarTransform trRho j
              (fun y' => cutF j y' * recF f (j : ℕ) j y') x
            - dbarTransform trRho j (fun y' => cutF j y' * recF f (j : ℕ) j y') y‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _j : Fin n, 2 * trRho * ((2 + L) * (K ^ n * S)) * ‖x - y‖ ^ α :=
          Finset.sum_le_sum (fun j _ => hterm j)
      _ = (n : ℝ) * (2 * trRho * ((2 + L) * (K ^ n * S)) * ‖x - y‖ ^ α) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ (2 * trRho * (n : ℝ) * K ^ n * (2 + L) + 1) * S * ‖x - y‖ ^ α :=
          harith2 (Real.rpow_nonneg (norm_nonneg _) α)

end Work.CR.Flat.Cauchy
