/-
# The clamped `V^r`-valued bilinear interpolation bound (area A8)

This module proves `Work.KMTAreas.A8.clamped_bound`, the interpolation step
`Work.KMTContract.VarBilinInterp` of the KMT contract: from the two endpoint estimates

  `‖V^r(T u v)‖_{ℓ^{q_i}} ≤ M_i ‖u‖_{a_i} ‖v‖_{b_i}`   (`i = 0, 1`)

for a bilinear operator `T` on finitely supported inputs one gets

  `‖V^r_K(T u v)‖_{ℓ^q} ≤ M₀^{1-θ} M₁^θ ‖u‖_a ‖v‖_b`

for the interpolated exponents `1/a = (1-θ)/a₀ + θ/a₁` (and likewise for `b`, `q`), where `V^r_K`
is the *clamped* variational norm `Work.KMTAreas.vNormK` of `A8Defs`.

## The argument (three lines / Stein interpolation, with the clamped norm linearised)

* The clamped norm on `ℂ^{K+1}` is linearised by a test object
  (`Work.KMTAreas.A8.exists_testObject`): for every vector `c` there is a finitely supported
  `Ψ` with `‖pair a Ψ‖ ≤ vNormK r K a` for *all* `a` and `pair c Ψ = vNormK r K c`
  (`exists_test_psi`, `lam_test_psi`).
* For a finitely supported test function `h` one chooses, for each `x`, such a `Ψ` rescaled by a
  unit complex number so that `pair (T u v · x) (ψ x) * h x = vNormK r K (T u v · x) * ‖h x‖` is
  real and nonnegative; then `lam T ψ u v h` is a *scalar trilinear form* in `(u, v, h)`.
* Its endpoint estimates follow from the hypotheses by `Work.KMTAreas.A8.lam_endpoint` (Hölder plus
  the pointwise domination of the pairing by the variational norm), and the interpolation is
  `Work.KMTAreas.lam_three_lines` (`three_lines_bound` here), the third slot's boundary estimates
  being `Work.Analysis.Interpolation.eLpNorm_analyticFamily_re_zero_of` / `_re_one_of`,
  with the exponent `t₀ = (1 - (q₀⁻¹).toReal)/(1 - (q⁻¹).toReal)` so that the boundary exponent
  `conjExp q₀` scales back to `conjExp q`.
* The extremal test function `h_s` of the `ℒ^q` duality (`finsupp_rpow_le`, `h_s x = (F x)^{q-1}`
  on a finite set `s`) turns the resulting bound `X ≤ C · X^{1 - 1/q}` into `X^{1/q} ≤ C`
  (`rpow_le_of_le_mul_rpow`), and monotone convergence over finite sets
  (`eLpNorm_ofReal_le_of_finset_rpow_le`) yields the `ℒ^q` bound.

The degenerate cases `M₀ = 0`, `M₁ = 0`, `‖u‖_a = 0`, `‖v‖_b = 0` are handled separately (there the
clamped norm vanishes pointwise), and the case `q = 1` (where the endpoint estimates force
`q₀ = q₁ = 1`, so that the third-slot endpoint exponent is `⊤`) uses the trivial analytic family
with exponents `t₀ = t₁ = 1`.
-/
import Mathlib
import Submission.Work.KMTAreas.A8Assembly
import Submission.Work.KMTAreas.A8.exists_testObject
import Submission.Work.KMTAreas.A8.vNormK_basic
import Submission.Work.KMTAreas.A8.lam_family
import Submission.Work.KMTAreas.A8.lam_endpoint
import Submission.Commons.Analysis.MeasureTheory.iSup_rpow_eq
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A8

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.InverseTheory (FinSupp)

lemma enorm_le_eLpNorm_count {ε : Type*} [TopologicalSpace ε] [ENorm ε] {f : ℤ → ε} {p : ENNReal} (hp : p ≠ 0)
    (hpf : p < ⊤) (x : ℤ) : ‖f x‖ₑ ≤ eLpNorm f p Measure.count := by
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp (ne_of_lt hpf)
  have h1 : ‖f x‖ₑ ^ p.toReal ≤ ∑' y : ℤ, ‖f y‖ₑ ^ p.toReal :=
    ENNReal.le_tsum (f := fun y : ℤ => ‖f y‖ₑ ^ p.toReal) x
  calc ‖f x‖ₑ = (‖f x‖ₑ ^ p.toReal) ^ (1 / p.toReal) := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt hpR), ENNReal.rpow_one]
    _ ≤ (∑' y : ℤ, ‖f y‖ₑ ^ p.toReal) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow h1 (by positivity)
    _ = eLpNorm f p Measure.count := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := AEStronglyMeasurable.of_discrete) hp (ne_of_lt hpf), lintegral_count]

lemma eq_zero_of_eLpNorm_eq_zero {ε : Type*} [TopologicalSpace ε] [ENormedAddMonoid ε]
    {f : ℤ → ε} {p : ENNReal} (hp : p ≠ 0) (hpf : p < ⊤)
    (h : eLpNorm f p Measure.count = 0) : ∀ x, f x = 0 := by
  intro x
  have h1 := enorm_le_eLpNorm_count (f := f) hp hpf x
  rw [h] at h1
  have h2 : ‖f x‖ₑ = 0 := le_antisymm h1 bot_le
  simpa using h2

lemma pair_smul_right (a : ℕ → ℂ) (c : ℂ) (l : ℕ →₀ ℂ) :
    pair a (c • l) = c * pair a l := by
  rw [pair, pair, Finsupp.sum_smul_index (fun i => by simp only [mul_zero]), Finsupp.mul_sum]
  exact Finsupp.sum_congr (fun i _ => by ring)

lemma norm_pair_smul_right (a : ℕ → ℂ) (c : ℂ) (l : ℕ →₀ ℂ) :
    ‖pair a (c • l)‖ = ‖c‖ * ‖pair a l‖ := by
  rw [pair_smul_right, norm_mul]

lemma exists_test_psi {T : (ℤ → ℂ) → (ℤ → ℂ) → ℕ → ℤ → ℂ} {r : NNReal} (hr : 1 ≤ r)
    (K : ℕ) (u v : ℤ → ℂ) (h : ℤ →₀ ℂ) :
    ∃ ψ : ℤ → ℕ →₀ ℂ,
      (∀ (x : ℤ) (a : ℕ → ℂ),
        ENNReal.ofReal ‖pair a (ψ x)‖ ≤ PointwiseErgodicTheorems.variationalNorm r a) ∧
      (∀ x : ℤ, pair (fun n : ℕ => T u v n x) (ψ x) * (h x : ℂ)
          = (((vNormK r K (fun n : ℕ => T u v n x)) * ‖(h x : ℂ)‖ : ℝ) : ℂ)) := by
  obtain ⟨Ψ, hΨ₁, hΨ₂⟩ := exists_testObject r hr
  refine ⟨fun x => (if h x = 0 then (1 : ℂ) else ((‖(h x : ℂ)‖ : ℝ) : ℂ) / (h x : ℂ))
      • Ψ K (fun n : ℕ => T u v n x), ?_, ?_⟩
  · intro x a
    set ν : ℂ := if h x = 0 then (1 : ℂ) else ((‖(h x : ℂ)‖ : ℝ) : ℂ) / (h x : ℂ) with hν
    have hν1 : ‖ν‖ ≤ 1 := by
      rw [hν]
      by_cases hx : h x = 0
      · rw [if_pos hx]; simp
      · rw [if_neg hx, norm_div]
        have h1 : ‖(((‖(h x : ℂ)‖ : ℝ)) : ℂ)‖ = ‖(h x : ℂ)‖ := by simp
        rw [h1, div_self (norm_ne_zero_iff.mpr hx)]
    calc ENNReal.ofReal ‖pair a (ν • Ψ K (fun n : ℕ => T u v n x))‖
        = ENNReal.ofReal (‖ν‖ * ‖pair a (Ψ K (fun n : ℕ => T u v n x))‖) := by
          rw [norm_pair_smul_right]
      _ ≤ ENNReal.ofReal (1 * ‖pair a (Ψ K (fun n : ℕ => T u v n x))‖) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hν1 (norm_nonneg _))
      _ = ENNReal.ofReal ‖pair a (Ψ K (fun n : ℕ => T u v n x))‖ := by rw [one_mul]
      _ ≤ ENNReal.ofReal (vNormK r K a) :=
          ENNReal.ofReal_le_ofReal (hΨ₁ K (fun n : ℕ => T u v n x) a)
      _ ≤ PointwiseErgodicTheorems.variationalNorm r a := (vNormK_basic r hr a).1 K
  · intro x
    set ν : ℂ := if h x = 0 then (1 : ℂ) else ((‖(h x : ℂ)‖ : ℝ) : ℂ) / (h x : ℂ) with hν
    have hνmul : ν * (h x : ℂ) = ((‖(h x : ℂ)‖ : ℝ) : ℂ) := by
      rw [hν]
      by_cases hx : h x = 0
      · rw [if_pos hx, hx]; simp
      · rw [if_neg hx, div_mul_cancel₀ _ hx]
    rw [pair_smul_right, hΨ₂ K (fun n : ℕ => T u v n x)]
    have hswap : (ν * (((vNormK r K (fun n : ℕ => T u v n x)) : ℝ)) : ℂ) * (h x : ℂ)
        = (((vNormK r K (fun n : ℕ => T u v n x)) : ℝ) : ℂ) * (ν * (h x : ℂ)) := by ring
    rw [hswap, hνmul]
    exact (Complex.ofReal_mul _ _).symm

lemma lam_test_psi {T : (ℤ → ℂ) → (ℤ → ℂ) → ℕ → ℤ → ℂ} {r : NNReal} (K : ℕ) (u v : ℤ → ℂ)
    (h : ℤ →₀ ℂ) (ψ : ℤ → ℕ →₀ ℂ)
    (hψ : ∀ x : ℤ, pair (fun n : ℕ => T u v n x) (ψ x) * (h x : ℂ)
          = (((vNormK r K (fun n : ℕ => T u v n x)) * ‖(h x : ℂ)‖ : ℝ) : ℂ))
    (hu : FinSupp u) (hv : FinSupp v) (hh : FinSupp (fun x : ℤ => (h x : ℂ))) :
    lam T ψ u v (fun x : ℤ => (h x : ℂ))
      = ((∑ x ∈ h.support, vNormK r K (fun n : ℕ => T u v n x) * ‖(h x : ℂ)‖ : ℝ) : ℂ) := by
  rw [lam_of_finSupp hu hv hh]
  rw [tsum_eq_sum (s := h.support) (fun x hx => ?_)]
  · rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    exact hψ x
  · rw [Finsupp.notMem_support_iff] at hx
    show pair (fun n : ℕ => T u v n x) (ψ x) * (h x : ℂ) = 0
    rw [hx, mul_zero]

lemma finsupp_rpow_le {φ : ℤ → ℝ} (hφ : ∀ x, 0 ≤ φ x) {q : ENNReal} (hq : 1 ≤ q) (hqf : q < ⊤)
    (s : Finset ℤ) (hs : s.Nonempty) :
    (eLpNorm (fun x : ℤ => ((∑ y ∈ s, Finsupp.single y ((φ y ^ (q.toReal - 1) : ℝ) : ℂ)) x : ℂ))
        (conjExp q) Measure.count ≤
      (∑ x ∈ s, ENNReal.ofReal (φ x) ^ q.toReal) ^ (1 - (q⁻¹).toReal))
    ∧ (∑ x ∈ s, φ x
        * ‖(((∑ y ∈ s, Finsupp.single y ((φ y ^ (q.toReal - 1) : ℝ) : ℂ)) : ℤ →₀ ℂ) : ℤ → ℂ) x‖
        = ∑ x ∈ s, φ x ^ q.toReal) := by
  have hval : ∀ x : ℤ,
      (((∑ y ∈ s, Finsupp.single y ((φ y ^ (q.toReal - 1) : ℝ) : ℂ)) : ℤ →₀ ℂ) : ℤ → ℂ) x
        = if x ∈ s then (((φ x) ^ (q.toReal - 1) : ℝ) : ℂ) else 0 := by
    intro x
    rw [Finsupp.finsetSum_apply]
    by_cases hx : x ∈ s
    · rw [if_pos hx, Finset.sum_eq_single x]
      · simp
      · intro y _ hyx
        rw [Finsupp.single_eq_of_ne (Ne.symm hyx)]
      · intro hx'
        exact absurd hx hx'
    · rw [if_neg hx]
      refine Finset.sum_eq_zero (fun y hy => ?_)
      rw [Finsupp.single_eq_of_ne ?_]
      rintro rfl
      exact hx hy
  constructor
  · by_cases hq1 : q = 1
    · subst hq1
      have hconj : conjExp (1 : ENNReal) = ⊤ := by
        simp only [conjExp, inv_one, tsub_self, ENNReal.inv_zero]
      have hexp : 1 - ((1 : ENNReal)⁻¹).toReal = 0 := by
        simp only [inv_one, ENNReal.toReal_one, sub_self]
      rw [hconj, hexp, ENNReal.rpow_zero, eLpNorm_exponent_top (hf := by pw_aesm)]
      refine eLpNormEssSup_le_of_ae_enorm_bound ?_
      filter_upwards with x
      rw [hval x]
      by_cases hx : x ∈ s
      · rw [if_pos hx]
        norm_num
      · rw [if_neg hx]
        simp
    · have hq_gt : 1 < q := lt_of_le_of_ne hq (Ne.symm hq1)
      have hqR : 1 < q.toReal := by
        simpa using ENNReal.toReal_strict_mono (ne_of_lt hqf) hq_gt
      set st : ℝ := 1 - (q⁻¹).toReal with hst
      have hst_pos : 0 < st := by
        rw [hst, ENNReal.toReal_inv]
        have h3 : (q.toReal)⁻¹ < 1 := by
          rw [← one_div, div_lt_one (by linarith : (0:ℝ) < q.toReal)]
          exact hqR
        linarith
      have hconj : conjExp q = ENNReal.ofReal (st⁻¹) := by
        rw [conjExp]
        have h1 : ENNReal.ofReal st = 1 - q⁻¹ := by
          rw [hst, ENNReal.ofReal_sub 1 ENNReal.toReal_nonneg, ENNReal.ofReal_one,
            ENNReal.ofReal_toReal (ENNReal.inv_ne_top.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hq)))]
        rw [← h1, ENNReal.ofReal_inv_of_pos hst_pos]
      have harith : (q.toReal - 1) * st⁻¹ = q.toReal := by
        rw [hst, ENNReal.toReal_inv]
        have h2 : q.toReal ≠ 1 := ne_of_gt hqR
        have h3 : q.toReal ≠ 0 := ne_of_gt (lt_trans zero_lt_one hqR)
        field_simp
      have htsum : (∑' x : ℤ,
          ‖(((∑ y ∈ s, Finsupp.single y ((φ y ^ (q.toReal - 1) : ℝ) : ℂ)) : ℤ →₀ ℂ)
            : ℤ → ℂ) x‖ₑ ^ st⁻¹)
          = ∑ x ∈ s, ENNReal.ofReal (φ x) ^ q.toReal := by
        rw [tsum_eq_sum (s := s) (fun x hx => ?_)]
        · refine Finset.sum_congr rfl (fun x hx => ?_)
          have hpow' : ENNReal.ofReal (φ x) ^ (q.toReal - 1)
              = ENNReal.ofReal ((φ x) ^ (q.toReal - 1)) :=
            ENNReal.ofReal_rpow_of_nonneg (x := φ x) (p := q.toReal - 1)
              (hφ x) (by linarith [hqR])
          rw [hval x, if_pos hx, ← ofReal_norm,
            show ‖((((φ x) ^ (q.toReal - 1) : ℝ)) : ℂ)‖ = |(φ x) ^ (q.toReal - 1)|
              from RCLike.norm_ofReal _,
            abs_of_nonneg (Real.rpow_nonneg (hφ x) _),
            ← hpow', ← ENNReal.rpow_mul, harith]
        · rw [hval x, if_neg hx]
          simp only [enorm_zero]
          exact ENNReal.zero_rpow_of_pos (inv_pos.mpr hst_pos)
      have hexp : 1 - (q⁻¹).toReal = st := rfl
      rw [hconj, Commons.Analysis.DiscreteCZ.eLpNorm_count_eq_tsum (p := st⁻¹)
        (inv_pos.mpr hst_pos), htsum, one_div, inv_inv]
  · refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [hval x, if_pos hx,
      show ‖((((φ x) ^ (q.toReal - 1) : ℝ)) : ℂ)‖ = |(φ x) ^ (q.toReal - 1)|
        from RCLike.norm_ofReal _,
      abs_of_nonneg (Real.rpow_nonneg (hφ x) _)]
    have h2 : (0:ℝ) < q.toReal := by
      have h3 : (1:ℝ) ≤ q.toReal := by
        rw [← ENNReal.toReal_one]
        exact ENNReal.toReal_mono (ne_of_lt hqf) hq
      linarith
    have hpow := Real.rpow_add' (x := φ x) (y := 1) (z := q.toReal - 1) (hφ x)
      (by linarith : (1:ℝ) + (q.toReal - 1) ≠ 0)
    rw [Real.rpow_one] at hpow
    rw [← hpow, show (1:ℝ) + (q.toReal - 1) = q.toReal from by ring]

lemma eLpNorm_ofReal_le_of_finset_rpow_le {φ : ℤ → ℝ} (hφ : ∀ x, 0 ≤ φ x) {q : ENNReal}
    (hq : 1 ≤ q) (hqf : q < ⊤) {C : ENNReal}
    (hC : ∀ s : Finset ℤ, (∑ x ∈ s, ENNReal.ofReal (φ x) ^ q.toReal) ^ (1 / q.toReal) ≤ C) :
    eLpNorm (fun x : ℤ => (φ x : ℂ)) q Measure.count ≤ C := by
  have hq0 : q ≠ 0 := (lt_of_lt_of_le zero_lt_one hq).ne'
  have hqt : q ≠ ⊤ := ne_of_lt hqf
  have hpos : 0 < 1 / q.toReal := by
    have h : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
    positivity
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hq0 hqt]
  have hcongr : (fun x : ℤ => ‖((φ x : ℂ))‖ₑ ^ q.toReal)
      = fun x => ENNReal.ofReal (φ x) ^ q.toReal := by
    funext x
    rw [← ofReal_norm, show ‖(((φ x : ℝ)) : ℂ)‖ = |φ x| from RCLike.norm_ofReal _,
      abs_of_nonneg (hφ x)]
  rw [hcongr, lintegral_count, ENNReal.tsum_eq_iSup_sum,
    Commons.Analysis.MeasureTheory.iSup_rpow_eq hpos]
  exact iSup_le hC

lemma inv_relation_real {p₀ p₁ p : ENNReal} {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hp₀0 : p₀ ≠ 0) (hp₀f : p₀ < ⊤) (hp₁0 : p₁ ≠ 0) (hp₁f : p₁ < ⊤)
    (hrel : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) :
    p.toReal⁻¹ = (1 - θ) * p₀.toReal⁻¹ + θ * p₁.toReal⁻¹ := by
  have h1 : ENNReal.ofReal (1 - θ) * p₀⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.mpr hp₀0)
  have h2 : ENNReal.ofReal θ * p₁⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.mpr hp₁0)
  have h := congrArg ENNReal.toReal hrel
  rw [ENNReal.toReal_add h1 h2, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal hθ₀.le] at h
  exact h

lemma one_sub_inv_relation {p₀ p₁ p : ENNReal} {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hp₀0 : p₀ ≠ 0) (hp₀f : p₀ < ⊤) (hp₁0 : p₁ ≠ 0) (hp₁f : p₁ < ⊤)
    (hrel : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) :
    1 - (p⁻¹).toReal = (1 - θ) * (1 - (p₀⁻¹).toReal) + θ * (1 - (p₁⁻¹).toReal) := by
  have h := inv_relation_real hθ₀ hθ₁ hp₀0 hp₀f hp₁0 hp₁f hrel
  rw [ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_inv]
  linarith

lemma one_le_conjExp {p : ENNReal} (hp : 1 ≤ p) : 1 ≤ conjExp p := by
  rw [conjExp, ENNReal.one_le_inv]
  exact tsub_le_self

lemma conjExp_lt_top {p : ENNReal} (hp : 1 < p) : conjExp p < ⊤ := by
  rw [conjExp, ENNReal.inv_lt_top, tsub_pos_iff_lt, ENNReal.inv_lt_one]
  exact hp


/-- The three-lines step: from the two endpoint estimates (in the `V^r`-norm) for the bilinear
operator `T`, the interpolated estimate for the trilinear form built from a test family `ψ`. -/
lemma three_lines_bound {T : (ℤ → ℂ) → (ℤ → ℂ) → ℕ → ℤ → ℂ}
    (hlin₁ : ∀ f f' g (c : ℂ), FinSupp f → FinSupp f' → FinSupp g →
      T (f + c • f') g = T f g + c • T f' g)
    (hlin₂ : ∀ f g g' (c : ℂ), FinSupp f → FinSupp g → FinSupp g' →
      T f (g + c • g') = T f g + c • T f g')
    {r : NNReal} (hr : 1 ≤ r)
    {a₀ b₀ q₀ a₁ b₁ q₁ a b q : ENNReal} {θ : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (ha₀ : 1 < a₀) (ha₀f : a₀ < ⊤) (hb₀ : 1 < b₀) (hb₀f : b₀ < ⊤)
    (ha₁ : 1 < a₁) (ha₁f : a₁ < ⊤) (hb₁ : 1 < b₁) (hb₁f : b₁ < ⊤)
    (hq₀ : 1 ≤ q₀) (hq₀f : q₀ < ⊤) (hq₁ : 1 ≤ q₁) (hq₁f : q₁ < ⊤)
    (hrela : a.toReal⁻¹ = (1 - θ) * a₀.toReal⁻¹ + θ * a₁.toReal⁻¹)
    (hrelb : b.toReal⁻¹ = (1 - θ) * b₀.toReal⁻¹ + θ * b₁.toReal⁻¹)
    (haf : a < ⊤) (hbf : b < ⊤) (hag : 1 ≤ a) (hbg : 1 ≤ b)
    {M₀ M₁ : NNReal}
    (hT₀ : ∀ u v : ℤ → ℂ, FinSupp u → FinSupp v →
      eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => T u v n x)) q₀ Measure.count
        ≤ (M₀ : ENNReal) * eLpNorm u a₀ Measure.count * eLpNorm v b₀ Measure.count)
    (hT₁ : ∀ u v : ℤ → ℂ, FinSupp u → FinSupp v →
      eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => T u v n x)) q₁ Measure.count
        ≤ (M₁ : ENNReal) * eLpNorm u a₁ Measure.count * eLpNorm v b₁ Measure.count)
    {ψ : ℤ → ℕ →₀ ℂ}
    (hψ : ∀ (x : ℤ) (a : ℕ → ℂ),
      ENNReal.ofReal ‖pair a (ψ x)‖ ≤ PointwiseErgodicTheorems.variationalNorm r a)
    {u v h : ℤ → ℂ} (hu : FinSupp u) (hv : FinSupp v) (hh : FinSupp h)
    (hU : eLpNorm u a Measure.count < ⊤) (hU0 : eLpNorm u a Measure.count ≠ 0)
    (hV : eLpNorm v b Measure.count < ⊤) (hV0 : eLpNorm v b Measure.count ≠ 0)
    {t₀ t₁ : ℝ} (ht₀ : 0 ≤ t₀) (ht₁ : 0 ≤ t₁) (ht : (1 - θ) * t₀ + θ * t₁ = 1)
    {W : ENNReal} (hWlt : W < ⊤) (hW0 : W ≠ 0)
    (hbd₀ : ∀ z : ℂ, z.re = 0 →
      eLpNorm (Work.Analysis.Interpolation.analyticFamily h ((t₀ : ℝ) : ℂ) ((t₁ : ℝ) : ℂ) z)
        (conjExp q₀) Measure.count ≤ W ^ t₀)
    (hbd₁ : ∀ z : ℂ, z.re = 1 →
      eLpNorm (Work.Analysis.Interpolation.analyticFamily h ((t₀ : ℝ) : ℂ) ((t₁ : ℝ) : ℂ) z)
        (conjExp q₁) Measure.count ≤ W ^ t₁) :
    ‖lam T ψ u v h‖ₑ ≤ ((M₀ : ENNReal) ^ (1 - θ) * (M₁ : ENNReal) ^ θ)
      * eLpNorm u a Measure.count * eLpNorm v b Measure.count * W := by
  have hpθ : 1 / a.toReal = (1 - θ) / a₀.toReal + θ / a₁.toReal := by
    rw [one_div, div_eq_mul_inv, div_eq_mul_inv]
    exact hrela
  have hqθ : 1 / b.toReal = (1 - θ) / b₀.toReal + θ / b₁.toReal := by
    rw [one_div, div_eq_mul_inv, div_eq_mul_inv]
    exact hrelb
  have hpa₀ : 0 < a₀.toReal := ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one ha₀)) (ne_of_lt ha₀f)
  have hpa₁ : 0 < a₁.toReal := ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one ha₁)) (ne_of_lt ha₁f)
  have hpb₀ : 0 < b₀.toReal := ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one hb₀)) (ne_of_lt hb₀f)
  have hpb₁ : 0 < b₁.toReal := ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one hb₁)) (ne_of_lt hb₁f)
  have hpa : 0 < a.toReal := ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hag)) (ne_of_lt haf)
  have hpb : 0 < b.toReal := ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hbg)) (ne_of_lt hbf)
  have h₀ : ∀ u' v' w' : ℤ → ℂ, ‖lam T ψ u' v' w'‖ₑ ≤ (M₀ : ENNReal)
      * eLpNorm u' (ENNReal.ofReal (a₀.toReal)) Measure.count
      * eLpNorm v' (ENNReal.ofReal (b₀.toReal)) Measure.count
      * eLpNorm w' (conjExp q₀) Measure.count := by
    intro u' v' w'
    have h := lam_endpoint hlin₁ hlin₂ hr ψ hψ (A := a₀) (B := b₀) (Q := q₀) hq₀
      (M := M₀) hT₀ u' v' w'
    simpa only [ENNReal.ofReal_toReal (ne_of_lt ha₀f), ENNReal.ofReal_toReal (ne_of_lt hb₀f)] using h
  have h₁ : ∀ u' v' w' : ℤ → ℂ, ‖lam T ψ u' v' w'‖ₑ ≤ (M₁ : ENNReal)
      * eLpNorm u' (ENNReal.ofReal (a₁.toReal)) Measure.count
      * eLpNorm v' (ENNReal.ofReal (b₁.toReal)) Measure.count
      * eLpNorm w' (conjExp q₁) Measure.count := by
    intro u' v' w'
    have h := lam_endpoint hlin₁ hlin₂ hr ψ hψ (A := a₁) (B := b₁) (Q := q₁) hq₁
      (M := M₁) hT₁ u' v' w'
    simpa only [ENNReal.ofReal_toReal (ne_of_lt ha₁f), ENNReal.ofReal_toReal (ne_of_lt hb₁f)] using h
  obtain ⟨hdiff, hbdd⟩ := lam_family hlin₁ hlin₂ ψ u v h hu hv hh
    (a.toReal / a₀.toReal) (a.toReal / a₁.toReal) (b.toReal / b₀.toReal) (b.toReal / b₁.toReal)
    t₀ t₁
  have hkey := lam_three_lines (T := T) (psi := ψ) u v h
    (p₀ := a₀.toReal) (p₁ := a₁.toReal) (q₀ := b₀.toReal) (q₁ := b₁.toReal)
    (p := a.toReal) (q := b.toReal) (θ' := θ)
    hpa₀ hpa₁ hpb₀ hpb₁ hpa hpb hθ₀ hθ₁ hpθ hqθ
    (r₀ := conjExp q₀) (r₁ := conjExp q₁) (one_le_conjExp hq₀) (one_le_conjExp hq₁)
    (M₀ := M₀) (M₁ := M₁) (t₀ := t₀) (t₁ := t₁) ht₀ ht₁ ht (W := W) hWlt hbd₀ hbd₁
    hdiff hbdd h₀ h₁
    (by rwa [ENNReal.ofReal_toReal (ne_of_lt haf)]) (by rwa [ENNReal.ofReal_toReal (ne_of_lt hbf)])
    (by rwa [ENNReal.ofReal_toReal (ne_of_lt haf)]) (by rwa [ENNReal.ofReal_toReal (ne_of_lt hbf)])
    hW0
  simpa only [ENNReal.ofReal_toReal (ne_of_lt haf), ENNReal.ofReal_toReal (ne_of_lt hbf)] using hkey


lemma norm_ofReal_of_nonneg' (r : ℝ) (h : 0 ≤ r) : ‖(r : ℂ)‖ = r := by
  rw [show ‖(r : ℂ)‖ = |r| from RCLike.norm_ofReal r, abs_of_nonneg h]

lemma vNormK_nonneg (r : NNReal) (K : ℕ) (a : ℕ → ℂ) : 0 ≤ vNormK r K a := by
  rw [vNormK]
  exact add_nonneg (supK_basic K a).1 ((varK_basic r a).1 K)

lemma rpow_le_of_le_mul_rpow {X C : ENNReal} {q : ENNReal} (hq : 1 ≤ q) (hqf : q < ⊤)
    (hX : X < ⊤) (h : X ≤ C * X ^ (1 - (q⁻¹).toReal)) : X ^ (1 / q.toReal) ≤ C := by
  have hqinv_le : (q⁻¹).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top (ENNReal.inv_le_one.mpr hq)
  have hexpnn : 0 ≤ 1 - (q⁻¹).toReal := by linarith
  have hqR : (0:ℝ) < q.toReal := by
    have h1 : (1:ℝ) ≤ q.toReal := by
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_mono (ne_of_lt hqf) hq
    linarith
  rcases eq_or_ne X 0 with hX0 | hX0
  · rw [hX0, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hqR)]
    exact zero_le
  · have hexp : 1 / q.toReal + (1 - (q⁻¹).toReal) = 1 := by
      rw [ENNReal.toReal_inv, one_div]
      ring
    have hB0 : X ^ (1 - (q⁻¹).toReal) ≠ 0 := by
      intro hz
      rw [ENNReal.rpow_eq_zero_iff] at hz
      rcases hz with ⟨hx, -⟩ | ⟨hx, -⟩
      · exact hX0 hx
      · exact (ne_of_lt hX) hx
    have hBtop : X ^ (1 - (q⁻¹).toReal) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg hexpnn (ne_of_lt hX)
    have hXeq : X ^ (1 / q.toReal) * X ^ (1 - (q⁻¹).toReal) = X := by
      rw [← ENNReal.rpow_add (x := X) (y := 1 / q.toReal) (z := 1 - (q⁻¹).toReal) hX0
        (ne_of_lt hX), hexp, ENNReal.rpow_one]
    have h' : X ^ (1 / q.toReal) * X ^ (1 - (q⁻¹).toReal)
        ≤ C * X ^ (1 - (q⁻¹).toReal) := by
      rw [hXeq]
      exact h
    exact (ENNReal.mul_le_mul_iff_left hB0 (ne_of_lt hBtop)).mp h'

/-- The exponent facts collected for the main proof. -/
lemma conjExp_one_eq : conjExp (1 : ENNReal) = ⊤ := by
  simp only [conjExp, inv_one, tsub_self, ENNReal.inv_zero]

theorem clamped_bound {T : (ℤ → ℂ) → (ℤ → ℂ) → ℕ → ℤ → ℂ}
    (hlin₁ : ∀ f f' g (c : ℂ), Work.Analysis.InverseTheory.FinSupp f →
      Work.Analysis.InverseTheory.FinSupp f' → Work.Analysis.InverseTheory.FinSupp g →
      T (f + c • f') g = T f g + c • T f' g)
    (hlin₂ : ∀ f g g' (c : ℂ), Work.Analysis.InverseTheory.FinSupp f →
      Work.Analysis.InverseTheory.FinSupp g → Work.Analysis.InverseTheory.FinSupp g' →
      T f (g + c • g') = T f g + c • T f g')
    {r : NNReal} (hr : 1 ≤ r) (K : ℕ)
    {a₀ b₀ q₀ a₁ b₁ q₁ a b q : ENNReal} {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (ha₀ : 1 < a₀) (ha₀f : a₀ < ⊤) (hb₀ : 1 < b₀) (hb₀f : b₀ < ⊤)
    (ha₁ : 1 < a₁) (ha₁f : a₁ < ⊤) (hb₁ : 1 < b₁) (hb₁f : b₁ < ⊤)
    (hq₀ : 1 ≤ q₀) (hq₀f : q₀ < ⊤) (hq₁ : 1 ≤ q₁) (hq₁f : q₁ < ⊤)
    (hqrel₀ : a⁻¹ = ENNReal.ofReal (1 - θ) * a₀⁻¹ + ENNReal.ofReal θ * a₁⁻¹)
    (hqrel₁ : b⁻¹ = ENNReal.ofReal (1 - θ) * b₀⁻¹ + ENNReal.ofReal θ * b₁⁻¹)
    (hqrel₂ : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    {M₀ M₁ : NNReal}
    (hT₀ : ∀ u v : ℤ → ℂ, Work.Analysis.InverseTheory.FinSupp u → Work.Analysis.InverseTheory.FinSupp v →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => T u v n x)) q₀ MeasureTheory.Measure.count
        ≤ (M₀ : ENNReal) * MeasureTheory.eLpNorm u a₀ MeasureTheory.Measure.count * MeasureTheory.eLpNorm v b₀ MeasureTheory.Measure.count)
    (hT₁ : ∀ u v : ℤ → ℂ, Work.Analysis.InverseTheory.FinSupp u → Work.Analysis.InverseTheory.FinSupp v →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => T u v n x)) q₁ MeasureTheory.Measure.count
        ≤ (M₁ : ENNReal) * MeasureTheory.eLpNorm u a₁ MeasureTheory.Measure.count * MeasureTheory.eLpNorm v b₁ MeasureTheory.Measure.count) :
    ∀ u v : ℤ → ℂ, Work.Analysis.InverseTheory.FinSupp u → Work.Analysis.InverseTheory.FinSupp v →
      MeasureTheory.eLpNorm (fun x : ℤ => (Work.KMTAreas.vNormK r K (fun n : ℕ => T u v n x) : ℂ)) q MeasureTheory.Measure.count
        ≤ ((M₀ : ENNReal) ^ (1 - θ) * (M₁ : ENNReal) ^ θ)
            * MeasureTheory.eLpNorm u a MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm v b MeasureTheory.Measure.count := by
  intro u v hu hv
  -- ## exponent bookkeeping
  have hq_ge : 1 ≤ q := by
    rw [← ENNReal.inv_le_one]
    calc q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹ := hqrel₂
      _ ≤ ENNReal.ofReal (1 - θ) * 1 + ENNReal.ofReal θ * 1 := by
          gcongr
          · exact ENNReal.inv_le_one.mpr hq₀
          · exact ENNReal.inv_le_one.mpr hq₁
      _ = 1 := by
          rw [mul_one, mul_one, ← ENNReal.ofReal_add (by linarith) (by linarith)]
          norm_num
  have hq_lt : q < ⊤ := by
    have hqinv0 : q⁻¹ ≠ 0 := by
      rw [hqrel₂]
      refine ne_of_gt (lt_of_lt_of_le ?_ le_add_self)
      exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hθ₀).ne'
        (ENNReal.inv_ne_zero.mpr (ne_of_lt hq₁f))
    refine lt_top_iff_ne_top.mpr fun h => hqinv0 ?_
    rw [h, ENNReal.inv_top]
  have hq0' : q ≠ 0 := (lt_of_lt_of_le zero_lt_one hq_ge).ne'
  have hqR : (0:ℝ) < q.toReal := ENNReal.toReal_pos hq0' (ne_of_lt hq_lt)
  have hq₀0 : q₀ ≠ 0 := (lt_of_lt_of_le zero_lt_one hq₀).ne'
  have hq₁0 : q₁ ≠ 0 := (lt_of_lt_of_le zero_lt_one hq₁).ne'
  have ha₀0 : a₀ ≠ 0 := (lt_of_lt_of_le zero_lt_one (le_of_lt ha₀)).ne'
  have ha₁0 : a₁ ≠ 0 := (lt_of_lt_of_le zero_lt_one (le_of_lt ha₁)).ne'
  have hb₀0 : b₀ ≠ 0 := (lt_of_lt_of_le zero_lt_one (le_of_lt hb₀)).ne'
  have hb₁0 : b₁ ≠ 0 := (lt_of_lt_of_le zero_lt_one (le_of_lt hb₁)).ne'
  have ha_ge : 1 ≤ a := by
    rw [← ENNReal.inv_le_one]
    calc a⁻¹ = ENNReal.ofReal (1 - θ) * a₀⁻¹ + ENNReal.ofReal θ * a₁⁻¹ := hqrel₀
      _ ≤ ENNReal.ofReal (1 - θ) * 1 + ENNReal.ofReal θ * 1 := by
          gcongr
          · exact ENNReal.inv_le_one.mpr (le_of_lt ha₀)
          · exact ENNReal.inv_le_one.mpr (le_of_lt ha₁)
      _ = 1 := by
          rw [mul_one, mul_one, ← ENNReal.ofReal_add (by linarith) (by linarith)]
          norm_num
  have hb_ge : 1 ≤ b := by
    rw [← ENNReal.inv_le_one]
    calc b⁻¹ = ENNReal.ofReal (1 - θ) * b₀⁻¹ + ENNReal.ofReal θ * b₁⁻¹ := hqrel₁
      _ ≤ ENNReal.ofReal (1 - θ) * 1 + ENNReal.ofReal θ * 1 := by
          gcongr
          · exact ENNReal.inv_le_one.mpr (le_of_lt hb₀)
          · exact ENNReal.inv_le_one.mpr (le_of_lt hb₁)
      _ = 1 := by
          rw [mul_one, mul_one, ← ENNReal.ofReal_add (by linarith) (by linarith)]
          norm_num
  have ha_ne : a ≠ ⊤ := by
    intro h
    have hpos : 0 < a⁻¹ := by
      rw [hqrel₀]
      exact lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hθ₀).ne'
        (ENNReal.inv_ne_zero.mpr (ne_of_lt ha₁f))) le_add_self
    rw [h, ENNReal.inv_top] at hpos
    exact lt_irrefl _ hpos
  have hb_ne : b ≠ ⊤ := by
    intro h
    have hpos : 0 < b⁻¹ := by
      rw [hqrel₁]
      exact lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hθ₀).ne'
        (ENNReal.inv_ne_zero.mpr (ne_of_lt hb₁f))) le_add_self
    rw [h, ENNReal.inv_top] at hpos
    exact lt_irrefl _ hpos
  have haf : a < ⊤ := lt_top_iff_ne_top.mpr ha_ne
  have hbf : b < ⊤ := lt_top_iff_ne_top.mpr hb_ne
  have ha0 : a ≠ 0 := (lt_of_lt_of_le zero_lt_one ha_ge).ne'
  have hb0 : b ≠ 0 := (lt_of_lt_of_le zero_lt_one hb_ge).ne'
  have hrela : a.toReal⁻¹ = (1 - θ) * a₀.toReal⁻¹ + θ * a₁.toReal⁻¹ :=
    inv_relation_real hθ₀ hθ₁ ha₀0 ha₀f ha₁0 ha₁f hqrel₀
  have hrelb : b.toReal⁻¹ = (1 - θ) * b₀.toReal⁻¹ + θ * b₁.toReal⁻¹ :=
    inv_relation_real hθ₀ hθ₁ hb₀0 hb₀f hb₁0 hb₁f hqrel₁
  have hrelq : 1 - (q⁻¹).toReal
      = (1 - θ) * (1 - (q₀⁻¹).toReal) + θ * (1 - (q₁⁻¹).toReal) :=
    one_sub_inv_relation hθ₀ hθ₁ hq₀0 hq₀f hq₁0 hq₁f hqrel₂
  -- ## the function `F` and the goal
  set F : ℤ → ℝ := fun x => vNormK r K (fun n : ℕ => T u v n x) with hFdef
  have hFnn : ∀ x, 0 ≤ F x := fun x => by rw [hFdef]; exact vNormK_nonneg r K _
  set Cst : ENNReal := (M₀ : ENNReal) ^ (1 - θ) * (M₁ : ENNReal) ^ θ with hCstdef
  suffices hgoal : eLpNorm (fun x : ℤ => (F x : ℂ)) q Measure.count
      ≤ Cst * eLpNorm u a Measure.count * eLpNorm v b Measure.count by
    simpa only [hFdef, hCstdef] using hgoal
  obtain ⟨Ψ, hΨ₁, hΨ₂⟩ := exists_testObject r hr
  have hvz : vNormK r K (0 : ℕ → ℂ) = 0 := by
    have h := hΨ₂ K (0 : ℕ → ℂ)
    have h2 : pair (0 : ℕ → ℂ) (Ψ K 0) = 0 := by
      simp only [pair, Finsupp.sum]
      exact Finset.sum_eq_zero (fun i hi => by simp)
    rw [h2] at h
    exact Complex.ofReal_eq_zero.mp h.symm
  -- ## degenerate cases
  by_cases hM : (M₀ : ENNReal) = 0 ∨ (M₁ : ENNReal) = 0
  · have hFzero : ∀ x, F x = 0 := by
      intro x
      have hVn : PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => T u v n x) = 0 := by
        rcases hM with hM | hM
        · have h := hT₀ u v hu hv
          rw [hM, zero_mul, zero_mul] at h
          exact (eq_zero_of_eLpNorm_eq_zero (f := fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => T u v n x)) hq₀0 hq₀f
            (le_antisymm h bot_le)) x
        · have h := hT₁ u v hu hv
          rw [hM, zero_mul, zero_mul] at h
          exact (eq_zero_of_eLpNorm_eq_zero (f := fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => T u v n x)) hq₁0 hq₁f
            (le_antisymm h bot_le)) x
      have h1 := (vNormK_basic r hr (fun n : ℕ => T u v n x)).1 K
      rw [hVn] at h1
      have h2 : ENNReal.ofReal (F x) = 0 := le_antisymm h1 bot_le
      exact le_antisymm (ENNReal.ofReal_eq_zero.mp h2) (hFnn x)
    have hzero : (fun x : ℤ => (F x : ℂ)) = fun _ => 0 := funext (fun x => by rw [hFzero x]; rfl)
    rw [hzero]
    simp
  · have hM0 : (M₀ : ENNReal) ≠ 0 := fun h => hM (Or.inl h)
    have hM1 : (M₁ : ENNReal) ≠ 0 := fun h => hM (Or.inr h)
    by_cases hU0 : eLpNorm u a Measure.count = 0
    · have hu0 : ∀ x, u x = 0 :=
        eq_zero_of_eLpNorm_eq_zero (f := u) ha0 haf hU0
      have hu_eq : u = 0 := funext hu0
      have hFzero : ∀ x, F x = 0 := by
        intro x
        have hvec : (fun n : ℕ => T u v n x) = (0 : ℕ → ℂ) := by
          funext n
          rw [hu_eq]
          exact congrFun (congrFun (T_zero_left hlin₁ v hv) n) x
        show vNormK r K (fun n : ℕ => T u v n x) = 0
        rw [hvec, hvz]
      have hzero : (fun x : ℤ => (F x : ℂ)) = fun _ => 0 :=
        funext (fun x => by rw [hFzero x]; rfl)
      rw [hzero]
      simp
    · by_cases hV0 : eLpNorm v b Measure.count = 0
      · have hv0 : ∀ x, v x = 0 :=
          eq_zero_of_eLpNorm_eq_zero (f := v) hb0 hbf hV0
        have hv_eq : v = 0 := funext hv0
        have hFzero : ∀ x, F x = 0 := by
          intro x
          have hvec : (fun n : ℕ => T u v n x) = (0 : ℕ → ℂ) := by
            funext n
            rw [hv_eq]
            exact congrFun (congrFun (T_zero_right hlin₂ u hu) n) x
          show vNormK r K (fun n : ℕ => T u v n x) = 0
          rw [hvec, hvz]
        have hzero : (fun x : ℤ => (F x : ℂ)) = fun _ => 0 :=
          funext (fun x => by rw [hFzero x]; rfl)
        rw [hzero]
        simp
      · have hCst_ne : Cst ≠ 0 := by
          rw [hCstdef]
          refine mul_ne_zero ?_ ?_
          · intro hz
            rw [ENNReal.rpow_eq_zero_iff] at hz
            rcases hz with ⟨hx, -⟩ | ⟨hx, hy⟩
            · exact hM0 hx
            · linarith
          · intro hz
            rw [ENNReal.rpow_eq_zero_iff] at hz
            rcases hz with ⟨hx, -⟩ | ⟨hx, hy⟩
            · exact hM1 hx
            · linarith
        by_cases hUt : eLpNorm u a Measure.count = ⊤
        · have hbig : Cst * eLpNorm u a Measure.count * eLpNorm v b Measure.count = ⊤ := by
            rw [hUt, ENNReal.mul_top hCst_ne, ENNReal.top_mul hV0]
          rw [hbig]
          exact le_top
        · by_cases hVt : eLpNorm v b Measure.count = ⊤
          · have hbig : Cst * eLpNorm u a Measure.count * eLpNorm v b Measure.count = ⊤ := by
              rw [hVt, ENNReal.mul_top (mul_ne_zero hCst_ne hU0)]
            rw [hbig]
            exact le_top
          · -- ## the main case
            have hUfin : eLpNorm u a Measure.count < ⊤ := lt_top_iff_ne_top.mpr hUt
            have hVfin : eLpNorm v b Measure.count < ⊤ := lt_top_iff_ne_top.mpr hVt
            have hKey : ∀ s : Finset ℤ,
                (∑ x ∈ s, ENNReal.ofReal (F x) ^ q.toReal) ^ (1 / q.toReal)
                  ≤ Cst * eLpNorm u a Measure.count * eLpNorm v b Measure.count := by
              intro s
              by_cases hs : s.Nonempty
              · set X : ENNReal := ∑ x ∈ s, ENNReal.ofReal (F x) ^ q.toReal with hXdef
                have hXfin : X < ⊤ := by
                  rw [hXdef]
                  exact ENNReal.sum_lt_top.mpr (fun x hx =>
                    ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
                by_cases hX0 : X = 0
                · rw [hX0, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hqR)]
                  exact zero_le
                · set W : ENNReal := X ^ (1 - (q⁻¹).toReal) with hWdef
                  have hWlt : W < ⊤ := by
                    rw [hWdef]
                    refine ENNReal.rpow_lt_top_of_nonneg ?_ (ne_of_lt hXfin)
                    have h1 : (q⁻¹).toReal ≤ 1 := by
                      rw [← ENNReal.toReal_one]
                      exact ENNReal.toReal_mono ENNReal.one_ne_top (ENNReal.inv_le_one.mpr hq_ge)
                    linarith
                  have hW0 : W ≠ 0 := by
                    rw [hWdef]
                    intro hz
                    rw [ENNReal.rpow_eq_zero_iff] at hz
                    rcases hz with ⟨hx, -⟩ | ⟨hx, -⟩
                    · exact hX0 hx
                    · exact (ne_of_lt hXfin) hx
                  set hfs : ℤ →₀ ℂ :=
                    ∑ y ∈ s, Finsupp.single y (((F y) ^ (q.toReal - 1) : ℝ) : ℂ) with hfsdef
                  have hfsval : ∀ x : ℤ, (hfs : ℤ → ℂ) x
                      = if x ∈ s then (((F x) ^ (q.toReal - 1) : ℝ) : ℂ) else 0 := by
                    intro x
                    rw [hfsdef, Finsupp.finsetSum_apply]
                    by_cases hx : x ∈ s
                    · rw [if_pos hx, Finset.sum_eq_single x]
                      · simp
                      · intro y _ hyx
                        rw [Finsupp.single_eq_of_ne (Ne.symm hyx)]
                      · intro hx'
                        exact absurd hx hx'
                    · rw [if_neg hx]
                      refine Finset.sum_eq_zero (fun y hy => ?_)
                      rw [Finsupp.single_eq_of_ne ?_]
                      rintro rfl
                      exact hx hy
                  have hfsfin : FinSupp (fun x : ℤ => (hfs x : ℂ)) :=
                    ⟨s, fun x hx => by
                      show (hfs : ℤ → ℂ) x = 0
                      rw [hfsval x, if_neg hx]⟩
                  obtain ⟨ψ, hψ1, hψ2⟩ := exists_test_psi hr K u v hfs
                  have hψ : ∀ (x : ℤ) (a : ℕ → ℂ),
                      ENNReal.ofReal ‖pair a (ψ x)‖
                        ≤ PointwiseErgodicTheorems.variationalNorm r a := hψ1
                  have hthree : ‖lam T ψ u v (fun x : ℤ => (hfs x : ℂ))‖ₑ
                      ≤ Cst * eLpNorm u a Measure.count * eLpNorm v b Measure.count * W := by
                    by_cases hq1 : q = 1
                    · have hq₀1 : q₀ = 1 := by
                        have h0 : 1 - (q⁻¹).toReal = 0 := by rw [hq1]; simp
                        have hs₀ : 1 - (q₀⁻¹).toReal = 0 := by
                          rw [h0] at hrelq
                          have h1 : (q₀⁻¹).toReal ≤ 1 := by
                            rw [← ENNReal.toReal_one]
                            exact ENNReal.toReal_mono ENNReal.one_ne_top
                              (ENNReal.inv_le_one.mpr hq₀)
                          have h2 : (q₁⁻¹).toReal ≤ 1 := by
                            rw [← ENNReal.toReal_one]
                            exact ENNReal.toReal_mono ENNReal.one_ne_top
                              (ENNReal.inv_le_one.mpr hq₁)
                          nlinarith [hrelq]
                        have h3 : (q₀⁻¹).toReal = 1 := by linarith
                        have h4 : q₀⁻¹ = 1 := by
                          rw [← ENNReal.ofReal_toReal (ENNReal.inv_ne_top.mpr hq₀0), h3,
                            ENNReal.ofReal_one]
                        rw [← inv_inv q₀, h4, inv_one]
                      have hq₁1 : q₁ = 1 := by
                        have h0 : 1 - (q⁻¹).toReal = 0 := by rw [hq1]; simp
                        have hs₁ : 1 - (q₁⁻¹).toReal = 0 := by
                          rw [h0] at hrelq
                          have h1 : (q₀⁻¹).toReal ≤ 1 := by
                            rw [← ENNReal.toReal_one]
                            exact ENNReal.toReal_mono ENNReal.one_ne_top
                              (ENNReal.inv_le_one.mpr hq₀)
                          have h2 : (q₁⁻¹).toReal ≤ 1 := by
                            rw [← ENNReal.toReal_one]
                            exact ENNReal.toReal_mono ENNReal.one_ne_top
                              (ENNReal.inv_le_one.mpr hq₁)
                          nlinarith [hrelq]
                        have h3 : (q₁⁻¹).toReal = 1 := by linarith
                        have h4 : q₁⁻¹ = 1 := by
                          rw [← ENNReal.ofReal_toReal (ENNReal.inv_ne_top.mpr hq₁0), h3,
                            ENNReal.ofReal_one]
                        rw [← inv_inv q₁, h4, inv_one]
                      have hW1 : W = 1 := by rw [hWdef, hq1]; simp
                      refine three_lines_bound (t₀ := 1) (t₁ := 1) (W := W) (q := q)
                        hlin₁ hlin₂ hr hθ₀ hθ₁ ha₀ ha₀f hb₀ hb₀f
                        ha₁ ha₁f hb₁ hb₁f hq₀ hq₀f hq₁ hq₁f hrela hrelb haf hbf ha_ge hb_ge
                        hT₀ hT₁ hψ hu hv hfsfin hUfin hU0 hVfin hV0 (by norm_num) (by norm_num)
                        (by ring) hWlt hW0 ?_ ?_
                      · intro z hz
                        rw [hW1, ENNReal.rpow_one, hq₀1, conjExp_one_eq,
                          show Work.Analysis.Interpolation.analyticFamily
                            (fun x : ℤ => (hfs x : ℂ)) (((1 : ℝ) : ℂ)) (((1 : ℝ) : ℂ)) z
                            = (fun x : ℤ => (hfs x : ℂ))
                            from Work.Analysis.Interpolation.analyticFamily_self (by push_cast; ring)]
                        rw [eLpNorm_exponent_top (hf := by pw_aesm)]
                        refine eLpNormEssSup_le_of_ae_enorm_bound ?_
                        filter_upwards with x
                        rw [hfsval x]
                        by_cases hx : x ∈ s
                        · rw [if_pos hx, hq1]
                          norm_num
                        · rw [if_neg hx]
                          simp
                      · intro z hz
                        rw [hW1, ENNReal.rpow_one, hq₁1, conjExp_one_eq,
                          show Work.Analysis.Interpolation.analyticFamily
                            (fun x : ℤ => (hfs x : ℂ)) (((1 : ℝ) : ℂ)) (((1 : ℝ) : ℂ)) z
                            = (fun x : ℤ => (hfs x : ℂ))
                            from Work.Analysis.Interpolation.analyticFamily_self (by push_cast; ring)]
                        rw [eLpNorm_exponent_top (hf := by pw_aesm)]
                        refine eLpNormEssSup_le_of_ae_enorm_bound ?_
                        filter_upwards with x
                        rw [hfsval x]
                        by_cases hx : x ∈ s
                        · rw [if_pos hx, hq1]
                          norm_num
                        · rw [if_neg hx]
                          simp
                    · have hq_gt : 1 < q := lt_of_le_of_ne hq_ge (Ne.symm hq1)
                      have hqR' : 1 < q.toReal := by
                        simpa using ENNReal.toReal_strict_mono (ne_of_lt hq_lt) hq_gt
                      set st : ℝ := 1 - (q⁻¹).toReal with hst
                      have hst_pos : 0 < st := by
                        rw [hst, ENNReal.toReal_inv]
                        have h3 : (q.toReal)⁻¹ < 1 := by
                          rw [← one_div, div_lt_one (by linarith : (0:ℝ) < q.toReal)]
                          exact hqR'
                        linarith
                      set t₀ : ℝ := (1 - (q₀⁻¹).toReal) / st with ht₀def
                      set t₁ : ℝ := (1 - (q₁⁻¹).toReal) / st with ht₁def
                      have ht₀nn : 0 ≤ t₀ := by
                        rw [ht₀def]
                        have h1 : (q₀⁻¹).toReal ≤ 1 := by
                          rw [← ENNReal.toReal_one]
                          exact ENNReal.toReal_mono ENNReal.one_ne_top
                            (ENNReal.inv_le_one.mpr hq₀)
                        exact div_nonneg (by linarith) (le_of_lt hst_pos)
                      have ht₁nn : 0 ≤ t₁ := by
                        rw [ht₁def]
                        have h1 : (q₁⁻¹).toReal ≤ 1 := by
                          rw [← ENNReal.toReal_one]
                          exact ENNReal.toReal_mono ENNReal.one_ne_top
                            (ENNReal.inv_le_one.mpr hq₁)
                        exact div_nonneg (by linarith) (le_of_lt hst_pos)
                      have ht_eq : (1 - θ) * t₀ + θ * t₁ = 1 := by
                        have hst_eq : (1 - θ) * (1 - (q₀⁻¹).toReal) + θ * (1 - (q₁⁻¹).toReal)
                            = st := by rw [hst]; exact hrelq.symm
                        have h1 : (1 - θ) * t₀ + θ * t₁
                            = ((1 - θ) * (1 - (q₀⁻¹).toReal) + θ * (1 - (q₁⁻¹).toReal)) / st := by
                          rw [ht₀def, ht₁def]; ring
                        rw [h1, hst_eq, div_self (ne_of_gt hst_pos)]
                      have hconjq : (conjExp q).toReal = st⁻¹ := by
                        rw [conjExp]
                        have h1 : ENNReal.ofReal st = 1 - q⁻¹ := by
                          rw [hst, ENNReal.ofReal_sub 1 ENNReal.toReal_nonneg,
                            ENNReal.ofReal_one,
                            ENNReal.ofReal_toReal (ENNReal.inv_ne_top.mpr hq0')]
                        rw [← h1, ← ENNReal.ofReal_inv_of_pos hst_pos,
                          ENNReal.toReal_ofReal (by positivity)]
                      have hconjq₀ : ((conjExp q₀)⁻¹).toReal = 1 - (q₀⁻¹).toReal := by
                        rw [conjExp, inv_inv,
                          ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.mpr hq₀)
                            ENNReal.one_ne_top,
                          ENNReal.toReal_one]
                      have hconjq₁ : ((conjExp q₁)⁻¹).toReal = 1 - (q₁⁻¹).toReal := by
                        rw [conjExp, inv_inv,
                          ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.mpr hq₁)
                            ENNReal.one_ne_top,
                          ENNReal.toReal_one]
                      have hle_base : eLpNorm (fun x : ℤ => (hfs x : ℂ)) (conjExp q) Measure.count ≤ W := by
                        rw [hWdef, hXdef]
                        simpa only [hfsdef] using
                          (finsupp_rpow_le (φ := F) hFnn hq_ge hq_lt s hs).1
                      have hbd₀ : ∀ z : ℂ, z.re = 0 →
                          eLpNorm (Work.Analysis.Interpolation.analyticFamily
                            (fun x : ℤ => (hfs x : ℂ)) ((t₀ : ℝ) : ℂ) ((t₁ : ℝ) : ℂ) z)
                            (conjExp q₀) Measure.count ≤ W ^ t₀ := by
                        intro z hz
                        have hP : 0 < (conjExp q).toReal := by rw [hconjq]; positivity
                        have ht' : t₀ = (conjExp q).toReal * ((conjExp q₀)⁻¹).toReal := by
                          rw [ht₀def, hconjq, hconjq₀]; ring
                        have h := Work.Analysis.Interpolation.eLpNorm_analyticFamily_re_zero_of (μ := Measure.count)
                          (f := fun x : ℤ => (hfs x : ℂ)) (P := (conjExp q).toReal)
                          (t := t₀) (t₁ := t₁) (s := conjExp q₀) (z := z) hP
                          (one_le_conjExp hq₀) ht' hz
                        rw [ENNReal.ofReal_toReal (ne_of_lt (conjExp_lt_top hq_gt))] at h
                        exact h.trans (ENNReal.rpow_le_rpow hle_base ht₀nn)
                      have hbd₁ : ∀ z : ℂ, z.re = 1 →
                          eLpNorm (Work.Analysis.Interpolation.analyticFamily
                            (fun x : ℤ => (hfs x : ℂ)) ((t₀ : ℝ) : ℂ) ((t₁ : ℝ) : ℂ) z)
                            (conjExp q₁) Measure.count ≤ W ^ t₁ := by
                        intro z hz
                        have hP : 0 < (conjExp q).toReal := by rw [hconjq]; positivity
                        have ht' : t₁ = (conjExp q).toReal * ((conjExp q₁)⁻¹).toReal := by
                          rw [ht₁def, hconjq, hconjq₁]; ring
                        have h := Work.Analysis.Interpolation.eLpNorm_analyticFamily_re_one_of (μ := Measure.count)
                          (f := fun x : ℤ => (hfs x : ℂ)) (P := (conjExp q).toReal)
                          (t₀ := t₀) (t := t₁) (s := conjExp q₁) (z := z) hP
                          (one_le_conjExp hq₁) ht' hz
                        rw [ENNReal.ofReal_toReal (ne_of_lt (conjExp_lt_top hq_gt))] at h
                        exact h.trans (ENNReal.rpow_le_rpow hle_base ht₁nn)
                      have hres := three_lines_bound (t₀ := t₀) (t₁ := t₁) (W := W) (q := q)
                        hlin₁ hlin₂ hr hθ₀ hθ₁ ha₀ ha₀f hb₀ hb₀f
                        ha₁ ha₁f hb₁ hb₁f hq₀ hq₀f hq₁ hq₁f hrela hrelb haf hbf ha_ge hb_ge
                        hT₀ hT₁ hψ hu hv hfsfin hUfin hU0 hVfin hV0 ht₀nn ht₁nn ht_eq hWlt hW0
                        hbd₀ hbd₁
                      simpa only [hCstdef] using hres
                  have hLHS : ‖lam T ψ u v (fun x : ℤ => (hfs x : ℂ))‖ₑ = X := by
                    have hsum : (∑ x ∈ hfs.support, vNormK r K (fun n : ℕ => T u v n x)
                        * ‖(hfs x : ℂ)‖ : ℝ) = ∑ x ∈ s, F x ^ q.toReal := by
                      have h1 : (∑ x ∈ hfs.support, vNormK r K (fun n : ℕ => T u v n x)
                          * ‖(hfs x : ℂ)‖ : ℝ)
                          = ∑ x ∈ hfs.support, F x * ‖(hfs x : ℂ)‖ :=
                        Finset.sum_congr rfl (fun x _ => by simp only [hFdef])
                      have h2 : (∑ x ∈ hfs.support, F x * ‖(hfs x : ℂ)‖ : ℝ)
                          = ∑ x ∈ s, F x * ‖(hfs x : ℂ)‖ := by
                        refine Finset.sum_subset ?_ ?_
                        · intro x hx
                          rw [Finsupp.mem_support_iff] at hx
                          by_contra hxs
                          exact hx (by rw [hfsval x, if_neg hxs])
                        · intro x hxs hxnot
                          rw [Finsupp.notMem_support_iff] at hxnot
                          rw [hxnot, norm_zero, mul_zero]
                      rw [h1, h2]
                      exact (finsupp_rpow_le (φ := F) hFnn hq_ge hq_lt s hs).2
                    rw [lam_test_psi K u v hfs ψ hψ2 hu hv hfsfin, hXdef, ← ofReal_norm]
                    rw [show ‖(((∑ x ∈ hfs.support, vNormK r K (fun n : ℕ => T u v n x)
                          * ‖(hfs x : ℂ)‖ : ℝ)) : ℂ)‖
                        = ((∑ x ∈ hfs.support, vNormK r K (fun n : ℕ => T u v n x)
                          * ‖(hfs x : ℂ)‖ : ℝ)) from
                      norm_ofReal_of_nonneg' _ (Finset.sum_nonneg (fun x _ =>
                        mul_nonneg (vNormK_nonneg r K _) (norm_nonneg _)))]
                    rw [hsum, ENNReal.ofReal_sum_of_nonneg (fun x _ =>
                      Real.rpow_nonneg (hFnn x) _)]
                    refine Finset.sum_congr rfl (fun x _ => ?_)
                    exact (ENNReal.ofReal_rpow_of_nonneg (hFnn x) (by positivity)).symm
                  rw [hLHS] at hthree
                  rw [hWdef] at hthree
                  exact rpow_le_of_le_mul_rpow hq_ge hq_lt hXfin hthree
              · rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.sum_empty]
                rw [show (0 : ENNReal) ^ (1 / q.toReal) = 0 from
                  ENNReal.zero_rpow_of_pos (one_div_pos.mpr hqR)]
                exact zero_le
            exact eLpNorm_ofReal_le_of_finset_rpow_le hFnn hq_ge hq_lt hKey

end Work.KMTAreas.A8
