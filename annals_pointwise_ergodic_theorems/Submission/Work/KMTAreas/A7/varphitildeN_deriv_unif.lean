/-
# The *uniform* derivative bound for the §6 bump `φ̃_N`

`varphitildeN_deriv_bound` proves, for each fixed pair `(N, k)`, the `C²`-bound

  `‖φ̃_N^{(j)}(x)‖ ≤ C(N,k) · 2^{-j d (k - Log N)}`,  `j ≤ 2`.

The point of *this* file is that the constant can be taken **independent of `N` and `k`**: the
proof of `varphitildeN_deriv_bound` already exhibits the explicit constant
`C = K·(1 + 2^{2d}) + 1`, where `K` bounds `η, η', η''` globally (possible because `η` vanishes off
`[-1,1]`) and depends only on `d`.  Here the whole family is handled at once, with the `∃ C`
hoisted outside the quantifiers over `N` and `k`.

The two ingredients are elementary:

* the `j`-th derivative of a dilation `ξ ↦ η (c ξ)` is `c^j · η^{(j)} (c ξ)`
  (`iteratedDeriv_comp_const_smul`), so it is bounded by `K c^j`;
* `φ̃_N` is a single dilation at the bottom scale `k = 0` (with `c = 2^{d·Log N}`, which is exactly
  `2^{-d (0 - Log N)}`) and a difference of two dilations at `k ≥ 1` (the second dilation carrying
  the factor `2^d`, hence the extra `2^{2d}` in the constant because `j ≤ 2`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.kmtEta_deriv_bounds
import Submission.Work.KMTAreas.A7.varphiNt_bounds

namespace Work.KMTAreas.A7

open Work.KMTContract

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary `2`-power algebra -/

/-- `C / 2 ^ (j * a) = C * (2 ^ (-a)) ^ j`. -/
private lemma div_rpow_two_mul_eq_unif (C a : ℝ) (j : ℕ) :
    C / (2 : ℝ) ^ (a * (j : ℝ)) = C * ((2 : ℝ) ^ (-a)) ^ j := by
  rw [div_eq_mul_inv, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) a, inv_pow,
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) a (j : ℝ), Real.rpow_natCast]

/-- `C / 2 ^ (j * a) = C * (2 ^ (-a)) ^ j`, with the product in the exponent written the other
way round. -/
private lemma div_rpow_two_mul_eq_unif' (C a : ℝ) (j : ℕ) :
    C / (2 : ℝ) ^ ((j : ℝ) * a) = C * ((2 : ℝ) ^ (-a)) ^ j := by
  rw [mul_comm (j : ℝ) a, div_rpow_two_mul_eq_unif]

/-! ## The chain rule for a dilation -/

/-- The `j`-th derivative of a dilation `ξ ↦ f (c ξ)` of a complex-valued `f`. -/
private lemma iteratedDeriv_comp_mul_apply_unif (f : ℝ → ℂ) (c x : ℝ) (j : ℕ)
    (h : ContDiff ℝ j f) :
    iteratedDeriv j (fun ξ : ℝ => f (c * ξ)) x = (c : ℂ) ^ j * iteratedDeriv j f (c * x) := by
  have h1 : iteratedDeriv j (fun ξ : ℝ => f (c * ξ)) x
      = (c ^ j : ℝ) • iteratedDeriv j f (c * x) :=
    congrFun (iteratedDeriv_comp_const_smul (𝕜 := ℝ) (F := ℂ) h c) x
  rw [h1, Complex.real_smul, Complex.ofReal_pow]

/-- The dilation gains the factor `c^j`, so its `j`-th derivative is bounded by `K c^j`. -/
private lemma iteratedDeriv_comp_mul_norm_le_unif (f : ℝ → ℂ) (c K : ℝ) (hc : 0 ≤ c)
    (hK : ∀ m : ℕ, m ≤ 2 → ∀ y : ℝ, ‖iteratedDeriv m f y‖ ≤ K)
    (hcd : ∀ m : ℕ, m ≤ 2 → ContDiff ℝ m f)
    (j : ℕ) (hj : j ≤ 2) (x : ℝ) :
    ‖iteratedDeriv j (fun ξ : ℝ => f (c * ξ)) x‖ ≤ K * c ^ j := by
  rw [iteratedDeriv_comp_mul_apply_unif f c x j (hcd j hj), norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hc, mul_comm K (c ^ j)]
  exact mul_le_mul_of_nonneg_left (hK j hj (c * x)) (pow_nonneg hc j)

/-! ## The uniform derivative bound -/

theorem varphitildeN_deriv_unif (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N k j : ℕ), j ≤ 2 → ∀ x : ℝ,
      ‖iteratedDeriv j (Work.KMTAreas.A7.varphitildeN d N k) x‖
        ≤ C / (2 : ℝ) ^ ((j : ℝ) * ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) := by
  have _ : 1 ≤ d := hd
  -- the `C²`-bounds on the cutoff `η`
  obtain ⟨M0, M1, M2, hM0, hM1, hM2, hcd, hb0, hb1, hb2, hz0, hz1, hz2, _hd, _hd2⟩ :=
    kmtEta_deriv_bounds
  set K : ℝ := max M0 (max M1 M2) with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; exact le_trans hM0 (le_max_left _ _)
  have hM0K : M0 ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hM1K : M1 ≤ K := by rw [hKdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hM2K : M2 ≤ K := by rw [hKdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  -- `η` and its first two derivatives are *globally* bounded by `K`: they vanish off `[-1,1]`
  have gb : ∀ m : ℕ, m ≤ 2 → ∀ y : ℝ, ‖iteratedDeriv m kmtEta y‖ ≤ K := by
    intro m hm y
    interval_cases m
    · rw [iteratedDeriv_zero]
      by_cases h : |y| ≤ 1
      · exact le_trans (hb0 y h) hM0K
      · rw [hz0 y (not_le.mp h).le, norm_zero]; exact hK0
    · rw [iteratedDeriv_one]
      by_cases h : |y| ≤ 1
      · exact le_trans (hb1 y h) hM1K
      · rw [hz1 y (not_le.mp h).le, norm_zero]; exact hK0
    · by_cases h : |y| ≤ 1
      · exact le_trans (hb2 y h) hM2K
      · rw [hz2 y (not_le.mp h).le, norm_zero]; exact hK0
  have hcd' : ∀ m : ℕ, m ≤ 2 → ContDiff ℝ m kmtEta := fun m hm =>
    hcd.of_le (by exact_mod_cast hm)
  -- the constant: `2^{d(Log N-k+1)} = 2^d · 2^{d(Log N-k)}`, so with `j ≤ 2` the second dilation
  -- contributes at most a further factor `2^{2d}`; note that it does **not** depend on `N` or `k`
  set Cfin : ℝ := K * (1 + (2 : ℝ) ^ (2 * d)) + 1 with hCdef
  have hT0 : 0 ≤ (2 : ℝ) ^ (2 * d) := by positivity
  have hCpos : 0 < Cfin := by
    rw [hCdef]; nlinarith [hT0, hK0]
  have hKC : K ≤ Cfin := by
    rw [hCdef]; nlinarith [hT0, mul_nonneg hK0 hT0]
  refine ⟨Cfin, hCpos, ?_⟩
  intro N k j hj x
  have hj' : (j : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hj
  rcases eq_or_ne k 0 with hk | hk
  · -- the bottom scale `k = 0`: `φ̃_N` is a single dilation
    subst hk
    simp only [Nat.cast_zero]
    set c : ℝ := (2 : ℝ) ^ ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) with hcdef
    have hc0 : 0 ≤ c := by rw [hcdef]; positivity
    have hf : varphitildeN d N 0 = fun ξ : ℝ => kmtEta (c * ξ) := by
      funext ξ
      rw [varphitildeN, if_pos rfl, hcdef]
    have hca : (2 : ℝ) ^ (-((d : ℝ) * ((0 : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) = c := by
      rw [hcdef]
      congr 1
      ring
    have hrhs : Cfin
          / (2 : ℝ) ^ ((j : ℝ) * ((d : ℝ) * ((0 : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))))
        = Cfin * c ^ j := by
      rw [div_rpow_two_mul_eq_unif' Cfin
        ((d : ℝ) * ((0 : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) j, hca]
    rw [hf, hrhs]
    calc ‖iteratedDeriv j (fun ξ : ℝ => kmtEta (c * ξ)) x‖ ≤ K * c ^ j :=
          iteratedDeriv_comp_mul_norm_le_unif kmtEta c K hc0 gb hcd' j hj x
      _ ≤ Cfin * c ^ j := mul_le_mul_of_nonneg_right hKC (pow_nonneg hc0 j)
  · -- a positive scale `k ≥ 1`: `φ̃_N` is the difference of two dilations
    set c0 : ℝ := (2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))
      with hc0def
    set c1 : ℝ :=
      (2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) with hc1def
    have hc00 : 0 ≤ c0 := by rw [hc0def]; positivity
    have hc10 : 0 ≤ c1 := by rw [hc1def]; positivity
    have hc1 : c1 = 2 ^ d * c0 := by
      rw [hc1def, hc0def]
      have hexp : (d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)
          = (d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) + (d : ℝ) := by ring
      rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
      ring
    have hf : varphitildeN d N k = fun ξ : ℝ => kmtEta (c0 * ξ) - kmtEta (c1 * ξ) := by
      funext ξ
      rw [varphitildeN, if_neg hk, ← hc0def, ← hc1def]
    have hca : (2 : ℝ) ^ (-((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) = c0 := by
      rw [hc0def]
      congr 1
      ring
    have hrhs : Cfin
          / (2 : ℝ) ^ ((j : ℝ) * ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))))
        = Cfin * c0 ^ j := by
      rw [div_rpow_two_mul_eq_unif' Cfin
        ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) j, hca]
    rw [hf, hrhs]
    have hcf : ContDiff ℝ 2 (fun ξ : ℝ => kmtEta (c0 * ξ)) :=
      hcd.comp (contDiff_const.mul contDiff_id)
    have hcg : ContDiff ℝ 2 (fun ξ : ℝ => kmtEta (c1 * ξ)) :=
      hcd.comp (contDiff_const.mul contDiff_id)
    have hsub : iteratedDeriv j (fun ξ : ℝ => kmtEta (c0 * ξ) - kmtEta (c1 * ξ)) x
        = iteratedDeriv j (fun ξ : ℝ => kmtEta (c0 * ξ)) x
          - iteratedDeriv j (fun ξ : ℝ => kmtEta (c1 * ξ)) x :=
      iteratedDeriv_sub (n := j) (x := x) (f := fun ξ : ℝ => kmtEta (c0 * ξ))
        (g := fun ξ : ℝ => kmtEta (c1 * ξ))
        (hcf.contDiffAt.of_le hj') (hcg.contDiffAt.of_le hj')
    rw [hsub]
    have hb0' := iteratedDeriv_comp_mul_norm_le_unif kmtEta c0 K hc00 gb hcd' j hj x
    have hb1' := iteratedDeriv_comp_mul_norm_le_unif kmtEta c1 K hc10 gb hcd' j hj x
    have hpow : c1 ^ j = ((2 : ℝ) ^ d) ^ j * c0 ^ j := by rw [hc1, mul_pow]
    have hdj : d * j ≤ 2 * d := by
      calc d * j ≤ d * 2 := Nat.mul_le_mul_left d hj
        _ = 2 * d := Nat.mul_comm d 2
    have hpj : ((2 : ℝ) ^ d) ^ j ≤ (2 : ℝ) ^ (2 * d) := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hdj
    have hc0j : 0 ≤ c0 ^ j := pow_nonneg hc00 j
    calc ‖iteratedDeriv j (fun ξ : ℝ => kmtEta (c0 * ξ)) x
            - iteratedDeriv j (fun ξ : ℝ => kmtEta (c1 * ξ)) x‖
        ≤ ‖iteratedDeriv j (fun ξ : ℝ => kmtEta (c0 * ξ)) x‖
            + ‖iteratedDeriv j (fun ξ : ℝ => kmtEta (c1 * ξ)) x‖ := norm_sub_le _ _
      _ ≤ K * c0 ^ j + K * c1 ^ j := add_le_add hb0' hb1'
      _ = K * c0 ^ j * (1 + ((2 : ℝ) ^ d) ^ j) := by rw [hpow]; ring
      _ ≤ K * c0 ^ j * (1 + (2 : ℝ) ^ (2 * d)) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK0 hc0j)
            linarith [hpj]
      _ ≤ Cfin * c0 ^ j := by
            rw [hCdef]
            nlinarith [hK0, hc0j, hT0, mul_nonneg hK0 hc0j]

end Work.KMTAreas.A7
