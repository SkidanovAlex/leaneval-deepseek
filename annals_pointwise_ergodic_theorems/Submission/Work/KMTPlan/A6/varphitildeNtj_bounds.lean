/-
# Bounds for the modified modulated bump `φ̃_{N,t,j}` (A6, §6/§8)

The paper's modified bump `φ̃_{N,t,j}(ξ) = (2^{-dk} N^d ξ)^j φ̃_{N,t}(ξ)` (KMT (tpntj)) is the
product of the modulated bump `φ̃_{N,t}` with a power of the frequency variable.  This file proves
that on `t ∈ [1/2,1]` it is `C²`, compactly supported, and that the integrals of its modulus and of
the modulus of its second derivative are bounded by a constant `S` independent of `t`.

The weight `ξ ↦ (c ξ)^j` is *singular* at `ξ = 0` when `j < 0`; the hypothesis `k ≠ 0 ∨ 0 ≤ j` of
the statement is exactly the case where this cannot happen, because for `k ≠ 0` the bump `φ̃_N` is a
*difference* of two rescalings of the flat-topped cutoff `η` and therefore vanishes identically on a
neighbourhood of the origin.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Tle_varphitildeNt_bounded
import Submission.Work.KMTPlan.A6.MdlKerVarphitildeNtj
import Submission.Work.KMTPlan.A6.natPow_mul_bounds

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped Topology

set_option maxHeartbeats 4000000

/-! ## 1.  Support, vanishing and integrability of the bump `φ̃_N` -/

/-- **Support of `φ̃_N`.**  A nonzero value forces `|ξ| ≤ 2^{d(k-Log N)}` (`d = P.natDegree`).

Both branches of the definition are rescalings `ξ ↦ η(2^{a} ξ)` of the cutoff `η`, whose support is
the unit ball; since the exponents of the two branches are `d(Log N - k)` and `d(Log N - k) + d`,
the smaller bound is the one coming from `d(Log N - k)`. -/
private lemma varphitildeN_ne_zero_abs_le (d N k : ℕ) {ξ : ℝ}
    (h : Work.KMTAreas.A7.varphitildeN d N k ξ ≠ 0) :
    |ξ| ≤ (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) := by
  have hd : (0:ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  by_cases hk : k = 0
  · subst hk
    rw [Work.KMTAreas.A7.varphitildeN, if_pos rfl] at h
    have hb := Work.KMTAreas.A7.abs_le_of_eta_rpow_ne_zero
      (L := (d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) (k := 0) (ξ := ξ)
      (by simpa using h)
    have hexp : ((0:ℕ):ℝ) - (d:ℝ) * (Work.Analysis.EndVar.logN N : ℝ) =
        (d:ℝ) * (((0:ℕ):ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by push_cast; ring
    rw [hexp] at hb
    simpa using hb
  · rw [Work.KMTAreas.A7.varphitildeN, if_neg hk] at h
    have hor : Work.KMTContract.kmtEta
          ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ξ) ≠ 0 ∨
        Work.KMTContract.kmtEta
          ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * ξ)
          ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h (by rw [hc.1, hc.2, sub_zero])
    rcases hor with h1 | h2
    · have hb := Work.KMTAreas.A7.abs_le_of_eta_rpow_ne_zero
        (L := (d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) (k := 0) (ξ := ξ)
        (by simpa using h1)
      have hexp : ((0:ℕ):ℝ) - (d:ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k:ℝ)) =
          (d:ℝ) * ((k:ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by push_cast; ring
      rw [hexp] at hb
      exact hb
    · have hb := Work.KMTAreas.A7.abs_le_of_eta_rpow_ne_zero
        (L := (d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) (k := 0) (ξ := ξ)
        (by simpa using h2)
      refine le_trans hb ?_
      apply (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr
      push_cast
      nlinarith [hd]

/-- **`φ̃_N` vanishes near the origin when `k ≠ 0`.**  Indeed, on the open ball of radius
`2^{-(d(Log N - k) + d + 1)}` both rescaled cutoffs of the difference are equal to `1`, because
the cutoff `η` is `1` on `[-1/2,1/2]`. -/
private lemma varphitildeN_eq_zero_of_abs_lt (d N k : ℕ) (hk : k ≠ 0) {ξ : ℝ}
    (h : |ξ| < (2:ℝ) ^ (-(d * ((Work.Analysis.EndVar.logN N : ℝ) - (k:ℝ)) + (d:ℝ) + 1))) :
    Work.KMTAreas.A7.varphitildeN d N k ξ = 0 := by
  rw [Work.KMTAreas.A7.varphitildeN, if_neg hk]
  have h2pos : (0:ℝ) < 2 := by norm_num
  have hone1 : Work.KMTContract.kmtEta
      ((2:ℝ) ^ ((d:ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k:ℝ))) * ξ) = 1 := by
    apply Work.KMTContract.kmtEta_one
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos h2pos _)]
    have hlt := mul_lt_mul_of_pos_left h
      (Real.rpow_pos_of_pos h2pos ((d:ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k:ℝ))))
    have hstep : (2:ℝ) ^ ((d:ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k:ℝ))) *
        (2:ℝ) ^ (-(d * ((Work.Analysis.EndVar.logN N : ℝ) - (k:ℝ)) + (d:ℝ) + 1)) =
        (2:ℝ) ^ (-((d:ℝ) + 1)) := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1; ring
    rw [hstep] at hlt
    have hle : (2:ℝ) ^ (-((d:ℝ) + 1)) ≤ 1/2 := by
      have h1 : -((d:ℝ) + 1) ≤ (-1:ℝ) := by
        have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
        linarith
      calc (2:ℝ) ^ (-((d:ℝ) + 1)) ≤ (2:ℝ) ^ (-1:ℝ) :=
            (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr h1
        _ = 1/2 := by norm_num [Real.rpow_neg_one]
    linarith [hle, hlt]
  have hone2 : Work.KMTContract.kmtEta
      ((2:ℝ) ^ ((d:ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k:ℝ) + 1)) * ξ) = 1 := by
    apply Work.KMTContract.kmtEta_one
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos h2pos _)]
    have hlt := mul_lt_mul_of_pos_left h
      (Real.rpow_pos_of_pos h2pos ((d:ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k:ℝ) + 1)))
    have hstep : (2:ℝ) ^ ((d:ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k:ℝ) + 1)) *
        (2:ℝ) ^ (-(d * ((Work.Analysis.EndVar.logN N : ℝ) - (k:ℝ)) + (d:ℝ) + 1)) =
        (2:ℝ) ^ (-1:ℝ) := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1; ring
    rw [hstep] at hlt
    have h2 : (2:ℝ) ^ (-1:ℝ) = 1/2 := by norm_num [Real.rpow_neg_one]
    rw [h2] at hlt
    exact le_of_lt hlt
  rw [hone1, hone2, sub_self]

/-- Compact support of the iterated derivatives of `φ̃_N`. -/
private lemma hcs_iteratedDeriv_varphitildeN (d N k m : ℕ) (hm : m ≤ 2) :
    HasCompactSupport (iteratedDeriv m (Work.KMTAreas.A7.varphitildeN d N k)) := by
  interval_cases m
  · rw [iteratedDeriv_zero]; exact Work.KMTAreas.A7.hasCompactSupport_varphitildeN d N k
  · rw [iteratedDeriv_one]; exact (Work.KMTAreas.A7.hasCompactSupport_varphitildeN d N k).deriv
  · rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact ((Work.KMTAreas.A7.hasCompactSupport_varphitildeN d N k).deriv).deriv

/-- Integrability of the modulus of the iterated derivatives of `φ̃_N` (up to order two). -/
private lemma integrable_iteratedDeriv_varphitildeN (d N k m : ℕ) (hm : m ≤ 2) :
    Integrable (fun y : ℝ => ‖iteratedDeriv m (Work.KMTAreas.A7.varphitildeN d N k) y‖) := by
  have hcont : Continuous (iteratedDeriv m (Work.KMTAreas.A7.varphitildeN d N k)) :=
    (Work.KMTAreas.A7.contDiff_varphitildeN d N k).continuous_iteratedDeriv m
      (by exact_mod_cast hm)
  exact (hcont.integrable_of_hasCompactSupport (hcs_iteratedDeriv_varphitildeN d N k m hm)).norm

/-! ## 2.  The weight `ξ ↦ (c ξ)^j` and its derivatives -/

/-- Pulling a constant out of an iterated derivative (real valued). -/
private lemma iteratedDeriv_const_mul_real (K : ℝ) (f : ℝ → ℝ) (k : ℕ) :
    iteratedDeriv k (fun x : ℝ => K * f x) = fun x => K * iteratedDeriv k f x := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    funext x
    rw [deriv_const_mul_field]

/-- **Differentiation commutes with the inclusion `ℝ → ℂ`** (function level). -/
private lemma deriv_ofReal_comp (H : ℝ → ℝ) :
    deriv (fun ξ : ℝ => ((H ξ : ℝ) : ℂ)) = fun ξ => ((deriv H ξ : ℝ) : ℂ) := by
  funext ξ
  by_cases h : DifferentiableAt ℝ H ξ
  · exact (h.hasDerivAt.ofReal_comp).deriv
  · rw [deriv_zero_of_not_differentiableAt h]
    have h' : ¬ DifferentiableAt ℝ (fun ξ : ℝ => ((H ξ : ℝ) : ℂ)) ξ := fun hc =>
      h ((Complex.reCLM.differentiableAt.comp ξ hc).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => by simp))
    rw [deriv_zero_of_not_differentiableAt h']
    simp

/-- **Differentiation commutes with the inclusion `ℝ → ℂ`** (iterated, function level). -/
private lemma iteratedDeriv_ofReal_comp_fun (f : ℝ → ℝ) (n : ℕ) :
    iteratedDeriv n (fun ξ : ℝ => ((f ξ : ℝ) : ℂ)) = fun ξ => ((iteratedDeriv n f ξ : ℝ) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, deriv_ofReal_comp]
    simp only [iteratedDeriv_succ]

/-- **Differentiation commutes with the inclusion `ℝ → ℂ`** (pointwise). -/
private lemma iteratedDeriv_ofReal_comp (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun ξ : ℝ => ((f ξ : ℝ) : ℂ)) x = ((iteratedDeriv n f x : ℝ) : ℂ) :=
  congr_fun (iteratedDeriv_ofReal_comp_fun f n) x

/-- The `k`-th derivative of `x ↦ K x^j`, in closed form. -/
private lemma iteratedDeriv_zpow_const_mul (K : ℝ) (j : ℤ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun ξ : ℝ => K * ξ ^ j) x =
      K * ((∏ i ∈ Finset.range k, ((j : ℝ) - (i : ℝ))) * x ^ (j - (k : ℤ))) := by
  rw [iteratedDeriv_const_mul_real]
  simpa [iteratedDeriv_eq_iterate] using iter_deriv_zpow j x k

/-- **The `k`-th derivative of the weight `ξ ↦ (c ξ)^j`**, in closed form (valid for every
`ξ : ℝ`, including the origin, by the convention on `zpow`). -/
private lemma iteratedDeriv_zpow_comp_C (c : ℝ) (j : ℤ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x =
      ((((c ^ j) * ((∏ i ∈ Finset.range k, ((j : ℝ) - (i : ℝ))) * x ^ (j - (k : ℤ))) : ℝ)) : ℂ) := by
  have hfun : (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) =
      fun ξ : ℝ => (((c * ξ) ^ j : ℝ) : ℂ) := by
    funext ξ; exact (Complex.ofReal_zpow (c * ξ) j).symm
  have h1 : iteratedDeriv k (fun ξ : ℝ => (((c * ξ) ^ j : ℝ) : ℂ)) x
      = ((iteratedDeriv k (fun ξ : ℝ => (c * ξ) ^ j) x : ℝ) : ℂ) :=
    iteratedDeriv_ofReal_comp _ k x
  have h2 : iteratedDeriv k (fun ξ : ℝ => (c * ξ) ^ j) x =
      c ^ j * ((∏ i ∈ Finset.range k, ((j : ℝ) - (i : ℝ))) * x ^ (j - (k : ℤ))) := by
    rw [show (fun ξ : ℝ => (c * ξ) ^ j) = fun ξ : ℝ => c ^ j * ξ ^ j from
      funext fun ξ => (Commute.all c ξ).mul_zpow j]
    exact iteratedDeriv_zpow_const_mul (c ^ j) j k x
  rw [hfun, h1, h2]

/-- The `j`-th power of a nonzero real number is `C²` at that point. -/
private lemma contDiffAt_zpow_real (j : ℤ) {y : ℝ} (hy : y ≠ 0) :
    ContDiffAt ℝ 2 (fun y : ℝ => y ^ j) y := by
  by_cases hj : 0 ≤ j
  · have hje : j = ((j.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hj).symm
    have : (fun y : ℝ => y ^ j) = fun y : ℝ => y ^ j.toNat := by
      funext y
      rw [hje, zpow_natCast, Int.toNat_natCast]
    rw [this]
    exact contDiffAt_id.pow _
  · have hj' : j < 0 := lt_of_not_ge hj
    have hje : j = -(((-j).toNat : ℕ) : ℤ) := by
      have h2 : (((-j).toNat : ℕ) : ℤ) = -j := Int.toNat_of_nonneg (by omega)
      omega
    have : (fun y : ℝ => y ^ j) = fun y : ℝ => (y ^ (-j).toNat)⁻¹ := by
      funext y
      rw [hje, zpow_neg, zpow_natCast, neg_neg, Int.toNat_natCast]
    rw [this]
    refine (contDiffAt_id.pow _).inv ?_
    exact pow_ne_zero _ hy

/-- **The weight `ξ ↦ (c ξ)^j` is `C²` at `ξ` whenever `c = 0` or `c ξ ≠ 0`** (if `c = 0` it is a
constant). -/
private lemma contDiffAt_weight (c : ℝ) (j : ℤ) {x : ℝ} (hx : c = 0 ∨ c * x ≠ 0) :
    ContDiffAt ℝ 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x := by
  rcases hx with rfl | hx
  · rcases eq_or_ne j 0 with hj | hj
    · subst hj
      have : (fun ξ : ℝ => (((0:ℝ) * ξ : ℝ) : ℂ) ^ (0:ℤ)) = fun _ : ℝ => (1:ℂ) := by
        funext ξ; simp
      rw [this]
      exact contDiffAt_const
    · have : (fun ξ : ℝ => (((0:ℝ) * ξ : ℝ) : ℂ) ^ j) = fun _ : ℝ => (0:ℂ) := by
        funext ξ; simp [zero_zpow j hj]
      rw [this]
      exact contDiffAt_const
  · have hφ : ContDiffAt ℝ 2 (fun ξ : ℝ => c * ξ) x := contDiffAt_const.mul contDiffAt_id
    have hB : ContDiffAt ℝ 2 (fun y : ℝ => y ^ j) (c * x) := contDiffAt_zpow_real j hx
    have h1 : ContDiffAt ℝ 2 (fun ξ : ℝ => (c * ξ) ^ j) x := hB.comp x hφ
    have h2 : ContDiffAt ℝ 2 (fun ξ : ℝ => (((c * ξ) ^ j : ℝ) : ℂ)) x :=
      (Complex.ofRealCLM.contDiff.contDiffAt).comp x h1
    refine h2.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun ξ => (Complex.ofReal_zpow (c * ξ) j).symm


/-! ## 3.  The engine for a negative exponent -/

/-- Leibniz' rule at order one. -/
private lemma iteratedDeriv_one_mul (f g : ℝ → ℂ) (x : ℝ)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    iteratedDeriv 1 (f * g) x = f x * iteratedDeriv 1 g x + iteratedDeriv 1 f x * g x := by
  rw [iteratedDeriv_mul (n := 1) (hf.of_le (by norm_num)) (hg.of_le (by norm_num))]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    Nat.choose_one_right, iteratedDeriv_zero, Nat.reduceSub, Nat.cast_one, one_mul]
  ring

/-- A function vanishing identically near a point has vanishing iterated derivatives there. -/
private lemma iteratedDeriv_eq_zero_of_eventuallyEq_zero {f : ℝ → ℂ} {x : ℝ}
    (h : f =ᶠ[𝓝 x] 0) (k : ℕ) : iteratedDeriv k f x = 0 := by
  rw [Filter.EventuallyEq.iteratedDeriv_eq k h]
  simp

/-- **The engine**: if `u` is `C²` with compact support, vanishes on the open ball of radius
`δ > 0` about the origin and outside `[-R,R]`, then for every `c ≠ 0` and every `j < 0` the product
`ξ ↦ (c ξ)^j u(ξ)` is `C²` with compact support, and it and its first two derivatives are
dominated by the corresponding derivatives of `u`. -/
private lemma weight_zpow_bounds (u : ℝ → ℂ) (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R)
    (hin : ∀ ξ : ℝ, |ξ| < δ → u ξ = 0) (hout : ∀ ξ : ℝ, R < |ξ| → u ξ = 0)
    (c : ℝ) (hc : c ≠ 0) (j : ℤ) (hj : j < 0) :
    ContDiff ℝ 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j * u ξ) ∧
    HasCompactSupport (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j * u ξ) ∧
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ ξ : ℝ, ‖((c * ξ : ℝ) : ℂ) ^ j * u ξ‖ ≤ K * ‖u ξ‖) ∧
      (∀ ξ : ℝ, ‖iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j * u ξ) ξ‖ ≤
        K * (‖u ξ‖ + ‖iteratedDeriv 1 u ξ‖)) ∧
      (∀ ξ : ℝ, ‖iteratedDeriv 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j * u ξ) ξ‖ ≤
        K * (‖u ξ‖ + ‖iteratedDeriv 1 u ξ‖ + ‖iteratedDeriv 2 u ξ‖)) := by
  set A : ℝ → ℂ := fun ξ => ((c * ξ : ℝ) : ℂ) ^ j with hAd
  have hAcd : ∀ x : ℝ, x ≠ 0 → ContDiffAt ℝ 2 A x := by
    intro x hx
    rw [hAd]
    exact contDiffAt_weight c j (Or.inr (mul_ne_zero hc hx))
  have hevsmall : ∀ x : ℝ, |x| < δ →
      (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j * u ξ) =ᶠ[𝓝 x] 0 := by
    intro x hx
    filter_upwards [isOpen_lt continuous_abs continuous_const |>.mem_nhds hx] with y hy
    simp [hin y hy]
  have hevbig : ∀ x : ℝ, R < |x| →
      (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j * u ξ) =ᶠ[𝓝 x] 0 := by
    intro x hx
    filter_upwards [isOpen_lt continuous_const continuous_abs |>.mem_nhds hx] with y hy
    simp [hout y hy]
  have hzero : ∀ x : ℝ, (|x| < δ ∨ R < |x|) → ∀ k : ℕ,
      iteratedDeriv k (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j * u ξ) x = 0 := by
    intro x hx k
    rcases hx with hx | hx
    · exact iteratedDeriv_eq_zero_of_eventuallyEq_zero (hevsmall x hx) k
    · exact iteratedDeriv_eq_zero_of_eventuallyEq_zero (hevbig x hx) k
  have hcd : ContDiff ℝ 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j * u ξ) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : |x| < δ
    · exact contDiffAt_const.congr_of_eventuallyEq (hevsmall x hx)
    · have hxδ : δ ≤ |x| := le_of_not_gt hx
      have hx0 : x ≠ 0 := by
        intro h; rw [h, abs_zero] at hxδ; linarith
      exact (hAcd x hx0).mul hu.contDiffAt
  set s : Set ℝ := {x : ℝ | δ ≤ |x| ∧ |x| ≤ R} with hs
  have hscomp : IsCompact s := by
    have h1 : s = Set.Icc (-R) R ∩ {x : ℝ | δ ≤ |x|} := by
      rw [hs]
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨abs_le.mp h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, abs_le.mpr h1⟩
    rw [h1]
    exact isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hAfun : ∀ k : ℕ,
      (fun x : ℝ => iteratedDeriv k (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x) =
      fun x : ℝ => ((((c ^ j) * ((∏ i ∈ Finset.range k, ((j : ℝ) - (i : ℝ)))
        * x ^ (j - (k : ℤ))) : ℝ)) : ℂ) := by
    intro k
    funext x
    exact iteratedDeriv_zpow_comp_C c j k x
  have hcont (k : ℕ) :
      ContinuousOn (fun x : ℝ => ‖iteratedDeriv k (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x‖)
        s := by
    have hfun : (fun x : ℝ => ‖iteratedDeriv k (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x‖) =
        fun x : ℝ => ‖((((c ^ j) * ((∏ i ∈ Finset.range k, ((j : ℝ) - (i : ℝ)))
          * x ^ (j - (k : ℤ))) : ℝ)) : ℂ)‖ := by
      funext x
      simp only [hAfun k]
    rw [hfun]
    intro x hx
    have hxδ : δ ≤ |x| := hx.1
    have hx0 : x ≠ 0 := by
      intro h; rw [h, abs_zero] at hxδ; linarith
    have h1 : ContinuousAt (fun y : ℝ => (c ^ j) *
        ((∏ i ∈ Finset.range k, ((j : ℝ) - (i : ℝ))) * y ^ (j - (k : ℤ)))) x :=
      continuousAt_const.mul (continuousAt_const.mul
        (continuousAt_zpow₀ x (j - (k : ℤ)) (Or.inl hx0)))
    exact ((Complex.continuous_ofReal.continuousAt.comp h1).norm).continuousWithinAt
  obtain ⟨K₀, hK₀⟩ := hscomp.exists_bound_of_continuousOn (hcont 0)
  obtain ⟨K₁, hK₁⟩ := hscomp.exists_bound_of_continuousOn (hcont 1)
  obtain ⟨K₂, hK₂⟩ := hscomp.exists_bound_of_continuousOn (hcont 2)
  set C : ℝ := |K₀| + |K₁| + |K₂| with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have hC0' : K₀ ≤ C := by
    rw [hCdef]; linarith [le_abs_self K₀, abs_nonneg K₁, abs_nonneg K₂]
  have hC1' : K₁ ≤ C := by
    rw [hCdef]; linarith [le_abs_self K₁, abs_nonneg K₀, abs_nonneg K₂]
  have hC2' : K₂ ≤ C := by
    rw [hCdef]; linarith [le_abs_self K₂, abs_nonneg K₀, abs_nonneg K₁]
  have hCle : ∀ k : ℕ, k ≤ 2 → ∀ x : ℝ, δ ≤ |x| → |x| ≤ R →
      ‖iteratedDeriv k (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x‖ ≤ C := by
    intro k hk x hx1 hx2
    have hx : x ∈ s := ⟨hx1, hx2⟩
    interval_cases k
    · exact le_trans (by simpa using hK₀ x hx) hC0'
    · exact le_trans (by simpa using hK₁ x hx) hC1'
    · exact le_trans (by simpa using hK₂ x hx) hC2'
  have hKmem : ∀ x : ℝ, ¬(δ ≤ |x| ∧ |x| ≤ R) → |x| < δ ∨ R < |x| := by
    intro x hx
    by_contra h
    push Not at h
    exact hx h
  refine ⟨hcd, hcs.mul_left, max 1 (3 * (C + 1)), le_trans zero_le_one (le_max_left 1 _),
    ?_, ?_, ?_⟩
  · intro x
    by_cases hx : δ ≤ |x| ∧ |x| ≤ R
    · have h1 : ‖((c * x : ℝ) : ℂ) ^ j‖ ≤ C := hCle 0 (by norm_num) x hx.1 hx.2
      have hK : C ≤ max 1 (3 * (C + 1)) := by
        have := le_max_right 1 (3 * (C + 1)); linarith
      calc ‖((c * x : ℝ) : ℂ) ^ j * u x‖ = ‖((c * x : ℝ) : ℂ) ^ j‖ * ‖u x‖ := norm_mul _ _
        _ ≤ C * ‖u x‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ max 1 (3 * (C + 1)) * ‖u x‖ := mul_le_mul_of_nonneg_right hK (norm_nonneg _)
    · have hz : ((c * x : ℝ) : ℂ) ^ j * u x = 0 := by
        simpa using hzero x (hKmem x hx) 0
      rw [hz]
      simp
  · intro x
    by_cases hx : δ ≤ |x| ∧ |x| ≤ R
    · have hx0 : x ≠ 0 := by
        intro h; rw [h, abs_zero] at hx; linarith [hx.1]
      have hAx : ContDiffAt ℝ 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x := hAcd x hx0
      have hkey := iteratedDeriv_one_mul (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) u x hAx
        hu.contDiffAt
      have h0 : ‖((c * x : ℝ) : ℂ) ^ j‖ ≤ C := hCle 0 (by norm_num) x hx.1 hx.2
      have h1 := hCle 1 (by norm_num) x hx.1 hx.2
      have hK : 2 * C ≤ max 1 (3 * (C + 1)) := by
        have := le_max_right 1 (3 * (C + 1)); linarith
      have hu0 : (0:ℝ) ≤ ‖u x‖ := norm_nonneg _
      have hu1 : (0:ℝ) ≤ ‖iteratedDeriv 1 u x‖ := norm_nonneg _
      rw [show iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j * u ξ) x
            = ((c * x : ℝ) : ℂ) ^ j * iteratedDeriv 1 u x
              + iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x * u x from hkey]
      calc ‖((c * x : ℝ) : ℂ) ^ j * iteratedDeriv 1 u x
              + iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x * u x‖
          ≤ ‖((c * x : ℝ) : ℂ) ^ j * iteratedDeriv 1 u x‖
              + ‖iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x * u x‖ := norm_add_le _ _
        _ = ‖((c * x : ℝ) : ℂ) ^ j‖ * ‖iteratedDeriv 1 u x‖
              + ‖iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x‖ * ‖u x‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ C * ‖iteratedDeriv 1 u x‖ + C * ‖u x‖ := by
            linarith [mul_le_mul_of_nonneg_right h0 hu1,
              mul_le_mul_of_nonneg_right h1 hu0]
        _ ≤ max 1 (3 * (C + 1)) * (‖u x‖ + ‖iteratedDeriv 1 u x‖) := by
            have hCK : C ≤ max 1 (3 * (C + 1)) := by
              have := le_max_right 1 (3 * (C + 1)); linarith
            nlinarith [hCK, hu0, hu1]
    · have hz : iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j * u ξ) x = 0 :=
        hzero x (hKmem x hx) 1
      rw [hz] <;> simp <;> positivity
  · intro x
    by_cases hx : δ ≤ |x| ∧ |x| ≤ R
    · have hx0 : x ≠ 0 := by
        intro h; rw [h, abs_zero] at hx; linarith [hx.1]
      have hAx : ContDiffAt ℝ 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x := hAcd x hx0
      have hkey := Work.KMTAreas.A7.iteratedDeriv_two_mul
        (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) u x hAx hu.contDiffAt
      have h0 : ‖((c * x : ℝ) : ℂ) ^ j‖ ≤ C := hCle 0 (by norm_num) x hx.1 hx.2
      have h1 : ‖iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x‖ ≤ C :=
        hCle 1 (by norm_num) x hx.1 hx.2
      have h2 : ‖iteratedDeriv 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x‖ ≤ C := by
        simpa using hCle 2 (by norm_num) x hx.1 hx.2
      have hK : 3 * C ≤ max 1 (3 * (C + 1)) := by
        have := le_max_right 1 (3 * (C + 1)); linarith
      have hu0 : (0:ℝ) ≤ ‖u x‖ := norm_nonneg _
      have hu1 : (0:ℝ) ≤ ‖iteratedDeriv 1 u x‖ := norm_nonneg _
      have hu2 : (0:ℝ) ≤ ‖iteratedDeriv 2 u x‖ := norm_nonneg _
      have t1 : ‖iteratedDeriv 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x * u x‖
          ≤ C * ‖u x‖ := by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right h2 hu0
      have t2 : ‖2 * (iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x
            * iteratedDeriv 1 u x)‖ ≤ 2 * C * ‖iteratedDeriv 1 u x‖ := by
        rw [norm_mul, Complex.norm_ofNat, norm_mul]
        nlinarith [mul_le_mul_of_nonneg_right h1 hu1]
      have t3 : ‖((c * x : ℝ) : ℂ) ^ j * iteratedDeriv 2 u x‖ ≤ C * ‖iteratedDeriv 2 u x‖ := by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right h0 hu2
      rw [show iteratedDeriv 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j * u ξ) x
            = iteratedDeriv 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x * u x
              + 2 * (iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x
                * iteratedDeriv 1 u x)
              + ((c * x : ℝ) : ℂ) ^ j * iteratedDeriv 2 u x from hkey]
      calc ‖iteratedDeriv 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x * u x
              + 2 * (iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x
                * iteratedDeriv 1 u x)
              + ((c * x : ℝ) : ℂ) ^ j * iteratedDeriv 2 u x‖
          ≤ ‖iteratedDeriv 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x * u x
              + 2 * (iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x
                * iteratedDeriv 1 u x)‖
              + ‖((c * x : ℝ) : ℂ) ^ j * iteratedDeriv 2 u x‖ := norm_add_le _ _
        _ ≤ (‖iteratedDeriv 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x * u x‖
              + ‖2 * (iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x
                * iteratedDeriv 1 u x)‖)
              + ‖((c * x : ℝ) : ℂ) ^ j * iteratedDeriv 2 u x‖ := by
            have := norm_add_le (iteratedDeriv 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x * u x)
              (2 * (iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j) x * iteratedDeriv 1 u x))
            linarith
        _ ≤ max 1 (3 * (C + 1)) * (‖u x‖ + ‖iteratedDeriv 1 u x‖ + ‖iteratedDeriv 2 u x‖) := by
            have hCK : C ≤ max 1 (3 * (C + 1)) := by
              have := le_max_right 1 (3 * (C + 1)); linarith
            nlinarith [t1, t2, t3, hCK, hu0, hu1, hu2]
    · have hz : iteratedDeriv 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j * u ξ) x = 0 :=
        hzero x (hKmem x hx) 2
      rw [hz] <;> simp <;> positivity

/-! ## 4.  From pointwise bounds to integral bounds -/

private lemma mod_bounds (U : ℝ → ℂ) (hUcd : ContDiff ℝ 2 U) (hUcs : HasCompactSupport U)
    (G : ℝ → ℂ) (hGcd : ContDiff ℝ 2 G) (hGcs : HasCompactSupport G)
    {K : ℝ} (hK : 0 ≤ K)
    (hb0 : ∀ ξ : ℝ, ‖G ξ‖ ≤ K * ‖U ξ‖)
    (hb1 : ∀ ξ : ℝ, ‖iteratedDeriv 1 G ξ‖ ≤ K * (‖U ξ‖ + ‖iteratedDeriv 1 U ξ‖))
    (hb2 : ∀ ξ : ℝ, ‖iteratedDeriv 2 G ξ‖ ≤
      K * (‖U ξ‖ + ‖iteratedDeriv 1 U ξ‖ + ‖iteratedDeriv 2 U ξ‖))
    (hint : ∀ m : ℕ, m ≤ 2 → Integrable (fun ξ : ℝ => ‖iteratedDeriv m U ξ‖))
    (M : ℝ) (hM : 0 ≤ M) (cc : ℝ) (hcc : |cc| ≤ M) :
    (∫ ξ, ‖G ξ * Work.KMTAreas.A7.ee (cc * ξ)‖
        ≤ K * (1 + (1 + 2 * Real.pi * M)) ^ 2 *
          ((∫ ξ, ‖U ξ‖) + (∫ ξ, ‖iteratedDeriv 1 U ξ‖) + (∫ ξ, ‖iteratedDeriv 2 U ξ‖))) ∧
    (∫ ξ, ‖iteratedDeriv 2 (G * fun ξ => Work.KMTAreas.A7.ee (cc * ξ)) ξ‖
        ≤ K * (1 + (1 + 2 * Real.pi * M)) ^ 2 *
          ((∫ ξ, ‖U ξ‖) + (∫ ξ, ‖iteratedDeriv 1 U ξ‖) + (∫ ξ, ‖iteratedDeriv 2 U ξ‖))) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hC0 : (0:ℝ) ≤ 2 * Real.pi * M := by positivity
  have hcm : 2 * Real.pi * |cc| ≤ 2 * Real.pi * M := by
    have := abs_nonneg cc
    nlinarith
  set C : ℝ := 1 + 2 * Real.pi * M with hC
  have hC0' : (0:ℝ) ≤ C := by rw [hC]; linarith
  have hone : (1:ℝ) ≤ (1 + C) ^ 2 := by
    have hc : (0:ℝ) ≤ C := hC0'
    nlinarith [sq_nonneg C]
  have hI0 : Integrable (fun ξ : ℝ => ‖U ξ‖) := hint 0 (by norm_num)
  have hI1 : Integrable (fun ξ : ℝ => ‖iteratedDeriv 1 U ξ‖) := hint 1 (by norm_num)
  have hI2 : Integrable (fun ξ : ℝ => ‖iteratedDeriv 2 U ξ‖) := hint 2 le_rfl
  set D : ℝ → ℝ := fun ξ => ‖U ξ‖ + ‖iteratedDeriv 1 U ξ‖ + ‖iteratedDeriv 2 U ξ‖ with hD
  have hDint : (∫ ξ, D ξ) = (∫ ξ, ‖U ξ‖) + (∫ ξ, ‖iteratedDeriv 1 U ξ‖)
      + (∫ ξ, ‖iteratedDeriv 2 U ξ‖) := by
    have h1 : Integrable (fun ξ : ℝ => ‖U ξ‖ + ‖iteratedDeriv 1 U ξ‖) := hI0.add hI1
    have e1 : (∫ ξ, (‖U ξ‖ + ‖iteratedDeriv 1 U ξ‖ + ‖iteratedDeriv 2 U ξ‖))
        = (∫ ξ, ‖U ξ‖ + ‖iteratedDeriv 1 U ξ‖) + (∫ ξ, ‖iteratedDeriv 2 U ξ‖) :=
      integral_add h1 hI2
    have e2 : (∫ ξ, ‖U ξ‖ + ‖iteratedDeriv 1 U ξ‖)
        = (∫ ξ, ‖U ξ‖) + (∫ ξ, ‖iteratedDeriv 1 U ξ‖) :=
      integral_add hI0 hI1
    simp only [hD]
    rw [e1, e2]
  have hDnn : (0:ℝ) ≤ ∫ ξ, D ξ := by
    rw [hDint]
    have h1 : (0:ℝ) ≤ ∫ ξ, ‖U ξ‖ := integral_nonneg (fun ξ => norm_nonneg _)
    have h2 : (0:ℝ) ≤ ∫ ξ, ‖iteratedDeriv 1 U ξ‖ := integral_nonneg (fun ξ => norm_nonneg _)
    have h3 : (0:ℝ) ≤ ∫ ξ, ‖iteratedDeriv 2 U ξ‖ := integral_nonneg (fun ξ => norm_nonneg _)
    linarith
  have hIntD : Integrable D := by
    have h1 : Integrable (fun ξ : ℝ => ‖U ξ‖ + ‖iteratedDeriv 1 U ξ‖) := hI0.add hI1
    have h2 : Integrable (fun ξ : ℝ => ‖U ξ‖ + ‖iteratedDeriv 1 U ξ‖ + ‖iteratedDeriv 2 U ξ‖) :=
      h1.add hI2
    simpa only [hD] using h2
  have hpt1 : ∀ ξ : ℝ, ‖G ξ * Work.KMTAreas.A7.ee (cc * ξ)‖ ≤ K * D ξ := by
    intro ξ
    rw [norm_mul, Work.KMTAreas.A7.norm_ee, mul_one]
    have hb := hb0 ξ
    have hd : D ξ = ‖U ξ‖ + ‖iteratedDeriv 1 U ξ‖ + ‖iteratedDeriv 2 U ξ‖ := rfl
    rw [hd]
    have h3 : (0:ℝ) ≤ ‖iteratedDeriv 1 U ξ‖ := norm_nonneg _
    have h4 : (0:ℝ) ≤ ‖iteratedDeriv 2 U ξ‖ := norm_nonneg _
    nlinarith
  have hpt2 : ∀ ξ : ℝ,
      ‖iteratedDeriv 2 (G * fun ξ => Work.KMTAreas.A7.ee (cc * ξ)) ξ‖ ≤ (1 + C) ^ 2 * (K * D ξ) := by
    intro ξ
    have h := Work.KMTAreas.A7.norm_iteratedDeriv_two_mul_ee_le G cc hGcd ξ
    have h0 := hb0 ξ
    have h1 := hb1 ξ
    have h2 := hb2 ξ
    have hd : D ξ = ‖U ξ‖ + ‖iteratedDeriv 1 U ξ‖ + ‖iteratedDeriv 2 U ξ‖ := rfl
    have hu0 : (0:ℝ) ≤ ‖U ξ‖ := norm_nonneg _
    have hu1 : (0:ℝ) ≤ ‖iteratedDeriv 1 U ξ‖ := norm_nonneg _
    have hu2 : (0:ℝ) ≤ ‖iteratedDeriv 2 U ξ‖ := norm_nonneg _
    have hco : 2 * (2 * Real.pi * |cc|) ≤ 2 * C := by rw [hC]; linarith [hcm]
    have hco2 : (2 * Real.pi * |cc|) ^ 2 ≤ C ^ 2 := by
      have h1' : (0:ℝ) ≤ 2 * Real.pi * |cc| := by positivity
      nlinarith [hcm, hC0', h1']
    have hA : 2 * (2 * Real.pi * |cc|) * ‖iteratedDeriv 1 G ξ‖ ≤
        2 * C * (K * (‖U ξ‖ + ‖iteratedDeriv 1 U ξ‖)) :=
      mul_le_mul hco h1 (norm_nonneg _) (by positivity)
    have hB : (2 * Real.pi * |cc|) ^ 2 * ‖G ξ‖ ≤ C ^ 2 * (K * ‖U ξ‖) :=
      mul_le_mul hco2 h0 (norm_nonneg _) (by positivity)
    have hDge : ‖U ξ‖ + ‖iteratedDeriv 1 U ξ‖ ≤ D ξ := by
      rw [hd]; linarith
    have hDge' : ‖U ξ‖ ≤ D ξ := by
      rw [hd]; linarith
    have hA' : 2 * C * (K * (‖U ξ‖ + ‖iteratedDeriv 1 U ξ‖)) ≤ 2 * C * (K * D ξ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDge hK)
        (by nlinarith [hC0'])
    have hB' : C ^ 2 * (K * ‖U ξ‖) ≤ C ^ 2 * (K * D ξ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDge' hK) (by positivity)
    have h2' : ‖iteratedDeriv 2 G ξ‖ ≤ K * D ξ := by
      rw [hd]; exact h2
    calc ‖iteratedDeriv 2 (G * fun ξ => Work.KMTAreas.A7.ee (cc * ξ)) ξ‖
        ≤ ‖iteratedDeriv 2 G ξ‖ + 2 * (2 * Real.pi * |cc|) * ‖iteratedDeriv 1 G ξ‖
            + (2 * Real.pi * |cc|) ^ 2 * ‖G ξ‖ := h
      _ ≤ K * D ξ + 2 * C * (K * D ξ) + C ^ 2 * (K * D ξ) := by linarith [h2', hA, hB, hA', hB']
      _ = (1 + C) ^ 2 * (K * D ξ) := by ring
  have hL1 : Integrable (fun ξ : ℝ => ‖G ξ * Work.KMTAreas.A7.ee (cc * ξ)‖) := by
    have : Integrable (fun ξ : ℝ => G ξ * Work.KMTAreas.A7.ee (cc * ξ)) :=
      ((hGcd.mul (Work.KMTAreas.A7.contDiff_ee_const_mul 2 cc)).continuous).integrable_of_hasCompactSupport
        (hGcs.mul_right)
    exact this.norm
  have hcs2 : HasCompactSupport
      (iteratedDeriv 2 (G * fun ξ => Work.KMTAreas.A7.ee (cc * ξ))) := by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact ((hGcs.mul_right).deriv).deriv
  have hL2 : Integrable (fun ξ : ℝ =>
      ‖iteratedDeriv 2 (G * fun ξ => Work.KMTAreas.A7.ee (cc * ξ)) ξ‖) := by
    have : Integrable
        (fun ξ : ℝ => iteratedDeriv 2 (G * fun ξ => Work.KMTAreas.A7.ee (cc * ξ)) ξ) :=
      (((hGcd.mul (Work.KMTAreas.A7.contDiff_ee_const_mul 2 cc)).continuous_iteratedDeriv 2
          le_rfl).integrable_of_hasCompactSupport hcs2)
    exact this.norm
  have hmain1 : (∫ ξ, ‖G ξ * Work.KMTAreas.A7.ee (cc * ξ)‖) ≤ K * ∫ ξ, D ξ := by
    have := integral_mono hL1 (hIntD.const_mul K) hpt1
    rwa [integral_const_mul] at this
  have hmain2 : (∫ ξ, ‖iteratedDeriv 2 (G * fun ξ => Work.KMTAreas.A7.ee (cc * ξ)) ξ‖)
      ≤ (1 + C) ^ 2 * (K * ∫ ξ, D ξ) := by
    have := integral_mono hL2 ((hIntD.const_mul K).const_mul ((1 + C) ^ 2)) hpt2
    rwa [integral_const_mul, integral_const_mul] at this
  have hSnn : (0:ℝ) ≤ (∫ ξ, ‖U ξ‖) + (∫ ξ, ‖iteratedDeriv 1 U ξ‖)
      + (∫ ξ, ‖iteratedDeriv 2 U ξ‖) := by
    rw [← hDint]; exact hDnn
  constructor
  · calc (∫ ξ, ‖G ξ * Work.KMTAreas.A7.ee (cc * ξ)‖)
        ≤ K * ∫ ξ, D ξ := hmain1
      _ ≤ K * (1 + C) ^ 2 * (∫ ξ, D ξ) := by
          have hstep : (1:ℝ) * (∫ ξ, D ξ) ≤ (1 + C) ^ 2 * (∫ ξ, D ξ) :=
            mul_le_mul_of_nonneg_right hone hDnn
          calc K * (∫ ξ, D ξ) = K * (1 * (∫ ξ, D ξ)) := by ring
            _ ≤ K * ((1 + C) ^ 2 * (∫ ξ, D ξ)) := mul_le_mul_of_nonneg_left hstep hK
            _ = K * (1 + C) ^ 2 * (∫ ξ, D ξ) := by ring
      _ = K * (1 + (1 + 2 * Real.pi * M)) ^ 2 *
            ((∫ ξ, ‖U ξ‖) + (∫ ξ, ‖iteratedDeriv 1 U ξ‖) + (∫ ξ, ‖iteratedDeriv 2 U ξ‖)) := by
          rw [hDint, hC]
  · calc (∫ ξ, ‖iteratedDeriv 2 (G * fun ξ => Work.KMTAreas.A7.ee (cc * ξ)) ξ‖)
        ≤ (1 + C) ^ 2 * (K * ∫ ξ, D ξ) := hmain2
      _ = K * (1 + C) ^ 2 * (∫ ξ, D ξ) := by ring
      _ = K * (1 + (1 + 2 * Real.pi * M)) ^ 2 *
            ((∫ ξ, ‖U ξ‖) + (∫ ξ, ‖iteratedDeriv 1 U ξ‖) + (∫ ξ, ‖iteratedDeriv 2 U ξ‖)) := by
          rw [hDint, hC]


/-! ## 5.  Unfolding of the modified modulated bump -/

/-- The modified modulated bump is the product of the weight `(c ξ)^j`, the unmodulated bump
`φ̃_N` and the modulation `e(P(N t) ξ)`. -/
private lemma varphitildeNtj_eq (P : Polynomial ℤ) (N k : ℕ) (j : ℤ) (t : ℝ) :
    varphitildeNtj P N k j t = fun ξ : ℝ =>
      (((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * ξ : ℝ) : ℂ) ^ j
        * Work.KMTAreas.A7.varphitildeN P.natDegree N k ξ
        * Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((N : ℝ) * t) * ξ) := by
  funext ξ
  simp only [varphitildeNtj, Work.KMTAreas.A7.varphitildeNt]
  ring

/-! ## 6.  The main statement -/

theorem varphitildeNtj_bounds (P : Polynomial ℤ) (N k : ℕ) (j : ℤ) (hk : k ≠ 0 ∨ 0 ≤ j) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      ContDiff ℝ 2 (Work.KMTPlan.A6.varphitildeNtj P N k j t) ∧
      HasCompactSupport (Work.KMTPlan.A6.varphitildeNtj P N k j t) ∧
      (∫ y, ‖Work.KMTPlan.A6.varphitildeNtj P N k j t y‖ ∂MeasureTheory.volume) ≤ S ∧
      (∫ y, ‖iteratedDeriv 2 (Work.KMTPlan.A6.varphitildeNtj P N k j t) y‖ ∂MeasureTheory.volume) ≤ S := by
  classical
  set d : ℕ := P.natDegree with hd
  set c : ℝ := (2 : ℝ) ^ (-((d : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ d with hc
  set u : ℝ → ℂ := Work.KMTAreas.A7.varphitildeN d N k with hu
  set R : ℝ := (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) with hR
  set M : ℝ := max 1 ((∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|) *
    (1 + (N : ℝ)) ^ P.natDegree) with hM
  have hM0 : 0 ≤ M := by rw [hM]; exact le_trans zero_le_one (le_max_left 1 _)
  have hu_cd : ContDiff ℝ 2 u := by
    rw [hu]; exact Work.KMTAreas.A7.contDiff_varphitildeN d N k
  have hu_cs : HasCompactSupport u := by
    rw [hu]; exact Work.KMTAreas.A7.hasCompactSupport_varphitildeN d N k
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hout : ∀ ξ : ℝ, R < |ξ| → u ξ = 0 := by
    intro ξ hξ
    rw [hu]
    by_contra hne
    have hb := varphitildeN_ne_zero_abs_le d N k hne
    rw [hR] at hξ
    linarith
  have hint : ∀ m : ℕ, m ≤ 2 → Integrable (fun y : ℝ => ‖iteratedDeriv m u y‖) := by
    intro m hm
    rw [hu]
    exact integrable_iteratedDeriv_varphitildeN d N k m hm
  obtain ⟨K, G, hK, hGcd, hGcs, hGeq, hb0, hb1, hb2⟩ :
      ∃ (K : ℝ) (G : ℝ → ℂ), 0 ≤ K ∧ ContDiff ℝ 2 G ∧ HasCompactSupport G ∧
        G = (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j * u ξ) ∧
        (∀ ξ : ℝ, ‖G ξ‖ ≤ K * ‖u ξ‖) ∧
        (∀ ξ : ℝ, ‖iteratedDeriv 1 G ξ‖ ≤ K * (‖u ξ‖ + ‖iteratedDeriv 1 u ξ‖)) ∧
        (∀ ξ : ℝ, ‖iteratedDeriv 2 G ξ‖ ≤
          K * (‖u ξ‖ + ‖iteratedDeriv 1 u ξ‖ + ‖iteratedDeriv 2 u ξ‖)) := by
    by_cases hj : (0:ℤ) ≤ j
    · obtain ⟨hcd, hcs, K, hK, hb0, hb1, hb2⟩ :=
        natPow_mul_bounds u hu_cd hu_cs hR0 hout c j.toNat
      have hAeq : (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j * u ξ)
          = fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j.toNat * u ξ := by
        funext ξ
        rw [show ((c * ξ : ℝ) : ℂ) ^ j = ((c * ξ : ℝ) : ℂ) ^ j.toNat from by
          rw [← zpow_natCast, Int.toNat_of_nonneg hj]]
      exact ⟨K, (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j * u ξ), hK, by rw [hAeq]; exact hcd,
        by rw [hAeq]; exact hcs, rfl, fun ξ => by rw [hAeq]; exact hb0 ξ,
        fun ξ => by rw [hAeq]; exact hb1 ξ, fun ξ => by rw [hAeq]; exact hb2 ξ⟩
    · have hjneg : j < 0 := lt_of_not_ge hj
      have hk0 : k ≠ 0 := hk.resolve_right hj
      by_cases hc0 : c = 0
      · have hzero : (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j * u ξ) = fun _ : ℝ => (0:ℂ) := by
          funext ξ
          rw [hc0]
          simp [zero_zpow j (ne_of_lt hjneg)]
        refine ⟨1, (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j * u ξ), zero_le_one, ?_, ?_, rfl, ?_, ?_, ?_⟩
        · rw [hzero]; exact contDiff_const
        · rw [hzero]; exact HasCompactSupport.zero
        · intro ξ; rw [hzero]; simp <;> positivity
        · intro ξ; rw [hzero]; simp <;> positivity
        · intro ξ; rw [hzero]; simp <;> positivity
      · set δ : ℝ := (2 : ℝ) ^ (-(d * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) + (d : ℝ) + 1))
          with hδ
        have hδpos : 0 < δ := by rw [hδ]; positivity
        have hin : ∀ ξ : ℝ, |ξ| < δ → u ξ = 0 := by
          intro ξ hξ
          rw [hu]
          rw [hδ] at hξ
          exact varphitildeN_eq_zero_of_abs_lt d N k hk0 hξ
        obtain ⟨hcd, hcs, K, hK, hb0, hb1, hb2⟩ :=
          weight_zpow_bounds u hu_cd hu_cs hδpos hR0 hin hout c hc0 j hjneg
        exact ⟨K, (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ j * u ξ), hK, hcd, hcs, rfl, hb0, hb1, hb2⟩
  refine ⟨K * (1 + (1 + 2 * Real.pi * M)) ^ 2 *
      ((∫ y, ‖u y‖) + (∫ y, ‖iteratedDeriv 1 u y‖) + (∫ y, ‖iteratedDeriv 2 u y‖)) + 1, ?_, ?_⟩
  · have hS : (0:ℝ) ≤ (∫ y, ‖u y‖) + (∫ y, ‖iteratedDeriv 1 u y‖)
        + (∫ y, ‖iteratedDeriv 2 u y‖) := by
      have h1 : (0:ℝ) ≤ ∫ y, ‖u y‖ := integral_nonneg (fun y => norm_nonneg _)
      have h2 : (0:ℝ) ≤ ∫ y, ‖iteratedDeriv 1 u y‖ := integral_nonneg (fun y => norm_nonneg _)
      have h3 : (0:ℝ) ≤ ∫ y, ‖iteratedDeriv 2 u y‖ := integral_nonneg (fun y => norm_nonneg _)
      linarith
    positivity
  · intro t ht
    have ht1 : |t| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [ht.1], ht.2⟩
    have hcc : |Work.KMTAreas.A7.PevalR P ((N : ℝ) * t)| ≤ M :=
      le_trans (Work.KMTAreas.A7.abs_PevalR_mul_le P N ht1)
        (by rw [hM]; exact le_max_right 1 _)
    have hfun : varphitildeNtj P N k j t =
        G * fun ξ => Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((N : ℝ) * t) * ξ) := by
      rw [varphitildeNtj_eq, hGeq]
      funext ξ
      show (((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * ξ : ℝ)
              : ℂ) ^ j
          * Work.KMTAreas.A7.varphitildeN P.natDegree N k ξ
          * Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((N : ℝ) * t) * ξ)
        = (((2 : ℝ) ^ (-((d : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ d * ξ : ℝ)
              : ℂ) ^ j
          * Work.KMTAreas.A7.varphitildeN d N k ξ
          * Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((N : ℝ) * t) * ξ)
      rw [← hd]
    obtain ⟨hI1, hI2⟩ := mod_bounds u hu_cd hu_cs G hGcd hGcs hK hb0 hb1 hb2 hint M hM0
      (Work.KMTAreas.A7.PevalR P ((N : ℝ) * t)) hcc
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hfun]
      exact hGcd.mul (Work.KMTAreas.A7.contDiff_ee_const_mul 2 _)
    · rw [hfun]
      exact hGcs.mul_right
    · rw [hfun]
      refine le_trans hI1 ?_
      linarith
    · rw [hfun]
      refine le_trans hI2 ?_
      linarith

end Work.KMTPlan.A6
