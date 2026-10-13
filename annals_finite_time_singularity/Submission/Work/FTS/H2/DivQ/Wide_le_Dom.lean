/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Wide ≤ Dom`: the pointwise domination behind the near-region inversion

Level-`l` pointwise domination `Wide l ≤ Dom l` (`1 ≤ l ≤ 4`) for the near-region inversion of
`Submission/Work/FTS/H2/DivQ/NOTES.md` §4, stated on top of the **public** vocabulary
(`Wide`, `Dom`, `AccDom`, `SubEta`, `HonGam`, `Restn`, `Expn`) exported by
`Submission/Work/FTS/H2/DivQ/WDefs.lean`.  This is what turns the inversion's *lower* bound on
the honest `Denγ` data into the base bound `B_l ≤ C RHS`, and hence makes `Wide l` integrable.

The proof is the one of `inversionNear.lean`'s (private) `wide_le_dom`: the diagonal term is
isolated by the `aCoeff_diag` identity `a l l = (2κ)^{l+1}`, the off-diagonal remainder is
estimated by Cauchy–Schwarz over its `l` summands, the `l = 0` slot is absorbed into `SubEta`
through `x^{4-γ} ≤ x^{-η}`, and the Young inequality `A² ≤ 2(A+R)² + 2R²` produces exactly the
recursion `Dom`.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.DivQ.WDefs
import Submission.Work.FTS.H2.DivQ.inversionNear
import Submission.Work.FTS.H2.DivQ.aCoeff_diag
import Submission.Work.FTS.H2.DivQ.aCoeff_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The pointwise estimates -/

/-- **Diagonal domination.** -/
private lemma wide_le_diag {α : ℝ} {h : ℝ → ℝ} {j : ℕ} {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) xNear) :
    Wide α h j x
      ≤ (aCoeff j j x * (x ^ j * iteratedDeriv (j + 1) (sliceX h) x)) ^ 2
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := by
  have hxpos : (0:ℝ) < x := hx.1
  have hk1 : (1:ℝ) ≤ 2 * kappa x := two_kappa_ge_one ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hk0 : (2 * kappa x) ≠ 0 := by positivity
  have hA : (2 * kappa x) ^ (2 * j + 2) * (1 / (2 * kappa x)) = (2 * kappa x) ^ (2 * j + 1) := by
    rw [show 2 * j + 2 = (2 * j + 1) + 1 by ring, pow_succ, one_div, mul_assoc,
      mul_inv_cancel₀ hk0, mul_one]
  have hB : (x ^ j) ^ 2 * x ^ (-(Work.Spaces.gam α))
      = x ^ (2 * (j : ℝ) - Work.Spaces.gam α) := by
    have h := pow_sq_mul_rpow hxpos j (-(Work.Spaces.gam α))
    rwa [show 2 * (j : ℝ) + (-(Work.Spaces.gam α)) = 2 * (j : ℝ) - Work.Spaces.gam α by ring]
      at h
  have key : ((2 * kappa x) ^ (j + 1) * (x ^ j * iteratedDeriv (j + 1) (sliceX h) x)) ^ 2
        * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      = (2 * kappa x) ^ (2 * j + 1)
        * (x ^ (2 * (j : ℝ) - Work.Spaces.gam α)
            * (iteratedDeriv (j + 1) (sliceX h) x) ^ 2) := by
    set g : ℝ := iteratedDeriv (j + 1) (sliceX h) x
    have h1 : ((2 * kappa x) ^ (j + 1)) ^ 2 = (2 * kappa x) ^ (2 * j + 2) := by
      rw [← pow_mul, show (j + 1) * 2 = 2 * j + 2 by ring]
    have h2 : (x ^ j * g) ^ 2 = (x ^ j) ^ 2 * g ^ 2 := mul_pow (x ^ j) g 2
    have h3 : ((2 * kappa x) ^ (j + 1) * (x ^ j * g)) ^ 2
        = ((2 * kappa x) ^ (j + 1)) ^ 2 * (x ^ j * g) ^ 2 :=
      mul_pow ((2 * kappa x) ^ (j + 1)) (x ^ j * g) 2
    have h4 : (2 * kappa x) ^ (2 * j + 2) * ((x ^ j) ^ 2 * g ^ 2)
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
        = ((2 * kappa x) ^ (2 * j + 2) * (1 / (2 * kappa x)))
          * ((x ^ j) ^ 2 * x ^ (-(Work.Spaces.gam α))) * g ^ 2 := by ring
    rw [h3, h1, h2, h4, hA, hB]
    ring
  have hadiag : aCoeff j j x = (2 * kappa x) ^ (j + 1) := by rw [aCoeff_diag]
  rw [hadiag, key, Wide]
  have hnn : (0:ℝ) ≤ x ^ (2 * (j : ℝ) - Work.Spaces.gam α)
      * (iteratedDeriv (j + 1) (sliceX h) x) ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hxpos.le _) (sq_nonneg _)
  have h2' : (1:ℝ) ≤ (2 * kappa x) ^ (2 * j + 1) := one_le_pow₀ hk1
  calc x ^ (2 * (j : ℝ) - Work.Spaces.gam α) * (iteratedDeriv (j + 1) (sliceX h) x) ^ 2
      = 1 * (x ^ (2 * (j : ℝ) - Work.Spaces.gam α)
          * (iteratedDeriv (j + 1) (sliceX h) x) ^ 2) := by ring
    _ ≤ (2 * kappa x) ^ (2 * j + 1)
          * (x ^ (2 * (j : ℝ) - Work.Spaces.gam α)
              * (iteratedDeriv (j + 1) (sliceX h) x) ^ 2) :=
        mul_le_mul_of_nonneg_right h2' hnn

/-- The `m ≥ 1` summand of `Restn`: the weight `x^{-γ}` combines with `x^{2m}` into `Wide m`. -/
private lemma rest_term_eq {α : ℝ} {h : ℝ → ℝ} {l m : ℕ} {x : ℝ} (hx : 0 < x) :
    (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
        * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)))
      = (aCoeff l m x) ^ 2 * Wide α h m x * (1 / (2 * kappa x)) := by
  have hB : (x ^ m) ^ 2 * x ^ (-(Work.Spaces.gam α))
      = x ^ (2 * (m : ℝ) - Work.Spaces.gam α) := by
    have h := pow_sq_mul_rpow hx m (-(Work.Spaces.gam α))
    rwa [show 2 * (m : ℝ) + (-(Work.Spaces.gam α)) = 2 * (m : ℝ) - Work.Spaces.gam α by ring]
      at h
  have h3 : (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
      = (aCoeff l m x) ^ 2
        * ((x ^ m) ^ 2 * (iteratedDeriv (m + 1) (sliceX h) x) ^ 2) := by
    rw [mul_pow (aCoeff l m x) (x ^ m * iteratedDeriv (m + 1) (sliceX h) x) 2,
      mul_pow (x ^ m) (iteratedDeriv (m + 1) (sliceX h) x) 2]
  rw [h3, Wide]
  set g : ℝ := iteratedDeriv (m + 1) (sliceX h) x
  rw [show (aCoeff l m x) ^ 2 * ((x ^ m) ^ 2 * g ^ 2)
        * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)))
      = (aCoeff l m x) ^ 2 * ((x ^ m) ^ 2 * x ^ (-(Work.Spaces.gam α)))
        * g ^ 2 * (1 / (2 * kappa x)) by ring]
  rw [hB]
  ring

/-- **The off-diagonal remainder.** -/
private lemma rest_le {α : ℝ} {h : ℝ → ℝ} {Cm : ℝ} (hCm : 0 ≤ Cm) (hα1 : α ≤ 1) {l : ℕ}
    (hl : 1 ≤ l)
    (hCb : ∀ m ≤ l, ∀ x ∈ Set.Icc (0:ℝ) xNear, |aCoeff l m x| ≤ Cm)
    (hC0 : ∀ x ∈ Set.Icc (0:ℝ) xNear, |aCoeff l 0 x| ≤ Cm * x ^ 2)
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hWle : ∀ m, 1 ≤ m → m < l → ∀ x ∈ Set.Ioo (0:ℝ) xNear, Wide α h m x ≤ Dom α h Cm m x)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) xNear) :
    (Restn h l x) ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      ≤ ((l : ℝ)) * Cm ^ 2 * AccDom α h Cm l x := by
  have hxpos : (0:ℝ) < x := hx.1
  have hxIcc : x ∈ Set.Icc (0:ℝ) xNear := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hxle1 : x ≤ 1 := by linarith [hx.2, xNear_lt]
  have hk1 : (1:ℝ) ≤ 2 * kappa x := two_kappa_ge_one hxIcc
  have hkpos : (0:ℝ) < 2 * kappa x := lt_of_lt_of_le one_pos hk1
  have hknn : (0:ℝ) ≤ 1 / (2 * kappa x) := by positivity
  have hlnn : (0:ℝ) ≤ (l : ℝ) := by positivity
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range l)
    (f := fun m => aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x))
  have hCS : (∑ m ∈ Finset.range l,
        aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
      ≤ ((l : ℝ)) * ∑ m ∈ Finset.range l,
          (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2 := by
    simpa using hcs
  have hterm : ∀ m ∈ Finset.range l,
      (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
          * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)))
        ≤ Cm ^ 2 * Dom α h Cm m x := by
    intro m hm
    have hml : m ≤ l := by have := Finset.mem_range.mp hm; omega
    have hmlt : m < l := Finset.mem_range.mp hm
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      have hinv : 1 / (2 * kappa x) ≤ 1 := by rw [div_le_one hkpos]; linarith
      have h4η : x ^ (4 - Work.Spaces.gam α) ≤ x ^ (-(Work.Spaces.eta)) :=
        Real.rpow_le_rpow_of_exponent_ge hxpos hxle1 (by have := gam_lt_four hα1; linarith)
      have hsub : x ^ (-(Work.Spaces.eta)) * (deriv (sliceX h) x) ^ 2 ≤ SubEta h x :=
        etaPiece_le_subEta hsm hx
      have h1 : (aCoeff l 0 x) ^ 2 ≤ Cm ^ 2 * x ^ 4 := by
        have hle : |aCoeff l 0 x| ≤ Cm * x ^ 2 := hC0 x hxIcc
        rw [show (aCoeff l 0 x) ^ 2 = |aCoeff l 0 x| ^ 2 from (sq_abs _).symm]
        calc |aCoeff l 0 x| ^ 2 ≤ (Cm * x ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hle 2
          _ = Cm ^ 2 * x ^ 4 := by ring
      have hx4 : x ^ 4 * x ^ (-(Work.Spaces.gam α)) = x ^ (4 - Work.Spaces.gam α) := by
        have hh := (Real.rpow_add hxpos (4:ℝ) (-(Work.Spaces.gam α))).symm
        rw [← Real.rpow_natCast x 4]
        exact hh.trans (congrArg (fun e => x ^ e)
          (by ring : (4:ℝ) + (-(Work.Spaces.gam α)) = 4 - Work.Spaces.gam α))
      have hkey : x ^ 4 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
          ≤ x ^ (-(Work.Spaces.eta)) := by
        calc x ^ 4 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
            = x ^ (4 - Work.Spaces.gam α) * (1 / (2 * kappa x)) := by rw [hx4]
          _ ≤ x ^ (4 - Work.Spaces.gam α) * 1 :=
              mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg hxpos.le _)
          _ = x ^ (4 - Work.Spaces.gam α) := by ring
          _ ≤ x ^ (-(Work.Spaces.eta)) := h4η
      simp only [pow_zero, one_mul, Nat.zero_add, iteratedDeriv_one]
      calc (aCoeff l 0 x * deriv (sliceX h) x) ^ 2
              * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)))
          = (aCoeff l 0 x) ^ 2 * (deriv (sliceX h) x) ^ 2
              * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by ring
        _ ≤ (Cm ^ 2 * x ^ 4) * (deriv (sliceX h) x) ^ 2
              * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by
            refine mul_le_mul_of_nonneg_right ?_ ?_
            · exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
            · exact mul_nonneg (Real.rpow_nonneg hxpos.le _) hknn
        _ = Cm ^ 2 * (deriv (sliceX h) x) ^ 2
              * (x ^ 4 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by ring
        _ ≤ Cm ^ 2 * (deriv (sliceX h) x) ^ 2 * x ^ (-(Work.Spaces.eta)) := by
            refine mul_le_mul_of_nonneg_left hkey (mul_nonneg (sq_nonneg Cm) (sq_nonneg _))
        _ ≤ Cm ^ 2 * SubEta h x := by
            have hh := mul_le_mul_of_nonneg_left hsub (sq_nonneg Cm)
            rw [show Cm ^ 2 * (deriv (sliceX h) x) ^ 2 * x ^ (-(Work.Spaces.eta))
              = Cm ^ 2 * (x ^ (-(Work.Spaces.eta)) * (deriv (sliceX h) x) ^ 2) by ring]
            exact hh
        _ = Cm ^ 2 * Dom α h Cm 0 x := by rw [Dom_zero]
    · have h1 : (aCoeff l m x) ^ 2 ≤ Cm ^ 2 := by
        have hle : |aCoeff l m x| ≤ Cm := hCb m hml x hxIcc
        rw [show (aCoeff l m x) ^ 2 = |aCoeff l m x| ^ 2 from (sq_abs _).symm]
        calc |aCoeff l m x| ^ 2 ≤ Cm ^ 2 := by
              simpa using pow_le_pow_left₀ (abs_nonneg _) hle 2
          _ = Cm ^ 2 := rfl
      have hinv : 1 / (2 * kappa x) ≤ 1 := by rw [div_le_one hkpos]; linarith
      rw [rest_term_eq (α := α) (h := h) (x := x) hxpos]
      calc (aCoeff l m x) ^ 2 * Wide α h m x * (1 / (2 * kappa x))
          ≤ Cm ^ 2 * Wide α h m x * 1 := by
            have hp : (0:ℝ) < 1 / (2 * kappa x) := div_pos one_pos hkpos
            exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (Wide_nonneg α h m hxpos.le))
              hinv (le_of_lt hp) (mul_nonneg (sq_nonneg Cm) (Wide_nonneg α h m hxpos.le))
        _ ≤ Cm ^ 2 * Dom α h Cm m x := by
            have h3 := hWle m hmpos hmlt x hx
            nlinarith [h3, sq_nonneg Cm]
  have hstep1 : (Restn h l x) ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      ≤ ((l : ℝ)) * ∑ m ∈ Finset.range l,
          (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
            * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by
    have hz : (0:ℝ) ≤ x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) :=
      mul_nonneg (Real.rpow_nonneg hxpos.le _) hknn
    have h0 : (Restn h l x) ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
        = (Restn h l x) ^ 2 * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by
      ring
    have hS : Restn h l x = ∑ m ∈ Finset.range l,
        aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x) := rfl
    rw [hS]
    rw [show (∑ m ∈ Finset.range l, aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
        = (∑ m ∈ Finset.range l, aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
          * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) by ring]
    refine (mul_le_mul_of_nonneg_right hCS hz).trans (le_of_eq ?_)
    rw [mul_assoc, Finset.sum_mul]
  calc (Restn h l x) ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      ≤ ((l : ℝ)) * ∑ m ∈ Finset.range l,
          (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
            * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := hstep1
    _ ≤ ((l : ℝ)) * ∑ m ∈ Finset.range l, Cm ^ 2 * Dom α h Cm m x :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hlnn
    _ = ((l : ℝ)) * Cm ^ 2 * ∑ m ∈ Finset.range l, Dom α h Cm m x := by
        have h1 : ((l : ℝ)) * ∑ m ∈ Finset.range l, Cm ^ 2 * Dom α h Cm m x
            = ((l : ℝ)) * (Cm ^ 2 * ∑ m ∈ Finset.range l, Dom α h Cm m x) := by
          simp only [Finset.mul_sum]
        rw [show ((l : ℝ)) * Cm ^ 2 * ∑ m ∈ Finset.range l, Dom α h Cm m x
            = ((l : ℝ)) * (Cm ^ 2 * ∑ m ∈ Finset.range l, Dom α h Cm m x) by ring]
        exact h1
    _ = ((l : ℝ)) * Cm ^ 2 * AccDom α h Cm l x := by rw [accDom_eq_sum]

/-- The pointwise Young step at level `k+1`. -/
private lemma wide_le_dom_succ {α : ℝ} {h : ℝ → ℝ} {Cm : ℝ} {k : ℕ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hCm : 0 ≤ Cm) (hα1 : α ≤ 1) (hk : k + 1 ≤ 4)
    (hCb : ∀ m ≤ k + 1, ∀ x ∈ Set.Icc (0 : ℝ) xNear, |aCoeff (k + 1) m x| ≤ Cm)
    (hC0 : ∀ x ∈ Set.Icc (0 : ℝ) xNear, |aCoeff (k + 1) 0 x| ≤ Cm * x ^ 2)
    (hWle : ∀ m, 1 ≤ m → m ≤ k → ∀ x ∈ Set.Ioo (0 : ℝ) xNear,
      Wide α h m x ≤ Dom α h Cm m x)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) xNear) :
    Wide α h (k + 1) x ≤ Dom α h Cm (k + 1) x := by
  have hxpos : (0 : ℝ) < x := hx.1
  have hkpos : (0 : ℝ) < 2 * kappa x :=
    lt_of_lt_of_le one_pos (two_kappa_ge_one ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hknn : (0 : ℝ) ≤ x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) :=
    mul_nonneg (Real.rpow_nonneg hxpos.le _) (le_of_lt (div_pos one_pos hkpos))
  set A : ℝ := aCoeff (k + 1) (k + 1) x
    * (x ^ (k + 1) * iteratedDeriv ((k + 1) + 1) (sliceX h) x) with hA
  set R : ℝ := Restn h (k + 1) x with hR
  have hExp : Work.Elliptic.Dth1Iter (k + 1) (deriv h) (thetaOf x) = Expn h (k + 1) x :=
    Dth1Iter_deriv_expansion (k + 1) hsm hx
  have hR' : (∑ l ∈ Finset.range (k + 1), aCoeff (k + 1) l x
      * (x ^ l * iteratedDeriv (l + 1) (sliceX h) x)) = R := by
    rw [hR]; rfl
  have hsplit : Expn h (k + 1) x = A + R := by
    have hE : Expn h (k + 1) x
        = (∑ l ∈ Finset.range (k + 1), aCoeff (k + 1) l x
            * (x ^ l * iteratedDeriv (l + 1) (sliceX h) x))
          + (aCoeff (k + 1) (k + 1) x
            * (x ^ (k + 1) * iteratedDeriv ((k + 1) + 1) (sliceX h) x)) := by
      simp only [Expn]
      rw [Finset.sum_range_succ]
    rw [hE, hR', ← hA, add_comm]
  have hHon : HonGam α h (k + 1) x
      = (A + R) ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := by
    simp only [HonGam]
    rw [← hsplit, ← hExp]
  have hdiag : Wide α h (k + 1) x
      ≤ A ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := by
    rw [hA]; exact wide_le_diag hx
  have hY2 : A ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      ≤ (2 * (A + R) ^ 2 + 2 * R ^ 2) * x ^ (-(Work.Spaces.gam α))
          * (1 / (2 * kappa x)) := by
    have := mul_le_mul_of_nonneg_right (young A R) hknn
    simpa only [mul_assoc] using this
  have h2 : (2 * (A + R) ^ 2 + 2 * R ^ 2) * x ^ (-(Work.Spaces.gam α))
        * (1 / (2 * kappa x))
      = 2 * HonGam α h (k + 1) x
        + 2 * (R ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by
    rw [hHon]; ring
  have h3 : R ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      ≤ (((k + 1 : ℕ) : ℝ)) * Cm ^ 2 * AccDom α h Cm (k + 1) x := by
    rw [hR]
    exact rest_le (α := α) (h := h) (Cm := Cm) hCm hα1 (by omega) hCb hC0 hsm
      (fun m hm1 hmk => hWle m hm1 (by omega)) hx
  calc Wide α h (k + 1) x ≤ A ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := hdiag
    _ ≤ (2 * (A + R) ^ 2 + 2 * R ^ 2) * x ^ (-(Work.Spaces.gam α))
          * (1 / (2 * kappa x)) := hY2
    _ = 2 * HonGam α h (k + 1) x
          + 2 * (R ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := h2
    _ ≤ 2 * HonGam α h (k + 1) x
          + 2 * ((((k + 1 : ℕ) : ℝ)) * Cm ^ 2 * AccDom α h Cm (k + 1) x) := by
        linarith [h3]
    _ = Dom α h Cm (k + 1) x := by rw [Dom_succ_eq]; ring

/-- **`Wide ≤ Dom`.**  The `x`-weighted square of the `(l+1)`-st slice derivative is dominated
by the level-`l` member of the inversion recursion, for `1 ≤ l ≤ 4`. -/
theorem Wide_le_Dom {α : ℝ} {h : ℝ → ℝ} {Cm : ℝ}
    (hα1 : α ≤ 1) (hCm : 0 ≤ Cm)
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hCb : ∀ (n m : ℕ), 1 ≤ n → n ≤ 4 → m ≤ n →
      ∀ x ∈ Set.Icc (0 : ℝ) xNear, |aCoeff n m x| ≤ Cm)
    (hC0 : ∀ (n : ℕ), 1 ≤ n → n ≤ 4 →
      ∀ x ∈ Set.Icc (0 : ℝ) xNear, |aCoeff n 0 x| ≤ Cm * x ^ 2)
    {l : ℕ} (hl1 : 1 ≤ l) (hl4 : l ≤ 4) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) xNear) :
    Wide α h l x ≤ Dom α h Cm l x := by
  have key : ∀ k ≤ 3, ∀ m, 1 ≤ m → m ≤ k + 1 → ∀ x ∈ Set.Ioo (0 : ℝ) xNear,
      Wide α h m x ≤ Dom α h Cm m x := by
    intro k hk
    induction k with
    | zero =>
        intro m hm1 hm2 x hx
        obtain rfl : m = 1 := by omega
        exact wide_le_dom_succ hsm hCm hα1 (by omega)
          (fun m hm x hx => hCb 1 m le_rfl (by norm_num) hm x hx)
          (fun x hx => hC0 1 le_rfl (by norm_num) x hx)
          (fun m hm1 hm2 => by omega) hx
    | succ k ih =>
        intro m hm1 hm2 x hx
        rcases Nat.lt_or_ge m (k + 2) with hlt | hge
        · exact ih (by omega) m hm1 (by omega) x hx
        · obtain rfl : m = k + 2 := by omega
          refine wide_le_dom_succ hsm hCm hα1 (by omega)
            (fun m hm x hx => hCb (k + 2) m (by omega) (by omega) hm x hx)
            (fun x hx => hC0 (k + 2) (by omega) (by omega) x hx) ?_ hx
          intro r hr1 hr2
          exact ih (by omega) r hr1 (by omega)
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  exact key k (by omega) (k + 1) (by omega) le_rfl x hx

end Work.FTS.H2.DivQ
