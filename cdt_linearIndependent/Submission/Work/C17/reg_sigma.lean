import Mathlib
import Submission.Work.C17.lead_defs
import Submission.Commons.FieldTheory.RatFunc.ordAtT_algebraMap
import Submission.Commons.FieldTheory.RatFunc.ordAtT_div
import Submission.Commons.FieldTheory.RatFunc.ordAtT_mul
import Submission.Commons.FieldTheory.RatFunc.ordAtT_pow
import Submission.Commons.FieldTheory.RatFunc.ordAtT_inv
import Submission.Commons.FieldTheory.RatFunc.ordAtT_add_ge
import Submission.Commons.FieldTheory.RatFunc.ordAtT_neg
import Submission.Commons.FieldTheory.RatFunc.ordAtT_eq_top_iff
import Submission.Commons.FieldTheory.RatFunc.ordAtT_add_eq_of_le_succ

/-!
# `Reg` and `Unit0` are preserved by the deck involution `sigmaQ`

The deck involution `σ : x ↦ x/(x-1)` of `ℚ(x)` (the nontrivial deck transformation of the double
cover `y = x²/(x-1)`, see `Work.C17.sigmaQ`) fixes the point `x = 0` and is a *local isomorphism*
there: `σ x = x/(x-1) = -x·(1-x)⁻¹`, so `σ` is a unit of the local ring at `0` whose leading term
is `-x`.  Consequently `σ` preserves the order of vanishing at `0`:

  `ordAtT 0 (σ f) = ordAtT 0 f`   for every `f : ℚ(x)`.

The two conclusions of `reg_sigma` are immediate consequences: regularity at `0` is preserved, and
the image of a polynomial `p` with `p(0) ≠ 0` is a unit of the local ring at `0`.

The mathematical content is the computation of the order at `0` of `p(x/(x-1))`
(`ordAtT_eval₂_uQ`): it equals the multiplicity of `0` as a root of `p`.  The local parameter
`x ↦ x/(x-1)` has order one, and `uQ` is a unit of the local ring at `0` in the sense that
`ordAtT 0 (algebraMap c + uQ·f) = 0` for every nonzero constant `c` and every regular `f`
(`ordAtT_algMap_rat_add_uQ_mul`, from the strict-dominance rule `ordAtT_add_eq_of_le_succ`).
-/

namespace Work.C17

open Commons.FieldTheory.RatFunc
open Polynomial

noncomputable section

/- The auxiliary lemmas below are about the local behaviour at `x = 0` of the deck involution;
they are scoped in their own namespace to keep the `Work.C17` namespace clean. -/
namespace regSigma

/-- The deck involution applied to the local parameter: `u = σ x = x/(x-1)`. -/
noncomputable def uQ : RatFunc ℚ := xQ / (xQ - 1)

lemma sigmaQ_xQ_eq_uQ : sigmaQ xQ = uQ := sigmaQ_X

lemma xQ_ne_zero : (xQ : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero

lemma uQ_ne_zero : uQ ≠ 0 := by
  rw [← sigmaQ_xQ_eq_uQ]
  exact fun h => xQ_ne_zero (sigmaQ.injective (by rw [h, map_zero]))

lemma xQ_sub_one_ne_zero : (xQ : RatFunc ℚ) - 1 ≠ 0 := by
  have h : (xQ : RatFunc ℚ) - 1 = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X - Polynomial.C 1) := by
    simp [xQ]
  rw [h]
  exact RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero (1 : ℚ))

lemma ordAtT_xQ : ordAtT (0:ℚ) xQ = 1 := by
  have h : xQ = algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X := rfl
  rw [h, ordAtT_algebraMap (Polynomial.X_ne_zero)]
  have : Polynomial.rootMultiplicity (0:ℚ) Polynomial.X = 1 := by
    rw [show (Polynomial.X : Polynomial ℚ) = Polynomial.X - Polynomial.C 0 by simp]
    rw [Polynomial.rootMultiplicity_X_sub_C]; simp
  rw [this]; norm_num

lemma ordAtT_xQ_sub_one : ordAtT (0:ℚ) ((xQ : RatFunc ℚ) - 1) = 0 := by
  have h : (xQ : RatFunc ℚ) - 1 = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X - Polynomial.C 1) := by
    simp [xQ]
  rw [h, ordAtT_algebraMap (Polynomial.X_sub_C_ne_zero (1 : ℚ))]
  have : Polynomial.rootMultiplicity (0:ℚ) (Polynomial.X - Polynomial.C 1) = 0 := by
    rw [Polynomial.rootMultiplicity_X_sub_C]; simp
  rw [this]; norm_num

lemma ordAtT_uQ : ordAtT (0:ℚ) uQ = 1 := by
  rw [uQ, ordAtT_div (0:ℚ) xQ_ne_zero xQ_sub_one_ne_zero, ordAtT_xQ, ordAtT_xQ_sub_one]
  norm_num

lemma reg_add {f g : RatFunc ℚ} (hf : Reg f) (hg : Reg g) : Reg (f + g) := by
  unfold Reg at *
  exact le_trans (le_min hf hg) (ordAtT_add_ge (0:ℚ) f g)

lemma reg_mul {f g : RatFunc ℚ} (hf : Reg f) (hg : Reg g) : Reg (f * g) := by
  unfold Reg at *
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [zero_mul]; simp [ordAtT]
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [mul_zero]; simp [ordAtT]
  rw [ordAtT_mul (0:ℚ) hf0 hg0]
  exact add_nonneg hf hg

lemma reg_algebraMap_poly (p : Polynomial ℚ) :
    Reg (algebraMap (Polynomial ℚ) (RatFunc ℚ) p) := by
  unfold Reg
  rcases eq_or_ne p 0 with rfl | hp
  · rw [map_zero]; simp [ordAtT]
  rw [ordAtT_algebraMap hp]
  exact_mod_cast Int.natCast_nonneg _

lemma algMap_rat_eq_C (c : ℚ) : algebraMap ℚ (RatFunc ℚ) c = RatFunc.C c :=
  RingHom.congr_fun (RingHom.ext_rat (algebraMap ℚ (RatFunc ℚ)) RatFunc.C) c

lemma reg_C (c : ℚ) : Reg (RatFunc.C c) := by
  rw [← RatFunc.algebraMap_C (K := ℚ) c]
  exact reg_algebraMap_poly (Polynomial.C c)

lemma reg_algebraMap_rat (c : ℚ) : Reg (algebraMap ℚ (RatFunc ℚ) c) := by
  rw [algMap_rat_eq_C]; exact reg_C c

lemma reg_one : Reg (1 : RatFunc ℚ) := by
  simpa using reg_algebraMap_poly (1 : Polynomial ℚ)

lemma reg_uQ : Reg uQ := by
  unfold Reg; rw [ordAtT_uQ]; norm_num

lemma reg_pow {f : RatFunc ℚ} (hf : Reg f) (n : ℕ) : Reg (f ^ n) := by
  induction n with
  | zero => simpa using reg_one
  | succ n ih => rw [pow_succ]; exact reg_mul ih hf

lemma ordAtT_algMap_rat {c : ℚ} (hc : c ≠ 0) :
    ordAtT (0:ℚ) (algebraMap ℚ (RatFunc ℚ) c) = ((0:ℤ) : WithTop ℤ) := by
  rw [algMap_rat_eq_C, ← RatFunc.algebraMap_C (K := ℚ) c]
  rw [ordAtT_algebraMap (Polynomial.C_ne_zero.mpr hc)]
  rw [Polynomial.rootMultiplicity_C]; norm_num

lemma reg_eval₂_uQ (p : Polynomial ℚ) :
    Reg (p.eval₂ (algebraMap ℚ (RatFunc ℚ)) uQ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval₂_add]; exact reg_add hp hq
  | monomial n a =>
    rw [Polynomial.eval₂_monomial]
    exact reg_mul (reg_algebraMap_rat a) (reg_pow reg_uQ n)

lemma one_le_ordAtT_mul_uQ {f : RatFunc ℚ} (hf : Reg f) :
    (1 : WithTop ℤ) ≤ ordAtT (0:ℚ) (uQ * f) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [mul_zero]; simp [ordAtT]
  rw [ordAtT_mul (0:ℚ) uQ_ne_zero hf0, ordAtT_uQ]
  have h0 : ((0:ℤ) : WithTop ℤ) ≤ ordAtT (0:ℚ) f := hf
  exact le_add_of_nonneg_right h0

lemma ordAtT_algMap_rat_add_uQ_mul {c : ℚ} (hc : c ≠ 0) {f : RatFunc ℚ} (hf : Reg f) :
    ordAtT (0:ℚ) (algebraMap ℚ (RatFunc ℚ) c + uQ * f) = ((0:ℤ) : WithTop ℤ) :=
  ordAtT_add_eq_of_le_succ (ordAtT_algMap_rat hc) (by simpa using one_le_ordAtT_mul_uQ hf)

lemma sigmaQ_algebraMap_eval₂ (p : Polynomial ℚ) :
    sigmaQ (algebraMap (Polynomial ℚ) (RatFunc ℚ) p)
      = p.eval₂ (algebraMap ℚ (RatFunc ℚ)) (sigmaQ xQ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval₂_add]; simp only [map_add, hp, hq]
  | monomial n a =>
    rw [Polynomial.eval₂_monomial, ← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow]
    rw [RatFunc.algebraMap_X, RatFunc.algebraMap_C, algMap_rat_eq_C]
    rw [show (RatFunc.X : RatFunc ℚ) = xQ from rfl, sigmaQ_xQ_eq_uQ]
    rw [← algMap_rat_eq_C a, sigmaQ.commutes a]

lemma eval₂_uQ_ne_zero {q : Polynomial ℚ} (hq : q ≠ 0) :
    q.eval₂ (algebraMap ℚ (RatFunc ℚ)) uQ ≠ 0 := by
  rw [← sigmaQ_xQ_eq_uQ, ← sigmaQ_algebraMap_eval₂ q]
  intro hc
  have hz : algebraMap (Polynomial ℚ) (RatFunc ℚ) q = 0 := by
    have := congrArg sigmaQ hc
    simpa using this
  exact hq (RatFunc.algebraMap_injective ℚ (by simpa using hz))

lemma rootMultiplicity_zero_X : Polynomial.rootMultiplicity (0:ℚ) (Polynomial.X : Polynomial ℚ) = 1 := by
  rw [show (Polynomial.X : Polynomial ℚ) = Polynomial.X - Polynomial.C 0 by simp]
  rw [Polynomial.rootMultiplicity_X_sub_C]; simp

lemma ordAtT_eval₂_uQ (p : Polynomial ℚ) (hp : p ≠ 0) :
    ordAtT (0:ℚ) (p.eval₂ (algebraMap ℚ (RatFunc ℚ)) uQ)
      = ((p.rootMultiplicity (0:ℚ) : ℤ) : WithTop ℤ) := by
  have H : ∀ n, ∀ p : Polynomial ℚ, p.natDegree = n → p ≠ 0 →
      ordAtT (0:ℚ) (p.eval₂ (algebraMap ℚ (RatFunc ℚ)) uQ)
        = ((p.rootMultiplicity (0:ℚ) : ℤ) : WithTop ℤ) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro p hdeg hp
      have hpc : p = Polynomial.X * p.divX + Polynomial.C (p.coeff 0) :=
        (Polynomial.X_mul_divX_add p).symm
      rcases eq_or_ne (p.coeff 0) 0 with hc | hc
      · have hpX : p = Polynomial.X * p.divX := by
          have h := Polynomial.X_mul_divX_add p
          rw [hc, Polynomial.C_0, add_zero] at h
          exact h.symm
        have hq : p.divX ≠ 0 := by
          intro h0; rw [hpX, h0, mul_zero] at hp; exact hp rfl
        have hlt : p.divX.natDegree < n := by
          have := Polynomial.natDegree_X_mul hq
          rw [← hpX, hdeg] at this
          omega
        have hIH := ih p.divX.natDegree hlt p.divX rfl hq
        have hXq : Polynomial.X * p.divX ≠ 0 := by rw [← hpX]; exact hp
        have hev : (p.eval₂ (algebraMap ℚ (RatFunc ℚ)) uQ)
            = uQ * (p.divX).eval₂ (algebraMap ℚ (RatFunc ℚ)) uQ := by
          conv_lhs => rw [hpX]
          rw [Polynomial.eval₂_mul, Polynomial.eval₂_X]
        have hrm : p.rootMultiplicity (0:ℚ) = 1 + (p.divX).rootMultiplicity (0:ℚ) := by
          conv_lhs => rw [hpX]
          rw [Polynomial.rootMultiplicity_mul hXq, rootMultiplicity_zero_X]
        rw [hev, hrm, ordAtT_mul (0:ℚ) uQ_ne_zero (eval₂_uQ_ne_zero hq), ordAtT_uQ, hIH]
        push_cast; ring_nf
      · have hrm0 : p.rootMultiplicity (0:ℚ) = 0 := by
          rw [Polynomial.rootMultiplicity_eq_zero]
          intro hroot
          rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero] at hroot
          exact hc hroot
        have hev : p.eval₂ (algebraMap ℚ (RatFunc ℚ)) uQ
            = algebraMap ℚ (RatFunc ℚ) (p.coeff 0)
              + uQ * (p.divX).eval₂ (algebraMap ℚ (RatFunc ℚ)) uQ := by
          conv_lhs => rw [hpc]
          rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]
          ring
        rw [hev, hrm0]
        exact ordAtT_algMap_rat_add_uQ_mul hc (reg_eval₂_uQ p.divX)
  exact H p.natDegree p rfl hp

lemma ordAt_sigmaQ_algebraMap (p : Polynomial ℚ) (hp : p ≠ 0) :
    ordAt (0:ℚ) (sigmaQ (algebraMap (Polynomial ℚ) (RatFunc ℚ) p))
      = (p.rootMultiplicity (0:ℚ) : ℤ) := by
  have hne : sigmaQ (algebraMap (Polynomial ℚ) (RatFunc ℚ) p) ≠ 0 := by
    intro h
    have : algebraMap (Polynomial ℚ) (RatFunc ℚ) p = 0 := sigmaQ.injective (by rw [h, map_zero])
    exact hp (RatFunc.algebraMap_injective ℚ (by simpa using this))
  have h := ordAtT_eval₂_uQ p hp
  rw [← sigmaQ_xQ_eq_uQ, ← sigmaQ_algebraMap_eval₂ p] at h
  rw [ordAtT_def (0:ℚ) hne] at h
  exact WithTop.coe_injective h

lemma ordAt_sigmaQ (f : RatFunc ℚ) (hf : f ≠ 0) :
    ordAt (0:ℚ) (sigmaQ f) = ordAt (0:ℚ) f := by
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have h1 := ordAt_sigmaQ_algebraMap f.num hnum
  have h2 := ordAt_sigmaQ_algebraMap f.denom hden
  have hne1 : sigmaQ (algebraMap (Polynomial ℚ) (RatFunc ℚ) f.num) ≠ 0 := by
    intro h
    have : algebraMap (Polynomial ℚ) (RatFunc ℚ) f.num = 0 := sigmaQ.injective (by rw [h, map_zero])
    exact hnum (RatFunc.algebraMap_injective ℚ (by simpa using this))
  have hne2 : sigmaQ (algebraMap (Polynomial ℚ) (RatFunc ℚ) f.denom) ≠ 0 := by
    intro h
    have : algebraMap (Polynomial ℚ) (RatFunc ℚ) f.denom = 0 := sigmaQ.injective (by rw [h, map_zero])
    exact hden (RatFunc.algebraMap_injective ℚ (by simpa using this))
  have hfe : sigmaQ f = sigmaQ (algebraMap (Polynomial ℚ) (RatFunc ℚ) f.num)
      / sigmaQ (algebraMap (Polynomial ℚ) (RatFunc ℚ) f.denom) := by
    conv_lhs => rw [← RatFunc.num_div_denom f]
    rw [map_div₀]
  rw [hfe, ordAt_div (0:ℚ) hne1 hne2, h1, h2, ordAt_def]

lemma ordAtT_sigmaQ (f : RatFunc ℚ) : ordAtT (0:ℚ) (sigmaQ f) = ordAtT (0:ℚ) f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hsf : sigmaQ f ≠ 0 := fun h => hf (sigmaQ.injective (by rw [h, map_zero]))
  rw [ordAtT_def (0:ℚ) hsf, ordAtT_def (0:ℚ) hf, ordAt_sigmaQ f hf]

end regSigma

theorem reg_sigma (f : RatFunc ℚ) (hf : Reg f) : Reg (sigmaQ f) ∧
    (∀ p : Polynomial ℚ, p.coeff 0 ≠ 0 →
      Unit0 (sigmaQ (algebraMap (Polynomial ℚ) (RatFunc ℚ) p))) := by
  refine ⟨?_, ?_⟩
  · unfold Reg at *
    rw [regSigma.ordAtT_sigmaQ f]
    exact hf
  · intro p hp
    unfold Unit0
    have hp0 : p ≠ 0 := by
      intro h; rw [h] at hp; exact hp (by simp)
    rw [regSigma.ordAtT_sigmaQ (algebraMap (Polynomial ℚ) (RatFunc ℚ) p), ordAtT_algebraMap hp0]
    have hrm : p.rootMultiplicity (0:ℚ) = 0 := by
      rw [Polynomial.rootMultiplicity_eq_zero]
      intro hroot
      rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero] at hroot
      exact hp hroot
    rw [hrm]; norm_num

end

end Work.C17
