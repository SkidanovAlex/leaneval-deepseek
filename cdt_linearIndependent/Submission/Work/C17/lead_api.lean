import Mathlib
import Submission.Work.C17.lead_defs

/-!
# Local expansion data at `0`: the arithmetic API

Lemmas about `Reg`, `Unit0`, `LeadAt`, `Lead2At` (see `Submission.Work.C17.lead_defs`),
proved from the order-of-vanishing function `ordAtT 0`.
-/

namespace Work.C17

open Commons.FieldTheory.RatFunc
open Polynomial

noncomputable section

/-! ## Order facts -/

theorem ordAtT_zero : ordAtT (0 : ℚ) (0 : RatFunc ℚ) = ⊤ := by
  rw [ordAtT]; simp

theorem withTop_coe_le_coe_int {a b : ℤ} (h : a ≤ b) :
    ((a : ℤ) : WithTop ℤ) ≤ ((b : ℤ) : WithTop ℤ) := by
  exact_mod_cast h

theorem withTop_coe_le_coe_int' {a b : ℤ} (h : ((a : ℤ) : WithTop ℤ) ≤ ((b : ℤ) : WithTop ℤ)) :
    a ≤ b := by
  exact_mod_cast h

theorem xQ_eq_algebraMap : xQ = algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X := by
  rw [xQ, RatFunc.algebraMap_X]

theorem xQ_ne_zero : xQ ≠ (0 : RatFunc ℚ) := by
  rw [xQ_eq_algebraMap]
  exact RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero

theorem ordAtT_xQ : ordAtT (0 : ℚ) xQ = 1 := by
  rw [xQ_eq_algebraMap, ordAtT_algebraMap Polynomial.X_ne_zero]
  rw [show (Polynomial.X : Polynomial ℚ) = Polynomial.X - Polynomial.C 0 by simp,
    Polynomial.rootMultiplicity_X_sub_C_self]
  norm_num

theorem ordAtT_rat {c : ℚ} (hc : c ≠ 0) :
    ordAtT (0 : ℚ) (algebraMap ℚ (RatFunc ℚ) c) = 0 := by
  rw [IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (RatFunc ℚ) c,
    show (algebraMap ℚ (Polynomial ℚ)) c = Polynomial.C c from (Polynomial.C_eq_algebraMap c).symm,
    ordAtT_algebraMap (Polynomial.C_ne_zero.mpr hc), Polynomial.rootMultiplicity_C]
  norm_num

theorem ordAtT_xQ_zpow (k : ℤ) : ordAtT (0 : ℚ) (xQ ^ k) = (k : WithTop ℤ) := by
  rcases lt_or_ge 0 k with hk | hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hk)
    rw [zpow_natCast, ordAtT_pow (0 : ℚ) xQ_ne_zero n, ordAtT_xQ]
    simp
  · have hk0 : (0 : ℤ) ≤ -k := by omega
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hk0
    have hkn : k = -(n : ℤ) := by omega
    rw [hkn, zpow_neg, zpow_natCast,
      ordAtT_inv (0 : ℚ) (pow_ne_zero n xQ_ne_zero),
      ordAtT_pow (0 : ℚ) xQ_ne_zero n, ordAtT_xQ]
    simp

theorem rootMultiplicity_zero_eq_zero {p : Polynomial ℚ} (hp : p.coeff 0 ≠ 0) :
    p.rootMultiplicity (0 : ℚ) = 0 := by
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree']
  exact Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hp)

/-- If `X ^ k ∣ p` and `q` does not vanish at `0`, then `p/q` has order at least `k` at `0`. -/
theorem ordAtT_div_algebraMap_ge {p q : Polynomial ℚ} (hq : q.coeff 0 ≠ 0) {k : ℕ}
    (hp : Polynomial.X ^ k ∣ p) :
    (k : WithTop ℤ) ≤ ordAtT (0 : ℚ)
      (algebraMap (Polynomial ℚ) (RatFunc ℚ) p / algebraMap (Polynomial ℚ) (RatFunc ℚ) q) := by
  have hq0 : q ≠ 0 := fun h => hq (by rw [h, Polynomial.coeff_zero])
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [map_zero, zero_div, ordAtT_zero]; exact le_top
  · have hkroot : k ≤ p.rootMultiplicity (0 : ℚ) := by
      rw [(Polynomial.le_rootMultiplicity_iff hp0)]
      rwa [show (Polynomial.X - Polynomial.C (0 : ℚ)) = Polynomial.X by simp]
    have hkrootZ : (k : ℤ) ≤ (p.rootMultiplicity (0 : ℚ) : ℤ) := by exact_mod_cast hkroot
    rw [ordAtT_div (0 : ℚ) (RatFunc.algebraMap_ne_zero hp0) (RatFunc.algebraMap_ne_zero hq0),
      ordAtT_algebraMap hp0, ordAtT_algebraMap hq0, rootMultiplicity_zero_eq_zero hq]
    refine le_trans (withTop_coe_le_coe_int hkrootZ) (le_of_eq ?_)
    simp

theorem ordAtT_mul_ge {a b : RatFunc ℚ} {j k : ℤ}
    (ha : ((j : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) a)
    (hb : ((k : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) b) :
    ((j + k : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) (a * b) := by
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_mul, ordAtT_zero]; exact le_top
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [mul_zero, ordAtT_zero]; exact le_top
  rw [ordAtT_mul (0 : ℚ) ha0 hb0, WithTop.coe_add]
  exact add_le_add ha hb

theorem ordAtT_add_ge' {a b : RatFunc ℚ} {j : ℤ}
    (ha : ((j : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) a)
    (hb : ((j : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) b) :
    ((j : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) (a + b) :=
  le_trans (le_min ha hb) (ordAtT_add_ge (0 : ℚ) a b)

/-! ## `Reg` -/

theorem reg_zero : Reg (0 : RatFunc ℚ) := by
  rw [Reg, ordAtT_zero]; exact le_top

theorem reg_rat (c : ℚ) : Reg (algebraMap ℚ (RatFunc ℚ) c) := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero]; exact reg_zero
  · rw [Reg, ordAtT_rat hc]

theorem reg_one : Reg (1 : RatFunc ℚ) := by
  have h : (1 : RatFunc ℚ) = algebraMap ℚ (RatFunc ℚ) 1 := by rw [map_one]
  rw [h]; exact reg_rat 1

theorem reg_algebraMap (p : Polynomial ℚ) :
    Reg (algebraMap (Polynomial ℚ) (RatFunc ℚ) p) := by
  rcases eq_or_ne p 0 with rfl | hp
  · rw [map_zero]; exact reg_zero
  · rw [Reg, ordAtT_algebraMap hp]
    exact withTop_coe_le_coe_int (Int.natCast_nonneg _)

theorem reg_add {f g : RatFunc ℚ} (hf : Reg f) (hg : Reg g) : Reg (f + g) := by
  rw [Reg] at hf hg ⊢
  exact ordAtT_add_ge' hf hg

theorem reg_neg {f : RatFunc ℚ} (hf : Reg f) : Reg (-f) := by
  rw [Reg] at hf ⊢
  rwa [ordAtT_neg]

theorem reg_sub {f g : RatFunc ℚ} (hf : Reg f) (hg : Reg g) : Reg (f - g) := by
  rw [sub_eq_add_neg]
  exact reg_add hf (reg_neg hg)

theorem reg_mul {f g : RatFunc ℚ} (hf : Reg f) (hg : Reg g) : Reg (f * g) := by
  rw [Reg] at hf hg ⊢
  exact ordAtT_mul_ge hf hg

theorem reg_pow {f : RatFunc ℚ} (hf : Reg f) (n : ℕ) : Reg (f ^ n) := by
  induction n with
  | zero => simpa using reg_one
  | succ n ih => rw [pow_succ]; exact reg_mul ih hf

theorem reg_X : Reg xQ := by
  rw [Reg, ordAtT_xQ]; norm_num

theorem reg_xQ_zpow {k : ℤ} (hk : 0 ≤ k) : Reg (xQ ^ k) := by
  rw [Reg, ordAtT_xQ_zpow]
  exact withTop_coe_le_coe_int hk

theorem reg_xQ_zpow_mul {f : RatFunc ℚ} (hf : Reg f) {k : ℤ} (hk : 0 ≤ k) :
    Reg (xQ ^ k * f) :=
  reg_mul (reg_xQ_zpow hk) hf

theorem reg_of_ordAtT_ge {f : RatFunc ℚ} {j : ℤ} (h : ((j : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) f)
    (hj : 0 ≤ j) : Reg f :=
  le_trans (withTop_coe_le_coe_int hj) h

theorem reg_div_algebraMap {p q : Polynomial ℚ} (hq : q.coeff 0 ≠ 0) :
    Reg (algebraMap (Polynomial ℚ) (RatFunc ℚ) p / algebraMap (Polynomial ℚ) (RatFunc ℚ) q) :=
  reg_of_ordAtT_ge (ordAtT_div_algebraMap_ge hq (k := 0) (one_dvd p)) le_rfl

/-! ## `Unit0` -/

theorem unit0_ne_zero {f : RatFunc ℚ} (hf : Unit0 f) : f ≠ 0 := by
  intro h0
  rw [Unit0, h0, ordAtT_zero] at hf
  exact WithTop.top_ne_zero hf

theorem unit0_to_reg {f : RatFunc ℚ} (hf : Unit0 f) : Reg f := by
  rw [Reg, hf]

theorem unit0_rat {c : ℚ} (hc : c ≠ 0) : Unit0 (algebraMap ℚ (RatFunc ℚ) c) :=
  ordAtT_rat hc

theorem unit0_one : Unit0 (1 : RatFunc ℚ) := by
  have h : (1 : RatFunc ℚ) = algebraMap ℚ (RatFunc ℚ) 1 := by rw [map_one]
  rw [h]; exact unit0_rat one_ne_zero

theorem unit0_algebraMap {p : Polynomial ℚ} (hp : p.coeff 0 ≠ 0) :
    Unit0 (algebraMap (Polynomial ℚ) (RatFunc ℚ) p) := by
  have hp0 : p ≠ 0 := fun h => hp (by rw [h, Polynomial.coeff_zero])
  rw [Unit0, ordAtT_algebraMap hp0, rootMultiplicity_zero_eq_zero hp]
  simp

theorem unit0_mul {f g : RatFunc ℚ} (hf : Unit0 f) (hg : Unit0 g) : Unit0 (f * g) := by
  have hf0 := unit0_ne_zero hf
  have hg0 := unit0_ne_zero hg
  rw [Unit0] at hf hg ⊢
  rw [ordAtT_mul (0 : ℚ) hf0 hg0, hf, hg]
  simp

theorem unit0_inv {f : RatFunc ℚ} (hf : Unit0 f) : Unit0 f⁻¹ := by
  have hf0 := unit0_ne_zero hf
  rw [Unit0] at hf ⊢
  rw [ordAtT_inv (0 : ℚ) hf0, hf]
  simp

theorem reg_inv_of_unit {f : RatFunc ℚ} (hf : Unit0 f) : Reg f⁻¹ := by
  have hf0 := unit0_ne_zero hf
  rw [Reg, ordAtT_inv (0 : ℚ) hf0, hf]
  simp

theorem unit0_X_sub_one : Unit0 (xQ - 1) := by
  have hx : xQ - 1 = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X - 1) := by
    rw [xQ_eq_algebraMap, map_sub, map_one]
  rw [hx]
  apply unit0_algebraMap
  simp

theorem unit0_X_sub_one_inv : Unit0 ((xQ - 1)⁻¹) :=
  unit0_inv unit0_X_sub_one

/-- `c + x·g` is a unit of the local ring at `0` when `c ≠ 0` and `g` is regular. -/
theorem unit0_rat_add_xQ_mul {c : ℚ} (hc : c ≠ 0) {g : RatFunc ℚ} (hg : Reg g) :
    Unit0 (algebraMap ℚ (RatFunc ℚ) c + xQ * g) := by
  have hreg : Reg (algebraMap ℚ (RatFunc ℚ) c + xQ * g) :=
    reg_add (reg_rat c) (reg_mul reg_X hg)
  rw [Unit0]
  refine le_antisymm ?_ hreg
  have hxg : ((1 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) (xQ * g) :=
    ordAtT_mul_ge (a := xQ) (b := g) (j := 1) (k := 0)
      (by rw [ordAtT_xQ]; norm_num) hg
  have hnxg : ((1 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) (-(xQ * g)) := by
    rw [ordAtT_neg]; exact hxg
  have h4 : min (ordAtT (0 : ℚ) (algebraMap ℚ (RatFunc ℚ) c + xQ * g))
      (ordAtT (0 : ℚ) (-(xQ * g))) ≤ (0 : WithTop ℤ) := by
    have h := ordAtT_add_ge (0 : ℚ) (algebraMap ℚ (RatFunc ℚ) c + xQ * g) (-(xQ * g))
    rw [show algebraMap ℚ (RatFunc ℚ) c + xQ * g + (-(xQ * g)) = algebraMap ℚ (RatFunc ℚ) c
      by ring, show ordAtT (0 : ℚ) (algebraMap ℚ (RatFunc ℚ) c) = 0 from ordAtT_rat hc] at h
    exact h
  by_contra hcon
  push_neg at hcon
  have h5 : (0 : WithTop ℤ) < ordAtT (0 : ℚ) (-(xQ * g)) := lt_of_lt_of_le zero_lt_one hnxg
  have h6 : (0 : WithTop ℤ) < min (ordAtT (0 : ℚ) (algebraMap ℚ (RatFunc ℚ) c + xQ * g))
      (ordAtT (0 : ℚ) (-(xQ * g))) := lt_min hcon h5
  exact absurd (lt_of_lt_of_le h6 h4) (lt_irrefl 0)

theorem unit0_one_add_xQ_mul {g : RatFunc ℚ} (hg : Reg g) : Unit0 (1 + xQ * g) := by
  have h : (1 : RatFunc ℚ) + xQ * g = algebraMap ℚ (RatFunc ℚ) 1 + xQ * g := by rw [map_one]
  rw [h]; exact unit0_rat_add_xQ_mul one_ne_zero hg

/-! ## `LeadAt` -/

theorem leadAt_of_eq_mul_X {f : RatFunc ℚ} {e : ℤ} {l : ℚ} (hl : l ≠ 0) {g : RatFunc ℚ}
    (hg : Reg g) (h : f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l = xQ * g) : LeadAt f e l := by
  refine ⟨hl, ?_⟩
  rw [h]
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [mul_zero, ordAtT_zero]; exact le_top
  · rw [ordAtT_mul (0 : ℚ) xQ_ne_zero hg0, ordAtT_xQ]
    rw [Reg] at hg
    exact le_add_of_nonneg_right hg

theorem LeadAt.ne_zero {f : RatFunc ℚ} {e : ℤ} {l : ℚ} (h : LeadAt f e l) : f ≠ 0 := by
  obtain ⟨hl, hle⟩ := h
  intro hf
  rw [hf, zero_mul, zero_sub] at hle
  rw [show (-(algebraMap ℚ (RatFunc ℚ) l)) = algebraMap ℚ (RatFunc ℚ) (-l) by rw [map_neg],
    ordAtT_rat (neg_ne_zero.mpr hl)] at hle
  exact absurd hle (by norm_num)

theorem LeadAt.neg {f : RatFunc ℚ} {e : ℤ} {l : ℚ} (h : LeadAt f e l) : LeadAt (-f) e (-l) := by
  obtain ⟨hl, hle⟩ := h
  refine ⟨neg_ne_zero.mpr hl, ?_⟩
  have h1 : (-f) * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) (-l)
      = -(f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l) := by
    rw [map_neg]; ring
  rw [h1, ordAtT_neg]
  exact hle

/-- `g * x^{-e'}` is regular if `LeadAt g e' l'`. -/
theorem reg_mul_xQ_zpow_of_lead {g : RatFunc ℚ} {e' : ℤ} {l' : ℚ} (hg : LeadAt g e' l') :
    Reg (g * xQ ^ (-e')) := by
  obtain ⟨hl', hg1⟩ := hg
  have h1 : Reg (g * xQ ^ (-e') - algebraMap ℚ (RatFunc ℚ) l') := reg_of_ordAtT_ge hg1 (by norm_num)
  have h2 := reg_add h1 (reg_rat l')
  simpa using h2

theorem LeadAt.mul {f g : RatFunc ℚ} {e e' : ℤ} {l l' : ℚ} (hf : LeadAt f e l)
    (hg : LeadAt g e' l') : LeadAt (f * g) (e + e') (l * l') := by
  obtain ⟨hl, hf1⟩ := hf
  obtain ⟨hl', hg1⟩ := hg
  have hB : Reg (g * xQ ^ (-e')) := reg_mul_xQ_zpow_of_lead ⟨hl', hg1⟩
  have hB' : ((0 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) (g * xQ ^ (-e')) := hB
  refine ⟨mul_ne_zero hl hl', ?_⟩
  have heq : f * g * xQ ^ (-(e + e')) - algebraMap ℚ (RatFunc ℚ) (l * l')
      = (f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l) * (g * xQ ^ (-e'))
        + algebraMap ℚ (RatFunc ℚ) l * (g * xQ ^ (-e') - algebraMap ℚ (RatFunc ℚ) l') := by
    rw [map_mul, neg_add, zpow_add₀ xQ_ne_zero]
    ring
  rw [heq]
  refine ordAtT_add_ge' ?_ ?_
  · have := ordAtT_mul_ge (a := f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l)
      (b := g * xQ ^ (-e')) (j := 1) (k := 0) hf1 hB'
    simpa using this
  · have := ordAtT_mul_ge (a := algebraMap ℚ (RatFunc ℚ) l)
      (b := g * xQ ^ (-e') - algebraMap ℚ (RatFunc ℚ) l') (j := 0) (k := 1)
      (le_of_eq (ordAtT_rat hl).symm) hg1
    simpa using this

theorem LeadAt.add_of_eq {f g : RatFunc ℚ} {e : ℤ} {l l' : ℚ} (hf : LeadAt f e l)
    (hg : LeadAt g e l') (hsum : l + l' ≠ 0) : LeadAt (f + g) e (l + l') := by
  obtain ⟨hl, hf1⟩ := hf
  obtain ⟨hl', hg1⟩ := hg
  refine ⟨hsum, ?_⟩
  have heq : (f + g) * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) (l + l')
      = (f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l)
        + (g * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l') := by
    rw [map_add]; ring
  rw [heq]
  exact ordAtT_add_ge' hf1 hg1

theorem LeadAt.sub_of_eq {f g : RatFunc ℚ} {e : ℤ} {l l' : ℚ} (hf : LeadAt f e l)
    (hg : LeadAt g e l') (hsub : l - l' ≠ 0) : LeadAt (f - g) e (l - l') := by
  have hsub' : l + -l' ≠ 0 := by simpa only [sub_eq_add_neg] using hsub
  have h := LeadAt.add_of_eq hf (LeadAt.neg hg) hsub'
  simpa [sub_eq_add_neg] using h

theorem LeadAt.add_of_lt {f g : RatFunc ℚ} {e e' : ℤ} {l l' : ℚ} (hf : LeadAt f e l)
    (hg : LeadAt g e' l') (hlt : e < e') : LeadAt (f + g) e l := by
  obtain ⟨hl, hf1⟩ := hf
  have hB : Reg (g * xQ ^ (-e')) := reg_mul_xQ_zpow_of_lead hg
  have hB' : ((0 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) (g * xQ ^ (-e')) := hB
  refine ⟨hl, ?_⟩
  have heq : (f + g) * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l
      = (f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l)
        + xQ ^ (e' - e) * (g * xQ ^ (-e')) := by
    have hz : xQ ^ (-e) = xQ ^ (e' - e) * xQ ^ (-e') := by
      rw [← zpow_add₀ xQ_ne_zero]; congr 1; ring
    rw [hz]; ring
  rw [heq]
  refine ordAtT_add_ge' hf1 ?_
  have hge : (1 : ℤ) ≤ e' - e := by omega
  have := ordAtT_mul_ge (a := xQ ^ (e' - e)) (b := g * xQ ^ (-e')) (j := e' - e) (k := 0)
    (le_of_eq (ordAtT_xQ_zpow (e' - e)).symm) hB'
  exact le_trans (withTop_coe_le_coe_int hge) (by simpa using this)

theorem LeadAt.rat {c : ℚ} (hc : c ≠ 0) : LeadAt (algebraMap ℚ (RatFunc ℚ) c) 0 c := by
  refine leadAt_of_eq_mul_X hc (g := 0) reg_zero ?_
  simp

/-! ## `Lead2At` -/

theorem lead2At_of_eq_mul_X_sq {f : RatFunc ℚ} {e : ℤ} {l m : ℚ} (hl : l ≠ 0) {g : RatFunc ℚ}
    (hg : Reg g)
    (h : f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l - algebraMap ℚ (RatFunc ℚ) m * xQ
      = xQ ^ 2 * g) : Lead2At f e l m := by
  refine ⟨hl, ?_⟩
  rw [h]
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [mul_zero, ordAtT_zero]; exact le_top
  · rw [ordAtT_mul (0 : ℚ) (pow_ne_zero 2 xQ_ne_zero) hg0,
      ordAtT_pow (0 : ℚ) xQ_ne_zero 2, ordAtT_xQ]
    rw [Reg] at hg
    simpa using le_add_of_nonneg_right hg

theorem Lead2At.to_LeadAt {f : RatFunc ℚ} {e : ℤ} {l m : ℚ} (h : Lead2At f e l m) :
    LeadAt f e l := by
  obtain ⟨hl, hle⟩ := h
  refine ⟨hl, ?_⟩
  have heq : f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l
      = (f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l - algebraMap ℚ (RatFunc ℚ) m * xQ)
        + algebraMap ℚ (RatFunc ℚ) m * xQ := by ring
  rw [heq]
  refine ordAtT_add_ge' (j := 1) ?_ ?_
  · exact le_trans (show ((1 : ℤ) : WithTop ℤ) ≤ ((2 : ℤ) : WithTop ℤ) by norm_num) hle
  · rcases eq_or_ne m 0 with rfl | hm
    · rw [map_zero, zero_mul, ordAtT_zero]; exact le_top
    · have hm0 : algebraMap ℚ (RatFunc ℚ) m ≠ 0 := by
        intro h0; exact hm ((algebraMap ℚ (RatFunc ℚ)).injective (by rw [h0, map_zero]))
      rw [ordAtT_mul (0 : ℚ) hm0 xQ_ne_zero, ordAtT_rat hm, ordAtT_xQ]
      norm_num

theorem Lead2At.ne_zero {f : RatFunc ℚ} {e : ℤ} {l m : ℚ} (h : Lead2At f e l m) : f ≠ 0 :=
  (h.to_LeadAt).ne_zero

/-- `Reg` of `f / X ^ 2` when `f` has order at least `2`. -/
theorem reg_div_xQ_sq {f : RatFunc ℚ} (hf : ((2 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) f) :
    Reg (f / xQ ^ 2) := by
  set H : RatFunc ℚ := f / xQ ^ 2 with hH
  have hmul : xQ ^ 2 * H = f := by
    rw [hH, div_eq_mul_inv, ← mul_assoc, mul_comm (xQ ^ 2) f,
      mul_inv_cancel_right₀ (pow_ne_zero 2 xQ_ne_zero)]
  rw [Reg]
  rcases eq_or_ne H 0 with h0 | h0
  · rw [h0, ordAtT_zero]; exact le_top
  · rw [← hmul] at hf
    rw [ordAtT_mul (0 : ℚ) (pow_ne_zero 2 xQ_ne_zero) h0,
      ordAtT_pow (0 : ℚ) xQ_ne_zero 2, ordAtT_xQ] at hf
    cases hHval : ordAtT (0 : ℚ) H with
    | top => exact le_top
    | coe k =>
      simp only [hHval, mul_one, ← WithTop.coe_add] at hf
      exact withTop_coe_le_coe_int (by
        have : (2 : ℤ) ≤ 2 + k := withTop_coe_le_coe_int' (by simpa using hf)
        omega)

end

end Work.C17

