import Mathlib
import Submission.Work.LinnikBurgess.frame_step_defs
import Submission.Work.LinnikBurgess.fcd_aux
import Submission.Work.LinnikBurgess.fcd_class
import Submission.Work.LinnikBurgess.cube_root_card_le_three
import Submission.Work.LinnikBurgess.DLd_prod_of_DLp

/-!
# Multi-prime frame step, no `a1 ∉ b` hypothesis

`Work.LinnikBurgess.frame_step_card_d_nohb`: the `DL_d` frame step of the Burgess route in the form
that does *not* assume that `a1` differs from the entries of `b`.

The proof splits on whether `a1` occurs among the entries of `b`.

* If it does (degenerate case), evaluating the pencil relation of `critN_pencil` at `-a1` forces
  the pencil unit `c` to be `1`, so the two cubics agree modulo `p^(k - v_p 2)` and comparing
  `X ^ 2` coefficients pins `a2` modulo `p^(max 0 (k - v_p 2 - v_p (a0 - a1)))` to a *single* class,
  for each prime `p ∣ d` (and hence for all of them at once).
* If it does not, the single-prime frame step confines the admissible `a2` to at most three classes
  per prime, and the Chinese remainder theorem assembles them into at most `3 ^ ω(d)` classes
  modulo `M = ∏_{p ∣ d} p ^ (max 0 (v_p d - v_p 2 - v_p (a0 - a1)))`.

Both cases are fed into the same counting lemma `frameStepD_assembly` (a union of at most
`3 ^ ω(d)` residue classes modulo `M`, each meeting `[1, H]` in at most `H / M + 1` elements).
-/

set_option linter.unusedVariables false

open scoped BigOperators
open Finset
open Polynomial

namespace Work.LinnikBurgess

/-- In `[1, H]`, a residue class modulo `M` has at most `H / M + 1` elements. -/
theorem fsd_card_Icc_filter_mod_eq_le {M H r : ℕ} :
    ((Finset.Icc 1 H).filter (fun a2 => a2 % M = r)).card ≤ H / M + 1 := by
  set s : Finset ℕ := (Finset.Icc 1 H).filter (fun a2 => a2 % M = r) with hs
  have hmaps : Set.MapsTo (fun a2 : ℕ => a2 / M) ↑s ↑(Finset.range (H / M + 1)) := by
    intro x hx
    simp only [Finset.mem_coe] at hx
    rw [hs] at hx
    obtain ⟨hxI, -⟩ := Finset.mem_filter.mp hx
    simp only [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Finset.mem_Icc.mp hxI).2)
  have hinj : Set.InjOn (fun a2 : ℕ => a2 / M) ↑s := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe] at hx hy
    rw [hs] at hx hy
    obtain ⟨-, hxr⟩ := Finset.mem_filter.mp hx
    obtain ⟨-, hyr⟩ := Finset.mem_filter.mp hy
    have hxy' : x / M = y / M := hxy
    calc x = M * (x / M) + x % M := (Nat.div_add_mod x M).symm
      _ = M * (y / M) + y % M := by rw [hxy', hxr, hyr]
      _ = y := Nat.div_add_mod y M
  calc s.card ≤ (Finset.range (H / M + 1)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = H / M + 1 := Finset.card_range _

/-- `((m : ℤ)) ∣ A ↔ m ∣ A.natAbs`. -/
lemma fsd_int_dvd_iff_dvd_natAbs {m : ℕ} {A : ℤ} : (m : ℤ) ∣ A ↔ m ∣ A.natAbs := by
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]

/-- The three congruences extracted from the pencil relation `critN_pencil` for an admissible `a2`
at a unit `y`, with an integer lift `C` of the pencil unit. -/
def FrameAdmGood (p k : ℕ) (a0 a1 : ℕ) (b : Fin 3 → ℕ) (a2 y : ℕ) (C : ℤ) : Prop :=
  UnitAt p y ![a0, a1, a2] b ∧ ¬ (p : ℤ) ∣ C ∧
    ((p ^ (k - padicValNat p 2) : ℕ) : ℤ)
      ∣ C * (∏ l : Fin 3, ((b l : ℤ) - (a0 : ℤ))) - (1 - C) * ((y + a0 : ℕ) : ℤ) ^ 3 ∧
    ((p ^ (k - padicValNat p 2) : ℕ) : ℤ)
      ∣ C * (∏ l : Fin 3, ((b l : ℤ) - (a1 : ℤ))) - (1 - C) * ((y + a1 : ℕ) : ℤ) ^ 3 ∧
    ((p ^ (k - padicValNat p 2) : ℕ) : ℤ)
      ∣ (((a0 + a1 + a2 : ℕ) : ℤ)) - C * (((b 0 + b 1 + b 2 : ℕ) : ℤ))
          + 3 * (1 - C) * (y : ℤ)




/-- The `X ^ 2`-coefficient of `(X - t) ^ 3` is `-3 t`. -/
lemma fsd_coeff_two_cube {N : ℕ} (t : ZMod N) :
    ((Polynomial.X - Polynomial.C t) ^ 3 : Polynomial (ZMod N)).coeff 2 = -3 * t := by
  have h : (Polynomial.X - Polynomial.C t : Polynomial (ZMod N))
      = Polynomial.X + Polynomial.C (-t) := by
    rw [Polynomial.C_neg, sub_eq_add_neg]
  rw [h, Polynomial.coeff_X_add_C_pow]
  norm_num [Nat.choose]
  ring


/-- **Frame-step congruences.**  Let `y` be a unit for the six roots of the pair `(a, b)` with
`a = ![a0, a1, a2]`, at which `critN a b` and its derivative both vanish modulo `p ^ k`.  Then, with
`s = k - v_p(2)`, there is an integer `C` coprime to `p` such that modulo `p ^ s`

* `C * f_b(-a0) ≡ (1 - C) (y + a0) ^ 3`,
* `C * f_b(-a1) ≡ (1 - C) (y + a1) ^ 3`,
* `a0 + a1 + a2 ≡ C (b0 + b1 + b2) - 3 (1 - C) y`.

These are the pencil relation `f_a ≡ c f_b + (1 - c) (X - y)^3 (mod p ^ s)` of `critN_pencil`
evaluated at the two roots `-a0`, `-a1` of `f_a`, together with the comparison of `X ^ 2`
coefficients (`C` being any lift of the unit `c`). -/
theorem fsd_pencil_frame_congr {p k : ℕ} [Fact p.Prime] (a0 a1 a2 : ℕ) (b : Fin 3 → ℕ) (y : ℕ)
    (hy : UnitAt p y ![a0, a1, a2] b)
    (hN : ((p ^ k : ℕ) : ℤ) ∣ (critN ![a0, a1, a2] b).eval (y : ℤ))
    (hN' : ((p ^ k : ℕ) : ℤ) ∣ (Polynomial.derivative (critN ![a0, a1, a2] b)).eval (y : ℤ)) :
    ∃ C : ℤ, ¬ (p : ℤ) ∣ C ∧
      ((p ^ (k - padicValNat p 2) : ℕ) : ℤ)
        ∣ C * (∏ l : Fin 3, ((b l : ℤ) - (a0 : ℤ))) - (1 - C) * ((y + a0 : ℕ) : ℤ) ^ 3
      ∧ ((p ^ (k - padicValNat p 2) : ℕ) : ℤ)
        ∣ C * (∏ l : Fin 3, ((b l : ℤ) - (a1 : ℤ))) - (1 - C) * ((y + a1 : ℕ) : ℤ) ^ 3
      ∧ ((p ^ (k - padicValNat p 2) : ℕ) : ℤ)
        ∣ (((a0 + a1 + a2 : ℕ) : ℤ)) - C * (((b 0 + b 1 + b 2 : ℕ) : ℤ))
            + 3 * (1 - C) * (y : ℤ) := by
  classical
  set s : ℕ := k - padicValNat p 2 with hs
  set B0i : ℤ := ∏ l : Fin 3, ((b l : ℤ) - (a0 : ℤ)) with hB0i
  set B1i : ℤ := ∏ l : Fin 3, ((b l : ℤ) - (a1 : ℤ)) with hB1i
  set U0i : ℤ := ((y + a0 : ℕ) : ℤ) with hU0i
  set U1i : ℤ := ((y + a1 : ℕ) : ℤ) with hU1i
  set E1i : ℤ := ((b 0 + b 1 + b 2 : ℕ) : ℤ) with hE1i
  set S3i : ℤ := ((a0 + a1 + a2 : ℕ) : ℤ) with hS3i
  set Yi : ℤ := (y : ℤ) with hYi
  obtain ⟨c, hcunit, hpencil⟩ := critN_pencil (p := p) (k := k) ![a0, a1, a2] b y hy hN hN'
  by_cases hs0 : s = 0
  · refine ⟨1, fun h => (Fact.out : p.Prime).not_dvd_one (Int.natCast_dvd_natCast.mp h), ?_, ?_, ?_⟩
    · have h1 : ((p ^ s : ℕ) : ℤ) = 1 := by rw [hs0]; norm_num
      rw [h1]; exact one_dvd _
    · have h1 : ((p ^ s : ℕ) : ℤ) = 1 := by rw [hs0]; norm_num
      rw [h1]; exact one_dvd _
    · have h1 : ((p ^ s : ℕ) : ℤ) = 1 := by rw [hs0]; norm_num
      rw [h1]; exact one_dvd _
  · have hs1 : 1 ≤ s := by omega
    haveI : NeZero (p ^ s) := ⟨pow_ne_zero s (Fact.out : p.Prime).ne_zero⟩
    have hcval : ((c.val : ZMod (p ^ s))) = c := ZMod.natCast_zmod_val c
    have hpC : ¬ (p : ℤ) ∣ (c.val : ℤ) := by
      intro h
      have hpv : p ∣ c.val := Int.natCast_dvd_natCast.mp h
      obtain ⟨u, hu⟩ := hcunit
      have hcop : Nat.Coprime c.val (p ^ s) := by
        rw [← hu]
        exact ZMod.val_coe_unit_coprime u
      have hpg : p ∣ p ^ s := by simpa using pow_dvd_pow p hs1
      have hg := Nat.dvd_gcd hpv hpg
      rw [hcop.gcd_eq_one] at hg
      exact (Fact.out : p.Prime).not_dvd_one hg
    -- the two `f_b`-congruences
    have hcong0 : c * ((B0i : ℤ) : ZMod (p ^ s))
        - (1 - c) * ((U0i : ℤ) : ZMod (p ^ s)) ^ 3 = 0 := by
      have hev := congrArg (fun Q : Polynomial (ZMod (p ^ s)) =>
        Polynomial.eval (-(a0 : ZMod (p ^ s))) Q) hpencil
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_sub, Polynomial.eval_X] at hev
      have hL : Polynomial.eval (-(a0 : ZMod (p ^ s)))
          ((cubicZ ![a0, a1, a2]).map (Int.castRingHom (ZMod (p ^ s)))) = 0 := by
        have h := fcd_eval_cubicZ_map_self ![a0, a1, a2] (p ^ s) 0
        simpa using h
      have hR : Polynomial.eval (-(a0 : ZMod (p ^ s)))
          ((cubicZ b).map (Int.castRingHom (ZMod (p ^ s)))) = ((B0i : ℤ) : ZMod (p ^ s)) := by
        rw [fcd_eval_cubicZ_map]
        rw [show ((B0i : ℤ) : ZMod (p ^ s))
            = ((∏ l : Fin 3, ((b l : ℤ) - (a0 : ℤ)) : ℤ) : ZMod (p ^ s)) from by rw [hB0i]]
        push_cast
        refine Finset.prod_congr rfl (fun l _ => ?_)
        ring
      rw [hL, hR] at hev
      have hy0 : (-(a0 : ZMod (p ^ s)) - (y : ZMod (p ^ s)))
          = -(((U0i : ℤ) : ZMod (p ^ s))) := by
        rw [hU0i]; push_cast; ring
      rw [hy0] at hev
      have hneg : (1 - c) * (-(((U0i : ℤ) : ZMod (p ^ s)))) ^ 3
          = -((1 - c) * (((U0i : ℤ) : ZMod (p ^ s))) ^ 3) := by ring
      rw [hneg] at hev
      simpa [sub_eq_add_neg] using hev.symm
    have hcong1 : c * ((B1i : ℤ) : ZMod (p ^ s))
        - (1 - c) * ((U1i : ℤ) : ZMod (p ^ s)) ^ 3 = 0 := by
      have hev := congrArg (fun Q : Polynomial (ZMod (p ^ s)) =>
        Polynomial.eval (-(a1 : ZMod (p ^ s))) Q) hpencil
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_sub, Polynomial.eval_X] at hev
      have hL : Polynomial.eval (-(a1 : ZMod (p ^ s)))
          ((cubicZ ![a0, a1, a2]).map (Int.castRingHom (ZMod (p ^ s)))) = 0 := by
        have h := fcd_eval_cubicZ_map_self ![a0, a1, a2] (p ^ s) 1
        simpa using h
      have hR : Polynomial.eval (-(a1 : ZMod (p ^ s)))
          ((cubicZ b).map (Int.castRingHom (ZMod (p ^ s)))) = ((B1i : ℤ) : ZMod (p ^ s)) := by
        rw [fcd_eval_cubicZ_map]
        rw [show ((B1i : ℤ) : ZMod (p ^ s))
            = ((∏ l : Fin 3, ((b l : ℤ) - (a1 : ℤ)) : ℤ) : ZMod (p ^ s)) from by rw [hB1i]]
        push_cast
        refine Finset.prod_congr rfl (fun l _ => ?_)
        ring
      rw [hL, hR] at hev
      have hy1 : (-(a1 : ZMod (p ^ s)) - (y : ZMod (p ^ s)))
          = -(((U1i : ℤ) : ZMod (p ^ s))) := by
        rw [hU1i]; push_cast; ring
      rw [hy1] at hev
      have hneg : (1 - c) * (-(((U1i : ℤ) : ZMod (p ^ s)))) ^ 3
          = -((1 - c) * (((U1i : ℤ) : ZMod (p ^ s))) ^ 3) := by ring
      rw [hneg] at hev
      simpa [sub_eq_add_neg] using hev.symm
    -- the divisibility form of the two `f_b`-congruences
    have hkey0 : ((p ^ s : ℕ) : ℤ) ∣ (c.val : ℤ) * B0i - (1 - (c.val : ℤ)) * U0i ^ 3 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      rw [hcval]
      exact hcong0
    have hkey1 : ((p ^ s : ℕ) : ℤ) ∣ (c.val : ℤ) * B1i - (1 - (c.val : ℤ)) * U1i ^ 3 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      rw [hcval]
      exact hcong1
    -- the linear congruence, from the `X ^ 2` coefficients
    have hkey2 : ((p ^ s : ℕ) : ℤ) ∣ S3i - (c.val : ℤ) * E1i + 3 * (1 - (c.val : ℤ)) * Yi := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      rw [hcval]
      have hcoeff := congrArg (fun Q : Polynomial (ZMod (p ^ s)) => Q.coeff 2) hpencil
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_map,
        fcd_cubicZ_coeff_two, fsd_coeff_two_cube] at hcoeff
      simp only [fcd_esymm3_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val] at hcoeff
      have hcL : (Int.castRingHom (ZMod (p ^ s))) ((a0 : ℤ) + (a1 : ℤ) + (a2 : ℤ))
          = ((a0 : ZMod (p ^ s)) + (a1 : ZMod (p ^ s)) + (a2 : ZMod (p ^ s))) := by
        change ((((a0 : ℤ) + (a1 : ℤ) + (a2 : ℤ) : ℤ)) : ZMod (p ^ s))
          = ((a0 : ZMod (p ^ s)) + (a1 : ZMod (p ^ s)) + (a2 : ZMod (p ^ s)))
        push_cast
        ring
      have hcR : (Int.castRingHom (ZMod (p ^ s))) ((b 0 : ℤ) + (b 1 : ℤ) + (b 2 : ℤ))
          = ((b 0 : ZMod (p ^ s)) + (b 1 : ZMod (p ^ s)) + (b 2 : ZMod (p ^ s))) := by
        change ((((b 0 : ℤ) + (b 1 : ℤ) + (b 2 : ℤ) : ℤ)) : ZMod (p ^ s))
          = ((b 0 : ZMod (p ^ s)) + (b 1 : ZMod (p ^ s)) + (b 2 : ZMod (p ^ s)))
        push_cast
        ring
      rw [hcL, hcR] at hcoeff
      have hS3 : ((S3i : ℤ) : ZMod (p ^ s))
          = (a0 : ZMod (p ^ s)) + (a1 : ZMod (p ^ s)) + (a2 : ZMod (p ^ s)) := by
        rw [hS3i]; push_cast; ring
      have hE1 : ((E1i : ℤ) : ZMod (p ^ s))
          = (b 0 : ZMod (p ^ s)) + (b 1 : ZMod (p ^ s)) + (b 2 : ZMod (p ^ s)) := by
        rw [hE1i]; push_cast; ring
      have hY : ((Yi : ℤ) : ZMod (p ^ s)) = (y : ZMod (p ^ s)) := by
        rw [hYi]; push_cast; rfl
      rw [hS3, hE1, hY]
      linear_combination hcoeff
    exact ⟨(c.val : ℤ), hpC, hkey0, hkey1, hkey2⟩


/-- **Frame congruence step.**  Let `p` be prime, `s ≥ 1`, `E ≤ s`, `B0 ≠ 0` with
`v_p(B0) = κ`.  Suppose `p ∤ u`, `p ∤ u'`, `u ≡ u' (mod p ^ (E - κ))` and that two frames `(C, u)`,
`(C', u')` satisfy
`C · B0 ≡ (1 - C) · u ^ 3` and `a2 ≡ C · E1 - 3 · (1 - C) · (u - A0)` modulo `p ^ s`
(and the primed versions, with the same `B0, E1, A0`).  Then `a2 ≡ a2' (mod p ^ E)`.

Multiplying the linear congruence by `B0 + u^3` and using the first congruence turns it into
`(B0 + u^3) a2 ≡ u^3 E1 - 3 B0 (u - A0) (mod p^s)`; combining the two frames gives
`U (a2 - a2') ≡ B0 · W (mod p^s)` with `U = (B0 + u^3)(B0 + u'^3)` coprime to `p` and `W`
divisible by `u - u'`, hence by `p ^ E` because `v_p(u - u') ≥ E - κ`. -/
theorem fsd_frame_congruence_step {p s E κ : ℕ} [Fact p.Prime] (hs : 1 ≤ s) (hEs : E ≤ s)
    {B0 E1 A0 u u' C C' a2 a2' : ℤ}
    (hB0 : B0 ≠ 0) (hκ : padicValNat p B0.natAbs = κ)
    (hu : ¬ (p : ℤ) ∣ u) (hu' : ¬ (p : ℤ) ∣ u')
    (hud : ((p ^ (E - κ) : ℕ) : ℤ) ∣ u - u')
    (h1 : ((p ^ s : ℕ) : ℤ) ∣ C * B0 - (1 - C) * u ^ 3)
    (h1' : ((p ^ s : ℕ) : ℤ) ∣ C' * B0 - (1 - C') * u' ^ 3)
    (h2 : ((p ^ s : ℕ) : ℤ) ∣ a2 - (C * E1 - 3 * (1 - C) * (u - A0)))
    (h2' : ((p ^ s : ℕ) : ℤ) ∣ a2' - (C' * E1 - 3 * (1 - C') * (u' - A0))) :
    ((p ^ E : ℕ) : ℤ) ∣ a2 - a2' := by
  have hpEs : ((p ^ E : ℕ) : ℤ) ∣ ((p ^ s : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (pow_dvd_pow p hEs)
  have hpsp : (p : ℤ) ∣ ((p ^ s : ℕ) : ℤ) := by
    have h : ((p ^ 1 : ℕ) : ℤ) ∣ ((p ^ s : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr (pow_dvd_pow p hs)
    simpa using h
  -- the three congruences in usable form
  have hT : ((p ^ s : ℕ) : ℤ) ∣ C * (B0 + u ^ 3) - u ^ 3 := by
    have h : C * (B0 + u ^ 3) - u ^ 3 = C * B0 - (1 - C) * u ^ 3 := by ring
    rw [h]; exact h1
  have hT' : ((p ^ s : ℕ) : ℤ) ∣ C' * (B0 + u' ^ 3) - u' ^ 3 := by
    have h : C' * (B0 + u' ^ 3) - u' ^ 3 = C' * B0 - (1 - C') * u' ^ 3 := by ring
    rw [h]; exact h1'
  have hA : ((p ^ s : ℕ) : ℤ) ∣ (B0 + u ^ 3) * a2 - (u ^ 3 * E1 - 3 * B0 * (u - A0)) := by
    have hident : (B0 + u ^ 3) * a2 - (u ^ 3 * E1 - 3 * B0 * (u - A0))
        = (B0 + u ^ 3) * (a2 - (C * E1 - 3 * (1 - C) * (u - A0)))
          + (E1 + 3 * (u - A0)) * (C * (B0 + u ^ 3) - u ^ 3) := by ring
    rw [hident]
    exact dvd_add (dvd_mul_of_dvd_right h2 (B0 + u ^ 3))
      (dvd_mul_of_dvd_right hT (E1 + 3 * (u - A0)))
  have hA' : ((p ^ s : ℕ) : ℤ) ∣ (B0 + u' ^ 3) * a2' - (u' ^ 3 * E1 - 3 * B0 * (u' - A0)) := by
    have hident : (B0 + u' ^ 3) * a2' - (u' ^ 3 * E1 - 3 * B0 * (u' - A0))
        = (B0 + u' ^ 3) * (a2' - (C' * E1 - 3 * (1 - C') * (u' - A0)))
          + (E1 + 3 * (u' - A0)) * (C' * (B0 + u' ^ 3) - u' ^ 3) := by ring
    rw [hident]
    exact dvd_add (dvd_mul_of_dvd_right h2' (B0 + u' ^ 3))
      (dvd_mul_of_dvd_right hT' (E1 + 3 * (u' - A0)))
  -- the combined congruence
  set X : ℤ := B0 * (u ^ 2 + u * u' + u' ^ 2) * (3 * A0 - E1) + 3 * B0 ^ 2
    - 3 * B0 * u * u' * (u + u') with hX
  have hB : ((p ^ s : ℕ) : ℤ)
      ∣ (B0 + u ^ 3) * (B0 + u' ^ 3) * (a2 - a2') + (u - u') * X := by
    have hident : (B0 + u' ^ 3) * ((B0 + u ^ 3) * a2 - (u ^ 3 * E1 - 3 * B0 * (u - A0)))
        - (B0 + u ^ 3) * ((B0 + u' ^ 3) * a2' - (u' ^ 3 * E1 - 3 * B0 * (u' - A0)))
        = (B0 + u ^ 3) * (B0 + u' ^ 3) * (a2 - a2') + (u - u') * X := by
      rw [hX]; ring
    rw [← hident]
    exact dvd_sub (dvd_mul_of_dvd_right hA (B0 + u' ^ 3))
      (dvd_mul_of_dvd_right hA' (B0 + u ^ 3))
  -- valuations
  have hXκ : ((p ^ κ : ℕ) : ℤ) ∣ X := by
    have hB0dvd : ((p ^ κ : ℕ) : ℤ) ∣ B0 :=
      fsd_int_dvd_iff_dvd_natAbs.mpr
        ((padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hB0)).mpr (le_of_eq hκ.symm))
    have hXfac : X = B0 * ((u ^ 2 + u * u' + u' ^ 2) * (3 * A0 - E1) + 3 * B0
        - 3 * u * u' * (u + u')) := by rw [hX]; ring
    rw [hXfac]
    exact dvd_mul_of_dvd_left hB0dvd _
  have hprod : ((p ^ E : ℕ) : ℤ) ∣ (u - u') * X := by
    have hsp : ((p ^ E : ℕ) : ℤ) ∣ ((p ^ (E - κ) : ℕ) : ℤ) * ((p ^ κ : ℕ) : ℤ) := by
      have hcast : (((p ^ (E - κ)) * (p ^ κ) : ℕ) : ℤ)
          = ((p ^ (E - κ) : ℕ) : ℤ) * ((p ^ κ : ℕ) : ℤ) := by push_cast; ring
      rw [← hcast, Int.natCast_dvd_natCast]
      by_cases h : κ ≤ E
      · rw [← pow_add, Nat.sub_add_cancel h]
      · have h0 : E - κ = 0 := by omega
        rw [h0, pow_zero, one_mul]
        exact pow_dvd_pow p (by omega)
    obtain ⟨t, ht⟩ := hud
    obtain ⟨r, hr⟩ := hXκ
    rw [ht, hr]
    have hmul : ((p ^ (E - κ) : ℕ) : ℤ) * t * (((p ^ κ : ℕ) : ℤ) * r)
        = (((p ^ (E - κ) : ℕ) : ℤ) * ((p ^ κ : ℕ) : ℤ)) * (t * r) := by ring
    rw [hmul]
    exact dvd_mul_of_dvd_left hsp (t * r)
  -- `p ^ E ∣ (B0 + u^3)(B0 + u'^3)(a2 - a2')`
  have hfork : ((p ^ E : ℕ) : ℤ) ∣ (B0 + u ^ 3) * (B0 + u' ^ 3) * (a2 - a2') := by
    have h1'' : ((p ^ E : ℕ) : ℤ)
        ∣ (B0 + u ^ 3) * (B0 + u' ^ 3) * (a2 - a2') + (u - u') * X :=
      dvd_trans hpEs hB
    have hkey : (B0 + u ^ 3) * (B0 + u' ^ 3) * (a2 - a2') + (u - u') * X - (u - u') * X
        = (B0 + u ^ 3) * (B0 + u' ^ 3) * (a2 - a2') := by ring
    rw [← hkey]
    exact dvd_sub h1'' hprod
  -- the multiplier is a unit modulo `p`
  have hpU : ¬ (p : ℤ) ∣ B0 + u ^ 3 := by
    intro hdiv
    have hCs : (p : ℤ) ∣ C * (B0 + u ^ 3) := dvd_mul_of_dvd_right hdiv C
    have hTs : (p : ℤ) ∣ C * (B0 + u ^ 3) - u ^ 3 := dvd_trans hpsp hT
    have hu3 : (p : ℤ) ∣ u ^ 3 := by
      have := dvd_sub hCs hTs
      simpa using this
    have hu3' : p ∣ (u ^ 3).natAbs := fsd_int_dvd_iff_dvd_natAbs.mp hu3
    rw [Int.natAbs_pow] at hu3'
    exact hu (fsd_int_dvd_iff_dvd_natAbs.mpr ((Fact.out : p.Prime).dvd_of_dvd_pow hu3'))
  have hpU' : ¬ (p : ℤ) ∣ B0 + u' ^ 3 := by
    intro hdiv
    have hCs : (p : ℤ) ∣ C' * (B0 + u' ^ 3) := dvd_mul_of_dvd_right hdiv C'
    have hTs : (p : ℤ) ∣ C' * (B0 + u' ^ 3) - u' ^ 3 := dvd_trans hpsp hT'
    have hu3 : (p : ℤ) ∣ u' ^ 3 := by
      have := dvd_sub hCs hTs
      simpa using this
    have hu3' : p ∣ (u' ^ 3).natAbs := fsd_int_dvd_iff_dvd_natAbs.mp hu3
    rw [Int.natAbs_pow] at hu3'
    exact hu' (fsd_int_dvd_iff_dvd_natAbs.mpr ((Fact.out : p.Prime).dvd_of_dvd_pow hu3'))
  -- conclude by coprimality in `ℕ`
  have hcop : Nat.Coprime ((B0 + u ^ 3) * (B0 + u' ^ 3)).natAbs (p ^ E) := by
    refine (Fact.out : p.Prime).coprime_pow_of_not_dvd ?_
    rw [Int.natAbs_mul]
    exact (Fact.out : p.Prime).not_dvd_mul
      (fun h => hpU (fsd_int_dvd_iff_dvd_natAbs.mpr h))
      (fun h => hpU' (fsd_int_dvd_iff_dvd_natAbs.mpr h))
  have hnat : p ^ E ∣ (a2 - a2').natAbs := by
    have h1n : p ^ E ∣ ((B0 + u ^ 3) * (B0 + u' ^ 3)).natAbs * (a2 - a2').natAbs := by
      have h := fsd_int_dvd_iff_dvd_natAbs.mp hfork
      rwa [Int.natAbs_mul] at h
    exact hcop.symm.dvd_of_dvd_mul_left (by simpa only [Nat.mul_comm] using h1n)
  exact fsd_int_dvd_iff_dvd_natAbs.mpr hnat


/-- Two unit witnesses `y`, `y'` (for the same pair of roots `a0 ≠ a1`) whose labels
`(y + a0)/(y + a1)` and `(y' + a0)/(y' + a1)` agree in `ZMod (p ^ m)` satisfy
`y ≡ y' (mod p ^ (m - v_p(a0 - a1)))`.

Clearing denominators gives `(y + a0)(y' + a1) ≡ (y' + a0)(y + a1) (mod p ^ m)`; the difference of
the two sides is `(a0 - a1)(y' - y)`, and dividing by the `p`-power inside `a0 - a1` gives the
stated congruence. -/
theorem fsd_label_modEq_y_sub {p m : ℕ} [Fact p.Prime] (hm : 1 ≤ m) {a0 a1 y y' : ℕ}
    (h01 : a0 ≠ a1) (hy : ¬ p ∣ y + a1) (hy' : ¬ p ∣ y' + a1)
    (h : ((y + a0 : ℕ) : ZMod (p ^ m)) * (((y + a1 : ℕ) : ZMod (p ^ m))⁻¹)
        = ((y' + a0 : ℕ) : ZMod (p ^ m)) * (((y' + a1 : ℕ) : ZMod (p ^ m))⁻¹)) :
    ((p ^ (m - padicValNat p (((a0 : ℤ) - (a1 : ℤ)).natAbs)) : ℕ) : ℤ)
      ∣ ((y : ℤ) - (y' : ℤ)) := by
  have hm0 : 0 < m := hm
  have h' : (((y : ZMod (p ^ m)) + (a0 : ZMod (p ^ m)))
        * (((y : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))))⁻¹)
      = (((y' : ZMod (p ^ m)) + (a0 : ZMod (p ^ m)))
        * (((y' : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))))⁻¹) := by
    simpa only [Nat.cast_add] using h
  have hV : ((y : ZMod (p ^ m)) + (a1 : ZMod (p ^ m)))
      = ((y + a1 : ℕ) : ZMod (p ^ m)) := by push_cast; ring
  have hV' : ((y' : ZMod (p ^ m)) + (a1 : ZMod (p ^ m)))
      = ((y' + a1 : ℕ) : ZMod (p ^ m)) := by push_cast; ring
  have hiv : IsUnit ((y : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))) := by
    rw [hV]
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hm0).mpr hy
  have hiv' : IsUnit ((y' : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))) := by
    rw [hV']
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hm0).mpr hy'
  have hii : (((y : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))))⁻¹
      * ((y : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))) = 1 := ZMod.inv_mul_of_unit _ hiv
  have hii' : (((y' : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))))⁻¹
      * ((y' : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))) = 1 := ZMod.inv_mul_of_unit _ hiv'
  have hcross : ((y : ZMod (p ^ m)) + (a0 : ZMod (p ^ m)))
        * ((y' : ZMod (p ^ m)) + (a1 : ZMod (p ^ m)))
      = ((y' : ZMod (p ^ m)) + (a0 : ZMod (p ^ m)))
        * ((y : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))) := by
    have h2 : (((y : ZMod (p ^ m)) + (a0 : ZMod (p ^ m)))
          * (((y : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))))⁻¹)
          * (((y : ZMod (p ^ m)) + (a1 : ZMod (p ^ m)))
            * ((y' : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))))
        = (((y' : ZMod (p ^ m)) + (a0 : ZMod (p ^ m)))
          * (((y' : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))))⁻¹)
          * (((y : ZMod (p ^ m)) + (a1 : ZMod (p ^ m)))
            * ((y' : ZMod (p ^ m)) + (a1 : ZMod (p ^ m)))) := by rw [h']
    have e1 : (((y : ZMod (p ^ m)) + (a0 : ZMod (p ^ m)))
          * (((y : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))))⁻¹)
          * (((y : ZMod (p ^ m)) + (a1 : ZMod (p ^ m)))
            * ((y' : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))))
        = ((y : ZMod (p ^ m)) + (a0 : ZMod (p ^ m)))
          * ((y' : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))) := by
      rw [show (((y : ZMod (p ^ m)) + (a0 : ZMod (p ^ m)))
            * (((y : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))))⁻¹)
            * (((y : ZMod (p ^ m)) + (a1 : ZMod (p ^ m)))
              * ((y' : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))))
          = ((y : ZMod (p ^ m)) + (a0 : ZMod (p ^ m)))
            * ((((y : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))))⁻¹
              * ((y : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))))
            * ((y' : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))) from by ring, hii]
      ring
    have e2 : (((y' : ZMod (p ^ m)) + (a0 : ZMod (p ^ m)))
          * (((y' : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))))⁻¹)
          * (((y : ZMod (p ^ m)) + (a1 : ZMod (p ^ m)))
            * ((y' : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))))
        = ((y' : ZMod (p ^ m)) + (a0 : ZMod (p ^ m)))
          * ((y : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))) := by
      rw [show (((y' : ZMod (p ^ m)) + (a0 : ZMod (p ^ m)))
            * (((y' : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))))⁻¹)
            * (((y : ZMod (p ^ m)) + (a1 : ZMod (p ^ m)))
              * ((y' : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))))
          = ((y' : ZMod (p ^ m)) + (a0 : ZMod (p ^ m)))
            * ((((y' : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))))⁻¹
              * ((y' : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))))
            * ((y : ZMod (p ^ m)) + (a1 : ZMod (p ^ m))) from by ring, hii']
      ring
    rw [e1, e2] at h2
    exact h2
  have hdvdZ : ((p ^ m : ℕ) : ℤ) ∣ (((y + a0 : ℕ) * (y' + a1 : ℕ) : ℕ) : ℤ)
      - (((y' + a0 : ℕ) * (y + a1 : ℕ) : ℕ) : ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    rw [hcross, sub_self]
  have hdiff : (((y + a0 : ℕ) * (y' + a1 : ℕ) : ℕ) : ℤ)
        - (((y' + a0 : ℕ) * (y + a1 : ℕ) : ℕ) : ℤ)
      = ((a0 : ℤ) - (a1 : ℤ)) * ((y' : ℤ) - (y : ℤ)) := by
    push_cast
    ring
  rw [hdiff] at hdvdZ
  by_cases hyy : ((y' : ℤ) - (y : ℤ)) = 0
  · rw [show ((y : ℤ) - (y' : ℤ)) = 0 from by omega]
    exact dvd_zero _
  · have hA : ((a0 : ℤ) - (a1 : ℤ)) ≠ 0 := fun hh => h01 (by omega)
    have hprodne : ((a0 : ℤ) - (a1 : ℤ)) * ((y' : ℤ) - (y : ℤ)) ≠ 0 := mul_ne_zero hA hyy
    have hmle : m ≤ padicValNat p ((((a0 : ℤ) - (a1 : ℤ)) * ((y' : ℤ) - (y : ℤ)))).natAbs :=
      (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hprodne)).mp
        (fsd_int_dvd_iff_dvd_natAbs.mp hdvdZ)
    have hsplit : padicValNat p ((((a0 : ℤ) - (a1 : ℤ)) * ((y' : ℤ) - (y : ℤ)))).natAbs
        = padicValNat p (((a0 : ℤ) - (a1 : ℤ)).natAbs)
          + padicValNat p (((y' : ℤ) - (y : ℤ)).natAbs) := by
      rw [Int.natAbs_mul,
        padicValNat.mul (Int.natAbs_ne_zero.mpr hA) (Int.natAbs_ne_zero.mpr hyy)]
    have hleZ : m - padicValNat p (((a0 : ℤ) - (a1 : ℤ)).natAbs)
        ≤ padicValNat p (((y' : ℤ) - (y : ℤ)).natAbs) := by
      rw [hsplit] at hmle
      omega
    have hdvdZ' : ((p ^ (m - padicValNat p (((a0 : ℤ) - (a1 : ℤ)).natAbs)) : ℕ) : ℤ)
        ∣ ((y' : ℤ) - (y : ℤ)) :=
      fsd_int_dvd_iff_dvd_natAbs.mpr
        ((padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hyy)).mpr hleZ)
    have hneg := dvd_neg.mpr hdvdZ'
    simpa using hneg

/-- If `p ^ e ∣ A - B`, `A ≠ 0` and `v_p(A) = m < e`, then `B ≠ 0` and `v_p(B) = m`. -/
lemma fsd_padicValNat_eq_of_dvd_sub {p e m : ℕ} [Fact p.Prime] {A B : ℤ}
    (hA : A ≠ 0) (hAB : ((p ^ e : ℕ) : ℤ) ∣ A - B) (hAv : padicValNat p A.natAbs = m)
    (hm : m < e) : B ≠ 0 ∧ padicValNat p B.natAbs = m := by
  have hAne : A.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hA
  have hBne : B ≠ 0 := by
    intro hB
    have hdvdA : ((p ^ e : ℕ) : ℤ) ∣ A := by rw [hB, sub_zero] at hAB; exact hAB
    have : e ≤ padicValNat p A.natAbs :=
      (padicValNat_dvd_iff_le hAne).mp (fsd_int_dvd_iff_dvd_natAbs.mp hdvdA)
    omega
  have hBne' : B.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hBne
  have hmle : m ≤ padicValNat p B.natAbs := by
    have h1 : ((p ^ m : ℕ) : ℤ) ∣ A := fsd_int_dvd_iff_dvd_natAbs.mpr
      ((padicValNat_dvd_iff_le hAne).mpr (le_of_eq hAv.symm))
    have h2 : ((p ^ m : ℕ) : ℤ) ∣ A - B :=
      dvd_trans (Int.natCast_dvd_natCast.mpr (pow_dvd_pow p (le_of_lt hm))) hAB
    have h3 : ((p ^ m : ℕ) : ℤ) ∣ B := by
      have hkey : A - (A - B) = B := by ring
      rw [← hkey]
      exact dvd_sub h1 h2
    exact (padicValNat_dvd_iff_le hBne').mp (fsd_int_dvd_iff_dvd_natAbs.mp h3)
  have hmge : padicValNat p B.natAbs ≤ m := by
    by_contra hcon
    have h1 : m + 1 ≤ padicValNat p B.natAbs := by omega
    have hBdvd : ((p ^ (m + 1) : ℕ) : ℤ) ∣ B :=
      fsd_int_dvd_iff_dvd_natAbs.mpr ((padicValNat_dvd_iff_le hBne').mpr h1)
    have hABdvd : ((p ^ (m + 1) : ℕ) : ℤ) ∣ A - B :=
      dvd_trans (Int.natCast_dvd_natCast.mpr (pow_dvd_pow p (by omega : m + 1 ≤ e))) hAB
    have hAdvd : ((p ^ (m + 1) : ℕ) : ℤ) ∣ A := by
      have hkey : (A - B) + B = A := by ring
      rw [← hkey]
      exact dvd_add hABdvd hBdvd
    have : m + 1 ≤ padicValNat p A.natAbs :=
      (padicValNat_dvd_iff_le hAne).mp (fsd_int_dvd_iff_dvd_natAbs.mp hAdvd)
    omega
  exact ⟨hBne, le_antisymm hmge hmle⟩

/-- **Case B, valuation computation.**  If `C · B0 ≡ (1 - C) u₀³` and `C · B1 ≡ (1 - C) u₁³`
modulo `p ^ s`, with `C, u₀, u₁` units and `v_p(B0) = κ < s`, then `v_p(1 - C) = κ` and
`v_p(B1) = κ`. -/
theorem fsd_caseB_val_eq {p s κ : ℕ} [Fact p.Prime] (hs : 1 ≤ s) {B0 B1 C u₀ u₁ : ℤ}
    (hB0 : B0 ≠ 0) (hB1 : B1 ≠ 0) (hκ : padicValNat p B0.natAbs = κ) (hκs : κ < s)
    (hC : ¬ (p : ℤ) ∣ C) (hu₀ : ¬ (p : ℤ) ∣ u₀) (hu₁ : ¬ (p : ℤ) ∣ u₁)
    (h1 : ((p ^ s : ℕ) : ℤ) ∣ C * B0 - (1 - C) * u₀ ^ 3)
    (h2 : ((p ^ s : ℕ) : ℤ) ∣ C * B1 - (1 - C) * u₁ ^ 3) :
    padicValNat p (1 - C).natAbs = κ ∧ padicValNat p B1.natAbs = κ := by
  have hCne : C ≠ 0 := fun h => hC (by rw [h]; exact dvd_zero _)
  have hu₀ne : u₀ ≠ 0 := fun h => hu₀ (by rw [h]; exact dvd_zero _)
  have hu₁ne : u₁ ≠ 0 := fun h => hu₁ (by rw [h]; exact dvd_zero _)
  have hCne' : C.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hCne
  have h1C : 1 - C ≠ 0 := by
    intro h0
    have hC1 : C = 1 := by omega
    have hd : ((p ^ s : ℕ) : ℤ) ∣ B0 := by
      have h := h1
      rw [h0, hC1] at h
      simpa using h
    have : s ≤ padicValNat p B0.natAbs :=
      (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hB0)).mp (fsd_int_dvd_iff_dvd_natAbs.mp hd)
    omega
  have h1C' : (1 - C).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr h1C
  have hA0 : C * B0 ≠ 0 := mul_ne_zero hCne hB0
  have hAv : padicValNat p (C * B0).natAbs = κ := by
    rw [Int.natAbs_mul, padicValNat.mul hCne' (Int.natAbs_ne_zero.mpr hB0),
      padicValNat.eq_zero_of_not_dvd (fun h => hC (fsd_int_dvd_iff_dvd_natAbs.mpr h)), hκ]
    omega
  have hv1 := fsd_padicValNat_eq_of_dvd_sub (p := p) (e := s) (m := κ) hA0 h1 hAv hκs
  have hval1 : padicValNat p (1 - C).natAbs = κ := by
    have h2' : padicValNat p ((1 - C) * u₀ ^ 3).natAbs = padicValNat p (1 - C).natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_pow,
        padicValNat.mul h1C' (pow_ne_zero 3 (Int.natAbs_ne_zero.mpr hu₀ne)), padicValNat.pow,
        padicValNat.eq_zero_of_not_dvd (fun h => hu₀ (fsd_int_dvd_iff_dvd_natAbs.mpr h))]
      omega
    rw [← h2']; exact hv1.2
  have hA2 : (1 - C) * u₁ ^ 3 ≠ 0 := mul_ne_zero h1C (pow_ne_zero 3 hu₁ne)
  have hA2v : padicValNat p ((1 - C) * u₁ ^ 3).natAbs = κ := by
    rw [Int.natAbs_mul, Int.natAbs_pow,
      padicValNat.mul h1C' (pow_ne_zero 3 (Int.natAbs_ne_zero.mpr hu₁ne)), padicValNat.pow,
      padicValNat.eq_zero_of_not_dvd (fun h => hu₁ (fsd_int_dvd_iff_dvd_natAbs.mpr h)), hval1]
    omega
  have hAB2 : ((p ^ s : ℕ) : ℤ) ∣ ((1 - C) * u₁ ^ 3) - C * B1 := by
    have h := h2
    have : ((1 - C) * u₁ ^ 3) - C * B1 = -(C * B1 - (1 - C) * u₁ ^ 3) := by ring
    rw [this]
    exact dvd_neg.mpr h
  have hv2 := fsd_padicValNat_eq_of_dvd_sub (p := p) (e := s) (m := κ) hA2 hAB2 hA2v hκs
  refine ⟨hval1, ?_⟩
  have h3 : padicValNat p (C * B1).natAbs = padicValNat p B1.natAbs := by
    rw [Int.natAbs_mul, padicValNat.mul hCne' (Int.natAbs_ne_zero.mpr hB1),
      padicValNat.eq_zero_of_not_dvd (fun h => hC (fsd_int_dvd_iff_dvd_natAbs.mpr h))]
    omega
  rw [← h3]; exact hv2.2

/-- An integer coprime to `p` is a unit modulo `p ^ d`. -/
lemma fsd_isUnit_intCast {p d : ℕ} [Fact p.Prime] {z : ℤ} (h : ¬ p ∣ z.natAbs) :
    IsUnit ((z : ZMod (p ^ d))) := by
  have hcop : Nat.Coprime z.natAbs (p ^ d) := (Fact.out : p.Prime).coprime_pow_of_not_dvd h
  have hunit : IsUnit (((z.natAbs : ℕ) : ZMod (p ^ d))) := (ZMod.isUnit_iff_coprime _ _).mpr hcop
  rcases Int.natAbs_eq z with hz | hz
  · rw [hz]; simpa using hunit
  · rw [hz]
    have h2 : IsUnit (((↑z.natAbs : ℤ) : ZMod (p ^ d))) := by simpa using hunit
    simpa using h2.neg

/-- If `p ^ s ∣ p ^ κ * X` and `κ ≤ s`, then `p ^ (s - κ) ∣ X`. -/
lemma fsd_dvd_of_pow_mul {p κ s : ℕ} [Fact p.Prime] (hκle : κ ≤ s) {X : ℤ}
    (h : ((p ^ s : ℕ) : ℤ) ∣ ((p ^ κ : ℕ) : ℤ) * X) : ((p ^ (s - κ) : ℕ) : ℤ) ∣ X := by
  obtain ⟨w, hw⟩ := h
  have hcast : ((p ^ s : ℕ) : ℤ) = ((p ^ κ : ℕ) : ℤ) * ((p ^ (s - κ) : ℕ) : ℤ) := by
    rw [← Nat.cast_mul, ← pow_add, Nat.add_comm κ (s - κ), Nat.sub_add_cancel hκle]
  rw [hcast] at hw
  refine ⟨w, mul_left_cancel₀ (a := ((p ^ κ : ℕ) : ℤ)) ?_ ?_⟩
  · exact_mod_cast (pow_ne_zero κ (Fact.out : p.Prime).ne_zero)
  · rw [hw]; ring

/-- In a commutative ring: if `β₀ U₁³ = β₁ U₀³` with `U₀, U₁, β₀, β₁` units, then
`(U₀ / U₁)³ = β₀ / β₁`. -/
lemma fsd_cube_ratio {N : ℕ} {U₀ U₁ β₀ β₁ : ZMod N} (hU₀ : IsUnit U₀) (hU₁ : IsUnit U₁)
    (hβ₀ : IsUnit β₀) (hβ₁ : IsUnit β₁) (hrel : β₀ * U₁ ^ 3 = β₁ * U₀ ^ 3) :
    (U₀ * U₁⁻¹) ^ 3 = β₀ * β₁⁻¹ := by
  obtain ⟨u₀, hu₀⟩ := hU₀
  obtain ⟨u₁, hu₁⟩ := hU₁
  obtain ⟨w₀, hw₀⟩ := hβ₀
  obtain ⟨w₁, hw₁⟩ := hβ₁
  rw [← hu₀, ← hu₁, ← hw₀, ← hw₁] at hrel ⊢
  have h : w₀ * u₁ ^ 3 = w₁ * u₀ ^ 3 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_pow_eq_pow_val]
    exact hrel
  have h1 : w₁⁻¹ * (w₀ * u₁ ^ 3) = u₀ ^ 3 := by rw [h]; group
  have hgrp : (u₀ * u₁⁻¹) ^ 3 = w₀ * w₁⁻¹ := by
    calc (u₀ * u₁⁻¹) ^ 3 = u₀ ^ 3 * (u₁ ^ 3)⁻¹ := by rw [mul_pow, inv_pow]
      _ = (w₁⁻¹ * (w₀ * u₁ ^ 3)) * (u₁ ^ 3)⁻¹ := by rw [h1]
      _ = w₁⁻¹ * (w₀ * (u₁ ^ 3 * (u₁ ^ 3)⁻¹)) := by rw [mul_assoc, mul_assoc]
      _ = w₁⁻¹ * (w₀ * 1) := by rw [mul_inv_cancel]
      _ = w₀ * w₁⁻¹ := by rw [mul_one, mul_comm]
  calc ((u₀ : ZMod N) * ((u₁ : ZMod N))⁻¹) ^ 3 = ((u₀ * u₁⁻¹ : (ZMod N)ˣ) : ZMod N) ^ 3 := by
        rw [Units.val_mul, ZMod.inv_coe_unit]
    _ = (((u₀ * u₁⁻¹) ^ 3 : (ZMod N)ˣ) : ZMod N) := by rw [Units.val_pow_eq_pow_val]
    _ = ((w₀ * w₁⁻¹ : (ZMod N)ˣ) : ZMod N) := by rw [hgrp]
    _ = (w₀ : ZMod N) * ((w₁ : ZMod N))⁻¹ := by rw [Units.val_mul, ZMod.inv_coe_unit]

/-- **Case-B label computation.**  Let `p` be prime, `s ≥ 1`, `κ < s`.  Suppose `C`, `u₀`, `u₁` are
integers coprime to `p` and `B0, B1 ≠ 0` with `v_p(B0) = κ`, `B0 = p ^ κ * B0'`, `B1 = p ^ κ * B1'`,
such that modulo `p ^ s` we have `C B0 ≡ (1 - C) u₀³` and `C B1 ≡ (1 - C) u₁³`.  Then the ratio
`B0'/B1'` is a unit of `ZMod (p ^ (s - κ))` and the ratio `u₀/u₁` is one of its cube roots there. -/
theorem fsd_label_cube_root {p s κ : ℕ} [Fact p.Prime] (hs : 1 ≤ s) (hκs : κ < s)
    {B0 B1 C u₀ u₁ B0' B1' : ℤ} (hB0ne : B0 ≠ 0) (hB1ne : B1 ≠ 0)
    (hκ : padicValNat p B0.natAbs = κ)
    (hB0eq : B0 = (p : ℤ) ^ κ * B0') (hB1eq : B1 = (p : ℤ) ^ κ * B1')
    (hC : ¬ (p : ℤ) ∣ C) (hu₀ : ¬ (p : ℤ) ∣ u₀) (hu₁ : ¬ (p : ℤ) ∣ u₁)
    (h1 : ((p ^ s : ℕ) : ℤ) ∣ C * B0 - (1 - C) * u₀ ^ 3)
    (h2 : ((p ^ s : ℕ) : ℤ) ∣ C * B1 - (1 - C) * u₁ ^ 3) :
    IsUnit ((B0' : ZMod (p ^ (s - κ))) * ((B1' : ZMod (p ^ (s - κ)))⁻¹)) ∧
      ((u₀ : ZMod (p ^ (s - κ))) * ((u₁ : ZMod (p ^ (s - κ)))⁻¹)) ^ 3
        = (B0' : ZMod (p ^ (s - κ))) * ((B1' : ZMod (p ^ (s - κ)))⁻¹) := by
  have hκle : κ ≤ s := le_of_lt hκs
  have hval := fsd_caseB_val_eq (p := p) (s := s) (κ := κ) hs hB0ne hB1ne hκ hκs hC hu₀ hu₁ h1 h2
  -- `B0'` and `B1'` are coprime to `p`
  have hpB0' : ¬ (p : ℤ) ∣ B0' := by
    intro hdvd
    obtain ⟨B0'', hB0''⟩ := hdvd
    have h2' : ((p ^ (κ + 1) : ℕ) : ℤ) ∣ B0 :=
      ⟨B0'', by rw [hB0eq, hB0'', pow_succ, Int.natCast_mul, Int.natCast_pow]; ring⟩
    have : κ + 1 ≤ padicValNat p B0.natAbs :=
      (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hB0ne)).mp
        (fsd_int_dvd_iff_dvd_natAbs.mp h2')
    omega
  have hpB1' : ¬ (p : ℤ) ∣ B1' := by
    intro hdvd
    obtain ⟨B1'', hB1''⟩ := hdvd
    have h2' : ((p ^ (κ + 1) : ℕ) : ℤ) ∣ B1 :=
      ⟨B1'', by rw [hB1eq, hB1'', pow_succ, Int.natCast_mul, Int.natCast_pow]; ring⟩
    have : κ + 1 ≤ padicValNat p B1.natAbs :=
      (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hB1ne)).mp
        (fsd_int_dvd_iff_dvd_natAbs.mp h2')
    omega
  -- `p ^ κ ∣ 1 - C`
  have hDdvd : ((p ^ κ : ℕ) : ℤ) ∣ (1 - C) := by
    have hpκs : ((p ^ κ : ℕ) : ℤ) ∣ ((p ^ s : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr (pow_dvd_pow p hκle)
    have h3 : ((p ^ κ : ℕ) : ℤ) ∣ C * B0 - (1 - C) * u₀ ^ 3 := dvd_trans hpκs h1
    have h4 : ((p ^ κ : ℕ) : ℤ) ∣ C * B0 :=
      ⟨C * B0', by rw [hB0eq, Int.natCast_pow]; ring⟩
    have h5 : ((p ^ κ : ℕ) : ℤ) ∣ (1 - C) * u₀ ^ 3 := by
      have hkey : C * B0 - (C * B0 - (1 - C) * u₀ ^ 3) = (1 - C) * u₀ ^ 3 := by ring
      rw [← hkey]
      exact dvd_sub h4 h3
    have hu0cop : Nat.Coprime u₀.natAbs (p ^ κ) :=
      (Fact.out : p.Prime).coprime_pow_of_not_dvd
        (fun hh => hu₀ (fsd_int_dvd_iff_dvd_natAbs.mpr hh))
    have hna : p ^ κ ∣ ((1 - C) * u₀ ^ 3).natAbs := fsd_int_dvd_iff_dvd_natAbs.mp h5
    rw [Int.natAbs_mul, Int.natAbs_pow] at hna
    exact fsd_int_dvd_iff_dvd_natAbs.mpr
      (Nat.Coprime.dvd_of_dvd_mul_right (hu0cop.symm.pow_right 3) hna)
  obtain ⟨D, hD⟩ := hDdvd
  have hD' : 1 - C = (p : ℤ) ^ κ * D := by rw [hD]; push_cast; ring
  -- the two congruences modulo `p ^ (s - κ)`
  have hX1 : ((p ^ (s - κ) : ℕ) : ℤ) ∣ C * B0' - D * u₀ ^ 3 := by
    have hh : ((p ^ s : ℕ) : ℤ) ∣ ((p ^ κ : ℕ) : ℤ) * (C * B0' - D * u₀ ^ 3) := by
      have hxx := h1
      rw [hB0eq, hD'] at hxx
      have hkey : C * ((p : ℤ) ^ κ * B0') - ((p : ℤ) ^ κ * D) * u₀ ^ 3
          = (p : ℤ) ^ κ * (C * B0' - D * u₀ ^ 3) := by ring
      rw [hkey] at hxx
      exact hxx
    exact fsd_dvd_of_pow_mul hκle hh
  have hX2 : ((p ^ (s - κ) : ℕ) : ℤ) ∣ C * B1' - D * u₁ ^ 3 := by
    have hh : ((p ^ s : ℕ) : ℤ) ∣ ((p ^ κ : ℕ) : ℤ) * (C * B1' - D * u₁ ^ 3) := by
      have hxx := h2
      rw [hB1eq, hD'] at hxx
      have hkey : C * ((p : ℤ) ^ κ * B1') - ((p : ℤ) ^ κ * D) * u₁ ^ 3
          = (p : ℤ) ^ κ * (C * B1' - D * u₁ ^ 3) := by ring
      rw [hkey] at hxx
      exact hxx
    exact fsd_dvd_of_pow_mul hκle hh
  -- combine and cancel `C`
  have hcomb : ((p ^ (s - κ) : ℕ) : ℤ) ∣ C * (B0' * u₁ ^ 3 - B1' * u₀ ^ 3) := by
    have h := dvd_sub (dvd_mul_of_dvd_right hX1 (u₁ ^ 3)) (dvd_mul_of_dvd_right hX2 (u₀ ^ 3))
    have hkey : u₁ ^ 3 * (C * B0' - D * u₀ ^ 3) - u₀ ^ 3 * (C * B1' - D * u₁ ^ 3)
        = C * (B0' * u₁ ^ 3 - B1' * u₀ ^ 3) := by ring
    rw [hkey] at h
    exact h
  have hfinal : ((p ^ (s - κ) : ℕ) : ℤ) ∣ B0' * u₁ ^ 3 - B1' * u₀ ^ 3 := by
    have hCcop : Nat.Coprime C.natAbs (p ^ (s - κ)) :=
      (Fact.out : p.Prime).coprime_pow_of_not_dvd
        (fun hh => hC (fsd_int_dvd_iff_dvd_natAbs.mpr hh))
    have hna : p ^ (s - κ) ∣ (C * (B0' * u₁ ^ 3 - B1' * u₀ ^ 3)).natAbs :=
      fsd_int_dvd_iff_dvd_natAbs.mp hcomb
    rw [Int.natAbs_mul] at hna
    exact fsd_int_dvd_iff_dvd_natAbs.mpr (hCcop.symm.dvd_of_dvd_mul_left (by
      simpa only [Nat.mul_comm] using hna))
  -- turn the congruence into the cube-root relation
  have hrel : (B0' : ZMod (p ^ (s - κ))) * ((u₁ : ZMod (p ^ (s - κ))) ^ 3)
      = (B1' : ZMod (p ^ (s - κ))) * ((u₀ : ZMod (p ^ (s - κ))) ^ 3) := by
    have h0 : (((B0' * u₁ ^ 3 - B1' * u₀ ^ 3 : ℤ)) : ZMod (p ^ (s - κ))) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hfinal
    push_cast at h0
    exact sub_eq_zero.mp h0
  have hU₀ : IsUnit ((u₀ : ZMod (p ^ (s - κ)))) :=
    fsd_isUnit_intCast (fun hh => hu₀ (fsd_int_dvd_iff_dvd_natAbs.mpr hh))
  have hU₁ : IsUnit ((u₁ : ZMod (p ^ (s - κ)))) :=
    fsd_isUnit_intCast (fun hh => hu₁ (fsd_int_dvd_iff_dvd_natAbs.mpr hh))
  have hβ₀ : IsUnit ((B0' : ZMod (p ^ (s - κ)))) :=
    fsd_isUnit_intCast (fun hh => hpB0' (fsd_int_dvd_iff_dvd_natAbs.mpr hh))
  have hβ₁ : IsUnit ((B1' : ZMod (p ^ (s - κ)))) :=
    fsd_isUnit_intCast (fun hh => hpB1' (fsd_int_dvd_iff_dvd_natAbs.mpr hh))
  have hρinv : IsUnit (((B1' : ZMod (p ^ (s - κ))))⁻¹) := by
    obtain ⟨w, hw⟩ := hβ₁
    rw [← hw, ZMod.inv_coe_unit]
    exact (w⁻¹).isUnit
  exact ⟨hβ₀.mul hρinv, fsd_cube_ratio hU₀ hU₁ hβ₀ hβ₁ hrel⟩


/-- **Degenerate case, single prime (modulus `p ^ (k - v_p 2)`).**  If some entry of `b` equals `a1`,
then evaluating the pencil relation at `-a1` (a common root of `f_a` and `f_b`) forces the pencil
unit to be `1`, so the two cubics agree and their `X ^ 2` coefficients, i.e. their elementary
symmetric functions `e₁`, agree: `a2 = e₁(b) - a0 - a1`. -/
theorem fsd_degenerate_class_K {p k : ℕ} [Fact p.Prime] (a0 a1 : ℕ) (b : Fin 3 → ℕ)
    (h01 : a0 ≠ a1) (hbl : ∃ l : Fin 3, b l = a1) {a2 : ℕ}
    (ha2 : fcd_frameAdm p k a0 a1 b a2) :
    (a2 : ZMod (p ^ (k - padicValNat p 2)))
      = (((b 0 : ℤ) + (b 1 : ℤ) + (b 2 : ℤ) - (a0 : ℤ) - (a1 : ℤ) : ℤ)
          : ZMod (p ^ (k - padicValNat p 2))) := by
  obtain ⟨y, hy, hN, hN'⟩ := ha2
  set K := k - padicValNat p 2 with hK
  obtain ⟨c, hcunit, hpencil⟩ := critN_pencil (p := p) (k := k) ![a0, a1, a2] b y hy hN hN'
  have hev := congrArg (fun Q : Polynomial (ZMod (p ^ K)) =>
    Polynomial.eval (-(a1 : ZMod (p ^ K))) Q) hpencil
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X] at hev
  have hL : Polynomial.eval (-(a1 : ZMod (p ^ K)))
      ((cubicZ ![a0, a1, a2]).map (Int.castRingHom (ZMod (p ^ K)))) = 0 := by
    have h := fcd_eval_cubicZ_map_self ![a0, a1, a2] (p ^ K) 1
    simpa using h
  have hb1 : Polynomial.eval (-(a1 : ZMod (p ^ K)))
      ((cubicZ b).map (Int.castRingHom (ZMod (p ^ K)))) = 0 := by
    rw [fcd_eval_cubicZ_map]
    obtain ⟨l, hl⟩ := hbl
    refine Finset.prod_eq_zero (Finset.mem_univ l) ?_
    simp [hl]
  rw [hL, hb1, mul_zero, zero_add] at hev
  have hunit : IsUnit ((-(a1 : ZMod (p ^ K)) - (y : ZMod (p ^ K))) ^ 3) := by
    have h1 : IsUnit (((y + a1 : ℕ)) : ZMod (p ^ K)) :=
      fcd_isUnit_natCast_zmod_of_not_dvd (p := p) (K := K) (hy 1).1
    have h2 : (-(a1 : ZMod (p ^ K)) - (y : ZMod (p ^ K)))
        = -(((y + a1 : ℕ)) : ZMod (p ^ K)) := by push_cast; ring
    rw [h2]
    exact (h1.neg).pow 3
  have hc1 : c = 1 := by
    have hz : (1 - c) * ((-(a1 : ZMod (p ^ K)) - (y : ZMod (p ^ K))) ^ 3) = 0 := hev.symm
    exact (sub_eq_zero.mp ((IsUnit.mul_left_eq_zero hunit).mp hz)).symm
  have hp : (cubicZ ![a0, a1, a2]).map (Int.castRingHom (ZMod (p ^ K)))
      = (cubicZ b).map (Int.castRingHom (ZMod (p ^ K))) := by
    have h := hpencil
    rw [hc1] at h
    simpa using h
  have hcoeff := congrArg (fun Q : Polynomial (ZMod (p ^ K)) => Q.coeff 2) hp
  rw [Polynomial.coeff_map, Polynomial.coeff_map, fcd_cubicZ_coeff_two, fcd_cubicZ_coeff_two]
    at hcoeff
  have hsum : ((a0 : ZMod (p ^ K)) + (a1 : ZMod (p ^ K)) + (a2 : ZMod (p ^ K)))
      = ((b 0 : ZMod (p ^ K)) + (b 1 : ZMod (p ^ K)) + (b 2 : ZMod (p ^ K))) := by
    have h := hcoeff
    simp only [fcd_esymm3_zero] at h
    push_cast at h
    simpa using h
  have h : ((b 0 : ℤ) + (b 1 : ℤ) + (b 2 : ℤ) - (a0 : ℤ) - (a1 : ℤ) : ℤ)
      = ((b 0 : ℤ) + (b 1 : ℤ) + (b 2 : ℤ)) - ((a0 : ℤ) + (a1 : ℤ)) := by ring
  rw [h]
  simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast]
  linear_combination hsum

/-- **Degenerate case, single prime** (`a1` occurs among the entries of `b`): every admissible
`a2` lies in the single class `e₁(b) - a0 - a1` modulo
`p ^ (max 0 (k - v_p 2 - v_p (a0 - a1)))`. -/
theorem fsd_degenerate_class {p k : ℕ} [Fact p.Prime] (a0 a1 : ℕ) (b : Fin 3 → ℕ)
    (h01 : a0 ≠ a1) (hbl : ∃ l : Fin 3, b l = a1) {a2 : ℕ}
    (ha2 : fcd_frameAdm p k a0 a1 b a2) :
    (a2 : ZMod (p ^ (max 0 (k - padicValNat p 2
        - padicValNat p (((a0 : ℤ) - (a1 : ℤ)).natAbs)))))
      = (((b 0 : ℤ) + (b 1 : ℤ) + (b 2 : ℤ) - (a0 : ℤ) - (a1 : ℤ) : ℤ)
          : ZMod (p ^ (max 0 (k - padicValNat p 2
            - padicValNat p (((a0 : ℤ) - (a1 : ℤ)).natAbs))))) := by
  classical
  set E : ℕ := max 0 (k - padicValNat p 2
    - padicValNat p (((a0 : ℤ) - (a1 : ℤ)).natAbs)) with hE
  set mu : ℤ := (b 0 : ℤ) + (b 1 : ℤ) + (b 2 : ℤ) - (a0 : ℤ) - (a1 : ℤ) with hmu
  have hle : E ≤ k - padicValNat p 2 := by
    rw [hE]; exact max_le (Nat.zero_le _) (Nat.sub_le _ _)
  have hdvd : p ^ E ∣ p ^ (k - padicValNat p 2) := pow_dvd_pow p hle
  have hK := fsd_degenerate_class_K (p := p) (k := k) a0 a1 b h01 hbl ha2
  rw [← hmu] at hK
  have h2 : ((((a2 : ℤ) - mu : ℤ)) : ZMod (p ^ (k - padicValNat p 2))) = 0 := by
    rw [Int.cast_sub, Int.cast_natCast, hK, sub_self]
  have hdiv0 : (((p ^ (k - padicValNat p 2) : ℕ)) : ℤ) ∣ ((a2 : ℤ) - mu) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2
  have hdiv1 : ((p ^ E : ℕ) : ℤ) ∣ ((a2 : ℤ) - mu) :=
    dvd_trans (Int.natCast_dvd_natCast.mpr hdvd) hdiv0
  rw [← Int.cast_natCast (R := ZMod (p ^ E)) a2]
  rw [← sub_eq_zero, ← Int.cast_sub]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv1

/-- **Case A (single prime).**  If `p ^ (k - v_p 2) ∣ f_b(-a0)`, then every admissible `a2` lies in
the single class `e₁(b) - a0 - a1` modulo `p ^ (max 0 (k - v_p 2 - v_p (a0 - a1)))`. -/
theorem frameAdm_prime_class_dvd {p k : ℕ} [Fact p.Prime] (a0 a1 : ℕ) (b : Fin 3 → ℕ)
    (h01 : a0 ≠ a1) (hb : ∀ l : Fin 3, a1 ≠ b l)
    (hAi : ((p ^ (k - padicValNat p 2) : ℕ) : ℤ)
      ∣ ∏ l : Fin 3, ((b l : ℤ) - (a0 : ℤ))) :
    ∃ R : Finset (ZMod (p ^ (max 0 (k - padicValNat p 2
        - padicValNat p (((a0 : ℤ) - (a1 : ℤ)).natAbs))))),
      R.card ≤ 3 ∧ ∀ a2 : ℕ, fcd_frameAdm p k a0 a1 b a2 →
        (a2 : ZMod (p ^ (max 0 (k - padicValNat p 2
          - padicValNat p (((a0 : ℤ) - (a1 : ℤ)).natAbs))))) ∈ R := by
  classical
  set E : ℕ := max 0 (k - padicValNat p 2
    - padicValNat p (((a0 : ℤ) - (a1 : ℤ)).natAbs)) with hE
  have hle : E ≤ k - padicValNat p 2 := by
    rw [hE]; exact max_le (Nat.zero_le _) (Nat.sub_le _ _)
  have hdvd : p ^ E ∣ p ^ (k - padicValNat p 2) := pow_dvd_pow p hle
  refine ⟨{(((b 0 : ℤ) + (b 1 : ℤ) + (b 2 : ℤ) - (a0 : ℤ) - (a1 : ℤ) : ℤ) : ZMod (p ^ E))},
    by simp, ?_⟩
  intro a2 ha2
  rw [Finset.mem_singleton]
  set r1 : ℤ := (b 0 : ℤ) + (b 1 : ℤ) + (b 2 : ℤ) - (a0 : ℤ) - (a1 : ℤ) with hr1
  have h1 := fcd_frame_class_pow_dvd (p := p) (k := k) a0 a1 b h01 hb hAi ha2
  rw [← hr1] at h1
  have h2 : ((((a2 : ℤ) - r1 : ℤ)) : ZMod (p ^ (k - padicValNat p 2))) = 0 := by
    rw [Int.cast_sub, Int.cast_natCast, h1, sub_self]
  have hdiv0 : (((p ^ (k - padicValNat p 2) : ℕ)) : ℤ) ∣ ((a2 : ℤ) - r1) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2
  have hdiv1 : ((p ^ E : ℕ) : ℤ) ∣ ((a2 : ℤ) - r1) :=
    dvd_trans (Int.natCast_dvd_natCast.mpr hdvd) hdiv0
  rw [← Int.cast_natCast (R := ZMod (p ^ E)) a2]
  rw [← sub_eq_zero, ← Int.cast_sub]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv1

/-- **Case B (single prime).**  If `p ^ (k - v_p 2) ∤ f_b(-a0)`, the admissible `a2` are confined
to the at most three classes modulo `p ^ (max 0 (k - v_p 2 - v_p (a0 - a1)))` determined by the
cube roots of the unit `B₀' / B₁'` (`critN_pencil` written out at the two roots `-a0`, `-a1`). -/
theorem frameAdm_prime_class_not_dvd {p k : ℕ} [Fact p.Prime] (a0 a1 : ℕ) (b : Fin 3 → ℕ)
    (h01 : a0 ≠ a1) (hb : ∀ l : Fin 3, a1 ≠ b l)
    (hAi : ¬ ((p ^ (k - padicValNat p 2) : ℕ) : ℤ)
      ∣ ∏ l : Fin 3, ((b l : ℤ) - (a0 : ℤ))) :
    ∃ R : Finset (ZMod (p ^ (max 0 (k - padicValNat p 2
        - padicValNat p (((a0 : ℤ) - (a1 : ℤ)).natAbs))))),
      R.card ≤ 3 ∧ ∀ a2 : ℕ, fcd_frameAdm p k a0 a1 b a2 →
        (a2 : ZMod (p ^ (max 0 (k - padicValNat p 2
          - padicValNat p (((a0 : ℤ) - (a1 : ℤ)).natAbs))))) ∈ R := by
  classical
  set s : ℕ := k - padicValNat p 2 with hs
  set iota : ℕ := padicValNat p (((a0 : ℤ) - (a1 : ℤ)).natAbs) with hi
  set E : ℕ := max 0 (s - iota) with hE
  set B0 : ℤ := ∏ l : Fin 3, ((b l : ℤ) - (a0 : ℤ)) with hB0
  set B1 : ℤ := ∏ l : Fin 3, ((b l : ℤ) - (a1 : ℤ)) with hB1
  have hEmax : E = s - iota := by rw [hE, Nat.zero_max]
  by_cases hempty : ∃ a2 : ℕ, fcd_frameAdm p k a0 a1 b a2
  swap
  · refine ⟨∅, by simp, ?_⟩
    intro a2 ha2
    exact absurd ⟨a2, ha2⟩ hempty
  obtain ⟨x₀, hx₀⟩ := hempty
  -- the choice data attached to an admissible `a2`
  have hdata : ∀ a2 : ℕ, fcd_frameAdm p k a0 a1 b a2 →
      ∃ y : ℕ, ∃ C : ℤ, FrameAdmGood p k a0 a1 b a2 y C := by
    intro a2 ha2
    obtain ⟨y, hy, hN, hN'⟩ := ha2
    obtain ⟨C, hC, h1, h2, h3⟩ := fsd_pencil_frame_congr (p := p) (k := k) a0 a1 a2 b y hy hN hN'
    exact ⟨y, C, hy, hC, h1, h2, h3⟩
  let Y : ℕ → ℕ := fun a2 =>
    if h : fcd_frameAdm p k a0 a1 b a2 then Classical.choose (hdata a2 h) else 0
  let Cc : ℕ → ℤ := fun a2 =>
    if h : fcd_frameAdm p k a0 a1 b a2 then
      Classical.choose (Classical.choose_spec (hdata a2 h)) else 0
  have hYeq : ∀ a2 (h : fcd_frameAdm p k a0 a1 b a2),
      Y a2 = Classical.choose (hdata a2 h) := by
    intro a2 h; simp only [Y]; exact dif_pos h
  have hCceq : ∀ a2 (h : fcd_frameAdm p k a0 a1 b a2),
      Cc a2 = Classical.choose (Classical.choose_spec (hdata a2 h)) := by
    intro a2 h; simp only [Cc]; exact dif_pos h
  have hgood : ∀ a2 (h : fcd_frameAdm p k a0 a1 b a2),
      FrameAdmGood p k a0 a1 b a2 (Y a2) (Cc a2) := by
    intro a2 h
    rw [hYeq a2 h, hCceq a2 h]
    exact Classical.choose_spec (Classical.choose_spec (hdata a2 h))
  have hY0z : ∀ a2 (h : fcd_frameAdm p k a0 a1 b a2),
      ¬ (p : ℤ) ∣ (((Y a2 + a0 : ℕ)) : ℤ) := fun a2 h hh =>
    ((hgood a2 h).1 0).1 (Int.natCast_dvd_natCast.mp hh)
  have hY1z : ∀ a2 (h : fcd_frameAdm p k a0 a1 b a2),
      ¬ (p : ℤ) ∣ (((Y a2 + a1 : ℕ)) : ℤ) := fun a2 h hh =>
    ((hgood a2 h).1 1).1 (Int.natCast_dvd_natCast.mp hh)
  have hY1 : ∀ a2 (h : fcd_frameAdm p k a0 a1 b a2), ¬ p ∣ Y a2 + a1 :=
    fun a2 h => ((hgood a2 h).1 1).1
  -- `B0`, `B1` are nonzero, `κ = v_p B0` and `κ < s`
  have hB0ne : B0 ≠ 0 := by
    intro h0
    exact hAi (by rw [h0]; exact dvd_zero _)
  have hB1ne : B1 ≠ 0 := by
    rw [hB1, Fin.prod_univ_three]
    exact mul_ne_zero
      (mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast (Ne.symm (hb 0))))
        (sub_ne_zero.mpr (by exact_mod_cast (Ne.symm (hb 1)))))
      (sub_ne_zero.mpr (by exact_mod_cast (Ne.symm (hb 2))))
  set κ : ℕ := padicValNat p B0.natAbs with hκ
  have hκlt : κ < s := by
    by_contra hcon
    have hle : s ≤ κ := by omega
    have hdiv : ((p ^ s : ℕ) : ℤ) ∣ B0 :=
      fsd_int_dvd_iff_dvd_natAbs.mpr ((padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hB0ne)).mpr hle)
    exact hAi hdiv
  have hs1 : 1 ≤ s := by omega
  -- the reference witness `x₀` gives `v_p B1 = κ`
  have hval := fsd_caseB_val_eq (p := p) (s := s) (κ := κ) hs1 hB0ne hB1ne hκ.symm hκlt
    (hgood x₀ hx₀).2.1 (hY0z x₀ hx₀) (hY1z x₀ hx₀) (hgood x₀ hx₀).2.2.1 (hgood x₀ hx₀).2.2.2.1
  obtain ⟨B0', hB0eq⟩ := dvd_def.mp (show (p : ℤ) ^ κ ∣ B0 from by
    have h : ((p ^ κ : ℕ) : ℤ) ∣ B0 :=
      fsd_int_dvd_iff_dvd_natAbs.mpr ((padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hB0ne)).mpr (le_of_eq hκ.symm))
    simpa only [Int.natCast_pow] using h)
  obtain ⟨B1', hB1eq⟩ := dvd_def.mp (show (p : ℤ) ^ κ ∣ B1 from by
    have h : ((p ^ κ : ℕ) : ℤ) ∣ B1 :=
      fsd_int_dvd_iff_dvd_natAbs.mpr ((padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hB1ne)).mpr (le_of_eq hval.2.symm))
    simpa only [Int.natCast_pow] using h)
  set ρ : ZMod (p ^ (s - κ)) :=
    (B0' : ZMod (p ^ (s - κ))) * ((B1' : ZMod (p ^ (s - κ)))⁻¹) with hρ
  have hroot := fsd_label_cube_root (p := p) (s := s) (κ := κ) hs1 hκlt hB0ne hB1ne hκ.symm
    hB0eq hB1eq (hgood x₀ hx₀).2.1 (hY0z x₀ hx₀) (hY1z x₀ hx₀)
    (hgood x₀ hx₀).2.2.1 (hgood x₀ hx₀).2.2.2.1
  have hTcard : ((Finset.univ : Finset (ZMod (p ^ (s - κ)))).filter
      (fun z => z ^ 3 = ρ)).card ≤ 3 := cube_root_card_le_three p (s - κ) ρ hroot.1
  -- the label and the fibre condition
  let lab : ℕ → ZMod (p ^ (s - κ)) := fun a2 =>
    if _ : fcd_frameAdm p k a0 a1 b a2 then
      (((Y a2 + a0 : ℕ)) : ZMod (p ^ (s - κ))) *
        ((((Y a2 + a1 : ℕ)) : ZMod (p ^ (s - κ))))⁻¹
    else 0
  have hlabel : ∀ a2 (h : fcd_frameAdm p k a0 a1 b a2),
      lab a2 ∈ (Finset.univ : Finset (ZMod (p ^ (s - κ)))).filter (fun z => z ^ 3 = ρ) := by
    intro a2 h
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hr := fsd_label_cube_root (p := p) (s := s) (κ := κ) hs1 hκlt hB0ne hB1ne hκ.symm
      hB0eq hB1eq (hgood a2 h).2.1 (hY0z a2 h) (hY1z a2 h)
      (hgood a2 h).2.2.1 (hgood a2 h).2.2.2.1
    have hcube := hr.2
    simp only [Int.cast_natCast] at hcube
    rw [hρ]
    simp only [lab, dif_pos h]
    exact hcube
  have hfib : ∀ a2 a2' : ℕ, fcd_frameAdm p k a0 a1 b a2 → fcd_frameAdm p k a0 a1 b a2' →
      lab a2 = lab a2' → (a2 : ZMod (p ^ E)) = (a2' : ZMod (p ^ E)) := by
    intro a2 a2' ha2 ha2' heq
    have hratio : (((Y a2 + a0 : ℕ)) : ZMod (p ^ (s - κ))) *
          ((((Y a2 + a1 : ℕ)) : ZMod (p ^ (s - κ))))⁻¹
        = (((Y a2' + a0 : ℕ)) : ZMod (p ^ (s - κ))) *
          ((((Y a2' + a1 : ℕ)) : ZMod (p ^ (s - κ))))⁻¹ := by
      have h := heq
      simp only [lab, dif_pos ha2, dif_pos ha2'] at h
      exact h
    have hsub : ((p ^ ((s - κ) - iota) : ℕ) : ℤ) ∣ ((Y a2 : ℤ) - (Y a2' : ℤ)) :=
      fsd_label_modEq_y_sub (p := p) (m := s - κ) (by omega) h01 (hY1 a2 ha2) (hY1 a2' ha2') hratio
    have hexp : E - κ = (s - κ) - iota := by
      rw [hEmax]; omega
    have hud : ((p ^ (E - κ) : ℕ) : ℤ)
        ∣ (((Y a2 + a0 : ℕ)) : ℤ) - (((Y a2' + a0 : ℕ)) : ℤ) := by
      rw [hexp]
      convert hsub using 1
      push_cast
      ring
    have h2a : ((p ^ s : ℕ) : ℤ) ∣ (((a0 + a1 + a2 : ℕ)) : ℤ)
        - (Cc a2 * (((b 0 + b 1 + b 2 : ℕ)) : ℤ)
          - 3 * (1 - Cc a2) * ((((Y a2 + a0 : ℕ)) : ℤ) - (a0 : ℤ))) := by
      convert (hgood a2 ha2).2.2.2.2 using 1
      push_cast
      ring
    have h2b : ((p ^ s : ℕ) : ℤ) ∣ (((a0 + a1 + a2' : ℕ)) : ℤ)
        - (Cc a2' * (((b 0 + b 1 + b 2 : ℕ)) : ℤ)
          - 3 * (1 - Cc a2') * ((((Y a2' + a0 : ℕ)) : ℤ) - (a0 : ℤ))) := by
      convert (hgood a2' ha2').2.2.2.2 using 1
      push_cast
      ring
    have hstep := fsd_frame_congruence_step (p := p) (s := s) (E := E) (κ := κ)
      (B0 := B0) (E1 := (((b 0 + b 1 + b 2 : ℕ)) : ℤ)) (A0 := (a0 : ℤ))
      (u := (((Y a2 + a0 : ℕ)) : ℤ)) (u' := (((Y a2' + a0 : ℕ)) : ℤ))
      (C := Cc a2) (C' := Cc a2')
      (a2 := (((a0 + a1 + a2 : ℕ)) : ℤ)) (a2' := (((a0 + a1 + a2' : ℕ)) : ℤ))
      hs1 (by rw [hEmax]; exact Nat.sub_le _ _) hB0ne hκ.symm (hY0z a2 ha2) (hY0z a2' ha2') hud
      (hgood a2 ha2).2.2.1 (hgood a2' ha2').2.2.1 h2a h2b
    have hfin : ((p ^ E : ℕ) : ℤ) ∣ ((a2 : ℤ) - (a2' : ℤ)) := by
      convert hstep using 1
      push_cast
      ring
    rw [← Int.cast_natCast (R := ZMod (p ^ E)) a2, ← Int.cast_natCast (R := ZMod (p ^ E)) a2',
      ← sub_eq_zero, ← Int.cast_sub]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hfin
  -- the covering set of residues modulo `p ^ E`
  refine ⟨((Finset.univ : Finset (ZMod (p ^ (s - κ)))).filter (fun z => z ^ 3 = ρ)).image
    (fun z => if h : ∃ a2 : ℕ, fcd_frameAdm p k a0 a1 b a2 ∧ lab a2 = z
      then ((Classical.choose h : ℕ) : ZMod (p ^ E)) else 0), ?_, ?_⟩
  · calc _ ≤ ((Finset.univ : Finset (ZMod (p ^ (s - κ)))).filter (fun z => z ^ 3 = ρ)).card :=
        Finset.card_image_le
      _ ≤ 3 := hTcard
  · intro a2 ha2
    simp only [Finset.mem_image]
    refine ⟨lab a2, hlabel a2 ha2, ?_⟩
    have hex : ∃ a2' : ℕ, fcd_frameAdm p k a0 a1 b a2' ∧ lab a2' = lab a2 := ⟨a2, ha2, rfl⟩
    rw [dif_pos hex]
    exact hfib (Classical.choose hex) a2 (Classical.choose_spec hex).1 ha2
      (Classical.choose_spec hex).2

/-- **Assembly step.**  Suppose that for every prime `p ∣ d` the `a2` admissible at level
`p ^ (v_p d)` are confined to at most three classes modulo `q p = p ^ (max 0 (v_p d - v_p 2 -
v_p (a0 - a1)))`.  Then the `DL_d`-admissible `a2 ∈ [1, H]` lie in at most `3 ^ ω(d)` classes
modulo `M = ∏_{p ∣ d} q p`, hence number at most `3 ^ ω(d) * (H / M + 1)`. -/
theorem frameStepD_assembly {d : ℕ} (hd : 0 < d) (a0 a1 : ℕ) (b : Fin 3 → ℕ) (H : ℕ)
    (h01 : a0 ≠ a1)
    (hcls : ∀ p ∈ d.primeFactors, ∃ R : Finset (ZMod (p ^ (max 0 (d.factorization p
        - padicValNat p 2
        - padicValNat p (((a0 : ℤ) - (a1 : ℤ)).natAbs))))),
      R.card ≤ 3 ∧ ∀ a2 : ℕ, fcd_frameAdm p (d.factorization p) a0 a1 b a2 →
        (a2 : ZMod (p ^ (max 0 (d.factorization p - padicValNat p 2
          - padicValNat p (((a0 : ℤ) - (a1 : ℤ)).natAbs))))) ∈ R) :
    (frameStepSetD d H a0 a1 b).card
      ≤ 3 ^ d.primeFactors.card *
          (H / (∏ p ∈ d.primeFactors, p ^ (max 0 (d.factorization p - padicValNat p 2
            - padicValNat p (((a0 : ℤ) - (a1 : ℤ)).natAbs)))) + 1) := by
  classical
  let q : ℕ → ℕ := fun p => p ^ (max 0 (d.factorization p - padicValNat p 2
      - padicValNat p (((a0 : ℤ) - (a1 : ℤ)).natAbs)))
  let M : ℕ := ∏ p ∈ d.primeFactors, q p
  have hMpos : 0 < M := by
    refine Finset.prod_pos (fun p hp => ?_)
    exact pow_pos (Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp)) _
  have key : ∀ p : ℕ, ∃ R : Finset (ZMod (q p)),
      (p ∈ d.primeFactors → R.card ≤ 3) ∧
      (p ∈ d.primeFactors → ∀ a2 : ℕ, fcd_frameAdm p (d.factorization p) a0 a1 b a2 →
        (a2 : ZMod (q p)) ∈ R) := by
    intro p
    by_cases hp : p ∈ d.primeFactors
    · obtain ⟨R, h1, h2⟩ := hcls p hp
      exact ⟨R, fun _ => h1, fun _ => h2⟩
    · exact ⟨∅, fun h => absurd h hp, fun h => absurd h hp⟩
  let R : (p : ℕ) → Finset (ZMod (q p)) := fun p => (key p).choose
  have hRcard : ∀ p ∈ d.primeFactors, (R p).card ≤ 3 := fun p hp => (key p).choose_spec.1 hp
  have hRmem : ∀ p ∈ d.primeFactors, ∀ a2 : ℕ, fcd_frameAdm p (d.factorization p) a0 a1 b a2 →
      (a2 : ZMod (q p)) ∈ R p := fun p hp a2 ha2 => (key p).choose_spec.2 hp a2 ha2
  let T : Finset ℕ := (Finset.range M).filter
      (fun r => ∀ p ∈ d.primeFactors, (r : ZMod (q p)) ∈ R p)
  have hSdef : ∀ a2 : ℕ, a2 ∈ frameStepSetD d H a0 a1 b ↔ a2 ∈ Finset.Icc 1 H ∧ ∃ y : ℕ,
      (∀ p ∈ d.primeFactors, UnitAt p y ![a0, a1, a2] b)
        ∧ ((d : ℤ) ∣ (critN ![a0, a1, a2] b).eval (y : ℤ))
        ∧ ((d : ℤ) ∣ (Polynomial.derivative (critN ![a0, a1, a2] b)).eval (y : ℤ)) := by
    intro a2
    rw [frameStepSetD]
    exact Finset.mem_filter
  have hadm : ∀ a2 : ℕ, a2 ∈ frameStepSetD d H a0 a1 b → ∀ p ∈ d.primeFactors,
      fcd_frameAdm p (d.factorization p) a0 a1 b a2 := by
    intro a2 ha2 p hp
    obtain ⟨-, y, hunit, hN, hN'⟩ := (hSdef a2).mp ha2
    have hpd : ((p ^ d.factorization p : ℕ) : ℤ) ∣ (d : ℤ) :=
      Int.natCast_dvd_natCast.mpr (Nat.ordProj_dvd d p)
    exact ⟨y, hunit p hp, dvd_trans hpd hN, dvd_trans hpd hN'⟩
  have hTcard : T.card ≤ 3 ^ d.primeFactors.card := by
    have hmaps : Set.MapsTo (fun r : ℕ => fun p (hp : p ∈ d.primeFactors) => (r : ZMod (q p)))
        ↑T ↑(Finset.pi d.primeFactors R) := by
      intro r hr
      rw [Finset.mem_coe] at hr
      simp only [T, Finset.mem_filter] at hr
      exact Finset.mem_pi.mpr (fun p hp => hr.2 p hp)
    have hinj : Set.InjOn (fun r : ℕ => fun p (hp : p ∈ d.primeFactors) => (r : ZMod (q p)))
        ↑T := by
      intro r hr r' hr' heq
      rw [Finset.mem_coe] at hr hr'
      simp only [T, Finset.mem_filter] at hr hr'
      have hdvd : ∀ p ∈ d.primeFactors, ((q p : ℕ) : ℤ) ∣ ((r : ℤ) - (r' : ℤ)) := by
        intro p hp
        have h : (r : ZMod (q p)) = (r' : ZMod (q p)) := congrFun (congrFun heq p) hp
        have h2 : (((r : ℤ) - (r' : ℤ) : ℤ) : ZMod (q p)) = 0 := by
          rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, h, sub_self]
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd ((r : ℤ) - (r' : ℤ)) (q p)).mp h2
      have hMdvd : (M : ℤ) ∣ ((r : ℤ) - (r' : ℤ)) :=
        prod_primePowers_dvd d.primeFactors
          (fun p hp => Nat.prime_of_mem_primeFactors hp)
          (fun p => max 0 (d.factorization p - padicValNat p 2
            - padicValNat p (((a0 : ℤ) - (a1 : ℤ)).natAbs))) hdvd
      have habs : |((r : ℤ) - (r' : ℤ))| < (M : ℤ) := by
        have hrl : (r : ℤ) < (M : ℤ) := by exact_mod_cast Finset.mem_range.mp hr.1
        have hr'l : (r' : ℤ) < (M : ℤ) := by exact_mod_cast Finset.mem_range.mp hr'.1
        rw [abs_lt]
        constructor <;> omega
      have hzero : ((r : ℤ) - (r' : ℤ)) = 0 := Int.eq_zero_of_abs_lt_dvd hMdvd habs
      exact_mod_cast (sub_eq_zero.mp hzero)
    calc T.card ≤ (Finset.pi d.primeFactors R).card :=
          Finset.card_le_card_of_injOn _ hmaps hinj
      _ = ∏ p ∈ d.primeFactors, (R p).card := Finset.card_pi _ _
      _ ≤ ∏ p ∈ d.primeFactors, 3 :=
            Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _) (fun p hp => hRcard p hp)
      _ = 3 ^ d.primeFactors.card := Finset.prod_const 3
  have hcover : frameStepSetD d H a0 a1 b ⊆ T.biUnion
      (fun r => (Finset.Icc 1 H).filter (fun a2 => a2 % M = r)) := by
    intro a2 ha2
    rw [Finset.mem_biUnion]
    obtain ⟨ha2I, -⟩ := (hSdef a2).mp ha2
    refine ⟨a2 % M, ?_, ?_⟩
    · simp only [T, Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt _ hMpos, fun p hp => ?_⟩
      have hmem := hRmem p hp a2 (hadm a2 ha2 p hp)
      have hqpM : q p ∣ M := Finset.dvd_prod_of_mem _ hp
      have hclass : ((a2 % M : ℕ) : ZMod (q p)) = (a2 : ZMod (q p)) := by
        calc ((a2 % M : ℕ) : ZMod (q p))
            = (((a2 % M) % q p : ℕ) : ZMod (q p)) := (ZMod.natCast_mod (a2 % M) (q p)).symm
          _ = ((a2 % q p : ℕ) : ZMod (q p)) := by rw [Nat.mod_mod_of_dvd a2 hqpM]
          _ = (a2 : ZMod (q p)) := ZMod.natCast_mod a2 (q p)
      simpa only [hclass] using hmem
    · exact Finset.mem_filter.mpr ⟨ha2I, rfl⟩
  calc (frameStepSetD d H a0 a1 b).card
      ≤ (T.biUnion (fun r => (Finset.Icc 1 H).filter (fun a2 => a2 % M = r))).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ r ∈ T, ((Finset.Icc 1 H).filter (fun a2 => a2 % M = r)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ r ∈ T, (H / M + 1) :=
        Finset.sum_le_sum (fun r _ => fsd_card_Icc_filter_mod_eq_le)
    _ = T.card * (H / M + 1) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 3 ^ d.primeFactors.card * (H / M + 1) := Nat.mul_le_mul_right _ hTcard

/-- Multi-prime frame step, no `a1 ∉ b` hypothesis.  Fix `d > 0` and a "frame" `(a0, a1, b0, b1, b2)` with only `a0 ≠ a1`.  Then the possible third `a`-entries `a2 ∈ [1,H]` for which `![a0,a1,a2]`, `b` is `DL_d`-double-critical (the set `frameStepSetD d H a0 a1 b`) number at most `3^(d.primeFactors.card) * (H/M + 1)` with `M = ∏_{p ∣ d} p^(max 0 (v_p(d) - v_p(2) - v_p(a0-a1)))`. -/
theorem frame_step_card_d_nohb {d : ℕ} (hd : 0 < d) (a0 a1 : ℕ) (b : Fin 3 → ℕ) (H : ℕ)
    (h01 : a0 ≠ a1) :
    (frameStepSetD d H a0 a1 b).card
      ≤ 3 ^ d.primeFactors.card *
          (H / (∏ p ∈ d.primeFactors, p ^ (max 0 (d.factorization p - padicValNat p 2
            - padicValNat p (((a0 : ℤ) - (a1 : ℤ)).natAbs)))) + 1) := by
  classical
  by_cases hbl : ∃ l : Fin 3, b l = a1
  · refine frameStepD_assembly hd a0 a1 b H h01 ?_
    intro p hp
    haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    refine ⟨({(((b 0 : ℤ) + (b 1 : ℤ) + (b 2 : ℤ) - (a0 : ℤ) - (a1 : ℤ) : ℤ)
        : ZMod (p ^ (max 0 (d.factorization p - padicValNat p 2
          - padicValNat p (((a0 : ℤ) - (a1 : ℤ)).natAbs))))) } : Finset _), by simp, ?_⟩
    intro a2 ha2
    rw [Finset.mem_singleton]
    exact fsd_degenerate_class (p := p) (k := d.factorization p) a0 a1 b h01 hbl ha2
  · refine frameStepD_assembly hd a0 a1 b H h01 ?_
    intro p hp
    haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    have hb : ∀ l : Fin 3, a1 ≠ b l := fun l h => hbl ⟨l, h.symm⟩
    by_cases hAi : ((p ^ (d.factorization p - padicValNat p 2) : ℕ) : ℤ)
        ∣ ∏ l : Fin 3, ((b l : ℤ) - (a0 : ℤ))
    · exact frameAdm_prime_class_dvd (p := p) (k := d.factorization p) a0 a1 b h01 hb hAi
    · exact frameAdm_prime_class_not_dvd (p := p) (k := d.factorization p) a0 a1 b h01 hb hAi

end Work.LinnikBurgess
