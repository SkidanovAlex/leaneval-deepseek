import Mathlib
import Submission.Work.LinnikAreas.CorrAllR.Defs
import Submission.Work.LinnikAreas.CorrAllR.DefsSq
import Submission.Work.LinnikAreas.CorrAllR.prod_chi_ratio
import Submission.Work.LinnikAreas.CorrAllR.deriv_prod_linear_eval
import Submission.Work.LinnikAreas.CorrAllR.deriv_prod_linear_eval_simple_root
import Submission.Commons.NumberTheory.DirichletCharacter.primesq_weil_bound
import Submission.Commons.NumberTheory.DirichletCharacter.chi_one_add_primePow_isPrimitiveRoot
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_conj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators
open Finset

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace Work.LinnikAreas.CorrAllR


/-! ### Basic helpers -/

/-- Modulo-`p` inequality upgrade to `ZMod p`. -/
lemma natCast_ne_of_mod_ne (p : ℕ) [NeZero p] {x y : ℕ} (h : x % p ≠ y % p) :
    (x : ZMod p) ≠ (y : ZMod p) :=
  fun hh => h ((ZMod.natCast_eq_natCast_iff x y p).mp hh)

/-- `castHom` of a digit-decomposed residue. -/
lemma castHom_zmd_add (p : ℕ) [Fact p.Prime] (ρ y : ZMod p) (c : ℕ) :
    ZMod.castHom (show p ∣ p ^ 2 from ⟨p, by ring⟩) (ZMod p)
      (zmd p ρ y + ((c : ℕ) : ZMod (p ^ 2))) = ρ + (c : ZMod p) := by
  have hd : p ∣ p ^ 2 := ⟨p, by ring⟩
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [map_add]
  congr 1
  · rw [zmd, map_add, map_mul, map_natCast, map_natCast, ZMod.natCast_self, zero_mul, add_zero,
      ZMod.natCast_zmod_val]
  · rw [map_natCast]

/-- Swapping the two blocks conjugates the correlation sum. -/
lemma sum_swap_sq (p : ℕ) [NeZero (p ^ 2)] (χ : DirichletCharacter ℂ (p ^ 2)) {r : ℕ}
    (a b : Fin r → ℕ) :
    (∑ x : ZMod (p ^ 2), χ (∏ l : Fin r, (x + (a l : ZMod (p ^ 2))))
        * (starRingEnd ℂ) (χ (∏ l : Fin r, (x + (b l : ZMod (p ^ 2))))))
      = (starRingEnd ℂ) (∑ x : ZMod (p ^ 2), χ (∏ l : Fin r, (x + (b l : ZMod (p ^ 2))))
        * (starRingEnd ℂ) (χ (∏ l : Fin r, (x + (a l : ZMod (p ^ 2)))))) := by
  rw [map_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [starRingEnd_apply, star_mul, star_star]

/-- Rearrangement of a product of two scaled powers in a commutative monoid. -/
lemma mul_pow_mul_pow {M : Type*} [CommMonoid M] (x z c d : M) (y : ℕ) :
    (c * x ^ y) * (d * z ^ y) = (c * d) * (x * z) ^ y := by
  rw [mul_pow]
  ac_rfl

/-! ### The `a`-unique case of the local prime-square bound -/

theorem corrSum_sq_le_of_unique_a (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (χ : DirichletCharacter ℂ (p ^ 2)) (hprim : χ.IsPrimitive) {r : ℕ} (hr : 0 < r)
    (a b : Fin r → ℕ) (k : Fin r)
    (ha : ∀ l : Fin r, l ≠ k → (a l : ZMod p) ≠ (a k : ZMod p))
    (hb : ∀ l : Fin r, (b l : ZMod p) ≠ (a k : ZMod p)) :
    ‖∑ x : ZMod (p ^ 2), χ (∏ l : Fin r, (x + (a l : ZMod (p ^ 2))))
        * (starRingEnd ℂ) (χ (∏ l : Fin r, (x + (b l : ZMod (p ^ 2)))))‖
      ≤ (2 * (r : ℝ)) * (p : ℝ) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hd : p ∣ p ^ 2 := ⟨p, by ring⟩
  set ζ : ℂ := χ (((1 + p : ℕ)) : ZMod (p ^ 2)) with hζdef
  have hζ : IsPrimitiveRoot ζ p := by
    simpa [hζdef] using
      Commons.NumberTheory.DirichletCharacter.chi_one_add_primePow_isPrimitiveRoot p 2 hp2
        (le_refl 2) χ hprim
  have hζpow : ζ ^ p = 1 := hζ.pow_eq_one
  have hζne : ζ ≠ 1 := hζ.ne_one hp.one_lt
  set A : Polynomial (ZMod p) := ∏ l : Fin r, (Polynomial.X + Polynomial.C ((a l : ZMod p)))
    with hA
  set B : Polynomial (ZMod p) := ∏ l : Fin r, (Polynomial.X + Polynomial.C ((b l : ZMod p)))
    with hB
  set P : Polynomial (ZMod p) := A.derivative * B - A * B.derivative with hP
  have hAeval : ∀ x : ZMod p, A.eval x = ∏ l : Fin r, (x + (a l : ZMod p)) := by
    intro x
    rw [hA, Polynomial.eval_prod]
    exact Finset.prod_congr rfl (fun l _ => by simp)
  have hBeval : ∀ x : ZMod p, B.eval x = ∏ l : Fin r, (x + (b l : ZMod p)) := by
    intro x
    rw [hB, Polynomial.eval_prod]
    exact Finset.prod_congr rfl (fun l _ => by simp)
  have hAdeg : A.natDegree ≤ r := by
    rw [hA]
    calc (∏ l : Fin r, (Polynomial.X + Polynomial.C ((a l : ZMod p)))).natDegree
        ≤ ∑ l : Fin r, (Polynomial.X + Polynomial.C ((a l : ZMod p))).natDegree :=
          Polynomial.natDegree_prod_le _ _
      _ = r := by
        have h1 : ∀ l : Fin r,
            (Polynomial.X + Polynomial.C ((a l : ZMod p))).natDegree = 1 :=
          fun l => Polynomial.natDegree_X_add_C _
        rw [Finset.sum_congr rfl (fun l _ => h1 l)]
        simp
  have hBdeg : B.natDegree ≤ r := by
    rw [hB]
    calc (∏ l : Fin r, (Polynomial.X + Polynomial.C ((b l : ZMod p)))).natDegree
        ≤ ∑ l : Fin r, (Polynomial.X + Polynomial.C ((b l : ZMod p))).natDegree :=
          Polynomial.natDegree_prod_le _ _
      _ = r := by
        have h1 : ∀ l : Fin r,
            (Polynomial.X + Polynomial.C ((b l : ZMod p))).natDegree = 1 :=
          fun l => Polynomial.natDegree_X_add_C _
        rw [Finset.sum_congr rfl (fun l _ => h1 l)]
        simp
  have hPdeg : P.natDegree ≤ 2 * r - 1 := by
    rw [hP]
    have h1 : (A.derivative * B).natDegree ≤ 2 * r - 1 := by
      calc (A.derivative * B).natDegree ≤ A.derivative.natDegree + B.natDegree :=
            Polynomial.natDegree_mul_le
        _ ≤ 2 * r - 1 := by
            have h1 := Polynomial.natDegree_derivative_le A
            omega
    have h2 : (A * B.derivative).natDegree ≤ 2 * r - 1 := by
      calc (A * B.derivative).natDegree ≤ A.natDegree + B.derivative.natDegree :=
            Polynomial.natDegree_mul_le
        _ ≤ 2 * r - 1 := by
            have h1 := Polynomial.natDegree_derivative_le B
            omega
    calc (A.derivative * B - A * B.derivative).natDegree
        ≤ max (A.derivative * B).natDegree (A * B.derivative).natDegree :=
          Polynomial.natDegree_sub_le _ _
      _ ≤ 2 * r - 1 := max_le h1 h2
  have hPne : P ≠ 0 := by
    intro hP0
    have hzero : A.derivative * B = A * B.derivative := by
      have hh := hP0; rw [hP] at hh; exact sub_eq_zero.mp hh
    set γ : ZMod p := (a k : ZMod p) with hγ
    have hAroot : A.eval (-γ) = 0 := by
      rw [hAeval]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hγ])
    have hAdne : A.derivative.eval (-γ) ≠ 0 := by
      have hh := deriv_prod_linear_eval_simple_root (fun l => (a l : ZMod p)) k
        (fun l hl => ha l hl)
      simpa [hA, hγ] using hh
    have hBeq := congrArg (fun q : Polynomial (ZMod p) => q.eval (-γ)) hzero
    rw [Polynomial.eval_mul, Polynomial.eval_mul, hAroot, zero_mul] at hBeq
    have hBroot : B.eval (-γ) = 0 := by
      rcases mul_eq_zero.mp hBeq with hh | hh
      · exact absurd hh hAdne
      · exact hh
    rw [hBeval] at hBroot
    obtain ⟨l, -, hl⟩ := Finset.prod_eq_zero_iff.mp hBroot
    have hbl : (b l : ZMod p) = (a k : ZMod p) := by
      have h2 : (b l : ZMod p) - (a k : ZMod p) = 0 := by
        rw [← hγ, sub_eq_add_neg, add_comm]
        exact hl
      exact sub_eq_zero.mp h2
    exact hb l hbl
  have hS : (∑ x : ZMod (p ^ 2), χ (∏ l : Fin r, (x + (a l : ZMod (p ^ 2))))
        * (starRingEnd ℂ) (χ (∏ l : Fin r, (x + (b l : ZMod (p ^ 2))))))
      = ∑ x : ZMod (p ^ 2), (∏ l : Fin r, χ (x + (a l : ZMod (p ^ 2))))
        * (∏ l : Fin r, (χ⁻¹) (x + (b l : ZMod (p ^ 2)))) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [map_prod χ (fun l => x + (a l : ZMod (p ^ 2))) Finset.univ,
      Commons.NumberTheory.DirichletCharacter.star_apply_char χ
        (∏ l : Fin r, (x + (b l : ZMod (p ^ 2)))),
      map_prod (χ⁻¹) (fun l => x + (b l : ZMod (p ^ 2))) Finset.univ]
  rw [hS]
  have hbij : Function.Bijective (fun am : ZMod p × ZMod p => zmd p am.1 am.2) := by
    simpa [zmd] using Commons.NumberTheory.DirichletCharacter.zmod_sq_digits_bijective p
  have hsum1 : (∑ x : ZMod (p ^ 2), (∏ l : Fin r, χ (x + (a l : ZMod (p ^ 2))))
        * (∏ l : Fin r, (χ⁻¹) (x + (b l : ZMod (p ^ 2)))))
      = ∑ am : ZMod p × ZMod p, (∏ l : Fin r, χ (zmd p am.1 am.2 + (a l : ZMod (p ^ 2))))
        * (∏ l : Fin r, (χ⁻¹) (zmd p am.1 am.2 + (b l : ZMod (p ^ 2)))) :=
    (Fintype.sum_bijective (fun am : ZMod p × ZMod p => zmd p am.1 am.2) hbij _ _
      (fun _ => rfl)).symm
  rw [hsum1, Fintype.sum_prod_type]
  simp only []
  have hfiber : ∀ ρ : ZMod p,
      ‖∑ y : ZMod p, (∏ l : Fin r, χ (zmd p ρ y + (a l : ZMod (p ^ 2))))
        * (∏ l : Fin r, (χ⁻¹) (zmd p ρ y + (b l : ZMod (p ^ 2))))‖
      ≤ if P.eval ρ = 0 then (p : ℝ) else 0 := by
    intro ρ
    by_cases hAB : A.eval ρ * B.eval ρ = 0
    · have hzero : ∀ y : ZMod p, (∏ l : Fin r, χ (zmd p ρ y + (a l : ZMod (p ^ 2))))
            * (∏ l : Fin r, (χ⁻¹) (zmd p ρ y + (b l : ZMod (p ^ 2)))) = 0 := by
        intro y
        rcases mul_eq_zero.mp hAB with hA0 | hB0
        · have hprod0 : (∏ l : Fin r, (ρ + (a l : ZMod p))) = 0 := by
            rw [← hAeval ρ]; exact hA0
          obtain ⟨l, -, hl⟩ := Finset.prod_eq_zero_iff.mp hprod0
          have hfac : χ (zmd p ρ y + (a l : ZMod (p ^ 2))) = 0 := by
            apply MulChar.map_nonunit
            intro hunit
            have hcast : ZMod.castHom hd (ZMod p) (zmd p ρ y + (a l : ZMod (p ^ 2))) = 0 := by
              rw [castHom_zmd_add p ρ y (a l)]
              exact hl
            exact not_isUnit_zero (by
              rw [← hcast]; exact hunit.map (ZMod.castHom hd (ZMod p)))
          rw [Finset.prod_eq_zero (Finset.mem_univ l) hfac, zero_mul]
        · have hprod0 : (∏ l : Fin r, (ρ + (b l : ZMod p))) = 0 := by
            rw [← hBeval ρ]; exact hB0
          obtain ⟨l, -, hl⟩ := Finset.prod_eq_zero_iff.mp hprod0
          have hfac : (χ⁻¹) (zmd p ρ y + (b l : ZMod (p ^ 2))) = 0 := by
            apply MulChar.map_nonunit
            intro hunit
            have hcast : ZMod.castHom hd (ZMod p) (zmd p ρ y + (b l : ZMod (p ^ 2))) = 0 := by
              rw [castHom_zmd_add p ρ y (b l)]
              exact hl
            exact not_isUnit_zero (by
              rw [← hcast]; exact hunit.map (ZMod.castHom hd (ZMod p)))
          rw [show (∏ l : Fin r, (χ⁻¹) (zmd p ρ y + (b l : ZMod (p ^ 2)))) = 0 from
            Finset.prod_eq_zero (Finset.mem_univ l) hfac, mul_zero]
      rw [Finset.sum_eq_zero (fun y _ => hzero y), norm_zero]
      split <;> positivity
    · have hAnz : A.eval ρ ≠ 0 := fun hh => hAB (by rw [hh, zero_mul])
      have hBnz : B.eval ρ ≠ 0 := fun hh => hAB (by rw [hh, mul_zero])
      have hAnz_l : ∀ l : Fin r, ρ + (a l : ZMod p) ≠ 0 := fun l =>
        (Finset.prod_ne_zero_iff.mp (by rw [← hAeval ρ]; exact hAnz)) l (Finset.mem_univ l)
      have hBnz_l : ∀ l : Fin r, ρ + (b l : ZMod p) ≠ 0 := fun l =>
        (Finset.prod_ne_zero_iff.mp (by rw [← hBeval ρ]; exact hBnz)) l (Finset.mem_univ l)
      set DA : ℕ := ∑ l : Fin r, ((ρ + (a l : ZMod p))⁻¹).val with hDA
      set DB : ℕ := ∑ l : Fin r, ((ρ + (b l : ZMod p))⁻¹).val with hDB
      set G : ℕ := DA + (p - 1) * DB with hG
      have hζinv : ζ⁻¹ = ζ ^ (p - 1) := by
        have h1 : ζ ^ (p - 1) * ζ = 1 := by
          rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hζpow]
        exact inv_eq_of_mul_eq_one_left h1
      have hAeq : ∀ y : ZMod p, (∏ l : Fin r, χ (zmd p ρ y + (a l : ZMod (p ^ 2))))
          = (∏ l : Fin r, χ (zmd p ρ 0 + (a l : ZMod (p ^ 2)))) * (ζ ^ DA) ^ y.val := by
        intro y
        have hh := prod_chi_ratio p χ a ρ hAnz_l y
        simpa [hζdef, hDA] using hh
      have hBinv : (χ⁻¹) (1 + (p : ZMod (p ^ 2))) = ζ⁻¹ := by
        have hu : IsUnit (1 + (p : ZMod (p ^ 2))) := by
          rw [show (1 + (p : ZMod (p ^ 2))) = (((1 + p : ℕ)) : ZMod (p ^ 2)) by
            push_cast; ring]
          rw [ZMod.isUnit_iff_coprime]
          simpa using Commons.NumberTheory.DirichletCharacter.coprime_one_add_prime_pow_pred hp
            (le_refl 2 : 2 ≤ 2)
        have hχu : χ (1 + (p : ZMod (p ^ 2))) = ζ := by
          rw [hζdef]
          congr 1
          push_cast
          ring
        have hmul : (χ⁻¹) (1 + (p : ZMod (p ^ 2))) * χ (1 + (p : ZMod (p ^ 2))) = 1 := by
          rw [← MulChar.mul_apply, inv_mul_cancel]
          exact MulChar.one_apply hu
        rw [hχu] at hmul
        exact (inv_eq_of_mul_eq_one_left hmul).symm
      have hBeq : ∀ y : ZMod p, (∏ l : Fin r, (χ⁻¹) (zmd p ρ y + (b l : ZMod (p ^ 2))))
          = (∏ l : Fin r, (χ⁻¹) (zmd p ρ 0 + (b l : ZMod (p ^ 2))))
            * ((ζ⁻¹) ^ DB) ^ y.val := by
        intro y
        have hh := prod_chi_ratio p (χ⁻¹) b ρ hBnz_l y
        simpa [hDB, hBinv] using hh
      have hratio : ∀ y : ZMod p, (∏ l : Fin r, χ (zmd p ρ y + (a l : ZMod (p ^ 2))))
            * (∏ l : Fin r, (χ⁻¹) (zmd p ρ y + (b l : ZMod (p ^ 2))))
          = ((∏ l : Fin r, χ (zmd p ρ 0 + (a l : ZMod (p ^ 2))))
              * (∏ l : Fin r, (χ⁻¹) (zmd p ρ 0 + (b l : ZMod (p ^ 2)))))
            * (ζ ^ G) ^ y.val := by
        intro y
        rw [hAeq y, hBeq y, hG]
        have h1 : (ζ⁻¹) ^ DB = ζ ^ ((p - 1) * DB) := by rw [hζinv, pow_mul]
        rw [mul_pow_mul_pow (ζ ^ DA) ((ζ⁻¹) ^ DB)
          (∏ l : Fin r, χ (zmd p ρ 0 + (a l : ZMod (p ^ 2))))
          (∏ l : Fin r, (χ⁻¹) (zmd p ρ 0 + (b l : ZMod (p ^ 2)))) y.val]
        rw [h1, ← pow_add]
      have hAderiv : A.derivative.eval ρ = A.eval ρ * (∑ l : Fin r, (ρ + (a l : ZMod p))⁻¹) := by
        rw [hAeval ρ, hA]
        exact deriv_prod_linear_eval (fun l => (a l : ZMod p)) ρ hAnz_l
      have hBderiv : B.derivative.eval ρ = B.eval ρ * (∑ l : Fin r, (ρ + (b l : ZMod p))⁻¹) := by
        rw [hBeval ρ, hB]
        exact deriv_prod_linear_eval (fun l => (b l : ZMod p)) ρ hBnz_l
      have hPform : P.eval ρ = A.eval ρ * B.eval ρ
          * ((∑ l : Fin r, (ρ + (a l : ZMod p))⁻¹)
              - (∑ l : Fin r, (ρ + (b l : ZMod p))⁻¹)) := by
        rw [hP]
        simp only [Polynomial.eval_sub, Polynomial.eval_mul]
        rw [hAderiv, hBderiv]
        ring
      have hGeq : (G : ZMod p) = (∑ l : Fin r, (ρ + (a l : ZMod p))⁻¹)
          - (∑ l : Fin r, (ρ + (b l : ZMod p))⁻¹) := by
        have h1 : ((∑ l : Fin r, ((ρ + (a l : ZMod p))⁻¹).val : ℕ) : ZMod p)
            = (∑ l : Fin r, (ρ + (a l : ZMod p))⁻¹) := by
          rw [Nat.cast_sum]
          exact Finset.sum_congr rfl (fun l _ => ZMod.natCast_zmod_val _)
        have h2 : ((∑ l : Fin r, ((ρ + (b l : ZMod p))⁻¹).val : ℕ) : ZMod p)
            = (∑ l : Fin r, (ρ + (b l : ZMod p))⁻¹) := by
          rw [Nat.cast_sum]
          exact Finset.sum_congr rfl (fun l _ => ZMod.natCast_zmod_val _)
        have h3 : ((p - 1 : ℕ) : ZMod p) = -1 := by
          rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one, ZMod.natCast_self, zero_sub]
        rw [hG, hDA, hDB, Nat.cast_add, Nat.cast_mul, h1, h2, h3]
        ring
      have hGiff : ζ ^ G = 1 ↔ P.eval ρ = 0 := by
        constructor
        · intro hG1
          have hdvd : p ∣ G := (hζ.pow_eq_one_iff_dvd G).mp hG1
          have hcast : (G : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff G p).mpr hdvd
          rw [hGeq] at hcast
          rw [hPform, hcast, mul_zero]
        · intro hP0
          have hσ : (∑ l : Fin r, (ρ + (a l : ZMod p))⁻¹)
              - (∑ l : Fin r, (ρ + (b l : ZMod p))⁻¹) = 0 := by
            have hh := hP0
            rw [hPform] at hh
            exact (mul_eq_zero.mp hh).resolve_left hAB
          have hcast : (G : ZMod p) = 0 := by rw [hGeq, hσ]
          have hdvd : p ∣ G := (ZMod.natCast_eq_zero_iff G p).mp hcast
          exact (hζ.pow_eq_one_iff_dvd G).mpr hdvd
      have hCnorm : ‖(∏ l : Fin r, χ (zmd p ρ 0 + (a l : ZMod (p ^ 2))))
          * (∏ l : Fin r, (χ⁻¹) (zmd p ρ 0 + (b l : ZMod (p ^ 2))))‖ ≤ 1 := by
        rw [norm_mul]
        have h1 : ‖(∏ l : Fin r, χ (zmd p ρ 0 + (a l : ZMod (p ^ 2))))‖ ≤ 1 := by
          calc ‖(∏ l : Fin r, χ (zmd p ρ 0 + (a l : ZMod (p ^ 2))))‖
              ≤ ∏ l : Fin r, ‖χ (zmd p ρ 0 + (a l : ZMod (p ^ 2)))‖ := Finset.norm_prod_le _ _
            _ ≤ ∏ l : Fin r, (1 : ℝ) := Finset.prod_le_prod₀ (fun l _ => norm_nonneg _)
                  (fun l _ => DirichletCharacter.norm_le_one χ _)
            _ = 1 := by simp
        have h2 : ‖(∏ l : Fin r, (χ⁻¹) (zmd p ρ 0 + (b l : ZMod (p ^ 2))))‖ ≤ 1 := by
          calc ‖(∏ l : Fin r, (χ⁻¹) (zmd p ρ 0 + (b l : ZMod (p ^ 2))))‖
              ≤ ∏ l : Fin r, ‖(χ⁻¹) (zmd p ρ 0 + (b l : ZMod (p ^ 2)))‖ :=
                Finset.norm_prod_le _ _
            _ ≤ ∏ l : Fin r, (1 : ℝ) := Finset.prod_le_prod₀ (fun l _ => norm_nonneg _)
                  (fun l _ => DirichletCharacter.norm_le_one (χ⁻¹) _)
            _ = 1 := by simp
        have h1' := norm_nonneg (∏ l : Fin r, χ (zmd p ρ 0 + (a l : ZMod (p ^ 2))))
        have h2' := norm_nonneg (∏ l : Fin r, (χ⁻¹) (zmd p ρ 0 + (b l : ZMod (p ^ 2))))
        nlinarith
      rw [Finset.sum_congr rfl (fun y _ => hratio y), ← Finset.mul_sum, norm_mul]
      by_cases hP0 : P.eval ρ = 0
      · rw [if_pos hP0]
        have hG1 : ζ ^ G = 1 := hGiff.mpr hP0
        have hsum : (∑ y : ZMod p, (ζ ^ G) ^ y.val) = (p : ℂ) := by
          rw [hG1]
          simp [Finset.sum_const, ZMod.card]
        rw [hsum, Complex.norm_natCast]
        calc ‖(∏ l : Fin r, χ (zmd p ρ 0 + (a l : ZMod (p ^ 2))))
              * (∏ l : Fin r, (χ⁻¹) (zmd p ρ 0 + (b l : ZMod (p ^ 2))))‖ * (p : ℝ)
            ≤ 1 * (p : ℝ) := mul_le_mul_of_nonneg_right hCnorm (Nat.cast_nonneg p)
          _ = (p : ℝ) := one_mul _
      · rw [if_neg hP0]
        have hG1 : ζ ^ G ≠ 1 := fun hh => hP0 (hGiff.mp hh)
        have hsum : (∑ y : ZMod p, (ζ ^ G) ^ y.val) = 0 :=
          Commons.NumberTheory.DirichletCharacter.sum_val_pow_eq_zero
            (by rw [← pow_mul, Nat.mul_comm, pow_mul, hζpow, one_pow]) hG1
        rw [hsum, norm_zero, mul_zero]
  calc ‖∑ ρ : ZMod p, ∑ y : ZMod p, (∏ l : Fin r, χ (zmd p ρ y + (a l : ZMod (p ^ 2))))
        * (∏ l : Fin r, (χ⁻¹) (zmd p ρ y + (b l : ZMod (p ^ 2))))‖
      ≤ ∑ ρ : ZMod p, ‖∑ y : ZMod p, (∏ l : Fin r, χ (zmd p ρ y + (a l : ZMod (p ^ 2))))
        * (∏ l : Fin r, (χ⁻¹) (zmd p ρ y + (b l : ZMod (p ^ 2))))‖ := norm_sum_le _ _
    _ ≤ ∑ ρ : ZMod p, (if P.eval ρ = 0 then (p : ℝ) else 0) :=
        Finset.sum_le_sum (fun ρ _ => hfiber ρ)
    _ = (p : ℝ) * ((Finset.univ.filter (fun ρ : ZMod p => P.eval ρ = 0)).card : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ (p : ℝ) * (P.natDegree : ℝ) :=
        mul_le_mul_of_nonneg_left
          (by exact_mod_cast Commons.NumberTheory.DirichletCharacter.card_roots_le P hPne)
          (Nat.cast_nonneg p)
    _ ≤ (p : ℝ) * ((2 * r - 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hPdeg) (Nat.cast_nonneg p)
    _ ≤ (2 * (r : ℝ)) * (p : ℝ) := by
        have hle : ((2 * r - 1 : ℕ) : ℝ) ≤ 2 * (r : ℝ) := by
          have h1 : ((2 * r - 1 : ℕ) : ℝ) ≤ ((2 * r : ℕ) : ℝ) := by
            exact_mod_cast Nat.sub_le (2 * r) 1
          simpa using h1
        have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
        nlinarith

/-! ### The `b`-unique case -/

theorem corrSum_sq_le_of_unique_b (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (χ : DirichletCharacter ℂ (p ^ 2)) (hprim : χ.IsPrimitive) {r : ℕ} (hr : 0 < r)
    (a b : Fin r → ℕ) (k : Fin r)
    (hb : ∀ l : Fin r, l ≠ k → (b l : ZMod p) ≠ (b k : ZMod p))
    (ha : ∀ l : Fin r, (a l : ZMod p) ≠ (b k : ZMod p)) :
    ‖∑ x : ZMod (p ^ 2), χ (∏ l : Fin r, (x + (a l : ZMod (p ^ 2))))
        * (starRingEnd ℂ) (χ (∏ l : Fin r, (x + (b l : ZMod (p ^ 2)))))‖
      ≤ (2 * (r : ℝ)) * (p : ℝ) := by
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (Fact.out : p.Prime).pos.ne'⟩
  have h := corrSum_sq_le_of_unique_a p hp2 χ hprim hr b a k hb ha
  rw [sum_swap_sq p χ a b, Complex.norm_conj]
  exact h

/-! ### Reduction of the `2r`-tuple statement to the two split cases -/

theorem corrSumV_sq_le_corr (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (χ : DirichletCharacter ℂ (p ^ 2)) (hprim : χ.IsPrimitive) {r : ℕ} (hr : 0 < r)
    (v : Fin (r + r) → ℕ) (i : Fin (r + r)) (huniq : Work.LinnikAreas.IsUniqModV p v i) :
    ‖Work.LinnikAreas.corrSumV (p ^ 2) χ r v‖ ≤ (2 * (r : ℝ)) * (p : ℝ) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  set a : Fin r → ℕ := fun l => v (Fin.castAdd r l) with ha
  set b : Fin r → ℕ := fun l => v (Fin.natAdd r l) with hb
  have hv : v = Work.LinnikAreas.combShift a b := by
    rw [ha, hb]
    exact (Work.LinnikAreas.combShift_split v).symm
  have hsum : Work.LinnikAreas.corrSumV (p ^ 2) χ r v
      = ∑ x : ZMod (p ^ 2), χ (∏ l : Fin r, (x + (a l : ZMod (p ^ 2))))
          * (starRingEnd ℂ) (χ (∏ l : Fin r, (x + (b l : ZMod (p ^ 2))))) := by
    rw [hv, Work.LinnikAreas.corrSumV_combShift]
    rfl
  rw [hsum]
  rcases lt_or_ge i.val r with hi | hi
  · set k : Fin r := ⟨i.val, hi⟩ with hk
    have hik : Fin.castAdd r k = i := by
      refine Fin.ext ?_
      simp [hk]
    have hauniq : ∀ l : Fin r, l ≠ k → (a l : ZMod p) ≠ (a k : ZMod p) := by
      intro l hl hcon
      have hji : Fin.castAdd r l ≠ i := by
        intro hh
        have h2 := congrArg Fin.val hh
        rw [Fin.val_castAdd] at h2
        exact hl (Fin.ext (by simp [hk, h2]))
      have h1 := huniq (Fin.castAdd r l) hji
      simp only [ha] at hcon
      rw [hik] at hcon
      exact h1 ((ZMod.natCast_eq_natCast_iff (v (Fin.castAdd r l)) (v i) p).mp hcon)
    have hbuniq : ∀ l : Fin r, (b l : ZMod p) ≠ (a k : ZMod p) := by
      intro l hcon
      have hji : Fin.natAdd r l ≠ i := by
        intro hh
        have h2 := congrArg Fin.val hh
        rw [Fin.val_natAdd] at h2
        omega
      have h1 := huniq (Fin.natAdd r l) hji
      simp only [hb, ha] at hcon
      rw [hik] at hcon
      exact h1 ((ZMod.natCast_eq_natCast_iff (v (Fin.natAdd r l)) (v i) p).mp hcon)
    exact corrSum_sq_le_of_unique_a p hp2 χ hprim hr a b k hauniq hbuniq
  · set k : Fin r := ⟨i.val - r, by omega⟩ with hk
    have hik : Fin.natAdd r k = i := by
      refine Fin.ext ?_
      rw [Fin.val_natAdd]
      simp [hk]
      omega
    have hbuniq : ∀ l : Fin r, l ≠ k → (b l : ZMod p) ≠ (b k : ZMod p) := by
      intro l hl hcon
      have hji : Fin.natAdd r l ≠ i := by
        intro hh
        have h2 := congrArg Fin.val hh
        rw [Fin.val_natAdd] at h2
        exact hl (Fin.ext (by simp [hk]; omega))
      have h1 := huniq (Fin.natAdd r l) hji
      simp only [hb] at hcon
      rw [hik] at hcon
      exact h1 ((ZMod.natCast_eq_natCast_iff (v (Fin.natAdd r l)) (v i) p).mp hcon)
    have hauniq : ∀ l : Fin r, (a l : ZMod p) ≠ (b k : ZMod p) := by
      intro l hcon
      have hji : Fin.castAdd r l ≠ i := by
        intro hh
        have h2 := congrArg Fin.val hh
        rw [Fin.val_castAdd] at h2
        omega
      have h1 := huniq (Fin.castAdd r l) hji
      simp only [ha, hb] at hcon
      rw [hik] at hcon
      exact h1 ((ZMod.natCast_eq_natCast_iff (v (Fin.castAdd r l)) (v i) p).mp hcon)
    exact corrSum_sq_le_of_unique_b p hp2 χ hprim hr a b k hbuniq hauniq

/-! ### The case `p = 2` -/

lemma zmod_two_eq_zero_or_one (u : ZMod 2) : u = 0 ∨ u = 1 := by
  haveI : NeZero 2 := ⟨by norm_num⟩
  have hlt : u.val < 2 := ZMod.val_lt u
  have h : u.val = 0 ∨ u.val = 1 := by omega
  rcases h with h | h
  · left
    rw [← ZMod.natCast_zmod_val u, h]
    simp
  · right
    rw [← ZMod.natCast_zmod_val u, h]
    simp

lemma zmod_two_add_self (a : ZMod 2) : a + a = 0 := CharTwo.add_self_eq_zero a

lemma zmod_two_add_eq_one_of_ne {x y : ZMod 2} (h : x ≠ y) : x + y = 1 := by
  rcases zmod_two_eq_zero_or_one x with hx | hx <;> rcases zmod_two_eq_zero_or_one y with hy | hy
  · exact absurd (hx.trans hy.symm) h
  · rw [hx, hy]; simp
  · rw [hx, hy]; simp
  · exact absurd (hx.trans hy.symm) h

lemma zmod_two_eq_of_ne_of_ne {x y z : ZMod 2} (h1 : x ≠ y) (h2 : z ≠ y) : x = z := by
  have h1' := zmod_two_add_eq_one_of_ne h1
  have h2' := zmod_two_add_eq_one_of_ne h2
  have hh : x + y = z + y := by rw [h1', h2']
  have h3 := congrArg (fun t : ZMod 2 => t - y) hh
  simpa using h3

theorem corrSumV_two_eq_zero {r : ℕ} (hr : 0 < r) (χ : DirichletCharacter ℂ 4)
    (v : Fin (r + r) → ℕ) (i : Fin (r + r)) (huniq : Work.LinnikAreas.IsUniqModV 2 v i) :
    Work.LinnikAreas.corrSumV 4 χ r v = 0 := by
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  have hd : (2 : ℕ) ∣ 4 := by norm_num
  have hne : ∀ j : Fin (r + r), j ≠ i → (v j : ZMod 2) ≠ (v i : ZMod 2) :=
    fun j hj => natCast_ne_of_mod_ne 2 (huniq j hj)
  refine Finset.sum_eq_zero (fun x _ => ?_)
  set ε : ZMod 2 := ZMod.castHom hd (ZMod 2) x with hε
  have hfacA : ∀ l : Fin r, ZMod.castHom hd (ZMod 2) (x + (v (Fin.castAdd r l) : ZMod 4))
      = ε + (v (Fin.castAdd r l) : ZMod 2) := by
    intro l
    rw [hε, map_add, map_natCast]
  have hfacB : ∀ l : Fin r, ZMod.castHom hd (ZMod 2) (x + (v (Fin.natAdd r l) : ZMod 4))
      = ε + (v (Fin.natAdd r l) : ZMod 2) := by
    intro l
    rw [hε, map_add, map_natCast]
  rcases lt_or_ge i.val r with hi | hi
  · set k : Fin r := ⟨i.val, hi⟩ with hk
    have hik : Fin.castAdd r k = i := by
      refine Fin.ext ?_
      simp [hk]
    by_cases hcase : (v i : ZMod 2) = ε
    · have hzeroA : ZMod.castHom hd (ZMod 2)
          (∏ l : Fin r, (x + (v (Fin.castAdd r l) : ZMod 4))) = 0 := by
        rw [map_prod]
        refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
        rw [hfacA k, hik, hcase, zmod_two_add_self]
      have hnu : ¬ IsUnit (∏ l : Fin r, (x + (v (Fin.castAdd r l) : ZMod 4))) := by
        intro hunit
        exact not_isUnit_zero (by
          rw [← hzeroA]; exact hunit.map (ZMod.castHom hd (ZMod 2)))
      rw [show χ (∏ l : Fin r, (x + (v (Fin.castAdd r l) : ZMod 4))) = 0 from
        MulChar.map_nonunit χ hnu, zero_mul]
    · have hbval : ∀ l : Fin r, (v (Fin.natAdd r l) : ZMod 2) = ε := by
        intro l
        have hji : Fin.natAdd r l ≠ i := by
          intro hh
          have h2 := congrArg Fin.val hh
          rw [Fin.val_natAdd] at h2
          omega
        exact zmod_two_eq_of_ne_of_ne (hne (Fin.natAdd r l) hji) (fun h => hcase h.symm)
      have hzeroB : ZMod.castHom hd (ZMod 2)
          (∏ l : Fin r, (x + (v (Fin.natAdd r l) : ZMod 4))) = 0 := by
        rw [map_prod]
        refine Finset.prod_eq_zero (Finset.mem_univ ⟨0, hr⟩) ?_
        rw [hfacB ⟨0, hr⟩, hbval ⟨0, hr⟩, zmod_two_add_self]
      have hnu : ¬ IsUnit (∏ l : Fin r, (x + (v (Fin.natAdd r l) : ZMod 4))) := by
        intro hunit
        exact not_isUnit_zero (by
          rw [← hzeroB]; exact hunit.map (ZMod.castHom hd (ZMod 2)))
      rw [show χ (∏ l : Fin r, (x + (v (Fin.natAdd r l) : ZMod 4))) = 0 from
        MulChar.map_nonunit χ hnu, map_zero, mul_zero]
  · set k : Fin r := ⟨i.val - r, by omega⟩ with hk
    have hik : Fin.natAdd r k = i := by
      refine Fin.ext ?_
      rw [Fin.val_natAdd]
      simp [hk]
      omega
    by_cases hcase : (v i : ZMod 2) = ε
    · have hzeroB : ZMod.castHom hd (ZMod 2)
          (∏ l : Fin r, (x + (v (Fin.natAdd r l) : ZMod 4))) = 0 := by
        rw [map_prod]
        refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
        rw [hfacB k, hik, hcase, zmod_two_add_self]
      have hnu : ¬ IsUnit (∏ l : Fin r, (x + (v (Fin.natAdd r l) : ZMod 4))) := by
        intro hunit
        exact not_isUnit_zero (by
          rw [← hzeroB]; exact hunit.map (ZMod.castHom hd (ZMod 2)))
      rw [show χ (∏ l : Fin r, (x + (v (Fin.natAdd r l) : ZMod 4))) = 0 from
        MulChar.map_nonunit χ hnu, map_zero, mul_zero]
    · have haval : ∀ l : Fin r, (v (Fin.castAdd r l) : ZMod 2) = ε := by
        intro l
        have hji : Fin.castAdd r l ≠ i := by
          intro hh
          have h2 := congrArg Fin.val hh
          rw [Fin.val_castAdd] at h2
          omega
        exact zmod_two_eq_of_ne_of_ne (hne (Fin.castAdd r l) hji) (fun h => hcase h.symm)
      have hzeroA : ZMod.castHom hd (ZMod 2)
          (∏ l : Fin r, (x + (v (Fin.castAdd r l) : ZMod 4))) = 0 := by
        rw [map_prod]
        refine Finset.prod_eq_zero (Finset.mem_univ ⟨0, hr⟩) ?_
        rw [hfacA ⟨0, hr⟩, haval ⟨0, hr⟩, zmod_two_add_self]
      have hnu : ¬ IsUnit (∏ l : Fin r, (x + (v (Fin.castAdd r l) : ZMod 4))) := by
        intro hunit
        exact not_isUnit_zero (by
          rw [← hzeroA]; exact hunit.map (ZMod.castHom hd (ZMod 2)))
      rw [show χ (∏ l : Fin r, (x + (v (Fin.castAdd r l) : ZMod 4))) = 0 from
        MulChar.map_nonunit χ hnu, zero_mul]

/-- The `p = 2` instance of the target bound. -/
lemma corrSumV_sq_le_two (χ : DirichletCharacter ℂ (2 ^ 2)) {r : ℕ} (hr : 0 < r)
    (v : Fin (r + r) → ℕ) (i : Fin (r + r)) (huniq : Work.LinnikAreas.IsUniqModV 2 v i) :
    ‖Work.LinnikAreas.corrSumV (2 ^ 2) χ r v‖ ≤ (2 * r : ℝ) * (2 : ℝ) := by
  have hzero : Work.LinnikAreas.corrSumV (2 ^ 2) χ r v = 0 :=
    corrSumV_two_eq_zero hr χ v i huniq
  rw [hzero, norm_zero]
  positivity

/-! ### The target -/

/-- **Local prime-square correlation bound (general `r`).**

For primitive non-trivial `χ` mod `p^2` (any prime `p`, including `p = 2`), a `2r`-tuple of shifts
`v` and an index `i` unique modulo `p`: `‖corrSumV (p^2) χ r v‖ ≤ 2r p` (definitions `corrSumV`,
`IsUniqModV` from `Submission.Work.LinnikAreas.CorrAllR.Defs`, which you should import).

Sketch (digits `x = x₀ + p y`; `A = ∏_{l<r}(X + v l)`, `B = ∏_{l<r}(X + v (r+l))`, `o = orderOf χ`):
`x₀` with `A x₀` or `B x₀` a non-unit contributes `0`.  Otherwise
`A(x₀+py)·B(x₀+py)^(o-1) ≡ A x₀ · (B x₀)^(o-1) · (1 + p y Φ x₀)` with
`Φ x₀ = A'x₀/A x₀ + (o-1) B'x₀/B x₀` mod `p`, and `χ(1+pz) = χ(1+p)^z`
(`primePowKernel_char_pow`) with `χ(1+p)` a primitive `p`-th root of unity for `p ≠ 2`
(`chi_one_add_primePow_isPrimitiveRoot`); the inner sum over `y` is `p` if `Φ x₀ = 0` and `0`
otherwise (`primePowKernel_geom_sum_zmod`).  `Φ x₀ = 0` is `Ψ x₀ = 0` for
`Ψ = A'·B + (o-1)·A·B'`, of degree `≤ 2r-1`, and `Ψ ≠ 0` because `(A·B^(o-1))' = B^(o-2)·Ψ`, so
`Ψ = 0` would make `A·B^(o-1)` a `p`-th power, forcing the root multiplicity `N_A c + (o-1)N_B c`
to vanish mod `p` at every residue `c`, whereas at `c = v i % p` it is `1` or `o-1`, never
divisible by `p`.  Hence at most `2r-1` values of `x₀` contribute, giving `≤ (2r-1)p ≤ 2rp`.
For `p = 2`: uniqueness mod `2` says the `2r` shifts do not all have the same parity, so for every
`x` one of `A x`, `B x` is a non-unit and every summand is `0` (total `0`).
`Commons.NumberTheory.DirichletCharacter.charCorrelation6_primeSq` is the `r = 3` instance of this
statement and a good template. -/
theorem corrSumV_sq_good (p : ℕ) [Fact p.Prime] [NeZero (p ^ 2)] (χ : DirichletCharacter ℂ (p ^ 2))
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {r : ℕ} (hr : 0 < r) (v : Fin (r + r) → ℕ)
    (i : Fin (r + r)) (huniq : Work.LinnikAreas.IsUniqModV p v i) :
    ‖Work.LinnikAreas.corrSumV (p ^ 2) χ r v‖ ≤ (2 * r : ℝ) * (p : ℝ) := by
  rcases eq_or_ne p 2 with hp2eq | hp2
  · subst hp2eq
    exact corrSumV_sq_le_two χ hr v i huniq
  · exact corrSumV_sq_le_corr p hp2 χ hprim hr v i huniq

end Work.LinnikAreas.CorrAllR
