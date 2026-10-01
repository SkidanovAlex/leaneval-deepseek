import Mathlib
import Submission.Work.LinnikBurgess.ddDefs
import Submission.Work.LinnikBurgess.ddLevelDefs
import Submission.Commons.NumberTheory.DirichletCharacter.levelSum3_degenerate_step
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation6_levelSum_nondegenerate
import Submission.Commons.NumberTheory.GaussSum.quadratic_phase_prime_pow
import Submission.Work.LinnikBurgess.ddPhi_expansion
import Submission.Work.LinnikBurgess.ddEFacts
import Submission.Work.LinnikBurgess.ddChiLevelPrimitive
import Submission.Work.LinnikBurgess.ddLog_pow_eq
import Submission.Work.LinnikBurgess.ddProdCoord3Cubic
import Submission.Work.LinnikBurgess.ddLogPolyCompShape
import Submission.Work.LinnikBurgess.ddExistsIsCubicOfDecomp

/-!
# The level sum at a doubly degenerate critical class is `p` times a cubic Weyl sum

This file proves `Work.LinnikBurgess.dd_levelSum_eq_cubicSum`:

> under the three divisibility hypotheses `(D1) p² ∣ Δ₁`, `(D2) p ∣ Δ₂`, `(D3) p ∤ Δ₃` on the
> power-sum defects `Δ_k = ∑ A_l^k - ∑ C_l^k`, there is a *genuine cubic* integer polynomial `H`
> (`IsCubic p H`) with
> `‖levelSum3 p e 1 (e-2) χ A C‖ = p · ‖Tsum (p^(e-3)) H‖`.

## Structure

* `levelSum3_degenerate_step` (commons) already gives the factor `p` together with the reduction
  from `M = e-2` to `M = e-3` digits;
* the remaining task is to identify the phase `χ (prodCoord3 p e 1 A C n)` on `ZMod (p^(e-3))`
  with `E (p^(e-3)) (H n)` for an explicit cubic `H`.  Since `prodCoord3 p e 1 A C = 1 + p³ v`
  with `v` an explicit polynomial in `n` (this is `(D1)`+`(D2)`: the linear and quadratic
  coefficients of the product coordinate are `p²`-divisible), the phase is a character of the
  group `1 + p³ Z`, evaluated through the *bijection* `v ↦ 1 + p³ v`; the discrepancy between
  that bijection and the group parametrisation is exactly the `p`-adic logarithm, and `(D3)`
  makes the cubic coefficient of the logarithm a unit.
-/

set_option maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.LinnikBurgess

open scoped BigOperators
open Commons.NumberTheory.DirichletCharacter

variable {p e : ℕ}

/-! ## The case `p = 3` is vacuous -/

/-- For `p = 3` the three divisibility hypotheses on the power-sum defects are contradictory:
reduce modulo `3` and use `x³ = x` on `ZMod 3`. -/
private lemma three_case_false {A C : Fin 3 → ZMod (3 ^ e)} (he : 1 ≤ e)
    (h1 : (3 : ℕ) ^ 2 ∣ (ddDsum 3 e 1 A C).val)
    (h3 : ¬ (3 : ℕ) ∣ (ddDsum 3 e 3 A C).val) : False := by
  have hd : 3 ∣ 3 ^ e := pow_dvd_pow 3 he
  have hcube : ∀ x : ZMod 3, x ^ 3 = x := fun x => by simpa using ZMod.pow_card x
  have hzero : ZMod.castHom hd (ZMod 3) (ddDsum 3 e 1 A C) = 0 := by
    refine (castHom_eq_zero_iff_dvd_val_one hd _).mpr ?_
    exact dvd_trans (by norm_num : (3:ℕ) ∣ 3 ^ 2) h1
  have hEq : ZMod.castHom hd (ZMod 3) (ddDsum 3 e 3 A C) = 0 := by
    have hred : ZMod.castHom hd (ZMod 3) (ddDsum 3 e 3 A C)
        = (∑ l : Fin 3, (ZMod.castHom hd (ZMod 3) (A l)) ^ 3)
          - (∑ l : Fin 3, (ZMod.castHom hd (ZMod 3) (C l)) ^ 3) := by
      simp only [ddDsum, map_sub, map_sum, map_pow]
    rw [hred, Finset.sum_congr rfl (fun l _ => hcube _),
      Finset.sum_congr rfl (fun l _ => hcube _)]
    have h1' : ZMod.castHom hd (ZMod 3) ((∑ l : Fin 3, A l) - (∑ l : Fin 3, C l)) = 0 := by
      simpa only [ddDsum, pow_one] using hzero
    rw [map_sub, map_sum, map_sum] at h1'
    rw [sub_eq_zero] at h1' ⊢
    exact h1'
  exact h3 ((castHom_eq_zero_iff_dvd_val_one hd _).mp hEq)

/-- A prime `p ≠ 2` which is not `3` is at least `5`. -/
private lemma five_le_of_ne_two_ne_three [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) : 5 ≤ p := by
  have hp := Fact.out (p := p.Prime)
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have h2 := hp.two_le
  omega

/-! ## The factor `p` and the reduction from `e - 2` to `e - 3` digits -/

/-- Under `(D1)` and `(D2)` the level sum at level `1` over `ZMod (p^(e-2))` is `p` times the
level sum over `ZMod (p^(e-3))`. -/
private lemma levelSum3_degenerate_reduce [Fact p.Prime] (hp2 : p ≠ 2) (he : 4 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive)
    (A C : Fin 3 → ZMod (p ^ e))
    (h1 : (p : ℕ) ^ 2 ∣ (ddDsum p e 1 A C).val)
    (h2 : (p : ℕ) ∣ (ddDsum p e 2 A C).val) :
    levelSum3 p e 1 (e - 2) χ A C = (p : ℂ) * levelSum3 p e 1 (e - 3) χ A C := by
  obtain ⟨m, hm⟩ := h1
  have hpe : p ≠ 0 := (Fact.out (p := p.Prime)).ne_zero
  -- κ with `(ddDsum p e 1 A C).val = p * κ`, namely `κ = p * m`
  have hsum : (∑ l : Fin 3, A l) - (∑ l : Fin 3, C l)
      = (((p : ℕ) ^ 1 * (p * m) : ℕ) : ZMod (p ^ e)) := by
    have hdm : ddDsum p e 1 A C = (∑ l : Fin 3, A l) - (∑ l : Fin 3, C l) := by
      simp [ddDsum]
    rw [← hdm, ← ZMod.natCast_zmod_val (ddDsum p e 1 A C), hm]
    push_cast
    ring
  have hpκ : (p : ℕ) ∣ p * m := dvd_mul_right p m
  have hΔ : (p : ℕ) ∣ ((∑ l : Fin 3, A l ^ 2) - (∑ l : Fin 3, C l ^ 2) : ZMod (p ^ e)).val := by
    simpa only [ddDsum] using h2
  have hstep := levelSum3_degenerate_step (p := p) (e := e) (ℓ := 1) (M := e - 2) hp2
    (by omega) le_rfl (by omega) (by omega) χ hχ A C (p * m) hsum hΔ
  rw [if_pos hpκ] at hstep
  rw [hstep, show e - 2 - 1 = e - 3 by omega]



/-! ## Auxiliary facts: the exponential `E`, units in `ZMod (p^N)`, and reduction of `ZMod` -/

/-- `E N 1` is a primitive `N`-th root of unity. -/
lemma E_one_isPrimitiveRoot (N : ℕ) [NeZero N] :
    IsPrimitiveRoot (Commons.NumberTheory.GaussSum.E N 1) N := by
  rw [Commons.NumberTheory.GaussSum.E_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) / (N : ℂ))
      = 2 * (Real.pi : ℂ) * Complex.I / (N : ℂ) := by push_cast; ring
  rw [h]
  exact Complex.isPrimitiveRoot_exp N (NeZero.ne N)

/-- Powers of `E N 1` are again values of `E N`. -/
lemma E_one_pow (N : ℕ) [NeZero N] (k : ℕ) :
    (Commons.NumberTheory.GaussSum.E N 1) ^ k
      = Commons.NumberTheory.GaussSum.E N ((k : ℕ) : ℤ) := by
  unfold Commons.NumberTheory.GaussSum.E
  rw [← AddChar.map_nsmul_eq_pow (ZMod.stdAddChar) k ((1 : ℤ) : ZMod N)]
  congr 1
  push_cast
  rw [nsmul_eq_mul, mul_one]

/-- `E N` only depends on the class modulo `N`. -/
lemma E_eq_of_cast_eq {N : ℕ} [NeZero N] {j k : ℤ}
    (h : ((j : ℤ) : ZMod N) = ((k : ℤ) : ZMod N)) :
    Commons.NumberTheory.GaussSum.E N j = Commons.NumberTheory.GaussSum.E N k := by
  unfold Commons.NumberTheory.GaussSum.E
  rw [h]

/-- A unit of `ZMod (p^N)` (`N ≥ 1`) has a representative which is not divisible by `p`. -/
lemma not_dvd_val_of_isUnit {p N : ℕ} [Fact p.Prime] (hN : 1 ≤ N) {x : ZMod (p ^ N)}
    (hx : IsUnit x) : ¬ p ∣ x.val := by
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N (Fact.out : p.Prime).ne_zero⟩
  have hcop : x.val.Coprime (p ^ N) := by
    rw [← ZMod.natCast_zmod_val x] at hx
    exact (ZMod.isUnit_iff_coprime x.val (p ^ N)).mp hx
  intro hd
  have h1 : p ∣ Nat.gcd x.val (p ^ N) := Nat.dvd_gcd hd (by simpa using pow_dvd_pow p hN)
  have hg : Nat.gcd x.val (p ^ N) = 1 := hcop
  rw [hg] at h1
  exact (Fact.out : p.Prime).not_dvd_one h1

/-- If `x : ZMod (p^e)` is not a multiple of `p`, then its canonical representative is not
divisible by `p`. -/
lemma not_dvd_val_of_not_prime_mul {p e : ℕ} [NeZero (p ^ e)] {x : ZMod (p ^ e)}
    (h : ¬ ∃ t : ZMod (p ^ e), x = (p : ZMod (p ^ e)) * t) : ¬ p ∣ x.val := by
  intro hd
  obtain ⟨k, hk⟩ := hd
  refine h ⟨(k : ZMod (p ^ e)), ?_⟩
  rw [← ZMod.natCast_zmod_val x, hk]
  push_cast
  ring

/-- Conversely, an element of `ZMod (p^e)` whose representative is not divisible by `p` is a
unit. -/
lemma isUnit_of_not_dvd_val {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) {x : ZMod (p ^ e)}
    (h : ¬ p ∣ x.val) : IsUnit x := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e (Fact.out : p.Prime).ne_zero⟩
  have hcop : x.val.Coprime (p ^ e) := by
    rw [Nat.coprime_pow_right_iff (by omega : 0 < e)]
    exact (((Fact.out : p.Prime).coprime_iff_not_dvd).mpr h).symm
  rw [← ZMod.natCast_zmod_val x]
  exact (ZMod.isUnit_iff_coprime x.val (p ^ e)).mpr hcop

/-! ## The target -/

theorem dd_levelSum_eq_cubicSum {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 4 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive)
    (A C : Fin 3 → ZMod (p ^ e))
    (h1 : (p : ℕ) ^ 2 ∣ (Work.LinnikBurgess.ddDsum p e 1 A C).val)
    (h2 : (p : ℕ) ∣ (Work.LinnikBurgess.ddDsum p e 2 A C).val)
    (h3 : ¬ (p : ℕ) ∣ (Work.LinnikBurgess.ddDsum p e 3 A C).val) :
    ∃ H : Polynomial ℤ, Work.LinnikBurgess.IsCubic p H ∧
      ‖Commons.NumberTheory.DirichletCharacter.levelSum3 p e 1 (e - 2) χ A C‖
        = (p : ℝ) * ‖Commons.NumberTheory.GaussSum.Tsum (p ^ (e - 3)) H‖ := by
  by_cases hp3 : p = 3
  · subst hp3
    exact (three_case_false (e := e) (A := A) (C := C) (by omega) h1 h3).elim
  · have hpP : p.Prime := Fact.out
    have hKe : e - 3 ≤ e := by omega
    have hK1 : 1 ≤ e - 3 := by omega
    haveI : NeZero (p ^ (e - 3)) := ⟨pow_ne_zero _ hpP.ne_zero⟩
    -- ## Step 1: the reduction `e - 2 ↦ e - 3`
    have hred : Commons.NumberTheory.DirichletCharacter.levelSum3 p e 1 (e - 2) χ A C
        = (p : ℂ) * Commons.NumberTheory.DirichletCharacter.levelSum3 p e 1 (e - 3) χ A C :=
      levelSum3_degenerate_reduce hp2 he χ hχ A C h1 h2
    -- ## Step 2: the product coordinate is `1 + p³ U(w)` with an explicit `U`
    obtain ⟨a, b, G, haD, hbE, hG⟩ := ddProdCoord3Cubic hp2 hp3 (by omega) A C h1 h2 h3
    -- ## Step 3: the reduction to level `e - 3`
    set ρ : ZMod (p ^ e) →+* ZMod (p ^ (e - 3)) :=
      ZMod.castHom (pow_dvd_pow p hKe) (ZMod (p ^ (e - 3))) with hρdef
    -- ## Step 4: the character value at `1 + p³`
    have hζ0 : IsPrimitiveRoot (χ ((1 + p ^ 3 : ℕ) : ZMod (p ^ e))) (p ^ (e - 3)) :=
      ddChiLevelPrimitive hp2 (j := 3) (by norm_num) (by omega) χ hχ
    obtain ⟨c, _hc_lt, hc_cop, hc_eq⟩ :=
      (IsPrimitiveRoot.isPrimitiveRoot_iff (E_one_isPrimitiveRoot (p ^ (e - 3)))).mp hζ0
    -- ## Step 5: the truncated logarithm at level `e - 3` applied to `V`
    have hlam_unit : IsUnit (ddLog p (e - 3) 1) := ddLog_one_isUnit hK1
    set V : Polynomial (ZMod (p ^ (e - 3))) :=
      Polynomial.C (ρ a) * Polynomial.X + Polynomial.C (ρ b) * Polynomial.X ^ 2
        + Polynomial.C (ρ (ddE3 A C)) * Polynomial.X ^ 3
        + Polynomial.C (p : ZMod (p ^ (e - 3))) * G.map ρ with hVdef
    obtain ⟨W'', hW''⟩ :=
      ddLogPolyCompShape (p := p) (K := e - 3) hK1 (ρ a) (ρ b) (ρ (ddE3 A C)) (G.map ρ)
    have hcomp : (ddLogPoly p (e - 3)).comp V
        = Polynomial.C (ρ a) * Polynomial.X + Polynomial.C (ρ b) * Polynomial.X ^ 2
          + Polynomial.C (ρ (ddE3 A C)) * Polynomial.X ^ 3
          + Polynomial.C (p : ZMod (p ^ (e - 3))) * W'' := by
      rw [hVdef]; exact hW''
    have hcompEval : ∀ x : ZMod (p ^ (e - 3)),
        ddLog p (e - 3) (V.eval x) = ρ a * x + ρ b * x ^ 2 + ρ (ddE3 A C) * x ^ 3
          + (p : ZMod (p ^ (e - 3))) * W''.eval x := by
      intro x
      have h1 : ddLog p (e - 3) (V.eval x) = ((ddLogPoly p (e - 3)).comp V).eval x := by
        rw [Polynomial.eval_comp, ddLogPoly_eval]
      rw [h1, hcomp]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X] <;> ring
    -- ## Step 6: the polynomial `W` whose value at `n` is `c λ⁻¹ L(V(n))`, in cubic shape
    set w1 : ZMod (p ^ (e - 3)) := (c : ZMod (p ^ (e - 3))) * (ddLog p (e - 3) 1)⁻¹ * ρ a
      with hw1def
    set w2 : ZMod (p ^ (e - 3)) := (c : ZMod (p ^ (e - 3))) * (ddLog p (e - 3) 1)⁻¹ * ρ b
      with hw2def
    set w3 : ZMod (p ^ (e - 3)) := (c : ZMod (p ^ (e - 3))) * (ddLog p (e - 3) 1)⁻¹ * ρ (ddE3 A C)
      with hw3def
    set W' : Polynomial (ZMod (p ^ (e - 3))) :=
      Polynomial.C (c : ZMod (p ^ (e - 3))) * Polynomial.C ((ddLog p (e - 3) 1)⁻¹) * W''
      with hW'def
    set W : Polynomial (ZMod (p ^ (e - 3))) := Polynomial.C w1 * Polynomial.X
        + Polynomial.C w2 * Polynomial.X ^ 2 + Polynomial.C w3 * Polynomial.X ^ 3
        + Polynomial.C (p : ZMod (p ^ (e - 3))) * W' with hWdef
    have hW_eval : ∀ n : ℕ, W.eval ((n : ℤ) : ZMod (p ^ (e - 3)))
        = (c : ZMod (p ^ (e - 3))) * (ddLog p (e - 3) 1)⁻¹
            * ddLog p (e - 3) (V.eval ((n : ℤ) : ZMod (p ^ (e - 3)))) := by
      intro n
      rw [hWdef, hw1def, hw2def, hw3def, hW'def, hcompEval]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X]
      ring
    -- ## Step 7: `w3` is not divisible by `p`, so the lift to `ℤ[X]` exists
    have hγunit : IsUnit (ρ (ddE3 A C)) := by
      have hne : ¬ ∃ t : ZMod (p ^ e), ddE3 A C = (p : ZMod (p ^ e)) * t :=
        (ddEFacts hp2 hp3 A C h1 h2 h3).2.2
      have hnd : ¬ p ∣ (ddE3 A C).val := not_dvd_val_of_not_prime_mul hne
      exact (isUnit_of_not_dvd_val (p := p) (e := e) (by omega) hnd).map ρ
    have hw3unit : IsUnit w3 := by
      rw [hw3def]
      refine IsUnit.mul (IsUnit.mul ?_ ?_) hγunit
      · exact (ZMod.isUnit_iff_coprime c (p ^ (e - 3))).mpr hc_cop
      · exact IsUnit.of_mul_eq_one (ddLog p (e - 3) 1) (ZMod.inv_mul_of_unit _ hlam_unit)
    have hw3 : ¬ p ∣ w3.val := not_dvd_val_of_isUnit hK1 hw3unit
    obtain ⟨H, hHcubic, hHeval⟩ :=
      ddExistsIsCubicOfDecomp W W' w1 w2 w3 hw3 (by rw [hWdef])
    -- ## Step 8: the summand is `E (p^(e-3)) (H n)`
    have hterm : ∀ n : ℕ,
        Commons.NumberTheory.DirichletCharacter.phase3 p e 1 χ A C ((n : ℕ) : ZMod (p ^ e))
          = Commons.NumberTheory.GaussSum.E (p ^ (e - 3)) (H.eval (n : ℤ)) := by
      intro n
      set U : ZMod (p ^ e) := a * ((n : ℤ) : ZMod (p ^ e)) + b * ((n : ℤ) : ZMod (p ^ e)) ^ 2
          + ddE3 A C * ((n : ℤ) : ZMod (p ^ e)) ^ 3
          + (p : ZMod (p ^ e)) * G.eval ((n : ℤ) : ZMod (p ^ e)) with hUdef
      have hUn : Commons.NumberTheory.DirichletCharacter.prodCoord3 p e 1 A C
          ((n : ℤ) : ZMod (p ^ e)) = 1 + (p : ZMod (p ^ e)) ^ 3 * U := by
        rw [hUdef]; exact hG n
      have hρU : ZMod.castHom (pow_dvd_pow p hKe) (ZMod (p ^ (e - 3))) U
          = V.eval ((n : ℤ) : ZMod (p ^ (e - 3))) := by
        rw [← hρdef, hUdef, hVdef]
        have hGρ : (G.map ρ).eval (((n : ℤ) : ZMod (p ^ (e - 3))))
            = ρ (G.eval ((n : ℤ) : ZMod (p ^ e))) := by
          conv_lhs => rw [← map_intCast ρ n]
          exact Polynomial.eval_map_apply ρ _
        simp only [map_add, map_mul, map_pow, map_natCast, map_intCast, Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, hGρ,
          Polynomial.eval_natCast] <;> ring
      set m : ℕ := ((ρ (ddLog p e 1))⁻¹ * ρ (ddLog p e U)).val with hmdef
      have hpow : (1 + (p : ZMod (p ^ e)) ^ 3) ^ m = 1 + (p : ZMod (p ^ e)) ^ 3 * U := by
        rw [hmdef]
        exact ddLog_pow_eq hp2 he U
      have hcastU : ρ (ddLog p e U)
          = ddLog p (e - 3) (V.eval ((n : ℤ) : ZMod (p ^ (e - 3)))) := by
        rw [hρdef, ddLog_cast hKe U, hρU]
      have hm_eq : m = ((ddLog p (e - 3) 1)⁻¹
          * ddLog p (e - 3) (V.eval ((n : ℤ) : ZMod (p ^ (e - 3))))).val := by
        rw [hmdef, hρdef, ddLog_cast hKe 1, map_one, hcastU]
      have hn : ((n : ℕ) : ZMod (p ^ e)) = ((n : ℤ) : ZMod (p ^ e)) := by push_cast; ring
      rw [Commons.NumberTheory.DirichletCharacter.phase3_eq_chi_prodCoord3 (ℓ := 1) (by norm_num)
          χ A C, hn, hUn, ← hpow, map_pow]
      have hbase : χ (1 + (p : ZMod (p ^ e)) ^ 3) = χ ((1 + p ^ 3 : ℕ) : ZMod (p ^ e)) := by
        congr 1; push_cast; ring
      rw [hbase, ← hc_eq, ← pow_mul, E_one_pow]
      refine E_eq_of_cast_eq ?_
      push_cast
      rw [hm_eq, hHeval n, hW_eval n, ZMod.natCast_zmod_val]
      ring
    -- ## Step 9: the sum is `Tsum (p^(e-3)) H`
    have hsum : Commons.NumberTheory.DirichletCharacter.levelSum3 p e 1 (e - 3) χ A C
        = Commons.NumberTheory.GaussSum.Tsum (p ^ (e - 3)) H := by
      rw [Commons.NumberTheory.DirichletCharacter.levelSum3_eq_range_sum,
        Commons.NumberTheory.GaussSum.Tsum]
      exact Finset.sum_congr rfl (fun n _ => hterm n)
    exact ⟨H, hHcubic, by rw [hred, norm_mul, Complex.norm_natCast, hsum]⟩

end Work.LinnikBurgess

