import Mathlib
import Submission.CDT.SympDescent
import Submission.CDT.EichlerInput

/-!
# Lemma `Gdenominatortype` (CDT): denominator doubling under symmetrization

In CDT (arXiv:2408.15403), §"The symmetrization of `H(x)`", the paper proves

> **Lemma `Gdenominatortype`.** If `a, b, c ∈ ℚ`, then
> `G(y) = Sym⁺H(x)` has denominator type `[1,2,…,2n]²`.
> (`G(y) = H(x) + H(x/(x−1)) ∈ ℂ⟦y⟧` with
> `H = aH_A + bH_B + cH_C`.)

The input is the denominator type `[1..n]²` of `H` (paper Lemma `defabc`
item 2, isolated in this repository as the hypothesis `HasDenomTypeSq` of
`ModularIntegralityB`/`ModularIntegralityC`, combined by
`functionsH_denomtype_int`); the *doubling* `[1..n]² → [1..2n]²` is pure
algebra — it is the content of this module.

**Mechanism.** By `SympDescent`, the symmetrization is computed by the
triangular descent recursion (`sympDescCoeff_eq`)

`gₙ = (f_{2n} − Σ_{m<n} g_m·coeff (2n)(yᵐ))·(coeff (2n)(yⁿ))⁻¹`,

and `coeff (2n)(yⁿ) = (−1)ⁿ` is a *unit* (`coeff_sympY_pow_diag`), while
`coeff (2n)(yᵐ) ∈ ℤ` (`sympY_IntSeries`).  Hence

`[1..2n]²·gₙ = ([1..2n]²·f_{2n} − Σ_{m<n} ([1..2n]²·g_m)·coeff (2n)(yᵐ))·(−1)ⁿ`,

and every term on the right is an integer: `[1..2n]²·f_{2n} ∈ ℤ` by the
input hypothesis (the input says `[1..m]²·f_m ∈ ℤ` and `[1..m]` divides
`[1..2n]` for `m ≤ 2n`), and `[1..2n]²·g_m` is an integer for `m < n` by
the induction hypothesis (`[1..2m] ∣ [1..2n]`).

**Proved here** (no axioms, no `sorry`):

* `HasDenomTypeSq_subst` — denominator type `[1..n]²` is preserved by
  substitution with an integer-coefficient series of positive valuation
  (the `HasDenomTypeSq` analogue of `intSeries_subst`);
* `sympDescCoeff_denomType` — the descent coefficients of a
  `[1..n]²`-denominator series have denominator type `[1..2n]²`;
* `sympSym_denomType` — the same for `Sym⁺H` (the symmetrization of a
  power series with `[1..n]²`-denominator-type coefficients);
* `Gdenominatortype` — **the paper's Lemma `Gdenominatortype`**, for
  `H = aH_A + bH_B + cH_C` with `a, b, c ∈ ℤ` under the node-(2) inputs
  `ModularIntegralityB`/`ModularIntegralityC` (`functionsH_denomtype_int`).
-/

noncomputable section

open PowerSeries

namespace Submission.CDT

/-! ## denominator types and substitution -/

/-- **denominator type `[1..n]²` is preserved by substitution** with a
series `b` having `coeff 0 b = 0` and integer powers: if all coefficients of
`F` satisfy `[1..n]²·Fₙ ∈ ℤ`, so do those of `F ∘ b`. -/
lemma HasDenomTypeSq_subst {F b : PowerSeries ℚ}
    (hF : HasDenomTypeSq (fun n => PowerSeries.coeff n F))
    (hb0 : PowerSeries.coeff 0 b = 0) (hbp : ∀ m, IntSeries (b ^ m)) :
    HasDenomTypeSq (fun n => PowerSeries.coeff n (F.subst b)) := by
  intro n
  change ∃ z : ℤ, ((lcmRange n : ℚ)) ^ 2 * PowerSeries.coeff n (F.subst b) = z
  rw [coeff_subst_range F hb0 n]
  have hsplit : ((lcmRange n : ℚ)) ^ 2 *
      (∑ m ∈ Finset.range (n + 1), PowerSeries.coeff m F * PowerSeries.coeff n (b ^ m))
      = ∑ m ∈ Finset.range (n + 1),
          (((lcmRange n : ℚ)) ^ 2 * PowerSeries.coeff m F) * PowerSeries.coeff n (b ^ m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [hsplit]
  have ha : ∀ m ∈ Finset.range (n + 1), ∃ z : ℤ,
      (z : ℚ) = ((lcmRange n : ℚ)) ^ 2 * PowerSeries.coeff m F := by
    intro m hm
    have hmn : m ≤ n := by
      have := Finset.mem_range.mp hm
      omega
    rcases hF m with ⟨z, hz⟩
    obtain ⟨q, hq⟩ := lcmRange_dvd_of_le hmn
    have hL : ((lcmRange n : ℚ)) = ((lcmRange m : ℚ)) * (q : ℚ) := by
      rw [show ((lcmRange m : ℚ)) * (q : ℚ) = (((lcmRange m) * q : ℕ) : ℚ) by
        push_cast
        ring]
      rw [← hq]
    refine ⟨q ^ 2 * z, ?_⟩
    calc
      ((q ^ 2 * z : ℤ) : ℚ) = (q : ℚ) ^ 2 * (z : ℚ) := by push_cast; ring
      _ = (q : ℚ) ^ 2 * (((lcmRange m : ℚ)) ^ 2 * PowerSeries.coeff m F) := by rw [← hz]
      _ = ((lcmRange n : ℚ)) ^ 2 * PowerSeries.coeff m F := by rw [hL]; ring
  have hb : ∀ m ∈ Finset.range (n + 1), ∃ z : ℤ,
      (z : ℚ) = PowerSeries.coeff n (b ^ m) := by
    intro m hm
    exact hbp m n
  obtain ⟨Z, hZ⟩ := exists_int_finset_sum_mul (s := Finset.range (n + 1))
    (a := fun m => ((lcmRange n : ℚ)) ^ 2 * PowerSeries.coeff m F)
    (b := fun m => PowerSeries.coeff n (b ^ m)) ha hb
  exact ⟨Z, hZ.symm⟩

/-- the coefficients of `sympY^m` are integers -/
lemma exists_int_coeff_sympY_pow (k m : ℕ) :
    ∃ z : ℤ, (z : ℚ) = PowerSeries.coeff k (sympY ^ m) :=
  intSeries_pow sympY_IntSeries m k

/-! ## the descent coefficients of a `[1..n]²`-denominator series -/

/-- **the descent coefficients of a `[1..n]²`-denominator series have
denominator type `[1..2n]²`**: the algebraic heart of Lemma
`Gdenominatortype`. -/
lemma sympDescCoeff_denomType (f : PowerSeries ℚ)
    (hf : HasDenomTypeSq (fun n => PowerSeries.coeff n f)) :
    ∀ n, ∃ z : ℤ, ((lcmRange (2 * n) : ℚ)) ^ 2 * sympDescCoeff f n = z := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hsum : ∃ Z : ℤ, (Z : ℚ) = ∑ m ∈ Finset.range n,
        (((lcmRange (2 * n) : ℚ)) ^ 2 * sympDescCoeff f m)
          * PowerSeries.coeff (2 * n) (sympY ^ m) := by
      apply exists_int_finset_sum_mul (s := Finset.range n)
      · intro m hm
        have hmn : m < n := Finset.mem_range.mp hm
        rcases ih m hmn with ⟨z, hz⟩
        obtain ⟨q, hq⟩ := lcmRange_dvd_of_le (show 2 * m ≤ 2 * n by omega)
        have hL : ((lcmRange (2 * n) : ℚ)) = ((lcmRange (2 * m) : ℚ)) * (q : ℚ) := by
          rw [show ((lcmRange (2 * m) : ℚ)) * (q : ℚ)
              = (((lcmRange (2 * m)) * q : ℕ) : ℚ) by push_cast; ring]
          rw [← hq]
        refine ⟨q ^ 2 * z, ?_⟩
        calc
          ((q ^ 2 * z : ℤ) : ℚ)
              = (q : ℚ) ^ 2 * (z : ℚ) := by push_cast; ring
          _ = (q : ℚ) ^ 2 * (((lcmRange (2 * m) : ℚ)) ^ 2 * sympDescCoeff f m) := by rw [hz]
          _ = ((lcmRange (2 * n) : ℚ)) ^ 2 * sympDescCoeff f m := by rw [hL]; ring
      · intro m hm
        exact exists_int_coeff_sympY_pow (2 * n) m
    rcases hsum with ⟨Z, hZ⟩
    rcases hf (2 * n) with ⟨zf, hzf⟩
    refine ⟨(zf - Z) * (-1 : ℤ) ^ n, ?_⟩
    rw [sympDescCoeff_eq_sign f n]
    have hLsum : ((lcmRange (2 * n) : ℚ)) ^ 2 * (∑ m ∈ Finset.range n,
          sympDescCoeff f m * PowerSeries.coeff (2 * n) (sympY ^ m)) = (Z : ℚ) := by
      rw [hZ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    calc
      ((lcmRange (2 * n) : ℚ)) ^ 2 *
          ((PowerSeries.coeff (2 * n) f - ∑ m ∈ Finset.range n,
              sympDescCoeff f m * PowerSeries.coeff (2 * n) (sympY ^ m))
            * (((-1 : ℤ) ^ n) : ℚ))
          = (((lcmRange (2 * n) : ℚ)) ^ 2 * PowerSeries.coeff (2 * n) f
              - ((lcmRange (2 * n) : ℚ)) ^ 2 * (∑ m ∈ Finset.range n,
                  sympDescCoeff f m * PowerSeries.coeff (2 * n) (sympY ^ m)))
              * (((-1 : ℤ) ^ n) : ℚ) := by ring
      _ = ((zf : ℚ) - (Z : ℚ)) * (((-1 : ℤ) ^ n) : ℚ) := by rw [hzf, hLsum]
      _ = (((zf - Z) * (-1 : ℤ) ^ n : ℤ) : ℚ) := by push_cast; ring

/-! ## the symmetrization -/

/-- **denominator doubling for `Sym⁺H`**: if all coefficients of `H` satisfy
`[1..n]²·Hₙ ∈ ℤ`, then the symmetrization `G = Sym⁺H` has denominator type
`[1..2n]²`. -/
theorem sympSym_denomType (H : PowerSeries ℚ)
    (hH : HasDenomTypeSq (fun n => PowerSeries.coeff n H)) :
    ∀ n, ∃ z : ℤ,
      ((lcmRange (2 * n) : ℚ)) ^ 2 * PowerSeries.coeff n (sympSym H) = z := by
  have hsub : HasDenomTypeSq (fun n => PowerSeries.coeff n (H.subst sympPhi)) :=
    HasDenomTypeSq_subst hH coeff_sympPhi_zero
      (fun m => intSeries_pow sympPhi_IntSeries m)
  have hcomb : HasDenomTypeSq (fun n => PowerSeries.coeff n (H + H.subst sympPhi)) := by
    intro k
    change ∃ z : ℤ, ((lcmRange k : ℚ)) ^ 2 * PowerSeries.coeff k (H + H.subst sympPhi) = z
    rw [map_add]
    simpa [mul_add] using HasDenomTypeSq_add hH hsub k
  intro n
  rw [sympSym_eq_sympDesc H, sympDesc_coeff]
  exact sympDescCoeff_denomType (H + H.subst sympPhi) hcomb n

/-- **Lemma `Gdenominatortype` of CDT** (paper §"The symmetrization of
`H(x)`"): for `H = aH_A + bH_B + cH_C` with `a, b, c ∈ ℤ`, the
symmetrization `G = Sym⁺H` has denominator type `[1,2,…,2n]²` — under the
node-(2) modular inputs `ModularIntegralityB`, `ModularIntegralityC`
(which supply `[1..n]²·bₙ, [1..n]²·cₙ ∈ ℤ`; `aₙ ∈ ℤ` is free). -/
theorem Gdenominatortype (a b c : ℤ) (hB : ModularIntegralityB) (hC : ModularIntegralityC) :
    ∀ n, ∃ z : ℤ, ((lcmRange (2 * n) : ℚ)) ^ 2
      * PowerSeries.coeff n (sympSym (ZagierH (a : ℚ) (b : ℚ) (c : ℚ))) = z := by
  refine sympSym_denomType _ ?_
  intro n
  change ∃ z : ℤ, ((lcmRange n : ℚ)) ^ 2
    * PowerSeries.coeff n (ZagierH (a : ℚ) (b : ℚ) (c : ℚ)) = z
  rw [ZagierH_eq_mk, PowerSeries.coeff_mk]
  exact functionsH_denomtype_int a b c hB hC n

end Submission.CDT
