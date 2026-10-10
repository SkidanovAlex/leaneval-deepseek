import Mathlib
import Submission.Work.Genus.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.CharP

open Polynomial

/-- **In characteristic `p` over a perfect field, the kernel of `d/dt` is the subfield of `p`-th
powers.**  If `deriv f = 0` then `f = g ^ p` for some `g`.

Route: `f = num / denom` with `num' * denom = num * denom'`; coprimality gives `num ∣ num'` and
`denom ∣ denom'`; if `num' ≠ 0` then `natDegree num' < natDegree num` contradicts divisibility, so
`num' = 0`, and similarly `denom' = 0`.  By `Polynomial.expand_contract : derivative f = 0 →
∃ g, f = Polynomial.expand F p g` (characteristic `p`), `num = expand F p num₀` and
`denom = expand F p denom₀` for polynomials `num₀, denom₀`; `PerfectField F` (via
`PerfectField.toPerfectRing` and `PerfectRing.bijective_frobenius`) lets one lift the coefficients
and write `num₀ = (num₁) ^ p`, `denom₀ = (denom₁) ^ p` for polynomials `num₁, denom₁`, whence
`f = (num₁ / denom₁) ^ p`. -/
theorem exists_pow_eq_of_deriv_eq_zero {F : Type*} [Field F] {p : ℕ} [Fact p.Prime]
    [CharP F p] [PerfectField F] {f : RatFunc F} (h : Work.Genus.deriv f = 0) :
    ∃ g : RatFunc F, f = g ^ p := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  -- ## Step 1: `deriv f = 0` gives the polynomial identity `num' * denom = num * denom'`.
  have hden : (algebraMap F[X] (RatFunc F)) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have hnum : (algebraMap F[X] (RatFunc F)) f.num.derivative
      * (algebraMap F[X] (RatFunc F)) f.denom
      - (algebraMap F[X] (RatFunc F)) f.num
        * (algebraMap F[X] (RatFunc F)) f.denom.derivative = 0 := by
    have hh := h
    unfold Work.Genus.deriv at hh
    rcases (div_eq_zero_iff.mp hh) with h' | h'
    · exact h'
    · exact absurd h' (pow_ne_zero 2 hden)
  have hpoly : f.num.derivative * f.denom - f.num * f.denom.derivative = 0 := by
    refine RatFunc.algebraMap_injective F ?_
    rw [map_sub, map_mul, map_mul, map_zero]
    exact hnum
  have hmul : f.num.derivative * f.denom = f.num * f.denom.derivative := sub_eq_zero.mp hpoly
  -- ## Step 2: coprimality of the reduced form gives `num ∣ num'` and `denom ∣ denom'`.
  have hnumdvd : f.num ∣ f.num.derivative :=
    (RatFunc.isCoprime_num_denom f).dvd_of_dvd_mul_right
      (by rw [hmul]; exact dvd_mul_right _ _)
  have hdendvd : f.denom ∣ f.denom.derivative :=
    (RatFunc.isCoprime_num_denom f).symm.dvd_of_dvd_mul_right
      (by rw [mul_comm f.denom.derivative f.num, ← hmul]; exact dvd_mul_left _ _)
  -- A divisibility `num ∣ num'` together with `natDegree num' < natDegree num` forces `num' = 0`
  -- (in *every* characteristic: the derivative of a non-constant polynomial has smaller degree).
  have hnum_deriv : f.num.derivative = 0 := by
    by_cases h0 : f.num.natDegree = 0
    · exact Polynomial.derivative_of_natDegree_zero h0
    · by_contra hne
      have hle := natDegree_le_of_dvd hnumdvd hne
      have hlt := Polynomial.natDegree_derivative_lt (p := f.num) h0
      omega
  have hden_deriv : f.denom.derivative = 0 := by
    by_cases h0 : f.denom.natDegree = 0
    · exact Polynomial.derivative_of_natDegree_zero h0
    · by_contra hne
      have hle := natDegree_le_of_dvd hdendvd hne
      have hlt := Polynomial.natDegree_derivative_lt (p := f.denom) h0
      omega
  -- ## Step 3: `num` and `denom` lie in the image of `expand F p` (`Polynomial.expand_contract`).
  obtain ⟨num₀, hnum_eq⟩ : ∃ num₀ : F[X], expand F p num₀ = f.num :=
    ⟨contract p f.num, Polynomial.expand_contract p hnum_deriv hp⟩
  obtain ⟨den₀, hden_eq⟩ : ∃ den₀ : F[X], expand F p den₀ = f.denom :=
    ⟨contract p f.denom, Polynomial.expand_contract p hden_deriv hp⟩
  -- ## Step 4: lift the coefficients through the (surjective) Frobenius of the perfect field.
  have hsurj : Function.Surjective (frobenius F p) := surjective_frobenius F p
  have hmap_surj : Function.Surjective (Polynomial.map (frobenius F p)) :=
    Polynomial.map_surjective (frobenius F p) hsurj
  obtain ⟨num₁, hnum₁⟩ := hmap_surj num₀
  obtain ⟨den₁, hden₁⟩ := hmap_surj den₀
  have hnum_pow : num₁ ^ p = f.num := by
    calc num₁ ^ p = Polynomial.map (frobenius F p) (expand F p num₁) :=
          (Polynomial.map_frobenius_expand p num₁).symm
      _ = expand F p (Polynomial.map (frobenius F p) num₁) :=
          (Polynomial.map_expand (p := p) (f := frobenius F p) (q := num₁))
      _ = expand F p num₀ := by rw [hnum₁]
      _ = f.num := hnum_eq
  have hden_pow : den₁ ^ p = f.denom := by
    calc den₁ ^ p = Polynomial.map (frobenius F p) (expand F p den₁) :=
          (Polynomial.map_frobenius_expand p den₁).symm
      _ = expand F p (Polynomial.map (frobenius F p) den₁) :=
          (Polynomial.map_expand (p := p) (f := frobenius F p) (q := den₁))
      _ = expand F p den₀ := by rw [hden₁]
      _ = f.denom := hden_eq
  -- ## Step 5: assemble.
  refine ⟨algebraMap F[X] (RatFunc F) num₁ / algebraMap F[X] (RatFunc F) den₁, ?_⟩
  rw [div_pow, ← map_pow, ← map_pow, hnum_pow, hden_pow]
  exact (RatFunc.num_div_denom f).symm

end Work.Genus.CharP
