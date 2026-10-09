import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.CompletionLocalField
import Submission.Work.LocalFields.isAdicComplete_maximalIdeal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped Valued

/-- An element of the ring of integers of a valued field lies in the maximal ideal if and only if
its valuation is `< 1`. -/
lemma mem_maximalIdeal_iff_v_lt_one {k : Type*} [Field k]
    [Valued k (WithZero (Multiplicative ℤ))] {x : 𝒪[k]} :
    x ∈ 𝓂[k] ↔ Valued.v (x : k) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rw [(Valuation.integer.integers (Valued.v)).isUnit_iff_valuation_eq_one]
  have hle : Valued.v (x : k) ≤ 1 := x.2
  constructor
  · intro h; exact lt_of_le_of_ne hle h
  · intro h; exact ne_of_lt h

/-- The natural number `n` is nonzero when it is coprime to the characteristic of the residue
field. -/
lemma nat_ne_zero_of_coprime_ringChar {k : Type*} [Field k]
    [Valued k (WithZero (Multiplicative ℤ))] {n : ℕ}
    (hn : Nat.Coprime n (ringChar (Valued.ResidueField k))) : n ≠ 0 := by
  rintro rfl
  exact CharP.ringChar_ne_one ((Nat.coprime_zero_left _).mp hn)

/-- `n` is a unit in the residue field when it is coprime to the characteristic. -/
lemma isUnit_natCast_residueField {k : Type*} [Field k]
    [Valued k (WithZero (Multiplicative ℤ))] {n : ℕ}
    (hn : Nat.Coprime n (ringChar (Valued.ResidueField k))) :
    IsUnit ((n : 𝓀[k])) := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have hdvd : ringChar (𝓀[k]) ∣ n := (ringChar.spec (𝓀[k]) n).mp h0
  have h1 : ringChar (𝓀[k]) = 1 := Nat.eq_one_of_dvd_coprimes hn hdvd (dvd_refl _)
  exact CharP.ringChar_ne_one h1

theorem exists_pow_eq_of_one_sub_lt_one {k : Type*} [Field k]
    [Valued k (WithZero (Multiplicative ℤ))] [Work.LocalFields.IsLocalField k] {n : ℕ}
    (hn : Nat.Coprime n (ringChar (Valued.ResidueField k))) {x : k}
    (hx : Valued.v (x - 1) < 1) : ∃ y : k, y ^ n = x := by
  have hn0 : n ≠ 0 := nat_ne_zero_of_coprime_ringChar hn
  -- `x` lies in the ring of integers `𝒪[k]`
  have hx_le : Valued.v x ≤ 1 := by
    have h1 : Valued.v (1 : k) ≤ 1 := le_of_eq (map_one (Valued.v))
    have h2 : Valued.v (x - 1) ≤ 1 := le_of_lt hx
    have := Valuation.map_add_le (Valued.v) h1 h2
    simpa using this
  set a : 𝒪[k] := ⟨x, (Valuation.mem_integer_iff (Valued.v) x).mpr hx_le⟩ with ha_def
  have ha : (a : k) = x := rfl
  -- `1 - x` lies in the maximal ideal
  have hx1m : (1 - a : 𝒪[k]) ∈ 𝓂[k] := by
    rw [mem_maximalIdeal_iff_v_lt_one]
    have hcast : (((1 - a : 𝒪[k]) : k)) = 1 - x := by
      push_cast
      rw [ha]
    rw [hcast, Valuation.map_sub_swap]
    exact hx
  -- Hensel's lemma applied to `T ^ n - x` at the simple root `1` of its reduction
  let f : Polynomial 𝒪[k] := Polynomial.X ^ n - Polynomial.C a
  have hfmonic : f.Monic := by
    simpa only [f] using Polynomial.monic_X_pow_sub_C a hn0
  have hfeval : f.eval 1 ∈ 𝓂[k] := by
    have : f.eval 1 = 1 - a := by simp [f]
    rw [this]; exact hx1m
  have hderivval : f.derivative.eval 1 = (n : 𝒪[k]) := by
    simp only [f, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
      sub_zero, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      one_pow, mul_one]
  have hderiv : IsUnit ((Ideal.Quotient.mk 𝓂[k]) (f.derivative.eval 1)) := by
    rw [hderivval]
    have hunit : IsUnit ((n : 𝓀[k])) := isUnit_natCast_residueField hn
    rw [show (Ideal.Quotient.mk 𝓂[k]) (n : 𝒪[k]) = (n : 𝓀[k]) by rfl]
    exact hunit
  have hcomplete : IsAdicComplete 𝓂[k] 𝒪[k] := isAdicComplete_maximalIdeal
  have hH : HenselianRing 𝒪[k] 𝓂[k] :=
    @IsAdicComplete.henselianRing 𝒪[k] _ 𝓂[k] hcomplete
  obtain ⟨a', hroot, _hm⟩ := hH.is_henselian f hfmonic 1 hfeval hderiv
  refine ⟨(a' : k), ?_⟩
  have heval : f.eval a' = a' ^ n - a := by simp [f]
  have hco : ((a' : k)) ^ n - x = 0 := by
    have h := congrArg (fun z : 𝒪[k] => (z : k)) hroot
    rw [heval] at h
    push_cast at h
    rw [ha] at h
    simpa using h
  exact sub_eq_zero.mp hco

end Work.LocalFields
