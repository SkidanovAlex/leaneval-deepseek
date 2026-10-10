import Mathlib
import Submission.Work.MotV5.Nodes.maxValueAttainedTwice
import Submission.Work.MotV5.Nodes.powLinearDependence
import Submission.Work.MotV5.Nodes.powSubEqDiv

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `[L : F]!`-th power of a value lies in the value group of the restriction

Let `L / F` be a finite extension of fields (with `L` a field, `L` an `F`-algebra), let
`w : Valuation L Γ` be a valuation with values in a linearly ordered commutative group with zero
`Γ`, and let `x ∈ L` with `w x ≠ 0`.  Write `v = w ∘ algebraMap F L` for the restriction of `w`
to `F`.  This file proves

`(w x) ^ [L : F]! ∈ v(F^*)`,

i.e. the `[L : F]!`-th power of a value of `w` lies in the value group of the restriction `v`.

## Proof

The `[L : F] + 1` powers `1, x, …, x ^ [L : F]` are linearly dependent over `F` (an
`F`-vector space of dimension `[L : F]`), so there is a nontrivial relation `Σ gᵢ xⁱ = 0` with
`gᵢ ∈ F` (`powLinearDependence`, from
`Submission/Work/MotV5/Nodes/powLinearDependence.lean`).  In the sum `Σ (gᵢ xⁱ) = 0` the maximal
value of the summands is attained at least twice (`maxValueAttainedTwice`, from
`Submission/Work/MotV5/Nodes/maxValueAttainedTwice.lean`): there are `i ≠ j` with

`v (gᵢ) * (w x)ⁱ = v (g_j) * (w x)^j ≠ 0`.

Assume `i < j` (otherwise swap the two).  Cancelling powers (`powSubEqDiv`, from
`Submission/Work/MotV5/Nodes/powSubEqDiv.lean`) gives

`(w x) ^ (j - i) = v (gᵢ / g_j)`  with  `0 < j - i ≤ [L : F]`,

so *some* positive power `m ≤ [L : F]` of `w x` is the value of an element of `F`
(`exists_pow_eq_val_of_finrank`).  Since `m ∣ [L : F]!`, raising to the `[L : F]! / m`-th power
exhibits `(w x) ^ [L : F]!` as a value of an element of `F`, i.e. as an element of `v(F^*)`.
-/

set_option autoImplicit false

namespace Work.MotV5.Nodes

/-- **The key step.**  For `x : L` with `w x ≠ 0` there is a positive `m ≤ [L : F]` such that
`(w x) ^ m` is the value under `w` of an element of `F`. -/
theorem exists_pow_eq_val_of_finrank {F L Γ : Type*} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation L Γ) {x : L} (hx : w x ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ m ≤ Module.finrank F L ∧
      ∃ y : F, w (algebraMap F L y) = w x ^ m := by
  classical
  obtain ⟨g, hgne, hgsum⟩ := powLinearDependence (F := F) (L := L) x
  have hx0 : x ≠ 0 := (Valuation.ne_zero_iff w).mp hx
  have hne : ∃ i : Fin (Module.finrank F L + 1),
      w (algebraMap F L (g i) * x ^ ((i : ℕ))) ≠ 0 := by
    obtain ⟨i₀, hi₀⟩ := hgne
    have hv : (w.comap (algebraMap F L)) (g i₀) ≠ 0 :=
      (Valuation.ne_zero_iff (w.comap (algebraMap F L))).mpr hi₀
    have hwxi : w (x ^ ((i₀ : ℕ))) ≠ 0 :=
      (Valuation.ne_zero_iff w).mpr (pow_ne_zero _ hx0)
    refine ⟨i₀, fun hzero => ?_⟩
    refine mul_ne_zero hv hwxi ?_
    show w (algebraMap F L (g i₀)) * w (x ^ ((i₀ : ℕ))) = 0
    rw [← Valuation.map_mul w (algebraMap F L (g i₀)) (x ^ ((i₀ : ℕ)))]
    exact hzero
  obtain ⟨p, q, hpqne, hp0, hpqeq, -⟩ :=
    maxValueAttainedTwice w
      (fun i : Fin (Module.finrank F L + 1) => algebraMap F L (g i) * x ^ ((i : ℕ)))
      hne hgsum
  have key : ∀ p q : Fin (Module.finrank F L + 1), (p : ℕ) ≤ (q : ℕ) → p ≠ q →
      w (algebraMap F L (g p) * x ^ ((p : ℕ))) = w (algebraMap F L (g q) * x ^ ((q : ℕ))) →
      w (algebraMap F L (g p) * x ^ ((p : ℕ))) ≠ 0 →
      ∃ m : ℕ, 0 < m ∧ m ≤ Module.finrank F L ∧
        ∃ y : F, w (algebraMap F L y) = w x ^ m := by
    intro p q hpq hpqne heq hp0
    have hqw : w (algebraMap F L (g q) * x ^ ((q : ℕ))) ≠ 0 := by
      rw [← heq]; exact hp0
    have hpw' : w (algebraMap F L (g p) * x ^ ((p : ℕ)))
        = w (algebraMap F L (g p)) * w x ^ ((p : ℕ)) := by
      rw [Valuation.map_mul, Valuation.map_pow]
    have hqw' : w (algebraMap F L (g q) * x ^ ((q : ℕ)))
        = w (algebraMap F L (g q)) * w x ^ ((q : ℕ)) := by
      rw [Valuation.map_mul, Valuation.map_pow]
    have hmain : w (algebraMap F L (g p)) * w x ^ ((p : ℕ))
        = w (algebraMap F L (g q)) * w x ^ ((q : ℕ)) := by
      rw [← hpw', ← hqw']; exact heq
    have hb : w (algebraMap F L (g q)) ≠ 0 := by
      intro hz
      exact hqw (by rw [hqw', hz, zero_mul])
    have hpow := powSubEqDiv hx hb hpq hmain
    have hm0 : 0 < (q : ℕ) - (p : ℕ) := by
      have hne' : (p : ℕ) ≠ (q : ℕ) := Fin.val_ne_of_ne hpqne
      omega
    have hmn : (q : ℕ) - (p : ℕ) ≤ Module.finrank F L := by
      have hl := q.isLt
      omega
    refine ⟨(q : ℕ) - (p : ℕ), hm0, hmn, g p / g q, ?_⟩
    rw [map_div₀, Valuation.map_div]
    exact hpow.symm
  rcases lt_or_ge (q : ℕ) (p : ℕ) with h | h
  · refine key q p (le_of_lt h) (Ne.symm hpqne) hpqeq.symm ?_
    rw [← hpqeq]; exact hp0
  · exact key p q h hpqne hpqeq hp0

theorem powFactorialMemValueGroup {F L Γ : Type*} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [Module.Free F L] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation L Γ) {x : L} (hx : w x ≠ 0) :
    (Units.mk0 (w x) hx) ^ (Nat.factorial (Module.finrank F L)) ∈
      MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass (w.comap (algebraMap F L))) := by
  classical
  obtain ⟨m, hm0, hmn, y, hy⟩ := exists_pow_eq_val_of_finrank (F := F) w hx
  -- some positive power `m ≤ [L : F]` of `w x` is a value of an element of `F`
  have hdvd : m ∣ Nat.factorial (Module.finrank F L) := Nat.dvd_factorial hm0 hmn
  set r : ℕ := Nat.factorial (Module.finrank F L) / m with hr
  have hmr : m * r = Nat.factorial (Module.finrank F L) := by
    rw [hr]
    exact Nat.mul_div_cancel' hdvd
  -- `y ^ r` realises the `[L : F]!`-th power of `w x` as a value on `F`
  refine MonoidWithZeroHom.mem_valueGroup _ ⟨y ^ r, ?_⟩
  rw [show MonoidWithZeroHom.ofClass (w.comap (algebraMap F L)) (y ^ r)
      = w (algebraMap F L (y ^ r)) from rfl]
  rw [map_pow, Valuation.map_pow, hy, ← pow_mul, hmr]
  rw [Units.val_pow_eq_pow_val, Units.val_mk0]

end Work.MotV5.Nodes
