/-
# Evaluation of power series at the class of `T` in `𝒪[F][T]/(f^{(n)}(T))`

Milne, *Classical Field Theory*, §I.3 evaluates the Lubin–Tate series `[a]` at torsion points by
substituting a topologically nilpotent element into a power series.  Here the torsion point is
replaced by the class `τ = tau` of `T` in the finite ring
`T_n = 𝒪[F][T] / (f^{(n)}(T))`, `f(T) = πT + T^q`, and one has to check Milne's two hypotheses on
the family `(τ) : Fin 1 → T_n`:

* `τ` is topologically nilpotent for the `𝔪[F]`-adic topology of `T_n`.  This is where the
  congruence `f^{(n)}(X) ≡ X ^ (q ^ n) (mod π)` is used: it gives `τ ^ (q ^ n) ∈ (π)`, and an
  element whose positive power lies in the defining ideal is topologically nilpotent.
* the family tends to `0` along the cofinite filter — automatic for the one-point index type
  `Fin 1`.

## Main results

* `NK.LocalReciprocityLubinTate.Eval.hasEval_ltTorsionRing` — `MvPowerSeries.HasEval` for `τ`;
* `NK.LocalReciprocityLubinTate.Eval.isTopologicallyNilpotent_adicTopology_of_pow_mem` — the
  general criterion for the `I`-adic topology used above.
-/
import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Eval.TorsionRing
import Submission.NK.LocalReciprocityLubinTate.Eval.ltpolyIter_sub_X_pow_mem_span
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open Filter Topology MvPowerSeries Polynomial

namespace NK.LocalReciprocityLubinTate.Eval

noncomputable section

universe u

/-- **Nilpotence criterion for an adic topology.**  If a positive power of `x` lies in the ideal
`I`, then `x` is topologically nilpotent for the `I`-adic topology:  from `x ^ d ∈ I` one gets
`x ^ k ∈ I ^ m` as soon as `k ≥ d * m`.

(For the `I`-adic topology the neighbourhoods of `0` are the powers `I ^ m`.) -/
theorem isTopologicallyNilpotent_adicTopology_of_pow_mem {A : Type u} [CommRing A]
    (I : Ideal A) {x : A} {d : ℕ} (hd : 0 < d) (hx : x ^ d ∈ I) :
    @IsTopologicallyNilpotent A _ (I.adicTopology) x := by
  show Filter.Tendsto (fun k : ℕ => x ^ k) Filter.atTop (@nhds A (I.adicTopology) 0)
  rw [I.hasBasis_nhds_zero_adic.tendsto_right_iff]
  intro m _
  filter_upwards [eventually_ge_atTop (d * m)] with k hk
  have hkm : m ≤ k / d := by
    rw [Nat.le_div_iff_mul_le hd]
    calc m * d = d * m := Nat.mul_comm m d
      _ ≤ k := hk
  have hsplit : k = k % d + d * (k / d) :=
    (Nat.div_add_mod k d).symm.trans (add_comm _ _)
  rw [hsplit, pow_add, pow_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hkm (Ideal.pow_mem_pow hx (k / d)))

/-- The class `τ = tau` of `T` in `𝒪[F][T]/(f^{(n)}(T))` satisfies `τ ^ (q ^ n) ∈ (π)`.

Indeed `f^{(n)}(X) ≡ X ^ (q ^ n) (mod π)`, i.e. `f^{(n)}(X) − X ^ (q ^ n) = π · a`, and evaluating
this congruence at `τ` (using `f^{(n)}(τ) = 0`) gives `τ ^ (q ^ n) = − π · a(τ)`. -/
private theorem tau_pow_mem_adicIdeal {F : Type u} [Field F] [ValuativeRel F]
    (π : ↥(ValuativeRel.valuation F).integer) (q n : ℕ) (hq : 2 ≤ q) :
    LTtorsionRing.tau π q n ^ q ^ n ∈ LTtorsionRing.adicIdeal π q n := by
  have hq1 : 1 ≤ q := by omega
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp
    (ltpolyIter_sub_X_pow_mem_span π q n hq1)
  have h1 : (Polynomial.aeval (LTtorsionRing.tau π q n))
      (NK.LocalReciprocityLubinTate.LTpolyIter π q n - Polynomial.X ^ (q ^ n))
      = -(LTtorsionRing.tau π q n ^ q ^ n) := by
    rw [map_sub, LTtorsionRing.tau_spec, map_pow, Polynomial.aeval_X, zero_sub]
  rw [ha, map_mul, Polynomial.aeval_C] at h1
  have h2 : LTtorsionRing.tau π q n ^ q ^ n
      = -(LTtorsionRing.piT π q n * (Polynomial.aeval (LTtorsionRing.tau π q n)) a) := by
    have hh := congrArg Neg.neg h1
    rw [neg_neg] at hh
    exact hh.symm
  rw [h2]
  exact neg_mem (Ideal.mul_mem_right _ _
    (Ideal.subset_span (Set.mem_singleton _)))

/-- **The family `(τ)` admits evaluation of power series.**  The class `τ` of `T` in
`𝒪[F][T]/(f^{(n)}(T))` is topologically nilpotent (its `q ^ n`-th power lies in `(π)`), and the
constant family on the one-point index `Fin 1` tends to zero along the cofinite filter. -/
theorem hasEval_ltTorsionRing {F : Type u} [Field F] [ValuativeRel F]
    (π : ↥(ValuativeRel.valuation F).integer) (q n : ℕ) (hq : 2 ≤ q) :
    MvPowerSeries.HasEval
      (fun _ : Fin 1 => NK.LocalReciprocityLubinTate.Eval.LTtorsionRing.tau π q n) := by
  refine ⟨fun _ => ?_, ?_⟩
  · exact isTopologicallyNilpotent_adicTopology_of_pow_mem (LTtorsionRing.adicIdeal π q n)
      (Nat.pow_pos (by omega)) (tau_pow_mem_adicIdeal π q n hq)
  · simp

end

end NK.LocalReciprocityLubinTate.Eval
