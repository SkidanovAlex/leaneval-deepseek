-- Redirected copy of `Submission.Work.DSM2p.exists_real_valuation_of_continuous` (imports re-pointed to the `AALvaln` vocabulary layer so that
-- `area_AAL_proved.lean` can import the result without an import cycle).  The original
-- file is untouched; this copy is generated mechanically.
import Mathlib
import Submission.Work.DSM2p.AALcopy_nilp_log_valuation

namespace Work.DSM2p

open scoped Classical

/-- **A real-valued valuation attached to a continuous valuation.**

Let `v : D → Γ` be a valuation on a commutative ring `D` and let `x₀ : D` be such that `v` is
*continuous* at `x₀` (the powers of `v x₀` become smaller than any prescribed positive value) and
`v x₀ ≠ 0` (so that `0 < v x₀ < 1`).  Then there is a valuation `w : D → WithZero (Multiplicative ℝ)`
which is still continuous at `x₀`, whose value at `x₀` is `< 1`, and which is `≤ 1` on any given
unit ball `t` of `v`.

The construction is the one of `Work.DSM2p.nilp_log_valuation`: the continuity hypothesis is
exactly the cofinality of the powers of `g = v x₀` below every non-zero element of `Γ`, which is
what makes Hölder's archimedean logarithm `ψ` (`Work.DSM2p.cofinal_log_real_aux`) well defined.  Its
encoding `encHom ψ` is a monotone monoid-with-zero homomorphism `Γ →*₀ WithZero (Multiplicative ℝ)`
sending `g` to `↑(ofAdd (-1)) < 1`, and `w := v.map (encHom ψ)` has all the required properties. -/
theorem exists_real_valuation_of_continuous {D : Type*} [CommRing D] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation D Γ) (x₀ : D) (t : Set D)
    (hball : IsUnitBall v t) (hlt : v x₀ < 1) (hne : v x₀ ≠ 0)
    (hcont : IsContinuousValuation x₀ v) :
    ∃ w : Valuation D (WithZero (Multiplicative ℝ)),
      IsUnitBall w t ∧ w x₀ < 1 ∧ IsContinuousValuation x₀ w := by
  have _ := hlt
  -- The continuity of `v` at `x₀` says exactly that the powers of `g = v x₀` are cofinal.
  obtain ⟨ψ, hψ1, hψg, hadd, hmono⟩ := cofinal_log_real_aux (v x₀) hne hcont
  -- The "logarithmic" encoding as an order-preserving monoid-with-zero homomorphism.
  let φo : Γ →*₀o WithZero (Multiplicative ℝ) :=
    ⟨encHom ψ hψ1 hadd, encHom_mono ψ hψ1 hadd hmono⟩
  have hφg : φo (v x₀)
      = ((Multiplicative.ofAdd (-1) : Multiplicative ℝ) : WithZero (Multiplicative ℝ)) := by
    show encHom ψ hψ1 hadd (v x₀) = _
    exact encHom_apply_of_eq_one ψ hψ1 hadd hne hψg
  refine ⟨v.map φo, ?_, ?_, ?_⟩
  · -- the unit ball: `v b ≤ 1` and `φo` is monotone with `φo 1 = 1`
    intro b hb
    rw [Valuation.map_apply]
    calc φo (v b) ≤ φo 1 := φo.monotone' (hball b hb)
      _ = 1 := map_one φo
  · -- `w x₀ = φo (v x₀) = ↑(ofAdd (-1)) < 1`
    rw [Valuation.map_apply, hφg]
    exact ofAdd_neg_one_lt_one
  · -- continuity: the powers of `w x₀ = ↑(ofAdd (-1))` tend to `0`
    intro γ hγ
    rw [Valuation.map_apply, hφg]
    exact ofAdd_neg_one_pow_cofinal γ hγ

end Work.DSM2p
