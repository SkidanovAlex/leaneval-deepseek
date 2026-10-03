/-
# `Work.KMTPlan.A6.AdelicFormPropPlus` — the adelic form of the good scales, with nonnegative
constants

This module holds the *statement* of the adelic-form input of the frozen-slice estimate
`Work.KMTPlan.A6.MdlSliceCoreGainMemLp` (paper `model-est-2`, `all-all-large-2` at `(2,2,1)`,
Krause--Mirek--Tao, Annals **195** (2022), §8), in the form the final assembly consumes.

It is the statement of `Work.KMTPlan.A6.AdelicFormProp` (`MdlAdelicDefs.lean`) **with the two
sign conditions `0 ≤ Ku` and `0 ≤ Kv` added**.  The addition is not cosmetic:

`AdelicFormProp` controls the constants `Ku`, `Kv` only through the `ℝ≥0∞`-valued bounds
`ENNReal.ofReal Ku ≤ ⋯`, and `ENNReal.ofReal` sends every nonpositive real to `0`.  Hence a
witness `Ku < 0` of `AdelicFormProp` is compatible with every one of its clauses while giving
*no* upper bound on the variation datum `∫⁻ (VrLiftData R Q u)²` (the clause
`∫⁻ ⋯ ≤ ENNReal.ofReal (Ku ^ 2)` is only a *lower* bound on `|Ku|`).  The `ZMod Q` variational
chain `Work.KMTPlan.A6.ZModChainProp`, on the other hand, needs a *nonnegative* constant `Ku`
with `ENNReal.ofReal Ku` bounded, and its conclusion carries `ENNReal.ofReal Ku`; without the
sign condition the good part of the slice cannot be bounded from the data of `AdelicFormProp`.

The proof of `AdelicFormPropPlus` is the paper's §8 content: the construction of the adelic lift
of the good scales (`exists_adelicLift`), its presentation as `zmodAvg P Q (u ·) (v ·)`
(paper `form-1`/`form-2`, `Btwist_eq_fiberSum`), the arithmetic bilinear estimate for the two
packet families at height `≤ l` (`MdlBileOfR1`, with the packets' minor-arc property), and the
`L²(ℝ; V^R(ℓ²(ZMod Q)))`-data bound for the two packet families (the adelic form of
`(lin-1)`/`(lin-2)`, i.e. the fibre-sampling form of the linear lacunary variational estimates).
The witnesses `M`, `Ku`, `Kv` are then the natural *nonnegative* constants: `M` an operator-norm
bound, `Ku`, `Kv` the (nonnegative) bounds on the two `VrLiftData` integrals.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlAdelicDefs

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7

/-- **The reflected polynomial `P̃(y) = -P(-y)`.**  The workspace's `zmodAvg P̃ Q` is the paper's
arithmetic averaging operator `A_Ẑ` for the polynomial `P`: the paper defines
`A_Ẑ(f,g)(x) = ∫_Ẑ f(x - P₁(y)) g(x - P₂(y)) dμ_Ẑ(y)` (Example `avg-mult`), i.e. with **minus**
signs, while `zmodAvg P Q u v θ = Q⁻¹ ∑_{y<Q} u(θ+y) v(θ+P(y))` carries **plus** signs.  The two
agree after the substitution `y ↦ -y`, which replaces `P` by `P̃`:

  `zmodAvg P̃ Q u v θ = Q⁻¹ ∑_y u(θ-y) v(θ-P(y)) = A_Ẑ(u,v)(θ)`.

This is the convention of (i) the fibre factorisation `Work.KMTAreas.A7.Btwist_eq_fiberSum`
(whose two fibres are `fiberOpSet … n₀` and `fiberOpPSet P … n₀` with the *same* `n₀`) and (ii) the
arithmetic bilinear theorem `Work.KMTPlan.A6.MdlBileOfR1Improv`, which is stated for
`polyBilinearAverageZMod Polynomial.X P Q` — i.e. `Q⁻¹ ∑_y f(x-y) g(x-P(y))`, again with minus
signs.  Hence the adelic-form clauses below are stated for `zmodAvg (negReflect P)`, and so is the
`B` argument of the assembly in `MdlSliceCoreGainMemLp2.lean`; with the plus-sign `zmodAvg P Q` the
clauses are *not* satisfiable (the required packet values would have to be the samples of a
band-limited function but carry the modulation `e(-2α·)`, which is outside the band `1/(8Q)`). -/
def negReflect (P : ℤ[X]) : ℤ[X] := -(P.comp (-Polynomial.X))

/-- Evaluation of the reflected polynomial: `(P̃ y) = -P(-y)`. -/
lemma negReflect_eval (P : ℤ[X]) (y : ℤ) : (negReflect P).eval y = -(P.eval (-y)) := by
  simp [negReflect]

/-- **The adelic form of the good part of the frozen slice, with nonnegative constants.**  Same
statement as `Work.KMTPlan.A6.AdelicFormProp`, except that the constants `Ku`, `Kv` of the two
`L²(ℝ; V^R(ℓ²(ZMod Q)))`-data bounds are required to be nonnegative (which is what the
`ZMod Q` variational chain `Work.KMTPlan.A6.ZModChainProp` consumes). -/
def AdelicFormPropPlus (P : ℤ[X]) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ Cin : NNReal → NNReal,
      ∀ (r : NNReal) (hr : 2 < r) (R : ℝ) (hR : 2 ≤ R) (hRr : R < (r : ℝ))
        (C₀ : ℕ) (a : ℕ → NNReal) (Λ : NNReal)
        (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (j₁ j₂ : ℤ)
        (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
        (f g : ℤ → ℂ),
        1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₁ = 0 → j₁ ≠ -1) → (k₂ = 0 → j₂ ≠ -1) →
        MemLp f 2 Measure.count → MemLp g 2 Measure.count →
        ∃ (F : ℕ → ℝ → ℤ → ℂ)
          (u v : ℕ → ℝ → ZMod (arithQ ρ (max l₁ l₂)) → ℂ) (M Ku Kv : ℝ),
          (∀ (n : ℕ) (ρ' : ℤ), Work.KMTAreas.A7Rep.HasRealFreqSupport (fun X : ℝ => F n X ρ')
              (Set.Icc (-(1 / (8 * (arithQ ρ (max l₁ l₂) : ℝ))))
                (1 / (8 * (arithQ ρ (max l₁ l₂) : ℝ))))) ∧
          (∀ (n : ℕ) (x : ℤ), F n (x : ℝ) (x % ((arithQ ρ (max l₁ l₂) : ℕ) : ℤ))
              = (if goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
                  mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x else 0)) ∧
          (∀ (n : ℕ) (X : ℝ) (ρ' : ℤ), F n X ρ'
              = zmodAvg (negReflect P) (arithQ ρ (max l₁ l₂)) (u n X) (v n X)
                  ((ρ' : ℤ) : ZMod (arithQ ρ (max l₁ l₂)))) ∧
          (0 ≤ M ∧ ENNReal.ofReal M
              ≤ (Cin Λ : ENNReal)
                * ENNReal.ofReal ((2 : ℝ) ^ (-(c * max (l₁ : ℝ) (l₂ : ℝ))))) ∧
          (0 ≤ Ku ∧ ENNReal.ofReal Ku ≤ (Cin Λ : ENNReal)
              * ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂) * eLpNorm f 2 Measure.count) ∧
          (0 ≤ Kv ∧ ENNReal.ofReal Kv ≤ (Cin Λ : ENNReal)
              * ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂) * eLpNorm g 2 Measure.count) ∧
          (∫⁻ X : ℝ, (VrLiftData R (arithQ ρ (max l₁ l₂)) (fun n : ℕ => u n X)) ^ (2 : ℕ)
              ≤ ENNReal.ofReal (Ku ^ 2)) ∧
          (∫⁻ X : ℝ, (VrLiftData R (arithQ ρ (max l₁ l₂)) (fun n : ℕ => v n X)) ^ (2 : ℕ)
              ≤ ENNReal.ofReal (Kv ^ 2)) ∧
          (∀ (n : ℕ) (θ : ZMod (arithQ ρ (max l₁ l₂))),
              AEMeasurable (fun X : ℝ => u n X θ)) ∧
          (∀ (n : ℕ) (θ : ZMod (arithQ ρ (max l₁ l₂))),
              AEMeasurable (fun X : ℝ => v n X θ)) ∧
          (∀ (X : ℝ) (n : ℕ),
            eLpNorm (fun ρ' : ZMod (arithQ ρ (max l₁ l₂)) =>
                zmodAvg (negReflect P) (arithQ ρ (max l₁ l₂)) (u n X) (v n X) ρ') (r : ENNReal)
                (Measure.count : Measure (ZMod (arithQ ρ (max l₁ l₂))))
              ≤ ENNReal.ofReal M
                * eLpNorm (u n X) 2 (Measure.count : Measure (ZMod (arithQ ρ (max l₁ l₂))))
                * eLpNorm (v n X) 2 (Measure.count : Measure (ZMod (arithQ ρ (max l₁ l₂))))) ∧
          (∀ (X : ℝ) (m n l : ℕ),
            eLpNorm (fun ρ' : ZMod (arithQ ρ (max l₁ l₂)) =>
                zmodAvg (negReflect P) (arithQ ρ (max l₁ l₂)) (u m X - u n X) (v l X) ρ') (r : ENNReal)
                (Measure.count : Measure (ZMod (arithQ ρ (max l₁ l₂))))
              ≤ ENNReal.ofReal M
                * eLpNorm (u m X - u n X) 2 (Measure.count : Measure (ZMod (arithQ ρ (max l₁ l₂))))
                * eLpNorm (v l X) 2 (Measure.count : Measure (ZMod (arithQ ρ (max l₁ l₂))))) ∧
          (∀ (X : ℝ) (m n l : ℕ),
            eLpNorm (fun ρ' : ZMod (arithQ ρ (max l₁ l₂)) =>
                zmodAvg (negReflect P) (arithQ ρ (max l₁ l₂)) (u l X) (v m X - v n X) ρ') (r : ENNReal)
                (Measure.count : Measure (ZMod (arithQ ρ (max l₁ l₂))))
              ≤ ENNReal.ofReal M
                * eLpNorm (u l X) 2 (Measure.count : Measure (ZMod (arithQ ρ (max l₁ l₂))))
                * eLpNorm (v m X - v n X) 2
                    (Measure.count : Measure (ZMod (arithQ ρ (max l₁ l₂)))))

end

end Work.KMTPlan.A6
