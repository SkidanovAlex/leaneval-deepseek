/-
# The adelic form of the good scales, on the paper's exponent range `2 < r < 2d/(d-1)`

This module holds the statement of the adelic-form input of the frozen-slice estimate
`Work.KMTPlan.A6.MdlSliceCoreGainMemLp` (paper `model-est-2`, `all-all-large-2` at `(2,2,1)`,
Krause--Mirek--Tao, Annals **195** (2022), §8) in the form in which the final assembly *needs and
can use* it.

It is `Work.KMTPlan.A6.AdelicFormPropPlus` (`MdlAdelicFormPlusDefs.lean`) with **one extra
hypothesis on the variation exponent**, namely the paper's range

  `2 < r < 2d/(d-1)`,  `d = P.natDegree`,

and this extra hypothesis is *necessary*, not cosmetic.  The clauses `hbase`/`hB1`/`hB2` of the
adecilic form bound `‖zmodAvg P Q (u n X) (v n X)‖_{L^r}` — the operator norm of the arithmetic
averaging operator at the exponent `r` — and the only available estimate of that operator norm is
the paper's Theorem `bile` (`Succ_avg`, formalised in the tree by `MdlBileR1OfImprov` and
`MdlBileOfR1`), which holds exactly in the range `2 ≤ r < 2d/(d-1)`.  The paper says so
explicitly (§8, right after `bilinear-fkr`):

  *"To prove (all-all-large-2) for `r > 2`, we use the slice formulation (form-2).  It suffices by
  monotonicity of `V^r` norms to work in the range `2 < r < 2d/(d-1)`."*

**The second correction is the normalization.**  The two `L²`-data clauses (`hSu`, `hSv`) are
stated with `Work.KMTPlan.A6.VrLiftDataP`, i.e. against the *probability* Haar measure
`zmodProb Q` on `ZMod Q` (`Q⁻¹ • count`), not the counting measure: these are the objects the
paper's linear estimates `(lin-1)`/`(lin-2)` control, and they are exactly what the (probability
normalized) chain `Work.KMTPlan.A6.ZModChainPropP` consumes.  The counting-measure datum is
`Q^{1/2}` times this one, which would break the `Q`-uniformity of the constants.  See
`MdlAdelicProb.lean`.

The corresponding monotonicity is `Work.Analysis.Variation.varPart_antitone`
(`varPart s a ≤ varPart p a` for `1 ≤ p ≤ s`), which the consumer
`Work.KMTPlan.A6.MdlSliceCoreGainMemLp_of_le` (in
`Submission/Work/KMTPlan/A6/MdlSliceCoreGainAll.lean`) uses to pass from an in-range exponent to
any larger one.  So the present statement is the one that has to be proved, and it is enough.

**The fourth correction is the quantifier order of the constants.**  The original
`AdelicFormPropPlus` put `∃ c, A, ρ₀, Cin` *outside* `∀ r, R, C₀, j₁, j₂`, i.e. it asked for a
single gain rate `c` and a single arithmetic constant `Cin` valid for every exponent `r`.  That is
unprovable: the tree's arithmetic inputs produce a rate `c(r) > 0` separately for each
`r < 2d/(d-1)` (`Work.KMTPlan.A6.MdlBileOfR1Improv`'s docstring says so explicitly, and
`Work.KMTPlan.A6.MdlBileOfR1` quantifies `∃ c` after `r`), and `c(r)` degenerates as
`r → 2d/(d-1)` — so there is no uniform-in-`r` rate.  (This is the *proved* finding of
`NOTES_A6_adelicQuantifierOrder_SESSION.md` §1, where the same repair is applied to the sibling
interface `A6Clean.AdelicFormPropRangeP`.)  The constants are therefore quantified *inside*
`(r, R, C₀, j₁, j₂)` below, and only `Cin` is still quantified before the *datum*
`(a, Λ, l₁, l₂, k₁, k₂, t, f, g)` — which is what the §8 assembly needs, since its final constant
`K(Λ)` is built from `Cin Λ`.

**The third correction is the sign convention of the averaging operator.**  The workspace's
`Work.KMTPlan.A6.zmodAvg` carries **plus** signs (`u (θ+y) v (θ+P(y))`), while the paper's
averaging operator `A_Ẑ` — and the tree's arithmetic bilinear theorem, which is stated for
`Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P` — carries **minus** signs
(`f (x-P₁(y)) g (x-P₂(y))`).  The two differ by `y ↦ -y`, i.e. the second argument must be
evaluated at `-P(y)`, which is what the reflected polynomial
`Work.KMTPlan.A6.negReflect P = -(P.comp (-X))` does: `negReflect P` evaluated at `y` is
`-P(-y)`.  Thus all presentation and packet clauses below are stated for
`zmodAvg (negReflect P)`.  With the unreflected `zmodAvg P` the presentation clause is *false*
(the packets forced by the diagonal identity would not be band limited); see
`HANDOFF_A6_MdlSliceCoreGainMemLp2_SESSION2.md` §1 for the verification.

The proof of `AdelicFormPropRange` is the paper's §8 content, and it splits into three
independent obligations (see `NOTES_A6_MdlSliceCoreGainAll_SESSION2.md` §3):

* **(A) the structural part**: on the good scales the slice is the diagonal of a lift `F` with
  band `≤ 1/(8Q)` which is `zmodAvg P Q (u n X) (v n X)` — the fibre identity
  `Work.KMTAreas.A7.Btwist_eq_fiberSum`, the lift `Work.KMTPlan.A6.exists_adelicLift` and
  `Work.KMTPlan.A6.modQ_decomposition_of_fourierInv` supply the ingredients; the de-modulated
  amplitudes are the objects `Work.KMTAreas.A7.varphiNt`/`Tex` are built from.

* **(B) the arithmetic packet estimates** `hbase`/`hB1`/`hB2` at exponent `r ∈ (2, 2d/(d-1))` with
  `M ≲ 2^{-c·max(l₁,l₂)}`.  These are the paper's Theorem `bile`: `Work.KMTPlan.A6.MdlBileOfR1`
  (with its unconditional input `Work.KMTPlan.A6.MdlBilAvgImprov`, proved from the contract's Area
  A4) interpolated with the `L¹` gain `Work.KMTPlan.A6.MdlBileR1OfImprov`, applied to the packets
  — which are `Work.KMTPlan.A6.MdlIwMinorArc` at height `l` because of the narrowness of
  `Work.KMTAreas.A7.varphiNt` (and of the model's windows).  Note the sign convention: `zmodAvg`
  sums `u (θ+y) v (θ+P(y))` while `Work.Analysis.Concentration.polyBilinearAverageZMod X P Q`
  sums `f (x-y) g (x-P(y))` (the substitution `y ↦ -y`, i.e. `P` is replaced by `P(-X)`, which
  preserves the estimates); and `LpNormZMod` is the *normalized* (`Q⁻¹∑`) norm.

* **(C) the linear data bounds** `∫ (VrLiftDataP R Q (u · X))² ≤ Ku²` with
  `Ku ≤ Cin Λ · lossWeight A ρ l₁ l₂ k₁ k₂ · ‖f‖₂` (and the same for `v`, `g`, `Kv`).  These are
  the paper's `(lin-1)`/`(lin-2)`: the `L²(Ẑ)`-valued lacunary variational estimates for the two
  packet families, in the **normalized** form — the discrete forms are
  `Work.KMTAreas.A7.RepFiberVarSampling`, `Work.KMTAreas.A7.RepFiberVarSamplingG` and (in the
  A6 model carrier) `Work.KMTPlan.A6.MdlSlicePktLinF`, `Work.KMTPlan.A6.MdlSlicePktLinG`.

The proofs of `AdelicFormPropRange` may therefore assume the tree's deep linear estimates as
named inputs; what must **not** happen is the counting-measure normalization of §2.2 of the notes
(it is unprovable). the construction of the adelic lift
of the good scales (`exists_adelicLift`), its presentation as `zmodAvg P Q (u ·) (v ·)` (paper
`form-1`/`form-2`, `Btwist_eq_fiberSum`), the arithmetic bilinear estimate for the two packet
families at height `≤ l` (`MdlBileOfR1`, whose input `(Avg-prof)` is
`Work.KMTPlan.A6.MdlBilAvgImprov` — proved from the contract's Area A4; note that the packets are
`MdlIwMinorArc`), and the `L²(ℝ; V^R(ℓ²(ZMod Q)))`-data bound for the two packet families (the
adelic form of `(lin-1)`/`(lin-2)`, i.e. the fibre-sampling form of the linear lacunary
variational estimates).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlAdelicFormPlusDefs
import Submission.Work.KMTPlan.A6.MdlAdelicProb

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

/-- **The upper end of the paper's exponent range `2d/(d-1)`, for `d = P.natDegree`.** -/
noncomputable def adelicRTop (P : ℤ[X]) : ℝ :=
  2 * (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1)

/-- `adelicRTop P > 2` for `2 ≤ P.natDegree`. -/
lemma two_lt_adelicRTop {P : ℤ[X]} (hd : 2 ≤ P.natDegree) : 2 < adelicRTop P := by
  have hdR : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
  have hpos : (0 : ℝ) < (P.natDegree : ℝ) - 1 := by linarith
  rw [adelicRTop, lt_div_iff₀ hpos]
  nlinarith

/-- **The adelic form of the good part of the frozen slice, on the paper's exponent range.**

Same statement as `Work.KMTPlan.A6.AdelicFormPropPlus`, except that the variation exponent `r` is
restricted to the range `2 < r < 2d/(d-1)` in which the arithmetic bilinear estimate (the paper's
Theorem `bile`) is available.  By the monotonicity of the `V^r` norms
(`Work.Analysis.Variation.varPart_antitone`) this restricted form entails the unrestricted one, so
it is exactly what the §8 assembly consumes.

(`Work.Analysis.Variation.varPart_antitone`) this restricted form entails the unrestricted one, so
it is exactly what the §8 assembly consumes. -/
def AdelicFormPropRange (P : ℤ[X]) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P) : Prop :=
  ∀ (r : NNReal) (hr : 2 < r) (hrT : (r : ℝ) < adelicRTop P)
    (R : ℝ) (hR : 2 ≤ R) (hRr : R < (r : ℝ))
    (C₀ : ℕ) (j₁ j₂ : ℤ)
    (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)),
    ∃ c : ℝ, 0 < c ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ Cin : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal)
        (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f g : ℤ → ℂ),
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
          (∫⁻ X : ℝ, (VrLiftDataP R (arithQ ρ (max l₁ l₂)) (fun n : ℕ => u n X)) ^ (2 : ℕ)
              ≤ ENNReal.ofReal (Ku ^ 2)) ∧
          (∫⁻ X : ℝ, (VrLiftDataP R (arithQ ρ (max l₁ l₂)) (fun n : ℕ => v n X)) ^ (2 : ℕ)
              ≤ ENNReal.ofReal (Kv ^ 2)) ∧
          (∀ (n : ℕ) (θ : ZMod (arithQ ρ (max l₁ l₂))),
              AEMeasurable (fun X : ℝ => u n X θ)) ∧
          (∀ (n : ℕ) (θ : ZMod (arithQ ρ (max l₁ l₂))),
              AEMeasurable (fun X : ℝ => v n X θ)) ∧
          (∀ (X : ℝ) (n : ℕ),
            eLpNorm (fun ρ' : ZMod (arithQ ρ (max l₁ l₂)) =>
                zmodAvg (negReflect P) (arithQ ρ (max l₁ l₂)) (u n X) (v n X) ρ') (r : ENNReal)
                (zmodProb (arithQ ρ (max l₁ l₂)))
              ≤ ENNReal.ofReal M
                * eLpNorm (u n X) 2 (zmodProb (arithQ ρ (max l₁ l₂)))
                * eLpNorm (v n X) 2 (zmodProb (arithQ ρ (max l₁ l₂)))) ∧
          (∀ (X : ℝ) (m n l : ℕ),
            eLpNorm (fun ρ' : ZMod (arithQ ρ (max l₁ l₂)) =>
                zmodAvg (negReflect P) (arithQ ρ (max l₁ l₂)) (u m X - u n X) (v l X) ρ') (r : ENNReal)
                (zmodProb (arithQ ρ (max l₁ l₂)))
              ≤ ENNReal.ofReal M
                * eLpNorm (u m X - u n X) 2 (zmodProb (arithQ ρ (max l₁ l₂)))
                * eLpNorm (v l X) 2 (zmodProb (arithQ ρ (max l₁ l₂)))) ∧
          (∀ (X : ℝ) (m n l : ℕ),
            eLpNorm (fun ρ' : ZMod (arithQ ρ (max l₁ l₂)) =>
                zmodAvg (negReflect P) (arithQ ρ (max l₁ l₂)) (u l X) (v m X - v n X) ρ') (r : ENNReal)
                (zmodProb (arithQ ρ (max l₁ l₂)))
              ≤ ENNReal.ofReal M
                * eLpNorm (u l X) 2 (zmodProb (arithQ ρ (max l₁ l₂)))
                * eLpNorm (v m X - v n X) 2
                    (zmodProb (arithQ ρ (max l₁ l₂))))

end

end Work.KMTPlan.A6
