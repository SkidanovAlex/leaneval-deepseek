import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.Q1FibBound
import Submission.Work.BoseFixB1S.a0A2QJointNormScalar
import Submission.Work.BoseFixB1S.boxCrossHoppingSharpLowAux
import Submission.Work.BoseFixB1S.boxFibLine
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.a0A2QJointEdgeAtomFix` — the per-edge sharp hop atom, **with the
parentheses** (the correct form of the requested statement)

`Submission/Work/BoseFixB1S/a0A2QJointEdgeAtom.lean` was handed to the fleet with the statement

    δ·∫ ψ_c·fib(xᵢ)·ψ_p  ≥  −(4X)·∫ (ψ_c)²·fib(xᵢ)  −  (δ²/(16X))·∫ (ψ_p)²·fib(xᵢ)

written **without parentheses around the two factors of the right-hand side's second line**.
Because the set-integral notation's body has precedence `60` while `-` is `infixl:65`, the written
text parses as

    δ·∫ ψ_c·fib(xᵢ)·ψ_p  ≥  −(4X)·∫ ( (ψ_c)²·fib(xᵢ) − (δ²/(16X))·∫ (ψ_p)²·fib(xᵢ) ) ,

i.e. the subtracted term is *swallowed into the body of the first integral* — a strictly stronger
(and false) claim; see the FINDING in `a0A2QJointEdgeAtom.lean` and
`FINDING_a0A2QJointEdgeAtom_FALSE.md` for the exact refutation (the extra term is
`4X·(δ²/(16X))·|abox|·∫(ψ_p)²fib`).

This module states and proves the **intended** atom, with each integral explicitly parenthesised
(and with the corpus's own name `w1Fibre` for the localised fibre, in all three occurrences).
It is sorry-free and safe to import.

* `atomA0A2QFib` — the scalar core: with the *nonnegative* weight `f`, the sharp atom
  `(−4X)x²f − (d²/(16X))y²f ≤ d·(x·f·y)`, `X = (√(t+1)+√m)²`, via the completion of squares

      4Xx² + dxy + (d²/(16X))y² = (1/(4X))·(4Xx + (d/2)y)² ;

* `a0A2QJointEdgeAtomFibre` — the per-edge atom itself: for `p ∈ hopPairSet i`,
  `fib = w1Fibre ℓ (wSmall1Pair h M ℓ d u) ≥ 0` (`boxFibLine_fibre_nonneg`), the pointwise atom
  with `ψ_{cᵢ(p)}`, `ψ_p` and the fibre `fib(xᵢ)`, integrated over the compact box `abox N ℓ`
  (the three integrands are bounded/measurable, hence integrable).

`FINDING_a0A2QJointNormB1Fix.md` §2 and `FINDING_hopAmgmB1.md` §4 identify this atom as the step
that makes the *sharp* FS weights `(√(t+1) ± √m)²` available on the (nonnegative) uncentred fibre.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseFixB1S

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The scalar sharp atom with a nonnegative weight.**  For `t, m ≥ 0`, `f ≥ 0` and *all* reals
`x, y`,

    (−4X)·x²f − (d²/(16X))·y²f ≤ d·(x·f·y) ,   d := t − 1 − m ,  X := (√(t+1)+√m)² .

It is the proved `atomA0A2Q` (`a0A2QJointNormScalar`) multiplied by the nonnegative weight `f/2`,
exhibited as a manifest square:

    d·(xfy) − [d·(xfy) − 4X·x²f − (d²/(16X))·y²f] = f·(1/(4X))·(4X·x + (d/2)·y)² ≥ 0 .

No sign hypothesis on `x, y` is needed; only the weight must be nonnegative. -/
theorem atomA0A2QFib {t m x y f : ℝ} (ht : 0 ≤ t) (hm : 0 ≤ m) (hf : 0 ≤ f) :
    (-(4 * (Real.sqrt (t + 1) + Real.sqrt m) ^ 2)) * (x ^ 2 * f)
      - ((t - 1 - m) ^ 2 / (16 * (Real.sqrt (t + 1) + Real.sqrt m) ^ 2)) * (y ^ 2 * f)
      ≤ (t - 1 - m) * (x * f * y) := by
  set X : ℝ := (Real.sqrt (t + 1) + Real.sqrt m) ^ 2 with hXdef
  have hX : 0 < X := by rw [hXdef]; exact sqrtSumSq_pos ht hm
  have hid : (-(4 * X)) * (x ^ 2 * f) - ((t - 1 - m) ^ 2 / (16 * X)) * (y ^ 2 * f)
      = (t - 1 - m) * (x * f * y)
        - f * ((1 / (4 * X)) * (4 * X * x + ((t - 1 - m) / 2) * y) ^ 2) := by
    field_simp
    ring
  rw [hid]
  have hnn : 0 ≤ f * ((1 / (4 * X)) * (4 * X * x + ((t - 1 - m) / 2) * y) ^ 2) :=
    mul_nonneg hf (mul_nonneg (div_nonneg zero_le_one (le_of_lt (mul_pos (by norm_num) hX)))
      (sq_nonneg _))
  linarith

/-- **The per-edge sharp hop atom** (the requested statement with the right-hand side explicitly
parenthesised; see the module header).  For an edge `p ∈ hopPairSet i`, `t = |p.1|`, `m = μV`,
`δ = t − 1 − m`, `X = (√(t+1)+√m)²` and the nonnegative uncentred fibre
`fib = w1Fibre ℓ (wSmall1Pair h M ℓ d u)`:

    δ·∫ ψ_{cᵢ(p)}·fib(xᵢ)·ψ_p  ≥  (−4X)·∫ (ψ_{cᵢ(p)})²·fib(xᵢ)  −  (δ²/(16X))·∫ (ψ_p)²·fib(xᵢ) .

Proof: `atomA0A2QFib` holds pointwise with the nonnegative weight `f = fib(xᵢ) ≥ 0`
(`boxFibLine_fibre_nonneg`); the three integrands are bounded (the two joint components are
`GoodState`s by `goodState_boxCompT`, the fibre is uniformly bounded by `q1Fib_aem_bound`), hence
integrable on the compact box; monotonicity of the integral (`integral_mono_ae`) together with
linearity gives the claim. -/
theorem a0A2QJointEdgeAtomFibre {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) :
    ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
      (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
      (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
      (hμv : 1 ≤ μ * Work.SmallBoxSliding.boxMass ℓ d u)
      {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
      (i : Fin N) (p : Finset (Fin N) × Finset (Fin N))
      (hp : p ∈ Work.BoseFixB1S.hopPairSet i),
      (((p.1.card : ℝ) - 1 - μ * Work.SmallBoxSliding.boxMass ℓ d u)
          * (∫ x in Submission.BoseGases.abox N ℓ,
              Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) (p.1.erase i) (insert i p.2) Φ x
                * Submission.BoseGases.w1Fibre ℓ
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)
                * Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) p.1 p.2 Φ x))
        ≥ (-(4 * (Real.sqrt ((p.1.card : ℝ) + 1)
              + Real.sqrt (μ * Work.SmallBoxSliding.boxMass ℓ d u)) ^ 2))
            * (∫ x in Submission.BoseGases.abox N ℓ,
                (Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) (p.1.erase i) (insert i p.2) Φ x) ^ 2
                  * Submission.BoseGases.w1Fibre ℓ
                      (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
          - ((((p.1.card : ℝ) - 1 - μ * Work.SmallBoxSliding.boxMass ℓ d u) ^ 2
                / (16 * (Real.sqrt ((p.1.card : ℝ) + 1)
                    + Real.sqrt (μ * Work.SmallBoxSliding.boxMass ℓ d u)) ^ 2))
              * (∫ x in Submission.BoseGases.abox N ℓ,
                  (Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
                      (Submission.BoseGases.dlBox ℓ d u) p.1 p.2 Φ x) ^ 2
                    * Submission.BoseGases.w1Fibre ℓ
                        (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))) := by
  intro ℓ d μ hℓ hd hR hRχ u hvol hμv N Φ hΦc i p hp
  -- ## abbreviations
  let ψc : Submission.BoseGases.X N → ℝ :=
    Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
      (Submission.BoseGases.dlBox ℓ d u) (p.1.erase i) (insert i p.2) Φ
  let ψp : Submission.BoseGases.X N → ℝ :=
    Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
      (Submission.BoseGases.dlBox ℓ d u) p.1 p.2 Φ
  let fib : EuclideanSpace ℝ (Fin 3) → ℝ :=
    Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u)
  let t : ℝ := (p.1.card : ℝ)
  let m : ℝ := μ * Work.SmallBoxSliding.boxMass ℓ d u
  let Xw : ℝ := (Real.sqrt (t + 1) + Real.sqrt m) ^ 2
  change (t - 1 - m) * (∫ x in Submission.BoseGases.abox N ℓ, ψc x * fib (x i) * ψp x)
      ≥ (-(4 * Xw)) * (∫ x in Submission.BoseGases.abox N ℓ, ψc x ^ 2 * fib (x i))
        - ((t - 1 - m) ^ 2 / (16 * Xw))
            * (∫ x in Submission.BoseGases.abox N ℓ, ψp x ^ 2 * fib (x i))
  -- ## basic facts
  have ht : 0 ≤ t := by
    change (0 : ℝ) ≤ (p.1.card : ℝ)
    exact_mod_cast Nat.zero_le p.1.card
  have hm : 0 ≤ m := by
    change (0 : ℝ) ≤ μ * Work.SmallBoxSliding.boxMass ℓ d u
    linarith
  have hXpos : 0 < Xw := by
    change 0 < (Real.sqrt (t + 1) + Real.sqrt m) ^ 2
    exact sqrtSumSq_pos ht hm
  have hfibnn : ∀ z : EuclideanSpace ℝ (Fin 3), 0 ≤ fib z := by
    intro z
    change 0 ≤ Submission.BoseGases.w1Fibre ℓ
      (Submission.BoseGases.wSmall1Pair h M ℓ d u) z
    exact boxFibLine_fibre_nonneg hR0 hv hvrad hv_supp h u z
  -- ## the fibre is a.e. strongly measurable and uniformly bounded
  obtain ⟨-, ⟨hFibAesm', Cf, hCf0, hCfb'⟩⟩ :=
    Work.BoseFixB1.q1Fib_aem_bound (v := v) (R0 := R0) hv_supp hR0 hv hvrad h (M := M) hM
      hℓ hd hR hRχ u
  have hFibAesm : MeasureTheory.AEStronglyMeasurable fib
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)) := hFibAesm'
  have hCfb : ∀ z : EuclideanSpace ℝ (Fin 3), |fib z| ≤ Cf := hCfb'
  -- ## box data and the two joint components as `GoodState`s
  have hAmeas : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hVeq : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ d u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  have hΦg : Work.BoseFixB1S.GoodState ℓ Φ := Work.BoseFixB1S.goodState_of_continuous hℓ hΦc
  obtain ⟨hψcm, Cc, hψcb⟩ := Work.BoseFixB1S.goodState_boxCompT hℓ hvol hAmeas hVeq hAc
    (p.1.erase i) (insert i p.2) hΦg
  obtain ⟨hψpm, Cp, hψpb⟩ := Work.BoseFixB1S.goodState_boxCompT hℓ hvol hAmeas hVeq hAc
    p.1 p.2 hΦg
  have hfibm : MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N => fib (x i))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) :=
    Submission.BoseGases.aem_comp_coord' i hFibAesm
  -- ## integrability of the three integrands on the compact box
  have hI1 : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N => ψc x * fib (x i) * ψp x)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) := by
    refine Work.BoseFixB1S.integrableOn_abox_of_bound_aesm
      (C := max Cc 0 * max Cf 0 * max Cp 0) hℓ ?_ ?_
    · exact (hψcm.aestronglyMeasurable.mul hfibm).mul hψpm.aestronglyMeasurable
    · intro x hx
      have h1 : |ψc x| ≤ max Cc 0 := le_trans (hψcb x hx) (le_max_left _ _)
      have h2 : |fib (x i)| ≤ max Cf 0 := le_trans (hCfb (x i)) (le_max_left _ _)
      have h3 : |ψp x| ≤ max Cp 0 := le_trans (hψpb x hx) (le_max_left _ _)
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (le_max_right _ _)) h3 (abs_nonneg _)
        (mul_nonneg (le_max_right _ _) (le_max_right _ _))
  have hI2 : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N => ψc x ^ 2 * fib (x i))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) := by
    refine Work.BoseFixB1S.integrableOn_abox_of_bound_aesm
      (C := (max Cc 0) ^ 2 * max Cf 0) hℓ ?_ ?_
    · exact (hψcm.aestronglyMeasurable.pow 2).mul hfibm
    · intro x hx
      have h1 : |ψc x| ≤ max Cc 0 := le_trans (hψcb x hx) (le_max_left _ _)
      have h2 : |fib (x i)| ≤ max Cf 0 := le_trans (hCfb (x i)) (le_max_left _ _)
      have h1' : (0 : ℝ) ≤ max Cc 0 := le_max_right _ _
      have hsq : ψc x ^ 2 ≤ (max Cc 0) ^ 2 := by
        have hb := abs_le.mp h1
        nlinarith [hb.1, hb.2, h1']
      rw [abs_mul, abs_of_nonneg (sq_nonneg (ψc x))]
      exact mul_le_mul hsq h2 (abs_nonneg _) (sq_nonneg _)
  have hI3 : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N => ψp x ^ 2 * fib (x i))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) := by
    refine Work.BoseFixB1S.integrableOn_abox_of_bound_aesm
      (C := (max Cp 0) ^ 2 * max Cf 0) hℓ ?_ ?_
    · exact (hψpm.aestronglyMeasurable.pow 2).mul hfibm
    · intro x hx
      have h1 : |ψp x| ≤ max Cp 0 := le_trans (hψpb x hx) (le_max_left _ _)
      have h2 : |fib (x i)| ≤ max Cf 0 := le_trans (hCfb (x i)) (le_max_left _ _)
      have h1' : (0 : ℝ) ≤ max Cp 0 := le_max_right _ _
      have hsq : ψp x ^ 2 ≤ (max Cp 0) ^ 2 := by
        have hb := abs_le.mp h1
        nlinarith [hb.1, hb.2, h1']
      rw [abs_mul, abs_of_nonneg (sq_nonneg (ψp x))]
      exact mul_le_mul hsq h2 (abs_nonneg _) (sq_nonneg _)
  -- ## the pointwise atom and the monotonicity of the integral
  have hpt : ∀ x : Submission.BoseGases.X N,
      -(4 * Xw) * (ψc x ^ 2 * fib (x i))
          - ((t - 1 - m) ^ 2 / (16 * Xw)) * (ψp x ^ 2 * fib (x i))
        ≤ (t - 1 - m) * (ψc x * fib (x i) * ψp x) := by
    intro x
    exact atomA0A2QFib (t := t) (m := m) (x := ψc x) (y := ψp x) (f := fib (x i))
      ht hm (hfibnn (x i))
  have hIg2 : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N => -(4 * Xw) * (ψc x ^ 2 * fib (x i)))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) := hI2.const_mul (-(4 * Xw))
  have hIg3 : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N =>
        ((t - 1 - m) ^ 2 / (16 * Xw)) * (ψp x ^ 2 * fib (x i)))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) := hI3.const_mul ((t - 1 - m) ^ 2 / (16 * Xw))
  have hIg : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N => -(4 * Xw) * (ψc x ^ 2 * fib (x i))
          - ((t - 1 - m) ^ 2 / (16 * Xw)) * (ψp x ^ 2 * fib (x i)))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) := hIg2.sub hIg3
  have hIh : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N => (t - 1 - m) * (ψc x * fib (x i) * ψp x))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) := hI1.const_mul (t - 1 - m)
  have hmono :
      (t - 1 - m) * (∫ x in Submission.BoseGases.abox N ℓ, ψc x * fib (x i) * ψp x)
        ≥ (-(4 * Xw)) * (∫ x in Submission.BoseGases.abox N ℓ, ψc x ^ 2 * fib (x i))
          - ((t - 1 - m) ^ 2 / (16 * Xw))
              * (∫ x in Submission.BoseGases.abox N ℓ, ψp x ^ 2 * fib (x i)) := by
    have h := MeasureTheory.integral_mono_ae hIg hIh (Filter.Eventually.of_forall hpt)
    rw [MeasureTheory.integral_sub hIg2 hIg3, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at h
    exact h
  exact hmono

end Work.BoseFixB1S
