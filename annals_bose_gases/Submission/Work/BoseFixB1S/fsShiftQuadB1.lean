import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.fsPSpectralB1
import Submission.Work.BoseFixB1S.fsPsideMassB1
import Submission.Work.BoseFixB1S.n0FunOp_affineB1_of_continuous
import Submission.Work.BoseFixB1S.n0FunOp_monoB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.fsShiftQuadB1` — the `√n₀`-shift quadratic forms of FS's
completion of squares

FS's completion of squares (`Papers/fournais_solovej/final_v2.tex` l. 3726–3743, the heart of
`lm:appinteractionestimate`) replaces the *unweighted* normal form
`(n₀ − μ|B|)·Θ` by the `√`-weighted one

    (n₀ − μ|B|)·Θ = (n₀^{1/2} + (μ|B|)^{1/2})·Θ·((n₀+1)^{1/2} − (μ|B|)^{1/2}) ,

which produces exactly two `n₀`-quadratic forms.  Both are bounded here, in the corpus's
`n₀`-functional-calculus vocabulary (`n0FunOp volA A g = g(n₀)`, `n0Op volA A = n₀`, and
`n0ProjOp volA A S` the subset idempotents):

* **`n0FunOp_shiftQuadLeB1`** — the *crude* half of the split, `(√(r+1)−√m)² ≤ r + (1+m)` in
  quadratic-form (expectation) sense:

      ∫ (g(n₀)Ψ)·Ψ ≤ ∫ (n₀Ψ)·Ψ + (1+m)·∫Ψ² ,      g(r) = (√(r+1) − √m)² .

  (This is the content of the on-disk stub `Work.BoseFixB1S.n0FunOpShiftQuadLeB1`; it is the
  `P`-side weight used by the FS-completion chain of `n0ShiftPsideBoundB1` /
  `qSideLossB1`.)

* **`n0FunOp_shiftSharpB1`** — the *sharp* (`n₀`-weighted) form, FS's own display l.3741–3743:
  `r·(√(r+1)−√m)² ≤ (r+1−m)²` in quadratic-form sense:

      ∫ (n0FunOp (fun r => r·(√(r+1)−√m)²) Ψ)·Ψ ≤ ∫ (n0FunOp (fun r => (r+1−m)²) Ψ)·Ψ .

  This is the *only* place where the `√`-weights kill the `n₀²`/`N`-slopes: the P-side loss
  `−¼|B|⁻¹((n₀+1)^{1/2}−(μ|B|)^{1/2})²ΣᵢPᵢχW₁*χPᵢ ≥ −¼((n₀+1)/|B| − μ)²∬w₁` of FS
  l.3741–3743 is *this* inequality.  The scalar core is
  `Work.BoseFixB1S.mul_sqrt_sq_le` (`fsPSpectralB1.lean`: `t(√(t+1)−√c)² ≤ (t+1−c)²`
  for `t, c ≥ 0`), applied termwise on the spectrum `{0,…,N}`.

* **`n0FunOp_shiftSharpScalarB1`** — the sharp bound *explicitly summed over the subset
  idempotents*, `∫ (n₀·g(n₀)Ψ)·Ψ ≤ Σ_S (|S|+1−m)²·∫(P_SΨ)²`, the form in which the corpus's
  spectral moments (`n0SpectralMomentsB1`, `boxFlatCount`, `boxPairCount`) consume it.

All three are proved from the `n₀`-calculus interface alone: `n0FunOp_monoB1` turns a *termwise
scalar* inequality on `{0,…,N}` into the quadratic-form inequality, because the diagonal
`∫(P_SΨ)²` is a square, hence non-negative.

**Sharpness note (do not replace the sharp form by the crude one).**  For `r ≈ m ≫ 1` the two
weights differ by the factor `(√(r+1)+√m)²`: the crude form gives coefficient `r + (1+m)` while
the sharp one gives `(r+1−m)²/r`.  Using only the crude form is exactly the loss recorded in
`Submission/Work/BoseFixB1S/FINDING_hopAmgmB1.md` §4.1 (the signed-fibre trap): a *sharp* proof
of `lm:appinteractionestimate` needs the `r`-weighted version.
-/

noncomputable section

set_option linter.unusedVariables false

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. Two elementary regularity facts about `n₀ = ΣᵢP_{B,i}`

(`n0Op` is a finite sum of bounded measurable slot means, so it is bounded and measurable on the
analysis box.) -/

theorem measurable_n0Op {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨm : Measurable Ψ) :
    Measurable (fun x : Submission.BoseGases.X N => n0Op volA A Ψ x) := by
  simp only [n0Op]
  exact Finset.measurable_sum _ (fun i _ => measurable_boxPInd volA A hA i hΨm)

theorem abs_n0Op_le {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} {C : ℝ}
    (hC : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ C) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ, |n0Op volA A Ψ x| ≤ (N : ℝ) * |C| := by
  intro x hx
  simp only [n0Op]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc (∑ i : Fin N, |Work.UBBInputs8.boxPInd volA A i Ψ x|)
      ≤ ∑ _i : Fin N, |C| :=
        Finset.sum_le_sum fun i _ =>
          le_trans (abs_boxPInd_le hℓ hvol hA hvolA hAc i hC x hx) (le_abs_self C)
    _ = (N : ℝ) * |C| := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## 1. The crude `√`-split weight -/

/-- **The scalar atom**: `(√(t+1) − √m)² ≤ t + (1+m)` for `t, m ≥ 0`. -/
theorem sqrtShift_sq_le (t m : ℝ) (ht : 0 ≤ t) (hm : 0 ≤ m) :
    (Real.sqrt (t + 1) - Real.sqrt m) ^ 2 ≤ t + 1 + m := by
  have ht1 : (0 : ℝ) ≤ t + 1 := by linarith
  have h1 : Real.sqrt (t + 1) ^ 2 = t + 1 := Real.sq_sqrt ht1
  have h2 : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm
  have h3 : 0 ≤ Real.sqrt (t + 1) * Real.sqrt m :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [h1, h2, h3]

/-- **`n₀`-quadratic form of the crude `√`-shift weight.**  For a state `Ψ` measurable and bounded
on the analysis box,

    ∫ (g(n₀)Ψ)·Ψ ≤ ∫ (n₀Ψ)·Ψ + (1+m)·∫Ψ² ,     g(r) = (√(r+1) − √m)² .

This is the content of the on-disk stub `Work.BoseFixB1S.n0FunOpShiftQuadLeB1`
(`Submission/Work/BoseFixB1S/n0FunOpShiftQuadLeB1.lean`). -/
theorem n0FunOp_shiftQuadLeB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {m : ℝ} (hm : 0 ≤ m)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨm : Measurable Ψ) {C : ℝ}
    (hΨb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ C) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (n0FunOp volA A (fun r => (Real.sqrt (r + 1) - Real.sqrt m) ^ 2) Ψ x) * Ψ x)
      ≤ (∫ x in Submission.BoseGases.abox N ℓ, (n0Op volA A Ψ x) * Ψ x)
        + (1 + m) * ∫ x in Submission.BoseGases.abox N ℓ, (Ψ x) ^ 2 := by
  classical
  have hΨG : GoodState ℓ Ψ := ⟨hΨm, C, hΨb⟩
  -- the affine model, at `c := -m`
  have haff := n0FunOp_affineB1_of_goodState (N := N) hℓ hvol hA hvolA hAc (-m) hΨG
  rw [show (fun r : ℝ => r + 1 - (-m)) = fun r : ℝ => r + 1 + m from by funext r; ring] at haff
  -- monotonicity of the functional calculus between the two weights
  have hmono := n0FunOp_monoB1 (N := N) hℓ hvol hA hvolA hAc
    (g := fun r => (Real.sqrt (r + 1) - Real.sqrt m) ^ 2) (h := fun r => r + 1 + m)
    (fun k _ => sqrtShift_sq_le (k : ℝ) m (Nat.cast_nonneg k) hm) hΨm hΨb
  -- integrability of the two pieces of the affine model
  have hn0m : Measurable (fun x : Submission.BoseGases.X N => n0Op volA A Ψ x) :=
    measurable_n0Op hℓ hvol hA hvolA hAc hΨm
  have hI1 : IntegrableOn (fun x : Submission.BoseGases.X N => n0Op volA A Ψ x * Ψ x)
      (Submission.BoseGases.abox N ℓ) volume :=
    integrableOn_mul_of_bound hℓ hn0m hΨm
      (abs_n0Op_le hℓ hvol hA hvolA hAc hΨb)
      (fun x hx => le_trans (hΨb x hx) (le_abs_self C))
  have hI2 : IntegrableOn (fun x : Submission.BoseGases.X N => ((1 + m) * Ψ x) * Ψ x)
      (Submission.BoseGases.abox N ℓ) volume := by
    have h0 : IntegrableOn (fun x : Submission.BoseGases.X N => Ψ x * Ψ x)
        (Submission.BoseGases.abox N ℓ) volume :=
      integrableOn_mul_of_bound hℓ hΨm hΨm
        (fun x hx => le_trans (hΨb x hx) (le_abs_self C))
        (fun x hx => le_trans (hΨb x hx) (le_abs_self C))
    refine (h0.const_mul (1 + m)).congr ?_
    filter_upwards with x
    ring
  -- the affine evaluation
  have hval : (∫ x in Submission.BoseGases.abox N ℓ,
        (n0FunOp volA A (fun r : ℝ => r + 1 + m) Ψ x) * Ψ x)
      = (∫ x in Submission.BoseGases.abox N ℓ, (n0Op volA A Ψ x) * Ψ x)
        + (1 + m) * ∫ x in Submission.BoseGases.abox N ℓ, (Ψ x) ^ 2 := by
    have hae : (fun x => n0FunOp volA A (fun r : ℝ => r + 1 + m) Ψ x)
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
        fun x => n0Op volA A Ψ x + (1 + m) * Ψ x := by
      simpa only [sub_neg_eq_add] using haff
    calc (∫ x in Submission.BoseGases.abox N ℓ,
            (n0FunOp volA A (fun r : ℝ => r + 1 + m) Ψ x) * Ψ x)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            (n0Op volA A Ψ x + (1 + m) * Ψ x) * Ψ x :=
          integral_congr_ae (hae.mono fun x hx => by simpa using congrArg (fun y => y * Ψ x) hx)
      _ = (∫ x in Submission.BoseGases.abox N ℓ, n0Op volA A Ψ x * Ψ x)
            + ∫ x in Submission.BoseGases.abox N ℓ, ((1 + m) * Ψ x) * Ψ x := by
          rw [← MeasureTheory.integral_add hI1 hI2]
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      _ = (∫ x in Submission.BoseGases.abox N ℓ, (n0Op volA A Ψ x) * Ψ x)
            + (1 + m) * ∫ x in Submission.BoseGases.abox N ℓ, (Ψ x) ^ 2 := by
          rw [show (fun x : Submission.BoseGases.X N => ((1 + m) * Ψ x) * Ψ x)
                = fun x => (1 + m) * (Ψ x * Ψ x) from by funext x; ring,
            MeasureTheory.integral_const_mul]
          congr 1
          congr 1
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  linarith [hmono, hval]

/-! ## 2. The sharp (`n₀`-weighted) `√`-split weight -/

/-- **The sharp (`n₀`-weighted) `√`-split weight** — FS `final_v2.tex` l.3741–3743.  For a state
`Ψ` measurable and bounded on the analysis box,

    ∫ (n₀·g(n₀)Ψ)·Ψ ≤ ∫ ((n₀+1−m)²Ψ)·Ψ ,     g(r) = (√(r+1) − √m)² .

The scalar core is `mul_sqrt_sq_le` applied termwise on the spectrum `{0,…,N}`. -/
theorem n0FunOp_shiftSharpB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {m : ℝ} (hm : 0 ≤ m)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨm : Measurable Ψ) {C : ℝ}
    (hΨb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ C) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (n0FunOp volA A (fun r => r * (Real.sqrt (r + 1) - Real.sqrt m) ^ 2) Ψ x) * Ψ x)
      ≤ ∫ x in Submission.BoseGases.abox N ℓ,
          (n0FunOp volA A (fun r => (r + 1 - m) ^ 2) Ψ x) * Ψ x :=
  n0FunOp_monoB1 hℓ hvol hA hvolA hAc
    (g := fun r => r * (Real.sqrt (r + 1) - Real.sqrt m) ^ 2)
    (h := fun r => (r + 1 - m) ^ 2)
    (fun k _ => mul_sqrt_sq_le (k : ℝ) m (Nat.cast_nonneg k) hm) hΨm hΨb

/-- **The sharp bound, summed over the subset idempotents** — the form in which the corpus's
spectral moments consume it: `∫ (n₀·g(n₀)Ψ)·Ψ ≤ Σ_S (|S|+1−m)²·∫(P_SΨ)²`.

(The right side is `⟨Φ, (n₀+1−m)²Φ⟩` read on the spectral decomposition
`Φ = Σ_S P_SΦ` of `n0FunOp_eq_sum_card`; its value is
`Var(n₀) + (⟨n₀⟩+1−m)²` on a normalised state.) -/
theorem n0FunOp_shiftSharpScalarB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {m : ℝ} (hm : 0 ≤ m)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨm : Measurable Ψ) {C : ℝ}
    (hΨb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ C) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (n0FunOp volA A (fun r => r * (Real.sqrt (r + 1) - Real.sqrt m) ^ 2) Ψ x) * Ψ x)
      ≤ ∑ S : Finset (Fin N),
          ((S.card : ℝ) + 1 - m) ^ 2
            * ∫ x in Submission.BoseGases.abox N ℓ,
                (n0ProjOp volA A S Ψ x) * (n0ProjOp volA A S Ψ x) := by
  classical
  have hΨG : GoodState ℓ Ψ := ⟨hΨm, C, hΨb⟩
  have hΨn : BoxNice ℓ Ψ := ⟨hΨm, C, hΨb⟩
  have hG : ∀ S : Finset (Fin N), BoxNice ℓ (n0ProjOp volA A S Ψ) := fun S => by
    have h := BoxNice.iter hℓ hvol hA hvolA hAc (fun i => decide (i ∈ S)) hΨn
      (List.ofFn (fun i : Fin N => i))
    simpa only [n0ProjOp] using h
  -- the diagonal pairing equals the square (`n0ProjOp` is an idempotent projection)
  have hdiag : ∀ S : Finset (Fin N),
      (∫ x in Submission.BoseGases.abox N ℓ, n0ProjOp volA A S Ψ x * Ψ x)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            n0ProjOp volA A S Ψ x * n0ProjOp volA A S Ψ x := by
    intro S
    have hsum := n0PairingSumNice hℓ hvol hA hvolA hAc hΨm hΨb S
    have hsingle : (∑ T : Finset (Fin N), ∫ x in Submission.BoseGases.abox N ℓ,
          n0ProjOp volA A T Ψ x * n0ProjOp volA A S Ψ x)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            n0ProjOp volA A S Ψ x * n0ProjOp volA A S Ψ x :=
      Finset.sum_eq_single S
        (fun T _ hTS => n0PairingZeroNice hℓ hvol hA hvolA hAc hΨm hΨb hTS)
        (fun hS => absurd (Finset.mem_univ S) hS)
    have hflip : (∫ x in Submission.BoseGases.abox N ℓ, n0ProjOp volA A S Ψ x * Ψ x)
        = ∫ x in Submission.BoseGases.abox N ℓ, Ψ x * n0ProjOp volA A S Ψ x :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
    rw [hflip, hsum, hsingle]
  -- the quadratic form of `r·g(r)` as a sum of non-negative diagonal terms
  have hquad : (∫ x in Submission.BoseGases.abox N ℓ,
        (n0FunOp volA A (fun r => r * (Real.sqrt (r + 1) - Real.sqrt m) ^ 2) Ψ x) * Ψ x)
      = ∑ S : Finset (Fin N),
          ((S.card : ℝ) * (Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt m) ^ 2)
            * ∫ x in Submission.BoseGases.abox N ℓ,
                n0ProjOp volA A S Ψ x * n0ProjOp volA A S Ψ x := by
    have hpt : (fun x : Submission.BoseGases.X N =>
          n0FunOp volA A (fun r => r * (Real.sqrt (r + 1) - Real.sqrt m) ^ 2) Ψ x * Ψ x)
        = fun x => ∑ S : Finset (Fin N),
            ((S.card : ℝ) * (Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt m) ^ 2)
              * (n0ProjOp volA A S Ψ x * Ψ x) := by
      funext x
      have hx := congrFun (n0FunOp_eq_sum_card volA A
        (fun r => r * (Real.sqrt (r + 1) - Real.sqrt m) ^ 2) Ψ) x
      simp only [hx, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun S _ => by ring)
    have hint : ∀ S ∈ (Finset.univ : Finset (Finset (Fin N))), IntegrableOn
        (fun x : Submission.BoseGases.X N => n0ProjOp volA A S Ψ x * Ψ x)
        (Submission.BoseGases.abox N ℓ) volume := fun S _ =>
      integrableOn_mul_of_bound hℓ (hG S).1 hΨm (hG S).2.choose_spec hΨb
    rw [hpt, integral_finsetSum _ (fun S _ => (hint S (Finset.mem_univ S)).const_mul _)]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [integral_const_mul, hdiag S]
  rw [hquad]
  refine Finset.sum_le_sum (fun S _ => ?_)
  refine mul_le_mul_of_nonneg_right (mul_sqrt_sq_le (S.card : ℝ) m (Nat.cast_nonneg _) hm) ?_
  exact integral_nonneg (fun x => mul_self_nonneg _)

/-! ## 3. The `P`-side loss bound of FS's completion of squares

Combining the mass identity `fsPsideMassB1` with the sharp shift bound
`n0FunOp_shiftSharpScalarB1` gives the *actual* `P`-side loss of FS `final_v2.tex` l.3741–3743:
the `Θ₋`-weighted `P`-mass is dominated by the spectral sum `Σ_S(|S|+1−c)²∫(Π_SΦ)²`, i.e. by
`Var(n₀) + (S+1−c)²` in the corpus's scalars.  This is the form the `(A)`-assembly consumes
(next to `qSideLossB1`'s `Q`-side bound); see
`Submission/Work/BoseFixB1S/FINDING_fsCompletionExactB1S.md` §1–§2. -/

theorem fsPsideSharpBoundB1 {N : ℕ} {ℓ volA c : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (hc : 0 ≤ c)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
            (Work.UBBInputs8.boxPInd volA A i Φ) x) ^ 2)
      ≤ ∑ S : Finset (Fin N),
          ((S.card : ℝ) + 1 - c) ^ 2
            * ∫ x in Submission.BoseGases.abox N ℓ, (n0ProjOp volA A S Φ x) ^ 2 := by
  obtain ⟨C, _hC0, hCb⟩ := exists_abox_bound hℓ hΦc
  rw [fsPsideMassB1 hℓ hvol hA hvolA hAc (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c) hΦc]
  simpa only [sq] using
    n0FunOp_shiftSharpScalarB1 hℓ hvol hA hvolA hAc hc hΦc.measurable hCb

end Work.BoseFixB1S
