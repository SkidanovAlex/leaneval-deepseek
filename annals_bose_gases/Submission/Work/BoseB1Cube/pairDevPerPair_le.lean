import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.mfPairDefectLeB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.pairDevPerPair_le` — the per-pair deviation estimate with a box-supported kernel

**Statement.**  For `i ≠ j` and a pair kernel `W` which is *supported in the box* (`W x y ≠ 0 →
x ∈ A ∧ y ∈ A`) and bounded by `Cw`, the squared deviation of the state `Φ` from the two-fold
box projection `P_iP_jΦ` is paid, on the analysis box, by the two one-slot excited counts:

  `∫_{abox N ℓ} (Φ − P_iP_jΦ)²·W(x_i,x_j) ≤ 2·Cw·(∫ (Q_iΦ)² + ∫ (Q_jΦ)²)`.

**Math.**  Let `σ_a := 1_A(x_a)`.  Because `W` is supported in `A × A`, the integrand vanishes
wherever `σ_i = 0` or `σ_j = 0`; there the right-hand side is `≥ 0` for free (both terms are
squares, `Cw ≥ 0`).  On the set `{σ_i = σ_j = 1}` the two box projections simplify
(`boxPInd_boxQInd_pointwise`):

  `P_iQ_jΦ = σ_j·(P_iΦ − P_iP_jΦ) = P_iΦ − P_iP_jΦ`,   `Q_iΦ = σ_i·Φ − P_iΦ = Φ − P_iΦ`,

whence the exact pointwise identity

  `Φ − P_iP_jΦ = Q_iΦ + P_iQ_jΦ`   on `{σ_i = σ_j = 1}`.

Since `|W| ≤ Cw`, `(a+b)² ≤ 2a² + 2b²` gives the pointwise bound

  `(Φ − P_iP_jΦ)²·W(x_i,x_j) ≤ Cw·(2(Q_iΦ)² + 2(P_iQ_jΦ)²)`,

and integrating, `∫(P_iQ_jΦ)² = ∫(P_i(Q_jΦ))² ≤ ∫(Q_jΦ)²` by the `L²` contraction of `P_i`
(`boxPInd_sq_le_self`).  Everything is bounded on the compact box, so the integrability
hypotheses are supplied by `integrableOn_sq_of_bound` (and, for the integrand itself, by
`Integrable.bdd_mul` against the kernel `hWint`).

Note the contrast with `Work.BoseFixB1S.mfPairDefectPerPair` (the model of this proof): there the
box support is carried by the *state* (`Φ x ≠ 0 → x_p ∈ A`), here by the *kernel*.
-/

namespace Work.BoseB1Cube

open MeasureTheory

theorem pairDevPerPair_le {N : ℕ} {ℓ V : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hℓ : 0 < ℓ) (hV : 0 < V) (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (Cw : ℝ) (hCwnn : 0 ≤ Cw) (hWle : ∀ x y, |W x y| ≤ Cw)
    (hWsupp : ∀ x y, W x y ≠ 0 → x ∈ A ∧ y ∈ A)
    {i j : Fin N} (hij : i ≠ j)
    (hWint : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => W (x i) (x j))
      (Submission.BoseGases.abox N ℓ)) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Φ x - Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x) ^ 2
          * W (x i) (x j))
      ≤ 2 * Cw * ((∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
          + (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A j Φ x) ^ 2)) := by
  classical
  have hΦm : Measurable Φ := hΦc.measurable
  -- ## 1. Bounds of the state and of the projected states on the compact box
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox N ℓ) (f := Φ) hΦc.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 (Submission.BoseGases.zero_mem_abox hℓ.le))
  have hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ C :=
    fun x hx => by simpa [Real.norm_eq_abs] using hC x hx
  have hPjb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd V A j Φ x| ≤ C :=
    Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc j hΦb
  have hPijb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x| ≤ C :=
    Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc i hPjb
  have hQib : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd V A i Φ x| ≤ 2 * C :=
    Work.BoseFixB1S.abs_boxQInd_le hℓ hV hA hVeq hAc i hΦb
  have hQjb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd V A j Φ x| ≤ 2 * C :=
    Work.BoseFixB1S.abs_boxQInd_le hℓ hV hA hVeq hAc j hΦb
  have hPiQjb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A j Φ) x| ≤ 2 * C :=
    Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc i hQjb
  -- ## 2. Measurability
  have hQim : Measurable (fun x : Submission.BoseGases.X N =>
      Work.UBBInputs8.boxQInd V A i Φ x) :=
    Work.BoseFixB1S.measurable_boxQInd V hA i hΦm
  have hQjm : Measurable (fun x : Submission.BoseGases.X N =>
      Work.UBBInputs8.boxQInd V A j Φ x) :=
    Work.BoseFixB1S.measurable_boxQInd V hA j hΦm
  have hPiQjm : Measurable (fun x : Submission.BoseGases.X N =>
      Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A j Φ) x) :=
    Work.BoseFixB1S.measurable_boxPInd V A hA i hQjm
  have hPijm : Measurable (fun x : Submission.BoseGases.X N =>
      Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x) :=
    Work.BoseFixB1S.measurable_boxPInd V A hA i
      (Work.BoseFixB1S.measurable_boxPInd V A hA j hΦm)
  -- ## 3. The exact pointwise identity on `{σ_i = σ_j = 1}`
  have hkey : ∀ x ∈ Submission.BoseGases.abox N ℓ, x i ∈ A → x j ∈ A →
      Φ x - Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x
        = Work.UBBInputs8.boxQInd V A i Φ x
          + Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A j Φ) x := by
    intro x hx hxi hxj
    have hp := Work.BoseFixB1S.boxPInd_boxQInd_pointwise hℓ hV hA hVeq hAc hij hΦc x hx
    rw [Set.indicator_of_mem hxj, one_mul] at hp
    have hq : Work.UBBInputs8.boxQInd V A i Φ x
        = Φ x - Work.UBBInputs8.boxPInd V A i Φ x := by
      rw [Work.BoseFixB1S.boxQInd_eq]
      have hIndi : Work.BoseFixB1S.Aind A (x i) = 1 := by
        unfold Work.BoseFixB1S.Aind
        rw [Set.indicator_of_mem hxi]
      rw [hIndi, one_mul]
    rw [hq, hp]
    ring
  -- ## 4. The pointwise bound a.e. on the box
  have hpt : ∀ᵐ x ∂((MeasureTheory.volume : Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N ℓ)),
      (Φ x - Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x) ^ 2
          * W (x i) (x j)
        ≤ Cw * (2 * (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2
            + 2 * (Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A j Φ) x) ^ 2) := by
    rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    refine Filter.Eventually.of_forall fun x hx => ?_
    by_cases hxi : x i ∈ A
    · by_cases hxj : x j ∈ A
      · -- the box-supported case: the exact identity applies
        have hid := hkey x hx hxi hxj
        have hsq : (Φ x - Work.UBBInputs8.boxPInd V A i
              (Work.UBBInputs8.boxPInd V A j Φ) x) ^ 2
            ≤ 2 * (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2
              + 2 * (Work.UBBInputs8.boxPInd V A i
                  (Work.UBBInputs8.boxQInd V A j Φ) x) ^ 2 := by
          rw [hid]
          nlinarith [sq_nonneg (Work.UBBInputs8.boxQInd V A i Φ x
            - Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A j Φ) x)]
        calc (Φ x - Work.UBBInputs8.boxPInd V A i
                (Work.UBBInputs8.boxPInd V A j Φ) x) ^ 2 * W (x i) (x j)
            ≤ (Φ x - Work.UBBInputs8.boxPInd V A i
                (Work.UBBInputs8.boxPInd V A j Φ) x) ^ 2 * |W (x i) (x j)| := by
              have h1 : W (x i) (x j) ≤ |W (x i) (x j)| := le_abs_self _
              nlinarith [sq_nonneg (Φ x - Work.UBBInputs8.boxPInd V A i
                (Work.UBBInputs8.boxPInd V A j Φ) x)]
          _ ≤ (Φ x - Work.UBBInputs8.boxPInd V A i
                (Work.UBBInputs8.boxPInd V A j Φ) x) ^ 2 * Cw :=
              mul_le_mul_of_nonneg_left (hWle _ _)
                (sq_nonneg (Φ x - Work.UBBInputs8.boxPInd V A i
                  (Work.UBBInputs8.boxPInd V A j Φ) x))
          _ ≤ (2 * (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2
                + 2 * (Work.UBBInputs8.boxPInd V A i
                    (Work.UBBInputs8.boxQInd V A j Φ) x) ^ 2) * Cw :=
              mul_le_mul_of_nonneg_right hsq hCwnn
          _ = Cw * (2 * (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2
                + 2 * (Work.UBBInputs8.boxPInd V A i
                    (Work.UBBInputs8.boxQInd V A j Φ) x) ^ 2) := by ring
      · -- `x j ∉ A`: the kernel vanishes there
        have hW0 : W (x i) (x j) = 0 := by
          by_contra h
          exact hxj (hWsupp _ _ h).2
        rw [hW0, mul_zero]
        exact mul_nonneg hCwnn (by
          nlinarith [sq_nonneg (Work.UBBInputs8.boxQInd V A i Φ x),
            sq_nonneg (Work.UBBInputs8.boxPInd V A i
              (Work.UBBInputs8.boxQInd V A j Φ) x)])
    · -- `x i ∉ A`: the kernel vanishes there
      have hW0 : W (x i) (x j) = 0 := by
        by_contra h
        exact hxi (hWsupp _ _ h).1
      rw [hW0, mul_zero]
      exact mul_nonneg hCwnn (by
        nlinarith [sq_nonneg (Work.UBBInputs8.boxQInd V A i Φ x),
          sq_nonneg (Work.UBBInputs8.boxPInd V A i
            (Work.UBBInputs8.boxQInd V A j Φ) x)])
  -- ## 5. The three integrability facts
  have hQisq : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
      (Submission.BoseGases.abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_sq_of_bound hℓ hQim hQib
  have hQjsq : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => (Work.UBBInputs8.boxQInd V A j Φ x) ^ 2)
      (Submission.BoseGases.abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_sq_of_bound hℓ hQjm hQjb
  have hPiQjsq : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A j Φ) x) ^ 2)
      (Submission.BoseGases.abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_sq_of_bound hℓ hPiQjm hPiQjb
  -- the integrand itself, using the integrability of the kernel
  have hfint : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Φ x - Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x) ^ 2
          * W (x i) (x j))
      (Submission.BoseGases.abox N ℓ) volume := by
    refine MeasureTheory.Integrable.bdd_mul (c := (2 * C) ^ 2) hWint
      ((hΦm.sub hPijm).pow_const 2).aestronglyMeasurable ?_
    rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    refine Filter.Eventually.of_forall fun x hx => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : |Φ x - Work.UBBInputs8.boxPInd V A i
        (Work.UBBInputs8.boxPInd V A j Φ) x| ≤ 2 * C := by
      calc |Φ x - Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x|
          ≤ |Φ x| + |Work.UBBInputs8.boxPInd V A i
              (Work.UBBInputs8.boxPInd V A j Φ) x| := abs_sub _ _
        _ ≤ C + C := add_le_add (hΦb x hx) (hPijb x hx)
        _ = 2 * C := by ring
    calc (Φ x - Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x) ^ 2
        = |Φ x - Work.UBBInputs8.boxPInd V A i
            (Work.UBBInputs8.boxPInd V A j Φ) x| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * C) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hgint : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        Cw * (2 * (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2
          + 2 * (Work.UBBInputs8.boxPInd V A i
              (Work.UBBInputs8.boxQInd V A j Φ) x) ^ 2))
      (Submission.BoseGases.abox N ℓ) volume :=
    (((hQisq.const_mul 2).add (hPiQjsq.const_mul 2))).const_mul Cw
  -- ## 6. The integral comparison
  have hmono : (∫ x in Submission.BoseGases.abox N ℓ,
        (Φ x - Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x) ^ 2
          * W (x i) (x j))
      ≤ ∫ x in Submission.BoseGases.abox N ℓ,
        Cw * (2 * (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2
          + 2 * (Work.UBBInputs8.boxPInd V A i
              (Work.UBBInputs8.boxQInd V A j Φ) x) ^ 2) :=
    MeasureTheory.integral_mono_ae hfint hgint hpt
  have hsplit : (∫ x in Submission.BoseGases.abox N ℓ,
        Cw * (2 * (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2
          + 2 * (Work.UBBInputs8.boxPInd V A i
              (Work.UBBInputs8.boxQInd V A j Φ) x) ^ 2))
      = Cw * (2 * (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
          + 2 * (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd V A i
              (Work.UBBInputs8.boxQInd V A j Φ) x) ^ 2)) := by
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add (hQisq.const_mul 2) (hPiQjsq.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  -- the `L²` contraction of `P_i` at `Q_jΦ`
  have hcontr : (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A j Φ) x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A j Φ x) ^ 2 :=
    Work.BoseFixB1S.boxPInd_sq_le_self hℓ hV hA hVeq hAc i hQjm hQjb
  -- ## 7. Assembly
  calc (∫ x in Submission.BoseGases.abox N ℓ,
        (Φ x - Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x) ^ 2
          * W (x i) (x j))
      ≤ ∫ x in Submission.BoseGases.abox N ℓ,
        Cw * (2 * (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2
          + 2 * (Work.UBBInputs8.boxPInd V A i
              (Work.UBBInputs8.boxQInd V A j Φ) x) ^ 2) := hmono
    _ = Cw * (2 * (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
          + 2 * (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd V A i
              (Work.UBBInputs8.boxQInd V A j Φ) x) ^ 2)) := hsplit
    _ ≤ Cw * (2 * (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
          + 2 * (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A j Φ x) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCwnn
        linarith [hcontr]
    _ = 2 * Cw * ((∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
          + (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A j Φ x) ^ 2)) := by ring

end Work.BoseB1Cube
