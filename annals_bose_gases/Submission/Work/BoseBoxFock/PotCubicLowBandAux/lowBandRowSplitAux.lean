import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.atomPairG
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.potCubicIntegrableGen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicLowBandAux.lowBandRowSplitAux`

The **row split + Cauchy–Schwarz** step of FS `lem:Q3-splitting2` in the cubic (`Q̃₃`) chapter.

Writing `Row := (∫ star Θ · potCubic … PHs … Θ).re − (∫ star Θ · potCubic … excited … Θ).re`,
`B T := boxSlotSum e T`, `LB := excited ∖ PHs` and, for `p : Mode × Mode`,

    `w p := E.fL p.1 * E.W1 p.2`,
    `X p := a_{f (p.1 − p.2)} a_{f p.2} Θ`,   `Y p := a_{g p.1} a_{e₀} Θ`   (`a_w := boxAnnOf e w`),
    `A p := (cIPn d (X p) (X p)).re`,          `B p := (cIPn d (Y p) (Y p)).re`,
    `z p := cIPn (d+2) Θ (potCubicAtom … p … Θ)`,

the statement is `Row ≤ 2 ℓ⁻³ √(Σ w A) √(Σ w B)`.

The proof is in four steps, each a separate lemma in this file:

1. **the low-band split** (`potCubic_lowBand_split'`): `potCubic PHs = potCubic excited − potCubic LB`,
   hence (linearity of the Bochner integral, `potCubicIntegrableGen`) `Row = − (∫ star Θ · potCubic LB Θ).re`;
2. **the atom expansion** (`cIPnAux_expand`): `∫ star Θ · potCubic LB Θ = ℓ⁻³ Σ_p w p · z p`;
3. **the per-pair bound** (`cIPnAux_atomNorm`): `‖z p‖ ≤ 2 √(A p) √(B p)`, from the FS pairing
   `cIPn_atom_eq_pairG` (`cIPn Θ (atom_p Θ) = cIPn d X Y + cIPn d Y X`) and Cauchy–Schwarz
   (`cIPnAux_cauchy`);
4. **the weighted discrete Cauchy–Schwarz** (`cIPnAux_weightedCS`): `‖Σ_p w_p z_p‖ ≤ 2 √(Σ|w|A) √(Σ|w|B)`.

All the analytic content of the row is therefore a finite-sum Cauchy–Schwarz; the *sizes* of the
two sums (`Σ w A = lowBandChiSum`, `Σ w B = lowBandCondSum`) are the two sibling lemmas.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PotCubicLowBandAux

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Elementary complex facts -/

/-- The real part of `star z * z` is `‖z‖ ^ 2`. -/
theorem cIPnAux_star_mul_self_re (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  have h : star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
    rw [Complex.star_def]
    exact Complex.normSq_eq_conj_mul_self.symm
  rw [h, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- The self-pairing of a function is the integral of `‖·‖²`. -/
theorem cIPnAux_self_re {n : ℕ} {X : Work.BoseDict.Xn n → ℂ}
    (hX : Integrable (fun x => star (X x) * X x) (volume : Measure (Work.BoseDict.Xn n))) :
    (Work.BoseDict.cIPn n X X).re = ∫ x, ‖X x‖ ^ 2 := by
  change (∫ x : Work.BoseDict.Xn n, star (X x) * X x).re = ∫ x, ‖X x‖ ^ 2
  have hpt : ∀ x : Work.BoseDict.Xn n, star (X x) * X x = ((‖X x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    have h : star (X x) * X x = ((Complex.normSq (X x) : ℝ) : ℂ) := by
      rw [Complex.star_def]
      exact Complex.normSq_eq_conj_mul_self.symm
    rw [h, Complex.normSq_eq_norm_sq]
  calc (∫ x : Work.BoseDict.Xn n, star (X x) * X x).re
      = (∫ x : Work.BoseDict.Xn n, ((‖X x‖ ^ 2 : ℝ) : ℂ)).re := by
        rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    _ = ((((∫ x, ‖X x‖ ^ 2) : ℝ)) : ℂ).re := by rw [integral_complex_ofReal]
    _ = ∫ x, ‖X x‖ ^ 2 := by simp

/-- `‖X‖²` is integrable exactly when `star X · X` is. -/
theorem cIPnAux_integrable_star_mul_self {n : ℕ} {X : Work.BoseDict.Xn n → ℂ}
    (hXm : AEMeasurable X (volume : Measure (Work.BoseDict.Xn n)))
    (hX : Integrable (fun x => ‖X x‖ ^ 2) (volume : Measure (Work.BoseDict.Xn n))) :
    Integrable (fun x => star (X x) * X x) (volume : Measure (Work.BoseDict.Xn n)) := by
  have haesm : AEStronglyMeasurable (fun x : Work.BoseDict.Xn n => star (X x) * X x)
      (volume : Measure (Work.BoseDict.Xn n)) :=
    ((Complex.continuous_conj.measurable.comp_aemeasurable hXm).mul hXm).aestronglyMeasurable
  have hnorm : Integrable (fun x : Work.BoseDict.Xn n => ‖star (X x) * X x‖) volume := by
    refine hX.congr (Filter.Eventually.of_forall fun x => ?_)
    show ‖X x‖ ^ 2 = ‖star (X x) * X x‖
    rw [norm_mul, norm_star]
    ring
  exact (MeasureTheory.integrable_norm_iff haesm).mp hnorm

/-- The weak regularity class (`WRegG`) gives `L²`-integrability. -/
theorem cIPnAux_wreg_integrable_normSq {n : ℕ} {ℓ : ℝ} {X : Work.BoseDict.Xn n → ℂ}
    (h : Work.BoseBoxFock.WRegG ℓ X) :
    Integrable (fun x => ‖X x‖ ^ 2) (volume : Measure (Work.BoseDict.Xn n)) := by
  obtain ⟨hm, ⟨C, hC⟩, hs⟩ := h
  have hXC : Integrable X (volume : Measure (Work.BoseDict.Xn n)) :=
    Work.MB.integrable_of_bdd_of_support (Work.MB.measurableSet_boxPow n ℓ)
      (Work.MB.volume_boxPow_lt_top n ℓ) hm.aestronglyMeasurable
      (fun x => (hC x).trans (le_max_left C 0))
      (fun x hx => Function.notMem_support.mp (fun hxs => hx (hs hxs)))
  refine (hXC.norm.const_mul (max C 0)).mono' (hm.norm.pow_const 2).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two]
  exact mul_le_mul_of_nonneg_right ((hC x).trans (le_max_left C 0)) (norm_nonneg _)

/-! ## 2. Cauchy–Schwarz for `cIPn` -/

/-- **Cauchy–Schwarz for the box pairing `cIPn`**, in the real form consumed by the row
decomposition:
`‖cIPn n X Y‖ ≤ √((cIPn n X X).re) · √((cIPn n Y Y).re)`. -/
theorem cIPnAux_cauchy {n : ℕ} {X Y : Work.BoseDict.Xn n → ℂ}
    (hXm : AEMeasurable X (volume : Measure (Work.BoseDict.Xn n)))
    (hYm : AEMeasurable Y (volume : Measure (Work.BoseDict.Xn n)))
    (hX : Integrable (fun x => ‖X x‖ ^ 2) (volume : Measure (Work.BoseDict.Xn n)))
    (hY : Integrable (fun x => ‖Y x‖ ^ 2) (volume : Measure (Work.BoseDict.Xn n))) :
    ‖Work.BoseDict.cIPn n X Y‖
      ≤ Real.sqrt ((Work.BoseDict.cIPn n X X).re)
        * Real.sqrt ((Work.BoseDict.cIPn n Y Y).re) := by
  have h1 : ‖Work.BoseDict.cIPn n X Y‖ ≤ ∫ x, ‖X x‖ * ‖Y x‖ := by
    rw [Work.BoseDict.cIPn]
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖(starRingEnd ℂ) (X x) * Y x‖ = ‖X x‖ * ‖Y x‖
    rw [norm_mul, Complex.norm_conj]
  have hX2 : MeasureTheory.MemLp X (ENNReal.ofReal (2 : ℝ))
      (volume : Measure (Work.BoseDict.Xn n)) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 from by norm_num]
    exact (MeasureTheory.memLp_two_iff_integrable_sq_norm hXm.aestronglyMeasurable).mpr hX
  have hY2 : MeasureTheory.MemLp Y (ENNReal.ofReal (2 : ℝ))
      (volume : Measure (Work.BoseDict.Xn n)) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 from by norm_num]
    exact (MeasureTheory.memLp_two_iff_integrable_sq_norm hYm.aestronglyMeasurable).mpr hY
  have h2 := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    (μ := (volume : Measure (Work.BoseDict.Xn n))) Real.HolderConjugate.two_two hX2 hY2
  have h3 : (∫ x, ‖X x‖ ^ (2 : ℝ) ∂volume) = ∫ x, ‖X x‖ ^ 2 ∂volume := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖X x‖ ^ (2 : ℝ) = ‖X x‖ ^ 2
    rw [Real.rpow_two]
  have h4 : (∫ x, ‖Y x‖ ^ (2 : ℝ) ∂volume) = ∫ x, ‖Y x‖ ^ 2 ∂volume := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖Y x‖ ^ (2 : ℝ) = ‖Y x‖ ^ 2
    rw [Real.rpow_two]
  rw [h3, h4] at h2
  have h5 : (∫ x, ‖X x‖ ^ 2 ∂volume) ^ ((1 : ℝ) / 2)
      = Real.sqrt (∫ x, ‖X x‖ ^ 2 ∂volume) := (Real.sqrt_eq_rpow _).symm
  have h6 : (∫ x, ‖Y x‖ ^ 2 ∂volume) ^ ((1 : ℝ) / 2)
      = Real.sqrt (∫ x, ‖Y x‖ ^ 2 ∂volume) := (Real.sqrt_eq_rpow _).symm
  rw [h5, h6] at h2
  have hsX : Real.sqrt (∫ x, ‖X x‖ ^ 2 ∂volume)
      = Real.sqrt ((Work.BoseDict.cIPn n X X).re) := by
    rw [cIPnAux_self_re (cIPnAux_integrable_star_mul_self hXm hX)]
  have hsY : Real.sqrt (∫ x, ‖Y x‖ ^ 2 ∂volume)
      = Real.sqrt ((Work.BoseDict.cIPn n Y Y).re) := by
    rw [cIPnAux_self_re (cIPnAux_integrable_star_mul_self hYm hY)]
  rw [hsX, hsY] at h2
  exact h1.trans h2

/-! ## 3. Weighted discrete Cauchy–Schwarz -/

/-- **Weighted Cauchy–Schwarz** on a finite index set: if `‖z i‖ ≤ 2 √(A i) √(B i)` for all
`i ∈ S`, then `‖Σ_i w_i z_i‖ ≤ 2 √(Σ_i |w_i| A_i) √(Σ_i |w_i| B_i)`. -/
theorem cIPnAux_weightedCS {ι : Type*} (S : Finset ι) (w A B : ι → ℝ) (z : ι → ℂ)
    (hA : ∀ i ∈ S, 0 ≤ A i) (hB : ∀ i ∈ S, 0 ≤ B i)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 2 * (Real.sqrt (A i) * Real.sqrt (B i))) :
    ‖∑ i ∈ S, (w i : ℂ) * z i‖
      ≤ 2 * Real.sqrt (∑ i ∈ S, |w i| * A i) * Real.sqrt (∑ i ∈ S, |w i| * B i) := by
  classical
  have h1 : ‖∑ i ∈ S, (w i : ℂ) * z i‖
      ≤ ∑ i ∈ S, |w i| * (2 * (Real.sqrt (A i) * Real.sqrt (B i))) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hnorm : ‖((w i : ℝ) : ℂ)‖ = |w i| := by simp
    rw [norm_mul, hnorm]
    exact mul_le_mul_of_nonneg_left (hz i hi) (abs_nonneg _)
  have h2 : ∑ i ∈ S, |w i| * (2 * (Real.sqrt (A i) * Real.sqrt (B i)))
      = 2 * ∑ i ∈ S, (Real.sqrt |w i| * Real.sqrt (A i)) * (Real.sqrt |w i| * Real.sqrt (B i)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hsq : Real.sqrt |w i| ^ 2 = |w i| := Real.sq_sqrt (abs_nonneg _)
    calc |w i| * (2 * (Real.sqrt (A i) * Real.sqrt (B i)))
        = 2 * (Real.sqrt |w i| ^ 2 * (Real.sqrt (A i) * Real.sqrt (B i))) := by
          rw [hsq]; ring
      _ = 2 * ((Real.sqrt |w i| * Real.sqrt (A i)) * (Real.sqrt |w i| * Real.sqrt (B i))) := by
          ring
  set f : ι → ℝ := fun i => Real.sqrt |w i| * Real.sqrt (A i) with hf
  set g : ι → ℝ := fun i => Real.sqrt |w i| * Real.sqrt (B i) with hg
  have hf2 : ∑ i ∈ S, f i ^ 2 = ∑ i ∈ S, |w i| * A i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hf]
    simp only [Pi.pow_apply, mul_pow, Real.sq_sqrt (abs_nonneg (w i)), Real.sq_sqrt (hA i hi)]
  have hg2 : ∑ i ∈ S, g i ^ 2 = ∑ i ∈ S, |w i| * B i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hg]
    simp only [Pi.pow_apply, mul_pow, Real.sq_sqrt (abs_nonneg (w i)), Real.sq_sqrt (hB i hi)]
  have hle : ∑ i ∈ S, f i * g i
      ≤ Real.sqrt (∑ i ∈ S, f i ^ 2) * Real.sqrt (∑ i ∈ S, g i ^ 2) := by
    rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg (f i))]
    exact Real.le_sqrt_of_sq_le (Finset.sum_mul_sq_le_sq_mul_sq S f g)
  calc ‖∑ i ∈ S, (w i : ℂ) * z i‖
      ≤ ∑ i ∈ S, |w i| * (2 * (Real.sqrt (A i) * Real.sqrt (B i))) := h1
    _ = 2 * ∑ i ∈ S, f i * g i := h2
    _ ≤ 2 * (Real.sqrt (∑ i ∈ S, f i ^ 2) * Real.sqrt (∑ i ∈ S, g i ^ 2)) :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
    _ = 2 * Real.sqrt (∑ i ∈ S, |w i| * A i) * Real.sqrt (∑ i ∈ S, |w i| * B i) := by
        rw [hf2, hg2]; ring

/-! ## 4. The per-pair bound -/

/-- **The `(s,k)`-pair bound.** With `X := a_{f(s−k)}a_{fk}Θ`, `Y := a_{g s}a_{e₀}Θ`,

    `‖cIPn (d+2) Θ (atom_{s,k} Θ)‖ ≤ 2 √((cIPn d X X).re) √((cIPn d Y Y).re)`. -/
theorem cIPnAux_atomNorm {m d : ℕ} [NeZero m] {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (s k : Mode)
    {Θ : Work.BoseDict.Xn (d + 2) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow (d + 2) ℓ)
    (hΘsym : ∀ (σ : Equiv.Perm (Fin (d + 2))) (x : Work.BoseDict.Xn (d + 2)),
      Θ (x ∘ σ) = Θ x) :
    ‖Work.BoseDict.cIPn (d + 2) Θ
        (Work.BoseBoxFock.FRK.potCubicAtom (fun T => Work.BoseDict.boxSlotSum e T)
          f g s k Θ)‖
      ≤ 2 * (Real.sqrt ((Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e (f (s - k)) d
                (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e (f (s - k)) d
                (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))).re)
            * Real.sqrt ((Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseBoxFock.evec0 m) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseBoxFock.evec0 m) (d + 1) Θ))).re)) := by
  have hpair := cIPn_atom_eq_pairG hmeas hbdd hsupp horth hMemLp f g s k
    hΘm hΘb hΘsupp hΘsym
  have hΘW : Work.BoseBoxFock.WRegG ℓ Θ := ⟨hΘm, hΘb, hΘsupp⟩
  have hX : Work.BoseBoxFock.WRegG ℓ
      (Work.BoseDict.boxAnnOf e (f (s - k)) d (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ)) :=
    Work.BoseBoxFock.boxAnnOf_wregG hmeas hbdd hsupp (f (s - k))
      (Work.BoseBoxFock.boxAnnOf_wregG hmeas hbdd hsupp (f k) hΘW)
  have hY : Work.BoseBoxFock.WRegG ℓ
      (Work.BoseDict.boxAnnOf e (g s) d
        (Work.BoseDict.boxAnnOf e (Work.BoseBoxFock.evec0 m) (d + 1) Θ)) :=
    Work.BoseBoxFock.boxAnnOf_wregG hmeas hbdd hsupp (g s)
      (Work.BoseBoxFock.boxAnnOf_wregG hmeas hbdd hsupp (Work.BoseBoxFock.evec0 m) hΘW)
  have hcsXY := cIPnAux_cauchy hX.meas.aemeasurable hY.meas.aemeasurable
    (cIPnAux_wreg_integrable_normSq hX) (cIPnAux_wreg_integrable_normSq hY)
  have hcsYX := cIPnAux_cauchy hY.meas.aemeasurable hX.meas.aemeasurable
    (cIPnAux_wreg_integrable_normSq hY) (cIPnAux_wreg_integrable_normSq hX)
  have hYX : ‖Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseBoxFock.evec0 m) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (f (s - k)) d
              (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))‖
      ≤ Real.sqrt ((Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e (f (s - k)) d
                (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e (f (s - k)) d
                (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))).re)
        * Real.sqrt ((Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseBoxFock.evec0 m) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseBoxFock.evec0 m) (d + 1) Θ))).re) := by
    refine hcsYX.trans (le_of_eq ?_)
    ring
  calc ‖Work.BoseDict.cIPn (d + 2) Θ
          (Work.BoseBoxFock.FRK.potCubicAtom (fun T => Work.BoseDict.boxSlotSum e T)
            f g s k Θ)‖
      = ‖Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (f (s - k)) d
              (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseBoxFock.evec0 m) (d + 1) Θ))
          + Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseBoxFock.evec0 m) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (f (s - k)) d
              (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))‖ := by rw [hpair]
    _ ≤ ‖Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (f (s - k)) d
              (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseBoxFock.evec0 m) (d + 1) Θ))‖
          + ‖Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseBoxFock.evec0 m) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (f (s - k)) d
              (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))‖ := norm_add_le _ _
    _ ≤ (Real.sqrt ((Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e (f (s - k)) d
                (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e (f (s - k)) d
                (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))).re)
          * Real.sqrt ((Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseBoxFock.evec0 m) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseBoxFock.evec0 m) (d + 1) Θ))).re))
        + (Real.sqrt ((Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e (f (s - k)) d
                (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e (f (s - k)) d
                (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))).re)
          * Real.sqrt ((Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseBoxFock.evec0 m) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseBoxFock.evec0 m) (d + 1) Θ))).re)) :=
        add_le_add hcsXY hYX
    _ = 2 * (Real.sqrt ((Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e (f (s - k)) d
                (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e (f (s - k)) d
                (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))).re)
            * Real.sqrt ((Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseBoxFock.evec0 m) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseBoxFock.evec0 m) (d + 1) Θ))).re)) := by
        ring

/-! ## 5. The atom expansion of the cubic row -/

/-- **The expansion of `∫ star Θ · potCubic … L … Θ`** into its weighted atoms (linearity of the
Bochner integral over the finite `(s,k)`-sum). -/
theorem cIPnAux_expand {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {m d : ℕ} [NeZero m] {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hemeas : ∀ l, Measurable (e l)) (heb : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hes : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (f g : Mode → Fin m → ℝ) (L : Finset Mode) (E : Work.BoseB7.Q3Env Mode)
    {Θ : Work.BoseDict.Xn (d + 2) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow (d + 2) ℓ) :
    (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g L E Θ x)
      = ((E.ell ^ (-(3 : ℝ)) : ℝ) : ℂ) *
        ∑ p ∈ (Work.BoseB7.excited Mode) ×ˢ L,
          ((E.fL p.1 * E.W1 p.2 : ℝ) : ℂ) *
            Work.BoseDict.cIPn (d + 2) Θ
              (Work.BoseBoxFock.FRK.potCubicAtom (fun T => Work.BoseDict.boxSlotSum e T)
                f g p.1 p.2 Θ) := by
  have hnest : (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ L,
        (E.fL s * E.W1 k) •
          Work.BoseBoxFock.FRK.potCubicAtom (fun T => Work.BoseDict.boxSlotSum e T) f g s k Θ)
      = ∑ p ∈ (Work.BoseB7.excited Mode) ×ˢ L,
          (E.fL p.1 * E.W1 p.2) •
            Work.BoseBoxFock.FRK.potCubicAtom (fun T => Work.BoseDict.boxSlotSum e T)
              f g p.1 p.2 Θ := by
    rw [Finset.sum_product]
  have h2 : (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g L E Θ x)
      = ((E.ell ^ (-(3 : ℝ)) : ℝ) : ℂ) *
        Work.BoseDict.cIPn (d + 2) Θ
          (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ L,
            (E.fL s * E.W1 k) •
              Work.BoseBoxFock.FRK.potCubicAtom (fun T => Work.BoseDict.boxSlotSum e T)
                f g s k Θ) := by
    change Work.BoseDict.cIPn (d + 2) Θ
        (Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g L E Θ)
      = ((E.ell ^ (-(3 : ℝ)) : ℝ) : ℂ) *
        Work.BoseDict.cIPn (d + 2) Θ
          (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ L,
            (E.fL s * E.W1 k) •
              Work.BoseBoxFock.FRK.potCubicAtom (fun T => Work.BoseDict.boxSlotSum e T)
                f g s k Θ)
    rw [Work.BoseBoxFock.FRK.potCubic_eq_sum_atom,
      Work.BoseBoxFock.FRK.cIPn_smul]
  have h3 : Work.BoseDict.cIPn (d + 2) Θ
        (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ L,
          (E.fL s * E.W1 k) •
            Work.BoseBoxFock.FRK.potCubicAtom (fun T => Work.BoseDict.boxSlotSum e T)
              f g s k Θ)
      = ∑ p ∈ (Work.BoseB7.excited Mode) ×ˢ L,
          ((E.fL p.1 * E.W1 p.2 : ℝ) : ℂ) *
            Work.BoseDict.cIPn (d + 2) Θ
              (Work.BoseBoxFock.FRK.potCubicAtom (fun T => Work.BoseDict.boxSlotSum e T)
                f g p.1 p.2 Θ) := by
    rw [hnest]
    exact Work.BoseBoxFock.FRK.cIPn_sum_smul _ _
      (fun p hp => atomIntegrableG hemeas heb hes hΘm hΘb hΘs f g p.1 p.2 E)
  rw [h2, h3]

/-! ## 6. The main theorem -/

theorem lowBandRowSplitAux {m d : ℕ} [NeZero m] {ℓ : ℝ}
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (f g : Mode → Fin m → ℝ) (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode)
    (hsub : PHs ⊆ Work.BoseB7.excited Mode) (hℓE : 0 < E.ell)
    {Θ : Work.BoseDict.Xn (d + 2) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow (d + 2) ℓ)
    (hΘsym : ∀ (σ : Equiv.Perm (Fin (d + 2))) (x : Work.BoseDict.Xn (d + 2)),
      Θ (x ∘ σ) = Θ x) :
    (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g PHs E Θ x).re
      - (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
          (Work.BoseB7.excited Mode) E Θ x).re
    ≤ 2 * (E.ell ^ (-(3 : ℝ))) *
        Real.sqrt (∑ s ∈ Work.BoseB7.excited Mode,
          ∑ k ∈ Work.BoseB7.excited Mode \ PHs,
            |E.fL s| * |E.W1 k| *
              (Work.BoseDict.cIPn d
                (Work.BoseDict.boxAnnOf e (f (s - k)) d
                  (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
                (Work.BoseDict.boxAnnOf e (f (s - k)) d
                  (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))).re) *
        Real.sqrt (∑ s ∈ Work.BoseB7.excited Mode,
          ∑ k ∈ Work.BoseB7.excited Mode \ PHs,
            |E.fL s| * |E.W1 k| *
              (Work.BoseDict.cIPn d
                (Work.BoseDict.boxAnnOf e (g s) d
                  (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
                (Work.BoseDict.boxAnnOf e (g s) d
                  (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re) := by
  classical
  -- ## Step 0: local notation
  let P : Finset (Mode × Mode) := (Work.BoseB7.excited Mode) ×ˢ (Work.BoseB7.excited Mode \ PHs)
  let w : Mode × Mode → ℝ := fun p => E.fL p.1 * E.W1 p.2
  let A : Mode × Mode → ℝ := fun p => (Work.BoseDict.cIPn d
      (Work.BoseDict.boxAnnOf e (f (p.1 - p.2)) d
        (Work.BoseDict.boxAnnOf e (f p.2) (d + 1) Θ))
      (Work.BoseDict.boxAnnOf e (f (p.1 - p.2)) d
        (Work.BoseDict.boxAnnOf e (f p.2) (d + 1) Θ))).re
  let B : Mode × Mode → ℝ := fun p => (Work.BoseDict.cIPn d
      (Work.BoseDict.boxAnnOf e (g p.1) d
        (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
      (Work.BoseDict.boxAnnOf e (g p.1) d
        (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re
  let z : Mode × Mode → ℂ := fun p => Work.BoseDict.cIPn (d + 2) Θ
      (Work.BoseBoxFock.FRK.potCubicAtom (fun T => Work.BoseDict.boxSlotSum e T)
        f g p.1 p.2 Θ)
  -- ## Step 1: integrability of the cubic integrands and the low-band split
  have hIntExc := potCubicIntegrableGen hmeas hbdd hsupp hΘm hΘb hΘsupp f g
    (Work.BoseB7.excited Mode) E
  have hIntLB := potCubicIntegrableGen hmeas hbdd hsupp hΘm hΘb hΘsupp f g
    (Work.BoseB7.excited Mode \ PHs) E
  have hsplit : (fun x : Work.BoseDict.Xn (d + 2) => star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g PHs E Θ x)
      = fun x => star (Θ x) * Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T)
            f g (Work.BoseB7.excited Mode) E Θ x
          - star (Θ x) * Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T)
            f g (Work.BoseB7.excited Mode \ PHs) E Θ x := by
    funext x
    have h := congrFun (congrFun (Work.BoseBoxFock.FRK.potCubic_lowBand_split'
      (fun T => Work.BoseDict.boxSlotSum e T) f g PHs hsub E) Θ) x
    simp only [Pi.sub_apply] at h
    rw [h]
    ring
  have hRowEq : (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g PHs E Θ x).re
      - (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
          (Work.BoseB7.excited Mode) E Θ x).re
      = - (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
          (Work.BoseB7.excited Mode \ PHs) E Θ x).re := by
    have hsub' : (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
          Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g PHs E Θ x)
        = (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
            Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
              (Work.BoseB7.excited Mode) E Θ x)
          - (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
            Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
              (Work.BoseB7.excited Mode \ PHs) E Θ x) := by
      rw [hsplit]
      exact MeasureTheory.integral_sub hIntExc hIntLB
    rw [hsub', Complex.sub_re]
    ring
  -- ## Step 2: the atom expansion
  have hexp := cIPnAux_expand hmeas hbdd hsupp f g (Work.BoseB7.excited Mode \ PHs) E
    hΘm hΘb hΘsupp
  have hRowEq2 : (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g PHs E Θ x).re
      - (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
          (Work.BoseB7.excited Mode) E Θ x).re
      = - (E.ell ^ (-(3 : ℝ)) * (∑ p ∈ P, ((w p : ℝ) : ℂ) * z p).re) := by
    rw [hRowEq, hexp, Complex.re_ofReal_mul]
  -- ## Step 3: the weighted Cauchy–Schwarz
  have hAnnA : ∀ p ∈ P, 0 ≤ A p := by
    intro p hp
    dsimp only [A]
    have hX : Work.BoseBoxFock.WRegG ℓ
        (Work.BoseDict.boxAnnOf e (f (p.1 - p.2)) d
          (Work.BoseDict.boxAnnOf e (f p.2) (d + 1) Θ)) :=
      Work.BoseBoxFock.boxAnnOf_wregG hmeas hbdd hsupp (f (p.1 - p.2))
        (Work.BoseBoxFock.boxAnnOf_wregG hmeas hbdd hsupp (f p.2)
          ⟨hΘm, hΘb, hΘsupp⟩)
    rw [cIPnAux_self_re (cIPnAux_integrable_star_mul_self hX.meas.aemeasurable
      (cIPnAux_wreg_integrable_normSq hX))]
    exact MeasureTheory.integral_nonneg (fun x => sq_nonneg (‖Work.BoseDict.boxAnnOf e
      (f (p.1 - p.2)) d (Work.BoseDict.boxAnnOf e (f p.2) (d + 1) Θ) x‖))
  have hAnnB : ∀ p ∈ P, 0 ≤ B p := by
    intro p hp
    dsimp only [B]
    have hY : Work.BoseBoxFock.WRegG ℓ
        (Work.BoseDict.boxAnnOf e (g p.1) d
          (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ)) :=
      Work.BoseBoxFock.boxAnnOf_wregG hmeas hbdd hsupp (g p.1)
        (Work.BoseBoxFock.boxAnnOf_wregG hmeas hbdd hsupp (Work.BoseB4.evec m 0)
          ⟨hΘm, hΘb, hΘsupp⟩)
    rw [cIPnAux_self_re (cIPnAux_integrable_star_mul_self hY.meas.aemeasurable
      (cIPnAux_wreg_integrable_normSq hY))]
    exact MeasureTheory.integral_nonneg (fun x => sq_nonneg (‖Work.BoseDict.boxAnnOf e
      (g p.1) d (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ) x‖))
  have hzbd : ∀ p ∈ P, ‖z p‖ ≤ 2 * (Real.sqrt (A p) * Real.sqrt (B p)) := by
    intro p hp
    dsimp only [z, A, B]
    exact cIPnAux_atomNorm hmeas hbdd hsupp horth hMemLp f g p.1 p.2 hΘm hΘb hΘsupp hΘsym
  have hCS := cIPnAux_weightedCS (S := P) (w := w) (A := A) (B := B) (z := z)
    hAnnA hAnnB hzbd
  have hSX : (∑ p ∈ P, |w p| * A p)
      = ∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ Work.BoseB7.excited Mode \ PHs,
          |E.fL s| * |E.W1 k| * (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (f (s - k)) d
              (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (f (s - k)) d
              (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))).re := by
    dsimp only [P]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => ?_
    dsimp only [w, A]
    rw [abs_mul]
  have hSY : (∑ p ∈ P, |w p| * B p)
      = ∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ Work.BoseB7.excited Mode \ PHs,
          |E.fL s| * |E.W1 k| * (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re := by
    dsimp only [P]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => ?_
    dsimp only [w, B]
    rw [abs_mul]
  rw [hSX, hSY] at hCS
  have hsq : 0 ≤ E.ell ^ (-(3 : ℝ)) := Real.rpow_nonneg hℓE.le _
  calc (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g PHs E Θ x).re
      - (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
          (Work.BoseB7.excited Mode) E Θ x).re
      = - (E.ell ^ (-(3 : ℝ)) * (∑ p ∈ P, ((w p : ℝ) : ℂ) * z p).re) := hRowEq2
    _ ≤ |E.ell ^ (-(3 : ℝ)) * (∑ p ∈ P, ((w p : ℝ) : ℂ) * z p).re| := neg_le_abs _
    _ = E.ell ^ (-(3 : ℝ)) * |(∑ p ∈ P, ((w p : ℝ) : ℂ) * z p).re| := by
        rw [abs_mul, abs_of_nonneg hsq]
    _ ≤ E.ell ^ (-(3 : ℝ)) * ‖∑ p ∈ P, ((w p : ℝ) : ℂ) * z p‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hsq
    _ ≤ E.ell ^ (-(3 : ℝ)) * (2 * Real.sqrt (∑ s ∈ Work.BoseB7.excited Mode,
          ∑ k ∈ Work.BoseB7.excited Mode \ PHs,
            |E.fL s| * |E.W1 k| * (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e (f (s - k)) d
                (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e (f (s - k)) d
                (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))).re)
        * Real.sqrt (∑ s ∈ Work.BoseB7.excited Mode,
          ∑ k ∈ Work.BoseB7.excited Mode \ PHs,
            |E.fL s| * |E.W1 k| * (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re)) :=
        mul_le_mul_of_nonneg_left hCS hsq
    _ = 2 * (E.ell ^ (-(3 : ℝ))) * Real.sqrt (∑ s ∈ Work.BoseB7.excited Mode,
          ∑ k ∈ Work.BoseB7.excited Mode \ PHs,
            |E.fL s| * |E.W1 k| * (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e (f (s - k)) d
                (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e (f (s - k)) d
                (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))).re) *
        Real.sqrt (∑ s ∈ Work.BoseB7.excited Mode,
          ∑ k ∈ Work.BoseB7.excited Mode \ PHs,
            |E.fL s| * |E.W1 k| * (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re) := by
        ring

end Work.BoseBoxFock.PotCubicLowBandAux
