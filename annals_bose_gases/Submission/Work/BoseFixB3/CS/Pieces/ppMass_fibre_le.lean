import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB3.CS.Pieces.abox2_peel
import Submission.Work.BoseFixB3.CS.Pieces.q4B_pair_swap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.ppMass_fibre_le`

The **fibre form** of the `n = 2` congruence-step bound `Pieces.ppMass_le_q4mass_cnPlus_two`:
for an `n`-body state `Φ`, a background configuration `x` and a pair of distinct slots
`i ≠ j`, the condensate amplitude

  `X = aP ℓ i (aP ℓ j Φ) x`

is dominated by the `4Q`-square and the two `Q`-masses **localised on the pair fibre**

  `u ↦ Φ (Function.update (Function.update x i (u 0)) j (u 1))`,  `u : X 2`.

The proof restricts the `n = 2` theorem to that fibre (`pairFibre_*` from
`Pieces.pairFibreDefs` transport the projections and the `4Q`-bracket) and converts the two
box integrals of the `n = 2` theorem into the iterated cube integrals of the statement
(`Pieces.abox2_peel`).

## Parse warning and the companion `ppMass_fibre_le_outer`

The `∫ … in …, ` notation parses its body at precedence `60`, so in the statement of
`ppMass_fibre_le` the additive term `+ (ℓ ^ 2)⁻¹ * (∫ y, ∫ z, …)` is *inside* the body of the
preceding double integral, i.e. the statement reads

  `2 X² ≤ C * (2 · ∫∫ (F + (ℓ²)⁻¹·Q))`,    `Q := ∫∫ ((Q_i Φ)² + (Q_j Φ)²)`,

and not the (intended) additive form `C · (2·∫∫ F + (ℓ²)⁻¹·∫∫ (…)²)` of the design note
`DESIGN_ppMass_le_q4mass_cnPlus.md` §14.1.  Since `∫∫ (F + c) = ∫∫ F + c·ℓ⁶` for a constant
`c`, the two readings differ by the factor `2·ℓ⁴` against `ℓ⁻²` on the fluctuation term; the
as-written form is *weaker* for `ℓ > 2^{-1/6}` and does not imply the additive form.

Both statements are theorems here: the sharp (additive) form is the private `fibre_core` /
public `ppMass_fibre_le_outer` below, and `ppMass_fibre_le` — whose statement is fixed —
follows from it with the additional *free* constant `2 + ((R/chiR0)⁶)⁻¹`
(`fibre_split_le` supplies the two monotonicity inequalities `∫∫F ≤ ∫∫(F + c)` and
`c·ℓ⁶ ≤ ∫∫(F + c)` on the fibre; the arithmetic is the `calc` at the end of
`ppMass_fibre_le`).

**Consumers of the design note's §14.1 statement should use `ppMass_fibre_le_outer`.**
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB3.CS.Pieces

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.style.haveILetI false

/-- **The sharp fibre bound (additive form).**  For every `ℓ` with `R ≤ ℓ·chiR0`, every `n`,
every distinct pair `i ≠ j`, every continuous `Φ : X n → ℝ` and every configuration `x`,

  `2·(P_i P_j Φ x)² ≤ C·( 2·∬ (q4B_{ij})²·w + ℓ⁻²·∬ ((Q_iΦ)² + (Q_jΦ)²) )`,

with `∬` the iterated integral over the cube `acube ℓ` and the fibre configuration
`Function.update (Function.update x i y) j z`. -/
private theorem fibre_core {v : E3 → ℝ} (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1 MeasureTheory.volume)
    (R : ℝ) (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hav : 0 < BoseGases.a v)
    (h : ∃ w : E3 → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℝ), 0 < ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
      ∀ (n : ℕ) (i j : Fin n), i ≠ j → ∀ {Φ : Submission.BoseGases.X n → ℝ}, Continuous Φ →
      ∀ x : Submission.BoseGases.X n,
      2 * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x) ^ 2
        ≤ C * (2 * (∫ y in Submission.BoseGases.acube ℓ,
                ∫ z in Submission.BoseGases.acube ℓ,
                (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h))
                    Φ (i, j) (Function.update (Function.update x i y) j z)) ^ 2
                  * Submission.BoseGases.wLoc ℓ v 0 y z)
            + (ℓ ^ 2)⁻¹ * (∫ y in Submission.BoseGases.acube ℓ,
                ∫ z in Submission.BoseGases.acube ℓ,
                  (Submission.BoseGases.aQ ℓ i Φ
                      (Function.update (Function.update x i y) j z)) ^ 2
                + (Submission.BoseGases.aQ ℓ j Φ
                      (Function.update (Function.update x i y) j z)) ^ 2)) := by
  classical
  obtain ⟨C₂, hC₂0, hC₂⟩ := ppMass_le_q4mass_cnPlus_two hv hvrad hv1 R hR hv_supp hav h
  refine ⟨C₂, hC₂0, ?_⟩
  intro ℓ hℓ hRℓ n i j hij Φ hΦc x₀
  set ω : E3 → ℝ := Classical.choose h with hωdef
  have hv_int : MeasureTheory.Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
  have hsuppv : ∀ z : E3, R ≤ ‖z‖ → v z = 0 := fun z hz =>
    Submission.BoseGases.v_eq_zero_of_norm_ge hv_supp hz
  have hsymω : ∀ a b : E3, Submission.BoseGases.omC ω a b = Submission.BoseGases.omC ω b a :=
    fun a b => Submission.BoseGases.omC_chosen_sym h a b
  have hsymw : ∀ a b : E3,
      Submission.BoseGases.wLoc ℓ v 0 a b = Submission.BoseGases.wLoc ℓ v 0 b a :=
    fun a b => Work.BoseBox.wLoc_pair_symm (Submission.BoseGases.radial_even hvrad) ℓ 0 a b
  have hΨc : Continuous (pairFibre x₀ i j Φ) := pairFibre_continuous hΦc
  -- ## the left-hand side
  have hLHS : Work.BoseFixB3.CS.ppMass ℓ (pairFibre x₀ i j Φ)
      = 2 * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x₀) ^ 2 := by
    rw [ppMass_two_eq hℓ hΨc,
      aP_aP_pairFibre_const hℓ hij hΦc x₀ (0 : Submission.BoseGases.X 2)]
  -- ## the `4Q`-mass of the fibre
  have hQ4 : Work.BoseFixB3.CS.q4Mass ℓ (Submission.BoseGases.omC ω)
        (Submission.BoseGases.wLoc ℓ v 0) (pairFibre x₀ i j Φ)
      = 2 * (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
          (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) Φ (i, j)
              (Function.update (Function.update x₀ i y) j z)) ^ 2
            * Submission.BoseGases.wLoc ℓ v 0 y z) := by
    have hpair : Submission.BoseGases.pairSet 2 = ({(0,1),(1,0)} : Finset (Fin 2 × Fin 2)) := by
      decide
    have hnotmem : ((0,1) : Fin 2 × Fin 2) ∉ ({(1,0)} : Finset (Fin 2 × Fin 2)) := by decide
    rw [Work.BoseFixB3.CS.q4Mass, hpair, Finset.sum_insert hnotmem, Finset.sum_singleton]
    have hI01 : (∫ x in Submission.BoseGases.abox 2 ℓ,
          (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) (pairFibre x₀ i j Φ) (0, 1) x) ^ 2
            * Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1))
        = ∫ x in Submission.BoseGases.abox 2 ℓ,
          (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) Φ (i, j) (pairUpd x₀ i j x)) ^ 2
            * Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) := by
      refine MeasureTheory.setIntegral_congr_ae (Submission.BoseGases.abox_measurable 2 ℓ) ?_
      filter_upwards with x _
      rw [q4B_pairFibre_zero_one hij (Submission.BoseGases.omC ω) Φ x₀ x]
    have hI10 : (∫ x in Submission.BoseGases.abox 2 ℓ,
          (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) (pairFibre x₀ i j Φ) (1, 0) x) ^ 2
            * Submission.BoseGases.wLoc ℓ v 0 (x 1) (x 0))
        = ∫ x in Submission.BoseGases.abox 2 ℓ,
          (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) Φ (i, j) (pairUpd x₀ i j x)) ^ 2
            * Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) := by
      refine MeasureTheory.setIntegral_congr_ae (Submission.BoseGases.abox_measurable 2 ℓ) ?_
      filter_upwards with x _
      rw [q4B_pairFibre_one_zero hij (Submission.BoseGases.omC ω) Φ x₀ x,
        q4B_pair_swap hsymω hij hΦc (pairUpd x₀ i j x),
        hsymw (x 1) (x 0)]
    rw [hI01, hI10]
    have hFint0 : MeasureTheory.IntegrableOn
        (fun u : Submission.BoseGases.X 2 =>
          (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) (pairFibre x₀ i j Φ) (0, 1) u) ^ 2
            * Submission.BoseGases.wLoc ℓ v 0 (u 0) (u 1))
        (Submission.BoseGases.abox 2 ℓ) MeasureTheory.volume := by
      obtain ⟨-, hmeas01, B, hB0, hbnd01⟩ :=
        ae_bounded_q4B_abox hv hvrad R hR hv_supp hav h (ℓ := ℓ) hℓ
          (Φ := pairFibre x₀ i j Φ) hΨc (p := (0, 1)) (by decide)
      exact integrableOn_sq_mul_wLoc hℓ hv_int hsuppv hRℓ (p := (0, 1)) (by decide)
        hmeas01 hB0 hbnd01
    have hFint : MeasureTheory.IntegrableOn
        (fun u : Submission.BoseGases.X 2 =>
          (fun a b : E3 => (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) Φ (i, j)
              (Function.update (Function.update x₀ i a) j b)) ^ 2
            * Submission.BoseGases.wLoc ℓ v 0 a b) (u 0) (u 1))
        (Submission.BoseGases.abox 2 ℓ) MeasureTheory.volume :=
      hFint0.congr_fun (fun u _ => by
        show (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) (pairFibre x₀ i j Φ) (0, 1) u) ^ 2
              * Submission.BoseGases.wLoc ℓ v 0 (u 0) (u 1)
            = (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) Φ (i, j)
                (Function.update (Function.update x₀ i (u 0)) j (u 1))) ^ 2
              * Submission.BoseGases.wLoc ℓ v 0 (u 0) (u 1)
        rw [q4B_pairFibre_zero_one hij (Submission.BoseGases.omC ω) Φ x₀ u]
        rfl)
        (Submission.BoseGases.abox_measurable 2 ℓ)
    have hpeel : (∫ u in Submission.BoseGases.abox 2 ℓ,
          (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) Φ (i, j) (pairUpd x₀ i j u)) ^ 2
            * Submission.BoseGases.wLoc ℓ v 0 (u 0) (u 1))
        = ∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
          (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) Φ (i, j)
              (Function.update (Function.update x₀ i y) j z)) ^ 2
            * Submission.BoseGases.wLoc ℓ v 0 y z :=
      abox2_peel (ℓ := ℓ) (F := fun a b : E3 =>
        (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) Φ (i, j)
            (Function.update (Function.update x₀ i a) j b)) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 a b) hFint
    rw [hpeel]
    ring
  -- ## the fluctuation mass of the fibre
  have hCN : Submission.BoseGases.cnPlus ℓ (pairFibre x₀ i j Φ)
      = ∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
          ((Submission.BoseGases.aQ ℓ i Φ (Function.update (Function.update x₀ i y) j z)) ^ 2
            + (Submission.BoseGases.aQ ℓ j Φ (Function.update (Function.update x₀ i y) j z)) ^ 2) := by
    rw [Submission.BoseGases.cnPlus, Fin.sum_univ_two]
    have hA : (∫ u in Submission.BoseGases.abox 2 ℓ,
          (Submission.BoseGases.aQ ℓ 0 (pairFibre x₀ i j Φ) u) ^ 2)
        = ∫ u in Submission.BoseGases.abox 2 ℓ,
            (Submission.BoseGases.aQ ℓ i Φ (pairUpd x₀ i j u)) ^ 2 := by
      refine MeasureTheory.setIntegral_congr_ae (Submission.BoseGases.abox_measurable 2 ℓ) ?_
      filter_upwards with u _
      rw [aQ_zero_pairFibre hij Φ x₀ u]
    have hB : (∫ u in Submission.BoseGases.abox 2 ℓ,
          (Submission.BoseGases.aQ ℓ 1 (pairFibre x₀ i j Φ) u) ^ 2)
        = ∫ u in Submission.BoseGases.abox 2 ℓ,
            (Submission.BoseGases.aQ ℓ j Φ (pairUpd x₀ i j u)) ^ 2 := by
      refine MeasureTheory.setIntegral_congr_ae (Submission.BoseGases.abox_measurable 2 ℓ) ?_
      filter_upwards with u _
      rw [aQ_one_pairFibre hij Φ x₀ u]
    have hAint : MeasureTheory.IntegrableOn
        (fun u : Submission.BoseGases.X 2 => (Submission.BoseGases.aQ ℓ i Φ (pairUpd x₀ i j u)) ^ 2)
        (Submission.BoseGases.abox 2 ℓ) MeasureTheory.volume :=
      (((Submission.BoseGases.aQ_continuous hℓ i hΦc).comp (pairUpd_continuous x₀ i j)).pow 2).continuousOn
        |>.integrableOn_compact (Submission.BoseGases.abox_compact 2 hℓ)
    have hBint : MeasureTheory.IntegrableOn
        (fun u : Submission.BoseGases.X 2 => (Submission.BoseGases.aQ ℓ j Φ (pairUpd x₀ i j u)) ^ 2)
        (Submission.BoseGases.abox 2 ℓ) MeasureTheory.volume :=
      (((Submission.BoseGases.aQ_continuous hℓ j hΦc).comp (pairUpd_continuous x₀ i j)).pow 2).continuousOn
        |>.integrableOn_compact (Submission.BoseGases.abox_compact 2 hℓ)
    have hFint : MeasureTheory.IntegrableOn
        (fun u : Submission.BoseGases.X 2 =>
          (fun a b : E3 =>
            (Submission.BoseGases.aQ ℓ i Φ (Function.update (Function.update x₀ i a) j b)) ^ 2
              + (Submission.BoseGases.aQ ℓ j Φ (Function.update (Function.update x₀ i a) j b)) ^ 2)
            (u 0) (u 1))
        (Submission.BoseGases.abox 2 ℓ) MeasureTheory.volume := by
      have hcont : Continuous (fun u : Submission.BoseGases.X 2 =>
          (Submission.BoseGases.aQ ℓ i Φ (pairUpd x₀ i j u)) ^ 2
            + (Submission.BoseGases.aQ ℓ j Φ (pairUpd x₀ i j u)) ^ 2) :=
        (((Submission.BoseGases.aQ_continuous hℓ i hΦc).comp (pairUpd_continuous x₀ i j)).pow 2).add
          (((Submission.BoseGases.aQ_continuous hℓ j hΦc).comp (pairUpd_continuous x₀ i j)).pow 2)
      exact hcont.continuousOn.integrableOn_compact (Submission.BoseGases.abox_compact 2 hℓ)
    rw [hA, hB, ← MeasureTheory.integral_add hAint hBint]
    have hpeel : (∫ u in Submission.BoseGases.abox 2 ℓ,
          ((Submission.BoseGases.aQ ℓ i Φ (pairUpd x₀ i j u)) ^ 2
            + (Submission.BoseGases.aQ ℓ j Φ (pairUpd x₀ i j u)) ^ 2))
        = ∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
          ((Submission.BoseGases.aQ ℓ i Φ (Function.update (Function.update x₀ i y) j z)) ^ 2
            + (Submission.BoseGases.aQ ℓ j Φ (Function.update (Function.update x₀ i y) j z)) ^ 2) :=
      abox2_peel (ℓ := ℓ) (F := fun a b : E3 =>
        (Submission.BoseGases.aQ ℓ i Φ (Function.update (Function.update x₀ i a) j b)) ^ 2
          + (Submission.BoseGases.aQ ℓ j Φ (Function.update (Function.update x₀ i a) j b)) ^ 2) hFint
    rw [hpeel]
  -- ## assembly
  have hmain := hC₂ ℓ hℓ hRℓ hΨc
  rw [hLHS, hQ4, hCN] at hmain
  exact hmain



/-- **The comparison between the sharp (additive) form and the as-written (inner) form.**  With
`F := (q4B_{ij})²·w`, `G := (Q_iΦ)² + (Q_jΦ)²`, `A := ∬F`, `B := ∬G` and
`I := ∬(F + (ℓ²)⁻¹·B)` (iterated integrals over `acube ℓ` at the fibre configuration), one has

  `2·A + (ℓ²)⁻¹·B ≤ (2 + ((R/chiR0)⁶)⁻¹)·I`.

Indeed `I ≥ A` and `I ≥ ∬(ℓ²)⁻¹B = (ℓ²)⁻¹B·ℓ⁶ = ℓ⁴B` (monotonicity of the box integral, the
constant integral computed with `abox_volume`), whence `(ℓ²)⁻¹B ≤ ℓ⁻⁶·I ≤ ((R/chiR0)⁶)⁻¹·I`
because `ℓ ≥ R/chiR0`.  No additive splitting of the iterated integral is used: only the two
pointwise monotonicity inequalities. -/
private theorem fibre_split_le {v : E3 → ℝ} (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1 MeasureTheory.volume)
    (R : ℝ) (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hav : 0 < BoseGases.a v)
    (h : ∃ w : E3 → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) (x₀ : Submission.BoseGases.X n) :
    2 * (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i y) j z)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 y z)
      + (ℓ ^ 2)⁻¹ * (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, (Submission.BoseGases.aQ ℓ i Φ (Function.update (Function.update x₀ i y) j z)) ^ 2 + (Submission.BoseGases.aQ ℓ j Φ (Function.update (Function.update x₀ i y) j z)) ^ 2)
    ≤ (2 + ((R / Submission.BoseGases.chiR0) ^ 6)⁻¹)
        * (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
            ((Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i y) j z)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 y z
              + (ℓ ^ 2)⁻¹ * (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, (Submission.BoseGases.aQ ℓ i Φ (Function.update (Function.update x₀ i y) j z)) ^ 2 + (Submission.BoseGases.aQ ℓ j Φ (Function.update (Function.update x₀ i y) j z)) ^ 2))) := by
  classical
  have hv_int : MeasureTheory.Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
  have hsuppv : ∀ z : E3, R ≤ ‖z‖ → v z = 0 := fun z hz =>
    Submission.BoseGases.v_eq_zero_of_norm_ge hv_supp hz
  have hΨc : Continuous (pairFibre x₀ i j Φ) := pairFibre_continuous hΦc
  have hFint0 : MeasureTheory.IntegrableOn
      (fun u : Submission.BoseGases.X 2 =>
        (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h))
            (pairFibre x₀ i j Φ) (0, 1) u) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (u 0) (u 1))
      (Submission.BoseGases.abox 2 ℓ) MeasureTheory.volume := by
    obtain ⟨-, hmeas01, B0, hB00, hbnd01⟩ :=
      ae_bounded_q4B_abox hv hvrad R hR hv_supp hav h (ℓ := ℓ) hℓ
        (Φ := pairFibre x₀ i j Φ) hΨc (p := (0, 1)) (by decide)
    exact integrableOn_sq_mul_wLoc hℓ hv_int hsuppv hRℓ (p := (0, 1)) (by decide)
      hmeas01 hB00 hbnd01
  have hFint : MeasureTheory.IntegrableOn
      (fun u : Submission.BoseGases.X 2 => (fun a b : E3 => (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i a) j b)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 a b) (u 0) (u 1))
      (Submission.BoseGases.abox 2 ℓ) MeasureTheory.volume :=
    hFint0.congr_fun (fun u _ => by
      show (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h))
              (pairFibre x₀ i j Φ) (0, 1) u) ^ 2
            * Submission.BoseGases.wLoc ℓ v 0 (u 0) (u 1)
          = (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h))
              Φ (i, j) (Function.update (Function.update x₀ i (u 0)) j (u 1))) ^ 2
            * Submission.BoseGases.wLoc ℓ v 0 (u 0) (u 1)
      rw [q4B_pairFibre_zero_one hij (Submission.BoseGases.omC (Classical.choose h)) Φ x₀ u]
      rfl)
      (Submission.BoseGases.abox_measurable 2 ℓ)
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.abox_lt_top 2 ℓ hℓ.le⟩
  set B : ℝ := (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, (Submission.BoseGases.aQ ℓ i Φ (Function.update (Function.update x₀ i y) j z)) ^ 2 + (Submission.BoseGases.aQ ℓ j Φ (Function.update (Function.update x₀ i y) j z)) ^ 2) with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    refine MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall (fun y => ?_))
    refine MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall (fun z => ?_))
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  set c : ℝ := (ℓ ^ 2)⁻¹ * B with hcdef
  have hc_nn : 0 ≤ c := mul_nonneg (by positivity) hBnn
  have hcint : MeasureTheory.IntegrableOn (fun _ : Submission.BoseGases.X 2 => c)
      (Submission.BoseGases.abox 2 ℓ) MeasureTheory.volume := MeasureTheory.integrable_const c
  have hGint : MeasureTheory.IntegrableOn
      (fun u : Submission.BoseGases.X 2 => (fun a b : E3 => (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i a) j b)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 a b + c) (u 0) (u 1))
      (Submission.BoseGases.abox 2 ℓ) MeasureTheory.volume := hFint.add hcint
  have hpeelF : (∫ u in Submission.BoseGases.abox 2 ℓ,
        (fun a b : E3 => (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i a) j b)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 a b) (u 0) (u 1))
      = ∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i y) j z)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 y z :=
    abox2_peel (ℓ := ℓ) (F := fun a b : E3 => (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i a) j b)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 a b) hFint
  have hpeelG : (∫ u in Submission.BoseGases.abox 2 ℓ,
        (fun a b : E3 => (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i a) j b)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 a b + c) (u 0) (u 1))
      = ∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, ((Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i y) j z)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 y z + c) :=
    abox2_peel (ℓ := ℓ) (F := fun a b : E3 => (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i a) j b)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 a b + c) hGint
  have hcval : (∫ _u in Submission.BoseGases.abox 2 ℓ, c) = c * ℓ ^ 6 := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
      Submission.BoseGases.abox_volume 2 ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity),
      smul_eq_mul]
    ring
  have hIexpr : (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, ((Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i y) j z)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 y z + c))
      = (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
          ((Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i y) j z)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 y z + (ℓ ^ 2)⁻¹ * B)) := rfl
  have hA_le : (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i y) j z)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 y z)
      ≤ (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, ((Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i y) j z)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 y z + c)) := by
    rw [← hpeelF, ← hpeelG]
    refine MeasureTheory.integral_mono hFint hGint (fun u => ?_)
    show (fun a b : E3 => (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i a) j b)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 a b) (u 0) (u 1)
        ≤ (fun a b : E3 => (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i a) j b)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 a b + c) (u 0) (u 1)
    linarith [hc_nn]
  have hc_le : c * ℓ ^ 6 ≤ (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, ((Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i y) j z)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 y z + c)) := by
    rw [← hcval, ← hpeelG]
    refine MeasureTheory.integral_mono hcint hGint (fun u => ?_)
    show c ≤ (fun a b : E3 => (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i a) j b)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 a b + c) (u 0) (u 1)
    have hz : 0 ≤ (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h))
        Φ (i, j) (Function.update (Function.update x₀ i (u 0)) j (u 1))) ^ 2
        * Submission.BoseGases.wLoc ℓ v 0 (u 0) (u 1) :=
      mul_nonneg (sq_nonneg _) (Work.BoseFixR.wLoc_zero_nonneg hv ℓ (u 0) (u 1))
    linarith [hz]
  have hℓmin : R / Submission.BoseGases.chiR0 ≤ ℓ := by
    rw [div_le_iff₀ Submission.BoseGases.chiR0_pos]
    simpa [mul_comm] using hRℓ
  have hA0 : 0 ≤ (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i y) j z)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 y z) := by
    refine MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall (fun y => ?_))
    refine MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall (fun z => ?_))
    exact mul_nonneg (sq_nonneg _) (Work.BoseFixR.wLoc_zero_nonneg hv ℓ y z)
  have hI0 : 0 ≤ (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, ((Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i y) j z)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 y z + c)) := le_trans hA0 hA_le
  have hrc : 0 < R / Submission.BoseGases.chiR0 :=
    div_pos hR Submission.BoseGases.chiR0_pos
  have hpow : (ℓ ^ 6)⁻¹ ≤ ((R / Submission.BoseGases.chiR0) ^ 6)⁻¹ := by
    rw [inv_le_inv₀ (pow_pos hℓ 6) (pow_pos hrc 6)]
    exact pow_le_pow_left₀ hrc.le hℓmin 6
  have hcle : c ≤ (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, ((Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i y) j z)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 y z + c))
      * ((R / Submission.BoseGases.chiR0) ^ 6)⁻¹ := by
    have h1 : c = (c * ℓ ^ 6) * (ℓ ^ 6)⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero 6 (ne_of_gt hℓ)), mul_one]
    calc c = (c * ℓ ^ 6) * (ℓ ^ 6)⁻¹ := h1
      _ ≤ (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, ((Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i y) j z)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 y z + c)) * (ℓ ^ 6)⁻¹ :=
          mul_le_mul_of_nonneg_right hc_le (inv_nonneg.mpr (pow_nonneg hℓ.le 6))
      _ ≤ (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, ((Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i y) j z)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 y z + c))
            * ((R / Submission.BoseGases.chiR0) ^ 6)⁻¹ :=
          mul_le_mul_of_nonneg_left hpow hI0
  linarith [hA_le, hcle]

/-- **The fibre bound in the additive ("outer") form** — the statement intended by the design
note `DESIGN_ppMass_le_q4mass_cnPlus.md` §14.1 (see the parse warning in the module docstring):
the fluctuation term `(ℓ²)⁻¹·∬((Q_iΦ)² + (Q_jΦ)²)` is added to `2·∬(q4B)²w` *outside* the
double integrals. -/
theorem ppMass_fibre_le_outer {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1 MeasureTheory.volume)
    (R : ℝ) (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hav : 0 < BoseGases.a v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℝ), 0 < ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
      ∀ (n : ℕ) (i j : Fin n), i ≠ j → ∀ {Φ : Submission.BoseGases.X n → ℝ}, Continuous Φ →
      ∀ x : Submission.BoseGases.X n,
      2 * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x) ^ 2
        ≤ C * (2 * (∫ y in Submission.BoseGases.acube ℓ,
                ∫ z in Submission.BoseGases.acube ℓ,
                (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h))
                    Φ (i, j) (Function.update (Function.update x i y) j z)) ^ 2
                  * Submission.BoseGases.wLoc ℓ v 0 y z)
            + (ℓ ^ 2)⁻¹ * (∫ y in Submission.BoseGases.acube ℓ,
                ∫ z in Submission.BoseGases.acube ℓ,
                  (Submission.BoseGases.aQ ℓ i Φ
                      (Function.update (Function.update x i y) j z)) ^ 2
                + (Submission.BoseGases.aQ ℓ j Φ
                      (Function.update (Function.update x i y) j z)) ^ 2)) :=
  fibre_core hv hvrad hv1 R hR hv_supp hav h

theorem ppMass_fibre_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1 MeasureTheory.volume)
    (R : ℝ) (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hav : 0 < BoseGases.a v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℝ), 0 < ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
      ∀ (n : ℕ) (i j : Fin n), i ≠ j → ∀ {Φ : Submission.BoseGases.X n → ℝ}, Continuous Φ →
      ∀ x : Submission.BoseGases.X n,
      2 * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x) ^ 2
        ≤ C * (2 * ∫ y in Submission.BoseGases.acube ℓ,
              ∫ z in Submission.BoseGases.acube ℓ,
                (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h))
                    Φ (i, j) (Function.update (Function.update x i y) j z)) ^ 2
                  * Submission.BoseGases.wLoc ℓ v 0 y z
            + (ℓ ^ 2)⁻¹ * (∫ y in Submission.BoseGases.acube ℓ,
                ∫ z in Submission.BoseGases.acube ℓ,
                  (Submission.BoseGases.aQ ℓ i Φ
                      (Function.update (Function.update x i y) j z)) ^ 2
                + (Submission.BoseGases.aQ ℓ j Φ
                      (Function.update (Function.update x i y) j z)) ^ 2)) := by
  classical
  obtain ⟨C₀, hC₀0, hC₀⟩ := fibre_core hv hvrad hv1 R hR hv_supp hav h
  refine ⟨C₀ * (2 + ((R / Submission.BoseGases.chiR0) ^ 6)⁻¹),
    mul_nonneg hC₀0 (by positivity), ?_⟩
  intro ℓ hℓ hRℓ n i j hij Φ hΦc x₀
  have hsharp := hC₀ ℓ hℓ hRℓ n i j hij hΦc x₀
  have hcomp := fibre_split_le hv hvrad hv1 R hR hv_supp hav h hℓ hRℓ hij hΦc x₀
  have hI0 : 0 ≤ (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, ((Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i y) j z)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 y z + (ℓ ^ 2)⁻¹ * (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, (Submission.BoseGases.aQ ℓ i Φ (Function.update (Function.update x₀ i y) j z)) ^ 2 + (Submission.BoseGases.aQ ℓ j Φ (Function.update (Function.update x₀ i y) j z)) ^ 2))) := by
    refine MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall (fun y => ?_))
    refine MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall (fun z => ?_))
    refine add_nonneg (mul_nonneg (sq_nonneg _) (Work.BoseFixR.wLoc_zero_nonneg hv ℓ y z)) ?_
    refine mul_nonneg (by positivity) ?_
    refine MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall (fun y' => ?_))
    refine MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall (fun z' => ?_))
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hmain : 2 * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x₀) ^ 2
      ≤ (C₀ * (2 + ((R / Submission.BoseGases.chiR0) ^ 6)⁻¹))
        * (2 * (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, ((Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i y) j z)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 y z + (ℓ ^ 2)⁻¹ * (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, (Submission.BoseGases.aQ ℓ i Φ (Function.update (Function.update x₀ i y) j z)) ^ 2 + (Submission.BoseGases.aQ ℓ j Φ (Function.update (Function.update x₀ i y) j z)) ^ 2)))) := by
    calc 2 * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x₀) ^ 2
        ≤ C₀ * (2 * (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i y) j z)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 y z) + (ℓ ^ 2)⁻¹ * (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, (Submission.BoseGases.aQ ℓ i Φ (Function.update (Function.update x₀ i y) j z)) ^ 2 + (Submission.BoseGases.aQ ℓ j Φ (Function.update (Function.update x₀ i y) j z)) ^ 2)) := hsharp
      _ ≤ C₀ * ((2 + ((R / Submission.BoseGases.chiR0) ^ 6)⁻¹)
            * (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, ((Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i y) j z)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 y z + (ℓ ^ 2)⁻¹ * (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, (Submission.BoseGases.aQ ℓ i Φ (Function.update (Function.update x₀ i y) j z)) ^ 2 + (Submission.BoseGases.aQ ℓ j Φ (Function.update (Function.update x₀ i y) j z)) ^ 2)))) :=
          mul_le_mul_of_nonneg_left hcomp hC₀0
      _ ≤ (C₀ * (2 + ((R / Submission.BoseGases.chiR0) ^ 6)⁻¹))
            * (2 * (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, ((Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (Function.update (Function.update x₀ i y) j z)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 y z + (ℓ ^ 2)⁻¹ * (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, (Submission.BoseGases.aQ ℓ i Φ (Function.update (Function.update x₀ i y) j z)) ^ 2 + (Submission.BoseGases.aQ ℓ j Φ (Function.update (Function.update x₀ i y) j z)) ^ 2)))) := by
          nlinarith [hC₀0, hI0,
            (by positivity : (0:ℝ) ≤ 2 + ((R / Submission.BoseGases.chiR0) ^ 6)⁻¹)]
  exact hmain

end Work.BoseFixB3.CS.Pieces
