import Mathlib
import Submission.Work.FBif.MRMTInput
import Submission.Work.FBif.Defs
import Submission.Work.FBif.Liouville
import Submission.Work.FBif.tendsto_eLpNorm_top_zero_of_ae_bound
import Submission.Work.FBif.bounded_conj_of_decay
import Submission.Work.FBif.far_bound_of_decay
import Submission.Work.FBif.tendstoLocallyUniformly_symm_of_decay

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function MeasureTheory
open scoped Topology

noncomputable section

namespace Work.FBif

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The straightening follows from the gluing family and MRMT.**

Let `c` be a parameter with parabolic point `z₁`, `q` a perturbation, `δ' > 0` a cycle
neighbourhood radius and `R > 0` a far radius.  Suppose that for a sequence `ε_n → 0⁺` the gluing
datum `Work.FBif.GluingDatum c z₁ q δ' R (ε_n)` exists for every `n`.  Then the family
straightens in the sense of `Work.FBif.Straightening`: there are homeomorphisms `Φ_n` (and their
inverses) tending to the identity locally uniformly, and parameters `c_n → c`, with
`Φ_n ∘ f_{ε_n}^[5] = T_{c_n}^[5] ∘ Φ_n` on `ball z₁ δ'`.

Route.  Put `Φ_n := Work.MRMT.Found.principal (μ_n)` (`M1`; `μ_n` is the datum's coefficient).
By MRMT `M2″` (`Work.MRMT.Found.principal_conj_contDiff`, whose five hypotheses are exactly
`adm`, `contDiff`, `hS`, `hrev`, `hinv`) the map `G_n := Φ_n ∘ F_n ∘ Φ_n⁻¹` is entire
antiholomorphic; by `asymp` and `decay` (plus continuity of `G_n` on a compact set, for which no
quantitative input is needed) `G_n z - z̄²` is bounded, so Liouville
(`Work.FBif.antiholo_of_norm_sub_sq_bounded`) gives `G_n = T_{c_n}`.  Evaluating the far-field
asymptotics at a far point turns `c_n = G_n z - z̄²` into `‖c_n - c‖ ≤ K * C_n` with `C_n ≤ ε_n`,
hence `c_n → c`.  The conjugacy of the fifth iterates on `ball z₁ δ'` follows from `agree5` and
`Φ_n ∘ F_n = T_{c_n} ∘ Φ_n`.  `Φ_n → id` is MRMT `M6` (`Work.MRMT.Found.tendsto_principal`) —
note its hypotheses need a *uniform* bound `k < 1` and a *fixed* support radius `R`, both supplied
by `small`/`supp` after passing to the tail of the sequence on which `ε_n ≤ 1/2`.  Finally
`Φ_n⁻¹ → id` follows from the uniform far-field decay of `Φ_n` (`C_n ≤ ε_n → 0`), the compact
containment `Φ_n⁻¹ (closedBall 0 A) ⊆ closedBall 0 (rcRd R)`
(`Work.MRMT.Found.image_closedBall_subset_closedBall_of_decay`) and the local uniform convergence
of `Φ_n` on that compact ball. -/
theorem straightening_of_gluingFamily {c z₁ : ℂ} {q : ℂ → ℂ} {δ' R : ℝ} {εs : ℕ → ℝ}
    (hδ' : 0 < δ') (hR : 0 < R) (hεs : ∀ n : ℕ, 0 < εs n)
    (hε0 : Filter.Tendsto εs Filter.atTop (nhds 0))
    (h : ∀ n : ℕ, Work.FBif.GluingDatum c z₁ q δ' R (εs n)) :
    Work.FBif.Straightening c z₁ q := by
  -- the far radius, made `≥ 1`
  let R₀ : ℝ := max R 1
  have hR₀1 : 1 ≤ R₀ := le_max_right R 1
  have hRR₀ : R ≤ R₀ := le_max_left R 1
  -- pass to the tail of the sequence on which `εs n < 1/2`
  have hhalf_ev : ∀ᶠ n : ℕ in Filter.atTop, εs n < 1 / 2 :=
    hε0.eventually (eventually_lt_nhds (by norm_num))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hhalf_ev
  let εs' : ℕ → ℝ := fun n => εs (n + N)
  have hεs'_pos : ∀ n : ℕ, 0 < εs' n := fun n => hεs (n + N)
  have hεs'_half : ∀ n : ℕ, εs' n < 1 / 2 := fun n => hN (n + N) (Nat.le_add_left N n)
  have hεs'_tend : Filter.Tendsto εs' Filter.atTop (nhds 0) :=
    hε0.comp (Filter.tendsto_add_atTop_nat N)
  -- the gluing data along the tail
  let D : (n : ℕ) → Work.FBif.GluingDatum c z₁ q δ' R (εs' n) := fun n => h (n + N)
  -- the smallness and decay constants of the gluing data
  let k : ℕ → ℝ := fun n => Classical.choose (D n).small
  have hk_spec : ∀ n : ℕ, 0 ≤ k n ∧ k n ≤ εs' n ∧
      ∀ᵐ z ∂(volume : Measure ℂ), ‖(D n).μ z‖ ≤ k n :=
    fun n => Classical.choose_spec (D n).small
  let Cf : ℕ → ℝ := fun n => Classical.choose (D n).decay
  have hCf_spec : ∀ n : ℕ, 0 ≤ Cf n ∧ Cf n ≤ εs' n ∧
      ∀ z : ℂ, R ≤ ‖z‖ → ‖Work.MRMT.Found.principal ((D n).μ) z - z‖ ≤ Cf n / ‖z‖ :=
    fun n => Classical.choose_spec (D n).decay
  -- the principal solutions `Φ_n`
  let Φs : ℕ → ℂ ≃ₜ ℂ := fun n => Work.MRMT.Found.principal ((D n).μ)
  have hΦs_coe : ∀ n : ℕ, Φs n = Work.MRMT.Found.principal ((D n).μ) := fun n => rfl
  -- (M6) `Φ_n → id` locally uniformly
  have h0Lp : Filter.Tendsto (fun n => MeasureTheory.eLpNorm ((D n).μ) ⊤ (volume : Measure ℂ))
      Filter.atTop (nhds 0) :=
    tendsto_eLpNorm_top_zero_of_ae_bound (μs := fun n => (D n).μ) (εs := εs')
      (fun n => (D n).adm.meas) hεs'_tend
      (fun n => (hk_spec n).2.2.mono (fun z hz => le_trans hz (hk_spec n).2.1))
  have hΦtend : TendstoLocallyUniformly (fun n : ℕ => (Φs n : ℂ → ℂ)) id Filter.atTop :=
    Work.MRMT.Found.principal_tendsto (μs := fun n => (D n).μ) (hμ := fun n => (D n).adm)
      (R := R₀) (k := 1 / 2) (by norm_num)
      (fun n => fun _ hz => Metric.closedBall_subset_closedBall hRR₀ ((D n).supp hz))
      (fun n => (hk_spec n).2.2.mono (fun z hz => by
        have h1 : k n ≤ (1 : ℝ) / 2 := le_of_lt (lt_of_le_of_lt (hk_spec n).2.1 (hεs'_half n))
        linarith))
      h0Lp
  have hCf_tend : Filter.Tendsto Cf Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => (hCf_spec n).1) (fun n => (hCf_spec n).2.1) hεs'_tend
  -- `Φ_n⁻¹ → id` locally uniformly
  have hΦsymm : TendstoLocallyUniformly (fun n : ℕ => ((Φs n).symm : ℂ → ℂ)) id Filter.atTop :=
    tendstoLocallyUniformly_symm_of_decay (Φs := Φs) (Cs := Cf) (R := R₀) hR₀1
      (fun n => (hCf_spec n).1)
      (fun n z hz => (hCf_spec n).2.2 z (le_trans hRR₀ hz))
      hCf_tend hΦtend
  -- the Liouville step, one parameter `c_n` for each `n`
  have hliouville : ∀ n : ℕ, ∃ c' : ℂ,
      ∀ z : ℂ, Φs n ((D n).F ((Φs n).symm z)) = Tantibar c' z := by
    intro n
    refine antiholo_of_norm_sub_sq_bounded ?_ ?_
    · have h := Work.MRMT.Found.principal_conj_contDiff (hμ := (D n).adm) (f := (D n).F)
        (hf := (D n).contDiff) (hS := (D n).hS) (hrev := (D n).hrev) (hinv := (D n).hinv)
      exact h
    · exact bounded_conj_of_decay (c := c) (Φ := Φs n) (F := (D n).F) (R := R₀) (C := Cf n)
        hR₀1 (hCf_spec n).1 (D n).contDiff.continuous
        (fun z hz => (hCf_spec n).2.2 z (le_trans hRR₀ hz))
        (fun z hz => (D n).asymp z (le_trans hRR₀ hz))
  choose cs hcs using hliouville
  -- the parameters converge: `c_n → c`
  obtain ⟨T, hTnn, hT⟩ := far_bound_of_decay (R := R₀) hR₀1 c
  have hfar : ∀ n : ℕ, ‖cs n - c‖ ≤ 4 * Cf n := by
    intro n
    have hC1 : Cf n ≤ 1 := by
      have h1 := hεs'_half n
      have h2 := (hCf_spec n).2.1
      linarith
    have hb := hT (Cf n) (Φs n) ((D n).F) (hCf_spec n).1 hC1
      (fun z hz => (hCf_spec n).2.2 z (le_trans hRR₀ hz))
      (fun z hz => (D n).asymp z (le_trans hRR₀ hz))
      ((T : ℝ) : ℂ) (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hTnn])
    have h1 : Φs n ((D n).F ((Φs n).symm ((T : ℝ) : ℂ))) =
        (star ((T : ℝ) : ℂ)) ^ 2 + cs n := hcs n ((T : ℝ) : ℂ)
    have h2 : Φs n ((D n).F ((Φs n).symm ((T : ℝ) : ℂ))) - (star ((T : ℝ) : ℂ)) ^ 2 - c
        = cs n - c := by
      rw [h1]; ring
    rwa [← h2]
  have hcs_tend : Filter.Tendsto cs Filter.atTop (nhds c) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) hfar ?_
    simpa using hCf_tend.const_mul 4
  -- the conjugacy of the fifth iterates
  refine ⟨δ', hδ', εs', hεs'_pos, hεs'_tend, Φs, hΦtend, hΦsymm, cs, hcs_tend, ?_⟩
  intro n z hz
  have hconj : Conjugates (Φs n) ((D n).F) (Tantibar (cs n)) := by
    intro w
    have h := hcs n (Φs n w)
    rwa [Homeomorph.symm_apply_apply] at h
  have hiter := (Conjugates.iterate hconj 5) z
  rw [← (D n).agree5 z hz]
  exact hiter

end Work.FBif
