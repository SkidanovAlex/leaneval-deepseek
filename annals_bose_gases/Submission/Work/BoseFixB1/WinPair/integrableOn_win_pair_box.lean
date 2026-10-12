import ChallengeDeps
import Submission.Work.BoseFixB1.WinPair.WinChiFacts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WinPair.integrableOn_win_pair_box`

The **box integrability of the windowed pair integrand**: for a smooth general window `χ`,
a smooth `Ψ`, distinct slots `i ≠ j` and the dilute regime `R ≤ s·chiR0`,

`x ↦ (PᵢPⱼΨ)(x)·(QⱼQᵢΨ)(x)·(χ_B(xᵢ)·W₁(xᵢ−xⱼ)·χ_B(xⱼ))`

is integrable on the analysis box `abox (N+2) s`, where `χ_B = winChi s χ` is the
box-restricted window (`WinPair.Defs`) and `W₁ = wScaled s (g₀ v h)` is the
χ-renormalised scattering kernel.

This is the general-window counterpart of `SmallBoxPairRelDecomp.q4_pair_integrable` (which
treats `χ = chiScale s`, where the window is automatically confined to the box): the proof is
the same domination argument

  `|χ_B(xᵢ)|·|W₁(xᵢ−xⱼ)|·|χ_B(xⱼ)| ≤ Cχ · 2·|g₀(xᵢ−xⱼ)| · Cχ`

(with `Cχ` the sup of the window on the compact box, `WinChiFacts.exists_abs_winChi_le`, and
`|W₁| ≤ 2|g₀|` from the dilute regime, `KernelMean.wScaled_abs_le_two`), so that the majorant
is a constant times `|g₀(xᵢ−xⱼ)|`, which is `L¹` over the box
(`WordInteg.integrableOn_abs_sub_abox`).

The one genuinely new ingredient is the **a.e. measurability of `x ↦ f (xᵢ − xⱼ)`** for a
merely a.e.-measurable `f` (as `g₀` is: it is only `L¹_loc`, not assumed measurable).  This is
provided here by

* `quasiMeasurePreserving_pair_sub`: the pair map `x ↦ xᵢ − xⱼ` pushes
  `volume.restrict (abox N ℓ)` to a measure absolutely continuous w.r.t. Lebesgue measure
  (a null set in `ℝ³` is pulled back to a null set of the box — `WordInteg.abox_null_preimage_pair`),
* `aemeasurable_comp_pair`: hence a.e.-measurable functions compose with it.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.WinPair

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The pair map is quasi-measure-preserving -/

/-- **The relative-coordinate map `x ↦ xᵢ − xⱼ` is quasi-measure-preserving** from the box
`abox N ℓ` (with Lebesgue measure) to `ℝ³`.  A (Lebesgue) null set is pulled back to a null
set of the box by `WordInteg.abox_null_preimage_pair`; for a non-measurable null set pass to a
measurable null superset. -/
lemma quasiMeasurePreserving_pair_sub {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (i j : Fin N) (hij : i ≠ j) :
    Measure.QuasiMeasurePreserving (fun x : X N => x i - x j)
      ((volume : Measure (X N)).restrict (abox N ℓ)) volume := by
  have hf : Measurable (fun x : X N => x i - x j) := by fun_prop
  refine ⟨hf, ?_⟩
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hs hμ
  rw [Measure.map_apply hf hs]
  exact abox_null_preimage_pair hℓ hs hμ i j hij

/-- **A.e.-measurable functions compose with the relative-coordinate map.**  If
`f : ℝ³ → ℝ` is a.e. strongly measurable for Lebesgue measure then `x ↦ f (xᵢ − xⱼ)` is
a.e. strongly measurable on the box `abox N ℓ`. -/
lemma aemeasurable_comp_pair {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 → ℝ}
    (hf : AEMeasurable f (volume : Measure E3)) (i j : Fin N) (hij : i ≠ j) :
    AEMeasurable (fun x : X N => f (x i - x j))
      ((volume : Measure (X N)).restrict (abox N ℓ)) := by
  have h := hf.comp_quasiMeasurePreserving (quasiMeasurePreserving_pair_sub hℓ i j hij)
  simpa [Function.comp_def] using h

/-! ## The target -/

theorem integrableOn_win_pair_box {N : ℕ} {s R : ℝ} (hs : 0 < s) (hR : 0 < R)
    (hRs : R ≤ s * Submission.BoseGases.chiR0) {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : ContDiff ℝ (⊤ : ℕ∞) χ)
    {Ψ : Submission.BoseGases.X (N + 2) → ℝ} (hΨc : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (i j : Fin (N + 2)) (hij : i ≠ j) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (N + 2) =>
      (Submission.BoseGases.aP s i (Submission.BoseGases.aP s j Ψ) x)
        * (Submission.BoseGases.aQ s j (Submission.BoseGases.aQ s i Ψ) x)
        * (Work.BoseFixB1.winChi s χ (x i)
            * Submission.BoseGases.wScaled s (Submission.BoseGases.g0 v h) (x i - x j)
            * Work.BoseFixB1.winChi s χ (x j)))
      (Submission.BoseGases.abox (N + 2) s) MeasureTheory.volume := by
  have hχc' : Continuous χ := hχc.continuous
  have hΨc' : Continuous Ψ := hΨc.continuous
  -- the numerator `g₀` is `L¹`, supported in `ball 0 R`
  have hg_int : Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hg_supp : ∀ z : E3, R ≤ ‖z‖ → g0 v h z = 0 :=
    fun z hz => g0_zero_of_norm_ge hv_supp hz h
  -- the window and `Ψ` are bounded on the box
  obtain ⟨Cχ, hCχ0, hCχ⟩ := exists_abs_winChi_le hs hχc'
  obtain ⟨B, hB0, hBΨ⟩ := exists_abox_bound hs hΨc'
  have hP : ∀ x ∈ abox (N + 2) s, |aP s i (aP s j Ψ) x| ≤ B := fun x hx =>
    aP_abs_le hs i (aP_continuous hs j hΨc') hB0
      (fun y hy => aP_abs_le hs j hΨc' hB0 hBΨ y hy) x hx
  have hQ : ∀ x ∈ abox (N + 2) s, |aQ s j (aQ s i Ψ) x| ≤ 4 * B :=
    aQ_pair_abs_le hs i j hΨc' hB0 hBΨ
  -- the renormalised kernel is dominated by twice its numerator
  have hWb : ∀ z : E3, |wScaled s (g0 v h) z| ≤ 2 * |g0 v h z| :=
    fun z => wScaled_abs_le_two hs hR.le hRs hg_supp z
  -- the majorant is a constant times `|g₀(xᵢ − xⱼ)|`, integrable over the box
  set K : ℝ := (B * (4 * B)) * (Cχ * (2 * Cχ)) with hKdef
  have hbase : IntegrableOn (fun x : X (N + 2) => |g0 v h (x i - x j)|)
      (abox (N + 2) s) volume := integrableOn_abs_sub_abox hs hg_int i j hij
  have hmaj : Integrable (fun x : X (N + 2) => K * |g0 v h (x i - x j)|)
      ((volume : Measure (X (N + 2))).restrict (abox (N + 2) s)) :=
    hbase.integrable.const_mul K
  -- measurability of the integrand
  have hw : AEMeasurable (wScaled s (g0 v h)) (volume : Measure E3) := by
    have h0 : AEMeasurable (fun z : E3 => g0 v h z / convScale s z) (volume : Measure E3) :=
      hg_int.aemeasurable.div (convScale_continuous s).aemeasurable
    have hw_eq : (wScaled s (g0 v h)) = fun z : E3 => g0 v h z / convScale s z := rfl
    rw [hw_eq]
    exact h0
  have hW_aesm : AEStronglyMeasurable
      (fun x : X (N + 2) => wScaled s (g0 v h) (x i - x j))
      ((volume : Measure (X (N + 2))).restrict (abox (N + 2) s)) :=
    (aemeasurable_comp_pair hs hw i j hij).aestronglyMeasurable
  have hA_aesm : AEStronglyMeasurable
      (fun x : X (N + 2) => aP s i (aP s j Ψ) x)
      ((volume : Measure (X (N + 2))).restrict (abox (N + 2) s)) :=
    (aP_continuous hs i (aP_continuous hs j hΨc')).aestronglyMeasurable
  have hQ_aesm : AEStronglyMeasurable
      (fun x : X (N + 2) => aQ s j (aQ s i Ψ) x)
      ((volume : Measure (X (N + 2))).restrict (abox (N + 2) s)) :=
    (aQ_continuous hs j (aQ_continuous hs i hΨc')).aestronglyMeasurable
  have hCi_aesm : AEStronglyMeasurable (fun x : X (N + 2) => winChi s χ (x i))
      ((volume : Measure (X (N + 2))).restrict (abox (N + 2) s)) :=
    ((measurable_winChi hχc'.measurable).comp (measurable_pi_apply i)).aestronglyMeasurable
  have hCj_aesm : AEStronglyMeasurable (fun x : X (N + 2) => winChi s χ (x j))
      ((volume : Measure (X (N + 2))).restrict (abox (N + 2) s)) :=
    ((measurable_winChi hχc'.measurable).comp (measurable_pi_apply j)).aestronglyMeasurable
  refine Integrable.mono' hmaj ((hA_aesm.mul hQ_aesm).mul ((hCi_aesm.mul hW_aesm).mul hCj_aesm)) ?_
  filter_upwards [ae_restrict_mem (abox_measurable (N + 2) s)] with x hx
  have h1 : |aP s i (aP s j Ψ) x| ≤ B := hP x hx
  have h2 : |aQ s j (aQ s i Ψ) x| ≤ 4 * B := hQ x hx
  have h3 : |winChi s χ (x i)| ≤ Cχ := hCχ (x i)
  have h4 : |wScaled s (g0 v h) (x i - x j)| ≤ 2 * |g0 v h (x i - x j)| := hWb _
  have h5 : |winChi s χ (x j)| ≤ Cχ := hCχ (x j)
  have h4nn : (0 : ℝ) ≤ 2 * |g0 v h (x i - x j)| := by positivity
  have hBnn : (0 : ℝ) ≤ B := hB0
  have h4Bnn : (0 : ℝ) ≤ 4 * B := by positivity
  simp only [Real.norm_eq_abs, abs_mul]
  have hinner : |winChi s χ (x i)| * |wScaled s (g0 v h) (x i - x j)| * |winChi s χ (x j)|
      ≤ Cχ * (2 * |g0 v h (x i - x j)|) * Cχ :=
    mul_le_mul (mul_le_mul h3 h4 (abs_nonneg _) hCχ0) h5 (abs_nonneg _)
      (mul_nonneg hCχ0 h4nn)
  have houter : |aP s i (aP s j Ψ) x| * |aQ s j (aQ s i Ψ) x| ≤ B * (4 * B) :=
    mul_le_mul h1 h2 (abs_nonneg _) hBnn
  calc |aP s i (aP s j Ψ) x| * |aQ s j (aQ s i Ψ) x|
        * (|winChi s χ (x i)| * |wScaled s (g0 v h) (x i - x j)| * |winChi s χ (x j)|)
      ≤ B * (4 * B) * (Cχ * (2 * |g0 v h (x i - x j)|) * Cχ) :=
        mul_le_mul houter hinner (by positivity) (mul_nonneg hBnn h4Bnn)
    _ = K * |g0 v h (x i - x j)| := by rw [hKdef]; ring

end Work.BoseFixB1.WinPair
