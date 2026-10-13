/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/XBallLimAux/MajorantIntegrable.lean`

**Integrability of the majorant `G ∘ thShift` on `Iθ × [-ε,ε]`** — a copy of
`Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.MajorantIntegrable` (which is complete but rests
on the `sorry`-stub `FstarJepsSmoothAux.ThShiftPreimageNull`) in which that gap is replaced by the
proved lemma `XBallLimAux.thShift_null_preimage`.  This is the *only* modification: the
dependency cone of `XBallLimAux.MajorantIntegrable` below this point is `sorry`-free.

It is consumed by the cloned `XBallLimAux.FstarJepsSmooth`/`XBallLimAux.FstarPzJepsSmooth`, which
supply the `fsm` input of the class-`C` clause of the limit slice in
`Submission/Work/FTS/StrongEps/EpsE4Thr/XBallLimExists.lean`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ThShiftSubst
import Submission.Work.FTS.StrongEps.JepsHkMem.lintegral_thShift_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ThShiftAEMeasurable
import Submission.Work.FTS.StrongEps.EpsE4Thr.XBallLimAux.ThShiftNullPreimage
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.LintegralProdThShiftLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the majorant `G ∘ thShift` on `Iθ × [-ε,ε]`

For the smoothness of `Fstar (Jeps ρ ε W)` in the log-coordinate scheme one needs that an
angular majorant `G`, merely *integrable* on `(0,π/2)` (not measurable in any stronger sense),
can be pushed through the angular shift `thShift θ p = arctan (tan θ · e^{-p})`:

  `(θ,p) ↦ G (thShift θ p)` and `(θ,p) ↦ sin θ cos²θ · G (thShift θ p)`

are integrable for the product measure `(volume.restrict Iθ).prod (volume.restrict (Icc (-ε) ε))`,
`Iθ = [0,π/2]`.

## The route

`G` is integrable on `(0,π/2)`, hence *a.e.* strongly measurable there: take a strongly measurable
representative `G'` (`AEStronglyMeasurable` is by definition the existence of such a
representative).  Then

* `G'` is strongly measurable, integrable on `(0,π/2)` and equals `G` a.e. there — the first
  three conjuncts;
* `G' ∘ thShift` is integrable: its a.e. measurability comes from `G'` measurable together with
  the a.e. measurability of the shift (`aemeasurable_thShift_prod`), and the finiteness of the
  `lintegral` of its norm from the `θ`-substitution bound `JepsHkMem.lintegral_thShift_le`
  (which is *measurability free*) integrated against the finite `p`-measure
  (`LintegralProdThShiftLe`), applied to the measurable representative of `G'` — the passage
  between the two needs the null-preimage statement `thShift_null_preimage`
  (`ae_eq_comp_thShift`);
* multiplying by the bounded continuous factor `sinCos2` preserves integrability
  (`Integrable.mono'` with `‖sinCos2 θ‖ ≤ 1`);
* replacing `G'` by `G` inside the product is again the a.e. equality `G' ∘ thShift = G ∘ thShift`.

All the null sets involved (`Iθ \ (0,π/2)`, the preimage of a null set under `θ ↦ thShift θ p`)
are those of `ThShiftAEMeasurable` / `thShift_null_preimage`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.XBallLimAux

open Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Two reductions about the composition with the angular shift -/

/-- **A.e. equality is preserved by `thShift`.**  If `F = g` a.e. on `(0,π/2)`, then
`F ∘ thShift = g ∘ thShift` a.e. for the product measure on `Iθ × [-ε,ε]`: the shift maps a.e.
`(θ,p)` (namely those with `θ ∈ (0,π/2)`) into `(0,π/2)` (`thShift_mem`), and the preimage of a
null set is null (`thShift_null_preimage`). -/
theorem ae_eq_comp_thShift {ε : ℝ} (hε : 0 < ε) {F g : ℝ → ℝ}
    (h : F =ᵐ[volume.restrict (Set.Ioo 0 (π / 2))] g) :
    (fun x : ℝ × ℝ => F (Work.FTS.StrongEps.thShift x.1 x.2))
      =ᵐ[((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε)))]
      (fun x : ℝ × ℝ => g (Work.FTS.StrongEps.thShift x.1 x.2)) := by
  have hν0 : (volume.restrict (Set.Ioo 0 (π / 2))) {θ : ℝ | F θ ≠ g θ} = 0 :=
    ae_iff.mp h
  obtain ⟨Z, hZsub, hZmeas, hZ0'⟩ := exists_measurable_superset_of_null hν0
  have hZvol : (volume : Measure ℝ) (Z ∩ Set.Ioo 0 (π / 2)) = 0 := by
    rw [← Measure.restrict_apply hZmeas]
    exact hZ0'
  have hZn : ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε)))
      {x : ℝ × ℝ | Work.FTS.StrongEps.thShift x.1 x.2 ∈ Z ∩ Set.Ioo 0 (π / 2)} = 0 :=
    thShift_null_preimage hε (hZmeas.inter measurableSet_Ioo) hZvol
  have hA : ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε)))
      {x : ℝ × ℝ | x.1 ∉ Set.Ioo 0 (π / 2)} = 0 := by
    rw [show {x : ℝ × ℝ | x.1 ∉ Set.Ioo 0 (π / 2)}
        = (Set.Ioo 0 (π / 2))ᶜ ×ˢ (Set.univ : Set ℝ) from by ext x; simp]
    rw [Measure.prod_prod, measure_Iθ_compl_Ioo_eq_zero, zero_mul]
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null ?_ (measure_union_null hA hZn)
  intro x hx
  by_cases hxI : x.1 ∈ Set.Ioo 0 (π / 2)
  · right
    exact ⟨hZsub hx, Work.FTS.StrongEps.thShift_mem hxI⟩
  · exact Or.inl hxI

/-- **Integrability of `θ ↦ F (thShift θ p)` as a function of `(θ,p)`.**  For `F` integrable on
`(0,π/2)` the composite with the angular shift is integrable for the product measure on
`Iθ × [-ε,ε]`.

A.e. strong measurability: `F` has a strongly measurable representative `g` (a.e. measurable),
and `g ∘ thShift` is a.e. strongly measurable because `thShift` is a.e. (strongly) measurable
(`aemeasurable_thShift_prod`); the a.e. equality `F ∘ thShift = g ∘ thShift` is
`ae_eq_comp_thShift`.

Finiteness of the `lintegral` of the norm: replace `F` by `g` (a.e. equality), split `‖·‖ₑ` into
`ofReal |·|`, apply `LintegralProdThShiftLe` to `U θ = ofReal |g θ|`, and identify the remaining
`θ`-integral with `ofReal (∫_{(0,π/2)} |g|) < ∞` (`lintegral_Iθ_eq_Ioo`,
`ofReal_integral_eq_lintegral_ofReal`). -/
theorem integrable_comp_thShift {ε : ℝ} (hε : 0 < ε) {F : ℝ → ℝ}
    (hF : MeasureTheory.IntegrableOn F (Set.Ioo 0 (π / 2))) :
    MeasureTheory.Integrable (fun x : ℝ × ℝ => F (Work.FTS.StrongEps.thShift x.1 x.2))
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε))) := by
  obtain ⟨g, hgmeas, hgae⟩ := hF.aestronglyMeasurable.aemeasurable
  have hgint : MeasureTheory.IntegrableOn g (Set.Ioo 0 (π / 2)) := hF.congr hgae
  have haeeq := ae_eq_comp_thShift hε hgae
  refine ⟨?_, ?_⟩
  · exact ((hgmeas.comp_aemeasurable aemeasurable_thShift_prod).congr haeeq.symm).aestronglyMeasurable
  · have hmeas_abs : Measurable (fun θ : ℝ => ENNReal.ofReal |g θ|) :=
      ENNReal.measurable_ofReal.comp hgmeas.abs
    calc ∫⁻ x : ℝ × ℝ, ‖F (Work.FTS.StrongEps.thShift x.1 x.2)‖ₑ
            ∂((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε)))
        = ∫⁻ x : ℝ × ℝ, ENNReal.ofReal |F (Work.FTS.StrongEps.thShift x.1 x.2)|
            ∂((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε))) :=
          lintegral_congr fun x => by
            rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal]; norm_cast
      _ = ∫⁻ x : ℝ × ℝ, ENNReal.ofReal |g (Work.FTS.StrongEps.thShift x.1 x.2)|
            ∂((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε))) := by
          refine lintegral_congr_ae ?_
          filter_upwards [haeeq] with x hx
          rw [hx]
      _ ≤ ENNReal.ofReal (Real.exp (3 * ε) * (2 * ε)) *
            ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |g θ| :=
          LintegralProdThShiftLe hε hmeas_abs
      _ < ⊤ := by
          refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
          rw [lintegral_Iθ_eq_Ioo,
            ← ofReal_integral_eq_lintegral_ofReal hgint.abs
              (Filter.Eventually.of_forall fun θ => abs_nonneg (g θ))]
          exact ENNReal.ofReal_lt_top

/-! ## The target -/

theorem MajorantIntegrable {G : ℝ → ℝ} (hG : MeasureTheory.IntegrableOn G (Set.Ioo 0 (Real.pi / 2)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G' : ℝ → ℝ, MeasureTheory.StronglyMeasurable G' ∧ MeasureTheory.IntegrableOn G' (Set.Ioo 0 (Real.pi / 2)) ∧
      (∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))), G' θ = G θ) ∧
      MeasureTheory.Integrable (fun x : ℝ × ℝ => G' (Work.FTS.StrongEps.thShift x.1 x.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod (MeasureTheory.volume.restrict (Set.Icc (-ε) ε))) ∧
      MeasureTheory.Integrable (fun x : ℝ × ℝ => Work.Elliptic.sinCos2 x.1 * G' (Work.FTS.StrongEps.thShift x.1 x.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod (MeasureTheory.volume.restrict (Set.Icc (-ε) ε))) ∧
      MeasureTheory.Integrable (fun x : ℝ × ℝ => Work.Elliptic.sinCos2 x.1 * G (Work.FTS.StrongEps.thShift x.1 x.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod (MeasureTheory.volume.restrict (Set.Icc (-ε) ε))) := by
  obtain ⟨G', hG'sm, hG'ae⟩ := hG.aestronglyMeasurable
  have hG'int : MeasureTheory.IntegrableOn G' (Set.Ioo 0 (Real.pi / 2)) := hG.congr hG'ae
  have hcomp' : (fun x : ℝ × ℝ => G' (Work.FTS.StrongEps.thShift x.1 x.2))
      =ᵐ[((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε)))]
      (fun x : ℝ × ℝ => G (Work.FTS.StrongEps.thShift x.1 x.2)) :=
    (ae_eq_comp_thShift hε hG'ae).symm
  have h1 : MeasureTheory.Integrable (fun x : ℝ × ℝ => G' (Work.FTS.StrongEps.thShift x.1 x.2))
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε))) :=
    integrable_comp_thShift hε hG'int
  have hsinCos2_cont : Continuous (fun θ : ℝ => Work.Elliptic.sinCos2 θ) := by
    rw [show Work.Elliptic.sinCos2 = fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 from rfl]
    fun_prop
  have hsinCos2 : ∀ θ : ℝ, ‖Work.Elliptic.sinCos2 θ‖ ≤ 1 := by
    intro θ
    rw [Work.Elliptic.sinCos2, Real.norm_eq_abs, abs_mul]
    have hc : |Real.cos θ ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one θ)
    calc |Real.sin θ| * |Real.cos θ ^ 2| ≤ 1 * 1 :=
          mul_le_mul (Real.abs_sin_le_one θ) hc (abs_nonneg _) (by norm_num)
      _ = 1 := mul_one 1
  have h2 : MeasureTheory.Integrable
      (fun x : ℝ × ℝ => Work.Elliptic.sinCos2 x.1 * G' (Work.FTS.StrongEps.thShift x.1 x.2))
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε))) := by
    refine MeasureTheory.Integrable.mono' h1.norm ?_ ?_
    · exact (hsinCos2_cont.measurable.comp measurable_fst).aestronglyMeasurable.mul
        h1.aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      calc |Work.Elliptic.sinCos2 x.1| * |G' (Work.FTS.StrongEps.thShift x.1 x.2)|
          ≤ 1 * |G' (Work.FTS.StrongEps.thShift x.1 x.2)| :=
            mul_le_mul_of_nonneg_right (hsinCos2 x.1) (abs_nonneg _)
        _ = |G' (Work.FTS.StrongEps.thShift x.1 x.2)| := one_mul _
  refine ⟨G', hG'sm, hG'int, hG'ae.symm, h1, h2, h2.congr ?_⟩
  filter_upwards [hcomp'] with x hx
  rw [hx]

end Work.FTS.StrongEps.EpsE4Thr.XBallLimAux
