import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.SlotT2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The two-level Cauchy–Schwarz bound for a pair of canonical slots

The slot bound `Work.FTS.TransportS.SlotT2.slotCS` is *not* proved by the two-step
(`θ`-then-`z`) route described in its docstring, but by a strictly shorter one that uses
the pointwise slot domination of `Basic.lean` first and then a *single* level of
Cauchy–Schwarz (in `L²` of the product `z`-measure):

* `canonW q z θ · (X z θ)² ≤ HkIntegrand α 4 f z θ` for every slot `X` of `ℋ⁴` (this is
  `canonW_mul_z_le` for a pure `D_z`-slot and `canonW_mul_mixed_le` for a mixed slot);
* hence, pointwise on `Iθ`, `canonW q z θ |X| |Y| = √(canonW q z θ X²) · √(canonW q z θ Y²)
  ≤ √(HkIntegrand α 4 f z θ) · √(HkIntegrand α 4 g z θ)`;
* two applications of `cs_sqrt_le` (the square-root form of the `L²` Cauchy–Schwarz
  inequality on a set) then give

  `∫_z∫_θ canonW q |X| |Y| ≤ √(∫_z (∫_θ HkIntegrand α 4 f)) · √(∫_z (∫_θ HkIntegrand α 4 g))`,

  and the two factors are `HkSq α 4 f`, `HkSq α 4 g` by definition.  So the constant is
  `C = 1`, and none of the measurability bookkeeping of `Basic.lean` (beyond the
  integrability of the `θ`-slices and of the marginals, which is `HkMem`) is needed. -/

/-- **The square-root form of the Cauchy–Schwarz inequality on a set.**  For nonnegative
functions `A`, `B` integrable on `s`,

  `∫_s √A · √B ≤ √(∫_s A) · √(∫_s B)`.

This is `Work.Spaces.cs_integral` applied to `u = √A`, `v = √B` (which are in `L²` precisely
because `√A ^ 2 = A` pointwise), followed by `√(∫A · ∫B) = √(∫A)·√(∫B)`. -/
theorem cs_sqrt_le {s : Set ℝ} {A B : ℝ → ℝ}
    (hA : IntegrableOn A s) (hB : IntegrableOn B s)
    (hAnn : ∀ x, 0 ≤ A x) (hBnn : ∀ x, 0 ≤ B x) :
    (∫ x in s, Real.sqrt (A x) * Real.sqrt (B x))
      ≤ Real.sqrt (∫ x in s, A x) * Real.sqrt (∫ x in s, B x) := by
  have hu_meas : AEStronglyMeasurable (fun x => Real.sqrt (A x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have hv_meas : AEStronglyMeasurable (fun x => Real.sqrt (B x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable
  have hu_sq : Integrable (fun x => Real.sqrt (A x) ^ 2) (volume.restrict s) :=
    hA.congr (Filter.Eventually.of_forall (fun x => (Real.sq_sqrt (hAnn x)).symm))
  have hv_sq : Integrable (fun x => Real.sqrt (B x) ^ 2) (volume.restrict s) :=
    hB.congr (Filter.Eventually.of_forall (fun x => (Real.sq_sqrt (hBnn x)).symm))
  have hu_lp : MemLp (fun x => Real.sqrt (A x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hu_meas).mpr hu_sq
  have hv_lp : MemLp (fun x => Real.sqrt (B x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hv_meas).mpr hv_sq
  have hcs := Work.Spaces.cs_integral hu_lp hv_lp
  have e1 : (∫ x in s, Real.sqrt (A x) ^ 2) = ∫ x in s, A x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => Real.sq_sqrt (hAnn x))
  have e2 : (∫ x in s, Real.sqrt (B x) ^ 2) = ∫ x in s, B x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => Real.sq_sqrt (hBnn x))
  rw [e1, e2] at hcs
  calc (∫ x in s, Real.sqrt (A x) * Real.sqrt (B x))
      ≤ Real.sqrt ((∫ x in s, A x) * (∫ x in s, B x)) := Real.le_sqrt_of_sq_le hcs
    _ = Real.sqrt (∫ x in s, A x) * Real.sqrt (∫ x in s, B x) :=
        Real.sqrt_mul (integral_nonneg hAnn) _

/-! ## Slots of `ℋ⁴` -/

/-- A function `X` is a canonical slot of `ℋ⁴` for the datum `f` with exponent `q` if its
`canonW q`-weighted square is dominated, pointwise on `Iz × Iθ`, by the `ℋ⁴`-integrand of `f`.
This is the only property of a slot that the Cauchy–Schwarz bound uses. -/
structure SlotW (α q : ℝ) (X : ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ) : Prop where
  le : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
    canonW q z θ * (X z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ

/-- A pure `D_z`-slot `D_z^j f`, `j ≤ 4`, priced with `q ≤ η`. -/
theorem slotW_z (α : ℝ) {q : ℝ} (hq0 : 0 < q) (hq : q ≤ Work.Spaces.eta)
    (f : ℝ → ℝ → ℝ) (j : ℕ) (hj : j ≤ 4) :
    SlotW α q (Work.Spaces.DzIter j f) f := by
  refine ⟨fun z hz θ hθ => ?_⟩
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · subst h0
    rw [canonW_zero_z, zero_mul]
    exact Work.Spaces.HkIntegrand_nonneg α 4 f 0 θ
  · exact canonW_mul_z_le α f hq0 hq hz0 hθ j hj

/-- A mixed slot `D_z^j D_θ^i f`, `1 ≤ i`, `i + j ≤ 4`, priced with `q ≤ γ`. -/
theorem slotW_mixed (α : ℝ) {q : ℝ} (hq0 : 0 < q) (hqγ : q ≤ Work.Spaces.gam α)
    (f : ℝ → ℝ → ℝ) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    SlotW α q (Work.Spaces.mixed j i f) f := by
  refine ⟨fun z hz θ hθ => ?_⟩
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · subst h0
    rw [canonW_zero_z, zero_mul]
    exact Work.Spaces.HkIntegrand_nonneg α 4 f 0 θ
  · exact canonW_mul_mixed_le α f hq0 hqγ hz0 hθ j i hi hij

/-- **The Cauchy–Schwarz engine.**  For two canonical slots `X`, `Y` (of `f` resp. `g`)
priced with the same exponent `q`,

  `∫_z∫_θ canonW q z θ |X| |Y| ≤ √(HkSq α 4 f) · √(HkSq α 4 g)`.

The pointwise domination `canonW q (X²) ≤ HkIntegrand α 4 f` turns the integrand into the
product of the `L²`-functions `√(HkIntegrand α 4 f)`, `√(HkIntegrand α 4 g)`; the `θ`- and
`z`-integrals of the latter are `HkSq α 4 f`, `HkSq α 4 g`. -/
theorem slotCS_engine (α : ℝ) {q : ℝ} {X Y f g : ℝ → ℝ → ℝ}
    (hX : SlotW α q X f) (hY : SlotW α q Y g)
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemg : Work.Spaces.HkMem α 4 g) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * |X z θ| * |Y z θ|)
      ≤ Real.sqrt (Work.Spaces.HkSq α 4 f) * Real.sqrt (Work.Spaces.HkSq α 4 g) := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  set F : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ with hF
  set G : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ with hG
  have hFnn : ∀ z, 0 ≤ F z := fun z => MeasureTheory.setIntegral_nonneg hIθm
    (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
  have hGnn : ∀ z, 0 ≤ G z := fun z => MeasureTheory.setIntegral_nonneg hIθm
    (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
  have hFint : IntegrableOn F Work.Spaces.Iz := hmemf.2
  have hGint : IntegrableOn G Work.Spaces.Iz := hmemg.2
  -- the pointwise domination and the `θ`-Cauchy–Schwarz, for every `z ∈ Iz`
  have hpt : ∀ z ∈ Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
      canonW q z θ * |X z θ| * |Y z θ|) ≤ Real.sqrt (F z) * Real.sqrt (G z) := by
    intro z hz
    have hdom : ∀ θ ∈ Work.Spaces.Iθ,
        canonW q z θ * |X z θ| * |Y z θ|
          ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ) *
            Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) := by
      intro θ hθ
      have hc : 0 ≤ canonW q z θ := canonW_nonneg hθ
      have hs : Real.sqrt (canonW q z θ) * Real.sqrt (canonW q z θ) = canonW q z θ := by
        rw [← sq, Real.sq_sqrt hc]
      calc canonW q z θ * |X z θ| * |Y z θ|
          = (Real.sqrt (canonW q z θ) * Real.sqrt (canonW q z θ)) * |X z θ| * |Y z θ| := by
            rw [hs]
        _ = Real.sqrt (canonW q z θ * (X z θ) ^ 2)
              * Real.sqrt (canonW q z θ * (Y z θ) ^ 2) := by
            rw [Real.sqrt_mul hc, Real.sqrt_mul hc, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
            ring
        _ ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ) *
              Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) :=
            mul_le_mul (Real.sqrt_le_sqrt (hX.le z hz θ hθ))
              (Real.sqrt_le_sqrt (hY.le z hz θ hθ))
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hf_sq : Integrable (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) :=
      (hmemf.1 z hz).congr (Filter.Eventually.of_forall
        (fun θ => (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α 4 f z θ)).symm))
    have hg_sq : Integrable (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) :=
      (hmemg.1 z hz).congr (Filter.Eventually.of_forall
        (fun θ => (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α 4 g z θ)).symm))
    have hf_meas : AEStronglyMeasurable
        (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ))
        (volume.restrict Work.Spaces.Iθ) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable (hmemf.1 z hz).aestronglyMeasurable
    have hg_meas : AEStronglyMeasurable
        (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ))
        (volume.restrict Work.Spaces.Iθ) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable (hmemg.1 z hz).aestronglyMeasurable
    have hf_lp : MemLp (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)) 2
        (volume.restrict Work.Spaces.Iθ) := (memLp_two_iff_integrable_sq hf_meas).mpr hf_sq
    have hg_lp : MemLp (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) 2
        (volume.restrict Work.Spaces.Iθ) := (memLp_two_iff_integrable_sq hg_meas).mpr hg_sq
    have hprod : Integrable (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ) *
        Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) (volume.restrict Work.Spaces.Iθ) :=
      memLp_one_iff_integrable.mp (hf_lp.mul hg_lp)
    calc (∫ θ in Work.Spaces.Iθ, canonW q z θ * |X z θ| * |Y z θ|)
        ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ) *
            Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) :=
          integral_mono_of_nonneg
            (ae_restrict_of_forall_mem hIθm (fun θ hθ =>
              mul_nonneg (mul_nonneg (canonW_nonneg hθ) (abs_nonneg _)) (abs_nonneg _)))
            hprod (ae_restrict_of_forall_mem hIθm hdom)
      _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) *
            Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) :=
          cs_sqrt_le (hmemf.1 z hz) (hmemg.1 z hz)
            (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
            (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
      _ = Real.sqrt (F z) * Real.sqrt (G z) := by rw [hF, hG]
  -- the `z`-monotonicity and the `z`-Cauchy–Schwarz
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * |X z θ| * |Y z θ|)
      ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (F z) * Real.sqrt (G z) := by
    refine integral_mono_of_nonneg ?_ ?_ (ae_restrict_of_forall_mem hIzm hpt)
    · exact ae_restrict_of_forall_mem hIzm (fun z hz => MeasureTheory.setIntegral_nonneg hIθm
        (fun θ hθ => mul_nonneg (mul_nonneg (canonW_nonneg hθ) (abs_nonneg _)) (abs_nonneg _)))
    · have hF_meas : AEStronglyMeasurable (fun z => Real.sqrt (F z))
          (volume.restrict Work.Spaces.Iz) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable hFint.aestronglyMeasurable
      have hG_meas : AEStronglyMeasurable (fun z => Real.sqrt (G z))
          (volume.restrict Work.Spaces.Iz) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable hGint.aestronglyMeasurable
      have hF_sq : Integrable (fun z => Real.sqrt (F z) ^ 2) (volume.restrict Work.Spaces.Iz) :=
        hFint.congr (Filter.Eventually.of_forall (fun z => (Real.sq_sqrt (hFnn z)).symm))
      have hG_sq : Integrable (fun z => Real.sqrt (G z) ^ 2) (volume.restrict Work.Spaces.Iz) :=
        hGint.congr (Filter.Eventually.of_forall (fun z => (Real.sq_sqrt (hGnn z)).symm))
      have hF_lp : MemLp (fun z => Real.sqrt (F z)) 2 (volume.restrict Work.Spaces.Iz) :=
        (memLp_two_iff_integrable_sq hF_meas).mpr hF_sq
      have hG_lp : MemLp (fun z => Real.sqrt (G z)) 2 (volume.restrict Work.Spaces.Iz) :=
        (memLp_two_iff_integrable_sq hG_meas).mpr hG_sq
      exact memLp_one_iff_integrable.mp (hF_lp.mul hG_lp)
  have hFeq : (∫ z in Work.Spaces.Iz, F z) = Work.Spaces.HkSq α 4 f := by
    simp only [hF, Work.Spaces.HkSq]
  have hGeq : (∫ z in Work.Spaces.Iz, G z) = Work.Spaces.HkSq α 4 g := by
    simp only [hG, Work.Spaces.HkSq]
  calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * |X z θ| * |Y z θ|)
      ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (F z) * Real.sqrt (G z) := houter
    _ ≤ Real.sqrt (∫ z in Work.Spaces.Iz, F z) * Real.sqrt (∫ z in Work.Spaces.Iz, G z) :=
        cs_sqrt_le hFint hGint hFnn hGnn
    _ = Real.sqrt (Work.Spaces.HkSq α 4 f) * Real.sqrt (Work.Spaces.HkSq α 4 g) := by
        rw [hFeq, hGeq]

/-- **The two-level Cauchy–Schwarz bound for a single pair of canonical slots.**
With the canonical weight `w(z)² sin(2θ)^{-q}` and the two `ℋ⁴`-slots
`mixed j1 i1 f`, `mixed j2 i2 g` (each of them a summand of `HkIntegrand α 4`: either a pure
`D_z`-slot `i = 0`, `j ≤ 4`, or a mixed slot `1 ≤ i`, `i + j ≤ 4`),

  `∫_z∫_θ w² σ^{-q} |D_z^{j1}D_θ^{i1} f| |D_z^{j2}D_θ^{i2} g| ≤ |f|_{ℋ⁴}|g|_{ℋ⁴}`,

with `C = 1`.  The two conditional hypotheses `i = 0 → q ≤ η` are exactly the requirement that
a pure-`D_z` slot is priced with the lighter exponent `sin(2θ)^{-η}`.

Route (all the integrability/measurability facts are in
`Submission/Work/FTS/TransportS/SlotT2/Basic.lean`):
* `zslot_slice_aesm` / `mslot_slice_aesm` and `zslot_slice_integrable` /
  `mslot_slice_integrable` give, for a.e. `z ∈ Iz`, the a.e. strong measurability and the
  integrability of `θ ↦ canonW q z θ · (mixed j i g z θ)²` (dispatch on `i = 0` vs `1 ≤ i`);
* `zslot_marginal_aesm`/`mslot_marginal_aesm` and `zslot_marginal_integrable`/
  `mslot_marginal_integrable` give the same for the marginals `z ↦ ∫_θ …`;
* `canonW_z_iterated_le` / `canonW_mixed_iterated_le` bound the two energies by
  `HkSq α 4 f` resp. `HkSq α 4 g`;
* then apply `Work.Spaces.cs_integral` twice (as in `Work.FTS.H2.H4Pair_cs`): first on each
  angular slice with `u = √(canonW q z θ (mixed j1 i1 f)²)`, `v = √(canonW q z θ (mixed j2 i2 g)²)`,
  then in `z` with `u = √(A z)`, `v = √(B z)`, where `A`, `B` are the two marginals. -/
theorem slotCS : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ) (q : ℝ) (j1 i1 j2 i2 : ℕ),
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
    Work.Spaces.HkMem α 4 f → Work.Spaces.HkMem α 4 g → 0 < q →
    ((i1 = 0 ∧ j1 ≤ 4) ∨ (1 ≤ i1 ∧ i1 + j1 ≤ 4)) →
    ((i2 = 0 ∧ j2 ≤ 4) ∨ (1 ≤ i2 ∧ i2 + j2 ≤ 4)) →
    (i1 = 0 → q ≤ Work.Spaces.eta) → (i2 = 0 → q ≤ Work.Spaces.eta) →
    q ≤ Work.Spaces.gam α →
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * |Work.Spaces.mixed j1 i1 f z θ| * |Work.Spaces.mixed j2 i2 g z θ|)
      ≤ C * (Real.sqrt (Work.Spaces.HkSq α 4 f) * Real.sqrt (Work.Spaces.HkSq α 4 g)) := by
  refine ⟨1, one_pos, ?_⟩
  intro α f g q j1 i1 j2 i2 hα hα1 hf hg hmemf hmemg hq0 hs1 hs2 hq1 hq2 hqγ
  have hX : SlotW α q (Work.Spaces.mixed j1 i1 f) f := by
    rcases hs1 with ⟨h1, hj1⟩ | ⟨hi1, hij1⟩
    · rw [h1, Work.Spaces.mixed_zero_right]
      exact slotW_z α hq0 (hq1 h1) f j1 hj1
    · exact slotW_mixed α hq0 hqγ f j1 i1 hi1 hij1
  have hY : SlotW α q (Work.Spaces.mixed j2 i2 g) g := by
    rcases hs2 with ⟨h2, hj2⟩ | ⟨hi2, hij2⟩
    · rw [h2, Work.Spaces.mixed_zero_right]
      exact slotW_z α hq0 (hq2 h2) g j2 hj2
    · exact slotW_mixed α hq0 hqγ g j2 i2 hi2 hij2
  have hmain := slotCS_engine α hX hY hmemf hmemg
  simpa only [canonW, one_mul] using hmain

end Work.FTS.TransportS.SlotT2
