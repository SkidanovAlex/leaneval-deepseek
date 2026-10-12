import Mathlib
import Submission.Work.BoseBoxFock.slotProj_adjoint
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotProj_adjoint_meas` — self-adjointness of `slotProj` for a bounded
measurable state

`Work.BoseBoxFock.slotProj_adjoint` proves

`∫ x, star (slotProj e S Φ x) * Ψ x = ∫ x, star (Φ x) * slotProj e S Ψ x`

for `Φ`, `Ψ` continuous with compact support.  Inspecting that proof, the regularity of `Ψ` is
used *only* to produce the `Integrable` hypotheses of the two Fubini steps: continuity is used
solely to obtain the joint continuity (hence `AEStronglyMeasurable`) of the two product
integrands.  Both integrability statements survive when `Ψ` is merely measurable and bounded —
the compactly supported kernel provides the compact support, the bound of `Ψ` provides the
domination.  This file carries out that adaptation:

* `hasCompactSupport_fst_mul_prod_PV` — the joint (configuration, fibre) function
  `x ↦ f x.1 * ∏_{i ∈ S} PV e (x.1 i) (x.2 i)` is compactly supported as soon as `f` is;
* `integrable_slotKernelM` — the measurable/bounded replacement of `integrable_slotKernel`;
* `slotKernelG_integrableM`, `slotKernelH_integrableM` — the measurable/bounded replacements of
  `slotKernelG_integrable`, `slotKernelH_integrable` (the latter by transporting along the
  measure preserving swap `slotSwapMeas S`, exactly as before);
* `slotProj_adjoint_meas` — the target, whose proof repeats the change of variables of
  `slotProj_adjoint` verbatim.
-/

noncomputable section

namespace Work.BoseBoxFock

open MeasureTheory

set_option autoImplicit false

-- `horth` (orthonormality of the modes) is part of the requested statement but is *not* needed
-- (just as in `slotProj_adjoint`): the change of variables never uses it.
set_option linter.unusedVariables false

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Joint compact support of the (configuration, fibre) integrand -/

/-- The joint function `p ↦ f p.1 * ∏_{i ∈ S} PV e (p.1 i.1) (p.2 i)` is compactly supported
whenever `f` is: the configuration variable must lie in `tsupport f`, and every fibre coordinate
must lie in `⋃ l, tsupport (e l)` (otherwise the corresponding `PV`-factor vanishes, whatever the
configuration is). -/
theorem hasCompactSupport_fst_mul_prod_PV {m n : ℕ} (e : Fin m → Ω → ℂ)
    (hec : ∀ l, HasCompactSupport (e l)) (S : Finset (Fin n))
    {f : (Fin n → Ω) → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun p : (Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω) =>
      f p.1 * ∏ i : {i : Fin n // i ∈ S}, PV e (p.1 i.1) (p.2 i)) := by
  classical
  have hKz : IsCompact (Set.univ.pi fun _ : {i : Fin n // i ∈ S} =>
      ⋃ l : Fin m, tsupport (e l)) :=
    isCompact_univ_pi (fun _ : {i : Fin n // i ∈ S} =>
      isCompact_iUnion (fun l : Fin m => (hec l).isCompact))
  refine HasCompactSupport.intro
    (K := tsupport f ×ˢ (Set.univ.pi fun _ : {i : Fin n // i ∈ S} =>
      ⋃ l : Fin m, tsupport (e l))) (hf.isCompact.prod hKz) ?_
  intro p hp
  by_cases h1 : p.1 ∈ tsupport f
  · have hp2 : p.2 ∉ Set.univ.pi (fun _ : {i : Fin n // i ∈ S} =>
        ⋃ l : Fin m, tsupport (e l)) :=
      fun hmem => hp (Set.mem_prod.mpr ⟨h1, hmem⟩)
    rw [Set.mem_univ_pi] at hp2
    obtain ⟨i, hi⟩ := not_forall.mp hp2
    refine mul_eq_zero_of_right _ ?_
    exact Finset.prod_eq_zero (Finset.mem_univ i) (PV_eq_zero_of_factors e
      (fun l => image_eq_zero_of_notMem_tsupport (fun hl => hi (Set.mem_iUnion.mpr ⟨l, hl⟩))))
  · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]

/-! ## 2. Integrability of the two product integrands against a bounded measurable state -/

/-- Measurable/bounded form of `integrable_slotKernel`: the configuration factor `f` is continuous
with compact support, the state `g` is only measurable and bounded. -/
theorem integrable_slotKernelM {m n : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l)) (S : Finset (Fin n))
    {f : (Fin n → Ω) → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {g : (Fin n → Ω) → ℂ} (hgm : Measurable g) {C : ℝ} (hgb : ∀ z, ‖g z‖ ≤ C) :
    Integrable (fun p : (Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω) =>
      f p.1 * (∏ i : {i : Fin n // i ∈ S}, PV e (p.1 i.1) (p.2 i)) *
        g (Function.updateFinset p.1 S p.2))
      (volume : Measure ((Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω))) := by
  classical
  have hcont : Continuous (fun p : (Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω) =>
      f p.1 * (∏ i : {i : Fin n // i ∈ S}, PV e (p.1 i.1) (p.2 i))) :=
    (hf.comp continuous_fst).mul (continuous_prod_PV_pair e he S)
  have hcs : HasCompactSupport (fun p : (Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω) =>
      f p.1 * (∏ i : {i : Fin n // i ∈ S}, PV e (p.1 i.1) (p.2 i))) :=
    hasCompactSupport_fst_mul_prod_PV e hec S hfc
  have hmeas : AEStronglyMeasurable (fun p : (Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω) =>
      g (Function.updateFinset p.1 S p.2))
      (volume : Measure ((Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω))) :=
    ((hgm.comp (measurable_updateFinset_pair S)).aestronglyMeasurable)
  haveI h1 : IsFiniteMeasureOnCompacts (volume : Measure (Fin n → Ω)) := inferInstance
  haveI h2 : IsFiniteMeasureOnCompacts (volume : Measure ({i : Fin n // i ∈ S} → Ω)) := inferInstance
  haveI h3 : IsFiniteMeasureOnCompacts (volume : Measure ((Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω))) := inferInstance
  exact integrable_mul_of_continuous_hasCompactSupport_of_bounded hcont hcs hmeas
    ⟨C, fun p => hgb _⟩

/-- The right-hand integrand of the adjointness identity is integrable for a bounded measurable
`Ψ`. -/
theorem slotKernelG_integrableM {m n : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l)) (S : Finset (Fin n))
    {Φ Ψ : (Fin n → Ω) → ℂ} (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    Integrable (slotKernelG e S Φ Ψ)
      (volume : Measure ((Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω))) := by
  obtain ⟨CΨ, hCΨ⟩ := hΨb
  exact integrable_slotKernelM e he hec S (f := fun x => star (Φ x)) hΦ.star
    (hΦc.comp_left (g := star) (by simp : star (0 : ℂ) = 0)) hΨm hCΨ

/-- The left-hand integrand of the adjointness identity is integrable for a bounded measurable
`Ψ`: transport the previous statement along the measure preserving swap `slotSwapMeas S`. -/
theorem slotKernelH_integrableM {m n : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l)) (S : Finset (Fin n))
    {Φ Ψ : (Fin n → Ω) → ℂ} (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    Integrable (slotKernelH e S Φ Ψ)
      (volume : Measure ((Fin n → Ω) × ({i : Fin n // i ∈ S} → Ω))) :=
  (((measurePreserving_slotSwapMeas S).integrable_comp_emb
      (slotSwapMeas S).measurableEmbedding).mpr
    (slotKernelG_integrableM e he hec S hΦ hΦc hΨm hΨb)).congr
    (Filter.Eventually.of_forall fun p => slotKernel_swap_pointwise e S Φ Ψ p)

/-! ## 3. The target: self-adjointness for a bounded measurable second argument -/

-- Self-adjointness of `slotProj e S` for a *measurable bounded* second argument (the existing
-- `slotProj_adjoint` requires `Ψ` continuous with compact support; only boundedness of `Ψ` is
-- actually used there).  Adapt the proof of `slotProj_adjoint` in
-- `Submission/Work/BoseBoxFock/slotProj_adjoint.lean`: copy `integrable_slotKernel`,
-- `slotKernelG_integrable`, `slotKernelH_integrable` with the hypothesis `hg : Continuous g`
-- weakened to `hg : Measurable g` (continuity was used only to produce
-- `hintcont : Continuous (...)`; `Integrable.mono'` only needs `AEStronglyMeasurable`), then reuse
-- verbatim the change of variables along `slotSwapMeas S` (`slotKernel_swap_pointwise`,
-- `measurePreserving_slotSwapMeas`, `integral_prod`).  No other change is needed.
theorem slotProj_adjoint_meas {m n : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    (S : Finset (Fin n)) (Φ Ψ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    ∫ x, star (slotProj e S Φ x) * Ψ x = ∫ x, star (Φ x) * slotProj e S Ψ x := by
  classical
  have hIntG := slotKernelG_integrableM e he hec S hΦ hΦc hΨm hΨb
  have hIntH := slotKernelH_integrableM e he hec S hΦ hΦc hΨm hΨb
  have hstep1 : (∫ x, star (slotProj e S Φ x) * Ψ x)
      = ∫ p, slotKernelH e S Φ Ψ p := by
    have h1 : (∫ x, star (slotProj e S Φ x) * Ψ x)
        = ∫ x, ∫ z : ({i : Fin n // i ∈ S} → Ω), slotKernelH e S Φ Ψ (x, z) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [slotKernelH]
      rw [slotProj, slotStar_integral volume, ← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.updateFinset_def, star_mul]
      ring
    exact h1.trans (integral_prod (slotKernelH e S Φ Ψ) hIntH).symm
  have hstep2 : (∫ x, star (Φ x) * slotProj e S Ψ x)
      = ∫ p, slotKernelG e S Φ Ψ p := by
    have h1 : (∫ x, star (Φ x) * slotProj e S Ψ x)
        = ∫ x, ∫ z : ({i : Fin n // i ∈ S} → Ω), slotKernelG e S Φ Ψ (x, z) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [slotKernelG]
      rw [slotProj, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.updateFinset_def]
      ring
    exact h1.trans (integral_prod (slotKernelG e S Φ Ψ) hIntG).symm
  have hswap : (∫ p, slotKernelH e S Φ Ψ p) = ∫ p, slotKernelG e S Φ Ψ p :=
    (integral_congr_ae (Filter.Eventually.of_forall fun p =>
      (slotKernel_swap_pointwise e S Φ Ψ p).symm)).trans
      (MeasurePreserving.integral_comp (measurePreserving_slotSwapMeas S)
        (slotSwapMeas S).measurableEmbedding (slotKernelG e S Φ Ψ))
  exact hstep1.trans (hswap.trans hstep2.symm)

end Work.BoseBoxFock
