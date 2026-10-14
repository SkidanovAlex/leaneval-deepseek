import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.FTS.StrongEps.EpsLocalPStar.SliceTracePiO
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Ip6DzAux
import Submission.Work.FTS.StrongPersist.SP6.EH6
import Submission.Work.FTS.StrongPersist.SP6.EUz6
import Submission.Work.FTS.StrongPersist.SP6.EV6
import Submission.Work.FTS.StrongPersist.SP6.EVz6
import Submission.Work.FTS.StrongPersist.SP6.Flat6Defs
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.StarPkg6Assembly
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.SliceTracePiPth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The angular trace of a slice at `θ = π/2`, in the `pth`/`mixed`/`Wt` vocabulary

`SliceTracePiPth` is the right-endpoint companion of `SliceTracePth` (same directory): the
weighted angular energy is written with the plain angular derivative `∂_θ f = pth f`, and the
integrability hypothesis is the `(0,1)`-slot form `(D_θ f · W)²` of the `ε`-scheme.  The two
integrands are related by

  `(mixed 0 1 f z θ · Wt α z θ)² = (w z)² · sin(2θ)^{2-γ} · (∂_θ f z θ)²`

(`mixed 0 1 f = D_θ f = sin(2θ)·∂_θ f`, `Wt = w·sin(2θ)^{-γ/2}`), so the slot hypothesis is
integrability of the weighted energy `sin(2θ)^{2-γ}(∂_θ f)²` up to the nonzero constant
`(w z)²` (`Work.FTS.StrongEps.EpsSqTools.pth_slice_integrable`).  The slice `θ ↦ f z θ` is `C¹`
on `(0,π/2)` because `f` is `C^∞` on the open quadrant (`SmoothOpen.curry_θ`), so the requested
trace and its weighted Hardy rate are exactly `SliceTracePiO`. -/

/-- The integrand of `SliceTracePiO` for the slice `θ ↦ f z θ`, with `pth` unfolded and the two
factors exchanged; the two sides are equal pointwise. -/
private lemma pthSq_sin_eq_pi (f : ℝ → ℝ → ℝ) (z α : ℝ) :
    (fun θ : ℝ => (deriv (fun θ' : ℝ => f z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      = fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth f z θ) ^ 2 := by
  funext θ
  rw [Work.Spaces.pth]
  ring

theorem SliceTracePiPth {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hslot : MeasureTheory.Integrable
      (fun θ => (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ)^2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    ∃ mu : ℝ, Filter.Tendsto (fun θ => f z θ)
        (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds mu) ∧
      ∀ θ ∈ Set.Ioo (Real.pi/4) (Real.pi/2),
        (f z θ - mu)^2 ≤ 100/(Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
          * (∫ σ in Work.Spaces.Iθ,
              (Real.sin (2*σ))^(2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ)^2) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- the integrability of the weighted angular energy of the slice, from the slot hypothesis
  have hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth f z θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.StrongEps.EpsSqTools.pth_slice_integrable hα0 hα1 hz hslot
  -- the same integrand in the shape consumed by `SliceTracePiO`
  have hint' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun θ' : ℝ => f z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
    rw [pthSq_sin_eq_pi f z α]
    exact hint
  -- the slice is `C¹` on `(0,π/2)`, being the `θ`-slice of a `C^∞` datum on the open quadrant
  have hsm : ContDiffOn ℝ 1 (fun θ : ℝ => f z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (hso.curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])
  obtain ⟨mu, hmu, hbd⟩ := SliceTracePiO (α := α) (u := fun θ : ℝ => f z θ) hα hsm hint'
  refine ⟨mu, hmu, fun θ hθ => ?_⟩
  have hInt : (∫ σ in Work.Spaces.Iθ,
        (deriv (fun θ' : ℝ => f z θ') σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      = ∫ σ in Work.Spaces.Iθ,
        (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ) ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) fun σ _ => ?_
    rw [Work.Spaces.pth]
    ring
  have h := hbd θ hθ
  rw [hInt] at h
  simpa using h

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SP6.FlatW6FieldsAlpha =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.SP6

/-!
# `FTS/StrongPersist/SP6/FlatW6FieldsAlpha` — the order-six flat bounds of the five star fields

The five fields of the star package are, on the open quadrant,

* `EH α Y = 2Y + 2α sin²θ·(Y/(z+1) + z∂_zY) + sin 2θ·∂_θY`,
* `EVz Y = 2(cos²θ - 2 sin²θ)·Y + sin 2θ·∂_θY`,  `EV Y = (z/(z+1))·EVz Y`,
* `EUz α Y = -(3Y + α(Y/(z+1) + z∂_zY))`,  `EU α Y = (z/(z+1))·EUz α Y`,

and they are *linear* in the three blocks `Y`, `∂_θY`, `z∂_zY`; hence from the flat data of the
blocks (`Fb 6 KY Y`, `FlatW 7 Y K`, `F0 6 KD (Yblk Y)`) one gets `FlatW 6` of each field at a
constant `C·(α+1)·(K+KY+KD)`.  The factor `(α+1)` is genuinely needed for `EH`, `EUz`, `EU`
(they grow linearly in `α`); on `EV`, `EVz` it is only a weakening.  The α-free variant is
*false*: see `Submission/Work/FTS/StrongPersist/SP6/FlatW6Fields.lean`, `not_FlatW6Fields`.

## The decomposition

Each field is proved separately, following the route fixed in
`Submission/Work/FTS/StrongPersist/SP6/Flat6Defs.lean`: the first clause `F0 6 (field)` from the
bilinear flat calculus (`F0_mul`/`F0_add`/`F0_const_mul`, which keep the constant *linear* in
the block bounds), and the second clause `F0 5 (∂_θ(field))` from an `Fb 5` bound of the field
(`Fb_add`, `Fb_mul_theta_free`, `Fb_const_mul`), assembled with `flatW6_of_F0`:

* `Work.FTS.StrongPersist.SP6.EH6` — the `EH`-field;
* `Work.FTS.StrongPersist.SP6.EVz6` — the `EVz`-field;
* `Work.FTS.StrongPersist.SP6.EV6` — the `EV`-field;
* `Work.FTS.StrongPersist.SP6.EUz6` — the `EUz`-field;
* `Work.FTS.StrongPersist.SP6.EU6` — the `EU`-field.

This file is the assembly: the five constants are merged by taking
`C = C_EH + C_EVz + C_EV + C_EUz + C_EU + 1`, which dominates each of them and is positive.
-/

theorem FlatW6FieldsAlpha : ∃ C : ℝ, 0 < C ∧ ∀ (α K KY KD : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ α → 0 ≤ K → 0 ≤ KY → 0 ≤ KD → Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.VocabO2.FlatW 7 Y K → Work.FTS.PhiStar.Fb 6 KY Y → Work.FTS.PhiStar.F0 6 KD (Work.FTS.PhiStar.Yblk Y) →
    Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EH α Y) (C * (α + 1) * (K + KY + KD)) ∧
    Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EVz Y) (C * (α + 1) * (K + KY + KD)) ∧
    Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EV Y) (C * (α + 1) * (K + KY + KD)) ∧
    Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EUz α Y) (C * (α + 1) * (K + KY + KD)) ∧
    Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EU α Y) (C * (α + 1) * (K + KY + KD)) := by
  obtain ⟨C₁, hC₁, hH⟩ := EH6
  obtain ⟨C₂, hC₂, hVz⟩ := EVz6
  obtain ⟨C₃, hC₃, hV⟩ := EV6
  obtain ⟨C₄, hC₄, hUz⟩ := EUz6
  obtain ⟨C₅, hC₅, hU⟩ := EU6
  refine ⟨C₁ + C₂ + C₃ + C₄ + C₅ + 1, by linarith, ?_⟩
  intro α K KY KD Y hα hK hKY hKD hsm hW hFb hD
  have hS : (0 : ℝ) ≤ (α + 1) * (K + KY + KD) :=
    mul_nonneg (by linarith) (by linarith)
  have hbig1 : C₁ ≤ C₁ + C₂ + C₃ + C₄ + C₅ + 1 := by linarith
  have hbig2 : C₂ ≤ C₁ + C₂ + C₃ + C₄ + C₅ + 1 := by linarith
  have hbig3 : C₃ ≤ C₁ + C₂ + C₃ + C₄ + C₅ + 1 := by linarith
  have hbig4 : C₄ ≤ C₁ + C₂ + C₃ + C₄ + C₅ + 1 := by linarith
  have hbig5 : C₅ ≤ C₁ + C₂ + C₃ + C₄ + C₅ + 1 := by linarith
  have step : ∀ c : ℝ, c ≤ C₁ + C₂ + C₃ + C₄ + C₅ + 1 → ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.VocabO2.FlatW 6 f (c * (α + 1) * (K + KY + KD)) →
      Work.FTS.VocabO2.FlatW 6 f ((C₁ + C₂ + C₃ + C₄ + C₅ + 1) * (α + 1) * (K + KY + KD)) := by
    intro c hc f hf
    refine FlatW_mono6 hf ?_
    calc c * (α + 1) * (K + KY + KD) = c * ((α + 1) * (K + KY + KD)) := by ring
      _ ≤ (C₁ + C₂ + C₃ + C₄ + C₅ + 1) * ((α + 1) * (K + KY + KD)) :=
          mul_le_mul_of_nonneg_right hc hS
      _ = (C₁ + C₂ + C₃ + C₄ + C₅ + 1) * (α + 1) * (K + KY + KD) := by ring
  exact ⟨step C₁ hbig1 _ (hH α K KY KD Y hα hK hKY hKD hsm hW hFb hD),
    step C₂ hbig2 _ (hVz α K KY KD Y hα hK hKY hKD hsm hW hFb hD),
    step C₃ hbig3 _ (hV α K KY KD Y hα hK hKY hKD hsm hW hFb hD),
    step C₄ hbig4 _ (hUz α K KY KD Y hα hK hKY hKD hsm hW hFb hD),
    step C₅ hbig5 _ (hU α K KY KD Y hα hK hKY hKD hsm hW hFb hD)⟩

end Work.FTS.StrongPersist.SP6
end
