/-
# `OpenPkg/l12zero_field` — the `l12zero` field of the primed norm interface `N4Norm'`

Elgindi's Proposition `muestimate` (tex 1516), first line of the proof, in the **open-quadrant**
class `Work.FTS.VocabO.HQo α 4 f = Work.FTS.EllipticEst.SmoothOpen f ∧ HkMem α 4 f`:

`|L₁₂(f)(0)| ≤ C |f|_{ℋ⁴}`, with `C` universal (we use `C = 3`).

The estimate itself is the one of `Work.FTS.H2.L12ZeroQ` (the `SmoothQuad`/`RegQ` version) and of
`Work.FTS.H2.L12ZeroLe` (the `SmoothNbhd` version): with `L₁₂(f)(0) = ∫_{r>0} L₁₂dens(f)(r) dr`,

* `|L₁₂dens(f)(r)| ≤ √3 √(∫_θ f(r,θ)²)/r` (`Work.Coercivity.L12dens_sq_slice`, Cauchy–Schwarz
  against `K ∈ L²(Iθ)`), i.e. the weighted angular energy `(∫_θ f²)·((1+r)/r)²` controls the
  density after splitting `1/r = ((1+r)/r)·(1/(1+r))`;
* Cauchy–Schwarz in `r` against `r ↦ (1+r)^{-1} ∈ L²(0,∞)` of norm `≤ 2`
  (`Work.FTS.H2.InvOneAddSq`), giving `|L₁₂(f)(0)| ≤ √6 √(∫_{r>0} (∫_θ f²) w r) ≤ 3√…`;
* the pointwise Hardy comparison `(∫_θ f(r,θ)²) w r ≤ ∫_θ HkIntegrand α 4 f r θ` needs no
  smoothness at all (`Work.FTS.H2.L12Q.phiWeight_slice_le`).

Compared with `L12ZeroQ` only the three *regularity* inputs change, from `SmoothQuad` (which is
`C^∞` through `z = 0`) to `SmoothOpen` (interior `C^∞` on `z > 0`): the slice `θ ↦ f(z,θ)²` is
only a.e. strongly measurable on `Iθ` (its two endpoints are null), and the weighted angular
energy `r ↦ (∫_θ f²)·((1+r)/r)²` is a.e. strongly measurable on `(0,∞)`, by Fubini from the
joint continuity of `(r,θ) ↦ (f r θ)²` on the open quadrant
(`Work.Spaces.aesm_of_continuousOn_Qd`, `Work.Spaces.aesm_slice_of_continuousOn_Qd`).  The
"weak" `L₁₂(0)` bound itself (no smoothness, only the two integrability hypotheses) is
`Work.FTS.Nonlinear.Pieces.L12_zero_le_weak`, which is the migration-ready form of the
`L12ZeroQ` assembly.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.H2.L12ZeroQ
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.Nonlinear.Pieces.L12_zero_le_weak

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.OpenPkg

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

variable {f : ℝ → ℝ → ℝ}

/-- **Joint continuity of `(z,θ) ↦ (f z θ)²` on the open quadrant**, from `SmoothOpen f`.  This is
`l12q_quad_continuous` of `Work.FTS.H2.L12ZeroQ` with `SmoothQuad` weakened to `SmoothOpen` (the
two sets are literally the same open quadrant, so no restriction step is needed). -/
theorem l12zero_quad_continuous (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have h1 : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    simpa only [Work.FTS.EllipticEst.Q0] using hsm.continuousOn
  have h2 : ContinuousOn (fun p : ℝ × ℝ => (Function.uncurry f p) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := h1.pow 2
  simpa only [Function.uncurry] using h2

/-- **A.e. strong measurability of the Hardy-weighted angular energy in the interior class**, from
mere continuity of the datum on the open quadrant: `r ↦ (∫_θ f(r,θ)²)·((1+r)/r)²` on `(0,∞)`.
By Fubini from the joint a.e. strong measurability of `(r,θ) ↦ (f r θ)²` for the product of the
restrictions of Lebesgue measure to `Iz` and `Iθ` (`Work.Spaces.aesm_of_continuousOn_Qd`); the
Hardy weight `r ↦ ((1+r)/r)²` is continuous on `(0,∞)`. -/
theorem l12zero_energy_aesm
    (hc : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    MeasureTheory.AEStronglyMeasurable
      (fun r => (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hsq : ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    change ContinuousOn (fun p : ℝ × ℝ => (Function.uncurry f p) ^ 2) _
    exact hc.pow 2
  have hquad : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hsq
  have hslice : MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right' hquad
  have hmono : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      ≤ MeasureTheory.volume.restrict Work.Spaces.Iz :=
    MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume Set.Ioi_subset_Ici_self
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := hslice.mono_measure hmono
  have hw : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    ((ContinuousOn.div (continuousOn_const.add continuousOn_id) continuousOn_id
      (fun r hr => ne_of_gt (Set.mem_Ioi.mp hr))).pow 2).aestronglyMeasurable measurableSet_Ioi
  exact h1.mul hw

/-- **Integrability of the squared angular slice in the interior class.**  For `SmoothOpen f` and
`HkMem α 4 f`, every radial slice `θ ↦ (f z θ)²` with `z > 0` is integrable on `Iθ`.

This is `Work.FTS.H2.l12q_slice_sq_integrableOn` with `SmoothQuad` replaced by `SmoothOpen`: for
a.e. `θ ∈ Iθ` (all `θ ∈ Ioo 0 (π/2)`) one has `0 < sin(2θ) ≤ 1` and `w z ≥ 1`, so
`(f z θ)² ≤ (f z θ·(w z/sin(2θ)^{η/2}))² ≤ HkIntegrand α 4 f z θ`
(`Work.Spaces.sq_le_HkIntegrand_z`, `i = 0`); the majorant is integrable on `Iθ` by `hmem.1`, and
the dominated function is a.e. strongly measurable there by
`Work.Spaces.aesm_slice_of_continuousOn_Qd` (continuity on the open quadrant from `SmoothOpen`). -/
theorem l12zero_slice_sq_integrableOn (α : ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 4 f) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ := by
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      (l12zero_quad_continuous hsm) hz
  refine MeasureTheory.Integrable.mono' (hmem.1 z (le_of_lt hz)) haesm ?_
  -- the pointwise bound only fails on the two null endpoints
  have hcongr : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := (π / 2))).symm
  rw [hcongr]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsle : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hs0) hs1 (by have := Work.Spaces.eta_pos; linarith)
  have hspos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    Real.rpow_pos_of_pos hs0 _
  have hw1 : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div (by positivity)]
    nlinarith [hz]
  have hkey : 1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
    rw [one_le_div hspos]
    exact le_trans hsle hw1
  have hW2 : 1 ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    have h := mul_le_mul hkey hkey (zero_le_one) (le_trans zero_le_one hkey)
    simpa only [one_mul, pow_two] using h
  have hpt : (f z θ) ^ 2 ≤ (f z θ * (Work.Spaces.w z
      / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    calc (f z θ) ^ 2 = (f z θ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (f z θ) ^ 2
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hW2 (sq_nonneg _)
      _ = (f z θ * (Work.Spaces.w z
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := (mul_pow _ _ 2).symm
  calc ‖(f z θ) ^ 2‖ = (f z θ) ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
    _ ≤ (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := hpt
    _ = (Work.Spaces.DzIter 0 f z θ * (Work.Spaces.w z
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl
    _ ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ 0 (by norm_num)

/-- **The `L₁₂(0)` bound from a pointwise weight bound.**  If the angular slices are integrable
for a.e. `r > 0`, the Hardy-weighted angular energy is a.e. strongly measurable there, and it is
dominated a.e. by an integrable `Φ`, then `|L₁₂(f)(0)| ≤ 3 √(∫_{r>0} Φ)`.

This is `Work.FTS.Nonlinear.Pieces.L12_zero_le_of_weight_bound` (the assembly used by the rows),
whose `L²`-Cauchy–Schwarz core is the unconditional `Work.FTS.Nonlinear.Pieces.L12_zero_le_weak`.
It is `Work.FTS.H2.L12ZeroQ`'s assembly with the slicewise regularity inputs replaced by their
hypotheses. -/
theorem l12zero_of_weight_bound {Φ : ℝ → ℝ}
    (hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => f r θ ^ 2) Work.Spaces.Iθ)
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun r => (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hΦ : MeasureTheory.IntegrableOn Φ (Set.Ioi (0 : ℝ)))
    (hbd : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2 ≤ Φ r) :
    |Work.Construction.L12 f 0| ≤ 3 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Φ r) := by
  have hnn : ∀ r : ℝ, 0 ≤ (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2 :=
    fun r => mul_nonneg (integral_nonneg fun θ => sq_nonneg _) (sq_nonneg _)
  have hfin : MeasureTheory.IntegrableOn
      (fun r => (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    refine hΦ.mono' hmeas ?_
    filter_upwards [hbd] with r hr
    rw [Real.norm_of_nonneg (hnn r)]
    exact hr
  have hle := Work.FTS.Nonlinear.Pieces.L12_zero_le_weak 0 f hsl hfin
  have hmono : (∫ r in Set.Ioi (0 : ℝ),
        (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2)
      ≤ ∫ r in Set.Ioi (0 : ℝ), Φ r :=
    MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r _ => hnn r)) hΦ hbd
  calc |Work.Construction.L12 f 0|
      ≤ 3 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2) := hle
    _ ≤ 3 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Φ r) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmono) (by norm_num)

/-- **The zero mode of `L₁₂` in the open-quadrant class** (the field `N4Norm'.l12zero`):
for `HQo α 4 f` (interior `C^∞` plus honest `ℋ⁴`-membership), `|L₁₂(f)(0)| ≤ 3|f|_{ℋ⁴}`, with the
constant `3` independent of `α` and `f`.  The paper's form is `|L₁₂(f)(0)| ≤ C‖((z+1)/z)f‖_{L²}`
together with `‖((1+z)/z)f‖²_{L²} = ∫∫ f²w ≤ ∫∫ f²w²/sin(2θ)^η = |f|²_{ℋ⁴}`, the second step
being `Work.FTS.H2.L12Q.phiWeight_slice_le` (no smoothness).

The estimate never uses `α ≤ 1` (the constant is universal), so the version below is stated for
every `α > 0`; the field `N4Norm'.l12zero` of `N4Norm'_of_fields` quantifies over
`α ∈ Set.Ioc 0 α₂`, for which this is exactly the right shape. -/
theorem l12zero_field_all :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.VocabO.HQo α 4 f →
      |Work.Construction.L12 f 0| ≤ C * Work.FTS.Nonlin.Xn α f := by
  refine ⟨3, by norm_num, ?_⟩
  intro α _hα f hf
  obtain ⟨hopen, hmem⟩ := hf
  have hcont : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    simpa only [Work.FTS.EllipticEst.Q0] using hopen.continuousOn
  -- the three slicewise/radial regularity inputs
  have hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ : ℝ => (f r θ) ^ 2) Work.Spaces.Iθ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact l12zero_slice_sq_integrableOn α hopen hmem (Set.mem_Ioi.mp hr)
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun r => (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    l12zero_energy_aesm hcont
  -- the Hardy-weighted angular energy is dominated by `r ↦ ∫_θ HkIntegrand α 4 f r θ`
  have hΦ : MeasureTheory.IntegrableOn
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)
      (Set.Ioi (0 : ℝ)) := hmem.2.mono_set Set.Ioi_subset_Ici_self
  have hbd : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact Work.FTS.H2.L12Q.phiWeight_slice_le α f hmem r (Set.mem_Ioi.mp hr)
  have hmain := l12zero_of_weight_bound hsl hmeas hΦ hbd
  -- the radial integral of `∫_θ HkIntegrand` over `(0,∞)` is `HkSq α 4 f`
  have hHkSq : (∫ r in Set.Ioi (0 : ℝ),
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)
      = Work.Spaces.HkSq α 4 f := by
    rw [Work.Spaces.HkSq, Work.Spaces.Iz]
    exact MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))
  calc |Work.Construction.L12 f 0|
      ≤ 3 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ) := hmain
    _ = 3 * Work.FTS.Nonlin.Xn α f := by
        rw [hHkSq, Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]

/-- **The zero mode of `L₁₂` in the open-quadrant class** (`Work.FTS.VocabO.HQo α 4 f`, i.e.
interior `C^∞` plus honest `ℋ⁴`-membership): `|L₁₂(f)(0)| ≤ C|f|_{ℋ⁴}` with `C = 3` universal.
This is the requested field `N4Norm'.l12zero` in the form of its consumers, which take
`α ∈ (0,1]`; the slightly stronger `l12zero_field_all` above covers every `α > 0`. -/
theorem l12zero_field :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.VocabO.HQo α 4 f →
      |Work.Construction.L12 f 0| ≤ C * Work.FTS.Nonlin.Xn α f := by
  obtain ⟨C, hC, h⟩ := l12zero_field_all
  exact ⟨C, hC, fun α hα _hα1 f hf => h α hα f hf⟩

end

end Work.FTS.OpenPkg
