import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le6
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.Blocks.IMC.cs_integral_mul_le
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option maxHeartbeats 1600000

/- Cauchy–Schwarz for the `k ≥ 5` group of the `L₁₂·D_θ` slot expansion.

Context: `IsLeafW α a ρ` says `ρ` is one of the three leaf weights
`w(z)²sin(2θ)^{-η}`, `w(z)²`, `w(z)²sin(2θ)^{-γ}` (the last only when `a ≥ 1`);
`HkNorm α k f = √(HkSq α k f)`; `HkSq α k` is the weighted ℋ^k energy
(`HkIntegrand α k` contains, for every slot `(i,j)` with `1 ≤ i`, `i + j ≤ k`, the term
`(D_z^jD_θ^if·Wt α z θ)²` with `(Wt α z θ)² = w(z)²sin(2θ)^{-γ}`, and for every `i ≤ k` the
term `(D_z^if·w(z)/sin(2θ)^{η/2})²`).

Claim: for `f` smooth on the open quadrant with honest `ℋ⁶`-integral, `a + b ≤ 6`,
`5 ≤ k ≤ b` and a leaf weight `ρ` of the slot `a`, the `ρ`-weighted pairing of the two slots
`D_z^{b-k}D_θ^{a+1}f` and `D_z^bD_θ^a f` is bounded by `C·|f|_{ℋ⁴}·|f|_{ℋ⁶}`.

Route: the two slots have orders `(b-k)+(a+1) ≤ a+b-4 ≤ 2` and `a+b ≤ 6`, and
`ρ ≤ slotW α aᵢ` for both slot indices `aᵢ ∈ {a, a+1}` (the `γ`-leaf only occurs with
`1 ≤ a`, and `a ≤ aᵢ`).  Hence `ρ·(D_z^{i}D_θ^{j}f)² ≤ HkIntegrand α m f` for the two slots, so
`∫∫ρU² ≤ HkSq α 2 f` and `∫∫ρV² ≤ HkSq α 6 f`; two Cauchy–Schwarz applications
(`Work.Blocks.IMC.cs_integral_mul_le` for the product measure, or the iterated form via
`abs_integral_le_integral_abs` + `integral_mono_of_nonneg`) give
`∫_z|∫_θ ρUV| ≤ ∫∫ρ|U||V| ≤ √(HkSq α 2 f)·√(HkSq α 6 f) ≤ HkNorm α 4 f·HkNorm α 6 f`
(monotonicity `HkSq α 2 ≤ HkSq α 4`).  a.e. strong measurability comes from continuity on the
open quadrant (`Work.Spaces.aesm_of_continuousOn_Qd`), and the measure is
`(volume.restrict Iz).prod (volume.restrict Iθ)` (`Measure.prod_restrict`).

**Implementation note (the constant is `1`).**  The proof runs the two-level
Cauchy–Schwarz argument of `slotCS_z` (whose `cs_sqrt_le_fts`, `leaf_prod_sqrt_le`,
`leaf_nonneg_Iθ`, `leaf_sq_le4`, `leaf_sq_le6` are reused verbatim), with the first slot
shifted: because the two slots here are `U = D_z^{b-k}D_θ^{a+1}f` and `V = D_z^bD_θ^af`,
the first one is dominated by `HkIntegrand α 4 f` through `leaf_sq_le4` applied to the slot
index `a+1` — which is legitimate since `IsLeafW α a ρ` implies `IsLeafW α (a+1) ρ` (the
`γ`-leaf is the only `a`-dependent case, and `1 ≤ a → 1 ≤ a+1`) — and the second one by
`HkIntegrand α 6 f` through `leaf_sq_le6`.  Both square-root factors are then combined in
the angular slice and, after a second Cauchy–Schwarz, in `z`, giving
`√(HkSq α 4 f)·√(HkSq α 6 f) = HkNorm α 4 f·HkNorm α 6 f`.  The a.e. estimability is
supplied by `ae_restrict_Iθ_of_Ioo`/`ae_restrict_of_forall_mem` throughout, and no
monotonicity of `HkSq` is needed. -/
theorem LeafShiftCSLe : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : ℝ → ℝ → ℝ) (a b k : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.FTS.TransportS.IsLeafW α a ρ → 5 ≤ k → k ≤ b → a + b ≤ 6 →
      (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ,
          ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ * Work.Spaces.mixed b a f z θ|)
        ≤ C * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f := by
  refine ⟨1, one_pos, ?_⟩
  intro α hαI f a b k ρ hso hmem hleaf hk hkb hab
  obtain ⟨hα, _hα1⟩ := hαI
  -- the level-four honesty of `f`, which the shifted slot needs
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hso 4 (by norm_num) hmem
  -- `ρ` is also a leaf weight of the (*shifted*) slot index `a + 1`
  have hleaf' : Work.FTS.TransportS.IsLeafW α (a + 1) ρ := by
    rcases hleaf with h | h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨Nat.le_succ_of_le h1, h2⟩)
  have habk : a + 1 + (b - k) ≤ 4 := by omega
  let U : ℝ → ℝ → ℝ := Work.Spaces.mixed (b - k) (a + 1) f
  let V : ℝ → ℝ → ℝ := Work.Spaces.mixed b a f
  let A : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.HkIntegrand α 4 f z θ
  let B : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.HkIntegrand α 6 f z θ
  change (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, ρ z θ * U z θ * V z θ|)
    ≤ 1 * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have h4nn : ∀ z θ, 0 ≤ A z θ := fun z θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have h6nn : ∀ z θ, 0 ≤ B z θ := fun z θ => Work.Spaces.HkIntegrand_nonneg α 6 f z θ
  have hAslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => A z θ) Work.Spaces.Iθ := hmem4.1
  have hBslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => B z θ) Work.Spaces.Iθ := hmem.1
  have hAint : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, A z θ) Work.Spaces.Iz := hmem4.2
  have hBint : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, B z θ) Work.Spaces.Iz := hmem.2
  have hAnn : ∀ z, 0 ≤ ∫ θ in Work.Spaces.Iθ, A z θ := fun z =>
    MeasureTheory.integral_nonneg_of_ae
      (ae_restrict_of_forall_mem hIθm (fun θ _ => h4nn z θ))
  have hBnn : ∀ z, 0 ≤ ∫ θ in Work.Spaces.Iθ, B z θ := fun z =>
    MeasureTheory.integral_nonneg_of_ae
      (ae_restrict_of_forall_mem hIθm (fun θ _ => h6nn z θ))
  -- ## the angular slice estimate: the two slots are dominated by `A` resp. `B`
  have hsliceAll : ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, ρ z θ * U z θ * V z θ|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ) := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · -- at `z = 0` every leaf weight vanishes
      subst h0
      have hρ0 : ∀ θ : ℝ, ρ 0 θ = 0 := fun θ => by
        rcases hleaf with rfl | rfl | ⟨-, rfl⟩ <;>
          simp [Work.FTS.TransportS.leafEta, Work.FTS.TransportS.leafOne,
            Work.FTS.TransportS.leafGam, Work.Spaces.w]
      have hzero : (fun θ : ℝ => ρ 0 θ * U 0 θ * V 0 θ) = fun _ => (0 : ℝ) := by
        funext θ; rw [hρ0 θ]; ring
      rw [hzero, integral_zero, abs_zero]
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · -- the open quadrant: pointwise domination and Cauchy–Schwarz on the slice
      have hstep1 : |∫ θ in Work.Spaces.Iθ, ρ z θ * U z θ * V z θ|
          ≤ ∫ θ in Work.Spaces.Iθ, |ρ z θ * U z θ * V z θ| := by
        simpa only [Real.norm_eq_abs] using
          (MeasureTheory.norm_integral_le_integral_norm
            (μ := volume.restrict Work.Spaces.Iθ) (fun θ : ℝ => ρ z θ * U z θ * V z θ))
      have hcongr : (∫ θ in Work.Spaces.Iθ, |ρ z θ * U z θ * V z θ|)
          = ∫ θ in Work.Spaces.Iθ, ρ z θ * |U z θ| * |V z θ| := by
        refine integral_congr_ae (ae_restrict_of_forall_mem hIθm (fun θ hθ => ?_))
        simp only [abs_mul, abs_of_nonneg (leaf_nonneg_Iθ hleaf z θ hθ)]
      have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
          ρ z θ * |U z θ| * |V z θ| ≤ Real.sqrt (A z θ) * Real.sqrt (B z θ) :=
        Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => by
          refine leaf_prod_sqrt_le (leaf_nonneg_Iθ hleaf z θ ⟨le_of_lt h1, le_of_lt h2⟩) ?_ ?_
          · exact leaf_sq_le4 hα hleaf' habk hz0 ⟨h1, h2⟩
          · exact leaf_sq_le6 hα hleaf hab hz0 ⟨h1, h2⟩)
      have h4_meas : AEStronglyMeasurable (fun θ => Real.sqrt (A z θ))
          (volume.restrict Work.Spaces.Iθ) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable (hAslice z hz).aestronglyMeasurable
      have h6_meas : AEStronglyMeasurable (fun θ => Real.sqrt (B z θ))
          (volume.restrict Work.Spaces.Iθ) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable (hBslice z hz).aestronglyMeasurable
      have h4_sq : Integrable (fun θ => Real.sqrt (A z θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
        (hAslice z hz).congr (Eventually.of_forall (fun θ => (Real.sq_sqrt (h4nn z θ)).symm))
      have h6_sq : Integrable (fun θ => Real.sqrt (B z θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
        (hBslice z hz).congr (Eventually.of_forall (fun θ => (Real.sq_sqrt (h6nn z θ)).symm))
      have h4_lp : MemLp (fun θ => Real.sqrt (A z θ)) 2 (volume.restrict Work.Spaces.Iθ) :=
        (memLp_two_iff_integrable_sq h4_meas).mpr h4_sq
      have h6_lp : MemLp (fun θ => Real.sqrt (B z θ)) 2 (volume.restrict Work.Spaces.Iθ) :=
        (memLp_two_iff_integrable_sq h6_meas).mpr h6_sq
      have hprod : Integrable (fun θ => Real.sqrt (A z θ) * Real.sqrt (B z θ))
          (volume.restrict Work.Spaces.Iθ) :=
        memLp_one_iff_integrable.mp (h4_lp.mul h6_lp)
      have hstep3 : (∫ θ in Work.Spaces.Iθ, ρ z θ * |U z θ| * |V z θ|)
          ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (A z θ) * Real.sqrt (B z θ) :=
        MeasureTheory.integral_mono_of_nonneg
          (ae_restrict_of_forall_mem hIθm (fun θ hθ => mul_nonneg
            (mul_nonneg (leaf_nonneg_Iθ hleaf z θ hθ) (abs_nonneg _)) (abs_nonneg _)))
          hprod hpt
      have hstep4 : (∫ θ in Work.Spaces.Iθ, Real.sqrt (A z θ) * Real.sqrt (B z θ))
          ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ) :=
        cs_sqrt_le_fts (hAslice z hz) (hBslice z hz)
          (fun θ => h4nn z θ) (fun θ => h6nn z θ)
      calc |∫ θ in Work.Spaces.Iθ, ρ z θ * U z θ * V z θ|
          ≤ ∫ θ in Work.Spaces.Iθ, |ρ z θ * U z θ * V z θ| := hstep1
        _ = ∫ θ in Work.Spaces.Iθ, ρ z θ * |U z θ| * |V z θ| := hcongr
        _ ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (A z θ) * Real.sqrt (B z θ) := hstep3
        _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ) := hstep4
  -- ## the radial Cauchy–Schwarz
  have houter_int : IntegrableOn (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)
      * Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ)) Work.Spaces.Iz := by
    have h1meas : AEStronglyMeasurable (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ))
        (volume.restrict Work.Spaces.Iz) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hAint.aestronglyMeasurable
    have h2meas : AEStronglyMeasurable (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ))
        (volume.restrict Work.Spaces.Iz) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hBint.aestronglyMeasurable
    have h1sq : Integrable (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ) ^ 2)
        (volume.restrict Work.Spaces.Iz) :=
      hAint.congr (Eventually.of_forall (fun z => (Real.sq_sqrt (hAnn z)).symm))
    have h2sq : Integrable (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ) ^ 2)
        (volume.restrict Work.Spaces.Iz) :=
      hBint.congr (Eventually.of_forall (fun z => (Real.sq_sqrt (hBnn z)).symm))
    have h1lp : MemLp (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)) 2
        (volume.restrict Work.Spaces.Iz) :=
      (memLp_two_iff_integrable_sq h1meas).mpr h1sq
    have h2lp : MemLp (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ)) 2
        (volume.restrict Work.Spaces.Iz) :=
      (memLp_two_iff_integrable_sq h2meas).mpr h2sq
    exact memLp_one_iff_integrable.mp (h1lp.mul h2lp)
  have houter : (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, ρ z θ * U z θ * V z θ|)
      ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => abs_nonneg _)
      houter_int (ae_restrict_of_forall_mem hIzm hsliceAll)
  have hCS : (∫ z in Work.Spaces.Iz, Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ))
      ≤ Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, A z θ)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, B z θ) :=
    cs_sqrt_le_fts hAint hBint hAnn hBnn
  calc (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, ρ z θ * U z θ * V z θ|)
      ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ) := houter
    _ ≤ Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, A z θ)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, B z θ) := hCS
    _ = 1 * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f := by
        simp only [Work.Spaces.HkNorm, Work.Spaces.HkSq, one_mul]
        rfl

end Work.FTS.StrongPersist.H6Pair6Aux
