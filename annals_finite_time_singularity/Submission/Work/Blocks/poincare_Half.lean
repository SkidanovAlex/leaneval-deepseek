import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.HalfSmooth
import Submission.Work.FTS.EllipticEst.Blocks.slice_f_bound
import Submission.Work.FTS.EllipticEst.Blocks.slice_d_bound
import Submission.Work.Blocks.SmoothHalfAux
import Submission.Work.Blocks.HkIntegrand_integral_le_pth2_half
import Submission.Work.Blocks.HkIntegrand_integral_le_pth2_pth_half

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks

open Work.FTS.EllipticEst Work.FTS.EllipticEst.Blocks

set_option autoImplicit false

/-
**The weighted angular Poincaré estimate in the half-strip smoothness class `SmoothHalf`.**

Namespace `Work.FTS.EllipticEst.Blocks`.

This is the **port** of the *already proved* estimate
`Work.FTS.EllipticEst.Blocks.theta_Hk_poincare`
(`Submission/Work/FTS/EllipticEst/Blocks/theta_Hk_poincare.lean`, verified `sorry`-free with
`#print axioms`) from the hypothesis `Work.Spaces.SmoothNbhd` to the weaker, *provable*
hypothesis `Work.FTS.EllipticEst.SmoothHalf` (see `Submission/Work/FTS/EllipticEst/HalfSmooth.lean`).

WHY the port is needed.  `SmoothNbhd f` demands `C^∞` on an open *neighbourhood of the closed
quadrant*, in particular on `z < 0`.  For the straightened residual
`Ξ = Work.Elliptic.EllResid α F Ψ = Ψ - (1/(4α))·sin 2θ·L₁₂(F)` that is FALSE, because
`EllHyp.sol` forces `F = bslOp α Ψ` only for `z > 0`; see the counterexample recorded in
`Submission/Work/Blocks/NOTES_EllResid_certs_counterexample.md`.  `SmoothHalf Ξ` *does* hold.

ROUTE.  The two per-`z` comparisons of the angular integrals are
`Work.Blocks.HkIntegrand_integral_le_pth2_half` and `…_pth_half` (ports of
`Blocks.HkIntegrand_integral_le_pth2` and `Blocks.HkIntegrand_integral_le_pth2_pth` to the
half-strip class; they consume the slice estimates `Blocks.slice_f_bound` / `Blocks.slice_d_bound`
and the half-strip layer `Work.FTS.EllipticEst.HalfU` of
`Submission/Work/Blocks/SmoothHalfAux.lean`).  What is left — and what this file does — is exactly
the `z`-integration bookkeeping of `theta_Hk_poincare`: `HkSq` is the iterated integral over
`Iz × Iθ`, the slice comparisons hold at *every* `z ∈ Iz` (at `z = 0` both sides vanish because
`w 0 = 0`), the right-hand integrand is honest by `HkMem α k (∂_θ²f)`, so
`integral_mono_of_nonneg` compares the outer integrals and `Real.sqrt_le_sqrt` plus the
square-root arithmetic finishes.  The only difference from the `SmoothNbhd` version is that the
slice constants are uniformised over the finitely many levels `K ≤ k` (`cf`, `cd` below) exactly
as there.
-/
theorem poincare_Half (k : ℕ) (hk : 2 ≤ k) : Work.FTS.EllipticEst.PoinHalf k hk := by
  -- the slice constants, uniformised over the finitely many levels `K ≤ k`
  let cf : ℕ → ℝ := fun K => Classical.choose (Work.FTS.EllipticEst.Blocks.slice_f_bound K)
  have hcf : ∀ K : ℕ, 0 < cf K ∧
      (∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 → SliceSmooth u → u 0 = 0 →
        u (Real.pi / 2) = 0 →
        IntegrableOn (fun θ => (sliceV u θ) ^ 2 * thEta θ) Work.Spaces.Iθ →
        (∀ m ∈ Finset.Icc 1 K, IntegrableOn
          (fun θ => (LopIter m (sliceV u) θ) ^ 2 * thGam α θ) Work.Spaces.Iθ) →
        (∀ θ ∈ Work.Spaces.Iθ, (u θ) ^ 2 * thEta θ ≤ cf K * slicePhi α K u θ) ∧
        (∀ i ∈ Finset.Icc 1 K, ∀ θ ∈ Work.Spaces.Iθ,
          (LopIter i u θ) ^ 2 * thGam α θ ≤ cf K * slicePhi α K u θ)) :=
    fun K => Classical.choose_spec (Work.FTS.EllipticEst.Blocks.slice_f_bound K)
  let cd : ℕ → ℝ := fun K => Classical.choose (Work.FTS.EllipticEst.Blocks.slice_d_bound K)
  have hcd : ∀ K : ℕ, 0 < cd K ∧
      (∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 → SliceSmooth u → u 0 = 0 →
        u (Real.pi / 2) = 0 →
        IntegrableOn (fun θ => (sliceV u θ) ^ 2 * thEta θ) Work.Spaces.Iθ →
        (∀ m ∈ Finset.Icc 1 K, IntegrableOn
          (fun θ => (LopIter m (sliceV u) θ) ^ 2 * thGam α θ) Work.Spaces.Iθ) →
        (∀ θ ∈ Work.Spaces.Iθ, (deriv u θ) ^ 2 * thEta θ ≤ cd K * slicePhi α K u θ) ∧
        (∀ i ∈ Finset.Icc 1 K, ∀ θ ∈ Work.Spaces.Iθ,
          (LopIter i (deriv u) θ) ^ 2 * thGam α θ ≤ cd K * slicePhi α K u θ)) :=
    fun K => Classical.choose_spec (Work.FTS.EllipticEst.Blocks.slice_d_bound K)
  let C1 : ℝ := (∑ K ∈ Finset.range (k + 1), cf K) + 1
  let C2 : ℝ := (∑ K ∈ Finset.range (k + 1), cd K) + 1
  have hle1 : ∀ K ≤ k, cf K ≤ C1 := by
    intro K hK
    have hmem : K ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hK)
    have hsum : cf K ≤ ∑ K' ∈ Finset.range (k + 1), cf K' :=
      Finset.single_le_sum (fun K' _ => le_of_lt (hcf K').1) hmem
    simp only [C1]; linarith
  have hle2 : ∀ K ≤ k, cd K ≤ C2 := by
    intro K hK
    have hmem : K ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hK)
    have hsum : cd K ≤ ∑ K' ∈ Finset.range (k + 1), cd K' :=
      Finset.single_le_sum (fun K' _ => le_of_lt (hcd K').1) hmem
    simp only [C2]; linarith
  have hunif1 : ∀ (K : ℕ), K ≤ k → ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 → SliceSmooth u →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      IntegrableOn (fun θ => (sliceV u θ) ^ 2 * thEta θ) Work.Spaces.Iθ →
      (∀ m ∈ Finset.Icc 1 K, IntegrableOn
        (fun θ => (LopIter m (sliceV u) θ) ^ 2 * thGam α θ) Work.Spaces.Iθ) →
      (∀ θ ∈ Work.Spaces.Iθ, (u θ) ^ 2 * thEta θ ≤ C1 * slicePhi α K u θ) ∧
      (∀ i ∈ Finset.Icc 1 K, ∀ θ ∈ Work.Spaces.Iθ,
        (LopIter i u θ) ^ 2 * thGam α θ ≤ C1 * slicePhi α K u θ) := by
    intro K hK α u hα hα1 hsm h0 hpi hint hm
    obtain ⟨b1, b2⟩ := (hcf K).2 α u hα hα1 hsm h0 hpi hint hm
    exact ⟨fun θ hθ => le_trans (b1 θ hθ)
        (mul_le_mul_of_nonneg_right (hle1 K hK) (slicePhi_nonneg α K u hθ)),
      fun i hi θ hθ => le_trans (b2 i hi θ hθ)
        (mul_le_mul_of_nonneg_right (hle1 K hK) (slicePhi_nonneg α K u hθ))⟩
  have hunif2 : ∀ (K : ℕ), K ≤ k → ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 → SliceSmooth u →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      IntegrableOn (fun θ => (sliceV u θ) ^ 2 * thEta θ) Work.Spaces.Iθ →
      (∀ m ∈ Finset.Icc 1 K, IntegrableOn
        (fun θ => (LopIter m (sliceV u) θ) ^ 2 * thGam α θ) Work.Spaces.Iθ) →
      (∀ θ ∈ Work.Spaces.Iθ, (deriv u θ) ^ 2 * thEta θ ≤ C2 * slicePhi α K u θ) ∧
      (∀ i ∈ Finset.Icc 1 K, ∀ θ ∈ Work.Spaces.Iθ,
        (LopIter i (deriv u) θ) ^ 2 * thGam α θ ≤ C2 * slicePhi α K u θ) := by
    intro K hK α u hα hα1 hsm h0 hpi hint hm
    obtain ⟨b1, b2⟩ := (hcd K).2 α u hα hα1 hsm h0 hpi hint hm
    exact ⟨fun θ hθ => le_trans (b1 θ hθ)
        (mul_le_mul_of_nonneg_right (hle2 K hK) (slicePhi_nonneg α K u hθ)),
      fun i hi θ hθ => le_trans (b2 i hi θ hθ)
        (mul_le_mul_of_nonneg_right (hle2 K hK) (slicePhi_nonneg α K u hθ))⟩
  obtain ⟨D1, hD1pos, hD1⟩ := HkIntegrand_integral_le_pth2_half k C1 hunif1
  obtain ⟨D2, hD2pos, hD2⟩ := HkIntegrand_integral_le_pth2_pth_half k C2 hunif2
  refine ⟨Real.sqrt (max D1 D2 + 1), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro α f hα hα1 hsm hvan hmem
  have hmem1 := hmem.1
  have hIz : MeasurableSet Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]; exact measurableSet_Ici
  set G : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ with hGdef
  have hGnn : ∀ z ∈ Work.Spaces.Iz, 0 ≤ G z :=
    fun z _ => setIntegral_nonneg measurableSet_Icc fun θ _ =>
      Work.Spaces.HkIntegrand_nonneg α k _ z θ
  have hGint : IntegrableOn G Work.Spaces.Iz := hmem.2
  have hfactor : max D1 D2 ≤ max D1 D2 + 1 := le_add_of_nonneg_right zero_le_one
  have h1z : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) z
        ≤ (max D1 D2 + 1) * G z := by
    filter_upwards [ae_restrict_mem hIz] with z hz
    have h := hD1 α f hα hα1 hsm hvan hmem1 z hz
    exact le_trans h (mul_le_mul_of_nonneg_right
      (le_trans (le_max_left D1 D2) hfactor) (hGnn z hz))
  have hnn1 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iz]
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) :=
    Eventually.of_forall fun z => setIntegral_nonneg measurableSet_Icc fun θ _ =>
      Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hInt1 : IntegrableOn (fun z => (max D1 D2 + 1) * G z) Work.Spaces.Iz :=
    hGint.const_mul _
  have hSq1 : Work.Spaces.HkSq α k f
      ≤ (max D1 D2 + 1) * Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 f) := by
    have hm1 := integral_mono_of_nonneg hnn1 hInt1 h1z
    calc Work.Spaces.HkSq α k f
        = ∫ z in Work.Spaces.Iz, (fun z => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k f z θ) z := rfl
      _ ≤ ∫ z in Work.Spaces.Iz, (max D1 D2 + 1) * G z := hm1
      _ = (max D1 D2 + 1) * ∫ z in Work.Spaces.Iz, G z := integral_const_mul _ _
      _ = (max D1 D2 + 1) * Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 f) := rfl
  have h2z : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ) z
        ≤ (max D1 D2 + 1) * G z := by
    filter_upwards [ae_restrict_mem hIz] with z hz
    have h := hD2 α f hα hα1 hsm hvan hmem1 z hz
    exact le_trans h (mul_le_mul_of_nonneg_right
      (le_trans (le_max_right D1 D2) hfactor) (hGnn z hz))
  have hnn2 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iz]
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ) :=
    Eventually.of_forall fun z => setIntegral_nonneg measurableSet_Icc fun θ _ =>
      Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.pth f) z θ
  have hInt2 : IntegrableOn (fun z => (max D1 D2 + 1) * G z) Work.Spaces.Iz :=
    hGint.const_mul _
  have hSq2 : Work.Spaces.HkSq α k (Work.Spaces.pth f)
      ≤ (max D1 D2 + 1) * Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 f) := by
    have hm2 := integral_mono_of_nonneg hnn2 hInt2 h2z
    calc Work.Spaces.HkSq α k (Work.Spaces.pth f)
        = ∫ z in Work.Spaces.Iz, (fun z => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ) z := rfl
      _ ≤ ∫ z in Work.Spaces.Iz, (max D1 D2 + 1) * G z := hm2
      _ = (max D1 D2 + 1) * ∫ z in Work.Spaces.Iz, G z := integral_const_mul _ _
      _ = (max D1 D2 + 1) * Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 f) := rfl
  constructor
  · calc Work.Spaces.HkNorm α k f = Real.sqrt (Work.Spaces.HkSq α k f) := rfl
      _ ≤ Real.sqrt ((max D1 D2 + 1) * Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 f)) :=
          Real.sqrt_le_sqrt hSq1
      _ = Real.sqrt (max D1 D2 + 1) * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 f) := by
          rw [Real.sqrt_mul (by positivity), Work.Spaces.HkNorm]
  · calc Work.Spaces.HkNorm α k (Work.Spaces.pth f)
        = Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.pth f)) := rfl
      _ ≤ Real.sqrt ((max D1 D2 + 1) * Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 f)) :=
          Real.sqrt_le_sqrt hSq2
      _ = Real.sqrt (max D1 D2 + 1) * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 f) := by
          rw [Real.sqrt_mul (by positivity), Work.Spaces.HkNorm]

end Work.Blocks
