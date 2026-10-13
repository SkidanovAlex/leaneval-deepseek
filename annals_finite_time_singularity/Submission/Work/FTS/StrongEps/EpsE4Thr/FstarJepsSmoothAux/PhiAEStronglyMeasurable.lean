import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.GalBasis.exists_mixed_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# A.e. strong measurability of the parametric integral `Phi`

The function

  `x = (θ, p₂) ↦ ∫ p₁, ∂₁^m (Jker ρ ε) (p₁, p₂) · W (e^{s - p₁}) (thShift θ p₂)`

is a.e. strongly measurable for the measure
`(volume.restrict Iθ).prod (volume.restrict [-ε,ε])`.

The proof separates the integrand into the product of two factors:

* the kernel factor `q ↦ ∂₁^m (Jker ρ ε) (q.1, q.2.2)` is *continuous*: the kernel is `C^∞` on
  the whole plane (`Jker_smooth`, from the smoothness of `ρ`), and
  `contDiffOn_uncurry_pzIter_le` turns the iterated `∂₁`-derivative of a smooth function into a
  continuous function of both variables;
* the profile factor `q ↦ W (e^{s-q.1}) (thShift q.2.1 q.2.2)` is continuous *on the set*
  `S = {q | q.2.1 ∈ (0, π/2)}`: there `thShift` is continuous (away from the poles of `tan`) and
  the shifted point `(e^{s-q.1}, thShift q.2.1 q.2.2)` lies in the open quadrant `Q0`, where `W`
  is smooth.  The set `S` is conull for `volume.prod ((volume.restrict Iθ).prod ...)` — its
  complement only involves the two endpoints `0, π/2` of `Iθ`, a null set — so the behaviour of
  `W` off the quadrant is irrelevant.

Both factors are a.e. strongly measurable for the joint measure, hence so is their product, and
`AEStronglyMeasurable.integral_prod_right'` (applied to the swapped variables) gives the a.e.
strong measurability of the `p₁`-integral as a function of `x`.
-/

theorem PhiAEStronglyMeasurable {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {W : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen W) (m : ℕ) (s : ℝ) :
    MeasureTheory.AEStronglyMeasurable (fun x : ℝ × ℝ => ∫ p₁ : ℝ,
      Work.Spaces.pzIter m (fun a b => Work.FTS.StrongEps.Jker ρ ε (a, b)) p₁ x.2
        * W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod (MeasureTheory.volume.restrict (Set.Icc (-ε) ε))) := by
  set S : Set (ℝ × (ℝ × ℝ)) := {q | q.2.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} with hSdef
  -- ### the kernel factor is jointly continuous
  have hKcont : Continuous (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.pzIter m (fun a b => Work.FTS.StrongEps.Jker ρ ε (a, b)) q.1 q.2.2) := by
    have hbase : ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞)
        (Function.uncurry (fun a b : ℝ => Work.FTS.StrongEps.Jker ρ ε (a, b))) Set.univ :=
      (Work.FTS.StrongEps.Jker_smooth hρ ε (n := m)).contDiffOn
    have h1 : ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞)
        (Function.uncurry (Work.Spaces.pzIter m
          (fun a b : ℝ => Work.FTS.StrongEps.Jker ρ ε (a, b)))) Set.univ :=
      Work.FTS.GalBasis.contDiffOn_uncurry_pzIter_le
        (G := fun a b : ℝ => Work.FTS.StrongEps.Jker ρ ε (a, b))
        (V := Set.univ) isOpen_univ hbase m 0 (by omega)
    exact ((contDiffOn_univ.mp h1).continuous).comp (continuous_fst.prodMk continuous_snd.snd)
  -- ### the profile factor is continuous on `S`
  have hcontW : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      W (Real.exp (s - q.1)) (Work.FTS.StrongEps.thShift q.2.1 q.2.2)) S := by
    rw [hSdef]
    have htan : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => Real.tan q.2.1)
        {q : ℝ × (ℝ × ℝ) | q.2.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} := by
      refine Real.continuousOn_tan.comp continuous_snd.fst.continuousOn (fun q hq => ?_)
      simp only [Set.mem_ofPred_eq] at hq
      exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hq.1], hq.2⟩).ne'
    have h1 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => Real.tan q.2.1 * Real.exp (-q.2.2))
        {q : ℝ × (ℝ × ℝ) | q.2.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} :=
      htan.mul (Real.continuous_exp.comp_continuousOn (continuous_snd.snd.neg).continuousOn)
    have hth : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => Work.FTS.StrongEps.thShift q.2.1 q.2.2)
        {q : ℝ × (ℝ × ℝ) | q.2.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} := by
      have h2 := Real.continuous_arctan.comp_continuousOn h1
      simpa only [Work.FTS.StrongEps.thShift, Function.comp_def] using h2
    have hexp : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => Real.exp (s - q.1))
        {q : ℝ × (ℝ × ℝ) | q.2.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} := by fun_prop
    have hpair : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
        (Real.exp (s - q.1), Work.FTS.StrongEps.thShift q.2.1 q.2.2))
        {q : ℝ × (ℝ × ℝ) | q.2.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} := hexp.prodMk hth
    have hmem : ∀ q ∈ {q : ℝ × (ℝ × ℝ) | q.2.1 ∈ Set.Ioo (0 : ℝ) (π / 2)},
        (Real.exp (s - q.1), Work.FTS.StrongEps.thShift q.2.1 q.2.2) ∈ Work.FTS.EllipticEst.Q0 :=
      fun q hq => ⟨Real.exp_pos _, Work.FTS.StrongEps.thShift_mem hq⟩
    have h3 := hsm.continuousOn.comp hpair hmem
    simpa only [Function.uncurry, Function.comp_def] using h3
  have hSmeas : MeasurableSet S := by
    rw [hSdef]
    exact (isOpen_Ioo.preimage continuous_snd.fst).measurableSet
  -- ### `S` is conull
  have hnull : (MeasureTheory.volume.prod ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
      (MeasureTheory.volume.restrict (Set.Icc (-ε) ε)))) Sᶜ = 0 := by
    have hB : (MeasureTheory.volume.restrict Work.Spaces.Iθ) ((Set.Ioo (0 : ℝ) (π / 2))ᶜ) = 0 := by
      rw [Measure.restrict_apply measurableSet_Ioo.compl]
      have h0 : (MeasureTheory.volume : Measure ℝ) ({0} ∪ {π / 2}) = 0 :=
        measure_union_null (measure_singleton 0) (measure_singleton (π / 2))
      refine measure_mono_null ?_ h0
      intro x hx
      simp only [Work.Spaces.Iθ, Set.mem_inter_iff, Set.mem_Icc, Set.mem_compl_iff, Set.mem_Ioo,
        Set.mem_union, Set.mem_singleton_iff] at hx ⊢
      obtain ⟨hxn, hxI⟩ := hx
      rcases lt_or_ge (0 : ℝ) x with h | h
      · rcases lt_or_ge x (π / 2) with h2 | h2
        · exact absurd ⟨h, h2⟩ hxn
        · exact Or.inr (le_antisymm hxI.2 h2)
      · exact Or.inl (le_antisymm h hxI.1)
    have hinner : ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict (Set.Icc (-ε) ε)))
        (((Set.Ioo (0 : ℝ) (π / 2))ᶜ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
      rw [Measure.prod_prod, hB]
      simp
    rw [hSdef]
    have hset : ({q : ℝ × (ℝ × ℝ) | q.2.1 ∈ Set.Ioo (0 : ℝ) (π / 2)}ᶜ : Set (ℝ × (ℝ × ℝ)))
        = (Set.univ : Set ℝ) ×ˢ (((Set.Ioo (0 : ℝ) (π / 2))ᶜ) ×ˢ (Set.univ : Set ℝ)) := by
      ext q
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true,
        true_and]
    rw [hset, Measure.prod_prod, hinner]
    simp
  have hW : AEStronglyMeasurable (fun q : ℝ × (ℝ × ℝ) =>
      W (Real.exp (s - q.1)) (Work.FTS.StrongEps.thShift q.2.1 q.2.2))
      (MeasureTheory.volume.prod ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict (Set.Icc (-ε) ε)))) := by
    have hSae : ∀ᵐ q ∂(MeasureTheory.volume.prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
          (MeasureTheory.volume.restrict (Set.Icc (-ε) ε)))), q ∈ S := by
      filter_upwards [compl_mem_ae_iff.mpr hnull] with q hq
      simpa only [Set.mem_compl_iff, not_not] using hq
    rw [← Measure.restrict_eq_self_of_ae_mem hSae]
    exact hcontW.aestronglyMeasurable hSmeas
  -- ### the joint integrand, and the parametric integral
  have hjoint : AEStronglyMeasurable (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.pzIter m (fun a b => Work.FTS.StrongEps.Jker ρ ε (a, b)) q.1 q.2.2
        * W (Real.exp (s - q.1)) (Work.FTS.StrongEps.thShift q.2.1 q.2.2))
      (MeasureTheory.volume.prod ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict (Set.Icc (-ε) ε)))) :=
    hKcont.aestronglyMeasurable.mul hW
  have hswap := hjoint.prod_swap
  exact MeasureTheory.AEStronglyMeasurable.integral_prod_right'
    (μ := (MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
      (MeasureTheory.volume.restrict (Set.Icc (-ε) ε)))
    (ν := (MeasureTheory.volume : Measure ℝ)) hswap

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
