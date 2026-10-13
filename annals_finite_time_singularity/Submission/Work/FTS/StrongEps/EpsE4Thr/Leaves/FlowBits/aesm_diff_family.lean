import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.EpsE4Thr.mixed_sub_of_contDiffOn_six
import Submission.Work.FTS.EpsEngine.aesm_HkIntegrand_of_slots
import Submission.Work.FTS.EpsEngine.aesm_uncurry_restricted

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A.e. strong measurability of the difference family `V s - W`

Given a family `V s` (`s ∈ [0,δ]`) and a fixed profile `W`, all `C^∞` on the open quadrant
`Q0 = (0,∞) × (0,π/2)`, and assuming that all the mixed derivatives `D_z^jD_θ^i (V s)` are
a.e. strongly measurable in `s` at every point of the quadrant (for `i + j ≤ k`), we show

* the same for the mixed derivatives of the difference `V s - W` (subtraction on the open
  quadrant, `Work.FTS.StrongEps.EpsE4Thr.mixed_sub_of_contDiffOn_six`); and
* the joint a.e. strong measurability of the `ℋ^k`-integrand of the difference on the
  product measure `(volume.restrict (Icc 0 δ)) × (volume.restrict Iz) × (volume.restrict Iθ)`.

The second part is a Carathéodory argument (`aesm_uncurry_of_continuousOn_of_zero`): the
integrand is continuous in `(z,θ)` on the open quadrant (for `s ∈ Icc 0 δ`) and measurable
in `s` at each point of the quadrant; the target product measure is that of the restriction
to `A ×ˢ Q0`, and the points where `(z,θ)` leaves `Q0` (the coordinate axes and the lines
`θ = 0`, `θ = π/2`) are null for `(volume.restrict Iz).prod (volume.restrict Iθ)`.
-/

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits

open MeasureTheory Set Filter
open scoped Real Topology

/-! ## Two auxiliary measurability lemmas -/

/-- A finite sum (evaluated pointwise) of a.e. strongly measurable real functions is a.e.
strongly measurable.  (Local copy of the helper of `aesm_HkIntegrand_of_slots`.) -/
private lemma aesm_finsetSum_apply {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℝ}
    {μ : MeasureTheory.Measure ℝ}
    (hf : ∀ i ∈ s, MeasureTheory.AEStronglyMeasurable (f i) μ) :
    MeasureTheory.AEStronglyMeasurable (fun a : ℝ => ∑ i ∈ s, f i a) μ := by
  have h := Finset.aestronglyMeasurable_sum (M := ℝ) (f := f) s hf
  refine h.congr (Filter.Eventually.of_forall fun a => ?_)
  exact Finset.sum_apply a s f

/-- `aesm_HkIntegrand_of_slots` with the measurability hypothesis required only for the slots
`j + i ≤ k` that actually occur in `HkIntegrand α k`. -/
private lemma aesm_HkIntegrand_of_slots_le {μ : MeasureTheory.Measure ℝ} {B : ℝ → ℝ → ℝ → ℝ}
    {α : ℝ} {k : ℕ} {z θ : ℝ}
    (h : ∀ j i : ℕ, j + i ≤ k →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (B s) z θ) μ) :
    MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => Work.Spaces.HkIntegrand α k (B s) z θ) μ := by
  unfold Work.Spaces.HkIntegrand
  have hA : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => ∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i (B s) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) μ :=
    aesm_finsetSum_apply (fun i hi => by
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      exact ((h i 0 (by omega)).mul_const
        (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))).pow 2)
  have hB : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => ∑ i ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i (B s) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)) μ :=
    aesm_finsetSum_apply (fun i _ => aesm_finsetSum_apply (fun j _ => by
      by_cases hh : 1 ≤ i ∧ i + j ≤ k
      · have hthis : (fun s : ℝ => (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i (B s) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
            = fun s : ℝ => (Work.Spaces.mixed j i (B s) z θ * Work.Spaces.Wt α z θ) ^ 2 :=
          funext fun s => ite_eq_left hh
        rw [hthis]
        exact (((h j i (by omega)).mul_const (Work.Spaces.Wt α z θ)).pow 2)
      · have hthis : (fun s : ℝ => (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i (B s) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
            = fun _ : ℝ => (0 : ℝ) :=
          funext fun s => ite_eq_right hh
        rw [hthis]
        exact MeasureTheory.aestronglyMeasurable_const))
  exact hA.add hB

theorem aesm_diff_family {α : ℝ} {k : ℕ} {δ : ℝ} {V : ℝ → ℝ → ℝ → ℝ} {W : ℝ → ℝ → ℝ}
    (hle : k ≤ 6)
    (hsmV : ∀ s ∈ Set.Icc 0 δ, Work.FTS.EllipticEst.SmoothOpen (V s))
    (hsmW : Work.FTS.EllipticEst.SmoothOpen W)
    (hmeasV : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (V s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc 0 δ))) :
    (∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => Work.Spaces.mixed j i (fun z θ => V s z θ - W z θ) z θ)
        (MeasureTheory.volume.restrict (Set.Icc 0 δ))) ∧
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Work.Spaces.HkIntegrand α k
        (fun z θ => V p.1 z θ - W z θ) p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.Icc 0 δ)).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
  classical
  set A : Set ℝ := Set.Icc 0 δ with hAdef
  have hAmeas : MeasurableSet A := by rw [hAdef]; exact measurableSet_Icc
  have haeA : ∀ᵐ s ∂(MeasureTheory.volume.restrict A), s ∈ A := by
    rw [MeasureTheory.ae_restrict_iff' hAmeas]
    exact Filter.Eventually.of_forall (fun s hs => hs)
  -- the difference of the two profiles is `C^∞` on the open quadrant
  have hsm_diff : ∀ s ∈ A, Work.FTS.EllipticEst.SmoothOpen (fun z θ => V s z θ - W z θ) := by
    intro s hs
    exact ContDiffOn.sub (hsmV s hs) hsmW
  -- **Part 1**: the mixed derivatives of the difference are a.e. strongly measurable
  have hpart1 : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => Work.Spaces.mixed j i (fun z θ => V s z θ - W z θ) z θ)
        (MeasureTheory.volume.restrict A) := by
    intro j i hji z θ hzθ
    obtain ⟨hz0, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    have haesm := (hmeasV j i hji z θ hzθ).sub
      (MeasureTheory.aestronglyMeasurable_const (b := Work.Spaces.mixed j i W z θ))
    refine haesm.congr ?_
    filter_upwards [haeA] with s hs
    exact (Work.FTS.StrongEps.EpsE4Thr.mixed_sub_of_contDiffOn_six (hji := by omega)
      (hz := hz0) (hθ := ⟨hθ0, hθ1⟩)
      (hA := (hsmV s hs).forall 6) (hB := hsmW.forall 6)).symm
  refine ⟨hpart1, ?_⟩
  -- pointwise (at a point of the quadrant) measurability of the `ℋ^k`-integrand
  have hpoint : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => Work.Spaces.HkIntegrand α k
          (fun z θ => V s z θ - W z θ) z θ) (MeasureTheory.volume.restrict A) := by
    intro z θ hzθ
    exact aesm_HkIntegrand_of_slots_le (B := fun s z θ => V s z θ - W z θ)
      (fun j i hji => hpart1 j i hji z θ hzθ)
  -- the integrand, truncated to the open quadrant in `(z,θ)`
  set g₂ : ℝ → ℝ → ℝ → ℝ := fun s z θ =>
      if z ∈ Set.Ioi 0 ∧ θ ∈ Set.Ioo 0 (Real.pi / 2) then
        Work.Spaces.HkIntegrand α k (fun z θ => V s z θ - W z θ) z θ else 0 with hg₂
  have hcont₂ : ∀ s ∈ A, ContinuousOn (fun q : ℝ × ℝ => g₂ s q.1 q.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    intro s hs
    refine ((hsm_diff s hs).continuousOn_HkIntegrand α k).congr ?_
    intro q hq
    obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
    have hcond : q.1 ∈ Set.Ioi 0 ∧ q.2 ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hq1, hq2⟩
    simp only [hg₂]
    rw [ite_eq_left hcond]
  have hzero₂ : ∀ s ∈ A, ∀ q : ℝ × ℝ, q ∉ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) →
      g₂ s q.1 q.2 = 0 := by
    intro s _ q hq
    have hq' : ¬ (q.1 ∈ Set.Ioi 0 ∧ q.2 ∈ Set.Ioo 0 (Real.pi / 2)) := by
      simpa only [Set.mem_prod] using hq
    simp only [hg₂, ite_eq_right hq']
  have hmeas₂ : ∀ q : ℝ × ℝ, MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => g₂ s q.1 q.2) (MeasureTheory.volume.restrict A) := by
    intro q
    by_cases hq : q ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
    · obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
      have hcond : q.1 ∈ Set.Ioi 0 ∧ q.2 ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hq1, hq2⟩
      have hEq : (fun s : ℝ => g₂ s q.1 q.2)
          = fun s : ℝ => Work.Spaces.HkIntegrand α k
              (fun z θ => V s z θ - W z θ) q.1 q.2 := by
        funext s
        simp only [hg₂]
        rw [ite_eq_left hcond]
      rw [hEq]
      exact hpoint q.1 q.2 hq
    · have hq' : ¬ (q.1 ∈ Set.Ioi 0 ∧ q.2 ∈ Set.Ioo 0 (Real.pi / 2)) := by
        simpa only [Set.mem_prod] using hq
      have hEq : (fun s : ℝ => g₂ s q.1 q.2) = fun _ => (0 : ℝ) := by
        funext s
        simp only [hg₂, ite_eq_right hq']
      rw [hEq]
      exact MeasureTheory.aestronglyMeasurable_const
  -- Carathéodory: joint measurability of the truncated integrand
  have hbig := Work.FTS.EpsEngine.aesm_uncurry_restricted (A := A) hAmeas
    hcont₂ hzero₂ hmeas₂
  -- the angular product measure is that of the open quadrant inside the closed box
  have hIZ : ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rw [MeasureTheory.Measure.prod_restrict (μ := MeasureTheory.volume)
      (ν := MeasureTheory.volume) Work.Spaces.Iz Work.Spaces.Iθ]
    refine MeasureTheory.Measure.restrict_congr_set ?_
    exact MeasureTheory.Measure.set_prod_ae_eq (MeasureTheory.Ioi_ae_eq_Ici).symm
      (MeasureTheory.Ioo_ae_eq_Icc).symm
  have hν : ((MeasureTheory.volume.restrict A).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ((MeasureTheory.volume : Measure ℝ).prod
          (MeasureTheory.volume.prod MeasureTheory.volume)).restrict
          (A ×ˢ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) := by
    rw [hIZ]
    rw [MeasureTheory.Measure.prod_restrict (μ := MeasureTheory.volume)
      (ν := MeasureTheory.volume.prod MeasureTheory.volume) A
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))]
  have hle : ((MeasureTheory.volume.restrict A).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      ≤ (MeasureTheory.volume.restrict A).prod (MeasureTheory.volume : Measure (ℝ × ℝ)) :=
    MeasureTheory.Measure.prod_mono le_rfl
      (MeasureTheory.Measure.prod_mono MeasureTheory.Measure.restrict_le_self
        MeasureTheory.Measure.restrict_le_self)
  refine (hbig.mono_measure hle).congr ?_
  rw [hν, Filter.EventuallyEq,
    MeasureTheory.ae_restrict_iff' (hAmeas.prod (measurableSet_Ioi.prod measurableSet_Ioo))]
  exact Filter.Eventually.of_forall (fun p hp => by
    obtain ⟨_, hpQ⟩ := hp
    obtain ⟨hpQ1, hpQ2⟩ := Set.mem_prod.mp hpQ
    have hcond : p.2.1 ∈ Set.Ioi 0 ∧ p.2.2 ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hpQ1, hpQ2⟩
    simp only [hg₂]
    rw [ite_eq_left hcond])

end Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits
