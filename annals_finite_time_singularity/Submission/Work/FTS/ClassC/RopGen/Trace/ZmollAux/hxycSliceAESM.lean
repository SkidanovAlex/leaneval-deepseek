/-
# `Work.FTS.ClassC.RopGen.Trace.ZmollAux.hxycSliceAESM`

Measurability in `t` of the angular slice integral

  `t ↦ ∫ s, k (θ - s) * Hxyc G t s`,  `Hxyc G t s = Qext G (exp t) s`,

where `G` is `C^∞` on the open quadrant, `k` is continuous and supported in `[-ε, ε]` with
`ε ≤ 1/2`, and `θ ∈ (-1/4, π/2 + 1/4)`.

Only measurability is claimed (no integrability of the slices): the argument is that, for every
fixed `t`, the integrand agrees a.e. in `s` with the *explicit* three-branch expression

  `1_{(θ-ε,0)}(s) · k(θ-s)·(-G(exp t, -s)) + 1_{(0,π/2)}(s) · k(θ-s)·G(exp t, s)
     + 1_{(π/2,θ+ε)}(s) · k(θ-s)·(-G(exp t, π-s))`,

(`Qext` is odd about `0` and about `π/2`, and off the window `k(θ - s) = 0`), which is a sum of
indicators of measurable sets times functions that are continuous on those sets (the reflected
arguments `-s` and `π - s` land in the open quadrant `(0, π/2)` because
`(-3/4, π/2 + 3/4) ⊆ (-π/2, π)`).  Joint measurability on the product then gives measurability
of the slice integral by `MeasureTheory.AEStronglyMeasurable.integral_prod_right'`.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.mollHon

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.RopGen.Trace.ZmollAux

open MeasureTheory Set Filter
open scoped Real Topology

set_option linter.deprecated false

/-! ## The three branches of the doubly-odd extension, as functions on the plane -/

/-- The left branch `k (θ-s) · (-G (exp t, -s))` of the slice integrand, as a function of
`p = (t, s)`. -/
private noncomputable def Sl1 (G : ℝ → ℝ → ℝ) (k : ℝ → ℝ) (θ : ℝ) : ℝ × ℝ → ℝ :=
  fun p => k (θ - p.2) * (-(Function.uncurry G (Real.exp p.1, -p.2)))

/-- The middle branch `k (θ-s) · G (exp t, s)`. -/
private noncomputable def Sl2 (G : ℝ → ℝ → ℝ) (k : ℝ → ℝ) (θ : ℝ) : ℝ × ℝ → ℝ :=
  fun p => k (θ - p.2) * Function.uncurry G (Real.exp p.1, p.2)

/-- The right branch `k (θ-s) · (-G (exp t, π-s))`. -/
private noncomputable def Sl3 (G : ℝ → ℝ → ℝ) (k : ℝ → ℝ) (θ : ℝ) : ℝ × ℝ → ℝ :=
  fun p => k (θ - p.2) * (-(Function.uncurry G (Real.exp p.1, Real.pi - p.2)))

/-- The window on the left of the origin. -/
private def SlSet (θ ε : ℝ) : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo (θ - ε) 0

/-- The middle window `(0, π/2)`. -/
private def SmSet (_θ _ε : ℝ) : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)

/-- The window on the right of `π/2`. -/
private def SrSet (θ ε : ℝ) : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo (Real.pi / 2) (θ + ε)

/-- The three-piece representative of the slice integrand.  It agrees with
`(t,s) ↦ k (θ - s) * Qext G (exp t) s` except on the null set `ℝ × {0, π/2, θ-ε, θ+ε}`. -/
private noncomputable def SliceSum (G : ℝ → ℝ → ℝ) (k : ℝ → ℝ) (θ ε : ℝ) : ℝ × ℝ → ℝ :=
  fun p => (SlSet θ ε).indicator (Sl1 G k θ) p
    + (SmSet θ ε).indicator (Sl2 G k θ) p
    + (SrSet θ ε).indicator (Sl3 G k θ) p

private lemma SliceSum_apply (G : ℝ → ℝ → ℝ) (k : ℝ → ℝ) (θ ε t s : ℝ) :
    SliceSum G k θ ε (t, s)
      = (SlSet θ ε).indicator (Sl1 G k θ) (t, s)
        + (SmSet θ ε).indicator (Sl2 G k θ) (t, s)
        + (SrSet θ ε).indicator (Sl3 G k θ) (t, s) := rfl

private lemma Sl1_apply (G : ℝ → ℝ → ℝ) (k : ℝ → ℝ) (θ : ℝ) (t s : ℝ) :
    Sl1 G k θ (t, s) = k (θ - s) * (-(Function.uncurry G (Real.exp t, -s))) := rfl

private lemma Sl2_apply (G : ℝ → ℝ → ℝ) (k : ℝ → ℝ) (θ : ℝ) (t s : ℝ) :
    Sl2 G k θ (t, s) = k (θ - s) * Function.uncurry G (Real.exp t, s) := rfl

private lemma Sl3_apply (G : ℝ → ℝ → ℝ) (k : ℝ → ℝ) (θ : ℝ) (t s : ℝ) :
    Sl3 G k θ (t, s) = k (θ - s) * (-(Function.uncurry G (Real.exp t, Real.pi - s))) := rfl

/-! ## The three branches of `Qext`, in uncurried form -/

private lemma qext_lt_zero' (G : ℝ → ℝ → ℝ) (z s : ℝ) (hs : s < 0) :
    Work.FTS.EllSol.PkgK5.K5c.Qext G z s = -(Function.uncurry G (z, -s)) := by
  rw [Work.FTS.EllSol.PkgK5.K5c.Qext, if_neg (fun h => absurd h.1 (not_le.mpr hs)), if_pos hs]
  rfl

private lemma qext_mem' (G : ℝ → ℝ → ℝ) (z s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.EllSol.PkgK5.K5c.Qext G z s = Function.uncurry G (z, s) := by
  rw [Work.FTS.EllSol.PkgK5.K5c.Qext_of_mem G z s hs]
  rfl

private lemma qext_pihalf_lt' (G : ℝ → ℝ → ℝ) (z s : ℝ) (hs : Real.pi / 2 < s) :
    Work.FTS.EllSol.PkgK5.K5c.Qext G z s = -(Function.uncurry G (z, Real.pi - s)) := by
  have h0s : (0 : ℝ) < s := by linarith [Real.pi_pos]
  rw [Work.FTS.EllSol.PkgK5.K5c.Qext, if_neg (fun h => (not_le.mpr hs) h.2),
    if_neg (not_lt.mpr h0s.le)]
  rfl

/-! ## The pointwise identification, off the four exceptional angles -/

private lemma slice_eq (G : ℝ → ℝ → ℝ) {k : ℝ → ℝ} {ε θ t s : ℝ}
    (hvan : ∀ x : ℝ, ε < |x| → k x = 0)
    (hs : s ∉ ({0, Real.pi / 2, θ - ε, θ + ε} : Set ℝ)) :
    SliceSum G k θ ε (t, s) = k (θ - s) * Work.FTS.EllSol.EllPkgAux.Hxyc G t s := by
  rw [SliceSum_apply, Work.FTS.EllSol.EllPkgAux.Hxyc]
  have hmL : (t, s) ∈ SlSet θ ε ↔ s ∈ Set.Ioo (θ - ε) 0 := by
    simp only [SlSet, Set.mem_prod, Set.mem_univ, true_and]
  have hmM : (t, s) ∈ SmSet θ ε ↔ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    simp only [SmSet, Set.mem_prod, Set.mem_univ, true_and]
  have hmR : (t, s) ∈ SrSet θ ε ↔ s ∈ Set.Ioo (Real.pi / 2) (θ + ε) := by
    simp only [SrSet, Set.mem_prod, Set.mem_univ, true_and]
  have hneL : s ≠ θ - ε := fun h => hs (by rw [h]; simp)
  have hneR : s ≠ θ + ε := fun h => hs (by rw [h]; simp)
  by_cases h1 : s ∈ Set.Ioo (θ - ε) 0
  · -- left branch
    have h2 : s ∉ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun h => by linarith [h1.2, h.1]
    have h3 : s ∉ Set.Ioo (Real.pi / 2) (θ + ε) := fun h => by
      linarith [h1.2, h.1, Real.pi_pos]
    rw [Set.indicator_of_mem (hmL.mpr h1), Set.indicator_of_notMem (fun h => h2 (hmM.mp h)),
      Set.indicator_of_notMem (fun h => h3 (hmR.mp h)), Sl1_apply,
      qext_lt_zero' G (Real.exp t) s h1.2]
    ring
  · by_cases h2 : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · -- middle branch
      have h3 : s ∉ Set.Ioo (Real.pi / 2) (θ + ε) := fun h => by linarith [h2.2, h.1]
      rw [Set.indicator_of_notMem (fun h => h1 (hmL.mp h)), Set.indicator_of_mem (hmM.mpr h2),
        Set.indicator_of_notMem (fun h => h3 (hmR.mp h)), Sl2_apply,
        qext_mem' G (Real.exp t) s ⟨h2.1.le, h2.2.le⟩]
      ring
    · by_cases h3 : s ∈ Set.Ioo (Real.pi / 2) (θ + ε)
      · -- right branch
        rw [Set.indicator_of_notMem (fun h => h1 (hmL.mp h)),
          Set.indicator_of_notMem (fun h => h2 (hmM.mp h)),
          Set.indicator_of_mem (hmR.mpr h3), Sl3_apply, qext_pihalf_lt' G (Real.exp t) s h3.1]
        ring
      · -- outside the window: `k (θ - s) = 0` and all three indicators vanish
        have hnot : ¬ (θ - ε < s ∧ s < θ + ε) := by
          rintro ⟨hlt, hgt⟩
          rcases lt_trichotomy s 0 with h | h | h
          · exact h1 ⟨hlt, h⟩
          · exact hs (by rw [h]; simp)
          · rcases lt_trichotomy s (Real.pi / 2) with h' | h' | h'
            · exact h2 ⟨h, h'⟩
            · exact hs (by rw [h']; simp)
            · exact h3 ⟨h', hgt⟩
        rw [not_and_or, not_lt, not_lt] at hnot
        have hk0 : k (θ - s) = 0 := by
          apply hvan
          rcases hnot with h | h
          · have hlt : s < θ - ε := lt_of_le_of_ne h hneL
            calc ε < θ - s := by linarith
              _ ≤ |θ - s| := le_abs_self _
          · have hlt : θ + ε < s := lt_of_le_of_ne h (Ne.symm hneR)
            calc ε < s - θ := by linarith
              _ ≤ |s - θ| := le_abs_self _
              _ = |θ - s| := abs_sub_comm _ _
        rw [Set.indicator_of_notMem (fun h => h1 (hmL.mp h)),
          Set.indicator_of_notMem (fun h => h2 (hmM.mp h)),
          Set.indicator_of_notMem (fun h => h3 (hmR.mp h)), hk0, zero_mul]
        ring

/-! ## Joint measurability of the three-piece representative -/

private lemma aesm_sliceSum (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G)
    {k : ℝ → ℝ} (hk : Continuous k) {ε θ : ℝ}
    (ha : -(Real.pi / 2) < θ - ε) (hb : θ + ε < Real.pi) :
    AEStronglyMeasurable (SliceSum G k θ ε) (volume.prod volume) := by
  have hcont : ContinuousOn (Function.uncurry G) Work.FTS.EllipticEst.Q0 := hS.continuousOn
  have hK : ContinuousOn (fun p : ℝ × ℝ => k (θ - p.2)) (SlSet θ ε) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ => k (θ - p.2)).continuousOn
  have hg1 : ContinuousOn (fun p : ℝ × ℝ => Function.uncurry G (Real.exp p.1, -p.2))
      (SlSet θ ε) := by
    refine ContinuousOn.comp hcont ?_ ?_
    · fun_prop
    · intro p hp
      simp only [SlSet, Set.mem_prod, Set.mem_univ, true_and, Set.mem_Ioo] at hp
      rw [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨Real.exp_pos p.1, by linarith [hp.2], by linarith [ha, hp.1]⟩
  have hc1 : ContinuousOn (Sl1 G k θ) (SlSet θ ε) := hK.mul hg1.neg
  have hg2 : ContinuousOn (fun p : ℝ × ℝ => Function.uncurry G (Real.exp p.1, p.2))
      (SmSet θ ε) := by
    refine ContinuousOn.comp hcont ?_ ?_
    · fun_prop
    · intro p hp
      simp only [SmSet, Set.mem_prod, Set.mem_univ, true_and, Set.mem_Ioo] at hp
      rw [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨Real.exp_pos p.1, hp.1, hp.2⟩
  have hK2 : ContinuousOn (fun p : ℝ × ℝ => k (θ - p.2)) (SmSet θ ε) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ => k (θ - p.2)).continuousOn
  have hc2 : ContinuousOn (Sl2 G k θ) (SmSet θ ε) := hK2.mul hg2
  have hg3 : ContinuousOn (fun p : ℝ × ℝ => Function.uncurry G (Real.exp p.1, Real.pi - p.2))
      (SrSet θ ε) := by
    refine ContinuousOn.comp hcont ?_ ?_
    · fun_prop
    · intro p hp
      simp only [SrSet, Set.mem_prod, Set.mem_univ, true_and, Set.mem_Ioo] at hp
      rw [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨Real.exp_pos p.1, by linarith [hb, hp.2], by linarith [hp.1]⟩
  have hK3 : ContinuousOn (fun p : ℝ × ℝ => k (θ - p.2)) (SrSet θ ε) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ => k (θ - p.2)).continuousOn
  have hc3 : ContinuousOn (Sl3 G k θ) (SrSet θ ε) := hK3.mul hg3.neg
  have hLm : MeasurableSet (SlSet θ ε) := by
    rw [SlSet]; exact MeasurableSet.univ.prod isOpen_Ioo.measurableSet
  have hMm : MeasurableSet (SmSet θ ε) := by
    rw [SmSet]; exact MeasurableSet.univ.prod isOpen_Ioo.measurableSet
  have hRm : MeasurableSet (SrSet θ ε) := by
    rw [SrSet]; exact MeasurableSet.univ.prod isOpen_Ioo.measurableSet
  have h1 : AEStronglyMeasurable ((SlSet θ ε).indicator (Sl1 G k θ)) (volume.prod volume) :=
    (aestronglyMeasurable_indicator_iff hLm).mpr (hc1.aestronglyMeasurable hLm)
  have h2 : AEStronglyMeasurable ((SmSet θ ε).indicator (Sl2 G k θ)) (volume.prod volume) :=
    (aestronglyMeasurable_indicator_iff hMm).mpr (hc2.aestronglyMeasurable hMm)
  have h3 : AEStronglyMeasurable ((SrSet θ ε).indicator (Sl3 G k θ)) (volume.prod volume) :=
    (aestronglyMeasurable_indicator_iff hRm).mpr (hc3.aestronglyMeasurable hRm)
  have h12 := h1.add h2
  exact h12.add h3

theorem hxycSliceAESM (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G)
    {k : ℝ → ℝ} (hk : Continuous k) {ε θ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hvan : ∀ x : ℝ, ε < |x| → k x = 0)
    (hθ : θ ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4)) :
    MeasureTheory.AEStronglyMeasurable (fun t : ℝ => ∫ s : ℝ, k (θ - s) *
      Work.FTS.EllSol.EllPkgAux.Hxyc G t s) MeasureTheory.volume := by
  -- the window `(θ - ε, θ + ε)` lies in `(-π/2, π)`
  have ha : -(Real.pi / 2) < θ - ε := by linarith [hθ.1, hε1, Real.pi_gt_three]
  have hb : θ + ε < Real.pi := by linarith [hθ.2, hε1, Real.pi_gt_three]
  have hΨ : AEStronglyMeasurable (SliceSum G k θ ε) (volume.prod volume) :=
    aesm_sliceSum G hS hk ha hb
  have hInt : AEStronglyMeasurable (fun t : ℝ => ∫ s : ℝ, SliceSum G k θ ε (t, s)) volume :=
    hΨ.integral_prod_right'
  refine hInt.congr (Filter.Eventually.of_forall fun t => ?_)
  -- for every `t`, the two integrands agree a.e. in `s` (they can only differ on a finite set)
  have hae : (fun s : ℝ => SliceSum G k θ ε (t, s)) =ᵐ[volume]
      (fun s : ℝ => k (θ - s) * Work.FTS.EllSol.EllPkgAux.Hxyc G t s) := by
    filter_upwards [((by simp : ({0, Real.pi / 2, θ - ε, θ + ε} : Set ℝ).Countable).ae_notMem
      volume)] with s hs
    exact slice_eq G hvan hs
  exact MeasureTheory.integral_congr_ae hae

end Work.FTS.ClassC.RopGen.Trace.ZmollAux
