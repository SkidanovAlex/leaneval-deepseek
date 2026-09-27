import Mathlib
import Submission.Work.Drive.PushDisc.lensWiringDefs
import Submission.Work.Drive.PushDisc.lensWiringConfig
import Submission.Work.Drive.PushDisc.lensCornerSignOfCharts
import Submission.Work.Drive.PushDisc.smoothChartOfInjOnImmersion
import Submission.Work.Drive.PushDisc.exists_contDiff_eqOn_of_contDiffOn
import Submission.Work.Drive.PushDisc.chartSplitSafe

/-!
# The finger's parametrisation `S₂` of the lens wiring

`LWFingerData` bundles the globally smooth parametrisation `S₂` of the finger (the second sheet of
the Whitney bigon) in the flat-tube chart `Φ₀`, its `w`-frame `V`, and the four rows on the
**window** `|x| ≤ X'`, `‖v‖ ≤ r` of the finger chart `F`:

* `S₂` agrees on the window with the chart parametrisation `p ↦ Φ₀ (f (c.symm (splitE p)));
* so does its derivative;
* `S₂` is injective and immersive on the window;
* the `w`-derivative of `S₂` at `(x, 0)` is `∑ j, w j • V x j`.

The parametrisation is the standard cutoff extension of a function smooth on an open neighbourhood
of a compact set (`exists_contDiff_eqOn_of_contDiffOn`), which is why the rows hold on the whole
window: the window is compact and lies inside the target of the chart, where the composite is
smooth.  Injectivity of `S₂` on the window is the cleanliness of the bigon (the chart's source
avoids `p₁` and `q₁`, so `f` is injective on it), and the immersion row is the chart
parametrisation lemma `injective_fderiv_chartSplitSafe`.
-/

/-!
# The finger's parametrisation `S₂` (variant using `chartSplitSafe`)

The same statement as `Work.Drive.PushDisc.fingerDataSolid`, proved against
`Submission.Work.Drive.PushDisc.chartSplitSafe` so that the module can be imported together with the
`firstSheet_xyJet_signCoherence` side of the tree (name-clash-free).
-/

namespace Work.Drive.PushDisc

open scoped ContDiff Manifold
open Set Metric Filter

noncomputable section

/-- The **window** of the finger's chart: `|x| ≤ X'` and `‖v‖ ≤ r`. -/
def fingerWindow (k : ℕ) (X' r : ℝ) : Set (ℝ × EuclideanSpace ℝ (Fin k)) :=
  {p | |p.1| ≤ X' ∧ ‖p.2‖ ≤ r}

/-- The window is compact (it is a product of closed balls). -/
theorem isCompact_fingerWindow (k : ℕ) {X' r : ℝ} :
    IsCompact (fingerWindow k X' r) := by
  have heq : fingerWindow k X' r =
      (Set.Icc (-X') X') ×ˢ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) r) := by
    ext p
    simp only [fingerWindow, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Icc, Metric.mem_closedBall,
      dist_zero_right]
    constructor
    · intro h
      exact ⟨⟨(abs_le.mp h.1).1, (abs_le.mp h.1).2⟩, h.2⟩
    · intro h
      exact ⟨abs_le.mpr ⟨h.1.1, h.1.2⟩, h.2⟩
  rw [heq]
  exact isCompact_Icc.prod (isCompact_closedBall _ _)

/-- **The `w`-frame of a smooth map on `ℝ × ℝ^k`.**  For a `C^∞` map `S`, the derivative of the
slice `w' ↦ S (x, w')` at `0` is `w ↦ ∑ j, w j • V x j` for the `C^∞` family
`V x j = (fderiv S (x,0)) (0, e_j)`. -/
theorem exists_contDiff_sliceV {k : ℕ}
    (S : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k)
    (hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S) :
    ∃ V : ℝ → Fin k → Work.Drive.Whitney.Mdl k,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧
      ∀ (x : ℝ) (w : EuclideanSpace ℝ (Fin k)),
        (fderiv ℝ (fun w' : EuclideanSpace ℝ (Fin k) => S (x, w')) 0) w
          = ∑ j : Fin k, w j • V x j := by
  have hsingle : ∀ w : EuclideanSpace ℝ (Fin k),
      (∑ j : Fin k, w j • EuclideanSpace.single j (1 : ℝ)) = w := by
    intro w
    have h : WithLp.ofLp (∑ i : Fin k, w i • EuclideanSpace.single i (1 : ℝ)) = WithLp.ofLp w := by
      rw [WithLp.ofLp_sum, WithLp.ofLp]
      ext j
      simp [Finset.sum_apply, PiLp.ofLp_single, Pi.single_apply, Finset.sum_ite_eq]
    exact (WithLp.equiv 2 (Fin k → ℝ)).injective h
  let V : ℝ → Fin k → Work.Drive.Whitney.Mdl k := fun x j =>
    (fderiv ℝ S (x, 0)) (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin k))
      (EuclideanSpace.single j (1 : ℝ)))
  refine ⟨V, ?_, ?_⟩
  · have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ S) := hS.fderiv_right (by simp)
    have h0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => fderiv ℝ S (x, 0)) := by
      simpa [Function.comp_def] using hfd.comp (by fun_prop :
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : ℝ => (x, (0 : EuclideanSpace ℝ (Fin k)))))
    exact contDiff_pi.mpr (fun j => h0.clm_apply contDiff_const)
  · intro x w
    have hslice : fderiv ℝ (fun w' : EuclideanSpace ℝ (Fin k) => S (x, w')) 0
        = (fderiv ℝ S (x, 0)).comp (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin k))) := by
      have hg : HasFDerivAt (fun w' : EuclideanSpace ℝ (Fin k) => (x, w'))
          (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin k))) 0 :=
        hasFDerivAt_prodMk_right x 0
      have hf : HasFDerivAt S (fderiv ℝ S (x, 0)) (x, 0) :=
        ((hS.differentiable (by simp)).differentiableAt).hasFDerivAt
      have hcomp := hf.comp 0 hg
      simpa [Function.comp_def] using hcomp.fderiv
    have hmain : (fderiv ℝ S (x, 0))
          (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin k)) w)
        = ∑ j : Fin k, w j • (fderiv ℝ S (x, 0))
            (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin k))
              (EuclideanSpace.single j (1 : ℝ))) := by
      set L : EuclideanSpace ℝ (Fin k) →L[ℝ] Work.Drive.Whitney.Mdl k :=
        (fderiv ℝ S (x, 0)).comp (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin k)))
      change L w = ∑ j : Fin k, w j • L (EuclideanSpace.single j (1 : ℝ))
      conv_lhs => rw [← hsingle w]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smul]
    rw [hslice, ContinuousLinearMap.comp_apply]
    exact hmain

/-- **The window lies in the chart's target.**  For `|x| ≤ X'` and `‖v‖ ≤ r` the rescaled point
`(x, r⁻¹ v)` has its second coordinate of norm `≤ 1`, so the window row `F.hwin` applies. -/
theorem fingerWindow_mem_target {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (C : LWConfig (k + 1) M) (F : LWFingerChart k M C) :
    ∀ p ∈ fingerWindow k F.X' F.r, splitE k p ∈ F.c.target := by
  intro p hp
  obtain ⟨h1, h2⟩ := hp
  have hnorm : ‖F.r⁻¹ • p.2‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos F.hr]
    calc F.r⁻¹ * ‖p.2‖ ≤ F.r⁻¹ * F.r :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr F.hr.le)
      _ = 1 := by rw [inv_mul_cancel₀ (ne_of_gt F.hr)]
  have hwin := F.hwin (p.1, F.r⁻¹ • p.2) h1 hnorm
  have hp' : (p.1, F.r • (F.r⁻¹ • p.2)) = p := by
    refine Prod.ext rfl ?_
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt F.hr), one_smul]
  rwa [hp'] at hwin

/-- **`f` is injective on the finger chart's source.**  Both the source and the cleanliness row
give membership in `W`, and the source avoids `p₁` and `q₁`, so all four exceptional pairs of the
cleanliness row are excluded. -/
theorem f_injOn_chartSource {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (C : LWConfig (k + 1) M) (F : LWFingerChart k M C) :
    Set.InjOn C.f F.c.source := by
  intro y hy z hz hyz
  rcases C.hclean y z (F.hcsrc hy) (F.hcsrc hz) hyz with h | h | h | h | h
  · exact h
  · exact absurd (h.1 ▸ hy) F.hp₁c
  · exact absurd (h.2 ▸ hz) F.hp₁c
  · exact absurd (h.1 ▸ hy) F.hq₁c
  · exact absurd (h.2 ▸ hz) F.hq₁c

/-- **The chart parametrisation of the finger is injective on the window**: `Φ₀` is injective, `f`
is injective on the chart's source, and `c.symm ∘ splitE` is injective. -/
theorem fingerFormula_injOn {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (C : LWConfig (k + 1) M) (T : LWFlatTube k M C) (F : LWFingerChart k M C) :
    Set.InjOn (fun q : ℝ × EuclideanSpace ℝ (Fin k) => T.Φ₀ (C.f (F.c.symm (splitE k q))))
      (fingerWindow k F.X' F.r) := by
  have hΦinj : Function.Injective T.Φ₀ := fun a b hab => by
    rw [← T.hΘ₀Φ₀ a, hab, T.hΘ₀Φ₀ b]
  intro p hp q hq hpq
  have hpmem : splitE k p ∈ F.c.target := fingerWindow_mem_target C F p hp
  have hqmem : splitE k q ∈ F.c.target := fingerWindow_mem_target C F q hq
  have h1 : C.f (F.c.symm (splitE k p)) = C.f (F.c.symm (splitE k q)) := hΦinj hpq
  have h2 : F.c.symm (splitE k p) = F.c.symm (splitE k q) :=
    f_injOn_chartSource C F (F.c.map_target hpmem) (F.c.map_target hqmem) h1
  have h3 : splitE k p = splitE k q := by
    have hh := congrArg (fun x => F.c x) h2
    rwa [F.c.right_inv hpmem, F.c.right_inv hqmem] at hh
  exact (splitE k).injective h3

theorem fingerDataSolidSafe {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (C : Work.Drive.PushDisc.LWConfig (k + 1) M)
    (T : Work.Drive.PushDisc.LWFlatTube k M C)
    (F : Work.Drive.PushDisc.LWFingerChart k M C) :
    Nonempty (Work.Drive.PushDisc.LWFingerData k M C T F) := by
  classical
  -- the chart parametrisation is smooth on the preimage of the chart's target
  have hU : IsOpen ((splitE k) ⁻¹' F.c.target) :=
    F.c.open_target.preimage (LinearMap.continuous_of_finiteDimensional (splitE k).toLinearMap)
  have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin k) => T.Φ₀ (C.f (F.c.symm (splitE k q))))
      ((splitE k) ⁻¹' F.c.target) := by
    have hΦuniv : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin (2 * (k + 1))) => T.Φ₀ y) Set.univ :=
      ((contMDiff_iff_contDiff).mpr T.hΦ₀sm).contMDiffOn
    have hcsymm : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : EuclideanSpace ℝ (Fin (k + 1)) => F.c.symm u) F.c.target := F.hcsmooth.2
    have hfuniv : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : M => C.f y) Set.univ := C.hf.contMDiffOn
    have hfon : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : EuclideanSpace ℝ (Fin (k + 1)) => C.f (F.c.symm u)) F.c.target :=
      ContMDiffOn.comp hfuniv hcsymm (fun u _ => Set.mem_univ _)
    have hgon : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : EuclideanSpace ℝ (Fin (k + 1)) => T.Φ₀ (C.f (F.c.symm u))) F.c.target :=
      ContMDiffOn.comp hΦuniv hfon (fun u _ => Set.mem_univ _)
    have hgfull : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : EuclideanSpace ℝ (Fin (k + 1)) => T.Φ₀ (C.f (F.c.symm u))) F.c.target :=
      (contMDiffOn_iff_contDiffOn).mp hgon
    have hsplit : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × EuclideanSpace ℝ (Fin k) => splitE k q) := by
      have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          ⇑(LinearEquiv.toContinuousLinearEquiv (splitE k)) := ContinuousLinearEquiv.contDiff _
      simpa using hh
    exact hgfull.comp hsplit.contDiffOn (fun q hq => hq)
  -- the cutoff extension of the chart parametrisation off the compact window
  obtain ⟨S₂, hS₂sm, hS₂eq, hS₂d⟩ :=
    exists_contDiff_eqOn_of_contDiffOn (K := fingerWindow k F.X' F.r)
      (U := (splitE k) ⁻¹' F.c.target) (isCompact_fingerWindow k) hU
      (fingerWindow_mem_target C F) hg
  -- its `w`-frame
  obtain ⟨V, hVsm, hVrow⟩ := exists_contDiff_sliceV S₂ hS₂sm
  refine ⟨⟨S₂, hS₂sm, ?_, ?_, ?_, ?_, V, hVsm, ?_⟩⟩
  · intro p hp1 hp2
    exact hS₂eq p ⟨hp1, hp2⟩
  · intro p hp1 hp2
    exact hS₂d p ⟨hp1, hp2⟩
  · intro p hp q hq hpq
    have hpq' : T.Φ₀ (C.f (F.c.symm (splitE k p)))
        = T.Φ₀ (C.f (F.c.symm (splitE k q))) := by
      rw [← hS₂eq p hp, ← hS₂eq q hq]
      exact hpq
    exact fingerFormula_injOn C T F hp hq hpq'
  · intro p hp
    rw [hS₂d p hp]
    exact injective_fderiv_chartSplitSafe C.hf C.himm T.hΦ₀sm T.hΘ₀sm T.hΘ₀Φ₀ F.c F.hcsmooth
      (fingerWindow_mem_target C F p hp)
  · intro x w _
    exact hVrow x w

end

end Work.Drive.PushDisc
