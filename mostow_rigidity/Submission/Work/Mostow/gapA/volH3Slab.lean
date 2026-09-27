import Mathlib
import Submission.Work.Mostow.gapA.slabDefs
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.gapA.geodFacts
import Submission.Work.Mostow.fermi_inv
import Submission.Work.Mostow.gapA.chartPtFacts
import Submission.Work.Mostow.gapA.coshHdistChartPt
import Submission.Work.Mostow.gapA.coshHdistFermi12
import Submission.Work.Mostow.gapA.tubeMeasure12Ball
import Submission.Work.Mostow.gapA.volH1Ico
import Submission.Work.Mostow.gapA.slabMeasurable
import Submission.Work.Mostow.gapA.fermiSlabImage
import Submission.Work.Mostow.volH_fermi_prod

/-!
# The volume of a Fermi slab of `ℍ³` (`Work.Mostow.gapA.volH3Slab`)

The Fermi slab `{s ≤ sig a b u < s + L, distGeod a b u ≤ R}` around the geodesic joining two
distinct boundary points `a ≠ b` of `ℍ³` has volume `L · π · sinh²R`:
in Fermi coordinates `(σ, r, φ)` about the geodesic the volume element is
`cosh r · sinh r · dσ dr dφ`, and the slab is `σ ∈ [s, s+L]`, `r ∈ [0, R]`.

The proof transports the standard Fermi chart `fermi 1 2` (about the standard geodesic of
`stdTG 1 2`) to the geodesic `geodSet a b` by the explicit chart map `chartMap a b B`, shows
that this map is an isometry (hence of the form `u ↦ g • u`), and computes the volume of the
transported region with `fermi_measurePreserving`.
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- An orthonormal (Minkowski) basis of the normal plane `NormSub a b` of a geodesic exists. -/
theorem exists_axisBasis_volH3Slab (a b : E 3) (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) :
    ∃ B : AxisBasis a b, True := by
  obtain ⟨E1, E2, h1, h2, h11, h22, h12, hsp, hspV⟩ :=
    normSub_orthonormalBasis a b ha hb hab
  exact ⟨⟨E1, E2, h1, h2, h11, h22, h12,
    fun Z hZ => ⟨mink Z E1, mink Z E2, hsp Z hZ⟩, hspV⟩, trivial⟩

/-- `sig` of a point of the `(a,b)` Fermi chart. -/
theorem sig_chartMap (a b : E 3) (B : AxisBasis a b) (ha : a ∈ Sph 3) (hb : b ∈ Sph 3)
    (hab : a ≠ b) (u : E 3) :
    sig a b (chartMap a b B u) = Real.arsinh ((fermiInv 1 2 u).1 0) :=
  (chartPtFacts a b B ha hb hab (fermiInv 1 2 u).1 (fermiInv 1 2 u).2).2.1

/-- `distGeod` of a point of the `(a,b)` Fermi chart. -/
theorem distGeod_chartMap (a b : E 3) (B : AxisBasis a b) (ha : a ∈ Sph 3) (hb : b ∈ Sph 3)
    (hab : a ≠ b) (u : E 3) :
    distGeod a b (chartMap a b B u) = ‖(fermiInv 1 2 u).2‖ :=
  (chartPtFacts a b B ha hb hab (fermiInv 1 2 u).1 (fermiInv 1 2 u).2).2.2

/-- The Fermi chart change of variables preserves the hyperbolic distance. -/
theorem chartMap_hdist (hA : POActionProp 3) (hI : HypIsometryProp 3) (a b : E 3)
    (B : AxisBasis a b) (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) (u v : E 3) :
    hdist (chartMap a b B u) (chartMap a b B v) = hdist u v := by
  have hId : HypIsoData 3 := HypIsoData.ofProp hI
  have hcosh : Real.cosh (hdist (chartMap a b B u) (chartMap a b B v))
      = Real.cosh (hdist u v) := by
    have hu : u = fermi 1 2 (fermiInv 1 2 u).1 (fermiInv 1 2 u).2 :=
      ((fermi_inv 1 2).2.1 u).symm
    have hv : v = fermi 1 2 (fermiInv 1 2 v).1 (fermiInv 1 2 v).2 :=
      ((fermi_inv 1 2).2.1 v).symm
    show Real.cosh (hdist (chartPt a b B (fermiInv 1 2 u).1 (fermiInv 1 2 u).2)
        (chartPt a b B (fermiInv 1 2 v).1 (fermiInv 1 2 v).2)) = Real.cosh (hdist u v)
    rw [coshHdistChartPt a b B ha hb hab]
    conv_rhs => rw [hu, hv]
    rw [coshHdistFermi12]
  exact Real.cosh_injOn (hId.nonneg _ _) (hId.nonneg _ _) hcosh

/-- The chart map is realised by an isometry of `ℍ³`. -/
theorem exists_chartMap_eq_smul (hA : POActionProp 3) (hI : HypIsometryProp 3) (a b : E 3)
    (B : AxisBasis a b) (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) :
    ∃ g : PO 3 1, ∀ u : E 3, chartMap a b B u = g • u :=
  (HypIsoData.ofProp hI).surj_isom (chartMap a b B) (chartMap_hdist hA hI a b B ha hb hab)

/-- **The volume of a Fermi slab.** -/
theorem volH3Slab (hA : Submission.Mostow.POActionProp 3) (hI : Submission.Mostow.HypIsometryProp 3)
    (a b : Submission.Mostow.E 3) (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3)
    (hab : a ≠ b) (M : ℕ) (hM : 0 < M) (b₀ : LeanEval.Geometry.MostowRigidity.PO 3 1)
    (hrot : Work.Mostow.IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)))
    (s L R : ℝ) (hL : 0 ≤ L) (hR : 0 ≤ R) :
    (Submission.Mostow.volH 3)
        {u : Submission.Mostow.E 3 | Work.Mostow.gapA.sig a b u ∈ Set.Ico s (s + L) ∧
          Work.Mostow.distGeod a b u ≤ R}
      = ENNReal.ofReal (L * Real.pi * Real.sinh R ^ 2) := by
  obtain ⟨B, -⟩ := exists_axisBasis_volH3Slab a b ha hb hab
  obtain ⟨g, hg⟩ := exists_chartMap_eq_smul hA hI a b B ha hb hab
  have hId : HypIsoData 3 := HypIsoData.ofProp hI
  set T : Set (E 3) := {u : E 3 | sig a b u ∈ Set.Ico s (s + L) ∧ distGeod a b u ≤ R} with hT
  set Se : Set (E 3) := {x : E 3 | Real.arsinh ((fermiInv 1 2 x).1 0) ∈ Set.Ico s (s + L) ∧
      ‖(fermiInv 1 2 x).2‖ ≤ R} with hSe
  set Iv : Set (E 1) := {v : E 1 | v 0 ∈ Set.Ico (Real.sinh s) (Real.sinh (s + L))} with hIv
  set Bl : Set (E 2) := Metric.closedBall (0 : E 2) R with hBl
  have hTmeas : MeasurableSet T := by
    rw [hT]; exact slabMeasurable a b ha hb s L R
  have hpre : (fun x : E 3 => g • x) ⁻¹' T = Se := by
    ext x
    rw [Set.mem_preimage, hSe, hT]
    simp only [Set.mem_setOf_eq]
    have h1 : sig a b (g • x) = Real.arsinh ((fermiInv 1 2 x).1 0) := by
      rw [← hg x]; exact sig_chartMap a b B ha hb hab x
    have h2 : distGeod a b (g • x) = ‖(fermiInv 1 2 x).2‖ := by
      rw [← hg x]; exact distGeod_chartMap a b B ha hb hab x
    rw [h1, h2]
  have hvol1 : (volH 3) T = (volH 3) Se := by
    rw [← hpre]
    exact ((hId.measurePreserving_smul g).measure_preimage hTmeas.nullMeasurableSet).symm
  have hSeimg : Se = (fun p : E 1 × E 2 => fermi 1 2 p.1 p.2) '' (Iv ×ˢ Bl) := by
    rw [hSe, hIv, hBl]; exact fermiSlabImage s L R
  have hIvmeas : MeasurableSet Iv := by
    rw [hIv]
    refine measurableSet_Ico.preimage ?_
    have hof : Continuous (WithLp.ofLp : E 1 → (Fin 1 → ℝ)) :=
      PiLp.continuous_ofLp 2 (fun _ : Fin 1 => ℝ)
    exact ((continuous_apply (0 : Fin 1)).comp hof).measurable
  have hBlmeas : MeasurableSet Bl := by
    rw [hBl]; exact Metric.isClosed_closedBall.measurableSet
  have hvol2 : (volH 3) Se = (volH 1) Iv * (tubeMeasure 1 2) Bl := by
    rw [hSeimg]
    exact volH_fermi_prod 1 2 Iv Bl hIvmeas hBlmeas
  have hIval : (volH 1) Iv
      = ENNReal.ofReal (Real.arsinh (Real.sinh (s + L)) - Real.arsinh (Real.sinh s)) := by
    rw [hIv]
    exact volH1Ico (Real.sinh s) (Real.sinh (s + L)) (Real.sinh_le_sinh.mpr (by linarith))
  have hBval : (tubeMeasure 1 2) Bl = ENNReal.ofReal (Real.pi * Real.sinh R ^ 2) := by
    rw [hBl]; exact tubeMeasure12Ball R hR
  rw [hvol1, hvol2, hIval, hBval, Real.arsinh_sinh, Real.arsinh_sinh,
    show (s + L) - s = L from by ring, ← ENNReal.ofReal_mul hL]
  congr 1
  ring

end

end Work.Mostow.gapA
