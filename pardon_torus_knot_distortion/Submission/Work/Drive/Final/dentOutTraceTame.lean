import Mathlib
import Submission.Work.Drive.Final.dentOut_trace
import Submission.Work.Drive.Mono.SweepGeom3
import Submission.Work.Drive.Final.dent_annulus_margin
import Submission.Work.Drive.Final.dent_annulus_regular
import Submission.Work.Drive.Final.dentDeform_homeomorph
import Submission.Work.Drive.Final.trace_localModel_of_event_off

import Submission.Work.Drive.Mono.IsLocallyEuclidean_trace_spherePoint_holds
import Submission.Work.Drive.Final.trace_localModel_inBox
import Submission.Work.Drive.Final.exists_dentSurface
import Submission.Work.Drive.Final.dent_frontier_shift_core
import Submission.Work.Drive.Final.hdirDeformed
import Submission.Work.Drive.Final.boxSphereWallJunctionLocalModel
import Submission.Work.Drive.Final.isLocallyEuclidean_preimage_homeomorph
import Submission.Work.Drive.Mono.LocalEuclideanTrace_of_traceCurves
import Submission.Work.Drive.Final.dentOut_hgen
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Drive.Final

noncomputable section

open Set

variable {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
  {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}

/-- The deformation of a dent is the identity outside the closed ball of radius `r`. -/
theorem deform_eq_self_of_ge (D : AnyDentDatum ψ K s c σ u v h R ℓ U) {y : R3}
    (hy : D.r ≤ ‖y - D.centre‖) : D.deform y = y :=
  dentDeform_eq_self_of_le D.r_pos D.χ_eq_zero hy

/-- On the core `‖y - centre‖ < r / 2` the deformation is the translation by `a' • d`. -/
theorem deform_eq_translate_of_lt (D : AnyDentDatum ψ K s c σ u v h R ℓ U)
    (hχ1 : ∀ t : ℝ, |t| ≤ 1 / 2 → D.χ t = 1) {y : R3} (hy : ‖y - D.centre‖ < D.r / 2) :
    D.deform y = y + D.a' • D.d := by
  rw [AnyDentDatum.deform, dentDeform]
  have hchi : D.χ (‖y - D.centre‖ / D.r) = 1 := by
    apply hχ1
    rw [abs_of_nonneg (div_nonneg (norm_nonneg _) D.r_pos.le), div_le_iff₀ D.r_pos]
    linarith
  rw [hchi, mul_one]

/-- The slab functional is invariant under the deformation of the dent. -/
theorem inner_deform_eq (D : AnyDentDatum ψ K s c σ u v h R ℓ U) (y : R3) :
    inner ℝ v (D.deform y) = inner ℝ v y := by
  rw [AnyDentDatum.deform, dentDeform, inner_add_right, inner_smul_right, D.d_orth_v, mul_zero,
    add_zero]

/-- The deformation preserves membership in the open box (globally). -/
theorem deform_mem_PBox_iff (D : AnyDentDatum ψ K s c σ u v h R ℓ U) (y : R3) :
    D.deform y ∈ Submission.PBox s c σ ↔ y ∈ Submission.PBox s c σ := by
  rcases lt_or_ge ‖y - D.centre‖ D.r with hy | hy
  · exact (D.box_pres y (le_of_lt hy)).symm
  · rw [deform_eq_self_of_ge D hy]

/-- The deformation preserves the closed slab (in the `tiltedSlabClosed` spelling). -/
theorem deform_mem_tiltedSlabClosed (D : AnyDentDatum ψ K s c σ u v h R ℓ U) (y : R3) :
    D.deform y ∈ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ↔
      y ∈ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h := by
  simp only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq]
  rw [inner_deform_eq D y]

/-- The preimage of the removed set of a level under the deformation of the dent, in the *hybrid*
form: the undeformed box and slab, and the *deformed* wall. -/
theorem deform_preimage_tiltedLevelRemoved (D : AnyDentDatum ψ K s c σ u v h R ℓ U) :
    D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre) =
      Submission.PBox s c σ \
        (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
          {y : R3 | ℓ (D.deform y) < ℓ D.centre}) := by
  rw [Work.Drive.Mono.tiltedLevelRemoved]
  ext y
  simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [deform_mem_PBox_iff D y, deform_mem_tiltedSlabClosed D y]

/-- Restricting a locally Euclidean set to an open set. -/
theorem isLocallyEuclidean_inter_isOpen {Z W : Set R3} (hW : IsOpen W)
    (h : Work.Smooth.OneManifold.IsLocallyEuclidean Z) :
    Work.Smooth.OneManifold.IsLocallyEuclidean (W ∩ Z) := by
  refine h.of_isOpenIn Set.inter_subset_right ?_
  show IsOpen (Subtype.val ⁻¹' (W ∩ Z) : Set Z)
  rw [show (Subtype.val ⁻¹' (W ∩ Z) : Set Z) = Subtype.val ⁻¹' W from ?_]
  · exact hW.preimage continuous_subtype_val
  · ext y; exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩

/-- **The surface's part of the box sphere is locally Euclidean** from a slicing of the box sphere
by the surface. -/
theorem carrier_inter_sphereSet_isLocallyEuclidean {P : Work.CoreTopology.ParamTorus} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {s : ℝ}
    (h : Work.InnermostDisk.SphereSlicing P (Work.BoxShrink.Core.sphereSet c σ s)) :
    Work.Smooth.OneManifold.IsLocallyEuclidean (P.carrier ∩ Work.BoxShrink.Core.sphereSet c σ s) := by
  have hset : P.carrier ∩ Work.BoxShrink.Core.sphereSet c σ s = ⋃ i, Set.range (h.c i).γ := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
        (Work.InnermostDisk.carrier_inter_subset_iUnion_range_of_sphereSlicing h hy)
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    · intro y hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      exact ⟨(h.c i).range_subset_carrier hi, by obtain ⟨t, rfl⟩ := hi; exact h.mem i t⟩
  rw [hset]
  refine Work.Drive.Mono.isLocallyEuclidean_iUnion_of_isClosed_pairwise_disjoint
    (F := fun i => Set.range (h.c i).γ) ?_ ?_ ?_
  · intro i
    rw [Work.Drive.Mono.closedCurve_range_eq_image_Icc]
    exact (isCompact_Icc.image (h.c i).cont).isClosed
  · intro i j hij
    exact h.disjoint hij
  · intro i
    exact Work.EpsW.localEuclidean_range_of_periodic_injOn (h.c i).cont (h.c i).periodic (h.simple i)

/-- The frontier of two sets that agree on an open set agrees there. -/
theorem frontier_inter_open_eq {S S' V : Set R3} (hV : IsOpen V) (h : S ∩ V = S' ∩ V) :
    frontier S ∩ V = frontier S' ∩ V := by
  rw [← frontier_inter_open_inter hV (s := S), h, frontier_inter_open_inter hV (s := S')]

/-- The box norm is at most `s` on the closure of the box. -/
theorem boxNorm_le_of_mem_closure_PBox {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {y : R3}
    (hy : y ∈ closure (Submission.PBox s c σ)) : Submission.boxNorm c σ y ≤ s :=
  closure_minimal (fun _ hz => le_of_lt ((Submission.mem_PBox_iff s c σ _).mp hz))
    (isClosed_le (Work.Topology.SphereSlicing.frontier_PBox_boxNorm_continuous c σ)
      continuous_const) hy

/-- **The exterior of the dent's ball**: the trace of the deformed removed set is the undeformed
trace there, and the undeformed local model applies. -/
theorem dentOutTrace_exterior
    {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : R3 →L[ℝ] ℝ} {U : Set R3} {exc : Finset ℝ} {lam0 lam1 : ℝ} {p q : ℕ}
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U)
    (hwin0 : lam0 ≤ ℓ D.centre) (hwin1 : ℓ D.centre ≤ lam1)
    {x : R3}
    (hx : x ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)))
    (hρ : D.r < ‖x - D.centre‖) :
    ∃ V : Set R3, IsOpen V ∧ x ∈ V ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (V ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)))) := by
  classical
  obtain ⟨hxc, hxfr⟩ := hx
  have hG3 : Work.Drive.Final.GoodSweepData3 ψ K s c σ u v h R ℓ exc lam0 lam1 := hDP.2.1
  obtain ⟨-, -, -, -, -, -, -, -, hone, -⟩ := hG3
  set Rm : Set R3 := Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre) with hRmdef
  have hnoev : ∀ qq : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ qq = x →
      ℓ (Work.BoxShrink.Pinch.par ψ qq) = ℓ D.centre →
      ¬ Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ qq := by
    intro qq hq hℓq hev
    have h2 := hone qq D.p hev D.isEvent (by rw [hℓq, D.centre_eq])
    rw [← D.centre_eq] at h2
    have h3 : ‖x - D.centre‖ = 0 := by rw [← h2, ← hq]; simp
    rw [h3] at hρ
    linarith [D.r_pos]
  set W : Set R3 := {y : R3 | D.r < ‖y - D.centre‖} with hWdef
  have hWopen : IsOpen W := by
    rw [hWdef]
    exact isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
  have hxW : x ∈ W := hρ
  have hfrW : frontier (D.deform ⁻¹' Rm) ∩ W = frontier Rm ∩ W := by
    refine frontier_inter_open_eq hWopen ?_
    ext y
    constructor
    · rintro ⟨hy, hyW⟩
      rw [Set.mem_preimage, deform_eq_self_of_ge D (le_of_lt hyW)] at hy
      exact ⟨hy, hyW⟩
    · rintro ⟨hy, hyW⟩
      exact ⟨by rw [Set.mem_preimage, deform_eq_self_of_ge D (le_of_lt hyW)]; exact hy, hyW⟩
  have hfrW' : ∀ y : R3, y ∈ W → (y ∈ frontier (D.deform ⁻¹' Rm) ↔ y ∈ frontier Rm) := by
    intro y hyW
    have h : (y ∈ frontier (D.deform ⁻¹' Rm) ∩ W) ↔ y ∈ frontier Rm ∩ W := by rw [hfrW]
    simpa [hyW] using h
  have hxfront : x ∈ frontier Rm := (hfrW' x hxW).mp (hRmdef.symm ▸ hxfr)
  obtain ⟨O, hOopen, hxO, hOloc⟩ :=
    trace_localModel_of_event_off hDP ⟨hwin0, hwin1⟩ ⟨hxc, hxfront⟩ hnoev
  refine ⟨O ∩ W, hOopen.inter hWopen, ⟨hxO, hxW⟩, ?_⟩
  have hset : (O ∩ W) ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier (D.deform ⁻¹' Rm))
      = W ∩ (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier Rm)) := by
    ext y
    constructor
    · rintro ⟨⟨hyO, hyW⟩, hyc, hyfr⟩
      exact ⟨hyW, hyO, hyc, (hfrW' y hyW).mp hyfr⟩
    · rintro ⟨hyW, hyO, hyc, hyfr⟩
      exact ⟨⟨hyO, hyW⟩, hyc, (hfrW' y hyW).mpr hyfr⟩
  rw [hset]
  exact isLocallyEuclidean_inter_isOpen hWopen hOloc

/-- **The core of the dent** (`‖x - centre‖ < r / 2`). -/
theorem dentOutTrace_core
    {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : R3 →L[ℝ] ℝ} {U : Set R3} {exc : Finset ℝ} {lam0 lam1 : ℝ} {p q : ℕ}
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U)
    (hχ1 : ∀ t : ℝ, |t| ≤ 1 / 2 → D.χ t = 1)
    (hisoEv : ∀ p' : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p' →
      ‖Work.BoxShrink.Pinch.par ψ p' - D.centre‖ ≤ D.r →
      Work.BoxShrink.Pinch.par ψ p' = D.centre)
    (hwin1 : ℓ D.centre ≤ lam1) (hwin2 : lam0 ≤ ℓ D.centre - D.a' * ℓ D.d)
    {x : R3}
    (hx : x ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)))
    (hρ : ‖x - D.centre‖ < D.r / 2) :
    ∃ V : Set R3, IsOpen V ∧ x ∈ V ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (V ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)))) := by
  classical
  obtain ⟨hxc, hxfr⟩ := hx
  set lam' : ℝ := ℓ D.centre - D.a' * ℓ D.d with hlam'def
  set Rm : Set R3 := Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre) with hRmdef
  set Rm' : Set R3 := Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam' with hRm'def
  set B : Set R3 := Metric.ball D.centre (D.r / 2) with hBdef
  have hBopen : IsOpen B := by rw [hBdef]; exact Metric.isOpen_ball
  have hxB : x ∈ B := by rw [hBdef, Metric.mem_ball, dist_eq_norm]; exact hρ
  have hρle : ‖x - D.centre‖ ≤ D.r := by linarith [D.r_pos]
  have had : 0 < D.a' * ℓ D.d := mul_pos D.a'_pos D.push_pos
  have hTcoe : ∀ z : R3, (Homeomorph.addRight (D.a' • D.d)) z = z + D.a' • D.d := fun z => rfl
  have hfrB : ∀ y : R3, y ∈ B → (y ∈ frontier (D.deform ⁻¹' Rm) ↔ y ∈ frontier Rm') := by
    intro y hyB
    have hyB' : ‖y - D.centre‖ < D.r / 2 := by
      rw [hBdef, Metric.mem_ball, dist_eq_norm] at hyB; exact hyB
    have hagree : D.deform ⁻¹' Rm ∩ B = (Homeomorph.addRight (D.a' • D.d)) ⁻¹' Rm ∩ B := by
      ext z
      constructor
      · rintro ⟨hz, hzB⟩
        have hzB' : ‖z - D.centre‖ < D.r / 2 := by
          rw [hBdef, Metric.mem_ball, dist_eq_norm] at hzB; exact hzB
        refine ⟨?_, hzB⟩
        rw [Set.mem_preimage] at hz ⊢
        rwa [deform_eq_translate_of_lt D hχ1 hzB'] at hz
      · rintro ⟨hz, hzB⟩
        have hzB' : ‖z - D.centre‖ < D.r / 2 := by
          rw [hBdef, Metric.mem_ball, dist_eq_norm] at hzB; exact hzB
        refine ⟨?_, hzB⟩
        rw [Set.mem_preimage] at hz ⊢
        rwa [deform_eq_translate_of_lt D hχ1 hzB']
    have hfr1 : frontier (D.deform ⁻¹' Rm) ∩ B
        = frontier ((Homeomorph.addRight (D.a' • D.d)) ⁻¹' Rm) ∩ B :=
      frontier_inter_open_eq hBopen hagree
    have h1 : (y ∈ frontier (D.deform ⁻¹' Rm)) ↔
        (y ∈ frontier ((Homeomorph.addRight (D.a' • D.d)) ⁻¹' Rm)) := by
      have h := congrArg (fun s : Set R3 => y ∈ s) hfr1
      simpa [hyB] using h
    rw [h1, frontier_preimage_homeomorph, Set.mem_preimage, hTcoe y]
    exact (dent_frontier_shift_core D hχ1 hyB').symm
  have hxfr' : x ∈ frontier Rm' := (hfrB x hxB).mp (hRmdef.symm ▸ hxfr)
  have hnoev : ∀ qq : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ qq = x →
      ℓ (Work.BoxShrink.Pinch.par ψ qq) = lam' →
      ¬ Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ qq := by
    intro qq hq hℓq hev
    have h1 : Work.BoxShrink.Pinch.par ψ qq = D.centre := hisoEv qq hev (by rw [hq]; exact hρle)
    have h2 : ℓ D.centre = lam' := by rw [← h1]; exact hℓq
    rw [hlam'def] at h2
    linarith
  have hlam'mem : lam' ∈ Set.Icc lam0 lam1 := by
    refine ⟨hwin2, ?_⟩
    rw [hlam'def]; linarith
  obtain ⟨O, hOopen, hxO, hOloc⟩ :=
    trace_localModel_of_event_off hDP hlam'mem ⟨hxc, hxfr'⟩ hnoev
  refine ⟨O ∩ B, hOopen.inter hBopen, ⟨hxO, hxB⟩, ?_⟩
  have hset : (O ∩ B) ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier (D.deform ⁻¹' Rm))
      = B ∩ (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier Rm')) := by
    ext y
    constructor
    · rintro ⟨⟨hyO, hyB⟩, hyc, hyfr⟩
      exact ⟨hyB, hyO, hyc, (hfrB y hyB).mp hyfr⟩
    · rintro ⟨hyB, hyO, hyc, hyfr⟩
      exact ⟨⟨hyO, hyB⟩, hyc, (hfrB y hyB).mpr hyfr⟩
  rw [hset]
  exact isLocallyEuclidean_inter_isOpen hBopen hOloc

/-! ## The annulus of the dent -/

theorem slabFn_deform {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U) (y : R3) :
    Work.Drive.Final.slabFn c u v (D.deform y) = Work.Drive.Final.slabFn c u v y := by
  rw [Work.Drive.Final.slabFn_apply, Work.Drive.Final.slabFn_apply, inner_deform_eq]

/-- **The annulus of the dent** (`D.r / 2 ≤ ‖x - centre‖ ≤ D.r`). -/
theorem dentOutTrace_annulus
    {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : R3 →L[ℝ] ℝ} {U : Set R3} {exc : Finset ℝ} {lam0 lam1 : ℝ} {p q : ℕ}
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) D.χ)
    (hχ1 : ∀ t : ℝ, |t| ≤ 1 / 2 → D.χ t = 1)
    (hiso : D.a' * D.κ < D.r)
    (hann : ∀ q' : ℝ × ℝ,
      D.r / 2 ≤ ‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ →
      ‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ ≤ D.r →
      Work.BoxShrink.Pinch.par ψ q' ∈ closure (Submission.PBox s c σ) →
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q')| ≤ h →
      fderiv ℝ (fun q'' : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q''))) q' ≠ 0 ∧
      (|Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q')| = h → ∀ t : ℝ,
        fderiv ℝ (fun q'' : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q''))) q' ≠
          t • fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) q') ∧
      (Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q') = s → ∀ t : ℝ,
        fderiv ℝ (fun q'' : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q''))) q' ≠
          t • fderiv ℝ (fun q'' : ℝ × ℝ =>
            Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q'')) q'))
    (hslack : ∀ q' : ℝ × ℝ,
      D.r / 2 ≤ ‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ →
      ‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ ≤ D.r →
      ¬ (Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q') = s ∧
        |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q')| = h))
    {x : R3}
    (hx : x ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)))
    (hρ1 : D.r / 2 ≤ ‖x - D.centre‖) (hρ2 : ‖x - D.centre‖ ≤ D.r) :
    ∃ V : Set R3, IsOpen V ∧ x ∈ V ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (V ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)))) := by
  classical
  obtain ⟨hxc, hxfr⟩ := hx
  -- the bundle and its pieces
  have hData : Work.Drive.Mono.DataPackage ψ K s u c σ v h R ℓ exc lam0 lam1 p q := hDP.1
  have hG3 : Work.Drive.Final.GoodSweepData3 ψ K s c σ u v h R ℓ exc lam0 lam1 := hDP.2.1
  have hG2 : Work.Drive.Final.GoodSweepData2 ψ K s c σ u v h R ℓ exc lam0 lam1 := hG3.1
  have hGSA : Work.Drive.Final.GoodSweepData ψ K s c σ u v h R ℓ exc lam0 lam1 := hG2.1
  have hΓ : ∀ p' : ℝ × ℝ, Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p') = s →
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p')| ≤ h →
      fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p' ≠ 0 ∧
      ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p' ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p' :=
    hG3.2.2.2.2.1
  have hfaceRegD := hData.faceReg
  have hslice : Nonempty (Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
      (Work.BoxShrink.Core.sphereSet c σ s)) := hData.slicing
  have hv1 : ‖v‖ = 1 := (hGSA.1).2.1
  have hℓne : ℓ ≠ 0 := (hGSA.1).2.2.1
  have hh : 0 < h := (hGSA.1).2.2.2.2.2.1
  have hs : 0 < s := by
    obtain ⟨y, hyP, -⟩ := hData.slabCuts.1
    have h1 : Submission.boxNorm c σ y < s := (Submission.mem_PBox_iff s c σ y).mp hyP
    have h2 : 0 ≤ Submission.boxNorm c σ y := Submission.boxNorm_nonneg c σ y
    linarith
  have hv : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv1
    exact one_ne_zero hv1.symm
  -- the deformation is a homeomorphism, and the dented surface
  obtain ⟨Φ, hΦ⟩ := dentDeform_homeomorph D.κ_pos D.r_pos D.d_norm.le D.χ_diff D.χ_deriv_bound
    (by rw [abs_of_pos D.a'_pos]; exact hiso)
  have hdeform : D.deform = ⇑Φ := funext (fun z => (hΦ z).symm)
  obtain ⟨ψ', hpar', hcarrier'⟩ := exists_dentSurface (D := D) hχ hχ1 hiso
  set Rlm : Set R3 := Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre) with hRlmdef
  have hfrΦ : frontier (D.deform ⁻¹' Rlm) = D.deform ⁻¹' frontier Rlm := by
    rw [hdeform]; exact frontier_preimage_homeomorph Φ Rlm
  have hcarrier_mem : ∀ y : R3, y ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ↔
      y ∈ D.deform ⁻¹' (Work.Drive.EpsSphere.torusOf ψ').carrier := by
    intro y
    constructor
    · intro hy
      show D.deform y ∈ (Work.Drive.EpsSphere.torusOf ψ').carrier
      rw [hcarrier']; exact ⟨y, hy, rfl⟩
    · intro hy
      rw [Set.mem_preimage, hcarrier'] at hy
      obtain ⟨y', hy'c, hy'eq⟩ := hy
      have hyy : y' = y := Φ.injective (by rw [← hdeform]; exact hy'eq)
      rwa [hyy] at hy'c
  have hhyb : D.deform ⁻¹' Rlm = Submission.PBox s c σ \
      (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
        {y : R3 | ℓ (D.deform y) < ℓ D.centre}) := hRlmdef ▸ deform_preimage_tiltedLevelRemoved D
  have hxrange : x ∈ Set.range (Work.BoxShrink.Pinch.par ψ) := by
    rw [← Work.BoxShrink.Pinch.carrier_eq_range ψ]; exact hxc
  -- the frontier of the box sphere is the box sphere: a reusable step
  have boxSphereStep : ∀ (Ws : Set R3), IsOpen Ws → x ∈ Ws →
      D.deform ⁻¹' Rlm ∩ Ws = Submission.PBox s c σ ∩ Ws →
      ∃ V : Set R3, IsOpen V ∧ x ∈ V ∧
        Work.Smooth.OneManifold.IsLocallyEuclidean
          (V ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier (D.deform ⁻¹' Rlm))) := by
    intro Ws hWsopen hxWs hVeq
    have hfrWs : frontier (D.deform ⁻¹' Rlm) ∩ Ws = Work.BoxShrink.Core.sphereSet c σ s ∩ Ws := by
      rw [frontier_inter_open_eq hWsopen hVeq, Work.Topology.SphereSlicing.frontier_PBox hs c σ,
        ← Work.BoxShrink.Core.sphereSet_eq_BoxSphere]
    have hfrWs' : ∀ y : R3, y ∈ Ws → (y ∈ frontier (D.deform ⁻¹' Rlm) ↔
        y ∈ Work.BoxShrink.Core.sphereSet c σ s) := by
      intro y hyW
      have h := congrArg (fun t : Set R3 => y ∈ t) hfrWs
      simpa [hyW] using h
    refine ⟨Ws, hWsopen, hxWs, ?_⟩
    have hset : Ws ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier (D.deform ⁻¹' Rlm))
        = Ws ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          Work.BoxShrink.Core.sphereSet c σ s) := by
      ext y
      constructor
      · rintro ⟨hyW, hyc, hyfr⟩
        exact ⟨hyW, hyc, (hfrWs' y hyW).mp hyfr⟩
      · rintro ⟨hyW, hyc, hysph⟩
        exact ⟨hyW, hyc, (hfrWs' y hyW).mpr hysph⟩
    rw [hset]
    exact isLocallyEuclidean_inter_isOpen hWsopen
      (carrier_inter_sphereSet_isLocallyEuclidean hslice.some)
  by_cases hxP : x ∈ Submission.PBox s c σ
  · -- ### the box interior: the local model of the dented surface
    obtain ⟨px, hpx⟩ := hxrange
    set z : R3 := D.deform x with hzdef
    have hzPbox : z ∈ Submission.PBox s c σ := (deform_mem_PBox_iff D x).mpr hxP
    have hzcarrier : z ∈ (Work.Drive.EpsSphere.torusOf ψ').carrier := (hcarrier_mem x).mp hxc
    have hzfront : z ∈ frontier Rlm := by
      have h := hfrΦ ▸ hxfr
      rw [Set.mem_preimage] at h
      exact h
    have hinj : ∀ q q' : ℝ × ℝ, D.deform (Work.BoxShrink.Pinch.par ψ q) =
        D.deform (Work.BoxShrink.Pinch.par ψ q') → Work.BoxShrink.Pinch.par ψ q =
          Work.BoxShrink.Pinch.par ψ q' := by
      intro q q' hq
      exact Φ.injective (by rw [← hdeform]; exact hq)
    have hslabFn_par : ∀ q : ℝ × ℝ, Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ' q) =
        Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q) := by
      intro q
      rw [hpar', slabFn_deform]
    have hsweep : Work.Drive.EpsForm.sweepHeight ψ' ℓ =
        fun q : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q)) := by
      funext q
      change ℓ (Work.BoxShrink.Pinch.par ψ' q) =
        ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q))
      rw [hpar' q]
    have hslabPar : Work.Drive.Final.slabFnPar ψ' c u v = Work.Drive.Final.slabFnPar ψ c u v := by
      funext q
      rw [Work.Drive.Final.slabFnPar_apply, Work.Drive.Final.slabFnPar_apply, hslabFn_par q]
    have hppx : ∀ pp : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ' pp = z →
        Work.BoxShrink.Pinch.par ψ pp = x := by
      intro pp hp1
      have h1 : D.deform (Work.BoxShrink.Pinch.par ψ pp) = D.deform x := by
        rw [← hpar' pp, hp1, hzdef]
      have h2 : D.deform (Work.BoxShrink.Pinch.par ψ px) = D.deform x := by
        rw [hpx]
      have h : Work.BoxShrink.Pinch.par ψ pp = Work.BoxShrink.Pinch.par ψ px :=
        Φ.injective (by rw [hdeform] at h1 h2; exact h1.trans h2.symm)
      rw [h, hpx]
    have hgen1 : ∀ pp : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ' pp = z →
        Work.BoxShrink.Pinch.par ψ' pp ∈ Submission.PBox s c σ →
        Work.BoxShrink.Pinch.par ψ' pp ∈
          Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h →
        ℓ (Work.BoxShrink.Pinch.par ψ' pp) = ℓ D.centre →
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ' ℓ) pp ≠ 0 := by
      intro pp hp1 hp2 hp3 hp4
      have hppxx := hppx pp hp1
      have hxp : Work.BoxShrink.Pinch.par ψ pp ∈ Submission.PBox s c σ :=
        (deform_mem_PBox_iff D (Work.BoxShrink.Pinch.par ψ pp)).mp (by rw [← hpar' pp]; exact hp2)
      have hslab : |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ pp)| ≤ h := by
        have h1 : |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ' pp)| ≤ h := by
          simpa only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq,
            Work.Drive.Final.slabFn_apply] using hp3
        rwa [hslabFn_par pp] at h1
      have hρ1' : D.r / 2 ≤ ‖Work.BoxShrink.Pinch.par ψ pp - D.centre‖ := by
        rw [hppxx]; exact hρ1
      have hρ2' : ‖Work.BoxShrink.Pinch.par ψ pp - D.centre‖ ≤ D.r := by
        rw [hppxx]; exact hρ2
      have hcl : Work.BoxShrink.Pinch.par ψ pp ∈ closure (Submission.PBox s c σ) :=
        subset_closure hxp
      have hmain := (hann pp hρ1' hρ2' hcl hslab).1
      rwa [hsweep]
    have hgen2 : ∀ pp : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ' pp = z →
        Work.BoxShrink.Pinch.par ψ' pp ∈ Submission.PBox s c σ →
        |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ' pp)| = h →
        ℓ (Work.BoxShrink.Pinch.par ψ' pp) = ℓ D.centre →
        ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ' ℓ) pp ≠
          t • fderiv ℝ (Work.Drive.Final.slabFnPar ψ' c u v) pp := by
      intro pp hp1 hp2 hp3 hp4 t
      have hppxx := hppx pp hp1
      have hxp : Work.BoxShrink.Pinch.par ψ pp ∈ Submission.PBox s c σ :=
        (deform_mem_PBox_iff D (Work.BoxShrink.Pinch.par ψ pp)).mp (by rw [← hpar' pp]; exact hp2)
      have hslab : |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ pp)| = h := by
        have h1 : |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ' pp)| = h := hp3
        rwa [hslabFn_par pp] at h1
      have hρ1' : D.r / 2 ≤ ‖Work.BoxShrink.Pinch.par ψ pp - D.centre‖ := by
        rw [hppxx]; exact hρ1
      have hρ2' : ‖Work.BoxShrink.Pinch.par ψ pp - D.centre‖ ≤ D.r := by
        rw [hppxx]; exact hρ2
      have hcl : Work.BoxShrink.Pinch.par ψ pp ∈ closure (Submission.PBox s c σ) :=
        subset_closure hxp
      have hmain := (hann pp hρ1' hρ2' hcl (le_of_eq hslab)).2.1 hslab t
      rw [hsweep, hslabPar]
      exact hmain
    have hfaceReg' : |Work.Drive.Final.slabFn c u v z| = h → ∃ pp : ℝ × ℝ,
        Work.BoxShrink.Pinch.par ψ' pp = z ∧
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ' ((innerSL ℝ) v)) pp ≠ 0 := by
      intro hf
      have hfx : |Work.Drive.Final.slabFn c u v x| = h := by
        rw [← slabFn_deform D x]; exact hf
      obtain ⟨pp, hpp, h0⟩ := hfaceRegD x hxc hxP hfx
      refine ⟨pp, ?_, ?_⟩
      · rw [hpar' pp, hpp]
      · have hsame : (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ' q)) =
            fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q) := by
          funext q
          rw [hpar', inner_deform_eq]
        rw [Work.Drive.EpsForm.sweepHeight_innerSL ψ' v, hsame]
        exact h0
    obtain ⟨O, hOopen, hzO, hOloc⟩ :=
      trace_localModel_inBox (ψ := ψ') hs hv hh hℓne ⟨hzcarrier, hzfront⟩ hzPbox hgen1 hgen2
        hfaceReg'
    refine ⟨D.deform ⁻¹' O, hOopen.preimage (continuous_anyDentDatum_deform D), hzO, ?_⟩
    have hset : D.deform ⁻¹' O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier (D.deform ⁻¹' Rlm))
        = D.deform ⁻¹' (O ∩ ((Work.Drive.EpsSphere.torusOf ψ').carrier ∩ frontier Rlm)) := by
      rw [hfrΦ]
      ext y
      constructor
      · rintro ⟨hyO, hyc, hyfr⟩
        exact ⟨hyO, (hcarrier_mem y).mp hyc, hyfr⟩
      · rintro ⟨hyO, hyc', hyfr⟩
        exact ⟨hyO, (hcarrier_mem y).mpr hyc', hyfr⟩
    rw [hset, hdeform]
    exact isLocallyEuclidean_preimage_homeomorph Φ hOloc
  · -- ### the box sphere
    have hxclos : x ∈ closure (Submission.PBox s c σ) :=
      closure_mono (by rw [hhyb]; exact Set.sdiff_subset) (frontier_subset_closure hxfr)
    have hxnorm : Submission.boxNorm c σ x = s :=
      le_antisymm (boxNorm_le_of_mem_closure_PBox hxclos) (not_lt.mp (fun hlt =>
        hxP ((Submission.mem_PBox_iff s c σ x).mpr hlt)))
    rcases lt_trichotomy |Work.Drive.Final.slabFn c u v x| h with hinside | heq | houtside
    · -- #### strictly inside the slab
      rcases lt_trichotomy (ℓ (D.deform x)) (ℓ D.centre) with hbelow' | hwall' | habove'
      · -- ##### below the wall
        exfalso
        set Wb : Set R3 := {y : R3 | |Work.Drive.Final.slabFn c u v y| < h} ∩
          {y : R3 | ℓ (D.deform y) < ℓ D.centre} with hWbdef
        have hWbopen : IsOpen Wb := by
          have hcont : Continuous (fun y : R3 => |Work.Drive.Final.slabFn c u v y|) := by
            rw [show Work.Drive.Final.slabFn c u v =
              fun y : R3 => inner ℝ v y - (inner ℝ v c + u) from rfl]
            exact continuous_abs.comp ((continuous_const.inner continuous_id).sub continuous_const)
          rw [hWbdef]
          exact (isOpen_lt hcont continuous_const).inter
            (isOpen_lt ((ContinuousLinearMap.continuous ℓ).comp
              (continuous_anyDentDatum_deform D)) continuous_const)
        have hxWb : x ∈ Wb := by
          rw [hWbdef]
          exact ⟨hinside, hbelow'⟩
        have hemsub : D.deform ⁻¹' Rlm ⊆ Wbᶜ := by
          intro y hy hyWb
          have hmem : y ∈ D.deform ⁻¹' Rlm ∩ Wb := ⟨hy, hyWb⟩
          rw [hhyb] at hmem
          have hlt : y ∈ ({y : R3 | |inner ℝ v y - (inner ℝ v c + u)| < h} : Set R3) := by
            simpa only [Work.Drive.Final.slabFn_apply] using hmem.2.1
          have hS : y ∈ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h := by
            simp only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq]
            simp only [Set.mem_ofPred_eq] at hlt
            linarith
          exact hmem.1.2 ⟨hS, hmem.2.2⟩
        have h1 : x ∈ closure Wbᶜ := closure_mono hemsub (frontier_subset_closure hxfr)
        rw [hWbopen.isClosed_compl.closure_eq] at h1
        exact h1 hxWb
      · -- ##### the wall passes through: the box-sphere/wall junction
        obtain ⟨p₀, hp₀⟩ := hxrange
        have hB : fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ
              (Work.BoxShrink.Pinch.par ψ q)) p₀ ≠ 0 :=
          (hΓ p₀ (by rw [hp₀]; exact hxnorm) (by rw [hp₀]; exact le_of_lt hinside)).1
        have hannB : ∀ q' : ℝ × ℝ,
            D.r / 2 ≤ ‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ →
            ‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ ≤ D.r →
            Work.BoxShrink.Pinch.par ψ q' ∈ closure (Submission.PBox s c σ) →
            |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q')| ≤ h →
            Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q') = s → ∀ t : ℝ,
            fderiv ℝ (fun q'' : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q''))) q' ≠
              t • fderiv ℝ (fun q'' : ℝ × ℝ =>
                Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q'')) q' :=
          fun q' h1 h2 h3 h4 h5 t => (hann q' h1 h2 h3 h4).2.2 h5 t
        have hdir := hdirDeformed (D := D) hs hpar' hΓ hann hxc hxnorm hinside hwall' hρ1 hρ2
        exact boxSphereWallJunctionLocalModel (D := D) hpar' hs hℓne hiso hdir hp₀ hB hannB
          hxc hxnorm hinside hwall' hρ1 hρ2
      · -- ##### above the wall
        set Wa : Set R3 := {y : R3 | |Work.Drive.Final.slabFn c u v y| < h} ∩
          {y : R3 | ℓ D.centre < ℓ (D.deform y)} with hWadef
        have hWaopen : IsOpen Wa := by
          have hcont : Continuous (fun y : R3 => |Work.Drive.Final.slabFn c u v y|) := by
            rw [show Work.Drive.Final.slabFn c u v =
              fun y : R3 => inner ℝ v y - (inner ℝ v c + u) from rfl]
            exact continuous_abs.comp ((continuous_const.inner continuous_id).sub continuous_const)
          rw [hWadef]
          exact (isOpen_lt hcont continuous_const).inter
            (isOpen_lt continuous_const ((ContinuousLinearMap.continuous ℓ).comp
              (continuous_anyDentDatum_deform D)))
        have hxWa : x ∈ Wa := by
          rw [hWadef]
          exact ⟨hinside, habove'⟩
        have hVeq : D.deform ⁻¹' Rlm ∩ Wa = Submission.PBox s c σ ∩ Wa := by
          rw [hhyb]
          ext y
          constructor
          · rintro ⟨⟨hyP, -⟩, hyW⟩
            exact ⟨hyP, hyW⟩
          · rintro ⟨hyP, hyW⟩
            refine ⟨⟨hyP, ?_⟩, hyW⟩
            rintro ⟨-, hneg⟩
            have hcontra : ¬ (ℓ (D.deform y) < ℓ D.centre) := not_lt.mpr (le_of_lt hyW.2)
            exact hcontra hneg
        exact boxSphereStep Wa hWaopen hxWa hVeq
    · -- #### on a slab face: excluded by `hslack`
      obtain ⟨q', hq'⟩ := hxrange
      refine absurd (hslack q' (by rw [hq']; exact hρ1) (by rw [hq']; exact hρ2)) ?_
      rintro hcon
      exact hcon ⟨by rw [hq']; exact hxnorm, by rw [hq']; exact heq⟩
    · -- #### outside the closed slab
      set Ws : Set R3 := {y : R3 | h < |Work.Drive.Final.slabFn c u v y|} with hWsdef
      have hWsopen : IsOpen Ws := by
        have hcont : Continuous (fun y : R3 => |Work.Drive.Final.slabFn c u v y|) := by
          rw [show Work.Drive.Final.slabFn c u v =
            fun y : R3 => inner ℝ v y - (inner ℝ v c + u) from rfl]
          exact continuous_abs.comp ((continuous_const.inner continuous_id).sub continuous_const)
        rw [hWsdef]; exact isOpen_lt continuous_const hcont
      have hxWs : x ∈ Ws := by rw [hWsdef]; exact houtside
      have hVeq : D.deform ⁻¹' Rlm ∩ Ws = Submission.PBox s c σ ∩ Ws := by
        rw [hhyb]
        ext y
        constructor
        · rintro ⟨⟨hyP, -⟩, hyW⟩
          exact ⟨hyP, hyW⟩
        · rintro ⟨hyP, hyW⟩
          refine ⟨⟨hyP, ?_⟩, hyW⟩
          rintro ⟨hS, -⟩
          have hS' : |Work.Drive.Final.slabFn c u v y| ≤ h := by
            simpa only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq,
              Work.Drive.Final.slabFn_apply] using hS
          have hyW' : h < |Work.Drive.Final.slabFn c u v y| := by
            rw [hWsdef] at hyW; exact hyW
          exact absurd hS' (not_le.mpr hyW')
      exact boxSphereStep Ws hWsopen hxWs hVeq

open LeanEval.KnotTheory.PardonDistortion in
/-- **L4b (`NOTES_LEAD_L4b.md` §1.E): the trace of the level `ℓ = ℓ D.centre` of the *deformed*
removed set is a compact topological `1`-manifold.**

READ FIRST `Submission/Work/Drive/Final/NOTES_L4b_triple_obstruction.md`.  The earlier spelling of
this statement (without `hslack`) was refuted by this very obstruction: in the annulus the removed
set is the **hybrid** `PBox \ (tiltedSlabClosed ∩ {ℓ ∘ D.deform < λ*})` (the box and the slab are the
*undeformed* ones, since `Ψ := D.deform` satisfies `inner ℝ v (Ψ y) = inner ℝ v y` and, by `box_pres`,
`Ψ ⁻¹' PBox = PBox` near the annulus), so at a **deformed triple point** — a point of the carrier with
`boxNorm = s` **and** `|slabFn| = h` whose deformed level is `λ*` — the frontier has four branches
(`{u = 0} ∪ {v = 0, u < 0} ∪ {w = 0, u ≤ 0}` for `u = boxNorm - s`, `v = slabFn ∓ h`,
`w = ℓ ∘ Ψ - λ*`, with `dw = du - dv`), which is not locally Euclidean.  The new hypothesis `hslack`
excludes exactly that point on the annulus, and `hisoEv` (event isolation) is the other exclusion
used below; both are supplied by `Work.Drive.Final.exists_dentCaptureDepth`.

## Proof plan (all ingredients proved in this workspace)

Write `Ψ := D.deform`, `λ* := ℓ D.centre`, `λ' := λ* - D.a' * ℓ D.d`, `carrier' := Ψ '' carrier`,
`T := carrier ∩ frontier (Ψ ⁻¹' tiltedLevelRemoved s c σ u v h ℓ λ*)` and
`T' := carrier' ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ λ*)`.  `hiso` makes `Ψ` a homeomorphism
of `ℝ³` (`Work.Drive.Final.dentDeform_homeomorph`) with `Ψ '' carrier = carrier'`, so `T = Ψ ⁻¹' T'`;
compactness is then free (`carrier'` compact, `T'` closed in it) and local Euclideanness is proved for
`T'` and pulled back (`Work.Drive.Final.isLocallyEuclidean_preimage_homeomorph`).

For `T'`, cover its points by the three regions and use
`Work.Drive.Mono.isLocallyEuclidean_of_forall_exists_isOpen` to glue:

1. *exterior* (`‖z - D.centre‖ > D.r`): `χ` vanishes, `Ψ = id`
   (`Work.Drive.Final.dentDeform_eq_self_of_le'`), and `T'` is the undeformed trace at the level
   `λ* ∈ [lam0,lam1]` (`hwin0`, `hwin1`).  Apply the pointwise local model
   `Work.Drive.Mono.trace_localModel_at_of_localData` for `ψ`: its `hnoev` clause holds because an
   `IsAnyEvent` of value `λ*` has image `D.centre` (`hDP`'s *one event per level* together with
   `Work.Drive.Mono.eventValue_mem_exc`), whose distance to `z` is `> D.r ≥ 0`.
2. *core* (`‖z - D.centre‖ ≤ D.r / 2`): `χ = 1` (`hχ1`), `Ψ` is the translation by `D.a' • D.d`
   (`Work.Drive.Final.dentDeform_eq_translate_of_lt`), and `T'` near `z` is the translate of the
   undeformed trace `carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ λ')` near `Ψ ⁻¹' z`.
   Apply `trace_localModel_at_of_localData` (or `Work.Drive.Final.trace_localModel_at_of_localData_lam`)
   for `ψ` at the level `λ'`: `hwin2` puts `λ' ∈ [lam0,lam1]`, and its `hnoev` clause holds by
   `hisoEv` (a trace point of the core satisfies `‖· - D.centre‖ ≤ D.r / 2 ≤ D.r`, so an event there
   would be `D.centre`, of level `λ* ≠ λ'`); `hwin3` is the alternative route (`λ' ∉ exc`).
3. *annulus* (`D.r / 2 ≤ ρ ≤ D.r`): by `hslack` no trace point of the annulus lies on both the box
   sphere and a slab face, so at most two of the three constraints `boxNorm = s`, `|slabFn| = h`,
   `ℓ ∘ Ψ = λ*` are active at any point of `T'`; each junction type is then locally a `V` (two rays),
   and regularity comes from `hann`.  Use the *dented* surface `ψ' := dentSurface D`
   (`Work.Drive.Final.exists_dentSurface`) and the *pointwise* form of
   `trace_localModel_at_of_localData` at `ψ'`, dispatching by point type as in its in-box branch
   (`wallPoint`, `facePoint`, the face-wall and wall-sphere junctions); pull back with
   `Work.Smooth.OneManifold.isLocallyArc_of_homeomorph`.  (The pure wall and face pieces of the
   annulus are the easy cases: `{ℓ ∘ Ψ = λ*}`, resp. `{slabFn = ±h}`, cut out of the dented carrier.) -/
theorem dentOutTraceTame {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3} {exc : Finset ℝ} {lam0 lam1 : ℝ}
    {p q : ℕ}
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    (D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) D.χ)
    (hχ1 : ∀ t : ℝ, |t| ≤ 1 / 2 → D.χ t = 1)
    (hiso : D.a' * D.κ < D.r)
    (hisoEv : ∀ p' : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p' →
      ‖Work.BoxShrink.Pinch.par ψ p' - D.centre‖ ≤ D.r →
      Work.BoxShrink.Pinch.par ψ p' = D.centre)
    (hwin0 : lam0 ≤ ℓ D.centre)
    (hwin1 : ℓ D.centre ≤ lam1)
    (hwin2 : lam0 ≤ ℓ D.centre - D.a' * ℓ D.d)
    (hwin3 : ℓ D.centre - D.a' * ℓ D.d ∉ (exc : Set ℝ))
    (hslack : ∀ q' : ℝ × ℝ,
      D.r / 2 ≤ ‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ →
      ‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ ≤ D.r →
      ¬ (Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q') = s ∧
        |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q')| = h))
    (hann : ∀ q' : ℝ × ℝ,
      D.r / 2 ≤ ‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ →
      ‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ ≤ D.r →
      Work.BoxShrink.Pinch.par ψ q' ∈ closure (Submission.PBox s c σ) →
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q')| ≤ h →
      fderiv ℝ (fun q'' : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q''))) q' ≠ 0 ∧
      (|Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q')| = h → ∀ t : ℝ,
        fderiv ℝ (fun q'' : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q''))) q' ≠
          t • fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) q') ∧
      (Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q') = s → ∀ t : ℝ,
        fderiv ℝ (fun q'' : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q''))) q' ≠
          t • fderiv ℝ (fun q'' : ℝ × ℝ =>
            Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q'')) q'))
    : IsCompact ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))) ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))) := by
  classical
  refine ⟨?_, ?_⟩
  · exact (Work.Smooth.Morse.Surface.isCompact_torus ψ).of_isClosed_subset
      ((Work.CoreTopology.isClosed_carrier (Work.Drive.EpsSphere.torusOf ψ)).inter
        isClosed_frontier) Set.inter_subset_left
  · refine Work.Drive.Mono.isLocallyEuclidean_of_forall_exists_isOpen ?_
    rintro ⟨x, hx⟩
    rcases lt_or_ge ‖x - D.centre‖ (D.r / 2) with hcore | hannulus
    · exact dentOutTrace_core hDP D hχ1 hisoEv hwin1 hwin2 hx hcore
    · rcases lt_trichotomy ‖x - D.centre‖ D.r with hle | heq | hgt
      · exact dentOutTrace_annulus hDP D hχ hχ1 hiso hann hslack hx hannulus (le_of_lt hle)
      · exact dentOutTrace_annulus hDP D hχ hχ1 hiso hann hslack hx hannulus (le_of_eq heq)
      · exact dentOutTrace_exterior hDP D hwin0 hwin1 hx hgt

end

end Work.Drive.Final
