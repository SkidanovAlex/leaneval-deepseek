import Mathlib
import Submission.Work.Drive.Mono.g3WitnessDefs
import Submission.Work.Drive.Mono.Geom3Defs
import Submission.Work.Drive.Mono.g3Wrapper
import Submission.Work.Drive.Mono.g3OneEvDefs
import Submission.Work.Drive.Mono.oneEventPerLevel_of_nd
import Submission.Work.Drive.Mono.ndEvent_of_clauses
import Submission.Work.Drive.Mono.tiltData_window_of_dir_export_param_good
import Submission.Work.Drive.Mono.TiltDataSmallSlab
import Submission.Work.Drive.Mono.geom3Extra
import Submission.Work.Drive.Mono.g3_faceRegClosed
import Submission.Work.Drive.Mono.g3_gammaTransverse
import Submission.Work.Drive.Mono.cornerSlab_of_vertEdgeFinite
import Submission.Work.Drive.Mono.levelCount_lt_min_all
import Submission.Work.Drive.Mono.exists_nat_count_bounds
import Submission.Work.Drive.Mono.encard_tiltedCrossings_le_flat
import Submission.Work.Drive.Mono.ae_slabBoxCrossReg
import Submission.Work.Drive.Mono.no_eventOnFace_null
import Submission.Work.Drive.Mono.faceEvent_degen_null
import Submission.Work.Drive.Mono.g3_corner_dir_bad_null
import Submission.Work.Drive.Mono.g3_offKFace_bad_null
import Submission.Work.Drive.Mono.g3_corner_event_bad_null
import Submission.Work.Drive.Mono.offK_null
import Submission.Work.Drive.Mono.sweepDataGood_exists
import Submission.Work.Drive.Mono.g3_faceValues_finite_of_witness
import Submission.Work.Drive.Final.sphereCoverAt_of_edgeFree
import Submission.Work.Drive.Mono.g3_tripleBad_null

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2000000

/-- **The assembly of `Work.Drive.Mono.Geom3Data` from the witness bundle, with `EdgeFree` assumed.**
This is the body of the requested `Work.Drive.Mono.g3_geom3Data_of_witness`, but taking the
`EdgeFree` clause of `Work.Drive.Mono.G3Extra` as a hypothesis `hEF` — see
`Submission/Work/Drive/Mono/g3EdgeFreeNegative.lean` for why that clause is *not* a consequence of
the remaining hypotheses. -/
theorem g3_assembly
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot) {r s u : ℝ}
    (hr : 0 < r) (hrs : r < s) (hs : s < (1 + Submission.eps) * r)
    (hu : |u| < Submission.eps * r)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (p q : ℕ)
    (hp : 0 < p) (hq : 0 < q)
    (d : ℝ) (hd : 0 ≤ d) (hbound : Work.Sweep.IsDistortionBound K d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (hbox : Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ)
    (hslice : Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
        {y : LeanEval.KnotTheory.PardonDistortion.R3 | Submission.boxNorm c σ y = s})
    (hBGE : Work.Drive.Mono.BoxGenE ψ c σ s)
    (hS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)))
    (hsub : Set.range K.curve ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hU : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)))
    (hP : Work.Drive.Mono.G3Pointwise ψ K s u c σ)
    (V n a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3) (ρ A B : ℝ) (N : ℕ)
    (γ : Fin N → ℝ → LeanEval.KnotTheory.PardonDistortion.R3) (η m δg mE : ℝ)
    (hW : Work.Drive.Mono.WitnessData3 ψ K s u c σ V n a₀ b₀ ρ A B N γ η m δg mE)
    (hmE : 0 < mE)
    (hhedge : ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      |z (σ 0) - c (σ 0)| = Submission.boxSide 0 * s →
      |z (σ 1) - c (σ 1)| = Submission.boxSide 1 * s →
      mE ≤ |z (σ 2) - (c (σ 2) + u)|)
    (hnull : MeasureTheory.volume {y : ℝ × ℝ |
      Work.Drive.Mono.OneEvBad ψ s c σ V a₀ b₀ u y.1 y.2} = 0)
    (hEF : ∀ h ∈ Set.Ioo A B, Work.Drive.Mono.EdgeFree ψ s c σ u V h) :
    ∃ (h R : ℝ) (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ)
      (exc : Finset ℝ),
      Work.Drive.Mono.Geom3Data ψ K s u c σ V h R ℓ exc lam0 lam1 p q := by
  classical
  have hs0 : 0 < s := lt_trans hr hrs
  have hWkeep : Work.Drive.Mono.WitnessData3 ψ K s u c σ V n a₀ b₀ ρ A B N γ η m δg mE := hW
  -- ## 1. the witness bundle
  obtain ⟨hV1, haxis, hVclose, hn1, hVn, hngood, ha0, hb0, hab, hVa, hVb, hnb, hρ0, hA0, hAB,
    hAdef, hBwin, hBdg, hBmE, hBhalf, hcl1, hcl2, hcl3, hcl4, hη0, hm0, hBm, hγcd, hγh, hγβ,
    hcover, harcℓ, harcv, hsliver⟩ := hW
  obtain ⟨ε₀, hε₀0, hsliv1, hsliv2, hsliv3, hsliv4⟩ := hsliver
  -- ## 2. the finite box-sphere trace of the knot
  have hfinS : ({t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      Submission.boxNorm c σ (K.curve t) = s}).Finite :=
    Work.Drive.Mono.g3_boxSphereTrace_finite K c σ hS
  -- ## 3. the prescribed null set of forbidden `(h, τ)`
  have hSbcr_ae : ∀ᵐ h' ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Drive.Mono.SlabBoxCrossReg ψ c σ s V (inner ℝ V c + u) h' :=
    Work.Drive.Mono.ae_slabBoxCrossReg ψ c σ s u V
      (Work.Drive.Mono.g3_hreg_of_boxGen ψ c σ s hBGE.1)
  have hSbcrc : MeasureTheory.volume {h' : ℝ |
      ¬ Work.Drive.Mono.SlabBoxCrossReg ψ c σ s V (inner ℝ V c + u) h'} = 0 :=
    MeasureTheory.ae_iff.mp hSbcr_ae
  set S₁ : Set (ℝ × ℝ) := {y : ℝ × ℝ |
      Work.Drive.Mono.OneEvBad ψ s c σ V a₀ b₀ u y.1 y.2} with hS₁def
  set S₂ : Set (ℝ × ℝ) := {h' : ℝ |
      ¬ Work.Drive.Mono.SlabBoxCrossReg ψ c σ s V (inner ℝ V c + u) h'} ×ˢ
        (Set.univ : Set ℝ) with hS₂def
  set S₃ : Set (ℝ × ℝ) := {y : ℝ × ℝ | ∃ i : Fin 3, i ≠ 2 ∧
      (innerSL ℝ) (Work.Drive.Mono.Band.dirOf y.2 a₀ b₀)
        (Work.Drive.Final.crossDir V (σ i)) = 0} with hS₃def
  set Nknot : Set ℝ := {z : ℝ | ∃ t : ℝ,
      deriv (fun r : ℝ => inner ℝ V (K.curve r)) t = 0 ∧
      inner ℝ V (K.curve t) = z} with hNknotdef
  set S₄ : Set (ℝ × ℝ) := {y : ℝ × ℝ | (inner ℝ V c + u + y.1) ∈ Nknot ∨
      (inner ℝ V c + u - y.1) ∈ Nknot} with hS₄def
  set S₅ : Set (ℝ × ℝ) := {y : ℝ × ℝ |
      Work.Drive.Mono.Band.HeightGood ψ (Work.Drive.Mono.Band.dirOf y.2 a₀ b₀) ∧
        ∃ q : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ q ∈ Submission.PBox s c σ ∧
          fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
            ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf y.2 a₀ b₀))) q = 0 ∧
          |Work.Drive.Final.slabFn c u V (Work.BoxShrink.Pinch.par ψ q)| = y.1} with hS₅def
  set S₆ : Set (ℝ × ℝ) := {y : ℝ × ℝ | ¬ (∀ q : ℝ × ℝ, Work.Drive.Final.IsFaceEvent ψ s c σ u V
        y.1 ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf y.2 a₀ b₀)) q →
        ∃ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
            ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf y.2 a₀ b₀))) q
            = t • fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u V) q ∧
          ∀ w : ℝ × ℝ, w ≠ 0 →
            fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u V) q w = 0 →
            (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ =>
              Work.Drive.EpsForm.sweepHeight ψ
                ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf y.2 a₀ b₀)) q
                - t * Work.Drive.Final.slabFnPar ψ c u V q)) q) w w ≠ 0)} with hS₆def
  set S₇ : Set (ℝ × ℝ) := {y : ℝ × ℝ | ∃ p : ℝ × ℝ, Work.Drive.Final.IsFaceEvent ψ s c σ u V
        y.1 ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf y.2 a₀ b₀)) p ∧
      ∃ t : ℝ, K.curve t = Work.BoxShrink.Pinch.par ψ p} with hS₇def
  set S₈ : Set (ℝ × ℝ) := {y : ℝ × ℝ | ∃ t : ℝ,
      K.curve t ∈ closure (Submission.PBox s c σ) ∧
      Submission.boxNorm c σ (K.curve t) = s ∧
      |Work.Drive.Final.slabFn c u V (K.curve t)| = y.1} with hS₈def
  set S₉ : Set (ℝ × ℝ) := {y : ℝ × ℝ | ∃ p : ℝ × ℝ,
      (∃ i j : Fin 3, i ≠ j ∧
        |(Work.BoxShrink.Pinch.par ψ p) (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |(Work.BoxShrink.Pinch.par ψ p) (σ j) - c (σ j)| = Submission.boxSide j * s) ∧
      |Work.Drive.Final.slabFn c u V (Work.BoxShrink.Pinch.par ψ p)| = y.1 ∧
      Work.Drive.Mono.Band.HeightGood ψ (Work.Drive.Mono.Band.dirOf y.2 a₀ b₀) ∧
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
        ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf y.2 a₀ b₀))) p = 0} with hS₉def
  have hS₉0 : MeasureTheory.volume S₉ = 0 :=
    Work.Drive.Mono.g3_tripleBad_null ψ s u c σ V a₀ b₀ hV1 ha0 hb0 hab hVa hVb
  have hS₁0 : MeasureTheory.volume S₁ = 0 := hnull
  have hS₂0 : MeasureTheory.volume S₂ = 0 := by
    rw [hS₂def, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
      hSbcrc, zero_mul]
  have hS₃0 : MeasureTheory.volume S₃ = 0 :=
    Work.Drive.Mono.g3_corner_dir_bad_null V a₀ b₀ σ hV1 ha0 hb0 hab hVa hVb haxis
  have hS₄0 : MeasureTheory.volume S₄ = 0 := by
    have hker : MeasureTheory.volume Nknot = 0 := by
      rw [hNknotdef]; exact Work.Drive.Mono.volume_knotCritValues_eq_zero K V
    have h1 : MeasureTheory.volume {h' : ℝ | inner ℝ V c + u + h' ∈ Nknot} = 0 :=
      (MeasureTheory.measure_preimage_add (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        (inner ℝ V c + u) Nknot).trans hker
    have h2 : MeasureTheory.volume {h' : ℝ | inner ℝ V c + u - h' ∈ Nknot} = 0 := by
      have hmap := MeasureTheory.Measure.map_sub_left_eq_self
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (inner ℝ V c + u)
      have hle := MeasureTheory.Measure.le_map_apply
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
        (f := fun x : ℝ => inner ℝ V c + u - x)
        (measurable_const.sub measurable_id).aemeasurable Nknot
      rw [hmap, hker] at hle
      have hset : {h' : ℝ | inner ℝ V c + u - h' ∈ Nknot}
          = (fun x : ℝ => inner ℝ V c + u - x) ⁻¹' Nknot := rfl
      rw [hset]
      exact le_antisymm hle bot_le
    rw [hS₄def]
    have hset : {y : ℝ × ℝ | (inner ℝ V c + u + y.1) ∈ Nknot ∨
        (inner ℝ V c + u - y.1) ∈ Nknot}
        = ({h' : ℝ | inner ℝ V c + u + h' ∈ Nknot} ∪
            {h' : ℝ | inner ℝ V c + u - h' ∈ Nknot}) ×ˢ (Set.univ : Set ℝ) := by
      ext y; simp
    rw [hset, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
      MeasureTheory.measure_union_null h1 h2, zero_mul]
  have hS₅0 : MeasureTheory.volume S₅ = 0 :=
    Work.Drive.Mono.no_eventOnFace_null ψ s u c σ V a₀ b₀ ha0 hb0 hab hVa hVb
  have hS₆0 : MeasureTheory.volume S₆ = 0 :=
    Work.Drive.Mono.faceEvent_degen_null ψ s u c σ V a₀ b₀ hV1 ha0 hb0 hab hVa hVb
  have hS₇0 : MeasureTheory.volume S₇ = 0 :=
    Work.Drive.Mono.g3_offKFace_bad_null ψ K s c σ u V a₀ b₀ hV1 ha0 hb0 hab hVa hVb
  have hS₈0 : MeasureTheory.volume S₈ = 0 :=
    Work.Drive.Mono.g3_corner_event_bad_null ψ K s u c σ V hfinS
  set S : Set (ℝ × ℝ) := ((S₁ ∪ S₂ ∪ (S₃ ∪ S₄)) ∪ ((S₅ ∪ S₆) ∪ ((S₇ ∪ S₈) ∪ S₉))) with hSdef
  have hSnull : MeasureTheory.volume S = 0 := by
    rw [hSdef]
    exact MeasureTheory.measure_union_null
      (MeasureTheory.measure_union_null (MeasureTheory.measure_union_null hS₁0 hS₂0)
        (MeasureTheory.measure_union_null hS₃0 hS₄0))
      (MeasureTheory.measure_union_null (MeasureTheory.measure_union_null hS₅0 hS₆0)
        (MeasureTheory.measure_union_null (MeasureTheory.measure_union_null hS₇0 hS₈0) hS₉0))
  have hmemS₁ : S₁ ⊆ S := by
    intro y hy; rw [hSdef]; simp only [Set.mem_union]; tauto
  have hmemS₂ : S₂ ⊆ S := by
    intro y hy; rw [hSdef]; simp only [Set.mem_union]; tauto
  have hmemS₃ : S₃ ⊆ S := by
    intro y hy; rw [hSdef]; simp only [Set.mem_union]; tauto
  have hmemS₄ : S₄ ⊆ S := by
    intro y hy; rw [hSdef]; simp only [Set.mem_union]; tauto
  have hmemS₅ : S₅ ⊆ S := by
    intro y hy; rw [hSdef]; simp only [Set.mem_union]; tauto
  have hmemS₆ : S₆ ⊆ S := by
    intro y hy; rw [hSdef]; simp only [Set.mem_union]; tauto
  have hmemS₇ : S₇ ⊆ S := by
    intro y hy; rw [hSdef]; simp only [Set.mem_union]; tauto
  have hmemS₈ : S₈ ⊆ S := by
    intro y hy; rw [hSdef]; simp only [Set.mem_union]; tauto
  have hmemS₉ : S₉ ⊆ S := by
    intro y hy; rw [hSdef]; simp only [Set.mem_union]; tauto
  -- ## 4. the exported tilt data
  obtain ⟨h, τ, exc₀, hAh, hhB, hSavoid, hboxw, hρτ, hτ1, hτV, hτgood, hτcoord, hgen₀, hfaceRegP⟩ :=
    Work.Drive.Mono.tiltData_window_of_dir_export_param_good ψ s c σ u A B ρ V n hA0 hAB hBwin
      hρ0 hV1 hn1 hVn haxis hngood a₀ b₀ ha0 hb0 hab hVa hVb hnb S hSnull
  have hAhB : h ∈ Set.Ioo A B := ⟨hAh, hhB⟩
  set nn : LeanEval.KnotTheory.PardonDistortion.R3 :=
    Work.Drive.Mono.Band.dirOf τ a₀ b₀ with hnndef
  set ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ := (innerSL ℝ) nn with hℓdef
  have hnn1 : ‖nn‖ = 1 := by rw [hnndef]; exact hτ1
  have hnρ : ‖nn - n‖ < ρ := by rw [hnndef]; exact hρτ
  have hnnV : inner ℝ V nn = 0 := by rw [hnndef]; exact hτV
  have hnngood : Work.Drive.Mono.Band.HeightGood ψ nn := by rw [hnndef]; exact hτgood
  have hnncoord : ∀ i : Fin 3, (innerSL ℝ) nn
      (EuclideanSpace.single (σ i) (1 : ℝ)) ≠ 0 := by
    intro i; rw [hnndef]; exact hτcoord i
  -- ## 5. the exceptional set: the face values of the knot
  obtain ⟨Fex, hFex⟩ :=
    Work.Drive.Mono.g3_faceValues_finite_of_witness ψ K c σ V n a₀ b₀ ρ A B N γ η m δg mE
      hWkeep h hAhB ℓ
  set exc : Finset ℝ := exc₀ ∪ Fex with hexcdef
  have hFexmem : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |Work.Drive.Final.slabFn c u V (K.curve t)| = h → ℓ (K.curve t) ∈ (exc : Set ℝ) := by
    intro t ht hval
    exact Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_coe.mp (hFex t ht hval)))
  have hgen : Work.Drive.Final.TiltedGenericity ψ s c σ u V h ℓ exc := by
    have hh := Work.Drive.Mono.tiltedGenericity_monoExc (B := Fex) hgen₀
    rw [hexcdef]
    exact hh
  -- ## 6. the window on the closed box
  have hsize : ‖V - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) < h := by
    rw [← hAdef]; exact hAh
  have hRbox : ∀ y ∈ closure (Submission.PBox s c σ), ‖y - c‖ ≤ 5 / 2 * s :=
    fun y hy => Work.Drive.Mono.norm_sub_le_of_mem_closure_PBox (s := s) (c := c) (σ := σ)
      (le_of_lt hs0) hy
  have hℓne : ℓ ≠ 0 := by
    intro h0
    have h1 : (innerSL ℝ) nn nn = 0 := by rw [← hℓdef, h0]; rfl
    rw [innerSL_apply_apply, real_inner_self_eq_norm_sq, hnn1] at h1
    norm_num at h1
  have hℓv : ℓ V = 0 := by
    rw [hℓdef, innerSL_apply_apply]
    rw [real_inner_comm]; exact hnnV
  obtain ⟨lam0, lam1, hT, hwin⟩ :=
    Work.Drive.Mono.exists_window_of_genericity hs0 hgen hV1 hℓne hℓv hsize hRbox
  have hposh : 0 < h := hT.2.2.2.2.2.1
  -- ## 7. the slab, the belt, the corner clauses
  have hcut : Work.Drive.Mono.SlabCutsBox s c σ (inner ℝ V c + u) h V :=
    Work.Drive.Mono.slabCutsBox_of_width hs0 hposh hboxw
  have hband : ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → Submission.boxNorm c σ z = s →
      |inner ℝ V z - (inner ℝ V c + u)| ≤ h → |z (σ 2) - (c (σ 2) + u)| ≤ 2 * h :=
    fun z _ hz hval => Work.Drive.Mono.g3_traceBand (s := s) (u := u) (h := h) hsize z hz hval
  have hbelt : ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → z ∈ closure (Submission.PBox s c σ) →
      |Work.Drive.Final.slabFn c u V z| ≤ h → |z (σ 2) - c (σ 2)| < Submission.boxSide 2 * s := by
    have hhalf : h < (Submission.boxSide 2 * s - |u|) / 2 := lt_of_lt_of_le hhB hBhalf
    exact fun z hz hzcl hzval =>
      Work.Drive.Mono.g3_slabInBelt hs0 hsize hhalf z hz hzcl hzval
  have hEFh : Work.Drive.Mono.EdgeFree ψ s c σ u V h := hEF h hAhB
  have heps0 : (0 : ℝ) < Submission.eps := Submission.eps_pos
  have hbsum : (0 : ℝ) ≤ Submission.boxSide 0 + Submission.boxSide 1 +
      Submission.boxSide 2 := by
    have h0 := Submission.boxSide_pos 0
    have h1' := Submission.boxSide_pos 1
    have h2' := Submission.boxSide_pos 2
    linarith
  have htwo : 4 * Submission.eps + Submission.boxSide 0 + Submission.boxSide 1 <
      3 * Submission.boxSide 2 := by
    have h1 : Submission.boxSide 1 ≤ Submission.boxSide 2 := by
      rw [Submission.boxSide_one, Submission.boxSide_two]
      exact Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2) |>.mpr (by norm_num)
    have h2 : (1 : ℝ) ≤ Submission.boxSide 2 := by
      simpa [Submission.boxSide_two] using Submission.one_le_rpow_two_thirds
    rw [Submission.boxSide_zero, Submission.eps]
    linarith
  have hthin : h + |u| + ‖V - Work.BoxShrink.shiftVσ σ 1‖ *
      ((Submission.boxSide 0 + Submission.boxSide 1 + Submission.boxSide 2) * s)
      < Submission.boxSide 2 * s := by
    have hu2 : |u| < Submission.eps * s := by
      have h1 : Submission.eps * r < Submission.eps * s := mul_lt_mul_of_pos_left hrs heps0
      linarith [hu, h1]
    have hb2 : h < (Submission.boxSide 2 * s - |u|) / 2 := lt_of_lt_of_le hhB hBhalf
    have hcor : ‖V - Work.BoxShrink.shiftVσ σ 1‖ *
        ((Submission.boxSide 0 + Submission.boxSide 1 + Submission.boxSide 2) * s)
        ≤ (1 / 8 : ℝ) *
          ((Submission.boxSide 0 + Submission.boxSide 1 + Submission.boxSide 2) * s) :=
      mul_le_mul_of_nonneg_right hVclose (mul_nonneg hbsum (le_of_lt hs0))
    have hkey : (Submission.boxSide 2 + Submission.eps) / 2
        + (1 / 8 : ℝ) * (Submission.boxSide 0 + Submission.boxSide 1 + Submission.boxSide 2)
        < Submission.boxSide 2 := by
      nlinarith [htwo]
    nlinarith [hb2, hu2, hcor, hkey, hs0]
  have hcorner : ({z : LeanEval.KnotTheory.PardonDistortion.R3 |
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∧ Submission.boxNorm c σ z = s ∧
        |inner ℝ V z - (inner ℝ V c + u)| ≤ h ∧
        (∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
          |z (σ j) - c (σ j)| = Submission.boxSide j * s)}).Finite :=
    Work.Drive.Mono.cornerSlab_of_vertEdgeFinite ψ s u h c V σ hBGE.2.1 hV1 hthin
  have hcornerEmpty : ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → Submission.boxNorm c σ z = s →
      |Work.Drive.Final.slabFn c u V z| ≤ h →
      (∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |z (σ j) - c (σ j)| = Submission.boxSide j * s) → False :=
    Work.Drive.Mono.g3_corner_empty (ψ := ψ) (s := s) (u := u) (h := h) (c := c) (v := V) (σ := σ)
      hs0 hEFh hbelt
  -- ## 8. the event clauses
  have hnoEventFace : ∀ p' : ℝ × ℝ, Work.Drive.Final.IsEvent ψ s c σ u V h ℓ p' →
      |Work.Drive.Final.slabFn c u V (Work.BoxShrink.Pinch.par ψ p')| < h := by
    intro p' hp'
    obtain ⟨hpPBox, hpSlab, hpCrit⟩ := hp'
    have hle : |Work.Drive.Final.slabFn c u V (Work.BoxShrink.Pinch.par ψ p')| ≤ h := by
      simpa [Work.Drive.Final.slabFn_apply, Work.Drive.EpsForm.tiltedSlabClosed] using hpSlab
    by_contra hcon
    push Not at hcon
    have hEq : |Work.Drive.Final.slabFn c u V (Work.BoxShrink.Pinch.par ψ p')| = h :=
      le_antisymm hle hcon
    refine hSavoid (hmemS₅ (by
      rw [hS₅def]
      exact ⟨by simpa [hℓdef, hnndef] using hτgood, p', hpPBox,
        by simpa [hℓdef, hnndef] using hpCrit, by simpa [hℓdef, hnndef] using hEq⟩))
  have hfaceND : ∀ p' : ℝ × ℝ, Work.Drive.Final.IsFaceEvent ψ s c σ u V h ℓ p' →
      ∃ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p' =
          t • fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u V) p' ∧
        ∀ w : ℝ × ℝ, w ≠ 0 → fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u V) p' w = 0 →
          (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ =>
            Work.Drive.EpsForm.sweepHeight ψ ℓ q
              - t * Work.Drive.Final.slabFnPar ψ c u V q)) p') w w ≠ 0 := by
    by_contra hcon
    refine hSavoid (hmemS₆ (by
      rw [hS₆def]
      exact fun hh => hcon (fun q hq => by
        have hres := hh q (by simpa [hℓdef] using hq)
        simpa [hℓdef] using hres)))
  have htriple : ∀ p' : ℝ × ℝ, Work.Drive.Final.IsTriplePoint ψ s c σ u V h p' →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p' ≠ 0 := by
    intro p' hp' hcrit
    refine hSavoid (hmemS₉ (by
      rw [hS₉def]
      exact ⟨p', hp'.1, hp'.2, by simpa [hℓdef, hnndef] using hτgood,
        by simpa [hℓdef, hnndef] using hcrit⟩))
  -- ## 9. the level count
  have hcountConst : Submission.countConst = 150 := rfl
  have hsmall' : 150 * d < (Nat.min p q : ℝ) := by
    rw [← hcountConst]; exact hsmall
  have heps75 : 10 * (1 + Submission.eps) / Submission.eps = 75 := by
    norm_num [Submission.eps]
  have heps375 : 5 * (1 + Submission.eps) / Submission.eps = 75 / 2 := by
    norm_num [Submission.eps]
  have hS' : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)) ≤
      ENNReal.ofReal (75 * d) := by
    rw [← heps75]; exact hS
  have hU' : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      K.curve t ∈ Submission.PBox s c σ ∧
      (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)) ≤
      ENNReal.ofReal (75 / 2 * d) := by
    rw [← heps375]; exact hU
  obtain ⟨A₀, B₀, harith, hAenc, hBenc⟩ :=
    Work.Drive.Mono.exists_nat_count_bounds (Nat.min p q) d hd hsmall' hS' hU'
  have htilt : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      K.curve t ∈ Submission.PBox s c σ ∧
      inner ℝ V (K.curve t) = inner ℝ V c + u} ≤ (B₀ : ℕ∞) :=
    Work.Drive.Mono.encard_tiltedCrossings_le_flat K hε₀0 hBenc hsliv1 hsliv2 hsliv3 hsliv4
  have hcount := Work.Drive.Mono.levelCount_lt_min_all p q hp hq ψ K hr hrs hu c σ
    (A := A₀) (B := B₀) hAenc harith V h (5 / 2 * s) ℓ exc lam0 lam1 hT htilt
    (fun t hbs => hcl1 h hAhB t hbs)
    (fun t htmem hd0 => hcl2 h hAhB t htmem hd0)
    (fun t htmem hle => by
      have h3 := hcl3 h hAhB nn hnn1 hnρ t htmem hle
      simpa [hℓdef] using h3)
    (fun t htmem hfeq => hcl4 h hAhB t htmem hfeq)
  -- ## 10. `knotGP`
  have hknotGP : ∀ t : ℝ, |Work.Drive.Final.slabFn c u V (K.curve t)| = h →
      deriv (fun s : ℝ => inner ℝ V (K.curve s)) t ≠ 0 := by
    intro t ht hd0
    have hval : |inner ℝ V (K.curve t) - (inner ℝ V c + u)| = h := by
      simpa [Work.Drive.Final.slabFn_apply] using ht
    have ha : inner ℝ V c + u + h ∈ Nknot ∨ inner ℝ V c + u - h ∈ Nknot := by
      rcases le_or_gt 0 (inner ℝ V (K.curve t) - (inner ℝ V c + u)) with hpos | hneg
      · left
        refine ⟨t, hd0, ?_⟩
        rw [abs_of_nonneg hpos] at hval
        linarith
      · right
        refine ⟨t, hd0, ?_⟩
        rw [abs_of_neg hneg] at hval
        linarith
    exact hSavoid (hmemS₄ (by rw [hS₄def]; exact ha))
  -- ## 11. `SlabBoxCrossReg`, the corner direction, `offK`, the non-degeneracy
  have hSBCR : Work.Drive.Mono.SlabBoxCrossReg ψ c σ s V (inner ℝ V c + u) h := by
    by_contra hcon
    exact hSavoid (hmemS₂ (by rw [hS₂def]; exact ⟨hcon, trivial⟩))
  have hcross : ∀ i : Fin 3, i ≠ 2 → ℓ (Work.Drive.Final.crossDir V (σ i)) ≠ 0 := by
    intro i hi hcon
    refine hSavoid (hmemS₃ (by
      rw [hS₃def]
      exact ⟨i, hi, by simpa [hℓdef] using hcon⟩))
  have hwall : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |Work.Drive.Final.slabFn c u V (K.curve t)| ≤ h →
      deriv (fun r : ℝ => ℓ (K.curve r)) t ≠ 0 := by
    intro t htmem hle
    have h3 := hcl3 h hAhB nn hnn1 hnρ t htmem hle
    simpa [hℓdef] using h3
  have harcℓ' : ∀ k : Fin N, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h →
      deriv (fun r : ℝ => ℓ (γ k r)) t ≠ 0 := by
    intro k t htI ht2h
    have hdiff : DifferentiableAt ℝ (γ k) t := by
      have hnhds : Set.Icc (-η) η ∈ nhds t := Icc_mem_nhds htI.1 htI.2
      exact ((hγcd k).contDiffAt hnhds).differentiableAt (by norm_num)
    have hder : deriv (fun r : ℝ => ℓ (γ k r)) t = inner ℝ nn (deriv (γ k) t) := by
      have h1 : (fun r : ℝ => ℓ (γ k r)) = fun r : ℝ => inner ℝ nn (γ k r) := by
        funext r; rw [hℓdef, innerSL_apply_apply]
      rw [h1, deriv_inner_apply ℝ (differentiableAt_const nn) hdiff]
      simp
    rw [hder]
    exact harcℓ h hAhB k t htI ht2h nn hnn1 hnρ
  have hΓ : ∀ p' : ℝ × ℝ, Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p') = s →
      |Work.Drive.Final.slabFn c u V (Work.BoxShrink.Pinch.par ψ p')| ≤ h →
      fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p' ≠ 0 ∧
      ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p' ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p' :=
    Work.Drive.Mono.g3_gammaTransverse hs0 hEFh hbelt hBGE.1 hη0 hγcd hγh hγβ
      (fun z hz hzbox hzval hnoedge => hcover h hAhB z hz hzbox hzval hnoedge)
      (fun k t htI ht2h => harcℓ h hAhB k t htI ht2h nn hnn1 hnρ) hnn1 hℓdef
  have hfaceRegClosed : ∀ p' : ℝ × ℝ,
      Work.BoxShrink.Pinch.par ψ p' ∈ closure (Submission.PBox s c σ) →
      |Work.Drive.Final.slabFn c u V (Work.BoxShrink.Pinch.par ψ p')| = h →
      fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u V) p' ≠ 0 :=
    Work.Drive.Mono.g3_faceRegClosed hSBCR hbelt
      (fun z hz hzbox hzval => hfaceRegP z hz hzbox hzval)
  have hND : ∀ p' : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u V h ℓ p' →
      Work.Drive.Mono.NDEvent ψ s c σ u V h ℓ p' :=
    fun p' hp' => Work.Drive.Mono.ndEvent_of_clauses hgen hcut hEFh hbelt hSBCR hΓ
      hfaceRegClosed hnoEventFace hfaceND hp'
  have honeEv : ¬ Work.Drive.Mono.OneEvBad ψ s c σ V a₀ b₀ u h τ := by
    intro hbad
    exact hSavoid (hmemS₁ (by rw [hS₁def]; exact hbad))
  have honeEvent : ∀ p p' : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u V h ℓ p →
      Work.Drive.Final.IsAnyEvent ψ s c σ u V h ℓ p' →
      ℓ (Work.BoxShrink.Pinch.par ψ p) = ℓ (Work.BoxShrink.Pinch.par ψ p') →
      Work.BoxShrink.Pinch.par ψ p = Work.BoxShrink.Pinch.par ψ p' :=
    Work.Drive.Mono.oneEventPerLevel_of_nd (hℓ := hℓdef) hgen hND honeEv
  have hoffKface : ∀ p' : ℝ × ℝ, Work.Drive.Final.IsFaceEvent ψ s c σ u V h ℓ p' →
      ∀ t : ℝ, K.curve t ≠ Work.BoxShrink.Pinch.par ψ p' := by
    intro p' hp' t hcon
    refine hSavoid (hmemS₇ (by
      rw [hS₇def]
      exact ⟨p', by simpa [hℓdef] using hp', t, hcon⟩))
  have hoffKcorner : ∀ p' : ℝ × ℝ, Work.Drive.Final.IsCornerEvent ψ s c σ u V h p' →
      ∀ t : ℝ, K.curve t ≠ Work.BoxShrink.Pinch.par ψ p' := by
    intro p' hp' t hcon
    obtain ⟨hpcl, hpbox, hpslab⟩ := hp'
    refine hSavoid (hmemS₈ (by
      rw [hS₈def]
      exact ⟨t, by rw [hcon]; exact hpcl, by rw [hcon]; exact hpbox,
        by rw [hcon]; exact hpslab⟩))
  have hoffK : ∀ p' : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u V h ℓ p' →
      ∀ t : ℝ, K.curve t ≠ Work.BoxShrink.Pinch.par ψ p' := by
    intro p' hp' t hcon
    rcases hp' with h1 | h2 | h3
    · exact Work.Drive.Mono.g3_offK_isEvent hsub hwall p' h1 t hcon
    · exact hoffKface p' h2 t hcon
    · exact hoffKcorner p' h3 t hcon
  -- ## 12. the final assembly
  refine ⟨h, 5 / 2 * s, ℓ, lam0, lam1, exc, ?_, ?_, ?_⟩
  · refine ⟨⟨hT, hwin, hcut, hnncoord, hboxw, hVclose, hband, hcorner,
      (fun z hz hzbox hzval => hfaceRegP z hz hzbox hzval),
      (fun t ht => hcl1 h hAhB t ht),
      (fun t htmem hd0 => hcl2 h hAhB t htmem hd0),
      (fun t htmem hle hd0 => (hwall t htmem hle) hd0),
      (fun t htmem hfeq => hcl4 h hAhB t htmem hfeq),
      hFexmem,
      (fun lam hlam _ => hcount lam hlam),
      (fun p' hpPBox hpSlab hcrit t hcon =>
        Work.Drive.Mono.g3_offK_of_hwall hsub hwall p' hpPBox hpSlab hcrit t hcon),
      hknotGP, hnoEventFace, hfaceND, htriple⟩,
      ⟨N, γ, η, hη0, hγcd, hγh, hγβ,
        (fun z hz hzbox hzval hnoedge => hcover h hAhB z hz hzbox hzval hnoedge),
        (fun k t htI ht2h => harcℓ' k t htI ht2h),
        (fun k t htI ht2h => harcv h hAhB k t htI ht2h)⟩,
      (fun z hz hzbox hzval hext => hcornerEmpty z hz hzbox (le_of_eq hzval) hext)⟩
  · exact ⟨hEFh, hbelt, hSBCR, hΓ, hfaceRegClosed, hcross, hoffK, honeEvent,
      (fun lam _ => Work.Drive.Final.sphereCoverAt_of_edgeFree hs0 hposh hV1 hℓv hℓne hcross
        hEFh hbelt lam)⟩
  · exact hcount
