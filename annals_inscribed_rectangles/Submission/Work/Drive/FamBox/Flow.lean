import Mathlib
import Submission.Work.Drive.FamBox.Defs
import Submission.Work.Drive.ManifoldParity.InterSetFlowDefs
import Submission.Work.Drive.ManifoldParity.FlowSetupPairing

/-!
# The same-box parity engine: the flow argument

Continues `Submission.Work.Drive.FamBox.Defs`.  Here we set up the abstract flow theory of
`Work.Drive.FlowSetup` (`Submission/Work/Drive/ManifoldParity/FlowSetupDefs.lean`) for the meet set
`K = boxMeet F G` of two smooth maps `F G : ℝ⁵ → M` and a smooth compactly supported field `V`
tangent to `K`:

* `face_data_box` — from the face hypothesis in the `σ`-form of `Lf` we get the form of the face
  hypothesis used by the flow argument (the `i`-th component of `V` does not vanish at a boundary
  meet);
* `flowChart_at_box` — a `FlowChart` of `K` at a point of `K` with a prescribed coordinate;
* `boxFlowSetup` — the `FlowSetup` of the global flow of `V` acting on `K`;
* `exists_flowCover_box` — a finite cover of `K` by chart regions;
* `even_ncard_boxBMeet` — **the engine**: under the transversality and face hypotheses, the boundary
  meet set is finite and has even cardinality.
-/

namespace Work.Drive.FamBox

open scoped Manifold ContDiff Topology
open Manifold Set Filter

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- **The face condition in the `V`-form.**  At a boundary meet `b` the field `V` does not vanish in
the face coordinate. -/
theorem face_data_box (F G : Amb 4 → M)
    (hF : ContMDiff (𝓡 5) (𝓡 4) Ctop F) (hG : ContMDiff (𝓡 5) (𝓡 4) Ctop G)
    (htrans : ∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 → F x = G x →
      Function.Surjective (Lf F G x))
    (V : Amb 4 → Amb 4)
    (hVtan : ∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 → F x = G x → ∀ p : M,
      x ∈ chartReg p F G → fderiv ℝ (chartDif p F G) x (V x) = 0)
    (hVne : ∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 → F x = G x → V x ≠ 0)
    (hface : ∀ b : Amb 4, b ∈ Submission.Drive.unitBox 4 → F b = G b →
      b ∈ Submission.Drive.unitBoxBdry 4 →
      ∃ i : Fin 5, (b i = 0 ∨ b i = 1) ∧ (∀ j : Fin 5, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ σ : Amb 4, Lf F G b σ = 0 ∧ σ i ≠ 0) :
    ∀ b : Amb 4, b ∈ boxMeet F G → b ∈ Submission.Drive.unitBoxBdry 4 →
      ∃ i : Fin 5, (b i = 0 ∨ b i = 1) ∧
        (∀ j : Fin 5, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧ V b i ≠ 0 := by
  intro b hb hbbdry
  obtain ⟨hbox, heq⟩ := mem_boxMeet.mp hb
  have hbx : b ∈ chartReg (F b) F G := mem_chartReg_self F G heq
  have hsurj : Function.Surjective (fderiv ℝ (chartDif (F b) F G) b) :=
    chartDif_surjective_of_Lf (F b) F G hF hG hbx heq (htrans b hbox heq)
  have htan : fderiv ℝ (chartDif (F b) F G) b (V b) = 0 :=
    hVtan b hbox heq (F b) hbx
  have hne : V b ≠ 0 := hVne b hbox heq
  obtain ⟨i, hiface, hother, σ, hσ, hσi⟩ := hface b hbox heq hbbdry
  refine ⟨i, hiface, hother, ?_⟩
  refine kernel_coord_ne_zero hsurj htan hne ?_
  exact chartDif_face_of_kernel (F b) F G hF hG hbx heq hsurj hσ hσi

/-- **The local chart of the meet set at a point of the meet set.**  If the charted difference map
is a submersion at `x` and also on the coordinate hyperplane `{v | v i = 0}`, and the field `V` is
tangent there, then there is a `FlowChart` for `K = boxMeet F G` at `x` with coordinate `i`. -/
theorem flowChart_at_box {F G : Amb 4 → M}
    (hF : ContMDiff (𝓡 5) (𝓡 4) Ctop F) (hG : ContMDiff (𝓡 5) (𝓡 4) Ctop G)
    {V : Amb 4 → Amb 4} (hVcont : Continuous V)
    {x : Amb 4} (hx : x ∈ boxMeet F G)
    (hsurj : Function.Surjective (fderiv ℝ (chartDif (F x) F G) x))
    (htan : fderiv ℝ (chartDif (F x) F G) x (V x) = 0) (hne : V x ≠ 0)
    (i : Fin 5)
    (hsurj_i : Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
      fderiv ℝ (chartDif (F x) F G) x v.1)) :
    ∃ C : FlowChart V (boxMeet F G) x, C.i = i ∧ x ∈ C.region := by
  obtain ⟨hbox, heq⟩ := mem_boxMeet.mp hx
  have hxreg : x ∈ chartReg (F x) F G := mem_chartReg_self F G heq
  obtain ⟨δ, ρ, η, hδ, hρ, hηcd, hηi, hηx, hchar⟩ :=
    exists_local_graph_box (F x) F G hF hG hxreg heq i hsurj_i
  have hηc : Continuous η := hηcd.continuous
  have hVi : V x i ≠ 0 := kernel_coord_ne_zero hsurj htan hne hsurj_i
  have hVipos : 0 < |V x i| := abs_pos.mpr hVi
  have hcont_i : Continuous fun y : Amb 4 => V y i :=
    (PiLp.continuous_apply 2 (fun _ : Fin 5 => ℝ) i).comp hVcont
  obtain ⟨εV, hεV, hεV'⟩ : ∃ εV > 0, ∀ y, ‖y - x‖ < εV → |V y i - V x i| < |V x i| / 2 := by
    have hhalf : 0 < |V x i| / 2 := by linarith
    obtain ⟨εV, hεV, h⟩ := Metric.continuousAt_iff.mp hcont_i.continuousAt (|V x i| / 2) hhalf
    exact ⟨εV, hεV, fun y hy => by
      have h' := h (by rwa [dist_eq_norm])
      rwa [Real.dist_eq] at h'⟩
  have hε0 : (0 : ℝ) < min εV 1 := lt_min hεV one_pos
  obtain ⟨εη, hεη, hεη'⟩ : ∃ εη > 0, ∀ u, |u - x i| < εη → ‖η u - η (x i)‖ < min εV 1 / 3 := by
    have h3 : 0 < min εV 1 / 3 := by linarith
    obtain ⟨εη, hεη, h⟩ := Metric.continuousAt_iff.mp hηc.continuousAt (min εV 1 / 3) h3
    exact ⟨εη, hεη, fun u hu => by
      have h' := h (by rwa [Real.dist_eq])
      rwa [dist_eq_norm] at h'⟩
  set δs : ℝ := min δ (min εη (min εV 1 / 3)) with hδsdef
  set ρs : ℝ := min ρ (min εV 1 / 3) with hρsdef
  set cval : ℝ := |V x i| / 2 with hcvaldef
  have hδs : 0 < δs := by
    rw [hδsdef]; exact lt_min hδ (lt_min hεη (by linarith))
  have hρs : 0 < ρs := by
    rw [hρsdef]; exact lt_min hρ (by linarith)
  have hcval : 0 < cval := by rw [hcvaldef]; linarith
  have hδsle : δs ≤ δ := by rw [hδsdef]; exact min_le_left _ _
  have hρsle : ρs ≤ ρ := by rw [hρsdef]; exact min_le_left _ _
  have hδsε : δs ≤ min εV 1 / 3 := by
    rw [hδsdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hδsη : δs ≤ εη := by rw [hδsdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρsε : ρs ≤ min εV 1 / 3 := by rw [hρsdef]; exact min_le_right _ _
  have hball : ∀ y : Amb 4, |y i - x i| < δs →
      ‖y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)‖ < ρs →
      ‖y - x‖ < min εV 1 := by
    intro y h1 h2
    have h1' : |y i - x i| < min εV 1 / 3 := lt_of_lt_of_le h1 hδsε
    have h1'' : |y i - x i| < εη := lt_of_lt_of_le h1 hδsη
    have h2' : ‖y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)‖ < min εV 1 / 3 :=
      lt_of_lt_of_le h2 hρsε
    have h3 : ‖η (y i) - η (x i)‖ < min εV 1 / 3 := hεη' (y i) h1''
    have hdecomp : y - x = (y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)) +
        (η (y i) - η (x i)) + ((y i - x i) • EuclideanSpace.single i (1 : ℝ)) := by
      rw [hηx]; module
    have hsingle : ‖(y i - x i) • EuclideanSpace.single (i : Fin 5) (1 : ℝ)‖ = |y i - x i| := by
      rw [norm_smul, Real.norm_eq_abs, PiLp.norm_single]
      simp
    rw [hdecomp]
    calc ‖(y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)) + (η (y i) - η (x i)) +
          ((y i - x i) • EuclideanSpace.single i (1 : ℝ))‖
        ≤ ‖y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)‖ + ‖η (y i) - η (x i)‖ +
          ‖(y i - x i) • EuclideanSpace.single i (1 : ℝ)‖ := by
          have h1 := norm_add_le (y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i))
            (η (y i) - η (x i))
          have h2 := norm_add_le
            ((y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)) + (η (y i) - η (x i)))
            ((y i - x i) • EuclideanSpace.single i (1 : ℝ))
          linarith
      _ = ‖y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)‖ + ‖η (y i) - η (x i)‖ +
          |y i - x i| := by rw [hsingle]
      _ < min εV 1 := by linarith
  have hgraphs : ∀ y : Amb 4, |y i - x i| < δs →
      ‖y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)‖ < ρs → y ∈ boxMeet F G →
      y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i) := by
    intro y h1 h2 hy
    obtain ⟨-, hiff⟩ := hchar y (lt_of_lt_of_le h1 hδsle) (lt_of_lt_of_le h2 hρsle)
    exact hiff.mp hy.2
  have hvels : ∀ y : Amb 4, |y i - x i| < δs →
      ‖y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)‖ < ρs → cval ≤ |V y i| := by
    intro y h1 h2
    have hb := hball y h1 h2
    have hεV'' : ‖y - x‖ < εV := lt_of_lt_of_le hb (min_le_left _ _)
    have hlt : |V y i - V x i| < |V x i| / 2 := hεV' y hεV''
    have htri : |V x i| - |V y i| ≤ |V x i - V y i| := by
      have h := abs_add_le (V x i - V y i) (V y i)
      rw [sub_add_cancel] at h
      linarith
    have hlt' : |V x i - V y i| < |V x i| / 2 := by rwa [abs_sub_comm] at hlt
    have : |V x i| - |V y i| < |V x i| / 2 := lt_of_le_of_lt htri hlt'
    rw [hcvaldef]
    linarith
  let C : FlowChart V (boxMeet F G) x :=
    { i := i, δ := δs, ρ := ρs, c := cval, η := η, hδ := hδs, hρ := hρs,
      hc := hcval, hηc := hηc, hηi := hηi, hgraph := hgraphs, hvel := hvels }
  refine ⟨C, rfl, ?_⟩
  rw [FlowChart.mem_region]
  refine ⟨by simp only [sub_self, abs_zero]; exact hδs, ?_⟩
  have h0 : x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i) = 0 := by
    rw [hηx]; abel
  rw [h0, norm_zero]
  exact hρs

/-- **The flow setup of the tangential field `V` on the meet set.** -/
def boxFlowSetup (F G : Amb 4 → M) (V : Amb 4 → Amb 4) (hV : ContDiff ℝ Ctop V)
    (hVs : HasCompactSupport V)
    (hmapsTo : ∀ x ∈ boxMeet F G, ∀ t : ℝ,
      (∀ u ∈ Set.uIcc (0 : ℝ) t, flowV V hV hVs u x ∈ Submission.Drive.unitBox 4) →
      flowV V hV hVs t x ∈ boxMeet F G) : FlowSetup 4 where
  W := V
  Φ := flowV V hV hVs
  K := boxMeet F G
  zero := flowV_zero V hV hVs
  add := flowV_add V hV hVs
  deriv := flowV_deriv V hV hVs
  mapsTo := hmapsTo
  cont := hV.continuous

/-- **A finite chart cover of the meet set.** -/
theorem exists_flowCover_box (F G : Amb 4 → M)
    (hF : ContMDiff (𝓡 5) (𝓡 4) Ctop F) (hG : ContMDiff (𝓡 5) (𝓡 4) Ctop G)
    (htrans : ∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 → F x = G x →
      Function.Surjective (Lf F G x))
    (V : Amb 4 → Amb 4) (hV : ContDiff ℝ Ctop V) (hVs : HasCompactSupport V)
    (hVtan : ∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 → F x = G x → ∀ p : M,
      x ∈ chartReg p F G → fderiv ℝ (chartDif p F G) x (V x) = 0)
    (hVne : ∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 → F x = G x → V x ≠ 0)
    (hmapsTo : ∀ x ∈ boxMeet F G, ∀ t : ℝ,
      (∀ u ∈ Set.uIcc (0 : ℝ) t, flowV V hV hVs u x ∈ Submission.Drive.unitBox 4) →
      flowV V hV hVs t x ∈ boxMeet F G) :
    Nonempty (FlowCover (boxFlowSetup F G V hV hVs hmapsTo)) := by
  classical
  have hpoint (x : Amb 4) (hx : x ∈ boxMeet F G) :
      ∃ C : FlowChart V (boxMeet F G) x, x ∈ C.region := by
    have hbox : x ∈ Submission.Drive.unitBox 4 := hx.1
    have heq : F x = G x := hx.2
    have hxreg : x ∈ chartReg (F x) F G := mem_chartReg_self F G heq
    have hsurj : Function.Surjective (fderiv ℝ (chartDif (F x) F G) x) :=
      chartDif_surjective_of_Lf (F x) F G hF hG hxreg heq (htrans x hbox heq)
    obtain ⟨i, hi⟩ := exists_domRestrict_surjective hsurj
    obtain ⟨C, -, hCx⟩ := flowChart_at_box hF hG hV.continuous hx hsurj
      (hVtan x hbox heq (F x) hxreg) (hVne x hbox heq) i hi
    exact ⟨C, hCx⟩
  let Cof : ∀ x : Amb 4, x ∈ boxMeet F G → FlowChart V (boxMeet F G) x :=
    fun x hx => Classical.choose (hpoint x hx)
  by_cases hne : (boxMeet F G).Nonempty
  · haveI : Nonempty {x : Amb 4 // x ∈ boxMeet F G} :=
      ⟨⟨hne.choose, hne.choose_spec⟩⟩
    obtain ⟨t, ht⟩ := (isCompact_boxMeet F G hF.continuous hG.continuous).elim_finite_subcover
      (fun x : {x : Amb 4 // x ∈ boxMeet F G} => (Cof x.1 x.2).region)
      (fun x => (Cof x.1 x.2).isOpen_region)
      (fun x hx => Set.mem_iUnion.mpr
        ⟨⟨x, hx⟩, Classical.choose_spec (hpoint x hx)⟩)
    have hcover : boxMeet F G ∩ Submission.Drive.unitBox 4 ⊆
        ⋃ j : {j : {x : Amb 4 // x ∈ boxMeet F G} // j ∈ t}, (Cof j.1.1 j.1.2).region := by
      intro y hy
      have h := ht hy.1
      simp only [Set.mem_iUnion] at h
      obtain ⟨i, hi, hyi⟩ := h
      exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hyi⟩
    let Cov : FlowCover (boxFlowSetup F G V hV hVs hmapsTo) :=
      { ι := {j : {x : Amb 4 // x ∈ boxMeet F G} // j ∈ t}, str := inferInstance,
        p := fun j => j.1.1, C := fun j => Cof j.1.1 j.1.2, cover := hcover }
    exact ⟨Cov⟩
  · let p0 : Fin 0 → Amb 4 := fun j => j.elim0
    have hcover : boxMeet F G ∩ Submission.Drive.unitBox 4 ⊆
        ⋃ j : Fin 0, (j.elim0 : FlowChart V (boxMeet F G) (p0 j)).region := by
      intro y hy
      exact absurd ⟨y, hy.1⟩ hne
    let Cov : FlowCover (boxFlowSetup F G V hV hVs hmapsTo) :=
      { ι := Fin 0, str := inferInstance, p := p0, C := fun j => j.elim0, cover := hcover }
    exact ⟨Cov⟩

end

end Work.Drive.FamBox
