import Mathlib
import Submission.Work.Tubular.ThomRepOfLocalDegree
import Submission.Work.Tubular.Gauss
import Submission.Work.Tubular.OnePointModel
import Submission.Work.Stems.hurewiczChain_eq_of_homotopic
import Submission.Work.ThomBordism.collapseInterp
import Submission.Work.ThomBordism.collapseRelK8_indep_R

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

noncomputable section

open scoped Manifold ContDiff Topology unitInterval
open Function Topology Filter
open Work.Tubular
open Work.ThomBordism.PontryaginThom (EmbeddingData)

/-! ## Two auxiliary continuity facts for the blow-up map -/

variable {V : Work.ThomBordism.Man8} {k : ℕ}
variable {E : EmbeddingData V (8 + k)}

/-- If a family of normal vectors has normal norm tending to `+∞`, its image in `ν⁺` tends to `∞`. -/
lemma collapseRadial_tendsto_nhds_infty {α : Type*} {l : Filter α}
    {f : α → Work.Tubular.NormalTotal E}
    (h : Tendsto (fun a => Work.Tubular.normalNorm E (f a)) l atTop) :
    Tendsto (fun a => (OnePoint.some (f a) : OnePoint (Work.Tubular.NormalTotal E))) l
      (𝓝 OnePoint.infty) := by
  refine (OnePoint.hasBasis_nhds_infty.tendsto_right_iff).mpr ?_
  intro K hK
  obtain ⟨hKc, hKcomp⟩ := hK
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp
    ((hKcomp.image (Work.Tubular.continuous_normalNorm E)).isBounded)
  have hMK : ∀ q ∈ K, Work.Tubular.normalNorm E q ≤ max r 0 := by
    intro q hq
    have h1 : Work.Tubular.normalNorm E q ∈ Metric.closedBall (0 : ℝ) r :=
      hr (Set.mem_image_of_mem _ hq)
    have h2 := Metric.mem_closedBall.mp h1
    rw [Real.dist_eq, sub_zero] at h2
    exact le_trans (le_abs_self _) (le_trans h2 (le_max_left _ _))
  filter_upwards [(tendsto_atTop.1 h (max r 0 + 1))] with a ha
  refine Or.inl ⟨f a, fun hmem => ?_, rfl⟩
  have hle := hMK (f a) hmem
  linarith

/-- The two-variable blow-up `(r, p) ↦ normalBlowUp E r p` is continuous wherever `‖p‖ < r`. -/
lemma collapseRadial_continuousAt_normalBlowUp_pair {r : ℝ} {p : Work.Tubular.NormalTotal E}
    (hp : Work.Tubular.normalNorm E p < r) :
    ContinuousAt (fun q : ℝ × Work.Tubular.NormalTotal E =>
      Work.Tubular.normalBlowUp E q.1 q.2) (r, p) := by
  have hne : r - Work.Tubular.normalNorm E p ≠ 0 := by
    have := Work.Tubular.normalNorm_nonneg E p; linarith
  have hbase : ContinuousAt (fun q : ℝ × Work.Tubular.NormalTotal E =>
      ((q.2.1.1, (q.1 * (q.1 - Work.Tubular.normalNorm E q.2)⁻¹) • q.2.1.2) :
        V.pt × Work.Tubular.Euc (8 + k))) (r, p) := by
    refine ContinuousAt.prodMk ?_ ?_
    · exact ((continuous_fst.comp continuous_subtype_val).comp continuous_snd).continuousAt
    · have hs : ContinuousAt (fun q : ℝ × Work.Tubular.NormalTotal E =>
          q.1 * (q.1 - Work.Tubular.normalNorm E q.2)⁻¹) (r, p) := by
        refine ContinuousAt.mul continuousAt_fst ?_
        refine ContinuousAt.inv₀ ?_ ?_
        · exact continuousAt_fst.sub
            ((Work.Tubular.continuous_normalNorm E).continuousAt.comp continuousAt_snd)
        · exact hne
      have hv : ContinuousAt (fun q : ℝ × Work.Tubular.NormalTotal E =>
          q.2.1.2) (r, p) :=
        ((continuous_snd.comp continuous_subtype_val).comp continuous_snd).continuousAt
      exact hs.smul hv
  have hval : (Subtype.val ∘ fun q : ℝ × Work.Tubular.NormalTotal E =>
      Work.Tubular.normalBlowUp E q.1 q.2)
      = fun q => (q.2.1.1, (q.1 * (q.1 - Work.Tubular.normalNorm E q.2)⁻¹) • q.2.1.2) := by
    funext q; rfl
  rw [← continuousWithinAt_univ,
    (Topology.IsEmbedding.subtypeVal
      (p := fun z : V.pt × Work.Tubular.Euc (8 + k) =>
        z.2 ∈ Work.Tubular.normalSpace E z.1)).isInducing.continuousWithinAt_iff,
    hval]
  simpa only [ContinuousWithinAt, ContinuousAt, nhdsWithin_univ] using hbase


/-! ## The main continuity statement -/

open Work.Tubular

theorem continuous_collapseRadial_interp_aux {ε ε' : ℝ}
    (C : TubeChart E ε) (hε' : 0 < ε') (hle : ε' ≤ ε) :
    Continuous (fun p : unitInterval × Work.Tubular.Euc (8 + k) =>
      collapseRadial C (tubeRadiusInterp ε ε' p.1) p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s₀, y₀⟩
  have hrfcont : Continuous (fun s : unitInterval => tubeRadiusInterp ε ε' s) :=
    continuous_tubeRadiusInterp ε ε'
  have hrfmem : ∀ s : unitInterval,
      ε' ≤ tubeRadiusInterp ε ε' s ∧ tubeRadiusInterp ε ε' s ≤ ε :=
    fun s => tubeRadiusInterp_mem hle s
  have hrfpos : ∀ s : unitInterval, 0 < tubeRadiusInterp ε ε' s :=
    fun s => tubeRadiusInterp_pos hle hε' s
  have hcontrf : ContinuousAt (fun p : unitInterval × Work.Tubular.Euc (8 + k) =>
      tubeRadiusInterp ε ε' p.1) (s₀, y₀) :=
    hrfcont.continuousAt.comp continuous_fst.continuousAt
  by_cases hyU : y₀ ∈ C.U
  · by_cases hlt : normalNorm E (C.inv y₀) < tubeRadiusInterp ε ε' s₀
    · -- the point lies strictly inside the interpolated tube
      have hltE : normalNorm E (C.inv y₀) < ε := lt_of_lt_of_le hlt (hrfmem s₀).2
      have hyOpen : y₀ ∈ C.openTube := ⟨C.inv y₀, hltE, C.tubeMap_inv y₀ hyU⟩
      have hinvAt : ContinuousAt C.inv y₀ :=
        C.continuousOn_openTube_inv.continuousAt (C.openTube_isOpen.mem_nhds hyOpen)
      have hcontinv : ContinuousAt (fun p : unitInterval × Work.Tubular.Euc (8 + k) =>
          C.inv p.2) (s₀, y₀) := hinvAt.comp continuous_snd.continuousAt
      have hnormcont : ContinuousAt (fun p : unitInterval × Work.Tubular.Euc (8 + k) =>
          normalNorm E (C.inv p.2)) (s₀, y₀) :=
        (continuous_normalNorm E).continuousAt.comp hcontinv
      have hblow : ContinuousAt (fun q : ℝ × Work.Tubular.NormalTotal E =>
          normalBlowUp E q.1 q.2) (tubeRadiusInterp ε ε' s₀, C.inv y₀) :=
        collapseRadial_continuousAt_normalBlowUp_pair hlt
      have hpair : ContinuousAt (fun p : unitInterval × Work.Tubular.Euc (8 + k) =>
          (tubeRadiusInterp ε ε' p.1, C.inv p.2)) (s₀, y₀) := hcontrf.prodMk hcontinv
      have hblow' : ContinuousAt (fun p : unitInterval × Work.Tubular.Euc (8 + k) =>
          normalBlowUp E (tubeRadiusInterp ε ε' p.1) (C.inv p.2)) (s₀, y₀) :=
        ContinuousAt.comp (x := (s₀, y₀))
          (f := fun p : unitInterval × Work.Tubular.Euc (8 + k) =>
            (tubeRadiusInterp ε ε' p.1, C.inv p.2)) hblow hpair
      have hformula : ContinuousAt (fun p : unitInterval × Work.Tubular.Euc (8 + k) =>
          OnePoint.some (normalBlowUp E (tubeRadiusInterp ε ε' p.1) (C.inv p.2)))
          (s₀, y₀) := by
        refine OnePoint.continuous_coe.continuousAt.comp ?_
        exact hblow'
      refine hformula.congr ?_
      have h1 : ∀ᶠ p : unitInterval × Work.Tubular.Euc (8 + k) in 𝓝 (s₀, y₀), p.2 ∈ C.U := by
        have hmem : C.openTube ∈ 𝓝 y₀ := C.openTube_isOpen.mem_nhds hyOpen
        have hev : ∀ᶠ y in 𝓝 y₀, y ∈ C.openTube := hmem
        have hsnd : Tendsto (fun p : unitInterval × Work.Tubular.Euc (8 + k) => p.2)
            (𝓝 (s₀, y₀)) (𝓝 y₀) := continuous_snd.continuousAt
        exact hsnd.eventually hev |>.mono (fun p hp => C.openTube_subset_U hp)
      have h2 : ∀ᶠ p : unitInterval × Work.Tubular.Euc (8 + k) in 𝓝 (s₀, y₀),
          normalNorm E (C.inv p.2) < tubeRadiusInterp ε ε' p.1 := by
        have hg : (0 : ℝ) < tubeRadiusInterp ε ε' s₀ - normalNorm E (C.inv y₀) := by linarith
        have hAev : ∀ᶠ p : unitInterval × Work.Tubular.Euc (8 + k) in 𝓝 (s₀, y₀),
            tubeRadiusInterp ε ε' s₀ - (tubeRadiusInterp ε ε' s₀ - normalNorm E (C.inv y₀)) / 2
              < tubeRadiusInterp ε ε' p.1 :=
          (tendsto_order.1 hcontrf).1 _ (by linarith)
        have hBev : ∀ᶠ p : unitInterval × Work.Tubular.Euc (8 + k) in 𝓝 (s₀, y₀),
            normalNorm E (C.inv p.2)
              < normalNorm E (C.inv y₀)
                + (tubeRadiusInterp ε ε' s₀ - normalNorm E (C.inv y₀)) / 2 :=
          (tendsto_order.1 hnormcont).2 _ (by linarith)
        filter_upwards [hAev, hBev] with p hpA hpB
        linarith
      filter_upwards [h1, h2] with p hp1 hp2
      exact (collapseRadial_of_mem C hp1 hp2).symm
    · -- the point lies on the boundary sphere of the interpolated tube: the value is `∞` and all
      -- nearby finite values blow up
      set A : Set (unitInterval × Work.Tubular.Euc (8 + k)) :=
        {p | p.2 ∈ C.U ∧ normalNorm E (C.inv p.2) < tubeRadiusInterp ε ε' p.1} with hAdef
      have hAmem : A ∈ 𝓝 (s₀, y₀) ⊓ 𝓟 A := le_principal_iff.mp inf_le_right
      have hcontrfA : Tendsto (fun p : unitInterval × Work.Tubular.Euc (8 + k) =>
          tubeRadiusInterp ε ε' p.1) (𝓝 (s₀, y₀) ⊓ 𝓟 A)
            (𝓝 (tubeRadiusInterp ε ε' s₀)) :=
        hcontrf.mono_left inf_le_left
      have hmaps : Set.MapsTo (fun p : unitInterval × Work.Tubular.Euc (8 + k) => p.2)
          (Set.univ ×ˢ C.U) C.U := fun p hp => hp.2
      have hCW : ContinuousWithinAt (fun p : unitInterval × Work.Tubular.Euc (8 + k) =>
          C.inv p.2) (Set.univ ×ˢ C.U) (s₀, y₀) :=
        (C.continuousOn_inv.continuousWithinAt hyU).comp continuous_snd.continuousWithinAt hmaps
      have hmono : 𝓝 (s₀, y₀) ⊓ 𝓟 A ≤ 𝓝 (s₀, y₀) ⊓ 𝓟 (Set.univ ×ˢ C.U) :=
        inf_le_inf_left _ (Filter.principal_mono.mpr (fun p hp => ⟨trivial, hp.1⟩))
      have hinvA : Tendsto (fun p : unitInterval × Work.Tubular.Euc (8 + k) => C.inv p.2)
          (𝓝 (s₀, y₀) ⊓ 𝓟 A) (𝓝 (C.inv y₀)) := hCW.mono_left hmono
      have hnormA : Tendsto (fun p : unitInterval × Work.Tubular.Euc (8 + k) =>
          normalNorm E (C.inv p.2)) (𝓝 (s₀, y₀) ⊓ 𝓟 A)
            (𝓝 (normalNorm E (C.inv y₀))) :=
        ((continuous_normalNorm E).continuousAt.tendsto).comp hinvA
      have hnumA := hcontrfA.mul hnormA
      have hdenA := hcontrfA.sub hnormA
      have hnum_ev : ∀ᶠ p : unitInterval × Work.Tubular.Euc (8 + k) in 𝓝 (s₀, y₀) ⊓ 𝓟 A,
          ε' ^ 2 / 2 < tubeRadiusInterp ε ε' p.1 * normalNorm E (C.inv p.2) :=
        (tendsto_order.1 hnumA).1 _ (by
          have h1 : ε' ≤ tubeRadiusInterp ε ε' s₀ := (hrfmem s₀).1
          have h2 : ε' ≤ normalNorm E (C.inv y₀) :=
            le_trans (hrfmem s₀).1 (le_of_not_gt hlt)
          nlinarith)
      have hval : collapseRadial C (tubeRadiusInterp ε ε' s₀) y₀ = OnePoint.infty :=
        collapseRadial_of_not C (fun h => hlt h.2)
      show Tendsto (fun p : unitInterval × Work.Tubular.Euc (8 + k) =>
        collapseRadial C (tubeRadiusInterp ε ε' p.1) p.2) (𝓝 (s₀, y₀))
        (𝓝 (collapseRadial C (tubeRadiusInterp ε ε' s₀) y₀))
      rw [hval]
      refine (OnePoint.hasBasis_nhds_infty.tendsto_right_iff).mpr ?_
      intro K hK
      obtain ⟨hKc, hKcomp⟩ := hK
      obtain ⟨rK, hrK⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp
        ((hKcomp.image (continuous_normalNorm E)).isBounded)
      set M : ℝ := max rK 0 with hMdef
      have hMK : ∀ q ∈ K, normalNorm E q ≤ M := by
        intro q hq
        have h1 : normalNorm E q ∈ Metric.closedBall (0 : ℝ) rK := hrK (Set.mem_image_of_mem _ hq)
        have h2 := Metric.mem_closedBall.mp h1
        rw [Real.dist_eq, sub_zero] at h2
        exact le_trans (le_abs_self _) (le_trans h2 (le_max_left _ _))
      -- on `A` the blow-up norm is eventually bigger than `M`
      have hden_pos : ∀ᶠ p : unitInterval × Work.Tubular.Euc (8 + k) in 𝓝 (s₀, y₀) ⊓ 𝓟 A,
          0 < tubeRadiusInterp ε ε' p.1 - normalNorm E (C.inv p.2) := by
        filter_upwards [hAmem] with p hp
        linarith [hp.2]
      have hfin : ∀ᶠ p : unitInterval × Work.Tubular.Euc (8 + k) in 𝓝 (s₀, y₀) ⊓ 𝓟 A,
          M < normalNorm E (normalBlowUp E (tubeRadiusInterp ε ε' p.1) (C.inv p.2)) := by
        have heq : (fun p : unitInterval × Work.Tubular.Euc (8 + k) =>
            tubeRadiusInterp ε ε' p.1 * normalNorm E (C.inv p.2)
              / (tubeRadiusInterp ε ε' p.1 - normalNorm E (C.inv p.2)))
            =ᶠ[𝓝 (s₀, y₀) ⊓ 𝓟 A]
            (fun p => normalNorm E (normalBlowUp E (tubeRadiusInterp ε ε' p.1) (C.inv p.2))) := by
          filter_upwards [hAmem] with p hp
          exact (normalNorm_normalBlowUp (hrfpos p.1) hp.2).symm
        have hlim : Tendsto (fun p : unitInterval × Work.Tubular.Euc (8 + k) =>
            tubeRadiusInterp ε ε' p.1 * normalNorm E (C.inv p.2)
              / (tubeRadiusInterp ε ε' p.1 - normalNorm E (C.inv p.2)))
            (𝓝 (s₀, y₀) ⊓ 𝓟 A) atTop := by
          refine tendsto_atTop.2 (fun a => ?_)
          have hden_small : ∀ᶠ p : unitInterval × Work.Tubular.Euc (8 + k) in 𝓝 (s₀, y₀) ⊓ 𝓟 A,
              tubeRadiusInterp ε ε' p.1 - normalNorm E (C.inv p.2)
                < (ε' ^ 2 / 2) / (max a 0 + 1) :=
            (tendsto_order.1 hdenA).2 _ (by
              have h1 : tubeRadiusInterp ε ε' s₀ - normalNorm E (C.inv y₀) ≤ 0 := by linarith
              have h2 : (0 : ℝ) < (ε' ^ 2 / 2) / (max a 0 + 1) := by positivity
              linarith)
          filter_upwards [hnum_ev, hden_small, hden_pos] with p hn hd hp
          have hKpos : (0 : ℝ) < max a 0 + 1 := by linarith [le_max_right a 0]
          have hd' : (tubeRadiusInterp ε ε' p.1 - normalNorm E (C.inv p.2)) * (max a 0 + 1)
              < ε' ^ 2 / 2 := (lt_div_iff₀ hKpos).mp hd
          have h4 : (max a 0 + 1) * (tubeRadiusInterp ε ε' p.1 - normalNorm E (C.inv p.2))
              < tubeRadiusInterp ε ε' p.1 * normalNorm E (C.inv p.2) := by nlinarith
          have h3 : (max a 0 + 1) ≤ tubeRadiusInterp ε ε' p.1 * normalNorm E (C.inv p.2)
              / (tubeRadiusInterp ε ε' p.1 - normalNorm E (C.inv p.2)) :=
            (le_div_iff₀ hp).mpr (le_of_lt h4)
          linarith [le_max_left a 0]
        filter_upwards [tendsto_atTop.1 (Tendsto.congr' heq hlim) (M + 1)] with p hp
        linarith
      have hfin' : ∀ᶠ p : unitInterval × Work.Tubular.Euc (8 + k) in 𝓝 (s₀, y₀),
          p ∈ A → M < normalNorm E (normalBlowUp E (tubeRadiusInterp ε ε' p.1) (C.inv p.2)) :=
        (eventually_inf_principal).mp hfin
      filter_upwards [hfin'] with p hp
      by_cases hpA : p ∈ A
      · rw [collapseRadial_of_mem C hpA.1 hpA.2]
        refine Or.inl ⟨_, fun hmem => ?_, rfl⟩
        have hle := hMK _ hmem
        linarith [hp hpA]
      · rw [collapseRadial_of_not C (fun h => hpA (hAdef ▸ h))]
        exact Or.inr rfl
  · -- the point is outside the tube
    have hmem : ∀ᶠ p : unitInterval × Work.Tubular.Euc (8 + k) in 𝓝 (s₀, y₀), p.2 ∉ C.U := by
      have h1 : (C.U)ᶜ ∈ 𝓝 y₀ := C.isClosed_U.isOpen_compl.mem_nhds hyU
      have h2 : ∀ᶠ y in 𝓝 y₀, y ∈ (C.U)ᶜ := h1
      have hsnd : Tendsto (fun p : unitInterval × Work.Tubular.Euc (8 + k) => p.2)
          (𝓝 (s₀, y₀)) (𝓝 y₀) := continuous_snd.continuousAt
      exact hsnd.eventually h2
    refine ContinuousAt.congr
      (f := fun _ : unitInterval × Work.Tubular.Euc (8 + k) => OnePoint.infty)
      continuousAt_const ?_
    filter_upwards [hmem] with p hp
    exact (collapseRadial_of_not_mem C hp).symm



/-! ## The collapse class depends only on the homotopy class of the collapse loop -/

/-- **Two homotopic collapse loops give the same collapse class.**  `Work.Tubular.collapseRelK8` is
obtained from the cube loop `Work.Tubular.tubeGenLoopOnePoint` by applying the Hurewicz chain and
two fixed linear maps, so the Hurewicz invariance of the chain under homotopies rel the boundary of
the cube (`Work.Stems.hurewiczChain_eq_of_homotopic`) gives the result. -/
theorem collapseRelK8_congr_of_homotopic {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
    {ε' : ℝ} (C' : Work.Tubular.TubeChart E ε')
    (g' : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg' : ∀ y, y ∉ C'.openTube → g' (OnePoint.some y) = OnePoint.infty)
    {R' : ℝ} (hR' : 0 ≤ R') (hbox' : ∀ y ∈ C'.U, ∀ j : Fin (8 + k), |y j| < R')
    (h : GenLoop.Homotopic (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox)
      (Work.Tubular.tubeGenLoopOnePoint C' g' hg' hR' hbox')) :
    Work.Tubular.collapseRelK8 C g hg hR hbox
      = Work.Tubular.collapseRelK8 C' g' hg' hR' hbox' := by
  have hchain := Work.Stems.hurewiczChain_eq_of_homotopic (8 + k) (by omega) h
  unfold Work.Tubular.collapseRelK8
  rw [hchain]

/-! ## Independence of the tube radius -/

/-- **The tube-radius homotopy.**  For two tube charts `C`, `C'` of the same embedding with
`ε' ≤ ε`, pinned collapse maps `g`, `g'`, and a common cube radius `ρ ≥ 0` satisfying the box
condition for both tubes, the two collapse loops of the cube are homotopic rel the boundary.

The homotopy interpolates the tube radius along `s ↦ (1-s) ε + s ε'` inside the *larger* chart `C`
(so that `C.inv` is available on all the intermediate tubes):
`H(s,t) = collapseRadial C ((1-s) ε + s ε') (cubeToEuc (8+k) ρ t)`.
Its continuity is `Work.ThomBordism.continuous_collapseRadial_interp`.  On the boundary of the cube
the point `cubeToEuc (8+k) ρ t` has a coordinate of absolute value `ρ`, hence lies outside
`C.U ⊇ openTubeSet E ε_s` by the box condition, so the homotopy lands on `∞` there.  The slices
`s = 0` and `s = 1` are the two collapse loops, by the pinned form of `g` and `g'`. -/
theorem tubeGenLoop_homotopic_tube {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε ε' : ℝ} (hle : ε' ≤ ε)
    (C : Work.Tubular.TubeChart E ε) (C' : Work.Tubular.TubeChart E ε')
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    (g' : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg' : ∀ y, y ∉ C'.openTube → g' (OnePoint.some y) = OnePoint.infty)
    (hg2' : ∀ y, y ∈ C'.openTube →
      g' (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε' (C'.inv y)))
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < ρ)
    (hbox' : ∀ y ∈ C'.U, ∀ j : Fin (8 + k), |y j| < ρ) :
    GenLoop.Homotopic (Work.Tubular.tubeGenLoopOnePoint C g hg hρ hbox)
      (Work.Tubular.tubeGenLoopOnePoint C' g' hg' hρ hbox') := by
  -- the pinned value of `g` on the cube
  have hgval : ∀ y : Work.Tubular.Euc (8 + k),
      g (OnePoint.some y) = collapseRadial C ε y := fun y => tubeData_apply C hg hg2 y
  -- the pinned value of `g'`, expressed as the collapse of the *large* chart at the small radius
  have hg'val : ∀ y : Work.Tubular.Euc (8 + k),
      g' (OnePoint.some y) = collapseRadial C ε' y := by
    intro y
    by_cases h : y ∈ C'.openTube
    · rw [collapseRadial_of_le_chart_mem C C' hle h, hg2' y h]
    · rw [collapseRadial_of_le_chart_notMem C C' hle h, hg' y h]
  -- continuity of the interpolated collapse, composed with the cube
  have hcont : Continuous (fun p : unitInterval × Work.Tubular.Euc (8 + k) =>
      collapseRadial C (tubeRadiusInterp ε ε' p.1) p.2) :=
    continuous_collapseRadial_interp_aux C C'.eps_pos hle
  have hcont' : Continuous (fun p : unitInterval × (Fin (8 + k) → unitInterval) =>
      collapseRadial C (tubeRadiusInterp ε ε' p.1)
        (cubeToEuc (8 + k) ρ p.2)) :=
    hcont.comp (continuous_fst.prodMk ((cubeToEuc (8 + k) ρ).continuous.comp continuous_snd))
  have h0 : ∀ x : Fin (8 + k) → unitInterval,
      collapseRadial C (tubeRadiusInterp ε ε' 0) (cubeToEuc (8 + k) ρ x)
        = tubeCollapseCubeOnePoint g ρ x := by
    intro x
    rw [tubeRadiusInterp_zero, tubeCollapseCubeOnePoint_apply]
    exact (hgval (cubeToEuc (8 + k) ρ x)).symm
  have h1 : ∀ x : Fin (8 + k) → unitInterval,
      collapseRadial C (tubeRadiusInterp ε ε' 1) (cubeToEuc (8 + k) ρ x)
        = tubeCollapseCubeOnePoint g' ρ x := by
    intro x
    rw [tubeRadiusInterp_one, tubeCollapseCubeOnePoint_apply]
    exact (hg'val (cubeToEuc (8 + k) ρ x)).symm
  have hprop : ∀ (t : unitInterval) (x : Fin (8 + k) → unitInterval),
      x ∈ Cube.boundary (Fin (8 + k)) →
      collapseRadial C (tubeRadiusInterp ε ε' t) (cubeToEuc (8 + k) ρ x)
        = tubeCollapseCubeOnePoint g ρ x := by
    intro t x hx
    rw [tubeCollapseCubeOnePoint_boundary C g hg hρ hbox hx]
    refine collapseRadial_of_not_mem C (fun hmem => ?_)
    obtain ⟨i, hi⟩ := cubeToEuc_boundary (8 + k) hρ hx
    have h2 := hbox _ hmem i
    rw [hi] at h2
    exact absurd h2 (lt_irrefl ρ)
  let Hfun : unitInterval × (Fin (8 + k) → unitInterval) → OnePoint (NormalTotal E) :=
    fun p => collapseRadial C (tubeRadiusInterp ε ε' p.1) (cubeToEuc (8 + k) ρ p.2)
  have hHcont : Continuous Hfun := hcont'
  exact ⟨⟨⟨Hfun, hHcont⟩, h0, h1⟩, hprop⟩

/-- **The collapse class does not depend on the tube data.**  For two tube charts `C`, `C'` of the
same embedding `E` (of radii `ε`, `ε'`), collapse maps `g`, `g'` pinned by the metric-free blow-up
formula on the respective open tubes (and `∞` outside), and cube radii `R`, `R'` satisfying the box
condition, the classes `collapseRelK8` agree.

Note (from the reviews): the tube data are almost forced — `C.U = tubeMap '' {‖·‖ ≤ ε}` and
`openTubeSet E ε` do not mention `C`, and `C.inv` is the tube inverse on `C.U` — so the content is
that the `ε`-collapse and the `ε'`-collapse of the cube differ by a *positive* fibrewise radial
rescaling (they are maps of pairs of the same degree `+1`).  Both a loop-homotopy argument (using
intermediate radii `ε_s = (1-s)ε + sε'` and a common large cube radius `ρ ≥ max R R'`, with the
intermediate collapse map defined on the tube of the *larger* chart so that `C.inv` is available) and
a degree/isotopy-of-pairs argument work; the cube-radius part is the separate lemma
`collapseRelK8_indep_R` (prove it inline, or import it once it is axiom-clean). -/
theorem collapseRelK8_indep_tube {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε ε' : ℝ}
    (C : Work.Tubular.TubeChart E ε) (C' : Work.Tubular.TubeChart E ε')
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    (g' : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg' : ∀ y, y ∉ C'.openTube → g' (OnePoint.some y) = OnePoint.infty)
    (hg2' : ∀ y, y ∈ C'.openTube →
      g' (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε' (C'.inv y)))
    {R R' : ℝ} (hR : 0 ≤ R) (hR' : 0 ≤ R')
    (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
    (hbox' : ∀ y ∈ C'.U, ∀ j : Fin (8 + k), |y j| < R') :
    Work.Tubular.collapseRelK8 C g hg hR hbox = Work.Tubular.collapseRelK8 C' g' hg' hR' hbox' := by
  -- a common cube radius for the two charts
  set ρ : ℝ := max R R' with hρdef
  have hρ0 : 0 ≤ ρ := le_trans hR (le_max_left R R')
  have hboxC : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < ρ :=
    fun y hy j => lt_of_lt_of_le (hbox y hy j) (le_max_left R R')
  have hboxC' : ∀ y ∈ C'.U, ∀ j : Fin (8 + k), |y j| < ρ :=
    fun y hy j => lt_of_lt_of_le (hbox' y hy j) (le_max_right R R')
  -- change the cube radius of both charts to `ρ`, then change the tube radius
  calc Work.Tubular.collapseRelK8 C g hg hR hbox
      = Work.Tubular.collapseRelK8 C g hg hρ0 hboxC :=
        collapseRelK8_indep_R C g hg hR hρ0 hbox hboxC
    _ = Work.Tubular.collapseRelK8 C' g' hg' hρ0 hboxC' := by
        rcases le_total ε' ε with hle | hle
        · exact collapseRelK8_congr_of_homotopic C g hg hρ0 hboxC C' g' hg' hρ0 hboxC'
            (tubeGenLoop_homotopic_tube hle C C' g hg hg2 g' hg' hg2' hρ0 hboxC hboxC')
        · exact (collapseRelK8_congr_of_homotopic C' g' hg' hρ0 hboxC' C g hg hρ0 hboxC
            (tubeGenLoop_homotopic_tube hle C' C g' hg' hg2' g hg hg2 hρ0 hboxC' hboxC)).symm
    _ = Work.Tubular.collapseRelK8 C' g' hg' hR' hbox' :=
        (collapseRelK8_indep_R C' g' hg' hR' hρ0 hbox' hboxC').symm

end

end Work.ThomBordism
