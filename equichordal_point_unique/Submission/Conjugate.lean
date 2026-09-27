import Submission.UnifDeps
import Submission.RiemannSurface
import Submission.Holomorphic
import Submission.Commons.Analysis.Complex.Analytic.eventually_eq_of_re_eq_zero
import Submission.Commons.Topology.Covering.section_of_monodromy_eq_self_weak

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

theorem exists_conjData {h : X → ℝ} (hh : HarmonicOnX h univ) (x : X) :
    ∃ (B : Set X) (F : X → ℂ), IsOpen B ∧ x ∈ B ∧ HolomorphicOnX F B ∧
      ∀ y ∈ B, (F y).re = h y := by
  have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hharm : HarmonicOnXAt h x := hh x (mem_univ x)
  rw [HarmonicOnXAt] at hharm
  obtain ⟨R₁, hR₁, hR₁sub⟩ := Metric.mem_nhds_iff.mp
    ((InnerProductSpace.isOpen_setOfPred_harmonicAt (h ∘ (chartAt ℂ x).symm)).mem_nhds hharm)
  obtain ⟨R₂, hR₂, hR₂sub⟩ := Metric.mem_nhds_iff.mp
    ((chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source hxsrc))
  have hρ : 0 < min R₁ R₂ / 2 := by positivity
  have hρ₁ : min R₁ R₂ / 2 ≤ R₁ := by linarith [min_le_left R₁ R₂, hR₁]
  have hρ₂ : min R₁ R₂ / 2 ≤ R₂ := by linarith [min_le_right R₁ R₂, hR₂]
  have hρsub : Metric.ball ((chartAt ℂ x) x) (min R₁ R₂ / 2) ⊆ (chartAt ℂ x).target :=
    (Metric.ball_subset_ball hρ₂).trans hR₂sub
  have hharm' : InnerProductSpace.HarmonicOnNhd (h ∘ (chartAt ℂ x).symm)
      (Metric.ball ((chartAt ℂ x) x) (min R₁ R₂ / 2)) :=
    fun w hw => hR₁sub (Metric.ball_subset_ball hρ₁ hw)
  obtain ⟨F₀, hF₀ana, hF₀re⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hharm'
  refine ⟨chartBall (chartAt ℂ x) ((chartAt ℂ x) x) (min R₁ R₂ / 2),
    fun y => F₀ ((chartAt ℂ x) y), chartBall_isOpen _ _ _, ?_, ?_, ?_⟩
  · rw [mem_chartBall]
    exact ⟨hxsrc, Metric.mem_ball_self hρ⟩
  · intro y hy
    rw [mem_chartBall] at hy
    obtain ⟨hysrc, hyball⟩ := hy
    rw [HolomorphicOnXAt_iff_chart hysrc]
    have hev : ((fun y : X => F₀ ((chartAt ℂ x) y)) ∘ (chartAt ℂ x).symm)
        =ᶠ[𝓝 ((chartAt ℂ x) y)] F₀ := by
      filter_upwards [(chartAt ℂ x).open_target.mem_nhds (hρsub hyball)] with w hw
      simp only [Function.comp_apply]
      rw [(chartAt ℂ x).right_inv hw]
    exact (hF₀ana _ hyball).congr hev.symm
  · intro y hy
    rw [mem_chartBall] at hy
    obtain ⟨hysrc, hyball⟩ := hy
    calc (F₀ ((chartAt ℂ x) y)).re = h ((chartAt ℂ x).symm ((chartAt ℂ x) y)) := hF₀re hyball
      _ = h y := by rw [(chartAt ℂ x).left_inv hysrc]

def conjGraph (B : Set X) (F : X → ℂ) : Set (X × ℝ) := {p | p.1 ∈ B ∧ p.2 = (F p.1).im}

def conjFamily (h : X → ℝ) : Set (Set (X × ℝ)) :=
  {S | ∃ (B : Set X) (F : X → ℂ), IsOpen B ∧ HolomorphicOnX F B ∧
      (∀ x ∈ B, (F x).re = h x) ∧ S = conjGraph B F}

def conjTopology (h : X → ℝ) : TopologicalSpace (X × ℝ) :=
  TopologicalSpace.generateFrom (conjFamily h)

theorem isOpen_conjGraph {h : X → ℝ} {B : Set X} {F : X → ℂ} (hB : IsOpen B)
    (hF : HolomorphicOnX F B) (hre : ∀ x ∈ B, (F x).re = h x) :
    IsOpen[conjTopology h] (conjGraph B F) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨B, F, hB, hF, hre, rfl⟩

theorem conjGraph_add (B : Set X) (F : X → ℂ) (c : ℂ) :
    conjGraph B (fun y => F y + c) = {p : X × ℝ | p.1 ∈ B ∧ p.2 = (F p.1).im + c.im} := by
  ext p
  simp [conjGraph, Complex.add_im]

theorem conjGraph_sub_real (B : Set X) (F : X → ℂ) (c : ℝ) :
    conjGraph B (fun y => F y - (c : ℂ) * Complex.I) =
      {p : X × ℝ | p.1 ∈ B ∧ p.2 = (F p.1).im - c} := by
  ext p
  simp [conjGraph, Complex.sub_im, Complex.mul_im, Complex.ofReal_im]

theorem holomorphicOnX_add_const {h : X → ℝ} {B : Set X} {F : X → ℂ} (hF : HolomorphicOnX F B)
    (hre : ∀ x ∈ B, (F x).re = h x) (c : ℂ) :
    HolomorphicOnX (fun y => F y + c) B ∧
      ∀ x ∈ B, ((fun y => F y + c) x).re = h x + c.re := by
  constructor
  · intro x hx
    have : (fun y : X => F y + c) = F + fun _ : X => c := rfl
    rw [this]
    exact (hF x hx).add (holomorphicOnXAt_const _ x)
  · intro x hx
    simp [Complex.add_re, hre x hx]

theorem holomorphicOnX_add_const' {h : X → ℝ} {B : Set X} {F : X → ℂ} (hF : HolomorphicOnX F B)
    (hre : ∀ x ∈ B, (F x).re = h x) (c : ℂ) (hc : c.re = 0) :
    HolomorphicOnX (fun y => F y + c) B ∧ ∀ x ∈ B, ((fun y => F y + c) x).re = h x := by
  obtain ⟨h1, h2⟩ := holomorphicOnX_add_const hF hre c
  exact ⟨h1, fun x hx => by rw [h2 x hx, hc, add_zero]⟩

theorem eventual_const_of_eventually_re {B : Set X} {F : X → ℂ} (hB : IsOpen B)
    (hF : HolomorphicOnX F B) (hre : ∀ x ∈ B, (F x).re = 0) {x : X} (hx : x ∈ B) :
    ∀ᶠ y in 𝓝 x, F y = F x := by
  have hcx : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hFx : AnalyticAt ℂ (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hF x hx
  have hcont : ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) x) :=
    (chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source hcx)
  have hx' : (chartAt ℂ x).symm ((chartAt ℂ x) x) ∈ B := by
    rw [(chartAt ℂ x).left_inv hcx]; exact hx
  have hevB : ∀ᶠ w in 𝓝 ((chartAt ℂ x) x), (chartAt ℂ x).symm w ∈ B :=
    hcont.eventually (hB.mem_nhds hx')
  have hev : ∀ᶠ w in 𝓝 ((chartAt ℂ x) x), ((F ∘ (chartAt ℂ x).symm) w).re = 0 := by
    filter_upwards [hevB] with w hw
    exact hre _ hw
  have h1 := Commons.Analysis.Complex.Analytic.eventually_eq_of_re_eq_zero hFx hev
  have h2 : ∀ᶠ y in 𝓝 x,
      (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y) = (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    ((chartAt ℂ x).continuousAt hcx).tendsto.eventually h1
  have h2x : (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = F x := by
    simp only [Function.comp_apply]
    rw [(chartAt ℂ x).left_inv hcx]
  filter_upwards [h2, (chartAt ℂ x).open_source.eventually_mem hcx] with y hy hysrc
  rw [← h2x, ← hy, Function.comp_apply, (chartAt ℂ x).left_inv hysrc]

/-- The set where `Im (G - F) = c` is open, `F`,`G` being conjugates of `h`. -/
theorem isOpen_setOf_im_sub_eq {h : X → ℝ} {B B' : Set X} {F G : X → ℂ} (hB : IsOpen B)
    (hF : HolomorphicOnX F B) (hreF : ∀ x ∈ B, (F x).re = h x)
    (hB' : IsOpen B') (hG : HolomorphicOnX G B') (hreG : ∀ x ∈ B', (G x).re = h x)
    (c : ℝ) : IsOpen {y | y ∈ B ∩ B' ∧ (G y).im - (F y).im = c} := by
  have hBi : IsOpen (B ∩ B') := hB.inter hB'
  have hH : HolomorphicOnX (G - F) (B ∩ B') :=
    (hG.mono Set.inter_subset_right).sub (hF.mono Set.inter_subset_left)
  have hreH : ∀ x ∈ B ∩ B', ((G - F) x).re = 0 := fun x hx => by
    simp [Complex.sub_re, hreG x hx.2, hreF x hx.1]
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyBi, hyc⟩
  have hev := eventual_const_of_eventually_re hBi hH hreH hyBi
  filter_upwards [hev, hBi.mem_nhds hyBi] with z hz hzBi
  refine ⟨hzBi, ?_⟩
  have hy0 : (G - F) y = ((c : ℝ) : ℂ) * Complex.I := by
    refine Complex.ext ?_ ?_
    · simpa using hreH y hyBi
    · simpa [Complex.sub_im] using hyc
  have hz0 : (G - F) z = ((c : ℝ) : ℂ) * Complex.I := hz.trans hy0
  have := congrArg Complex.im hz0
  simpa [Complex.sub_im] using this

theorem image_fst_conjGraph (B : Set X) (F : X → ℂ) : Prod.fst '' conjGraph B F = B := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp.1
  · intro hy
    exact ⟨(y, (F y).im), ⟨hy, rfl⟩, rfl⟩

/-- The fibre of `Prod.fst : X × ℝ → X` over `x`. -/
abbrev conjFiber (x : X) : Set (X × ℝ) := Prod.fst ⁻¹' ({x} : Set X)

/-- The set above `B`. -/
abbrev conjOver (B : Set X) : Set (X × ℝ) := Prod.fst ⁻¹' B

/-- The point of the fibre over `x` with second coordinate `w`. -/
def conjFiberPt (x : X) (w : ℝ) : ↥(conjFiber x) := ⟨(x, w), rfl⟩

theorem conjFiberPt_eq_iff {x : X} {w : ℝ} {i : ↥(conjFiber x)} :
    conjFiberPt x w = i ↔ w = i.1.2 := by
  constructor
  · intro h
    rw [← h]
    rfl
  · intro h
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact i.2.symm
    · exact h

/-- The trivialization of the étale space over a conjugate chart ball. -/
def conjTriv (B : Set X) (F : X → ℂ) (x : X) :
    ↥(conjOver B) → ↥B × ↥(conjFiber x) :=
  fun e => (⟨e.1.1, e.2⟩, conjFiberPt x (e.1.2 - (F e.1.1).im + (F x).im))

/-- The inverse of the trivialization. -/
def conjTrivSymm (B : Set X) (F : X → ℂ) (x : X) :
    ↥B × ↥(conjFiber x) → ↥(conjOver B) :=
  fun e => ⟨(e.1.1, e.2.1.2 + (F e.1.1).im - (F x).im), e.1.2⟩

theorem conjTriv_left_inv (B : Set X) (F : X → ℂ) (x : X) :
    Function.LeftInverse (conjTrivSymm B F x) (conjTriv B F x) := by
  rintro ⟨⟨y, v⟩, hy⟩
  refine Subtype.ext (Prod.ext rfl ?_)
  simp only [conjTriv, conjTrivSymm, conjFiberPt]
  ring

theorem conjTriv_right_inv (B : Set X) (F : X → ℂ) (x : X) :
    Function.RightInverse (conjTrivSymm B F x) (conjTriv B F x) := by
  rintro ⟨b, ⟨⟨p₁, p₂⟩, hp⟩⟩
  have hp' : p₁ = x := hp
  subst hp'
  refine Prod.ext (Subtype.ext rfl) (Subtype.ext (Prod.ext rfl ?_))
  simp only [conjTriv, conjTrivSymm, conjFiberPt]
  ring



theorem continuous_fst_conjTopology {h : X → ℝ} (hh : HarmonicOnX h univ) :
    @Continuous (X × ℝ) X (conjTopology h) _ Prod.fst := by
  letI : TopologicalSpace (X × ℝ) := conjTopology h
  rw [continuous_def]
  intro W hW
  rw [isOpen_iff_mem_nhds]
  rintro p hp
  obtain ⟨B, F, hB, hpB, hF, hre⟩ := exists_conjData hh p.1
  have hBW : IsOpen (B ∩ W) := hB.inter hW
  have hFm : HolomorphicOnX F (B ∩ W) := hF.mono Set.inter_subset_left
  have hrem : ∀ x ∈ B ∩ W, (F x).re = h x := fun x hx => hre x hx.1
  set c : ℂ := ((p.2 - (F p.1).im : ℝ) : ℂ) * Complex.I with hcdef
  have hcim : c.im = p.2 - (F p.1).im := by rw [hcdef]; simp
  have hF' : HolomorphicOnX (fun y => F y + c) (B ∩ W) :=
    (holomorphicOnX_add_const hFm hrem c).1
  have hre' : ∀ x ∈ B ∩ W, ((fun y => F y + c) x).re = h x :=
    fun x hx => by rw [(holomorphicOnX_add_const hFm hrem c).2 x hx, hcdef]; simp
  have hmem : p ∈ conjGraph (B ∩ W) (fun y => F y + c) := by
    rw [conjGraph_add]
    simp only [Set.mem_ofPred_eq]
    exact ⟨⟨hpB, hp⟩, by rw [hcim]; ring⟩
  have hsub : conjGraph (B ∩ W) (fun y => F y + c) ⊆ Prod.fst ⁻¹' W := by
    rintro q ⟨⟨-, hqW⟩, -⟩
    exact hqW
  exact Filter.mem_of_superset ((isOpen_conjGraph hBW hF' hre').mem_nhds hmem) hsub




/-- The translation action on the étale space. -/
def conjShift (c : ℝ) : X × ℝ → X × ℝ := fun p => (p.1, p.2 + c)

theorem conjShift_preimage_mem {h : X → ℝ} {S : Set (X × ℝ)} (hS : S ∈ conjFamily h) (c : ℝ) :
    conjShift c ⁻¹' S ∈ conjFamily h := by
  obtain ⟨B, F, hB, hF, hre, rfl⟩ := hS
  refine ⟨B, fun y => F y - (c : ℂ) * Complex.I, hB, ?_, ?_, ?_⟩
  · have : (fun y : X => F y - (c : ℂ) * Complex.I) = F - fun _ : X => (c : ℂ) * Complex.I := rfl
    rw [this]
    exact hF.sub (holomorphicOnX_const _)
  · intro x hx
    simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      hre x hx]
  · ext p
    simp only [Set.mem_preimage, conjShift, conjGraph, Set.mem_ofPred_eq, Complex.sub_im,
      Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one,
      mul_zero, sub_zero]
    constructor
    · rintro ⟨hpB, hp⟩; exact ⟨hpB, by linarith⟩
    · rintro ⟨hpB, hp⟩; exact ⟨hpB, by linarith⟩

theorem continuous_conjShift {h : X → ℝ} (c : ℝ) :
    @Continuous (X × ℝ) (X × ℝ) (conjTopology h) (conjTopology h)
      (conjShift c) := by
  letI : TopologicalSpace (X × ℝ) := conjTopology h
  rw [continuous_def]
  intro S hS
  change TopologicalSpace.GenerateOpen (conjFamily h) S at hS
  change TopologicalSpace.GenerateOpen (conjFamily h) (conjShift c ⁻¹' S)
  induction hS with
  | basic s hs => exact TopologicalSpace.GenerateOpen.basic _ (conjShift_preimage_mem hs c)
  | univ => simpa using TopologicalSpace.GenerateOpen.univ
  | inter s t _ _ ihs iht =>
      rw [preimage_inter]; exact TopologicalSpace.GenerateOpen.inter _ _ ihs iht
  | sUnion S _ ih =>
      rw [Set.preimage_sUnion,
        ← Set.sUnion_image (fun t : Set (X × ℝ) => conjShift c ⁻¹' t) S]
      exact TopologicalSpace.GenerateOpen.sUnion _ (fun s hs => by
        obtain ⟨t, htS, rfl⟩ := hs
        exact ih t htS)


section Covering

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

open scoped Classical in
set_option maxHeartbeats 400000 in
theorem isCoveringMap_fst_conjTopology {h : X → ℝ} (hh : HarmonicOnX h univ) :
    @IsCoveringMap (X × ℝ) X (conjTopology h) _ Prod.fst := by
  letI : TopologicalSpace (X × ℝ) := conjTopology h
  intro x
  obtain ⟨B, F, hB, hxB, hF, hre⟩ := exists_conjData hh x
  have hdisc : DiscreteTopology ↥(conjFiber x) := by
    rw [discreteTopology_iff_isOpen_singleton]
    rintro ⟨p, hp⟩
    obtain ⟨B₀, F₀, hB₀, hpB₀, hF₀, hre₀⟩ := exists_conjData hh p.1
    set c : ℂ := Complex.ofReal (p.2 - (F₀ p.1).im) * Complex.I with hcdef
    have hcim : c.im = p.2 - (F₀ p.1).im := by rw [hcdef]; simp
    have hF₀' := holomorphicOnX_add_const' hF₀ hre₀ c (by rw [hcdef]; simp)
    have hmem : p ∈ conjGraph B₀ (fun y => F₀ y + c) := by
      rw [conjGraph_add]
      exact ⟨hpB₀, by rw [hcim]; ring⟩
    have hopen : IsOpen (conjGraph B₀ (fun y => F₀ y + c)) := isOpen_conjGraph hB₀ hF₀'.1 hF₀'.2
    rw [show ({⟨p, hp⟩} : Set ↥(conjFiber x))
        = Subtype.val ⁻¹' conjGraph B₀ (fun y => F₀ y + c) from ?_]
    · exact hopen.preimage continuous_subtype_val
    · ext q
      constructor
      · intro hq
        rw [Set.mem_singleton_iff] at hq
        subst hq
        exact hmem
      · intro hq
        rw [Set.mem_singleton_iff]
        have hq1 : (q : X × ℝ).1 = x := q.2
        have hp1 : p.1 = x := hp
        have hq2 : (q : X × ℝ).2 = ((fun y => F₀ y + c) (q : X × ℝ).1).im := hq.2
        have hp2 : p.2 = ((fun y => F₀ y + c) p.1).im := hmem.2
        exact Subtype.ext (Prod.ext (by rw [hq1, hp1]) (by rw [hq2, hp2, hq1, hp1]))
  have hopenOver : IsOpen (conjOver B) := by
    have hset : (conjOver B) = ⋃ t : ℝ,
        conjGraph B (fun y => F y + Complex.ofReal t * Complex.I) := by
      ext p
      constructor
      · intro hp
        refine Set.mem_iUnion.mpr ⟨p.2 - (F p.1).im, ?_⟩
        rw [conjGraph_add]
        refine ⟨hp, ?_⟩
        have hc : (Complex.ofReal (p.2 - (F p.1).im) * Complex.I).im = p.2 - (F p.1).im := by
          simp
        rw [hc]; ring
      · intro hp
        obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hp
        exact ht.1
    rw [hset]
    refine isOpen_iUnion fun t => isOpen_conjGraph hB ?_ ?_
    · exact (holomorphicOnX_add_const' hF hre _ (by simp)).1
    · exact (holomorphicOnX_add_const' hF hre _ (by simp)).2
  have hcontτ : Continuous (conjTriv B F x) := by
    have hfst : Continuous (Prod.fst : X × ℝ → X) := continuous_fst_conjTopology hh
    have h1 : Continuous (fun e : ↥(conjOver B) => (⟨e.1.1, e.2⟩ : ↥B)) :=
      Continuous.subtype_mk (f := fun e : ↥(conjOver B) => (e.1 : X × ℝ).1)
        (hfst.comp (continuous_subtype_val : Continuous (Subtype.val : ↥(conjOver B) → X × ℝ))) _
    have h2 : Continuous (fun e : ↥(conjOver B) =>
        conjFiberPt x (e.1.2 - (F e.1.1).im + (F x).im)) := by
      rw [continuous_def]
      intro S hS
      rw [show (fun e : ↥(conjOver B) => conjFiberPt x (e.1.2 - (F e.1.1).im + (F x).im)) ⁻¹' S
          = ⋃ (i : ↥(conjFiber x)) (_ : i ∈ S),
              (fun e : ↥(conjOver B) => conjFiberPt x
                (e.1.2 - (F e.1.1).im + (F x).im)) ⁻¹' {i} from ?_]
      · refine isOpen_iUnion fun i => isOpen_iUnion fun _ => ?_
        have hset : (fun e : ↥(conjOver B) => conjFiberPt x
              (e.1.2 - (F e.1.1).im + (F x).im)) ⁻¹' {i}
            = Subtype.val ⁻¹' conjGraph B
                (fun y => F y + Complex.ofReal (i.1.2 - (F x).im) * Complex.I) := by
          ext z
          constructor
          · intro hz
            simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
            rw [conjFiberPt_eq_iff] at hz
            have hc : (Complex.ofReal (i.1.2 - (F x).im) * Complex.I).im = i.1.2 - (F x).im := by
              simp
            rw [conjGraph_add]
            exact ⟨z.2, by rw [hc]; linarith⟩
          · intro hz
            rw [conjGraph_add] at hz
            obtain ⟨hzB, hz2⟩ := hz
            have hc : (Complex.ofReal (i.1.2 - (F x).im) * Complex.I).im = i.1.2 - (F x).im := by
              simp
            rw [hc] at hz2
            simp only [Set.mem_preimage, Set.mem_singleton_iff]
            rw [conjFiberPt_eq_iff]
            linarith
        rw [hset]
        refine (isOpen_conjGraph hB ?_ ?_).preimage continuous_subtype_val
        · exact (holomorphicOnX_add_const' hF hre _ (by simp)).1
        · exact (holomorphicOnX_add_const' hF hre _ (by simp)).2
      · ext z
        simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff]
        constructor
        · intro hz
          exact ⟨conjFiberPt x (z.1.2 - (F z.1.1).im + (F x).im), hz, rfl⟩
        · rintro ⟨i, hi, hzi⟩
          rw [hzi]; exact hi
    exact h1.prodMk h2
  have hcontσ : Continuous (fun z : ↥B × ↥(conjFiber x) =>
      ((conjTrivSymm B F x z : ↥(conjOver B)) : X × ℝ)) := by
    rw [continuous_def]
    intro S hS
    change TopologicalSpace.GenerateOpen (conjFamily h) S at hS
    induction hS with
    | basic s hs =>
        obtain ⟨B', G, hB', hG, hreG, rfl⟩ := hs
        rw [show (fun z : ↥B × ↥(conjFiber x) =>
              ((conjTrivSymm B F x z : ↥(conjOver B)) : X × ℝ)) ⁻¹' conjGraph B' G
            = ⋃ (i : ↥(conjFiber x)),
                ({b : ↥B | b.1 ∈ B' ∧ i.1.2 + (F b.1).im - (F x).im = (G b.1).im}
                  ×ˢ ({i} : Set ↥(conjFiber x))) from ?_]
        · refine isOpen_iUnion fun i => ?_
          have hbase : IsOpen {b : ↥B | b.1 ∈ B' ∧ i.1.2 + (F b.1).im - (F x).im = (G b.1).im} := by
            have hX : IsOpen {y : X | y ∈ B ∩ B' ∧ (G y).im - (F y).im = i.1.2 - (F x).im} :=
              isOpen_setOf_im_sub_eq hB hF hre hB' hG hreG _
            have hset : {b : ↥B | b.1 ∈ B' ∧ i.1.2 + (F b.1).im - (F x).im = (G b.1).im}
                = Subtype.val ⁻¹' {y : X | y ∈ B ∩ B' ∧
                    (G y).im - (F y).im = i.1.2 - (F x).im} := by
              ext b
              constructor
              · rintro ⟨hb', hc⟩
                exact ⟨⟨b.2, hb'⟩, by linarith⟩
              · rintro ⟨⟨-, hb'⟩, hc⟩
                exact ⟨hb', by linarith⟩
            rw [hset]
            exact hX.preimage continuous_subtype_val
          exact hbase.prod (isOpen_discrete _)
        · ext z
          obtain ⟨b, i⟩ := z
          simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_setOf_eq,
            Set.mem_singleton_iff, conjGraph, conjTrivSymm]
          constructor
          · rintro ⟨hzB, hz2⟩
            exact ⟨i, ⟨hzB, by linarith⟩, rfl⟩
          · rintro ⟨i', ⟨hzB, hz2⟩, hi'⟩
            subst hi'
            exact ⟨hzB, by linarith⟩
    | univ => simp
    | inter s t _ _ ihs iht => rw [Set.preimage_inter]; exact ihs.inter iht
    | sUnion S _ ih =>
        rw [Set.preimage_sUnion]
        exact isOpen_iUnion fun t => isOpen_iUnion fun ht => ih t ht
  let H : ↥(conjOver B) ≃ ↥B × ↥(conjFiber x) :=
    { toFun := conjTriv B F x, invFun := conjTrivSymm B F x,
      left_inv := conjTriv_left_inv B F x, right_inv := conjTriv_right_inv B F x }
  refine ⟨hdisc, B, hxB, hB, hopenOver, ?_, ?_⟩
  · exact Homeomorph.mk H hcontτ
      (Continuous.subtype_mk hcontσ (fun z => (conjTrivSymm B F x z).2))
  · rintro ⟨e, he⟩
    rfl

end Covering



section Monodromy

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The translation on a fibre, as a map of fibres. -/
def conjFiberShift (c : ℝ) {x : X} (e : ↥(conjFiber x)) : ↥(conjFiber x) :=
  ⟨(e.1.1, e.1.2 + c), e.2⟩

@[simp] theorem conjFiberShift_coe (c : ℝ) {x : X} (e : ↥(conjFiber x)) :
    (conjFiberShift c e).1 = conjShift (X := X) c e.1 := rfl

theorem monodromy_mk_liftPath {E : Type*} [TopologicalSpace E] {p : E → X}
    (cov : IsCoveringMap p) {a b : X} (γ : Path a b) (e : E) (he : p e = a) :
    (cov.monodromy (Path.Homotopic.Quotient.mk γ) ⟨e, he⟩).1 =
      cov.liftPath γ e (γ.source.trans he.symm) 1 := rfl

theorem liftPath_conjShift_apply [htop : TopologicalSpace (X × ℝ)]
    (cov : IsCoveringMap (Prod.fst : X × ℝ → X)) (c : ℝ)
    (hσ : Continuous (conjShift (X := X) c))
    {x y : X} (γ : Path x y) (e : X × ℝ) (he : γ 0 = Prod.fst e) :
    ∀ t : unitInterval,
      cov.liftPath γ (conjShift (X := X) c e) (by rw [conjShift]; exact he) t =
        conjShift (X := X) c (cov.liftPath γ e he t) := by
  intro t
  have h := (cov.eq_liftPath_iff' (γ := γ) (e := conjShift (X := X) c e)
    (γ_0 := by rw [conjShift]; exact he)
    (Γ := ⟨fun s => conjShift (X := X) c (cov.liftPath γ e he s),
      hσ.comp (cov.liftPath γ e he).continuous⟩)).mpr ?_
  · rw [← h]
    rfl
  · refine ⟨?_, ?_⟩
    · funext s
      simp only [ContinuousMap.coe_mk, Function.comp_apply]
      rw [show Prod.fst (conjShift (X := X) c (cov.liftPath γ e he s))
          = Prod.fst (cov.liftPath γ e he s) from rfl]
      exact congr_fun (cov.liftPath_lifts γ e he) s
    · simp only [ContinuousMap.coe_mk]
      rw [cov.liftPath_zero]

theorem monodromy_conjFiberShift [htop : TopologicalSpace (X × ℝ)]
    (cov : IsCoveringMap (Prod.fst : X × ℝ → X)) (c : ℝ)
    (hσ : Continuous (conjShift (X := X) c))
    {x y : X} (γ : Path.Homotopic.Quotient x y) (e : ↥(conjFiber x)) :
    cov.monodromy γ (conjFiberShift c e) = conjFiberShift c (cov.monodromy γ e) := by
  obtain ⟨γ⟩ := γ
  apply Subtype.ext
  apply Prod.ext
  · exact (cov.monodromy _ (conjFiberShift c e)).2.trans
      ((conjFiberShift c (cov.monodromy _ e)).2).symm
  · show (cov.monodromy (Path.Homotopic.Quotient.mk γ) (conjFiberShift c e)).1.2
      = (conjFiberShift c (cov.monodromy (Path.Homotopic.Quotient.mk γ) e)).1.2
    rw [show conjFiberShift c e = (⟨conjShift (X := X) c e.1, e.2⟩ : ↥(conjFiber x)) from rfl]
    rw [monodromy_mk_liftPath cov γ (conjShift (X := X) c e.1) e.2]
    rw [show conjFiberShift c (cov.monodromy (Path.Homotopic.Quotient.mk γ) e)
        = (⟨conjShift (X := X) c
              (cov.liftPath γ e.1 (γ.source.trans e.2.symm) 1),
            (cov.monodromy (Path.Homotopic.Quotient.mk γ) e).2⟩ : ↥(conjFiber y)) from by
      refine Subtype.ext ?_
      exact congrArg (conjShift (X := X) c) (monodromy_mk_liftPath cov γ e.1 e.2)]
    exact congrArg (fun z : X × ℝ => z.2)
      (liftPath_conjShift_apply cov c hσ γ e.1 (γ.source.trans e.2.symm) 1)

/-- The period of a loop, read off from the monodromy of the covering. -/
noncomputable def conjPeriod [htop : TopologicalSpace (X × ℝ)] (x : X) (e₀ : ↥(conjFiber x))
    (cov : IsCoveringMap (Prod.fst : X × ℝ → X)) (γ : FundamentalGroup X x) : ℝ :=
  (cov.monodromy γ e₀).1.2 - e₀.1.2

theorem monodromy_eq_conjFiberShift [htop : TopologicalSpace (X × ℝ)]
    (cov : IsCoveringMap (Prod.fst : X × ℝ → X)) (x : X) (e₀ : ↥(conjFiber x))
    (γ : FundamentalGroup X x) :
    cov.monodromy γ e₀ = conjFiberShift (conjPeriod x e₀ cov γ) e₀ := by
  apply Subtype.ext
  apply Prod.ext
  · exact (cov.monodromy γ e₀).2.trans e₀.2.symm
  · simp only [conjFiberShift, conjPeriod]
    ring

theorem conjPeriod_add [htop : TopologicalSpace (X × ℝ)]
    (cov : IsCoveringMap (Prod.fst : X × ℝ → X)) (x : X) (e₀ : ↥(conjFiber x))
    (hσ : ∀ c : ℝ, Continuous (conjShift (X := X) c))
    (γ₁ γ₂ : FundamentalGroup X x) :
    conjPeriod x e₀ cov (γ₁ * γ₂) = conjPeriod x e₀ cov γ₁ + conjPeriod x e₀ cov γ₂ := by
  have h2 : cov.monodromy γ₁ (conjFiberShift (conjPeriod x e₀ cov γ₂) e₀)
      = conjFiberShift (conjPeriod x e₀ cov γ₂) (cov.monodromy γ₁ e₀) :=
    monodromy_conjFiberShift cov (conjPeriod x e₀ cov γ₂)
      (hσ (conjPeriod x e₀ cov γ₂)) γ₁ e₀
  rw [FundamentalGroup.mul_def, conjPeriod, cov.monodromy_trans_apply γ₂ γ₁ e₀]
  rw [monodromy_eq_conjFiberShift cov x e₀ γ₂, h2,
    monodromy_eq_conjFiberShift cov x e₀ γ₁]
  simp only [conjFiberShift, conjPeriod]
  ring

theorem conjPeriod_one [htop : TopologicalSpace (X × ℝ)]
    (cov : IsCoveringMap (Prod.fst : X × ℝ → X)) (x : X) (e₀ : ↥(conjFiber x)) :
    conjPeriod x e₀ cov 1 = 0 := by
  rw [show (1 : FundamentalGroup X x) = Path.Homotopic.Quotient.refl x from rfl]
  simp [conjPeriod, cov.monodromy_refl]

/-- The period of a loop as an additive homomorphism. -/
noncomputable def conjPeriodHom [htop : TopologicalSpace (X × ℝ)] (x : X)
    (e₀ : ↥(conjFiber x)) (cov : IsCoveringMap (Prod.fst : X × ℝ → X))
    (hσ : ∀ c : ℝ, Continuous (conjShift (X := X) c)) :
    Additive (FundamentalGroup X x) →+ ℝ where
  toFun a := conjPeriod x e₀ cov a.toMul
  map_zero' := conjPeriod_one cov x e₀
  map_add' a b := conjPeriod_add cov x e₀ hσ a.toMul b.toMul

end Monodromy

section Final

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [ConnectedSpace X]

/-- **Existence of a global holomorphic conjugate.**  On a connected complex one-manifold whose
fundamental group has no nontrivial homomorphism to `ℝ`, every harmonic function is the real part
of a global holomorphic function. -/
theorem exists_holomorphicOnX_re_of_harmonic (x : X)
    [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    {h : X → ℝ} (hh : HarmonicOnX h univ) :
    ∃ F : X → ℂ, HolomorphicOnX F univ ∧ ∀ y, (F y).re = h y := by
  letI : TopologicalSpace (X × ℝ) := conjTopology h
  haveI : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace (H := ℂ) (M := X)
  have cov : IsCoveringMap (Prod.fst : X × ℝ → X) := isCoveringMap_fst_conjTopology hh
  have hσ : ∀ c : ℝ, Continuous (conjShift (X := X) c) := fun c => continuous_conjShift c
  have hper : ∀ γ : FundamentalGroup X x, conjPeriod x (conjFiberPt x 0) cov γ = 0 := by
    intro γ
    have h0 : conjPeriodHom x (conjFiberPt x 0) cov hσ = 0 := Subsingleton.elim _ _
    have := congrFun (congrArg (fun f : Additive (FundamentalGroup X x) →+ ℝ =>
      (f : Additive (FundamentalGroup X x) → ℝ)) h0) (Additive.ofMul γ)
    simpa [conjPeriodHom, conjPeriod] using this
  have hmono : ∀ γ : FundamentalGroup X x,
      cov.monodromy γ (conjFiberPt x 0) = conjFiberPt x 0 := by
    intro γ
    rw [monodromy_eq_conjFiberShift cov x (conjFiberPt x 0) γ, hper γ]
    refine Subtype.ext (Prod.ext rfl ?_)
    simp [conjFiberShift, conjFiberPt]
  obtain ⟨σ, hσ0, hσp⟩ :=
    Commons.Topology.Covering.section_of_monodromy_eq_self_weak cov (x, 0) (fun γ => hmono γ)
  refine ⟨fun y => (h y : ℂ) + Complex.I * (σ y).2, ?_, ?_⟩
  · intro y _
    obtain ⟨B, G, hB, hyB, hG, hreG⟩ := exists_conjData hh y
    set t : ℝ := (σ y).2 - (G y).im with htdef
    set G' : X → ℂ := fun z => G z + Complex.I * (t : ℂ) with hG'def
    have hIre : (Complex.I * (t : ℂ)).re = 0 := by simp
    have hIim : (Complex.I * (t : ℂ)).im = t := by simp
    have hG're : ∀ z ∈ B, (G' z).re = h z := by
      intro z hz
      rw [hG'def, Complex.add_re, hreG z hz, hIre, add_zero]
    have hG'hol : HolomorphicOnX G' B := by
      rw [hG'def]
      exact (holomorphicOnX_add_const hG hreG (Complex.I * (t : ℂ))).1
    have hsym : σ y ∈ conjGraph B G' := by
      refine ⟨?_, ?_⟩
      · show (σ y).1 ∈ B
        rw [hσp y]; exact hyB
      · show (σ y).2 = (G' (σ y).1).im
        rw [hG'def, hσp y, Complex.add_im, hIim, htdef]
        ring
    have hnbhd : ∀ᶠ z in 𝓝 y, σ z ∈ conjGraph B G' :=
      (σ.continuous.continuousAt.eventually ((isOpen_conjGraph hB hG'hol hG're).mem_nhds hsym))
    have hev : (fun z : X => (h z : ℂ) + Complex.I * (σ z).2) =ᶠ[𝓝 y] G' := by
      filter_upwards [hnbhd] with z hz
      have hz2 : (σ z).2 = (G' z).im := by
        have h1 : (σ z).1 ∈ B ∧ (σ z).2 = (G' (σ z).1).im := hz
        rw [hσp z] at h1
        exact h1.2
      have hzB : z ∈ B := by rw [← hσp z]; exact hz.1
      apply Complex.ext
      · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, add_zero]
        rw [hG're z hzB]
      · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
          Complex.ofReal_re, Complex.ofReal_im, zero_add]
        rw [hz2]
    rw [HolomorphicOnXAt]
    have hcyt : ((chartAt ℂ y) y) ∈ (chartAt ℂ y).target :=
      (chartAt ℂ y).map_source (mem_chart_source ℂ y)
    have hyc : (chartAt ℂ y).symm ((chartAt ℂ y) y) = y :=
      (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
    have hcont : ContinuousAt (chartAt ℂ y).symm ((chartAt ℂ y) y) :=
      (chartAt ℂ y).continuousAt_symm hcyt
    have hev2 : (fun z : X => (h z : ℂ) + Complex.I * (σ z).2)
        =ᶠ[𝓝 ((chartAt ℂ y).symm ((chartAt ℂ y) y))] G' := by
      rw [hyc]; exact hev
    have hev' : ((fun z : X => (h z : ℂ) + Complex.I * (σ z).2) ∘ (chartAt ℂ y).symm)
        =ᶠ[𝓝 ((chartAt ℂ y) y)] (G' ∘ (chartAt ℂ y).symm) :=
      hcont.eventually hev2
    exact AnalyticAt.congr (hG'hol y hyB) hev'.symm
  · intro y
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_one, mul_zero, sub_zero, zero_mul, add_zero]

end Final

end Submission
