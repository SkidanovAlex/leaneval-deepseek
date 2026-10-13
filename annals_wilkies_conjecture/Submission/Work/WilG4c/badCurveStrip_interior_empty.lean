import Mathlib
import Submission.Work.WilG4c.StepLipDefs
import Submission.Work.WilG1.Main
import Submission.Work.WilG4c.HbddSide
import Submission.Work.WilG4c.graphOf_member_mem
import Submission.Work.WilG4c.PullXLip
import Submission.Work.WilG4c.contDiffAt_famFunHat_xPt
import Submission.Work.WilG4c.exists_nearmax_of_bdd
import Submission.Work.WilG1.Cell.smooth_k_cover
import Submission.Work.WilG1.Cell.thin_closure

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.WilG4c

open Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 0. Elementary helpers -/

theorem isOpen_openCube (μ : ℕ) : IsOpen (openCube μ) := by
  have h : openCube μ = ⋂ i : Fin μ, {t : Fin μ → ℝ | t i ∈ Set.Ioo (0 : ℝ) 1} := by
    ext t
    simp only [openCube, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (continuous_apply i)

/-- For a finite order, the `C^m`-locus is open. -/
theorem isOpen_contDiffAt_locus {N : ℕ} (m : ℕ) (g : (Fin N → ℝ) → ℝ) :
    IsOpen {z : Fin N → ℝ | ContDiffAt ℝ m g z} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hz' : ContDiffAt ℝ m g z := by simpa using hz
  exact Filter.mem_of_superset (hz'.eventually (by simp)) (fun y hy => hy)

/-- For a finite order, a point of the `C^m`-locus is an interior point of it. -/
theorem mem_interior_contDiffAt_locus {N : ℕ} (m : ℕ) (g : (Fin N → ℝ) → ℝ) (z : Fin N → ℝ) :
    z ∈ interior {z' : Fin N → ℝ | ContDiffAt ℝ m g z'} ↔ ContDiffAt ℝ m g z := by
  rw [(isOpen_contDiffAt_locus m g).interior_eq]
  exact Iff.rfl

/-- The continuous linear map `t ↦ Fin.cons 0 t`. -/
def consLin (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) where
  toFun := fun t => Fin.cons 0 t
  map_add' := by
    intro a b
    funext k
    refine Fin.cases ?_ ?_ k <;> simp [Fin.cons_zero, Fin.cons_succ]
  map_smul' := by
    intro c a
    funext k
    refine Fin.cases ?_ ?_ k <;> simp [Fin.cons_zero, Fin.cons_succ]

@[simp] theorem consLin_apply (n : ℕ) (t : Fin n → ℝ) : consLin n t = Fin.cons 0 t := rfl

theorem consLin_single {n : ℕ} (i : Fin n) :
    consLin n (Pi.single i 1) = (Pi.single i.succ 1 : Fin (n + 1) → ℝ) := by
  funext k
  rw [consLin_apply]
  refine Fin.cases ?_ ?_ k
  · rw [Fin.cons_zero, Pi.single_eq_of_ne (Fin.succ_ne_zero i).symm]
  · intro j
    rw [Fin.cons_succ]
    by_cases hji : j = i
    · subst hji
      rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hji,
        Pi.single_eq_of_ne (by intro h; exact hji (Fin.succ_injective n h))]

/-- A `y`-partial of `g` at `Fin.cons x y` is bounded by the operator norm of the derivative of
the slice `y ↦ g (Fin.cons x y)`.  No differentiability hypothesis is needed: when `g` is not
differentiable at `Fin.cons x y` the left-hand side is the junk value `0`. -/
theorem abs_fderiv_cons_le {n : ℕ} (g : (Fin (n + 1) → ℝ) → ℝ) (x : ℝ) (y : Fin n → ℝ)
    (i : Fin n) :
    |fderiv ℝ g (Fin.cons x y) (Pi.single i.succ 1)|
      ≤ ‖iteratedFDeriv ℝ 1 (slice g x) y‖ := by
  have hL : consLin n (Pi.single i 1) = (Pi.single i.succ 1 : Fin (n + 1) → ℝ) :=
    consLin_single i
  have hslice : slice g x = fun t : Fin n → ℝ => g (Fin.cons x t) := rfl
  by_cases hd : DifferentiableAt ℝ g (Fin.cons x y)
  · have hφ : HasFDerivAt (fun t : Fin n → ℝ => Fin.cons x t) (consLin n) y := by
      have hfun : (fun t : Fin n → ℝ => Fin.cons x t)
          = fun t : Fin n → ℝ => (Fin.cons x 0 : Fin (n + 1) → ℝ) + consLin n t := by
        funext t k
        refine Fin.cases ?_ ?_ k <;> simp [consLin_apply, Fin.cons_zero, Fin.cons_succ]
      rw [hfun]
      exact (ContinuousLinearMap.hasFDerivAt (consLin n)).const_add _
    have hcomp : HasFDerivAt (fun t : Fin n → ℝ => g (Fin.cons x t))
        ((fderiv ℝ g (Fin.cons x y)).comp (consLin n)) y := hd.hasFDerivAt.comp y hφ
    have hder : fderiv ℝ (slice g x) y = (fderiv ℝ g (Fin.cons x y)).comp (consLin n) := by
      rw [hslice]; exact hcomp.fderiv
    have hval : fderiv ℝ (slice g x) y (Pi.single i 1)
        = fderiv ℝ g (Fin.cons x y) (Pi.single i.succ 1) := by
      rw [hder, ContinuousLinearMap.comp_apply, hL]
    calc |fderiv ℝ g (Fin.cons x y) (Pi.single i.succ 1)|
        = |fderiv ℝ (slice g x) y (Pi.single i 1)| := by rw [hval]
      _ = ‖fderiv ℝ (slice g x) y (Pi.single i 1)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (slice g x) y‖ * ‖(Pi.single i 1 : Fin n → ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (slice g x) y‖ := by rw [Pi.norm_single, norm_one, mul_one]
      _ = ‖iteratedFDeriv ℝ 1 (slice g x) y‖ :=
          (norm_iteratedFDeriv_one (𝕜 := ℝ) (f := slice g x) (x := y)).symm
  · have hzero : fderiv ℝ g (Fin.cons x y) = 0 :=
      fderiv_zero_of_not_differentiableAt hd
    rw [hzero]
    simp

/-! ## 1. The non-`C¹` locus has nowhere dense closure -/

/-- The closure of the non-`C¹` locus of a definable function is nowhere dense: the
`interior (closure ·) = ∅` strengthening of generic smoothness (`smooth_k_cover`). -/
theorem interior_closure_nonC1_empty (S : WilkiesDesign.SOMin) (hcd : S.SharpCD)
    {N F D : ℕ} (g : (Fin N → ℝ) → ℝ) (hg : WilkiesDesign.graphOf g ∈ S.Ω F D (N + 1)) :
    interior (closure {z : Fin N → ℝ | ¬ ContDiffAt ℝ 1 g z}) = ∅ := by
  obtain ⟨m, a, b, A, hA, hint, hsub⟩ :=
    Work.WilG1.Cell.smooth_k_cover (S := S) hcd (k := 1) g hg
  have hnw : ∀ i : Fin m, IsNowhereDense (A i) := fun i =>
    Work.WilG1.Cell.thin_closure (S := S) hcd (hA i) (hint i)
  have hnwU : IsNowhereDense (⋃ i : Fin m, A i) := IsNowhereDense.iUnion hnw
  exact Set.eq_empty_of_subset_empty
    (le_trans (interior_mono (closure_mono hsub)) (le_of_eq hnwU))

/-! ## 2. The coordinate maps `ℝ^{p+1} × ℝ^n → ℝ^{p+(n+1)}` -/

variable {p n : ℕ}

/-- The ambient point `(l, x, y) ∈ ℝ^{p+(n+1)}` attached to `w = (l,x) ∈ ℝ^{p+1}` and `y`. -/
def yPt (w : Fin (p + 1) → ℝ) (y : Fin n → ℝ) : Fin (p + (n + 1)) → ℝ :=
  xPt (fun i => w (Fin.castSucc i)) (w (Fin.last p)) y

/-- The `(l,x)`-part of a point of `ℝ^{p+(n+1)}`. -/
def takeLx (z : Fin (p + (n + 1)) → ℝ) : Fin (p + 1) → ℝ :=
  Fin.snoc (fun i : Fin p => z (Fin.castAdd (n + 1) i)) (z (Fin.natAdd p 0))

/-- The `y`-part of a point of `ℝ^{p+(n+1)}`. -/
def takeY (z : Fin (p + (n + 1)) → ℝ) : Fin n → ℝ := fun j => z (yIdx p n j)

theorem continuous_takeLx : Continuous (takeLx (p := p) (n := n)) := by
  rw [continuous_pi_iff]
  intro i
  refine Fin.lastCases ?_ ?_ i
  · have he : (fun z : Fin (p + (n + 1)) → ℝ => takeLx z (Fin.last p))
        = fun z => z (Fin.natAdd p 0) := by
      funext z; simp [takeLx]
    rw [he]; exact continuous_apply _
  · intro i'
    have he : (fun z : Fin (p + (n + 1)) → ℝ => takeLx z i'.castSucc)
        = fun z => z (Fin.castAdd (n + 1) i') := by
      funext z; simp [takeLx]
    rw [he]; exact continuous_apply _

theorem continuous_takeY : Continuous (takeY (p := p) (n := n)) := by
  rw [continuous_pi_iff]
  intro j
  exact continuous_apply _

theorem continuous_yPt (y : Fin n → ℝ) : Continuous (fun w : Fin (p + 1) → ℝ => yPt w y) := by
  rw [continuous_pi_iff]
  intro k
  refine Fin.addCases (m := p) (n := n + 1) ?_ ?_ k
  · intro i
    have he : (fun w : Fin (p + 1) → ℝ => yPt w y (Fin.castAdd (n + 1) i))
        = fun w => w (Fin.castSucc i) := by
      funext w
      simp only [yPt, xPt, Fin.append_left]
    rw [he]; exact continuous_apply _
  · intro j
    refine Fin.cases ?_ ?_ j
    · have he : (fun w : Fin (p + 1) → ℝ => yPt w y (Fin.natAdd p 0))
          = fun w => w (Fin.last p) := by
        funext w
        simp only [yPt, xPt, Fin.append_right, Fin.cons_zero]
      rw [he]; exact continuous_apply _
    · intro j'
      have he : (fun w : Fin (p + 1) → ℝ => yPt w y (Fin.natAdd p j'.succ))
          = fun _ => y j' := by
        funext w
        simp only [yPt, xPt, Fin.append_right, Fin.cons_succ]
      rw [he]; exact continuous_const

theorem takeLx_yPt (w : Fin (p + 1) → ℝ) (y : Fin n → ℝ) : takeLx (yPt w y) = w := by
  have h1 : (fun i : Fin p => yPt w y (Fin.castAdd (n + 1) i))
      = fun i => w (Fin.castSucc i) := by
    funext i
    simp only [yPt, xPt, Fin.append_left]
  have h2 : yPt w y (Fin.natAdd p 0) = w (Fin.last p) := by
    simp only [yPt, xPt, Fin.append_right, Fin.cons_zero]
  rw [takeLx, h1, h2]
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Fin.snoc_last]
  · intro i'
    rw [Fin.snoc_castSucc]

theorem takeY_yPt (w : Fin (p + 1) → ℝ) (y : Fin n → ℝ) : takeY (yPt w y) = y := by
  funext j
  simp only [takeY, yIdx, yPt, xPt, Fin.append_right, Fin.cons_succ]

theorem yPt_takeLx_takeY (z : Fin (p + (n + 1)) → ℝ) :
    yPt (takeLx z) (takeY z) = z := by
  funext k
  refine Fin.addCases (m := p) (n := n + 1) ?_ ?_ k
  · intro i
    simp only [yPt, xPt, Fin.append_left, Function.comp_apply, takeLx, Fin.snoc_castSucc]
  · intro j
    refine Fin.cases ?_ ?_ j
    · simp only [yPt, xPt, Fin.append_right, Fin.cons_zero, takeLx, Fin.snoc_last]
    · intro j'
      simp only [yPt, xPt, Fin.append_right, Fin.cons_succ, takeY, yIdx]

/-! ## 3. The "empty fibre" set is nowhere dense -/

/-- The points `w = (l,x)` whose whole fibre lies outside the interior of the `C¹` locus. -/
def CaseA (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) : Set (Fin (p + 1) → ℝ) :=
  {w | ∀ y ∈ openCube n,
    yPt w y ∉ interior {z : Fin (p + (n + 1)) → ℝ | ContDiffAt ℝ 1 (famFunHat f) z}}

theorem CaseA_eq_compl_closure_nonC1
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    interior {z : Fin (p + (n + 1)) → ℝ | ContDiffAt ℝ 1 (famFunHat f) z}
      = (closure {z : Fin (p + (n + 1)) → ℝ | ¬ ContDiffAt ℝ 1 (famFunHat f) z})ᶜ := by
  have h : ({z : Fin (p + (n + 1)) → ℝ | ¬ ContDiffAt ℝ 1 (famFunHat f) z})ᶜ
      = {z : Fin (p + (n + 1)) → ℝ | ContDiffAt ℝ 1 (famFunHat f) z} := by
    ext z; simp
  rw [← h, interior_compl]

theorem closure_CaseA_subset (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    closure (CaseA f) ⊆
      {w | ∀ y ∈ openCube n,
        yPt w y ∈ closure {z : Fin (p + (n + 1)) → ℝ | ¬ ContDiffAt ℝ 1 (famFunHat f) z}} := by
  intro w hw y hy
  by_contra hcon
  have hLoc : yPt w y ∈ interior {z : Fin (p + (n + 1)) → ℝ |
      ContDiffAt ℝ 1 (famFunHat f) z} := by
    rw [CaseA_eq_compl_closure_nonC1 f]
    exact hcon
  have hnb : {w' : Fin (p + 1) → ℝ | yPt w' y ∈
      interior {z : Fin (p + (n + 1)) → ℝ | ContDiffAt ℝ 1 (famFunHat f) z}} ∈ 𝓝 w :=
    (continuous_yPt (p := p) y).continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hLoc)
  obtain ⟨w', hw'⟩ := mem_closure_iff_nhds.mp hw _ hnb
  obtain ⟨hw'1, hw'2⟩ := hw'
  exact hw'2 y hy hw'1

theorem CaseA_nowhereDense (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (hD : interior (closure {z : Fin (p + (n + 1)) → ℝ |
      ¬ ContDiffAt ℝ 1 (famFunHat f) z}) = ∅) :
    IsNowhereDense (CaseA f) := by
  rw [IsNowhereDense, ← Set.not_nonempty_iff_eq_empty]
  intro hne
  obtain ⟨w, hw⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior w hw
  set y₀ : Fin n → ℝ := fun _ => (1 / 2 : ℝ) with hy₀def
  have hy₀ : y₀ ∈ openCube n := fun i => by
    simp only [openCube, Set.mem_ofPred_eq, hy₀def]
    norm_num
  set E : Set (Fin (p + (n + 1)) → ℝ) :=
    {z | takeLx z ∈ Metric.ball w ε ∧ takeY z ∈ openCube n} with hEdef
  have hEopen : IsOpen E := by
    have h1 : IsOpen (takeLx ⁻¹' Metric.ball w ε) :=
      Metric.isOpen_ball.preimage (continuous_takeLx (p := p) (n := n))
    have h2 : IsOpen (takeY ⁻¹' openCube n) :=
      (isOpen_openCube n).preimage (continuous_takeY (p := p) (n := n))
    have h3 := h1.inter h2
    rwa [show takeLx ⁻¹' Metric.ball w ε ∩ takeY ⁻¹' openCube n = E from rfl] at h3
  have hz₀ : yPt w y₀ ∈ E := by
    refine ⟨?_, ?_⟩
    · rw [takeLx_yPt]; exact Metric.mem_ball_self hε
    · rw [takeY_yPt]; exact hy₀
  have hEsub : E ⊆ closure {z : Fin (p + (n + 1)) → ℝ |
      ¬ ContDiffAt ℝ 1 (famFunHat f) z} := by
    intro z hz
    have hrel := closure_CaseA_subset f (interior_subset (hball hz.1)) (takeY z) hz.2
    rwa [yPt_takeLx_takeY] at hrel
  have hmem : yPt w y₀ ∈ interior (closure {z : Fin (p + (n + 1)) → ℝ |
      ¬ ContDiffAt ℝ 1 (famFunHat f) z}) := interior_maximal hEsub hEopen hz₀
  rw [hD] at hmem
  exact hmem

/-! ## 4. The main theorem -/

theorem badCurveStrip_interior_empty (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (hchoice : Work.WilkG4c.ChoiceHyp S) (h1 : ∀ q, WilkiesDesign.CG.F1Affine S q)
    {p n F0 D r : ℕ} (hr : 1 ≤ r) {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    (hf : WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1))
    (hval : ∀ l : Fin p → ℝ, ∀ z ∈ WilkiesDesign.openCube (n + 1), f l z ∈ Set.Ioo (0 : ℝ) 1)
    (hY : ∀ l : Fin p → ℝ, ∀ x ∈ Work.WilkG4c.I, ∀ m, m ≤ r → ∀ y ∈ WilkiesDesign.openCube n,
      ‖iteratedFDeriv ℝ m (Work.WilkG4c.slice (f l) x) y‖ ≤ 1) :
    interior {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ Work.WilkG4c.I ∧ w ∈ Work.WilkG4c.badCurve f}
      = ∅ := by
  classical
  obtain ⟨K, hK⟩ := Work.WilG4c.graphOf_member_mem S p n
  -- (1) the `x`-partial is bounded off a finite set of `x`, for each parameter `l`
  have hperl : ∀ l : Fin p → ℝ, ∃ s : Finset ℝ, ∀ x ∈ I, x ∉ s →
      BddAbove ((fun y => |xDeriv f l x y|) ''
        {y : Fin n → ℝ | y ∈ openCube n ∧
          xPt l x y ∈ interior {z : Fin (p + (n + 1)) → ℝ |
            ContDiffAt ℝ 1 (famFunHat f) z}}) := by
    intro l
    obtain ⟨s, hs⟩ := (bddDxHyp_of_choice S hcd hder hchoice) (f l)
      (hK F0 D f l hf) (fun z hz => hval l z hz) (by
        refine ⟨∅, fun x hx _ => ⟨1, fun y hy _ i => ?_⟩⟩
        calc |fderiv ℝ (f l) (Fin.cons x y) (Pi.single i.succ 1)|
            ≤ ‖iteratedFDeriv ℝ 1 (slice (f l) x) y‖ := abs_fderiv_cons_le (f l) x y i
          _ ≤ 1 := hY l x hx 1 hr y hy)
    refine ⟨s, fun x hx hxs => ?_⟩
    obtain ⟨B, hB⟩ := hs x hx hxs
    refine ⟨B, ?_⟩
    rintro b ⟨y, ⟨hyc, hyl⟩, rfl⟩
    change |xDeriv f l x y| ≤ B
    have hlocus : ContDiffAt ℝ 1 (famFunHat f) (xPt l x y) :=
      (mem_interior_contDiffAt_locus 1 (famFunHat f) (xPt l x y)).mp hyl
    rw [Work.WilG4c.pullX_xDeriv_eq_fderiv f l x y (hlocus.differentiableAt (by norm_num))]
    refine hB y hyc ?_
    exact (mem_interior_contDiffAt_locus 1 (f l) (Fin.cons x y)).mpr
      (by simpa [pt] using contDiffAt_famFunHat_xPt f l x y hlocus)
  -- (2) the second exceptional set has empty interior
  let sOf : (Fin p → ℝ) → Finset ℝ := fun l => Classical.choose (hperl l)
  have hsOf : ∀ l, ∀ x ∈ I, x ∉ sOf l → BddAbove ((fun y => |xDeriv f l x y|) ''
      {y : Fin n → ℝ | y ∈ openCube n ∧
        xPt l x y ∈ interior {z : Fin (p + (n + 1)) → ℝ |
          ContDiffAt ℝ 1 (famFunHat f) z}}) := fun l => Classical.choose_spec (hperl l)
  set Sset : Set (Fin (p + 1) → ℝ) :=
    {w | w (Fin.last p) ∈ sOf (fun i => w (Fin.castSucc i))} with hSsetdef
  have hinteriorS : interior Sset = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨w, hw⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior w hw
    set x₀ : ℝ := w (Fin.last p) with hx₀def
    set l₀ : Fin p → ℝ := fun i => w (Fin.castSucc i) with hl₀def
    have hw_eq : (Fin.snoc l₀ x₀ : Fin (p + 1) → ℝ) = w := by
      funext i
      refine Fin.lastCases ?_ ?_ i
      · rw [Fin.snoc_last, hx₀def]
      · intro i'; rw [Fin.snoc_castSucc, hl₀def]
    have hsub : Set.Ioo (x₀ - ε) (x₀ + ε) ⊆ (sOf l₀ : Set ℝ) := by
      intro x hx
      have hmem : (Fin.snoc l₀ x : Fin (p + 1) → ℝ) ∈ Metric.ball w ε := by
        rw [Metric.mem_ball]
        rw [show dist (Fin.snoc l₀ x : Fin (p + 1) → ℝ) w
            = |x - x₀| from by rw [← hw_eq]; exact Work.WilG1.Cell.dist_snoc_last l₀ x x₀]
        rw [abs_lt]
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have hS := interior_subset (hball hmem)
      simp only [hSsetdef, Set.mem_ofPred_eq] at hS
      have hl : (fun i : Fin p => (Fin.snoc l₀ x : Fin (p + 1) → ℝ) (Fin.castSucc i)) = l₀ := by
        funext i; rw [Fin.snoc_castSucc]
      have hlast : (Fin.snoc l₀ x : Fin (p + 1) → ℝ) (Fin.last p) = x := by simp
      rw [hl, hlast] at hS
      exact hS
    have hinf : (Set.Ioo (x₀ - ε) (x₀ + ε)).Infinite := Set.Ioo_infinite (by linarith)
    exact (Set.Infinite.mono hsub hinf) ((sOf l₀).finite_toSet)
  -- (3) the `CaseA` set is nowhere dense
  have hD := interior_closure_nonC1_empty S hcd (famFunHat f) hf
  have hCA : IsNowhereDense (CaseA f) := CaseA_nowhereDense f hD
  -- (4) every bad `(l,x)` with `x ∈ I` lies in `CaseA f ∪ Sset`
  have hTsub : {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ I ∧ w ∈ badCurve f}
      ⊆ CaseA f ∪ Sset := by
    intro w hw
    obtain ⟨hxI, hbad⟩ := hw
    simp only [badCurve, Set.mem_ofPred_eq] at hbad
    by_cases hx : w (Fin.last p) ∈ sOf (fun i => w (Fin.castSucc i))
    · exact Or.inr hx
    · refine Or.inl fun y hy hyl => ?_
      exfalso
      have hbdd := hsOf (fun i => w (Fin.castSucc i)) (w (Fin.last p)) hxI hx
      have hne : ({y : Fin n → ℝ | y ∈ openCube n ∧
          xPt (fun i => w (Fin.castSucc i)) (w (Fin.last p)) y ∈
            interior {z : Fin (p + (n + 1)) → ℝ |
              ContDiffAt ℝ 1 (famFunHat f) z}}).Nonempty := ⟨y, hy, hyl⟩
      obtain ⟨y₀, hy₀, hmax⟩ := Work.WilG4c.exists_nearmax_of_bdd hne
        (fun y => xDeriv f (fun i => w (Fin.castSucc i)) (w (Fin.last p)) y) hbdd
      exact hbad ⟨y₀, hy₀.1, hy₀.2, fun y' hy' hyl' => hmax y' ⟨hy', hyl'⟩⟩
  -- (5) assemble
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨w, hw⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior w hw
  have hB_sub : Metric.ball w ε ⊆ CaseA f ∪ Sset :=
    fun z hz => hTsub (interior_subset (hball hz))
  have hne : (Metric.ball w ε \ closure (CaseA f)).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hcon
    have hsub' : Metric.ball w ε ⊆ interior (closure (CaseA f)) :=
      interior_maximal hcon Metric.isOpen_ball
    rw [show interior (closure (CaseA f)) = ∅ from hCA] at hsub'
    exact hsub' (Metric.mem_ball_self hε)
  obtain ⟨z, hz⟩ := hne
  have hopen : IsOpen (Metric.ball w ε \ closure (CaseA f)) :=
    IsOpen.sdiff Metric.isOpen_ball isClosed_closure
  have hzS : Metric.ball w ε \ closure (CaseA f) ⊆ Sset := by
    intro z' hz'
    rcases hB_sub hz'.1 with h | h
    · exact absurd (subset_closure h) hz'.2
    · exact h
  have hzint : z ∈ interior Sset :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hopen.mem_nhds hz) hzS)
  rw [hinteriorS] at hzint
  exact hzint

end Work.WilG4c
