/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.ProducerH.H2.PsiBlock` — the first block of the closed-box `C²` argument

`E g` (for `g` of the source class `C` and `E` carrying `Ctx`) is continuous on the closed box
`cbox a b = [a,b] × [0,π/2]`, its radial slices have the within-derivative `∂_z(E g)`, and its
angular slices have the within-derivative `Bf L0 L1 (E g)` (the interior `θ`-derivative with
the one-sided endpoint limits `L0`, `L1` supplied by `LimitsAt`).

The three ingredients are:

* `psiDz_rate` (`BoxAux.th2EgRate`) gives the uniform angular rate
  `|E g z θ| ≤ C · Xn₆(g) · min θ (π/2-θ)` on the box, which dominates the two boundary lines
  `θ = 0`, `θ = π/2` *uniformly in `z`* — this is continuity on the closed box
  (`continuousOn_cbox_of_min_rate` below);
* `EllClassOk` supplies `SmoothOpen (E g)` (open-quadrant `C^∞`) and the Dirichlet values
  `E g z 0 = E g z (π/2) = 0` (`IsBslSol`), which give the radial within-derivatives
  (`SmoothOpen.hasDerivAt_slice`, resp. the identically vanishing boundary slices);
* `sliceContinuousOn` (`H2.Slice`) plus the one-sided limits of `∂_θ(E g)` from `LimitsAt`
  give the angular within-derivatives at the two endpoints (`hasDerivWithinAt_Icc_left/right`).

Note: the scope `Real` must be opened at the top of the file, otherwise the `π` of the
statement is not the notation for `Real.pi` (and, with `autoImplicit = false`, the statement
does not even elaborate).  The statement of `PsiBlock` itself is verbatim the one requested.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Clause1Aux
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.BoxC2
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgRate
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.Trace
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Slice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.H2

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **Continuity of `F` on the closed box from an angular `min θ (π/2-θ)`-rate.**

`F` is continuous on the open quadrant (this is the hypothesis `hint`, at the interior points),
vanishes on the two boundary lines `θ = 0` and `θ = π/2` (hypotheses `h0`, `hpi`) and is
dominated by `C · min θ (π/2-θ)` on the open strip (`hbound`).  The rate controls the two
boundary lines *uniformly in `z`*, which is exactly what is needed for continuity there; the
interior is open. -/
theorem continuousOn_cbox_of_min_rate {F : ℝ → ℝ → ℝ} {a b C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |F z θ| ≤ C * min θ (π / 2 - θ))
    (hint : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (π / 2),
      ContinuousWithinAt (Function.uncurry F) (Work.FTS_EllLimOK.cbox a b) (z, θ))
    (h0 : ∀ z, F z 0 = 0) (hpi : ∀ z, F z (π / 2) = 0) :
    ContinuousOn (Function.uncurry F) (Work.FTS_EllLimOK.cbox a b) := by
  -- the numerical facts used at both boundary lines
  have hquot : C / (C + 1) < 1 := by
    rw [div_lt_one (by linarith : (0 : ℝ) < C + 1)]
    linarith
  have hfinal : ∀ ε : ℝ, 0 < ε → C * (ε / (C + 1)) < ε := by
    intro ε hε
    have h1 : C * (ε / (C + 1)) = ε * (C / (C + 1)) := by ring
    rw [h1]
    calc ε * (C / (C + 1)) < ε * 1 := mul_lt_mul_of_pos_left hquot hε
      _ = ε := mul_one ε
  intro p hp
  obtain ⟨z, θ⟩ := p
  rw [Work.FTS_EllLimOK.mem_cbox] at hp
  obtain ⟨hz, hθ⟩ := hp
  rcases eq_or_lt_of_le hθ.1 with hθ0 | hθ0
  · -- ## the lower boundary line `θ = 0`
    subst hθ0
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    refine ⟨ε / (C + 1), by positivity, fun q hq hdist => ?_⟩
    obtain ⟨z', θ'⟩ := q
    rw [Work.FTS_EllLimOK.mem_cbox] at hq
    obtain ⟨hz', hθ'⟩ := hq
    have hdd : dist (z', θ') (z, 0) = max |z' - z| |θ' - 0| := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    have hthlt : |θ' - 0| < ε / (C + 1) := by
      rw [hdd] at hdist
      exact lt_of_le_of_lt (le_max_right _ _) hdist
    simp only [Function.uncurry_apply_pair]
    rw [Real.dist_eq]
    rcases eq_or_lt_of_le hθ'.1 with h1 | h1
    · subst h1
      simpa only [h0, sub_zero, abs_zero] using hε
    rcases eq_or_lt_of_le hθ'.2 with h2 | h2
    · subst h2
      simpa only [h0, hpi, sub_zero, abs_zero] using hε
    have hb := hbound z' hz' θ' ⟨h1, h2⟩
    have hstep : |F z' θ'| ≤ C * θ' :=
      le_trans hb (mul_le_mul_of_nonneg_left (min_le_left _ _) hC)
    have hθ'lt : θ' < ε / (C + 1) := by
      rw [sub_zero, abs_of_pos h1] at hthlt
      exact hthlt
    have hCθ : C * θ' < ε := by
      have hmul : C * θ' ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hθ'lt.le hC
      linarith [hmul, hfinal ε hε]
    rw [h0, sub_zero]
    exact lt_of_le_of_lt hstep hCθ
  · rcases eq_or_lt_of_le hθ.2 with hθp | hθp
    · -- ## the upper boundary line `θ = π/2`
      subst hθp
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      refine ⟨ε / (C + 1), by positivity, fun q hq hdist => ?_⟩
      obtain ⟨z', θ'⟩ := q
      rw [Work.FTS_EllLimOK.mem_cbox] at hq
      obtain ⟨hz', hθ'⟩ := hq
      have hdd : dist (z', θ') (z, π / 2) = max |z' - z| |θ' - π / 2| := by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      have hthlt : |θ' - π / 2| < ε / (C + 1) := by
        rw [hdd] at hdist
        exact lt_of_le_of_lt (le_max_right _ _) hdist
      simp only [Function.uncurry_apply_pair]
      rw [Real.dist_eq]
      rcases eq_or_lt_of_le hθ'.1 with h1 | h1
      · subst h1
        simpa only [hpi, h0, sub_zero, abs_zero] using hε
      rcases eq_or_lt_of_le hθ'.2 with h2 | h2
      · subst h2
        simpa only [hpi, sub_zero, abs_zero] using hε
      have hb := hbound z' hz' θ' ⟨h1, h2⟩
      have hstep : |F z' θ'| ≤ C * (π / 2 - θ') :=
        le_trans hb (mul_le_mul_of_nonneg_left (min_le_right _ _) hC)
      have hnear : π / 2 - θ' ≤ |θ' - π / 2| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      have hCθ : C * (π / 2 - θ') < ε := by
        have hmul : C * (π / 2 - θ') ≤ C * |θ' - π / 2| :=
          mul_le_mul_of_nonneg_left hnear hC
        have habs : C * |θ' - π / 2| ≤ C * (ε / (C + 1)) :=
          mul_le_mul_of_nonneg_left hthlt.le hC
        linarith [hmul, habs, hfinal ε hε]
      rw [hpi, sub_zero]
      exact lt_of_le_of_lt hstep hCθ
    · -- ## an interior point: `F` is continuous there on the open quadrant
      exact hint z hz θ ⟨hθ0, hθp⟩

theorem PsiBlock {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : Work.FTS_EllLimOK.ProducerH.H2.Ctx α Ce E) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hdata : Work.FTS_EllLimOK.ProducerH.H2.BoxData α Ce E a b)
    (g : Work.FTS.Galerkin.Fn) (hg : Work.FTS.ClassC.ClassC α g)
    {C : ℝ} {L0 N0 L1 N1 : ℝ → ℝ}
    (hLim : Work.FTS_EllLimOK.ProducerH.H2.LimitsAt (E g) (Work.FTS.StrongGlobal.Xn6 α g) C a b
      L0 N0 L1 N1) :
    ContinuousOn (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b) ∧
    (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun z' => (E g) z' θ) (Work.Spaces.pz (E g) z θ) (Set.Icc a b) z) ∧
    (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun θ' => (E g) z θ')
        (Work.FTS_EllLimOK.ProducerH.H2.Bf L0 L1 (E g) z θ) (Set.Icc 0 (π / 2)) θ) := by
  -- ## the class data
  obtain ⟨hO, -, -⟩ := hE g hg
  have hSsm : Work.FTS.EllipticEst.SmoothOpen (E g) := hO.2.1
  have hsol : Work.Elliptic.IsBslSol α g (E g) := hO.1
  have h0v : ∀ z, (E g) z 0 = 0 := hsol.2.1
  have hpiv : ∀ z, (E g) z (π / 2) = 0 := hsol.2.2.1
  -- ## the frozen endpoint limits
  obtain ⟨hT0, _, _, _, hT1, _, _, _, _, _, _, _, _, _⟩ := hLim
  -- ## the angular rate of `E g` (the `j = 0` instance of the pointwise radial bounds)
  obtain ⟨Cp, hCppos, hCp⟩ :=
    Work.FTS_EllLimOK.ProducerH.BoxAux.psiDz_rate hα hα4 hE ha hab.le
  have hrate : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |(E g) z θ| ≤ (Cp * Work.FTS.StrongGlobal.Xn6 α g) * min θ (π / 2 - θ) := by
    intro z hz θ hθ
    have h := hCp g hg 0 (by norm_num) z hz θ hθ
    simpa using h
  refine ⟨?_, ?_, ?_⟩
  · -- ## (1) continuity on the box
    refine continuousOn_cbox_of_min_rate
      (mul_nonneg hCppos.le (Xn6_nonneg α g)) hrate ?_ h0v hpiv
    intro z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz0, hθ.1, hθ.2⟩
    exact ((hSsm.continuousOn.continuousWithinAt hmem).continuousAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).continuousWithinAt
  · -- ## (2) the `z`-within-derivative of the radial slice
    intro z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    rcases eq_or_lt_of_le hθ.1 with h | h
    · subst h
      have hzid : (fun z' => (E g) z' 0) = fun _ => (0 : ℝ) := funext h0v
      have hpz : Work.Spaces.pz (E g) z 0 = 0 := by
        simp only [Work.Spaces.pz]
        rw [hzid]
        simp
      rw [hzid, hpz]
      exact hasDerivWithinAt_const z (Set.Icc a b) (0 : ℝ)
    rcases eq_or_lt_of_le hθ.2 with hp | hp
    · subst hp
      have hzid : (fun z' => (E g) z' (π / 2)) = fun _ => (0 : ℝ) := funext hpiv
      have hpz : Work.Spaces.pz (E g) z (π / 2) = 0 := by
        simp only [Work.Spaces.pz]
        rw [hzid]
        simp
      rw [hzid, hpz]
      exact hasDerivWithinAt_const z (Set.Icc a b) (0 : ℝ)
    · exact (hSsm.hasDerivAt_slice ⟨h, hp⟩ hz0).hasDerivWithinAt
  · -- ## (3) the `θ`-within-derivative of the angular slice
    intro z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hcont : ContinuousOn (fun θ' => (E g) z θ') (Set.Icc 0 (π / 2)) :=
      sliceContinuousOn hα hα4 hE hg hz0
    have hslice : ContDiffOn ℝ 2 (fun θ' => (E g) z θ') (Set.Ioo 0 (π / 2)) :=
      (hSsm.curry_θ hz0).of_le (by norm_num)
    have hdiff : ∀ x ∈ Set.Ioo (0 : ℝ) (π / 2),
        HasDerivAt (fun θ' => (E g) z θ') (Work.Spaces.pth (E g) z x) x := by
      intro x hx
      exact ((hslice.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt
    rcases eq_or_lt_of_le hθ.1 with h | h
    · subst h
      rw [Bf_zero]
      exact hasDerivWithinAt_Icc_left (f := fun θ' => (E g) z θ')
        (f' := fun x => Work.Spaces.pth (E g) z x) (T := π / 2) (L := L0 z)
        (by positivity) hcont hdiff (hT0 z hz)
    rcases eq_or_lt_of_le hθ.2 with hp | hp
    · subst hp
      rw [Bf_pi]
      exact hasDerivWithinAt_Icc_right (f := fun θ' => (E g) z θ')
        (f' := fun x => Work.Spaces.pth (E g) z x) (T := π / 2) (L := L1 z)
        (by positivity) hcont hdiff (hT1 z hz)
    · rw [Bf_of_mem_Ioo ⟨h, hp⟩]
      exact (((hslice.contDiffAt (isOpen_Ioo.mem_nhds ⟨h, hp⟩)).differentiableAt
        (by norm_num)).hasDerivAt).hasDerivWithinAt

end Work.FTS_EllLimOK.ProducerH.H2
