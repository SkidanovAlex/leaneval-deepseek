import Mathlib
import Submission.Work.WilC4aCS.CurveSelStep
import Submission.Work.WilC4aRW.Main
import Submission.Work.WilC4aAL.Main
import Submission.Work.WilC4aP.Main
import Submission.Work.WilC4aTS.TS

/-!
# `Work.WilE7.Dim.curve_sel_in_cube`

Analytic curve selection inside a basic semianalytic set intersected with the closed cube
`E.cubeC q = {x | ∀ i, |x i| ≤ 1}`.

The available curve selection principle (`CG.C4a.CurveSel`, proved for every dimension in
`Submission/Work/WilC4aCS/CurveSelStep.lean`) applies to the *basic* semianalytic set
`BasicSA F g = {F = 0, ∀ j, g j > 0}`, whose defining inequalities are strict; the cube
conditions `1 - (x i)^2 ≥ 0` are not of this form.

The reduction used here is the standard one: make the cube conditions into *equations* by
adding one slack variable `t i` per coordinate, tied by `1 - (x i)^2 = (t i)^2`.  Thus a point
`x` lies in `cubeC q ∩ BasicSA F g` iff the lift

  `liftPt x = Fin.append x (fun i => √(1 - x i ^ 2))`

lies in the basic semianalytic set `BasicSA (liftEq F) (liftIn g)` in `ℝ ^ (q + q)`, where

  `liftEq F z = F (fstProj q z) ^ 2 + ∑ i, (1 - (fstProj q z) i ^ 2 - (sndProj q z) i ^ 2) ^ 2`

is the "sum of squares" encoding of the (possibly several) equations
`F (fst z) = 0` and `1 - (fst z) i ^ 2 = (snd z) i ^ 2`.  `liftPt` is continuous, so the
hypothesis `y ∈ closure (cubeC q ∩ BasicSA F g)` transfers to
`liftPt y ∈ closure (BasicSA (liftEq F) (liftIn g))`; curve selection in dimension `q + q`
produces an analytic arc `Γ` through `liftPt y` inside the lifted set, and its first projection
`γ = fstProj q ∘ Γ` is the required arc.  The *only* use of the hypothesis is monotonicity of
`closure` along the continuous map `liftPt`, plus the exact identity
`fstProj '' BasicSA (liftEq F) (liftIn g) = cubeC q ∩ BasicSA F g`.
-/

set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped Topology

namespace Work.WilE7.Dim

/-! ## 1. Splitting `ℝ ^ (q + q)` into two blocks of size `q` -/

/-- The projection `ℝ ^ (q + q) → ℝ ^ q` onto the first block. -/
def fstProj (q : ℕ) : (Fin (q + q) → ℝ) →L[ℝ] (Fin q → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (Fin.castAdd q i))

/-- The projection `ℝ ^ (q + q) → ℝ ^ q` onto the second block. -/
def sndProj (q : ℕ) : (Fin (q + q) → ℝ) →L[ℝ] (Fin q → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (Fin.natAdd q i))

lemma fstProj_apply (q : ℕ) (z : Fin (q + q) → ℝ) (i : Fin q) :
    fstProj q z i = z (Fin.castAdd q i) := by simp [fstProj]

lemma sndProj_apply (q : ℕ) (z : Fin (q + q) → ℝ) (i : Fin q) :
    sndProj q z i = z (Fin.natAdd q i) := by simp [sndProj]

lemma fstProj_append (q : ℕ) (x t : Fin q → ℝ) : fstProj q (Fin.append x t) = x := by
  funext i; rw [fstProj_apply]; simp

lemma sndProj_append (q : ℕ) (x t : Fin q → ℝ) : sndProj q (Fin.append x t) = t := by
  funext i; rw [sndProj_apply, Fin.append_right]

/-! ## 2. The lifted basic semianalytic set -/

/-- The lifted equation: `F (fst z) = 0` and `1 - (fst z) i ^ 2 = (snd z) i ^ 2` for all `i`,
encoded as a single sum of squares (which vanishes exactly when all the equations do). -/
def liftEq {q : ℕ} (F : (Fin q → ℝ) → ℝ) : (Fin (q + q) → ℝ) → ℝ :=
  fun z => F (fstProj q z) ^ 2 + ∑ i : Fin q, (1 - fstProj q z i ^ 2 - sndProj q z i ^ 2) ^ 2

/-- The lifted inequalities: `g j (fst z) > 0`. -/
def liftIn {q l : ℕ} (g : Fin l → (Fin q → ℝ) → ℝ) : Fin l → (Fin (q + q) → ℝ) → ℝ :=
  fun j z => g j (fstProj q z)

/-- The canonical lift of a point of `ℝ ^ q`: the slack variable for the `i`-th cube condition
is `√(1 - x i ^ 2)`, so that `1 - x i ^ 2 = (slack i) ^ 2`. -/
def liftPt {q : ℕ} (y : Fin q → ℝ) : Fin (q + q) → ℝ :=
  Fin.append y (fun i => Real.sqrt (1 - y i ^ 2))

lemma fstProj_liftPt {q : ℕ} (y : Fin q → ℝ) : fstProj q (liftPt y) = y := by
  rw [liftPt, fstProj_append]

/-- A point of `cubeC q ∩ BasicSA F g` lifts to the lifted basic semianalytic set. -/
lemma lift_liftPt_mem {q l : ℕ} (F : (Fin q → ℝ) → ℝ) (g : Fin l → (Fin q → ℝ) → ℝ)
    {x : Fin q → ℝ} (hx : x ∈ WilkiesDesign.E.cubeC q ∩ WilkiesDesign.CG.C4a.BasicSA F g) :
    liftPt x ∈ WilkiesDesign.CG.C4a.BasicSA (liftEq F) (liftIn g) := by
  obtain ⟨hcube, hF0, hgj⟩ := hx
  have hsqrt : ∀ i : Fin q, Real.sqrt (1 - x i ^ 2) ^ 2 = 1 - x i ^ 2 := by
    intro i
    have hx2 : x i ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one (x i)).mpr (hcube i)
    exact Real.sq_sqrt (by linarith)
  have hterm : ∀ i : Fin q, (1 - x i ^ 2 - sndProj q (liftPt x) i ^ 2) = 0 := by
    intro i
    rw [liftPt, sndProj_append, hsqrt i]
    ring
  refine ⟨?_, ?_⟩
  · rw [liftEq, fstProj_liftPt, hF0]
    rw [Finset.sum_eq_zero (fun i _ => by rw [hterm i]; ring)]
    ring
  · intro j
    simpa [liftIn, fstProj_liftPt] using hgj j

/-! ## 3. The projection of the lifted set is the cube-intersected set -/

/-- **The key identity.**  Projecting the lifted basic semianalytic set onto the first block
returns exactly `cubeC q ∩ BasicSA F g`. -/
lemma image_fstProj_liftSA {q l : ℕ} (F : (Fin q → ℝ) → ℝ)
    (g : Fin l → (Fin q → ℝ) → ℝ) :
    fstProj q '' WilkiesDesign.CG.C4a.BasicSA (liftEq F) (liftIn g)
      = WilkiesDesign.E.cubeC q ∩ WilkiesDesign.CG.C4a.BasicSA F g := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hΦ, hG⟩ := hz
    -- `F (fst z) = 0` from the sum of squares
    have hF0 : F (fstProj q z) = 0 := by
      have h1 : F (fstProj q z) ^ 2 ≤ liftEq F z := by
        rw [liftEq]
        exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => sq_nonneg _))
      rw [hΦ] at h1
      exact sq_eq_zero_iff.mp (le_antisymm h1 (sq_nonneg _))
    -- `|(fst z) i| ≤ 1` from the sum of squares
    have hcube : ∀ i : Fin q, |fstProj q z i| ≤ 1 := by
      intro i
      have h1 : (1 - fstProj q z i ^ 2 - sndProj q z i ^ 2) ^ 2 ≤ liftEq F z := by
        rw [liftEq]
        have h2 : (1 - fstProj q z i ^ 2 - sndProj q z i ^ 2) ^ 2 ≤
            ∑ j : Fin q, (1 - fstProj q z j ^ 2 - sndProj q z j ^ 2) ^ 2 :=
          Finset.single_le_sum
            (f := fun j => (1 - fstProj q z j ^ 2 - sndProj q z j ^ 2) ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        linarith [h2, sq_nonneg (F (fstProj q z))]
      rw [hΦ] at h1
      have hz0 : (1 - fstProj q z i ^ 2 - sndProj q z i ^ 2) ^ 2 = 0 :=
        le_antisymm h1 (sq_nonneg _)
      have heq : 1 - fstProj q z i ^ 2 = sndProj q z i ^ 2 := by
        have := sq_eq_zero_iff.mp hz0
        linarith
      have hx2 : fstProj q z i ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg (sndProj q z i)]
      exact (sq_le_one_iff_abs_le_one _).mp hx2
    exact ⟨hcube, hF0, fun j => by simpa [liftIn] using hG j⟩
  · intro hx
    exact ⟨liftPt x, lift_liftPt_mem F g hx, fstProj_liftPt x⟩

/-! ## 4. Transfer of the closure hypothesis along the continuous lift -/

/-- The lift `liftPt` is continuous (each coordinate is either a coordinate of `x` or a square
root of a continuous function of one coordinate). -/
lemma continuous_liftPt {q : ℕ} : Continuous (liftPt : (Fin q → ℝ) → (Fin (q + q) → ℝ)) := by
  refine continuous_pi (fun k => ?_)
  induction k using Fin.addCases with
  | left i =>
      simpa [liftPt] using (continuous_apply i : Continuous (fun x : Fin q → ℝ => x i))
  | right i =>
      rw [show (fun a : Fin q → ℝ => liftPt a (Fin.natAdd q i)) =
          (fun a : Fin q → ℝ => Real.sqrt (1 - a i ^ 2)) by
        funext a; rw [liftPt, Fin.append_right]]
      exact (continuous_const.sub
        ((continuous_apply i : Continuous (fun x : Fin q → ℝ => x i)).pow 2)).sqrt

/-- The closure hypothesis transfers to the lifted set. -/
lemma closure_liftPt {q l : ℕ} (F : (Fin q → ℝ) → ℝ) (g : Fin l → (Fin q → ℝ) → ℝ)
    (y : Fin q → ℝ)
    (hcl : y ∈ closure (WilkiesDesign.E.cubeC q ∩ WilkiesDesign.CG.C4a.BasicSA F g)) :
    liftPt y ∈ closure (WilkiesDesign.CG.C4a.BasicSA (liftEq F) (liftIn g)) := by
  have hsub : (liftPt : (Fin q → ℝ) → (Fin (q + q) → ℝ)) ''
      (WilkiesDesign.E.cubeC q ∩ WilkiesDesign.CG.C4a.BasicSA F g) ⊆
      WilkiesDesign.CG.C4a.BasicSA (liftEq F) (liftIn g) := by
    rintro _ ⟨x, hx, rfl⟩
    exact lift_liftPt_mem F g hx
  exact closure_mono hsub (continuous_liftPt.continuousOn.image_closure ⟨y, hcl, rfl⟩)

/-! ## 5. Curve selection inside the cube -/

theorem curve_sel_in_cube {q l : ℕ} (F : (Fin q → ℝ) → ℝ) (g : Fin l → (Fin q → ℝ) → ℝ)
    (y : Fin q → ℝ) (hF : AnalyticAt ℝ F y) (hg : ∀ j, AnalyticAt ℝ (g j) y)
    (hcl : y ∈ closure (WilkiesDesign.E.cubeC q ∩ WilkiesDesign.CG.C4a.BasicSA F g)) :
    ∃ γ : ℝ → (Fin q → ℝ), AnalyticAt ℝ γ 0 ∧ γ 0 = y ∧
      ∃ ε > (0 : ℝ), ∀ s ∈ Set.Ioo (0 : ℝ) ε,
        γ s ∈ WilkiesDesign.E.cubeC q ∩ WilkiesDesign.CG.C4a.BasicSA F g := by
  -- curve selection in every dimension (area C4a, proved from the three sub-holes)
  have hCS := Work.WilC4aCS.curveSel_all WilkiesDesign.CG.C4a.C4a_RW_proved
    (Work.WilC4aAL.C4a_arcLift_proved WilkiesDesign.CG.C4a.C4a_puiseux_proved)
    Work.WilC4aTS.C4a_TS1_proved
  have hfst : fstProj q (liftPt y) = y := fstProj_liftPt y
  -- analyticity of the lifted data at the lifted point
  have hΦan : AnalyticAt ℝ (liftEq F) (liftPt y) := by
    change AnalyticAt ℝ (fun z : Fin (q + q) → ℝ =>
      F (fstProj q z) ^ 2 + ∑ i : Fin q, (1 - fstProj q z i ^ 2 - sndProj q z i ^ 2) ^ 2)
      (liftPt y)
    have h1 : AnalyticAt ℝ (fun z : Fin (q + q) → ℝ => F (fstProj q z)) (liftPt y) := by
      have hF' : AnalyticAt ℝ F (fstProj q (liftPt y)) := by rw [hfst]; exact hF
      exact hF'.comp ((fstProj q).analyticAt (liftPt y))
    have h2 : AnalyticAt ℝ (fun z : Fin (q + q) → ℝ =>
        ∑ i : Fin q, (1 - fstProj q z i ^ 2 - sndProj q z i ^ 2) ^ 2) (liftPt y) := by
      have hterm : ∀ i : Fin q, AnalyticAt ℝ (fun z : Fin (q + q) → ℝ =>
          (1 - fstProj q z i ^ 2 - sndProj q z i ^ 2) ^ 2) (liftPt y) := by
        intro i
        have ha : AnalyticAt ℝ (fun z : Fin (q + q) → ℝ => fstProj q z i) (liftPt y) :=
          ((ContinuousLinearMap.proj i).comp (fstProj q)).analyticAt (liftPt y)
        have hb : AnalyticAt ℝ (fun z : Fin (q + q) → ℝ => sndProj q z i) (liftPt y) :=
          ((ContinuousLinearMap.proj i).comp (sndProj q)).analyticAt (liftPt y)
        have h1 : AnalyticAt ℝ (fun z : Fin (q + q) → ℝ => 1 - fstProj q z i ^ 2)
            (liftPt y) :=
          (analyticAt_const (v := (1 : ℝ)) (x := liftPt y)).sub (ha.pow 2)
        have h2 : AnalyticAt ℝ (fun z : Fin (q + q) → ℝ =>
            1 - fstProj q z i ^ 2 - sndProj q z i ^ 2) (liftPt y) := h1.sub (hb.pow 2)
        exact h2.pow 2
      rw [show (fun z : Fin (q + q) → ℝ => ∑ i : Fin q,
            (1 - fstProj q z i ^ 2 - sndProj q z i ^ 2) ^ 2)
          = ∑ i : Fin q, (fun z : Fin (q + q) → ℝ =>
            (1 - fstProj q z i ^ 2 - sndProj q z i ^ 2) ^ 2) by
        funext z; rw [Finset.sum_apply]]
      exact Finset.analyticAt_sum (Finset.univ : Finset (Fin q))
        (f := fun i (z : Fin (q + q) → ℝ) =>
          (1 - fstProj q z i ^ 2 - sndProj q z i ^ 2) ^ 2)
        (fun i _ => hterm i)
    exact (h1.pow 2).add h2
  have hGan : ∀ j, AnalyticAt ℝ (liftIn g j) (liftPt y) := by
    intro j
    have hgj : AnalyticAt ℝ (g j) (fstProj q (liftPt y)) := by rw [hfst]; exact hg j
    exact hgj.comp ((fstProj q).analyticAt (liftPt y))
  -- curve selection in the lifted space
  obtain ⟨Γ, hΓan, hΓ0, ε, hε, hΓmem⟩ :=
    hCS (q + q) l (liftEq F) (liftIn g) (liftPt y) hΦan hGan (closure_liftPt F g y hcl)
  refine ⟨fun s : ℝ => fstProj q (Γ s), ?_, ?_, ε, hε, ?_⟩
  · have h := ((fstProj q).analyticAt (Γ 0)).comp hΓan
    simpa [Function.comp_def] using h
  · show fstProj q (Γ 0) = y
    rw [hΓ0, hfst]
  · intro s hs
    have hmem : fstProj q (Γ s) ∈
        fstProj q '' WilkiesDesign.CG.C4a.BasicSA (liftEq F) (liftIn g) :=
      ⟨Γ s, hΓmem s hs, rfl⟩
    rwa [image_fstProj_liftSA] at hmem

end Work.WilE7.Dim
