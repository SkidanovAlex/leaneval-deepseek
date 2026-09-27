import Mathlib
import Submission.Work.Drive.chartPertData
import Submission.Work.Drive.projRotSmooth

/-!
# Smoothness of the chart coordinates of the class perturbation `1 + L (t)`

The perturbation of the projective class used by the chart-perturbation family is the projectivised
quaternionic left multiplication `[v] ↦ [(1 + L (t)) v]` (`Work.Drive.classMap`,
`Work.Drive.classEquiv`).  Read in the `i`-th affine chart of `ℝP³` it becomes the rational map

> `(t, x) ↦ projCoordFun i (classEquiv t (projSection i x))`,

i.e. the chart-coordinate map `Work.Drive.chartProjMap (classEquiv t) i` of the *family* of linear
automorphisms `classEquiv t`.  This file proves that this map is `C^∞` at every point where its
denominator — the `i`-th coordinate of `classEquiv t (projSection i x)` — does not vanish.  This is
the parametric version of `Work.Drive.differentiableAt_chartProjMap`, and the smoothness input of
the transport of the engine's conditions along the perturbation family.

The proof is the chain rule.  The facts used are

* the section `x ↦ projSection i x` is `C^∞` (`Work.Drive.contDiff_projSection`),
* `(t, v) ↦ classGen t v` is `C^∞` (it is bilinear: `classGen t v = (t 1) • genI v + (t 2) •
  genJ v + (t 3) • genK v`), proved here as `Work.Drive.contDiff_classGen_pair`,
* the chart coordinates `projCoordFun i` are `C^∞` where their denominator does not vanish
  (`Work.Drive.contDiffAt_projCoordFun`).
-/

namespace Work.Drive

open scoped ContDiff

noncomputable section

set_option maxHeartbeats 4000000

/-! ## The class generator is smooth in the pair `(t, v)` -/

/-- **The class generator `(t, v) ↦ classGen t v` is `C^∞`.**  It is the bilinear map
`(t, v) ↦ (t 1) • genI v + (t 2) • genJ v + (t 3) • genK v`. -/
lemma contDiff_classGen_pair :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Eucl 3 × Eucl 3 => classGen p.1 p.2) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Eucl 3 × Eucl 3 => p.1.ofLp (1 : Fin 4)) :=
    (contDiff_piLp_apply (p := 2) (E := fun _ : Fin 4 => ℝ) (i := (1 : Fin 4))).comp
      (contDiff_fst (𝕜 := ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Eucl 3 × Eucl 3 => p.1.ofLp (2 : Fin 4)) :=
    (contDiff_piLp_apply (p := 2) (E := fun _ : Fin 4 => ℝ) (i := (2 : Fin 4))).comp
      (contDiff_fst (𝕜 := ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Eucl 3 × Eucl 3 => p.1.ofLp (3 : Fin 4)) :=
    (contDiff_piLp_apply (p := 2) (E := fun _ : Fin 4 => ℝ) (i := (3 : Fin 4))).comp
      (contDiff_fst (𝕜 := ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  have hgI : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Eucl 3 × Eucl 3 => genI p.2) :=
    genI.contDiff.comp (contDiff_snd (𝕜 := ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  have hgJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Eucl 3 × Eucl 3 => genJ p.2) :=
    genJ.contDiff.comp (contDiff_snd (𝕜 := ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  have hgK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Eucl 3 × Eucl 3 => genK p.2) :=
    genK.contDiff.comp (contDiff_snd (𝕜 := ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  have hgoal : (fun p : Eucl 3 × Eucl 3 => classGen p.1 p.2)
      = (fun p : Eucl 3 × Eucl 3 => p.1.ofLp (1 : Fin 4) • genI p.2)
        + (fun p : Eucl 3 × Eucl 3 => p.1.ofLp (2 : Fin 4) • genJ p.2)
        + (fun p : Eucl 3 × Eucl 3 => p.1.ofLp (3 : Fin 4) • genK p.2) := by
    funext p
    exact classGen_apply p.1 p.2
  rw [hgoal]
  exact ((h1.smul hgI).add (h2.smul hgJ)).add (h3.smul hgK)

/-! ## The family `(t, x) ↦ classEquiv t (projSection i x)` is smooth -/

/-- **The class perturbation reading the `i`-th chart section is `C^∞` jointly in the parameter `t`
and the chart coordinates `x`.**  This is `v ↦ (1 + L (t)) v` at `v = projSection i x`, i.e.
`(t, x) ↦ projSection i x + classGen t (projSection i x)`. -/
lemma contDiff_classEquiv_projSection (i : Fin 4) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : Eucl 3 × EuclideanSpace ℝ (Fin 3) =>
        classEquiv u.1 (projSection (n := 3) i u.2)) := by
  have hsec : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : Eucl 3 × EuclideanSpace ℝ (Fin 3) => projSection (n := 3) i u.2) :=
    ContDiff.fun_comp (g := projSection (n := 3) i)
      (f := fun u : Eucl 3 × EuclideanSpace ℝ (Fin 3) => u.2)
      (contDiff_projSection 3 i) (contDiff_snd (𝕜 := ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  have hpair : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : Eucl 3 × EuclideanSpace ℝ (Fin 3) =>
        (u.1, projSection (n := 3) i u.2)) :=
    (contDiff_fst (𝕜 := ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).prodMk hsec
  have hgen : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : Eucl 3 × EuclideanSpace ℝ (Fin 3) =>
        classGen u.1 (projSection (n := 3) i u.2)) :=
    ContDiff.fun_comp (g := fun p : Eucl 3 × Eucl 3 => classGen p.1 p.2)
      (f := fun u : Eucl 3 × EuclideanSpace ℝ (Fin 3) =>
        (u.1, projSection (n := 3) i u.2))
      contDiff_classGen_pair hpair
  have hgoal : (fun u : Eucl 3 × EuclideanSpace ℝ (Fin 3) =>
        classEquiv u.1 (projSection (n := 3) i u.2))
      = fun u : Eucl 3 × EuclideanSpace ℝ (Fin 3) =>
        projSection (n := 3) i u.2 + classGen u.1 (projSection (n := 3) i u.2) := by
    funext u
    exact classEquiv_apply u.1 (projSection (n := 3) i u.2)
  rw [hgoal]
  exact hsec.add hgen

/-! ## The theorem -/

/-- **The chart coordinates of the class perturbation are `C^∞` where the denominator does not
vanish.**  For `(t₀, x₀)` with `(classEquiv t₀ (projSection i x₀)).ofLp i ≠ 0`, the map
`(t, x) ↦ projCoordFun i (classEquiv t (projSection i x))` is `C^∞` at `(t₀, x₀)`. -/
theorem contDiffAt_projCoordFun_classEquiv (i : Fin 4) (t₀ : Work.Drive.Eucl 3)
    (x₀ : EuclideanSpace ℝ (Fin 3))
    (hj : (Work.Drive.classEquiv t₀ (projSection (n := 3) i x₀)).ofLp i ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : Work.Drive.Eucl 3 × EuclideanSpace ℝ (Fin 3) =>
        projCoordFun i (Work.Drive.classEquiv u.1 (projSection (n := 3) i u.2))) (t₀, x₀) := by
  have hpt : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (projCoordFun (n := 3) i)
      (classEquiv t₀ (projSection (n := 3) i x₀)) :=
    contDiffAt_projCoordFun 3 i (classEquiv t₀ (projSection (n := 3) i x₀)) hj
  have hfam : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : Eucl 3 × EuclideanSpace ℝ (Fin 3) =>
        classEquiv u.1 (projSection (n := 3) i u.2)) (t₀, x₀) :=
    (contDiff_classEquiv_projSection i).contDiffAt
  exact ContDiffAt.fun_comp (x := (t₀, x₀)) (g := projCoordFun (n := 3) i)
    (f := fun u : Eucl 3 × EuclideanSpace ℝ (Fin 3) =>
      classEquiv u.1 (projSection (n := 3) i u.2)) hpt hfam

end

end Work.Drive
