import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.planeChain
import Submission.Work.Drive.linearPlaneChart
import Submission.Work.Drive.chartShiftHsurj
import Submission.Work.Drive.mk2CLM
import Submission.Work.Drive.contMDiffAt_halfLineProjective_iff
import Submission.Work.Drive.SeamSweep
import Submission.Work.Drive.diskHomotopyChain
import Submission.Work.Drive.classTripleAssemblyLiftFree

/-!
# The *clause homotopy* of the reference-triple route (`NOTES_LEAD_hloc_htube_hsurj.md` §3.2(iv))

`Work.Drive.HasClassLinearization P` asks for a homotopy of each of the three class maps of the
design's plane triple from `planeClassMap (P k)` to the disk model of a *linear* plane.  For the
reference-triple route the triple is `P' k = Ξ (blk k t) ∘ refTriple k` — the **chart-perturbed**
reference planes — so the homotopy of clause `k` has to pass through three stages:

1. `s ≤ 1/3`: the *chart perturbation* is undone, `cls (Ξ (ρ (1-3s) • blk k t) (refTriple k y))`;
2. `1/3 ≤ s ≤ 2/3`: the (B)-lane homotopy `H0 k` from the **unperturbed** plane `refTriple k` to the
   linear disk model;
3. `s ≥ 2/3`: the linear disk model itself.

The three stages glue `C^∞` because each is *locally constant* near the two joins: the cutoff `ρ`
vanishes on `(-∞, 1/10]` and equals `1` on `[9/10, ∞)`, so near `s = 1/3` both the first and the
second stage are `cls (refTriple k y)` and near `s = 2/3` both the second and the third are
`cls (diskPlane (linPlaneChart (φ k) c hc) y)`.

This file defines the family and proves its four defining properties: the two endpoints, the seam
invariance, and the `C^∞`-smoothness of the chain.  The endpoint and seam facts are exactly the
`HasClassLinearization` clauses; the smoothness is the `Meet3Hyp.smooth` field of the encoded chains.

**Note on the interface.**  The (B)-lane homotopies `H0 k` are given only through their *chain*
smoothness `ContMDiff (𝓡 3) (𝓡 3) (fun x => H0 k (x 2, mk2 (x 0) (x 1)))` (this is the shape in which
`Work.Drive.exists_homotopyClauses_rotPresentation` produces them) — the `(s, y)`-form of `ℝ × ℝ²` is
never needed, and could not be stated with the product model of `ℝ × ℝ²` anyway (`ℝ × ℝ²` carries no
`ChartedSpace 𝔼¹ × 𝔼²` instance).
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-! ## 1. The class projection, and the smoothness of a class map in every dimension -/

/-- **The projective class of a capped point.** -/
def cls (p : CappingSpace) : Projectivization ℝ (Eucl 3) := (cappingSpaceHomeoProj p).2

@[simp] lemma cls_apply (p : CappingSpace) : cls p = (cappingSpaceHomeoProj p).2 := rfl

/-- **The class map of a smooth presentation is `C^∞`** — the general-dimension form of
`Work.Drive.contMDiffAt_cls_of_contMDiff` (`classTripleAssemblyLiftFree.lean`, stated there for the
domain `ℝ²`).  The class is a component of the presentation read in the transparent model
`(0,∞) × ℝP³`, so its smoothness is componentwise smoothness of `cappingSpaceHomeoProj ∘ P`. -/
theorem contMDiffAt_cls_of_contMDiff_gen {k : ℕ} {P : EuclideanSpace ℝ (Fin k) → CappingSpace}
    (hP : ContMDiff (𝓡 k) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (y : EuclideanSpace ℝ (Fin k)) :
    ContMDiffAt (𝓡 k) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' => cls (P y')) y := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    Work.Drive.halfLineProjectiveCharted
  have hG : ContMDiffAt (𝓡 k) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => Work.Drive.cappingSpaceHomeoProj (P w)) y := by
    have hiff := Work.Drive.chartedStructure_contMDiffWithinAt
      (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4)) (H := EuclideanSpace ℝ (Fin 4))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (E' := EuclideanSpace ℝ (Fin k)) (H' := EuclideanSpace ℝ (Fin k)) (𝓡 k)
      (M := Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
      (M' := Work.Drive.CappingSpace) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      Work.Drive.cappingSpaceHomeoProj.symm P Set.univ y
    exact hiff.mp (hP.contMDiffAt)
  exact ((Work.Drive.contMDiffAt_halfLineProjective_iff
    (fun w => Work.Drive.cappingSpaceHomeoProj (P w)) y).mp hG).2

/-! ## 2. The cutoff -/

/-- **The cutoff of the clause homotopy**: `C^∞`, `0` on `(-∞, 1/10]`, `1` on `[9/10, ∞)`. -/
def clauseRho (s : ℝ) : ℝ := Real.smoothTransition ((5 / 4 : ℝ) * s - (1 / 8))

lemma contDiff_clauseRho : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) clauseRho := by
  unfold clauseRho
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)

lemma clauseRho_eq_zero {s : ℝ} (h : s ≤ 1 / 10) : clauseRho s = 0 := by
  unfold clauseRho
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

lemma clauseRho_eq_one {s : ℝ} (h : 9 / 10 ≤ s) : clauseRho s = 1 := by
  unfold clauseRho
  exact Real.smoothTransition.one_of_one_le (by linarith)

lemma clauseRho_mem (s : ℝ) : clauseRho s ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

@[simp] lemma clauseRho_zero : clauseRho 0 = 0 := clauseRho_eq_zero (by norm_num)
@[simp] lemma clauseRho_one : clauseRho 1 = 1 := clauseRho_eq_one (by norm_num)

/-! ## 3. The three stages of the clause homotopy -/

variable {Q : ℂ → CappingSpace}

/-- **The perturbation stage** of the clause homotopy, as a function of the chain parameter
`x = (x 0, x 1, x 2)`: the chart perturbation is undone along `x 2` by the cutoff. -/
def clauseA (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) :
    Projectivization ℝ (Eucl 3) :=
  cls (Ξ (clauseRho (1 - 3 * x 2) • blk k t) (P k (mk2 (x 0) (x 1))))

/-- **The (B)-lane stage** of the clause homotopy: the given homotopy `H0 k` from the unperturbed
plane to the linear disk model, reparametrised by the cutoff. -/
def clauseB (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) : Projectivization ℝ (Eucl 3) :=
  H0 k (clauseRho (3 * x 2 - 1), mk2 (x 0) (x 1))

/-- **The linear stage** of the clause homotopy: the disk model of the linear plane `φ k` at the level
`c`. -/
def clauseC (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c) (k : Fin 3)
    (x : EuclideanSpace ℝ (Fin 3)) : Projectivization ℝ (Eucl 3) :=
  cls (diskPlane (linPlaneChart (φ k) c hc) (mk2 (x 0) (x 1)))

/-- **The clause homotopy** (`NOTES_LEAD_hloc_htube_hsurj.md` §3.2(iv)), in its `(s, y)`-form. -/
def clauseHomot (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (t : EuclideanSpace ℝ (Fin 12)) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3)
    (c : ℝ) (hc : 0 < c) (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (k : Fin 3) (q : ℝ × EuclideanSpace ℝ (Fin 2)) : Projectivization ℝ (Eucl 3) :=
  if q.1 ≤ 1 / 3 then cls (Ξ (clauseRho (1 - 3 * q.1) • blk k t) (P k q.2))
  else if q.1 ≤ 2 / 3 then H0 k (clauseRho (3 * q.1 - 1), q.2)
  else cls (diskPlane (linPlaneChart (φ k) c hc) q.2)

/-- The chain form of the clause homotopy, as a function of the three chain parameters. -/
def clauseChain (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (t : EuclideanSpace ℝ (Fin 12)) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3)
    (c : ℝ) (hc : 0 < c) (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) : Projectivization ℝ (Eucl 3) :=
  if x 2 ≤ 1 / 3 then clauseA P Ξ t k x
  else if x 2 ≤ 2 / 3 then clauseB H0 k x else clauseC φ c hc k x

/-- The two forms of the clause homotopy agree (`(x 0, x 1, x 2) ↦ (x 2, mk2 (x 0) (x 1))`). -/
lemma clauseHomot_chain (P Ξ t φ c hc H0 k x) :
    clauseHomot P Ξ t φ c hc H0 k (x 2, mk2 (x 0) (x 1))
      = clauseChain P Ξ t φ c hc H0 k x := rfl

/-! ## 4. The smoothness of the two polynomial stages -/

/-- **The perturbation stage is `C^∞`.** -/
theorem contMDiff_clauseA (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3)
    (hP : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P k))
    (hΞ : ChartPert Q 4 Ξ) :
    ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (clauseA P Ξ t k) := by
  have h1 : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => clauseRho (1 - 3 * x 2) • blk k t) := by
    refine contMDiff_iff_contDiff.mpr ?_
    exact (contDiff_clauseRho.comp (by fun_prop)).smul contDiff_const
  have h2 : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => P k (mk2 (x 0) (x 1))) := by
    have hclm : ContMDiff (𝓡 3) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) mk2CLM :=
      mk2CLM.contDiff.contMDiff
    simpa only [Function.comp_def, mk2CLM_apply] using (hP k).comp hclm
  have hsm : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) =>
        Ξ (clauseRho (1 - 3 * x 2) • blk k t) (P k (mk2 (x 0) (x 1)))) :=
    hΞ.2.1.comp (h1.prodMk h2)
  intro x
  exact contMDiffAt_cls_of_contMDiff_gen hsm x

/-- **The linear stage is `C^∞`.** -/
theorem contMDiff_clauseC (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c) (k : Fin 3) :
    ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (clauseC φ c hc k) := by
  have hA : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (planeClassMap (diskPlane (linPlaneChart (φ k) c hc))) :=
    fun y => contMDiffAt_cls_of_contMDiff_gen
      (contMDiff_diskPlane (linPlaneChart_contMDiff (φ k) c hc)) y
  have hclm : ContMDiff (𝓡 3) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) mk2CLM :=
    mk2CLM.contDiff.contMDiff
  intro x
  exact (hA.comp hclm) x

/-! ## 5. The two joins are locally constant -/

/-- **The first join.**  Near `x 2 = 1/3` the perturbation stage and the (B)-lane stage agree: both
are `cls (P k y)`, the class map of the unperturbed plane. -/
lemma clauseA_eventuallyEq_clauseB (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3) (hΞ0 : ∀ p : CappingSpace, Ξ 0 p = p)
    (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (h0 : ∀ y : EuclideanSpace ℝ (Fin 2), H0 k (0, y) = planeClassMap (P k) y)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x 2 = 1 / 3) :
    clauseA P Ξ t k =ᶠ[𝓝 x] clauseB H0 k := by
  have hU1 : ∀ᶠ y in 𝓝 x, 1 - 3 * y 2 < 1 / 10 :=
    (isOpen_lt (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) => 1 - 3 * y 2)
      continuous_const).mem_nhds (by show (1:ℝ) - 3 * x 2 < 1 / 10; rw [hx]; norm_num)
  have hU2 : ∀ᶠ y in 𝓝 x, 3 * y 2 - 1 < 1 / 10 :=
    (isOpen_lt (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) => 3 * y 2 - 1)
      continuous_const).mem_nhds (by show 3 * x 2 - 1 < 1 / 10; rw [hx]; norm_num)
  filter_upwards [hU1, hU2] with y hy1 hy2
  rw [clauseA, clauseB, clauseRho_eq_zero hy1.le, clauseRho_eq_zero hy2.le, zero_smul, hΞ0, h0]
  rfl

/-- **The second join.**  Near `x 2 = 2/3` the (B)-lane stage and the linear stage agree: both are the
disk model of the linear plane. -/
lemma clauseB_eventuallyEq_clauseC (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (k : Fin 3)
    (h1 : ∀ y : EuclideanSpace ℝ (Fin 2),
      H0 k (1, y) = planeClassMap (diskPlane (linPlaneChart (φ k) c hc)) y)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x 2 = 2 / 3) :
    clauseB H0 k =ᶠ[𝓝 x] clauseC φ c hc k := by
  have hU : ∀ᶠ y in 𝓝 x, 9 / 10 < 3 * y 2 - 1 :=
    (isOpen_lt continuous_const (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) => 3 * y 2 - 1)).mem_nhds
      (by show (9:ℝ) / 10 < 3 * x 2 - 1; rw [hx]; norm_num)
  filter_upwards [hU] with y hy
  rw [clauseB, clauseC, clauseRho_eq_one hy.le, h1]
  rfl

/-! ## 6. The smoothness of the chain, and the four defining properties -/

/-- **The chain of the clause homotopy is `C^∞`.**  The three stages are smooth and each pair that
meets at a join agrees on a neighbourhood of the join, so the piecewise function is smooth. -/
theorem contMDiff_clauseChain (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (t : EuclideanSpace ℝ (Fin 12)) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3)
    (c : ℝ) (hc : 0 < c) (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (k : Fin 3)
    (hP : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P k))
    (hΞ : ChartPert Q 4 Ξ)
    (hB : ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (clauseB H0 k))
    (hΞ0 : ∀ p : CappingSpace, Ξ 0 p = p)
    (h0 : ∀ y : EuclideanSpace ℝ (Fin 2), H0 k (0, y) = planeClassMap (P k) y)
    (h1 : ∀ y : EuclideanSpace ℝ (Fin 2),
      H0 k (1, y) = planeClassMap (diskPlane (linPlaneChart (φ k) c hc)) y) :
    ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (clauseChain P Ξ t φ c hc H0 k) := by
  intro x
  have hA := contMDiff_clauseA P Ξ t k hP hΞ
  have hC := contMDiff_clauseC φ c hc k
  rcases lt_trichotomy (x 2) (1 / 3) with hlt | heq | hgt
  · -- first stage
    refine (hA x).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) => y 2)
      continuous_const).mem_nhds hlt] with y hy
    rw [clauseChain]; exact if_pos hy.le
  · -- first join
    refine (hB x).congr_of_eventuallyEq ?_
    have hAB := clauseA_eventuallyEq_clauseB P Ξ t k hΞ0 H0 h0 heq
    have hmid : ∀ᶠ y in 𝓝 x, y 2 < 2 / 3 :=
      (isOpen_lt (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) => y 2)
        continuous_const).mem_nhds (by show x 2 < 2 / 3; rw [heq]; norm_num)
    filter_upwards [hAB, hmid] with y hy hy2
    rw [clauseChain]
    by_cases hle : y 2 ≤ 1 / 3
    · rw [if_pos hle]; exact hy
    · rw [if_neg hle, if_pos hy2.le]
  · -- second stage
    rcases lt_trichotomy (x 2) (2 / 3) with hlt2 | heq2 | hgt2
    · refine (hB x).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_const (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) => y 2)).mem_nhds hgt,
        (isOpen_lt (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) => y 2) continuous_const).mem_nhds hlt2]
        with y hy1 hy2
      rw [clauseChain, if_neg (not_le.mpr hy1), if_pos hy2.le]
    · -- second join
      refine (hC x).congr_of_eventuallyEq ?_
      have hBC := clauseB_eventuallyEq_clauseC φ c hc H0 k h1 heq2
      have hmid : ∀ᶠ y in 𝓝 x, 1 / 3 < y 2 :=
        (isOpen_lt continuous_const (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) => y 2)).mem_nhds
          (by show (1:ℝ) / 3 < x 2; rw [heq2]; norm_num)
      filter_upwards [hBC, hmid] with y hy hy1
      rw [clauseChain]
      by_cases hle : y 2 ≤ 2 / 3
      · rw [if_neg (not_le.mpr hy1), if_pos hle]; exact hy
      · rw [if_neg (not_le.mpr hy1), if_neg hle]
    · refine (hC x).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_const (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) => y 2)).mem_nhds hgt2]
        with y hy
      rw [clauseChain, if_neg (not_le.mpr (lt_trans (by norm_num) hy)), if_neg (not_le.mpr hy)]

/-- **The first endpoint**: at `s = 0` the clause homotopy is the class map of the *perturbed* plane
`Ξ (blk k t) ∘ P k` — the `HasClassLinearization` clause. -/
theorem clauseHomot_zero (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (t : EuclideanSpace ℝ (Fin 12)) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3)
    (c : ℝ) (hc : 0 < c) (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (k : Fin 3) :
    (fun y => clauseHomot P Ξ t φ c hc H0 k (0, y))
      = planeClassMap (fun y => Ξ (blk k t) (P k y)) := by
  funext y
  rw [clauseHomot, if_pos (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  simp only [Prod.fst, Prod.snd, mul_zero, sub_zero, clauseRho_one, one_smul, planeClassMap,
    cls_apply]

/-- **The second endpoint**: at `s = 1` the clause homotopy is the disk model of the linear plane —
the `HasClassLinearization` clause. -/
theorem clauseHomot_one (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (t : EuclideanSpace ℝ (Fin 12)) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3)
    (c : ℝ) (hc : 0 < c) (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (k : Fin 3) :
    (fun y => clauseHomot P Ξ t φ c hc H0 k (1, y))
      = planeClassMap (diskPlane (linPlaneChart (φ k) c hc)) := by
  funext y
  rw [clauseHomot, if_neg (by norm_num : ¬ ((1 : ℝ) ≤ 1 / 3)),
    if_neg (by norm_num : ¬ ((1 : ℝ) ≤ 2 / 3))]
  simp only [Prod.fst, Prod.snd, planeClassMap, cls_apply]

/-- **The seam invariance** of the clause homotopy: the chain is invariant under the antipodal
involution of the parameter square on the seam — the `Meet3Hyp.seam` clause of the encoded chains. -/
theorem clauseHomot_seam (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (t : EuclideanSpace ℝ (Fin 12)) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3)
    (c : ℝ) (hc : 0 < c) (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (k : Fin 3)
    (hPseam : ∀ k : Fin 3, ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P k (seamInv2 y) = P k y)
    (hH0seam : ∀ (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y →
      H0 k (s, seamInv2 y) = H0 k (s, y))
    {s : ℝ} {y : EuclideanSpace ℝ (Fin 2)} (hy : onSeam2 y) :
    clauseHomot P Ξ t φ c hc H0 k (s, seamInv2 y)
      = clauseHomot P Ξ t φ c hc H0 k (s, y) := by
  by_cases hs : s ≤ 1 / 3
  · simp only [clauseHomot, Prod.fst, Prod.snd, if_pos hs]
    rw [hPseam k y hy]
  · by_cases hs2 : s ≤ 2 / 3
    · simp only [clauseHomot, Prod.fst, Prod.snd, if_neg hs, if_pos hs2]
      exact hH0seam (clauseRho (3 * s - 1)) y hy
    · simp only [clauseHomot, Prod.fst, Prod.snd, if_neg hs, if_neg hs2]
      rw [diskPlane_seamInv2 (Q := linPlaneChart (φ k) c hc)
        (fun z hz => linPlaneChart_neg (φ k) c hc hz) hy]

end

end Work.Drive
