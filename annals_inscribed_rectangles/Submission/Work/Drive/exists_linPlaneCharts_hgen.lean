import Mathlib
import Submission.Work.Drive.linPlaneReparamCount
import Submission.Work.Drive.linCommonPoint
import Submission.Work.Drive.linPlaneChartNormals

/-!
# An explicit three-chart family with the common point off all three lines at infinity

`Work.Drive.linCommonPt φ c hc h` is the unique point of the level `c` of the capping space lying on
all three linear projective planes `projLine (linSub (φ k))` when those are in general position.  The
end-contribution count (`Work.Drive.ncard_linPlaneReparamTriples_eq_one`, `hgen` in
`Work.Drive.ncard_linPlaneTriples_eq_one`) needs a family for which this common point is **not on the
boundary circle** of any of the three disk models `linPlaneChart (φ k) c hc` — the non-degeneracy
witness of `Submission/Work/Drive/EXPLICIT_LIN_PLANE_CHARTS.md`.

This file supplies it, by taking the three charts to be **coordinate permutations** of the four real
coordinates of `Eucl 3 = ℝ⁴`:

* `coordPerms 0 := (0 2)(1 3)`: `0↦2`, `1↦3`, `2↦0`, `3↦1`;
* `coordPerms 1 := (0 1 3 2)`: `0↦1`, `1↦3`, `2↦0`, `3↦2`;
* `coordPerms 2 := (0 1 2)`  : `0↦1`, `1↦2`, `2↦0`, `3↦3`.

The two facts that make the construction work are, with `coordPermCLM ρ` the coordinate permutation of
`Eucl 3`:

* `linFun (coordPermCLM ρ) v = v (ρ 3)`, so `linSub (coordPermCLM ρ) = {v : v (ρ 3) = 0}`.  Since `coordPerms k 3`
  runs over `1, 2, 3`, the triple intersection is `{v : v 1 = v 2 = v 3 = 0} = ℝ ∙ single 0 1`
  (`Work.Drive.iInf_linSub_coordPerms_eq`), and the common point is the class of `single 0 1`
  (`Work.Drive.eq_linCommonPt`);
* the line at infinity of the standard disk model is the class of `linVecC z` with `‖z‖ = 1`, which
  has vanishing coordinates `2` and `3`; a permutation `ρ` moves it to the coordinates `ρ 2`, `ρ 3`.
  With `ρ 2 = 0` for all three permutations and `(ρ k).symm 0 = 2`, the image of the boundary circle
  has vanishing coordinate `0`, whereas every multiple of `single 0 1` has coordinate `0` equal to its
  coefficient.  Hence the common point is not attained on any of the three boundary circles.

* `Work.Drive.exists_linPlaneCharts_hgen` — the lemma, with the general-position hypothesis `h` and the
  boundary avoidance `hgen` for these three charts.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-! ## 1. Coordinate permutations of `Eucl 3 = ℝ⁴` as continuous linear equivalences

`coordPermCLM ρ` is the continuous linear equivalence `(x j) ↦ (x (ρ.symm j))` of `Eucl 3`: it moves the
`i`-th coordinate to the `ρ i`-th position. -/

/-- The continuous linear equivalence of `Eucl 3 = ℝ⁴` induced by a permutation `ρ` of the four
coordinates, characterised by `(coordPermCLM ρ x) j = x (ρ.symm j)`. -/
def coordPermCLM (ρ : Equiv.Perm (Fin 4)) : Eucl 3 ≃L[ℝ] Eucl 3 :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ ρ).toContinuousLinearEquiv

lemma coordPermCLM_apply (ρ : Equiv.Perm (Fin 4)) (x : Eucl 3) (j : Fin 4) :
    coordPermCLM ρ x j = x (ρ.symm j) := by
  simp only [coordPermCLM, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

/-- The inverse of a coordinate permutation moves the coordinates by `ρ` itself. -/
lemma coordPermCLM_symm_apply (ρ : Equiv.Perm (Fin 4)) (x : Eucl 3) (j : Fin 4) :
    (coordPermCLM ρ).symm x j = x (ρ j) := by
  have h1 : coordPermCLM ρ ((coordPermCLM ρ).symm x) = x := (coordPermCLM ρ).apply_symm_apply x
  have h2 := congrArg (fun v : Eucl 3 => v (ρ j)) h1
  rw [coordPermCLM_apply] at h2
  rwa [Equiv.symm_apply_apply] at h2

/-- The normal functional `linFun` of a coordinate permutation is the coordinate functional at
`ρ 3`: `linFun φ` is the functional whose kernel is the plane `linSub φ = φ linStd`. -/
lemma linFun_coordPermCLM_apply (ρ : Equiv.Perm (Fin 4)) (v : Eucl 3) :
    linFun (coordPermCLM ρ) v = v (ρ 3) := by
  rw [linFun_apply, coordPermCLM_symm_apply]

/-- **The plane of a coordinate permutation is a coordinate hyperplane**: a vector lies in
`linSub (coordPermCLM ρ)` exactly when its `ρ 3`-th coordinate vanishes. -/
lemma mem_linSub_coordPermCLM_iff (ρ : Equiv.Perm (Fin 4)) (v : Eucl 3) :
    v ∈ linSub (coordPermCLM ρ) ↔ v (ρ 3) = 0 := by
  rw [← ker_linFun, LinearMap.mem_ker, linFun_coordPermCLM_apply]

/-! ## 2. The second real coordinate of the standard sphere lift

For `‖z‖ = 1` the sphere lift `linVecC z = (z, 1 - ‖z‖²)` of the disk model has vanishing second
complex coordinate, i.e. vanishing real coordinates `2` and `3`. -/

/-- The real coordinate `2` of `linVecC z` is the real part of its second complex coordinate, i.e.
`1 - ‖z‖²`; it vanishes on the unit circle. -/
lemma linVecC_apply_two (z : ℂ) : (linVecC z) 2 = 1 - ‖z‖ ^ 2 := by
  rw [show (linVecC z) 2 = (c₂ (linVecC z)).re from by simp [c₂], linVecC, c₂_ofComplex,
    Complex.ofReal_re]

/-! ## 3. The three coordinate permutations and their index arithmetic -/

/-- The coordinate permutation `(0 2)(1 3)`: `0↦2`, `1↦3`, `2↦0`, `3↦1`. -/
def coordPerm0 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3
/-- The coordinate permutation `(0 1 3 2)`: `0↦1`, `1↦3`, `2↦0`, `3↦2`. -/
def coordPerm1 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 0 3 * Equiv.swap 0 1
/-- The coordinate permutation `(0 1 2)`: `0↦1`, `1↦2`, `2↦0`, `3↦3`. -/
def coordPerm2 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 0 1

/-- The three coordinate permutations, as a family indexed by `Fin 3`. -/
def coordPerms : Fin 3 → Equiv.Perm (Fin 4) := ![coordPerm0, coordPerm1, coordPerm2]

/-- `coordPerms 0` is `(0 2)(1 3)`. -/
lemma coordPerms_zero : coordPerms 0 = coordPerm0 := rfl
/-- `coordPerms 1` is `(0 1 3 2)`. -/
lemma coordPerms_one : coordPerms 1 = coordPerm1 := rfl
/-- `coordPerms 2` is `(0 1 2)`. -/
lemma coordPerms_two : coordPerms 2 = coordPerm2 := rfl

/-- The three planes have distinct normal coordinates `1`, `2`, `3`: `coordPerms k 3` runs over `1, 2, 3`
(so in particular never vanishes). -/
lemma coordPerms_three_zero : coordPerms 0 3 = 1 := by decide
lemma coordPerms_three_one : coordPerms 1 3 = 2 := by decide
lemma coordPerms_three_two : coordPerms 2 3 = 3 := by decide

/-- The `ρ`-preimage of the coordinate `0` is the coordinate `2` for all three permutations: this is
what turns "the boundary circle has vanishing coordinate `2`" into "the image of the boundary circle
has vanishing coordinate `0`". -/
lemma coordPerms_symm_zero (k : Fin 3) : (coordPerms k).symm 0 = 2 := by fin_cases k <;> decide

/-- No plane's normal coordinate is `0`, i.e. `single 0 1` lies in all three planes. -/
lemma coordPerms_three_ne_zero (k : Fin 3) : coordPerms k 3 ≠ 0 := by fin_cases k <;> decide

/-! ## 4. The generator of the triple intersection and its finrank -/

/-- The first standard basis vector of `Eucl 3` is non-zero. -/
lemma hgenSingle_ne_zero : (EuclideanSpace.single 0 (1:ℝ) : Eucl 3) ≠ 0 := by
  intro h
  have h' := congrArg (fun v : Eucl 3 => v 0) h
  simp at h'

/-- `single 0 1` lies in all three planes: its `coordPerms k 3`-th coordinate vanishes. -/
lemma mem_linSub_hgenSingle (k : Fin 3) :
    (EuclideanSpace.single 0 (1:ℝ) : Eucl 3) ∈ linSub (coordPermCLM (coordPerms k)) := by
  rw [mem_linSub_coordPermCLM_iff]
  rw [PiLp.single_apply, if_neg (coordPerms_three_ne_zero k)]

/-- **The triple intersection of the three planes is the line spanned by `single 0 1`.** -/
lemma iInf_linSub_coordPerms_eq :
    (⨅ k : Fin 3, linSub (coordPermCLM (coordPerms k))) = ℝ ∙ (EuclideanSpace.single 0 (1:ℝ) : Eucl 3) := by
  have hmem : (EuclideanSpace.single 0 (1:ℝ) : Eucl 3) ∈
      (⨅ k : Fin 3, linSub (coordPermCLM (coordPerms k))) := by
    rw [Submodule.mem_iInf]
    intro k
    exact mem_linSub_hgenSingle k
  refine le_antisymm ?_ ?_
  · intro v hv
    rw [Submodule.mem_iInf] at hv
    rw [Submodule.mem_span_singleton]
    refine ⟨v 0, ?_⟩
    ext j
    fin_cases j
    · simp
    · have h : v 1 = 0 := by
        have h' : v (coordPerms 0 3) = 0 := (mem_linSub_coordPermCLM_iff _ v).mp (hv 0)
        rwa [coordPerms_three_zero] at h'
      simp [PiLp.smul_apply, h]
    · have h : v 2 = 0 := by
        have h' : v (coordPerms 1 3) = 0 := (mem_linSub_coordPermCLM_iff _ v).mp (hv 1)
        rwa [coordPerms_three_one] at h'
      simp [PiLp.smul_apply, h]
    · have h : v 3 = 0 := by
        have h' : v (coordPerms 2 3) = 0 := (mem_linSub_coordPermCLM_iff _ v).mp (hv 2)
        rwa [coordPerms_three_two] at h'
      simp [PiLp.smul_apply, h]
  · rw [Submodule.span_le]
    rintro x rfl
    exact hmem

/-- **General position**: the three planes `linSub (coordPermCLM (coordPerms k))` meet in a line. -/
lemma finrank_iInf_linSub_coordPerms :
    Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (coordPermCLM (coordPerms k))) = 1 := by
  rw [iInf_linSub_coordPerms_eq]
  exact finrank_span_singleton hgenSingle_ne_zero

/-! ## 5. The theorem -/

open Manifold in
open scoped Manifold ContDiff in
theorem exists_linPlaneCharts_hgen (c : ℝ) (hc : 0 < c) :
    ∃ φ : Fin 3 → Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3,
      ∃ h : Module.finrank ℝ ↥(⨅ k : Fin 3, Work.Drive.linSub (φ k)) = 1,
        ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
          Work.Drive.linPlaneChart (φ k) c hc z ≠ Work.Drive.linCommonPt φ c hc h := by
  refine ⟨fun k => coordPermCLM (coordPerms k), finrank_iInf_linSub_coordPerms, ?_⟩
  intro k z hz heq
  -- The common point of the three planes is the class of `single 0 1` at the level `c`.
  have hpt : cappingVecPoint c hc (EuclideanSpace.single 0 1) hgenSingle_ne_zero
      = linCommonPt (fun k => coordPermCLM (coordPerms k)) c hc finrank_iInf_linSub_coordPerms := by
    refine eq_linCommonPt (fun k => coordPermCLM (coordPerms k)) c hc finrank_iInf_linSub_coordPerms ?_ ?_
    · rw [cappingSpaceHomeoProj_cappingVecPoint]
    · intro j
      rw [cappingSpaceHomeoProj_cappingVecPoint]
      exact ⟨_, hgenSingle_ne_zero, mem_linSub_hgenSingle j, rfl⟩
  -- Equality of the chart value with the common point is an equality of projective classes.
  have hcls := congrArg (fun p => (cappingSpaceHomeoProj p).2) (heq.trans hpt.symm)
  rw [cappingSpaceHomeoProj_linPlaneChart, cappingSpaceHomeoProj_cappingVecPoint] at hcls
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℝ (coordPermCLM (coordPerms k) (linVecC z))
      (EuclideanSpace.single 0 1) (phi_linVecC_ne_zero (coordPermCLM (coordPerms k)) z)
      hgenSingle_ne_zero).mp hcls
  -- The image of the boundary circle has vanishing coordinate `0`, while `a • single 0 1` has
  -- coordinate `0` equal to `a`.  (For `‖z‖ = 1` the lift `linVecC z` has vanishing coordinates
  -- `2` and `3`, which are transported to the coordinate `0` by each of the three permutations.)
  have hzero : (coordPermCLM (coordPerms k) (linVecC z)) 0 = 0 := by
    rw [coordPermCLM_apply, coordPerms_symm_zero k, linVecC_apply_two, hz]
    norm_num
  have hkey : ((a : ℝ)) = 0 := by
    have h := congrArg (fun v : Eucl 3 => v 0) ha
    rw [hzero] at h
    rw [Units.smul_def, PiLp.smul_apply, PiLp.single_eq_same, smul_eq_mul, mul_one] at h
    exact h
  exact Units.ne_zero a hkey

end

end Work.Drive
