import Submission.Work.PTGeometric.Perturbation
import Submission.Work.PTGeometric.TransferLemma
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.mfderiv_surjective_of_submersionAt
import Submission.Work.PTGeometric.RieszProj.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: G3 in ambient coordinates — the moving-plane Sard step

The perturbation step of the null-bordism construction in the form in which the *ambient* data take
it: a smooth field `v : M → ℝⁿ` which takes values in the moving planes `im (P x)` of a smooth
projection-valued map `P`, and a finite family of Grassmannian charts `(ell l, U l)`, each carrying a
smooth `ell l`-adapted frame `e l` of the planes (i.e. `ell l (∑ j, t j • e l j y) = t` for `y` in the
chart).  Translating `v` by `χ • ∑ j, t j • e l j` (an amount which is *constant in the chart
coordinates*), the parametric Sard theorem `volume_badSet_eq_zero` makes every zero of the perturbed
field transverse in the chart `l` for almost every `t`.

The cutoffs of the finitely many stages are chosen with pairwise disjoint closures, so at a point of
one active region all the other perturbations vanish identically near it, and the transversality
obtained at one stage survives all the later ones — no new zeros are created outside the active
region.

## Main results

* `Work.PTGeometric.ambientPerturbation_step` — one step
* `Work.PTGeometric.exists_ambient_perturbation` — the theorem
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter MeasureTheory

namespace Work.PTGeometric

noncomputable section

variable {n k : ℕ}

/-- **The chart data of the ambient perturbation**: for each index `l`, an open set `U l` on which
the linear coordinate `ell l` is injective on the moving planes `im (P x)`, together with a smooth
`ell l`-adapted frame `e l` of those planes over `U l`. -/
structure AmbCharts (n k : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M]
    (P : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (m : ℕ) where
  /-- the chart coordinates -/
  ell : Fin m → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k)
  /-- the chart neighbourhoods -/
  U : Fin m → Set M
  /-- the `ell`-adapted frame of the moving planes -/
  e : Fin m → Fin k → M → EuclideanSpace ℝ (Fin n)
  /-- the chart neighbourhoods are open -/
  isOpen_U : ∀ l, IsOpen (U l)
  /-- the chart neighbourhoods cover the source -/
  covers : ∀ x, ∃ l, x ∈ U l
  /-- the frame is smooth -/
  contMDiff_e : ∀ l j, ContMDiff (𝓡∂ ((8 + k) + 1))
    (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (e l j)
  /-- the chart coordinate is injective on the planes over the chart -/
  ell_inj : ∀ l y, y ∈ U l → ∀ z : EuclideanSpace ℝ (Fin n),
    P y z = z → ell l z = 0 → z = 0
  /-- the frame vectors lie in the planes -/
  mem_e : ∀ l j y, y ∈ U l → P y (e l j y) = e l j y
  /-- the frame is `ell`-adapted: the frame sum has the chart coordinates `t` -/
  ell_frame : ∀ l y, y ∈ U l → ∀ t : EuclideanSpace ℝ (Fin k),
    ell l ((Finset.univ : Finset (Fin k)).sum (fun j => t j • e l j y)) = t

namespace AmbCharts

variable {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
  [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M]
  {P : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)} {m : ℕ}

/-- The frame sum `∑ j, t j • e l j` is smooth. -/
lemma contMDiff_frameSum (C : AmbCharts n k M P m) (l : Fin m)
    (t : EuclideanSpace ℝ (Fin k)) :
    ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun y => (Finset.univ : Finset (Fin k)).sum (fun j => t j • C.e l j y)) := by
  classical
  have key : ∀ s : Finset (Fin k), ContMDiff (𝓡∂ ((8 + k) + 1))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun y => s.sum (fun j => t j • C.e l j y)) := by
    intro s
    induction s using Finset.induction with
    | empty =>
      simpa using (contMDiff_const (I := 𝓡∂ ((8 + k) + 1))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (c := (0 : EuclideanSpace ℝ (Fin n))))
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (((contMDiff_const (I := 𝓡∂ ((8 + k) + 1))
        (I' := 𝓘(ℝ, ℝ)) (c := t a)).smul (C.contMDiff_e l a))).add ih
  simpa using key Finset.univ

/-- The frame sum takes values in the moving planes. -/
lemma mem_frameSum (C : AmbCharts n k M P m) (l : Fin m)
    (t : EuclideanSpace ℝ (Fin k)) {y : M} (hy : y ∈ C.U l) :
    P y ((Finset.univ : Finset (Fin k)).sum (fun j => t j • C.e l j y))
      = (Finset.univ : Finset (Fin k)).sum (fun j => t j • C.e l j y) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, C.mem_e l j y hy]

end AmbCharts

/-- **Goodness of an ambient field at a point**: the point is not a zero of the field, or it is a
chart-transverse zero of it. -/
def AmbGood {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M]
    {P : M → EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin n)} {m : ℕ} (C : AmbCharts n k M P m)
    (u : M → EuclideanSpace ℝ (Fin n)) (x : M) : Prop :=
  u x ≠ 0 ∨ ∃ l, x ∈ C.U l ∧
    IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞ (fun y => C.ell l (u y)) x

variable {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
  [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M] [Nonempty M]
  {P : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)} {m : ℕ}
  {C : AmbCharts n k M P m}

/-- **The perturbed field**: translate `u` by `χ • ∑ j, t j • e l j`. -/
def ambPerturb (C : AmbCharts n k M P m) (l : Fin m) (χ : M → ℝ)
    (t : EuclideanSpace ℝ (Fin k)) (u : M → EuclideanSpace ℝ (Fin n)) :
    M → EuclideanSpace ℝ (Fin n) :=
  fun y => u y + χ y • (Finset.univ : Finset (Fin k)).sum (fun j => t j • C.e l j y)

/-- The perturbation of a smooth `P`-valued field is smooth. -/
lemma contMDiff_ambPerturb (C : AmbCharts n k M P m) (l : Fin m) {χ : M → ℝ}
    {u : M → EuclideanSpace ℝ (Fin n)} (t : EuclideanSpace ℝ (Fin k))
    (hχ : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ∞ χ)
    (hu : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ u) :
    ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (ambPerturb C l χ t u) := by
  refine hu.add ?_
  exact hχ.smul (C.contMDiff_frameSum l t)

/-- The perturbation of a `P`-valued field is `P`-valued. -/
lemma ambPerturb_mem (C : AmbCharts n k M P m) (l : Fin m) (χ : M → ℝ)
    (t : EuclideanSpace ℝ (Fin k)) {u : M → EuclideanSpace ℝ (Fin n)}
    (hu : ∀ y, P y (u y) = u y) (hχ : ∀ y, χ y ≠ 0 → y ∈ C.U l) :
    ∀ y, P y (ambPerturb C l χ t u y) = ambPerturb C l χ t u y := by
  intro y
  rw [ambPerturb, map_add]
  by_cases h : χ y = 0
  · simp only [h, zero_smul, map_zero, add_zero, hu y]
  · rw [hu y, map_smul, C.mem_frameSum l t (hχ y h)]

/-- The chart expression of the perturbation is `ell l u + χ • t`. -/
lemma ambPerturb_ell (C : AmbCharts n k M P m) (l : Fin m) (χ : M → ℝ)
    (t : EuclideanSpace ℝ (Fin k)) (u : M → EuclideanSpace ℝ (Fin n))
    (hχ : ∀ y, χ y ≠ 0 → y ∈ C.U l) (y : M) :
    C.ell l (ambPerturb C l χ t u y) = C.ell l (u y) + χ y • t := by
  rw [ambPerturb, map_add, map_smul]
  by_cases h : χ y = 0
  · simp only [h, zero_smul, add_zero]
  · rw [C.ell_frame l y (hχ y h) t]

/-- **One step of the ambient perturbation.**  Given a smooth `P`-valued field `u`, a chart index
`l` and a smooth nonnegative cut-off `χ` vanishing outside `U l`, there is a parameter `t` (of
arbitrarily small norm) such that every zero of the perturbed field `ambPerturb C l χ t u` inside
`{χ ≠ 0}` is `ell l`-transverse. -/
theorem ambientPerturbation_step (C : AmbCharts n k M P m) (l : Fin m) (χ : M → ℝ)
    (hχ : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ∞ χ) (hχ0 : ∀ y, 0 ≤ χ y)
    (hχU : ∀ y, χ y ≠ 0 → y ∈ C.U l)
    (u : M → EuclideanSpace ℝ (Fin n))
    (hu : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ u)
    (hmem : ∀ y, P y (u y) = u y) (δ : ℝ) (hδ : 0 < δ) :
    ∃ t : EuclideanSpace ℝ (Fin k), ‖t‖ ≤ δ ∧
      ∀ x, (𝓡∂ ((8 + k) + 1)).IsInteriorPoint x → χ x ≠ 0 →
        ambPerturb C l χ t u x = 0 →
        IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞
          (fun y => C.ell l (ambPerturb C l χ t u y)) x := by
  classical
  set G : M → EuclideanSpace ℝ (Fin k) := fun y => -(C.ell l (u y)) with hGdef
  have hGsm : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞ G :=
    ((C.ell l).contMDiff.comp hu).neg
  set Bad : Set (EuclideanSpace ℝ (Fin k)) := {t |
      ∃ x, (𝓡∂ ((8 + k) + 1)).IsInteriorPoint x ∧ 0 < χ x ∧ G x = χ x • t ∧
        ¬ Function.Surjective (mfderiv (𝓡∂ ((8 + k) + 1)) (𝓡 k)
          (fun y => G y - χ y • t) x)} with hBaddef
  have hB : volume Bad = 0 := by
    rw [hBaddef]
    exact Work.ThomBordism.Transversality.TransversalApproximation.volume_badSet_eq_zero
      (𝓡∂ ((8 + k) + 1)) G hGsm χ hχ hχ0
  obtain ⟨t, htBad, htball⟩ : ∃ t, t ∉ Bad ∧ t ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) δ := by
    by_contra h
    have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin k)) δ ⊆ Bad := by
      intro u hu
      by_contra hc
      exact h ⟨u, hc, hu⟩
    have hle : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) δ) ≤ volume Bad :=
      measure_mono hsub
    rw [hB, le_zero_iff] at hle
    exact absurd hle (ne_of_gt (Metric.measure_ball_pos volume
      (0 : EuclideanSpace ℝ (Fin k)) hδ))
  have htδ : ‖t‖ ≤ δ := by
    have h1 : dist t 0 < δ := Metric.mem_ball.mp htball
    rw [dist_eq_norm, sub_zero] at h1
    exact le_of_lt h1
  refine ⟨t, htδ, ?_⟩
  intro x hxint hχx hvx
  have hxU : x ∈ C.U l := hχU x hχx
  have hpos : 0 < χ x := lt_of_le_of_ne (hχ0 x) (Ne.symm hχx)
  have hell : C.ell l (ambPerturb C l χ t u x) = C.ell l (u x) + χ x • t :=
    ambPerturb_ell C l χ t u hχU x
  have hval : C.ell l (ambPerturb C l χ t u x) = 0 := by rw [hvx, map_zero]
  have hGx : G x = χ x • t := by
    rw [hGdef]
    show -(C.ell l (u x)) = χ x • t
    have h : C.ell l (u x) + χ x • t = 0 := by rw [← hell, hval]
    rw [← neg_eq_iff_add_eq_zero.mpr h]
  have hkey : (fun y => G y - χ y • t) = fun y => -(C.ell l (ambPerturb C l χ t u y)) := by
    funext y
    have h := ambPerturb_ell C l χ t u hχU y
    show -(C.ell l (u y)) - χ y • t = -(C.ell l (ambPerturb C l χ t u y))
    rw [h]
    abel
  have hsurjG : Function.Surjective (mfderiv (𝓡∂ ((8 + k) + 1)) (𝓡 k)
      (fun y => G y - χ y • t) x) := by
    by_contra hc
    apply htBad
    rw [hBaddef]
    exact ⟨x, hxint, hpos, hGx, hc⟩
  have hsurj : Function.Surjective (mfderiv (𝓡∂ ((8 + k) + 1)) (𝓡 k)
      (fun y => -(C.ell l (ambPerturb C l χ t u y))) x) := by
    rwa [hkey] at hsurjG
  have hsurj' : Function.Surjective (mfderiv (𝓡∂ ((8 + k) + 1)) (𝓡 k)
      (fun y => C.ell l (ambPerturb C l χ t u y)) x) := by
    intro v
    obtain ⟨w, hw⟩ := hsurj (-v)
    have h2 : (mfderiv (𝓡∂ ((8 + k) + 1)) (𝓡 k)
        (fun y => -(C.ell l (ambPerturb C l χ t u y))) x) w
        = -((mfderiv (𝓡∂ ((8 + k) + 1)) (𝓡 k)
          (fun y => C.ell l (ambPerturb C l χ t u y)) x) w) := by
      have hneg : mfderiv (𝓡∂ ((8 + k) + 1)) (𝓡 k)
          (fun y => -(C.ell l (ambPerturb C l χ t u y))) x
          = -(mfderiv (𝓡∂ ((8 + k) + 1)) (𝓡 k)
            (fun y => C.ell l (ambPerturb C l χ t u y)) x) := by
        rw [show (fun y => -(C.ell l (ambPerturb C l χ t u y)))
            = -(fun y => C.ell l (ambPerturb C l χ t u y)) from rfl]
        exact mfderiv_neg
      rw [hneg]
      rfl
    rw [h2] at hw
    exact ⟨w, neg_injective hw⟩
  have hsm : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞
      (fun y => C.ell l (ambPerturb C l χ t u y)) :=
    (C.ell l).contMDiff.comp (contMDiff_ambPerturb C l t hχ hu)
  exact Work.ThomBordism.Transversality.TransversalApproximation.isSubmersionAt_of_surjective_mfderiv
    (𝓡∂ ((8 + k) + 1)) hsm hxint hval hsurj'

/-- A perturbation whose cut-off vanishes at the point is the identity there. -/
lemma ambPerturb_eq_of_chi_eq_zero (C : AmbCharts n k M P m) (l : Fin m) {χ : M → ℝ}
    (t : EuclideanSpace ℝ (Fin k)) (u : M → EuclideanSpace ℝ (Fin n)) {y : M} (h : χ y = 0) :
    ambPerturb C l χ t u y = u y := by
  rw [ambPerturb, h, zero_smul, add_zero]

/-- **The transfer lemma for the ambient perturbation.**  At an interior zero of the cut-off `χ`, the
perturbation `ambPerturb C l χ t u` has the same derivative as `u`: a nonnegative factor vanishing at
an interior point contributes nothing to the derivative. -/
lemma mfderiv_ambPerturb_eq_of_chi_eq_zero (C : AmbCharts n k M P m) (l : Fin m) {χ : M → ℝ}
    (hχ : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ∞ χ) (hχ0 : ∀ y, 0 ≤ χ y)
    (t : EuclideanSpace ℝ (Fin k)) {u : M → EuclideanSpace ℝ (Fin n)}
    (hu : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ u)
    {x : M} (hxint : (𝓡∂ ((8 + k) + 1)).IsInteriorPoint x) (hχx : χ x = 0) :
    mfderiv (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (ambPerturb C l χ t u) x =
      mfderiv (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) u x := by
  have hsm : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun y => χ y • (Finset.univ : Finset (Fin k)).sum (fun j => t j • C.e l j y)) :=
    hχ.smul (C.contMDiff_frameSum l t)
  have hzero : mfderiv (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (fun y => χ y • (Finset.univ : Finset (Fin k)).sum (fun j => t j • C.e l j y)) x = 0 :=
    mfderiv_smul_eq_zero_of_isLocalMin (𝓡∂ ((8 + k) + 1)) hχ
      (C.contMDiff_frameSum l t) hχ0 hχx hxint
  rw [show ambPerturb C l χ t u =
      (u + fun y => χ y • (Finset.univ : Finset (Fin k)).sum (fun j => t j • C.e l j y))
      from rfl,
    mfderiv_add (hu.mdifferentiableAt (by simp)) (hsm.mdifferentiableAt (by simp)), hzero,
    add_zero]

/-- **The transfer lemma in a chart coordinate.**  Composing with a continuous linear coordinate `ℓ`,
the perturbation does not change the derivative at an interior zero of the cut-off.  This is the form
in which the perturbation stages of the iteration are compared. -/
lemma mfderiv_comp_ell_ambPerturb_eq_of_chi_eq_zero (C : AmbCharts n k M P m) (l : Fin m)
    {χ : M → ℝ} (hχ : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ∞ χ) (hχ0 : ∀ y, 0 ≤ χ y)
    (t : EuclideanSpace ℝ (Fin k)) {u : M → EuclideanSpace ℝ (Fin n)}
    (hu : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ u)
    (ℓ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k))
    {x : M} (hxint : (𝓡∂ ((8 + k) + 1)).IsInteriorPoint x) (hχx : χ x = 0) :
    mfderiv (𝓡∂ ((8 + k) + 1)) (𝓡 k) (fun y => ℓ (ambPerturb C l χ t u y)) x =
      mfderiv (𝓡∂ ((8 + k) + 1)) (𝓡 k) (fun y => ℓ (u y)) x := by
  have hS : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun y => (Finset.univ : Finset (Fin k)).sum (fun j => t j • C.e l j y)) :=
    C.contMDiff_frameSum l t
  have hcomp : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) ∞
      (fun y => ℓ ((Finset.univ : Finset (Fin k)).sum (fun j => t j • C.e l j y))) :=
    ℓ.contMDiff.comp hS
  have h1 : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) ∞
      (fun y => ℓ (u y)) := ℓ.contMDiff.comp hu
  have h2 : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) ∞
      (fun y => χ y •
        ℓ ((Finset.univ : Finset (Fin k)).sum (fun j => t j • C.e l j y))) := hχ.smul hcomp
  have hzero : mfderiv (𝓡∂ ((8 + k) + 1)) (𝓡 k)
      (fun y => χ y • ℓ ((Finset.univ : Finset (Fin k)).sum (fun j => t j • C.e l j y))) x = 0 :=
    mfderiv_smul_eq_zero_of_isLocalMin (𝓡∂ ((8 + k) + 1)) hχ hcomp hχ0 hχx hxint
  have hfun : (fun y => ℓ (ambPerturb C l χ t u y)) =
      ((fun y => ℓ (u y)) + fun y => χ y •
        ℓ ((Finset.univ : Finset (Fin k)).sum (fun j => t j • C.e l j y))) := by
    funext y
    simp only [ambPerturb, map_add, map_smul, Pi.add_apply]
  rw [hfun, mfderiv_add (h1.mdifferentiableAt (by simp)) (h2.mdifferentiableAt (by simp)),
    hzero, add_zero]

/-- **The ambient perturbation theorem.**  A smooth `P`-valued field `v` on a compact source, a finite
family of Grassmannian charts with adapted frames, nonnegative cut-offs `χ l` with `{χ l ≠ 0} ⊆ U l`
contained in the interior and vanishing near the boundary, and the covering condition that every point
where all the cut-offs vanish is already `AmbGood` for `v`: then some perturbation of `v` (by the
chartwise frame sums) is still `P`-valued, agrees with `v` off the active regions, and is transverse
to the zero section along the planes everywhere.

The cut-offs need **no** disjointness assumption: the transfer lemma
`mfderiv_comp_ell_ambPerturb_eq_of_chi_eq_zero` shows that a perturbation supported at an interior zero
of its own cut-off does not change the derivative there, which is exactly what makes the
transversality obtained at one stage survive the later stages. -/
theorem exists_ambient_perturbation (C : AmbCharts n k M P m) (v : M → EuclideanSpace ℝ (Fin n))
    (hv : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ v)
    (hmem : ∀ x, P x (v x) = v x)
    (χ : Fin m → M → ℝ)
    (hχsm : ∀ l, ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ∞ (χ l))
    (hχrange : ∀ l x, 0 ≤ χ l x ∧ χ l x ≤ 1)
    (hχU : ∀ l y, χ l y ≠ 0 → y ∈ C.U l)
    (hχint : ∀ l y, χ l y ≠ 0 → (𝓡∂ ((8 + k) + 1)).IsInteriorPoint y)
    (hbd : ∃ V : Set M, IsOpen V ∧ (𝓡∂ ((8 + k) + 1)).boundary M ⊆ V ∧
      ∀ l y, y ∈ V → χ l y = 0)
    (hcov : ∀ x, (∀ l, χ l x = 0) → AmbGood C v x) :
    ∃ v' : M → EuclideanSpace ℝ (Fin n),
      ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ v' ∧
      (∀ y, P y (v' y) = v' y) ∧
      (∀ x, (∀ l, χ l x = 0) → v' x = v x) ∧
      (∀ x, AmbGood C v' x) := by
  classical
  have key : ∀ r : ℕ, r ≤ m → ∃ w : M → EuclideanSpace ℝ (Fin n),
      ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ w ∧
      (∀ y, P y (w y) = w y) ∧
      (∀ x, (∀ l, l.1 < r → χ l x = 0) → w x = v x) ∧
      (∀ x, (𝓡∂ ((8 + k) + 1)).IsInteriorPoint x →
        (∀ l, l.1 < r → χ l x = 0) →
        ∀ ℓ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k),
          mfderiv (𝓡∂ ((8 + k) + 1)) (𝓡 k) (fun y => ℓ (w y)) x =
            mfderiv (𝓡∂ ((8 + k) + 1)) (𝓡 k) (fun y => ℓ (v y)) x) ∧
      (∀ x, (𝓡∂ ((8 + k) + 1)).IsInteriorPoint x →
        (∃ l : Fin m, l.1 < r ∧ χ l x ≠ 0) → w x = 0 →
        ∃ l : Fin m, l.1 < r ∧ χ l x ≠ 0 ∧
          IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞ (fun y => C.ell l (w y)) x) := by
    intro r hr
    induction r with
    | zero =>
      refine ⟨v, hv, hmem, fun _ _ => rfl, fun _ _ _ _ => rfl, ?_⟩
      rintro x _ ⟨l, hl, _⟩
      exact absurd hl (Nat.not_lt_zero l.1)
    | succ r ih =>
      obtain ⟨w, hwsm, hwmem, hwv, hwmf, hwS⟩ := ih (Nat.le_of_succ_le hr)
      have hrm : r < m := Nat.lt_of_succ_le hr
      obtain ⟨t, -, hsard⟩ := ambientPerturbation_step C ⟨r, hrm⟩ (χ ⟨r, hrm⟩)
        (hχsm ⟨r, hrm⟩) (fun y => (hχrange ⟨r, hrm⟩ y).1)
        (fun y hy => hχU ⟨r, hrm⟩ y hy) w hwsm hwmem 1 one_pos
      refine ⟨ambPerturb C ⟨r, hrm⟩ (χ ⟨r, hrm⟩) t w,
        contMDiff_ambPerturb C ⟨r, hrm⟩ t (hχsm ⟨r, hrm⟩) hwsm,
        ambPerturb_mem C ⟨r, hrm⟩ (χ ⟨r, hrm⟩) t hwmem
          (fun y hy => hχU ⟨r, hrm⟩ y hy), ?_, ?_, ?_⟩
      · -- the value is unchanged where all the cut-offs up to `r` vanish
        intro x hx
        rw [ambPerturb_eq_of_chi_eq_zero C ⟨r, hrm⟩ t w (hx ⟨r, hrm⟩ (Nat.lt_succ_self r))]
        exact hwv x (fun l hl => hx l (Nat.lt_trans hl (Nat.lt_succ_self r)))
      · -- the derivative does not change either
        intro x hxint hx ℓ
        have hχr : χ ⟨r, hrm⟩ x = 0 := hx ⟨r, hrm⟩ (Nat.lt_succ_self r)
        rw [mfderiv_comp_ell_ambPerturb_eq_of_chi_eq_zero C ⟨r, hrm⟩ (hχsm ⟨r, hrm⟩)
          (fun y => (hχrange ⟨r, hrm⟩ y).1) t hwsm ℓ hxint hχr]
        exact hwmf x hxint (fun l hl => hx l (Nat.lt_trans hl (Nat.lt_succ_self r))) ℓ
      · -- the transversality at the new zeros and the survival of the old ones
        intro x hxint hact hwx
        obtain ⟨l, hl, hlχ⟩ := hact
        by_cases hχr : χ ⟨r, hrm⟩ x = 0
        · -- the last perturbation vanishes at `x`: the derivative is unchanged
          have hzer : ambPerturb C ⟨r, hrm⟩ (χ ⟨r, hrm⟩) t w x = w x :=
            ambPerturb_eq_of_chi_eq_zero C ⟨r, hrm⟩ t w hχr
          have hwx' : w x = 0 := by rw [← hzer]; exact hwx
          have hlt : l.1 < r := by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hl with h | h
            · exact h
            · have hle : l = ⟨r, hrm⟩ := Fin.ext h
              exact absurd (hle.symm ▸ hχr) hlχ
          obtain ⟨l', hl't, hl'χ, hsub⟩ := hwS x hxint ⟨l, hlt, hlχ⟩ hwx'
          refine ⟨l', Nat.lt_trans hl't (Nat.lt_succ_self r), hl'χ, ?_⟩
          have hsurj := Work.ThomBordism.Transversality.TransversalApproximation.mfderiv_surjective_of_submersionAt (𝓡∂ ((8 + k) + 1)) hxint hsub
          rw [← mfderiv_comp_ell_ambPerturb_eq_of_chi_eq_zero C ⟨r, hrm⟩ (hχsm ⟨r, hrm⟩)
            (fun y => (hχrange ⟨r, hrm⟩ y).1) t hwsm (C.ell l') hxint hχr] at hsurj
          exact Work.ThomBordism.Transversality.TransversalApproximation.isSubmersionAt_of_surjective_mfderiv (𝓡∂ ((8 + k) + 1))
            ((C.ell l').contMDiff.comp (contMDiff_ambPerturb C ⟨r, hrm⟩ t
              (hχsm ⟨r, hrm⟩) hwsm)) hxint
            (by simp only [Function.comp_apply, hwx, map_zero]) hsurj
        · -- the new chart
          exact ⟨⟨r, hrm⟩, Nat.lt_succ_self r, hχr,
            hsard x hxint hχr hwx⟩
  obtain ⟨w, hwsm, hwmem, hwv, hwmf, hwS⟩ := key m le_rfl
  obtain ⟨V, hVopen, hVbd, hV0⟩ := hbd
  refine ⟨w, hwsm, hwmem, fun x hx => hwv x (fun l _ => hx l), ?_⟩
  intro x
  by_cases hwx : w x = 0
  · by_cases hact : ∃ l : Fin m, χ l x ≠ 0
    · obtain ⟨l, hl⟩ := hact
      obtain ⟨l', hl', hl'χ, hsub⟩ := hwS x (hχint l x hl) ⟨l, l.2, hl⟩ hwx
      exact Or.inr ⟨l', hχU l' x hl'χ, hsub⟩
    · simp only [not_exists] at hact
      have hall : ∀ l : Fin m, χ l x = 0 := fun l => not_not.mp (hact l)
      have hvw : v x = w x := (hwv x (fun l _ => hall l)).symm
      have hvx : v x = 0 := by rw [hvw]; exact hwx
      rcases hcov x hall with hvne | ⟨l, hxU, hsub⟩
      · exact absurd (hvw ▸ hvx) hvne
      · by_cases hxint : (𝓡∂ ((8 + k) + 1)).IsInteriorPoint x
        · refine Or.inr ⟨l, hxU, ?_⟩
          have hsurj := Work.ThomBordism.Transversality.TransversalApproximation.mfderiv_surjective_of_submersionAt (𝓡∂ ((8 + k) + 1)) hxint hsub
          rw [← hwmf x hxint (fun l' _ => hall l') (C.ell l)] at hsurj
          exact Work.ThomBordism.Transversality.TransversalApproximation.isSubmersionAt_of_surjective_mfderiv (𝓡∂ ((8 + k) + 1))
            ((C.ell l).contMDiff.comp hwsm) hxint
            (by simp only [Function.comp_apply, hwx, map_zero]) hsurj
        · have hxbd : x ∈ (𝓡∂ ((8 + k) + 1)).boundary M := by
            by_contra h
            exact hxint (((𝓡∂ ((8 + k) + 1)).isInteriorPoint_iff_not_isBoundaryPoint x).mpr h)
          have hev : (fun y => C.ell l (w y)) =ᶠ[𝓝 x] (fun y => C.ell l (v y)) := by
            filter_upwards [hVopen.mem_nhds (hVbd hxbd)] with y hy
            rw [hwv y (fun l' _ => hV0 l' y hy)]
          exact Or.inr ⟨l, hxU, (IsSubmersionAt.congr_iff hev).mpr hsub⟩
  · exact Or.inl hwx

end

end Work.PTGeometric
