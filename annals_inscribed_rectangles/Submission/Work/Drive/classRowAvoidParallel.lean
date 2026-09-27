import Mathlib
import Submission.Work.Drive.exists_linPlaneCharts_hgen
import Submission.Work.Drive.linearPlaneChart
import Submission.Work.Drive.endsHomotopy
import Submission.Work.Sard.wp.Defs

/-!
# One linear automorphism near the identity avoiding the anti-parallel cone of three curves

**Statement.**  For three smooth nowhere vanishing curves `w k : ℝ → Eucl 3`, `k : Fin 3`, and any
`ε > 0` there is a linear automorphism `A` of `Eucl 3` with

* `‖A - 1‖ < ε` (operator norm on `Eucl 3 →L[ℝ] Eucl 3`), and
* for every `k` and every `t ∈ [-1,1]`, the image of `linVecC t` under
  `(coordPermCLM (coordPerms k)) ∘ A` is *not* a negative multiple of `w k t`.

This is the *simultaneous* (three-curve) form of
`Work.Drive.exists_linearIsometryEquiv_avoid_negParallel_dense`, and it is the analytic input that
the three-chart family `Work.Drive.exists_linPlaneCharts_hgen` needs: the three charts are the
coordinate permutations `coordPerms k`, and one single automorphism `A` must move all three
conjugated charts off the anti-parallel locus of their respective curves.

## The mathematics

The composite `(coordPermCLM ρ).trans A` is `A ∘ coordPermCLM ρ`, so — with `f k := coordPermCLM
(coordPerms k)` — the condition is `A (f k (linVecC t)) ∉ ℝ_{<0} · (w k t)`.  In coordinates
`linVecC t = t • e₀ + (1 - t²) • e₂` with `e₀ = linVecC 1`, `e₂ = linVecC 0`, so

> `f k (linVecC t) = (1 - t²) • e₀ + t • e_{ρ k 0}`,  where `ρ k := coordPerms k`,

because `f k` permutes coordinates and `ρ k 2 = 0`, `ρ 0 0 = 2`, `ρ 1 0 = ρ 2 0 = 1`
(`coordPerms_symm_zero`, `coordPerms_val_*`).

Take `A` to be the linear map with columns `A e₀ = p`, `A e₁ = q`, `A e₂ = r`, `A e₃ = e₃` (and
close to the identity, hence invertible: `Work.Drive.colsLM`).  Then
`A (f k (linVecC t)) = (1 - t²) • p + t • (a k)` with `a := ![r, q, q]`, and a negative multiple of
`w k t` would force `w k t ∈ span {p, a k}`:

* `k = 0`: `span {p, r}`, excluded by `Work.Drive.notMem_span_of_avoid` for the pair `(r, p)` and
  the curve `w 0`;
* `k = 1, 2`: `span {p, q}`, excluded the same way for the pair `(q, p)` and the curves `w 1`, `w 2`.

The two generic inputs of that `crNotMem_span_of_avoid` are produced by the Baire arguments
`exists_avoidCone_family_cr` (the vector `q` avoids the cones over `w 1`, `w 2`; the vector `r` avoids
the cone over `w 0`) and `exists_avoidPlane_family_cr` (the vector `p` avoids the planes
`ℝ (a k) + ℝ (w k t)` for all three curves): each bad set is a *countable* union of compact images
of smooth maps from a lower-dimensional source, hence has empty interior by
`Work.Sard.wp.interior_eq_empty_iUnion_isClosed` and
`Work.Drive.interior_image_empty_of_contDiffOn`, so its complement meets every ball.

The linear algebra of the columns is isolated in `colsLin_cr` (coordinates) and `colsLM_cr`
(`Eucl 3`), together with the norm bound `colsLM_norm_le_cr` and the injectivity `colsLM_injective_cr`
that turn `colsLM_cr p q r` into a continuous linear equivalence.
-/

namespace Work.Drive

open Set Metric Filter
open scoped ContDiff Topology

noncomputable section

/-- The coordinate equivalence `Eucl 3 ≃ ℝ⁴` (a fresh copy: the original lives in a module which
cannot be co-imported with `Submission.Work.Drive.projTimesLine`). -/
noncomputable abbrev crEuclCoordsT : Eucl 3 ≃L[ℝ] (Fin 4 → ℝ) := EuclideanSpace.equiv (Fin 4) ℝ

/-- In the coordinates `Eucl 3 ≅ (Fin 4 → ℝ)`, the sphere lift of a *real* `t` is
`t • e₀ + (1 - t²) • e₂`. -/
lemma crEucEq_linVecC (t : ℝ) :
    EuclideanSpace.equiv (Fin 4) ℝ (linVecC (t : ℂ))
      = t • Pi.single 0 1 + (1 - t ^ 2) • Pi.single 2 1 := by
  have hre : ((t : ℂ) ^ 2).re = t ^ 2 := by
    have h : ((t : ℂ) ^ 2) = ((t * t : ℝ) : ℂ) := by rw [pow_two, ← Complex.ofReal_mul]
    rw [h, Complex.ofReal_re]; ring
  have him : ((t : ℂ) ^ 2).im = 0 := by
    have h : ((t : ℂ) ^ 2) = ((t * t : ℝ) : ℂ) := by rw [pow_two, ← Complex.ofReal_mul]
    rw [h, Complex.ofReal_im]
  funext i
  fin_cases i <;> simp [linVecC, ofComplex, hre, him]


/-- **Step 3.**  The plane `span {a, x}` misses the arc when `a` is not a multiple of any
`w t` and `x` is not in the cone `s • a + c • w t`. -/
theorem crNotMem_span_of_avoid (w : ℝ → Eucl 3) (hw : ∀ t : ℝ, w t ≠ 0) (a x : Eucl 3)
    (ha : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ∀ s : ℝ, s • w t ≠ a)
    (hx : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ∀ s c : ℝ, s • a + c • w t ≠ x) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, w t ∉ Submodule.span ℝ ({a, x} : Set (Eucl 3)) := by
  intro t ht hmem
  rw [Submodule.mem_span_pair] at hmem
  obtain ⟨μ, ν, hμν⟩ := hmem
  by_cases hν : ν = 0
  · rw [hν, zero_smul, add_zero] at hμν
    by_cases hμ : μ = 0
    · exact hw t (by rw [← hμν, hμ, zero_smul])
    · refine ha t ht μ⁻¹ ?_
      have h : μ⁻¹ • (μ • a) = μ⁻¹ • w t := by rw [← hμν]
      rw [smul_smul, inv_mul_cancel₀ hμ, one_smul] at h
      exact h.symm
  · have h1 : ν • x = w t - μ • a := by
      rw [← hμν]
      abel
    have h2 := congrArg (fun z : Eucl 3 => ν⁻¹ • z) h1
    rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hν, one_smul] at h2
    refine hx t ht (-(ν⁻¹ * μ)) ν⁻¹ ?_
    rw [h2]
    module


/-- The coordinate model sends `linVecC 1` to the first standard basis vector. -/
lemma euclCoordsT_linVecC_one : crEuclCoordsT (linVecC (1 : ℂ)) = Pi.single 0 1 := by
  show crEuclCoordsT (linVecC ((1 : ℝ) : ℂ)) = Pi.single 0 1
  rw [crEucEq_linVecC 1]; norm_num

/-- The coordinate model sends `linVecC 0` to the third standard basis vector. -/
lemma euclCoordsT_linVecC_zero : crEuclCoordsT (linVecC (0 : ℂ)) = Pi.single 2 1 := by
  show crEuclCoordsT (linVecC ((0 : ℝ) : ℂ)) = Pi.single 2 1
  rw [crEucEq_linVecC 0]; norm_num



/-! ## 1. Avoiding the cones over finitely many curves (Baire) -/

/-- **The cones over finitely many curves, avoided.**  For `C^∞` curves `W k` (`k : ι`, `ι` finite),
a centre `A₀` and any `ρ > 0` there is `a` within `ρ` of `A₀` which is not a real multiple of any
`W k t`, `t ∈ [-1,1]`.

The bad set is the countable union over `(k, m) : ι × ℕ` of the compact images of
`(s, t) ↦ s • W k t` over `closedBall 0 m ×ˢ Icc (-1) 1`; each piece has empty interior because it
is contained in the image of the same smooth map from the `2`-dimensional source `ℝ × ℝ` (a blow-up
of `ℝ²` into `Eucl 3 = ℝ⁴`), and a countable union of closed nowhere dense sets has empty interior
by Baire. -/
lemma exists_avoidCone_family_cr {ι : Type*} [Fintype ι] (W : ι → ℝ → Eucl 3)
    (hWc : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W k)) (A₀ : Eucl 3) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ a : Eucl 3, ‖a - A₀‖ < ρ ∧
      ∀ (k : ι) (t : ℝ), t ∈ Set.Icc (-1 : ℝ) 1 → ∀ s : ℝ, s • W k t ≠ a := by
  classical
  set F : ι × ℕ → Set (Eucl 3) := fun p =>
    (fun q : ℝ × ℝ => q.1 • W p.1 q.2) ''
      (Metric.closedBall (0 : ℝ) (p.2 : ℝ) ×ˢ Set.Icc (-1 : ℝ) 1) with hF
  have hclosed : ∀ p, IsClosed (F p) := by
    intro p
    have hcont : Continuous (fun q : ℝ × ℝ => q.1 • W p.1 q.2) := by
      have hk : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W p.1) := hWc p.1
      fun_prop
    rw [hF]
    exact (IsCompact.image_of_continuousOn
      ((isCompact_closedBall (0 : ℝ) (p.2 : ℝ)).prod isCompact_Icc) hcont.continuousOn).isClosed
  have hempty : ∀ p, interior (F p) = ∅ := by
    intro p
    have hk : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W p.1) := hWc p.1
    have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => q.1 • W p.1 q.2) := by
      fun_prop
    have h1 : interior ((fun q : ℝ × ℝ => q.1 • W p.1 q.2) ''
        (Set.univ ×ˢ Set.Icc (-1 : ℝ) 1)) = ∅ :=
      interior_image_empty_of_contDiffOn (E := ℝ × ℝ) (F := Eucl 3) (by simp)
        isOpen_univ hsm.contDiffOn (subset_univ _)
    rw [hF]
    exact Set.eq_empty_of_subset_empty
      ((interior_mono (Set.image_mono (Set.prod_mono (subset_univ _) Subset.rfl))).trans
        (le_of_eq h1))
  have hBad : interior (⋃ p, F p) = ∅ :=
    Work.Sard.wp.interior_eq_empty_iUnion_isClosed hclosed hempty
  have hdense : Dense ((⋃ p, F p))ᶜ := interior_eq_empty_iff_dense_compl.mp hBad
  obtain ⟨a, ha, haball⟩ := hdense.exists_mem_open Metric.isOpen_ball
    (Metric.nonempty_ball.mpr hρ)
  refine ⟨a, ?_, ?_⟩
  · have h := Metric.mem_ball.mp haball
    rwa [dist_eq_norm] at h
  · intro k t ht s hs
    have hmem : a ∈ ⋃ p, F p := by
      obtain ⟨m, hm⟩ := exists_nat_ge (max |s| |t|)
      refine Set.mem_iUnion.mpr ⟨(k, m), ?_⟩
      rw [hF]
      refine ⟨(s, t), ?_, hs⟩
      rw [Set.mem_prod]
      refine ⟨?_, ht⟩
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs]
      exact le_trans (le_max_left _ _) hm
    exact ha hmem

/-- **The planes through prescribed vectors and finitely many curves, avoided.**  For `C^∞` curves
`W k`, vectors `a k` (`k : ι`, `ι` finite), a centre `A₀` and any `ρ > 0` there is `x` within `ρ` of
`A₀` which is not of the form `s • a k + c • W k t` with `t ∈ [-1,1]`.

Same Baire argument; the pieces are compact images of the smooth map
`((s, c), t) ↦ s • a k + c • W k t` from the `3`-dimensional source `(ℝ × ℝ) × ℝ` into
`Eucl 3 = ℝ⁴`, so each has empty interior (`3 < 4`). -/
lemma exists_avoidPlane_family_cr {ι : Type*} [Fintype ι] (W : ι → ℝ → Eucl 3) (a : ι → Eucl 3)
    (hWc : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W k)) (A₀ : Eucl 3) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ x : Eucl 3, ‖x - A₀‖ < ρ ∧
      ∀ (k : ι) (t : ℝ), t ∈ Set.Icc (-1 : ℝ) 1 →
        ∀ s c : ℝ, s • a k + c • W k t ≠ x := by
  classical
  set F : ι × ℕ → Set (Eucl 3) := fun p =>
    (fun q : (ℝ × ℝ) × ℝ => q.1.1 • a p.1 + q.1.2 • W p.1 q.2) ''
      ((Metric.closedBall (0 : ℝ) (p.2 : ℝ) ×ˢ Metric.closedBall (0 : ℝ) (p.2 : ℝ))
        ×ˢ Set.Icc (-1 : ℝ) 1) with hF
  have hclosed : ∀ p, IsClosed (F p) := by
    intro p
    have hcont : Continuous (fun q : (ℝ × ℝ) × ℝ => q.1.1 • a p.1 + q.1.2 • W p.1 q.2) := by
      have hk : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W p.1) := hWc p.1
      fun_prop
    rw [hF]
    exact (IsCompact.image_of_continuousOn
      (((isCompact_closedBall (0 : ℝ) (p.2 : ℝ)).prod
        (isCompact_closedBall (0 : ℝ) (p.2 : ℝ))).prod isCompact_Icc)
      hcont.continuousOn).isClosed
  have hempty : ∀ p, interior (F p) = ∅ := by
    intro p
    have hk : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W p.1) := hWc p.1
    have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : (ℝ × ℝ) × ℝ => q.1.1 • a p.1 + q.1.2 • W p.1 q.2) := by
      fun_prop
    have h1 : interior ((fun q : (ℝ × ℝ) × ℝ => q.1.1 • a p.1 + q.1.2 • W p.1 q.2) ''
        (Set.univ ×ˢ Set.Icc (-1 : ℝ) 1)) = ∅ :=
      interior_image_empty_of_contDiffOn (E := (ℝ × ℝ) × ℝ) (F := Eucl 3) (by simp)
        isOpen_univ hsm.contDiffOn (subset_univ _)
    rw [hF]
    exact Set.eq_empty_of_subset_empty
      ((interior_mono (Set.image_mono (Set.prod_mono (subset_univ _) Subset.rfl))).trans
        (le_of_eq h1))
  have hBad : interior (⋃ p, F p) = ∅ :=
    Work.Sard.wp.interior_eq_empty_iUnion_isClosed hclosed hempty
  have hdense : Dense ((⋃ p, F p))ᶜ := interior_eq_empty_iff_dense_compl.mp hBad
  obtain ⟨x, hx, hxball⟩ := hdense.exists_mem_open Metric.isOpen_ball
    (Metric.nonempty_ball.mpr hρ)
  refine ⟨x, ?_, ?_⟩
  · have h := Metric.mem_ball.mp hxball
    rwa [dist_eq_norm] at h
  · intro k t ht s c hsc
    have hmem : x ∈ ⋃ p, F p := by
      obtain ⟨m, hm⟩ := exists_nat_ge (max (max |s| |c|) |t|)
      refine Set.mem_iUnion.mpr ⟨(k, m), ?_⟩
      rw [hF]
      refine ⟨((s, c), t), ?_, hsc⟩
      rw [Set.mem_prod, Set.mem_prod]
      refine ⟨⟨?_, ?_⟩, ht⟩
      · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs]
        exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
      · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs]
        exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
    exact hx hmem

/-- **The family form of `Work.Drive.notMem_span_of_avoid`**: if `a` is not a multiple of any
`W k t` and `x` is not in any of the planes `ℝ (a k) + ℝ (W k t)`, then no `W k t` lies in
`span {a k, x}`. -/
lemma notMem_span_of_avoid_family_cr {ι : Type*} (W : ι → ℝ → Eucl 3) (hW : ∀ k t, W k t ≠ 0)
    (a x : ι → Eucl 3)
    (ha : ∀ k t, t ∈ Set.Icc (-1 : ℝ) 1 → ∀ s : ℝ, s • W k t ≠ a k)
    (hx : ∀ k t, t ∈ Set.Icc (-1 : ℝ) 1 → ∀ s c : ℝ, s • a k + c • W k t ≠ x k) :
    ∀ k t, t ∈ Set.Icc (-1 : ℝ) 1 → W k t ∉ Submodule.span ℝ ({a k, x k} : Set (Eucl 3)) := by
  intro k t ht hmem
  rw [Submodule.mem_span_pair] at hmem
  obtain ⟨μ, ν, hμν⟩ := hmem
  by_cases hν : ν = 0
  · rw [hν, zero_smul, add_zero] at hμν
    by_cases hμ : μ = 0
    · exact hW k t (by rw [← hμν, hμ, zero_smul])
    · refine ha k t ht μ⁻¹ ?_
      have h : μ⁻¹ • (μ • a k) = μ⁻¹ • W k t := by rw [← hμν]
      rw [smul_smul, inv_mul_cancel₀ hμ, one_smul] at h
      exact h.symm
  · have h1 : ν • x k = W k t - μ • a k := by
      rw [← hμν]
      abel
    have h2 := congrArg (fun z : Eucl 3 => ν⁻¹ • z) h1
    rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hν, one_smul] at h2
    refine hx k t ht (-(ν⁻¹ * μ)) ν⁻¹ ?_
    rw [h2]
    module

/-! ## 2. The endomorphism of `Eucl 3` with three prescribed columns -/

/-- The endomorphism of `Fin 4 → ℝ` with columns `P`, `Q`, `R` and the last standard basis vector
`e₃`, i.e. the map with `(v ↦ (P i * v 0 + Q i * v 1 + R i * v 2 + [i = 3] * v 3) i)`. -/
def colsLin_cr (P Q R : Fin 4 → ℝ) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearMap.pi fun i : Fin 4 =>
    (P i) • LinearMap.proj 0 + (Q i) • LinearMap.proj 1 + (R i) • LinearMap.proj 2
      + (if i = 3 then (1:ℝ) else 0) • LinearMap.proj 3

lemma colsLin_apply_cr (P Q R : Fin 4 → ℝ) (v : Fin 4 → ℝ) (i : Fin 4) :
    colsLin_cr P Q R v i = P i * v 0 + Q i * v 1 + R i * v 2 + (if i = 3 then v 3 else 0) := by
  simp only [colsLin_cr, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The columns of `colsLin_cr P Q R`: the first three are `P`, `Q`, `R` and the fourth is `e₃`. -/
lemma colsLin_eq_cr (P Q R : Fin 4 → ℝ) (v : Fin 4 → ℝ) :
    colsLin_cr P Q R v = (v 0) • P + (v 1) • Q + (v 2) • R + (v 3) • Pi.single 3 1 := by
  funext i
  rw [colsLin_apply_cr]
  by_cases h : i = 3
  · subst h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, ↓reduceIte]
    ring
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne h, h, ↓reduceIte]
    ring

lemma pi_eq_sum_single_cr (v : Fin 4 → ℝ) :
    v = (v 0) • Pi.single 0 1 + (v 1) • Pi.single 1 1 + (v 2) • Pi.single 2 1
      + (v 3) • Pi.single 3 1 := by
  funext i
  fin_cases i <;> simp

/-- **The perturbation of `colsLin_cr` away from the identity, in coordinates**: subtracting the
identity only sees the first three columns. -/
lemma colsLin_sub_one_cr (P Q R : Fin 4 → ℝ) (w : Fin 4 → ℝ) :
    colsLin_cr P Q R w - w = (w 0) • (P - Pi.single 0 1) + (w 1) • (Q - Pi.single 1 1)
      + (w 2) • (R - Pi.single 2 1) := by
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [colsLin_apply_cr]
  fin_cases i <;> simp [Pi.single_eq_same, Pi.single_eq_of_ne] <;> ring

/-- The `Eucl 3` version of `colsLin_cr`: the linear map with columns `p`, `q`, `r`, `e₃`. -/
def colsLM_cr (p q r : Eucl 3) : Eucl 3 →ₗ[ℝ] Eucl 3 :=
  (crEuclCoordsT.symm : (Fin 4 → ℝ) →ₗ[ℝ] Eucl 3).comp
    ((colsLin_cr (crEuclCoordsT p) (crEuclCoordsT q) (crEuclCoordsT r)).comp
      (crEuclCoordsT : Eucl 3 →ₗ[ℝ] (Fin 4 → ℝ)))

lemma colsLM_apply_cr (p q r : Eucl 3) (v : Eucl 3) :
    colsLM_cr p q r v
      = crEuclCoordsT.symm (colsLin_cr (crEuclCoordsT p) (crEuclCoordsT q) (crEuclCoordsT r) (crEuclCoordsT v)) :=
  rfl

/-- `colsLM_cr` on a vector given in coordinates. -/
lemma colsLM_coords_cr (p q r : Eucl 3) (a : Fin 4 → ℝ) :
    colsLM_cr p q r (crEuclCoordsT.symm a)
      = (a 0) • p + (a 1) • q + (a 2) • r + (a 3) • crEuclCoordsT.symm (Pi.single 3 1) := by
  rw [colsLM_apply_cr]
  simp only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply,
    colsLin_eq_cr, map_add, map_smul]

lemma colsLM_eq_cr (p q r : Eucl 3) (v : Eucl 3) :
    colsLM_cr p q r v = (crEuclCoordsT v) 0 • p + (crEuclCoordsT v) 1 • q + (crEuclCoordsT v) 2 • r
      + (crEuclCoordsT v) 3 • crEuclCoordsT.symm (Pi.single 3 1) := by
  conv_lhs => rw [← ContinuousLinearEquiv.symm_apply_apply crEuclCoordsT v]
  exact colsLM_coords_cr p q r (crEuclCoordsT v)

lemma colsLM_linVecC_one_cr (p q r : Eucl 3) : colsLM_cr p q r (linVecC 1) = p := by
  rw [colsLM_eq_cr, euclCoordsT_linVecC_one]; simp

lemma colsLM_single_one_cr (p q r : Eucl 3) :
    colsLM_cr p q r (crEuclCoordsT.symm (Pi.single 1 1)) = q := by
  rw [colsLM_eq_cr]; simp

lemma colsLM_linVecC_zero_cr (p q r : Eucl 3) : colsLM_cr p q r (linVecC 0) = r := by
  rw [colsLM_eq_cr, euclCoordsT_linVecC_zero]; simp

/-- `colsLM_cr` coincides with the identity on the last coordinate direction. -/
lemma colsLM_single_three_cr (p q r : Eucl 3) :
    colsLM_cr p q r (crEuclCoordsT.symm (Pi.single 3 1)) = crEuclCoordsT.symm (Pi.single 3 1) := by
  rw [colsLM_eq_cr]; simp

/-- **The norm bound.**  The distance of `colsLM_cr p q r` from the identity is at most the sum of the
distances of the three prescribed columns from the corresponding standard columns. -/
lemma colsLM_norm_le_cr (p q r : Eucl 3) :
    ‖(LinearMap.toContinuousLinearMap (colsLM_cr p q r) : Eucl 3 →L[ℝ] Eucl 3) - 1‖ ≤
      ‖p - linVecC 1‖ + ‖q - crEuclCoordsT.symm (Pi.single 1 1)‖ + ‖r - linVecC 0‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  have hsub : ((LinearMap.toContinuousLinearMap (colsLM_cr p q r) : Eucl 3 →L[ℝ] Eucl 3) - 1) v
      = (crEuclCoordsT v) 0 • (p - linVecC 1)
        + (crEuclCoordsT v) 1 • (q - crEuclCoordsT.symm (Pi.single 1 1))
        + (crEuclCoordsT v) 2 • (r - linVecC 0) := by
    rw [show ((LinearMap.toContinuousLinearMap (colsLM_cr p q r) : Eucl 3 →L[ℝ] Eucl 3) - 1) v
        = colsLM_cr p q r v - v from by
      rw [sub_apply, LinearMap.coe_toContinuousLinearMap', one_apply_eq_self]]
    set a : Fin 4 → ℝ := crEuclCoordsT v with ha
    have hv : v = crEuclCoordsT.symm a := by
      rw [ha]; exact (ContinuousLinearEquiv.symm_apply_apply crEuclCoordsT v).symm
    rw [hv, colsLM_coords_cr]
    -- `eucl_coords` applied to `a`, without touching the `crEuclCoordsT.symm (single 3 1)`
    have hcoe : crEuclCoordsT.symm a
        = (a 0) • linVecC 1 + (a 1) • crEuclCoordsT.symm (Pi.single 1 1)
          + (a 2) • linVecC 0 + (a 3) • crEuclCoordsT.symm (Pi.single 3 1) := by
      conv_lhs => rw [pi_eq_sum_single_cr a]
      rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
        ← euclCoordsT_linVecC_one, ← euclCoordsT_linVecC_zero]
      simp
    rw [hcoe]
    simp only [smul_sub]
    abel
  rw [hsub]
  have hcoord : ∀ i : Fin 4, ‖(crEuclCoordsT v) i‖ ≤ ‖v‖ := by
    intro i
    have h1 : ‖(crEuclCoordsT v) i‖ ≤ ‖crEuclCoordsT v‖ := norm_le_pi_norm (crEuclCoordsT v) i
    have h2 : ‖crEuclCoordsT v‖ ≤ ‖v‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr (fun i => ?_)
      simpa using PiLp.norm_apply_le v i
    linarith
  have h0 : ‖(crEuclCoordsT v) 0 • (p - linVecC 1)‖ ≤ ‖v‖ * ‖p - linVecC 1‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hcoord 0) (norm_nonneg _)
  have h1 : ‖(crEuclCoordsT v) 1 • (q - crEuclCoordsT.symm (Pi.single 1 1))‖
      ≤ ‖v‖ * ‖q - crEuclCoordsT.symm (Pi.single 1 1)‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hcoord 1) (norm_nonneg _)
  have h2 : ‖(crEuclCoordsT v) 2 • (r - linVecC 0)‖ ≤ ‖v‖ * ‖r - linVecC 0‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hcoord 2) (norm_nonneg _)
  calc ‖(crEuclCoordsT v) 0 • (p - linVecC 1)
        + (crEuclCoordsT v) 1 • (q - crEuclCoordsT.symm (Pi.single 1 1))
        + (crEuclCoordsT v) 2 • (r - linVecC 0)‖
      ≤ ‖(crEuclCoordsT v) 0 • (p - linVecC 1)
          + (crEuclCoordsT v) 1 • (q - crEuclCoordsT.symm (Pi.single 1 1))‖
        + ‖(crEuclCoordsT v) 2 • (r - linVecC 0)‖ := norm_add_le _ _
    _ ≤ (‖(crEuclCoordsT v) 0 • (p - linVecC 1)‖
          + ‖(crEuclCoordsT v) 1 • (q - crEuclCoordsT.symm (Pi.single 1 1))‖)
        + ‖(crEuclCoordsT v) 2 • (r - linVecC 0)‖ := by
          have := norm_add_le ((crEuclCoordsT v) 0 • (p - linVecC 1))
            ((crEuclCoordsT v) 1 • (q - crEuclCoordsT.symm (Pi.single 1 1)))
          linarith
    _ ≤ (‖v‖ * ‖p - linVecC 1‖ + ‖v‖ * ‖q - crEuclCoordsT.symm (Pi.single 1 1)‖)
        + ‖v‖ * ‖r - linVecC 0‖ := by linarith
    _ = (‖p - linVecC 1‖ + ‖q - crEuclCoordsT.symm (Pi.single 1 1)‖ + ‖r - linVecC 0‖) * ‖v‖ := by
        ring

/-- **Injectivity from smallness.**  If the three prescribed columns are close enough to the
standard ones, `colsLM_cr p q r` is injective. -/
lemma colsLM_injective_cr {p q r : Eucl 3}
    (h : ‖p - linVecC 1‖ + ‖q - crEuclCoordsT.symm (Pi.single 1 1)‖ + ‖r - linVecC 0‖ < 1) :
    Function.Injective (colsLM_cr p q r) := by
  intro v v' hvv
  have hw : colsLM_cr p q r (v - v') = 0 := by rw [map_sub, hvv, sub_self]
  have hsub : v - v' = -(((LinearMap.toContinuousLinearMap (colsLM_cr p q r) : Eucl 3 →L[ℝ] Eucl 3) - 1)
      (v - v')) := by
    rw [sub_apply, LinearMap.coe_toContinuousLinearMap', one_apply_eq_self, hw]
    abel
  have hle : ‖v - v'‖ ≤ (‖p - linVecC 1‖ + ‖q - crEuclCoordsT.symm (Pi.single 1 1)‖
      + ‖r - linVecC 0‖) * ‖v - v'‖ := by
    have h1 : ‖v - v'‖ ≤ ‖(LinearMap.toContinuousLinearMap (colsLM_cr p q r) : Eucl 3 →L[ℝ] Eucl 3) - 1‖
        * ‖v - v'‖ := by
      calc ‖v - v'‖ = ‖-(((LinearMap.toContinuousLinearMap (colsLM_cr p q r) : Eucl 3 →L[ℝ] Eucl 3) - 1)
            (v - v'))‖ := by conv_lhs => rw [hsub]
        _ = ‖((LinearMap.toContinuousLinearMap (colsLM_cr p q r) : Eucl 3 →L[ℝ] Eucl 3) - 1) (v - v')‖ :=
            norm_neg _
        _ ≤ _ := ContinuousLinearMap.le_opNorm _ _
    calc ‖v - v'‖ ≤ _ := h1
      _ ≤ _ := mul_le_mul_of_nonneg_right (colsLM_norm_le_cr p q r) (norm_nonneg _)
  by_contra hne
  have hpos : 0 < ‖v - v'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hlt : ‖v - v'‖ < ‖v - v'‖ := by
    calc ‖v - v'‖ ≤ (‖p - linVecC 1‖ + ‖q - crEuclCoordsT.symm (Pi.single 1 1)‖
          + ‖r - linVecC 0‖) * ‖v - v'‖ := hle
      _ < 1 * ‖v - v'‖ := mul_lt_mul_of_pos_right h hpos
      _ = ‖v - v'‖ := one_mul _
  exact absurd hlt (lt_irrefl _)

/-! ## 3. The three coordinate permutations on the arc `linVecC` -/

lemma euclCoordsT_coordPermCLM_apply_cr (ρ : Equiv.Perm (Fin 4)) (x : Eucl 3) (j : Fin 4) :
    crEuclCoordsT (coordPermCLM ρ x) j = crEuclCoordsT x (ρ.symm j) := by
  rw [show crEuclCoordsT (coordPermCLM ρ x) j = (coordPermCLM ρ x) j from rfl, coordPermCLM_apply]
  rfl

lemma single_apply_symm_cr (ρ : Equiv.Perm (Fin 4)) (i : Fin 4) (j : Fin 4) :
    (Pi.single i (1:ℝ) : Fin 4 → ℝ) (ρ.symm j) = (Pi.single (ρ i) 1 : Fin 4 → ℝ) j := by
  rw [Pi.single_apply, Pi.single_apply]
  by_cases h : j = ρ i
  · subst h; simp
  · have h2 : ρ.symm j ≠ i := fun hh => h (by rw [← hh, Equiv.apply_symm_apply])
    simp [h, h2]

lemma linVecC_eq_cr (t : ℝ) :
    linVecC (t : ℂ) = crEuclCoordsT.symm (t • Pi.single 0 1 + (1 - t^2) • Pi.single 2 1) := by
  rw [show linVecC (t:ℂ) = crEuclCoordsT.symm (crEuclCoordsT (linVecC (t:ℂ))) from
    (ContinuousLinearEquiv.symm_apply_apply crEuclCoordsT (linVecC (t:ℂ))).symm, crEucEq_linVecC t]

lemma euclCoordsT_symm_apply_cr (X : Fin 4 → ℝ) (j : Fin 4) :
    crEuclCoordsT (crEuclCoordsT.symm X) j = X j := by
  rw [show crEuclCoordsT (crEuclCoordsT.symm X) j = (crEuclCoordsT (crEuclCoordsT.symm X)) j from rfl,
    ContinuousLinearEquiv.apply_symm_apply]

/-- `ρ 2 = 0` for the three coordinate permutations: the boundary circle of the disk model has
vanishing coordinate `2`, which each permutation moves to the coordinate `0`. -/
lemma coordPerms_two_eq_zero_cr (k : Fin 3) : (coordPerms k) 2 = 0 := by fin_cases k <;> decide
lemma coordPerms_val_zero_cr : (coordPerms 0) 0 = 2 := by decide
lemma coordPerms_val_one_cr : (coordPerms 1) 0 = 1 := by decide
lemma coordPerms_val_two_cr : (coordPerms 2) 0 = 1 := by decide
lemma coordPerms_val_cr (k : Fin 3) : (coordPerms k) 0 = ![2, 1, 1] k := by
  fin_cases k <;> decide
lemma coordPerms_val_ne_zero_cr (k : Fin 3) : (coordPerms k) 0 ≠ 0 := by
  fin_cases k <;> decide

/-- **The arc `f k (linVecC t)` in coordinates.**  Since `linVecC t = t • e₀ + (1 - t²) • e₂` and
`f k` permutes the coordinates with `(coordPerms k) 2 = 0`, the image of the arc is
`(1 - t²) • e₀ + t • e_{ρ k 0}`. -/
lemma coords_coordPermCLM_linVecC_cr (k : Fin 3) (t : ℝ) :
    crEuclCoordsT (coordPermCLM (coordPerms k) (linVecC (t : ℂ)))
      = (1 - t^2) • Pi.single 0 1 + t • Pi.single ((coordPerms k) 0) 1 := by
  funext j
  rw [euclCoordsT_coordPermCLM_apply_cr, linVecC_eq_cr, euclCoordsT_symm_apply_cr]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, single_apply_symm_cr, coordPerms_two_eq_zero_cr]
  ring

lemma symm_single_zero_cr : crEuclCoordsT.symm (Pi.single 0 1) = linVecC 1 := by
  rw [← euclCoordsT_linVecC_one, ContinuousLinearEquiv.symm_apply_apply]
lemma symm_single_two_cr : crEuclCoordsT.symm (Pi.single 2 1) = linVecC 0 := by
  rw [← euclCoordsT_linVecC_zero, ContinuousLinearEquiv.symm_apply_apply]

/-- **The value of `colsLM_cr p q r` on the arc `t ↦ f k (linVecC t)`.**  With `a := ![r, q, q]` this
is `(1 - t²) • p + t • a k`. -/
lemma colsLM_coordPerm_cr (p q r : Eucl 3) (k : Fin 3) (t : ℝ) :
    colsLM_cr p q r (coordPermCLM (coordPerms k) (linVecC (t : ℂ)))
      = (1 - t ^ 2) • p + t • (![r, q, q] : Fin 3 → Eucl 3) k := by
  have hv : ∀ k : Fin 3, coordPermCLM (coordPerms k) (linVecC (t:ℂ))
      = (1 - t^2) • crEuclCoordsT.symm (Pi.single 0 1)
        + t • crEuclCoordsT.symm (Pi.single ((coordPerms k) 0) 1) := by
    intro k
    apply crEuclCoordsT.injective
    rw [map_add, map_smul, map_smul, coords_coordPermCLM_linVecC_cr]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  obtain rfl | rfl | rfl := hk
  · rw [hv 0, map_add, map_smul, map_smul, symm_single_zero_cr, coordPerms_val_zero_cr, symm_single_two_cr,
      colsLM_linVecC_one_cr, colsLM_linVecC_zero_cr]
    simp
  · rw [hv 1, map_add, map_smul, map_smul, symm_single_zero_cr, coordPerms_val_one_cr, colsLM_linVecC_one_cr,
      colsLM_single_one_cr]
    simp
  · rw [hv 2, map_add, map_smul, map_smul, symm_single_zero_cr, coordPerms_val_two_cr, colsLM_linVecC_one_cr,
      colsLM_single_one_cr]
    simp

lemma span_pair_comm_cr (a b : Eucl 3) :
    Submodule.span ℝ ({a, b} : Set (Eucl 3)) = Submodule.span ℝ ({b, a} : Set (Eucl 3)) := by
  rw [Set.pair_comm]

/-! ## 4. The theorem -/

theorem exists_trans_avoid_negParallel_cr (w : Fin 3 → ℝ → Eucl 3)
    (hw : ∀ (k : Fin 3) (t : ℝ), w k t ≠ 0) (hwc : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (w k))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : Eucl 3 ≃L[ℝ] Eucl 3,
      ‖(A : Eucl 3 →L[ℝ] Eucl 3) - 1‖ < ε ∧
      ∀ (k : Fin 3) (t : ℝ), t ∈ Set.Icc (-1 : ℝ) 1 →
        ¬ ∃ lam : ℝ, lam < 0 ∧
          ((coordPermCLM (coordPerms k)).trans A) (linVecC (t : ℂ)) = lam • w k t := by
  -- the smallness parameter
  set ρ : ℝ := min (1/4) (ε/4) with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; exact lt_min (by norm_num) (by linarith)
  have hρ4 : ρ ≤ 1/4 := by rw [hρdef]; exact min_le_left _ _
  have hρ_one : 3 * ρ < 1 := by linarith
  have hρ_eps : 3 * ρ < ε := by
    have h : ρ ≤ ε / 4 := by rw [hρdef]; exact min_le_right _ _
    linarith
  -- the curve family `(w 1, w 2)` and the vector `q`
  have hW2c : ∀ k : Fin 2, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      ((![w 1, w 2] : Fin 2 → ℝ → Eucl 3) k) := by
    intro k
    fin_cases k
    · simpa using hwc 1
    · simpa using hwc 2
  obtain ⟨q, hq_ball, hq_avoid⟩ :=
    exists_avoidCone_family_cr (![w 1, w 2] : Fin 2 → ℝ → Eucl 3) hW2c
      (crEuclCoordsT.symm (Pi.single 1 1)) ρ hρ
  have hq1 : ∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 → ∀ s : ℝ, s • w 1 t ≠ q := by
    intro t ht s
    exact hq_avoid 0 t ht s
  have hq2 : ∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 → ∀ s : ℝ, s • w 2 t ≠ q := by
    intro t ht s
    exact hq_avoid 1 t ht s
  -- the vector `r` avoiding the cone over `w 0`
  obtain ⟨r, hr_ball, hr_avoid⟩ :=
    exists_avoidCone_family_cr (fun _ : Fin 1 => w 0) (fun _ => hwc 0) (linVecC 0) ρ hρ
  have hr0 : ∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 → ∀ s : ℝ, s • w 0 t ≠ r :=
    fun t ht s => hr_avoid 0 t ht s
  -- the vector `p` avoiding the three plane families
  obtain ⟨p, hp_ball, hp_avoid⟩ :=
    exists_avoidPlane_family_cr w (![r, q, q] : Fin 3 → Eucl 3) hwc (linVecC 1) ρ hρ
  have hp1 : ∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 → ∀ s c : ℝ, s • q + c • w 1 t ≠ p := by
    intro t ht s c
    exact hp_avoid 1 t ht s c
  have hp2 : ∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 → ∀ s c : ℝ, s • q + c • w 2 t ≠ p := by
    intro t ht s c
    exact hp_avoid 2 t ht s c
  have hp0 : ∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 → ∀ s c : ℝ, s • r + c • w 0 t ≠ p := by
    intro t ht s c
    exact hp_avoid 0 t ht s c
  -- smallness of the columns, and invertibility
  have hsmall : ‖p - linVecC 1‖ + ‖q - crEuclCoordsT.symm (Pi.single 1 1)‖ + ‖r - linVecC 0‖ < 1 := by
    linarith
  have hinj : Function.Injective (colsLM_cr p q r) := colsLM_injective_cr hsmall
  -- package the injective linear map as a continuous linear equivalence
  let φE : Eucl 3 ≃ₗ[ℝ] Eucl 3 := LinearEquiv.ofInjectiveEndo (colsLM_cr p q r) hinj
  have hφE : ∀ v, φE v = colsLM_cr p q r v := by
    intro v
    rw [LinearEquiv.coe_ofInjectiveEndo]
  have hcont : Continuous ⇑φE := by
    rw [LinearEquiv.coe_ofInjectiveEndo]
    exact (colsLM_cr p q r).continuous_of_finiteDimensional
  let φC : Eucl 3 ≃L[ℝ] Eucl 3 := φE.toContinuousLinearEquivOfContinuous hcont
  have hφC : ∀ v, φC v = colsLM_cr p q r v := by
    intro v
    rw [show φC v = φE v from rfl, hφE v]
  refine ⟨φC, ?_, ?_⟩
  · have hCLMeq : (φC : Eucl 3 →L[ℝ] Eucl 3) = LinearMap.toContinuousLinearMap (colsLM_cr p q r) := by
      apply ContinuousLinearMap.ext
      intro v
      rw [LinearMap.coe_toContinuousLinearMap']
      exact hφC v
    rw [hCLMeq]
    linarith [colsLM_norm_le_cr p q r, hp_ball, hq_ball, hr_ball, hρ_eps]
  · intro k t ht hbad
    obtain ⟨lam, hlam, hval⟩ := hbad
    -- the arc value of `φC`
    have harc : φC (coordPermCLM (coordPerms k) (linVecC (t : ℂ)))
        = (1 - t ^ 2) • p + t • (![r, q, q] : Fin 3 → Eucl 3) k := by
      rw [hφC, colsLM_coordPerm_cr]
    have h1 : (1 - t ^ 2) • p + t • (![r, q, q] : Fin 3 → Eucl 3) k = lam • w k t := by
      rw [← harc]
      have h := hval
      rw [ContinuousLinearEquiv.trans_apply] at h
      exact h
    have hmem : w k t ∈ Submodule.span ℝ ({p, (![r, q, q] : Fin 3 → Eucl 3) k} : Set (Eucl 3)) := by
      have hw' : w k t = lam⁻¹ • ((1 - t ^ 2) • p + t • (![r, q, q] : Fin 3 → Eucl 3) k) := by
        rw [h1, smul_smul, inv_mul_cancel₀ (ne_of_lt hlam), one_smul]
      rw [hw']
      refine Submodule.smul_mem _ _ (Submodule.add_mem _ ?_ ?_)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
    obtain rfl | rfl | rfl := hk
    · have hspan := crNotMem_span_of_avoid (w 0) (hw 0) r p hr0 hp0 t ht
      refine hspan ?_
      have h' : w 0 t ∈ Submodule.span ℝ ({p, r} : Set (Eucl 3)) := by simpa using hmem
      rwa [span_pair_comm_cr p r] at h'
    · have hspan := crNotMem_span_of_avoid (w 1) (hw 1) q p hq1 hp1 t ht
      refine hspan ?_
      have h' : w 1 t ∈ Submodule.span ℝ ({p, q} : Set (Eucl 3)) := by simpa using hmem
      rwa [span_pair_comm_cr p q] at h'
    · have hspan := crNotMem_span_of_avoid (w 2) (hw 2) q p hq2 hp2 t ht
      refine hspan ?_
      have h' : w 2 t ∈ Submodule.span ℝ ({p, q} : Set (Eucl 3)) := by simpa using hmem
      rwa [span_pair_comm_cr p q] at h'

end

end Work.Drive
