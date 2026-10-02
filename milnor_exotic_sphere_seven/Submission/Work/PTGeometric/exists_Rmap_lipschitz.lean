import Mathlib
import Submission.Work.PTGeometric.grassmannianRetraction

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The retraction `Rmap` onto `Gr_k(ℝⁿ)` is Lipschitz near the Grassmannian

**Target.**  `Work.PTGeometric.exists_Rmap_lipschitz`: there is a constant `L` with

`‖Rmap A - P‖ ≤ L * ‖A - P‖`  whenever `P ∈ Gr n k` and `‖A - P‖ ≤ 1/8`.

**Where the statement sits.**  `Rmap A = Phi (symm A)` is the Riesz projection of the symmetrised
part of `A` (`RieszProj/Defs.lean`), and `good n k = ⋃_{P ∈ Gr n k} {A | ‖symm A - P‖ < 1/4}` is the
open set on which it is `C^∞` (`RieszProj/SmoothPhi.lean`).  The `1/8`-neighbourhood of the
Grassmannian is a *compact* subset of `good n k`, and `Rmap` fixes `Gr n k` pointwise, so the
statement is the standard "`C^1` on a neighbourhood of a compact set ⟹ Lipschitz there" argument,
with the mean value inequality applied along the *segment* from a point of `Gr n k` to `A`.

The proof has three parts.

* `Gr n k` is compact: it is closed (the conditions `P† = P`, `P * P = P`, `trace P = k` are closed;
  for the trace we use the orthonormal-basis formula `LinearMap.trace_eq_sum_inner`, which exhibits
  `trace` as a continuous sum of inner products) and bounded (`‖P‖ ≤ 1`, from
  `‖P‖ = ‖P† ∘SL P‖ = ‖P * P‖ = ‖P‖²`).
* The tube `rmapTube n k = Gr n k + closedBall 0 (1/8)` is compact and contained in `good n k`
  (because `symm` is a contraction and fixes the members of `Gr n k`); hence the continuous function
  `x ↦ ‖fderiv ℝ Rmap x‖` (continuous on `good n k` by `ContDiffOn.continuousOn_fderiv_of_isOpen`)
  is bounded on it.
* Given `P ∈ Gr n k` and `‖A - P‖ ≤ 1/8`, the segment `t ↦ P + t • (A - P)` stays in the tube, so
  `Rmap` is differentiable along it with derivative bounded by `L := max M 0`; the one-dimensional
  mean value inequality `norm_image_sub_le_of_norm_deriv_le_segment_01'` gives the claim.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Topology InnerProduct ContDiff
open Set Function MeasureTheory

namespace Work.PTGeometric

noncomputable section

variable {n k : ℕ}

/-! ## `Gr n k` is compact -/

/-- An orthogonal projection has operator norm at most `1`: since `P† ∘SL P = P * P = P`, the
identity `‖A† ∘SL A‖ = ‖A‖ * ‖A‖` forces `‖P‖ = ‖P‖ * ‖P‖`. -/
lemma norm_le_one_of_mem_Gr {P : EndOp n} (hP : P ∈ Gr n k) : ‖P‖ ≤ 1 := by
  have hc : P† ∘SL P = P := by
    rw [hP.1, ← ContinuousLinearMap.mul_def, hP.2.1]
  have hnorm : ‖P‖ = ‖P‖ * ‖P‖ := by
    rw [← ContinuousLinearMap.norm_adjoint_comp_self P, hc]
  nlinarith [norm_nonneg P]

/-- The trace, computed in an orthonormal basis of `ℝⁿ`, as a sum of inner products.  This is the
form in which the trace of an operator is visibly continuous. -/
lemma trace_eq_sum_orthoBasis (A : EndOp n) (b : OrthonormalBasis (Fin n) ℝ (Amb n)) :
    LinearMap.trace ℝ (Amb n) A = ∑ i : Fin n, inner ℝ (b i) (A (b i)) := by
  rw [LinearMap.trace_eq_sum_inner (A : Amb n →ₗ[ℝ] Amb n) b]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- `Gr n k` is closed.  The first two conditions are closed by continuity of the adjoint and of the
product; the trace condition is closed because in an orthonormal basis the trace is
`∑ i, ⟪b i, A (b i)⟫` (continuous in `A`). -/
lemma isClosed_Gr (n k : ℕ) : IsClosed (Gr n k) := by
  set b : OrthonormalBasis (Fin n) ℝ (Amb n) := EuclideanSpace.basisFun (Fin n) ℝ with hb
  have h1 : IsClosed {A : EndOp n | A† = A} := isClosed_eq continuous_adjoint_clm continuous_id
  have h2 : IsClosed {A : EndOp n | A * A = A} :=
    isClosed_eq (continuous_id.mul continuous_id) continuous_id
  have h3 : IsClosed {A : EndOp n | ∑ i : Fin n, inner ℝ (b i) (A (b i)) = (k : ℝ)} :=
    isClosed_eq (by fun_prop) continuous_const
  have heq : Gr n k = {A : EndOp n | A† = A} ∩ {A : EndOp n | A * A = A} ∩
      {A : EndOp n | ∑ i : Fin n, inner ℝ (b i) (A (b i)) = (k : ℝ)} := by
    ext A
    constructor
    · intro hA
      refine ⟨⟨hA.1, hA.2.1⟩, ?_⟩
      show ∑ i : Fin n, inner ℝ (b i) (A (b i)) = (k : ℝ)
      rw [← trace_eq_sum_orthoBasis A b]
      exact hA.2.2
    · rintro ⟨⟨hA1, hA2⟩, hA3⟩
      refine ⟨hA1, hA2, ?_⟩
      rw [trace_eq_sum_orthoBasis A b]
      exact hA3
  rw [heq]
  exact (h1.inter h2).inter h3

/-- `Gr n k` is compact: closed (above), and contained in the closed unit ball. -/
lemma isCompact_Gr (n k : ℕ) : IsCompact (Gr n k) := by
  refine (Metric.isCompact_iff_isClosed_bounded).mpr ⟨isClosed_Gr n k, ?_⟩
  refine (Metric.isBounded_closedBall (x := (0 : EndOp n)) (r := 1)).subset (fun P hP => ?_)
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_one_of_mem_Gr hP

/-- The retraction fixes the Grassmannian pointwise. -/
lemma Rmap_eq_self_of_mem_Gr {P : EndOp n} (hP : P ∈ Gr n k) : Rmap P = P := by
  rw [Rmap, symm_eq_self_of_mem_Gr hP, Phi_eq_self_of_mem_Gr hP (finrank_amb n)]

/-! ## The `1/8`-tube around the Grassmannian -/

/-- The `1/8`-neighbourhood of `Gr n k`, written as a Minkowski sum so that compactness is
immediate.  Membership means `x = P + v` with `P ∈ Gr n k` and `‖v‖ ≤ 1/8`, i.e.
`∃ P ∈ Gr n k, ‖x - P‖ ≤ 1/8`. -/
def rmapTube (n k : ℕ) : Set (EndOp n) :=
  (fun p : EndOp n × EndOp n => p.1 + p.2) '' (Gr n k ×ˢ Metric.closedBall (0 : EndOp n) (1 / 8))

lemma isCompact_rmapTube (n k : ℕ) : IsCompact (rmapTube n k) :=
  ((isCompact_Gr n k).prod (isCompact_closedBall (0 : EndOp n) (1 / 8))).image
    (continuous_fst.add continuous_snd)

/-- The tube is contained in `good n k`: for `x = P + v` with `P ∈ Gr n k` one has
`symm x - P = symm v` (as `symm` is additive and fixes `P`), of norm `≤ ‖v‖ ≤ 1/8 < 1/4`. -/
lemma rmapTube_subset_good (n k : ℕ) : rmapTube n k ⊆ good n k := by
  rintro x ⟨⟨P, v⟩, ⟨⟨hP, hv⟩, rfl⟩⟩
  rw [mem_good_iff]
  refine ⟨P, hP, ?_⟩
  have hv' : ‖v‖ ≤ 1 / 8 := by simpa [Metric.mem_closedBall, dist_zero_right] using hv
  have hsymm : symm (P + v) - P = symm v := by
    have h := symm_sub_symm (P + v) P
    rw [symm_eq_self_of_mem_Gr hP] at h
    have hsub : (P + v) - P = v := by abel
    rwa [hsub] at h
  rw [hsymm]
  have h1 : ‖symm v‖ ≤ ‖v‖ := norm_symm_le v
  linarith

/-- **The uniform derivative bound on the tube.**  `Rmap` is `C^∞` on the open set `good n k`
containing the compact tube, so `‖fderiv ℝ Rmap x‖` is bounded on the tube. -/
lemma exists_fderiv_Rmap_bound (n k : ℕ) :
    ∃ M : ℝ, ∀ x ∈ rmapTube n k, ‖fderiv ℝ (fun A : EndOp n => Rmap A) x‖ ≤ M := by
  have hcont : ContinuousOn (fun x : EndOp n => ‖fderiv ℝ (fun A : EndOp n => Rmap A) x‖)
      (rmapTube n k) :=
    (((contDiffOn_Rmap n k).continuousOn_fderiv_of_isOpen (isOpen_good n k) (by simp)).mono
      (rmapTube_subset_good n k)).norm
  obtain ⟨C, hC⟩ := (isCompact_rmapTube n k).exists_bound_of_continuousOn hcont
  refine ⟨C, fun x hx => ?_⟩
  have hnn : 0 ≤ ‖fderiv ℝ (fun A : EndOp n => Rmap A) x‖ :=
    norm_nonneg (fderiv ℝ (fun A : EndOp n => Rmap A) x)
  calc ‖fderiv ℝ (fun A : EndOp n => Rmap A) x‖
      = ‖‖fderiv ℝ (fun A : EndOp n => Rmap A) x‖‖ := (Real.norm_of_nonneg hnn).symm
    _ ≤ C := hC x hx

/-! ## The Lipschitz statement -/

theorem exists_Rmap_lipschitz (n k : ℕ) (hk : k ≤ n) :
    ∃ L : NNReal, ∀ A P : Work.PTGeometric.EndOp n,
      P ∈ Work.PTGeometric.Gr n k → ‖A - P‖ ≤ 1 / 8 →
      ‖Work.PTGeometric.Rmap A - P‖ ≤ (L : ℝ) * ‖A - P‖ := by
  classical
  obtain ⟨M, hM⟩ := exists_fderiv_Rmap_bound n k
  set L : NNReal := ⟨max M 0, le_max_right M 0⟩ with hL
  refine ⟨L, ?_⟩
  have hLcoe : (L : ℝ) = max M 0 := rfl
  intro A P hP hAP
  -- the segment from `P` to `A` stays in the tube
  set γ : ℝ → EndOp n := fun t => P + t • (A - P) with hγ
  have htube : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ rmapTube n k := by
    intro t ht
    refine ⟨(P, t • (A - P)), ⟨⟨hP, ?_⟩, rfl⟩⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    nlinarith [ht.2, norm_nonneg (A - P), hAP]
  -- differentiability along the segment, with the explicit derivative
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => Rmap (γ s))
      ((fderiv ℝ (fun X : EndOp n => Rmap X) (γ t)) (A - P)) t := by
    intro t ht
    have hmem := htube t ht
    have hgood : γ t ∈ good n k := rmapTube_subset_good n k hmem
    have hdiff : DifferentiableAt ℝ (fun X : EndOp n => Rmap X) (γ t) :=
      ((contDiffOn_Rmap n k).differentiableOn (by simp)).differentiableAt
        ((isOpen_good n k).mem_nhds hgood)
    have hγd : HasDerivAt γ (A - P) t := by
      have h1 : HasDerivAt (fun s : ℝ => P + s • (A - P)) (A - P) t := by
        simpa using (hasDerivAt_id t).smul_const (A - P) |>.const_add P
      simpa [hγ] using h1
    have h2 := hdiff.hasFDerivAt.comp_hasDerivAt t hγd
    simpa [Function.comp_def] using h2
  -- the derivative is bounded by the uniform constant
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖(fderiv ℝ (fun X : EndOp n => Rmap X) (γ t)) (A - P)‖ ≤ max M 0 * ‖A - P‖ := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, le_of_lt ht.2⟩
    have hmem := htube t htI
    have hle : ‖fderiv ℝ (fun X : EndOp n => Rmap X) (γ t)‖ ≤ max M 0 :=
      le_trans (hM _ hmem) (le_max_left _ _)
    calc ‖(fderiv ℝ (fun X : EndOp n => Rmap X) (γ t)) (A - P)‖
        ≤ ‖fderiv ℝ (fun X : EndOp n => Rmap X) (γ t)‖ * ‖A - P‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ max M 0 * ‖A - P‖ := by gcongr
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (f := fun s : ℝ => Rmap (γ s))
      (f' := fun t => (fderiv ℝ (fun X : EndOp n => Rmap X) (γ t)) (A - P))
      (C := max M 0 * ‖A - P‖) (fun t ht => (hderiv t ht).hasDerivWithinAt) hbound
  have h1 : γ 1 = A := by
    show P + (1 : ℝ) • (A - P) = A
    rw [show (1 : ℝ) • (A - P) = A - P from one_smul ℝ _]
    abel
  have h0 : γ 0 = P := by
    show P + (0 : ℝ) • (A - P) = P
    rw [show (0 : ℝ) • (A - P) = 0 from by ext x; simp, add_zero]
  rw [h1, h0, Rmap_eq_self_of_mem_Gr hP] at hmvt
  rw [hLcoe]
  exact hmvt

end

end Work.PTGeometric
