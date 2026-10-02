import Mathlib
import Submission.Work.PTGeometric.AmbientPerturbation
import Submission.Work.PTGeometric.GrRank
import Submission.Work.PTGeometric.isInvertible_comp_adjoint_iff
import Submission.Work.PTGeometric.existsCoordInjOnGr

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace Work.PTGeometric

open scoped Manifold ContDiff
open Function Set Topology

noncomputable section

variable {n k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
  [IsManifold (𝓡∂ ((8 + k) + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-! ### Auxiliary lemmas

No Hausdorff assumption on `M` is used anywhere in this file (the statement does not have one): the
cut-off that globalises the local frames is built from `‖P y - P x‖²`, which is a *smooth* function
because `P` is smooth, and it controls the operator norm of the Gram operator `L ∘ P y ∘ L†` through
the continuity of `L`. -/

/-- Units in the endomorphism ring of `ℝᵏ` are exactly the invertible maps. -/
theorem isUnit_iff_isInvertible_end (A : EndOp k) : IsUnit A ↔ A.IsInvertible := by
  constructor
  · intro h
    exact ⟨ContinuousLinearEquiv.ofUnit h.unit, h.unit_spec⟩
  · rintro ⟨e, rfl⟩
    exact ⟨ContinuousLinearEquiv.toUnit e, rfl⟩

/-- The set of invertible endomorphisms of `ℝᵏ` is open. -/
theorem isOpen_setOf_isInvertible_end : IsOpen {A : EndOp k | A.IsInvertible} := by
  have h : {A : EndOp k | A.IsInvertible} = {A | IsUnit A} := by
    ext A; exact (isUnit_iff_isInvertible_end A).symm
  rw [h]
  exact Units.isOpen

/-- The inverse family is smooth on the invertibility locus. -/
theorem contMDiffOn_inverse_end (Λ : M → EndOp k)
    (hΛ : ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, EndOp k) ((⊤ : ℕ∞) : WithTop ℕ∞) Λ) :
    ContMDiffOn (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, EndOp k) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => (Λ y).inverse) {y | (Λ y).IsInvertible} := by
  intro y hy
  have hinv : ContMDiffAt 𝓘(ℝ, EndOp k) 𝓘(ℝ, EndOp k) ((⊤ : ℕ∞) : WithTop ℕ∞)
      ContinuousLinearMap.inverse (Λ y) :=
    (contMDiffAt_iff_contDiffAt (𝕜 := ℝ)
      (f := fun A : EndOp k => ContinuousLinearMap.inverse A) (x := Λ y)).mpr
      (hy.contDiffAt_map_inverse)
  have hcomp : ContMDiffAt (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, EndOp k) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => ContinuousLinearMap.inverse (Λ z)) y := hinv.comp y (hΛ y)
  exact hcomp.contMDiffWithinAt

/-- A smooth cut-off times a function that is smooth on an open set containing the support closure
is smooth. -/
theorem contMDiff_smul_of_contMDiffOn_of_tsupport_subset_end
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {φ : M → ℝ} {f : M → E'} {s : Set M} {N : WithTop ℕ∞}
    (hs : IsOpen s) (hφ : ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, ℝ) N φ)
    (hf : ContMDiffOn (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, E') N f s)
    (hsub : tsupport φ ⊆ s) :
    ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, E') N (fun x => φ x • f x) := by
  have hsmul : ContMDiffOn (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, E') N (fun x => φ x • f x) s :=
    hφ.contMDiffOn.smul hf
  have hzero : ContMDiffOn (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, E') N (fun x => φ x • f x)
      (tsupport φ)ᶜ := by
    refine (contMDiffOn_const (c := (0 : E'))).congr (fun y hy => ?_)
    simp [image_eq_zero_of_notMem_tsupport hy]
  refine contMDiff_of_contMDiffOn_union_of_isOpen hsmul hzero ?_ hs
    (isClosed_tsupport φ).isOpen_compl
  rw [Set.eq_univ_iff_forall]
  intro x
  by_cases hx : x ∈ s
  · exact Or.inl hx
  · exact Or.inr fun h => hx (hsub h)


/-- **The operator norm of an endomorphism of `ℝᵏ` is bounded by the `ℓ²`-norm of its values on the
standard basis** (the finite-dimensional instance of the equivalence of norms on `End(ℝᵏ)`).  This is
what makes the cut-off of the frame construction *smooth*: the quantity
`∑ i, ‖(Λ y - Λ x) eᵢ‖²` is a sum of squares of inner products, hence smooth in `y`, while the
operator norm itself is not. -/
theorem opNorm_sq_le_sum_norm_sq_end (A : EndOp k) :
    ‖A‖ ^ 2 ≤ ∑ i : Fin k, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
  set hsq : ℝ := ∑ i : Fin k, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 with hsqdef
  have hsqnn : 0 ≤ hsq := Finset.sum_nonneg fun i _ => sq_nonneg _
  have key : ∀ v : Amb k, ‖A v‖ ≤ Real.sqrt hsq * ‖v‖ := by
    intro v
    have hAv : A v = ∑ i : Fin k, v.ofLp i • A (EuclideanSpace.single i (1 : ℝ)) := by
      conv_lhs => rw [← sum_smul_single_eq v]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
    have h1 : ‖A v‖ ≤ ∑ i : Fin k, |v.ofLp i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖ := by
      rw [hAv]
      calc ‖∑ i : Fin k, v.ofLp i • A (EuclideanSpace.single i (1 : ℝ))‖
          ≤ ∑ i : Fin k, ‖v.ofLp i • A (EuclideanSpace.single i (1 : ℝ))‖ := norm_sum_le _ _
        _ = ∑ i : Fin k, |v.ofLp i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖ :=
            Finset.sum_congr rfl fun i _ => by rw [norm_smul, Real.norm_eq_abs]
    have h2 : (∑ i : Fin k, |v.ofLp i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2
        ≤ (∑ i : Fin k, (v.ofLp i) ^ 2) * hsq := by
      have h3 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin k))
        (fun i => |v.ofLp i|) (fun i => ‖A (EuclideanSpace.single i (1 : ℝ))‖)
      simp only [sq_abs] at h3
      rw [hsqdef]
      simpa using h3
    have h4 : (∑ i : Fin k, (v.ofLp i) ^ 2) = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]
    have h5 : ‖A v‖ ^ 2 ≤ (Real.sqrt hsq * ‖v‖) ^ 2 := by
      have h6 := pow_le_pow_left₀ (norm_nonneg (A v)) h1 2
      calc ‖A v‖ ^ 2
          ≤ (∑ i : Fin k, |v.ofLp i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2 := h6
        _ ≤ (∑ i : Fin k, (v.ofLp i) ^ 2) * hsq := h2
        _ = ‖v‖ ^ 2 * hsq := by rw [h4]
        _ = (Real.sqrt hsq * ‖v‖) ^ 2 := by rw [mul_pow, Real.sq_sqrt hsqnn]; ring
    calc ‖A v‖ = Real.sqrt (‖A v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((Real.sqrt hsq * ‖v‖) ^ 2) := Real.sqrt_le_sqrt h5
      _ = Real.sqrt hsq * ‖v‖ := Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  have hA : ‖A‖ ≤ Real.sqrt hsq := ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) key
  calc ‖A‖ ^ 2 ≤ (Real.sqrt hsq) ^ 2 := pow_le_pow_left₀ (norm_nonneg A) hA 2
    _ = hsq := Real.sq_sqrt hsqnn

/-- **The local chart datum.**  If `L : ℝⁿ → ℝᵏ` is injective on the plane of `P x`, then there is an
open neighbourhood `U` of `x` on which `L` is still injective on the moving planes, carrying an
`L`-adapted frame `e` of those planes that is smooth on all of `M`.

The frame is `e j y = χ y • P y (L† ((Λ y)⁻¹ eⱼ))` where `Λ y = L ∘ P y ∘ L†` and the cut-off `χ` is
`1` near `x` and vanishes where `Λ` is far from `Λ x`.  The cut-off is built from
`ψ y = ∑ i, ‖(Λ y - Λ x) eᵢ‖²`, a *smooth* sum of squares (`Real.smoothTransition` of an affine
function of `ψ`), so no separation axiom on `M` is needed. -/
theorem exists_local_frame {P : M → EndOp n}
    (hP : ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, EndOp n) ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (hproj : ∀ x, P x ∈ Gr n k)
    (L : Amb n →L[ℝ] Amb k) (x : M)
    (hx : ∀ z : Amb n, P x z = z → L z = 0 → z = 0) :
    ∃ (U : Set M) (e : Fin k → M → Amb n),
      IsOpen U ∧ x ∈ U ∧ U ⊆ {y | ∀ z : Amb n, P y z = z → L z = 0 → z = 0} ∧
      (∀ j, ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Amb n) ((⊤ : ℕ∞) : WithTop ℕ∞) (e j)) ∧
      (∀ j y, y ∈ U → P y (e j y) = e j y) ∧
      (∀ y ∈ U, ∀ t : Amb k,
        L ((Finset.univ : Finset (Fin k)).sum fun j => t j • e j y) = t) := by
  classical
  -- the Gram operator `Λ y = L ∘ P y ∘ L†`
  let Λ : M → EndOp k := fun y => L.comp ((P y).comp L.adjoint)
  have hΛfun : ∀ y : M, Λ y = L.comp ((P y).comp L.adjoint) := fun y => rfl
  have hΛsm : ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, EndOp k) ((⊤ : ℕ∞) : WithTop ℕ∞) Λ :=
    (contMDiff_const (𝕜 := ℝ) (I := 𝓡∂ ((8 + k) + 1))
      (I' := 𝓘(ℝ, Amb n →L[ℝ] Amb k)) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (c := L)).clm_comp
      (hP.clm_comp contMDiff_const)
  have hxinv : (Λ x).IsInvertible := by
    rw [hΛfun x]
    exact (isInvertible_comp_adjoint_iff L (P x) (hproj x)).mpr hx
  -- a ball around `Λ x` on which invertibility persists
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ y : M, ‖Λ y - Λ x‖ < δ → (Λ y).IsInvertible := by
    obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp isOpen_setOf_isInvertible_end (Λ x) hxinv
    refine ⟨δ, hδpos, fun y hy => hδ ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    exact hy
  set a : ℝ := δ ^ 2 / 4 with hadef
  set b : ℝ := δ ^ 2 / 2 with hbdef
  have hapos : 0 < a := by rw [hadef]; positivity
  have hba : 0 < b - a := by rw [hadef, hbdef]; linarith [sq_pos_of_pos hδpos]
  -- the control function `ψ` and the cut-off `χ`
  set ψ : M → ℝ := fun y => ∑ i : Fin k, ‖(Λ y - Λ x) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
    with hψdef
  have hψsm : ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := by
    rw [hψdef]
    have hterm : ∀ i : Fin k, ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : M => ‖(Λ y - Λ x) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
      intro i
      have hf : ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Amb k) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : M => (Λ y - Λ x) (EuclideanSpace.single i (1 : ℝ))) :=
        (hΛsm.sub contMDiff_const).clm_apply
          (contMDiff_const (c := EuclideanSpace.single i (1 : ℝ)))
      have hg : ContMDiff 𝓘(ℝ, Amb k) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun v : Amb k => ‖v‖ ^ 2) := by
        have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : Amb k => inner ℝ v v) :=
          ContDiff.inner (𝕜 := ℝ) contDiff_id contDiff_id
        have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : Amb k => ‖v‖ ^ 2) := by
          simpa only [real_inner_self_eq_norm_sq] using h2
        exact h3.contMDiff
      exact hg.comp hf
    exact ContMDiff.sum (𝕜 := ℝ) (I := 𝓘(ℝ, ℝ)) (I' := 𝓡∂ ((8 + k) + 1))
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (fun i _ => hterm i)
  have hψle : ∀ y : M, ‖Λ y - Λ x‖ ^ 2 ≤ ψ y := by
    intro y
    rw [hψdef]
    exact opNorm_sq_le_sum_norm_sq_end (Λ y - Λ x)
  have hψlt_imp : ∀ y : M, ψ y < a → ‖Λ y - Λ x‖ < δ := by
    intro y hy
    have h4 : ‖Λ y - Λ x‖ ^ 2 < δ ^ 2 / 4 := by
      rw [hadef] at hy
      exact lt_of_le_of_lt (hψle y) hy
    nlinarith [norm_nonneg (Λ y - Λ x), hδpos]
  let χ : M → ℝ := fun y => Real.smoothTransition ((b - ψ y) / (b - a))
  have hχsm : ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) χ := by
    have h1 : ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : M => (b - ψ y) / (b - a)) :=
      (contMDiff_const.sub hψsm).div_const (b - a)
    exact Real.smoothTransition.contDiff.contMDiff.comp h1
  have hχone : ∀ y : M, ψ y ≤ a → χ y = 1 := by
    intro y hy
    have h1 : (1 : ℝ) ≤ (b - ψ y) / (b - a) := by
      rw [le_div_iff₀ hba]
      linarith
    exact Real.smoothTransition.one_of_one_le h1
  have hχzero : ∀ y : M, b ≤ ψ y → χ y = 0 := by
    intro y hy
    exact Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hba))
  -- the frame
  let e : Fin k → M → Amb n :=
    fun j y => χ y • P y (L.adjoint ((Λ y).inverse (EuclideanSpace.single j (1 : ℝ))))
  have heval : ∀ (j : Fin k) (y : M),
      e j y = χ y • P y (L.adjoint ((Λ y).inverse (EuclideanSpace.single j (1 : ℝ)))) :=
    fun j y => rfl
  refine ⟨{y : M | ψ y < a}, e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isOpen_lt hψsm.continuous continuous_const
  · have h0 : ψ x = 0 := by rw [hψdef]; simp
    show ψ x < a
    rw [h0]; exact hapos
  · intro y hy z hz h0
    have hinv : (Λ y).IsInvertible := hδ y (hψlt_imp y hy)
    refine (isInvertible_comp_adjoint_iff L (P y) (hproj y)).mp ?_ z hz h0
    simpa only [hΛfun y] using hinv
  · intro j
    show ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Amb n) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M => χ y • P y (L.adjoint ((Λ y).inverse (EuclideanSpace.single j (1 : ℝ)))))
    refine contMDiff_smul_of_contMDiffOn_of_tsupport_subset_end (k := k) (M := M)
      (s := {y : M | (Λ y).IsInvertible}) ?_ hχsm ?_ ?_
    · exact isOpen_setOf_isInvertible_end.preimage hΛsm.continuous
    · have h1 : ContMDiffOn (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, EndOp k) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y => (Λ y).inverse) {y : M | (Λ y).IsInvertible} :=
        contMDiffOn_inverse_end Λ hΛsm
      have h2 : ContMDiffOn (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Amb k) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y => (Λ y).inverse (EuclideanSpace.single j (1 : ℝ)))
          {y : M | (Λ y).IsInvertible} :=
        h1.clm_apply contMDiffOn_const
      have h3 : ContMDiffOn (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Amb n) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y => L.adjoint ((Λ y).inverse (EuclideanSpace.single j (1 : ℝ))))
          {y : M | (Λ y).IsInvertible} :=
        L.adjoint.contMDiff.comp_contMDiffOn h2
      exact hP.contMDiffOn.clm_apply h3
    · have h1 : support χ ⊆ {y : M | ψ y < b} := by
        intro y hy
        by_contra hc
        exact hy (hχzero y (le_of_not_gt hc))
      refine (closure_mono h1).trans ?_
      refine (closure_minimal (fun y hy => le_of_lt hy)
        (isClosed_le hψsm.continuous continuous_const)).trans ?_
      intro y hy
      apply hδ y
      have h3 : ‖Λ y - Λ x‖ ^ 2 ≤ δ ^ 2 / 2 := by
        rw [← hbdef]
        exact le_trans (hψle y) hy
      nlinarith [norm_nonneg (Λ y - Λ x), hδpos]
  · intro j y hy
    rw [heval j y, hχone y (le_of_lt (show ψ y < a from hy)), one_smul,
      mem_Gr_apply_apply (hproj y)]
  · intro y hy t
    have hχ1 : χ y = 1 := hχone y (le_of_lt (show ψ y < a from hy))
    have hyinv : (Λ y).IsInvertible := hδ y (hψlt_imp y hy)
    show L ((Finset.univ : Finset (Fin k)).sum fun j => t j • e j y) = t
    have hstep : ∀ j : Fin k, L (t j • e j y) = t j • EuclideanSpace.single j (1 : ℝ) := by
      intro j
      rw [heval j y, hχ1, one_smul, map_smul]
      congr 1
      show (Λ y) ((Λ y).inverse (EuclideanSpace.single j (1 : ℝ))) = EuclideanSpace.single j (1 : ℝ)
      rw [hΛfun y]
      exact ContinuousLinearMap.IsInvertible.self_apply_inverse hyinv _
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun j _ => hstep j)]
    rw [sum_smul_single_eq t]

/-- **The chart family of a projection-valued map, refined by a prescribed family.**  The main theorem
of this file: given a finite family `(ell j, U j, pt j)` of "prescribed charts" — open sets `U j`, a
point `pt j ∈ U j` and a linear coordinate `ell j` injective on the moving planes over `U j` — there is
a full chart family `C : AmbCharts n k M P m'` for the compact source `M` which *contains* each
prescribed chart, shrunk to a neighbourhood of `pt j` inside `U j`. -/
theorem nonempty_ambCharts_of_family {n k : ℕ} (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M] [IsManifold (𝓡∂ ((8 + k) + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) M] [CompactSpace M] {P : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)} (hP : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) P) (hproj : ∀ x, P x ∈ Work.PTGeometric.Gr n k) (m : ℕ) (ell : Fin m → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k)) (U : Fin m → Set M) (pt : Fin m → M) (hUopen : ∀ j, IsOpen (U j)) (hpt : ∀ j, pt j ∈ U j) (hinj : ∀ j y, y ∈ U j → ∀ z : EuclideanSpace ℝ (Fin n), P y z = z → ell j z = 0 → z = 0) : ∃ m' : ℕ, ∃ C : Work.PTGeometric.AmbCharts n k M P m', ∀ j : Fin m, ∃ l : Fin m', C.ell l = ell j ∧ pt j ∈ C.U l ∧ C.U l ⊆ U j := by
  classical
  -- ### a local frame around every point of `M`
  have hlocal : ∀ x : M, ∃ (Lx : Amb n →L[ℝ] Amb k) (Ux : Set M) (ex : Fin k → M → Amb n),
      IsOpen Ux ∧ x ∈ Ux ∧
      Ux ⊆ {y | ∀ z : Amb n, P y z = z → Lx z = 0 → z = 0} ∧
      (∀ j, ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Amb n) ((⊤ : ℕ∞) : WithTop ℕ∞) (ex j)) ∧
      (∀ j y, y ∈ Ux → P y (ex j y) = ex j y) ∧
      (∀ y ∈ Ux, ∀ t : Amb k,
        Lx ((Finset.univ : Finset (Fin k)).sum fun j => t j • ex j y) = t) := by
    intro x
    obtain ⟨Lx, hLx⟩ := existsCoordInjOnGr (P x) (hproj x)
    obtain ⟨Ux, ex, h1, h2, h3, h4, h5, h6⟩ := exists_local_frame hP hproj Lx x hLx
    exact ⟨Lx, Ux, ex, h1, h2, h3, h4, h5, h6⟩
  choose Lx Ux ex hUxopen hxmem hUxsub hUxsm hUxmem' hUxframe using hlocal
  -- ### a finite subcover of `M`
  have hcoverM : (univ : Set M) ⊆ ⋃ x : M, Ux x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hxmem x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : M => Ux x) hUxopen hcoverM
  -- ### the prescribed charts, shrunk inside the `U j`
  have hgiven : ∀ j : Fin m, ∃ (Uj : Set M) (ej : Fin k → M → Amb n),
      IsOpen Uj ∧ pt j ∈ Uj ∧ Uj ⊆ U j ∧
      (∀ y ∈ Uj, ∀ z : Amb n, P y z = z → ell j z = 0 → z = 0) ∧
      (∀ i, ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Amb n) ((⊤ : ℕ∞) : WithTop ℕ∞) (ej i)) ∧
      (∀ i y, y ∈ Uj → P y (ej i y) = ej i y) ∧
      (∀ y ∈ Uj, ∀ s : Amb k,
        ell j ((Finset.univ : Finset (Fin k)).sum fun i => s i • ej i y) = s) := by
    intro j
    obtain ⟨Uj, ej, h1, h2, h3, h4, h5, h6⟩ :=
      exists_local_frame hP hproj (ell j) (pt j) (fun z hz => hinj j (pt j) (hpt j) z hz)
    exact ⟨Uj ∩ U j, ej, h1.inter (hUopen j), ⟨h2, hpt j⟩, Set.inter_subset_right,
      fun y hy => h3 hy.1, h4, fun i y hy => h5 i y hy.1, fun y hy s => h6 y hy.1 s⟩
  choose Uj ej hUjopen hUjmem hUjsub hUjinj hUjsm hUjmem' hUjframe using hgiven
  -- ### the index embedding of the finite cover
  let idx : Fin t.card → M := fun i => ((Finset.equivFin t).symm i : t).1
  have hidx : ∀ (y : M) (hy : y ∈ t), idx ((Finset.equivFin t) ⟨y, hy⟩) = y := by
    intro y hy
    simp [idx]
  -- ### the assembled family
  refine ⟨t.card + m, ?_, ?_⟩
  · refine ⟨fun l => Sum.elim (fun i : Fin t.card => Lx (idx i)) ell (finSumFinEquiv.symm l),
      fun l => Sum.elim (fun i : Fin t.card => Ux (idx i)) Uj (finSumFinEquiv.symm l),
      fun l => Sum.elim (fun i : Fin t.card => ex (idx i)) ej (finSumFinEquiv.symm l),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l
      cases h : finSumFinEquiv.symm l with
      | inl i => exact hUxopen (idx i)
      | inr j => exact hUjopen j
    · intro x
      have hx : x ∈ ⋃ y ∈ t, Ux y := ht (mem_univ x)
      rcases Set.mem_iUnion.mp hx with ⟨y, hy⟩
      rcases Set.mem_iUnion.mp hy with ⟨hyt, hxy⟩
      refine ⟨finSumFinEquiv (Sum.inl ((Finset.equivFin t) ⟨y, hyt⟩)), ?_⟩
      show x ∈ Sum.elim (fun i : Fin t.card => Ux (idx i)) Uj
        (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl ((Finset.equivFin t) ⟨y, hyt⟩))))
      rw [Equiv.symm_apply_apply]
      simpa only [Sum.elim_inl, hidx y hyt] using hxy
    · intro l j
      cases h : finSumFinEquiv.symm l with
      | inl i => exact hUxsm (idx i) j
      | inr i => exact hUjsm i j
    · intro l y hy z hz h0
      cases h : finSumFinEquiv.symm l with
      | inl i =>
        rw [h] at hy h0
        exact hUxsub (idx i) hy z hz h0
      | inr i =>
        rw [h] at hy h0
        exact hUjinj i y hy z hz h0
    · intro l j y hy
      cases h : finSumFinEquiv.symm l with
      | inl i =>
        rw [h] at hy
        exact hUxmem' (idx i) j y hy
      | inr i =>
        rw [h] at hy
        exact hUjmem' i j y hy
    · intro l y hy t
      cases h : finSumFinEquiv.symm l with
      | inl i =>
        rw [h] at hy
        exact hUxframe (idx i) y hy t
      | inr i =>
        rw [h] at hy
        exact hUjframe i y hy t
  · intro j
    refine ⟨finSumFinEquiv (Sum.inr j), ?_, ?_, ?_⟩
    · show Sum.elim (fun i : Fin t.card => Lx (idx i)) ell
        (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j))) = ell j
      rw [Equiv.symm_apply_apply]
      rfl
    · show pt j ∈ Sum.elim (fun i : Fin t.card => Ux (idx i)) Uj
        (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j)))
      rw [Equiv.symm_apply_apply]
      exact hUjmem j
    · show Sum.elim (fun i : Fin t.card => Ux (idx i)) Uj
        (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j))) ⊆ U j
      rw [Equiv.symm_apply_apply]
      exact hUjsub j

end

end Work.PTGeometric
