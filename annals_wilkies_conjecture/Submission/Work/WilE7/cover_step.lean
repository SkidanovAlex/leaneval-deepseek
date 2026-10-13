/-
  Area E7: the "cover step" of Binyamini–Vorobjov's effective fibre cutting.

  Given a `Good` stratum `S ⊆ ℝ^{p+q}` whose fibres `S_x` have dimension `q - S.j > 0`
  (hypothesis `S.j < q`), every point of `S` projects to a base point `x` over which either

  * the fibre of the fibrewise closure of `S.X.set` is strictly larger than the fibre of
    `S.X.set` itself (i.e. `x` lies in the projection of the fibrewise frontier), or
  * some fibre coordinate `y_l` has a critical point on the fibre of `S`.

  The proof is the extremal argument of BV Lemma 8: if `x` is *not* in the projection of the
  fibrewise frontier then the fibre `S_x` is closed in `ℝ^q`, hence compact, so any coordinate
  function `y_l` attains a maximum on it.  At a maximum point `y*`, the Good condition makes a
  neighbourhood of `y*` in `S_x` equal to the zero locus of `h`, and the Lagrange multiplier
  theorem (Mathlib's `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt`) shows that the
  derivative `e_l` of `y_l` is a linear combination of the derivatives `∂_y h_a`.  Since the
  Jacobian `∂_y h` has full rank `S.j` at `y*`, this linear relation is exactly the vanishing of
  all `(S.j+1)`-minors of `[∂_y h ; e_l]`, i.e. `(x, y*) ∈ critSet S l`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.FiberCutDefs
import Submission.Work.WilE5.Basic
import Submission.Work.WilE9.EaD.eaD_hasFDerivAt
import Submission.Work.WilE9.EaD.eaEval_contDiff
import Submission.Work.Strat.detOpSt_eq_zero_of_row_combination

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical Topology Filter
open scoped Topology Matrix

namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## Elementary helpers -/

/-- The linear map `y ↦ Fin.append 0 y`, i.e. the inclusion of the `q` fibre coordinates into
`ℝ^{p+q}`.  It is the linear part of the affine map `y ↦ Fin.append x y`. -/
private def cs_fibAppendCLM (p q : ℕ) : (Fin q → ℝ) →L[ℝ] (Fin (p + q) → ℝ) :=
  ContinuousLinearMap.pi fun s : Fin (p + q) =>
    Fin.append (fun _ : Fin p => (0 : (Fin q → ℝ) →L[ℝ] ℝ))
      (fun l : Fin q => (ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ)) s

@[simp] private theorem cs_fibAppendCLM_apply (p q : ℕ) (y : Fin q → ℝ) :
    cs_fibAppendCLM p q y = Fin.append (0 : Fin p → ℝ) y := by
  ext s
  refine Fin.addCases (fun i => ?_) (fun l => ?_) s <;>
    simp [cs_fibAppendCLM, ContinuousLinearMap.pi_apply]

/-- The affine map `y ↦ Fin.append x y` is strictly differentiable, with linear part
`cs_fibAppendCLM`. -/
private theorem cs_hasStrictFDerivAt_fibAppend (p q : ℕ) (x : Fin p → ℝ) (y₀ : Fin q → ℝ) :
    HasStrictFDerivAt (fun y : Fin q → ℝ => Fin.append x y) (cs_fibAppendCLM p q) y₀ := by
  have h1 : HasStrictFDerivAt (fun y : Fin q → ℝ => Fin.append x 0 + cs_fibAppendCLM p q y)
      (cs_fibAppendCLM p q) y₀ :=
    (cs_fibAppendCLM p q).hasStrictFDerivAt.const_add (Fin.append x (0 : Fin q → ℝ))
  have hfun : (fun y : Fin q → ℝ => Fin.append x 0 + cs_fibAppendCLM p q y)
      = fun y : Fin q → ℝ => Fin.append x y := by
    funext y
    ext s
    rw [Pi.add_apply, cs_fibAppendCLM_apply]
    refine Fin.addCases (fun i => ?_) (fun l => ?_) s <;> simp
  rwa [hfun] at h1

/-- Continuity of the affine map `y ↦ Fin.append x y`. -/
private theorem cs_continuous_finAppend (p q : ℕ) (x : Fin p → ℝ) :
    Continuous (fun y : Fin q → ℝ => Fin.append x y) :=
  continuous_iff_continuousAt.mpr fun y => (cs_hasStrictFDerivAt_fibAppend p q x y).continuousAt

/-- The derivative of `y ↦ eaEval c Q (Fin.append x y)` in the fibre directions. -/
private theorem cs_eaEval_fibAppend_hasStrictFDerivAt {p q r : ℕ} (c : EAChain (p + q) r)
    (Q : EAPoly (p + q) r) (x : Fin p → ℝ) (y₀ : Fin q → ℝ) :
    HasStrictFDerivAt (fun y : Fin q → ℝ => eaEval c Q (Fin.append x y))
      (∑ d : Fin q, eaEval c (eaD c (Fin.natAdd p d) Q) (Fin.append x y₀) •
        (ContinuousLinearMap.proj d : (Fin q → ℝ) →L[ℝ] ℝ)) y₀ := by
  set D : (Fin (p + q) → ℝ) →L[ℝ] ℝ :=
    ∑ i : Fin (p + q), eaEval c (eaD c i Q) (Fin.append x y₀) •
      (ContinuousLinearMap.proj i : (Fin (p + q) → ℝ) →L[ℝ] ℝ) with hD
  have heval : HasStrictFDerivAt (fun w : Fin (p + q) → ℝ => eaEval c Q w) D
      (Fin.append x y₀) := by
    refine ContDiffAt.hasStrictFDerivAt' (Work.WilE9.EaD.eaEval_contDiff c Q).contDiffAt ?_ ?_
    · simpa only [hD] using Work.WilE9.EaD.eaD_hasFDerivAt c Q (Fin.append x y₀)
    · simp
  have hcomp := heval.comp y₀ (cs_hasStrictFDerivAt_fibAppend p q x y₀)
  have hCLM : ContinuousLinearMap.comp D (cs_fibAppendCLM p q)
      = ∑ d : Fin q, eaEval c (eaD c (Fin.natAdd p d) Q) (Fin.append x y₀) •
          (ContinuousLinearMap.proj d : (Fin q → ℝ) →L[ℝ] ℝ) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, hD, Finset.sum_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      cs_fibAppendCLM_apply]
    rw [Fin.sum_univ_add]
    simp
  rwa [hCLM] at hcomp

/-- `eaEval` of a variable `X (Sum.inl i)`. -/
private theorem cs_eaEval_X_inl {k r : ℕ} (c : EAChain k r) (i : Fin k) (w : Fin k → ℝ) :
    eaEval c (MvPolynomial.X (Sum.inl i)) w = w i := by
  simp [eaEval]

/-- Evaluation of a "sum of scalars times coordinate functionals" on a basis vector. -/
private theorem cs_sum_smul_proj_apply_single {q : ℕ} (f : Fin q → ℝ) (d : Fin q) :
    (∑ d' : Fin q, f d' • (ContinuousLinearMap.proj d' : (Fin q → ℝ) →L[ℝ] ℝ))
      (Pi.single d 1) = f d := by
  rw [ContinuousLinearMap.sum_apply]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single d]
  · simp
  · intro d' _ hne
    simp [Pi.single_eq_of_ne hne]
  · intro hd
    exact absurd (Finset.mem_univ d) hd

/-! ## The fibre is closed over a base point outside the frontier projection -/

private theorem cs_fiber_isClosed {p q : ℕ} (X : Set (Fin (p + q) → ℝ)) (x : Fin p → ℝ)
    (h : x ∉ projFirst p q '' (fiberClosure X \ X)) : IsClosed (fiber X x) := by
  rw [← closure_subset_iff_isClosed]
  intro y hy
  change Fin.append x y ∈ X
  by_contra hyX
  refine h ⟨Fin.append x y, ⟨?_, hyX⟩, ?_⟩
  · show projSnd p q (Fin.append x y) ∈ closure (fiber X (projFirst p q (Fin.append x y)))
    rw [show projFirst p q (Fin.append x y) = x from by funext i; simp [projFirst, Fin.append_left],
      show projSnd p q (Fin.append x y) = y from by funext i; simp [projSnd, Fin.append_right]]
    exact hy
  · funext i
    simp [projFirst, Fin.append_left]

private theorem cs_cubeC_eq (q : ℕ) :
    cubeC q = Set.univ.pi (fun _ : Fin q => Set.Icc (-1 : ℝ) 1) := by
  ext y
  simp only [cubeC, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc,
    abs_le]

private theorem cs_fiber_subset_cubeC {p q : ℕ} (S : Stratum p q) (x : Fin p → ℝ) :
    fiber S.X.set x ⊆ cubeC q := by
  intro y hy
  have hy1 : Fin.append x y ∈ cubeC (p + q) := by
    have hy' : Fin.append x y ∈ S.X.set := hy
    rw [SemiPf.set, Set.mem_setOf_eq] at hy'
    exact hy'.1
  intro d
  have h2 : |(Fin.append x y) (Fin.natAdd p d)| ≤ 1 := by
    have hh := hy1
    rw [cubeC, Set.mem_setOf_eq] at hh
    exact hh (Fin.natAdd p d)
  rwa [Fin.append_right] at h2

/-! ## The Good condition, transported to the fibre -/

private theorem cs_eventually_mem_fiber {p q : ℕ} (S : Stratum p q) (hGood : S.Good)
    (x : Fin p → ℝ) (y : Fin q → ℝ) (hz : Fin.append x y ∈ S.X.set) :
    Filter.Eventually (fun y' : Fin q → ℝ =>
        (∀ a, eaEval S.X.c (S.h a) (Fin.append x y') = 0) → y' ∈ fiber S.X.set x)
      (nhds y) := by
  have hG := (hGood (Fin.append x y) hz).2.2
  have hcont : Continuous (fun y' : Fin q → ℝ => Fin.append x y') :=
    cs_continuous_finAppend p q x
  have h1 := (hcont.continuousAt (x := y)).eventually hG
  filter_upwards [h1] with y' hy'
  intro hzero
  exact hy' (by funext i; simp [projFirst, Fin.append_left]) hzero

/-! ## Full rank forces the transpose to be injective -/

private theorem cs_mulVec_transpose_eq_zero_of_rank {j q : ℕ} (M : Matrix (Fin j) (Fin q) ℝ)
    (hM : M.rank = j) (v : Fin j → ℝ) (hv : Matrix.mulVec (Matrix.transpose M) v = 0) :
    v = 0 := by
  have hrank : (Matrix.transpose M).rank = j := by rw [Matrix.rank_transpose, hM]
  have hker : Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (Matrix.transpose M))) = 0 := by
    have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin (Matrix.transpose M))
    rw [← Matrix.rank, hrank, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  have hbot : LinearMap.ker (Matrix.mulVecLin (Matrix.transpose M)) = ⊥ :=
    Submodule.finrank_eq_zero.mp hker
  have hmem : v ∈ LinearMap.ker (Matrix.mulVecLin (Matrix.transpose M)) := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact hv
  rw [hbot] at hmem
  exact (Submodule.mem_bot ℝ).mp hmem

/-! ## The cover step -/

theorem cover_step {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (hGood : S.Good) (hj : S.j < q) : WilkiesDesign.E.projFirst p q '' S.X.set ⊆ (WilkiesDesign.E.projFirst p q '' (WilkiesDesign.E.fiberClosure S.X.set \ S.X.set)) ∪ (⋃ l : Fin q, WilkiesDesign.E.projFirst p q '' (Work.WilE7.critSet S l).set) := by
  rintro x ⟨w, hw, rfl⟩
  by_cases hfront : projFirst p q w ∈ projFirst p q '' (fiberClosure S.X.set \ S.X.set)
  · exact Or.inl hfront
  · refine Or.inr ?_
    have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le S.j) hj
    let l : Fin q := ⟨0, hq⟩
    refine Set.mem_iUnion.mpr ⟨l, ?_⟩
    -- the fibre over `projFirst p q w` is closed, hence compact
    have hclosed : IsClosed (fiber S.X.set (projFirst p q w)) :=
      cs_fiber_isClosed S.X.set _ hfront
    have hbdd : fiber S.X.set (projFirst p q w) ⊆ cubeC q :=
      cs_fiber_subset_cubeC S _
    have hcompact : IsCompact (fiber S.X.set (projFirst p q w)) := by
      refine (isCompact_univ_pi (fun _ : Fin q => isCompact_Icc (a := (-1 : ℝ)) (b := 1))).of_isClosed_subset
        hclosed ?_
      simpa [cs_cubeC_eq] using hbdd
    have hne : (fiber S.X.set (projFirst p q w)).Nonempty := by
      refine ⟨projSnd p q w, ?_⟩
      show Fin.append (projFirst p q w) (projSnd p q w) ∈ S.X.set
      have happ : Fin.append (projFirst p q w) (projSnd p q w) = w := by
        funext i
        refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [projFirst, projSnd]
      rw [happ]
      exact hw
    obtain ⟨ys, hys_mem, hys_max⟩ :=
      hcompact.exists_isMaxOn hne (continuous_apply l).continuousOn
    -- the maximum point is our witness `z`
    set z : Fin (p + q) → ℝ := Fin.append (projFirst p q w) ys with hz
    have hzX : z ∈ S.X.set := by
      rw [hz]
      simpa [fiber] using hys_mem
    have hvan : ∀ a, eaEval S.X.c (S.h a) z = 0 := (hGood z hzX).1
    have hrank : (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
        eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (S.h a)) z).rank = S.j := (hGood z hzX).2.1
    have hgerm := cs_eventually_mem_fiber S hGood (projFirst p q w) ys (by rw [← hz]; exact hzX)
    have hmax : ∀ y' ∈ fiber S.X.set (projFirst p q w), y' l ≤ ys l :=
      fun y' hy' => isMaxOn_iff.mp hys_max y' hy'
    -- `ys` is a local maximum of `y_l` on the zero locus of `h`
    have hextr : IsLocalExtrOn
        (fun y : Fin q → ℝ =>
          eaEval S.X.c (MvPolynomial.X (Sum.inl (fibDir p q l))) (Fin.append (projFirst p q w) y))
        {y : Fin q → ℝ | ∀ a, eaEval S.X.c (S.h a) (Fin.append (projFirst p q w) y)
          = eaEval S.X.c (S.h a) (Fin.append (projFirst p q w) ys)} ys := by
      refine Or.inr ?_
      rw [IsMaxFilter, eventually_nhdsWithin_iff]
      filter_upwards [hgerm] with y' hy' hyS
      have hy0 : ∀ a, eaEval S.X.c (S.h a) (Fin.append (projFirst p q w) y') = 0 := by
        intro a
        rw [hyS a, ← hz, hvan a]
      have hmem : y' ∈ fiber S.X.set (projFirst p q w) := hy' hy0
      have hle : y' l ≤ ys l := hmax y' hmem
      simpa [eaEval, MvPolynomial.eval_X, fibDir, Fin.append_right] using hle
    -- the derivatives of the `h_a` and of `y_l` on the fibre
    set fa : Fin S.j → (Fin q → ℝ) →L[ℝ] ℝ :=
      fun a => ∑ d : Fin q,
        (eaEval S.X.c (eaD S.X.c (Fin.natAdd p d) (S.h a)) z) •
          (ContinuousLinearMap.proj d : (Fin q → ℝ) →L[ℝ] ℝ) with hfa
    set phi : (Fin q → ℝ) →L[ℝ] ℝ :=
      ∑ d : Fin q,
        (eaEval S.X.c (eaD S.X.c (Fin.natAdd p d) (MvPolynomial.X (Sum.inl (fibDir p q l)))) z) •
          (ContinuousLinearMap.proj d : (Fin q → ℝ) →L[ℝ] ℝ) with hphi
    have hfa_strict : ∀ a : Fin S.j, HasStrictFDerivAt
        (fun y : Fin q → ℝ => eaEval S.X.c (S.h a) (Fin.append (projFirst p q w) y))
        (fa a) ys := by
      intro a
      have h := cs_eaEval_fibAppend_hasStrictFDerivAt (p := p) (q := q) (r := S.X.r)
        S.X.c (S.h a) (projFirst p q w) ys
      simpa [hfa, hz] using h
    have hphi_strict : HasStrictFDerivAt
        (fun y : Fin q → ℝ =>
          eaEval S.X.c (MvPolynomial.X (Sum.inl (fibDir p q l))) (Fin.append (projFirst p q w) y))
        phi ys := by
      have h := cs_eaEval_fibAppend_hasStrictFDerivAt (p := p) (q := q) (r := S.X.r)
        S.X.c (MvPolynomial.X (Sum.inl (fibDir p q l))) (projFirst p q w) ys
      simpa [hphi, hz] using h
    -- Lagrange multipliers
    obtain ⟨Λ, Λ₀, hΛ, heq⟩ :=
      hextr.exists_multipliers_of_hasStrictFDerivAt hfa_strict hphi_strict
    have hfa_val : ∀ (a : Fin S.j) (d : Fin q),
        fa a (Pi.single d 1) = eaEval S.X.c (eaD S.X.c (Fin.natAdd p d) (S.h a)) z := by
      intro a d
      simp only [hfa]
      exact cs_sum_smul_proj_apply_single
        (fun d' => eaEval S.X.c (eaD S.X.c (Fin.natAdd p d') (S.h a)) z) d
    have hphi_val : ∀ d : Fin q,
        phi (Pi.single d 1)
          = eaEval S.X.c (eaD S.X.c (Fin.natAdd p d) (MvPolynomial.X (Sum.inl (fibDir p q l)))) z := by
      intro d
      simp only [hphi]
      exact cs_sum_smul_proj_apply_single
        (fun d' => eaEval S.X.c (eaD S.X.c (Fin.natAdd p d') (MvPolynomial.X (Sum.inl (fibDir p q l)))) z) d
    have heq_val : ∀ d : Fin q,
        (∑ a : Fin S.j, Λ a * eaEval S.X.c (eaD S.X.c (Fin.natAdd p d) (S.h a)) z)
          + Λ₀ * eaEval S.X.c (eaD S.X.c (Fin.natAdd p d) (MvPolynomial.X (Sum.inl (fibDir p q l)))) z
        = 0 := by
      intro d
      have h := congrArg (fun (L : (Fin q → ℝ) →L[ℝ] ℝ) => L (Pi.single d 1)) heq
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply, smul_eq_mul] at h
      simpa [hfa_val, hphi_val] using h
    -- the multiplier of `y_l` is non-zero (full rank of `∂_y h`)
    have hΛ₀ : Λ₀ ≠ 0 := by
      intro h0
      have hsum : (∑ a : Fin S.j, Λ a • fa a) = 0 := by
        have h := heq
        rw [h0, zero_smul, add_zero] at h
        exact h
      have hpt : ∀ d : Fin q,
          ∑ a : Fin S.j, Λ a * eaEval S.X.c (eaD S.X.c (Fin.natAdd p d) (S.h a)) z = 0 := by
        intro d
        have h := congrArg (fun (L : (Fin q → ℝ) →L[ℝ] ℝ) => L (Pi.single d 1)) hsum
        simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.zero_apply, smul_eq_mul] at h
        simpa [hfa_val] using h
      set M : Matrix (Fin S.j) (Fin q) ℝ :=
        Matrix.of fun (a : Fin S.j) (l : Fin q) =>
          eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (S.h a)) z with hM
      have hMrank : M.rank = S.j := by rw [hM]; exact hrank
      have hmv : Matrix.mulVec (Matrix.transpose M) Λ = 0 := by
        funext d
        rw [Matrix.mulVec_apply_eq_sum]
        simp only [Matrix.transpose_apply, hM, Matrix.of_apply]
        simpa [mul_comm] using hpt d
      have hzero : Λ = 0 := cs_mulVec_transpose_eq_zero_of_rank M hMrank Λ hmv
      exact hΛ (by simp [hzero, h0])
    -- the resulting row relation on the derivatives
    have hrow : ∀ d : Fin q,
        eaEval S.X.c (eaD S.X.c (Fin.natAdd p d) (MvPolynomial.X (Sum.inl (fibDir p q l)))) z
          = ∑ a : Fin S.j,
              (-(Λ₀)⁻¹ * Λ a) * eaEval S.X.c (eaD S.X.c (Fin.natAdd p d) (S.h a)) z := by
      intro d
      have h := heq_val d
      have h' : eaEval S.X.c (eaD S.X.c (Fin.natAdd p d)
            (MvPolynomial.X (Sum.inl (fibDir p q l)))) z
          = -(Λ₀)⁻¹ * (∑ a : Fin S.j,
              Λ a * eaEval S.X.c (eaD S.X.c (Fin.natAdd p d) (S.h a)) z) := by
        have h2 : Λ₀⁻¹ * ((∑ a : Fin S.j,
              Λ a * eaEval S.X.c (eaD S.X.c (Fin.natAdd p d) (S.h a)) z)
            + Λ₀ * eaEval S.X.c (eaD S.X.c (Fin.natAdd p d)
                (MvPolynomial.X (Sum.inl (fibDir p q l)))) z) = 0 := by
          rw [h, mul_zero]
        rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hΛ₀, one_mul] at h2
        linarith
      rw [h', neg_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    -- assemble: the maximum point is fibre-critical for `y_l`
    refine ⟨z, ?_, ?_⟩
    · rw [critSet_set]
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      refine ⟨hzX, fun σ => ?_⟩
      have hcrit := Work.Strat.eaEval_detOp_eq_zero_of_row_relation (p := p) (q := q) S.X.c S.h
        (fun b : Fin S.j => σ (Fin.castSucc b)) (MvPolynomial.X (Sum.inl (fibDir p q l))) z
        (σ (Fin.last S.j)) (fun a : Fin S.j => -(Λ₀)⁻¹ * Λ a)
        (fun d => by simpa [Work.WilE5.yDir] using hrow d)
      simpa only [critMinor, Work.WilE5.yDir, fibDir] using hcrit
    · rw [hz]
      funext i
      simp [projFirst, Fin.append_left]

end Work.WilE7
