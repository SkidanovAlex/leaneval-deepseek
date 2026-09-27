import Mathlib
import Submission.Work.Drive.Whitney.whitneyDiscDefs
import Submission.Work.Drive.Whitney.dimH_badAvoid
import Submission.Work.Drive.Whitney.dimH_badInj
import Submission.Work.Drive.Whitney.dimH_badTransBot
import Submission.Work.Drive.Whitney.dimH_badTransTop
import Submission.Work.Projection.dimH_image_le_of_contDiffOn

/-!
# The smooth Whitney disc of a bigon

The target of this file is `Work.Drive.Whitney.whitneyDiscSmooth`: for a smooth immersion
`f : M^n → ℝ^{2n}` (`n ≥ 3`) of a compact manifold and two smooth arcs `γ₁, γ₂` whose `f`-images
meet only at the two common endpoints, there is a smooth disc on `[-1,1] × [0,1]` with the two arcs
as its horizontal edges, constant on the vertical edges, injective on the open square, whose
interior misses `f '' M`, and which is transverse to `f '' M` along the two edges.

The disc is built as `D v = baseDisc + ∑ k, (discBump k) • v k` (see
`Submission.Work.Drive.Whitney.whitneyDiscDefs`) for a translation parameter `v` chosen outside the
four "bad sets" `badAvoid`, `badInj`, `badTransBot`, `badTransTop`, each of which has Hausdorff
dimension `< 8n` in the parameter space `(Fin 2 × Fin 2) → ℝ^{2n}`.
-/

namespace Work.Drive.Whitney

open scoped Manifold ContDiff ENNReal Topology
open Set Metric

noncomputable section

variable {n : ℕ}

lemma contDiff_sigR :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sigR : ℝ → ℝ) := by
  unfold sigR; fun_prop

/-- The composite `x ↦ f (γ (sigR x))` is smooth. -/
lemma contDiff_arcComp {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ : ℝ → M)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hγ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => f (γ (sigR x))) := by
  have h1 : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) (sigR : ℝ → ℝ) := contDiff_sigR.contMDiff
  exact ((hf.comp hγ).comp h1).contDiff

/-- The candidate disc `discMap f γ₁ γ₂ v` is smooth. -/
lemma contDiff_discMap {M : Type*} (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M)
    (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n)))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => f (γ₁ (sigR x))))
    (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => f (γ₂ (sigR x)))) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (discMap f γ₁ γ₂ v) := by
  rw [show discMap f γ₁ γ₂ v = fun p : ℝ × ℝ =>
      (1 - p.2) • f (γ₁ (sigR p.1)) + p.2 • f (γ₂ (sigR p.1))
        + ∑ k : Fin 2 × Fin 2, (discBump k p) • v k from rfl]
  have h₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => f (γ₁ (sigR p.1))) :=
    hA.comp contDiff_fst
  have h₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => f (γ₂ (sigR p.1))) :=
    hB.comp contDiff_fst
  have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => ∑ k : Fin 2 × Fin 2, (discBump k p) • v k) :=
    ContDiff.sum fun k _ => (contDiff_discBump k).smul contDiff_const
  have h4 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (1 - p.2) • f (γ₁ (sigR p.1)) + p.2 • f (γ₂ (sigR p.1))) :=
    (((contDiff_const.sub contDiff_snd).smul h₁).add (contDiff_snd.smul h₂))
  exact h4.add h3

lemma differentiableAt_discMap {M : Type*} (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (γ₁ γ₂ : ℝ → M) (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) (p : ℝ × ℝ)
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => f (γ₁ (sigR x))))
    (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => f (γ₂ (sigR x)))) :
    DifferentiableAt ℝ (discMap f γ₁ γ₂ v) p :=
  (contDiff_discMap f γ₁ γ₂ v hA hB).differentiable (by simp) |>.differentiableAt

/-! ## The boundary values of the candidate disc -/

lemma discMap_bot {M : Type*} (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M)
    (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) (x : ℝ) :
    discMap f γ₁ γ₂ v (x, 0) = f (γ₁ (sigR x)) := by
  rw [discMap, baseDisc_bot, discPert_zero_u, add_zero]

lemma discMap_top {M : Type*} (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M)
    (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) (x : ℝ) :
    discMap f γ₁ γ₂ v (x, 1) = f (γ₂ (sigR x)) := by
  rw [discMap, baseDisc_top, discPert_one_u, add_zero]

lemma discMap_left {M : Type*} (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M)
    (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) (u : ℝ)
    (h : f (γ₂ 0) = f (γ₁ 0)) :
    discMap f γ₁ γ₂ v ((-1 : ℝ), u) = f (γ₁ 0) := by
  rw [discMap, discPert_left, add_zero, baseDisc, sigR_neg_one]
  simp only [Prod.snd]
  rw [h]
  rw [show (1 - u) • f (γ₁ 0) + u • f (γ₁ 0) = ((1 - u) + u) • f (γ₁ 0) from
    (add_smul (1 - u) u (f (γ₁ 0))).symm]
  norm_num

lemma discMap_right {M : Type*} (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M)
    (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) (u : ℝ)
    (h : f (γ₂ 1) = f (γ₁ 1)) :
    discMap f γ₁ γ₂ v ((1 : ℝ), u) = f (γ₁ 1) := by
  rw [discMap, discPert_right, add_zero, baseDisc, sigR_one]
  simp only [Prod.snd]
  rw [h]
  rw [show (1 - u) • f (γ₁ 1) + u • f (γ₁ 1) = ((1 - u) + u) • f (γ₁ 1) from
    (add_smul (1 - u) u (f (γ₁ 1))).symm]
  norm_num

/-! ## The derivative of the candidate disc along the two edges -/

lemma hasDerivAt_pert (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) (x : ℝ) :
    HasDerivAt (fun u : ℝ => ∑ k : Fin 2 × Fin 2, (uBeta k.1 u * xAlpha k.2 x) • v k)
      (∑ k : Fin 2 × Fin 2, (xAlpha k.2 x) • v k) 0 := by
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h1 : HasDerivAt (fun u : ℝ => uBeta k.1 u * xAlpha k.2 x) (1 * xAlpha k.2 x) 0 :=
    (hasDerivAt_uBeta_zero k.1).mul_const (xAlpha k.2 x)
  have h2 : HasDerivAt (fun u : ℝ => (uBeta k.1 u * xAlpha k.2 x) • v k)
      ((1 * xAlpha k.2 x) • v k) 0 := h1.smul_const (v k)
  simpa using h2

lemma hasDerivAt_pert_one (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) (x : ℝ) :
    HasDerivAt (fun u : ℝ => ∑ k : Fin 2 × Fin 2, (uBeta k.1 u * xAlpha k.2 x) • v k)
      (∑ k : Fin 2 × Fin 2, (bumpU1 k x) • v k) 1 := by
  refine HasDerivAt.fun_sum fun k _ => ?_
  by_cases h : k.1 = 0
  · rw [bumpU1_eq]
    simp only [if_pos h]
    rw [h, uBeta_zero_fun]
    have h1 : HasDerivAt (fun u : ℝ => uBump u * xAlpha k.2 x) (-1 * xAlpha k.2 x) 1 :=
      hasDerivAt_uBump_one.mul_const (xAlpha k.2 x)
    have h2 : HasDerivAt (fun u : ℝ => (uBump u * xAlpha k.2 x) • v k)
        ((-1 * xAlpha k.2 x) • v k) 1 := h1.smul_const (v k)
    simpa using h2
  · rw [bumpU1_eq]
    simp only [if_neg h]
    rw [uBeta_ne_zero_fun h]
    have h1 : HasDerivAt (fun u : ℝ => uBump2 u * xAlpha k.2 x) (0 * xAlpha k.2 x) 1 :=
      hasDerivAt_uBump2_one.mul_const (xAlpha k.2 x)
    have h2 : HasDerivAt (fun u : ℝ => (uBump2 u * xAlpha k.2 x) • v k)
        ((0 * xAlpha k.2 x) • v k) 1 := h1.smul_const (v k)
    simpa using h2

lemma hasDerivAt_one_sub (c u₀ : ℝ) : HasDerivAt (fun u : ℝ => c - u) (-1) u₀ := by
  have h : HasDerivAt ((fun _ : ℝ => c) - id) (0 - 1) u₀ :=
    (hasDerivAt_const (x := u₀) c).sub (hasDerivAt_id u₀)
  have hfun : ((fun _ : ℝ => c) - id) = fun u : ℝ => c - u := rfl
  rw [hfun] at h
  norm_num at h
  exact h

/-- The derivative of the candidate disc at the lower edge. -/
lemma fderiv_discMap_bot {M : Type*} (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (γ₁ γ₂ : ℝ → M) (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) (x : ℝ)
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => f (γ₁ (sigR x))))
    (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => f (γ₂ (sigR x)))) :
    fderiv ℝ (discMap f γ₁ γ₂ v) (x, 0) (0, 1) =
      (f (γ₂ (sigR x)) - f (γ₁ (sigR x))) + ∑ k, (bumpU k x) • v k := by
  rw [fderiv_snd_eq_deriv _ x 0 (differentiableAt_discMap f γ₁ γ₂ v (x, 0) hA hB)]
  have hfun : (fun u : ℝ => discMap f γ₁ γ₂ v (x, u)) = fun u : ℝ =>
      ((1 - u) • f (γ₁ (sigR x)) + u • f (γ₂ (sigR x)))
        + ∑ k : Fin 2 × Fin 2, (uBeta k.1 u * xAlpha k.2 x) • v k := by
    funext u; simp only [discMap, baseDisc, discPert, discBump]
  rw [hfun]
  have h1 : HasDerivAt (fun u : ℝ => (1 - u) • f (γ₁ (sigR x)))
      ((-1 : ℝ) • f (γ₁ (sigR x))) 0 :=
    (hasDerivAt_one_sub 1 0).smul_const _
  have h2 : HasDerivAt (fun u : ℝ => u • f (γ₂ (sigR x)))
      ((1 : ℝ) • f (γ₂ (sigR x))) 0 :=
    (hasDerivAt_id (0 : ℝ)).smul_const _
  have h3 := hasDerivAt_pert v x
  have hfun' : (fun u : ℝ => (1 - u) • f (γ₁ (sigR x)) + u • f (γ₂ (sigR x))
        + ∑ k : Fin 2 × Fin 2, (uBeta k.1 u * xAlpha k.2 x) • v k)
      = (fun u : ℝ => (1 - u) • f (γ₁ (sigR x))) + (fun u : ℝ => u • f (γ₂ (sigR x)))
        + (fun u : ℝ => ∑ k : Fin 2 × Fin 2, (uBeta k.1 u * xAlpha k.2 x) • v k) := by
    funext u; simp only [Pi.add_apply]
  have hder : (-1 : ℝ) • f (γ₁ (sigR x)) + (1 : ℝ) • f (γ₂ (sigR x))
      + ∑ k : Fin 2 × Fin 2, (xAlpha k.2 x) • v k
      = (f (γ₂ (sigR x)) - f (γ₁ (sigR x))) + ∑ k : Fin 2 × Fin 2, (bumpU k x) • v k := by
    have hs : (∑ k : Fin 2 × Fin 2, (xAlpha k.2 x) • v k)
        = ∑ k : Fin 2 × Fin 2, (bumpU k x) • v k :=
      Finset.sum_congr rfl fun k _ => by rw [bumpU_eq]
    rw [hs]
    simp only [one_smul, neg_one_smul]
    abel
  rw [hfun', ((h1.add h2).add h3).deriv]
  exact hder

/-- The derivative of the candidate disc at the upper edge. -/
lemma fderiv_discMap_top {M : Type*} (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (γ₁ γ₂ : ℝ → M) (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) (x : ℝ)
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => f (γ₁ (sigR x))))
    (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => f (γ₂ (sigR x)))) :
    fderiv ℝ (discMap f γ₁ γ₂ v) (x, 1) (0, 1) =
      (f (γ₂ (sigR x)) - f (γ₁ (sigR x))) + ∑ k, (bumpU1 k x) • v k := by
  rw [fderiv_snd_eq_deriv _ x 1 (differentiableAt_discMap f γ₁ γ₂ v (x, 1) hA hB)]
  have hfun : (fun u : ℝ => discMap f γ₁ γ₂ v (x, u)) = fun u : ℝ =>
      ((1 - u) • f (γ₁ (sigR x)) + u • f (γ₂ (sigR x)))
        + ∑ k : Fin 2 × Fin 2, (uBeta k.1 u * xAlpha k.2 x) • v k := by
    funext u; simp only [discMap, baseDisc, discPert, discBump]
  rw [hfun]
  have h1 : HasDerivAt (fun u : ℝ => (1 - u) • f (γ₁ (sigR x)))
      ((-1 : ℝ) • f (γ₁ (sigR x))) 1 :=
    (hasDerivAt_one_sub 1 1).smul_const _
  have h2 : HasDerivAt (fun u : ℝ => u • f (γ₂ (sigR x)))
      ((1 : ℝ) • f (γ₂ (sigR x))) 1 :=
    (hasDerivAt_id (1 : ℝ)).smul_const _
  have h3 := hasDerivAt_pert_one v x
  have hfun' : (fun u : ℝ => (1 - u) • f (γ₁ (sigR x)) + u • f (γ₂ (sigR x))
        + ∑ k : Fin 2 × Fin 2, (uBeta k.1 u * xAlpha k.2 x) • v k)
      = (fun u : ℝ => (1 - u) • f (γ₁ (sigR x))) + (fun u : ℝ => u • f (γ₂ (sigR x)))
        + (fun u : ℝ => ∑ k : Fin 2 × Fin 2, (uBeta k.1 u * xAlpha k.2 x) • v k) := by
    funext u; simp only [Pi.add_apply]
  have hder : (-1 : ℝ) • f (γ₁ (sigR x)) + (1 : ℝ) • f (γ₂ (sigR x))
      + ∑ k : Fin 2 × Fin 2, (bumpU1 k x) • v k
      = (f (γ₂ (sigR x)) - f (γ₁ (sigR x))) + ∑ k : Fin 2 × Fin 2, (bumpU1 k x) • v k := by
    simp only [one_smul, neg_one_smul]
    abel
  rw [hfun', ((h1.add h2).add h3).deriv]
  exact hder

/-- **A good translation parameter exists** once the four dimension bounds are available. -/
theorem exists_goodParam_of_bounds {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M)
    (h1 : dimH (badAvoid f γ₁ γ₂) ≤ ((7 * n + 2 : ℕ) : ENNReal))
    (h2 : dimH (badInj f γ₁ γ₂) ≤ ((6 * n + 4 : ℕ) : ENNReal))
    (h3 : dimH (badTransBot f γ₁ γ₂) ≤ ((7 * n + 1 : ℕ) : ENNReal))
    (h4 : dimH (badTransTop f γ₁ γ₂) ≤ ((7 * n + 1 : ℕ) : ENNReal)) :
    ∃ v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n)),
      v ∉ badAvoid f γ₁ γ₂ ∧ v ∉ badInj f γ₁ γ₂ ∧ v ∉ badTransBot f γ₁ γ₂ ∧
        v ∉ badTransTop f γ₁ γ₂ := by
  have hAB : dimH (badAvoid f γ₁ γ₂ ∪ badInj f γ₁ γ₂) ≤ ((7 * n + 2 : ℕ) : ENNReal) := by
    rw [dimH_union]
    exact max_le h1 (le_trans h2 (by exact_mod_cast (by omega : 6 * n + 4 ≤ 7 * n + 2)))
  have hCD : dimH (badTransBot f γ₁ γ₂ ∪ badTransTop f γ₁ γ₂) ≤ ((7 * n + 2 : ℕ) : ENNReal) := by
    rw [dimH_union]
    exact max_le (le_trans h3 (by exact_mod_cast (by omega : 7 * n + 1 ≤ 7 * n + 2)))
      (le_trans h4 (by exact_mod_cast (by omega : 7 * n + 1 ≤ 7 * n + 2)))
  have hU : dimH ((badAvoid f γ₁ γ₂ ∪ badInj f γ₁ γ₂)
      ∪ (badTransBot f γ₁ γ₂ ∪ badTransTop f γ₁ γ₂)) ≤ ((7 * n + 2 : ℕ) : ENNReal) := by
    rw [dimH_union]
    exact max_le hAB hCD
  have hfin : (Module.finrank ℝ ((Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) : ENNReal)
      = ((8 * n : ℕ) : ENNReal) := by
    rw [Module.finrank_pi_fintype]
    simp [finrank_euclideanSpace_fin, Finset.sum_const, Fintype.card_prod]
    ring
  have hlt : dimH ((badAvoid f γ₁ γ₂ ∪ badInj f γ₁ γ₂)
      ∪ (badTransBot f γ₁ γ₂ ∪ badTransTop f γ₁ γ₂))
      < (Module.finrank ℝ ((Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) : ENNReal) := by
    rw [hfin]
    refine lt_of_le_of_lt hU ?_
    exact_mod_cast (by omega : 7 * n + 2 < 8 * n)
  obtain ⟨v, hv⟩ := (dense_compl_of_dimH_lt_finrank hlt).nonempty
  rw [Set.mem_compl_iff] at hv
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · intro hA; exact hv (Or.inl (Or.inl hA))
  · intro hB; exact hv (Or.inl (Or.inr hB))
  · intro hC; exact hv (Or.inr (Or.inl hC))
  · intro hD; exact hv (Or.inr (Or.inr hD))

/-- **The smooth Whitney disc of a bigon.** -/
theorem whitneyDiscSmooth {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (γ₁ γ₂ : ℝ → M)
    (hγ₁ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (hγv0 : f (γ₁ 0) = f (γ₂ 0)) (hγv1 : f (γ₁ 1) = f (γ₂ 1))
    (hγ₁injf : Set.InjOn (fun s : ℝ => f (γ₁ s)) (Set.Icc (0 : ℝ) 1))
    (hγ₂injf : Set.InjOn (fun s : ℝ => f (γ₂ s)) (Set.Icc (0 : ℝ) 1))
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    ∃ D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D ∧
      (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → D (x, 0) = f (γ₁ ((x + 1) / 2))) ∧
      (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → D (x, 1) = f (γ₂ ((x + 1) / 2))) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → D ((-1 : ℝ), t) = f (γ₁ 0)) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → D (1, t) = f (γ₁ 1)) ∧
      Set.InjOn D (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) ∧
      D '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) ∩
        (f '' (Set.univ : Set M)) = ∅ ∧
      (∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 →
        fderiv ℝ D (x, 0) (0, 1) ∉ (mfderiv
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f
            (γ₁ ((x + 1) / 2))).range) ∧
      (∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 →
        fderiv ℝ D (x, 1) (0, 1) ∉ (mfderiv
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f
            (γ₂ ((x + 1) / 2))).range) := by
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => f (γ₁ (sigR x))) :=
    contDiff_arcComp f γ₁ hf hγ₁
  have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => f (γ₂ (sigR x))) :=
    contDiff_arcComp f γ₂ hf hγ₂
  have hb1 : dimH (badAvoid f γ₁ γ₂) ≤ ((7 * n + 2 : ℕ) : ENNReal) :=
    dimH_badAvoid hn f hf γ₁ γ₂ hγ₁ hγ₂
  have hb2 : dimH (badInj f γ₁ γ₂) ≤ ((6 * n + 4 : ℕ) : ENNReal) :=
    dimH_badInj hn f hf γ₁ γ₂ hγ₁ hγ₂
  have hb3 : dimH (badTransBot f γ₁ γ₂) ≤ ((7 * n + 1 : ℕ) : ENNReal) :=
    dimH_badTransBot hn f hf γ₁ γ₂ hγ₁ hγ₂
  have hb4 : dimH (badTransTop f γ₁ γ₂) ≤ ((7 * n + 1 : ℕ) : ENNReal) :=
    dimH_badTransTop hn f hf γ₁ γ₂ hγ₁ hγ₂
  obtain ⟨v, hv1, hv2, hv3, hv4⟩ := exists_goodParam_of_bounds hn f γ₁ γ₂ hb1 hb2 hb3 hb4
  refine ⟨discMap f γ₁ γ₂ v, contDiff_discMap f γ₁ γ₂ v hA hB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; exact discMap_bot f γ₁ γ₂ v x
  · intro x hx; exact discMap_top f γ₁ γ₂ v x
  · intro t ht; exact discMap_left f γ₁ γ₂ v t hγv0.symm
  · intro t ht; exact discMap_right f γ₁ γ₂ v t hγv1.symm
  · intro p hp q hq hpq
    by_contra hne
    exact hv2 ⟨p, hp, q, hq, hne, hpq⟩
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨⟨p, hp, hzp⟩, ⟨y, -, hzy⟩⟩
    exact hv1 ⟨p, hp, y, hzp.trans hzy.symm⟩
  · intro x hx hmem
    rw [fderiv_discMap_bot f γ₁ γ₂ v x hA hB] at hmem
    exact hv3 ⟨x, hx, hmem⟩
  · intro x hx hmem
    rw [fderiv_discMap_top f γ₁ γ₂ v x hA hB] at hmem
    exact hv4 ⟨x, hx, hmem⟩

end

end Work.Drive.Whitney
