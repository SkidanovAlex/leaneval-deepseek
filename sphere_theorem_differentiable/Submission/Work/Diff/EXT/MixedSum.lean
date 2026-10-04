import Mathlib
import Submission.Work.Diff.EXT.jets_eq_of_t_derivs_eq
import Submission.Commons.Analysis.Calculus.FDeriv.secondDirectional_commute_two

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Mixed-derivative sums for functions on `ℝ × E`

Support file for `Work.Diff.EXT.norm_iteratedFDeriv_le_mixed`.  It contains

* `evalTupleCLM`: evaluation of a continuous multilinear map at a fixed tuple, as a
  continuous linear map, and the resulting commutation of `iteratedDeriv` with evaluation;
* `clmApplyConst_of`: commutation of `iteratedFDeriv` with the application of a
  `CLM`-valued family to a fixed vector;
* `iteratedFDeriv_succ_snoc_apply`: peeling off the last argument of an iterated derivative;
* `contDiffOn_fderiv_apply`: smoothness on an open set of `z ↦ fderiv Φ z c`;
* `iteratedFDeriv_slice_eq`: the iterated derivative of a slice, as a composition with `inr`;
* `contDiffAt_sliceJet`: smoothness in `t` of the `j`-jet of the slices `y ↦ Φ (t, y)`;
* `mixedSum`: the sum of the norms of the mixed partial derivatives.
-/

open scoped Topology ContDiff
open Filter ContinuousLinearMap

namespace Work.Diff.EXT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-! ## Evaluation of a multilinear map at a fixed tuple -/

/-- Evaluation of a continuous `k`-multilinear map at a fixed tuple, as a continuous linear map. -/
noncomputable def evalTupleCLM (k : ℕ) (b : Fin k → E) : (E [×k]→L[ℝ] Z) →L[ℝ] Z :=
  LinearMap.mkContinuous
    { toFun := fun T => T b
      map_add' := fun T T' => by simp
      map_smul' := fun c T => by simp }
    (∏ i, ‖b i‖)
    (fun T => by rw [mul_comm]; exact T.le_opNorm b)

lemma evalTupleCLM_apply (k : ℕ) (b : Fin k → E) (T : E [×k]→L[ℝ] Z) :
    evalTupleCLM (Z := Z) k b T = T b := rfl

/-- `iteratedDeriv` commutes with evaluation of a multilinear map at a fixed tuple. -/
lemma iteratedDeriv_evalTuple {k : ℕ} (b : Fin k → E) {g : ℝ → (E [×k]→L[ℝ] Z)} {t : ℝ}
    {l : ℕ} (hg : ContDiffAt ℝ l g t) :
    (iteratedDeriv l g t) b = iteratedDeriv l (fun s => g s b) t := by
  have h := (evalTupleCLM (Z := Z) k b).iteratedFDeriv_comp_left (f := g) hg (i := l) (by simp)
  have h2 := congrArg (fun T : ℝ [×l]→L[ℝ] Z => T (fun _ => (1 : ℝ))) h
  have hfun : (⇑(evalTupleCLM (Z := Z) k b) ∘ g) = fun s => g s b := by
    funext s; exact evalTupleCLM_apply k b (g s)
  rw [hfun] at h2
  simpa [iteratedDeriv, evalTupleCLM_apply] using h2.symm

/-! ## Applying a `CLM`-valued family to a fixed vector -/

/-- `iteratedFDeriv` of a `CLM`-valued family applied to a fixed vector. -/
lemma clmApplyConst_of {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {c : V → F →L[ℝ] G} {x : V} {n : ℕ∞ω} (hc : ContDiffAt ℝ n c x) {i : ℕ}
    (hi : (i : ℕ∞ω) ≤ n) {u : F} {m : Fin i → V} :
    (iteratedFDeriv ℝ i (fun y => (c y) u) x) m = ((iteratedFDeriv ℝ i c x) m) u := by
  have key : iteratedFDeriv ℝ i (fun y => (c y) u) x
      = (ContinuousLinearMap.apply ℝ G u).compContinuousMultilinearMap (iteratedFDeriv ℝ i c x) := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply]
      using (ContinuousLinearMap.apply ℝ G u).iteratedFDeriv_comp_left (f := c) hc (i := i) hi
  rw [key]
  simp [ContinuousLinearMap.compContinuousMultilinearMap_coe, ContinuousLinearMap.apply_apply]

/-- Peeling the last argument of an iterated derivative. -/
lemma iteratedFDeriv_succ_snoc_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {G : V → W} {q : V} {k : ℕ} {n : ℕ∞ω} (h : ContDiffAt ℝ n (fderiv ℝ G) q)
    (hi : (k : ℕ∞ω) ≤ n) (v : Fin k → V) (ζ : V) :
    iteratedFDeriv ℝ (k + 1) G q (Fin.snoc v ζ)
      = iteratedFDeriv ℝ k (fun y => fderiv ℝ G y ζ) q v := by
  rw [iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
  exact (clmApplyConst_of h hi).symm

/-! ## Smoothness of derived functions -/

/-- `z ↦ fderiv Φ z c` is `C^n` if `Φ` is `C^{n+1}` on an open set. -/
lemma contDiffOn_fderiv_apply {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {u : Set (ℝ × E)} (hu : IsOpen u) {Φ : ℝ × E → W} {n : ℕ}
    (hΦ : ContDiffOn ℝ (n + 1) Φ u) (c : ℝ × E) :
    ContDiffOn ℝ n (fun z => fderiv ℝ Φ z c) u := by
  have h1 : ContDiffOn ℝ n (fderivWithin ℝ Φ u) u :=
    ContDiffOn.fderivWithin hΦ hu.uniqueDiffOn le_rfl
  have h2 : ContDiffOn ℝ n (fderiv ℝ Φ) u :=
    h1.congr (fun z hz => (fderivWithin_of_isOpen hu hz).symm)
  exact h2.clm_apply contDiffOn_const

/-- Local version of composition with a continuous linear map on the right. -/
lemma iteratedFDeriv_comp_right_at {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    (g : W →L[ℝ] V) {f : V → T} {x : W} {n : ℕ} (hf : ContDiffAt ℝ n f (g x)) {i : ℕ}
    (hi : i ≤ n) :
    iteratedFDeriv ℝ i (f ∘ g) x
      = (iteratedFDeriv ℝ i f (g x)).compContinuousLinearMap (fun _ => g) := by
  obtain ⟨s, hs_mem, hs⟩ := hf.contDiffOn (m := (i : ℕ∞ω)) (by exact_mod_cast hi) (by simp)
  obtain ⟨v, hv_sub, hv_open, hv_mem⟩ := mem_nhds_iff.mp hs_mem
  have hv_uniq : UniqueDiffOn ℝ v := hv_open.uniqueDiffOn
  have hgv_uniq : UniqueDiffOn ℝ (⇑g ⁻¹' v) := (hv_open.preimage g.continuous).uniqueDiffOn
  have hcv : ContDiffOn ℝ (i : ℕ∞ω) f v := hs.mono hv_sub
  have hkey := g.iteratedFDerivWithin_comp_right hcv hv_uniq hgv_uniq hv_mem (i := i) le_rfl
  rw [iteratedFDerivWithin_of_isOpen i (hv_open.preimage g.continuous) (by simpa using hv_mem),
    iteratedFDerivWithin_of_isOpen i hv_open hv_mem] at hkey
  exact hkey

/-- The iterated derivative of a slice: composition with `inr` and translation. -/
lemma iteratedFDeriv_slice_eq {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {Φ : ℝ × E → W} {k : ℕ} {z : ℝ × E} (h : ContDiffAt ℝ k Φ z) :
    iteratedFDeriv ℝ k (fun y' : E => Φ (z.1, y')) z.2
      = (iteratedFDeriv ℝ k Φ z).compContinuousLinearMap
          (fun _ : Fin k => ContinuousLinearMap.inr ℝ ℝ E) := by
  have hdecomp : (fun y' : E => Φ (z.1, y'))
      = (fun q : ℝ × E => Φ (q + (z.1, (0 : E)))) ∘ (ContinuousLinearMap.inr ℝ ℝ E) := by
    funext y'; simp [ContinuousLinearMap.inr_apply]
  have hpt : (ContinuousLinearMap.inr ℝ ℝ E z.2) + (z.1, (0 : E)) = z := by
    ext <;> simp [ContinuousLinearMap.inr_apply]
  have hsm : ContDiffAt ℝ k (fun q : ℝ × E => Φ (q + (z.1, (0 : E))))
      (ContinuousLinearMap.inr ℝ ℝ E z.2) :=
    ContDiffAt.comp (ContinuousLinearMap.inr ℝ ℝ E z.2) (by rw [hpt]; exact h)
      (contDiffAt_id.add contDiffAt_const)
  rw [hdecomp, iteratedFDeriv_comp_right_at (ContinuousLinearMap.inr ℝ ℝ E) hsm (le_refl k)]
  congr 1
  rw [iteratedFDeriv_comp_add_right']
  simp only [hpt]

/-- The family of `j`-jets of the slices is `C^L` when `Φ` is `C^{L+j}` on an open set. -/
lemma contDiffAt_sliceJet {u : Set (ℝ × E)} (hu : IsOpen u) {Φ : ℝ × E → Z} {N : ℕ}
    (hΦ : ContDiffOn ℝ (N : ℕ∞ω) Φ u) {j L : ℕ} (hL : L + j ≤ N) {t : ℝ} {y : E}
    (hmem : (t, y) ∈ u) :
    ContDiffAt ℝ (L : ℕ∞ω) (fun s : ℝ => iteratedFDeriv ℝ j (fun y' : E => Φ (s, y')) y) t := by
  have hJ : ContDiffAt ℝ (L : ℕ∞ω) (iteratedFDeriv ℝ j Φ) (t, y) :=
    (hΦ.contDiffAt (hu.mem_nhds hmem)).iteratedFDeriv_right (m := (L : ℕ∞ω)) (i := j)
      (by exact_mod_cast hL)
  have h1 : ContDiffAt ℝ (L : ℕ∞ω) (fun s : ℝ => iteratedFDeriv ℝ j Φ (s, y)) t :=
    ContDiffAt.comp t hJ (contDiffAt_id.prodMk contDiffAt_const)
  have hT : ContDiffAt ℝ (L : ℕ∞ω)
      (fun s : ℝ => (iteratedFDeriv ℝ j Φ (s, y)).compContinuousLinearMap
        (fun _ : Fin j => ContinuousLinearMap.inr ℝ ℝ E)) t :=
    ContDiffAt.comp t (((ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin j => ContinuousLinearMap.inr ℝ ℝ E)) :
      ((ℝ × E) [×j]→L[ℝ] Z) →L[ℝ] (E [×j]→L[ℝ] Z)).contDiff.contDiffAt) h1
  refine hT.congr_of_eventuallyEq ?_
  have hEm : ∀ᶠ s : ℝ in 𝓝 t, (s, y) ∈ u :=
    (continuousAt_id.prodMk continuousAt_const).eventually (hu.mem_nhds hmem)
  filter_upwards [hEm] with s hs
  exact iteratedFDeriv_slice_eq ((hΦ.contDiffAt (hu.mem_nhds hs)).of_le
    (by exact_mod_cast (show j ≤ N by omega)))

/-! ## The mixed sum -/

/-- The mixed sum bounding the `m`-th derivative. -/
noncomputable def mixedSum (m : ℕ) (F : ℝ × E → Z) (p : ℝ × E) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    ‖iteratedDeriv (m - k) (fun t : ℝ => iteratedFDeriv ℝ k (fun y' : E => F (t, y')) p.2) p.1‖

end Work.Diff.EXT
