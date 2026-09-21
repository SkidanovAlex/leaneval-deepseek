import Mathlib

/-!
# Slice derivatives as joint partial derivatives

For a function `F : ℝ × ℝ → ℝ` that is `C^∞` on an open set `V`, the operator
`pderiv1 V F p := fderivWithin ℝ F V p (1, 0)` computes the derivative in the first variable
of `F` at `p`.  Its `k`-th iterate gives the `k`-th `iteratedDeriv` of the vertical slices
`u ↦ F (u, t)`, and the iterates are again `C^∞` on `V`.
-/

namespace Work.OddVolterra.Smooth

open Set Filter
open scoped Topology

noncomputable section

/-- The partial derivative of `F` in the first variable (computed within the set `V`),
viewed as a function on `ℝ × ℝ`. -/
def pderiv1 (V : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => fderivWithin ℝ F V p (1, 0)

/-- The `k`-th iterate of `pderiv1`. -/
def pderiv1Iter (V : Set (ℝ × ℝ)) (k : ℕ) (F : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  (pderiv1 V)^[k] F

lemma pderiv1_apply (V : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    pderiv1 V F p = fderivWithin ℝ F V p (1, 0) := rfl

lemma pderiv1Iter_zero (V : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) : pderiv1Iter V 0 F = F :=
  Function.iterate_zero_apply (pderiv1 V) F

lemma pderiv1Iter_succ (V : Set (ℝ × ℝ)) (k : ℕ) (F : ℝ × ℝ → ℝ) :
    pderiv1Iter V (k + 1) F = pderiv1 V (pderiv1Iter V k F) :=
  Function.iterate_succ_apply' (pderiv1 V) k F

/-- The top of `ℕ∞`, coerced into `WithTop ℕ∞`, satisfies `↑⊤ + 1 ≤ ↑⊤`. -/
lemma top_coe_add_one_le : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  rw [show (1 : WithTop ℕ∞) = ((1 : ℕ∞) : WithTop ℕ∞) by simp, ← WithTop.coe_add]
  simp

/-- If `F` is `C^∞` on an open set `V`, then so is its first partial derivative. -/
lemma contDiffOn_pderiv1 {V : Set (ℝ × ℝ)} (hV : IsOpen V) {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F V) : ContDiffOn ℝ (⊤ : ℕ∞) (pderiv1 V F) V := by
  have h := hF.fderivWithin hV.uniqueDiffOn top_coe_add_one_le
  have h2 := h.clm_apply (contDiffOn_const (c := ((1 : ℝ), (0 : ℝ))))
  have h3 : (fun x : ℝ × ℝ => (fderivWithin ℝ F V x) ((1 : ℝ), (0 : ℝ))) = pderiv1 V F := by
    funext x
    rfl
  rwa [h3] at h2

/-- The `k`-th iterate of the first partial derivative is again `C^∞` on `V`. -/
lemma contDiffOn_pderiv1Iter {V : Set (ℝ × ℝ)} (hV : IsOpen V) {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F V) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (pderiv1Iter V k F) V := by
  induction k with
  | zero => simpa [pderiv1Iter] using hF
  | succ k ih =>
    rw [pderiv1Iter_succ]
    exact contDiffOn_pderiv1 hV ih

/-- The derivative of a vertical slice of a `C^∞` function is its first partial derivative. -/
lemma hasDerivAt_slice {V : Set (ℝ × ℝ)} (hV : IsOpen V) {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F V) {s t : ℝ} (hst : (s, t) ∈ V) :
    HasDerivAt (fun u : ℝ => F (u, t)) (pderiv1 V F (s, t)) s := by
  have hmem : V ∈ 𝓝 (s, t) := hV.mem_nhds hst
  have hd : DifferentiableAt ℝ F (s, t) :=
    (hF.differentiableOn (by simp)).differentiableAt hmem
  have hderiv : HasFDerivAt F (fderiv ℝ F (s, t)) (s, t) := hd.hasFDerivAt
  have hι : HasFDerivAt (fun u : ℝ => (u, t))
      ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ)) s :=
    (hasFDerivAt_id s).prodMk (hasFDerivAt_const t s)
  have hc := hderiv.comp s hι
  have hfun : (fun u : ℝ => F (u, t)) = F ∘ (fun u : ℝ => (u, t)) := rfl
  rw [hfun]
  have hval : (((fderiv ℝ F (s, t)) ∘SL ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ))) 1)
      = pderiv1 V F (s, t) := by
    rw [pderiv1_apply]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, zero_apply]
    rw [fderivWithin_of_mem_nhds hmem]
  rw [← hval]
  exact hc.hasDerivAt

/-- The derivative of a vertical slice of a `C^∞` function is its first partial derivative. -/
lemma deriv_slice_eq_pderiv1 {V : Set (ℝ × ℝ)} (hV : IsOpen V) {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F V) {s t : ℝ} (hst : (s, t) ∈ V) :
    deriv (fun u : ℝ => F (u, t)) s = pderiv1 V F (s, t) :=
  (hasDerivAt_slice hV hF hst).deriv

/-- The `k`-th iterated derivative of a vertical slice is the `k`-th iterate of `pderiv1`,
provided `(s, t) ∈ V` and `F` is `C^∞` on the open set `V`. -/
lemma iteratedDeriv_eq_pderiv1Iter {V : Set (ℝ × ℝ)} (hV : IsOpen V) {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F V) {s t : ℝ} (hst : (s, t) ∈ V) (k : ℕ) :
    iteratedDeriv k (fun u : ℝ => F (u, t)) s = pderiv1Iter V k F (s, t) := by
  induction k generalizing s with
  | zero => simp [pderiv1Iter]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hcd : ContDiffOn ℝ (⊤ : ℕ∞) (pderiv1Iter V k F) V := contDiffOn_pderiv1Iter hV hF k
    have hcont : ContinuousAt (fun u : ℝ => (u, t)) s :=
      (continuous_id.prodMk continuous_const).continuousAt
    have hev : iteratedDeriv k (fun u : ℝ => F (u, t))
        =ᶠ[𝓝 s] (fun u : ℝ => pderiv1Iter V k F (u, t)) := by
      filter_upwards [hcont.eventually (hV.mem_nhds hst)] with w hw
      exact ih hw
    rw [Filter.EventuallyEq.deriv_eq hev, deriv_slice_eq_pderiv1 hV hcd hst, pderiv1Iter_succ]

end

end Work.OddVolterra.Smooth
