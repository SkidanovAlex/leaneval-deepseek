/-
  WilG4c — the "mean value inequality" behind the §5.3 reduction to `1`-Lipschitz
  (BNZ, *Wilkie's conjecture for Pfaffian structures*, §5.3).

  Suppose a family member `f : ℝ^p → ℝ^{n+1} → ℝ`, read as the single function
  `famFunHat f` on `ℝ^{p + (n+1)}`, is `C¹` on the cube, has `x`-derivative bounded by `C`
  and all `y`-derivatives bounded by `1` on the cube. Then each member is
  `max C 1 * (n+1)`-Lipschitz on the cube: this is the discrete mean value inequality in
  the `n+1` coordinate directions, using that the sup norm of the gradient of a `C¹`
  function of `N` variables is at most the sum of the coordinate-wise sup norms.

  The only point needing care is that `Fin.append l` is the (affine) map putting the
  parameters `l` in the first `p` coordinates; its derivative is a continuous linear map
  sending the `i`-th coordinate direction of `ℝ^{n+1}` to the `(p+i)`-th coordinate
  direction of `ℝ^{p + (n+1)}` (`appCLM`, `appCLM_single` below).
-/
import Mathlib
import Submission.Work.WilG4c.LipDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open Work.WilkG4c

/-! ## 1. The derivative of `v ↦ Fin.append l v` -/

/-- The continuous linear map underlying `v ↦ Fin.append l v`: it is the (non-dependent)
"append `0`" map, sending the `i`-th coordinate of `ℝ^{n+1}` to the `(p+i)`-th coordinate
of `ℝ^{p + (n+1)}` and killing the first `p` coordinates. -/
def appCLM (p n : ℕ) : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (p + (n + 1)) → ℝ) :=
  ContinuousLinearMap.pi
    (Fin.addCases (fun _ : Fin p => (0 : (Fin (n + 1) → ℝ) →L[ℝ] ℝ))
      (fun j : Fin (n + 1) => ContinuousLinearMap.proj j))

lemma appCLM_apply (p n : ℕ) (v : Fin (n + 1) → ℝ) :
    appCLM p n v = Fin.append (0 : Fin p → ℝ) v := by
  funext j
  unfold appCLM
  rw [ContinuousLinearMap.pi_apply]
  induction j using Fin.addCases with
  | left i' => rw [Fin.addCases_left, zero_apply, Fin.append_left]; rfl
  | right j' =>
      rw [Fin.addCases_right, ContinuousLinearMap.proj_apply, Fin.append_right]

/-- `appCLM` sends the `i`-th standard basis vector of `ℝ^{n+1}` to the `(p+i)`-th standard
basis vector of `ℝ^{p+(n+1)}`. -/
lemma appCLM_single (p n : ℕ) (i : Fin (n + 1)) :
    appCLM p n (Pi.single i (1 : ℝ)) =
      (Pi.single (Fin.natAdd p i) (1 : ℝ) : Fin (p + (n + 1)) → ℝ) := by
  rw [appCLM_apply]
  ext j
  refine Fin.addCases
    (motive := fun j =>
      (Fin.append (0 : Fin p → ℝ) (Pi.single i (1 : ℝ))) j =
        (Pi.single (Fin.natAdd p i) (1 : ℝ) : Fin (p + (n + 1)) → ℝ) j) ?_ ?_ j
  · intro i'
    rw [Fin.append_left, Pi.single_eq_of_ne]
    · rfl
    · intro h
      have hv := Fin.ext_iff.mp h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
  · intro j'
    rw [Fin.append_right, Pi.single_apply, Pi.single_apply]
    by_cases h : j' = i
    · subst h; simp
    · simp [h, Fin.natAdd_inj]

/-- `v ↦ Fin.append l v` is differentiable with derivative `appCLM p n` (independent of `l`),
the constant part `Fin.append l 0` being annihilated. -/
lemma hasFDerivAt_append (p n : ℕ) (l : Fin p → ℝ) (w : Fin (n + 1) → ℝ) :
    HasFDerivAt (fun v : Fin (n + 1) → ℝ => Fin.append l v) (appCLM p n) w := by
  have key : HasFDerivAt (fun x : Fin (n + 1) → ℝ => fun i => Fin.append l x i)
      (ContinuousLinearMap.pi
        (Fin.addCases (fun _ : Fin p => (0 : (Fin (n + 1) → ℝ) →L[ℝ] ℝ))
          (fun j : Fin (n + 1) => ContinuousLinearMap.proj j))) w := by
    rw [hasFDerivAt_pi]
    intro i
    induction i using Fin.addCases with
    | left i' =>
        have : (fun v : Fin (n + 1) → ℝ => Fin.append l v (Fin.castAdd (n + 1) i')) =
            fun _ => l i' := by
          funext v; rw [Fin.append_left]
        rw [this]
        simpa using hasFDerivAt_const (l i') w
    | right j =>
        have : (fun v : Fin (n + 1) → ℝ => Fin.append l v (Fin.natAdd p j)) =
            fun v => v j := by
          funext v; rw [Fin.append_right]
        rw [this]
        simpa using (hasFDerivAt_apply (𝕜 := ℝ) j w)
  exact key

/-! ## 2. The operator norm bound from coordinate-wise bounds -/

/-- Mean value inequality, linear-algebra part: if `L : (Fin N → ℝ) →L[ℝ] ℝ` is bounded by
`M` on each standard basis vector then `‖L‖ ≤ M * N`.  Indeed `L v = ∑ i, v i * L e_i`, and
each `‖v i‖ ≤ ‖v‖`. -/
lemma opNorm_le_coord {N : ℕ} (L : (Fin N → ℝ) →L[ℝ] ℝ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ i, |L (Pi.single i 1)| ≤ M) : ‖L‖ ≤ M * N := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hM (Nat.cast_nonneg N))
    (fun v => ?_)
  have hv : (∑ i, v i • Pi.single i 1) = v := by
    have := Module.Basis.sum_repr (Pi.basisFun ℝ (Fin N)) v
    simpa only [Pi.basisFun_repr, Pi.basisFun_apply] using this
  calc ‖L v‖ = ‖L (∑ i, v i • Pi.single i 1)‖ := by rw [hv]
    _ = ‖∑ i, L (v i • Pi.single i 1)‖ := by rw [map_sum]
    _ ≤ ∑ i, ‖L (v i • Pi.single i 1)‖ := norm_sum_le _ _
    _ = ∑ i, ‖v i‖ * ‖L (Pi.single i 1)‖ := by
        apply Finset.sum_congr rfl; intro i _
        rw [map_smul, norm_smul]
    _ ≤ ∑ i, ‖v‖ * M := by
        apply Finset.sum_le_sum; intro i _
        exact mul_le_mul (norm_le_pi_norm v i) (by rw [Real.norm_eq_abs]; exact h i)
          (norm_nonneg _) (norm_nonneg _)
    _ = M * N * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-! ## 3. Convexity of the cube and the value of `famFunHat` on the cube -/

lemma convex_openCube (μ : ℕ) : Convex ℝ (WilkiesDesign.openCube μ) := by
  intro x hx y hy a b ha hb hab i
  have key := (convex_Ioo (0 : ℝ) 1) (hx i) (hy i) ha hb hab
  simpa [Pi.smul_apply, Pi.add_apply] using key

lemma famFunHat_append_raw (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (l : Fin p → ℝ) (w : Fin (n + 1) → ℝ) : famFunHat f (Fin.append l w) = f l w := by
  simp [famFunHat, Fin.append_left, Fin.append_right]

/-! ## 4. The lemma -/

theorem LipOnCubeOfBound {p n : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hC1 : ∀ l : Fin p → ℝ, ∀ z ∈ WilkiesDesign.openCube (n + 1),
        ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat f) (Fin.append l z))
    (hx : ∀ l : Fin p → ℝ, ∀ z ∈ WilkiesDesign.openCube (n + 1),
        |fderiv ℝ (Work.WilkG4c.famFunHat f) (Fin.append l z)
          (Pi.single (Work.WilkG4c.xDirHat p n) 1)| ≤ C)
    (hy : ∀ l : Fin p → ℝ, ∀ z ∈ WilkiesDesign.openCube (n + 1), ∀ j : Fin n,
        |fderiv ℝ (Work.WilkG4c.famFunHat f) (Fin.append l z)
          (Pi.single (Fin.natAdd p j.succ) 1)| ≤ 1) :
    Work.WilkG4c.LipOnCube (fun _ : Fin 1 => f) (max C 1 * ((n : ℝ) + 1)) := by
  intro i l z z' hz hz'
  change |f l z - f l z'| ≤ max C 1 * ((n : ℝ) + 1) * dist z z'
  have hdiff : ∀ w ∈ WilkiesDesign.openCube (n + 1),
      DifferentiableAt ℝ (fun x : Fin (n + 1) → ℝ => famFunHat f (Fin.append l x)) w := by
    intro w hw
    exact DifferentiableAt.comp w ((hC1 l w hw).differentiableAt (by norm_num))
      (hasFDerivAt_append p n l w).differentiableAt
  have hbound : ∀ w ∈ WilkiesDesign.openCube (n + 1),
      ‖fderiv ℝ (fun x : Fin (n + 1) → ℝ => famFunHat f (Fin.append l x)) w‖
        ≤ max C 1 * ((n : ℝ) + 1) := by
    intro w hw
    have hfam : HasFDerivAt (famFunHat f) (fderiv ℝ (famFunHat f) (Fin.append l w))
        (Fin.append l w) := ((hC1 l w hw).differentiableAt (by norm_num)).hasFDerivAt
    have hG : fderiv ℝ (fun x : Fin (n + 1) → ℝ => famFunHat f (Fin.append l x)) w
        = (fderiv ℝ (famFunHat f) (Fin.append l w)) ∘SL appCLM p n :=
      (hfam.comp w (hasFDerivAt_append p n l w)).fderiv
    rw [hG]
    have hcoord : ∀ i : Fin (n + 1),
        |((fderiv ℝ (famFunHat f) (Fin.append l w)) ∘SL appCLM p n) (Pi.single i 1)|
          ≤ max C 1 := by
      intro i
      rw [ContinuousLinearMap.comp_apply, appCLM_single]
      induction i using Fin.cases with
      | zero => simpa [Work.WilkG4c.xDirHat] using le_trans (hx l w hw) (le_max_left C 1)
      | succ j => exact le_trans (hy l w hw j) (le_max_right C 1)
    have hmain := opNorm_le_coord ((fderiv ℝ (famFunHat f) (Fin.append l w)) ∘SL appCLM p n)
      (max C 1) (le_trans zero_le_one (le_max_right C 1)) hcoord
    calc ‖(fderiv ℝ (famFunHat f) (Fin.append l w)) ∘SL appCLM p n‖
        ≤ max C 1 * ((n + 1 : ℕ) : ℝ) := hmain
      _ = max C 1 * ((n : ℝ) + 1) := by push_cast; ring
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound
    (convex_openCube (n + 1)) hz hz'
  rw [famFunHat_append_raw, famFunHat_append_raw, Real.norm_eq_abs, abs_sub_comm, ← dist_eq_norm,
    dist_comm] at hmvt
  exact hmvt

end Work.WilG4c
