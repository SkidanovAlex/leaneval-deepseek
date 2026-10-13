import Mathlib

namespace Work.WilG4b

theorem xDeriv_eq {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (γ : ℝ → (Fin n → ℝ)) (x₀ φ' : ℝ)
    (γ' : Fin n → ℝ) (hf : ContDiffAt ℝ 1 f (Fin.cons x₀ (γ x₀)))
    (hγ : ∀ i : Fin n, HasDerivAt (fun x => γ x i) (γ' i) x₀)
    (hφ : HasDerivAt (fun x : ℝ => f (Fin.cons x (γ x))) φ' x₀) :
    fderiv ℝ f (Fin.cons x₀ (γ x₀)) (Pi.single 0 1)
      = φ' - ∑ i : Fin n, fderiv ℝ f (Fin.cons x₀ (γ x₀)) (Pi.single i.succ 1) * γ' i := by
  -- Fréchet differentiability of `f` at the base point, from `ContDiffAt ℝ 1`.
  have hfd : HasFDerivAt f (fderiv ℝ f (Fin.cons x₀ (γ x₀))) (Fin.cons x₀ (γ x₀)) :=
    (hf.differentiableAt_one).hasFDerivAt
  -- Differentiability of the curve `x ↦ γ x`, componentwise.
  have hγd : HasDerivAt γ γ' x₀ := hasDerivAt_pi.mpr hγ
  -- Derivative of the curve `x ↦ Fin.cons x (γ x)`: it is `Fin.cons 1 γ'`.
  have hcons : HasDerivAt (fun x : ℝ => Fin.cons x (γ x))
      ((Fin.cons (1:ℝ) γ' : Fin (n+1) → ℝ)) x₀ :=
    HasDerivAt.finCons (F' := fun _ : Fin (n+1) => ℝ) (hasDerivAt_id x₀) hγd
  -- Chain rule.
  have hchain : HasDerivAt (fun x : ℝ => f (Fin.cons x (γ x)))
      ((fderiv ℝ f (Fin.cons x₀ (γ x₀))) ((Fin.cons (1:ℝ) γ' : Fin (n+1) → ℝ))) x₀ :=
    hfd.comp_hasDerivAt x₀ hcons
  -- Uniqueness of the derivative.
  have hkey : (fderiv ℝ f (Fin.cons x₀ (γ x₀))) ((Fin.cons (1:ℝ) γ' : Fin (n+1) → ℝ)) = φ' :=
    hchain.unique hφ
  -- Coordinate expansion of `Fin.cons 1 γ'` in the standard basis.
  have hsplit : ((Fin.cons (1:ℝ) γ' : Fin (n+1) → ℝ))
      = Pi.single 0 1 + ∑ i : Fin n, γ' i • Pi.single i.succ 1 := by
    show (fun j : Fin (n+1) => (Fin.cons (1:ℝ) γ' : Fin (n+1) → ℝ) j)
        = Pi.single 0 1 + ∑ i : Fin n, γ' i • Pi.single i.succ 1
    rw [← Finset.univ_sum_single
      (fun j : Fin (n+1) => (Fin.cons (1:ℝ) γ' : Fin (n+1) → ℝ) j)]
    rw [Fin.sum_univ_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.cons_succ]
    have h := Pi.single_smul' i.succ (γ' i) (1:ℝ)
    rw [smul_eq_mul, mul_one] at h
    exact h
  -- Linearity of the Fréchet derivative applied to that expansion.
  have hdecomp : (fderiv ℝ f (Fin.cons x₀ (γ x₀))) ((Fin.cons (1:ℝ) γ' : Fin (n+1) → ℝ))
      = (fderiv ℝ f (Fin.cons x₀ (γ x₀))) (Pi.single 0 1)
        + ∑ i : Fin n, (fderiv ℝ f (Fin.cons x₀ (γ x₀))) (Pi.single i.succ 1) * γ' i := by
    rw [hsplit, map_add, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, smul_eq_mul, mul_comm]
  rw [eq_sub_iff_add_eq]
  rw [← hdecomp, hkey]

end Work.WilG4b
