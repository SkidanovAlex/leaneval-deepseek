import Mathlib

set_option autoImplicit false
-- `hN : 1 ≤ N` is part of the requested interface; the argument below works for all `N`.
set_option linter.unusedVariables false
noncomputable section

open scoped Topology
open Filter

namespace Work.WilG4c

/-! ### Auxiliary lemmas

The main result says that limits of the `(m+1)`-st iterated derivative of `g` along the coordinate
directions give a limit of the `m`-th iterated derivative of `x ↦ fderiv ℝ g x`.  The two
ingredients are

* the algebraic identity `iteratedFDeriv_succ_apply_right` relating the `(m+1)`-st iterated
  derivative of `g` to the `m`-th iterated derivative of the derivative of `g`, combined with the
  basis bookkeeping of `Fin.snoc`/`Fin.init`; and
* the analytic fact that, on the finite dimensional space `Fin N → ℝ`, a family of continuous
  linear maps converges in the operator norm as soon as its values on the standard basis vectors
  converge. -/

/-- **Operator-norm bound in terms of the standard basis.**  For a continuous linear map out of
`Fin N → ℝ`, the operator norm is bounded by the sum of the norms of its values on the standard
basis vectors `Pi.single j 1`. -/
theorem clm_norm_le_sum_basis {N : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : (Fin N → ℝ) →L[ℝ] F) :
    ‖S‖ ≤ ∑ j : Fin N, ‖S (Pi.single j 1)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound S (Finset.sum_nonneg (fun j _ => norm_nonneg _)) ?_
  intro y
  calc ‖S y‖ = ‖∑ j : Fin N, y j • S (Pi.single j 1)‖ := by
        congr 1
        conv_lhs => rw [show y = ∑ j : Fin N, y j • Pi.single j 1 from by
          funext i
          rw [Finset.sum_apply, Finset.sum_eq_single i]
          · simp
          · intro j _ hj; simp [Pi.single_eq_of_ne (Ne.symm hj)]
          · intro hi; exact absurd (Finset.mem_univ i) hi]
        rw [map_sum]
        exact Finset.sum_congr rfl (fun j _ => by rw [map_smul])
      _ ≤ ∑ j : Fin N, ‖y j • S (Pi.single j 1)‖ := norm_sum_le _ _
      _ = ∑ j : Fin N, ‖y j‖ * ‖S (Pi.single j 1)‖ := by
        apply Finset.sum_congr rfl; intro j _; rw [norm_smul]
      _ ≤ ∑ j : Fin N, ‖y‖ * ‖S (Pi.single j 1)‖ := by
        apply Finset.sum_le_sum; intro j _
        exact mul_le_mul_of_nonneg_right (norm_le_pi_norm y j) (norm_nonneg _)
      _ = ∑ j : Fin N, ‖S (Pi.single j 1)‖ * ‖y‖ := by
        apply Finset.sum_congr rfl; intro j _; rw [mul_comm]
      _ = (∑ j : Fin N, ‖S (Pi.single j 1)‖) * ‖y‖ := by rw [Finset.sum_mul]

/-- The explicitly constructed linear map `y ↦ ∑ j, (y j) • s j` takes the standard basis vector
`Pi.single k 1` to `s k`. -/
theorem basis_apply {N : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : Fin N → F) (k : Fin N) :
    (∑ j : Fin N,
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) j).smulRight (s j))
      (Pi.single k 1) = s k := by
  rw [show (∑ j : Fin N,
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) j).smulRight (s j)) =
      (∑ j ∈ (Finset.univ : Finset (Fin N)),
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) j).smulRight (s j)) from rfl]
  rw [sum_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
    rw [Pi.single_eq_of_ne hj, zero_smul]
  · intro hk; exact absurd (Finset.mem_univ k) hk

/-- **Convergence of continuous linear maps from convergence on the standard basis.**  On the
finite dimensional space `Fin N → ℝ` a family of continuous linear maps converges in the operator
norm as soon as its values on all standard basis vectors `Pi.single j 1` converge. -/
theorem exists_tendsto_clm_of_tendsto_basis {N : ℕ} {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {α : Type*} {l : Filter α} (L : α → (Fin N → ℝ) →L[ℝ] F)
    {s : Fin N → F}
    (h : ∀ j : Fin N, Tendsto (fun a => L a (Pi.single j 1)) l (𝓝 (s j))) :
    ∃ T : (Fin N → ℝ) →L[ℝ] F, Tendsto L l (𝓝 T) := by
  let T : (Fin N → ℝ) →L[ℝ] F :=
    ∑ j : Fin N, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) j).smulRight (s j)
  have hT : ∀ k : Fin N, T (Pi.single k 1) = s k := fun k => basis_apply s k
  refine ⟨T, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero
    (f := fun a => ‖L a - T‖) (g := fun a => ∑ j : Fin N, ‖L a (Pi.single j 1) - s j‖)
    (fun a => norm_nonneg _) (fun a => ?_) ?_
  · calc ‖L a - T‖ ≤ ∑ j : Fin N, ‖(L a - T) (Pi.single j 1)‖ := clm_norm_le_sum_basis _
      _ = ∑ j : Fin N, ‖L a (Pi.single j 1) - s j‖ := by
          apply Finset.sum_congr rfl; intro j _
          rw [sub_apply, hT j]
  · have h2 : Tendsto (fun a => ∑ j : Fin N, ‖L a (Pi.single j 1) - s j‖) l
        (𝓝 (∑ j : Fin N, (0:ℝ))) := by
      apply tendsto_finsetSum
      intro j _
      have hj : Tendsto (fun a => ‖L a (Pi.single j 1) - s j‖) l (𝓝 0) := by
        have h1 : Tendsto (fun a => L a (Pi.single j 1) - s j) l (𝓝 0) := by
          simpa using (h j).sub (tendsto_const_nhds (x := s j))
        simpa using h1.norm
      simpa using hj
    simpa using h2

/-- **Splitting the last coordinate of an iterated derivative.**  Evaluating the `(m+1)`-st
iterated derivative of `g` on the coordinate directions `Fin.snoc w j` equals evaluating the
`m`-th iterated derivative of the derivative `y ↦ fderiv ℝ g y` on the first `m` coordinate
directions `w`, and then applying the resulting continuous linear map to `Pi.single j 1`. -/
theorem iteratedFDeriv_succ_apply_snoc {N m : ℕ} {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : (Fin N → ℝ) → F} {x : Fin N → ℝ}
    (w : Fin m → Fin N) (j : Fin N) :
    iteratedFDeriv ℝ (m + 1) g x
        (fun i => Pi.single ((Fin.snoc (α := fun _ => Fin N) w j) i) 1) =
      (iteratedFDeriv ℝ m (fun y => fderiv ℝ g y) x (fun i => Pi.single (w i) 1))
        (Pi.single j 1) := by
  rw [iteratedFDeriv_succ_apply_right]
  simp only [Fin.init_def, Fin.snoc_castSucc, Fin.snoc_last]

/-! ### The requested lemma -/

theorem TendstoIteratedFDerivFderiv {N m : ℕ} (hN : 1 ≤ N) {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : (Fin N → ℝ) → F} {u : Fin N → ℝ}
    (h : ∀ v : Fin (m + 1) → Fin N, ∃ s : F,
      Filter.Tendsto (fun x => iteratedFDeriv ℝ (m + 1) g x (fun i => Pi.single (v i) 1))
        (nhdsWithin u {u}ᶜ) (nhds s)) :
    ∀ v : Fin m → Fin N, ∃ s : (Fin N → ℝ) →L[ℝ] F,
      Filter.Tendsto (fun x => iteratedFDeriv ℝ m (fun y => fderiv ℝ g y) x
        (fun i => Pi.single (v i) 1)) (nhdsWithin u {u}ᶜ) (nhds s) := by
  intro w
  -- The limits along the words `Fin.snoc w j` give the coordinate functions of the limit.
  choose s hs using fun j : Fin N => h (Fin.snoc w j)
  have hbase : ∀ j : Fin N,
      Filter.Tendsto (fun x => (iteratedFDeriv ℝ m (fun y => fderiv ℝ g y) x
        (fun i => Pi.single (w i) 1)) (Pi.single j 1)) (nhdsWithin u {u}ᶜ) (nhds (s j)) := by
    intro j
    simpa only [iteratedFDeriv_succ_apply_snoc w j] using hs j
  obtain ⟨T, hT⟩ := exists_tendsto_clm_of_tendsto_basis
    (L := fun x => iteratedFDeriv ℝ m (fun y => fderiv ℝ g y) x (fun i => Pi.single (w i) 1))
    hbase
  exact ⟨T, hT⟩

end Work.WilG4c
