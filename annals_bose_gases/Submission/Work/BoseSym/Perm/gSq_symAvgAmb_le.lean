import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The symmetrisation average does not increase the gradient energy

The symmetrisation average of an element `p` of the ambient space is

`symAvgAmb N p = (N!)⁻¹ • ∑_σ permAmb N σ p`,

the average of the permutation orbit of `p`.  Since `gSq` is a sum of squared
norms of the gradient components, it is convex, and since every `permAmb N σ`
is an isometry for `gSq` (`gSq_permAmb`), the average of isometries is a
contraction:

`gSq (symAvgAmb N p) ≤ gSq p`.

The formal proof follows the triangle-inequality (i.e. Jensen) route, with the
Cauchy–Schwarz inequality over the finite group `Equiv.Perm (Fin N)` supplying
the constant:

* `gSq` of a finite sum of ambient vectors is at most `card` times the sum of
  the `gSq`'s of the summands (`gSq_sum_le`), a consequence of
  `‖∑ v_i‖² ≤ card * ∑ ‖v_i‖²` for a normed group
  (`norm_sum_sq_le_card_mul_sum_norm_sq`);
* `gSq` is quadratic under scalar multiplication, `gSq (c • p) = c² * gSq p`
  (`gSq_smul`).

Applying the first with the `N!` summands `permAmb N σ p` and the second with
`c = (N!)⁻¹` gives `gSq (symAvgAmb N p) ≤ (N!)⁻² · (N!)² · gSq p = gSq p`.
-/

namespace Work.BoseSym.Perm

/-! ## Auxiliary estimates -/

/-- **The squared norm of a finite sum.**  In a seminormed additive group, the
squared norm of a finite sum is bounded by the number of terms times the sum of
the squared norms of the terms (a form of Cauchy–Schwarz). -/
private lemma norm_sum_sq_le_card_mul_sum_norm_sq {ι : Type*} {E : Type*}
    [SeminormedAddCommGroup E] (s : Finset ι) (v : ι → E) :
    ‖∑ i ∈ s, v i‖ ^ 2 ≤ ((s.card : ℕ) : ℝ) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  calc ‖∑ i ∈ s, v i‖ ^ 2 ≤ (∑ i ∈ s, ‖v i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s v) 2
    _ = (∑ i ∈ s, (1 : ℝ) * ‖v i‖) ^ 2 := by simp
    _ ≤ (∑ i ∈ s, (1 : ℝ) ^ 2) * ∑ i ∈ s, ‖v i‖ ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq s _ _
    _ = ((s.card : ℕ) : ℝ) * ∑ i ∈ s, ‖v i‖ ^ 2 := by simp

/-- `gSq` is homogeneous of degree two. -/
private lemma gSq_smul {N : ℕ} (c : ℝ) (p : Amb N) : gSq (c • p) = c ^ 2 * gSq p := by
  simp only [gSq, Prod.smul_snd, Pi.smul_apply, norm_smul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mul_pow, Real.norm_eq_abs, sq_abs]

/-- `gSq` is subadditive up to the number of summands: the squared gradient
energy of a finite sum of ambient vectors is at most `card` times the sum of
the squared gradient energies of the summands. -/
private lemma gSq_sum_le {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Amb N) :
    gSq (∑ i ∈ s, f i) ≤ ((s.card : ℕ) : ℝ) * ∑ i ∈ s, gSq (f i) := by
  have h1 : ∀ j : GIdx N,
      ‖(∑ i ∈ s, f i).2 j‖ ^ 2 ≤ ((s.card : ℕ) : ℝ) * ∑ i ∈ s, ‖(f i).2 j‖ ^ 2 := by
    intro j
    rw [Prod.snd_sum, Finset.sum_apply]
    exact norm_sum_sq_le_card_mul_sum_norm_sq s (fun i => (f i).2 j)
  simp only [gSq]
  calc ∑ j, ‖(∑ i ∈ s, f i).2 j‖ ^ 2
      ≤ ∑ j, (((s.card : ℕ) : ℝ) * ∑ i ∈ s, ‖(f i).2 j‖ ^ 2) :=
        Finset.sum_le_sum (fun j _ => h1 j)
    _ = ((s.card : ℕ) : ℝ) * ∑ j, ∑ i ∈ s, ‖(f i).2 j‖ ^ 2 := by rw [Finset.mul_sum]
    _ = ((s.card : ℕ) : ℝ) * ∑ i ∈ s, ∑ j, ‖(f i).2 j‖ ^ 2 := by rw [Finset.sum_comm]
    _ = ((s.card : ℕ) : ℝ) * ∑ i ∈ s, gSq (f i) := rfl

/-! ## The symmetrisation average -/

/-- The symmetrisation average does not increase the gradient energy: it is the
average of the isometries `permAmb N σ`, hence a contraction for `gSq`. -/
theorem gSq_symAvgAmb_le {N : ℕ} (p : Work.BoseSym.Amb N) :
    Work.BoseSym.gSq (Work.BoseSym.symAvgAmb N p) ≤ Work.BoseSym.gSq p := by
  have hcard : (((Finset.univ : Finset (Equiv.Perm (Fin N))).card : ℕ) : ℝ) =
      (Nat.factorial N : ℝ) := by
    simp [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  -- The group average is bounded by `(N!)² gSq p`, by Cauchy–Schwarz over the group
  -- and the invariance `gSq (permAmb N σ p) = gSq p`.
  have h1 : gSq (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin N))), permAmb N σ p)
      ≤ (Nat.factorial N : ℝ) * (Nat.factorial N : ℝ) * gSq p := by
    have hmain := gSq_sum_le (Finset.univ : Finset (Equiv.Perm (Fin N)))
      (fun σ => permAmb N σ p)
    rw [hcard] at hmain
    refine hmain.trans ?_
    have hperm : (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin N))),
          gSq (permAmb N σ p)) = (Nat.factorial N : ℝ) * gSq p := by
      rw [Finset.sum_congr rfl (fun σ _ => gSq_permAmb σ p)]
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
    rw [hperm]
    apply le_of_eq
    ring
  -- Unfold the average and use homogeneity of degree two.
  have h2 : gSq (symAvgAmb N p) = ((Nat.factorial N : ℝ)⁻¹) ^ 2 *
      gSq (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin N))), permAmb N σ p) := by
    rw [symAvgAmb, gSq_smul]
  rw [h2]
  calc ((Nat.factorial N : ℝ)⁻¹) ^ 2 *
        gSq (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin N))), permAmb N σ p)
      ≤ ((Nat.factorial N : ℝ)⁻¹) ^ 2 *
        ((Nat.factorial N : ℝ) * (Nat.factorial N : ℝ) * gSq p) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = gSq p := by
        have hfact : ((Nat.factorial N : ℝ)) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero N
        field_simp

end Work.BoseSym.Perm
