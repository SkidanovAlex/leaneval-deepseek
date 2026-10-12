import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseSym.Minimiser.minimiser_set_linear
import Submission.Work.BoseSym.Perm.dirForm_permAmb
import Submission.Work.BoseSym.Perm.permAmb_mem_Hsub
import Submission.Work.BoseSym.Perm.symAvgAmb_mem_Hsub
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym.Minimiser — the minimiser set is invariant under symmetrisation

The Dirichlet form `dirForm W p = gSq p + potSq W p` and the `L²` norm-squared
`l2Sq p = ‖p.1‖²` are quadratic forms on the ambient space `Amb N`, so the
defect

`R p = dirForm W p - lam * l2Sq p`

is a quadratic form as well.  If `lam` is a lower bound for `R` on the energy
space `Hsub N L`, then the set of points of `Hsub N L` at which the bound is
attained is a linear subspace: it is closed under `+` and `-`
(`Minimiser.minimiser_set_linear`, the parallelogram argument) and under
scalar multiples (homogeneity `R (c • p) = c² * R p`).

The symmetrisation average

`symAvgAmb N p = (N!)⁻¹ • ∑_σ permAmb N σ p`

is therefore a minimiser whenever `p` is one: each permuted point `permAmb N σ p`
is a minimiser because both `dirForm W` and `l2Sq` are invariant under the
particle permutation (for a permutation-invariant `W`), a finite sum of
minimisers is a minimiser, and a scalar multiple of a minimiser is a minimiser.

The scalar homogeneity of the four ingredients is proved below by direct
computation on the `L²` representatives; `l2Sq` and `gSq` are sums of squared
norms, while `potSq W (c • x) = c² * potSq W x` follows from the almost
everywhere description of the scalar multiple of an `L²` class
(`Lp.coeFn_smul`) and `integral_const_mul`.

## Main result

* `minimiser_set_symAvg` : the symmetrisation average of a minimiser is a
  minimiser.
-/

namespace Work.BoseSym.Minimiser

open MeasureTheory Filter
open Work.BoseSym.Perm

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Scalar homogeneity of the ingredients of the Dirichlet form -/

/-- The squared `L²` norm is homogeneous of degree two. -/
lemma l2Sq_smul_amb {N : ℕ} (c : ℝ) (x : Amb N) : l2Sq (c • x) = c ^ 2 * l2Sq x := by
  simp only [l2Sq, Prod.smul_fst, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-- The squared gradient norm is homogeneous of degree two. -/
lemma gSq_smul_amb {N : ℕ} (c : ℝ) (x : Amb N) : gSq (c • x) = c ^ 2 * gSq x := by
  simp only [gSq, Prod.smul_snd, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [Finset.mul_sum]

/-- The squared `L²` norm vanishes at the origin. -/
lemma l2Sq_zero_amb {N : ℕ} : l2Sq (0 : Amb N) = 0 := by simp [l2Sq]

/-- The weighted quadratic form `potSq W` is homogeneous of degree two. -/
lemma potSq_smul_amb {N : ℕ} {W : Conf N → ℝ} (c : ℝ) (x : Amb N) :
    potSq W (c • x) = c ^ 2 * potSq W x := by
  simp only [potSq, Prod.smul_fst]
  -- the `L²` representative of the scalar multiple is the pointwise scalar multiple
  have hcoe : ((c • x.1 : L2 N) : Conf N → ℝ) =ᵐ[volC N]
      fun y => c * (x.1 : Conf N → ℝ) y := by
    filter_upwards [Lp.coeFn_smul c x.1] with y hy
    rw [hy, Pi.smul_apply, smul_eq_mul]
  rw [show (∫ y, W y * ((c • x.1 : L2 N) : Conf N → ℝ) y ^ 2)
        = ∫ y, W y * (c * (x.1 : Conf N → ℝ) y) ^ 2 from by
      refine integral_congr_ae ?_
      filter_upwards [hcoe] with y hy
      rw [hy]]
  -- pull the constant `c ^ 2` out of the integral
  rw [show (∫ y, W y * (c * (x.1 : Conf N → ℝ) y) ^ 2)
        = ∫ y, c ^ 2 * (W y * (x.1 : Conf N → ℝ) y ^ 2) from by
      refine integral_congr_ae (Eventually.of_forall fun y => by ring)]
  rw [integral_const_mul]

/-- The Dirichlet form is homogeneous of degree two. -/
lemma dirForm_smul_amb {N : ℕ} {W : Conf N → ℝ} (c : ℝ) (x : Amb N) :
    dirForm W (c • x) = c ^ 2 * dirForm W x := by
  simp only [dirForm, gSq_smul_amb, potSq_smul_amb]
  ring

/-- The Dirichlet form vanishes at the origin. -/
lemma dirForm_zero_amb {N : ℕ} (W : Conf N → ℝ) : dirForm W (0 : Amb N) = 0 := by
  have hp : potSq W (0 : Amb N) = 0 := by
    simp only [potSq]
    have hcoe : (((0 : Amb N).1) : Conf N → ℝ) =ᵐ[volC N] (0 : Conf N → ℝ) :=
      Lp.coeFn_zero ℝ 2 (volC N)
    have h : (fun x => W x * (((0 : Amb N).1) : Conf N → ℝ) x ^ 2)
        =ᵐ[volC N] fun x => (0 : ℝ) := by
      filter_upwards [hcoe] with x hx
      rw [hx, Pi.zero_apply]
      ring
    rw [integral_congr_ae h]
    simp
  have hg : gSq (0 : Amb N) = 0 := by simp [gSq]
  rw [dirForm, hg, hp, add_zero]

/-! ## The main result -/

theorem minimiser_set_symAvg {N : ℕ} (L : ℝ) {W : Conf N → ℝ}
    (hWperm : ∀ σ x, W (tauPerm N σ x) = W x) {C : ℝ} (hW : BddBy N W C)
    (hWm : AEMeas N W) (lam : ℝ)
    (hmin : ∀ p : Hsub N L, lam * l2Sq (p : Amb N) ≤ dirForm W (p : Amb N))
    {p : Amb N} (hp : p ∈ Hsub N L) (hpm : dirForm W p = lam * l2Sq p) :
    dirForm W (symAvgAmb N p) = lam * l2Sq (symAvgAmb N p) := by
  classical
  -- Every permuted point of the orbit of `p` is a minimiser.
  have hperm : ∀ σ : Equiv.Perm (Fin N),
      dirForm W (permAmb N σ p) = lam * l2Sq (permAmb N σ p) := by
    intro σ
    rw [dirForm_permAmb hWperm σ p, l2Sq_permAmb σ p, hpm]
  -- A finite sum of minimisers is a minimiser (parallelogram argument).
  have hsum : ∀ s : Finset (Equiv.Perm (Fin N)),
      dirForm W (∑ σ ∈ s, permAmb N σ p) = lam * l2Sq (∑ σ ∈ s, permAmb N σ p) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [dirForm_zero_amb, l2Sq_zero_amb]
    | insert σ t hσ ih =>
        rw [Finset.sum_insert hσ]
        exact (minimiser_set_linear L hW hWm hmin
          ⟨permAmb N σ p, permAmb_mem_Hsub σ hp⟩
          ⟨∑ τ ∈ t, permAmb N τ p, Submodule.sum_mem _ fun τ _ => permAmb_mem_Hsub τ hp⟩
          (hperm σ) ih).1
  have hS := hsum Finset.univ
  -- `symAvgAmb N p` is a scalar multiple of that sum, and the form is homogeneous.
  have key : dirForm W ((Nat.factorial N : ℝ)⁻¹ •
      (∑ σ : Equiv.Perm (Fin N), permAmb N σ p))
      = lam * l2Sq ((Nat.factorial N : ℝ)⁻¹ •
        (∑ σ : Equiv.Perm (Fin N), permAmb N σ p)) := by
    rw [dirForm_smul_amb, l2Sq_smul_amb, hS]
    ring
  have hdef : symAvgAmb N p
      = (Nat.factorial N : ℝ)⁻¹ • (∑ σ : Equiv.Perm (Fin N), permAmb N σ p) := rfl
  rw [hdef]
  exact key

end

end Work.BoseSym.Minimiser
