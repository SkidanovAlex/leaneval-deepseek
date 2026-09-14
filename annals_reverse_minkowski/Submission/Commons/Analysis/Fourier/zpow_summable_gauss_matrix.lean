import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Lattice.Summable.summable_exp_neg_mul_norm_sq

open scoped BigOperators
open Matrix

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace Commons.Analysis.Fourier

noncomputable section

namespace ZpowSummableGaussMatrix

variable {n : ℕ}

abbrev E (n : ℕ) := Fin n → ℝ

/-- `M.mulVec` as a linear equivalence when `M.det ≠ 0`. -/
def matrixMulVecLinearEquiv (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.det ≠ 0) :
    E n ≃ₗ[ℝ] E n where
  toFun := fun v => M.mulVec v
  invFun := fun v => M⁻¹.mulVec v
  map_add' := by
    intro x y
    exact M.mulVec_add x y
  map_smul' := by
    intro r x
    exact M.mulVec_smul r x
  left_inv := by
    intro x
    dsimp
    rw [Matrix.mulVec_mulVec]
    rw [Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM)]
    simp
  right_inv := by
    intro x
    dsimp
    rw [Matrix.mulVec_mulVec]
    rw [Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM)]
    simp

@[simp] lemma matrixMulVecLinearEquiv_apply (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.det ≠ 0)
    (v : E n) : matrixMulVecLinearEquiv M hM v = M.mulVec v := rfl

/-- The standard full integer lattice inside `Fin n → ℝ`: all functions with integer values. -/
def stdLattice (n : ℕ) : Submodule ℤ (E n) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))

instance instDiscreteTopology_stdLattice (n : ℕ) : DiscreteTopology (stdLattice n) := by
  dsimp [stdLattice]
  exact ZSpan.discreteTopology_pi_basisFun (ι := Fin n)

/-- An integer vector, embedded in `Fin n → ℝ`. -/
def intVec (m : Fin n → ℤ) : E n := fun j : Fin n => (m j : ℝ)

lemma intVec_mem_stdLattice (m : Fin n → ℤ) : intVec m ∈ stdLattice n := by
  change (fun j : Fin n => (m j : ℝ)) ∈ stdLattice n
  dsimp [stdLattice]
  rw [Module.Basis.mem_span_iff_repr_mem (R := ℤ) (S := ℝ) (M := E n)
      (b := Pi.basisFun ℝ (Fin n)) (m := fun j : Fin n => (m j : ℝ))]
  intro i
  rw [Pi.basisFun_repr]
  exact ⟨m i, rfl⟩

/-- The canonical inclusion of the integer vectors into the standard lattice. -/
def intVecLattice (m : Fin n → ℤ) : stdLattice n :=
  ⟨intVec m, intVec_mem_stdLattice m⟩

/-- The type of integer vectors is in bijection with the standard lattice. -/
def stdLatticeEquiv (n : ℕ) : (Fin n → ℤ) ≃ stdLattice n := Equiv.ofBijective
  (intVecLattice (n := n))
  (by
    constructor
    · intro a b h
      apply funext
      intro j
      have hval := congrArg Subtype.val h
      have h' := congr_fun hval j
      change (a j : ℝ) = (b j : ℝ) at h'
      exact Int.cast_injective h'
    · intro x
      have hx : (x : E n) ∈ stdLattice n := x.2
      have hcoords : ∀ i : Fin n, (x : E n) i ∈ Set.range (algebraMap ℤ ℝ) := by
        intro i
        have hb := (Module.Basis.mem_span_iff_repr_mem (R := ℤ) (S := ℝ) (M := E n)
            (b := Pi.basisFun ℝ (Fin n)) (m := (x : E n))).mp hx
        simpa [Pi.basisFun_repr] using hb i
      let m : Fin n → ℤ := fun i => Classical.choose (hcoords i)
      refine ⟨m, ?_⟩
      apply Subtype.ext
      funext j
      change algebraMap ℤ ℝ (m j) = (x : E n) j
      dsimp [m]
      exact Classical.choose_spec (hcoords j))

/-- For functions `Fin n → ℝ`, `‖w‖² ≤ ∑ᵢ (w i)²` (the `ℓ∞` norm is no larger than `ℓ²`). -/
lemma norm_sq_le_sum_sq (w : E n) : ‖w‖ ^ 2 ≤ ∑ i : Fin n, (w i) ^ 2 := by
  let r : ℝ := Real.sqrt (∑ i : Fin n, (w i) ^ 2)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hle_i : ∀ i : Fin n, |w i| ≤ r := by
    intro i
    have hterm : (w i) ^ 2 ≤ ∑ j : Fin n, (w j) ^ 2 := by
      exact Finset.single_le_sum (fun j hj => sq_nonneg (w j)) (Finset.mem_univ i)
    calc
      |w i| = Real.sqrt ((w i) ^ 2) := by rw [Real.sqrt_sq_eq_abs]
      _ ≤ r := by
        dsimp [r]
        exact Real.sqrt_le_sqrt hterm
  have hnorm : ‖w‖ ≤ r := by
    rw [pi_norm_le_iff_of_nonneg hr0]
    intro i
    simpa using hle_i i
  have hnn : 0 ≤ ‖w‖ := norm_nonneg _
  have hr2 : r ^ 2 = ∑ i : Fin n, (w i) ^ 2 := by
    dsimp [r]
    rw [Real.sq_sqrt]
    exact Finset.sum_nonneg (fun i hi => sq_nonneg (w i))
  calc
    ‖w‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hnn hnorm 2
    _ = ∑ i : Fin n, (w i) ^ 2 := hr2

end ZpowSummableGaussMatrix

open ZpowSummableGaussMatrix

/-- For an invertible real `n × n` matrix `M` and `0 < c`, the Gaussian family
`m ↦ exp (-c · Σᵢ (M·m)ᵢ²)` is summable over `m : ℤⁿ = Fin n → ℤ`.  (Here `(M·m)ᵢ` means
`(M.mulVec fun j => (m j : ℝ)) i`.)  This double-exponential decay on the lattice follows for
instance from comparing with a lattice sum of the form `∑ exp (-c'·‖z‖²)` over a discrete
`ℤ`-submodule of `EuclideanSpace ℝ (Fin n)` (`Mathlib.Algebra.Module.ZLattice.Summable`,
`ZLattice.summable_norm_pow_inv`), after reindexing the bijection `m ↦ M·m`.) -/
theorem zpow_summable_gauss_matrix (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.det ≠ 0)
    (c : ℝ) (hc : 0 < c) :
    Summable (fun m : Fin n → ℤ =>
      Real.exp (-c * (∑ i, ((M.mulVec fun j : Fin n => (m j : ℝ)) i) ^ 2))) := by
  classical
  let A : E n ≃ₗ[ℝ] E n := matrixMulVecLinearEquiv M hM
  let Acl : E n ≃L[ℝ] E n := A.symm.toContinuousLinearEquiv
  let L : Submodule ℤ (E n) := ZLattice.comap ℝ (stdLattice n) (Acl : E n →ₗ[ℝ] E n)
  letI : DiscreteTopology L := by
    dsimp [L]
    exact ZLattice.comap_discreteTopology (K := ℝ) (L := stdLattice n)
      (e := (Acl : E n →ₗ[ℝ] E n)) Acl.continuous Acl.injective
  -- Gaussian over the image lattice L
  let g : L → ℝ := fun z => Real.exp (-c * ‖(z : E n)‖ ^ 2)
  have hsum_g : Summable g := by
    dsimp [g]
    exact Commons.Lattice.Summable.summable_exp_neg_mul_norm_sq (E := E n) (L := L) (c := c) hc
  -- equivalence between the standard lattice and the image lattice
  let f : stdLattice n → L := fun x => ⟨(A : E n → E n) (x : E n), by
      dsimp [L]
      change (Acl : E n →ₗ[ℝ] E n) (A (x : E n)) ∈ stdLattice n
      simpa [Acl] using x.2⟩
  let ginv : L → stdLattice n := fun y => ⟨(A.symm : E n → E n) (y : E n), by
      exact y.2⟩
  have hf_bij : Function.Bijective f := by
    constructor
    · intro x₁ x₂ h
      apply Subtype.ext
      exact A.injective (congrArg Subtype.val h)
    · intro y
      refine ⟨ginv y, ?_⟩
      apply Subtype.ext
      change (A : E n → E n) ((A.symm : E n → E n) (y : E n)) = (y : E n)
      exact A.apply_symm_apply (y : E n)
  let ce : stdLattice n ≃ L := Equiv.ofBijective f hf_bij
  -- pull back the sum over the image lattice to the integer vectors
  let φ : (Fin n → ℤ) ≃ L := (stdLatticeEquiv n).trans ce
  have hφ : ∀ m : Fin n → ℤ, (φ m : E n) = M.mulVec (fun j : Fin n => (m j : ℝ)) := by
    intro m
    calc
      (φ m : E n) = (ce (stdLatticeEquiv n m) : E n) := by rfl
      _ = A ((stdLatticeEquiv n m : E n)) := by rfl
      _ = A (intVec m) := by rfl
      _ = M.mulVec (intVec m) := by simp [A]
      _ = M.mulVec (fun j : Fin n => (m j : ℝ)) := by rfl
  have hsum_phi :
      Summable (fun m : Fin n → ℤ => Real.exp (-c * ‖((φ m) : E n)‖ ^ 2)) := by
    change Summable (g ∘ ⇑φ)
    exact (Equiv.summable_iff (f := g) (e := φ)).mpr hsum_g
  -- pointwise domination of the target by the pulled-back Gaussian
  refine Summable.of_nonneg_of_le (fun m => (Real.exp_pos _).le) ?_ hsum_phi
  intro m
  rw [hφ m]
  rw [Real.exp_le_exp]
  have hle := norm_sq_le_sum_sq (M.mulVec (fun j : Fin n => (m j : ℝ)))
  have hc0 : 0 ≤ c := le_of_lt hc
  have hmul : c * ‖M.mulVec (fun j : Fin n => (m j : ℝ))‖ ^ 2 ≤
      c * (∑ i : Fin n, (M.mulVec (fun j : Fin n => (m j : ℝ)) i) ^ 2) :=
    mul_le_mul_of_nonneg_left hle hc0
  nlinarith

end

end Commons.Analysis.Fourier