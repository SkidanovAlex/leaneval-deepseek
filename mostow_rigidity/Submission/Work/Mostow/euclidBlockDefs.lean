import Mathlib
import Submission.Work.Mostow.ellipticDefs

/-!
# Coordinate splitting of `E n` and the adapted orthonormal basis

Vocabulary for the Euclidean block normal form `Work.Mostow.euclid_block_normal_form`.

* `tailOf k u` : the last `n - k` coordinates of `u : E n`, as an element of `E (n - k)`;
* `splitFun` / `splitEquiv` : the order preserving identification `Fin n ≃ Fin k ⊕ Fin (n - k)`;
* `adaptedBasis` : given a submodule `V` of `E n` with an orthonormal basis of `V` and one of
  `Vᗮ`, the orthonormal basis of `E n` whose first `k` vectors lie in `V` and whose last
  `n - k` vectors lie in `Vᗮ`;
* `vblk_ofLp_of_lt` / `vblk_ofLp_of_ge` : the coordinates of `Work.Mostow.vblk`.
-/

namespace Work.Mostow

open Submission.Mostow

noncomputable section

variable {n : ℕ}

/-! ### The tail of a vector -/

/-- the last `n - k` coordinates of `u`, as an element of `E (n - k)` -/
def tailOf (k : ℕ) (u : E n) : E (n - k) :=
  WithLp.toLp 2 (fun j : Fin (n - k) => u.ofLp ⟨k + j.val, by have := j.isLt; omega⟩)

@[simp] theorem tailOf_ofLp (k : ℕ) (u : E n) (j : Fin (n - k)) :
    (tailOf k u).ofLp j = u.ofLp ⟨k + j.val, by have := j.isLt; omega⟩ := rfl

theorem tailOf_add (k : ℕ) (u v : E n) : tailOf k (u + v) = tailOf k u + tailOf k v := by
  apply WithLp.ofLp_injective
  funext j
  simp only [WithLp.ofLp_add, tailOf_ofLp, Pi.add_apply]

theorem tailOf_smul (k : ℕ) (c : ℝ) (u : E n) : tailOf k (c • u) = c • tailOf k u := by
  apply WithLp.ofLp_injective
  funext j
  simp only [WithLp.ofLp_smul, tailOf_ofLp, Pi.smul_apply]

theorem fin_castAdd_eq_iff (k : ℕ) (i : Fin n) (h : ¬ (i : ℕ) < k) (j : Fin (n - k)) :
    ((⟨k + j.val, by have := j.isLt; omega⟩ : Fin n) = i)
      ↔ (j = ⟨i.val - k, by have := i.isLt; omega⟩) := by
  constructor
  · intro hcon
    refine Fin.ext ?_
    show j.val = i.val - k
    have h2 : k + j.val = i.val := congrArg Fin.val hcon
    omega
  · intro hcon
    refine Fin.ext ?_
    show k + j.val = i.val
    have h2 : j.val = i.val - k := congrArg Fin.val hcon
    omega

theorem tailOf_single_of_lt (k : ℕ) (i : Fin n) (h : (i : ℕ) < k) :
    tailOf k (EuclideanSpace.single i (1 : ℝ)) = 0 := by
  apply WithLp.ofLp_injective
  funext j
  rw [tailOf_ofLp, PiLp.single_apply, PiLp.zero_apply]
  rw [if_neg]
  intro hcon
  have h2 : k + j.val = i.val := congrArg Fin.val hcon
  omega

theorem tailOf_single_of_ge (k : ℕ) (i : Fin n) (h : ¬ (i : ℕ) < k) :
    tailOf k (EuclideanSpace.single i (1 : ℝ))
      = EuclideanSpace.single ⟨i.val - k, by have := i.isLt; omega⟩ (1 : ℝ) := by
  apply WithLp.ofLp_injective
  funext j
  rw [tailOf_ofLp, PiLp.single_apply, PiLp.single_apply]
  by_cases hj : (⟨k + j.val, by have := j.isLt; omega⟩ : Fin n) = i
  · rw [if_pos hj, if_pos ((fin_castAdd_eq_iff k i h j).mp hj)]
  · rw [if_neg hj, if_neg]
    intro hcon
    exact hj ((fin_castAdd_eq_iff k i h j).mpr hcon)

/-! ### The index splitting -/

/-- the order preserving splitting `Fin n = Fin k ⊔ Fin (n-k)` -/
def splitFun (k n : ℕ) (hk : k ≤ n) (i : Fin n) : Fin k ⊕ Fin (n - k) :=
  if h : (i : ℕ) < k then Sum.inl ⟨i.val, h⟩
  else Sum.inr ⟨i.val - k, by have := i.isLt; omega⟩

theorem splitFun_of_lt (k n : ℕ) (hk : k ≤ n) (i : Fin n) (h : (i : ℕ) < k) :
    splitFun k n hk i = Sum.inl ⟨i.val, h⟩ := by
  simp only [splitFun, dif_pos h]

theorem splitFun_of_ge (k n : ℕ) (hk : k ≤ n) (i : Fin n) (h : ¬ (i : ℕ) < k) :
    splitFun k n hk i = Sum.inr ⟨i.val - k, by have := i.isLt; omega⟩ := by
  simp only [splitFun, dif_neg h]

/-- the order preserving equivalence `Fin n ≃ Fin k ⊕ Fin (n-k)` -/
def splitEquiv (k n : ℕ) (hk : k ≤ n) : Fin n ≃ Fin k ⊕ Fin (n - k) :=
  Equiv.ofBijective (splitFun k n hk)
    ⟨by
      intro i i' hii
      by_cases hi : (i : ℕ) < k <;> by_cases hi' : (i' : ℕ) < k
      · rw [splitFun_of_lt k n hk i hi, splitFun_of_lt k n hk i' hi'] at hii
        have : (⟨i.val, hi⟩ : Fin k) = ⟨i'.val, hi'⟩ := Sum.inl.inj hii
        exact Fin.ext (by simpa using congrArg Fin.val this)
      · rw [splitFun_of_lt k n hk i hi, splitFun_of_ge k n hk i' hi'] at hii
        exact absurd hii (by simp)
      · rw [splitFun_of_ge k n hk i hi, splitFun_of_lt k n hk i' hi'] at hii
        exact absurd hii (by simp)
      · rw [splitFun_of_ge k n hk i hi, splitFun_of_ge k n hk i' hi'] at hii
        have : (⟨i.val - k, _⟩ : Fin (n - k)) = ⟨i'.val - k, _⟩ := Sum.inr.inj hii
        have h2 : i.val - k = i'.val - k := congrArg Fin.val this
        have h3 : k ≤ i.val := Nat.le_of_not_lt hi
        have h4 : k ≤ i'.val := Nat.le_of_not_lt hi'
        exact Fin.ext (by omega),
     by
      intro s
      rcases s with a | c
      · refine ⟨⟨a.val, by omega⟩, ?_⟩
        rw [splitFun_of_lt k n hk _ a.isLt]
      · refine ⟨⟨k + c.val, by omega⟩, ?_⟩
        have h : ¬ (k + c.val) < k := by omega
        rw [splitFun_of_ge k n hk _ h]
        refine congrArg Sum.inr (Fin.ext ?_)
        simp⟩

theorem splitEquiv_apply (k n : ℕ) (hk : k ≤ n) (i : Fin n) :
    splitEquiv k n hk i = splitFun k n hk i := rfl

/-! ### The adapted orthonormal basis -/

/-- The orthonormal basis of `E n` whose first `k` vectors form `bV` and whose last `n - k`
vectors form `bW`. -/
def adaptedBasis (k : ℕ) (hk : k ≤ n) (V : Submodule ℝ (E n))
    (bV : OrthonormalBasis (Fin k) ℝ V) (bW : OrthonormalBasis (Fin (n - k)) ℝ Vᗮ) :
    OrthonormalBasis (Fin n) ℝ (E n) :=
  ((bV.prod bW).map V.orthogonalDecomposition.symm).reindex (splitEquiv k n hk).symm

theorem adaptedBasis_apply_left (k : ℕ) (hk : k ≤ n) (V : Submodule ℝ (E n))
    (bV : OrthonormalBasis (Fin k) ℝ V) (bW : OrthonormalBasis (Fin (n - k)) ℝ Vᗮ)
    (i : Fin n) (h : (i : ℕ) < k) :
    adaptedBasis k hk V bV bW i = ((bV ⟨i.val, h⟩ : V) : E n) := by
  rw [adaptedBasis, OrthonormalBasis.reindex_apply, OrthonormalBasis.map_apply,
    OrthonormalBasis.prod_apply]
  simp only [Equiv.symm_symm, splitEquiv_apply, splitFun_of_lt k n hk i h]
  simp [Submodule.orthogonalDecomposition_symm_apply]

theorem adaptedBasis_apply_right (k : ℕ) (hk : k ≤ n) (V : Submodule ℝ (E n))
    (bV : OrthonormalBasis (Fin k) ℝ V) (bW : OrthonormalBasis (Fin (n - k)) ℝ Vᗮ)
    (i : Fin n) (h : ¬ (i : ℕ) < k) :
    adaptedBasis k hk V bV bW i = ((bW ⟨i.val - k, by have := i.isLt; omega⟩ : Vᗮ) : E n) := by
  rw [adaptedBasis, OrthonormalBasis.reindex_apply, OrthonormalBasis.map_apply,
    OrthonormalBasis.prod_apply]
  simp only [Equiv.symm_symm, splitEquiv_apply, splitFun_of_ge k n hk i h]
  simp [Submodule.orthogonalDecomposition_symm_apply]

/-! ### Coordinates of `vblk` -/

theorem vblk_ofLp_of_lt (k : ℕ) (hk : k ≤ n) (R : E (n - k) ≃ₗᵢ[ℝ] E (n - k))
    (u : E n) (i : Fin n) (h : (i : ℕ) < k) :
    (vblk k hk R u).ofLp i = u.ofLp i := by
  simp [vblk, h]

theorem vblk_ofLp_of_ge (k : ℕ) (hk : k ≤ n) (R : E (n - k) ≃ₗᵢ[ℝ] E (n - k))
    (u : E n) (i : Fin n) (h : ¬ (i : ℕ) < k) :
    (vblk k hk R u).ofLp i
      = (R (tailOf k u)).ofLp ⟨i.val - k, by have := i.isLt; omega⟩ := by
  simp only [vblk, dite_eq_right h, tailOf]

end

end Work.Mostow
