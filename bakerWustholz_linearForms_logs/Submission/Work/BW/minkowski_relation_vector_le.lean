import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Minkowski's relation vector, non-strict form

`Work.BW.minkowski_relation_vector` gives, for `∏ i, c i > 1`, a nonzero integer vector `s`
with `|s k| ≤ c k` and `|t k · s j − s k · t j| ≤ |t k| · c j` for `j ≠ k`.  Here we prove the
boundary case `∏ i, c i ≥ 1` (the form actually consumed by `Work.BW.waldschmidt_relation_bound`).

The starting point is the compact (i.e. non-strict) Minkowski convex body theorem
`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure`: the body
`A⁻¹(∏ᵢ [−cᵢ, cᵢ])` is convex, symmetric, **compact**, and has volume `2ⁿ ∏ cᵢ / |det A|`,
which is `≥ 2ⁿ` as soon as `|det A| ≤ ∏ cᵢ`.  The relation statement is then the special case
`A = 1 + w ⊗ e k` (determinant `1`), exactly as in the strict file.
-/

namespace Work.BW

open MeasureTheory Module Matrix

/-- Volume of the closed box `∏ᵢ [−cᵢ, cᵢ]` in `ℝⁿ`. -/
lemma bwBoxVolume_closed {n : ℕ} (c : Fin n → ℝ) :
    volume (Set.pi Set.univ (fun i => Set.Icc (-(c i)) (c i)))
      = ∏ i, ENNReal.ofReal (2 * c i) := by
  rw [volume_pi, Measure.pi_pi]
  exact Finset.prod_congr rfl (fun i _ => by
    rw [Real.volume_Icc, show c i - -(c i) = 2 * c i by ring])

/-- The numerical inequality underlying the non-strict Minkowski linear forms theorem:
if `0 < cᵢ` and `|d| ≤ ∏ cᵢ` then `2ⁿ ≤ |d⁻¹| · ∏ (2 cᵢ)` (in `ENNReal`). -/
lemma bwEnnrealIneq_le {n : ℕ} (d : ℝ) (c : Fin n → ℝ) (hd : d ≠ 0)
    (hc : ∀ i, 0 < c i) (hprod : |d| ≤ ∏ i, c i) :
    (2 : ENNReal) ^ n ≤ ENNReal.ofReal |d⁻¹| * ∏ i, ENNReal.ofReal (2 * c i) := by
  have hmulprod : ∏ i : Fin n, (2 * c i) = (2:ℝ)^n * ∏ i, c i := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hdabs : 0 < |d| := abs_pos.mpr hd
  have hA : 0 < (2:ℝ)^n := by positivity
  have hnn : 0 ≤ |d⁻¹| * ∏ i : Fin n, (2 * c i) :=
    mul_nonneg (abs_nonneg _) (Finset.prod_nonneg (fun i _ => by linarith [hc i]))
  have hmain : (2:ℝ)^n ≤ |d⁻¹| * ∏ i : Fin n, (2 * c i) := by
    rw [abs_inv, hmulprod,
        show |d|⁻¹ * ((2:ℝ)^n * ∏ i, c i) = (2:ℝ)^n * (|d|⁻¹ * ∏ i, c i) by ring]
    rw [le_mul_iff_one_le_right hA, inv_mul_eq_div, one_le_div hdabs]
    exact hprod
  calc (2 : ENNReal) ^ n
      = ENNReal.ofReal ((2:ℝ)^n) := by
        rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)]; simp
    _ ≤ ENNReal.ofReal (|d⁻¹| * ∏ i : Fin n, (2 * c i)) := by
        rw [ENNReal.ofReal_le_ofReal_iff hnn]
        exact hmain
    _ = ENNReal.ofReal |d⁻¹| * ∏ i, ENNReal.ofReal (2 * c i) := by
        rw [ENNReal.ofReal_mul (abs_nonneg _),
            ENNReal.ofReal_prod_of_nonneg (fun i _ => by linarith [hc i])]

/-- **Minkowski's theorem on linear forms, non-strict form.**  For a nonsingular real `n × n`
matrix `A` and positive reals `c i` with `|det A| ≤ ∏ i, c i`, there is a nonzero integer
vector `x` with `|∑ j, A i j * x j| ≤ c i` for every `i`. -/
theorem minkowski_linear_forms_le {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) (hprod : |A.det| ≤ ∏ i, c i) :
    ∃ x : Fin n → ℤ, x ≠ 0 ∧ ∀ i, |∑ j, A i j * (x j : ℝ)| ≤ c i := by
  classical
  -- The lattice `ℤⁿ ⊆ ℝⁿ` and its unit fundamental domain.
  haveI : Countable ↥((Submodule.span ℤ
      (Set.range (Pi.basisFun ℝ (Fin n)))).toAddSubgroup) :=
    inferInstanceAs (Countable ↥(Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))))
  haveI : DiscreteTopology ↥((Submodule.span ℤ
      (Set.range (Pi.basisFun ℝ (Fin n)))).toAddSubgroup) := inferInstance
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  haveI : Nontrivial (Fin n → ℝ) := inferInstance
  have hFvol : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin n))) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi, Measure.pi_pi]
    simp [Real.volume_Ico]
  -- The linear map defined by `A` and the symmetric convex body.
  set f : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.toLin' A with hf
  have hfdet : LinearMap.det f = A.det := by rw [hf, LinearMap.det_toLin']
  have hfne : LinearMap.det f ≠ 0 := by rw [hfdet]; exact hA
  set s : Set (Fin n → ℝ) := {x | ∀ i, |(f x) i| ≤ c i} with hsd
  have hs_eq : s = f ⁻¹' (Set.pi Set.univ (fun i => Set.Icc (-(c i)) (c i))) := by
    ext x
    simp only [hsd, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      forall_true_left, Set.mem_Icc, abs_le]
  -- Symmetry.
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    simp only [hsd, Set.mem_ofPred_eq] at hx ⊢
    intro i
    rw [map_neg, Pi.neg_apply, abs_neg]
    exact hx i
  -- Convexity.
  have hconv : Convex ℝ s := by
    rw [hs_eq]
    exact (convex_pi (fun i _ => convex_Icc (-(c i)) (c i))).linear_preimage f
  -- Compactness (the new ingredient compared with the strict version).
  have hcpt : IsCompact s := by
    rw [hs_eq]
    have hker : LinearMap.ker f = ⊥ := by
      by_contra h
      exact hfne ((LinearMap.det_eq_zero_iff_ker_ne_bot).mpr h)
    exact (LinearMap.isClosedEmbedding_of_injective (f := f) hker).isCompact_preimage
      (isCompact_univ_pi (fun i => isCompact_Icc))
  -- Volume of the body.
  have hvol : volume s = ENNReal.ofReal |(A.det)⁻¹| * ∏ i, ENNReal.ofReal (2 * c i) := by
    have hpre : volume (f ⁻¹' (Set.pi Set.univ (fun i => Set.Icc (-(c i)) (c i))))
        = ENNReal.ofReal |(A.det)⁻¹| * ∏ i, ENNReal.ofReal (2 * c i) := by
      rw [Measure.addHaar_preimage_linearMap volume hfne
            (Set.pi Set.univ (fun i => Set.Icc (-(c i)) (c i))), hfdet, bwBoxVolume_closed]
    rw [hs_eq, hpre]
  -- The Minkowski volume inequality.
  have hineq : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin n)))
      * 2 ^ Module.finrank ℝ (Fin n → ℝ) ≤ volume s := by
    rw [hFvol, one_mul, hvol, Module.finrank_fin_fun]
    exact bwEnnrealIneq_le A.det c hA hc hprod
  -- Minkowski's (non-strict) convex body theorem.
  obtain ⟨x0, hx0ne, hx0mem⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      (ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin n)) volume) hsymm hconv hcpt hineq
  -- Extract the integer coordinates of `x0`.
  have hcoord : ∀ i, ∃ z : ℤ, (x0 : Fin n → ℝ) i = (z : ℝ) := by
    intro i
    have hmem : (x0 : Fin n → ℝ)
        ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) := by
      simpa using x0.2
    have h := (Module.Basis.mem_span_iff_repr_mem ℤ (Pi.basisFun ℝ (Fin n))
        (x0 : Fin n → ℝ)).mp hmem i
    obtain ⟨z, hz⟩ := h
    refine ⟨z, ?_⟩
    rw [Pi.basisFun_repr] at hz
    simpa using hz.symm
  choose z hz using hcoord
  refine ⟨z, ?_, ?_⟩
  · -- `z ≠ 0`
    intro hz0
    exact hx0ne (by
      apply Subtype.ext
      funext i
      rw [hz i, hz0]
      simp)
  · -- the size estimates
    intro i
    have hmem : ∀ i, |(f (x0 : Fin n → ℝ)) i| ≤ c i := by
      simpa [hsd, Set.mem_ofPred_eq] using hx0mem
    have hfi : (f (x0 : Fin n → ℝ)) i = ∑ j, A i j * (x0 : Fin n → ℝ) j := by
      rw [hf, Matrix.toLin'_apply, Matrix.mulVec_apply_eq_sum]
    calc |∑ j, A i j * (z j : ℝ)|
        = |∑ j, A i j * (x0 : Fin n → ℝ) j| := by
          congr 1
          exact Finset.sum_congr rfl (fun j _ => by rw [← hz j])
      _ = |(f (x0 : Fin n → ℝ)) i| := by rw [hfi]
      _ ≤ c i := hmem i

/-- **Minkowski's relation vector, non-strict form** (`Work.BW.minkowski_relation_vector_le`).

Given integers `t : Fin M → ℤ` with `t k ≠ 0` and positive reals `c` with `∏ i, c i ≥ 1`,
there is a nonzero integer vector `s` with

* `|s k| ≤ c k`, and
* `|t k · s j − s k · t j| ≤ |t k| · c j` for every `j ≠ k`. -/
theorem minkowski_relation_vector_le {M : ℕ} (t : Fin M → ℤ) (k : Fin M) (htk : t k ≠ 0)
    (c : Fin M → ℝ) (hc : ∀ i, 0 < c i) (hprod : 1 ≤ ∏ i, c i) :
    ∃ s : Fin M → ℤ, s ≠ 0 ∧ |(s k : ℝ)| ≤ c k ∧
      ∀ j : Fin M, j ≠ k →
        |((t k : ℤ) : ℝ) * (s j : ℝ) - (s k : ℝ) * ((t j : ℤ) : ℝ)|
          ≤ |((t k : ℤ) : ℝ)| * c j := by
  classical
  -- The rank-one vector `u` (equal to `t i / t k` off `k`, and `0` at `k`),
  -- and the elementary vector `r = e k`.
  let r : Fin M → ℝ := fun j => if j = k then 1 else 0
  let w : Fin M → ℝ := fun i => -(if i = k then 0 else ((t i : ℤ) : ℝ) / ((t k : ℤ) : ℝ))
  -- The matrix `A = 1 - u ⊗ e k`: row `k` is `e k`, row `i ≠ k` is `e i − (t i / t k) e k`.
  let A : Matrix (Fin M) (Fin M) ℝ := 1 + Matrix.replicateCol Unit w * Matrix.replicateRow Unit r
  -- Its determinant is `1`.
  have hdet : A.det = 1 := by
    show (1 + Matrix.replicateCol Unit w * Matrix.replicateRow Unit r).det = 1
    rw [Matrix.det_one_add_replicateCol_mul_replicateRow]
    have hdot : r ⬝ᵥ w = 0 := by
      rw [dotProduct]
      apply Finset.sum_eq_zero
      intro x _
      by_cases h : x = k
      · subst h; simp [r, w]
      · simp [r, w, h]
    rw [hdot]; norm_num
  have hAne : A.det ≠ 0 := by rw [hdet]; norm_num
  have hprod' : |A.det| ≤ ∏ i, c i := by rw [hdet]; simpa using hprod
  -- Minkowski's linear forms theorem (non-strict).
  obtain ⟨x, hx0, hx⟩ := minkowski_linear_forms_le k.pos A hAne c hc hprod'
  -- Entries of `A`.
  have hAij : ∀ i j : Fin M, A i j = (if i = j then (1:ℝ) else 0) + w i * r j := by
    intro i j
    simp [A, Matrix.mul_apply, Matrix.one_apply]
  have hwk : w k = 0 := by simp [w]
  have hwj : ∀ j : Fin M, j ≠ k → w j = -(((t j : ℤ):ℝ) / ((t k:ℤ):ℝ)) := by
    intro j hj; simp [w, hj]
  -- Evaluation of the linear forms on `x`.
  have hsum : ∀ i, ∑ j, A i j * (x j : ℝ) = (x i : ℝ) + w i * (x k : ℝ) := by
    intro i
    have h1 : ∑ j, A i j * (x j : ℝ)
        = ∑ j, ((if i = j then (1:ℝ) else 0) * (x j : ℝ)) + ∑ j, w i * r j * (x j : ℝ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hAij i j]; ring
    rw [h1]
    have h2 : ∑ j, (if i = j then (1:ℝ) else 0) * (x j : ℝ) = (x i : ℝ) := by
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq]; simp
    have h3 : ∑ j, w i * r j * (x j : ℝ) = w i * (x k : ℝ) := by
      have h3a : ∑ j, w i * r j * (x j : ℝ) = ∑ j, w i * (r j * (x j : ℝ)) := by
        refine Finset.sum_congr rfl (fun j _ => by ring)
      rw [h3a, ← Finset.mul_sum]
      congr 1
      simp only [r, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq']; simp
    rw [h2, h3]
  refine ⟨x, hx0, ?_, ?_⟩
  · -- `|x k| ≤ c k`
    have hk := hx k
    rw [hsum k] at hk
    rw [hwk] at hk
    simpa using hk
  · -- the determinant-type bound
    intro j hj
    have hj' := hx j
    rw [hsum j, hwj j hj] at hj'
    have hT : ((t k : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr htk
    have hkey : ((t k : ℤ) : ℝ) * (x j : ℝ) - (x k : ℝ) * ((t j : ℤ) : ℝ)
        = ((t k : ℤ) : ℝ) * ((x j : ℝ) - (((t j : ℤ) : ℝ) / ((t k : ℤ) : ℝ)) * (x k : ℝ)) := by
      field_simp
    rw [hkey, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    convert hj' using 1
    ring_nf

end Work.BW
