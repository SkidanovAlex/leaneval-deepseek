import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.HP3.dmin_two_singleton_pos
import Submission.Work.HP.HP3.dmin_le_norm_mul_dual
import Submission.Work.HP.detgam_span_pair_wedgeNorm
import Submission.Work.HP.MinkDefs

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.HP.MM2

/-- For `n ≥ 1` and a nonzero integer vector `x : Fin (n+1) → ℤ`, the least determinant
`𝔡₂(x) = dmin 2 {x}` of a rank-`2` sublattice of `ℤ^{n+1}` containing `x` is at most `‖x‖`.

Choose a coordinate `j` with `x j ≠ 0` and an index `k ≠ j` (possible since `card (Fin (n+1)) ≥ 2`
because `n ≥ 1`); then `x` and the standard basis vector `e_k` are `ℤ`-linearly independent and

`detL (span ℤ {x, e_k}) = wedgeNorm x e_k = √(‖x‖²‖e_k‖² − ⟨x,e_k⟩²) ≤ ‖x‖‖e_k‖ = ‖x‖`. -/
theorem dmin_two_singleton_le_eNorm (n : ℕ) (hn : 1 ≤ n) (x : Fin (n + 1) → ℤ) (hx : x ≠ 0) :
    dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ eNorm x := by
  classical
  -- a nonzero coordinate of `x`
  obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), x j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hx (funext h)
  -- a second index `k ≠ j` (there is one since `card (Fin (n+1)) = n + 1 ≥ 2`)
  obtain ⟨k, hk⟩ : ∃ k : Fin (n + 1), k ≠ j := by
    refine Fintype.exists_ne_of_one_lt_card ?_ j
    rw [Fintype.card_fin]; omega
  -- the standard basis vector `e_k`
  let e : Fin (n + 1) → ℤ := Pi.single k 1
  have hek : e k = 1 := by simp [e]
  have hej : e j = 0 := by simp [e, Ne.symm hk]
  -- `x` and `e_k` are `ℤ`-linearly independent
  have hli : LinearIndependent ℤ (![x, e] : Fin 2 → (Fin (n + 1) → ℤ)) := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have hj0 : a * x j = 0 := by
      have h := congr_fun hab j
      simpa [hej] using h
    have ha : a = 0 := (mul_eq_zero.mp hj0).resolve_right hj
    refine ⟨ha, ?_⟩
    have hk0 : a * x k + b = 0 := by
      have h := congr_fun hab k
      simpa [hek] using h
    rw [ha, zero_mul, zero_add] at hk0
    exact hk0
  -- `‖e_k‖ = 1`
  have henorm : eNorm e = 1 := by
    rw [eNorm]
    have h : ∑ i, (((e i : ℤ) : ℝ)) ^ 2 = 1 := by
      rw [Finset.sum_eq_single k]
      · simp [e]
      · intro b _ hb
        have hbk : b ≠ k := hb
        simp [e, Pi.single_eq_of_ne hbk]
      · intro hk'
        exact absurd (Finset.mem_univ k) hk'
    rw [h, Real.sqrt_one]
  -- the witness lattice `span ℤ {x, e_k}` has rank `2` and contains `x`
  have hrk : rk (Submodule.span ℤ (Set.range (![x, e] : Fin 2 → (Fin (n + 1) → ℤ)))) = 2 := by
    rw [rk, Module.finrank_eq_card_basis (Module.Basis.span hli)]
    simp
  have hxL : x ∈ Submodule.span ℤ (Set.range (![x, e] : Fin 2 → (Fin (n + 1) → ℤ))) :=
    Submodule.subset_span ⟨0, rfl⟩
  have hsub : ({x} : Set (Fin (n + 1) → ℤ)) ⊆
      Submodule.span ℤ (Set.range (![x, e] : Fin 2 → (Fin (n + 1) → ℤ))) :=
    Set.singleton_subset_iff.mpr hxL
  -- its covolume is at most `‖x‖`
  have hdet : detL (Submodule.span ℤ (Set.range (![x, e] : Fin 2 → (Fin (n + 1) → ℤ)))) ≤ eNorm x := by
    rw [Work.HP.HP3.detL_span_range_pair x e hli, wedgeNorm]
    have h1 : eNorm x ^ 2 * eNorm e ^ 2 - dotR (toR x) (toR e) ^ 2 ≤ eNorm x ^ 2 := by
      rw [henorm]
      nlinarith [sq_nonneg (dotR (toR x) (toR e))]
    calc Real.sqrt (eNorm x ^ 2 * eNorm e ^ 2 - dotR (toR x) (toR e) ^ 2)
        ≤ Real.sqrt (eNorm x ^ 2) := Real.sqrt_le_sqrt h1
      _ = eNorm x := Real.sqrt_sq (eNorm_nonneg x)
  exact (Work.HP.HP3.dmin_le_detL hrk hsub).trans hdet

end Work.HP.MM2
