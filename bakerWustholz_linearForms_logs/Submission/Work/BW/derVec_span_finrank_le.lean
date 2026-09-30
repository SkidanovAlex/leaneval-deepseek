import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BW.derVec_span_finrank_le`

Given `r` integer vectors `L j = (L j i)_i` in `ℤ^n` (`j : Fin r`, `i : Fin n`) and an integer
vector `b ∈ ℤ^n` lying in the rational row span of the `L j` with `b k ≠ 0`, the `n` vectors

  `c_j i = derVec b k L j i = b k * L i j - b j * L i k   (i : Fin r)`

(these are the coefficient vectors of BW's operators `∂*_j`, `j ≠ k`) span a rational subspace of
`ℚ^r` of dimension at most `r - 1`.

The reason: if `q : Fin r → ℚ` is a combination of the rows exhibiting `b` (so
`∑ i, q i * L i j = b j` for all `j`), then `q ≠ 0` and the functional `T x = ∑ i, q i * x i`
kills every `c_j`, since
`T c_j = b k * (∑ i, q i * L i j) - b j * (∑ i, q i * L i k) = b k * b j - b j * b k = 0`.
Hence the span lies in a hyperplane and has dimension `≤ r - 1`.
-/

namespace Work.BW

open scoped BigOperators

theorem derVec_span_finrank_le {n r : ℕ} (L : Fin r → Fin n → ℤ) (b : Fin n → ℤ) (k : Fin n)
    (hspan : (fun i => (b i : ℚ)) ∈ Submodule.span ℚ (Set.range fun j i => (L j i : ℚ)))
    (hbk : b k ≠ 0) :
    Module.finrank ℚ
      (Submodule.span ℚ (Set.range (fun j : Fin n => fun i : Fin r => (derVec b k L j i : ℚ)))) ≤ r - 1 := by
  -- Write `b` as a rational combination of the rows of `L`.
  rw [Submodule.mem_span_range_iff_exists_fun] at hspan
  obtain ⟨q, hq⟩ := hspan
  have hqj : ∀ j, ∑ i, q i * (L i j : ℚ) = (b j : ℚ) := by
    intro j
    have h := congrFun hq j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [h]
  -- Since `b k ≠ 0`, the coefficient vector `q` is nonzero.
  have hqne : ∃ i, q i ≠ 0 := by
    by_contra h
    have h0 : q = 0 := by
      funext i
      by_contra hi
      exact h ⟨i, hi⟩
    exact hbk (by
      have hk := hqj k
      rw [h0] at hk
      simp at hk
      exact_mod_cast hk.symm)
  obtain ⟨i₀, hi₀⟩ := hqne
  -- The functional `T x = ∑ i, q i * x i` on `ℚ^r`.
  let T : (Fin r → ℚ) →ₗ[ℚ] ℚ := ∑ i, q i • (LinearMap.proj i : (Fin r → ℚ) →ₗ[ℚ] ℚ)
  have hTapply : ∀ x : Fin r → ℚ, T x = ∑ i, q i * x i := by
    intro x
    simp [T, LinearMap.sum_apply, LinearMap.proj_apply, smul_eq_mul]
  have hTne : T ≠ 0 := by
    intro hT0
    have he : T (Pi.single i₀ (1 : ℚ)) = q i₀ := by
      rw [hTapply]
      rw [Finset.sum_eq_single i₀]
      · simp
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj]
        simp
      · intro h; exact absurd (Finset.mem_univ i₀) h
    rw [hT0] at he
    simp at he
    exact hi₀ he.symm
  -- `T` annihilates every vector `derVec b k L j`.
  have hTq : ∀ j : Fin n, T (fun i => (derVec b k L j i : ℚ)) = 0 := by
    intro j
    rw [hTapply]
    have h1 : ∑ i, q i * (derVec b k L j i : ℚ)
        = (b k : ℚ) * (∑ i, q i * (L i j : ℚ)) - (b j : ℚ) * (∑ i, q i * (L i k : ℚ)) := by
      simp only [derVec, Int.cast_sub, Int.cast_mul]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [h1, hqj j, hqj k]
    ring
  -- Hence the span lies in the kernel of the nonzero functional `T`, a hyperplane.
  have hle : Submodule.span ℚ
      (Set.range (fun j : Fin n => fun i : Fin r => (derVec b k L j i : ℚ))) ≤ T.ker := by
    rw [Submodule.span_le]
    rintro x ⟨j, rfl⟩
    exact LinearMap.mem_ker.mpr (hTq j)
  have h1 : Module.finrank ℚ
        (Submodule.span ℚ (Set.range (fun j : Fin n => fun i : Fin r => (derVec b k L j i : ℚ))))
      ≤ Module.finrank ℚ T.ker :=
    Submodule.finrank_mono hle
  have h2 : Module.finrank ℚ T.ker ≤ r - 1 := by
    have hlt : T.ker < ⊤ :=
      lt_top_iff_ne_top.mpr fun h => hTne (LinearMap.ker_eq_top.mp h)
    have hlt2 := Submodule.finrank_lt_finrank_of_lt hlt
    rw [finrank_top, Module.finrank_fin_fun] at hlt2
    omega
  omega

end Work.BW
