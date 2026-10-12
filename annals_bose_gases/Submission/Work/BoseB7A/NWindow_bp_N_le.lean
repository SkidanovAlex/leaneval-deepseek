import Mathlib.Analysis.Normed.Field.Basic
import Submission.Work.BoseB7A.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.NWindow_bp_N_le`

The basic window estimate for FS's `n₊`: if `Φ = 1_{[0,𝓜]}(n₊)Φ` (a finite sum of
`n₊`-eigenvectors with eigenvalues `m ≤ ⌊𝓜⌋₊`, which is what `TildeData.NWindow`
records algebraically), then

  `⟨Φ, n₊Φ⟩ ≤ 𝓜 ‖Φ‖²`.

The proof is the spectral argument in elementary form: eigenvectors of the
self-adjoint `n₊` with *distinct* eigenvalues are orthogonal (so the double sum
`Σ_{m,m'} ⟨φ_m, φ_{m'}⟩` collapses to its diagonal), and each eigenvalue is
`≤ ⌊𝓜⌋₊ ≤ 𝓜`.  No diagonalisation and no completeness of the `φ_m` is needed.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

theorem NWindow_bp_N_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) {M : ℝ} {Φ : F.H}
    (hM : 0 ≤ M) (hΦ : T.NWindow M Φ) :
    F.bp (T.N Φ) Φ ≤ M * F.normSq Φ := by
  obtain ⟨φ, hφ, hsum0⟩ := hΦ
  set n : ℕ := ⌊M⌋₊ with hn
  set S : Finset ℕ := Finset.range (n + 1) with hS
  have hsum : Φ = ∑ m ∈ S, φ m := by rw [hS, hn]; exact hsum0
  have hMn : (n : ℝ) ≤ M := by rw [hn]; exact Nat.floor_le hM
  have hmle : ∀ m ∈ S, m ≤ n := by
    intro m hm
    rw [hS] at hm
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  -- eigenvectors of the self-adjoint `n₊` with distinct eigenvalues are orthogonal
  have horth : ∀ m ∈ S, ∀ m' ∈ S, m ≠ m' → F.bp (φ m) (φ m') = 0 := by
    intro m hm m' hm' hne
    have h1 : F.bp (T.N (φ m)) (φ m') = (m : ℝ) * F.bp (φ m) (φ m') := by
      rw [hφ m, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
    have h2 : F.bp (T.N (φ m)) (φ m') = (m' : ℝ) * F.bp (φ m) (φ m') := by
      rw [T.N_symm, hφ m', LinearMap.map_smul, smul_eq_mul]
    have hne' : ((m : ℝ) - (m' : ℝ)) ≠ 0 :=
      sub_ne_zero.mpr (by exact_mod_cast hne)
    have hzero : ((m : ℝ) - (m' : ℝ)) * F.bp (φ m) (φ m') = 0 := by
      rw [sub_mul, ← h1, ← h2, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_left hne'
  -- each `φ m` is orthogonal to `Φ`, up to its own diagonal term
  have hkey : ∀ m ∈ S, F.bp (φ m) Φ = F.bp (φ m) (φ m) := by
    intro m hm
    rw [hsum, map_sum]
    refine Finset.sum_eq_single m ?_ ?_
    · intro m' hm' hne
      exact horth m hm m' hm' (Ne.symm hne)
    · intro hnot
      exact absurd hm hnot
  have h1 : F.bp (T.N Φ) Φ = ∑ m ∈ S, (m : ℝ) * F.bp (φ m) (φ m) := by
    have hNΦ : T.N Φ = ∑ m ∈ S, (m : ℝ) • φ m := by
      rw [hsum, map_sum]
      exact Finset.sum_congr rfl (fun m _ => hφ m)
    rw [hNΦ, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, hkey m hm]
  have h2 : F.normSq Φ = ∑ m ∈ S, F.bp (φ m) (φ m) := by
    rw [Work.BoseB7.FockData.normSq]
    nth_rewrite 2 [hsum]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [F.bp_symm, hkey m hm]
  calc F.bp (T.N Φ) Φ = ∑ m ∈ S, (m : ℝ) * F.bp (φ m) (φ m) := h1
    _ ≤ ∑ m ∈ S, M * F.bp (φ m) (φ m) := by
        refine Finset.sum_le_sum (fun m hm => ?_)
        refine mul_le_mul_of_nonneg_right ?_ (F.bp_nonneg (φ m))
        exact le_trans (by exact_mod_cast hmle m hm) hMn
    _ = M * F.normSq Φ := by rw [h2, Finset.mul_sum]

end Work.BoseB7A
