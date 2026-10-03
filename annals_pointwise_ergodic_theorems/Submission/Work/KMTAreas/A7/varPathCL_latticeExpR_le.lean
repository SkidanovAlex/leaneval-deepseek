import Mathlib
import Submission.Work.KMTAreas.A7.lacDilTriVarDefs

namespace Work.KMTAreas.A7

open Finset
open scoped ENNReal BigOperators

noncomputable section

/-! ### Extending a finite strictly monotone chain to `ℕ` -/

/-- Total extension of `u : Fin (J+1) → ℕ` (agreeing with `u` below `J`). -/
private def chainFwd (J : ℕ) (u : Fin (J + 1) → ℕ) : ℕ → ℕ :=
  fun k => if h : k ≤ J then u ⟨k, Nat.lt_succ_of_le h⟩ else 0

private lemma chainFwd_of_le {J : ℕ} {u : Fin (J + 1) → ℕ} {k : ℕ} (h : k ≤ J) :
    chainFwd J u k = u ⟨k, Nat.lt_succ_of_le h⟩ := by
  simp only [chainFwd, dif_pos h]

/-- The reversed chain `n ↦ L - u (J - n)`, extended to all of `ℕ`. -/
private def chainRev (L J : ℕ) (u : Fin (J + 1) → ℕ) : ℕ → ℕ :=
  fun n => L - u ⟨J - n, Nat.lt_succ_of_le (Nat.sub_le J n)⟩ + (n - J)

private lemma chainRev_of_le {L J : ℕ} {u : Fin (J + 1) → ℕ} {n : ℕ} (h : n ≤ J) :
    chainRev L J u n = L - u ⟨J - n, Nat.lt_succ_of_le (Nat.sub_le J n)⟩ := by
  simp only [chainRev, Nat.sub_eq_zero_of_le h, add_zero]

private lemma chainRev_of_ge {L J : ℕ} {u : Fin (J + 1) → ℕ} {n : ℕ} (hn : J ≤ n) :
    chainRev L J u n = L - u ⟨0, Nat.zero_lt_succ J⟩ + (n - J) := by
  simp only [chainRev]
  have e : (⟨J - n, Nat.lt_succ_of_le (Nat.sub_le J n)⟩ : Fin (J + 1)) = ⟨0, Nat.zero_lt_succ J⟩ := by
    apply Fin.ext
    show J - n = 0
    omega
  rw [e]

private lemma strictMono_chainRev {L J : ℕ} {u : Fin (J + 1) → ℕ} (hu : StrictMono u)
    (huL : ∀ i, u i ≤ L) : StrictMono (chainRev L J u) := by
  intro m n hmn
  by_cases hn : n ≤ J
  · rw [chainRev_of_le (L := L) (u := u) (le_trans (le_of_lt hmn) hn),
      chainRev_of_le (L := L) (u := u) hn]
    have h1 : u ⟨J - n, Nat.lt_succ_of_le (Nat.sub_le J n)⟩
        < u ⟨J - m, Nat.lt_succ_of_le (Nat.sub_le J m)⟩ := by
      apply hu
      show J - n < J - m
      omega
    have h2 : u ⟨J - m, Nat.lt_succ_of_le (Nat.sub_le J m)⟩ ≤ L := huL _
    omega
  · have hn' : J < n := lt_of_not_ge hn
    by_cases hm : m ≤ J
    · rw [chainRev_of_le (L := L) (u := u) hm,
        chainRev_of_ge (L := L) (u := u) (le_of_lt hn')]
      have h1 : u ⟨0, Nat.zero_lt_succ J⟩ ≤ u ⟨J - m, Nat.lt_succ_of_le (Nat.sub_le J m)⟩ := by
        apply hu.monotone
        show (0 : ℕ) ≤ J - m
        omega
      have h2 : u ⟨J - m, Nat.lt_succ_of_le (Nat.sub_le J m)⟩ ≤ L := huL _
      omega
    · have hm' : J < m := lt_of_not_ge hm
      rw [chainRev_of_ge (L := L) (u := u) (le_of_lt hm'),
        chainRev_of_ge (L := L) (u := u) (le_of_lt hn')]
      omega

/-- Reindexing identity: reading a chain variation along the *reversed* chain gives the same
`r`-sum.  For `u : Fin (J+1) → ℕ` strictly increasing with `u i ≤ L` there is a strictly
increasing `w : ℕ → ℕ` whose reversed values `L - w k` are the chain values, so that the
`range`-sum of the differences of `L - w` equals the `Fin`-sum of the differences of `u`. -/
private lemma exists_strictMono_w_sum_eq {J L : ℕ} (u : Fin (J + 1) → ℕ)
    (hu : StrictMono u) (huL : ∀ i, u i ≤ L) (f : ℕ → ℝ) (p : ℝ) :
    ∃ w : ℕ → ℕ, StrictMono w ∧
      (∑ k ∈ Finset.range J, |f (L - w (k + 1)) - f (L - w k)| ^ p)
        = ∑ j : Fin J, |f (u j.succ) - f (u j.castSucc)| ^ p := by
  refine ⟨chainRev L J u, strictMono_chainRev hu huL, ?_⟩
  have h1 : ∀ j : Fin J, chainFwd J u (↑j + 1) = u j.succ := by
    intro j
    rw [chainFwd_of_le (J := J) (u := u) (k := (↑j : ℕ) + 1)
      (h := Nat.succ_le_of_lt j.isLt)]
    rfl
  have h2 : ∀ j : Fin J, chainFwd J u ↑j = u j.castSucc := by
    intro j
    rw [chainFwd_of_le (J := J) (u := u) (k := (↑j : ℕ)) (h := le_of_lt j.isLt)]
    rfl
  have hR : (∑ j : Fin J, |f (u j.succ) - f (u j.castSucc)| ^ p)
      = ∑ k ∈ Finset.range J, |f (chainFwd J u (k + 1)) - f (chainFwd J u k)| ^ p := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => |f (chainFwd J u (k + 1)) - f (chainFwd J u k)| ^ p) J]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h1 j, h2 j]
  rw [hR]
  rw [← Finset.sum_range_reflect (f := fun k =>
    |f (L - chainRev L J u (k + 1)) - f (L - chainRev L J u k)| ^ p)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < J := Finset.mem_range.mp hk
  have e1 : L - chainRev L J u (J - k) = chainFwd J u k := by
    rw [chainRev_of_le (L := L) (u := u) (h := show J - k ≤ J by omega)]
    rw [Nat.sub_sub_self (huL _)]
    rw [chainFwd_of_le (J := J) (u := u) (k := k) (h := show k ≤ J by omega)]
    congr 1
    apply Fin.ext
    show J - (J - k) = k
    omega
  have e2 : L - chainRev L J u (J - 1 - k) = chainFwd J u (k + 1) := by
    rw [chainRev_of_le (L := L) (u := u) (h := show J - 1 - k ≤ J by omega)]
    rw [Nat.sub_sub_self (huL _)]
    rw [chainFwd_of_le (J := J) (u := u) (k := k + 1) (h := show k + 1 ≤ J by omega)]
    congr 1
    apply Fin.ext
    show J - (J - 1 - k) = k + 1
    omega
  rw [show J - 1 - k + 1 = J - k by omega, e1, e2, abs_sub_comm]

theorem varPathCL_latticeExpR_le (r : NNReal) (L : ℕ) (τ : ℤ) (h : ℤ → ℝ) (x : ℤ) :
    Work.KMTAreas.A7.varPathCL L (fun k => (Work.Analysis.Hilbert.latticeExpR k τ h x : ℂ))
        (r : ℝ)
      ≤ Work.KMTAreas.A7.latVarSupR r L τ h x := by
  simp only [varPathCL, latVarSupR]
  refine iSup_le fun J => iSup_le fun u => iSup_le fun hu => iSup_le fun huL => ?_
  obtain ⟨w, hwmono, hweq⟩ :=
    exists_strictMono_w_sum_eq (L := L) u hu huL
      (fun k => Work.Analysis.Hilbert.latticeExpR k τ h x) (r : ℝ)
  have hL : (∑ j : Fin J,
        ‖((Work.Analysis.Hilbert.latticeExpR (u j.succ) τ h x : ℝ) : ℂ)
          - ((Work.Analysis.Hilbert.latticeExpR (u j.castSucc) τ h x : ℝ) : ℂ)‖ ^ (r : ℝ))
      = ∑ j : Fin J, |Work.Analysis.Hilbert.latticeExpR (u j.succ) τ h x
          - Work.Analysis.Hilbert.latticeExpR (u j.castSucc) τ h x| ^ (r : ℝ) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  refine le_iSup_of_le (i := (⟨w, hwmono⟩ : {w : ℕ → ℕ // StrictMono w}))
    (le_iSup_of_le (i := J) ?_)
  rw [hL, ← hweq]

end

end Work.KMTAreas.A7
