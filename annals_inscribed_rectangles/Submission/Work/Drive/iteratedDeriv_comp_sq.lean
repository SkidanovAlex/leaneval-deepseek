import Mathlib

namespace Work.Drive

/-- Faà di Bruno for the substitution `t ↦ t ^ 2`: the `(2j)`-th iterated derivative at `0` of
`φ (t ^ 2)` only receives the partitions of `Fin (2 * j)` all of whose parts have size `2`, and the
scalar `(2j)! / j!` counts those partitions weighted by the factor `2 ^ j` coming from
`iteratedDeriv 2 (· ^ 2) 0 = 2`. -/
theorem iteratedDeriv_comp_sq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : ℝ → F}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (j : ℕ) :
    iteratedDeriv (2 * j) (fun t : ℝ => φ (t ^ 2)) 0 =
      ((Nat.factorial (2 * j) : ℝ) / (Nat.factorial j : ℝ)) • iteratedDeriv j φ 0 := by
  have hi : ((2 * j : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr (le_top : ((2 * j : ℕ) : ℕ∞) ≤ ⊤)
  have hsq : ∀ k : ℕ, iteratedDeriv k (fun t : ℝ => t ^ 2) 0 = if k = 2 then (2 : ℝ) else 0 := by
    intro k
    simpa using iteratedDeriv_fun_pow_zero (𝕜 := ℝ) (n := k) (m := 2)
  have hpow : ∀ k : ℕ, iteratedDeriv k (fun y : ℝ => y ^ j) 0 =
      if k = j then (Nat.factorial j : ℝ) else 0 := by
    intro k
    simpa using iteratedDeriv_fun_pow_zero (𝕜 := ℝ) (n := k) (m := j)
  -- The product of the inner derivatives vanishes unless all parts have size two.
  have hP : ∀ c : OrderedFinpartition (2 * j),
      (∏ m, iteratedDeriv (c.partSize m) (fun t : ℝ => t ^ 2) 0) ≠ 0 → c.length = j := by
    intro c hc
    have hall : ∀ m, c.partSize m = 2 := by
      intro m
      by_contra hm
      exact hc (by
        show (∏ m : Fin c.length, iteratedDeriv (c.partSize m) (fun t : ℝ => t ^ 2) 0) = 0
        exact Finset.prod_eq_zero (Finset.mem_univ m) (by rw [hsq, if_neg hm]))
    have hsum : ∑ m : Fin c.length, c.partSize m = 2 * j := by
      have h := OrderedFinpartition.sum_sigma_eq_sum c (fun _ : Fin (2 * j) => (1 : ℕ))
      simpa using h
    have hsum2 : ∑ m : Fin c.length, c.partSize m = c.length * 2 := by
      calc ∑ m : Fin c.length, c.partSize m = ∑ _ : Fin c.length, (2 : ℕ) :=
            Finset.sum_congr rfl (fun m _ => hall m)
        _ = c.length * 2 := by simp
    omega
  have hFdP := iteratedDeriv_scomp_eq_sum_orderedFinpartition (𝕜 := ℝ) (E := F)
      (g := φ) (f := fun t : ℝ => t ^ 2) (x := 0)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (i := 2 * j) hφ.contDiffAt (by fun_prop) hi
  simp only [zero_pow (show (2 : ℕ) ≠ 0 by norm_num)] at hFdP
  have hpt : ∀ c : OrderedFinpartition (2 * j),
      (∏ m, iteratedDeriv (c.partSize m) (fun t : ℝ => t ^ 2) 0) • iteratedDeriv c.length φ 0 =
      (∏ m, iteratedDeriv (c.partSize m) (fun t : ℝ => t ^ 2) 0) • iteratedDeriv j φ 0 := by
    intro c
    rcases eq_or_ne c.length j with h | h
    · rw [congrArg (fun k : ℕ => iteratedDeriv k φ 0) h]
    · have hP0 : (∏ m, iteratedDeriv (c.partSize m) (fun t : ℝ => t ^ 2) 0) = 0 := by
        by_contra hne
        exact h (hP c hne)
      simp only [hP0, zero_smul]
  have hmain : iteratedDeriv (2 * j) (fun t : ℝ => φ (t ^ 2)) 0 =
      (∑ c : OrderedFinpartition (2 * j), ∏ m, iteratedDeriv (c.partSize m) (fun t : ℝ => t ^ 2) 0) •
        iteratedDeriv j φ 0 := by
    rw [show (fun t : ℝ => φ (t ^ 2)) = φ ∘ (fun t : ℝ => t ^ 2) from rfl, hFdP]
    exact (Finset.sum_congr rfl (fun c _ => hpt c)).trans (Finset.sum_smul).symm
  -- Bootstrap the count of partitions into pairs using the scalar function `y ↦ y ^ j`.
  have hFdP2 := iteratedDeriv_scomp_eq_sum_orderedFinpartition (𝕜 := ℝ) (E := ℝ)
      (g := fun y : ℝ => y ^ j) (f := fun t : ℝ => t ^ 2) (x := 0)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (i := 2 * j) (by fun_prop) (by fun_prop) hi
  simp only [zero_pow (show (2 : ℕ) ≠ 0 by norm_num)] at hFdP2
  have hsum3 : (∑ c : OrderedFinpartition (2 * j),
        (∏ m, iteratedDeriv (c.partSize m) (fun t : ℝ => t ^ 2) 0) •
          iteratedDeriv c.length (fun y : ℝ => y ^ j) 0) =
      (∑ c : OrderedFinpartition (2 * j), ∏ m, iteratedDeriv (c.partSize m) (fun t : ℝ => t ^ 2) 0) *
        (Nat.factorial j : ℝ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    rcases eq_or_ne c.length j with h | h
    · rw [congrArg (fun k : ℕ => iteratedDeriv k (fun y : ℝ => y ^ j) 0) h,
        hpow j, if_pos rfl, smul_eq_mul]
    · have hP0 : (∏ m, iteratedDeriv (c.partSize m) (fun t : ℝ => t ^ 2) 0) = 0 := by
        by_contra hne
        exact h (hP c hne)
      rw [hP0]
      simp only [zero_smul, zero_mul]
  have hLHS2 : iteratedDeriv (2 * j) ((fun y : ℝ => y ^ j) ∘ (fun t : ℝ => t ^ 2)) 0 =
      (Nat.factorial (2 * j) : ℝ) := by
    have hc : ((fun y : ℝ => y ^ j) ∘ (fun t : ℝ => t ^ 2)) = (fun t : ℝ => t ^ (2 * j)) := by
      funext t
      simp [pow_mul]
    rw [hc]
    simpa using iteratedDeriv_fun_pow_zero (𝕜 := ℝ) (n := 2 * j) (m := 2 * j)
  have h2 : (Nat.factorial (2 * j) : ℝ) =
      (∑ c : OrderedFinpartition (2 * j), ∏ m, iteratedDeriv (c.partSize m) (fun t : ℝ => t ^ 2) 0) *
        (Nat.factorial j : ℝ) := by
    rw [← hLHS2, hFdP2, hsum3]
  have hQ : (∑ c : OrderedFinpartition (2 * j),
        ∏ m, iteratedDeriv (c.partSize m) (fun t : ℝ => t ^ 2) 0) =
      (Nat.factorial (2 * j) : ℝ) / (Nat.factorial j : ℝ) := by
    rw [eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero j)]
    exact h2.symm
  rw [hmain, hQ]

end Work.Drive
