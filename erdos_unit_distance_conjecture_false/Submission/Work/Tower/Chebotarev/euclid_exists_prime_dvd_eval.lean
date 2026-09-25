import Mathlib

namespace Work.Tower.Chebotarev

open Polynomial

/-- Infinitely many primes lie outside any finite set of naturals and above any bound. -/
theorem exists_prime_gt_not_mem (S : Finset ℕ) (n : ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ n < q ∧ q ∉ S := by
  have hinf : ¬ (({p : ℕ | Nat.Prime p} : Set ℕ) ⊆
      (↑(S ∪ Finset.range (n + 1)) : Set ℕ)) := by
    intro hsub
    exact Nat.infinite_setOfPred_prime
      ((Finset.finite_toSet (S ∪ Finset.range (n + 1))).subset hsub)
  rw [Set.not_subset] at hinf
  obtain ⟨q, hq, hqS⟩ := hinf
  refine ⟨q, hq, ?_, ?_⟩
  · by_contra h
    have h' : q ≤ n := by omega
    exact hqS (Finset.mem_coe.mpr
      (Finset.mem_union_right _ (Finset.mem_range.mpr (Nat.lt_succ_of_le h'))))
  · intro h
    exact hqS (Finset.mem_coe.mpr (Finset.mem_union_left _ h))

/-- A nonconstant integer polynomial takes a value of absolute value at least `2` at some natural
number: the set of `k` with `|H(k)| ≤ 1` is finite since it lies in the union of the (finitely
many) integer roots of `H`, `H - 1` and `H + 1`. -/
theorem exists_natAbs_eval_ge_two (H : ℤ[X]) (hH : 0 < H.natDegree) :
    ∃ k : ℕ, 2 ≤ (H.eval (k : ℤ)).natAbs := by
  by_contra hc
  simp only [not_exists, not_le] at hc
  have hne : ∀ v : ℤ, H - C v ≠ 0 := by
    intro v hz
    have hdeg := congrArg Polynomial.natDegree hz
    rw [Polynomial.natDegree_sub_C, Polynomial.natDegree_zero] at hdeg
    omega
  classical
  set T : Finset ℕ := ({0, 1, -1} : Finset ℤ).biUnion
    (fun v => (H - C v).roots.toFinset.preimage (fun k : ℕ => (k : ℤ))
      Nat.cast_injective.injOn) with hT_def
  have hmemT : ∀ k : ℕ, k ∈ T := by
    intro k
    have hk2 : (H.eval (k : ℤ)).natAbs < 2 := hc k
    have hvmem : H.eval (k : ℤ) ∈ ({0, 1, -1} : Finset ℤ) := by
      have h0or1 : (H.eval (k : ℤ)).natAbs = 0 ∨ (H.eval (k : ℤ)).natAbs = 1 := by omega
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h0or1 with h0 | h1
      · exact Or.inl (Int.natAbs_eq_zero.mp h0)
      · rcases (Int.natAbs_eq_iff.mp h1) with h1 | h1
        · exact Or.inr (Or.inl (by simpa using h1))
        · exact Or.inr (Or.inr (by simpa using h1))
    rw [hT_def, Finset.mem_biUnion]
    refine ⟨H.eval (k : ℤ), hvmem, ?_⟩
    rw [Finset.mem_preimage, Multiset.mem_toFinset, Polynomial.mem_roots']
    exact ⟨hne _, by simp [Polynomial.IsRoot]⟩
  have hinf : ¬ ((Set.univ : Set ℕ) ⊆ (↑T : Set ℕ)) := by
    intro hsub
    exact Set.infinite_univ ((Finset.finite_toSet T).subset hsub)
  rw [Set.not_subset] at hinf
  obtain ⟨k, -, hkT⟩ := hinf
  exact hkT (Finset.mem_coe.mpr (hmemT k))

/-- The elementary Euclid argument: for a nonconstant integer polynomial `f` and any finite set
`S` of natural numbers, there are arbitrarily large primes outside `S` dividing some value of `f`
at an integer. -/
theorem euclid_exists_prime_dvd_eval (f : ℤ[X]) (hf : 0 < f.natDegree) (S : Finset ℕ) (n : ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ n < q ∧ q ∉ S ∧ ∃ a : ℤ, (q : ℤ) ∣ f.eval a := by
  classical
  -- write `c = f.eval 0`
  set c : ℤ := f.eval 0 with hc_def
  by_cases hc0 : c = 0
  · -- if `f(0) = 0`, every prime divides the value `f(0) = 0`
    obtain ⟨q, hqp, hqn, hqS⟩ := exists_prime_gt_not_mem S n
    exact ⟨q, hqp, hqn, hqS, 0, by rw [← hc_def, hc0]; exact dvd_zero _⟩
  · -- `P` is a multiple of every prime in `S` and of every prime `≤ n`
    set P : ℕ := (S.filter Nat.Prime).prod id * Nat.factorial n with hP_def
    have hPprod : (S.filter Nat.Prime).prod id ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro i hi
      exact (Finset.mem_filter.mp hi).2.ne_zero
    have hP : P ≠ 0 := by
      rw [hP_def]
      exact mul_ne_zero hPprod (Nat.factorial_ne_zero n)
    have hprime_dvd_P : ∀ q : ℕ, Nat.Prime q → q ∈ S → q ∣ P := by
      intro q hq hqS
      rw [hP_def]
      exact dvd_mul_of_dvd_left
        (Finset.dvd_prod_of_mem (fun p => p) (Finset.mem_filter.mpr ⟨hqS, hq⟩)) _
    have hle_dvd_P : ∀ q : ℕ, Nat.Prime q → q ≤ n → q ∣ P := by
      intro q hq hqn
      rw [hP_def]
      exact dvd_mul_of_dvd_right (Nat.dvd_factorial hq.pos hqn) _
    set PZ : ℤ := (P : ℤ) with hPZ_def
    have hPZ : PZ ≠ 0 := by
      rw [hPZ_def, Nat.cast_ne_zero]
      exact hP
    -- `f = c + X * g`
    obtain ⟨g, hg⟩ : ∃ g : ℤ[X], f - C c = X * g := by
      refine Polynomial.X_dvd_iff.mpr ?_
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_zero, Polynomial.coeff_zero_eq_eval_zero,
        ← hc_def, sub_self]
    have hfac : f = C c + X * g := by
      rw [add_comm]; exact sub_eq_iff_eq_add.mp hg
    -- substitute `X ↦ u = c * P * X`
    set u : ℤ[X] := C (c * PZ) * X with hu_def
    set H : ℤ[X] := 1 + C PZ * X * g.comp u with hH_def
    have hu_deg : u.natDegree = 1 := by
      rw [hu_def]
      exact Polynomial.natDegree_C_mul_X _ (mul_ne_zero hc0 hPZ)
    have hfid : f.comp u = C c * H := by
      rw [hfac, hH_def]
      simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.X_comp, Polynomial.C_comp]
      rw [hu_def, Polynomial.C_mul]
      ring
    -- `H` is nonconstant, so some value of it has absolute value at least `2`
    have hH_deg : 0 < H.natDegree := by
      have h1 : (f.comp u).natDegree = f.natDegree := by
        rw [Polynomial.natDegree_comp, hu_deg, mul_one]
      have h2 : (C c * H).natDegree = H.natDegree := Polynomial.natDegree_C_mul hc0
      rw [hfid, h2] at h1
      omega
    obtain ⟨k, hk⟩ := exists_natAbs_eval_ge_two H hH_deg
    have heval_u : u.eval (k : ℤ) = (k : ℤ) * c * PZ := by
      rw [hu_def]
      simp [Polynomial.eval_mul, Polynomial.eval_X]
      ring
    -- `H(k) ≡ 1 mod P`
    have hid : H.eval (k : ℤ) = 1 + (k : ℤ) * PZ * g.eval ((k : ℤ) * c * PZ) := by
      rw [hH_def]
      simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_comp, heval_u]
      ring
    have hkey : f.eval ((k : ℤ) * c * PZ) = c * H.eval (k : ℤ) := by
      have h1 : f.eval ((k : ℤ) * c * PZ) = (f.comp u).eval (k : ℤ) := by
        rw [Polynomial.eval_comp, heval_u]
      rw [h1, hfid, Polynomial.eval_mul, Polynomial.eval_C]
    -- take a prime factor `q` of `H(k)`
    obtain ⟨q, hqp, hqD⟩ :=
      Nat.exists_prime_and_dvd (n := (H.eval (k : ℤ)).natAbs) (by omega)
    have hq_dvd_h : (q : ℤ) ∣ H.eval (k : ℤ) :=
      Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hqD)
    -- `q ∤ P`, because `H(k) ≡ 1 mod P`
    have hq_notdvd_P : ¬ q ∣ P := by
      intro hqP
      have hqPZ : (q : ℤ) ∣ PZ := by
        rw [hPZ_def]
        exact Int.natCast_dvd_natCast.mpr hqP
      have h1 : (q : ℤ) ∣ (1 : ℤ) := by
        have hsub := dvd_sub hq_dvd_h
          (hqPZ.mul_left ((k : ℤ) * g.eval ((k : ℤ) * c * PZ)))
        rw [hid] at hsub
        have hz : (1 : ℤ) + (k : ℤ) * PZ * g.eval ((k : ℤ) * c * PZ)
            - ((k : ℤ) * g.eval ((k : ℤ) * c * PZ)) * PZ = 1 := by ring
        rwa [hz] at hsub
      have h1' : q ∣ 1 := Int.natCast_dvd_natCast.mp (by simpa using h1)
      exact hqp.not_dvd_one h1'
    have hqS : q ∉ S := fun hqs => hq_notdvd_P (hprime_dvd_P q hqp hqs)
    have hqn : n < q := by
      by_contra h
      have h' : q ≤ n := by omega
      exact hq_notdvd_P (hle_dvd_P q hqp h')
    exact ⟨q, hqp, hqn, hqS, (k : ℤ) * c * PZ, by
      rw [hkey]
      exact hq_dvd_h.mul_left c⟩

end Work.Tower.Chebotarev
