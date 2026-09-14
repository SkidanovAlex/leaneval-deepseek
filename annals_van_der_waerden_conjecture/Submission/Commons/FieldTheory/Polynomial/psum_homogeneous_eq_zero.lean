import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.Polynomial

open Polynomial

/-- If the weighted power sums `∑ i, m i * (x i) ^ (j+1)` vanish for all `j : Fin r`, and
every nonempty subset-sum of the weights `m` is nonzero, then every `x i` is zero.

This is the homogeneous "moment" statement used to show that a system of `r` power sums with
`r` weights forces all the indeterminates to vanish (a weighted Vandermonde / Lagrange
interpolation argument: grouping the indices by the value of `x` shows each nonzero fiber of
`x` has weight-sum `0`, contradicting the hypothesis `hm`). -/
theorem psum_homogeneous_eq_zero {F : Type*} [Field F] {r : ℕ} (x : Fin r → F) (m : Fin r → F)
    (hm : ∀ s : Finset (Fin r), s.Nonempty → ∑ i ∈ s, m i ≠ 0)
    (h : ∀ j : Fin r, ∑ i : Fin r, m i * (x i) ^ ((j : ℕ) + 1) = 0) :
    ∀ i, x i = 0 := by
  classical
  -- The linear functional `Q ↦ ∑ i, m i * Q.eval (x i)` annihilates every polynomial `Q`
  -- with vanishing constant coefficient and `natDegree ≤ r`.
  have hkey : ∀ Q : Polynomial F, Q.coeff 0 = 0 → Q.natDegree ≤ r →
      ∑ i : Fin r, m i * Q.eval (x i) = 0 := by
    intro Q hQ0 hQd
    have hlt : Q.natDegree < r + 1 := by omega
    have heval : ∀ a : F, Q.eval a = ∑ k ∈ Finset.range (r+1), Q.coeff k * a^k :=
      fun a => Polynomial.eval_eq_sum_range' hlt a
    calc ∑ i : Fin r, m i * Q.eval (x i)
        = ∑ i : Fin r, m i * (∑ k ∈ Finset.range (r+1), Q.coeff k * (x i)^k) := by
            simp only [heval]
      _ = ∑ i : Fin r, ∑ k ∈ Finset.range (r+1), m i * (Q.coeff k * (x i)^k) := by
            apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
      _ = ∑ k ∈ Finset.range (r+1), ∑ i : Fin r, m i * (Q.coeff k * (x i)^k) := by
            rw [Finset.sum_comm]
      _ = ∑ k ∈ Finset.range (r+1), Q.coeff k * (∑ i : Fin r, m i * (x i)^k) := by
            apply Finset.sum_congr rfl; intro k _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro i _
            ring
      _ = 0 := by
            apply Finset.sum_eq_zero
            intro k hk
            rw [Finset.mem_range] at hk
            rcases Nat.eq_zero_or_pos k with hk0 | hkpos
            · subst hk0; rw [hQ0]; simp
            · have hj : k - 1 < r := by omega
              have hkj : ((⟨k - 1, hj⟩ : Fin r) : ℕ) + 1 = k := by
                simp [Nat.sub_add_cancel hkpos]
              have hsum : ∑ i : Fin r, m i * (x i)^k = 0 := by
                have hh := h ⟨k-1, hj⟩
                rwa [hkj] at hh
              rw [hsum, mul_zero]
  intro i
  by_contra hi
  -- Suppose `x i ≠ 0`.  Consider the set of all nonzero values attained by `x`,
  -- and the fiber over the value `v = x i`.
  set v : F := x i with hv
  have hvne : v ≠ 0 := by rw [hv]; exact hi
  set S : Finset (Fin r) := Finset.univ.filter (fun j => x j ≠ 0) with hS
  set V : Finset F := S.image x with hV
  set fiber : Finset (Fin r) := Finset.univ.filter (fun j => x j = v) with hfiber
  -- Lagrange-style polynomial vanishing at every nonzero value other than `v`, times `X`.
  set R : Polynomial F := ∏ w ∈ V.erase v, (Polynomial.X - Polynomial.C w) with hR
  set Q : Polynomial F := Polynomial.X * R with hQ
  have hvV : v ∈ V := by
    rw [hV, hS]
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨i, hi, hv.symm⟩
  have hQ0 : Q.coeff 0 = 0 := by
    rw [hQ, Polynomial.coeff_mul]
    simp [Polynomial.coeff_X]
  have hdegR : R.natDegree ≤ (V.erase v).card := by
    rw [hR]
    calc (∏ w ∈ V.erase v, (Polynomial.X - Polynomial.C w) : Polynomial F).natDegree
        ≤ ∑ w ∈ V.erase v, (Polynomial.X - Polynomial.C w).natDegree :=
          Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ w ∈ V.erase v, (1:ℕ) := by
            apply Finset.sum_le_sum
            intro w _
            exact Polynomial.natDegree_X_sub_C_le w
      _ = (V.erase v).card := by simp
  have hVcard : V.card ≤ r := by
    rw [hV, hS]
    calc ((Finset.univ.filter (fun j => x j ≠ 0)).image x).card
        ≤ (Finset.univ.filter (fun j => x j ≠ 0)).card := Finset.card_image_le
      _ ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = r := by simp
  have hdeg : Q.natDegree ≤ r := by
    have h1 : Q.natDegree ≤ 1 + R.natDegree := by
      rw [hQ]
      calc (Polynomial.X * R).natDegree ≤ Polynomial.X.natDegree + R.natDegree :=
            Polynomial.natDegree_mul_le
        _ = 1 + R.natDegree := by rw [Polynomial.natDegree_X]
    have h3 : 1 + (V.erase v).card = V.card := by
      have := Finset.card_erase_add_one hvV; omega
    omega
  have hevalQ : ∀ a : F, Q.eval a = a * ∏ w ∈ V.erase v, (a - w) := by
    intro a
    rw [hQ, hR, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_X]
    congr 1
    apply Finset.prod_congr rfl
    intro w _
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  -- `Q.eval` vanishes outside the fiber over `v` ...
  have hQeval_zero : ∀ j : Fin r, x j ≠ v → Q.eval (x j) = 0 := by
    intro j hj
    rw [hevalQ (x j)]
    rcases eq_or_ne (x j) 0 with hxj | hxj
    · rw [hxj, zero_mul]
    · have hmem : x j ∈ V := by
        rw [hV, hS]
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨j, hxj, rfl⟩
      have hmem2 : x j ∈ V.erase v := by
        rw [Finset.mem_erase]; exact ⟨hj, hmem⟩
      have hz : ∏ w ∈ V.erase v, (x j - w) = 0 :=
        Finset.prod_eq_zero hmem2 (by rw [sub_self])
      rw [hz, mul_zero]
  -- ... and equals a fixed nonzero constant `v * ∏ (v - w)` on it.
  have hQeval_v : ∀ j : Fin r, x j = v → Q.eval (x j) = v * ∏ w ∈ V.erase v, (v - w) := by
    intro j hj
    rw [hevalQ (x j), hj]
  have hc_ne : (v * ∏ w ∈ V.erase v, (v - w)) ≠ 0 := by
    apply mul_ne_zero hvne
    rw [Finset.prod_ne_zero_iff]
    intro w hw
    rw [Finset.mem_erase] at hw
    exact sub_ne_zero.mpr (Ne.symm hw.1)
  have hsum_out : ∑ j : Fin r, m j * Q.eval (x j) = ∑ j ∈ fiber, m j * Q.eval (x j) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ fiber)
    intro j _ hj
    have hxj : x j ≠ v := by
      intro hxv; exact hj (by rw [hfiber]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hxv⟩)
    rw [hQeval_zero j hxj, mul_zero]
  have hsum_fiber : ∑ j ∈ fiber, m j * Q.eval (x j)
      = (∑ j ∈ fiber, m j) * (v * ∏ w ∈ V.erase v, (v - w)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : x j = v := by
      rw [hfiber] at hj
      exact (Finset.mem_filter.mp hj).2
    rw [hQeval_v j hj']
  have htotal : ∑ j : Fin r, m j * Q.eval (x j) = 0 := hkey Q hQ0 hdeg
  have hprod : (∑ j ∈ fiber, m j) * (v * ∏ w ∈ V.erase v, (v - w)) = 0 := by
    rw [← hsum_fiber, ← hsum_out]; exact htotal
  have hfiber0 : ∑ j ∈ fiber, m j = 0 := by
    rcases mul_eq_zero.mp hprod with hh | hh
    · exact hh
    · exact absurd hh hc_ne
  have hfib_ne : fiber.Nonempty :=
    ⟨i, by rw [hfiber]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hv.symm⟩⟩
  exact (hm fiber hfib_ne) hfiber0

end Commons.FieldTheory.Polynomial