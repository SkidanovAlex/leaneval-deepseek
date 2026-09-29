import Mathlib
import Submission.Work.ResMath.resamplingDefs
import Submission.Work.DFT.rootSumZ

/-!
# ℤ-reindexing helpers for the resampling identity
-/

namespace Work.ResMath

open HvdH

/-- The bijection `Fin n × ℤ ≃ ℤ`, `(i,j) ↦ i + n j` (for `n > 0`). -/
noncomputable def finProdIntEquiv (n : ℕ) (hn : 0 < n) : Fin n × ℤ ≃ ℤ where
  toFun p := (p.1 : ℤ) + (n : ℤ) * p.2
  invFun m := (⟨(m % (n : ℤ)).toNat, by
      have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
      have h1 : 0 ≤ m % (n : ℤ) := Int.emod_nonneg m hnz
      have h2 : m % (n : ℤ) < (n : ℤ) := Int.emod_lt_of_pos m (by exact_mod_cast hn)
      have h3 : (((m % (n : ℤ)).toNat : ℕ) : ℤ) = m % (n : ℤ) := Int.toNat_of_nonneg h1
      omega⟩, m / (n : ℤ))
  left_inv := by
    rintro ⟨i, j⟩
    have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
    have hi0 : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg _
    have hin : (i : ℤ) < (n : ℤ) := by exact_mod_cast i.isLt
    have hmod : ((i : ℤ) + (n : ℤ) * j) % (n : ℤ) = (i : ℤ) := by
      rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hi0 hin]
    have hdiv : ((i : ℤ) + (n : ℤ) * j) / (n : ℤ) = j := by
      have h1 := Int.emod_add_mul_ediv ((i : ℤ) + (n : ℤ) * j) (n : ℤ)
      rw [hmod] at h1
      have h2 : (n : ℤ) * (((i : ℤ) + (n : ℤ) * j) / (n : ℤ)) = (n : ℤ) * j := by linarith
      exact mul_left_cancel₀ hnz h2
    simp only [Prod.mk.injEq]
    refine ⟨?_, hdiv⟩
    apply Fin.ext
    show (((i : ℤ) + (n : ℤ) * j) % (n : ℤ)).toNat = i.val
    rw [hmod]
    exact Int.toNat_natCast i
  right_inv := by
    intro m
    have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
    have h1 : 0 ≤ m % (n : ℤ) := Int.emod_nonneg m hnz
    have h3 : (((m % (n : ℤ)).toNat : ℕ) : ℤ) = m % (n : ℤ) := Int.toNat_of_nonneg h1
    show (((m % (n : ℤ)).toNat : ℕ) : ℤ) + (n : ℤ) * (m / (n : ℤ)) = m
    rw [h3]
    exact Int.emod_add_mul_ediv m (n : ℤ)

/-- Decompose a sum over `ℤ` into residue classes modulo `n`. -/
theorem tsum_int_residue (n : ℕ) (hn : 0 < n) (F : ℤ → ℂ) (hF : Summable F) :
    (∑' m : ℤ, F m) = ∑ i : Fin n, ∑' j : ℤ, F ((i : ℤ) + (n : ℤ) * j) := by
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  symm
  rw [← Equiv.tsum_eq (finProdIntEquiv n hn) F]
  rw [Summable.tsum_prod' ?_ ?_]
  · rw [tsum_fintype]
    rfl
  · exact (Equiv.summable_iff (finProdIntEquiv n hn)).mpr hF
  · intro i
    refine hF.comp_injective ?_
    intro a b hab
    change (i : ℤ) + (n : ℤ) * a = (i : ℤ) + (n : ℤ) * b at hab
    have h : (n : ℤ) * a = (n : ℤ) * b := by linarith
    exact mul_left_cancel₀ hnz h

/-- A sum over the arithmetic progression `r + nℤ` equals a sum with an indicator. -/
theorem tsum_int_coset (n : ℕ) (hn : 0 < n) (r : ℤ) (F : ℤ → ℂ) (hF : Summable F) :
    (∑' j : ℤ, F (r + (n : ℤ) * j)) = ∑' m : ℤ, (if (n : ℤ) ∣ (m - r) then F m else 0) := by
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  let s : Set ℤ := {m : ℤ | (n : ℤ) ∣ (m - r)}
  let e : ℤ ≃ s :=
    { toFun := fun j => ⟨r + (n : ℤ) * j, ⟨j, by ring⟩⟩
      invFun := fun m => (m.1 - r) / (n : ℤ)
      left_inv := by
        intro j
        show (r + (n : ℤ) * j - r) / (n : ℤ) = j
        rw [add_sub_cancel_left, Int.mul_ediv_cancel_left _ hnz]
      right_inv := by
        intro m
        obtain ⟨q, hq⟩ := m.2
        have hdiv : (m.1 - r) / (n : ℤ) = q := by
          rw [hq, Int.mul_ediv_cancel_left _ hnz]
        have hmr : r + (n : ℤ) * ((m.1 - r) / (n : ℤ)) = m.1 := by
          rw [hdiv]; linarith
        exact Subtype.ext hmr }
  calc (∑' j : ℤ, F (r + (n : ℤ) * j))
      = ∑' j : ℤ, (fun x : s => F x.1) (e j) := by
        refine tsum_congr fun j => ?_
        rfl
    _ = ∑' x : s, F x.1 := Equiv.tsum_eq e (fun x : s => F x.1)
    _ = ∑' m : ℤ, s.indicator F m := tsum_subtype s F
    _ = ∑' m : ℤ, (if (n : ℤ) ∣ (m - r) then F m else 0) := by
        refine tsum_congr fun m => ?_
        simp only [s, Set.indicator, Set.mem_setOf_eq]



/-! ## Permutation matrices -/

/-- `P_s` acts by `j ↦ tj mod s`. -/
lemma permS_mulVec (s t : ℕ) (hs : 0 < s) (v : Fin s → ℂ) (j : Fin s) :
    (HvdH.permS s t).mulVec v j = v ⟨t * (j : ℕ) % s, Nat.mod_lt _ hs⟩ := by
  simp only [HvdH.permS, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (⟨t * (j : ℕ) % s, Nat.mod_lt _ hs⟩)]
  · simp
  · intro i _ hi
    have hne : (i : ℕ) ≠ t * (j : ℕ) % s := fun h => hi (Fin.ext h)
    simp [hne]
  · intro hi
    exact absurd (Finset.mem_univ _) hi

/-- `P_t` acts by `k ↦ (t - sk mod t) mod t`. -/
lemma permT_mulVec (s t : ℕ) (ht : 0 < t) (z : Fin t → ℂ) (k : Fin t) :
    (HvdH.permT s t).mulVec z k = z ⟨(t - s * (k : ℕ) % t) % t, Nat.mod_lt _ ht⟩ := by
  simp only [HvdH.permT, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (⟨(t - s * (k : ℕ) % t) % t, Nat.mod_lt _ ht⟩)]
  · simp
  · intro i _ hi
    have hne : (i : ℕ) ≠ (t - s * (k : ℕ) % t) % t := fun h => hi (Fin.ext h)
    simp [hne]
  · intro hi
    exact absurd (Finset.mem_univ _) hi

/-- `t` divides `(t - sk mod t) mod t + sk`. -/
lemma permT_index_dvd (s t k : ℕ) (ht : 0 < t) :
    (t : ℤ) ∣ (((t - s * k % t) % t : ℕ) : ℤ) + (s : ℤ) * (k : ℤ) := by
  have hnat : t ∣ ((t - s * k % t) % t) + s * k := by
    rw [Nat.dvd_iff_mod_eq_zero, ← ZMod.val_natCast, ZMod.val_eq_zero, Nat.cast_add,
      ZMod.natCast_mod (t - s * k % t) t, ← ZMod.natCast_mod (s * k) t]
    have hsub : (t - s * k % t : ℕ) + (s * k % t) = t :=
      Nat.sub_add_cancel (le_of_lt (Nat.mod_lt _ ht))
    have h1 : (((t - s * k % t : ℕ)) : ZMod t) = -(((s * k % t : ℕ)) : ZMod t) := by
      rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add, hsub, ZMod.natCast_self]
    rw [h1]
    ring
  obtain ⟨q, hq⟩ := hnat
  refine ⟨(q : ℤ), ?_⟩
  have hX : ((((t - s * k % t) % t) + s * k : ℕ) : ℤ) = (t : ℤ) * (q : ℤ) := by
    rw [hq]; push_cast; ring
  have hsplit : ((((t - s * k % t) % t) + s * k : ℕ) : ℤ)
      = (((t - s * k % t) % t : ℕ) : ℤ) + (s : ℤ) * (k : ℤ) := by push_cast; ring
  linarith [hX, hsplit]

/-- The `k`-th row of `P_t` combined with the DFT of length `t`. -/
lemma dftMat_mulVec_permTrow (s t : ℕ) (ht : 0 < t) (w : Fin t → ℂ) (k : Fin t) :
    (HvdH.dftMat t).mulVec w ⟨(t - s * (k : ℕ) % t) % t, Nat.mod_lt _ ht⟩
      = FtZ t w (-((s : ℤ) * (k : ℤ))) := by
  rw [dftMat_mulVec_FtZ]
  obtain ⟨q, hq⟩ := permT_index_dvd s t (k : ℕ) ht
  have hq' : -((s : ℤ) * (k : ℤ)) = (((t - s * (k : ℕ) % t) % t : ℕ) : ℤ) + (t : ℤ) * (-q) := by
    linarith [hq]
  rw [hq', FtZ_period t ht w (((t - s * (k : ℕ) % t) % t : ℕ) : ℤ) (-q)]

/-- Root-of-unity sum in the `ℂ`-division form used by `FtZ`. -/
lemma rootUnitySum (t : ℕ) (ht : 0 < t) (C : ℤ) :
    (∑ l : Fin t, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (C : ℂ) * (l : ℂ) / (t : ℂ)))
      = if (t : ℤ) ∣ C then (t : ℂ) else 0 := by
  rw [← Work.DFT.rootSumZ t ht C]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  push_cast
  ring

/-- `resTmat` entrywise in complex form. -/
lemma resTmat_apply (s t α : ℕ) (k : Fin t) (j : Fin s) :
    HvdH.resTmat s t α k j =
      ∑' q : ℤ, (Real.exp (-Real.pi * (α : ℝ) ^ 2 * (t : ℝ) ^ 2 *
        ((k : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ) - (q : ℝ)) ^ 2) : ℂ) := by
  rw [HvdH.resTmat, Complex.ofReal_tsum]



/-- `(1/a) * (X * (a * Y)) = X * Y`. -/
lemma inv_mul_scale (a : ℂ) (ha : a ≠ 0) (X Y : ℂ) : (1 / a) * (X * (a * Y)) = X * Y := by
  field_simp


/-- `(1/a) * (X * (if P then a else 0)) = if P then X else 0`. -/
lemma inv_mul_ite (a : ℂ) (ha : a ≠ 0) (P : Prop) [Decidable P] (X : ℂ) :
    (1 / a) * (X * (if P then a else 0)) = if P then X else 0 := by
  by_cases h : P
  · rw [if_pos h, if_pos h]
    field_simp
  · rw [if_neg h, if_neg h, mul_zero, mul_zero]


/-- Root-of-unity sum in the `Phz` form. -/
lemma rootUnitySum_phz (t : ℕ) (ht : 0 < t) (C : ℤ) :
    (∑ l : Fin t, Phz t ((C : ℂ)) (l : ℕ)) = if (t : ℤ) ∣ C then (t : ℂ) else 0 := by
  rw [← rootUnitySum t ht C]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Phz]
  congr 1
  ring
end Work.ResMath
