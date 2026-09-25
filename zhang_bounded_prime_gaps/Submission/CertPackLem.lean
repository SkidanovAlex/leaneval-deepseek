import Submission.CertPacked
import Submission.Commons.Data.Nat.packed_sparse_block
import Submission.Commons.Data.Nat.packed_sparse_block_zero

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 200000

open scoped BigOperators
open Finset

/-!
# The packed representation: extraction and state-space facts

This module proves (F1) of the roadmap SESSION 46 §3 — the extraction lemma
`unpack_pack` — together with the state-space facts (`certStates.Nodup`, class membership,
`muVal` linearity on `m - e_v`, class closure under `+ e_v` / `- e_v`) that the correctness of
the packed operations `packedMulA` / `packedMulH` rests on.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- `certStates` has no repeated element.  Immediate from `pos_inj`. -/
theorem certStates_nodup : certStates.Nodup := pos_inj.of_map

/-- Every class list is duplicate-free. -/
theorem classJ_nodup (j : ℕ) : (classJ j).Nodup := by
  rw [classJ]; exact certStates_nodup.filter _

/-- Membership in a class. -/
theorem mem_classJ_iff {m : MV} {j : ℕ} : m ∈ classJ j ↔ m ∈ certStates ∧ degV m = 2 * j := by
  rw [classJ, List.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, of_decide_eq_true h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, decide_eq_true_eq.mpr h2⟩

/-- The class list viewed as a `Finset`. -/
def cset (j : ℕ) : Finset MV := (classJ j).toFinset

theorem mem_cset {m : MV} {j : ℕ} : m ∈ cset j ↔ m ∈ classJ j := List.mem_toFinset

/-- The class word is a `Finset` sum over the class. -/
theorem classWord_eq_sum (F : MV → ℕ) (i : ℕ) :
    classWord F i = ∑ m ∈ cset i, F m * 2 ^ (BB * muVal m) := by
  unfold classWord cset
  exact (List.sum_toFinset (fun m => F m * 2 ^ (BB * muVal m)) (classJ_nodup i)).symm

/-! ## Linearity of `muVal` on `m ± e_v` -/

theorem muVal_sub_evec (m : MV) (v : Fin 12) (hv : 1 ≤ m v) :
    muVal (m - evec v) = muVal m - mu v := by
  have h1 : ∀ i : Fin 12, i ≠ v → (m - evec v) i = m i := by
    intro i hi
    rw [Pi.sub_apply, evec, Pi.single_eq_of_ne hi 1, tsub_zero]
  have h2 : (m - evec v) v = m v - 1 := by
    rw [Pi.sub_apply, evec, Pi.single_eq_same]
  have hA : muVal (m - evec v)
      = ∑ i ∈ Finset.univ.erase v, mu i * (m - evec v) i + mu v * (m v - 1) := by
    unfold muVal
    rw [← Finset.sum_erase_add _ (fun i => mu i * (m - evec v) i) (Finset.mem_univ v), h2]
  have hB : muVal m = ∑ i ∈ Finset.univ.erase v, mu i * m i + mu v * m v := by
    unfold muVal
    rw [← Finset.sum_erase_add _ (fun i => mu i * m i) (Finset.mem_univ v)]
  have hC : ∑ i ∈ Finset.univ.erase v, mu i * (m - evec v) i
      = ∑ i ∈ Finset.univ.erase v, mu i * m i :=
    Finset.sum_congr rfl (fun i hi => by rw [h1 i (Finset.mem_erase.mp hi).1])
  rw [hA, hB, hC]
  have h3 : mu v * (m v - 1) + mu v = mu v * m v := by
    have h4 : mu v * (m v - 1) + mu v * 1 = mu v * m v := by
      rw [← Nat.mul_add]
      congr 1
      omega
    simpa using h4
  omega

theorem sub_add_evec (m : MV) (v : Fin 12) (hv : 1 ≤ m v) : (m - evec v) + evec v = m := by
  funext i
  rw [Pi.add_apply, Pi.sub_apply]
  by_cases h : i = v
  · subst h
    rw [evec, Pi.single_eq_same]
    omega
  · rw [evec, Pi.single_eq_of_ne h 1]
    have h2 : (m i - 0) = m i := by omega
    rw [h2, add_zero]

theorem add_sub_evec (m : MV) (v : Fin 12) : (m + evec v) - evec v = m := by
  funext i
  rw [Pi.sub_apply, Pi.add_apply]
  by_cases h : i = v
  · subst h
    rw [evec, Pi.single_eq_same]
    omega
  · rw [evec, Pi.single_eq_of_ne h 1, add_zero, tsub_zero]

/-! ## Class closure -/

theorem mem_classJ_add (j : ℕ) (v : Fin 12) (m : MV) (hm : m ∈ classJ j)
    (hj : j + (v : ℕ) + 1 < 13) : m + evec v ∈ classJ (j + (v : ℕ) + 1) := by
  have hdeg : degV m = 2 * j := (mem_classJ_iff.mp hm).2
  have hcert : m ∈ certStates := (mem_classJ_iff.mp hm).1
  have h2 : degV (m + evec v) = 2 * (j + (v : ℕ) + 1) := by
    rw [degV_add_single, hdeg]; ring
  have hle : degV (m + evec v) ≤ 24 := by
    rw [h2]; omega
  exact mem_classJ_iff.mpr ⟨mem_certStates_of_deg _ hle, h2⟩

theorem mem_classJ_sub (i j : ℕ) (v : Fin 12) (hij : i = j + (v : ℕ) + 1) (m : MV)
    (hm : m ∈ classJ i) (hv : 1 ≤ m v) : m - evec v ∈ classJ j := by
  have hdeg : degV m = 2 * i := (mem_classJ_iff.mp hm).2
  have hcert : m ∈ certStates := (mem_classJ_iff.mp hm).1
  have h1 := degV_sub_evec_add m v hv
  have h2 : degV (m - evec v) = 2 * j := by
    rw [hij] at hdeg
    have : degV (m - evec v) + 2 * ((v : ℕ) + 1) = 2 * (j + (v : ℕ) + 1) := by
      rw [h1, hdeg]
    omega
  exact mem_classJ_iff.mpr ⟨certStates_sub_evec m hcert v hv, h2⟩

/-! ## (F1) the extraction lemma -/

/-- A `List.sum` of a mapped list is the `Fin`-indexed sum over the list's entries. -/
theorem list_sum_map_eq_fin_sum {α : Type*} (l : List α) (g : α → ℕ) :
    (l.map g).sum = ∑ i : Fin l.length, g (l[(i : ℕ)]) := by
  rw [← List.sum_ofFn (M := ℕ) (f := fun i : Fin l.length => g (l[(i : ℕ)]))]
  congr 1
  refine List.ext_getElem ?_ ?_
  · simp
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getElem_map]

/-- Injectivity of a list index map into a `Nodup` image. -/
theorem fin_getElem_inj_of_nodup_map {α β : Type*} {l : List α} {f : α → β}
    (h : (l.map f).Nodup) (a b : Fin l.length)
    (hab : f (l[(a : ℕ)]) = f (l[(b : ℕ)])) : a = b := by
  have h1 : (l.map f)[(a : ℕ)] = (l.map f)[(b : ℕ)] := by
    rw [List.getElem_map, List.getElem_map, hab]
  exact Fin.ext ((h.getElem_inj_iff).mp h1)

/-- **(F1)** The packed word `pack F` reads back the coefficient function `F` at every state,
provided all values of `F` are smaller than the block size `2^BB`. -/
theorem unpack_pack (F : MV → ℕ) (hF : ∀ m ∈ certStates, F m < 2 ^ BB) (m : MV)
    (hm : m ∈ certStates) :
    unpack (pack F) m = F m := by
  have hdeg := degV_le_of_mem_certStates m hm
  have hjeven : 2 * (degV m / 2) = degV m := degV_even m
  have hjlt : degV m / 2 < 13 := by omega
  have hmclass : m ∈ classJ (degV m / 2) := by
    rw [mem_classJ_iff]
    exact ⟨hm, by omega⟩
  have hgetD : (pack F).getD (degV m / 2) 0 = classWord F (degV m / 2) := by
    unfold pack
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hjlt]
    rfl
  have hB : 1 < 2 ^ BB := Nat.one_lt_pow (n := BB) (a := 2) (by decide) (by decide)
  -- `classWord F j` as a `Fin`-sum over the class list
  have hsum : classWord F (degV m / 2)
      = ∑ i : Fin (classJ (degV m / 2)).length,
          F ((classJ (degV m / 2))[(i : ℕ)])
            * 2 ^ (BB * muVal ((classJ (degV m / 2))[(i : ℕ)])) := by
    unfold classWord
    exact list_sum_map_eq_fin_sum _ _
  obtain ⟨i0, hi0, hval⟩ := List.getElem_of_mem hmclass
  have hinj : Function.Injective (fun i : Fin (classJ (degV m / 2)).length =>
      muVal ((classJ (degV m / 2))[(i : ℕ)])) := by
    intro a b hab
    exact fin_getElem_inj_of_nodup_map (mu_inj_class _ hjlt) a b hab
  have hx : ∀ i : Fin (classJ (degV m / 2)).length,
      F ((classJ (degV m / 2))[(i : ℕ)]) < 2 ^ BB := fun i =>
    hF _ (mem_classJ_iff.mp (List.getElem_mem _)).1
  have hkey := Commons.Data.Nat.packed_sparse_block (B := 2 ^ BB) hB
    (fun i : Fin (classJ (degV m / 2)).length => muVal ((classJ (degV m / 2))[(i : ℕ)]))
    hinj (fun i => F ((classJ (degV m / 2))[(i : ℕ)])) hx
    (⟨(i0 : ℕ), hi0⟩ : Fin (classJ (degV m / 2)).length)
  rw [unpack, Nat.shiftRight_eq_div_pow, hgetD, hsum]
  simp only [Nat.pow_mul] at hkey ⊢
  rw [show muVal m = muVal ((classJ (degV m / 2))[i0]) from by rw [hval],
    show F m = F ((classJ (degV m / 2))[i0]) from by rw [hval]]
  exact hkey


/-! ## (F2) the packed operations compute `mulA` / `mulH` -/

theorem mu_le_muVal (m : MV) (v : Fin 12) (hv : 1 ≤ m v) : mu v ≤ muVal m := by
  unfold muVal
  calc mu v = mu v * 1 := (mul_one _).symm
    _ ≤ mu v * m v := Nat.mul_le_mul_left _ hv
    _ ≤ ∑ i : Fin 12, mu i * m i :=
        Finset.single_le_sum (f := fun i : Fin 12 => mu i * m i)
          (fun i _ => Nat.zero_le _) (Finset.mem_univ v)

theorem muVal_eq_sub_add (m : MV) (v : Fin 12) (hv : 1 ≤ m v) :
    muVal m = muVal (m - evec v) + mu v := by
  have h1 := muVal_sub_evec m v hv
  have h2 := mu_le_muVal m v hv
  omega

/-- **Shifting a class word.**  Summing `Q (m - e_v) · 2^(BB·muVal m)` over the states `m` of
class `i` that contain the part `2(v+1)` is the same as reading the class word of `Q` at class
`i - v - 1` and shifting it left by `BB · mu v`. -/
theorem classWord_shift (Q : MV → ℕ) (v : Fin 12) (i : Fin 13) :
    (∑ m ∈ (cset (i : ℕ)).filter (fun m => 1 ≤ m v), Q (m - evec v) * 2 ^ (BB * muVal m))
      = if (v : ℕ) + 1 ≤ (i : ℕ) then
          classWord Q ((i : ℕ) - (v : ℕ) - 1) * 2 ^ (BB * mu v) else 0 := by
  by_cases hv : (v : ℕ) + 1 ≤ (i : ℕ)
  · rw [if_pos hv]
    have hjlt : ((i : ℕ) - (v : ℕ) - 1) + (v : ℕ) + 1 < 13 := by
      have := i.isLt; omega
    have hji : ((i : ℕ) - (v : ℕ) - 1) + (v : ℕ) + 1 = (i : ℕ) := by omega
    have hbij : (∑ m ∈ (cset (i : ℕ)).filter (fun m => 1 ≤ m v),
          Q (m - evec v) * 2 ^ (BB * muVal m))
        = ∑ m' ∈ cset ((i : ℕ) - (v : ℕ) - 1),
            Q m' * 2 ^ (BB * muVal m') * 2 ^ (BB * mu v) := by
      refine Finset.sum_bij (fun m _ => m - evec v) ?_ ?_ ?_ ?_
      · intro m hm
        obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
        exact mem_cset.mpr (mem_classJ_sub _ _ v hji.symm m (mem_cset.mp hm1) hm2)
      · intro m1 hm1 m2 hm2 heq
        have h1 : 1 ≤ m1 v := (Finset.mem_filter.mp hm1).2
        have h2 : 1 ≤ m2 v := (Finset.mem_filter.mp hm2).2
        rw [← sub_add_evec m1 v h1, heq, sub_add_evec m2 v h2]
      · intro m' hm'
        refine ⟨m' + evec v, ?_, add_sub_evec m' v⟩
        rw [Finset.mem_filter]
        refine ⟨mem_cset.mpr ?_, ?_⟩
        · have h := mem_classJ_add _ v m' (mem_cset.mp hm') hjlt
          rwa [hji] at h
        · rw [Pi.add_apply, evec, Pi.single_eq_same]; omega
      · intro m hm
        have hm2 : 1 ≤ m v := (Finset.mem_filter.mp hm).2
        have hmu := muVal_eq_sub_add m v hm2
        rw [hmu, Nat.mul_add, pow_add]
        ring
    rw [hbij, ← Finset.sum_mul, ← classWord_eq_sum Q ((i : ℕ) - (v : ℕ) - 1)]
  · rw [if_neg hv]
    refine Finset.sum_eq_zero (fun m hm => ?_)
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
    have hdeg : degV m = 2 * (i : ℕ) := (mem_classJ_iff.mp (mem_cset.mp hm1)).2
    have hle : 2 * ((v : ℕ) + 1) ≤ degV m := by
      unfold degV
      calc 2 * ((v : ℕ) + 1) = 2 * ((v : ℕ) + 1) * 1 := by ring
        _ ≤ 2 * ((v : ℕ) + 1) * m v := Nat.mul_le_mul_left _ hm2
        _ ≤ ∑ j : Fin 12, 2 * ((j : ℕ) + 1) * m j :=
            Finset.single_le_sum (f := fun j : Fin 12 => 2 * ((j : ℕ) + 1) * m j)
              (fun j _ => Nat.zero_le _) (Finset.mem_univ v)
    omega

/-- **The class word of a binomial operator.**  This is the algebraic content of (F2): the packed
"shift-add" of `packedMulA`/`packedMulH` computes the coefficient operator `mulBin c d`. -/
theorem classWord_mulBin (c : ℕ) (d : Fin 12 → ℕ) (Q : XVec) (i : Fin 13) :
    classWord (mulBin c d Q) (i : ℕ)
      = c * classWord Q (i : ℕ)
        + ∑ v : Fin 12, if (v : ℕ) + 1 ≤ (i : ℕ) then
            d v * (classWord Q ((i : ℕ) - (v : ℕ) - 1) * 2 ^ (BB * mu v)) else 0 := by
  have hstep : (∑ m ∈ cset (i : ℕ),
        (∑ v : Fin 12, if 1 ≤ m v then d v * Q (m - evec v) else 0) * 2 ^ (BB * muVal m))
      = ∑ v : Fin 12, if (v : ℕ) + 1 ≤ (i : ℕ) then
            d v * (classWord Q ((i : ℕ) - (v : ℕ) - 1) * 2 ^ (BB * mu v)) else 0 := by
    refine (Finset.sum_congr rfl (fun m (_ : m ∈ cset (i : ℕ)) =>
      Finset.sum_mul (s := Finset.univ)
        (f := fun v : Fin 12 => if 1 ≤ m v then d v * Q (m - evec v) else 0)
        (a := 2 ^ (BB * muVal m)))).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have h1 : (∑ m ∈ cset (i : ℕ),
          (if 1 ≤ m v then d v * Q (m - evec v) else 0) * 2 ^ (BB * muVal m))
        = ∑ m ∈ cset (i : ℕ),
            (if 1 ≤ m v then (d v * Q (m - evec v)) * 2 ^ (BB * muVal m) else 0) := by
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [ite_mul, zero_mul]
    rw [h1, ← Finset.sum_filter]
    have h2 : (∑ m ∈ (cset (i : ℕ)).filter (fun m => 1 ≤ m v),
          (d v * Q (m - evec v)) * 2 ^ (BB * muVal m))
        = d v * (∑ m ∈ (cset (i : ℕ)).filter (fun m => 1 ≤ m v),
            Q (m - evec v) * 2 ^ (BB * muVal m)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
    rw [h2, classWord_shift Q v i, mul_ite, mul_zero]
  have hpt : ∀ m ∈ cset (i : ℕ), mulBin c d Q m * 2 ^ (BB * muVal m)
      = c * (Q m * 2 ^ (BB * muVal m))
        + (∑ v : Fin 12, if 1 ≤ m v then d v * Q (m - evec v) else 0)
            * 2 ^ (BB * muVal m) := by
    intro m _
    simp only [mulBin]
    ring
  rw [classWord_eq_sum (mulBin c d Q) (i : ℕ)]
  calc ∑ m ∈ cset (i : ℕ), mulBin c d Q m * 2 ^ (BB * muVal m)
      = ∑ m ∈ cset (i : ℕ), (c * (Q m * 2 ^ (BB * muVal m))
          + (∑ v : Fin 12, if 1 ≤ m v then d v * Q (m - evec v) else 0)
            * 2 ^ (BB * muVal m)) :=
        Finset.sum_congr rfl hpt
    _ = c * (∑ m ∈ cset (i : ℕ), Q m * 2 ^ (BB * muVal m))
          + ∑ m ∈ cset (i : ℕ),
              (∑ v : Fin 12, if 1 ≤ m v then d v * Q (m - evec v) else 0)
                * 2 ^ (BB * muVal m) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = c * classWord Q (i : ℕ)
          + ∑ v : Fin 12, if (v : ℕ) + 1 ≤ (i : ℕ) then
              d v * (classWord Q ((i : ℕ) - (v : ℕ) - 1) * 2 ^ (BB * mu v)) else 0 := by
        rw [hstep, classWord_eq_sum Q (i : ℕ)]

/-- `getD` on a packed word. -/
theorem pack_getD (F : MV → ℕ) (k : ℕ) (hk : k < 13) : (pack F).getD k 0 = classWord F k := by
  unfold pack
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hk]
  rfl

/-- The packed word is a `List.ofFn`. -/
theorem pack_eq_ofFn (F : MV → ℕ) :
    pack F = List.ofFn (fun i : Fin 13 => classWord F (i : ℕ)) := rfl

/-- **(F2a)** The packed multiplication by `A` computes `mulA`. -/
theorem packedMulA_pack (F : MV → ℕ) : packedMulA (pack F) = pack (mulA F) := by
  rw [mulA_eq_mulBin]
  unfold packedMulA
  rw [pack_eq_ofFn (mulBin 1 (fun v : Fin 12 => Nat.factorial (2 * ((v : ℕ) + 1))) F)]
  rw [List.ofFn_inj]
  funext i
  rw [pack_getD F (i : ℕ) i.isLt, classWord_mulBin]
  rw [one_mul, Nat.add_left_cancel_iff]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  by_cases hv : (v : ℕ) + 1 ≤ (i : ℕ)
  · rw [if_pos hv, if_pos hv, pack_getD F ((i : ℕ) - (v : ℕ) - 1) (by have := i.isLt; omega),
      Nat.shiftLeft_eq]
  · rw [if_neg hv, if_neg hv]

/-- **(F2b)** The packed multiplication by `h_w` computes `mulH`. -/
theorem packedMulH_pack (w : Fin 12) (F : MV → ℕ) :
    packedMulH w (pack F) = pack (mulH w F) := by
  rw [mulH_eq_mulBin]
  unfold packedMulH
  rw [pack_eq_ofFn (mulBin (Nat.factorial (2 * ((w : ℕ) + 1)))
        (fun v : Fin 12 => Nat.factorial (2 * ((v : ℕ) + 1) + 2 * ((w : ℕ) + 1))) F)]
  rw [List.ofFn_inj]
  funext i
  rw [pack_getD F (i : ℕ) i.isLt, classWord_mulBin]
  rw [Nat.add_left_cancel_iff]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  by_cases hv : (v : ℕ) + 1 ≤ (i : ℕ)
  · rw [if_pos hv, if_pos hv, pack_getD F ((i : ℕ) - (v : ℕ) - 1) (by have := i.isLt; omega),
      Nat.shiftLeft_eq]
  · rw [if_neg hv, if_neg hv]

end Commons.NumberTheory.MaynardSieve
