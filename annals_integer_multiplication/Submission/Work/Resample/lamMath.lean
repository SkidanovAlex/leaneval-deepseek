import Mathlib
import Submission.Work.Resample.lamDefs
import Submission.Work.Resample.lamFacts
import Submission.Work.Resample.buQWsort

/-!
# The mathematics of the key formula (`Work.Resample.buLamWord`)

* `lamOk_iff_egRho` / `lamKey_eq_egLam`: the formula `lamKey s t m i` (defined in
  `Work.Resample.lamDefs`) computes `egLam s t i` when `m` is the `σ_t`-pre-image of `i`;
* `lamSorted_entry`: after sorting the list `lamRecs s t` of pairs `(σ_t k, k)` by `pairKey`,
  the `i`-th entry is `(i, lamMu s t i)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-! ## The two roundings -/

/-- The integer-floor characterisation of `Int.fdiv` at a positive divisor. -/
theorem fdiv_eq_iff_of_pos {N D : ℤ} (hD : 0 < D) {c : ℤ} :
    N.fdiv D = c ↔ c * D ≤ N ∧ N < (c + 1) * D := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt hD)]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 := Int.ediv_mul_le N (ne_of_gt hD)
      rw [h] at h1
      linarith
    · have h1 := Int.lt_ediv_add_one_mul_self N hD
      rw [h] at h1
      linarith
  · rintro ⟨h1, h2⟩
    have h3 : c ≤ N / D := (Int.le_ediv_iff_mul_le hD).mpr h1
    have h4 : N / D < c + 1 := (Int.ediv_lt_iff_lt_mul hD).mpr h2
    omega

/-- The row index `γ ℓ = egRho s t ℓ` of `C̃`, by an additive inequality. -/
theorem egRho_eq_iff (s t ℓ m : ℕ) (hs : 0 < s) :
    egRho s t ℓ = m ↔ 2 * s * m ≤ 2 * t * ℓ + s ∧ 2 * t * ℓ + s < 2 * s * (m + 1) := by
  have h2s : (0 : ℤ) < ((2 * s : ℕ) : ℤ) := by positivity
  have key : ((egRho s t ℓ : ℕ) : ℤ) = ((2 * t * ℓ + s : ℕ) : ℤ) / ((2 * s : ℕ) : ℤ) := by
    simp only [egRho]
    exact Int.natCast_div _ _
  constructor
  · intro h
    have h' : ((2 * t * ℓ + s : ℕ) : ℤ) / ((2 * s : ℕ) : ℤ) = (m : ℤ) := by
      rw [← key]
      exact_mod_cast h
    have h1 := Int.ediv_mul_le ((2 * t * ℓ + s : ℕ) : ℤ) (ne_of_gt h2s)
    rw [h'] at h1
    have h2 := Int.lt_ediv_add_one_mul_self ((2 * t * ℓ + s : ℕ) : ℤ) h2s
    rw [h'] at h2
    have h1c : (((2 * s * m : ℕ)) : ℤ) ≤ ((2 * t * ℓ + s : ℕ) : ℤ) := by
      push_cast at h1 ⊢
      linarith
    have h2c : ((2 * t * ℓ + s : ℕ) : ℤ) < (((2 * s * (m + 1) : ℕ)) : ℤ) := by
      push_cast at h2 ⊢
      linarith
    exact ⟨by exact_mod_cast h1c, by exact_mod_cast h2c⟩
  · rintro ⟨h1, h2⟩
    have h1z : (((2 * s * m : ℕ)) : ℤ) ≤ ((2 * t * ℓ + s : ℕ) : ℤ) := by exact_mod_cast h1
    have h2z : ((2 * t * ℓ + s : ℕ) : ℤ) < (((2 * s * (m + 1) : ℕ)) : ℤ) := by exact_mod_cast h2
    have hm1 : (m : ℤ) ≤ ((2 * t * ℓ + s : ℕ) : ℤ) / ((2 * s : ℕ) : ℤ) := by
      rw [Int.le_ediv_iff_mul_le h2s]
      push_cast at h1z ⊢
      linarith
    have hm2 : ((2 * t * ℓ + s : ℕ) : ℤ) / ((2 * s : ℕ) : ℤ) < (m : ℤ) + 1 := by
      rw [Int.ediv_lt_iff_lt_mul h2s]
      push_cast at h2z ⊢
      linarith
    have h3 : ((2 * t * ℓ + s : ℕ) : ℤ) / ((2 * s : ℕ) : ℤ) = (m : ℤ) := by omega
    have h4 : ((egRho s t ℓ : ℕ) : ℤ) = (m : ℤ) := by
      rw [key]
      exact h3
    exact_mod_cast h4

/-- The nearest-integer `lamL s t m = ⌊(2 s m + t)/(2 t)⌋`, by an additive inequality. -/
theorem lamL_eq_iff (s t m ℓ : ℕ) (ht : 0 < t) :
    lamL (s : ℤ) (t : ℤ) (m : ℤ) = (ℓ : ℤ) ↔
      2 * t * ℓ ≤ 2 * s * m + t ∧ 2 * s * m + t < 2 * t * (ℓ + 1) := by
  have hD : (0 : ℤ) < ((2 * t : ℕ) : ℤ) := by positivity
  have key : lamL (s : ℤ) (t : ℤ) (m : ℤ) =
      (((2 * s * m + t : ℕ) : ℤ)).fdiv ((2 * t : ℕ) : ℤ) := by
    simp only [lamL]
    push_cast
    ring_nf
  rw [key, fdiv_eq_iff_of_pos hD]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have h1c : (((2 * t * ℓ : ℕ)) : ℤ) ≤ (((2 * s * m + t : ℕ)) : ℤ) := by
        push_cast at h1 ⊢
        linarith
      exact_mod_cast h1c
    · have h2c : (((2 * s * m + t : ℕ)) : ℤ) < (((2 * t * (ℓ + 1) : ℕ)) : ℤ) := by
        push_cast at h2 ⊢
        linarith
      exact_mod_cast h2c
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have h1c : (((2 * t * ℓ : ℕ)) : ℤ) ≤ (((2 * s * m + t : ℕ)) : ℤ) := by
        exact_mod_cast h1
      push_cast at h1c ⊢
      linarith
    · have h2c : (((2 * s * m + t : ℕ)) : ℤ) < (((2 * t * (ℓ + 1) : ℕ)) : ℤ) := by
        exact_mod_cast h2
      push_cast at h2c ⊢
      linarith

theorem lamL_nonneg (s t m : ℕ) (ht : 0 < t) : 0 ≤ lamL (s : ℤ) (t : ℤ) (m : ℤ) := by
  simp only [lamL]
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by positivity)]
  exact Int.ediv_nonneg (by positivity) (by positivity)

/-! ## `lamOk` is the image of the row index -/

/-- The candidate `lamL s t m` is a genuine pre-image of `m` whenever `lamOk` holds. -/
theorem lamOk_toNat (s t m : ℕ) (hs : 0 < s) (hst : s < t)
    (h : lamOk (s : ℤ) (t : ℤ) (m : ℤ)) :
    (lamL (s : ℤ) (t : ℤ) (m : ℤ)).toNat < s ∧
      egRho s t (lamL (s : ℤ) (t : ℤ) (m : ℤ)).toNat = m := by
  have ht : 0 < t := lt_trans hs hst
  have hL0 : 0 ≤ lamL (s : ℤ) (t : ℤ) (m : ℤ) := lamL_nonneg s t m ht
  have hLnat : (((lamL (s : ℤ) (t : ℤ) (m : ℤ)).toNat : ℕ) : ℤ) =
      lamL (s : ℤ) (t : ℤ) (m : ℤ) := Int.toNat_of_nonneg hL0
  have h1 : -(s : ℤ) ≤ 2 * ((t : ℤ) * lamL (s : ℤ) (t : ℤ) (m : ℤ) - (s : ℤ) * (m : ℤ)) := h.1
  have h2 : 2 * ((t : ℤ) * lamL (s : ℤ) (t : ℤ) (m : ℤ) - (s : ℤ) * (m : ℤ)) < (s : ℤ) := h.2.1
  have h3 : lamL (s : ℤ) (t : ℤ) (m : ℤ) < (s : ℤ) := h.2.2
  have h1z : (2 * (s : ℤ) * (m : ℤ) : ℤ) ≤
      2 * (t : ℤ) * lamL (s : ℤ) (t : ℤ) (m : ℤ) + (s : ℤ) := by linarith
  have h2z : 2 * (t : ℤ) * lamL (s : ℤ) (t : ℤ) (m : ℤ) + (s : ℤ) <
      2 * (s : ℤ) * ((m : ℤ) + 1) := by linarith
  constructor
  · have : (((lamL (s : ℤ) (t : ℤ) (m : ℤ)).toNat : ℕ) : ℤ) < (s : ℤ) := by
      rw [hLnat]
      exact h3
    exact_mod_cast this
  · apply (egRho_eq_iff s t _ m hs).mpr
    refine ⟨?_, ?_⟩
    · have hz : (((2 * s * m : ℕ)) : ℤ) ≤
          ((2 * t * ((lamL (s : ℤ) (t : ℤ) (m : ℤ)).toNat) + s : ℕ) : ℤ) := by
        push_cast
        rw [hLnat]
        linarith
      exact_mod_cast hz
    · have hz : ((2 * t * ((lamL (s : ℤ) (t : ℤ) (m : ℤ)).toNat) + s : ℕ) : ℤ) <
          (((2 * s * (m + 1) : ℕ)) : ℤ) := by
        push_cast
        rw [hLnat]
        linarith
      exact_mod_cast hz

/-- `lamOk s t m` holds exactly for the values `m` of the row index `γ` on `ℓ < s`. -/
theorem lamOk_iff_egRho (s t m : ℕ) (hs : 0 < s) (hst : s < t) :
    lamOk (s : ℤ) (t : ℤ) (m : ℤ) ↔ ∃ ℓ, ℓ < s ∧ egRho s t ℓ = m := by
  constructor
  · intro h
    exact ⟨_, lamOk_toNat s t m hs hst h⟩
  · rintro ⟨ℓ, hℓs, hρ⟩
    have ht : 0 < t := lt_trans hs hst
    obtain ⟨hA, hB⟩ := (egRho_eq_iff s t ℓ m hs).mp hρ
    have hA' : (2 * (s : ℤ) * (m : ℤ) : ℤ) ≤ 2 * (t : ℤ) * (ℓ : ℤ) + (s : ℤ) := by
      have := hA
      push_cast at this ⊢
      linarith
    have hB' : 2 * (t : ℤ) * (ℓ : ℤ) + (s : ℤ) < 2 * (s : ℤ) * ((m : ℤ) + 1) := by
      have := hB
      push_cast at this ⊢
      linarith
    have hstZ : (s : ℤ) < (t : ℤ) := by exact_mod_cast hst
    have hLL : lamL (s : ℤ) (t : ℤ) (m : ℤ) = (ℓ : ℤ) := by
      apply (lamL_eq_iff s t m ℓ ht).mpr
      refine ⟨?_, ?_⟩
      · have hz : (((2 * t * ℓ : ℕ)) : ℤ) ≤ (((2 * s * m + t : ℕ)) : ℤ) := by
          push_cast
          nlinarith
        exact_mod_cast hz
      · have hz : (((2 * s * m + t : ℕ)) : ℤ) < (((2 * t * (ℓ + 1) : ℕ)) : ℤ) := by
          push_cast
          nlinarith
        exact_mod_cast hz
    have hDval : lamD (s : ℤ) (t : ℤ) (m : ℤ) =
        2 * ((t : ℤ) * (ℓ : ℤ) - (s : ℤ) * (m : ℤ)) := by
      rw [lamD, hLL]
    refine ⟨?_, ?_, ?_⟩
    · rw [hDval]
      linarith
    · rw [hDval]
      linarith
    · rw [hLL]
      exact_mod_cast hℓs

/-! ## The key formula -/

/-- **The key formula computes `egLam`**: if `m = σ_t^{-1}(i)` then `lamKey s t m i = egLam s t i`. -/
theorem lamKey_eq_egLam (s t m i : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t)
    (hm : m < t) (hi : i < t) (hσ : egSigT s t m = i) :
    lamKey (s : ℤ) (t : ℤ) (m : ℤ) (i : ℤ) = (egLam s t i : ℤ) := by
  have hs0 : 0 < s := by omega
  have ht : 0 < t := by omega
  have hs1 : (1 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs0
  have hiff : lamOk (s : ℤ) (t : ℤ) (m : ℤ) ↔ ∃ ℓ : Fin s, egNu s t (ℓ : ℕ) = i := by
    rw [lamOk_iff_egRho s t m hs0 hst]
    constructor
    · rintro ⟨ℓ, hℓs, hρ⟩
      exact ⟨⟨ℓ, hℓs⟩, by rw [egNu, hρ, hσ]⟩
    · rintro ⟨ℓ, hν⟩
      have h1 : egSigT s t (egRho s t (ℓ : ℕ)) = egSigT s t m := by
        show egNu s t (ℓ : ℕ) = egSigT s t m
        rw [hν, hσ]
      exact ⟨(ℓ : ℕ), ℓ.isLt,
        (egSigTKey s t hcop ht).2 _ _ (egRho_lt s t hs0 hst _ ℓ.isLt) hm h1⟩
  by_cases hok : lamOk (s : ℤ) (t : ℤ) (m : ℤ)
  · have hmem : ∃ ℓ : Fin s, egNu s t (ℓ : ℕ) = i := hiff.mp hok
    obtain ⟨hlt, hρ⟩ := lamOk_toNat s t m hs0 hst hok
    have hν0 : egNu s t ((lamL (s : ℤ) (t : ℤ) (m : ℤ)).toNat) = i := by
      rw [egNu, hρ, hσ]
    have hchoose : (Classical.choose hmem : Fin s) =
        ⟨(lamL (s : ℤ) (t : ℤ) (m : ℤ)).toNat, hlt⟩ := by
      apply egNu_inj s t hs0 hst hcop
      show egNu s t ((Classical.choose hmem : Fin s) : ℕ) =
        egNu s t (((⟨(lamL (s : ℤ) (t : ℤ) (m : ℤ)).toNat, hlt⟩ : Fin s) : ℕ))
      rw [Classical.choose_spec hmem]
      exact hν0.symm
    have hL0 : 0 ≤ lamL (s : ℤ) (t : ℤ) (m : ℤ) := lamL_nonneg s t m ht
    rw [lamKey_of_ok hs1 hok, egLam_of_mem s t i hmem, hchoose]
    exact (Int.toNat_of_nonneg hL0).symm
  · have hnot : ¬ ∃ ℓ : Fin s, egNu s t (ℓ : ℕ) = i := fun h => hok (hiff.mpr h)
    rw [lamKey_of_not hs1 hok, egLam_of_not s t i hnot]
    push_cast
    ring

/-! ## The sorted list of pairs `(σ_t k, k)` -/

theorem lamRecs_key_nodup (s t : ℕ) (hcop : Nat.Coprime s t) (ht : 0 < t) :
    ((lamRecs s t).map pairKey).Nodup := by
  rw [lamRecs_key]
  apply List.Nodup.map_on
  · intro x hx y hy hxy
    exact (egSigTKey s t hcop ht).2 x y (List.mem_range.mp hx) (List.mem_range.mp hy)
      (by exact_mod_cast hxy)
  · exact List.nodup_range

theorem lamRecs_mem {s t : ℕ} {x : Val} (hx : x ∈ lamRecs s t) :
    ∃ k, k < t ∧ x = lamRec s t k := by
  rw [lamRecs, List.mem_map] at hx
  obtain ⟨k, hk, hkx⟩ := hx
  exact ⟨k, List.mem_range.mp hk, hkx.symm⟩

/-- The `i`-th entry of the list `lamRecs s t` sorted by `pairKey` is `(i, lamMu s t i)`. -/
theorem lamSorted_entry (s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t)
    (ys : List Val) (hperm : ys.Perm (lamRecs s t))
    (hsort : ys.Pairwise fun a b => pairKey a < pairKey b) :
    ∀ i < t, ys.getD i .nil = .cons (.int (i : ℤ)) (.int ((lamMu s t i : ℕ) : ℤ)) := by
  have ht : 0 < t := by omega
  have hyslen : ys.length = t := by rw [hperm.length_eq, lamRecs_length]
  have hmem : ∀ x ∈ ys, ∃ k, k < t ∧ x = lamRec s t k := by
    intro x hx
    exact lamRecs_mem ((hperm.mem_iff).mp hx)
  have hkey_nonneg : ∀ x ∈ ys, (0 : ℤ) ≤ pairKey x := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := hmem x hx
    rw [pairKey_lamRec]
    exact Int.natCast_nonneg _
  have hsort' : ys.Pairwise fun a b => (pairKey a).toNat < (pairKey b).toNat := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have h1 : pairKey ys[i] < pairKey ys[j] := (List.pairwise_iff_getElem.mp hsort) i j hi hj hij
    have hf1 : ((pairKey ys[i]).toNat : ℤ) = pairKey ys[i] :=
      Int.toNat_of_nonneg (hkey_nonneg _ (List.getElem_mem hi))
    have hf2 : ((pairKey ys[j]).toNat : ℤ) = pairKey ys[j] :=
      Int.toNat_of_nonneg (hkey_nonneg _ (List.getElem_mem hj))
    have hz : (((pairKey ys[i]).toNat : ℤ)) < (((pairKey ys[j]).toNat : ℤ)) := by
      rw [hf1, hf2]
      exact h1
    exact_mod_cast hz
  have hnd' : ((lamRecs s t).map fun x => (pairKey x).toNat).Nodup := by
    have heq : (lamRecs s t).map (fun x => (pairKey x).toNat) =
        (List.range t).map (fun k => egSigT s t k) := by
      rw [lamRecs, List.map_map]
      apply List.map_congr_left
      intro k hk
      show (pairKey (lamRec s t k)).toNat = egSigT s t k
      rw [pairKey_lamRec, Int.toNat_natCast]
    rw [heq]
    apply List.Nodup.map_on
    · intro x hx y hy hxy
      exact (egSigTKey s t hcop ht).2 x y (List.mem_range.mp hx) (List.mem_range.mp hy) hxy
    · exact List.nodup_range
  have hcov : ∀ ℓ < t, ∃ x ∈ lamRecs s t, (pairKey x).toNat = ℓ := by
    intro ℓ hℓt
    refine ⟨lamRec s t (lamMu s t ℓ), ?_, ?_⟩
    · rw [lamRecs, List.mem_map]
      exact ⟨lamMu s t ℓ, List.mem_range.mpr (lamMu_lt s t hcop ht ℓ hℓt), rfl⟩
    · show (pairKey (lamRec s t (lamMu s t ℓ))).toNat = ℓ
      rw [pairKey_lamRec, Int.toNat_natCast]
      exact lamMu_spec s t hcop ht ℓ hℓt
  have hentry := buQWsort (fun x : Val => (pairKey x).toNat) (lamRecs s t) ys t hperm hsort' hnd' hcov
  intro i hi
  obtain ⟨hmem_i, hkey_i⟩ := hentry i hi
  obtain ⟨k, hk, hkx⟩ := lamRecs_mem hmem_i
  have hkx' : ys.getD i .nil = lamRec s t k := by
    have h1 : ys.getD i .nil = ys[i] := List.getD_eq_getElem _ _ (by rw [hyslen]; exact hi)
    have h2 : ys.getD i default = ys[i] := List.getD_eq_getElem _ _ (by rw [hyslen]; exact hi)
    rw [h1, ← h2]
    exact hkx
  have hσk : egSigT s t k = i := by
    have h := hkey_i
    rw [hkx, pairKey_lamRec, Int.toNat_natCast] at h
    exact h
  have hk_eq : k = lamMu s t i := by
    have h1 : egSigT s t k = egSigT s t (lamMu s t i) := by
      rw [hσk, lamMu_spec s t hcop ht i hi]
    exact (egSigTKey s t hcop ht).2 k (lamMu s t i) hk (lamMu_lt s t hcop ht i hi) h1
  rw [hkx', hk_eq]
  simp only [lamRec]
  rw [lamMu_spec s t hcop ht i hi]

end Work.Resample
