import Submission.ZagierHoffmanProof.DescentGen

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Polynomial
open scoped BigOperators

/-!
# The one-residue case of the Frobenius descent

For an index `N ≡ q - 1 (mod q)` the general descent of `DescentGen.lean` collapses to a single
residue vector `(q-1, 0, 0, …)`: the no-carry condition forces every other entry to be divisible
by `q` and hence to vanish.  The resulting identity

  `c_{q m + q - 1} = (c_m) ^ q`

is the natural generalisation of the classical recursion `c_{q^M - 1} = (c_{q^{M-1}-1})^q`
(`Descent.atCoeff_card_pow_sub_one_succ`).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- The single residue vector `(q-1, 0, 0, …)`. -/
noncomputable def deltaRes {B : ℕ} : Fin B → ℕ := fun i => if (i : ℕ) = 0 then Nat.card F - 1 else 0

omit [Field F] [Finite F] in
lemma deltaRes_apply {B : ℕ} (i : Fin B) :
    deltaRes F i = if (i : ℕ) = 0 then Nat.card F - 1 else 0 := rfl

omit [Field F] [Finite F] in
lemma deltaRes_apply_zero {B : ℕ} (hB : 0 < B) :
    deltaRes F (⟨0, hB⟩ : Fin B) = Nat.card F - 1 := by
  rw [deltaRes_apply, if_pos rfl]

omit [Field F] [Finite F] in
lemma deltaRes_apply_ne {B : ℕ} {i : Fin B} (hi : (i : ℕ) ≠ 0) : deltaRes F i = 0 := by
  rw [deltaRes_apply, if_neg hi]

/-- A vector with a single non-zero entry has no carries in base `p`. -/
lemma noCarryVec_single {B : ℕ} (hB : 0 < B) (x : ℕ) :
    NoCarryVec F (fun i : Fin B => if (i : ℕ) = 0 then x else 0) := by
  have hp0 : 0 < ringChar F := Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite F)
  intro j
  rw [Finset.sum_eq_single (⟨0, hB⟩ : Fin B)]
  · show (if (((⟨0, hB⟩ : Fin B)) : ℕ) = 0 then x else 0) / ringChar F ^ j % ringChar F < ringChar F
    rw [if_pos rfl]
    exact Nat.mod_lt _ hp0
  · intro i _ hi
    have hi' : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
    show (if ((i : Fin B) : ℕ) = 0 then x else 0) / ringChar F ^ j % ringChar F = 0
    rw [if_neg hi', Nat.zero_div, Nat.zero_mod]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma deltaRes_noCarry (B : ℕ) (hB : 0 < B) : NoCarryVec F (deltaRes F (B := B)) :=
  noCarryVec_single F hB (Nat.card F - 1)

/-- The multinomial coefficient of a single-entry vector is `1`. -/
lemma deltaRes_multinomial (B : ℕ) (hB : 0 < B) :
    Nat.multinomial Finset.univ (deltaRes F (B := B)) = 1 := by
  have h := Nat.multinomial_congr_of_sdiff (s := ({⟨0, hB⟩} : Finset (Fin B)))
      (t := Finset.univ) (f := deltaRes F (B := B)) (g := deltaRes F (B := B))
      (fun x _ => Finset.mem_univ x)
      (fun x hx => by
        rw [Finset.mem_sdiff] at hx
        rw [deltaRes_apply_ne F (fun h => hx.2 (Finset.mem_singleton.mpr (Fin.ext h)))])
      (fun x _ => rfl)
  rw [Nat.multinomial_singleton] at h
  exact h.symm

/-- The residue sum of `(q-1, 0, 0, …)` is `q - 1`. -/
lemma deltaRes_sum {B : ℕ} (hB : 0 < B) :
    (∑ i : Fin B, deltaRes F i * Nat.card F ^ (i : ℕ)) = Nat.card F - 1 := by
  rw [Finset.sum_eq_single (⟨0, hB⟩ : Fin B)]
  · rw [deltaRes_apply_zero, Nat.pow_zero, mul_one]
  · intro i _ hi
    rw [deltaRes_apply_ne F (fun h => hi (Fin.ext h)), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The `0`-th entry is forced.**  A residue vector of an index `≡ q - 1 (mod q)` has
`res_0 = q - 1`. -/
theorem residueSet_apply_zero {m B : ℕ} (hB : 0 < B) {res : Fin B → ℕ}
    (hres : res ∈ residueSet F (Nat.card F * m + (Nat.card F - 1)) B) :
    res ⟨0, hB⟩ = Nat.card F - 1 := by
  classical
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  obtain ⟨hle, hdvd, hresv, hnc⟩ := (mem_residueSet F).mp hres
  have hmod0 : (∑ k : Fin B, res k * Nat.card F ^ (k : ℕ)) % Nat.card F
      = res ⟨0, hB⟩ % Nat.card F := by
    have hsplit := (Finset.sum_erase_add (Finset.univ : Finset (Fin B))
        (fun k => res k * Nat.card F ^ (k : ℕ)) (Finset.mem_univ (⟨0, hB⟩ : Fin B))).symm
    have hdvd : Nat.card F ∣ ∑ k ∈ (Finset.univ.erase (⟨0, hB⟩ : Fin B)),
        res k * Nat.card F ^ (k : ℕ) := by
      refine Finset.dvd_sum (fun k hk => ?_)
      rw [Finset.mem_erase] at hk
      have hk1 : 1 ≤ (k : ℕ) := by
        rcases Nat.eq_zero_or_pos (k : ℕ) with h | h
        · exact absurd (Fin.ext (by simpa using h)) hk.1
        · exact h
      refine ⟨res k * Nat.card F ^ ((k : ℕ) - 1), ?_⟩
      have hd : Nat.card F ^ (k : ℕ) = Nat.card F * Nat.card F ^ ((k : ℕ) - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hk1]
      rw [hd]; ring
    rw [hsplit, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, Nat.zero_add, Nat.pow_zero, Nat.mul_one]
    exact Nat.mod_mod ..
  have hNmod : (Nat.card F * m + (Nat.card F - 1)) % Nat.card F = Nat.card F - 1 := by
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod,
      Nat.zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have hsub : (Nat.card F * m + (Nat.card F - 1)
        - ∑ k : Fin B, res k * Nat.card F ^ (k : ℕ)) % Nat.card F = 0 :=
    Nat.mod_eq_zero_of_dvd hdvd
  have hkey : (∑ k : Fin B, res k * Nat.card F ^ (k : ℕ)) % Nat.card F = Nat.card F - 1 := by
    have h1 : (Nat.card F * m + (Nat.card F - 1)
        - ∑ k : Fin B, res k * Nat.card F ^ (k : ℕ)
        + ∑ k : Fin B, res k * Nat.card F ^ (k : ℕ)) % Nat.card F
        = (Nat.card F * m + (Nat.card F - 1)) % Nat.card F := by
      rw [Nat.sub_add_cancel hle]
    rw [Nat.add_mod, hsub, Nat.zero_add, hNmod] at h1
    simpa [Nat.mod_mod] using h1
  rw [hmod0] at hkey
  have hlt : res ⟨0, hB⟩ < Nat.card F := hresv _
  have h := Nat.mod_add_div (res ⟨0, hB⟩) (Nat.card F)
  rw [hkey, Nat.div_eq_of_lt hlt, mul_zero, add_zero] at h
  exact h.symm

/-- **The other entries vanish**: the no-carry condition at the low digits kills every entry of a
residue vector of `(q - 1, 0, 0, …)`-type except the first. -/
theorem residueSet_apply_ne_zero {m B : ℕ} (hB : 0 < B) {res : Fin B → ℕ}
    (hres : res ∈ residueSet F (Nat.card F * m + (Nat.card F - 1)) B)
    {i : Fin B} (hi : i ≠ (⟨0, hB⟩ : Fin B)) : res i = 0 := by
  classical
  obtain ⟨l, hp, hpq⟩ := card_eq_ringChar_pow F
  have hp2 : 2 ≤ ringChar F := hp.two_le
  have hl : 1 ≤ l := by
    rcases Nat.eq_zero_or_pos l with h | h
    · rw [h, pow_zero] at hpq; have := carlitz_card_ge_two F; omega
    · exact h
  obtain ⟨-, -, hresv, hnc⟩ := (mem_residueSet F).mp hres
  have h0 : res ⟨0, hB⟩ = Nat.card F - 1 := residueSet_apply_zero F hB hres
  have hlt : res i < Nat.card F := hresv i
  have hdigit0 : ∀ j, j < l →
      res ⟨0, hB⟩ / (ringChar F) ^ j % (ringChar F) = (ringChar F) - 1 := by
    intro j hj
    rw [h0, hpq, Commons.Data.Nat.div_pow_pow_sub_one_mod (ringChar F) l hp2 hl j, if_pos hj]
  have hkey : ∀ j, j < l → res i / (ringChar F) ^ j % (ringChar F) = 0 := by
    intro j hj
    have hsplit : (∑ k : Fin B, res k / (ringChar F) ^ j % (ringChar F))
        = res ⟨0, hB⟩ / (ringChar F) ^ j % (ringChar F)
          + ∑ k ∈ (Finset.univ.erase (⟨0, hB⟩ : Fin B)),
              res k / (ringChar F) ^ j % (ringChar F) := by
      rw [add_comm]
      exact (Finset.sum_erase_add _ _ (Finset.mem_univ _)).symm
    have hS : (∑ k ∈ (Finset.univ.erase (⟨0, hB⟩ : Fin B)),
        res k / (ringChar F) ^ j % (ringChar F)) = 0 := by
      have := hnc j
      rw [hsplit, hdigit0 j hj] at this
      omega
    have hle' : res i / (ringChar F) ^ j % (ringChar F)
        ≤ ∑ k ∈ (Finset.univ.erase (⟨0, hB⟩ : Fin B)),
            res k / (ringChar F) ^ j % (ringChar F) :=
      Finset.single_le_sum (f := fun k => res k / (ringChar F) ^ j % (ringChar F))
        (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
    rw [hS] at hle'
    omega
  have hdvdq : Nat.card F ∣ res i := by
    rw [hpq, Nat.dvd_iff_mod_eq_zero]
    exact (Commons.Data.Nat.mod_pow_eq_zero_iff (ringChar F) l (res i) (by omega)).mpr hkey
  exact Nat.eq_zero_of_dvd_of_lt hdvdq hlt

/-- **The residue set at an index `N = q m + q - 1` is the single point `(q-1,0,…)`.** -/
theorem residueSet_eq_singleton (m B : ℕ) (hB : 0 < B) :
    residueSet F (Nat.card F * m + (Nat.card F - 1)) B = {deltaRes F (B := B)} := by
  classical
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
  · rw [mem_residueSet]
    refine ⟨by rw [deltaRes_sum F hB]; omega, ?_, ?_, deltaRes_noCarry F B hB⟩
    · refine ⟨m, ?_⟩
      have : Nat.card F * m + (Nat.card F - 1) - (Nat.card F - 1) = Nat.card F * m := by omega
      rw [deltaRes_sum F hB, this]
    · intro i
      rw [deltaRes_apply]
      split <;> omega
  · intro res hres
    funext i
    by_cases hi : i = (⟨0, hB⟩ : Fin B)
    · subst hi
      rw [deltaRes_apply_zero]
      exact residueSet_apply_zero F hB hres
    · rw [deltaRes_apply_ne F (fun h => hi (Fin.ext h))]
      exact residueSet_apply_ne_zero F hB hres hi

/-- ★★★ **The one-residue descent**: `c_{q m + q - 1} = (c_m)^q`. -/
theorem atCoeff_mul_card_add_pred (m : ℕ) :
    atCoeff F (Nat.card F * m + (Nat.card F - 1)) = (atCoeff F m) ^ (Nat.card F) := by
  classical
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hB : 0 < Nat.card F * m + (Nat.card F - 1) + 1 := by omega
  rw [atCoeff_descend F (Nat.card F * m + (Nat.card F - 1))
      (Nat.card F * m + (Nat.card F - 1) + 1) le_rfl]
  rw [residueSet_eq_singleton F m _ hB, Finset.sum_singleton]
  have hmult : ((Nat.multinomial Finset.univ (deltaRes F (B := Nat.card F * m + (Nat.card F - 1) + 1))
      : ℕ) : atQ F) = 1 := by
    rw [deltaRes_multinomial F _ hB, Nat.cast_one]
  have hprod : (∏ i : Fin (Nat.card F * m + (Nat.card F - 1) + 1),
      atE F ((i : ℕ)) ^ (deltaRes F i)) = 1 := by
    rw [Finset.prod_eq_single (⟨0, hB⟩ : Fin (Nat.card F * m + (Nat.card F - 1) + 1))]
    · simp only [deltaRes_apply_zero, atE, atGamma_zero, atD, carlitzFact_zero, map_one,
        inv_one, mul_one, one_pow]
    · intro i _ hi
      rw [deltaRes_apply_ne F (fun h => hi (Fin.ext h)), pow_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have harg : (Nat.card F * m + (Nat.card F - 1)
        - ∑ i : Fin (Nat.card F * m + (Nat.card F - 1) + 1),
            deltaRes F i * Nat.card F ^ (i : ℕ)) / Nat.card F = m := by
    rw [deltaRes_sum F hB]
    have h1 : Nat.card F * m + (Nat.card F - 1) - (Nat.card F - 1) = Nat.card F * m := by omega
    rw [h1, Nat.mul_div_cancel_left _ (by omega : 0 < Nat.card F)]
  rw [hmult, hprod, harg]
  ring

end ZagierHoffmanPositiveChar
