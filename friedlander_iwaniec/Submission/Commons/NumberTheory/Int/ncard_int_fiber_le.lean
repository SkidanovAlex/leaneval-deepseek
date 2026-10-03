import Mathlib
import Submission.Commons.NumberTheory.Int.ncard_int_residue_class_sq_le

namespace Commons.NumberTheory.Int

/-- The integers `a` with `a^2 ≤ M` are finite (they lie in `[-⌊√M⌋, ⌊√M⌋]`). -/
private lemma finite_int_sq_le (M : ℝ) : ({a : ℤ | (a : ℝ) ^ 2 ≤ M}).Finite := by
  refine Set.Finite.subset (Finset.finite_toSet (Finset.Icc (-⌊Real.sqrt M⌋) ⌊Real.sqrt M⌋)) ?_
  intro a ha
  rw [Finset.mem_coe, Finset.mem_Icc]
  have h1 : Real.sqrt ((a : ℝ) ^ 2) ≤ Real.sqrt M := Real.sqrt_le_sqrt ha
  rw [Real.sqrt_sq_eq_abs] at h1
  have h2 : ((|a| : ℤ) : ℝ) ≤ Real.sqrt M := by rw [Int.cast_abs]; exact h1
  have h3 : |a| ≤ ⌊Real.sqrt M⌋ := Int.le_floor.mpr h2
  exact abs_le.mp h3

theorem ncard_int_fiber_le {d x : ℕ} (hd : 1 ≤ d) (b : ℤ) :
    (({a : ℤ | a ^ 2 + b ^ 4 ≤ (x : ℤ) ∧ (d : ℤ) ∣ (a ^ 2 + b ^ 4)}.ncard : ℝ) ≤
      (((Finset.range d).filter (fun r : ℕ => (d : ℤ) ∣ ((r : ℤ) ^ 2 + b ^ 4))).card : ℝ)
        * (2 * Real.sqrt ((x : ℝ) - (b : ℝ) ^ 4) / (d : ℝ) + 1)) := by
  classical
  set M : ℝ := (x : ℝ) - (b : ℝ) ^ 4 with hMdef
  set S : Set ℤ := {a : ℤ | a ^ 2 + b ^ 4 ≤ (x : ℤ) ∧ (d : ℤ) ∣ (a ^ 2 + b ^ 4)} with hSdef
  set R : Finset ℕ :=
    (Finset.range d).filter (fun r : ℕ => (d : ℤ) ∣ ((r : ℤ) ^ 2 + b ^ 4)) with hRdef
  change (S.ncard : ℝ) ≤ (R.card : ℝ) * (2 * Real.sqrt M / (d : ℝ) + 1)
  have hsq_of_mem : ∀ a ∈ S, (a : ℝ) ^ 2 ≤ M := by
    intro a ha
    obtain ⟨hle, _⟩ := ha
    have hcast : ((a ^ 2 + b ^ 4 : ℤ) : ℝ) ≤ ((x : ℤ) : ℝ) := by exact_mod_cast hle
    push_cast at hcast
    rw [hMdef]; linarith
  have hSfin : S.Finite :=
    Set.Finite.subset (finite_int_sq_le M) (fun a ha => hsq_of_mem a ha)
  let Sf : Finset ℤ := hSfin.toFinset
  let T : ℕ → Finset ℤ := fun r => Sf.filter (fun a : ℤ => a ≡ (r : ℤ) [ZMOD (d : ℤ)])
  have hmemS : ∀ {a : ℤ}, a ∈ Sf → a ∈ S := by
    intro a ha
    exact (Set.Finite.mem_toFinset hSfin).mp ha
  have hcover : Sf ⊆ R.biUnion T := by
    intro a ha
    have haS : a ∈ S := hmemS ha
    obtain ⟨hle, hdvd⟩ := haS
    set ra : ℕ := (a % (d : ℤ)).toNat with hradef
    have hdZ : (d : ℤ) ≠ 0 := by omega
    have hra_nonneg : 0 ≤ a % (d : ℤ) := Int.emod_nonneg a hdZ
    have hra_cast : (ra : ℤ) = a % (d : ℤ) := Int.toNat_of_nonneg hra_nonneg
    have hra_lt : ra < d := by
      have hh : a % (d : ℤ) < (d : ℤ) := Int.emod_lt_of_pos a (by omega)
      rw [← hra_cast] at hh
      exact_mod_cast hh
    have hcong : a ≡ (ra : ℤ) [ZMOD (d : ℤ)] := by
      have h1 : a % (d : ℤ) ≡ a [ZMOD (d : ℤ)] := Int.mod_modEq a (d : ℤ)
      have h2 : a ≡ a % (d : ℤ) [ZMOD (d : ℤ)] := h1.symm
      rwa [← hra_cast] at h2
    have hdvd_ra : (d : ℤ) ∣ (ra : ℤ) ^ 2 + b ^ 4 := by
      have hsq : a ^ 2 ≡ (ra : ℤ) ^ 2 [ZMOD (d : ℤ)] := hcong.pow 2
      have hadd : a ^ 2 + b ^ 4 ≡ (ra : ℤ) ^ 2 + b ^ 4 [ZMOD (d : ℤ)] :=
        hsq.add (Int.ModEq.refl (b ^ 4))
      have h0 : a ^ 2 + b ^ 4 ≡ 0 [ZMOD (d : ℤ)] := Int.modEq_zero_iff_dvd.mpr hdvd
      exact Int.modEq_zero_iff_dvd.mp (hadd.symm.trans h0)
    rw [Finset.mem_biUnion]
    exact ⟨ra, by rw [Finset.mem_filter]; exact ⟨Finset.mem_range.mpr hra_lt, hdvd_ra⟩,
      by rw [Finset.mem_filter]; exact ⟨ha, hcong⟩⟩
  have hcard1 : (Sf.card : ℝ) ≤ ((R.biUnion T).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hcover
  have hcard2 : ((R.biUnion T).card : ℝ) ≤ ∑ r ∈ R, ((T r).card : ℝ) := by
    have hb : (R.biUnion T).card ≤ ∑ r ∈ R, (T r).card := Finset.card_biUnion_le
    have hcast : ((∑ r ∈ R, (T r).card : ℕ) : ℝ) = ∑ r ∈ R, ((T r).card : ℝ) := by
      push_cast; rfl
    calc ((R.biUnion T).card : ℝ) ≤ ((∑ r ∈ R, (T r).card : ℕ) : ℝ) := by exact_mod_cast hb
      _ = ∑ r ∈ R, ((T r).card : ℝ) := hcast
  have hTle : ∀ r ∈ R, ((T r).card : ℝ) ≤ 2 * Real.sqrt M / (d : ℝ) + 1 := by
    intro r _
    have hsub : (↑(T r) : Set ℤ)
        ⊆ {a : ℤ | a ≡ (r : ℤ) [ZMOD (d : ℤ)] ∧ (a : ℝ) ^ 2 ≤ M} := by
      intro a ha
      rw [Finset.mem_coe, Finset.mem_filter] at ha
      exact ⟨ha.2, hsq_of_mem a (hmemS ha.1)⟩
    have hfin : ({a : ℤ | a ≡ (r : ℤ) [ZMOD (d : ℤ)] ∧ (a : ℝ) ^ 2 ≤ M}).Finite :=
      Set.Finite.subset (finite_int_sq_le M) (fun a ha => ha.2)
    have hle' : ((T r).card : ℝ)
        ≤ (({a : ℤ | a ≡ (r : ℤ) [ZMOD (d : ℤ)] ∧ (a : ℝ) ^ 2 ≤ M}).ncard : ℝ) := by
      have := Set.ncard_le_ncard hsub hfin
      rw [Set.ncard_coe_finset] at this
      exact_mod_cast this
    have hb := ncard_int_residue_class_sq_le (d := d) hd (r : ℤ) M
    linarith [hle', hb]
  have hsum : ∑ r ∈ R, ((T r).card : ℝ) ≤ ∑ r ∈ R, (2 * Real.sqrt M / (d : ℝ) + 1) :=
    Finset.sum_le_sum (fun r hr => hTle r hr)
  have hconst : ∑ r ∈ R, (2 * Real.sqrt M / (d : ℝ) + 1)
      = (R.card : ℝ) * (2 * Real.sqrt M / (d : ℝ) + 1) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [Set.ncard_eq_toFinset_card S hSfin]
  calc (Sf.card : ℝ) ≤ ((R.biUnion T).card : ℝ) := hcard1
    _ ≤ ∑ r ∈ R, ((T r).card : ℝ) := hcard2
    _ ≤ ∑ r ∈ R, (2 * Real.sqrt M / (d : ℝ) + 1) := hsum
    _ = (R.card : ℝ) * (2 * Real.sqrt M / (d : ℝ) + 1) := hconst

end Commons.NumberTheory.Int
