import Mathlib
import Submission.Work.TMC16Core.Basic.nnDist

namespace Work.TMC16Core.Trig

open Work.TMC16Core.Basic

set_option linter.unusedVariables false

/-- **Number-theoretic crux.** For `0 < q` and `Nat.Coprime p.natAbs q`, the map
`k ↦ ((k : ℤ) * p) % q` is a bijection from `{1,…,q}` onto `{0,…,q-1}`; in
particular every residue `j < q` has a preimage in `{1,…,q}`. -/
lemma emod_mul_surj {q : ℕ} (hq : 0 < q) {p : ℤ} (hcop : Nat.Coprime p.natAbs q) :
    ∀ j : ℕ, j < q → ∃ k : ℕ, 1 ≤ k ∧ k ≤ q ∧ ((k : ℤ) * p) % (q : ℤ) = (j : ℤ) := by
  intro j hj
  have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hne : (q : ℤ) ≠ 0 := hqZ.ne'
  set f : ℕ → ℤ := fun k => ((k : ℤ) * p) % (q : ℤ) with hf
  have hinj : Set.InjOn f ↑(Finset.Icc 1 q) := by
    intro k hk k' hk' heq
    rw [Finset.mem_coe, Finset.mem_Icc] at hk hk'
    rw [hf] at heq
    have hmod : ((k : ℤ) * p) ≡ ((k' : ℤ) * p) [ZMOD (q : ℤ)] := heq
    have hdv : (q : ℤ) ∣ ((k' : ℤ) - (k : ℤ)) * p := by
      have h := Int.ModEq.dvd hmod
      convert h using 1
      ring
    have hnat : q ∣ (((k' : ℤ) - (k : ℤ)).natAbs * p.natAbs) := by
      have h := (Int.natAbs_dvd_natAbs (a := (q : ℤ))
        (b := ((k' : ℤ) - (k : ℤ)) * p)).mpr hdv
      simpa [Int.natAbs_mul] using h
    have hnat2 : q ∣ ((k' : ℤ) - (k : ℤ)).natAbs := hcop.symm.dvd_of_dvd_mul_right hnat
    have hbound : ((k' : ℤ) - (k : ℤ)).natAbs < q := by
      rcases le_total k k' with h | h
      · have h1 : (k' : ℤ) - (k : ℤ) = ((k' - k : ℕ) : ℤ) := by omega
        rw [h1, Int.natAbs_natCast]
        omega
      · have h1 : (k' : ℤ) - (k : ℤ) = -((k - k' : ℕ) : ℤ) := by omega
        rw [h1, Int.natAbs_neg, Int.natAbs_natCast]
        omega
    have hzero : ((k' : ℤ) - (k : ℤ)).natAbs = 0 := Nat.eq_zero_of_dvd_of_lt hnat2 hbound
    have hz : (k' : ℤ) - (k : ℤ) = 0 := Int.natAbs_eq_zero.mp hzero
    omega
  have hmem : ∀ k ∈ Finset.Icc 1 q,
      f k ∈ (Finset.Ico 0 q).image (fun j : ℕ => (j : ℤ)) := by
    intro k _
    have h0 : 0 ≤ f k := by rw [hf]; exact Int.emod_nonneg _ hne
    have hlt : f k < (q : ℤ) := by rw [hf]; exact Int.emod_lt_of_pos _ hqZ
    have hcast : ((f k).toNat : ℤ) = f k := Int.toNat_of_nonneg h0
    have hltn : (f k).toNat < q := by
      have : ((f k).toNat : ℤ) < (q : ℤ) := by rw [hcast]; exact hlt
      exact_mod_cast this
    exact Finset.mem_image.mpr
      ⟨(f k).toNat, by simp only [Finset.mem_Ico]; exact ⟨Nat.zero_le _, hltn⟩, hcast⟩
  have hsub : (Finset.Icc 1 q).image f ⊆ (Finset.Ico 0 q).image (fun j : ℕ => (j : ℤ)) := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    exact hmem k hk
  have hcard1 : ((Finset.Icc 1 q).image f).card = q := by
    rw [Finset.card_image_of_injOn hinj, Nat.card_Icc]
    omega
  have hcard2 : ((Finset.Ico 0 q).image (fun j : ℕ => (j : ℤ))).card = q := by
    rw [Finset.card_image_of_injOn (f := fun j : ℕ => (j : ℤ)) (s := Finset.Ico 0 q)
      (fun _ _ _ _ hab => Nat.cast_injective hab), Nat.card_Ico]
    omega
  have hset : (Finset.Icc 1 q).image f = (Finset.Ico 0 q).image (fun j : ℕ => (j : ℤ)) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard2, hcard1])
  have hjmem : (j : ℤ) ∈ (Finset.Ico 0 q).image (fun j : ℕ => (j : ℤ)) := by
    refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
    simp only [Finset.mem_Ico]
    exact ⟨Nat.zero_le j, hj⟩
  rw [← hset] at hjmem
  obtain ⟨k, hkIcc, hkf⟩ := Finset.mem_image.mp hjmem
  rw [hf] at hkf
  exact ⟨k, (Finset.mem_Icc.mp hkIcc).1, (Finset.mem_Icc.mp hkIcc).2, hkf⟩

/-- Periodicity: `k·(p/q)` and `((k·p) mod q)/q` differ by an integer, so the two
`nn`-values coincide. -/
lemma nn_mul_div_emod' {q : ℕ} (hq : 0 < q) (p : ℤ) (x : ℝ) (k : ℕ) :
    nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) =
      nn (2 * x + ((((k : ℤ) * p) % q).toNat : ℝ) / (q : ℝ)) := by
  have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqRne : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have hnonneg : 0 ≤ ((k : ℤ) * p) % (q : ℤ) := Int.emod_nonneg _ hqZ.ne'
  have htoNat : ((((k : ℤ) * p) % (q : ℤ) : ℤ) : ℝ) = ((((k : ℤ) * p) % (q : ℤ)).toNat : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hnonneg).symm
  have hkeq : (k : ℝ) * ((p : ℝ) / (q : ℝ)) = (((k : ℤ) * p : ℤ) : ℝ) / (q : ℝ) := by
    push_cast
    ring
  have hmain : 2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))
      = (2 * x + ((((k : ℤ) * p) % (q : ℤ) : ℤ) : ℝ) / (q : ℝ))
        + ((((k : ℤ) * p) / (q : ℤ) : ℤ) : ℝ) := by
    have hAcast : (((k : ℤ) * p : ℤ) : ℝ)
        = ((((k : ℤ) * p) / (q : ℤ) : ℤ) : ℝ) * (q : ℝ)
          + ((((k : ℤ) * p) % (q : ℤ) : ℤ) : ℝ) := by
      have h := Int.ediv_mul_add_emod ((k : ℤ) * p) (q : ℤ)
      exact_mod_cast h.symm
    rw [hkeq, hAcast]
    field_simp
    ring
  rw [hmain, htoNat, nn_add_intCast]

theorem nn_grid_min_transfer {q : ℕ} (hq : 0 < q) {p : ℤ} (hcop : Nat.Coprime p.natAbs q) (x : ℝ)
    {k₁ : ℕ} (hk₁ : k₁ ∈ Finset.Icc 1 q)
    (hmin : ∀ k ∈ Finset.Icc 1 q,
      Work.TMC16Core.Basic.nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) ≥
        Work.TMC16Core.Basic.nn (2 * x + (k₁ : ℝ) * ((p : ℝ) / (q : ℝ)))) :
    ∀ j < q, Work.TMC16Core.Basic.nn (2 * x + (j : ℝ) / (q : ℝ)) ≥
      Work.TMC16Core.Basic.nn (2 * x + ((((k₁ : ℤ) * p) % q).toNat : ℝ) / (q : ℝ)) := by
  intro j hj
  have hk1 := nn_mul_div_emod' hq p x k₁
  rw [← hk1]
  obtain ⟨k, hk1le, hkq, hkeq⟩ := emod_mul_surj hq hcop j hj
  have hk_mem : k ∈ Finset.Icc 1 q := Finset.mem_Icc.mpr ⟨hk1le, hkq⟩
  have hk2 : ((((k : ℤ) * p) % q).toNat : ℝ) = (j : ℝ) := by
    rw [hkeq]
    simp
  have hL : Work.TMC16Core.Basic.nn (2 * x + (j : ℝ) / (q : ℝ))
      = Work.TMC16Core.Basic.nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) := by
    rw [nn_mul_div_emod' hq p x k, hk2]
  rw [hL]
  exact hmin k hk_mem

end Work.TMC16Core.Trig
