import Mathlib

set_option linter.unusedVariables false
set_option autoImplicit false

namespace Commons.Data.Int.Window

/-- A finite set of naturals, all `≤ t`, pairwise congruent modulo `C`, has at most
`t / C + 1` elements: the map `e ↦ e / C` is injective on it (equal quotients and equal
remainders force equality), and its image lies inside `{0, …, t / C}`. -/
private lemma card_le_div_add_one_of_pairwise_modEq (t C : ℕ) {E : Finset ℕ}
    (hE : ∀ e ∈ E, e ≤ t)
    (hmod : ∀ ⦃a : ℕ⦄, a ∈ E → ∀ ⦃b : ℕ⦄, b ∈ E → a ≡ b [MOD C]) :
    E.card ≤ t / C + 1 := by
  classical
  let Q : Finset ℕ := E.image (fun e : ℕ => e / C)
  have hQcard : Q.card = E.card := by
    dsimp [Q]
    rw [Finset.card_image_of_injOn]
    intro a ha b hb hq
    have hq' : a / C = b / C := by simpa using hq
    have hrem : a % C = b % C := hmod ha hb
    calc
      a = a / C * C + a % C := (Nat.div_add_mod' a C).symm
      _ = b / C * C + b % C := by rw [hq', hrem]
      _ = b := Nat.div_add_mod' b C
  have hQle : Q.card ≤ t / C + 1 := by
    have hsub : Q ⊆ Finset.range (t / C + 1) := by
      intro q hq
      rw [Finset.mem_range]
      rcases Finset.mem_image.mp hq with ⟨e, he, rfl⟩
      have hle : e / C ≤ t / C := Nat.div_le_div_right (hE e he)
      omega
    exact (Finset.card_le_card hsub).trans_eq (Finset.card_range (t / C + 1))
  calc
    E.card = Q.card := hQcard.symm
    _ ≤ t / C + 1 := hQle

/-- Among eight consecutive integers `n0, …, n0+7`, the number of integers congruent to a
fixed residue class modulo `D` is at most `⌊7/D⌋ + 1`. -/
theorem coset_eight_window_card_le {D : ℕ} (hD : 0 < D) (a n0 : ℤ) :
    ((Finset.Icc n0 (n0 + 7)).filter (fun m : ℤ => ((D : ℕ) : ℤ) ∣ m - a)).card ≤
      (7 : ℕ) / D + 1 := by
  classical
  let S : Finset ℤ := (Finset.Icc n0 (n0 + 7)).filter (fun m : ℤ => ((D : ℕ) : ℤ) ∣ m - a)
  let E : Finset ℕ := S.image (fun m : ℤ => (m - n0).toNat)
  have hEcard : E.card = S.card := by
    dsimp [E]
    rw [Finset.card_image_of_injOn]
    intro m1 hm1 m2 hm2 hto
    have hm1nz : 0 ≤ m1 - n0 := by
      have hlo : n0 ≤ m1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm1).1).1
      omega
    have hm2nz : 0 ≤ m2 - n0 := by
      have hlo : n0 ≤ m2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm2).1).1
      omega
    have hc1 : ((m1 - n0).toNat : ℤ) = m1 - n0 := Int.toNat_of_nonneg hm1nz
    have hc2 : ((m2 - n0).toNat : ℤ) = m2 - n0 := Int.toNat_of_nonneg hm2nz
    have hto' : ((m1 - n0).toNat : ℤ) = ((m2 - n0).toNat : ℤ) :=
      congrArg (fun n : ℕ => (n : ℤ)) hto
    have hdiff : m1 - n0 = m2 - n0 := by
      calc
        m1 - n0 = ((m1 - n0).toNat : ℤ) := hc1.symm
        _ = ((m2 - n0).toNat : ℤ) := hto'
        _ = m2 - n0 := hc2
    omega
  have hEsub : ∀ e ∈ E, e ≤ 7 := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨m, hm, rfl⟩
    rw [Int.toNat_le]
    have hmem : m ≤ n0 + 7 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
    omega
  have hmod : ∀ ⦃e1 : ℕ⦄, e1 ∈ E → ∀ ⦃e2 : ℕ⦄, e2 ∈ E → e1 ≡ e2 [MOD D] := by
    intro e1 he1 e2 he2
    rcases Finset.mem_image.mp he1 with ⟨m1, hm1, rfl⟩
    rcases Finset.mem_image.mp he2 with ⟨m2, hm2, rfl⟩
    rw [Nat.modEq_iff_dvd]
    have hm1nz : 0 ≤ m1 - n0 := by
      have hlo : n0 ≤ m1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm1).1).1
      omega
    have hm2nz : 0 ≤ m2 - n0 := by
      have hlo : n0 ≤ m2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm2).1).1
      omega
    have hc1 : ((m1 - n0).toNat : ℤ) = m1 - n0 := Int.toNat_of_nonneg hm1nz
    have hc2 : ((m2 - n0).toNat : ℤ) = m2 - n0 := Int.toNat_of_nonneg hm2nz
    rw [hc2, hc1]
    have hdv : (D : ℤ) ∣ (m2 - a) - (m1 - a) :=
      dvd_sub (Finset.mem_filter.mp hm2).2 (Finset.mem_filter.mp hm1).2
    have hsame : (m2 - n0) - (m1 - n0) = (m2 - a) - (m1 - a) := by ring
    rwa [hsame]
  have hE : E.card ≤ (7 : ℕ) / D + 1 :=
    card_le_div_add_one_of_pairwise_modEq (t := 7) (C := D) (E := E) hEsub hmod
  calc
    ((Finset.Icc n0 (n0 + 7)).filter (fun m : ℤ => ((D : ℕ) : ℤ) ∣ m - a)).card = S.card := by
      rfl
    _ = E.card := hEcard.symm
    _ ≤ (7 : ℕ) / D + 1 := hE

end Commons.Data.Int.Window
