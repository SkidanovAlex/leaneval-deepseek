import Submission.Work.Pseudo

open Finset

namespace GTTrans

variable {p : ℕ} [Fact p.Prime]

/-- The coefficient tuple of the cube form `y₀ + ω·h` (with `y₀` the extra `0`-th variable). -/
def cubeCoeff (d : ℕ) (ω : Fin d → Bool) : Fin (d + 1) → ℚ :=
  Fin.cons 1 (fun j => if ω j then 1 else 0)

/-- The coefficient tuple of the cube form `b + ω·h`. -/
def cubeCoeff0 (d : ℕ) (ω : Fin d → Bool) : Fin d → ℚ :=
  fun j => if ω j then 1 else 0

lemma qmod_one : qmod p (1 : ℚ) = 1 := by
  simp [qmod, Rat.num_one, Rat.den_one]

lemma qmod_zero : qmod p (0 : ℚ) = 0 := by
  simp [qmod, Rat.num_zero]

lemma isSmallRat_one {L₀ : ℕ} (h : 1 ≤ L₀) : IsSmallRat L₀ (1 : ℚ) := by
  refine ⟨?_, by simpa [Rat.den_one] using h⟩
  simpa [Rat.num_one] using h

lemma isSmallRat_zero {L₀ : ℕ} (h : 1 ≤ L₀) : IsSmallRat L₀ (0 : ℚ) :=
  ⟨by simp [Rat.num_zero], by simpa [Rat.den_one] using h⟩

lemma isSmallRat_cubeCoeff {d L₀ : ℕ} (h : d + 1 ≤ L₀) (ω : Fin d → Bool)
    (j : Fin (d + 1)) : IsSmallRat L₀ (cubeCoeff d ω j) := by
  rcases Fin.eq_zero_or_eq_succ j with h0 | ⟨i, rfl⟩
  · subst h0
    exact isSmallRat_one (by omega)
  · simp only [cubeCoeff, Fin.cons_succ]
    split
    · exact isSmallRat_one (by omega)
    · exact isSmallRat_zero (by omega)

lemma nonzeroTuple_cubeCoeff (d : ℕ) (ω : Fin d → Bool) : NonzeroTuple (cubeCoeff d ω) :=
  ⟨0, by simp [cubeCoeff]⟩

lemma nonzeroTuple_cubeCoeff0 {d : ℕ} {ω : Fin d → Bool} (hω : ω ≠ 0) :
    NonzeroTuple (cubeCoeff0 d ω) := by
  by_contra h
  simp only [NonzeroTuple, not_exists, not_not] at h
  apply hω
  funext i
  have hi := h i
  simp only [cubeCoeff0] at hi
  by_cases hb : ω i
  · simp [hb] at hi
  · show ω i = false
    simpa using hb

lemma notProp_cubeCoeff {d : ℕ} {ω ω' : Fin d → Bool} (h : ω ≠ ω') :
    NotProp (cubeCoeff d ω) (cubeCoeff d ω') := by
  rintro ⟨lam, hlam⟩
  have h0 := hlam 0
  simp only [cubeCoeff, Fin.cons_zero, mul_one] at h0
  have hlam1 : lam = 1 := h0.symm
  subst hlam1
  apply h
  funext j
  have hj := hlam j.succ
  simp only [cubeCoeff, Fin.cons_succ, one_mul] at hj
  cases hb : ω j <;> cases hb' : ω' j <;> simp_all

lemma linForm_cubeCoeff (d : ℕ) (ω : Fin d → Bool) (y : Fin (d + 1) → ZMod p) :
    linForm p (cubeCoeff d ω) 0 y
      = y 0 + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * y j.succ := by
  rw [linForm, add_zero, Fin.sum_univ_succ]
  have h0 : qmod p (cubeCoeff d ω 0) * y 0 = y 0 := by
    rw [show cubeCoeff d ω 0 = 1 by simp [cubeCoeff], qmod_one, one_mul]
  rw [h0]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [show cubeCoeff d ω j.succ = (if ω j then 1 else 0) by simp [cubeCoeff]]
  split <;> simp [qmod_one, qmod_zero]

/-- The linear forms condition applied to the cube forms `y ↦ y 0 + ω · h`. -/
theorem cube_lfc {d : ℕ} (hd : 1 ≤ d) (ν : ZMod p → ℝ) (ε : ℝ)
    (hLFC : LinFormsCond p ν ((d + 1) * 2 ^ d) (3 * (d + 1) - 4) (d + 1) ε)
    (A : Finset (Fin d → Bool)) (hA : A.Nonempty) :
    |((Fintype.card (Fin (d + 1) → ZMod p) : ℝ))⁻¹ *
      (∑ y : Fin (d + 1) → ZMod p,
        ∏ ω ∈ A, ν (y 0 + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * y j.succ)) - 1|
      ≤ ε := by
  have hcard1 : 1 ≤ Fintype.card {ω : Fin d → Bool // ω ∈ A} := by
    rw [Fintype.card_coe]
    have := Finset.card_pos.mpr hA
    omega
  have hcard2 : Fintype.card {ω : Fin d → Bool // ω ∈ A} ≤ (d + 1) * 2 ^ d := by
    rw [Fintype.card_coe]
    calc A.card ≤ (Finset.univ : Finset (Fin d → Bool)).card := Finset.card_le_card (by intro a _; simp)
      _ = 2 ^ d := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      _ ≤ (d + 1) * 2 ^ d := Nat.le_mul_of_pos_left _ (by omega)
  have ht1 : 1 ≤ d + 1 := by omega
  have ht2 : d + 1 ≤ 3 * (d + 1) - 4 := by omega
  have h := hLFC {ω : Fin d → Bool // ω ∈ A} hcard1 hcard2 (d + 1) ht1 ht2
    (fun i => cubeCoeff d i.1) (fun i j => isSmallRat_cubeCoeff (by omega) i.1 j)
    (fun i => nonzeroTuple_cubeCoeff d i.1)
    (fun i i' hii => notProp_cubeCoeff (fun hc => hii (Subtype.ext hc)))
    (fun _ => 0)
  simp only [linForm_cubeCoeff] at h
  have hsum : (∑ y : Fin (d + 1) → ZMod p,
        ∏ ω ∈ A, ν (y 0 + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * y j.succ))
      = ∑ y : Fin (d + 1) → ZMod p,
        ∏ i : {ω : Fin d → Bool // ω ∈ A},
          ν (y 0 + ∑ j : Fin d, (if (i : Fin d → Bool) j then (1 : ZMod p) else 0) * y j.succ) := by
    apply Finset.sum_congr rfl
    intro y _
    exact (Finset.prod_attach A
      (fun ω => ν (y 0 + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * y j.succ))).symm
  rw [hsum]
  exact h

/-- The cube linear forms condition, in the `(z,h)` coordinates used by `mua`. -/
theorem cube_lfc' {d : ℕ} (hd : 1 ≤ d) (ν : ZMod p → ℝ) (ε : ℝ)
    (hLFC : LinFormsCond p ν ((d + 1) * 2 ^ d) (3 * (d + 1) - 4) (d + 1) ε)
    (A : Finset (Fin d → Bool)) (hA : A.Nonempty) :
    |((Fintype.card (ZMod p) : ℝ) ^ (d + 1))⁻¹ *
      (∑ z : ZMod p, ∑ h : Fin d → ZMod p,
        ∏ ω ∈ A, ν (z + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j)) - 1| ≤ ε := by
  have h := cube_lfc hd ν ε hLFC A hA
  have hcardR : ((Fintype.card (Fin (d + 1) → ZMod p) : ℝ))
      = (Fintype.card (ZMod p) : ℝ) ^ (d + 1) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  have hsum : (∑ z : ZMod p, ∑ h : Fin d → ZMod p,
        ∏ ω ∈ A, ν (z + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j))
      = ∑ y : Fin (d + 1) → ZMod p,
        ∏ ω ∈ A, ν (y 0 + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * y j.succ) := by
    rw [← Fintype.sum_prod_type (α₁ := ZMod p) (α₂ := Fin d → ZMod p)
      (f := fun q : ZMod p × (Fin d → ZMod p) =>
        ∏ ω ∈ A, ν (q.1 + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * q.2 j)),
      ← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (d + 1) => ZMod p))
        (fun y : Fin (d + 1) → ZMod p =>
          ∏ ω ∈ A, ν (y 0 + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * y j.succ))]
    refine Finset.sum_congr rfl fun q _ => Finset.prod_congr rfl fun ω _ => ?_
    rw [show Fin.consEquiv (fun _ : Fin (d + 1) => ZMod p) q = Fin.cons q.1 q.2 from rfl]
    simp only [Fin.cons_zero, Fin.cons_succ]
  rw [hsum, ← hcardR]
  exact h

lemma isSmallRat_cubeCoeff0 {d L₀ : ℕ} (h : 1 ≤ L₀) (ω : Fin d → Bool) (j : Fin d) :
    IsSmallRat L₀ (cubeCoeff0 d ω j) := by
  simp only [cubeCoeff0]
  split
  · exact isSmallRat_one h
  · exact isSmallRat_zero h

lemma linForm_cubeCoeff0 (d : ℕ) (ω : Fin d → Bool) (b : ZMod p) (h : Fin d → ZMod p) :
    linForm p (cubeCoeff0 d ω) b h
      = b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j := by
  rw [linForm, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [cubeCoeff0]
  split <;> simp [qmod_one, qmod_zero]

lemma cubeCoeff0_inj {d : ℕ} {ω ω' : Fin d → Bool}
    (h : ∀ j, cubeCoeff0 d ω j = cubeCoeff0 d ω' j) : ω = ω' := by
  funext j
  have hj := h j
  simp only [cubeCoeff0] at hj
  by_cases hb : ω j <;> by_cases hb' : ω' j <;> simp_all

lemma eq_zero_of_cubeCoeff0_eq_zero {d : ℕ} {ω : Fin d → Bool}
    (h : ∀ j, cubeCoeff0 d ω j = 0) : ω = 0 := by
  by_contra hω
  obtain ⟨j, hj⟩ := nonzeroTuple_cubeCoeff0 hω
  exact hj (h j)

lemma cubeCoeff0_eq_zero_or_one (d : ℕ) (ω : Fin d → Bool) (j : Fin d) :
    cubeCoeff0 d ω j = 0 ∨ cubeCoeff0 d ω j = 1 := by
  simp only [cubeCoeff0]; split <;> simp

lemma notProp_cubeCoeff0 {d : ℕ} {ω ω' : Fin d → Bool} (hω : ω ≠ 0) (hω' : ω' ≠ 0)
    (h : ω ≠ ω') : NotProp (cubeCoeff0 d ω) (cubeCoeff0 d ω') := by
  rintro ⟨lam, hlam⟩
  obtain ⟨j0, hj0⟩ := nonzeroTuple_cubeCoeff0 hω
  have hone : cubeCoeff0 d ω j0 = 1 := by
    rcases cubeCoeff0_eq_zero_or_one d ω j0 with hh | hh
    · exact absurd hh hj0
    · exact hh
  have hval : lam = cubeCoeff0 d ω' j0 := by
    have := hlam j0
    rw [hone, mul_one] at this
    exact this.symm
  rcases cubeCoeff0_eq_zero_or_one d ω' j0 with h0 | h1
  · apply hω'
    have hz : ∀ j, cubeCoeff0 d ω' j = 0 := fun j => by
      have := hlam j
      rw [hval, h0, zero_mul] at this
      exact this
    exact eq_zero_of_cubeCoeff0_eq_zero hz
  · apply h
    apply cubeCoeff0_inj
    intro j
    have := hlam j
    rw [hval, h1, one_mul] at this
    exact this.symm


/-- The linear forms condition applied to the cube forms `h ↦ b + ω · h` (fixed shift `b`). -/
theorem cube_lfc_fixed {d : ℕ} (hd : 1 ≤ d) (ν : ZMod p → ℝ) (ε : ℝ)
    (hLFC : LinFormsCond p ν (d * 2 ^ d) (3 * (d + 1) - 4) (d + 1) ε)
    (A : Finset (Fin d → Bool)) (hA : A.Nonempty) (h0 : (0 : Fin d → Bool) ∉ A)
    (b : ZMod p) :
    |((Fintype.card (Fin d → ZMod p) : ℝ))⁻¹ *
      (∑ h : Fin d → ZMod p,
        ∏ ω ∈ A, ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j)) - 1|
      ≤ ε := by
  have hcard1 : 1 ≤ Fintype.card {ω : Fin d → Bool // ω ∈ A} := by
    rw [Fintype.card_coe]
    have := Finset.card_pos.mpr hA
    omega
  have hcard2 : Fintype.card {ω : Fin d → Bool // ω ∈ A} ≤ d * 2 ^ d := by
    rw [Fintype.card_coe]
    calc A.card ≤ (Finset.univ : Finset (Fin d → Bool)).card := Finset.card_le_card (by intro a _; simp)
      _ = 2 ^ d := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      _ ≤ d * 2 ^ d := Nat.le_mul_of_pos_left _ (by omega)
  have ht1 : 1 ≤ d := hd
  have ht2 : d ≤ 3 * (d + 1) - 4 := by omega
  have h := hLFC {ω : Fin d → Bool // ω ∈ A} hcard1 hcard2 d ht1 ht2
    (fun i => cubeCoeff0 d i.1) (fun i j => isSmallRat_cubeCoeff0 (by omega) i.1 j)
    (fun i => nonzeroTuple_cubeCoeff0 (fun hc => h0 (hc ▸ i.2)))
    (fun i i' hii => notProp_cubeCoeff0 (fun hc => h0 (hc ▸ i.2)) (fun hc => h0 (hc ▸ i'.2))
      (fun hc => hii (Subtype.ext hc)))
    (fun _ => b)
  simp only [linForm_cubeCoeff0] at h
  have hsum : (∑ h : Fin d → ZMod p,
        ∏ ω ∈ A, ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j))
      = ∑ h : Fin d → ZMod p,
        ∏ i : {ω : Fin d → Bool // ω ∈ A},
          ν (b + ∑ j : Fin d, (if (i : Fin d → Bool) j then (1 : ZMod p) else 0) * h j) := by
    apply Finset.sum_congr rfl
    intro hh _
    exact (Finset.prod_attach A
      (fun ω => ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * hh j))).symm
  rw [hsum]
  exact h

/-- GT's `(dual-bounded)`: `𝔼_h ∏_{ω ≠ 0} (ν(x + ω·h) + 1) ≤ 2^{2^d−1}(1 + ε)`. -/
theorem cube_prod_add_one_le {d : ℕ} (hd : 1 ≤ d) (ν : ZMod p → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hLFC : LinFormsCond p ν (d * 2 ^ d) (3 * (d + 1) - 4) (d + 1) ε) (b : ZMod p) :
    ((Fintype.card (Fin d → ZMod p) : ℝ))⁻¹ *
      (∑ h : Fin d → ZMod p,
        ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
          (ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j) + 1))
      ≤ (2 : ℝ) ^ (2 ^ d - 1) * (1 + ε) := by
  set s : Finset (Fin d → Bool) := Finset.univ.erase 0 with hs
  have hcard : s.card = 2 ^ d - 1 := by
    rw [hs, Finset.card_erase_of_mem (by simp), Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool]
  have hpos : (0 : ℝ) < (Fintype.card (Fin d → ZMod p) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨fun _ => 0⟩
  have hterm : ∀ t ∈ s.powerset, ((Fintype.card (Fin d → ZMod p) : ℝ))⁻¹ *
      (∑ h : Fin d → ZMod p,
        ∏ ω ∈ t, ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j))
        ≤ 1 + ε := by
    intro t ht
    rw [Finset.mem_powerset] at ht
    rcases t.eq_empty_or_nonempty with rfl | hne
    · simp only [Finset.prod_empty, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
      have hX : (0 : ℝ) < ((Fintype.card (ZMod p) ^ d : ℕ) : ℝ) := by
        have h1 : (0 : ℕ) < Fintype.card (ZMod p) ^ d :=
          pow_pos (Fintype.card_pos_iff.mpr ⟨(0 : ZMod p)⟩) d
        exact_mod_cast h1
      rw [inv_mul_cancel₀ (ne_of_gt hX)]
      linarith
    · have h0t : (0 : Fin d → Bool) ∉ t := fun hmem => by
        have := ht hmem
        rw [hs, Finset.mem_erase] at this
        exact this.1 rfl
      have hcf := cube_lfc_fixed hd ν ε hLFC t hne h0t b
      rw [abs_le] at hcf
      linarith [hcf.2]
  have hexp : ∀ h : Fin d → ZMod p,
      ∏ ω ∈ s, (ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j) + 1)
      = ∑ t ∈ s.powerset,
          ∏ ω ∈ t, ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j) := by
    intro h
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.prod_const_one, mul_one]
  have hexp' : (∑ h : Fin d → ZMod p,
        ∏ ω ∈ s, (ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j) + 1))
      = ∑ h : Fin d → ZMod p, ∑ t ∈ s.powerset,
          ∏ ω ∈ t, ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j) :=
    Finset.sum_congr rfl fun h _ => hexp h
  rw [hexp', Finset.sum_comm, Finset.mul_sum]
  calc ∑ t ∈ s.powerset, ((Fintype.card (Fin d → ZMod p) : ℝ))⁻¹ *
        (∑ h : Fin d → ZMod p,
          ∏ ω ∈ t, ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j))
      ≤ ∑ _t ∈ s.powerset, (1 + ε) := Finset.sum_le_sum hterm
    _ = 2 ^ (2 ^ d - 1) * (1 + ε) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset, hcard]
        push_cast
        ring

/-- GT (dual-bounded): every basic Gowers anti-uniform function is bounded. -/
theorem dualFunc_bound {d : ℕ} (hd : 1 ≤ d) (ν : ZMod p → ℝ) (hν : ∀ x, 0 ≤ ν x) (ε : ℝ)
    (hε : 0 ≤ ε) (hLFC : LinFormsCond p ν (d * 2 ^ d) (3 * (d + 1) - 4) (d + 1) ε)
    (F : ZMod p → ℝ) (hF : ∀ x, |F x| ≤ ν x + 1) (b : ZMod p) :
    |((Fintype.card (Fin d → ZMod p) : ℝ))⁻¹ *
      (∑ h : Fin d → ZMod p,
        ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
          F (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j))|
      ≤ (2 : ℝ) ^ (2 ^ d - 1) * (1 + ε) := by
  have hpos : (0 : ℝ) < (Fintype.card (Fin d → ZMod p) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨fun _ => 0⟩
  have hbound := cube_prod_add_one_le hd ν ε hε hLFC b
  refine le_trans ?_ hbound
  rw [abs_mul, abs_of_pos (inv_pos.mpr hpos)]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (inv_pos.mpr hpos))
  calc |∑ h : Fin d → ZMod p,
        ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
          F (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j)|
      ≤ ∑ h : Fin d → ZMod p,
        |∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
          F (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ h : Fin d → ZMod p,
        ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
          |F (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j)| := by
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Finset.abs_prod]
    _ ≤ ∑ h : Fin d → ZMod p,
        ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
          (ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j) + 1) := by
        refine Finset.sum_le_sum fun h _ => Finset.prod_le_prod ?_ ?_
        · intro ω _; exact abs_nonneg _
        · intro ω _; exact hF _

end GTTrans
