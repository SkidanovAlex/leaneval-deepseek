import Mathlib
import Submission.Work.ORFinal.TorsionData.Defs

namespace Work.ORFinal.TorsionData

open Work.ORLinnell

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Nontrivial U]
  [Algebra K U]

noncomputable section

/-! ## Right fractions over a subring

We isolate the ring-theoretic core of the common denominator statement.  For a subring
`R ≤ U` we say that `x : U` *has a right denominator in `R`* if `x * t ∈ R` for some nonzero
`t ∈ R`.  Assuming the right Ore condition on `R` and that nonzero elements of `R` are units of
`U` (so that `R` has no zero divisors), the elements having a right denominator form a
division-closed subring of `U`, and finitely many of them have a *common* right denominator. -/

/-- `x : U` has a right denominator in the subring `R ≤ U`: some nonzero `t ∈ R` with
`x * t ∈ R`. -/
def IsRightFrac (R : Subring U) (x : U) : Prop := ∃ t ∈ R, t ≠ 0 ∧ x * t ∈ R

/-- The right Ore condition on a subring `R ≤ U`. -/
def IsRightOre (R : Subring U) : Prop :=
  ∀ a ∈ R, a ≠ 0 → ∀ b ∈ R, b ≠ 0 →
    ∃ c ∈ R, c ≠ 0 ∧ ∃ d ∈ R, d ≠ 0 ∧ a * c = b * d

theorem IsRightFrac.zero (R : Subring U) : IsRightFrac R 0 :=
  ⟨1, R.one_mem, one_ne_zero, by rw [zero_mul]; exact R.zero_mem⟩

theorem IsRightFrac.one (R : Subring U) : IsRightFrac R 1 :=
  ⟨1, R.one_mem, one_ne_zero, by rw [one_mul]; exact R.one_mem⟩

omit [Nontrivial U] in
theorem IsRightFrac.neg {R : Subring U} {x : U} (h : IsRightFrac R x) :
    IsRightFrac R (-x) := by
  obtain ⟨t, htR, hne, hxt⟩ := h
  exact ⟨t, htR, hne, by rw [neg_mul]; exact R.neg_mem hxt⟩

theorem IsRightFrac.add {R : Subring U} (hOre : IsRightOre R)
    (hUnit : ∀ t ∈ R, t ≠ 0 → IsUnit t) {x y : U}
    (hx : IsRightFrac R x) (hy : IsRightFrac R y) : IsRightFrac R (x + y) := by
  obtain ⟨s, hsR, hsne, hxs⟩ := hx
  obtain ⟨t, htR, htne, hyt⟩ := hy
  obtain ⟨c, hcR, hcne, d, hdR, hdne, hcd⟩ := hOre s hsR hsne t htR htne
  refine ⟨s * c, R.mul_mem hsR hcR, ((hUnit s hsR hsne).mul (hUnit c hcR hcne)).ne_zero, ?_⟩
  rw [add_mul]
  exact R.add_mem (by rw [← mul_assoc x s c]; exact R.mul_mem hxs hcR)
    (by rw [hcd, ← mul_assoc y t d]; exact R.mul_mem hyt hdR)

theorem IsRightFrac.mul {R : Subring U} (hOre : IsRightOre R)
    (hUnit : ∀ t ∈ R, t ≠ 0 → IsUnit t) {x y : U}
    (hx : IsRightFrac R x) (hy : IsRightFrac R y) : IsRightFrac R (x * y) := by
  rcases eq_or_ne y 0 with rfl | hyne
  · rw [mul_zero]; exact IsRightFrac.zero R
  obtain ⟨s, hsR, hsne, hxs⟩ := hx
  obtain ⟨t, htR, htne, hyt⟩ := hy
  have hytne : y * t ≠ 0 := by
    intro h0
    exact hyne ((hUnit t htR htne).mul_right_cancel (by rw [h0, zero_mul]))
  obtain ⟨c, hcR, hcne, d, hdR, hdne, hcd⟩ := hOre s hsR hsne (y * t) hyt hytne
  refine ⟨t * d, R.mul_mem htR hdR, ((hUnit t htR htne).mul (hUnit d hdR hdne)).ne_zero, ?_⟩
  rw [mul_assoc x y (t * d), ← mul_assoc y t d, ← hcd, ← mul_assoc x s c]
  exact R.mul_mem hxs hcR

/-- Finitely many elements with a right denominator have a **common** right denominator, by the
right Ore condition. -/
theorem exists_common_denom_finset {R : Subring U} (hOre : IsRightOre R)
    (hUnit : ∀ t ∈ R, t ≠ 0 → IsUnit t) {ι : Type*} [DecidableEq ι] :
    ∀ s : Finset ι, ∀ x : ι → U, (∀ i ∈ s, IsRightFrac R (x i)) →
      ∃ t ∈ R, t ≠ 0 ∧ ∀ i ∈ s, x i * t ∈ R := by
  intro s
  refine Finset.induction_on s ?_ ?_
  · intro x _
    exact ⟨1, R.one_mem, one_ne_zero, by intro i hi; simp at hi⟩
  · intro a s _ ih x h
    have h1 : ∀ i ∈ s, IsRightFrac R (x i) := fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨t, htR, htne, ht⟩ := ih x h1
    obtain ⟨ta, htaR, htane, hta⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨c, hcR, hcne, d, hdR, hdne, hcd⟩ := hOre t htR htne ta htaR htane
    refine ⟨t * c, R.mul_mem htR hcR, ((hUnit t htR htne).mul (hUnit c hcR hcne)).ne_zero, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · rw [hcd, ← mul_assoc (x i) ta d]; exact R.mul_mem hta hdR
    · rw [← mul_assoc (x i) t c]; exact R.mul_mem (ht i hi') hcR

/-! ## Units of the division closure -/

/-- A nonzero element of `L.D H` is a unit of `U` (via the division ring structure of `L.D H`). -/
theorem isUnit_of_mem_D (L : LinnellDatum K G U) {H : Subgroup G}
    (hdivH : ∀ x : ↥(L.D H), x ≠ 0 → IsUnit x) {t : U} (ht : t ∈ L.D H) (hne : t ≠ 0) :
    IsUnit t :=
  (isUnit_of_mem_D_of_le L le_rfl hdivH ht hne).map (Subring.subtype (L.D H))

/-- If `x * t ∈ L.D H` with `t ∈ L.D H` nonzero, then `x ∈ L.D H`: the inverse of `t` lies in
`L.D H` because `L.D H` is division closed. -/
theorem mem_D_of_mul_mem_D (L : LinnellDatum K G U) {H : Subgroup G}
    (hdivH : ∀ x : ↥(L.D H), x ≠ 0 → IsUnit x) {x t : U}
    (ht : t ∈ L.D H) (htne : t ≠ 0) (hxt : x * t ∈ L.D H) : x ∈ L.D H := by
  obtain ⟨u, hu⟩ := isUnit_of_mem_D L hdivH ht htne
  have hinv : (↑(u⁻¹) : U) ∈ L.D H :=
    L.isDivisionClosed H t ht (↑(u⁻¹)) (by rw [← hu, Units.mul_inv])
  have hxeq : x = (x * t) * ↑(u⁻¹) := by rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  rw [hxeq]
  exact (L.D H).mul_mem hxt hinv

/-- A nonzero element of `TorsionR L N H ⊆ L.D H` is a unit of `U`. -/
theorem isUnit_of_mem_TorsionR (L : LinnellDatum K G U) {N H : Subgroup G} (hNH : N ≤ H)
    (hdivH : ∀ x : ↥(L.D H), x ≠ 0 → IsUnit x) {t : U}
    (ht : t ∈ TorsionR L N H) (hne : t ≠ 0) : IsUnit t :=
  isUnit_of_mem_D L hdivH (TorsionR_le_D L hNH ht) hne

end

theorem commonDenomInR {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Nontrivial U] [Algebra K U] (L : Work.ORLinnell.LinnellDatum K G U) {N H : Subgroup G}
    (hNH : N ≤ H) (hdivH : ∀ x : ↥(L.D H), x ≠ 0 → IsUnit x)
    (hore : ∀ a ∈ Work.ORFinal.TorsionData.TorsionR L N H, a ≠ 0 →
      ∀ b ∈ Work.ORFinal.TorsionData.TorsionR L N H, b ≠ 0 →
      ∃ c ∈ Work.ORFinal.TorsionData.TorsionR L N H, c ≠ 0 ∧
        ∃ d ∈ Work.ORFinal.TorsionData.TorsionR L N H, d ≠ 0 ∧ a * c = b * d)
    (m : ℕ) (δ : Fin m → ↥(L.D H)) :
    ∃ t ∈ Work.ORFinal.TorsionData.TorsionR L N H, t ≠ 0 ∧
      ∀ j, ((δ j : U) * t) ∈ Work.ORFinal.TorsionData.TorsionR L N H := by
  classical
  let R : Subring U := TorsionR L N H
  have hOre : IsRightOre R := hore
  have hUnit : ∀ t ∈ R, t ≠ 0 → IsUnit t :=
    fun t ht hne => isUnit_of_mem_TorsionR L hNH hdivH ht hne
  let O : Subring U :=
    { carrier := IsRightFrac R
      mul_mem' := fun hx hy => IsRightFrac.mul hOre hUnit hx hy
      one_mem' := IsRightFrac.one R
      add_mem' := fun hx hy => IsRightFrac.add hOre hUnit hx hy
      zero_mem' := IsRightFrac.zero R
      neg_mem' := fun hx => IsRightFrac.neg hx }
  have hOclosed : IsDivisionClosed O := by
    intro x hx y hxy
    have hx' : IsRightFrac R x := hx
    obtain ⟨s, hsR, hsne, hxs⟩ := hx'
    have hsD : s ∈ L.D H := TorsionR_le_D L hNH hsR
    have hxsD : x * s ∈ L.D H := TorsionR_le_D L hNH hxs
    have hxD : x ∈ L.D H := mem_D_of_mul_mem_D L hdivH hsD hsne hxsD
    have hyD : y ∈ L.D H := L.isDivisionClosed H x hxD y hxy
    have hxne : x ≠ 0 := by
      intro h; rw [h, zero_mul] at hxy; exact one_ne_zero hxy.symm
    have hxunit : IsUnit x := isUnit_of_mem_D L hdivH hxD hxne
    have hsunit : IsUnit s := isUnit_of_mem_D L hdivH hsD hsne
    have hyx : y * x = 1 := by
      obtain ⟨u, hu⟩ := hxunit
      have h2 : y = ↑(u⁻¹) :=
        IsUnit.mul_left_cancel (show IsUnit (u : U) from ⟨u, rfl⟩)
          (by rw [hu, hxy, ← hu, Units.mul_inv])
      rw [h2, ← hu, Units.inv_mul]
    refine ⟨x * s, hxs, (hxunit.mul hsunit).ne_zero, ?_⟩
    rw [← mul_assoc y x s, hyx, one_mul]
    exact hsR
  have hgen : ∀ h : H, (L.gen (h : G) : U) ∈ O := by
    intro h
    refine ⟨1, R.one_mem, one_ne_zero, ?_⟩
    rw [mul_one]
    exact Subring.subset_closure (Set.mem_union_right _ ⟨h, rfl⟩)
  have hK : ∀ k : K, algebraMap K U k ∈ O := by
    intro k
    refine ⟨1, R.one_mem, one_ne_zero, ?_⟩
    rw [mul_one]
    exact Subring.subset_closure (Set.mem_union_left _ (L.algebraMap_mem N k))
  have hDle : L.D H ≤ O := L.minimal H O hgen hK hOclosed
  obtain ⟨t, htR, htne, ht⟩ := exists_common_denom_finset hOre hUnit Finset.univ
    (fun j : Fin m => ((δ j : ↥(L.D H)) : U)) (fun j _ => hDle (δ j).2)
  exact ⟨t, htR, htne, fun j => ht j (Finset.mem_univ j)⟩

end Work.ORFinal.TorsionData
