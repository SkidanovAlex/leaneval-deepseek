import Mathlib
import Submission.Work.ORTorsion.Defs

/-- v4.35 port: `TensorProduct.induction_on` lost `@[elab_as_elim]` when deprecated. -/
@[elab_as_elim] private theorem tpInductionOn' {R M N : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] {motive : TensorProduct R M N → Prop}
    (z : TensorProduct R M N) (zero : motive 0) (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z zero tmul add


set_option autoImplicit false

namespace Work.ORTorsion.Grading

open scoped TensorProduct

open Work.ORTorsion

open Work.ORTorsion.LaurentBase

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Algebra K U]

/-! ## The two elementary rules of the grading

`Mk` extracts a degree coordinate and `Tm` shifts degrees, so composing `Mk i` with `Tm k`
shifts the extracted degree by `k`, and `Mk i` kills the image of `V ⊗[K] D(N)` unless `i = 0`.
These are `LaurentBase.coord_shift` and `LaurentBase.coord_base` transported through the tensor
product.  They are proved here (rather than imported) so that this file is self-contained. -/

/-- **Degree shift.** The degree-`i` coordinate of `Tm k z` is the degree-`(i - k)` coordinate
of `z`. -/
theorem mk_tm (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (i k : ℤ) (z : V ⊗[K] ↥Lb.R) : Mk Lb i (Tm Lb k z) = Mk Lb (i - k) z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul v y => rw [Tm_tmul, Mk_tmul, Mk_tmul, Lb.coord_shift]
  | add z w hz hw =>
      simp only [map_add]
      rw [hz, hw]

/-- The degree-`j` coordinate of (the image in `R` of) an element of `D(N)` is the element
itself in degree `0` and `0` otherwise. -/
theorem coord_self (L : TorsionData K G U) {H : Subgroup G} {φ : H →* Multiplicative ℤ}
    (Lb : LaurentBase K U G L.gen L.D H φ) (j : ℤ) (d : ↥(L.D Lb.N)) :
    Lb.coord j ⟨(d : U), Lb.DN_le_R d.2⟩ = if j = 0 then d else 0 := by
  have h0 : (⟨(d : U), Lb.DN_le_R d.2⟩ : ↥Lb.R)
      = Lb.rightMulU 0 ⟨(d : U), Lb.DN_le_R d.2⟩ := by
    apply Subtype.ext
    rw [Lb.rightMulU_coe]
    simp
  rw [h0]
  exact Lb.coord_base j 0 d

/-- **The image of `V ⊗[K] D(N)` sits in degree `0`.** -/
theorem mk_inclDN (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (i : ℤ) (z : V ⊗[K] ↥(L.D Lb.N)) :
    Mk Lb i (inclDN Lb z) = if i = 0 then z else 0 := by
  induction z using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero]
      by_cases h : i = 0 <;> simp [h]
  | tmul v d =>
      rw [inclDN_tmul, Mk_tmul, coord_self L Lb i d]
      by_cases h : i = 0
      · simp [h]
      · simp [h, TensorProduct.tmul_zero]
  | add z w hz hw =>
      rw [map_add, map_add, hz, hw]
      by_cases h : i = 0 <;> simp [h]

/-! ## The degree expansion and the top degree -/

/-- **The degree coordinates vanish outside a finite support.**  If `z : V ⊗[K] R` admits the
expansion `z = ∑_{i ∈ S} Tm i (inclDN (Mk i z))` in the grading shifts `Tm i`, then the `i`-th
coordinate of `z` vanishes for every `i ∉ S`.  This is obtained by applying `Mk j` to the
expansion and using `mk_tm` and `mk_inclDN`. -/
theorem Mk_eq_zero_of_not_mem (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (z : V ⊗[K] ↥Lb.R) (S : Finset ℤ)
    (hS : z = ∑ i ∈ S, Tm Lb i (inclDN Lb (Mk Lb i z))) :
    ∀ i, i ∉ S → Mk Lb i z = 0 := by
  intro i hi
  have hterm : ∀ k : ℤ, Mk Lb i (Tm Lb k (inclDN Lb (Mk Lb k z))) =
      if i = k then Mk Lb k z else 0 := by
    intro k
    rw [mk_tm L Lb i k, mk_inclDN L Lb (i - k) (Mk Lb k z)]
    rcases eq_or_ne i k with h | h
    · rw [h]; simp
    · have h' : i - k ≠ 0 := sub_ne_zero.mpr h
      simp [h, h']
  have h : Mk Lb i z = ∑ k ∈ S, Mk Lb i (Tm Lb k (inclDN Lb (Mk Lb k z))) := by
    conv_lhs => rw [hS]
    rw [map_sum]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)] at h
  rw [Finset.sum_ite_eq] at h
  simpa [hi] using h

/-- **The degree expansion of an element of `V ⊗[K] R`.**  Every `z` is a finite sum of its
graded pieces `Tm i (inclDN (Mk i z))`.  On pure tensors this is the reconstruction
`LaurentBase.coord_expand`; for sums one takes the union of the support sets, the extra terms
vanishing by `Mk_eq_zero_of_not_mem`. -/
theorem exists_expansion (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (z : V ⊗[K] ↥Lb.R) : ∃ S : Finset ℤ, z = ∑ i ∈ S, Tm Lb i (inclDN Lb (Mk Lb i z)) := by
  revert z
  intro z
  refine tpInductionOn' z ?_ ?_ ?_
  · exact ⟨∅, by simp⟩
  · intro v y
    obtain ⟨S, hS⟩ := Lb.coord_expand y
    refine ⟨S, ?_⟩
    conv_lhs => rw [← hS]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Mk_tmul, inclDN_tmul, Tm_tmul]
  · intro z w hz hw
    obtain ⟨Sz, hzS⟩ := hz
    obtain ⟨Sw, hwS⟩ := hw
    have hzf : (∑ i ∈ Sz, Tm Lb i (inclDN Lb (Mk Lb i z)))
        = ∑ i ∈ Sz ∪ Sw, Tm Lb i (inclDN Lb (Mk Lb i z)) :=
      Finset.sum_subset (fun x hx => Finset.mem_union.mpr (Or.inl hx)) (fun i _ hiSz => by
        have h0 : Mk Lb i z = 0 := Mk_eq_zero_of_not_mem L Lb z Sz hzS i hiSz
        simp [h0])
    have hwf : (∑ i ∈ Sw, Tm Lb i (inclDN Lb (Mk Lb i w)))
        = ∑ i ∈ Sz ∪ Sw, Tm Lb i (inclDN Lb (Mk Lb i w)) :=
      Finset.sum_subset (fun x hx => Finset.mem_union.mpr (Or.inr hx)) (fun i _ hiSw => by
        have h0 : Mk Lb i w = 0 := Mk_eq_zero_of_not_mem L Lb w Sw hwS i hiSw
        simp [h0])
    refine ⟨Sz ∪ Sw, ?_⟩
    have hsum : (∑ i ∈ Sz ∪ Sw, Tm Lb i (inclDN Lb (Mk Lb i (z + w))))
        = (∑ i ∈ Sz ∪ Sw, Tm Lb i (inclDN Lb (Mk Lb i z)))
          + (∑ i ∈ Sz ∪ Sw, Tm Lb i (inclDN Lb (Mk Lb i w))) := by
      simp only [map_add, Finset.sum_add_distrib]
    rw [hsum, ← hzf, ← hwf, ← hzS, ← hwS]

/-- **Existence of a top degree.**  A nonzero element `z` of `V ⊗[K] R` is the sum of its
graded pieces over a finite set `S` of degrees, and there is a degree `d` with nonzero
coordinate `Mk d z` which is maximal among the degrees in `S` carrying a nonzero coordinate:
the degree-`(b+d)` component of `z` in L5 of the design. -/
theorem exists_top_degree {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (z : V ⊗[K] ↥Lb.R) (hz : z ≠ 0) :
    ∃ (d : ℤ) (S : Finset ℤ), z = ∑ i ∈ S, Tm Lb i (inclDN Lb (Mk Lb i z)) ∧
      Mk Lb d z ≠ 0 ∧ (∀ i ∈ S, d < i → Mk Lb i z = 0) := by
  classical
  obtain ⟨S, hS⟩ := exists_expansion L Lb z
  have hne : (S.filter (fun i => Mk Lb i z ≠ 0)).Nonempty := by
    by_contra hemp
    refine hz ?_
    rw [hS]
    refine Finset.sum_eq_zero (fun i hiS => ?_)
    have h0 : Mk Lb i z = 0 := by
      by_contra hc
      have hmem : i ∈ S.filter (fun i => Mk Lb i z ≠ 0) := Finset.mem_filter.mpr ⟨hiS, hc⟩
      exact hemp ⟨i, hmem⟩
    simp [h0]
  refine ⟨(S.filter (fun i => Mk Lb i z ≠ 0)).max' hne, S, hS, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
  · intro i hiS hlt
    by_contra hc
    have hmem : i ∈ S.filter (fun i => Mk Lb i z ≠ 0) := Finset.mem_filter.mpr ⟨hiS, hc⟩
    have hle : i ≤ (S.filter (fun i => Mk Lb i z ≠ 0)).max' hne := Finset.le_max' _ i hmem
    omega

end Work.ORTorsion.Grading
