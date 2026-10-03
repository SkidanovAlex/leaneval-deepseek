import Mathlib
import Submission.Work.ORTorsion.Defs

/-- v4.35 port: `TensorProduct.induction_on` lost `@[elab_as_elim]` when deprecated. -/
@[elab_as_elim] private theorem tpInductionOn' {R M N : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] {motive : TensorProduct R M N → Prop}
    (z : TensorProduct R M N) (zero : motive 0) (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z zero tmul add


namespace Work.ORTorsion.Grading

open scoped TensorProduct

open Work.ORTorsion

open Work.ORTorsion.LaurentBase

/-!
# The degree expansion of an element of `V ⊗[K] R`

For the Laurent datum `Lb` attached to a surjection `φ : H ↠ ℤ` with kernel `N` and subalgebra
`R = Σ_{h ∈ H} D(N) h`, the structure field `coord_expand` reconstructs an element `y ∈ R` from
its graded components `coord i y`:
`y = ∑_{i ∈ S} (coord i y) · u ^ i` for a suitable finite `S`.

This file lifts that statement to the tensor product `V ⊗[K] R`: every `z` is the sum of its
graded components `Tm i (inclDN (Mk i z))`.  The proof first isolates the correct "support" of
an element (the finite set of indices carrying a nonzero coordinate), showing that the
reconstruction holds for *any* finite set containing the support; then runs
`TensorProduct.induction_on`, taking unions of supports.
-/

section Helpers

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Algebra K U]
  {gen : G →* Uˣ} {D : Subgroup G → Subalgebra K U} {H : Subgroup G} {φ : H →* Multiplicative ℤ}
  {V : Type*} [AddCommGroup V] [Module K V]

/-! ## The graded component maps on `R` -/

/-- The degree-`i` component of `y ∈ R`, viewed as an element of `R`:
`e i y = coord i y · u ^ i`. -/
noncomputable def e (Lb : LaurentBase K U G gen D H φ) (i : ℤ) :
    ↥Lb.R →ₗ[K] ↥Lb.R :=
  (Lb.rightMulU i).comp ((Subalgebra.inclusion Lb.DN_le_R).toLinearMap.comp (Lb.coord i))

theorem e_apply (Lb : LaurentBase K U G gen D H φ) (i : ℤ) (y : ↥Lb.R) :
    e Lb i y = Lb.rightMulU i ⟨(Lb.coord i y : U), Lb.DN_le_R (Lb.coord i y).2⟩ := rfl

/-- `rightMulU 0` is the identity. -/
theorem rightMulU_zero_apply (Lb : LaurentBase K U G gen D H φ) (y : ↥Lb.R) :
    Lb.rightMulU 0 y = y := by
  apply Subtype.ext; rw [Lb.rightMulU_coe]; simp

/-- The degree-`j` coordinate of an element of `D(N) ⊆ R`. -/
theorem coord_inclusion (Lb : LaurentBase K U G gen D H φ) (j : ℤ) (d : ↥(D Lb.N)) :
    Lb.coord j (⟨(d : U), Lb.DN_le_R d.2⟩ : ↥Lb.R) = if j = 0 then d else 0 := by
  have h := Lb.coord_base j 0 d
  rw [rightMulU_zero_apply] at h
  exact h

/-- The coordinates of a graded component: `coord k (e i y)` is `coord k y` if `k = i` and `0`
otherwise. -/
theorem coord_e (Lb : LaurentBase K U G gen D H φ) (k i : ℤ) (y : ↥Lb.R) :
    Lb.coord k (e Lb i y) = if k = i then Lb.coord i y else 0 := by
  rw [e_apply, Lb.coord_shift, coord_inclusion]
  simp only [sub_eq_zero]

/-- Coordinates of the sum of the graded components. -/
theorem coord_sum_e (Lb : LaurentBase K U G gen D H φ) (S : Finset ℤ) (y : ↥Lb.R) (k : ℤ) :
    Lb.coord k (∑ i ∈ S, e Lb i y) = if k ∈ S then Lb.coord k y else 0 := by
  rw [map_sum]
  simp_rw [coord_e]
  exact Finset.sum_ite_eq S k (fun x => Lb.coord x y)

/-- The coordinate maps are jointly injective: an element all of whose coordinates vanish is `0`. -/
theorem eq_zero_of_coord_eq_zero (Lb : LaurentBase K U G gen D H φ) (y : ↥Lb.R)
    (h : ∀ k, Lb.coord k y = 0) : y = 0 := by
  obtain ⟨S, hS⟩ := Lb.coord_expand y
  have hS' : ∑ i ∈ S, e Lb i y = y := hS
  rw [← hS']
  apply Finset.sum_eq_zero
  intro i hi
  rw [e_apply]
  have hzero : (⟨(Lb.coord i y : U), Lb.DN_le_R (Lb.coord i y).2⟩ : ↥Lb.R) = 0 := by
    apply Subtype.ext; rw [h i]; simp
  rw [hzero, map_zero]

/-- The coordinate maps determine an element of `R`. -/
theorem eq_of_coord_eq (Lb : LaurentBase K U G gen D H φ) {y y' : ↥Lb.R}
    (h : ∀ k, Lb.coord k y = Lb.coord k y') : y = y' := by
  have hsub : y - y' = 0 := eq_zero_of_coord_eq_zero Lb (y - y')
    (fun k => by rw [map_sub, h k, sub_self])
  exact sub_eq_zero.mp hsub

/-- **The reconstruction holds for any set containing the support.**  If `S` contains every index
`i` with `coord i y ≠ 0`, then `y` is the sum of its graded components over `S`. -/
theorem sum_e_eq_of_support (Lb : LaurentBase K U G gen D H φ) (S : Finset ℤ) (y : ↥Lb.R)
    (hS : ∀ i, Lb.coord i y ≠ 0 → i ∈ S) : ∑ i ∈ S, e Lb i y = y := by
  apply eq_of_coord_eq Lb
  intro k
  rw [coord_sum_e]
  by_cases hk : k ∈ S
  · rw [if_pos hk]
  · rw [if_neg hk]
    have h0 : Lb.coord k y = 0 := by
      by_contra hc; exact hk (hS k hc)
    rw [h0]

/-! ## The graded component maps on `V ⊗[K] R` -/

/-- The degree-`i` component of `z ∈ V ⊗[K] R`. -/
noncomputable def Phi (Lb : LaurentBase K U G gen D H φ) (i : ℤ) :
    V ⊗[K] ↥Lb.R →ₗ[K] V ⊗[K] ↥Lb.R :=
  (Tm Lb i).comp ((inclDN Lb).comp (Mk Lb i))

theorem Phi_apply (Lb : LaurentBase K U G gen D H φ) (i : ℤ) (z : V ⊗[K] ↥Lb.R) :
    Phi Lb i z = Tm Lb i (inclDN Lb (Mk Lb i z)) := rfl

theorem Phi_tmul (Lb : LaurentBase K U G gen D H φ) (i : ℤ) (v : V) (y : ↥Lb.R) :
    Phi Lb i (v ⊗ₜ[K] y) = v ⊗ₜ[K] (e Lb i y) := by
  rw [Phi_apply, Mk_tmul, inclDN_tmul, Tm_tmul, ← e_apply]

/-- The sum of the graded components over a finite set `S`. -/
noncomputable def F (Lb : LaurentBase K U G gen D H φ) (S : Finset ℤ) :
    V ⊗[K] ↥Lb.R →ₗ[K] V ⊗[K] ↥Lb.R := ∑ i ∈ S, Phi Lb i

theorem F_apply (Lb : LaurentBase K U G gen D H φ) (S : Finset ℤ) (z : V ⊗[K] ↥Lb.R) :
    F Lb S z = ∑ i ∈ S, Phi Lb i z := by
  rw [F, LinearMap.sum_apply]

theorem F_tmul (Lb : LaurentBase K U G gen D H φ) (S : Finset ℤ) (v : V) (y : ↥Lb.R) :
    F Lb S (v ⊗ₜ[K] y) = v ⊗ₜ[K] (∑ i ∈ S, e Lb i y) := by
  rw [F_apply]
  simp_rw [Phi_tmul]
  rw [TensorProduct.tmul_sum]

/-- `F S` is insensitive to the part of `S` outside the support of `z`. -/
theorem F_eq_of_support (Lb : LaurentBase K U G gen D H φ) {S S' : Finset ℤ}
    (z : V ⊗[K] ↥Lb.R)
    (hS : ∀ i, Mk Lb i z ≠ 0 → i ∈ S) (hS' : ∀ i, Mk Lb i z ≠ 0 → i ∈ S') :
    F Lb S z = F Lb S' z := by
  have h1 : ∑ i ∈ S, Phi Lb i z = ∑ i ∈ S ∪ S', Phi Lb i z := by
    apply Finset.sum_subset (Finset.subset_union_left)
    intro x hx hxS
    have hx0 : Mk Lb x z = 0 := by by_contra hc; exact hxS (hS x hc)
    rw [Phi_apply, hx0, map_zero, map_zero]
  have h2 : ∑ i ∈ S', Phi Lb i z = ∑ i ∈ S ∪ S', Phi Lb i z := by
    apply Finset.sum_subset (Finset.subset_union_right)
    intro x hx hxS
    have hx0 : Mk Lb x z = 0 := by by_contra hc; exact hxS (hS' x hc)
    rw [Phi_apply, hx0, map_zero, map_zero]
  rw [F_apply, F_apply, h1, h2]

/-- Every `z ∈ V ⊗[K] R` is the sum of its graded components over a finite set containing its
support. -/
theorem exists_F_eq (Lb : LaurentBase K U G gen D H φ) (z : V ⊗[K] ↥Lb.R) :
    ∃ S : Finset ℤ, (∀ i, Mk Lb i z ≠ 0 → i ∈ S) ∧ F Lb S z = z := by
  refine tpInductionOn' z ?_ ?_ ?_
  · exact ⟨∅, by simp, by simp⟩
  · intro v y
    obtain ⟨S0, hS0⟩ := Lb.coord_expand y
    have hS0' : ∑ j ∈ S0, e Lb j y = y := hS0
    have hmem : ∀ i, i ∉ S0 → Lb.coord i y = 0 := by
      intro i hi
      have hc : Lb.coord i y = Lb.coord i (∑ j ∈ S0, e Lb j y) := by rw [hS0']
      rw [hc, coord_sum_e, if_neg hi]
    have hsup : ∀ i, Lb.coord i y ≠ 0 → i ∈ S0 := fun i hi => by
      by_contra hc; exact hi (hmem i hc)
    refine ⟨S0, ?_, ?_⟩
    · intro i hi
      by_contra hc
      apply hi
      rw [Mk_tmul, hmem i hc]
      simp
    · rw [F_tmul, sum_e_eq_of_support Lb S0 y hsup]
  · intro z w hz hw
    obtain ⟨S1, hS1, hF1⟩ := hz
    obtain ⟨S2, hS2, hF2⟩ := hw
    refine ⟨S1 ∪ S2, ?_, ?_⟩
    · intro i hi
      rw [Finset.mem_union]
      by_cases h1 : Mk Lb i z = 0
      · right
        apply hS2 i
        intro h2
        apply hi
        rw [map_add, h1, h2, zero_add]
      · left; exact hS1 i h1
    · rw [map_add]
      have e1 : F Lb (S1 ∪ S2) z = z := by
        rw [← F_eq_of_support Lb z hS1 (fun i hi => Finset.mem_union.mpr (Or.inl (hS1 i hi)))]
        exact hF1
      have e2 : F Lb (S1 ∪ S2) w = w := by
        rw [← F_eq_of_support Lb w hS2 (fun i hi => Finset.mem_union.mpr (Or.inr (hS2 i hi)))]
        exact hF2
      rw [e1, e2]

end Helpers

/-- **Expansion into graded components.**  Every `z ∈ V ⊗[K] R` is the sum of its graded
components `Tm i (inclDN (Mk i z))` over a finite set of indices. -/
theorem expansion {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Algebra K U]
    (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (z : V ⊗[K] ↥Lb.R) : ∃ S : Finset ℤ, z = ∑ i ∈ S, Tm Lb i (inclDN Lb (Mk Lb i z)) := by
  obtain ⟨S, _, hF⟩ := exists_F_eq Lb z
  exact ⟨S, hF.symm.trans (by simp only [F_apply, Phi_apply])⟩

end Work.ORTorsion.Grading
