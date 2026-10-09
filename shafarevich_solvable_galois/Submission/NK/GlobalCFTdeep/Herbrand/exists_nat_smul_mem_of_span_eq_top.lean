import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.exists_int_smul_mem_of_mem_span_rat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.Herbrand

/-- If `x` lies in the `ℚ`-span of an additive subgroup `M` of a `ℚ`-module `A`, then a nonzero
natural number multiple of `x` lies in `M`. -/
theorem exists_nat_smul_mem_of_mem_span {A : Type} [AddCommGroup A] [Module ℚ A]
    (M : AddSubgroup A) {x : A} (hx : x ∈ Submodule.span ℚ (M : Set A)) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : ℤ) • x ∈ M := by
  obtain ⟨m, hm, hmx⟩ := exists_int_smul_mem_of_mem_span_rat M hx
  have hm0 : m.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hm
  rcases lt_or_ge m 0 with h | h
  · refine ⟨m.natAbs, hm0, ?_⟩
    have hcast : ((m.natAbs : ℕ) : ℤ) = -m := by
      have h1 : (((-m).natAbs : ℕ) : ℤ) = -m := Int.natAbs_of_nonneg (by omega)
      rwa [Int.natAbs_neg] at h1
    rw [hcast]
    simpa using M.neg_mem hmx
  · refine ⟨m.natAbs, hm0, ?_⟩
    have hcast : ((m.natAbs : ℕ) : ℤ) = m := Int.natAbs_of_nonneg h
    rw [hcast]
    exact hmx

/-- If `L` is a finitely generated additive subgroup of a `ℚ`-module `A` and the additive subgroup `M` spans `A` over `ℚ`, then a single nonzero natural number `n` carries all of `L` into `M`. -/
theorem exists_nat_smul_mem_of_span_eq_top {A : Type} [AddCommGroup A] [Module ℚ A]
    (L M : AddSubgroup A) (hM : Submodule.span ℚ (M : Set A) = ⊤)
    [Module.Finite ℤ ↥L] :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ x ∈ L, (n : ℤ) • x ∈ M := by
  classical
  obtain ⟨S, hS⟩ := (inferInstance : Module.Finite ℤ ↥L).fg_top
  have hgen : ∀ y : ↥L, ∃ n : ℕ, n ≠ 0 ∧ (n : ℤ) • (y : A) ∈ M := by
    intro y
    exact exists_nat_smul_mem_of_mem_span M (by rw [hM]; trivial)
  let g : ↥L → ℕ := fun y => Classical.choose (hgen y)
  have hg : ∀ y : ↥L, g y ≠ 0 ∧ (g y : ℤ) • (y : A) ∈ M :=
    fun y => Classical.choose_spec (hgen y)
  refine ⟨∏ y ∈ S, g y, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro y _
    exact (hg y).1
  · intro x hx
    have key : ∀ z : ↥L, ((∏ y ∈ S, g y : ℕ) : ℤ) • (z : A) ∈ M := by
      intro z
      refine Submodule.span_induction (s := (S : Set ↥L))
        (p := fun z _ => ((∏ y ∈ S, g y : ℕ) : ℤ) • (z : A) ∈ M) ?_ ?_ ?_ ?_ (by rw [hS]; exact Submodule.mem_top : z ∈ Submodule.span ℤ (S : Set ↥L))
      · intro y hy
        obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem g hy
        have hz : ((∏ y ∈ S, g y : ℕ) : ℤ) • (y : A)
            = (k : ℤ) • ((g y : ℤ) • (y : A)) := by
          rw [hk]
          push_cast
          rw [mul_comm, smul_smul]
        rw [hz]
        exact M.zsmul_mem (hg y).2 k
      · simp
      · intro y z _ _ ihy ihz
        rw [AddSubgroup.coe_add, smul_add]
        exact M.add_mem ihy ihz
      · intro a y _ ihy
        rw [AddSubgroup.coe_zsmul, smul_smul, mul_comm, ← smul_smul]
        exact M.zsmul_mem ihy a
    exact key ⟨x, hx⟩

end NK.GlobalCFTdeep.Herbrand
