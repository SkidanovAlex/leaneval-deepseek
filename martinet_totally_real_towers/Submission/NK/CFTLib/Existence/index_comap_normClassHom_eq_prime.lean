import Mathlib
import Submission.NK.GlobalCFT.IdeleClassGroupExact
import Submission.NK.GlobalCFT.NormFunctorial
import Submission.NK.GlobalCFT.NormGroup.Basic

/-!
# The index of the preimage of an index-`p` subgroup under a norm map

This file contains a purely group-theoretic lemma and its application to the norm map of idèle
class groups, `NormClassHom K K' : C[K'] →* C[K]`.

## Main results

* `NK.CFTLib.Existence.index_comap_eq_prime_of_not_dvd_range_index` — **the group-theoretic
  kernel of the argument.**  Let `f : G →* H` be a group homomorphism, `V ≤ H` a subgroup of
  prime index `p`, and suppose that `p` does not divide the index of the range of `f`.  Then the
  preimage `f ⁻¹' V` again has index `p` in `G`.

  Note that `f` need not be surjective: the point is that `p ∤ [H : f.range]` forces the range of
  `f` to be "large enough" relative to `V`.  Concretely, with `y := [f.range : V ∩ f.range]`
  one has

  * `y * [H : f.range] = [H : V ∩ f.range] = p * [V : V ∩ f.range]` (Lagrange), so that
    `p ∣ y` because `p ∤ [H : f.range]`;
  * `y ≤ p`, because `f.range ⧸ (V ∩ f.range)` embeds into the coset space `H ⧸ V`, which has `p`
    elements (`Subgroup.relIndex_le_of_le_right`);
  * `y ≠ 0`, because that coset space is finite (`V.index = p ≠ 0`).

  Hence `y = p`, i.e. `[G : f ⁻¹' V] = y = p`.

* `NK.CFTLib.Existence.index_comap_normClassHom_eq_prime` — the application: the norm subgroup
  `N_{K'/K} C_{K'}` is the range of `NormClassHom K K'`
  (`NK.GlobalCFT.Idele.normClassSubgroup_eq_range`), so a subgroup `V ≤ C_K` of prime index `p`
  whose index is not divisible by `p` pulls back to a subgroup of `C_{K'}` of index `p`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace NK.CFTLib.Existence

/-! ## The group-theoretic lemma -/

/-- **Preimages of index-`p` subgroups under maps whose range index is coprime to `p`.**

If `V ≤ H` has prime index `p` and `p` does not divide the index of the range of `f : G →* H`,
then `f ⁻¹' V` has index `p` in `G`. -/
theorem index_comap_eq_prime_of_not_dvd_range_index {G H : Type*} [Group G] [Group H]
    (f : G →* H) (V : Subgroup H) {p : ℕ} (hp : p.Prime) (hV : V.index = p)
    (hcop : ¬ p ∣ f.range.index) : (V.comap f).index = p := by
  -- the coset space `H ⧸ V` is finite
  haveI hfin : Finite (H ⧸ V) := by
    rw [← not_infinite_iff_finite]
    intro hinf
    haveI := hinf
    have h0 : Nat.card (H ⧸ V) = 0 := Nat.card_eq_zero_of_infinite
    exact hp.ne_zero (by rw [← hV]; exact h0)
  -- reduce to the relative index of `V` inside `f.range`
  rw [Subgroup.index_comap]
  set R : Subgroup H := f.range with hR
  -- Lagrange: `[R : V ⊓ R] * [H : R] = [H : V ⊓ R] = [V : V ⊓ R] * p`
  have hlag1 : (V ⊓ R).relIndex R * R.index = (V ⊓ R).index :=
    Subgroup.relIndex_mul_index inf_le_right
  have hlag2 : (V ⊓ R).relIndex V * V.index = (V ⊓ R).index :=
    Subgroup.relIndex_mul_index inf_le_left
  have hb : R.index ≠ 0 := fun h => hcop (by rw [h]; exact dvd_zero p)
  -- hence `p` divides `[R : V ⊓ R]`
  have hpy : p ∣ (V ⊓ R).relIndex R := by
    have h1 : p ∣ (V ⊓ R).relIndex R * R.index := by
      rw [hlag1, ← hlag2, hV]
      exact dvd_mul_left p _
    rcases hp.dvd_mul.mp h1 with h | h
    · exact h
    · exact absurd h hcop
  -- and `[R : V ⊓ R] ≤ [H : V] = p`
  have hle : (V ⊓ R).relIndex R ≤ p := by
    rw [Subgroup.inf_relIndex_right V R]
    have h := Subgroup.relIndex_le_of_le_right (H := V) (K := R) (L := ⊤) le_top
      (by rw [Subgroup.relIndex_top_right, hV]; exact hp.ne_zero)
    rwa [Subgroup.relIndex_top_right, hV] at h
  -- orbit-stabilizer identifies `[R : V ⊓ R]` with the orbit of the coset `V` under `R`;
  -- that orbit is a nonempty subset of the finite set `H ⧸ V`, so `[R : V ⊓ R] ≠ 0`.
  let x0 : H ⧸ V := QuotientGroup.mk (1 : H)
  have hsmul : ∀ r : ↥R, r • x0 = (QuotientGroup.mk (r : H) : H ⧸ V) := by
    intro r
    show (r : ↥R) • (QuotientGroup.mk (1 : H) : H ⧸ V) = _
    first
      | (rw [MulAction.compHom_smul_def, MulAction.Quotient.smul_mk]; simp)
      | (rw [MulAction.Quotient.smul_mk]; simp)
      | (simp [MulAction.Quotient.smul_mk])
      | rfl
      | (change (QuotientGroup.mk ((r : H) * 1) : H ⧸ V) = _; simp)
  have hstab : MulAction.stabilizer ↥R x0 = (V ⊓ R).subgroupOf R := by
    ext r
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hsmul r]
    constructor
    · intro h
      exact ⟨by simpa using (QuotientGroup.eq.mp h), r.2⟩
    · rintro ⟨h1, h2⟩
      exact QuotientGroup.eq.mpr (by simpa using h1)
  have hy : (V ⊓ R).relIndex R = (MulAction.orbit ↥R x0).ncard := by
    have h := MulAction.index_stabilizer ↥R x0
    rw [hstab] at h
    exact h
  have horbfin : (MulAction.orbit ↥R x0).Finite :=
    Set.Finite.subset (Set.finite_univ (α := H ⧸ V)) (Set.subset_univ _)
  have hne : (V ⊓ R).relIndex R ≠ 0 := by
    rw [hy]
    exact (Set.ncard_pos horbfin).mpr ⟨x0, MulAction.mem_orbit_self x0⟩ |>.ne'
  -- `p ∣ y`, `y ≤ p`, `y ≠ 0` force `y = p`
  have hyval : (V ⊓ R).relIndex R = p := by
    obtain ⟨k, hk⟩ := hpy
    have hk1 : k = 1 := by
      have hkp : k ≤ 1 := by
        have h2 : p * k ≤ p := by rw [← hk]; exact hle
        have h3 : p * k ≤ p * 1 := by simpa using h2
        exact Nat.le_of_mul_le_mul_left h3 hp.pos
      have hk0 : k ≠ 0 := by
        intro h0
        exact hne (by rw [hk, h0, mul_zero])
      omega
    rw [hk, hk1, mul_one]
  rw [← Subgroup.inf_relIndex_right V R]
  exact hyval

/-! ## The application to idèle class groups -/

theorem index_comap_normClassHom_eq_prime
    {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    [FiniteDimensional K K'] (p : ℕ) [Fact p.Prime]
    (V : Subgroup (NK.GlobalCFT.IdeleClassGroup K)) (hV : V.index = p)
    (hcop : ¬ p ∣ (NK.GlobalCFT.Idele.normClassSubgroup K K').index) :
    (V.comap (NK.GlobalCFT.IdeleClassGroup.normClassHom K K')).index = p := by
  refine index_comap_eq_prime_of_not_dvd_range_index
    (NK.GlobalCFT.IdeleClassGroup.normClassHom K K') V (Fact.out : p.Prime) hV ?_
  rw [NK.GlobalCFT.Idele.normClassSubgroup_eq_range] at hcop
  exact hcop

end NK.CFTLib.Existence
