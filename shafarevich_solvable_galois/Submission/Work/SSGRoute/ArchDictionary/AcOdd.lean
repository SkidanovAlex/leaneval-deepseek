import Mathlib
import Submission.Work.SSGRoute.ArchDictionary.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The involution `⟨c⟩` acts with trivial `H¹` for odd `p`

For `p` odd and `c` an involution of `Ω ≃ₐ[k] Ω`, the action of `⟨c⟩` on an `𝔽_p`-module `E`
through `SSGRoute.res k K` satisfies: the cocycle value `x = B c` has `x + c • x = 0`, so
`m := -(2⁻¹) • x` (with `2` invertible in `𝔽_p`) is a coboundary witness.  Hence every `1`-cocycle
on `⟨c⟩` is a coboundary, i.e. `Ac = H¹(⟨c⟩,E) = 0`.
-/

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory SSGRoute.PTExt

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
variable (K : IntermediateField k Ω) [Normal k K]

/-- In a group, an element of `⟨a⟩` is `1` or `a` when `a` is an involution. -/
theorem eq_one_or_eq_of_mem_zpowers {G : Type} [Group G] {a g : G} (ha : a ^ 2 = 1)
    (hg : g ∈ Subgroup.zpowers a) : g = 1 ∨ g = a := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_ofNat]; exact ha
  rcases Int.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · left
    rw [hm, show m + m = 2 * m from by ring, zpow_mul, h2, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

variable (p : ℕ) [Fact p.Prime] (E : Type) [AddCommGroup E] [Module (ZMod p) E]
variable [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]

/-- **For odd `p` every cocycle on the involution `⟨c⟩` is a coboundary.** -/
theorem isCoboundaryOn_of_odd (hp2 : p ≠ 2) (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1)
    (B : (Ω ≃ₐ[k] Ω) → E)
    (hbc : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) B) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) B := by
  have hp : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    exact hp2 (le_antisymm hle hge)
  -- the value at `1` is `0`
  have hone : B 1 = 0 := by
    have h := hbc 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
    simp only [mul_one, map_one, one_smul] at h
    exact add_left_cancel (by rw [add_zero]; exact h.symm)
  have hcc : c * c = 1 := by rw [← pow_two]; exact hc2
  -- the cocycle relation at `(c,c)`
  have hrel : B c + (SSGRoute.res k K c) • (B c) = 0 := by
    have h := hbc c (Subgroup.mem_zpowers c) c (Subgroup.mem_zpowers c)
    rw [hcc, hone] at h
    exact h.symm
  have hσ : (SSGRoute.res k K c) • (B c) = -(B c) := by
    have h := hrel
    rw [add_comm] at h
    exact eq_neg_of_add_eq_zero_left h
  refine ⟨-((2 : ZMod p)⁻¹ • (B c)), fun g hg => ?_⟩
  rcases eq_one_or_eq_of_mem_zpowers hc2 hg with hg1 | hgc
  · rw [hg1, hone]; simp
  · rw [hgc]
    have hcomm : (SSGRoute.res k K c) • ((2 : ZMod p)⁻¹ • (B c))
        = (2 : ZMod p)⁻¹ • ((SSGRoute.res k K c) • (B c)) :=
      SMulCommClass.smul_comm (SSGRoute.res k K c) ((2 : ZMod p)⁻¹) (B c)
    calc B c
        = ((2 : ZMod p)⁻¹ * 2) • (B c) := by rw [inv_mul_cancel₀ hp, one_smul]
      _ = ((2 : ZMod p)⁻¹ + (2 : ZMod p)⁻¹) • (B c) := by ring_nf
      _ = ((2 : ZMod p)⁻¹ • (B c)) + ((2 : ZMod p)⁻¹ • (B c)) := add_smul _ _ _
      _ = -((2 : ZMod p)⁻¹ • (-(B c))) + ((2 : ZMod p)⁻¹ • (B c)) := by
          rw [smul_neg, neg_neg]
      _ = -((2 : ZMod p)⁻¹ • ((SSGRoute.res k K c) • (B c))) + ((2 : ZMod p)⁻¹ • (B c)) := by
          rw [hσ]
      _ = -((SSGRoute.res k K c) • ((2 : ZMod p)⁻¹ • (B c))) + ((2 : ZMod p)⁻¹ • (B c)) := by
          rw [hcomm]
      _ = (SSGRoute.res k K c) • (-((2 : ZMod p)⁻¹ • (B c))) - (-((2 : ZMod p)⁻¹ • (B c))) := by
          rw [smul_neg]; abel

/-- **For odd `p` the involution cohomology group `Ac = H¹(⟨c⟩,E)` is trivial.** -/
theorem Ac_subsingleton_of_odd (hp2 : p ≠ 2) (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) :
    Subsingleton (Ac (K := K) (E := E) c) := by
  have hzero : ∀ b : ↥(Zc K E c), Acπ (K := K) (E := E) c b = 0 := fun b =>
    (Acπ_eq_zero_iff (K := K) (E := E) b).mpr
      (isCoboundaryOn_of_odd (K := K) (p := p) (E := E) hp2 c hc2 (b : (Ω ≃ₐ[k] Ω) → E)
        (show SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c)
          (b : (Ω ≃ₐ[k] Ω) → E) from b.2))
  refine ⟨fun x y => ?_⟩
  obtain ⟨b, rfl⟩ := Acπ_surjective (K := K) (E := E) c x
  obtain ⟨b', rfl⟩ := Acπ_surjective (K := K) (E := E) c y
  rw [hzero b, hzero b']

end Work.SSGRoute.ArchDictionary
