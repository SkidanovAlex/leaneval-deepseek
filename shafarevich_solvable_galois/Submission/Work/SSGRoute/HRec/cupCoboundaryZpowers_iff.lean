import Mathlib
import Submission.Work.SSGRoute.HRec.PartB_arch
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local cup class at an involution is the indicator of its value

For `p = 2` and an involution `c` (`c ^ 2 = 1`) of `G_k`, the `Ω`-world cup cochain
`evCupFun a b` of two locally constant `1`-cocycles `a`, `b` is a locally constant
`2`-coboundary on the cyclic subgroup `⟨c⟩` **iff** its value at `(c, c)` vanishes.

This is the explicit computation that `Work.SSGRoute.HRec.archPair_eq_indicator_two` performs
inline (`hcob`, `hdual`): on `⟨c⟩ = {1, c}` the cocycle conditions force the three "trivial" values
`cN 1 1 = cN 1 c = cN c 1 = 0`, and for `p = 2` the action on the line `DualMod p T` is trivial, so
the single remaining equation at `(c,c)` decides the coboundary condition.  Published separately
because the archimedean matching (`Work.SSGRoute.HRec.cupKummer_archMatchK`) needs the criterion
for the *level* cocycle, where it is not reproved inline.
-/

open SSGRoute
open scoped TensorProduct

noncomputable section

namespace Work.SSGRoute.HRec

theorem cupCoboundaryZpowers_iff (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hp : p = 2)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (ha1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a) (ha2 : SSGRoute.IsLocConstOn ⊤ a)
    (hb1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hb2 : SSGRoute.IsLocConstOn ⊤ b)
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) :
    (Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b ∈
        Work.SSGRoute.coboundaries2 p k Ω K (Work.SSGRoute.DualMod p T)
          (Subgroup.zpowers c)) ↔
      Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b c c = 0 := by
  classical
  set cN : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T :=
    Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b with hcNdef
  have ha_one : a 1 = 0 := by
    have h := ha1 1 (Subgroup.mem_top 1) 1 (Subgroup.mem_top 1)
    rw [mul_one, map_one, one_smul] at h
    exact (add_left_cancel (a := a 1) (b := 0) (c := a 1)
      (by rw [add_zero]; exact h)).symm
  have hb_one : b 1 = 0 := by
    have h := hb1 1 (Subgroup.mem_top 1) 1 (Subgroup.mem_top 1)
    rw [mul_one, map_one, one_smul] at h
    exact (add_left_cancel (a := b 1) (b := 0) (c := b 1)
      (by rw [add_zero]; exact h)).symm
  have hcN11 : cN 1 1 = 0 := by
    rw [hcNdef]
    simp [Work.SSGRoute.E7Fin.evCupFun_apply, ha_one]
  have hcN1c : cN 1 c = 0 := by
    rw [hcNdef]
    simp [Work.SSGRoute.E7Fin.evCupFun_apply, ha_one]
  have hcNc1 : cN c 1 = 0 := by
    rw [hcNdef]
    simp [Work.SSGRoute.E7Fin.evCupFun_apply, hb_one]
  have hmem : ∀ g : Ω ≃ₐ[k] Ω, g ∈ Subgroup.zpowers c → g = 1 ∨ g = c :=
    fun g hg => Ach.mem_zpowers_eq_one_or c hc hg
  constructor
  · rintro ⟨b', _hb'loc, hb'eq⟩
    have hb'1 : b' 1 = 0 := by
      have h1 := hb'eq 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
      rw [mul_one, map_one, one_smul, hcN11] at h1
      simpa using h1.symm
    have h2 := hb'eq c (Subgroup.mem_zpowers c) c (Subgroup.mem_zpowers c)
    rw [show c * c = 1 from by rw [← pow_two, hc], hb'1, sub_zero,
      smul_dualMod_eq_self p k Ω K T hp hT.1 (SSGRoute.res k K c) (b' c),
      Ach.add_self_eq_zero_of_eq_two p hp (b' c)] at h2
    exact h2
  · intro h
    refine ⟨fun _ => 0, ⟨⊤, isOpen_univ, fun g _ u _ _ => rfl⟩, ?_⟩
    intro g hg h' hh
    rcases hmem g hg with hg1 | hgc <;> rcases hmem h' hh with hh1 | hhc
    · simp only [hg1, hh1, map_zero, smul_zero, sub_zero, add_zero]
      exact hcN11
    · simp only [hg1, hhc, map_zero, smul_zero, sub_zero, add_zero]
      exact hcN1c
    · simp only [hgc, hh1, map_zero, smul_zero, sub_zero, add_zero]
      exact hcNc1
    · simp only [hgc, hhc, map_zero, smul_zero, sub_zero, add_zero]
      exact h

end Work.SSGRoute.HRec
