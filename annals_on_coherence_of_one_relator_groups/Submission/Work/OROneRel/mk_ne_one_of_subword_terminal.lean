import Mathlib
import Submission.Work.OROneRel.Basic

/-!
# Nontriviality of short subwords of powers of a single generator

A subword of a power of the one-letter word `of x` is again a power of `of x`; and in the
one-relator group `⟨α | x ^ l⟩` the image of `of x ^ m` is nontrivial as soon as `0 < m < l`
(the map `⟨α | x ^ l⟩ → ℤ/l` sending `x ↦ 1` detects it).

Together these give the terminal case of Weinbaum's theorem: a nontrivial subword `v` of
`(of x ^ l) ^ k` of length `< l` is nontrivial in `⟨α | x ^ l⟩`.
-/

namespace Work.OROneRel

universe u

open FreeGroup

/-- A subword of a power `of a ^ n` of the one-letter word `of a` is a power of `of a`: the
reduced word of `v` is a constant list of letters `(a, true)`. -/
theorem isSubwordOf_pow_single_gen {α : Type u} (a : α) (n : ℕ) (v : FreeGroup α)
    (h : Work.OROneRel.IsSubwordOf v (FreeGroup.of a ^ n)) :
    ∃ m : ℕ, v = FreeGroup.of a ^ m := by
  classical
  obtain ⟨L₁, L₂, hL⟩ := h
  have hmem : ∀ b ∈ FreeGroup.toWord v, b = (a, true) := by
    intro b hb
    have h1 : b ∈ FreeGroup.toWord (FreeGroup.of a ^ n) := by
      rw [hL]
      exact List.mem_append_left _ (List.mem_append_right _ hb)
    rw [FreeGroup.toWord_of_pow] at h1
    exact (List.mem_replicate.mp h1).2
  exact ⟨(FreeGroup.toWord v).length, by
    apply FreeGroup.toWord_injective
    rw [FreeGroup.toWord_of_pow]
    exact List.eq_replicate_length.mpr hmem⟩

/-- In the one-relator group `⟨α | x ^ l⟩`, the image of `of x ^ m` is nontrivial whenever
`0 < m < l`: the homomorphism `⟨α | x ^ l⟩ →* Multiplicative (ZMod l)` sending `x` to the
generator `1` of `ℤ/l` sends `of x ^ m` to `ofAdd m ≠ 1`. -/
theorem presentedGroup_mk_pow_single_gen_ne_one {α : Type u} (x : α) (l m : ℕ)
    (hm : m ≠ 0) (hml : m < l) :
    PresentedGroup.mk ({FreeGroup.of x ^ l} : Set (FreeGroup α)) (FreeGroup.of x ^ m) ≠ 1 := by
  classical
  set f : α → Multiplicative (ZMod l) :=
    fun a => if a = x then Multiplicative.ofAdd (1 : ZMod l) else 1 with hf
  have hfx : f x = Multiplicative.ofAdd (1 : ZMod l) := by simp [hf]
  have hrel : ∀ r ∈ ({FreeGroup.of x ^ l} : Set (FreeGroup α)), FreeGroup.lift f r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    rw [map_pow, FreeGroup.lift_apply_of, hfx, ← ofAdd_nsmul]
    have : l • (1 : ZMod l) = 0 := by rw [nsmul_eq_mul, mul_one, ZMod.natCast_self]
    rw [this, ofAdd_zero]
  intro hc
  have hφ : (PresentedGroup.toGroup hrel)
      (PresentedGroup.mk ({FreeGroup.of x ^ l}) (FreeGroup.of x ^ m))
      = Multiplicative.ofAdd (m : ZMod l) := by
    rw [show (PresentedGroup.toGroup hrel)
        (PresentedGroup.mk ({FreeGroup.of x ^ l}) (FreeGroup.of x ^ m))
        = FreeGroup.lift f (FreeGroup.of x ^ m) from rfl]
    rw [map_pow, FreeGroup.lift_apply_of, hfx, ← ofAdd_nsmul]
    congr 1
    rw [nsmul_eq_mul, mul_one]
  rw [hc] at hφ
  rw [MonoidHom.map_one] at hφ
  have hm0 : ((m : ZMod l)) = 0 := ofAdd_eq_one.mp hφ.symm
  have hdvd : l ∣ m := (ZMod.natCast_eq_zero_iff m l).mp hm0
  exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hm) hml hdvd

set_option linter.unusedVariables false in
theorem mk_ne_one_of_subword_terminal {α : Type u} (x : α) (l : ℕ) (hl : 1 ≤ l) (k : ℕ)
    (v : FreeGroup α) (h : Work.OROneRel.IsSubwordOf v ((FreeGroup.of x ^ l) ^ k))
    (hv : Work.OROneRel.relatorNorm v < l) (hv1 : v ≠ 1) :
    PresentedGroup.mk ({FreeGroup.of x ^ l} : Set (FreeGroup α)) v ≠ 1 := by
  classical
  rw [← pow_mul] at h
  obtain ⟨m, rfl⟩ := isSubwordOf_pow_single_gen x (l * k) v h
  have hnorm : Work.OROneRel.relatorNorm (FreeGroup.of x ^ m) = m := by
    simp [Work.OROneRel.relatorNorm, FreeGroup.norm_of_pow]
  rw [hnorm] at hv
  have hm : m ≠ 0 := by
    rintro rfl
    exact hv1 (by simp)
  exact presentedGroup_mk_pow_single_gen_ne_one x l m hm hv

end Work.OROneRel
