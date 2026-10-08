/-
# The Singer cycle of `Aut((Z/2)^3)`

An elementary abelian group of order `8` (a finite group of order `8` and exponent `2`) carries
an automorphism of order `7` acting transitively on its seven non-identity elements.  This is the
`GL(3,2)`-Singer cycle, transported through the classification
`Work.Hering.Step5.iso_fin3` of groups of order `8` and exponent `2`.
-/

import Mathlib
import Submission.Work.Hering.Step5.mulAut_eight_order21

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
namespace Work.Hering.GL32

open Work.Hering.Step5

/-- `𝔽₂³` as a multiplicative group. -/
abbrev W3 : Type := Multiplicative (Fin 3 → ZMod 2)

/-- `e7` (of order `7`) acts transitively on the seven non-identity elements of `𝔽₂³`. -/
theorem e7_trans (x y : W3) (hx : x ≠ 1) (hy : y ≠ 1) : ∃ k : ℕ, (e7 ^ k) x = y := by
  obtain ⟨k, hk⟩ :=
    (show ∀ x y : W3, x ≠ 1 → y ≠ 1 → ∃ k : Fin 7, (e7 ^ (k : ℕ)) x = y from by decide)
      x y hx hy
  exact ⟨(k : ℕ), hk⟩

/-- **The Singer cycle.** A finite group of order `8` and exponent `2` has an automorphism of
order `7` transitive on its non-identity elements. -/
theorem singer_of_exp_two {V : Type*} [Group V] [Finite V] (habel : ∀ x y : V, x * y = y * x)
    (hexp : ∀ x : V, x * x = 1) (hcard : Nat.card V = 8) :
    ∃ ξ : MulAut V, orderOf ξ = 7 ∧
      ∀ a b : V, a ≠ 1 → b ≠ 1 → ∃ k : ℕ, (ξ ^ k) a = b := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨e⟩ := iso_fin3 hcard hexp
  refine ⟨(MulAut.congr e).symm e7, ?_, ?_⟩
  · exact (orderOf_injective ((MulAut.congr e).symm : MulAut W3 →* MulAut V)
      (MulAut.congr e).symm.injective e7).trans (orderOf_eq_prime e7_pow_seven e7_ne_one)
  · intro a b ha hb
    have ha' : e a ≠ 1 := fun h => ha (by rw [← e.symm_apply_apply a, h, map_one])
    have hb' : e b ≠ 1 := fun h => hb (by rw [← e.symm_apply_apply b, h, map_one])
    obtain ⟨k, hk⟩ := e7_trans (e a) (e b) ha' hb'
    refine ⟨k, ?_⟩
    have hpow : ((MulAut.congr e).symm e7) ^ k = (MulAut.congr e).symm (e7 ^ k) :=
      (map_pow _ _ _).symm
    rw [hpow]
    have hval : ((MulAut.congr e).symm (e7 ^ k)) a = e.symm ((e7 ^ k) (e a)) := rfl
    rw [hval, hk, e.symm_apply_apply]

end Work.Hering.GL32
