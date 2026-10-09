import Mathlib
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.HonestPairing
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.NormPow
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.LocalFactor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer level of a product is contained in the compositum of the Kummer levels

The level `hLevel β = ↥K(β^{1/p})` of a global unit `β ∈ Kˣ` (the Kummer field of `β` inside the
separable closure `Ω`, `NK.LocalAnabelian.kummerField`) is *submultiplicative in the compositum*:

  `hLevel (β * β') ≤ hLevel β ⊔ hLevel β'`.

Note that this is an inequality, not an equality: the reverse inclusion would require the `p`-th
roots of unity of `K` to lie in `K`, which is not assumed (the statement is used only in the
direction `≤`, for transporting a pairing value computed at a Kummer level up to a bigger field).

The mathematical content is the elementary observation that *some* `p`-th root of `β'` lies in the
compositum `M := hLevel β ⊔ hLevel β'` and that the quotient of a `p`-th root of `β * β'` by it is
a `p`-th root of `β`; the Kummer field is the `adjoin` of *all* the `p`-th roots, so this suffices.

The existence of the `p`-th root of `β'` in `Ω` is supplied by the algebraic closedness of `Ω`.
-/

namespace Work.SSGRoute.ZDataMup.LTRecFamHonest

open Classical

noncomputable section

set_option linter.unusedSectionVars false

/-- **The Kummer field of a product is contained in the compositum of the Kummer fields.**

If `K'` contains a `p`-th root `δ` of `b`, then every `p`-th root `α` of `a * b` lies in
`k(a^{1/p}) ⊔ k(b^{1/p})`: indeed `α / δ` is a `p`-th root of `a`.

The hypothesis `hb` is the only thing that has to be supplied by the situation; in the intended
application `K' = Ω` is algebraically closed and `hb` follows from
`IsAlgClosed.exists_pow_nat_eq`. -/
theorem kummerField_mul_le {p : ℕ} (hp : 0 < p) {k K' : Type*} [Field k] [Field K']
    [Algebra k K'] (a b : kˣ) (hb : ∃ δ : K', δ ^ p = algebraMap k K' (b : k)) :
    NK.LocalAnabelian.kummerField (K' := K') p (a * b) ≤
      NK.LocalAnabelian.kummerField (K' := K') p a ⊔
        NK.LocalAnabelian.kummerField (K' := K') p b := by
  rw [NK.LocalAnabelian.kummerField_le_iff]
  intro α hα
  obtain ⟨δ, hδ⟩ := hb
  -- `b` is a unit, so `algebraMap b ≠ 0`, hence any `p`-th root `δ` of it is nonzero
  have hb0 : algebraMap k K' (b : k) ≠ 0 := by simp
  have hδ0 : δ ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne'] at hδ
    exact hb0 hδ.symm
  -- `α / δ` is a `p`-th root of `a`
  have hγ : α / δ ∈ NK.LocalAnabelian.kummerField (K' := K') p a := by
    apply NK.LocalAnabelian.mem_kummerField_of_pow_eq
    rw [div_pow, hα, hδ, Units.val_mul, map_mul]
    exact mul_div_cancel_right₀ _ hb0
  have hγM : α / δ ∈ NK.LocalAnabelian.kummerField (K' := K') p a ⊔
      NK.LocalAnabelian.kummerField (K' := K') p b :=
    (show NK.LocalAnabelian.kummerField (K' := K') p a ≤ _ from le_sup_left) hγ
  have hδM : δ ∈ NK.LocalAnabelian.kummerField (K' := K') p a ⊔
      NK.LocalAnabelian.kummerField (K' := K') p b :=
    (show NK.LocalAnabelian.kummerField (K' := K') p b ≤ _ from le_sup_right)
      (NK.LocalAnabelian.mem_kummerField_of_pow_eq hδ)
  have hm := mul_mem hγM hδM
  rwa [div_mul_cancel₀ _ hδ0] at hm

/-- **Submultiplicativity of the Kummer level in the compositum**: the Kummer level of a product of
two global units is contained in the compositum of the Kummer levels. -/
theorem hLevel_mul_le {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (β β' : (↥K)ˣ) :
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) (β * β') ≤
      Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) β ⊔
        Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) β' := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  -- a `p`-th root of `β'` exists because `Ω` is algebraically closed
  have hb : ∃ δ : Ω, δ ^ p = algebraMap ↥K Ω (β' : ↥K) :=
    IsAlgClosed.exists_pow_nat_eq (algebraMap ↥K Ω (β' : ↥K)) hp
  exact kummerField_mul_le (k := ↥K) (K' := Ω) hp β β' hb

end

end Work.SSGRoute.ZDataMup.LTRecFamHonest
