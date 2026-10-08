import Mathlib
import Submission.Work.Frobenius.Fpf.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Fixed-point-freeness descends to invariant quotients (A8b)

If `α` is a fixed-point-free automorphism of a finite group `K` and `N ≤ K` is `α`-invariant,
then the automorphism `QuotientGroup.congr N N α _` induced by `α` on `K ⧸ N` is again
fixed-point-free.

The mathematical content is the following.  Fixed points of the induced automorphism on `K ⧸ N`
are exactly the cosets `xN` with `x⁻¹ * α x ∈ N`.  The map `f z = z⁻¹ * α z` is injective on `K`
(lemma F1, `isFpf_mulInv_injective`) and, since `N` is `α`-invariant, carries `N` into `N`; as `N`
is finite, `f|_N : N → N` is a bijection, so `f x ∈ N` forces `x ∈ N`, i.e. the coset is trivial.
-/

namespace Work.Frobenius.Fpf

open Work.NPC.Fpf

/-- **Key observation.**  If `α` is fixed-point-free and `N` is `α`-invariant, then an element
`x` whose "twisted difference" `x⁻¹ * α x` lies in `N` must itself lie in `N`.

Indeed `f z = z⁻¹ * α z` is injective on `K` (F1) and maps `N` into itself (invariance); since `N`
is finite, `f|_N` is bijective, and `f x ∈ N` exhibits `x` as the preimage of an element of `N`. -/
theorem mem_of_inv_mul_mem_of_isFpf {K : Type*} [Group K] [Finite K] {N : Subgroup K}
    {α : MulAut K} (hα : Work.NPC.Fpf.IsFpf α) (hN : Work.NPC.Fpf.IsInv α N) {x : K}
    (hx : x⁻¹ * α x ∈ N) : x ∈ N := by
  set f : K → K := fun z => z⁻¹ * α z with hf
  have hf_inj : Function.Injective f := isFpf_mulInv_injective hα
  have hfN : ∀ z ∈ N, f z ∈ N := by
    intro z hz
    exact N.mul_mem (N.inv_mem hz) ((hN z).mpr hz)
  let g : ↥N → ↥N := fun z => ⟨f z, hfN z z.2⟩
  have hg_inj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    apply hf_inj
    exact congrArg Subtype.val hab
  have hg_surj : Function.Surjective g := (Finite.injective_iff_bijective.mp hg_inj).2
  obtain ⟨z, hz⟩ := hg_surj ⟨f x, hx⟩
  have hzx : (z : K) = x := hf_inj (congrArg Subtype.val hz)
  exact hzx ▸ z.2

theorem isFpf_quotientCongr {K : Type*} [Group K] [Finite K] {N : Subgroup K} [N.Normal] {α : MulAut K} (hα : Work.NPC.Fpf.IsFpf α) (hN : Work.NPC.Fpf.IsInv α N) : Work.NPC.Fpf.IsFpf (QuotientGroup.congr N N α (by simpa using hN.map_eq)) := by
  intro y
  refine QuotientGroup.induction_on y ?_
  intro x hy
  have hβx : (QuotientGroup.congr N N α (by simpa using hN.map_eq)) (QuotientGroup.mk x)
      = QuotientGroup.mk (α x) :=
    QuotientGroup.congr_mk N N α (by simpa using hN.map_eq) x
  have hx_eq : QuotientGroup.mk (α x) = QuotientGroup.mk x := hβx.symm.trans hy
  rw [QuotientGroup.eq_one_iff]
  refine mem_of_inv_mul_mem_of_isFpf hα hN ?_
  rw [← QuotientGroup.eq]
  exact hx_eq.symm

end Work.Frobenius.Fpf
