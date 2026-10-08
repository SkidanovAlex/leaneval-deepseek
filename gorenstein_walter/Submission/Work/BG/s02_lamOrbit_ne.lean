import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.centralValue
import Submission.Work.BG.lambda_mul_irreducible

/-!
# Area BG: the `Λ`-orbit of an irreducible character of `H₀` is not a singleton

`Λ` is the group of linear characters of `H₀/U` inflated to `H₀` (the class functions
`Work.BG.lamCF C β`, `β : H₀/U →* ℂˣ`); it acts on the class functions of `H₀` by pointwise
multiplication and preserves `Irr(H₀)` (`Work.BG.lambda_mul_irreducible`).  The claim proved
here is that **no** irreducible character `ν` of `H₀` is fixed by every element of `Λ` —
equivalently, that the `Λ`-orbit `Λν` has at least two elements.  This is exactly the
hypothesis-free input "`|Λν| ≥ 2`" of Bender–Glauberman 1981, Lemma 2.1(c)
(`Work.BG.OrbitCardProp`), the complement of the orbit–stabiliser computation giving that
`|Λν|` is a `2`-power (which needs the action to be free of the trivial orbit).

Note that the statement is *not* about the stabiliser `Λ_ν` alone: what matters for the orbit
sums of Lemma 1.7(ii) is that the action of `Λ` on `Irr(H₀)` is never trivial.  (The stabiliser
*can* be large: for `H₀ = A₄`, `U = 1` the character of degree `3` is fixed by every linear
character, since it is the only irreducible of its degree; that configuration is excluded here,
`H₀/U` being a cyclic `2`-group with `t ∉ U`.)

## The argument

Let `a = tU ∈ H₀/U` be the class of the central involution `t`; `a ≠ 1` because `t ∉ U`
(`Sec2Ctx.t_not_mem_U`).  By duality of finite abelian groups
(`CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`, `ℂ` having enough roots of unity)
there is `β : H₀/U →* ℂˣ` with `β a ≠ 1`; as `a² = 1`, its image satisfies `β a = ±1`, hence
`β a = -1`.  This is `Work.BG.s02_exists_lamCF_apply_t_eq_neg_one` below, the character
`λ₁` of the proof of Lemma 1.7(iii) of Bender–Glauberman 1981.

If `lamCF C β * ν = ν` held, evaluating at `t` would give `(-1) · ν(t) = ν(t)`, hence
`ν(t) = 0`.  But `t` is central in `H₀` and an involution, so by Schur's lemma it acts on the
underlying irreducible representation by the scalar `±1`, whence `ν(t) = ±ν(1) ≠ 0`
(`Work.BG.centralValue`).  Contradiction.

## Implementation remark

`H₀/U` is commutative *because it is cyclic* (`Sec2Ctx.quot_cyclic`); we record this as a lemma
rather than as a `CommGroup` instance, to avoid putting a second (definitionally equal) `Group`
structure on the quotient.  Inside the proof of the character-existence lemma the commuting
structure is installed locally through `IsMulCommutative.instCommGroup`, which is
instance-reducible and therefore unfolds to the canonical quotient group — so that the
`MonoidHom` produced by duality is *the same type* as the one `Work.BG.lamCF` expects.  (A
local `CommGroup` instance built by hand from a structure literal does *not* unfold, and the
two types then fail to be definitionally equal.)
-/

set_option linter.style.haveILetI false

namespace Work.BG

open OddOrder.RepresentationTheory
open Subgroup

/-- `H₀/U` is cyclic: the class of the element `c` exhibited by `Sec2Ctx.quot_cyclic` generates
it. -/
private theorem s02_quot_isCyclic {G : Type} [Group G] [Finite G] (C : Sec2Ctx G) :
    IsCyclic (quotGroup C.P) := by
  obtain ⟨c, hc, hgen⟩ := C.quot_cyclic
  refine isCyclic_iff_exists_zpowers_eq_top.mpr ⟨quotMk C.P ⟨c, hc⟩, ?_⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ x
  obtain ⟨k, hk⟩ := hgen (y : G) y.2
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← map_zpow]
  refine (QuotientGroup.eq).mpr ?_
  rw [Subgroup.mem_subgroupOf]
  -- `y * (c ^ k)⁻¹ ∈ U` is normalised by `y⁻¹`
  have hnorm : (C.P.U.subgroupOf C.P.H0).Normal := C.U_normal
  have hyinv : (y : G)⁻¹ ∈ C.P.H0 := C.P.H0.inv_mem y.2
  have hconj := hnorm.conj_mem
    (⟨(y : G) * (c ^ k)⁻¹, C.P.U_le_H0 hk⟩ : ↥C.P.H0)
    (by rw [Subgroup.mem_subgroupOf]; exact hk)
    (⟨(y : G)⁻¹, hyinv⟩ : ↥C.P.H0)
  rw [Subgroup.mem_subgroupOf] at hconj
  simpa [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using hconj

/-- `H₀/U` is commutative (it is cyclic). -/
private theorem s02_quot_comm {G : Type} [Group G] [Finite G] (C : Sec2Ctx G)
    (x y : quotGroup C.P) : x * y = y * x := by
  haveI : IsCyclic (quotGroup C.P) := s02_quot_isCyclic C
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := quotGroup C.P)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg y)
  rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]

/-- **A linear character of `H₀/U` with value `-1` at the class of `t`.**

Since `t ∉ U` the class `tU ∈ H₀/U` is non-trivial, and `ℂ` has enough roots of unity, so
duality of finite abelian groups gives `β : H₀/U →* ℂˣ` with `β (tU) ≠ 1`; as `tU` is an
involution, `β (tU)² = 1` and therefore `β (tU) = -1`, i.e. `lamCF C β C.t = -1`.

This is Bender–Glauberman's character `λ₁` of the proof of Lemma 1.7(iii) (the reflection of
`H₀` at `t` killing `U`), and the character used in Lemma 2.1 to split `Λν` into the halves
`{χ : χ(t) = χ(1)}` and its complement. -/
theorem s02_exists_lamCF_apply_t_eq_neg_one {G : Type} [Group G] [Finite G] (C : Sec2Ctx G) :
    ∃ β : quotGroup C.P →* ℂˣ, lamCF C β C.t = -1 := by
  -- the cyclic quotient is commutative; install that commutativity as the `CommGroup`
  -- structure through the instance-reducible `IsMulCommutative.instCommGroup`, so that the
  -- homomorphisms obtained below have `Work.BG.lamCF`'s (canonical) `MonoidHom` type
  haveI : IsMulCommutative (quotGroup C.P) :=
    IsMulCommutative.of_comm (fun x y => s02_quot_comm C x y)
  letI : CommGroup (quotGroup C.P) := IsMulCommutative.instCommGroup
  -- `tU ≠ 1`
  have hne : (quotMk C.P C.t : quotGroup C.P) ≠ 1 := by
    intro h
    exact C.t_not_mem_U ((QuotientGroup.eq_one_iff (N := C.P.U.subgroupOf C.P.H0) C.t).mp h)
  -- duality separates points
  obtain ⟨β, hβ⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (quotGroup C.P) ℂ hne
  -- `β (tU)² = 1` as `tU` is an involution, and `β (tU) ≠ 1`, so `β (tU) = -1`
  have hsq : β (quotMk C.P C.t) ^ 2 = 1 := by
    rw [← map_pow, show (quotMk C.P C.t : quotGroup C.P) ^ 2 = 1 from by
      rw [← map_pow, C.t_sq, map_one], map_one]
  have hval : ((β (quotMk C.P C.t) : ℂˣ) : ℂ) = -1 := by
    have h2 : (((β (quotMk C.P C.t) : ℂˣ) : ℂ)) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hsq]; rfl
    have hfac : (((β (quotMk C.P C.t) : ℂˣ) : ℂ) - 1) *
        (((β (quotMk C.P C.t) : ℂˣ) : ℂ) + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (sub_eq_zero.mp h) (fun hh => hβ (Units.ext hh))
    · exact add_eq_zero_iff_eq_neg.mp h
  refine ⟨β, ?_⟩
  rw [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply]
  exact hval

theorem s02_lamOrbit_ne {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [CommGroup (Work.BG.quotGroup C.P)]
    (ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ)
    (hν : OddOrder.RepresentationTheory.IsIrreducibleCharacter ν) :
    ∃ β : Work.BG.quotGroup C.P →* ℂˣ,
      Work.BG.lamCF C β * ν ≠ ν := by
  -- a member of `Λ` which takes the value `-1` at the central involution `t`
  obtain ⟨β, hβ⟩ := s02_exists_lamCF_apply_t_eq_neg_one C
  refine ⟨β, ?_⟩
  intro hfix
  -- evaluating the fixed-point equation at `t` gives `-ν t = ν t`, i.e. `ν t = 0`
  have hval : (lamCF C β * ν) C.t = ν C.t :=
    congrArg (fun f : ClassFunction ↥C.P.H0 ℂ => f C.t) hfix
  rw [ClassFunction.mul_apply, hβ] at hval
  have hzero : ν C.t = 0 := by
    have h2 : (2 : ℂ) * ν C.t = 0 := by linear_combination -hval
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  -- but `ν t = ±ν 1 ≠ 0` (Schur at the central involution `t`)
  obtain ⟨hvt, h1ne⟩ := centralValue C ν hν
  rcases hvt with h | h
  · rw [hzero] at h
    exact h1ne h.symm
  · rw [hzero] at h
    exact h1ne (neg_eq_zero.mp h.symm)

end Work.BG
