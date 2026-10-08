import Mathlib
import Submission.Work.BSW.Cases.K2NCS.Setup

namespace Work.BSW.Cases.K2NCS

open Subgroup Work.GW2

/-- **Key step of the `|K| = 2` dichotomy.**  An element `x ∉ C_G(t)` cannot centralize an
involution `w ∈ C_G(t)`.

Indeed `C_G(t)` is abelian of order `4` (`Work.BSW.Api.card_centralizer_of_card_K_two`), so it is
contained in `C_G(w)`; and every involution `w` has `|C_G(w)| = 4`
(`Work.BSW.Cases.bswK2Involution`).  Hence `C_G(w) = C_G(t)`, which would force `x ∈ C_G(t)`. -/
theorem not_centralizes_of_mem_centralizer {G : Type} [Group G] [Finite G] {t s : G}
    {K : Subgroup G} (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2)
    {x w : G} (hw : w ∈ Subgroup.centralizer ({t} : Set G)) (hw2 : orderOf w = 2)
    (hxC : x ∉ Subgroup.centralizer ({t} : Set G)) (hxw : x * w = w * x) : False := by
  have hCcard : Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 4 :=
    Work.BSW.Api.card_centralizer_of_card_K_two h hk
  have hwcard : Nat.card ↥(Subgroup.centralizer ({w} : Set G)) = 4 :=
    (Work.BSW.Cases.bswK2Involution h hk hw2).1
  have hxmem : x ∈ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxw
  have hle : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.centralizer ({w} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_comm_of_mem_centralizer h hk ha hw
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hCcard, hwcard])
  exact hxC (by rw [heq]; exact hxmem)

/-- In the `|K| = 2` case, an element of `N_G(C_G(t))` outside `C_G(t)` conjugates `t` to `s` or to
`t * s`, and correspondingly `s` to `t * s` or `t` (i.e. it permutes the three involutions of the
Klein four-group `C_G(t)` by a 3-cycle).

Here `x ∈ N_G(C_G(t))` acts on `C_G(t) = {1, t, s, ts}`; since `x ∉ C_G(t) = C_G(C_G(t))` this
action is nontrivial.  We show it cannot be a transposition: it cannot fix `t` (that is exactly
`x ∈ C_G(t)`), and if it fixed `s` or `t * s` then `x` would centralize that involution of
`C_G(t)`, contradicting `not_centralizes_of_mem_centralizer`.  Hence it fixes none of the three
involutions, i.e. it is a 3-cycle, and `xtx⁻¹ ∈ {s, ts}` determines which one. -/
theorem mul_conj_dichotomy {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) {x : G}
    (hxN : x ∈ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G))
    (hxC : x ∉ Subgroup.centralizer ({t} : Set G)) :
    (x * t * x⁻¹ = s ∧ x * s * x⁻¹ = t * s) ∨
      (x * t * x⁻¹ = t * s ∧ x * s * x⁻¹ = t) := by
  have hst : s ≠ t := fun h1 => Work.BSW.s_notMem_K h (h1 ▸ Work.BSW.t_mem_K h)
  -- `x` normalizes `C_G(t)`, so it conjugates `t` and `s` into `C_G(t)`.
  have hxt := (Subgroup.mem_normalizer_iff.mp hxN t).mp (Work.BSW.t_mem_centralizer_t h)
  have hxs := (Subgroup.mem_normalizer_iff.mp hxN s).mp (Work.BSW.s_mem_centralizer_t h)
  -- `x t x⁻¹` and `x s x⁻¹` are involutions (conjugates of `t` and `s`).
  have hu2 : orderOf (x * t * x⁻¹) = 2 := by
    have he : x * t * x⁻¹ = MulAut.conj x t := (MulAut.conj_apply x t).symm
    rw [he, MulEquiv.orderOf_eq (MulAut.conj x) t, Work.BSW.orderOf_t h]
  have hv2 : orderOf (x * s * x⁻¹) = 2 := by
    have he : x * s * x⁻¹ = MulAut.conj x s := (MulAut.conj_apply x s).symm
    rw [he, MulEquiv.orderOf_eq (MulAut.conj x) s, Work.BSW.orderOf_s h]
  have hu1 : x * t * x⁻¹ ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hu2; exact absurd hu2 (by norm_num)
  have hv1 : x * s * x⁻¹ ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hv2; exact absurd hv2 (by norm_num)
  -- `x` does not fix `t`.
  have hut : x * t * x⁻¹ ≠ t := by
    intro h1
    apply hxC
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc x * t = (x * t * x⁻¹) * x := by group
        _ = t * x := by rw [h1])
  -- `x` conjugates `t` and `s` to distinct involutions.
  have huv : x * t * x⁻¹ ≠ x * s * x⁻¹ := by
    intro h1
    have h2 : MulAut.conj x t = MulAut.conj x s := by
      rw [MulAut.conj_apply, MulAut.conj_apply]; exact h1
    have hts : t = s := (MulAut.conj x).injective h2
    exact hst hts.symm
  -- enumerate the possible values of `x t x⁻¹` and `x s x⁻¹` in `C_G(t) = {1,t,s,ts}`.
  have hu : x * t * x⁻¹ = s ∨ x * t * x⁻¹ = t * s := by
    rcases (mem_centralizer_iff_one_or h hk (x * t * x⁻¹)).mp hxt with h1 | h1 | h1 | h1
    · exact absurd h1 hu1
    · exact absurd h1 hut
    · exact Or.inl h1
    · exact Or.inr h1
  have hv : x * s * x⁻¹ = t ∨ x * s * x⁻¹ = s ∨ x * s * x⁻¹ = t * s := by
    rcases (mem_centralizer_iff_one_or h hk (x * s * x⁻¹)).mp hxs with h1 | h1 | h1 | h1
    · exact absurd h1 hv1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  rcases hu with hu | hu
  · -- `x t x⁻¹ = s`
    rcases hv with hv | hv | hv
    · -- `x s x⁻¹ = t`: then `x` fixes `t * s`, impossible.
      exfalso
      have hwC : t * s ∈ Subgroup.centralizer ({t} : Set G) :=
        Subgroup.mul_mem _ (Work.BSW.t_mem_centralizer_t h) (Work.BSW.s_mem_centralizer_t h)
      have hw2 : orderOf (t * s) = 2 :=
        orderOf_eq_two_of_mem_centralizer h hk hwC (by
          intro h1
          have h2 : s = t := by
            have hc := congrArg (fun z => t * z) h1
            rw [mul_one, ← mul_assoc, Work.BSW.t_mul_self h, one_mul] at hc
            exact hc
          exact hst h2)
      have hcomm : x * (t * s) = (t * s) * x := by
        calc x * (t * s) = (x * t * x⁻¹) * (x * s * x⁻¹) * x := by group
          _ = s * t * x := by rw [hu, hv]
          _ = (t * s) * x := by rw [Work.BSW.s_mul_t_eq_t_mul_s h]
      exact not_centralizes_of_mem_centralizer h hk hwC hw2 hxC hcomm
    · -- `x s x⁻¹ = s = x t x⁻¹`, contradicting injectivity of conjugation.
      exfalso; exact huv (hu.trans hv.symm)
    · -- `x t x⁻¹ = s` and `x s x⁻¹ = t * s`: the first alternative.
      exact Or.inl ⟨hu, hv⟩
  · -- `x t x⁻¹ = t * s`
    rcases hv with hv | hv | hv
    · -- `x s x⁻¹ = t`: the second alternative.
      exact Or.inr ⟨hu, hv⟩
    · -- `x s x⁻¹ = s`: then `x` fixes `s`, impossible.
      exfalso
      have hcomm : x * s = s * x := by
        calc x * s = (x * s * x⁻¹) * x := by group
          _ = s * x := by rw [hv]
      exact not_centralizes_of_mem_centralizer h hk (Work.BSW.s_mem_centralizer_t h)
        (Work.BSW.orderOf_s h) hxC hcomm
    · -- `x s x⁻¹ = t * s = x t x⁻¹`, contradictory.
      exfalso; exact huv (hu.trans hv.symm)

end Work.BSW.Cases.K2NCS
