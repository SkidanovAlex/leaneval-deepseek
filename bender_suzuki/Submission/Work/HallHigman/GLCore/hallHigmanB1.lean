import Mathlib
import Submission.Work.HallHigman.HallHigmanB
import Submission.Work.HallHigman.Basic
import Submission.Work.HallHigman.GLCore.abelian_case
import Submission.Work.HallHigman.GLCore.centralizer_opCore_le
import Submission.Work.HallHigman.GLCore.glCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.HallHigman.GLCore

/-- In a ring of characteristic `p`, an element `T` with `(T - 1) ^ (p - 1) = 0` satisfies
`T ^ p = 1`.  Indeed `(T - 1) ^ p = T ^ p - 1` (freshman's dream for the commuting pair
`T`, `1`), and `(T - 1) ^ p = (T - 1) ^ (p - 1) * (T - 1) = 0`. -/
lemma pow_eq_one_of_sub_one_pow_pred_eq_zero {R : Type*} [Ring R] {p : ℕ} [Fact p.Prime]
    [CharP R p] {T : R} (h : (T - 1) ^ (p - 1) = 0) : T ^ p = 1 := by
  have hp1 : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
  have hpow : (T - 1) ^ p = T ^ p - 1 := by
    simpa using sub_pow_char_of_commute (R := R) p (Commute.one_right T)
  have h0 : (T - 1) ^ p = 0 := by
    rw [show p = (p - 1) + 1 from (Nat.sub_add_cancel hp1).symm, pow_succ, h, zero_mul]
  have hT : T ^ p - 1 = 0 := by rw [← hpow, h0]
  rwa [sub_eq_zero] at hT

/-- **L18 of the GL-core design** (§2.1/§3 of `NOTES_LEAD_ft_hallhigman.md`):  **Hall--Higman
Theorem B in the order-`p` odd order form** (B1), i.e. `Work.HallHigman.HallHigmanB1`.

Proof: let `G` be `p`-solvable of odd order, `V` a faithful `K[G]`-module with `O_p(G) = 1`, and
`x ≠ 1` with `(V.ρ x - 1) ^ (p - 1) = 0`; derive `x ^ p = 1` (from `(X - 1) ^ p = X ^ p - 1`), so
`x` is a nontrivial `p`-element and hence `x ∉ O_{p'}(G)`.  By L15
(`centralizer_opCore_le`), `C_G(O_{p'}(G)) ≤ O_{p'}(G)`, so `x` does not centralise `O_{p'}(G)`;
therefore `X := ρ x` does not commute with `𝒬 := (O_{p'}(G)).map V.ρ.toHomUnits` (using
faithfulness), and `CoreHyp p 𝒬 X` holds: `𝒬` is finite, of odd order and of order prime to `p`,
`X ^ p = 1`, `X` normalises `𝒬` (as `O_{p'}(G)` is normal).  The GL-core (L17, `glCore`) then
gives the contradiction. -/
theorem hallHigmanB1 {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (K : Type*) [Field K] [CharP K p] :
    Work.HallHigman.HallHigmanB1 K p := by
  intro G _ _ hps hodd V hfaith hOp x hx1 hzero
  have hpprime : p.Prime := Fact.out
  by_cases hV : Nontrivial V
  · haveI : Nontrivial V := hV
    -- the ring of endomorphisms of a nontrivial module in characteristic `p` has characteristic `p`
    haveI hcharEnd : CharP (Module.End K V) p := charP_moduleEnd
    -- step 1: `(ρx - 1) ^ (p - 1) = 0` forces `x ^ p = 1`
    have hxpow : x ^ p = 1 := by
      have h1 : (V.ρ x) ^ p = 1 := pow_eq_one_of_sub_one_pow_pred_eq_zero hzero
      exact hfaith (by rw [map_pow, h1, map_one])
    have hxord : orderOf x = p := orderOf_eq_prime hxpow hx1
    -- step 2: a nontrivial `p`-element does not lie in `O_{p'}(G)`
    have hxnot : x ∉ Work.HallHigman.opCore p G := by
      intro hxmem
      have hdvd : p ∣ Nat.card ↥(Work.HallHigman.opCore p G) := by
        have h := Subgroup.orderOf_dvd_natCard (Work.HallHigman.opCore p G) hxmem
        rwa [hxord] at h
      exact (Work.HallHigman.piCore_isPiNat (π := (· ≠ p)) (G := G)) p hpprime hdvd rfl
    -- step 3: hence `x` does not centralise `O_{p'}(G)`, by L15
    have hcen := Work.HallHigman.GLCore.centralizer_opCore_le (G := G) (p := p) hps hOp
    have hxnc : x ∉ Subgroup.centralizer (Work.HallHigman.opCore p G : Set G) :=
      fun hxmem => hxnot (hcen hxmem)
    have hnc : ∃ y ∈ Work.HallHigman.opCore p G, y * x ≠ x * y := by
      by_contra hcon
      push Not at hcon
      exact hxnc (Subgroup.mem_centralizer_iff.mpr hcon)
    -- step 4: transport to `GL(V)`
    have hQnorm : (Work.HallHigman.opCore p G).Normal := Work.HallHigman.opCore_normal
    have hinj : Function.Injective V.ρ.toHomUnits := by
      intro a b hab
      apply hfaith
      have h := congrArg (fun z : (Module.End K V)ˣ => (z : Module.End K V)) hab
      simpa using h
    have hcardQ : Nat.card ↥((Work.HallHigman.opCore p G).map V.ρ.toHomUnits)
        = Nat.card ↥(Work.HallHigman.opCore p G) := Subgroup.card_map_of_injective hinj
    have hcore : Work.HallHigman.CoreHyp p ((Work.HallHigman.opCore p G).map V.ρ.toHomUnits)
        (V.ρ.toHomUnits x) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact Finite.of_surjective
          (Subgroup.equivMapOfInjective (Work.HallHigman.opCore p G) V.ρ.toHomUnits hinj)
          (EquivLike.surjective _)
      · rw [hcardQ]
        refine Odd.of_dvd_nat hodd ?_
        rw [← Subgroup.card_top (G := G)]
        exact Subgroup.card_dvd_of_le le_top
      · rw [hcardQ]
        intro hpd
        exact (Work.HallHigman.piCore_isPiNat (π := (· ≠ p)) (G := G)) p hpprime hpd rfl
      · rw [← map_pow, hxpow, map_one]
      · intro a ha
        obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha
        have heq : (V.ρ.toHomUnits x) * (V.ρ.toHomUnits g) * (V.ρ.toHomUnits x)⁻¹
            = V.ρ.toHomUnits (x * g * x⁻¹) := by
          simp only [map_mul, map_inv]
        rw [heq]
        exact Subgroup.mem_map_of_mem V.ρ.toHomUnits (hQnorm.conj_mem g hg x)
      · obtain ⟨y, hy, hne⟩ := hnc
        refine ⟨V.ρ.toHomUnits y, ?_, ?_⟩
        · exact Subgroup.mem_map_of_mem V.ρ.toHomUnits hy
        · intro hcontra
          refine hne (hinj ?_)
          rw [map_mul, map_mul]
          exact hcontra
    -- step 5: the GL-core gives the contradiction
    exact (Work.HallHigman.GLCore.glCore (K := K) (V := V) (p := p) hp hcore) hzero
  · -- a trivial module cannot carry a faithful representation of a nontrivial group
    exfalso
    haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    exact hx1 (hfaith (LinearMap.ext fun v => Subsingleton.elim _ _))

end Work.HallHigman.GLCore
