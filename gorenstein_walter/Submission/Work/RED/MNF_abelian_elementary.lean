import Mathlib
import Submission.Work.RED.Basic

/-!
# RED: an abelian minimal normal subgroup is elementary abelian

Field `abelian_elementary` of `Work.RED.GW2.MinimalNormalFactsProp`.

If `N` is a minimal normal subgroup of a finite group `G` and `N` is abelian, then `N` is
elementary abelian: there is a prime `p` with `x ^ p = 1` for every `x ∈ N`.

Proof.  Pick a prime `p` dividing `|N|` (which exists since `N ≠ ⊥`).  Since `N` is abelian,
the `p`-torsion of `N`,
`M = { x ∈ N | x ^ p = 1 }`,
is a subgroup of `G`; it is contained in `N`, and it is normal in `G` because conjugation
preserves `p`-th powers and `N` is normal.  It is nontrivial by Cauchy's theorem applied in
`N`.  Minimality of `N` forces `N ≤ M`, so `M = N`, i.e. every element of `N` has `p`-th
power `1`.
-/

namespace Work.RED

open Subgroup

/-- An abelian minimal normal subgroup is elementary abelian. -/
theorem MNF_abelian_elementary (G : Type*) [Group G] [Finite G] (N : Subgroup G)
    (hN : Work.RED.GW2.IsMinimalNormal N) (hab : IsMulCommutative N) :
    ∃ p : ℕ, p.Prime ∧ ∀ x ∈ N, x ^ p = 1 := by
  classical
  -- `N` is nontrivial, so `|N| > 1` and some prime divides `|N|`.
  have hne : N ≠ ⊥ := hN.ne_bot
  have hcard : 1 < Nat.card ↥N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥N) (by omega)
  have hp' : Fact p.Prime := ⟨hp⟩
  -- Cauchy's theorem in `N` gives an element of order `p`.
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hpdvd
  -- The `p`-torsion subgroup of `N`, viewed in `G`.
  let M : Subgroup G :=
    { carrier := {x | x ∈ N ∧ x ^ p = 1}
      mul_mem' := by
        rintro a b ⟨ha, hap⟩ ⟨hb, hbp⟩
        exact ⟨N.mul_mem ha hb,
          by rw [Commute.mul_pow (setLike_mul_comm ha hb) p, hap, hbp, one_mul]⟩
      one_mem' := ⟨N.one_mem, one_pow p⟩
      inv_mem' := by
        rintro a ⟨ha, hap⟩
        exact ⟨N.inv_mem ha, by rw [inv_pow, hap, inv_one]⟩ }
  have hMle : M ≤ N := fun x hx => hx.1
  -- `M` is normal in `G`: conjugation preserves `p`-th powers, and `N ⊴ G`.
  have hMnorm : M.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨hnN, hnp⟩ := hn
    refine ⟨hN.normal.conj_mem n hnN g, ?_⟩
    have hconj : (g * n * g⁻¹) = (MulAut.conj g) n := (MulAut.conj_apply g n).symm
    rw [hconj, ← map_pow, hnp, map_one]
  -- `M` is nontrivial: the Cauchy element `y` lies in it.
  have hyM : (y : G) ∈ M := by
    refine ⟨y.2, ?_⟩
    have h1 := pow_orderOf_eq_one y
    rw [hyord] at h1
    simpa using congrArg Subtype.val h1
  have hMne : M ≠ ⊥ := by
    intro hbot
    have hy1 : (y : G) = 1 := by
      have h2 : (y : G) ∈ (⊥ : Subgroup G) := hbot ▸ hyM
      rwa [Subgroup.mem_bot] at h2
    have h3 : y = 1 := Subtype.ext hy1
    rw [h3, orderOf_one] at hyord
    exact hp.ne_one hyord.symm
  -- Minimality of `N` forces `N ≤ M`, hence `N = M`.
  have hNM : N ≤ M := hN.2.2 M hMnorm hMne hMle
  exact ⟨p, hp, fun x hx => (hNM hx).2⟩

end Work.RED
