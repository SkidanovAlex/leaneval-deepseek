import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1aFrattiniConj
import Submission.Work.CORE3.Case1aFrattiniApi

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- Design pass 13 §1, D1 (Bender 1981 §3, p. 222): the conjugating element of
`Work.CORE3.Case1aFrattiniConj` can be chosen inside `N_G(V₁)`.  It is produced there as
`c * n₀` with `n₀ ∈ N_G(V₁)` (`Work.CORE3.FusionNormalizerV1`) and `c ∈ C_G(V₁) ⊆ N_G(V₁)`, so
copying that proof and keeping the extra membership gives the statement. -/
theorem Case1aFrattiniConjV (G : Type) [Group G] [Finite G] (T : LocalToolkit) (hBc : BenderCtx G)
    (B : BenderSetup G) (D : Case1aData B) (P2 : Subgroup G) (hsyl : P1SylowIn B D P2) :
    ∃ n ∈ normalizer ((pCoreIn D.p B.U ⊔ P2 : Subgroup G) : Set G),
      n ∈ normalizer ((V1 B D : Subgroup G) : Set G) ∧ n * B.t * n⁻¹ = D.t1 := by
  classical
  obtain ⟨hP1le, hP1grp, hP1rel⟩ := hsyl
  obtain ⟨n0, hn0N, hn0t⟩ := FusionNormalizerV1 G T hBc B D
  set P1 : Subgroup G := (pCoreIn D.p B.U ⊔ P2 : Subgroup G) with hP1def
  set H : Subgroup G := Subgroup.centralizer ((V1 B D : Subgroup G) : Set G) with hHdef
  have hP1leH : P1 ≤ H := hP1le
  -- the conjugate `Q = n₀ P₁ n₀⁻¹` is again a Sylow `p`-subgroup of `C_G(V₁)`
  set Q : Subgroup G := P1.map (MulAut.conj n0).toMonoidHom with hQdef
  have hQH : Q ≤ H := map_conj_le_centralizer (V1 B D) P1 n0 hn0N hP1leH
  have hQgrp : IsPGroup D.p Q := hP1grp.map (MulAut.conj n0).toMonoidHom
  have hcard : Nat.card ↥P1 = Nat.card ↥Q := by
    have h := Subgroup.card_map_of_injective (K := P1) (f := (MulAut.conj n0).toMonoidHom)
      (MulAut.conj n0).injective
    exact h.symm
  obtain ⟨c, hcH, hcQ⟩ :=
    ConjSylowOfSubgroup D.p D.hp H P1 Q hP1leH hQH hP1grp hQgrp hcard hP1rel
  -- `c ∈ C_G(V₁) ⊆ N_G(V₁)`, hence `c * n₀` stays inside `N_G(V₁)`
  have hcN : c ∈ Subgroup.normalizer ((V1 B D : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ hcH
  have hfix : ∀ x : G, (c * n0) * x * (c * n0)⁻¹ = c * (n0 * x * n0⁻¹) * c⁻¹ := by
    intro x; group
  have hct : c * D.t1 * c⁻¹ = D.t1 :=
    conj_eq_self_of_mem_centralizer (V1 B D) hcH
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t1))
  refine ⟨c * n0, ?_, ?_, ?_⟩
  · -- `c * n₀` normalizes `P₁`
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hfix x]
      refine (hcQ _).mp ?_
      rw [hQdef]
      change (MulAut.conj n0) x ∈ P1.map (MulAut.conj n0).toMonoidHom
      exact Subgroup.mem_map_of_mem (MulAut.conj n0).toMonoidHom hx
    · intro hx
      have h2 : c * (n0 * x * n0⁻¹) * c⁻¹ ∈ P1 := by rw [← hfix x]; exact hx
      have h1 : n0 * x * n0⁻¹ ∈ Q := (hcQ _).mpr h2
      rw [hQdef, mem_map_conj_iff] at h1
      have hconj : n0⁻¹ * (n0 * x * n0⁻¹) * n0 = x := by group
      rwa [hconj] at h1
  · -- `c * n₀` normalizes `V₁`
    exact (Subgroup.normalizer _).mul_mem hcN hn0N
  · calc (c * n0) * B.t * (c * n0)⁻¹ = c * (n0 * B.t * n0⁻¹) * c⁻¹ := hfix B.t
      _ = c * D.t1 * c⁻¹ := by rw [hn0t]
      _ = D.t1 := hct

end Work.CORE3
