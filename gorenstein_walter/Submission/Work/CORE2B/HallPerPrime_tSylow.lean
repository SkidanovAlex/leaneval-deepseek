import Mathlib
import Submission.Work.CORE2B.HallPerPrime_aux

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# AREA CORE2B — the `t`-invariant Sylow `p`-subgroup step of Bender's Theorem 2.10

Bender (J. Algebra 70 (1981) 216–228), proof of Theorem 2.10, p. 222:

> With `p` a prime, assume `1 ≠ X := C_{O_p(U)}(s) ≠ O_p(U)`.  By 1.1(ii), some `t`-invariant
> `S_p`-subgroup `P` of `O(C_G(s))` contains `X`.

Here `X = O_p(U) ∩ C_G(s)` lies in the odd core `O(C_G(s))` of `C_G(s)` (that containment is the
hypothesis `hX`; it is supplied by `HallPerPrime_Xodd`).  The task of this file is the **existence
of `P`**: a `p`-subgroup of `O(C_G(s))` containing `X`, of `p`-power index in `O(C_G(s))`
(i.e. a Sylow `p`-subgroup there), and invariant under conjugation by `B.t`.

The argument is Bender's 1.1(ii) (`T.c11ii`), applied with

* the acting group `P₀ = ⟨t⟩` — a `2`-group, because `t` is an involution (`B.t_order`);
* the acted-on group `K = O(C_G(s))` — of **odd** order, so `2` is coprime to `|K|`;
* the `p`-subgroup `X ≤ K` (that is `hX`), invariant under `P₀`.

Two facts make the hypotheses of 1.1(ii) available:

* `t` commutes with every element of `U` (`t_commutes_U`), so conjugation by `t` fixes `O_p(U)`
  pointwise; and `t` commutes with `s` (`t_central_in_S`, `s ∈ S`, `t` central in `S`), so it
  preserves `C_G(s)`.  Hence `t` normalises `X`.
* `t ∈ C_G(s)`, and `C_G(s)` normalises its own characteristic odd core `O(C_G(s))`; hence `t`
  normalises `K`.

1.1(ii) then returns a `p`-subgroup `P` with `X ≤ P ≤ K`, `⟨t⟩ ≤ N_G(P)` and `p ∤ [K : P]`, which
is exactly the assertion.
-/

/-- **The `t`-invariant Sylow `p`-subgroup step of Bender's Theorem 2.10.**

Let `B` be Bender's configuration, `s ∈ S − S₀` and `p` a prime; if the `p`-part `X` of `U`
centralised by `s` lies in the odd core `O(C_G(s))` of `C_G(s)`, then `X` is contained in a
`p`-subgroup `P ≤ O(C_G(s))` of `p`-power index there which is invariant under conjugation by
the central involution `t ∈ S`. -/
theorem HallPerPrime_tSylow (T : Work.GW2.LocalToolkit) (G : Type) [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (s : G) (hs : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0)
    (p : ℕ) (hp : Nat.Prime p)
    (hX : Work.GW2.pCoreIn p B.U ⊓ Subgroup.centralizer ({s} : Set G) ≤
      Work.GW2.oddCoreIn (Subgroup.centralizer ({s} : Set G))) :
    ∃ P : Subgroup G,
      (Work.GW2.pCoreIn p B.U ⊓ Subgroup.centralizer ({s} : Set G) ≤ P) ∧
      P ≤ Work.GW2.oddCoreIn (Subgroup.centralizer ({s} : Set G)) ∧
      IsPGroup p P ∧
      ¬ p ∣ P.relIndex (Work.GW2.oddCoreIn (Subgroup.centralizer ({s} : Set G))) ∧
      P.map (MulAut.conj B.t).toMonoidHom = P := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- notation: `C = C_G(s)`, `K = O(C_G(s))`, `X = O_p(U) ∩ C_G(s)`
  let C : Subgroup G := Subgroup.centralizer ({s} : Set G)
  let K : Subgroup G := Work.GW2.oddCoreIn C
  let X : Subgroup G := Work.GW2.pCoreIn p B.U ⊓ Subgroup.centralizer ({s} : Set G)
  -- `t` is an involution
  have hBt2 : B.t * B.t = 1 := by
    have h := pow_orderOf_eq_one B.t
    rwa [B.t_order, pow_two] at h
  have hBti : B.t⁻¹ = B.t := inv_eq_of_mul_eq_one_right hBt2
  -- `t ∈ C_G(s)`
  have htC : B.t ∈ C := by
    show B.t ∈ Subgroup.centralizer ({s} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact t_central_in_S B s hs
  -- `O_p(U)` is a `p`-group
  have hPpU : IsPGroup p (Work.GW2.pCoreIn p B.U) := by
    have h1 : IsPGroup p ↥(Work.GW2.pCore p ↥(B.U)) := by
      rw [hall_pCore_eq_opCore]
      exact OddOrder.Isaacs.Ch01.opCore_isPGroup p ↥(B.U)
    rw [Work.GW2.pCoreIn]
    exact h1.map B.U.subtype
  have hXpg : IsPGroup p X := hPpU.to_le inf_le_left
  have hXleK : X ≤ K := hX
  -- conjugation by `t` fixes `O_p(U)` pointwise (as `t` commutes with `U`)
  have hfixX : ∀ y ∈ X, B.t * y * B.t⁻¹ = y := by
    intro y hy
    have hyU : y ∈ B.U := (in_le_self B.U p ∅).2.1 hy.1
    have htu : B.t * y = y * B.t := t_commutes_U B y hyU
    calc B.t * y * B.t⁻¹ = (B.t * y) * B.t⁻¹ := rfl
      _ = (y * B.t) * B.t⁻¹ := by rw [htu]
      _ = y := by rw [mul_assoc, mul_inv_cancel, mul_one]
  -- hence `t` normalises `X`
  have hmemX_iff : ∀ y : G, y ∈ X ↔ B.t * y * B.t⁻¹ ∈ X := by
    intro y
    constructor
    · intro hy; rw [hfixX y hy]; exact hy
    · intro hy
      have h2 : B.t * (B.t * y * B.t⁻¹) * B.t⁻¹ = B.t * y * B.t⁻¹ := hfixX _ hy
      have h3 : B.t * (B.t * y * B.t⁻¹) * B.t⁻¹ = y := by
        rw [hBti]
        calc B.t * (B.t * y * B.t) * B.t
            = (B.t * B.t) * y * (B.t * B.t) := by group
          _ = y := by rw [hBt2]; simp
      have hy' : y = B.t * y * B.t⁻¹ := h3.symm.trans h2
      rw [hy']; exact hy
  have htN : B.t ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    exact hmemX_iff
  have hzpX : Subgroup.zpowers B.t ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.zpowers_le.mpr htN
  -- `C_G(s)` normalises its characteristic odd core `K = O(C_G(s))`, and `t ∈ C_G(s)`
  have hC_NK : C ≤ Subgroup.normalizer (K : Set G) := by
    show C ≤ Subgroup.normalizer (((Work.GW2.oddCore ↥C).map C.subtype : Subgroup G) : Set G)
    exact le_normalizer_map_subtype_local C (Work.GW2.oddCore ↥C) (Work.GW2.oddCore_normal ↥C)
  have hzpK : Subgroup.zpowers B.t ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.zpowers_le.mpr (hC_NK htC)
  -- `K`, being an odd core, has odd order
  have hKodd : Odd (Nat.card K) := by
    show Odd (Nat.card ↥((Work.GW2.oddCore ↥C).map C.subtype))
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact oddCore_odd (G := ↥C)
  have hcop : Nat.Coprime 2 (Nat.card K) :=
    Nat.prime_two.coprime_iff_not_dvd.mpr
      (fun h => (Nat.not_even_iff_odd.mpr hKodd) (even_iff_two_dvd.mpr h))
  -- the acting group `⟨t⟩` is a `2`-group
  have h2pg : IsPGroup 2 (Subgroup.zpowers B.t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, B.t_order, pow_one]
  -- Bender 1.1(ii) with `P₀ = ⟨t⟩`, `K = O(C_G(s))`, `q = p`, `Q = X`
  obtain ⟨hmain, _⟩ :=
    T.c11ii G 2 (Subgroup.zpowers B.t) K h2pg hcop hzpK p X hXleK hXpg hzpX
  obtain ⟨R, hXR, hRK, hNR, hRpg, hRrel⟩ := hmain
  refine ⟨R, hXR, hRK, hRpg, hRrel, ?_⟩
  -- `⟨t⟩ ≤ N_G(R)` gives `t`-invariance of `R`
  have htR : B.t ∈ Subgroup.normalizer (R : Set G) := hNR (Subgroup.mem_zpowers B.t)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp htR

end Work.CORE2B
