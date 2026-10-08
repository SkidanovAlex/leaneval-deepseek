import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1aFrattini
import Submission.Work.CORE3.Case1aAbelian
import Submission.Work.CORE3.Case1aSetup
import Submission.Work.CORE3.Case1aP_ne_bot

/-!
# CORE3 / A7V18: `P₀ = O_p(U) ∩ M ≠ 1` (Bender 1981, §3, p. 222)

Deliverable `Work.CORE3.A7V18.P0ne`.

Bender 1981, *Finite groups with dihedral Sylow 2-subgroups*, J. Algebra 70, §3, p. 222:

> Take a maximal subgroup `M` of `G` containing `N_G(P₂)`.  Then `S ≤ M` and
> `P₀ := P ∩ M ≠ 1`.

With `Case1 B`, `Ĥ = H`, `D : Case1aData B`, `P = O_p(U) = pCoreIn D.p B.U` and
`P₂ ∈ Syl_p(C_U(S))`, the second claim has a one-line proof that uses *exactly* the
hypothesis `N_G(P₂) ≤ M` (which is why Bender takes `M ⊇ N_G(P₂)` rather than
`M ⊇ N_G(P₁)`):

* `P₂ ≤ B.U ≤ N_G(P)` (as `O_p(U) ⊴ U`), so the `p`-group `P₂` acts on the nontrivial
  `p`-group `P = O_p(U) ≠ 1` (see `Work.CORE3.Case1aP_ne_bot`);
* a `p`-group acting on a nontrivial `p`-group has a nontrivial fixed point: the conjugation
  action of `P₂` on the set `P` satisfies `|P^{P₂}| ≡ |P| ≡ 0 (mod p)` and `1` is fixed, so
  there is `x ∈ P`, `x ≠ 1`, with `x ∈ C_G(P₂)`.  This is the lemma
  `exists_ne_one_mem_centralizer_of_isPGroup` below (Mathlib's
  `IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point` for the conjugation action);
* `C_G(P₂) ≤ N_G(P₂) ≤ M`, hence `x ∈ P ∩ M` and `P ∩ M ≠ ⊥`.
-/

set_option linter.style.haveILetI false
set_option linter.dupNamespace false

namespace Work.CORE3.A7V18

open Subgroup

/-- **Nontrivial fixed points of a `p`-group acting on a `p`-group.**  If `A ≤ N_G(P)` with `A`
and `P` finite `p`-groups and `P ≠ ⊥`, then some nontrivial element of `P` is centralized by
`A`.

This is the orbit-counting fact for the conjugation action of the `p`-group `A` on the set `P`:
`|P^A| ≡ |P| ≡ 0 (mod p)`, and `1 ∈ P^A`, so `|P^A| ≥ p > 1`. -/
theorem exists_ne_one_mem_centralizer_of_isPGroup {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A P : Subgroup G} (hA : IsPGroup p A) (hP : IsPGroup p P)
    (hAP : A ≤ Subgroup.normalizer (P : Set G)) (hPne : P ≠ ⊥) :
    ∃ x : G, x ∈ P ∧ x ≠ 1 ∧ x ∈ Subgroup.centralizer (A : Set G) := by
  classical
  haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPne
  -- the conjugation action of `A` on `P`, using `A ≤ N_G(P)`
  letI : MulAction ↥A ↥P :=
    { smul := fun a x => ⟨(a : G) * (x : G) * (a : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hAP a.2) (x : G)).mp x.2⟩
      one_smul := by
        intro x
        apply Subtype.ext
        show ((1 : ↥A) : G) * (x : G) * (((1 : ↥A)) : G)⁻¹ = (x : G)
        simp
      mul_smul := by
        intro a b x
        apply Subtype.ext
        show (((a * b : ↥A)) : G) * (x : G) * ((((a * b : ↥A))) : G)⁻¹
          = (a : G) * ((b : G) * (x : G) * (b : G)⁻¹) * (a : G)⁻¹
        rw [Subgroup.coe_mul]
        group }
  -- `p ∣ |P|`, as `P` is a nontrivial `p`-group
  have hpdvd : p ∣ Nat.card ↥P := by
    obtain ⟨n, hn0, hn⟩ := (hP.nontrivial_iff_card).mp inferInstance
    exact hn.symm ▸ dvd_pow_self p (ne_of_gt hn0)
  -- `1` is a fixed point
  have h1fix : (1 : ↥P) ∈ MulAction.fixedPoints ↥A ↥P := by
    rw [MulAction.mem_fixedPoints]
    intro a
    apply Subtype.ext
    show ((a : G) * ((1 : ↥P) : G) * (a : G)⁻¹) = ((1 : ↥P) : G)
    simp
  -- so there is a *second* fixed point
  obtain ⟨b, hbfix, hbne⟩ :=
    hA.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥P hpdvd h1fix
  refine ⟨(b : G), b.2, ?_, ?_⟩
  · intro hb
    exact hbne (Subtype.ext (by rw [hb]; rfl))
  · rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h : (⟨a, ha⟩ : ↥A) • b = b := (MulAction.mem_fixedPoints.mp hbfix) ⟨a, ha⟩
    have h2 : a * (b : G) * a⁻¹ = (b : G) := congrArg (fun z : ↥P => (z : G)) h
    calc a * (b : G) = a * (b : G) * a⁻¹ * a := by group
      _ = (b : G) * a := by rw [h2]

/-- Bender 1981 §3, p. 222 (`Ĥ = H`): for a maximal subgroup `M ⊇ N_G(P₂)`, the `p`-core
`P = O_p(U)` meets `M` nontrivially, `P₀ := P ∩ M ≠ 1`.

The point is that `N_G(P₂) ≤ M` gives `C_G(P₂) ≤ M`, and the `p`-group `P₂` has a nontrivial
fixed point `1 ≠ x ∈ P = O_p(U) ≠ 1`; then `x ∈ P ∩ M`. -/
theorem P0ne (I : Work.CORE3.Case1Inputs) (hFr : Work.GW2.Case1aFrattiniProp)
    (hAb : Work.GW2.Case1aAbelianProp) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case1 B → B.Hhat = B.H → ∀ D : Work.GW2.Case1aData B, ∀ P2 M : Subgroup G,
        P2 ≤ B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) → IsPGroup D.p P2 →
        ¬ D.p ∣ P2.relIndex (B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G)) →
        IsCoatom M → Subgroup.normalizer (P2 : Set G) ≤ M →
        (Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G) ≠ ⊥ := by
  intro G _instG _finG _hFT _hBc B _hCase1 _hHhat D P2 M hP2le hP2grp _hP2ndvd _hMcoat hNM
  haveI hpprime : Fact D.p.Prime := ⟨D.hp⟩
  -- `P = O_p(U)` is a nontrivial `p`-group
  have hPne : Work.GW2.pCoreIn D.p B.U ≠ ⊥ := Work.CORE3.Case1aP_ne_bot G B D
  have hPgrp : IsPGroup D.p (Work.GW2.pCoreIn D.p B.U) :=
    Work.CORE3.c1aIsPGroup_pCoreIn D.p B.U
  -- `P₂ ≤ U ≤ N_G(O_p(U))`, so the `p`-group `P₂` acts on `P`
  have hPn : P2 ≤ Subgroup.normalizer ((Work.GW2.pCoreIn D.p B.U : Subgroup G) : Set G) :=
    (hP2le.trans inf_le_left).trans
      ((Subgroup.le_normalizer).trans (Work.CORE3.c1aLe_normalizer_pCoreIn D.p B.U))
  -- a nontrivial element of `P` centralized by `P₂`
  obtain ⟨x, hxP, hx1, hxC⟩ :=
    exists_ne_one_mem_centralizer_of_isPGroup hP2grp hPgrp hPn hPne
  -- it lies in `M`, because `C_G(P₂) ≤ N_G(P₂) ≤ M`
  have hxM : x ∈ M := hNM (Subgroup.centralizer_le_normalizer (P2 : Set G) hxC)
  intro hbot
  have hx : x ∈ (Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G) := ⟨hxP, hxM⟩
  rw [hbot] at hx
  exact hx1 (Subgroup.mem_bot.mp hx)

end Work.CORE3.A7V18
