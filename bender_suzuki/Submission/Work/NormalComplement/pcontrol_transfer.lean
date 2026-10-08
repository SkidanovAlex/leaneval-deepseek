/-
# `pcontrol_transfer` is FALSE as stated — counterexample and diagnosis

**The requested statement**

  `IsPControl p E W → y ∈ E → y ≠ 1 → (∃ k, orderOf y = p ^ k) → y ∉ ⁅E,E⁆ → y ∉ O^p(W)`

is **false**, because the third clause of `IsPControl` (`Defs.lean`) takes the centralizer in the
*ambient* group `G` and *joins* it with `E`:

  `∀ U ≤ E, IsPGroup p U → ∀ x ∈ W, conj x U ≤ E → x ∈ Subgroup.centralizer (U : Set G) ⊔ E`.

Peterfalvi's condition (Ch. III §1, p. 172) instead asks for the *set product* `C_W(U)·E` inside
`W`; the join in a larger ambient group is strictly weaker, and for `G > W` it can become vacuous
on the very elements the conclusion is about.

**Explicit counterexample** (all facts machine-checked with GAP):

* `G := Equiv.Perm (Fin 5)` (the symmetric group `S₅`, `|G| = 120`);
* `W := S₄ = Stab(5) ≤ G` (`|W| = 24`), `E := W ⊓ AlternatingGroup = A₄` (`|E| = 12`, `[W:E] = 2`);
* `p := 3` (so `3 ∤ [W:E]`), `y := (2 3 4) ∈ E`, `orderOf y = 3 = 3¹`, `y ∉ ⁅E,E⁆ = V₄`.

`IsPControl 3 E W` **holds**: for every `3`-subgroup `U ≤ A₄` (namely `U = 1` and the four
subgroups of order `3`) one has `⟨C_G(U), E⟩ = S₅ ⊇ W` — the centralizer `C_{S₅}(U)` contains the
transposition exchanging the two fixed points of a `3`-cycle, and together with `A₄` it generates
`S₅` (GAP: for all five `U`: `⟨C_G(U), A₄⟩ = S₅`); since `A₄ ⊴ S₄`, the conjugation hypothesis
`conj x U ≤ E` holds for *every* `x ∈ W`, so the control condition is satisfied.

But the **conclusion fails**: `O^3(W) = ⟨3'-elements of S₄⟩ = S₄` (the transpositions generate
`S₄`; GAP: `|O³(W)| = 24 = |W|`), and `y = (2 3 4) ∈ O³(W)`.  So `y ∈ O^p(W)` although
`y ∈ E ∖ ⁅E,E⁆` and `E` is `p`-control in `W` in the formalized sense.

(Equivalently, the product form used by the transfer argument fails: with `U := ⟨y⟩` and
`x := (4 5) ∈ W` one has `conj x⁻¹ U = U ≤ E`, yet `x ∉ C_W(U)·E = E`, since `C_W(U) ≤ E` and
`x` is odd.)

**Repair.** Replace the third clause of `IsPControl` by the product *inside* `W`,
`∃ c ∈ C_W(U), ∃ e ∈ E, x = c * e` (equivalently `(Subgroup.centralizer (U : Set G) ⊓ W) ⊔ E`).
With the ambient group taken to be `W` itself (whence the two formulations coincide) extensive GAP
searches over all groups of order `≤ 80` found no counterexample to the theorem; this file records
the transfer argument conditional on that product form.
-/
import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.Grun.Main
import Submission.Work.LocalPrelim.regular_sylow_fusion
import Submission.Work.NormalComplement.pcontrol_mul_form
import Submission.Work.NormalComplement.notMem_pResidual_sup_commutator
import Submission.Work.NormalComplement.map_pResidual_sup_commutator_subgroupOf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open Classical
open scoped Pointwise commutatorElement IsMulCommutative
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Conjugates of elements of a `p`-subgroup `U ≤ E` landing in `E` are `E`-conjugate, given the
product form of the control condition. -/
lemma conj_eq_conj_of_control {E W : Subgroup G}
    (hmul : ∀ (U : Subgroup G), U ≤ E → IsPGroup p U → ∀ (x : G), x ∈ W →
      conj x⁻¹ U ≤ E →
      ∃ c : G, c ∈ Subgroup.centralizer (U : Set G) ∧ c ∈ W ∧ ∃ e ∈ E, x = c * e)
    {U : Subgroup G} (hU : U ≤ E) (hUp : IsPGroup p U) {x a : G} (hxW : x ∈ W)
    (hconj : conj x⁻¹ U ≤ E) (ha : a ∈ U) :
    ∃ e ∈ E, x⁻¹ * a * x = e⁻¹ * a * e := by
  obtain ⟨c, hc, hcW, e, heE, rfl⟩ := hmul U hU hUp x hxW hconj
  refine ⟨e, heE, ?_⟩
  have hca : c * a = a * c := ((Subgroup.mem_centralizer_iff.mp hc) a ha).symm
  have hc1 : c⁻¹ * a * c = a := by
    rw [mul_assoc, ← hca, ← mul_assoc, inv_mul_cancel, one_mul]
  have h1 : (c * e)⁻¹ * a * (c * e) = e⁻¹ * (c⁻¹ * a * c) * e := by group
  rw [h1, hc1]

/-- The transfer step of Peterfalvi I Ch. III §1 Lemma 1, with the external inputs
(`hmul` = the product form of the control condition, `hnotmem`/`hbridge` = the two halves of the
statement that `y ∉ O^p(E)·[E,E]`) as hypotheses. -/
theorem pcontrol_transfer_aux {E W : Subgroup G} (h : IsPControl p E W) {y : G}
    (hyE : y ∈ E) (hy1 : y ≠ 1) (hord : ∃ k : ℕ, orderOf y = p ^ k)
    (hy' : y ∉ ⁅E, E⁆)
    (hmul : ∀ (U : Subgroup G), U ≤ E → IsPGroup p U → ∀ (x : G), x ∈ W →
      conj x⁻¹ U ≤ E →
      ∃ c : G, c ∈ Subgroup.centralizer (U : Set G) ∧ c ∈ W ∧ ∃ e ∈ E, x = c * e)
    (hnotmem : y ∉ Work.Grun.pResidual p E ⊔ ⁅E, E⁆)
    (hbridge : ∀ z : ↥W,
      z ∈ (Work.NPC.Frobenius.pResidual p ↥(E.subgroupOf W) ⊔
            commutator ↥(E.subgroupOf W)).map (E.subgroupOf W).subtype →
        (z : G) ∈ Work.Grun.pResidual p E ⊔ ⁅E, E⁆) :
    y ∉ Work.Grun.pResidual p W := by
  obtain ⟨hEW, hIdx, hCtrl⟩ := h
  have hyW : y ∈ W := hEW hyE
  set Hx : Subgroup ↥W := E.subgroupOf W with hHx
  set yX : ↥W := ⟨y, hyW⟩ with hyX
  have hpow : ∀ k : ℕ, yX ^ k ∈ Hx := by
    intro k
    rw [hyX, hHx, Subgroup.mem_subgroupOf]
    exact E.pow_mem hyE k
  have hyHx : yX ∈ Hx := by simpa using hpow 1
  set yHx : ↥Hx := ⟨yX, hyHx⟩ with hyHxdef
  set N : Subgroup ↥Hx := Work.NPC.Frobenius.pResidual p ↥Hx ⊔ commutator ↥Hx with hN
  have hNnorm : N.Normal := by rw [hN]; exact Subgroup.sup_normal _ _
  haveI hNnormI : N.Normal := hNnorm
  haveI hcommI : IsMulCommutative (↥Hx ⧸ N) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_sup_right
  have hAp : IsPGroup p (↥Hx ⧸ N) := by
    intro z
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N z
    obtain ⟨n, hn⟩ := Work.NPC.Frobenius.isPGroup_quotient_pResidual (G := ↥Hx) (p := p) a
    refine ⟨n, ?_⟩
    have h1 : ((QuotientGroup.mk' N) (a ^ p ^ n)) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN]
      exact SetLike.le_def.mp le_sup_left (by rw [← QuotientGroup.eq_one_iff]; exact hn)
    simpa [map_pow] using h1
  set φ : ↥Hx →* (↥Hx ⧸ N) := QuotientGroup.mk' N with hφ
  -- the congruence hypothesis for the transfer
  have hkey : ∀ (k : ℕ) (g₀ : ↥W) (hk : g₀⁻¹ * yX ^ k * g₀ ∈ Hx),
      φ ⟨g₀⁻¹ * yX ^ k * g₀, hk⟩ = φ ⟨yX ^ k, hpow k⟩ := by
    intro k g₀ hk
    have hgW : (g₀ : G) ∈ W := g₀.2
    have hmemE : (g₀ : G)⁻¹ * y ^ k * (g₀ : G) ∈ E := by
      have h1 : (((g₀⁻¹ * yX ^ k * g₀ : ↥W)) : G) ∈ E := by
        rw [hHx, Subgroup.mem_subgroupOf] at hk
        exact hk
      simpa [hyX] using h1
    have hUE : Subgroup.zpowers (y ^ k) ≤ E := Subgroup.zpowers_le.mpr (E.pow_mem hyE k)
    have hUp : IsPGroup p (Subgroup.zpowers (y ^ k)) := by
      obtain ⟨j, hj⟩ := hord
      refine IsPGroup.of_card_dvd_pow (n := j) ?_
      rw [Nat.card_zpowers, ← hj]
      exact orderOf_pow_dvd k
    have hconj : conj (g₀ : G)⁻¹ (Subgroup.zpowers (y ^ k)) ≤ E := by
      intro z hz
      rw [Submission.Blueprint.conj, Subgroup.mem_map] at hz
      obtain ⟨u, hu, rfl⟩ := hz
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      have h1 : (MulAut.conj (g₀ : G)⁻¹) ((y ^ k) ^ m) =
          ((g₀ : G)⁻¹ * y ^ k * (g₀ : G)) ^ m := by
        rw [map_zpow]
        congr 1
        rw [MulAut.conj_apply, inv_inv]
      change (MulAut.conj (g₀ : G)⁻¹) ((y ^ k) ^ m) ∈ E
      rw [h1]
      exact E.zpow_mem hmemE m
    obtain ⟨e, heE, heq⟩ :=
      conj_eq_conj_of_control hmul hUE hUp hgW hconj (Subgroup.mem_zpowers (y ^ k))
    have heW : e ∈ W := hEW heE
    set eX : ↥W := ⟨e, heW⟩ with heXdef
    have heHx : eX ∈ Hx := by rw [hHx, Subgroup.mem_subgroupOf, heXdef]; exact heE
    set eHx : ↥Hx := ⟨eX, heHx⟩ with heHxdef
    have heqX : eHx⁻¹ * (⟨yX ^ k, hpow k⟩ : ↥Hx) * eHx =
        (⟨g₀⁻¹ * yX ^ k * g₀, hk⟩ : ↥Hx) := by
      apply Subtype.ext
      apply Subtype.ext
      simp only [heHxdef, heXdef, hyX, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      exact heq.symm
    have hAeq : (⟨g₀⁻¹ * yX ^ k * g₀, hk⟩ : ↥Hx) =
        eHx⁻¹ * (⟨yX ^ k, hpow k⟩ : ↥Hx) * eHx := heqX.symm
    have hmemN : (⟨g₀⁻¹ * yX ^ k * g₀, hk⟩ : ↥Hx)⁻¹ * (⟨yX ^ k, hpow k⟩ : ↥Hx) ∈ N := by
      rw [hAeq, hN]
      refine SetLike.le_def.mp le_sup_right ?_
      have hmem : ⁅eHx⁻¹, (⟨yX ^ k, hpow k⟩ : ↥Hx)⁻¹⁆ ∈ commutator ↥Hx :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      convert hmem using 1
      rw [commutatorElement_def]
      group
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq (s := N)).mpr hmemN
  -- the transfer computation
  have htransfer : (MonoidHom.transfer φ) yX = φ ⟨yX ^ Hx.index, hpow Hx.index⟩ :=
    Work.LocalPrelim.transfer_eq_pow_of_congruent φ yX hpow hkey
  -- if `y ∈ O^p(W)` then the transfer kills `yX`
  have hkill : Work.NPC.Frobenius.pResidual p ↥W ≤ (MonoidHom.transfer φ).ker := by
    rw [Work.NPC.Frobenius.pResidual]
    refine (Subgroup.closure_le _).mpr ?_
    rintro z hz
    have h1 : orderOf ((MonoidHom.transfer φ) z) ∣ orderOf z := orderOf_map_dvd _ z
    obtain ⟨n, hn⟩ := hAp ((MonoidHom.transfer φ) z)
    have h2 : orderOf ((MonoidHom.transfer φ) z) ∣ p ^ n :=
      orderOf_dvd_iff_pow_eq_one.mpr hn
    have hdvd := Nat.dvd_gcd h1 h2
    have hcop : (orderOf z).Coprime (p ^ n) :=
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hz).symm.pow_right n
    rw [hcop.gcd_eq_one] at hdvd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
  intro hyK
  -- `y ∈ O^p(W)` gives `yX ∈ O^p(↥W)`
  have hyXK : yX ∈ Work.NPC.Frobenius.pResidual p ↥W := by
    rw [Work.Grun.pResidual_eq_map_pResidual p W, Subgroup.mem_map] at hyK
    obtain ⟨z, hz, hzy⟩ := hyK
    have hzx : z = yX := by
      have h1 : (yX : G) = y := by rw [hyX]
      exact Subtype.ext (hzy.trans h1.symm)
    rwa [hzx] at hz
  have hTy : (MonoidHom.transfer φ) yX = 1 := MonoidHom.mem_ker.mp (hkill hyXK)
  -- the class of `yX` in the abelian `p`-group `↥Hx ⧸ N` is killed by `Hx.index`
  have hyHxN : yHx ∈ N := by
    have hIdxN : yHx ^ Hx.index ∈ N := by
      have h1 : φ (yHx ^ Hx.index) = 1 := by
        have h2 : (⟨yX ^ Hx.index, hpow Hx.index⟩ : ↥Hx) = yHx ^ Hx.index := by
          apply Subtype.ext; rfl
        rw [← h2, ← htransfer]; exact hTy
      rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have hJ : orderOf ((QuotientGroup.mk' N) yHx) ∣ Hx.index := by
      rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact hIdxN
    obtain ⟨k, hk⟩ := hord
    have hK : orderOf ((QuotientGroup.mk' N) yHx) ∣ p ^ k := by
      have h1 : orderOf ((QuotientGroup.mk' N) yHx) ∣ orderOf yHx := orderOf_map_dvd _ yHx
      have h2 : orderOf yHx = p ^ k := by
        rw [← Subgroup.orderOf_coe yHx]
        rw [show ((yHx : ↥Hx) : ↥W) = yX from rfl]
        rw [hyX, ← Subgroup.orderOf_coe (⟨y, hyW⟩ : ↥W)]
        exact hk
      rwa [h2] at h1
    have hdvd := Nat.dvd_gcd hK hJ
    have hcop : Hx.index.Coprime (p ^ k) :=
      (Fact.out : p.Prime).coprime_pow_of_not_dvd (m := k) (by rw [hHx]; exact hIdx)
    rw [Nat.gcd_comm, hcop.gcd_eq_one] at hdvd
    have h1 : (QuotientGroup.mk' N) yHx = 1 :=
      orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  -- `yX` therefore lies in the image of `N`, and the bridge produces the contradiction
  have hyXmap : yX ∈ N.map Hx.subtype := Subgroup.mem_map.mpr ⟨yHx, hyHxN, rfl⟩
  rw [hN, hHx] at hyXmap
  exact hnotmem (by simpa [hyX] using hbridge yX hyXmap)

theorem pcontrol_transfer {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {E W : Subgroup G} (h : Work.NormalComplement.IsPControl p E W) {y : G}
    (hyE : y ∈ E) (hy1 : y ≠ 1) (hord : ∃ k : ℕ, orderOf y = p ^ k)
    (hy' : y ∉ ⁅E, E⁆) :
    y ∉ Work.Grun.pResidual p W := by
  refine pcontrol_transfer_aux h hyE hy1 hord hy'
    (fun U hU hUp x hxW hconj => Work.NormalComplement.pcontrol_mul_form h hU hUp hxW hconj)
    (Work.NormalComplement.notMem_pResidual_sup_commutator hyE hy1 hord hy') ?_
  intro z hz
  have h1 : (z : G) ∈ ((Work.NPC.Frobenius.pResidual p ↥(E.subgroupOf W) ⊔
      commutator ↥(E.subgroupOf W)).map (E.subgroupOf W).subtype).map W.subtype :=
    Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  rwa [Work.NormalComplement.map_pResidual_sup_commutator_subgroupOf h.1] at h1

end Work.NormalComplement
