import Mathlib
import Submission.Work.AppXIShadow.Basic
import Submission.Work.AppXIShadow.AppII7
import Submission.Work.AppXIShadow.exists_prime_card_eq_pow_of_transitive_aut
import Submission.Work.AppXIField.Main.Basic
import Submission.Work.AppXIField.Main.exists_conjAut_R
import Submission.Work.AppXIField.Main.exists_conjAction_quot
import Submission.Work.AppXIShadow.CGP_twoTransitive
import Submission.Work.AppXIShadow.card_fixP_eq_card_CQ_add_one
import Submission.Work.AppXIShadow.zpowers_sMulT_inf_KerIn_eq_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint
open scoped commutatorElement

namespace Work.AppXIShadow

open Work.ThmF.ChV3

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}

/-! ### Elementary API for the kernel `KerIn H Q P t` -/

/-- `KerIn H Q P t` is exactly the kernel of the action of `C_G(P)` on `fixP H P` (A2,
`Work.AppXIShadow.fixP_kernel_iff`), read inside `↥C_G(P)`. -/
theorem mem_KerIn_iff_v2 (c : CtxF H Q t s r P) {g : ↥(centP P)} :
    g ∈ KerIn H Q P t ↔ ∀ ω : ↥(fixP H P), g • ω = ω := by
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hg ω
    refine Subtype.ext ?_
    rw [fixP_smul_coe]
    exact (fixP_kernel_iff c g.2).mpr hg (ω : G ⧸ H) ω.2
  · intro hg
    exact (fixP_kernel_iff c g.2).mp (fun ω hω => congrArg Subtype.val (hg ⟨ω, hω⟩))

/-- `KerIn H Q P t` is normal in `C_G(P)`, being the kernel of the action on `fixP H P`. -/
theorem KerIn_normal_v2 (c : CtxF H Q t s r P) : (KerIn H Q P t).Normal := by
  refine Subgroup.Normal.mk ?_
  intro n hn g
  rw [mem_KerIn_iff_v2 c] at hn ⊢
  intro ω
  calc (g * n * g⁻¹) • ω = g • (n • (g⁻¹ • ω)) := by rw [mul_smul, mul_smul]
    _ = g • (g⁻¹ • ω) := by rw [hn (g⁻¹ • ω)]
    _ = ω := by rw [← mul_smul, mul_inv_cancel, one_smul]

/-- `KerIn H Q P t ≤ fixPStab c`: the kernel fixes the base point. -/
theorem KerIn_le_fixPStab_v2 (c : CtxF H Q t s r P) : KerIn H Q P t ≤ fixPStab c := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff]
  exact (mem_KerIn_iff_v2 c).mp hg (fixPBaseC c)

/-! ### The conjugation action of `C_Q(P)` on the quotient `R / K`

This is the "middle" of A5: `C_Q(P) ≤ C_G(P)` acts on the normal subgroup
`R ⊴ C_G(P)` by conjugation, this descends to the quotient `A = R ⧸ K.subgroupOf R` (because
`K = KerIn H Q P t` is normal in `C_G(P)`), and under the identification `A ≃ fixP H P` of
orbit–stabiliser this action is the left action of `C_Q(P)` on `fixP H P`, which by A1
(`Work.AppXIShadow.CQ_regular_on_fixP`) is sharply transitive on the complement of the base
point.  Hence `C_Q(P)` is transitive on the non-identity elements of `A`. -/
theorem exists_conj_hom_quotient_v2 (c : CtxF H Q t s r P)
    (R : Subgroup ↥(centP P)) (hRn : R.Normal)
    (hKle : KerIn H Q P t ≤ R)
    (hstab : R ⊓ fixPStab c = KerIn H Q P t)
    (htr : ∀ ω : ↥(fixP H P), ∃ x ∈ R, x • fixPBaseC c = ω)
    [hKsubn : ((KerIn H Q P t).subgroupOf R).Normal] :
    ∃ φ : ↥(CQ Q P) →* MulAut (↥R ⧸ (KerIn H Q P t).subgroupOf R),
      (∀ a : ↥R ⧸ (KerIn H Q P t).subgroupOf R, a ≠ 1 →
        ∀ b : ↥R ⧸ (KerIn H Q P t).subgroupOf R, b ≠ 1 →
        ∃ g : ↥(CQ Q P), φ g a = b) := by
  classical
  haveI hKn : (KerIn H Q P t).Normal := KerIn_normal_v2 c
  let Acq : Subgroup ↥(centP P) := (CQ Q P).subgroupOf (centP P)
  have hnorm : Acq ≤ Subgroup.normalizer (R : Set ↥(centP P)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hRn]; exact le_top
  obtain ⟨cR, hcR⟩ := Work.AppXIField.Main.exists_conjAut_R Acq R hnorm
  have hcK : ∀ (a : ↥Acq) (x : ↥R), x ∈ (KerIn H Q P t).subgroupOf R →
      cR a x ∈ (KerIn H Q P t).subgroupOf R := by
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hcR a x]
    exact Subgroup.Normal.conj_mem hKn (x : ↥(centP P)) hx (a : ↥(centP P))
  obtain ⟨act, hact⟩ := Work.AppXIField.Main.exists_conjAction_quot Acq R
      ((KerIn H Q P t).subgroupOf R) cR hcK
  let e : ↥Acq ≃* ↥(CQ Q P) := Subgroup.subgroupOfEquivOfLe (CQ_le_CGP c)
  refine ⟨act.comp e.symm.toMonoidHom, ?_⟩
  -- ### basic facts
  have hfix_iff : ∀ x : ↥R, x ∈ (KerIn H Q P t).subgroupOf R ↔ x • fixPBaseC c = fixPBaseC c := by
    intro x
    rw [Subgroup.smul_def, ← MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, ← hstab,
      Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hmk_key : ∀ u y : ↥R, u • fixPBaseC c = y • fixPBaseC c →
      QuotientGroup.mk' ((KerIn H Q P t).subgroupOf R) u =
        QuotientGroup.mk' ((KerIn H Q P t).subgroupOf R) y := by
    intro u y h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [hfix_iff (u⁻¹ * y), Subgroup.smul_def]
    have h' : (u : ↥(centP P)) • fixPBaseC c = (y : ↥(centP P)) • fixPBaseC c := by
      simpa only [Subgroup.smul_def] using h
    have hcoeuy : ((u⁻¹ * y : ↥R) : ↥(centP P)) = (u : ↥(centP P))⁻¹ * (y : ↥(centP P)) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoeuy, mul_smul, ← h', inv_smul_smul]
  -- ### coercion of `x • ∞` to `G ⧸ H`
  have hcoe_smul : ∀ x : ↥R, (((x • fixPBaseC c) : ↥(fixP H P)) : G ⧸ H)
      = (x : G) • ((1 : G) : G ⧸ H) := by
    intro x
    rw [Subgroup.smul_def, fixP_smul_coe, fixPBase_coe]
  -- ### the main argument
  rintro a ha b hb
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((KerIn H Q P t).subgroupOf R) a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective ((KerIn H Q P t).subgroupOf R) b
  have hxK : x ∉ (KerIn H Q P t).subgroupOf R := by
    intro h
    exact ha (by rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact h)
  have hyK : y ∉ (KerIn H Q P t).subgroupOf R := by
    intro h
    exact hb (by rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact h)
  have hxb : x • fixPBaseC c ≠ fixPBaseC c := fun h => hxK ((hfix_iff x).mpr h)
  have hyb : y • fixPBaseC c ≠ fixPBaseC c := fun h => hyK ((hfix_iff y).mpr h)
  have hxG : (((x • fixPBaseC c) : ↥(fixP H P)) : G ⧸ H) ≠ ((1 : G) : G ⧸ H) := by
    intro hh
    refine hxb (Subtype.ext ?_)
    rw [hh, fixPBase_coe H P (P_le_H c)]
  have hyG : (((y • fixPBaseC c) : ↥(fixP H P)) : G ⧸ H) ≠ ((1 : G) : G ⧸ H) := by
    intro hh
    refine hyb (Subtype.ext ?_)
    rw [hh, fixPBase_coe H P (P_le_H c)]
  obtain ⟨z, hz, hzx⟩ := CQ_transitive_on_fixP_remove_base c
    ((x • fixPBaseC c).2) hxG ((y • fixPBaseC c).2) hyG
  have hzH : z ∈ H := CQ_le_H c hz
  have hzx1 : (((x • fixPBaseC c) : ↥(fixP H P)) : G ⧸ H) = (x : G) • ((1 : G) : G ⧸ H) :=
    hcoe_smul x
  have hzy1 : (((y • fixPBaseC c) : ↥(fixP H P)) : G ⧸ H) = (y : G) • ((1 : G) : G ⧸ H) :=
    hcoe_smul y
  have hzx' : (z : G) • ((x : G) • ((1 : G) : G ⧸ H)) = (y : G) • ((1 : G) : G ⧸ H) := by
    rw [← hzx1, ← hzy1]; exact hzx
  -- the conjugating element as an `Hc` element
  let zg : ↥(CQ Q P) := ⟨z, hz⟩
  have hez : ((e.symm zg : ↥Acq) : ↥(centP P)) = ⟨z, CQ_le_CGP c hz⟩ := rfl
  refine ⟨zg, ?_⟩
  -- evaluate the action
  show (act.comp e.symm.toMonoidHom) zg
      (QuotientGroup.mk' ((KerIn H Q P t).subgroupOf R) x) = _
  rw [MonoidHom.comp_apply]
  change (act (e.symm zg)) (QuotientGroup.mk' ((KerIn H Q P t).subgroupOf R) x) = _
  rw [hact (e.symm zg) x]
  refine hmk_key (cR (e.symm zg) x) y ?_
  apply Subtype.ext
  rw [Subgroup.smul_def, fixP_smul_coe, Subgroup.smul_def, fixP_smul_coe, fixPBase_coe]
  rw [hcR (e.symm zg) x, hez]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [mul_smul, mul_smul, Work.ZassenhausTwoGroup.IsTIQ.smul_basePt_of_mem H (H.inv_mem hzH)]
  simpa using hzx'

/-- **A5, numeric core.**  `f = o(st)` is prime, `|C_Q(P)| + 1 = f^m` and `|R| = |Ker| · f^m`
for the normal subgroup `R ⊴ C_G(P)` produced by `Work.AppXIShadow.app3_regular_normal` in the
standing context `CtxF H Q t s r P`; the membership `st ∈ R` is taken as the hypothesis `hst`
(proved separately by `Work.AppXIShadow.s_mul_t_mem_R`).

Hypotheses (`K = KerIn H Q P t`): `R ⊴ C_G(P)`, `K ≤ R`, `[R,R] ≤ K`, `R ⊓ C_H(P) = K`,
`R` transitive on the `C_G(P)`-set `fixP H P`, and `st ∈ R`.

Route.

* `K` is the kernel of the action (`Work.AppXIShadow.fixP_kernel_iff`), so `K ⊴ C_G(P)`,
  `K.subgroupOf R ⊴ R`, and `A := R ⧸ K.subgroupOf R` is a group with
  `Nat.card A * Nat.card K = Nat.card R` (orbit–stabiliser for `R` on `fixP H P` with point
  stabiliser `R ⊓ fixPStab c = K`, via `hstab`/`htr`); `[R,R] ≤ K` makes `A` abelian
  (`Subgroup.Normal.quotient_commutative_iff_commutator_le`).
* `x ↦ x • ∞` descends to a bijection `A ≃ ↥(fixP H P)` (surjective by `htr`; injective since
  `x • ∞ = y • ∞` forces `y⁻¹x ∈ R ⊓ fixPStab c = K`), so `Nat.card A = |fixP| = |C_Q(P)| + 1`
  (A1: `Work.AppXIShadow.CQ_regular_on_fixP`).
* `C_Q(P) ≤ C_G(P)` acts on `A` by conjugation (`MulAut.conjNormal` composed with the quotient
  map); under the bijection this is the left action of `C_Q(P)` on `fixP H P` (`C_Q(P) ≤ H` fixes
  `∞`), which is sharply transitive on `fixP H P ∖ {∞}` (A1), so `C_Q(P)` acts transitively on
  `A ∖ {1}`, and `exists_prime_card_eq_pow_of_transitive_aut` gives a prime `f₀` with
  `orderOf a = f₀` for every `1 ≠ a : A` and `Nat.card A = f₀ ^ m`.
* `hst : st ∈ R` and `st ∉ K` (`st ∈ K ≤ fixPStab` would force `t • ∞ = ∞`, i.e. `t ∈ H`); so the
  class of `st` in `A` is non-trivial and has order `f₀`: `f₀ ∣ o(st)` and `(st)^{f₀} ∈ K`.
* `⟨st⟩ ⊓ K = 1`: `x = (st)^j ∈ K` commutes with `st` (`x ∈ ⟨st⟩`) and with `s`
  (`s ∈ C_Q(P)` and `K ≤ C(C_Q(P))`), hence with `t = s·(st)`; but `t` inverts `st`, hence `x`,
  so `x = x⁻¹`; and `x ∈ K ≤ Ker ≤ D = twoPoint H t`, which is odd (`c.odd_card_twoPoint`), so
  `x = 1`.
* Hence `o(st) ∣ f₀`, so `o(st) = f₀` is prime, `|fixP| = |C_Q(P)| + 1 = f₀^m` and
  `Nat.card R = Nat.card K · f₀^m`; finally `1 ≤ m` since `|C_Q(P)| + 1 > 1 = f₀^0`. -/
theorem orderOf_s_mul_t_prime_v2 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P)
    (R : Subgroup ↥(Work.AppXIShadow.centP P)) (hRn : R.Normal)
    (hKle : Work.AppXIShadow.KerIn H Q P t ≤ R)
    (hRK : ⁅R, R⁆ ≤ Work.AppXIShadow.KerIn H Q P t)
    (hstab : R ⊓ Work.AppXIShadow.fixPStab c = Work.AppXIShadow.KerIn H Q P t)
    (htr : ∀ ω : ↥(Work.AppXIShadow.fixP H P),
      ∃ x ∈ R, x • Work.AppXIShadow.fixPBaseC c = ω)
    (hst : Work.AppXIShadow.sMulT c ∈ R) :
    (orderOf (s * t)).Prime ∧
    ∃ m : ℕ, 1 ≤ m ∧
      Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = orderOf (s * t) ^ m ∧
      Nat.card ↥R = Nat.card ↥(Work.AppXIShadow.KerIn H Q P t) * orderOf (s * t) ^ m := by
  classical
  haveI hKn : (KerIn H Q P t).Normal := KerIn_normal_v2 c
  haveI hKsubn : ((KerIn H Q P t).subgroupOf R).Normal := hKn.subgroupOf R
  -- the conjugating action homomorphism and its transitivity
  obtain ⟨φ, hφtr⟩ := exists_conj_hom_quotient_v2 c R hRn hKle hstab htr
  -- the quotient is abelian
  have hcomm : ∀ a b : ↥R ⧸ (KerIn H Q P t).subgroupOf R, a * b = b * a :=
    isMulCommutative_iff.mp
      (Work.AppXIField.isMulCommutative_quot R (KerIn H Q P t)
        (fun x hx y hy => by
          have h := hRK (Subgroup.commutator_mem_commutator hx hy)
          simpa only [commutatorElement_def] using h))
  -- the prime `f` and the exponent `m`
  obtain ⟨f, m, hfprime, hford, hfcard⟩ :=
    exists_prime_card_eq_pow_of_transitive_aut
      (A := ↥R ⧸ (KerIn H Q P t).subgroupOf R) (B := ↥(CQ Q P)) hcomm φ hφtr
  -- ### the cardinality of the quotient `R/K`
  have hstabR : MulAction.stabilizer ↥R (fixPBaseC c) =
      (KerIn H Q P t).subgroupOf R := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    rw [Subgroup.smul_def]
    rw [← MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      rw [← hstab]
      exact ⟨g.2, h⟩
    · intro h
      have h' : (g : ↥(centP P)) ∈ R ⊓ fixPStab c := by rw [hstab]; exact h
      exact h'.2
  have hA_card_fixP :
      Nat.card (↥R ⧸ (KerIn H Q P t).subgroupOf R) = Nat.card ↥(fixP H P) := by
    have h1 := Nat.card_congr
      (MulAction.orbitEquivQuotientStabilizer ↥R (fixPBaseC c)).symm
    rw [hstabR] at h1
    have h2 : MulAction.orbit ↥R (fixPBaseC c) = Set.univ := by
      ext ω
      rw [MulAction.mem_orbit_iff]
      exact ⟨fun _ => trivial, fun _ => by
        obtain ⟨x, hx, hxω⟩ := htr ω
        exact ⟨⟨x, hx⟩, by simpa [Subgroup.smul_def] using hxω⟩⟩
    rw [h2] at h1
    rw [h1]
    exact Nat.card_congr (Equiv.Set.univ (↥(fixP H P)))
  have hA_card : Nat.card (↥R ⧸ (KerIn H Q P t).subgroupOf R) = Nat.card ↥(CQ Q P) + 1 :=
    hA_card_fixP.trans (card_fixP_eq_card_CQ_add_one c)
  -- ### the class of `st`
  have hst_ne_one : sMulT c ≠ 1 := by
    intro h
    have h1 : s * t = 1 := by
      have := congrArg (fun z : ↥(centP P) => (z : G)) h
      simpa [sMulT_coe] using this
    have ht : t = s := by
      have h2 : s⁻¹ = t := mul_eq_one_iff_inv_eq.mp h1
      rw [inv_eq_of_mul_eq_one_left (s_mul_s c)] at h2
      exact h2.symm
    exact t_not_mem_H c (ht.symm ▸ CQ_le_H c (s_mem_CQ c))
  have hstK : sMulT c ∉ KerIn H Q P t := by
    intro h
    have hmem : sMulT c ∈ Subgroup.zpowers (sMulT c) ⊓ KerIn H Q P t :=
      ⟨Subgroup.mem_zpowers _, h⟩
    rw [zpowers_sMulT_inf_KerIn_eq_bot c] at hmem
    exact hst_ne_one (Subgroup.mem_bot.mp hmem)
  let r0 : ↥R := ⟨sMulT c, hst⟩
  have hclass_ne : QuotientGroup.mk' ((KerIn H Q P t).subgroupOf R) r0 ≠ 1 := by
    intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact hstK h
  have hford_r0 : orderOf (QuotientGroup.mk' ((KerIn H Q P t).subgroupOf R) r0) = f :=
    hford _ hclass_ne
  have hord_eq : orderOf (sMulT c) = orderOf r0 := by
    rw [← Subgroup.orderOf_coe r0]
  have h_dvd1 : f ∣ orderOf r0 := by
    have h := orderOf_map_dvd (QuotientGroup.mk' ((KerIn H Q P t).subgroupOf R)) r0
    rwa [hford_r0] at h
  have h_dvd2 : orderOf r0 ∣ f := by
    have haf : (QuotientGroup.mk' ((KerIn H Q P t).subgroupOf R) r0) ^ f = 1 := by
      rw [← hford_r0, pow_orderOf_eq_one]
    have hmk : QuotientGroup.mk' ((KerIn H Q P t).subgroupOf R) (r0 ^ f) = 1 := by
      rw [map_pow (QuotientGroup.mk' ((KerIn H Q P t).subgroupOf R)) r0 f]; exact haf
    have hmk' : (↑(r0 ^ f) : ↥R ⧸ (KerIn H Q P t).subgroupOf R) = 1 := by
      rw [QuotientGroup.mk'_apply] at hmk; exact hmk
    have hmem : r0 ^ f ∈ (KerIn H Q P t).subgroupOf R := by
      rw [← QuotientGroup.eq_one_iff]; exact hmk'
    have hmemK : (sMulT c) ^ f ∈ KerIn H Q P t := by
      rw [← Subgroup.coe_pow (H := R) r0 f]
      exact (Subgroup.mem_subgroupOf).mp hmem
    have hz : (sMulT c) ^ f ∈ Subgroup.zpowers (sMulT c) :=
      Subgroup.pow_mem _ (Subgroup.mem_zpowers _) f
    have hmem2 : (sMulT c) ^ f ∈ Subgroup.zpowers (sMulT c) ⊓ KerIn H Q P t := ⟨hz, hmemK⟩
    rw [zpowers_sMulT_inf_KerIn_eq_bot c] at hmem2
    have hpow1 : (sMulT c) ^ f = 1 := Subgroup.mem_bot.mp hmem2
    have h := orderOf_dvd_of_pow_eq_one hpow1
    rwa [hord_eq] at h
  have hord_r0_eq : orderOf r0 = f := Nat.dvd_antisymm h_dvd2 h_dvd1
  have hord_st : orderOf (s * t) = orderOf (sMulT c) := by
    rw [← sMulT_coe c]
    exact Subgroup.orderOf_coe (sMulT c)
  have hord_f : orderOf (s * t) = f := by rw [hord_st, hord_eq, hord_r0_eq]
  -- ### the cardinality of `R`
  have hRcard : Nat.card ↥R = Nat.card ↥(KerIn H Q P t) * f ^ m := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((KerIn H Q P t).subgroupOf R)
    rw [h1, hfcard, Work.AppXIField.card_subgroupOf R (KerIn H Q P t) hKle]
    exact mul_comm _ _
  refine ⟨?_, m, ?_, ?_, ?_⟩
  · rw [hord_f]; exact hfprime
  · rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      have hpos : 0 < Nat.card ↥(CQ Q P) := by
        haveI : Nonempty ↥(CQ Q P) := ⟨⟨1, (CQ Q P).one_mem⟩⟩
        exact Nat.card_pos
      have hm0 : f ^ m = 1 := by rw [h, pow_zero]
      rw [hm0, hA_card] at hfcard
      omega
    · exact h
  · rw [hord_f]; exact hA_card.symm.trans hfcard
  · rw [hord_f]; exact hRcard

end Work.AppXIShadow
