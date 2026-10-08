import Mathlib
import Submission.Work.Hering.Config
import Submission.Work.Hering.HardCore.abelian_setup
import Submission.Work.Hering.HardCore.abelian_thm
import Submission.Work.Hering.HardCore.sq_level2_surj
import Submission.Work.Hering.HardCore.card_map_level2
import Submission.Work.Hering.HardCore.centralizer_map_level2
import Submission.Work.Hering.HardCore.actsAsAut_map_level2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The abelian case of the hard core of Hering's theorem

This file proves `Work.Hering.HardCore.abelian_case`: the abelian case of Peterfalvi I
Chapter IV, §3, Proposition 2.  The configuration is

* `V ⊴ G` is elementary abelian of order `8` (`hcard`, `hexp`),
* `C = C_G(V)` is a 2-group with `Ω₁(C) = V` (`hC`, `hC2`, `hinv`),
* `G/C ≅ Aut(V)` (`hAut`),
* all involutions of `G` lie in `C` (`hnoinv`),
* `C` is abelian (`hCab`).

Under these hypotheses we derive a contradiction.  Equivalently (Peterfalvi I §3 Prop. 2):
with the first four items assumed, there *is* an involution of `G` outside `C`; this is
proved by strong induction on `|G|` as `Work.Hering.HardCore.prop2_aux`.

The induction step passes to the quotient `G ⧸ V`, in which the elementary abelian normal
subgroup is the image `V̄ = C₂/V` of the second level `C₂ = {c ∈ C | c² ∈ V}` of `C` (an
elementary abelian group of order `8`, with `C_{G/V}(V̄) = C/V` and `G/C ≅ Aut(V̄)`); the lemmas
collecting these facts are proved in the auxiliary files `sq_level2_surj`, `card_map_level2`,
`centralizer_map_level2`, `actsAsAut_map_level2`.  The core of the abelian case -- Peterfalvi I
§3 Prop. 2, steps 3–9 -- is the file `abelian_thm.lean`.
-/

set_option autoImplicit false

namespace Work.Hering.HardCore

open LeanEval.GroupTheory.Defs

variable {G : Type*} [Group G] [Finite G]

/-! ## The second level of `C` modulo `V` -/

/-- The image of the second level in `G ⧸ V` has exponent two. -/
theorem map_level2_sq_one (V C : Subgroup G) [V.Normal]
    (hC : C = Subgroup.centralizer ((V : Set G)))
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (hexp : ∀ x ∈ V, x * x = 1) :
    ∀ x ∈ (level2 V C hC hCab hexp).map (QuotientGroup.mk' V), x * x = 1 := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  rw [← hyx, ← map_mul]
  exact (QuotientGroup.eq_one_iff (y * y)).mpr hy.2

/-- The image of `C` in `G ⧸ V` is a `2`-group. -/
theorem isPGroup_map_quotient (V C : Subgroup G) [V.Normal] (hC2 : IsPGroup 2 ↥C) :
    IsPGroup 2 ↥(C.map (QuotientGroup.mk' V)) :=
  IsPGroup.map hC2 (QuotientGroup.mk' V)

/-- The elements of order two of `C/V` lie in `C₂/V`. -/
theorem orderOf_two_mem_map_level2 (V C : Subgroup G) [V.Normal]
    (hC : C = Subgroup.centralizer ((V : Set G)))
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (hexp : ∀ x ∈ V, x * x = 1)
    (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V) {x : G ⧸ V}
    (hx : x ∈ C.map (QuotientGroup.mk' V)) (hx2 : orderOf x = 2) :
    x ∈ (level2 V C hC hCab hexp).map (QuotientGroup.mk' V) := by
  obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hx
  have hx' : x = QuotientGroup.mk' V c := hcx.symm
  have hx2' : x * x = 1 := by
    rw [← pow_two, ← hx2]
    exact pow_orderOf_eq_one x
  have hc2V : c * c ∈ V := by
    have h1 : QuotientGroup.mk' V (c * c) = 1 := by
      rw [map_mul, ← hx']
      exact hx2'
    have h2 : c * c ∈ (QuotientGroup.mk' V).ker := MonoidHom.mem_ker.mpr h1
    rwa [QuotientGroup.ker_mk'] at h2
  rw [hx']
  exact Subgroup.mem_map.mpr ⟨c, ⟨hc, hc2V⟩, rfl⟩

/-- `C/V` is abelian. -/
theorem map_quotient_comm (V C : Subgroup G) [V.Normal]
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) :
    ∀ x ∈ C.map (QuotientGroup.mk' V), ∀ y ∈ C.map (QuotientGroup.mk' V), x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
  obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp hy
  have hx' : x = QuotientGroup.mk' V a := hax.symm
  have hy' : y = QuotientGroup.mk' V b := hby.symm
  rw [hx', hy', ← map_mul, ← map_mul, ← hCab a ha b hb]

/-- The second level `C₂ = {c ∈ C | c² ∈ V}` is normal in `G`. -/
theorem normal_level2 (V C : Subgroup G) [V.Normal]
    (hC : C = Subgroup.centralizer ((V : Set G)))
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (hexp : ∀ x ∈ V, x * x = 1) :
    (level2 V C hC hCab hexp).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨hxC, hx2⟩ := hx
  refine ⟨(C_normal V C inferInstance hC).conj_mem x hxC g, ?_⟩
  have h1 : g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
  rw [h1]
  exact (inferInstance : V.Normal).conj_mem (x * x) hx2 g

/-- `|G ⧸ V| < |G|` when `V` is non-trivial. -/
theorem card_quotient_lt_card (V : Subgroup G) [V.Normal] (hcard : Nat.card V = 8) :
    Nat.card (G ⧸ V) < Nat.card G := by
  have h1 : Nat.card G = Nat.card (G ⧸ V) * Nat.card V :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup V
  rw [hcard] at h1
  haveI : Nonempty (G ⧸ V) := ⟨1⟩
  have h2 : 0 < Nat.card (G ⧸ V) := Nat.card_pos
  omega


/-! ## The general statement, by strong induction on `|G|`

Peterfalvi I §3, Proposition 2 states that in the configuration (without the hypothesis
`Inv(G) = V#`) there is an involution of `G` outside `C`.  We prove it by strong induction on
`|G|`, the induction step being applied to `G/V` (where the first level is `C₂/C₁ ≅ V`);
under the contrary hypothesis `Inv(G) = V#` the paper's computation (steps 1-9 of §3 Prop. 2)
gives a contradiction: `(ts)⁴` is an element `c₁` of `C_m` for which the element `c₁⁻¹` lies in
the image of `c ↦ c^b c` (`b = (ts)²`), so that the coset `bC` contains an involution, and `b ∈ C`
— but `b`'s image in `G/C ≅ GL(3,2)` is a transvection. -/

/-- **Peterfalvi I §3, Proposition 2.**  In the abelian configuration, `G` has an involution
outside `C = C_G(V)`. -/
theorem prop2_aux.{u} (k : ℕ) : ∀ (G : Type u) [Group G] [Finite G], Nat.card G = k →
    ∀ (V C : Subgroup G) (hV : V.Normal) (hcard : Nat.card V = 8)
      (hexp : ∀ x ∈ V, x * x = 1) (hC : C = Subgroup.centralizer ((V : Set G)))
      (hC2 : IsPGroup 2 ↥C) (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V)
      (hAut : ActsAsAut V hV) (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x),
      ∃ u : G, orderOf u = 2 ∧ u ∉ C := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro G _ _ hk V C hV hcard hexp hC hC2 hinv hAut hCab
    by_cases hout : ∃ u : G, orderOf u = 2 ∧ u ∉ C
    · exact hout
    · -- all involutions of `G` lie in `C`; this is the situation of the paper's computation
      push_neg at hout
      haveI : V.Normal := hV
      -- An element of `C` acts trivially by conjugation on `V`.
      have hconj_mem_C : ∀ z ∈ C, MulAut.conjNormal (H := V) z = 1 := by
        intro z hz
        apply MulEquiv.ext
        intro v
        rw [MulAut.one_apply]
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        have hzv : z * (v : G) = (v : G) * z :=
          ((mem_C_iff V C hC z).mp hz (v : G) v.2).symm
        rw [hzv, mul_assoc, mul_inv_cancel, mul_one]
      by_cases hexpC : ∀ c ∈ C, c * c = 1
      · -- ## Case A: `C` has exponent two, hence is elementary abelian
        -- Then `C ⊆ Ω₁(C) = V`.  The preimage `t` of an involution of `G/C ≅ Aut(V) = GL(3,2)`
        -- satisfies `t * t ∈ C ⊆ V`; either `t * t = 1`, so that `t` is an involution outside
        -- `C`, or `t * t ∈ V#` is a witness for `abelian_contra`.
        have hCV : ∀ x ∈ C, x ∈ V := by
          intro x hx
          rcases eq_or_ne x 1 with h1 | h1
          · rw [h1]; exact V.one_mem
          · exact hinv x hx (orderOf_eq_prime (by rw [pow_two]; exact hexpC x hx) h1)
        obtain ⟨e⟩ := Work.Hering.Step5.iso_fin3 hcard
          (fun x : ↥V => Subtype.ext (by simpa using hexp x x.2))
        obtain ⟨t, ht⟩ := hAut (tauV V e)
        have htc : MulAut.conjNormal (H := V) t = tauV V e := by
          apply MulEquiv.ext
          intro v
          apply Subtype.ext
          rw [MulAut.conjNormal_apply]
          exact (congrArg Subtype.val (ht v)).symm
        have ht2C : t * t ∈ C := by
          apply mem_C_of_conjNormal_eq_one V C hC
          intro x
          rw [map_mul, htc, MulAut.mul_apply, ← MulAut.mul_apply, tauV_mul_self,
            MulAut.one_apply]
        have htC : t ∉ C := by
          intro htcin
          have h1 := hconj_mem_C t htcin
          rw [htc] at h1
          exact tauV_ne_one V e h1
        have ht_ne_one : t ≠ 1 := fun h => htC (h ▸ C.one_mem)
        have ht2V : t * t ∈ V := hCV (t * t) ht2C
        by_cases ht2 : t * t = 1
        · exact absurd (hout t (orderOf_eq_prime (by rw [pow_two]; exact ht2) ht_ne_one)) htC
        · exact (abelian_contra V C hcard hexp hC hC2 hinv hAut hCab hout
            ⟨t, htC, ht2V, ht2⟩).elim
      · -- ## Case B: `C` has an element of order at least four
        -- The quotient `G/V` satisfies the configuration again, with `V̄ = C₂/V` the image of
        -- the second level `C₂` and `C̄ = C/V`; the induction hypothesis produces an involution
        -- of `G/V` outside `C/V`, i.e. an element `q ∉ C` with `q * q ∈ V#`.
        push_neg at hexpC
        obtain ⟨c₀, hc₀C, hc₀ne⟩ := hexpC
        have hne : ∃ c ∈ C, c * c ≠ 1 := ⟨c₀, hc₀C, hc₀ne⟩
        have hsq : ∀ v ∈ V, ∃ x ∈ level2 V C hC hCab hexp, x * x = v :=
          fun v hv => sq_level2_surj V C hcard hexp hC hC2 hinv hAut hCab hne hv
        haveI : (level2 V C hC hCab hexp).Normal := normal_level2 V C hC hCab hexp
        have hVbar_normal : ((level2 V C hC hCab hexp).map (QuotientGroup.mk' V)).Normal :=
          inferInstance
        have hVbar_card :
            Nat.card ↥((level2 V C hC hCab hexp).map (QuotientGroup.mk' V)) = 8 :=
          card_map_level2 V C hcard hexp hC hC2 hinv hAut hCab hne
        have hVbar_exp : ∀ x ∈ (level2 V C hC hCab hexp).map (QuotientGroup.mk' V),
            x * x = 1 := map_level2_sq_one V C hC hCab hexp
        have hCbar_eq : (C.map (QuotientGroup.mk' V))
            = Subgroup.centralizer
              (((level2 V C hC hCab hexp).map (QuotientGroup.mk' V) : Set (G ⧸ V))) :=
          centralizer_map_level2 V C hC hCab hexp hsq
        have hCbar_2 : IsPGroup 2 ↥(C.map (QuotientGroup.mk' V)) :=
          isPGroup_map_quotient V C hC2
        have hCbar_inv : ∀ x ∈ C.map (QuotientGroup.mk' V), orderOf x = 2 →
            x ∈ (level2 V C hC hCab hexp).map (QuotientGroup.mk' V) :=
          fun x hx hx2 => orderOf_two_mem_map_level2 V C hC hCab hexp hinv hx hx2
        have hCbar_ab : ∀ x ∈ C.map (QuotientGroup.mk' V),
            ∀ y ∈ C.map (QuotientGroup.mk' V), x * y = y * x :=
          map_quotient_comm V C hCab
        have hAutbar : ActsAsAut ((level2 V C hC hCab hexp).map (QuotientGroup.mk' V))
            hVbar_normal :=
          actsAsAut_map_level2 V C hC hexp hinv hCab hsq hAut hVbar_normal
        haveI : Finite (G ⧸ V) :=
          Finite.of_surjective (QuotientGroup.mk' V) (QuotientGroup.mk'_surjective V)
        have hlt : Nat.card (G ⧸ V) < k := by
          rw [← hk]
          exact card_quotient_lt_card V hcard
        obtain ⟨u, hu2, huC⟩ :=
          ih (Nat.card (G ⧸ V)) hlt (G ⧸ V) rfl
            ((level2 V C hC hCab hexp).map (QuotientGroup.mk' V))
            (C.map (QuotientGroup.mk' V)) hVbar_normal hVbar_card hVbar_exp hCbar_eq hCbar_2
            hCbar_inv hAutbar hCbar_ab
        obtain ⟨q, hq⟩ := QuotientGroup.mk'_surjective V u
        have hqC : q ∉ C := by
          intro hqc
          exact huC (hq ▸ Subgroup.mem_map.mpr ⟨q, hqc, rfl⟩)
        have hq2V : q * q ∈ V := by
          have hu2' : u * u = 1 := by
            rw [← pow_two, ← hu2]
            exact pow_orderOf_eq_one u
          have h1 : QuotientGroup.mk' V (q * q) = 1 := by
            rw [map_mul, hq]
            exact hu2'
          have h2 : q * q ∈ (QuotientGroup.mk' V).ker := MonoidHom.mem_ker.mpr h1
          rwa [QuotientGroup.ker_mk'] at h2
        have hq2ne : q * q ≠ 1 := by
          intro h1
          have hq1 : q ≠ 1 := fun h => hqC (h ▸ C.one_mem)
          have h2 : q ^ 2 = 1 := by rw [pow_two]; exact h1
          exact hqC (hout q (orderOf_eq_prime h2 hq1))
        exact (abelian_contra V C hcard hexp hC hC2 hinv hAut hCab hout
          ⟨q, hqC, hq2V, hq2ne⟩).elim

/-- **The abelian case of the hard core of Hering's theorem** (Peterfalvi I, Ch. IV §3,
Proposition 2 and the contradiction it entails): no finite group carries the abelian
version of the reduced configuration of Hering's theorem. -/
theorem abelian_case {G : Type*} [Group G] [Finite G] (V C : Subgroup G) (hV : V.Normal)
    (hcard : Nat.card V = 8) (hexp : ∀ x ∈ V, x * x = 1)
    (hC : C = Subgroup.centralizer ((V : Set G)))
    (hC2 : IsPGroup 2 ↥C)
    (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V)
    (hAut : ActsAsAut V hV)
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hnoinv : ∀ u : G, orderOf u = 2 → u ∈ C) : False := by
  obtain ⟨u, h2, huC⟩ := prop2_aux (Nat.card G) G rfl V C hV hcard hexp hC hC2 hinv hAut hCab
  exact huC (hnoinv u h2)

end Work.Hering.HardCore
