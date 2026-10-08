import Mathlib
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmF.ChV12.exists_linear

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi II, Ch. V §1: a nontrivial linear character of `D` trivial on `K`

In the split rank-one situation `H = Q ⋊ D` (`D = H ⊓ H^t = twoPoint H t`, `t` an involution
outside `H`), put

* `V = C_D(t) = centD H t`,
* `K = J(D,t) = Kset H t = {x ∈ D | t x t⁻¹ = x⁻¹}`, and `K̄ = ⟨K⟩ = Ksub H t`.

The paper (proof of Théorème G, p. 257) needs a linear character `λ ≠ 1` of `H` with
`QK ⊆ ker λ`, "which exists because `H/QK ≅ V` is solvable and `≠ 1`".

This file provides the `D`-part of that statement: **if `V ≠ 1` and `K` is a subgroup
(`Ksub H t = Kset H t` as sets), then `D` has a nontrivial linear character `χ : D →* ℂˣ`
which is trivial on `K`.**

The ingredients are the classical facts of Peterfalvi App. I (1)(b), (4) for an involution `t`
acting on the odd-order group `D`:

* `V ⊓ K = ⊥` (an element both inverted and fixed by `t` has order dividing `2`);
* `V ≤ N_G(K)` (for `v ∈ V`, `k ∈ K`, conjugation `v k v⁻¹` is again inverted by `t`);
* `V · K = D` — the multiplication map `V × K → D` is injective and, by the counting
  `|V| · |K| = |D|` (`Work.ThmF.card_centD_mul_card_Kset`), it is a bijection;
* consequently `D ≤ N_G(K)`, i.e. `K` is normal in `D` (App. I (4)).

Then `D/K` is a finite group of odd order and `≠ 1` (its order is `|V|`), so Feit–Thompson
makes it solvable and a nontrivial finite solvable group has a nontrivial homomorphism into
`ℂˣ` (`Work.ThmF.ChV12.exists_monoidHom_units_ne_one`); pulling back along `D → D/K` gives the
required `χ`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ThmF.ChV12

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem chi_on_D {G : Type} [Group G] [Fintype G] (hFT : FeitThompsonProp) {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t) (hV : centD H t ≠ ⊥) (hKset : (Ksub H t : Set G) = Kset H t) : ∃ χ : ↥(twoPoint H t) →* ℂˣ, χ ≠ 1 ∧ ∀ x : ↥(twoPoint H t), (x : G) ∈ Kset H t → χ x = 1 := by
  classical
  -- `K̄ = ⟨K⟩ = K` as sets
  have hKm : ∀ x : G, x ∈ Ksub H t ↔ x ∈ Kset H t := fun x => by
    show x ∈ (Ksub H t : Set G) ↔ x ∈ Kset H t
    rw [hKset]
  -- ## Step 1: `V ⊓ K̄ = ⊥`
  have hVK : centD H t ⊓ Ksub H t = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxV, hxK⟩ := hx
    have hxK' : x ∈ Kset H t := (hKm x).mp hxK
    obtain ⟨hxD, hxinv⟩ := hxK'
    obtain ⟨-, hxcent⟩ := Subgroup.mem_inf.mp hxV
    have htx : t * x = x * t := (Subgroup.mem_centralizer_iff.mp hxcent) t (by simp)
    have hfix : t * x * t⁻¹ = x := by rw [htx, mul_assoc, mul_inv_cancel, mul_one]
    have hx1 : x = x⁻¹ := (hxinv.symm.trans hfix).symm
    have hxx : x * x = 1 := by
      nth_rewrite 2 [hx1]
      rw [mul_inv_cancel]
    have ho2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hxx)
    have hodD : orderOf x ∣ Nat.card ↥(twoPoint H t) := by
      have h1 : orderOf (⟨x, hxD⟩ : ↥(twoPoint H t)) ∣ Nat.card ↥(twoPoint H t) :=
        orderOf_dvd_natCard _
      rwa [← Subgroup.orderOf_coe] at h1
    rcases (Nat.dvd_prime Nat.prime_two).mp ho2 with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      have h2dvd : 2 ∣ Nat.card ↥(twoPoint H t) := h1 ▸ hodD
      exact (Nat.not_even_iff_odd.mpr (split_odd_card_twoPoint h)) (even_iff_two_dvd.mpr h2dvd)
  -- ## Step 2: `V ≤ N_G(K̄)`
  have hVN : centD H t ≤ Subgroup.normalizer (Ksub H t : Set G) := by
    have hconj_t : ∀ w ∈ centD H t, t * w * t⁻¹ = w := by
      intro w hw
      have hwt : t * w = w * t :=
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hw).2) t (by simp)
      rw [hwt, mul_assoc, mul_inv_cancel, mul_one]
    have key : ∀ v ∈ centD H t, ∀ y ∈ Kset H t, v * y * v⁻¹ ∈ Ksub H t := by
      intro v hv y hy
      obtain ⟨hyD, hyinv⟩ := hy
      obtain ⟨hvD, -⟩ := Subgroup.mem_inf.mp hv
      have hvt : t * v * t⁻¹ = v := hconj_t v hv
      have hvtinv : t * v⁻¹ * t⁻¹ = v⁻¹ := by
        rw [show t * v⁻¹ * t⁻¹ = (t * v * t⁻¹)⁻¹ by group, hvt]
      have hmemD : v * y * v⁻¹ ∈ twoPoint H t :=
        (twoPoint H t).mul_mem ((twoPoint H t).mul_mem hvD hyD) ((twoPoint H t).inv_mem hvD)
      have hinv : t * (v * y * v⁻¹) * t⁻¹ = (v * y * v⁻¹)⁻¹ := by
        rw [show t * (v * y * v⁻¹) * t⁻¹
              = (t*v*t⁻¹) * (t*y*t⁻¹) * (t*v⁻¹*t⁻¹) by group, hvt, hyinv, hvtinv]
        group
      have hmem : v * y * v⁻¹ ∈ (Ksub H t : Set G) := by
        rw [hKset]; exact ⟨hmemD, hinv⟩
      exact hmem
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact key v hv x ((hKm x).mp hx)
    · intro hx
      have hx' : v * x * v⁻¹ ∈ Kset H t := (hKm _).mp hx
      have h2 := key v⁻¹ ((centD H t).inv_mem hv) (v * x * v⁻¹) hx'
      have hconj : v⁻¹ * (v * x * v⁻¹) * v⁻¹⁻¹ = x := by group
      rwa [hconj] at h2
  -- ## Step 3: `D = V · K̄` (App. I (1)(b))
  let φ : ↥(centD H t) × ↥(Kset H t) → ↥(twoPoint H t) := fun p =>
    ⟨(p.1 : G) * (p.2 : G),
      (twoPoint H t).mul_mem (centD_le_twoPoint t p.1.2) (Kset_subset H t p.2.2)⟩
  have hφinj : Function.Injective φ := by
    intro p q hpq
    have hval : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) :=
      congrArg (fun z : ↥(twoPoint H t) => (z : G)) hpq
    have hmem : (q.1 : G)⁻¹ * (p.1 : G) ∈ centD H t ⊓ Ksub H t := by
      refine ⟨(centD H t).mul_mem ((centD H t).inv_mem q.1.2) p.1.2, ?_⟩
      have hEq : (q.1 : G)⁻¹ * (p.1 : G) = (q.2 : G) * (p.2 : G)⁻¹ := by
        have h := congrArg (fun z => (q.1 : G)⁻¹ * z * (p.2 : G)⁻¹) hval
        simpa [mul_assoc] using h
      rw [hEq]
      exact (Ksub H t).mul_mem (Kset_le_Ksub H t q.2.2)
        ((Ksub H t).inv_mem (Kset_le_Ksub H t p.2.2))
    rw [hVK] at hmem
    have hone : (q.1 : G)⁻¹ * (p.1 : G) = 1 := Subgroup.mem_bot.mp hmem
    have hq1 : (p.1 : G) = (q.1 : G) := by
      have := congrArg (fun z => (q.1 : G) * z) hone
      simpa using this
    have hp2 : (p.2 : G) = (q.2 : G) := by
      have h2 : (p.1 : G) * (p.2 : G) = (p.1 : G) * (q.2 : G) := by rw [hval, hq1]
      exact mul_left_cancel h2
    exact Prod.ext (Subtype.ext hq1) (Subtype.ext hp2)
  have hφsurj : Function.Surjective φ := by
    have hcard : Nat.card (↥(centD H t) × ↥(Kset H t)) = Nat.card ↥(twoPoint H t) := by
      rw [Nat.card_prod, Nat.card_coe_set_eq]
      exact card_centD_mul_card_Kset (IsSplitRankOne.toData h)
    have himg : (φ '' (Set.univ : Set (↥(centD H t) × ↥(Kset H t)))).ncard
        = Nat.card (↥(centD H t) × ↥(Kset H t)) := by
      rw [Set.ncard_image_of_injective _ hφinj, Set.ncard_univ]
    have hle : (Set.univ : Set ↥(twoPoint H t)).ncard
        ≤ (φ '' (Set.univ : Set (↥(centD H t) × ↥(Kset H t)))).ncard := by
      rw [Set.ncard_univ, himg]
      exact hcard.ge
    have hEq : φ '' (Set.univ : Set (↥(centD H t) × ↥(Kset H t)))
        = (Set.univ : Set ↥(twoPoint H t)) :=
      Set.eq_of_subset_of_ncard_le (Set.subset_univ _) hle
    intro d
    have hd : d ∈ φ '' (Set.univ : Set (↥(centD H t) × ↥(Kset H t))) := by
      rw [hEq]; exact Set.mem_univ d
    obtain ⟨p, -, hp⟩ := hd
    exact ⟨p, hp⟩
  -- ## Step 4: `K̄ ⊴ D`
  have hDN : twoPoint H t ≤ Subgroup.normalizer (Ksub H t : Set G) := by
    intro d hd
    obtain ⟨p, hp⟩ := hφsurj ⟨d, hd⟩
    have hval : d = (p.1 : G) * (p.2 : G) := (congrArg Subtype.val hp).symm
    rw [hval]
    exact (Subgroup.normalizer (Ksub H t : Set G)).mul_mem (hVN p.1.2)
      (Subgroup.le_normalizer (Kset_le_Ksub H t p.2.2))
  haveI hKDn : ((Ksub H t).subgroupOf (twoPoint H t)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Ksub_le_twoPoint t)).mpr hDN
  -- ## Step 5: the quotient `D/K̄` is a nontrivial finite odd-order group, hence solvable
  let KD : Subgroup ↥(twoPoint H t) := (Ksub H t).subgroupOf (twoPoint H t)
  haveI hfin : Fintype (↥(twoPoint H t) ⧸ KD) := Fintype.ofFinite _
  have hAodd : Odd (Nat.card (↥(twoPoint H t) ⧸ KD)) := by
    have hindex : Nat.card ↥(twoPoint H t) = KD.index * Nat.card ↥KD := by
      rw [mul_comm]; exact (Subgroup.card_mul_index KD).symm
    have hdvd : KD.index ∣ Nat.card ↥(twoPoint H t) := ⟨Nat.card ↥KD, hindex⟩
    have hquot : Nat.card (↥(twoPoint H t) ⧸ KD) = KD.index := (Subgroup.index_eq_card KD).symm
    rw [hquot, ← Nat.not_even_iff_odd]
    intro he
    exact (Nat.not_even_iff_odd.mpr (split_odd_card_twoPoint h))
      (even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp he) hdvd))
  haveI hsolv : Group.IsSolvable (↥(twoPoint H t) ⧸ KD) := hFT _ hAodd
  have hnt : Nontrivial (↥(twoPoint H t) ⧸ KD) := by
    obtain ⟨v, hvne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV
    have hvD : (v : G) ∈ twoPoint H t := centD_le_twoPoint t v.2
    refine ⟨1, QuotientGroup.mk' KD ⟨(v : G), hvD⟩, ?_⟩
    intro hcon
    have hmem : (⟨(v : G), hvD⟩ : ↥(twoPoint H t)) ∈ KD :=
      (QuotientGroup.eq_one_iff _).mp (by simpa using hcon.symm)
    have hvK : (v : G) ∈ Ksub H t := Subgroup.mem_subgroupOf.mp hmem
    have hmem2 : (v : G) ∈ centD H t ⊓ Ksub H t := ⟨v.2, hvK⟩
    rw [hVK] at hmem2
    exact hvne (Subtype.ext (Subgroup.mem_bot.mp hmem2))
  -- ## Step 6: conclude
  obtain ⟨φ₀, hφ₀ne⟩ := exists_monoidHom_units_ne_one hnt
  refine ⟨φ₀.comp (QuotientGroup.mk' KD), ?_, ?_⟩
  · intro h1
    apply hφ₀ne
    refine MonoidHom.ext (fun z => ?_)
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective KD z
    have h1x : φ₀ (QuotientGroup.mk' KD x) = 1 := by
      have := DFunLike.congr_fun h1 x
      simpa [MonoidHom.comp_apply] using this
    rw [← hx]
    simpa using h1x
  · intro x hxKset
    have hxK : (x : G) ∈ Ksub H t := (hKm (x : G)).mpr hxKset
    have hxKD : x ∈ KD := Subgroup.mem_subgroupOf.mpr hxK
    have hq : QuotientGroup.mk' KD x = 1 := (QuotientGroup.eq_one_iff x).mpr hxKD
    show (φ₀.comp (QuotientGroup.mk' KD)) x = 1
    rw [MonoidHom.comp_apply, hq, map_one]

end Work.ThmF.ChV12
