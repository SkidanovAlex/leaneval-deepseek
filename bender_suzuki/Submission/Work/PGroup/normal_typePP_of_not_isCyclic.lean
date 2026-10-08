/-
# A non-cyclic finite odd `p`-group has a normal subgroup of type `(p,p)`

`Work.PGroup.normal_typePP_of_not_isCyclic`: let `G` be a finite group, `p` an odd prime and
`P ≤ G` a non-cyclic `p`-subgroup.  Then `P` contains a subgroup `W` which is normal in `P` and
which is elementary abelian of order `p ^ 2` — "of type `(p,p)`" in the sense of
`Work.LocalPrelim.IsTypePP`.

The proof (strong induction on `|X|` for a finite `p`-group `X`, `p` odd, in
`exists_normal_typePP_aux`) is the classical one:

* if the centre `Z(X)` is **not cyclic**, apply `Work.ETheorems.exists_isTypePP_le` to the
  non-cyclic abelian `p`-group `Z(X)`: the resulting elementary abelian subgroup `B ≤ Z(X)` is
  central, hence normal in `X`;
* if `Z(X)` **is cyclic**, pick `z ∈ Z(X)` of order `p` and put `K = ⟨z⟩`.  Then `X / K` is again
  a non-cyclic `p`-group of strictly smaller order, so by induction it has a normal elementary
  abelian subgroup `W̄` of order `p ^ 2`.  Its preimage `V ⊴ X` satisfies `K ≤ V` and
  `V / K ≅ (p,p)`, so `|V| = p ^ 3` while `[V,V] ≤ K ≤ Z(V)` and `V ^ p ≤ K`: `V` has class at
  most two modulo a central subgroup of exponent `p`.  For `p` odd the `p`-th power map on `V` is
  a homomorphism (`Work.Coprime.tto_pow_mul_eq_commutator_pow`), so `Ω = {v ∈ V | v ^ p = 1}` is a
  characteristic subgroup of `V`, hence normal in `X`, and
  `Work.PGroup.omega_card_le_of_class_two` gives `|V| ≤ |Ω| · |K|`, i.e. `|Ω| ≥ p ^ 2`;
* finally `Work.PGroup.exists_elementaryAbelian_card_prime_sq_of_exponent_pp` turns a normal
  subgroup of a finite `p`-group that has exponent `p` and order at least `p ^ 2` into a normal
  elementary abelian subgroup of order exactly `p ^ 2`.

The three ingredients are proved in the modules imported below and are used as black boxes here.
-/
import Mathlib
import Submission.Work.LocalPrelim.Defs
import Submission.Work.PGroup.Basic
import Submission.Work.ETheorems.exists_isTypePP_le
import Submission.Work.PGroup.exists_elementaryAbelian_card_prime_sq_of_exponent_pp
import Submission.Work.PGroup.omega_card_le_of_class_two
import Submission.Work.Coprime.trivial_of_trivial_on_omega1
import Submission.Work.LocalPrelim.ft8_13

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical Pointwise commutatorElement
open Subgroup

noncomputable section

namespace Work.PGroup

variable {p : ℕ}

/-! ### Elementary helpers -/

/-- A subgroup of the centre is normal. -/
private theorem normal_of_le_center {G : Type*} [Group G] {K : Subgroup G}
    (hK : K ≤ Subgroup.center G) : K.Normal :=
  Subgroup.Normal.mk fun n hn g => by
    have h := Subgroup.mem_center_iff.mp (hK hn) g
    rw [h, mul_inv_cancel_right]
    exact hn

/-- **Auxiliary (strong) induction**: every non-cyclic finite `p`-group with `p` odd has a normal
elementary abelian subgroup of order `p ^ 2`. -/
private theorem exists_normal_typePP_aux (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    ∀ (n : ℕ) (X : Type*) [Group X] [Finite X], Nat.card X = n → IsPGroup p X → ¬ IsCyclic X →
      ∃ W : Subgroup X, W.Normal ∧ IsElementaryAbelian p W ∧ Nat.card W = p ^ 2 := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n' ih X _ _ hcardX hXp hnc
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hZ : IsCyclic ↥(Subgroup.center X)
  · -- ## Case: the centre is cyclic
    haveI hXnt : Nontrivial X := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hss
      haveI := hss
      exact hnc (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨1, le_antisymm le_top (by
        intro x _
        rw [Subsingleton.elim x 1]
        exact Subgroup.mem_zpowers 1)⟩)
    -- an element of the centre of order `p`
    obtain ⟨z, hzmem, hzord⟩ : ∃ z : X, z ∈ Subgroup.center X ∧ orderOf z = p := by
      have hnt : Nontrivial ↥(Subgroup.center X) := hXp.center_nontrivial
      have hdvd : p ∣ Nat.card ↥(Subgroup.center X) := by
        obtain ⟨k, hk0, hk⟩ :=
          (hXp.to_subgroup (Subgroup.center X)).nontrivial_iff_card.mp hnt
        exact hk.symm ▸ dvd_pow_self p hk0.ne'
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p hdvd
      refine ⟨(w : X), w.2, ?_⟩
      rw [Subgroup.orderOf_coe]
      exact hw
    let K : Subgroup X := Subgroup.zpowers z
    have hKle : K ≤ Subgroup.center X := by
      intro x hx
      rw [Subgroup.mem_zpowers_iff] at hx
      obtain ⟨m, rfl⟩ := hx
      exact Subgroup.zpow_mem (Subgroup.center X) hzmem m
    haveI hKn : K.Normal := normal_of_le_center hKle
    have hKcard : Nat.card ↥K = p := by
      show Nat.card ↥(Subgroup.zpowers z) = p
      rw [Nat.card_zpowers, hzord]
    have hXbP : IsPGroup p (X ⧸ K) := hXp.to_quotient K
    have hXbNC : ¬ IsCyclic (X ⧸ K) := by
      intro hcyc
      haveI : IsCyclic (X ⧸ K) := hcyc
      haveI : IsMulCommutative X :=
        (QuotientGroup.mk' K).isMulCommutative_of_isCyclic_of_ker_le_center
          (by rw [QuotientGroup.ker_mk']; exact hKle)
      have hcent : Subgroup.center X = ⊤ := Subgroup.center_eq_top
      haveI hcycTop : IsCyclic ↥(⊤ : Subgroup X) := hcent ▸ hZ
      exact hnc (isCyclic_of_surjective (Subgroup.topEquiv (G := X)).toMonoidHom
        (MulEquiv.surjective _))
    -- the order strictly drops when passing to `X / K`
    have hcard_lt : Nat.card (X ⧸ K) < n' := by
      have hmul : Nat.card (X ⧸ K) * p = n' := by
        rw [← hcardX, ← Subgroup.index_eq_card K, ← hKcard, Subgroup.index_mul_card K]
      have hle : Nat.card (X ⧸ K) * 2 ≤ n' := by
        rw [← hmul]
        exact Nat.mul_le_mul_left _ hp.two_le
      have h2eq : Nat.card (X ⧸ K) * 2 = Nat.card (X ⧸ K) + Nat.card (X ⧸ K) := by ring
      have hpos : 0 < Nat.card (X ⧸ K) := Nat.card_pos
      omega
    obtain ⟨Wbar, hWbarN, hWbarEA, hWbarcard⟩ :=
      ih (Nat.card (X ⧸ K)) hcard_lt (X ⧸ K) rfl hXbP hXbNC
    -- the lift of `W̄` to `X`
    let V : Subgroup X := Wbar.comap (QuotientGroup.mk' K)
    have hVn : V.Normal := hWbarN.comap _
    have hKleV : K ≤ V := fun x hx => by
      show QuotientGroup.mk' K x ∈ Wbar
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
      exact Wbar.one_mem
    have hmap : Subgroup.map (QuotientGroup.mk' K) V = Wbar :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective K) Wbar
    let φ : ↥V →* X ⧸ K := (QuotientGroup.mk' K).comp V.subtype
    have hφker : φ.ker = K.subgroupOf V := by
      ext x
      show QuotientGroup.mk' K (x : X) = 1 ↔ (x : X) ∈ K
      rw [QuotientGroup.mk'_apply]
      exact QuotientGroup.eq_one_iff (x : X)
    have hφrange : φ.range = Wbar := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_map]
      have htop : Subgroup.map V.subtype (⊤ : Subgroup ↥V) = V := by
        rw [← Subgroup.top_subgroupOf (H := V), Subgroup.subgroupOf_map_subtype, top_inf_eq]
      rw [htop, hmap]
    have hquotcard : Nat.card (↥V ⧸ (K.subgroupOf V)) = Nat.card ↥Wbar := by
      rw [← hφker, ← hφrange]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    -- the three hypotheses of the class-two power lemma
    have hcent : K.subgroupOf V ≤ Subgroup.center ↥V := by
      intro c hc
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      show (y : X) * (((c : ↥V)) : X) = (((c : ↥V)) : X) * (y : X)
      exact Subgroup.mem_center_iff.mp (hKle (Subgroup.mem_subgroupOf.mp hc)) (y : X)
    have hmem_range : ∀ x : ↥V, φ x ∈ Wbar := fun x => by
      rw [← hφrange, MonoidHom.range_eq_map]
      exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_top x, rfl⟩
    have hcomm : ∀ x y : ↥V, x * y * x⁻¹ * y⁻¹ ∈ K.subgroupOf V := by
      intro x y
      rw [← commutatorElement_def, ← hφker, MonoidHom.mem_ker, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      simpa using congrArg Subtype.val
        (isMulCommutative_iff.mp hWbarEA.1 ⟨φ x, hmem_range x⟩ ⟨φ y, hmem_range y⟩)
    have hKexp : ∀ c : K.subgroupOf V, c ^ p = 1 := by
      intro c
      have h1 : (Subgroup.subgroupOfEquivOfLe hKleV c) ^ p = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one, ← hKcard]
        exact orderOf_dvd_natCard _
      have h2 := congrArg (Subgroup.subgroupOfEquivOfLe hKleV).symm h1
      rwa [map_pow, MulEquiv.symm_apply_apply, map_one] at h2
    have hpow : ∀ x : ↥V, x ^ p ∈ K.subgroupOf V := by
      intro x
      rw [← hφker, MonoidHom.mem_ker, map_pow]
      show φ x ^ p = 1
      simpa using congrArg Subtype.val (hWbarEA.2 ⟨φ x, hmem_range x⟩)
    obtain ⟨ΩV, hΩVmem, hΩVn, hΩVcard⟩ := omega_card_le_of_class_two hp hodd hcent hcomm hKexp hpow
    -- cardinality of `V` and of `K ↾ V`
    have hKsubcard : Nat.card ↥(K.subgroupOf V) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKleV).toEquiv, hKcard]
    have hVcard : Nat.card ↥V = p * p ^ 2 := by
      have h1 : Nat.card ↥V = (K.subgroupOf V).index * Nat.card ↥(K.subgroupOf V) :=
        (Subgroup.index_mul_card (K.subgroupOf V)).symm
      rw [Subgroup.index_eq_card] at h1
      rw [h1, hquotcard, hKsubcard, hWbarcard]
      ring
    have hΩVcard' : p ^ 2 ≤ Nat.card ↥ΩV := by
      have h1 : Nat.card ↥V ≤ Nat.card ↥ΩV * Nat.card ↥(K.subgroupOf V) := hΩVcard
      rw [hKsubcard, hVcard, show p * p ^ 2 = p ^ 2 * p by ring] at h1
      exact Nat.le_of_mul_le_mul_right h1 hp.pos
    -- transport `ΩV` to a normal subgroup of `X`
    have hΩn : (ΩV.map V.subtype).Normal := by
      refine Subgroup.Normal.mk fun m hm g => ?_
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hm
      have hmemV : g * (v : X) * g⁻¹ ∈ V := hVn.conj_mem (v : X) v.2 g
      refine Subgroup.mem_map.mpr ⟨⟨g * (v : X) * g⁻¹, hmemV⟩, ?_, rfl⟩
      rw [hΩVmem]
      apply Subtype.ext
      show (g * (v : X) * g⁻¹) ^ p = 1
      have hv' : (v : X) ^ p = 1 := by
        simpa using congrArg Subtype.val ((hΩVmem v).mp hv)
      rw [show g * (v : X) * g⁻¹ = MulAut.conj g (v : X) by rw [MulAut.conj_apply],
        ← map_pow (MulAut.conj g) (v : X) p, hv', map_one]
    have hΩexp : ∀ w : ↥(ΩV.map V.subtype), w ^ p = 1 := by
      intro w
      obtain ⟨v, hv, hvw⟩ := Subgroup.mem_map.mp w.2
      apply Subtype.ext
      show (w : X) ^ p = 1
      have hv' : v ^ p = 1 := (hΩVmem v).mp hv
      rw [← hvw, ← map_pow, hv', map_one]
    have hΩcard : p ^ 2 ≤ Nat.card ↥(ΩV.map V.subtype) := by
      rw [← Nat.card_congr (Subgroup.equivMapOfInjective ΩV V.subtype
        (fun a b h => Subtype.ext h)).toEquiv]
      exact hΩVcard'
    obtain ⟨W, -, hWN, hWEA, hWcard⟩ := exists_elementaryAbelian_card_prime_sq_of_exponent_pp hp hXp hΩn hΩexp hΩcard
    exact ⟨W, hWN, hWEA, hWcard⟩
  · -- ## Case: the centre is not cyclic
    obtain ⟨B, hBle, hBEA, hBcard⟩ :=
      Work.ETheorems.exists_isTypePP_le (G := X) hp hodd (hXp.to_subgroup (Subgroup.center X))
        (inferInstance : IsMulCommutative ↥(Subgroup.center X)) hZ
    exact ⟨B, normal_of_le_center hBle, hBEA, hBcard⟩

/-- A non-cyclic finite `p`-group with `p` odd has a **normal** subgroup of type `(p,p)`: a normal subgroup `W` which is elementary abelian of order `p ^ 2`.  (Written for a subgroup `P` of an ambient finite group; `(W.subgroupOf P).Normal` says `W ⊴ P`.) -/
theorem normal_typePP_of_not_isCyclic {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) {P : Subgroup G} (hPp : IsPGroup p P)
    (hnc : ¬ IsCyclic ↥P) :
    ∃ W : Subgroup G, W ≤ P ∧ (W.subgroupOf P).Normal ∧ Work.LocalPrelim.IsTypePP p W := by
  obtain ⟨W', hW'N, hW'EA, hW'card⟩ :=
    exists_normal_typePP_aux p hp hodd (Nat.card ↥P) P rfl hPp hnc
  have hsub : (W'.map P.subtype).subgroupOf P = W' := by
    rw [← Subgroup.comap_subtype (W'.map P.subtype) P, Subgroup.comap_map_eq,
      Subgroup.ker_subtype P, sup_bot_eq]
  have hEA : IsElementaryAbelian p (W'.map P.subtype) :=
    isElementaryAbelian_map P.subtype_injective hW'EA
  have hcard : Nat.card ↥(W'.map P.subtype) = p ^ 2 := by
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective W' P.subtype
      (fun a b h => Subtype.ext h)).toEquiv]
    exact hW'card
  exact ⟨W'.map P.subtype, Subgroup.map_subtype_le W', by rw [hsub]; exact hW'N, hEA, hcard⟩

end Work.PGroup
