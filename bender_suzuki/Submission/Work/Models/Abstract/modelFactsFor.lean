import Mathlib
import Submission.Work.Models.Abstract.ModelData
import Submission.Work.Models.Port.BenderSetup
import Submission.Work.Models.Basic
import Submission.Work.Models.Abstract.involutions_subset_U
import Submission.Work.Models.Abstract.exists_conj_eq
import Submission.Work.Models.Abstract.invertedBy_twoPoint
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.mem_sup_of_le_normalizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Models.Abstract.modelFactsFor` — the abstract model facts of a simple Bender group

The `ModelFactsProp` area of the blueprint asks, for a finite simple group `Y` with a strongly
embedded subgroup, for the four structural facts that the three families `PSL(2,2ⁿ)`, `Sz(q)`,
`PSU(3,q)` satisfy:

* `Y` is simple, has 2-rank `≥ 2` and a strongly embedded subgroup,
* the involutions of every strongly embedded `H ≤ Y` commute,
* for every involution `t ∉ H` there is `S ≤ H` with `H = S ⋊ D` (`D = H ⊓ H^t` the two-point
  stabiliser, `S` a normal `2`-subgroup) and `K = J(D,t) = {x ∈ D | x^t = x⁻¹}` is cyclic of order
  `#Inv(H)`.

Here `Work.Models.ModelData G` is the abstract rank-one `(B,N)`-pair of a group with a strongly
embedded subgroup, together with the four model-specific facts: `K₀ = J(T,w) = invertedBy T w` is
cyclic of order `#Inv(B) ≥ 2`, `T` is abelian, `w² = 1`, and the involutions of `U` are central
in `U`.  This file assembles `ModelFactsFor G` from that data:

* the four-group comes from `#Inv(B) ≥ 2`: two distinct involutions of `B` lie in `U`
  (`involutions_subset_U`) and commute (`hUinv`);
* every strongly embedded `H` is a conjugate of `B` (`exists_conj_eq`);
* the two-point stabiliser `D = B ⊓ B^t` of an involution `t ∉ B` is a `B`-conjugate of `T` and
  `J(D,t)` the corresponding conjugate of `K₀ = J(T,w)` (`invertedBy_twoPoint`);
* `U` is a complement of every `B`-conjugate of `T` in `B` (`U_inf_sup_conj_T`), so `U` plays the
  role of the normal `2`-subgroup `S`;
* conjugating by `g` transports all of this from `B` to `H = B^g` (the small transport lemmas
  `conj_inf`, `conj_sup`, `isCyclic_map_conj`, `map_conj_coe`, `ncard_involutions_conj`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.Models.Abstract

/-! ## Elementary transport along conjugation -/

/-- Conjugation is a lattice isomorphism: it commutes with `⊓`. -/
theorem conj_inf {G : Type*} [Group G] (g : G) (X Y : Subgroup G) :
    Submission.Blueprint.conj g (X ⊓ Y)
      = Submission.Blueprint.conj g X ⊓ Submission.Blueprint.conj g Y :=
  Subgroup.map_inf X Y (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

/-- Conjugation commutes with `⊔`. -/
theorem conj_sup {G : Type*} [Group G] (g : G) (X Y : Subgroup G) :
    Submission.Blueprint.conj g (X ⊔ Y)
      = Submission.Blueprint.conj g X ⊔ Submission.Blueprint.conj g Y :=
  Subgroup.map_sup X Y (MulAut.conj g).toMonoidHom

/-- The underlying set of a conjugated subgroup. -/
theorem map_conj_coe {G : Type*} [Group G] (K : Subgroup G) (h : G) :
    ((K.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G)
      = (fun x => h * x * h⁻¹) '' (K : Set G) := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Set.mem_image,
    SetLike.mem_coe]

/-- Cyclicity survives conjugation of a subgroup. -/
theorem isCyclic_map_conj {G : Type*} [Group G] (K : Subgroup G) (g : G) (h : IsCyclic K) :
    IsCyclic (K.map (MulAut.conj g).toMonoidHom) := by
  haveI : IsCyclic ↥K := h
  let e : ↥K ≃* ↥(K.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

/-- The number of elements of a set is unchanged by a conjugation. -/
theorem ncard_image_conj {G : Type*} [Group G] (s : Set G) (g : G) :
    ((fun x => g * x * g⁻¹) '' s).ncard = s.ncard :=
  Set.ncard_image_of_injective s
    (fun x y hxy => (MulAut.conj g).injective (by simpa [MulAut.conj_apply] using hxy))

/-- `orderOf` is invariant under `x ↦ z⁻¹ x z`. -/
theorem orderOf_conj_inv {G : Type*} [Group G] (z a : G) : orderOf (z⁻¹ * a * z) = orderOf a := by
  have h := MulEquiv.orderOf_eq (MulAut.conj z⁻¹) a
  simpa only [MulAut.conj_apply, inv_inv] using h

/-- The number of involutions of a subgroup is unchanged by a conjugation. -/
theorem ncard_involutions_conj {G : Type*} [Group G] (K : Subgroup G) (g : G) :
    (Submission.Blueprint.involutions
        ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)).ncard
      = (Submission.Blueprint.involutions (K : Set G)).ncard := by
  rw [Work.Models.involutions_conj g K]
  exact ncard_image_conj _ g

/-! ## The four-group -/

/-- `#Inv(B) = |K₀| ≥ 2`, and every involution of `B` lies in `U` where involutions are central;
so two distinct involutions of `B` commute: `G` has 2-rank `≥ 2`. -/
theorem hasFourGroup_of_modelData {G : Type*} [Group G] [Finite G] (P : Work.Models.ModelData G) :
    Submission.Blueprint.HasFourGroup G := by
  have hfin : (Submission.Blueprint.involutions (P.B : Set G)).Finite := Set.toFinite _
  have h2 : 2 ≤ (Submission.Blueprint.involutions (P.B : Set G)).ncard := by
    rw [← P.hK0card]; exact P.hK0two
  have h1 : 1 < (Submission.Blueprint.involutions (P.B : Set G)).ncard := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := (Set.one_lt_ncard hfin).mp h1
  have ha2 : a * a = 1 := by
    have h := pow_orderOf_eq_one a
    rw [Work.Models.mem_involutions_iff] at ha
    rw [ha.2] at h
    simpa [pow_two] using h
  have hb2 : b * b = 1 := by
    have h := pow_orderOf_eq_one b
    rw [Work.Models.mem_involutions_iff] at hb
    rw [hb.2] at h
    simpa [pow_two] using h
  have hUa : a ∈ P.U := involutions_subset_U P.toBenderPair ha
  have hUb : b ∈ P.U := involutions_subset_U P.toBenderPair hb
  exact ⟨a, b, ha.2, hb.2, hab, P.hUinv a hUa ha2 b hUb⟩

/-! ## `U` is a complement of every `B`-conjugate of `T` in `B` -/

/-- In a Bender pair, `U` is a complement of `conj b T` in `B` for every `b ∈ B` (so that `U`
plays the role of the normal `2`-subgroup `S` of a rank-one split `BN`-pair).

Write `b = u * t` with `u ∈ U`, `t ∈ T`; then `conj b T = conj u T`.  An element of
`U ⊓ conj u T` is `u y u⁻¹` with `y ∈ T`, and `y = u⁻¹ (u y u⁻¹) u ∈ U ⊓ T = ⊥`.  For the
supremum, both factors lie in `B` and `|U ⊔ conj u T| = |U| · |T| = |B|`. -/
theorem U_inf_sup_conj_T {G : Type*} [Group G] [Finite G] (P : Submission.BenderPair G) {b : G}
    (hb : b ∈ P.B) :
    P.U ⊓ Submission.Blueprint.conj b P.T = ⊥ ∧
      P.U ⊔ Submission.Blueprint.conj b P.T = P.B := by
  have hbB : b ∈ P.U ⊔ P.T := by rw [← P.hB]; exact hb
  obtain ⟨u, hu, t, ht, hbut⟩ :=
    Commons.GroupTheory.Subgroup.mem_sup_of_le_normalizer P.U P.T P.hTnU hbB
  -- `conj b T = conj u T`, since `t ∈ T` fixes `T`.
  have hconj_eq : Submission.Blueprint.conj b P.T = Submission.Blueprint.conj u P.T := by
    rw [hbut, Work.Models.conj_mul,
      Work.Models.conj_self_of_mem_normalizer (Subgroup.le_normalizer ht)]
  have hconj_le_B : Submission.Blueprint.conj u P.T ≤ P.B :=
    calc Submission.Blueprint.conj u P.T ≤ Submission.Blueprint.conj u P.B :=
          Subgroup.map_mono P.T_le_B
      _ = P.B := Work.Models.conj_self_of_mem_normalizer (Subgroup.le_normalizer (P.U_le_B hu))
  -- The infimum.
  have hinf : P.U ⊓ Submission.Blueprint.conj u P.T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf, Work.Models.mem_conj_iff] at hx
    obtain ⟨hxU, hxT⟩ := hx
    have hmem : u⁻¹ * x * u ∈ P.U ⊓ P.T :=
      ⟨P.U.mul_mem (P.U.mul_mem (P.U.inv_mem hu) hxU) hu, hxT⟩
    have h1 : u⁻¹ * x * u = 1 := by
      rw [P.hUT, Subgroup.mem_bot] at hmem; exact hmem
    show x ∈ (⊥ : Subgroup G)
    rw [Subgroup.mem_bot]
    calc x = u * (u⁻¹ * x * u) * u⁻¹ := by group
      _ = 1 := by rw [h1]; group
  -- The supremum, by comparing the orders.
  have hle : P.U ⊔ Submission.Blueprint.conj u P.T ≤ P.B := sup_le P.U_le_B hconj_le_B
  have hcard : Nat.card ↥(P.U ⊔ Submission.Blueprint.conj u P.T) = Nat.card ↥P.B := by
    rw [Commons.GroupTheory.Subgroup.card_sup_of_inf_eq_bot_of_le_normalizer P.U _ ?_ hinf]
    · rw [Work.Models.card_conj, Submission.BenderPair.card_eq_card_U_mul_card_T]
    · exact hconj_le_B.trans P.le_normalizer_U
  have hsup : P.U ⊔ Submission.Blueprint.conj u P.T = P.B :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  exact ⟨by rw [hconj_eq, hinf], by rw [hconj_eq, hsup]⟩

/-! ## The abstract model facts -/

theorem modelFactsFor {G : Type*} [Group G] [Finite G] (P : Work.Models.ModelData G)
    (hs : IsSimpleGroup G) : Work.Models.ModelFactsFor G := by
  refine ⟨hs, hasFourGroup_of_modelData P, ⟨P.B, P.hSemb⟩, ?_⟩
  intro H hH
  -- Every strongly embedded subgroup is a conjugate of the Borel subgroup `B`.
  obtain ⟨g, hg⟩ := exists_conj_eq P.toBenderPair hH
  constructor
  · -- **Involutions of `H` commute.**  Transport them into `B ⊆ U ⊔ T`, where they lie in the
    -- `2`-group `U` and are central in `U`.
    intro a ha b hb
    rw [Work.Models.mem_involutions_iff] at ha hb
    have haH : a ∈ Submission.Blueprint.conj g P.B := by rw [← hg]; exact ha.1
    have hbH : b ∈ Submission.Blueprint.conj g P.B := by rw [← hg]; exact hb.1
    have ha' : g⁻¹ * a * g ∈ Submission.Blueprint.involutions (P.B : Set G) :=
      ⟨Work.Models.mem_conj_iff.mp haH,
        by rw [orderOf_conj_inv, ha.2]⟩
    have hb' : g⁻¹ * b * g ∈ Submission.Blueprint.involutions (P.B : Set G) :=
      ⟨Work.Models.mem_conj_iff.mp hbH,
        by rw [orderOf_conj_inv, hb.2]⟩
    have hUa : g⁻¹ * a * g ∈ P.U := involutions_subset_U P.toBenderPair ha'
    have hUb : g⁻¹ * b * g ∈ P.U := involutions_subset_U P.toBenderPair hb'
    have ha2 : (g⁻¹ * a * g) * (g⁻¹ * a * g) = 1 := by
      have h := pow_orderOf_eq_one (g⁻¹ * a * g)
      rw [ha'.2] at h
      simpa [pow_two] using h
    have hcomm := P.hUinv _ hUa ha2 _ hUb
    calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [hcomm]
      _ = b * a := by group
  · -- **The rank-one decomposition and `J(D,t)`.**  Transport the involution into `B`.
    intro t ht2 htH
    set t' : G := g⁻¹ * t * g with ht'def
    have ht_eq : g * t' * g⁻¹ = t := by rw [ht'def]; group
    have ht'2 : orderOf t' = 2 := by
      rw [ht'def, orderOf_conj_inv, ht2]
    have ht'B : t' ∉ P.B := by
      intro hmem
      exact htH (by rw [hg]; exact Work.Models.mem_conj_iff.mpr (by rw [← ht'def]; exact hmem))
    -- `D = twoPoint P.B t'` is a `B`-conjugate of `T`, and `J(D,t')` the corresponding
    -- conjugate of `K₀ = J(T,w)`.
    obtain ⟨b, hbB, hDb, hKb⟩ :=
      invertedBy_twoPoint P.toBenderPair P.hTab P.hww ht'2 ht'B
    have hUS := U_inf_sup_conj_T P.toBenderPair hbB
    -- The two-point stabiliser, in the Borel.
    have h2p : Submission.Blueprint.twoPoint H t
        = Submission.Blueprint.conj g (Submission.Blueprint.twoPoint P.B t') := by
      rw [hg, Work.Models.twoPoint_conj_conj, ht'def]
    refine ⟨P.U.map (MulAut.conj g).toMonoidHom, P.K0.map (MulAut.conj (g * b)).toMonoidHom,
      P.hU2.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- `S ≤ H`
      rw [hg]
      exact Subgroup.map_mono P.U_le_B
    · -- `H ≤ N(S)`
      rw [hg, Commons.GroupTheory.Subgroup.normalizer_map_mulAut_conj]
      exact Subgroup.map_mono P.le_normalizer_U
    · -- `S ⊓ D = ⊥`
      rw [h2p, ← conj_inf, hDb, hUS.1, Work.Models.conj_bot]
    · -- `S ⊔ D = H`
      rw [h2p, ← conj_sup, hDb, hUS.2, ← hg]
    · -- `K = J(D,t)`
      have hstep : Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t
          = (fun x => g * x * g⁻¹) ''
              Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint P.B t') t' := by
        rw [h2p, ← ht_eq, Work.Models.invertedBy_conj]
      rw [hstep, hKb, ← P.hK0, Set.image_image, map_conj_coe]
      congr 1
      funext x
      group
    · -- `K` is cyclic
      exact isCyclic_map_conj P.K0 (g * b) P.hK0cyc
    · -- `|K| = #Inv(H)`
      rw [Subgroup.card_map_of_injective (MulAut.conj (g * b)).injective, P.hK0card, hg]
      exact (ncard_involutions_conj P.B g).symm

end Work.Models.Abstract
