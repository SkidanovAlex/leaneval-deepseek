import Mathlib
import Submission.Work.ZassenhausTwoGroup.Feit35Aux
import Submission.Work.ThmG.rankOne_index
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.card_involutions_eq_index_mul
import Submission.Work.ZassenhausPSL2.ZData.feit_bound

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Feit 1960, Lemma 3.5: the pieces of the counting argument

This module collects the counting lemmas used by `feit_lemma3_5_classes`.  Throughout,
`G` is a finite group with split rank-one Zassenhaus data `IsSplitRankOne H Q t`,
`IsZassenhaus H`, and `¬ IsPGroup 2 Q`; we write `m = |Q|`, `q = |D| = |twoPoint H t|`,
`Ω = G ⧸ H` and `i = |Inv(Q)|`.

The counting strategy is Feit's (Lemma 3.5, p. 182): count ordered pairs `(u,v)` of
involutions of `G` and relate them to the elements `u * v`, which are products of two
involutions.  The elements `u * v` which are not involutions and whose two factors lie in
*different* conjugates of `Q` are never conjugate into `Q` (Feit's Lemma 3.4, second half),
hence lie in one of the classes counted by `feit_lemma3_5_classes`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open scoped Classical

namespace Work.ZassenhausTwoGroup

/-! ## Elementary conversions between `Finset.card` and `Nat.card` -/

lemma invFinset_card_natCard (G : Type) [Group G] [Fintype G] :
    (invFinset G).card = Nat.card {u : G // orderOf u = 2} := by
  rw [show invFinset G = Finset.univ.filter (fun u : G => orderOf u = 2) from rfl]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma invFinsetQ_card_natCard {G : Type} [Group G] [Fintype G] (Q : Subgroup G) :
    (invFinsetQ Q).card = Nat.card {u : G // u ∈ Q ∧ orderOf u = 2} := by
  rw [show invFinsetQ Q = Finset.univ.filter (fun u : G => u ∈ Q ∧ orderOf u = 2) from rfl]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma centralizerInvols_card_natCard {G : Type} [Group G] [Fintype G] (u₀ : G) :
    (centralizerInvols u₀).card =
      Nat.card {w : G // orderOf w = 2 ∧ w ∈ Subgroup.centralizer ({u₀} : Set G)} := by
  rw [show centralizerInvols u₀ = Finset.univ.filter
      (fun w : G => orderOf w = 2 ∧ w ∈ Subgroup.centralizer ({u₀} : Set G)) from rfl]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma goodElem_card_natCard {G : Type} [Group G] [Fintype G] (Q : Subgroup G) :
    (goodElem Q).card = Nat.card {x : G // goodPred Q x} := by
  rw [show goodElem Q = Finset.univ.filter (fun x : G => goodPred Q x) from rfl]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The involutions of a subgroup `K`, counted inside `G`. -/
lemma natCard_involutions_subgroup {G : Type} [Group G] [Fintype G] (K : Subgroup G) :
    Nat.card {u : K // orderOf u = 2} = (Submission.Blueprint.involutions (K : Set G)).ncard := by
  rw [← Nat.card_coe_set_eq (Submission.Blueprint.involutions (K : Set G))]
  exact Nat.card_congr
    { toFun := fun u => ⟨(u.1 : G), ⟨u.1.2, by rw [Subgroup.orderOf_coe]; exact u.2⟩⟩
      invFun := fun u => ⟨⟨u.1, u.2.1⟩, by rw [← Subgroup.orderOf_coe]; exact u.2.2⟩
      left_inv := fun u => rfl
      right_inv := fun u => rfl }

lemma invFinsetQ_card_ncard {G : Type} [Group G] [Fintype G] (Q : Subgroup G) :
    (invFinsetQ Q).card = (Submission.Blueprint.involutions (Q : Set G)).ncard := by
  rw [invFinsetQ_card_natCard,
    ← Nat.card_coe_set_eq (Submission.Blueprint.involutions (Q : Set G))]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
    simp only [Submission.Blueprint.involutions, Set.mem_ofPred_eq]; exact Iff.rfl))

/-! ## The order of `G` and the number of involutions -/

/-- `|G| = |Q| · |D| · |G ⧸ H|`. -/
theorem feit35_card_G {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) :
    Nat.card G = Nat.card Q * Nat.card (Submission.Blueprint.twoPoint H t) *
      Nat.card (G ⧸ H) := by
  have hcard : Nat.card G = Nat.card H * H.index := (Subgroup.card_mul_index H).symm
  rw [hcard, Subgroup.index_eq_card, card_H_eq h]

/-- The set of involutions of `G` is the disjoint union of the sets of involutions of the
`|G ⧸ H|` conjugates of `Q`; each conjugate has `|Inv(Q)|` involutions.  Hence
`|Inv(G)| = |G ⧸ H| · |Inv(Q)|`. -/
theorem feit35_invol_card {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    (hQ2 : ¬ IsPGroup 2 Q) :
    (invFinset G).card = Nat.card (G ⧸ H) * (invFinsetQ Q).card := by
  have hse := h.stronglyEmbedded
  have hmain := Commons.GroupTheory.StronglyEmbedded.card_involutions_eq_index_mul H
    hse.1 hse.2.1 hse.2.2
  have hidx : H.index = Nat.card Q + 1 := Work.ThmG.rankOne_index h
  have ho : Nat.card (G ⧸ H) = Nat.card Q + 1 := card_quotient_eq h
  have hiH : Nat.card {u : H // orderOf u = 2} = (invFinsetQ Q).card := by
    rw [natCard_involutions_subgroup H, invFinsetQ_card_ncard Q,
      Work.ZassenhausPSL2.ZData.ncard_involutions_Q_eq h hZ]
  calc (invFinset G).card = Nat.card {u : G // orderOf u = 2} := invFinset_card_natCard G
    _ = H.index * Nat.card {u : H // orderOf u = 2} := hmain
    _ = Nat.card (G ⧸ H) * (invFinsetQ Q).card := by rw [hidx, ho, hiH]

/-- `|D| ≤ |Inv(Q)|`: `D` acts fixed point freely on `Q#`, so the `D`-orbit of any involution
of `Q` consists of `|D|` distinct involutions of `Q`. -/
theorem feit35_card_twoPoint_le {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H) :
    Nat.card (Submission.Blueprint.twoPoint H t) ≤ (invFinsetQ Q).card := by
  rw [invFinsetQ_card_ncard Q]
  exact le_of_eq (Work.ZassenhausPSL2.ZData.ncard_involutions_Q_eq_card_twoPoint h hZ).symm

/-- The involutions of `G` form a single conjugacy class, so the class of any involution `u₀`
has `|G : C_G(u₀)|` elements and `|Inv(G)| · |C_G(u₀)| = |G|`. -/
theorem feit35_invol_class_card {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) {u₀ : G} (hu₀ : orderOf u₀ = 2) :
    (invFinset G).card * Nat.card (Subgroup.centralizer ({u₀} : Set G)) = Nat.card G := by
  obtain ⟨u, _hu2, hconj⟩ := feit_lemma3_4 H Q t h
  -- an element is an involution iff it is conjugate to `u₀`
  have hiff : ∀ x : G, orderOf x = 2 ↔ IsConj u₀ x := by
    intro x
    constructor
    · intro hx
      exact ((hconj u₀ hu₀).symm).trans (hconj x hx)
    · intro hx
      obtain ⟨c, hc⟩ := isConj_iff.mp hx
      have h1 : orderOf (MulAut.conj c u₀) = orderOf u₀ :=
        orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective u₀
      rw [MulAut.conj_apply, hc] at h1
      rw [h1, hu₀]
  -- orbit–stabiliser for the conjugation action
  have hos := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) u₀
  have h2 : Fintype.card ↥(MulAction.orbit (ConjAct G) u₀) = (invFinset G).card := by
    rw [← Set.toFinset_card]
    congr 1
    ext x
    rw [Set.mem_toFinset, ConjAct.mem_orbit_conjAct, isConj_comm]
    simp only [invFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hiff x).symm
  have h3 : Fintype.card ↥(MulAction.stabilizer (ConjAct G) u₀) =
      Nat.card (Subgroup.centralizer ({u₀} : Set G)) :=
    (Nat.card_eq_fintype_card).symm.trans
      (Subgroup.nat_card_centralizer_nat_card_stabilizer u₀).symm
  rw [h2, h3] at hos
  have hGG : Fintype.card (ConjAct G) = Nat.card G := by
    rw [Nat.card_eq_fintype_card]; rfl
  rw [hGG] at hos
  exact hos


/-! ## Orbit–stabiliser for a single conjugacy class, and the class sum of centralisers -/

/-- For any element `x₀` of a finite group, the conjugacy class of `x₀` has `|G : C_G(x₀)|`
elements. -/
lemma ncard_carrier_mul_card_centralizer {G : Type} [Group G] [Fintype G] (x₀ : G) :
    ((ConjClasses.mk x₀).carrier).ncard *
      Nat.card (Subgroup.centralizer ({x₀} : Set G)) = Nat.card G := by
  have hos := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) x₀
  have h2 : (MulAction.orbit (ConjAct G) x₀).ncard =
      ((ConjClasses.mk x₀).carrier).ncard := by
    rw [ConjAct.orbit_eq_carrier_conjClasses]
  have h2' : Fintype.card ↥(MulAction.orbit (ConjAct G) x₀) =
      (MulAction.orbit (ConjAct G) x₀).ncard := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  have h3 : Fintype.card ↥(MulAction.stabilizer (ConjAct G) x₀) =
      Nat.card (Subgroup.centralizer ({x₀} : Set G)) :=
    (Nat.card_eq_fintype_card).symm.trans
      (Subgroup.nat_card_centralizer_nat_card_stabilizer x₀).symm
  rw [h2', h3, h2] at hos
  have hGG : Fintype.card (ConjAct G) = Nat.card G := by
    rw [Nat.card_eq_fintype_card]; rfl
  rw [hGG] at hos
  exact hos

/-- Conjugate elements have centralisers of the same order. -/
lemma natCard_centralizer_conj {G : Type} [Group G] (g x : G) :
    Nat.card (Subgroup.centralizer ({g * x * g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  have hmap : (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [Subgroup.mem_centralizer_singleton_iff] at hc
      rw [show (g * c * g⁻¹) * (g * x * g⁻¹) = g * (c * x) * g⁻¹ by group,
        show (g * x * g⁻¹) * (g * c * g⁻¹) = g * (x * c) * g⁻¹ by group, hc]
    · intro hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      refine ⟨g⁻¹ * y * g, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc (g⁻¹ * y * g) * x
            = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hy]
          _ = x * (g⁻¹ * y * g) := by group
      · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
  rw [← hmap, Subgroup.card_map_of_injective]
  exact (MulAut.conj g).injective

theorem feit35_sum_centralizer_carrier {G : Type} [Group G] [Fintype G] (c : ConjClasses G) :
    classCentralizerSum c = Nat.card G := by
  obtain ⟨x₀, rfl⟩ := ConjClasses.exists_rep c
  have hconst : ∀ x ∈ (ConjClasses.mk x₀).carrier.toFinset,
      Nat.card (Subgroup.centralizer ({x} : Set G)) =
        Nat.card (Subgroup.centralizer ({x₀} : Set G)) := by
    intro x hx
    rw [Set.mem_toFinset, ConjClasses.mem_carrier_iff_mk_eq,
      ConjClasses.mk_eq_mk_iff_isConj] at hx
    obtain ⟨g, hg⟩ := isConj_iff.mp hx
    rw [← hg]
    exact (natCard_centralizer_conj g x).symm
  show (∑ x ∈ (ConjClasses.mk x₀).carrier.toFinset,
      Nat.card (Subgroup.centralizer ({(x : G)} : Set G))) = Nat.card G
  calc ∑ x ∈ (ConjClasses.mk x₀).carrier.toFinset,
        Nat.card (Subgroup.centralizer ({(x : G)} : Set G))
      = ∑ _x ∈ (ConjClasses.mk x₀).carrier.toFinset,
          Nat.card (Subgroup.centralizer ({x₀} : Set G)) := Finset.sum_congr rfl hconst
    _ = (ConjClasses.mk x₀).carrier.toFinset.card *
          Nat.card (Subgroup.centralizer ({x₀} : Set G)) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = ((ConjClasses.mk x₀).carrier).ncard *
          Nat.card (Subgroup.centralizer ({x₀} : Set G)) := by
        rw [← Set.ncard_eq_toFinset_card']
    _ = Nat.card G := ncard_carrier_mul_card_centralizer x₀

/-- In a finite group, the number of pairs of involutions with product `x` is at most the order
of the centraliser of `x`: `u ↦ u` is injective on such pairs, and the possible `u` form a coset
of `C_G(x)`. -/
theorem feit35_fiber_le {G : Type} [Group G] [Fintype G] (x : G) :
    (prodFiberPairs G x).card ≤ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  set S : Finset G := Finset.univ.filter (fun u : G => orderOf u = 2 ∧ u * x * u⁻¹ = x⁻¹)
    with hS
  have hinj : Set.InjOn Prod.fst (↑(prodFiberPairs G x) : Set (G × G)) := by
    intro p hp q hq hpq
    rw [Finset.mem_coe] at hp hq
    obtain ⟨-, hpx⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, hqx⟩ := Finset.mem_filter.mp hq
    have h1 : p.1 = q.1 := hpq
    have hp2 : p.2 = p.1⁻¹ * x := by rw [← hpx]; group
    have hq2 : q.2 = q.1⁻¹ * x := by rw [← hqx]; group
    exact Prod.ext h1 (by rw [hp2, hq2, h1])
  have h1 : (prodFiberPairs G x).card ≤ S.card := by
    have him : (Finset.image Prod.fst (prodFiberPairs G x)).card =
        (prodFiberPairs G x).card := Finset.card_image_of_injOn hinj
    have hsub : Finset.image Prod.fst (prodFiberPairs G x) ⊆ S := by
      intro u hu
      rw [Finset.mem_image] at hu
      obtain ⟨p, hp, rfl⟩ := hu
      obtain ⟨hpI, hpx⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpI
      have hu2 : p.1 * p.1 = 1 := by
        have h2 : orderOf p.1 = 2 := (Finset.mem_filter.mp hp1).2
        have h3 := pow_orderOf_eq_one p.1
        rwa [h2, pow_two] at h3
      have hv2 : p.2 * p.2 = 1 := by
        have h2 : orderOf p.2 = 2 := (Finset.mem_filter.mp hp2).2
        have h3 := pow_orderOf_eq_one p.2
        rwa [h2, pow_two] at h3
      rw [hS, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp1).2, ?_⟩
      calc p.1 * x * p.1⁻¹ = p.1 * (p.1 * p.2) * p.1⁻¹ := by rw [hpx]
        _ = (p.1 * p.1) * (p.2 * p.1⁻¹) := by group
        _ = p.2 * p.1⁻¹ := by rw [hu2, one_mul]
        _ = p.2⁻¹ * p.1⁻¹ := by rw [inv_eq_of_mul_eq_one_right hv2]
        _ = (p.1 * p.2)⁻¹ := by rw [mul_inv_rev]
        _ = x⁻¹ := by rw [hpx]
    calc (prodFiberPairs G x).card = (Finset.image Prod.fst (prodFiberPairs G x)).card := him.symm
      _ ≤ S.card := Finset.card_le_card hsub
  refine le_trans h1 ?_
  rcases S.eq_empty_or_nonempty with hS0 | ⟨u₁, hu₁⟩
  · rw [hS0]; simp
  · have hu₁mem : u₁ * x * u₁⁻¹ = x⁻¹ := ((Finset.mem_filter.mp hu₁).2).2
    have hC : S ⊆ Finset.univ.filter (fun u : G =>
        u₁⁻¹ * u ∈ Subgroup.centralizer ({x} : Set G)) := by
      intro u hu
      rw [Finset.mem_filter] at hu ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hu_eq : u * x * u⁻¹ = x⁻¹ := hu.2.2
      have hux : u * x = x⁻¹ * u := by
        calc u * x = (u * x * u⁻¹) * u := by group
          _ = x⁻¹ * u := by rw [hu_eq]
      have hx : u₁⁻¹ * x⁻¹ * u₁ = x := by
        rw [← hu₁mem]; group
      calc (u₁⁻¹ * u) * x = u₁⁻¹ * (u * x) := by group
        _ = u₁⁻¹ * (x⁻¹ * u) := by rw [hux]
        _ = (u₁⁻¹ * x⁻¹ * u₁) * (u₁⁻¹ * u) := by group
        _ = x * (u₁⁻¹ * u) := by rw [hx]
    have hcard : (Finset.univ.filter (fun u : G =>
        u₁⁻¹ * u ∈ Subgroup.centralizer ({x} : Set G))).card =
        Nat.card (Subgroup.centralizer ({x} : Set G)) := by
      rw [← Fintype.card_coe (Finset.univ.filter (fun u : G =>
          u₁⁻¹ * u ∈ Subgroup.centralizer ({x} : Set G)))]
      rw [Nat.card_eq_fintype_card]
      refine Fintype.card_congr ?_
      exact
        { toFun := fun u => ⟨u₁⁻¹ * (u : G), (Finset.mem_filter.mp u.2).2⟩
          invFun := fun c => ⟨u₁ * (c : G), by
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            show u₁⁻¹ * (u₁ * (c : G)) ∈ Subgroup.centralizer ({x} : Set G)
            rw [show u₁⁻¹ * (u₁ * (c : G)) = (c : G) by group]
            exact c.2⟩
          left_inv := fun u => by
            apply Subtype.ext
            show u₁ * (u₁⁻¹ * (u : G)) = u
            group
          right_inv := fun c => by
            apply Subtype.ext
            show u₁⁻¹ * (u₁ * (c : G)) = c
            group }
    calc S.card ≤ (Finset.univ.filter (fun u : G =>
          u₁⁻¹ * u ∈ Subgroup.centralizer ({x} : Set G))).card := Finset.card_le_card hC
      _ = Nat.card (Subgroup.centralizer ({x} : Set G)) := hcard


/-! ## Conjugation invariance -/

/-- `goodPred Q` is invariant under conjugation. -/
lemma goodPred_conj_iff {G : Type} [Group G] {Q : Subgroup G} (γ x : G) :
    goodPred Q (γ * x * γ⁻¹) ↔ goodPred Q x := by
  have key : ∀ {a : G}, goodPred Q a → ∀ g : G, goodPred Q (g * a * g⁻¹) := by
    rintro a ⟨ha1, ha2, ha3, ha4⟩ g
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      exact ha1 (by
        have h2 := congrArg (fun z : G => g⁻¹ * z * g) h
        simpa [mul_assoc] using h2)
    · have h1 : orderOf (g * a * g⁻¹) = orderOf a := by
        rw [← MulAut.conj_apply g a]
        exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a
      rw [h1]; exact ha2
    · obtain ⟨u, v, hu, hv, huv⟩ := ha3
      refine ⟨g * u * g⁻¹, g * v * g⁻¹, ?_, ?_, ?_⟩
      · have h1 : orderOf (g * u * g⁻¹) = orderOf u := by
          rw [← MulAut.conj_apply g u]
          exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective u
        rw [h1]; exact hu
      · have h1 : orderOf (g * v * g⁻¹) = orderOf v := by
          rw [← MulAut.conj_apply g v]
          exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective v
        rw [h1]; exact hv
      · rw [huv]; group
    · intro h hQ
      apply ha4 (h * g)
      rw [show (h * g) * a * (h * g)⁻¹ = h * (g * a * g⁻¹) * h⁻¹ by group]
      exact hQ
  refine ⟨fun hx => ?_, fun hx => key hx γ⟩
  have h := key hx γ⁻¹
  have heq : γ⁻¹ * (γ * x * γ⁻¹) * (γ⁻¹)⁻¹ = x := by group
  rwa [heq] at h

/-- `conj g (conj h Q) = conj (g * h) Q`. -/
lemma conj_mul_conj {G : Type} [Group G] (Q : Subgroup G) (g h : G) :
    Submission.Blueprint.conj g (Submission.Blueprint.conj h Q) =
      Submission.Blueprint.conj (g * h) Q := by
  ext x
  constructor
  · intro hx
    rw [Submission.Blueprint.conj, Subgroup.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [Submission.Blueprint.conj, Subgroup.mem_map] at hy
    obtain ⟨q, hq, hqy⟩ := hy
    rw [Submission.Blueprint.conj, Subgroup.mem_map]
    refine ⟨q, hq, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx hqy ⊢
    rw [← hyx, ← hqy]; group
  · intro hx
    rw [Submission.Blueprint.conj, Subgroup.mem_map] at hx
    obtain ⟨q, hq, hqx⟩ := hx
    rw [Submission.Blueprint.conj, Subgroup.mem_map]
    refine ⟨h * q * h⁻¹, ?_, ?_⟩
    · rw [Submission.Blueprint.conj, Subgroup.mem_map]
      exact ⟨q, hq, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hqx ⊢
      rw [← hqx]; group

/-- The involutions centralising a conjugate of `u` are the conjugates of the involutions
centralising `u`. -/
lemma centralizerInvols_conj {G : Type} [Group G] [Fintype G] (γ u : G) :
    (centralizerInvols (γ * u * γ⁻¹)).card = (centralizerInvols u).card := by
  have himg : Finset.image (fun w : G => γ * w * γ⁻¹) (centralizerInvols u) =
      centralizerInvols (γ * u * γ⁻¹) := by
    ext w
    rw [Finset.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [centralizerInvols, Finset.mem_filter] at hz ⊢
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · have h1 : orderOf (γ * z * γ⁻¹) = orderOf z := by
          rw [← MulAut.conj_apply γ z]
          exact orderOf_injective (MulAut.conj γ).toMonoidHom (MulAut.conj γ).injective z
        rw [h1]; exact hz.2.1
      · rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
        calc (γ * z * γ⁻¹) * (γ * u * γ⁻¹) = γ * (z * u) * γ⁻¹ := by group
          _ = γ * (u * z) * γ⁻¹ := by rw [hz.2.2]
          _ = (γ * u * γ⁻¹) * (γ * z * γ⁻¹) := by group
    · intro hw
      rw [centralizerInvols, Finset.mem_filter] at hw
      refine ⟨γ⁻¹ * w * γ, ?_, by group⟩
      rw [centralizerInvols, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · have h1 : orderOf (γ⁻¹ * w * γ) = orderOf w := by
          rw [show γ⁻¹ * w * γ = MulAut.conj γ⁻¹ w from by rw [MulAut.conj_apply, inv_inv]]
          exact orderOf_injective (MulAut.conj γ⁻¹).toMonoidHom (MulAut.conj γ⁻¹).injective w
        rw [h1]; exact hw.2.1
      · rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
        calc (γ⁻¹ * w * γ) * u = γ⁻¹ * (w * (γ * u * γ⁻¹)) * γ := by group
          _ = γ⁻¹ * ((γ * u * γ⁻¹) * w) * γ := by rw [hw.2.2]
          _ = u * (γ⁻¹ * w * γ) := by group
  rw [← himg, Finset.card_image_of_injective]
  exact fun a b hab => by
    have := congrArg (fun z : G => γ⁻¹ * z * γ) hab
    simpa [mul_assoc] using this

/-- The number of involutions centralising conjugate elements is the same. -/
lemma centralizerInvols_card_of_isConj {G : Type} [Group G] [Fintype G] {a b : G}
    (h : IsConj a b) : (centralizerInvols a).card = (centralizerInvols b).card := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h.symm
  rw [← hc, centralizerInvols_conj]


/-- `orderOf (g⁻¹ * x * g) = orderOf x`. -/
lemma orderOf_inv_conj_eq {G : Type} [Group G] (g x : G) :
    orderOf (g⁻¹ * x * g) = orderOf x := by
  rw [show g⁻¹ * x * g = MulAut.conj g⁻¹ x from by rw [MulAut.conj_apply, inv_inv]]
  exact orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective x

/-! ## Products of two involutions in a conjugate of `Q` -/

/-- If `u`, `v` are involutions with `u * v ≠ 1` and `u * v ∈ Q`, then `u, v ∈ Q`
(Feit 1960, Lemma 3.4, second half, in the case of `Q` itself). -/
lemma mem_Q_of_mul_mem_Q {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    {u v : G} (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : u * v ≠ 1)
    (hmem : u * v ∈ Q) : u ∈ Q ∧ v ∈ Q := by
  have hu2 : u * u = 1 := by
    have h3 := pow_orderOf_eq_one u; rwa [hu, pow_two] at h3
  have hv2 : v * v = 1 := by
    have h3 := pow_orderOf_eq_one v; rwa [hv, pow_two] at h3
  have hxinv : (u * v)⁻¹ = u * (u * v) * u⁻¹ := by
    rw [show u * (u * v) * u⁻¹ = (u * u) * v * u⁻¹ by group, hu2, one_mul, mul_inv_rev,
      inv_eq_of_mul_eq_one_right hv2, inv_eq_of_mul_eq_one_right hu2]
  have hmemP : (u * v)⁻¹ ∈ Q ⊓ Submission.Blueprint.conj u Q := by
    refine ⟨Q.inv_mem hmem, ?_⟩
    rw [hxinv]
    exact Subgroup.mem_map.mpr ⟨u * v, hmem, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have hne : Q ⊓ Submission.Blueprint.conj u Q ≠ ⊥ := by
    intro hbot
    exact (inv_ne_one.mpr huv) (Subgroup.mem_bot.mp (hbot ▸ hmemP))
  have huH : u ∈ H := by
    by_contra huH
    exact hne (isTI_Q h hZ u huH)
  have huQ : u ∈ Q :=
    Work.ZassenhausPSL2.ZData.involution_mem_Q h hZ ⟨huH, hu⟩
  exact ⟨huQ, by
    rw [show v = u⁻¹ * (u * v) by group]
    exact Q.mul_mem (Q.inv_mem huQ) hmem⟩

/-- Feit 1960, Lemma 3.4 (second half), in terms of an arbitrary conjugate of `Q`: if `u`, `v`
are involutions with `u * v ≠ 1` and `u * v ∈ conj e Q`, then `u` and `v` themselves lie in
`conj e Q`. -/
theorem feit35_product_mem_conj {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    (hQ2 : ¬ IsPGroup 2 Q) {u v : G} (hu : orderOf u = 2) (hv : orderOf v = 2)
    (huv : u * v ≠ 1) {e : G} (hpQ : u * v ∈ Submission.Blueprint.conj e Q) :
    u ∈ Submission.Blueprint.conj e Q ∧ v ∈ Submission.Blueprint.conj e Q := by
  obtain ⟨q, hq, hqeq⟩ := Subgroup.mem_map.mp hpQ
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hqeq
  -- conjugate the situation into `Q`
  have hmem : (e⁻¹ * u * e) * (e⁻¹ * v * e) ∈ Q := by
    have h1 : e⁻¹ * (u * v) * e = q := by rw [← hqeq]; group
    rw [show (e⁻¹ * u * e) * (e⁻¹ * v * e) = e⁻¹ * (u * v) * e by group, h1]
    exact hq
  have hu' : orderOf (e⁻¹ * u * e) = 2 := by
    rw [orderOf_inv_conj_eq e u, hu]
  have hv' : orderOf (e⁻¹ * v * e) = 2 := by
    rw [orderOf_inv_conj_eq e v, hv]
  have huv' : (e⁻¹ * u * e) * (e⁻¹ * v * e) ≠ 1 := by
    rw [show (e⁻¹ * u * e) * (e⁻¹ * v * e) = e⁻¹ * (u * v) * e by group]
    intro h1
    apply huv
    have h2 := congrArg (fun z : G => e * z * e⁻¹) h1
    simpa [mul_assoc] using h2
  obtain ⟨huQ, hvQ⟩ := mem_Q_of_mul_mem_Q h hZ hu' hv' huv' hmem
  constructor
  · rw [show u = e * (e⁻¹ * u * e) * e⁻¹ by group]
    exact Subgroup.mem_map.mpr ⟨e⁻¹ * u * e, huQ, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  · rw [show v = e * (e⁻¹ * v * e) * e⁻¹ by group]
    exact Subgroup.mem_map.mpr ⟨e⁻¹ * v * e, hvQ, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩

/-! ## The number of ordered pairs of involutions with involution product -/

theorem feit35_inv_product_pairs {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) {u₀ : G} (hu₀ : orderOf u₀ = 2) :
    (invProductPairs G).card =
      (invFinset G).card * ((centralizerInvols u₀).card - 1) := by
  obtain ⟨u₁, _hu2, hconj⟩ := feit_lemma3_4 H Q t h
  -- the fibre of `(u,v) ↦ u` over an involution `u` is `C_I(u) \ {u}`
  have hfib : ∀ u : G, u ∈ invFinset G →
      ((invFinset G).filter (fun v : G => orderOf (u * v) = 2)) = (centralizerInvols u).erase u := by
    intro u hu
    have hu2 : orderOf u = 2 := (Finset.mem_filter.mp hu).2
    ext v
    simp only [Finset.mem_filter, Finset.mem_erase, centralizerInvols, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨hv, huv⟩
      have hv2 : orderOf v = 2 := (Finset.mem_filter.mp hv).2
      have hv2' : v * v = 1 := by
        have h3 := pow_orderOf_eq_one v; rwa [hv2, pow_two] at h3
      have hu2' : u * u = 1 := by
        have h3 := pow_orderOf_eq_one u; rwa [hu2, pow_two] at h3
      have hsq : (u * v) * (u * v) = 1 := by
        have h3 := pow_orderOf_eq_one (u * v); rwa [huv, pow_two] at h3
      have hcomm : u * v = v * u := by
        have h1 : u * v * u * v = 1 := by rw [← mul_assoc] at hsq; exact hsq
        have h2 : u * v * u = v := by
          have h := congrArg (fun z : G => z * v⁻¹) h1
          rw [one_mul, show (u * v * u * v) * v⁻¹ = u * v * u by group,
            inv_eq_of_mul_eq_one_right hv2'] at h
          exact h
        have h3 : u * v = v * u := by
          have h := congrArg (fun z : G => z * u⁻¹) h2
          rw [show u * v * u * u⁻¹ = u * v by group,
            inv_eq_of_mul_eq_one_right hu2'] at h
          exact h
        exact h3
      have hne : v ≠ u := by
        intro hvu
        rw [hvu, hu2', orderOf_one] at huv
        exact absurd huv (by norm_num)
      exact ⟨hne, hv2, by rw [Subgroup.mem_centralizer_singleton_iff]; exact hcomm.symm⟩
    · rintro ⟨hne, hv2, hcomm⟩
      have hv2' : v * v = 1 := by
        have h3 := pow_orderOf_eq_one v; rwa [hv2, pow_two] at h3
      have hu2' : u * u = 1 := by
        have h3 := pow_orderOf_eq_one u; rwa [hu2, pow_two] at h3
      have hcomm' : v * u = u * v := Subgroup.mem_centralizer_singleton_iff.mp hcomm
      have hsq : (u * v) * (u * v) = 1 := by
        rw [show (u * v) * (u * v) = u * (v * u) * v by group, hcomm',
          show u * (u * v) * v = (u * u) * (v * v) by group, hu2', hv2', mul_one]
      have hne1 : u * v ≠ 1 := by
        intro h1
        apply hne
        have h2 : v = u⁻¹ := by
          have h3 := congrArg (fun z : G => u⁻¹ * z) h1
          simpa [mul_assoc] using h3
        rw [h2, inv_eq_of_mul_eq_one_right hu2']
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv2⟩, ?_⟩
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two]; exact hsq) hne1
  have h1 : (invProductPairs G).card =
      ∑ u ∈ invFinset G,
        ((invFinset G).filter (fun v : G => orderOf (u * v) = 2)).card := by
    rw [invProductPairs, Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl ?_
    intro u _hu
    rw [Finset.card_filter]
  have h2 : ∀ u ∈ invFinset G, (centralizerInvols u).card = (centralizerInvols u₀).card := by
    intro u hu
    have hu2 : orderOf u = 2 := (Finset.mem_filter.mp hu).2
    exact centralizerInvols_card_of_isConj ((hconj u hu2).symm.trans (hconj u₀ hu₀))
  rw [h1]
  have h3 : ∀ u ∈ invFinset G,
      ((invFinset G).filter (fun v : G => orderOf (u * v) = 2)).card =
        (centralizerInvols u₀).card - 1 := by
    intro u hu
    rw [hfib u hu]
    have humem : u ∈ centralizerInvols u := by
      rw [centralizerInvols, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2,
        Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    rw [Finset.card_erase_of_mem humem, h2 u hu]
  rw [Finset.sum_congr rfl h3, Finset.sum_const, smul_eq_mul]


/-! ## The number of ordered pairs of involutions in a common conjugate of `Q` -/

/-- Every involution of `G` lies in a conjugate of `Q`. -/
lemma involution_mem_conj_Q {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    {u : G} (hu : orderOf u = 2) : ∃ g : G, u ∈ Submission.Blueprint.conj g Q := by
  obtain ⟨g, hg⟩ := Work.ThmF.Bender.involutionMemConj h.stronglyEmbedded hu
  obtain ⟨a, haH, hag⟩ := Subgroup.mem_map.mp hg
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hag
  have ha2 : orderOf a = 2 := by
    have h1 : orderOf (g * a * g⁻¹) = orderOf a := by
      rw [← MulAut.conj_apply g a]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a
    rw [← hag, h1] at hu
    exact hu
  exact ⟨g, Subgroup.mem_map.mpr
    ⟨a, Work.ZassenhausPSL2.ZData.involution_mem_Q h hZ ⟨haH, ha2⟩,
      by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; exact hag⟩⟩

/-- An element of the normaliser of `Q` conjugates `Q` to itself. -/
lemma conj_eq_self_of_mem_normalizer {G : Type} [Group G] {Q : Subgroup G} {h : G}
    (hh : h ∈ Subgroup.normalizer (Q : Set G)) : Submission.Blueprint.conj h Q = Q := by
  ext x
  rw [Submission.Blueprint.conj, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    rw [← hyx]
    exact (Subgroup.mem_normalizer_iff.mp hh y).mp hy
  · intro hx
    exact ⟨h⁻¹ * x * h, (Subgroup.mem_normalizer_iff.mp hh _).mpr (by
      rw [show h * (h⁻¹ * x * h) * h⁻¹ = x by group]; exact hx),
      by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

/-- The conjugate of `Q` attached to a coset does not depend on the representative. -/
lemma conj_out_eq_conj {G : Type} [Group G] {H Q : Subgroup G}
    (hN : H ≤ Subgroup.normalizer (Q : Set G)) (g : G) :
    Submission.Blueprint.conj (Quotient.out (g : G ⧸ H)) Q =
      Submission.Blueprint.conj g Q := by
  have h1 : ((Quotient.out (g : G ⧸ H) : G) : G ⧸ H) = (g : G ⧸ H) := Quotient.out_eq _
  rw [QuotientGroup.eq] at h1
  have hmem : (Quotient.out (g : G ⧸ H))⁻¹ * g ∈ Subgroup.normalizer (Q : Set G) := hN h1
  calc Submission.Blueprint.conj (Quotient.out (g : G ⧸ H)) Q
      = Submission.Blueprint.conj (Quotient.out (g : G ⧸ H))
          (Submission.Blueprint.conj ((Quotient.out (g : G ⧸ H))⁻¹ * g) Q) := by
        rw [conj_eq_self_of_mem_normalizer hmem]
    _ = Submission.Blueprint.conj
          (Quotient.out (g : G ⧸ H) * ((Quotient.out (g : G ⧸ H))⁻¹ * g)) Q :=
        conj_mul_conj Q _ _
    _ = Submission.Blueprint.conj g Q := by
        rw [show Quotient.out (g : G ⧸ H) * ((Quotient.out (g : G ⧸ H))⁻¹ * g) = g by group]

theorem feit35_same_conj_pairs {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    (hQ2 : ¬ IsPGroup 2 Q) :
    (sameConjPairs Q).card = Nat.card (G ⧸ H) * (invFinsetQ Q).card ^ 2 := by
  classical
  have hQne : Q ≠ ⊥ := by
    intro hbot
    exact hQ2 (hbot ▸ IsPGroup.of_subsingleton 2 ↥(⊥ : Subgroup G))
  -- each involution lies in a unique conjugate of `Q`
  have huniq : ∀ u : G, orderOf u = 2 → ∀ g g' : G, u ∈ Submission.Blueprint.conj g Q →
      u ∈ Submission.Blueprint.conj g' Q → (g : G ⧸ H) = (g' : G ⧸ H) := by
    intro u hu g g' hg hg'
    have hu1 : u ≠ 1 := by
      intro h0; rw [h0, orderOf_one] at hu; exact absurd hu (by norm_num)
    obtain ⟨a, haQ, hag⟩ := Subgroup.mem_map.mp hg
    obtain ⟨b, hbQ, hbg⟩ := Subgroup.mem_map.mp hg'
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hag hbg
    have hxQ : g⁻¹ * u * g ∈ Q := by
      rw [show g⁻¹ * u * g = a by rw [← hag]; group]; exact haQ
    have hxQ' : g⁻¹ * u * g ∈ Submission.Blueprint.conj (g⁻¹ * g') Q := by
      refine Subgroup.mem_map.mpr ⟨b, hbQ, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show (g⁻¹ * g') * b * (g⁻¹ * g')⁻¹ = g⁻¹ * u * g by rw [← hbg]; group]
    have hne : Q ⊓ Submission.Blueprint.conj (g⁻¹ * g') Q ≠ ⊥ := by
      intro hbot
      have hone : g⁻¹ * u * g = 1 := Subgroup.mem_bot.mp (hbot ▸ ⟨hxQ, hxQ'⟩)
      exact hu1 (by
        have h2 := congrArg (fun z : G => g * z * g⁻¹) hone
        simpa [mul_assoc] using h2)
    have hmem : g⁻¹ * g' ∈ H := by
      by_contra hc
      exact hne (isTI_Q h hZ _ hc)
    exact QuotientGroup.eq.mpr hmem
  -- the sets `S ω` of involutions in the conjugate of `Q` indexed by `ω`
  set S : G ⧸ H → Finset G := fun ω => conjInvFinset H Q ω with hS
  have hScard : ∀ ω, (S ω).card = (invFinsetQ Q).card := by
    intro ω
    have himg : (invFinsetQ Q).image
        (fun u : G => Quotient.out ω * u * (Quotient.out ω)⁻¹) = S ω := by
      ext x
      constructor
      · intro hx
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨-, huQ, hu2⟩ := Finset.mem_filter.mp hu
        rw [hS]
        simp only [conjInvFinset, Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · rw [invFinset, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have h1 : orderOf (Quotient.out ω * u * (Quotient.out ω)⁻¹) = orderOf u := by
            rw [← MulAut.conj_apply (Quotient.out ω) u]
            exact orderOf_injective (MulAut.conj (Quotient.out ω)).toMonoidHom
              (MulAut.conj (Quotient.out ω)).injective u
          rw [h1, hu2]
        · exact Subgroup.mem_map.mpr ⟨u, huQ, by
            rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
      · intro hx
        rw [hS] at hx
        simp only [conjInvFinset, Finset.mem_filter] at hx
        obtain ⟨hxI, hxQ⟩ := hx
        obtain ⟨u, huQ, hu⟩ := Subgroup.mem_map.mp hxQ
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hu
        refine Finset.mem_image.mpr ⟨u, ?_, hu⟩
        rw [invFinsetQ, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, huQ, ?_⟩
        have hx2 : orderOf x = 2 := (Finset.mem_filter.mp hxI).2
        rw [← hu] at hx2
        have h1 : orderOf (Quotient.out ω * u * (Quotient.out ω)⁻¹) = orderOf u := by
          rw [← MulAut.conj_apply (Quotient.out ω) u]
          exact orderOf_injective (MulAut.conj (Quotient.out ω)).toMonoidHom
            (MulAut.conj (Quotient.out ω)).injective u
        rwa [h1] at hx2
    rw [← himg, Finset.card_image_of_injective]
    intro a b hab
    have h := congrArg (fun z : G => (Quotient.out ω)⁻¹ * z * (Quotient.out ω)) hab
    simpa [mul_assoc] using h
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (G ⧸ H)) : Set (G ⧸ H))
      (fun ω => S ω ×ˢ S ω) := by
    rw [Finset.pairwiseDisjoint_iff]
    intro ω _ ω' _ hne
    obtain ⟨p, hp⟩ := hne
    rw [Finset.mem_inter, Finset.mem_product, Finset.mem_product] at hp
    obtain ⟨⟨hp1, -⟩, ⟨hp1', -⟩⟩ := hp
    rw [hS] at hp1 hp1'
    simp only [conjInvFinset, Finset.mem_filter] at hp1 hp1'
    have hu2 : orderOf p.1 = 2 := (Finset.mem_filter.mp hp1.1).2
    have h1 := huniq p.1 hu2 _ _ hp1.2 hp1'.2
    have h2 : ((Quotient.out ω : G) : G ⧸ H) = ω := Quotient.out_eq ω
    have h3 : ((Quotient.out ω' : G) : G ⧸ H) = ω' := Quotient.out_eq ω'
    rw [h2, h3] at h1
    exact h1
  have hmain : sameConjPairs Q =
      (Finset.univ : Finset (G ⧸ H)).biUnion (fun ω => S ω ×ˢ S ω) := by
    ext p
    constructor
    · intro hp
      rw [sameConjPairs, Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hp1I, hp2I⟩, g, hp1Q, hp2Q⟩ := hp
      refine Finset.mem_biUnion.mpr ⟨(g : G ⧸ H), Finset.mem_univ _, ?_⟩
      rw [Finset.mem_product, hS]
      simp only [conjInvFinset, Finset.mem_filter]
      rw [conj_out_eq_conj h.normal g]
      exact ⟨⟨hp1I, hp1Q⟩, ⟨hp2I, hp2Q⟩⟩
    · intro hp
      obtain ⟨ω, -, hpω⟩ := Finset.mem_biUnion.mp hp
      rw [Finset.mem_product, hS] at hpω
      simp only [conjInvFinset, Finset.mem_filter] at hpω
      obtain ⟨⟨hp1I, hp1Q⟩, ⟨hp2I, hp2Q⟩⟩ := hpω
      rw [sameConjPairs, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hp1I, hp2I⟩, Quotient.out ω, hp1Q, hp2Q⟩
  rw [hmain, Finset.card_biUnion hdisj]
  simp only [Finset.card_product]
  rw [Finset.sum_congr rfl (fun ω _ => by rw [hScard ω])]
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card]
  ring


/-! ## The sum of centraliser orders over the elements of the counted classes -/

lemma mem_goodClasses {G : Type} [Group G] [Fintype G] (Q : Subgroup G) (c : ConjClasses G) :
    c ∈ goodClasses Q ↔ ∀ x ∈ c.carrier, goodPred Q x := by
  rw [goodClasses, Finset.mem_filter]
  simp

lemma goodPred_of_isConj {G : Type} [Group G] {Q : Subgroup G} {x y : G} (h : IsConj x y) :
    goodPred Q x → goodPred Q y := by
  intro hx
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  rw [← hg]
  exact (goodPred_conj_iff g x).mpr hx

theorem feit35_goodElem_sum {G : Type} [Group G] [Fintype G] (Q : Subgroup G) :
    ∑ x ∈ goodElem Q, Nat.card (Subgroup.centralizer ({(x : G)} : Set G)) =
      (goodClasses Q).card * Nat.card G := by
  classical
  -- the classes of the elements of `goodElem Q`
  have hgood : ∀ (c : ConjClasses G) (x : G),
      x ∈ (goodElem Q).filter (fun x => ConjClasses.mk x = c) → c ∈ goodClasses Q := by
    intro c x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxg, hxc⟩ := hx
    simp only [goodElem, Finset.mem_filter, Finset.mem_univ, true_and] at hxg
    rw [mem_goodClasses]
    intro y hy
    have hy' : ConjClasses.mk y = c := ConjClasses.mem_carrier_iff_mk_eq.mp hy
    exact goodPred_of_isConj (ConjClasses.mk_eq_mk_iff_isConj.mp (by rw [hy', hxc])).symm hxg
  have hfib : ∀ c : ConjClasses G, c ∈ goodClasses Q →
      (goodElem Q).filter (fun x => ConjClasses.mk x = c) = c.carrier.toFinset := by
    intro c hc
    ext x
    rw [Finset.mem_filter, Set.mem_toFinset, ConjClasses.mem_carrier_iff_mk_eq]
    simp only [goodElem, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, hxc⟩
      exact hxc
    · intro hx
      exact ⟨(mem_goodClasses Q c).mp hc x (ConjClasses.mem_carrier_iff_mk_eq.mpr hx), hx⟩
  have hzero : ∀ c : ConjClasses G, c ∉ goodClasses Q →
      ∑ x ∈ (goodElem Q).filter (fun x => ConjClasses.mk x = c),
        Nat.card (Subgroup.centralizer ({(x : G)} : Set G)) = 0 := by
    intro c hc
    exact Finset.sum_eq_zero (fun x hx => absurd (hgood c x hx) hc)
  have hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (ConjClasses G)) : Set (ConjClasses G))
      (fun c => (goodElem Q).filter (fun x => ConjClasses.mk x = c)) := by
    rw [Finset.pairwiseDisjoint_iff]
    intro c _ c' _ hne
    obtain ⟨x, hx⟩ := hne
    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hx
    exact hx.1.2.symm.trans hx.2.2
  have hbiUnion : (Finset.univ : Finset (ConjClasses G)).biUnion
      (fun c => (goodElem Q).filter (fun x => ConjClasses.mk x = c)) = goodElem Q := by
    ext x
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨c, -, hx⟩
      exact (Finset.mem_filter.mp hx).1
    · intro hx
      exact ⟨ConjClasses.mk x, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
  rw [← hbiUnion, Finset.sum_biUnion hdisj]
  rw [← Finset.sum_subset (Finset.subset_univ (goodClasses Q)) (fun c _ hc => hzero c hc)]
  rw [Finset.sum_congr rfl (fun c hc => ?_)]
  · rw [Finset.sum_const, smul_eq_mul]
  · rw [hfib c hc]
    exact feit35_sum_centralizer_carrier c

end Work.ZassenhausTwoGroup
