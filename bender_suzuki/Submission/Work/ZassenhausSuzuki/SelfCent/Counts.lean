import Mathlib
import Submission.Work.ZassenhausSuzuki.CountingDefs
import Submission.Work.ZassenhausSuzuki.SzSetting
import Submission.Work.ZassenhausSuzuki.SingerData
import Submission.Work.ZassenhausSuzuki.SingerAux
import Submission.Work.ZassenhausSuzuki.centralizer_abelian_of_strongly_real
import Submission.Work.ZassenhausSuzuki.twoPoint_inverted

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The class count of Suzuki 1962 §8, pp. 118–119

This module contains the counting lemmas that pin down `[N_G(S.V) : S.V] = 2` — i.e.
`|N_G(S.V)| = 2(q+1)` — for the Singer cycle `S.V` of the Zassenhaus split rank-one set-up
(`SzHyp`), given the self-centralising property `C_G(S.V) = S.V` (proved in
`Submission.Work.ZassenhausSuzuki.SelfCent.SingerCent`).

* `not_conj_mem_Q_of_stronglyReal` (Suzuki 1962, Prop. 13/14): a strongly real `x` with
  `x * x ≠ 1` is never conjugate into the `2`-group `Q`.
* `two_mul_numClasses_nonzero_twoPoint_le`: each class meeting `D#` contains `k` and `k⁻¹`, so
  the number of classes meeting `D#` is at most `(|D|-1)/2`.
* `numClasses_stronglyReal_le` (HB III XI 10.8 (d)): every class of a strongly real element
  `x ≠ 1` with `x * x ≠ 1` meets `D#` or `S.V#` (given the element structure `hD3`).
* `mul_index_le_card_nonzero`: for a subgroup `V` all of whose non-identity elements are
  self-centralising, `#(classes meeting V#) * [N_G(V) : V] ≤ |V| - 1` (the `N_G(V)`-orbit of any
  element of `V#` lies in its class, and has `[N_G(V) : V]` elements).
* `centralizer_conj_eq`: `C_G(g x g⁻¹) = (C_G(x)).map (conj g)`.

Together with the count `#(classes of strongly real x ≠ 1, x * x ≠ 1) = |Q0sub H| - 1 = q - 1`
of Suzuki 1962 p. 118 (proved in `Submission.Work.ZassenhausSuzuki.numClasses_stronglyReal`),
these give `#(classes meeting S.V#) ≥ q/2`, hence `[N_G(S.V) : S.V] ≤ 2`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.ZassenhausSuzuki.SelfCent

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}

/-- Conjugation turns a centraliser into the image of a centraliser:
`C_G(g x g⁻¹) = (C_G x).map (conj g)`. -/
theorem centralizer_conj_eq (g x : G) :
    Subgroup.centralizer ({g * x * g⁻¹} : Set G) =
      (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · calc (g⁻¹ * y * g) * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hy]
        _ = x * (g⁻¹ * y * g) := by group
    · show MulAut.conj g (g⁻¹ * y * g) = y
      rw [MulAut.conj_apply]; group
  · rintro ⟨z, hz, rfl⟩
    show MulAut.conj g z * MulAut.conj g x = MulAut.conj g x * MulAut.conj g z
    rw [← map_mul, ← map_mul, hz]

/-- **No strongly real element of order `≠ 2` is conjugate into `Q`** (Suzuki 1962, Prop. 13–14).
If `x = a * b` is a product of two involutions with `x * x ≠ 1` then no conjugate of `x` lies in
the `2`-group `Q`: Proposition 14 makes `C_G(x)` of odd order, so `orderOf x` is odd, while an
element of `Q` has `2`-power order. -/
theorem not_conj_mem_Q_of_stronglyReal (h : SzHyp H Q t s) {x : G} (hx2 : x * x ≠ 1)
    (hsr : IsStronglyReal x) : ¬ (∃ g : G, g * x * g⁻¹ ∈ Q) := by
  rintro ⟨g, hg⟩
  obtain ⟨-, hodd, -⟩ := centralizer_abelian_of_strongly_real h.split h.zass h.two hx2 hsr
  have hxmem : x ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hoddx : Odd (orderOf x) :=
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hxmem)
  obtain ⟨e, he⟩ := h.two.exists_card_eq
  have hconj : orderOf (g * x * g⁻¹) = orderOf x := by
    rw [show g * x * g⁻¹ = MulAut.conj g x from (MulAut.conj_apply g x).symm]
    exact MulEquiv.orderOf_eq (MulAut.conj g) x
  have hdvd : orderOf x ∣ 2 ^ e := by
    rw [← hconj, ← he]
    exact Subgroup.orderOf_dvd_natCard Q hg
  have hcop : Nat.Coprime (orderOf x) (2 ^ e) := (Nat.coprime_two_right.mpr hoddx).pow_right e
  have h1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd
  exact hx2 (by rw [orderOf_eq_one_iff.mp h1, mul_one])

/-- **The classes meeting `D#`** (`D = twoPoint H t`): each of them contains at least the two
elements `k`, `k⁻¹` of `D#` (`t` inverts `D`, and `D` has odd order so `k⁻¹ ≠ k`), hence

  `2 * #(classes meeting D#) ≤ |D| - 1`. -/
theorem two_mul_numClasses_nonzero_twoPoint_le (h : SzHyp H Q t s) :
    2 * numClasses (nonzero (twoPoint H t : Set G)) ≤ Nat.card ↥(twoPoint H t) - 1 := by
  classical
  haveI : Fintype (ConjClasses G) := Fintype.ofFinite _
  have hoddD : Odd (Nat.card ↥(twoPoint H t)) := Work.ThmF.split_odd_card_twoPoint h.split
  have hinv : ∀ d : G, d ∈ twoPoint H t → t * d * t⁻¹ = d⁻¹ :=
    twoPoint_inverted h.split h.zass (SzHyp.Q_ne_bot h) h.two
  have ht2 : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rw [h.split.invol] at h1
    simpa [pow_two] using h1
  -- the non-identity elements of `D`
  let α := {d : G // d ∈ (twoPoint H t : Set G) ∧ d ≠ 1}
  haveI : Fintype α := Fintype.ofFinite _
  have hcardα : Nat.card α = Nat.card ↥(twoPoint H t) - 1 := by
    have h1 : Nat.card α =
        Nat.card ((((twoPoint H t : Subgroup G) : Set G)) \ {1} : Set G) := rfl
    rw [h1, Nat.card_coe_set_eq,
      Set.ncard_sdiff_singleton_of_mem (twoPoint H t).one_mem]
    congr 1
  -- the classes meeting `D#`
  let 𝓒 : Finset (ConjClasses G) :=
    Finset.univ.filter (fun C => (C.carrier ∩ nonzero (twoPoint H t : Set G)).Nonempty)
  have h𝓒card : 𝓒.card = numClasses (nonzero (twoPoint H t : Set G)) := by
    rw [numClasses]
    have h1 : Nat.card {C : ConjClasses G // (C.carrier ∩ nonzero
        (twoPoint H t : Set G)).Nonempty} = Fintype.card {C : ConjClasses G //
          (C.carrier ∩ nonzero (twoPoint H t : Set G)).Nonempty} := Nat.card_eq_fintype_card
    rw [h1, Fintype.card_subtype]
  -- every such class contains `k` and `k⁻¹` for `k ∈ C ∩ D#`
  have hfiber : ∀ C ∈ 𝓒, 2 ≤ (Finset.univ.filter
      (fun d : α => (ConjClasses.mk d.1 : ConjClasses G) = C)).card := by
    intro C hC
    rw [Finset.mem_filter] at hC
    obtain ⟨-, d, hdC, hdD, hd1⟩ := hC
    have hdinv : d⁻¹ ∈ twoPoint H t := (twoPoint H t).inv_mem hdD
    have hdne : d⁻¹ ≠ d := by
      intro hcon
      have hsq : d * d = 1 := by
        have h2 : d = d⁻¹ := hcon.symm
        nth_rewrite 2 [h2]
        exact mul_inv_cancel d
      have hdvd : orderOf d ∣ Nat.card ↥(twoPoint H t) :=
        Subgroup.orderOf_dvd_natCard _ hdD
      have hdvd2 : orderOf d ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one]; simpa [pow_two] using hsq
      have hodd_ord : Odd (orderOf d) := Odd.of_dvd_nat hoddD hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h2 | h2
      · exact hd1 (orderOf_eq_one_iff.mp h2)
      · rw [h2] at hodd_ord
        exact absurd hodd_ord (by decide)
    have hmkd : (ConjClasses.mk d : ConjClasses G) = C :=
      ConjClasses.mem_carrier_iff_mk_eq.mp hdC
    have hmkinv : (ConjClasses.mk d⁻¹ : ConjClasses G) = C := by
      rw [← hmkd, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
      refine ⟨t, ?_⟩
      rw [← hinv d hdD, inv_eq_of_mul_eq_one_right ht2]
      rw [show t * (t * d * t) * t = (t * t) * d * (t * t) by group, ht2]
      group
    have hsub : ({⟨d, hdD, hd1⟩, ⟨d⁻¹, hdinv, inv_ne_one.mpr hd1⟩} : Finset α) ⊆
        (Finset.univ.filter (fun d : α => (ConjClasses.mk d.1 : ConjClasses G) = C)) := by
      intro e he
      rw [Finset.mem_insert, Finset.mem_singleton] at he
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases he with rfl | rfl
      · exact hmkd
      · exact hmkinv
    have h2 : ({⟨d, hdD, hd1⟩, ⟨d⁻¹, hdinv, inv_ne_one.mpr hd1⟩} : Finset α).card = 2 := by
      rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_singleton]
            exact fun hc => hdne (congrArg Subtype.val hc).symm), Finset.card_singleton]
    exact le_trans (le_of_eq h2.symm) (Finset.card_le_card hsub)
  -- sum the fibres
  have hsum := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset α))
    (t := (Finset.univ : Finset (ConjClasses G)))
    (f := fun d : α => (ConjClasses.mk d.1 : ConjClasses G)) (fun x _ => Finset.mem_univ _)
  have hmain : 2 * 𝓒.card ≤ (Finset.univ : Finset α).card := by
    calc 2 * 𝓒.card = 𝓒.sum (fun _ => 2) := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      _ ≤ 𝓒.sum (fun C => (Finset.univ.filter
            (fun d : α => (ConjClasses.mk d.1 : ConjClasses G) = C)).card) :=
          Finset.sum_le_sum (fun C hC => hfiber C hC)
      _ ≤ (Finset.univ : Finset (ConjClasses G)).sum (fun C => (Finset.univ.filter
            (fun d : α => (ConjClasses.mk d.1 : ConjClasses G) = C)).card) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun x _ _ => Nat.zero_le _)
      _ = (Finset.univ : Finset α).card := hsum.symm
  rw [h𝓒card, Finset.card_univ, ← Nat.card_eq_fintype_card, hcardα] at hmain
  exact hmain

/-- **The classes of strongly real elements `x ≠ 1` with `x * x ≠ 1` meet `D#` or `S.V#`**
(HB III XI 10.8 (d)).  Given the element structure `hD3` and the exclusion of the `Q`-case
(`hE1`), the number of such classes is at most the number of classes meeting `D#` plus the number
meeting `S.V#`. -/
theorem numClasses_stronglyReal_le (h : SzHyp H Q t s) (S : SingerCycle.Data G H t)
    (hD3 : ∀ x : G, x * x ≠ 1 → IsStronglyReal x →
      (∃ g : G, g * x * g⁻¹ ∈ Q) ∨
        (∃ g : G, g * x * g⁻¹ ∈ twoPoint H t) ∨
        (∃ g : G, g * x * g⁻¹ ∈ S.V))
    (hE1 : ∀ x : G, x * x ≠ 1 → IsStronglyReal x → ¬ (∃ g : G, g * x * g⁻¹ ∈ Q)) :
    numClasses {x : G | IsStronglyReal x ∧ x ≠ 1 ∧ x * x ≠ 1}
      ≤ numClasses (nonzero (twoPoint H t : Set G)) + numClasses (nonzero (S.V : Set G)) := by
  classical
  haveI : Fintype (ConjClasses G) := Fintype.ofFinite _
  -- every class meeting `X` meets `D#` or `V#`
  have hkey : ∀ C : ConjClasses G,
      (C.carrier ∩ {x : G | IsStronglyReal x ∧ x ≠ 1 ∧ x * x ≠ 1}).Nonempty →
      (C.carrier ∩ nonzero (twoPoint H t : Set G)).Nonempty ∨
        (C.carrier ∩ nonzero (S.V : Set G)).Nonempty := by
    intro C hC
    obtain ⟨x, hxC, hsr, hx1, hx2⟩ := hC
    have hmkx : (ConjClasses.mk x : ConjClasses G) = C :=
      ConjClasses.mem_carrier_iff_mk_eq.mp hxC
    have hmemC : ∀ g : G, g * x * g⁻¹ ∈ C.carrier := by
      intro g
      rw [← hmkx, ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj,
        isConj_iff]
      exact ⟨g⁻¹, by group⟩
    have hne : ∀ g : G, g * x * g⁻¹ ≠ 1 := by
      intro g hcon
      exact hx1 (by
        have h' : x = g⁻¹ * (g * x * g⁻¹) * g := by group
        rw [h', hcon]; group)
    rcases hD3 x hx2 hsr with ⟨g, hg⟩ | ⟨g, hg⟩ | ⟨g, hg⟩
    · exact absurd ⟨g, hg⟩ (hE1 x hx2 hsr)
    · exact Or.inl ⟨g * x * g⁻¹, hmemC g, hg, hne g⟩
    · exact Or.inr ⟨g * x * g⁻¹, hmemC g, hg, hne g⟩
  -- the finset inclusion
  have hsub : (Finset.univ.filter (fun C : ConjClasses G =>
        (C.carrier ∩ {x : G | IsStronglyReal x ∧ x ≠ 1 ∧ x * x ≠ 1}).Nonempty)) ⊆
      (Finset.univ.filter (fun C : ConjClasses G =>
          (C.carrier ∩ nonzero (twoPoint H t : Set G)).Nonempty)) ∪
        (Finset.univ.filter (fun C : ConjClasses G =>
          (C.carrier ∩ nonzero (S.V : Set G)).Nonempty)) := by
    intro C hC
    rw [Finset.mem_filter] at hC
    rcases hkey C hC.2 with hCA | hCB
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCA⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCB⟩)
  have hnum : ∀ Z : Set G, (Finset.univ.filter
      (fun C : ConjClasses G => (C.carrier ∩ Z).Nonempty)).card = numClasses Z := by
    intro Z
    rw [numClasses]
    have h1 : Nat.card {C : ConjClasses G // (C.carrier ∩ Z).Nonempty} =
        Fintype.card {C : ConjClasses G // (C.carrier ∩ Z).Nonempty} := Nat.card_eq_fintype_card
    rw [h1, Fintype.card_subtype]
  calc numClasses {x : G | IsStronglyReal x ∧ x ≠ 1 ∧ x * x ≠ 1}
      = (Finset.univ.filter (fun C : ConjClasses G =>
          (C.carrier ∩ {x : G | IsStronglyReal x ∧ x ≠ 1 ∧ x * x ≠ 1}).Nonempty)).card :=
        (hnum _).symm
    _ ≤ ((Finset.univ.filter (fun C : ConjClasses G =>
          (C.carrier ∩ nonzero (twoPoint H t : Set G)).Nonempty)) ∪
        (Finset.univ.filter (fun C : ConjClasses G =>
          (C.carrier ∩ nonzero (S.V : Set G)).Nonempty))).card := Finset.card_le_card hsub
    _ ≤ _ + _ := Finset.card_union_le _ _
    _ = numClasses (nonzero (twoPoint H t : Set G)) + numClasses (nonzero (S.V : Set G)) := by
        rw [hnum, hnum]

/-- **The fibre count for the Singer cycle** (Suzuki 1962 §8, p. 118).  If every non-identity
element of a subgroup `V ≤ G` is self-centralising (`C_G(v) = V`), then every conjugacy class
meeting `V#` contains at least `[N_G(V) : V]` elements of `V#` (namely the `N_G(V)`-orbit of any
of its elements), whence

  `#(classes meeting V#) * [N_G(V) : V] ≤ |V| - 1`. -/
theorem mul_index_le_card_nonzero (V : Subgroup G)
    (hcent : ∀ v : G, v ∈ (V : Set G) → v ≠ 1 → Subgroup.centralizer ({v} : Set G) = V) :
    numClasses (nonzero (V : Set G)) *
        (V.subgroupOf (Subgroup.normalizer (V : Set G))).index ≤ Nat.card ↥V - 1 := by
  classical
  haveI hCj : Fintype (ConjClasses G) := Fintype.ofFinite _
  set N : Subgroup G := Subgroup.normalizer (V : Set G) with hNdef
  have hVN : V ≤ N := Subgroup.le_normalizer
  haveI hVf : Fintype ↥V := Fintype.ofFinite _
  haveI hNf : Fintype ↥N := Fintype.ofFinite _
  let α := {v : G // v ∈ (V : Set G) ∧ v ≠ 1}
  haveI : Fintype α := Fintype.ofFinite _
  have hcardα : Nat.card α = Nat.card ↥V - 1 := by
    have h1 : Nat.card α = Nat.card ((((V : Subgroup G) : Set G)) \ {1} : Set G) := rfl
    rw [h1, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem V.one_mem]
    congr 1
  -- the classes meeting `V#`
  let 𝓒 : Finset (ConjClasses G) :=
    Finset.univ.filter (fun C => (C.carrier ∩ nonzero (V : Set G)).Nonempty)
  have h𝓒card : 𝓒.card = numClasses (nonzero (V : Set G)) := by
    rw [numClasses]
    have h1 : Nat.card {C : ConjClasses G // (C.carrier ∩ nonzero (V : Set G)).Nonempty} =
        Fintype.card {C : ConjClasses G // (C.carrier ∩ nonzero (V : Set G)).Nonempty} :=
      Nat.card_eq_fintype_card
    rw [h1, Fintype.card_subtype]
  -- every class meeting `V#` contains the whole `N`-orbit of each of its elements, of size `index`
  have hle : ∀ C ∈ 𝓒, (V.subgroupOf N).index ≤
      Nat.card {v : α // (ConjClasses.mk v.1 : ConjClasses G) = C} := by
    intro C hC
    rw [Finset.mem_filter] at hC
    obtain ⟨-, v₀, hv₀C, hv₀V, hv₀1⟩ := hC
    have hmkv₀ : (ConjClasses.mk v₀ : ConjClasses G) = C :=
      ConjClasses.mem_carrier_iff_mk_eq.mp hv₀C
    -- the stabiliser of `v₀` in `N` is `V`
    have hstab : MulAction.stabilizer ↥N (⟨v₀, hv₀V⟩ : ↥V) = V.subgroupOf N := by
      ext g
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
      constructor
      · intro hg
        have h2 : (g : G) * v₀ * (g : G)⁻¹ = v₀ := congrArg (fun t : ↥V => (t : G)) hg
        have h3 : (g : G) * v₀ = v₀ * (g : G) := by
          calc (g : G) * v₀ = ((g : G) * v₀ * (g : G)⁻¹) * (g : G) := by group
            _ = v₀ * (g : G) := by rw [h2]
        rw [← hcent v₀ hv₀V hv₀1]
        exact Subgroup.mem_centralizer_singleton_iff.mpr h3
      · intro hg
        have h4 : (g : G) ∈ Subgroup.centralizer ({v₀} : Set G) := by
          rw [hcent v₀ hv₀V hv₀1]
          exact hg
        have h3 : (g : G) * v₀ = v₀ * (g : G) := Subgroup.mem_centralizer_singleton_iff.mp h4
        show (g • (⟨v₀, hv₀V⟩ : ↥V) : ↥V) = ⟨v₀, hv₀V⟩
        apply Subtype.ext
        show (g : G) * v₀ * (g : G)⁻¹ = v₀
        rw [h3]; group
    have horbitcard : Nat.card (MulAction.orbit ↥N (⟨v₀, hv₀V⟩ : ↥V)) =
        (V.subgroupOf N).index := by
      have h1 := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥N)
        (⟨v₀, hv₀V⟩ : ↥V)
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
        at h1
      rw [hstab] at h1
      have hcardV : Nat.card ↥(V.subgroupOf N) = Nat.card ↥V :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv
      have hNcard : Nat.card ↥N = Nat.card ↥V * (V.subgroupOf N).index := by
        have h2 := Subgroup.card_mul_index (V.subgroupOf N)
        rw [hcardV] at h2
        exact h2.symm
      rw [hcardV, hNcard, Nat.mul_comm (Nat.card ↥V) (V.subgroupOf N).index] at h1
      exact Nat.mul_right_cancel (Nat.card_pos (α := ↥V)) h1
    -- the orbit injects into the fibre
    have hmem1 : ∀ u : MulAction.orbit ↥N (⟨v₀, hv₀V⟩ : ↥V), ((u.1 : ↥V) : G) ≠ 1 := by
      intro u
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp u.2
      have hval : ((u.1 : ↥V) : G) = (g : G) * v₀ * (g : G)⁻¹ := by rw [← hg]; rfl
      rw [hval]
      intro hcon
      exact hv₀1 (by
        have h' : v₀ = (g : G)⁻¹ * ((g : G) * v₀ * (g : G)⁻¹) * (g : G) := by group
        rw [h', hcon]; group)
    have hmem2 : ∀ u : MulAction.orbit ↥N (⟨v₀, hv₀V⟩ : ↥V),
        (ConjClasses.mk ((u.1 : ↥V) : G) : ConjClasses G) = C := by
      intro u
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp u.2
      have hval : ((u.1 : ↥V) : G) = (g : G) * v₀ * (g : G)⁻¹ := by rw [← hg]; rfl
      rw [hval, ← hmkv₀, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
      exact ⟨(g : G)⁻¹, by group⟩
    rw [← horbitcard]
    refine Nat.card_le_card_of_injective
      (fun u : MulAction.orbit ↥N (⟨v₀, hv₀V⟩ : ↥V) =>
        (⟨⟨((u.1 : ↥V) : G), u.1.2, hmem1 u⟩, hmem2 u⟩ :
          {v : α // (ConjClasses.mk v.1 : ConjClasses G) = C})) ?_
    intro u u' huu
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t => ((t.1 : α) : G)) huu
  -- sum the fibres
  have hsum := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset α))
    (t := (Finset.univ : Finset (ConjClasses G)))
    (f := fun v : α => (ConjClasses.mk v.1 : ConjClasses G)) (fun x _ => Finset.mem_univ _)
  have hmain : 𝓒.card * (V.subgroupOf N).index ≤ (Finset.univ : Finset α).card := by
    calc 𝓒.card * (V.subgroupOf N).index = 𝓒.sum (fun _ => (V.subgroupOf N).index) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 𝓒.sum (fun C => (Finset.univ.filter
            (fun v : α => (ConjClasses.mk v.1 : ConjClasses G) = C)).card) :=
          Finset.sum_le_sum (fun C hC => by
            have h1 : (Finset.univ.filter
                (fun v : α => (ConjClasses.mk v.1 : ConjClasses G) = C)).card =
                Nat.card {v : α // (ConjClasses.mk v.1 : ConjClasses G) = C} := by
              rw [← Fintype.card_subtype, Nat.card_eq_fintype_card]
            rw [h1]
            exact hle C hC)
      _ ≤ (Finset.univ : Finset (ConjClasses G)).sum (fun C => (Finset.univ.filter
            (fun v : α => (ConjClasses.mk v.1 : ConjClasses G) = C)).card) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun x _ _ => Nat.zero_le _)
      _ = (Finset.univ : Finset α).card := hsum.symm
  rw [h𝓒card, Finset.card_univ, ← Nat.card_eq_fintype_card, hcardα] at hmain
  exact hmain

end Work.ZassenhausSuzuki.SelfCent
