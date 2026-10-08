/-
# BMAX — `C_G(O^p(S)) ∩ B ≤ A` for a witness `S` between `E(A)` and `F*(A)`

This file proves

  `Work.BMAX.centralizer_pResidualIn_witness_le`

one of the elementary steps of Bender 1970 §1.7 (the "if `O^p(F*(A)) ≠ 1` then
`C_G(O^p(S)) ≤ A`" line of the printed proof, in the weakened form `… ∩ B ≤ A` needed here).

## Mathematics

Assume `G` is a finite simple group, `A < G` maximal (`IsCoatom A`), and `S` is a subgroup with

  `E(A) = layerIn A ≤ S ≤ F*(A) = fstarIn A`,   `Z(F(A)) = zcenterIn (fittingIn A) ≤ S`.

Assume `p` is a prime with `O^p(F*(A)) = pResidualIn p (fstarIn A) ≠ ⊥`.  Then

  `C_G(O^p(S)) ∩ B ≤ A`.

The coatom/simplicity argument (`le_coatom_of_le_normalizer_of_ne_bot`) shows that it suffices
to exhibit `⊥ ≠ N ≤ A` with `N` normalised by `A` and by `C_G(O^p(S))`; the natural choice is

  `N := O^p(E(A)) ⊔ O^p(Z(F(A)))`.

* `N ≤ O^p(S)`: both summands are `O^p` of subgroups of `S` (`layerIn A ≤ S`, `zcenterIn … ≤ S`)
  and `O^p` is monotone.
* `N ≤ A` and `A ≤ N_G(N)`: `E(A)` is normal in `A`, `Z(F(A))` is characteristic in `A`, and
  `O^p` of a subgroup normalised by `A` is again normalised by `A`.
* `N ≠ ⊥`: if `O^p(E(A)) = ⊥` and `O^p(Z(F(A))) = ⊥` then `E(A)` and `Z(F(A))` are `p`-groups.
  A finite nilpotent group whose centre is a `p`-group is a `p`-group
  (`Group.IsNilpotent.prime_dvd_card_center`), so `F(A)` is a `p`-group; the product of the
  normal `p`-subgroups `F(A)` and `E(A)` is then a `p`-group, i.e. `O^p(F*(A)) = ⊥`, contrary to
  the hypothesis.

## Formalisation

The elementary group theory is collected above the theorem; the two inputs about `F(A)` are
`isNilpotent_fittingIn` (the contract's `fitting` is Isaacs' Fitting subgroup, via
`Work.CORE2A.fitting_eq_isaacsFitting`) and the characterisation `pResidual = ⊥ ↔ IsPGroup`.
-/
import Mathlib
import Submission.Work.BMAX.D17Defs
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.Basic
import Submission.Work.CORE2A.thm26_aux
import Submission.Work.BMAX.FstarSamePrime

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Work.BMAX

open Subgroup

/-! ## 1. `O^p` of a finite group vanishes exactly on `p`-groups -/

/-- For a finite group, the `p`-residual `O^p(H) = ⟨{x | p ∤ orderOf x}⟩` is trivial if and
only if `H` is a `p`-group.

(`⟸`) In a `p`-group every element has `p`-power order, so the generating set is `{1}`.
(`⟹`) If `H` is not a `p`-group then some prime `q ≠ p` divides `|H|`; Cauchy's theorem gives an
element of order `q`, a nontrivial `p'`-element. -/
theorem pResidual_eq_bot_iff_isPGroup {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime] :
    Work.BMAX.pResidual p H = ⊥ ↔ IsPGroup p H := by
  constructor
  · intro h
    rw [isPGroup_iff_primeFactors_card_subset (Fact.out : Nat.Prime p).ne_zero]
    intro q hq
    have hqprime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
    have hqdiv : q ∣ Nat.card H := (Nat.mem_primeFactors.mp hq).2.1
    by_contra hqp
    have hqne : q ≠ p := fun h' => hqp (by
      rw [h', (Fact.out : Nat.Prime p).primeFactors]; exact Finset.mem_singleton_self p)
    haveI : Fact q.Prime := ⟨hqprime⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hqdiv
    have hxbot : x ∈ Work.BMAX.pResidual p H :=
      Work.BMAX.pResidual.subset_closure (by
        rw [hx]
        exact fun hpq => hqne ((Nat.prime_dvd_prime_iff_eq Fact.out hqprime).mp hpq).symm)
    rw [h] at hxbot
    have hx1 : x = 1 := hxbot
    rw [hx1, orderOf_one] at hx
    exact hqprime.ne_one hx.symm
  · intro h
    rw [eq_bot_iff, Work.BMAX.pResidual, Subgroup.closure_le]
    intro x hx
    change x = 1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).mp h x
    by_cases hk0 : k = 0
    · exact orderOf_eq_one_iff.mp (by rw [hk, hk0, pow_zero])
    · exact absurd (hk ▸ dvd_pow_self p hk0) hx

/-- The relative version: for a subgroup `K ≤ G` of a finite group, `O^p(K) = ⊥` iff `K` is a
`p`-group.  (Reduce to `pResidual` along the injective `K.subtype`.) -/
theorem pResidualIn_eq_bot_iff_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (K : Subgroup G) : Work.BMAX.pResidualIn p K = ⊥ ↔ IsPGroup p ↥K := by
  rw [Work.BMAX.pResidualIn.eq_map, Subgroup.map_eq_bot_iff]
  have hker : K.subtype.ker = ⊥ := MonoidHom.ker_eq_bot_iff _ |>.mpr K.subtype_injective
  rw [hker, le_bot_iff, pResidual_eq_bot_iff_isPGroup]

/-! ## 2. A finite nilpotent group whose centre is a `p`-group is a `p`-group -/

/-- If `H` is finite and nilpotent and its centre `Z(H)` is a `p`-group, then `H` is a
`p`-group.

Indeed every prime `q` dividing `|H|` divides `|Z(H)|` (`Group.IsNilpotent.prime_dvd_card_center`),
and the only prime dividing `|Z(H)|` is `p`. -/
theorem isPGroup_of_isPGroup_center_of_isNilpotent {H : Type*} [Group H] [Finite H]
    [Group.IsNilpotent H] {p : ℕ} [Fact p.Prime]
    (h : IsPGroup p ↥(Subgroup.center H)) : IsPGroup p H := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp h
  rw [isPGroup_iff_primeFactors_card_subset (Fact.out : Nat.Prime p).ne_zero]
  intro q hq
  have hqprime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
  have hqdiv : q ∣ Nat.card H := (Nat.mem_primeFactors.mp hq).2.1
  haveI : Fact q.Prime := ⟨hqprime⟩
  have hqdivc : q ∣ Nat.card ↥(Subgroup.center H) :=
    Group.IsNilpotent.prime_dvd_card_center hqdiv
  rw [hk] at hqdivc
  have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hqprime Fact.out).mp
    (hqprime.dvd_of_dvd_pow hqdivc)
  rw [hqp, (Fact.out : Nat.Prime p).primeFactors]
  exact Finset.mem_singleton_self p

/-! ## 3. `zcenterIn` is the image of the centre -/


/-- `zcenterIn K` is a `p`-group iff the centre of `↥K` is (the two have the same cardinality,
`|K.subtype '' Z(K)| = |Z(K)|`). -/
theorem isPGroup_zcenterIn_iff {G : Type*} [Group G] [Finite G] {K : Subgroup G} {p : ℕ}
    [Fact p.Prime] :
    IsPGroup p ↥(Work.GW2.zcenterIn K) ↔ IsPGroup p ↥(Subgroup.center ↥K) := by
  have hcard : Nat.card ↥(Work.GW2.zcenterIn K) = Nat.card ↥(Subgroup.center ↥K) := by
    rw [zcenterIn_eq_map_center, Subgroup.card_map_of_injective K.subtype_injective]
  rw [isPGroup_iff_primeFactors_card_subset (Fact.out : Nat.Prime p).ne_zero,
      isPGroup_iff_primeFactors_card_subset (Fact.out : Nat.Prime p).ne_zero, hcard]

/-! ## 4. Normalizer containments -/

/-- A normal subgroup `L` of `↥A` gives a subgroup `L.map A.subtype` normalised by `A`. -/
theorem le_normalizer_map_subtype_of_normal {G : Type*} [Group G] {A : Subgroup G}
    {L : Subgroup ↥A} (hL : L.Normal) :
    A ≤ Subgroup.normalizer ((L.map A.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro a ha x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨(⟨a, ha⟩ : ↥A) * y * (⟨a, ha⟩ : ↥A)⁻¹, hL.conj_mem y hy ⟨a, ha⟩, rfl⟩

/-- The layer `E(A) = ⨆ {E | E.Normal ∧ IsQuasisimple E}` is normal in `↥A`. -/
theorem layer_normal {G : Type*} [Group G] (A : Subgroup G) :
    (Work.GW2.layer A).Normal :=
  Subgroup.sSup_normal _ (fun _ hH => hH.1)

/-- `E(A) = layerIn A` is normalised by `A`. -/
theorem le_normalizer_layerIn {G : Type*} [Group G] (A : Subgroup G) :
    A ≤ Subgroup.normalizer ((Work.GW2.layerIn A : Subgroup G) : Set G) := by
  rw [Work.GW2.layerIn]
  exact le_normalizer_map_subtype_of_normal (layer_normal A)

/-- The Fitting subgroup `F(A)` is normal in `↥A`. -/
theorem fitting_normal {G : Type*} [Group G] (A : Subgroup G) :
    (Work.GW2.fitting A).Normal := by
  rw [Work.GW2.fitting]
  exact Subgroup.normalCore_normal _

/-- `F(A) = fittingIn A` is normalised by `A`. -/
theorem le_normalizer_fittingIn {G : Type*} [Group G] (A : Subgroup G) :
    A ≤ Subgroup.normalizer ((Work.GW2.fittingIn A : Subgroup G) : Set G) := by
  rw [Work.GW2.fittingIn]
  exact le_normalizer_map_subtype_of_normal (fitting_normal A)

/-- `Z(K) = zcenterIn K` is normalised by any subgroup normalising `K` (the centre is
characteristic; verified here by an explicit conjugation computation). -/
theorem le_normalizer_zcenterIn_of_le_normalizer {G : Type*} [Group G] {K C : Subgroup G}
    (h : C ≤ Subgroup.normalizer (K : Set G)) :
    C ≤ Subgroup.normalizer ((Work.GW2.zcenterIn K : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff] at h ⊢
  intro c hc z hz
  obtain ⟨hzK, hzc⟩ := hz
  refine ⟨h c hc z hzK, fun y hy => ?_⟩
  have hcyK : c⁻¹ * y * c ∈ K := by
    have hh := h c⁻¹ (C.inv_mem hc) y hy
    rwa [inv_inv] at hh
  have hstep : c * z * c⁻¹ * y = c * (z * (c⁻¹ * y * c)) * c⁻¹ := by group
  rw [hstep, hzc (c⁻¹ * y * c) hcyK]
  group

/-- `O^p(K)` is normalised by any subgroup normalising `K` (conjugation preserves `K` and the
order of an element, hence permutes the `p'`-elements generating `O^p(K)`). -/
theorem le_normalizer_pResidualIn_of_le_normalizer {G : Type*} [Group G] {K C : Subgroup G}
    {p : ℕ} (h : C ≤ Subgroup.normalizer (K : Set G)) :
    C ≤ Subgroup.normalizer ((Work.BMAX.pResidualIn p K : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff] at h ⊢
  intro c hc x hx
  have hmap : (Work.BMAX.pResidualIn p K).map (MulAut.conj c).toMonoidHom ≤
      Work.BMAX.pResidualIn p K := by
    rw [Work.BMAX.pResidualIn, MonoidHom.map_closure, Subgroup.closure_le]
    rintro y ⟨z, hz, rfl⟩
    exact Subgroup.subset_closure ⟨h c hc z hz.1, by
      show ¬ p ∣ orderOf ((MulAut.conj c) z)
      rw [MulAut.conj_apply, Work.BMAX.orderOf_conj_eq]
      exact hz.2⟩
  exact hmap (Subgroup.mem_map.mpr ⟨x, hx, by
    show (MulAut.conj c) x = c * x * c⁻¹
    rw [MulAut.conj_apply]⟩)

/-! ## 5. `F(A)` is nilpotent -/

/-- The Fitting subgroup `F(A)` (as a group in its own right) is nilpotent.  Fitting's theorem
is available for Isaacs' Fitting subgroup in the odd-order library; `fittingIn` is carried to it
by `Work.CORE2A.fitting_eq_isaacsFitting`. -/
theorem isNilpotent_fittingIn {G : Type} [Group G] [Finite G] (A : Subgroup G) :
    Group.IsNilpotent ↥(Work.GW2.fittingIn A) := by
  haveI : Group.IsNilpotent ↥(Work.GW2.fitting A) := by
    rw [Work.CORE2A.fitting_eq_isaacsFitting (G := ↥A)]
    infer_instance
  rw [show Work.GW2.fittingIn A = (Work.GW2.fitting A).map A.subtype from rfl]
  exact (Group.isNilpotent_congr
    (Subgroup.equivMapOfInjective (Work.GW2.fitting A) A.subtype A.subtype_injective)).mp
    inferInstance

/-! ## 6. The theorem -/

theorem centralizer_pResidualIn_witness_le {G : Type} [Group G] [Finite G]
    (hG : IsSimpleGroup G) (A B S : Subgroup G) (hA : IsCoatom A) (hB : B ≠ ⊤)
    (hA_D : Work.GW2.IsDGroup A) (hSB : S ≤ B) (hSf : S ≤ Work.GW2.fstarIn A)
    (hSl : Work.GW2.layerIn A ≤ S) (hZs : Work.GW2.zcenterIn (Work.GW2.fittingIn A) ≤ S)
    (p : ℕ) (hp : p.Prime) (hpi : p ∈ Work.GW2.primesOf (Work.GW2.fittingIn A))
    (hne : Work.BMAX.pResidualIn p (Work.GW2.fstarIn A) ≠ ⊥) :
    Subgroup.centralizer ((Work.BMAX.pResidualIn p S : Subgroup G) : Set G) ⊓ B ≤ A := by
  haveI : Fact p.Prime := ⟨hp⟩
  set N : Subgroup G := Work.BMAX.pResidualIn p (Work.GW2.layerIn A) ⊔
      Work.BMAX.pResidualIn p (Work.GW2.zcenterIn (Work.GW2.fittingIn A)) with hN
  have hNS : N ≤ Work.BMAX.pResidualIn p S :=
    sup_le (Work.BMAX.pResidualIn.mono hSl) (Work.BMAX.pResidualIn.mono hZs)
  have hNA : N ≤ A :=
    sup_le (le_trans (Work.BMAX.pResidualIn.le _) (Work.GW2.layerIn_le_self A))
      (le_trans (Work.BMAX.pResidualIn.le _)
        (le_trans (Work.GW2.zcenterIn_le _) (Work.GW2.fittingIn_le_self A)))
  have hAnorm : A ≤ Subgroup.normalizer (N : Set G) := by
    rw [hN]
    refine le_trans (le_inf ?_ ?_) (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    · exact le_normalizer_pResidualIn_of_le_normalizer (le_normalizer_layerIn A)
    · exact le_normalizer_pResidualIn_of_le_normalizer
        (le_normalizer_zcenterIn_of_le_normalizer (le_normalizer_fittingIn A))
  have hNbot : N ≠ ⊥ := by
    rw [hN]
    intro hbot
    rw [sup_eq_bot_iff] at hbot
    obtain ⟨hEl, hZl⟩ := hbot
    -- `E(A)` and `Z(F(A))` are `p`-groups
    have hElpg : IsPGroup p ↥(Work.GW2.layerIn A) :=
      (pResidualIn_eq_bot_iff_isPGroup _).mp hEl
    have hZpg : IsPGroup p ↥(Work.GW2.zcenterIn (Work.GW2.fittingIn A)) :=
      (pResidualIn_eq_bot_iff_isPGroup _).mp hZl
    -- hence so is `F(A)`, because `F(A)` is nilpotent
    haveI hFnil : Group.IsNilpotent ↥(Work.GW2.fittingIn A) := isNilpotent_fittingIn A
    have hFpg : IsPGroup p ↥(Work.GW2.fittingIn A) :=
      isPGroup_of_isPGroup_center_of_isNilpotent ((isPGroup_zcenterIn_iff).mp hZpg)
    have hcardF : Nat.card ↥(Work.GW2.fittingIn A) = Nat.card ↥(Work.GW2.fitting A) := by
      rw [Work.GW2.fittingIn, Subgroup.card_map_of_injective A.subtype_injective]
    have hFpgA : IsPGroup p ↥(Work.GW2.fitting A) := by
      rw [isPGroup_iff_primeFactors_card_subset hp.ne_zero, ← hcardF]
      exact (isPGroup_iff_primeFactors_card_subset hp.ne_zero).mp hFpg
    have hcardE : Nat.card ↥(Work.GW2.layerIn A) = Nat.card ↥(Work.GW2.layer A) := by
      rw [Work.GW2.layerIn, Subgroup.card_map_of_injective A.subtype_injective]
    have hEpgA : IsPGroup p ↥(Work.GW2.layer A) := by
      rw [isPGroup_iff_primeFactors_card_subset hp.ne_zero, ← hcardE]
      exact (isPGroup_iff_primeFactors_card_subset hp.ne_zero).mp hElpg
    -- the product of the normal `p`-subgroups `F(A)`, `E(A)` is a `p`-group
    haveI : (Work.GW2.fitting A).Normal := fitting_normal A
    have hFE : IsPGroup p ↥(Work.GW2.fitting A ⊔ Work.GW2.layer A) :=
      IsPGroup.to_sup_of_normal_left hFpgA hEpgA
    have hcardFE : Nat.card ↥(Work.GW2.fstarIn A) =
        Nat.card ↥(Work.GW2.fitting A ⊔ Work.GW2.layer A) := by
      rw [Work.GW2.fstarIn_eq_sup, Work.GW2.fittingIn, Work.GW2.layerIn, ← Subgroup.map_sup]
      exact Subgroup.card_map_of_injective A.subtype_injective
    have hSstar : IsPGroup p ↥(Work.GW2.fstarIn A) := by
      rw [isPGroup_iff_primeFactors_card_subset hp.ne_zero, hcardFE]
      exact (isPGroup_iff_primeFactors_card_subset hp.ne_zero).mp hFE
    -- so `O^p(F*(A)) = ⊥`, contradicting the hypothesis
    exact hne ((pResidualIn_eq_bot_iff_isPGroup _).mpr hSstar)
  have hMnorm : Subgroup.centralizer ((Work.BMAX.pResidualIn p S : Subgroup G) : Set G) ⊓ B ≤
      Subgroup.normalizer (N : Set G) :=
    le_trans inf_le_left (le_trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hNS))
      (Subgroup.centralizer_le_normalizer (N : Set G)))
  exact le_coatom_of_le_normalizer_of_ne_bot hG hA hNbot hNA hAnorm hMnorm

end Work.BMAX
