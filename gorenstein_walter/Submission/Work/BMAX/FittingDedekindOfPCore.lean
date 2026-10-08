/-
# BMAX — `F(A)` is Dedekind as soon as every `O_p(A)` is

**Mathematical content.**  Let `A` be a subgroup of a finite group `G` and suppose that for
every prime `p` the `p`-core `O_p(A)` is a *Dedekind* group, i.e. every subgroup of `O_p(A)` is
normal in `O_p(A)`:

  `h : ∀ p, p.Prime → ∀ Y ≤ O_p(A), O_p(A) ≤ N_G(Y)`.

Then the Fitting subgroup `F(A)` is Dedekind:

  `∀ X ≤ F(A), F(A) ≤ N_G(X)`.

The proof is the standard structure theory of finite nilpotent groups, carried out inside the
group `K := ↥A` and then transported along `A.subtype`:

* `F(K)` is nilpotent, and any `p`-subgroup of `F(K)` lies in a Sylow `p`-subgroup of `F(K)`
  (`IsPGroup.exists_le_sylow`), which is normal by nilpotency; `O_p(F(K))` is characteristic in
  `F(K) ◁ K`, hence a normal `p`-subgroup of `K`.  So every `p`-subgroup of `F(K)` lies in
  `O_p(K)` (`le_opCore_of_le_fitting`);
* consequently, for `X ≤ F(K)`, the join decomposition `X = ⨆_{p prime} (X ⊓ O_p(K))` holds
  (`subgroup_eq_iSup_inf_opCore_of_le_fitting`): `X` is nilpotent (it embeds in `F(K)`), hence
  the join of its own Sylow subgroups, and those are `p`-subgroups of `F(K)`;
* an element `x ∈ O_p(K)` normalizes each `X ⊓ O_q(K)` — for `q = p` by the hypothesis `h`, for
  `q ≠ p` because `x` commutes with every element of `O_q(K)`
  (`commute_opCore_of_ne`, `mem_normalizer_of_forall_commute`);
* `N_K(X)` contains a join of subgroups as soon as it contains each of them, and
  `F(K) = ⨆_{p prime} O_p(K)`, so `F(K) ≤ N_K(X)`.  This is `dedekind_of_opCore_dedekind`.

The two transport steps (the hypothesis into `K`, and the conclusion back into `G`) are short
computations with `Subgroup.mem_normalizer_iff` and `Subgroup.normal_subgroupOf_iff`.
-/
import Mathlib
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.fittingPiIn_le_iSup_pCoreIn

set_option linter.style.haveILetI false
set_option autoImplicit false

open scoped MatrixGroups

namespace Work.BMAX

open Subgroup

/-! ## 0. A normalizer helper -/

/-- If `x` commutes with every element of `Q`, it normalizes every subgroup of `Q`. -/
theorem mem_normalizer_of_forall_commute {G : Type*} [Group G] {x : G} {P Q : Subgroup G}
    (hPQ : P ≤ Q) (hcomm : ∀ y ∈ Q, Commute x y) : x ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hc : x * y = y * x := (hcomm y (hPQ hy)).eq
    have hxy : x * y * x⁻¹ = y := by rw [hc]; group
    rw [hxy]; exact hy
  · intro hy
    have hz : x * y * x⁻¹ ∈ Q := hPQ hy
    have h2 : x⁻¹ * (x * y * x⁻¹) = (x * y * x⁻¹) * x⁻¹ :=
      (hcomm (x * y * x⁻¹) hz).inv_left.eq
    have hxy : y = x * y * x⁻¹ := by
      calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
        _ = (x * y * x⁻¹) * x⁻¹ * x := by rw [h2]
        _ = x * y * x⁻¹ := by group
    rw [hxy]; exact hy

/-! ## 1. `p`-subgroups of the Fitting subgroup -/

section Abstract

variable {K : Type*} [Group K]

/-- Every `p`-subgroup of a finite nilpotent group lies in `O_p`: it lies in some Sylow
`p`-subgroup, which is normal by nilpotency, hence equals `O_p`. -/
theorem le_opCore_of_isPGroup_of_isNilpotent [Finite K] [Group.IsNilpotent K] {p : ℕ}
    [Fact p.Prime] {X : Subgroup K} (hX : IsPGroup p X) :
    X ≤ OddOrder.Isaacs.Ch01.opCore p K := by
  obtain ⟨Q, hXQ⟩ := hX.exists_le_sylow
  haveI : (Q : Subgroup K).Normal := OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent Q
  exact hXQ.trans (le_of_eq (OddOrder.Isaacs.Ch01.Sylow.eq_opCore_of_normal Q ‹_›))

/-- **A `p`-subgroup of the Fitting subgroup of a finite group lies in the `p`-core.**
`F(K)` is nilpotent, so such a subgroup lies in its unique Sylow `p`-subgroup `O_p(F(K))`; the
latter is characteristic in `F(K) ◁ K`, hence a normal `p`-subgroup of `K`. -/
theorem le_opCore_of_le_fitting [Finite K] {p : ℕ} [Fact p.Prime] {Q : Subgroup K}
    (hQ : Q ≤ OddOrder.Isaacs.Ch01.fitting K) (hQp : IsPGroup p Q) :
    Q ≤ OddOrder.Isaacs.Ch01.opCore p K := by
  haveI : (OddOrder.Isaacs.Ch01.fitting K).Normal := OddOrder.Isaacs.Ch01.fitting.normal K
  haveI : Group.IsNilpotent ↥(OddOrder.Isaacs.Ch01.fitting K) :=
    OddOrder.Isaacs.Ch01.fitting.isNilpotent
  have hQ' : IsPGroup p (Q.subgroupOf (OddOrder.Isaacs.Ch01.fitting K)) := by
    rw [← Subgroup.comap_subtype Q (OddOrder.Isaacs.Ch01.fitting K)]
    exact hQp.comap_of_injective _ (OddOrder.Isaacs.Ch01.fitting K).subtype_injective
  have hle : Q.subgroupOf (OddOrder.Isaacs.Ch01.fitting K) ≤
      OddOrder.Isaacs.Ch01.opCore p ↥(OddOrder.Isaacs.Ch01.fitting K) :=
    le_opCore_of_isPGroup_of_isNilpotent hQ'
  haveI hchar :
      (OddOrder.Isaacs.Ch01.opCore p ↥(OddOrder.Isaacs.Ch01.fitting K)).Characteristic :=
    OddOrder.Isaacs.Ch01.opCore.characteristic p _
  calc Q = (Q.subgroupOf (OddOrder.Isaacs.Ch01.fitting K)).map
        (OddOrder.Isaacs.Ch01.fitting K).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hQ).symm
    _ ≤ (OddOrder.Isaacs.Ch01.opCore p ↥(OddOrder.Isaacs.Ch01.fitting K)).map
        (OddOrder.Isaacs.Ch01.fitting K).subtype := Subgroup.map_mono hle
    _ ≤ OddOrder.Isaacs.Ch01.opCore p K :=
        OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore
          ((OddOrder.Isaacs.Ch01.opCore_isPGroup p
            ↥(OddOrder.Isaacs.Ch01.fitting K)).map
              (OddOrder.Isaacs.Ch01.fitting K).subtype)

/-- Distinct `p`-cores commute elementwise: they are normal subgroups of coprime order. -/
theorem commute_opCore_of_ne (p q : Nat.Primes) (hpq : p ≠ q) :
    ∀ x ∈ OddOrder.Isaacs.Ch01.opCore (p : ℕ) K,
      ∀ y ∈ OddOrder.Isaacs.Ch01.opCore (q : ℕ) K, Commute x y := by
  have hpq' : (p : ℕ) ≠ (q : ℕ) := fun h => hpq (Subtype.ext h)
  haveI : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩
  haveI : Fact (Nat.Prime (q : ℕ)) := ⟨q.2⟩
  intro x hx y hy
  exact Subgroup.commute_of_normal_of_disjoint _ _
    (OddOrder.Isaacs.Ch01.opCore.normal _ _) (OddOrder.Isaacs.Ch01.opCore.normal _ _)
    (IsPGroup.disjoint_of_ne (p : ℕ) (q : ℕ) hpq' _ _
      (OddOrder.Isaacs.Ch01.opCore_isPGroup _ _) (OddOrder.Isaacs.Ch01.opCore_isPGroup _ _))
    x y hx hy

/-- **A subgroup of the Fitting subgroup is the join of its intersections with the `p`-cores.**
`X` embeds in the nilpotent group `F(K)`, hence is nilpotent and the join of its own Sylow
subgroups; each of those is a `p`-subgroup of `F(K)`, hence lies in `O_p(K)`. -/
theorem subgroup_eq_iSup_inf_opCore_of_le_fitting [Finite K] {X : Subgroup K}
    (hX : X ≤ OddOrder.Isaacs.Ch01.fitting K) :
    X = ⨆ p : Nat.Primes, X ⊓ OddOrder.Isaacs.Ch01.opCore (p : ℕ) K := by
  haveI : Group.IsNilpotent ↥(OddOrder.Isaacs.Ch01.fitting K) :=
    OddOrder.Isaacs.Ch01.fitting.isNilpotent
  haveI : Group.IsNilpotent ↥X :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hX)
  have htop : (⊤ : Subgroup ↥X).map X.subtype = X := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmap : (⨆ p : (Nat.card ↥X).primeFactors,
        (↑(default : Sylow (p : ℕ) ↥X) : Subgroup ↥X)).map X.subtype = X := by
    rw [OddOrder.Isaacs.Ch01.iSup_default_sylow_eq_top_of_nilpotent ↥X, htop]
  refine le_antisymm ?_ (iSup_le fun p => inf_le_left)
  calc X = (⨆ p : (Nat.card ↥X).primeFactors,
        (↑(default : Sylow (p : ℕ) ↥X) : Subgroup ↥X)).map X.subtype := hmap.symm
    _ = ⨆ p : (Nat.card ↥X).primeFactors,
        (↑(default : Sylow (p : ℕ) ↥X) : Subgroup ↥X).map X.subtype :=
        Subgroup.map_iSup _ _
    _ ≤ ⨆ q : (Nat.card ↥X).primeFactors,
        X ⊓ OddOrder.Isaacs.Ch01.opCore (q : ℕ) K := by
        refine iSup_le fun p => ?_
        haveI : Fact (Nat.Prime (p : ℕ)) := ⟨Nat.prime_of_mem_primeFactors p.2⟩
        have hmap_le : Subgroup.map X.subtype (↑(default : Sylow (p : ℕ) ↥X)) ≤ X :=
          Subgroup.map_subtype_le _
        have hmap_core : Subgroup.map X.subtype (↑(default : Sylow (p : ℕ) ↥X)) ≤
            OddOrder.Isaacs.Ch01.opCore (p : ℕ) K :=
          le_opCore_of_le_fitting (hmap_le.trans hX)
            (IsPGroup.map (default : Sylow (p : ℕ) ↥X).isPGroup' X.subtype)
        exact (le_inf hmap_le hmap_core).trans (le_iSup
          (fun q : (Nat.card ↥X).primeFactors =>
            X ⊓ OddOrder.Isaacs.Ch01.opCore (q : ℕ) K) p)
    _ ≤ ⨆ q : Nat.Primes, X ⊓ OddOrder.Isaacs.Ch01.opCore (q : ℕ) K :=
        iSup_le fun p => le_iSup
          (fun q : Nat.Primes => X ⊓ OddOrder.Isaacs.Ch01.opCore (q : ℕ) K)
          ⟨(p : ℕ), Nat.prime_of_mem_primeFactors p.2⟩

/-- **If every `p`-core of a finite group is Dedekind, then so is the Fitting subgroup.** -/
theorem dedekind_of_opCore_dedekind [Finite K]
    (h : ∀ p : ℕ, p.Prime → ∀ Y : Subgroup K, Y ≤ OddOrder.Isaacs.Ch01.opCore p K →
      OddOrder.Isaacs.Ch01.opCore p K ≤ Subgroup.normalizer (Y : Set K)) :
    ∀ X : Subgroup K, X ≤ OddOrder.Isaacs.Ch01.fitting K →
      OddOrder.Isaacs.Ch01.fitting K ≤ Subgroup.normalizer (X : Set K) := by
  intro X hX
  have hdec : X = ⨆ p : Nat.Primes, X ⊓ OddOrder.Isaacs.Ch01.opCore (p : ℕ) K :=
    subgroup_eq_iSup_inf_opCore_of_le_fitting hX
  have key : ∀ p : Nat.Primes,
      OddOrder.Isaacs.Ch01.opCore (p : ℕ) K ≤ Subgroup.normalizer (X : Set K) := by
    intro p x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hXq : ∀ q : Nat.Primes, x ∈ Subgroup.normalizer
        (((X ⊓ OddOrder.Isaacs.Ch01.opCore (q : ℕ) K) : Subgroup K) : Set K) := by
      intro q
      by_cases hqp : q = p
      · subst hqp
        exact h (q : ℕ) q.2 (X ⊓ OddOrder.Isaacs.Ch01.opCore (q : ℕ) K) inf_le_right hx
      · exact mem_normalizer_of_forall_commute inf_le_right
          (fun y hy => commute_opCore_of_ne p q (Ne.symm hqp) x hx y hy)
    have hstep : Subgroup.map (↑(MulAut.conj x) : K →* K) X
        = ⨆ q : Nat.Primes, Subgroup.map (↑(MulAut.conj x) : K →* K)
            (X ⊓ OddOrder.Isaacs.Ch01.opCore (q : ℕ) K) := by
      conv_lhs => rw [hdec]
      rw [Subgroup.map_iSup (↑(MulAut.conj x) : K →* K)]
    rw [hstep, iSup_congr fun q => Subgroup.mem_normalizer_iff_map_conj_eq.mp (hXq q)]
    exact hdec.symm
  rw [show OddOrder.Isaacs.Ch01.fitting K
      = ⨆ p : Nat.Primes, OddOrder.Isaacs.Ch01.opCore (p : ℕ) K from rfl]
  exact iSup_le key

end Abstract

/-! ## 2. The `…In` version -/

section InAux

variable {G : Type*} [Group G]

/-- `F(A) ⊆ A`, as subgroups of the ambient group. -/
theorem fittingIn_le_self (A : Subgroup G) : Work.GW2.fittingIn A ≤ A :=
  Subgroup.map_subtype_le _

end InAux

section Main

variable {G : Type} [Group G] [Finite G]

/-- `Work.GW2.pCoreIn p A = (O_p(↥A)).map A.subtype`. -/
theorem pCoreIn_eq_opCore (p : ℕ) [Fact p.Prime] (A : Subgroup G) :
    Work.GW2.pCoreIn p A = (OddOrder.Isaacs.Ch01.opCore p ↥A).map A.subtype := by
  rw [Work.GW2.pCoreIn, PiPart.pCore_eq_opCore]

/-- `Work.GW2.fittingIn A = (F(↥A)).map A.subtype`. -/
theorem fittingIn_eq_fitting (A : Subgroup G) :
    Work.GW2.fittingIn A = (OddOrder.Isaacs.Ch01.fitting ↥A).map A.subtype := by
  rw [Work.GW2.fittingIn, PiPart.fitting_eq_isaacsFitting]

end Main

section Deliverable

theorem FittingDedekindOfPCore {G : Type} [Group G] [Finite G] (A : Subgroup G)
    (h : ∀ p : ℕ, p.Prime → ∀ Y : Subgroup G, Y ≤ Work.GW2.pCoreIn p A →
      Work.GW2.pCoreIn p A ≤ Subgroup.normalizer (Y : Set G)) :
    ∀ X : Subgroup G, X ≤ Work.GW2.fittingIn A →
      Work.GW2.fittingIn A ≤ Subgroup.normalizer (X : Set G) := by
  -- The hypothesis, transported to the group `↥A`.
  have hK : ∀ p : ℕ, p.Prime → ∀ Y : Subgroup ↥A, Y ≤ OddOrder.Isaacs.Ch01.opCore p ↥A →
      OddOrder.Isaacs.Ch01.opCore p ↥A ≤ Subgroup.normalizer (Y : Set ↥A) := by
    intro p hp Y hY
    haveI : Fact p.Prime := ⟨hp⟩
    have hYmap : Y.map A.subtype ≤ Work.GW2.pCoreIn p A := by
      rw [pCoreIn_eq_opCore p A]
      exact Subgroup.map_mono hY
    have hxN : ∀ x ∈ OddOrder.Isaacs.Ch01.opCore p ↥A, A.subtype x ∈
        Subgroup.normalizer ((Y.map A.subtype : Subgroup G) : Set G) := by
      intro x hx
      refine h p hp (Y.map A.subtype) hYmap ?_
      rw [pCoreIn_eq_opCore p A]
      exact Subgroup.mem_map_of_mem _ hx
    intro x hx
    have hxNy := hxN x hx
    rw [Subgroup.mem_normalizer_iff] at hxNy
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hyG : A.subtype y ∈ Y.map A.subtype := Subgroup.mem_map_of_mem _ hy
      have hmem : A.subtype (x * y * x⁻¹) ∈ Y.map A.subtype := by
        have := (hxNy (A.subtype y)).mp hyG
        simpa using this
      obtain ⟨y', hy', hy'e⟩ := hmem
      have : y' = x * y * x⁻¹ := A.subtype_injective hy'e
      rwa [← this]
    · intro hy
      have hmem : A.subtype x * A.subtype y * (A.subtype x)⁻¹ ∈ Y.map A.subtype := by
        have := Subgroup.mem_map_of_mem A.subtype hy
        simpa using this
      have hmem' : A.subtype y ∈ Y.map A.subtype := (hxNy (A.subtype y)).mpr hmem
      obtain ⟨y', hy', hy'e⟩ := hmem'
      have : y' = y := A.subtype_injective hy'e
      rwa [← this]
  intro X hX
  -- `X`, pulled back to `↥A`, lies in `F(↥A)`.
  have hX' : X.subgroupOf A ≤ OddOrder.Isaacs.Ch01.fitting ↥A := by
    intro x hx
    have hxX : A.subtype x ∈ X := hx
    have hle : A.subtype x ∈ Work.GW2.fittingIn A := hX hxX
    rw [fittingIn_eq_fitting A] at hle
    obtain ⟨y, hy, hye⟩ := hle
    have : y = x := A.subtype_injective hye
    rwa [this] at hy
  have hnorm := dedekind_of_opCore_dedekind (K := ↥A) hK (X.subgroupOf A) hX'
  -- Push the normality of `X.subgroupOf A` in `F(↥A)` back to `G`.
  have hN' : ((X.subgroupOf A).subgroupOf (OddOrder.Isaacs.Ch01.fitting ↥A)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX').mpr hnorm
  have hfin : (X.subgroupOf (Work.GW2.fittingIn A)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hX]
    intro a b ha hb
    have haA : a ∈ A := fittingIn_le_self A (hX ha)
    have hbA : b ∈ A := fittingIn_le_self A hb
    have ha' : (⟨a, haA⟩ : ↥A) ∈ X.subgroupOf A := ha
    have hb' : (⟨b, hbA⟩ : ↥A) ∈ OddOrder.Isaacs.Ch01.fitting ↥A := by
      have hbb : A.subtype (⟨b, hbA⟩ : ↥A) ∈ Work.GW2.fittingIn A := hb
      rw [fittingIn_eq_fitting A] at hbb
      obtain ⟨b₁, hb₁, hb₁e⟩ := hbb
      have : b₁ = (⟨b, hbA⟩ : ↥A) := A.subtype_injective hb₁e
      rwa [this] at hb₁
    have hm : (⟨b, hbA⟩ : ↥A) * (⟨a, haA⟩ : ↥A) * (⟨b, hbA⟩ : ↥A)⁻¹ ∈ X.subgroupOf A :=
      (Subgroup.normal_subgroupOf_iff hX').mp hN'
        (⟨a, haA⟩ : ↥A) (⟨b, hbA⟩ : ↥A) ha' hb'
    have hmem : A.subtype ((⟨b, hbA⟩ : ↥A) * (⟨a, haA⟩ : ↥A) * (⟨b, hbA⟩ : ↥A)⁻¹) ∈ X := hm
    have heq : A.subtype ((⟨b, hbA⟩ : ↥A) * (⟨a, haA⟩ : ↥A) * (⟨b, hbA⟩ : ↥A)⁻¹)
        = b * a * b⁻¹ := by simp
    rwa [heq] at hmem
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hX).mp hfin

end Deliverable

end Work.BMAX
