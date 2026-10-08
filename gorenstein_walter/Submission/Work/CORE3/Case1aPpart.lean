import Mathlib
import Submission.Work.CORE3.Case1aFrattiniApi
import Submission.Work.CORE3.Case1aSetup
import Submission.Work.CORE3.Case1aFrattiniSAct
import Submission.Work.CORE3.LePCoreInOfNormal
import Submission.Work.CORE3.pCoreIn_of_pow_eq_one_of_mem_fittingIn
import Submission.Work.CORE2A.exists_mul_of_mem_sup_of_normal

/-!
# CORE3: the `p`-part of `C_U(t₁)` (Bender 1981, §3, p. 222)

Deliverable: `Work.CORE3.PpartProp B D`, i.e. the identity

`|C_U(t₁)|_p = |O_p(U)| · |C_U(S)|_p`.

Mathematically (Bender, *Finite groups with dihedral Sylow 2-subgroups*, J. Algebra **70** (1981),
§3, p. 222): under Case (1) of Theorem 2.10 the group `S` acts trivially on `U/F(U)`, so that
`B₀ := C_U(S)` satisfies `U = F(U)·B₀`; and `t₁` centralizes `O_p(U)`.  Writing
`C := C_{F(U)}(t₁)` one has `C_U(t₁) = C·B₀`, with `B₀` normalizing `C`, hence

`|C_U(t₁)| · |C ∧ B₀| = |C| · |B₀|`.

Now `C ∧ B₀ = C_{F(U)}(S)`, whose order is prime to `p` because every `p`-element of the nilpotent
group `F(U)` lies in its Sylow `p`-subgroup `O_p(U)`, while `t₂` inverts `O_p(U)` and centralizes
`C_U(S)`.  Moreover `|C|_p = |O_p(U)|` because `O_p(U)` is the Sylow `p`-subgroup of `F(U)`.
Both facts are instances of the elementary nilpotent-group lemmas proved at the top of this file.

## Contents

* `not_dvd_index_opCore` — in a finite nilpotent group, `p ∤ [N : O_p(N)]`;
* `subgroupOf_map_subtype_eq` — `(H.map K.subtype).subgroupOf K = H` for `H ≤ ↥K`;
* `not_dvd_relIndex_pCoreIn_self` — `p ∤ [K : O_p(K)]` for `K` nilpotent (in the ambient group);
* `not_dvd_relIndex_opCore_fitting` — `p ∤ [F(N) : O_p(N)]` for any finite group `N`;
* `not_dvd_relIndex_pCoreIn_fittingIn` — the same for a subgroup `K ≤ G` in the ambient group;
* `card_sup_mul_card_inf_of_le_normalizer` — `|A ⊔ B| · |A ⊓ B| = |A| · |B|` when `B ≤ N_G(A)`;
* `Case1aPpart` — the deliverable.
-/

set_option linter.style.haveILetI false
set_option linter.dupNamespace false

namespace Work.CORE3

open Work.GW2
open Subgroup
open scoped commutatorElement

/-! ## Elementary lemmas on nilpotent groups and core indices -/

/-- In a finite nilpotent group the `p`-core is a Sylow `p`-subgroup, so its index is prime
to `p`. -/
theorem not_dvd_index_opCore {N : Type} [Group N] [Finite N] [Group.IsNilpotent N]
    (q : ℕ) [Fact q.Prime] :
    ¬ q ∣ (OddOrder.Isaacs.Ch01.opCore q N).index := by
  obtain ⟨P⟩ := Sylow.nonempty (p := q) (G := N)
  have hPn : (P : Subgroup N).Normal := OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent P
  have hPeq : (P : Subgroup N) = OddOrder.Isaacs.Ch01.opCore q N :=
    OddOrder.Isaacs.Ch01.Sylow.eq_opCore_of_normal P hPn
  have hcard : Nat.card ↥(OddOrder.Isaacs.Ch01.opCore q N) =
      q ^ (Nat.card N).factorization q := by
    rw [← hPeq]
    exact Sylow.card_eq_multiplicity P
  intro hdvd
  have hN0 : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have hmul : Nat.card ↥(OddOrder.Isaacs.Ch01.opCore q N)
      * (OddOrder.Isaacs.Ch01.opCore q N).index = Nat.card N := Subgroup.card_mul_index _
  have hkey : q ^ ((Nat.card N).factorization q + 1) ∣ Nat.card N := by
    calc q ^ ((Nat.card N).factorization q + 1)
        = Nat.card ↥(OddOrder.Isaacs.Ch01.opCore q N) * q := by rw [hcard, pow_succ]
      _ ∣ Nat.card ↥(OddOrder.Isaacs.Ch01.opCore q N)
            * (OddOrder.Isaacs.Ch01.opCore q N).index := mul_dvd_mul_left _ hdvd
      _ = Nat.card N := hmul
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization (Fact.out : q.Prime) hN0).mp hkey
  omega

/-- Inside `K`, the preimage of the image of a subgroup `H ≤ ↥K` is `H` itself. -/
theorem subgroupOf_map_subtype_eq {G : Type} [Group G] (K : Subgroup G) (H : Subgroup ↥K) :
    (H.map K.subtype).subgroupOf K = H := by
  rw [← Subgroup.comap_subtype (H.map K.subtype) K]
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    rwa [← hyx']
  · exact fun hx => ⟨x, hx, rfl⟩

/-- `p ∤ [K : O_p(K)]` when the subgroup `K` is nilpotent. -/
theorem not_dvd_relIndex_pCoreIn_self {G : Type} [Group G] [Finite G]
    (K : Subgroup G) [Group.IsNilpotent ↥K] (p : ℕ) [Fact p.Prime] :
    ¬ p ∣ (pCoreIn p K).relIndex K := by
  have hsub : (pCoreIn p K).subgroupOf K = OddOrder.Isaacs.Ch01.opCore p ↥K := by
    rw [Work.GW2.pCoreIn, Work.CORE2A.pCore_eq_opCore]
    exact subgroupOf_map_subtype_eq K (OddOrder.Isaacs.Ch01.opCore p ↥K)
  show ¬ p ∣ ((pCoreIn p K).subgroupOf K).index
  rw [hsub]
  exact not_dvd_index_opCore (N := ↥K) p

/-- In any finite group `N`, the `p`-core has `p`-prime index in the Fitting subgroup:
`O_p(N)` is the Sylow `p`-subgroup of `F(N)`. -/
theorem not_dvd_relIndex_opCore_fitting {N : Type} [Group N] [Finite N]
    (p : ℕ) [Fact p.Prime] :
    ¬ p ∣ (OddOrder.Isaacs.Ch01.opCore p N).relIndex (Work.GW2.fitting N) := by
  set X : Subgroup N := Work.GW2.fitting N with hX
  haveI hXnormal : X.Normal := by
    rw [hX, Work.CORE2A.fitting_eq_isaacsFitting (G := N)]
    exact OddOrder.Isaacs.Ch01.fitting.normal N
  have hle1 : OddOrder.Isaacs.Ch01.opCore p N ≤ pCoreIn p X := by
    refine LePCoreInOfNormal ?_ ?_ ?_
    · rw [hX, Work.CORE2A.fitting_eq_isaacsFitting (G := N)]
      exact OddOrder.Isaacs.Ch01.opCore_le_fitting ⟨p, (Fact.out : p.Prime)⟩ N
    · intro x _
      rw [Subgroup.normalizer_eq_top (OddOrder.Isaacs.Ch01.opCore p N)]
      trivial
    · exact OddOrder.Isaacs.Ch01.opCore_isPGroup p N
  have hle2 : pCoreIn p X ≤ OddOrder.Isaacs.Ch01.opCore p N := by
    have hNX : ∀ g : N, g ∈ Subgroup.normalizer (X : Set N) :=
      fun _ => (Subgroup.normalizer_eq_top X).symm ▸ trivial
    haveI hYnormal : (pCoreIn p X).Normal :=
      Subgroup.Normal.mk fun x hx g =>
        (Subgroup.mem_normalizer_iff.mp
          (Work.CORE3.c1aLe_normalizer_pCoreIn p X (hNX g)) x).mp hx
    exact OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore (c1aIsPGroup_pCoreIn p X)
  have hXY : OddOrder.Isaacs.Ch01.opCore p N = pCoreIn p X := le_antisymm hle1 hle2
  haveI hXnil : Group.IsNilpotent ↥X := by
    rw [hX, Work.CORE2A.fitting_eq_isaacsFitting (G := N)]
    exact OddOrder.Isaacs.Ch01.fitting.isNilpotent
  rw [hXY]
  exact not_dvd_relIndex_pCoreIn_self X p

/-- In the ambient group, the `p`-core has `p`-prime index in the Fitting subgroup. -/
theorem not_dvd_relIndex_pCoreIn_fittingIn {G : Type} [Group G] [Finite G]
    (K : Subgroup G) (p : ℕ) [Fact p.Prime] :
    ¬ p ∣ (Work.GW2.pCoreIn p K).relIndex (Work.GW2.fittingIn K) := by
  have hFleK : fittingIn K ≤ K := c1aFittingIn_le K
  have hrel : (pCoreIn p K).relIndex (fittingIn K)
      = ((pCoreIn p K).subgroupOf K).relIndex ((fittingIn K).subgroupOf K) :=
    (Subgroup.relIndex_subgroupOf (H := pCoreIn p K) (K := fittingIn K) (L := K) hFleK).symm
  rw [hrel]
  have hP' : (pCoreIn p K).subgroupOf K = OddOrder.Isaacs.Ch01.opCore p ↥K := by
    rw [Work.GW2.pCoreIn, Work.CORE2A.pCore_eq_opCore]
    exact subgroupOf_map_subtype_eq K (OddOrder.Isaacs.Ch01.opCore p ↥K)
  have hF' : (fittingIn K).subgroupOf K = Work.GW2.fitting ↥K := by
    rw [Work.GW2.fittingIn]
    exact subgroupOf_map_subtype_eq K (Work.GW2.fitting ↥K)
  rw [hP', hF']
  exact not_dvd_relIndex_opCore_fitting (N := ↥K) p

/-- `|A ⊔ B| · |A ⊓ B| = |A| · |B|` for subgroups `A`, `B` with `B ≤ N_G(A)`: the cardinality
shadow of the second isomorphism theorem. -/
theorem card_sup_mul_card_inf_of_le_normalizer {G : Type} [Group G] [Finite G]
    {A B : Subgroup G} (h : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hAB : (A ⊓ B).subgroupOf B = A.subgroupOf B := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  have h1 : (A.subgroupOf B).index * Nat.card ↥(A ⊓ B) = Nat.card ↥B := by
    have hc : Nat.card ↥(A.subgroupOf B) = Nat.card ↥(A ⊓ B) := by
      rw [← hAB]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ B ≤ B)).toEquiv
    rw [← hc]
    exact Subgroup.index_mul_card (A.subgroupOf B)
  have h2 : (A.subgroupOf (A ⊔ B)).index * Nat.card ↥A = Nat.card ↥(A ⊔ B) := by
    have hc : Nat.card ↥(A.subgroupOf (A ⊔ B)) = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ B)).toEquiv
    rw [← hc]
    exact Subgroup.index_mul_card (A.subgroupOf (A ⊔ B))
  have hidx : (A.subgroupOf B).index = (A.subgroupOf (A ⊔ B)).index := by
    haveI := Subgroup.normal_subgroupOf_of_le_normalizer h
    haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
    have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient B A h
    rw [Subgroup.index_eq_card (A.subgroupOf B),
      Subgroup.index_eq_card (A.subgroupOf (A ⊔ B)), sup_comm]
    exact Nat.card_congr e.toEquiv
  calc Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B)
      = ((A.subgroupOf (A ⊔ B)).index * Nat.card ↥A) * Nat.card ↥(A ⊓ B) := by rw [h2]
    _ = ((A.subgroupOf B).index * Nat.card ↥A) * Nat.card ↥(A ⊓ B) := by rw [hidx]
    _ = Nat.card ↥A * ((A.subgroupOf B).index * Nat.card ↥(A ⊓ B)) := by ring
    _ = Nat.card ↥A * Nat.card ↥B := by rw [h1]

/-! ## The deliverable -/

theorem Case1aPpart (G : Type) [Group G] [Finite G] (hFT : Work.GW2.FeitThompsonProp) (T : Work.GW2.LocalToolkit) (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case1aData B) (hSAct : Work.CORE3.SActsTriviallyModFitting B) : Work.CORE3.PpartProp B D := by
  classical
  haveI hpFact : Fact D.p.Prime := ⟨D.hp⟩
  haveI htwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- ## Notation
  set S : Subgroup G := (B.S : Subgroup G) with hS
  set U : Subgroup G := B.U with hU
  set F : Subgroup G := fittingIn U with hF
  set P : Subgroup G := pCoreIn D.p U with hP
  set B0 : Subgroup G := U ⊓ centralizer (S : Set G) with hB0
  set C : Subgroup G := F ⊓ centralizer ({D.t1} : Set G) with hC
  set A : Subgroup G := U ⊓ centralizer ({D.t1} : Set G) with hA
  -- ## Basic facts
  have hF_le_U : F ≤ U := c1aFittingIn_le U
  have hP_le_F : P ≤ F := c1aPcoreIn_le_fittingIn D.p U
  have hB0_le_U : B0 ≤ U := inf_le_left
  have hPU : P = pCoreIn D.p B.U := by rw [hP, hU]
  have hFU : F = fittingIn B.U := by rw [hF, hU]
  have hB0U : B0 = B.U ⊓ centralizer ((B.S : Subgroup G) : Set G) := by rw [hB0, hU, hS]
  have hAU : A = B.U ⊓ centralizer ({D.t1} : Set G) := by rw [hA, hU]
  -- `C(S) ≤ C(t₁)` since `t₁ ∈ S`
  have hCS_le_Ct1 : centralizer (S : Set G) ≤ centralizer ({D.t1} : Set G) :=
    Subgroup.centralizer_le (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact D.t1_mem)
  -- `F ◁ U`
  have hU_le_NF : U ≤ Subgroup.normalizer (F : Set G) := by
    haveI hchar : (Work.GW2.fitting ↥U).Characteristic := c1aFitting_characteristic U
    have hN : (Work.GW2.fitting ↥U).Normal := by
      rw [Work.CORE2A.fitting_eq_isaacsFitting (G := ↥U)]
      exact OddOrder.Isaacs.Ch01.fitting.normal ↥U
    have h := c1aLe_normalizer_map_subtype (K := U) (N := Work.GW2.fitting ↥U) hN
    rw [hF]
    simpa [Work.GW2.fittingIn] using h
  have hF_norm : (F.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hF_le_U).mpr hU_le_NF
  -- ## Step 1: `[S,U] ≤ F(U)`
  have hcommS : (⁅S, U⁆ : Subgroup G) ≤ F := by
    rw [Subgroup.commutator_le]
    intro s hs u hu
    have hz : u⁻¹ * (s * u * s⁻¹) ∈ F := hSAct s hs u hu
    have heq : ⁅s, u⁆ = u * (u⁻¹ * (s * u * s⁻¹)) * u⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.mp (hU_le_NF hu)
      (u⁻¹ * (s * u * s⁻¹))).mp hz
  -- ## Step 2: the coprime-action decomposition `U = [S,U] · C_U(S)`
  have hU_decomp : U = (⁅S, U⁆ : Subgroup G) ⊔ B0 := by
    have hSp : IsPGroup 2 S := B.S.isPGroup'
    have hcp : Nat.Coprime 2 (Nat.card U) := Odd.coprime_two_left (Work.CORE2A.bSetup_U_odd B)
    have hnorm : S ≤ Subgroup.normalizer (U : Set G) :=
      fun x hx => Work.CORE2A.bender_s_mem_normalizer_U B hx
    exact ((T.c11i G 2 S U hSp hcp hnorm).2).symm
  have hF_sup_B0 : F ⊔ B0 = U := by
    refine le_antisymm ?_ ?_
    · exact sup_le (c1aFittingIn_le U) inf_le_left
    · rw [hU_decomp]
      exact sup_le_sup_right hcommS B0
  -- elementwise decomposition of `U` with respect to `(F, B0)`
  have hdecomp : ∀ x ∈ U, ∃ f ∈ F, ∃ b ∈ B0, f * b = x :=
    Work.CORE2A.exists_mul_of_mem_sup_of_normal hF_le_U inf_le_left hF_norm hF_sup_B0
  -- ## Step 3: `C_U(t₁) = C · B₀`
  have hA_eq : A = C ⊔ B0 := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨f, hf, b, hb, hfb⟩ := hdecomp x hx.1
      have hb1 : D.t1 * b = b * D.t1 := (Subgroup.mem_centralizer_iff.mp hb.2) D.t1 D.t1_mem
      have hx1 : D.t1 * x = x * D.t1 :=
        (Subgroup.mem_centralizer_iff.mp hx.2) D.t1 (by simp)
      have hf1 : D.t1 * f = f * D.t1 := by
        have h0 : D.t1 * (f * b) = (f * b) * D.t1 := by rw [hfb]; exact hx1
        have h2 : D.t1 * f * b = f * D.t1 * b := by
          calc D.t1 * f * b = D.t1 * (f * b) := by group
            _ = (f * b) * D.t1 := h0
            _ = f * (b * D.t1) := by group
            _ = f * (D.t1 * b) := by rw [← hb1]
            _ = f * D.t1 * b := by group
        exact mul_right_cancel h2
      have hfC : f ∈ C := ⟨hf, by
        change f ∈ Subgroup.centralizer ({D.t1} : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hf1⟩
      rw [← hfb]
      exact Subgroup.mul_mem_sup hfC hb
    · refine sup_le ?_ ?_
      · intro x hx
        exact ⟨hF_le_U hx.1, hx.2⟩
      · refine le_inf inf_le_left ?_
        intro x hx
        exact hCS_le_Ct1 hx.2
  -- ## Step 4: `B₀` normalizes `C`, hence the cardinality identity
  have hB0_le_NC : B0 ≤ Subgroup.normalizer (C : Set G) := by
    have key : ∀ {T : Set G} {g x : G}, g ∈ Subgroup.centralizer T →
        x ∈ Subgroup.centralizer T → g * x * g⁻¹ ∈ Subgroup.centralizer T := by
      intro T g x hg hx
      rw [Subgroup.mem_centralizer_iff] at hg hx ⊢
      intro y hy
      have hyg : y * g = g * y := hg y hy
      have hyx : y * x = x * y := hx y hy
      have hygi : y * g⁻¹ = g⁻¹ * y := by
        have h := congrArg (fun z => g⁻¹ * z * g⁻¹) hyg
        simpa [mul_assoc] using h.symm
      calc y * (g * x * g⁻¹) = (y * g) * x * g⁻¹ := by group
        _ = (g * y) * x * g⁻¹ := by rw [hyg]
        _ = g * (y * x) * g⁻¹ := by group
        _ = g * (x * y) * g⁻¹ := by rw [hyx]
        _ = g * x * (y * g⁻¹) := by group
        _ = g * x * (g⁻¹ * y) := by rw [hygi]
        _ = (g * x * g⁻¹) * y := by group
    rw [hC, Subgroup.le_normalizer_iff]
    intro b hb f hf
    refine ⟨?_, ?_⟩
    · exact Subgroup.le_normalizer_iff.mp hU_le_NF b hb.1 f hf.1
    · exact key (hCS_le_Ct1 hb.2) hf.2
  have hcard : Nat.card ↥A * Nat.card ↥(C ⊓ B0) = Nat.card ↥C * Nat.card ↥B0 := by
    have h := card_sup_mul_card_inf_of_le_normalizer (A := C) (B := B0) hB0_le_NC
    rwa [← hA_eq] at h
  -- ## Step 5: the two `p`-part computations
  -- (a) `|C|_p = |P|_p`
  have hPC : P ≤ C := fun x hx => ⟨hP_le_F hx, D.cent hx⟩
  have hC_fac : (Nat.card ↥C).factorization D.p = (Nat.card ↥P).factorization D.p := by
    have hnotdvd : ¬ D.p ∣ P.relIndex C := by
      have h1 : ¬ D.p ∣ P.relIndex F := by
        have h2 := not_dvd_relIndex_pCoreIn_fittingIn U D.p
        simpa [P, F] using h2
      intro hdvd
      rw [← Subgroup.relIndex_mul_relIndex P C F hPC inf_le_left] at h1
      exact h1 (dvd_mul_of_dvd_left hdvd _)
    have hrel : P.relIndex C * Nat.card ↥(P ⊓ C) = Nat.card ↥C :=
      Subgroup.relIndex_mul_card P C
    rw [inf_eq_left.mpr hPC] at hrel
    have hne1 : P.relIndex C ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hrel
      have hCne : Nat.card ↥C ≠ 0 := by
        haveI : Nonempty ↥C := ⟨⟨1, C.one_mem⟩⟩
        exact Nat.card_pos.ne'
      exact hCne hrel.symm
    have hne2 : Nat.card ↥P ≠ 0 := by
      haveI : Nonempty ↥P := ⟨⟨1, P.one_mem⟩⟩
      exact Nat.card_pos.ne'
    rw [← hrel, Nat.factorization_mul hne1 hne2]
    simp only [Finsupp.add_apply]
    rw [Nat.factorization_eq_zero_of_not_dvd hnotdvd, zero_add]
  -- (b) `|C ⊓ B₀|` is prime to `p`
  have hoddP : Odd (Nat.card ↥P) := by
    have hp_odd : Odd D.p := by
      have h2 : D.p ∣ Nat.card ↥(fittingIn B.U) := (Nat.mem_primeFactors.mp D.p_mem).2.1
      have h3 : D.p ∣ Nat.card ↥B.U :=
        dvd_trans h2 (Subgroup.card_dvd_of_le (c1aFittingIn_le B.U))
      exact Odd.of_dvd_nat (Work.CORE2A.bSetup_U_odd B) h3
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (c1aIsPGroup_pCoreIn D.p B.U)
    have hcardP : Nat.card ↥P = D.p ^ k := hk
    rw [hcardP]
    exact hp_odd.pow
  have hCB0_fac : (Nat.card ↥(C ⊓ B0)).factorization D.p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(C ⊓ B0)) D.p hdvd
    have hxmem : (x : G) ∈ C ⊓ B0 := x.2
    have hxF : (x : G) ∈ fittingIn B.U := hxmem.1.1
    have hxp : (x : G) ^ D.p = 1 := by
      have h1 : x ^ orderOf x = 1 := pow_orderOf_eq_one x
      rw [hxord] at h1
      simpa using congrArg (fun z : ↥(C ⊓ B0) => (z : G)) h1
    have hxP : (x : G) ∈ P := pCoreIn_of_pow_eq_one_of_mem_fittingIn B.U D.p hxF hxp
    have hxcen : (x : G) ∈ centralizer ({D.t2} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Subgroup.mem_centralizer_iff.mp hxmem.2.2) D.t2 D.t2_mem
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
      have hbot : P ⊓ centralizer ({D.t2} : Set G) = ⊥ :=
        Work.CORE2A.inverts_inf_centralizer_eq_bot_of_odd D.inv hoddP
      rw [← hbot]
      exact ⟨hxP, hxcen⟩
    have hx1 : (x : G) = 1 := Subgroup.mem_bot.mp hxbot
    have hx1' : x = 1 := Subtype.ext (by simpa using hx1)
    rw [hx1', orderOf_one] at hxord
    exact absurd hxord (Fact.out : D.p.Prime).one_lt.ne
  -- ## Step 6: assemble
  have hpos : ∀ H : Subgroup G, Nat.card ↥H ≠ 0 := fun H => by
    haveI : Nonempty ↥H := ⟨⟨1, H.one_mem⟩⟩
    exact Nat.card_pos.ne'
  have hmain : (Nat.card ↥A).factorization D.p
      = (Nat.card ↥P).factorization D.p + (Nat.card ↥B0).factorization D.p := by
    have h1 := congrArg (fun n : ℕ => n.factorization D.p) hcard
    rw [Nat.factorization_mul (hpos A) (hpos (C ⊓ B0)),
      Nat.factorization_mul (hpos C) (hpos B0)] at h1
    simp only [Finsupp.add_apply] at h1
    rw [hCB0_fac, hC_fac] at h1
    simpa using h1
  show (Nat.card ↥A).factorization D.p
      = (Nat.card ↥P).factorization D.p + (Nat.card ↥B0).factorization D.p
  exact hmain

end Work.CORE3
