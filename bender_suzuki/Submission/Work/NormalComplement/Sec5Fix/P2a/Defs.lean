/-
# `Work.NormalComplement.Sec5Fix.P2a.Defs`

Shared vocabulary for the proof of Peterfalvi I Ch. III §5 Prop. 2 (a)
(`orderOf (u * t) ∈ {3, 5}`) along the route of the source: `F = O^{2'}(C_G(V))` acts on
`Ω_V = fixedPts H V` (with `V = centD H t`), `F ⊓ H` is strongly embedded in `F`, and its Sylow
`2`-subgroup `S` (normal in `F ⊓ H`) has a unique involution and exponent `4`; Appendix III is then
applied to `𝒩 = N_G(V)`, divided by the kernel `KKg` of its action on `Ω_V`.

The file provides

* `P2aSdata H t S` — the list of properties of the Sylow `2`-subgroup `S` that the argument uses,
  and `p2aSdata_exists`, producing such an `S` from the §5 configuration;
* `KKg H t` — the kernel of the action of `𝒩 = N_G(V)` on `Ω_V`, as a subgroup of the ambient
  group, with its basic API;
* `Nq H t = ↥(𝒩) ⧸ KK H t` — the group to which `AppIIIProp` is applied, with its action on `Ω_V`.
-/
import Mathlib
import Submission.Work.NormalComplement.Sec5Fix.Defs
import Submission.Work.NormalComplement.Sec5Fix.p3F_anti
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.sec5f_setup
import Submission.Work.NormalComplement.p2a_invol_unique
import Submission.Work.NormalComplement.p2a_pow_four
import Submission.Work.NormalComplement.p2a_appIII_cyclic
import Submission.Work.ThreePoints.P3Sub.p3pkg_of_subnormal
import Submission.Work.ThreePoints.chIIFourP3Subnormal
import Submission.Work.ThreePoints.P3NeBot.maximal_of_twoTransitive
import Submission.Work.BrauerSuzuki.Main
import Submission.Work.ThmF.ChV12.glaubermanZJ_free
import Submission.Work.DoubleTransitivity.Sec7.ThmA
import Submission.Work.Models.models

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical
open Submission.Blueprint
open LeanEval.GroupTheory.Defs

namespace Work.NormalComplement.Sec5Fix
namespace P2a

variable {G : Type} [Group G] [Finite G]

/-! ## Elementary prerequisites -/

/-- An element of `2`-power order lies in `O^{2'}`. -/
theorem mem_oddResidual_of_pow_two_eq_one {L : Type} [Group L] [Finite L] {x : L} {k : ℕ}
    (hx : x ^ 2 ^ k = 1) : x ∈ Submission.Blueprint.oddResidual L := by
  induction k generalizing x with
  | zero =>
      rw [pow_zero, pow_one] at hx
      rw [hx]
      exact Subgroup.one_mem _
  | succ k ih =>
      have h2 : (x * x) ^ 2 ^ k = 1 := by
        rw [← pow_two, ← pow_mul, ← pow_succ', hx]
      exact Work.Reductions.mem_oddResidual_of_mul_self_mem (ih h2)

/-- An element of `C` of `2`-power order lies in `O^{2'}(C)` (as a subgroup of `G`). -/
theorem mem_p3F_of_orderOf_two_pow {C : Subgroup G} {x : G} (hx : x ∈ C) {k : ℕ}
    (h : orderOf x = 2 ^ k) : x ∈ (Submission.Blueprint.oddResidual C).map C.subtype := by
  refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩, ?_, rfl⟩
  refine mem_oddResidual_of_pow_two_eq_one (x := (⟨x, hx⟩ : ↥C)) (k := k) ?_
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← h, pow_orderOf_eq_one]
  rfl

/-- `A` is subnormal in `V = centD H t` in the §5 configuration. -/
theorem IsSubnormalIn_A_V {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ}
    {P A : Subgroup G} {r : ℕ} (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    IsSubnormalIn A (centD H t) :=
  Relation.ReflTransGen.single
    ⟨h.A_le, (Subgroup.normal_subgroupOf_iff_le_normalizer h.A_le).mpr h.A_normal⟩

/-- The hypothesis `N_K(A) ≠ 1` of Ch. II §4 Prop. 3 for `X = A` in the §5 configuration. -/
theorem HasNonTrivialNK_A {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ}
    {P A : Subgroup G} {r : ℕ} (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    Work.ThreePoints.HasNonTrivialNK H t A := by
  classical
  have hp2 : 2 ≤ p := h.prime.two_le
  have hcard : 3 ≤ (Work.NormalComplement.Design.CK H t A).ncard := by
    rw [h.A_CK]
    have h4 : 4 ≤ 2 ^ p := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp2
    omega
  obtain ⟨k, hk, hk1⟩ : ∃ k ∈ Work.NormalComplement.Design.CK H t A, k ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hsub : Work.NormalComplement.Design.CK H t A ⊆ ({1} : Set G) :=
      fun x hx => by simpa using hcon x hx
    have h1 : (Work.NormalComplement.Design.CK H t A).ncard ≤ 1 := by
      calc (Work.NormalComplement.Design.CK H t A).ncard ≤ ({1} : Set G).ncard :=
            Set.ncard_le_ncard hsub (Set.finite_singleton 1)
        _ = 1 := Set.ncard_singleton 1
    omega
  have hkK : k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t := by
    have hh := hk.1
    simpa [Work.NormalComplement.Design.CK, Work.ThmF.Kset] using hh
  exact ⟨k, hkK, hk1, Subgroup.centralizer_le_normalizer _ hk.2⟩

/-- If `S` is a normal Sylow `2`-subgroup of `K`, every element of `K` of `2`-power order lies
in `S`. -/
theorem mem_of_orderOf_two_pow_of_normal_sylow {K S : Subgroup G} (hSK : S ≤ K)
    (hSn : (S.subgroupOf K).Normal) (hSpg : IsPGroup 2 (S.subgroupOf K))
    (hidx : ¬ 2 ∣ (S.subgroupOf K).index) {x : G} (hxK : x ∈ K) {k : ℕ}
    (hx : orderOf x = 2 ^ k) : x ∈ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S' : Subgroup ↥K := S.subgroupOf K
  haveI : S'.Normal := hSn
  let x' : ↥K := ⟨x, hxK⟩
  have hx'ord : orderOf x' = 2 ^ k := (Subgroup.orderOf_coe x').symm.trans hx
  have hpg : IsPGroup 2 (Subgroup.zpowers x') := by
    rw [IsPGroup.iff_card]
    exact ⟨k, by rw [Nat.card_zpowers, hx'ord]⟩
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hpg
  haveI : (hSpg.toSylow hidx).Normal := by
    rw [IsPGroup.toSylow_coe hSpg hidx]; exact hSn
  have hQeq : Q = hSpg.toSylow hidx := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥K) Q (hSpg.toSylow hidx)
    calc Q = g⁻¹ • (g • Q) := (inv_smul_smul g Q).symm
      _ = g⁻¹ • (hSpg.toSylow hidx) := by rw [hg]
      _ = hSpg.toSylow hidx := Sylow.smul_eq_of_normal
  have hxSyl : x' ∈ ((hSpg.toSylow hidx : Sylow 2 ↥K) : Subgroup ↥K) := by
    rw [← hQeq]
    exact hQ (Subgroup.mem_zpowers x')
  rw [IsPGroup.toSylow_coe hSpg hidx] at hxSyl
  rw [Subgroup.mem_subgroupOf] at hxSyl
  exact hxSyl

/-- `IsPGroup` passes to a subgroup of the form `S.subgroupOf K`. -/
theorem isPGroup_subgroupOf {p : ℕ} {K S : Subgroup G} (hSK : S ≤ K) (h : IsPGroup p ↥S) :
    IsPGroup p ↥(S.subgroupOf K) :=
  IsPGroup.of_injective h (Subgroup.subgroupOfEquivOfLe hSK).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hSK).injective

/-! ## The Sylow `2`-subgroup `S` of `F ⊓ H` -/

/-- The list of properties of the Sylow `2`-subgroup `S ≤ F ⊓ H` (`F = O^{2'}(C_G(V))`,
`V = centD H t`) used by the proof of §5 Prop. 2 (a): `S` is the (normal) Sylow `2`-subgroup of
`F ⊓ H`, `H ⊓ N_G(V) = S ⋊ N_D(V)`, `S` is sharply transitive from `H^t` onto `Ω_V ∖ {H}`
(so `|Ω_V| = |S| + 1`), `S` has a unique involution and exponent `4`, and `|S| ≤ 8`. -/
structure P2aSdata (H : Subgroup G) (t : G) (S : Subgroup G) : Prop where
  /-- `S` is a `2`-group. -/
  pg : IsPGroup 2 S
  /-- `S` is nontrivial. -/
  ne_bot : S ≠ ⊥
  /-- `S ≤ F ⊓ H`. -/
  le : S ≤ Fc H t ⊓ H
  /-- `S` is a Sylow `2`-subgroup of `F ⊓ H`. -/
  idx : ¬ 2 ∣ (S.subgroupOf (Fc H t ⊓ H)).index
  /-- `H ⊓ N_G(V)` normalises `S`, whence `S ⊴ F ⊓ H`. -/
  norm : H ⊓ Sec5f.NN H t ≤ Subgroup.normalizer (S : Set G)
  /-- `S ⊓ D = ⊥` with `D = twoPoint H t`. -/
  infD : S ⊓ twoPoint H t = ⊥
  /-- `S ⊔ (D ⊓ N_G(V)) = H ⊓ N_G(V)`. -/
  sup : S ⊔ (twoPoint H t ⊓ Sec5f.NN H t) = H ⊓ Sec5f.NN H t
  /-- `S` has a unique involution. -/
  uniq : (involutions (S : Set G)).ncard = 1
  /-- `D = twoPoint H t = H ⊓ H^t` has odd order (strong embeddedness of `H`). -/
  oddD : Odd (Nat.card ↥(twoPoint H t))
  /-- `S` has exponent `4`. -/
  exp4 : ∀ x ∈ S, x ^ 4 = 1
  /-- `S` is sharply transitive from `H^t` onto `Ω_V ∖ {H}`. -/
  sharp : ∀ c ∈ Om H t, c ≠ (QuotientGroup.mk (1 : G) : G ⧸ H) →
      ∃! q : ↥S, (q : G) • (QuotientGroup.mk t : G ⧸ H) = c
  /-- `|Ω_V| = |S| + 1`. -/
  card : (Om H t).ncard = (S : Set G).ncard + 1
  /-- `|S| ≤ 8`. -/
  small : (S : Set G).ncard ≤ 8

section Sdata

variable {H : Subgroup G} {t : G} {S : Subgroup G}

theorem P2aSdata.subtype_le (h : P2aSdata H t S) : S ≤ Fc H t := h.le.trans inf_le_left

theorem P2aSdata.le_H (h : P2aSdata H t S) : S ≤ H := h.le.trans inf_le_right

theorem P2aSdata.le_NN (h : P2aSdata H t S) : S ≤ Sec5f.NN H t :=
  h.subtype_le.trans (Fc_le_normalizer H t)

/-- `S` is normal in `F ⊓ H`. -/
theorem P2aSdata.subgroupOf_normal (h : P2aSdata H t S) :
    (S.subgroupOf (Fc H t ⊓ H)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mpr
    (le_trans (le_inf inf_le_right (le_trans inf_le_left (Fc_le_normalizer H t))) h.norm)

end Sdata

/-! ## Existence of the datum `P2aSdata` -/

/-- In the §5 configuration there is a unique involution `u ∈ H` centralising `V = centD H t`,
together with the uniqueness statement. -/
theorem exists_unique_involution_CHV (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp) {H : Subgroup G} {t : G}
    {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    ∃ u : G, u ∈ H ∧ orderOf u = 2 ∧ u ∈ Subgroup.centralizer (centD H t : Set G) ∧
      ∀ v : G, v ∈ H ⊓ Subgroup.centralizer (centD H t : Set G) → orderOf v = 2 → v = u := by
  classical
  obtain ⟨u, hu⟩ := Set.ncard_eq_one.mp
    (Work.NormalComplement.p2a_invol_unique hFT hC hC4 hP3 h)
  have humem : u ∈ involutions
      ((H ⊓ Subgroup.centralizer (centD H t : Set G) : Subgroup G) : Set G) := by
    rw [hu]; exact Set.mem_singleton u
  rw [Submission.Blueprint.involutions, Set.mem_setOf_eq] at humem
  refine ⟨u, (Subgroup.mem_inf.mp humem.1).1, humem.2, (Subgroup.mem_inf.mp humem.1).2, ?_⟩
  intro v hv hvo
  have hvmem : v ∈ involutions
      ((H ⊓ Subgroup.centralizer (centD H t : Set G) : Subgroup G) : Set G) := by
    rw [Submission.Blueprint.involutions, Set.mem_setOf_eq]
    exact ⟨hv, hvo⟩
  rw [hu] at hvmem
  exact Set.mem_singleton_iff.mp hvmem

/-- Existence of the Sylow `2`-subgroup `S ≤ F ⊓ H` and its datum, from the §5 configuration. -/
theorem p2aSdata_exists (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hMF2 : Submission.Blueprint.BenderModelFacts2Prop) {H : Subgroup G} {t : G}
    {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    ∃ S : Subgroup G, P2aSdata H t S := by
  classical
  have hBrSz : Submission.Blueprint.BrauerSuzukiProp := Work.BrauerSuzuki.brauerSuzuki
  have hZJ : Submission.Blueprint.GlaubermanZJProp := Work.ThmF.ChV12.glaubermanZJ_free
  have hA : Submission.Blueprint.ThmAProp :=
    Work.DoubleTransitivity.Sec7.ThmA hFT hZJ hBrSz
  have hMod : Submission.Blueprint.ModelFactsProp := Work.Models.models hFT
  have hPkg := Work.ThreePoints.p3pkg hFT hC hA hZJ hBrSz hMod h.sit h.se h.invol h.notMem
    (centD H t) le_rfl ⟨A, h.A_ne, IsSubnormalIn_A_V h, HasNonTrivialNK_A h⟩
  obtain ⟨⟨hNGeq, S, hSpg, hSle, hSidx, hSnorm, hSD, hSsup⟩, h2t⟩ := hPkg
  -- the unique involution `u₀` of `H ⊓ C_G(V)`, which lies in `F ⊓ H` and hence in `S`
  obtain ⟨u0, hu0H, hu0ord, hu0C, hu0uniq⟩ :=
    exists_unique_involution_CHV hFT hC hC4 hP3 h
  have hu0C' : u0 ∈ (Subgroup.centralizer (centD H t : Set G)) := hu0C
  have hu0F : u0 ∈ Fc H t :=
    mem_p3F_of_orderOf_two_pow (C := Subgroup.centralizer (centD H t : Set G)) hu0C'
      (k := 1) (by simpa using hu0ord)
  have hu0FH : u0 ∈ Fc H t ⊓ H := Subgroup.mem_inf.mpr ⟨hu0F, hu0H⟩
  have hu0S : u0 ∈ S :=
    mem_of_orderOf_two_pow_of_normal_sylow hSle
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hSle).mpr
        (le_trans (le_inf inf_le_right (le_trans inf_le_left (Fc_le_normalizer H t))) hSnorm))
      (isPGroup_subgroupOf hSle hSpg) hSidx hu0FH (k := 1) (by simpa using hu0ord)
  have hu0ne : u0 ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hu0ord
    exact absurd hu0ord (by norm_num)
  -- ## `S ≠ ⊥`
  have hnebot : S ≠ ⊥ := fun hbot => hu0ne (by rw [hbot] at hu0S; simpa using hu0S)
  -- ## uniqueness of the involution of `S`
  have huniq : (involutions (S : Set G)).ncard = 1 := by
    have hsubset : involutions (S : Set G) ⊆ ({u0} : Set G) := by
      intro v hv
      rw [Submission.Blueprint.involutions, Set.mem_ofPred_eq] at hv
      rw [Set.mem_singleton_iff]
      exact hu0uniq v (Subgroup.mem_inf.mpr
        ⟨(hSle hv.1).2, (Fc_le_centralizer H t) (hSle hv.1).1⟩) hv.2
    have hmem : u0 ∈ involutions (S : Set G) := by
      rw [Submission.Blueprint.involutions, Set.mem_ofPred_eq]
      exact ⟨hu0S, hu0ord⟩
    have hset : involutions (S : Set G) = {u0} := by
      refine Set.Subset.antisymm hsubset ?_
      intro v hv
      rw [Set.mem_singleton_iff] at hv
      rw [hv]; exact hmem
    rw [hset, Set.ncard_singleton]
  -- ## exponent `4`
  have hexp4 : ∀ x ∈ S, x ^ 4 = 1 := by
    intro x hxS
    have hxH : x ∈ H := (hSle hxS).2
    have hxA : x ∈ Work.ThreePoints.p3F A :=
      Work.NormalComplement.Sec5Fix.p3F_anti h.A_le (hSle hxS).1
    have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥S)).mp hSpg
    have hdvd : orderOf x ∣ 2 ^ n := by
      rw [← hn]
      exact Subgroup.orderOf_dvd_natCard S hxS
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact Work.NormalComplement.p2a_pow_four hFT hC hC4 hMF2 h x hxH hxA ⟨k, hk⟩
  -- ## sharp transitivity
  have hsharp : ∀ c ∈ Om H t, c ≠ (QuotientGroup.mk (1 : G) : G ⧸ H) →
      ∃! q : ↥S, (q : G) • (QuotientGroup.mk t : G ⧸ H) = c :=
    Work.ThreePoints.P3Sub.sharpTrans_of_P3Ab_aux h.invol h.notMem (le_refl (centD H t)) h2t
      hSle hSnorm hSD hSsup
  -- ## `|Ω_V| = |S| + 1`
  have hcard : (Om H t).ncard = (S : Set G).ncard + 1 := by
    have hne_t_one : (QuotientGroup.mk t : G ⧸ H) ≠ (QuotientGroup.mk (1 : G) : G ⧸ H) :=
      Work.ThreePoints.P3Sub.mk_one_ne_mk_t h.notMem |>.symm
    have hmem : ∀ q : ↥S, (q : G) • (QuotientGroup.mk t : G ⧸ H) ∈
        Om H t \ {(QuotientGroup.mk (1 : G) : G ⧸ H)} := by
      intro q
      refine ⟨Work.ThreePoints.smul_mem_fixedPts_of_mem_normalizer
        ((Fc_le_normalizer H t) (hSle q.2).1)
        (Work.ThreePoints.mk_t_mem_fixedPts_of_le_centD (le_refl (centD H t))), ?_⟩
      intro hcon
      have h2 : (q : G)⁻¹ • ((q : G) • (QuotientGroup.mk t : G ⧸ H)) =
          (q : G)⁻¹ • (QuotientGroup.mk (1 : G) : G ⧸ H) := by rw [hcon]
      rw [inv_smul_smul] at h2
      have h3 : (q : G)⁻¹ • (QuotientGroup.mk (1 : G) : G ⧸ H) =
          (QuotientGroup.mk (1 : G) : G ⧸ H) := by
        rw [Work.DoubleTransitivity.smul_mk, mul_one]
        exact QuotientGroup.eq.mpr (by simpa using H.inv_mem (hSle q.2).2)
      rw [h3] at h2
      exact hne_t_one h2
    have hcarddif : (Om H t \ {(QuotientGroup.mk (1 : G) : G ⧸ H)}).ncard =
        (S : Set G).ncard := by
      refine Eq.symm (Set.ncard_congr (s := (S : Set G))
        (t := Om H t \ {(QuotientGroup.mk (1 : G) : G ⧸ H)})
        (fun q : G => fun _ => q • (QuotientGroup.mk t : G ⧸ H))
        (fun q hq => hmem ⟨q, hq⟩) ?_ ?_)
      · intro a b ha hb hab
        have hc := hmem ⟨a, ha⟩
        obtain ⟨q, hq, huniq⟩ := hsharp _ hc.1 hc.2
        have h1 : (⟨a, ha⟩ : ↥S) = q := huniq ⟨a, ha⟩ (by simpa using hab)
        have h2 : (⟨b, hb⟩ : ↥S) = q := huniq ⟨b, hb⟩ (by simpa using hab.symm)
        exact congrArg Subtype.val (h1.trans h2.symm)
      · intro c hc
        obtain ⟨q, hq, -⟩ := hsharp c hc.1 hc.2
        exact ⟨(q : G), q.2, hq⟩
    have hmem1 : (QuotientGroup.mk (1 : G) : G ⧸ H) ∈ Om H t :=
      Work.ThreePoints.pt_mem_fixedPts_of_le_centD (le_refl (centD H t))
    have hsplit := Set.ncard_sdiff_singleton_of_mem hmem1
    have hpos : 1 ≤ (Om H t).ncard := by
      have h0 : 0 < (Om H t).ncard := Set.ncard_pos (Set.toFinite _) |>.mpr ⟨_, hmem1⟩
      omega
    omega
  -- ## `|S| ≤ 8`
  have hsmall : (S : Set G).ncard ≤ 8 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have huniqInv : Work.BrauerSuzuki.HasUniqueInvolution ↥S :=
      Work.NormalComplement.p2a_appIII_hasUniqueInvolution_of_ncard_eq_one huniq
    have hcardS : Nat.card ↥S = (S : Set G).ncard :=
      Work.NormalComplement.p2a_appIII_ncard_sub_eq_natCard S |>.symm
    rcases Work.BrauerSuzuki.Group.isCyclicOrGenQuaternion_of_uniqueInvolution hSpg huniqInv
      with hcyc | hgen
    · have := Work.NormalComplement.p2a_appIII_cyclic_card_le_four hcyc hexp4
      rw [← hcardS]; omega
    · have h8 := Work.NormalComplement.p2a_appIII_genQuaternion_card_eq_eight hgen hexp4
      rw [← hcardS, h8]
  exact ⟨S, hSpg, hnebot, hSle, hSidx, hSnorm, hSD, hSsup, huniq,
    h.se.2.2 t h.notMem, hexp4, hsharp, hcard, hsmall⟩

/-- `S` contains (the unique) involution of `H ⊓ C_G(V)`. -/
theorem P2aSdata.mem_of_involution {H : Subgroup G} {t : G} {S : Subgroup G}
    (h : P2aSdata H t S) {v : G} (hvH : v ∈ H)
    (hvC : v ∈ Subgroup.centralizer (centD H t : Set G)) (hvo : orderOf v = 2) : v ∈ S :=
  mem_of_orderOf_two_pow_of_normal_sylow h.le h.subgroupOf_normal (isPGroup_subgroupOf h.le h.pg)
    h.idx (Subgroup.mem_inf.mpr
      ⟨mem_p3F_of_orderOf_two_pow (C := _) hvC (k := 1) (by simpa using hvo), hvH⟩)
    (k := 1) (by simpa using hvo)

end P2a
end Work.NormalComplement.Sec5Fix
