/-
# Wielandt's fusion lemma for regular Sylow subgroups (Huppert IV.8.1 / IV.8.3)

Target (the statement of this file):

  `P ⊓ G' ≤ ⁅N_G(P), N_G(P)⁆`  for a *regular* Sylow `p`-subgroup `P` of a finite group `G`.

## Mathematical content

By Mathlib's focal subgroup theorem (`Subgroup.commutator_inf_eq_focalSubgroup`) the subgroup
`P ⊓ G'` is the focal subgroup of `P` in `G`.  The statement above is therefore *equivalent* to
"N_G(P) controls p-transfer in G" (Isaacs, *Finite Group Theory*, §5D), which for `P` regular is the
theorem of P. Hall and H. Wielandt (Huppert, *Endliche Gruppen I*, IV.8.1 + IV.8.3; Isaacs §10A).

## Reduction used here

Write `N = N_G(P)` and let `𝔄 ≤ N` be the kernel of the transfer of `N` into `P ⧸ P'`, so that
`𝔄` is normal in `N` with `N ⧸ 𝔄` abelian (indeed `N ⧸ 𝔄 ≃ P ⧸ P*` is a `p`-group) and
`𝔄 ⊓ P = P ⊓ N'`.  Let `V : G →* N ⧸ 𝔄` be the transfer of `G` with respect to the quotient map
`N →* N ⧸ 𝔄`.  Then

* `normalizerTransfer_eq_pow` (the crux, Huppert IV.8.3): for `x ∈ P` one has
  `V x = (x 𝔄) ^ [G : N]`.  This is proved by induction on `orderOf x` from the orbit formula for
  the transfer (`MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot`) together with
  Huppert's analysis of the action of `P` on `G ⧸ N`
  (`Work.LocalPrelim.rsf_block_decomposition`) and the regularity of `P`
  (Huppert III.10.5, 10.6; `Work.LocalPrelim.rsf_regular_block_product`);

* assembly: for `x ∈ P ⊓ G'` we get `V x = 1` (as `G'` lies in the kernel of any homomorphism into
  an abelian group) and hence `(x 𝔄) ^ [G : N] = 1`; since `x 𝔄` lies in the `p`-group
  `P ⧸ (P ⊓ 𝔄)` and `p ∤ [G : N]`, this forces `x ∈ 𝔄 ⊓ P = P ⊓ N'`, so `x ∈ N'`.
-/
import Mathlib
import Submission.Work.SmallRank.Regular.Defs
import Submission.Work.SmallRank.Regular.commutator_pow_eq_one_of_regular
import Submission.Work.SmallRank.Regular.mul_pow_of_commutator_pow_eq_one
import Submission.Work.SmallRank.Regular.pow_mul_eq_one_of_isRegular
import Submission.Work.SmallRank.Regular.isRegular_quotient
import Submission.Work.SmallRank.Regular.isRegular_subgroup
import Submission.Work.SmallRank.Regular.agemo_eq_bot_of_pow
import Submission.Work.SmallRank.Regular.commutator_le_of_mem
import Submission.Work.LocalPrelim.rsf_block_decomposition
import Submission.Work.LocalPrelim.rsf_regular_block_product
import Submission.Work.LocalPrelim.rsf_fixed_coset_eq_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000

namespace Work.LocalPrelim

open scoped commutatorElement Pointwise IsMulCommutative
open Subgroup

variable {G : Type*} [Group G]

/-- **Transfer computation with congruence.**

Let `H ≤ G` have finite index, `A` abelian and `φ : H →* A`.  If conjugates of powers of `g` that
land in `H` are congruent to those powers modulo `φ.ker`, then the transfer of `G` into `A`
relative to `φ` sends `g` to the `[G : H]`-th power of `g`.

This is `MonoidHom.transfer_eq_pow` with the pointwise "key" hypothesis weakened to a congruence
modulo `φ.ker`; this is exactly the form needed in Huppert, *Endliche Gruppen I*, IV.8.3. -/
theorem transfer_eq_pow_of_congruent {H : Subgroup G} [H.FiniteIndex]
    {A : Type*} [CommGroup A] (φ : H →* A) (g : G) (hpow : ∀ k : ℕ, g ^ k ∈ H)
    (key : ∀ (k : ℕ) (g₀ : G) (hk : g₀⁻¹ * g ^ k * g₀ ∈ H),
      φ ⟨g₀⁻¹ * g ^ k * g₀, hk⟩ = φ ⟨g ^ k, hpow k⟩) :
    MonoidHom.transfer φ g = φ ⟨g ^ H.index, hpow H.index⟩ := by
  classical
  haveI : Fintype (Quotient (MulAction.orbitRel (↥(Subgroup.zpowers g)) (G ⧸ H))) :=
    Fintype.ofFinite _
  have hg : g ∈ H := by simpa using hpow 1
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  trans ∏ q : Quotient (MulAction.orbitRel (↥(Subgroup.zpowers g)) (G ⧸ H)),
      φ ⟨g, hg⟩ ^ Function.minimalPeriod (fun x => g • x) q.out
  · refine Finset.prod_congr rfl (fun q _ => ?_)
    rw [key _ _ _, ← map_pow]
    congr 1
  · rw [Finset.prod_pow_eq_pow_sum, Subgroup.index_eq_sum_minimalPeriod H g, ← map_pow]
    congr 1

section Setup

variable [Finite G] {p : ℕ} [Fact p.Prime]

/-- The normalizer `N_G(P)` of a Sylow subgroup. -/
abbrev sylowNormalizer (P : Sylow p G) : Subgroup G := Subgroup.normalizer (P : Set G)

/-- `P`, viewed as a Sylow `p`-subgroup of its own normalizer `N_G(P)` (this is possible because
`P ⊴ N_G(P)`, so `P` is the unique Sylow `p`-subgroup of `N_G(P)`). -/
noncomputable def sylowInNormalizer (P : Sylow p G) : Sylow p (sylowNormalizer P) :=
  (P.isPGroup'.comap_subtype : IsPGroup p
      ↥((P : Subgroup G).subgroupOf (sylowNormalizer P))).toSylow
    (by
      intro h
      apply Sylow.not_dvd_index P
      rw [← Subgroup.relIndex_mul_index
        (le_normalizer : (P : Subgroup G) ≤ Subgroup.normalizer (P : Set G))]
      exact dvd_trans h (dvd_mul_right _ _))

/-- `P`, as a subgroup of `N_G(P)`, consists of the elements of `P`. -/
theorem mem_sylowInNormalizer (P : Sylow p G) (x : G) (hx : x ∈ (P : Subgroup G)) :
    (⟨x, P.le_normalizer hx⟩ : ↥(sylowNormalizer P)) ∈
      (sylowInNormalizer P : Subgroup ↥(sylowNormalizer P)) := by
  have hsyl : (sylowInNormalizer P : Subgroup ↥(sylowNormalizer P)) =
      (P : Subgroup G).subgroupOf (sylowNormalizer P) := IsPGroup.toSylow_coe _ _
  rw [hsyl]
  show ((⟨x, P.le_normalizer hx⟩ : ↥(sylowNormalizer P)) : G) ∈ (P : Subgroup G)
  exact hx

/-- The kernel `𝔄` of the transfer of `N_G(P)` into `P ⧸ P'`; it is the normal subgroup of
`N_G(P)` with `𝔄 ⊓ P = P ⊓ N'` (the focal subgroup of `P` in `N_G(P)`). -/
noncomputable abbrev normalizerFocal (P : Sylow p G) : Subgroup ↥(sylowNormalizer P) :=
  (sylowInNormalizer P).transferFocal.ker

/-- `N_G(P) ⧸ 𝔄` is abelian (it is isomorphic to `P ⧸ P*`). -/
noncomputable instance instIsMulCommutativeNormalizerFocal (P : Sylow p G) :
    IsMulCommutative (↥(sylowNormalizer P) ⧸ normalizerFocal P) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    (Abelianization.commutator_subset_ker (sylowInNormalizer P).transferFocal)

/-- The transfer of `G` into the abelian quotient `N_G(P) ⧸ 𝔄`. -/
noncomputable abbrev normalizerTransfer (P : Sylow p G) :
    G →* (↥(sylowNormalizer P) ⧸ normalizerFocal P) :=
  MonoidHom.transfer (QuotientGroup.mk' (normalizerFocal P))

theorem orderOf_conj' (a b : G) : orderOf (a⁻¹ * b * a) = orderOf b := by
  have h : a⁻¹ * b * a = MulAut.conj a⁻¹ b := by rw [MulAut.conj_apply, inv_inv]
  rw [h, MulEquiv.orderOf_eq]

theorem not_dvd_index_sylowNormalizer (P : Sylow p G) :
    ¬ p ∣ (sylowNormalizer P).index := by
  intro h
  refine Sylow.not_dvd_index P ?_
  rw [← Subgroup.relIndex_mul_index
    (le_normalizer : (P : Subgroup G) ≤ Subgroup.normalizer (P : Set G))]
  exact dvd_mul_of_dvd_right h _

theorem mem_sylow_of_mem_normalizer (P : Sylow p G) {z : G} (hz : z ∈ (P : Subgroup G))
    {s : G} (hs : s⁻¹ * z * s ∈ sylowNormalizer P) : s⁻¹ * z * s ∈ (P : Subgroup G) := by
  set N := sylowNormalizer P with hN
  set z' : ↥N := ⟨s⁻¹ * z * s, hs⟩ with hz'def
  haveI hPnorm : ((sylowInNormalizer P : Subgroup ↥N)).Normal := Subgroup.normal_in_normalizer
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_orderOf_eq_pow (⟨z, hz⟩ : ↥(P : Subgroup G))
  have hkz : orderOf z = p ^ k := by
    show orderOf ((⟨z, hz⟩ : ↥(P : Subgroup G)) : G) = p ^ k
    rw [Subgroup.orderOf_coe, hk]
  have hk' : orderOf z' = p ^ k := by
    rw [(Subgroup.orderOf_coe z').symm]
    show orderOf (s⁻¹ * z * s) = p ^ k
    rw [orderOf_conj', hkz]
  have hquot : (QuotientGroup.mk' ((sylowInNormalizer P : Subgroup ↥N))) z' = 1 := by
    have h1 : orderOf ((QuotientGroup.mk' ((sylowInNormalizer P : Subgroup ↥N))) z') ∣ p ^ k := by
      rw [← hk']
      exact orderOf_map_dvd _ _
    have h2 : orderOf ((QuotientGroup.mk' ((sylowInNormalizer P : Subgroup ↥N))) z') ∣
        Nat.card (↥N ⧸ (sylowInNormalizer P : Subgroup ↥N)) := orderOf_dvd_natCard _
    have h3 : ¬ p ∣ Nat.card (↥N ⧸ (sylowInNormalizer P : Subgroup ↥N)) := by
      rw [← Subgroup.index_eq_card]
      exact Sylow.not_dvd_index (sylowInNormalizer P)
    have h4 : orderOf ((QuotientGroup.mk' ((sylowInNormalizer P : Subgroup ↥N))) z') = 1 := by
      have hcop : (p ^ k).Coprime (Nat.card (↥N ⧸ (sylowInNormalizer P : Subgroup ↥N))) :=
        (Nat.Prime.coprime_pow_of_not_dvd (m := k) Fact.out h3).symm
      have hdvd := Nat.dvd_gcd h1 h2
      rw [hcop.gcd_eq_one] at hdvd
      exact Nat.dvd_one.mp hdvd
    rwa [orderOf_eq_one_iff] at h4
  have hmem : z' ∈ (sylowInNormalizer P : Subgroup ↥N) := by
    have := MonoidHom.mem_ker.mpr hquot
    rwa [QuotientGroup.ker_mk'] at this
  have hcoe : (sylowInNormalizer P : Subgroup ↥N) = (P : Subgroup G).subgroupOf N :=
    Sylow.coe_subtype P le_normalizer
  rw [hcoe, Subgroup.mem_subgroupOf] at hmem
  simpa [hz'def] using hmem

/-- `F` follows from `E`. -/
theorem F_of_E (P : Sylow p G)
    (hE : ∀ (z : G) (hz : z ∈ (P : Subgroup G)),
      normalizerTransfer P z =
        ((QuotientGroup.mk' (normalizerFocal P)) ⟨z, P.le_normalizer hz⟩) ^
          (sylowNormalizer P).index) :
    ∀ (z : G) (hz : z ∈ (P : Subgroup G)) (s : G) (hs : s⁻¹ * z * s ∈ sylowNormalizer P),
      (QuotientGroup.mk' (normalizerFocal P)) ⟨s⁻¹ * z * s, hs⟩ =
        (QuotientGroup.mk' (normalizerFocal P)) ⟨z, P.le_normalizer hz⟩ := by
  intro z hz s hs
  have hz'P : s⁻¹ * z * s ∈ (P : Subgroup G) := mem_sylow_of_mem_normalizer P hz hs
  have hV : normalizerTransfer P (s⁻¹ * z * s) = normalizerTransfer P z := by
    rw [map_mul, map_mul, map_inv]
    rw [mul_assoc, mul_comm (normalizerTransfer P z) (normalizerTransfer P s), ← mul_assoc,
      inv_mul_cancel, one_mul]
  have h1 := hE z hz
  have h2 := hE (s⁻¹ * z * s) hz'P
  have heq : ((QuotientGroup.mk' (normalizerFocal P)) ⟨s⁻¹ * z * s, P.le_normalizer hz'P⟩) ^
        (sylowNormalizer P).index =
      ((QuotientGroup.mk' (normalizerFocal P)) ⟨z, P.le_normalizer hz⟩) ^
        (sylowNormalizer P).index := by
    rw [← h2, ← h1, hV]
  set M : Subgroup (↥(sylowNormalizer P) ⧸ normalizerFocal P) :=
    (sylowInNormalizer P : Subgroup ↥(sylowNormalizer P)).map
      (QuotientGroup.mk' (normalizerFocal P)) with hMdef
  have hM : IsPGroup p ↥M := (sylowInNormalizer P).2.map _
  have hmem1 : (QuotientGroup.mk' (normalizerFocal P)) ⟨s⁻¹ * z * s, P.le_normalizer hz'P⟩ ∈ M :=
    Subgroup.mem_map.mpr ⟨_, mem_sylowInNormalizer P _ hz'P, rfl⟩
  have hmem2 : (QuotientGroup.mk' (normalizerFocal P)) ⟨z, P.le_normalizer hz⟩ ∈ M :=
    Subgroup.mem_map.mpr ⟨_, mem_sylowInNormalizer P z hz, rfl⟩
  have hEq : (⟨(QuotientGroup.mk' (normalizerFocal P)) ⟨s⁻¹ * z * s, P.le_normalizer hz'P⟩,
        hmem1⟩ : ↥M) = ⟨(QuotientGroup.mk' (normalizerFocal P)) ⟨z, P.le_normalizer hz⟩, hmem2⟩ := by
    refine ((hM.powEquiv' (not_dvd_index_sylowNormalizer P)).apply_eq_iff_eq
      (x := ⟨_, hmem1⟩) (y := ⟨_, hmem2⟩)).mp ?_
    simpa using heq
  simpa using congrArg Subtype.val hEq

/-- The order-restricted form of `F_of_E`: `F` for elements of a fixed order follows from `E`
for elements of that same order (needed for the two-phase induction). -/
theorem F_of_E_of_order (P : Sylow p G) (n : ℕ)
    (hE : ∀ (z : G) (hz : z ∈ (P : Subgroup G)), orderOf z = n →
      normalizerTransfer P z =
        ((QuotientGroup.mk' (normalizerFocal P)) ⟨z, P.le_normalizer hz⟩) ^
          (sylowNormalizer P).index) :
    ∀ (z : G) (hz : z ∈ (P : Subgroup G)), orderOf z = n →
      ∀ (s : G) (hs : s⁻¹ * z * s ∈ sylowNormalizer P),
        (QuotientGroup.mk' (normalizerFocal P)) ⟨s⁻¹ * z * s, hs⟩ =
          (QuotientGroup.mk' (normalizerFocal P)) ⟨z, P.le_normalizer hz⟩ := by
  intro z hz hzn s hs
  have hz'P : s⁻¹ * z * s ∈ (P : Subgroup G) := mem_sylow_of_mem_normalizer P hz hs
  have hV : normalizerTransfer P (s⁻¹ * z * s) = normalizerTransfer P z := by
    rw [map_mul, map_mul, map_inv]
    rw [mul_assoc, mul_comm (normalizerTransfer P z) (normalizerTransfer P s), ← mul_assoc,
      inv_mul_cancel, one_mul]
  have h1 := hE z hz hzn
  have h2 := hE (s⁻¹ * z * s) hz'P (by rw [orderOf_conj', hzn])
  have heq : ((QuotientGroup.mk' (normalizerFocal P)) ⟨s⁻¹ * z * s, P.le_normalizer hz'P⟩) ^
        (sylowNormalizer P).index =
      ((QuotientGroup.mk' (normalizerFocal P)) ⟨z, P.le_normalizer hz⟩) ^
        (sylowNormalizer P).index := by
    rw [← h2, ← h1, hV]
  set M : Subgroup (↥(sylowNormalizer P) ⧸ normalizerFocal P) :=
    (sylowInNormalizer P : Subgroup ↥(sylowNormalizer P)).map
      (QuotientGroup.mk' (normalizerFocal P)) with hMdef
  have hM : IsPGroup p ↥M := (sylowInNormalizer P).2.map _
  have hmem1 : (QuotientGroup.mk' (normalizerFocal P)) ⟨s⁻¹ * z * s, P.le_normalizer hz'P⟩ ∈ M :=
    Subgroup.mem_map.mpr ⟨_, mem_sylowInNormalizer P _ hz'P, rfl⟩
  have hmem2 : (QuotientGroup.mk' (normalizerFocal P)) ⟨z, P.le_normalizer hz⟩ ∈ M :=
    Subgroup.mem_map.mpr ⟨_, mem_sylowInNormalizer P z hz, rfl⟩
  have hEq : (⟨(QuotientGroup.mk' (normalizerFocal P)) ⟨s⁻¹ * z * s, P.le_normalizer hz'P⟩,
        hmem1⟩ : ↥M) = ⟨(QuotientGroup.mk' (normalizerFocal P)) ⟨z, P.le_normalizer hz⟩, hmem2⟩ := by
    refine ((hM.powEquiv' (not_dvd_index_sylowNormalizer P)).apply_eq_iff_eq
      (x := ⟨_, hmem1⟩) (y := ⟨_, hmem2⟩)).mp ?_
    simpa using heq
  simpa using congrArg Subtype.val hEq

theorem phase1_mov (P : Sylow p G) (n : ℕ) (z : G) (hzP : z ∈ (P : Subgroup G))
    (hz1 : z ≠ 1) (hzn : orderOf z = n)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers z) (G ⧸ sylowNormalizer P))]
    (ih : ∀ k < n, ∀ (w : G) (hw : w ∈ (P : Subgroup G)), orderOf w = k →
        ∀ (s : G) (hs : s⁻¹ * w * s ∈ sylowNormalizer P),
          (QuotientGroup.mk' (normalizerFocal P)) ⟨s⁻¹ * w * s, hs⟩ =
            (QuotientGroup.mk' (normalizerFocal P)) ⟨w, P.le_normalizer hw⟩) :
    (∏ q ∈ Finset.univ.filter
        (fun q : MulAction.orbitRel.Quotient (Subgroup.zpowers z) (G ⧸ sylowNormalizer P) =>
          ¬ (Function.minimalPeriod (z • ·) q.out = 1)),
        (QuotientGroup.mk' (normalizerFocal P))
          ⟨(q.out.out)⁻¹ * z ^ Function.minimalPeriod (z • ·) q.out * q.out.out,
            QuotientGroup.out_conj_pow_minimalPeriod_mem (sylowNormalizer P) z q.out⟩)
      = ((QuotientGroup.mk' (normalizerFocal P)) ⟨z, P.le_normalizer hzP⟩) ^
        (∑ q ∈ Finset.univ.filter
          (fun q : MulAction.orbitRel.Quotient (Subgroup.zpowers z) (G ⧸ sylowNormalizer P) =>
            ¬ (Function.minimalPeriod (z • ·) q.out = 1)),
          Function.minimalPeriod (z • ·) q.out) := by
  trans ∏ q ∈ Finset.univ.filter
        (fun q : MulAction.orbitRel.Quotient (Subgroup.zpowers z) (G ⧸ sylowNormalizer P) =>
          ¬ (Function.minimalPeriod (z • ·) q.out = 1)),
      ((QuotientGroup.mk' (normalizerFocal P)) ⟨z, P.le_normalizer hzP⟩) ^
        Function.minimalPeriod (z • ·) q.out
  · refine Finset.prod_congr rfl (fun q hq => ?_)
    rw [Finset.mem_filter] at hq
    obtain ⟨-, hq1⟩ := hq
    -- `n = p ^ s` and the minimal period divides `n`
    obtain ⟨s, hs⟩ := P.isPGroup'.exists_orderOf_eq_pow (⟨z, hzP⟩ : ↥(P : Subgroup G))
    have hzn' : n = p ^ s := by
      rw [← hzn]
      show orderOf z = p ^ s
      rw [show z = ((⟨z, hzP⟩ : ↥(P : Subgroup G)) : G) from rfl, Subgroup.orderOf_coe, hs]
    have hn0 : n ≠ 0 := by rw [hzn']; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero
    have hper : Function.IsPeriodicPt (z • ·) n q.out := by
      rw [MulAction.isPeriodicPt_smul_iff, ← hzn, pow_orderOf_eq_one, one_smul]
    have hdiv : Function.minimalPeriod (z • ·) q.out ∣ n := hper.minimalPeriod_dvd
    have hne0 : Function.minimalPeriod (z • ·) q.out ≠ 0 :=
      fun h0 => hn0 (Nat.zero_dvd.mp (h0 ▸ hdiv))
    -- hence `orderOf (z ^ m) < n`
    have hlt : orderOf (z ^ Function.minimalPeriod (z • ·) q.out) < n := by
      rw [orderOf_pow, hzn, Nat.gcd_eq_right hdiv]
      exact Nat.div_lt_self (Nat.pos_of_ne_zero hn0)
        (Nat.lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hne0) (Ne.symm hq1))
    -- apply the induction hypothesis `F` to `z ^ m`
    have hw := ih (orderOf (z ^ Function.minimalPeriod (z • ·) q.out)) hlt
      (z ^ Function.minimalPeriod (z • ·) q.out) (pow_mem hzP _) rfl
      (q.out.out) (QuotientGroup.out_conj_pow_minimalPeriod_mem (sylowNormalizer P) z q.out)
    rw [hw, ← map_pow]
    congr 1
  · exact Finset.prod_pow_eq_pow_sum _ _ _

/-- If a coset `c` of `N_G(P)` is fixed by `z`, then `c.out⁻¹ * z * c.out ∈ N_G(P)`. -/
theorem mem_of_fixed (P : Sylow p G) {z : G} {c : G ⧸ sylowNormalizer P}
    (h : z • c = c) : (c.out)⁻¹ * z * (c.out) ∈ sylowNormalizer P := by
  have h1 : ((z * c.out : G) : G ⧸ sylowNormalizer P) =
      ((c.out : G) : G ⧸ sylowNormalizer P) := by
    rw [← smul_eq_mul, MulAction.Quotient.coe_smul_out, h, QuotientGroup.out_eq']
  have h2 : (z * c.out)⁻¹ * c.out ∈ sylowNormalizer P := QuotientGroup.eq.mp h1
  have h3 : (c.out)⁻¹ * z⁻¹ * c.out ∈ sylowNormalizer P := by simpa [mul_assoc] using h2
  simpa [mul_assoc] using (sylowNormalizer P).inv_mem h3

/-
## Remaining proof of `normalizerTransfer_eq_pow` (the crux), with the ingredients in place

The pieces already proved above are `orderOf_conj'`, `not_dvd_index_sylowNormalizer`,
`mem_sylow_of_mem_normalizer`, `mem_sylowInNormalizer`, `mem_of_fixed`, `F_of_E` (`F` follows
from `E`), `phase1_mov` (the non-fixed orbits of Huppert's computation) and, in sibling files,
`rsf_block_decomposition` (Huppert IV.8.3 (a)), `rsf_regular_block_product` (Huppert IV.8.3 (c)),
`rsf_fixed_coset_eq_one` (the base point is the unique `P`-fixed coset).

Do it by strong induction on `orderOf x`, in two phases for each order `n`:

* phase 1 (`E` for elements of order `n`): for `z ∈ P` with `orderOf z = n` and `z ≠ 1`, rewrite
  `normalizerTransfer P z` with `MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot` (after
  `haveI : Fintype (MulAction.orbitRel.Quotient (↥(zpowers z)) (G ⧸ N)) := Fintype.ofFinite _`),
  split the product with `Finset.prod_filter_mul_prod_filter_not` along
  `fun q => Function.minimalPeriod (z • ·) q.out = 1`;
  * the `≠ 1` part is `phase1_mov` (available for any `n`), using only `F` for orders `< n`;
  * the `= 1` part is the product over the fixed cosets: prove the bijection
    `q ↦ q.out` from the fixed orbits onto the fixed cosets using `Finset.prod_bij`
    (`Function.minimalPeriod_eq_one_iff_isFixedPt`, `Quotient.out_eq'`), then split
    `Finset.univ.filter (fun c => z • c = c)` as `insert 1 (image (fun (p : ι × ZMod p) => e p.1 p.2))`
    using `rsf_block_decomposition` (with `hbase` from `P ≤ N` and `huniq` from
    `rsf_fixed_coset_eq_one`), and apply `rsf_regular_block_product` to each block — its hypothesis
    `hb` comes from `F` for `z ^ p` (whose order is `< n`, since `n` is a `p`-power and `z ≠ 1`);
    the base coset contributes `φ z`;
  * conclude with `Subgroup.index_eq_sum_minimalPeriod`, `Finset.prod_pow_eq_pow_sum` and
    `Finset.card_image`/`Finset.card_univ` (`Finset.card_filter_add_card_filter_not`): the count is
    `N.index = ∑_q m_q = (∑_{m_q ≠ 1} m_q) + 1 + p * Fintype.card ι`.
* phase 2 (`F` for elements of order `n`): immediate from phase 1 via `F_of_E`.

Finally `(key (orderOf x)).1 x hx rfl` gives the statement. -/
/-- **Huppert, *Endliche Gruppen I*, IV.8.3.**  For a *regular* Sylow `p`-subgroup `P` the transfer
of `G` into `N_G(P) ⧸ 𝔄` acts on `P` as the `[G : N_G(P)]`-th power map. -/
theorem normalizerTransfer_eq_pow (P : Sylow p G)
    (hreg : Work.SmallRank.IsRegular p ↥(P : Subgroup G)) :
    ∀ (x : G) (hx : x ∈ (P : Subgroup G)),
      normalizerTransfer P x =
        ((QuotientGroup.mk' (normalizerFocal P)) ⟨x, P.le_normalizer hx⟩) ^
          (sylowNormalizer P).index := by
  have key : ∀ n : ℕ,
      (∀ (z : G) (hz : z ∈ (P : Subgroup G)), orderOf z = n →
        normalizerTransfer P z =
          ((QuotientGroup.mk' (normalizerFocal P)) ⟨z, P.le_normalizer hz⟩) ^
            (sylowNormalizer P).index) ∧
      (∀ (z : G) (hz : z ∈ (P : Subgroup G)), orderOf z = n →
        ∀ (s : G) (hs : s⁻¹ * z * s ∈ sylowNormalizer P),
          (QuotientGroup.mk' (normalizerFocal P)) ⟨s⁻¹ * z * s, hs⟩ =
            (QuotientGroup.mk' (normalizerFocal P)) ⟨z, P.le_normalizer hz⟩) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have hE : ∀ (z : G) (hz : z ∈ (P : Subgroup G)), orderOf z = n →
          normalizerTransfer P z =
            ((QuotientGroup.mk' (normalizerFocal P)) ⟨z, P.le_normalizer hz⟩) ^
              (sylowNormalizer P).index := by
        intro z hz hzn
        classical
        by_cases hz1 : z = 1
        · subst hz1
          rw [normalizerTransfer, map_one]
          rw [show (QuotientGroup.mk' (normalizerFocal P))
              ⟨(1 : G), P.le_normalizer P.one_mem⟩ = 1 from map_one _, one_pow]
        rw [normalizerTransfer]
        obtain ⟨s, hs⟩ := P.isPGroup'.exists_orderOf_eq_pow (⟨z, hz⟩ : ↥(P : Subgroup G))
        have hzn' : n = p ^ s := by
          rw [← hzn]
          exact (show orderOf z = p ^ s by
            rw [show z = ((⟨z, hz⟩ : ↥(P : Subgroup G)) : G) from rfl, Subgroup.orderOf_coe, hs])
        have hs1 : 1 ≤ s := by
          rcases Nat.eq_zero_or_pos s with h0 | h0
          · exact absurd (orderOf_eq_one_iff.mp (by rw [hzn', h0, pow_zero] at hzn; exact hzn)) hz1
          · exact h0
        haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers z)
            (G ⧸ sylowNormalizer P))) := Fintype.ofFinite _
        haveI : Fintype (G ⧸ sylowNormalizer P) := Fintype.ofFinite _
        -- `F` holds for the element `z ^ p`, whose order is smaller
        have hordp : orderOf (z ^ p) < n := by
          have hdvd : orderOf (z ^ p) ∣ p ^ (s - 1) := by
            rw [orderOf_dvd_iff_pow_eq_one, ← pow_mul,
              show p * p ^ (s - 1) = p ^ s by rw [← pow_succ', Nat.sub_add_cancel hs1],
              ← hzn', ← hzn, pow_orderOf_eq_one]
          have hlt : p ^ (s - 1) < n := by
            rw [hzn']
            exact Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (Nat.sub_lt (by omega) (by omega))
          exact lt_of_le_of_lt (Nat.le_of_dvd (pow_pos (Fact.out : p.Prime).pos _) hdvd) hlt
        have hFp : ∀ (t : G) (ht : t⁻¹ * z ^ p * t ∈ sylowNormalizer P),
            (QuotientGroup.mk' (normalizerFocal P)) ⟨t⁻¹ * z ^ p * t, ht⟩ =
            (QuotientGroup.mk' (normalizerFocal P))
              ⟨z ^ p, P.le_normalizer (pow_mem hz p)⟩ :=
          fun t ht => ((ih (orderOf (z ^ p)) hordp).2 (z ^ p) (pow_mem hz p) rfl) t ht
        -- the transfer formula
        let F0 : Quotient (MulAction.orbitRel (Subgroup.zpowers z)
            (G ⧸ sylowNormalizer P)) → (↥(sylowNormalizer P) ⧸ normalizerFocal P) := fun q =>
          (QuotientGroup.mk' (normalizerFocal P))
            ⟨(Quotient.out q.out)⁻¹ * z ^ Function.minimalPeriod (z • ·) q.out * Quotient.out q.out,
              QuotientGroup.out_conj_pow_minimalPeriod_mem (sylowNormalizer P) z q.out⟩
        rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
        change (∏ q, F0 q) = _
        rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Quotient
          (MulAction.orbitRel (Subgroup.zpowers z) (G ⧸ sylowNormalizer P))))
          (fun q => Function.minimalPeriod (z • ·) q.out = 1) F0]
        -- the non-singleton orbits contribute `φ z ^ (sum of the orbit sizes)`
        have hmov := phase1_mov P n z hz hz1 hzn (fun k hk => (ih k hk).2)
        simp only [F0] at hmov
        -- the singleton orbits contribute `φ z ^ (number of fixed cosets)`
        have hsing : (∏ q ∈ (Finset.univ : Finset (Quotient (MulAction.orbitRel (Subgroup.zpowers z)
                (G ⧸ sylowNormalizer P)))).filter
              (fun q => Function.minimalPeriod (z • ·) q.out = 1), F0 q)
            = ((QuotientGroup.mk' (normalizerFocal P)) ⟨z, P.le_normalizer hz⟩) ^
              ((Finset.univ : Finset (Quotient (MulAction.orbitRel (Subgroup.zpowers z)
                (G ⧸ sylowNormalizer P)))).filter
                (fun q => Function.minimalPeriod (z • ·) q.out = 1)).card := by
          let gfix : (c : G ⧸ sylowNormalizer P) → (↥(sylowNormalizer P) ⧸ normalizerFocal P) :=
            fun c => if h : z • c = c then
              (QuotientGroup.mk' (normalizerFocal P))
                ⟨(Quotient.out c)⁻¹ * z * (Quotient.out c), mem_of_fixed P h⟩ else 1
          have hA : (∏ q ∈ (Finset.univ : Finset (Quotient (MulAction.orbitRel (Subgroup.zpowers z)
                (G ⧸ sylowNormalizer P)))).filter
                  (fun q => Function.minimalPeriod (z • ·) q.out = 1), F0 q)
              = ∏ c ∈ (Finset.univ : Finset (G ⧸ sylowNormalizer P)).filter (fun c => z • c = c),
                  gfix c := by
            refine Finset.prod_bij (fun q _ => q.out) ?_ ?_ ?_ ?_
            · intro q hq
              rw [Finset.mem_filter] at hq ⊢
              exact ⟨Finset.mem_univ _, by
                have := Function.minimalPeriod_eq_one_iff_isFixedPt.mp hq.2
                simpa only [Function.IsFixedPt] using this⟩
            · intro q₁ h₁ q₂ h₂ heq
              rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂, heq]
            · intro c hc
              rw [Finset.mem_filter] at hc
              have hout : (Quotient.mk'' c : Quotient (MulAction.orbitRel (Subgroup.zpowers z)
                  (G ⧸ sylowNormalizer P))).out = c := by
                have h1 : (MulAction.orbitRel (↥(Subgroup.zpowers z)) (G ⧸ sylowNormalizer P))
                    (Quotient.mk'' c).out c :=
                  Quotient.exact (Quotient.out_eq (Quotient.mk'' c))
                rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h1
                obtain ⟨x, hx⟩ := h1
                have hzstab : z ∈ MulAction.stabilizer G c :=
                  MulAction.mem_stabilizer_iff.mpr hc.2
                have h1 : (x : G) ∈ MulAction.stabilizer G c :=
                  Subgroup.zpowers_le.mpr hzstab x.2
                have hxc : x • c = c := by
                  show (x : G) • c = c
                  exact MulAction.mem_stabilizer_iff.mp h1
                rw [← hx, hxc]
              refine ⟨Quotient.mk'' c, ?_, hout⟩
              rw [Finset.mem_filter]
              exact ⟨Finset.mem_univ _, by
                have h1 : Function.IsFixedPt (z • ·) c := by
                  simpa only [Function.IsFixedPt] using hc.2
                rw [Function.minimalPeriod_eq_one_iff_isFixedPt, hout]
                exact h1⟩
            · intro q hq
              rw [Finset.mem_filter] at hq
              have hmp : Function.minimalPeriod (z • ·) q.out = 1 := hq.2
              show F0 q = gfix q.out
              dsimp only [F0, gfix]
              have hfixq : z • q.out = q.out := by
                have := Function.minimalPeriod_eq_one_iff_isFixedPt.mp hmp
                simpa only [Function.IsFixedPt] using this
              rw [dif_pos hfixq]
              have helem : (Quotient.out q.out)⁻¹ * z ^ Function.minimalPeriod (z • ·) q.out
                    * Quotient.out q.out
                  = (Quotient.out q.out)⁻¹ * z * Quotient.out q.out := by
                rw [hmp, pow_one]
              exact congrArg (QuotientGroup.mk' (normalizerFocal P)) (Subtype.ext helem)
          rw [hA]
          set β : G ⧸ sylowNormalizer P := ((1 : G) : G ⧸ sylowNormalizer P) with hβ
          have hbase : ∀ q : ↥(P : Subgroup G), q • β = β := by
            intro q
            have hq : (q : G) ∈ sylowNormalizer P := P.le_normalizer q.2
            change (((q : G) * 1 : G) : G ⧸ sylowNormalizer P) = ((1 : G) : G ⧸ sylowNormalizer P)
            rw [mul_one]
            exact (QuotientGroup.eq).mpr (by simpa using (sylowNormalizer P).inv_mem hq)
          obtain ⟨ι, hι, e, yy, hEinj, hycyc, hyp, hxfixB, hiff, hdisj⟩ :=
            rsf_block_decomposition (p := p) (Fact.out : p.Prime) (P.isPGroup') ⟨z, hz⟩ β hbase
              (fun a ha => rsf_fixed_coset_eq_one P a ha)
          haveI := hι
          have hCfix : (Finset.univ : Finset (G ⧸ sylowNormalizer P)).filter (fun c => z • c = c)
              = insert β (((Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset (ZMod p))).image
                  (fun q : ι × ZMod p => e q.1 q.2)) := by
            ext c
            rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_image]
            constructor
            · rintro ⟨-, hc⟩
              by_cases hcβ : c = β
              · exact Or.inl hcβ
              · obtain ⟨i, k, hik⟩ := (hiff c).mp ⟨hc, hcβ⟩
                exact Or.inr ⟨(i, k), by rw [Finset.mem_product]; exact ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hik⟩
            · rintro (rfl | ⟨q, hq, rfl⟩)
              · exact ⟨Finset.mem_univ _, hbase ⟨z, hz⟩⟩
              · rw [Finset.mem_product] at hq
                exact ⟨Finset.mem_univ _, ((hiff (e q.1 q.2)).mpr ⟨q.1, q.2, rfl⟩).1⟩
          have hβnotmem : β ∉ (((Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset (ZMod p))).image
              (fun q : ι × ZMod p => e q.1 q.2)) := by
            intro hmem
            rw [Finset.mem_image] at hmem
            obtain ⟨q, -, hq⟩ := hmem
            exact ((hiff β).mpr ⟨q.1, q.2, hq⟩).2 rfl
          have hinj : Function.Injective (fun q : ι × ZMod p => e q.1 q.2) := by
            rintro ⟨i, k⟩ ⟨j, l⟩ h
            obtain ⟨rfl, rfl⟩ := hdisj i k j l h
            rfl
          have hβval : gfix β = (QuotientGroup.mk' (normalizerFocal P))
              ⟨z, P.le_normalizer hz⟩ := by
            have hfixβ : z • β = β := hbase ⟨z, hz⟩
            have houtβ : (Quotient.out β)⁻¹ * z * (Quotient.out β) ∈ sylowNormalizer P :=
              mem_of_fixed P hfixβ
            have hmemβ : Quotient.out β ∈ sylowNormalizer P := by
              have h1 : (Quotient.out β)⁻¹ ∈ sylowNormalizer P := by
                have h2 := QuotientGroup.out_eq' β
                rw [hβ] at h2
                have h3 := (QuotientGroup.eq).mp h2
                simpa using h3
              simpa using (sylowNormalizer P).inv_mem h1
            have hconjβ : (⟨(Quotient.out β)⁻¹ * z * (Quotient.out β), houtβ⟩ : ↥(sylowNormalizer P))
                = (⟨Quotient.out β, hmemβ⟩ : ↥(sylowNormalizer P))⁻¹
                  * (⟨z, P.le_normalizer hz⟩ : ↥(sylowNormalizer P))
                  * (⟨Quotient.out β, hmemβ⟩ : ↥(sylowNormalizer P)) :=
              Subtype.ext rfl
            show gfix β = _
            dsimp only [gfix]
            rw [dif_pos hfixβ]
            rw [congrArg (QuotientGroup.mk' (normalizerFocal P)) hconjβ]
            simp only [map_mul, map_inv]
            rw [mul_comm ((QuotientGroup.mk' (normalizerFocal P))
                (⟨Quotient.out β, hmemβ⟩ : ↥(sylowNormalizer P)))⁻¹
              ((QuotientGroup.mk' (normalizerFocal P)) ⟨z, P.le_normalizer hz⟩),
              mul_assoc, inv_mul_cancel, mul_one]
          have hblock : ∀ i : ι, (∏ k : ZMod p, gfix (e i k)) = ((QuotientGroup.mk' (normalizerFocal P))
              ⟨z, P.le_normalizer hz⟩) ^ p := by
            intro i
            have hzpfix : ∀ k, z ^ p • e i k = e i k := by
              intro k
              have hgen : ∀ m : ℕ, z ^ m • e i k = e i k := by
                intro m
                induction m with
                | zero => simp
                | succ m ihm =>
                    rw [pow_succ, mul_smul,
                      show z • e i k = e i k from by
                        simpa only [Subgroup.smul_def] using hxfixB i k, ihm]
              exact hgen p
            have hgfix : ∀ k, gfix (e i k) = (QuotientGroup.mk' (normalizerFocal P))
                ⟨(Quotient.out (e i k))⁻¹ * z * (Quotient.out (e i k)),
                  mem_of_fixed P (hxfixB i k)⟩ := by
              intro k
              dsimp only [gfix]
              rw [dif_pos (by simpa only [Subgroup.smul_def] using hxfixB i k)]
            rw [Finset.prod_congr rfl (fun k _ => hgfix k)]
            refine rsf_regular_block_product P hreg (sylowNormalizer P)
              (QuotientGroup.mk' (normalizerFocal P)) z ((yy i : ↥(P : Subgroup G)) : G)
              hz (yy i).2 (P.le_normalizer hz)
              (fun k => e i k) (fun k => Quotient.out (e i k))
              (hEinj i) (fun k => QuotientGroup.out_eq' _) (fun k => hxfixB i k)
              (fun k => by
                show (((yy i : ↥(P : Subgroup G)) : G)) • e i k = e i (k + 1)
                simpa only [Subgroup.smul_def] using hycyc i k)
              (fun k => mem_of_fixed P (hxfixB i k))
              (fun k => by
                have hfac : ((QuotientGroup.mk' (normalizerFocal P))
                      ⟨(Quotient.out (e i k))⁻¹ * z * (Quotient.out (e i k)),
                        mem_of_fixed P (hxfixB i k)⟩) ^ p
                    = (QuotientGroup.mk' (normalizerFocal P))
                      ⟨(Quotient.out (e i k))⁻¹ * z ^ p * (Quotient.out (e i k)),
                        mem_of_fixed P (hzpfix k)⟩ := by
                  rw [← map_pow]
                  refine congrArg _ (Subtype.ext ?_)
                  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
                  rw [show (Quotient.out (e i k))⁻¹ * z * (Quotient.out (e i k))
                      = MulAut.conj (Quotient.out (e i k))⁻¹ z from by
                    rw [MulAut.conj_apply, inv_inv]]
                  rw [← map_pow, MulAut.conj_apply, inv_inv]
                rw [hfac, hFp (Quotient.out (e i k)) (mem_of_fixed P (hzpfix k)), ← map_pow]
                exact congrArg _ (Subtype.ext (by simp)))
          have hcardSing : ((Finset.univ : Finset (Quotient (MulAction.orbitRel (Subgroup.zpowers z)
                (G ⧸ sylowNormalizer P)))).filter
                (fun q => Function.minimalPeriod (z • ·) q.out = 1)).card
              = ((Finset.univ : Finset (G ⧸ sylowNormalizer P)).filter (fun c => z • c = c)).card := by
            refine Finset.card_bij (fun q _ => q.out) ?_ ?_ ?_
            · intro q hq
              rw [Finset.mem_filter] at hq ⊢
              exact ⟨Finset.mem_univ _, by
                have := Function.minimalPeriod_eq_one_iff_isFixedPt.mp hq.2
                simpa only [Function.IsFixedPt] using this⟩
            · intro q₁ h₁ q₂ h₂ heq
              rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂, heq]
            · intro c hc
              rw [Finset.mem_filter] at hc
              have hout : (Quotient.mk'' c : Quotient (MulAction.orbitRel (Subgroup.zpowers z)
                  (G ⧸ sylowNormalizer P))).out = c := by
                have h1 : (MulAction.orbitRel (↥(Subgroup.zpowers z)) (G ⧸ sylowNormalizer P))
                    (Quotient.mk'' c).out c :=
                  Quotient.exact (Quotient.out_eq (Quotient.mk'' c))
                rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h1
                obtain ⟨x, hx⟩ := h1
                have hzstab : z ∈ MulAction.stabilizer G c :=
                  MulAction.mem_stabilizer_iff.mpr hc.2
                have h1' : (x : G) ∈ MulAction.stabilizer G c :=
                  Subgroup.zpowers_le.mpr hzstab x.2
                have hxc : x • c = c := by
                  show (x : G) • c = c
                  exact MulAction.mem_stabilizer_iff.mp h1'
                rw [← hx, hxc]
              refine ⟨Quotient.mk'' c, ?_, hout⟩
              rw [Finset.mem_filter]
              exact ⟨Finset.mem_univ _, by
                have h1 : Function.IsFixedPt (z • ·) c := by
                  simpa only [Function.IsFixedPt] using hc.2
                rw [Function.minimalPeriod_eq_one_iff_isFixedPt, hout]
                exact h1⟩
          have hcardC : ((Finset.univ : Finset (G ⧸ sylowNormalizer P)).filter
              (fun c => z • c = c)).card = p * Fintype.card ι + 1 := by
            rw [hCfix, Finset.card_insert_of_notMem hβnotmem,
              Finset.card_image_of_injective _ hinj, Finset.card_product, Finset.card_univ,
              Finset.card_univ, ZMod.card, Nat.mul_comm (Fintype.card ι) p]
          calc ∏ c ∈ (Finset.univ : Finset (G ⧸ sylowNormalizer P)).filter (fun c => z • c = c), gfix c
              = gfix β * ∏ q ∈ ((Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset (ZMod p))),
                  gfix (e q.1 q.2) := by
                rw [hCfix, Finset.prod_insert hβnotmem,
                  Finset.prod_image (hinj.injOn)]
            _ = (QuotientGroup.mk' (normalizerFocal P)) ⟨z, P.le_normalizer hz⟩
                * ∏ i : ι, ∏ k : ZMod p, gfix (e i k) := by
                rw [hβval, Finset.prod_product]
            _ = (QuotientGroup.mk' (normalizerFocal P)) ⟨z, P.le_normalizer hz⟩
                * ∏ _i : ι, ((QuotientGroup.mk' (normalizerFocal P))
                    ⟨z, P.le_normalizer hz⟩) ^ p := by
                rw [Finset.prod_congr rfl (fun i _ => hblock i)]
            _ = (QuotientGroup.mk' (normalizerFocal P)) ⟨z, P.le_normalizer hz⟩
                * (((QuotientGroup.mk' (normalizerFocal P))
                    ⟨z, P.le_normalizer hz⟩) ^ p) ^ Fintype.card ι := by
                rw [Finset.prod_const, Finset.card_univ]
            _ = ((QuotientGroup.mk' (normalizerFocal P)) ⟨z, P.le_normalizer hz⟩)
                ^ (p * Fintype.card ι + 1) := by
                rw [← pow_mul, ← pow_succ']
            _ = ((QuotientGroup.mk' (normalizerFocal P)) ⟨z, P.le_normalizer hz⟩)
                ^ ((Finset.univ : Finset (Quotient (MulAction.orbitRel (Subgroup.zpowers z)
                    (G ⧸ sylowNormalizer P)))).filter
                    (fun q => Function.minimalPeriod (z • ·) q.out = 1)).card := by
                congr 1
                rw [hcardSing, hcardC]
        rw [hsing, hmov, ← pow_add]
        congr 1
        have hcard : ((Finset.univ : Finset (Quotient (MulAction.orbitRel (Subgroup.zpowers z)
              (G ⧸ sylowNormalizer P)))).filter
                (fun q => Function.minimalPeriod (z • ·) q.out = 1)).card
            = ∑ q ∈ (Finset.univ : Finset (Quotient (MulAction.orbitRel (Subgroup.zpowers z)
                (G ⧸ sylowNormalizer P)))).filter
                (fun q => Function.minimalPeriod (z • ·) q.out = 1),
              Function.minimalPeriod (z • ·) q.out := by
          rw [Finset.sum_congr rfl (fun q hq => (Finset.mem_filter.mp hq).2), Finset.sum_const]
          simp
        rw [hcard, Subgroup.index_eq_sum_minimalPeriod (sylowNormalizer P) z]
        rw [Finset.sum_filter_add_sum_filter_not
          (Finset.univ : Finset (Quotient (MulAction.orbitRel (Subgroup.zpowers z)
            (G ⧸ sylowNormalizer P))))
          (fun q => Function.minimalPeriod (z • ·) q.out = 1)
          (fun q => Function.minimalPeriod (z • ·) q.out)]
      exact ⟨hE, F_of_E_of_order P n hE⟩
  intro x hx
  exact (key (orderOf x)).1 x hx rfl

end Setup

theorem regular_sylow_fusion {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (P : Sylow p G) (hreg : Work.SmallRank.IsRegular p ↥(P : Subgroup G)) :
    (P : Subgroup G) ⊓ _root_.commutator G ≤
      ⁅Subgroup.normalizer (P : Set G), Subgroup.normalizer (P : Set G)⁆ := by
  haveI := Fact.mk hp
  intro x hx
  obtain ⟨hxP, hxG'⟩ := hx
  -- `x` lies in the kernel of the transfer into an abelian group
  have hker : x ∈ (normalizerTransfer P).ker :=
    Abelianization.commutator_subset_ker (normalizerTransfer P) hxG'
  rw [MonoidHom.mem_ker] at hker
  -- the crux
  have hpow := normalizerTransfer_eq_pow P hreg x hxP
  rw [hker] at hpow
  have hpow' : ((QuotientGroup.mk' (normalizerFocal P)) ⟨x, P.le_normalizer hxP⟩) ^
      (sylowNormalizer P).index = 1 := hpow.symm
  -- `p ∤ [G : N_G(P)]`
  have hnotdvd : ¬ p ∣ (sylowNormalizer P).index := by
    intro h
    refine Sylow.not_dvd_index P ?_
    rw [← Subgroup.relIndex_mul_index
      (le_normalizer : (P : Subgroup G) ≤ Subgroup.normalizer (P : Set G))]
    exact dvd_mul_of_dvd_right h _
  -- the image of `P` in `N ⧸ 𝔄` is a `p`-group, on which `y ↦ y ^ [G : N]` is injective
  let M : Subgroup (↥(sylowNormalizer P) ⧸ normalizerFocal P) :=
    (sylowInNormalizer P : Subgroup ↥(sylowNormalizer P)).map
      (QuotientGroup.mk' (normalizerFocal P))
  have hM : IsPGroup p ↥M := (sylowInNormalizer P).2.map _
  have hmemM : (QuotientGroup.mk' (normalizerFocal P)) ⟨x, P.le_normalizer hxP⟩ ∈ M :=
    Subgroup.mem_map.mpr ⟨⟨x, P.le_normalizer hxP⟩, mem_sylowInNormalizer P x hxP, rfl⟩
  have hone : (QuotientGroup.mk' (normalizerFocal P)) ⟨x, P.le_normalizer hxP⟩ = 1 := by
    have h2 : (⟨(QuotientGroup.mk' (normalizerFocal P)) ⟨x, P.le_normalizer hxP⟩, hmemM⟩ :
        ↥M) = 1 := by
      refine ((hM.powEquiv' hnotdvd).apply_eq_iff_eq (x := ⟨_, hmemM⟩) (y := 1)).mp ?_
      simpa using hpow'
    exact congrArg Subtype.val h2
  -- hence `x ∈ 𝔄 ⊓ P`, the focal subgroup of `P` in `N_G(P)`
  have hxA : (⟨x, P.le_normalizer hxP⟩ : ↥(sylowNormalizer P)) ∈ normalizerFocal P := by
    have := MonoidHom.mem_ker.mpr hone
    rwa [QuotientGroup.ker_mk'] at this
  have hfoc : (⟨x, P.le_normalizer hxP⟩ : ↥(sylowNormalizer P)) ∈
      (sylowInNormalizer P).focalSubgroup := by
    rw [← ker_transferFocal_inf_eq_focalSubgroup (sylowInNormalizer P)]
    exact ⟨hxA, mem_sylowInNormalizer P x hxP⟩
  have hfin : (⟨x, P.le_normalizer hxP⟩ : ↥(sylowNormalizer P)) ∈
      _root_.commutator ↥(sylowNormalizer P) :=
    Subgroup.focalSubgroup_le_commutator
      (sylowInNormalizer P : Subgroup ↥(sylowNormalizer P)) hfoc
  have htop : (⊤ : Subgroup ↥(sylowNormalizer P)).map (sylowNormalizer P).subtype =
      (sylowNormalizer P) := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hmap : (_root_.commutator ↥(sylowNormalizer P)).map (sylowNormalizer P).subtype =
      ⁅Subgroup.normalizer (P : Set G), Subgroup.normalizer (P : Set G)⁆ := by
    have h : _root_.commutator ↥(sylowNormalizer P) =
        ⁅(⊤ : Subgroup ↥(sylowNormalizer P)), ⊤⁆ := rfl
    rw [h, Subgroup.map_commutator]
    exact congrArg₂ (fun a b => ⁅a, b⁆) htop htop
  rw [← hmap]
  exact Subgroup.mem_map.mpr ⟨_, hfin, rfl⟩

end Work.LocalPrelim
