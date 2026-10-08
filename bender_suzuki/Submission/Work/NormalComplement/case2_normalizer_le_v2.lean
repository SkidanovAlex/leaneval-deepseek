/-
# Chapter III §2 (case 2): the normaliser of a three-point-fixing `U` lies in the subgroup
built from the "rank-one" subgroup `S` supplied by Ch. II §4 Prop. 3.

This is the "case 2" step of the minimal-counterexample argument of Peterfalvi I Ch. III §2
(p.175–176).  Compared with `Work.NormalComplement.case2_normalizer_le` this version takes the
extra hypotheses `ChIIFourP3SubnormalProp` (`hP3`) and `KInvariantUnderD H t` (`hKinv`), and
accordingly routes through the blue-print-faithful `Work.NormalComplement.case2_prop3b_v2`
(instead of the unproved `case2_prop3b`).  The subsequent assembly is identical.

## The mathematics

`U ≤ W ⊓ D` with `D = H ∩ H^t` and `3 ≤ |Fix(U)|`.  Ch. II §4 Prop. 3 (`case2_prop3b_v2`) applied
to the pair `X = U`, `Y = U₁` (where `U₁ ≤ U` is a nontrivial subgroup normalised by a nontrivial
`k ∈ Kset D t`, as supplied by `hcase2`) produces a `2`-subgroup `S ≤ H ⊓ C_G(U)` with

  `H ⊓ N_G(U) = S ⊔ (D ⊓ N_G(U))`   and   `H ⊓ N_G(U) ≤ N_G(S)`.

Since `S ≤ H` and the index `[H : W]` is odd (`W ⊴ H`, `H = W ⊔ D` with `D` of odd order), `S ≤ W`;
as `p` is odd and `S` is a normal `2`-subgroup of `C_W(U)`, actually `S ≤ O_{p'}(C_W(U))`.  The
modular identity `(S ⊔ M) ⊓ W ≤ S ⊔ (M ⊓ W)` (valid because `S ≤ W` and `S ⊔ M ≤ N_G(S)`) then
places every element of `N_G(U) ⊓ W` in `O_{p'}(C_W(U)) ⊔ (N_G(U) ⊓ (W ⊓ D))`, which is the claim.
-/
import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.Prelim
import Submission.Work.NormalComplement.prop2b_conj_into_centD
import Submission.Work.NormalComplement.IsSubnormalInPgroup
import Submission.Work.NormalComplement.case1_normalizer_le
import Submission.Work.NormalComplement.case2_prop3b_v2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-! ## Elementary subgroup bookkeeping for the Case-2 assembly -/

/-- `|A ⊔ B| · |A ⊓ B| = |A| · |B|` when `B` is normal in the ambient group. -/
private lemma card_sup_mul_card_inf_aux {G : Type*} [Group G] {A B : Subgroup G} [B.Normal] :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hcard : ∀ {H K : Subgroup G}, Nat.card ↥(H.subgroupOf K) = Nat.card ↥(H ⊓ K) := by
    intro H K
    rw [← Subgroup.inf_subgroupOf_right H K]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := H ⊓ K) (K := K) inf_le_right).toEquiv
  have h1 : Nat.card ↥(A ⊔ B) = B.relIndex A * Nat.card ↥B := by
    rw [← Subgroup.index_mul_card (B.subgroupOf (A ⊔ B)),
      show (B.subgroupOf (A ⊔ B)).index = B.relIndex A from
        Subgroup.relIndex_sup_right (H := A) (K := B),
      hcard (H := B) (K := A ⊔ B), inf_of_le_left le_sup_right]
  have h2 : Nat.card ↥A = B.relIndex A * Nat.card ↥(A ⊓ B) := by
    rw [← Subgroup.index_mul_card (B.subgroupOf A),
      show (B.subgroupOf A).index = B.relIndex A from rfl,
      hcard (H := B) (K := A), inf_comm]
  rw [h1, h2]; ring

/-- `|A ⊔ B| · |A ⊓ B| = |A| · |B|` when `A ⊔ B ≤ N_G(B)`. -/
private lemma card_sup_mul_card_inf_of_le_normalizer {G : Type*} [Group G] (A B : Subgroup G)
    (h : A ⊔ B ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hB : (B.subgroupOf (A ⊔ B)).Normal := Subgroup.normal_subgroupOf_of_le_normalizer h
  have key : Nat.card ↥(A.subgroupOf (A ⊔ B) ⊔ B.subgroupOf (A ⊔ B)) *
      Nat.card ↥(A.subgroupOf (A ⊔ B) ⊓ B.subgroupOf (A ⊔ B)) =
      Nat.card ↥(A.subgroupOf (A ⊔ B)) * Nat.card ↥(B.subgroupOf (A ⊔ B)) :=
    card_sup_mul_card_inf_aux (G := ↥(A ⊔ B)) (A := A.subgroupOf (A ⊔ B))
      (B := B.subgroupOf (A ⊔ B))
  rw [← Subgroup.subgroupOf_sup (A := A) (A' := B) (B := A ⊔ B) le_sup_left le_sup_right,
      Subgroup.subgroupOf_self, Subgroup.card_top] at key
  have hinf : A.subgroupOf (A ⊔ B) ⊓ B.subgroupOf (A ⊔ B) = (A ⊓ B).subgroupOf (A ⊔ B) := by
    ext x; simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have hAB : Nat.card ↥((A ⊓ B).subgroupOf (A ⊔ B)) = Nat.card ↥(A ⊓ B) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans le_sup_left)).toEquiv
  have hA : Nat.card ↥(A.subgroupOf (A ⊔ B)) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  have hBB : Nat.card ↥(B.subgroupOf (A ⊔ B)) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [hinf, hAB, hA, hBB] at key
  exact key

/-- `(W.subgroupOf H).index * |W| = |H|` for `W ≤ H`. -/
private lemma index_subgroupOf_mul_card {G : Type*} [Group G] {W H : Subgroup G} (hWH : W ≤ H) :
    (W.subgroupOf H).index * Nat.card ↥W = Nat.card ↥H := by
  have h := Subgroup.index_mul_card (W.subgroupOf H)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWH).toEquiv] at h
  exact h

/-- The index of `W` in `H` is odd when `W ⊴ H` and `H = W ⊔ D` with `D` of odd order. -/
private lemma odd_index_subgroupOf {G : Type*} [Group G] [Finite G] {W D H : Subgroup G}
    (hWH : W ≤ H) (hn : H ≤ Subgroup.normalizer (W : Set G)) (hsup : W ⊔ D = H)
    (hDodd : Odd (Nat.card ↥D)) : Odd (W.subgroupOf H).index := by
  have hcard : Nat.card ↥(D ⊔ W) * Nat.card ↥(D ⊓ W) = Nat.card ↥D * Nat.card ↥W :=
    card_sup_mul_card_inf_of_le_normalizer D W (by rw [sup_comm, hsup]; exact hn)
  rw [sup_comm, hsup] at hcard
  have hidx := index_subgroupOf_mul_card hWH
  have hkey : (W.subgroupOf H).index * Nat.card ↥(D ⊓ W) = Nat.card ↥D := by
    have h1 : (W.subgroupOf H).index * Nat.card ↥(D ⊓ W) * Nat.card ↥W =
        (W.subgroupOf H).index * Nat.card ↥W * Nat.card ↥(D ⊓ W) := by ring
    have h2 : (W.subgroupOf H).index * Nat.card ↥W * Nat.card ↥(D ⊓ W) =
        Nat.card ↥D * Nat.card ↥W := by rw [hidx, hcard]
    exact Nat.mul_right_cancel (Nat.card_pos (α := ↥W)) (h1.trans h2)
  exact hDodd.of_dvd_nat ⟨Nat.card ↥(D ⊓ W), hkey.symm⟩

/-- A finite `2`-subgroup whose index is odd lies in the subgroup. -/
private lemma isPGroup_two_le_of_odd_index {G : Type*} [Group G] [Finite G]
    {S W H : Subgroup G} (hS2 : IsPGroup 2 S) (hSH : S ≤ H) (hWH : W ≤ H)
    (hn : H ≤ Subgroup.normalizer (W : Set G)) (hodd : Odd (W.subgroupOf H).index) :
    S ≤ W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hWn : (W.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hn
  intro s hs
  have hsH : s ∈ H := hSH hs
  let s' : ↥H := ⟨s, hsH⟩
  let q : ↥H →* (↥H ⧸ W.subgroupOf H) := QuotientGroup.mk' (W.subgroupOf H)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS2) (⟨s, hs⟩ : ↥S)
  have hdiv : orderOf s' ∣ orderOf (⟨s, hs⟩ : ↥S) :=
    orderOf_map_dvd (Subgroup.inclusion hSH) (⟨s, hs⟩ : ↥S)
  have h2 : orderOf (q s') ∣ 2 ^ k := by
    have h := orderOf_map_dvd q s'
    rw [hk] at hdiv
    exact h.trans hdiv
  have h3 : orderOf (q s') ∣ (W.subgroupOf H).index := by
    rw [Subgroup.index_eq_card (W.subgroupOf H)]
    exact orderOf_dvd_natCard (q s')
  have hcop : Nat.Coprime (2 ^ k) (W.subgroupOf H).index :=
    (Nat.coprime_two_left.mpr hodd).pow_left k
  have hone : orderOf (q s') = 1 := by
    have hg := Nat.dvd_gcd h2 h3
    rw [hcop.gcd_eq_one] at hg
    exact Nat.dvd_one.mp hg
  rw [orderOf_eq_one_iff] at hone
  have hmem : s' ∈ W.subgroupOf H := by
    rw [← QuotientGroup.eq_one_iff (N := W.subgroupOf H) s', ← QuotientGroup.mk'_apply]
    exact hone
  exact hmem

/-- A normal `2`-subgroup of a group, `p` odd, lies in the `p'`-core. -/
private lemma isPGroup_two_le_pPrimeCoreSub {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hpodd : Odd p) {S X : Subgroup G} (hSX : S ≤ X) (hS2 : IsPGroup 2 S)
    (hSn : X ≤ Subgroup.normalizer (S : Set G)) : S ≤ pPrimeCoreSub p X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (S.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hSn
  have hcardS : Nat.card ↥(S.subgroupOf X) = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv
  have hcop : Nat.Coprime (Nat.card ↥(S.subgroupOf X)) p := by
    rw [hcardS]
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hS2
    rw [hm]
    exact (Nat.coprime_two_left.mpr hpodd).pow_left m
  have hle : S.subgroupOf X ≤ Submission.Blueprint.pPrimeCore p ↥X :=
    le_sSup ⟨inferInstance, hcop⟩
  calc S = (S.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hSX).symm
    _ ≤ (Submission.Blueprint.pPrimeCore p ↥X).map X.subtype := Subgroup.map_mono hle
    _ = pPrimeCoreSub p X := rfl

/-- An element of `S ⊔ M`, with `S` normalised by the join, is a product `s * m`. -/
private lemma mem_sup_iff_exists_mul_of_le_normalizer {G : Type*} [Group G] {S M : Subgroup G}
    (h : S ⊔ M ≤ Subgroup.normalizer (S : Set G)) {x : G} :
    x ∈ S ⊔ M ↔ ∃ s ∈ S, ∃ m ∈ M, s * m = x := by
  constructor
  · intro hx
    haveI : (S.subgroupOf (S ⊔ M)).Normal := Subgroup.normal_subgroupOf_of_le_normalizer h
    have hmem : (⟨x, hx⟩ : ↥(S ⊔ M)) ∈
        S.subgroupOf (S ⊔ M) ⊔ M.subgroupOf (S ⊔ M) := by
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
      trivial
    rw [Subgroup.mem_sup_of_normal_left] at hmem
    obtain ⟨y, hy, z, hz, hyz⟩ := hmem
    refine ⟨(y : G), Subgroup.mem_subgroupOf.mp hy, (z : G), Subgroup.mem_subgroupOf.mp hz, ?_⟩
    have h2 := congrArg (fun w : ↥(S ⊔ M) => (w : G))
      (show (y : ↥(S ⊔ M)) * (z : ↥(S ⊔ M)) = (⟨x, hx⟩ : ↥(S ⊔ M)) from hyz)
    simpa using h2
  · rintro ⟨s, hs, m, hm, rfl⟩
    exact Subgroup.mul_mem_sup hs hm

/-- Modular inequality for subgroups: `(S ⊔ M) ⊓ W ≤ S ⊔ (M ⊓ W)` for `S ≤ W`. -/
private lemma inf_sup_le_of_le_left {G : Type*} [Group G] {S M W : Subgroup G}
    (hS : S ≤ W) (hN : S ⊔ M ≤ Subgroup.normalizer (S : Set G)) :
    (S ⊔ M) ⊓ W ≤ S ⊔ M ⊓ W := by
  intro x hx
  obtain ⟨hxSM, hxW⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨s, hs, m, hm, rfl⟩ := (mem_sup_iff_exists_mul_of_le_normalizer hN).mp hxSM
  have hmW : m ∈ W := by
    have h1 : s⁻¹ * (s * m) ∈ W := W.mul_mem (W.inv_mem (hS hs)) hxW
    simpa using h1
  exact Subgroup.mul_mem_sup hs (Subgroup.mem_inf.mpr ⟨hm, hmW⟩)

variable {G : Type} [Group G] [Finite G]

theorem case2_normalizer_le_v2 (G : Type) [Group G] [Finite G]
    (hS : Submission.Blueprint.Situation G) (hBP : Work.NormalComplement.BenderPrelimProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    {t : G} (ht : orderOf t = 2) (htH : t ∉ H)
    {W : Subgroup G} (hW : W ≤ H) (hn : H ≤ Subgroup.normalizer (W : Set G))
    (hsup : W ⊔ Submission.Blueprint.twoPoint H t = H)
    (hKinv : Work.NormalComplement.KInvariantUnderD H t)
    {p : ℕ} (hp : p.Prime) {U : Subgroup G}
    (hUE : U ≤ W ⊓ Submission.Blueprint.twoPoint H t) (hUp : IsPGroup p U)
    (h3 : 3 ≤ (Submission.Blueprint.fixedPts H U).ncard)
    (hcase2 : ∃ U₁ : Subgroup G, U₁ ≤ U ∧ U₁ ≠ ⊥ ∧
        ∃ k ∈ Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
          ∀ u ∈ U₁, k * u = u * k) :
    Subgroup.normalizer (U : Set G) ⊓ W ≤
      Work.NormalComplement.pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ⊔
        (Subgroup.normalizer (U : Set G) ⊓ (W ⊓ Submission.Blueprint.twoPoint H t)) := by
  obtain ⟨U₁, hU1U, hU1ne, k, hkK, hkne, hkcomm⟩ := hcase2
  haveI : Fact p.Prime := ⟨hp⟩
  -- `U ≤ D` and `D` has odd order
  have hUD : U ≤ Submission.Blueprint.twoPoint H t := hUE.trans inf_le_right
  have hDodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) := hH.2.2 t htH
  -- `U ≠ ⊥`, hence `p` is odd
  have hUne : U ≠ ⊥ := fun h => hU1ne (le_bot_iff.mp (by rw [h] at hU1U; exact hU1U))
  have hUD_dvd : Nat.card ↥U ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUD).toEquiv]
    exact Subgroup.card_subgroup_dvd_card (U.subgroupOf (Submission.Blueprint.twoPoint H t))
  have hpU : p ∣ Nat.card ↥U := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hUp
    cases n with
    | zero => exact absurd (Subgroup.card_eq_one.mp hn) hUne
    | succ n => exact ⟨p ^ n, by rw [hn, pow_succ, mul_comm]⟩
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd (even_iff_two_dvd.mpr (h ▸ (hpU.trans hUD_dvd)))
        (Nat.not_even_iff_odd.mpr hDodd)
    · exact h
  -- apply the blue-print-faithful Prop. 3(b) at `X = U`, `Y = U₁`
  have hkU1 : k ∈ Subgroup.normalizer (U₁ : Set G) :=
    Subgroup.centralizer_le_normalizer (U₁ : Set G)
      (Subgroup.mem_centralizer_iff.mpr (fun u hu => (hkcomm u hu).symm))
  obtain ⟨S, hS2, hSHc, hSD, hSN, hSsup⟩ :=
    case2_prop3b_v2 G hS hBP hC4 hP3 hH ht htH hKinv hUD hUp h3 hU1U hU1ne
      ⟨k, hkK, hkne, hkU1⟩
  -- `S ≤ W`
  have hSH : S ≤ H := hSHc.trans inf_le_left
  have hSC : S ≤ Subgroup.centralizer (U : Set G) := hSHc.trans inf_le_right
  have hSleW : S ≤ W :=
    isPGroup_two_le_of_odd_index hS2 hSH hW hn
      (odd_index_subgroupOf hW hn hsup hDodd)
  -- `S ≤ O_{p'}(C_W(U))`
  have hCWin : Subgroup.centralizer (U : Set G) ⊓ W ≤ Subgroup.normalizer (U : Set G) ⊓ H :=
    le_inf (inf_le_left.trans (Subgroup.centralizer_le_normalizer (U : Set G)))
      (inf_le_right.trans hW)
  have hSn : Subgroup.centralizer (U : Set G) ⊓ W ≤ Subgroup.normalizer (S : Set G) :=
    hCWin.trans hSN
  have hSpc : S ≤ pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) :=
    isPGroup_two_le_pPrimeCoreSub hp hpodd (le_inf hSC hSleW) hS2 hSn
  -- assembly
  have hNsup : S ⊔ (Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (U : Set G)) ≤
      Subgroup.normalizer (S : Set G) := by
    rw [← hSsup, inf_comm]
    exact hSN
  have hmod : Subgroup.normalizer (U : Set G) ⊓ W ≤
      S ⊔ (Subgroup.normalizer (U : Set G) ⊓ (W ⊓ Submission.Blueprint.twoPoint H t)) := by
    refine (le_inf (le_inf (inf_le_right.trans hW) inf_le_left) inf_le_right).trans ?_
    rw [hSsup]
    refine (inf_sup_le_of_le_left hSleW hNsup).trans ?_
    rw [show (Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (U : Set G)) ⊓ W
        = Subgroup.normalizer (U : Set G) ⊓ (W ⊓ Submission.Blueprint.twoPoint H t) from by
      ac_rfl]
  exact hmod.trans (sup_le (hSpc.trans le_sup_left) le_sup_right)

end Work.NormalComplement
