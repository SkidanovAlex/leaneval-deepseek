
/-
# PORT NOTE (S5K): verbatim copy of `NC4/prop2cd.lean` into the `sec4_P2d` world.

`Work.NormalComplement.normalizedBy_twoPoint` is defined both in
`Submission/Work/NormalComplement/sec2_one.lean` and in
`Submission/Work/NormalComplement/sec4_P2d.lean`, so Lean refuses to have both modules in one
environment.  The §4 chain `NC4.prop2cd` sits in the `sec2_one` world, while §4 Prop. 2 (b)
(`NC4.prop2b`) sits in the `sec4_P2d` world, and the assembly of `Setup5` needs both.  This file is
the copy of `NC4/prop2cd.lean` relocated to the `sec4_P2d` world; only the imports are changed (they point at
the other copies in `S5K/`), the mathematics is untouched.
-/
/-
# Ch. III §4 Proposition 2 (c), (d): `|K| = r^a (2^p - 1)` and `F(V) = E' ⊓ V`

This module proves `Work.NormalComplement.NC4.prop2cd`, Peterfalvi I Ch. III §4 Proposition 2
(c), (d) (p.181): there are a prime `r` and `a ≥ 1` with `r ∣ 2^p - 1`, `|K| = r^a (2^p - 1)`, and
`F(V) = E' ⊓ V` is an `r`-Sylow subgroup of `V` (in particular nontrivial).

The inputs are the four preceding steps of §4 (`Lemma1dConc`, `Prop1Conc`, `Prop2aConc`,
`Prop2bConc`), all of which are hypotheses of the statement.

Route, in the paper's notation (`D = twoPoint H t`, `V = centD H t`, `K = Kset D t`,
`E = Egrp H t W`, `E' = Ecomm H t W`, `R = E' ⊓ V = ⁅A,P⁆`, `C = A ⊓ C_G(P)`):

* **(c), `prop2c_step`.**  Fix a prime `q` and a nonzero `P`-invariant `q`-subgroup `Q ≤ A` with
  `Q ≤ E'`.  By `Prop2b` (`E'` nilpotent, same primes as `|K|`) there is a `q`-split
  `E' = S ⊔ T` with `S` a `q`-group, `q ∤ |T|`, `S,T` commuting and `t`-invariant
  (`nilpotent_split`).  Then `Q ≤ S`, `Kset T t ⊆ C_G(Q)`, and the two `ncard` identities of
  `kset_decomp` give `|K| * |C_{K₁}(Q)| = |K₁| * |C_K(Q)|` with `K₁ = Kset S t`,
  `|C_K(Q)| = |C_K(A)| = 2^p - 1` (`Setup45A.A_B` and `Setup45A.A_CK`).  Both `|K₁| = q^b` and
  `|C_{K₁}(Q)| = q^c` are powers of `q`, `q ∤ |Kset T t|`, and
  * `b ≥ 1` because `q ∣ |K|` (`Prop2b`) and `q ∤ |Kset T t|`;
  * `c ≥ 1` because `Z(S) ≠ 1` is contained in `C_S(Q)` while `Z(S) ∩ V = 1` (a central element of
    `S` centralises `S` and commutes with `T`, hence centralises `K ⊆ E'`, while `C_V(K) = 1` is
    hypothesis (D2)) — so `C_S(Q) ⊄ V` and `|C_{K₁}(Q)| = |C_S(Q) : C_S(Q) ⊓ V| > 1`;
  * `c < b` since `c = b` would force `Q` to centralise `K₁` and `K₂`, hence `K`, contradicting
    `C_V(K) = 1` and `Q ≠ 1`.
  Then `2^p - 1 = q^c |K₂|` gives `q ∣ 2^p - 1` and `|K| = q^{b-c} (2^p - 1)` with `b - c ≥ 1`.
* **(d), `prop2d_step`.**  Applying (c) to a Sylow `q`-subgroup of `R` and to a second prime shows
  that `|R|` has a single prime divisor `q`, so `R` is a `q`-group; `q ∤ |C_A(P)|` (else
  `Prop1Conc`'s `π`-property would give `q ∤ |K|`), so `|V| = |R| p |C_A(P)|` (`card_centD`) has
  `q`-part `|R|`: `R` is the Sylow `q` of `V`.  `F(V) ≤ A`, so `F(V) = R × Q` with `Q ≤ C_A(P)`;
  if `Q ≠ 1`, an `s`-subgroup `Q_s` of `Q` has `s ∤ |E'|` (the `π`-property again) and centralises
  `C_S(R) = Z(R)·C_{K₁}(R)` (App. I (1)(b) applied to the `t`-invariant subgroup `C_S(R)`), so
  Thompson's `P × Q` lemma (`centralizer_of_fixed`) makes `Q_s` centralise `S`, hence `K₁`, and
  `Q_s ≤ C_A(P)` centralises `K₂`: then `Q_s ≤ C_V(K) = 1`, a contradiction.
-/
import Mathlib
import Submission.Work.NormalComplement.NC4.Defs
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.appI_one
import Submission.Work.NormalComplement.sec4_one_c
import Submission.Work.NormalComplement.card_sup_mul_card_inf
import Submission.Work.Fitting.fitting_isNilpotent
import Submission.Work.Fitting.Defs
import Submission.Work.NormalComplement.NC4.nilpotent_split
import Submission.Work.NormalComplement.NC4.kset_decomp
import Submission.Work.NormalComplement.NC4.centralizer_of_fixed
import Submission.Work.Coprime.thompson_PxQ
import Submission.Work.Frobenius.Fpf.Basic
import Submission.Work.NormalComplement.S5K.sec2_lemma1_w2
import Submission.Work.NormalComplement.S5K.card_centD_w2
import Submission.Work.NormalComplement.S5K.prop2d_step_w2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement.NC4

variable {G : Type} [Group G] [Finite G]

/-! ## Auxiliary group theory -/

/-- `Kset` is monotone in the subgroup. -/
lemma kset_mono {D₁ D₂ : Subgroup G} (h : D₁ ≤ D₂) (t : G) : Kset D₁ t ⊆ Kset D₂ t :=
  fun _ hx => ⟨h hx.1, hx.2⟩

/-- If `Kset D t ⊆ X` and `X ≤ D`, then `Kset X t = Kset D t`. -/
lemma kset_eq_of_subset {D X : Subgroup G} {t : G} (hXD : X ≤ D)
    (h : Kset D t ⊆ (X : Set G)) : Kset X t = Kset D t := by
  refine Set.Subset.antisymm (fun z hz => ⟨hXD hz.1, hz.2⟩) fun z hz => ⟨h hz, hz.2⟩

/-- Peterfalvi, Appendix I (1)(a): `|Kset X t|` is the index of `C_X(t)` in `X`. -/
lemma kset_ncard_eq_index {X : Subgroup G} {t : G} (ht : orderOf t = 2)
    (htX : NormalizedBy t X) (hodd : Odd (Nat.card ↥X)) :
    (Kset X t).ncard = ((Subgroup.centralizer ({t} : Set G) ⊓ X).subgroupOf X).index := by
  have hcop : (Nat.card ↥X).Coprime 2 := Nat.coprime_two_right.mpr hodd
  have h1 : Kapp t X = Kset X t := ((appI_one (d := 2) Nat.prime_two ht htX hcop).2 rfl).1
  rw [← h1]
  exact appI_kapp_ncard t X

/-- Consequently `|Kset X t|` divides `|X|`. -/
lemma kset_ncard_dvd {X : Subgroup G} {t : G} (ht : orderOf t = 2)
    (htX : NormalizedBy t X) (hodd : Odd (Nat.card ↥X)) :
    (Kset X t).ncard ∣ Nat.card ↥X := by
  rw [kset_ncard_eq_index ht htX hodd]
  exact Subgroup.index_dvd_card _

/-- If `S ⊔ T = E` with `S ⊓ T = ⊥` and `E ≤ N(S)`, then every element of `E` is a product
`s * u` with `s ∈ S`, `u ∈ T`. -/
lemma exists_mul_mem_of_sup_eq {E S T : Subgroup G} (hS : S ≤ E) (hT : T ≤ E)
    (hsup : S ⊔ T = E) (hN : E ≤ Subgroup.normalizer (S : Set G)) :
    ∀ z ∈ E, ∃ s ∈ S, ∃ u ∈ T, z = s * u := by
  intro z hz
  haveI : (S.subgroupOf E).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
  have htop : (S.subgroupOf E) ⊔ (T.subgroupOf E) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hS hT, hsup]
    exact Subgroup.subgroupOf_eq_top.mpr le_rfl
  have hmul : (((S.subgroupOf E) ⊔ (T.subgroupOf E) : Subgroup ↥E) : Set ↥E) =
      ((S.subgroupOf E : Set ↥E) * (T.subgroupOf E : Set ↥E)) := Subgroup.normal_mul _ _
  have hz' : (⟨z, hz⟩ : ↥E) ∈ (((S.subgroupOf E) ⊔ (T.subgroupOf E) : Subgroup ↥E) : Set ↥E) := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [hmul, Set.mem_mul] at hz'
  obtain ⟨a, ha, b, hb, hab⟩ := hz'
  exact ⟨(a : G), ha, (b : G), hb, by simpa using (congrArg Subtype.val hab).symm⟩

/-- If `E = S ⊔ T` with `S ⊓ T = ⊥`, `E ≤ N(S)`, `S` and `T` commuting and `T` a `q'`-group,
then every element of `E` of `q`-power order lies in `S` (used to see that the `q`-part of a
`P`-invariant subgroup of `E` meets the `q`-Sylow `S` nontrivially). -/
lemma mem_of_pow_eq_one_of_isPGroup {E S T : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hS_le : S ≤ E) (hT_le : T ≤ E) (hST_sup : S ⊔ T = E) (hST_inf : S ⊓ T = ⊥)
    (hST_comm : ∀ s ∈ S, ∀ u ∈ T, s * u = u * s)
    (hE_le_NS : E ≤ Subgroup.normalizer (S : Set G)) (hqT : ¬ q ∣ Nat.card ↥T) :
    ∀ x ∈ E, (∃ k, x ^ q ^ k = 1) → x ∈ S := by
  have hsplit := exists_mul_mem_of_sup_eq hS_le hT_le hST_sup hE_le_NS
  have hT_q' : ∀ u ∈ T, ¬ q ∣ orderOf u := by
    intro u hu hdvd
    have h1 : orderOf (⟨u, hu⟩ : ↥T) ∣ Nat.card ↥T := orderOf_dvd_natCard _
    have h2 : orderOf u = orderOf (⟨u, hu⟩ : ↥T) :=
      orderOf_injective T.subtype T.subtype_injective ⟨u, hu⟩
    rw [h2] at hdvd
    exact hqT (hdvd.trans h1)
  intro x hx hxk
  obtain ⟨s, hs, u, hu, hsu⟩ := hsplit x hx
  obtain ⟨k, hk⟩ := hxk
  have hpow : x ^ q ^ k = s ^ q ^ k * u ^ q ^ k := by
    rw [hsu]
    exact Commute.mul_pow (show Commute s u from hST_comm s hs u hu) _
  rw [hpow] at hk
  have hs_bot : s ^ q ^ k = 1 := by
    have hsT : s ^ q ^ k = (u ^ q ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hk
    have hmem : s ^ q ^ k ∈ S ⊓ T := ⟨S.pow_mem hs _, by
      rw [hsT]
      exact T.inv_mem (T.pow_mem hu _)⟩
    rw [hST_inf] at hmem
    simpa using hmem
  have hu_pow : u ^ q ^ k = 1 := by
    rw [hs_bot, one_mul] at hk
    exact hk
  have hu1 : u = 1 := by
    rcases (Nat.dvd_prime_pow hq).mp ((orderOf_dvd_iff_pow_eq_one).mpr hu_pow) with ⟨j, -, hj⟩
    have hord : orderOf u = 1 := by
      by_cases hj0 : j = 0
      · rw [hj, hj0, pow_zero]
      · exfalso
        refine hT_q' u hu ?_
        rw [hj]
        exact ⟨q ^ (j - 1), by
          rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hj0)]⟩
    rwa [orderOf_eq_one_iff] at hord
  rw [hsu, hu1, mul_one]
  exact hs

/-! ## Proposition 2 (c): `|K| = r^a (2^p - 1)` -/

/-- **Ch. III §4 Prop. 2 (c)**, in the form used below.  Given the `q`-split `E' = S ⊔ T`
(`S` a `q`-group, `q ∤ |T|`, `S ⊓ T = ⊥`, elements commuting, `t`-invariant) and a nonzero
`P`-invariant `q`-subgroup `Q ≤ S` with `Q ≤ A`, one has `q ∣ 2^p - 1` and
`|K| = q^a (2^p - 1)` with `a ≥ 1`. -/
theorem prop2c_step {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (h : Design.Setup45A G H t W p P A)
    (h2a : Prop2aConc H t W p P A) (h2b : Prop2bConc H t W p P A)
    (q : ℕ) (hq : q.Prime) {S T Q : Subgroup G}
    (hS_le : S ≤ Design.Ecomm H t W) (hT_le : T ≤ Design.Ecomm H t W)
    (hST_sup : S ⊔ T = Design.Ecomm H t W) (hST_inf : S ⊓ T = ⊥)
    (hST_comm : ∀ s ∈ S, ∀ u ∈ T, s * u = u * s)
    (hEc_le_NS : Design.Ecomm H t W ≤ Subgroup.normalizer (S : Set G))
    (htS : NormalizedBy t S) (htT : NormalizedBy t T)
    (hSp : IsPGroup q S) (hqT' : ¬ q ∣ Nat.card ↥T)
    (hQS : Q ≤ S) (hQA : Q ≤ A)
    (hQN : P ≤ Subgroup.normalizer (Q : Set G)) (hQne : Q ≠ ⊥) (hQp : IsPGroup q Q) :
    q ∣ 2 ^ p - 1 ∧ ∃ a : ℕ, 1 ≤ a ∧ (Kset (twoPoint H t) t).ncard = q ^ a * (2 ^ p - 1) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have ht : orderOf t = 2 := h.invol
  have hD_odd : Odd (Nat.card ↥(twoPoint H t)) := h.se.2.2 t h.notMem
  -- `K ⊆ E'` and `t` normalises `E'`
  have hsec2 := sec2_lemma1_w2 hFT h.toSetup3
  have hKsub : Kset (twoPoint H t) t ⊆ (Design.Ecomm H t W : Set G) := hsec2.1
  have hE_tinv : ∀ e ∈ Design.Egrp H t W, t * e * t⁻¹ ∈ Design.Egrp H t W := hsec2.2.1
  have hEc_le_D : Design.Ecomm H t W ≤ twoPoint H t :=
    Subgroup.commutator_le_of_le inf_le_right inf_le_right
  have hKset_eq : Kset (Design.Ecomm H t W) t = Kset (twoPoint H t) t :=
    kset_eq_of_subset hEc_le_D hKsub
  have hEc_odd : Odd (Nat.card ↥(Design.Ecomm H t W)) :=
    Odd.of_dvd_nat hD_odd (Subgroup.card_dvd_of_le hEc_le_D)
  have hEc_tinv : NormalizedBy t (Design.Ecomm H t W) := by
    intro x hx
    have hmapE : (Design.Egrp H t W).map (MulAut.conj t).toMonoidHom = Design.Egrp H t W := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rw [Subgroup.map_le_iff_le_comap]
        intro y hy
        simpa [MulAut.conj_apply] using hE_tinv y hy
      · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
    have hmap : (Design.Ecomm H t W).map (MulAut.conj t).toMonoidHom = Design.Ecomm H t W := by
      have hE' : Design.Ecomm H t W = ⁅Design.Egrp H t W, Design.Egrp H t W⁆ := rfl
      rw [hE', Subgroup.map_commutator, hmapE]
    have hx' : (MulAut.conj t) x ∈ (Design.Ecomm H t W).map (MulAut.conj t).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hmap] at hx'
    simpa [MulAut.conj_apply] using hx'
  -- ## `q ∣ |K|`
  have hq_Ec : q ∣ Nat.card ↥(Design.Ecomm H t W) := by
    have h1 : q ∣ Nat.card ↥Q := by
      obtain ⟨k, hk⟩ := hQp.exists_card_eq
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · rw [hk0, pow_zero] at hk
          exact absurd (Subgroup.card_eq_one.mp hk) hQne
        · exact hkpos
      rw [hk]
      exact ⟨q ^ (k - 1), by rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hk1]⟩
    exact h1.trans (Subgroup.card_dvd_of_le (hQS.trans hS_le))
  have hq_K : q ∣ (Kset (twoPoint H t) t).ncard := (h2b.2.2 q hq).mp hq_Ec
  -- ## the `q`-split of `E'`
  have hS_odd : Odd (Nat.card ↥S) := Odd.of_dvd_nat hEc_odd (Subgroup.card_dvd_of_le hS_le)
  have hT_odd : Odd (Nat.card ↥T) := Odd.of_dvd_nat hEc_odd (Subgroup.card_dvd_of_le hT_le)
  have hcard_Ec : Nat.card ↥(Design.Ecomm H t W) = Nat.card ↥S * Nat.card ↥T := by
    have h1 := card_sup_mul_card_inf (H := S) (K := T) (hT_le.trans hEc_le_NS)
    rw [hST_sup, hST_inf, Subgroup.card_bot, mul_one] at h1
    exact h1
  have hsplit := exists_mul_mem_of_sup_eq hS_le hT_le hST_sup hEc_le_NS
  -- ## `Kset T t ⊆ C_G(Q)`
  have hQT : Kset T t ⊆ (Subgroup.centralizer (Q : Set G) : Set G) := by
    intro u hu
    exact Subgroup.mem_centralizer_iff.mpr (fun x hx => hST_comm x (hQS hx) u hu.1)
  -- ## the two `ncard` identities
  obtain ⟨hk1, hk2, hk3, hk4⟩ := kset_decomp hS_le hT_le hST_sup hST_inf hST_comm htS htT hQT
  have hCK_Q : (Kset (twoPoint H t) t ∩ (Subgroup.centralizer (Q : Set G) : Set G)).ncard
      = 2 ^ p - 1 := by
    have h1 := congrArg Set.ncard (h.A_B Q hQne hQA hQN)
    rw [h.A_CK] at h1
    exact h1
  -- ## the two factors are powers of `q`
  have hK₁_pow : ∃ b : ℕ, (Kset S t).ncard = q ^ b := by
    have hdvd : (Kset S t).ncard ∣ Nat.card ↥S := kset_ncard_dvd ht htS hS_odd
    obtain ⟨j, hj⟩ := hSp.exists_card_eq
    rw [hj] at hdvd
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hq).mp hdvd
    exact ⟨b, hb⟩
  have hK₁Q_eq : (Kset S t ∩ (Subgroup.centralizer (Q : Set G) : Set G))
      = Kset (S ⊓ Subgroup.centralizer (Q : Set G)) t := by
    ext z
    constructor
    · rintro ⟨hz, hzc⟩
      exact ⟨⟨hz.1, hzc⟩, hz.2⟩
    · rintro ⟨⟨hzS, hzc⟩, hzt⟩
      exact ⟨⟨hzS, hzt⟩, hzc⟩
  have hX_odd : Odd (Nat.card ↥(S ⊓ Subgroup.centralizer (Q : Set G))) :=
    Odd.of_dvd_nat hS_odd (Subgroup.card_dvd_of_le inf_le_left)
  have hQ_le_V : Q ≤ centD H t := hQA.trans h.A_le
  have htQ : ∀ x ∈ Q, t * x * t⁻¹ = x := by
    intro x hx
    have h1 : t * x = x * t :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hQ_le_V hx).2).symm
    rw [h1, mul_assoc, mul_inv_cancel, mul_one]
  have hX_norm : NormalizedBy t (S ⊓ Subgroup.centralizer (Q : Set G)) := by
    intro z hz
    refine ⟨htS z hz.1, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr (fun x hx => ?_)
    have hzx : x * z = z * x := (Subgroup.mem_centralizer_iff.mp hz.2) x hx
    have h1 : z * x * z⁻¹ = x := by rw [← hzx]; group
    have hxt : t * x = x * t := by
      have h2 : t * x * t⁻¹ = x := htQ x hx
      calc t * x = (t * x * t⁻¹) * t := by group
        _ = x * t := by rw [h2]
    have hxt' : x * t⁻¹ = t⁻¹ * x := by
      have h2 : t * x * t⁻¹ = x := htQ x hx
      calc x * t⁻¹ = t⁻¹ * (t * x * t⁻¹) := by group
        _ = t⁻¹ * x := by rw [h2]
    calc x * (t * z * t⁻¹) = (x * t) * z * t⁻¹ := by group
      _ = (t * x) * z * t⁻¹ := by rw [hxt]
      _ = t * (x * z) * t⁻¹ := by group
      _ = t * (z * x) * t⁻¹ := by rw [hzx]
      _ = t * z * (x * t⁻¹) := by group
      _ = t * z * (t⁻¹ * x) := by rw [hxt']
      _ = (t * z * t⁻¹) * x := by group
  have hK₁Q_pow : ∃ c : ℕ, (Kset (S ⊓ Subgroup.centralizer (Q : Set G)) t).ncard = q ^ c := by
    have hdvd : (Kset (S ⊓ Subgroup.centralizer (Q : Set G)) t).ncard ∣ Nat.card ↥S :=
      (kset_ncard_dvd ht hX_norm hX_odd).trans (Subgroup.card_dvd_of_le inf_le_left)
    obtain ⟨j, hj⟩ := hSp.exists_card_eq
    rw [hj] at hdvd
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hq).mp hdvd
    exact ⟨c, hc⟩
  obtain ⟨b, hb⟩ := hK₁_pow
  obtain ⟨c, hc⟩ := hK₁Q_pow
  have hA : (Kset (twoPoint H t) t).ncard = q ^ b * (Kset T t).ncard := by
    rw [← hKset_eq, hk1, hb]
  have hB : 2 ^ p - 1 = q ^ c * (Kset T t).ncard := by
    have h1 : (Kset (Design.Ecomm H t W) t
        ∩ (Subgroup.centralizer (Q : Set G) : Set G)).ncard = 2 ^ p - 1 := by
      rw [hKset_eq]
      exact hCK_Q
    rw [← h1, hk4, hK₁Q_eq, hc]
  have hK₂_dvd : (Kset T t).ncard ∣ Nat.card ↥T := kset_ncard_dvd ht htT hT_odd
  have hq_K₂ : ¬ q ∣ (Kset T t).ncard := fun hd => hqT' (hd.trans hK₂_dvd)
  -- ## `1 ≤ b`
  have hb_pos : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with hb0 | hbpos
    · exfalso
      rw [hb0, pow_zero, one_mul] at hA
      rw [hA] at hq_K
      exact hq_K₂ hq_K
    · exact hbpos
  -- ## `1 ≤ c`
  have hc_pos : 1 ≤ c := by
    have hS_ne : S ≠ ⊥ := by
      intro hb'
      apply hqT'
      have h1 : Nat.card ↥(Design.Ecomm H t W) = Nat.card ↥T := by
        rw [hcard_Ec, hb', Subgroup.card_bot, one_mul]
      rwa [h1] at hq_Ec
    haveI : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hS_ne
    haveI : Nontrivial ↥(Subgroup.center ↥S) := IsPGroup.center_nontrivial hSp
    obtain ⟨z₀, hz₀⟩ := exists_ne (1 : ↥(Subgroup.center ↥S))
    set z : G := ((z₀ : ↥S) : G) with hzdef
    have hzS : z ∈ S := (z₀ : ↥S).2
    have hz1 : z ≠ 1 := fun h => hz₀ (Subtype.ext (Subtype.ext h))
    have hzcent : ∀ w ∈ S, w * z = z * w := by
      intro w hw
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp z₀.2) ⟨w, hw⟩)
    have hzK : ∀ k ∈ Kset (twoPoint H t) t, k * z = z * k := by
      intro k hk
      obtain ⟨s, hs, u, hu, hsu⟩ := hsplit k (hKsub hk)
      have h1 : s * z = z * s := hzcent s hs
      have h2 : u * z = z * u := (hST_comm z hzS u hu).symm
      calc k * z = (s * u) * z := by rw [hsu]
        _ = s * (u * z) := by group
        _ = s * (z * u) := by rw [h2]
        _ = (s * z) * u := by group
        _ = (z * s) * u := by rw [h1]
        _ = z * (s * u) := by group
        _ = z * k := by rw [hsu]
    have hzV : z ∉ centD H t := by
      intro hzV
      have hmem : z ∈ centD H t
          ⊓ Subgroup.centralizer ((Kset (twoPoint H t) t) : Set G) := by
        exact ⟨hzV, Subgroup.mem_centralizer_iff.mpr (fun k hk => hzK k hk)⟩
      rw [h.d2.2.1] at hmem
      exact hz1 (by simpa using hmem)
    have hCSQ : ¬ (S ⊓ Subgroup.centralizer (Q : Set G) ≤ centD H t) := by
      intro hle
      exact hzV (hle ⟨hzS,
        Subgroup.mem_centralizer_iff.mpr (fun x hx => hzcent x (hQS hx))⟩)
    have hCGeq : Subgroup.centralizer ({t} : Set G) ⊓ (S ⊓ Subgroup.centralizer (Q : Set G))
        = centD H t ⊓ (S ⊓ Subgroup.centralizer (Q : Set G)) := by
      ext w
      constructor
      · rintro ⟨hw1, hw2⟩
        exact ⟨⟨hEc_le_D (hS_le hw2.1), hw1⟩, hw2⟩
      · rintro ⟨hw1, hw2⟩
        exact ⟨hw1.2, hw2⟩
    have hne : (centD H t ⊓ (S ⊓ Subgroup.centralizer (Q : Set G))).subgroupOf
        (S ⊓ Subgroup.centralizer (Q : Set G)) ≠ ⊤ := by
      intro htop
      apply hCSQ
      intro w hw
      have hmem : (⟨w, hw⟩ : ↥(S ⊓ Subgroup.centralizer (Q : Set G)))
          ∈ (centD H t ⊓ (S ⊓ Subgroup.centralizer (Q : Set G))).subgroupOf
              (S ⊓ Subgroup.centralizer (Q : Set G)) := by
        rw [htop]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp hmem).1
    have hone : 1 < (Kset (S ⊓ Subgroup.centralizer (Q : Set G)) t).ncard := by
      rw [kset_ncard_eq_index ht hX_norm hX_odd, hCGeq]
      exact Subgroup.one_lt_index_of_ne_top hne
    have hc0 : c ≠ 0 := by
      intro hc0
      rw [hc, hc0, pow_zero] at hone
      exact absurd hone (lt_irrefl 1)
    omega
  -- ## `c < b`
  have hcb : c < b := by
    by_contra hcon
    have hle : b ≤ c := Nat.le_of_not_lt hcon
    have hK₁Q_card : (Kset S t ∩ (Subgroup.centralizer (Q : Set G) : Set G)).ncard = q ^ c := by
      rw [hK₁Q_eq, hc]
    have hle_bc : q ^ b ≤ q ^ c := Nat.pow_le_pow_right hq.one_le hle
    have hle_cb : q ^ c ≤ q ^ b := by
      rw [← hK₁Q_card, ← hb]
      exact Set.ncard_le_ncard Set.inter_subset_left
    have hcb_eq : c = b := Nat.pow_right_injective hq.two_le (le_antisymm hle_cb hle_bc)
    have hK₁C : Kset S t ⊆ (Subgroup.centralizer (Q : Set G) : Set G) := by
      have heq : Kset S t ∩ (Subgroup.centralizer (Q : Set G) : Set G) = Kset S t := by
        refine Set.eq_of_subset_of_ncard_le (s := Kset S t ∩
          (Subgroup.centralizer (Q : Set G) : Set G)) (t := Kset S t) Set.inter_subset_left ?_
        rw [hb, hK₁Q_card]
        exact Nat.pow_le_pow_right hq.one_le hle
      intro k hk
      have hk' : k ∈ Kset S t ∩ (Subgroup.centralizer (Q : Set G) : Set G) := by
        rw [heq]
        exact hk
      exact hk'.2
    have hQK : ∀ x ∈ Q, ∀ k ∈ Kset (twoPoint H t) t, x * k * x⁻¹ = k := by
      intro x hx k hk
      have hk' : k ∈ Kset (Design.Ecomm H t W) t := by rw [hKset_eq]; exact hk
      obtain ⟨s, hs, u, hu, hsu⟩ := hk2 k hk'
      have h1 : x * s * x⁻¹ = s := by
        have h1a := (Subgroup.mem_centralizer_iff.mp (hK₁C hs)) x hx
        rw [h1a]; group
      have h2 : x * u * x⁻¹ = u := by
        have h2a := hST_comm x (hQS hx) u hu.1
        rw [h2a]; group
      rw [hsu, show x * (s * u) * x⁻¹ = (x * s * x⁻¹) * (x * u * x⁻¹) from by group, h1, h2]
    have hbot : Q ≤ centD H t
        ⊓ Subgroup.centralizer ((Kset (twoPoint H t) t) : Set G) := by
      refine le_inf hQ_le_V fun x hx => ?_
      refine Subgroup.mem_centralizer_iff.mpr (fun k hk => ?_)
      have h1 : k * x = x * k := by
        calc k * x = (x * k * x⁻¹) * x := by rw [hQK x hx k hk]
          _ = x * k := by group
      exact h1
    rw [h.d2.2.1] at hbot
    exact hQne (le_bot_iff.mp hbot)
  -- ## conclusion
  refine ⟨?_, b - c, by omega, ?_⟩
  · rw [hB]
    exact ⟨q ^ (c - 1) * (Kset T t).ncard, by
      rw [← mul_assoc, mul_comm q (q ^ (c - 1)), ← pow_succ, Nat.sub_add_cancel hc_pos]⟩
  · rw [hA, hB, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (le_of_lt hcb)]

/-! ## Proposition 2 (c), (d) -/

/-- **Ch. III §4 Proposition 2 (c), (d)** (p.181). -/
theorem prop2cd (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G}
    (h : Work.NormalComplement.Design.Setup45A G H t W p P A)
    (h1d : Work.NormalComplement.NC4.Lemma1dConc H t W p P A)
    (hP1 : Work.NormalComplement.NC4.Prop1Conc H t W p P A)
    (h2a : Work.NormalComplement.NC4.Prop2aConc H t W p P A)
    (h2b : Work.NormalComplement.NC4.Prop2bConc H t W p P A) :
    Work.NormalComplement.NC4.Prop2cdConc H t W p P A := by
  classical
  have hp : p.Prime := h.prime
  -- ## `t` normalises `E'`
  have hsec2 := sec2_lemma1_w2 hFT h.toSetup3
  have hKsub : Kset (twoPoint H t) t ⊆ (Design.Ecomm H t W : Set G) := hsec2.1
  have hE_tinv : ∀ e ∈ Design.Egrp H t W, t * e * t⁻¹ ∈ Design.Egrp H t W := hsec2.2.1
  have hEc_le_D : Design.Ecomm H t W ≤ twoPoint H t :=
    Subgroup.commutator_le_of_le inf_le_right inf_le_right
  have hEc_odd : Odd (Nat.card ↥(Design.Ecomm H t W)) :=
    Odd.of_dvd_nat (h.se.2.2 t h.notMem) (Subgroup.card_dvd_of_le hEc_le_D)
  have hEc_tinv : NormalizedBy t (Design.Ecomm H t W) := by
    intro x hx
    have hmapE : (Design.Egrp H t W).map (MulAut.conj t).toMonoidHom = Design.Egrp H t W := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rw [Subgroup.map_le_iff_le_comap]
        intro y hy
        simpa [MulAut.conj_apply] using hE_tinv y hy
      · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
    have hmap : (Design.Ecomm H t W).map (MulAut.conj t).toMonoidHom = Design.Ecomm H t W := by
      have hE' : Design.Ecomm H t W = ⁅Design.Egrp H t W, Design.Egrp H t W⁆ := rfl
      rw [hE', Subgroup.map_commutator, hmapE]
    have hx' : (MulAut.conj t) x ∈ (Design.Ecomm H t W).map (MulAut.conj t).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hmap] at hx'
    simpa [MulAut.conj_apply] using hx'
  -- ## `P` normalises `E'` and `R = E' ⊓ V`
  have hE_norm : twoPoint H t ≤ Subgroup.normalizer (Design.Egrp H t W : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro d hd e he
    obtain ⟨heW, heD⟩ := Subgroup.mem_inf.mp he
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (h.normal hd.1) e).mp heW,
      (twoPoint H t).mul_mem ((twoPoint H t).mul_mem hd heD) ((twoPoint H t).inv_mem hd)⟩
  have hE'_norm : twoPoint H t ≤ Subgroup.normalizer (Design.Ecomm H t W : Set G) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator]
    have h1 : Subgroup.map (MulAut.conj d) (Design.Egrp H t W) = Design.Egrp H t W :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hE_norm hd)
    rw [h1]
  have hP_le_NE' : P ≤ Subgroup.normalizer (Design.Ecomm H t W : Set G) :=
    ((h.P_le.trans inf_le_right).trans inf_le_left).trans hE'_norm
  have hR_norm : centD H t ≤ Subgroup.normalizer (Design.Ecomm H t W ⊓ centD H t : Set G) :=
    (Subgroup.le_normalizer_iff (H := centD H t)
      (K := Design.Ecomm H t W ⊓ centD H t)).mpr (fun v hv w hw => by
        obtain ⟨hwE', hwV⟩ := Subgroup.mem_inf.mp hw
        exact Subgroup.mem_inf.mpr ⟨
          (Subgroup.mem_normalizer_iff.mp (hE'_norm ((inf_le_left : centD H t ≤ twoPoint H t) hv)) w).mp hwE',
          (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hv) w).mp hwV⟩)
  have hP_le_NR : P ≤ Subgroup.normalizer (Design.Ecomm H t W ⊓ centD H t : Set G) :=
    (h.P_le.trans inf_le_right).trans hR_norm
  have hR_le_A : Design.Ecomm H t W ⊓ centD H t ≤ A := by
    rw [h2a.2.2]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((h.P_le.trans inf_le_right).trans h.A_normal)
  have hR_ne : Design.Ecomm H t W ⊓ centD H t ≠ ⊥ := h.d2.2.2
  -- ## the key computation, for every prime divisor `q'` of `|R|`
  have key : ∀ q' : ℕ, q'.Prime →
      q' ∣ Nat.card ↥(Design.Ecomm H t W ⊓ centD H t) →
      q' ∣ 2 ^ p - 1 ∧ ∃ a' : ℕ, 1 ≤ a' ∧
        (Kset (twoPoint H t) t).ncard = q' ^ a' * (2 ^ p - 1) := by
    intro q' hq' hq'R
    haveI : Fact q'.Prime := ⟨hq'⟩
    obtain ⟨S, T, hS_le, hT_le, hST_sup, hST_inf, hST_comm, hEc_le_NS, htS, htT, hSp, hqT⟩ :=
      nilpotent_split h2b.1 hEc_tinv hq'
    -- the `q'`-elements of `E'` are exactly the elements of `S`
    have hS_eq : ∀ z ∈ Design.Ecomm H t W, (z ∈ S ↔ ∃ k, z ^ q' ^ k = 1) := by
      intro z hz
      exact ⟨fun hzS => by
          obtain ⟨k, hk⟩ := hSp ⟨z, hzS⟩
          exact ⟨k, congrArg Subtype.val hk⟩,
        fun hk => mem_of_pow_eq_one_of_isPGroup hq' hS_le hT_le hST_sup hST_inf hST_comm
          hEc_le_NS hqT z hz hk⟩
    have hP_le_NS : P ≤ Subgroup.normalizer (S : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro x hx z hz
      have hzE' : z ∈ Design.Ecomm H t W := hS_le hz
      have hzE'' : x * z * x⁻¹ ∈ Design.Ecomm H t W :=
        (Subgroup.mem_normalizer_iff.mp (hP_le_NE' hx) z).mp hzE'
      refine (hS_eq _ hzE'').mpr ?_
      obtain ⟨k, hk⟩ := (hS_eq z hzE').mp hz
      exact ⟨k, by
        have h2 : x * z * x⁻¹ = (MulAut.conj x) z := by simp [MulAut.conj_apply]
        rw [h2, ← map_pow, hk, map_one]⟩
    have hP_le_NQ : P ≤ Subgroup.normalizer (S ⊓ (Design.Ecomm H t W ⊓ centD H t) : Set G) :=
      (Subgroup.le_normalizer_iff (H := P)
        (K := S ⊓ (Design.Ecomm H t W ⊓ centD H t))).mpr (fun x hx z hz => by
          obtain ⟨hzS, hzR⟩ := Subgroup.mem_inf.mp hz
          exact Subgroup.mem_inf.mpr ⟨
            (Subgroup.mem_normalizer_iff.mp (hP_le_NS hx) z).mp hzS,
            (Subgroup.mem_normalizer_iff.mp (hP_le_NR hx) z).mp hzR⟩)
    -- a nontrivial `q'`-element of `R`
    haveI : Fintype ↥(Design.Ecomm H t W ⊓ centD H t) := Fintype.ofFinite _
    obtain ⟨x₀, hx₀ord⟩ := exists_prime_orderOf_dvd_card
      (G := ↥(Design.Ecomm H t W ⊓ centD H t)) q' (Fintype.card_eq_nat_card.symm ▸ hq'R)
    have hx₀R : ((x₀ : ↥(Design.Ecomm H t W ⊓ centD H t)) : G)
        ∈ Design.Ecomm H t W ⊓ centD H t := x₀.2
    have hx₀order : orderOf ((x₀ : ↥(Design.Ecomm H t W ⊓ centD H t)) : G) = q' :=
      (orderOf_injective (Subgroup.subtype _) (Subgroup.subtype_injective _) x₀).trans hx₀ord
    have hx₀S : ((x₀ : ↥(Design.Ecomm H t W ⊓ centD H t)) : G) ∈ S :=
      (hS_eq _ hx₀R.1).mpr ⟨1, by rw [pow_one, ← hx₀order]; exact pow_orderOf_eq_one _⟩
    have hx₀ne : ((x₀ : ↥(Design.Ecomm H t W ⊓ centD H t)) : G) ≠ 1 := by
      intro hcon
      rw [hcon, orderOf_one] at hx₀order
      exact absurd hx₀order (Nat.Prime.one_lt hq').ne
    have hQR_ne : S ⊓ (Design.Ecomm H t W ⊓ centD H t) ≠ ⊥ := by
      intro hb
      have hmem : ((x₀ : ↥(Design.Ecomm H t W ⊓ centD H t)) : G)
          ∈ S ⊓ (Design.Ecomm H t W ⊓ centD H t) := ⟨hx₀S, hx₀R⟩
      rw [hb] at hmem
      exact hx₀ne (by simpa using hmem)
    have hQp : IsPGroup q' ↥(S ⊓ (Design.Ecomm H t W ⊓ centD H t)) :=
      IsPGroup.of_injective hSp (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
    exact prop2c_step hFT h h2a h2b q' hq' hS_le hT_le hST_sup hST_inf hST_comm hEc_le_NS
      (Q := S ⊓ (Design.Ecomm H t W ⊓ centD H t)) htS htT hSp hqT
      (inf_le_left : S ⊓ (Design.Ecomm H t W ⊓ centD H t) ≤ S)
      ((inf_le_right : S ⊓ (Design.Ecomm H t W ⊓ centD H t) ≤
        Design.Ecomm H t W ⊓ centD H t).trans hR_le_A)
      hP_le_NQ hQR_ne hQp
  -- ## a prime divisor of `|R|`
  obtain ⟨q, hq, hqR⟩ := Nat.exists_prime_and_dvd
    (fun h1 => hR_ne (Subgroup.card_eq_one.mp h1))
  obtain ⟨hqdvd, a, ha, hKa⟩ := key q hq hqR
  -- ## uniqueness of the prime divisor
  have hpos : 0 < 2 ^ p - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hp.ne_zero (by norm_num))
  have huniq : ∀ q' : ℕ, q'.Prime → q' ∣ Nat.card ↥(Design.Ecomm H t W ⊓ centD H t) → q' = q := by
    intro q' hq' hq'R
    obtain ⟨-, a', ha', hK'⟩ := key q' hq' hq'R
    have h2 : q' ^ a' * (2 ^ p - 1) = q ^ a * (2 ^ p - 1) := hK'.symm.trans hKa
    have h3 : q' ^ a' = q ^ a := Nat.mul_right_cancel hpos h2
    have hdvd' : q' ∣ q' ^ a' := ⟨q' ^ (a' - 1),
      by rw [mul_comm, ← pow_succ, Nat.sub_add_cancel ha']⟩
    have hdvd : q' ∣ q := hq'.dvd_of_dvd_pow (h3 ▸ hdvd')
    rcases (Nat.dvd_prime hq).mp hdvd with h1 | h1
    · exact absurd h1 hq'.ne_one
    · exact h1
  have hRp : IsPGroup q ↥(Design.Ecomm H t W ⊓ centD H t) :=
    IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd (p := q) Nat.card_pos.ne'
      (fun {d} hd hdd => huniq d hd hdd))
  have hqK : q ∣ (Kset (twoPoint H t) t).ncard := by
    rw [hKa]
    exact ⟨q ^ (a - 1) * (2 ^ p - 1), by
      rw [← mul_assoc, mul_comm q (q ^ (a - 1)), ← pow_succ, Nat.sub_add_cancel ha]⟩
  obtain ⟨hfit, hfit_ne, hfit_syl⟩ := prop2d_step hFT h h1d hP1 h2a h2b q hq hqK hRp
  exact ⟨q, a, hq, ha, hqdvd, hKa, hfit, hfit_ne, hfit_syl⟩

end Work.NormalComplement.NC4
