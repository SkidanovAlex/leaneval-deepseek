import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs
import Submission.Work.ZassenhausSuzuki.Odd.isCZ_basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The orders of non-conjugate `ℱ`-subgroups are coprime

The Bender–Suzuki family `ℱ = Work.ZassenhausSuzuki.Odd.IsCZ` consists of the centralisers
`C_G(x)` of the non-involution strongly real elements `x` of `G`.  This file proves the
"pairwise coprimality" of the orders of distinct members of `ℱ`:

> if `A, B ∈ ℱ` and a prime `p` divides both `|A|` and `|B|`, then `A` and `B` are conjugate.

The mathematics is HB (Huppert–Blackburn) XI, 10.4 (b), whose statement for the Suzuki
configuration is Suzuki 1962, §10 (the discussion preceding Proposition 16):

* by Suzuki's Proposition 14 (`Work.ZassenhausSuzuki.centralizer_abelian_of_strongly_real`) an
  `A ∈ ℱ` has odd order and `C_G(a) = A` for every `1 ≠ a ∈ A` (recorded as
  `Work.ZassenhausSuzuki.Odd.isCZ_basic`);
* consequently `A` is a **Hall subgroup** of `G`: if a prime `p` divided both `|A|` and
  `[G : A]`, a Sylow `p`-subgroup `Q` of `G` would have `1 ≠ P = Q ⊓ A < Q`; by the normalizer
  condition in the `p`-group `Q` the subgroup `P` has a non-trivial centralizer inside
  `N_Q(P)`, so some `b ∈ N_Q(P) \ P` commutes with some `1 ≠ a ∈ P`; then `b ∈ C_G(a) = A`,
  so `b ∈ A ⊓ Q = P`, a contradiction.  This is `isCZ_coprime_index` below;
* hence for `p | |A|` the `p`-part `|A|_p` equals `|G|_p`, so `A` contains the image `K_A` of a
  Sylow `p`-subgroup of `A`, which is a Sylow `p`-subgroup of `G` (`IsPGroup.toSylow`); the
  Sylow subgroups `K_A`, `K_B` of `G` are conjugate, `K_B = g K_A g⁻¹ ⊆ B ⊓ g A g⁻¹`, and two
  members of `ℱ` meeting non-trivially coincide (immediate from `C_G(a) = A` for `a ∈ A#`).

-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.ZassenhausSuzuki.Odd

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-! ## Elementary properties of `IsCZ` -/

/-- Conjugation carries the centraliser of a singleton to the centraliser of the image:
`g C_G(k) g⁻¹ = C_G(g k g⁻¹)`. -/
theorem conj_conj_centralizer_singleton (g k : G) :
    Submission.Blueprint.conj g (Subgroup.centralizer ({k} : Set G))
      = Subgroup.centralizer ({g * k * g⁻¹} : Set G) := by
  ext x
  rw [Submission.Blueprint.conj, Subgroup.mem_map_equiv,
    Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have hsymm : ((MulEquiv.symm (MulAut.conj g)) x : G) = g⁻¹ * x * g := by simp
  rw [hsymm]
  constructor
  · intro hc
    calc x * (g * k * g⁻¹) = g * ((g⁻¹ * x * g) * k) * g⁻¹ := by group
      _ = g * (k * (g⁻¹ * x * g)) * g⁻¹ := by rw [hc]
      _ = (g * k * g⁻¹) * x := by group
  · intro hc
    calc (g⁻¹ * x * g) * k = g⁻¹ * (x * (g * k * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * k * g⁻¹) * x) * g := by rw [← hc]
      _ = k * (g⁻¹ * x * g) := by group

/-- `IsCZ` is invariant under conjugation. -/
theorem isCZ_conj {A : Subgroup G} (hA : IsCZ A) (g : G) :
    IsCZ (Submission.Blueprint.conj g A) := by
  obtain ⟨x, hsr, hx1, hx2, hAx⟩ := hA
  obtain ⟨u, v, hu, hv, huv⟩ := hsr
  have hu' : (g * u * g⁻¹) * (g * u * g⁻¹) = 1 := by
    calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hu]; group
  have hv' : (g * v * g⁻¹) * (g * v * g⁻¹) = 1 := by
    calc (g * v * g⁻¹) * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
      _ = 1 := by rw [hv]; group
  have huv' : (g * u * g⁻¹) * (g * v * g⁻¹) = g * x * g⁻¹ := by
    calc (g * u * g⁻¹) * (g * v * g⁻¹) = g * (u * v) * g⁻¹ := by group
      _ = g * x * g⁻¹ := by rw [huv]
  refine ⟨g * x * g⁻¹, ⟨g * u * g⁻¹, g * v * g⁻¹, hu', hv', huv'⟩, ?_, ?_, ?_⟩
  · intro hc
    exact hx1 (by
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [hc]
        _ = 1 := by group)
  · intro hc
    exact hx2 (by
      calc x * x = g⁻¹ * ((g * x * g⁻¹) * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * 1 * g := by rw [hc]
        _ = 1 := by group)
  · rw [(conj_conj_centralizer_singleton g x).symm, hAx]

/-- Two members of `ℱ` that meet non-trivially coincide: a non-identity element of `A ⊓ B` has
centraliser both `A` and `B`. -/
theorem isCZ_eq_of_inf_ne_bot (h : SzOddHyp H Q t) {A B : Subgroup G} (hA : IsCZ A)
    (hB : IsCZ B) (hne : A ⊓ B ≠ ⊥) : A = B := by
  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hzA : (z : G) ∈ A := z.2.1
  have hzB : (z : G) ∈ B := z.2.2
  have hz1 : (z : G) ≠ 1 := fun hc => hz (Subtype.ext hc)
  have h1 : Subgroup.centralizer ({(z : G)} : Set G) = A :=
    ((isCZ_basic h hA).2.2 (z : G) hzA hz1).2
  have h2 : Subgroup.centralizer ({(z : G)} : Set G) = B :=
    ((isCZ_basic h hB).2.2 (z : G) hzB hz1).2
  rw [← h1, h2]

/-! ## The Hall property of a member of `ℱ` -/

/-- An element of the normaliser (inside `S`) of `P.subgroupOf S` normalises `P` in `G`. -/
theorem mem_normalizer_of_mem_normalizer_subgroupOf {P S : Subgroup G} (hP : P ≤ S) {x : ↥S}
    (hx : x ∈ Subgroup.normalizer ((P.subgroupOf S : Subgroup ↥S) : Set ↥S)) :
    (x : G) ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro p
  constructor
  · intro hp
    have hpS : p ∈ S := hP hp
    have h1 : (⟨p, hpS⟩ : ↥S) ∈ P.subgroupOf S := Subgroup.mem_subgroupOf.mpr hp
    have h2 := (hx ⟨p, hpS⟩).1 h1
    have h3 : ((x * ⟨p, hpS⟩ * x⁻¹ : ↥S) : G) ∈ P := Subgroup.mem_subgroupOf.mp h2
    simpa using h3
  · intro hp
    have hxinv : x⁻¹ ∈ Subgroup.normalizer ((P.subgroupOf S : Subgroup ↥S) : Set ↥S) :=
      (Subgroup.normalizer ((P.subgroupOf S : Subgroup ↥S) : Set ↥S)).inv_mem hx
    have h1 : (⟨(x : G) * p * (x : G)⁻¹, hP hp⟩ : ↥S) ∈ P.subgroupOf S :=
      Subgroup.mem_subgroupOf.mpr hp
    have h2 := (hxinv ⟨(x : G) * p * (x : G)⁻¹, hP hp⟩).1 h1
    have h3 : ((x⁻¹ * ⟨(x : G) * p * (x : G)⁻¹, hP hp⟩ * x⁻¹⁻¹ : ↥S) : G) ∈ P :=
      Subgroup.mem_subgroupOf.mp h2
    have h4 : ((x⁻¹ * ⟨(x : G) * p * (x : G)⁻¹, hP hp⟩ * x⁻¹⁻¹ : ↥S) : G) = p := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      group
    rw [h4] at h3
    exact h3

/-- In a finite `p`-group `S`, for `1 ≠ P < S` some non-identity element of `P` commutes with
some element of `S \ P`.  (Take the centre of `T = N_S(P) > P`: either it meets `P` in a
non-identity element, which then commutes with everything in `T` outside `P`, or an element of
it lies outside `P` and commutes with the whole of `P`.) -/
theorem exists_commute_of_lt_isPGroup {p : ℕ} [Fact p.Prime] {S P : Subgroup G}
    (hS : IsPGroup p S) (hPle : P ≤ S) (hP1 : P ≠ ⊥) (hPS : P ≠ S) :
    ∃ a ∈ P, a ≠ 1 ∧ ∃ b ∈ S, b ∉ P ∧ a * b = b * a := by
  haveI : Group.IsNilpotent ↥S := IsPGroup.isNilpotent hS
  have hnc : NormalizerCondition ↥S := Group.normalizerCondition_of_isNilpotent
  have hHtop : (P.subgroupOf S) ≠ ⊤ := by
    intro h
    exact hPS (le_antisymm hPle (Subgroup.subgroupOf_eq_top.mp h))
  obtain ⟨-, y, hyN, hyH⟩ :=
    SetLike.lt_iff_le_and_exists.mp (hnc (P.subgroupOf S) (lt_top_iff_ne_top.mpr hHtop))
  have hyNP : (y : G) ∈ Subgroup.normalizer (P : Set G) :=
    mem_normalizer_of_mem_normalizer_subgroupOf hPle hyN
  have hyP : (y : G) ∉ P := fun h => hyH (Subgroup.mem_subgroupOf.mpr h)
  set T : Subgroup G := Subgroup.normalizer (P : Set G) ⊓ S with hT
  have hPT : P ≤ T := fun x hx => ⟨Subgroup.le_normalizer hx, hPle hx⟩
  have hyT : (y : G) ∈ T := ⟨hyNP, y.2⟩
  have hTne : T ≠ P := fun hEq => hyP (hEq ▸ hyT)
  have hTp : IsPGroup p T := IsPGroup.to_le hS inf_le_right
  have hyne : (⟨(y : G), hyT⟩ : ↥T) ≠ ⟨1, T.one_mem⟩ := by
    intro hc
    have h1 : (y : G) = 1 := by simpa using congrArg Subtype.val hc
    exact hyP (by rw [h1]; exact P.one_mem)
  haveI : Nontrivial ↥T := ⟨⟨(y : G), hyT⟩, ⟨1, T.one_mem⟩, hyne⟩
  have hZ : ⊥ < Subgroup.center ↥T := IsPGroup.bot_lt_center hTp
  obtain ⟨-, z, hzc, hz1'⟩ := SetLike.lt_iff_le_and_exists.mp hZ
  have hz1 : z ≠ 1 := hz1'
  by_cases hzP : (z : G) ∈ P
  · obtain ⟨-, u, huT, huP⟩ :=
      SetLike.lt_iff_le_and_exists.mp (lt_of_le_of_ne hPT (Ne.symm hTne))
    refine ⟨(z : G), hzP, fun hc => hz1 (Subtype.ext hc), u, huT.2, huP, ?_⟩
    have hcomm := Subgroup.mem_center_iff.mp hzc ⟨u, huT⟩
    have h5 : u * (z : G) = (z : G) * u := by
      have hcv := congrArg Subtype.val hcomm
      simpa [Subgroup.coe_mul] using hcv
    exact h5.symm
  · obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP1
    refine ⟨(a : G), a.2, fun hc => ha (Subtype.ext hc), (z : G), z.2.2, hzP, ?_⟩
    have hcomm := Subgroup.mem_center_iff.mp hzc ⟨(a : G), hPT a.2⟩
    have h5 : (a : G) * (z : G) = (z : G) * (a : G) := by
      have hcv := congrArg Subtype.val hcomm
      simpa [Subgroup.coe_mul] using hcv
    exact h5

/-- **The Hall property.**  If `A ∈ ℱ` and `p` is a prime divisor of `|A|`, then `p` does not
divide the index `[G : A]`.  (HB XI, 10.4 (b).) -/
theorem prime_not_dvd_index_of_isCZ (h : SzOddHyp H Q t) {A : Subgroup G} (hA : IsCZ A)
    {p : ℕ} (hp : p.Prime) (hpa : p ∣ Nat.card ↥A) : ¬ p ∣ A.index := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro hpi
  -- a non-identity element of `A` of order `p`
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) p hpa
  have hxG : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe]; exact hx
  have hxne : (x : G) ≠ 1 := by
    intro hc
    have h1 : orderOf (x : G) = 1 := by rw [hc, orderOf_one]
    rw [hxG] at h1
    exact hp.ne_one h1
  -- a Sylow `p`-subgroup of `G` containing `x`
  have hxp : IsPGroup p ↥(Subgroup.zpowers (x : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxG, pow_one])
  obtain ⟨SY, hSYle⟩ := IsPGroup.exists_le_sylow hxp
  have hxS : (x : G) ∈ (SY : Subgroup G) := hSYle (Subgroup.mem_zpowers _)
  set P : Subgroup G := (SY : Subgroup G) ⊓ A with hPdef
  have hPleS : P ≤ (SY : Subgroup G) := inf_le_left
  have hPleA : P ≤ A := inf_le_right
  have hxP : (x : G) ∈ P := ⟨hxS, x.2⟩
  have hP1 : P ≠ ⊥ := by
    intro hbot
    exact hxne (Subgroup.mem_bot.mp (hbot ▸ hxP))
  have hPS : P ≠ (SY : Subgroup G) := by
    intro hEq
    have hSA : (SY : Subgroup G) ≤ A := hEq ▸ hPleA
    have hdiv : A.index ∣ (SY : Subgroup G).index := Subgroup.index_dvd_of_le hSA
    exact SY.not_dvd_index (dvd_trans hpi hdiv)
  obtain ⟨a, haP, ha1, b, hbS, hbP, hab⟩ :=
    exists_commute_of_lt_isPGroup (p := p) (S := (SY : Subgroup G)) (P := P)
      SY.isPGroup' hPleS hP1 hPS
  have hca : Subgroup.centralizer ({a} : Set G) = A :=
    ((isCZ_basic h hA).2.2 a (hPleA haP) ha1).2
  have hbA : b ∈ A := by
    rw [← hca]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hab.symm
  exact hbP ⟨hbS, hbA⟩

/-- `|A|` is coprime to `[G : A]` for `A ∈ ℱ` (the Hall property in coprime form). -/
theorem isCZ_coprime_index (h : SzOddHyp H Q t) {A : Subgroup G} (hA : IsCZ A) :
    Nat.Coprime (Nat.card ↥A) A.index := by
  by_contra hnc
  obtain ⟨p, hp, hpa, hpi⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  exact prime_not_dvd_index_of_isCZ h hA hp hpa hpi

/-! ## The conjugacy statement -/

/-- The pointwise action of `MulAut.conj g` on subgroups is the conjugation of the blueprint. -/
theorem smul_conj_eq_blueprint_conj (g : G) (K : Subgroup G) :
    MulAut.conj g • K = Submission.Blueprint.conj g K := by
  rw [Subgroup.pointwise_smul_def, Submission.Blueprint.conj]
  congr 1

theorem isCZ_conj_of_prime_dvd (h : Work.ZassenhausSuzuki.Odd.SzOddHyp H Q t)
    {A B : Subgroup G} (hA : Work.ZassenhausSuzuki.Odd.IsCZ A)
    (hB : Work.ZassenhausSuzuki.Odd.IsCZ B) {p : ℕ} (hp : p.Prime)
    (hAa : p ∣ Nat.card ↥A) (hBb : p ∣ Nat.card ↥B) :
    ∃ g : G, B = Submission.Blueprint.conj g A := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hAi : ¬ p ∣ A.index := fun hpi =>
    Nat.not_coprime_of_dvd_of_dvd hp.one_lt hAa hpi (isCZ_coprime_index h hA)
  have hBi : ¬ p ∣ B.index := fun hpi =>
    Nat.not_coprime_of_dvd_of_dvd hp.one_lt hBb hpi (isCZ_coprime_index h hB)
  -- Sylow `p`-subgroups of `A` and of `B`, transported into `G`
  obtain ⟨SA⟩ := Sylow.nonempty (p := p) (G := ↥A)
  obtain ⟨SB⟩ := Sylow.nonempty (p := p) (G := ↥B)
  set KA : Subgroup G := Subgroup.map A.subtype (SA : Subgroup ↥A) with hKAdef
  set KB : Subgroup G := Subgroup.map B.subtype (SB : Subgroup ↥B) with hKBdef
  have hKAle : KA ≤ A := Subgroup.map_subtype_le _
  have hKBle : KB ≤ B := Subgroup.map_subtype_le _
  have hKAp : IsPGroup p KA := (SA.isPGroup').map A.subtype
  have hKBp : IsPGroup p KB := (SB.isPGroup').map B.subtype
  have hKAsub : KA.subgroupOf A = (SA : Subgroup ↥A) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, hzy⟩
      have hzy' : z = y := Subtype.ext hzy
      exact hzy' ▸ hz
    · exact fun hy => ⟨y, hy, rfl⟩
  have hKBsub : KB.subgroupOf B = (SB : Subgroup ↥B) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, hzy⟩
      have hzy' : z = y := Subtype.ext hzy
      exact hzy' ▸ hz
    · exact fun hy => ⟨y, hy, rfl⟩
  -- the index in `G` of the transported Sylow subgroup is not divisible by `p`
  have hKAi : ¬ p ∣ KA.index := by
    intro hpi
    have h1 : p ∣ KA.relIndex A := by
      have hmul := Subgroup.relIndex_mul_index hKAle
      rw [← hmul] at hpi
      rcases hp.dvd_mul.mp hpi with hh | hh
      · exact hh
      · exact absurd hh hAi
    have h2 : KA.relIndex A = (SA : Subgroup ↥A).index := by
      show (KA.subgroupOf A).index = (SA : Subgroup ↥A).index
      rw [hKAsub]
    rw [h2] at h1
    exact SA.not_dvd_index h1
  have hKBi : ¬ p ∣ KB.index := by
    intro hpi
    have h1 : p ∣ KB.relIndex B := by
      have hmul := Subgroup.relIndex_mul_index hKBle
      rw [← hmul] at hpi
      rcases hp.dvd_mul.mp hpi with hh | hh
      · exact hh
      · exact absurd hh hBi
    have h2 : KB.relIndex B = (SB : Subgroup ↥B).index := by
      show (KB.subgroupOf B).index = (SB : Subgroup ↥B).index
      rw [hKBsub]
    rw [h2] at h1
    exact SB.not_dvd_index h1
  -- the transported Sylow subgroups are non-trivial
  have hKAne : KA ≠ ⊥ := by
    have hcard : Nat.card ↥KA = Nat.card ↥(SA : Subgroup ↥A) :=
      Subgroup.card_map_of_injective Subtype.coe_injective
    have hpdvd : p ∣ Nat.card ↥KA := hcard ▸ (by
      have hmul := Subgroup.card_mul_index (SA : Subgroup ↥A)
      rcases hp.dvd_mul.mp (hmul ▸ hAa) with hh | hh
      · exact hh
      · exact absurd hh SA.not_dvd_index)
    intro hbot
    rw [hbot, Subgroup.card_bot] at hpdvd
    exact hp.not_dvd_one hpdvd
  have hKBne : KB ≠ ⊥ := by
    have hcard : Nat.card ↥KB = Nat.card ↥(SB : Subgroup ↥B) :=
      Subgroup.card_map_of_injective Subtype.coe_injective
    have hpdvd : p ∣ Nat.card ↥KB := hcard ▸ (by
      have hmul := Subgroup.card_mul_index (SB : Subgroup ↥B)
      rcases hp.dvd_mul.mp (hmul ▸ hBb) with hh | hh
      · exact hh
      · exact absurd hh SB.not_dvd_index)
    intro hbot
    rw [hbot, Subgroup.card_bot] at hpdvd
    exact hp.not_dvd_one hpdvd
  -- Sylow's theorem: the two Sylow subgroups are conjugate
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hKAp.toSylow hKAi) (hKBp.toSylow hKBi)
  have hconj : KB = Submission.Blueprint.conj g KA := by
    have h1 : (((g • (hKAp.toSylow hKAi) : Sylow p G)) : Subgroup G)
        = MulAut.conj g • KA := by
      rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe]
    rw [← IsPGroup.toSylow_coe hKBp hKBi, ← hg, h1, smul_conj_eq_blueprint_conj]
  -- a conjugate of `A` meets `B` non-trivially
  have hne : Submission.Blueprint.conj g A ⊓ B ≠ ⊥ := by
    intro hbot
    have hle : KB ≤ (⊥ : Subgroup G) := by
      rw [← hbot]
      refine le_inf ?_ hKBle
      rw [hconj]
      exact Subgroup.map_mono hKAle
    exact hKBne (le_bot_iff.mp hle)
  have heq : Submission.Blueprint.conj g A = B :=
    isCZ_eq_of_inf_ne_bot h (isCZ_conj hA g) hB hne
  exact ⟨g, heq.symm⟩

end Work.ZassenhausSuzuki.Odd
