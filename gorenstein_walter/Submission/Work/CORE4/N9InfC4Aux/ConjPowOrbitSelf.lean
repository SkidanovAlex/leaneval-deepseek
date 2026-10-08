import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.Case2Count11
import Submission.Work.CORE4.EightAnormalPcore_of_Qpos
import Submission.Work.CORE4.ncard_subgroups_prime_cube

open scoped commutatorElement

namespace Work.CORE4.N9InfC4Self

open Subgroup


theorem conjSub_one_self {G : Type} [Group G] (K : Subgroup G) :
    Work.GW2.conjSub (1 : G) K = K := by
  show K.map (MulAut.conj (1 : G)).toMonoidHom = K
  have h : MulAut.conj (1 : G) = 1 := by
    ext x
    simp [MulAut.conj_apply]
  rw [h]
  exact Subgroup.map_id K

theorem ConjPowOrbit {G : Type} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (Q A : Subgroup G) (q : G)
    (hqQ : q ∈ Q) (hAQ : A ≤ Q) (hAcard : Nat.card ↥A = p ^ 2)
    (hAexp : ∀ x ∈ A, x ^ p = 1) (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hZcard : Nat.card ↥(Work.CORE4.centerIn Q) = p) (hZle : Work.CORE4.centerIn Q ≤ A)
    (hcomm : ∀ a ∈ A, q * a * q⁻¹ * a⁻¹ ∈ Work.CORE4.centerIn Q)
    (hne : ∃ a ∈ A, q * a * q⁻¹ * a⁻¹ ≠ 1)
    (L₁ L₂ : Subgroup G) (hL₁A : L₁ ≤ A) (hL₂A : L₂ ≤ A)
    (hL₁card : Nat.card ↥L₁ = p) (hL₂card : Nat.card ↥L₂ = p)
    (hL₁ne : L₁ ≠ Work.CORE4.centerIn Q) (hL₂ne : L₂ ≠ Work.CORE4.centerIn Q) :
    ∃ i : ℕ, Work.GW2.conjSub (q ^ i) L₁ = L₂ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  set Z : Subgroup G := Work.CORE4.centerIn Q with hZdef
  have hZc : Nat.card ↥Z = p := by rw [hZdef]; exact hZcard
  have hZleA : Z ≤ A := by rw [hZdef]; exact hZle
  have hcommZ : ∀ a ∈ A, q * a * q⁻¹ * a⁻¹ ∈ Z := by
    intro a ha; rw [hZdef]; exact hcomm a ha
  have hL₁neZ : L₁ ≠ Z := fun h => hL₁ne (h.trans hZdef)
  have hL₂neZ : L₂ ≠ Z := fun h => hL₂ne (h.trans hZdef)
  -- ## `Z` centralises `Q`
  have hZQ : ∀ z ∈ Z, ∀ y ∈ Q, y * z = z * y := by
    intro z hz y hy
    rw [hZdef] at hz
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
    have h1 := congrArg Subtype.val ((Subgroup.mem_center_iff (G := ↥Q)).mp hw ⟨y, hy⟩)
    simp only [Subgroup.coe_mul] at h1
    rw [show (w : G) = z from hwz] at h1
    exact h1
  have hmemconj : ∀ (g : G) (K : Subgroup G) (y : G),
      y ∈ Work.GW2.conjSub g K ↔ ∃ x ∈ K, g * x * g⁻¹ = y := by
    intro g K y
    rw [Work.GW2.conjSub, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, by rw [← hxy]; simp [MulAut.conj_apply]⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, by rw [← hxy]; simp [MulAut.conj_apply]⟩
  have hZfixelem : ∀ g ∈ Q, ∀ z ∈ Z, g * z * g⁻¹ = z := by
    intro g hg z hz
    have h := hZQ z hz g hg
    rw [h]
    group
  have hZfixconj : ∀ g ∈ Q, Work.GW2.conjSub g Z = Z := by
    intro g hg
    apply le_antisymm
    · intro z hz
      obtain ⟨w, hw, hwz⟩ := (hmemconj g Z z).mp hz
      rw [← hwz, hZfixelem g hg w hw]
      exact hw
    · intro z hz
      exact (hmemconj g Z z).mpr ⟨z, hz, hZfixelem g hg z hz⟩
  -- ## `A ⊓ C_G(q) = Z`
  have hfix : ∀ a ∈ A, q * a * q⁻¹ = a → a ∈ Z := by
    intro a ha haq
    have hZK : Z ≤ A ⊓ Subgroup.centralizer ({q} : Set G) := by
      refine le_inf hZleA ?_
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hZQ z hz q hqQ
    have hKA : A ⊓ Subgroup.centralizer ({q} : Set G) ≤ A := inf_le_left
    have hKne : A ⊓ Subgroup.centralizer ({q} : Set G) ≠ A := by
      intro hcontra
      obtain ⟨a₀, ha₀A, ha₀⟩ := hne
      have hmem : a₀ ∈ A ⊓ Subgroup.centralizer ({q} : Set G) :=
        (le_of_eq hcontra.symm) ha₀A
      have ha₀C : a₀ ∈ Subgroup.centralizer ({q} : Set G) := (Subgroup.mem_inf.mp hmem).2
      have hcq : q * a₀ = a₀ * q :=
        (Subgroup.mem_centralizer_iff.mp ha₀C) q (Set.mem_singleton q)
      exact ha₀ (by rw [hcq]; group)
    have hKlt : Nat.card ↥(A ⊓ Subgroup.centralizer ({q} : Set G)) < Nat.card ↥A :=
      Subgroup.card_lt_of_lt (lt_of_le_of_ne hKA hKne)
    have hKdiv : Nat.card ↥(A ⊓ Subgroup.centralizer ({q} : Set G)) ∣ p ^ 2 := by
      rw [← hAcard]; exact Subgroup.card_dvd_of_le hKA
    have hpdvd : p ∣ Nat.card ↥(A ⊓ Subgroup.centralizer ({q} : Set G)) := by
      rw [← hZc]; exact Subgroup.card_dvd_of_le hZK
    have hppos : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer ({q} : Set G)) := by
      haveI : Nonempty ↥(A ⊓ Subgroup.centralizer ({q} : Set G)) :=
        ⟨⟨1, (A ⊓ Subgroup.centralizer ({q} : Set G)).one_mem⟩⟩
      exact Nat.card_pos
    have hple : p ≤ Nat.card ↥(A ⊓ Subgroup.centralizer ({q} : Set G)) :=
      Nat.le_of_dvd hppos hpdvd
    obtain ⟨k, hk2, hkeq⟩ := (Nat.dvd_prime_pow hp).mp hKdiv
    have hk1 : k = 1 := by
      have hk0 : k ≠ 0 := by
        intro hk0
        rw [hk0, pow_zero] at hkeq
        omega
      have hk2' : k ≠ 2 := by
        intro hk2''
        rw [hk2'', ← hAcard] at hkeq
        exact hKne (Subgroup.eq_of_le_of_card_ge hKA (le_of_eq hkeq.symm))
      omega
    have hKeq : Nat.card ↥(A ⊓ Subgroup.centralizer ({q} : Set G)) = p := by
      rw [hkeq, hk1, pow_one]
    have hKZ : Z = A ⊓ Subgroup.centralizer ({q} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hZK (by rw [hZc, hKeq])
    rw [hKZ]
    refine Subgroup.mem_inf.mpr ⟨ha, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    show q * a = a * q
    calc q * a = (q * a * q⁻¹) * q := by group
      _ = a * q := by rw [haq]
  -- ## the conjugation action of `q` on `A`
  have hσA : ∀ a ∈ A, q * a * q⁻¹ ∈ A := by
    intro a ha
    rw [show q * a * q⁻¹ = q * a * q⁻¹ * a⁻¹ * a from by group]
    exact A.mul_mem (hZleA (hcommZ a ha)) ha
  set σ : ↥A → ↥A := fun a => ⟨q * (a : G) * q⁻¹, hσA a a.2⟩ with hσdef
  have hσcoe : ∀ a : ↥A, ((σ a : ↥A) : G) = q * (a : G) * q⁻¹ := by
    intro a; rw [hσdef]
  set cc : ↥A → G := fun a => q * (a : G) * q⁻¹ * (a : G)⁻¹ with hcdef
  have hccZ : ∀ a : ↥A, cc a ∈ Z := fun a => hcommZ a a.2
  have hccA : ∀ a : ↥A, cc a ∈ A := fun a => hZleA (hccZ a)
  have hccval : ∀ a : ↥A, cc a = q * (a : G) * q⁻¹ * (a : G)⁻¹ := by
    intro a; rw [hcdef]
  have hσiter : ∀ (n : ℕ) (a : ↥A), ((σ^[n] a : ↥A) : G) = q ^ n * (a : G) * (q ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [Function.iterate_succ_apply', hσcoe, ih a, pow_succ']
      group
  have hσpow : ∀ (n : ℕ) (a : ↥A), ((σ^[n] a : ↥A) : G) = (cc a) ^ n * (a : G) := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      have hz : (cc a) ^ n ∈ Z := Z.pow_mem (hccZ a) n
      have hqcomm : q * (cc a) ^ n = (cc a) ^ n * q := hZQ ((cc a) ^ n) hz q hqQ
      have hca : q * (a : G) * q⁻¹ = (cc a) * (a : G) := by
        rw [hccval a]
        show q * (a : G) * q⁻¹ = q * (a : G) * q⁻¹ * (a : G)⁻¹ * (a : G)
        group
      rw [Function.iterate_succ_apply', hσcoe, ih a]
      calc q * ((cc a) ^ n * (a : G)) * q⁻¹
          = (q * (cc a) ^ n) * (a : G) * q⁻¹ := by group
        _ = ((cc a) ^ n * q) * (a : G) * q⁻¹ := by rw [hqcomm]
        _ = (cc a) ^ n * (q * (a : G) * q⁻¹) := by group
        _ = (cc a) ^ n * ((cc a) * (a : G)) := by rw [hca]
        _ = (cc a) ^ (n + 1) * (a : G) := by rw [pow_succ']; group
  -- ## `L ⊓ Z = ⊥` for `L ≠ Z` of order `p` inside `A`
  have hLZbot : ∀ L : Subgroup G, L ≤ A → Nat.card ↥L = p → L ≠ Z → L ⊓ Z = ⊥ := by
    intro L hLA hLc hLne'
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxL, hxZ⟩ := Subgroup.mem_inf.mp hx
    by_contra hxne
    have hcard : Nat.card ↥(L ⊓ Z) = p := by
      have hdvd : Nat.card ↥(L ⊓ Z) ∣ p := by
        rw [← hLc]; exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
      · exact absurd h1 (fun h1' =>
          hxne (Subgroup.mem_bot.mp (Subgroup.card_eq_one.mp h1' ▸ hx)))
      · exact h1
    have hLZle : L ≤ Z := by
      have heq : L ⊓ Z = L := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, hLc])
      exact heq ▸ inf_le_right
    exact hLne' (Subgroup.eq_of_le_of_card_ge hLZle (by rw [hZc, hLc]))
  -- ## no noncentral order-`p` subgroup of `A` is fixed by `q^d`, `0 < d < p`
  have hd_ne : ∀ d : ℕ, 0 < d → d < p → ∀ L : Subgroup G, L ≤ A → Nat.card ↥L = p →
      L ≠ Z → Work.GW2.conjSub (q ^ d) L ≠ L := by
    intro d hd0 hdp L hLA hLc hLne' hfixL
    have hLsub : L ≤ Z := by
      intro x hxL
      have hxA : x ∈ A := hLA hxL
      have hin : q ^ d * x * (q ^ d)⁻¹ ∈ L := by
        have h := (hmemconj (q ^ d) L (q ^ d * x * (q ^ d)⁻¹)).mpr ⟨x, hxL, rfl⟩
        rwa [hfixL] at h
      have hcx : (cc ⟨x, hxA⟩) ^ d ∈ L := by
        have h1 : ((σ^[d] ⟨x, hxA⟩ : ↥A) : G) = (cc ⟨x, hxA⟩) ^ d * x := hσpow d ⟨x, hxA⟩
        have h2 : ((σ^[d] ⟨x, hxA⟩ : ↥A) : G) ∈ L := by
          rw [hσiter d ⟨x, hxA⟩]
          exact hin
        rw [h1] at h2
        have h3 : x⁻¹ ∈ L := L.inv_mem hxL
        have h4 : (cc ⟨x, hxA⟩) ^ d * x * x⁻¹ ∈ L := L.mul_mem h2 h3
        rwa [mul_assoc, mul_inv_cancel, mul_one] at h4
      have hcz : (cc ⟨x, hxA⟩) ^ d ∈ Z := Z.pow_mem (hccZ ⟨x, hxA⟩) d
      have hbot : L ⊓ Z = ⊥ := hLZbot L hLA hLc hLne'
      have h1 : (cc ⟨x, hxA⟩) ^ d = 1 := by
        have hmem : (cc ⟨x, hxA⟩) ^ d ∈ L ⊓ Z := Subgroup.mem_inf.mpr ⟨hcx, hcz⟩
        rw [hbot] at hmem
        exact Subgroup.mem_bot.mp hmem
      have hc1 : cc ⟨x, hxA⟩ = 1 := by
        have hcpp : (cc ⟨x, hxA⟩) ^ p = 1 := hAexp _ (hccA ⟨x, hxA⟩)
        have hdvd1 : orderOf (cc ⟨x, hxA⟩) ∣ d := orderOf_dvd_iff_pow_eq_one.mpr h1
        have hdvd2 : orderOf (cc ⟨x, hxA⟩) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hcpp
        have hgcd : orderOf (cc ⟨x, hxA⟩) ∣ d.gcd p := Nat.dvd_gcd hdvd1 hdvd2
        have hcop : d.gcd p = 1 := by
          have hnot : ¬ p ∣ d := fun hpd => by
            have := Nat.le_of_dvd hd0 hpd
            omega
          exact (hp.coprime_iff_not_dvd.mpr hnot).symm.gcd_eq_one
        rw [hcop] at hgcd
        exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
      have hqx : q * x * q⁻¹ = x := by
        have h2 : q * x * q⁻¹ * x⁻¹ = 1 := by
          rw [← hccval ⟨x, hxA⟩]
          exact hc1
        calc q * x * q⁻¹ = (q * x * q⁻¹ * x⁻¹) * x := by group
          _ = 1 * x := by rw [h2]
          _ = x := by rw [one_mul]
      exact hfix x hxA hqx
    exact hLne' (Subgroup.eq_of_le_of_card_ge hLsub (by rw [hZc, hLc]))
  -- ## the count of order-`p` subgroups of `A`
  have hScount : {L : Subgroup G | L ≤ A ∧ Nat.card ↥L = p}.ncard = p + 1 := by
    have hexp' : ∀ x : ↥A, x ^ p = 1 := by
      intro x
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      exact hAexp x x.2
    have hcomm' : ∀ a b : ↥A, a * b = b * a := by
      intro a b
      apply Subtype.ext
      exact hAcomm a a.2 b b.2
    have hsq : {X : Subgroup ↥A | Nat.card ↥X = p}.ncard = p + 1 :=
      Work.CORE4.NcardSubgroupsCardPrimeSq p ↥A hAcard hexp' hcomm'
    have hbij : {X : Subgroup ↥A | Nat.card ↥X = p}.ncard
        = {L : Subgroup G | L ≤ A ∧ Nat.card ↥L = p}.ncard := by
      refine Set.ncard_congr' ?_
      refine
        { toFun := fun X => ⟨X.1.map A.subtype, ?_⟩
          invFun := fun L => ⟨L.1.subgroupOf A, ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      · exact ⟨Subgroup.map_subtype_le X.1,
          by rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective A)]; exact X.2⟩
      · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe L.2.1).toEquiv).trans L.2.2
      · intro X
        exact Subtype.ext (by
          apply le_antisymm
          · intro x hx
            rw [Subgroup.mem_subgroupOf] at hx
            obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
            have hyx' : y = x := Subtype.ext hyx
            rw [← hyx']
            exact hy
          · intro x hx
            rw [Subgroup.mem_subgroupOf]
            exact Subgroup.mem_map_of_mem A.subtype hx)
      · intro L
        exact Subtype.ext (Subgroup.map_subgroupOf_eq_of_le L.2.1)
    rw [← hbij]
    exact hsq
  -- ## the orbit argument
  set S : Set (Subgroup G) := {L : Subgroup G | L ≤ A ∧ Nat.card ↥L = p} with hSdef
  set S' : Set (Subgroup G) := {L : Subgroup G | L ≤ A ∧ Nat.card ↥L = p ∧ L ≠ Z} with hS'def
  have hScount' : S.ncard = p + 1 := by rw [hSdef]; exact hScount
  have hSeq : S = insert Z S' := by
    ext L
    rw [hSdef, hS'def]
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
    constructor
    · rintro ⟨hLA, hLc⟩
      by_cases h : L = Z
      · exact Or.inl h
      · exact Or.inr ⟨hLA, hLc, h⟩
    · rintro (rfl | ⟨hLA, hLc, -⟩)
      · exact ⟨hZleA, hZc⟩
      · exact ⟨hLA, hLc⟩
  have hZnotS' : Z ∉ S' := by
    rw [hS'def]
    simp
  have hS'card : S'.ncard = p := by
    have h1 : S.ncard = S'.ncard + 1 := by
      rw [hSeq, Set.ncard_insert_of_notMem hZnotS']
    rw [hScount'] at h1
    omega
  have hqmemA : ∀ i : ℕ, ∀ a ∈ A, q ^ i * a * (q ^ i)⁻¹ ∈ A := by
    intro i
    induction i with
    | zero => intro a ha; simpa using ha
    | succ i ih =>
      intro a ha
      have h1 : q ^ (i + 1) * a * (q ^ (i + 1))⁻¹ =
          q * (q ^ i * a * (q ^ i)⁻¹) * q⁻¹ := by
        rw [pow_succ']; group
      rw [h1]
      exact hσA _ (ih a ha)
  have hconjA : ∀ i : ℕ, Work.GW2.conjSub (q ^ i) A ≤ A := by
    intro i y hy
    obtain ⟨a, haA, hay⟩ := (hmemconj (q ^ i) A y).mp hy
    rw [← hay]
    exact hqmemA i a haA
  set g : Fin p → Subgroup G := fun i => Work.GW2.conjSub (q ^ (i : ℕ)) L₁ with hgdef
  have hcardg : ∀ i : Fin p, Nat.card ↥(g i) = p := by
    intro i
    rw [hgdef]
    show Nat.card ↥(L₁.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom) = p
    rw [Subgroup.card_map_of_injective (MulAut.conj (q ^ (i : ℕ))).injective, hL₁card]
  have hneq : ∀ i : Fin p, g i ≠ Z := by
    intro i hcon
    rw [hgdef] at hcon
    have h1 : L₁ = Work.GW2.conjSub ((q ^ (i : ℕ))⁻¹) Z := by
      have h2 := congrArg (fun K => Work.GW2.conjSub ((q ^ (i : ℕ))⁻¹) K) hcon
      rw [Work.CORE4.conjSub_mul', inv_mul_cancel, conjSub_one_self] at h2
      exact h2
    have h3 : Work.GW2.conjSub ((q ^ (i : ℕ))⁻¹) Z = Z :=
      hZfixconj _ (Q.inv_mem (Q.pow_mem hqQ (i : ℕ)))
    exact hL₁neZ (h1.trans h3)
  have key : ∀ a b : ℕ, a < b → b < p →
      Work.GW2.conjSub (q ^ a) L₁ = Work.GW2.conjSub (q ^ b) L₁ → False := by
    intro a b hab hbp heq
    have hd0 : 0 < b - a := by omega
    have hdp : b - a < p := by omega
    have hfixb : Work.GW2.conjSub (q ^ (b - a)) L₁ = L₁ := by
      have h1 := congrArg (fun K => Work.GW2.conjSub ((q ^ a)⁻¹) K) heq
      rw [Work.CORE4.conjSub_mul', Work.CORE4.conjSub_mul', inv_mul_cancel,
        conjSub_one_self] at h1
      have hba : (q ^ a)⁻¹ * q ^ b = q ^ (b - a) := by
        have h2 : a + (b - a) = b := Nat.add_sub_of_le (le_of_lt hab)
        calc (q ^ a)⁻¹ * q ^ b = (q ^ a)⁻¹ * q ^ (a + (b - a)) := by rw [h2]
          _ = (q ^ a)⁻¹ * (q ^ a * q ^ (b - a)) := by rw [pow_add]
          _ = q ^ (b - a) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      rw [hba] at h1
      exact h1.symm
    exact hd_ne (b - a) hd0 hdp L₁ hL₁A hL₁card hL₁neZ hfixb
  have hginj : Function.Injective g := by
    intro i j hij
    by_contra hne'
    rw [hgdef] at hij
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · exact key (i : ℕ) (j : ℕ) (by simpa using hlt) j.2 hij
    · exact key (j : ℕ) (i : ℕ) (by simpa using hlt) i.2 hij.symm
  have himgsub : Set.range g ⊆ S' := by
    rintro L ⟨i, rfl⟩
    rw [hS'def]
    exact ⟨(Subgroup.map_mono hL₁A).trans (hconjA (i : ℕ)), hcardg i, hneq i⟩
  have hrange : Set.range g = S' :=
    Set.eq_of_subset_of_ncard_le himgsub (by
      rw [Set.ncard_range_of_injective hginj, hS'card]
      simp)
  have hL₂S' : L₂ ∈ S' := by
    rw [hS'def]
    exact ⟨hL₂A, hL₂card, hL₂neZ⟩
  obtain ⟨i, hi⟩ := hrange ▸ hL₂S'
  exact ⟨(i : ℕ), hi⟩

end Work.CORE4.N9InfC4Self
