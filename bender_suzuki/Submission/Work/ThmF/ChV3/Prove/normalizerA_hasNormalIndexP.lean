import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.Step9Defs
import Submission.Work.ThmF.Prove.centDLowerCentralizerS
import Submission.Work.ThmF.ChV12.Lemma5Defs
import Submission.Work.ThmF.ChV12.L6basic
import Submission.Work.ThmF.ChV3.Prove.G0_hasNormalIndexP_of_fixed_elementary
import Submission.Work.ThmF.ChV3.Prove.G2_card_sup_closure_pair_le
import Submission.Work.ThmF.ChV3.Prove.L_facts
import Submission.Work.ThmF.ChV3.Prove.S1_centralizerP_eq
import Submission.Work.ThmF.ChV3.Prove.S2_commS_mem_R
import Submission.Work.ThmF.ChV3.Prove.S3_T_facts
import Submission.Work.ThmF.ChV3.Prove.S5_cst_inf_cs
import Submission.Work.ThmF.ChV3.Prove.A_le_cst
import Submission.Work.ThmF.ChV3.Prove.W_V_on_L
import Submission.Work.ThmF.ChV3.Prove.W_le_centralizer_X5
import Submission.Work.ThmF.ChV3.Prove.card_sup_of_le_normalizer
import Submission.Work.ThmF.ChV3.Prove.OrbitCountDefs
import Submission.Work.ThmF.ChV3.A_aux.W_sup_P_eq_centD_of_FT
import Submission.Work.ThmF.ChV3.Prove.T_sig_facts
import Submission.Work.ThmF.ChV3.Prove.P_on_L
import Submission.Work.ThmF.ChV3.Prove.A_LV_facts
import Submission.Work.ThmF.ChV3.Prove.A_stronglyReal_normalizer
import Submission.Work.ThmF.ChV3.Prove.A_weaklyClosed
import Submission.Work.ThmF.ChV3.Prove.cst_center_sylow
import Submission.Work.ThmF.ChV3.Prove.cst_isPGroup
import Submission.Work.ThmF.ChV3.Prove.cP_inf_cst

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 3000000
set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV3.Prove

open Work.ThmF.ChV3 Submission.Blueprint
open scoped commutatorElement



variable {G : Type} [Group G]

/-- If `K` normalises `H`, every element of `H ⊔ K` is a product `h * k`. -/
theorem mem_sup_of_le_normalizer {H K : Subgroup G} (h : K ≤ Subgroup.normalizer (H : Set G))
    {x : G} : x ∈ H ⊔ K ↔ ∃ y ∈ H, ∃ z ∈ K, y * z = x := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left H K h, Set.mem_mul]
  exact Iff.rfl

/-- Cardinality of `H.subgroupOf K` is that of `H ⊓ K`. -/
theorem card_subgroupOf_eq_card_inf {H K : Subgroup G} :
    Nat.card ↥(H.subgroupOf K) = Nat.card ↥(H ⊓ K) := by
  have h := Subgroup.card_map_of_injective (K := H.subgroupOf K) (f := K.subtype)
    K.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype] at h
  exact h.symm

/-- **Product formula for subgroups**: if `K` normalises `H` then
`|H ⊔ K| * |H ⊓ K| = |H| * |K|`. -/
theorem card_sup_mul_card_inf_of_le_normalizer {H K : Subgroup G}
    (h : K ≤ Subgroup.normalizer (H : Set G)) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card ↥H * Nat.card ↥K := by
  set M := H ⊔ K with hM
  have hHM : H ≤ M := le_sup_left
  have hKM : K ≤ M := le_sup_right
  have hnorm : M ≤ Subgroup.normalizer (H : Set G) := sup_le Subgroup.le_normalizer h
  have hN' : (H.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mpr hnorm
  haveI := hN'
  have hHcard : Nat.card ↥(H.subgroupOf M) = Nat.card ↥H := by
    rw [card_subgroupOf_eq_card_inf, inf_eq_left.mpr hHM]
  have hKcard : Nat.card ↥(K.subgroupOf M) = Nat.card ↥K := by
    rw [card_subgroupOf_eq_card_inf, inf_eq_left.mpr hKM]
  set ψ : ↥(K.subgroupOf M) →* (↥M ⧸ (H.subgroupOf M)) :=
    (QuotientGroup.mk' (H.subgroupOf M)).comp (Subgroup.subtype (K.subgroupOf M)) with hψ
  have hmem_ker : ∀ x : ↥(K.subgroupOf M), ψ x = 1 ↔ ((x : ↥M) : G) ∈ H := by
    intro x
    rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have hker : Nat.card ↥ψ.ker = Nat.card ↥(H ⊓ K) := by
    have hbij : ψ.ker ≃ ↥(H ⊓ K) :=
      { toFun := fun x => ⟨(((x : ↥(K.subgroupOf M)) : ↥M) : G),
          hmem_ker ↑x |>.mp (MonoidHom.mem_ker.mp x.2),
          Subgroup.mem_subgroupOf.mp ((x : ↥(K.subgroupOf M)).2)⟩
        invFun := fun y => ⟨⟨⟨(y : G), hKM y.2.2⟩, Subgroup.mem_subgroupOf.mpr y.2.2⟩,
          MonoidHom.mem_ker.mpr (hmem_ker _ |>.mpr y.2.1)⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => Subtype.ext rfl }
    exact Nat.card_congr hbij
  have hrange : ψ.range = ⊤ := by
    rw [eq_top_iff]
    rintro q -
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (H.subgroupOf M) q
    have hm : (m : G) ∈ H ⊔ K := hM ▸ m.2
    obtain ⟨y, hy, z, hz, hyz⟩ := (mem_sup_of_le_normalizer h).mp hm
    refine ⟨⟨⟨z, hKM hz⟩, Subgroup.mem_subgroupOf.mpr hz⟩, ?_⟩
    show QuotientGroup.mk (s := H.subgroupOf M) (⟨z, hKM hz⟩ : ↥M)
      = QuotientGroup.mk (s := H.subgroupOf M) m
    have hyk : QuotientGroup.mk (s := H.subgroupOf M) (⟨y, hHM hy⟩ : ↥M) = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hy
    have hzy : (⟨y, hHM hy⟩ : ↥M) * ⟨z, hKM hz⟩ = m := Subtype.ext hyz
    calc QuotientGroup.mk (s := H.subgroupOf M) (⟨z, hKM hz⟩ : ↥M)
        = 1 * QuotientGroup.mk (s := H.subgroupOf M) (⟨z, hKM hz⟩ : ↥M) := (one_mul _).symm
      _ = QuotientGroup.mk (s := H.subgroupOf M) (⟨y, hHM hy⟩ : ↥M) *
            QuotientGroup.mk (s := H.subgroupOf M) (⟨z, hKM hz⟩ : ↥M) := by rw [hyk]
      _ = QuotientGroup.mk (s := H.subgroupOf M) ((⟨y, hHM hy⟩ : ↥M) * ⟨z, hKM hz⟩) :=
            (QuotientGroup.mk_mul (H.subgroupOf M) _ _).symm
      _ = QuotientGroup.mk (s := H.subgroupOf M) m := by rw [hzy]
  -- |K| = |H ⊓ K| * |M / H'|
  have hmain : Nat.card ↥K = Nat.card ↥(H ⊓ K) * Nat.card (↥M ⧸ (H.subgroupOf M)) := by
    rw [← hKcard, ← hker]
    have h1 : ψ.ker.index = Nat.card (↥M ⧸ (H.subgroupOf M)) := by
      rw [Subgroup.index_eq_card,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hrange,
        Subgroup.card_top]
    have h2 := Subgroup.card_mul_index ψ.ker
    rw [h1] at h2
    exact h2.symm
  have hMcard : Nat.card ↥M = Nat.card ↥H * Nat.card (↥M ⧸ (H.subgroupOf M)) := by
    rw [← hHcard, ← Subgroup.index_eq_card (H.subgroupOf M)]
    exact (Subgroup.card_mul_index (H.subgroupOf M)).symm
  rw [hMcard, hmain]
  ring





variable {G : Type} [Group G] [Finite G]
variable {H Q : Subgroup G} {t s r : G} {P : Subgroup G}

/-! ### generic helpers -/

theorem card_le_card_of_le {H K : Subgroup G} (h : H ≤ K) : Nat.card ↥H ≤ Nat.card ↥K :=
  Nat.card_le_card_of_injective (fun x : ↥H => (⟨(x : G), h x.2⟩ : ↥K))
    (fun a b hab => Subtype.ext (congrArg (fun x : ↥K => (x : G)) hab))

theorem isMulCommutative_of_card_eq_three {M : Type*} [Group M] [Finite M]
    (h : Nat.card M = 3) : IsMulCommutative M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hnt : Nontrivial M := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hpg : IsPGroup 3 M := IsPGroup.of_card (n := 1) (by rw [h]; norm_num)
  have hc : Nontrivial ↥(Subgroup.center M) := hpg.center_nontrivial
  have h1 : 1 < Nat.card ↥(Subgroup.center M) := Finite.one_lt_card_iff_nontrivial.mpr hc
  have h2 : Nat.card ↥(Subgroup.center M) ∣ 3 := by
    rw [← h]; exact Subgroup.card_subgroup_dvd_card _
  have h3 : Nat.card ↥(Subgroup.center M) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp h2 with h | h
    · omega
    · exact h
  exact Subgroup.center_eq_top_iff.mp (Subgroup.eq_top_of_card_eq _ (by rw [h3, h]))

theorem isMulCommutative_of_card_eq_nine {M : Type*} [Group M] [Finite M]
    (h : Nat.card M = 9) : IsMulCommutative M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [h]; norm_num)

/-- A common normaliser of two subgroups normalises their join. -/
theorem le_normalizer_sup {A B C : Subgroup G} (hA : C ≤ Subgroup.normalizer (A : Set G))
    (hB : C ≤ Subgroup.normalizer (B : Set G)) :
    C ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro c hc
  rw [← cj_eq_self_iff]
  rw [cj, Subgroup.map_sup]
  congr 1
  · exact (cj_eq_self_iff c A).mpr (hA hc)
  · exact (cj_eq_self_iff c B).mpr (hB hc)

/-- Elementwise commutation gives a normaliser inclusion. -/
theorem le_normalizer_of_forall_mul_comm {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : B ≤ Subgroup.normalizer (A : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have h1 : a * b = b * a := h a ha b hb
    rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
    exact ha
  · intro ha
    have h1 : (b * a * b⁻¹) * b = b * (b * a * b⁻¹) := h (b * a * b⁻¹) ha b hb
    have h2 : b * a = b * (b * a * b⁻¹) := by rw [← h1]; group
    have h3 : a = b * a * b⁻¹ := mul_left_cancel h2
    rw [h3]; exact ha

/-- A subgroup of index three in a `3`-group is normal. -/
theorem normal_of_index_three_of_isPGroup {H K : Subgroup G} (hHK : H ≤ K)
    (hK : IsPGroup 3 ↥K) (hidx : Nat.card ↥K = 3 * Nat.card ↥H) :
    K ≤ Subgroup.normalizer (H : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hHK]
  have hcard : Nat.card ↥(H.subgroupOf K) = Nat.card ↥H := by
    rw [card_subgroupOf_eq_card_inf, inf_eq_left.mpr hHK]
  have hidx3 : (H.subgroupOf K).index = 3 := by
    have h1 : Nat.card ↥(H.subgroupOf K) * (H.subgroupOf K).index = Nat.card ↥K :=
      Subgroup.card_mul_index _
    rw [hcard] at h1
    rw [hidx, mul_comm 3] at h1
    exact Nat.mul_left_cancel (Nat.card_pos (α := ↥H)) h1
  have hmin : (Nat.card ↥K).minFac = 3 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK
    have hprime : ((Nat.card ↥K).minFac).Prime :=
      Nat.minFac_prime (by have := Nat.card_pos (α := ↥H); omega)
    have hdvd3 : (Nat.card ↥K).minFac ∣ 3 := by
      have h : (Nat.card ↥K).minFac ∣ 3 ^ n := by rw [← hn]; exact Nat.minFac_dvd _
      exact hprime.dvd_of_dvd_pow h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
    · exact absurd h hprime.ne_one
    · exact h
  exact Subgroup.normal_of_index_eq_minFac_card (H := H.subgroupOf K) (by rw [hidx3, hmin])

/-- Commutators against a join, given them against the pieces. -/
theorem commutator_mem_of_sup {Z A₁ A₂ : Subgroup G} {b : G}
    (hA₁Z : A₁ ≤ Subgroup.normalizer (Z : Set G)) (hA₂Z : A₂ ≤ Subgroup.normalizer (Z : Set G))
    (hA₂A₁ : A₂ ≤ Subgroup.normalizer (A₁ : Set G))
    (h₁ : ∀ a ∈ A₁, ⁅a, b⁆ ∈ Z) (h₂ : ∀ a ∈ A₂, ⁅a, b⁆ ∈ Z) :
    ∀ a ∈ A₁ ⊔ A₂, ⁅a, b⁆ ∈ Z := by
  intro a ha
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_of_le_normalizer hA₂A₁).mp ha
  rw [commutatorElement_mul_left_eq_conj_mul]
  exact Z.mul_mem ((Subgroup.le_normalizer_iff.mp hA₁Z) x hx (⁅y, b⁆) (h₂ y hy)) (h₁ x hx)

/-- Elements of a join of two commuting abelian subgroups commute. -/
theorem mul_comm_of_sup {A B : Subgroup G}
    (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
  have hfine : B ≤ Subgroup.normalizer (A : Set G) := le_normalizer_of_forall_mul_comm hAB
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_le_normalizer hfine).mp hx
  obtain ⟨a', ha', b', hb', rfl⟩ := (mem_sup_of_le_normalizer hfine).mp hy
  have h1 : b * a' = a' * b := (hAB a' ha' b hb).symm
  have h2 : a * a' = a' * a := hA a ha a' ha'
  have h3 : b * b' = b' * b := hB b hb b' hb'
  have h4 : a * b' = b' * a := hAB a ha b' hb'
  calc (a * b) * (a' * b') = a * (b * a') * b' := by group
    _ = a * (a' * b) * b' := by rw [h1]
    _ = (a * a') * (b * b') := by group
    _ = (a' * a) * (b' * b) := by rw [h2, h3]
    _ = a' * (a * b') * b := by group
    _ = a' * (b' * a) * b := by rw [h4]
    _ = (a' * b') * (a * b) := by group

/-- A join of two exponent-three commuting subgroups has exponent three. -/
theorem pow_three_eq_one_of_sup {A B : Subgroup G}
    (hA : ∀ a ∈ A, a ^ 3 = 1) (hB : ∀ b ∈ B, b ^ 3 = 1)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ x ∈ A ⊔ B, x ^ 3 = 1 := by
  have hfine : B ≤ Subgroup.normalizer (A : Set G) := le_normalizer_of_forall_mul_comm hAB
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_le_normalizer hfine).mp hx
  have h1 : Commute a b := hAB a ha b hb
  rw [h1.mul_pow, hA a ha, hB b hb, one_mul]





variable {G : Type} [Group G]

/-! ### decompositions in a join with a normalised subgroup -/




variable {G : Type} [Group G] [Finite G]
variable {H Q : Subgroup G} {t s r : G} {P : Subgroup G}

/-! ### the standing objects of case (10-2) -/

theorem card_P_case102 (hpf : Nat.card P = orderOf (s * t)) (d : Case102 H Q t s P) :
    Nat.card P = 3 := hpf.trans d.f3

theorem m_eq_two (h15 : Chain15 H Q t s r P) (d : Case102 H Q t s P) : h15.m = 2 := by
  have h1 : orderOf (s * t) ^ h15.m = 9 := by rw [← h15.hcq, d.cq8]
  rw [d.f3] at h1
  have h2 : (3 : ℕ) ^ h15.m = 3 ^ 2 := by rw [h1]; norm_num
  exact Nat.pow_right_injective (a := 3) (by norm_num) h2

theorem card_R (h15 : Chain15 H Q t s r P) (h7 : Ker H Q P t = P)
    (hpf : Nat.card P = orderOf (s * t)) (d : Case102 H Q t s P) :
    Nat.card ↥h15.R = 27 := by
  rw [h15.hcardR, h7, card_P_case102 hpf d, d.f3, m_eq_two h15 d]
  norm_num

theorem card_Z1 (d : Case102 H Q t s P) : Nat.card ↥(Z1 s t) = 3 :=
  (Nat.card_zpowers (s * t)).trans d.f3

theorem V_le_Cst (c : CtxF H Q t s r P) : centD H t ≤ Cst s t := by
  have hVs : centD H t ≤ Subgroup.centralizer ({s} : Set G) :=
    Work.ThmF.Prove.centDLowerCentralizerS c.split c.s_mem c.s_inv c.r_mem c.sid
  have hVt : centD H t ≤ Subgroup.centralizer ({t} : Set G) :=
    fun x hx => (Subgroup.mem_inf.mp hx).2
  exact (le_inf hVs hVt).trans (centralizer_mul_le_centralizer s t)

theorem Sig_le_Cst (c : CtxF H Q t s r P) : Sig H t P ≤ Cst s t :=
  ((inf_le_left : Sig H t P ≤ W H t).trans (Work.ThmF.W_le_centD H t)).trans (V_le_Cst c)

theorem Sig_le_CGP : Sig H t P ≤ CG P := inf_le_right

theorem R_inf_Sig (hFT : FeitThompsonProp) (hC4 : ChIIFourProp) (c : CtxF H Q t s r P)
    (h15 : Chain15 H Q t s r P) (h7 : Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t)) :
    h15.R ⊓ Sig H t P = ⊥ := by
  have h1 := (S1_centralizerP_eq hFT hC4 c h15 h7 hpf).1
  have hle : h15.R ⊓ Sig H t P ≤ ⊥ := by
    rw [← h1]
    exact le_inf inf_le_left (inf_le_right.trans le_sup_right)
  exact le_antisymm hle bot_le

theorem card_RSig (hFT : FeitThompsonProp) (hC4 : ChIIFourProp) (c : CtxF H Q t s r P)
    (h15 : Chain15 H Q t s r P) (h7 : Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    (d : Case102 H Q t s P) : Nat.card ↥(h15.R ⊔ Sig H t P) = 81 := by
  have hnorm : Sig H t P ≤ Subgroup.normalizer (h15.R : Set G) :=
    Sig_le_CGP.trans h15.hRn
  rw [card_sup_of_le_normalizer hnorm (R_inf_Sig hFT hC4 c h15 h7 hpf),
    card_R h15 h7 hpf d, d.sig3]

theorem T_facts (hFT : FeitThompsonProp) (hC4 : ChIIFourProp) (c : CtxF H Q t s r P)
    (h15 : Chain15 H Q t s r P) (h7 : Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    {T : Subgroup G} (h11 : Step11Out H Q t P h15.R T) (d : Case102 H Q t s P) :
    (∀ x ∈ T, s * x * s⁻¹ = x⁻¹) ∧ s * t ∈ T ∧ (∀ x ∈ T, x ^ 3 = 1) ∧
      Nat.card ↥T = 9 := by
  have h1 := S1_centralizerP_eq hFT hC4 c h15 h7 hpf
  have h2 : ∀ g ∈ CG P, g * s * g⁻¹ * s⁻¹ ∈ h15.R :=
    S2_commS_mem_R hFT hC4 c hpf h1.2.1 h15.hRn
  have h3 := S3_T_facts hFT hC4 c hpf h15.m h15.hm h11 h7 h15.hcardR h15.hcq h2
  refine ⟨h3.1, h3.2.1, fun x hx => ?_, ?_⟩
  · have := h3.2.2.1 x hx
    rwa [card_P_case102 hpf d] at this
  · rw [h3.2.2.2, card_P_case102 hpf d, m_eq_two h15 d]
    norm_num

theorem T_le_R (h15 : Chain15 H Q t s r P) {T : Subgroup G}
    (h11 : Step11Out H Q t P h15.R T) : T ≤ h15.R := by
  rw [← h11.TPR]; exact le_sup_left

theorem Z1_le_T (hFT : FeitThompsonProp) (hC4 : ChIIFourProp) (c : CtxF H Q t s r P)
    (h15 : Chain15 H Q t s r P) (h7 : Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    {T : Subgroup G} (h11 : Step11Out H Q t P h15.R T) (d : Case102 H Q t s P) : Z1 s t ≤ T :=
  Subgroup.zpowers_le.mpr (T_facts hFT hC4 c h15 h7 hpf h11 d).2.1

theorem Z1_le_R (hFT : FeitThompsonProp) (hC4 : ChIIFourProp) (c : CtxF H Q t s r P)
    (h15 : Chain15 H Q t s r P) (h7 : Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    {T : Subgroup G} (h11 : Step11Out H Q t P h15.R T) (d : Case102 H Q t s P) :
    Z1 s t ≤ h15.R := (Z1_le_T hFT hC4 c h15 h7 hpf h11 d).trans (T_le_R h15 h11)

theorem Z1_le_L (hFT : FeitThompsonProp) (hC4 : ChIIFourProp) (c : CtxF H Q t s r P)
    (h15 : Chain15 H Q t s r P) (d : Case102 H Q t s P) : Z1 s t ≤ Lsub H s t :=
  Subgroup.zpowers_le.mpr (L_facts hFT hC4 c h15 d).2.2.2

theorem R_le_Cst (hFT : FeitThompsonProp) (hC4 : ChIIFourProp) (c : CtxF H Q t s r P)
    (h15 : Chain15 H Q t s r P) (h7 : Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    {T : Subgroup G} (h11 : Step11Out H Q t P h15.R T) (d : Case102 H Q t s P) :
    h15.R ≤ Cst s t := by
  intro x hx
  rw [Cst, Subgroup.mem_centralizer_singleton_iff]
  exact mul_comm_of_mem h11.comm hx
    ((T_le_R h15 h11) (T_facts hFT hC4 c h15 h7 hpf h11 d).2.1)

theorem T_le_Cst (hFT : FeitThompsonProp) (hC4 : ChIIFourProp) (c : CtxF H Q t s r P)
    (h15 : Chain15 H Q t s r P) (h7 : Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    {T : Subgroup G} (h11 : Step11Out H Q t P h15.R T) (d : Case102 H Q t s P) :
    T ≤ Cst s t := (T_le_R h15 h11).trans (R_le_Cst hFT hC4 c h15 h7 hpf h11 d)

theorem Lsub_inf_RSig (hFT : FeitThompsonProp) (hC4 : ChIIFourProp) (c : CtxF H Q t s r P)
    (h15 : Chain15 H Q t s r P) (h7 : Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    {T : Subgroup G} (h11 : Step11Out H Q t P h15.R T) (d : Case102 H Q t s P)
    (hPL : (∃ x ∈ P, ∃ y ∈ Lsub H s t, x * y ≠ y * x) ∧
      (∀ a ∈ Lsub H s t, ∀ b ∈ P, a * b * a⁻¹ * b⁻¹ ∈ Z1 s t)) :
    Lsub H s t ⊓ (h15.R ⊔ Sig H t P) = Z1 s t := by
  have hLc := L_facts hFT hC4 c h15 d
  have hZ1L := Z1_le_L hFT hC4 c h15 d
  have hZ1R := Z1_le_R hFT hC4 c h15 h7 hpf h11 d
  have hle : Z1 s t ≤ Lsub H s t ⊓ (h15.R ⊔ Sig H t P) := le_inf hZ1L (hZ1R.trans le_sup_left)
  set m := Nat.card ↥(Lsub H s t ⊓ (h15.R ⊔ Sig H t P)) with hm
  have hdvd : m ∣ 9 := by
    rw [hm, ← hLc.2.1]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hge3 : 3 ≤ m := by
    rw [hm, ← card_Z1 d]
    exact card_le_card_of_le hle
  have hle9 : m ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
  have hne9 : m ≠ 9 := by
    intro h9
    have hLR : Lsub H s t ≤ h15.R ⊔ Sig H t P := by
      have heq : Lsub H s t ⊓ (h15.R ⊔ Sig H t P) = Lsub H s t := by
        refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
        rw [← hm, h9, hLc.2.1]
      rw [← heq]
      exact inf_le_right
    have hLCG : Lsub H s t ≤ CG P := hLR.trans (sup_le h15.hRc Sig_le_CGP)
    obtain ⟨x, hx, y, hy, hxy⟩ := hPL.1
    exact hxy (Subgroup.mem_centralizer_iff.mp (hLCG hy) x hx)
  have hm3 : m = 3 := by
    interval_cases m
    all_goals
      first
        | rfl
        | (exfalso; exact hne9 rfl)
        | norm_num at hdvd
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [← hm, hm3, card_Z1 d]


/-- `(m * k) ^ n` stays, modulo `M`, equal to `k ^ n`. -/
theorem pow_mem_of_le_normalizer_sup {M K : Subgroup G}
    (hKM : K ≤ Subgroup.normalizer (M : Set G)) {m k : G} (hm : m ∈ M) (hk : k ∈ K) (n : ℕ) :
    ∃ m' ∈ M, (m * k) ^ n = m' * k ^ n := by
  induction n with
  | zero => exact ⟨1, M.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨m', hm', ih'⟩ := ih
    refine ⟨m' * (k ^ n * m * (k ^ n)⁻¹),
      M.mul_mem hm' ((Subgroup.le_normalizer_iff.mp hKM) (k ^ n) (K.pow_mem hk n) m hm), ?_⟩
    rw [pow_succ, ih']
    group

/-- Commutators of two elements of `M ⊔ K` with `K` commutative land in `M`. -/
theorem commutator_mem_of_le_normalizer_sup {M K : Subgroup G}
    (hKM : K ≤ Subgroup.normalizer (M : Set G))
    (hK : ∀ k ∈ K, ∀ k' ∈ K, k * k' = k' * k)
    {m k m' k' : G} (hm : m ∈ M) (hk : k ∈ K) (hm' : m' ∈ M) (hk' : k' ∈ K) :
    ⁅m * k, m' * k'⁆ ∈ M := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  refine M.mul_mem (M.mul_mem (M.mul_mem hm ?_) (M.inv_mem hm)) ?_
  · -- `⁅k, m' * k'⁆ ∈ M`
    rw [commutatorElement_mul_right_eq_mul_conj]
    have h1 : ⁅k, k'⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hK k hk k' hk')
    have h2 : ⁅k, m'⁆ ∈ M := by
      have h3 : k * m' * k⁻¹ ∈ M := (Subgroup.le_normalizer_iff.mp hKM) k hk m' hm'
      have h4 : ⁅k, m'⁆ = (k * m' * k⁻¹) * m'⁻¹ := by
        unfold commutatorElement; group
      rw [h4]
      exact M.mul_mem h3 (M.inv_mem hm')
    rw [h1]
    have h5 : ⁅k, m'⁆ * m' * 1 * m'⁻¹ = ⁅k, m'⁆ := by group
    rw [h5]
    exact h2
  · -- `⁅m, m' * k'⁆ ∈ M`
    rw [commutatorElement_mul_right_eq_mul_conj]
    have h1 : ⁅m, m'⁆ ∈ M := by
      unfold commutatorElement
      exact M.mul_mem (M.mul_mem (M.mul_mem hm hm') (M.inv_mem hm)) (M.inv_mem hm')
    have h2 : ⁅m, k'⁆ ∈ M := by
      have h3 : k' * m * k'⁻¹ ∈ M := (Subgroup.le_normalizer_iff.mp hKM) k' hk' m hm
      have h4 : ⁅m, k'⁆ = m * (k' * m * k'⁻¹)⁻¹ := by
        unfold commutatorElement
        group
      rw [h4]
      exact M.mul_mem hm (M.inv_mem h3)
    exact M.mul_mem (M.mul_mem (M.mul_mem h1 hm') h2) (M.inv_mem hm')

/-- Conjugation transports centralisers of singletons. -/
theorem map_centralizer_singleton {G : Type} [Group G] {u g : G} :
    (Subgroup.centralizer ({u} : Set G)).map (MulAut.conj g).toMonoidHom
      = Subgroup.centralizer ({g * u * g⁻¹} : Set G) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
    have hxy' : g * y * g⁻¹ = x := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hxy
    rw [← hxy']
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    calc (g * y * g⁻¹) * (g * u * g⁻¹) = g * (y * u) * g⁻¹ := by group
      _ = g * (u * y) * g⁻¹ := by rw [hy]
      _ = (g * u * g⁻¹) * (g * y * g⁻¹) := by group
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      calc (g⁻¹ * x * g) * u = g⁻¹ * (x * (g * u * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * u * g⁻¹) * x) * g := by rw [hx]
        _ = u * (g⁻¹ * x * g) := by group
    · show (MulAut.conj g) (g⁻¹ * x * g) = x
      rw [MulAut.conj_apply]; group

/-- Commutators land in `M` if the quotient `S/M` has order three. -/
theorem commutator_mem_of_card_quotient_three {G : Type} [Group G] [Finite G] {M S : Subgroup G} (hMS : M ≤ S)
    (hN : S ≤ Subgroup.normalizer (M : Set G))
    (hcard : Nat.card (↥S ⧸ (M.subgroupOf S)) = 3) :
    ∀ a ∈ S, ∀ b ∈ S, ⁅a, b⁆ ∈ M := by
  haveI : (M.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMS).mpr hN
  haveI : Finite ↥S := Finite.of_injective (Subtype.val : ↥S → G) Subtype.val_injective
  haveI : Finite (↥S ⧸ (M.subgroupOf S)) :=
    Finite.of_surjective (QuotientGroup.mk' (M.subgroupOf S)) (QuotientGroup.mk'_surjective _)
  haveI hq : IsMulCommutative (↥S ⧸ (M.subgroupOf S)) :=
    isMulCommutative_of_card_eq_three hcard
  intro a ha b hb
  set x : ↥S := ⟨a, ha⟩ with hx
  set y : ↥S := ⟨b, hb⟩ with hy
  have h2 : (QuotientGroup.mk' (M.subgroupOf S) ⁅x, y⁆ : ↥S ⧸ (M.subgroupOf S)) = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hq.is_comm.comm _ _)
  have h3 : (⁅x, y⁆ : ↥S) ∈ M.subgroupOf S := (QuotientGroup.eq_one_iff (⁅x, y⁆ : ↥S)).mp h2
  have h4 : ((⁅x, y⁆ : ↥S) : G) = ⁅a, b⁆ := by
    show (Subgroup.subtype S) ⁅x, y⁆ = ⁅a, b⁆
    rw [map_commutatorElement, hx, hy]
    rfl
  have h5 : (⁅a, b⁆ : G) ∈ M := by
    have h6 := Subgroup.mem_subgroupOf.mp h3
    rwa [h4] at h6
  exact h5

/-- Third powers land in `M` if the quotient `S/M` has order three. -/
theorem pow_mem_of_card_quotient_three {G : Type} [Group G] [Finite G] {M S : Subgroup G}
    (hMS : M ≤ S) (hN : S ≤ Subgroup.normalizer (M : Set G))
    (hcard : Nat.card (↥S ⧸ (M.subgroupOf S)) = 3) :
    ∀ a ∈ S, a ^ 3 ∈ M := by
  haveI : (M.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMS).mpr hN
  haveI : Finite ↥S := Finite.of_injective (Subtype.val : ↥S → G) Subtype.val_injective
  haveI : Finite (↥S ⧸ (M.subgroupOf S)) :=
    Finite.of_surjective (QuotientGroup.mk' (M.subgroupOf S)) (QuotientGroup.mk'_surjective _)
  intro a ha
  set x : ↥S := ⟨a, ha⟩ with hx
  have h3 : orderOf (QuotientGroup.mk' (M.subgroupOf S) x : ↥S ⧸ (M.subgroupOf S)) ∣ 3 := by
    haveI : Fintype (↥S ⧸ (M.subgroupOf S)) := Fintype.ofFinite _
    have h := orderOf_dvd_card (x := (QuotientGroup.mk' (M.subgroupOf S) x : ↥S ⧸ (M.subgroupOf S)))
    rwa [← Nat.card_eq_fintype_card, hcard] at h
  have h1 : (QuotientGroup.mk' (M.subgroupOf S) x : ↥S ⧸ (M.subgroupOf S)) ^ 3 = 1 :=
    (orderOf_dvd_iff_pow_eq_one).mp h3
  have h2 : (QuotientGroup.mk' (M.subgroupOf S) (x ^ 3) : ↥S ⧸ (M.subgroupOf S)) = 1 := by
    rw [map_pow, h1]
  have h2' : (x ^ 3 : ↥S) ∈ M.subgroupOf S := (QuotientGroup.eq_one_iff (x ^ 3)).mp h2
  rw [Subgroup.mem_subgroupOf] at h2'
  have h4 : ((x : ↥S) ^ 3 : ↥S) = (⟨a ^ 3, S.pow_mem ha 3⟩ : ↥S) := by rw [hx]; rfl
  rw [h4] at h2'
  simpa using h2'

/-- Commutators land in `M` if the quotient `S/M` has order nine (a group of order `9` is
abelian, and every group of order `p ^ 2` is abelian). -/
theorem commutator_mem_of_card_quotient_nine {G : Type} [Group G] [Finite G] {M S : Subgroup G}
    (hMS : M ≤ S) (hN : S ≤ Subgroup.normalizer (M : Set G))
    (hcard : Nat.card (↥S ⧸ (M.subgroupOf S)) = 9) :
    ∀ a ∈ S, ∀ b ∈ S, ⁅a, b⁆ ∈ M := by
  haveI : (M.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMS).mpr hN
  haveI : Finite ↥S := Finite.of_injective (Subtype.val : ↥S → G) Subtype.val_injective
  haveI : Finite (↥S ⧸ (M.subgroupOf S)) :=
    Finite.of_surjective (QuotientGroup.mk' (M.subgroupOf S)) (QuotientGroup.mk'_surjective _)
  haveI hq : IsMulCommutative (↥S ⧸ (M.subgroupOf S)) :=
    isMulCommutative_of_card_eq_nine hcard
  intro a ha b hb
  set x : ↥S := ⟨a, ha⟩ with hx
  set y : ↥S := ⟨b, hb⟩ with hy
  have h2 : (QuotientGroup.mk' (M.subgroupOf S) ⁅x, y⁆ : ↥S ⧸ (M.subgroupOf S)) = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hq.is_comm.comm _ _)
  have h3 : (⁅x, y⁆ : ↥S) ∈ M.subgroupOf S := (QuotientGroup.eq_one_iff (⁅x, y⁆ : ↥S)).mp h2
  have h4 : ((⁅x, y⁆ : ↥S) : G) = ⁅a, b⁆ := by
    show (Subgroup.subtype S) ⁅x, y⁆ = ⁅a, b⁆
    rw [map_commutatorElement, hx, hy]
    rfl
  have h5 : (⁅a, b⁆ : G) ∈ M := by
    have h6 := Subgroup.mem_subgroupOf.mp h3
    rwa [h4] at h6
  exact h5



/-! ## The standing hypotheses of the argument, bundled -/

/-- The context of step (17b): the standing hypotheses plus the conclusions of the leaves
`T_sig_facts`, `P_on_L`, `A_LV_facts`, `A_stronglyReal_normalizer`, `A_weaklyClosed`,
`cst_center_sylow`, `cst_isPGroup`, `cP_inf_cst`. -/
structure Aux {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} {T : Subgroup G} {h15 : Chain15 H Q t s r P} where
  hFT : FeitThompsonProp
  hC4 : ChIIFourProp
  c : CtxF H Q t s r P
  h7 : Ker H Q P t = P
  hpf : Nat.card P = orderOf (s * t)
  h11 : Step11Out H Q t P h15.R T
  d : Case102 H Q t s P
  hTsig : (∀ σ ∈ Sig H t P, σ ≠ 1 → ∃ x ∈ T, σ * x * σ⁻¹ ≠ x) ∧
    (∀ a ∈ T, ∀ b ∈ Sig H t P, a * b * a⁻¹ * b⁻¹ ∈ Z1 s t) ∧
    T ⊓ CG (Sig H t P) = Z1 s t
  hPL : (∃ x ∈ P, ∃ y ∈ Lsub H s t, x * y ≠ y * x) ∧
    (∀ a ∈ Lsub H s t, ∀ b ∈ P, a * b * a⁻¹ * b⁻¹ ∈ Z1 s t)
  hALV : IsMulCommutative ↥(Asub H P s t) ∧ Nat.card ↥(Asub H P s t) = 27 ∧
    Z1 s t ⊓ (P ⊔ Sig H t P) = ⊥ ∧
    Nat.card ↥(Lsub H s t ⊔ centD H t) = 27 * Nat.card ↥(W H t) ∧
    Asub H P s t ≤ Lsub H s t ⊔ centD H t ∧
    (∀ x ∈ Lsub H s t ⊔ centD H t, x ^ 3 = 1 → x ∈ Asub H P s t) ∧
    (∀ a ∈ Z1 s t ⊔ Sig H t P, ∀ y ∈ Lsub H s t ⊔ centD H t, a * y = y * a)
  h16 : (∀ g : G, ∀ a ∈ Asub H P s t, StronglyReal (g * a * g⁻¹) → a ∈ Z1 s t) ∧
    NG (Asub H P s t) = Cst s t ⊔ Subgroup.zpowers s
  h17a : ∀ g : G, cj g (Asub H P s t) ≤ Cst s t → cj g (Asub H P s t) = Asub H P s t
  h14 : (∀ z ∈ Cst s t, (∀ y ∈ Cst s t, z * y = y * z) → z ∈ Z1 s t) ∧
    Nat.card ↥(Cst s t) = pPart 3 (Nat.card G)
  h13 : IsPGroup 3 ↥(Cst s t)
  h14b : CG P ⊓ Cst s t = h15.R ⊔ Sig H t P


section Assembling

variable {G : Type} [Group G] [Finite G]
variable {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
variable {T : Subgroup G} {h15 : Chain15 H Q t s r P}

/-- The elementary cardinality and containment facts of the context. -/
theorem aux_elem (A : Aux (H := H) (Q := Q) (t := t) (s := s) (r := r) (P := P) (T := T) (h15 := h15)) :
    Nat.card P = 3 ∧ Nat.card ↥h15.R = 27 ∧ Nat.card ↥(h15.R ⊔ Sig H t P) = 81 ∧
    Nat.card ↥(Z1 s t) = 3 ∧ Nat.card ↥(Lsub H s t) = 9 ∧ Nat.card ↥(Asub H P s t) = 27 ∧
    Nat.card ↥(Cst s t) = 81 * Nat.card ↥(W H t) ∧
    (Z1 s t ≤ T) ∧ (Z1 s t ≤ h15.R) ∧ (Z1 s t ≤ Lsub H s t) ∧ (T ≤ h15.R) ∧
    (T ≤ Cst s t) ∧ (h15.R ≤ Cst s t) ∧ (Lsub H s t ≤ Cst s t) ∧ (P ≤ Cst s t) ∧
    (Sig H t P ≤ Cst s t) ∧ (Sig H t P ≤ CG P) ∧ (Asub H P s t ≤ Cst s t) ∧
    (∀ x ∈ P, x ∈ h15.R) ∧ (centD H t ≤ Subgroup.centralizer ({s} : Set G)) ∧
    (s * (s * t) * s⁻¹ = (s * t)⁻¹) ∧ (Sig H t P ≤ centD H t) ∧
    (IsCyclic ↥(Lsub H s t) ∧ (∀ x ∈ Lsub H s t, s * x * s⁻¹ = x⁻¹) ∧
      s * t ∈ Lsub H s t) ∧
    ((∀ x ∈ T, s * x * s⁻¹ = x⁻¹) ∧ s * t ∈ T ∧ (∀ x ∈ T, x ^ 3 = 1) ∧ Nat.card ↥T = 9) := by
  obtain ⟨hFT, hC4, c, h7, hpf, h11, d, hTsig, hPL, hALV, h16, h17a, h14, h13, h14b⟩ := A
  refine ⟨card_P_case102 hpf d, card_R h15 h7 hpf d, card_RSig hFT hC4 c h15 h7 hpf d,
    card_Z1 d, (L_facts hFT hC4 c h15 d).2.1, hALV.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h14.2, d.G3]; norm_num
  · exact Z1_le_T hFT hC4 c h15 h7 hpf h11 d
  · exact Z1_le_R hFT hC4 c h15 h7 hpf h11 d
  · exact Z1_le_L hFT hC4 c h15 d
  · exact T_le_R h15 h11
  · exact T_le_Cst hFT hC4 c h15 h7 hpf h11 d
  · exact R_le_Cst hFT hC4 c h15 h7 hpf h11 d
  · exact Lsub_le_Cst
  · exact P_le_Cst c
  · exact Sig_le_Cst c
  · exact Sig_le_CGP
  · refine sup_le (sup_le ?_ (P_le_Cst c)) (Sig_le_Cst c)
    exact (Z1_le_T hFT hC4 c h15 h7 hpf h11 d).trans (T_le_Cst hFT hC4 c h15 h7 hpf h11 d)
  · exact fun x hx => h11.TPR ▸ (le_sup_right : P ≤ T ⊔ P) hx
  · exact Work.ThmF.Prove.centDLowerCentralizerS c.split c.s_mem c.s_inv c.r_mem c.sid
  · exact (T_facts hFT hC4 c h15 h7 hpf h11 d).1 (s * t) (T_facts hFT hC4 c h15 h7 hpf h11 d).2.1
  · exact (inf_le_left : Sig H t P ≤ W H t).trans (Work.ThmF.W_le_centD H t)
  · exact ⟨(L_facts hFT hC4 c h15 d).1, (L_facts hFT hC4 c h15 d).2.2.1,
      (L_facts hFT hC4 c h15 d).2.2.2⟩
  · exact T_facts hFT hC4 c h15 h7 hpf h11 d

/-- The normalizer facts of section 1. -/
theorem aux_basic1 (A : Aux (H := H) (Q := Q) (t := t) (s := s) (r := r) (P := P) (T := T)
    (h15 := h15)) :
    (∀ z ∈ Z1 s t, ∀ c ∈ Cst s t, z * c = c * z) ∧
    (P ≤ NG (Z1 s t)) ∧ (Sig H t P ≤ Subgroup.normalizer (P : Set G)) ∧
    (Lsub H s t ≤ NG (Z1 s t)) ∧ (Lsub H s t ≤ NG (Z1 s t ⊔ P)) ∧
    (Sig H t P ≤ NG (Z1 s t)) ∧ (Sig H t P ≤ NG (Z1 s t ⊔ P)) := by
  obtain ⟨hcardP, hcardR, hcardRSig, hcardZ1, hcardL, hA27, hCst81, hZ1T, hZ1R, hZ1L,
    hTR, hTC, hRC, hLC, hPC, hSigC, hSigP, hAC, hmemRP0, hcentD, hsinv, hSigV, hLfacts,
    hTfacts⟩ := aux_elem A
  obtain ⟨hFT, hC4, c, h7, hpf, h11, d, hTsig, hPL, hALV, h16, h17a, h14, h13, h14b⟩ := A
  have hmemRP : ∀ {x : G}, x ∈ P → x ∈ h15.R := fun {x} hx => hmemRP0 x hx
  have hZ1_Cst_comm : ∀ z ∈ Z1 s t, ∀ a ∈ Cst s t, z * a = a * z := by
    intro z hz a ha
    have hast : a * (s * t) = (s * t) * a := Subgroup.mem_centralizer_singleton_iff.mp ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((show Commute a (s * t) from hast).zpow_right k).eq.symm
  have hPZ1 : P ≤ NG (Z1 s t) := by
    intro p hp
    rw [← cj_eq_self_iff]
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_cj])
    intro y hx
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hx
    have hzy' : p * z * p⁻¹ = y := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hzy
    rw [← hzy']
    have hcomm : p * z = z * p :=
      mul_comm_of_mem h11.comm (hmemRP hp) (hTR (hZ1T hz))
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact hz
  have hSigNormP : Sig H t P ≤ Subgroup.normalizer (P : Set G) :=
    hSigP.trans (Subgroup.centralizer_le_normalizer (P : Set G))
  have hLZ1 : Lsub H s t ≤ NG (Z1 s t) := by
    intro a ha
    rw [← cj_eq_self_iff]
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_cj])
    intro y hx
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hx
    have hzy' : a * z * a⁻¹ = y := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hzy
    rw [← hzy', ← hZ1_Cst_comm z hz a (hLC ha), mul_assoc, mul_inv_cancel, mul_one]
    exact hz
  have hLZ1P : Lsub H s t ≤ NG (Z1 s t ⊔ P) := by
    intro a ha
    rw [← cj_eq_self_iff]
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_cj])
    intro y hx
    obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hx
    have hwy' : a * w * a⁻¹ = y := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hwy
    rw [← hwy']
    obtain ⟨z, hz, q, hq, hzq⟩ := (mem_sup_of_le_normalizer hPZ1).mp hw
    have haz : a * z * a⁻¹ = z := by
      rw [← hZ1_Cst_comm z hz a (hLC ha), mul_assoc, mul_inv_cancel, mul_one]
    have hap : a * q * a⁻¹ ∈ Z1 s t ⊔ P := by
      have h1 : a * q * a⁻¹ * q⁻¹ ∈ Z1 s t := hPL.2 a ha q hq
      rw [show a * q * a⁻¹ = (a * q * a⁻¹ * q⁻¹) * q from by group]
      exact Subgroup.mul_mem_sup h1 hq
    have hzq' : a * (z * q) * a⁻¹ = (a * z * a⁻¹) * (a * q * a⁻¹) := by group
    rw [← hzq, hzq', haz]
    exact (Z1 s t ⊔ P).mul_mem (Subgroup.mem_sup_left hz) hap
  have hSigZ1 : Sig H t P ≤ NG (Z1 s t) := by
    intro σ hσ
    rw [← cj_eq_self_iff]
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_cj])
    intro y hx
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hx
    have hzy' : σ * z * σ⁻¹ = y := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hzy
    rw [← hzy', ← hZ1_Cst_comm z hz σ (hSigC hσ), mul_assoc, mul_inv_cancel, mul_one]
    exact hz
  have hSigZ1P : Sig H t P ≤ NG (Z1 s t ⊔ P) := by
    intro σ hσ
    rw [← cj_eq_self_iff]
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_cj])
    intro y hx
    obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hx
    have hwy' : σ * w * σ⁻¹ = y := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hwy
    rw [← hwy']
    obtain ⟨z, hz, q, hq, hzq⟩ := (mem_sup_of_le_normalizer hPZ1).mp hw
    have hσz : σ * z * σ⁻¹ = z := by
      rw [← hZ1_Cst_comm z hz σ (hSigC hσ), mul_assoc, mul_inv_cancel, mul_one]
    have hσp : σ * q * σ⁻¹ = q := by
      have h1 : q * σ = σ * q := Subgroup.mem_centralizer_iff.mp (hSigP hσ) q hq
      rw [← h1]; group
    have hzq' : σ * (z * q) * σ⁻¹ = (σ * z * σ⁻¹) * (σ * q * σ⁻¹) := by group
    rw [← hzq, hzq', hσz, hσp]
    exact Subgroup.mul_mem_sup hz hq
  exact ⟨hZ1_Cst_comm, hPZ1, hSigNormP, hLZ1, hLZ1P, hSigZ1, hSigZ1P⟩

/-- Section 2: `C_G(Z₁P) = RΣ`, `L ≤ N(RΣ)`, `|RΣL| = 243`. -/
theorem aux_basic2 (A : Aux (H := H) (Q := Q) (t := t) (s := s) (r := r) (P := P) (T := T)
    (h15 := h15))
    (hZ1_Cst_comm : ∀ z ∈ Z1 s t, ∀ c ∈ Cst s t, z * c = c * z)
    (hPZ1 : P ≤ NG (Z1 s t)) (hLZ1 : Lsub H s t ≤ NG (Z1 s t))
    (hLZ1P : Lsub H s t ≤ NG (Z1 s t ⊔ P)) (hSigZ1 : Sig H t P ≤ NG (Z1 s t))
    (hSigC : Sig H t P ≤ Cst s t) (hSigP : Sig H t P ≤ CG P)
    (hRC : h15.R ≤ Cst s t) (hcardRSig : Nat.card ↥(h15.R ⊔ Sig H t P) = 81)
    (hcardL : Nat.card ↥(Lsub H s t) = 9) (hcardZ1 : Nat.card ↥(Z1 s t) = 3)
    (hIL : Lsub H s t ⊓ (h15.R ⊔ Sig H t P) = Z1 s t) (hZ1R : Z1 s t ≤ h15.R)
    (hmemRP : ∀ {x : G}, x ∈ P → x ∈ h15.R) :
    (Subgroup.centralizer ((Z1 s t ⊔ P : Subgroup G) : Set G) = h15.R ⊔ Sig H t P) ∧
    (Lsub H s t ≤ NG (h15.R ⊔ Sig H t P)) ∧
    (Nat.card ↥(h15.R ⊔ Sig H t P ⊔ Lsub H s t) = 243) := by
  obtain ⟨hFT, hC4, c, h7, hpf, h11, d, hTsig, hPL, hALV, h16, h17a, h14, h13, h14b⟩ := A
  have hZ1P_CG : Subgroup.centralizer ((Z1 s t ⊔ P : Subgroup G) : Set G) = h15.R ⊔ Sig H t P := by
    refine le_antisymm ?_ ?_
    · intro x hx
      have hxP : x ∈ CG P := Subgroup.mem_centralizer_iff.mpr (fun p hp =>
        Subgroup.mem_centralizer_iff.mp hx p (Subgroup.mem_sup_right hp))
      have hxst : x * (s * t) = (s * t) * x :=
        (Subgroup.mem_centralizer_iff.mp hx (s * t)
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers (s * t)))).symm
      have hxC : x ∈ Cst s t := Subgroup.mem_centralizer_singleton_iff.mpr hxst
      have hx2 : x ∈ CG P ⊓ Cst s t := ⟨hxP, hxC⟩
      rwa [h14b] at hx2
    · intro x hx
      obtain ⟨r, hr, σ, hσ, hrσ⟩ := (mem_sup_of_le_normalizer (hSigP.trans h15.hRn)).mp hx
      refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
      obtain ⟨z, hz, p, hp, hzp⟩ := (mem_sup_of_le_normalizer hPZ1).mp hy
      have hrz : r * z = z * r := mul_comm_of_mem h11.comm hr (hZ1R hz)
      have hrp : r * p = p * r := mul_comm_of_mem h11.comm hr (hmemRP hp)
      have hσz : σ * z = z * σ := (hZ1_Cst_comm z hz σ (hSigC hσ)).symm
      have hσp : σ * p = p * σ := (Subgroup.mem_centralizer_iff.mp (hSigP hσ) p hp).symm
      rw [← hrσ, ← hzp]
      calc (z * p) * (r * σ) = z * (p * r) * σ := by group
        _ = z * (r * p) * σ := by rw [← hrp]
        _ = (z * r) * (p * σ) := by group
        _ = (r * z) * (σ * p) := by rw [← hrz, ← hσp]
        _ = r * (z * σ) * p := by group
        _ = r * (σ * z) * p := by rw [← hσz]
        _ = (r * σ) * (z * p) := by group
  have hLR : Lsub H s t ≤ NG (h15.R ⊔ Sig H t P) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha
    have ha_inv : a⁻¹ ∈ Lsub H s t := Subgroup.inv_mem (Lsub H s t) ha
    rw [← hZ1P_CG]
    intro y hy
    refine Subgroup.mem_centralizer_iff.mpr (fun z hz => ?_)
    have hz' : a⁻¹ * z * a ∈ Z1 s t ⊔ P := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hLZ1P ha_inv) z).mp hz
    have hcomm : (a⁻¹ * z * a) * y = y * (a⁻¹ * z * a) :=
      Subgroup.mem_centralizer_iff.mp hy (a⁻¹ * z * a) hz'
    calc z * (a * y * a⁻¹) = a * ((a⁻¹ * z * a) * y) * a⁻¹ := by group
      _ = a * (y * (a⁻¹ * z * a)) * a⁻¹ := by rw [hcomm]
      _ = (a * y * a⁻¹) * z := by group
  refine ⟨hZ1P_CG, hLR, ?_⟩
  have h := card_sup_mul_card_inf_of_le_normalizer (H := h15.R ⊔ Sig H t P)
    (K := Lsub H s t) hLR
  rw [hcardRSig, hcardL, inf_comm, hIL, hcardZ1] at h
  omega

/-- Section 3: `[A,T] ⊆ Z₁` and `[A,L] ⊆ Z₁`. -/
theorem aux_basic3 (A : Aux (H := H) (Q := Q) (t := t) (s := s) (r := r) (P := P) (T := T)
    (h15 := h15))
    (hZ1_Cst_comm : ∀ z ∈ Z1 s t, ∀ c ∈ Cst s t, z * c = c * z)
    (hPZ1 : P ≤ NG (Z1 s t)) (hSigZ1 : Sig H t P ≤ NG (Z1 s t))
    (hSigZ1P : Sig H t P ≤ NG (Z1 s t ⊔ P))
    (hSigNormP : Sig H t P ≤ Subgroup.normalizer (P : Set G))
    (hZ1T : Z1 s t ≤ T) (hZ1L : Z1 s t ≤ Lsub H s t) (hTR : T ≤ h15.R) (hLC : Lsub H s t ≤ Cst s t)
    (hSigC : Sig H t P ≤ Cst s t) (hSigP : Sig H t P ≤ CG P)
    (hmemRP : ∀ {x : G}, x ∈ P → x ∈ h15.R) :
    (⁅Asub H P s t, T⁆ ≤ Z1 s t) ∧ (⁅Asub H P s t, Lsub H s t⁆ ≤ Z1 s t) := by
  obtain ⟨hFT, hC4, c, h7, hpf, h11, d, hTsig, hPL, hALV, h16, h17a, h14, h13, h14b⟩ := A
  have hST_le : ⁅Sig H t P, T⁆ ≤ Z1 s t := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_le.mpr hTsig.2.1
  have hInnerAT : ∀ t' ∈ T, ∀ a ∈ Z1 s t ⊔ P, ⁅a, t'⁆ ∈ Z1 s t := by
    intro t' ht'
    refine commutator_mem_of_sup (Z := Z1 s t) (A₁ := Z1 s t) (A₂ := P)
      Subgroup.le_normalizer hPZ1 hPZ1 ?_ ?_
    · intro z hz
      have hcomm : z * t' = t' * z :=
        mul_comm_of_mem h11.comm (hTR (hZ1T hz)) (hTR ht')
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
      exact Subgroup.one_mem _
    · intro p hp
      have hcomm : p * t' = t' * p :=
        mul_comm_of_mem h11.comm (hmemRP hp) (hTR ht')
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
      exact Subgroup.one_mem _
  have hAT : ⁅Asub H P s t, T⁆ ≤ Z1 s t := by
    rw [Subgroup.commutator_le]
    intro a ha t' ht'
    exact commutator_mem_of_sup (Z := Z1 s t) (A₁ := Z1 s t ⊔ P) (A₂ := Sig H t P)
      (sup_le Subgroup.le_normalizer hPZ1) hSigZ1 (le_normalizer_sup hSigZ1 hSigNormP)
      (fun x hx => hInnerAT t' ht' x hx)
      (fun σ hσ => Subgroup.commutator_le.mp hST_le σ hσ t' ht') a ha
  have hPL_le : ⁅P, Lsub H s t⁆ ≤ Z1 s t := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_le.mpr hPL.2
  have hInnerAL : ∀ l ∈ Lsub H s t, ∀ a ∈ Z1 s t ⊔ P, ⁅a, l⁆ ∈ Z1 s t := by
    intro l hl
    refine commutator_mem_of_sup (Z := Z1 s t) (A₁ := Z1 s t) (A₂ := P)
      Subgroup.le_normalizer hPZ1 hPZ1 ?_ ?_
    · intro z hz
      rw [show ⁅z, l⁆ = 1 from
        commutatorElement_eq_one_iff_mul_comm.mpr (hZ1_Cst_comm z hz l (hLC hl))]
      exact Subgroup.one_mem _
    · intro p hp
      exact Subgroup.commutator_le.mp hPL_le p hp l hl
  have hSigL_le : ⁅Sig H t P, Lsub H s t⁆ ≤ Z1 s t := by
    rw [Subgroup.commutator_le]
    intro σ hσ l hl
    have hσc : σ ∈ Subgroup.centralizer (Work.ThmF.Lemma5.X5 H t : Set G) :=
      W_le_centralizer_X5 hC4 c.sit c.split (Subgroup.mem_inf.mp hσ).1
    have hlX : l ∈ Work.ThmF.Lemma5.X5 H t := (Subgroup.mem_inf.mp hl).1
    have hcomm : l * σ = σ * l := Subgroup.mem_centralizer_iff.mp hσc l hlX
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm]
    exact Subgroup.one_mem _
  have hAL : ⁅Asub H P s t, Lsub H s t⁆ ≤ Z1 s t := by
    rw [Subgroup.commutator_le]
    intro a ha l hl
    exact commutator_mem_of_sup (Z := Z1 s t) (A₁ := Z1 s t ⊔ P) (A₂ := Sig H t P)
      (sup_le Subgroup.le_normalizer hPZ1) hSigZ1 (le_normalizer_sup hSigZ1 hSigNormP)
      (fun x hx => hInnerAL l hl x hx)
      (fun σ hσ => Subgroup.commutator_le.mp hSigL_le σ hσ l hl) a ha
  exact ⟨hAT, hAL⟩

/-- Section 4: `A ⊴ Cst` and the `s`-normalizers. -/
theorem aux_basic4 (A : Aux (H := H) (Q := Q) (t := t) (s := s) (r := r) (P := P) (T := T)
    (h15 := h15))
    (hAC : Asub H P s t ≤ Cst s t) (hLC : Lsub H s t ≤ Cst s t) (hPC : P ≤ Cst s t)
    (hSigC : Sig H t P ≤ Cst s t) (hSigV : Sig H t P ≤ centD H t)
    (hcentD : centD H t ≤ Subgroup.centralizer ({s} : Set G))
    (hsinv : s * (s * t) * s⁻¹ = (s * t)⁻¹)
    (hTfacts : (∀ x ∈ T, s * x * s⁻¹ = x⁻¹) ∧ s * t ∈ T ∧ (∀ x ∈ T, x ^ 3 = 1) ∧
      Nat.card ↥T = 9) :
    (Cst s t ≤ NG (Asub H P s t)) ∧ (s ∈ NG (Asub H P s t)) ∧ (s ∈ NG (Cst s t)) ∧
    (s ∈ NG T) ∧ (s ∈ NG P) ∧ (s ∈ NG (Lsub H s t)) ∧ (s ∈ NG h15.R) := by
  obtain ⟨hFT, hC4, c, h7, hpf, h11, d, hTsig, hPL, hALV, h16, h17a, h14, h13, h14b⟩ := A
  have hA_normal : Cst s t ≤ NG (Asub H P s t) := by
    intro g hg
    rw [← cj_eq_self_iff]
    refine h17a g ?_
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
    have hxy' : g * y * g⁻¹ = x := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hxy
    rw [← hxy']
    exact (Cst s t).mul_mem ((Cst s t).mul_mem hg (hAC hy)) ((Cst s t).inv_mem hg)
  have hsT : s ∈ NG T := by
    rw [← cj_eq_self_iff]
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_cj])
    intro y hx
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hx
    have hzy' : s * z * s⁻¹ = y := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hzy
    rw [← hzy', hTfacts.1 z hz]
    exact T.inv_mem hz
  have hsP : s ∈ NG P := by
    rw [← cj_eq_self_iff]
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_cj])
    intro y hx
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hx
    have hzy' : s * z * s⁻¹ = y := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hzy
    rw [← hzy']
    have hcs : z * s = s * z := Subgroup.mem_centralizer_singleton_iff.mp (hcentD (c.P_le hz))
    rw [show s * z * s⁻¹ = z from by rw [← hcs]; group]
    exact hz
  have hsL : s ∈ NG (Lsub H s t) := by
    rw [← cj_eq_self_iff]
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_cj])
    intro y hx
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hx
    have hzy' : s * z * s⁻¹ = y := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hzy
    rw [← hzy', (L_facts hFT hC4 c h15 d).2.2.1 z hz]
    exact (Lsub H s t).inv_mem hz
  have hsR : s ∈ NG h15.R := by
    rw [← cj_eq_self_iff, ← h11.TPR, cj, Subgroup.map_sup]
    congr 1
    · exact (cj_eq_self_iff s T).mpr hsT
    · exact (cj_eq_self_iff s P).mpr hsP
  have hsA : s ∈ NG (Asub H P s t) := by
    have hZ1c : (Z1 s t).map (MulAut.conj s).toMonoidHom = Z1 s t := by
      show (Subgroup.zpowers (s * t)).map (MulAut.conj s).toMonoidHom = Subgroup.zpowers (s * t)
      rw [map_zpowers_conj, hsinv]
      refine le_antisymm ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_zpowers_iff.mpr ⟨-1, zpow_neg_one (s * t)⟩
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_zpowers_iff.mpr ⟨-1, by rw [zpow_neg_one, inv_inv]⟩
    have hPc : P.map (MulAut.conj s).toMonoidHom = P := by
      simpa only [cj] using (cj_eq_self_iff s P).mpr hsP
    have hSigc : (Sig H t P).map (MulAut.conj s).toMonoidHom = Sig H t P := by
      have h1 : s ∈ NG (Sig H t P) := by
        rw [← cj_eq_self_iff]
        refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_cj])
        intro y hx
        obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hx
        have hzy' : s * z * s⁻¹ = y := by
          simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hzy
        rw [← hzy']
        have hcs : z * s = s * z := Subgroup.mem_centralizer_singleton_iff.mp (hcentD (hSigV hz))
        rw [show s * z * s⁻¹ = z from by rw [← hcs]; group]
        exact hz
      simpa only [cj] using (cj_eq_self_iff s (Sig H t P)).mpr h1
    rw [← cj_eq_self_iff, cj, Subgroup.map_sup, Subgroup.map_sup, hZ1c, hPc, hSigc]
  have hsCst : s ∈ NG (Cst s t) := by
    rw [Cst, ← cj_eq_self_iff]
    show (Subgroup.centralizer ({s * t} : Set G)).map (MulAut.conj s).toMonoidHom
      = Subgroup.centralizer ({s * t} : Set G)
    rw [map_centralizer_singleton, hsinv, centralizer_singleton_inv]
  exact ⟨hA_normal, hsA, hsCst, hsT, hsP, hsL, hsR⟩

/-- Case `|W| = 3`. -/
theorem aux_case3 (A : Aux (H := H) (Q := Q) (t := t) (s := s) (r := r) (P := P) (T := T)
    (h15 := h15)) (hW3 : Nat.card ↥(W H t) = 3)
    (B1 : (∀ z ∈ Z1 s t, ∀ c ∈ Cst s t, z * c = c * z) ∧
      (P ≤ NG (Z1 s t)) ∧ (Sig H t P ≤ Subgroup.normalizer (P : Set G)) ∧
      (Lsub H s t ≤ NG (Z1 s t)) ∧ (Lsub H s t ≤ NG (Z1 s t ⊔ P)) ∧
      (Sig H t P ≤ NG (Z1 s t)) ∧ (Sig H t P ≤ NG (Z1 s t ⊔ P)))
    (B2 : (Subgroup.centralizer ((Z1 s t ⊔ P : Subgroup G) : Set G) = h15.R ⊔ Sig H t P) ∧
      (Lsub H s t ≤ NG (h15.R ⊔ Sig H t P)) ∧
      (Nat.card ↥(h15.R ⊔ Sig H t P ⊔ Lsub H s t) = 243))
    (B3 : (⁅Asub H P s t, T⁆ ≤ Z1 s t) ∧ (⁅Asub H P s t, Lsub H s t⁆ ≤ Z1 s t))
    (B4 : (Cst s t ≤ NG (Asub H P s t)) ∧ (s ∈ NG (Asub H P s t)) ∧ (s ∈ NG (Cst s t)) ∧
      (s ∈ NG T) ∧ (s ∈ NG P) ∧ (s ∈ NG (Lsub H s t)) ∧ (s ∈ NG h15.R))
    (hE : Nat.card P = 3 ∧ Nat.card ↥h15.R = 27 ∧ Nat.card ↥(h15.R ⊔ Sig H t P) = 81 ∧
      Nat.card ↥(Z1 s t) = 3 ∧ Nat.card ↥(Lsub H s t) = 9 ∧ Nat.card ↥(Asub H P s t) = 27 ∧
      Nat.card ↥(Cst s t) = 81 * Nat.card ↥(W H t) ∧ (Z1 s t ≤ T) ∧ (Z1 s t ≤ h15.R) ∧
      (Z1 s t ≤ Lsub H s t) ∧ (T ≤ h15.R) ∧ (T ≤ Cst s t) ∧ (h15.R ≤ Cst s t) ∧
      (Lsub H s t ≤ Cst s t) ∧ (P ≤ Cst s t) ∧ (Sig H t P ≤ Cst s t) ∧ (Sig H t P ≤ CG P) ∧
      (Asub H P s t ≤ Cst s t) ∧ (∀ x ∈ P, x ∈ h15.R) ∧
      (centD H t ≤ Subgroup.centralizer ({s} : Set G)) ∧
      (s * (s * t) * s⁻¹ = (s * t)⁻¹) ∧ (Sig H t P ≤ centD H t) ∧
      (IsCyclic ↥(Lsub H s t) ∧ (∀ x ∈ Lsub H s t, s * x * s⁻¹ = x⁻¹) ∧
        s * t ∈ Lsub H s t) ∧
      ((∀ x ∈ T, s * x * s⁻¹ = x⁻¹) ∧ s * t ∈ T ∧ (∀ x ∈ T, x ^ 3 = 1) ∧ Nat.card ↥T = 9)) :
    HasNormalIndexP 3 ↥(NG (Asub H P s t)) := by
  obtain ⟨hFT, hC4, c, h7, hpf, h11, d, hTsig, hPL, hALV, h16, h17a, h14, h13, h14b⟩ := A
  obtain ⟨hZ1_Cst_comm, hPZ1, hSigNormP, hLZ1, hLZ1P, hSigZ1, hSigZ1P⟩ := B1
  obtain ⟨hZ1P_CG, hLR, hcardRSL0⟩ := B2
  obtain ⟨hAT, hAL⟩ := B3
  obtain ⟨hA_normal, hsA, hsCst, hsT, hsP, hsL, hsR⟩ := B4
  obtain ⟨hcardP, hcardR, hcardRSig, hcardZ1, hcardL, hA27, hCst81, hZ1T, hZ1R, hZ1L, hTR,
    hTC, hRC, hLC, hPC, hSigC, hSigP, hAC, hmemRP0, hcentD, hsinv, hSigV, hLfacts,
    hTfacts⟩ := hE
  have hmemRP : ∀ {x : G}, x ∈ P → x ∈ h15.R := fun {x} hx => hmemRP0 x hx
  have hcardRSL : Nat.card ↥(h15.R ⊔ Sig H t P ⊔ Lsub H s t) = 243 := hcardRSL0
  have hcardCst : Nat.card ↥(Cst s t) = 243 := by rw [hCst81, hW3]
  have hCst_RSL : h15.R ⊔ Sig H t P ⊔ Lsub H s t = Cst s t := by
    have hcard : Nat.card ↥(Cst s t) ≤ Nat.card ↥(h15.R ⊔ Sig H t P ⊔ Lsub H s t) := by
      rw [hcardCst, hcardRSL]
    exact Subgroup.eq_of_le_of_card_ge (sup_le (sup_le hRC hSigC) hLC) hcard
  have hRSL_le_MPS : h15.R ⊔ Sig H t P ⊔ Lsub H s t ≤ (T ⊔ Lsub H s t) ⊔ P ⊔ Sig H t P := by
    have hTP : (T ⊔ P) ⊔ Sig H t P ⊔ Lsub H s t ≤ (T ⊔ Lsub H s t) ⊔ P ⊔ Sig H t P := by
      have hA : T ≤ T ⊔ Lsub H s t := le_sup_left
      have hB : T ⊔ Lsub H s t ≤ (T ⊔ Lsub H s t) ⊔ P := le_sup_left
      have hTP1 : T ⊔ P ≤ (T ⊔ Lsub H s t) ⊔ P := sup_le (hA.trans hB) le_sup_right
      have hTP2 : T ⊔ P ≤ (T ⊔ Lsub H s t) ⊔ P ⊔ Sig H t P := hTP1.trans le_sup_left
      have hC : Lsub H s t ≤ T ⊔ Lsub H s t := le_sup_right
      have hD : T ⊔ Lsub H s t ≤ (T ⊔ Lsub H s t) ⊔ P := le_sup_left
      have hE : (T ⊔ Lsub H s t) ⊔ P ≤ (T ⊔ Lsub H s t) ⊔ P ⊔ Sig H t P := le_sup_left
      exact sup_le (sup_le hTP2 le_sup_right) ((hC.trans hD).trans hE)
    rw [← h11.TPR]
    exact hTP
  have hMPS_le : (T ⊔ Lsub H s t) ⊔ P ⊔ Sig H t P ≤ Cst s t :=
    sup_le (sup_le (sup_le hTC hLC) hPC) hSigC
  have hMPC : (T ⊔ Lsub H s t) ⊔ P ⊔ Sig H t P = Cst s t := by
    refine Subgroup.eq_of_le_of_card_ge hMPS_le ?_
    rw [← hCst_RSL]
    exact card_le_card_of_le hRSL_le_MPS
  have hMPC' : T ⊔ Lsub H s t ⊔ (P ⊔ Sig H t P) = Cst s t := by
    rw [← sup_assoc]; exact hMPC
  have hMle : T ⊔ Lsub H s t ≤ Cst s t := by
    rw [← hMPC']; exact le_sup_left
  have hPM : P ≤ NG (T ⊔ Lsub H s t) := by
    refine le_normalizer_sup ?_ ?_
    · rw [Subgroup.le_normalizer_iff]
      intro p hp y hy
      have hcomm : p * y = y * p := mul_comm_of_mem h11.comm (hmemRP hp) (hTR hy)
      have h2 : p * y * p⁻¹ = y := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [h2]
      exact hy
    · rw [Subgroup.le_normalizer_iff_commutator_le_right]
      have h1 : ⁅P, Lsub H s t⁆ ≤ Z1 s t := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_le.mpr hPL.2
      exact h1.trans hZ1L
  have hSigM : Sig H t P ≤ NG (T ⊔ Lsub H s t) := by
    refine le_normalizer_sup ?_ ?_
    · rw [Subgroup.le_normalizer_iff_commutator_le_right, Subgroup.commutator_comm]
      exact (Subgroup.commutator_le.mpr hTsig.2.1).trans hZ1T
    · refine le_normalizer_of_forall_mul_comm ?_
      intro l hl σ hσ
      have hσc : σ ∈ Subgroup.centralizer (Work.ThmF.Lemma5.X5 H t : Set G) :=
        W_le_centralizer_X5 hC4 c.sit c.split (Subgroup.mem_inf.mp hσ).1
      have hlX : l ∈ Work.ThmF.Lemma5.X5 H t := (Subgroup.mem_inf.mp hl).1
      exact Subgroup.mem_centralizer_iff.mp hσc l hlX
  have hM_normal : Cst s t ≤ NG (T ⊔ Lsub H s t) := by
    rw [← hMPC]
    exact sup_le (sup_le Subgroup.le_normalizer hPM) hSigM
  have hsM : s ∈ NG (T ⊔ Lsub H s t) :=
    le_normalizer_sup (Subgroup.zpowers_le.mpr hsT) (Subgroup.zpowers_le.mpr hsL)
      (Subgroup.mem_zpowers s)
  have hPcomm : ∀ a ∈ P ⊔ Sig H t P, ∀ b ∈ P ⊔ Sig H t P, a * b = b * a :=
    mul_comm_of_sup (fun a ha a' ha' =>
        mul_comm_of_mem (isMulCommutative_of_card_eq_three hcardP) ha ha')
      (fun a ha a' ha' =>
        mul_comm_of_mem (isMulCommutative_of_card_eq_three d.sig3) ha ha')
      (fun a ha b hb => Subgroup.mem_centralizer_iff.mp (hSigP hb) a ha)
  have hPKexp : ∀ a ∈ P ⊔ Sig H t P, a ^ 3 = 1 :=
    pow_three_eq_one_of_sup (fun a ha => by
        haveI : Fintype ↥P := Fintype.ofFinite _
        have h1 : orderOf (⟨a, ha⟩ : ↥P) ∣ 3 := by
          have h := orderOf_dvd_card (x := (⟨a, ha⟩ : ↥P))
          rwa [← Nat.card_eq_fintype_card, hcardP] at h
        have h2 : (⟨a, ha⟩ : ↥P) ^ 3 = 1 := (orderOf_dvd_iff_pow_eq_one).mp h1
        simpa using congrArg (fun z : ↥P => (z : G)) h2)
      (fun a ha => by
        haveI : Fintype ↥(Sig H t P) := Fintype.ofFinite _
        have h1 : orderOf (⟨a, ha⟩ : ↥(Sig H t P)) ∣ 3 := by
          have h := orderOf_dvd_card (x := (⟨a, ha⟩ : ↥(Sig H t P)))
          rwa [← Nat.card_eq_fintype_card, d.sig3] at h
        have h2 : (⟨a, ha⟩ : ↥(Sig H t P)) ^ 3 = 1 := (orderOf_dvd_iff_pow_eq_one).mp h1
        simpa using congrArg (fun z : ↥(Sig H t P) => (z : G)) h2)
      (fun a ha b hb => Subgroup.mem_centralizer_iff.mp (hSigP hb) a ha)
  have hK_M : P ⊔ Sig H t P ≤ NG (T ⊔ Lsub H s t) := sup_le hPM hSigM
  have hab : ∀ a ∈ Cst s t, ∀ b ∈ Cst s t, a * b * a⁻¹ * b⁻¹ ∈ T ⊔ Lsub H s t := by
    intro a ha b hb
    obtain ⟨m, hm, y, hy, hmy⟩ := (mem_sup_of_le_normalizer hK_M).mp (hMPC'.symm ▸ ha)
    obtain ⟨m', hm', y', hy', hmy'⟩ := (mem_sup_of_le_normalizer hK_M).mp (hMPC'.symm ▸ hb)
    rw [← hmy, ← hmy']
    exact commutator_mem_of_le_normalizer_sup hK_M hPcomm hm hy hm' hy'
  have hpow : ∀ a ∈ Cst s t, a ^ 3 ∈ T ⊔ Lsub H s t := by
    intro a ha
    obtain ⟨m, hm, y, hy, hmy⟩ := (mem_sup_of_le_normalizer hK_M).mp (hMPC'.symm ▸ ha)
    obtain ⟨m', hm', hmeq⟩ := pow_mem_of_le_normalizer_sup hK_M hm hy 3
    rw [← hmy, hmeq, hPKexp y hy, mul_one]
    exact hm'
  have hCs : ∀ c2 ∈ Cst s t, ⁅c2, s⁆ ∈ T ⊔ Lsub H s t := by
    intro c2 hc
    obtain ⟨m, hm, y, hy, hmy⟩ := (mem_sup_of_le_normalizer hK_M).mp (hMPC'.symm ▸ hc)
    rw [← hmy, commutatorElement_mul_left_eq_conj_mul]
    have hy_s : ⁅y, s⁆ = 1 := by
      obtain ⟨p, hp, σ, hσ, hpy⟩ := (mem_sup_of_le_normalizer hSigNormP).mp hy
      have hp_s : p * s = s * p := Subgroup.mem_centralizer_singleton_iff.mp (hcentD (c.P_le hp))
      have hσ_s : σ * s = s * σ := Subgroup.mem_centralizer_singleton_iff.mp (hcentD (hSigV hσ))
      rw [← hpy]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (by
        calc (p * σ) * s = p * (σ * s) := by group
          _ = p * (s * σ) := by rw [hσ_s]
          _ = s * (p * σ) := by rw [← mul_assoc, hp_s, mul_assoc])
    rw [hy_s]
    have h6 : m * 1 * m⁻¹ * ⁅m, s⁆ = ⁅m, s⁆ := by group
    rw [h6]
    have hm3 : s * m⁻¹ * s⁻¹ ∈ T ⊔ Lsub H s t :=
      (Subgroup.mem_normalizer_iff.mp hsM m⁻¹).mp (Subgroup.inv_mem _ hm)
    have h7 : ⁅m, s⁆ = m * (s * m⁻¹ * s⁻¹) := by
      unfold commutatorElement; group
    rw [h7]
    exact Subgroup.mul_mem _ hm hm3
  have hCstA : ∀ a ∈ Cst s t, ∀ b ∈ Cst s t, ⁅a, b⁆ ∈ Asub H P s t :=
    commutator_mem_of_card_quotient_nine hAC hA_normal (by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((Asub H P s t).subgroupOf (Cst s t))
      rw [card_subgroupOf_eq_card_inf, inf_eq_left.mpr hAC, hA27, hcardCst] at h1
      omega)
  have hTLA : ∀ a ∈ T, ∀ b ∈ Lsub H s t, ⁅a, b⁆ ∈ Asub H P s t := by
    have h2 : ⁅Cst s t, Cst s t⁆ ≤ Asub H P s t := Subgroup.commutator_le.mpr hCstA
    exact fun a ha b hb =>
      Subgroup.commutator_le.mp ((Subgroup.commutator_mono hTC hLC).trans h2) a ha b hb
  obtain ⟨xT, hxT, hxZ1⟩ : ∃ x ∈ T, x ∉ Z1 s t := by
    by_contra h
    push_neg at h
    have := card_le_card_of_le (h : T ≤ Z1 s t)
    rw [hTfacts.2.2.2, hcardZ1] at this
    omega
  obtain ⟨l, hl_mem, hl9, hl3⟩ : ∃ l ∈ Lsub H s t, orderOf l = 9 ∧ l ^ 3 ∈ Z1 s t := by
    haveI : IsCyclic ↥(Lsub H s t) := hLfacts.1
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(Lsub H s t))
    refine ⟨(g : G), g.2, ?_, ?_⟩
    · have h1 : Nat.card ↥(Subgroup.zpowers ((g : G))) = Nat.card ↥(Subgroup.zpowers g) := by
        have h := Subgroup.card_map_of_injective (K := Subgroup.zpowers g)
          (f := Subgroup.subtype (Lsub H s t)) (Subgroup.subtype_injective _)
        simpa only [MonoidHom.map_zpowers, Subgroup.subtype_apply] using h
      rw [← Nat.card_zpowers ((g : G)), h1, Nat.card_zpowers g, hg, hcardL]
    · exact pow_mem_of_card_quotient_three hZ1L hLZ1 (by
        have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((Z1 s t).subgroupOf (Lsub H s t))
        rw [card_subgroupOf_eq_card_inf, inf_eq_left.mpr hZ1L, hcardZ1, hcardL] at h1
        omega) (g : G) g.2
  have hT_eq : Z1 s t ⊔ Subgroup.zpowers xT = T := by
    set n := Nat.card ↥(Z1 s t ⊔ Subgroup.zpowers xT) with hn
    have hleT : Z1 s t ⊔ Subgroup.zpowers xT ≤ T :=
      sup_le hZ1T (Subgroup.zpowers_le.mpr hxT)
    have hdvd : n ∣ 9 := by
      rw [hn, ← hTfacts.2.2.2]
      exact Subgroup.card_dvd_of_le hleT
    have hgt : 3 < n := by
      rw [hn]
      have hle : Nat.card ↥(Z1 s t) ≤ Nat.card ↥(Z1 s t ⊔ Subgroup.zpowers xT) :=
        card_le_card_of_le le_sup_left
      rw [hcardZ1] at hle
      rcases lt_or_ge 3 (Nat.card ↥(Z1 s t ⊔ Subgroup.zpowers xT)) with h | h
      · exact h
      · exfalso
        have hcard' : Nat.card ↥(Z1 s t ⊔ Subgroup.zpowers xT) ≤ Nat.card ↥(Z1 s t) := by
          rw [hcardZ1]; omega
        have heq : Z1 s t ⊔ Subgroup.zpowers xT = Z1 s t :=
          (Subgroup.eq_of_le_of_card_ge le_sup_left hcard').symm
        exact hxZ1 (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers xT))
    have hle9 : n ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
    have hn9 : n = 9 := by
      interval_cases n
      · exact absurd hdvd (by norm_num)
      · exact absurd hdvd (by norm_num)
      · exact absurd hdvd (by norm_num)
      · exact absurd hdvd (by norm_num)
      · exact absurd hdvd (by norm_num)
      · rfl
    exact Subgroup.eq_of_le_of_card_ge hleT (by rw [hTfacts.2.2.2, ← hn, hn9])
  have hL_eq : Z1 s t ⊔ Subgroup.zpowers l = Lsub H s t := by
    refine Subgroup.eq_of_le_of_card_ge
      (sup_le hZ1L (Subgroup.zpowers_le.mpr hl_mem)) ?_
    have h1 : Nat.card ↥(Z1 s t ⊔ Subgroup.zpowers l) ≤ 9 := by
      rw [← hcardL]
      exact card_le_card_of_le (sup_le hZ1L (Subgroup.zpowers_le.mpr hl_mem))
    have h2 : 9 ≤ Nat.card ↥(Z1 s t ⊔ Subgroup.zpowers l) := by
      rw [← hl9, ← Nat.card_zpowers l]
      exact card_le_card_of_le le_sup_right
    omega
  have hM_sub : T ⊔ Lsub H s t ≤ Z1 s t ⊔ Subgroup.closure ({xT, l} : Set G) := by
    refine sup_le ?_ ?_
    · rw [← hT_eq]
      exact sup_le le_sup_left
        ((Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))).trans le_sup_right)
    · rw [← hL_eq]
      exact sup_le le_sup_left
        ((Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))).trans le_sup_right)
  have hG2 := G2_card_sup_closure_pair_le (Z := Z1 s t) xT l
    (fun z hz => ⟨mul_comm_of_mem h11.comm (hTR (hZ1T hz)) (hTR hxT),
      (hZ1_Cst_comm z hz l (hLC hl_mem))⟩)
    (by rw [hTfacts.2.2.1 xT hxT]; exact (Z1 s t).one_mem) hl3
    (Subgroup.commutator_le.mp hAT (⁅xT, l⁆) (hTLA xT hxT l hl_mem) xT hxT)
    (Subgroup.commutator_le.mp hAL (⁅xT, l⁆) (hTLA xT hxT l hl_mem) l hl_mem)
  have hM_le81 : Nat.card ↥(T ⊔ Lsub H s t) ≤ 81 := by
    have h1 : Nat.card ↥(T ⊔ Lsub H s t) ≤
        Nat.card ↥(Z1 s t ⊔ Subgroup.closure ({xT, l} : Set G)) := card_le_card_of_le hM_sub
    have h2 : Nat.card ↥(Z1 s t ⊔ Subgroup.closure ({xT, l} : Set G)) ≤ 81 := by
      have h3 := hG2
      rw [hcardZ1] at h3
      simpa using h3
    exact h1.trans h2
  have hM_ne : T ⊔ Lsub H s t ≠ Cst s t := by
    intro hEq
    have hle := card_le_card_of_le (le_of_eq hEq.symm)
    rw [hcardCst] at hle
    exact absurd (hle.trans hM_le81) (by norm_num)
  obtain ⟨x, hxCst, hxM⟩ : ∃ x ∈ Cst s t, x ∉ T ⊔ Lsub H s t := by
    by_contra h
    push_neg at h
    exact hM_ne (le_antisymm hMle h)
  have hX_le : NG (Asub H P s t) ≤ NG (T ⊔ Lsub H s t) := by
    rw [h16.2]
    exact sup_le hM_normal (Subgroup.zpowers_le.mpr hsM)
  refine G0_hasNormalIndexP_of_fixed_elementary (p := 3) Nat.prime_three
    (X := NG (Asub H P s t)) (S := Cst s t) (C := Subgroup.zpowers s)
    (N := T ⊔ Lsub H s t) hA_normal (Subgroup.zpowers_le.mpr hsA) ?_ ?_ hX_le hMle
    h13 ?_ hab hpow hxCst hxM ?_
  · rw [h16.2]
  · rw [h16.2]
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hsCst)
  · rw [Nat.card_zpowers, c.s_inv]; norm_num
  · intro y hy
    have h2 : s * s = 1 := by
      have h := pow_orderOf_eq_one s
      rwa [c.s_inv, pow_two] at h
    have hs1 : s ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = 1 + 1 by norm_num, zpow_add, zpow_one, h2]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hy1 : s ^ k = 1 ∨ s ^ k = s := by
      rcases Int.even_or_odd k with he | ho
      · left
        obtain ⟨m, hm⟩ := he
        rw [hm, ← two_mul, zpow_mul, hs1, one_zpow]
      · right
        obtain ⟨m, hm⟩ := ho
        rw [hm, zpow_add, zpow_mul, hs1, one_zpow, one_mul, zpow_one]
    rcases hy1 with h1 | h1
    · rw [h1, show (1 : G) * x * 1⁻¹ * x⁻¹ = 1 by group]
      exact (T ⊔ Lsub H s t).one_mem
    · rw [h1]
      rw [show s * x * s⁻¹ * x⁻¹ = ⁅x, s⁆⁻¹ from by
        rw [commutatorElement_inv]; unfold commutatorElement; group]
      exact (T ⊔ Lsub H s t).inv_mem (hCs x hxCst)

/-- In case `|W| = 9`, `W` is not contained in `R Σ L`.  Otherwise `R Σ L = L V`, so
`T ≤ Ω₁(LV) = A`; then `|A| = |T| · |P|` forces `A = T ⊔ P = R` and hence `Σ ≤ R`, absurd. -/
theorem W_not_le_RSL (A : Aux (H := H) (Q := Q) (t := t) (s := s) (r := r) (P := P) (T := T)
    (h15 := h15)) (hW9 : Nat.card ↥(W H t) = 9)
    (hcardRSL : Nat.card ↥(h15.R ⊔ Sig H t P ⊔ Lsub H s t) = 243) :
    ¬ W H t ≤ h15.R ⊔ Sig H t P ⊔ Lsub H s t := by
  obtain ⟨hcardP, hcardR, hcardRSig, hcardZ1, hcardL, hA27, hCst81, hZ1T, hZ1R, hZ1L, hTR,
    hTC, hRC, hLC, hPC, hSigC, hSigP, hAC, hmemRP0, hcentD, hsinv, hSigV, hLfacts,
    hTfacts⟩ := aux_elem A
  obtain ⟨hFT, hC4, c, h7, hpf, h11, d, hTsig, hPL, hALV, h16, h17a, h14, h13, h14b⟩ := A
  have hmemRP : ∀ {x : G}, x ∈ P → x ∈ h15.R := fun {x} hx => hmemRP0 x hx
  intro hWle
  have hVeq : centD H t = W H t ⊔ P :=
    (Work.ThmF.ChV3.A_aux.W_sup_P_eq_centD_of_FT hFT hC4 c).symm
  have hP_le_R : P ≤ h15.R := fun x hx => hmemRP0 x hx
  have hP_le_A : P ≤ Asub H P s t := le_sup_right.trans le_sup_left
  have hP_le_RSL : P ≤ h15.R ⊔ Sig H t P ⊔ Lsub H s t :=
    hP_le_R.trans (le_sup_left.trans le_sup_left)
  have hLV_le : Lsub H s t ⊔ centD H t ≤ h15.R ⊔ Sig H t P ⊔ Lsub H s t := by
    refine sup_le le_sup_right ?_
    rw [hVeq]
    exact sup_le hWle hP_le_RSL
  have hLVcard : Nat.card ↥(Lsub H s t ⊔ centD H t) = 243 := by
    rw [hALV.2.2.2.1, hW9]
  have hLV_eq : Lsub H s t ⊔ centD H t = h15.R ⊔ Sig H t P ⊔ Lsub H s t :=
    Subgroup.eq_of_le_of_card_ge hLV_le (by rw [hLVcard, hcardRSL])
  have hT_le_LV : T ≤ Lsub H s t ⊔ centD H t := by
    rw [hLV_eq]
    exact hTR.trans (le_sup_left.trans le_sup_left)
  have hT_le_A : T ≤ Asub H P s t :=
    fun x hx => hALV.2.2.2.2.2.1 x (hT_le_LV hx) (hTfacts.2.2.1 x hx)
  have hP_norm_T : P ≤ Subgroup.normalizer (T : Set G) :=
    le_normalizer_of_forall_mul_comm (fun a ha b hb =>
      mul_comm_of_mem hALV.1 (hT_le_A ha) (hP_le_A hb))
  have hTPA : T ⊔ P = Asub H P s t := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hT_le_A hP_le_A) ?_
    rw [hA27]
    have hcard := card_sup_mul_card_inf_of_le_normalizer (H := T) (K := P) hP_norm_T
    rw [h11.TP, Subgroup.card_bot, mul_one, hTfacts.2.2.2, hcardP] at hcard
    omega
  have hRA : h15.R = Asub H P s t := by rw [← h11.TPR, hTPA]
  have hSig_le_R : Sig H t P ≤ h15.R := hRA ▸ le_sup_right
  have hSig_bot : Sig H t P = ⊥ := by
    have h1 : Sig H t P ≤ h15.R ⊓ Sig H t P := le_inf hSig_le_R le_rfl
    rw [R_inf_Sig hFT hC4 c h15 h7 hpf] at h1
    exact le_antisymm h1 bot_le
  have h2 : Nat.card ↥(Sig H t P) = 1 := by rw [hSig_bot, Subgroup.card_bot]
  rw [d.sig3] at h2
  omega

/-- Case `|W| = 9`. -/
theorem aux_case9 (A : Aux (H := H) (Q := Q) (t := t) (s := s) (r := r) (P := P) (T := T)
    (h15 := h15)) (hW9 : Nat.card ↥(W H t) = 9)
    (B1 : (∀ z ∈ Z1 s t, ∀ c ∈ Cst s t, z * c = c * z) ∧
      (P ≤ NG (Z1 s t)) ∧ (Sig H t P ≤ Subgroup.normalizer (P : Set G)) ∧
      (Lsub H s t ≤ NG (Z1 s t)) ∧ (Lsub H s t ≤ NG (Z1 s t ⊔ P)) ∧
      (Sig H t P ≤ NG (Z1 s t)) ∧ (Sig H t P ≤ NG (Z1 s t ⊔ P)))
    (B2 : (Subgroup.centralizer ((Z1 s t ⊔ P : Subgroup G) : Set G) = h15.R ⊔ Sig H t P) ∧
      (Lsub H s t ≤ NG (h15.R ⊔ Sig H t P)) ∧
      (Nat.card ↥(h15.R ⊔ Sig H t P ⊔ Lsub H s t) = 243))
    (B3 : (⁅Asub H P s t, T⁆ ≤ Z1 s t) ∧ (⁅Asub H P s t, Lsub H s t⁆ ≤ Z1 s t))
    (B4 : (Cst s t ≤ NG (Asub H P s t)) ∧ (s ∈ NG (Asub H P s t)) ∧ (s ∈ NG (Cst s t)) ∧
      (s ∈ NG T) ∧ (s ∈ NG P) ∧ (s ∈ NG (Lsub H s t)) ∧ (s ∈ NG h15.R))
    (hE : Nat.card P = 3 ∧ Nat.card ↥h15.R = 27 ∧ Nat.card ↥(h15.R ⊔ Sig H t P) = 81 ∧
      Nat.card ↥(Z1 s t) = 3 ∧ Nat.card ↥(Lsub H s t) = 9 ∧ Nat.card ↥(Asub H P s t) = 27 ∧
      Nat.card ↥(Cst s t) = 81 * Nat.card ↥(W H t) ∧ (Z1 s t ≤ T) ∧ (Z1 s t ≤ h15.R) ∧
      (Z1 s t ≤ Lsub H s t) ∧ (T ≤ h15.R) ∧
      (T ≤ Cst s t) ∧ (h15.R ≤ Cst s t) ∧ (Lsub H s t ≤ Cst s t) ∧ (P ≤ Cst s t) ∧
      (Sig H t P ≤ Cst s t) ∧ (Sig H t P ≤ CG P) ∧ (Asub H P s t ≤ Cst s t) ∧
      (∀ x ∈ P, x ∈ h15.R) ∧
      (centD H t ≤ Subgroup.centralizer ({s} : Set G)) ∧
      (s * (s * t) * s⁻¹ = (s * t)⁻¹) ∧ (Sig H t P ≤ centD H t) ∧
      (IsCyclic ↥(Lsub H s t) ∧ (∀ x ∈ Lsub H s t, s * x * s⁻¹ = x⁻¹) ∧
        s * t ∈ Lsub H s t) ∧
      ((∀ x ∈ T, s * x * s⁻¹ = x⁻¹) ∧ s * t ∈ T ∧ (∀ x ∈ T, x ^ 3 = 1) ∧ Nat.card ↥T = 9)) :
    HasNormalIndexP 3 ↥(NG (Asub H P s t)) := by
  have A' := A
  obtain ⟨hFT, hC4, c, h7, hpf, h11, d, hTsig, hPL, hALV, h16, h17a, h14, h13, h14b⟩ := A
  obtain ⟨hZ1_Cst_comm, hPZ1, hSigNormP, hLZ1, hLZ1P, hSigZ1, hSigZ1P⟩ := B1
  obtain ⟨hZ1P_CG, hLR, hcardRSL0⟩ := B2
  obtain ⟨hAT, hAL⟩ := B3
  obtain ⟨hA_normal, hsA, hsCst, hsT, hsP, hsL, hsR⟩ := B4
  obtain ⟨hcardP, hcardR, hcardRSig, hcardZ1, hcardL, hA27, hCst81, hZ1T, hZ1R, hZ1L, hTR,
    hTC, hRC, hLC, hPC, hSigC, hSigP, hAC, hmemRP0, hcentD, hsinv, hSigV, hLfacts,
    hTfacts⟩ := hE
  have hmemRP : ∀ {x : G}, x ∈ P → x ∈ h15.R := fun {x} hx => hmemRP0 x hx
  have hcardRSL : Nat.card ↥(h15.R ⊔ Sig H t P ⊔ Lsub H s t) = 243 := hcardRSL0
  have hcardCst : Nat.card ↥(Cst s t) = 729 := by rw [hCst81, hW9]
  have hRSL_le_Cst : h15.R ⊔ Sig H t P ⊔ Lsub H s t ≤ Cst s t := sup_le (sup_le hRC hSigC) hLC
  have hRSL_normal : Cst s t ≤ NG (h15.R ⊔ Sig H t P ⊔ Lsub H s t) :=
    normal_of_index_three_of_isPGroup hRSL_le_Cst h13 (by rw [hcardCst, hcardRSL])
  have hsSig : s ∈ NG (Sig H t P) :=
    Subgroup.centralizer_le_normalizer ((Sig H t P : Subgroup G) : Set G)
      (by rw [Subgroup.mem_centralizer_iff]
          intro σ hσ
          exact Subgroup.mem_centralizer_singleton_iff.mp (hcentD (hSigV hσ)))
  have hsRSL : s ∈ NG (h15.R ⊔ Sig H t P ⊔ Lsub H s t) :=
    le_normalizer_sup
      (Subgroup.zpowers_le.mpr (le_normalizer_sup (Subgroup.zpowers_le.mpr hsR)
        (Subgroup.zpowers_le.mpr hsSig) (Subgroup.mem_zpowers s)))
      (Subgroup.zpowers_le.mpr hsL) (Subgroup.mem_zpowers s)
  have hNn : NG (Asub H P s t) ≤ NG (h15.R ⊔ Sig H t P ⊔ Lsub H s t) := by
    rw [h16.2]
    exact sup_le hRSL_normal (Subgroup.zpowers_le.mpr hsRSL)
  have hquot : Nat.card (↥(Cst s t) ⧸
      ((h15.R ⊔ Sig H t P ⊔ Lsub H s t).subgroupOf (Cst s t))) = 3 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((h15.R ⊔ Sig H t P ⊔ Lsub H s t).subgroupOf (Cst s t))
    rw [card_subgroupOf_eq_card_inf, inf_eq_left.mpr hRSL_le_Cst, hcardRSL, hcardCst] at h1
    omega
  have hab : ∀ a ∈ Cst s t, ∀ b ∈ Cst s t,
      a * b * a⁻¹ * b⁻¹ ∈ h15.R ⊔ Sig H t P ⊔ Lsub H s t :=
    commutator_mem_of_card_quotient_three hRSL_le_Cst hRSL_normal hquot
  have hpow : ∀ a ∈ Cst s t, a ^ 3 ∈ h15.R ⊔ Sig H t P ⊔ Lsub H s t :=
    pow_mem_of_card_quotient_three hRSL_le_Cst hRSL_normal hquot
  have hW_le_Cst : W H t ≤ Cst s t := by
    intro w hw
    have hwt : w ∈ centD H t := Work.ThmF.W_le_centD H t hw
    have h1 : w * t = t * w :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hwt).2
    have h2 : w * s = s * w := Subgroup.mem_centralizer_singleton_iff.mp (hcentD hwt)
    rw [Cst, Subgroup.mem_centralizer_singleton_iff]
    calc w * (s * t) = (w * s) * t := by group
      _ = (s * w) * t := by rw [h2]
      _ = s * (w * t) := by group
      _ = s * (t * w) := by rw [h1]
      _ = (s * t) * w := by group
  have hW_Cs : ∀ w ∈ W H t, w * s = s * w := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mp (hcentD (Work.ThmF.W_le_centD H t hw))
  have hW_not_le : ¬ W H t ≤ h15.R ⊔ Sig H t P ⊔ Lsub H s t := W_not_le_RSL A' hW9 hcardRSL
  obtain ⟨x, hxW, hxRSL⟩ : ∃ x ∈ W H t, x ∉ h15.R ⊔ Sig H t P ⊔ Lsub H s t := by
    by_contra h
    push_neg at h
    exact hW_not_le h
  refine G0_hasNormalIndexP_of_fixed_elementary (p := 3) Nat.prime_three
    (X := NG (Asub H P s t)) (S := Cst s t) (C := Subgroup.zpowers s)
    (N := h15.R ⊔ Sig H t P ⊔ Lsub H s t)
    hA_normal (Subgroup.zpowers_le.mpr hsA) ?_ ?_ hNn hRSL_le_Cst h13 ?_ hab hpow ?_ hxRSL ?_
  · rw [h16.2]
  · rw [h16.2]
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hsCst)
  · rw [Nat.card_zpowers, c.s_inv]; norm_num
  · exact hW_le_Cst hxW
  · intro y hy
    have h2 : s * s = 1 := by
      have h := pow_orderOf_eq_one s
      rwa [c.s_inv, pow_two] at h
    have hs1 : s ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = 1 + 1 by norm_num, zpow_add, zpow_one, h2]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hy1 : s ^ k = 1 ∨ s ^ k = s := by
      rcases Int.even_or_odd k with he | ho
      · left
        obtain ⟨m, hm⟩ := he
        rw [hm, ← two_mul, zpow_mul, hs1, one_zpow]
      · right
        obtain ⟨m, hm⟩ := ho
        rw [hm, zpow_add, zpow_mul, hs1, one_zpow, one_mul, zpow_one]
    rcases hy1 with h1 | h1
    · rw [h1, show (1 : G) * x * 1⁻¹ * x⁻¹ = 1 by group]
      exact Subgroup.one_mem _
    · rw [h1, show s * x * s⁻¹ * x⁻¹ = 1 by rw [← hW_Cs x hxW]; group]
      exact Subgroup.one_mem _

/-- **§3 step (17b)**: `N_G(A)` has a normal subgroup of index `3`, in case (10-2). -/
theorem normalizerA_hasNormalIndexP {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    {T : Subgroup G} (h11 : Work.ThmF.ChV3.Step11Out H Q t P h15.R T)
    (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    Work.ThmF.HasNormalIndexP 3 ↥(Work.ThmF.ChV3.NG (Work.ThmF.ChV3.Asub H P s t)) := by
  classical
  have A : Aux (H := H) (Q := Q) (t := t) (s := s) (r := r) (P := P) (T := T) (h15 := h15) :=
    { hFT := hFT
      hC4 := hC4
      c := c
      h7 := h7
      hpf := hpf
      h11 := h11
      d := d
      hTsig := T_sig_facts hFT hC4 c h15 h7 hpf h11 d
      hPL := P_on_L hFT hC4 c h15 h7 hpf h11 d
      hALV := A_LV_facts hFT hC4 c h15 h7 hpf h11 d
      h16 := A_stronglyReal_normalizer hFT hC4 c h15 h7 hpf h11 d
      h17a := A_weaklyClosed hFT hC4 c h15 h7 hpf h11 d
      h14 := cst_center_sylow hFT hC4 c h15 h7 hpf h11 d
      h13 := cst_isPGroup hFT hC4 c h15 d
      h14b := (cP_inf_cst hFT hC4 c h15 h7 hpf h11 d).1 }
  have hEl := aux_elem A
  have B1 := aux_basic1 A
  have B1' := B1
  have hEl' := hEl
  obtain ⟨hZ1_Cst_comm, hPZ1, hSigNormP, hLZ1, hLZ1P, hSigZ1, hSigZ1P⟩ := B1
  obtain ⟨hcardP, hcardR, hcardRSig, hcardZ1, hcardL, hA27, hCst81, hZ1T, hZ1R, hZ1L, hTR,
    hTC, hRC, hLC, hPC, hSigC, hSigP, hAC, hmemRP0, hcentD, hsinv, hSigV, hLfacts,
    hTfacts⟩ := hEl
  have hmemRP : ∀ {x : G}, x ∈ P → x ∈ h15.R := fun {x} hx => hmemRP0 x hx
  have hIL : Lsub H s t ⊓ (h15.R ⊔ Sig H t P) = Z1 s t :=
    Lsub_inf_RSig hFT hC4 c h15 h7 hpf h11 d (P_on_L hFT hC4 c h15 h7 hpf h11 d)
  have B2 := aux_basic2 A hZ1_Cst_comm hPZ1 hLZ1 hLZ1P hSigZ1 hSigC hSigP hRC hcardRSig
    hcardL hcardZ1 hIL hZ1R hmemRP
  have B3 := aux_basic3 A hZ1_Cst_comm hPZ1 hSigZ1 hSigZ1P hSigNormP hZ1T hZ1L hTR hLC hSigC
    hSigP hmemRP
  have B4 := aux_basic4 A hAC hLC hPC hSigC hSigV hcentD hsinv hTfacts
  rcases d.W39 with hW3 | hW9
  · exact aux_case3 A hW3 B1' B2 B3 B4 hEl'
  · exact aux_case9 A hW9 B1' B2 B3 B4 hEl'

end Assembling

end Work.ThmF.ChV3.Prove
