import Mathlib
import Submission.Work.Hering.AppVII.Setup
import Submission.Work.Hering.AppVII.map_appVIIZ_equiv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.AppVII

universe u v u' v'

open scoped commutatorElement

/-- Cardinality of a `subgroupOf` is unchanged. -/
theorem card_subgroupOf_eq {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card ↥(H.subgroupOf K) = Nat.card ↥H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

/-- `subgroupOf` commutes with intersections. -/
theorem subgroupOf_inf {G : Type*} [Group G] (H K B : Subgroup G) :
    (H ⊓ K).subgroupOf B = H.subgroupOf B ⊓ K.subgroupOf B := by
  ext x; simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]

/-- If `H ≤ K` are subgroups of a finite group and `|K|` is odd then `|H|` is odd. -/
theorem odd_card_of_le {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K)
    (hK : Odd (Nat.card ↥K)) : Odd (Nat.card ↥H) := by
  have h1 : Nat.card ↥(H.subgroupOf K) = Nat.card ↥H := card_subgroupOf_eq h
  rw [← h1]
  exact Odd.of_dvd_nat hK (Subgroup.card_subgroup_dvd_card (H.subgroupOf K))

/-- The centralizer of `P` inside a subgroup `B` of the ambient group is the centralizer in `B`
of the induced subgroup. -/
theorem centralizer_subgroupOf {G : Type*} [Group G] (P B : Subgroup G) (hPB : P ≤ B) :
    (Subgroup.centralizer (P : Set G)).subgroupOf B
      = Subgroup.centralizer ((P.subgroupOf B : Subgroup ↥B) : Set ↥B) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    apply Subtype.ext
    simpa only [Subgroup.coe_mul] using h (y : G) (Subgroup.mem_subgroupOf.mp hy)
  · intro h y hy
    have := congrArg (Subtype.val) (h ⟨y, hPB hy⟩ (Subgroup.mem_subgroupOf.mpr hy))
    simpa only [Subgroup.coe_mul] using this

/-- `AppVIIStmt` is independent of the universes of the acting group `A` and of the coefficient
group `K`: a proof at universes `(u,v)` gives a proof at any other pair `(u',v')`, by replacing a
configuration in `(u',v')` by an isomorphic model in `(u,v)`
(`Finite.exists_type_univ_nonempty_mulEquiv`) and transporting `appVIIZ` along the two
isomorphisms (`map_appVIIZ_equiv`). -/
theorem AppVIIStmt_univ {n : ℕ} (h : AppVIIStmt.{u, v} n) : AppVIIStmt.{u', v'} n := by
  intro A instA finA P Q hQn hinf hsup p hp hcardP hpQ K instK finK instAct hcop hodd hsize
  letI : Group A := instA
  letI : Finite A := finA
  letI : Group K := instK
  letI : Finite K := finK
  letI : MulDistribMulAction A K := instAct
  -- isomorphic models of `A` and `K` in the universes of the hypothesis
  obtain ⟨A₂, instA₂, finA₂, ⟨eA⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{u', u} A
  letI : Group A₂ := instA₂
  letI : Fintype A₂ := finA₂
  obtain ⟨K₂, instK₂, finK₂, ⟨eK⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{v', v} K
  letI : Group K₂ := instK₂
  letI : Fintype K₂ := finK₂
  -- the transported action of `A₂` on `K₂`
  let act₂ : MulDistribMulAction A₂ K₂ :=
    { smul := fun a k => eK (eA.symm a • eK.symm k)
      one_smul := fun k => by
        show eK (eA.symm 1 • eK.symm k) = k
        rw [map_one, one_smul, eK.apply_symm_apply]
      mul_smul := fun a b k => by
        show eK (eA.symm (a * b) • eK.symm k)
          = eK (eA.symm a • eK.symm (eK (eA.symm b • eK.symm k)))
        rw [map_mul, mul_smul, eK.symm_apply_apply]
      smul_one := fun a => by
        show eK (eA.symm a • eK.symm 1) = 1
        rw [map_one, smul_one, map_one]
      smul_mul := fun a m n => by
        show eK (eA.symm a • eK.symm (m * n))
          = eK (eA.symm a • eK.symm m) * eK (eA.symm a • eK.symm n)
        rw [map_mul, smul_mul', map_mul] }
  letI := act₂
  -- the hypotheses of the configuration transported to `(u,v)`
  have hQn₂ : (Q.map eA.toMonoidHom).Normal := hQn.map eA.toMonoidHom eA.surjective
  have hinf₂ : P.map eA.toMonoidHom ⊓ Q.map eA.toMonoidHom = ⊥ := by
    rw [← Subgroup.map_inf P Q eA.toMonoidHom eA.injective, hinf, Subgroup.map_bot]
  have hsup₂ : P.map eA.toMonoidHom ⊔ Q.map eA.toMonoidHom = ⊤ := by
    rw [← Subgroup.map_sup P Q eA.toMonoidHom, hsup,
      Subgroup.map_top_of_surjective eA.toMonoidHom eA.surjective]
  have hcardP₂ : Nat.card ↥(P.map eA.toMonoidHom) = p := by
    rw [Subgroup.card_map_of_injective (K := P) eA.injective]; exact hcardP
  have hpQ₂ : ¬ p ∣ Nat.card ↥(Q.map eA.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (K := Q) eA.injective]; exact hpQ
  have hcop₂ : Nat.Coprime (Nat.card K₂) (Nat.card A₂) := by
    rw [← Nat.card_congr eK.toEquiv, ← Nat.card_congr eA.toEquiv]; exact hcop
  have hsize₂ : Nat.card A₂ * Nat.card K₂ = n := by
    rw [← Nat.card_congr eA.toEquiv, ← Nat.card_congr eK.toEquiv]; exact hsize
  have hcent₂ : Subgroup.centralizer ((P.map eA.toMonoidHom : Subgroup A₂) : Set A₂)
      = (Subgroup.centralizer (P : Set A)).map eA.toMonoidHom := by
    ext x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_map]
    constructor
    · intro hx
      refine ⟨eA.symm x, ?_, eA.apply_symm_apply x⟩
      intro w hw
      have h1 : eA w * x = x * eA w := hx (eA w) (Subgroup.mem_map.mpr ⟨w, hw, rfl⟩)
      apply eA.injective
      simpa only [map_mul, eA.apply_symm_apply] using h1
    · rintro ⟨y, hy, rfl⟩ z hz
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
      rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hy) w hw]
  have hodd₂ : Odd (Nat.card ↥(Q.map eA.toMonoidHom ⊓
      Subgroup.centralizer ((P.map eA.toMonoidHom : Subgroup A₂) : Set A₂))) := by
    rw [hcent₂,
      ← Subgroup.map_inf Q (Subgroup.centralizer (P : Set A)) eA.toMonoidHom eA.injective,
      Subgroup.card_map_of_injective (K := Q ⊓ Subgroup.centralizer (P : Set A)) eA.injective]
    exact hodd
  -- apply the hypothesis to the transported configuration
  have hz : appVIIZ A₂ (P.map eA.toMonoidHom) (Q.map eA.toMonoidHom) K₂ = ⊤ :=
    h (P.map eA.toMonoidHom) (Q.map eA.toMonoidHom) hQn₂ hinf₂ hsup₂ p hp hcardP₂ hpQ₂
      hcop₂ hodd₂ hsize₂
  have hact : ∀ (a : A) (k : K), eK (a • k) = eA a • eK k := by
    intro a k
    show eK (a • k) = eK (eA.symm (eA a) • eK.symm (eK k))
    rw [eA.symm_apply_apply, eK.symm_apply_apply]
  rw [← map_appVIIZ_equiv eA eK hact P Q] at hz
  -- transport the conclusion back
  rw [eq_top_iff]
  intro x _
  have hx : eK x ∈ (appVIIZ A P Q K).map eK.toMonoidHom := hz ▸ Subgroup.mem_top (eK x)
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  rwa [eK.injective hyx] at hy

theorem hcent_of_eq_bot {n : ℕ} (ih : ∀ m < n, AppVIIStmt m)
    {A : Type u} [Group A] [Finite A] (P Q : Subgroup A) (hQn : Q.Normal)
    (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) (p : ℕ) (hp : p.Prime) (hcardP : Nat.card ↥P = p)
    (hpQ : ¬ p ∣ Nat.card ↥Q) {K : Type v} [Group K] [Finite K] [MulDistribMulAction A K]
    (hcop : Nat.Coprime (Nat.card K) (Nat.card A))
    (hodd : Odd (Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set A))))
    (hsize : Nat.card A * Nat.card K = n)
    (hZbot : appVIIZ A P Q K = ⊥)
    (hfaith : ∀ a : A, (∀ x : K, a • x = x) → a = 1) :
    ∀ Q' : Subgroup A, Q' ≤ Q → Q' ≠ ⊥ → Q' ≠ Q → ⁅P, Q'⁆ ≤ Q' → ⁅P, Q'⁆ = ⊥ := by
  intro Q' hQ'le _hQ'ne_bot hQ'ne_Q hcomm
  haveI : Q.Normal := hQn
  -- `B := P ⊔ Q'`; it is proper because `Q' ≠ Q`.
  let B : Subgroup A := P ⊔ Q'
  have hPB : P ≤ B := le_sup_left
  have hQ'B : Q' ≤ B := le_sup_right
  -- `Q'` is normalised by `B`
  have hQ'N : B ≤ Subgroup.normalizer (Q' : Set A) := by
    show P ⊔ Q' ≤ Subgroup.normalizer ↑Q'
    apply sup_le
    · rw [Subgroup.le_normalizer_iff]
      intro x hx k hk
      have h1 : ⁅x, k⁆ ∈ Q' := hcomm (Subgroup.commutator_mem_commutator hx hk)
      have h2 : x * k * x⁻¹ = ⁅x, k⁆ * k := by rw [commutatorElement_def]; group
      rw [h2]
      exact Q'.mul_mem h1 hk
    · rw [Subgroup.le_normalizer_iff]
      intro k hk x hx
      exact Q'.mul_mem (Q'.mul_mem hk hx) (Q'.inv_mem hk)
  have hQ'Bnorm : (Q'.subgroupOf B).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hQ'B]
    intro h k hh hk
    exact (Subgroup.le_normalizer_iff.mp hQ'N k hk h hh)
  haveI : (Q'.subgroupOf B).Normal := hQ'Bnorm
  -- the configuration induced on `B`
  have hPQ'inf : P ⊓ Q' = ⊥ := by
    have : P ⊓ Q' ≤ (⊥ : Subgroup A) := by rw [← hinf]; exact inf_le_inf_left P hQ'le
    exact le_antisymm this bot_le
  have hinfB : P.subgroupOf B ⊓ Q'.subgroupOf B = ⊥ := by
    rw [← subgroupOf_inf P Q' B, hPQ'inf, Subgroup.bot_subgroupOf]
  have hsupB : P.subgroupOf B ⊔ Q'.subgroupOf B = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hPB hQ'B]
    exact Subgroup.subgroupOf_self B
  have hcardPB : Nat.card ↥(P.subgroupOf B) = p := by
    rw [card_subgroupOf_eq hPB, hcardP]
  have hdvdQ'Q : Nat.card ↥Q' ∣ Nat.card ↥Q := by
    rw [← card_subgroupOf_eq hQ'le]
    exact Subgroup.card_subgroup_dvd_card (Q'.subgroupOf Q)
  have hpQ'B : ¬ p ∣ Nat.card ↥(Q'.subgroupOf B) := by
    rw [card_subgroupOf_eq hQ'B]
    exact fun h => hpQ (h.trans hdvdQ'Q)
  have hdvdBA : Nat.card ↥B ∣ Nat.card A := Subgroup.card_subgroup_dvd_card B
  have hcopB : Nat.Coprime (Nat.card K) (Nat.card ↥B) := hcop.coprime_dvd_right hdvdBA
  have hoddB : Odd (Nat.card ↥(Q'.subgroupOf B ⊓
      Subgroup.centralizer ((P.subgroupOf B : Subgroup ↥B) : Set ↥B))) := by
    rw [← centralizer_subgroupOf P B hPB,
      ← subgroupOf_inf Q' (Subgroup.centralizer (P : Set A)) B,
      card_subgroupOf_eq (H := Q' ⊓ Subgroup.centralizer (P : Set A)) (K := B)
        (le_trans inf_le_left hQ'B)]
    exact odd_card_of_le (le_inf (le_trans inf_le_left hQ'le) inf_le_right) hodd
  -- `B ≠ ⊤`, hence `|B| < |A|`
  have hBne : B ≠ ⊤ := by
    intro hBtop
    have hQleQ' : Q ≤ Q' := by
      intro q hq
      have hqB : (⟨q, by rw [hBtop]; exact Subgroup.mem_top q⟩ : ↥B)
          ∈ P.subgroupOf B ⊔ Q'.subgroupOf B := by rw [hsupB]; exact Subgroup.mem_top _
      obtain ⟨pp, hpp, qq, hqq, hpq⟩ :=
        (Subgroup.mem_sup_of_normal_right (s := P.subgroupOf B) (t := Q'.subgroupOf B)).mp hqB
      have hpqA : (pp : A) * (qq : A) = q := by
        have := congrArg (Subtype.val) hpq
        simpa only [Subgroup.coe_mul] using this
      have hpP : (pp : A) ∈ P := Subgroup.mem_subgroupOf.mp hpp
      have hqQ' : (qq : A) ∈ Q' := Subgroup.mem_subgroupOf.mp hqq
      have hpQ : (pp : A) ∈ Q := by
        have hpp_eq : (pp : A) = q * (qq : A)⁻¹ := by rw [← hpqA]; group
        rw [hpp_eq]
        exact Q.mul_mem hq (Q.inv_mem (hQ'le hqQ'))
      have hpbot : (pp : A) ∈ (⊥ : Subgroup A) := by rw [← hinf]; exact ⟨hpP, hpQ⟩
      have hp1 : (pp : A) = 1 := Subgroup.mem_bot.mp hpbot
      rw [hp1, one_mul] at hpqA
      rwa [← hpqA]
    exact hQ'ne_Q (le_antisymm hQ'le hQleQ')
  have hBlt : Nat.card ↥B < Nat.card A := by
    have hne : Nat.card ↥B ≠ Nat.card A := fun h => hBne (Subgroup.eq_top_of_card_eq B h)
    exact Nat.lt_of_le_of_ne (Nat.le_of_dvd (Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩) hdvdBA) hne
  have hm : Nat.card ↥B * Nat.card K < n := by
    rw [← hsize]
    exact Nat.mul_lt_mul_of_pos_right hBlt (Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩)
  -- apply the induction hypothesis to the configuration on `B`
  letI : MulDistribMulAction ↥B K := instRestrictAct B
  have hZtop : appVIIZ A P Q' K = ⊤ := by
    have ih' : AppVIIStmt.{u, v} (Nat.card ↥B * Nat.card K) :=
      AppVIIStmt_univ (ih (Nat.card ↥B * Nat.card K) hm)
    have h : appVIIZ ↥B (P.subgroupOf B) (Q'.subgroupOf B) K = ⊤ :=
      ih' (P.subgroupOf B) (Q'.subgroupOf B)
        hQ'Bnorm hinfB hsupB p hp hcardPB hpQ'B hcopB hoddB rfl
    rwa [appVIIZ_subgroupOf_eq P Q' B hPB hQ'B] at h
  -- `[P,Q']` acts trivially on `K`, hence is trivial by faithfulness
  have hF1top : appVIIF1 A P Q' K = ⊤ := by
    apply le_antisymm le_top
    rw [← hZtop, appVIIZ, Subgroup.closure_le]
    rintro k (hk | hk)
    · exact hk
    · obtain ⟨x, hx⟩ := hk
      have hx' : k ∈ appVIIFx A P Q K ⟨(x : A), hQ'le x.2⟩ := hx
      have hkbot : k ∈ (⊥ : Subgroup K) := by
        rw [← hZbot]
        exact appVIIFx_le_appVIIZ A P Q K ⟨(x : A), hQ'le x.2⟩ hx'
      rw [Subgroup.mem_bot] at hkbot
      rw [hkbot]
      exact (appVIIF1 A P Q' K).one_mem
  refine le_antisymm ?_ bot_le
  intro y hy
  rw [Subgroup.mem_bot]
  exact hfaith y (fun x => by
    have hx : x ∈ appVIIF1 A P Q' K := by rw [hF1top]; exact Subgroup.mem_top x
    exact hx y hy)

end Work.Hering.AppVII
