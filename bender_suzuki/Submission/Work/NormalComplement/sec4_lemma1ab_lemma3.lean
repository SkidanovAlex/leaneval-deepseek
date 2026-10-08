import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.appV_prod
import Submission.Work.NormalComplement.appI_one
import Submission.Work.NormalComplement.appI_four
import Submission.Work.Models.Basic
import Submission.Work.ThmF.Bender.DTransInvAux
import Submission.Work.NormalComplement.sec1_lemma3_fixpts
import Submission.Work.NormalComplement.sec4_lm3_kapp_structure

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

/-- If `g` fixes `X` pointwise under conjugation then `g` normalises `X`. -/
private lemma mem_normalizer_of_fix' {G : Type*} [Group G] {X : Subgroup G} {g : G}
    (h : ∀ x ∈ X, g * x * g⁻¹ = x) : g ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm ?_ ?_
  · rintro y ⟨z, hz, hyz⟩
    rw [← hyz]
    change g * z * g⁻¹ ∈ X
    rw [h z hz]
    exact hz
  · intro x hx
    exact Subgroup.mem_map.mpr ⟨x, hx,
      by simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h x hx⟩

/-- Peterfalvi I Ch. III §1, p.175, in the exact form §4 (a),(b) consumes: `1 ≠ X ≤ V = centD H t`
with `N_K(X) ≠ 1`; `1 ≠ P ≤ V` normalising `X` and acting fixed-point-freely on
`N_K(X) = Design.NK H t X`. Then `N_K(X) = C_K(X)` (as sets), `|C_K(X)| = 2^|P| - 1`, and with
`V₁ = N_V(X) = centD H t ⊓ N_G(X) ⊆ V`: `V₁ ⊓ C(N_K(X)) ⊓ P = ⊥` and `V₁ ⊓ C(N_K(X)) ⊔ P = V₁`.

Route (paper p.175): `S` a 2-Sylow of `C_H(X)`, `Q = Ω₁(S)`; Ch. II §4 Prop. 3 (`hC4`) gives
`Q = {1} ∪ Inv N_H(X)` elementary abelian, `K₁ = N_K(X) = C_K(X)` cyclic and regular on `Q#`, and
`C_{N_V(X)}(K₁) = N_V(X) ⊓ C_G(Q)`; for `1 ≠ P₁ ≤ P`, `C_{K₁}(P₁) = 1` forces `|C_Q(P₁)| = 2`; then
App. V with `d = 2`, `U = N_D(X)`, `T = K₁`.

The structural input is the (sorry-free) `Work.NormalComplement.sec4_lm3_kapp_structure`, the
fixed-point count is `Work.NormalComplement.sec1_lemma3_fixpts`, and App. V (d) is applied in its
product form `Work.NormalComplement.appV_prod`. -/
theorem sec4_lemma1ab_lemma3 (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hMod : Submission.Blueprint.ModelFactsProp)
    (hV : Work.NormalComplement.AppVProp) {G : Type} [Group G] [Finite G]
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2)
    (htH : t ∉ H) {X P : Subgroup G} (hX : X ≠ ⊥)
    (hXV : X ≤ Submission.Blueprint.centD H t)
    (hNK : ∃ k ∈ Work.NormalComplement.Design.NK H t X, k ≠ 1) (hP : P ≠ ⊥)
    (hPV : P ≤ Submission.Blueprint.centD H t)
    (hPX : P ≤ Subgroup.normalizer (X : Set G))
    (hfpf : Work.NormalComplement.Design.FpfOn P (Work.NormalComplement.Design.NK H t X)) :
    Work.NormalComplement.Design.NK H t X = Work.NormalComplement.Design.CK H t X ∧
      (Work.NormalComplement.Design.CK H t X).ncard = 2 ^ Nat.card P - 1 ∧
      (Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G) ⊓
          Subgroup.centralizer (Work.NormalComplement.Design.NK H t X)) ⊓ P = ⊥ ∧
      (Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G) ⊓
          Subgroup.centralizer (Work.NormalComplement.Design.NK H t X)) ⊔ P =
        Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G) := by
  classical
  -- ## 0. the structural input (Ch. II §4 Prop. 3 + `ModelFactsProp`)
  obtain ⟨Q, K₁, hQcar, hK1car, hNKeqCK, hK1cyc, hQsq, hQcomm, hreg, hQne⟩ :=
    sec4_lm3_kapp_structure hFT hC4 hMod hS hH ht htH hX hXV hNK
  have hK1le : (K₁ : Set G) ⊆ Work.NormalComplement.Design.NK H t X := le_of_eq hK1car
  have hNKle : Work.NormalComplement.Design.NK H t X ⊆ (K₁ : Set G) := le_of_eq hK1car.symm
  -- ## 1. the symmetry `u` of Ch. II §4 Prop. 2 (a)
  obtain ⟨u, huInv, huV⟩ := (hC4 (G := G) hS H hH t ht htH).2.1
  have huH : u ∈ H := huInv.1
  have hu2 : orderOf u = 2 := huInv.2
  have hu1 : u ≠ 1 := by
    intro h; rw [h, orderOf_one] at hu2; exact absurd hu2 (by norm_num)
  have huC : ∀ x ∈ X, u * x * u⁻¹ = x := by
    intro x hx
    have hxV : x ∈ Submission.Blueprint.centD H t := hXV hx
    rw [huV] at hxV
    have hxu : u * x = x * u :=
      (Subgroup.mem_centralizer_iff.mp hxV.2) u (Set.mem_singleton u)
    rw [hxu]; group
  have huNX : u ∈ Subgroup.normalizer (X : Set G) := mem_normalizer_of_fix' huC
  have huQ : u ∈ Q := by
    have h : u ∈ (Q : Set G) := by rw [hQcar]; exact Or.inr ⟨⟨huH, huNX⟩, hu2⟩
    exact h
  -- ## 2. the two normalisers `U = N_D(X)`, `V₁ = N_V(X)`
  set U : Subgroup G :=
    Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G) with hUdef
  set V₁ : Subgroup G :=
    Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G) with hV1def
  have hP_le_V1 : P ≤ V₁ := by
    intro p hp
    rw [hV1def]
    exact Subgroup.mem_inf.mpr ⟨hPV hp, hPX hp⟩
  have hP_le_U : P ≤ U := by
    intro p hp
    rw [hUdef]
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (hPV hp)).1, hPX hp⟩
  have hPu : P ≤ Subgroup.centralizer ({u} : Set G) := by
    intro p hp
    have h := hPV hp
    rw [huV] at h
    exact h.2
  have huQP : u ∈ Q ⊓ Subgroup.centralizer (P : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨huQ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (Subgroup.mem_centralizer_iff.mp (hPu hp) u (Set.mem_singleton u)).symm
  -- ## 3. `K₁ ≤ U`, `N_H(X) ≤ N(Q)` and `U ≤ N(Q)`
  have hK1leU : K₁ ≤ U := by
    intro k hk
    have hkNK : k ∈ Work.NormalComplement.Design.NK H t X := hK1le hk
    have hkD : k ∈ Submission.Blueprint.twoPoint H t :=
      (Work.Models.mem_invertedBy_iff.mp hkNK.1).1
    rw [hUdef]
    exact Subgroup.mem_inf.mpr ⟨hkD, hkNK.2⟩
  have hNQ : H ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (Q : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr ?_
    intro m hm q hq
    have hq' : q ∈ (Q : Set G) := hq
    rw [hQcar] at hq'
    have hmem : m * q * m⁻¹ ∈ (insert 1 (Submission.Blueprint.involutions
        ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G)) : Set G) := by
      rcases hq' with hq1 | hqI
      · rw [hq1]; simp
      · refine Or.inr ⟨(H ⊓ Subgroup.normalizer (X : Set G)).mul_mem
            ((H ⊓ Subgroup.normalizer (X : Set G)).mul_mem hm hqI.1)
            ((H ⊓ Subgroup.normalizer (X : Set G)).inv_mem hm), ?_⟩
        rw [Work.ThmF.Bender.orderOf_conj_eq, hqI.2]
    rw [← hQcar] at hmem
    exact hmem
  have hU_le_NQ : U ≤ Subgroup.normalizer (Q : Set G) := by
    intro z hz
    rw [hUdef] at hz
    exact hNQ ⟨(Subgroup.mem_inf.mp hz).1.1, (Subgroup.mem_inf.mp hz).2⟩
  have hK1NQ : K₁ ≤ Subgroup.normalizer (Q : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr ?_
    intro k hk q hq
    have hkM : k ∈ H ⊓ Subgroup.normalizer (X : Set G) := by
      have hkU := hK1leU hk
      rw [hUdef] at hkU
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hkU).1.1, (Subgroup.mem_inf.mp hkU).2⟩
    have hq' : q ∈ (Q : Set G) := hq
    rw [hQcar] at hq'
    have hmem : k * q * k⁻¹ ∈ (insert 1 (Submission.Blueprint.involutions
        ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G)) : Set G) := by
      rcases hq' with hq1 | hqI
      · rw [hq1]; simp
      · refine Or.inr ⟨(H ⊓ Subgroup.normalizer (X : Set G)).mul_mem
            ((H ⊓ Subgroup.normalizer (X : Set G)).mul_mem hkM hqI.1)
            ((H ⊓ Subgroup.normalizer (X : Set G)).inv_mem hkM), ?_⟩
        rw [Work.ThmF.Bender.orderOf_conj_eq, hqI.2]
    rw [← hQcar] at hmem
    exact hmem
  -- ## 4. `V₁ ≤ N(K₁)` (App. I (4): `V = C_D(t)` normalises `K = J(D,t)`)
  have hV1_norm : ∀ v ∈ V₁, ∀ k ∈ K₁, v * k * v⁻¹ ∈ K₁ := by
    intro v hv k hk
    have hv' : v ∈ Submission.Blueprint.centD H t ∧ v ∈ Subgroup.normalizer (X : Set G) := by
      rw [hV1def] at hv; exact Subgroup.mem_inf.mp hv
    have hvt : t * v = v * t :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hv'.1).2) t (Set.mem_singleton t)
    have hvt' : t * v * t⁻¹ = v := by rw [hvt]; group
    have hkNK : k ∈ Work.NormalComplement.Design.NK H t X := hK1le hk
    obtain ⟨hkD, hkinv⟩ := Work.Models.mem_invertedBy_iff.mp hkNK.1
    have hvD : v ∈ Submission.Blueprint.twoPoint H t := (Subgroup.mem_inf.mp hv'.1).1
    have h1 : v * k * v⁻¹ ∈ Submission.Blueprint.twoPoint H t :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hvD hkD) (Subgroup.inv_mem _ hvD)
    have h2 : t * (v * k * v⁻¹) * t⁻¹ = (v * k * v⁻¹)⁻¹ := by
      have hvinv : t * v⁻¹ * t⁻¹ = v⁻¹ :=
        (by group : t * v⁻¹ * t⁻¹ = (t * v * t⁻¹)⁻¹).trans (congrArg Inv.inv hvt')
      calc t * (v * k * v⁻¹) * t⁻¹
          = (t * v * t⁻¹) * (t * k * t⁻¹) * (t * v⁻¹ * t⁻¹) := by group
        _ = v * k⁻¹ * v⁻¹ := by rw [hvt', hkinv, hvinv]
        _ = (v * k * v⁻¹)⁻¹ := by group
    have h3 : v * k * v⁻¹ ∈ Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t :=
      ⟨h1, h2⟩
    have h4 : v * k * v⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hv'.2 hkNK.2) (Subgroup.inv_mem _ hv'.2)
    exact hNKle ⟨h3, h4⟩
  have hV1_le_NK1 : V₁ ≤ Subgroup.normalizer (K₁ : Set G) :=
    Subgroup.le_normalizer_iff.mpr hV1_norm
  -- ## 5. `U ≤ N(K₁)` (App. I (1): `N_D(X) = N_K(X)·N_V(X)`)
  have hDodd : Odd (Nat.card (Submission.Blueprint.twoPoint H t)) :=
    Work.Models.IsStronglyEmbedded.odd_twoPoint hH htH
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t; rw [ht] at h; simpa [pow_two] using h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htCent : ∀ x ∈ X, t * x * t⁻¹ = x := by
    intro x hx
    have hxV : x ∈ Submission.Blueprint.centD H t := hXV hx
    have hxt : t * x = x * t :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxV).2) t (Set.mem_singleton t)
    rw [hxt]; group
  have htNX : t ∈ Subgroup.normalizer (X : Set G) := mem_normalizer_of_fix' htCent
  have hnormU : Work.NormalComplement.NormalizedBy t U := by
    intro x hx
    rw [hUdef] at hx ⊢
    obtain ⟨hxD, hxN⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxH, hxc⟩ := Subgroup.mem_inf.mp hxD
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · have hxt : t * x * t⁻¹ = t⁻¹ * x * t := by rw [hti]
      rw [hxt]
      exact Work.Models.mem_conj_iff.mp hxc
    · rw [Work.Models.mem_conj_iff]
      have h1 : t⁻¹ * (t * x * t⁻¹) * t = x := by group
      rw [h1]; exact hxH
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ htNX hxN) (Subgroup.inv_mem _ htNX)
  have hcopU : Nat.Coprime (Nat.card U) 2 := by
    have hle : U ≤ Submission.Blueprint.twoPoint H t := by rw [hUdef]; exact inf_le_left
    exact Nat.coprime_two_right.mpr (Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le hle))
  have hU_le_NK1 : U ≤ Subgroup.normalizer (K₁ : Set G) := by
    intro z hz
    obtain ⟨hKappEq, hdec⟩ := (appI_one (d := 2) Nat.prime_two ht hnormU hcopU).2 rfl
    obtain ⟨⟨c, k⟩, ⟨hcC, hcU, hkKapp, hck⟩, -⟩ := hdec z hz
    have hcV1 : c ∈ V₁ := by
      rw [hV1def]
      rw [hUdef] at hcU
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hcU).1, hcC⟩,
        (Subgroup.mem_inf.mp hcU).2⟩
    have hkK1 : k ∈ K₁ := by
      have hkKset : k ∈ Work.NormalComplement.Kset U t := by rw [← hKappEq]; exact hkKapp
      obtain ⟨hkU, hkinv⟩ := Work.Models.mem_invertedBy_iff.mp hkKset
      rw [hUdef] at hkU
      exact hNKle ⟨⟨(Subgroup.mem_inf.mp hkU).1, hkinv⟩, (Subgroup.mem_inf.mp hkU).2⟩
    rw [← hck]
    exact Subgroup.mul_mem _ (hV1_le_NK1 hcV1) (Subgroup.le_normalizer hkK1)
  -- ## 6. `V₁ ⊓ C(Q) ⊆ V₁ ⊓ C(K₁)` from faithfulness of the regular action of `K₁` on `Q`
  have hfaithK : ∀ x ∈ K₁, (∀ q ∈ Q, x * q * x⁻¹ = q) → x = 1 := by
    intro x hx hfixq
    obtain ⟨y₀, ⟨hy₀K1, hy₀u⟩, huniq⟩ := hreg u huQ hu1 u huQ hu1
    have h1 : x = y₀ := huniq x ⟨hx, hfixq u huQ⟩
    have h2 : (1 : G) = y₀ := huniq 1 ⟨K₁.one_mem, by group⟩
    rw [h1, ← h2]
  have hsame_action : ∀ x ∈ K₁, ∀ y ∈ K₁,
      (∀ q ∈ Q, x * q * x⁻¹ = y * q * y⁻¹) → x = y := by
    intro x hx y hy hs
    have hyx : y⁻¹ * x ∈ K₁ := K₁.mul_mem (K₁.inv_mem hy) hx
    have htriv : ∀ q ∈ Q, (y⁻¹ * x) * q * (y⁻¹ * x)⁻¹ = q := by
      intro q hq
      calc (y⁻¹ * x) * q * (y⁻¹ * x)⁻¹ = y⁻¹ * (x * q * x⁻¹) * y := by group
        _ = y⁻¹ * (y * q * y⁻¹) * y := by rw [hs q hq]
        _ = q := by group
    have h1 : y⁻¹ * x = 1 := hfaithK _ hyx htriv
    have h2 : y * (y⁻¹ * x) = y * 1 := by rw [h1]
    simpa using h2
  have hCQ_le_CK : V₁ ⊓ Subgroup.centralizer (Q : Set G) ≤
      V₁ ⊓ Subgroup.centralizer (K₁ : Set G) := by
    intro v hv
    obtain ⟨hvV1, hvQ⟩ := Subgroup.mem_inf.mp hv
    refine Subgroup.mem_inf.mpr ⟨hvV1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hfixv : ∀ x ∈ Q, v * x * v⁻¹ = x := by
      intro x hx
      have h := (Subgroup.mem_centralizer_iff.mp hvQ) x hx
      rw [← h]; group
    have hfixvi : ∀ x ∈ Q, v⁻¹ * x * v = x := by
      intro x hx
      calc v⁻¹ * x * v = v⁻¹ * (v * x * v⁻¹) * v := by rw [hfixv x hx]
        _ = x := by group
    have hvk : v * k * v⁻¹ ∈ K₁ := hV1_norm v hvV1 k hk
    have hact : ∀ q ∈ Q, (v * k * v⁻¹) * q * (v * k * v⁻¹)⁻¹ = k * q * k⁻¹ := by
      intro q hq
      have hkq : k * q * k⁻¹ ∈ Q := Subgroup.le_normalizer_iff.mp hK1NQ k hk q hq
      calc (v * k * v⁻¹) * q * (v * k * v⁻¹)⁻¹
          = v * k * (v⁻¹ * q * v) * k⁻¹ * v⁻¹ := by group
        _ = v * k * q * k⁻¹ * v⁻¹ := by rw [hfixvi q hq]
        _ = v * (k * q * k⁻¹) * v⁻¹ := by group
        _ = k * q * k⁻¹ := hfixv _ hkq
    have hkeq : v * k * v⁻¹ = k := hsame_action _ hvk _ hk hact
    calc k * v = (v * k * v⁻¹) * v := by rw [hkeq]
      _ = v * k := by group
  -- ## 6b. `P ⊓ C(Q) = ⊥`
  have hPf : P ⊓ Subgroup.centralizer (Q : Set G) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxP, hxQ⟩ := Subgroup.mem_inf.mp hx
    have hxCK : x ∈ Subgroup.centralizer (K₁ : Set G) :=
      (Subgroup.mem_inf.mp
        (hCQ_le_CK (Subgroup.mem_inf.mpr ⟨hP_le_V1 hxP, hxQ⟩))).2
    obtain ⟨k, hkNK, hk1⟩ := hNK
    have hkK1 : k ∈ K₁ := hNKle hkNK
    have hcomm : x * k * x⁻¹ = k := by
      have hxk : k * x = x * k := (Subgroup.mem_centralizer_iff.mp hxCK) k hkK1
      rw [← hxk]; group
    rw [Subgroup.mem_bot]
    by_contra hx1
    exact hk1 (hfpf x hxP hx1 k hkNK hcomm)
  -- ## 7. `|C_Q(P₁)| = 2` for `1 ≠ P₁ ≤ P`
  have hfix : ∀ P₁ : Subgroup G, P₁ ≤ P → P₁ ≠ ⊥ →
      Nat.card ↥(Q ⊓ Subgroup.centralizer (P₁ : Set G)) = 2 :=
    sec1_lemma3_fixpts (H := H) (X := X) (P := P) (Q := Q) (K₁ := K₁) (t := t) (u := u)
      hK1car hQcar hreg hV1_le_NK1 huQ hu1 hP_le_V1 hPu hfpf
  -- ## 8. `K₁` is irreducible on `Q` (it acts regularly on `Q#`)
  have hQexp : ∀ x ∈ Q, x ^ 2 = 1 := by
    intro x hx
    rw [pow_two]; exact hQsq x hx
  have hirr : ∀ R : Subgroup G, R ≤ Q → K₁ ≤ Subgroup.normalizer (R : Set G) →
      R = ⊥ ∨ R = Q := by
    intro R hRQ hKR
    by_cases hR : R = ⊥
    · exact Or.inl hR
    · right
      obtain ⟨x, hxR, hx1⟩ : ∃ x ∈ R, x ≠ 1 := by
        by_contra h
        apply hR
        rw [eq_bot_iff]
        intro y hy
        by_contra hy1
        exact h ⟨y, hy, hy1⟩
      have hxQ : x ∈ Q := hRQ hxR
      have hsubset : ∀ b ∈ Q, b ≠ 1 → b ∈ R := by
        intro b hbQ hb1
        obtain ⟨k, hkK1, hkb⟩ := (hreg x hxQ hx1 b hbQ hb1).exists
        have hk := Subgroup.le_normalizer_iff.mp hKR k hkK1 x hxR
        rwa [hkb] at hk
      refine le_antisymm hRQ ?_
      intro b hbQ
      by_cases hb1 : b = 1
      · rw [hb1]; exact R.one_mem
      · exact hsubset b hbQ hb1
  -- ## 9. App. V (d), product form
  obtain ⟨hprime, hcardQ, hcent⟩ :=
    appV_prod (G := G) 2 U Q K₁ P Nat.prime_two hQcomm hQexp hQne hU_le_NQ hK1leU
      hU_le_NK1 hK1cyc hirr hP_le_U hP hPf hfix
  have hUc : U ⊓ Subgroup.centralizer ({u} : Set G) = V₁ := by
    rw [hUdef, hV1def, huV]
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  have hUcQ : U ⊓ Subgroup.centralizer (Q : Set G) = V₁ ⊓ Subgroup.centralizer (Q : Set G) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxU, hxQ⟩ := Subgroup.mem_inf.mp hx
      have hxCu : x ∈ Subgroup.centralizer ({u} : Set G) :=
        Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huQ) hxQ
      rw [hUdef] at hxU
      obtain ⟨hxD, hxN⟩ := Subgroup.mem_inf.mp hxU
      refine Subgroup.mem_inf.mpr ⟨?_, hxQ⟩
      rw [hV1def]
      exact Subgroup.mem_inf.mpr ⟨by rw [huV]; exact ⟨hxD, hxCu⟩, hxN⟩
    · intro x hx
      obtain ⟨hxV1, hxQ⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨?_, hxQ⟩
      rw [hV1def] at hxV1
      rw [hUdef]
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hxV1).1.1, (Subgroup.mem_inf.mp hxV1).2⟩
  have hV1eq : V₁ = P ⊔ (V₁ ⊓ Subgroup.centralizer (Q : Set G)) :=
    calc V₁ = U ⊓ Subgroup.centralizer ({u} : Set G) := hUc.symm
      _ = P ⊔ (U ⊓ Subgroup.centralizer (Q : Set G)) := hcent u huQP hu1
      _ = P ⊔ (V₁ ⊓ Subgroup.centralizer (Q : Set G)) := by rw [hUcQ]
  -- ## 10. arithmetic for the cardinality conjunct
  set S : Set G := Submission.Blueprint.involutions
    ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) with hSdef
  have hQcar' : (Q : Set G) = insert 1 S := by rw [hQcar, hSdef]
  have hconj_mem_S : ∀ a ∈ K₁, a * u * a⁻¹ ∈ S := by
    intro a ha
    have haU : a ∈ U := hK1leU ha
    rw [hUdef] at haU
    obtain ⟨haD, haN⟩ := Subgroup.mem_inf.mp haU
    have haH : a ∈ H := (Subgroup.mem_inf.mp haD).1
    rw [hSdef]
    exact ⟨⟨H.mul_mem (H.mul_mem haH huH) (H.inv_mem haH),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ haN huNX) (Subgroup.inv_mem _ haN)⟩,
      by rw [Work.ThmF.Bender.orderOf_conj_eq, hu2]⟩
  have hconj_ne_one : ∀ a ∈ K₁, a * u * a⁻¹ ≠ 1 := by
    intro a ha h
    have hu_eq : u = 1 := by
      calc u = a⁻¹ * (a * u * a⁻¹) * a := by group
        _ = a⁻¹ * 1 * a := by rw [h]
        _ = 1 := by group
    exact hu1 hu_eq
  have hmemQ : ∀ a ∈ K₁, a * u * a⁻¹ ∈ Q := by
    intro a ha
    have h : a * u * a⁻¹ ∈ (Q : Set G) := by rw [hQcar']; exact Or.inr (hconj_mem_S a ha)
    exact h
  have hbij : Nat.card ↥K₁ = S.ncard := by
    have hf : ∀ k : ↥K₁, (k : G) * u * (k : G)⁻¹ ∈ S := fun k => hconj_mem_S k k.2
    have hinj : Function.Injective (fun k : ↥K₁ => (⟨(k : G) * u * (k : G)⁻¹, hf k⟩ : ↥S)) := by
      intro k k' h
      have hval : (k : G) * u * (k : G)⁻¹ = (k' : G) * u * (k' : G)⁻¹ := congrArg Subtype.val h
      obtain ⟨y, ⟨hyK, hyv⟩, hyuni⟩ :=
        hreg u huQ hu1 ((k : G) * u * (k : G)⁻¹) (hmemQ k k.2) (hconj_ne_one k k.2)
      exact Subtype.ext ((hyuni k ⟨k.2, rfl⟩).trans (hyuni k' ⟨k'.2, hval.symm⟩).symm)
    have hsurj : Function.Surjective (fun k : ↥K₁ => (⟨(k : G) * u * (k : G)⁻¹, hf k⟩ : ↥S)) := by
      intro b
      have hbQ : (b : G) ∈ (Q : Set G) := by rw [hQcar']; exact Or.inr b.2
      have hb1 : (b : G) ≠ 1 := by
        intro h
        have h2 : orderOf (b : G) = 2 := (Work.Models.mem_involutions_iff.mp b.2).2
        rw [h, orderOf_one] at h2
        exact absurd h2 (by norm_num)
      obtain ⟨y, ⟨hyK, hyv⟩, -⟩ := hreg u huQ hu1 (b : G) hbQ hb1
      exact ⟨⟨y, hyK⟩, Subtype.ext hyv⟩
    exact Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)
  have hQncard : Nat.card ↥Q = (Q : Set G).ncard := by
    rw [← Set.ncard_univ (α := ↥Q), Set.ncard_coe]
  have hK1ncard : Nat.card ↥K₁ = 2 ^ Nat.card P - 1 := by
    have h1S : (1 : G) ∉ S := by
      rw [hSdef]; exact Work.Models.one_notMem_involutions _
    have h1 : (Q : Set G).ncard = S.ncard + 1 := by
      rw [hQcar']
      exact Set.ncard_insert_of_notMem h1S
    have h2 : (Q : Set G).ncard = Nat.card ↥K₁ + 1 := by rw [h1, ← hbij]
    omega
  -- ## 11. the final conjuncts
  refine ⟨hNKeqCK, ?_, ?_, ?_⟩
  · have hset : Work.NormalComplement.Design.CK H t X = (K₁ : Set G) :=
      hNKeqCK.symm.trans hK1car.symm
    rw [hset]
    have hcnt : (K₁ : Set G).ncard = Nat.card ↥K₁ :=
      (Set.ncard_coe (K₁ : Set G)).symm.trans (Set.ncard_univ (α := ↥(K₁ : Set G)))
    rw [hcnt]
    exact hK1ncard
  · have hA : V₁ ⊓ Subgroup.centralizer (Work.NormalComplement.Design.NK H t X) =
        V₁ ⊓ Subgroup.centralizer (K₁ : Set G) := by
      rw [show (Work.NormalComplement.Design.NK H t X) = (K₁ : Set G) from hK1car.symm]
    rw [hA]
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxV1CK, hxP⟩ := Subgroup.mem_inf.mp hx
    have hxCK : x ∈ Subgroup.centralizer (K₁ : Set G) := (Subgroup.mem_inf.mp hxV1CK).2
    obtain ⟨k, hkNK, hk1⟩ := hNK
    have hkK1 : k ∈ K₁ := hNKle hkNK
    have hcomm : x * k * x⁻¹ = k := by
      have hxk : k * x = x * k := (Subgroup.mem_centralizer_iff.mp hxCK) k hkK1
      rw [← hxk]; group
    rw [Subgroup.mem_bot]
    by_contra hx1
    exact hk1 (hfpf x hxP hx1 k hkNK hcomm)
  · have hA : V₁ ⊓ Subgroup.centralizer (Work.NormalComplement.Design.NK H t X) =
        V₁ ⊓ Subgroup.centralizer (K₁ : Set G) := by
      rw [show (Work.NormalComplement.Design.NK H t X) = (K₁ : Set G) from hK1car.symm]
    rw [hA]
    refine le_antisymm ?_ ?_
    · exact sup_le inf_le_left hP_le_V1
    · calc V₁ = P ⊔ (V₁ ⊓ Subgroup.centralizer (Q : Set G)) := hV1eq
        _ ≤ P ⊔ (V₁ ⊓ Subgroup.centralizer (K₁ : Set G)) :=
            sup_le_sup_left hCQ_le_CK P
        _ = (V₁ ⊓ Subgroup.centralizer (K₁ : Set G)) ⊔ P := by rw [sup_comm]

end Work.NormalComplement
