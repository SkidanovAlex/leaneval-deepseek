import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.MDataAux
import Submission.Work.CORE3.H_eq_U_sup_S
import Submission.Work.CORE3.MData.OddCoreLeBc
import Submission.Work.CORE3.MData.BcInfMLeOddCore
import Submission.Work.CORE3.MData.LayerSurjA7Surj
import Submission.Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot
import Submission.Work.CORE2A.Basic

/-!
# CORE3 (`MData`): `U ∩ M ≤ P₀ ⊔ B` in the subcase `Ĥ = H`

Deliverable `Work.CORE3.MData.UMLe`, the `≤`-direction of the third conjunct of
`Work.CORE3.Case1aMDataProp` (Bender 1981, §3, p. 223, display `U ∩ M = P₀ × (B ∩ M)`),
for `P₀ = O_p(U) ∩ M` and `B = C_U(S)`.

Writing `V := U ∩ M` and `C := C_M(E(M)) = O(M)` (so `C ≤ B`, by
`Work.CORE3.MData.OddCoreLeBc`), the argument is:

* `C_M(t) = V ⊔ S`, so `|C_M(t)| = 8|V|`;
* the image of `C_M(t)` under the surjection `M ↠ M/C ≅ A₇` (Bender's `E/Z(E) ≅ A₇`,
  `Work.CORE3.MData.LayerSurjA7`) lies in the centralizer of an involution of `A₇`, of order `24`
  (`A7ModelProp`); hence `8|V| ≤ 24|C|` and `|V| ≤ 3|C|`;
* `P₀ ⊓ B = 1` (`D.inv` inverts `O_p(U)` while `B` centralizes `S ∋ D.t2`), so `|V| ≥ 3|C|`;
* hence `|V| = 3|C|`, `V = P₀ · C` and `V ≤ P₀ ⊔ B`.
-/

set_option linter.style.haveILetI false

namespace Work.CORE3.MData

open Subgroup
open Work.GW2
open scoped Pointwise

/-- **Cardinality of the image of a subgroup.**  For a group homomorphism `f` and a subgroup `X`,
`|X.map f| * |X ⊓ f.ker| = |X|`. -/
theorem card_map_mul_card_inf_ker {G N : Type*} [Group G] [Group N] (f : G →* N)
    (X : Subgroup G) : Nat.card ↥(X.map f) * Nat.card ↥(X ⊓ f.ker) = Nat.card ↥X := by
  let φ : ↥X →* N := f.comp X.subtype
  have hker : φ.ker = (X ⊓ f.ker).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, MonoidHom.mem_ker]
    show f (x : G) = 1 ↔ (x : G) ∈ X ∧ f (x : G) = 1
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hrange : φ.range = X.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h1 : Nat.card ↥(X.map f) = φ.ker.index := by
    rw [← hrange, Subgroup.index_eq_card φ.ker]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv).symm
  have h2 : Nat.card ↥φ.ker = Nat.card ↥(X ⊓ f.ker) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h1, ← h2]
  exact Subgroup.index_mul_card φ.ker

/-- A natural number is coprime to `8` as soon as it is odd. -/
theorem coprime_eight_of_odd {n : ℕ} (h : Odd n) : Nat.Coprime n 8 := by
  have h2 : Nat.Coprime n 2 := (Nat.coprime_two_left.mpr h).symm
  simpa using h2.pow_right 3

/-- `K` normalizes `O(K) = O_{2'}(K)`. -/
theorem le_normalizer_oddCoreIn_self {G : Type*} [Group G] [Finite G] (K : Subgroup G) :
    K ≤ Subgroup.normalizer ((Work.GW2.oddCoreIn K : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro k hk x hx
  rw [Work.GW2.oddCoreIn, Subgroup.mem_map] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹,
    (Work.GW2.oddCore_normal ↥K).conj_mem y hy ⟨k, hk⟩, by simp⟩

/-- An element of order two of `E` is not central when `|Z(E)|` is odd (used to see that the
image of `B.t` in `A₇` is a genuine involution). -/
theorem not_mem_center_of_sq_eq_one {X : Type*} [Group X] (E : Subgroup X)
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥E))) {x : X} (hx : x ∈ E)
    (hx2 : x ^ 2 = 1) (hxne : x ≠ 1) : (⟨x, hx⟩ : ↥E) ∉ Subgroup.center ↥E := by
  intro hxZ
  have hord : orderOf (⟨x, hx⟩ : ↥E) = 2 := by
    have h2 : (⟨x, hx⟩ : ↥E) ^ 2 = 1 := by
      apply Subtype.ext
      show x ^ 2 = 1
      exact hx2
    have hne : (⟨x, hx⟩ : ↥E) ≠ 1 := fun h1 => hxne (Subtype.ext_iff.mp h1)
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr h2) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  have hle : Subgroup.zpowers (⟨x, hx⟩ : ↥E) ≤ Subgroup.center ↥E := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Subgroup.zpow_mem _ hxZ k
  have hdvd : Nat.card ↥(Subgroup.zpowers (⟨x, hx⟩ : ↥E)) ∣
      Nat.card ↥(Subgroup.center ↥E) := Subgroup.card_dvd_of_le hle
  rw [Nat.card_zpowers, hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem UMLe (I : Work.CORE3.Case1Inputs) (hSetup : Work.GW2.Case1aSetupProp)
    (hFr : Work.GW2.Case1aFrattiniProp) (hAb : Work.GW2.Case1aAbelianProp)
    (hA7 : Work.GW2.Case1aA7Prop) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G, Work.GW2.Case1 B → B.Hhat = B.H →
      ∀ D : Work.GW2.Case1aData B, ∀ P2 M : Subgroup G,
      P2 ≤ B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) → IsPGroup D.p P2 →
      ¬ D.p ∣ P2.relIndex (B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G)) →
      IsCoatom M → Subgroup.normalizer (P2 : Set G) ≤ M →
      B.U ⊓ M ≤ (Work.GW2.pCoreIn D.p B.U ⊓ M) ⊔
        (B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G)) := by
  intro G _instG _finG hFT hCtx B hCase hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- ## the `A₇`-data of the §3 `M`-analysis
  obtain ⟨hSM, hV2, hEiso0, hScard, hP0card⟩ :=
    hA7 G hFT hCtx B hCase hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM
  obtain ⟨f, hfsurj, hfker⟩ :=
    LayerSurjA7Surj I hSetup hFr hAb hA7 G hFT hCtx B hCase hHhat D P2 M
      hP2le hP2grp hP2ndvd hMcoat hNM
  -- ## `t ∈ E(M)`, and `E(M)` is non-trivial
  have htS : B.t ∈ (B.S : Subgroup G) := Work.CORE2A.bSetup_t_mem_S B
  have htM : B.t ∈ M := hSM htS
  have htE : B.t ∈ Work.GW2.layerIn M :=
    hV2 (Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t))
  have htlay : (⟨B.t, htM⟩ : ↥M) ∈ Work.GW2.layer ↥M := by
    rw [Work.GW2.layerIn, Subgroup.mem_map] at htE
    obtain ⟨y, hy, hyeq⟩ := htE
    have hyy : y = ⟨B.t, htM⟩ := Subtype.ext hyeq
    rwa [hyy] at hy
  have hneM : (⟨B.t, htM⟩ : ↥M) ≠ 1 :=
    fun h1 => Work.CORE2A.bSetup_t_ne_one B (Subtype.ext_iff.mp h1)
  have hlayer_ne : Work.GW2.layer ↥M ≠ ⊥ := by
    intro hbot
    have h1 : Work.GW2.layerIn M = ⊥ := by
      show (Work.GW2.layer ↥M).map M.subtype = ⊥
      rw [hbot, Subgroup.map_bot]
    exact Work.CORE2A.bSetup_t_ne_one B (Subgroup.mem_bot.mp (h1 ▸ htE))
  obtain ⟨hEq, hZodd⟩ := mdata_layer_quasisimple I hCtx B hMcoat hlayer_ne
  -- ## `|M|₂ = 2³` and `E(M)/Z(E(M)) ≅ A₇`
  let SM : Sylow 2 ↥M := Sylow.subtype B.S hSM
  have hSMcoe : (SM : Subgroup ↥M) = ((B.S : Subgroup G)).subgroupOf M := Sylow.coe_subtype B.S hSM
  have hSMcard : Nat.card ↥(SM : Subgroup ↥M) = 8 := by
    rw [hSMcoe, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv, hScard]
  have h2M : (Nat.card ↥M).factorization 2 = 3 := by
    have h : Nat.card ↥(SM : Subgroup ↥M) = 2 ^ ((Nat.card ↥M).factorization 2) :=
      Sylow.card_eq_multiplicity SM
    rw [hSMcard] at h
    have h' : 2 ^ ((Nat.card ↥M).factorization 2) = 2 ^ 3 := by rw [← h]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h'
  have hisoE : Nonempty ((↥(Work.GW2.layer ↥M) ⧸ Subgroup.center ↥(Work.GW2.layer ↥M)) ≃*
      alternatingGroup (Fin 7)) := by
    obtain ⟨e⟩ := hEiso0
    let ee : ↥(Work.GW2.layer ↥M) ≃* ↥(Work.GW2.layerIn M) :=
      Subgroup.equivMapOfInjective (Work.GW2.layer ↥M) M.subtype M.subtype_injective
    have hcen : Subgroup.map (ee : ↥(Work.GW2.layer ↥M) →* ↥(Work.GW2.layerIn M))
        (Subgroup.center ↥(Work.GW2.layer ↥M)) = Subgroup.center ↥(Work.GW2.layerIn M) :=
      Subgroup.map_center_eq ee
    exact ⟨(QuotientGroup.congr (Subgroup.center ↥(Work.GW2.layer ↥M))
      (Subgroup.center ↥(Work.GW2.layerIn M)) ee hcen).trans e⟩
  have hCodd : Odd (Nat.card ↥(Subgroup.centralizer
      (((Work.GW2.layer ↥M : Subgroup ↥M)) : Set ↥M))) :=
    OddCentralizerLayerAux M hEq hZodd h2M hisoE
  -- ## the subgroups of the argument
  set V : Subgroup G := B.U ⊓ M with hVdef
  set C : Subgroup ↥M := f.ker with hCdef
  set CgM : Subgroup G := C.map M.subtype with hCgMdef
  set P0 : Subgroup G := Work.GW2.pCoreIn D.p B.U ⊓ M with hP0def
  set Bc : Subgroup G := B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) with hBcdef
  have hVodd : Odd (Nat.card ↥V) :=
    Odd.of_dvd_nat (Work.CORE2A.bSetup_U_odd B) (Subgroup.card_dvd_of_le inf_le_left)
  have hUodd : Odd (Nat.card ↥B.U) := Work.CORE2A.bSetup_U_odd B
  -- ## `C ≤ O(M) ≤ B`
  have hCdef' : C = Subgroup.centralizer (((Work.GW2.layer ↥M : Subgroup ↥M)) : Set ↥M) :=
    hCdef.trans hfker
  have hCodd' : Odd (Nat.card ↥C) := by rw [hCdef']; exact hCodd
  have hCgM_le_M : CgM ≤ M := by rw [hCgMdef]; exact Subgroup.map_subtype_le C
  have hCgM_sub : (CgM.subgroupOf M) = C := by
    rw [hCgMdef, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hCgM_le_O : CgM ≤ Work.GW2.oddCoreIn M := by
    refine Work.CORE2A.le_oddCoreIn_of_normal_of_odd hCgM_le_M ?_ ?_
    · rw [hCgM_sub]; exact inferInstance
    · rw [hCgMdef, Subgroup.card_map_of_injective M.subtype_injective]; exact hCodd'
  have hO_le_Bc : Work.GW2.oddCoreIn M ≤ Bc :=
    OddCoreLeBc I hSetup hFr hAb hA7 G hFT hCtx B hCase hHhat D P2 M
      hP2le hP2grp hP2ndvd hMcoat hNM
  have hO_le_U : Work.GW2.oddCoreIn M ≤ B.U := (le_inf_iff.mp hO_le_Bc).1
  have hCgM_le_Bc : CgM ≤ Bc := hCgM_le_O.trans hO_le_Bc
  have hCgM_le_V : CgM ≤ V := le_inf (hCgM_le_O.trans hO_le_U) hCgM_le_M
  have hCgM_card : Nat.card ↥CgM = Nat.card ↥C := by
    rw [hCgMdef]; exact Subgroup.card_map_of_injective M.subtype_injective
  -- ## `P₀ ⊓ B = 1`
  have hP0_le_V : P0 ≤ V := by
    refine le_inf ?_ inf_le_right
    exact le_trans inf_le_left (Subgroup.map_subtype_le (Work.GW2.pCore D.p ↥B.U))
  have hP0card' : Nat.card ↥P0 = 3 := by rw [hP0def]; exact hP0card
  have hP0_inf_Bc : P0 ⊓ Bc = ⊥ := by
    have hp : Work.GW2.pCoreIn D.p B.U ⊓ Subgroup.centralizer ({D.t2} : Set G) = ⊥ :=
      Work.CORE2A.inverts_inf_centralizer_eq_bot_of_odd D.inv
        (Odd.of_dvd_nat hUodd
          (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le (Work.GW2.pCore D.p ↥B.U))))
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxP0, hxBc⟩ := Subgroup.mem_inf.mp hx
    have hxP0' : x ∈ Work.GW2.pCoreIn D.p B.U ⊓ M := hP0def ▸ hxP0
    obtain ⟨hxP, _hxM⟩ := Subgroup.mem_inf.mp hxP0'
    have hxBc' : x ∈ B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) :=
      hBcdef ▸ hxBc
    obtain ⟨_hxU, hxcen⟩ := Subgroup.mem_inf.mp hxBc'
    have hx1 : x ∈ Work.GW2.pCoreIn D.p B.U ⊓ Subgroup.centralizer ({D.t2} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hxP, ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hxcen ⊢
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hxcen D.t2 D.t2_mem
    rw [hp] at hx1
    exact hx1
  have hP0_inf_CgM : P0 ⊓ CgM = ⊥ :=
    le_antisymm (le_trans (inf_le_inf le_rfl hCgM_le_Bc) (le_of_eq hP0_inf_Bc)) bot_le
  -- ## `C_M(t) = V ⊔ S` and `|C_M(t)| = 8|V|`
  have hVS_bot : V ⊓ (B.S : Subgroup G) = ⊥ := by
    have hodd : Odd (Nat.card ↥(V ⊓ (B.S : Subgroup G))) :=
      Odd.of_dvd_nat hVodd (Subgroup.card_dvd_of_le inf_le_left)
    have hdvd : Nat.card ↥(V ⊓ (B.S : Subgroup G)) ∣ 8 := by
      rw [← hScard]; exact Subgroup.card_dvd_of_le inf_le_right
    exact Subgroup.card_eq_one.mp
      (Nat.eq_one_of_dvd_coprimes (coprime_eight_of_odd hodd) dvd_rfl hdvd)
  have hS_le_normU : (B.S : Subgroup G) ≤ Subgroup.normalizer (B.U : Set G) :=
    (Work.CORE2A.bSetup_S_le_H B).trans
      (Work.CORE3.MData.le_normalizer_oddCoreIn_self B.H)
  have hS_le_normV : (B.S : Subgroup G) ≤ Subgroup.normalizer (V : Set G) := by
    have h1 : (B.S : Subgroup G) ≤ Subgroup.normalizer (B.U : Set G) := hS_le_normU
    have h2 : (B.S : Subgroup G) ≤ Subgroup.normalizer (M : Set G) :=
      hSM.trans Subgroup.le_normalizer
    refine (le_inf h1 h2).trans ?_
    show Subgroup.normalizer (B.U : Set G) ⊓ Subgroup.normalizer (M : Set G)
      ≤ Subgroup.normalizer ((B.U ⊓ M : Subgroup G) : Set G)
    exact Subgroup.inf_normalizer_le_normalizer_inf
  have hCt_eq : Subgroup.centralizer ({B.t} : Set G) ⊓ M = V ⊔ (B.S : Subgroup G) := by
    show B.H ⊓ M = V ⊔ (B.S : Subgroup G)
    rw [(Work.CORE3.H_eq_U_sup_S G I.T hCtx B).symm]
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxUS, hxM⟩ := Subgroup.mem_inf.mp hx
      have hcoe : ((B.U ⊔ (B.S : Subgroup G) : Subgroup G) : Set G) =
          (B.U : Set G) * ((B.S : Subgroup G) : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left B.U (B.S : Subgroup G) hS_le_normU
      have hxUS' : x ∈ (B.U : Set G) * ((B.S : Subgroup G) : Set G) := by
        rw [← hcoe]; exact hxUS
      obtain ⟨u, hu, s, hs, hus⟩ := Set.mem_mul.mp hxUS'
      have huM : u ∈ M := by
        have h1 : u * s * s⁻¹ ∈ M := M.mul_mem (hus ▸ hxM) (M.inv_mem (hSM hs))
        rwa [mul_assoc, mul_inv_cancel, mul_one] at h1
      rw [← hus]
      exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hu, huM⟩) hs
    · refine sup_le (le_inf (le_trans inf_le_left le_sup_left) inf_le_right)
        (le_inf le_sup_right hSM)
  have hCt_card : Nat.card ↥(Subgroup.centralizer ({B.t} : Set G) ⊓ M) = Nat.card ↥V * 8 := by
    rw [hCt_eq, Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot hS_le_normV hVS_bot,
      hScard]
  -- ## `C_M(t)` inside `↥M`
  set CtM : Subgroup ↥M := Subgroup.centralizer ({⟨B.t, htM⟩} : Set ↥M) with hCtMdef
  have hC_le_CtM : C ≤ CtM := by
    rw [hCdef', hCtMdef]
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htlay)
  have hCtM_map : CtM.map M.subtype = Subgroup.centralizer ({B.t} : Set G) ⊓ M := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hCtMdef, Subgroup.mem_centralizer_iff] at hy
      refine ⟨?_, y.2⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact Subtype.ext_iff.mp (hy ⟨B.t, htM⟩ (by rw [Set.mem_singleton_iff]))
    · rintro ⟨hx1, hx2⟩
      refine ⟨⟨x, hx2⟩, ?_, rfl⟩
      rw [hCtMdef, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      apply Subtype.ext
      rw [Subgroup.mem_centralizer_iff] at hx1
      exact hx1 B.t (by rw [Set.mem_singleton_iff])
  have hCtM_card : Nat.card ↥CtM = Nat.card ↥V * 8 := by
    rw [← Subgroup.card_map_of_injective (f := M.subtype) (K := CtM) M.subtype_injective,
      hCtM_map, hCt_card]
  -- ## the image of `C_M(t)` in `A₇`
  have hCtM_le_a7 : CtM.map f ≤
      Subgroup.centralizer ({f ⟨B.t, htM⟩} : Set (alternatingGroup (Fin 7))) := by
    refine (Subgroup.map_centralizer_le_centralizer_image
      ({⟨B.t, htM⟩} : Set ↥M) f).trans ?_
    rw [Set.image_singleton]
  have htM_order : orderOf (⟨B.t, htM⟩ : ↥M) = 2 := by
    have h2 : (⟨B.t, htM⟩ : ↥M) ^ 2 = 1 := by
      apply Subtype.ext
      show B.t ^ 2 = 1
      rw [← orderOf_dvd_iff_pow_eq_one, B.t_order]
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr h2) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hneM
    · exact h
  have hft_order : orderOf (f ⟨B.t, htM⟩) = 2 := by
    have hx2 : (⟨B.t, htM⟩ : ↥M) ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, htM_order]
    have h2 : (f ⟨B.t, htM⟩) ^ 2 = 1 := by
      rw [← map_pow, hx2, map_one]
    have hne : f ⟨B.t, htM⟩ ≠ 1 := by
      intro h1
      have hmem : (⟨B.t, htM⟩ : ↥M) ∈ C := MonoidHom.mem_ker.mpr h1
      rw [hfker, Subgroup.mem_centralizer_iff] at hmem
      have hZmem : (⟨⟨B.t, htM⟩, htlay⟩ : ↥(Work.GW2.layer ↥M)) ∈
          Subgroup.center ↥(Work.GW2.layer ↥M) := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext
          (show (y : ↥M) * ⟨B.t, htM⟩ = ⟨B.t, htM⟩ * (y : ↥M) from hmem (y : ↥M) y.2)
      exact (not_mem_center_of_sq_eq_one (Work.GW2.layer ↥M) hZodd htlay hx2 hneM) hZmem
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr h2) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  have h24 : Nat.card ↥(Subgroup.centralizer
      ({f ⟨B.t, htM⟩} : Set (alternatingGroup (Fin 7)))) = 24 :=
    (I.T.a7).2.2.1 (f ⟨B.t, htM⟩) hft_order
  -- ## the counting: `|V| ≤ 3|C|`
  have hCtM_fact : Nat.card ↥(CtM.map f) * Nat.card ↥C = Nat.card ↥V * 8 := by
    have h := card_map_mul_card_inf_ker f CtM
    have hinf : CtM ⊓ f.ker = C := by rw [← hCdef]; exact inf_eq_right.mpr hC_le_CtM
    rw [hinf, hCtM_card] at h
    exact h
  have hle24 : Nat.card ↥(CtM.map f) ≤ 24 := by
    have h := Subgroup.card_dvd_of_le hCtM_le_a7
    rw [h24] at h
    exact Nat.le_of_dvd (by norm_num) h
  have hV_le_3C : Nat.card ↥V ≤ 3 * Nat.card ↥C := by
    have h' : Nat.card ↥V * 8 ≤ 24 * Nat.card ↥C := by
      rw [← hCtM_fact]; exact Nat.mul_le_mul_right _ hle24
    have h'' : 8 * Nat.card ↥V ≤ 8 * (3 * Nat.card ↥C) := by
      calc 8 * Nat.card ↥V = Nat.card ↥V * 8 := by ring
        _ ≤ 24 * Nat.card ↥C := h'
        _ = 8 * (3 * Nat.card ↥C) := by ring
    exact Nat.le_of_mul_le_mul_left h'' (by norm_num)
  -- ## the lower bound: `3|C| ≤ |V|`, via `P₀`
  set Vsub : Subgroup ↥M := V.subgroupOf M with hVsubdef
  have hVsub_card : Nat.card ↥Vsub = Nat.card ↥V := by
    rw [hVsubdef]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hC_le_Vsub : C ≤ Vsub := by
    intro x hx
    rw [hVsubdef, Subgroup.mem_subgroupOf]
    exact hCgM_le_V (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hP0sub_inf_C : (P0.subgroupOf M) ⊓ C = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_subgroupOf] at hx1
    have hx' : (x : G) ∈ P0 ⊓ CgM := ⟨hx1, Subgroup.mem_map.mpr ⟨x, hx2, rfl⟩⟩
    rw [hP0_inf_CgM] at hx'
    exact Subtype.ext (Subgroup.mem_bot.mp hx')
  have hP0sub_le_Vsub : (P0.subgroupOf M) ≤ Vsub := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [hVsubdef, Subgroup.mem_subgroupOf]
    exact hP0_le_V hx
  have hP0map_card : Nat.card ↥((P0.subgroupOf M).map f) = 3 := by
    have h := card_map_mul_card_inf_ker f (P0.subgroupOf M)
    have hinf : (P0.subgroupOf M) ⊓ f.ker = ⊥ := by rw [← hCdef]; exact hP0sub_inf_C
    rw [hinf, Subgroup.card_bot, mul_one] at h
    rw [h]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).trans hP0card'
  have hVsub_le_CtM : Vsub ≤ CtM := by
    intro x hx
    rw [hVsubdef, Subgroup.mem_subgroupOf] at hx
    have hx' : (x : G) ∈ B.U ⊓ M := hVdef ▸ hx
    obtain ⟨hxU, _hxM⟩ := Subgroup.mem_inf.mp hx'
    rw [hCtMdef, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (Work.CORE2A.bSetup_U_le_H B hxU)) B.t
      (Set.mem_singleton B.t)
  have hVsubmap_ge3 : 3 ≤ Nat.card ↥(Vsub.map f) := by
    have hdiv : 3 ∣ Nat.card ↥(Vsub.map f) := by
      rw [← hP0map_card]
      exact Subgroup.card_dvd_of_le (Subgroup.map_mono hP0sub_le_Vsub)
    have hne : Nat.card ↥(Vsub.map f) ≠ 0 :=
      Nat.card_ne_zero.mpr ⟨⟨f 1, Subgroup.mem_map.mpr ⟨1, Subgroup.one_mem Vsub, rfl⟩⟩,
        inferInstance⟩
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdiv
  have hVsubmap_dvd3 : Nat.card ↥(Vsub.map f) ∣ 3 := by
    have hodd : Odd (Nat.card ↥(Vsub.map f)) :=
      Odd.of_dvd_nat (by rw [hVsub_card]; exact hVodd) (Subgroup.card_map_dvd Vsub f)
    have h24dv : Nat.card ↥(Vsub.map f) ∣ 24 := by
      rw [← h24]
      exact Subgroup.card_dvd_of_le ((Subgroup.map_mono hVsub_le_CtM).trans hCtM_le_a7)
    exact (coprime_eight_of_odd hodd).dvd_of_dvd_mul_right
      (by rw [show (3 : ℕ) * 8 = 24 from by norm_num]; exact h24dv)
  have hVsubmap_eq3 : Nat.card ↥(Vsub.map f) = 3 :=
    le_antisymm (Nat.le_of_dvd (by norm_num) hVsubmap_dvd3) hVsubmap_ge3
  -- ## `V = P₀ · C`
  have hVsubmap_eq : (P0.subgroupOf M).map f = Vsub.map f :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hP0sub_le_Vsub)
      (by rw [hP0map_card, hVsubmap_eq3])
  have hV_le_C : V ≤ P0 ⊔ CgM := by
    intro v hv
    have hv' : v ∈ B.U ⊓ M := hVdef ▸ hv
    obtain ⟨_hvU, hvM⟩ := Subgroup.mem_inf.mp hv'
    set vm : ↥M := ⟨v, hvM⟩ with hvm
    have hvmVsub : vm ∈ Vsub := by
      rw [hVsubdef, Subgroup.mem_subgroupOf]
      exact hv
    have hfvm : f vm ∈ (P0.subgroupOf M).map f := by
      rw [hVsubmap_eq]
      exact Subgroup.mem_map.mpr ⟨vm, hvmVsub, rfl⟩
    obtain ⟨p, hp, hfp⟩ := Subgroup.mem_map.mp hfvm
    have hpc : vm * p⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfp, mul_inv_cancel]
    have hcG : M.subtype (vm * p⁻¹) ∈ CgM :=
      Subgroup.mem_map.mpr ⟨vm * p⁻¹, hpc, rfl⟩
    have hpG : M.subtype p ∈ P0 := Subgroup.mem_subgroupOf.mp hp
    have hdecomp : v = M.subtype (vm * p⁻¹) * M.subtype p := by
      have h1 : M.subtype (vm * p⁻¹) = v * (M.subtype p)⁻¹ := by
        show M.subtype (⟨v, hvM⟩ * p⁻¹) = v * (M.subtype p)⁻¹
        rw [map_mul, map_inv]
        rfl
      rw [h1]
      group
    rw [hdecomp, sup_comm]
    exact Subgroup.mul_mem_sup hcG hpG
  exact hV_le_C.trans (sup_le le_sup_left (hCgM_le_Bc.trans le_sup_right))

end Work.CORE3.MData
