import Mathlib
import Submission.Work.CORE4.Defs27
import Submission.Work.CORE4.Case2S0_comm_U
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2SNotMemS0
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2EHcard
import Submission.Work.CORE4.A7VnotCyclicAux
import Submission.Work.CORE4.SevenX.piFU_le_pi_K0F
import Submission.Work.CORE4.exists_conj_le_of_le_sylow
import Submission.Work.CORE4.mul_mem_of_relIndex_eq_two
import Submission.Work.CORE4.mem_of_isFourGroup_le_of_relIndex_eq_two
import Submission.Work.CORE4.eq_of_le_of_normalizer_eq_of_isNilpotent

open scoped MatrixGroups

namespace Work.CORE4

open Work.GW2 Subgroup

set_option linter.style.haveILetI false

/-! ## helpers -/

variable {G : Type} [Group G] [Finite G]

/-- A four-group containing `t` has an element other than `1` and `t`. -/
theorem exists_mem_isFourGroup_ne_one_ne {W : Subgroup G} {t : G} (h4 : Work.GW2.IsFourGroup W)
    (htW : t ∈ W) : ∃ σ ∈ W, σ ≠ 1 ∧ σ ≠ t := by
  by_contra h
  push Not at h
  have hsub : (W : Set G) ⊆ ({1, t} : Set G) := by
    intro x hx
    by_cases h1 : x = 1
    · simp [h1]
    · simp [h x hx h1]
  have hcard : (W : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact h4.1
  have hle : (W : Set G).ncard ≤ ({1, t} : Set G).ncard := Set.ncard_le_ncard hsub
  have h2 : ({1, t} : Set G).ncard ≤ 2 := by
    rcases eq_or_ne (1 : G) t with h | h
    · rw [h]; simp
    · rw [Set.ncard_pair h]
  omega

/-- A subgroup of odd order of `H` lies in `U` when `U ⊴ H` and `U` has `2`-power index in `H`. -/
theorem le_of_odd_order_of_relIndex_eq_pow_two {H U Z : Subgroup G} (hUH : U ≤ H)
    (hNU : (U.subgroupOf H).Normal) {n : ℕ} (hidx : U.relIndex H = 2 ^ n) (hZ : Z ≤ H)
    (hZodd : Odd (Nat.card Z)) : Z ≤ U := by
  haveI := hNU
  have hcard : Nat.card (↥H ⧸ (U.subgroupOf H)) = 2 ^ n := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  intro z hz
  set q := QuotientGroup.mk' (U.subgroupOf H) with hq
  have h1 : orderOf (q ⟨z, hZ hz⟩) ∣ 2 ^ n := by
    rw [← hcard]
    simpa using Subgroup.orderOf_dvd_natCard ⊤ (Subgroup.mem_top (q ⟨z, hZ hz⟩))
  have h2 : orderOf (q ⟨z, hZ hz⟩) ∣ orderOf (⟨z, hZ hz⟩ : ↥H) := orderOf_map_dvd q _
  have h3 : orderOf (q ⟨z, hZ hz⟩) ∣ Nat.card Z := by
    refine h2.trans ?_
    rw [Subgroup.orderOf_mk]
    exact Subgroup.orderOf_dvd_natCard Z hz
  have h4 : orderOf (q ⟨z, hZ hz⟩) ∣ (2 ^ n).gcd (Nat.card Z) := Nat.dvd_gcd h1 h3
  have hcop : Nat.Coprime (2 ^ n) (Nat.card Z) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hZodd)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h4
  have hzU : (⟨z, hZ hz⟩ : ↥H) ∈ U.subgroupOf H := by
    rw [← QuotientGroup.eq_one_iff]
    simpa [hq] using h4
  exact Subgroup.mem_subgroupOf.mp hzU

/-- `F(U)` is normal in `U`. -/
theorem fittingIn_conj_mem {U : Subgroup G} {x y : G} (hx : x ∈ U)
    (hy : y ∈ Work.GW2.fittingIn U) : x * y * x⁻¹ ∈ Work.GW2.fittingIn U := by
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
  have hnorm : (Work.GW2.fitting ↥U).Normal := Subgroup.normalCore_normal _
  have hzy' : (z : G) = y := hzy
  refine ⟨(⟨x, hx⟩ : ↥U) * z * (⟨x, hx⟩ : ↥U)⁻¹, hnorm.conj_mem z hz ⟨x, hx⟩, ?_⟩
  have hw : U.subtype ((⟨x, hx⟩ : ↥U) * z * (⟨x, hx⟩ : ↥U)⁻¹) = x * (z : G) * x⁻¹ := by
    simp [map_mul, map_inv]
  rw [hw, hzy']

/-- Inverting a conjugation relation. -/
theorem inv_mul_eq_mul_inv_of_mul_eq_mul {x σ : G} (h : x * σ = σ * x) (hσ : σ ^ 2 = 1) :
    x⁻¹ * σ = σ * x⁻¹ := by
  have hσσ : σ * σ = 1 := by rw [← pow_two]; exact hσ
  have hσinv : σ⁻¹ = σ := by
    have h1 : σ⁻¹ * σ = σ * σ := by rw [inv_mul_cancel, hσσ]
    exact mul_right_cancel h1
  have h2 : σ⁻¹ * x⁻¹ = x⁻¹ * σ⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev]
    exact congrArg Inv.inv h
  rw [hσinv] at h2
  exact h2.symm

/-! ## The main leaf -/

/-- Design-27 leaf `Work.GW2.C27.FourCentProp I` (see `Submission/Work/_design_gw/Core27.lean:94`
and `CORE4/Defs27.lean`).

In words (Bender p. 227: "`|Q| = 4` would imply `C_G(Q) ⊆ M` because `C_G(⟨t,s⟩) = ⟨t,s⟩B ⊆ M` and
`s` now is an arbitrary element of `S − S₀`"): for `BenderCtx G`, `B : BenderSetup G`,
`h : Case2Ctx B`, `Case2 B`, `Case2PrePlus B h.D`, `Case2SevenFacts B h.D`, and `V ≤ E(M)` a
four-group, every subgroup `Y` of odd order centralizing `V` lies in `M`:
`Odd |Y| → Y ≤ C_G(V) → Y ≤ h.D.M`.

Route (as in the design docstring): `V^e ≤ S` for some `e ∈ E` (`S ≤ E` by `nine`; Sylow); a
four-group of the dihedral `S` contains `t` (`|S| = 4`: `V^e = S`; `|S| ≥ 8`: `t` generates
`Z(S)`), so `V^e = ⟨t, s'⟩` with `s' ∈ S ∖ S₀`, i.e. `s' = s z`, `z ∈ S₀`.  Then
`Y^e ≤ C(t) = H = U S` (`I.toolkit.split`) has odd order, so `Y^e ≤ C_U(s')`; and `C_U(s') ≤ M`:
`z` centralizes `U` (`Work.CORE4.Case2S0_comm_U`), so `s'` inverts `K` like `s`, hence
`C_{F(U)}(s') ⊓ M = C_{K₀F}(s') = F` (`SixThree`), and `F' := C_{F(U)}(s') ≥ F` is nilpotent with
`N_{F'}(F) ≤ N_G(F) ⊓ F' = F` (`normalizer F = M`), so `F' = F` and `C_U(s') ≤ N_G(F') = M`.
Finally `Y ≤ M^{e⁻¹} = M`.

Must be sorry-free: `#print axioms Work.CORE4.FourCent` = `[propext, Classical.choice, Quot.sound]`. -/
theorem FourCent (I : Work.GW2.C4Inputs) : Work.GW2.C27.FourCentProp I := by
  intro G _instG _finG hbc B h h2 hplus h7 V hVE hV4 Y hYodd hYC
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSE : (B.S : Subgroup G) ≤ Work.GW2.layerIn h.D.M := S_le_layerIn h
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (G := ↥V) (n := 2) (by rw [hV4.1]; norm_num)
  obtain ⟨e, heE, heV⟩ :=
    exists_conj_le_of_le_sylow (E := Work.GW2.layerIn h.D.M) B.S hSE hVE hV2
  have heM : e ∈ h.D.M := Work.CORE4.layerIn_le h.D.M heE
  -- `W = V^e` is a four-group inside `S`, containing `t`
  have hW4 : Work.GW2.IsFourGroup (Work.GW2.conjSub e V) :=
    isFourGroup_map_mulEquiv (MulAut.conj e) hV4
  have hWS : Work.GW2.conjSub e V ≤ (B.S : Subgroup G) := heV
  have htW : B.t ∈ Work.GW2.conjSub e V :=
    mem_of_isFourGroup_le_of_relIndex_eq_two B.S0_le B.S0_index B.S0_cyclic B.t_mem B.t_order
      hWS hW4
  -- `Y^e`
  have hY'odd : Odd (Nat.card (Work.GW2.conjSub e Y)) := by
    rw [card_conjSub]; exact hYodd
  have hY'C : Work.GW2.conjSub e Y ≤ centralizer (Work.GW2.conjSub e V : Set G) :=
    conjSub_le_centralizer e hYC
  have hY'H : Work.GW2.conjSub e Y ≤ B.H :=
    hY'C.trans (Subgroup.centralizer_le (by rw [Set.singleton_subset_iff]; exact htW))
  -- `Y^e ≤ U`
  have hY'U : Work.GW2.conjSub e Y ≤ B.U := by
    obtain ⟨n, hn⟩ := B.S.isPGroup'.exists_card_eq
    exact le_of_odd_order_of_relIndex_eq_pow_two B.U_le_H B.U_normal
      (by rw [Work.GW2.Case2Ctx.relIndex_U_H I h, hn]) hY'H hY'odd
  -- pick `σ ∈ W`, `σ ≠ 1`, `σ ≠ t`
  obtain ⟨σ, hσW, hσ1, hσt⟩ := exists_mem_isFourGroup_ne_one_ne hW4 htW
  have hσS : σ ∈ (B.S : Subgroup G) := hWS hσW
  have hσ2 : σ ^ 2 = 1 := hW4.2 σ hσW
  have hσord : orderOf σ = 2 := by
    have hdvd : orderOf σ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hσ2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h' | h'
    · exact absurd (orderOf_eq_one_iff.mp h') hσ1
    · exact h'
  have hσS0 : σ ∉ B.S0 := by
    intro hmem
    haveI : IsCyclic ↥B.S0 := B.S0_cyclic
    have h1 : (⟨σ, hmem⟩ : ↥B.S0) = ⟨B.t, B.t_mem⟩ :=
      eq_of_orderOf_eq_two_of_isCyclic
        (by rw [Subgroup.orderOf_mk]; exact hσord)
        (by rw [Subgroup.orderOf_mk]; exact B.t_order)
    exact hσt (congrArg Subtype.val h1)
  -- `s σ ∈ S₀`, so `σ = s · (s σ)` acts on `U` exactly as `s` does
  have hsS : h.D.s ∈ (B.S : Subgroup G) := h.D.s_mem_S
  have hsS0 : h.D.s ∉ B.S0 := Case2SNotMemS0 I hbc h
  have hsσ : h.D.s * σ ∈ B.S0 :=
    mul_mem_of_relIndex_eq_two B.S0_le B.S0_index hsS hσS hsS0 hσS0
  have hss : h.D.s * h.D.s = 1 := by
    have hs2 : h.D.s ^ 2 = 1 := by
      rw [← h.D.s_order]; exact pow_orderOf_eq_one h.D.s
    rw [← pow_two]; exact hs2
  have hσeq : σ = h.D.s * (h.D.s * σ) := by rw [← mul_assoc, hss, one_mul]
  have hS0centU : B.S0 ≤ Subgroup.centralizer ((B.U : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (Case2S0_comm_U I hbc h2 h hplus h7)
  have hσ_act : ∀ u ∈ B.U, σ * u * σ⁻¹ = h.D.s * u * h.D.s⁻¹ := by
    intro u hu
    have hzcent : h.D.s * σ ∈ Subgroup.centralizer ((B.U : Subgroup G) : Set G) :=
      hS0centU hsσ
    have hzc : u * (h.D.s * σ) = (h.D.s * σ) * u :=
      Subgroup.mem_centralizer_iff.mp hzcent u hu
    have hin : (h.D.s * σ) * u * (h.D.s * σ)⁻¹ = u := by rw [← hzc]; group
    have h1 : σ * u * σ⁻¹ = (h.D.s * (h.D.s * σ)) * u * (h.D.s * (h.D.s * σ))⁻¹ := by
      conv_lhs => rw [hσeq]
    rw [h1]
    calc (h.D.s * (h.D.s * σ)) * u * (h.D.s * (h.D.s * σ))⁻¹
        = h.D.s * ((h.D.s * σ) * u * (h.D.s * σ)⁻¹) * h.D.s⁻¹ := by group
      _ = h.D.s * u * h.D.s⁻¹ := by rw [hin]
  -- `F' := C_{F(U)}(σ)`
  set F' : Subgroup G := Work.GW2.fittingIn B.U ⊓ Subgroup.centralizer ({σ} : Set G) with hF'def
  have hF'le : F' ≤ Work.GW2.fittingIn B.U := inf_le_left
  have hF_le_F' : h.D.F ≤ F' := by
    refine le_inf (Case2Data.F_le_fitting B h.D) ?_
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfU : f ∈ B.U := (Case2Data.F_le_U B h.D) hf
    have hsf : h.D.s * f * h.D.s⁻¹ = f := by
      have hfB0 : f ∈ h.D.B0 := (Case2Data.F_le_B0 B h.D) hf
      rw [h.D.B0_def] at hfB0
      have hfs : f * h.D.s = h.D.s * f :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hfB0).2
      rw [← hfs]; group
    have hσf : σ * f * σ⁻¹ = f := by rw [hσ_act f hfU, hsf]
    calc f * σ = (σ * f * σ⁻¹) * σ := by rw [hσf]
      _ = σ * f := by group
  -- `F' ⊓ M = F`
  have hF_le_M : h.D.F ≤ h.D.M :=
    (Case2Data.F_le_B0 B h.D).trans ((Case2Data.B0_le B h.D).trans inf_le_right)
  have hF'infM : F' ⊓ h.D.M = h.D.F := by
    refine le_antisymm ?_ (le_inf hF_le_F' hF_le_M)
    intro x hx
    obtain ⟨hxF', hxM⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxfit, hxcen⟩ := Subgroup.mem_inf.mp hxF'
    have hxU : x ∈ B.U := Subgroup.map_subtype_le _ hxfit
    have hxB0 : x ∈ h.D.B0 := by
      rw [h.D.B0_def]
      refine Subgroup.mem_inf.mpr ⟨⟨hxU, hxM⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxσ : x * σ = σ * x := Subgroup.mem_centralizer_singleton_iff.mp hxcen
      have hσx : σ * x * σ⁻¹ = x := by rw [← hxσ]; group
      have h1 : x = h.D.s * x * h.D.s⁻¹ := hσx.symm.trans (hσ_act x hxU)
      calc x * h.D.s = (h.D.s * x * h.D.s⁻¹) * h.D.s := congrArg (· * h.D.s) h1
        _ = h.D.s * x := by group
    rw [h.D.F_def]
    exact Subgroup.mem_inf.mpr ⟨hxB0, hxfit⟩
  -- nilpotency ⇒ `F' = F`
  have hNF : F' ⊓ Subgroup.normalizer (h.D.F : Set G) = h.D.F := by
    rw [Work.GW2.Case2Pre.N_F B h.D h.pre]
    exact hF'infM
  have hF'_eq : F' = h.D.F := by
    set N : Subgroup G := Work.GW2.fittingIn B.U with hNdef
    haveI : Group.IsNilpotent ↥N := Work.CORE4.SevenX.PiFU.isNilpotent_fittingIn B.U
    have hDFleN : h.D.F ≤ N := Case2Data.F_le_fitting B h.D
    have hsub : h.D.F.subgroupOf N ≤ F'.subgroupOf N := Subgroup.subgroupOf_mono N hF_le_F'
    have hNN : F'.subgroupOf N ⊓ Subgroup.normalizer ((h.D.F.subgroupOf N) : Set ↥N)
        = h.D.F.subgroupOf N := by
      rw [← Subgroup.subgroupOf_normalizer_eq hDFleN]
      dsimp only [Subgroup.subgroupOf]
      rw [← Subgroup.comap_inf, hNF]
    have heq : h.D.F.subgroupOf N = F'.subgroupOf N :=
      eq_of_le_of_normalizer_eq_of_isNilpotent hsub hNN
    refine le_antisymm ?_ hF_le_F'
    intro x hx
    have hx' : (⟨x, hF'le hx⟩ : ↥N) ∈ F'.subgroupOf N := Subgroup.mem_subgroupOf.mpr hx
    rw [← heq] at hx'
    exact Subgroup.mem_subgroupOf.mp hx'
  -- `C_U(σ) ≤ N_G(F') = N_G(F) = M`
  have hconj : ∀ y ∈ F', ∀ x ∈ (B.U ⊓ Subgroup.centralizer ({σ} : Set G)),
      x * y * x⁻¹ ∈ F' := by
    intro y hy x hx
    obtain ⟨hxU, hxcen⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hyfit, hycen⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_inf.mpr ⟨fittingIn_conj_mem hxU hyfit, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxcen hycen ⊢
    have hxinv : x⁻¹ * σ = σ * x⁻¹ := inv_mul_eq_mul_inv_of_mul_eq_mul hxcen hσ2
    calc (x * y * x⁻¹) * σ = x * y * (x⁻¹ * σ) := by group
      _ = x * y * (σ * x⁻¹) := by rw [hxinv]
      _ = x * (y * σ) * x⁻¹ := by group
      _ = x * (σ * y) * x⁻¹ := by rw [hycen]
      _ = (x * σ) * y * x⁻¹ := by group
      _ = (σ * x) * y * x⁻¹ := by rw [hxcen]
      _ = σ * (x * y * x⁻¹) := by group
  have hCU_le_N : B.U ⊓ Subgroup.centralizer ({σ} : Set G) ≤
      Subgroup.normalizer (F' : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hconj y hy x hx
    · intro hy
      have h2 : x⁻¹ ∈ B.U ⊓ Subgroup.centralizer ({σ} : Set G) := by
        obtain ⟨hxU, hxcen⟩ := Subgroup.mem_inf.mp hx
        refine Subgroup.mem_inf.mpr ⟨B.U.inv_mem hxU, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hxcen ⊢
        exact inv_mul_eq_mul_inv_of_mul_eq_mul hxcen hσ2
      have h3 := hconj (x * y * x⁻¹) hy x⁻¹ h2
      have h4 : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
      rwa [h4] at h3
  have hCU_le_M : B.U ⊓ Subgroup.centralizer ({σ} : Set G) ≤ h.D.M := by
    refine hCU_le_N.trans ?_
    rw [hF'_eq, Work.GW2.Case2Pre.N_F B h.D h.pre]
  -- assemble
  have hY'M : Work.GW2.conjSub e Y ≤ h.D.M := by
    refine le_trans ?_ hCU_le_M
    refine le_inf hY'U ?_
    exact hY'C.trans (Subgroup.centralizer_le (by rw [Set.singleton_subset_iff]; exact hσW))
  intro y hy
  have hy' : e * y * e⁻¹ ∈ Work.GW2.conjSub e Y :=
    Subgroup.mem_map.mpr ⟨y, hy, by simp [MulAut.conj_apply]⟩
  have hmem := hY'M hy'
  have h4 : y = e⁻¹ * (e * y * e⁻¹) * e := by group
  rw [h4]
  exact h.D.M.mul_mem (h.D.M.mul_mem (h.D.M.inv_mem heM) hmem) heM

end Work.CORE4
