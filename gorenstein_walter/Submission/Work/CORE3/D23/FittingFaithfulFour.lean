import Mathlib
import Submission.Work.CORE3.D23.Core23A
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE2A.pCoreIn_conjSub

namespace Work.CORE3.D23

open Work.GW2

/-! ## Support API -/

/-- An automorphism of `V` restricts to a permutation of the nonidentity elements of `V`. -/
noncomputable def restrictPermHom {G : Type} [Group G] (V : Subgroup G) :
    MulAut V →* Equiv.Perm {v : V // v ≠ 1} where
  toFun e := Equiv.subtypeEquiv e (fun a => (MulEquiv.map_ne_one_iff e).symm)
  map_one' := by ext v; rfl
  map_mul' e f := by ext v; rfl

/-- A group of order `4` has exactly three nonidentity elements. -/
theorem card_ne_one_of_card_four {V : Type*} [Group V] [Finite V] (h : Nat.card V = 4) :
    Nat.card {v : V // v ≠ 1} = 3 := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  have h1 : Nat.card {v : V // v ≠ 1} = Fintype.card {v : V // v ≠ 1} := Nat.card_eq_fintype_card
  rw [h1, Fintype.card_subtype]
  have h2 : (Finset.univ.filter (fun x : V => x ≠ 1)) = (Finset.univ.erase (1 : V)) := by
    ext x; simp
  rw [h2, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have h3 : Fintype.card V = 4 := by rw [← Nat.card_eq_fintype_card]; exact h
  omega

/-! ## L3 -/

/-- **L3 of GW design pass 23 §A** (the correct half of Bender 1981, p. 224, (7)), in the
unfolded form of `Work.CORE3.D23.FittingFaithfulFourProp`: an odd subgroup `Y ≤ F(U)` that lies
in the conjugate `Ĥ^g`, in a configuration where `V^g ⊓ Ĥ = ⊥` (`V = O₂(Ĥ)`), has order dividing
`3`.

Route.  `Y ≤ Ĥ^g` and `V^g = O₂(Ĥ^g)`, so `Y` normalizes `V^g` (conjugate of
`Work.CORE3.NormalizerPcoreEqHhat`, `O₂(K) ⊴ K`); hence `C_Y(V^g)` is normalized by `V^g` as
well.  If `C_Y(V^g) ≠ ⊥`, then — as `C_Y(V^g) ≤ F(U)` — local control (the second conjunct of
`h1 : Case1 B`) gives `V^g ≤ Ĥ`, contradicting `V^g ⊓ Ĥ = ⊥` together with `V^g ≠ ⊥` (which is
`D.four`, `|V| = 4`, transported along `conjSub g`).  So `Y` acts faithfully on the three
involutions of `V^g`, i.e. `Y` embeds into `Equiv.Perm` of that three-element set and
`|Y| ∣ 6`; `Y` is odd because `Y ≤ F(U) ≤ U = oddCoreIn B.H` is a `2'`-group, so `|Y| ∣ 3`. -/
theorem FittingFaithfulFour (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (h : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) (g : G) (Y : Subgroup G)
    (hYF : Y ≤ Work.GW2.fittingIn B.U) (hYH : Y ≤ Work.GW2.conjSub g B.Hhat)
    (hV : Work.GW2.conjSub g (Work.GW2.pCoreIn 2 B.Hhat) ⊓ B.Hhat = ⊥) :
    Nat.card Y ∣ 3 := by
  classical
  set V0 : Subgroup G := Work.GW2.pCoreIn 2 B.Hhat with hV0def
  set Vg : Subgroup G := Work.GW2.conjSub g V0 with hVgdef
  -- `V0 = O₂(Ĥ)` is a four-group; so is its conjugate `Vg = O₂(Ĥ)^g`.
  have hV0four : Nat.card V0 = 4 := by rw [hV0def]; exact D.four.1
  have hV0sq : ∀ v ∈ V0, v ^ 2 = 1 := by
    intro v hv
    exact D.four.2 v (by rw [hV0def] at hv; exact hv)
  have hVgcard : Nat.card Vg = 4 := by
    rw [hVgdef, Work.CORE2A.card_conjSub]; exact hV0four
  have hVint : Vg ⊓ B.Hhat = ⊥ := by rw [hVgdef, hV0def]; exact hV
  have hVg4 : IsFourGroup Vg := by
    refine ⟨hVgcard, ?_⟩
    intro v hv
    have hv' : g⁻¹ * v * g ∈ V0 := by
      rw [hVgdef] at hv
      exact Work.CORE2A.mem_conjSub_iff.mp hv
    have h4 : (g⁻¹ * v * g) ^ 2 = 1 := hV0sq _ hv'
    have h5 : g⁻¹ * v ^ 2 * g = 1 := by
      have h6 : (g⁻¹ * v * g) ^ 2 = g⁻¹ * v ^ 2 * g := by rw [pow_two, pow_two]; group
      rw [← h6]; exact h4
    calc v ^ 2 = g * (g⁻¹ * v ^ 2 * g) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [h5]
      _ = 1 := by group
  -- `V0 ⊴ Ĥ`, so `Vg ⊴ Ĥ^g` and a fortiori `Y ≤ Ĥ^g` normalizes `Vg`.
  have hYV : Y ≤ Subgroup.normalizer ((Vg : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy v hv
    have hyH : y ∈ Work.GW2.conjSub g B.Hhat := hYH hy
    rw [Work.CORE2A.conjSub_eq_map, Subgroup.mem_map] at hyH
    obtain ⟨a, ha, hay⟩ := hyH
    have hay' : y = g * a * g⁻¹ := by
      rw [← hay]
      exact MulAut.conj_apply g a
    have hvV : v ∈ Work.GW2.conjSub g V0 := by rw [← hVgdef]; exact hv
    rw [Work.CORE2A.conjSub_eq_map, Subgroup.mem_map] at hvV
    obtain ⟨b, hb, hbv⟩ := hvV
    have hbv' : v = g * b * g⁻¹ := by
      rw [← hbv]
      exact MulAut.conj_apply g b
    have hbV : b ∈ Work.GW2.pCoreIn 2 B.Hhat := by rw [← hV0def]; exact hb
    have hab : a * b * a⁻¹ ∈ V0 := by
      rw [hV0def]
      exact (Subgroup.mem_normalizer_iff.mp (Work.CORE2A.le_normalizer_pCoreIn B.Hhat 2 ha) b).mp
        hbV
    rw [hay', hbv', hVgdef, Work.CORE2A.conjSub_eq_map, Subgroup.mem_map]
    refine ⟨a * b * a⁻¹, hab, ?_⟩
    show (MulAut.conj g) (a * b * a⁻¹) = (g * a * g⁻¹) * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹
    rw [MulAut.conj_apply]
    group
  -- If `C_Y(Vg) ≠ 1` then `Vg ≤ N_G(C_Y(Vg)) ≤ Ĥ` by local control, contradicting `Vg ⊓ Ĥ = ⊥`.
  have hCbot : Y ⊓ Subgroup.centralizer ((Vg : Subgroup G) : Set G) = ⊥ := by
    by_contra hne
    set K : Subgroup G := Y ⊓ Subgroup.centralizer ((Vg : Subgroup G) : Set G) with hKdef
    have hKle : K ≤ Work.GW2.fittingIn B.U := le_trans inf_le_left hYF
    have hNle : Subgroup.normalizer (K : Set G) ≤ B.Hhat := h1.2 K hne hKle
    have hVgle : Vg ≤ Subgroup.normalizer (K : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro v hv k hk
      have hcomm : v * k = k * v := (Subgroup.mem_centralizer_iff.mp hk.2) v hv
      have hkv : v * k * v⁻¹ = k := by rw [hcomm]; group
      rw [hkv]; exact hk
    have hVgH : Vg ≤ B.Hhat := le_trans hVgle hNle
    have hbot : Vg ≤ ⊥ := by rw [← hVint]; exact le_inf le_rfl hVgH
    have hcard1 : Nat.card Vg = 1 := by rw [le_bot_iff.mp hbot]; exact Subgroup.card_bot
    omega
  -- `Y` acts faithfully on the three nonidentity elements of `Vg`.
  let psi : Y →* Equiv.Perm {v : Vg // v ≠ 1} :=
    (restrictPermHom Vg).comp ((Subgroup.normalizerMonoidHom Vg).comp (Subgroup.inclusion hYV))
  have hker : MonoidHom.ker psi = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hcent : (y : G) ∈ Subgroup.centralizer ((Vg : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      by_cases hv1 : (⟨v, hv⟩ : Vg) = 1
      · have hv' : v = 1 := Subtype.ext_iff.mp hv1
        rw [hv']; simp
      · have hc : psi y ⟨⟨v, hv⟩, hv1⟩ = ⟨⟨v, hv⟩, hv1⟩ := by rw [hy]; rfl
        have hval : ((psi y ⟨⟨v, hv⟩, hv1⟩ : {w : Vg // w ≠ 1}) : Vg) = ⟨v, hv⟩ :=
          congrArg Subtype.val hc
        have hgen : (y : G) * v * (y : G)⁻¹ = v := by
          have h2 := congrArg (fun (u : Vg) => (u : G)) hval
          exact h2
        have h3 : (y : G) * v = v * (y : G) := by
          calc (y : G) * v = ((y : G) * v * (y : G)⁻¹) * (y : G) := by group
            _ = v * (y : G) := by rw [hgen]
        exact h3.symm
    have hyc : (y : G) ∈ Y ⊓ Subgroup.centralizer ((Vg : Subgroup G) : Set G) := ⟨y.2, hcent⟩
    rw [hCbot] at hyc
    exact Subgroup.mem_bot.mp hyc
  have hdiv : Nat.card Y ∣ Nat.card (Equiv.Perm {v : Vg // v ≠ 1}) := by
    have hinj : Function.Injective psi := (MonoidHom.ker_eq_bot_iff psi).mp hker
    rw [Nat.card_congr (MonoidHom.ofInjective (f := psi) hinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card (MonoidHom.range psi)
  have hperm6 : Nat.card (Equiv.Perm {v : Vg // v ≠ 1}) = 6 := by
    rw [Nat.card_perm, card_ne_one_of_card_four hVgcard]
    norm_num
  rw [hperm6] at hdiv
  -- `Y ≤ F(U) ≤ U` is a `2'`-group.
  have hYodd : Odd (Nat.card Y) := by
    refine Odd.of_dvd_nat (Work.CORE2A.bSetup_U_odd B) ?_
    have hle : Y ≤ B.U := le_trans hYF (Subgroup.map_subtype_le _)
    have hdvd := Subgroup.card_subgroup_dvd_card (Y.subgroupOf B.U)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hdvd
  -- `|Y| ∣ 6` and `|Y|` odd force `|Y| ∣ 3`.
  have hmem : Nat.card Y ∈ Nat.divisors 6 := Nat.mem_divisors.mpr ⟨hdiv, by norm_num⟩
  rw [show Nat.divisors 6 = {1, 2, 3, 6} from by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hh | hh | hh | hh
  · rw [hh]; norm_num
  · rw [hh] at hYodd; obtain ⟨k, hk⟩ := hYodd; omega
  · exact hh ▸ dvd_rfl
  · rw [hh] at hYodd; obtain ⟨k, hk⟩ := hYodd; omega

end Work.CORE3.D23
