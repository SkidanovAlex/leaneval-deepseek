import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.L27_su_not_le_h22_proved
import Submission.Work.CORE2B.L27_fourGroup_in_C_M_t
import Submission.Work.BMAX.InvolutionInverts

namespace Work.CORE2B

open Subgroup
open scoped commutatorElement
open scoped Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## Elementary helper lemmas -/

/-- `n` is odd as soon as `2 ∤ n`. -/
theorem odd_of_not_two_dvd {n : ℕ} (h : ¬ 2 ∣ n) : Odd n :=
  Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using h)

/-- **An odd subgroup inverted by an element of `S` lies in `[S,U]`.**

If `s ∈ S` inverts an odd-order subgroup `X ≤ U`, then `x ↦ x²` is a bijection on `X` (odd
order), and `x² = ⁅x,s⁆ ∈ ⁅X, ⟨s⟩⁆ ≤ ⁅U,S⁆`.  Hence `X ≤ ⁅S,U⁆`. -/
theorem L27su_le_commutator_of_inverts {G : Type} [Group G] [Finite G] {S U X : Subgroup G}
    {s : G} (hs : s ∈ S) (hX : X ≤ U) (hodd : Odd (Nat.card X))
    (hinv : ∀ x ∈ X, s * x * s⁻¹ = x⁻¹) : X ≤ ⁅S, U⁆ := by
  intro x hx
  obtain ⟨k, hk⟩ := hodd
  have hcard : Nat.card X = 2 * k + 1 := hk
  have hstep : x ^ Nat.card X = 1 := by
    have h := Subgroup.orderOf_dvd_natCard X hx
    rwa [orderOf_dvd_iff_pow_eq_one] at h
  have hpow : (x ^ (k + 1)) ^ 2 = x := by
    calc (x ^ (k + 1)) ^ 2 = x ^ ((k + 1) * 2) := by rw [pow_mul]
      _ = x ^ (Nat.card X + 1) := by rw [hcard]; ring_nf
      _ = x ^ Nat.card X * x := pow_succ x (Nat.card X)
      _ = x := by rw [hstep, one_mul]
  have hxinv : ⁅s, x ^ (k + 1)⁆ = x⁻¹ := by
    rw [commutatorElement_def]
    have hyinv : s * x ^ (k + 1) * s⁻¹ = (x ^ (k + 1))⁻¹ :=
      hinv _ (Subgroup.pow_mem X hx (k + 1))
    rw [hyinv]
    calc (x ^ (k + 1))⁻¹ * (x ^ (k + 1))⁻¹
        = ((x ^ (k + 1)) * (x ^ (k + 1)))⁻¹ := (mul_inv_rev _ _).symm
      _ = x⁻¹ := by rw [← pow_two, hpow]
  have hmem : x⁻¹ ∈ ⁅S, U⁆ := by
    rw [← hxinv, Subgroup.commutator_def]
    exact Subgroup.subset_closure ⟨s, hs, x ^ (k + 1),
      hX (Subgroup.pow_mem X hx (k + 1)), rfl⟩
  simpa using (⁅S, U⁆).inv_mem hmem

/-- **Sylow conjugacy inside a subgroup.**  If `P` is a Sylow 2-subgroup of `G` contained in
`H` and `a ∈ H` is an involution, then some `H`-conjugate of `a` lies in `P` (so `P` is also a
Sylow 2-subgroup of `H`). -/
theorem L27su_sylow_conj {G : Type} [Group G] [Finite G] (H : Subgroup G) (P : Sylow 2 G)
    (hPH : (P : Subgroup G) ≤ H) {a : G} (haH : a ∈ H) (ha2 : a * a = 1) :
    ∃ h ∈ H, h * a * h⁻¹ ∈ (P : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥H := Subtype.finite
  let aH : ↥H := ⟨a, haH⟩
  let A : Subgroup ↥H := Subgroup.zpowers aH
  have hA : IsPGroup 2 A := by
    have hdvd : Nat.card A ∣ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_iff_pow_eq_one.mpr (by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        simpa [pow_two] using ha2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [h]; norm_num)
    · exact IsPGroup.of_card (n := 1) (by rw [h]; norm_num)
  obtain ⟨R, hAR⟩ := hA.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (M := ↥H) R (P.subtype hPH)
  have hy' : (MulAut.conj y) • (R : Subgroup ↥H)
      = ((P.subtype hPH : Sylow 2 ↥H) : Subgroup ↥H) :=
    congrArg (fun Q : Sylow 2 ↥H => (Q : Subgroup ↥H)) hy
  have hmem : (MulAut.conj y) aH ∈ ((P.subtype hPH : Sylow 2 ↥H) : Subgroup ↥H) := by
    rw [← hy', Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨aH, hAR (Subgroup.mem_zpowers aH), rfl⟩
  have hmem' : (MulAut.conj y) aH ∈ (P.subgroupOf H) := by
    rw [Sylow.coe_subtype] at hmem
    exact hmem
  refine ⟨(y : G), y.2, ?_⟩
  have hcoe : (((MulAut.conj y) aH : ↥H) : G) = (y : G) * a * (y : G)⁻¹ := by
    rw [MulAut.conj_apply]
    rfl
  rw [← hcoe]
  exact Subgroup.mem_subgroupOf.mp hmem'

/-! ## Bender's transport step -/

/-- **Bender's transport step (the heart of Lemma 2.7 (b)).**  Let `Y ≤ M` be a nontrivial normal
subgroup of `M` that is a `π'`-group, meets `Ĥ` trivially, and is inverted by `t` (the canonical
case being `Y = F_{π'}(M)`: `h23(ii)` gives `Y ⊓ Ĥ = ⊥`, `Y` is characteristic in `M`,
`inverts_fittingPiIn_pi_compl_local` gives the inversion, and `Y` is a `π'`-group); let `v ∈ M` be
an involution commuting with `t`, `v ≠ t` (so that `V := ⟨t, v⟩` is a Klein four-group inside
`C_M(t)`).  Then the commutator subgroup `[S,U]` contains a nontrivial `π'`-subgroup of `U`.

Route (Bender's argument, `NOTES_LEAD_gw_design3.md` §7a):
* `Y ◁ M` and `V ≤ M` give `V ≤ N_G(Y)`, and `Y` is odd because `2 ∈ B.pi` (`two_mem_pi_local`,
  from `h26`) while all primes of `|Y|` lie outside `B.pi`.  `T.c11iii` (1.1(iii)) applied to the
  four-group `V` acting on `Y` gives `Y = ⨆_{w ∈ V#} (Y ⊓ C_G(w))`; since
  `Y ⊓ C_G(t) ≤ Y ⊓ Ĥ = ⊥` and `Y ≠ ⊥`, some `w ∈ V`, `w ≠ 1`, `w ≠ t` has `Y₀ := Y ⊓ C_G(w) ≠ ⊥`.
* `T.fus` (fusion of involutions: `N_G(V)` is transitive on `V#`) gives `h ∈ N_G(V)` with
  `h * t * h⁻¹ = w`.  Then `X := Y₀` conjugated by `h⁻¹` is centralized by `t` (since
  `w^{h⁻¹} = t`), hence `X ≤ C_G(t) = H`, and `X` is odd, so `X ≤ U = O(H)`; it is inverted by
  `t^{h⁻¹} ∈ V ≤ C_G(t) = H ⊆ N_G(U)`.
* `S` is a Sylow 2-subgroup of `N_G(U)` (`S ≤ H ≤ N_G(U)` and maximality in `G`); conjugating by
  an element of `N_G(U)` puts the inverting involution into `S`.  An involution `s ∈ S` inverting
  the odd group `X` satisfies `[s, X] = X`, whence `X ≤ [S,U]`.  `X ≠ ⊥` and its order is `π'`. -/
theorem L27su_transport :
    ∀ (T : Work.GW2.LocalToolkit) (h23 : Work.GW2.Lemma23Prop) (h26 : Work.GW2.Thm26Prop)
      (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), Work.CORE2B.L27Hyp B M →
      (∃ v ∈ M, orderOf v = 2 ∧ v ≠ B.t ∧ v * B.t = B.t * v) →
      ∀ Y : Subgroup G, Y ≤ M → (Y.subgroupOf M).Normal → Y ≠ ⊥ → Y ⊓ B.Hhat = ⊥ →
        Work.GW2.Inverts B.t Y →
        (∀ p : ℕ, p.Prime → p ∣ Nat.card Y → p ∉ B.pi) →
        ∃ X : Subgroup G, X ≠ ⊥ ∧ X ≤ B.U ∧
          (∀ p : ℕ, p.Prime → p ∣ Nat.card X → p ∉ B.pi) ∧
          X ≤ ⁅(B.S : Subgroup G), B.U⁆ := by
  intro T h23 h26 G _ _ hFT hCtx B M hL hvBex Y hYM hYnorm hYne hYdisj hYinv hYpi'
  obtain ⟨v, hvM, hv2, hvt, hvtc⟩ := hvBex
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `t` and `v` are nontrivial involutions
  have ht2 : B.t ^ 2 = 1 := by
    rw [← B.t_order]; exact pow_orderOf_eq_one B.t
  have ht1 : B.t ≠ 1 := by
    intro h
    have : orderOf B.t = 1 := by rw [h, orderOf_one]
    rw [B.t_order] at this
    exact absurd this (by norm_num)
  have hv2' : v ^ 2 = 1 := by
    rw [← hv2]; exact pow_orderOf_eq_one v
  have hv1 : v ≠ 1 := by
    intro h
    have : orderOf v = 1 := by rw [h, orderOf_one]
    rw [hv2] at this
    exact absurd this (by norm_num)
  -- the four-group `V = ⟨t, v⟩`
  set V : Subgroup G := Subgroup.closure ({B.t, v} : Set G) with hVdef
  have hF : Work.GW2.IsFourGroup V ∧ B.t ∈ V ∧ V ≤ Subgroup.centralizer ({B.t} : Set G) := by
    have h := fourGroup_closure_pair (t := B.t) (v := v) ht2 hv2' ht1 hv1 hvt hvtc
    rwa [← hVdef] at h
  obtain ⟨hVfour, htV, hVleCt⟩ := hF
  have hVsq : ∀ x ∈ V, x ^ 2 = 1 := hVfour.2
  have hVcard : Nat.card V = 4 := hVfour.1
  have hVP : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hVcard]; norm_num)
  have hVcomm : IsMulCommutative V := by
    refine IsMulCommutative.of_comm fun a b => ?_
    apply Subtype.ext
    show (a : G) * (b : G) = (b : G) * (a : G)
    have ha2 : (a : G) * (a : G) = 1 := by
      have h := hVsq (a : G) a.2; simpa [pow_two] using h
    have hb2 : (b : G) * (b : G) = 1 := by
      have h := hVsq (b : G) b.2; simpa [pow_two] using h
    have hab2 : ((a : G) * (b : G)) * ((a : G) * (b : G)) = 1 := by
      have h := hVsq ((a : G) * (b : G)) (V.mul_mem a.2 b.2); simpa [pow_two] using h
    calc (a : G) * (b : G) = ((a : G) * (b : G))⁻¹ := (inv_eq_of_mul_eq_one_right hab2).symm
      _ = (b : G)⁻¹ * (a : G)⁻¹ := mul_inv_rev _ _
      _ = (b : G) * (a : G) := by
          rw [inv_eq_of_mul_eq_one_right hb2, inv_eq_of_mul_eq_one_right ha2]
  -- `V ≤ M` and `V ≤ N_G(Y)`
  have hVM : V ≤ M := by
    rw [hVdef, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hL.t_mem
    · exact hvM
  have hYnormM : ∀ h k : G, h ∈ Y → k ∈ M → k * h * k⁻¹ ∈ Y :=
    (Subgroup.normal_subgroupOf_iff hYM).mp hYnorm
  have hVnormY : V ≤ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hxV z hzY
    exact hYnormM z x hzY (hVM hxV)
  -- `Y` is odd and coprime to `2`
  have h2pi : 2 ∈ B.pi := two_mem_pi_local h26 hFT hCtx B
  have h2ndvd : ¬ 2 ∣ Nat.card Y := fun h => hYpi' 2 Nat.prime_two h h2pi
  have hYodd : Odd (Nat.card Y) := odd_of_not_two_dvd h2ndvd
  have hYcop : Nat.Coprime 2 (Nat.card Y) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2ndvd
  -- `Y ⊓ C(t) = ⊥`
  have hHle : Subgroup.centralizer ({B.t} : Set G) ≤ B.Hhat := B.H_le_Hhat
  have hYct : Y ⊓ Subgroup.centralizer ({B.t} : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_left Y hHle).trans (le_of_eq hYdisj))
  -- 1.1(iii): `Y = ⨆_{w ∈ V#} (Y ⊓ C(w))`
  set F : G → Subgroup G := fun a => Y ⊓ Subgroup.centralizer ({a} : Set G) with hFdef
  have hdec : Y = ⨆ (a : G) (_ : a ∈ V) (_ : a ≠ 1), F a :=
    T.c11iii G 2 V Y V hVP hYcop hVnormY le_rfl (by rw [hVcard]; norm_num) hVsq hVcomm
  -- split off the `t`-term
  have hsplit : (⨆ (a : G) (_ : a ∈ V) (_ : a ≠ 1), F a) ≤
      F B.t ⊔ (⨆ (a : G) (_ : a ∈ V) (_ : a ≠ 1) (_ : a ≠ B.t), F a) := by
    refine iSup_le fun a => iSup_le fun haV => iSup_le fun ha1 => ?_
    by_cases hat : a = B.t
    · subst hat
      exact le_sup_of_le_left le_rfl
    · exact le_sup_of_le_right
        (le_iSup_of_le a (le_iSup_of_le haV (le_iSup_of_le ha1 (le_iSup_of_le hat le_rfl))))
  have hFt : F B.t = ⊥ := hYct
  have hYle' : Y ≤ (⨆ (a : G) (_ : a ∈ V) (_ : a ≠ 1) (_ : a ≠ B.t), F a) := by
    have h1 : Y ≤ F B.t ⊔ _ := hdec.le.trans hsplit
    rwa [hFt, bot_sup_eq] at h1
  have hY'ne : (⨆ (a : G) (_ : a ∈ V) (_ : a ≠ 1) (_ : a ≠ B.t), F a) ≠ ⊥ := by
    intro hbot
    exact hYne (le_bot_iff.mp (hYle'.trans (le_of_eq hbot)))
  have hex : ∃ a : G, ∃ (_ : a ∈ V), ∃ (_ : a ≠ 1), ∃ (_ : a ≠ B.t), F a ≠ ⊥ := by
    by_contra h
    apply hY'ne
    refine iSup_eq_bot.mpr fun a => iSup_eq_bot.mpr fun ha => iSup_eq_bot.mpr fun ha1 =>
      iSup_eq_bot.mpr fun hat => ?_
    by_contra hne
    exact h ⟨a, ha, ha1, hat, hne⟩
  obtain ⟨a, haV, ha1, hat, haY0⟩ := hex
  -- fusion: `a = g t g⁻¹` with `g ∈ N_G(V)`
  obtain ⟨n, hn2, hdih⟩ := L27su_S_dihedral hCtx B
  have hno2 : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := no_index_two_normal hCtx
  obtain ⟨g, hgN, hgt⟩ := (T.fus G B.S n hn2 hdih hno2).2 V hVfour B.t htV a haV ht1 ha1
  -- conjugate by `h = g⁻¹`: `X := α_h(Y ⊓ C(a))`, inverted by `c := h t h⁻¹`
  set h : G := g⁻¹ with hhdef
  have hhN : h ∈ Subgroup.normalizer (V : Set G) := by
    rw [hhdef]; exact Subgroup.inv_mem _ hgN
  have hhcV : h * B.t * h⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hhN B.t).mp htV
  have hkey : h⁻¹ * B.t * h = a := by
    rw [hhdef]
    simpa using hgt
  set X : Subgroup G := (F a).map (MulAut.conj h).toMonoidHom with hXdef
  have hci : ∀ y : G, (MulAut.conj h).toMonoidHom y = h * y * h⁻¹ :=
    fun y => MulAut.conj_apply h y
  have hXne : X ≠ ⊥ := by
    intro hbot
    exact haY0 ((Subgroup.map_eq_bot_iff_of_injective (F a) (MulAut.conj h).injective).mp
      (by rwa [hXdef] at hbot))
  have hXcard : Nat.card X = Nat.card (F a) := by
    rw [hXdef]
    exact Subgroup.card_map_of_injective (MulAut.conj h).injective
  have hFacard_dvd : Nat.card (F a) ∣ Nat.card Y := Subgroup.card_dvd_of_le inf_le_left
  have hXcard_dvd : Nat.card X ∣ Nat.card Y := by rw [hXcard]; exact hFacard_dvd
  have hXodd : Odd (Nat.card X) := odd_of_not_two_dvd fun hd => h2ndvd (hd.trans hXcard_dvd)
  -- `X ≤ C(t) = H`
  have hXH : X ≤ B.H := by
    intro x hx
    rw [hXdef, Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyC : a * y = y * a := (Subgroup.mem_centralizer_iff.mp hy.2) a rfl
    show (MulAut.conj h).toMonoidHom y ∈ Subgroup.centralizer ({B.t} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rw [hci]
    have key : B.t * (h * y * h⁻¹) * B.t⁻¹ = h * y * h⁻¹ := by
      calc B.t * (h * y * h⁻¹) * B.t⁻¹
          = h * ((h⁻¹ * B.t * h) * y * (h⁻¹ * B.t * h)⁻¹) * h⁻¹ := by group
        _ = h * (a * y * a⁻¹) * h⁻¹ := by rw [hkey]
        _ = h * y * h⁻¹ := by rw [hyC]; group
    calc B.t * (h * y * h⁻¹) = (B.t * (h * y * h⁻¹) * B.t⁻¹) * B.t := by group
      _ = (h * y * h⁻¹) * B.t := by rw [key]
  -- `c := h t h⁻¹` is an involution of `H` inverting `X`
  have hcH : h * B.t * h⁻¹ ∈ B.H := hVleCt hhcV
  have hc2 : (h * B.t * h⁻¹) * (h * B.t * h⁻¹) = 1 := by
    have h := hVsq (h * B.t * h⁻¹) hhcV
    simpa [pow_two] using h
  have hcinvX : ∀ x ∈ X, (h * B.t * h⁻¹) * x * (h * B.t * h⁻¹)⁻¹ = x⁻¹ := by
    intro x hx
    rw [hXdef, Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyinv : B.t * y * B.t⁻¹ = y⁻¹ := hYinv y hy.1
    rw [hci]
    calc (h * B.t * h⁻¹) * (h * y * h⁻¹) * (h * B.t * h⁻¹)⁻¹
        = h * (B.t * y * B.t⁻¹) * h⁻¹ := by group
      _ = h * y⁻¹ * h⁻¹ := by rw [hyinv]
      _ = (h * y * h⁻¹)⁻¹ := by group
  -- `X ≤ U`
  have hXU : X ≤ B.U := L27su_odd_subgroup_le_U T hCtx B X hXH hXodd
  -- move the inverting involution into `S` by conjugating inside `H`
  obtain ⟨h', hh'H, hh'c⟩ := L27su_sylow_conj B.H B.S (L27su_S_le_H B) hcH hc2
  set X' : Subgroup G := X.map (MulAut.conj h').toMonoidHom with hX'def
  have hci' : ∀ y : G, (MulAut.conj h').toMonoidHom y = h' * y * h'⁻¹ :=
    fun y => MulAut.conj_apply h' y
  have hX'ne : X' ≠ ⊥ := by
    intro hbot
    exact hXne ((Subgroup.map_eq_bot_iff_of_injective X (MulAut.conj h').injective).mp
      (by rwa [hX'def] at hbot))
  have hX'card : Nat.card X' = Nat.card X := by
    rw [hX'def]
    exact Subgroup.card_map_of_injective (MulAut.conj h').injective
  have hX'U : X' ≤ B.U := by
    intro x hx
    rw [hX'def, Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hci']
    exact (Subgroup.mem_normalizer_iff.mp (L27su_H_le_normalizer_U B hh'H) y).mp (hXU hy)
  have hX'odd : Odd (Nat.card X') := by rw [hX'card]; exact hXodd
  have hX'pi' : ∀ p : ℕ, p.Prime → p ∣ Nat.card X' → p ∉ B.pi := by
    intro p hp hd
    rw [hX'card, hXcard] at hd
    exact hYpi' p hp (hd.trans hFacard_dvd)
  have hinvX' : ∀ x ∈ X',
      (h' * (h * B.t * h⁻¹) * h'⁻¹) * x * (h' * (h * B.t * h⁻¹) * h'⁻¹)⁻¹ = x⁻¹ := by
    intro x hx
    rw [hX'def, Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyinv := hcinvX y hy
    rw [hci']
    calc (h' * (h * B.t * h⁻¹) * h'⁻¹) * (h' * y * h'⁻¹) * (h' * (h * B.t * h⁻¹) * h'⁻¹)⁻¹
        = h' * ((h * B.t * h⁻¹) * y * (h * B.t * h⁻¹)⁻¹) * h'⁻¹ := by group
      _ = h' * y⁻¹ * h'⁻¹ := by rw [hyinv]
      _ = (h' * y * h'⁻¹)⁻¹ := by group
  exact ⟨X', hX'ne, hX'U, hX'pi', L27su_le_commutator_of_inverts hh'c hX'U hX'odd hinvX'⟩

end Work.CORE2B
