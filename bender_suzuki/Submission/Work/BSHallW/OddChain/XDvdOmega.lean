import Mathlib
import Submission.Work.ThmF.Prove.Step9Defs
import Submission.Work.ThmF.Prove.step9N2
import Submission.Work.ThmF.Prove.step9N3a
import Submission.Work.ThmF.Prove.step9Omega1
import Submission.Work.ThmF.Prove.step9Omega2
import Submission.Work.ThmF.Prove.step9SylowW
import Submission.Work.ThmF.Prove.step9N4
import Submission.Work.ThmF.Prove.n1NotDvdQ
import Submission.Work.BSHallW.OddChain.HallReduction
import Submission.Work.ThmF.Prove.NormalizerOddPart
import Submission.Work.ThmF.ChV3.Chain15
import Submission.Work.BSHallW.Defs
import Submission.Work.S3.P_card_ne_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.BSHallW.OddChain

open Work.ThmF Work.ThmF.Prove

variable {G : Type} [Group G]

/-- `V = C_D(t)` normalises `W = C_V(K)`, because `[V,V] ≤ W` and `W ≤ V`. -/
lemma normW_of_VW {H : Subgroup G} {t : G}
    (hVW : ∀ a ∈ centD H t, ∀ b ∈ centD H t, a * b * a⁻¹ * b⁻¹ ∈ W H t) :
    centD H t ≤ Subgroup.normalizer ((W H t) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : x ∈ centD H t := Work.ThmF.W_le_centD H t hx
    have hcomm : a * x * a⁻¹ * x⁻¹ ∈ W H t := hVW a ha x hx'
    have : a * x * a⁻¹ = (a * x * a⁻¹ * x⁻¹) * x := by group
    rw [this]
    exact (W H t).mul_mem hcomm hx
  · intro hx
    have ha' : a⁻¹ ∈ centD H t := (centD H t).inv_mem ha
    have hx' : a * x * a⁻¹ ∈ centD H t := Work.ThmF.W_le_centD H t hx
    have hcomm : a⁻¹ * (a * x * a⁻¹) * (a⁻¹)⁻¹ * (a * x * a⁻¹)⁻¹ ∈ W H t :=
      hVW a⁻¹ ha' (a * x * a⁻¹) hx'
    have : x = (a⁻¹ * (a * x * a⁻¹) * (a⁻¹)⁻¹ * (a * x * a⁻¹)⁻¹) * (a * x * a⁻¹) := by group
    rw [this]
    exact (W H t).mul_mem hcomm hx

/-- The pointwise form of `V ≤ N_G(W)`. -/
lemma normW_pointwise {H : Subgroup G} {t : G}
    (hVW : ∀ a ∈ centD H t, ∀ b ∈ centD H t, a * b * a⁻¹ * b⁻¹ ∈ W H t) :
    ∀ a ∈ centD H t, ∀ b ∈ W H t, a * b * a⁻¹ ∈ W H t := by
  intro a ha b hb
  have hb' : b ∈ centD H t := Work.ThmF.W_le_centD H t hb
  have h := hVW a ha b hb'
  have : a * b * a⁻¹ = (a * b * a⁻¹ * b⁻¹) * b := by group
  rw [this]
  exact (W H t).mul_mem h hb

/-- A Sylow `p`-subgroup of `G` lying in `V = C_D(t)` and containing `P`: a Sylow of `V` containing
`P`, which is a Sylow of `G` because `|G|_p = |V|_p` (`step9N2`). -/
lemma exists_sylow_le_centD [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hC4 : ChIIFourProp) (hTh : ThompsonFrobeniusProp)
    (c : ChV3.CtxF H Q t s r P) (h3 : Step3Out Q P)
    (hG : Nat.card G = (Nat.card Q + 1) * Nat.card ↥H)
    (hH : Nat.card ↥H = Nat.card Q * Nat.card ↥(twoPoint H t))
    (hD : Nat.card ↥(twoPoint H t) = (2 ^ Nat.card P - 1) * Nat.card ↥(W H t) * Nat.card P)
    (hV : Nat.card ↥(centD H t) = Nat.card ↥(W H t) * Nat.card P)
    (hX : ¬ Nat.card P ∣ Nat.card (G ⧸ H)) :
    ∃ S : Sylow (Nat.card P) G,
      P ≤ (S : Subgroup G) ∧ (S : Subgroup G) ≤ centD H t := by
  have hp : (Nat.card P).Prime := c.P_prime
  haveI : Fact (Nat.card P).Prime := ⟨hp⟩
  have hQ : ¬ Nat.card P ∣ Nat.card Q := n1NotDvdQ hC4 hTh c h3
  have hfact := step9N2 hp hQ hG hH hD hV hX
  have hPp : IsPGroup (Nat.card P) P := IsPGroup.of_card (n := 1) (by rw [pow_one])
  have hPpV : IsPGroup (Nat.card P) ↥(P.subgroupOf (centD H t)) :=
    IsPGroup.of_equiv hPp (Subgroup.subgroupOfEquivOfLe c.P_le).symm
  obtain ⟨SV, hPSV⟩ := hPpV.exists_le_sylow
  set Ssub : Subgroup G := (SV : Subgroup ↥(centD H t)).map (centD H t).subtype with hSsub
  have hPleSsub : P ≤ Ssub := by
    rw [hSsub]
    calc P = (P.subgroupOf (centD H t)).map (centD H t).subtype := by
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr c.P_le]
      _ ≤ _ := Subgroup.map_mono hPSV
  have hSsub_le : Ssub ≤ centD H t := by
    rw [hSsub]; exact Subgroup.map_subtype_le _
  have hSsub_p : IsPGroup (Nat.card P) Ssub := by
    rw [hSsub]; exact SV.isPGroup'.map _
  have hcardSsub : Nat.card ↥Ssub = (Nat.card P) ^ (Nat.card G).factorization (Nat.card P) := by
    rw [hSsub, Subgroup.card_map_of_injective Subtype.coe_injective,
      Sylow.card_eq_multiplicity SV, hfact]
  obtain ⟨S, hSsubS⟩ := hSsub_p.exists_le_sylow
  have hcardS : Nat.card ↥(S : Subgroup G) = (Nat.card P) ^ (Nat.card G).factorization (Nat.card P) :=
    Sylow.card_eq_multiplicity S
  have hEq : Ssub = (S : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hSsubS (le_of_eq (by rw [hcardS, ← hcardSsub]))
  exact ⟨S, by rw [← hEq]; exact hPleSsub, by rw [← hEq]; exact hSsub_le⟩

/-- A finite group with a normal subgroup of odd prime index `p` and even order is not simple. -/
theorem simple_not_hasNormalIndexP {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hs : IsSimpleGroup G) (heven : Even (Nat.card G)) :
    ¬ Work.ThmF.HasNormalIndexP p G := by
  rintro ⟨K, hKn, hKi⟩
  haveI : K.Normal := hKn
  have hpodd : Odd p := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left hp2)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ K hKn with h | h
  · rw [h, Subgroup.index_bot] at hKi
    rw [hKi] at heven
    exact (Nat.not_even_iff_odd.mpr hpodd) heven
  · rw [h, Subgroup.index_top] at hKi
    exact hp.ne_one hKi.symm

theorem xDvdOmega {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hC4 : Submission.Blueprint.ChIIFourProp) (hTh : Submission.Blueprint.ThompsonFrobeniusProp)
    (hHW : Work.BSHallW.HallWielandtOddProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h3 : Work.ThmF.Prove.Step3Out Q P)
    (h8 : Work.ThmF.Prove.Step8Out H Q t P)
    (hQ1 : Work.ThmF.oddPart Q ≠ ⊥)
    (hG : Nat.card G = (Nat.card Q + 1) * Nat.card ↥H)
    (hH : Nat.card ↥H = Nat.card Q * Nat.card ↥(Submission.Blueprint.twoPoint H t))
    (hD : Nat.card ↥(Submission.Blueprint.twoPoint H t) =
      (2 ^ Nat.card P - 1) * Nat.card ↥(Work.ThmF.W H t) * Nat.card P)
    (hV : Nat.card ↥(Submission.Blueprint.centD H t) = Nat.card ↥(Work.ThmF.W H t) * Nat.card P)
    (hPW : P ⊓ Work.ThmF.W H t = ⊥)
    (hfpfW : ∀ w ∈ Work.ThmF.W H t, w ≠ 1 →
      Work.ThmF.oddPart Q ⊓ Subgroup.centralizer ({w} : Set G) = ⊥)
    (hVW : ∀ a ∈ Submission.Blueprint.centD H t, ∀ b ∈ Submission.Blueprint.centD H t,
      a * b * a⁻¹ * b⁻¹ ∈ Work.ThmF.W H t)
    (hL2b : ∀ X : Subgroup G, X ≤ Submission.Blueprint.centD H t → X ≠ ⊥ →
      Subgroup.normalizer (X : Set G) =
        Subgroup.centralizer (X : Set G) ⊔ (Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G))) :
    Nat.card P ∣ Nat.card (G ⧸ H) := by
  classical
  have hp : (Nat.card P).Prime := c.P_prime
  have hp2 : Nat.card P ≠ 2 := Work.S3.P_card_ne_two c
  haveI : Fact (Nat.card P).Prime := ⟨hp⟩
  by_contra hX
  -- ## (N1) `p ∤ |Q|` and (N2) `|G|_p = |V|_p`
  have hpQ : ¬ Nat.card P ∣ Nat.card Q := n1NotDvdQ hC4 hTh c h3
  have hfac : (Nat.card ↥(centD H t)).factorization (Nat.card P) =
      (Nat.card G).factorization (Nat.card P) :=
    step9N2 hp hpQ hG hH hD hV hX
  -- ## a Sylow `p`-subgroup `S` of `G` with `P ≤ S ≤ V`
  obtain ⟨S, hPS, hSV⟩ := exists_sylow_le_centD hC4 hTh c h3 hG hH hD hV hX
  have hWVn : centD H t ≤ Subgroup.normalizer ((W H t) : Set G) := normW_of_VW hVW
  -- ## `T = S ⊓ W`
  set T : Subgroup G := (S : Subgroup G) ⊓ W H t with hTdef
  have hTW : T ≤ W H t := by rw [hTdef]; exact inf_le_right
  have hTS : T ≤ (S : Subgroup G) := by rw [hTdef]; exact inf_le_left
  have hTp : IsPGroup (Nat.card P) T := S.isPGroup'.to_le hTS
  have hW_Q : W H t ≤ Subgroup.normalizer (Q : Set G) :=
    (le_trans (le_trans (Work.ThmF.W_le_centD H t) inf_le_left) inf_le_left).trans c.split.normal
  have hTQ : T ≤ Subgroup.normalizer (Work.ThmF.oddPart Q : Set G) :=
    (hTW.trans hW_Q).trans (NormalizerOddPart Q)
  have hnotpQ1 : ¬ Nat.card P ∣ Nat.card ↥(Work.ThmF.oddPart Q) := fun h =>
    hpQ (h.trans (Subgroup.card_dvd_of_le (Work.ThmF.oddPart_le Q)))
  have hTcyc : IsCyclic ↥T := step9N3a hp hp2 hTW hTp hQ1 hnotpQ1 hTQ hfpfW
  -- ## `S = T ⋊ P`
  obtain ⟨hrelT, hSTP0⟩ :=
    step9SylowW (p := Nat.card P) hp (Work.ThmF.W_le_centD H t) hWVn hV c.P_le rfl hPW S hPS hSV
  have hSTP : (S : Subgroup G) = T ⊔ P := by rw [hTdef]; exact hSTP0
  -- ## a generator `y` of `P`
  obtain ⟨y0, hy0ord⟩ :=
    @exists_prime_orderOf_dvd_card' ↥P _ _ (Nat.card P) ⟨hp⟩ (dvd_refl (Nat.card P))
  let y : G := (y0 : G)
  have hyP : y ∈ P := y0.2
  have hordy : orderOf y = Nat.card P := by
    show orderOf ((y0 : ↥P) : G) = Nat.card P
    rw [Subgroup.orderOf_coe, hy0ord]
  have hygen : P = Subgroup.zpowers y := by
    have hle : Subgroup.zpowers y ≤ P := Subgroup.zpowers_le.mpr hyP
    have hcard : Nat.card ↥(Subgroup.zpowers y) = Nat.card ↥P := by
      rw [Nat.card_zpowers, hordy]
    exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)).symm
  have hSzy : (S : Subgroup G) = T ⊔ Subgroup.zpowers y := by rw [hSTP, hygen]
  have hyS : y ∈ (S : Subgroup G) := by
    rw [hSzy]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hordy
    exact hp.ne_one hordy.symm
  have hyT : y ∉ T := by
    intro hy
    have h2 : y ∈ P ⊓ W H t := ⟨hyP, hTW hy⟩
    rw [hPW] at h2
    exact hy1 (Subgroup.mem_bot.mp h2)
  -- ## `|C_T(y)| ≤ p`
  have hC : Nat.card ↥(T ⊓ Subgroup.centralizer ({y} : Set G)) ≤ Nat.card P := by
    have hle1 : T ⊓ Subgroup.centralizer ({y} : Set G) ≤ Work.ThmF.ChV3.Sig H t P := by
      intro x hx
      obtain ⟨hxT, hxc⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨hTW hxT, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hqy : q ∈ Subgroup.zpowers y := by rw [← hygen]; exact hq
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hqy
      have hxy : Commute x y := by
        rw [Commute]; exact (Subgroup.mem_centralizer_iff.mp hxc y (Set.mem_singleton y)).symm
      rw [← hk]
      exact ((Commute.zpow_right hxy k).eq).symm
    have hdvd1 : Nat.card ↥(T ⊓ Subgroup.centralizer ({y} : Set G)) ∣
        Nat.card ↥(Work.ThmF.ChV3.Sig H t P) := Subgroup.card_dvd_of_le hle1
    rcases eq_or_ne (Work.ThmF.ChV3.Sig H t P) ⊥ with hSig | hSig
    · rw [hSig, Subgroup.card_bot, Nat.dvd_one] at hdvd1
      rw [hdvd1]; exact hp.one_le
    · have hprime := (h8 hSig).1
      rcases (Nat.dvd_prime hprime).mp hdvd1 with h1 | h1
      · rw [h1]; exact hp.one_le
      · rw [h1]
        have hdvdT1 : Nat.card ↥(T ⊓ Subgroup.centralizer ({y} : Set G)) ∣ Nat.card ↥T :=
          Subgroup.card_dvd_of_le inf_le_left
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hTp
        have hpk : Nat.card ↥(Work.ThmF.ChV3.Sig H t P) ∣ Nat.card P ^ k := by
          rw [h1, hk] at hdvdT1; exact hdvdT1
        have hdvd2 : Nat.card ↥(Work.ThmF.ChV3.Sig H t P) ∣ Nat.card P := hprime.dvd_of_dvd_pow hpk
        rcases (Nat.dvd_prime hp).mp hdvd2 with h2 | h2
        · exact absurd h2 hprime.ne_one
        · exact le_of_eq h2
  -- ## `T ⊴ S`
  have hTn : ∀ g ∈ (S : Subgroup G), ∀ x ∈ T, g * x * g⁻¹ ∈ T := by
    intro g hg x hx
    have hxS : x ∈ (S : Subgroup G) := hTS hx
    have hxW : x ∈ W H t := hTW hx
    rw [hTdef]
    exact Subgroup.mem_inf.mpr
      ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hg hxS) ((S : Subgroup G).inv_mem hg),
       (Subgroup.mem_normalizer_iff.mp (hWVn (hSV hg)) x).mp hxW⟩
  -- ## `Ω₁(S) = C_T(y) ⊔ ⟨y⟩`
  obtain ⟨hAi, hAab'⟩ :=
    step9Omega1 (S := (S : Subgroup G)) (T := T) (y := y)
      hp hp2 hyS hyT hordy hTcyc hTp hTn hSzy hC
  set Z : Subgroup G := T ⊓ Subgroup.centralizer ({y} : Set G) with hZdef
  set A : Subgroup G := Z ⊔ Subgroup.zpowers y with hAdef
  have hAi' : ∀ x ∈ (S : Subgroup G), x ^ Nat.card P = 1 ↔ x ∈ A := by
    intro x hx
    rw [hAdef, hZdef]
    exact hAi x hx
  have hZA : Z ≤ A := by rw [hAdef]; exact le_sup_left
  have hAleS : A ≤ (S : Subgroup G) := by
    rw [hAdef]
    exact sup_le (le_trans inf_le_left hTS) (by rw [hSzy]; exact le_sup_right)
  have hZleS : Z ≤ (S : Subgroup G) := le_trans hZA hAleS
  have hAleV : A ≤ centD H t := le_trans hAleS hSV
  have hAne : A ≠ ⊥ := by
    intro h
    have hyA : y ∈ A := by rw [hAdef]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    rw [h] at hyA
    exact hy1 (Subgroup.mem_bot.mp hyA)
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := hAab'
  -- ## `A ⊓ W = Z`
  have hAinfW : A ⊓ W H t = Z := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxA, hxW⟩ := Subgroup.mem_inf.mp hx
      have hyZ : Subgroup.zpowers y ≤ Subgroup.normalizer (Z : Set G) := by
        rw [Subgroup.le_normalizer_iff]
        intro w hw z hz
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
        rw [← hk]
        have hzy : z * y = y * z :=
          (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 y (Set.mem_singleton y)).symm
        have hzc : Commute y z := hzy.symm
        rw [(hzc.zpow_left k).eq, mul_inv_cancel_right]
        exact hz
      have hdec : ∀ s : G, s ∈ A ↔ ∃ z ∈ Z, ∃ w ∈ Subgroup.zpowers y, z * w = s := by
        intro s
        rw [hAdef, ← SetLike.mem_coe,
          Subgroup.coe_mul_of_right_le_normalizer_left Z (Subgroup.zpowers y) hyZ]
        exact Set.mem_mul
      obtain ⟨z, hz, w, hw, hzw⟩ := (hdec x).mp hxA
      have hzW : z ∈ W H t := hTW (Subgroup.mem_inf.mp hz).1
      have hwW : w ∈ W H t := by
        have hweq : w = z⁻¹ * (z * w) := by group
        rw [hweq]
        exact (W H t).mul_mem ((W H t).inv_mem hzW) (hzw ▸ hxW)
      have hwP : w ∈ P := by rw [hygen]; exact hw
      have hwbot : w ∈ P ⊓ W H t := ⟨hwP, hwW⟩
      rw [hPW] at hwbot
      have hw1 : w = 1 := Subgroup.mem_bot.mp hwbot
      rw [← hzw, hw1, mul_one]
      exact hz
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨hZA hx, hTW (Subgroup.mem_inf.mp hx).1⟩
  -- ## `[S,S] ≤ Z`
  have hcommSZ : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G),
      a * b * a⁻¹ * b⁻¹ ∈ Z := by
    have h := step9Omega2 (S := (S : Subgroup G)) (T := T) (y := y)
      hp hp2 hSzy hTn hTcyc hTp hyT hordy hC
    intro a ha b hb
    have h' := h a ha b hb
    rw [hZdef]
    exact h'
  -- ## `N_G(S) ≤ N_G(A)`
  have hAlchar : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
      Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg a ha
    have hgaS : g * a * g⁻¹ ∈ (S : Subgroup G) :=
      (Subgroup.mem_normalizer_iff.mp hg a).mp (hAleS ha)
    have hap : a ^ Nat.card P = 1 := (hAi' a (hAleS ha)).mpr ha
    refine (hAi' (g * a * g⁻¹) hgaS).mp ?_
    have hmap : (g * a * g⁻¹) ^ Nat.card P = (MulAut.conj g) (a ^ Nat.card P) := by
      rw [map_pow]; rfl
    rw [hmap, hap, map_one]
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (A : Set G) :=
    fun g hg => hAlchar (Subgroup.le_normalizer (H := (S : Subgroup G)) hg)
  -- ## Hall–Wielandt in `G` with `A`
  have hwc : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) →
      A.map (MulAut.conj g).toMonoidHom = A := by
    intro g hg
    have hle : A.map (MulAut.conj g).toMonoidHom ≤ A := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      have hxS : g * a * g⁻¹ ∈ (S : Subgroup G) := hg (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
      refine (hAi' (g * a * g⁻¹) hxS).mp ?_
      have hmap : (g * a * g⁻¹) ^ Nat.card P = (MulAut.conj g) (a ^ Nat.card P) := by
        rw [map_pow]; rfl
      rw [hmap, (hAi' a (hAleS ha)).mpr ha, map_one]
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq
      (Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective).symm)
  have hHW1 := hHW G (Nat.card P) hp hp2 S A hAleS hwc hAab
  set N : Subgroup G := Subgroup.normalizer (A : Set G) with hNdef
  have hNGSle : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ N := hAlchar
  have hSN' : (S : Subgroup G) ≤ N := hSN
  -- ## `Z ⊴ N`
  have hNdecomp : N = Subgroup.centralizer (A : Set G) ⊔ (centD H t ⊓ N) := by
    rw [hNdef]; exact hL2b A hAleV hAne
  have hZGnormZ : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (Z : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro c hc z hz
    have h2 : c * z = z * c := (Subgroup.mem_centralizer_iff.mp hc z (hZA hz)).symm
    have h4 : c * z * c⁻¹ = z := by rw [h2]; group
    rw [h4]; exact hz
  have hZGNnormZ : centD H t ⊓ N ≤ Subgroup.normalizer (Z : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro d hd z hz
    have hdV : d ∈ centD H t := (Subgroup.mem_inf.mp hd).1
    have hdN : d ∈ N := (Subgroup.mem_inf.mp hd).2
    have hzaA : z ∈ A := hZA hz
    have hdzW : d * z * d⁻¹ * z⁻¹ ∈ W H t := hVW d hdV z (hAleV hzaA)
    have hdzA : d * z * d⁻¹ * z⁻¹ ∈ A :=
      A.mul_mem ((Subgroup.mem_normalizer_iff.mp hdN z).mp hzaA) (A.inv_mem hzaA)
    have hdzZ : d * z * d⁻¹ * z⁻¹ ∈ Z := by
      have hmem : d * z * d⁻¹ * z⁻¹ ∈ A ⊓ W H t := ⟨hdzA, hdzW⟩
      rwa [hAinfW] at hmem
    have h3 : d * z * d⁻¹ = (d * z * d⁻¹ * z⁻¹) * z := by group
    rw [h3]
    exact Z.mul_mem hdzZ hz
  have hZN' : N ≤ Subgroup.normalizer (Z : Set G) := by
    rw [hNdecomp]
    exact sup_le hZGnormZ hZGNnormZ
  have hZleN : Z ≤ N := le_trans hZA (by rw [hNdef]; exact Subgroup.le_normalizer (H := A))
  -- ## `N_G(S)` has a normal subgroup of index `p` containing `Z` (N4)
  have hSGsyl : ¬ Nat.card P ∣ (S : Subgroup G).relIndex
      (Subgroup.normalizer ((S : Subgroup G) : Set G)) := fun h =>
    Sylow.not_dvd_index S (Nat.dvd_trans h
      (Subgroup.relIndex_dvd_index_of_le (Subgroup.le_normalizer (H := (S : Subgroup G)))))
  have hSne : (S : Subgroup G) ≠ ⊥ := by
    intro h
    have hy' : y ∈ (⊥ : Subgroup G) := by rw [← h]; exact hyS
    exact hy1 (Subgroup.mem_bot.mp hy')
  obtain ⟨M, hMn, hMidx, hMle⟩ :=
    step9N4 (H := H) (Q := Q) (t := t) (s := s) (r := r) (P := P) (S₁ := (S : Subgroup G))
      hp hSV hSne S.isPGroup' hSGsyl hrelT (normW_pointwise hVW) hVW hL2b
  have hZleM : Z ≤ Subgroup.map (Subgroup.normalizer ((S : Subgroup G) : Set G)).subtype M := by
    intro z hz
    have hzT : z ∈ T := (Subgroup.mem_inf.mp hz).1
    have hzT' : z ∈ (S : Subgroup G) ⊓ W H t := by rw [← hTdef]; exact hzT
    have hzNGS : z ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
      Subgroup.le_normalizer (H := (S : Subgroup G)) (hTS hzT)
    refine Subgroup.mem_map.mpr ⟨⟨z, hzNGS⟩, ?_, rfl⟩
    exact hMle (Subgroup.mem_subgroupOf.mpr hzT')
  -- ## the second Hall–Wielandt reduction
  have hZsubM : Z.subgroupOf (Subgroup.normalizer ((S : Subgroup G) : Set G)) ≤ M := by
    intro x hx
    have hxZ : (x : G) ∈ Z := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨m, hmM, hmx⟩ := Subgroup.mem_map.mp (hZleM hxZ)
    have h2 : (m : G) = (x : G) := hmx
    rw [← Subtype.ext h2]; exact hmM
  have hNI : Work.ThmF.HasNormalIndexP (Nat.card P) ↥N :=
    Work.BSHallW.OddChain.HallReductionIndexP (p := Nat.card P) hp hp2 hHW S A Z hAleS hZleS hZA hZN'
      (fun a ha b hb => hcommSZ a ha b hb) hNGSle ⟨M, hMn, hMidx, hZsubM⟩
  have hHG : Work.ThmF.HasNormalIndexP (Nat.card P) G := hHW1.mpr hNI
  -- ## contradiction with simplicity
  have hGeven : Even (Nat.card G) := by
    obtain ⟨u, hu⟩ := Work.ThmF.split_even_card_H c.split
    rw [hG, hu]
    exact ⟨(Nat.card Q + 1) * u, by ring⟩
  exact simple_not_hasNormalIndexP hp hp2 c.simple hGeven hHG

end Work.BSHallW.OddChain
