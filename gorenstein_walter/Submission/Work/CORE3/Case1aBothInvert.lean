import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.BMAX.InvolutionInverts
import Submission.Work.ASM.Basic
import Submission.Work.DSTR.map_fittingPiIn_le
import Submission.Work.CORE3.isPGroup_le_or_inf_eq_bot_of_isHallIn
import Submission.Work.CORE3.fittingPiIn_eq_iSup_pCoreIn
import Submission.Work.CORE3.Case1aSetup

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.CORE3

namespace Work.CORE3

open Subgroup
open Work.GW2

/-! ## Elementary helpers (private to this file) -/

/-- An element of order two is an involution. -/
private theorem sq_mul_self_eq_one {G : Type} [Group G] {s : G} (hs : orderOf s = 2) :
    s * s = 1 := by
  have h := pow_orderOf_eq_one s
  rw [hs] at h
  simpa [pow_two] using h

/-- Membership transfer across `I = I_U(s)`, from `I_U(s)` to `I`. -/
private theorem mem_of_mem_invSet {G : Type} [Group G] {I U : Subgroup G} {s x : G}
    (hI : (I : Set G) = invSet U s) (hx : x ∈ invSet U s) : x ∈ (I : Set G) := hI.symm ▸ hx

/-- Membership transfer across `I = I_U(s)`, from `I` to `I_U(s)`. -/
private theorem mem_invSet_of_mem {G : Type} [Group G] {I U : Subgroup G} {s x : G}
    (hI : (I : Set G) = invSet U s) (hx : x ∈ I) : x ∈ invSet U s :=
  hI ▸ (show x ∈ (I : Set G) from hx)

/-- `O_π` only depends on the primes lying in `π`. -/
private theorem piCore_eq_of_prime_iff' {G : Type} [Group G] {π π' : Set ℕ}
    (h : ∀ q, q.Prime → (q ∈ π ↔ q ∈ π')) : piCore π G = piCore π' G := by
  have hset : {N : Subgroup G | N.Normal ∧ ∀ q ∈ (Nat.card N).primeFactors, q ∈ π}
      = {N : Subgroup G | N.Normal ∧ ∀ q ∈ (Nat.card N).primeFactors, q ∈ π'} := by
    ext N
    constructor
    · rintro ⟨hn, hπ⟩
      exact ⟨hn, fun q hq => (h q (Nat.prime_of_mem_primeFactors hq)).mp (hπ q hq)⟩
    · rintro ⟨hn, hπ⟩
      exact ⟨hn, fun q hq => (h q (Nat.prime_of_mem_primeFactors hq)).mpr (hπ q hq)⟩
  unfold piCore
  rw [hset]

/-- `F_{3'}(X) = O_{3'}(F(X))` only sees the primes `≠ 3`. -/
private theorem fittingPiIn_three_compl_eq' {G : Type} [Group G] [Finite G] (X : Subgroup G) :
    fittingPiIn ({3}ᶜ : Set ℕ) X = fittingPiIn {q : ℕ | q.Prime ∧ q ≠ 3} X := by
  have h : fittingPi ({3}ᶜ : Set ℕ) ↥X = fittingPi {q : ℕ | q.Prime ∧ q ≠ 3} ↥X := by
    show (piCore ({3}ᶜ) (fitting ↥X)).map (fitting ↥X).subtype
        = (piCore {q : ℕ | q.Prime ∧ q ≠ 3} (fitting ↥X)).map (fitting ↥X).subtype
    rw [piCore_eq_of_prime_iff' (G := ↥(fitting ↥X)) (π := ({3}ᶜ : Set ℕ))
      (π' := {q : ℕ | q.Prime ∧ q ≠ 3}) (fun q hq =>
        ⟨fun h3 => ⟨hq, by simpa using h3⟩, fun h3 => by simpa using h3.2⟩)]
  show (fittingPi ({3}ᶜ : Set ℕ) ↥X).map X.subtype
      = (fittingPi {q : ℕ | q.Prime ∧ q ≠ 3} ↥X).map X.subtype
  rw [h]

/-- `S` normalizes `U = O(H)`: `U` is the image of the characteristic subgroup `O(↥H)` of `H`,
and `S ≤ H`. -/
private theorem S_le_normalizer_U {G : Type} [Group G] [Finite G] (B : BenderSetup G) :
    (B.S : Subgroup G) ≤ Subgroup.normalizer (B.U : Set G) := by
  have hH : B.H ≤ Subgroup.normalizer (B.U : Set G) := by
    have h := Work.CORE3.c1aLe_normalizer_map_subtype (K := B.H) (N := oddCore ↥B.H)
      (Work.GW2.oddCore_normal ↥B.H)
    simpa [Work.GW2.oddCoreIn] using h
  exact le_trans (Work.CORE2A.bSetup_S_le_H B) hH

/-- Normality passes from `L` down to an intermediate subgroup `K`. -/
private theorem normal_subgroupOf_mono' {G : Type} [Group G] {N K L : Subgroup G} (hKL : K ≤ L)
    (hNK : N ≤ K) (h : (N.subgroupOf L).Normal) : (N.subgroupOf K).Normal := by
  rw [Subgroup.normal_subgroupOf_iff hNK]
  intro a b ha hb
  exact (Subgroup.normal_subgroupOf_iff (le_trans hNK hKL)).mp h a b ha (hKL hb)

/-- If every element of `S − S₀` centralizes `Q`, then all of `S` does. -/
private theorem le_centralizer_of_forall_notMem_S0 {G : Type} [Group G] [Finite G]
    (B : BenderSetup G) {s : G} (hsS : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0)
    (hs2 : s * s = 1) {Q : Subgroup G}
    (h : ∀ s' ∈ (B.S : Subgroup G), s' ∉ B.S0 → Q ≤ Subgroup.centralizer ({s'} : Set G)) :
    Q ≤ Subgroup.centralizer ((B.S : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hx' : ∀ z ∈ (B.S : Subgroup G), z ∉ B.S0 → z * x = x * z := by
    intro z hz hz0
    exact (Subgroup.mem_centralizer_iff.mp (h z hz hz0 hx)) z (by simp)
  by_cases hy0 : y ∈ B.S0
  · have hys_mem : y * s ∈ (B.S : Subgroup G) := mul_mem hy hsS
    have hys_not : y * s ∉ B.S0 := by
      intro hcon
      exact hs0 (by
        have h2 : y⁻¹ * (y * s) ∈ B.S0 := mul_mem (inv_mem hy0) hcon
        simpa using h2)
    have h1 : (y * s) * x = x * (y * s) := hx' (y * s) hys_mem hys_not
    have h2 : s * x = x * s := hx' s hsS hs0
    have key1 : y * x = (y * s) * (s * x) := by
      rw [mul_assoc, ← mul_assoc s s x, hs2, one_mul]
    calc y * x = (y * s) * (s * x) := key1
      _ = (y * s) * (x * s) := by rw [h2]
      _ = ((y * s) * x) * s := by rw [← mul_assoc]
      _ = (x * (y * s)) * s := by rw [h1]
      _ = x * y := by rw [mul_assoc, mul_assoc y s s, hs2, mul_one]
  · exact hx' y hy hy0

/-! ## The `O_q(U)` dichotomy -/

/-- Bender's Case (1) dichotomy for `O_q(U)`: `I_U(s)` is Hall in `F(U)`, so the `q`-core of `U`
is either entirely inverted by `s` or entirely centralized by it. -/
private theorem pCoreIn_inverted_or_centralized {G : Type} [Group G] [Finite G]
    (I : Case1Inputs) (hFT : FeitThompsonProp) (B : BenderSetup G) {q : ℕ} (hq : q.Prime)
    {s : G} (hsN : s ∈ Subgroup.normalizer (B.U : Set G)) (hs2 : orderOf s = 2)
    (Ih : Subgroup G) (hIhset : (Ih : Set G) = invSet B.U s)
    (hIhhall : IsHallIn Ih (fittingIn B.U)) :
    (∀ x ∈ pCoreIn q B.U, s * x * s⁻¹ = x⁻¹) ∨
      pCoreIn q B.U ≤ Subgroup.centralizer ({s} : Set G) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hss : s * s = 1 := sq_mul_self_eq_one hs2
  have hc15 := (I.T.c15 G hFT B.U s hs2 (Work.CORE2A.bSetup_U_odd B) hsN).2.2 Ih hIhset
  have hnormU : (Ih.subgroupOf B.U).Normal := hc15.2.1
  have hIhle : Ih ≤ fittingIn B.U := hc15.2.2
  have hInormF : (Ih.subgroupOf (fittingIn B.U)).Normal :=
    normal_subgroupOf_mono' (Work.CORE3.c1aFittingIn_le B.U) hIhle hnormU
  rcases Work.CORE3.isPGroup_le_or_inf_eq_bot_of_isHallIn hq hIhhall hInormF
      (Work.CORE3.c1aPcoreIn_le_fittingIn q B.U) (Work.CORE3.c1aIsPGroup_pCoreIn q B.U)
    with hle | hdisj
  · left
    intro x hx
    exact (mem_invSet_of_mem hIhset (hle hx)).2
  · right
    refine Work.CORE3.c1aCentralizer_of_no_inverted (Q := pCoreIn q B.U) (x := s) hss
      (Work.CORE3.c1aLe_normalizer_pCoreIn q B.U hsN) ?_
    intro y hy hyinv
    have hyU : y ∈ B.U := Work.CORE3.c1aPcoreIn_le_self q B.U hy
    have hyIh : y ∈ Ih := mem_of_mem_invSet hIhset ⟨hyU, hyinv⟩
    have hmem : y ∈ pCoreIn q B.U ⊓ Ih := ⟨hy, hyIh⟩
    rw [hdisj] at hmem
    simpa using hmem

/-! ## The mixed case -/

/-- Design pass 4 §1, the mixed case of Bender 1981 p. 222: if `s₁` centralizes and `s₂` inverts
`O_q(U)` for a prime `q ≠ 3`, then `(s₁, s₂, q)` is again admissible `Case1aData`, so `hFr` and
`hA7` apply and force `q = 3`. -/
private theorem case1aMixedContra {G : Type} [Group G] [Finite G] (hFT : FeitThompsonProp)
    (hCtx : BenderCtx G) (B : BenderSetup G) (hCase1 : Case1 B) (hH : B.Hhat = B.H)
    (hFr : Case1aFrattiniProp) (hA7 : Case1aA7Prop)
    {q : ℕ} (hq : q.Prime) (hq3 : q ≠ 3)
    (hQle : pCoreIn q B.U ≤ fittingIn B.U) (hQq : IsPGroup q (pCoreIn q B.U))
    (hQne : pCoreIn q B.U ≠ ⊥)
    {s1 s2 : G} (hs1 : s1 ∈ (B.S : Subgroup G)) (hs1n : s1 ∉ B.S0) (hs1o : orderOf s1 = 2)
    (hs2 : s2 ∈ (B.S : Subgroup G)) (hs2n : s2 ∉ B.S0) (hs2o : orderOf s2 = 2)
    (hcent : pCoreIn q B.U ≤ Subgroup.centralizer ({s1} : Set G))
    (hinv : Inverts s2 (pCoreIn q B.U)) : False := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : IsSimpleGroup G := hCtx.simple
  -- `q ∈ π(F(U))`
  have hp_mem : q ∈ primesOf (fittingIn B.U) := by
    change q ∈ (Nat.card (fittingIn B.U)).primeFactors
    rw [Nat.mem_primeFactors]
    obtain ⟨k, hk⟩ := hQq.exists_card_eq
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · exfalso
        rw [h0, pow_zero] at hk
        exact hQne (Subgroup.card_eq_one.mp hk)
      · exact hpos
    refine ⟨hq, ?_, (Nat.card_pos (α := ↥(fittingIn B.U))).ne'⟩
    have hdvdQ : q ∣ Nat.card (pCoreIn q B.U) := by
      rw [hk]
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk1)
      exact ⟨q ^ m, by rw [pow_succ']⟩
    exact hdvdQ.trans (Subgroup.card_dvd_of_le hQle)
  -- the new admissible data
  let D' : Case1aData B :=
    { t1 := s1, t2 := s2, p := q, hp := hq, t1_mem := hs1, t2_mem := hs2, t1_nmem := hs1n,
      t2_nmem := hs2n, t1_order := hs1o, t2_order := hs2o, p_mem := hp_mem, cent := hcent,
      inv := hinv }
  -- a Sylow `q`-subgroup of `B = C_U(S)`
  have hP2exists : ∃ P2 : Subgroup G,
      P2 ≤ B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) ∧ IsPGroup q P2 ∧
        ¬ q ∣ P2.relIndex (B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G)) := by
    set Bc : Subgroup G := B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) with hBc
    haveI : Finite ↥Bc := inferInstance
    refine ⟨(((default : Sylow q ↥Bc) : Subgroup ↥Bc).map Bc.subtype),
      Subgroup.map_subtype_le ((default : Sylow q ↥Bc) : Subgroup ↥Bc),
      (default : Sylow q ↥Bc).isPGroup'.map Bc.subtype, ?_⟩
    have hsub : (((default : Sylow q ↥Bc) : Subgroup ↥Bc).map Bc.subtype).subgroupOf Bc
        = ((default : Sylow q ↥Bc) : Subgroup ↥Bc) :=
      Subgroup.comap_map_eq_self_of_injective Bc.subtype_injective
        ((default : Sylow q ↥Bc) : Subgroup ↥Bc)
    have hrel : (((default : Sylow q ↥Bc) : Subgroup ↥Bc).map Bc.subtype).relIndex Bc
        = ((default : Sylow q ↥Bc) : Subgroup ↥Bc).index := by
      show ((((default : Sylow q ↥Bc) : Subgroup ↥Bc).map Bc.subtype).subgroupOf Bc).index
        = ((default : Sylow q ↥Bc) : Subgroup ↥Bc).index
      rw [hsub]
    rw [hrel]
    exact Sylow.not_dvd_index _
  obtain ⟨P2, hP2le, hP2q, hP2rel⟩ := hP2exists
  have hP2ne : P2 ≠ ⊥ := (hFr G hFT hCtx B hCase1 hH D' P2 hP2le hP2q hP2rel).2.2
  -- `N_G(P₂) ≠ ⊤`
  have hNne : Subgroup.normalizer (P2 : Set G) ≠ ⊤ := by
    intro hNtop
    haveI hP2normal : P2.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases Subgroup.Normal.eq_bot_or_eq_top P2 with hbot | htop
    · exact hP2ne hbot
    · have hle : P2 ≤ pCore q G := Work.CORE2A.le_pCore_of_normal_isPGroup hP2q
      have hcoretop : pCore q G = ⊤ := by
        rcases Subgroup.Normal.eq_bot_or_eq_top (pCore q G) with h | h
        · rw [h] at hle
          exact absurd (le_bot_iff.mp hle) hP2ne
        · exact h
      have hPG : IsPGroup q G := by
        have h1 : IsPGroup q (pCore q G) :=
          Work.CORE2A.pCore_isPGroup_of_finite (H := G) (p := q)
        exact IsPGroup.of_equiv (hcoretop ▸ h1) Subgroup.topEquiv
      obtain ⟨a, b, hab⟩ := hCtx.nonab
      have ha1 : a ≠ 1 := by
        intro h1
        rw [h1, one_mul, mul_one] at hab
        exact hab rfl
      haveI : Nontrivial G := ⟨⟨a, 1, ha1⟩⟩
      have hZnt : Nontrivial ↥(Subgroup.center G) := IsPGroup.center_nontrivial hPG
      have hZne : Subgroup.center G ≠ ⊥ := by
        intro hbot'
        haveI : Subsingleton ↥(Subgroup.center G) := by rw [hbot']; infer_instance
        obtain ⟨x, y, hxy⟩ := hZnt
        exact hxy (Subsingleton.elim x y)
      have hZtop : Subgroup.center G = ⊤ := by
        rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h | h
        · exact absurd h hZne
        · exact h
      refine hab ?_
      have ha : a ∈ Subgroup.center G := by rw [hZtop]; trivial
      exact (Subgroup.mem_center_iff.mp ha b).symm
  obtain ⟨M, hMc, hNM⟩ :=
    Work.ASM.exists_coatom_ge_of_ne_top (Subgroup.normalizer (P2 : Set G)) hNne
  have hA7' := hA7 G hFT hCtx B hCase1 hH D' P2 M hP2le hP2q hP2rel hMc hNM
  have hcard : Nat.card (pCoreIn q B.U ⊓ M : Subgroup G) = 3 := hA7'.2.2.2.2
  have hsubP : IsPGroup q ((pCoreIn q B.U ⊓ M : Subgroup G)) := hQq.to_le inf_le_left
  obtain ⟨k, hk⟩ := hsubP.exists_card_eq
  have hk3 : q ^ k = 3 := hk.symm.trans hcard
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · exfalso
      rw [h0, pow_zero] at hk3
      norm_num at hk3
    · exact hpos
  have hdvd : q ∣ q ^ k := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk1)
    exact ⟨q ^ m, by rw [pow_succ']⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp (hk3 ▸ hdvd) with h | h
  · exact absurd h hq.ne_one
  · exact hq3 h

/-! ## The main step: every `O_q(U)`, `q ≠ 3`, is inverted -/

/-- In the subcase `Ĥ = H`, any involution `s ∈ S − S₀` inverts `F_{3'}(U) = O_{3'}(F(U))`. -/
private theorem inverts_fittingPiIn {G : Type} [Group G] [Finite G] (I : Case1Inputs)
    (hFT : FeitThompsonProp) (hCtx : BenderCtx G) (B : BenderSetup G) (hCase1 : Case1 B)
    (hH : B.Hhat = B.H) (hFr : Case1aFrattiniProp) (hA7 : Case1aA7Prop)
    (hBpf : Case1aBFpfProp) {s : G} (hsS : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0)
    (hs2 : orderOf s = 2) (Ih : Subgroup G) (hIhset : (Ih : Set G) = invSet B.U s)
    (hIhhall : IsHallIn Ih (fittingIn B.U)) :
    Inverts s (fittingPiIn ({3}ᶜ : Set ℕ) B.U) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn2, hdih⟩ := Work.CORE3.SylowDihedral G hCtx B
  have hreflect : ∀ s' ∈ (B.S : Subgroup G), s' ∉ B.S0 → orderOf s' = 2 :=
    fun s' hs' hs'0 => Work.CORE3.OutsideS0OrderTwo G hCtx B n hn2 hdih s' hs' hs'0
  have hSN : (B.S : Subgroup G) ≤ Subgroup.normalizer (B.U : Set G) := S_le_normalizer_U B
  -- `O_q(B.U) ≤ F_{3'}(U)` for `q ≠ 3`
  have hpCore_le_fittingPi : ∀ q : ℕ, q.Prime → q ≠ 3 →
      pCoreIn q B.U ≤ fittingPiIn ({3}ᶜ : Set ℕ) B.U := by
    intro q hq hq3
    rw [fittingPiIn_three_compl_eq' (X := B.U),
        Work.CORE3.fittingPiIn_eq_iSup_pCoreIn (X := B.U)
          (π := {q' : ℕ | q'.Prime ∧ q' ≠ 3}) (fun q' hq' => hq'.1)]
    exact le_iSup_of_le q (le_iSup_of_le ⟨hq, hq3⟩ le_rfl)
  -- every prime core off `3` is inverted
  have key : ∀ q : ℕ, q.Prime → q ≠ 3 → pCoreIn q B.U ≤ Ih := by
    intro q hq hq3
    haveI : Fact q.Prime := ⟨hq⟩
    by_cases hQne : pCoreIn q B.U = ⊥
    · rw [hQne]; exact bot_le
    · rcases pCoreIn_inverted_or_centralized I hFT B hq (hSN hsS) hs2 Ih hIhset hIhhall with
        hinv | hcent
      · intro x hx
        exact mem_of_mem_invSet hIhset
          ⟨Work.CORE3.c1aPcoreIn_le_self q B.U hx, hinv x hx⟩
      · exfalso
        by_cases hall : ∀ s' ∈ (B.S : Subgroup G), s' ∉ B.S0 →
            pCoreIn q B.U ≤ Subgroup.centralizer ({s'} : Set G)
        · -- then `S` centralizes `O_q(U)`, contradicting `hBpf`
          have hCS : pCoreIn q B.U ≤ Subgroup.centralizer ((B.S : Subgroup G) : Set G) :=
            le_centralizer_of_forall_notMem_S0 B hsS hs0 (sq_mul_self_eq_one hs2) hall
          have hB : pCoreIn q B.U ≤ B.U ⊓
              Subgroup.centralizer ((B.S : Subgroup G) : Set G) :=
            le_inf (Work.CORE3.c1aPcoreIn_le_self q B.U) hCS
          obtain ⟨x, hxQ, hxne⟩ : ∃ x ∈ pCoreIn q B.U, x ≠ 1 := by
            by_contra hcon
            push_neg at hcon
            exact absurd ((Subgroup.eq_bot_iff_forall (pCoreIn q B.U)).mpr hcon) hQne
          have hxc : x ∈ Subgroup.centralizer ({x} : Set G) := by
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            rw [Set.mem_singleton_iff] at hy
            rw [hy]
          have hbot := hBpf G hFT hCtx B hCase1 hH x (hB hxQ) hxne
          have hmem : x ∈ fittingPiIn ({3}ᶜ : Set ℕ) B.U ⊓ Subgroup.centralizer ({x} : Set G) :=
            ⟨hpCore_le_fittingPi q hq hq3 hxQ, hxc⟩
          rw [hbot] at hmem
          exact hxne (by simpa using hmem)
        · -- some reflection inverts `O_q(U)`: the mixed case
          push_neg at hall
          obtain ⟨s', hs'S, hs'0, hs'nc⟩ := hall
          obtain ⟨Is', hIs'set, hIs'shall⟩ := hCase1.1 s' hs'S hs'0
          rcases pCoreIn_inverted_or_centralized I hFT B hq (hSN hs'S)
              (hreflect s' hs'S hs'0) Is' hIs'set hIs'shall with hinv' | hcent'
          · exact case1aMixedContra hFT hCtx B hCase1 hH hFr hA7 hq hq3
              (Work.CORE3.c1aPcoreIn_le_fittingIn q B.U) (Work.CORE3.c1aIsPGroup_pCoreIn q B.U)
              hQne hsS hs0 hs2 hs'S hs'0 (hreflect s' hs'S hs'0) hcent hinv'
          · exact hs'nc hcent'
  -- conclude
  intro x hx
  rw [fittingPiIn_three_compl_eq' (X := B.U),
      Work.CORE3.fittingPiIn_eq_iSup_pCoreIn (X := B.U)
        (π := {q' : ℕ | q'.Prime ∧ q' ≠ 3}) (fun q' hq' => hq'.1)] at hx
  have hle : (⨆ (q : ℕ) (_ : q ∈ {q' : ℕ | q'.Prime ∧ q' ≠ 3}), pCoreIn q B.U) ≤ Ih :=
    iSup_le fun q => iSup_le fun hq => key q hq.1 hq.2
  have hxIh : x ∈ Ih := hle hx
  exact (mem_invSet_of_mem hIhset hxIh).2

/-- Design pass 4 §1 (Bender 1981 p. 222, "both `tᵢ` invert `F_p(U)`", where `p` is necessarily
`3`): in the subcase `Ĥ = H`, both `t₁` and `t₂` invert `F_{3'}(U) = O_{3'}(F(U))`.

The earlier leaves are supplied as hypotheses, because the argument needs them:
`Case1aA7Prop` (`hA7`, `|P₀| = 3`, `E(M)/Z ≅ A₇`) rules out the mixed cases: each `O_r(U)`
(`r` odd, `r ≠ 3`) is centralized or inverted by each `tᵢ` (Bender's Case (1) makes `I_U(tᵢ)`
Hall in `F(U)`); if `t₁` centralized and `t₂` inverted `O_r(U)` then `r` would be an admissible
choice of the prime `p` of `Case1aData`, and `p = 3`; if both centralize then `S` centralizes
`O_r(U)`, so `O_r(U) ≤ C_U(S) = B`, contradicting `hBpf : Case1aBFpfProp` (Bender p. 223,
fixed-point-freeness of `B` on `F_{3'}(U)`). -/
theorem Case1aBothInvert (I : Case1Inputs) (hSetup : Case1aSetupProp) (hFr : Case1aFrattiniProp)
    (hAb : Case1aAbelianProp) (hA7 : Case1aA7Prop) (hBpf : Case1aBFpfProp) :
    Case1aBothInvertProp := by
  intro G _ _ hFT hCtx B hCase1 hH D
  obtain ⟨I1, hI1set, hI1hall⟩ := hCase1.1 D.t1 D.t1_mem D.t1_nmem
  obtain ⟨I2, hI2set, hI2hall⟩ := hCase1.1 D.t2 D.t2_mem D.t2_nmem
  exact ⟨inverts_fittingPiIn I hFT hCtx B hCase1 hH hFr hA7 hBpf D.t1_mem D.t1_nmem
      D.t1_order I1 hI1set hI1hall,
    inverts_fittingPiIn I hFT hCtx B hCase1 hH hFr hA7 hBpf D.t2_mem D.t2_nmem
      D.t2_order I2 hI2set hI2hall⟩

end Work.CORE3

open Work.GW2

/-- The same lemma, mirrored at the namespace of the file path, so that it can be cited both as
`Work.CORE3.Case1aBothInvert` (the name the area requests) and as
`Work.CORE3.Work.CORE3.Case1aBothInvert` (the skeleton's namespace layout). -/
theorem Case1aBothInvert (I : Case1Inputs) (hSetup : Case1aSetupProp) (hFr : Case1aFrattiniProp)
    (hAb : Case1aAbelianProp) (hA7 : Case1aA7Prop) (hBpf : Case1aBFpfProp) :
    Case1aBothInvertProp :=
  _root_.Work.CORE3.Work.CORE3.Case1aBothInvert I hSetup hFr hAb hA7 hBpf

end Work.CORE3
