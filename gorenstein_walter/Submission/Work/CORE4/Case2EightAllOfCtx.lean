import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2EightObjExists
import Submission.Work.CORE4.Case2SixEmbed
import Submission.Work.CORE4.Case2Eight
import Submission.Work.CORE4.Case2EightA_le_FsupK0
import Submission.Work.CORE4.Case2EightP0LeP1
import Submission.Work.CORE4.Case2EightP1Le
import Submission.Work.CORE4.S0CentUO2
import Submission.Work.CORE4.EightAeqOmega
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.EightAnormalFitting_of_pcore

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## §4 (6) without §4 (7)

The object layer of §4 (8) (`p ∣ |K₀|`, the `(p,p)`-subgroup `A`, `A ≤ F ⊔ K₀`) needs only Bender's
(6), not the (7) layer: `Case2SixEmbed` gives `|F| ∣ |K₀|` at the `Case2Ctx6` level, and
`p ∣ |F|` for `P ≤ F` of order `p`.  This is what lets the whole of §4 (8) be proved from `(1)–(6)`
plus the two trichotomy consequences. -/

/-- `Case2 B` from the §4 data (`h.D` carries `M`, `t ∈ E(M)`, `X ≤ F(U)` with `N_G(X) ≤ M`). -/
theorem case2_of_ctx {B : Work.GW2.BenderSetup G} (h : Work.GW2.Case2Ctx B) :
    Work.GW2.Case2 B :=
  ⟨h.D.M, h.D.M_coatom, h.D.t_mem, h.D.X, h.D.X_ne, h.D.X_le, h.D.NX_le⟩

/-- Forget §4 (7)–(9). -/
def ctx6_of_ctx {B : Work.GW2.BenderSetup G} (h : Work.GW2.Case2Ctx B) :
    Work.GW2.Case2Ctx6 B :=
  ⟨h.D, h.pre, h.F_ti, h.F_cyclic⟩

/-- **Bender's (6): `|F| ∣ |K₀|`** for the §4 configuration (`K₀ = F(U) ⊓ K`). -/
theorem card_F_dvd_card_K0_of_ctx (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) :
    Nat.card ↥h.D.F ∣ Nat.card ↥h.D.K0 :=
  Work.CORE4.Case2SixEmbed I G hbc B (ctx6_of_ctx h)

/-- **§4 (8), first conjunct: `p ∣ |K₀|`**, for every prime `p` with a subgroup `P ≤ F` of order
`p`.  Route: `p ∣ |F|` (Cauchy-free: `|P| = p`, `P ≤ F`), and `|F| ∣ |K₀|` by Bender's (6); no §4
(7) input is needed. -/
theorem dvd_card_K0_of_ctx (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    {p : ℕ} (hp : p.Prime) {P : Subgroup G} (hPF : P ≤ h.D.F) (hPcard : Nat.card P = p) :
    p ∣ Nat.card ↥h.D.K0 := by
  have hpF : p ∣ Nat.card ↥h.D.F := by
    rw [← hPcard]; exact Subgroup.card_dvd_of_le hPF
  exact hpF.trans (card_F_dvd_card_K0_of_ctx I hbc B h)

/-! ## The `(p,p)`-object of §4 (8) -/

/-- **§4 (8), object half, at the `Case2Ctx` level**: the unique subgroup `A ≤ F ⊔ K` of order
`p ^ 2` and exponent `p` containing `P`.  (The proof is `Case2EightObjExists`'s, with `p ∣ |K₀|`
supplied by `dvd_card_K0_of_ctx` instead of §4 (7).) -/
theorem ctxObjExists (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    (p : ℕ) (P : Subgroup G) (hp : p.Prime) (hPF : P ≤ h.D.F) (hPcard : Nat.card P = p) :
    ∃ A : Subgroup G, Work.GW2.Case2EightObj h.D p P A := by
  have hpF : p ∣ Nat.card ↥h.D.F := by
    rw [← hPcard]; exact Subgroup.card_dvd_of_le hPF
  have hpK0 : p ∣ Nat.card ↥h.D.K0 := dvd_card_K0_of_ctx I hbc B h hp hPF hPcard
  have hpK : p ∣ Nat.card ↥h.D.K := hpK0.trans (Subgroup.card_dvd_of_le inf_le_right)
  obtain ⟨Kp, hKp_le, hKp_card, hKp_omega⟩ :=
    CyclicOmegaPrime h.D.K p h.pre.K_cyclic hp hpK
  obtain ⟨Fp, hFp_le, hFp_card, hFp_omega⟩ := CyclicOmegaPrime h.D.F p h.F_cyclic hp hpF
  have hP_le_Fp : P ≤ Fp := fun x hx =>
    (hFp_omega x (hPF hx)).mp (pow_eq_one_of_card_eq hPcard hx)
  have hPFp : P = Fp :=
    Subgroup.eq_of_le_of_card_ge hP_le_Fp (by rw [hFp_card, hPcard])
  have hP_omega : ∀ x ∈ h.D.F, x ^ p = 1 ↔ x ∈ P := by
    intro x hx
    rw [hPFp]
    exact hFp_omega x hx
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    Case2EightPpSupUnique h.D.F h.D.K P Kp p (F_inf_K_eq_bot_c4 B h.D)
      (F_le_normalizer_K_c4 I B h.D) (F_commute_K_c4 I B h.D h.pre)
      hPF hKp_le hP_omega hKp_omega hPcard hKp_card
  exact ⟨P ⊔ Kp, hp, hPF, hPcard, h2, h3, h4, h1, h5⟩

/-- **§4 (8), second conjunct: `A ≤ F ⊔ K₀`** (the `p`-torsion of `K` lies in `K₀`). -/
theorem ctxA_le_FsupK0 (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    (p : ℕ) (P A : Subgroup G) (hp : p.Prime) (hPF : P ≤ h.D.F) (hPcard : Nat.card P = p)
    (hObj : Work.GW2.Case2EightObj h.D p P A) :
    A ≤ h.D.F ⊔ h.D.K0 := by
  obtain ⟨_, _, _, hAle, hAcard, hAexp, _, hAuniq⟩ := hObj
  have hpF : p ∣ Nat.card ↥h.D.F := by
    rw [← hPcard]; exact Subgroup.card_dvd_of_le hPF
  have hpK : p ∣ Nat.card ↥h.D.K :=
    (dvd_card_K0_of_ctx I hbc B h hp hPF hPcard).trans
      (Subgroup.card_dvd_of_le inf_le_right)
  have hpK0 : p ∣ Nat.card ↥h.D.K0 := dvd_card_K0_of_ctx I hbc B h hp hPF hPcard
  obtain ⟨Kp, hKp_le, hKp_card, hKp_omega⟩ :=
    CyclicOmegaPrime h.D.K p h.pre.K_cyclic hp hpK
  obtain ⟨Fp, hFp_le, hFp_card, hFp_omega⟩ := CyclicOmegaPrime h.D.F p h.F_cyclic hp hpF
  have hP_le_Fp : P ≤ Fp := fun x hx =>
    (hFp_omega x (hPF hx)).mp (pow_eq_one_of_card_eq hPcard hx)
  have hPFp : P = Fp :=
    Subgroup.eq_of_le_of_card_ge hP_le_Fp (by rw [hFp_card, hPcard])
  have hP_omega : ∀ x ∈ h.D.F, x ^ p = 1 ↔ x ∈ P := by
    intro x hx
    rw [hPFp]
    exact hFp_omega x hx
  obtain ⟨-, hPK_le, hPK_card, hPK_exp, huniq⟩ :=
    Case2EightPpSupUnique h.D.F h.D.K P Kp p (F_inf_K_eq_bot_c4 B h.D)
      (F_le_normalizer_K_c4 I B h.D) (F_commute_K_c4 I B h.D h.pre)
      hPF hKp_le hP_omega hKp_omega hPcard hKp_card
  have hAeq : A = P ⊔ Kp := huniq A hAle hAcard hAexp
  have hKp_K0 : Kp ≤ h.D.K0 :=
    omegaPrime_le_of_card_dvd hp inf_le_right hpK0 hKp_card hKp_omega
  rw [hAeq]
  exact sup_le (le_trans hPF le_sup_left) (le_trans hKp_K0 le_sup_right)

/-! ## The two §4 (8) inequalities

These are the only two inputs of §4 (8) that are *not* elementary: Bender's display (8) — the index
bound `|U : B₀ K F(U)| ≤ p` and the dichotomy for `I_U(s) = invSet U s`.  Both are stated at the
`Case2Ctx` level (as the paper's proof requires: the case analysis on `Q = Ω₁(Z₂(O_p(U)))` uses
`S ≤ E(M) ≅ L₂(q)` and the exclusion of `E(M)/Z(E) ≅ A₇`). -/

/-! ## §4 (8) auxiliaries: `A = Ω₁(F ⊔ K₀)`, `A ≤ F(U)`, and `3 ≤ p₀`

These are the elementary part of Bender's (8) which uses no case analysis on `Q`: Bender's (3)
(`SixThree`) and the `Ω₁`-description of `A` (`EightAeqOmega`), together with the observation that
`A = Ω₁(F(U))` — hence `A ⊴ U` — when `F(U) ≤ M`. -/

theorem image_omega1Set_c4 (p : ℕ) (X : Subgroup G) (g : G) :
    MulAut.conj g '' omega1Set p X = omega1Set p (Work.GW2.conjSub g X) := by
  ext y
  constructor
  · rintro ⟨x, hxX, rfl⟩
    obtain ⟨hxX', hxp⟩ := hxX
    refine ⟨?_, ?_⟩
    · rw [Work.GW2.conjSub]
      exact Subgroup.mem_map_of_mem _ hxX'
    · show ((MulAut.conj g : G →* G)) x ^ p = 1
      rw [← map_pow, hxp, map_one]
  · intro hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [Work.GW2.conjSub, Subgroup.mem_map] at hy1
    obtain ⟨x, hxX, rfl⟩ := hy1
    refine ⟨x, ⟨hxX, ?_⟩, rfl⟩
    have h1 : (MulAut.conj g) (x ^ p) = (MulAut.conj g) 1 := by
      simpa [map_pow, map_one] using hy2
    exact (MulAut.conj g).injective h1

/-- `Ω₁` commutes with conjugation: `(Ω₁ p X)^g = Ω₁ p (X^g)`. -/
theorem conjSub_omega1_c4 (p : ℕ) (X : Subgroup G) (g : G) :
    Work.GW2.conjSub g (omega1 p X) = omega1 p (Work.GW2.conjSub g X) := by
  rw [Work.GW2.conjSub, omega1, omega1, MonoidHom.map_closure]
  congr 1
  exact image_omega1Set_c4 p X g

/-- **`A ≤ F(U)`**: `A = Ω₁(F ⊔ K₀)` (`EightAeqOmega`) with `F ≤ F(U)` and `K₀ ≤ F(U)`. -/
theorem A_le_fittingIn_of_ctx (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    (p : ℕ) (P A : Subgroup G) (hp : p.Prime) (hPF : P ≤ h.D.F) (hPcard : Nat.card P = p)
    (hObj : Work.GW2.Case2EightObj h.D p P A) :
    A ≤ Work.GW2.fittingIn B.U := by
  obtain ⟨-, hAeq⟩ := EightAeqOmega I G hbc B h p P A hp hPF hPcard hObj
  rw [hAeq]
  refine le_trans ((Subgroup.closure_le (h.D.F ⊔ Work.GW2.Case2Data.K0 h.D)).mpr ?_) ?_
  · intro x hx; exact hx.1
  · exact sup_le (Work.GW2.Case2Data.F_le_fitting B h.D) inf_le_left

/-- If `F(U) ≤ M` then `A = Ω₁(F(U))`, hence `A ⊴ U`. -/
theorem A_eq_omega1_fittingIn_of_le_M (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    (p : ℕ) (P A : Subgroup G) (hp : p.Prime) (hPF : P ≤ h.D.F) (hPcard : Nat.card P = p)
    (hObj : Work.GW2.Case2EightObj h.D p P A)
    (hFM : Work.GW2.fittingIn B.U ≤ h.D.M) :
    A = omega1 p (Work.GW2.fittingIn B.U) := by
  obtain ⟨-, hAeq⟩ := EightAeqOmega I G hbc B h p P A hp hPF hPcard hObj
  have hSix : Work.GW2.fittingIn B.U = Work.GW2.Case2Data.K0 h.D ⊔ h.D.F := by
    have h := SixThree I G hbc B h.D h.pre
    rw [inf_eq_left.mpr hFM] at h
    simpa [Work.GW2.Case2Data.K0] using h
  rw [hSix, sup_comm]
  exact hAeq

/-- `U` normalizes `Ω₁(F(U))`. -/
theorem conjSub_omega1_fittingIn_eq (B : Work.GW2.BenderSetup G) (p : ℕ) {u : G}
    (hu : u ∈ B.U) :
    Work.GW2.conjSub u (omega1 p (Work.GW2.fittingIn B.U)) =
      omega1 p (Work.GW2.fittingIn B.U) := by
  have hU : Work.GW2.conjSub u B.U = B.U := by
    rw [Work.GW2.conjSub]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hu)
  rw [conjSub_omega1_c4, conjSub_fittingIn, hU]

/-- **Bender's (8), the third conjunct `3 ≤ p₀`**: `F(U) ≤ M` makes `A = Ω₁(F(U)) ⊴ U`, so
`N_U(A) = U` and `p₀ = |U : U ⊓ M|`, odd and `> 1`; otherwise `p₀ ≥ |F(U) : F(U) ⊓ M| > 1`. -/
theorem three_le_p0_of_ctx (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    (p : ℕ) (P A : Subgroup G) (hp : p.Prime) (hPF : P ≤ h.D.F) (hPcard : Nat.card P = p)
    (hObj : Work.GW2.Case2EightObj h.D p P A)
    (hAn : (A.subgroupOf (Work.GW2.fittingIn B.U)).Normal) :
    3 ≤ Work.GW2.Case2EightP0 B P A := by
  have hpne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hPcard
    have hp2 : 2 ≤ p := hp.two_le
    omega
  have hNU : B.U ⊓ Subgroup.normalizer (P : Set G) = B.U ⊓ h.D.M :=
    Case2Eight_NU B (ctx6_of_ctx h) P hPF hpne
  have hMN : B.U ⊓ h.D.M ≤ Subgroup.normalizer (A : Set G) :=
    Case2Eight_le_normalizer_A I B (ctx6_of_ctx h) p P A hObj
  have h4 : B.U ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (A : Set G) := by
    rw [hNU]; exact hMN
  have hp0odd : Odd (Work.GW2.Case2EightP0 B P A) := Case2Eight_odd_p0 B p P A h4
  have hp0eq : Work.GW2.Case2EightP0 B P A =
      (B.U ⊓ h.D.M).relIndex (B.U ⊓ Subgroup.normalizer (A : Set G)) := by
    rw [Work.GW2.Case2EightP0, hNU]
  have relIndex_pos : ∀ H K : Subgroup G, 0 < H.relIndex K := by
    intro H K
    rw [Nat.pos_iff_ne_zero]
    intro h0
    have hcard := Subgroup.relIndex_mul_card H K
    rw [h0, zero_mul] at hcard
    exact Nat.card_pos.ne' hcard.symm
  have hunotM : ¬ B.U ≤ h.D.M := by
    intro hUM
    exact Work.GW2.Case2Pre.not_H_le B h.D h.pre
      ((Work.GW2.Case2Ctx.H_eq_U_sup_S I h).trans_le (sup_le hUM (h.S_le_M)))
  by_cases hFM : Work.GW2.fittingIn B.U ≤ h.D.M
  · have hAeq : A = omega1 p (Work.GW2.fittingIn B.U) :=
      A_eq_omega1_fittingIn_of_le_M I hbc B h p P A hp hPF hPcard hObj hFM
    have hUleN : B.U ≤ Subgroup.normalizer (A : Set G) := by
      intro u hu
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, hAeq]
      exact conjSub_omega1_fittingIn_eq B p hu
    have hp0eq' : Work.GW2.Case2EightP0 B P A = (B.U ⊓ h.D.M).relIndex B.U := by
      rw [hp0eq, inf_eq_left.mpr hUleN]
    rw [hp0eq']
    have hne1 : (B.U ⊓ h.D.M).relIndex B.U ≠ 1 := by
      intro h1
      have hUle : B.U ≤ B.U ⊓ h.D.M :=
        (Subgroup.relIndex_eq_one (H := B.U ⊓ h.D.M) (K := B.U)).mp h1
      exact hunotM (le_trans hUle inf_le_right)
    have hpos : 0 < (B.U ⊓ h.D.M).relIndex B.U := relIndex_pos _ _
    have hgt1 : 1 < (B.U ⊓ h.D.M).relIndex B.U := by omega
    have hodd : Odd ((B.U ⊓ h.D.M).relIndex B.U) :=
      Odd.of_dvd_nat B.U_odd (Subgroup.relIndex_dvd_card (B.U ⊓ h.D.M) B.U)
    obtain ⟨k, hk⟩ := hodd
    omega
  · have hAleFU : A ≤ Work.GW2.fittingIn B.U :=
      A_le_fittingIn_of_ctx I hbc B h p P A hp hPF hPcard hObj
    have hFUleN : Work.GW2.fittingIn B.U ≤ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAleFU).mp hAn
    have hsup : (B.U ⊓ h.D.M) ⊔ Work.GW2.fittingIn B.U ≤
        B.U ⊓ Subgroup.normalizer (A : Set G) :=
      sup_le (le_inf inf_le_left hMN) (le_inf (Subgroup.map_subtype_le _) hFUleN)
    have htower := Subgroup.relIndex_mul_relIndex (H := B.U ⊓ h.D.M)
      (K := (B.U ⊓ h.D.M) ⊔ Work.GW2.fittingIn B.U)
      (L := B.U ⊓ Subgroup.normalizer (A : Set G)) le_sup_left hsup
    have hle : (B.U ⊓ h.D.M).relIndex ((B.U ⊓ h.D.M) ⊔ Work.GW2.fittingIn B.U) ≤
        Work.GW2.Case2EightP0 B P A := by
      rw [hp0eq, ← htower]
      exact Nat.le_mul_of_pos_right _ (relIndex_pos _ _)
    have hne1 : (B.U ⊓ h.D.M).relIndex ((B.U ⊓ h.D.M) ⊔ Work.GW2.fittingIn B.U) ≠ 1 := by
      intro h1
      have hle' : (B.U ⊓ h.D.M) ⊔ Work.GW2.fittingIn B.U ≤ B.U ⊓ h.D.M :=
        (Subgroup.relIndex_eq_one (H := B.U ⊓ h.D.M)
          (K := (B.U ⊓ h.D.M) ⊔ Work.GW2.fittingIn B.U)).mp h1
      exact hFM (le_trans (le_trans le_sup_right hle') inf_le_right)
    have hpos : 0 < (B.U ⊓ h.D.M).relIndex ((B.U ⊓ h.D.M) ⊔ Work.GW2.fittingIn B.U) :=
      relIndex_pos _ _
    have hgt1' : 1 < (B.U ⊓ h.D.M).relIndex ((B.U ⊓ h.D.M) ⊔ Work.GW2.fittingIn B.U) := by
      omega
    have hgt1 : 1 < Work.GW2.Case2EightP0 B P A := lt_of_lt_of_le hgt1' hle
    obtain ⟨k, hk⟩ := hp0odd
    omega

/-- **Bender 1981, §4 (8) (p. 225–226), the index bound `|U : B₀ K F(U)| ≤ p`.** -/
theorem Case2EightIndexOfCtx (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ∀ (p : ℕ) (P : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card P = p →
          (h.D.B0 ⊔ h.D.K ⊔ Work.GW2.fittingIn B.U).relIndex B.U ≤ p := by
  sorry

/-! ## The three §4 (8) facts in the excluded-exception case

Bender's exceptional clause `I_U(s) ⊴ Ĥ` (`Case2InvNormal`) does not occur — this is
`Work.CORE4.not_Case2InvNormal_of_ctx` (`Submission.Work.CORE4.S0CentUO2`), from `S₀ ≤ C_G(U)`
(Bender p. 227) and Lemma 2.8.  So only Bender's cases 1 and 2 of the `Q = Ω₁(Z₂(O_p(U)))`
trichotomy remain, and (8) reads: `u ≤ p`, `A ⊴ F(U)`, and `3 ≤ p₀` whenever `U ⊄ M`. -/

/-- **Bender §4 (8), case 1/2: `u = |U : N_U(A)| ≤ p`** (for the excluded exception). -/
theorem CtxDisjULeP (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ¬ Work.GW2.Case2InvNormal B h.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj h.D p P A →
          Work.GW2.Case2EightU B A ≤ p := by
  sorry

/-- **`A` is a `p`-group** (`|A| = p ^ 2`). -/
theorem A_isPGroup_of_ctx (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    (p : ℕ) (P A : Subgroup G) (hObj : Work.GW2.Case2EightObj h.D p P A) :
    IsPGroup p ↥A :=
  IsPGroup.of_card (n := 2) hObj.2.2.2.2.1

/-- **`A ≤ O_p(U)`**: `A ≤ F(U)` and `A` is a `p`-group, so every `x ∈ A` generates a
`p`-subgroup of the nilpotent `F(U)`, and a `p`-element of `F(U)` lies in `O_p(U)`
(`EightANF_pCoreIn_of_isPGroup_zpowers_of_mem_fittingIn`, proved in
`Submission.Work.CORE4.EightAnormalFitting_of_pcore`). -/
theorem A_le_pCoreIn_of_ctx (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    (p : ℕ) (P A : Subgroup G) (hp : p.Prime) (hPF : P ≤ h.D.F) (hPcard : Nat.card P = p)
    (hObj : Work.GW2.Case2EightObj h.D p P A) :
    A ≤ Work.GW2.pCoreIn p B.U := by
  intro x hx
  exact EightANF_pCoreIn_of_isPGroup_zpowers_of_mem_fittingIn B.U p hp
    (A_le_fittingIn_of_ctx I hbc B h p P A hp hPF hPcard hObj hx)
    ((A_isPGroup_of_ctx B h p P A hObj).to_le (Subgroup.zpowers_le.mpr hx))

/-- **Bender §4 (8), the object-layer input**: `A ⊴ O_p(U)` unless `I_U(s) ⊴ Ĥ` (cases 1–2 of
the trichotomy on `Q = Ω₁(Z₂(O_p(U)))`; case 3 is the excluded exception).  This is the single
deep input of the `A ⊴ F(U)` clause; it is the statement proved in
`Submission.Work.CORE4.APcoreCtx` (`Work.CORE4.APcoreCtx`). -/
theorem CtxAPcore (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ¬ Work.GW2.Case2InvNormal B h.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj h.D p P A →
          (A.subgroupOf (Work.GW2.pCoreIn p B.U)).Normal := by
  sorry

/-- **Bender §4 (8), case 1/2: `A ⊴ F(U)`** (for the excluded exception).  Route: `A ⊴ O_p(U)`
(the object-layer input `CtxAPcore`), `A ≤ F(U)`, `A` a `p`-group, and `O_p(U)` is the Sylow
`p`-subgroup of the nilpotent `F(U)`
(`EightAnormalFitting_of_pcore`, proved in `Submission.Work.CORE4.EightAnormalFitting_of_pcore`);
the `p'`-part of `F(U)` centralizes `O_p(U)`, hence normalizes `A`. -/
theorem CtxDisjANormal (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ¬ Work.GW2.Case2InvNormal B h.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj h.D p P A →
          (A.subgroupOf (Work.GW2.fittingIn B.U)).Normal := by
  intro G _ _ hbc B h hInv p P A hp hPF hPcard hObj
  exact EightAnormalFitting_of_pcore p hp A
    (A_le_fittingIn_of_ctx I hbc B h p P A hp hPF hPcard hObj)
    (A_isPGroup_of_ctx B h p P A hObj)
    (A_le_pCoreIn_of_ctx I hbc B h p P A hp hPF hPcard hObj)
    (CtxAPcore I G hbc B h hInv p P A hp hPF hPcard hObj)

/-- **Bender §4 (8), case 1/2: `3 ≤ p₀ = |N_U(A) : N_U(P)|`** (for the excluded exception).  This is
`three_le_p0_of_ctx` applied to `A ⊴ F(U)`. -/
theorem CtxDisjP0Three (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ¬ Work.GW2.Case2InvNormal B h.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj h.D p P A →
          (¬ B.U ≤ h.D.M → 3 ≤ Work.GW2.Case2EightP0 B P A) := by
  intro G _ _ hbc B h hInv p P A hp hPF hPcard hObj _
  exact three_le_p0_of_ctx I hbc B h p P A hp hPF hPcard hObj
    (CtxDisjANormal I G hbc B h hInv p P A hp hPF hPcard hObj)

/-- **Bender 1981, §4 (8) (p. 225–226), the dichotomy**: `I_U(s) ⊲ Ĥ`, or `u ≤ p` and `A ⊴ F(U)`
(and `3 ≤ p₀` whenever `U ⊄ M`). -/
theorem Case2EightDisjOfCtx (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj h.D p P A →
          (Work.GW2.Case2InvNormal B h.D ∨
            (Work.GW2.Case2EightU B A ≤ p ∧
              (A.subgroupOf (Work.GW2.fittingIn B.U)).Normal ∧
              (¬ B.U ≤ h.D.M → 3 ≤ Work.GW2.Case2EightP0 B P A))) := by
  intro G _ _ hbc B h p P A hp hPF hPcard hObj
  have hInv : ¬ Work.GW2.Case2InvNormal B h.D := not_Case2InvNormal_of_ctx I hbc h
  exact Or.inr ⟨CtxDisjULeP I G hbc B h hInv p P A hp hPF hPcard hObj,
    CtxDisjANormal I G hbc B h hInv p P A hp hPF hPcard hObj,
    fun hUM => CtxDisjP0Three I G hbc B h hInv p P A hp hPF hPcard hObj hUM⟩

/-! ## Assembly of §4 (8) at the `Case2Ctx` level -/

/-- Everything in `Case2EightFacts` except the last disjunction: `p ∣ |K₀|`, `A ≤ F ⊔ K₀`,
`N_U(P) = U ⊓ M`, `N_U(P) ≤ N_G(A)`, `Odd p₀`, `p₀ ≤ p₁ ≤ p + 1`, `p₀ ≤ p`. -/
theorem ctxEightElemFacts (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) :
    ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card P = p →
      Work.GW2.Case2EightObj h.D p P A →
      (p ∣ Nat.card ↥h.D.K0 ∧ A ≤ h.D.F ⊔ h.D.K0 ∧
        B.U ⊓ Subgroup.normalizer (P : Set G) = B.U ⊓ h.D.M ∧
        B.U ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (A : Set G) ∧
        Odd (Work.GW2.Case2EightP0 B P A) ∧
        Work.GW2.Case2EightP0 B P A ≤ Work.GW2.Case2EightP1 P A ∧
        Work.GW2.Case2EightP1 P A ≤ p + 1 ∧
        Work.GW2.Case2EightP0 B P A ≤ p) := by
  intro p P A hp hPF hPcard hObj
  have hAle : A ≤ h.D.F ⊔ h.D.K := hObj.2.2.2.1
  have hPA : P ≤ A := hObj.2.2.2.2.2.2.1
  have hpne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hPcard
    have hp2 : 2 ≤ p := hp.two_le
    omega
  have hNU : B.U ⊓ Subgroup.normalizer (P : Set G) = B.U ⊓ h.D.M :=
    Case2Eight_NU B (ctx6_of_ctx h) P hPF hpne
  have h4 : B.U ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (A : Set G) := by
    rw [hNU]; exact Case2Eight_le_normalizer_A I B (ctx6_of_ctx h) p P A hObj
  have hp0odd : Odd (Work.GW2.Case2EightP0 B P A) := Case2Eight_odd_p0 B p P A h4
  have h6a : Work.GW2.Case2EightP0 B P A ≤ Work.GW2.Case2EightP1 P A :=
    Case2EightP0LeP1 B p P A hPA h4
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := Case2Eight_A_comm I B (ctx6_of_ctx h) A hAle
  have h6b : Work.GW2.Case2EightP1 P A ≤ p + 1 :=
    Case2EightP1Le p P A hp hPA hObj.2.2.2.2.1 hObj.2.2.2.2.2.1 hAcomm hPcard
  have hpodd : Odd p := by
    have h1 : p ∣ Nat.card ↥h.D.F := by
      rw [← hPcard]; exact Subgroup.card_dvd_of_le hPF
    exact Odd.of_dvd_nat B.U_odd (h1.trans (Subgroup.card_dvd_of_le (h.D.F_le_U B)))
  exact ⟨dvd_card_K0_of_ctx I hbc B h hp hPF hPcard, ctxA_le_FsupK0 I hbc B h p P A hp hPF
    hPcard hObj, hNU, h4, hp0odd, h6a, h6b, Case2Eight_p0_le_p B p P A hp0odd h6a h6b hpodd⟩

/-- **Bender 1981, §4 (8) (pp. 225–226) at the `Case2Ctx` level**: for every prime-order `P ≤ F`, the
objects (`A` the unique `(p,p)`-subgroup of `F ⊔ K` containing `P`) exist and the inequalities hold.

This is the `hEight` input of `Work.CORE4.Case2Numeric_of_leaves`.  Its inputs are all available:
`Case2Ctx.toCase2` (`Case2 B` is `h.D`'s own data), `Case2Ctx.toCtx6`, `Case2PrePlusOfCtx`
(Bender's (1),(2) for this `B`), Bender's §4 (7) facts assembled in
`Submission.Work.CORE4.Case2Numeric` (`Case2SevenFacts_of_pieces`, using the (6)-witness from
`Case2SixEmbed`), the `(p,p)`-object existence from `Case2EightObjExists`, and the index bound
`Case2EightIndex9`.  Note that `Case2Ctx` (unlike `Case2Ctx6`) carries §4 (9) `S ≤ E(M)` and the
exclusion of `E(M)/Z(E) ≅ A₇`, which is what the §4 (8) trichotomy on
`Q = Ω₁(Z₂(O_p(U)))` (see `Submission.Work.CORE4.EightIdxDefs`) needs. -/
theorem Case2EightAllOfCtx (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        Work.GW2.Case2EightAll B h.D := by
  intro G _ _ hbc B h p P hp hPF hPcard
  obtain ⟨A, hObj⟩ := ctxObjExists I hbc B h p P hp hPF hPcard
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    ctxEightElemFacts I hbc B h p P A hp hPF hPcard hObj
  exact ⟨A, hObj, h1, h2, h3, h4, h5, h6, h7, h8,
    Case2EightIndexOfCtx I G hbc B h p P hp hPF hPcard,
    Case2EightDisjOfCtx I G hbc B h p P A hp hPF hPcard hObj⟩

end Work.CORE4
