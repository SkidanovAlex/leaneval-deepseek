import Mathlib
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.API
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.EightULeP
import Submission.Work.CORE4.Case2DisjULeP
import Submission.Work.CORE4.Case2DisjANormal
import Submission.Work.CORE4.EightAnormalPcore
import Submission.Work.CORE4.EightAnormalPcore_of_Qpos
import Submission.Work.CORE4.EightAnormalFitting_of_pcore
import Submission.Work.CORE4.Case2EightDisjOfCtx
import Submission.Work.CORE4.EightAeqOmega
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2Eight
import Submission.Work.CORE4.Case2EightQfacts

namespace Work.CORE4

open Work.GW2 Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## The `Case2Ctx6`-level ports needed for the dichotomy

Everything below the target is a verbatim port of a lemma that already exists at the `Case2Ctx`
level (`EightAeqOmega`, `A_eq_omega1_fittingIn_of_le_M`, `three_le_p0_of_not_invNormal`) to the
weaker bundle `Case2Ctx6`, which is `Case2Ctx` with the two §4 (9) fields (`notA7`, `nine`)
deleted.  None of those proofs uses §4 (9): their only inputs are `Case2Pre`, `F_ti` and
`F_cyclic`. -/

/-- Port of `Work.CORE4.EightAeqOmega` to `Case2Ctx6`: the `(p,p)`-subgroup `A ≤ F ⊔ K` of
`Case2EightObj` is exactly `Asub D p = Ω₁(F ⊔ K)`, and also `Ω₁(F ⊔ K₀)`. -/
theorem EightAeqOmegaCtx6_c4 (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ C.D.F → Nat.card ↥P = p →
          Work.GW2.Case2EightObj C.D p P A →
          A = Work.CORE4.Asub C.D p ∧
            A = Work.CORE4.omega1 p (C.D.F ⊔ Work.GW2.Case2Data.K0 C.D) := by
  intro G _ _ hbc B C p P A hp hPF hPcard hObj
  obtain ⟨-, -, -, hAle, hAcard, hAexp, -, _⟩ := hObj
  -- `p ∣ |F|`, `p ∣ |K₀|` (Bender's (6)), `p ∣ |K|`
  have hpF : p ∣ Nat.card ↥C.D.F := by
    rw [← hPcard]; exact Subgroup.card_dvd_of_le hPF
  have hFdvdK0 : Nat.card ↥C.D.F ∣ Nat.card ↥C.D.K0 :=
    Case2SixEmbed I G hbc B C
  have hpK0 : p ∣ Nat.card ↥C.D.K0 := hpF.trans hFdvdK0
  have hpK : p ∣ Nat.card ↥C.D.K := hpK0.trans (Subgroup.card_dvd_of_le inf_le_right)
  -- the `p`-torsion subgroups of `K` and `F`
  obtain ⟨Kp, hKp_le, hKp_card, hKp_omega⟩ :=
    CyclicOmegaPrime C.D.K p C.pre.K_cyclic hp hpK
  obtain ⟨Fp, hFp_le, hFp_card, hFp_omega⟩ :=
    CyclicOmegaPrime C.D.F p C.F_cyclic hp hpF
  have hP_le_Fp : P ≤ Fp := fun x hx =>
    (hFp_omega x (hPF hx)).mp (pow_eq_one_of_card_eq hPcard hx)
  have hPFp : P = Fp :=
    Subgroup.eq_of_le_of_card_ge hP_le_Fp (by rw [hFp_card, hPcard])
  have hP_omega : ∀ x ∈ C.D.F, x ^ p = 1 ↔ x ∈ P := by
    intro x hx; rw [hPFp]; exact hFp_omega x hx
  obtain ⟨-, -, -, -, hpuniq⟩ :=
    Case2EightPpSupUnique C.D.F C.D.K P Kp p (F_inf_K_eq_bot_c4 B C.D)
      (F_le_normalizer_K_c4 I B C.D) (F_commute_K_c4 I B C.D C.pre)
      hPF hKp_le hP_omega hKp_omega hPcard hKp_card
  -- `A = P ⊔ Kp = Fp ⊔ Kp`
  have hAeq : A = P ⊔ Kp := hpuniq A hAle hAcard hAexp
  -- `Ω₁(F ⊔ K) = Fp ⊔ Kp`
  have hOmega : omega1 p (C.D.F ⊔ C.D.K) = Fp ⊔ Kp :=
    omega1_sup_eq_torsion (F_inf_K_eq_bot_c4 B C.D) (F_le_normalizer_K_c4 I B C.D)
      (F_commute_K_c4 I B C.D C.pre) hFp_le hKp_le hFp_omega hKp_omega
  -- the `p`-torsion of `K` lies in `K₀`, hence `A ≤ F ⊔ K₀`
  have hKp_K0 : Kp ≤ C.D.K0 :=
    omegaPrime_le_of_card_dvd hp inf_le_right hpK0 hKp_card hKp_omega
  have hAleK0 : A ≤ C.D.F ⊔ C.D.K0 := by
    rw [hAeq]
    exact sup_le (le_trans hPF le_sup_left) (le_trans hKp_K0 le_sup_right)
  -- first conjunct: `A = Asub D p = Ω₁(F ⊔ K)`
  have hAsub : A = Asub C.D p := by
    show A = omega1 p (C.D.F ⊔ C.D.K)
    rw [hOmega, ← hPFp]
    exact hAeq
  refine ⟨hAsub, ?_⟩
  -- second conjunct: `A = Ω₁(F ⊔ K₀)`
  apply le_antisymm
  · intro x hx
    show x ∈ Subgroup.closure (omega1Set p (C.D.F ⊔ C.D.K0))
    exact Subgroup.subset_closure ⟨hAleK0 hx, hAexp x hx⟩
  · calc omega1 p (C.D.F ⊔ C.D.K0) ≤ omega1 p (C.D.F ⊔ C.D.K) :=
          omega1_mono (sup_le_sup le_rfl inf_le_right)
      _ = A := by rw [hOmega, ← hPFp]; exact hAeq.symm

/-- Port of `Work.CORE4.A_eq_omega1_fittingIn_of_le_M` to `Case2Ctx6`: if `F(U) ≤ M` then
`A = Ω₁(F(U))`. -/
theorem A_eq_omega1_fittingIn_of_le_M_ctx6 (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B)
    (p : ℕ) (P A : Subgroup G) (hp : p.Prime) (hPF : P ≤ C.D.F) (hPcard : Nat.card P = p)
    (hObj : Work.GW2.Case2EightObj C.D p P A)
    (hFM : Work.GW2.fittingIn B.U ≤ C.D.M) :
    A = omega1 p (Work.GW2.fittingIn B.U) := by
  obtain ⟨-, hAeq⟩ := EightAeqOmegaCtx6_c4 I G hbc B C p P A hp hPF hPcard hObj
  have hSix : Work.GW2.fittingIn B.U = Work.GW2.Case2Data.K0 C.D ⊔ C.D.F := by
    have h := SixThree I G hbc B C.D C.pre
    rw [inf_eq_left.mpr hFM] at h
    simpa [Work.GW2.Case2Data.K0] using h
  rw [hSix, sup_comm]
  exact hAeq

/-- Port of `Work.CORE4.three_le_p0_of_not_invNormal` to `Case2Ctx6`: `3 ≤ p₀` from
`A ≤ F(U)`, `A ⊴ F(U)` and `U ⊄ M`.  (The original derives `U ⊄ M` from `H ⊄ M`, `H = US` and
`S ≤ M`, all of which need §4 (9); here `U ⊄ M` is taken as a hypothesis, which is exactly the
antecedent supplied by the dichotomy.) -/
theorem three_le_p0_of_not_invNormal_ctx6 (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B)
    (p : ℕ) (P A : Subgroup G) (hp : p.Prime) (hPF : P ≤ C.D.F) (hPcard : Nat.card P = p)
    (hObj : Work.GW2.Case2EightObj C.D p P A)
    (hAle : A ≤ Work.GW2.fittingIn B.U)
    (hAn : (A.subgroupOf (Work.GW2.fittingIn B.U)).Normal)
    (hunotM : ¬ B.U ≤ C.D.M) :
    3 ≤ Work.GW2.Case2EightP0 B P A := by
  -- elementary §4 (8) reductions
  have hpne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hPcard
    have hp2 : 2 ≤ p := hp.two_le
    omega
  have hNU : B.U ⊓ Subgroup.normalizer (P : Set G) = B.U ⊓ C.D.M :=
    Case2Eight_NU B C P hPF hpne
  have hMN : B.U ⊓ C.D.M ≤ Subgroup.normalizer (A : Set G) :=
    Case2Eight_le_normalizer_A I B C p P A hObj
  have h4 : B.U ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (A : Set G) := by
    rw [hNU]; exact hMN
  have hp0odd : Odd (Work.GW2.Case2EightP0 B P A) := Case2Eight_odd_p0 B p P A h4
  have hp0eq : Work.GW2.Case2EightP0 B P A =
      (B.U ⊓ C.D.M).relIndex (B.U ⊓ Subgroup.normalizer (A : Set G)) := by
    rw [Work.GW2.Case2EightP0, hNU]
  have relIndex_pos : ∀ H K : Subgroup G, 0 < H.relIndex K := by
    intro H K
    rw [Nat.pos_iff_ne_zero]
    intro h0
    have hcard := Subgroup.relIndex_mul_card H K
    rw [h0, zero_mul] at hcard
    exact Nat.card_pos.ne' hcard.symm
  by_cases hFM : Work.GW2.fittingIn B.U ≤ C.D.M
  · -- ### Case (a): `F(U) ≤ M`
    have hAeq : A = omega1 p (Work.GW2.fittingIn B.U) :=
      A_eq_omega1_fittingIn_of_le_M_ctx6 I hbc B C p P A hp hPF hPcard hObj hFM
    have hUleN : B.U ≤ Subgroup.normalizer (A : Set G) := by
      intro u hu
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, hAeq]
      exact conjSub_omega1_fittingIn_eq B p hu
    have hp0eq' : Work.GW2.Case2EightP0 B P A = (B.U ⊓ C.D.M).relIndex B.U := by
      rw [hp0eq, inf_eq_left.mpr hUleN]
    rw [hp0eq']
    have hne1 : (B.U ⊓ C.D.M).relIndex B.U ≠ 1 := by
      intro h1
      have hUle : B.U ≤ B.U ⊓ C.D.M :=
        (Subgroup.relIndex_eq_one (H := B.U ⊓ C.D.M) (K := B.U)).mp h1
      exact hunotM (le_trans hUle inf_le_right)
    have hpos : 0 < (B.U ⊓ C.D.M).relIndex B.U := relIndex_pos _ _
    have hgt1 : 1 < (B.U ⊓ C.D.M).relIndex B.U := by omega
    have hodd : Odd ((B.U ⊓ C.D.M).relIndex B.U) :=
      Odd.of_dvd_nat B.U_odd (Subgroup.relIndex_dvd_card (B.U ⊓ C.D.M) B.U)
    obtain ⟨k, hk⟩ := hodd
    omega
  · -- ### Case (b): `F(U) ⊄ M`
    have hFUleN : Work.GW2.fittingIn B.U ≤ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAle).mp hAn
    have hsup : (B.U ⊓ C.D.M) ⊔ Work.GW2.fittingIn B.U ≤
        B.U ⊓ Subgroup.normalizer (A : Set G) :=
      sup_le (le_inf inf_le_left hMN) (le_inf (Subgroup.map_subtype_le _) hFUleN)
    have htower := Subgroup.relIndex_mul_relIndex (H := B.U ⊓ C.D.M)
      (K := (B.U ⊓ C.D.M) ⊔ Work.GW2.fittingIn B.U)
      (L := B.U ⊓ Subgroup.normalizer (A : Set G)) le_sup_left hsup
    have hle : (B.U ⊓ C.D.M).relIndex ((B.U ⊓ C.D.M) ⊔ Work.GW2.fittingIn B.U) ≤
        Work.GW2.Case2EightP0 B P A := by
      rw [hp0eq, ← htower]
      exact Nat.le_mul_of_pos_right _ (relIndex_pos _ _)
    have hne1 : (B.U ⊓ C.D.M).relIndex ((B.U ⊓ C.D.M) ⊔ Work.GW2.fittingIn B.U) ≠ 1 := by
      intro h1
      have hle' : (B.U ⊓ C.D.M) ⊔ Work.GW2.fittingIn B.U ≤ B.U ⊓ C.D.M :=
        (Subgroup.relIndex_eq_one (H := B.U ⊓ C.D.M)
          (K := (B.U ⊓ C.D.M) ⊔ Work.GW2.fittingIn B.U)).mp h1
      exact hFM (le_trans (le_trans le_sup_right hle') inf_le_right)
    have hpos : 0 < (B.U ⊓ C.D.M).relIndex ((B.U ⊓ C.D.M) ⊔ Work.GW2.fittingIn B.U) :=
      relIndex_pos _ _
    have hgt1' : 1 < (B.U ⊓ C.D.M).relIndex ((B.U ⊓ C.D.M) ⊔ Work.GW2.fittingIn B.U) := by
      omega
    have hgt1 : 1 < Work.GW2.Case2EightP0 B P A := lt_of_lt_of_le hgt1' hle
    obtain ⟨k, hk⟩ := hp0odd
    omega

/-- Bender 1981, §4 (8) (p. 226), the **repaired** dichotomy: with the position of `A` in
`Q := Qsub p B = Ω₁(Z₂(O_p(U)))` supplied as a hypothesis (Bender's trichotomy cases 1–2), the
three conclusions `u ≤ p`, `A ⊴ F(U)`, `3 ≤ p₀` all follow at the `Case2Ctx6` level.

This is the honest conditional form of `Work.CORE4.Case2EightExcept` (whose unconditional form is
recorded as under-hypothesised — the recorded hypotheses bound neither `|Q|` nor the position of
`A` inside `Z₂(O_p(U))`).  See `CORE4/NOTES_CASE2NUMERIC.md` §2/§4: the missing input is exactly
the position datum `A ≤ Q ∧ (A = Q ∨ Z(Q) < A < Q ∧ |Q : A| = p)`.

Route (all pieces are machine-checked already, at the `Case2Ctx` level; only the port to
`Case2Ctx6` is needed — none of them uses §4 (9) beyond the hypotheses recorded here):
* `u ≤ p`: `Case2DisjULeP_of_Qpos` (case `A = Q`: `U ≤ N_G(Q)` gives `u = 1`; case
  `Z(Q) < A < Q`, `A.relIndex Q = p`: `eightU_le_p_of_case2`, using `ConjSubOrbitNcard` and
  `ncard_subgroups_prime_cube`);
* `A ⊴ F(U)`: `ANormalPCoreIn_of_Qsub` + `EightAnormalFitting_of_pcore` (or `Case2DisjANormal`);
* `3 ≤ p₀`: `three_le_p0_of_not_invNormal`, whose only configuration-specific input is the
  antecedent `¬ B.U ≤ C.D.M`, hence the implication here.

`¬ Case2InvNormal B C.D` is carried for documentation (it is the exclusion of the third branch of
Bender's trichotomy); it may go unused.  The result must be sorry-free: `#print axioms
Work.CORE4.EightDichotomyOfTrich` must print `[propext, Classical.choice, Quot.sound]` only — in
particular it must not cite the `sorry`-backed `Case2DisjULeP`, `Case2DisjANormal`, `APcoreCtx`
or `EightTrichOfCtx`, but may cite their *proved* bodies (`Case2DisjULeP_of_Qpos`,
`eightU_le_p_of_case2`, `three_le_p0_of_not_invNormal`, `EightAnormalPcore_of_Qpos`, …). -/
theorem EightDichotomyOfTrich (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case2 B → ∀ C : Work.GW2.Case2Ctx6 B, Work.GW2.Case2PrePlus B C.D →
        Work.GW2.Case2SevenFacts B C.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ C.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj C.D p P A →
          ¬ Work.GW2.Case2InvNormal B C.D →
          (A ≤ Work.CORE4.Qsub p B ∧
            (A = Work.CORE4.Qsub p B ∨
              (Work.CORE4.centerIn (Work.CORE4.Qsub p B) < A ∧ A < Work.CORE4.Qsub p B ∧
                A.relIndex (Work.CORE4.Qsub p B) = p))) →
          (Work.GW2.Case2EightU B A ≤ p ∧
            (A.subgroupOf (Work.GW2.fittingIn B.U)).Normal ∧
            (¬ B.U ≤ C.D.M → 3 ≤ Work.GW2.Case2EightP0 B P A)) := by
  intro G _ _ hbc B _h2 C _hplus _h7 p P A hp hPF hPcard hObj _hInv hpos
  obtain ⟨hAQ, hpos'⟩ := hpos
  -- `p` is odd: `p ∣ |F| ∣ |U|` and `|U|` is odd
  have hpodd : Odd p := by
    have h1 : p ∣ Nat.card ↥C.D.F := by
      rw [← hPcard]; exact Subgroup.card_dvd_of_le hPF
    exact Odd.of_dvd_nat B.U_odd
      (h1.trans (Subgroup.card_dvd_of_le (Work.GW2.Case2Data.F_le_U B C.D)))
  -- the two `Q`-facts: `U ≤ N_G(Q)` and `Q` has exponent `p`
  have hQN : B.U ≤ Subgroup.normalizer ((Qsub p B : Subgroup G) : Set G) :=
    U_le_normalizer_Qsub_c4 p B
  have hQexp : ∀ x ∈ Qsub p B, x ^ p = 1 := Qsub_pow_eq_one_c4 p B hpodd
  -- `A ⊴ O_p(U)` from the position of `A` in `Q` (Bender's cases 1–2)
  have hAnOp : (A.subgroupOf (Work.GW2.pCoreIn p B.U)).Normal :=
    EightAnormalPcore_of_Qpos p hp A hAQ
      (hpos'.elim Or.inl fun hh => Or.inr hh.1)
  -- `A ≤ O_p(U) ≤ F(U)`
  have hAleOp : A ≤ Work.GW2.pCoreIn p B.U :=
    hAQ.trans (omega1_z2_le_self p _)
  have hAleFU : A ≤ Work.GW2.fittingIn B.U := hAleOp.trans (pCoreIn_le_fittingIn B.U hp)
  have hAp : IsPGroup p ↥A := IsPGroup.of_card (n := 2) hObj.2.2.2.2.1
  -- `A ⊴ F(U)`
  have hAnF : (A.subgroupOf (Work.GW2.fittingIn B.U)).Normal :=
    EightAnormalFitting_of_pcore (B := B) p hp A hAleFU hAp hAleOp hAnOp
  refine ⟨?_, hAnF, fun hunotM => ?_⟩
  · -- `u ≤ p`
    rcases hpos' with hAeq | ⟨hZlt, _hAlt, hidx⟩
    · -- case 1: `A = Q` is characteristic in `U`, so `u = 1`
      have hUleN : B.U ≤ Subgroup.normalizer (A : Set G) := by
        rw [hAeq]; exact hQN
      have hu : Work.GW2.Case2EightU B A = 1 := by
        rw [Work.GW2.Case2EightU, inf_eq_left.mpr hUleN, Subgroup.relIndex_self]
      rw [hu]
      exact hp.one_le
    · -- case 2: the orbit count `Work.CORE4.eightU_le_p_of_case2`
      exact eightU_le_p_of_case2 B hp hpodd hQN hAQ hZlt hObj.2.2.2.2.1 hidx hQexp
  · -- `3 ≤ p₀`
    exact three_le_p0_of_not_invNormal_ctx6 I hbc B C p P A hp hPF hPcard hObj hAleFU hAnF hunotM

end Work.CORE4
