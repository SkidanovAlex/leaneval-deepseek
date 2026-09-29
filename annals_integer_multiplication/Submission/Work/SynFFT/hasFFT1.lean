import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.dft1Math
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.fft1.stepKit
import Submission.Work.SynFFT.fft1.fft1Arith
import Submission.Work.SynFFT.fft1.levelsAdd
import Submission.Work.SynFFT.fft1.fftN_eq_dftN
import Submission.Work.SynFFT.fft1.updLvl
import Submission.Work.SynFFT.fft1.updMrg
import Submission.Work.SynFFT.fft1.transProg
import Submission.Work.SynFFT.fft1.postProg
import Submission.Work.SynFFT.fft1.preProg

/-!
# `HasFFT1`: the slice word of the synthetic FFT (paper Lemma 3.2, Prop. 3.3)
-/

set_option autoImplicit false
set_option maxHeartbeats 20000000

namespace Work.SynFFT

open HvdH
open Work.SynFFT.MrgKit
open Work.SynFFT.Fft1Kit

local infixl:68 " ;;; " => HvdH.Cmd.seq

/-- Size of the data list `ofList (cvecs ws)` for an array of `t` coefficient vectors. -/
theorem cvecs_bound (p r t : ℕ) (ws : List (List (ℤ × ℤ))) (hws : ws.length = t)
    (h : ∀ w ∈ ws, InDiscVec p r w) :
    vsz (ofList (cvecs ws)) ≤ 14 * (t * (r + 1) * (p + 1)) + 14 := by
  have h1 : vsz (ofList (cvecs ws)) ≤ t * (13 * (r + 1) * (p + 1) + 1) + 1 := by
    refine vsz_ofList_le_of_bound (cvecs ws) (13 * (r + 1) * (p + 1)) t ?_ ?_
    · intro v hv
      simp only [cvecs, List.mem_map] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      exact vsz_cvecVal_le p r w (h w hw).1 (h w hw).2
    · rw [cvecs, List.length_map, hws]
  have h2 : t * (13 * (r + 1) * (p + 1) + 1) + 1 = 13 * (t * (r + 1) * (p + 1)) + t + 1 := by
    ring
  rw [h2] at h1
  have h3 : t ≤ t * (r + 1) * (p + 1) := by
    calc t = t * 1 * 1 := by ring
      _ ≤ t * (r + 1) * (p + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul (le_refl t) (by omega)) (by omega)
  omega

/-- The invariant of the level fold, step `i`. -/
def LInv (r p t k : ℕ) (sgnz : ℤ) (rest : List Val) (u : Arr r) (e : ℝ) (i : ℕ)
    (acc : List Val) : Prop :=
  ∃ ws : List (List (ℤ × ℤ)),
    acc = ofList (cvecs ws) :: .int ((t / 2 ^ i : ℕ) : ℤ) ::
        .int ((Nat.clog 2 (2 * r) - k + i : ℕ) : ℤ) :: .int sgnz ::
        .int (r : ℤ) :: .int (p : ℤ) :: .int (k : ℤ) :: rest ∧
      ws.length = t ∧ (∀ w ∈ ws, InDiscVec p r w) ∧
      ApproxSL p r t ws (levels r sgnz t i u) (e + i)

/-- The invariant of the interleave ("merge") fold, step `i`. -/
def MInv (r p t k : ℕ) (sgnz : ℤ) (rest : List Val) (u : Arr r) (e : ℝ) (i : ℕ)
    (acc : List Val) : Prop :=
  ∃ ws : List (List (ℤ × ℤ)),
    acc = ofList (cvecs ws) :: .int ((2 ^ i : ℕ) : ℤ) :: .int (r : ℤ) :: .int (p : ℤ) ::
        .int sgnz :: .int (k : ℤ) :: rest ∧
      ws.length = t ∧ (∀ w ∈ ws, InDiscVec p r w) ∧
      ApproxSL p r t ws (mrgIterN r i (levels r sgnz t k u)) (e + k)

/-- `seq` for constant costs, with a predicate pre/post (no post-simplification). -/
theorem seqPred {main : Cmd} {p q : Cmd} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {P' : List Val → Prop} {Q' : List Val → List Val → Prop} {c1 c2 : ℕ}
    (hseq : ∀ (P : List Val → Prop) (Q : List Val → List Val → Prop) (C : List Val → ℕ)
      (P' : List Val → Prop) (Q' : List Val → List Val → Prop) (C' Bd : List Val → ℕ),
      WordR main p P Q C → WordR main q P' Q' C' →
      (∀ vs mid, P vs → Q vs mid → P' mid ∧ C' mid ≤ Bd vs) →
      WordR main (p ;;; q) P (fun vs out => ∃ mid, Q vs mid ∧ Q' mid out)
        (fun vs => C vs + Bd vs))
    (h1 : WordR main p P Q (fun _ => c1)) (h2 : WordR main q P' Q' (fun _ => c2))
    (h : ∀ vs mid, P vs → Q vs mid → P' mid) :
    WordR main (p ;;; q) P (fun vs out => ∃ mid, Q vs mid ∧ Q' mid out) (fun _ => c1 + c2) := by
  have := hseq P Q (fun _ => c1) P' Q' (fun _ => c2) (fun _ => c2) h1 h2
    (fun vs mid hvs hmid => ⟨h vs mid hvs hmid, le_rfl⟩)
  simpa using this

theorem hasFFT1 (hk : Work.SynFFT.KLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib)
    (hf : HvdH.FxLib) (hlp : Work.SynFFT.HasLvlPass) (hmp : Work.SynFFT.HasMrgPass)
    (hbr : Work.SynFFT.MrgBitrevProp) : Work.SynFFT.HasFFT1 := by
  obtain ⟨Lprog, KL, hL⟩ := hlp
  obtain ⟨Mprog, KM, hM⟩ := hmp
  obtain ⟨foldC, Kf, hfold⟩ := hk.foldList
  obtain ⟨kdrP, Kdr, hkdr⟩ := hk.drop
  obtain ⟨pickP, Kpk, hpick⟩ := hk.pick
  obtain ⟨pushP, Kpv, hpush⟩ := hk.pushVal
  obtain ⟨repP, Krp, hrep⟩ := hl.replicate
  obtain ⟨preP, Kpre, hpre⟩ := preProg hk hi hl
  obtain ⟨updP, Kupd, hupd⟩ := updLvl hk hi
  obtain ⟨udmP, Kudm, hudm⟩ := updMrg hk hi
  obtain ⟨trP, Ktr, htr⟩ := transProg hk
  obtain ⟨poP, Kpo, hpo⟩ := postProg hk
  refine ⟨preP ;;; foldC (kdrP ;;; Lprog ;;; updP) ;;; trP ;;; pushP (.nil) ;;; pickP 6 ;;;
      repP ;;; foldC (kdrP ;;; Mprog ;;; udmP) ;;; poP,
    1000000 * (KL + KM + Kf + Kdr + Kpk + Kpv + Krp + Kpre + Kupd + Kudm + Ktr + Kpo + 1), ?_⟩
  intro main p r t k sgn ws u e rest hIsPow ht htdvd h2rp hsgn hwlen hInD hApp
  obtain ⟨hAr1, hAr2, hAr3, hAr4, hAr5, hAr6, hAr7, hAr8, hAr9, hAr10⟩ :=
    fft1Arith r k t hIsPow ht htdvd
  have hWsz : vsz (ofList (cvecs ws)) ≤ 14 * (t * (r + 1) * (p + 1)) + 14 :=
    cvecs_bound p r t ws hwlen hInD
  have hir : isz (r : ℤ) ≤ p + 2 := by
    have h : r.size ≤ p := Nat.size_le.mpr (by nlinarith)
    rw [show isz (r : ℤ) = r.size + 2 from rfl]
    omega
  have hip : isz (p : ℤ) ≤ p + 2 := isz_natCast_le p
  have hik : isz (k : ℤ) ≤ k + 2 := isz_natCast_le k
  have hsg : isz sgn = 3 := isz_of_sign hsgn
  have hcrp : Nat.clog 2 (2 * r) ≤ p := by
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    omega
  have h2k : (2 : ℕ) ^ k = t := ht.symm
  have h2kpos : 0 < 2 ^ k := by positivity
  have htdiv : t / 2 ^ k = 1 := by rw [← h2k]; exact Nat.div_self h2kpos
  set S0 : ℕ := t * (r + 1) * (p + 1) with hS0def
  set T : ℕ := S0 * (k + 1) with hTdef
  set Sig : ℕ := KL + KM + Kf + Kdr + Kpk + Kpv + Krp + Kpre + Kupd + Kudm + Ktr + Kpo + 1
    with hSig
  have ht1 : 1 ≤ t := by rw [ht]; have := Nat.lt_two_pow_self (n := k); omega
  have hS0_1 : 1 ≤ S0 := by
    rw [hS0def]
    calc (1 : ℕ) = 1 * 1 * 1 := by ring
      _ ≤ t * (r + 1) * (p + 1) := Nat.mul_le_mul (Nat.mul_le_mul ht1 (by omega)) (by omega)
  have hk1 : 1 ≤ k + 1 := by omega
  have hSK : S0 ≤ S0 * (k + 1) := by
    have h := Nat.mul_le_mul_left S0 hk1
    simpa using h
  have hS0leT : S0 ≤ T := by rw [hTdef]; exact hSK
  have hkk : k ≤ T := by
    rw [hTdef]
    have h1 : k ≤ k + 1 := by omega
    have h2 : 1 * (k + 1) ≤ S0 * (k + 1) := Nat.mul_le_mul_right _ hS0_1
    omega
  have htS0 : t ≤ S0 := by
    rw [hS0def]
    calc t = t * 1 * 1 := by ring
      _ ≤ t * (r + 1) * (p + 1) := Nat.mul_le_mul (Nat.mul_le_mul (le_refl t) (by omega)) (by omega)
  have htt : t ≤ T := by rw [hTdef]; exact le_trans htS0 hSK
  have hpS0 : p ≤ S0 := by
    rw [hS0def]
    calc p ≤ p + 1 := by omega
      _ ≤ 1 * (p + 1) := by omega
      _ ≤ t * (r + 1) * (p + 1) := by
          have h1 : 1 ≤ t * (r + 1) := by
            have h2 : t * 1 ≤ t * (r + 1) := Nat.mul_le_mul_left _ (by omega)
            omega
          calc 1 * (p + 1) = (t * (r + 1)) * (p + 1) * 0 + 1 * (p + 1) := by ring
            _ ≤ (t * (r + 1)) * (p + 1) := by
                have := Nat.mul_le_mul_right (p + 1) h1
                omega
  have hpp : p ≤ T := le_trans hpS0 hS0leT
  have hT1 : 1 ≤ T := by nlinarith [hS0_1, hk1]
  have hWsz' : vsz (ofList (cvecs ws)) ≤ 14 * S0 + 14 := by rw [hS0def]; exact hWsz
  set cL : ℕ := 2 * Kdr + (KL * t * (r + 1) * (p + 1) + KL) + Kupd * (40 * (S0 + 1)) with hcL
  set cM : ℕ := 2 * Kdr + (KM * t * (r + 1) * (p + 1) + KM) + Kudm * (40 * (S0 + 1)) with hcM
  have hclog_le : isz ((Nat.clog 2 (2 * r) : ℕ) : ℤ) ≤ S0 + 2 := by
    have h1 : isz ((Nat.clog 2 (2 * r) : ℕ) : ℤ) ≤ Nat.clog 2 (2 * r) + 2 := isz_natCast_le _
    have h2 : Nat.clog 2 (2 * r) ≤ S0 := le_trans hcrp hpS0
    omega
  have hisz1 : isz (1 : ℤ) = 3 := isz_one
  -- ===================== the level fold step =====================
  have hstepL : ∀ (i : ℕ) (acc : List Val), i < (List.replicate k (Val.nil)).length →
      LInv r p t k sgn rest u e i acc →
      WordR main (kdrP ;;; Lprog ;;; updP)
        (fun vs => vs = (List.replicate k (Val.nil)).getD i .nil :: acc)
        (fun _ out => LInv r p t k sgn rest u e (i + 1) out) (fun _ => cL) := by
    intro i acc hi hacc
    rw [List.length_replicate] at hi
    have hget : (List.replicate k (Val.nil)).getD i .nil = (Val.nil : Val) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hi, Option.getD_some]
    obtain ⟨ws0, hacc_eq, hlen0, hdisc0, happ0⟩ := hacc
    -- 1. drop the driver element
    have h1 : WordR main kdrP (fun vs => vs = .nil :: acc) (fun _ out => out = acc)
        (fun _ => Kdr * (vsz (Val.nil) + 1)) := by
      refine WordR_conseqC (kdropStep (hkdr main) (Val.nil :: acc) (by simp)
        (Kdr * (vsz (Val.nil) + 1)) le_rfl) rfl (fun out hout => by simpa using hout) le_rfl
    -- 2. one level pass
    have h2 : WordR main Lprog (fun vs => vs = acc)
        (fun _ out => ∃ ws' : List (List (ℤ × ℤ)),
          out = ofList (cvecs ws') :: .int ((t / 2 ^ i : ℕ) : ℤ) ::
              .int ((Nat.clog 2 (2 * r) - k + i : ℕ) : ℤ) :: .int sgn ::
              .int (r : ℤ) :: .int (p : ℤ) :: .int (k : ℤ) :: rest ∧
            ws'.length = t ∧ (∀ w ∈ ws', InDiscVec p r w) ∧
            ApproxSL p r t ws' (lvlN r (t / 2 ^ i) sgn (levels r sgn t i u)) (e + i + 1))
        (fun _ => KL * t * (r + 1) * (p + 1) + KL) := by
      rw [hacc_eq]
      exact hL main p r t (t / 2 ^ i) (Nat.clog 2 (2 * r) - k + i) sgn ws0
        (levels r sgn t i u) (e + i) (.int (k : ℤ) :: rest)
        (hAr2 i hi) (hAr5 i hi) (hAr1 i (le_of_lt hi)) hsgn h2rp hlen0 hdisc0 happ0
    -- 3. update the parameters
    have h3 : ∀ (ws' : List (List (ℤ × ℤ))), ws'.length = t →
        (∀ w ∈ ws', InDiscVec p r w) →
        WordR main updP
          (fun vs => vs = ofList (cvecs ws') :: .int ((t / 2 ^ i : ℕ) : ℤ) ::
              .int ((Nat.clog 2 (2 * r) - k + i : ℕ) : ℤ) :: .int sgn ::
              .int (r : ℤ) :: .int (p : ℤ) :: .int (k : ℤ) :: rest)
          (fun _ out => out = ofList (cvecs ws') :: .int (((t / 2 ^ i) / 2 : ℕ) : ℤ) ::
              .int (((Nat.clog 2 (2 * r) - k + i) + 1 : ℕ) : ℤ) :: .int sgn ::
              .int (r : ℤ) :: .int (p : ℤ) :: .int (k : ℤ) :: rest)
          (fun _ => Kupd * (40 * (S0 + 1))) := by
      intro ws' hlen' hdisc'
      refine WordR_conseqC (hupd main (ofList (cvecs ws')) (t / 2 ^ i)
        (Nat.clog 2 (2 * r) - k + i) (.int sgn :: .int (r : ℤ) :: .int (p : ℤ) ::
          .int (k : ℤ) :: rest)
        (Kupd * (40 * (S0 + 1))) ?_) rfl (fun out hout => hout) le_rfl
      have hsz' : vsz (ofList (cvecs ws')) ≤ 14 * S0 + 14 := by
        rw [hS0def]; exact cvecs_bound p r t ws' hlen' hdisc'
      have hm : isz ((t / 2 ^ i : ℕ) : ℤ) ≤ S0 + 2 := by
        have h2' : t / 2 ^ i ≤ t := hAr9 i (le_of_lt hi)
        have h3' : isz ((t / 2 ^ i : ℕ) : ℤ) ≤ (t / 2 ^ i) + 2 := isz_natCast_le _
        rw [hS0def]; nlinarith
      have hs : isz ((Nat.clog 2 (2 * r) - k + i : ℕ) : ℤ) ≤ S0 + 2 := by
        have h4 : Nat.clog 2 (2 * r) - k + i ≤ p := by omega
        have h5 : isz ((Nat.clog 2 (2 * r) - k + i : ℕ) : ℤ) ≤
            (Nat.clog 2 (2 * r) - k + i) + 2 := isz_natCast_le _
        rw [hS0def]; nlinarith
      nlinarith [hsz', hm, hs, hS0_1]
    -- the manual composition
    intro vs0 hvs0 st0 R0 hR0
    rw [hget] at hvs0
    obtain ⟨v1, s1, n1, hQ1, he1, hn1, hstk1, hoth1⟩ := h1 vs0 hvs0 st0 R0 hR0
    obtain ⟨v2, s2, n2, hQ2, he2, hn2, hstk2, hoth2⟩ := h2 v1 hQ1 s1 R0 hstk1
    obtain ⟨ws', hv2, hlen', hdisc', happ'⟩ := hQ2
    obtain ⟨v3, s3, n3, hQ3, he3, hn3, hstk3, hoth3⟩ := h3 ws' hlen' hdisc' v2 hv2 s2 R0 hstk2
    refine ⟨v3, s3, (n1 + n2) + n3, ?_, Eval.seq (Eval.seq he1 he2) he3, ?_, hstk3, ?_⟩
    · -- the invariant
      refine ⟨ws', ?_, hlen', hdisc', ?_⟩
      · rw [hQ3, hAr4 i (le_of_lt hi)]
        have hexp : Nat.clog 2 (2 * r) - k + i + 1 = Nat.clog 2 (2 * r) - k + (i + 1) := by omega
        rw [hexp]
      · have hlev : levels r sgn t (i + 1) u = lvlN r (t / 2 ^ i) sgn (levels r sgn t i u) := by
          rw [levelsAdd r sgn t u i 1]
          rw [show levels r sgn (t / 2 ^ i) 1 (levels r sgn t i u) =
              levels r sgn (t / 2 ^ i / 2) 0
                (lvlN r (t / 2 ^ i) sgn (levels r sgn t i u)) from rfl]
          rw [levels_zero]
        rw [hlev]
        have herr : e + ((i + 1 : ℕ) : ℝ) = e + i + 1 := by push_cast; ring
        rw [herr]
        exact happ'
    · simp only [hcL]
      nlinarith [hn1, hn2, hn3, vsz_nil]
    · intro kk hkk'
      rw [hoth3 kk hkk', hoth2 kk hkk', hoth1 kk hkk']
  -- ===================== the merge fold step =====================
  have hstepM : ∀ (i : ℕ) (acc : List Val), i < (List.replicate k (Val.nil)).length →
      MInv r p t k sgn rest u e i acc →
      WordR main (kdrP ;;; Mprog ;;; udmP)
        (fun vs => vs = (List.replicate k (Val.nil)).getD i .nil :: acc)
        (fun _ out => MInv r p t k sgn rest u e (i + 1) out) (fun _ => cM) := by
    intro i acc hi hacc
    rw [List.length_replicate] at hi
    have hget : (List.replicate k (Val.nil)).getD i .nil = (Val.nil : Val) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hi, Option.getD_some]
    obtain ⟨ws0, hacc_eq, hlen0, hdisc0, happ0⟩ := hacc
    have h1 : WordR main kdrP (fun vs => vs = .nil :: acc) (fun _ out => out = acc)
        (fun _ => Kdr * (vsz (Val.nil) + 1)) := by
      refine WordR_conseqC (kdropStep (hkdr main) (Val.nil :: acc) (by simp)
        (Kdr * (vsz (Val.nil) + 1)) le_rfl) rfl (fun out hout => by simpa using hout) le_rfl
    have h2 : WordR main Mprog (fun vs => vs = acc)
        (fun _ out => ∃ ws' : List (List (ℤ × ℤ)),
          out = ofList (cvecs ws') :: .int ((2 ^ i : ℕ) : ℤ) :: .int (r : ℤ) :: .int (p : ℤ) ::
              .int sgn :: .int (k : ℤ) :: rest ∧
            ws'.length = t ∧ (∀ w ∈ ws', InDiscVec p r w) ∧
            ApproxSL p r t ws' (mrgN r (2 ^ i) (mrgIterN r i (levels r sgn t k u))) (e + k))
        (fun _ => KM * t * (r + 1) * (p + 1) + KM) := by
      rw [hacc_eq]
      exact hM main p r t (2 ^ i) ws0 (mrgIterN r i (levels r sgn t k u)) (e + k)
        (.int sgn :: .int (k : ℤ) :: rest)
        (pow_pos (by norm_num) i) (hAr3 i hi) hlen0 hdisc0 happ0
    have h3 : ∀ (ws' : List (List (ℤ × ℤ))), ws'.length = t →
        (∀ w ∈ ws', InDiscVec p r w) →
        WordR main udmP
          (fun vs => vs = ofList (cvecs ws') :: .int ((2 ^ i : ℕ) : ℤ) :: .int (r : ℤ) ::
              .int (p : ℤ) :: .int sgn :: .int (k : ℤ) :: rest)
          (fun _ out => out = ofList (cvecs ws') :: .int ((2 * 2 ^ i : ℕ) : ℤ) :: .int (r : ℤ) ::
              .int (p : ℤ) :: .int sgn :: .int (k : ℤ) :: rest)
          (fun _ => Kudm * (40 * (S0 + 1))) := by
      intro ws' hlen' hdisc'
      refine WordR_conseqC (hudm main (ofList (cvecs ws')) (2 ^ i)
        (.int (r : ℤ) :: .int (p : ℤ) :: .int sgn :: .int (k : ℤ) :: rest)
        (Kudm * (40 * (S0 + 1))) ?_) rfl (fun out hout => hout) le_rfl
      have hsz' : vsz (ofList (cvecs ws')) ≤ 14 * S0 + 14 := by
        rw [hS0def]; exact cvecs_bound p r t ws' hlen' hdisc'
      have hs : isz ((2 ^ i : ℕ) : ℤ) ≤ S0 + 2 := by
        have h2' : 2 ^ i ≤ t := hAr10 i (le_of_lt hi)
        have h3' : isz ((2 ^ i : ℕ) : ℤ) ≤ 2 ^ i + 2 := isz_natCast_le _
        rw [hS0def]; nlinarith
      nlinarith [hsz', hs, hS0_1]
    intro vs0 hvs0 st0 R0 hR0
    rw [hget] at hvs0
    obtain ⟨v1, s1, n1, hQ1, he1, hn1, hstk1, hoth1⟩ := h1 vs0 hvs0 st0 R0 hR0
    obtain ⟨v2, s2, n2, hQ2, he2, hn2, hstk2, hoth2⟩ := h2 v1 hQ1 s1 R0 hstk1
    obtain ⟨ws', hv2, hlen', hdisc', happ'⟩ := hQ2
    obtain ⟨v3, s3, n3, hQ3, he3, hn3, hstk3, hoth3⟩ := h3 ws' hlen' hdisc' v2 hv2 s2 R0 hstk2
    refine ⟨v3, s3, (n1 + n2) + n3, ?_, Eval.seq (Eval.seq he1 he2) he3, ?_, hstk3, ?_⟩
    · refine ⟨ws', ?_, hlen', hdisc', ?_⟩
      · rw [hQ3]
        have h2i : (2 : ℕ) * 2 ^ i = 2 ^ (i + 1) := by rw [pow_succ']
        rw [h2i]
      · change ApproxSL p r t ws' (mrgIterN r (i + 1) (levels r sgn t k u)) (e + k)
        exact happ'
    · simp only [hcM]
      nlinarith [hn1, hn2, hn3, vsz_nil]
    · intro kk hkk'
      rw [hoth3 kk hkk', hoth2 kk hkk', hoth1 kk hkk']
  -- ===================== the fold-list applications =====================
  have hszL : ∀ x ∈ List.replicate k (Val.nil), vsz x ≤ 1 := by
    intro x hx
    rw [List.mem_replicate] at hx
    rw [hx.2, vsz_nil]
  have hFL := hfold main (kdrP ;;; Lprog ;;; updP) (List.replicate k (Val.nil))
    (LInv r p t k sgn rest u e) cL 1 hszL hstepL
  have hFM := hfold main (kdrP ;;; Mprog ;;; udmP) (List.replicate k (Val.nil))
    (MInv r p t k sgn rest u e) cM 1 hszL hstepM
  -- ===================== prelude =====================
  have hpre0 : WordR main preP
      (fun vs => vs = ofList (cvecs ws) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) ::
        .int (p : ℤ) :: rest)
      (fun _ out => out = ofList (List.replicate k (Val.nil)) :: ofList (cvecs ws) ::
        .int ((2 ^ k : ℕ) : ℤ) :: .int ((Nat.clog 2 (2 * r) - k : ℕ) : ℤ) ::
        .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (k : ℤ) :: rest)
      (fun _ => Kpre * (40 * (T + 1))) :=
    hpre main (ofList (cvecs ws)) k sgn r p rest (Kpre * (40 * (T + 1))) hsgn hAr8 (by
      have hx : vsz (ofList (cvecs ws)) + isz (k : ℤ) + isz (r : ℤ) + isz (p : ℤ) +
          Nat.clog 2 (2 * r) + 2 ^ k + k + 1 ≤ 40 * (T + 1) := by
        rw [hTdef, hS0def]
        nlinarith [hWsz, hik, hir, hip, hcrp, hAr6, hS0def, hTdef]
      nlinarith [hx])
  have hpre1 : WordR main preP
      (fun vs => vs = ofList (cvecs ws) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) ::
        .int (p : ℤ) :: rest)
      (fun _ out => ∃ acc, out = ofList (List.replicate k (Val.nil)) :: acc ∧
        LInv r p t k sgn rest u e 0 acc)
      (fun _ => Kpre * (40 * (T + 1))) := by
    refine WordR_weaken hpre0 (fun vs hvs => hvs) ?_ (fun vs _ => le_rfl)
    intro vs out hvs hout
    refine ⟨ofList (cvecs ws) :: .int ((2 ^ k : ℕ) : ℤ) ::
        .int ((Nat.clog 2 (2 * r) - k : ℕ) : ℤ) ::
        .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (k : ℤ) :: rest, ?_, ?_⟩
    · rw [hout]
    · refine ⟨ws, ?_, hwlen, hInD, ?_⟩
      · simp only [pow_zero, Nat.div_one, Nat.add_zero]
        rw [← h2k]
      · simpa [levels_zero] using hApp
  -- ===================== transition =====================
  have htr1 : ∀ (ws' : List (List (ℤ × ℤ))), ws'.length = t →
      (∀ w ∈ ws', InDiscVec p r w) →
      WordR main trP
        (fun vs => vs = ofList (cvecs ws') :: .int ((t / 2 ^ k : ℕ) : ℤ) ::
            .int ((Nat.clog 2 (2 * r) - k + k : ℕ) : ℤ) :: .int sgn ::
            .int (r : ℤ) :: .int (p : ℤ) :: .int (k : ℤ) :: rest)
        (fun _ out => out = ofList (cvecs ws') :: .int (1 : ℤ) :: .int (r : ℤ) ::
            .int (p : ℤ) :: .int sgn :: .int (k : ℤ) :: rest)
        (fun _ => Ktr * (200 * (T + 1))) := by
    intro ws' hlen' hdisc'
    refine WordR_conseqC (htr main (ofList (cvecs ws')) (t / 2 ^ k) (Nat.clog 2 (2 * r) - k + k)
      sgn r p k rest (Ktr * (200 * (T + 1))) ?_) rfl (fun out hout => hout) le_rfl
    have hsz' : vsz (ofList (cvecs ws')) ≤ 14 * S0 + 14 := by
      rw [hS0def]; exact cvecs_bound p r t ws' hlen' hdisc'
    have hsh : isz ((Nat.clog 2 (2 * r) - k + k : ℕ) : ℤ) ≤ S0 + 2 := by
      have h1 : Nat.clog 2 (2 * r) - k + k ≤ p := by omega
      have h2 : isz ((Nat.clog 2 (2 * r) - k + k : ℕ) : ℤ) ≤
          (Nat.clog 2 (2 * r) - k + k) + 2 := isz_natCast_le _
      rw [hS0def]; nlinarith
    have hm : isz ((t / 2 ^ k : ℕ) : ℤ) ≤ S0 + 2 := by
      have h2 : isz ((t / 2 ^ k : ℕ) : ℤ) ≤ t / 2 ^ k + 2 := isz_natCast_le _
      rw [htdiv, hS0def]; nlinarith
    nlinarith [hsz', hsh, hm, hir, hip, hsg, hisz1, hik, hS0_1, hS0leT, hkk]
  -- ===================== the epilogue =====================
  have hpo1 : ∀ (ws' : List (List (ℤ × ℤ))), ws'.length = t →
      (∀ w ∈ ws', InDiscVec p r w) →
      WordR main poP
        (fun vs => vs = ofList (cvecs ws') :: .int ((2 ^ k : ℕ) : ℤ) :: .int (r : ℤ) ::
            .int (p : ℤ) :: .int sgn :: .int (k : ℤ) :: rest)
        (fun _ out => out = ofList (cvecs ws') :: .int (k : ℤ) :: .int sgn ::
            .int (r : ℤ) :: .int (p : ℤ) :: rest)
        (fun _ => Kpo * (200 * (T + 1))) := by
    intro ws' hlen' hdisc'
    refine WordR_conseqC (hpo main (ofList (cvecs ws')) (2 ^ k) r p k sgn rest
      (Kpo * (200 * (T + 1))) ?_) rfl (fun out hout => hout) le_rfl
    have hsz' : vsz (ofList (cvecs ws')) ≤ 14 * S0 + 14 := by
      rw [hS0def]; exact cvecs_bound p r t ws' hlen' hdisc'
    have h2kv : isz ((2 ^ k : ℕ) : ℤ) ≤ S0 + 2 := by
      have h1 : (2 ^ k : ℕ) ≤ t := by rw [h2k]
      have h2 : isz ((2 ^ k : ℕ) : ℤ) ≤ (2 ^ k : ℕ) + 2 := isz_natCast_le _
      rw [hS0def]; nlinarith
    nlinarith [hsz', h2kv, hir, hip, hsg, hik, hS0_1, hS0leT, hkk]
  -- ===================== assemble =====================
  have hFL' : WordR main (foldC (kdrP ;;; Lprog ;;; updP))
      (fun vs => ∃ acc, vs = ofList (List.replicate k (Val.nil)) :: acc ∧
        LInv r p t k sgn rest u e 0 acc)
      (fun _ out => LInv r p t k sgn rest u e k out)
      (fun _ => k * (cL + Kf * 2) + Kf) := by
    simpa using hFL
  have hFM' : WordR main (foldC (kdrP ;;; Mprog ;;; udmP))
      (fun vs => ∃ acc, vs = ofList (List.replicate k (Val.nil)) :: acc ∧
        MInv r p t k sgn rest u e 0 acc)
      (fun _ out => MInv r p t k sgn rest u e k out)
      (fun _ => k * (cM + Kf * 2) + Kf) := by
    simpa using hFM
  -- cost side conditions for the individual steps
  have hDtr : ∀ (ws' : List (List (ℤ × ℤ))), ws'.length = t →
      (∀ w ∈ ws', InDiscVec p r w) →
      Ktr * (vsz (ofList (cvecs ws')) + isz ((t / 2 ^ k : ℕ) : ℤ) +
        isz (Nat.clog 2 (2 * r) - k + k : ℕ) + isz sgn + isz (r : ℤ) + isz (p : ℤ) +
        isz (k : ℤ) + 1) ≤ Ktr * (200 * (T + 1)) := by
    intro ws' hlen' hdisc'
    have hsz' : vsz (ofList (cvecs ws')) ≤ 14 * S0 + 14 := by
      rw [hS0def]; exact cvecs_bound p r t ws' hlen' hdisc'
    have hsh : isz ((Nat.clog 2 (2 * r) - k + k : ℕ) : ℤ) ≤ S0 + 2 := by
      have h1 : Nat.clog 2 (2 * r) - k + k ≤ p := by omega
      have h2 : isz ((Nat.clog 2 (2 * r) - k + k : ℕ) : ℤ) ≤
          (Nat.clog 2 (2 * r) - k + k) + 2 := isz_natCast_le _
      rw [hS0def]; nlinarith
    have hm : isz ((t / 2 ^ k : ℕ) : ℤ) ≤ S0 + 2 := by
      have h2 : isz ((t / 2 ^ k : ℕ) : ℤ) ≤ t / 2 ^ k + 2 := isz_natCast_le _
      rw [htdiv, hS0def]; nlinarith
    have hsum : vsz (ofList (cvecs ws')) + isz ((t / 2 ^ k : ℕ) : ℤ) +
        isz (Nat.clog 2 (2 * r) - k + k : ℕ) + isz sgn + isz (r : ℤ) + isz (p : ℤ) +
        isz (k : ℤ) + 1 ≤ 200 * (T + 1) := by
      nlinarith [hsz', hsh, hm, hir, hip, hsg, hik, hS0_1, hS0leT, hkk, hpp, htt, hS0def, hTdef]
    exact Nat.mul_le_mul_left _ hsum
  have hDpush : Kpv * (vsz (Val.nil) + 1) ≤ Kpv * (200 * (T + 1)) := by
      rw [vsz_nil]; nlinarith
  have hDrep : ∀ (v3 : List Val), Krp * ((k + 1) * (vsz (Val.nil) + 1) + isz (k : ℤ) + 1) ≤
      Krp * (200 * (T + 1)) := by
    intro v3
    rw [vsz_nil]
    have : (k + 1) * (1 + 1) + isz (k : ℤ) + 1 ≤ 200 * (T + 1) := by
      nlinarith [hik, hkk, hT1, hTdef, hS0def]
    exact Nat.mul_le_mul_left _ this
  have hDpo : ∀ (ws' : List (List (ℤ × ℤ))), ws'.length = t →
      (∀ w ∈ ws', InDiscVec p r w) →
      Kpo * (vsz (ofList (cvecs ws')) + isz ((2 ^ k : ℕ) : ℤ) + isz (r : ℤ) + isz (p : ℤ) +
        isz sgn + isz (k : ℤ) + 1) ≤ Kpo * (200 * (T + 1)) := by
    intro ws' hlen' hdisc'
    have hsz' : vsz (ofList (cvecs ws')) ≤ 14 * S0 + 14 := by
      rw [hS0def]; exact cvecs_bound p r t ws' hlen' hdisc'
    have h2kv : isz ((2 ^ k : ℕ) : ℤ) ≤ S0 + 2 := by
      have h2 : isz ((2 ^ k : ℕ) : ℤ) ≤ (2 ^ k : ℕ) + 2 := isz_natCast_le _
      rw [hS0def]; nlinarith
    have hsum : vsz (ofList (cvecs ws')) + isz ((2 ^ k : ℕ) : ℤ) + isz (r : ℤ) + isz (p : ℤ) +
        isz sgn + isz (k : ℤ) + 1 ≤ 200 * (T + 1) := by
      nlinarith [hsz', h2kv, hir, hip, hsg, hik, hS0_1, hS0leT, hkk, hpp, htt, hS0def, hTdef]
    exact Nat.mul_le_mul_left _ hsum
  -- the manual chain
  intro vs0 hvs0 st0 R0 hR0
  -- (1) prelude
  obtain ⟨v1, s1, n1, hQ1, he1, hn1, hstk1, hoth1⟩ := hpre1 vs0 hvs0 st0 R0 hR0
  -- (2) level fold
  obtain ⟨v2, s2, n2, hQ2, he2, hn2, hstk2, hoth2⟩ :=
    hFL' v1 hQ1 s1 R0 hstk1
  obtain ⟨ws2, hstate2, hlen2, hdisc2, happ2⟩ := hQ2
  -- (3) transition
  obtain ⟨v3, s3, n3, hQ3, he3, hn3, hstk3, hoth3⟩ :=
    htr main (ofList (cvecs ws2)) (t / 2 ^ k) (Nat.clog 2 (2 * r) - k + k) sgn r p k rest
      (Ktr * (200 * (T + 1))) (hDtr ws2 hlen2 hdisc2) v2 hstate2 s2 R0 hstk2
  -- (4) push .nil
  obtain ⟨v4, s4, n4, hQ4, he4, hn4, hstk4, hoth4⟩ :=
    (pushStep (hpush main) (Val.nil) v3 (Kpv * (200 * (T + 1))) (by simpa using hDpush))
      v3 rfl s3 R0 hstk3
  have hstk4' : s4.stk 0 = encs (Val.nil :: v3) ++ R0 := by
    rw [hQ4] at hstk4
    exact hstk4
  -- (5) pick 6
  obtain ⟨v5, s5, n5, hQ5, he5, hn5, hstk5, hoth5⟩ :=
    (pickStep (hpick main) 6 (Val.nil :: v3)
      (by rw [hQ3]; simp [List.length_cons]) (Kpk * (600 * (T + 1))) (by
        have hsz : vsz (ofList (cvecs ws2)) ≤ 14 * S0 + 14 := by
          rw [hS0def]; exact cvecs_bound p r t ws2 hlen2 hdisc2
        rw [hQ3]
        have hgoal : ((((Val.nil :: ofList (cvecs ws2) :: .int 1 :: .int ↑r :: .int ↑p ::
            .int sgn :: .int ↑k :: rest).take (6 + 1)).map vsz).sum + 1) =
            vsz (Val.nil) + vsz (ofList (cvecs ws2)) + isz (1 : ℤ) + isz (r : ℤ) +
              isz (p : ℤ) + isz sgn + isz (k : ℤ) + 1 := by
          rw [show (6 : ℕ) + 1 = 7 from rfl]
          rw [show (Val.nil :: ofList (cvecs ws2) :: .int 1 :: .int ↑r :: .int ↑p ::
              .int sgn :: .int ↑k :: rest).take 7 =
              [Val.nil, ofList (cvecs ws2), .int 1, .int ↑r, .int ↑p, .int sgn, .int ↑k] from rfl]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            Work.SynFFT.MrgKit.vsz_int']
          ring
        rw [hgoal]
        nlinarith [hsz, hir, hip, hsg, hik, hS0_1, hS0leT, hkk, hpp, htt, hS0def, hTdef, vsz_nil]))
      (Val.nil :: v3) rfl s4 R0 hstk4'
  -- (6) replicate
  have hget6 : (Val.nil :: v3).getD 6 Val.nil = .int (k : ℤ) := by
    rw [hQ3]
    rfl
  have hv5 : v5 = .int (k : ℤ) :: Val.nil :: v3 := by
    rw [hQ5, hget6]
  obtain ⟨v6, s6, n6, hQ6, he6, hn6, hstk6, hoth6⟩ :=
    (replicateStep (hrep main) k (Val.nil) v3 (Krp * (200 * (T + 1)))
      (hDrep v3)) v5 hv5 s5 R0 hstk5
  -- (7) merge fold
  have hMinv0 : MInv r p t k sgn rest u e 0 v3 := by
    refine ⟨ws2, ?_, hlen2, hdisc2, ?_⟩
    · rw [hQ3]
      norm_num
    · change ApproxSL p r t ws2 (levels r sgn t k u) (e + ↑k)
      exact happ2
  obtain ⟨v7, s7, n7, hQ7, he7, hn7, hstk7, hoth7⟩ :=
    hFM' v6 ⟨v3, hQ6, hMinv0⟩ s6 R0 hstk6
  obtain ⟨ws7, hstate7, hlen7, hdisc7, happ7⟩ := hQ7
  -- (8) epilogue
  obtain ⟨v8, s8, n8, hQ8, he8, hn8, hstk8, hoth8⟩ :=
    hpo main (ofList (cvecs ws7)) (2 ^ k) r p k sgn rest (Kpo * (200 * (T + 1)))
      (hDpo ws7 hlen7 hdisc7) v7 hstate7 s7 R0 hstk7
  -- the final post
  refine ⟨v8, s8, (((((n1 + n2) + n3) + n4) + n5) + n6 + n7) + n8, ?_,
    Eval.seq (Eval.seq (Eval.seq (Eval.seq (Eval.seq (Eval.seq (Eval.seq he1 he2) he3) he4) he5) he6) he7) he8,
    ?_, hstk8, ?_⟩
  · refine ⟨ws7, ?_, hlen7, hdisc7, ?_⟩
    · rw [hQ8]
    · -- ApproxSL with the dftN function
      unfold ApproxSL at happ7 ⊢
      refine ⟨happ7.1, ?_⟩
      intro q hq c
      have hfft : mrgIterN r k (levels r sgn t k u) q c = dftN r t sgn u q c := by
        show fftN r t k sgn u q c = dftN r t sgn u q c
        rw [fftN_eq_dftN hbr r t k sgn u hIsPow ht htdvd hsgn q hq]
      change (2 : ℝ) ^ p * ‖fxC p ((ws7.getD q []).getD (c : ℕ) (0, 0)) - dftN r t sgn u q c‖ ≤
        e + ↑k
      rw [← hfft]
      exact happ7.2 q hq c
  · -- the cost bound
    have htotal : (((((n1 + n2) + n3) + n4) + n5) + n6 + n7) + n8 ≤
        1000000 * Sig * t * (r + 1) * (p + 1) * (k + 1) + 1000000 * Sig := by
      have hn1' : n1 ≤ Kpre * (40 * (T + 1)) := hn1
      have hn2' : n2 ≤ k * (cL + Kf * 2) + Kf := hn2
      have hn3' : n3 ≤ Ktr * (200 * (T + 1)) := hn3
      have hn4' : n4 ≤ Kpv * (200 * (T + 1)) := hn4
      have hn5' : n5 ≤ Kpk * (600 * (T + 1)) := hn5
      have hn6' : n6 ≤ Krp * (200 * (T + 1)) := hn6
      have hn7' : n7 ≤ k * (cM + Kf * 2) + Kf := hn7
      have hn8' : n8 ≤ Kpo * (200 * (T + 1)) := hn8
      simp only [hcL, hcM] at hn2' hn7'
      rw [hSig] at *
      rw [hS0def] at *
      rw [hTdef] at *
      nlinarith [hn1', hn2', hn3', hn4', hn5', hn6', hn7', hn8', hS0_1, hS0leT, hkk, hT1,
        vsz_nil,
        Nat.zero_le KL, Nat.zero_le KM, Nat.zero_le Kf, Nat.zero_le Kdr, Nat.zero_le Kpk,
        Nat.zero_le Kpv, Nat.zero_le Krp, Nat.zero_le Kpre, Nat.zero_le Kupd, Nat.zero_le Kudm,
        Nat.zero_le Ktr, Nat.zero_le Kpo]
    simpa using htotal
  · intro kk hkk'
    rw [hoth8 kk hkk', hoth7 kk hkk', hoth6 kk hkk', hoth5 kk hkk', hoth4 kk hkk',
      hoth3 kk hkk', hoth2 kk hkk', hoth1 kk hkk']

end Work.SynFFT
