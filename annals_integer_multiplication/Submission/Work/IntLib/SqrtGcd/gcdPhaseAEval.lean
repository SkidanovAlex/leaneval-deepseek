import Mathlib
import Submission.Work.IntLib.SqrtGcd.GcdProg

/-!
# The common-`2`-part phase of the binary gcd

`SG.gcdPhaseA` strips the factors of `2` common to the two bit regions `sU`, `sV` (least
significant bit first, delimited by their markers) and records their number as that many ticks on
the unary counter `sG`.  It stops as soon as one of the two regions runs out of leading `false`
bits, i.e. after `min (nFalses us) (nFalses vs)` iterations, where `nFalses` is the number of
leading `false` bits — that is `(us.takeWhile (fun b => !b)).length`.

The cost is at most ten steps per stripped bit (two peeks, two tests, two pops, a tick and the flag
settings), hence the generous `100 * (k + 1)` bound below.

The proof is a strong induction on the distance `k - j` to the final iteration.  Every iteration
except the last one finds a `false` bit on top of *both* regions (`head_drop_of_lt_takeWhile_not`)
and strips it (`phaseBody_cont`); the last one finds at least one non-`false` head
(`head_drop_takeWhile_not_ne`) and only sets the stop flag (`phaseBody_stop`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib.SqrtGcd

open HvdH Work.Layout
open Work.IntLib.SG

/-- The body of the phase-`A` loop, spelled out so that its evaluation lemmas can be stated. -/
def phaseBody : Cmd :=
  .seq (.peek sU rgT) (.seq (.peek sV rgU)
    (.ite rgT (.bit false)
      (.ite rgU (.bit false)
        (seqs [ .pop sU rgT, .pop sV rgU, .set rgW gTick, .push sG rgW,
                .set rgF gGo ])
        (.set rgF gStop))
      (.set rgF gStop)))

theorem gcdPhaseA_eq : SG.gcdPhaseA = .seq (.set rgF gGo) (.loop rgF gGo phaseBody) := rfl

/-- The state invariant of the phase-`A` loop: `j` leading `false` bits have been stripped from
both regions and recorded as `j` ticks on the counter `sG`. -/
def phaseInv (us vs : List Bool) (tick bU bV bG : List Glyph) (j : ℕ) (s : State) : Prop :=
  s.stk sU = (us.drop j).map Glyph.bit ++ Glyph.mk sU :: bU ∧
  s.stk sV = (vs.drop j).map Glyph.bit ++ Glyph.mk sV :: bV ∧
  s.stk sG = List.replicate j gTick ++ (tick ++ Glyph.mk sG :: bG)

/-! ## Leading `false` bits -/

/-- The `j`-th position of a list is a `false` bit as long as `j` is below the number of leading
`false` bits. -/
theorem head_drop_of_lt_takeWhile_not (l : List Bool) :
    ∀ j, j < (l.takeWhile (fun b => !b)).length → (l.drop j).head? = some false := by
  induction l with
  | nil => intro j hj; simp at hj
  | cons b t ih =>
    intro j hj
    cases b with
    | true =>
      rw [List.takeWhile_cons_of_neg (by simp)] at hj
      simp at hj
    | false =>
      rw [List.takeWhile_cons_of_pos (by simp)] at hj
      cases j with
      | zero => rfl
      | succ j => simpa using ih j (by simpa using hj)

/-- Past the leading `false` bits the next head, if any, is a `true` bit. -/
theorem head_drop_takeWhile_not_ne (l : List Bool) :
    (l.drop ((l.takeWhile (fun b => !b)).length)).head? ≠ some false := by
  induction l with
  | nil => simp
  | cons b t ih =>
    cases b with
    | true => simp [List.takeWhile_cons_of_neg]
    | false =>
      rw [List.takeWhile_cons_of_pos (by simp)]
      simpa using ih

/-- `headD` of a list whose `head?` is not `some c` is not `c` either. -/
theorem headD_ne_of_head?_ne {l : List Glyph} {c : Glyph} (he : Glyph.eos ≠ c) :
    l.head? ≠ some c → l.headD Glyph.eos ≠ c := by
  intro h
  cases l with
  | nil => simpa using he
  | cons b t => intro hc; exact h (show some b = some c from by rw [show b = c from hc])

/-- A region on a stack does not start with a `false` bit once the leading `false` bits of its
value have been exhausted and its marker is not a `false` bit. -/
theorem head_map_bit_append_ne {l : List Bool} {M : Glyph} {rest : List Glyph}
    (hM : M ≠ Glyph.bit false) (h : l.head? ≠ some false) :
    (l.map Glyph.bit ++ M :: rest).head? ≠ some (Glyph.bit false) := by
  rcases l with - | ⟨b, t⟩
  · simpa using hM
  · intro hc
    have h1 : Glyph.bit b = Glyph.bit false := by simpa using hc
    have hb : b = false := Glyph.bit.inj h1
    exact h (show some b = some false from by rw [hb])

/-- The phase-`A` program only touches the three stacks `sU`, `sV`, `sG`. -/
theorem not_mem_cmdTouches_gcdPhaseA (j : Stk) (h1 : j ≠ sU) (h2 : j ≠ sV)
    (h3 : j ≠ sG) : j ∉ cmdTouches SG.gcdPhaseA := by
  simp [SG.gcdPhaseA, cmdTouches, seqs]
  exact ⟨h2, h1, h3⟩

/-! ## One iteration of the loop -/

/-- **The stripping iteration.**  If both regions start with a `false` bit, the body pops one bit
from each, pushes one tick on the counter and keeps the loop flag at `gGo`. -/
theorem phaseBody_cont (main : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph)
    (AU AV : List Glyph)
    (hU : X sU = Glyph.bit false :: AU) (hV : X sV = Glyph.bit false :: AV) :
    ∃ s', Ev main phaseBody ⟨g, X⟩ s' 9 ∧ s'.stk sU = AU ∧ s'.stk sV = AV ∧
      s'.stk sG = gTick :: X sG ∧ s'.reg rgF = gGo := by
  have hne_UV : sU ≠ sV := by decide
  have hne_US : sU ≠ sG := by decide
  have hne_VS : sV ≠ sG := by decide
  have hne_TU : rgT ≠ rgU := by decide
  set g1 : Reg → Glyph := Function.update g rgT (Glyph.bit false) with hg1
  set g2 : Reg → Glyph := Function.update g1 rgU (Glyph.bit false) with hg2
  set g3 : Reg → Glyph := Function.update g2 rgT (Glyph.bit false) with hg3
  set g4 : Reg → Glyph := Function.update g3 rgU (Glyph.bit false) with hg4
  set g5 : Reg → Glyph := Function.update g4 rgW gTick with hg5
  set g7 : Reg → Glyph := Function.update g5 rgF gGo with hg7
  set X1 : Stk → List Glyph := Function.update X sU AU with hX1
  set X2 : Stk → List Glyph := Function.update X1 sV AV with hX2
  set X3 : Stk → List Glyph := Function.update X2 sG (gTick :: X sG) with hX3
  have hX1V : X1 sV = Glyph.bit false :: AV := by
    rw [hX1, Function.update_of_ne (Ne.symm hne_UV)]; exact hV
  have hg5W : g5 rgW = gTick := by rw [hg5, Function.update_self]
  have hX2S : X2 sG = X sG := by
    rw [hX2, hX1, Function.update_of_ne (Ne.symm hne_VS),
      Function.update_of_ne (Ne.symm hne_US)]
  have e1 : Ev main (.peek sU rgT) ⟨g, X⟩ ⟨g1, X⟩ 1 := by
    have h := ev_peek' main sU rgT g X
    have hx : (X sU).headD Glyph.eos = Glyph.bit false := by rw [hU]; rfl
    rwa [hx] at h
  have e2 : Ev main (.peek sV rgU) ⟨g1, X⟩ ⟨g2, X⟩ 1 := by
    have h := ev_peek' main sV rgU g1 X
    have hx : (X sV).headD Glyph.eos = Glyph.bit false := by rw [hV]; rfl
    rwa [hx] at h
  have e3 : Ev main (.pop sU rgT) ⟨g2, X⟩ ⟨g3, X1⟩ 1 := by
    have h := ev_pop' main sU rgT g2 X
    rw [hU] at h
    simpa only [List.headD_cons, List.tail_cons] using h
  have e4 : Ev main (.pop sV rgU) ⟨g3, X1⟩ ⟨g4, X2⟩ 1 := by
    have h := ev_pop' main sV rgU g3 X1
    rw [hX1V] at h
    simpa only [List.headD_cons, List.tail_cons] using h
  have e5 : Ev main (.set rgW gTick) ⟨g4, X2⟩ ⟨g5, X2⟩ 1 := ev_set' main rgW gTick g4 X2
  have e6 : Ev main (.push sG rgW) ⟨g5, X2⟩ ⟨g5, X3⟩ 1 := by
    have h := ev_push' main sG rgW g5 X2
    simpa only [hg5W, hX2S] using h
  have e7 : Ev main (.set rgF gGo) ⟨g5, X3⟩ ⟨g7, X3⟩ 1 := ev_set' main rgF gGo g5 X3
  have e34567 : Ev main (seqs [.pop sU rgT, .pop sV rgU, .set rgW gTick, .push sG rgW,
      .set rgF gGo]) ⟨g2, X⟩ ⟨g7, X3⟩ 5 := by
    have h : Ev main (.seq (.pop sU rgT) (.seq (.pop sV rgU) (.seq (.set rgW gTick)
        (.seq (.push sG rgW) (.set rgF gGo))))) ⟨g2, X⟩ ⟨g7, X3⟩ 5 :=
      Ev.seq e3 (Ev.seq e4 (Ev.seq e5 (Ev.seq e6 e7)))
    simpa [seqs] using h
  have hrgU : (⟨g2, X⟩ : State).reg rgU = Glyph.bit false := by
    show g2 rgU = _; rw [hg2, Function.update_self]
  have hrgT : (⟨g2, X⟩ : State).reg rgT = Glyph.bit false := by
    show g2 rgT = _
    rw [hg2, Function.update_of_ne hne_TU, hg1, Function.update_self]
  have eInner : Ev main (.ite rgU (.bit false)
      (seqs [.pop sU rgT, .pop sV rgU, .set rgW gTick, .push sG rgW, .set rgF gGo])
      (.set rgF gStop)) ⟨g2, X⟩ ⟨g7, X3⟩ 6 := Ev.iteT hrgU e34567
  have eOuter : Ev main (.ite rgT (.bit false)
      (.ite rgU (.bit false)
        (seqs [.pop sU rgT, .pop sV rgU, .set rgW gTick, .push sG rgW, .set rgF gGo])
        (.set rgF gStop))
      (.set rgF gStop)) ⟨g2, X⟩ ⟨g7, X3⟩ 7 := Ev.iteT hrgT eInner
  have eBody : Ev main phaseBody ⟨g, X⟩ ⟨g7, X3⟩ 9 := Ev.seq e1 (Ev.seq e2 eOuter)
  refine ⟨⟨g7, X3⟩, eBody, ?_, ?_, ?_, ?_⟩
  · show X3 sU = AU
    rw [hX3, hX2, hX1, Function.update_of_ne hne_US, Function.update_of_ne hne_UV,
      Function.update_self]
  · show X3 sV = AV
    rw [hX3, Function.update_of_ne hne_VS, hX2, Function.update_self]
  · show X3 sG = gTick :: X sG
    rw [hX3, Function.update_self]
  · show g7 rgF = gGo
    rw [hg7, Function.update_self]

/-- **The stopping iteration.**  If at least one of the two regions does not start with a `false`
bit, the body only sets the stop flag. -/
theorem phaseBody_stop (main : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph)
    (AU AV : List Glyph)
    (hU : X sU = AU) (hV : X sV = AV)
    (hstop : AU.head? ≠ some (Glyph.bit false) ∨ AV.head? ≠ some (Glyph.bit false)) :
    ∃ s', Ev main phaseBody ⟨g, X⟩ s' 5 ∧ s'.stk sU = AU ∧ s'.stk sV = AV ∧
      s'.stk sG = X sG ∧ s'.reg rgF = gStop := by
  have hne_TU : rgT ≠ rgU := by decide
  set g1 : Reg → Glyph := Function.update g rgT (AU.headD Glyph.eos) with hg1
  set g2 : Reg → Glyph := Function.update g1 rgU (AV.headD Glyph.eos) with hg2
  set g3 : Reg → Glyph := Function.update g2 rgF gStop with hg3
  have e1 : Ev main (.peek sU rgT) ⟨g, X⟩ ⟨g1, X⟩ 1 := by
    have h := ev_peek' main sU rgT g X
    rwa [hU] at h
  have e2 : Ev main (.peek sV rgU) ⟨g1, X⟩ ⟨g2, X⟩ 1 := by
    have h := ev_peek' main sV rgU g1 X
    rwa [hV] at h
  have hg2T : g2 rgT = g1 rgT := by rw [hg2, Function.update_of_ne hne_TU]
  by_cases hA : AU.head? = some (Glyph.bit false)
  · -- `sU` starts with a `false` bit, so `sV` decides the test
    have hB : AV.head? ≠ some (Glyph.bit false) := by
      rcases hstop with h | h
      · exact absurd hA h
      · exact h
    obtain ⟨AU', hAU⟩ := List.head?_eq_some_iff.mp hA
    have hB' : AV.headD Glyph.eos ≠ Glyph.bit false :=
      headD_ne_of_head?_ne (by decide) hB
    have hrgT : (⟨g2, X⟩ : State).reg rgT = Glyph.bit false := by
      show g2 rgT = _
      rw [hg2T, hg1, Function.update_self, hAU]
      rfl
    have hrgU : (⟨g2, X⟩ : State).reg rgU ≠ Glyph.bit false := by
      show g2 rgU ≠ _
      rw [hg2, Function.update_self]
      exact hB'
    have eSet : Ev main (.set rgF gStop) ⟨g2, X⟩ ⟨g3, X⟩ 1 := ev_set' main rgF gStop g2 X
    have eInner : Ev main (.ite rgU (.bit false)
        (seqs [.pop sU rgT, .pop sV rgU, .set rgW gTick, .push sG rgW, .set rgF gGo])
        (.set rgF gStop)) ⟨g2, X⟩ ⟨g3, X⟩ 2 := Ev.iteF hrgU eSet
    have eOuter : Ev main (.ite rgT (.bit false)
        (.ite rgU (.bit false)
          (seqs [.pop sU rgT, .pop sV rgU, .set rgW gTick, .push sG rgW, .set rgF gGo])
          (.set rgF gStop))
        (.set rgF gStop)) ⟨g2, X⟩ ⟨g3, X⟩ 3 := Ev.iteT hrgT eInner
    have eBody : Ev main phaseBody ⟨g, X⟩ ⟨g3, X⟩ 5 := Ev.seq e1 (Ev.seq e2 eOuter)
    refine ⟨⟨g3, X⟩, eBody, ?_, ?_, ?_, ?_⟩
    · show X sU = AU; exact hU
    · show X sV = AV; exact hV
    · rfl
    · show g3 rgF = gStop; rw [hg3, Function.update_self]
  · -- `sU` does not start with a `false` bit: the outer test decides
    have hA' : AU.headD Glyph.eos ≠ Glyph.bit false := headD_ne_of_head?_ne (by decide) hA
    have hrgT : (⟨g2, X⟩ : State).reg rgT ≠ Glyph.bit false := by
      show g2 rgT ≠ _
      rw [hg2T, hg1, Function.update_self]
      exact hA'
    have eSet : Ev main (.set rgF gStop) ⟨g2, X⟩ ⟨g3, X⟩ 1 := ev_set' main rgF gStop g2 X
    have eOuter : Ev main (.ite rgT (.bit false)
        (.ite rgU (.bit false)
          (seqs [.pop sU rgT, .pop sV rgU, .set rgW gTick, .push sG rgW, .set rgF gGo])
          (.set rgF gStop))
        (.set rgF gStop)) ⟨g2, X⟩ ⟨g3, X⟩ 2 := Ev.iteF hrgT eSet
    have eBody : Ev main phaseBody ⟨g, X⟩ ⟨g3, X⟩ 4 := Ev.seq e1 (Ev.seq e2 eOuter)
    refine ⟨⟨g3, X⟩, eBody.mono (by omega), ?_, ?_, ?_, ?_⟩
    · show X sU = AU; exact hU
    · show X sV = AV; exact hV
    · rfl
    · show g3 rgF = gStop; rw [hg3, Function.update_self]

/-! ## The whole phase -/

theorem gcdPhaseAEval (main : HvdH.Cmd) (us vs : List Bool) (tick : List HvdH.Glyph)
    (bU bV bG : List HvdH.Glyph) (s : HvdH.State)
    (hU : s.stk Work.IntLib.SG.sU = us.map HvdH.Glyph.bit ++ HvdH.Glyph.mk Work.IntLib.SG.sU :: bU)
    (hV : s.stk Work.IntLib.SG.sV = vs.map HvdH.Glyph.bit ++ HvdH.Glyph.mk Work.IntLib.SG.sV :: bV)
    (hG : s.stk Work.IntLib.SG.sG = tick ++ HvdH.Glyph.mk Work.IntLib.SG.sG :: bG) :
    ∃ s' m, HvdH.Eval main Work.IntLib.SG.gcdPhaseA s s' m ∧
      m ≤ 100 * (min ((us.takeWhile (fun b => !b)).length) ((vs.takeWhile (fun b => !b)).length) + 1) ∧
      s'.stk Work.IntLib.SG.sU =
        (us.drop (min ((us.takeWhile (fun b => !b)).length) ((vs.takeWhile (fun b => !b)).length))).map HvdH.Glyph.bit
          ++ HvdH.Glyph.mk Work.IntLib.SG.sU :: bU ∧
      s'.stk Work.IntLib.SG.sV =
        (vs.drop (min ((us.takeWhile (fun b => !b)).length) ((vs.takeWhile (fun b => !b)).length))).map HvdH.Glyph.bit
          ++ HvdH.Glyph.mk Work.IntLib.SG.sV :: bV ∧
      s'.stk Work.IntLib.SG.sG =
        (List.replicate (min ((us.takeWhile (fun b => !b)).length) ((vs.takeWhile (fun b => !b)).length))
            Work.IntLib.SG.gTick ++ tick) ++ HvdH.Glyph.mk Work.IntLib.SG.sG :: bG ∧
      (∀ j : HvdH.Stk, j ≠ Work.IntLib.SG.sU → j ≠ Work.IntLib.SG.sV → j ≠ Work.IntLib.SG.sG →
        s'.stk j = s.stk j) := by
  set k : ℕ := min ((us.takeWhile (fun b => !b)).length) ((vs.takeWhile (fun b => !b)).length) with hk
  have hInv0 : phaseInv us vs tick bU bV bG 0 s := by
    refine ⟨?_, ?_, ?_⟩
    · simpa using hU
    · simpa using hV
    · simpa using hG
  have key : ∀ d j, k - j = d → j ≤ k → ∀ s : State, phaseInv us vs tick bU bV bG j s →
      s.reg rgF = gGo →
      ∃ s' m, Eval main (.loop rgF gGo phaseBody) s s' m ∧ m ≤ 10 * d + 7 ∧
        phaseInv us vs tick bU bV bG k s' ∧ s'.reg rgF = gStop := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro j hd hjle s hInv hF
      rcases lt_or_eq_of_le hjle with hjlt | hjk
      · -- one more stripping iteration, then the induction hypothesis
        obtain ⟨hUs, hVs, hGs⟩ := hInv
        have hjmin : j < min ((us.takeWhile (fun b => !b)).length)
            ((vs.takeWhile (fun b => !b)).length) := by
          rw [← hk]; exact hjlt
        have hjU : j < (us.takeWhile (fun b => !b)).length :=
          lt_of_lt_of_le hjmin (Nat.min_le_left _ _)
        have hjV : j < (vs.takeWhile (fun b => !b)).length :=
          lt_of_lt_of_le hjmin (Nat.min_le_right _ _)
        obtain ⟨ru, hru⟩ := List.head?_eq_some_iff.mp (head_drop_of_lt_takeWhile_not us j hjU)
        obtain ⟨rv, hrv⟩ := List.head?_eq_some_iff.mp (head_drop_of_lt_takeWhile_not vs j hjV)
        have hU' : s.stk sU = Glyph.bit false :: (ru.map Glyph.bit ++ Glyph.mk sU :: bU) := by
          rw [hUs, hru, List.map_cons]; rfl
        have hV' : s.stk sV = Glyph.bit false :: (rv.map Glyph.bit ++ Glyph.mk sV :: bV) := by
          rw [hVs, hrv, List.map_cons]; rfl
        obtain ⟨s1, hev1, hsU1, hsV1, hsG1, hreg1⟩ :=
          phaseBody_cont main s.reg s.stk (ru.map Glyph.bit ++ Glyph.mk sU :: bU)
            (rv.map Glyph.bit ++ Glyph.mk sV :: bV) hU' hV'
        have hdropU : us.drop (j + 1) = ru := by
          rw [← List.drop_drop, hru, List.drop_succ_cons]; rfl
        have hdropV : vs.drop (j + 1) = rv := by
          rw [← List.drop_drop, hrv, List.drop_succ_cons]; rfl
        have hInv1 : phaseInv us vs tick bU bV bG (j + 1) s1 := by
          refine ⟨?_, ?_, ?_⟩
          · rw [hsU1, hdropU]
          · rw [hsV1, hdropV]
          · rw [hsG1, hGs, List.replicate_succ, ← List.cons_append]
        have hlt : k - (j + 1) < d := by omega
        obtain ⟨s2, m2, he2, hm2, hInv2, hreg2⟩ :=
          ih (k - (j + 1)) hlt (j + 1) rfl (by omega) s1 hInv1 hreg1
        obtain ⟨n1, he1, hn1⟩ := hev1
        exact ⟨s2, n1 + m2 + 1, Eval.loopT hF he1 he2, by omega, hInv2, hreg2⟩
      · -- the last iteration only stops the loop
        rw [hjk] at hInv hd
        obtain ⟨hUs, hVs, hGs⟩ := hInv
        have hkU : k = (us.takeWhile (fun b => !b)).length ∨
            k = (vs.takeWhile (fun b => !b)).length := by
          rcases le_total ((us.takeWhile (fun b => !b)).length)
            ((vs.takeWhile (fun b => !b)).length) with h | h
          · left; rw [hk, Nat.min_eq_left h]
          · right; rw [hk, Nat.min_eq_right h]
        have hstop' : ((us.drop k).map Glyph.bit ++ Glyph.mk sU :: bU).head? ≠
              some (Glyph.bit false) ∨
            ((vs.drop k).map Glyph.bit ++ Glyph.mk sV :: bV).head? ≠
              some (Glyph.bit false) := by
          rcases hkU with h | h
          · left
            exact head_map_bit_append_ne (M := Glyph.mk sU) (by decide)
              (by rw [h]; exact head_drop_takeWhile_not_ne us)
          · right
            exact head_map_bit_append_ne (M := Glyph.mk sV) (by decide)
              (by rw [h]; exact head_drop_takeWhile_not_ne vs)
        have hstop : (s.stk sU).head? ≠ some (Glyph.bit false) ∨
            (s.stk sV).head? ≠ some (Glyph.bit false) := by
          rcases hstop' with h | h
          · left; rwa [hUs]
          · right; rwa [hVs]
        obtain ⟨s1, hev1, hsU1, hsV1, hsG1, hreg1⟩ :=
          phaseBody_stop main s.reg s.stk (s.stk sU) (s.stk sV) rfl rfl hstop
        have hne : s1.reg rgF ≠ gGo := by rw [hreg1]; decide
        have hloop : Eval main (.loop rgF gGo phaseBody) s1 s1 1 := Eval.loopF hne
        obtain ⟨n1, he1, hn1⟩ := hev1
        refine ⟨s1, n1 + 1 + 1, Eval.loopT hF he1 hloop, ?_, ?_, hreg1⟩
        · omega
        · refine ⟨?_, ?_, ?_⟩
          · rw [hsU1]; exact hUs
          · rw [hsV1]; exact hVs
          · rw [hsG1]; exact hGs
  have hF0 : (⟨Function.update s.reg rgF gGo, s.stk⟩ : State).reg rgF = gGo := by
    show Function.update s.reg rgF gGo rgF = gGo
    rw [Function.update_self]
  have hInv1 : phaseInv us vs tick bU bV bG 0 ⟨Function.update s.reg rgF gGo, s.stk⟩ := by
    obtain ⟨a1, a2, a3⟩ := hInv0
    exact ⟨a1, a2, a3⟩
  obtain ⟨s1, m1, he1, hm1, hInvk, hregk⟩ := key k 0 (by simp) (by omega) _ hInv1 hF0
  have eSet : Ev main (.set rgF gGo) s ⟨Function.update s.reg rgF gGo, s.stk⟩ 1 :=
    ev_set' main rgF gGo s.reg s.stk
  obtain ⟨n0, he0, hn0⟩ := eSet
  refine ⟨s1, n0 + m1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gcdPhaseA_eq]
    exact Eval.seq he0 he1
  · omega
  · exact hInvk.1
  · exact hInvk.2.1
  · rw [List.append_assoc]; exact hInvk.2.2
  · intro j hjU hjV hjG
    exact Eval.stk_frame (Eval.seq he0 he1) (not_mem_cmdTouches_gcdPhaseA j hjU hjV hjG)

end Work.IntLib.SqrtGcd
