import Mathlib
import Submission.Work.IntLib.Shift.Defs
import Submission.Work.IntLib.Shift.Loop

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.IntLib.Shift

open HvdH

/-!
# `IntLib` / shift words: the magnitude-increment word `incRgn`

`incRgn` (defined in `Defs`) adds one to the magnitude region of `sM`.  Its carry loop walks the
least-significant-first bit region of `sM` above the frame marker `gmk sM`:

* a `true` bit is replaced by a `false` carry, which is parked on `sT`;
* the first `false` bit becomes `true` and the loop stops;
* if the whole region is `true` (or empty), the marker itself is popped, put back, and a fresh most
  significant `true` bit is pushed onto `sM`.

The final `drain sT sM (gmk sT) rZ rJ` then moves the parked carries back on top of the region of
`sM` (in the correct order), which wipes the frame marker of `sT` away again.

The two book-keeping functions below record exactly this: `incCarry Bs` is the list of carries
parked on `sT` (bottom-to-top), `incRem Bs` is what is left in the region of `sM` when the loop
stops.  Their concatenation is the usual carry propagation `incList`.
-/

/-! ## Pure list-level bookkeeping -/

/-- Carries parked on `sT` by the carry loop of `incRgn`, in chronological (bottom-to-top) order. -/
def incCarry : List Bool → List Bool
  | [] => []
  | true :: xs => false :: incCarry xs
  | false :: xs => [true]

/-- What is left in the magnitude region of `sM` (above its frame marker) when the carry loop of
`incRgn` stops.  In the "all bits are `true`" case the loop pushes a fresh `true` bit, which the
`[]` clause records. -/
def incRem : List Bool → List Bool
  | [] => [true]
  | true :: xs => incRem xs
  | false :: xs => xs

@[simp] theorem incCarry_nil : incCarry [] = [] := rfl
@[simp] theorem incCarry_true (xs : List Bool) : incCarry (true :: xs) = false :: incCarry xs := rfl
@[simp] theorem incCarry_false (xs : List Bool) : incCarry (false :: xs) = [true] := rfl
@[simp] theorem incRem_nil : incRem [] = [true] := rfl
@[simp] theorem incRem_true (xs : List Bool) : incRem (true :: xs) = incRem xs := rfl
@[simp] theorem incRem_false (xs : List Bool) : incRem (false :: xs) = xs := rfl

/-- The loop parks the carries on `sT` and leaves the rest of the region on `sM`; together they are
the result of the carry propagation `incList`. -/
theorem incCarry_append_incRem (Bs : List Bool) : incCarry Bs ++ incRem Bs = incList Bs := by
  induction Bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [ih]

/-- The loop parks at most one carry per bit. -/
theorem incCarry_length_le (Bs : List Bool) : (incCarry Bs).length ≤ Bs.length := by
  induction Bs with
  | nil => simp
  | cons b bs ih =>
      cases b <;>
        simp only [incCarry_true, incCarry_false, List.length_cons, List.length_nil] <;> omega

/-! ## One iteration of the carry loop -/

/-- One iteration of `incBody` when the current magnitude bit is `true`: the bit is replaced by a
`false` carry parked on `sT`, and the loop goes on (`rI` is unchanged). -/
theorem incBody_true_ev (main : Cmd) (s : State) (R : List Glyph)
    (h : s.stk sM = Glyph.bit true :: R) :
    ∃ (s' : State) (n : ℕ), Eval main incBody s s' n ∧ n ≤ 5 ∧ s'.reg rI = s.reg rI ∧
      s'.stk sM = R ∧ s'.stk sT = Glyph.bit false :: s.stk sT ∧
      (∀ j : Stk, j ≠ sM → j ≠ sT → s'.stk j = s.stk j) := by
  have hd : (s.stk sM).headD .eos = Glyph.bit true := by simp [h]
  have htl : (s.stk sM).tail = R := by simp [h]
  have hpop : Ev main (.pop sM rX) s
      ⟨Function.update s.reg rX (Glyph.bit true), Function.update s.stk sM R⟩ 1 := by
    have h0 := ev_pop_st main sM rX s
    rw [hd, htl] at h0
    exact h0
  have hpush : Ev main (pushC sT (Glyph.bit false) rY)
      ⟨Function.update s.reg rX (Glyph.bit true), Function.update s.stk sM R⟩
      ⟨Function.update (Function.update s.reg rX (Glyph.bit true)) rY (Glyph.bit false),
       Function.update (Function.update s.stk sM R) sT
         (Glyph.bit false :: (Function.update s.stk sM R) sT)⟩ 2 :=
    ev_pushC_st main sT (Glyph.bit false) rY _
  have hreg : (⟨Function.update s.reg rX (Glyph.bit true),
      Function.update s.stk sM R⟩ : State).reg rX = Glyph.bit true :=
    Function.update_self rX (Glyph.bit true) s.reg
  have hne : (⟨Function.update s.reg rX (Glyph.bit true),
      Function.update s.stk sM R⟩ : State).reg rX ≠ gmk sM := by
    rw [hreg]; exact bit_ne_gmk sM true
  have hite1 : Ev main (.ite rX (Glyph.bit true) (pushC sT (Glyph.bit false) rY)
      (seqs [pushC sT (Glyph.bit true) rY, .set rI gStop]))
      ⟨Function.update s.reg rX (Glyph.bit true), Function.update s.stk sM R⟩
      ⟨Function.update (Function.update s.reg rX (Glyph.bit true)) rY (Glyph.bit false),
       Function.update (Function.update s.stk sM R) sT
         (Glyph.bit false :: (Function.update s.stk sM R) sT)⟩ 3 :=
    Ev.iteT hreg hpush
  have hite2 : Ev main (.ite rX (gmk sM)
      (seqs [.push sM rX, pushC sM (Glyph.bit true) rY, .set rI gStop])
      (seqs [.ite rX (Glyph.bit true) (pushC sT (Glyph.bit false) rY)
        (seqs [pushC sT (Glyph.bit true) rY, .set rI gStop])]))
      ⟨Function.update s.reg rX (Glyph.bit true), Function.update s.stk sM R⟩
      ⟨Function.update (Function.update s.reg rX (Glyph.bit true)) rY (Glyph.bit false),
       Function.update (Function.update s.stk sM R) sT
         (Glyph.bit false :: (Function.update s.stk sM R) sT)⟩ 4 :=
    Ev.iteF hne hite1
  have hbody : Ev main incBody s
      ⟨Function.update (Function.update s.reg rX (Glyph.bit true)) rY (Glyph.bit false),
       Function.update (Function.update s.stk sM R) sT
         (Glyph.bit false :: (Function.update s.stk sM R) sT)⟩ 5 :=
    Ev.seq' hpop hite2 (le_rfl)
  obtain ⟨n, he, hn⟩ := hbody
  refine ⟨⟨Function.update (Function.update s.reg rX (Glyph.bit true)) rY (Glyph.bit false),
      Function.update (Function.update s.stk sM R) sT
        (Glyph.bit false :: (Function.update s.stk sM R) sT)⟩, n, he, by omega, ?_, ?_, ?_, ?_⟩
  · show (Function.update (Function.update s.reg rX (Glyph.bit true)) rY (Glyph.bit false)) rI
      = s.reg rI
    simp only [upReg_ne (show rI ≠ rY by decide), upReg_ne (show rI ≠ rX by decide)]
  · show (Function.update (Function.update s.stk sM R) sT
        (Glyph.bit false :: (Function.update s.stk sM R) sT)) sM = R
    simp only [upStk_ne (show sM ≠ sT by decide), upStk_same]
  · show (Function.update (Function.update s.stk sM R) sT
        (Glyph.bit false :: (Function.update s.stk sM R) sT)) sT
      = Glyph.bit false :: s.stk sT
    simp only [upStk_same, upStk_ne (show sT ≠ sM by decide)]
  · intro j hjM hjT
    show (Function.update (Function.update s.stk sM R) sT
        (Glyph.bit false :: (Function.update s.stk sM R) sT)) j = s.stk j
    simp only [upStk_ne hjT, upStk_ne hjM]

/-- One iteration of `incBody` when the current magnitude bit is `false`: it becomes `true` (parked
on `sT`) and the loop stops (`rI := gStop`). -/
theorem incBody_false_ev (main : Cmd) (s : State) (R : List Glyph)
    (h : s.stk sM = Glyph.bit false :: R) :
    ∃ (s' : State) (n : ℕ), Eval main incBody s s' n ∧ n ≤ 6 ∧ s'.reg rI = gStop ∧
      s'.stk sM = R ∧ s'.stk sT = Glyph.bit true :: s.stk sT ∧
      (∀ j : Stk, j ≠ sM → j ≠ sT → s'.stk j = s.stk j) := by
  have hd : (s.stk sM).headD .eos = Glyph.bit false := by simp [h]
  have htl : (s.stk sM).tail = R := by simp [h]
  have hpop : Ev main (.pop sM rX) s
      ⟨Function.update s.reg rX (Glyph.bit false), Function.update s.stk sM R⟩ 1 := by
    have h0 := ev_pop_st main sM rX s
    rw [hd, htl] at h0
    exact h0
  have hpush : Ev main (pushC sT (Glyph.bit true) rY)
      ⟨Function.update s.reg rX (Glyph.bit false), Function.update s.stk sM R⟩
      ⟨Function.update (Function.update s.reg rX (Glyph.bit false)) rY (Glyph.bit true),
       Function.update (Function.update s.stk sM R) sT
         (Glyph.bit true :: (Function.update s.stk sM R) sT)⟩ 2 :=
    ev_pushC_st main sT (Glyph.bit true) rY _
  have hset : Ev main (.set rI gStop)
      ⟨Function.update (Function.update s.reg rX (Glyph.bit false)) rY (Glyph.bit true),
       Function.update (Function.update s.stk sM R) sT
         (Glyph.bit true :: (Function.update s.stk sM R) sT)⟩
      ⟨Function.update (Function.update (Function.update s.reg rX (Glyph.bit false)) rY
          (Glyph.bit true)) rI gStop,
       Function.update (Function.update s.stk sM R) sT
         (Glyph.bit true :: (Function.update s.stk sM R) sT)⟩ 1 :=
    ev_set_st main rI gStop _
  have hbr : Ev main (seqs [pushC sT (Glyph.bit true) rY, .set rI gStop])
      ⟨Function.update s.reg rX (Glyph.bit false), Function.update s.stk sM R⟩
      ⟨Function.update (Function.update (Function.update s.reg rX (Glyph.bit false)) rY
          (Glyph.bit true)) rI gStop,
       Function.update (Function.update s.stk sM R) sT
         (Glyph.bit true :: (Function.update s.stk sM R) sT)⟩ 3 :=
    Ev.seq' hpush hset (le_rfl)
  have hreg : (⟨Function.update s.reg rX (Glyph.bit false),
      Function.update s.stk sM R⟩ : State).reg rX = Glyph.bit false :=
    Function.update_self rX (Glyph.bit false) s.reg
  have hne1 : (⟨Function.update s.reg rX (Glyph.bit false),
      Function.update s.stk sM R⟩ : State).reg rX ≠ Glyph.bit true := by
    rw [hreg]; decide
  have hne2 : (⟨Function.update s.reg rX (Glyph.bit false),
      Function.update s.stk sM R⟩ : State).reg rX ≠ gmk sM := by
    rw [hreg]; exact bit_ne_gmk sM false
  have hite1 : Ev main (.ite rX (Glyph.bit true) (pushC sT (Glyph.bit false) rY)
      (seqs [pushC sT (Glyph.bit true) rY, .set rI gStop]))
      ⟨Function.update s.reg rX (Glyph.bit false), Function.update s.stk sM R⟩
      ⟨Function.update (Function.update (Function.update s.reg rX (Glyph.bit false)) rY
          (Glyph.bit true)) rI gStop,
       Function.update (Function.update s.stk sM R) sT
         (Glyph.bit true :: (Function.update s.stk sM R) sT)⟩ 4 :=
    Ev.iteF hne1 hbr
  have hite2 : Ev main (.ite rX (gmk sM)
      (seqs [.push sM rX, pushC sM (Glyph.bit true) rY, .set rI gStop])
      (seqs [.ite rX (Glyph.bit true) (pushC sT (Glyph.bit false) rY)
        (seqs [pushC sT (Glyph.bit true) rY, .set rI gStop])]))
      ⟨Function.update s.reg rX (Glyph.bit false), Function.update s.stk sM R⟩
      ⟨Function.update (Function.update (Function.update s.reg rX (Glyph.bit false)) rY
          (Glyph.bit true)) rI gStop,
       Function.update (Function.update s.stk sM R) sT
         (Glyph.bit true :: (Function.update s.stk sM R) sT)⟩ 5 :=
    Ev.iteF hne2 hite1
  have hbody : Ev main incBody s
      ⟨Function.update (Function.update (Function.update s.reg rX (Glyph.bit false)) rY
          (Glyph.bit true)) rI gStop,
       Function.update (Function.update s.stk sM R) sT
         (Glyph.bit true :: (Function.update s.stk sM R) sT)⟩ 6 :=
    Ev.seq' hpop hite2 (le_rfl)
  obtain ⟨n, he, hn⟩ := hbody
  refine ⟨⟨Function.update (Function.update (Function.update s.reg rX (Glyph.bit false)) rY
      (Glyph.bit true)) rI gStop,
      Function.update (Function.update s.stk sM R) sT
        (Glyph.bit true :: (Function.update s.stk sM R) sT)⟩, n, he, by omega, ?_, ?_, ?_, ?_⟩
  · show (Function.update (Function.update (Function.update s.reg rX (Glyph.bit false)) rY
        (Glyph.bit true)) rI gStop) rI = gStop
    simp only [upReg_same]
  · show (Function.update (Function.update s.stk sM R) sT
        (Glyph.bit true :: (Function.update s.stk sM R) sT)) sM = R
    simp only [upStk_ne (show sM ≠ sT by decide), upStk_same]
  · show (Function.update (Function.update s.stk sM R) sT
        (Glyph.bit true :: (Function.update s.stk sM R) sT)) sT
      = Glyph.bit true :: s.stk sT
    simp only [upStk_same, upStk_ne (show sT ≠ sM by decide)]
  · intro j hjM hjT
    show (Function.update (Function.update s.stk sM R) sT
        (Glyph.bit true :: (Function.update s.stk sM R) sT)) j = s.stk j
    simp only [upStk_ne hjT, upStk_ne hjM]

/-- One iteration of `incBody` when the region of `sM` is exhausted (the marker is on top): the
marker is put back and a fresh most significant `true` bit is pushed; the loop stops. -/
theorem incBody_mark_ev (main : Cmd) (s : State) (R : List Glyph)
    (h : s.stk sM = gmk sM :: R) :
    ∃ (s' : State) (n : ℕ), Eval main incBody s s' n ∧ n ≤ 6 ∧ s'.reg rI = gStop ∧
      s'.stk sM = Glyph.bit true :: gmk sM :: R ∧ s'.stk sT = s.stk sT ∧
      (∀ j : Stk, j ≠ sM → j ≠ sT → s'.stk j = s.stk j) := by
  have hd : (s.stk sM).headD .eos = gmk sM := by simp [h]
  have htl : (s.stk sM).tail = R := by simp [h]
  have hpop : Ev main (.pop sM rX) s
      ⟨Function.update s.reg rX (gmk sM), Function.update s.stk sM R⟩ 1 := by
    have h0 := ev_pop_st main sM rX s
    rw [hd, htl] at h0
    exact h0
  have hpush : Ev main (.push sM rX)
      ⟨Function.update s.reg rX (gmk sM), Function.update s.stk sM R⟩
      ⟨Function.update s.reg rX (gmk sM),
       Function.update (Function.update s.stk sM R) sM (gmk sM :: R)⟩ 1 :=
    ev_push_st main sM rX _
  have hpushC : Ev main (pushC sM (Glyph.bit true) rY)
      ⟨Function.update s.reg rX (gmk sM),
       Function.update (Function.update s.stk sM R) sM (gmk sM :: R)⟩
      ⟨Function.update (Function.update s.reg rX (gmk sM)) rY (Glyph.bit true),
       Function.update (Function.update (Function.update s.stk sM R) sM (gmk sM :: R)) sM
         (Glyph.bit true ::
           (Function.update (Function.update s.stk sM R) sM (gmk sM :: R)) sM)⟩ 2 :=
    ev_pushC_st main sM (Glyph.bit true) rY _
  have hset : Ev main (.set rI gStop)
      ⟨Function.update (Function.update s.reg rX (gmk sM)) rY (Glyph.bit true),
       Function.update (Function.update (Function.update s.stk sM R) sM (gmk sM :: R)) sM
         (Glyph.bit true ::
           (Function.update (Function.update s.stk sM R) sM (gmk sM :: R)) sM)⟩
      ⟨Function.update (Function.update (Function.update s.reg rX (gmk sM)) rY
          (Glyph.bit true)) rI gStop,
       Function.update (Function.update (Function.update s.stk sM R) sM (gmk sM :: R)) sM
         (Glyph.bit true ::
           (Function.update (Function.update s.stk sM R) sM (gmk sM :: R)) sM)⟩ 1 :=
    ev_set_st main rI gStop _
  have hbr2 : Ev main (seqs [.push sM rX, pushC sM (Glyph.bit true) rY, .set rI gStop])
      ⟨Function.update s.reg rX (gmk sM), Function.update s.stk sM R⟩
      ⟨Function.update (Function.update (Function.update s.reg rX (gmk sM)) rY
          (Glyph.bit true)) rI gStop,
       Function.update (Function.update (Function.update s.stk sM R) sM (gmk sM :: R)) sM
         (Glyph.bit true ::
           (Function.update (Function.update s.stk sM R) sM (gmk sM :: R)) sM)⟩ 4 :=
    Ev.seq' hpush (Ev.seq' hpushC hset (le_rfl)) (le_rfl)
  have hreg : (⟨Function.update s.reg rX (gmk sM),
      Function.update s.stk sM R⟩ : State).reg rX = gmk sM :=
    Function.update_self rX (gmk sM) s.reg
  have hite : Ev main (.ite rX (gmk sM)
      (seqs [.push sM rX, pushC sM (Glyph.bit true) rY, .set rI gStop])
      (seqs [.ite rX (Glyph.bit true) (pushC sT (Glyph.bit false) rY)
        (seqs [pushC sT (Glyph.bit true) rY, .set rI gStop])]))
      ⟨Function.update s.reg rX (gmk sM), Function.update s.stk sM R⟩
      ⟨Function.update (Function.update (Function.update s.reg rX (gmk sM)) rY
          (Glyph.bit true)) rI gStop,
       Function.update (Function.update (Function.update s.stk sM R) sM (gmk sM :: R)) sM
         (Glyph.bit true ::
           (Function.update (Function.update s.stk sM R) sM (gmk sM :: R)) sM)⟩ 5 :=
    Ev.iteT hreg hbr2
  have hbody : Ev main incBody s
      ⟨Function.update (Function.update (Function.update s.reg rX (gmk sM)) rY
          (Glyph.bit true)) rI gStop,
       Function.update (Function.update (Function.update s.stk sM R) sM (gmk sM :: R)) sM
         (Glyph.bit true ::
           (Function.update (Function.update s.stk sM R) sM (gmk sM :: R)) sM)⟩ 6 :=
    Ev.seq' hpop hite (le_rfl)
  obtain ⟨n, he, hn⟩ := hbody
  refine ⟨⟨Function.update (Function.update (Function.update s.reg rX (gmk sM)) rY
      (Glyph.bit true)) rI gStop,
      Function.update (Function.update (Function.update s.stk sM R) sM (gmk sM :: R)) sM
        (Glyph.bit true ::
          (Function.update (Function.update s.stk sM R) sM (gmk sM :: R)) sM)⟩,
    n, he, by omega, ?_, ?_, ?_, ?_⟩
  · show (Function.update (Function.update (Function.update s.reg rX (gmk sM)) rY
        (Glyph.bit true)) rI gStop) rI = gStop
    simp only [upReg_same]
  · show (Function.update (Function.update (Function.update s.stk sM R) sM (gmk sM :: R)) sM
        (Glyph.bit true ::
          (Function.update (Function.update s.stk sM R) sM (gmk sM :: R)) sM)) sM
      = Glyph.bit true :: gmk sM :: R
    simp only [upStk_same]
  · show (Function.update (Function.update (Function.update s.stk sM R) sM (gmk sM :: R)) sM
        (Glyph.bit true ::
          (Function.update (Function.update s.stk sM R) sM (gmk sM :: R)) sM)) sT = s.stk sT
    simp only [upStk_ne (show sT ≠ sM by decide)]
  · intro j hjM hjT
    show (Function.update (Function.update (Function.update s.stk sM R) sM (gmk sM :: R)) sM
        (Glyph.bit true ::
          (Function.update (Function.update s.stk sM R) sM (gmk sM :: R)) sM)) j = s.stk j
    simp only [upStk_ne hjT, upStk_ne hjM]

/-! ## The carry loop -/

/-- The carry loop of `incRgn`: it parks the carries on `sT` (above the marker `gmk sT`) and stops
as soon as a bit of `sM` has been flipped, or the region of `sM` ran out (in which case a fresh
`true` bit is pushed).  `JJ` is junk already sitting on `sT` above its marker. -/
theorem incLoop_ev (main : Cmd) :
    ∀ (Bs : List Bool) (JM JT JJ : List Glyph) (s : State), s.reg rI = gGo →
      s.stk sM = Bs.map Glyph.bit ++ gmk sM :: JM →
      s.stk sT = JJ ++ gmk sT :: JT →
      ∃ (s' : State) (n : ℕ), Eval main (.loop rI gGo incBody) s s' n ∧
        n ≤ 6 * (Bs.length + 1) + 2 ∧ s'.reg rI = gStop ∧
        s'.stk sM = (incRem Bs).map Glyph.bit ++ gmk sM :: JM ∧
        s'.stk sT = ((incCarry Bs).map Glyph.bit).reverse ++ JJ ++ gmk sT :: JT ∧
        (∀ j : Stk, j ≠ sM → j ≠ sT → s'.stk j = s.stk j) := by
  intro Bs
  induction Bs with
  | nil =>
      intro JM JT JJ s hreg hM hT
      have hM' : s.stk sM = gmk sM :: JM := by simpa using hM
      obtain ⟨s1, n1, he1, hn1, hr1, hM1, hT1, ho1⟩ := incBody_mark_ev main s JM hM'
      have hne : s1.reg rI ≠ gGo := by rw [hr1]; exact gStop_ne_gGo
      refine ⟨s1, n1 + 1 + 1, Eval.loopT hreg he1 (Eval.loopF hne), ?_, hr1, ?_, ?_, ho1⟩
      · simp only [List.length_nil] at *; omega
      · simpa using hM1
      · simpa [hT] using hT1
  | cons b bs ih =>
      intro JM JT JJ s hreg hM hT
      cases b with
      | true =>
          have hM' : s.stk sM = Glyph.bit true :: bs.map Glyph.bit ++ gmk sM :: JM := by
            simpa using hM
          obtain ⟨s1, n1, he1, hn1, hr1, hM1, hT1, ho1⟩ :=
            incBody_true_ev main s (bs.map Glyph.bit ++ gmk sM :: JM) hM'
          have hreg1 : s1.reg rI = gGo := by rw [hr1]; exact hreg
          have hT1' : s1.stk sT = (Glyph.bit false :: JJ) ++ gmk sT :: JT := by
            rw [hT1, hT, List.cons_append]
          obtain ⟨s2, n2, he2, hn2, hr2, hM2, hT2, ho2⟩ :=
            ih JM JT (Glyph.bit false :: JJ) s1 hreg1 hM1 hT1'
          refine ⟨s2, n1 + n2 + 1, Eval.loopT hreg he1 he2, ?_, hr2, ?_, ?_, ?_⟩
          · simp only [List.length_cons] at *; omega
          · simpa using hM2
          · rw [hT2]; simp [incCarry, List.append_assoc]
          · intro j hjM hjT
            exact (ho2 j hjM hjT).trans (ho1 j hjM hjT)
      | false =>
          have hM' : s.stk sM = Glyph.bit false :: bs.map Glyph.bit ++ gmk sM :: JM := by
            simpa using hM
          obtain ⟨s1, n1, he1, hn1, hr1, hM1, hT1, ho1⟩ :=
            incBody_false_ev main s (bs.map Glyph.bit ++ gmk sM :: JM) hM'
          have hne : s1.reg rI ≠ gGo := by rw [hr1]; exact gStop_ne_gGo
          refine ⟨s1, n1 + 1 + 1, Eval.loopT hreg he1 (Eval.loopF hne), ?_, hr1, ?_, ?_, ho1⟩
          · simp only [List.length_cons] at *; omega
          · simpa using hM1
          · rw [hT1, hT]; simp [incCarry]

/-! ## The whole word -/

theorem incRgn_ev (main : HvdH.Cmd) (Bs : List Bool) (JM JT : List HvdH.Glyph) (s : HvdH.State)
    (hM : s.stk Work.IntLib.Shift.sM =
      Bs.map HvdH.Glyph.bit ++ Work.IntLib.Shift.gmk Work.IntLib.Shift.sM :: JM)
    (hT : s.stk Work.IntLib.Shift.sT = Work.IntLib.Shift.gmk Work.IntLib.Shift.sT :: JT) :
    ∃ (s' : HvdH.State) (n : ℕ), HvdH.Eval main Work.IntLib.Shift.incRgn s s' n ∧
      n ≤ 12 * (Bs.length + 1) + 24 ∧
      s'.stk Work.IntLib.Shift.sM =
        (Work.IntLib.Shift.incList Bs).map HvdH.Glyph.bit ++ Work.IntLib.Shift.gmk Work.IntLib.Shift.sM :: JM ∧
      s'.stk Work.IntLib.Shift.sT = Work.IntLib.Shift.gmk Work.IntLib.Shift.sT :: JT ∧
      s'.reg Work.IntLib.Shift.rI ≠ Work.IntLib.Shift.gGo ∧
      (∀ j : HvdH.Stk, j ≠ Work.IntLib.Shift.sM → j ≠ Work.IntLib.Shift.sT → s'.stk j = s.stk j) := by
  obtain ⟨n0, he0, hn0⟩ := ev_set_st main rI gGo s
  have hreg0 : (⟨Function.update s.reg rI gGo, s.stk⟩ : State).reg rI = gGo :=
    Function.update_self rI gGo s.reg
  have hT0 : (⟨Function.update s.reg rI gGo, s.stk⟩ : State).stk sT = [] ++ gmk sT :: JT := by
    simpa using hT
  obtain ⟨s1, n1, he1, hn1, hr1, hM1, hT1, ho1⟩ :=
    incLoop_ev main Bs JM JT [] ⟨Function.update s.reg rI gGo, s.stk⟩ hreg0 hM hT0
  have hnm : ∀ h ∈ ((incCarry Bs).map Glyph.bit).reverse, h ≠ gmk sT := by
    intro h hh
    exact noMark_bitsG (incCarry Bs) h (List.mem_reverse.mp hh) sT
  obtain ⟨s2, n2, he2, hn2, _, hTs2, hMs2, ho2⟩ :=
    drain_ev (main := main) sT sM (gmk sT) rZ rJ (by decide : sT ≠ sM) (by decide : rJ ≠ rZ)
      (((incCarry Bs).map Glyph.bit).reverse) JT ((incRem Bs).map Glyph.bit ++ gmk sM :: JM)
      s1.reg s1.stk hnm (by rw [hT1]; simp) hM1
  refine ⟨s2, n0 + (n1 + n2), Eval.seq he0 (Eval.seq he1 he2), ?_, ?_, hTs2, ?_, ?_⟩
  · have hlen : (((incCarry Bs).map Glyph.bit).reverse).length ≤ Bs.length := by
      rw [List.length_reverse, List.length_map]
      exact incCarry_length_le Bs
    omega
  · rw [hMs2]
    calc (((incCarry Bs).map Glyph.bit).reverse).reverse
          ++ ((incRem Bs).map Glyph.bit ++ gmk sM :: JM)
        = ((incCarry Bs).map Glyph.bit) ++ ((incRem Bs).map Glyph.bit ++ gmk sM :: JM) := by
          rw [List.reverse_reverse]
      _ = ((incCarry Bs ++ incRem Bs).map Glyph.bit) ++ gmk sM :: JM := by
          rw [List.map_append, List.append_assoc]
      _ = (incList Bs).map Glyph.bit ++ gmk sM :: JM := by
          rw [incCarry_append_incRem]
  · have hfr : s2.reg rI = s1.reg rI :=
      Eval_reg_frame he2 (r := rI) (by decide)
    rw [hfr, hr1]
    exact gStop_ne_gGo
  · intro j hjM hjT
    exact (ho2 j hjT hjM).trans (ho1 j hjM hjT)

end Work.IntLib.Shift
