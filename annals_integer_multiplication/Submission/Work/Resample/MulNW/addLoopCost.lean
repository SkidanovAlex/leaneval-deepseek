import Mathlib
import Submission.Work.Resample.MulNW.Defs

/-!
# `Work.Resample.MulNW.addLoopCost`

The inner addition loop `consume sA mkA rL addABody` of the schoolbook multiplier, with the tight
cost bound `17 * (|a| + 1)`: it consumes the `|a|` bits of `a` on `sA` and the `|a|` bits of the
remainder `ρ` on `sR`, saving the bits of `a` (reversed) on `sW`, the sum bits on `sT`, and the
final carry in the register `rCy`.

This is the tight version of `Work.IntLib.MulS.addLoop_ev` (which is stated for the `MulS` copy of
`consume`, whose stop glyph is `mkStop` rather than `mk 0`, and with a loose bound).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Resample.MulNW

open HvdH
open Work.IntLib.MulS

/-- One iteration of the `Work.IntLib` consume loop with handler `addABody`: pop a bit `a` of `α`
from `sA` (saving it on `sW`), pop the next bit `r` of `ρ` from `sR`, add `(β ? a : 0)`, `r` and the
carry `c`, push the sum bit on `sT` and keep the carry in `rCy`. -/
private theorem addStepG {main : Cmd} {β a r c : Bool} {α' ρ' γ τ : List Bool}
    {belowA belowR belowW belowT : List Glyph} {s : State}
    (hrCy : s.reg rCy = Glyph.bit c) (hrBit : s.reg rBit = Glyph.bit β)
    (hrL : s.reg rL = Glyph.eos)
    (hA : s.stk sA = Glyph.bit a :: (α'.map Glyph.bit ++ [mkA] ++ belowA))
    (hR : s.stk sR = Glyph.bit r :: (ρ'.map Glyph.bit ++ [mkR] ++ belowR))
    (hW : s.stk sW = γ.map Glyph.bit ++ [mkW] ++ belowW)
    (hT : s.stk sT = τ.map Glyph.bit ++ [mkT] ++ belowT) :
    ∃ s' n, Eval main (Work.IntLib.consumeStep sA mkA rL addABody) s s' n ∧ n ≤ 14 ∧
      s'.stk sA = α'.map Glyph.bit ++ [mkA] ++ belowA ∧
      s'.stk sR = ρ'.map Glyph.bit ++ [mkR] ++ belowR ∧
      s'.stk sW = Glyph.bit a :: (γ.map Glyph.bit ++ [mkW] ++ belowW) ∧
      s'.stk sT = Glyph.bit (faSum (if β then a else false) r c)
        :: (τ.map Glyph.bit ++ [mkT] ++ belowT) ∧
      s'.reg rCy = Glyph.bit (faCarry (if β then a else false) r c) ∧
      s'.reg rL = Glyph.eos ∧ s'.reg rBit = Glyph.bit β ∧
      (∀ k, k ≠ sA → k ≠ sR → k ≠ sW → k ≠ sT → s'.stk k = s.stk k) := by
  let S1 : State := ⟨Function.update s.reg rL (Glyph.bit a),
    Function.update s.stk sA (α'.map Glyph.bit ++ [mkA] ++ belowA)⟩
  let S2 : State := ⟨S1.reg, Function.update S1.stk sW (S1.reg rL :: S1.stk sW)⟩
  let S3 : State := ⟨Function.update S2.reg rRho ((S2.stk sR).headD .eos),
    Function.update S2.stk sR ((S2.stk sR).tail)⟩
  let S4 : State := ⟨Function.update S3.reg rA (S3.reg rL), S3.stk⟩
  let S5 : State := ⟨Function.update S4.reg rA (.bit (if β then a else false)), S4.stk⟩
  let S6 : State := ⟨Function.update (Function.update S5.reg rS
      (.bit (faSum (if β then a else false) r c))) rCy
      (.bit (faCarry (if β then a else false) r c)), S5.stk⟩
  let S7 : State := ⟨S6.reg, Function.update S6.stk sT (S6.reg rS :: S6.stk sT)⟩
  let S8 : State := ⟨Function.update S7.reg rL Glyph.eos, S7.stk⟩
  have k1 : S8.stk sA = α'.map Glyph.bit ++ [mkA] ++ belowA := by
    simp +decide [S8, S7, S6, S5, S4, S3, S2, S1]
  have k2 : S8.stk sR = ρ'.map Glyph.bit ++ [mkR] ++ belowR := by
    simp +decide [S8, S7, S6, S5, S4, S3, S2, S1, hR]
  have k3 : S8.stk sW = Glyph.bit a :: (γ.map Glyph.bit ++ [mkW] ++ belowW) := by
    simp +decide [S8, S7, S6, S5, S4, S3, S2, S1, hW]
  have k4 : S8.stk sT = Glyph.bit (faSum (if β then a else false) r c)
      :: (τ.map Glyph.bit ++ [mkT] ++ belowT) := by
    simp +decide [S8, S7, S6, S5, S4, S3, S2, S1, hT]
  have k5 : S8.reg rCy = .bit (faCarry (if β then a else false) r c) := by
    simp +decide [S8, S7, S6, S5, S4, S3, S2, S1]
  have k6 : S8.reg rL = Glyph.eos := by simp +decide [S8, S7, S6]
  have k6b : S8.reg rBit = .bit β := by simp +decide [S8, S7, S6, S5, S4, S3, S2, S1, hrBit]
  have k7 : ∀ k, k ≠ sA → k ≠ sR → k ≠ sW → k ≠ sT → S8.stk k = s.stk k := by
    intro k h1 h2 h3 h4
    simp +decide [S8, S7, S6, S5, S4, S3, S2, S1, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, Function.update_of_ne h4]
  have h1 : Ev main (.pop sA rL) s S1 1 := by
    dsimp only [S1]; simpa [hA] using ev_pop main sA rL s
  have h2 : Ev main (.push sW rL) S1 S2 1 := by dsimp only [S2]; exact ev_push main sW rL S1
  have h3 : Ev main (.pop sR rRho) S2 S3 1 := by dsimp only [S3]; exact ev_pop main sR rRho S2
  have h4 : Ev main (.mov rA rL) S3 S4 1 := by dsimp only [S4]; exact ev_mov main rA rL S3
  have h4rA : S4.reg rA = Glyph.bit a := by simp +decide [S4, S3, S2, S1]
  have h5 : Ev main (.ite rBit (.bit true) .skip (.set rA (.bit false))) S4 S5 2 := by
    refine Ev.ite_bool (b := β) (s := S4) (s' := S5) ?_ ?_ ?_
    · simp +decide [S4, S3, S2, S1, hrBit]
    · intro hb
      have hst : S4 = S5 := by
        have hrr : S4.reg = Function.update S4.reg rA (Glyph.bit a) := by
          funext j
          by_cases hj : j = rA
          · subst hj; simp [h4rA]
          · simp [Function.update_of_ne hj]
        simp only [S5, hb, ite_true]
        exact State.ext' hrr rfl
      rw [← hst]
      exact ev_skip main S4
    · intro hb
      have hst : S5 = (⟨Function.update S4.reg rA (.bit false), S4.stk⟩ : State) := by
        simp +decide [S5, hb]
      rw [hst]; exact ev_set main rA (.bit false) S4
  have h6 : Ev main fullAdd S5 S6 5 := by
    dsimp only [S6]
    refine fullAdd_ev (s := S5) ?_ ?_ ?_
    · simp +decide [S5]
    · simp +decide [S5, S4, S3, S2, S1, hR]
    · simp +decide [S5, S4, S3, S2, S1, hrCy]
  have h7 : Ev main (.push sT rS) S6 S7 1 := by dsimp only [S7]; exact ev_push main sT rS S6
  have h8 : Ev main (.set rL Glyph.eos) S7 S8 1 := by dsimp only [S8]; exact ev_set main rL Glyph.eos S7
  have hbody : Ev main addABody S1 S7 11 := by
    unfold addABody
    exact (Ev.seq h2 (Ev.seq h3 (Ev.seq h4 (Ev.seq h5 (Ev.seq h6 h7))))).mono (by norm_num)
  have hstep : Ev main (Work.IntLib.consumeStep sA mkA rL addABody) s S8 14 := by
    unfold Work.IntLib.consumeStep
    refine (Ev.seq h1 (Ev.iteF (show S1.reg rL ≠ mkA by simp +decide [S1])
      (Ev.seq hbody h8))).mono ?_
    norm_num
  obtain ⟨n, hev, hn⟩ := hstep
  exact ⟨S8, n, hev, hn, k1, k2, k3, k4, k5, k6, k6b, k7⟩

theorem addLoopCost (main : HvdH.Cmd) (β : Bool) :
    ∀ (c : Bool) (s : HvdH.State) (alp rho0 gam tav : List Bool)
      (belowA belowR belowW belowT : List HvdH.Glyph),
      s.reg rCy = HvdH.Glyph.bit c → s.reg rBit = HvdH.Glyph.bit β →
      alp.length = rho0.length →
      s.stk sA = alp.map HvdH.Glyph.bit ++ [mkA] ++ belowA →
      s.stk sR = rho0.map HvdH.Glyph.bit ++ [mkR] ++ belowR →
      s.stk sW = gam.map HvdH.Glyph.bit ++ [mkW] ++ belowW →
      s.stk sT = tav.map HvdH.Glyph.bit ++ [mkT] ++ belowT →
      ∃ s' n, HvdH.Eval main (consume sA mkA rL addABody) s s' n ∧ n ≤ 17 * (alp.length + 1) ∧
        s'.stk sA = [mkA] ++ belowA ∧
        s'.stk sR = [mkR] ++ belowR ∧
        s'.stk sW = alp.reverse.map HvdH.Glyph.bit ++ gam.map HvdH.Glyph.bit ++ [mkW] ++ belowW ∧
        s'.stk sT = (Work.IntLib.MulS.addBits (Work.IntLib.MulS.padFalse alp β) rho0 c).1.reverse.map HvdH.Glyph.bit
            ++ tav.map HvdH.Glyph.bit ++ [mkT] ++ belowT ∧
        s'.reg rCy = HvdH.Glyph.bit (Work.IntLib.MulS.addBits (Work.IntLib.MulS.padFalse alp β) rho0 c).2 ∧
        (∀ k, k ≠ sA → k ≠ sR → k ≠ sW → k ≠ sT → s'.stk k = s.stk k) := by
  have haux : ∀ (m : ℕ) (c : Bool) (s : State) (alp rho0 gam tav : List Bool)
      (belowA belowR belowW belowT : List Glyph), alp.length ≤ m →
      s.reg rCy = .bit c → s.reg rBit = .bit β → alp.length = rho0.length →
      s.reg rL = Glyph.eos →
      s.stk sA = alp.map Glyph.bit ++ [mkA] ++ belowA →
      s.stk sR = rho0.map Glyph.bit ++ [mkR] ++ belowR →
      s.stk sW = gam.map Glyph.bit ++ [mkW] ++ belowW →
      s.stk sT = tav.map Glyph.bit ++ [mkT] ++ belowT →
      ∃ s' n, Eval main (consumeLoop sA mkA rL addABody) s s' n
        ∧ n ≤ 17 * alp.length + 16 ∧
        s'.stk sA = [mkA] ++ belowA ∧
        s'.stk sR = [mkR] ++ belowR ∧
        s'.stk sW = alp.reverse.map Glyph.bit ++ gam.map Glyph.bit ++ [mkW] ++ belowW ∧
        s'.stk sT = (addBits (padFalse alp β) rho0 c).1.reverse.map Glyph.bit
          ++ tav.map Glyph.bit ++ [mkT] ++ belowT ∧
        s'.reg rCy = .bit (addBits (padFalse alp β) rho0 c).2 ∧
        (∀ k, k ≠ sA → k ≠ sR → k ≠ sW → k ≠ sT → s'.stk k = s.stk k) := by
    intro m
    induction m with
    | zero =>
      intro c s alp rho0 gam tav belowA belowR belowW belowT hle hrCy hrBit hlen hrL hA hR hW hT
      have halp : alp = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hle)
      subst halp
      have hrho0 : rho0 = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst hrho0
      simp only [List.map_nil, List.nil_append] at hA hR
      let S2 : State := ⟨Function.update s.reg rL ((s.stk sA).headD Glyph.eos),
        Function.update s.stk sA ((s.stk sA).tail)⟩
      let S3 : State := ⟨S2.reg, Function.update S2.stk sA (S2.reg rL :: S2.stk sA)⟩
      let S4 : State := ⟨Function.update S3.reg rL (Glyph.mk 0), S3.stk⟩
      have hS2rL : S2.reg rL = mkA := by simp +decide [S2, hA]
      have hbody : Eval main (Work.IntLib.consumeStep sA mkA rL addABody) s S4 4 := by
        unfold Work.IntLib.consumeStep
        exact Eval.seq (Eval.pop sA rL s)
          (Eval.iteT hS2rL (Eval.seq (Eval.push sA rL S2) (Eval.set rL (Glyph.mk 0) S3)))
      have hloopF : Eval main (consumeLoop sA mkA rL addABody) S4 S4 1 := by
        exact Eval.loopF (by simp +decide [S4])
      have hloop : Eval main (consumeLoop sA mkA rL addABody) s S4 6 := by
        exact Eval.loopT hrL hbody hloopF
      refine ⟨S4, 6, hloop, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp +decide [S4, S3, S2, hA]
      · simp +decide [S4, S3, S2, hR]
      · simp +decide [S4, S3, S2, hW]
      · simp +decide [S4, S3, S2, hT, addBits, padFalse]
      · simp +decide [S4, S3, S2, addBits, padFalse, hrCy]
      · intro k h1 h2 h3 h4
        simp +decide [S4, S3, S2, Function.update_of_ne h1, Function.update_of_ne h2,
          Function.update_of_ne h3, Function.update_of_ne h4]
    | succ m ih =>
      intro c s alp rho0 gam tav belowA belowR belowW belowT hle hrCy hrBit hlen hrL hA hR hW hT
      cases alp with
      | nil =>
        have hrho0 : rho0 = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
        subst hrho0
        simp only [List.map_nil, List.nil_append] at hA hR
        let S2 : State := ⟨Function.update s.reg rL ((s.stk sA).headD Glyph.eos),
          Function.update s.stk sA ((s.stk sA).tail)⟩
        let S3 : State := ⟨S2.reg, Function.update S2.stk sA (S2.reg rL :: S2.stk sA)⟩
        let S4 : State := ⟨Function.update S3.reg rL (Glyph.mk 0), S3.stk⟩
        have hS2rL : S2.reg rL = mkA := by simp +decide [S2, hA]
        have hbody : Eval main (Work.IntLib.consumeStep sA mkA rL addABody) s S4 4 := by
          unfold Work.IntLib.consumeStep
          exact Eval.seq (Eval.pop sA rL s)
            (Eval.iteT hS2rL (Eval.seq (Eval.push sA rL S2) (Eval.set rL (Glyph.mk 0) S3)))
        have hloopF : Eval main (consumeLoop sA mkA rL addABody) S4 S4 1 := by
          exact Eval.loopF (by simp +decide [S4])
        have hloop : Eval main (consumeLoop sA mkA rL addABody) s S4 6 := by
          exact Eval.loopT hrL hbody hloopF
        refine ⟨S4, 6, hloop, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp +decide [S4, S3, S2, hA]
        · simp +decide [S4, S3, S2, hR]
        · simp +decide [S4, S3, S2, hW]
        · simp +decide [S4, S3, S2, hT, addBits, padFalse]
        · simp +decide [S4, S3, S2, addBits, padFalse, hrCy]
        · intro k h1 h2 h3 h4
          simp +decide [S4, S3, S2, Function.update_of_ne h1, Function.update_of_ne h2,
            Function.update_of_ne h3, Function.update_of_ne h4]
      | cons a alp' =>
        cases rho0 with
        | nil => simp at hlen
        | cons r rho' =>
          have hlen' : alp'.length = rho'.length := by simpa using hlen
          have hle' : alp'.length ≤ m := by
            simp only [List.length_cons] at hle; omega
          obtain ⟨S2, n2, hev2, hn2, f2a, f2r, f2w, f2t, f2c, f2l, f2bit, f2fr⟩ :=
            addStepG (main := main) (β := β) (a := a) (r := r) (c := c)
              (α' := alp') (ρ' := rho') (γ := gam) (τ := tav) hrCy hrBit hrL hA hR hW hT
          have h2W : S2.stk sW = (a :: gam).map Glyph.bit ++ [mkW] ++ belowW := by
            simpa [List.map_cons, List.cons_append, List.append_assoc] using f2w
          have h2T : S2.stk sT = (faSum (if β then a else false) r c :: tav).map Glyph.bit
              ++ [mkT] ++ belowT := by
            simpa [List.map_cons, List.cons_append, List.append_assoc] using f2t
          obtain ⟨S3, n3, hev3, hn3, g3a, g3r, g3w, g3t, g3c, g3fr⟩ :=
            ih (faCarry (if β then a else false) r c) S2 alp' rho' (a :: gam)
              (faSum (if β then a else false) r c :: tav) belowA belowR belowW belowT hle'
              f2c f2bit hlen' f2l f2a f2r h2W h2T
          have hloop : Eval main (consumeLoop sA mkA rL addABody) s S3 (n2 + n3 + 1) :=
            Eval.loopT hrL hev2 hev3
          refine ⟨S3, n2 + n3 + 1, hloop, ?_, g3a, g3r, ?_, ?_, ?_, ?_⟩
          · rw [List.length_cons]
            omega
          · simp only [g3w, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
              List.append_assoc, List.singleton_append, List.nil_append]
          · simp only [g3t, padFalse_cons, addBits_cons, List.reverse_cons, List.map_append,
              List.map_cons, List.map_nil, List.append_assoc, List.singleton_append, List.nil_append]
          · simp only [g3c, padFalse_cons, addBits_cons]
          · intro k h1 h2 h3 h4
            rw [g3fr k h1 h2 h3 h4, f2fr k h1 h2 h3 h4]
  intro c s alp rho0 gam tav belowA belowR belowW belowT hrCy hrBit hlen hA hR hW hT
  let S0 : State := ⟨Function.update s.reg rL Glyph.eos, s.stk⟩
  have hset : Eval main (.set rL Glyph.eos) s S0 1 := Eval.set rL Glyph.eos s
  have hS0rL : S0.reg rL = Glyph.eos := by simp +decide [S0]
  have hS0A : S0.stk sA = alp.map Glyph.bit ++ [mkA] ++ belowA := by simp +decide [S0, hA]
  obtain ⟨s', n', hev', hn', f1, f2, f3, f4, f5, f6⟩ :=
    haux alp.length c S0 alp rho0 gam tav belowA belowR belowW belowT le_rfl hrCy hrBit hlen
      hS0rL hS0A hR hW hT
  exact ⟨s', 1 + n', Eval.seq hset hev', by omega, f1, f2, f3, f4, f5, f6⟩

end Work.Resample.MulNW
