import Mathlib
import Submission.Work.IntLib.mulSDefs
import Submission.Work.IntLib.mulSArith

/-!
# The schoolbook multiplication word: simulation lemmas

For every phase of `mulSProg` we prove a statement of the form
`∃ s' n, Eval main p s s' n ∧ n ≤ C ∧ <stack contents of s'> ∧ <untouched stacks>`,
so that phases can be composed without ever naming intermediate states.
-/

set_option autoImplicit false

namespace Work.IntLib
namespace MulS

open HvdH

/-! ## The full adder -/

/-- Branch on a bit-valued register. -/
theorem Ev.ite_bool {main : Cmd} {r : Reg} {p q : Cmd} {s s' : State} {n : ℕ} {b : Bool}
    (h : s.reg r = .bit b) (hp : b = true → Ev main p s s' n)
    (hq : b = false → Ev main q s s' n) : Ev main (.ite r (.bit true) p q) s s' (n + 1) := by
  cases b
  · exact Ev.iteF (by rw [h]; decide) (hq rfl)
  · exact Ev.iteT h (hp rfl)

theorem ev_of_eval {main : Cmd} {p : Cmd} {s s' : State} {n : ℕ} (h : Eval main p s s' n) :
    Ev main p s s' n := ⟨n, h, le_rfl⟩

theorem faLeaf_ev {main : Cmd} {s : State} {v w : Bool} :
    Ev main (faLeaf v w) s
      ⟨Function.update (Function.update s.reg rS (.bit v)) rCy (.bit w), s.stk⟩ 2 := by
  refine Ev.seq' (ev_set main rS (.bit v) s)
    (ev_set main rCy (.bit w) (⟨Function.update s.reg rS (.bit v), s.stk⟩ : State)) (by norm_num)

theorem fullAdd_ev {main : Cmd} {s : State} {a b c : Bool}
    (ha : s.reg rA = .bit a) (hb : s.reg rRho = .bit b) (hc : s.reg rCy = .bit c) :
    Ev main fullAdd s
      ⟨Function.update (Function.update s.reg rS (.bit (faSum a b c))) rCy
        (.bit (faCarry a b c)), s.stk⟩ 5 := by
  cases a <;> cases b <;> cases c <;>
    simp only [fullAdd, faSum, faCarry] <;>
    repeat' (first
      | refine Ev.iteT ha ?_
      | refine Ev.iteF (by rw [ha]; decide) ?_
      | refine Ev.iteT hb ?_
      | refine Ev.iteF (by rw [hb]; decide) ?_
      | refine Ev.iteT hc ?_
      | refine Ev.iteF (by rw [hc]; decide) ?_
      | exact faLeaf_ev)

/-! ## Drain loops: move every glyph above a marker to another stack -/

/-- `consumeLoop` with the "move the glyph to `dst`" handler: linear cost, and no other stack
is touched. -/
theorem drain_ev {main : Cmd} {src dst : Stk} (hne : src ≠ dst) {T : Glyph} {r : Reg}
    {below : List Glyph} (ws : List Glyph) (rest : List Glyph) (s : State)
    (hsrc : s.stk src = ws ++ T :: below) (hdst : s.stk dst = rest)
    (hws : ∀ g ∈ ws, g ≠ T) (hr : s.reg r = .eos) :
    ∃ s' n, Eval main (consumeLoop src T r (.push dst r)) s s' n ∧
      n ≤ 5 * (ws.length + 1) + 1 ∧
      s'.stk src = T :: below ∧ s'.stk dst = ws.reverse ++ rest ∧
      (∀ k, k ≠ src → k ≠ dst → s'.stk k = s.stk k) ∧ s'.reg r = mkStop := by
  induction ws generalizing rest s with
  | nil =>
    simp only [List.nil_append] at hsrc
    have hpop : Ev main (.pop src r) s
        ⟨Function.update s.reg r T, Function.update s.stk src below⟩ 1 := by
      simpa [hsrc] using ev_pop main src r s
    have hpush : Ev main (.push src r)
        ⟨Function.update s.reg r T, Function.update s.stk src below⟩
        ⟨Function.update s.reg r T,
          Function.update (Function.update s.stk src below) src (T :: below)⟩ 1 := by
      have h := ev_push main src r (⟨Function.update s.reg r T,
        Function.update s.stk src below⟩ : State)
      simpa using h
    have hset : Ev main (.set r mkStop)
        ⟨Function.update s.reg r T,
          Function.update (Function.update s.stk src below) src (T :: below)⟩
        ⟨Function.update (Function.update s.reg r T) r mkStop,
          Function.update (Function.update s.stk src below) src (T :: below)⟩ 1 :=
      ev_set main r mkStop _
    have hite : Ev main
        (.ite r T (.seq (.push src r) (.set r mkStop)) (.seq (.push dst r) (.set r .eos)))
        ⟨Function.update s.reg r T, Function.update s.stk src below⟩
        ⟨Function.update (Function.update s.reg r T) r mkStop,
          Function.update (Function.update s.stk src below) src (T :: below)⟩ 3 := by
      refine Ev.iteT (by simp) ?_
      exact Ev.seq' hpush hset (by norm_num)
    have hbody : Ev main (consumeStep src T r (.push dst r)) s
        ⟨Function.update (Function.update s.reg r T) r mkStop,
          Function.update (Function.update s.stk src below) src (T :: below)⟩ 4 :=
      Ev.seq' hpop hite (by norm_num)
    have hloopF : Ev main (consumeLoop src T r (.push dst r))
        ⟨Function.update (Function.update s.reg r T) r mkStop,
          Function.update (Function.update s.stk src below) src (T :: below)⟩
        ⟨Function.update (Function.update s.reg r T) r mkStop,
          Function.update (Function.update s.stk src below) src (T :: below)⟩ 1 :=
      Ev.loopF (by simp)
    have hmain := Ev.loopT hr hbody hloopF
    obtain ⟨n, hev, hn⟩ := hmain
    exact ⟨(⟨Function.update (Function.update s.reg r T) r mkStop,
        Function.update (Function.update s.stk src below) src (T :: below)⟩ : State),
      n, hev, hn, by simp [Function.update_self],
      by simp [hdst, Function.update_of_ne (Ne.symm hne)],
      by intro k hk1 hk2; simp [Function.update_of_ne hk1, Function.update_of_ne hk2],
      by simp⟩
  | cons g gs ih =>
    simp only [List.cons_append] at hsrc
    have hg : g ≠ T := hws g (by simp)
    have hws' : ∀ x ∈ gs, x ≠ T := fun x hx => hws x (by simp [hx])
    have hpop : Ev main (.pop src r) s
        ⟨Function.update s.reg r g, Function.update s.stk src (gs ++ T :: below)⟩ 1 := by
      simpa [hsrc] using ev_pop main src r s
    have hpush : Ev main (.push dst r)
        ⟨Function.update s.reg r g, Function.update s.stk src (gs ++ T :: below)⟩
        ⟨Function.update s.reg r g,
          Function.update (Function.update s.stk src (gs ++ T :: below)) dst (g :: rest)⟩ 1 := by
      have h := ev_push main dst r (⟨Function.update s.reg r g,
        Function.update s.stk src (gs ++ T :: below)⟩ : State)
      simpa [Function.update_self, Function.update_of_ne (Ne.symm hne), hdst] using h
    have hset : Ev main (.set r .eos)
        ⟨Function.update s.reg r g,
          Function.update (Function.update s.stk src (gs ++ T :: below)) dst (g :: rest)⟩
        ⟨Function.update (Function.update s.reg r g) r .eos,
          Function.update (Function.update s.stk src (gs ++ T :: below)) dst (g :: rest)⟩ 1 :=
      ev_set main r .eos _
    have hite : Ev main
        (.ite r T (.seq (.push src r) (.set r mkStop)) (.seq (.push dst r) (.set r .eos)))
        ⟨Function.update s.reg r g, Function.update s.stk src (gs ++ T :: below)⟩
        ⟨Function.update (Function.update s.reg r g) r .eos,
          Function.update (Function.update s.stk src (gs ++ T :: below)) dst (g :: rest)⟩ 3 := by
      refine Ev.iteF ?_ ?_
      · simpa using hg
      · exact Ev.seq' hpush hset (by norm_num)
    have hbody : Ev main (consumeStep src T r (.push dst r)) s
        ⟨Function.update (Function.update s.reg r g) r .eos,
          Function.update (Function.update s.stk src (gs ++ T :: below)) dst (g :: rest)⟩ 4 :=
      Ev.seq' hpop hite (by norm_num)
    obtain ⟨s', n', hev', hn', hsrc', hdst', hfr', hr'⟩ :=
      ih (g :: rest)
        ⟨Function.update (Function.update s.reg r g) r .eos,
          Function.update (Function.update s.stk src (gs ++ T :: below)) dst (g :: rest)⟩
        (by simp [Function.update_self, Function.update_of_ne hne])
        (by simp [Function.update_self, Function.update_of_ne (Ne.symm hne)])
        hws' (by simp)
    obtain ⟨n, hev, hn⟩ := Ev.loopT hr hbody (ev_of_eval hev')
    refine ⟨s', n, hev, ?_, hsrc', ?_, ?_, hr'⟩
    · simp only [List.length_cons]; omega
    · rw [hdst', List.reverse_cons]
      simp [List.append_assoc]
    · intro k hk1 hk2
      rw [hfr' k hk1 hk2]
      simp [Function.update_of_ne hk1, Function.update_of_ne hk2]

/-- `drain` (with the initialising `set`): move every glyph above the marker `T` on `src` to `dst`,
reversing the order. -/
theorem drain_ev' {main : Cmd} {src dst : Stk} (hne : src ≠ dst) {T : Glyph} {r : Reg}
    {below : List Glyph} (ws : List Glyph) (rest : List Glyph) (s : State)
    (hsrc : s.stk src = ws ++ T :: below) (hdst : s.stk dst = rest)
    (hws : ∀ g ∈ ws, g ≠ T) :
    ∃ s' n, Eval main (drain src dst T r) s s' n ∧ n ≤ 5 * (ws.length + 1) + 2 ∧
      s'.stk src = T :: below ∧ s'.stk dst = ws.reverse ++ rest ∧
      (∀ k, k ≠ src → k ≠ dst → s'.stk k = s.stk k) := by
  have hset : Ev main (.set r .eos) s ⟨Function.update s.reg r .eos, s.stk⟩ 1 :=
    ev_set main r .eos s
  obtain ⟨s', n, hev, hn, h1, h2, h3, _⟩ :=
    drain_ev (r := r) hne ws rest (⟨Function.update s.reg r .eos, s.stk⟩ : State) hsrc hdst hws
      (by simp)
  obtain ⟨n2, hev2, hn2⟩ := Ev.seq' hset (ev_of_eval hev)
    (C := 5 * (ws.length + 1) + 2) (by omega)
  refine ⟨s', n2, hev2, hn2, h1, h2, ?_⟩
  intro k hk1 hk2
  rw [h3 k hk1 hk2]


/-! ## One iteration of the addition loop -/

theorem addStep_ev {main : Cmd} {β a r c : Bool} {α' ρ' γ τ : List Bool}
    {belowA belowR belowW belowT : List Glyph} {s : State}
    (hrCy : s.reg rCy = .bit c) (hrBit : s.reg rBit = .bit β) (hrL : s.reg rL = .eos)
    (hA : s.stk sA = Glyph.bit a :: (α'.map Glyph.bit ++ [mkA] ++ belowA))
    (hR : s.stk sR = Glyph.bit r :: (ρ'.map Glyph.bit ++ [mkR] ++ belowR))
    (hW : s.stk sW = γ.map Glyph.bit ++ [mkW] ++ belowW)
    (hT : s.stk sT = τ.map Glyph.bit ++ [mkT] ++ belowT) :
    ∃ s' n, Eval main (consumeStep sA mkA rL addABody) s s' n ∧ n ≤ 16 ∧
      s'.stk sA = α'.map Glyph.bit ++ [mkA] ++ belowA ∧
      s'.stk sR = ρ'.map Glyph.bit ++ [mkR] ++ belowR ∧
      s'.stk sW = Glyph.bit a :: (γ.map Glyph.bit ++ [mkW] ++ belowW) ∧
      s'.stk sT = Glyph.bit (faSum (if β then a else false) r c)
        :: (τ.map Glyph.bit ++ [mkT] ++ belowT) ∧
      s'.reg rCy = .bit (faCarry (if β then a else false) r c) ∧
      s'.reg rL = .eos ∧ s'.reg rBit = .bit β ∧
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
  have hstep : Ev main (consumeStep sA mkA rL addABody) s S8 16 := by
    unfold consumeStep
    refine (Ev.seq h1 (Ev.iteF (show S1.reg rL ≠ mkA by simp +decide [S1])
      (Ev.seq hbody h8))).mono ?_
    norm_num
  obtain ⟨n, hev, hn⟩ := hstep
  exact ⟨S8, n, hev, hn, k1, k2, k3, k4, k5, k6, k6b, k7⟩


/-- The addition loop: `ρ += (β ? |a| : 0)` bit by bit, saving `|a|`'s bits on `sW`, accumulating
the sum bits on `sT` and the result bits on the carry register. -/
theorem addLoop_ev {main : Cmd} {β : Bool} :
    ∀ (c : Bool) (s : State) (alp rho0 gam tav : List Bool)
      (belowA belowR belowW belowT : List Glyph),
      s.reg rCy = .bit c → s.reg rBit = .bit β → alp.length = rho0.length →
      s.stk sA = alp.map Glyph.bit ++ [mkA] ++ belowA →
      s.stk sR = rho0.map Glyph.bit ++ [mkR] ++ belowR →
      s.stk sW = gam.map Glyph.bit ++ [mkW] ++ belowW →
      s.stk sT = tav.map Glyph.bit ++ [mkT] ++ belowT →
      ∃ s' n, Eval main (consume sA mkA rL addABody) s s' n ∧ n ≤ 20 * (alp.length + 1) + 20 ∧
        s'.stk sA = [mkA] ++ belowA ∧
        s'.stk sR = [mkR] ++ belowR ∧
        s'.stk sW = alp.reverse.map Glyph.bit ++ gam.map Glyph.bit ++ [mkW] ++ belowW ∧
        s'.stk sT = (addBits (padFalse alp β) rho0 c).1.reverse.map Glyph.bit
          ++ tav.map Glyph.bit ++ [mkT] ++ belowT ∧
        s'.reg rCy = .bit (addBits (padFalse alp β) rho0 c).2 ∧
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
        ∧ n ≤ 20 * (alp.length + 1) + 18 ∧
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
      let S4 : State := ⟨Function.update S3.reg rL mkStop, S3.stk⟩
      have hS2rL : S2.reg rL = mkA := by simp +decide [S2, hA]
      have hbody : Eval main (consumeStep sA mkA rL addABody) s S4 4 := by
        unfold consumeStep
        exact Eval.seq (Eval.pop sA rL s)
          (Eval.iteT hS2rL (Eval.seq (Eval.push sA rL S2) (Eval.set rL mkStop S3)))
      have hloopF : Eval main (consumeLoop sA mkA rL addABody) S4 S4 1 := by
        unfold consumeLoop
        exact Eval.loopF (by simp +decide [S4])
      have hloop : Eval main (consumeLoop sA mkA rL addABody) s S4 6 := by
        unfold consumeLoop
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
        let S4 : State := ⟨Function.update S3.reg rL mkStop, S3.stk⟩
        have hS2rL : S2.reg rL = mkA := by simp +decide [S2, hA]
        have hbody : Eval main (consumeStep sA mkA rL addABody) s S4 4 := by
          unfold consumeStep
          exact Eval.seq (Eval.pop sA rL s)
            (Eval.iteT hS2rL (Eval.seq (Eval.push sA rL S2) (Eval.set rL mkStop S3)))
        have hloopF : Eval main (consumeLoop sA mkA rL addABody) S4 S4 1 := by
          unfold consumeLoop
          exact Eval.loopF (by simp +decide [S4])
        have hloop : Eval main (consumeLoop sA mkA rL addABody) s S4 6 := by
          unfold consumeLoop
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
            addStep_ev (main := main) (β := β) (a := a) (r := r) (c := c)
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


/-! ## The whole addition phase `addAProg` -/

private theorem headD_map_of_ne {α β : Type} {l : List α} (h : l ≠ []) (f : α → β) (d : β) (d' : α) :
    (l.map f).headD d = f (l.headD d') := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs => rfl

private theorem tail_map' {α β : Type} (l : List α) (f : α → β) :
    (l.map f).tail = l.tail.map f := by
  cases l with
  | nil => rfl
  | cons x xs => rfl

private theorem bit_ne_mkT (c : Bool) : Glyph.bit c ≠ mkT := by intro h; cases h

private theorem bit_ne_mkW (c : Bool) : Glyph.bit c ≠ mkW := by intro h; cases h

private theorem headD_append_aux {α : Type} (l₁ l₂ : List α) (d : α) :
    (l₁ ++ l₂).headD d = l₁.headD (l₂.headD d) := by
  cases l₁ with
  | nil => rfl
  | cons x xs => rfl

private theorem tail_map_append_aux {α β : Type} (l : List α) (f : α → β) (rest : List β)
    (h : l ≠ []) : (l.map f ++ rest).tail = l.tail.map f ++ rest := by
  have h' : l.map f ≠ [] := fun hc => h (List.map_eq_nil_iff.mp hc)
  rw [List.tail_append_of_ne_nil h', tail_map']

theorem addA_ev {main : Cmd} {s : State} {alp rho0 acc : List Bool} {bb : Bool}
    {belowA belowR belowC belowT belowW : List Glyph}
    (hA : s.stk sA = alp.map Glyph.bit ++ [mkA] ++ belowA)
    (hR : s.stk sR = rho0.map Glyph.bit ++ [mkR] ++ belowR)
    (hW : s.stk sW = [mkW] ++ belowW) (hT : s.stk sT = [mkT] ++ belowT)
    (hC : s.stk sC = acc.map Glyph.bit ++ [mkC] ++ belowC)
    (hb : s.reg rBit = .bit bb) (hlen : alp.length = rho0.length) :
    ∃ s' n, Eval main addAProg s s' n ∧ n ≤ 40 * (alp.length + 1) + 60 ∧
      s'.stk sA = alp.map Glyph.bit ++ [mkA] ++ belowA ∧
      s'.stk sR = (stepR alp rho0 bb).2.map Glyph.bit ++ [mkR] ++ belowR ∧
      s'.stk sC = Glyph.bit (stepR alp rho0 bb).1 :: acc.map Glyph.bit ++ [mkC] ++ belowC ∧
      s'.stk sW = [mkW] ++ belowW ∧ s'.stk sT = [mkT] ++ belowT ∧
      (∀ k, k ≠ sA → k ≠ sR → k ≠ sC → k ≠ sW → k ≠ sT → s'.stk k = s.stk k) := by
  -- ## Step 1: clear the carry
  let S1 : State := ⟨Function.update s.reg rCy (Glyph.bit false), s.stk⟩
  have h1 : Eval main (.set rCy (.bit false)) s S1 1 := by
    dsimp only [S1]; exact Eval.set rCy (.bit false) s
  have hS1cy : S1.reg rCy = .bit false := by simp [S1]
  have hS1bit : S1.reg rBit = .bit bb := by
    dsimp only [S1]
    rw [Function.update_of_ne (by decide : (rBit : Reg) ≠ rCy)]
    exact hb
  have hS1A : S1.stk sA = alp.map Glyph.bit ++ [mkA] ++ belowA := hA
  have hS1R : S1.stk sR = rho0.map Glyph.bit ++ [mkR] ++ belowR := hR
  have hS1W : S1.stk sW = [mkW] ++ belowW := hW
  have hS1T : S1.stk sT = [mkT] ++ belowT := hT
  -- ## Step 2: the addition loop
  obtain ⟨S2, n2, h2, hn2, gA, gR, gW, gT, gcy, gfr⟩ :=
    addLoop_ev (main := main) (β := bb) false S1 alp rho0 [] [] belowA belowR belowW belowT
      hS1cy hS1bit hlen hS1A hS1R hS1W hS1T
  set sc : List Bool × Bool := addBits (padFalse alp bb) rho0 false with hsc
  set L : List Bool := sc.1 ++ [sc.2] with hL
  simp only [List.map_nil, List.append_nil] at gW gT
  have hsc1len : sc.1.length = alp.length := by
    rw [hsc]
    rw [addBits_len (padFalse alp bb) rho0 (by rw [padFalse_length, hlen]) false, padFalse_length]
  have hLne : L ≠ [] := by
    rw [hL]
    intro hc
    exact List.cons_ne_nil sc.2 [] (List.append_eq_nil_iff.mp hc).2
  -- ## Step 3: push the carry onto sT
  let S3 : State := ⟨S2.reg, Function.update S2.stk sT (S2.reg rCy :: S2.stk sT)⟩
  have h3 : Eval main (.push sT rCy) S2 S3 1 := by dsimp only [S3]; exact Eval.push sT rCy S2
  have h3T : S3.stk sT = (Glyph.bit sc.2 :: sc.1.reverse.map Glyph.bit) ++ mkT :: belowT := by
    dsimp only [S3]
    rw [Function.update_self, gcy, gT]
    simp only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]
  have h3R : S3.stk sR = [mkR] ++ belowR := by
    dsimp only [S3]
    rw [Function.update_of_ne (by decide : (sR : Stk) ≠ sT)]
    exact gR
  have h3ws : ∀ g ∈ (Glyph.bit sc.2 :: sc.1.reverse.map Glyph.bit), g ≠ mkT := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact bit_ne_mkT _
    · obtain ⟨b, _, rfl⟩ := List.mem_map.mp hg
      exact bit_ne_mkT _
  -- ## Step 4: drain sT -> sR
  obtain ⟨S4, n4, h4, hn4, g4T, g4R, g4fr⟩ :=
    drain_ev' (main := main) (src := sT) (dst := sR) (hne := (by decide : sT ≠ sR))
      (T := mkT) (r := rL) (below := belowT)
      (Glyph.bit sc.2 :: sc.1.reverse.map Glyph.bit) ([mkR] ++ belowR) S3 h3T h3R h3ws
  have g4R' : S4.stk sR = L.map Glyph.bit ++ ([mkR] ++ belowR) := by
    rw [g4R, hL]
    simp only [List.reverse_cons, List.map_reverse, List.reverse_reverse, List.map_append,
      List.map_cons, List.map_nil]
  have h4A : S4.stk sA = [mkA] ++ belowA := by
    rw [g4fr sA (by decide) (by decide)]
    dsimp only [S3]
    rw [Function.update_of_ne (by decide : (sA : Stk) ≠ sT)]
    exact gA
  have h4W : S4.stk sW = alp.reverse.map Glyph.bit ++ [mkW] ++ belowW := by
    rw [g4fr sW (by decide) (by decide)]
    dsimp only [S3]
    rw [Function.update_of_ne (by decide : (sW : Stk) ≠ sT)]
    exact gW
  have h4W' : S4.stk sW = alp.reverse.map Glyph.bit ++ mkW :: belowW := by
    rw [h4W, List.append_assoc, List.singleton_append]
  have h4ws : ∀ g ∈ alp.reverse.map Glyph.bit, g ≠ mkW := by
    intro g hg
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hg
    exact bit_ne_mkW _
  -- ## Step 5: drain sW -> sA
  obtain ⟨S5, n5, h5, hn5, g5W, g5A, g5fr⟩ :=
    drain_ev' (main := main) (src := sW) (dst := sA) (hne := (by decide : sW ≠ sA))
      (T := mkW) (r := rL) (below := belowW)
      (alp.reverse.map Glyph.bit) ([mkA] ++ belowA) S4 h4W' h4A h4ws
  have g5W' : S5.stk sW = [mkW] ++ belowW := by
    rw [g5W, List.singleton_append]
  have g5A' : S5.stk sA = alp.map Glyph.bit ++ [mkA] ++ belowA := by
    rw [g5A, List.map_reverse, List.reverse_reverse, List.append_assoc]
  -- ## Step 6: pop sR -> rOut
  have h5R : S5.stk sR = L.map Glyph.bit ++ ([mkR] ++ belowR) := by
    rw [g5fr sR (by decide) (by decide)]
    exact g4R'
  let S6 : State := ⟨Function.update S5.reg rOut ((S5.stk sR).headD .eos),
    Function.update S5.stk sR ((S5.stk sR).tail)⟩
  have h6 : Eval main (.pop sR rOut) S5 S6 1 := by dsimp only [S6]; exact Eval.pop sR rOut S5
  have h6out : S6.reg rOut = Glyph.bit (L.headD false) := by
    have hA1 : S6.reg rOut = (S5.stk sR).headD Glyph.eos := by
      dsimp only [S6]; rw [Function.update_self]
    rw [hA1, h5R]
    rw [headD_append_aux]
    exact headD_map_of_ne hLne Glyph.bit _ false
  have h6R : S6.stk sR = L.tail.map Glyph.bit ++ [mkR] ++ belowR := by
    have hA1 : S6.stk sR = (S5.stk sR).tail := by
      dsimp only [S6]; rw [Function.update_self]
    rw [hA1, h5R, tail_map_append_aux L Glyph.bit ([mkR] ++ belowR) hLne]
    rw [List.append_assoc]
  have h6A : S6.stk sA = alp.map Glyph.bit ++ [mkA] ++ belowA := by
    have hA1 : S6.stk sA = S5.stk sA := by
      dsimp only [S6]; rw [Function.update_of_ne (by decide : (sA : Stk) ≠ sR)]
    rw [hA1]; exact g5A'
  have h6W : S6.stk sW = [mkW] ++ belowW := by
    have hA1 : S6.stk sW = S5.stk sW := by
      dsimp only [S6]; rw [Function.update_of_ne (by decide : (sW : Stk) ≠ sR)]
    rw [hA1]; exact g5W'
  have h6T : S6.stk sT = mkT :: belowT := by
    have hA1 : S6.stk sT = S5.stk sT := by
      dsimp only [S6]; rw [Function.update_of_ne (by decide : (sT : Stk) ≠ sR)]
    have hA2 : S5.stk sT = S4.stk sT := g5fr sT (by decide) (by decide)
    rw [hA1, hA2]; exact g4T
  have h6C : S6.stk sC = acc.map Glyph.bit ++ [mkC] ++ belowC := by
    have hA1 : S6.stk sC = S5.stk sC := by
      dsimp only [S6]; rw [Function.update_of_ne (by decide : (sC : Stk) ≠ sR)]
    have hA2 : S5.stk sC = S4.stk sC := g5fr sC (by decide) (by decide)
    have hA3 : S4.stk sC = S3.stk sC := g4fr sC (by decide) (by decide)
    have hA4 : S3.stk sC = S2.stk sC := by
      dsimp only [S3]; rw [Function.update_of_ne (by decide : (sC : Stk) ≠ sT)]
    have hA5 : S2.stk sC = S1.stk sC := gfr sC (by decide) (by decide) (by decide) (by decide)
    rw [hA1, hA2, hA3, hA4, hA5]
    exact hC
  -- ## Step 7: push the output bit onto sC
  let S7 : State := ⟨S6.reg, Function.update S6.stk sC (S6.reg rOut :: S6.stk sC)⟩
  have h7 : Eval main (.push sC rOut) S6 S7 1 := by dsimp only [S7]; exact Eval.push sC rOut S6
  have hsR1 : (stepR alp rho0 bb).1 = L.headD false := by dsimp only [stepR]
  have hsR2 : (stepR alp rho0 bb).2 = L.tail := by dsimp only [stepR]
  -- ## Compose
  have e67 : Eval main (.seq (.pop sR rOut) (.push sC rOut)) S5 S7 (1 + 1) := Eval.seq h6 h7
  have e567 : Eval main (.seq (drain sW sA mkW rL) (.seq (.pop sR rOut) (.push sC rOut))) S4 S7
      (n5 + (1 + 1)) := Eval.seq h5 e67
  have e4567 : Eval main
      (.seq (drain sT sR mkT rL) (.seq (drain sW sA mkW rL) (.seq (.pop sR rOut) (.push sC rOut))))
      S3 S7 (n4 + (n5 + (1 + 1))) := Eval.seq h4 e567
  have e34567 : Eval main
      (.seq (.push sT rCy) (.seq (drain sT sR mkT rL)
        (.seq (drain sW sA mkW rL) (.seq (.pop sR rOut) (.push sC rOut)))))
      S2 S7 (1 + (n4 + (n5 + (1 + 1)))) := Eval.seq h3 e4567
  have e234567 : Eval main
      (.seq (consume sA mkA rL addABody) (.seq (.push sT rCy) (.seq (drain sT sR mkT rL)
        (.seq (drain sW sA mkW rL) (.seq (.pop sR rOut) (.push sC rOut))))))
      S1 S7 (n2 + (1 + (n4 + (n5 + (1 + 1))))) := Eval.seq h2 e34567
  have hprog : addAProg = .seq (.set rCy (.bit false))
      (.seq (consume sA mkA rL addABody) (.seq (.push sT rCy) (.seq (drain sT sR mkT rL)
        (.seq (drain sW sA mkW rL) (.seq (.pop sR rOut) (.push sC rOut)))))) := by
    simp only [addAProg, drain, seqs]
  have hfinal : Eval main addAProg s S7 (1 + (n2 + (1 + (n4 + (n5 + (1 + 1)))))) := by
    rw [hprog]
    exact Eval.seq h1 e234567
  -- ## Cost
  have hws1 : (Glyph.bit sc.2 :: sc.1.reverse.map Glyph.bit).length = alp.length + 1 := by
    simp only [List.length_cons, List.length_map, List.length_reverse, hsc1len]
  have hws2 : (alp.reverse.map Glyph.bit).length = alp.length := by
    simp only [List.length_map, List.length_reverse]
  have hcost : 1 + (n2 + (1 + (n4 + (n5 + (1 + 1))))) ≤ 40 * (alp.length + 1) + 60 := by
    simp only [hws1, hws2] at hn4 hn5
    omega
  refine ⟨S7, 1 + (n2 + (1 + (n4 + (n5 + (1 + 1))))), hfinal, hcost, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show S7.stk sA = S6.stk sA from by
      dsimp only [S7]; rw [Function.update_of_ne (by decide : (sA : Stk) ≠ sC)]]
    exact h6A
  · rw [show S7.stk sR = S6.stk sR from by
      dsimp only [S7]; rw [Function.update_of_ne (by decide : (sR : Stk) ≠ sC)]]
    rw [h6R, hsR2]
  · have hA1 : S7.stk sC = S6.reg rOut :: S6.stk sC := by
      dsimp only [S7]; rw [Function.update_self]
    rw [hA1, h6out, ← hsR1, h6C]
    simp only [List.cons_append, List.append_assoc, List.singleton_append]
  · rw [show S7.stk sW = S6.stk sW from by
      dsimp only [S7]; rw [Function.update_of_ne (by decide : (sW : Stk) ≠ sC)]]
    exact h6W
  · rw [show S7.stk sT = S6.stk sT from by
      dsimp only [S7]; rw [Function.update_of_ne (by decide : (sT : Stk) ≠ sC)]]
    rw [h6T, List.singleton_append]
  · intro k h1k h2k h3k h4k h5k
    have e7 : S7.stk k = S6.stk k := by
      dsimp only [S7]; rw [Function.update_of_ne (show k ≠ sC from h3k)]
    have e6 : S6.stk k = S5.stk k := by
      dsimp only [S6]; rw [Function.update_of_ne (show k ≠ sR from h2k)]
    have e5 : S5.stk k = S4.stk k := g5fr k (show k ≠ sW from h4k) (show k ≠ sA from h1k)
    have e4 : S4.stk k = S3.stk k := g4fr k (show k ≠ sT from h5k) (show k ≠ sR from h2k)
    have e3 : S3.stk k = S2.stk k := by
      dsimp only [S3]; rw [Function.update_of_ne (show k ≠ sT from h5k)]
    have e2 : S2.stk k = S1.stk k := gfr k h1k h2k h4k h5k
    rw [e7, e6, e5, e4, e3, e2]

end MulS
end Work.IntLib
