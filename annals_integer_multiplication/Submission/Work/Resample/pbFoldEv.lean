import Mathlib
import Submission.Work.Resample.pbKit
import Submission.Work.Layout.Move
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.Layout.Base
import Submission.Work.IntLib.encodeNatBridge

namespace Work.Resample

open HvdH
open Work.Layout

/-! ## Small encoding / arithmetic helpers -/

private theorem intList_cons_enc (t : ℕ) (rest : List ℕ) :
    (HvdH.intList (t :: rest)).enc =
      Glyph.cons :: ((HvdH.Val.int (t : ℤ)).enc ++ (HvdH.intList rest).enc) := rfl

private theorem intList_nil_enc : (HvdH.intList ([] : List ℕ)).enc = [Glyph.nil] := rfl

private theorem vsz_int_eq_isz (z : ℤ) : HvdH.vsz (HvdH.Val.int z) = HvdH.isz z :=
  Work.IntLib.vsz_int z

private theorem encs_cons'_rp (v : HvdH.Val) (vs : List HvdH.Val) :
    HvdH.encs (v :: vs) = v.enc ++ HvdH.encs vs := rfl

private theorem prod_nil_one : ([] : List ℕ).prod = 1 := List.prod_nil

private theorem one_le_prod (l : List ℕ) (h : ∀ t ∈ l, 1 ≤ t) : 1 ≤ l.prod := by
  induction l with
  | nil => simp [List.prod_nil]
  | cons t rest ih =>
      have ht : 1 ≤ t := h t (List.mem_cons_self ..)
      have hr : 1 ≤ rest.prod := ih (fun u hu => h u (List.mem_cons_of_mem t hu))
      rw [List.prod_cons]
      have := Nat.mul_le_mul ht hr
      simpa using this

/-- The per-iteration budget, in the form needed to telescope along the fold: the cost of one
`cons` iteration (with accumulator `P`, factor `t`, and a global size cap `N ≥ P`) is at most
`(16 + Km + 10) * (isz t + 1) * (N.size + 2)`. -/
private theorem pbFoldStepBudget (Km P t N : ℕ) (hPN : P ≤ N) :
    5 + 16 * (HvdH.isz (t : ℤ) + 1) + Km * (t.size + 1) * (P.size + 1)
      ≤ (16 + Km + 10) * (HvdH.isz (t : ℤ) + 1) * (N.size + 2) := by
  have hsz : P.size ≤ N.size := Nat.size_le_size hPN
  have htm : t.size + 1 ≤ HvdH.isz (t : ℤ) + 1 := by
    rw [HvdH.isz, Int.natAbs_natCast]; omega
  have hPNm : P.size + 1 ≤ N.size + 2 := by omega
  have h1 : 5 ≤ 5 * ((HvdH.isz (t : ℤ) + 1) * (N.size + 2)) :=
    Nat.le_mul_of_pos_right 5 (Nat.mul_pos (by omega) (by omega))
  have h2 : 16 * (HvdH.isz (t : ℤ) + 1) ≤ 16 * ((HvdH.isz (t : ℤ) + 1) * (N.size + 2)) :=
    Nat.mul_le_mul_left 16 (Nat.le_mul_of_pos_right _ (by omega))
  have h3 : Km * (t.size + 1) * (P.size + 1)
      ≤ Km * (HvdH.isz (t : ℤ) + 1) * (N.size + 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left Km htm) hPNm
  calc 5 + 16 * (HvdH.isz (t : ℤ) + 1) + Km * (t.size + 1) * (P.size + 1)
      ≤ 5 * ((HvdH.isz (t : ℤ) + 1) * (N.size + 2))
          + 16 * ((HvdH.isz (t : ℤ) + 1) * (N.size + 2))
          + Km * (HvdH.isz (t : ℤ) + 1) * (N.size + 2) := add_le_add (add_le_add h1 h2) h3
    _ = (21 + Km) * (HvdH.isz (t : ℤ) + 1) * (N.size + 2) := by ring
    _ ≤ (16 + Km + 10) * (HvdH.isz (t : ℤ) + 1) * (N.size + 2) :=
        Nat.mul_le_mul_right (N.size + 2)
          (Nat.mul_le_mul_right (HvdH.isz (t : ℤ) + 1) (by omega))

/-! ## One `nil` iteration of the fold body -/

/-- At the `nil` glyph the fold body consumes the glyph, sets the loop register to `nil` and stops,
leaving stack 7 equal to `Y7`; cost 4. -/
private theorem pbFoldNilStep (mulP : HvdH.Cmd) :
    ∀ (main : HvdH.Cmd) (Y7 : List HvdH.Glyph)
      (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph),
      X pbElt = (HvdH.intList ([] : List ℕ)).enc ++ Y7 →
      ∃ s₁, Ev main (pbFoldBody mulP) ⟨g, X⟩ s₁ 4 ∧
        s₁.stk 0 = X 0 ∧ s₁.stk pbElt = Y7 ∧ s₁.reg pbR = Glyph.nil ∧
        (∀ k : HvdH.Stk, k ≠ 0 → k ≠ pbElt → s₁.stk k = X k) := by
  intro main Y7 g X h7
  have hhead : (X pbElt).headD Glyph.eos = Glyph.nil := by rw [h7]; rfl
  have hne : ¬ ((X pbElt).headD Glyph.eos = Glyph.cons) := by rw [hhead]; decide
  have hbody_eq : pbFoldBody mulP = .seq (.peek pbElt pbR) (.ite pbR Glyph.cons
      (seqs [Cmd.pop pbElt pbR, mvVal pbElt 0 pbV1 pbV2, mulP, Cmd.set pbR Glyph.cons])
      (seqs [Cmd.pop pbElt pbR, Cmd.set pbR Glyph.nil])) := rfl
  have hnil : Ev main (seqs [Cmd.pop pbElt pbR, Cmd.set pbR Glyph.nil])
      ⟨Function.update g pbR ((X pbElt).headD Glyph.eos), X⟩
      ⟨Function.update (Function.update (Function.update g pbR ((X pbElt).headD Glyph.eos)) pbR
          ((X pbElt).headD Glyph.eos)) pbR Glyph.nil,
        Function.update X pbElt (X pbElt).tail⟩ 2 :=
    Ev.seq' (ev_pop' main pbElt pbR (Function.update g pbR ((X pbElt).headD Glyph.eos)) X)
      (ev_set' main pbR Glyph.nil _ _) (by norm_num)
  have hite : Ev main (.ite pbR Glyph.cons
      (seqs [Cmd.pop pbElt pbR, mvVal pbElt 0 pbV1 pbV2, mulP, Cmd.set pbR Glyph.cons])
      (seqs [Cmd.pop pbElt pbR, Cmd.set pbR Glyph.nil]))
      ⟨Function.update g pbR ((X pbElt).headD Glyph.eos), X⟩
      ⟨Function.update (Function.update (Function.update g pbR ((X pbElt).headD Glyph.eos)) pbR
          ((X pbElt).headD Glyph.eos)) pbR Glyph.nil,
        Function.update X pbElt (X pbElt).tail⟩ 3 :=
    Ev.iteF (by simpa using hne) hnil
  have hpeek : Ev main (.peek pbElt pbR) ⟨g, X⟩
      ⟨Function.update g pbR ((X pbElt).headD Glyph.eos), X⟩ 1 := ev_peek' main pbElt pbR g X
  refine ⟨⟨Function.update (Function.update (Function.update g pbR ((X pbElt).headD Glyph.eos)) pbR
            ((X pbElt).headD Glyph.eos)) pbR Glyph.nil,
          Function.update X pbElt (X pbElt).tail⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbody_eq]
    exact Ev.seq' hpeek hite (by norm_num)
  · show Function.update X pbElt (X pbElt).tail 0 = X 0
    rw [Function.update_of_ne (by decide : (0 : HvdH.Stk) ≠ pbElt)]
  · show Function.update X pbElt (X pbElt).tail pbElt = Y7
    rw [Function.update_self, h7]
    rfl
  · show (Function.update (Function.update (Function.update g pbR ((X pbElt).headD Glyph.eos)) pbR
        ((X pbElt).headD Glyph.eos)) pbR Glyph.nil) pbR = Glyph.nil
    rw [Function.update_self]
  · intro k hk0 hk7
    show Function.update X pbElt (X pbElt).tail k = X k
    rw [Function.update_of_ne hk7]

/-! ## One `cons` iteration of the fold body -/

/-- One `cons` iteration: the body consumes the `cons` glyph, moves `int t` from stack 7 onto
stack 0 and multiplies it into the accumulator `int P` using the multiplier `mulP` (whose `WordR`
spec is `hmul`), leaving `int (t * P)` on top of stack 0 and the rest of the chain on stack 7. -/
private theorem pbFoldConsStep (mulP : HvdH.Cmd) (Km : ℕ)
    (hmul : ∀ (main : HvdH.Cmd) (a b : ℕ), 1 ≤ a → 1 ≤ b → ∀ rest : List HvdH.Val,
      HvdH.WordR main mulP
        (fun vs => vs = HvdH.Val.int (a : ℤ) :: HvdH.Val.int (b : ℤ) :: rest)
        (fun _ out => out = HvdH.Val.int ((a * b : ℕ) : ℤ) :: rest)
        (fun _ => Km * (a.size + 1) * (b.size + 1))) :
    ∀ (main : HvdH.Cmd) (P t : ℕ), 1 ≤ P → 1 ≤ t →
      ∀ (rest : List ℕ) (acc : List HvdH.Val)
      (R Y7 : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph),
      X 0 = (HvdH.Val.int (P : ℤ)).enc ++ HvdH.encs acc ++ R →
      X pbElt = (HvdH.intList (t :: rest)).enc ++ Y7 →
      ∃ s₁ n₁, Ev main (pbFoldBody mulP) ⟨g, X⟩ s₁ n₁ ∧
        n₁ ≤ 4 + 16 * (HvdH.isz (t : ℤ) + 1) + Km * (t.size + 1) * (P.size + 1) ∧
        s₁.stk 0 = (HvdH.Val.int ((t * P : ℕ) : ℤ)).enc ++ HvdH.encs acc ++ R ∧
        s₁.stk pbElt = (HvdH.intList rest).enc ++ Y7 ∧
        s₁.reg pbR = Glyph.cons ∧
        (∀ k : HvdH.Stk, k ≠ 0 → k ≠ pbElt → s₁.stk k = X k) := by
  intro main P t hP ht rest acc R Y7 g X h0 h7
  have hhead : (X pbElt).headD Glyph.eos = Glyph.cons := by rw [h7]; rfl
  have htail : (X pbElt).tail = (HvdH.Val.int (t : ℤ)).enc ++ ((HvdH.intList rest).enc ++ Y7) := by
    rw [h7, intList_cons_enc, List.cons_append, List.append_assoc]
    rfl
  have hbody_eq : pbFoldBody mulP = .seq (.peek pbElt pbR) (.ite pbR Glyph.cons
      (seqs [Cmd.pop pbElt pbR, mvVal pbElt 0 pbV1 pbV2, mulP, Cmd.set pbR Glyph.cons])
      (seqs [Cmd.pop pbElt pbR, Cmd.set pbR Glyph.nil])) := rfl
  have hpeek : Ev main (.peek pbElt pbR) ⟨g, X⟩
      ⟨Function.update g pbR ((X pbElt).headD Glyph.eos), X⟩ 1 := ev_peek' main pbElt pbR g X
  have hpeekreg : (⟨Function.update g pbR ((X pbElt).headD Glyph.eos), X⟩ : State).reg pbR
      = Glyph.cons := by rw [reg_mk, Function.update_self, hhead]
  have hpop : Ev main (.pop pbElt pbR)
      ⟨Function.update g pbR ((X pbElt).headD Glyph.eos), X⟩
      ⟨Function.update (Function.update g pbR ((X pbElt).headD Glyph.eos)) pbR
          ((X pbElt).headD Glyph.eos),
        Function.update X pbElt (X pbElt).tail⟩ 1 :=
    ev_pop' main pbElt pbR (Function.update g pbR ((X pbElt).headD Glyph.eos)) X
  obtain ⟨s₂, n₂, hev₂, hn₂, hs₂a, hs₂0, hs₂c, hs₂d, hs₂f⟩ :=
    mvVal_ev_full (main := main) (a := pbElt) (b := (0 : HvdH.Stk)) (c := pbV1) (d := pbV2)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := Function.update (Function.update g pbR ((X pbElt).headD Glyph.eos)) pbR
              ((X pbElt).headD Glyph.eos))
      (X := Function.update X pbElt (X pbElt).tail)
      (v := HvdH.Val.int (t : ℤ)) (A := (HvdH.intList rest).enc ++ Y7) (B := X 0)
      (by rw [Function.update_self]; exact htail)
      (Function.update_of_ne (by decide : (0 : HvdH.Stk) ≠ pbElt) _ _)
  have hn₂' : n₂ ≤ 16 * (HvdH.isz (t : ℤ) + 1) := by
    rw [vsz_int_eq_isz] at hn₂
    exact hn₂
  have h0₂ : s₂.stk 0 = HvdH.encs (HvdH.Val.int (t : ℤ) :: HvdH.Val.int (P : ℤ) :: acc) ++ R := by
    rw [hs₂0, h0]
    simp only [encs_cons'_rp, List.append_assoc]
  obtain ⟨out, s₃, n₃, hpost, heval₃, hn₃, hs₃0, hs₃f⟩ :=
    (hmul main t P ht hP acc) (HvdH.Val.int (t : ℤ) :: HvdH.Val.int (P : ℤ) :: acc) rfl s₂ R h0₂
  have hev₃ : Ev main mulP s₂ s₃ (Km * (t.size + 1) * (P.size + 1)) := ⟨n₃, heval₃, hn₃⟩
  have hs₃0' : s₃.stk 0 = (HvdH.Val.int ((t * P : ℕ) : ℤ)).enc ++ HvdH.encs acc ++ R := by
    rw [hs₃0, hpost]
    simp only [encs_cons'_rp, List.append_assoc]
  have hset : Ev main (.set pbR Glyph.cons) s₃
      ⟨Function.update s₃.reg pbR Glyph.cons, s₃.stk⟩ 1 :=
    ev_set' main pbR Glyph.cons s₃.reg s₃.stk
  have hinner := Ev.seq hev₃ hset
  have hmid := Ev.seq hev₂ hinner
  have hbranch := Ev.seq hpop hmid
  have hite : Ev main (.ite pbR Glyph.cons
        (seqs [Cmd.pop pbElt pbR, mvVal pbElt 0 pbV1 pbV2, mulP, Cmd.set pbR Glyph.cons])
        (seqs [Cmd.pop pbElt pbR, Cmd.set pbR Glyph.nil]))
      ⟨Function.update g pbR ((X pbElt).headD Glyph.eos), X⟩
      ⟨Function.update s₃.reg pbR Glyph.cons, s₃.stk⟩
      ((1 + (n₂ + (Km * (t.size + 1) * (P.size + 1) + 1))) + 1) :=
    Ev.iteT hpeekreg hbranch
  have hbody : Ev main (.seq (.peek pbElt pbR) (.ite pbR Glyph.cons
        (seqs [Cmd.pop pbElt pbR, mvVal pbElt 0 pbV1 pbV2, mulP, Cmd.set pbR Glyph.cons])
        (seqs [Cmd.pop pbElt pbR, Cmd.set pbR Glyph.nil])))
      ⟨g, X⟩ ⟨Function.update s₃.reg pbR Glyph.cons, s₃.stk⟩
      (1 + ((1 + (n₂ + (Km * (t.size + 1) * (P.size + 1) + 1))) + 1)) :=
    Ev.seq hpeek hite
  refine ⟨⟨Function.update s₃.reg pbR Glyph.cons, s₃.stk⟩,
    (1 + ((1 + (n₂ + (Km * (t.size + 1) * (P.size + 1) + 1))) + 1)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbody_eq]
    exact hbody
  · show 1 + ((1 + (n₂ + (Km * (t.size + 1) * (P.size + 1) + 1))) + 1)
        ≤ 4 + 16 * (HvdH.isz (t : ℤ) + 1) + Km * (t.size + 1) * (P.size + 1)
    omega
  · show s₃.stk 0 = (HvdH.Val.int ((t * P : ℕ) : ℤ)).enc ++ HvdH.encs acc ++ R
    exact hs₃0'
  · show s₃.stk pbElt = (HvdH.intList rest).enc ++ Y7
    rw [hs₃f pbElt (by decide : pbElt ≠ (0 : HvdH.Stk)), hs₂a]
  · show (Function.update s₃.reg pbR Glyph.cons) pbR = Glyph.cons
    rw [Function.update_self]
  · intro k hk0 hk7
    show s₃.stk k = X k
    have h2 : s₂.stk k = X k := by
      by_cases hc : k = pbV1
      · subst hc
        rw [hs₂c, Function.update_of_ne (by decide : pbV1 ≠ pbElt)]
      · by_cases hd : k = pbV2
        · subst hd
          rw [hs₂d, Function.update_of_ne (by decide : pbV2 ≠ pbElt)]
        · rw [hs₂f k hk7 hk0 hc hd, Function.update_of_ne hk7]
    rw [hs₃f k hk0, h2]

/-! ## Two arithmetic gadgets for the telescoping cost bound -/

/-- The telescoping step of the fold: a `cons` iteration at factor `t` (coefficient `16+Km+10`)
followed by the rest of the fold (coefficient `16+Km+11`) fits in one budget of the latter shape,
because `1 + (Σ isz + length)` splits as `(isz t + 1) + (1 + (Σ isz_rest + length_rest))`. -/
private theorem pbFoldTelescope (Km : ℕ) {I A X Y : ℕ} (hX : X = I + A) :
    (16 + Km + 10) * I * Y + (16 + Km + 11) * A * Y ≤ (16 + Km + 11) * X * Y := by
  subst hX
  calc (16 + Km + 10) * I * Y + (16 + Km + 11) * A * Y
      ≤ (16 + Km + 11) * I * Y + (16 + Km + 11) * A * Y :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_right Y (Nat.mul_le_mul_right I (by omega))) _
    _ = (16 + Km + 11) * (I + A) * Y := by ring

/-- Absorbing the two extra steps of `pbFoldProg` (`set` and the failing loop test). -/
private theorem pbFoldFinal (Km : ℕ) {C X Y : ℕ} (hC : C ≤ (16 + Km + 11) * X * Y)
    (hXY : 2 ≤ X * Y) : C + 2 ≤ (16 + Km + 12) * X * Y := by
  calc C + 2 ≤ (16 + Km + 11) * X * Y + 2 := Nat.add_le_add_right hC 2
    _ ≤ (16 + Km + 11) * X * Y + X * Y := Nat.add_le_add_left hXY _
    _ = (16 + Km + 12) * X * Y := by ring

/-! ## The fold loop -/

/-- The main induction: from a state whose stack 7 holds the `cons`-chain `intList l` and whose
stack 0 holds the accumulator `int P`, the loop `pbFoldLoop` runs `l.length + 1` times (one `cons`
iteration per element plus the final `nil` iteration, after which the loop test fails), restoring
stack 7 to `Y7` and producing `int (P * l.prod)` on stack 0. -/
private theorem pbFoldAux (mulP : HvdH.Cmd) (Km : ℕ)
    (hmul : ∀ (main : HvdH.Cmd) (a b : ℕ), 1 ≤ a → 1 ≤ b → ∀ rest : List HvdH.Val,
      HvdH.WordR main mulP
        (fun vs => vs = HvdH.Val.int (a : ℤ) :: HvdH.Val.int (b : ℤ) :: rest)
        (fun _ out => out = HvdH.Val.int ((a * b : ℕ) : ℤ) :: rest)
        (fun _ => Km * (a.size + 1) * (b.size + 1))) :
    ∀ (l : List ℕ), (∀ t ∈ l, 1 ≤ t) → ∀ (main : HvdH.Cmd) (P : ℕ), 1 ≤ P →
      ∀ (acc : List HvdH.Val) (R Y7 : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph)
        (X : HvdH.Stk → List HvdH.Glyph),
      g pbR = Glyph.cons →
      X 0 = (HvdH.Val.int (P : ℤ)).enc ++ HvdH.encs acc ++ R →
      X 7 = (HvdH.intList l).enc ++ Y7 →
      ∃ s' C, Work.Layout.loopRuns main pbR Glyph.cons (pbFoldBody mulP) (l.length + 1)
          ⟨g, X⟩ s' C ∧
        C ≤ (16 + Km + 11) * (1 + ((l.map (fun t : ℕ => HvdH.isz (t : ℤ))).sum + l.length)) *
              ((P * l.prod).size + 2) ∧
        s'.stk 0 = (HvdH.Val.int ((P * l.prod : ℕ) : ℤ)).enc ++ HvdH.encs acc ++ R ∧
        s'.stk 7 = Y7 ∧
        s'.reg pbR = Glyph.nil ∧
        (∀ k : HvdH.Stk, k ≠ 0 → k ≠ 7 → s'.stk k = X k) := by
  intro l
  induction l with
  | nil =>
      intro _ main P hP acc R Y7 g X hg h0 h7
      obtain ⟨s₁, hev, hs₁0, hs₁7, hs₁reg, hs₁fr⟩ := pbFoldNilStep mulP main Y7 g X h7
      refine ⟨s₁, 4 + 1, loopRuns.one hg hev, ?_, ?_, ?_, hs₁reg, ?_⟩
      · have h18 : 5 ≤ 16 + Km + 11 := by omega
        have hM1 : 1 ≤ P.size + 2 := by omega
        have := Nat.mul_le_mul h18 hM1
        simpa using this
      · rw [hs₁0, h0]
        simp only [prod_nil_one, Nat.mul_one]
      · exact hs₁7
      · intro k hk0 hk7
        exact hs₁fr k hk0 hk7
  | cons t rest ih =>
      intro hl main P hP acc R Y7 g X hg h0 h7
      have ht : 1 ≤ t := hl t (List.mem_cons_self ..)
      have hl' : ∀ u ∈ rest, 1 ≤ u := fun u hu => hl u (List.mem_cons_of_mem t hu)
      obtain ⟨s₁, n₁, hev₁, hn₁, hs₁0, hs₁7, hs₁reg, hs₁fr⟩ :=
        pbFoldConsStep mulP Km hmul main P t hP ht rest acc R Y7 g X h0 h7
      have htP : 1 ≤ t * P := by
        have h := Nat.mul_le_mul ht hP
        simpa using h
      obtain ⟨s₂, C₂, hruns₂, hC₂, hs₂0, hs₂7, hs₂reg, hs₂fr⟩ :=
        ih hl' main (t * P) htP acc R Y7 s₁.reg s₁.stk hs₁reg hs₁0 hs₁7
      have hlen : 1 + (rest.length + 1) = (t :: rest).length + 1 := by
        simp only [List.length_cons]; omega
      have hA : 1 + (((t :: rest).map (fun u : ℕ => HvdH.isz (u : ℤ))).sum
            + (t :: rest).length)
          = (HvdH.isz (t : ℤ) + 1)
            + (1 + ((rest.map (fun u : ℕ => HvdH.isz (u : ℤ))).sum + rest.length)) := by
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        ring
      have hPeq : (t * P) * rest.prod = P * (t :: rest).prod := by
        rw [List.prod_cons]; ring
      have hNpos : 0 < (t :: rest).prod := by
        have h1 : 1 ≤ (t :: rest).prod := one_le_prod _ hl
        omega
      have hPN : P ≤ P * (t :: rest).prod := Nat.le_mul_of_pos_right P hNpos
      refine ⟨s₂, (n₁ + 1) + C₂, ?_, ?_, ?_, ?_, hs₂reg, ?_⟩
      · exact loopRuns.cast hlen
          (loopRuns.concat (rest.length + 1) (loopRuns.one hg hev₁) hruns₂)
      · have h1' : n₁ + 1 ≤ (16 + Km + 10) * (HvdH.isz (t : ℤ) + 1)
            * ((P * (t :: rest).prod).size + 2) := by
          have hb := pbFoldStepBudget Km P t (P * (t :: rest).prod) hPN
          omega
        have h2' : C₂ ≤ (16 + Km + 11)
            * (1 + ((rest.map (fun u : ℕ => HvdH.isz (u : ℤ))).sum + rest.length))
            * ((P * (t :: rest).prod).size + 2) := by
          rw [hPeq] at hC₂
          exact hC₂
        exact le_trans (add_le_add h1' h2') (pbFoldTelescope Km hA)
      · rw [hs₂0, hPeq]
      · exact hs₂7
      · intro k hk0 hk7
        exact (hs₂fr k hk0 hk7).trans (hs₁fr k hk0 hk7)

/-! ## The fold walk -/

/-- The fold walk of `Work.Resample.pbFoldProg mulP` (`Submission/Work/Resample/pbKit.lean`):
the `cons`-chain `intList l` sitting on stack 7 is consumed one factor at a time; each factor is moved
to the top of stack 0 on top of the accumulator `int P` and multiplied in by `mulP`.  At the `nil`
glyph the loop stops, so stack 7 is restored to `Y7` and stack 0 holds `int (P * l.prod)`.

Route: induction on `l` with `Work.Layout.loopRuns` (`loopRuns.one`, `loopRuns.concat`,
`loopRuns.eval`).  For `l = t :: rest` the body peeks `cons` (since `(intList (t::rest)).enc = cons ::
(int t).enc ++ (intList rest).enc`), pops it, `Work.Layout.mvVal_ev_full` moves `int t` onto stack 0,
`hmul` multiplies it into `int P`, and the induction hypothesis for `rest` applies with `P := P * t`;
the `nil` branch pops and stops.  Registers 0–4 are `mvVal`'s, `pbR = 9` is reset after `mulP`, and
`pbV1 = 3`, `pbV2 = 4` are restored by `mvVal_ev_full`.

The cost bound is stated in the form that telescopes: every intermediate accumulator divides
`P * l.prod`, so its size is `≤ (P * l.prod).size`, and the per-iteration cost is
`16*(isz t + 1) + Km*(t.size + 1)*(P.size + 1)`, which is `≤ (16 + Km)*(isz t + 1)*((P*l.prod).size + 2)`;
summing over the list gives the bound below, with `(P*t*rest.prod) = P*((t::rest).prod)` on the nose. -/
theorem pbFoldEv (mulP : HvdH.Cmd) (Km : ℕ)
    (hmul : ∀ (main : HvdH.Cmd) (a b : ℕ), 1 ≤ a → 1 ≤ b → ∀ rest : List HvdH.Val,
      HvdH.WordR main mulP
        (fun vs => vs = HvdH.Val.int (a : ℤ) :: HvdH.Val.int (b : ℤ) :: rest)
        (fun _ out => out = HvdH.Val.int ((a * b : ℕ) : ℤ) :: rest)
        (fun _ => Km * (a.size + 1) * (b.size + 1))) :
    ∃ K : ℕ, ∀ (main : HvdH.Cmd) (P : ℕ), 1 ≤ P → ∀ (l : List ℕ), (∀ t ∈ l, 1 ≤ t) →
      ∀ (acc : List HvdH.Val) (R Y7 : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph)
        (X : HvdH.Stk → List HvdH.Glyph),
      X 0 = (HvdH.Val.int (P : ℤ)).enc ++ HvdH.encs acc ++ R →
      X 7 = (HvdH.intList l).enc ++ Y7 →
      ∃ s' n, Work.Layout.Ev main (Work.Resample.pbFoldProg mulP) ⟨g, X⟩ s' n ∧
        n ≤ K * (1 + ((l.map (fun t : ℕ => HvdH.isz (t : ℤ))).sum + l.length)) *
              ((P * l.prod).size + 2) ∧
        s'.stk 0 = (HvdH.Val.int ((P * l.prod : ℕ) : ℤ)).enc ++ HvdH.encs acc ++ R ∧
        s'.stk 7 = Y7 ∧
        (∀ k : HvdH.Stk, k ≠ 0 → k ≠ 7 → s'.stk k = X k) := by
  refine ⟨16 + Km + 12, ?_⟩
  intro main P hP l hl acc R Y7 g X h0 h7
  have hset : Ev main (.set pbR Glyph.cons) ⟨g, X⟩
      ⟨Function.update g pbR Glyph.cons, X⟩ 1 := ev_set' main pbR Glyph.cons g X
  obtain ⟨s', C, hruns, hC, hs0, hs7, hsreg, hfr⟩ :=
    pbFoldAux mulP Km hmul l hl main P hP acc R Y7 (Function.update g pbR Glyph.cons) X
      (Function.update_self pbR Glyph.cons g) h0 h7
  have hne : s'.reg pbR ≠ Glyph.cons := by rw [hsreg]; decide
  have hloop : Ev main (.loop pbR Glyph.cons (pbFoldBody mulP))
      ⟨Function.update g pbR Glyph.cons, X⟩ s' (C + 1) := loopRuns.eval hruns hne
  have hprog : Ev main (pbFoldProg mulP) ⟨g, X⟩ s' (1 + (C + 1)) := by
    rw [show pbFoldProg mulP
        = .seq (.set pbR Glyph.cons) (.loop pbR Glyph.cons (pbFoldBody mulP)) from rfl]
    exact Ev.seq hset hloop
  refine ⟨s', 1 + (C + 1), hprog, ?_, hs0, hs7, hfr⟩
  have hXY : 2 ≤ (1 + ((l.map (fun t : ℕ => HvdH.isz (t : ℤ))).sum + l.length)) *
      ((P * l.prod).size + 2) := by
    have h1 : 1 ≤ 1 + ((l.map (fun t : ℕ => HvdH.isz (t : ℤ))).sum + l.length) := by omega
    have h2 : 2 ≤ (P * l.prod).size + 2 := by omega
    have h3 := Nat.mul_le_mul h1 h2
    simpa using h3
  calc 1 + (C + 1) = C + 2 := by ring
    _ ≤ (16 + Km + 12) * (1 + ((l.map (fun t : ℕ => HvdH.isz (t : ℤ))).sum + l.length)) *
          ((P * l.prod).size + 2) := pbFoldFinal Km hC hXY

end Work.Resample
