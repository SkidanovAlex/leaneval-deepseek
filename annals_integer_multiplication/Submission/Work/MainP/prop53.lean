import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.ConvR.basic
import Submission.Work.ConvR.dropUnder
import Submission.Work.Main.defs
import Submission.Work.Main.word.scaleVec
import Submission.Work.Transform.eps_mul
import Submission.Work.Transform.convC_norm
import Submission.Work.Transform.arrangeDefs
import Submission.Work.MainP.planWord
import Submission.Work.MainP.mulElem
import Submission.Work.MainP.listProdWord
import Submission.Work.MainP.approxChain
import Submission.Work.MainP.finalArith

/-! Guidance from the project lead (the requester):

AREA OWNER: Prop53 (paper Prop 5.3, REFS/nlogn.txt lines 2183–2204; split out of Main by the lead). Prove
`KernelLib → IntLib → LayoutLib → FxLib → DFTMathProp → Prop52Prop → Prop53Prop`.

All supporting modules are proved (sorry-free, axiom-clean):
`MainP/planWord` (`planWord`, `planWordL`), `MainP/mulElem`, `MainP/listProdWord` (+`intList_eq_map`),
`MainP/approxChain`, `MainP/finalArith`.  This file is the assembly; see `HANDOFF.md` for the design.
-/

set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace Work.MainP

open HvdH

local infixl:68 " ;;; " => HvdH.Cmd.seq

/-- Cost absorption for Proposition 5.3: with `S0 = ts.prod * p^2 + 1`, `KE0 = 10^12 * s` and
`KE = 100 * KE0`, the thirteen `KE0*S0` stages of the pipeline fit into the slack between
`fsCost K52` and `fsCost (K52+KE)`.  Stated with a small context so that `nlinarith` stays cheap. -/
theorem prop53Cost (K52 s : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ts : List ℕ) (hmono : Monotone Cm)
    (hT1 : 1 ≤ ts.prod) (hp1 : 1 ≤ p) :
    3 * HvdH.fsCost K52 Cm p α ts + 13 * (1000000000000 * s) * (ts.prod * p ^ 2 + 1)
      ≤ 3 * HvdH.fsCost (K52 + 100 * (1000000000000 * s)) Cm p α ts
        + (K52 + 100 * (1000000000000 * s)) := by
  have hS0le : ts.prod * p ^ 2 + 1 ≤ 2 * ts.prod * p ^ 2 := by
    have h : 1 ≤ ts.prod * p ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc ts.prod * p ^ 2 + 1 ≤ ts.prod * p ^ 2 + ts.prod * p ^ 2 := Nat.add_le_add_left h _
      _ = 2 * ts.prod * p ^ 2 := by ring
  have hmonoF : HvdH.fsCost K52 Cm p α ts + 3 * (100 * (1000000000000 * s)) * ts.prod * p ^ 2
      ≤ HvdH.fsCost (K52 + 100 * (1000000000000 * s)) Cm p α ts := by
    have hCm : Cm (K52 * p) ≤ Cm ((K52 + 100 * (1000000000000 * s)) * p) :=
      hmono (Nat.mul_le_mul_right p (Nat.le_add_right _ _))
    have hpow : (p + 1) ^ K52 ≤ (p + 1) ^ (K52 + 100 * (1000000000000 * s)) :=
      Nat.pow_le_pow_right (by omega) (Nat.le_add_right _ _)
    have ha : K52 * ts.prod * (Nat.sqrt p + 1) * α * (Cm (K52 * p) + p)
        ≤ (K52 + 100 * (1000000000000 * s)) * ts.prod * (Nat.sqrt p + 1) * α *
          (Cm ((K52 + 100 * (1000000000000 * s)) * p) + p) := by
      have h1 : K52 * ts.prod * (Nat.sqrt p + 1) * α * (Cm (K52 * p) + p)
          ≤ (K52 + 100 * (1000000000000 * s)) * ts.prod * (Nat.sqrt p + 1) * α *
            (Cm (K52 * p) + p) :=
        Nat.mul_le_mul_right (Cm (K52 * p) + p) (Nat.mul_le_mul_right α
          (Nat.mul_le_mul_right (Nat.sqrt p + 1) (Nat.mul_le_mul_right ts.prod
            (Nat.le_add_right K52 (100 * (1000000000000 * s))))))
      have h2 : (K52 + 100 * (1000000000000 * s)) * ts.prod * (Nat.sqrt p + 1) * α *
            (Cm (K52 * p) + p)
          ≤ (K52 + 100 * (1000000000000 * s)) * ts.prod * (Nat.sqrt p + 1) * α *
            (Cm ((K52 + 100 * (1000000000000 * s)) * p) + p) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_right hCm p)
      exact le_trans h1 h2
    have hb : K52 * ts.prod * p ^ 2 ≤ (K52 + 100 * (1000000000000 * s)) * ts.prod * p ^ 2 :=
      Nat.mul_le_mul_right (p ^ 2) (Nat.mul_le_mul_right ts.prod
        (Nat.le_add_right K52 (100 * (1000000000000 * s))))
    have hc : K52 * ts.sum * (p + 1) ^ K52
        ≤ (K52 + 100 * (1000000000000 * s)) * ts.sum *
          (p + 1) ^ (K52 + 100 * (1000000000000 * s)) := by
      have h := Nat.mul_le_mul (Nat.le_add_right K52 (100 * (1000000000000 * s)))
        (Nat.mul_le_mul_left ts.sum hpow)
      calc K52 * ts.sum * (p + 1) ^ K52 = K52 * (ts.sum * (p + 1) ^ K52) := by ring
        _ ≤ (K52 + 100 * (1000000000000 * s)) *
              (ts.sum * (p + 1) ^ (K52 + 100 * (1000000000000 * s))) := h
        _ = (K52 + 100 * (1000000000000 * s)) * ts.sum *
              (p + 1) ^ (K52 + 100 * (1000000000000 * s)) := by ring
    have hres : HvdH.resCost K52 Cm p α ts + (100 * (1000000000000 * s)) * ts.prod * p ^ 2
        ≤ HvdH.resCost (K52 + 100 * (1000000000000 * s)) Cm p α ts := by
      simp only [HvdH.resCost]
      nlinarith [ha, hb, hc]
    simp only [HvdH.fsCost]
    nlinarith [hres, hc]
  have hstep1 : 13 * (1000000000000 * s) * (ts.prod * p ^ 2 + 1)
      ≤ 26 * (1000000000000 * s) * (ts.prod * p ^ 2) := by
    calc 13 * (1000000000000 * s) * (ts.prod * p ^ 2 + 1)
        ≤ 13 * (1000000000000 * s) * (2 * ts.prod * p ^ 2) := Nat.mul_le_mul_left _ hS0le
      _ = 26 * (1000000000000 * s) * (ts.prod * p ^ 2) := by ring
  have hstep2 : 26 * (1000000000000 * s) * (ts.prod * p ^ 2)
      ≤ 3 * (3 * (100 * (1000000000000 * s)) * (ts.prod * p ^ 2)) := by
    have h : 26 * (1000000000000 * s) ≤ 9 * (100 * (1000000000000 * s)) := by
      calc 26 * (1000000000000 * s) ≤ 900 * (1000000000000 * s) :=
            Nat.mul_le_mul_right _ (by norm_num)
        _ = 9 * (100 * (1000000000000 * s)) := by ring
    calc 26 * (1000000000000 * s) * (ts.prod * p ^ 2)
        ≤ (9 * (100 * (1000000000000 * s))) * (ts.prod * p ^ 2) := Nat.mul_le_mul_right _ h
      _ = 3 * (3 * (100 * (1000000000000 * s)) * (ts.prod * p ^ 2)) := by ring
  calc 3 * HvdH.fsCost K52 Cm p α ts + 13 * (1000000000000 * s) * (ts.prod * p ^ 2 + 1)
      ≤ 3 * HvdH.fsCost K52 Cm p α ts
        + 3 * (3 * (100 * (1000000000000 * s)) * (ts.prod * p ^ 2)) :=
        Nat.add_le_add_left (le_trans hstep1 hstep2) _
    _ = 3 * (HvdH.fsCost K52 Cm p α ts + 3 * (100 * (1000000000000 * s)) * ts.prod * p ^ 2) := by
        ring
    _ ≤ 3 * HvdH.fsCost (K52 + 100 * (1000000000000 * s)) Cm p α ts := Nat.mul_le_mul_left 3 hmonoF
    _ ≤ 3 * HvdH.fsCost (K52 + 100 * (1000000000000 * s)) Cm p α ts
        + (K52 + 100 * (1000000000000 * s)) := Nat.le_add_right _ _

/-- `ofList` is injective. -/
private theorem ofList_inj {xs ys : List HvdH.Val} (h : HvdH.ofList xs = HvdH.ofList ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => simp only [HvdH.ofList] at h; cases h
  | cons x xs ih =>
    cases ys with
    | nil => simp only [HvdH.ofList] at h; cases h
    | cons y ys =>
      rw [show HvdH.ofList (x :: xs) = HvdH.Val.cons x (HvdH.ofList xs) from rfl,
          show HvdH.ofList (y :: ys) = HvdH.Val.cons y (HvdH.ofList ys) from rfl] at h
      simp only [HvdH.Val.cons.injEq] at h
      rw [ih h.2, h.1]

/-- `cfxVal` is injective. -/
theorem cfxVal_inj {a b : ℤ × ℤ} (h : HvdH.cfxVal a = HvdH.cfxVal b) : a = b := by
  simp only [HvdH.cfxVal, HvdH.Val.cons.injEq, HvdH.Val.int.injEq] at h
  exact Prod.ext h.1 h.2


/-! ## Helper lemmas for the assembly (cost arithmetic, list extraction, norm bound) -/

/-- Sequential composition of `WordC`s with one-argument intermediate predicates. -/
theorem seqW (hK : KernelLib) {main p q : Cmd} {P Qi R : List Val → Prop} {c1 c2 : ℕ}
    (h1 : Work.ConvR.WordC main p P (fun _ out => Qi out) c1)
    (h2 : Work.ConvR.WordC main q Qi (fun _ out => R out) c2) :
    Work.ConvR.WordC main (.seq p q) P (fun _ out => R out) (c1 + c2) := by
  refine hK.conseq (main := main) (p := .seq p q)
    (P := P) (Q := fun _ out => ∃ mid, Qi mid ∧ R out) (C := fun _ => c1 + c2)
    (P' := P) (Q' := fun _ out => R out) (C' := fun _ => c1 + c2)
    (hK.seq main p q P (fun _ out => Qi out) (fun _ => c1) Qi (fun _ out => R out)
      (fun _ => c2) (fun _ => c2) h1 h2 (fun vs mid _ hq => ⟨hq, le_rfl⟩))
    (fun vs h => h) (fun vs out _ hq => by obtain ⟨mid, hQi, hR⟩ := hq; exact hR) (fun vs _ => le_rfl)

/-- A `pushVal` of a constant above an arbitrary tail. -/
theorem pushWC {main : Cmd} {pushP : Val → Cmd} {K : ℕ}
    (hpv : ∀ (main : Cmd) (v : Val), WordR main (pushP v) (fun _ => True)
      (fun vs out => out = v :: vs) (fun _ => K * (vsz v + 1)))
    (v : Val) (rest : List Val) (C : ℕ) (hC : K * (vsz v + 1) ≤ C) :
    Work.ConvR.WordC main (pushP v) (fun vs => vs = rest) (fun _ out => out = v :: rest) C := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ := hpv main v vs trivial s R hR
  exact ⟨out, s', n, by rw [hq, hvs], he, le_trans hn hC, hstk, hoth⟩

/-- `cfxVal`-lists are equal iff their entries are. -/
theorem map_cfxVal_inj : ∀ (xs ys : List (ℤ × ℤ)),
    xs.map HvdH.cfxVal = ys.map HvdH.cfxVal → xs = ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons y ys => simp at h
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [cfxVal_inj h.1, ih ys h.2]

/-- `cvecVal` is injective. -/
theorem cvecVal_inj {xs ys : List (ℤ × ℤ)} (h : HvdH.cvecVal xs = HvdH.cvecVal ys) : xs = ys :=
  map_cfxVal_inj xs ys
    (ofList_inj (show HvdH.ofList (xs.map HvdH.cfxVal) = HvdH.ofList (ys.map HvdH.cfxVal) from h))

/-- Membership in an eight-element list. -/
theorem mem8 {α : Type*} {v a b c d e f g h : α} (hv : v ∈ [a, b, c, d, e, f, g, h]) :
    v = a ∨ v = b ∨ v = c ∨ v = d ∨ v = e ∨ v = f ∨ v = g ∨ v = h := by
  simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using hv

/-- A product of two bounded factors. -/
theorem budget2 {A B KB S0 CA CB H : ℕ} (hA : A ≤ KB * CA) (hB : B ≤ CB * S0)
    (hC : CA * CB ≤ H) : A * B ≤ H * KB * S0 := by
  calc A * B ≤ (KB * CA) * (CB * S0) := Nat.mul_le_mul hA hB
    _ = (CA * CB) * KB * S0 := by ring
    _ ≤ H * KB * S0 := Nat.mul_le_mul_right S0 (Nat.mul_le_mul_right KB hC)

/-- A product `K * B` with `K ≤ KB` and `B ≤ CB * S0`. -/
theorem budget1 {K KB B S0 CB H : ℕ} (hK : K ≤ KB) (hB : B ≤ CB * S0)
    (hC : CB ≤ H) : K * B ≤ H * KB * S0 :=
  budget2 (A := K) (CA := 1) (by simpa using hK) hB (by simpa using hC)

/-- `K ≤ H * KB * S0` for `K ≤ KB` and `H, S0 ≥ 1`. -/
theorem le_budget {K KB S0 H : ℕ} (hK : K ≤ KB) (hS0 : 1 ≤ S0) (hH : 1 ≤ H) :
    K ≤ H * KB * S0 := by
  have h1 : KB ≤ KB * S0 := by
    calc KB = KB * 1 := (Nat.mul_one KB).symm
      _ ≤ KB * S0 := Nat.mul_le_mul_left KB hS0
  have h2 : KB * S0 ≤ H * (KB * S0) := by
    have := Nat.mul_le_mul_right (KB * S0) hH
    simpa using this
  calc K ≤ KB := hK
    _ ≤ KB * S0 := h1
    _ ≤ H * (KB * S0) := h2
    _ = H * KB * S0 := by ring

/-- Sum of two half-budget bounds. -/
theorem bud_add {a b KB S0 : ℕ} (ha : a ≤ 4000000000 * KB * S0) (hb : b ≤ 4000000000 * KB * S0) :
    a + b ≤ 8000000000 * KB * S0 := by
  refine le_trans (Nat.add_le_add ha hb) ?_
  have h : (4000000000 : ℕ) * KB * S0 + 4000000000 * KB * S0 = 8000000000 * KB * S0 := by ring
  rw [h]

/-- A product plus a constant term. -/
theorem budget1add {K KB B S0 CB H : ℕ} (hK : K ≤ KB) (hB : B ≤ CB * S0) (hS0 : 1 ≤ S0)
    (hC : CB + 1 ≤ H) : K * B + K ≤ H * KB * S0 := by
  have h1 : K * B ≤ KB * CB * S0 := by
    calc K * B ≤ KB * (CB * S0) := Nat.mul_le_mul hK hB
      _ = KB * CB * S0 := by ring
  have h2 : K ≤ KB * S0 := by
    calc K ≤ KB := hK
      _ = KB * 1 := (Nat.mul_one KB).symm
      _ ≤ KB * S0 := Nat.mul_le_mul_left KB hS0
  calc K * B + K ≤ KB * CB * S0 + KB * S0 := Nat.add_le_add h1 h2
    _ = KB * (CB + 1) * S0 := by ring
    _ ≤ KB * H * S0 := Nat.mul_le_mul_right S0 (Nat.mul_le_mul_left KB hC)
    _ = H * KB * S0 := by ring

/-- The plan-shuffling cost of `planWordL`. -/
theorem planArith {Lm S0 n : ℕ} (hL : Lm + 1 ≤ 60000 * S0) (hS0 : 1 ≤ S0) (hn : n + 1 ≤ 20) :
    16 * ((16 * (Lm + 1) * 8 + 1) * (n + 1)) ≤ 2500000000 * S0 := by
  nlinarith [hL, hS0, hn]

/-- The scaling cost of `FxLib.scale`. -/
theorem svArith {S T p S0 : ℕ} (hS0 : S0 = T * p ^ 2 + 1) (hST : S ≤ T) (hT : 3 ≤ T)
    (hp : 100 ≤ p) : (S + 1) * (p + 1) * (p + 1) ≤ 2 * S0 := by
  have h3 : (0 : ℤ) ≤ (T : ℤ) - 3 := by omega
  have h4 : (0 : ℤ) ≤ (p : ℤ) - 100 := by omega
  have hprod : (0 : ℤ) ≤ ((T : ℤ) - 3) * ((p : ℤ) - 100) * ((p : ℤ) - 100) :=
    mul_nonneg (mul_nonneg h3 h4) h4
  have hS : ((S : ℕ) : ℤ) ≤ (T : ℤ) := by exact_mod_cast hST
  have hT3 : (3 : ℤ) ≤ (T : ℤ) := by exact_mod_cast hT
  have hp100 : (100 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  have key : (((S + 1) * (p + 1) * (p + 1) : ℕ) : ℤ) ≤ ((2 * S0 : ℕ) : ℤ) := by
    have hs0 : ((S0 : ℕ) : ℤ) = (T : ℤ) * ((p : ℤ)) ^ 2 + 1 := by
      rw [hS0]; push_cast; ring
    push_cast
    rw [hs0]
    nlinarith [hprod, hS, hT3, hp100]
  exact_mod_cast key

/-- The list-product cost. -/
theorem lpArith {L p S0 : ℕ} (hL : L + 1 ≤ 1730) (hp : 100 ≤ p) (hS0 : p ^ 2 + 1 ≤ S0) :
    (L + 1) * (p + 4) ^ 2 ≤ 3000 * S0 := by
  have h1 : (L + 1) * (p + 4) ^ 2 ≤ 1730 * (p + 4) ^ 2 := Nat.mul_le_mul_right _ hL
  have h2 : 1730 * (p + 4) ^ 2 ≤ 3000 * (p ^ 2 + 1) := by nlinarith [hp]
  have h3 : 3000 * (p ^ 2 + 1) ≤ 3000 * S0 := Nat.mul_le_mul_left _ hS0
  linarith

/-- The pointwise-product (`zipWith` + `mulElem`) cost. -/
theorem zipArith {n Kme Kzw p T KB S0 : ℕ} (hnT : n ≤ T) (hTp : T * p ^ 2 + 1 ≤ S0)
    (hp : 1 ≤ p) (hKme : Kme ≤ KB) (hKzw : Kzw ≤ KB) :
    n * (Kme * (p + 1) ^ 2 + Kzw * (2 * p + 9)) + Kzw ≤ 8000000000 * KB * S0 := by
  have hp1 : (p + 1) ^ 2 ≤ 4 * (p ^ 2) := by nlinarith [hp]
  have hp2 : 2 * p + 9 ≤ 11 * (p ^ 2) := by nlinarith [hp]
  have hTp2 : T * p ^ 2 ≤ S0 := by omega
  have hS01 : 1 ≤ S0 := by omega
  have hA : n * (p + 1) ^ 2 ≤ 4 * S0 := by
    have h1 : n * (p + 1) ^ 2 ≤ T * (p + 1) ^ 2 := Nat.mul_le_mul_right _ hnT
    have h2 : T * (p + 1) ^ 2 ≤ T * (4 * p ^ 2) := Nat.mul_le_mul_left _ hp1
    have h3 : T * (4 * p ^ 2) ≤ 4 * S0 := by nlinarith [hTp2]
    linarith
  have hB : n * (2 * p + 9) + 1 ≤ 12 * S0 := by
    have h1 : n * (2 * p + 9) ≤ T * (2 * p + 9) := Nat.mul_le_mul_right _ hnT
    have h2 : T * (2 * p + 9) ≤ T * (11 * p ^ 2) := Nat.mul_le_mul_left _ hp2
    have h3 : T * (11 * p ^ 2) ≤ 11 * S0 := by nlinarith [hTp2]
    have h4 : 1 ≤ S0 := hS01
    linarith
  calc n * (Kme * (p + 1) ^ 2 + Kzw * (2 * p + 9)) + Kzw
      = Kme * (n * (p + 1) ^ 2) + Kzw * (n * (2 * p + 9) + 1) := by ring
    _ ≤ KB * (4 * S0) + KB * (12 * S0) :=
        Nat.add_le_add (Nat.mul_le_mul hKme hA) (Nat.mul_le_mul hKzw hB)
    _ = KB * (16 * S0) := by ring
    _ ≤ 8000000000 * KB * S0 := by nlinarith

/-- The `ss.prod`-scaled norm of the normalised cyclic convolution, pointwise. -/
theorem smulConvCNorm {p : ℕ} {ss : List ℕ} (hpos : ∀ t ∈ ss, 0 < t) {us ws : List (ℤ × ℤ)}
    (hus : HvdH.InDiscVec p ss.prod us) (hws : HvdH.InDiscVec p ss.prod ws) :
    ∀ i, i < ss.prod → (ss.prod : ℝ) * ‖(1 / (ss.prod : ℂ)) *
      HvdH.vget (HvdH.convC ss (HvdH.fxVec p ss.prod us) (HvdH.fxVec p ss.prod ws)) i‖ ≤ 1 := by
  intro i hi
  have hSpos : 0 < ss.prod := List.prod_pos hpos
  have hSneR : (ss.prod : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hSpos)
  have hcn : ‖HvdH.convC ss (HvdH.fxVec p ss.prod us) (HvdH.fxVec p ss.prod ws)‖ ≤ 1 := by
    have h := Work.Transform.convC_norm ss hpos (HvdH.fxVec p ss.prod us) (HvdH.fxVec p ss.prod ws)
    have hU := Work.MainP.norm_fxVec_le p hus
    have hW := Work.MainP.norm_fxVec_le p hws
    have hUW : ‖HvdH.fxVec p ss.prod us‖ * ‖HvdH.fxVec p ss.prod ws‖ ≤ 1 := by
      simpa using mul_le_mul hU hW (norm_nonneg (HvdH.fxVec p ss.prod ws)) (by norm_num : (0:ℝ) ≤ 1)
    linarith
  have hvi : HvdH.vget (HvdH.convC ss (HvdH.fxVec p ss.prod us) (HvdH.fxVec p ss.prod ws)) i
      = HvdH.convC ss (HvdH.fxVec p ss.prod us) (HvdH.fxVec p ss.prod ws) ⟨i, hi⟩ := by
    simp only [HvdH.vget, dif_pos hi]
  have hcn' : ‖HvdH.convC ss (HvdH.fxVec p ss.prod us) (HvdH.fxVec p ss.prod ws) ⟨i, hi⟩‖ ≤ 1 :=
    le_trans (norm_le_pi_norm (HvdH.convC ss (HvdH.fxVec p ss.prod us) (HvdH.fxVec p ss.prod ws))
      ⟨i, hi⟩) hcn
  rw [hvi]
  have h1 : ‖(1 / (ss.prod : ℂ)) * HvdH.convC ss (HvdH.fxVec p ss.prod us)
        (HvdH.fxVec p ss.prod ws) ⟨i, hi⟩‖ =
      (ss.prod : ℝ)⁻¹ * ‖HvdH.convC ss (HvdH.fxVec p ss.prod us)
        (HvdH.fxVec p ss.prod ws) ⟨i, hi⟩‖ := by
    rw [norm_mul, one_div, norm_inv, Complex.norm_natCast]
  rw [h1, ← mul_assoc, mul_inv_cancel₀ hSneR, one_mul]
  exact hcn'


/-- The accumulated cost of the sixteen-stage pipeline. -/
theorem chainBudget (B F : ℕ) :
    (((((((((((((((B + B) + B) + F) + B) + F) + B) + B) + F) + B) + B) + B) + B) + B) + B) + B) ≤ 3 * F + 13 * B := by omega

/-- `getD` on a `cfxVal`-mapped list. -/
theorem getD_map_cfx {l : List (ℤ × ℤ)} {i : ℕ} (hi : i < l.length) :
    (l.map HvdH.cfxVal).getD i .nil = HvdH.cfxVal (l.getD i (0,0)) := by
  rw [Work.Transform.getD_default (l.map HvdH.cfxVal) (by rwa [List.length_map]) HvdH.Val.nil
    (HvdH.cfxVal (0,0))]
  exact List.getD_map (f := HvdH.cfxVal) (l := l) (d := (0,0))

/-- Extract a coefficient vector from a list of `cfxVal`s. -/
theorem cvecExtract : ∀ (l : List HvdH.Val),
    (∀ i, i < l.length → ∃ w : ℤ × ℤ, l.getD i .nil = HvdH.cfxVal w) →
    ∃ l' : List (ℤ × ℤ), l = l'.map HvdH.cfxVal := by
  intro l
  induction l with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons a t ih =>
    intro h
    obtain ⟨w, hw⟩ := h 0 (by simp)
    have hwa : a = HvdH.cfxVal w := by simpa using hw
    have ht : ∀ i, i < t.length → ∃ w' : ℤ × ℤ, t.getD i .nil = HvdH.cfxVal w' := by
      intro i hi
      obtain ⟨w', hw'⟩ := h (i + 1) (by simpa using Nat.succ_lt_succ hi)
      exact ⟨w', by simpa using hw'⟩
    obtain ⟨l', hl'⟩ := ih ht
    exact ⟨w :: l', by rw [hwa, hl']; rfl⟩

/-- Paper Proposition 5.3: approximate cyclic convolution of coprime size. -/
theorem prop53 : HvdH.KernelLib → HvdH.IntLib → HvdH.LayoutLib → HvdH.FxLib → HvdH.DFTMathProp →
    HvdH.Prop52Prop → HvdH.Prop53Prop := by
  intro hK hI hL hF hDFT h52
  obtain ⟨p52, K52, h52w⟩ := h52
  obtain ⟨lpProg, Klp, hlp⟩ := listProdWord hK hI
  obtain ⟨svProg, Ksv, hsv⟩ := Work.Main.word.scaleVec hK hF
  obtain ⟨pwProg, Kpw, hpw⟩ := planWordL hK
  obtain ⟨mulE, Kme, hmulE⟩ := mulElem hK hF
  obtain ⟨rollP, Kr, hroll⟩ := hK.roll
  obtain ⟨dropP, Kd, hdrop⟩ := hK.drop
  obtain ⟨pushP, Kpv, hpush⟩ := hK.pushVal
  obtain ⟨zipC, Kzw, hzip⟩ := hK.zipWith
  obtain ⟨duP, Kdu, hdu⟩ := Work.ConvR.dropUnder hK
  -- the three concrete shuffling plans (verified by python; `rfl`/`decide` below)
  let planA : List (Bool × ℕ) :=
    [(false,4),(false,1),(false,5),(true,2),(false,6),(true,6),(true,0),(false,10),(false,8),
      (true,6),(true,6),(true,6),(true,5),(false,14),(true,5),(true,5),(true,5),(true,5),(true,5)]
  let planC : List (Bool × ℕ) :=
    [(false,7),(false,1),(false,7),(false,7),(false,7),(false,7),(false,7),(false,7)]
  let planE : List (Bool × ℕ) :=
    [(false,2),(false,7),(false,2),(false,7),(false,7),(false,7),(false,7),(false,7)]
  let L0 : List Work.Transform.I8 := [0,1,2,3,4,5,6,7]
  let KE0 : ℕ := 1000000000000 * (K52 + Kpw + Ksv + Kme + Klp + Kdu + Kpv + Kr + Kd + Kzw + 1)
  let KE : ℕ := 100 * KE0
  refine ⟨pushP (HvdH.Val.int (-1)) ;;; pushP (HvdH.Val.int (1 : ℤ)) ;;; pwProg planA ;;; p52 ;;;
      pwProg planC ;;; p52 ;;; zipC mulE ;;; pwProg planE ;;; p52 ;;; rollP 1 ;;; lpProg ;;;
      rollP 1 ;;; svProg ;;; duP ;;; rollP 1 ;;; dropP, K52 + KE, ?_⟩
  intro main N Cm hmono hmul p α ss ts hFs h3 hKN
  have hFsP : HvdH.FsParams p α ss ts := hFs
  -- abbreviations for the parameter values
  let Pv : HvdH.Val := HvdH.Val.int (p : ℤ)
  let Av : HvdH.Val := HvdH.Val.int (α : ℤ)
  let Sv : HvdH.Val := HvdH.intList ss
  let Tv : HvdH.Val := HvdH.intList ts
  let M1 : HvdH.Val := HvdH.Val.int (-1)
  let O1 : HvdH.Val := HvdH.Val.int (1 : ℤ)
  -- the parameter facts
  obtain ⟨hPow2, hResP, h2Da, h3Dp, hST⟩ := hFs
  obtain ⟨hResSlen, hResTlen, hp100, hα2, hα2p, hResAll⟩ := hResP
  obtain ⟨hPowTlen, hPowAll, hPowPair, hPowProd, hPow100⟩ := hPow2
  have hD : HvdH.D = 1729 := by norm_num [HvdH.D]
  have hp1 : 1 ≤ p := by omega
  have hss_lt : ∀ t ∈ ss, t < 2 ^ p := by
    intro t ht
    rw [List.mem_iff_getElem] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    have hiD : i < HvdH.D := by rw [← hResSlen]; exact hi
    obtain ⟨-, hlt1, hlt2, -, -⟩ := hResAll i hiD
    rw [List.getD_eq_getElem _ _ hi] at hlt1
    exact lt_trans hlt1 hlt2
  have hss_ge : ∀ t ∈ ss, 1 ≤ t := by
    intro t ht
    rw [List.mem_iff_getElem] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    have hiD : i < HvdH.D := by rw [← hResSlen]; exact hi
    obtain ⟨hge, -, -, -, -⟩ := hResAll i hiD
    rw [List.getD_eq_getElem _ _ hi] at hge
    omega
  have hts_lt : ∀ t ∈ ts, t < 2 ^ p := by
    intro t ht
    rw [List.mem_iff_getElem] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    have hiD : i < HvdH.D := by rw [← hResTlen]; exact hi
    obtain ⟨-, -, hlt2, -, -⟩ := hResAll i hiD
    rw [List.getD_eq_getElem _ _ hi] at hlt2
    exact hlt2
  have hpos' : ∀ t ∈ ss, 0 < t := fun t ht => by have := hss_ge t ht; omega
  have hSl : ss.length = 1729 := by rw [hResSlen, hD]
  have hTl : ts.length = 1729 := by rw [hResTlen, hD]
  have hT1 : 1 ≤ ts.prod := by
    have := h3Dp; rw [hD] at this; nlinarith [hp100, Nat.zero_le p]
  have hT3 : 3 ≤ ts.prod := by
    have := h3Dp; rw [hD] at this; nlinarith [hp100, Nat.zero_le p]
  have hS_lt : ss.prod < 2 ^ p := lt_of_le_of_lt hST hPowProd
  have hS1 : 1 ≤ ss.prod := List.one_le_prod hss_ge
  have hαp : α ≤ p := by nlinarith [hα2p, hα2]
  have hL1 : 1 ≤ Nat.log 2 ts.prod := by
    have := Nat.log_pos (b := 2) (n := ts.prod) (by norm_num) (by omega)
    omega
  have hK52N : K52 * p < N :=
    lt_of_le_of_lt (Nat.mul_le_mul_right p (Nat.le_add_right K52 KE)) hKN
  -- the two cardinal quantities
  set S0 : ℕ := ts.prod * p ^ 2 + 1 with hS0
  set Lm : ℕ := 5000 * (ss.prod * (2 * p + 8) + p + 8) with hLm
  have hS0pos : 1 ≤ S0 := by rw [hS0]; omega
  have hS0le : S0 ≤ 2 * ts.prod * p ^ 2 := by
    have h : 1 ≤ ts.prod * p ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [hS0]
    calc ts.prod * p ^ 2 + 1 ≤ ts.prod * p ^ 2 + ts.prod * p ^ 2 := Nat.add_le_add_left h _
      _ = 2 * ts.prod * p ^ 2 := by ring
  have hp1sq : (p + 1) ^ 2 ≤ 4 * S0 := by rw [hS0]; nlinarith [hp1, hT1]
  have hLmb : Lm + 1 ≤ 60000 * S0 := by
    rw [hLm, hS0]; nlinarith [hST, hT1, hp1, Nat.zero_le p]
  have hcost : ∀ c : ℕ, c ≤ 10000000000 * (K52 + Kpw + Ksv + Kme + Klp + Kdu + Kpv + Kr + Kd + Kzw + 1) * S0 →
      c ≤ KE0 * S0 := by
    intro c hc
    have h1 : 10000000000 * (K52 + Kpw + Ksv + Kme + Klp + Kdu + Kpv + Kr + Kd + Kzw + 1) ≤ KE0 := by
      have h2 : KE0 = 1000000000000 * (K52 + Kpw + Ksv + Kme + Klp + Kdu + Kpv + Kr + Kd + Kzw + 1) :=
        rfl
      rw [h2]
      exact Nat.mul_le_mul_right _ (by norm_num)
    exact le_trans hc (Nat.mul_le_mul_right S0 h1)
  -- size bounds for the values appearing in the pools
  have hszON : HvdH.vsz O1 ≤ Lm := by
    have h : HvdH.vsz O1 ≤ 3 := by
      rw [Work.ConvR.vsz_int, HvdH.isz, Int.natAbs_one]
      have h' : Nat.size 1 ≤ 1 := Nat.size_le.mpr (by norm_num)
      omega
    rw [hLm]; nlinarith [h, hp1]
  have hszM1 : HvdH.vsz M1 ≤ Lm := by
    have h : HvdH.vsz M1 ≤ 3 := by
      rw [Work.ConvR.vsz_int, HvdH.isz, Int.natAbs_neg, Int.natAbs_one]
      have h' : Nat.size 1 ≤ 1 := Nat.size_le.mpr (by norm_num)
      omega
    rw [hLm]; nlinarith [h, hp1]
  have hszP : HvdH.vsz Pv ≤ Lm := by
    have h : HvdH.vsz Pv ≤ p + 2 := by
      rw [Work.ConvR.vsz_int]; exact Work.ConvR.isz_int_le p
    rw [hLm]; nlinarith [h, hp1]
  have hszA : HvdH.vsz Av ≤ Lm := by
    have h : HvdH.vsz Av ≤ α + 2 := by
      rw [Work.ConvR.vsz_int]; exact Work.ConvR.isz_int_le α
    rw [hLm]; nlinarith [h, hp1, hαp]
  have hszSS : HvdH.vsz Sv ≤ Lm := by
    have h1 := Work.ConvR.vsz_intList_le ss
    have h2 : (ss.map fun t => t.size + 3).sum ≤ ss.length * (p + 3) := by
      calc (ss.map fun t => t.size + 3).sum ≤ (ss.map fun _ => p + 3).sum :=
            List.sum_le_sum (fun t ht => by have := Nat.size_le.mpr (hss_lt t ht); omega)
        _ = ss.length * (p + 3) := Work.ConvR.sum_map_const ss (p + 3)
    rw [hSl] at h2
    rw [hLm]; nlinarith [h1, h2, Nat.zero_le (ss.prod * (2 * p + 8))]
  have hszTS : HvdH.vsz Tv ≤ Lm := by
    have h1 := Work.ConvR.vsz_intList_le ts
    have h2 : (ts.map fun t => t.size + 3).sum ≤ ts.length * (p + 3) := by
      calc (ts.map fun t => t.size + 3).sum ≤ (ts.map fun _ => p + 3).sum :=
            List.sum_le_sum (fun t ht => by have := Nat.size_le.mpr (hts_lt t ht); omega)
        _ = ts.length * (p + 3) := Work.ConvR.sum_map_const ts (p + 3)
    rw [hTl] at h2
    rw [hLm]; nlinarith [h1, h2, Nat.zero_le (ss.prod * (2 * p + 8))]
  have hszCV : ∀ (zs : List (ℤ × ℤ)), HvdH.InDiscVec p ss.prod zs → HvdH.vsz (HvdH.cvecVal zs) ≤ Lm := by
    intro zs hz
    have h1 := Work.ConvR.vsz_cvecVal_le (p := p) (r := ss.prod) hz
    simp only [Work.ConvR.cvecSz, Work.ConvR.cfxSz] at h1
    rw [hLm]; nlinarith [h1, Nat.zero_le ss.prod, Nat.zero_le p]
  -- the plan facts
  have hlenA : planA.length = 19 := rfl
  have hfoldA : planA.foldl Work.Transform.stepL L0 = ([2,3,4,5,1,6,2,3,4,5,1,7,2,2,3,4,5,0,4,2] : List Work.Transform.I8) := rfl
  have hbndA : ∀ s ∈ planA, s.2 < 16 := by decide
  have hrangeA : ∀ j, j < planA.length → (planA.getD j (true,0)).2 <
      ((planA.take j).foldl Work.Transform.stepL L0).length := by
    intro j hj
    rw [show planA.length = 19 from rfl] at hj
    interval_cases j <;> decide
  have hlenC : planC.length = 8 := rfl
  have hfoldC : planC.foldl Work.Transform.stepL L0 = ([1,2,3,4,5,6,0,7] : List Work.Transform.I8) := rfl
  have hbndC : ∀ s ∈ planC, s.2 < 16 := by decide
  have hrangeC : ∀ j, j < planC.length → (planC.getD j (true,0)).2 <
      ((planC.take j).foldl Work.Transform.stepL L0).length := by
    intro j hj
    rw [show planC.length = 8 from rfl] at hj
    interval_cases j <;> decide
  have hlenE : planE.length = 8 := rfl
  have hfoldE : planE.foldl Work.Transform.stepL L0 = ([1,3,4,5,6,0,7,2] : List Work.Transform.I8) := rfl
  have hbndE : ∀ s ∈ planE, s.2 < 16 := by decide
  have hrangeE : ∀ j, j < planE.length → (planE.getD j (true,0)).2 <
      ((planE.take j).foldl Work.Transform.stepL L0).length := by
    intro j hj
    rw [show planE.length = 8 from rfl] at hj
    interval_cases j <;> decide
  -- the final cost arithmetic (delegated to `prop53Cost`, proved in a small context)
  have hcostfinal : 3 * HvdH.fsCost K52 Cm p α ts + 13 * KE0 * S0
      ≤ 3 * HvdH.fsCost (K52 + KE) Cm p α ts + (K52 + KE) :=
    prop53Cost K52 (K52 + Kpw + Ksv + Kme + Klp + Kdu + Kpv + Kr + Kd + Kzw + 1) Cm p α ts
      hmono hT1 hp1
  -- the main core: its statement is exactly the goal
  have hCore : HvdH.WordR main
      (pushP (HvdH.Val.int (-1)) ;;; pushP (HvdH.Val.int (1 : ℤ)) ;;; pwProg planA ;;; p52 ;;;
        pwProg planC ;;; p52 ;;; zipC mulE ;;; pwProg planE ;;; p52 ;;; rollP 1 ;;; lpProg ;;;
        rollP 1 ;;; svProg ;;; duP ;;; rollP 1 ;;; dropP)
      (fun vs => ∃ us ws rest,
        vs = [Pv, Av, Sv, Tv, HvdH.cvecVal us, HvdH.cvecVal ws] ++ rest ∧
        HvdH.InDiscVec p ss.prod us ∧ HvdH.InDiscVec p ss.prod ws)
      (fun vs out => ∃ us ws rest zs,
        vs = [Pv, Av, Sv, Tv, HvdH.cvecVal us, HvdH.cvecVal ws] ++ rest ∧
        out = HvdH.cvecVal zs :: rest ∧
        HvdH.Approx p zs (HvdH.convC ss (HvdH.fxVec p ss.prod us) (HvdH.fxVec p ss.prod ws))
          ((2 ^ (2 * HvdH.D * α ^ 2 + 8) * ts.prod ^ 2 * Nat.log 2 ts.prod : ℕ) : ℝ))
      (fun _ => 3 * HvdH.fsCost (K52 + KE) Cm p α ts + (K52 + KE)) := by
    intro vs hpre
    obtain ⟨us, ws, rest, hvs, hus, hws⟩ := hpre
    have hszUS : HvdH.vsz (HvdH.cvecVal us) ≤ Lm := hszCV us hus
    have hszWS : HvdH.vsz (HvdH.cvecVal ws) ≤ Lm := hszCV ws hws
    -- the data predicates
    let E5 : ℝ := ((2 ^ (2 * HvdH.D * α ^ 2 + 5) * ts.prod * Nat.log 2 ts.prod : ℕ) : ℝ)
    let EFIN : ℝ := ((2 ^ (2 * HvdH.D * α ^ 2 + 8) * ts.prod ^ 2 * Nat.log 2 ts.prod : ℕ) : ℝ)
    let FU : Fin ss.prod → ℂ := HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us)
    let FW : Fin ss.prod → ℂ := HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws)
    let XE : Fin ss.prod → ℂ :=
      (1 / (ss.prod : ℂ)) • HvdH.convC ss (HvdH.fxVec p ss.prod us) (HvdH.fxVec p ss.prod ws)
    let A1 : List (ℤ × ℤ) → Prop := fun W1 => HvdH.Approx p W1 FU E5
    let A2 : List (ℤ × ℤ) → Prop := fun W2 => HvdH.Approx p W2 FW E5
    let A0 : List (ℤ × ℤ) → List (ℤ × ℤ) → Prop := fun W0 zs =>
      HvdH.Approx p W0 (HvdH.dftMulti ss 1 (HvdH.fxVec p ss.prod zs)) E5
    let HYP : List (ℤ × ℤ) → List (ℤ × ℤ) → List (ℤ × ℤ) → Prop := fun W1 W2 zs =>
      zs.length = ss.prod ∧ HvdH.InDiscVec p ss.prod zs ∧
      (∀ i : Fin ss.prod, (2 : ℝ) ^ p * ‖HvdH.fxC p (zs.getD i (0,0)) -
        HvdH.fxC p (W2.getD i (0,0)) * HvdH.fxC p (W1.getD i (0,0))‖ < 2)
    let ERR : List (ℤ × ℤ) → Prop := fun zsv =>
      ∀ i : Fin ss.prod, (2 : ℝ) ^ p * ‖HvdH.fxC p (zsv.getD i (0,0)) - (ss.prod : ℂ) * XE i‖
        < 2 * (ss.prod : ℝ) * (E5 + E5 + E5 + 2) + 3
    let DAT : List (ℤ × ℤ) → List (ℤ × ℤ) → List (ℤ × ℤ) → List (ℤ × ℤ) → List (ℤ × ℤ) → Prop :=
      fun W1 W2 zs W0 zsv => A1 W1 ∧ A2 W2 ∧ HYP W1 W2 zs ∧ A0 W0 zs ∧
        HvdH.InDiscVec p ss.prod zsv ∧ ERR zsv
    -- the built pipeline
    have hbuilt : HvdH.WordR main
        (pushP (HvdH.Val.int (-1)) ;;; pushP (HvdH.Val.int (1 : ℤ)) ;;; pwProg planA ;;; p52 ;;;
          pwProg planC ;;; p52 ;;; zipC mulE ;;; pwProg planE ;;; p52 ;;; rollP 1 ;;; lpProg ;;;
          rollP 1 ;;; svProg ;;; duP ;;; rollP 1 ;;; dropP)
        (fun w => w = [Pv, Av, Sv, Tv, HvdH.cvecVal us, HvdH.cvecVal ws] ++ rest)
        (fun _ out => ∃ W1 W2 zs W0 zsv,
          out = HvdH.cvecVal zsv :: rest ∧ DAT W1 W2 zs W0 zsv)
        (fun _ => 3 * HvdH.fsCost K52 Cm p α ts + 13 * KE0 * S0) := by
      let PP : List HvdH.Val := [Pv, Av, Sv, Tv, HvdH.cvecVal us, HvdH.cvecVal ws]
      let paA : List HvdH.Val := [O1, M1, Pv, Av, Sv, Tv, HvdH.cvecVal us, HvdH.cvecVal ws]
      let T0 : List HvdH.Val :=
        Pv :: Av :: Sv :: Tv :: M1 :: HvdH.cvecVal ws :: Pv :: Pv :: Av :: Sv :: Tv :: O1 ::
          Sv :: Pv :: rest
      let Tzip : List HvdH.Val := Pv :: Pv :: Av :: Sv :: Tv :: O1 :: Sv :: Pv :: rest
      let Tzip2 : List HvdH.Val := Pv :: Av :: Sv :: Tv :: O1 :: Sv :: Pv :: rest
      let Xc : ℕ → ℂ := fun i => (1 / (ss.prod : ℂ)) *
        HvdH.vget (HvdH.convC ss (HvdH.fxVec p ss.prod us) (HvdH.fxVec p ss.prod ws)) i
      let A0X : List (ℤ × ℤ) → Prop := fun W0 => HvdH.Approx p W0 XE (E5 + E5 + E5 + 2)
      let PD : List (ℤ × ℤ) → List (ℤ × ℤ) → List (ℤ × ℤ) → List (ℤ × ℤ) → Prop :=
        fun W1 W2 zs W0 => A1 W1 ∧ A2 W2 ∧ HYP W1 W2 zs ∧ A0 W0 zs ∧ A0X W0
      let KB : ℕ := K52 + Kpw + Ksv + Kme + Klp + Kdu + Kpv + Kr + Kd + Kzw + 1
      let BUD : ℕ := 8000000000 * KB * S0
      have hKB : KB = K52 + Kpw + Ksv + Kme + Klp + Kdu + Kpv + Kr + Kd + Kzw + 1 := rfl
      have hKpw_le : Kpw ≤ KB := by rw [hKB]; omega
      have hKsv_le : Ksv ≤ KB := by rw [hKB]; omega
      have hKme_le : Kme ≤ KB := by rw [hKB]; omega
      have hKlp_le : Klp ≤ KB := by rw [hKB]; omega
      have hKdu_le : Kdu ≤ KB := by rw [hKB]; omega
      have hKpv_le : Kpv ≤ KB := by rw [hKB]; omega
      have hKr_le : Kr ≤ KB := by rw [hKB]; omega
      have hKd_le : Kd ≤ KB := by rw [hKB]; omega
      have hKzw_le : Kzw ≤ KB := by rw [hKB]; omega
      have hKE0 : KE0 = 1000000000000 * KB := rfl
      have hBUDle : BUD ≤ KE0 * S0 := by
        rw [hKE0]
        exact Nat.mul_le_mul_right S0 (Nat.mul_le_mul_right KB (by norm_num))
      have hszSprod : HvdH.vsz (HvdH.Val.int ((ss.prod : ℕ) : ℤ)) ≤ Lm := by
        have h : HvdH.vsz (HvdH.Val.int ((ss.prod : ℕ) : ℤ)) ≤ p + 2 := by
          rw [Work.ConvR.vsz_int, HvdH.isz, Int.natAbs_natCast]
          have h' : Nat.size ss.prod ≤ p := Nat.size_le.mpr hS_lt
          omega
        rw [hLm]; nlinarith [h, hp1, Nat.zero_le (ss.prod * (2 * p + 8))]
      have hPA0 : Work.Transform.stateOf paA L0 ++ rest = O1 :: M1 :: PP ++ rest := rfl
      have hTA : Work.Transform.stateOf paA (planA.foldl Work.Transform.stepL L0) ++ rest =
          Pv :: Av :: Sv :: Tv :: M1 :: HvdH.cvecVal us :: T0 := by
        rw [hfoldA]; rfl
      have hSt1 : Work.ConvR.WordC main (pushP M1) (fun vs => vs = PP ++ rest)
          (fun _ out => out = M1 :: PP ++ rest) BUD :=
        pushWC hpush M1 (PP ++ rest) BUD
          (budget1 (B := HvdH.vsz M1 + 1) (CB := 60000) (H := 8000000000) hKpv_le
            (by omega) (by norm_num))
      have hSt2 : Work.ConvR.WordC main (pushP O1) (fun vs => vs = M1 :: PP ++ rest)
          (fun _ out => out = O1 :: M1 :: PP ++ rest) BUD :=
        pushWC hpush O1 (M1 :: PP ++ rest) BUD
          (budget1 (B := HvdH.vsz O1 + 1) (CB := 60000) (H := 8000000000) hKpv_le
            (by omega) (by norm_num))
      have hcostPlanA : Kpw * (16 * ((16 * (Lm + 1) * 8 + 1) * (planA.length + 1))) + Kpw ≤ BUD :=
        budget1add (B := 16 * ((16 * (Lm + 1) * 8 + 1) * (planA.length + 1)))
          (CB := 2500000000) (H := 8000000000) hKpw_le
          (planArith hLmb hS0pos (by omega)) hS0pos (by norm_num)
      have hSt3 : Work.ConvR.WordC main (pwProg planA)
          (fun vs => vs = O1 :: M1 :: PP ++ rest)
          (fun _ out => out = Pv :: Av :: Sv :: Tv :: M1 :: HvdH.cvecVal us :: T0) BUD := by
        refine Work.ConvR.WordC.conseq hK (C' := BUD)
          (hpw main paA L0 planA 16 Lm rest (by rfl) ?_ hbndA hrangeA) ?_ ?_ hcostPlanA
        · intro v hv
          rcases mem8 hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          exacts [hszON, hszM1, hszP, hszA, hszSS, hszTS, hszUS, hszWS]
        · intro vs hvs
          rw [hvs]
          exact hPA0.symm
        · intro vs out hvs hq
          rw [hq]
          exact hTA
      have hSt4 : Work.ConvR.WordC main p52
          (fun vs => vs = Pv :: Av :: Sv :: Tv :: M1 :: HvdH.cvecVal us :: T0)
          (fun _ out => ∃ W1, out = HvdH.cvecVal W1 :: T0 ∧ A1 W1)
          (HvdH.fsCost K52 Cm p α ts) := by
        intro vs hvs s R hR
        obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ :=
          h52w main N Cm hmono hmul p α ss ts (-1) (Or.inr rfl) hFsP h3 hK52N vs
            (by exact ⟨us, T0, hvs, hus⟩) s R hR
        obtain ⟨zs', rest', ws', hvs', hout, happ⟩ := hq
        rw [hvs] at hvs'
        have hzs : HvdH.cvecVal us = HvdH.cvecVal zs' :=
          congrArg (fun (l : List HvdH.Val) => l.getD 5 .nil) hvs'
        have hrest : T0 = rest' := congrArg (fun (l : List HvdH.Val) => l.drop 6) hvs'
        have hzu : us = zs' := cvecVal_inj hzs
        rw [← hzu] at happ
        exact ⟨out, s', n, ⟨ws',
          hout.trans (congrArg (fun l => HvdH.cvecVal ws' :: l) hrest.symm), happ⟩,
          he, hn, hstk, hoth⟩
      have hcostPlanC : Kpw * (16 * ((16 * (Lm + 1) * 8 + 1) * (planC.length + 1))) + Kpw ≤ BUD :=
        budget1add (B := 16 * ((16 * (Lm + 1) * 8 + 1) * (planC.length + 1)))
          (CB := 2500000000) (H := 8000000000) hKpw_le
          (planArith hLmb hS0pos (by rw [hlenC]; norm_num)) hS0pos (by norm_num)
      have hSt5 : Work.ConvR.WordC main (pwProg planC)
          (fun vs => ∃ W1, vs = HvdH.cvecVal W1 :: T0 ∧ A1 W1)
          (fun _ out => ∃ W1, out = Pv :: Av :: Sv :: Tv :: M1 :: HvdH.cvecVal ws ::
            HvdH.cvecVal W1 :: Tzip ∧ A1 W1) BUD := by
        intro vs hvs s R hR
        obtain ⟨W1, hvs', hA1⟩ := hvs
        obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ :=
          hpw main [HvdH.cvecVal W1, Pv, Av, Sv, Tv, M1, HvdH.cvecVal ws, Pv] L0 planC 16 Lm
            Tzip2 (by rfl) (by
              intro v hv
              rcases mem8 hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
              exacts [hszCV W1 hA1.1, hszP, hszA, hszSS, hszTS, hszM1, hszWS, hszP])
            hbndC hrangeC vs (by rw [hvs']; rfl) s R hR
        exact ⟨out, s', n, ⟨W1, by rw [hq, hfoldC]; rfl, hA1⟩, he,
          le_trans hn hcostPlanC, hstk, hoth⟩
      have hSt6 : Work.ConvR.WordC main p52
          (fun vs => ∃ W1, vs = Pv :: Av :: Sv :: Tv :: M1 :: HvdH.cvecVal ws ::
            HvdH.cvecVal W1 :: Tzip ∧ A1 W1)
          (fun _ out => ∃ W1 W2, out = HvdH.cvecVal W2 :: HvdH.cvecVal W1 :: Tzip ∧
            A1 W1 ∧ A2 W2) (HvdH.fsCost K52 Cm p α ts) := by
        intro vs hvs s R hR
        obtain ⟨W1, hvs', hA1⟩ := hvs
        obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ :=
          h52w main N Cm hmono hmul p α ss ts (-1) (Or.inr rfl) hFsP h3 hK52N vs
            (by exact ⟨ws, HvdH.cvecVal W1 :: Tzip, hvs', hws⟩) s R hR
        obtain ⟨zs', rest', ws', hvs'', hout, happ⟩ := hq
        rw [hvs'] at hvs''
        have hzs : HvdH.cvecVal ws = HvdH.cvecVal zs' :=
          congrArg (fun (l : List HvdH.Val) => l.getD 5 .nil) hvs''
        have hrest : HvdH.cvecVal W1 :: Tzip = rest' :=
          congrArg (fun (l : List HvdH.Val) => l.drop 6) hvs''
        have hzu : ws = zs' := cvecVal_inj hzs
        rw [← hzu] at happ
        exact ⟨out, s', n, ⟨W1, ws',
          hout.trans (congrArg (fun l => HvdH.cvecVal ws' :: l) hrest.symm), hA1, happ⟩,
          he, hn, hstk, hoth⟩
      have hSt7 : Work.ConvR.WordC main (zipC mulE)
          (fun vs => ∃ W1 W2, vs = HvdH.cvecVal W2 :: HvdH.cvecVal W1 :: Tzip ∧ A1 W1 ∧ A2 W2)
          (fun _ out => ∃ W1 W2 zs, out = HvdH.cvecVal zs :: Tzip ∧ A1 W1 ∧ A2 W2 ∧
            HYP W1 W2 zs) BUD := by
        intro vs hvs s R hR
        obtain ⟨W1, W2, hvs', hA1, hA2⟩ := hvs
        have hW1len : W1.length = ss.prod := hA1.1.1
        have hW2len : W2.length = ss.prod := hA2.1.1
        have hinner : ∀ x y, (∃ a b : ℤ × ℤ, x = HvdH.cfxVal a ∧ y = HvdH.cfxVal b ∧
            HvdH.inDisc p a ∧ HvdH.inDisc p b) →
            HvdH.WordR main mulE (fun vs => vs = x :: y :: Tzip)
              (fun _ out => ∃ z, out = z :: Tzip ∧
                (∃ a b w : ℤ × ℤ, x = HvdH.cfxVal a ∧ y = HvdH.cfxVal b ∧ z = HvdH.cfxVal w ∧
                  HvdH.inDisc p w ∧ (2:ℝ)^p * ‖HvdH.fxC p w - HvdH.fxC p a * HvdH.fxC p b‖ < 2) ∧
                HvdH.vsz z ≤ 2 * p + 8)
              (fun _ => Kme * (p + 1) ^ 2) := by
          intro x y hxy
          obtain ⟨a, b, hx, hy, ha, hb⟩ := hxy
          refine Work.ConvR.WordC.conseq hK (C' := Kme * (p + 1) ^ 2)
            (hmulE main p Tzip2 a b ha hb) ?_ ?_ le_rfl
          · intro vs hvs2
            rw [hvs2, hx, hy]
          · intro vs out hvs2 hq
            obtain ⟨w, hout, hw, herr⟩ := hq
            exact ⟨HvdH.cfxVal w, hout, ⟨a, b, w, hx, hy, rfl, hw, herr⟩,
              Work.ConvR.vsz_cfxVal_le hw⟩
        have hlen : (W2.map HvdH.cfxVal).length = (W1.map HvdH.cfxVal).length := by
          rw [List.length_map, List.length_map, hW2len, hW1len]
        have hP : ∀ i < (W2.map HvdH.cfxVal).length,
            (∃ a b : ℤ × ℤ, (W2.map HvdH.cfxVal).getD i .nil = HvdH.cfxVal a ∧
              (W1.map HvdH.cfxVal).getD i .nil = HvdH.cfxVal b ∧
              HvdH.inDisc p a ∧ HvdH.inDisc p b) := by
          intro i hi
          have hi2 : i < W2.length := by rwa [List.length_map] at hi
          have hi1 : i < W1.length := by rw [hW1len, ← hW2len]; exact hi2
          refine ⟨W2.getD i (0,0), W1.getD i (0,0), getD_map_cfx hi2, getD_map_cfx hi1, ?_, ?_⟩
          · rw [List.getD_eq_getElem _ _ hi2]; exact hA2.1.2 _ (List.getElem_mem hi2)
          · rw [List.getD_eq_getElem _ _ hi1]; exact hA1.1.2 _ (List.getElem_mem hi1)
        have hL : ∀ x ∈ (W2.map HvdH.cfxVal) ++ (W1.map HvdH.cfxVal), HvdH.vsz x ≤ 2 * p + 8 := by
          intro x hx
          rw [List.mem_append, List.mem_map, List.mem_map] at hx
          rcases hx with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
          · exact Work.ConvR.vsz_cfxVal_le (hA2.1.2 w hw)
          · exact Work.ConvR.vsz_cfxVal_le (hA1.1.2 w hw)
        obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ :=
          hzip main mulE Tzip
            (fun x y => ∃ a b : ℤ × ℤ, x = HvdH.cfxVal a ∧ y = HvdH.cfxVal b ∧
              HvdH.inDisc p a ∧ HvdH.inDisc p b)
            (fun x y z => ∃ a b w : ℤ × ℤ, x = HvdH.cfxVal a ∧ y = HvdH.cfxVal b ∧
              z = HvdH.cfxVal w ∧ HvdH.inDisc p w ∧
              (2:ℝ)^p * ‖HvdH.fxC p w - HvdH.fxC p a * HvdH.fxC p b‖ < 2)
            (Kme * (p + 1) ^ 2) (2 * p + 8) hinner (W2.map HvdH.cfxVal) (W1.map HvdH.cfxVal)
            hlen hP hL vs (by rw [hvs']; rfl) s R hR
        obtain ⟨zs, hout, hzlen, hQ⟩ := hq
        obtain ⟨zs', hzs'⟩ : ∃ zs' : List (ℤ × ℤ), zs = zs'.map HvdH.cfxVal := by
          refine cvecExtract zs ?_
          intro i hi
          obtain ⟨a, b, w, -, -, hzw, hw, -⟩ := hQ i (by rw [← hzlen]; exact hi)
          exact ⟨w, hzw⟩
        rw [hzs'] at hout hzlen hQ
        have hzsl : zs'.length = ss.prod := by
          have h1 : zs'.length = (W2.map HvdH.cfxVal).length := by
            rw [← hzlen, List.length_map]
          rw [h1, List.length_map, hW2len]
        have hi2' : ∀ i, i < ss.prod → i < (W2.map HvdH.cfxVal).length := by
          intro i hi
          rw [List.length_map, hW2len]; exact hi
        refine ⟨out, s', n, ⟨W1, W2, zs', ?_, hA1, hA2, ?_⟩, he, ?_, hstk, hoth⟩
        · exact hout
        · refine ⟨hzsl, ⟨hzsl, ?_⟩, ?_⟩
          · intro z hz
            rw [List.mem_iff_getElem] at hz
            obtain ⟨i, hi, rfl⟩ := hz
            obtain ⟨a, b, w, -, -, hzw, hw, -⟩ := hQ i (hi2' i (by rw [← hzsl]; exact hi))
            have hzw2 : HvdH.cfxVal (zs'.getD i (0,0)) = HvdH.cfxVal w := by
              rw [getD_map_cfx hi] at hzw
              exact hzw
            have hwi : zs'.getD i (0,0) = w := cfxVal_inj hzw2
            rw [← List.getD_eq_getElem _ _ hi, hwi]
            exact hw
          · intro i
            obtain ⟨a, b, w, hxa, hyb, hzw, hw, herr⟩ := hQ (i : ℕ) (hi2' (i : ℕ) i.isLt)
            have hxd := getD_map_cfx (l := W2) (i := (i : ℕ)) (by rw [hW2len]; exact i.isLt)
            have hyd := getD_map_cfx (l := W1) (i := (i : ℕ)) (by rw [hW1len]; exact i.isLt)
            have hzd := getD_map_cfx (l := zs') (i := (i : ℕ)) (by rw [hzsl]; exact i.isLt)
            rw [hxd] at hxa
            rw [hyd] at hyb
            rw [hzd] at hzw
            rw [cfxVal_inj hzw, cfxVal_inj hxa, cfxVal_inj hyb]
            exact herr
        · refine le_trans hn ?_
          exact zipArith (n := (W2.map HvdH.cfxVal).length) (Kme := Kme) (Kzw := Kzw) (p := p)
            (T := ts.prod) (KB := KB) (S0 := S0)
            (by rw [List.length_map, hW2len]; exact hST) (by rw [← hS0]) hp1 hKme_le hKzw_le
      have hcostPlanE : Kpw * (16 * ((16 * (Lm + 1) * 8 + 1) * (planE.length + 1))) + Kpw ≤ BUD :=
        budget1add (B := 16 * ((16 * (Lm + 1) * 8 + 1) * (planE.length + 1)))
          (CB := 2500000000) (H := 8000000000) hKpw_le
          (planArith hLmb hS0pos (by rw [hlenE]; norm_num)) hS0pos (by norm_num)
      have hSt8 : Work.ConvR.WordC main (pwProg planE)
          (fun vs => ∃ W1 W2 zs, vs = HvdH.cvecVal zs :: Tzip ∧ A1 W1 ∧ A2 W2 ∧ HYP W1 W2 zs)
          (fun _ out => ∃ W1 W2 zs, out = Pv :: Av :: Sv :: Tv :: O1 :: HvdH.cvecVal zs ::
            Sv :: Pv :: Pv :: rest ∧ A1 W1 ∧ A2 W2 ∧ HYP W1 W2 zs) BUD := by
        intro vs hvs s R hR
        obtain ⟨W1, W2, zs, hvs', hA1, hA2, hHYP⟩ := hvs
        obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ :=
          hpw main [HvdH.cvecVal zs, Pv, Pv, Av, Sv, Tv, O1, Sv] L0 planE 16 Lm (Pv :: rest)
            (by rfl) (by
              intro v hv
              rcases mem8 hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
              exacts [hszCV zs hHYP.2.1, hszP, hszP, hszA, hszSS, hszTS, hszON, hszSS])
            hbndE hrangeE vs (by rw [hvs']; rfl) s R hR
        exact ⟨out, s', n, ⟨W1, W2, zs, by rw [hq, hfoldE]; rfl, hA1, hA2, hHYP⟩, he,
          le_trans hn hcostPlanE, hstk, hoth⟩
      have hSt9 : Work.ConvR.WordC main p52
          (fun vs => ∃ W1 W2 zs, vs = Pv :: Av :: Sv :: Tv :: O1 :: HvdH.cvecVal zs ::
            Sv :: Pv :: Pv :: rest ∧ A1 W1 ∧ A2 W2 ∧ HYP W1 W2 zs)
          (fun _ out => ∃ W1 W2 zs W0, out = HvdH.cvecVal W0 :: Sv :: Pv :: Pv :: rest ∧
            PD W1 W2 zs W0) (HvdH.fsCost K52 Cm p α ts) := by
        intro vs hvs s R hR
        obtain ⟨W1, W2, zs, hvs', hA1, hA2, hHYP⟩ := hvs
        obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ :=
          h52w main N Cm hmono hmul p α ss ts 1 (Or.inl rfl) hFsP h3 hK52N vs
            (by exact ⟨zs, Sv :: Pv :: Pv :: rest, hvs', hHYP.2.1⟩) s R hR
        obtain ⟨zs'', rest', ws', hvs'', hout, happ⟩ := hq
        rw [hvs'] at hvs''
        have hzs : HvdH.cvecVal zs = HvdH.cvecVal zs'' :=
          congrArg (fun (l : List HvdH.Val) => l.getD 5 .nil) hvs''
        have hrest : Sv :: Pv :: Pv :: rest = rest' :=
          congrArg (fun (l : List HvdH.Val) => l.drop 6) hvs''
        have hzz : zs = zs'' := cvecVal_inj hzs
        rw [← hzz] at happ
        have hA0 : A0 ws' zs := happ
        have hA0X : A0X ws' :=
          approxChain hDFT p ss hpos' us ws W1 W2 zs ws' E5 E5 E5 hus hws hA1 hA2
            hHYP.2.1 (by
              intro i
              have hh := hHYP.2.2 i
              rwa [mul_comm (HvdH.fxC p (W2.getD i (0,0)))] at hh) hA0
        exact ⟨out, s', n, ⟨W1, W2, zs, ws',
          hout.trans (congrArg (fun l => HvdH.cvecVal ws' :: l) hrest.symm), hA1, hA2, hHYP,
          hA0, hA0X⟩, he, hn, hstk, hoth⟩
      have hSt10 : Work.ConvR.WordC main (rollP 1)
          (fun vs => ∃ W1 W2 zs W0, vs = HvdH.cvecVal W0 :: Sv :: Pv :: Pv :: rest ∧
            PD W1 W2 zs W0)
          (fun _ out => ∃ W1 W2 zs W0, out = Sv :: HvdH.cvecVal W0 :: Pv :: Pv :: rest ∧
            PD W1 W2 zs W0) BUD := by
        intro vs hvs s R hR
        obtain ⟨W1, W2, zs, W0, hvs', hPD⟩ := hvs
        obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ :=
          Work.ConvR.WordC.rollStep hK hroll (k := 1)
            (L := HvdH.cvecVal W0 :: Sv :: Pv :: Pv :: rest)
            (L' := Sv :: HvdH.cvecVal W0 :: Pv :: Pv :: rest) (by simp) (by simp)
            (budget2 (A := Kr * 2) (B := HvdH.vsz (HvdH.cvecVal W0) + HvdH.vsz Sv + 1)
              (KB := KB) (S0 := S0) (CA := 60000) (CB := 120000) (H := 8000000000)
              (Nat.mul_le_mul hKr_le (by norm_num)) (by
                have hw := hszCV W0 hPD.2.2.2.1.1
                omega) (by norm_num))
            vs hvs' s R hR
        exact ⟨out, s', n, ⟨W1, W2, zs, W0, hq, hPD⟩, he, hn, hstk, hoth⟩
      have hSt11 : Work.ConvR.WordC main lpProg
          (fun vs => ∃ W1 W2 zs W0, vs = Sv :: HvdH.cvecVal W0 :: Pv :: Pv :: rest ∧
            PD W1 W2 zs W0)
          (fun _ out => ∃ W1 W2 zs W0, out = HvdH.Val.int ((ss.prod : ℕ) : ℤ) ::
            HvdH.cvecVal W0 :: Pv :: Pv :: rest ∧ PD W1 W2 zs W0) BUD := by
        intro vs hvs s R hR
        obtain ⟨W1, W2, zs, W0, hvs', hPD⟩ := hvs
        have hcost11 : Klp * (ss.length + 1) * (p + 4) ^ 2 + Klp ≤ BUD := by
          have h1 : Klp * (ss.length + 1) * (p + 4) ^ 2 ≤ 4000000000 * KB * S0 :=
            budget2 (A := Klp * (ss.length + 1)) (B := (p + 4) ^ 2) (KB := KB) (S0 := S0)
              (CA := 1730) (CB := 2) (H := 4000000000)
              (Nat.mul_le_mul hKlp_le (by omega)) (by
                have h2 : (p + 4) ^ 2 ≤ 2 * (p ^ 2 + 1) := by nlinarith [hp1]
                have h3 : p ^ 2 + 1 ≤ S0 := by
                  have ha : p ^ 2 ≤ ts.prod * p ^ 2 := by
                    have := Nat.mul_le_mul_right (p ^ 2) hT1
                    simpa using this
                  rw [hS0]
                  exact Nat.add_le_add_right ha 1
                linarith) (by norm_num)
          have h2b : Klp ≤ 4000000000 * KB * S0 := le_budget hKlp_le hS0pos (by norm_num)
          exact bud_add h1 h2b
        have hlp' : Work.ConvR.WordC main lpProg
            (fun vs => vs = Sv :: HvdH.cvecVal W0 :: Pv :: Pv :: rest)
            (fun _ out => out = HvdH.Val.int ((ss.prod : ℕ) : ℤ) ::
              HvdH.cvecVal W0 :: Pv :: Pv :: rest)
            (Klp * (ss.length + 1) * (p + 4) ^ 2 + Klp) :=
          Work.ConvR.WordC.conseq hK
            (P' := fun vs => vs = Sv :: HvdH.cvecVal W0 :: Pv :: Pv :: rest)
            (C' := Klp * (ss.length + 1) * (p + 4) ^ 2 + Klp)
            (hlp main ss (HvdH.cvecVal W0 :: Pv :: Pv :: rest) p hss_lt hss_ge hS_lt)
            (fun vs hvs2 => by
              rw [hvs2, show Sv = HvdH.ofList (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ)))
                from intList_eq_map ss]) (fun _ _ _ hq => hq) le_rfl
        obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ := hlp' vs hvs' s R hR
        exact ⟨out, s', n, ⟨W1, W2, zs, W0, hq, hPD⟩, he, le_trans hn hcost11, hstk, hoth⟩
      have hSt12 : Work.ConvR.WordC main (rollP 1)
          (fun vs => ∃ W1 W2 zs W0, vs = HvdH.Val.int ((ss.prod : ℕ) : ℤ) ::
            HvdH.cvecVal W0 :: Pv :: Pv :: rest ∧ PD W1 W2 zs W0)
          (fun _ out => ∃ W1 W2 zs W0, out = HvdH.cvecVal W0 ::
            HvdH.Val.int ((ss.prod : ℕ) : ℤ) :: Pv :: Pv :: rest ∧ PD W1 W2 zs W0) BUD := by
        intro vs hvs s R hR
        obtain ⟨W1, W2, zs, W0, hvs', hPD⟩ := hvs
        obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ :=
          Work.ConvR.WordC.rollStep hK hroll (k := 1)
            (L := HvdH.Val.int ((ss.prod : ℕ) : ℤ) :: HvdH.cvecVal W0 :: Pv :: Pv :: rest)
            (L' := HvdH.cvecVal W0 :: HvdH.Val.int ((ss.prod : ℕ) : ℤ) :: Pv :: Pv :: rest)
            (by simp) (by simp)
            (budget2 (A := Kr * 2)
              (B := HvdH.vsz (HvdH.Val.int ((ss.prod : ℕ) : ℤ)) + HvdH.vsz (HvdH.cvecVal W0) + 1)
              (KB := KB) (S0 := S0) (CA := 60000) (CB := 120000) (H := 8000000000)
              (Nat.mul_le_mul hKr_le (by norm_num)) (by
                have hw := hszCV W0 hPD.2.2.2.1.1
                have hs := hszSprod
                omega) (by norm_num))
            vs hvs' s R hR
        exact ⟨out, s', n, ⟨W1, W2, zs, W0, hq, hPD⟩, he, hn, hstk, hoth⟩
      have hXc_eq : ∀ (i : ℕ) (hi : i < ss.prod), Xc i = (1 / (ss.prod : ℂ)) *
          HvdH.convC ss (HvdH.fxVec p ss.prod us) (HvdH.fxVec p ss.prod ws) ⟨i, hi⟩ := by
        intro i hi
        simp only [Xc, HvdH.vget, dif_pos hi]
      have hXE_eq : ∀ (i : ℕ) (hi : i < ss.prod), XE ⟨i, hi⟩ = Xc i := by
        intro i hi
        rw [hXc_eq i hi]
        simp only [XE, Pi.smul_apply, smul_eq_mul]
      have hSt13 : Work.ConvR.WordC main svProg
          (fun vs => ∃ W1 W2 zs W0, vs = HvdH.cvecVal W0 ::
            HvdH.Val.int ((ss.prod : ℕ) : ℤ) :: Pv :: Pv :: rest ∧ PD W1 W2 zs W0)
          (fun _ out => ∃ W1 W2 zs W0 zsv, out = HvdH.cvecVal zsv ::
            HvdH.Val.int ((ss.prod : ℕ) : ℤ) :: Pv :: Pv :: rest ∧
            A1 W1 ∧ A2 W2 ∧ HYP W1 W2 zs ∧ A0 W0 zs ∧ A0X W0 ∧
            HvdH.InDiscVec p ss.prod zsv ∧ ERR zsv) BUD := by
        intro vs hvs s R hR
        obtain ⟨W1, W2, zs, W0, hvs', hA1, hA2, hHYP, hA0, hA0X⟩ := hvs
        have hW0len : W0.length = ss.prod := hA0.1.1
        have hcost13 : Ksv * (W0.length + 1) * (p + 1) * (p + 1) + Ksv ≤ BUD := by
          have h1 : Ksv * ((W0.length + 1) * (p + 1) * (p + 1)) ≤ KB * (2 * S0) :=
            Nat.mul_le_mul hKsv_le
              (svArith hS0 (by rw [hW0len]; exact hST) hT3 hp100)
          have h3 : Ksv * (W0.length + 1) * (p + 1) * (p + 1)
              = Ksv * ((W0.length + 1) * (p + 1) * (p + 1)) := by ring
          rw [h3]
          have h4 : Ksv ≤ KB * S0 := by
            calc Ksv ≤ KB := hKsv_le
              _ = KB * 1 := (Nat.mul_one KB).symm
              _ ≤ KB * S0 := Nat.mul_le_mul_left KB hS0pos
          refine le_trans (Nat.add_le_add h1 h4) ?_
          calc KB * (2 * S0) + KB * S0 = KB * 3 * S0 := by ring
            _ = 3 * (KB * S0) := by ring
            _ ≤ 8000000000 * (KB * S0) := Nat.mul_le_mul_right _ (by norm_num)
            _ = 8000000000 * KB * S0 := by ring
        obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ :=
          hsv main p ss.prod W0 (Pv :: rest) Xc (E5 + E5 + E5 + 2) hS1
            (le_of_lt hS_lt) (by rw [hW0len]; exact hA0.1)
            vs (by
              refine ⟨hvs', ?_, ?_⟩
              · intro i hi
                rw [hW0len] at hi
                exact smulConvCNorm hpos' hus hws i hi
              · intro i hi
                rw [hW0len] at hi
                have hh := hA0X.2 ⟨i, hi⟩
                rw [hXE_eq i hi] at hh
                exact le_of_lt hh) s R hR
        obtain ⟨ws, hvseq, hout, hlen2, hdisc2, herr2⟩ := hq
        refine ⟨out, s', n, ⟨W1, W2, zs, W0, ws, hout, hA1, hA2, hHYP, hA0, hA0X, ?_, ?_⟩,
          he, le_trans hn hcost13, hstk, hoth⟩
        · exact ⟨by rw [hdisc2.1, hW0len], hdisc2.2⟩
        · intro i
          have hi0 : (i : ℕ) < W0.length := by rw [hW0len]; exact i.isLt
          have hh := herr2 (i : ℕ) hi0
          rw [← hXE_eq (i : ℕ) i.isLt] at hh
          exact hh
      have hSt14 : Work.ConvR.WordC main duP
          (fun vs => ∃ W1 W2 zs W0 zsv, vs = HvdH.cvecVal zsv ::
            HvdH.Val.int ((ss.prod : ℕ) : ℤ) :: Pv :: Pv :: rest ∧
            A1 W1 ∧ A2 W2 ∧ HYP W1 W2 zs ∧ A0 W0 zs ∧ A0X W0 ∧
            HvdH.InDiscVec p ss.prod zsv ∧ ERR zsv)
          (fun _ out => ∃ W1 W2 zs W0 zsv, out = HvdH.cvecVal zsv :: Pv :: rest ∧
            DAT W1 W2 zs W0 zsv) BUD := by
        intro vs hvs s R hR
        obtain ⟨W1, W2, zs, W0, zsv, hvs', hA1, hA2, hHYP, hA0, hA0X, hdisc, herr⟩ := hvs
        obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ :=
          hdu main (HvdH.cvecVal zsv) (HvdH.Val.int ((ss.prod : ℕ) : ℤ)) Pv (Pv :: rest)
            vs hvs' s R hR
        refine ⟨out, s', n, ⟨W1, W2, zs, W0, zsv, hq, hA1, hA2, hHYP, hA0, hdisc, herr⟩,
          he, ?_, hstk, hoth⟩
        have hz := hszCV zsv hdisc
        exact le_trans hn
          (budget1 (B := HvdH.vsz (HvdH.cvecVal zsv) +
              HvdH.vsz (HvdH.Val.int ((ss.prod : ℕ) : ℤ)) + HvdH.vsz Pv + 1)
            (CB := 180000) (H := 8000000000) hKdu_le (by omega) (by norm_num))
      have hSt15 : Work.ConvR.WordC main (rollP 1)
          (fun vs => ∃ W1 W2 zs W0 zsv, vs = HvdH.cvecVal zsv :: Pv :: rest ∧
            DAT W1 W2 zs W0 zsv)
          (fun _ out => ∃ W1 W2 zs W0 zsv, out = Pv :: HvdH.cvecVal zsv :: rest ∧
            DAT W1 W2 zs W0 zsv) BUD := by
        intro vs hvs s R hR
        obtain ⟨W1, W2, zs, W0, zsv, hvs', hDAT⟩ := hvs
        obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ :=
          Work.ConvR.WordC.rollStep hK hroll (k := 1)
            (L := HvdH.cvecVal zsv :: Pv :: rest) (L' := Pv :: HvdH.cvecVal zsv :: rest)
            (by simp) (by simp)
            (budget2 (A := Kr * 2) (B := HvdH.vsz (HvdH.cvecVal zsv) + HvdH.vsz Pv + 1)
              (KB := KB) (S0 := S0) (CA := 60000) (CB := 120000) (H := 8000000000)
              (Nat.mul_le_mul hKr_le (by norm_num)) (by
                have hz := hszCV zsv hDAT.2.2.2.2.1
                omega) (by norm_num))
            vs hvs' s R hR
        exact ⟨out, s', n, ⟨W1, W2, zs, W0, zsv, hq, hDAT⟩, he, hn, hstk, hoth⟩
      have hSt16 : Work.ConvR.WordC main dropP
          (fun vs => ∃ W1 W2 zs W0 zsv, vs = Pv :: HvdH.cvecVal zsv :: rest ∧
            DAT W1 W2 zs W0 zsv)
          (fun _ out => ∃ W1 W2 zs W0 zsv, out = HvdH.cvecVal zsv :: rest ∧
            DAT W1 W2 zs W0 zsv) BUD := by
        intro vs hvs s R hR
        obtain ⟨W1, W2, zs, W0, zsv, hvs', hDAT⟩ := hvs
        obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ :=
          Work.ConvR.WordC.dropStep hK hdrop (L := Pv :: HvdH.cvecVal zsv :: rest)
            (L' := HvdH.cvecVal zsv :: rest) (by simp) rfl
            (budget1 (B := HvdH.vsz Pv + 1) (CB := 60000) (H := 8000000000) hKd_le
              (by calc HvdH.vsz Pv + 1 ≤ Lm + 1 := Nat.add_le_add_right hszP 1
                    _ ≤ 60000 * S0 := hLmb) (by norm_num))
            vs hvs' s R hR
        exact ⟨out, s', n, ⟨W1, W2, zs, W0, zsv, hq, hDAT⟩, he, hn, hstk, hoth⟩
      have hchain := seqW hK (seqW hK (seqW hK (seqW hK (seqW hK (seqW hK (seqW hK (seqW hK
        (seqW hK (seqW hK (seqW hK (seqW hK (seqW hK (seqW hK (seqW hK hSt1 hSt2) hSt3) hSt4)
        hSt5) hSt6) hSt7) hSt8) hSt9) hSt10) hSt11) hSt12) hSt13) hSt14) hSt15) hSt16
      exact Work.ConvR.WordC.conseq hK hchain (fun vs h => h) (fun vs out hvs hq => hq)
        (le_trans (chainBudget (B := BUD) (F := HvdH.fsCost K52 Cm p α ts))
          (by have := hBUDle; nlinarith [this]))
    -- the error argument: from the data to the final approximation
    have hderive : ∀ (out : List HvdH.Val),
        (∃ W1 W2 zs W0 zsv, out = HvdH.cvecVal zsv :: rest ∧ DAT W1 W2 zs W0 zsv) →
        (∃ zs : List (ℤ × ℤ), out = HvdH.cvecVal zs :: rest ∧
          HvdH.Approx p zs (HvdH.convC ss (HvdH.fxVec p ss.prod us) (HvdH.fxVec p ss.prod ws))
            ((2 ^ (2 * HvdH.D * α ^ 2 + 8) * ts.prod ^ 2 * Nat.log 2 ts.prod : ℕ) : ℝ)) := by
      intro out h
      obtain ⟨W1, W2, zs, W0, zsv, hout, hA1, hA2, hHYP, hA0, hdisc, herr⟩ := h
      obtain ⟨hzslen, hzsd, hCM⟩ := hHYP
      refine ⟨zsv, hout, hdisc, fun i => ?_⟩
      have hCM' : ∀ i : Fin ss.prod, (2 : ℝ) ^ p * ‖HvdH.fxC p (zs.getD i (0,0)) -
          HvdH.fxC p (W1.getD i (0,0)) * HvdH.fxC p (W2.getD i (0,0))‖ < 2 := by
        intro i
        have hh := hCM i
        rwa [mul_comm (HvdH.fxC p (W2.getD i (0,0)))] at hh
      have hchain : HvdH.Approx p W0 XE (E5 + E5 + E5 + 2) :=
        approxChain hDFT p ss hpos' us ws W1 W2 zs W0 E5 E5 E5 hus hws hA1 hA2 hzsd hCM' hA0
      have hW0 : (2 : ℝ) ^ p * ‖HvdH.fxC p (W0.getD i (0,0)) - XE i‖ < E5 + E5 + E5 + 2 :=
        hchain.2 i
      have hSne : (ss.prod : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (List.prod_pos hpos'))
      have hXE : (ss.prod : ℂ) * XE i =
          HvdH.convC ss (HvdH.fxVec p ss.prod us) (HvdH.fxVec p ss.prod ws) i := by
        rw [show XE i = (1 / (ss.prod : ℂ)) *
            HvdH.convC ss (HvdH.fxVec p ss.prod us) (HvdH.fxVec p ss.prod ws) i by
          simp only [XE, Pi.smul_apply, smul_eq_mul]]
        rw [← mul_assoc, mul_one_div, div_self hSne, one_mul]
      have hS3 : E5 + E5 + E5 + 2 = 3 * ((2 ^ (2 * HvdH.D * α ^ 2 + 5) * ts.prod *
          Nat.log 2 ts.prod : ℕ) : ℝ) + 2 := by
        simp only [E5]; ring
      have hfin : 2 * (ss.prod : ℝ) * (E5 + E5 + E5 + 2) + 3
          < ((2 ^ (2 * HvdH.D * α ^ 2 + 8) * ts.prod ^ 2 * Nat.log 2 ts.prod : ℕ) : ℝ) := by
        rw [hS3]
        exact finalArith ss.prod ts.prod α (Nat.log 2 ts.prod) hST hT3 rfl
      have hErr := herr i
      rw [hXE] at hErr
      exact lt_trans hErr hfin
    have hbuilt2 : HvdH.WordR main
        (pushP (HvdH.Val.int (-1)) ;;; pushP (HvdH.Val.int (1 : ℤ)) ;;; pwProg planA ;;; p52 ;;;
          pwProg planC ;;; p52 ;;; zipC mulE ;;; pwProg planE ;;; p52 ;;; rollP 1 ;;; lpProg ;;;
          rollP 1 ;;; svProg ;;; duP ;;; rollP 1 ;;; dropP)
        (fun w => w = [Pv, Av, Sv, Tv, HvdH.cvecVal us, HvdH.cvecVal ws] ++ rest)
        (fun _ out => ∃ zs : List (ℤ × ℤ), out = HvdH.cvecVal zs :: rest ∧
          HvdH.Approx p zs (HvdH.convC ss (HvdH.fxVec p ss.prod us) (HvdH.fxVec p ss.prod ws))
            ((2 ^ (2 * HvdH.D * α ^ 2 + 8) * ts.prod ^ 2 * Nat.log 2 ts.prod : ℕ) : ℝ))
        (fun _ => 3 * HvdH.fsCost (K52 + KE) Cm p α ts + (K52 + KE)) :=
      hK.conseq main _ (fun w => w = [Pv, Av, Sv, Tv, HvdH.cvecVal us, HvdH.cvecVal ws] ++ rest)
        (fun w => w = [Pv, Av, Sv, Tv, HvdH.cvecVal us, HvdH.cvecVal ws] ++ rest)
        (fun _ out => ∃ W1 W2 zs W0 zsv, out = HvdH.cvecVal zsv :: rest ∧ DAT W1 W2 zs W0 zsv)
        (fun _ out => ∃ zs : List (ℤ × ℤ), out = HvdH.cvecVal zs :: rest ∧
          HvdH.Approx p zs (HvdH.convC ss (HvdH.fxVec p ss.prod us) (HvdH.fxVec p ss.prod ws))
            ((2 ^ (2 * HvdH.D * α ^ 2 + 8) * ts.prod ^ 2 * Nat.log 2 ts.prod : ℕ) : ℝ))
        (fun _ => 3 * HvdH.fsCost K52 Cm p α ts + 13 * KE0 * S0)
        (fun _ => 3 * HvdH.fsCost (K52 + KE) Cm p α ts + (K52 + KE))
        hbuilt (fun w h => h) (fun w out h hq => hderive out hq) (fun w h => hcostfinal)
    intro s R hs
    obtain ⟨out, s', n, hp, hev, hn, hstk, hfr⟩ := hbuilt2 vs hvs s R hs
    obtain ⟨zs, hout, hap⟩ := hp
    exact ⟨out, s', n, ⟨us, ws, rest, zs, hvs, hout, hap⟩, hev, hn, hstk, hfr⟩
  exact hCore

end Work.MainP
