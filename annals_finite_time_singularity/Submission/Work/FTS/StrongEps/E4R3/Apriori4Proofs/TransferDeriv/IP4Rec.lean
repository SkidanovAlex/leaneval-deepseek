import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.IP4Prep
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.IP4Slots
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.IP4Leaf
import Submission.Work.FTS.StrongEps.EpsE4Thr.WordCongr
import Submission.Work.FTS.IPGen.Defs
import Submission.Work.FTS.StrongEps.Dth_Jeps
import Submission.Work.FTS.StrongEps.mixed_Jeps

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TransferDeriv/IP4Rec.lean` — the recursion of the transfer defect

With `Def n b a` the transfer defect of the `n`-th pairing of the recursion at the slot `(a,b)`,
`HkIPStep` gives `Def (n+1) b a = Def n b a + c₁ Def n b (a+1) + c₂ Def n (b+1) a`; every slot
order stays below four (first argument) and five (second argument), so the level-zero bound is
uniform and the recursion multiplies the constant by `1 + |c₁| + |c₂|` at each step.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## The recursion of the pairings -/

/-- The coefficient pairs of the three steps of `Assembly.IP4`. -/
def stepC (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) : ℕ → ℝ × ℝ
  | 0 => (c₁, c₂)
  | 1 => (c₁', c₂')
  | _ => (c₁'', c₂'')

@[simp] theorem stepC_zero (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) :
    stepC c₁ c₂ c₁' c₂' c₁'' c₂'' 0 = (c₁, c₂) := rfl

@[simp] theorem stepC_one (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) :
    stepC c₁ c₂ c₁' c₂' c₁'' c₂'' 1 = (c₁', c₂') := rfl

theorem stepC_two (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) :
    stepC c₁ c₂ c₁' c₂' c₁'' c₂'' 2 = (c₁'', c₂'') := rfl

/-- The coercive recursion `HkIPStep`, iterated from `H1IP α` with free coefficient pairs. -/
noncomputable def QP (α : ℝ) (c : ℕ → ℝ × ℝ) : ℕ → Fn → Fn → ℝ
  | 0 => Work.Coercivity.H1IP α
  | n + 1 => Work.Coercivity.HkIPStep (c n).1 (c n).2 (QP α c n)

theorem QP_succ (α : ℝ) (c : ℕ → ℝ × ℝ) (n : ℕ) :
    QP α c (n + 1) = Work.Coercivity.HkIPStep (c n).1 (c n).2 (QP α c n) := rfl

/-- **The three-step recursion is `Assembly.IP4`.** -/
theorem QP_three_eq_IP4 (α : ℝ) (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) :
    QP α (stepC c₁ c₂ c₁' c₂' c₁'' c₂'') 3
      = Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α := by
  show Work.Coercivity.HkIPStep c₁'' c₂'' (Work.Coercivity.HkIPStep c₁' c₂'
      (Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α))) = _
  exact Work.FTS.IPGen.IPnG_eq_IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α

/-- `QP` only sees its two arguments on the open quadrant. -/
theorem QP_congr (α : ℝ) (c : ℕ → ℝ × ℝ) : ∀ n : ℕ, ∀ {X X' Y Y' : Fn},
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → X z θ = X' z θ) →
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → Y z θ = Y' z θ) →
    QP α c n X Y = QP α c n X' Y' := by
  intro n
  induction n with
  | zero => intro X X' Y Y' hX hY; exact Work.FTS.StrongEps.EpsE4Thr.H1IP_congr_Q0 α hX hY
  | succ n ih =>
      intro X X' Y Y' hX hY
      show QP α c n X Y + (c n).1 * QP α c n (Work.Spaces.Dth X) (Work.Spaces.Dth Y)
          + (c n).2 * QP α c n (Work.Spaces.Dz X) (Work.Spaces.Dz Y)
        = QP α c n X' Y' + (c n).1 * QP α c n (Work.Spaces.Dth X') (Work.Spaces.Dth Y')
          + (c n).2 * QP α c n (Work.Spaces.Dz X') (Work.Spaces.Dz Y')
      rw [ih hX hY,
        ih (Work.FTS.CoercivityStep.Base.Dth_congr_Qd hX)
          (Work.FTS.CoercivityStep.Base.Dth_congr_Qd hY),
        ih (Work.FTS.CoercivityStep.Base.Dz_congr_Qd hX)
          (Work.FTS.CoercivityStep.Base.Dz_congr_Qd hY)]

/-- `QP` only sees its *first* argument on the open quadrant. -/
theorem QP_congr_fst (α : ℝ) (c : ℕ → ℝ × ℝ) (n : ℕ) {X X' Y : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → X z θ = X' z θ) :
    QP α c n X Y = QP α c n X' Y :=
  QP_congr α c n h (fun _ _ _ => rfl)

/-- `QP` only sees its *second* argument on the open quadrant. -/
theorem QP_congr_snd (α : ℝ) (c : ℕ → ℝ × ℝ) (n : ℕ) {X Y Y' : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → Y z θ = Y' z θ) :
    QP α c n X Y = QP α c n X Y' :=
  QP_congr α c n (fun _ _ _ => rfl) h

/-- The constant of the recursion: the product of the `1 + |c₁| + |c₂|` of the steps. -/
def KCB (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => KCB c₁ c₂ c₁' c₂' c₁'' c₂'' n *
      (1 + |(stepC c₁ c₂ c₁' c₂' c₁'' c₂'' n).1| + |(stepC c₁ c₂ c₁' c₂' c₁'' c₂'' n).2|)

@[simp] theorem KCB_zero (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) :
    KCB c₁ c₂ c₁' c₂' c₁'' c₂'' 0 = 1 := rfl

@[simp] theorem KCB_succ (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) (n : ℕ) :
    KCB c₁ c₂ c₁' c₂' c₁'' c₂'' (n + 1) = KCB c₁ c₂ c₁' c₂' c₁'' c₂'' n *
      (1 + |(stepC c₁ c₂ c₁' c₂' c₁'' c₂'' n).1|
        + |(stepC c₁ c₂ c₁' c₂' c₁'' c₂'' n).2|) := rfl

theorem KCB_nonneg (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) (n : ℕ) :
    0 ≤ KCB c₁ c₂ c₁' c₂' c₁'' c₂'' n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [KCB_succ]
      exact mul_nonneg ih (by positivity)

theorem KCB_three (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) :
    KCB c₁ c₂ c₁' c₂' c₁'' c₂'' 3
      = (1 + |c₁| + |c₂|) * (1 + |c₁'| + |c₂'|) * (1 + |c₁''| + |c₂''|) := by
  simp only [KCB_succ, KCB_zero, stepC_zero, stepC_one, stepC_two]
  ring

/-- The transfer defect of the level-`n` pairing at the slot `(a,b)`. -/
noncomputable def Def (α : ℝ) (c : ℕ → ℝ × ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (f h : Fn)
    (n b a : ℕ) : ℝ :=
  QP α c n (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a f)) (Work.Spaces.mixed b a h)
    - QP α c n (Work.Spaces.mixed b a f)
        (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a h))

/-- **The recursion of the transfer defect**: `D_θ` and `D_z` shift the slot by one. -/
theorem Def_succ (α : ℝ) (c : ℕ → ℝ × ℝ) {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) {f h : Fn}
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) (hhs : Work.FTS.EllipticEst.SmoothOpen h)
    (n b a : ℕ) :
    Def α c ρ ε f h (n + 1) b a
      = Def α c ρ ε f h n b a + (c n).1 * Def α c ρ ε f h n b (a + 1)
        + (c n).2 * Def α c ρ ε f h n (b + 1) a := by
  have hA : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.mixed b a f) := hfs.mixed b a
  have hB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.mixed b a h) := hhs.mixed b a
  -- the `J_ε`-commutation on the open quadrant
  have hdA : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.Dth (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a f)) z θ
        = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.Dth (Work.Spaces.mixed b a f)) z θ :=
    fun z θ hh => Work.FTS.StrongEps.Dth_Jeps ρ hρ hε (hA.forall 1)
      ((hA.pth.forall 1).continuousOn) hh.1 hh.2
  have hdB : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.Dth (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a h)) z θ
        = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.Dth (Work.Spaces.mixed b a h)) z θ :=
    fun z θ hh => Work.FTS.StrongEps.Dth_Jeps ρ hρ hε (hB.forall 1)
      ((hB.pth.forall 1).continuousOn) hh.1 hh.2
  have hzA : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.Dz (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a f)) z θ
        = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.Dz (Work.Spaces.mixed b a f)) z θ :=
    fun z θ hh => Work.FTS.StrongEps.Dz_Jeps hρ hε (hA.forall 1)
      ((hA.pz.forall 1).continuousOn) hh.1 hh.2
  have hzB : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.Dz (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a h)) z θ
        = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.Dz (Work.Spaces.mixed b a h)) z θ :=
    fun z θ hh => Work.FTS.StrongEps.Dz_Jeps hρ hε (hB.forall 1)
      ((hB.pz.forall 1).continuousOn) hh.1 hh.2
  -- the two slot shifts
  have hsA : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ = Work.Spaces.mixed b (a + 1) f z θ :=
    Dth_mixed_apply hfs b a
  have hsB : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.Dth (Work.Spaces.mixed b a h) z θ = Work.Spaces.mixed b (a + 1) h z θ :=
    Dth_mixed_apply hhs b a
  have hJA : Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.Dth (Work.Spaces.mixed b a f))
      = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b (a + 1) f) :=
    Jeps_congr_Q0 hsA ρ ε
  have hJB : Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.Dth (Work.Spaces.mixed b a h))
      = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b (a + 1) h) :=
    Jeps_congr_Q0 hsB ρ ε
  -- the four shifted pairing terms
  have e1 : QP α c n (Work.Spaces.Dth (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a f)))
        (Work.Spaces.Dth (Work.Spaces.mixed b a h))
      = QP α c n (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b (a + 1) f))
        (Work.Spaces.mixed b (a + 1) h) :=
    (QP_congr_fst α c n hdA).trans
      ((QP_congr_fst α c n (fun _ _ _ => by rw [hJA])).trans
        (QP_congr_snd α c n hsB))
  have e2 : QP α c n (Work.Spaces.Dth (Work.Spaces.mixed b a f))
        (Work.Spaces.Dth (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a h)))
      = QP α c n (Work.Spaces.mixed b (a + 1) f)
        (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b (a + 1) h)) :=
    (QP_congr_snd α c n hdB).trans
      ((QP_congr_snd α c n (fun _ _ _ => by rw [hJB])).trans
        (QP_congr_fst α c n hsA))
  have e3 : QP α c n (Work.Spaces.Dz (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a f)))
        (Work.Spaces.Dz (Work.Spaces.mixed b a h))
      = QP α c n (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed (b + 1) a f))
        (Work.Spaces.mixed (b + 1) a h) :=
    (QP_congr_fst α c n hzA).trans (QP_congr_snd α c n (fun _ _ _ => rfl))
  have e4 : QP α c n (Work.Spaces.Dz (Work.Spaces.mixed b a f))
        (Work.Spaces.Dz (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a h)))
      = QP α c n (Work.Spaces.mixed (b + 1) a f)
        (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed (b + 1) a h)) :=
    (QP_congr_snd α c n hzB).trans (QP_congr_fst α c n (fun _ _ _ => rfl))
  unfold Def
  rw [QP_succ]
  simp only [Work.Coercivity.HkIPStep]
  rw [e1, e2, e3, e4]
  ring

/-- **The transfer bound at every level.**  Every slot order stays below four for the first
argument and five for the second, so the level-zero bound applies uniformly and the recursion
multiplies the constant by `1 + |c₁| + |c₂|` at each step. -/
theorem Def_bound {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {K : ℝ}
    (hK : 0 ≤ K) (hST : SlotTransfer ρ K) {α : ℝ} (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    {ε : ℝ} (hε : ε ∈ Set.Ioc (0 : ℝ) 1) {f h : Fn}
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) (hhs : Work.FTS.EllipticEst.SmoothOpen h)
    (hmf : Work.Spaces.HkMem α 4 f) (hmh : Work.Spaces.HkMem α 5 h)
    (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) :
    ∀ n b a : ℕ, a + b + n ≤ 3 →
      |Def α (stepC c₁ c₂ c₁' c₂' c₁'' c₂'') ρ ε f h n b a|
        ≤ KCB c₁ c₂ c₁' c₂' c₁'' c₂'' n
          * (3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * K * ε
              * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 5 h) := by
  intro n
  induction n with
  | zero =>
      intro b a hab
      have h := leaf_bound hρ hK hST hα hε hfs hhs hmf hmh (a₀ := a) (b₀ := b) (by omega)
      simpa only [Def, QP, KCB_zero, one_mul] using h
  | succ n ih =>
      intro b a hab
      have h1 : a + b + n ≤ 3 := by omega
      have h2 : (a + 1) + b + n ≤ 3 := by omega
      have h3 : a + (b + 1) + n ≤ 3 := by omega
      have i1 := ih b a h1
      have i2 := ih b (a + 1) h2
      have i3 := ih (b + 1) a h3
      have hrec := Def_succ α (stepC c₁ c₂ c₁' c₂' c₁'' c₂'') hρ.moll hε.1 hfs hhs n b a
      set D0 := Def α (stepC c₁ c₂ c₁' c₂' c₁'' c₂'') ρ ε f h n b a with hD0
      set D1 := Def α (stepC c₁ c₂ c₁' c₂' c₁'' c₂'') ρ ε f h n b (a + 1) with hD1
      set D2 := Def α (stepC c₁ c₂ c₁' c₂' c₁'' c₂'') ρ ε f h n (b + 1) a with hD2
      have j1 : |D0| ≤ KCB c₁ c₂ c₁' c₂' c₁'' c₂'' n
          * (3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * K * ε
              * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 5 h) := by
        exact i1
      have j2 : |D1| ≤ KCB c₁ c₂ c₁' c₂' c₁'' c₂'' n
          * (3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * K * ε
              * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 5 h) := by
        exact i2
      have j3 : |D2| ≤ KCB c₁ c₂ c₁' c₂' c₁'' c₂'' n
          * (3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * K * ε
              * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 5 h) := by
        exact i3
      rw [hrec, hD0, hD1, hD2, KCB_succ]
      have hA := abs_add_le (D0 + (stepC c₁ c₂ c₁' c₂' c₁'' c₂'' n).1 * D1)
        ((stepC c₁ c₂ c₁' c₂' c₁'' c₂'' n).2 * D2)
      have hB := abs_add_le D0 ((stepC c₁ c₂ c₁' c₂' c₁'' c₂'' n).1 * D1)
      rw [abs_mul] at hA hB
      have e : KCB c₁ c₂ c₁' c₂' c₁'' c₂'' n
            * (1 + |(stepC c₁ c₂ c₁' c₂' c₁'' c₂'' n).1|
              + |(stepC c₁ c₂ c₁' c₂' c₁'' c₂'' n).2|)
            * (3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * K * ε
                * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 5 h)
          = KCB c₁ c₂ c₁' c₂' c₁'' c₂'' n
              * (3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * K * ε
                  * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 5 h)
            + |(stepC c₁ c₂ c₁' c₂' c₁'' c₂'' n).1|
                * (KCB c₁ c₂ c₁' c₂' c₁'' c₂'' n
                  * (3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * K * ε
                      * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 5 h))
            + |(stepC c₁ c₂ c₁' c₂' c₁'' c₂'' n).2|
                * (KCB c₁ c₂ c₁' c₂' c₁'' c₂'' n
                  * (3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * K * ε
                      * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 5 h)) := by ring
      linarith [hA, hB, j1, j2, j3, e,
        mul_le_mul_of_nonneg_left j2 (abs_nonneg ((stepC c₁ c₂ c₁' c₂' c₁'' c₂'' n).1)),
        mul_le_mul_of_nonneg_left j3 (abs_nonneg ((stepC c₁ c₂ c₁' c₂' c₁'' c₂'' n).2))]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
