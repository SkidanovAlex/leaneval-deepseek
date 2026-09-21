import Mathlib
import Submission.Work.Geometry.Ulam.ulam_J_polynomial
import Submission.Work.Geometry.Ulam.ulam_faa_j
import Submission.Work.Analysis.Calculus.IteratedDeriv.contDiff_iteratedDeriv_param
import Submission.Work.Geometry.Ulam.ulam_volterra_state

set_option maxHeartbeats 800000

namespace Commons.Geometry.Ulam

open scoped ContDiff Topology

noncomputable section

/-- The affine function `L_s(t) = s t + h(s)` from the paper. -/
def ulamLine (h : ℝ → ℝ) (s t : ℝ) : ℝ := s * t + h s

/-- The divided difference `H(s,σ) = (h σ - h s)/(σ - s)`.  At `σ = s` we use the
value `0`; the paper only needs the off-diagonal values under the integral, and
the diagonal is handled separately by the averaged kernel. -/
def ulamHquot (h : ℝ → ℝ) (s σ : ℝ) : ℝ :=
  if σ = s then 0 else (h σ - h s) / (σ - s)

/-- The paper's `J₁(s,t,f)`, realized from the Faà-di-Bruno representation for
`U(x) = f² - (x t + h x)²`. -/
def ulamJ1 (n : ℕ) (h : ℝ → ℝ) (s t f : ℝ) : ℝ :=
  faaDiBrunoJ (n + 1) ((n : ℝ) + 1 / 2) s
    (fun i : Fin (n + 2) => iteratedDeriv i.1 (fun x : ℝ => f ^ 2 - ulamLine h x t ^ 2) s)

/-- The paper's `J₂(s,t,f)`, realized from the Faà-di-Bruno representation for
`U(x) = f² - (x t + h x)²`. -/
def ulamJ2 (n : ℕ) (h : ℝ → ℝ) (s t f : ℝ) : ℝ :=
  faaDiBrunoJ n ((n : ℝ) - 1 / 2) s
    (fun i : Fin (n + 1) => iteratedDeriv i.1 (fun x : ℝ => f ^ 2 - ulamLine h x t ^ 2) s)

/-- The paper's `K₁(s,σ,t)`. -/
def ulamK1 (n : ℕ) (h : ℝ → ℝ) (s σ t : ℝ) : ℝ :=
  ulamJ1 n h s t (ulamLine h σ t) /
    Real.sqrt ((t + ulamHquot h s σ) * (ulamLine h σ t + ulamLine h s t))

/-- The paper's `K₂(s,σ,t)`. -/
def ulamK2 (n : ℕ) (h : ℝ → ℝ) (s σ t : ℝ) : ℝ :=
  ulamJ2 n h s t (ulamLine h σ t) /
    Real.sqrt ((t + ulamHquot h s σ) * (ulamLine h σ t + ulamLine h s t))

/-- The two-component kernel `K` of the Abel-reduced equation, as a function of
the state `(x,y,x',y')`. -/
def ulamK (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : UlamState) : UlamState2 :=
  ![- (ulamK1 n h s σ (-(z 0)) * z 2 + ulamK1 n h s σ (z 1) * z 3),
    - (ulamK2 n h s σ (-(z 0)) * z 2 + ulamK2 n h s σ (z 1) * z 3)]

/-- `ulamJ1` is smooth in `(s,t,f)` on the region where its radicand is positive. -/
lemma ulamJ1_contDiffOn (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ × ℝ => ulamJ1 n h p.1 p.2.1 p.2.2)
      {p | 0 < p.2.2 ^ 2 - ulamLine h p.1 p.2.1 ^ 2} := by
  let U : ℝ × (ℝ × ℝ) → ℝ := fun xq => xq.2.2 ^ 2 - ulamLine h xq.1 xq.2.1 ^ 2
  have hU : ContDiff ℝ ∞ U := by
    dsimp [U, ulamLine]
    fun_prop
  let jet : (ℝ × ℝ × ℝ) → (Fin (n + 2) → ℝ) := fun p =>
    fun i => iteratedDeriv i.1 (fun x : ℝ => U (x, (p.2.1, p.2.2))) p.1
  have hjet : ContDiff ℝ ∞ jet := by
    apply contDiff_pi.mpr
    intro i
    simpa [jet] using
      (Commons.Analysis.Calculus.contDiff_iteratedDeriv_param (E := ℝ × ℝ) (i := i.1) hU)
  let G : (Fin (n + 2) → ℝ) → ℝ := fun v => faaDiBrunoJ (n + 1) ((n : ℝ) + 1 / 2) 0 v
  have hG : ContDiffOn ℝ ∞ G {v | 0 < v 0} :=
    faaDiBrunoJ_contDiffOn (n + 1) ((n : ℝ) + 1 / 2) 0
  have hmap : Set.MapsTo jet {p : ℝ × ℝ × ℝ | 0 < p.2.2 ^ 2 - ulamLine h p.1 p.2.1 ^ 2}
      {v : Fin (n + 2) → ℝ | 0 < v 0} := by
    intro p hp
    simpa [jet, U] using hp
  have hcomp := hG.comp hjet.contDiffOn hmap
  convert hcomp using 1
  funext p
  dsimp [G, jet, ulamJ1, U]
  rfl

/-- `ulamJ2` is smooth in `(s,t,f)` on the region where its radicand is positive. -/
lemma ulamJ2_contDiffOn (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ × ℝ => ulamJ2 n h p.1 p.2.1 p.2.2)
      {p | 0 < p.2.2 ^ 2 - ulamLine h p.1 p.2.1 ^ 2} := by
  let U : ℝ × (ℝ × ℝ) → ℝ := fun xq => xq.2.2 ^ 2 - ulamLine h xq.1 xq.2.1 ^ 2
  have hU : ContDiff ℝ ∞ U := by
    dsimp [U, ulamLine]
    fun_prop
  let jet : (ℝ × ℝ × ℝ) → (Fin (n + 1) → ℝ) := fun p =>
    fun i => iteratedDeriv i.1 (fun x : ℝ => U (x, (p.2.1, p.2.2))) p.1
  have hjet : ContDiff ℝ ∞ jet := by
    apply contDiff_pi.mpr
    intro i
    simpa [jet] using
      (Commons.Analysis.Calculus.contDiff_iteratedDeriv_param (E := ℝ × ℝ) (i := i.1) hU)
  let G : (Fin (n + 1) → ℝ) → ℝ := fun v => faaDiBrunoJ n ((n : ℝ) - 1 / 2) 0 v
  have hG : ContDiffOn ℝ ∞ G {v | 0 < v 0} :=
    faaDiBrunoJ_contDiffOn n ((n : ℝ) - 1 / 2) 0
  have hmap : Set.MapsTo jet {p : ℝ × ℝ × ℝ | 0 < p.2.2 ^ 2 - ulamLine h p.1 p.2.1 ^ 2}
      {v : Fin (n + 1) → ℝ | 0 < v 0} := by
    intro p hp
    simpa [jet, U] using hp
  have hcomp := hG.comp hjet.contDiffOn hmap
  convert hcomp using 1
  funext p
  dsimp [G, jet, ulamJ2, U]
  rfl

/-- The `J₁` representation specialized to the paper's `U(x) = f² - (x t + h x)²`. -/
lemma ulamJ1_spec (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (s t f : ℝ) (hpos : 0 < f ^ 2 - ulamLine h s t ^ 2) :
    iteratedDeriv (n + 1)
        (fun x : ℝ => (f ^ 2 - ulamLine h x t ^ 2) ^ ((n : ℝ) + 1 / 2)) s =
      ulamJ1 n h s t f / Real.sqrt (f ^ 2 - ulamLine h s t ^ 2) := by
  have hu : ContDiff ℝ ∞ (fun x : ℝ => f ^ 2 - ulamLine h x t ^ 2) := by
    unfold ulamLine
    fun_prop
  have hrep := faaDiBrunoJ_spec (n + 1) ((n : ℝ) + 1 / 2)
    (fun x : ℝ => f ^ 2 - ulamLine h x t ^ 2) s hu hpos
  have hpow : (f ^ 2 - ulamLine h s t ^ 2) ^
        (((n : ℝ) + 1 / 2) - ((n + 1 : ℕ) : ℝ)) =
        1 / Real.sqrt (f ^ 2 - ulamLine h s t ^ 2) := by
    have hexp : ((n : ℝ) + 1 / 2) - ((n + 1 : ℕ) : ℝ) = -(1 / 2) := by
      push_cast
      ring
    rw [hexp, Real.rpow_neg (le_of_lt hpos), Real.sqrt_eq_rpow]
    norm_num
  rw [hrep, hpow, ulamJ1, div_eq_mul_inv]
  ring

/-- The `J₂` representation specialized to the paper's `U(x) = f² - (x t + h x)²`. -/
lemma ulamJ2_spec (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (s t f : ℝ) (hpos : 0 < f ^ 2 - ulamLine h s t ^ 2) :
    iteratedDeriv n
        (fun x : ℝ => (f ^ 2 - ulamLine h x t ^ 2) ^ ((n : ℝ) - 1 / 2)) s =
      ulamJ2 n h s t f / Real.sqrt (f ^ 2 - ulamLine h s t ^ 2) := by
  have hu : ContDiff ℝ ∞ (fun x : ℝ => f ^ 2 - ulamLine h x t ^ 2) := by
    unfold ulamLine
    fun_prop
  have hrep := faaDiBrunoJ_spec n ((n : ℝ) - 1 / 2)
    (fun x : ℝ => f ^ 2 - ulamLine h x t ^ 2) s hu hpos
  have hpow : (f ^ 2 - ulamLine h s t ^ 2) ^
        (((n : ℝ) - 1 / 2) - (n : ℝ)) =
        1 / Real.sqrt (f ^ 2 - ulamLine h s t ^ 2) := by
    have hexp : ((n : ℝ) - 1 / 2) - (n : ℝ) = -(1 / 2) := by ring
    rw [hexp, Real.rpow_neg (le_of_lt hpos), Real.sqrt_eq_rpow]
    norm_num
  rw [hrep, hpow, ulamJ2, div_eq_mul_inv]
  ring

/-- `ulamHquot` is smooth off the diagonal `s = σ`. -/
lemma ulamHquot_contDiffOn {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => ulamHquot h p.1 p.2) {p | p.1 ≠ p.2} := by
  refine (contDiffOn_congr (s := {p : ℝ × ℝ | p.1 ≠ p.2})
    (f := fun p : ℝ × ℝ => (h p.2 - h p.1) / (p.2 - p.1)) ?_).mpr ?_
  · intro p hp
    simp [ulamHquot, Ne.symm hp]
  · apply ContDiffOn.div
    · fun_prop
    · fun_prop
    · intro p hp
      exact sub_ne_zero.mpr (Ne.symm hp)

/-- The jet-coordinate tuple map `s ↦ (s, (t, L_σ(t)))` is smooth. -/
lemma ulam_jet_tuple_contDiffOn {h : ℝ → ℝ} (_hh : ContDiff ℝ ∞ h) (σ t : ℝ) :
    ContDiffOn ℝ ∞ (fun s : ℝ => (s, (t, ulamLine h σ t))) Set.univ := by
  fun_prop

/-- The numerator of `ulamK1` is smooth in `s` on the positive-radicand region. -/
lemma ulamJ1_jet_contDiffOn (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (σ t : ℝ) :
    ContDiffOn ℝ ∞ (fun s : ℝ => ulamJ1 n h s t (ulamLine h σ t))
      {s | 0 < ulamLine h σ t ^ 2 - ulamLine h s t ^ 2} := by
  have hmap : Set.MapsTo (fun s : ℝ => (s, (t, ulamLine h σ t)))
      {s | 0 < ulamLine h σ t ^ 2 - ulamLine h s t ^ 2}
      {p : ℝ × ℝ × ℝ | 0 < p.2.2 ^ 2 - ulamLine h p.1 p.2.1 ^ 2} := by
    intro s hs
    change 0 < (ulamLine h σ t) ^ 2 - ulamLine h s t ^ 2
    exact hs
  exact ContDiffOn.comp
    (g := fun p : ℝ × ℝ × ℝ => ulamJ1 n h p.1 p.2.1 p.2.2)
    (f := fun s : ℝ => (s, (t, ulamLine h σ t)))
    (s := {s | 0 < ulamLine h σ t ^ 2 - ulamLine h s t ^ 2})
    (t := {p : ℝ × ℝ × ℝ | 0 < p.2.2 ^ 2 - ulamLine h p.1 p.2.1 ^ 2})
    (ulamJ1_contDiffOn n hh)
    ((ulam_jet_tuple_contDiffOn hh σ t).mono (by intro s hs; trivial)) hmap

/-- The numerator of `ulamK2` is smooth in `s` on the positive-radicand region. -/
lemma ulamJ2_jet_contDiffOn (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (σ t : ℝ) :
    ContDiffOn ℝ ∞ (fun s : ℝ => ulamJ2 n h s t (ulamLine h σ t))
      {s | 0 < ulamLine h σ t ^ 2 - ulamLine h s t ^ 2} := by
  have hmap : Set.MapsTo (fun s : ℝ => (s, (t, ulamLine h σ t)))
      {s | 0 < ulamLine h σ t ^ 2 - ulamLine h s t ^ 2}
      {p : ℝ × ℝ × ℝ | 0 < p.2.2 ^ 2 - ulamLine h p.1 p.2.1 ^ 2} := by
    intro s hs
    change 0 < (ulamLine h σ t) ^ 2 - ulamLine h s t ^ 2
    exact hs
  exact ContDiffOn.comp
    (g := fun p : ℝ × ℝ × ℝ => ulamJ2 n h p.1 p.2.1 p.2.2)
    (f := fun s : ℝ => (s, (t, ulamLine h σ t)))
    (s := {s | 0 < ulamLine h σ t ^ 2 - ulamLine h s t ^ 2})
    (t := {p : ℝ × ℝ × ℝ | 0 < p.2.2 ^ 2 - ulamLine h p.1 p.2.1 ^ 2})
    (ulamJ2_contDiffOn n hh)
    ((ulam_jet_tuple_contDiffOn hh σ t).mono (by intro s hs; trivial)) hmap

/-- The denominator of `ulamK1` is smooth off the diagonal. -/
lemma ulamK1_denom_contDiffOn {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (σ t : ℝ) :
    ContDiffOn ℝ ∞
      (fun s : ℝ => (t + ulamHquot h s σ) * (ulamLine h σ t + ulamLine h s t))
      {s | s ≠ σ} := by
  apply ContDiffOn.mul
  · apply ContDiffOn.add
    · exact contDiffOn_const
    · have hmap : Set.MapsTo (fun s : ℝ => (s, σ)) {s | s ≠ σ} {p : ℝ × ℝ | p.1 ≠ p.2} := by
        intro s hs; simpa using hs
      exact (ulamHquot_contDiffOn hh).comp (by fun_prop) hmap
  · apply ContDiffOn.add
    · exact contDiffOn_const
    · dsimp [ulamLine]; fun_prop

/-- `ulamK1` is smooth in its first argument on the positive-radicand region. -/
lemma ulamK1_contDiffOn (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (σ t : ℝ) :
    ContDiffOn ℝ ∞ (fun s : ℝ => ulamK1 n h s σ t)
      {s | s ≠ σ ∧
        0 < ulamLine h σ t ^ 2 - ulamLine h s t ^ 2 ∧
        0 < (t + ulamHquot h s σ) * (ulamLine h σ t + ulamLine h s t)} := by
  unfold ulamK1
  apply ContDiffOn.div
  · refine (ulamJ1_jet_contDiffOn n hh σ t).mono ?_
    intro s hs
    exact hs.2.1
  · have hden := (ulamK1_denom_contDiffOn hh σ t).mono
        (t := {s : ℝ | s ≠ σ ∧
          0 < ulamLine h σ t ^ 2 - ulamLine h s t ^ 2 ∧
          0 < (t + ulamHquot h s σ) * (ulamLine h σ t + ulamLine h s t)}) ?_
    · exact hden.sqrt (by intro s hs; exact ne_of_gt hs.2.2)
    · intro s hs
      exact hs.1
  · intro s hs
    exact ne_of_gt (Real.sqrt_pos_of_pos hs.2.2)

/-- `ulamK2` is smooth in its first argument on the positive-radicand region. -/
lemma ulamK2_contDiffOn (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (σ t : ℝ) :
    ContDiffOn ℝ ∞ (fun s : ℝ => ulamK2 n h s σ t)
      {s | s ≠ σ ∧
        0 < ulamLine h σ t ^ 2 - ulamLine h s t ^ 2 ∧
        0 < (t + ulamHquot h s σ) * (ulamLine h σ t + ulamLine h s t)} := by
  unfold ulamK2
  apply ContDiffOn.div
  · refine (ulamJ2_jet_contDiffOn n hh σ t).mono ?_
    intro s hs
    exact hs.2.1
  · have hden := (ulamK1_denom_contDiffOn hh σ t).mono
        (t := {s : ℝ | s ≠ σ ∧
          0 < ulamLine h σ t ^ 2 - ulamLine h s t ^ 2 ∧
          0 < (t + ulamHquot h s σ) * (ulamLine h σ t + ulamLine h s t)}) ?_
    · exact hden.sqrt (by intro s hs; exact ne_of_gt hs.2.2)
    · intro s hs
      exact hs.1
  · intro s hs
    exact ne_of_gt (Real.sqrt_pos_of_pos hs.2.2)

/-- The set of slopes on which the state-level kernel `ulamK n h · σ z` is smooth:
off the diagonal and with both chord denominators and radicands positive. -/
def ulamKgood (h : ℝ → ℝ) (σ : ℝ) (z : UlamState) : Set ℝ :=
  {s | s ≠ σ ∧
    (0 < ulamLine h σ (-(z 0)) ^ 2 - ulamLine h s (-(z 0)) ^ 2 ∧
      0 < ((-(z 0)) + ulamHquot h s σ) *
        (ulamLine h σ (-(z 0)) + ulamLine h s (-(z 0)))) ∧
    (0 < ulamLine h σ (z 1) ^ 2 - ulamLine h s (z 1) ^ 2 ∧
      0 < (z 1 + ulamHquot h s σ) * (ulamLine h σ (z 1) + ulamLine h s (z 1)))}

/-- First-argument smoothness of the state-level kernel `ulamK`. -/
lemma ulamK_contDiffOn_s (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (σ : ℝ) (z : UlamState) :
    ContDiffOn ℝ ∞ (fun s : ℝ => ulamK n h s σ z) (ulamKgood h σ z) := by
  rw [contDiffOn_pi]
  intro i
  fin_cases i
  · -- first component
    unfold ulamK
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
    apply ContDiffOn.neg
    apply ContDiffOn.add
    · apply ContDiffOn.mul
      · refine (ulamK1_contDiffOn n hh σ (-(z 0))).mono ?_
        intro s hs
        exact ⟨hs.1, hs.2.1⟩
      · exact contDiffOn_const
    · apply ContDiffOn.mul
      · refine (ulamK1_contDiffOn n hh σ (z 1)).mono ?_
        intro s hs
        exact ⟨hs.1, hs.2.2⟩
      · exact contDiffOn_const
  · -- second component
    unfold ulamK
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
    apply ContDiffOn.neg
    apply ContDiffOn.add
    · apply ContDiffOn.mul
      · refine (ulamK2_contDiffOn n hh σ (-(z 0))).mono ?_
        intro s hs
        exact ⟨hs.1, hs.2.1⟩
      · exact contDiffOn_const
    · apply ContDiffOn.mul
      · refine (ulamK2_contDiffOn n hh σ (z 1)).mono ?_
        intro s hs
        exact ⟨hs.1, hs.2.2⟩
      · exact contDiffOn_const

end

end Commons.Geometry.Ulam
