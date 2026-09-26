import Mathlib
import Submission.Work.Box.Defs
import Submission.Work.Sweep.Defs
import Submission.Work.Sweep.Interface
import Submission.Work.BoxSweep.levelCount_aemeasurable
import Submission.Work.BoxSweep.lintegral_levelCount_le_sum

set_option maxHeartbeats 3000000

/-!
# The box sweep: a level of the box norm and a plane level with few intersections

For a knot `K` with distortion bound `d`, a box centre `c` and a coordinate permutation `σ`,
there is a level `s ∈ (r, (1+ε)r)` of the box norm at which the curve meets the boundary
`∂PBox s c σ` in at most `10(1+ε)/ε · d` parameters, and for that same `s` a level `u` with
`|u| < ε r` of the `σ 2`-coordinate at which the curve meets the cutting plane
`{y | y (σ 2) = c (σ 2) + u}` inside the box in at most `5(1+ε)/ε · d` parameters.

Both are pigeonhole arguments on the one-dimensional coarea inequality
(`Work.Sweep.lintegral_mul_levelCount_le_subset`): the level integral of the number of
intersections is at most the arclength of the part of the curve inside a ball of radius
`5 · cc / 2`, and that arclength is at most `2 d · (5 cc) = 10 d cc` by the distortion bound.
Dividing by the length `ε r` of the level interval gives the constants above.

For the box norm one splits `[0, 2π]` into the finitely many disjoint pieces
(`facePiece`) on which a fixed signed coordinate is the first one attaining the box norm
(`Work.BoxSweep.lintegral_levelCount_le_sum`), so that the level count of the box norm is
exactly the sum of the level counts of those coordinate functions: this keeps the
multiplicity one and hence the sharp constant `10 d cc`.
-/

namespace Work.BoxSweep

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-! ## Pigeonhole for an integral bound -/

/-- **Pigeonhole for level counts.** If an integer-valued function `f ≥ 0` has integral at most
`C * (b - a)` over the interval `(a,b)` with `a < b` and `C ≥ 0`, then some point of `(a,b)`
satisfies `f ≤ C`. -/
theorem exists_le_of_lintegral_le {f : ℝ → ENNReal} {a b C : ℝ} (hab : a < b) (hC : 0 ≤ C)
    (hf : ∀ s, f s = ⊤ ∨ ∃ k : ℕ, f s = (k : ENNReal))
    (hint : ∫⁻ s in Set.Ioo a b, f s ≤ ENNReal.ofReal (C * (b - a))) :
    ∃ s ∈ Set.Ioo a b, f s ≤ ENNReal.ofReal C := by
  by_contra h
  push Not at h
  have hlt : ∀ s ∈ Set.Ioo a b, ENNReal.ofReal C < f s := fun s hs => h s hs
  have hpt : ∀ s ∈ Set.Ioo a b, (((⌊C⌋₊ + 1 : ℕ)) : ENNReal) ≤ f s := by
    intro s hs
    rcases hf s with htop | ⟨k, hk⟩
    · rw [htop]; exact le_top
    · rw [hk]
      have h1 : C < (k : ℝ) := by
        have h2 := hlt s hs
        rw [hk] at h2
        have h3 : C < ((k : NNReal) : ℝ) := (ENNReal.ofReal_lt_coe_iff hC).mp h2
        simpa using h3
      have h4 : ⌊C⌋₊ + 1 ≤ k := by
        have h5 : (⌊C⌋₊ : ℝ) ≤ C := Nat.floor_le hC
        have h6 : ((⌊C⌋₊ : ℕ) : ℝ) < (k : ℝ) := lt_of_le_of_lt h5 h1
        have h7 : (⌊C⌋₊ : ℕ) < k := by exact_mod_cast h6
        omega
      exact_mod_cast h4
  have hmono : ∫⁻ s in Set.Ioo a b, (((⌊C⌋₊ + 1 : ℕ)) : ENNReal) ≤ ∫⁻ s in Set.Ioo a b, f s :=
    setLIntegral_mono' measurableSet_Ioo hpt
  rw [setLIntegral_const, Real.volume_Ioo] at hmono
  have hba : 0 < b - a := sub_pos.mpr hab
  have hprod : ENNReal.ofReal (C * (b - a)) <
      (((⌊C⌋₊ + 1 : ℕ)) : ENNReal) * ENNReal.ofReal (b - a) := by
    rw [← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((⌊C⌋₊ + 1 : ℕ) : ℝ))]
    refine ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg hC hba.le) |>.mpr ?_
    have h7 : (⌊C⌋₊ : ℝ) ≤ C := Nat.floor_le hC
    have : C < ((⌊C⌋₊ + 1 : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one C
      push_cast
      linarith
    nlinarith
  have := lt_of_lt_of_le hprod (le_trans hmono hint)
  exact absurd this (lt_irrefl _)

/-- A version of `setLIntegral_mono` needing no measurability of the upper bound. -/
theorem setLIntegral_mono_aux {s : Set ℝ} (hs : MeasurableSet s) {f g : ℝ → ENNReal}
    (h : ∀ x ∈ s, f x ≤ g x) : ∫⁻ x in s, f x ≤ ∫⁻ x in s, g x := by
  rw [← MeasureTheory.lintegral_indicator hs f, ← MeasureTheory.lintegral_indicator hs g]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ s
  · simp [Set.indicator_of_mem, hx, h x hx]
  · simp [Set.indicator_of_notMem, hx]

/-- The set integral of `f` weighted by the indicator of `B` is the set integral of `f` over
`A ∩ B`. -/
theorem setLIntegral_mul_indicator {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (f : ℝ → ENNReal) :
    ∫⁻ t in A, f t * B.indicator (fun _ => (1 : ENNReal)) t = ∫⁻ t in A ∩ B, f t := by
  rw [← MeasureTheory.lintegral_indicator hA]
  rw [show (fun t => A.indicator (fun t => f t * B.indicator (fun _ => (1 : ENNReal)) t) t)
      = (A ∩ B).indicator f from ?_]
  · exact MeasureTheory.lintegral_indicator (hA.inter hB) f
  · funext t
    by_cases htA : t ∈ A <;> by_cases htB : t ∈ B <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, htA, htB]

/-- The level count of a set is either `⊤` or a natural number. -/
theorem levelCount_eq_top_or_nat (f : ℝ → ℝ) (S : Set ℝ) (y : ℝ) :
    Work.Sweep.levelCount f S y = ⊤ ∨ ∃ k : ℕ, Work.Sweep.levelCount f S y = (k : ENNReal) := by
  rcases eq_or_ne ((S ∩ f ⁻¹' {y}).encard) ⊤ with h | h
  · exact Or.inl (by rw [Work.Sweep.levelCount_eq_encard, h]; simp)
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h
    exact Or.inr ⟨k, by rw [Work.Sweep.levelCount_eq_encard, ← hk, ENat.toENNReal_coe]⟩

/-! ## The coordinate functions along the curve -/

/-- The `σ i`-coordinate of the curve, measured from the centre `c` and scaled by the side
length `boxSide i`. Its absolute value is the `i`-th term of the maximum defining `boxNorm`. -/
def coordFun (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (t : ℝ) : ℝ :=
  ((K.curve t).ofLp (σ i) - c.ofLp (σ i)) / Submission.boxSide i

/-- The derivative of `coordFun`. -/
def coordDeriv (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (t : ℝ) : ℝ :=
  ((deriv K.curve t).ofLp (σ i)) / Submission.boxSide i

/-- The box norm of the point `K.curve t`. -/
def boxNormCurve (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (t : ℝ) : ℝ :=
  Submission.boxNorm c σ (K.curve t)

theorem abs_coordFun (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (t : ℝ) :
    |coordFun K c σ i t| = |(K.curve t) (σ i) - c (σ i)| / Submission.boxSide i := by
  rw [coordFun, abs_div, abs_of_pos (Submission.boxSide_pos i)]

theorem boxNormCurve_eq (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (t : ℝ) :
    boxNormCurve K c σ t
      = max (max |coordFun K c σ 0 t| |coordFun K c σ 1 t|) |coordFun K c σ 2 t| := by
  simp only [boxNormCurve, Submission.boxNorm, abs_coordFun]

theorem boxNormCurve_nonneg (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (t : ℝ) :
    0 ≤ boxNormCurve K c σ t := Submission.boxNorm_nonneg c σ (K.curve t)

/-- Some coordinate of the curve attains the box norm. -/
theorem exists_coordFun_eq (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (t : ℝ) :
    ∃ i : Fin 3, |coordFun K c σ i t| = boxNormCurve K c σ t := by
  rw [boxNormCurve_eq]
  rcases le_total |(coordFun K c σ 0 t)| |(coordFun K c σ 1 t)| with h | h
  · rw [max_eq_right h]
    rcases le_total |(coordFun K c σ 1 t)| |(coordFun K c σ 2 t)| with h2 | h2
    · exact ⟨2, by rw [max_eq_right h2]⟩
    · exact ⟨1, by rw [max_eq_left h2]⟩
  · rw [max_eq_left h]
    rcases le_total |(coordFun K c σ 0 t)| |(coordFun K c σ 2 t)| with h2 | h2
    · exact ⟨2, by rw [max_eq_right h2]⟩
    · exact ⟨0, by rw [max_eq_left h2]⟩

theorem continuous_coordFun (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    Continuous (coordFun K c σ i) := by
  have h : Continuous fun t : ℝ => ((K.curve t).ofLp (σ i) - c.ofLp (σ i)) :=
    (((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ i)).comp K.smooth.continuous).sub
      continuous_const)
  exact h.div_const _

theorem coordFun_hasDerivAt (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3)
    (t : ℝ) : HasDerivAt (coordFun K c σ i) (coordDeriv K c σ i t) t := by
  have h1 : HasDerivAt (fun s : ℝ => (K.curve s).ofLp (σ i)) ((deriv K.curve t).ofLp (σ i)) t := by
    have h := (PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) (σ i)).hasFDerivAt.comp_hasDerivAt t
      (((K.smooth.differentiable (by simp)) t).hasDerivAt)
    rw [Function.comp_def] at h
    exact h
  have h2 := (h1.sub_const (c.ofLp (σ i))).div_const (Submission.boxSide i)
  have h3 : HasDerivAt (fun s : ℝ => coordFun K c σ i s) (coordDeriv K c σ i t) t := by
    simpa only [coordFun, coordDeriv] using h2
  exact h3

theorem continuous_coordDeriv_fun (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    Continuous (coordDeriv K c σ i) := by
  have key : Continuous (fun t : ℝ => coordDeriv K c σ i t) := by
    have h : Continuous fun t : ℝ => (deriv K.curve t).ofLp (σ i) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ i)).comp
        (K.smooth.continuous_deriv (by simp))
    simpa only [coordDeriv] using h.div_const (Submission.boxSide i)
  exact key

theorem continuousOn_coordDeriv (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    ContinuousOn (coordDeriv K c σ i) (Set.Icc 0 (2 * Real.pi)) := by
  have h : Continuous fun t : ℝ => (deriv K.curve t).ofLp (σ i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ i)).comp
      (K.smooth.continuous_deriv (by simp))
  exact (h.div_const _).continuousOn

theorem abs_coordDeriv_le_speed (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3)
    (t : ℝ) : |coordDeriv K c σ i t| ≤ speed K t := by
  have h1 : |(deriv K.curve t) (σ i)| ≤ ‖deriv K.curve t‖ := by
    have := PiLp.norm_apply_le (deriv K.curve t) (σ i)
    rwa [Real.norm_eq_abs] at this
  rw [coordDeriv, abs_div, abs_of_pos (Submission.boxSide_pos i), speed]
  have hb : (1 : ℝ) ≤ Submission.boxSide i := Submission.one_le_boxSide i
  calc |(deriv K.curve t) (σ i)| / Submission.boxSide i
      ≤ |(deriv K.curve t) (σ i)| / 1 :=
        div_le_div_of_nonneg_left (abs_nonneg _) one_pos hb
    _ = |(deriv K.curve t) (σ i)| := div_one _
    _ ≤ ‖deriv K.curve t‖ := h1

theorem continuous_boxNormCurve (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Continuous (boxNormCurve K c σ) := by
  have h : Continuous fun y : R3 => Submission.boxNorm c σ y := by
    simp only [Submission.boxNorm]
    refine ((Continuous.max ?_ ?_).max ?_) <;>
      refine Continuous.div_const (Continuous.abs ?_) _ <;>
      exact ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) _).sub continuous_const)
  exact h.comp K.smooth.continuous

/-! ## The faces of the box and the pieces of the fundamental interval -/

/-- The sign of the face: `1` for `true` and `-1` for `false`. -/
def faceSign (k : Fin 3 × Bool) : ℝ := if k.2 then 1 else -1

theorem abs_faceSign (k : Fin 3 × Bool) : |faceSign k| = 1 := by
  by_cases hb : k.2 <;> simp [faceSign, hb]

/-- The signed `σ i`-coordinate function: `coordFun` for `true`, its negative for `false`. -/
def faceFun (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (k : Fin 3 × Bool) (t : ℝ) : ℝ :=
  faceSign k * coordFun K c σ k.1 t

/-- The derivative of `faceFun`. -/
def faceDeriv (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (k : Fin 3 × Bool) (t : ℝ) : ℝ :=
  faceSign k * coordDeriv K c σ k.1 t

/-- The piece of `[0, 2π]` on which the signed `i`-th coordinate is the *first* coordinate
attaining the box norm (`i = k.1`, sign `k.2`).  These pieces are pairwise disjoint and cover
the part of the fundamental interval on which the box norm does not vanish. -/
def facePiece (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (k : Fin 3 × Bool) : Set ℝ :=
  Set.Icc 0 (2 * Real.pi) ∩ {t : ℝ | 0 < faceFun K c σ k t} ∩
    {t : ℝ | faceFun K c σ k t = boxNormCurve K c σ t} ∩
    {t : ℝ | ∀ j : Fin 3, j < k.1 → |coordFun K c σ j t| < boxNormCurve K c σ t}

theorem facePiece_subset (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (k : Fin 3 × Bool) :
    facePiece K c σ k ⊆ Set.Icc 0 (2 * Real.pi) := fun _ ht => ht.1.1.1

theorem facePiece_faceFun (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (k : Fin 3 × Bool)
    {t : ℝ} (ht : t ∈ facePiece K c σ k) : faceFun K c σ k t = boxNormCurve K c σ t :=
  ht.1.2

theorem facePiece_pos (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (k : Fin 3 × Bool)
    {t : ℝ} (ht : t ∈ facePiece K c σ k) : 0 < boxNormCurve K c σ t := by
  rw [← facePiece_faceFun K c σ k ht]; exact ht.1.1.2

theorem facePiece_le (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (k : Fin 3 × Bool)
    {t : ℝ} (ht : t ∈ facePiece K c σ k) {j : Fin 3} (hj : j < k.1) :
    |coordFun K c σ j t| < boxNormCurve K c σ t := ht.2 j hj

/-- The absolute value of the `i`-th coordinate of the curve is at most the box norm. -/
theorem abs_coordFun_le_boxNormCurve (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3)
    (t : ℝ) : |coordFun K c σ i t| ≤ boxNormCurve K c σ t := by
  rw [boxNormCurve_eq]
  fin_cases i
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_max_right _ _

theorem abs_faceFun (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (k : Fin 3 × Bool)
    (t : ℝ) : |faceFun K c σ k t| = |coordFun K c σ k.1 t| := by
  rw [faceFun, abs_mul, abs_faceSign, one_mul]

/-- On a piece, the absolute value of the coordinate of the piece equals the box norm. -/
theorem facePiece_abs (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (k : Fin 3 × Bool)
    {t : ℝ} (ht : t ∈ facePiece K c σ k) :
    |coordFun K c σ k.1 t| = boxNormCurve K c σ t := by
  rw [← abs_faceFun K c σ k t, facePiece_faceFun K c σ k ht,
    abs_of_pos (facePiece_pos K c σ k ht)]

theorem continuous_faceFun (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (k : Fin 3 × Bool) :
    Continuous (faceFun K c σ k) := by
  have key : Continuous (fun t : ℝ => faceFun K c σ k t) :=
    continuous_const.mul (continuous_coordFun K c σ k.1)
  exact key

theorem continuous_faceDeriv (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (k : Fin 3 × Bool) :
    Continuous (faceDeriv K c σ k) := by
  have key : Continuous (fun t : ℝ => faceDeriv K c σ k t) :=
    continuous_const.mul (continuous_coordDeriv_fun K c σ k.1)
  exact key

theorem measurableSet_facePiece (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3))
    (k : Fin 3 × Bool) : MeasurableSet (facePiece K c σ k) := by
  have hf : Continuous (fun t : ℝ => faceFun K c σ k t) := continuous_faceFun K c σ k
  have hg : Continuous (fun t : ℝ => boxNormCurve K c σ t) := continuous_boxNormCurve K c σ
  have hset : {t : ℝ | ∀ j : Fin 3, j < k.1 → |coordFun K c σ j t| < boxNormCurve K c σ t}
      = ⋂ j : Fin 3, {t : ℝ | j < k.1 → |coordFun K c σ j t| < boxNormCurve K c σ t} := by
    ext t; simp
  rw [facePiece, hset]
  refine (((measurableSet_Icc.inter ?_).inter ?_).inter (MeasurableSet.iInter fun j => ?_))
  · exact (isOpen_lt continuous_const hf).measurableSet
  · exact (isClosed_eq hf hg).measurableSet
  · by_cases hj : j < k.1
    · rw [show {t : ℝ | j < k.1 → |coordFun K c σ j t| < boxNormCurve K c σ t}
          = {t : ℝ | |coordFun K c σ j t| < boxNormCurve K c σ t} from by ext t; simp [hj]]
      exact (isOpen_lt ((continuous_coordFun K c σ j).abs) hg).measurableSet
    · rw [show {t : ℝ | j < k.1 → |coordFun K c σ j t| < boxNormCurve K c σ t} = Set.univ
          from by ext t; simp [hj]]
      exact MeasurableSet.univ

theorem faceFun_hasDerivAt (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (k : Fin 3 × Bool)
    (t : ℝ) : HasDerivAt (faceFun K c σ k) (faceDeriv K c σ k t) t := by
  have key : HasDerivAt (fun s : ℝ => faceFun K c σ k s) (faceDeriv K c σ k t) t := by
    have hcoord : HasDerivAt (fun s : ℝ => coordFun K c σ k.1 s) (coordDeriv K c σ k.1 t) t :=
      coordFun_hasDerivAt K c σ k.1 t
    simpa only [faceFun, faceDeriv] using hcoord.const_mul (faceSign k)
  exact key

theorem continuousOn_faceDeriv (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (k : Fin 3 × Bool) :
    ContinuousOn (faceDeriv K c σ k) (Set.Icc 0 (2 * Real.pi)) := by
  have key : ContinuousOn (fun t : ℝ => faceDeriv K c σ k t) (Set.Icc 0 (2 * Real.pi)) := by
    have hcoord : ContinuousOn (fun s : ℝ => coordDeriv K c σ k.1 s) (Set.Icc 0 (2 * Real.pi)) :=
      continuousOn_coordDeriv K c σ k.1
    simpa only [faceDeriv] using hcoord.const_mul (faceSign k)
  exact key

theorem abs_faceDeriv_le_speed (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (k : Fin 3 × Bool)
    (t : ℝ) : |faceDeriv K c σ k t| ≤ speed K t := by
  rw [faceDeriv, abs_mul, abs_faceSign, one_mul]
  exact abs_coordDeriv_le_speed K c σ k.1 t

/-- **Covering**: every parameter of the fundamental interval at which the box norm does not
vanish lies in one of the pieces. -/
theorem exists_mem_facePiece (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) {t : ℝ}
    (ht : t ∈ Set.Icc 0 (2 * Real.pi)) (hne : boxNormCurve K c σ t ≠ 0) :
    ∃ k : Fin 3 × Bool, t ∈ facePiece K c σ k := by
  have hg : 0 < boxNormCurve K c σ t :=
    lt_of_le_of_ne (boxNormCurve_nonneg K c σ t) (Ne.symm hne)
  have key : ∀ i : Fin 3, (∀ j : Fin 3, j < i → |coordFun K c σ j t| < boxNormCurve K c σ t) →
      |coordFun K c σ i t| = boxNormCurve K c σ t →
      ∃ k : Fin 3 × Bool, t ∈ facePiece K c σ k := by
    intro i hlt hi
    have hne0 : coordFun K c σ i t ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hi
      exact absurd hi.symm (ne_of_gt hg)
    rcases lt_or_gt_of_ne hne0 with hneg | hpos
    · refine ⟨(i, false), ⟨⟨ht, ?_⟩, ?_⟩, hlt⟩
      · show 0 < faceFun K c σ (i, false) t
        rw [faceFun, faceSign, if_neg (by simp)]
        linarith
      · show faceFun K c σ (i, false) t = boxNormCurve K c σ t
        rw [faceFun, faceSign, if_neg (by simp), ← hi, abs_of_neg hneg]
        ring
    · refine ⟨(i, true), ⟨⟨ht, ?_⟩, ?_⟩, hlt⟩
      · show 0 < faceFun K c σ (i, true) t
        simpa [faceFun, faceSign] using hpos
      · show faceFun K c σ (i, true) t = boxNormCurve K c σ t
        rw [faceFun, faceSign, if_pos rfl, one_mul, ← hi, abs_of_pos hpos]
  by_cases h0 : |coordFun K c σ 0 t| = boxNormCurve K c σ t
  · exact key 0 (fun j hj => absurd hj (by simp)) h0
  · have hl0 : |coordFun K c σ 0 t| < boxNormCurve K c σ t :=
      lt_of_le_of_ne (abs_coordFun_le_boxNormCurve K c σ 0 t) h0
    by_cases h1 : |coordFun K c σ 1 t| = boxNormCurve K c σ t
    · refine key 1 (fun j hj => ?_) h1
      have hj0 : j = 0 := by fin_cases j <;> simp_all
      rw [hj0]; exact hl0
    · have hl1 : |coordFun K c σ 1 t| < boxNormCurve K c σ t :=
        lt_of_le_of_ne (abs_coordFun_le_boxNormCurve K c σ 1 t) h1
      obtain ⟨i, hi⟩ := exists_coordFun_eq K c σ t
      have hi2 : i = 2 := by
        rcases (by fin_cases i <;> simp_all : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h
        · exact absurd (h ▸ hi) (ne_of_lt hl0)
        · exact absurd (h ▸ hi) (ne_of_lt hl1)
        · exact h
      refine key 2 (fun j hj => ?_) (by rw [← hi2]; exact hi)
      have hj2 : j = 0 ∨ j = 1 := by fin_cases j <;> simp_all
      rcases hj2 with h | h
      · rw [h]; exact hl0
      · rw [h]; exact hl1

/-- **Disjointness** of the pieces. -/
theorem disjoint_facePiece (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) {k l : Fin 3 × Bool}
    (hkl : k ≠ l) : Disjoint (facePiece K c σ k) (facePiece K c σ l) := by
  rw [Set.disjoint_left]
  intro t htk htl
  have hgk := facePiece_pos K c σ k htk
  by_cases hidx : k.1 = l.1
  · -- same coordinate index: the two signs are opposite, but both faces equal `g > 0`
    have hsign : k.2 ≠ l.2 := fun hb => hkl (Prod.ext hidx hb)
    have h1 : faceFun K c σ k t = boxNormCurve K c σ t := facePiece_faceFun K c σ k htk
    have h2 : faceFun K c σ l t = boxNormCurve K c σ t := facePiece_faceFun K c σ l htl
    have hsgn : faceSign k = - faceSign l := by
      by_cases hb : k.2
      · by_cases hb' : l.2
        · exact absurd (hb.trans hb'.symm) hsign
        · simp [faceSign, hb, hb']
      · by_cases hb' : l.2
        · simp [faceSign, hb, hb']
        · exact absurd ((Bool.eq_false_iff.mpr hb).trans (Bool.eq_false_iff.mpr hb').symm) hsign
    have hg := facePiece_pos K c σ k htk
    simp only [faceFun] at h1 h2
    rw [hsgn, hidx] at h1
    linarith
  · have habs_k := facePiece_abs K c σ k htk
    rcases lt_or_gt_of_ne hidx with hlt | hlt
    · have := facePiece_le K c σ l htl hlt
      rw [habs_k] at this
      exact absurd this (lt_irrefl _)
    · have := facePiece_le K c σ k htk hlt
      rw [facePiece_abs K c σ l htl] at this
      exact absurd this (lt_irrefl _)

theorem pairwise_disjoint_facePiece (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Pairwise (Function.onFun Disjoint (facePiece K c σ)) :=
  fun _ _ hkl => disjoint_facePiece K c σ hkl

/-- **The box `PBox s c σ` is open.** -/
theorem isOpen_PBox (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    IsOpen (Submission.PBox s c σ) := by
  have h : Submission.PBox s c σ
      = ⋂ i : Fin 3, {y : R3 | |y (σ i) - c (σ i)| < Submission.boxSide i * s} := by
    ext y; simp [Submission.PBox]
  rw [h]
  refine isOpen_iInter_of_finite fun i => isOpen_lt ?_ continuous_const
  exact ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ i)).sub continuous_const).abs

/-- **The level integral of the box norm.**

The integral over the levels `s ∈ (r, cc)` of the number of parameters at which the curve meets
the box sphere `{y | boxNorm c σ y = s}` is at most the arclength of the part of the curve in
the closed ball of radius `5 cc / 2` about `c` (which contains the box `PBox cc c σ`).

The box norm is not differentiable, so the level count is decomposed into the finitely many
disjoint pieces `facePiece` on which a fixed signed coordinate is the first one attaining the
box norm; on each piece the level count of the box norm is the level count of that smooth
coordinate function (`Work.BoxSweep.lintegral_levelCount_le_sum`), which gives the sharp
constant one. -/
theorem lintegral_boxNorm_levelCount_le (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3))
    {r cc : ℝ} (hr : 0 < r) (hrcc : r ≤ cc) :
    ∫⁻ s in Set.Ioo r cc,
        Work.Sweep.levelCount (boxNormCurve K c σ) (Set.Icc 0 (2 * Real.pi)) s
      ≤ Work.Sweep.arclengthIn K (Work.Sweep.paramSetIn K (Metric.closedBall c (5 / 2 * cc))) := by
  classical
  have hπ : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hcc0 : 0 ≤ cc := le_trans hr.le hrcc
  set w : ℝ → ENNReal := (Set.Ioo r cc).indicator (fun _ => (1 : ENNReal)) with hwdef
  have hwmeas : AEMeasurable w := (measurable_const.indicator measurableSet_Ioo).aemeasurable
  have hw0 : w 0 = 0 := by
    rw [hwdef, Set.indicator_of_notMem]
    simp only [Set.mem_Ioo, not_and]
    intro h
    linarith
  -- the piecewise coarea inequality for the box norm
  have hmain : ∫⁻ y, w y * Work.Sweep.levelCount (boxNormCurve K c σ) (Set.Icc 0 (2 * Real.pi)) y
      ≤ ∑ k : Fin 3 × Bool, ∫⁻ t in facePiece K c σ k,
          ENNReal.ofReal |faceDeriv K c σ k t| * w (faceFun K c σ k t) :=
    Work.BoxSweep.lintegral_levelCount_le_sum (g := boxNormCurve K c σ) (F := faceFun K c σ)
      (F' := faceDeriv K c σ) (S := facePiece K c σ) hπ
      (fun k => measurableSet_facePiece K c σ k) (fun k => facePiece_subset K c σ k)
      (pairwise_disjoint_facePiece K c σ)
      (fun k t _ => faceFun_hasDerivAt K c σ k t) (fun k => continuousOn_faceDeriv K c σ k)
      (fun k t ht => facePiece_faceFun K c σ k ht)
      (fun t ht hne => exists_mem_facePiece K c σ ht hne) hwmeas hw0
  -- the left-hand side is the integral over the levels `(r, cc)`
  have hLHS : ∫⁻ y, w y * Work.Sweep.levelCount (boxNormCurve K c σ) (Set.Icc 0 (2 * Real.pi)) y
      = ∫⁻ s in Set.Ioo r cc,
          Work.Sweep.levelCount (boxNormCurve K c σ) (Set.Icc 0 (2 * Real.pi)) s := by
    rw [hwdef]
    rw [show (fun y : ℝ => (Set.Ioo r cc).indicator (fun _ => (1 : ENNReal)) y *
          Work.Sweep.levelCount (boxNormCurve K c σ) (Set.Icc 0 (2 * Real.pi)) y)
        = (Set.Ioo r cc).indicator
            (fun y => Work.Sweep.levelCount (boxNormCurve K c σ) (Set.Icc 0 (2*Real.pi)) y)
        from ?_]
    · exact MeasureTheory.lintegral_indicator measurableSet_Ioo _
    · funext y
      by_cases hy : y ∈ Set.Ioo r cc <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
  rw [hLHS] at hmain
  -- each summand is bounded by the arclength over the part of the piece inside the box of size cc
  have hboxmeas : MeasurableSet {t : ℝ | boxNormCurve K c σ t < cc} :=
    (isOpen_lt (continuous_boxNormCurve K c σ) continuous_const).measurableSet
  have hterm : ∀ k : Fin 3 × Bool,
      ∫⁻ t in facePiece K c σ k, ENNReal.ofReal |faceDeriv K c σ k t| * w (faceFun K c σ k t)
        ≤ Work.Sweep.arclengthIn K
            (facePiece K c σ k ∩ {t : ℝ | boxNormCurve K c σ t < cc}) := by
    intro k
    have hpt : ∀ t ∈ facePiece K c σ k,
        ENNReal.ofReal |faceDeriv K c σ k t| * w (faceFun K c σ k t)
          ≤ ENNReal.ofReal (speed K t) *
              ({t : ℝ | boxNormCurve K c σ t < cc}).indicator (fun _ => (1 : ENNReal)) t := by
      intro t ht
      have h1 : ENNReal.ofReal |faceDeriv K c σ k t| ≤ ENNReal.ofReal (speed K t) :=
        ENNReal.ofReal_le_ofReal (abs_faceDeriv_le_speed K c σ k t)
      refine mul_le_mul' h1 ?_
      by_cases hb : faceFun K c σ k t ∈ Set.Ioo r cc
      · have hlt : t ∈ {t : ℝ | boxNormCurve K c σ t < cc} := by
          rw [Set.mem_setOf_eq, ← facePiece_faceFun K c σ k ht]; exact hb.2
        rw [hwdef, Set.indicator_of_mem hb]
        exact le_of_eq (Set.indicator_of_mem hlt (fun _ => (1 : ENNReal))).symm
      · rw [hwdef, Set.indicator_of_notMem hb]
        exact bot_le
    calc ∫⁻ t in facePiece K c σ k, ENNReal.ofReal |faceDeriv K c σ k t| * w (faceFun K c σ k t)
        ≤ ∫⁻ t in facePiece K c σ k, ENNReal.ofReal (speed K t) *
            ({t : ℝ | boxNormCurve K c σ t < cc}).indicator (fun _ => (1 : ENNReal)) t :=
          setLIntegral_mono_aux (measurableSet_facePiece K c σ k) hpt
      _ = ∫⁻ t in facePiece K c σ k ∩ {t : ℝ | boxNormCurve K c σ t < cc},
            ENNReal.ofReal (speed K t) :=
          setLIntegral_mul_indicator (measurableSet_facePiece K c σ k) hboxmeas _
      _ = Work.Sweep.arclengthIn K
            (facePiece K c σ k ∩ {t : ℝ | boxNormCurve K c σ t < cc}) := rfl
  -- sum up: the pieces are disjoint, and lie in the closed ball
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun k : Fin 3 × Bool => facePiece K c σ k ∩ {t : ℝ | boxNormCurve K c σ t < cc})) :=
    fun k l hkl => (pairwise_disjoint_facePiece K c σ hkl).mono Set.inter_subset_left
      Set.inter_subset_left
  have hmeas : ∀ k : Fin 3 × Bool,
      MeasurableSet (facePiece K c σ k ∩ {t : ℝ | boxNormCurve K c σ t < cc}) :=
    fun k => (measurableSet_facePiece K c σ k).inter hboxmeas
  have hsub : (⋃ k : Fin 3 × Bool, (facePiece K c σ k ∩ {t : ℝ | boxNormCurve K c σ t < cc}))
      ⊆ Work.Sweep.paramSetIn K (Metric.closedBall c (5 / 2 * cc)) := by
    intro t ht
    rw [Set.mem_iUnion] at ht
    obtain ⟨k, htk, hlt⟩ := ht
    have htIcc := facePiece_subset K c σ k htk
    have hmem : K.curve t ∈ Submission.PBox cc c σ :=
      (Submission.mem_PBox_iff cc c σ (K.curve t)).mpr hlt
    have hball := Submission.PBox_subset_ball cc hcc0 c σ hmem
    exact ⟨Metric.ball_subset_closedBall hball, htIcc⟩
  refine hmain.trans ?_
  calc ∑ k : Fin 3 × Bool, ∫⁻ t in facePiece K c σ k,
          ENNReal.ofReal |faceDeriv K c σ k t| * w (faceFun K c σ k t)
      ≤ ∑ k : Fin 3 × Bool, Work.Sweep.arclengthIn K
          (facePiece K c σ k ∩ {t : ℝ | boxNormCurve K c σ t < cc}) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = ∫⁻ t in ⋃ k : Fin 3 × Bool,
          (facePiece K c σ k ∩ {t : ℝ | boxNormCurve K c σ t < cc}), ENNReal.ofReal (speed K t) := by
        rw [MeasureTheory.lintegral_iUnion hmeas hdisj (fun t => ENNReal.ofReal (speed K t))]
        simp only [Work.Sweep.arclengthIn]
        exact (tsum_fintype _).symm
    _ ≤ Work.Sweep.arclengthIn K (Work.Sweep.paramSetIn K (Metric.closedBall c (5 / 2 * cc))) :=
        Work.Sweep.arclengthIn_mono K hsub

/-! ## The cutting plane -/

/-- The `σ 2`-coordinate of the curve, measured from the centre `c`. -/
def planeFun (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (t : ℝ) : ℝ :=
  (K.curve t).ofLp (σ 2) - c.ofLp (σ 2)

/-- The derivative of `planeFun`. -/
def planeDeriv (K : Knot) (σ : Equiv.Perm (Fin 3)) (t : ℝ) : ℝ :=
  (deriv K.curve t).ofLp (σ 2)

theorem planeFun_hasDerivAt (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (t : ℝ) :
    HasDerivAt (planeFun K c σ) (planeDeriv K σ t) t := by
  have h1 : HasDerivAt (fun s : ℝ => (K.curve s).ofLp (σ 2)) ((deriv K.curve t).ofLp (σ 2)) t := by
    have h := (PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) (σ 2)).hasFDerivAt.comp_hasDerivAt t
      (((K.smooth.differentiable (by simp)) t).hasDerivAt)
    rw [Function.comp_def] at h
    exact h
  have h2 := h1.sub_const (c.ofLp (σ 2))
  have h3 : HasDerivAt (fun s : ℝ => planeFun K c σ s) (planeDeriv K σ t) t := by
    simpa only [planeFun, planeDeriv] using h2
  exact h3

theorem continuousOn_planeDeriv (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    ContinuousOn (planeDeriv K σ) (Set.Icc 0 (2 * Real.pi)) := by
  have key : ContinuousOn (fun t : ℝ => planeDeriv K σ t) (Set.Icc 0 (2 * Real.pi)) := by
    have h : Continuous fun t : ℝ => (deriv K.curve t).ofLp (σ 2) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2)).comp
        (K.smooth.continuous_deriv (by simp))
    simpa only [planeDeriv] using h.continuousOn
  exact key

theorem abs_planeDeriv_le_speed (K : Knot) (σ : Equiv.Perm (Fin 3)) (t : ℝ) :
    |planeDeriv K σ t| ≤ speed K t := by
  have h1 : |(deriv K.curve t) (σ 2)| ≤ ‖deriv K.curve t‖ := by
    have := PiLp.norm_apply_le (deriv K.curve t) (σ 2)
    rwa [Real.norm_eq_abs] at this
  simpa only [planeDeriv, speed] using h1

/-- **The cutting plane.** For `0 < s ≤ (1+ε) r` there is a level `u` of the `σ 2`-coordinate
of the curve, with `|u| < ε r`, at which the curve meets the plane
`{y | y (σ 2) = c (σ 2) + u}` inside the box `PBox s c σ` in at most `5(1+ε)/ε · d`
parameters. -/
theorem exists_plane_level (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) {d r s : ℝ}
    (hd : 0 ≤ d) (hbound : Work.Sweep.IsDistortionBound K d) (hr : 0 < r) (hs : 0 < s)
    (hsr : s ≤ (1 + Submission.eps) * r) :
    ∃ u ∈ Set.Ioo (-(Submission.eps * r)) (Submission.eps * r),
      ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
        ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) := by
  classical
  have hπ : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  set ρ : ℝ := Submission.eps * r with hρ
  have hρpos : 0 < ρ := mul_pos Submission.eps_pos hr
  set S : Set ℝ := {t : ℝ | t ∈ Set.Icc 0 (2 * Real.pi) ∧ K.curve t ∈ Submission.PBox s c σ}
    with hS
  have hSmeas : MeasurableSet S :=
    measurableSet_Icc.inter ((isOpen_PBox s c σ).measurableSet.preimage K.smooth.continuous.measurable)
  have hSsub : S ⊆ Set.Icc (0 : ℝ) (2 * Real.pi) := fun _ ht => ht.1
  set w : ℝ → ENNReal := (Set.Ioo (-ρ) ρ).indicator (fun _ => (1 : ENNReal)) with hwdef
  have hwmeas : AEMeasurable w := (measurable_const.indicator measurableSet_Ioo).aemeasurable
  have hcoa := Work.Sweep.lintegral_mul_levelCount_le_subset (a := 0) (b := 2 * Real.pi) hπ
    hSmeas hSsub (w := w) hwmeas (fun t _ => planeFun_hasDerivAt K c σ t)
    (continuousOn_planeDeriv K c σ)
  -- the left-hand side is the integral of the level counts over `(-ρ, ρ)`
  have hLHS : ∫⁻ y, w y * Work.Sweep.levelCount (planeFun K c σ) S y
      = ∫⁻ u in Set.Ioo (-ρ) ρ, Work.Sweep.levelCount (planeFun K c σ) S u := by
    rw [hwdef]
    rw [show (fun y : ℝ => (Set.Ioo (-ρ) ρ).indicator (fun _ => (1 : ENNReal)) y *
          Work.Sweep.levelCount (planeFun K c σ) S y)
        = (Set.Ioo (-ρ) ρ).indicator (fun y => Work.Sweep.levelCount (planeFun K c σ) S y)
        from ?_]
    · exact MeasureTheory.lintegral_indicator measurableSet_Ioo _
    · funext y
      by_cases hy : y ∈ Set.Ioo (-ρ) ρ <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
  rw [hLHS] at hcoa
  -- the right-hand side is bounded by the arclength in the closed ball of radius `5 s / 2`
  have hRHS : ∫⁻ t in S, ENNReal.ofReal |planeDeriv K σ t| * w (planeFun K c σ t)
      ≤ ENNReal.ofReal (10 * d * s) := by
    have hw1 : ∀ t ∈ S, w (planeFun K c σ t) ≤ (1 : ENNReal) := by
      intro t _
      rw [hwdef]
      by_cases hb : planeFun K c σ t ∈ Set.Ioo (-ρ) ρ <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hb]
    have hpt : ∀ t ∈ S, ENNReal.ofReal |planeDeriv K σ t| * w (planeFun K c σ t)
        ≤ ENNReal.ofReal (speed K t) := by
      intro t ht
      refine (mul_le_mul' (ENNReal.ofReal_le_ofReal (abs_planeDeriv_le_speed K σ t))
        (hw1 t ht)).trans ?_
      rw [mul_one]
    have h1 : ∫⁻ t in S, ENNReal.ofReal |planeDeriv K σ t| * w (planeFun K c σ t)
        ≤ Work.Sweep.arclengthIn K S := by
      rw [Work.Sweep.arclengthIn]
      exact setLIntegral_mono_aux hSmeas hpt
    have h2 : Work.Sweep.arclengthIn K S
        ≤ Work.Sweep.arclengthIn K (Work.Sweep.paramSetIn K (Metric.closedBall c (5 / 2 * s))) := by
      refine Work.Sweep.arclengthIn_mono K fun t ht => ?_
      have hmem : K.curve t ∈ Submission.PBox s c σ := ht.2
      have hball := Submission.PBox_subset_ball s hs.le c σ hmem
      exact ⟨Metric.ball_subset_closedBall hball, ht.1⟩
    have h3 : Work.Sweep.arclengthIn K (Work.Sweep.paramSetIn K (Metric.closedBall c (5 / 2 * s)))
        ≤ ENNReal.ofReal (10 * d * s) := by
      refine (Work.Sweep.arclengthIn_closedBall_le (K := K) hd hbound c (R := 5 / 2 * s)).trans ?_
      refine ENNReal.ofReal_le_ofReal ?_
      ring_nf
      linarith
    exact h1.trans (h2.trans h3)
  -- pigeonhole
  have hle : ENNReal.ofReal (10 * d * s)
      ≤ ENNReal.ofReal ((5 * (1 + Submission.eps) / Submission.eps * d) * (ρ - (-ρ))) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have heps : Submission.eps ≠ 0 := ne_of_gt Submission.eps_pos
    have hρeq : ρ = Submission.eps * r := hρ
    rw [hρeq]
    have : (5 * (1 + Submission.eps) / Submission.eps * d) * (Submission.eps * r - -(Submission.eps * r))
        = 10 * (1 + Submission.eps) * d * r := by
      field_simp
      ring
    rw [this]
    nlinarith [hd, hsr, hr, Submission.eps_pos]
  have hInt : ∫⁻ u in Set.Ioo (-ρ) ρ, Work.Sweep.levelCount (planeFun K c σ) S u
      ≤ ENNReal.ofReal ((5 * (1 + Submission.eps) / Submission.eps * d) * (ρ - (-ρ))) :=
    hcoa.trans (hRHS.trans hle)
  have hint : ∀ y : ℝ, Work.Sweep.levelCount (planeFun K c σ) S y = ⊤ ∨
      ∃ k : ℕ, Work.Sweep.levelCount (planeFun K c σ) S y = (k : ENNReal) :=
    fun y => levelCount_eq_top_or_nat (planeFun K c σ) S y
  have hC0 : 0 ≤ 5 * (1 + Submission.eps) / Submission.eps * d := by
    have h' : 5 * (1 + Submission.eps) / Submission.eps = 75 / 2 := by norm_num [Submission.eps]
    rw [h']
    positivity
  obtain ⟨u, hu, huC⟩ := exists_le_of_lintegral_le (f := Work.Sweep.levelCount (planeFun K c σ) S)
    (a := -ρ) (b := ρ) (C := 5 * (1 + Submission.eps) / Submission.eps * d)
    (by linarith) hC0 hint hInt
  refine ⟨u, hu, ?_⟩
  have hsub : {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u}
      ⊆ S ∩ (planeFun K c σ) ⁻¹' {u} := by
    intro t ht
    refine ⟨⟨Set.Ico_subset_Icc_self ht.1, ht.2.1⟩, ?_⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, planeFun]
    linarith [ht.2.2]
  calc ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal))
      ≤ ((↑(Set.encard (S ∩ (planeFun K c σ) ⁻¹' {u})) : ENNReal)) :=
        ENat.toENNReal_le.mpr (Set.encard_le_encard hsub)
    _ = Work.Sweep.levelCount (planeFun K c σ) S u := rfl
    _ ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d) := huC

/-! ## The sweep estimate -/

theorem sweep (K : LeanEval.KnotTheory.PardonDistortion.Knot) {d : ℝ} (hd : 0 ≤ d)
    (hbound : Work.Sweep.IsDistortionBound K d) (r : ℝ) (hr : 0 < r)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) :
    ∃ s ∈ Set.Ioo r ((1 + Submission.eps) * r),
      ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
        ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) ∧
      ∃ u ∈ Set.Ioo (-(Submission.eps * r)) (Submission.eps * r),
        ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
            K.curve t ∈ Submission.PBox s c σ ∧
            (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
          ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) := by
  classical
  set cc : ℝ := (1 + Submission.eps) * r with hcc
  have hcc_pos : 0 < cc := by rw [hcc]; nlinarith [Submission.eps_pos, hr]
  have hrcc : r ≤ cc := by rw [hcc]; nlinarith [Submission.eps_pos, hr]
  have hccdiff : cc - r = Submission.eps * r := by rw [hcc]; ring
  have hrcc_lt : r < cc := by
    rw [hcc]
    nlinarith [Submission.eps_pos, hr]
  have hC0 : 0 ≤ 10 * (1 + Submission.eps) / Submission.eps * d := by
    have h' : 10 * (1 + Submission.eps) / Submission.eps = 75 := by norm_num [Submission.eps]
    rw [h']
    exact mul_nonneg (by norm_num) hd
  -- the integral bound for the box norm
  have hint : ∫⁻ s in Set.Ioo r cc,
        Work.Sweep.levelCount (boxNormCurve K c σ) (Set.Icc 0 (2 * Real.pi)) s
      ≤ ENNReal.ofReal ((10 * (1 + Submission.eps) / Submission.eps * d) * (cc - r)) := by
    refine (lintegral_boxNorm_levelCount_le K c σ hr hrcc).trans ?_
    refine (Work.Sweep.arclengthIn_closedBall_le (K := K) hd hbound c (R := 5 / 2 * cc)).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have h' : 10 * (1 + Submission.eps) / Submission.eps * d * (cc - r) = 10 * d * cc := by
      have heps : (Submission.eps : ℝ) ≠ 0 := ne_of_gt Submission.eps_pos
      have hcancel : (1 + Submission.eps) / Submission.eps * Submission.eps * r
          = (1 + Submission.eps) * r := by
        rw [div_mul_cancel₀ _ heps]
      rw [hccdiff, hcc]
      calc 10 * (1 + Submission.eps) / Submission.eps * d * (Submission.eps * r)
          = 10 * d * ((1 + Submission.eps) / Submission.eps * Submission.eps * r) := by ring
        _ = 10 * d * ((1 + Submission.eps) * r) := by rw [hcancel]
        _ = 10 * d * ((1 + Submission.eps) * r) := by ring
    rw [h', show 4 * d * (5 / 2 * cc) = 10 * d * cc by ring]
  -- the pigeonhole over the levels
  obtain ⟨s, hs, hsC⟩ := exists_le_of_lintegral_le
    (f := Work.Sweep.levelCount (boxNormCurve K c σ) (Set.Icc 0 (2 * Real.pi)))
    (a := r) (b := cc) (C := 10 * (1 + Submission.eps) / Submission.eps * d)
    hrcc_lt hC0 (fun y => levelCount_eq_top_or_nat _ _ y) hint
  -- the level count over `[0, 2π)` is at most the level count over `[0, 2π]`
  have hfirst : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal))
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d) := by
    have hle : ((↑(Set.encard ({t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          Submission.boxNorm c σ (K.curve t) = s})) : ENNReal))
        ≤ Work.Sweep.levelCount (boxNormCurve K c σ) (Set.Icc 0 (2 * Real.pi)) s := by
      rw [Work.Sweep.levelCount_eq_encard]
      refine ENat.toENNReal_le.mpr (Set.encard_le_encard ?_)
      intro t ht
      exact ⟨Set.Ico_subset_Icc_self ht.1, ht.2⟩
    exact hle.trans hsC
  refine ⟨s, hs, hfirst, ?_⟩
  exact exists_plane_level K c σ hd hbound hr (lt_trans hr hs.1) (le_of_lt hs.2)

end

end Work.BoxSweep
