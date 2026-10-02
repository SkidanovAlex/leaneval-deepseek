/-
# The arm-angle facts of the `b₂`-nest (`Work.ELAssembly.armAngle_facts`)

The six boundary angles of the level-`n` `b₂`-polygon are the affine functions of `y = 64⁻ⁿ`

* `armA1 n = 22/63 + (289/21483)·y`,   `armA2 n = 25/63 − (41/21483)·y`,
* `armB1 n = 25/63 + (1156/21483)·y`,  `armB2 n = 37/63 − (164/21483)·y`,
* `armC1 n = 37/63 + (4624/21483)·y`,  `armC2 n = 22/63 − (656/21483)·y`

(`Work.ELNest.armChain_nest`, the closed forms `.closed`).  This file collects the *angle* facts
which the assembly of the `b₂`-nest consumes:

* the level-`0` arm angles are the two root-portrait angles `α₁ = 371/1023`, `α₂ = 404/1023`;
* each of the six angles lies in its own tripod arc (`22/63, 25/63`), (`25/63, 37/63`),
  (`37/63, 22/63 + 1`) — including the two *shifts* by `1` that occur for the arm `C`
  (`armC2 n + 1`) and for the rotating arcs;
* each of the three *lower* tripod angles `22/63, 25/63, 37/63` lies in the "rotating" arc
  `(arm2 n, arm1 n + 1)` of its arm;
* the level-`(n+1)` rotating arcs are nested in the level-`n` ones (the arms shrink, the six
  angles move monotonically towards their tripod angles).

Everything is the elementary rational arithmetic of the affine families; the fractional-part
bookkeeping is `Int.fract_eq_self` for the values in `[0,1)` and one shift by `−1` for the
values in `[−1,0)`, and the nesting is proved through the characterization
`InArc x a b ↔ ∃ k : ℤ, a + k < x < b + k` of an arc of length `< 1`.
-/
import Mathlib
import Submission.Work.ELNest.Defs
import Submission.Work.ELNest.armChain_nest
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

open Work.EL (InArc arcLen)

noncomputable section

/-! ## The scale `y = 64⁻ⁿ` and the six affine angle families -/

/-- The scale `64⁻ⁿ` in which the level-`n` arm angles are affine. -/
def y64 (n : ℕ) : ℝ := ((64 : ℝ) ^ n)⁻¹

lemma y64_pos (n : ℕ) : 0 < y64 n := by rw [y64]; positivity

lemma y64_le_one (n : ℕ) : y64 n ≤ 1 := by
  rw [y64]; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

lemma y64_succ_le (n : ℕ) : y64 (n + 1) ≤ y64 n := by
  have h1 : (1:ℝ) ≤ (64:ℝ)^n := one_le_pow₀ (by norm_num)
  rw [y64, y64, pow_succ]
  exact (inv_le_inv₀ (by positivity) (by positivity)).mpr (by nlinarith)

/-- The level-`n` arm-`A` first angle as a function of `y = 64⁻ⁿ`. -/
def angA1 (y : ℝ) : ℝ := (22 : ℝ)/63 + ((289 : ℝ)/21483) * y

/-- The level-`n` arm-`A` second angle as a function of `y = 64⁻ⁿ`. -/
def angA2 (y : ℝ) : ℝ := (25 : ℝ)/63 - ((41 : ℝ)/21483) * y

/-- The level-`n` arm-`B` first angle as a function of `y = 64⁻ⁿ`. -/
def angB1 (y : ℝ) : ℝ := (25 : ℝ)/63 + ((1156 : ℝ)/21483) * y

/-- The level-`n` arm-`B` second angle as a function of `y = 64⁻ⁿ`. -/
def angB2 (y : ℝ) : ℝ := (37 : ℝ)/63 - ((164 : ℝ)/21483) * y

/-- The level-`n` arm-`C` first angle as a function of `y = 64⁻ⁿ`. -/
def angC1 (y : ℝ) : ℝ := (37 : ℝ)/63 + ((4624 : ℝ)/21483) * y

/-- The level-`n` arm-`C` second angle as a function of `y = 64⁻ⁿ`. -/
def angC2 (y : ℝ) : ℝ := (22 : ℝ)/63 - ((656 : ℝ)/21483) * y

lemma armA1_eq (n : ℕ) : Work.ELNest.armA1 n = angA1 (y64 n) := by
  rw [Work.ELNest.armA1_closed, angA1, y64]

lemma armA2_eq (n : ℕ) : Work.ELNest.armA2 n = angA2 (y64 n) := by
  rw [Work.ELNest.armA2_closed, angA2, y64]

lemma armB1_eq (n : ℕ) : Work.ELNest.armB1 n = angB1 (y64 n) := by
  rw [Work.ELNest.armB1_closed, angB1, y64]

lemma armB2_eq (n : ℕ) : Work.ELNest.armB2 n = angB2 (y64 n) := by
  rw [Work.ELNest.armB2_closed, angB2, y64]

lemma armC1_eq (n : ℕ) : Work.ELNest.armC1 n = angC1 (y64 n) := by
  rw [Work.ELNest.armC1_closed, angC1, y64]

lemma armC2_eq (n : ℕ) : Work.ELNest.armC2 n = angC2 (y64 n) := by
  rw [Work.ELNest.armC2_closed, angC2, y64]

/-! ## Monotonicity in `y` -/

lemma angA1_mono {y y' : ℝ} (h : y ≤ y') : angA1 y ≤ angA1 y' := by
  rw [angA1, angA1]; linarith

lemma angA2_anti {y y' : ℝ} (h : y ≤ y') : angA2 y' ≤ angA2 y := by
  rw [angA2, angA2]; linarith

lemma angB1_mono {y y' : ℝ} (h : y ≤ y') : angB1 y ≤ angB1 y' := by
  rw [angB1, angB1]; linarith

lemma angB2_anti {y y' : ℝ} (h : y ≤ y') : angB2 y' ≤ angB2 y := by
  rw [angB2, angB2]; linarith

lemma angC1_mono {y y' : ℝ} (h : y ≤ y') : angC1 y ≤ angC1 y' := by
  rw [angC1, angC1]; linarith

lemma angC2_anti {y y' : ℝ} (h : y ≤ y') : angC2 y' ≤ angC2 y := by
  rw [angC2, angC2]; linarith

/-! ## The three tripod arc lengths -/

lemma arcLen_A : arcLen (22/63 : ℝ) (25/63) = 1/21 := by
  rw [arcLen, show (25:ℝ)/63 - 22/63 = 1/21 by norm_num]
  exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

lemma arcLen_B : arcLen (25/63 : ℝ) (37/63) = 4/21 := by
  rw [arcLen, show (37:ℝ)/63 - 25/63 = 4/21 by norm_num]
  exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

lemma arcLen_C : arcLen (37/63 : ℝ) (22/63 + 1) = 16/21 := by
  rw [arcLen, show (22:ℝ)/63 + 1 - 37/63 = 16/21 by norm_num]
  exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

/-! ## Fractional-part bookkeeping -/

/-- `Int.fract v = v + 1` for `v ∈ [-1, 0)`. -/
lemma fract_eq_add_one_of_mem {v : ℝ} (h1 : -1 ≤ v) (h2 : v < 0) : Int.fract v = v + 1 := by
  rw [Int.fract_eq_iff]
  exact ⟨by linarith, by linarith, ⟨-1, by push_cast; ring⟩⟩

/-- The arc `(a, b)` of length `< 1` is the union of the translates `(a + k, b + k)`. -/
lemma inArc_iff_exists_int {x a b : ℝ} (h1 : 0 < b - a) (h2 : b - a < 1) :
    InArc x a b ↔ ∃ k : ℤ, a + (k : ℝ) < x ∧ x < b + (k : ℝ) := by
  have harc : arcLen a b = b - a := Int.fract_eq_self.mpr ⟨le_of_lt h1, h2⟩
  constructor
  · intro h
    rw [InArc, harc] at h
    refine ⟨⌊x - a⌋, ?_, ?_⟩
    · have := Int.floor_add_fract (x - a); linarith [h.1]
    · have := Int.floor_add_fract (x - a); linarith [h.2]
  · rintro ⟨k, hk1, hk2⟩
    have hf : Int.fract (x - a) = x - a - (k : ℝ) := by
      rw [Int.fract_eq_iff]
      exact ⟨by linarith, by linarith, ⟨k, by ring⟩⟩
    rw [InArc, harc, hf]
    constructor <;> linarith

/-- **Nesting of arcs of length `< 1`**: if `a₀ ≤ a₁` and `b₁ ≤ b₀` then the arc `(a₁, b₁)` is
contained in the arc `(a₀, b₀)`. -/
lemma inArc_mono {x a₀ b₀ a₁ b₁ : ℝ} (ha : a₀ ≤ a₁) (hb : b₁ ≤ b₀)
    (h0 : 0 < b₀ - a₀) (h1 : b₀ - a₀ < 1) (h2 : 0 < b₁ - a₁) (h3 : b₁ - a₁ < 1)
    (h : InArc x a₁ b₁) : InArc x a₀ b₀ := by
  obtain ⟨k, hk1, hk2⟩ := (inArc_iff_exists_int h2 h3).mp h
  exact (inArc_iff_exists_int h0 h1).mpr ⟨k, by linarith, by linarith⟩

/-! ## The six angles lie in their own tripod arcs -/

lemma inArc_angA1 {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    InArc (angA1 y) (22/63) (25/63) := by
  have h29 : ((289:ℝ)/21483) * y ≤ (289:ℝ)/21483 := mul_le_of_le_one_right (by norm_num) hy1
  have hf : Int.fract (angA1 y - 22/63) = ((289:ℝ)/21483) * y := by
    rw [angA1,
      show (22:ℝ)/63 + (289:ℝ)/21483 * y - 22/63 = (289:ℝ)/21483 * y by ring]
    exact Int.fract_eq_self.mpr ⟨by positivity, by linarith⟩
  rw [InArc, hf, arcLen_A]
  exact ⟨by positivity, by linarith⟩

lemma inArc_angA2 {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    InArc (angA2 y) (22/63) (25/63) := by
  have h41 : ((41:ℝ)/21483) * y ≤ (41:ℝ)/21483 := mul_le_of_le_one_right (by norm_num) hy1
  have hf : Int.fract (angA2 y - 22/63) = (1:ℝ)/21 - ((41:ℝ)/21483) * y := by
    rw [angA2,
      show (25:ℝ)/63 - (41:ℝ)/21483 * y - 22/63 = (1:ℝ)/21 - (41:ℝ)/21483 * y by ring]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [InArc, hf, arcLen_A]
  exact ⟨by linarith, by linarith⟩

lemma inArc_angB1 {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    InArc (angB1 y) (25/63) (37/63) := by
  have h : ((1156:ℝ)/21483) * y ≤ (1156:ℝ)/21483 := mul_le_of_le_one_right (by norm_num) hy1
  have hf : Int.fract (angB1 y - 25/63) = ((1156:ℝ)/21483) * y := by
    rw [angB1,
      show (25:ℝ)/63 + (1156:ℝ)/21483 * y - 25/63 = (1156:ℝ)/21483 * y by ring]
    exact Int.fract_eq_self.mpr ⟨by positivity, by linarith⟩
  rw [InArc, hf, arcLen_B]
  exact ⟨by positivity, by linarith⟩

lemma inArc_angB2 {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    InArc (angB2 y) (25/63) (37/63) := by
  have h : ((164:ℝ)/21483) * y ≤ (164:ℝ)/21483 := mul_le_of_le_one_right (by norm_num) hy1
  have hf : Int.fract (angB2 y - 25/63) = (4:ℝ)/21 - ((164:ℝ)/21483) * y := by
    rw [angB2,
      show (37:ℝ)/63 - (164:ℝ)/21483 * y - 25/63 = (4:ℝ)/21 - (164:ℝ)/21483 * y by ring]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [InArc, hf, arcLen_B]
  exact ⟨by linarith, by linarith⟩

lemma inArc_angC1 {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    InArc (angC1 y) (37/63) (22/63 + 1) := by
  have h : ((4624:ℝ)/21483) * y ≤ (4624:ℝ)/21483 := mul_le_of_le_one_right (by norm_num) hy1
  have hf : Int.fract (angC1 y - 37/63) = ((4624:ℝ)/21483) * y := by
    rw [angC1,
      show (37:ℝ)/63 + (4624:ℝ)/21483 * y - 37/63 = (4624:ℝ)/21483 * y by ring]
    exact Int.fract_eq_self.mpr ⟨by positivity, by linarith⟩
  rw [InArc, hf, arcLen_C]
  exact ⟨by positivity, by linarith⟩

lemma inArc_angC2 {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    InArc (angC2 y + 1) (37/63) (22/63 + 1) := by
  have h : ((656:ℝ)/21483) * y ≤ (656:ℝ)/21483 := mul_le_of_le_one_right (by norm_num) hy1
  have hf : Int.fract (angC2 y + 1 - 37/63) = (16:ℝ)/21 - ((656:ℝ)/21483) * y := by
    rw [angC2,
      show (22:ℝ)/63 - (656:ℝ)/21483 * y + 1 - 37/63
        = (16:ℝ)/21 - (656:ℝ)/21483 * y by ring]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [InArc, hf, arcLen_C]
  exact ⟨by linarith, by linarith⟩

/-! ## The three lower tripod angles lie in the rotating arcs -/

lemma inArc_angA_lo {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    InArc (22/63) (angA2 y) (angA1 y + 1) := by
  have h41 : ((41:ℝ)/21483) * y ≤ (41:ℝ)/21483 := mul_le_of_le_one_right (by norm_num) hy1
  have h330 : ((330:ℝ)/21483) * y ≤ (330:ℝ)/21483 := mul_le_of_le_one_right (by norm_num) hy1
  have hf : Int.fract ((22:ℝ)/63 - angA2 y) = (20:ℝ)/21 + ((41:ℝ)/21483) * y := by
    rw [angA2,
      show (22:ℝ)/63 - ((25:ℝ)/63 - (41:ℝ)/21483 * y)
        = -((1:ℝ)/21) + (41:ℝ)/21483 * y by ring]
    rw [fract_eq_add_one_of_mem (by linarith) (by linarith)]
    ring
  have hl : arcLen (angA2 y) (angA1 y + 1) = (20:ℝ)/21 + ((330:ℝ)/21483) * y := by
    rw [arcLen, angA1, angA2,
      show ((22:ℝ)/63 + (289:ℝ)/21483 * y + 1) - ((25:ℝ)/63 - (41:ℝ)/21483 * y)
        = (20:ℝ)/21 + (330:ℝ)/21483 * y by ring]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [InArc, hf, hl]
  exact ⟨by linarith, by linarith⟩

lemma inArc_angB_lo {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    InArc (25/63) (angB2 y) (angB1 y + 1) := by
  have h164 : ((164:ℝ)/21483) * y ≤ (164:ℝ)/21483 := mul_le_of_le_one_right (by norm_num) hy1
  have h1320 : ((1320:ℝ)/21483) * y ≤ (1320:ℝ)/21483 :=
    mul_le_of_le_one_right (by norm_num) hy1
  have hf : Int.fract ((25:ℝ)/63 - angB2 y) = (17:ℝ)/21 + ((164:ℝ)/21483) * y := by
    rw [angB2,
      show (25:ℝ)/63 - ((37:ℝ)/63 - (164:ℝ)/21483 * y)
        = -((4:ℝ)/21) + (164:ℝ)/21483 * y by ring]
    rw [fract_eq_add_one_of_mem (by linarith) (by linarith)]
    ring
  have hl : arcLen (angB2 y) (angB1 y + 1) = (17:ℝ)/21 + ((1320:ℝ)/21483) * y := by
    rw [arcLen, angB1, angB2,
      show ((25:ℝ)/63 + (1156:ℝ)/21483 * y + 1) - ((37:ℝ)/63 - (164:ℝ)/21483 * y)
        = (17:ℝ)/21 + (1320:ℝ)/21483 * y by ring]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [InArc, hf, hl]
  exact ⟨by linarith, by linarith⟩

lemma inArc_angC_lo {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    InArc (37/63) (angC2 y + 1) (angC1 y + 1) := by
  have h656 : ((656:ℝ)/21483) * y ≤ (656:ℝ)/21483 := mul_le_of_le_one_right (by norm_num) hy1
  have h5280 : ((5280:ℝ)/21483) * y ≤ (5280:ℝ)/21483 :=
    mul_le_of_le_one_right (by norm_num) hy1
  have hf : Int.fract ((37:ℝ)/63 - (angC2 y + 1)) = (5:ℝ)/21 + ((656:ℝ)/21483) * y := by
    rw [angC2,
      show (37:ℝ)/63 - ((22:ℝ)/63 - (656:ℝ)/21483 * y + 1)
        = -((16:ℝ)/21) + (656:ℝ)/21483 * y by ring]
    rw [fract_eq_add_one_of_mem (by linarith) (by linarith)]
    ring
  have hl : arcLen (angC2 y + 1) (angC1 y + 1) = (5:ℝ)/21 + ((5280:ℝ)/21483) * y := by
    rw [arcLen, angC1, angC2,
      show ((37:ℝ)/63 + (4624:ℝ)/21483 * y + 1) - ((22:ℝ)/63 - (656:ℝ)/21483 * y + 1)
        = (5:ℝ)/21 + (5280:ℝ)/21483 * y by ring]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [InArc, hf, hl]
  exact ⟨by linarith, by linarith⟩

/-! ## The three rotating arcs have length `< 1` -/

lemma angA_gap {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    0 < angA1 y + 1 - angA2 y ∧ angA1 y + 1 - angA2 y < 1 := by
  rw [angA1, angA2]; constructor <;> linarith

lemma angB_gap {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    0 < angB1 y + 1 - angB2 y ∧ angB1 y + 1 - angB2 y < 1 := by
  rw [angB1, angB2]; constructor <;> linarith

lemma angC_gap {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    0 < angC1 y + 1 - (angC2 y + 1) ∧ angC1 y + 1 - (angC2 y + 1) < 1 := by
  rw [angC1, angC2]; constructor <;> linarith

/-! ## The statement -/

theorem armAngle_facts :
    (Work.ELNest.armA1 0 = Work.EL.alpha1) ∧
    (Work.ELNest.armA2 0 = Work.EL.alpha2) ∧
    (∀ n : ℕ, Work.EL.InArc (Work.ELNest.armA1 n) (22 / 63) (25 / 63)) ∧
    (∀ n : ℕ, Work.EL.InArc (Work.ELNest.armA2 n) (22 / 63) (25 / 63)) ∧
    (∀ n : ℕ, Work.EL.InArc (Work.ELNest.armB1 n) (25 / 63) (37 / 63)) ∧
    (∀ n : ℕ, Work.EL.InArc (Work.ELNest.armB2 n) (25 / 63) (37 / 63)) ∧
    (∀ n : ℕ, Work.EL.InArc (Work.ELNest.armC1 n) (37 / 63) (22 / 63 + 1)) ∧
    (∀ n : ℕ, Work.EL.InArc (Work.ELNest.armC2 n + 1) (37 / 63) (22 / 63 + 1)) ∧
    (∀ n : ℕ, Work.EL.InArc (22 / 63) (Work.ELNest.armA2 n) (Work.ELNest.armA1 n + 1)) ∧
    (∀ n : ℕ, Work.EL.InArc (25 / 63) (Work.ELNest.armB2 n) (Work.ELNest.armB1 n + 1)) ∧
    (∀ n : ℕ, Work.EL.InArc (37 / 63) (Work.ELNest.armC2 n + 1) (Work.ELNest.armC1 n + 1)) ∧
    (∀ (n : ℕ) (θ : ℝ), Work.EL.InArc θ (Work.ELNest.armA2 (n + 1)) (Work.ELNest.armA1 (n + 1) + 1) →
      Work.EL.InArc θ (Work.ELNest.armA2 n) (Work.ELNest.armA1 n + 1)) ∧
    (∀ (n : ℕ) (θ : ℝ), Work.EL.InArc θ (Work.ELNest.armB2 (n + 1)) (Work.ELNest.armB1 (n + 1) + 1) →
      Work.EL.InArc θ (Work.ELNest.armB2 n) (Work.ELNest.armB1 n + 1)) ∧
    (∀ (n : ℕ) (θ : ℝ), Work.EL.InArc θ (Work.ELNest.armC2 (n + 1) + 1) (Work.ELNest.armC1 (n + 1) + 1) →
      Work.EL.InArc θ (Work.ELNest.armC2 n + 1) (Work.ELNest.armC1 n + 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [armA1_eq, Work.EL.alpha1]; norm_num [angA1, y64]
  · rw [armA2_eq, Work.EL.alpha2]; norm_num [angA2, y64]
  · intro n; rw [armA1_eq]; exact inArc_angA1 (y64_pos n) (y64_le_one n)
  · intro n; rw [armA2_eq]; exact inArc_angA2 (y64_pos n) (y64_le_one n)
  · intro n; rw [armB1_eq]; exact inArc_angB1 (y64_pos n) (y64_le_one n)
  · intro n; rw [armB2_eq]; exact inArc_angB2 (y64_pos n) (y64_le_one n)
  · intro n; rw [armC1_eq]; exact inArc_angC1 (y64_pos n) (y64_le_one n)
  · intro n; rw [armC2_eq]; exact inArc_angC2 (y64_pos n) (y64_le_one n)
  · intro n; rw [armA1_eq, armA2_eq]
    exact inArc_angA_lo (y64_pos n) (y64_le_one n)
  · intro n; rw [armB1_eq, armB2_eq]
    exact inArc_angB_lo (y64_pos n) (y64_le_one n)
  · intro n; rw [armC1_eq, armC2_eq]
    exact inArc_angC_lo (y64_pos n) (y64_le_one n)
  · intro n θ h
    rw [armA1_eq, armA2_eq] at h ⊢
    exact inArc_mono (angA2_anti (y64_succ_le n)) (by linarith [angA1_mono (y64_succ_le n)])
      (angA_gap (y64_pos n) (y64_le_one n)).1 (angA_gap (y64_pos n) (y64_le_one n)).2
      (angA_gap (y64_pos (n + 1)) (y64_le_one (n + 1))).1
      (angA_gap (y64_pos (n + 1)) (y64_le_one (n + 1))).2 h
  · intro n θ h
    rw [armB1_eq, armB2_eq] at h ⊢
    exact inArc_mono (angB2_anti (y64_succ_le n)) (by linarith [angB1_mono (y64_succ_le n)])
      (angB_gap (y64_pos n) (y64_le_one n)).1 (angB_gap (y64_pos n) (y64_le_one n)).2
      (angB_gap (y64_pos (n + 1)) (y64_le_one (n + 1))).1
      (angB_gap (y64_pos (n + 1)) (y64_le_one (n + 1))).2 h
  · intro n θ h
    rw [armC1_eq, armC2_eq] at h ⊢
    exact inArc_mono (by linarith [angC2_anti (y64_succ_le n)])
      (by linarith [angC1_mono (y64_succ_le n)])
      (angC_gap (y64_pos n) (y64_le_one n)).1 (angC_gap (y64_pos n) (y64_le_one n)).2
      (angC_gap (y64_pos (n + 1)) (y64_le_one (n + 1))).1
      (angC_gap (y64_pos (n + 1)) (y64_le_one (n + 1))).2 h

end

end Work.ELAssembly
