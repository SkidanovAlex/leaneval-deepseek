/-
# The regions `Wm1` and `O` of the socket construction

`Wm1 = {τ : τ+1 ∈ U0 ∧ τ+2 ∈ W1 ∧ |Re τ + 1| < thin(Im τ)}` is the strip to the left of
`Re τ = -1` on which the layer `F₂` is *defined* by the first recurrence; `O = U0 ∪ W1 ∪ Wm1`
is the open set of the socket.  This file records the elementary geometry of these sets.
-/
import Mathlib
import Submission.Work.CKFinal.Socket.WinDefs

noncomputable section

open UpperHalfPlane
open scoped Topology Manifold

namespace Work.CKFinal
namespace Socket

/-- The region to the left of `Re τ = -1` on which `F₂` is defined by the first recurrence. -/
noncomputable def Wm1 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) : Set ℍ :=
  {τ : ℍ | (1 : ℝ) +ᵥ τ ∈ U0 ∧ (2 : ℝ) +ᵥ τ ∈ W1 ℓ d hd ∧ |τ.re + 1| < thin τ.im}

/-- The open set `O` of the socket. -/
noncomputable def O (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) : Set ℍ :=
  U0 ∪ W1 ℓ d hd ∪ Wm1 ℓ d hd

lemma mem_Wm1 {ℓ : Work.Kernels.LogLambdaData} {d : ℕ} {hd : d = 8 ∨ d = 24} {τ : ℍ} :
    τ ∈ Wm1 ℓ d hd ↔ (1 : ℝ) +ᵥ τ ∈ U0 ∧ (2 : ℝ) +ᵥ τ ∈ W1 ℓ d hd ∧ |τ.re + 1| < thin τ.im :=
  Iff.rfl

lemma thin_le_quarter (y : ℝ) : thin y ≤ 1 / 4 := by
  rw [thin]
  exact div_le_div_of_nonneg_right (min_le_right (y ^ 2) 1) (by norm_num)

lemma thin_nonneg (y : ℝ) : 0 ≤ thin y := by
  rw [thin]
  exact div_nonneg (le_min (sq_nonneg y) zero_le_one) (by norm_num)

lemma thin_pos {y : ℝ} (hy : 0 < y) : 0 < thin y := by
  rw [thin]
  exact div_pos (lt_min (by positivity) one_pos) (by norm_num)

lemma continuous_thin_im :
    Continuous (fun τ : ℍ => thin τ.im) := by
  have h : Continuous fun τ : ℍ => τ.im := UpperHalfPlane.continuous_im
  exact ((h.pow 2).min continuous_const).div_const 4

/-- Translation by a real number is continuous on `ℍ`. -/
lemma continuous_vadd_real (x : ℝ) : Continuous (fun τ : ℍ => x +ᵥ τ) := by
  refine UpperHalfPlane.isOpenEmbedding_coe.isInducing.continuous_iff.mpr ?_
  have h : Continuous fun τ : ℍ => (x : ℂ) + (τ : ℂ) := by fun_prop
  simpa only [Function.comp_def, UpperHalfPlane.coe_vadd] using h

lemma vadd_one_re (τ : ℍ) : ((1 : ℝ) +ᵥ τ).re = τ.re + 1 := by
  rw [← UpperHalfPlane.coe_re, UpperHalfPlane.coe_vadd]
  simp only [Complex.add_re, Complex.ofReal_re, UpperHalfPlane.coe_re]
  ring

lemma vadd_two_re (τ : ℍ) : ((2 : ℝ) +ᵥ τ).re = τ.re + 2 := by
  rw [← UpperHalfPlane.coe_re, UpperHalfPlane.coe_vadd]
  simp only [Complex.add_re, Complex.ofReal_re, UpperHalfPlane.coe_re]
  ring

lemma isOpen_W1 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    IsOpen (W1 ℓ d hd) :=
  isOpen_iUnion fun s => isOpen_iUnion fun hs => isOpen_winBall ℓ d hd s hs

lemma isOpen_Wm1 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    IsOpen (Wm1 ℓ d hd) := by
  have h1 : IsOpen {τ : ℍ | (1 : ℝ) +ᵥ τ ∈ U0} :=
    isOpen_U0.preimage (continuous_vadd_real 1)
  have h2 : IsOpen {τ : ℍ | (2 : ℝ) +ᵥ τ ∈ W1 ℓ d hd} :=
    (isOpen_W1 ℓ d hd).preimage (continuous_vadd_real 2)
  have h3 : IsOpen {τ : ℍ | |τ.re + 1| < thin τ.im} := by
    have hc : Continuous fun τ : ℍ => |τ.re + 1| - thin τ.im :=
      (continuous_abs.comp (UpperHalfPlane.continuous_re.add continuous_const)).sub
        continuous_thin_im
    have hset : {τ : ℍ | |τ.re + 1| < thin τ.im} = {τ : ℍ | |τ.re + 1| - thin τ.im < 0} := by
      ext τ; simp [sub_neg]
    rw [hset]
    exact isOpen_lt hc continuous_const
  have hset : Wm1 ℓ d hd = {τ : ℍ | (1 : ℝ) +ᵥ τ ∈ U0} ∩ {τ : ℍ | (2 : ℝ) +ᵥ τ ∈ W1 ℓ d hd} ∩
      {τ : ℍ | |τ.re + 1| < thin τ.im} := by
    ext τ; simp [Wm1, and_assoc]
  rw [hset]
  exact (h1.inter h2).inter h3

lemma isOpen_O (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    IsOpen (O ℓ d hd) :=
  (isOpen_U0.union (isOpen_W1 ℓ d hd)).union (isOpen_Wm1 ℓ d hd)

/-- `Wm1` lies in the strip `Re τ ∈ (-5/4,-3/4)`. -/
lemma Wm1_re_bounds {ℓ : Work.Kernels.LogLambdaData} {d : ℕ} {hd : d = 8 ∨ d = 24} {τ : ℍ}
    (h : τ ∈ Wm1 ℓ d hd) : -5 / 4 < τ.re ∧ τ.re < -3 / 4 := by
  have hlt : |τ.re + 1| < 1 / 4 := lt_of_lt_of_le h.2.2 (thin_le_quarter τ.im)
  have := abs_lt.mp hlt
  constructor <;> linarith [this.1, this.2]

/-- `W1` lies in the strip `Re τ ∈ (3/4,5/4)`. -/
lemma W1_re_bounds {ℓ : Work.Kernels.LogLambdaData} {d : ℕ} {hd : d = 8 ∨ d = 24} {τ : ℍ}
    (h : τ ∈ W1 ℓ d hd) : 3 / 4 < τ.re ∧ τ.re < 5 / 4 := by
  obtain ⟨s, hs, hb⟩ := mem_W1.mp h
  have hlt : |τ.re - 1| < 1 / 4 := lt_of_lt_of_le (winBall_mem_re ℓ d hd hb) (thin_le_quarter τ.im)
  have := abs_lt.mp hlt
  constructor <;> linarith [this.1, this.2]

/-- `Wm1` and `W1` are disjoint. -/
lemma Wm1_disjoint_W1 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    Disjoint (Wm1 ℓ d hd) (W1 ℓ d hd) := by
  rw [Set.disjoint_left]
  intro τ h1 h2
  have a := (Wm1_re_bounds h1).2
  have b := (W1_re_bounds h2).1
  linarith

/-- A point of `Wm1` is not shifted into `Wm1` by `+1`. -/
lemma vadd_one_not_mem_Wm1 {ℓ : Work.Kernels.LogLambdaData} {d : ℕ} {hd : d = 8 ∨ d = 24}
    {τ : ℍ} (h : τ ∈ Wm1 ℓ d hd) : (1 : ℝ) +ᵥ τ ∉ Wm1 ℓ d hd := by
  intro h'
  have a := (Wm1_re_bounds h).1
  have b := (Wm1_re_bounds h').2
  rw [vadd_one_re] at b
  linarith

/-- A point of `Wm1` is not shifted into `Wm1` by `+2`. -/
lemma vadd_two_not_mem_Wm1 {ℓ : Work.Kernels.LogLambdaData} {d : ℕ} {hd : d = 8 ∨ d = 24}
    {τ : ℍ} (h : τ ∈ Wm1 ℓ d hd) : (2 : ℝ) +ᵥ τ ∉ Wm1 ℓ d hd := by
  intro h'
  have a := (Wm1_re_bounds h).1
  have b := (Wm1_re_bounds h').2
  rw [vadd_two_re] at b
  linarith

/-- A point of `Wm1` shifted by `+1` is not in `W1`. -/
lemma vadd_one_not_mem_W1 {ℓ : Work.Kernels.LogLambdaData} {d : ℕ} {hd : d = 8 ∨ d = 24}
    {τ : ℍ} (h : τ ∈ Wm1 ℓ d hd) : (1 : ℝ) +ᵥ τ ∉ W1 ℓ d hd := by
  intro h'
  have a := (Wm1_re_bounds h).2
  have b := (W1_re_bounds h').1
  rw [vadd_one_re] at b
  linarith

end Socket
end Work.CKFinal
