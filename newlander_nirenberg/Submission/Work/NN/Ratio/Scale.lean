/-
# The scaling data for the ratio-parameterised `∂̄`-Poincaré operator

Given `0 < ρ'' < ρ` (componentwise) we choose a small `η > 0` so that
`ρ'' j < ρ j * (1 - η)`, and the thresholds

  `a = 1 - 3η/4`,  `b = 1 - η/2`,  `T = 1 - η/4`,  `e = 1 - η`

of the flexible telescoping construction `Work.NN.Ratio.Geom`, together with the diagonal
scaling `S j = ρ j (1 - η/8) / T` and the maps

  `Φ y = (j ↦ S j * y j)`,  `Ψ z = (j ↦ (S j)⁻¹ * z j)`.

The point of the choice is that `e * S j ≥ ρ j (1 - η) > ρ'' j` (the equation is solved on a
polydisc strictly containing `ρ''`) while `T * S j = ρ j (1 - η/8) < ρ j` (the construction reads
its data inside the polydisc where the datum is closed).
-/
import Mathlib
import Submission.Work.NN.Ratio.Setup
import Submission.Work.CR.Flat.Holder.holderNorm_zero_comp_le
import Submission.Work.CR.Flat.Holder.holderNorm_smul
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comp_diagAffine
import Submission.Work.CR.Flat.Polydisc.dbarCoord_mul

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set MeasureTheory
open Work.CR.Flat

namespace Work.NN.Ratio

variable {n : ℕ}

/-- Monotonicity of the coercion of natural numbers into the smoothness scale. -/
lemma natCast_le {m m' : ℕ} (h : m ≤ m') : (m : ℕ∞ω) ≤ (m' : ℕ∞ω) := by
  exact_mod_cast h

/-- Membership in a polydisc of radius zero with a constant multiradius, in coordinates. -/
lemma mem_polydisc_const {n : ℕ} {c : ℝ} {z : Fin n → ℂ} :
    z ∈ polydisc (0 : Fin n → ℂ) (fun _ => c) ↔ ∀ j, ‖z j‖ < c := by
  simp [polydisc]

/-! ## The thresholds -/

/-- The tracking threshold of the construction. -/
def thrT (η : ℝ) : ℝ := 1 - η / 4

/-- The cutoff threshold of the construction. -/
def thrb (η : ℝ) : ℝ := 1 - η / 2

/-- The inner cutoff threshold of the construction. -/
def thra (η : ℝ) : ℝ := 1 - 3 * η / 4

/-- The equation threshold of the construction. -/
def thre (η : ℝ) : ℝ := 1 - η

@[simp] lemma thrT_def (η : ℝ) : thrT η = 1 - η / 4 := rfl

lemma thra_pos {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) : 0 < thra η := by
  rw [thra]; linarith

lemma thrb_pos {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) : 0 < thrb η := by
  rw [thrb]; linarith

lemma thrT_pos {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) : 0 < thrT η := by
  rw [thrT]; linarith

lemma thre_pos {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) : 0 < thre η := by
  rw [thre]; linarith

lemma thre_nonneg {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) : 0 ≤ thre η :=
  le_of_lt (thre_pos h0 h1)

lemma thra_lt_thrb {η : ℝ} (h0 : 0 < η) : thra η < thrb η := by rw [thra, thrb]; linarith

lemma thrb_lt_thrT {η : ℝ} (h0 : 0 < η) : thrb η < thrT η := by rw [thrb, thrT]; linarith

lemma thre_lt_thra {η : ℝ} (h0 : 0 < η) : thre η < thra η := by rw [thre, thra]; linarith

lemma thre_lt_thrT {η : ℝ} (h0 : 0 < η) : thre η < thrT η := by rw [thre, thrT]; linarith

lemma thrT_le_one {η : ℝ} (h0 : 0 < η) : thrT η ≤ 1 := by rw [thrT]; linarith

lemma one_sub_eighth_pos {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) : 0 < 1 - η / 8 := by
  linarith

/-! ## The scaling -/

/-- The diagonal scaling of the construction. -/
def scale (η : ℝ) (ρ : Fin n → ℝ) : Fin n → ℝ := fun j => ρ j * (1 - η / 8) / thrT η

lemma scale_pos {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) (j : Fin n) : 0 < scale η ρ j := by
  rw [scale]
  exact div_pos (mul_pos (hρ j) (one_sub_eighth_pos h0 h1)) (thrT_pos h0 h1)

lemma thrT_mul_scale {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) (ρ : Fin n → ℝ) (j : Fin n) :
    thrT η * scale η ρ j = ρ j * (1 - η / 8) := by
  rw [scale, ← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt (thrT_pos h0 h1))]

lemma thrT_mul_scale_lt {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) (j : Fin n) : thrT η * scale η ρ j < ρ j := by
  rw [thrT_mul_scale h0 h1]
  nlinarith [hρ j, h0]

lemma thre_mul_scale_ge {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) (j : Fin n) : ρ j * (1 - η) ≤ thre η * scale η ρ j := by
  rw [thre, scale]
  have hd : 0 < thrT η := thrT_pos h0 h1
  have hge : thrT η ≤ 1 - η / 8 := by rw [thrT]; linarith
  have hnn : 0 ≤ ρ j * (1 - η) := by
    have : 0 ≤ 1 - η := by linarith
    exact mul_nonneg (le_of_lt (hρ j)) this
  rw [show (1 - η) * (ρ j * (1 - η / 8) / thrT η)
      = ρ j * (1 - η) * (1 - η / 8) / thrT η by ring]
  rw [le_div_iff₀ hd]
  exact mul_le_mul_of_nonneg_left hge hnn

lemma rho''_lt_thre_mul_scale {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ ρ'' : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hlt : ∀ j, ρ'' j < ρ j * (1 - η)) (j : Fin n) :
    ρ'' j < thre η * scale η ρ j :=
  lt_of_lt_of_le (hlt j) (thre_mul_scale_ge h0 h1 hρ j)

/-- The choice of the small parameter. -/
lemma exists_eta {n : ℕ} (hn : 0 < n) {ρ ρ'' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hlt : ∀ j, ρ'' j < ρ j) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧ ∀ j, ρ'' j < ρ j * (1 - η) := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨j₀⟩ := (inferInstance : Nonempty (Fin n))
  set ε : Fin n → ℝ := fun j => (ρ j - ρ'' j) / (2 * ρ j) with hε
  have hεpos : ∀ j, 0 < ε j := fun j =>
    div_pos (sub_pos.mpr (hlt j)) (by linarith [hρ j])
  have hne : (Finset.univ.image ε).Nonempty :=
    ⟨ε j₀, Finset.mem_image.mpr ⟨j₀, Finset.mem_univ j₀, rfl⟩⟩
  set m : ℝ := (Finset.univ.image ε).min' hne with hm
  have hmpos : 0 < m := by
    obtain ⟨j, _, hji⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne)
    rw [hm, ← hji]
    exact hεpos j
  have hηpos : 0 < min (1 / 2) m := lt_min (by norm_num) hmpos
  refine ⟨min (1 / 2) m, hηpos, min_le_left _ _, fun j => ?_⟩
  have hle : m ≤ ε j := by
    rw [hm]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  have hlt' : min (1 / 2) m ≤ ε j := le_trans (min_le_right _ _) hle
  rw [hε] at hlt'
  have h2ρ : 0 < 2 * ρ j := by linarith [hρ j]
  rw [le_div_iff₀ h2ρ] at hlt'
  have h3 : ρ'' j ≤ ρ j - 2 * ρ j * min (1 / 2) m := by linarith
  have h4 : 0 < ρ j * min (1 / 2) m := mul_pos (hρ j) hηpos
  nlinarith [hρ j, h3, h4]

/-! ## The `Geom` data -/

private noncomputable def chiC (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) : ℝ :=
  (dbarC_rCut_bounded ha hab).choose
private lemma chiC_spec {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    0 ≤ chiC a b ha hab ∧ ∀ ζ : ℂ, ‖dbarC (rCut a b) ζ‖ ≤ chiC a b ha hab :=
  (dbarC_rCut_bounded ha hab).choose_spec

private noncomputable def chiC' (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) : ℝ :=
  (dbarC_rCut_lipschitz ha hab).choose
private lemma chiC'_spec {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    0 ≤ chiC' a b ha hab ∧
      ∀ ζ ζ' : ℂ, ‖dbarC (rCut a b) ζ - dbarC (rCut a b) ζ'‖ ≤ chiC' a b ha hab * ‖ζ - ζ'‖ :=
  (dbarC_rCut_lipschitz ha hab).choose_spec

private noncomputable def chiL (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) : ℝ :=
  (rCut_lipschitz ha hab).choose
private lemma chiL_spec {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    0 ≤ chiL a b ha hab ∧ ∀ ζ ζ' : ℂ, ‖rCut a b ζ - rCut a b ζ'‖ ≤ chiL a b ha hab * ‖ζ - ζ'‖ :=
  (rCut_lipschitz ha hab).choose_spec

/-- The geometric data of the flexible telescoping construction at the thresholds `a < b < T`
and equation radius `e` read off from `η`. -/
noncomputable def geomOf {n : ℕ} (η : ℝ) (h0 : 0 < η) (h1 : η ≤ 1 / 2) : Geom n :=
  Geom.mk (thra η) (thrb η) (thrT η) (2 * thrb η) (thre η)
    (thra_pos h0 h1) (thra_lt_thrb h0) (thrb_lt_thrT h0) (thre_lt_thra h0)
    le_rfl
    (by linarith [thrb_pos h0 h1])
    (rCut (thra η) (thrb η))
    (contDiff_rCut _ _)
    (fun ζ h => rCut_eq_one_of_norm_le (le_of_lt (thra_pos h0 h1)) (thra_lt_thrb h0) h)
    (fun ζ h => rCut_eq_zero_of_le_norm (le_of_lt (thra_pos h0 h1)) (thra_lt_thrb h0) h)
    (norm_rCut_le_one _ _)
    (fun ζ h => dbarC_rCut_eq_zero_of_norm_le (le_of_lt (thra_pos h0 h1)) (thra_lt_thrb h0) h)
    (fun ζ h => dbarC_rCut_eq_zero_of_le_norm (le_of_lt (thra_pos h0 h1)) (thra_lt_thrb h0) h)
    (chiC (thra η) (thrb η) (le_of_lt (thra_pos h0 h1)) (thra_lt_thrb h0))
    (chiC_spec (le_of_lt (thra_pos h0 h1)) (thra_lt_thrb h0)).1
    (chiC_spec (le_of_lt (thra_pos h0 h1)) (thra_lt_thrb h0)).2
    (chiC' (thra η) (thrb η) (le_of_lt (thra_pos h0 h1)) (thra_lt_thrb h0))
    (chiC'_spec (le_of_lt (thra_pos h0 h1)) (thra_lt_thrb h0)).1
    (chiC'_spec (le_of_lt (thra_pos h0 h1)) (thra_lt_thrb h0)).2
    (chiL (thra η) (thrb η) (le_of_lt (thra_pos h0 h1)) (thra_lt_thrb h0))
    (chiL_spec (le_of_lt (thra_pos h0 h1)) (thra_lt_thrb h0)).1
    (chiL_spec (le_of_lt (thra_pos h0 h1)) (thra_lt_thrb h0)).2

@[simp] lemma geomOf_a {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) :
    (geomOf (n := n) η h0 h1).a = thra η := rfl

@[simp] lemma geomOf_b {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) :
    (geomOf (n := n) η h0 h1).b = thrb η := rfl

@[simp] lemma geomOf_T {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) :
    (geomOf (n := n) η h0 h1).T = thrT η := rfl

@[simp] lemma geomOf_e {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) :
    (geomOf (n := n) η h0 h1).e = thre η := rfl

/-! ## The diagonal dilation and the pulled-back datum -/

/-- The diagonal dilation `y ↦ (j ↦ S j * y j)`. -/
def Phi (S : Fin n → ℝ) : (Fin n → ℂ) → (Fin n → ℂ) := fun y l => (S l : ℂ) * y l

/-- Its inverse `z ↦ (j ↦ (S j)⁻¹ * z j)`. -/
def Psi (S : Fin n → ℝ) : (Fin n → ℂ) → (Fin n → ℂ) :=
  fun z l => (((S l)⁻¹ : ℝ) : ℂ) * z l

/-- The pull-back of a `(0,1)`-form datum under the dilation. -/
def pull (S : Fin n → ℝ) (h : Fin n → (Fin n → ℂ) → ℂ) : Fin n → (Fin n → ℂ) → ℂ :=
  fun j y => (S j : ℂ) * h j (Phi S y)

@[simp] lemma Phi_apply (S : Fin n → ℝ) (y : Fin n → ℂ) (l : Fin n) :
    Phi S y l = (S l : ℂ) * y l := rfl

@[simp] lemma Psi_apply (S : Fin n → ℝ) (z : Fin n → ℂ) (l : Fin n) :
    Psi S z l = (((S l)⁻¹ : ℝ) : ℂ) * z l := rfl

@[simp] lemma pull_apply (S : Fin n → ℝ) (h : Fin n → (Fin n → ℂ) → ℂ) (j : Fin n)
    (y : Fin n → ℂ) : pull S h j y = (S j : ℂ) * h j (Phi S y) := rfl

lemma Phi_Psi {S : Fin n → ℝ} (hS : ∀ l, S l ≠ 0) (z : Fin n → ℂ) : Phi S (Psi S z) = z := by
  funext l
  show (S l : ℂ) * ((((S l)⁻¹ : ℝ) : ℂ) * z l) = z l
  rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (hS l), Complex.ofReal_one, one_mul]

lemma Psi_Phi {S : Fin n → ℝ} (hS : ∀ l, S l ≠ 0) (y : Fin n → ℂ) : Psi S (Phi S y) = y := by
  funext l
  show ((((S l)⁻¹ : ℝ) : ℂ)) * ((S l : ℂ) * y l) = y l
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (hS l), Complex.ofReal_one, one_mul]

lemma contDiff_Phi (S : Fin n → ℝ) : ContDiff ℝ ∞ (Phi S) := by
  rw [contDiff_pi]
  intro l
  exact contDiff_const.mul (contDiff_apply ℝ ℂ l)

lemma contDiff_Psi (S : Fin n → ℝ) : ContDiff ℝ ∞ (Psi S) := by
  rw [contDiff_pi]
  intro l
  exact contDiff_const.mul (contDiff_apply ℝ ℂ l)

/-- The Lipschitz bound for the dilation. -/
lemma norm_Phi_sub_le {S : Fin n → ℝ} (hS : ∀ l, 0 ≤ S l) (y y' : Fin n → ℂ) :
    ‖Phi S y - Phi S y'‖ ≤ (∑ l, S l) * ‖y - y'‖ := by
  have hsum : 0 ≤ ∑ l, S l := Finset.sum_nonneg fun l _ => hS l
  have hnn : 0 ≤ (∑ l, S l) * ‖y - y'‖ := mul_nonneg hsum (norm_nonneg _)
  refine (pi_norm_le_iff_of_nonneg hnn).mpr fun l => ?_
  show ‖(S l : ℂ) * y l - (S l : ℂ) * y' l‖ ≤ (∑ l, S l) * ‖y - y'‖
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hS l)]
  exact mul_le_mul (Finset.single_le_sum (fun l _ => hS l) (Finset.mem_univ l))
    (norm_le_pi_norm (y - y') l) (norm_nonneg _) hsum

/-! ## The cutoff on the physical variable -/

/-- The inner radius of the physical cutoff: the dilation of the tracking polydisc. -/
def cutIn (η : ℝ) (ρ : Fin n → ℝ) : Fin n → ℝ := fun j => thrT η * scale η ρ j

/-- The outer radius of the physical cutoff. -/
def cutOut (η : ℝ) (ρ : Fin n → ℝ) : Fin n → ℝ :=
  fun j => (thrT η * scale η ρ j + ρ j) / 2

lemma cutIn_nonneg {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) (j : Fin n) : 0 ≤ cutIn η ρ j := by
  rw [cutIn]
  exact mul_nonneg (le_of_lt (thrT_pos h0 h1)) (le_of_lt (scale_pos h0 h1 hρ j))

lemma cutIn_lt_cutOut {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) (j : Fin n) : cutIn η ρ j < cutOut η ρ j := by
  have := thrT_mul_scale_lt h0 h1 hρ j
  rw [cutIn, cutOut]
  linarith

lemma cutOut_lt_rho {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) (j : Fin n) : cutOut η ρ j < ρ j := by
  have := thrT_mul_scale_lt h0 h1 hρ j
  rw [cutOut]
  linarith

/-- The physical cutoff. -/
def polCut (η : ℝ) (ρ : Fin n → ℝ) : (Fin n → ℂ) → ℂ := polydiscCut (cutIn η ρ) (cutOut η ρ)

lemma contDiff_polCut {η : ℝ} (ρ : Fin n → ℝ) : ContDiff ℝ ∞ (polCut η ρ) :=
  contDiff_polydiscCut _ _

lemma polCut_eq_one_of_Phi {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) {y : Fin n → ℂ} (hy : y ∈ polydisc 0 (fun _ => thrT η)) :
    polCut η ρ (Phi (scale η ρ) y) = 1 := by
  refine polydiscCut_eq_one (fun j => cutIn_nonneg h0 h1 hρ j)
    (fun j => cutIn_lt_cutOut h0 h1 hρ j) (fun j => ?_)
  show ‖(scale η ρ j : ℂ) * y j‖ ≤ cutIn η ρ j
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt (scale_pos h0 h1 hρ j)), cutIn]
  have hyl : ‖y j‖ < thrT η := by simpa using hy j
  nlinarith [scale_pos h0 h1 hρ j]

lemma polCut_eq_one_of_norm_le_cutIn {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) {z : Fin n → ℂ} (hz : ∀ l, ‖z l‖ ≤ cutIn η ρ l) :
    polCut η ρ z = 1 :=
  polydiscCut_eq_one (fun j => cutIn_nonneg h0 h1 hρ j)
    (fun j => cutIn_lt_cutOut h0 h1 hρ j) hz

/-! ## Multiplication of a datum by a cutoff -/

/-- Multiplication of a `(0,1)`-form datum by a complex-valued function, as an `ℝ`-linear map. -/
noncomputable def cutMul (χ : (Fin n → ℂ) → ℂ) :
    (Fin n → (Fin n → ℂ) → ℂ) →ₗ[ℝ] (Fin n → (Fin n → ℂ) → ℂ) where
  toFun f := fun j y => χ y * f j y
  map_add' f g := by
    funext j y
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext j y
    simp only [Pi.smul_apply, Complex.real_smul, RingHom.id_apply]
    ring

@[simp] lemma cutMul_apply (χ : (Fin n → ℂ) → ℂ) (f : Fin n → (Fin n → ℂ) → ℂ)
    (j : Fin n) (y : Fin n → ℂ) : cutMul χ f j y = χ y * f j y := rfl

/-- The datum fed to the construction: the cutoff times `f`, rescaled by `S` and dilated. -/
noncomputable def dataOf (η : ℝ) (ρ : Fin n → ℝ) (f : Fin n → (Fin n → ℂ) → ℂ) :
    Fin n → (Fin n → ℂ) → ℂ :=
  pull (scale η ρ) (cutMul (polCut η ρ) f)

@[simp] lemma dataOf_apply (η : ℝ) (ρ : Fin n → ℝ) (f : Fin n → (Fin n → ℂ) → ℂ)
    (j : Fin n) (y : Fin n → ℂ) :
    dataOf η ρ f j y
      = (scale η ρ j : ℂ) * (polCut η ρ (Phi (scale η ρ) y) * f j (Phi (scale η ρ) y)) := rfl

/-- The dilation of a point of the tracking polydisc lies in `polydisc 0 ρ`. -/
lemma phi_mem_polydisc {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) {y : Fin n → ℂ} (hy : y ∈ polydisc 0 (fun _ => thrT η)) :
    Phi (scale η ρ) y ∈ polydisc 0 ρ := by
  intro l
  show ‖Phi (scale η ρ) y l - 0‖ < ρ l
  rw [sub_zero, Phi_apply, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (le_of_lt (scale_pos h0 h1 hρ l))]
  have hlt := thrT_mul_scale_lt h0 h1 hρ l
  have hyl : ‖y l‖ < thrT η := by simpa using hy l
  nlinarith [scale_pos h0 h1 hρ l]

/-- The `(0,1)`-dilation of a point of the tracking polydisc: also for `Ψ`. -/
lemma psi_mem_track {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) {z : Fin n → ℂ} (hz : ∀ l, ‖z l‖ < thre η * scale η ρ l) :
    Psi (scale η ρ) z ∈ polydisc 0 (fun _ => thrT η) := by
  intro l
  show ‖Psi (scale η ρ) z l - 0‖ < thrT η
  rw [sub_zero, Psi_apply, norm_mul, Complex.norm_real, norm_inv,
    Real.norm_of_nonneg (le_of_lt (scale_pos h0 h1 hρ l)), inv_mul_eq_div,
    div_lt_iff₀ (scale_pos h0 h1 hρ l)]
  have hzl := hz l
  have hlt := thre_lt_thrT h0
  nlinarith [scale_pos h0 h1 hρ l]

/-- The inverse dilation of the equation polydisc lands in the equation polydisc. -/
lemma psi_mem_solve {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) {z : Fin n → ℂ} (hz : ∀ l, ‖z l‖ < thre η * scale η ρ l)
    (l : Fin n) : ‖Psi (scale η ρ) z l‖ < thre η := by
  rw [Psi_apply, norm_mul, Complex.norm_real, norm_inv,
    Real.norm_of_nonneg (le_of_lt (scale_pos h0 h1 hρ l)), inv_mul_eq_div,
    div_lt_iff₀ (scale_pos h0 h1 hρ l)]
  exact hz l

/-- The inverse dilation of the equation polydisc lands in the constant polydisc of radius
`thre η`. -/
lemma psi_mem_polydisc {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) {z : Fin n → ℂ} (hz : ∀ l, ‖z l‖ < thre η * scale η ρ l) :
    Psi (scale η ρ) z ∈ polydisc 0 (fun _ => thre η) := by
  intro l
  show ‖Psi (scale η ρ) z l - 0‖ < thre η
  rw [sub_zero]
  exact psi_mem_solve h0 h1 hρ hz l

/-- The equation threshold times the scaling dominates `ρ''`. -/
lemma mem_solveSet_of_rho'' {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ ρ'' : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hlt : ∀ j, ρ'' j < ρ j * (1 - η)) {z : Fin n → ℂ}
    (hz : ∀ l, ‖z l‖ < ρ'' l) : Psi (scale η ρ) z ∈ polydisc 0 (fun _ => thre η) := by
  intro l
  show ‖Psi (scale η ρ) z l - 0‖ < thre η
  rw [sub_zero, Psi_apply, norm_mul, Complex.norm_real, norm_inv,
    Real.norm_of_nonneg (le_of_lt (scale_pos h0 h1 hρ l)), inv_mul_eq_div,
    div_lt_iff₀ (scale_pos h0 h1 hρ l)]
  linarith [hz l, hlt l, thre_mul_scale_ge h0 h1 hρ l]

/-- The equation radius times the scaling is still below `ρ`. -/
lemma thre_mul_scale_lt_rho {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) (j : Fin n) : thre η * scale η ρ j < ρ j :=
  lt_trans (mul_lt_mul_of_pos_right (thre_lt_thrT h0) (scale_pos h0 h1 hρ j))
    (thrT_mul_scale_lt h0 h1 hρ j)

/-- `S l ≠ 0` for all `l`. -/
lemma scale_ne_zero {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) (l : Fin n) : scale η ρ l ≠ 0 :=
  ne_of_gt (scale_pos h0 h1 hρ l)

/-- The Lipschitz bound for `Ψ`. -/
lemma norm_Psi_sub_le {S : Fin n → ℝ} (hS : ∀ l, 0 ≤ S l) (z z' : Fin n → ℂ) :
    ‖Psi S z - Psi S z'‖ ≤ (∑ l, (S l)⁻¹) * ‖z - z'‖ := by
  have hsum : 0 ≤ ∑ l, (S l)⁻¹ := Finset.sum_nonneg fun l _ => inv_nonneg.mpr (hS l)
  have hnn : 0 ≤ (∑ l, (S l)⁻¹) * ‖z - z'‖ := mul_nonneg hsum (norm_nonneg _)
  refine (pi_norm_le_iff_of_nonneg hnn).mpr fun l => ?_
  show ‖(((S l)⁻¹ : ℝ) : ℂ) * z l - (((S l)⁻¹ : ℝ) : ℂ) * z' l‖ ≤ (∑ l, (S l)⁻¹) * ‖z - z'‖
  rw [← mul_sub, norm_mul, Complex.norm_real, norm_inv, Real.norm_of_nonneg (hS l)]
  exact mul_le_mul (Finset.single_le_sum (fun l _ => inv_nonneg.mpr (hS l)) (Finset.mem_univ l))
    (norm_le_pi_norm (z - z') l) (norm_nonneg _) hsum

end Work.NN.Ratio
