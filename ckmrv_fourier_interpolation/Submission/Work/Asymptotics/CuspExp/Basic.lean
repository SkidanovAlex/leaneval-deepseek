/-
# Cusp bounds in powers of `E = e^{πiz}`

`Work.Asymptotics.CuspBdd K T f n M` (read: `f = O((1+im z)^M ‖E(z)‖^n)` for `τ ∈ K`,
`T ≤ im z`) is the asymptotic notion used in the proof of the cusp-`i∞` expansion of the
CKMRV kernel along the contour `z = it`.  Here `E z = e^{πiz}`, so `‖E z‖ = e^{-π Im z}`,
`n : ℤ` (negative powers occur: the leading term of `1/Δ(z)` is `E^{-2}`) and `M : ℝ`.

The file contains the notion, the gauge function `cuspG z M n = (1 + im z)^M ‖E z‖^n`, and
the closure properties of `CuspBdd` (addition, multiplication, multiplication by bounded
functions of `τ`, weakening of the exponents, congruence).
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Kernels.Theorem31
import Submission.Work.Residues.ThetaEpt

namespace Work.Asymptotics

open UpperHalfPlane

noncomputable section

/-! ## Elementary facts about `E(z) = e^{πiz}` -/

lemma Ept_ne_zero' (z : ℍ) : Work.Residues.Ept z ≠ 0 := Work.Residues.Ept_ne_zero z

/-- `‖E(it)‖ = e^{-πt}` for `t > 0`. -/
lemma norm_Ept_imagAxis (t : ℝ) (ht : 0 < t) :
    ‖Work.Residues.Ept (Work.Kernels.imagAxis t ht)‖ = Real.exp (-(Real.pi * t)) := by
  rw [Work.Residues.norm_Ept]
  congr 1
  simp [Work.Kernels.imagAxis]

/-- `‖E(z)‖ ≤ 1` for `0 ≤ Im z`. -/
lemma norm_Ept_le_one {z : ℍ} (hz : 0 ≤ z.im) : ‖Work.Residues.Ept z‖ ≤ 1 := by
  rw [Work.Residues.norm_Ept, Real.exp_le_one_iff]
  nlinarith [Real.pi_pos, hz]

/-- For `0 < r ≤ 1` the map `n ↦ r ^ n` (integer exponent) is antitone. -/
lemma zpow_le_zpow_of_le_one {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) {m n : ℤ} (hmn : m ≤ n) :
    r ^ n ≤ r ^ m := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = m + k := ⟨(n - m).toNat, by omega⟩
  rw [hk, zpow_add₀ (ne_of_gt h0), zpow_natCast]
  have hk1 : r ^ k ≤ 1 := pow_le_one₀ h0.le h1
  calc r ^ m * r ^ k ≤ r ^ m * 1 := mul_le_mul_of_nonneg_left hk1 (zpow_nonneg h0.le m)
    _ = r ^ m := mul_one _

/-! ## The gauge -/

/-- The weight `1 + |Re z| + Im z` (dominating `|z|` and `1 + Im z`). -/
def cuspW (z : ℍ) : ℝ := 1 + |(z : ℂ).re| + z.im

lemma cuspW_pos (z : ℍ) : 0 < cuspW z := by
  have h1 := z.im_pos
  have h2 := abs_nonneg (z : ℂ).re
  unfold cuspW
  linarith

lemma cuspW_one_le (z : ℍ) : 1 ≤ cuspW z := by
  have := z.im_pos; unfold cuspW; linarith [abs_nonneg (z : ℂ).re]

lemma coe_norm_le_cuspW (z : ℍ) : ‖(z : ℂ)‖ ≤ cuspW z := by
  have h := Complex.norm_le_abs_re_add_abs_im (z : ℂ)
  rw [UpperHalfPlane.coe_im, abs_of_pos z.im_pos] at h
  unfold cuspW
  linarith

/-- The gauge `(1 + |Re z| + Im z)^M ‖E(z)‖^n` in which the cusp bounds are measured. -/
def cuspG (z : ℍ) (M : ℝ) (n : ℤ) : ℝ := (cuspW z) ^ M * ‖Work.Residues.Ept z‖ ^ n

lemma cuspG_nonneg (z : ℍ) (M : ℝ) (n : ℤ) : 0 ≤ cuspG z M n :=
  mul_nonneg (Real.rpow_nonneg (le_of_lt (cuspW_pos z)) M) (zpow_nonneg (norm_nonneg _) _)

lemma cuspG_mul (z : ℍ) (M₁ M₂ : ℝ) (n₁ n₂ : ℤ) :
    cuspG z (M₁ + M₂) (n₁ + n₂) = cuspG z M₁ n₁ * cuspG z M₂ n₂ := by
  unfold cuspG
  rw [Real.rpow_add (cuspW_pos z),
    zpow_add₀ (ne_of_gt (norm_pos_iff.mpr (Ept_ne_zero' z)))]
  ring

lemma cuspG_mono (z : ℍ) {M M' : ℝ} {n n' : ℤ} (hM : M ≤ M') (hn : n' ≤ n) :
    cuspG z M n ≤ cuspG z M' n' := by
  have h1 : (1 : ℝ) ≤ cuspW z := cuspW_one_le z
  have h2 : (cuspW z) ^ M ≤ (cuspW z) ^ M' := Real.rpow_le_rpow_of_exponent_le h1 hM
  have h3 : ‖Work.Residues.Ept z‖ ^ n ≤ ‖Work.Residues.Ept z‖ ^ n' :=
    zpow_le_zpow_of_le_one (norm_pos_iff.mpr (Ept_ne_zero' z))
      (norm_Ept_le_one (by linarith [z.im_pos])) hn
  unfold cuspG
  exact mul_le_mul h2 h3 (zpow_nonneg (norm_nonneg _) _)
    (Real.rpow_nonneg (le_of_lt (cuspW_pos z)) M')

/-! ## The predicate -/

/-- `CuspBdd K T f n M`: there is `C > 0` with `‖f τ z‖ ≤ C (1 + Im z)^M ‖E(z)‖^n` for all
`τ ∈ K` and all `z` with `T ≤ Im z`. -/
def CuspBdd (K : Set ℍ) (T : ℝ) (f : ℍ → ℍ → ℂ) (n : ℤ) (M : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ K, ∀ z : ℍ, T ≤ z.im → ‖f τ z‖ ≤ C * cuspG z M n

namespace CuspBdd

variable {K : Set ℍ} {T : ℝ} {f g : ℍ → ℍ → ℂ} {n m : ℤ} {M N : ℝ}

lemma mono (hT : 0 ≤ T) {n' : ℤ} {M' : ℝ} (hn : n' ≤ n) (hM : M ≤ M')
    (h : CuspBdd K T f n M) : CuspBdd K T f n' M' := by
  obtain ⟨C, hC, hCb⟩ := h
  refine ⟨C, hC, fun τ hτ z hz => ?_⟩
  refine le_trans (hCb τ hτ z hz) ?_
  exact mul_le_mul_of_nonneg_left (cuspG_mono z hM hn) hC.le

lemma const_mul (c : ℂ) (h : CuspBdd K T f n M) :
    CuspBdd K T (fun τ z => c * f τ z) n M := by
  obtain ⟨C, hC, hCb⟩ := h
  refine ⟨‖c‖ * C + 1, by positivity, fun τ hτ z hz => ?_⟩
  calc ‖c * f τ z‖ = ‖c‖ * ‖f τ z‖ := norm_mul _ _
    _ ≤ ‖c‖ * (C * cuspG z M n) := mul_le_mul_of_nonneg_left (hCb τ hτ z hz) (norm_nonneg _)
    _ = ‖c‖ * C * cuspG z M n := by ring
    _ ≤ (‖c‖ * C + 1) * cuspG z M n := by
        exact mul_le_mul_of_nonneg_right (by linarith) (cuspG_nonneg z M n)

lemma mul_const (c : ℍ → ℂ) (B : ℝ) (hB : 0 < B) (hc : ∀ τ ∈ K, ‖c τ‖ ≤ B)
    (h : CuspBdd K T f n M) : CuspBdd K T (fun τ z => c τ * f τ z) n M := by
  obtain ⟨C, hC, hCb⟩ := h
  refine ⟨B * C + 1, by positivity, fun τ hτ z hz => ?_⟩
  calc ‖c τ * f τ z‖ = ‖c τ‖ * ‖f τ z‖ := norm_mul _ _
    _ ≤ B * (C * cuspG z M n) :=
        mul_le_mul (hc τ hτ) (hCb τ hτ z hz) (norm_nonneg _) hB.le
    _ = B * C * cuspG z M n := by ring
    _ ≤ (B * C + 1) * cuspG z M n :=
        mul_le_mul_of_nonneg_right (by linarith) (cuspG_nonneg z M n)

lemma add (h₁ : CuspBdd K T f n M) (h₂ : CuspBdd K T g n M) :
    CuspBdd K T (fun τ z => f τ z + g τ z) n M := by
  obtain ⟨C₁, hC₁, hb₁⟩ := h₁
  obtain ⟨C₂, hC₂, hb₂⟩ := h₂
  refine ⟨C₁ + C₂, by positivity, fun τ hτ z hz => ?_⟩
  calc ‖f τ z + g τ z‖ ≤ ‖f τ z‖ + ‖g τ z‖ := norm_add_le _ _
    _ ≤ C₁ * cuspG z M n + C₂ * cuspG z M n := add_le_add (hb₁ τ hτ z hz) (hb₂ τ hτ z hz)
    _ = (C₁ + C₂) * cuspG z M n := by ring

lemma neg (h : CuspBdd K T f n M) : CuspBdd K T (fun τ z => -f τ z) n M := by
  have h' := h.const_mul (-1)
  simpa only [neg_one_mul] using h'

lemma sub (h₁ : CuspBdd K T f n M) (h₂ : CuspBdd K T g n M) :
    CuspBdd K T (fun τ z => f τ z - g τ z) n M := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

lemma mul (h₁ : CuspBdd K T f n M) (h₂ : CuspBdd K T g m N) :
    CuspBdd K T (fun τ z => f τ z * g τ z) (n + m) (M + N) := by
  obtain ⟨C₁, hC₁, hb₁⟩ := h₁
  obtain ⟨C₂, hC₂, hb₂⟩ := h₂
  refine ⟨C₁ * C₂, by positivity, fun τ hτ z hz => ?_⟩
  calc ‖f τ z * g τ z‖ = ‖f τ z‖ * ‖g τ z‖ := norm_mul _ _
    _ ≤ (C₁ * cuspG z M n) * (C₂ * cuspG z N m) :=
        mul_le_mul (hb₁ τ hτ z hz) (hb₂ τ hτ z hz) (norm_nonneg _)
          (mul_nonneg hC₁.le (cuspG_nonneg z M n))
    _ = C₁ * C₂ * cuspG z (M + N) (n + m) := by rw [cuspG_mul]; ring

lemma congr {h : ℍ → ℍ → ℂ} (hfg : ∀ τ z, f τ z = h τ z) (hb : CuspBdd K T f n M) :
    CuspBdd K T h n M := by
  obtain ⟨C, hC, hCb⟩ := hb
  exact ⟨C, hC, fun τ hτ z hz => by rw [← hfg τ z]; exact hCb τ hτ z hz⟩

lemma of_bound {B : ℝ} (hB : 0 < B) (h : ∀ τ ∈ K, ∀ z : ℍ, T ≤ z.im → ‖f τ z‖ ≤ B) :
    CuspBdd K T f 0 0 := by
  refine ⟨B, hB, fun τ hτ z hz => ?_⟩
  simp only [cuspG, Real.rpow_zero, zpow_zero, mul_one]
  exact h τ hτ z hz

lemma zero (K : Set ℍ) (T : ℝ) (n : ℤ) (M : ℝ) :
    CuspBdd K T (fun _ _ => (0 : ℂ)) n M :=
  ⟨1, one_pos, fun _ _ z _ => by simp only [norm_zero, one_mul]; exact cuspG_nonneg z M n⟩

lemma one (K : Set ℍ) (T : ℝ) : CuspBdd K T (fun _ _ => (1 : ℂ)) 0 0 :=
  of_bound one_pos (fun _ _ _ _ => by simp)

/-- The function `z ↦ z`. -/
lemma coe (K : Set ℍ) (T : ℝ) : CuspBdd K T (fun _ z => (z : ℂ)) 0 1 := by
  refine ⟨1, one_pos, fun τ _ z hz => ?_⟩
  simp only [cuspG, Real.rpow_one, zpow_zero, one_mul, mul_one]
  exact coe_norm_le_cuspW z

/-- `E(z)` itself. -/
lemma Ept (K : Set ℍ) (T : ℝ) : CuspBdd K T (fun _ z => Work.Residues.Ept z) 1 0 := by
  refine ⟨1, one_pos, fun τ _ z hz => ?_⟩
  simp only [cuspG, Real.rpow_zero, zpow_one, mul_one, one_mul]
  exact le_refl _

/-- `E(z)⁻¹`. -/
lemma Ept_inv (K : Set ℍ) (T : ℝ) : CuspBdd K T (fun _ z => (Work.Residues.Ept z)⁻¹) (-1) 0 := by
  refine ⟨1, one_pos, fun τ _ z hz => ?_⟩
  simp only [cuspG, Real.rpow_zero, zpow_neg, zpow_one, mul_one, norm_inv]
  exact le_of_eq (by ring)

end CuspBdd

end

end Work.Asymptotics
