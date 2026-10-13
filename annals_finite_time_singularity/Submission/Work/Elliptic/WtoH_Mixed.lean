/-
Copyright: work module for the Elgindi finite-time singularity project.

# The mixed `𝒲^{4,∞} → ℋ⁴` transfer `WtoH_Mixed`

Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021),
Proposition `WtoH` (tex 1237).  This file proves the mixed-derivative half of the
transfer: for `0 < α ≤ 1`, `f` smooth near the quadrant and `(z+1)³/z²·f ∈ 𝒲^{4,∞}`,
every weighted mixed derivative `(1+z)·w(z)·z^m·∂_z^m D_θ^i f` with `1 ≤ i`, `m+i ≤ 4`
is controlled by `|(z+1)³/z²·f|_{𝒲^{4,∞}}` times the angular factor
`(α + sin 2θ)·sin(2θ)^{α/5}`.

The argument: write `f = z²κ` with `κ = Work.Elliptic.divZ2 f`; the Leibniz expansion
`∂_z^m D_θ^i f = z²∂_z^m κ + 2m z ∂_z^{m-1}κ + m(m-1)∂_z^{m-2}κ` (`expand_aux`) reduces
the claim to bounds on `∂_z^j κ`, which the triangular estimate `tri_bound` derives from
the `𝒲^{4,∞}`-bounds on `(z+1)^j ∂_z^j D_θ^i ((z+1)³/z² f)` supplied by `factor_bound`
(`tri_aux`); the remaining bookkeeping `z^j ≤ (z+1)^j` is `arith_aux`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.Elliptic.WtoH_Mixed_g_eq
import Submission.Work.Spaces.factor_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

open Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary absolute-value bookkeeping -/

/-- Comparison of powers: `|z^k X| ≤ |(z+1)^k X|` for `z ≥ 0`. -/
private lemma abs_mul_pow_le_succ (z X : ℝ) (hz : 0 ≤ z) (k : ℕ) :
    |z ^ k * X| ≤ |(z + 1) ^ k * X| := by
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hz k),
    abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ z + 1) k)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz (by linarith) k) (abs_nonneg X)

/-- Triangle inequality for three weighted terms. -/
private lemma abs_comb3_le {Cst : ℝ} (hCst : 0 ≤ Cst) {a b c : ℝ} (ha : |a| ≤ Cst)
    (hb : |b| ≤ Cst) (hc : |c| ≤ Cst) {A B D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    |A * a + B * b + D * c| ≤ (A + B + D) * Cst := by
  have h1 : |A * a| ≤ A * Cst := by
    rw [abs_mul, abs_of_nonneg hA]
    exact mul_le_mul_of_nonneg_left ha hA
  have h2 : |B * b| ≤ B * Cst := by
    rw [abs_mul, abs_of_nonneg hB]
    exact mul_le_mul_of_nonneg_left hb hB
  have h3 : |D * c| ≤ D * Cst := by
    rw [abs_mul, abs_of_nonneg hD]
    exact mul_le_mul_of_nonneg_left hc hD
  have htri : |A * a + B * b + D * c| ≤ |A * a| + |B * b| + |D * c| := by
    calc |A * a + B * b + D * c| ≤ |A * a + B * b| + |D * c| := abs_add_le _ _
      _ ≤ (|A * a| + |B * b|) + |D * c| := by linarith [abs_add_le (A * a) (B * b)]
      _ = |A * a| + |B * b| + |D * c| := by ring
  calc |A * a + B * b + D * c| ≤ |A * a| + |B * b| + |D * c| := htri
    _ ≤ A * Cst + B * Cst + D * Cst := by linarith
    _ = (A + B + D) * Cst := by ring

/-! ## The Leibniz expansion of `∂_z^l D_θ^i f` through `f = z²·divZ2 f` -/

/-- `∂_z^l D_θ^i f = z² ∂_z^l κ + 2l z ∂_z^{l-1}κ + l(l-1) ∂_z^{l-2}κ` with
`κ = D_θ^i (divZ2 f)`. -/
private theorem expand_aux {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f) (i l : ℕ)
    (hl : l ≤ 4) {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.pzIter l (Work.Spaces.DthIter i f) z θ
      = z ^ 2 * Work.Spaces.pzIter l (Work.Spaces.DthIter i (divZ2 f)) z θ
        + (2 * (l : ℝ)) * z * Work.Spaces.pzIter (l - 1) (Work.Spaces.DthIter i (divZ2 f)) z θ
        + ((l : ℝ) * ((l : ℝ) - 1))
            * Work.Spaces.pzIter (l - 2) (Work.Spaces.DthIter i (divZ2 f)) z θ := by
  have hκ : ContDiffAt ℝ ⊤ (fun z' => Work.Spaces.DthIter i (divZ2 f) z' θ) z :=
    contDiffAt_DthIter_divZ2_zslice hsm i θ hθ z hz
  have hmemIoi : Set.Ioi (0 : ℝ) ∈ 𝓝 z :=
    isOpen_Ioi.mem_nhds (by simp only [Set.mem_Ioi]; linarith)
  have hev : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ,
      Work.Spaces.DthIter i f z' θ' = z' ^ 2 * Work.Spaces.DthIter i (divZ2 f) z' θ' := by
    filter_upwards [hmemIoi] with z' hz' θ'
    exact DthIter_divZ2_eq i (ne_of_gt hz')
  rw [Work.Elliptic.pzIter_congr_of_eventually (u := Work.Spaces.DthIter i f)
    (v := fun z θ => z ^ 2 * Work.Spaces.DthIter i (divZ2 f) z θ) (z := z) (θ := θ) l hev]
  exact Work.Elliptic.pzIter_sq_mul l hl hκ

/-! ## From the `𝒲^{4,∞}`-bounds on `(z+1)³/z²·f` to bounds on `∂_z^j κ` -/

/-- The triangular estimate applied to `κ = D_θ^i (divZ2 f)`: the `𝒲^{4,∞}`-bounds on
`(z+1)^j ∂_z^j D_θ^i ((z+1)³/z²·f)` give `|(z+1)^{j+3} ∂_z^j κ| ≤ 6000·Λ`. -/
private theorem tri_aux {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd f)
    (hmem : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ))
    {i l : ℕ} (hi : 1 ≤ i) (hli : l + i ≤ 4) {z : ℝ} (hz : 0 < z) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ)
    (hGev : ∀ z' : ℝ, 0 < z' → ∀ θ' : ℝ,
      Work.Spaces.DthIter i (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) z' θ'
        = (z' + 1) ^ 3 * Work.Spaces.DthIter i (divZ2 f) z' θ') :
    ∀ j ≤ l, |(z + 1) ^ (j + 3) * Work.Spaces.pzIter j (Work.Spaces.DthIter i (divZ2 f)) z θ|
      ≤ 6000 * (Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
  set Λ : ℝ := Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) with hΛ
  have hmemIoi : Set.Ioi (0 : ℝ) ∈ 𝓝 z :=
    isOpen_Ioi.mem_nhds (by simp only [Set.mem_Ioi]; linarith)
  have hev : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ,
      Work.Spaces.DthIter i (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) z' θ'
        = (z' + 1) ^ 3 * Work.Spaces.DthIter i (divZ2 f) z' θ' := by
    filter_upwards [hmemIoi] with z' hz' θ'
    exact hGev z' hz' θ'
  have hbound : ∀ j ≤ l,
      |(z + 1) ^ j * Work.Spaces.pzIter j
        (fun z θ => (z + 1) ^ 3 * Work.Spaces.DthIter i (divZ2 f) z θ) z θ| ≤ Λ := by
    intro j hj
    have hji : j + i ≤ 4 := by omega
    have h1 := Work.Spaces.factor_bound α hα (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)
      hmem j i (by omega) (fun _ => hji) z θ (le_of_lt hz) hθ
    rw [if_neg (by omega : ¬ (i = 0))] at h1
    have hEq : Work.Spaces.pzIter j
          (fun z θ => (z + 1) ^ 3 * Work.Spaces.DthIter i (divZ2 f) z θ) z θ
        = Work.Spaces.pzIter j
          (Work.Spaces.DthIter i (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)) z θ :=
      (Work.Elliptic.pzIter_congr_of_eventually
        (u := Work.Spaces.DthIter i (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ))
        (v := fun z θ => (z + 1) ^ 3 * Work.Spaces.DthIter i (divZ2 f) z θ)
        (z := z) (θ := θ) j hev).symm
    rw [hEq, hΛ]
    exact h1
  have hκ : ContDiffAt ℝ ⊤ (fun z' => Work.Spaces.DthIter i (divZ2 f) z' θ) z :=
    contDiffAt_DthIter_divZ2_zslice hsm i θ hθ z hz
  have hmain : ∀ j ≤ l,
      |(z + 1) ^ (j + 3) * Work.Spaces.pzIter j (Work.Spaces.DthIter i (divZ2 f)) z θ|
        ≤ 6000 * Λ :=
    tri_bound (G := fun z θ => (z + 1) ^ 3 * Work.Spaces.DthIter i (divZ2 f) z θ)
      (κ := Work.Spaces.DthIter i (divZ2 f)) rfl (by omega) hz hκ hbound
  intro j hj
  have hj' := hmain j hj
  rw [hΛ] at hj'
  exact hj'

/-! ## The elementary weighted estimate -/

/-- If `|(z+1)^{j+3} K j| ≤ 6000 M Φ` for `j ≤ l ≤ 3`, `z > 0`, `M, Φ ≥ 0`, then the
weighted expression `((z+1)³ z^l/z²)·(z²K_l + 2l z K_{l-1} + l(l-1)K_{l-2})` is
`≤ 200000 M Φ`. -/
private theorem arith_aux {z : ℝ} (hz : 0 < z) {M Φ : ℝ} (hM : 0 ≤ M) (hΦ : 0 ≤ Φ)
    (l : ℕ) (hl : l ≤ 3) (K : ℕ → ℝ)
    (hK : ∀ j ≤ l, |(z + 1) ^ (j + 3) * K j| ≤ 6000 * (M * Φ)) :
    |(z + 1) ^ 3 * z ^ l / z ^ 2 * (z ^ 2 * K l + (2 * (l : ℝ)) * z * K (l - 1)
        + ((l : ℝ) * ((l : ℝ) - 1)) * K (l - 2))| ≤ 200000 * (M * Φ) := by
  have hMΦ : 0 ≤ M * Φ := mul_nonneg hM hΦ
  have hz0 : (0 : ℝ) ≤ z := le_of_lt hz
  have hterm : ∀ j ≤ l, |z ^ j * ((z + 1) ^ 3 * K j)| ≤ 6000 * (M * Φ) := by
    intro j hj
    refine le_trans (abs_mul_pow_le_succ z ((z + 1) ^ 3 * K j) hz0 j) ?_
    have h2 : (z + 1) ^ j * ((z + 1) ^ 3 * K j) = (z + 1) ^ (j + 3) * K j := by
      rw [← mul_assoc, ← pow_add]
    rw [h2]
    exact hK j hj
  interval_cases l
  · -- l = 0
    have hid : (z + 1) ^ 3 * z ^ 0 / z ^ 2
          * (z ^ 2 * K 0 + (2 * ((0 : ℕ) : ℝ)) * z * K (0 - 1)
              + (((0 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) - 1)) * K (0 - 2))
        = 1 * (z ^ 0 * ((z + 1) ^ 3 * K 0))
          + (2 * ((0 : ℕ) : ℝ)) * (z ^ 0 * ((z + 1) ^ 3 * K 0))
          + (((0 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) - 1)) * (z ^ 0 * ((z + 1) ^ 3 * K 0)) := by
      have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
      push_cast
      norm_num1
      field_simp <;> ring
    rw [hid]
    refine le_trans (abs_comb3_le (by nlinarith [hMΦ]) (hterm 0 (by norm_num))
      (hterm 0 (by norm_num)) (hterm 0 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num)) ?_
    norm_num1
    nlinarith [hMΦ]
  · -- l = 1
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
    have hid : (z + 1) ^ 3 * z ^ 1 / z ^ 2
          * (z ^ 2 * K 1 + (2 * ((1 : ℕ) : ℝ)) * z * K (1 - 1)
              + (((1 : ℕ) : ℝ) * (((1 : ℕ) : ℝ) - 1)) * K (1 - 2))
        = 1 * (z ^ 1 * ((z + 1) ^ 3 * K 1))
          + (2 * ((1 : ℕ) : ℝ)) * (z ^ (1 - 1) * ((z + 1) ^ 3 * K (1 - 1)))
          + (((1 : ℕ) : ℝ) * (((1 : ℕ) : ℝ) - 1))
              * (z ^ (1 - 2) * ((z + 1) ^ 3 * K (1 - 2))) := by
      push_cast
      norm_num1
      field_simp <;> ring
    rw [hid]
    refine le_trans (abs_comb3_le (by nlinarith [hMΦ]) (hterm 1 (by norm_num))
      (hterm 0 (by norm_num)) (hterm 0 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num)) ?_
    norm_num1
    nlinarith [hMΦ]
  · -- l = 2
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
    have hid : (z + 1) ^ 3 * z ^ 2 / z ^ 2
          * (z ^ 2 * K 2 + (2 * ((2 : ℕ) : ℝ)) * z * K (2 - 1)
              + (((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) - 1)) * K (2 - 2))
        = 1 * (z ^ 2 * ((z + 1) ^ 3 * K 2))
          + (2 * ((2 : ℕ) : ℝ)) * (z ^ (2 - 1) * ((z + 1) ^ 3 * K (2 - 1)))
          + (((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) - 1))
              * (z ^ (2 - 2) * ((z + 1) ^ 3 * K (2 - 2))) := by
      push_cast
      norm_num1
      field_simp <;> ring
    rw [hid]
    refine le_trans (abs_comb3_le (by nlinarith [hMΦ]) (hterm 2 (by norm_num))
      (hterm 1 (by norm_num)) (hterm 0 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num)) ?_
    norm_num1
    nlinarith [hMΦ]
  · -- l = 3
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
    have hid : (z + 1) ^ 3 * z ^ 3 / z ^ 2
          * (z ^ 2 * K 3 + (2 * ((3 : ℕ) : ℝ)) * z * K (3 - 1)
              + (((3 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) - 1)) * K (3 - 2))
        = 1 * (z ^ 3 * ((z + 1) ^ 3 * K 3))
          + (2 * ((3 : ℕ) : ℝ)) * (z ^ (3 - 1) * ((z + 1) ^ 3 * K (3 - 1)))
          + (((3 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) - 1))
              * (z ^ (3 - 2) * ((z + 1) ^ 3 * K (3 - 2))) := by
      push_cast
      norm_num1
      field_simp <;> ring
    rw [hid]
    refine le_trans (abs_comb3_le (by nlinarith [hMΦ]) (hterm 3 (by norm_num))
      (hterm 2 (by norm_num)) (hterm 1 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num)) ?_
    norm_num1
    nlinarith [hMΦ]

/-! ## The transfer -/

theorem WtoH_Mixed {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd f)
    (hmem : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)) :
    ∀ (i l : ℕ), 1 ≤ i → l + i ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |(1 + z) * Work.Spaces.w z * z ^ l
          * Work.Spaces.pzIter l (Work.Spaces.DthIter i f) z θ|
        ≤ 200000 * (Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
  intro i l hi hli z hz θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hθ.1]
    · linarith [hθ.2, Real.pi_pos]
  have hrad : 0 ≤ Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 _ hmem)
      (Work.Spaces.wlThSum_nonneg α 4 _ hmem)
  have hang : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hs0 _)
  have hGev : ∀ z' : ℝ, 0 < z' → ∀ θ' : ℝ,
      Work.Spaces.DthIter i (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) z' θ'
        = (z' + 1) ^ 3 * Work.Spaces.DthIter i (divZ2 f) z' θ' :=
    fun z' hz' θ' => WtoH_Mixed_g_eq i (ne_of_gt hz')
  have hK : ∀ j ≤ l, |(z + 1) ^ (j + 3)
      * Work.Spaces.pzIter j (Work.Spaces.DthIter i (divZ2 f)) z θ|
      ≤ 6000 * (Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
    tri_aux hα hsm hmem hi hli hz hθ hGev
  have hexp := expand_aux (f := f) hsm i l (by omega) hz hθ
  have hw : (1 + z) * Work.Spaces.w z * z ^ l = (z + 1) ^ 3 * z ^ l / z ^ 2 := by
    rw [Work.Spaces.w]
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
    field_simp <;> ring
  rw [hw, hexp]
  exact arith_aux hz hrad hang l (by omega)
    (fun j => Work.Spaces.pzIter j (Work.Spaces.DthIter i (divZ2 f)) z θ) hK

end Work.Elliptic
