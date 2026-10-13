import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS_RegExport.RXT.SysAux.PieceDefs
import Submission.Work.FTS_RegExport.RXT.SysAux.PieceCalc
import Submission.Work.FTS_RegExport.RXT.SysAux.piece_z_bounds_rho
import Submission.Work.FTS_RegExport.RXT.SysAux.piece_z_bounds_ab
import Submission.Work.FTS_RegExport.RXT.SysAux.piece_t_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.SysAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## §1  The one-variable factors

Every function below is a product of one of the radial factors

`ρ₁ = z²/(1+z)³`, `ρ₂ = z²/(1+z)⁴`, `a = 2z(1-z)/(1+z)³`, `b = 2z/(1+z)²`

with one of the angular factors `1`, `c2m θ = cos 2θ − sin²θ`, `sin²θ`; the pointwise bounds
on their one-variable iterates `ZIter j` / `TIter i` are the delegated lemmas
`piece_z_bounds_rho`, `piece_z_bounds_ab`, `piece_t_bounds`, and the separation identity
`mixed_sep` (in `PieceDefs`) turns a mixed jet of a separable product into a product of the
one-variable iterates. -/

private def rho1 (z : ℝ) : ℝ := z ^ 2 / (1 + z) ^ 3

private def rho2 (z : ℝ) : ℝ := z ^ 2 / (1 + z) ^ 4

private def aF (z : ℝ) : ℝ := 2 * z * (1 - z) / (1 + z) ^ 3

private def bF (z : ℝ) : ℝ := 2 * z / (1 + z) ^ 2

private def oneF (_ : ℝ) : ℝ := 1

private def c2mF (θ : ℝ) : ℝ := Work.Construction.c2m θ

private def sinsqF (θ : ℝ) : ℝ := Real.sin θ ^ 2

/-- The "leading" combination `E` of the forcing decomposition, as a function of `(z,θ)`. -/
private def Ef (μ β : ℝ) : ℝ → ℝ → ℝ := fun z θ =>
    ((1 - μ) + Work.Construction.c2m θ * (2 * β / (1 + z))) * (2 * z * (1 - z) / (1 + z) ^ 3)
  + (-(3 / (1 + z)) + β * (2 * z / (1 + z) ^ 2) / 2)
      * ((2 * β / 3) * Work.Construction.c2m θ * (2 * z / (1 + z) ^ 2))
  + ((1 + μ) - 2 / (1 + z) + β * Real.sin θ ^ 2 * (2 * z / (1 + z) ^ 2))
      * (2 * z / (1 + z) ^ 2)

/-! ## §2  The bounds on the one-variable iterates -/

private theorem ZIter_rho1_sq (j : ℕ) (hj : j ≤ 2) {z : ℝ} (hz : 0 < z) :
    |ZIter j rho1 z| ≤ 10 * (z ^ 2 / (1 + z) ^ 2) :=
  (piece_z_bounds_rho j hj z hz).1

private theorem ZIter_rho1_lin (j : ℕ) (hj : j ≤ 2) {z : ℝ} (hz : 0 < z) :
    |ZIter j rho1 z| ≤ 10 * (z / (1 + z) ^ 2) :=
  (piece_z_bounds_rho j hj z hz).2.1

private theorem ZIter_rho2_sq (j : ℕ) (hj : j ≤ 2) {z : ℝ} (hz : 0 < z) :
    |ZIter j rho2 z| ≤ 10 * (z ^ 2 / (1 + z) ^ 2) :=
  (piece_z_bounds_rho j hj z hz).2.2

private theorem ZIter_aF_le (j : ℕ) (hj : j ≤ 2) {z : ℝ} (hz : 0 < z) :
    |ZIter j aF z| ≤ 30 * (z / (1 + z) ^ 2) :=
  (piece_z_bounds_ab j hj z hz).1

private theorem ZIter_bF_le (j : ℕ) (hj : j ≤ 2) {z : ℝ} (hz : 0 < z) :
    |ZIter j bF z| ≤ 10 * (z / (1 + z) ^ 2) :=
  (piece_z_bounds_ab j hj z hz).2

private theorem TIter_oneF_le (i : ℕ) (hi : i ≤ 2) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) : |TIter i oneF θ| ≤ 1 :=
  (piece_t_bounds i hi θ hθ0 hθ1).1

private theorem TIter_c2mF_le (i : ℕ) (hi : i ≤ 2) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) : |TIter i c2mF θ| ≤ 12 :=
  (piece_t_bounds i hi θ hθ0 hθ1).2.1

private theorem TIter_sinsqF_le (i : ℕ) (hi : i ≤ 2) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) : |TIter i sinsqF θ| ≤ 4 :=
  (piece_t_bounds i hi θ hθ0 hθ1).2.2

/-! ## §3  Analyticity of the one-variable factors -/

private theorem contDiffOn_rho1 : ContDiffOn ℝ ⊤ rho1 (Set.Ioi 0) := by
  have hnum : ContDiffOn ℝ ⊤ (fun z : ℝ => z ^ 2) (Set.Ioi 0) := contDiffOn_id.pow 2
  have hden : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 + z) ^ 3) (Set.Ioi 0) :=
    (contDiffOn_const.add contDiffOn_id).pow 3
  have h := hnum.div hden (fun z hz => by
    have hz' : (0 : ℝ) < z := hz
    positivity)
  have hfun : rho1 = (fun z : ℝ => z ^ 2) / (fun z : ℝ => (1 + z) ^ 3) := by
    funext z
    simp only [rho1, Pi.div_apply]
  rwa [hfun]

private theorem contDiffOn_rho2 : ContDiffOn ℝ ⊤ rho2 (Set.Ioi 0) := by
  have hnum : ContDiffOn ℝ ⊤ (fun z : ℝ => z ^ 2) (Set.Ioi 0) := contDiffOn_id.pow 2
  have hden : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 + z) ^ 4) (Set.Ioi 0) :=
    (contDiffOn_const.add contDiffOn_id).pow 4
  have h := hnum.div hden (fun z hz => by
    have hz' : (0 : ℝ) < z := hz
    positivity)
  have hfun : rho2 = (fun z : ℝ => z ^ 2) / (fun z : ℝ => (1 + z) ^ 4) := by
    funext z
    simp only [rho2, Pi.div_apply]
  rwa [hfun]

private theorem contDiffOn_aF : ContDiffOn ℝ ⊤ aF (Set.Ioi 0) := by
  have hnum : ContDiffOn ℝ ⊤ (fun z : ℝ => 2 * z * (1 - z)) (Set.Ioi 0) :=
    (contDiffOn_const.mul contDiffOn_id).mul (contDiffOn_const.sub contDiffOn_id)
  have hden : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 + z) ^ 3) (Set.Ioi 0) :=
    (contDiffOn_const.add contDiffOn_id).pow 3
  have h := hnum.div hden (fun z hz => by
    have hz' : (0 : ℝ) < z := hz
    positivity)
  have hfun : aF = (fun z : ℝ => 2 * z * (1 - z)) / (fun z : ℝ => (1 + z) ^ 3) := by
    funext z
    simp only [aF, Pi.div_apply]
  rwa [hfun]

private theorem contDiffOn_bF : ContDiffOn ℝ ⊤ bF (Set.Ioi 0) := by
  have hnum : ContDiffOn ℝ ⊤ (fun z : ℝ => 2 * z) (Set.Ioi 0) :=
    contDiffOn_const.mul contDiffOn_id
  have hden : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi 0) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  have h := hnum.div hden (fun z hz => by
    have hz' : (0 : ℝ) < z := hz
    positivity)
  have hfun : bF = (fun z : ℝ => 2 * z) / (fun z : ℝ => (1 + z) ^ 2) := by
    funext z
    simp only [bF, Pi.div_apply]
  rwa [hfun]

private theorem contDiffOn_c2mF : ContDiffOn ℝ ⊤ c2mF (Set.Ioo 0 (π / 2)) := by
  have h : ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2)
      (Set.Ioo 0 (π / 2)) :=
    ((Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).sub
      ((Real.contDiff_sin.comp contDiff_id).pow 2)).contDiffOn
  have hfun : c2mF = fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2 := by
    funext θ
    simp only [c2mF, Work.Construction.c2m]
  rwa [hfun]

private theorem contDiffOn_sinsqF : ContDiffOn ℝ ⊤ sinsqF (Set.Ioo 0 (π / 2)) := by
  have h : ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.sin θ ^ 2) (Set.Ioo 0 (π / 2)) :=
    ((Real.contDiff_sin.comp contDiff_id).pow 2).contDiffOn
  have hfun : sinsqF = fun θ : ℝ => Real.sin θ ^ 2 := by
    funext θ
    simp only [sinsqF]
  rwa [hfun]

private theorem contDiffOn_oneF : ContDiffOn ℝ ⊤ oneF (Set.Ioo 0 (π / 2)) :=
  contDiffOn_const

/-! ## §4  The six pointwise bounds -/

/-- **Conjunct 1.**  The leading combination `E`. -/
private theorem piece1_bound {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    {μ β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    ∀ j i : ℕ, j + i ≤ 2 →
      |Work.Spaces.mixed j i (Ef μ β) z θ| ≤ 1120 * (1 + |μ|) * (z ^ 2 / (1 + z) ^ 2) := by
  intro j i hji
  have hj : j ≤ 2 := by omega
  have hi : i ≤ 2 := by omega
  have hθ : (z, θ) ∈ Q0 := ⟨hz, hθ0, hθ1⟩
  -- the separable closed form
  have hEqOn : Set.EqOn (Function.uncurry (Ef μ β))
      (Function.uncurry ((fun z θ => (4 * μ * rho1 z) * oneF θ)
        + (fun z θ => (β * (4 * β / 3 - 8) * rho2 z) * c2mF θ)
        + (fun z θ => (4 * β * rho2 z) * sinsqF θ))) Q0 := by
    intro p hp
    obtain ⟨z', θ'⟩ := p
    have hz' : (0 : ℝ) < z' := hp.1
    have hz1' : (1 : ℝ) + z' ≠ 0 := by positivity
    simp only [Function.uncurry, Ef, rho1, rho2, oneF, c2mF, sinsqF, Pi.add_apply]
    field_simp
    ring
  rw [mixed_congr_of_isOpen isOpen_Q0 hEqOn j i z θ hθ]
  -- additivity and separation
  have hcd1 : ContDiffOn ℝ ⊤
      (Function.uncurry (fun z θ => (4 * μ * rho1 z) * oneF θ)) Q0 :=
    contDiffOn_uncurry_sep ((contDiffOn_const (c := 4 * μ)).mul contDiffOn_rho1) contDiffOn_oneF
  have hcd2 : ContDiffOn ℝ ⊤
      (Function.uncurry (fun z θ => (β * (4 * β / 3 - 8) * rho2 z) * c2mF θ)) Q0 :=
    contDiffOn_uncurry_sep
      ((contDiffOn_const (c := β * (4 * β / 3 - 8))).mul contDiffOn_rho2) contDiffOn_c2mF
  have hcd3 : ContDiffOn ℝ ⊤
      (Function.uncurry (fun z θ => (4 * β * rho2 z) * sinsqF θ)) Q0 :=
    contDiffOn_uncurry_sep ((contDiffOn_const (c := 4 * β)).mul contDiffOn_rho2)
      contDiffOn_sinsqF
  have hcd12 : ContDiffOn ℝ ⊤
      (Function.uncurry ((fun z θ => (4 * μ * rho1 z) * oneF θ)
        + (fun z θ => (β * (4 * β / 3 - 8) * rho2 z) * c2mF θ))) Q0 :=
    hcd1.add hcd2
  rw [mixed_add isOpen_Q0 hcd12 hcd3 j i hθ, mixed_add isOpen_Q0 hcd1 hcd2 j i hθ]
  rw [mixed_sep j i (fun z => 4 * μ * rho1 z) oneF,
    mixed_sep j i (fun z => β * (4 * β / 3 - 8) * rho2 z) c2mF,
    mixed_sep j i (fun z => 4 * β * rho2 z) sinsqF]
  show |ZIter j (fun z => 4 * μ * rho1 z) z * TIter i oneF θ
      + ZIter j (fun z => β * (4 * β / 3 - 8) * rho2 z) z * TIter i c2mF θ
      + ZIter j (fun z => 4 * β * rho2 z) z * TIter i sinsqF θ|
      ≤ 1120 * (1 + |μ|) * (z ^ 2 / (1 + z) ^ 2)
  -- the three terms
  have hZ1 : |ZIter j (fun z => 4 * μ * rho1 z) z| ≤ 40 * |μ| * (z ^ 2 / (1 + z) ^ 2) := by
    have h1 : ZIter j (fun z => 4 * μ * rho1 z) z = 4 * μ * ZIter j rho1 z :=
      congrFun (ZIter_const_mul (4 * μ) rho1 j) z
    rw [h1, abs_mul]
    have h4 : |(4 : ℝ) * μ| = 4 * |μ| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    rw [h4]
    calc 4 * |μ| * |ZIter j rho1 z| ≤ 4 * |μ| * (10 * (z ^ 2 / (1 + z) ^ 2)) :=
          mul_le_mul_of_nonneg_left (ZIter_rho1_sq j hj hz) (by positivity)
      _ = 40 * |μ| * (z ^ 2 / (1 + z) ^ 2) := by ring
  have hZ2 : |ZIter j (fun z => β * (4 * β / 3 - 8) * rho2 z) z|
      ≤ 80 * β * (z ^ 2 / (1 + z) ^ 2) := by
    have h1 : ZIter j (fun z => β * (4 * β / 3 - 8) * rho2 z) z
        = β * (4 * β / 3 - 8) * ZIter j rho2 z :=
      congrFun (ZIter_const_mul (β * (4 * β / 3 - 8)) rho2 j) z
    rw [h1, abs_mul]
    have hcoef : |β * (4 * β / 3 - 8)| ≤ 8 * β := by
      rw [abs_mul, abs_of_nonneg hβ0.le]
      have hb : |(4 : ℝ) * β / 3 - 8| ≤ 8 := by
        rw [abs_le]
        constructor <;> linarith
      calc β * |(4 : ℝ) * β / 3 - 8| ≤ β * 8 := mul_le_mul_of_nonneg_left hb hβ0.le
        _ = 8 * β := by ring
    calc |β * (4 * β / 3 - 8)| * |ZIter j rho2 z|
          ≤ (8 * β) * (10 * (z ^ 2 / (1 + z) ^ 2)) :=
          mul_le_mul hcoef (ZIter_rho2_sq j hj hz) (abs_nonneg _) (by positivity)
      _ = 80 * β * (z ^ 2 / (1 + z) ^ 2) := by ring
  have hZ3 : |ZIter j (fun z => 4 * β * rho2 z) z| ≤ 40 * β * (z ^ 2 / (1 + z) ^ 2) := by
    have h1 : ZIter j (fun z => 4 * β * rho2 z) z = 4 * β * ZIter j rho2 z :=
      congrFun (ZIter_const_mul (4 * β) rho2 j) z
    rw [h1, abs_mul]
    have h4 : |(4 : ℝ) * β| = 4 * β := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_of_nonneg hβ0.le]
    rw [h4]
    calc 4 * β * |ZIter j rho2 z| ≤ 4 * β * (10 * (z ^ 2 / (1 + z) ^ 2)) :=
          mul_le_mul_of_nonneg_left (ZIter_rho2_sq j hj hz) (by positivity)
      _ = 40 * β * (z ^ 2 / (1 + z) ^ 2) := by ring
  have hb1 : |ZIter j (fun z => 4 * μ * rho1 z) z * TIter i oneF θ|
      ≤ 40 * |μ| * (z ^ 2 / (1 + z) ^ 2) := by
    rw [abs_mul]
    calc |ZIter j (fun z => 4 * μ * rho1 z) z| * |TIter i oneF θ|
          ≤ (40 * |μ| * (z ^ 2 / (1 + z) ^ 2)) * 1 :=
          mul_le_mul hZ1 (TIter_oneF_le i hi hθ0 hθ1) (abs_nonneg _) (by positivity)
      _ = 40 * |μ| * (z ^ 2 / (1 + z) ^ 2) := by ring
  have hb2 : |ZIter j (fun z => β * (4 * β / 3 - 8) * rho2 z) z * TIter i c2mF θ|
      ≤ 960 * β * (z ^ 2 / (1 + z) ^ 2) := by
    rw [abs_mul]
    calc |ZIter j (fun z => β * (4 * β / 3 - 8) * rho2 z) z| * |TIter i c2mF θ|
          ≤ (80 * β * (z ^ 2 / (1 + z) ^ 2)) * 12 :=
          mul_le_mul hZ2 (TIter_c2mF_le i hi hθ0 hθ1) (abs_nonneg _) (by positivity)
      _ = 960 * β * (z ^ 2 / (1 + z) ^ 2) := by ring
  have hb3 : |ZIter j (fun z => 4 * β * rho2 z) z * TIter i sinsqF θ|
      ≤ 160 * β * (z ^ 2 / (1 + z) ^ 2) := by
    rw [abs_mul]
    calc |ZIter j (fun z => 4 * β * rho2 z) z| * |TIter i sinsqF θ|
          ≤ (40 * β * (z ^ 2 / (1 + z) ^ 2)) * 4 :=
          mul_le_mul hZ3 (TIter_sinsqF_le i hi hθ0 hθ1) (abs_nonneg _) (by positivity)
      _ = 160 * β * (z ^ 2 / (1 + z) ^ 2) := by ring
  have hW : (0 : ℝ) ≤ z ^ 2 / (1 + z) ^ 2 := by positivity
  calc |ZIter j (fun z => 4 * μ * rho1 z) z * TIter i oneF θ
        + ZIter j (fun z => β * (4 * β / 3 - 8) * rho2 z) z * TIter i c2mF θ
        + ZIter j (fun z => 4 * β * rho2 z) z * TIter i sinsqF θ|
      ≤ |ZIter j (fun z => 4 * μ * rho1 z) z * TIter i oneF θ|
        + |ZIter j (fun z => β * (4 * β / 3 - 8) * rho2 z) z * TIter i c2mF θ|
        + |ZIter j (fun z => 4 * β * rho2 z) z * TIter i sinsqF θ| := by
        have h' := abs_add_le
          (ZIter j (fun z => 4 * μ * rho1 z) z * TIter i oneF θ
            + ZIter j (fun z => β * (4 * β / 3 - 8) * rho2 z) z * TIter i c2mF θ)
          (ZIter j (fun z => 4 * β * rho2 z) z * TIter i sinsqF θ)
        have h'' := abs_add_le (ZIter j (fun z => 4 * μ * rho1 z) z * TIter i oneF θ)
          (ZIter j (fun z => β * (4 * β / 3 - 8) * rho2 z) z * TIter i c2mF θ)
        linarith
    _ ≤ 40 * |μ| * (z ^ 2 / (1 + z) ^ 2) + 960 * β * (z ^ 2 / (1 + z) ^ 2)
        + 160 * β * (z ^ 2 / (1 + z) ^ 2) := add_le_add (add_le_add hb1 hb2) hb3
    _ ≤ 1120 * (1 + |μ|) * (z ^ 2 / (1 + z) ^ 2) := by
        have hA : (0 : ℝ) ≤ |μ| * (z ^ 2 / (1 + z) ^ 2) := mul_nonneg (abs_nonneg μ) hW
        have hB : (0 : ℝ) ≤ (1 - β) * (z ^ 2 / (1 + z) ^ 2) :=
          mul_nonneg (by linarith) hW
        nlinarith [hA, hB, hW]

/-- **Conjunct 2.**  The factor `a(z) = 2z(1-z)/(1+z)³`. -/
private theorem piece2_bound {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    ∀ j i : ℕ, j + i ≤ 2 →
      |Work.Spaces.mixed j i (fun z _ : ℝ => 2 * z * (1 - z) / (1 + z) ^ 3) z θ|
        ≤ 1120 * (z / (1 + z) ^ 2) := by
  intro j i hji
  have hj : j ≤ 2 := by omega
  have hi : i ≤ 2 := by omega
  have hθ : (z, θ) ∈ Q0 := ⟨hz, hθ0, hθ1⟩
  have hEqOn : Set.EqOn (Function.uncurry (fun z _ : ℝ => 2 * z * (1 - z) / (1 + z) ^ 3))
      (Function.uncurry (fun z θ => aF z * oneF θ)) Q0 := by
    intro p hp
    obtain ⟨z', θ'⟩ := p
    simp only [Function.uncurry, aF, oneF]
    ring
  rw [mixed_congr_of_isOpen isOpen_Q0 hEqOn j i z θ hθ]
  rw [mixed_sep j i aF oneF]
  show |ZIter j aF z * TIter i oneF θ| ≤ 1120 * (z / (1 + z) ^ 2)
  rw [abs_mul]
  calc |ZIter j aF z| * |TIter i oneF θ| ≤ (30 * (z / (1 + z) ^ 2)) * 1 :=
        mul_le_mul (ZIter_aF_le j hj hz) (TIter_oneF_le i hi hθ0 hθ1) (abs_nonneg _)
          (by positivity)
    _ ≤ 1120 * (z / (1 + z) ^ 2) := by
        have hW : (0 : ℝ) ≤ z / (1 + z) ^ 2 := by positivity
        nlinarith [hW]

/-- **Conjunct 3.**  The factor `b(z) = 2z/(1+z)²`. -/
private theorem piece3_bound {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    ∀ j i : ℕ, j + i ≤ 2 →
      |Work.Spaces.mixed j i (fun z _ : ℝ => 2 * z / (1 + z) ^ 2) z θ|
        ≤ 1120 * (z / (1 + z) ^ 2) := by
  intro j i hji
  have hj : j ≤ 2 := by omega
  have hi : i ≤ 2 := by omega
  have hθ : (z, θ) ∈ Q0 := ⟨hz, hθ0, hθ1⟩
  have hEqOn : Set.EqOn (Function.uncurry (fun z _ : ℝ => 2 * z / (1 + z) ^ 2))
      (Function.uncurry (fun z θ => bF z * oneF θ)) Q0 := by
    intro p hp
    obtain ⟨z', θ'⟩ := p
    simp only [Function.uncurry, bF, oneF]
    ring
  rw [mixed_congr_of_isOpen isOpen_Q0 hEqOn j i z θ hθ]
  rw [mixed_sep j i bF oneF]
  show |ZIter j bF z * TIter i oneF θ| ≤ 1120 * (z / (1 + z) ^ 2)
  rw [abs_mul]
  calc |ZIter j bF z| * |TIter i oneF θ| ≤ (10 * (z / (1 + z) ^ 2)) * 1 :=
        mul_le_mul (ZIter_bF_le j hj hz) (TIter_oneF_le i hi hθ0 hθ1) (abs_nonneg _)
          (by positivity)
    _ ≤ 1120 * (z / (1 + z) ^ 2) := by
        have hW : (0 : ℝ) ≤ z / (1 + z) ^ 2 := by positivity
        nlinarith [hW]

/-- **Conjunct 4.**  The factor `(2β/3)·c2m θ·b(z)`. -/
private theorem piece4_bound {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    {β : ℝ} (hβ0 : 0 < β) :
    ∀ j i : ℕ, j + i ≤ 2 →
      |Work.Spaces.mixed j i
          (fun z θ => (2 * β / 3) * Work.Construction.c2m θ * (2 * z / (1 + z) ^ 2)) z θ|
        ≤ 1120 * β * (z / (1 + z) ^ 2) := by
  intro j i hji
  have hj : j ≤ 2 := by omega
  have hi : i ≤ 2 := by omega
  have hθ : (z, θ) ∈ Q0 := ⟨hz, hθ0, hθ1⟩
  have hEqOn : Set.EqOn
      (Function.uncurry (fun z θ => (2 * β / 3) * Work.Construction.c2m θ * (2 * z / (1 + z) ^ 2)))
      (Function.uncurry (fun z θ => ((2 * β / 3) * bF z) * c2mF θ)) Q0 := by
    intro p hp
    obtain ⟨z', θ'⟩ := p
    simp only [Function.uncurry, bF, c2mF]
    ring
  rw [mixed_congr_of_isOpen isOpen_Q0 hEqOn j i z θ hθ]
  rw [mixed_sep j i (fun z => (2 * β / 3) * bF z) c2mF]
  show |ZIter j (fun z => (2 * β / 3) * bF z) z * TIter i c2mF θ|
      ≤ 1120 * β * (z / (1 + z) ^ 2)
  rw [abs_mul]
  have hZ : |ZIter j (fun z => (2 * β / 3) * bF z) z| ≤ 80 * β * (z / (1 + z) ^ 2) := by
    have h1 : ZIter j (fun z => (2 * β / 3) * bF z) z = (2 * β / 3) * ZIter j bF z :=
      congrFun (ZIter_const_mul (2 * β / 3) bF j) z
    rw [h1, abs_mul]
    have hc : |(2 * β / 3 : ℝ)| = 2 * β / 3 :=
      abs_of_nonneg (by positivity)
    rw [hc]
    calc 2 * β / 3 * |ZIter j bF z| ≤ 2 * β / 3 * (10 * (z / (1 + z) ^ 2)) :=
          mul_le_mul_of_nonneg_left (ZIter_bF_le j hj hz) (by positivity)
      _ = 20 * β / 3 * (z / (1 + z) ^ 2) := by ring
      _ ≤ 80 * β * (z / (1 + z) ^ 2) := by
          have hW : (0 : ℝ) ≤ z / (1 + z) ^ 2 := by positivity
          nlinarith [hW, hβ0]
  calc |ZIter j (fun z => (2 * β / 3) * bF z) z| * |TIter i c2mF θ|
        ≤ (80 * β * (z / (1 + z) ^ 2)) * 12 :=
        mul_le_mul hZ (TIter_c2mF_le i hi hθ0 hθ1) (abs_nonneg _) (by positivity)
    _ = 960 * β * (z / (1 + z) ^ 2) := by ring
    _ ≤ 1120 * β * (z / (1 + z) ^ 2) := by
        have hW : (0 : ℝ) ≤ z / (1 + z) ^ 2 := by positivity
        nlinarith [hW, hβ0]

/-- **Conjunct 5.**  The factor `c2m θ·(a-b)(z) - b(z)/β`. -/
private theorem piece5_bound {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    {β : ℝ} (hβ0 : 0 < β) :
    ∀ j i : ℕ, j + i ≤ 2 →
      |Work.Spaces.mixed j i
          (fun z θ => Work.Construction.c2m θ
              * (2 * z * (1 - z) / (1 + z) ^ 3 - 2 * z / (1 + z) ^ 2)
            - (1 / β) * (2 * z / (1 + z) ^ 2)) z θ|
        ≤ 1120 * (1 + 1 / β) * (z / (1 + z) ^ 2) := by
  intro j i hji
  have hj : j ≤ 2 := by omega
  have hi : i ≤ 2 := by omega
  have hθ : (z, θ) ∈ Q0 := ⟨hz, hθ0, hθ1⟩
  have hEqOn : Set.EqOn
      (Function.uncurry (fun z θ => Work.Construction.c2m θ
              * (2 * z * (1 - z) / (1 + z) ^ 3 - 2 * z / (1 + z) ^ 2)
            - (1 / β) * (2 * z / (1 + z) ^ 2)))
      (Function.uncurry ((fun z θ => (-4 * rho1 z) * c2mF θ)
        + (fun z θ => (-(1 / β) * bF z) * oneF θ))) Q0 := by
    intro p hp
    obtain ⟨z', θ'⟩ := p
    have hz' : (0 : ℝ) < z' := hp.1
    have hz1' : (1 : ℝ) + z' ≠ 0 := by positivity
    simp only [Function.uncurry, rho1, bF, c2mF, oneF, Pi.add_apply]
    field_simp
    ring
  rw [mixed_congr_of_isOpen isOpen_Q0 hEqOn j i z θ hθ]
  have hcd1 : ContDiffOn ℝ ⊤
      (Function.uncurry (fun z θ => (-4 * rho1 z) * c2mF θ)) Q0 :=
    contDiffOn_uncurry_sep
      ((contDiffOn_const (c := (-4 : ℝ))).mul contDiffOn_rho1) contDiffOn_c2mF
  have hcd2 : ContDiffOn ℝ ⊤
      (Function.uncurry (fun z θ => (-(1 / β) * bF z) * oneF θ)) Q0 :=
    contDiffOn_uncurry_sep
      ((contDiffOn_const (c := -(1 / β))).mul contDiffOn_bF) contDiffOn_oneF
  rw [mixed_add isOpen_Q0 hcd1 hcd2 j i hθ]
  rw [mixed_sep j i (fun z => -4 * rho1 z) c2mF,
    mixed_sep j i (fun z => -(1 / β) * bF z) oneF]
  show |ZIter j (fun z => -4 * rho1 z) z * TIter i c2mF θ
      + ZIter j (fun z => -(1 / β) * bF z) z * TIter i oneF θ|
      ≤ 1120 * (1 + 1 / β) * (z / (1 + z) ^ 2)
  have hZ1 : |ZIter j (fun z => -4 * rho1 z) z| ≤ 40 * (z / (1 + z) ^ 2) := by
    have h1 : ZIter j (fun z => -4 * rho1 z) z = -4 * ZIter j rho1 z :=
      congrFun (ZIter_const_mul (-4) rho1 j) z
    rw [h1, abs_mul]
    have h4 : |(-4 : ℝ)| = 4 := by norm_num
    rw [h4]
    calc 4 * |ZIter j rho1 z| ≤ 4 * (10 * (z / (1 + z) ^ 2)) :=
          mul_le_mul_of_nonneg_left (ZIter_rho1_lin j hj hz) (by norm_num)
      _ = 40 * (z / (1 + z) ^ 2) := by ring
  have hZ2 : |ZIter j (fun z => -(1 / β) * bF z) z| ≤ (1 / β) * 10 * (z / (1 + z) ^ 2) := by
    have h1 : ZIter j (fun z => -(1 / β) * bF z) z = -(1 / β) * ZIter j bF z :=
      congrFun (ZIter_const_mul (-(1 / β)) bF j) z
    rw [h1, abs_mul]
    have hc : |(-(1 / β) : ℝ)| = 1 / β := by
      rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / β)]
    rw [hc]
    calc 1 / β * |ZIter j bF z| ≤ 1 / β * (10 * (z / (1 + z) ^ 2)) :=
          mul_le_mul_of_nonneg_left (ZIter_bF_le j hj hz) (by positivity)
      _ = (1 / β) * 10 * (z / (1 + z) ^ 2) := by ring
  have hb1 : |ZIter j (fun z => -4 * rho1 z) z * TIter i c2mF θ| ≤ 480 * (z / (1 + z) ^ 2) := by
    rw [abs_mul]
    calc |ZIter j (fun z => -4 * rho1 z) z| * |TIter i c2mF θ|
          ≤ (40 * (z / (1 + z) ^ 2)) * 12 :=
          mul_le_mul hZ1 (TIter_c2mF_le i hi hθ0 hθ1) (abs_nonneg _) (by positivity)
      _ = 480 * (z / (1 + z) ^ 2) := by ring
  have hb2 : |ZIter j (fun z => -(1 / β) * bF z) z * TIter i oneF θ|
      ≤ (1 / β) * 10 * (z / (1 + z) ^ 2) := by
    rw [abs_mul]
    calc |ZIter j (fun z => -(1 / β) * bF z) z| * |TIter i oneF θ|
          ≤ ((1 / β) * 10 * (z / (1 + z) ^ 2)) * 1 :=
          mul_le_mul hZ2 (TIter_oneF_le i hi hθ0 hθ1) (abs_nonneg _) (by positivity)
      _ = (1 / β) * 10 * (z / (1 + z) ^ 2) := by ring
  have hW : (0 : ℝ) ≤ z / (1 + z) ^ 2 := by positivity
  calc |ZIter j (fun z => -4 * rho1 z) z * TIter i c2mF θ
        + ZIter j (fun z => -(1 / β) * bF z) z * TIter i oneF θ|
      ≤ |ZIter j (fun z => -4 * rho1 z) z * TIter i c2mF θ|
        + |ZIter j (fun z => -(1 / β) * bF z) z * TIter i oneF θ| := abs_add_le _ _
    _ ≤ 480 * (z / (1 + z) ^ 2) + (1 / β) * 10 * (z / (1 + z) ^ 2) := add_le_add hb1 hb2
    _ ≤ 1120 * (1 + 1 / β) * (z / (1 + z) ^ 2) := by
        have hB : (0 : ℝ) ≤ (1 / β) * (z / (1 + z) ^ 2) := by positivity
        nlinarith [hB, hW]

/-- **Conjunct 6.**  The factor `(β/3)·c2m θ·b(z) + sin²θ·b(z)`. -/
private theorem piece6_bound {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    {β : ℝ} (hβ0 : 0 < β) :
    ∀ j i : ℕ, j + i ≤ 2 →
      |Work.Spaces.mixed j i
          (fun z θ => ((2 * β / 3) * Work.Construction.c2m θ * (2 * z / (1 + z) ^ 2)) / 2
            + Real.sin θ ^ 2 * (2 * z / (1 + z) ^ 2)) z θ|
        ≤ 1120 * (1 + β) * (z / (1 + z) ^ 2) := by
  intro j i hji
  have hj : j ≤ 2 := by omega
  have hi : i ≤ 2 := by omega
  have hθ : (z, θ) ∈ Q0 := ⟨hz, hθ0, hθ1⟩
  have hEqOn : Set.EqOn
      (Function.uncurry (fun z θ => ((2 * β / 3) * Work.Construction.c2m θ
            * (2 * z / (1 + z) ^ 2)) / 2 + Real.sin θ ^ 2 * (2 * z / (1 + z) ^ 2)))
      (Function.uncurry ((fun z θ => ((β / 3) * bF z) * c2mF θ)
        + (fun z θ => bF z * sinsqF θ))) Q0 := by
    intro p hp
    obtain ⟨z', θ'⟩ := p
    simp only [Function.uncurry, bF, c2mF, sinsqF, Pi.add_apply]
    ring
  rw [mixed_congr_of_isOpen isOpen_Q0 hEqOn j i z θ hθ]
  have hcd1 : ContDiffOn ℝ ⊤
      (Function.uncurry (fun z θ => ((β / 3) * bF z) * c2mF θ)) Q0 :=
    contDiffOn_uncurry_sep
      ((contDiffOn_const (c := β / 3)).mul contDiffOn_bF) contDiffOn_c2mF
  have hcd2 : ContDiffOn ℝ ⊤ (Function.uncurry (fun z θ => bF z * sinsqF θ)) Q0 :=
    contDiffOn_uncurry_sep contDiffOn_bF contDiffOn_sinsqF
  rw [mixed_add isOpen_Q0 hcd1 hcd2 j i hθ]
  rw [mixed_sep j i (fun z => (β / 3) * bF z) c2mF, mixed_sep j i bF sinsqF]
  show |ZIter j (fun z => (β / 3) * bF z) z * TIter i c2mF θ
      + ZIter j bF z * TIter i sinsqF θ| ≤ 1120 * (1 + β) * (z / (1 + z) ^ 2)
  have hZ1 : |ZIter j (fun z => (β / 3) * bF z) z| ≤ (β / 3) * 10 * (z / (1 + z) ^ 2) := by
    have h1 : ZIter j (fun z => (β / 3) * bF z) z = (β / 3) * ZIter j bF z :=
      congrFun (ZIter_const_mul (β / 3) bF j) z
    rw [h1, abs_mul]
    have hc : |(β / 3 : ℝ)| = β / 3 := abs_of_nonneg (by positivity)
    rw [hc]
    calc β / 3 * |ZIter j bF z| ≤ β / 3 * (10 * (z / (1 + z) ^ 2)) :=
          mul_le_mul_of_nonneg_left (ZIter_bF_le j hj hz) (by positivity)
      _ = (β / 3) * 10 * (z / (1 + z) ^ 2) := by ring
  have hb1 : |ZIter j (fun z => (β / 3) * bF z) z * TIter i c2mF θ|
      ≤ 40 * β * (z / (1 + z) ^ 2) := by
    rw [abs_mul]
    calc |ZIter j (fun z => (β / 3) * bF z) z| * |TIter i c2mF θ|
          ≤ ((β / 3) * 10 * (z / (1 + z) ^ 2)) * 12 :=
          mul_le_mul hZ1 (TIter_c2mF_le i hi hθ0 hθ1) (abs_nonneg _) (by positivity)
      _ = 40 * β * (z / (1 + z) ^ 2) := by ring
  have hb2 : |ZIter j bF z * TIter i sinsqF θ| ≤ 40 * (z / (1 + z) ^ 2) := by
    rw [abs_mul]
    calc |ZIter j bF z| * |TIter i sinsqF θ| ≤ (10 * (z / (1 + z) ^ 2)) * 4 :=
          mul_le_mul (ZIter_bF_le j hj hz) (TIter_sinsqF_le i hi hθ0 hθ1) (abs_nonneg _)
            (by positivity)
      _ = 40 * (z / (1 + z) ^ 2) := by ring
  have hW : (0 : ℝ) ≤ z / (1 + z) ^ 2 := by positivity
  calc |ZIter j (fun z => (β / 3) * bF z) z * TIter i c2mF θ
        + ZIter j bF z * TIter i sinsqF θ|
      ≤ |ZIter j (fun z => (β / 3) * bF z) z * TIter i c2mF θ|
        + |ZIter j bF z * TIter i sinsqF θ| := abs_add_le _ _
    _ ≤ 40 * β * (z / (1 + z) ^ 2) + 40 * (z / (1 + z) ^ 2) := add_le_add hb1 hb2
    _ ≤ 1120 * (1 + β) * (z / (1 + z) ^ 2) := by nlinarith [hW, hβ0]

/-! ## §5  The theorem -/

/-- Pointwise `mixed`-jet bounds for the explicit rational/angular pieces of the forcing
decomposition: the "leading" combination `E` (which cancels at order `z`), and the explicit
factors `A1`, `A3`, `B1`, `α₁`, `α₂` against which the radial transforms `L₁₂(g)`, `𝔽K(g)` and
the perturbation slots are paired.  All bounds are for `z > 0`, `0 < θ < π/2`, `j + i ≤ 2`. -/
theorem explicit_piece_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ μ β : ℝ, 0 < β → β ≤ 1 →
      (∀ j i : ℕ, j + i ≤ 2 →
        |Work.Spaces.mixed j i (fun z θ => ((1 - μ) + Work.Construction.c2m θ * (2 * β / (1 + z)))
              * (2 * z * (1 - z) / (1 + z) ^ 3)
            + (-(3 / (1 + z)) + β * (2 * z / (1 + z) ^ 2) / 2)
              * ((2 * β / 3) * Work.Construction.c2m θ * (2 * z / (1 + z) ^ 2))
            + ((1 + μ) - 2 / (1 + z) + β * Real.sin θ ^ 2 * (2 * z / (1 + z) ^ 2))
              * (2 * z / (1 + z) ^ 2)) z θ| ≤ C * (1 + |μ|) * (z ^ 2 / (1 + z) ^ 2)) ∧
      (∀ j i : ℕ, j + i ≤ 2 →
        |Work.Spaces.mixed j i (fun z _ => 2 * z * (1 - z) / (1 + z) ^ 3) z θ|
          ≤ C * (z / (1 + z) ^ 2)) ∧
      (∀ j i : ℕ, j + i ≤ 2 →
        |Work.Spaces.mixed j i (fun z _ => 2 * z / (1 + z) ^ 2) z θ| ≤ C * (z / (1 + z) ^ 2)) ∧
      (∀ j i : ℕ, j + i ≤ 2 →
        |Work.Spaces.mixed j i (fun z θ => (2 * β / 3) * Work.Construction.c2m θ
            * (2 * z / (1 + z) ^ 2)) z θ| ≤ C * β * (z / (1 + z) ^ 2)) ∧
      (∀ j i : ℕ, j + i ≤ 2 →
        |Work.Spaces.mixed j i (fun z θ => Work.Construction.c2m θ
              * (2 * z * (1 - z) / (1 + z) ^ 3 - 2 * z / (1 + z) ^ 2)
            - (1 / β) * (2 * z / (1 + z) ^ 2)) z θ| ≤ C * (1 + 1 / β) * (z / (1 + z) ^ 2)) ∧
      (∀ j i : ℕ, j + i ≤ 2 →
        |Work.Spaces.mixed j i (fun z θ => ((2 * β / 3) * Work.Construction.c2m θ
              * (2 * z / (1 + z) ^ 2)) / 2
            + Real.sin θ ^ 2 * (2 * z / (1 + z) ^ 2)) z θ| ≤ C * (1 + β) * (z / (1 + z) ^ 2)) := by
  refine ⟨1120, by norm_num, ?_⟩
  intro z θ hz hθ0 hθ1 μ β hβ0 hβ1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j i hji
    show |Work.Spaces.mixed j i (Ef μ β) z θ|
        ≤ 1120 * (1 + |μ|) * (z ^ 2 / (1 + z) ^ 2)
    exact piece1_bound hz hθ0 hθ1 hβ0 hβ1 j i hji
  · intro j i hji
    exact piece2_bound hz hθ0 hθ1 j i hji
  · intro j i hji
    exact piece3_bound hz hθ0 hθ1 j i hji
  · intro j i hji
    exact piece4_bound hz hθ0 hθ1 hβ0 j i hji
  · intro j i hji
    exact piece5_bound hz hθ0 hθ1 hβ0 j i hji
  · intro j i hji
    exact piece6_bound hz hθ0 hθ1 hβ0 j i hji

end Work.FTS_RegExport.RXT.SysAux
