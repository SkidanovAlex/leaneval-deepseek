/-
# Row 19 of the open-quadrant design table — `|N₃^{**}|_{ℋ⁴} ≤ K α³`

The piece is `N₃^{**} = -2α·V(Φ̃_*)·D_zF_*` (`Work.FTS.Nonlin.N3ss`).  With

  `A := ((z+1)/z)·V(Φ̃_*)`,   `Z := α·Γ(θ)·(A·H₂)`,   `H₂(z) := 2z²(1-z)/(1+z)⁴`

one has the *exact* identity on the open quadrant

  `Z = c(α)·V(Φ̃_*)·D_zF_*`

because `D_zF_* = (α/c(α))·Γ(θ)·H(z)` with `H(z) = 2z(1-z)/(1+z)³` and
`H₂ = (z/(1+z))·H`.  The two pointwise families

* (η) `|(1+z)w(z)z^m ∂_z^m Z| ≤ Cη·α·Λ` (`Row19Prep.row19_eta_bound`),
* (γ) `|(1+z)w(z)z^l ∂_z^l ∂_θ^i Z| ≤ Cγ·α·Λ·Φ(θ)` (`Row19Prep.row19_gam_bound`),
  `Φ(θ) = (α + sin 2θ)·sin(2θ)^{α/5}`,

are exactly the hypotheses of `Work.FTS.NonlinRows.wtoHQ_of_pointwise_open`, which gives both
`HkMem α 4 Z` and `Xn α Z ≤ 10^10·W`, `W = C·α·Λ`, `Λ = |A|_{𝒲^{4,∞}}` (bounded by
`StarPkgo2.VzW`: `Λ ≤ max Cs 0·α`).  Since `Z = c(α)·(V·D_zF_*)` on the open quadrant and
`1/c(α) ≤ 10`, the two facts transfer to `V·D_zF_*` (`HkSq_congr_open`, `HkSq_const_mul`,
`HkMem_const_mul`, `HkMem_congr_Ioi`), and `N₃^{**} = -2α·(V·D_zF_*)` gives the row:
`Xn α N₃^{**} = 2α·Xn α (V·D_zF_*) ≤ 2α·10·10^10·C·(max Cs 0)·α² = K α³`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Nonlinear.Pieces.RNPV2.row19
import Submission.Work.FTS.Nonlinear.Open.Row19Prep.Defs
import Submission.Work.FTS.Nonlinear.Open.Row19Prep.H2bBound
import Submission.Work.FTS.Nonlinear.Open.Row19Prep.row19_eta_bound
import Submission.Work.FTS.Nonlinear.Open.Row19Prep.row19_gam_bound
import Submission.Work.FTS.NonlinRows.wtoHQ_of_pointwise_open
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.NonlinRows.smoothOpen_radA
import Submission.Work.FTS.Nonlinear.FstarPkg.DzFstar_W
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.LocData.HkSq_const_mul
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.Coercivity.HkMem_congr_Ioi
import Submission.Work.Spaces.c_bounds
import Submission.Work.FTS.Nonlinear.Open.Row23

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The vocabulary of the row -/

/-- `(z+1)/z` is `C^∞` on `(0,∞)`. -/
theorem contDiffOn_row19_zdiv : ∀ n : ℕ,
    ContDiffOn ℝ n (fun z : ℝ => (z + 1) / z) (Set.Ioi 0) := fun n =>
  (contDiffOn_id.add contDiffOn_const).div contDiffOn_id
    (fun z hz => ne_of_gt (by linarith [Set.mem_Ioi.mp hz]))

/-- `H₂(z) = 2z²(1-z)/(1+z)⁴` is `C^∞` on `(0,∞)`. -/
theorem contDiffOn_row19_H2b : ∀ n : ℕ,
    ContDiffOn ℝ n (fun z : ℝ => Row19Prep.H2b z) (Set.Ioi 0) := by
  intro n
  refine ContDiffOn.div (((contDiffOn_const (c := (2 : ℝ))).mul
    (contDiffOn_id.pow 2)).mul (contDiffOn_const.sub contDiffOn_id))
    ((contDiffOn_const.add contDiffOn_id).pow 4) ?_
  intro z hz
  have hz1 : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
  positivity

/-- The weighted star coefficient `A = ((z+1)/z)·V(Φ̃_*)` is `C^∞` on the open quadrant. -/
theorem smoothOpen_row19_A {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) :=
  (row23_smoothOpen_radial contDiffOn_row19_zdiv).mul
    (Work.FTS.NonlinRows.smoothOpen_Vop (Work.FTS.NonlinRows.smoothOpen_PhiTs hα hα1 hs))

/-- `Z = c(α)·V(Φ̃_*)·D_zF_*` on the open quadrant. -/
theorem row19_Z_eq_c {α : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ z θ : ℝ, 0 < z →
      Row19Prep.Zf α (fun z θ => (z + 1) / z
          * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) z θ
        = Work.Spaces.c α * (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ
            * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) := by
  intro z θ hz
  have hz1 : (-1 : ℝ) < z := by linarith
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  rw [Row19Prep.Zf_apply, Row19Prep.H2b,
    Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz hα hz1,
    Work.FTS.Nonlinear.FstarPkg.Hz]
  field_simp
  ring

/-! ## The row -/

theorem Row19 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N3ss α Φs) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3ss α Φs) ≤ K * (α ^ 3) := by
  obtain ⟨Cη, hCηpos, hη⟩ := Row19Prep.row19_eta_bound
  obtain ⟨Cγ, hCγpos, hγ⟩ := Row19Prep.row19_gam_bound
  obtain ⟨Cw, hCwpos, hwto⟩ := Work.FTS.NonlinRows.wtoHQ_of_pointwise_open
  refine ⟨200 * Cw * (Cη + Cγ + 1) * (max Cs 0 + 1) + 1, by positivity, ?_⟩
  intro α g Φs Φg hα hα1 hαα₂ hgal hs2 hell
  have hs : Work.FTS.VocabO.StarPkgo α Cs Φs := hs2.toStarPkgo
  -- the vocabulary
  set V : Fn := Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs with hV
  set G : Fn := Work.FTS.Nonlinear.Pieces.RNP.Gs α with hG
  set A : Fn := (fun z θ => (z + 1) / z * V z θ) with hA
  set Λ : ℝ := Work.Spaces.WlInf α 4 A with hΛ
  set C0 : ℝ := Cη + Cγ + 1 with hC0
  set W : ℝ := (10 * C0) * α * Λ with hW
  have hC0pos : 0 < C0 := by rw [hC0]; linarith
  have hAmem : Work.Spaces.WlInfMem α 4 A := hs2.VzW.1
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; exact Work.Spaces.WlInf_nonneg α 4 A hAmem
  have hAle : Λ ≤ max Cs 0 * α := by
    rw [hΛ, hA, hV]
    exact le_trans hs2.VzW.2 (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le)
  have hAsm : Work.FTS.EllipticEst.SmoothOpen A := by
    rw [hA, hV]
    exact smoothOpen_row19_A hα hα1 hs
  have hcpos : 0 < Work.Spaces.c α := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  have hc10 : (Work.Spaces.c α)⁻¹ ≤ 10 := by
    rw [inv_eq_one_div, div_le_iff₀ hcpos]
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  have hW0 : 0 ≤ W := by
    rw [hW]
    exact mul_nonneg (mul_nonneg (by positivity) hα.le) hΛ0
  -- smoothness of the product `Z`
  have hH2sm : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => Row19Prep.H2b z) :=
    row23_smoothOpen_radial contDiffOn_row19_H2b
  have hGamsm : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => α * Work.Spaces.Gam α θ) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul α (row23_smoothOpen_Gam α)
  have hsmZ : Work.FTS.EllipticEst.SmoothOpen (Row19Prep.Zf α A) := by
    show Work.FTS.EllipticEst.SmoothOpen (fun z θ => α * Work.Spaces.Gam α θ
      * (A z θ * Row19Prep.H2b z))
    exact (hGamsm.mul (hAsm.mul hH2sm)).congr
      (fun p _ => by simp only [Function.uncurry]; try ring)
  -- the two pointwise families
  have hηZ : ∀ (m : ℕ), m ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ m * Work.Spaces.pzIter m (Row19Prep.Zf α A) z θ|
        ≤ 200000 * W := by
    intro m hm z hz θ hθ
    have h := hη α Λ A hα hα1 hΛ0 le_rfl hAmem hAsm m hm z hz θ hθ
    have h1 : Cη * (α * Λ) ≤ 200000 * W := by
      rw [hW, hC0]
      nlinarith [hCηpos, hCγpos, hα, hΛ0]
    exact h.trans h1
  have hγZ : ∀ (i l : ℕ), 1 ≤ i → l + i ≤ 4 → ∀ z : ℝ, 0 < z →
      ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ l * Work.Spaces.pzIter l
          (Work.Spaces.DthIter i (Row19Prep.Zf α A)) z θ|
        ≤ 200000 * (W * Row19Prep.PhiA α θ) := by
    intro i l hi hli z hz θ hθ
    have h := hγ α Λ A hα hα1 hΛ0 le_rfl hAmem hAsm i l hi hli z hz θ hθ
    have hΦ0 : 0 ≤ Row19Prep.PhiA α θ := Row19Prep.PhiA_nonneg hα ⟨hθ.1.le, hθ.2.le⟩
    have h1 : Cγ * (α * Λ) * Row19Prep.PhiA α θ ≤ 200000 * (W * Row19Prep.PhiA α θ) := by
      rw [hW, hC0]
      have : Cγ * (α * Λ) ≤ 200000 * (10 * (Cη + Cγ + 1) * α * Λ) := by
        nlinarith [hCηpos, hCγpos, hα, hΛ0]
      calc Cγ * (α * Λ) * Row19Prep.PhiA α θ
          ≤ (200000 * (10 * (Cη + Cγ + 1) * α * Λ)) * Row19Prep.PhiA α θ :=
            mul_le_mul_of_nonneg_right this hΦ0
        _ = 200000 * (10 * (Cη + Cγ + 1) * α * Λ * Row19Prep.PhiA α θ) := by ring
    exact h.trans h1
  -- `wtoHQ_of_pointwise_open` applied to `Z`
  have hmain := hwto α (Row19Prep.Zf α A) W hα hα1 hW0 hsmZ hηZ hγZ
  -- transfer along the open quadrant: `Z = c(α)·(V·D_zF_*)`
  have hZeq : ∀ z θ : ℝ, 0 < z → Row19Prep.Zf α A z θ
      = Work.Spaces.c α * (V z θ * G z θ) := by
    intro z θ hz
    rw [hA, hV, hG]
    exact row19_Z_eq_c hα hα1 z θ hz
  have hmemVG : Work.Spaces.HkMem α 4 (fun z θ => V z θ * G z θ) := by
    have h1 : Work.Spaces.HkMem α 4
        (fun z θ => (Work.Spaces.c α)⁻¹ * Row19Prep.Zf α A z θ) :=
      Work.FTS.LocData.HkMem_const_mul α 4 (Work.Spaces.c α)⁻¹ hmain.1
    refine Work.Coercivity.HkMem_congr_Ioi α 4 h1 fun z hz θ hθ => ?_
    rw [hZeq z θ hz]
    field_simp
  have hsqVG : Work.Spaces.HkSq α 4 (fun z θ => V z θ * G z θ)
      = ((Work.Spaces.c α)⁻¹) ^ 2 * Work.Spaces.HkSq α 4 (Row19Prep.Zf α A) := by
    rw [Work.FTS.EllipticEst.HkSq_congr_open α 4
      (f := fun z θ => V z θ * G z θ)
      (g := fun z θ => (Work.Spaces.c α)⁻¹ * Row19Prep.Zf α A z θ) (fun z θ hz _ _ => ?_),
      Work.FTS.LocData.HkSq_const_mul α 4 (Work.Spaces.c α)⁻¹ hmain.1]
    rw [hZeq z θ hz]
    field_simp
  have hXnVG : Work.FTS.Nonlin.Xn α (fun z θ => V z θ * G z θ)
      ≤ (Work.Spaces.c α)⁻¹ * (Cw * W) := by
    have h1 : Work.FTS.Nonlin.Xn α (fun z θ => V z θ * G z θ)
        = (Work.Spaces.c α)⁻¹ * Work.FTS.Nonlin.Xn α (Row19Prep.Zf α A) := by
      simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, hsqVG]
      rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ ((Work.Spaces.c α)⁻¹) ^ 2),
        Real.sqrt_sq (by positivity : (0:ℝ) ≤ (Work.Spaces.c α)⁻¹)]
    rw [h1]
    exact mul_le_mul_of_nonneg_left hmain.2 (by positivity)
  -- the conclusion
  have hN3 : Work.FTS.Nonlin.N3ss α Φs = fun z θ => (-2 * α) * (V z θ * G z θ) := by
    funext z θ
    rw [hV, hG]
    simp only [Work.FTS.Nonlin.N3ss, Work.FTS.Nonlinear.Pieces.RNP.Vs,
      Work.FTS.Nonlinear.Pieces.RNP.Gs]
    ring
  constructor
  · rw [hN3]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (-2 * α) hmemVG
  · have habs : |(-2 : ℝ) * α| = 2 * α := by
      rw [abs_of_nonpos (by linarith : (-2 : ℝ) * α ≤ 0)]
      ring
    rw [hN3, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α (-2 * α), habs]
    calc 2 * α * Work.FTS.Nonlin.Xn α (fun z θ => V z θ * G z θ)
        ≤ 2 * α * ((Work.Spaces.c α)⁻¹ * (Cw * W)) :=
          mul_le_mul_of_nonneg_left hXnVG (by linarith)
      _ = 2 * (Work.Spaces.c α)⁻¹ * (Cw * ((10 * C0) * α * Λ)) * α := by rw [hW]; ring
      _ ≤ 2 * 10 * (Cw * ((10 * C0) * α * Λ)) * α := by
          have h2 : 0 ≤ α * (Cw * ((10 * C0) * α * Λ)) := by positivity
          nlinarith [hc10, h2]
      _ = 200 * Cw * C0 * α ^ 2 * Λ := by ring
      _ ≤ 200 * Cw * C0 * α ^ 2 * (max Cs 0 * α) :=
          mul_le_mul_of_nonneg_left hAle (by positivity)
      _ = 200 * Cw * C0 * max Cs 0 * α ^ 3 := by ring
      _ ≤ (200 * Cw * (Cη + Cγ + 1) * (max Cs 0 + 1) + 1) * α ^ 3 := by
          rw [hC0]
          have h6 : (0:ℝ) ≤ α ^ 3 := by positivity
          have h4 : max Cs 0 ≤ max Cs 0 + 1 := by linarith
          calc 200 * Cw * (Cη + Cγ + 1) * max Cs 0 * α ^ 3
              ≤ 200 * Cw * (Cη + Cγ + 1) * (max Cs 0 + 1) * α ^ 3 :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left h4 (by positivity)) h6
            _ ≤ (200 * Cw * (Cη + Cγ + 1) * (max Cs 0 + 1) + 1) * α ^ 3 :=
                mul_le_mul_of_nonneg_right (by linarith) h6

end Work.FTS.Nonlinear.Open
