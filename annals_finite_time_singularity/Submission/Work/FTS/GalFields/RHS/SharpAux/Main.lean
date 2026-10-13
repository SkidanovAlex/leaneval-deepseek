/-
# `SharpAux/Main` — the assembly `sharp_N_diff_asm`

Reduces `sharp_N_diff` to the two term-bound bundles (`SharpAux/WlInfTermsBound`,
`SharpAux/HonestTermsBound`) and the master identity (`SharpAux/Identity`).  Nothing here is
`sorry`-free-critical: the file contains no `sorry`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.GalFields.RHS.SharpAux.Assembly

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS.Sharp

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-- **The twenty term bounds, assembled into `sharp_N_diff`.** -/
theorem sharp_N_diff_asm {α α₂ Ci Ct Ce Cs : ℝ}
    {IP : ℝ → Fn → Fn → ℝ} {Φs : Fn} {EllSol : Fn → Fn}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ g : Fn, Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g))
    (hEllSub : ∀ g g' : Fn,
      EllSol (fun z θ => g z θ - g' z θ) = fun z θ => EllSol g z θ - EllSol g' z θ)
    (hα : 0 < α) (hαα₂ : α ≤ α₂)
    (hW : ∃ K : ℝ, 0 < K ∧ ∀ {g g' h : Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.GalClass α g' →
      Work.FTS.Nonlin.GalClass α h → α ≤ 1 →
      (Work.FTS.EllipticEst.SmoothOpen (TRA α Φs h) ∧
        Work.Spaces.HkMem α 4 (TRA α Φs h) ∧
        Work.FTS.Nonlin.Xn α (TRA α Φs h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (TUA α Φs h) ∧
        Work.Spaces.HkMem α 4 (TUA α Φs h) ∧
        Work.FTS.Nonlin.Xn α (TUA α Φs h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (TVA α Φs h) ∧
        Work.Spaces.HkMem α 4 (TVA α Φs h) ∧
        Work.FTS.Nonlin.Xn α (TVA α Φs h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (TRC α EllSol h) ∧
        Work.Spaces.HkMem α 4 (TRC α EllSol h) ∧
        Work.FTS.Nonlin.Xn α (TRC α EllSol h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (TUC α EllSol h) ∧
        Work.Spaces.HkMem α 4 (TUC α EllSol h) ∧
        Work.FTS.Nonlin.Xn α (TUC α EllSol h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (TVC α EllSol h) ∧
        Work.Spaces.HkMem α 4 (TVC α EllSol h) ∧
        Work.FTS.Nonlin.Xn α (TVC α EllSol h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (TDA α h) ∧
        Work.Spaces.HkMem α 4 (TDA α h) ∧
        Work.FTS.Nonlin.Xn α (TDA α h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (TDC α h) ∧
        Work.Spaces.HkMem α 4 (TDC α h) ∧
        Work.FTS.Nonlin.Xn α (TDC α h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (TEA α h) ∧
        Work.Spaces.HkMem α 4 (TEA α h) ∧
        Work.FTS.Nonlin.Xn α (TEA α h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (TEC α h) ∧
        Work.Spaces.HkMem α 4 (TEC α h) ∧
        Work.FTS.Nonlin.Xn α (TEC α h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h))
    (hH : ∃ K : ℝ, 0 < K ∧ ∀ {g g' h : Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.GalClass α g' →
      Work.FTS.Nonlin.GalClass α h → α ≤ 1 →
      (Work.FTS.EllipticEst.SmoothOpen (TRB α EllSol g' h) ∧
        Work.Spaces.HkMem α 4 (TRB α EllSol g' h) ∧
        Work.FTS.Nonlin.Xn α (TRB α EllSol g' h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (TUB α EllSol g' h) ∧
        Work.Spaces.HkMem α 4 (TUB α EllSol g' h) ∧
        Work.FTS.Nonlin.Xn α (TUB α EllSol g' h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (TVB α EllSol g' h) ∧
        Work.Spaces.HkMem α 4 (TVB α EllSol g' h) ∧
        Work.FTS.Nonlin.Xn α (TVB α EllSol g' h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (TDB α g' h) ∧
        Work.Spaces.HkMem α 4 (TDB α g' h) ∧
        Work.FTS.Nonlin.Xn α (TDB α g' h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (TEB α g' h) ∧
        Work.Spaces.HkMem α 4 (TEB α g' h) ∧
        Work.FTS.Nonlin.Xn α (TEB α g' h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (TRD α EllSol g h) ∧
        Work.Spaces.HkMem α 4 (TRD α EllSol g h) ∧
        Work.FTS.Nonlin.Xn α (TRD α EllSol g h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (TUD α EllSol g h) ∧
        Work.Spaces.HkMem α 4 (TUD α EllSol g h) ∧
        Work.FTS.Nonlin.Xn α (TUD α EllSol g h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (TVD α EllSol g h) ∧
        Work.Spaces.HkMem α 4 (TVD α EllSol g h) ∧
        Work.FTS.Nonlin.Xn α (TVD α EllSol g h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (TDD α g h) ∧
        Work.Spaces.HkMem α 4 (TDD α g h) ∧
        Work.FTS.Nonlin.Xn α (TDD α g h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (TED α g h) ∧
        Work.Spaces.HkMem α 4 (TED α g h) ∧
        Work.FTS.Nonlin.Xn α (TED α g h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h)) :
    ∃ K : ℝ, 0 < K ∧ ∀ g g' h : Fn,
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.GalClass α g' →
      Work.FTS.Nonlin.GalClass α h →
      (∀ z θ, h z θ = g z θ - g' z θ) → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
          Work.Construction.N α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + EllSol g z θ) z θ
            - Work.Construction.N α (Work.Construction.Ftot α g')
              (fun z θ => Φs z θ + EllSol g' z θ) z θ) ∧
      Work.Spaces.HkMem α 4 (fun z θ =>
          Work.Construction.N α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + EllSol g z θ) z θ
            - Work.Construction.N α (Work.Construction.Ftot α g')
              (fun z θ => Φs z θ + EllSol g' z θ) z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.Construction.N α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + EllSol g z θ) z θ
            - Work.Construction.N α (Work.Construction.Ftot α g')
              (fun z θ => Φs z θ + EllSol g' z θ) z θ)
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h ∧
      |Work.Construction.L12
          (Work.Construction.N α (Work.Construction.Ftot α g)
            (fun z θ => Φs z θ + EllSol g z θ)) 0
        - Work.Construction.L12
          (Work.Construction.N α (Work.Construction.Ftot α g')
            (fun z θ => Φs z θ + EllSol g' z θ)) 0|
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h := by
  obtain ⟨KW, hKWpos, hKW⟩ := hW
  obtain ⟨KH, hKHpos, hKH⟩ := hH
  set B : ℝ := max KW KH + 1 with hBdef
  set K0 : ℝ := 2 ^ (20 : ℕ) * 20 * B + 1 with hK0def
  set K : ℝ := K0 * (max 1 Ci + 1) + 1 with hKdef
  have hBpos : 0 < B := by
    rw [hBdef]
    nlinarith [hKWpos, le_max_left KW KH]
  have hBnn : 0 ≤ B := le_of_lt hBpos
  have hK0pos : 0 < K0 := by
    rw [hK0def]
    have h0 : (0 : ℝ) ≤ 2 ^ (20 : ℕ) * 20 * B := by positivity
    linarith
  have hmax1 : (1 : ℝ) ≤ max 1 Ci + 1 := by
    have := le_max_left (1 : ℝ) Ci
    linarith
  have hKpos : 0 < K := by
    rw [hKdef]
    nlinarith [hK0pos, hmax1]
  have hK0K : K0 ≤ K := by
    rw [hKdef]
    nlinarith [hK0pos, hmax1]
  have hCiK0K : Ci * K0 ≤ K := by
    rw [hKdef]
    have h1 : Ci ≤ max 1 Ci := le_max_right (1 : ℝ) Ci
    have h3 : (0 : ℝ) ≤ Ci := hN.pos.1.le
    nlinarith [hK0pos, hmax1, h1, h3]
  refine ⟨K, hKpos, ?_⟩
  intro g g' h hg hg' hh hh_eq hα1
  -- ### basic nonnegativity
  have hYnn : 0 ≤ Work.FTS.GalFields.Xn5 α g := Work.Spaces.HkNorm_nonneg α 5 g
  have hY'nn : 0 ≤ Work.FTS.GalFields.Xn5 α g' := Work.Spaces.HkNorm_nonneg α 5 g'
  have hYhnn : 0 ≤ Work.FTS.GalFields.Xn5 α h := Work.Spaces.HkNorm_nonneg α 5 h
  have h1YY : 0 ≤ 1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g' := by linarith
  have hX0 : 0 ≤ (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
      * Work.FTS.GalFields.Xn5 α h := mul_nonneg h1YY hYhnn
  have hBW : KW ≤ B := by
    rw [hBdef]
    exact le_trans (le_max_left _ _) (le_add_of_nonneg_right zero_le_one)
  have hBH : KH ≤ B := by
    rw [hBdef]
    exact le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one)
  -- ### the twenty term bounds
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10⟩ := hKW hg hg' hh hα1
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := hKH hg hg' hh hα1
  have hb1 : Work.FTS.Nonlin.Xn α (TRA α Φs h)
      ≤ B * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
    le_trans w1.2.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBW h1YY) hYhnn)
  have hb2 : Work.FTS.Nonlin.Xn α (TRB α EllSol g' h)
      ≤ B * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
    le_trans v1.2.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBH h1YY) hYhnn)
  have hb3 : Work.FTS.Nonlin.Xn α (TRC α EllSol h)
      ≤ B * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
    le_trans w4.2.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBW h1YY) hYhnn)
  have hb4 : Work.FTS.Nonlin.Xn α (TRD α EllSol g h)
      ≤ B * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
    le_trans v6.2.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBH h1YY) hYhnn)
  have hb5 : Work.FTS.Nonlin.Xn α (TUA α Φs h)
      ≤ B * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
    le_trans w2.2.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBW h1YY) hYhnn)
  have hb6 : Work.FTS.Nonlin.Xn α (TUB α EllSol g' h)
      ≤ B * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
    le_trans v2.2.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBH h1YY) hYhnn)
  have hb7 : Work.FTS.Nonlin.Xn α (TUC α EllSol h)
      ≤ B * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
    le_trans w5.2.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBW h1YY) hYhnn)
  have hb8 : Work.FTS.Nonlin.Xn α (TUD α EllSol g h)
      ≤ B * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
    le_trans v7.2.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBH h1YY) hYhnn)
  have hb9 : Work.FTS.Nonlin.Xn α (TVA α Φs h)
      ≤ B * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
    le_trans w3.2.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBW h1YY) hYhnn)
  have hb10 : Work.FTS.Nonlin.Xn α (TVB α EllSol g' h)
      ≤ B * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
    le_trans v3.2.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBH h1YY) hYhnn)
  have hb11 : Work.FTS.Nonlin.Xn α (TVC α EllSol h)
      ≤ B * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
    le_trans w6.2.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBW h1YY) hYhnn)
  have hb12 : Work.FTS.Nonlin.Xn α (TVD α EllSol g h)
      ≤ B * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
    le_trans v8.2.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBH h1YY) hYhnn)
  have hb13 : Work.FTS.Nonlin.Xn α (TDA α h)
      ≤ B * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
    le_trans w7.2.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBW h1YY) hYhnn)
  have hb14 : Work.FTS.Nonlin.Xn α (TDB α g' h)
      ≤ B * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
    le_trans v4.2.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBH h1YY) hYhnn)
  have hb15 : Work.FTS.Nonlin.Xn α (TDC α h)
      ≤ B * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
    le_trans w8.2.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBW h1YY) hYhnn)
  have hb16 : Work.FTS.Nonlin.Xn α (TDD α g h)
      ≤ B * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
    le_trans v9.2.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBH h1YY) hYhnn)
  have hb17 : Work.FTS.Nonlin.Xn α (TEA α h)
      ≤ B * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
    le_trans w9.2.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBW h1YY) hYhnn)
  have hb18 : Work.FTS.Nonlin.Xn α (TEB α g' h)
      ≤ B * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
    le_trans v5.2.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBH h1YY) hYhnn)
  have hb19 : Work.FTS.Nonlin.Xn α (TEC α h)
      ≤ B * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
    le_trans w10.2.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBW h1YY) hYhnn)
  have hb20 : Work.FTS.Nonlin.Xn α (TED α g h)
      ≤ B * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
    le_trans v10.2.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBH h1YY) hYhnn)
  -- ### the list facts
  have hSlist : ∀ f ∈ termList α Φs EllSol g g' h, Work.FTS.EllipticEst.SmoothOpen f := by
    intro f hf
    simp only [termList, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact w1.1
    · exact v1.1
    · exact w4.1
    · exact v6.1
    · exact w2.1
    · exact v2.1
    · exact w5.1
    · exact v7.1
    · exact w3.1
    · exact v3.1
    · exact w6.1
    · exact v8.1
    · exact w7.1
    · exact v4.1
    · exact w8.1
    · exact v9.1
    · exact w9.1
    · exact v5.1
    · exact w10.1
    · exact v10.1
  have hMlist : ∀ f ∈ termList α Φs EllSol g g' h, Work.Spaces.HkMem α 4 f := by
    intro f hf
    simp only [termList, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact w1.2.1
    · exact v1.2.1
    · exact w4.2.1
    · exact v6.2.1
    · exact w2.2.1
    · exact v2.2.1
    · exact w5.2.1
    · exact v7.2.1
    · exact w3.2.1
    · exact v3.2.1
    · exact w6.2.1
    · exact v8.2.1
    · exact w7.2.1
    · exact v4.2.1
    · exact w8.2.1
    · exact v9.2.1
    · exact w9.2.1
    · exact v5.2.1
    · exact w10.2.1
    · exact v10.2.1
  -- ### the identity and the norm bound
  have hagree : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (fun z θ =>
          Work.Construction.N α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + EllSol g z θ) z θ
            - Work.Construction.N α (Work.Construction.Ftot α g')
              (fun z θ => Φs z θ + EllSol g' z θ) z θ) z θ
        = (termList α Φs EllSol g g' h).foldr (fun f acc => f + acc) (0 : Fn) z θ := by
    intro z θ hz hθ1 hθ2
    have hq : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ1, hθ2⟩
    simp only [N_diff_eq_sum hN hstar hell hEllSub hα hαα₂ hg hg' hh hh_eq hα1 z θ hq,
      termList_foldr α Φs EllSol g g' h]
  have hGSm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + EllSol g z θ) z θ
        - Work.Construction.N α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ) z θ) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hNsm, -⟩ :=
      Work.FTS.GalFields.RHS.smoothOpen_atoms_of_gal hα hα1 hg
        (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hg.reg.1) hstar.smooth
        (hell g hg).smooth (hell g hg) hstar
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hNsm', -⟩ :=
      Work.FTS.GalFields.RHS.smoothOpen_atoms_of_gal hα hα1 hg'
        (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hg'.reg.1) hstar.smooth
        (hell g' hg').smooth (hell g' hg') hstar
    exact Work.FTS.EllipticEst.smoothOpen_sub hNsm hNsm'
  have hGmem : Work.Spaces.HkMem α 4 (fun z θ =>
      Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + EllSol g z θ) z θ
        - Work.Construction.N α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ) z θ) := by
    have hf := HkMem_listFoldr (α := α) (termList α Φs EllSol g g' h) hSlist hMlist
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hf ?_
    intro z hz θ hθ
    exact (hagree z θ hz hθ.1 hθ.2).symm
  have hSq : Work.Spaces.HkSq α 4 (fun z θ =>
      Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + EllSol g z θ) z θ
        - Work.Construction.N α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ) z θ)
      = Work.Spaces.HkSq α 4 ((termList α Φs EllSol g g' h).foldr
          (fun f acc => f + acc) (0 : Fn)) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 4 (fun z θ hz hθ1 hθ2 => hagree z θ hz hθ1 hθ2)
  have hsumle : (termList α Φs EllSol g g' h).foldr
      (fun f acc => Work.FTS.Nonlin.Xn α f + acc) 0
      ≤ 20 * (B * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h) := by
    simp only [termList, List.foldr_cons, List.foldr_nil]
    linarith [hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10,
      hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19, hb20]
  have hfoldle := HkNorm_listFoldr_le hα (termList α Φs EllSol g g' h) hSlist hMlist
  rw [termList_length α Φs EllSol g g' h] at hfoldle
  have hXnD0 : Work.FTS.Nonlin.Xn α (fun z θ =>
      Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + EllSol g z θ) z θ
        - Work.Construction.N α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ) z θ)
      ≤ K0 * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h := by
    have hXn1 : Work.FTS.Nonlin.Xn α (fun z θ =>
        Work.Construction.N α (Work.Construction.Ftot α g)
            (fun z θ => Φs z θ + EllSol g z θ) z θ
          - Work.Construction.N α (Work.Construction.Ftot α g')
            (fun z θ => Φs z θ + EllSol g' z θ) z θ)
        = Work.FTS.Nonlin.Xn α ((termList α Φs EllSol g g' h).foldr
            (fun f acc => f + acc) (0 : Fn)) := by
      show Work.Spaces.HkNorm α 4 _ = Work.Spaces.HkNorm α 4 _
      simp only [Work.Spaces.HkNorm, hSq]
    rw [hXn1]
    have h2 : Work.FTS.Nonlin.Xn α ((termList α Φs EllSol g g' h).foldr
        (fun f acc => f + acc) (0 : Fn))
        ≤ 2 ^ (20 : ℕ) * (20 * (B * (1 + Work.FTS.GalFields.Xn5 α g
            + Work.FTS.GalFields.Xn5 α g') * Work.FTS.GalFields.Xn5 α h)) :=
      le_trans hfoldle (mul_le_mul_of_nonneg_left hsumle (by positivity))
    have hBB : 2 ^ (20 : ℕ) * 20 * B ≤ K0 := by
      rw [hK0def]
      linarith
    refine le_trans h2 ?_
    calc 2 ^ (20 : ℕ) * (20 * (B * (1 + Work.FTS.GalFields.Xn5 α g
            + Work.FTS.GalFields.Xn5 α g') * Work.FTS.GalFields.Xn5 α h))
        = (2 ^ (20 : ℕ) * 20 * B)
            * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by ring
      _ ≤ K0 * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := mul_le_mul_of_nonneg_right hBB hX0
      _ = K0 * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h := by ring
  have hXnD : Work.FTS.Nonlin.Xn α (fun z θ =>
      Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + EllSol g z θ) z θ
        - Work.Construction.N α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ) z θ)
      ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
    le_trans hXnD0 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK0K h1YY) hYhnn)
  -- ### the `L₁₂`-clause
  have hDq : Work.FTS.VocabO.HQo α 4 (fun z θ =>
      Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + EllSol g z θ) z θ
        - Work.Construction.N α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ) z θ) := ⟨hGSm, hGmem⟩
  have hl12D : |Work.Construction.L12 (fun z θ =>
      Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + EllSol g z θ) z θ
        - Work.Construction.N α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ) z θ) 0|
      ≤ Ci * Work.FTS.Nonlin.Xn α (fun z θ =>
      Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + EllSol g z θ) z θ
        - Work.Construction.N α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ) z θ) :=
    hN.l12zero α ⟨hα, hαα₂⟩ _ hDq
  have hkNg : Work.Spaces.HkMem α 4 (Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + EllSol g z θ)) :=
    (Work.FTS.Nonlinear.Open.PiecesHkOpen IP hN hE hα hα1 hαα₂ hg hstar (hell g hg)).pN
  have hkNg' : Work.Spaces.HkMem α 4 (Work.Construction.N α (Work.Construction.Ftot α g')
      (fun z θ => Φs z θ + EllSol g' z θ)) :=
    (Work.FTS.Nonlinear.Open.PiecesHkOpen IP hN hE hα hα1 hαα₂ hg' hstar (hell g' hg')).pN
  have hNSm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.N α
      (Work.Construction.Ftot α g) (fun z θ => Φs z θ + EllSol g z θ)) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hNsm, -⟩ :=
      Work.FTS.GalFields.RHS.smoothOpen_atoms_of_gal hα hα1 hg
        (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hg.reg.1) hstar.smooth
        (hell g hg).smooth (hell g hg) hstar
    exact hNsm
  have hNSm' : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.N α
      (Work.Construction.Ftot α g') (fun z θ => Φs z θ + EllSol g' z θ)) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hNsm, -⟩ :=
      Work.FTS.GalFields.RHS.smoothOpen_atoms_of_gal hα hα1 hg'
        (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hg'.reg.1) hstar.smooth
        (hell g' hg').smooth (hell g' hg') hstar
    exact hNsm
  have hL12neg : Work.Construction.L12 (fun z θ => -(Work.Construction.N α
      (Work.Construction.Ftot α g') (fun z θ => Φs z θ + EllSol g' z θ) z θ)) 0
      = - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g')
        (fun z θ => Φs z θ + EllSol g' z θ)) 0 := by
    rw [show (fun z θ => -(Work.Construction.N α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ) z θ))
        = (fun z θ => (-1) * (Work.Construction.N α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ) z θ)) from by funext z θ; ring]
    rw [Work.FTS.GalBasis.L12_const_mul]
    ring
  have hL12add : Work.Construction.L12 (fun z θ =>
        Work.Construction.N α (Work.Construction.Ftot α g)
            (fun z θ => Φs z θ + EllSol g z θ) z θ
          + (-1) * (Work.Construction.N α (Work.Construction.Ftot α g')
            (fun z θ => Φs z θ + EllSol g' z θ) z θ)) 0
      = Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + EllSol g z θ)) 0
        - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ)) 0 := by
    rw [Work.FTS.GalBasis.cc.L12_add_of_HkMem hNSm
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-1) hNSm') hkNg
      (Work.FTS.LocData.HkMem_const_mul α 4 (-1) hkNg')]
    rw [show (fun z θ => (-1) * Work.Construction.N α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ) z θ)
        = (fun z θ => -(Work.Construction.N α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ) z θ)) from by funext z θ; ring]
    rw [hL12neg]
    ring
  have hkey : Work.Construction.L12 (fun z θ =>
      Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + EllSol g z θ) z θ
        - Work.Construction.N α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ) z θ) 0
      = Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + EllSol g z θ)) 0
        - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g')
          (fun z θ => Φs z θ + EllSol g' z θ)) 0 := by
    rw [← Work.FTS.GalBasis.L12_congr_all (a := fun z θ =>
          Work.Construction.N α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + EllSol g z θ) z θ
            + (-1) * (Work.Construction.N α (Work.Construction.Ftot α g')
              (fun z θ => Φs z θ + EllSol g' z θ) z θ))
        (b := fun z θ =>
          Work.Construction.N α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + EllSol g z θ) z θ
            - Work.Construction.N α (Work.Construction.Ftot α g')
              (fun z θ => Φs z θ + EllSol g' z θ) z θ)
        (fun z θ => by ring) 0]
    exact hL12add
  have hL12b : |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + EllSol g z θ)) 0
      - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g')
        (fun z θ => Φs z θ + EllSol g' z θ)) 0|
      ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h := by
    rw [← hkey]
    refine le_trans hl12D ?_
    calc Ci * Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.Construction.N α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + EllSol g z θ) z θ
            - Work.Construction.N α (Work.Construction.Ftot α g')
              (fun z θ => Φs z θ + EllSol g' z θ) z θ)
        ≤ Ci * (K0 * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h) :=
          mul_le_mul_of_nonneg_left hXnD0 hN.pos.1.le
      _ = (Ci * K0) * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h) := by ring
      _ ≤ K * ((1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h) := mul_le_mul_of_nonneg_right hCiK0K hX0
      _ = K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h := by ring
  exact ⟨hGSm, hGmem, hXnD, hL12b⟩

end Work.FTS.GalFields.RHS.Sharp
