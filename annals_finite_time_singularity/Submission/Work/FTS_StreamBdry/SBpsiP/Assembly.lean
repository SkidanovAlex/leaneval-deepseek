import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB3.DzJDefs
import Submission.Work.FTS_StreamBdry.SBpsiP.DzJ_crux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SBpsiP.Assembly` — `|D_z^j psiP| ≤ M·sin 2θ`, assembled

The target `Work.FTS_StreamBdry.PsiPDzLe αG M Ψ` says that the `U`-slot part of the stream
function satisfies `|D_z^j (psiP αG Ψ)| ≤ M·sin 2θ` on the open quadrant, for `j ≤ 2`, under
the slot bound `SlotBd αG Ψ M` (`|D_z^j U'(Ψ)| ≤ M`, `j ≤ 2`) and `Ψ ∈ C³`.

Since `psiP αG Ψ = -(s2 θ/αG)·J c (U'(Ψ))` *definitionally* (`c = 3/αG - 1`, `J` the scaled
parameter integral of `SB3/DzJDefs`), everything follows from the chain

  `D_z^j (psiP αG Ψ) = -(s2 θ/αG)·J c (D_z^j U'(Ψ))`   (`j ≤ 2`),

obtained by applying the differentiation identity `SBpsiP.J_Dz_eq` first to `h = U'(Ψ)` and
then to `h = D_z U'(Ψ)` (each application gives both the identity and the differentiability
of the slice which the next one needs), and from the integral bound

  `|J c h z θ| ≤ M·(αG/3)`   whenever `|h| ≤ M` and `c + 1 = 3/αG`.

This file is stated *conditionally* on those two ingredients (`hsm`, `hbd`), so that the
crux analysis (`J_Dz_eq`, proved in `SBpsiP/DzJ_crux`) is separated from the finite-order
smoothness of the slot iterates and the elementary integral bound; the target file
`SB3/psiP_DzLe` discharges the two hypotheses.
-/

noncomputable section
open scoped Real Topology Interval
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SBpsiP

open Work.FTS.StreamBdryIface (Uprime SlotBd psiP)

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- `C¹` on the open quadrant implies differentiability of the `z`-slices. -/
lemma slice_diff_of_contDiffOn_one {F : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Work.Construction.Qd)
    (h : ContDiffOn ℝ 1 (Function.uncurry F) Work.Construction.Qd) :
    DifferentiableAt ℝ (fun z' => F z' p.2) p.1 :=
  Work.Spaces.differentiableAt_curry_left
    ((h.differentiableOn (by norm_num)).differentiableAt (isOpen_Qd'.mem_nhds hp))

/-- `C²` on the open quadrant implies differentiability of the `z`-slices. -/
lemma slice_diff_of_contDiffOn_two {F : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Work.Construction.Qd)
    (h : ContDiffOn ℝ 2 (Function.uncurry F) Work.Construction.Qd) :
    DifferentiableAt ℝ (fun z' => F z' p.2) p.1 :=
  Work.Spaces.differentiableAt_curry_left
    ((h.differentiableOn (by norm_num)).differentiableAt (isOpen_Qd'.mem_nhds hp))

/-- The `θ`-only multiple rule for `D_z`. -/
lemma Dz_theta_mul {a : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hd : DifferentiableAt ℝ (fun z' => F z' θ) z) :
    Work.Spaces.Dz (fun z θ => a θ * F z θ) z θ = a θ * Work.Spaces.Dz F z θ := by
  have hfun : (fun z' : ℝ => a θ * F z' θ)
      = (fun z' : ℝ => a θ * (fun z'' : ℝ => F z'' θ) z') := rfl
  show z * deriv (fun z' : ℝ => a θ * F z' θ) z = a θ * (z * deriv (fun z' => F z' θ) z)
  rw [hfun, deriv_const_mul _ hd]
  ring

/-- **`|D_z^j psiP| ≤ M·sin 2θ` from the two ingredients.**  `hsm` is the finite-order
smoothness of the slot iterates (`D_z^j U'(Ψ) ∈ C^{2-j}` on the quadrant) and `hbd` the
elementary scaled-integral bound. -/
theorem psiP_DzLe_of_pieces
    (hsm : ∀ (αG : ℝ), 0 < αG → ∀ (Ψ : ℝ → ℝ → ℝ),
      ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd →
      ∀ j : ℕ, j ≤ 2 → ContDiffOn ℝ (2 - j)
        (Function.uncurry (Work.Spaces.DzIter j (Uprime αG Ψ))) Work.Construction.Qd)
    (hbd : ∀ (c B : ℝ), -1 < c → 0 ≤ B → ∀ (φ : ℝ → ℝ),
      ContinuousOn φ (Set.Ioc (0 : ℝ) 1) → (∀ v ∈ Set.Ioc (0 : ℝ) 1, |φ v| ≤ B) →
      |∫ v in (0 : ℝ)..1, v ^ c * φ v| ≤ B / (c + 1))
    {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) :
    Work.FTS_StreamBdry.PsiPDzLe αG M Ψ := by
  intro z θ hmem j hj
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS_StreamBdry.mem_Qd.mp hmem
  have hs2nn : 0 ≤ Work.Construction.s2 θ :=
    le_of_lt (Work.FTS_StreamBdry.s2_pos_of_Qd hmem)
  have hαGne : αG ≠ 0 := ne_of_gt hαG
  -- `M ≥ 0`
  have hM : 0 ≤ M := by
    have h1 : ((1 : ℝ), π / 4) ∈ Work.Construction.Qd :=
      Work.FTS_StreamBdry.mem_Qd.mpr
        ⟨by norm_num, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact le_trans (abs_nonneg _) (SlotBd.Uprime_le hslot h1)
  have hc : (-1 : ℝ) < 3 / αG - 1 := by
    have h3pos : (0 : ℝ) < 3 / αG := div_pos (by norm_num) hαG
    linarith
  -- continuity and bounds for the iterates of the slot
  have hcont_all : ∀ i : ℕ, i ≤ 2 → ContinuousOn
      (Function.uncurry (Work.Spaces.DzIter i (Uprime αG Ψ))) Work.Construction.Qd :=
    fun i hi => (hsm αG hαG Ψ h3 i hi).continuousOn
  have hbnd_all : ∀ i : ℕ, i ≤ 2 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.DzIter i (Uprime αG Ψ) z θ| ≤ M :=
    fun i hi z θ hzθ => SlotBd.Dz_le hslot hzθ hi
  -- the pointwise identity at level 0
  have hbase : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      psiP αG Ψ z θ = -(Work.Construction.s2 θ / αG)
        * Work.FTS_StreamBdry.SB3.J (3 / αG - 1) (Uprime αG Ψ) z θ := by
    intro z θ hzθ
    rw [Work.FTS_StreamBdry.psiP_eq_Iint, Work.FTS_StreamBdry.SB3.Iint_eq_J]
  -- the identity at level 1
  have h1pt : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.DzIter 1 (psiP αG Ψ) z θ
        = -(Work.Construction.s2 θ / αG) * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
            (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ := by
    intro z θ hzθ
    have hJ := J_Dz_eq (c := 3 / αG - 1) hc
      (h := Uprime αG Ψ)
      (hcont_all 0 (by norm_num)) (hcont_all 1 (by norm_num))
      (fun z θ hzθ => slice_diff_of_contDiffOn_two hzθ
        (by simpa using hsm αG hαG Ψ h3 0 (by norm_num)))
      (fun z θ hzθ => hbnd_all 0 (by norm_num) z θ hzθ)
      (fun z θ hzθ => hbnd_all 1 (by norm_num) z θ hzθ) z θ hzθ
    have hcongr : Work.Spaces.pz (psiP αG Ψ) z θ
        = Work.Spaces.pz (fun z θ => -(Work.Construction.s2 θ / αG)
            * Work.FTS_StreamBdry.SB3.J (3 / αG - 1) (Uprime αG Ψ) z θ) z θ :=
      Work.Spaces.pz_congr_of_isOpen isOpen_Qd'
        (fun q hq => by
          show Function.uncurry (psiP αG Ψ) q = Function.uncurry (fun z θ =>
            -(Work.Construction.s2 θ / αG)
              * Work.FTS_StreamBdry.SB3.J (3 / αG - 1) (Uprime αG Ψ) z θ) q
          simpa only [Function.uncurry] using hbase q.1 q.2 hq) hzθ
    have hDz : Work.Spaces.Dz (psiP αG Ψ) z θ
        = Work.Spaces.Dz (fun z θ => -(Work.Construction.s2 θ / αG)
            * Work.FTS_StreamBdry.SB3.J (3 / αG - 1) (Uprime αG Ψ) z θ) z θ := by
      show z * Work.Spaces.pz (psiP αG Ψ) z θ = z * Work.Spaces.pz (fun z θ =>
        -(Work.Construction.s2 θ / αG)
          * Work.FTS_StreamBdry.SB3.J (3 / αG - 1) (Uprime αG Ψ) z θ) z θ
      rw [hcongr]
    have hval : Work.Spaces.Dz (fun z θ => -(Work.Construction.s2 θ / αG)
          * Work.FTS_StreamBdry.SB3.J (3 / αG - 1) (Uprime αG Ψ) z θ) z θ
        = -(Work.Construction.s2 θ / αG) * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
            (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ := by
      rw [Dz_theta_mul (a := fun θ => -(Work.Construction.s2 θ / αG)) hJ.1, hJ.2]
      rfl
    change Work.Spaces.Dz (Work.Spaces.DzIter 0 (psiP αG Ψ)) z θ
      = -(Work.Construction.s2 θ / αG) * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
          (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ
    rw [Work.Spaces.DzIter_zero, hDz, hval]
  -- the identity at level 2
  have h2pt : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.DzIter 2 (psiP αG Ψ) z θ
        = -(Work.Construction.s2 θ / αG) * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
            (Work.Spaces.DzIter 2 (Uprime αG Ψ)) z θ := by
    intro z θ hzθ
    have hJ := J_Dz_eq (c := 3 / αG - 1) hc
      (h := Work.Spaces.DzIter 1 (Uprime αG Ψ))
      (hcont_all 1 (by norm_num)) (hcont_all 2 (by norm_num))
      (fun z θ hzθ => slice_diff_of_contDiffOn_one hzθ
        ((hsm αG hαG Ψ h3 1 (by norm_num)).of_le (by decide)))
      (fun z θ hzθ => hbnd_all 1 (by norm_num) z θ hzθ)
      (fun z θ hzθ => hbnd_all 2 (by norm_num) z θ hzθ) z θ hzθ
    have hcongr : Work.Spaces.pz (Work.Spaces.DzIter 1 (psiP αG Ψ)) z θ
        = Work.Spaces.pz (fun z θ => -(Work.Construction.s2 θ / αG)
            * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
                (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ) z θ :=
      Work.Spaces.pz_congr_of_isOpen isOpen_Qd'
        (fun q hq => by
          show Function.uncurry (Work.Spaces.DzIter 1 (psiP αG Ψ)) q
            = Function.uncurry (fun z θ => -(Work.Construction.s2 θ / αG)
                * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
                    (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ) q
          simpa only [Function.uncurry] using h1pt q.1 q.2 hq) hzθ
    have hDz : Work.Spaces.Dz (Work.Spaces.DzIter 1 (psiP αG Ψ)) z θ
        = Work.Spaces.Dz (fun z θ => -(Work.Construction.s2 θ / αG)
            * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
                (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ) z θ := by
      show z * Work.Spaces.pz (Work.Spaces.DzIter 1 (psiP αG Ψ)) z θ
        = z * Work.Spaces.pz (fun z θ => -(Work.Construction.s2 θ / αG)
            * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
                (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ) z θ
      rw [hcongr]
    have hval : Work.Spaces.Dz (fun z θ => -(Work.Construction.s2 θ / αG)
          * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
              (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ) z θ
        = -(Work.Construction.s2 θ / αG) * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
            (Work.Spaces.DzIter 2 (Uprime αG Ψ)) z θ := by
      rw [Dz_theta_mul (a := fun θ => -(Work.Construction.s2 θ / αG)) hJ.1, hJ.2]
      rfl
    change Work.Spaces.Dz (Work.Spaces.DzIter 1 (psiP αG Ψ)) z θ
      = -(Work.Construction.s2 θ / αG) * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
          (Work.Spaces.DzIter 2 (Uprime αG Ψ)) z θ
    rw [hDz, hval]
  -- the identity at the given `j`
  have hident : Work.Spaces.DzIter j (psiP αG Ψ) z θ
      = -(Work.Construction.s2 θ / αG) * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
          (Work.Spaces.DzIter j (Uprime αG Ψ)) z θ := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · simpa only [Work.Spaces.DzIter_zero] using hbase z θ hmem
    · exact h1pt z θ hmem
    · exact h2pt z θ hmem
  -- the integral bound
  have hJb : |Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
      (Work.Spaces.DzIter j (Uprime αG Ψ)) z θ| ≤ M * (αG / 3) := by
    have hφcont : ContinuousOn
        (fun v : ℝ => Work.Spaces.DzIter j (Uprime αG Ψ) (z * v) θ)
        (Set.Ioc (0 : ℝ) 1) := by
      have hlin : ContinuousOn (fun v : ℝ => (z * v, θ)) (Set.Ioc (0 : ℝ) 1) :=
        ((continuous_const.mul continuous_id).prodMk continuous_const).continuousOn
      have hcomp := (hcont_all j hj).comp hlin (fun v hv => ⟨mul_pos hz hv.1, hθ0, hθ1⟩)
      simpa [Function.comp_def, Function.uncurry] using hcomp
    have hφbd : ∀ v ∈ Set.Ioc (0 : ℝ) 1,
        |Work.Spaces.DzIter j (Uprime αG Ψ) (z * v) θ| ≤ M :=
      fun v hv => hbnd_all j hj (z * v) θ ⟨mul_pos hz hv.1, hθ0, hθ1⟩
    have hmain := hbd (3 / αG - 1) M hc hM
      (fun v : ℝ => Work.Spaces.DzIter j (Uprime αG Ψ) (z * v) θ) hφcont hφbd
    have hsimp : M / (3 / αG - 1 + 1) = M * (αG / 3) := by
      rw [show (3 / αG - 1 + 1 : ℝ) = 3 / αG by ring, div_eq_mul_inv, inv_div]
    simpa only [Work.FTS_StreamBdry.SB3.J_apply] using hmain.trans_eq hsimp
  -- absolute values
  have hAa : |-(Work.Construction.s2 θ / αG)| = Work.Construction.s2 θ / αG := by
    rw [abs_neg, abs_of_nonneg (div_nonneg hs2nn (le_of_lt hαG))]
  rw [hident, abs_mul, hAa]
  have hstep : (Work.Construction.s2 θ / αG) * |Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
        (Work.Spaces.DzIter j (Uprime αG Ψ)) z θ|
      ≤ (Work.Construction.s2 θ / αG) * (M * (αG / 3)) :=
    mul_le_mul_of_nonneg_left hJb (div_nonneg hs2nn (le_of_lt hαG))
  have hstep2 : (Work.Construction.s2 θ / αG) * (M * (αG / 3))
      = M * Work.Construction.s2 θ / 3 := by
    field_simp
  have hstep3 : M * Work.Construction.s2 θ / 3 ≤ M * Work.Construction.s2 θ := by
    nlinarith [hM, hs2nn]
  linarith [hstep, hstep2, hstep3]

end Work.FTS_StreamBdry.SBpsiP
