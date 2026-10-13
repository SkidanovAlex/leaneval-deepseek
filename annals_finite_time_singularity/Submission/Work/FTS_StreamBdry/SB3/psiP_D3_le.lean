import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB1.psiP_ode
import Submission.Work.FTS_StreamBdry.SB1.psiP_diff
import Submission.Work.FTS_StreamBdry.SB3.DzJDefs
import Submission.Work.FTS_StreamBdry.SBpsiP.DzJ_crux
import Submission.Work.FTS_StreamBdry.SBpsiP.SelfUprime
import Submission.Work.FTS_StreamBdry.SBpsiP.SelfBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB3.psiP_D3_le` — the third radial derivative of the `U`-slot part

`psiP αG Ψ = -(s2 θ/αG)·∫₀¹ v^{3/αG-1}·U'(Ψ)(zv,θ) dv` is the particular solution of the level-0
ODE `αG·D_z P + 3 P = -s2·U'(Ψ)` (`SB1/psiP_ode`), whose *first two* radial derivatives are
controlled directly by the slot bounds (`SlotBd`) through the scaling identity of the parameter
integral (`SBpsiP/DzJ_crux`, `SB3D3/DzIter2_psiP_eq_le`):

  `|D_z² (psiP αG Ψ)| ≤ M·s2 θ / 3`   (the sharp constant `1/3 = αG·∫₀¹v^{3/αG-1}dv`).

The *third* derivative is not of this form (`SlotBd` does not bound `D_z³U'`); it is obtained from
the ODE instead.  Writing `P = psiP αG Ψ`, `U = U'(Ψ)`, `c = -(s2 θ/αG)` and `k = 3/αG`, the ODE
reads `D_z P = c·U - k·P`; applying the operator `D_z = z∂_z` twice more gives the tower

  `D_z² P = c·D_z U - k·D_z P`,     `D_z³ P = c·D_z² U - k·D_z² P`,

and eliminating `D_z P` between the first identity and `αG·k = 3`, `αG·c = -s2 θ` gives

  `αG·D_z³ P + 3·D_z² P = -s2 θ·D_z² U`         (`psiP_D3_aux_tower`, `hI3` below).

Combining this with the sharp second-order bound yields

  `|D_z³ P| ≤ (s2 θ·M + 3·M·s2 θ/3)/αG = (2M/αG)·s2 θ`,

which is the statement of this file.

## Route of the tower

The tower is a statement about *slice* functions `t ↦ P t` at fixed `θ`.  Its inputs are

* `hode`: the ODE, read at fixed `θ` (`SB1.psiP_ode`);
* `hdP`: differentiability of the `z`-slices of `P` (`SB1.psiP_diff`);
* `hdφ`, `hdφ'`: differentiability of the `z`-slices of `U'` and of `∂_z U'`, from the `C²`
  regularity of the slot (`psiP_D3_aux_Uprime_c2`, proved here by the same `fderiv` computation
  as `SB1/contDiffOn_uncurry_Uprime`, one order higher).

The tower itself (`psiP_D3_aux_tower`) is then pure one-dimensional calculus: an identity
`D_z P = c·U - k·P` between functions on `(0,∞)` may be differentiated, because the two functions
agree *eventually* and `deriv` only sees the germ (`Filter.EventuallyEq.deriv_eq`); the
`DifferentiableAt` hypotheses are exactly what is needed to evaluate `deriv` of the right side and
to know that the *first* derivative function is itself differentiable for the second step.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB3

open Work.FTS.StreamBdryIface (Uprime SlotBd psiP)

set_option autoImplicit false

/-! ## §0 The `C²` regularity of the `U`-slot and of its `z`-derivative -/

/-- `∂_z` costs one order of smoothness on an open set, at finite order. -/
theorem psiP_D3_aux_pz_smooth {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {n : ℕ} (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by norm_num : (n + 1 : WithTop ℕ∞) ≠ 0)).differentiableAt
        (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- **The `U`-slot is `C²` on the open quadrant** as soon as `Ψ` is `C³` there.
`U'(Ψ) = (-3Ψ - αG·z∂_zΨ)/sin 2θ`: the numerator is `C²` (`∂_z` costs one order) and the
denominator is `C^∞` and non-vanishing on `Qd`. -/
theorem psiP_D3_aux_Uprime_c2 {αG : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd) :
    ContDiffOn ℝ 2 (Function.uncurry (Uprime αG Ψ)) Work.Construction.Qd := by
  have hQd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  have h2 : ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.Construction.Qd := h3.of_le (by norm_num)
  have hpz : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pz Ψ)) Work.Construction.Qd :=
    psiP_D3_aux_pz_smooth hQd h3
  have hnum : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      -3 * Function.uncurry Ψ p - αG * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p)
      Work.Construction.Qd := by
    refine (contDiffOn_const.mul h2).sub ?_
    exact (contDiffOn_const.mul (contDiff_fst.contDiffOn)).mul hpz
  have hden : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.Construction.Qd :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hne : ∀ p ∈ Work.Construction.Qd, Real.sin (2 * p.2) ≠ 0 := by
    intro p hp
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [Real.pi_pos, hp.2.2]))
  refine (hnum.div hden hne).congr (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry, Uprime, Work.Construction.Uop,
    Work.Construction.s2, Work.Spaces.pz, Pi.div_apply]

/-! ## §1 The one-dimensional tower for an abstract pair `(P, φ)` -/

/-- **The tower.**  If `P, φ : ℝ → ℝ` satisfy `t·P'(t) = c·φ(t) - k·P(t)` on `(0,∞)` and `P`, `φ`,
`φ'` are differentiable there, then applying `t·d/dt` to that identity twice gives

  `t·(t·P')'(t) = c·(t·φ'(t)) - k·(t·P'(t))`,
  `t·(t·(t·P')')'(t) = c·(t·(t·φ')'(t)) - k·(t·(t·P')'(t))`.

This is `(D_z P = c·U - k·P) ⟹ (D_z²P = c·D_zU - k·D_zP) ⟹ (D_z³P = c·D_z²U - k·D_z²P)`
for the *slice* functions, with `D_z = t·d/dt`. -/
theorem psiP_D3_aux_tower {c k : ℝ} {P φ : ℝ → ℝ}
    (hode : ∀ t ∈ Set.Ioi (0:ℝ), t * deriv P t = c * φ t - k * P t)
    (hdP : ∀ t ∈ Set.Ioi (0:ℝ), DifferentiableAt ℝ P t)
    (hdφ : ∀ t ∈ Set.Ioi (0:ℝ), DifferentiableAt ℝ φ t)
    (hdφ' : ∀ t ∈ Set.Ioi (0:ℝ), DifferentiableAt ℝ (fun s => deriv φ s) t) :
    (∀ t ∈ Set.Ioi (0:ℝ),
        t * deriv (fun s => s * deriv P s) t = c * (t * deriv φ t) - k * (t * deriv P t)) ∧
    (∀ t ∈ Set.Ioi (0:ℝ),
        t * deriv (fun s => s * deriv (fun u => u * deriv P u) s) t
          = c * (t * deriv (fun u => u * deriv φ u) t)
            - k * (t * deriv (fun u => u * deriv P u) t)) := by
  have hb : ∀ t ∈ Set.Ioi (0:ℝ),
      t * deriv (fun s => s * deriv P s) t = c * (t * deriv φ t) - k * (t * deriv P t) := by
    intro t ht
    have hEq : (fun s => s * deriv P s) =ᶠ[𝓝 t] (fun s => c * φ s - k * P s) :=
      Set.EqOn.eventuallyEq_of_mem (fun s hs => hode s hs) (isOpen_Ioi.mem_nhds ht)
    have h1 : deriv (fun s => s * deriv P s) t = c * deriv φ t - k * deriv P t := by
      rw [hEq.deriv_eq]
      exact (((hdφ t ht).hasDerivAt.const_mul c).sub
        ((hdP t ht).hasDerivAt.const_mul k)).deriv
    rw [h1]
    ring
  refine ⟨hb, ?_⟩
  intro t ht
  have hEq2 : (fun s => s * deriv (fun u => u * deriv P u) s)
      =ᶠ[𝓝 t] (fun s => c * (s * deriv φ s) - k * (s * deriv P s)) :=
    Set.EqOn.eventuallyEq_of_mem (fun s hs => hb s hs) (isOpen_Ioi.mem_nhds ht)
  have hEqP : (fun s => s * deriv P s) =ᶠ[𝓝 t] (fun s => c * φ s - k * P s) :=
    Set.EqOn.eventuallyEq_of_mem (fun s hs => hode s hs) (isOpen_Ioi.mem_nhds ht)
  have hP1 : DifferentiableAt ℝ (fun s => s * deriv P s) t :=
    hEqP.differentiableAt_iff.mpr (((hdφ t ht).const_mul c).sub ((hdP t ht).const_mul k))
  have hφ1 : DifferentiableAt ℝ (fun s => s * deriv φ s) t :=
    differentiableAt_id.mul (hdφ' t ht)
  have h1 : deriv (fun s => s * deriv (fun u => u * deriv P u) s) t
      = c * deriv (fun s => s * deriv φ s) t - k * deriv (fun s => s * deriv P s) t := by
    rw [hEq2.deriv_eq]
    exact (((hφ1.hasDerivAt.const_mul c).sub (hP1.hasDerivAt.const_mul k))).deriv
  rw [h1]
  ring

/-! ## §2 The sharp second-order bound `|D_z² psiP| ≤ M·s2 θ/3`

This is the `j = 2` case of the scaling identity for the parameter integral
`J c h z θ = ∫₀¹ v^c h(zv,θ) dv` (`SBpsiP/DzJ_crux`, proved by `J_Dz_eq`): applying it to
`h = U'(Ψ)` and then to `h = D_z U'(Ψ)` gives

  `D_z² (psiP αG Ψ) = -(s2 θ/αG)·J (3/αG-1) (D_z² U'(Ψ))`,

and the elementary estimate `|J c h| ≤ M/(c+1) = M·αG/3` (`SBpsiP/SelfBound`, for `|h| ≤ M`)
turns this into `M·s2 θ/3`.  The hypotheses of `J_Dz_eq` (continuity of the slot iterates and
their `z`-slice differentiability) are supplied by the finite-order smoothness
`SBpsiP.UprimeIterSmooth_self`.
-/

/-- `C¹` on the open quadrant implies differentiability of the `z`-slices. -/
private theorem psiP_D3_aux_slice_diff_one {F : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Work.Construction.Qd)
    (h : ContDiffOn ℝ 1 (Function.uncurry F) Work.Construction.Qd) :
    DifferentiableAt ℝ (fun z' => F z' p.2) p.1 :=
  Work.Spaces.differentiableAt_curry_left
    ((h.differentiableOn (by norm_num)).differentiableAt (isOpen_Qd.mem_nhds hp))

/-- `C²` on the open quadrant implies differentiability of the `z`-slices. -/
private theorem psiP_D3_aux_slice_diff_two {F : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Work.Construction.Qd)
    (h : ContDiffOn ℝ 2 (Function.uncurry F) Work.Construction.Qd) :
    DifferentiableAt ℝ (fun z' => F z' p.2) p.1 :=
  Work.Spaces.differentiableAt_curry_left
    ((h.differentiableOn (by norm_num)).differentiableAt (isOpen_Qd.mem_nhds hp))

/-- The `θ`-only multiple rule for `D_z`. -/
private theorem psiP_D3_aux_Dz_theta_mul {a : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hd : DifferentiableAt ℝ (fun z' => F z' θ) z) :
    Work.Spaces.Dz (fun z θ => a θ * F z θ) z θ = a θ * Work.Spaces.Dz F z θ := by
  show z * deriv (fun z' => a θ * F z' θ) z = a θ * (z * deriv (fun z' => F z' θ) z)
  rw [deriv_const_mul _ hd]
  ring

/-- **The sharp second-order bound**: `|D_z² (psiP αG Ψ)| ≤ M·s2 θ/3`. -/
theorem psiP_D3_aux_DzIter2_le {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.DzIter 2 (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ / 3 := by
  intro z θ hmem
  obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hmem
  have hQd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  have hs2nn : 0 ≤ Work.Construction.s2 θ := le_of_lt (Work.FTS_StreamBdry.s2_pos_of_Qd hmem)
  have hM : 0 ≤ M := by
    have h1 : ((1 : ℝ), Real.pi / 4) ∈ Work.Construction.Qd :=
      Work.FTS_StreamBdry.mem_Qd.mpr
        ⟨by norm_num, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact le_trans (abs_nonneg _) (SlotBd.Uprime_le hslot h1)
  have hc : (-1 : ℝ) < 3 / αG - 1 := by
    have : (0 : ℝ) < 3 / αG := div_pos (by norm_num) hαG
    linarith
  have hsm : ∀ j : ℕ, j ≤ 2 → ContDiffOn ℝ (2 - j)
      (Function.uncurry (Work.Spaces.DzIter j (Uprime αG Ψ))) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SBpsiP.UprimeIterSmooth_self hαG h3
  have hcont_all : ∀ i : ℕ, i ≤ 2 → ContinuousOn
      (Function.uncurry (Work.Spaces.DzIter i (Uprime αG Ψ))) Work.Construction.Qd :=
    fun i hi => (hsm i hi).continuousOn
  have hbnd_all : ∀ i : ℕ, i ≤ 2 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.DzIter i (Uprime αG Ψ) z θ| ≤ M :=
    fun i hi z θ hzθ => SlotBd.Dz_le hslot hzθ hi
  have hslice_all : ∀ i : ℕ, i ≤ 1 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter i (Uprime αG Ψ) z' θ) z := by
    intro i hi z θ hzθ
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact psiP_D3_aux_slice_diff_two hzθ (hsm 0 (by norm_num))
    · exact psiP_D3_aux_slice_diff_one hzθ (hsm 1 (by norm_num))
  -- the level-0 identity
  have hbase : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      psiP αG Ψ z θ = -(Work.Construction.s2 θ / αG)
        * Work.FTS_StreamBdry.SB3.J (3 / αG - 1) (Uprime αG Ψ) z θ := by
    intro z θ hzθ
    rw [Work.FTS_StreamBdry.psiP_eq_Iint, Work.FTS_StreamBdry.SB3.Iint_eq_J]
  -- the level-1 identity
  have h1pt : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.DzIter 1 (psiP αG Ψ) z θ = -(Work.Construction.s2 θ / αG)
        * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
            (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ := by
    intro z θ hzθ
    have hJ := Work.FTS_StreamBdry.SBpsiP.J_Dz_eq (c := 3 / αG - 1) hc
      (h := Uprime αG Ψ)
      (hcont_all 0 (by norm_num)) (hcont_all 1 (by norm_num))
      (hslice_all 0 (by norm_num))
      (hbnd_all 0 (by norm_num)) (hbnd_all 1 (by norm_num)) z θ hzθ
    have hcongr : Work.Spaces.pz (psiP αG Ψ) z θ
        = Work.Spaces.pz (fun z θ => -(Work.Construction.s2 θ / αG)
            * Work.FTS_StreamBdry.SB3.J (3 / αG - 1) (Uprime αG Ψ) z θ) z θ :=
      Work.Spaces.pz_congr_of_isOpen hQd
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
      rw [psiP_D3_aux_Dz_theta_mul (a := fun θ => -(Work.Construction.s2 θ / αG)) hJ.1, hJ.2]
      rfl
    change Work.Spaces.Dz (Work.Spaces.DzIter 0 (psiP αG Ψ)) z θ
      = -(Work.Construction.s2 θ / αG) * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
          (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ
    rw [Work.Spaces.DzIter_zero, hDz, hval]
  -- the level-2 identity
  have h2pt : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.DzIter 2 (psiP αG Ψ) z θ = -(Work.Construction.s2 θ / αG)
        * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
            (Work.Spaces.DzIter 2 (Uprime αG Ψ)) z θ := by
    intro z θ hzθ
    have hJ := Work.FTS_StreamBdry.SBpsiP.J_Dz_eq (c := 3 / αG - 1) hc
      (h := Work.Spaces.DzIter 1 (Uprime αG Ψ))
      (hcont_all 1 (by norm_num)) (hcont_all 2 (by norm_num))
      (hslice_all 1 (by norm_num))
      (hbnd_all 1 (by norm_num)) (hbnd_all 2 (by norm_num)) z θ hzθ
    have hcongr : Work.Spaces.pz (Work.Spaces.DzIter 1 (psiP αG Ψ)) z θ
        = Work.Spaces.pz (fun z θ => -(Work.Construction.s2 θ / αG)
            * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
                (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ) z θ :=
      Work.Spaces.pz_congr_of_isOpen hQd
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
      rw [psiP_D3_aux_Dz_theta_mul (a := fun θ => -(Work.Construction.s2 θ / αG)) hJ.1, hJ.2]
      rfl
    change Work.Spaces.Dz (Work.Spaces.DzIter 1 (psiP αG Ψ)) z θ
      = -(Work.Construction.s2 θ / αG) * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
          (Work.Spaces.DzIter 2 (Uprime αG Ψ)) z θ
    rw [hDz, hval]
  -- the integral bound
  have hJb : |Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
      (Work.Spaces.DzIter 2 (Uprime αG Ψ)) z θ| ≤ M * (αG / 3) := by
    have hφcont : ContinuousOn
        (fun v : ℝ => Work.Spaces.DzIter 2 (Uprime αG Ψ) (z * v) θ)
        (Set.Ioc (0 : ℝ) 1) := by
      have hlin : ContinuousOn (fun v : ℝ => (z * v, θ)) (Set.Ioc (0 : ℝ) 1) :=
        ((continuous_const.mul continuous_id).prodMk continuous_const).continuousOn
      have hcomp := (hcont_all 2 (by norm_num)).comp hlin
        (fun v hv => ⟨mul_pos hz hv.1, hθ1, hθ2⟩)
      simpa [Function.comp_def, Function.uncurry] using hcomp
    have hφbd : ∀ v ∈ Set.Ioc (0 : ℝ) 1,
        |Work.Spaces.DzIter 2 (Uprime αG Ψ) (z * v) θ| ≤ M :=
      fun v hv => hbnd_all 2 (by norm_num) (z * v) θ ⟨mul_pos hz hv.1, hθ1, hθ2⟩
    have hmain := Work.FTS_StreamBdry.SBpsiP.J_bound_self (c := 3 / αG - 1) (B := M)
      hc hM hφcont hφbd
    have hsimp : M / (3 / αG - 1 + 1) = M * (αG / 3) := by
      rw [show (3 / αG - 1 + 1 : ℝ) = 3 / αG by ring, div_eq_mul_inv, inv_div]
    simpa only [Work.FTS_StreamBdry.SB3.J_apply] using hmain.trans_eq hsimp
  -- assembly
  have hAa : |-(Work.Construction.s2 θ / αG)| = Work.Construction.s2 θ / αG := by
    rw [abs_neg, abs_of_nonneg (div_nonneg hs2nn (le_of_lt hαG))]
  rw [h2pt z θ hmem, abs_mul, hAa]
  have hstep : (Work.Construction.s2 θ / αG) * |Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
        (Work.Spaces.DzIter 2 (Uprime αG Ψ)) z θ|
      ≤ (Work.Construction.s2 θ / αG) * (M * (αG / 3)) :=
    mul_le_mul_of_nonneg_left hJb (div_nonneg hs2nn (le_of_lt hαG))
  have hstep2 : (Work.Construction.s2 θ / αG) * (M * (αG / 3))
      = M * Work.Construction.s2 θ / 3 := by
    field_simp
  linarith [hstep, hstep2]

/-! ## §3 The third-order bound -/

theorem psiP_D3_le {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.DzIter 3 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ|
        ≤ (2 * M / αG) * Work.Construction.s2 θ := by
  intro z θ hmem
  obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hmem
  have hQd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  -- positivity data
  have hs2pos : 0 < Work.Construction.s2 θ := Work.FTS_StreamBdry.s2_pos_of_Qd hmem
  have hs2nn : 0 ≤ Work.Construction.s2 θ := le_of_lt hs2pos
  have hMnn : 0 ≤ M := by
    have h1 : ((1 : ℝ), Real.pi / 4) ∈ Work.Construction.Qd :=
      Work.FTS_StreamBdry.mem_Qd.mpr
        ⟨by norm_num, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact le_trans (abs_nonneg _) (Work.FTS_StreamBdry.SlotBd.Uprime_le hslot h1)
  -- the two regularity inputs for the tower
  have hUsm : ContDiffOn ℝ 2 (Function.uncurry (Uprime αG Ψ)) Work.Construction.Qd :=
    psiP_D3_aux_Uprime_c2 h3
  have hpzU : ContDiffOn ℝ 1
      (Function.uncurry (Work.Spaces.pz (Uprime αG Ψ))) Work.Construction.Qd :=
    psiP_D3_aux_pz_smooth hQd hUsm
  have hode_psiP : Work.FTS_StreamBdry.PsiPOde αG M Ψ :=
    Work.FTS_StreamBdry.SB1.psiP_ode hαG h3 hslot
  have hpdiff : Work.FTS_StreamBdry.PsiPDiff αG M Ψ :=
    Work.FTS_StreamBdry.SB1.psiP_diff hαG h3 hslot
  -- slice notation
  set P : ℝ → ℝ := fun t => Work.FTS.StreamBdryIface.psiP αG Ψ t θ with hP
  set φ : ℝ → ℝ := fun t => Work.FTS.StreamBdryIface.Uprime αG Ψ t θ with hφ
  set c₂ : ℝ := -(Work.Construction.s2 θ / αG) with hc₂
  set k : ℝ := 3 / αG with hk
  -- the ODE, slicewise
  have hode : ∀ t ∈ Set.Ioi (0:ℝ), t * deriv P t = c₂ * φ t - k * P t := by
    intro t ht
    have hmemt : (t, θ) ∈ Work.Construction.Qd := ⟨ht, hθ1, hθ2⟩
    have h := hode_psiP t θ hmemt
    have h' : αG * (t * deriv P t) + 3 * P t = -(Work.Construction.s2 θ) * φ t := by
      have h'' : αG * t * deriv P t + 3 * P t = -(Work.Construction.s2 θ) * φ t := by
        simpa only [Work.Spaces.pz, hP, hφ] using h
      rw [mul_assoc] at h''
      exact h''
    rw [hc₂, hk]
    have h'' : αG * (t * deriv P t) = -(Work.Construction.s2 θ) * φ t - 3 * P t := by
      linarith [h']
    field_simp
    linarith [h'']
  have hdP : ∀ t ∈ Set.Ioi (0:ℝ), DifferentiableAt ℝ P t := by
    intro t ht
    have hmemt : (t, θ) ∈ Work.Construction.Qd := ⟨ht, hθ1, hθ2⟩
    simpa only [hP] using (hpdiff t θ hmemt).1
  have hdφ : ∀ t ∈ Set.Ioi (0:ℝ), DifferentiableAt ℝ φ t := by
    intro t ht
    have hmemt : (t, θ) ∈ Work.Construction.Qd := ⟨ht, hθ1, hθ2⟩
    have h1 := Work.Spaces.differentiableAt_curry_left
      ((hUsm.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hmemt))
    simpa only [hφ] using h1
  have hdφ' : ∀ t ∈ Set.Ioi (0:ℝ), DifferentiableAt ℝ (fun s => deriv φ s) t := by
    intro t ht
    have hmemt : (t, θ) ∈ Work.Construction.Qd := ⟨ht, hθ1, hθ2⟩
    have h1 := Work.Spaces.differentiableAt_curry_left
      ((hpzU.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hmemt))
    simpa only [hφ, Work.Spaces.pz] using h1
  have htower := psiP_D3_aux_tower hode hdP hdφ hdφ'
  -- the sharp second-order bound (from the level-2 scaling identity) and the slot bound
  have hb2 : |Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ|
      ≤ M * Work.Construction.s2 θ / 3 :=
    psiP_D3_aux_DzIter2_le hαG h3 hslot z θ hmem
  have hM2 : |Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.Uprime αG Ψ) z θ| ≤ M :=
    Work.FTS_StreamBdry.SlotBd.Dz_le hslot hmem (j := 2) (by norm_num)
  -- the `DzIter` values are the slice values
  have hD2P : Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ
      = z * deriv (fun s => s * deriv P s) z := by
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
      Work.Spaces.pz, hP]
  have hD3P : Work.Spaces.DzIter 3 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ
      = z * deriv (fun s => s * deriv (fun u => u * deriv P u) s) z := by
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
      Work.Spaces.pz, hP]
  have hD2φ : Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.Uprime αG Ψ) z θ
      = z * deriv (fun s => s * deriv φ s) z := by
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
      Work.Spaces.pz, hφ]
  -- the third-order ODE identity
  have hI3 : αG * (Work.Spaces.DzIter 3 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ)
      + 3 * (Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ)
      = -(Work.Construction.s2 θ)
        * (Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.Uprime αG Ψ) z θ) := by
    rw [hD3P, hD2P, hD2φ, htower.2 z hz, hc₂, hk]
    field_simp
    ring
  -- conclusion
  have hD3eq : Work.Spaces.DzIter 3 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ
      = (-(Work.Construction.s2 θ
            * Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.Uprime αG Ψ) z θ)
          - 3 * Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ) / αG := by
    rw [eq_div_iff (ne_of_gt hαG)]
    linarith [hI3]
  rw [hD3eq]
  have h1 : |-(Work.Construction.s2 θ
        * Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.Uprime αG Ψ) z θ)
        - 3 * Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ|
      ≤ Work.Construction.s2 θ * M + 3 * (M * Work.Construction.s2 θ / 3) := by
    refine (abs_sub _ _).trans ?_
    have hle1 : |-(Work.Construction.s2 θ
          * Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.Uprime αG Ψ) z θ)|
        ≤ Work.Construction.s2 θ * M := by
      rw [abs_neg, abs_mul, abs_of_nonneg hs2nn]
      exact mul_le_mul_of_nonneg_left hM2 hs2nn
    have hle2 : |3 * Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ|
        ≤ 3 * (M * Work.Construction.s2 θ / 3) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]
      exact mul_le_mul_of_nonneg_left hb2 (by norm_num)
    linarith
  calc |(-(Work.Construction.s2 θ
            * Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.Uprime αG Ψ) z θ)
          - 3 * Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ) / αG|
      = |-(Work.Construction.s2 θ
            * Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.Uprime αG Ψ) z θ)
          - 3 * Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ| / αG := by
        rw [abs_div, abs_of_pos hαG]
    _ ≤ (Work.Construction.s2 θ * M + 3 * (M * Work.Construction.s2 θ / 3)) / αG := by
        gcongr
    _ = (2 * M / αG) * Work.Construction.s2 θ := by
        field_simp
        ring

end Work.FTS_StreamBdry.SB3
