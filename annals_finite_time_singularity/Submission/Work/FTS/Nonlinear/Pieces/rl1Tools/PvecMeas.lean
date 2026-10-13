import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.Pvec
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.QuadMeasAux
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.aesm_star_ops
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.aesm_FK
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.aesm_Uop_of_div

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

open Work.FTS.Nonlin Work.Construction Work.Spaces

/-! ## Closure of a.e. strong measurability under the operations occurring in `pv` -/

theorem aesm_congr {F G : ℝ → ℝ → ℝ}
    (hF : AEStronglyMeasurable (Function.uncurry F) QdMeas)
    (hFG : ∀ z θ, F z θ = G z θ) :
    AEStronglyMeasurable (Function.uncurry G) QdMeas :=
  hF.congr (Filter.Eventually.of_forall fun p => hFG p.1 p.2)

theorem aesm_mul {f h : ℝ → ℝ → ℝ}
    (hf : AEStronglyMeasurable (Function.uncurry f) QdMeas)
    (hh : AEStronglyMeasurable (Function.uncurry h) QdMeas) :
    AEStronglyMeasurable (Function.uncurry (fun z θ => f z θ * h z θ)) QdMeas :=
  continuous_mul.comp_aestronglyMeasurable₂ hf hh

theorem aesm_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : AEStronglyMeasurable (Function.uncurry f) QdMeas) :
    AEStronglyMeasurable (Function.uncurry (fun z θ => c * f z θ)) QdMeas :=
  (continuous_const.mul continuous_id).comp_aestronglyMeasurable hf

theorem aesm_neg {f : ℝ → ℝ → ℝ}
    (hf : AEStronglyMeasurable (Function.uncurry f) QdMeas) :
    AEStronglyMeasurable (Function.uncurry (fun z θ => -f z θ)) QdMeas :=
  continuous_neg.comp_aestronglyMeasurable hf

theorem continuous_s2_snd : Continuous fun p : ℝ × ℝ => Work.Construction.s2 p.2 := by
  simp only [Work.Construction.s2]; fun_prop

theorem continuous_sinsq_snd : Continuous fun p : ℝ × ℝ => (Real.sin p.2) ^ 2 := by
  fun_prop

theorem aesm_s2_mul {f : ℝ → ℝ → ℝ}
    (hf : AEStronglyMeasurable (Function.uncurry f) QdMeas) :
    AEStronglyMeasurable (Function.uncurry (fun z θ => Work.Construction.s2 θ * f z θ)) QdMeas :=
  continuous_mul.comp_aestronglyMeasurable₂ continuous_s2_snd.aestronglyMeasurable hf

theorem aesm_sinsq_mul {f : ℝ → ℝ → ℝ}
    (hf : AEStronglyMeasurable (Function.uncurry f) QdMeas) :
    AEStronglyMeasurable (Function.uncurry (fun z θ => (Real.sin θ) ^ 2 * f z θ)) QdMeas :=
  continuous_mul.comp_aestronglyMeasurable₂ continuous_sinsq_snd.aestronglyMeasurable hf

/-! ## The profile `F_*` in terms of `c α = ∫_θ Γ K`

All the facts about `F_*` that the measurability argument needs are elementary *given*
`c α ≠ 0`; when `c α = 0` the profile `F_* = α (Γ/c) (2z/(1+z)²)` collapses to `0`, and
`L₁₂` and `(·,K)` of the zero function vanish.  Splitting on `c α = 0` avoids the extra
hypotheses `0 < α`, `α ≤ 1` of the library lemmas `L12_Fstar_eq`/`FK_Fstar` (which are only
used there to produce `c α ≠ 0`). -/

theorem Fstar_eq_zero_of_c_eq_zero {α : ℝ} (h : Work.Spaces.c α = 0) :
    ∀ z θ, Work.Construction.Fstar α z θ = 0 := by
  intro z θ
  simp [Work.Construction.Fstar, h]

theorem L12dens_Fstar_of_c_ne {α : ℝ} (hc : Work.Spaces.c α ≠ 0) (s : ℝ) :
    Work.Construction.L12dens (Work.Construction.Fstar α) s = α * (Work.FM.Fstar s / s) := by
  rw [Work.Construction.L12dens, Work.FM.L12dens]
  have hpoint : ∀ θ : ℝ, Work.Spaces.K θ * Work.Construction.Fstar α s θ / s
      = (α * (Work.Spaces.Gam α θ * Work.Spaces.K θ) / Work.Spaces.c α)
          * (Work.FM.Fstar s / s) := by
    intro θ
    simp only [Work.Construction.Fstar]
    ring
  rw [MeasureTheory.setIntegral_congr_fun (s := Set.Icc 0 (Real.pi / 2)) measurableSet_Icc
        (fun θ _ => hpoint θ)]
  rw [MeasureTheory.integral_mul_const]
  have hcint : (∫ θ in Set.Icc 0 (Real.pi / 2),
        α * (Work.Spaces.Gam α θ * Work.Spaces.K θ) / Work.Spaces.c α) = α := by
    rw [MeasureTheory.integral_div, MeasureTheory.integral_const_mul]
    have hval : (∫ θ in Set.Icc 0 (Real.pi / 2),
        Work.Spaces.Gam α θ * Work.Spaces.K θ) = Work.Spaces.c α := rfl
    rw [hval, mul_div_assoc, div_self hc, mul_one]
  rw [hcint]

theorem L12_zero (z : ℝ) : Work.Construction.L12 (fun _ _ => (0 : ℝ)) z = 0 := by
  rw [Work.Construction.L12, Work.FM.L12]
  have h0 : ∀ s : ℝ, Work.FM.L12dens Work.Spaces.K (fun _ _ => (0 : ℝ)) s = 0 := by
    intro s
    simp [Work.FM.L12dens]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s _ => h0 s)]
  simp

theorem L12_Fstar_eq_of_c_ne {α : ℝ} (hc : Work.Spaces.c α ≠ 0) {z : ℝ} (hz : -1 < z) :
    Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) := by
  rw [Work.Construction.L12, Work.FM.L12]
  rw [MeasureTheory.setIntegral_congr_fun (s := Set.Ioi z) measurableSet_Ioi
        (fun s _ => show Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α) s
            = α * (Work.FM.Fstar s / s) from L12dens_Fstar_of_c_ne hc s)]
  rw [MeasureTheory.integral_const_mul,
    Work.FTS.Nonlinear.FstarPkg.integral_Ioi_Fstar_div_of_gt_neg_one z hz]
  ring

theorem FK_Fstar_of_c_ne {α : ℝ} (hc : Work.Spaces.c α ≠ 0) (z : ℝ) :
    Work.Construction.FK (Work.Construction.Fstar α) z = α * (2 * z / (1 + z) ^ 2) := by
  rw [Work.Construction.FK]
  have h1 : ∀ θ ∈ Work.Spaces.Iθ,
      Work.Construction.Fstar α z θ * Work.Spaces.K θ
        = (α * Work.FM.Fstar z / Work.Spaces.c α) * (Work.Spaces.Gam α θ * Work.Spaces.K θ) := by
    intro θ _
    simp only [Work.Construction.Fstar]
    ring
  rw [MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc h1]
  rw [MeasureTheory.integral_const_mul]
  rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ * Work.Spaces.K θ) = Work.Spaces.c α
      from rfl]
  rw [div_mul_cancel₀ (α * Work.FM.Fstar z) hc, Work.FM.Fstar]

/-! ## `Θ α (F_*)` is `C^∞` on the open quadrant, for every `α` -/

theorem smoothQuad_Theta_Fstar_all (α : ℝ) :
    Work.FTS.LocData.SmoothQuad (Work.Construction.Theta α (Work.Construction.Fstar α)) := by
  by_cases hα : α = 0
  · have hfun : Work.Construction.Theta α (Work.Construction.Fstar α) = fun _ _ => (0 : ℝ) := by
      funext z θ
      simp [Work.Construction.Theta, hα]
    rw [hfun]
    exact contDiffOn_const
  · by_cases hc : Work.Spaces.c α = 0
    · have hF : Work.Construction.Fstar α = fun _ _ => (0 : ℝ) := by
        funext z θ
        exact Fstar_eq_zero_of_c_eq_zero hc z θ
      have hfun : Work.Construction.Theta α (Work.Construction.Fstar α) = fun _ _ => (0 : ℝ) := by
        funext z θ
        simp only [Work.Construction.Theta, hF, Work.Construction.s2]
        rw [L12_zero z]
        ring
      rw [hfun]
      exact contDiffOn_const
    · have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun p : ℝ × ℝ => Real.sin (2 * p.2) / (2 * (1 + p.1))) Work.Spaces.quadU := by
        have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
            (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.Spaces.quadU :=
          (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
        have hden : ContDiffOn ℝ Work.Stability.smoothOrder
            (fun p : ℝ × ℝ => 2 * (1 + p.1)) Work.Spaces.quadU :=
          contDiffOn_const.mul (contDiffOn_const.add contDiffOn_fst)
        have hne : ∀ p ∈ Work.Spaces.quadU, 2 * (1 + p.1) ≠ 0 := by
          intro p hp
          have hp1 : (0 : ℝ) < 1 + p.1 := by
            have := Set.mem_Ioi.mp hp.1; linarith
          positivity
        exact hnum.div hden hne
      refine hsmooth.congr ?_
      intro p hp
      obtain ⟨z, θ⟩ := p
      have hz : -1 < z := Set.mem_Ioi.mp hp.1
      simp only [Function.uncurry, Work.Construction.Theta, Work.Construction.s2]
      rw [L12_Fstar_eq_of_c_ne hc hz]
      field_simp
      ring

/-! ## The measurability of the atoms -/

theorem aesm_g_ops {α : ℝ} {g : ℝ → ℝ → ℝ} (hgal : Work.FTS.Nonlin.GalClass α g) :
    AEStronglyMeasurable (Function.uncurry g) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry (Work.Spaces.pth g)) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry (Work.Spaces.Dz g)) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry (Work.Spaces.Dth g)) QdMeas := by
  have hsm : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hio := Work.Spaces.isOpen_quadU
  exact ⟨aesm_of_smoothQuad hsm,
    aesm_of_smoothQuad (Work.FTS.LocData.contDiffOn_pth hio hsm),
    aesm_of_smoothQuad (Work.FTS.LocData.contDiffOn_Dz hio hsm),
    aesm_of_smoothQuad (Work.FTS.LocData.contDiffOn_Dth hio hsm)⟩

theorem aesm_F_ops (α : ℝ) :
    AEStronglyMeasurable (Function.uncurry (Work.Construction.Fstar α)) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry (Work.Spaces.pth (Work.Construction.Fstar α)))
      QdMeas ∧
    AEStronglyMeasurable (Function.uncurry (Work.Spaces.Dz (Work.Construction.Fstar α)))
      QdMeas := by
  have hsm : Work.FTS.LocData.SmoothQuad (Work.Construction.Fstar α) :=
    Work.FTS.LocData.SmoothQuad_Fstar α
  have hio := Work.Spaces.isOpen_quadU
  exact ⟨aesm_of_smoothQuad hsm,
    aesm_of_smoothQuad (Work.FTS.LocData.contDiffOn_pth hio hsm),
    aesm_of_smoothQuad (Work.FTS.LocData.contDiffOn_Dz hio hsm)⟩

theorem aesm_Tg_ops {α Ce : ℝ} {g Φg : Work.FTS.Galerkin.Fn}
    (hell : Work.FTS.Nonlin.EllPkgG α Ce g Φg) :
    AEStronglyMeasurable (Function.uncurry (Work.Construction.Rop α
        (Work.FTS.Nonlin.PhiTg α g Φg))) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry (Work.Construction.Uop α
        (Work.FTS.Nonlin.PhiTg α g Φg))) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry (Work.Construction.Vop
        (Work.FTS.Nonlin.PhiTg α g Φg))) QdMeas :=
  ⟨aesm_of_smoothQuad hell.R.1.1,
    aesm_Uop_of_div (aesm_of_smoothQuad hell.U.1.1),
    aesm_of_smoothQuad hell.V.1.1⟩

theorem aesm_FK_ops {α : ℝ} {g : ℝ → ℝ → ℝ} (hgal : Work.FTS.Nonlin.GalClass α g) :
    AEStronglyMeasurable (Function.uncurry (fun z θ => Work.Construction.FK g z)) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry (fun z θ =>
      Work.Construction.FK (Work.Construction.Fstar α) z)) QdMeas :=
  ⟨aesm_FK (aesm_of_smoothQuad hgal.reg.1),
    aesm_FK (aesm_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α))⟩

theorem PvecMeas {α Ce Cs : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn}
    (hgal : Work.FTS.Nonlin.GalClass α g) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (hell : Work.FTS.Nonlin.EllPkgG α Ce g Φg) :
    (∀ k : Fin 20, AEMeasurable (Function.uncurry (fun r θ =>
        Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k r θ))
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) ∧
    (∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), ∀ k : Fin 20, AEMeasurable
        (fun θ : ℝ => ENNReal.ofReal |Work.Spaces.K θ
          * Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k r θ|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    (∀ k : Fin 20, AEMeasurable
        (fun r : ℝ => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ
          * Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k r θ|)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) := by
  obtain ⟨hg, hpthg, hDzg, hDthg⟩ := aesm_g_ops hgal
  obtain ⟨hF, hpthF, hDzF⟩ := aesm_F_ops α
  obtain ⟨hRopTg, hUopTg, hVopTg⟩ := aesm_Tg_ops hell
  obtain ⟨hFKg, hFKF⟩ := aesm_FK_ops hgal
  obtain ⟨hRopTs, hUopTs, hVopTs⟩ := aesm_star_ops hs.smooth (smoothQuad_Theta_Fstar_all α)
  -- the twenty pieces of `pv`
  have hpiece : ∀ k : Fin 20, AEStronglyMeasurable (Function.uncurry (fun r θ =>
      Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k r θ)) QdMeas := by
    intro k
    fin_cases k
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTg α g Φg) z θ * g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTg hg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTg α g Φg) z θ * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTg hF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTs α Φs) z θ * g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTs hg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTs α Φs) z θ * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTs hF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTg α g Φg) z θ * pth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTg hpthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTg α g Φg) z θ * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTg hpthF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTs α Φs) z θ * pth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTs hpthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTs α Φs) z θ * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTs hpthF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTg α g Φg) z θ * Dz g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTg hDzg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTg α g Φg) z θ * Dz (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTg hDzF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTs α Φs) z θ * Dz g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTs hDzg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTs α Φs) z θ * Dz (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTs hDzF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * FK g z * Dth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_mul hFKg hDthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * s2 θ * FK g z * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_s2_mul (aesm_mul hFKg hpthF)))
        (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * FK (Fstar α) z * Dth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_mul hFKF hDthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * s2 θ * FK (Fstar α) z * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_s2_mul (aesm_mul hFKF hpthF)))
        (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK g z * g z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKg hg))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK g z * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKg hF))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK (Fstar α) z * g z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKF hg))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK (Fstar α) z * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKF hF))) (fun z θ => ?_)
      ring
  -- the `ENNReal`-valued versions, with the angular weight `K`
  have hENN : ∀ k : Fin 20, AEStronglyMeasurable (Function.uncurry (fun r θ =>
      ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlinear.Pieces.rl1Tools.pv
        α g Φs Φg k r θ|)) QdMeas := by
    intro k
    have hKcont : Continuous fun p : ℝ × ℝ => Work.Spaces.K p.2 := by
      simp only [Work.Spaces.K]; fun_prop
    have hK : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.K p.2) QdMeas :=
      hKcont.aestronglyMeasurable
    have hpair : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (Work.Spaces.K p.2, Function.uncurry (fun r θ =>
          Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k r θ) p)) QdMeas :=
      hK.prodMk (hpiece k)
    have hcomp : Continuous (fun q : ℝ × ℝ => ENNReal.ofReal |q.1 * q.2|) :=
      ENNReal.continuous_ofReal.comp
        (continuous_abs.comp (continuous_fst.mul continuous_snd))
    exact hcomp.comp_aestronglyMeasurable hpair
  refine ⟨fun k => (hpiece k).aemeasurable, ?_, ?_⟩
  · filter_upwards [eventually_all.2 fun k => (hENN k).prodMk_left] with r hr
    intro k
    exact (hr k).aemeasurable
  · intro k
    exact (hENN k).aemeasurable.lintegral_prod_right

end Work.FTS.Nonlinear.Pieces.rl1Tools
