import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.CoreResiduals.Defs
import Submission.Work.CoreResiduals.solVort_holder_strip
import Submission.Work.ConstructionInstance.solVort_holder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- Uniform `α`-Hölder regularity of the slices wherever the modulation is bounded below: for every `δ > 0` a single constant `H` works for every `t : ℝ` with `δ ≤ P.lam t`. No time interval is mentioned (so this also covers times `t < 0` of the half-window, where the strip lemma `solVort_holder_strip` cannot be applied); it is its quantitative strengthening, obtained by taking `δ = (T-S)/2` there via `ProfileData.hlam_low`.

Template: `Submission/Work/CoreResiduals/solVort_holder_strip.lean` proves exactly this with `hδle : δ ≤ P.lam t` derived from `hlam_low` and `t ∈ Icc 0 S`; replace that derivation by the hypothesis. Everything else is verbatim: the dilation factor `b = (P.lam t)⁻¹ ^ (1 / profExp α)` with `b ^ profExp α = (P.lam t)⁻¹`; `b ≤ bmax` with `bmax = (δ⁻¹) ^ (1 / profExp α)` (`Real.rpow_le_rpow` + `inv_le_inv₀ hlt hδ`); the dilation identity `solVort P x t = (P.lam t)⁻¹ • (Work.Stability.cutFactor P.L x • Work.ConstructionInstance.omegaS (profExp α) P.g (b • x))` (`solVort_holder_rho_smul`, `_theta_smul`, `_eTheta_smul`, `omegaS_apply'`, `omegaSz_apply`); the global datum regularity `holder_omegaS_of_data`; the datum bound `omegaS_norm_le` with `MA = 20 * profExp α + P.Cg`; and the calculus lemmas `holderWith_comp_smul`, `holderWith_smul_of_bounded_lipschitz` (`Mc = 1`, `Kφ` from `cutFactor_lipschitz`) and `holderWith_le_const` of that module. The constant is `H := Hcut * ↑⟨δ⁻¹, _⟩` with `Hcut := 1 * (C₀ * Real.toNNReal (bmax ^ (α:ℝ))) + MA * max (Kφ:ℝ) 2`, where `C₀` is the constant from `holder_omegaS_of_data`; the last step is `HolderWith.smul (P.lam t)⁻¹` plus `‖(P.lam t)⁻¹‖₊ ≤ δ⁻¹` (`Real.nnnorm_of_nonneg`, `inv_le_inv₀ hlt hδ`). -/
theorem solVort_holder_of_lam_ge {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ H : NNReal, ∀ t : ℝ, δ ≤ P.lam t →
      HolderWith H α (fun x : Work.CoreResiduals.R3 => Work.ConstructionInstance.solVort P x t) := by
  have hp : 0 < Work.ConstructionInstance.profExp α :=
    Work.ConstructionInstance.profExp_pos P.hα
  have hp1 : Work.ConstructionInstance.profExp α ≤ 1 := by
    rw [Work.ConstructionInstance.profExp]; linarith [P.hα13]
  have hα1 : α ≤ 1 := by
    rw [← NNReal.coe_le_coe]; push_cast; linarith [P.hα13]
  -- a *fixed* Hölder constant for the self-similar datum
  obtain ⟨C₀, hC₀⟩ : Holder α
      (Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g) :=
    Work.ConstructionInstance.holder_omegaS_of_data P.hα P.hα13 P.hCv P.hLg P.hLθ
      P.hvt P.hquad0 P.hquad P.hvan P.hzk P.hzth
      (ContDiffOn.of_le P.hsmooth (by simp))
  -- the Lipschitz constant of the cut-off factor
  obtain ⟨Kφ, hKφ⟩ := Work.Stability.cutFactor_lipschitz P.hL
  -- the uniform dilation factor produced by the lower bound `δ ≤ λ̄(t)`
  let bmax : ℝ := (δ⁻¹) ^ (1 / Work.ConstructionInstance.profExp α)
  have hbmax0 : 0 ≤ bmax := Real.rpow_nonneg (inv_nonneg.mpr hδ.le) _
  let CAdil : NNReal := C₀ * Real.toNNReal (bmax ^ (α : ℝ))
  let MA : ℝ := 20 * Work.ConstructionInstance.profExp α + P.Cg
  have hMAdef : MA = 20 * Work.ConstructionInstance.profExp α + P.Cg := rfl
  have hMA0 : 0 ≤ MA := by rw [hMAdef]; linarith [hp.le, P.hCg]
  let Hcut : NNReal := ⟨1 * (CAdil : ℝ) + MA * max (Kφ : ℝ) (2 * 1),
    add_nonneg (by norm_num)
      (mul_nonneg hMA0 (le_trans (by linarith) (le_max_right _ _)))⟩
  let δinv : NNReal := ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩
  refine ⟨Hcut * δinv, fun t hδle => ?_⟩
  have hlt : 0 < P.lam t := lt_of_lt_of_le hδ hδle
  -- the dilation factor `b = λ̄(t)^{-1/p}`, uniformly bounded by `bmax`
  let b : ℝ := (P.lam t)⁻¹ ^ (1 / Work.ConstructionInstance.profExp α)
  have hb : 0 < b := Real.rpow_pos_of_pos (inv_pos.mpr hlt) _
  have hb_eq : b = (P.lam t)⁻¹ ^ (1 / Work.ConstructionInstance.profExp α) := rfl
  have hbmax_eq : bmax = (δ⁻¹) ^ (1 / Work.ConstructionInstance.profExp α) := rfl
  have hbp : b ^ Work.ConstructionInstance.profExp α = (P.lam t)⁻¹ := by
    rw [hb_eq, ← Real.rpow_mul (inv_nonneg.mpr hlt.le)
        (1 / Work.ConstructionInstance.profExp α) (Work.ConstructionInstance.profExp α),
      div_mul_cancel₀ 1 (ne_of_gt hp), Real.rpow_one]
  have hb_le_bmax : b ≤ bmax := by
    rw [hb_eq, hbmax_eq]
    exact Real.rpow_le_rpow (inv_nonneg.mpr hlt.le)
      ((inv_le_inv₀ hlt hδ).mpr hδle) (by positivity)
  have hbα : b ^ (α : ℝ) ≤ bmax ^ (α : ℝ) :=
    Real.rpow_le_rpow hb.le hb_le_bmax α.coe_nonneg
  -- the dilation identity for the cylindrical coordinates
  have hz : ∀ x : Work.LWP.R3,
      Work.Cyl.rho (b • x) ^ Work.ConstructionInstance.profExp α
        = Work.Cyl.rho x ^ Work.ConstructionInstance.profExp α / P.lam t := by
    intro x
    rw [Work.ConstructionInstance.solVort_holder_rho_smul hb.le,
      Real.mul_rpow hb.le (Work.Cyl.rho_nonneg x), hbp, div_eq_mul_inv, mul_comm ((P.lam t)⁻¹)]
  have hω : ∀ x : Work.LWP.R3,
      Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g (b • x)
        = Work.ConstructionInstance.omegaSz (Work.ConstructionInstance.profExp α) P.g
            (Work.Cyl.rho x ^ Work.ConstructionInstance.profExp α / P.lam t) x := by
    intro x
    rw [Work.ConstructionInstance.omegaS_apply', Work.ConstructionInstance.omegaSz_apply,
      Work.ConstructionInstance.solVort_holder_theta_smul hb x,
      Work.ConstructionInstance.solVort_holder_eTheta_smul hb x, hz x]
  have hid : ∀ x : Work.LWP.R3, Work.ConstructionInstance.solVort P x t
      = (P.lam t)⁻¹ • (Work.Stability.cutFactor P.L x •
          Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g (b • x)) := by
    intro x
    rw [Work.ConstructionInstance.solVort_apply, Work.Stability.cutFactor_apply, hω x]
  -- the dilated datum is `α`-Hölder with the uniform constant `CAdil`
  have hH : HolderWith CAdil α (fun x : Work.LWP.R3 =>
      Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g (b • x)) := by
    have h1 : HolderWith (C₀ * Real.toNNReal (b ^ (α : ℝ))) α
        (fun x : Work.LWP.R3 =>
          Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g (b • x)) :=
      holderWith_comp_smul hC₀ hb.le
    refine holderWith_le_const h1 ?_
    have hCAdil : CAdil = C₀ * Real.toNNReal (bmax ^ (α : ℝ)) := rfl
    rw [hCAdil]
    exact mul_le_mul_of_nonneg_left (Real.toNNReal_le_toNNReal hbα)
      (zero_le : (0 : NNReal) ≤ C₀)
  -- the dilated datum is uniformly bounded by `MA`
  have hbd : ∀ x : Work.LWP.R3,
      ‖Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g (b • x)‖ ≤ MA := by
    intro x
    have hMθ : ∀ θ ∈ Work.Spaces.Iθ, 20 * Work.ConstructionInstance.profExp α
        * Work.ConstructionInstance.Gamma (Work.ConstructionInstance.profExp α / 3) θ + P.Cg
          ≤ MA := by
      intro θ hθ
      have hG : Work.ConstructionInstance.Gamma (Work.ConstructionInstance.profExp α / 3) θ ≤ 1 :=
        Work.ConstructionInstance.Gamma_le_one (by positivity) hθ
      have hMA : MA = 20 * Work.ConstructionInstance.profExp α + P.Cg := rfl
      rw [hMA]; nlinarith [hG, hp.le, P.hCg]
    exact Work.ConstructionInstance.omegaS_norm_le hp hp1 (Work.ConstructionInstance.bdd_g P)
      P.hCg hMθ (b • x)
  -- multiplying by the bounded Lipschitz cut-off keeps the constant uniform
  have hcut : HolderWith Hcut α (fun x : Work.LWP.R3 =>
      Work.Stability.cutFactor P.L x •
        Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g (b • x)) := by
    refine holderWith_smul_of_bounded_lipschitz hα1 (K := Kφ) (Mc := 1) (MA := MA)
      (C := CAdil) (by norm_num) ?_ hKφ hMA0 hbd hH
    intro x
    rw [Work.Stability.cutFactor_apply, abs_of_nonneg (Work.Stability.chi_nonneg _)]
    exact Work.Stability.chi_le_one _
  have hslice : HolderWith (Hcut * ‖(P.lam t)⁻¹‖₊) α
      ((P.lam t)⁻¹ • (fun x : Work.LWP.R3 => Work.Stability.cutFactor P.L x •
        Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g (b • x))) :=
    HolderWith.smul (P.lam t)⁻¹ hcut
  have hslice' : HolderWith (Hcut * ‖(P.lam t)⁻¹‖₊) α
      (fun x : Work.LWP.R3 => Work.ConstructionInstance.solVort P x t) := by
    rw [funext hid]
    exact hslice
  -- the scalar `λ̄(t)^{-1}` is uniformly bounded by `δ^{-1}`
  refine holderWith_le_const hslice' ?_
  refine mul_le_mul_of_nonneg_left ?_ (zero_le : (0 : NNReal) ≤ Hcut)
  rw [Real.nnnorm_of_nonneg (inv_nonneg.mpr hlt.le)]
  exact (inv_le_inv₀ hlt hδ).mpr hδle

end Work.CoreResiduals
