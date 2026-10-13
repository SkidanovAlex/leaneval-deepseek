import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.CoreResiduals.Defs
import Submission.Work.ConstructionInstance.solVort_holder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.CoreResiduals

/-! ## Uniform Hölder-constant calculus

The three lemmas below are the quantitative form of the chain
`Work.ConstructionInstance.solVort_holder` uses: they expose the *constant* produced at every step
so that it can be bounded uniformly over a time strip. -/

/-- **Monotonicity of `HolderWith` in its constant.** -/
theorem holderWith_le_const {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {C C' : NNReal} {r : NNReal} {f : X → Y} (h : HolderWith C r f) (hCC : C ≤ C') :
    HolderWith C' r f :=
  fun x y => le_trans (h x y) (mul_le_mul_left (ENNReal.coe_le_coe.mpr hCC) _)

/-- **Composition with a dilation of the domain.**  Precomposing an `r`-Hölder map with
`x ↦ b • x` (`b ≥ 0`) multiplies the Hölder constant by `b ^ r`. -/
theorem holderWith_comp_smul {α : NNReal} {Y : Type*} [PseudoMetricSpace Y]
    {f : EuclideanSpace ℝ (Fin 3) → Y} {C : NNReal} (hf : HolderWith C α f) {b : ℝ}
    (hb : 0 ≤ b) :
    HolderWith (C * Real.toNNReal (b ^ (α : ℝ))) α (fun x => f (b • x)) := by
  apply Work.Stability.holderWith_of_dist_le
  intro x y
  have h1 := hf.dist_le (b • x) (b • y)
  rw [dist_smul₀, Real.norm_of_nonneg hb, Real.mul_rpow hb dist_nonneg] at h1
  calc dist (f (b • x)) (f (b • y))
      ≤ (C : ℝ) * (b ^ (α : ℝ) * dist x y ^ (α : ℝ)) := h1
    _ = ((C * Real.toNNReal (b ^ (α : ℝ)) : NNReal) : ℝ) * dist x y ^ (α : ℝ) := by
        rw [NNReal.coe_mul, Real.coe_toNNReal (b ^ (α : ℝ)) (Real.rpow_nonneg hb _)]
        ring

/-- **Bounded Lipschitz scalar times bounded Hölder field**, with an *explicit* constant
`Mc·C + MA·max K (2Mc)`.  This is the quantitative companion of
`Work.Stability.holder_smul_of_bounded_lipschitz`, whose constant is existential and therefore
useless for a strip-uniform statement. -/
theorem holderWith_smul_of_bounded_lipschitz {X : Type*} [PseudoMetricSpace X] {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] {α : NNReal} (hα : α ≤ 1) {K : NNReal}
    {c : X → ℝ} {A : X → E} {Mc MA : ℝ} (hMc0 : 0 ≤ Mc) (hc : ∀ x, |c x| ≤ Mc)
    (hcl : LipschitzWith K c) (hMA0 : 0 ≤ MA) (hA : ∀ x, ‖A x‖ ≤ MA) {C : NNReal}
    (hAC : HolderWith C α A) :
    HolderWith ⟨Mc * (C : ℝ) + MA * max (K : ℝ) (2 * Mc),
      add_nonneg (mul_nonneg hMc0 C.coe_nonneg)
        (mul_nonneg hMA0 (le_trans (by linarith) (le_max_right _ _)))⟩ α (c • A) := by
  refine Work.Stability.holderWith_of_dist_le fun x y => ?_
  have hcx : |c x| ≤ Mc := hc x
  have hcy : |c y| ≤ Mc := hc y
  have hAy : ‖A y‖ ≤ MA := hA y
  have hdA : dist (A x) (A y) ≤ (C : ℝ) * dist x y ^ (α : ℝ) := hAC.dist_le x y
  have hdc1 : |c x - c y| ≤ (K : ℝ) * dist x y := by
    have h := hcl.dist_le_mul x y
    rwa [Real.dist_eq] at h
  have hdc2 : |c x - c y| ≤ 2 * Mc := by
    calc |c x - c y| = dist (c x) (c y) := by rw [Real.dist_eq]
      _ ≤ dist (c x) 0 + dist 0 (c y) := dist_triangle _ _ _
      _ = |c x| + |c y| := by rw [Real.dist_eq, Real.dist_eq, sub_zero, zero_sub, abs_neg]
      _ ≤ 2 * Mc := by linarith
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  have hmax0 : 0 ≤ max (K : ℝ) (2 * Mc) := le_trans (by linarith) (le_max_right _ _)
  have hdc : |c x - c y| ≤ max (K : ℝ) (2 * Mc) * dist x y ^ (α : ℝ) := by
    rcases lt_or_ge (dist x y) 1 with hd | hd
    · have hs : dist x y ≤ dist x y ^ (α : ℝ) :=
        Real.self_le_rpow_of_le_one dist_nonneg (le_of_lt hd) (by exact_mod_cast hα)
      calc |c x - c y| ≤ (K : ℝ) * dist x y := hdc1
        _ ≤ (K : ℝ) * dist x y ^ (α : ℝ) := mul_le_mul_of_nonneg_left hs hK0
        _ ≤ max (K : ℝ) (2 * Mc) * dist x y ^ (α : ℝ) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _)
    · have hs : (1 : ℝ) ≤ dist x y ^ (α : ℝ) := Real.one_le_rpow hd α.coe_nonneg
      calc |c x - c y| ≤ 2 * Mc := hdc2
        _ ≤ (2 * Mc) * dist x y ^ (α : ℝ) := le_mul_of_one_le_right (by linarith) hs
        _ ≤ max (K : ℝ) (2 * Mc) * dist x y ^ (α : ℝ) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg dist_nonneg _)
  have hdec : c x • A x - c y • A y = c x • (A x - A y) + (c x - c y) • A y := by
    rw [smul_sub, sub_smul]; abel
  calc dist (c x • A x) (c y • A y) = ‖c x • (A x - A y) + (c x - c y) • A y‖ := by
        rw [dist_eq_norm, hdec]
    _ ≤ ‖c x • (A x - A y)‖ + ‖(c x - c y) • A y‖ := norm_add_le _ _
    _ = |c x| * dist (A x) (A y) + |c x - c y| * ‖A y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, dist_eq_norm]
    _ ≤ Mc * ((C : ℝ) * dist x y ^ (α : ℝ))
          + (max (K : ℝ) (2 * Mc) * dist x y ^ (α : ℝ)) * MA :=
        add_le_add (mul_le_mul hcx hdA dist_nonneg hMc0)
          (mul_le_mul hdc hAy (norm_nonneg _) (mul_nonneg hmax0 (Real.rpow_nonneg dist_nonneg _)))
    _ = (Mc * (C : ℝ) + MA * max (K : ℝ) (2 * Mc)) * dist x y ^ (α : ℝ) := by ring

/-! ## The strip statement -/

/-- **Uniform-in-`t` Hölder regularity of the constructed vorticity on a time strip.**
`Work.ConstructionInstance.solVort_holder` gives `Holder α (solVort P · t)` for each `t` with a
`t`-dependent constant; on the strip `[0,S]`, `S < T`, the modulation satisfies `λ̄ ≥ (T-S)/2 > 0`,
and the dilation identity `solVort P x t = b • omegaS p g (b • x)` with `b^p = λ̄(t)^{-1}` makes the
Hölder constant `b^{1+α}·(constant of omegaS)` — bounded on the strip. -/
theorem solVort_holder_strip {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    {S : ℝ} (hS : 0 < S) (hST : S < P.T) :
    ∃ H : NNReal, ∀ t ∈ Set.Icc (0 : ℝ) S,
      HolderWith H α (fun x : Work.LWP.R3 => Work.ConstructionInstance.solVort P x t) := by
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
  -- the strip lower bound on the modulation, and the uniform dilation factor it gives
  let δ : ℝ := (P.T - S) / 2
  have hδdef : δ = (P.T - S) / 2 := rfl
  have hδ : 0 < δ := by rw [hδdef]; linarith
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
  refine ⟨Hcut * δinv, fun t ht => ?_⟩
  have htIco : t ∈ Set.Ico 0 P.T := ⟨ht.1, lt_of_le_of_lt ht.2 hST⟩
  have hδle : δ ≤ P.lam t := by
    have h1 : δ ≤ (P.T - t) / 2 := by rw [hδdef]; linarith [ht.2]
    exact le_trans h1 (P.hlam_low t htIco)
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
  -- the scalar `λ̄(t)^{-1}` is uniformly bounded by `δ^{-1}` on the strip
  refine holderWith_le_const hslice' ?_
  refine mul_le_mul_of_nonneg_left ?_ (zero_le : (0 : NNReal) ≤ Hcut)
  rw [Real.nnnorm_of_nonneg (inv_nonneg.mpr hlt.le)]
  exact (inv_le_inv₀ hlt hδ).mpr hδle

end Work.CoreResiduals
