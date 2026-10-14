import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.IsEpsSolPQ.EpsSq_intervalIntegral_le_sqrt
import Submission.Work.FTS_StreamBdry.Inputs.residual_slot_jetsB
import Submission.Work.FTS_StreamBdry.Inputs.slice_assy

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Flow5Leaves/IP4_JfamP_hasDerivWithinAt_of_flow.lean` — LEAF-C (level-four product rule)

The level-four energy identity, i.e. the differentiability of the `IP4`-energy of the
projected-mollified family along a regular `P₀`-solution.  This is the level-four twin of the
*proved* `E4R3/Flow5.lean` `rawE6_hasDerivWithinAt_of_flow` (which does the same for the
level-six form `IP6o`): the proof is the abstract product rule for a symmetric bilinear form.

Ingredients (all available in this workspace, and all `sorry`-free):

* `EpsFlowP.deriv` gives the `ℋ⁶`-differentiability of the *raw* flow `slice g` with derivative
  `epsRHSP τ` (a junk-proof `HkDerivWithin`);
* the projected mollifier `W_ε = Pz ∘ J_ε` is **linear** on the honest class: it is additive
  (`EpsLocalPStar.Wp_sub_eq_mem`: the difference of the projected mollifications is the projected
  mollification of the difference), and homogeneous (`PzJepsCalc.PzJeps_const_mul`); hence the
  remainder of the projected flow is exactly `Pz (J_ε (remainder of the raw flow))`, and it is
  priced in `ℋ⁴` by the `ℋ⁶`-size of that remainder (`PzJepsCalc.PzJeps_pricing`);
* `IP4` is symmetric (`IP4Algebra.IP4_symm_fts`), additive on the open class `HQo α 4`
  (`IP4Algebra.IP4_add_open`), homogeneous (`IPGen.ip4_smul`) and Cauchy–Schwarz bounded on
  `HQo α 4` (`IP4Algebra.IP4_cs_HQo`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Flow5Leaves

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps
open Work.FTS.EllipticEst
open Work.Spaces
open Work.FTS.VocabO
open Work.FTS.StrongEps.EpsE4Thr.E4R5

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "IP4" => Work.FTS.CoercivityFix.Assembly.IP4

/-- **LEAF-C (level-four product rule)**: along a regular `P₀`-solution the `IP4`-energy of the
projected mollified family is differentiable at `τ`, with derivative twice the pairing of the
projected mollified right-hand side with the slice at `τ`.

The proof is the abstract product rule for the bounded symmetric bilinear form `IP4` on the open
class `HQo α 4` (exactly as in `Flow5.rawE6_hasDerivWithinAt_of_flow`, but with the `ℋ⁶`-valued
`HkDerivWithin` of the *raw* flow transported to the projected family through the linearity
(`Wp_sub_eq_mem`) and the pricing (`PzJeps_pricing`) of `Pz ∘ J_ε`). -/
theorem IP4_JfamP_hasDerivWithinAt_of_flow {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hc₁' : 0 ≤ c₁') (hc₂' : 0 ≤ c₂') (hc₁'' : 0 ≤ c₁'') (hc₂'' : 0 ≤ c₂'')
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hε : 0 < ε)
    (hε1 : ε ≤ 1)
    (hreg : Work.FTS.StrongEps.EpsRegP α ρ ε T g)
    (hF : Work.FTS.StrongEps.EpsE4Thr.E4R5.EpsFlowP α ρ ε T Φs E g)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 T) :
    HasDerivWithinAt
      (fun s => Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s))
      (2 * Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
        (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
          (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ)))
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ))
      (Set.Icc 0 T) τ := by
  have hα0 : 0 < α := hα.1
  -- the pricing of the projected mollified profile and the three `IP4`-facts
  obtain ⟨K, hKpos, hKpricing⟩ := PzJeps_pricing (ρ := ρ) hρ hα hε hε1
  obtain ⟨CC, hCCpos, hcs⟩ := IP4_cs_HQo c₁ c₂ c₁' c₂' c₁'' c₂''
  -- ## the data at the fake time `τ`
  set V : Fn := epsRHSP α ρ ε Φs E g τ with hVdef
  set b : Fn := slice (JfamP ρ ε g) τ with hbdef
  set v : Fn := Pz (Jeps ρ ε V) with hvdef
  set F : ℝ → ℝ := fun s => IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
    (slice (JfamP ρ ε g) s) (slice (JfamP ρ ε g) s) with hFdef
  have hb : HQo α 4 b := (hKpricing (hreg.2 τ hτ).1 (hreg.2 τ hτ).2.1).1
  have hv : HQo α 4 v := (hKpricing (hF.rhs τ hτ).1 (hF.rhs τ hτ).2).1
  have hsmτ : SmoothOpen (slice g τ) := (hreg.2 τ hτ).1
  have hmτ4 : HkMem α 4 (slice g τ) :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmτ 4 (by norm_num) (hreg.2 τ hτ).2.1
  have hsmV : SmoothOpen V := (hF.rhs τ hτ).1
  have hmV6 : HkMem α 6 V := (hF.rhs τ hτ).2
  -- ## the structural facts about `Pz ∘ J_ε`
  have Wp_sub : ∀ {u w : Fn}, SmoothOpen u → SmoothOpen w → HkMem α 4 u → HkMem α 4 w →
      Pz (Jeps ρ ε u) - Pz (Jeps ρ ε w) = Pz (Jeps ρ ε (fun z θ => u z θ - w z θ)) := by
    intro u w hu hw hmu hmw
    simpa only [Work.FTS.StrongEps.EpsRLX.Wp] using
      (Work.FTS.StrongEps.EpsLocalPStar.Wp_sub_eq_mem (α := α) hα hρ hε hu hw hmu hmw)
  -- ## the linear structure of the projected flow
  have hstruct : ∀ s ∈ Set.Icc 0 T, HQo α 6 (rem (slice g) V s τ) →
      (fun z θ => slice (JfamP ρ ε g) s z θ - b z θ)
        = fun z θ => Pz (Jeps ρ ε (rem (slice g) V s τ)) z θ + (s - τ) * v z θ := by
    intro s hs hR6
    have hcVsm : SmoothOpen (fun z θ => (s - τ) * V z θ) :=
      Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen (s - τ) hsmV
    have hcV6 : HkMem α 6 (fun z θ => (s - τ) * V z θ) :=
      Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (s - τ) hmV6
    have hcV4 : HkMem α 4 (fun z θ => (s - τ) * V z θ) :=
      Work.FTS.OpenPkg.HkMem_mono_open hcVsm 4 (by norm_num) hcV6
    have hRsm : SmoothOpen (rem (slice g) V s τ) := hR6.1
    have hR4 : HkMem α 4 (rem (slice g) V s τ) :=
      Work.FTS.OpenPkg.HkMem_mono_open hRsm 4 (by norm_num) hR6.2
    have hsumSm : SmoothOpen (fun z θ => rem (slice g) V s τ z θ + (s - τ) * V z θ) :=
      Work.FTS.NonlinRows.smoothOpen_add hRsm hcVsm
    have hsum4 : HkMem α 4 (fun z θ => rem (slice g) V s τ z θ + (s - τ) * V z θ) :=
      Work.FTS.EllipticEst.HkMem_add_open hRsm hcVsm hR4 hcV4
    have step1 : slice (JfamP ρ ε g) s - slice (JfamP ρ ε g) τ
        = Pz (Jeps ρ ε (fun z θ => slice g s z θ - slice g τ z θ)) :=
      Wp_sub (hreg.2 s hs).1 hsmτ
        (Work.FTS.OpenPkg.HkMem_mono_open (hreg.2 s hs).1 4 (by norm_num) (hreg.2 s hs).2.1) hmτ4
    have hsplit : (fun z θ => slice g s z θ - slice g τ z θ)
        = fun z θ => rem (slice g) V s τ z θ + (s - τ) * V z θ := by
      funext z θ
      simp only [rem]
      ring
    have hsub : Pz (Jeps ρ ε (fun z θ => rem (slice g) V s τ z θ + (s - τ) * V z θ))
          - Pz (Jeps ρ ε (fun z θ => (s - τ) * V z θ))
        = Pz (Jeps ρ ε (rem (slice g) V s τ)) := by
      have h := Wp_sub hsumSm hcVsm hsum4 hcV4
      have hcancel : (fun z θ => (rem (slice g) V s τ z θ + (s - τ) * V z θ) - (s - τ) * V z θ)
          = rem (slice g) V s τ := by
        funext z θ
        ring
      rw [hcancel] at h
      exact h
    have hcV : Pz (Jeps ρ ε (fun z θ => (s - τ) * V z θ))
        = fun z θ => (s - τ) * v z θ := by
      rw [PzJeps_const_mul ρ ε (s - τ) V, ← hvdef]
    have hmain : Pz (Jeps ρ ε (fun z θ => rem (slice g) V s τ z θ + (s - τ) * V z θ))
        = Pz (Jeps ρ ε (rem (slice g) V s τ))
          + Pz (Jeps ρ ε (fun z θ => (s - τ) * V z θ)) :=
      sub_eq_iff_eq_add.mp hsub
    calc (fun z θ => slice (JfamP ρ ε g) s z θ - b z θ)
        = slice (JfamP ρ ε g) s - b := by funext z θ; simp only [Pi.sub_apply]
      _ = slice (JfamP ρ ε g) s - slice (JfamP ρ ε g) τ := by rw [hbdef]
      _ = Pz (Jeps ρ ε (fun z θ => slice g s z θ - slice g τ z θ)) := step1
      _ = Pz (Jeps ρ ε (fun z θ => rem (slice g) V s τ z θ + (s - τ) * V z θ)) := by rw [hsplit]
      _ = Pz (Jeps ρ ε (rem (slice g) V s τ))
          + Pz (Jeps ρ ε (fun z θ => (s - τ) * V z θ)) := hmain
      _ = (fun z θ => Pz (Jeps ρ ε (rem (slice g) V s τ)) z θ + (s - τ) * v z θ) := by
          rw [hcV]
          funext z θ
          simp only [Pi.add_apply]
  -- ## the algebraic identity behind the product rule
  have key : ∀ s ∈ Set.Icc 0 T, HQo α 6 (rem (slice g) V s τ) →
      F s - F τ - (s - τ) * (2 * IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α v b)
      = IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
          (fun z θ => slice (JfamP ρ ε g) s z θ - b z θ)
          (fun z θ => slice (JfamP ρ ε g) s z θ - b z θ)
        + 2 * IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (Pz (Jeps ρ ε (rem (slice g) V s τ))) b := by
    intro s hs hR6
    obtain ⟨d, hddef⟩ : ∃ d : Fn, d = fun z θ => slice (JfamP ρ ε g) s z θ - b z θ := ⟨_, rfl⟩
    obtain ⟨rr, hrrdef⟩ : ∃ rr : Fn, rr = Pz (Jeps ρ ε (rem (slice g) V s τ)) := ⟨_, rfl⟩
    rw [← hddef, ← hrrdef]
    have hFs : F s = IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
        (slice (JfamP ρ ε g) s) (slice (JfamP ρ ε g) s) := by simp only [hFdef]
    have hFτ : F τ = IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α b b := by simp only [hFdef, hbdef]
    rw [hFs, hFτ]
    have hX4 : HQo α 4 (slice (JfamP ρ ε g) s) :=
      (hKpricing (hreg.2 s hs).1 (hreg.2 s hs).2.1).1
    have hd : HQo α 4 d := by
      rw [hddef]
      exact Work.FTS.Open3.HQo_sub hX4 hb
    have hsum : HQo α 4 (fun z θ => b z θ + d z θ) := Work.FTS.Open3.HQo_add hb hd
    have he : HQo α 4 (fun z θ => (s - τ) * v z θ) :=
      Work.FTS.Open3.HQo_const_mul hv (s - τ)
    have hrr : HQo α 4 rr := by
      rw [hrrdef]
      exact (hKpricing hR6.1 hR6.2).1
    have hd_eq : d = fun z θ => rr z θ + (s - τ) * v z θ := by
      rw [hddef, hrrdef]
      exact hstruct s hs hR6
    have hXs : slice (JfamP ρ ε g) s = fun z θ => b z θ + d z θ := by
      funext z θ
      rw [hddef]
      ring
    have hs' : IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (slice (JfamP ρ ε g) s) (slice (JfamP ρ ε g) s)
        = IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (fun z θ => b z θ + d z θ)
            (fun z θ => b z θ + d z θ) := by rw [hXs]
    have A1 : IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (fun z θ => b z θ + d z θ)
          (fun z θ => b z θ + d z θ)
        = IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α b (fun z θ => b z θ + d z θ)
          + IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α d (fun z θ => b z θ + d z θ) :=
      IP4_add_open hα0 hb.1 hd.1 hsum.1 hb.2 hd.2 hsum.2
    have A2 : IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α b (fun z θ => b z θ + d z θ)
        = IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α b b + IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α d b :=
      (IP4_symm_fts c₁ c₂ c₁' c₂' c₁'' c₂'' α b (fun z θ => b z θ + d z θ)).trans
        (IP4_add_open hα0 hb.1 hd.1 hb.1 hb.2 hd.2 hb.2)
    have A3' : IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (fun z θ => b z θ + d z θ) d
        = IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α b d + IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α d d :=
      IP4_add_open hα0 hb.1 hd.1 hd.1 hb.2 hd.2 hd.2
    have Sbd : IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α b d = IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α d b :=
      IP4_symm_fts c₁ c₂ c₁' c₂' c₁'' c₂'' α b d
    have A3 : IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α d (fun z θ => b z θ + d z θ)
        = IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α d b + IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α d d :=
      ((IP4_symm_fts c₁ c₂ c₁' c₂' c₁'' c₂'' α d (fun z θ => b z θ + d z θ)).trans A3').trans
        (congrArg (· + IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α d d) Sbd)
    have A4' : IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (fun z θ => rr z θ + (s - τ) * v z θ) b
        = IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α rr b
          + IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (fun z θ => (s - τ) * v z θ) b :=
      IP4_add_open hα0 hrr.1 he.1 hb.1 hrr.2 he.2 hb.2
    have A4'' : IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (fun z θ => (s - τ) * v z θ) b
        = (s - τ) * IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α v b :=
      Work.FTS.IPGen.ip4_smul c₁ c₂ c₁' c₂' c₁'' c₂'' (s - τ) α v b
    have A4 : IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α d b
        = IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α rr b
          + (s - τ) * IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α v b := by
      rw [hd_eq, A4', A4'']
    have hτb : IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (slice (JfamP ρ ε g) τ) (slice (JfamP ρ ε g) τ)
        = IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α b b := by rw [hbdef]
    rw [hs', hτb, A1, A2, A3, A4]
    ring
  -- ## the little-`o` estimate
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  set nb : ℝ := HkNorm α 4 b with hnbdef
  set nv : ℝ := HkNorm α 4 v with hnvdef
  have hnb : 0 ≤ nb := Work.Spaces.HkNorm_nonneg α 4 b
  have hnv : 0 ≤ nv := Work.Spaces.HkNorm_nonneg α 4 v
  set η : ℝ := min 1 (c / (4 * CC * (nb + 1))) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : η ≤ c / (4 * CC * (nb + 1)) := min_le_right _ _
  set η₁ : ℝ := η / (2 * (K + 1)) with hη₁def
  have hη₁ : 0 < η₁ := by rw [hη₁def]; positivity
  have hKη₁ : K * η₁ ≤ η := by
    have h1 : K * η₁ = K * η / (2 * (K + 1)) := by rw [hη₁def]; ring
    rw [h1, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (K + 1))]
    nlinarith [hη.le, hKpos]
  obtain ⟨δ, hδ, hD⟩ := hF.deriv τ hτ η₁ hη₁
  set δ₂ : ℝ := c / (2 * CC * (1 + nv) ^ 2 + 1) with hδ₂def
  have hδ₂ : 0 < δ₂ := by rw [hδ₂def]; positivity
  have hball : Metric.ball τ (min δ δ₂) ∈ 𝓝[Set.Icc 0 T] τ :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds τ (lt_min hδ hδ₂))
  filter_upwards [self_mem_nhdsWithin, hball] with s hs hsb
  have hst : |s - τ| < min δ δ₂ := by rwa [Metric.mem_ball, Real.dist_eq] at hsb
  have hst1 : |s - τ| < δ := lt_of_lt_of_le hst (min_le_left _ _)
  have hst2 : |s - τ| < δ₂ := lt_of_lt_of_le hst (min_le_right _ _)
  obtain ⟨hR, hRn⟩ := hD s hs hst1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul, key s hs hR]
  -- the size inputs
  have hqR : HQo α 4 (Pz (Jeps ρ ε (rem (slice g) V s τ))) := (hKpricing hR.1 hR.2).1
  have hleR : HkNorm α 4 (Pz (Jeps ρ ε (rem (slice g) V s τ)))
      ≤ K * HkNorm α 6 (rem (slice g) V s τ) := (hKpricing hR.1 hR.2).2
  have hX4 : HQo α 4 (slice (JfamP ρ ε g) s) :=
    (hKpricing (hreg.2 s hs).1 (hreg.2 s hs).2.1).1
  have hdly : HQo α 4 (fun z θ => slice (JfamP ρ ε g) s z θ - b z θ) :=
    Work.FTS.Open3.HQo_sub hX4 hb
  have he : HQo α 4 (fun z θ => (s - τ) * v z θ) := Work.FTS.Open3.HQo_const_mul hv (s - τ)
  have h1 := hcs α hα _ _ hdly hdly
  have h2 := hcs α hα _ _ hqR hb
  set h : ℝ := |s - τ| with hhdef
  have hh0 : 0 ≤ h := by rw [hhdef]; exact abs_nonneg _
  set nd : ℝ := HkNorm α 4 (fun z θ => slice (JfamP ρ ε g) s z θ - b z θ) with hnddef
  set nr : ℝ := HkNorm α 4 (Pz (Jeps ρ ε (rem (slice g) V s τ))) with hnRdef
  have hnd0 : 0 ≤ nd := Work.Spaces.HkNorm_nonneg α 4 _
  have hCC0 : 0 ≤ CC := hCCpos.le
  -- the size of the projected remainder
  have hnr1 : nr ≤ K * η₁ * h := by
    calc nr ≤ K * HkNorm α 6 (rem (slice g) V s τ) := hleR
      _ ≤ K * (η₁ * h) := mul_le_mul_of_nonneg_left hRn hKpos.le
      _ = K * η₁ * h := by ring
  have hnr : nr ≤ η * h := by
    have h2 : K * η₁ * h ≤ η * h := by
      rw [show K * η₁ * h = (K * η₁) * h by ring]
      exact mul_le_mul_of_nonneg_right hKη₁ hh0
    linarith
  -- the size of the increment
  have hstruct_s := hstruct s hs hR
  have hnd' : nd ≤ (1 + nv) * h := by
    calc nd = HkNorm α 4 (fun z θ => Pz (Jeps ρ ε (rem (slice g) V s τ)) z θ
            + (s - τ) * v z θ) := by rw [hnddef, hstruct_s]
      _ ≤ HkNorm α 4 (Pz (Jeps ρ ε (rem (slice g) V s τ)))
          + HkNorm α 4 (fun z θ => (s - τ) * v z θ) := hkNorm_triangle' hqR he
      _ = nr + |s - τ| * nv := by rw [hkNorm_const_mul]
      _ = nr + h * nv := by rw [hhdef]
      _ ≤ K * η₁ * h + h * nv := by linarith [hnr1]
      _ ≤ (1 + nv) * h := by
          have hKh : K * η₁ * h ≤ h := by
            have h2 : K * η₁ ≤ 1 := le_trans hKη₁ hη1
            nlinarith [hh0]
          nlinarith [hKh, hh0, hnv]
  -- `|IP4 (dly) (dly)| ≤ (c/2) h`
  have b1 : CC * nd * nd ≤ c / 2 * h := by
    have hsq : nd * nd ≤ ((1 + nv) * h) * ((1 + nv) * h) := mul_le_mul hnd' hnd' hnd0
      (by positivity)
    have hhδ : (1 + nv) ^ 2 * h * (2 * CC * (1 + nv) ^ 2 + 1) ≤ (1 + nv) ^ 2 * c := by
      have h' : h * (2 * CC * (1 + nv) ^ 2 + 1) ≤ c := by
        have hle := hst2.le
        rw [hδ₂def, le_div_iff₀ (by positivity)] at hle
        linarith
      nlinarith [sq_nonneg (1 + nv)]
    have hden : 0 < 2 * CC * (1 + nv) ^ 2 + 1 := by positivity
    calc CC * nd * nd = CC * (nd * nd) := by ring
      _ ≤ CC * (((1 + nv) * h) * ((1 + nv) * h)) := mul_le_mul_of_nonneg_left hsq hCC0
      _ = (CC * (1 + nv) ^ 2 * h) * h := by ring
      _ ≤ c / 2 * h := by
          apply mul_le_mul_of_nonneg_right _ hh0
          rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
          have h3 : CC * (1 + nv) ^ 2 * h * 2 * (2 * CC * (1 + nv) ^ 2 + 1)
              ≤ c * (2 * CC * (1 + nv) ^ 2 + 1) := by nlinarith
          exact le_of_mul_le_mul_right (by linarith) hden
  -- `2|IP4 (rr) b| ≤ (c/2) h`
  have b2 : 2 * (CC * nr * nb) ≤ c / 2 * h := by
    have hηb : η * (4 * CC * (nb + 1)) ≤ c := by
      rw [le_div_iff₀ (by positivity)] at hη2
      linarith
    calc 2 * (CC * nr * nb) ≤ 2 * (CC * (K * η₁ * h) * nb) := by
          have h1' : CC * nr ≤ CC * (K * η₁ * h) := mul_le_mul_of_nonneg_left hnr1 hCC0
          have h2' : CC * nr * nb ≤ CC * (K * η₁ * h) * nb :=
            mul_le_mul_of_nonneg_right h1' hnb
          linarith
      _ = (η₁ * (4 * CC * K * nb)) * h / 2 := by ring
      _ ≤ (η₁ * (4 * CC * (nb + 1) * K)) * h / 2 := by
          have h' : η₁ * (4 * CC * K * nb) ≤ η₁ * (4 * CC * (nb + 1) * K) := by
            apply mul_le_mul_of_nonneg_left _ hη₁.le
            nlinarith [hnb]
          nlinarith [hh0]
      _ ≤ c * h / 2 := by
          have hstep : η₁ * (4 * CC * (nb + 1) * K) ≤ c := by
            have h1 : η₁ * (4 * CC * (nb + 1) * K) = (K * η₁) * (4 * CC * (nb + 1)) := by
              ring
            rw [h1]
            exact le_trans (mul_le_mul_of_nonneg_right hKη₁ (by positivity)) hηb
          nlinarith [hh0, hstep]
      _ = c / 2 * h := by ring
  calc |IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
          (fun z θ => slice (JfamP ρ ε g) s z θ - b z θ)
          (fun z θ => slice (JfamP ρ ε g) s z θ - b z θ)
        + 2 * IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (Pz (Jeps ρ ε (rem (slice g) V s τ))) b|
      ≤ |IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (fun z θ => slice (JfamP ρ ε g) s z θ - b z θ)
            (fun z θ => slice (JfamP ρ ε g) s z θ - b z θ)|
          + |2 * IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (Pz (Jeps ρ ε (rem (slice g) V s τ))) b| :=
        abs_add_le _ _
    _ = |IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (fun z θ => slice (JfamP ρ ε g) s z θ - b z θ)
            (fun z θ => slice (JfamP ρ ε g) s z θ - b z θ)|
          + 2 * |IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (Pz (Jeps ρ ε (rem (slice g) V s τ))) b| := by
        rw [abs_mul]; norm_num
    _ ≤ CC * nd * nd + 2 * (CC * nr * nb) := by linarith
    _ ≤ c / 2 * h + c / 2 * h := by linarith
    _ = c * h := by ring

end Work.FTS.StrongEps.E4R3.Flow5Leaves
