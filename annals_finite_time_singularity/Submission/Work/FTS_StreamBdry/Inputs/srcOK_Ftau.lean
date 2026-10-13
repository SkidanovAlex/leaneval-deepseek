import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS.PressureOn.VortWtAesm
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.Inputs

open Work.FTS.Regularity (pExp)

set_option autoImplicit false

/-! ## §1 Continuity of `Γ` and of `F_*` on the closed angular strip -/

/-- `Γ(θ) = (sin θ cos²θ)^{α/3}` is continuous on *any* set when `0 < α`.  (The base vanishes at
`θ = 0, π/2`, but the exponent is positive, so `Real.rpow` is continuous there too.) -/
theorem Gam_continuousOn (α : ℝ) (hα : 0 < α) (s : Set ℝ) :
    ContinuousOn (fun θ : ℝ => Work.Spaces.Gam α θ) s := by
  have hbase : ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) s :=
    (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn
  have h := hbase.rpow_const (p := α / 3) (fun θ _ => Or.inr (by linarith))
  simpa only [Work.Spaces.Gam] using h

/-- `F_{*,rad}(z) = 2z/(1+z)²` is continuous on `Ioi 0`. -/
theorem FM_Fstar_continuousOn : ContinuousOn (fun z : ℝ => Work.FM.Fstar z) (Set.Ioi 0) := by
  have h2 : ContinuousOn (fun z : ℝ => (2 : ℝ) * z / (1 + z) ^ 2) (Set.Ioi 0) :=
    ((continuousOn_const.mul continuousOn_id).div
      ((continuousOn_const.add continuousOn_id).pow 2)
      (fun z hz => pow_ne_zero 2 (by rw [Set.mem_Ioi] at hz; linarith)))
  simpa only [Work.FM.Fstar] using h2

/-- The closed form `∂_zF_{*,rad} = 2(1-z)/(1+z)³` on `Ioi 0`. -/
theorem deriv_FM_Fstar_closed {z : ℝ} (hz : z ∈ Set.Ioi 0) :
    deriv Work.FM.Fstar z = 2 * (1 - z) / (1 + z) ^ 3 := by
  have hz' : z ∈ Set.Ioi (-1) := by rw [Set.mem_Ioi]; rw [Set.mem_Ioi] at hz; linarith
  have h := Work.FTS.StrongPersist.H6Pair6Aux.deriv_iter_FM_Fstar_eq 1 hz'
  rw [Function.iterate_one] at h
  rw [h]
  norm_num
  ring

/-- `∂_zF_{*,rad}` is continuous on `Ioi 0`. -/
theorem continuousOn_deriv_FM_Fstar :
    ContinuousOn (fun z : ℝ => deriv Work.FM.Fstar z) (Set.Ioi 0) := by
  refine ContinuousOn.congr ?_ (fun z hz => deriv_FM_Fstar_closed hz)
  have hden : ContinuousOn (fun z : ℝ => (1 + z) ^ 3) (Set.Ioi 0) :=
    ((continuousOn_const.add continuousOn_id).pow 3)
  exact ((continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).div hden
    (fun z hz => pow_ne_zero 3 (by rw [Set.mem_Ioi] at hz; linarith)))

/-- `F_{*,rad}` is differentiable at every `z > 0`. -/
theorem FM_Fstar_differentiableAt {z : ℝ} (hz : 0 < z) : DifferentiableAt ℝ Work.FM.Fstar z := by
  have h : DifferentiableAt ℝ (fun z : ℝ => (2 : ℝ) * z / (1 + z) ^ 2) z := by
    refine ((differentiableAt_const (c := (2 : ℝ))).mul differentiableAt_id).div
      (((differentiableAt_const (c := (1 : ℝ))).add differentiableAt_id).pow 2) ?_
    exact pow_ne_zero 2 (by linarith)
  change DifferentiableAt ℝ (fun z : ℝ => (2 : ℝ) * z / (1 + z) ^ 2) z
  exact h

/-- The `z`-derivative of the radial profile `F_*(z,θ) = α(Γ(θ)/c)F_{*,rad}(z)`. -/
theorem pz_Fstar_eq {α : ℝ} {z θ : ℝ} (hz : 0 < z) :
    Work.Spaces.pz (Work.Construction.Fstar α) z θ
      = α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * deriv Work.FM.Fstar z := by
  have hdiff : DifferentiableAt ℝ Work.FM.Fstar z := FM_Fstar_differentiableAt hz
  rw [Work.Spaces.pz]
  change deriv ((fun z' => (α * (Work.Spaces.Gam α θ / Work.Spaces.c α))
      * Work.FM.Fstar z')) z
      = α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * deriv Work.FM.Fstar z
  rw [deriv_const_mul _ hdiff]

/-- `(z,θ) ↦ F_*(z,θ)` is continuous on the closed angular strip. -/
theorem continuousOn_Fstar_pair {α : ℝ} (hα : 0 < α) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Construction.Fstar α p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
  have hGam : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    (Gam_continuousOn α hα Set.univ).comp continuousOn_snd (fun p _ => trivial)
  have hFM : ContinuousOn (fun p : ℝ × ℝ => Work.FM.Fstar p.1)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    FM_Fstar_continuousOn.comp continuousOn_fst (fun p hp => hp.1)
  have h : ContinuousOn (fun p : ℝ × ℝ =>
      α * (Work.Spaces.Gam α p.2 / Work.Spaces.c α) * Work.FM.Fstar p.1)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    (continuousOn_const.mul (hGam.div_const _)).mul hFM
  refine h.congr (fun p _ => ?_)
  simp only [Work.Construction.Fstar]

/-- `(z,θ) ↦ ∂_zF_*(z,θ)` is continuous on the closed angular strip. -/
theorem continuousOn_pz_Fstar_pair {α : ℝ} (hα : 0 < α) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Construction.Fstar α) p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
  have hGam : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    (Gam_continuousOn α hα Set.univ).comp continuousOn_snd (fun p _ => trivial)
  have hd : ContinuousOn (fun p : ℝ × ℝ => deriv Work.FM.Fstar p.1)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    continuousOn_deriv_FM_Fstar.comp continuousOn_fst (fun p hp => hp.1)
  have h : ContinuousOn (fun p : ℝ × ℝ =>
      α * (Work.Spaces.Gam α p.2 / Work.Spaces.c α) * deriv Work.FM.Fstar p.1)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    (continuousOn_const.mul (hGam.div_const _)).mul hd
  exact h.congr (fun p hp => pz_Fstar_eq (α := α) (z := p.1) (θ := p.2) hp.1)

/-- **The numerical bounds of the radial profile**: on the closed angular strip,
`|F_*| ≤ 40α` and `|z ∂_zF_*| ≤ 40α` for `0 < α ≤ 1`.  (Uses `Γ ≤ 1`, `c ∈ [1/10,10]` and the
order-`≤ 1` jets `|F_{*,rad}| ≤ 2`, `|z ∂_zF_{*,rad}| ≤ 4`.) -/
theorem Fstar_bounds {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * Work.FM.Fstar z| ≤ 40 * α ∧
    |z * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * deriv Work.FM.Fstar z)| ≤ 40 * α := by
  obtain ⟨hGam0, _⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  obtain ⟨hc1, _⟩ := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hquot : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 := by
    rw [abs_div, abs_of_nonneg hGam0, abs_of_pos hcpos, div_le_iff₀ hcpos]
    linarith
  have hFM : |Work.FM.Fstar z| ≤ 2 := by
    have h := Work.FTS.StrongPersist.H6Pair6Aux.zpow_deriv_FM_Fstar_le 0 (le_of_lt hz)
    simpa using h
  have hzderiv : |z * deriv Work.FM.Fstar z| ≤ 4 := by
    have h := Work.FTS.StrongPersist.H6Pair6Aux.zpow_deriv_FM_Fstar_le 1 (le_of_lt hz)
    rw [pow_one, Function.iterate_one] at h
    norm_num at h
    rw [abs_mul]
    exact h
  have hα0 : 0 ≤ α := le_of_lt hα
  constructor
  · rw [abs_mul, abs_mul, abs_of_nonneg hα0]
    calc α * |Work.Spaces.Gam α θ / Work.Spaces.c α| * |Work.FM.Fstar z| ≤ α * 10 * 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hquot hα0) hFM (abs_nonneg _) (by positivity)
      _ ≤ 40 * α := by linarith
  · rw [show z * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * deriv Work.FM.Fstar z)
        = α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * (z * deriv Work.FM.Fstar z)
        from by ring]
    rw [abs_mul, abs_mul, abs_of_nonneg hα0]
    calc α * |Work.Spaces.Gam α θ / Work.Spaces.c α| * |z * deriv Work.FM.Fstar z|
        ≤ α * 10 * 4 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hquot hα0) hzderiv (abs_nonneg _) (by positivity)
      _ ≤ 40 * α := by linarith

/-! ## §2 Differentiability of a slice, and the splitting of `∂_z(F_* + ·)` -/

/-- **A slice of the family is differentiable in `z` on `z > 0`.**  This is the `hcont` field of
`RegPkg'` (`C¹` in `(z,τ)` on `Ioi (-1) ×ˢ Ioo (-1) (S+1)`) restricted to the line `τ = const`. -/
theorem RegPkg'_slice_differentiableAt {a S z θ τ : ℝ} {A B : ℝ → ℝ} {G' : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' a S A B G') (hθ : θ ∈ Work.Spaces.Iθ)
    (hτ : τ ∈ Set.Icc 0 S) (hz : 0 < z) : DifferentiableAt ℝ (fun z' => G' z' θ τ) z := by
  have hmem : (z, τ) ∈ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1) :=
    ⟨by rw [Set.mem_Ioi]; linarith,
      by rw [Set.mem_Ioo]; exact ⟨by linarith [hτ.1], by linarith [hτ.2]⟩⟩
  have hdiff : DifferentiableAt ℝ (fun q : ℝ × ℝ => G' q.1 θ q.2) (z, τ) :=
    ((h.hcont θ hθ).differentiableOn one_ne_zero (z, τ) hmem).differentiableAt
      ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hmem)
  have hline : DifferentiableAt ℝ (fun z' : ℝ => (z', τ)) z := by fun_prop
  have hcomp := hdiff.comp z hline
  have hfun : (fun z' : ℝ => G' z' θ τ)
      = ((fun q : ℝ × ℝ => G' q.1 θ q.2) ∘ (fun z' : ℝ => (z', τ))) := rfl
  rw [hfun]
  exact hcomp

/-- **The `z`-derivative of `F_* + G'` splits**: the radial profile contributes
`α(Γ/c)∂_zF_{*,rad}`, the perturbation its own `∂_z`. -/
theorem pz_add_eq {α : ℝ} {G' : ℝ → ℝ → ℝ → ℝ} {z θ τ : ℝ}
    (hdiff : DifferentiableAt ℝ (fun z' => G' z' θ τ) z) (hz : 0 < z) :
    Work.Spaces.pz (fun z θ => Work.Construction.Fstar α z θ + G' z θ τ) z θ
      = α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * deriv Work.FM.Fstar z
        + Work.Spaces.pz (fun z θ => G' z θ τ) z θ := by
  have hF : DifferentiableAt ℝ (fun z' : ℝ => Work.Construction.Fstar α z' θ) z := by
    have h : DifferentiableAt ℝ
        (fun z' : ℝ => (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * Work.FM.Fstar z') z :=
      (FM_Fstar_differentiableAt hz).const_mul _
    change DifferentiableAt ℝ
      (fun z' : ℝ => (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * Work.FM.Fstar z') z
    exact h
  have hsplit : deriv (fun z' : ℝ => Work.Construction.Fstar α z' θ + G' z' θ τ) z
      = deriv (fun z' : ℝ => Work.Construction.Fstar α z' θ) z
        + deriv (fun z' : ℝ => G' z' θ τ) z := by
    rw [show (fun z' : ℝ => Work.Construction.Fstar α z' θ + G' z' θ τ)
        = (fun z' : ℝ => Work.Construction.Fstar α z' θ)
          + (fun z' : ℝ => G' z' θ τ) from rfl]
    exact deriv_add hF hdiff
  have hFz : deriv (fun z' : ℝ => Work.Construction.Fstar α z' θ) z
      = α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * deriv Work.FM.Fstar z :=
    pz_Fstar_eq (α := α) (θ := θ) hz
  simp only [Work.Spaces.pz]
  rw [hsplit, hFz]

theorem srcOK_Ftau {a : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {g G : Work.FTS.Galerkin.Fam} {A B : ℝ → ℝ}
    (hreg : ∀ S : ℝ, 0 < S →
      Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∀ τ, 0 ≤ τ → ∃ L Mf : ℝ,
      Work.FTS.StreamBdryIface.SrcOK (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) L Mf := by
  intro τ hτ
  have hαpos : 0 < pExp a := Work.FTS.Regularity.pExp_pos ha
  have hα1 : pExp a ≤ 1 := Work.FTS.Regularity.pExp_le_one ha13
  set S : ℝ := max τ 1 with hSdef
  have hSpos : 0 < S := by rw [hSdef]; exact lt_of_lt_of_le one_pos (le_max_right τ 1)
  have hτS : τ ∈ Set.Icc 0 S := by rw [hSdef]; exact ⟨hτ, le_max_left τ 1⟩
  have hreg' : Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G) := hreg S hSpos
  obtain ⟨Ng, hJet⟩ := hreg'.hg
  obtain ⟨Npz, hJetpz⟩ := hreg'.hpz
  obtain ⟨L, hLpos, hLsupp⟩ := hreg'.hsupp
  have hNg0 : 0 ≤ Ng := hJet.1
  have hNpz0 : 0 ≤ Npz := hJetpz.1
  set Mf : ℝ := 80 * pExp a + Ng + L * Npz + 1 with hMfdef
  -- the `∂_z`-derivative of the full profile splits into that of `F_*` and that of the perturbation
  have hDz_eq : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      Work.Spaces.pz (Work.Construction.Ftau (pExp a) g τ) z θ
        = pExp a * (Work.Spaces.Gam (pExp a) θ / Work.Spaces.c (pExp a))
            * deriv Work.FM.Fstar z
          + Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG G z θ τ) z θ := by
    intro z θ hz hθ
    have hdiff : DifferentiableAt ℝ (fun z' => Work.FTS.RegPkgGal.extG G z' θ τ) z :=
      RegPkg'_slice_differentiableAt hreg' hθ hτS hz
    have h1 : Work.Spaces.pz (Work.Construction.Ftau (pExp a) g τ) z θ
        = Work.Spaces.pz (fun z θ => Work.Construction.Fstar (pExp a) z θ
            + Work.FTS.RegPkgGal.extG G z θ τ) z θ := by
      simp only [Work.Spaces.pz]
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      show Work.Construction.Ftau (pExp a) g τ z' θ
          = Work.Construction.Fstar (pExp a) z' θ + Work.FTS.RegPkgGal.extG G z' θ τ
      simp only [Work.Construction.Ftau]
      rw [Work.FTS.RegPkgGal.extG_of_pos hz' hτ, hG z' θ τ hz' hθ hτ]
    rw [h1, pz_add_eq (α := pExp a) (G' := fun z θ τ => Work.FTS.RegPkgGal.extG G z θ τ)
      (z := z) (θ := θ) (τ := τ) hdiff hz]
  -- `D_zF = 0` beyond the support radius
  have hDz_zero : ∀ z θ : ℝ, L < z → θ ∈ Work.Spaces.Iθ →
      Work.Spaces.Dz (Work.Construction.Ftau (pExp a) g τ) z θ = 0 := by
    intro z θ hzL hθ
    rw [Work.Spaces.Dz, Work.Spaces.pz]
    have hev : (fun z' : ℝ => Work.Construction.Ftau (pExp a) g τ z' θ) =ᶠ[nhds z] 0 := by
      filter_upwards [isOpen_Ioi.mem_nhds hzL] with z' hz'
      have hz'0 : 0 < z' := lt_trans hLpos hz'
      have h := hLsupp τ hτS z' θ (le_of_lt hz')
      simp only [Work.FTS.Regularity.profFull_apply] at h
      show Work.Construction.Ftau (pExp a) g τ z' θ = 0
      rw [Work.Construction.Ftau,
        ← hG z' θ τ hz'0 hθ hτ, ← Work.FTS.RegPkgGal.extG_of_pos (g := G) hz'0 hτ]
      exact h
    rw [Filter.EventuallyEq.deriv_eq hev]
    simp
  refine ⟨L, Mf, ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity of `F` on the closed angular strip
    have hFstar := continuousOn_Fstar_pair (α := pExp a) hαpos
    have hgs : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.RegPkgGal.extG G p.1 p.2 τ)
        (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
      (Work.FTS.PressureOn.continuousOn_uncurry_gSlice ha hJet hτS).mono
        (fun p hp => ⟨Set.mem_Ici.mpr (le_of_lt hp.1), hp.2⟩)
    refine ContinuousOn.congr (hFstar.add hgs) ?_
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    show Work.Construction.Fstar (pExp a) z θ + g z θ τ
        = Work.Construction.Fstar (pExp a) z θ + Work.FTS.RegPkgGal.extG G z θ τ
    rw [Work.FTS.RegPkgGal.extG_of_pos (g := G) hz hτ, hG z θ τ hz hθ hτ]
  · -- continuity of `D_zF` on the closed angular strip
    have hGam : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Gam (pExp a) p.2)
        (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
      (Gam_continuousOn (pExp a) hαpos Set.univ).comp continuousOn_snd (fun p _ => trivial)
    have hd : ContinuousOn (fun p : ℝ × ℝ => deriv Work.FM.Fstar p.1)
        (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
      continuousOn_deriv_FM_Fstar.comp continuousOn_fst (fun p hp => hp.1)
    have h1 : ContinuousOn (fun p : ℝ × ℝ => pExp a
          * (Work.Spaces.Gam (pExp a) p.2 / Work.Spaces.c (pExp a))
          * deriv Work.FM.Fstar p.1) (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
      (continuousOn_const.mul (hGam.div_const _)).mul hd
    have h2 : ContinuousOn (fun p : ℝ × ℝ =>
          Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG G z θ τ) p.1 p.2)
        (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
      (Work.FTS.PressureOn.continuousOn_uncurry_gSlice ha hJetpz hτS).mono
        (fun p hp => ⟨Set.mem_Ici.mpr (le_of_lt hp.1), hp.2⟩)
    refine ContinuousOn.congr (continuousOn_fst.mul (h1.add h2)) ?_
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    show Work.Spaces.Dz (Work.Construction.Ftau (pExp a) g τ) z θ
        = z * (pExp a * (Work.Spaces.Gam (pExp a) θ / Work.Spaces.c (pExp a))
            * deriv Work.FM.Fstar z
          + Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG G z θ τ) z θ)
    rw [Work.Spaces.Dz, hDz_eq z θ hz hθ]
  · -- the pointwise bounds
    intro z θ hz hθ
    have hFst1 : |pExp a * (Work.Spaces.Gam (pExp a) θ / Work.Spaces.c (pExp a))
        * Work.FM.Fstar z| ≤ 40 * pExp a := (Fstar_bounds hαpos hα1 hz hθ).1
    have hFst2 : |z * (pExp a * (Work.Spaces.Gam (pExp a) θ / Work.Spaces.c (pExp a))
        * deriv Work.FM.Fstar z)| ≤ 40 * pExp a := (Fstar_bounds hαpos hα1 hz hθ).2
    have hgz : |g z θ τ| ≤ Ng := by
      rw [← hG z θ τ hz hθ hτ, ← Work.FTS.RegPkgGal.extG_of_pos (g := G) hz hτ]
      exact hJet.abs_le (le_of_lt hz) hθ hτS
    have hgpz : |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG G z θ τ) z θ| ≤ Npz :=
      hJetpz.abs_le (le_of_lt hz) hθ hτS
    refine ⟨?_, ?_⟩
    · show |Work.Construction.Fstar (pExp a) z θ + g z θ τ| ≤ Mf
      calc |Work.Construction.Fstar (pExp a) z θ + g z θ τ|
          ≤ |Work.Construction.Fstar (pExp a) z θ| + |g z θ τ| := abs_add_le _ _
        _ ≤ 40 * pExp a + Ng := add_le_add hFst1 hgz
        _ ≤ Mf := by rw [hMfdef]; nlinarith [hαpos.le, hLpos.le, hNpz0]
    · by_cases hzL : z ≤ L
      · rw [Work.Spaces.Dz, hDz_eq z θ hz hθ]
        have h2 : |z * Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG G z θ τ) z θ|
            ≤ L * Npz := by
          rw [abs_mul, abs_of_pos hz]
          exact mul_le_mul hzL hgpz (abs_nonneg _) hLpos.le
        rw [show z * (pExp a * (Work.Spaces.Gam (pExp a) θ / Work.Spaces.c (pExp a))
              * deriv Work.FM.Fstar z
            + Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG G z θ τ) z θ)
            = z * (pExp a * (Work.Spaces.Gam (pExp a) θ / Work.Spaces.c (pExp a))
                * deriv Work.FM.Fstar z)
              + z * Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG G z θ τ) z θ
            from by ring]
        calc |z * (pExp a * (Work.Spaces.Gam (pExp a) θ / Work.Spaces.c (pExp a))
                * deriv Work.FM.Fstar z)
              + z * Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG G z θ τ) z θ|
            ≤ |z * (pExp a * (Work.Spaces.Gam (pExp a) θ / Work.Spaces.c (pExp a))
                * deriv Work.FM.Fstar z)|
              + |z * Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG G z θ τ) z θ| :=
              abs_add_le _ _
          _ ≤ 40 * pExp a + L * Npz := add_le_add hFst2 h2
          _ ≤ Mf := by rw [hMfdef]; nlinarith [hαpos.le, hNg0]
      · rw [hDz_zero z θ (not_le.mp hzL) hθ, abs_zero]
        rw [hMfdef]; nlinarith [hαpos.le, hNg0, hLpos.le, hNpz0]
  · -- vanishing on the angular boundary
    intro z hz
    have h0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by positivity⟩
    have hpi : (Real.pi / 2) ∈ Work.Spaces.Iθ := ⟨by positivity, le_rfl⟩
    obtain ⟨hv0, hv1⟩ := hreg'.hvt τ hτS
    have hg0 : g z 0 τ = 0 := by
      rw [← hG z 0 τ hz h0 hτ, ← Work.FTS.RegPkgGal.extG_of_pos (g := G) hz hτ]
      exact hv0 z
    have hgpi : g z (Real.pi / 2) τ = 0 := by
      rw [← hG z (Real.pi / 2) τ hz hpi hτ, ← Work.FTS.RegPkgGal.extG_of_pos (g := G) hz hτ]
      exact hv1 z
    refine ⟨?_, ?_⟩
    · show Work.Construction.Fstar (pExp a) z 0 + g z 0 τ = 0
      rw [hg0, add_zero]
      simp only [Work.Construction.Fstar, Work.Spaces.Gam_zero_left (pExp a) (ne_of_gt hαpos),
        zero_div, mul_zero, zero_mul]
    · show Work.Construction.Fstar (pExp a) z (Real.pi / 2) + g z (Real.pi / 2) τ = 0
      rw [hgpi, add_zero]
      simp only [Work.Construction.Fstar, Work.Spaces.Gam_zero_right (pExp a) (ne_of_gt hαpos),
        zero_div, mul_zero, zero_mul]
  · -- compact support
    refine ⟨hLpos, ?_⟩
    intro z θ hLz hθ
    have hz : 0 < z := lt_of_lt_of_le hLpos hLz
    have h := hLsupp τ hτS z θ hLz
    simp only [Work.FTS.Regularity.profFull_apply] at h
    show Work.Construction.Ftau (pExp a) g τ z θ = 0
    rw [Work.Construction.Ftau,
      ← hG z θ τ hz hθ hτ, ← Work.FTS.RegPkgGal.extG_of_pos (g := G) hz hτ]
    exact h

end Work.FTS_StreamBdry.Inputs
