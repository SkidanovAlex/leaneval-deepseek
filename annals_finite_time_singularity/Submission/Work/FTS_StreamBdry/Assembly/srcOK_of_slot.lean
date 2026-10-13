import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.Inputs.SliceTr
import Submission.Work.FTS_StreamBdry.Inputs.ftau_cont
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.Regularity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS_StreamBdry.Assembly.srcOK_of_slot` — the `SrcOK` slot of the slice adapter

For the profile `F(τ) = Ftau (pExp a) g τ = F_* + slice g τ` of the slice adapter, the
`SrcOK`-data of `Work.FTS.StreamBdryIface` is a consequence of the regularity package
`RegPkg' a S A B (extG G)` alone (together with the agreement `G = g` on the closed strip):
no `Sol`/`DynOK'`/`SlotBd` input is needed (those belong to the `SlotBd` conjunct).

* continuity on the closed angular strip `Ioi 0 ×ˢ Iθ` of `F(τ)` and of `D_zF(τ)`: the star
  profile `F_*` is visibly continuous (its radial factor `2z/(1+z)^2` is singular only at
  `z = -1`), and the perturbation slice is jointly `a`-Hölder on the strip by the two `Jet`
  moduli `hpz`, `hcont` of the package (transported from `extG G` to `g` by `hG` along the
  `z`-lines);
* the pointwise bounds `|F| ≤ Mf`, `|D_zF| ≤ Mf`: the `Γ`-decay of `F` (from `hvan`) and the
  splitting `D_z(F_* + g) = D_zF_* + z∂_zg` (the `z`-slice of `g` is differentiable by `hcont`),
  with `|D_zF_*| ≤ 20 pExp a·Γ ≤ 20 pExp a` and `|z∂_zg| ≤ L·Npz` below the support radius `L`
  and `D_zF = 0` beyond it;
* the endpoint values and the compact support come from `hvt` and `hsupp`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.Assembly

set_option autoImplicit false

open Work.FTS_StreamBdry.Inputs (Ftau_eq_profFull ftau_abs_le_Gamma ftau_vanish ftau_supp
  Dz_Fstar_abs_le_Gamma Gam_le_one_of_Iθ continuousOn_Fstar_ftau continuousOn_extG_slice)

/-! ## §1 A joint Hölder bound is continuity -/

/-- **Continuity from a joint `a`-Hölder bound of the sum metric.**  If `|f z θ - f z' θ'|` is
dominated by `N·(|z-z'| + |θ-θ'|)^a` — exactly the shape of the `(z,θ)`-half of
`Work.FTS.Regularity.Jet` — then `f` is continuous on the closed angular strip. -/
private theorem contOn_of_holder2 {N a : ℝ} (hN : 0 ≤ N) (ha : 0 < a) {f : ℝ → ℝ → ℝ}
    (h : ∀ z z' θ θ', 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |f z θ - f z' θ'| ≤ N * (|z - z'| + |θ - θ'|) ^ a) :
    ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
  refine Metric.continuousOn_iff.2 fun b hb ε hε => ?_
  obtain ⟨hbz, hbθ⟩ := hb
  have hN1 : (0 : ℝ) < N + 1 := by linarith
  have hpos : (0 : ℝ) < ε / (2 ^ a * (N + 1)) := by positivity
  set δ : ℝ := (ε / (2 ^ a * (N + 1))) ^ (1 / a) with hδ
  have hδpos : 0 < δ := Real.rpow_pos_of_pos hpos _
  refine ⟨δ, hδpos, fun q hq hdist => ?_⟩
  obtain ⟨hqz, hqθ⟩ := hq
  have hmain := h q.1 b.1 q.2 b.2 (le_of_lt hqz) (le_of_lt hbz) hqθ hbθ
  have hdist' : dist q b < δ := hdist
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hdist'
  have h1 : |q.1 - b.1| < δ := lt_of_le_of_lt (le_max_left _ _) hdist'
  have h2 : |q.2 - b.2| < δ := lt_of_le_of_lt (le_max_right _ _) hdist'
  have hsum_lt : |q.1 - b.1| + |q.2 - b.2| < 2 * δ := by linarith
  have hsum_nonneg : 0 ≤ |q.1 - b.1| + |q.2 - b.2| := by positivity
  have hrpow : (|q.1 - b.1| + |q.2 - b.2|) ^ a ≤ (2 * δ) ^ a :=
    Real.rpow_le_rpow hsum_nonneg (le_of_lt hsum_lt) ha.le
  have hmul : (2 * δ) ^ a = 2 ^ a * δ ^ a := Real.mul_rpow (by norm_num) hδpos.le
  have hδa : δ ^ a = ε / (2 ^ a * (N + 1)) := by
    rw [hδ, ← Real.rpow_mul hpos.le]
    have hone : 1 / a * a = 1 := by
      rw [one_div, inv_mul_cancel₀ (ne_of_gt ha)]
    rw [hone, Real.rpow_one]
  have hstep : N * (|q.1 - b.1| + |q.2 - b.2|) ^ a ≤ N * (2 ^ a * δ ^ a) := by
    rw [hmul] at hrpow
    exact mul_le_mul_of_nonneg_left hrpow hN
  have hkey : N * (2 ^ a * (ε / (2 ^ a * (N + 1)))) = ε * N / (N + 1) := by
    field_simp
  have hfinal : N * (|q.1 - b.1| + |q.2 - b.2|) ^ a < ε := by
    have h2' : N * (|q.1 - b.1| + |q.2 - b.2|) ^ a ≤ ε * N / (N + 1) := by
      rw [hδa, hkey] at hstep
      exact hstep
    have h3 : ε * N / (N + 1) < ε := by
      rw [div_lt_iff₀ hN1]
      nlinarith
    exact lt_of_le_of_lt h2' h3
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hmain hfinal

/-! ## §2 The `z`-derivative of the profile splits -/

/-- **The `z`-derivative of `F(τ) = F_* + slice g τ` splits** into that of the radial profile and
that of the perturbation, on the open half-strip.  The `z`-slice of the perturbation is
differentiable by the `hcont` field of the package (restricted to the line `τ = const`), and the
extended family `extG G` agrees with `g` along the `z`-lines. -/
private theorem pz_ftau_split {a : ℝ} (_ha : 0 < a)
    {g G : Work.FTS.Galerkin.Fam} {A B : ℝ → ℝ}
    (hreg : ∀ S : ℝ, 0 < S →
      Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      Work.Spaces.pz (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) z θ
        = Work.Spaces.pz (Work.Construction.Fstar (Work.FTS.Regularity.pExp a)) z θ
          + Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ := by
  intro z θ hz hθ
  have hS : 0 < τ + 1 := by linarith
  have hP : Work.FTS.RegPkgGal.RegPkg' a (τ + 1) A B (Work.FTS.RegPkgGal.extG G) := hreg (τ + 1) hS
  -- eventual agreement of the `z`-lines of `extG G` and of `g`
  have hevExt : (fun z' => Work.FTS.RegPkgGal.extG G z' θ τ) =ᶠ[𝓝 z] (fun z' => g z' θ τ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    rw [Work.FTS.RegPkgGal.extG_of_pos (g := G) hz' hτ, hG z' θ τ hz' hθ hτ]
  -- differentiability of the `z`-slice of `extG G`
  have hdExt : DifferentiableAt ℝ (fun z' => Work.FTS.RegPkgGal.extG G z' θ τ) z := by
    have hmem : (z, τ) ∈ Set.Ioi (-1) ×ˢ Set.Ioo (-1) ((τ + 1) + 1) :=
      ⟨by rw [Set.mem_Ioi]; linarith, by rw [Set.mem_Ioo]; exact ⟨by linarith, by linarith⟩⟩
    have hdiff : DifferentiableAt ℝ
        (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG G q.1 θ q.2) (z, τ) :=
      ((hP.hcont θ hθ).differentiableOn one_ne_zero (z, τ) hmem).differentiableAt
        ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hmem)
    have hline : DifferentiableAt ℝ (fun z' : ℝ => (z', τ)) z :=
      differentiableAt_id.prodMk (differentiableAt_const (c := τ))
    have hcomp := hdiff.comp z hline
    have hfun : (fun z' : ℝ => Work.FTS.RegPkgGal.extG G z' θ τ)
        = ((fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG G q.1 θ q.2)
            ∘ (fun z' : ℝ => (z', τ))) := rfl
    rw [hfun]
    exact hcomp
  have hdg : DifferentiableAt ℝ (fun z' => g z' θ τ) z :=
    hdExt.congr_of_eventuallyEq hevExt.symm
  have hdF : DifferentiableAt ℝ
      (fun z' => Work.Construction.Fstar (Work.FTS.Regularity.pExp a) z' θ) z := by
    have h : DifferentiableAt ℝ (fun z' : ℝ => (Work.FTS.Regularity.pExp a
        * (Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ
          / Work.Spaces.c (Work.FTS.Regularity.pExp a))) * Work.FM.Fstar z') z :=
      (Work.FM.hasDerivAt_Fstar z (by linarith)).differentiableAt.const_mul _
    simpa only [Work.Construction.Fstar] using h
  -- the slice of `F(τ)` agrees with `F_* + g(·,·,τ)` near `z`
  have hevF : (fun z' => Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ z' θ)
      =ᶠ[𝓝 z] (fun z' => Work.Construction.Fstar (Work.FTS.Regularity.pExp a) z' θ
        + g z' θ τ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' _
    simp only [Work.Construction.Ftau]
  have h1 : Work.Spaces.pz (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) z θ
      = Work.Spaces.pz (fun z' θ' => Work.Construction.Fstar (Work.FTS.Regularity.pExp a) z' θ'
          + g z' θ' τ) z θ := by
    simp only [Work.Spaces.pz]
    exact hevF.deriv_eq
  have h2 : Work.Spaces.pz (fun z' θ' => Work.Construction.Fstar (Work.FTS.Regularity.pExp a) z' θ'
          + g z' θ' τ) z θ
      = Work.Spaces.pz (Work.Construction.Fstar (Work.FTS.Regularity.pExp a)) z θ
        + Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ := by
    simp only [Work.Spaces.pz, Work.FTS.Galerkin.slice]
    exact deriv_add hdF hdg
  rw [h1, h2]

/-! ## §3 Continuity of `D_zF(τ)` on the closed strip -/

/-- **`D_zF(τ) = z∂_zF(τ)` is continuous on the closed angular strip.**  The perturbation
contribution `z∂_zg(τ)` is continuous because the `∂_zg`-jet `hpz` of the package bounds its
`(z,θ)`-oscillation by `Npz·(|Δz| + |Δθ|)^a`; the radial contribution `z∂_zF_*` is the smooth
closed form `α(Γ/c)·2z(1-z)/(1+z)^3`. -/
private theorem continuousOn_Dz_ftau {a : ℝ} (ha : 0 < a)
    {g G : Work.FTS.Galerkin.Fam} {A B : ℝ → ℝ}
    (hreg : ∀ S : ℝ, 0 < S →
      Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ContinuousOn (Function.uncurry (Work.Spaces.Dz
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ)))
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
  have hpa : 0 < Work.FTS.Regularity.pExp a := Work.FTS.Regularity.pExp_pos ha
  have hS : 0 < τ + 1 := by linarith
  have hP : Work.FTS.RegPkgGal.RegPkg' a (τ + 1) A B (Work.FTS.RegPkgGal.extG G) := hreg (τ + 1) hS
  have hτmem : τ ∈ Set.Icc (0 : ℝ) (τ + 1) := ⟨hτ, by linarith⟩
  have hev_of : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      ((fun z' => Work.FTS.RegPkgGal.extG G z' θ τ) =ᶠ[𝓝 z] fun z' => g z' θ τ) := by
    intro z θ hz hθ
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    rw [Work.FTS.RegPkgGal.extG_of_pos (g := G) hz' hτ, hG z' θ τ hz' hθ hτ]
  obtain ⟨Npz, hNpz⟩ := hP.hpz
  have hholder : ∀ z z' θ θ', 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG G) τ) z θ
          - Work.Spaces.pz (Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG G) τ) z' θ'|
        ≤ Npz * (|z - z'| + |θ - θ'|) ^ a := by
    intro z z' θ θ' hz hz' hθ hθ'
    have h := hNpz.2.2 z z' θ θ' τ τ hz hz' hθ hθ' hτmem hτmem
    simpa using h
  have hjetcont : ContinuousOn (Function.uncurry
      (Work.Spaces.pz (Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG G) τ)))
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := contOn_of_holder2 hNpz.1 ha hholder
  have hpz_eq : Set.EqOn (Function.uncurry (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ)))
      (Function.uncurry
        (Work.Spaces.pz (Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG G) τ)))
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
    intro p hp
    obtain ⟨hz, hθ⟩ := hp
    show Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) p.1 p.2
      = Work.Spaces.pz (Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG G) τ) p.1 p.2
    simp only [Work.Spaces.pz, Work.FTS.Galerkin.slice, Work.FTS.Regularity.gSlice]
    exact (hev_of p.1 p.2 hz hθ).deriv_eq.symm
  have hpzcont : ContinuousOn (Function.uncurry (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ)))
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := hjetcont.congr hpz_eq
  -- the perturbation contribution `z ∂_zg(τ)`
  have hA : ContinuousOn
      (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    continuous_fst.continuousOn.mul hpzcont
  -- the radial contribution `z ∂_zF_*`
  have hGam : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.Gam (Work.FTS.Regularity.pExp a) p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
    have h : Continuous (fun p : ℝ × ℝ => Work.FTS.Regularity.Gamma a p.2) :=
      (Work.FTS_StreamBdry.Inputs.continuous_Gamma ha).comp continuous_snd
    refine h.continuousOn.congr ?_
    intro p _
    exact (Work.FTS.Regularity.Gamma_eq_Gam a p.2).symm
  have hnum : ContinuousOn (fun p : ℝ × ℝ => 2 * p.1 * (1 - p.1))
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    (continuousOn_const.mul continuous_fst.continuousOn).mul
      (continuousOn_const.sub continuous_fst.continuousOn)
  have hden : ContinuousOn (fun p : ℝ × ℝ => (1 + p.1) ^ 3)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    (continuousOn_const.add continuous_fst.continuousOn).pow 3
  have hdenne : ∀ p : ℝ × ℝ, p ∈ (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) → (1 + p.1) ^ 3 ≠ 0 := by
    intro p hp
    have h1 : (0 : ℝ) < 1 + p.1 := by
      have h : (0 : ℝ) < p.1 := hp.1
      linarith
    exact ne_of_gt (pow_pos h1 3)
  have hfrac : ContinuousOn (fun p : ℝ × ℝ => 2 * p.1 * (1 - p.1) / (1 + p.1) ^ 3)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := hnum.div hden hdenne
  have hleft : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.Regularity.pExp a
      * (Work.Spaces.Gam (Work.FTS.Regularity.pExp a) p.2
        / Work.Spaces.c (Work.FTS.Regularity.pExp a)))
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := (hGam.div_const _).const_mul _
  have hB : ContinuousOn (fun p : ℝ × ℝ =>
      p.1 * Work.Spaces.pz (Work.Construction.Fstar (Work.FTS.Regularity.pExp a)) p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
    refine (hleft.mul hfrac).congr ?_
    intro p hp
    have hpz : (0 : ℝ) < p.1 := hp.1
    have h := Work.Construction.Dz_Fstar_eq (α := Work.FTS.Regularity.pExp a) hpa
      (z := p.1) (θ := p.2) (by linarith)
    simpa only [Work.Spaces.Dz, Pi.mul_apply] using h
  have hsum : ContinuousOn (fun p : ℝ × ℝ =>
      p.1 * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) p.1 p.2
        + p.1 * Work.Spaces.pz (Work.Construction.Fstar (Work.FTS.Regularity.pExp a)) p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := hA.add hB
  -- the pointwise splitting of `D_z` closes the argument
  refine ContinuousOn.congr hsum ?_
  rintro ⟨z, θ⟩ ⟨hz, hθ⟩
  have hsplit := pz_ftau_split (a := a) ha hreg hG hτ z θ hz hθ
  show Work.Spaces.Dz (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) z θ
    = z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ
      + z * Work.Spaces.pz (Work.Construction.Fstar (Work.FTS.Regularity.pExp a)) z θ
  rw [Work.Spaces.Dz, hsplit]
  ring

/-! ## §4 The slot -/

theorem srcOK_of_slot {a : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {g G : Work.FTS.Galerkin.Fam} {A B : ℝ → ℝ}
    (hreg : ∀ S : ℝ, 0 < S →
      Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∀ τ : ℝ, 0 ≤ τ → ∃ L Mf : ℝ,
      Work.FTS.StreamBdryIface.SrcOK
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) L Mf := by
  intro τ hτ
  have hpa : 0 < Work.FTS.Regularity.pExp a := Work.FTS.Regularity.pExp_pos ha
  have hS : 0 < τ + 1 := by linarith
  have hP : Work.FTS.RegPkgGal.RegPkg' a (τ + 1) A B (Work.FTS.RegPkgGal.extG G) := hreg (τ + 1) hS
  have hτmem : τ ∈ Set.Icc (0 : ℝ) (τ + 1) := ⟨hτ, by linarith⟩
  obtain ⟨Cg, hCg0, hCg⟩ := ftau_abs_le_Gamma (a := a) ha ha13 hτ hreg hG
  obtain ⟨L, hL0, hLsupp⟩ := ftau_supp (a := a) hτ hreg hG
  obtain ⟨Npz, hJetpz⟩ := hP.hpz
  have hNpz0 : 0 ≤ Npz := hJetpz.nonneg
  -- the `Γ`-fact on the closed strip
  have hΓ1 : ∀ θ ∈ Work.Spaces.Iθ, Work.FTS.Regularity.Gamma a θ ≤ 1 := fun θ hθ => by
    rw [Work.FTS.Regularity.Gamma_eq_Gam]
    exact Gam_le_one_of_Iθ ha hθ
  -- the pointwise bound on `∂_zg` on the strip
  have hpz_le : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ| ≤ Npz := by
    intro z θ hz hθ
    have hev : (fun z' => Work.FTS.RegPkgGal.extG G z' θ τ) =ᶠ[𝓝 z] (fun z' => g z' θ τ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      rw [Work.FTS.RegPkgGal.extG_of_pos (g := G) hz' hτ, hG z' θ τ hz' hθ hτ]
    have h : Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ
        = Work.Spaces.pz (Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG G) τ) z θ := by
      simp only [Work.Spaces.pz, Work.FTS.Galerkin.slice, Work.FTS.Regularity.gSlice]
      exact hev.deriv_eq.symm
    rw [h]
    exact hJetpz.abs_le (le_of_lt hz) hθ hτmem
  -- the splitting of `D_z` on the open quadrant
  have hDz_split : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      Work.Spaces.Dz (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) z θ
        = z * Work.Spaces.pz (Work.Construction.Fstar (Work.FTS.Regularity.pExp a)) z θ
          + z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ := by
    intro z θ hz hθ
    rw [Work.Spaces.Dz, pz_ftau_split (a := a) ha hreg hG hτ z θ hz hθ]
    ring
  refine ⟨L, 40 * Work.FTS.Regularity.pExp a + Cg + L * Npz + 1, ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity of `F(τ)`
    refine ContinuousOn.congr
      ((continuousOn_Fstar_ftau (a := a) ha).add (continuousOn_extG_slice (a := a) hreg hτ)) ?_
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    have h := Ftau_eq_profFull (a := a) hτ hG hz hθ
    simp only [Work.FTS.Regularity.profFull_apply] at h
    exact h
  · -- continuity of `D_zF(τ)`
    exact continuousOn_Dz_ftau (a := a) ha hreg hG hτ
  · -- the two pointwise bounds
    intro z θ hz hθ
    refine ⟨?_, ?_⟩
    · calc |Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ z θ|
          ≤ Cg * Work.FTS.Regularity.Gamma a θ := hCg z θ hz hθ
        _ ≤ Cg * 1 := mul_le_mul_of_nonneg_left (hΓ1 θ hθ) hCg0
        _ ≤ 40 * Work.FTS.Regularity.pExp a + Cg + L * Npz + 1 := by
            nlinarith [hpa.le, hCg0, hL0.le, hNpz0]
    · by_cases hzL : z ≤ L
      · rw [hDz_split z θ hz hθ]
        have h1 : |z * Work.Spaces.pz (Work.Construction.Fstar (Work.FTS.Regularity.pExp a)) z θ|
            ≤ 20 * Work.FTS.Regularity.pExp a := by
          have h := Dz_Fstar_abs_le_Gamma (a := a) ha ha13 (z := z) (θ := θ) hz hθ
          rw [Work.Spaces.Dz] at h
          calc |z * Work.Spaces.pz (Work.Construction.Fstar (Work.FTS.Regularity.pExp a)) z θ|
              ≤ 20 * Work.FTS.Regularity.pExp a * Work.FTS.Regularity.Gamma a θ := h
            _ ≤ 20 * Work.FTS.Regularity.pExp a * 1 :=
                mul_le_mul_of_nonneg_left (hΓ1 θ hθ) (by positivity)
            _ = 20 * Work.FTS.Regularity.pExp a := mul_one _
        have h2 : |z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ| ≤ L * Npz := by
          rw [abs_mul, abs_of_pos hz]
          exact mul_le_mul hzL (hpz_le z θ hz hθ) (abs_nonneg _) hL0.le
        calc |z * Work.Spaces.pz (Work.Construction.Fstar (Work.FTS.Regularity.pExp a)) z θ
              + z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ|
            ≤ |z * Work.Spaces.pz (Work.Construction.Fstar (Work.FTS.Regularity.pExp a)) z θ|
              + |z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ| := abs_add_le _ _
          _ ≤ 20 * Work.FTS.Regularity.pExp a + L * Npz := add_le_add h1 h2
          _ ≤ 40 * Work.FTS.Regularity.pExp a + Cg + L * Npz + 1 := by
              nlinarith [hpa.le, hCg0]
      · -- beyond the support radius the profile vanishes identically in `z`
        have hzL' : L < z := not_le.mp hzL
        have hzero : Work.Spaces.Dz (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ)
            z θ = 0 := by
          rw [Work.Spaces.Dz, Work.Spaces.pz]
          have hev0 : (fun z' => Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ z' θ)
              =ᶠ[𝓝 z] fun _ => 0 := by
            filter_upwards [isOpen_Ioi.mem_nhds hz, isOpen_Ioi.mem_nhds hzL'] with z' hz' hzL''
            exact hLsupp z' θ (le_of_lt hzL'') hθ
          rw [hev0.deriv_eq]
          simp
        rw [hzero, abs_zero]
        nlinarith [hpa.le, hCg0, hL0.le, hNpz0]
  · -- the endpoint values
    intro z hz
    exact ftau_vanish (a := a) ha.ne' hτ hreg hG z hz
  · -- the compact support
    exact ⟨hL0, hLsupp⟩

end Work.FTS_StreamBdry.Assembly
