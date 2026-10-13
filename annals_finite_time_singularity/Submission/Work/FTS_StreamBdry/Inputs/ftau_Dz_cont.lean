/-
# `Work.FTS_StreamBdry.Inputs.ftau_Dz_cont` — continuity of `D_z(F_* + g(τ))` on the closed strip

This is the second conjunct of `Work.FTS.StreamBdryIface.SrcOK` for the profile
`F(τ) = Ftau (pExp a) g τ = F_* + slice g τ` of the slice adapter: for every `τ ≥ 0` the function
`D_zF(τ) = z ∂_zF(τ)` is continuous on the closed angular strip `Ioi 0 ×ˢ Iθ`.

**Route.**  All the data come from the package `RegPkg' a S A B (extG G)` at the horizon
`S = τ + 1` (per `τ`; the constants of `RegPkg'` may depend on the horizon) transported through
the agreement hypothesis `hG` (`G = g` on the closed strip):

* `hpz` : the joint `a`-Hölder `Jet` of `(z,θ,τ) ↦ ∂_zg`.  At the fixed time `τ` this is a
  joint `(z,θ)`-Hölder estimate `|∂_zg(z,θ) - ∂_zg(z',θ')| ≤ Npz(|z-z'| + |θ-θ'|)^a`, which is
  exactly continuity (`contOn_of_holder2`), transported from `extG G` to `g` by eventual equality
  along the `z`-lines (`deriv`-agreement);
* `hcont` : the joint `C¹`-smoothness of `(z,τ) ↦ extG G z θ τ` at fixed `θ`, which gives the
  differentiability of the `z`-slice at `τ` and hence the *sum rule*
  `∂_z(F_* + g(τ)) = ∂_zF_* + ∂_zg(τ)`;
* the radial factor `z ∂_zF_* = α(Γ/c)·2z(1-z)/(1+z)³` is smooth (`Construction.Dz_Fstar_eq`).

The package `RegPkg'` controls `∂_zg` (not higher `z`-derivatives) through its `Jet`, so this is
the strongest form of the statement it can deliver — and it is exactly what `SrcOK` consumes.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_StreamBdry.Inputs.SliceTr
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.Inputs

set_option autoImplicit false

/-! ## §0 A Hölder function of `(z,θ)` (for the metric `|Δz| + |Δθ|`) is continuous -/

/-- **Continuity from a joint `a`-Hölder bound of the sum metric.**  If `|f z θ - f z' θ'|` is
dominated by `N·(|z-z'| + |θ-θ'|)^a` — exactly the shape of the `(z,θ)`-half of
`Work.FTS.Regularity.Jet` — then `f` is continuous on the closed angular strip. -/
theorem contOn_of_holder2 {N a : ℝ} (hN : 0 ≤ N) (ha : 0 < a) {f : ℝ → ℝ → ℝ}
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

/-! ## §1 The target -/

theorem ftau_Dz_cont {a : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {C₀ : ℝ} {g G : Work.FTS.Galerkin.Fam} {A B : ℝ → ℝ}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g)
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∀ τ : ℝ, 0 ≤ τ →
      ContinuousOn (Function.uncurry
        (Work.Spaces.Dz (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ)))
        (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
  intro τ hτ
  have hpa : 0 < Work.FTS.Regularity.pExp a := Work.FTS.Regularity.pExp_pos ha
  have hS : 0 < τ + 1 := by linarith
  have hP : Work.FTS.RegPkgGal.RegPkg' a (τ + 1) A B (Work.FTS.RegPkgGal.extG G) :=
    hreg (τ + 1) hS
  have hτmem : τ ∈ Set.Icc (0 : ℝ) (τ + 1) := ⟨hτ, by linarith⟩
  -- eventual agreement of the `z`-lines of `extG G` and of `g`
  have hev_of : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      ((fun z' => Work.FTS.RegPkgGal.extG G z' θ τ) =ᶠ[𝓝 z] fun z' => g z' θ τ) := by
    intro z θ hz hθ
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    rw [Work.FTS.RegPkgGal.extG_of_pos (g := G) hz' hτ, hG z' θ τ hz' hθ hτ]
  -- the joint Hölder bound of the `∂_zg`-jet at the fixed time `τ`
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
  -- transport to the slice of `g`
  have hpz_eq : Set.EqOn (Function.uncurry (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ)))
      (Function.uncurry
        (Work.Spaces.pz (Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG G) τ)))
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
    intro p hp
    obtain ⟨hz, hθ⟩ := hp
    change Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) p.1 p.2
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
      (continuous_Gamma ha).comp continuous_snd
    refine h.continuousOn.congr ?_
    intro p hp
    exact (Work.FTS.Regularity.Gamma_eq_Gam a p.2).symm
  have hnum : ContinuousOn (fun p : ℝ × ℝ => 2 * p.1 * (1 - p.1))
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    (continuousOn_const.mul continuous_fst.continuousOn).mul
      (continuousOn_const.sub continuous_fst.continuousOn)
  have hden : ContinuousOn (fun p : ℝ × ℝ => (1 + p.1) ^ 3)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    (continuousOn_const.add continuous_fst.continuousOn).pow 3
  have hfrac : ContinuousOn (fun p : ℝ × ℝ => 2 * p.1 * (1 - p.1) / (1 + p.1) ^ 3)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    hnum.div hden (fun p hp => by
      have h1 : (0 : ℝ) < 1 + p.1 := by
        have h : (0 : ℝ) < p.1 := hp.1
        linarith
      positivity)
  have hleft : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.Regularity.pExp a
      * (Work.Spaces.Gam (Work.FTS.Regularity.pExp a) p.2
        / Work.Spaces.c (Work.FTS.Regularity.pExp a)))
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := (hGam.div_const _).const_mul _
  have hB : ContinuousOn (fun p : ℝ × ℝ =>
      p.1 * Work.Spaces.pz (Work.Construction.Fstar (Work.FTS.Regularity.pExp a)) p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
    have hrat : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.Regularity.pExp a
        * (Work.Spaces.Gam (Work.FTS.Regularity.pExp a) p.2
          / Work.Spaces.c (Work.FTS.Regularity.pExp a))
        * (2 * p.1 * (1 - p.1) / (1 + p.1) ^ 3)) (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
      hleft.mul hfrac
    refine hrat.congr ?_
    intro p hp
    have hz : (0 : ℝ) < p.1 := hp.1
    have h := Work.Construction.Dz_Fstar_eq (α := Work.FTS.Regularity.pExp a) hpa
      (z := p.1) (θ := p.2) (by linarith)
    simpa only [Work.Spaces.Dz] using h
  have hsum : ContinuousOn (fun p : ℝ × ℝ =>
      p.1 * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) p.1 p.2
        + p.1 * Work.Spaces.pz (Work.Construction.Fstar (Work.FTS.Regularity.pExp a)) p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := hA.add hB
  -- the pointwise sum rule closes the argument
  refine hsum.congr ?_
  intro p hp
  obtain ⟨hz, hθ⟩ := hp
  have hzpos : (0 : ℝ) < p.1 := hz
  have hev := hev_of p.1 p.2 hzpos hθ
  have hdExt : DifferentiableAt ℝ (fun z' => Work.FTS.RegPkgGal.extG G z' p.2 τ) p.1 := by
    have hmem : (p.1, τ) ∈ Set.Ioi (-1) ×ˢ Set.Ioo (-1) ((τ + 1) + 1) :=
      ⟨show (-1 : ℝ) < p.1 by linarith,
        ⟨show (-1 : ℝ) < τ by linarith, show τ < (τ + 1) + 1 by linarith⟩⟩
    have hdiff : DifferentiableAt ℝ
        (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG G q.1 p.2 q.2) (p.1, τ) :=
      ((hP.hcont p.2 hθ).differentiableOn one_ne_zero (p.1, τ) hmem).differentiableAt
        ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hmem)
    exact Work.Spaces.differentiableAt_curry_left
      (G := fun x y : ℝ => Work.FTS.RegPkgGal.extG G x p.2 y) (z := p.1) (θ := τ) hdiff
  have hdg : DifferentiableAt ℝ (fun z' => g z' p.2 τ) p.1 :=
    hdExt.congr_of_eventuallyEq hev.symm
  have hdF : DifferentiableAt ℝ
      (fun z' => Work.Construction.Fstar (Work.FTS.Regularity.pExp a) z' p.2) p.1 := by
    have h : DifferentiableAt ℝ (fun z' : ℝ => (Work.FTS.Regularity.pExp a
        * (Work.Spaces.Gam (Work.FTS.Regularity.pExp a) p.2
          / Work.Spaces.c (Work.FTS.Regularity.pExp a))) * Work.FM.Fstar z') p.1 :=
      (Work.FM.hasDerivAt_Fstar p.1 (by linarith)).differentiableAt.const_mul _
    simpa only [Work.Construction.Fstar] using h
  have hfun : (fun z' => Work.Construction.Fstar (Work.FTS.Regularity.pExp a) z' p.2
        + g z' p.2 τ)
      = (fun z' => Work.Construction.Fstar (Work.FTS.Regularity.pExp a) z' p.2)
        + (fun z' => g z' p.2 τ) := by
    funext z'; rfl
  show Work.Spaces.Dz (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) p.1 p.2 = _
  simp only [Work.Spaces.Dz, Work.Spaces.pz, Work.FTS.Galerkin.slice, Work.Construction.Ftau]
  rw [hfun, deriv_add hdF hdg]
  ring

end Work.FTS_StreamBdry.Inputs
