import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.FTS.EpsEngine.ClassCStepEngine
import Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafA.sinpow_mixed_Jeps_le_strip
import Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafB.tendsto_EpsSq_strip

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `fts_localstep_thetaunif.lean` — the θ-uniform clause is FREE from `EpsMem` (ruling, curric-46, 2026-10-12)

Design: `cbc/fts_localstep_thetaunif.md`.

The mollifier `J_ε` is a convolution in the log coordinates `(s, ζ) = (log z, log tan θ)`, whose
Jacobian is `dz' dθ' · 2/(z' sin 2θ')`.  Cauchy–Schwarz on the kernel formula
(`mixed_Jeps_kernel_locInt`) and the Jacobian bound of `Jker_mul_inv_le_epsW_sq`, with the factor
`sin(2θ')^{γ-1}` KEPT (it is `≤ e^{ε(γ-1)} sin(2θ)^{γ-1}` on the kernel support,
`sech(ζ-p) ≤ e^{|p|} sech ζ`) instead of being bounded by `1`, give for every slot `(a,b)`

    sin(2θ)^{1-γ} · (mixed b a (J_ε g) z θ)²  ≤  C · EpsSq α (stripLo (thShift θ (-ε)) g)

with `C` independent of `z` (`z' w(z')² ≥ 1`).  The right side → 0 as θ → 0⁺ by dominated
convergence (`EpsMem α g` = integrability of `(g·epsW)²`).  Same at `π/2`.  Hence
`ThetaUnif α k (J_ε g)` — uniform in `z`, every order `k` — from `EpsMem α g` alone, and the
θ-uniform residual `hflat : ThetaUnifFam …` of `classC_step_of_flat` is unnecessary.

Only the two sub-leaves (A) `sinpow_mixed_Jeps_le_strip` and (B) `tendsto_EpsSq_strip` are `sorry`;
the leaf `thetaUnif_Jeps_of_epsMem` and everything below it are proved from them and in-tree lemmas.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine.ThetaFromEps

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Sub-leaf (A): the localized pointwise bound, with the `sin^{γ-1}` gain kept.**
Template: `Jeps_abs_le_sqrt_EpsSq` / `Jker_quad_le_aux` (Tonelli inequality + change of
variables) and `EpsSqIter_mixed_Jeps_le_gen` (kernel derivatives `Kd`, `KdK`); the new point is
`sin(2·thShift θ p) ≤ e^{|p|} sin(2θ)` on the kernel support, and that on the support every shifted
angle satisfies `thShift θ p ≤ thShift θ (-ε)` (resp. `≥ thShift θ ε`). -/
theorem sinpow_mixed_Jeps_le_strip {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (a b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Fn,
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      Work.FTS.StrongEps.EpsMem α g →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g) z θ) ^ 2
          ≤ C * Work.FTS.StrongEps.EpsSq α (stripLo (Work.FTS.StrongEps.thShift θ (-ε)) g) ∧
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g) z θ) ^ 2
          ≤ C * Work.FTS.StrongEps.EpsSq α
              (stripHi (Real.pi / 2 - Work.FTS.StrongEps.thShift θ ε) g) :=
  Work.FTS.EpsEngine.ThetaFromEpsLeafA.sinpow_mixed_Jeps_le_strip hρ hα hε hε1 a b

/-- **Sub-leaf (B): the strip energies vanish** (dominated convergence on `(g·epsW)²`).
Proved in `EpsEngine/ThetaFromEpsLeafB/tendsto_EpsSq_strip.lean`. -/
theorem tendsto_EpsSq_strip {α : ℝ} {g : Fn} (hg : Work.FTS.StrongEps.EpsMem α g) :
    Tendsto (fun φ => Work.FTS.StrongEps.EpsSq α (stripLo φ g)) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun φ => Work.FTS.StrongEps.EpsSq α (stripHi φ g)) (𝓝[>] 0) (𝓝 0) :=
  Work.FTS.EpsEngine.ThetaFromEpsLeafB.tendsto_EpsSq_strip (g := g) hg

/-- **THE LEAF: `J_ε` of an `EpsMem` profile is θ-uniformly flat at every order** (uniform in `z`).
From (A) + (B) + `thShift θ (-ε) → 0` as `θ → 0⁺` and `π/2 - thShift θ ε → 0` as `θ → π/2⁻`. -/
theorem thetaUnif_Jeps_of_epsMem {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {g : Fn}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hg : Work.FTS.StrongEps.EpsMem α g) (k : ℕ) :
    ThetaUnif α k (Work.FTS.StrongEps.Jeps ρ ε g) := by
  have hB := tendsto_EpsSq_strip hg
  -- the lower window edge tends to `0⁺`
  have hT0 : Tendsto (fun θ => Work.FTS.StrongEps.thShift θ (-ε)) (𝓝[>] 0) (𝓝[>] 0) := by
    have hc : ContinuousAt (fun θ => Real.arctan (Real.tan θ * Real.exp ε)) 0 :=
      Real.continuous_arctan.continuousAt.comp
        ((Real.continuousAt_tan.mpr (by simp)).mul continuousAt_const)
    have h0 : (fun θ => Real.arctan (Real.tan θ * Real.exp ε)) 0 = 0 := by simp
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simp only [Real.tan_zero, zero_mul, Real.arctan_zero] at this
      simpa [Work.FTS.StrongEps.thShift] using this
    · have hlt : Set.Iio (Real.pi / 2) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by positivity)
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hlt] with θ hθ hθ2
      have htan : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ hθ2
      simp only [Work.FTS.StrongEps.thShift, neg_neg, Set.mem_Ioi]
      exact Real.arctan_pos.mpr (mul_pos htan (Real.exp_pos _))
  -- the upper window edge tends to `(π/2)⁻`
  have hT1 : Tendsto (fun θ => Real.pi / 2 - Work.FTS.StrongEps.thShift θ ε)
      (𝓝[<] (Real.pi / 2)) (𝓝[>] 0) := by
    have htop : Tendsto (fun θ => Real.tan θ * Real.exp (-ε)) (𝓝[<] (Real.pi / 2)) atTop :=
      Real.tendsto_tan_pi_div_two.atTop_mul_const (Real.exp_pos _)
    have harc := Real.tendsto_arctan_atTop.comp htop
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h1 : Tendsto (fun θ => Real.arctan (Real.tan θ * Real.exp (-ε)))
          (𝓝[<] (Real.pi / 2)) (𝓝 (Real.pi / 2)) := harc.mono_right nhdsWithin_le_nhds
      have h2 := (tendsto_const_nhds (x := Real.pi / 2)).sub h1
      simpa [Work.FTS.StrongEps.thShift] using h2
    · refine Filter.Eventually.of_forall (fun θ => ?_)
      simp only [Work.FTS.StrongEps.thShift, Set.mem_Ioi, sub_pos]
      exact Real.arctan_lt_pi_div_two _
  constructor
  · intro a b hab ε' hε'
    obtain ⟨C, hC, hA⟩ := sinpow_mixed_Jeps_le_strip hρ hα hε hε1 a b
    have hev : ∀ᶠ φ in 𝓝[>] (0 : ℝ),
        Work.FTS.StrongEps.EpsSq α (stripLo φ g) < ε' / C :=
      hB.1 (Iio_mem_nhds (div_pos hε' hC))
    have hev' := hT0.eventually hev
    have hlt : Set.Iio (Real.pi / 2) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by positivity)
    have hall : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ < Real.pi / 2 ∧
        Work.FTS.StrongEps.EpsSq α (stripLo (Work.FTS.StrongEps.thShift θ (-ε)) g) < ε' / C := by
      filter_upwards [hev', mem_nhdsWithin_of_mem_nhds hlt] with θ h1 h2
      exact ⟨h2, h1⟩
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hall
    refine ⟨u, hu, fun θ hθ0 hθu z hz => ?_⟩
    obtain ⟨hθ2, hS⟩ := hsub ⟨hθ0, hθu⟩
    have h := (hA g hsm hg z θ hz hθ0 hθ2).1
    have : C * Work.FTS.StrongEps.EpsSq α (stripLo (Work.FTS.StrongEps.thShift θ (-ε)) g)
        ≤ ε' := by
      have := mul_lt_mul_of_pos_left hS hC
      rw [mul_div_cancel₀ _ hC.ne'] at this
      exact this.le
    linarith
  · intro a b hab ε' hε'
    obtain ⟨C, hC, hA⟩ := sinpow_mixed_Jeps_le_strip hρ hα hε hε1 a b
    have hev : ∀ᶠ φ in 𝓝[>] (0 : ℝ),
        Work.FTS.StrongEps.EpsSq α (stripHi φ g) < ε' / C :=
      hB.2 (Iio_mem_nhds (div_pos hε' hC))
    have hev' := hT1.eventually hev
    have hgt : Set.Ioi (0 : ℝ) ∈ 𝓝 (Real.pi / 2) := Ioi_mem_nhds (by positivity)
    have hall : ∀ᶠ θ in 𝓝[<] (Real.pi / 2), 0 < θ ∧
        Work.FTS.StrongEps.EpsSq α
          (stripHi (Real.pi / 2 - Work.FTS.StrongEps.thShift θ ε) g) < ε' / C := by
      filter_upwards [hev', mem_nhdsWithin_of_mem_nhds hgt] with θ h1 h2
      exact ⟨h2, h1⟩
    obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hall
    refine ⟨Real.pi / 2 - l, by simp only [Set.mem_Iio] at hl; linarith,
      fun θ hθ2 hθl z hz => ?_⟩
    obtain ⟨hθ0, hS⟩ := hsub ⟨by linarith, hθ2⟩
    have h := (hA g hsm hg z θ hz hθ0 hθ2).2
    have : C * Work.FTS.StrongEps.EpsSq α
        (stripHi (Real.pi / 2 - Work.FTS.StrongEps.thShift θ ε) g) ≤ ε' := by
      have := mul_lt_mul_of_pos_left hS hC
      rw [mul_div_cancel₀ _ hC.ne'] at this
      exact this.le
    linarith

/-- `Pz ∘ J_ε` of an `EpsMem` profile is θ-uniformly flat (PROVED from the leaf). -/
theorem thetaUnif_Pz_Jeps_of_epsMem {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {g : Fn}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hg : Work.FTS.StrongEps.EpsMem α g) (k : ℕ) :
    ThetaUnif α k (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε g)) :=
  thetaUnif_Pz
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
      (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hsm))
    (thetaUnif_Jeps_of_epsMem hρ hα hε hε1 hsm hg k)

/-- The pointwise θ-half `TauTraces` of `Pz (J_ε g)`, every order (PROVED from the leaf). -/
theorem tauTraces_Pz_Jeps_of_epsMem {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {g : Fn}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hg : Work.FTS.StrongEps.EpsMem α g) (k : ℕ) :
    TauTraces α k (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε g)) :=
  (thetaUnif_Pz_Jeps_of_epsMem hρ hα hε hε1 hsm hg k).tauTraces

/-- **`ClassC (Pz (J_ε u))` with residual (a) discharged**: only `fsm` remains (PROVED from the
leaf + `classC_Pz_Jeps_of_parts`). -/
theorem classC_Pz_Jeps_of_epsMem {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) (hα1 : α ≤ 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {u : Fn}
    (hsu : Work.FTS.EllipticEst.SmoothOpen u) (hmu : Work.Spaces.HkMem α 4 u)
    (hme : Work.FTS.StrongEps.EpsMem α u)
    (hfsm : ∀ m : ℕ, ContDiffOn ℝ m
      (Work.Elliptic.Fstar (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)))
      (Set.Ioi 0)) :
    Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)) :=
  classC_Pz_Jeps_of_parts hρ hα hα1 hε hε1 hsu hmu hme
    (tauTraces_Pz_Jeps_of_epsMem hρ hα hε hε1
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall u).mp hsu) hme 10) hfsm

/-- **Drop-in replacement for `classC_Pz_Jeps_add_of_increment`**: no `ThetaUnif` hypothesis. -/
theorem classC_Pz_Jeps_add_of_increment' {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) (hα1 : α ≤ 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {g₀ I : Fn}
    (hC : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε g₀)))
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g₀)
    (hIsm : Work.FTS.EllipticEst.SmoothOpen I)
    (hgmem : Work.Spaces.HkMem α 4 g₀) (hImem : Work.Spaces.HkMem α 4 I)
    (hIEps : Work.FTS.StrongEps.EpsMem α I)
    (hIfsm : ∀ m : ℕ, ContDiffOn ℝ m
      (Work.Elliptic.Fstar (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε I)))
      (Set.Ioi 0)) :
    Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
      (fun z θ => g₀ z θ + I z θ))) := by
  have hCI : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε I)) :=
    classC_Pz_Jeps_of_epsMem hρ hα hα1 hε hε1 hIsm hImem hIEps hIfsm
  have hadd : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε g₀)
      + Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε I)) :=
    Work.FTS.ClassC.classC_add hC hCI
  have hsum : Work.FTS.EllipticEst.SmoothOpen (fun z θ => g₀ z θ + I z θ) := hgsm.add hIsm
  have hmemSum : Work.Spaces.HkMem α 4 (fun z θ => g₀ z θ + I z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open hgsm hIsm hgmem hImem
  have hsub := Work.FTS.EpsEngine.Pz_Jeps_sub_eq (α := α) (ρ := ρ) (ε := ε)
    (u := fun z θ => g₀ z θ + I z θ) (v := g₀) hρ hα hε hsum hgsm hmemSum hgmem
  have hfun : (fun z θ : ℝ => (g₀ z θ + I z θ) - g₀ z θ) = I := by
    funext z θ; ring
  rw [hfun] at hsub
  have hgoal : Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (fun z θ => g₀ z θ + I z θ))
      = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε g₀)
        + Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε I) := by
    rw [hsub]; abel
  rw [hgoal]
  exact hadd

/-- **Drop-in replacement for `classC_step_of_flat`** (the engine's `hkeepIter` class-`C` clause):
the four flatness gates `hflat`/`hsmF`/`hmeasF`/`hsupF` are gone; `hIEps` was already an input. -/
theorem classC_step_of_epsMem {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {τ : ℝ} {n : ℕ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1) (hα1 : α ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hC₀ : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε g₀)))
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g₀) (hgmem : Work.Spaces.HkMem α 4 g₀)
    (hIsm : Work.FTS.EllipticEst.SmoothOpen (epsInc α ρ ε Φs E g₀ n τ))
    (hImem : Work.Spaces.HkMem α 4 (epsInc α ρ ε Φs E g₀ n τ))
    (hIEps : Work.FTS.StrongEps.EpsMem α (epsInc α ρ ε Φs E g₀ n τ))
    (hIfsm : ∀ m : ℕ, ContDiffOn ℝ m
      (Work.Elliptic.Fstar (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
        (epsInc α ρ ε Φs E g₀ n τ)))) (Set.Ioi 0)) :
    Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
      (slice (epsIter α ρ ε Φs E g₀ (n + 1)) τ))) := by
  rw [slice_epsIter_succ_eq]
  exact classC_Pz_Jeps_add_of_increment' hρ hα hα1 hε hε1 hC₀ hgsm hIsm hgmem hImem hIEps hIfsm

end Work.FTS.EpsEngine.ThetaFromEps
