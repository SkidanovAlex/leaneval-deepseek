/-
# `E4R3/N4C/HonRows/n0row6` — row 6 of the §8 table in the *honest* (open-quadrant) class

The honest counterpart of `Work.FTS.NonlinRows.NRow6`: for `g` carrying only the open-quadrant
data (`SmoothOpen g`, `HkMem α 4 g`, `HkMem α 5 g`, `L12 g 0 = 0`, `DecayAll 4 g`) the piece

  `N₀₅ᵇ = -c2m(θ)·L₁₂(g)·D_z g`

is `ℋ⁴`-honest and priced against the transport clause `N4ExtraH.t2`:

  `|IP α (N₀₅ᵇ) g| ≤ K · α^{-1/2} · Xn α g ^ 3`.

The frozen proof of `NRow6` used the frozen class `GalClass`, i.e. `SmoothQuad`
(`C^∞` on the *closed* strip `z > -1`), together with the frozen uniform bound
`L12_dzdIter_abs_le` of the `D_z`-iterates of `L₁₂(g)` and the decay of the `D_z`-iterates of
`g`.  Along the route those are not available; the two honest replacements are

* `N4C.L12_dzdIter_abs_le_open` (this chapter) — the same bound from `SmoothOpen`/`HkMem α 4`
  and `L12 g 0 = 0` alone, no decay hypothesis;
* `OpenPkg.HkMem_Dz_le` + `SmoothOpen.Dz` — honesty and smoothness of `D_z g` from the
  `ℋ⁵`-honesty of `g`.

Everything else is the `θ`-calculus of the coefficient `fcoef = -c2m(θ)·L₁₂(g)(z)` (angular
factor `c2m` priced by `OpenPkg.angmul_field`, radial factor by `L12_dzdIter_abs_le_open`), its
flat angular norm `CoefTh 1 fcoef ≤ 24·KL·Xn α g`, and the clause `t2`.  `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.E4R3.N4C.Defs
import Submission.Work.FTS.StrongEps.E4R3.N4C.L12AbsLeHon
import Submission.Work.FTS.NonlinRows.NRow6
import Submission.Work.FTS.NonlinRows.NRow1_7Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

-- Uniform-in-`Cs`, `Ce` restatement of `Work.FTS.StrongEps.E4R3.N4C.HonRows.n0row6`.
-- The two binders `Cs`, `Ce` are moved from the theorem's argument list into the inner
-- `forall`, so that the constant `K` does not depend on them (the target `rowsN0T`
-- quantifies `{Cs Ce}` *after* the `exists K`).  The proof script is unchanged.

namespace Work.FTS.StrongEps.E4R3.N4C.HonRowsU

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The angular profile `3 sin 2θ` and its basic calculus

(verbatim from `Work.FTS.NonlinRows.NRow6`, where the corresponding declarations are private). -/

private def Aang : ℝ → ℝ := fun θ => 3 * Real.sin (2 * θ)

private theorem hasDerivAt_Aang (θ : ℝ) : HasDerivAt Aang (6 * Real.cos (2 * θ)) θ := by
  have h : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * (2 * 1)) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
  have h3 : HasDerivAt (fun t : ℝ => 3 * Real.sin (2 * t))
      (3 * (Real.cos (2 * θ) * (2 * 1))) θ := h.const_mul 3
  have h3' : HasDerivAt Aang (3 * (Real.cos (2 * θ) * (2 * 1))) θ := h3
  rwa [show (3 : ℝ) * (Real.cos (2 * θ) * (2 * 1)) = 6 * Real.cos (2 * θ) from by ring] at h3'

private theorem abs_Aang_le (θ : ℝ) : |Aang θ| ≤ 3 := by
  have h : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one _
  simp only [Aang, abs_mul]
  have h3 : |(3 : ℝ)| = 3 := by norm_num
  rw [h3]
  linarith

private theorem abs_dthU_Aang_le (θ : ℝ) : |Work.Spaces.dthU Aang θ| ≤ 6 := by
  have hd : deriv Aang θ = 6 * Real.cos (2 * θ) := (hasDerivAt_Aang θ).deriv
  have hs : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one _
  have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  show |Real.sin (2 * θ) * deriv Aang θ| ≤ 6
  rw [hd, abs_mul, abs_mul]
  have h6 : |(6 : ℝ)| = 6 := by norm_num
  rw [h6]
  nlinarith [abs_nonneg (Real.sin (2 * θ)), abs_nonneg (Real.cos (2 * θ))]

/-! ## The angular smoothness of `c2m` -/

private theorem contDiff_c2m (n : WithTop ℕ∞) : ContDiff ℝ n Work.Construction.c2m := by
  show ContDiff ℝ n (fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2)
  exact (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).sub (Real.contDiff_sin.pow 2)

private theorem differentiableAt_c2m (θ : ℝ) : DifferentiableAt ℝ Work.Construction.c2m θ := by
  show DifferentiableAt ℝ (fun t : ℝ => Real.cos (2 * t) - Real.sin t ^ 2) θ
  fun_prop

private theorem smoothOpen_c2m_ang :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Construction.c2m θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen]
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => Work.Construction.c2m p.2) Work.FTS.EllipticEst.Q0
  exact (contDiff_c2m Work.Stability.smoothOrder).contDiffOn.comp contDiffOn_snd
    (fun p _ => Set.mem_univ p.2)

/-! ## The coefficient `fcoef = -c2m(θ)·L₁₂(g)(z)` -/

/-- The `θ`-dependent coefficient of `N₀₅ᵇ`. -/
private abbrev coeff6 (g : Fn) : Fn :=
  fun z θ => (-1 : ℝ) * (Work.Construction.c2m θ * Work.Construction.L12 g z)

/-- `∂_θ` of an angular `×` radial product. -/
private theorem pth_ang_rad (a : ℝ → ℝ) (r : ℝ → ℝ) (ha : ∀ θ, DifferentiableAt ℝ a θ) :
    Work.Spaces.pth (fun z θ => a θ * r z) = fun z θ => deriv a θ * r z := by
  funext z θ
  show deriv (fun θ' => a θ' * r z) θ = deriv a θ * r z
  exact deriv_mul_const (ha θ) (r z)

/-- `∂_θ (coeff6 g) = 3 sin(2θ)·L₁₂(g)(z)`. -/
private theorem pth_coeff6 (g : Fn) :
    Work.Spaces.pth (coeff6 g) = fun z θ => Aang θ * Work.Construction.L12 g z := by
  have hcongr : coeff6 g = fun z θ =>
      (fun θ' => (-1 : ℝ) * Work.Construction.c2m θ') θ
        * (fun z' => Work.Construction.L12 g z') z := by
    funext z θ
    simp only [coeff6]
    ring
  rw [hcongr, pth_ang_rad (fun θ' => (-1 : ℝ) * Work.Construction.c2m θ')
    (fun z' => Work.Construction.L12 g z')
    (fun θ => (differentiableAt_c2m θ).const_mul (-1))]
  funext z θ
  show deriv (fun θ' => (-1 : ℝ) * Work.Construction.c2m θ') θ
      * Work.Construction.L12 g z = Aang θ * Work.Construction.L12 g z
  rw [deriv_const_mul (-1) (differentiableAt_c2m θ),
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_deriv θ]
  simp only [Aang]
  ring

/-- The mixed iterates of `∂_θ (coeff6 g)`. -/
private theorem mixed_pth_coeff6 (g : Fn) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (Work.Spaces.pth (coeff6 g)) z θ
      = Work.Spaces.DthIter i (fun _ θ' => Aang θ') 0 θ
        * Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 g z) z := by
  rw [pth_coeff6]
  exact Work.FTS.Nonlinear.Pieces.mixed_ang_rad Aang
    (fun z => Work.Construction.L12 g z) j i z θ

/-- The pointwise bound of the constituents of `CoefTh 1 (coeff6 g)`. -/
private theorem mixed_pth_coeff6_le {M : ℝ} (hM : 0 ≤ M) {g : Fn}
    (hLpt : ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z| ≤ M)
    {b i : ℕ} (hbi : b + i ≤ 1) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    |Work.Spaces.mixed b i (Work.Spaces.pth (coeff6 g)) z θ| ≤ 6 * M := by
  have hDi : |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Aang θ') 0 θ| ≤ 6 := by
    have hi1 : i ≤ 1 := by omega
    interval_cases i
    · simp only [Work.Spaces.DthIter_zero]
      exact le_trans (abs_Aang_le θ) (by norm_num)
    · rw [Work.FTS.LocData.DthIter_rad_eq 1 Aang 0 θ, Function.iterate_one]
      exact abs_dthU_Aang_le θ
  have hDj : |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z| ≤ M :=
    hLpt b (by omega) z hz
  rw [mixed_pth_coeff6]
  rw [abs_mul]
  exact mul_le_mul hDi hDj (abs_nonneg _) (by norm_num)

/-- The `supAbsO`-bound of the constituents of `CoefTh 1 (coeff6 g)`. -/
private theorem sup_mixed_pth_coeff6 {M : ℝ} (hM : 0 ≤ M) {g : Fn}
    (hLpt : ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z| ≤ M)
    {b i : ℕ} (hbi : b + i ≤ 1) :
    Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth (coeff6 g))) ≤ 6 * M :=
  Work.FTS.H2.supAbsO_le (fun z θ hz hθ0 hθ1 => mixed_pth_coeff6_le hM hLpt hbi hz hθ0 hθ1)

/-- `CoefTh 1 f ≤ 4 K` from a uniform bound `K` on the three constituents. -/
private theorem coefTh_one_le_of_sup {f : ℝ → ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ b i : ℕ, b + i ≤ 1 →
      Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) ≤ K) :
    Work.FTS.VocabO.CoefTh 1 f ≤ 4 * K := by
  have hterm : ∀ b ∈ Finset.range 2, ∀ i ∈ Finset.range 2,
      (if b + i ≤ 1 then
        Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) else 0) ≤ K := by
    intro b _ i _
    by_cases hc : b + i ≤ 1
    · rw [if_pos hc]; exact h b i hc
    · rw [if_neg hc]; exact hK
  unfold Work.FTS.VocabO.CoefTh
  refine le_trans (Finset.sum_le_sum fun b hb => Finset.sum_le_sum fun i hi =>
    hterm b hb i hi) ?_
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact le_of_eq (by ring)

/-! ## Row 6 -/

theorem n0row6u (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Cs Ce α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      Work.Spaces.HkMem α 5 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.DecayAll 4 g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05bF α g) ∧
        |IP α (Work.FTS.Nonlin.N05bF α g) g|
          ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
  obtain ⟨hCi, _hα₂pos⟩ := hN.pos
  obtain ⟨hCt, _⟩ := hE.pos
  obtain ⟨Cam, hCampos, hCam⟩ := Work.FTS.OpenPkg.angmul_field
  obtain ⟨KL, hKLpos, hKLb⟩ := L12_dzdIter_abs_le_open
  refine ⟨Ct * (Cam * 1000 * Ci + 24 * KL) + 1, by positivity, ?_⟩
  intro Cs Ce α g Φs Φg hα hα1 hαα₂ hsmg hmem4 hmem5 hL120 hdec hells hellg
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  obtain ⟨hLmem, hLle⟩ :=
    hN.l12H α hIoc g (show Work.FTS.VocabO.HQo α 4 g from ⟨hsmg, hmem4⟩) hL120
  -- the uniform bound of the `D_z`-iterates of `L₁₂(g)` (honest version)
  have hLpt : ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z|
        ≤ KL * Work.FTS.Nonlin.Xn α g :=
    fun b hb z hz => hKLb hα hα1 hsmg hmem4 hL120 b hb z hz
  -- smoothness of the radial factor and of the coefficient
  have hLsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.L12 g z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα hellg.smooth hellg.V.1.1
  have hc2mLsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 g z) :=
    Work.FTS.NonlinRows.smoothOpen_c2m_L12 hα hellg.smooth hellg.V.1.1
  have hfSm : Work.FTS.EllipticEst.SmoothOpen (coeff6 g) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (-1) hc2mLsm
  -- the angular-multiplication package for `c2m`
  have ham := hCam α hα hα1 Work.Construction.c2m
    (fun z _ => Work.Construction.L12 g z) 1000
    smoothOpen_c2m_ang
    (fun θ hθ => by
      have h := Work.FTS.Nonlinear.Pieces.abs_c2m_le_two hθ
      linarith)
    (fun i hi hi4 θ hθ => by
      have h := Work.FTS.Nonlinear.Pieces.DthIter_c2m_le i hi hi4 θ
      have hsin0 : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
      have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hstep : 1000 * (Real.sin (2 * θ)) ^ (2 : ℝ) ≤ 1000 * Real.sin (2 * θ) := by
        rw [Real.rpow_two]
        nlinarith [hsin0, hsin1, sq_nonneg (Real.sin (2 * θ))]
      exact h.trans hstep)
    hLsm hLmem
  have hfMem : Work.Spaces.HkMem α 4 (coeff6 g) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (-1) ham.1
  -- the norm bound of the coefficient
  have hXn_f : Work.FTS.Nonlin.Xn α (coeff6 g)
      ≤ (Cam * 1000 * Ci) * Work.FTS.Nonlin.Xn α g := by
    have h1 : Work.FTS.Nonlin.Xn α (coeff6 g)
        = Work.FTS.Nonlin.Xn α
            (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 g z) := by
      simp only [coeff6, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul, abs_neg, abs_one,
        one_mul]
    rw [h1]
    calc Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 g z)
        ≤ Cam * 1000 * Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.L12 g z) := ham.2
      _ ≤ Cam * 1000 * (Ci * Work.FTS.Nonlin.Xn α g) :=
          mul_le_mul_of_nonneg_left hLle (by positivity)
      _ = (Cam * 1000 * Ci) * Work.FTS.Nonlin.Xn α g := by ring
  -- the flat angular coefficient
  have hsup : ∀ b i : ℕ, b + i ≤ 1 →
      Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth (coeff6 g)))
        ≤ 6 * (KL * Work.FTS.Nonlin.Xn α g) :=
    fun b i hbi => sup_mixed_pth_coeff6 (by positivity) hLpt hbi
  have hcoef : Work.FTS.VocabO.CoefTh 1 (coeff6 g)
      ≤ (24 * KL) * Work.FTS.Nonlin.Xn α g := by
    refine (coefTh_one_le_of_sup (by positivity) hsup).trans (le_of_eq ?_)
    ring
  have hcoefThMem : Work.FTS.VocabO.CoefThMem 1 (coeff6 g) :=
    fun b i hbi => ⟨6 * (KL * Work.FTS.Nonlin.Xn α g),
      fun z θ hz hθ0 hθ1 => mixed_pth_coeff6_le (by positivity) hLpt hbi hz hθ0 hθ1⟩
  -- the `ℋ⁴`-honesty
  have hDzMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g) :=
    Work.FTS.IPGen.HkMem_Dz_le (α := α) (k := 4) (f := g) hsmg hmem5
  have hDzSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz g) := hsmg.Dz
  have hprod := hN.prod α hIoc (coeff6 g) (Work.Spaces.Dz g)
    ⟨hfSm, hfMem⟩ ⟨hDzSm, hDzMem⟩
  have hfun : Work.FTS.Nonlin.N05bF α g
      = fun z θ => coeff6 g z θ * Work.Spaces.Dz g z θ := by
    funext z θ
    simp only [coeff6, Work.FTS.Nonlin.N05bF, Work.Construction.N05b]
    ring
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact hprod.1
  · rw [hfun]
    have ht2 := hE.t2 α hIoc (coeff6 g) g hfSm hfMem hcoefThMem hsmg hmem4 hmem5 hdec
    refine ht2.trans ?_
    have hsum : Work.FTS.Nonlin.Xn α (coeff6 g) + Work.FTS.VocabO.CoefTh 1 (coeff6 g)
        ≤ (Cam * 1000 * Ci + 24 * KL) * Work.FTS.Nonlin.Xn α g := by
      have hPQ : (Cam * 1000 * Ci + 24 * KL) * Work.FTS.Nonlin.Xn α g
          = (Cam * 1000 * Ci) * Work.FTS.Nonlin.Xn α g
            + (24 * KL) * Work.FTS.Nonlin.Xn α g := by ring
      rw [hPQ]
      linarith [hXn_f, hcoef]
    calc Ct * α ^ (-(1 / 2 : ℝ))
          * (Work.FTS.Nonlin.Xn α (coeff6 g) + Work.FTS.VocabO.CoefTh 1 (coeff6 g))
          * Work.FTS.Nonlin.Xn α g ^ 2
        ≤ Ct * α ^ (-(1 / 2 : ℝ))
          * ((Cam * 1000 * Ci + 24 * KL) * Work.FTS.Nonlin.Xn α g)
          * Work.FTS.Nonlin.Xn α g ^ 2 := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsum ?_) (by positivity)
          exact mul_nonneg hCt.le (Real.rpow_nonneg hα.le _)
      _ = (Ct * (Cam * 1000 * Ci + 24 * KL))
          * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by ring
      _ ≤ (Ct * (Cam * 1000 * Ci + 24 * KL) + 1)
          * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          linarith

end Work.FTS.StrongEps.E4R3.N4C.HonRowsU
