/-
# Row 7 of the primed §8 table: `N₀₆ = -c2m(θ)·L₁₂(F_*)·D_z g`

Target (fixed): `Work.FTS.NonlinRows.NRow7` — the `ℋ⁴`-honesty of `N06F α g` and the pairing
bound `|IP α (N06F α g) g| ≤ K·√α·|g|_{ℋ⁴}²`.

Mathematically: by `L₁₂(F_*)(z) = 2α/(1+z)` the piece is the product of the flat coefficient
`f(z,θ) = c2m(θ)·L₁₂(F_*)(z)` with `D_z g`.  The transport clause `N4Extra'.t3`
(`VocabO.T3Clause`) then gives
`|IP α (f·D_z g) g| ≤ Ct·α^{-1/2}·(|f|_{𝒲^{4,∞}} + CoefTh 3 f)·|g|_{ℋ⁴}²`, where

* `|f|_{𝒲^{4,∞}} ≤ Cw·α` (`Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W`),
* `CoefTh 3 f ≤ 11059200·α` (this file: the separated product `a(θ)·r(z)` with `a = ∂_θ c2m`,
  `r = L₁₂(F_*)` gives `mixed b i (∂_θ f) = (D_θ^i a)(θ)·D_z^b r(z)`; the angular factor is
  bounded by `144` via `Work.FTS.H2.abs_DthIter_Sfun_le` and the radial one by `4800α`
  via the Stirling expansion `Work.Spaces.DzIter_le_of_pzIter`),

so `Ct·α^{-1/2}·(Cw + 11059200)·α = Ct·(Cw + 11059200)·√α`.  The honesty conjunct is the
`wprod`-clause `N4Norm'.wprod` applied to `f` and `D_z g` (the latter is `HQo α 4` by
`CoercivityFix.QuadPorts.HkMem_Dz_quad` from `HkMem α 5 g`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.NonlinRows.Defs
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The angular factor: `∂_θ c2m(θ) = -3 sin 2θ` and its `D_θ`-iterates -/

/-- `∂_θ c2m = -3 sin(2θ)`, where `c2m θ = cos 2θ - sin²θ`. -/
private theorem hasDerivAt_c2m (θ : ℝ) :
    HasDerivAt (fun θ' => Work.Construction.c2m θ') (-3 * Real.sin (2 * θ)) θ := by
  have hfun : (fun θ' : ℝ => Work.Construction.c2m θ')
      = fun θ' => Real.cos (2 * θ') - Real.sin θ' * Real.sin θ' := by
    funext θ'; rw [Work.Construction.c2m_eq]; ring
  have h : HasDerivAt (fun θ' : ℝ => Work.Construction.c2m θ')
      (-(Real.sin (2 * θ) * 2) - (Real.cos θ * Real.sin θ + Real.sin θ * Real.cos θ)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-(Real.sin (2 * θ) * 2)) θ := by
      have h := (Real.hasDerivAt_cos (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
      simpa [Function.comp_def] using h
    have h2 : HasDerivAt (fun θ' : ℝ => Real.sin θ' * Real.sin θ')
        (Real.cos θ * Real.sin θ + Real.sin θ * Real.cos θ) θ :=
      (Real.hasDerivAt_sin θ).mul (Real.hasDerivAt_sin θ)
    have h3 := h1.sub h2
    rw [hfun]
    exact h3
  have hval : -(Real.sin (2 * θ) * 2) - (Real.cos θ * Real.sin θ + Real.sin θ * Real.cos θ)
      = -3 * Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]; ring
  rw [← hval]
  exact h

/-- `∂_θ c2m = -3 sin(2θ)`. -/
private theorem deriv_c2m (θ : ℝ) :
    deriv (fun θ' => Work.Construction.c2m θ') θ = -3 * Real.sin (2 * θ) :=
  (hasDerivAt_c2m θ).deriv

/-- `∂_θ (c2m(θ)·r(z)) = (∂_θ c2m)(θ)·r(z)`. -/
private theorem pth_c2m_mul_rad (r : ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => Work.Construction.c2m θ * r z)
      = fun z θ => deriv (fun θ' => Work.Construction.c2m θ') θ * r z := by
  funext z θ
  simp only [Work.Spaces.pth]
  rw [deriv_mul_const (hasDerivAt_c2m θ).differentiableAt (r z)]

/-- The mixed derivatives of `∂_θ(c2m(θ)·r(z))` separate into an angular and a radial factor. -/
private theorem mixed_pth_c2m_mul_rad (r : ℝ → ℝ) (b i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed b i (Work.Spaces.pth (fun z θ => Work.Construction.c2m θ * r z)) z θ
      = Work.Spaces.DthIter i (fun _ θ' =>
            deriv (fun θ'' => Work.Construction.c2m θ'') θ') 0 θ * Work.Elliptic.DzdIter b r z := by
  rw [pth_c2m_mul_rad r]
  exact Work.FTS.Nonlinear.Pieces.mixed_ang_rad
    (fun θ => deriv (fun θ'' => Work.Construction.c2m θ'') θ) r b i z θ

/-- `|D_θ^i (∂_θ c2m)| ≤ 144` on `Iθ`, for `i ≤ 3`. -/
private theorem dthIter_deriv_c2m_le (i : ℕ) (hi : i ≤ 3) (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter i (fun _ θ' =>
        deriv (fun θ'' => Work.Construction.c2m θ'') θ') 0 θ| ≤ 144 := by
  have hfun : (fun _ θ' : ℝ => deriv (fun θ'' => Work.Construction.c2m θ'') θ')
      = (fun z θ => (-3) * (fun _ θ' : ℝ => Real.sin (2 * θ')) z θ) := by
    funext z θ'
    rw [deriv_c2m]
  rw [hfun, Work.FTS.Nonlinear.Pieces.RowsN0Aux.DthIter_const_mul]
  rw [abs_mul, show |(-3 : ℝ)| = 3 from by norm_num]
  have hS : (fun _ θ' : ℝ => Real.sin (2 * θ')) = Work.FTS.H2.Sfun := rfl
  rw [hS]
  have hb := Work.FTS.H2.abs_DthIter_Sfun_le i (by omega) (0 : ℝ) hθ
  have hAs0 : 0 ≤ Work.FTS.H2.Asin i := (Work.FTS.H2.Asin_pos i).le
  have hAs : Work.FTS.H2.Asin i ≤ 48 := Work.FTS.H2.Asin_le i hi
  have hsin0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h1 : Work.FTS.H2.Asin i * Real.sin (2 * θ) ≤ 48 :=
    calc Work.FTS.H2.Asin i * Real.sin (2 * θ) ≤ 48 * 1 :=
          mul_le_mul hAs hsin1 hsin0 (by norm_num)
      _ = 48 := by norm_num
  have h2 : |Work.Spaces.DthIter i Work.FTS.H2.Sfun 0 θ| ≤ 48 := le_trans hb h1
  linarith

/-! ## The radial factor: `D_z`-iterates of `L₁₂(F_*) = 2α/(1+z)` -/

/-- The plain `z`-iterates of a radial function. -/
private theorem pzIter_radial (r : ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (fun z _ => r z) z θ = deriv^[k] r z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
      have hfun : (fun z' => Work.Spaces.pzIter k (fun z _ => r z) z' θ) = deriv^[k] r :=
        funext fun z' => ih z'
      show deriv (fun z' => Work.Spaces.pzIter k (fun z _ => r z) z' θ) z = deriv^[k + 1] r z
      rw [hfun, Function.iterate_succ_apply']

/-- `D_z` commutes with equality on the open half-line `(-1,∞)`. -/
private theorem DzdIter_congr_Ioi {u v : ℝ → ℝ} (h : ∀ z ∈ Set.Ioi (-1), u z = v z) :
    ∀ (b : ℕ) (z : ℝ), z ∈ Set.Ioi (-1) →
      Work.Elliptic.DzdIter b u z = Work.Elliptic.DzdIter b v z := by
  intro b
  induction b with
  | zero => intro z hz; exact h z hz
  | succ b ih =>
      intro z hz
      have hev : Work.Elliptic.DzdIter b u =ᶠ[𝓝 z] Work.Elliptic.DzdIter b v :=
        Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hz) (fun y hy => ih y hy)
      show z * deriv (Work.Elliptic.DzdIter b u) z
        = z * deriv (Work.Elliptic.DzdIter b v) z
      rw [hev.deriv_eq]

/-- `2α/(1+z)` is `C^∞` (indeed analytic) on `(-1,∞)`. -/
private theorem contDiffOn_invH (α : ℝ) :
    ContDiffOn ℝ ⊤ (fun z : ℝ => 2 * α / (1 + z)) (Set.Ioi (-1)) := by
  have h : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 + z)⁻¹) (Set.Ioi (-1)) := by
    refine ContDiffOn.inv ?_ ?_
    · have h : ContDiffOn ℝ ⊤ (fun z : ℝ => 1 + z) (Set.Ioi (-1)) := by fun_prop
      exact h
    · intro z hz; simp only [Set.mem_Ioi] at hz; linarith
  have h2 : ContDiffOn ℝ ⊤ (fun z : ℝ => (2 * α) * ((1 + z)⁻¹)) (Set.Ioi (-1)) :=
    ContDiffOn.mul contDiffOn_const h
  refine h2.congr ?_
  intro z _
  simp only [div_eq_mul_inv]

/-- `|z^j ∂_z^j (2α/(1+z))| ≤ 48α` for `j ≤ 4` on `[0,∞)`. -/
private theorem pzIter_invH_bound (α : ℝ) (hα : 0 < α) (j : ℕ) (hj : j ≤ 4) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |z ^ j * Work.Spaces.pzIter j (fun z _ => 2 * α / (1 + z)) z θ| ≤ 48 * α := by
  intro z hzIz θ _
  have hz0 : (0 : ℝ) ≤ z := hzIz
  rw [pzIter_radial (fun z => 2 * α / (1 + z)) j z θ]
  rw [show (fun z : ℝ => 2 * α / (1 + z)) = fun z => (2 * α) * (1 + z)⁻¹ from by
    funext z; rw [div_eq_mul_inv]]
  have hderiv : deriv^[j] (fun z : ℝ => (2 * α) * (1 + z)⁻¹) z
      = (2 * α) * deriv^[j] (fun z : ℝ => (1 + z)⁻¹) z := by
    rw [Work.FTS.Nonlinear.FstarPkg.deriv_iter_const_mul]
  rw [hderiv, Work.FTS.Nonlinear.FstarPkg.iter_deriv_nInvClosed j z (by linarith)]
  have hkey : z ^ j * |Work.FTS.Nonlinear.FstarPkg.nInvClosed j z| ≤ (j.factorial : ℝ) := by
    have h1 := Work.FTS.Nonlinear.FstarPkg.nInvClosed_weighted j z hz0
    have h2 : z ^ j * |Work.FTS.Nonlinear.FstarPkg.nInvClosed j z|
        ≤ (z + 1) ^ j * |Work.FTS.Nonlinear.FstarPkg.nInvClosed j z| :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz0 (by linarith) j) (abs_nonneg _)
    have h3 : (z + 1) ^ j * |Work.FTS.Nonlinear.FstarPkg.nInvClosed j z|
        = |(z + 1) ^ j * Work.FTS.Nonlinear.FstarPkg.nInvClosed j z| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ z + 1) j)]
    rw [h3] at h2
    linarith
  have hfact : (j.factorial : ℝ) ≤ 24 := by
    interval_cases j <;> norm_num
  have hα2 : (0 : ℝ) < 2 * α := by linarith
  have hgoal : |z ^ j * ((2 * α) * Work.FTS.Nonlinear.FstarPkg.nInvClosed j z)|
      = (2 * α) * (z ^ j * |Work.FTS.Nonlinear.FstarPkg.nInvClosed j z|) := by
    have h1 : |(2 : ℝ) * α| = 2 * α := abs_of_nonneg hα2.le
    have h2 : |z ^ j| = z ^ j := abs_of_nonneg (pow_nonneg hz0 j)
    rw [show z ^ j * ((2 * α) * Work.FTS.Nonlinear.FstarPkg.nInvClosed j z)
        = (2 * α) * (z ^ j * Work.FTS.Nonlinear.FstarPkg.nInvClosed j z) from by ring]
    simp only [abs_mul, h1, h2]
  rw [hgoal]
  calc (2 * α) * (z ^ j * |Work.FTS.Nonlinear.FstarPkg.nInvClosed j z|)
      ≤ (2 * α) * (j.factorial : ℝ) := mul_le_mul_of_nonneg_left hkey hα2.le
    _ ≤ (2 * α) * 24 := mul_le_mul_of_nonneg_left hfact hα2.le
    _ = 48 * α := by ring

/-- `|D_z^b (L₁₂(F_*)) z| ≤ 4800α` for `b ≤ 4`, `z > 0`. -/
private theorem DzdIter_L12Fstar_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (b : ℕ) (hb : b ≤ 4)
    {z : ℝ} (hz : 0 < z) :
    |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z|
      ≤ 4800 * α := by
  have hz1 : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  rw [DzdIter_congr_Ioi (u := fun z => Work.Construction.L12 (Work.Construction.Fstar α) z)
    (v := fun z => 2 * α / (1 + z))
    (fun y hy => Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1 hy) b z hz1]
  have hθ0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hmain := Work.Spaces.DzIter_le_of_pzIter (h := fun z _ => 2 * α / (1 + z))
    (M := 48 * α) (by positivity)
    (fun θ _ => contDiffOn_invH α)
    (fun j hj z hzIz θ hθ => pzIter_invH_bound α hα j hj z hzIz θ hθ)
    b hb z (le_of_lt hz) 0 hθ0
  have hrew : |Work.Spaces.DzIter b (fun z _ => 2 * α / (1 + z)) z 0|
      = |Work.Elliptic.DzdIter b (fun z => 2 * α / (1 + z)) z| := by
    rw [Work.Elliptic.DzIter_rad (fun z => 2 * α / (1 + z)) b z 0]
  rw [hrew] at hmain
  rw [show (100 : ℝ) * (48 * α) = 4800 * α from by ring] at hmain
  exact hmain

/-! ## The flat angular norm of the row-7 coefficient -/

/-- The per-slot bound behind `CoefThMem 3` for `f = c2m(θ)·L₁₂(F_*)(z)`. -/
private theorem coefTh_slot_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (b i : ℕ) (hbi : b + i ≤ 3) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b i (Work.Spaces.pth (fun z θ => Work.Construction.c2m θ *
        Work.Construction.L12 (Work.Construction.Fstar α) z)) z θ| ≤ 144 * (4800 * α) := by
  intro z θ hz hθ0 hθ1
  have hθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hi3 : i ≤ 3 := by omega
  have hb4 : b ≤ 4 := by omega
  rw [mixed_pth_c2m_mul_rad (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z)
    b i z θ]
  rw [abs_mul]
  exact mul_le_mul (dthIter_deriv_c2m_le i hi3 θ hθ)
    (DzdIter_L12Fstar_le α hα hα1 b hb4 hz) (abs_nonneg _) (by positivity)

/-- `CoefThMem 3` for `f = c2m(θ)·L₁₂(F_*)(z)`. -/
private theorem coefThMem_c2mL12 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.VocabO.CoefThMem 3 (fun z θ => Work.Construction.c2m θ *
      Work.Construction.L12 (Work.Construction.Fstar α) z) :=
  fun b i hbi => ⟨144 * (4800 * α), coefTh_slot_le α hα hα1 b i hbi⟩

/-- `CoefTh 3 f ≤ 16·144·4800·α = 11059200·α` for `f = c2m(θ)·L₁₂(F_*)(z)`. -/
private theorem coefTh_c2mL12_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.VocabO.CoefTh 3 (fun z θ => Work.Construction.c2m θ *
      Work.Construction.L12 (Work.Construction.Fstar α) z) ≤ 11059200 * α := by
  have hconst : ∀ c : ℝ, (∑ _b ∈ Finset.range 4, ∑ _i ∈ Finset.range 4, c) = 16 * c := by
    intro c
    simp [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    ring
  rw [Work.FTS.VocabO.CoefTh]
  calc (∑ b ∈ Finset.range (3 + 1), ∑ i ∈ Finset.range (3 + 1),
        if b + i ≤ 3 then Work.FTS.H2.supAbsO
          (Work.Spaces.mixed b i (Work.Spaces.pth (fun z θ => Work.Construction.c2m θ *
            Work.Construction.L12 (Work.Construction.Fstar α) z))) else 0)
      ≤ ∑ _b ∈ Finset.range 4, ∑ _i ∈ Finset.range 4, (144 * (4800 * α)) := by
        refine Finset.sum_le_sum fun b hb => Finset.sum_le_sum fun i hi => ?_
        by_cases hc : b + i ≤ 3
        · rw [if_pos hc]
          exact Work.FTS.H2.supAbsO_le (coefTh_slot_le α hα hα1 b i hc)
        · rw [if_neg hc]
          positivity
    _ = 11059200 * α := by
        rw [hconst]
        ring

/-! ## Smoothness of the coefficient -/

/-- `SmoothOpen` of the row-7 coefficient `c2m(θ)·L₁₂(F_*)(z)` (written as the explicit
separated product `c2m(θ)·2α/(1+z)` on the open quadrant). -/
private theorem smoothOpen_c2mL12 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.c2m θ *
      Work.Construction.L12 (Work.Construction.Fstar α) z) := by
  have hexp : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z))) := by
    change ContDiffOn ℝ Work.Stability.smoothOrder
      ((fun p : ℝ × ℝ => Work.Construction.c2m p.2) *
        (fun p : ℝ × ℝ => 2 * α / (1 + p.1))) Work.FTS.EllipticEst.Q0
    refine ContDiffOn.mul ?_ ?_
    · have hc : ContDiff ℝ Work.Stability.smoothOrder
          (fun θ : ℝ => Work.Construction.c2m θ) := by
        rw [show (fun θ : ℝ => Work.Construction.c2m θ)
            = fun θ => Real.cos (2 * θ) - Real.sin θ ^ 2 from by
              funext θ; rw [Work.Construction.c2m_eq]]
        fun_prop
      exact hc.comp_contDiffOn contDiffOn_snd
    · have hden : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun p : ℝ × ℝ => 1 + p.1) Work.FTS.EllipticEst.Q0 := by fun_prop
      have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, 1 + p.1 ≠ 0 := by
        intro p hp
        have := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
        linarith
      have hinv := hden.inv hne
      have hmul : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun p : ℝ × ℝ => (2 * α) * (1 + p.1)⁻¹) Work.FTS.EllipticEst.Q0 :=
        ContDiffOn.mul contDiffOn_const hinv
      refine hmul.congr ?_
      intro p _
      simp only [div_eq_mul_inv]
  refine ContDiffOn.congr hexp ?_
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry]
  rw [Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1 (by linarith)]

theorem NRow7 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.NonlinRows.Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N06F α g) ∧
        |IP α (Work.FTS.Nonlin.N06F α g) g|
          ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
  obtain ⟨Cw, hCwpos, hW⟩ := Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W
  refine ⟨Ct * (Cw + 11059200) + 1, by nlinarith [hE.pos.1, hCwpos], ?_⟩
  intro α g Φs Φg hctx
  have hα := hctx.hα
  have hα1 := hctx.hα1
  have hαα₂ := hctx.hαα₂
  have hgal := hctx.hg
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hreg4 : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
  obtain ⟨hWmem, hWle⟩ := hW α hα hα1
  set f : Fn := fun z θ => Work.Construction.c2m θ *
    Work.Construction.L12 (Work.Construction.Fstar α) z with hf
  have hfsm : Work.FTS.EllipticEst.SmoothOpen f := by rw [hf]; exact smoothOpen_c2mL12 α hα hα1
  have hWmem' : Work.Spaces.WlInfMem α 4 f := by rw [hf]; exact hWmem
  have hCTmem : Work.FTS.VocabO.CoefThMem 3 f := by
    rw [hf]; exact coefThMem_c2mL12 α hα hα1
  have hCTle : Work.FTS.VocabO.CoefTh 3 f ≤ 11059200 * α := by
    rw [hf]; exact coefTh_c2mL12_le α hα hα1
  have hHQoDz : Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dz g) :=
    ⟨(Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hgal.reg.1).Dz,
      Work.FTS.CoercivityFix.QuadPorts.HkMem_Dz_quad α 4 hgal.reg.1
        (Work.FTS.OpenPkg.galClass_HkMem5 hgal)⟩
  have hprod := hN.wprod α hIoc f (Work.Spaces.Dz g) hfsm hWmem' hHQoDz
  have hfun : Work.FTS.Nonlin.N06F α g = fun z θ => -(f z θ * Work.Spaces.Dz g z θ) := by
    funext z θ
    rw [hf]
    simp only [Work.FTS.Nonlin.N06F, Work.Construction.N06]
    ring
  constructor
  · have hneg : Work.Spaces.HkMem α 4 (-(fun z θ => f z θ * Work.Spaces.Dz g z θ)) := by
      unfold Work.Spaces.HkMem
      rw [Work.FTS.EllipticEst.HkIntegrand_neg]
      exact hprod.1
    rwa [hfun]
  · rw [hfun, hE.neg α hIoc (fun z θ => f z θ * Work.Spaces.Dz g z θ) g hprod.1 hreg4, abs_neg]
    have ht3 := hE.t3 α hIoc f g hfsm hWmem' hCTmem hreg4
      (Work.FTS.OpenPkg.galClass_HkMem5 hgal) (Work.FTS.OpenPkg.galClass_DecayAll4 hgal)
    refine ht3.trans ?_
    have hsum : Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f ≤ (Cw + 11059200) * α := by
      linarith
    have hsqrt : α ^ (-(1 / 2 : ℝ)) * α = Real.sqrt α := by
      have h := Real.rpow_add hα (-(1 / 2 : ℝ)) 1
      rw [Real.rpow_one] at h
      rw [Real.sqrt_eq_rpow, ← h]
      norm_num
    have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    calc Ct * α ^ (-(1 / 2 : ℝ)) * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f)
          * Work.FTS.Nonlin.Xn α g ^ 2
        ≤ Ct * α ^ (-(1 / 2 : ℝ)) * ((Cw + 11059200) * α)
            * Work.FTS.Nonlin.Xn α g ^ 2 := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum ?_)
            (pow_nonneg hX 2)
          exact mul_nonneg hE.pos.1.le (Real.rpow_nonneg hα.le _)
      _ = (Ct * (Cw + 11059200)) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
          rw [← hsqrt]; ring
      _ ≤ (Ct * (Cw + 11059200) + 1) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
          refine mul_le_mul_of_nonneg_right (by linarith) ?_
          exact mul_nonneg (Real.sqrt_nonneg α) (pow_nonneg hX 2)

end Work.FTS.NonlinRows
