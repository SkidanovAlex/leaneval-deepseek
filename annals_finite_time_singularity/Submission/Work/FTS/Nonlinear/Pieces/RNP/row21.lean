/-
# Row 21 of the design table: `|N₄^{g*}|_{ℋ⁴} ≤ C α^{3/2} X`

`N₄^{g*}(z,θ) = -(1/2) sin(2θ) · FK(g)(z) · ∂_θF_*(z,θ)` (row 21 of the table of
`Submission/Work/FTS/Nonlinear/NOTES_N4.md`).  Since `F_*(z,θ) = α(Γ(θ)/c)·2 hKer(z)` with
`hKer z = z/(1+z)²` and `D_θF_* = sin(2θ)·∂_θF_*`, the piece factors as a product of an
*angular* profile and a *radial* function:

  `N₄^{g*} = A(θ) · (FK(g)(z) · hKer(z))`,  `A(θ) = -(α/c α)·D_θΓ(θ)`.

Two ingredients:

* `FKhKerProd`: the radial function `z ↦ FK(g)(z)·hKer(z)` is in `ℋ⁴` with norm at most
  `10^12·|g|_{ℋ⁴}` (the Leibniz rules for the radial factor `FK g` follow from the `C⁴`-bound
  `RNP24.fk_contDiffOn_four`, the `ℋ⁴`-membership of `FK g` from the weighted `L²`-bounds
  `RNP24.dzdIter_FK_eq_qang` / `N4Fields.Qang_sq_w_sq_integral`);
* `XnAngProfHKer`: the angular profile `A` is `O(α²)` together with all its `D_θ`-iterates up
  to order `4` (the sharp bound `dthU_pow_Gam_sharp`), and the separation lemma
  `Xn_ang_rad_le_gen` (row 23) turns this into
  `Xn α (A · r) ≤ α²·K·Xn α r` for every radial `r ∈ ℋ⁴`.

The `α^{3/2}` of the stated bound is then immediate from `α² ≤ α^{3/2}` for `α ≤ 1`.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row23
import Submission.Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.fk_contDiffOn_four
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row22
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.dzIter_mixed_mul_rad
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.dzdIter_FK_eq_qang
import Submission.Work.FTS.Nonlinear.N4Fields.Qang_sq_w_sq_integral
import Submission.Work.FTS.Nonlinear.N4Fields.DzdIter_Qang_ae

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The factorisation of the piece -/

/-- **`N₄^{g*}` is the product of the angular profile `A` and the radial function `FK g · hKer`.**
Unconditional (no regularity hypothesis is used): it is the algebra
`∂_θF_*(z,θ) = (α·F_*'(z)/c α)·Γ'(θ)`, `F_*'(z) = 2 hKer z`, `D_θΓ = sin(2θ)Γ'`. -/
theorem N4gs_factor (α : ℝ) (g : Work.FTS.Galerkin.Fn) :
    Work.FTS.Nonlin.N4gs α g = fun z θ =>
      (-(α / Work.Spaces.c α) * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ)
        * (Work.Construction.FK g z * Work.Spaces.hKer z) := by
  funext z θ
  rw [Work.FTS.Nonlin.N4gs, Work.Construction.s2]
  have hpth : Work.Spaces.pth (Work.Construction.Fstar α) z θ
      = (α * Work.FM.Fstar z / Work.Spaces.c α)
          * deriv (fun t => Work.Spaces.Gam α t) θ := by
    rw [Work.Spaces.pth]
    rw [show (fun θ' => Work.Construction.Fstar α z θ')
        = fun θ' => (α * Work.FM.Fstar z / Work.Spaces.c α) * Work.Spaces.Gam α θ' from by
      funext θ'; rw [Work.Construction.Fstar]; ring]
    rw [Work.Spaces.deriv_const_mul']
  rw [hpth, Work.Spaces.dthU_apply, Work.Spaces.hKer_apply, Work.FM.Fstar]
  ring

/-! ## The angular profile `A = -(α/c)·D_θΓ` against a radial function -/

/-- **The separation estimate for the angular profile `A θ = -(α/c α)·D_θΓ(θ)`.**  For every
radial function `r` in `ℋ⁴`, `Xn α (A · r) ≤ α²·K·Xn α r`, with `K` independent of `α` (and
of `r`).  The profile is `O(α²)` together with its `D_θ`-iterates up to order `4`, with the
sharp endpoint behaviour of `dthU_pow_Gam_sharp`; `Xn_ang_rad_le_gen` (row 23) converts this
into the stated bound. -/
theorem XnAngProfHKer :
    ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ r : ℝ → ℝ,
      Work.Spaces.HkMem α 4 (fun z _ => r z) →
      Work.FTS.Nonlin.Xn α (fun z θ =>
          (-(α / Work.Spaces.c α) * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ) * r z)
        ≤ α ^ 2 * K * Work.FTS.Nonlin.Xn α (fun z θ => r z) := by
  obtain ⟨Cg, hCgpos, hCg⟩ := dthU_pow_Gam_sharp
  obtain ⟨M, hMpos, hM⟩ := gamWeightInt
  refine ⟨Real.sqrt (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) + 1, by positivity, ?_⟩
  intro α hα hα1 r hrmem
  set A : ℝ → ℝ := fun θ => -(α / Work.Spaces.c α)
    * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ with hA
  set G : ℝ → ℝ := fun θ => Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) with hG
  have hcge : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hcnn : (0 : ℝ) ≤ α / Work.Spaces.c α := div_nonneg hα.le hcpos.le
  have hc2 : α / Work.Spaces.c α ≤ 10 * α := by
    rw [div_le_iff₀ hcpos]; nlinarith [hcge, hα]
  have hGnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ G θ := by
    intro θ hθ
    have h1 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have h2 : 0 ≤ Real.sin (2 * θ) := Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
    rw [hG]; positivity
  have ha0 : ∀ θ ∈ Work.Spaces.Iθ, |A θ| ≤ 27 * α ^ 2 := by
    intro θ hθ
    have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have hΓ1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
    have hb : |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        ≤ (4 / 3) * α * Work.Spaces.Gam α θ := by
      have hrepr : Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
          = Work.Spaces.DthIter 1 (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ := by
        rw [Work.FTS.LocData.DthIter_rad_eq 1 (fun t => Work.Spaces.Gam α t) 0 θ,
          Function.iterate_one]
      rw [hrepr]; exact dthIter_one_Gam_le hα hα1 θ hθ
    have habs : |A θ| = (α / Work.Spaces.c α)
        * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ| := by
      rw [hA]; simp only
      rw [abs_mul, abs_neg, abs_of_nonneg hcnn]
    rw [habs]
    calc (α / Work.Spaces.c α) * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        ≤ (α / Work.Spaces.c α) * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
          mul_le_mul_of_nonneg_left hb hcnn
      _ ≤ (10 * α) * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
          mul_le_mul_of_nonneg_right hc2 (mul_nonneg (by positivity) hΓ0)
      _ ≤ 27 * α ^ 2 := by
          have h := mul_le_mul_of_nonneg_left hΓ1 (by positivity : (0 : ℝ) ≤ (40 / 3) * α ^ 2)
          nlinarith [h, sq_nonneg α]
  have ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => A θ') 0 θ| ≤ (20 * Cg * α ^ 2) * G θ := by
    intro i hi hi4 θ hθ
    have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have hsin2 : 0 ≤ Real.sin (2 * θ) :=
      Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
    have hrepr : Work.Spaces.DthIter i (fun _ (θ' : ℝ) => A θ') 0 θ
        = (-(α / Work.Spaces.c α))
          * Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ := by
      rw [Work.FTS.LocData.DthIter_rad_eq i A 0 θ]
      simp only [hA]
      rw [Work.Spaces.dthU_iter_const_mul, Work.Spaces.dthU_iter_comp]
    rw [hrepr, abs_mul, abs_neg, abs_of_nonneg hcnn, hG]
    have hchild := hCg α hα hα1 θ hθ (i + 1) (by omega) (by omega)
    have h1 : (α / Work.Spaces.c α)
          * |Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ|
        ≤ (α / Work.Spaces.c α)
          * (Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
      mul_le_mul_of_nonneg_left hchild hcnn
    have h2 : (α / Work.Spaces.c α)
          * (Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
        ≤ (20 * Cg * α ^ 2) * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by
      rw [show (α / Work.Spaces.c α)
            * (Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
          = ((α / Work.Spaces.c α) * Cg * α)
            * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) from by ring]
      refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hΓ0 (by linarith [hα, hsin2]))
      calc (α / Work.Spaces.c α) * Cg * α = (α / Work.Spaces.c α) * (Cg * α) := by ring
        _ ≤ (10 * α) * (Cg * α) := mul_le_mul_of_nonneg_right hc2 (by positivity)
        _ = 10 * Cg * α ^ 2 := by ring
        _ ≤ 20 * Cg * α ^ 2 := by nlinarith [hCgpos, sq_nonneg α]
    exact h1.trans h2
  obtain ⟨hI1, hm1⟩ := hM α hα hα1
  have hGae : (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
      = fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ := by
    funext θ; rw [hG]; ring
  have hI1' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ := by
    rw [hGae]; exact hI1
  have hm1' : ∫ θ in Work.Spaces.Iθ, G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ ≤ M := by
    rw [hGae]; exact hm1
  have hmain := Xn_ang_rad_le_gen α hα A r G (B0 := 27 * α ^ 2) (B1 := 20 * Cg * α ^ 2)
    (M1 := M) (by positivity) (by positivity) (le_of_lt hMpos) hGnn ha0 ha1 hI1' hm1' hrmem
  have hsqrt : Real.sqrt ((27 * α ^ 2) ^ 2 * 10000 + 4 * (20 * Cg * α ^ 2) ^ 2 * M)
      = α ^ 2 * Real.sqrt (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) := by
    rw [show (27 * α ^ 2) ^ 2 * 10000 + 4 * (20 * Cg * α ^ 2) ^ 2 * M
        = (α ^ 2) ^ 2 * (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) from by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α (fun z θ => r z) := Work.Spaces.HkNorm_nonneg α 4 _
  have hSnn : 0 ≤ Real.sqrt (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) := Real.sqrt_nonneg _
  calc Work.FTS.Nonlin.Xn α (fun z θ => A θ * r z)
      ≤ Real.sqrt ((27 * α ^ 2) ^ 2 * 10000 + 4 * (20 * Cg * α ^ 2) ^ 2 * M)
          * Work.FTS.Nonlin.Xn α (fun z θ => r z) := hmain
    _ = α ^ 2 * Real.sqrt (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M)
          * Work.FTS.Nonlin.Xn α (fun z θ => r z) := by rw [hsqrt]
    _ ≤ α ^ 2 * (Real.sqrt (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) + 1)
          * Work.FTS.Nonlin.Xn α (fun z θ => r z) := by
        nlinarith [hSnn, hX0, sq_nonneg α, mul_nonneg (sq_nonneg α) hX0]

/-! ## Auxiliary facts about the radial profile `hKer` -/

/-- `z ↦ hKer z = z/(1+z)²` is smooth in the analytic class, in the sense of `SmoothInt`. -/
private lemma hker_smoothInt : Work.Spaces.SmoothInt (fun z (θ : ℝ) => Work.Spaces.hKer z) := by
  have hfun : (fun z (θ : ℝ) => Work.Spaces.hKer z)
      = fun z (θ : ℝ) => z / (1 + z) ^ 2 := by
    funext z θ; rw [Work.Spaces.hKer_apply]
  rw [hfun]
  constructor
  · have hun : Function.uncurry (fun z (θ : ℝ) => z / (1 + z) ^ 2)
        = fun p : ℝ × ℝ => p.1 / (1 + p.1) ^ 2 := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hun]
    refine ContDiffOn.div contDiffOn_fst ?_ ?_
    · exact (contDiffOn_const.add contDiffOn_fst).pow 2
    · intro p hp
      simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp
      have h1 : 0 < 1 + p.1 := by linarith [hp.1]
      positivity
  · intro θ hθ
    refine ContDiffOn.div contDiffOn_id ?_ ?_
    · exact (contDiffOn_const.add contDiffOn_id).pow 2
    · intro z hz
      rw [Set.mem_Ioi] at hz
      have h1 : 0 < 1 + z := by linarith
      positivity

/-- `hKer` is of class `𝒲^{4,∞}` with norm at most `200`. -/
private lemma hker_wlInfMem (α : ℝ) :
    Work.Spaces.WlInfMem α 4 (fun z (θ : ℝ) => Work.Spaces.hKer z) := by
  simpa using (Work.FTS.Nonlinear.Pieces.RNP.hKerConstWlInf α 1).1

/-- **The `D_z`-iterates of `hKer` are bounded by `3000` on `Iz`.** -/
private lemma hker_dzdIter_le {α : ℝ} (hα : 0 < α) {m : ℕ} (hm : m ≤ 4) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) :
    |Work.Elliptic.DzdIter m (fun z => Work.Spaces.hKer z) z| ≤ 3000 := by
  have hSI : Work.Spaces.SmoothInt (fun z (θ : ℝ) => Work.Spaces.hKer z) := hker_smoothInt
  have hmem : Work.Spaces.WlInfMem α 4 (fun z (θ : ℝ) => Work.Spaces.hKer z) := hker_wlInfMem α
  have hW : Work.Spaces.WlInf α 4 (fun z (θ : ℝ) => Work.Spaces.hKer z) ≤ 200 := by
    simpa using (Work.FTS.Nonlinear.Pieces.RNP.hKerConstWlInf α 1).2
  have h := Work.Spaces.DzIter_le_WlInf hα hSI hmem hm hz Work.Spaces.zero_mem_Iθ
  rw [Work.Elliptic.DzIter_rad] at h
  calc |Work.Elliptic.DzdIter m (fun z => Work.Spaces.hKer z) z|
      ≤ 15 * Work.Spaces.WlInf α 4 (fun z (θ : ℝ) => Work.Spaces.hKer z) := h
    _ ≤ 15 * 200 := by linarith [hW]
    _ ≤ 3000 := by norm_num

/-- The two angular constants: `∫_θ Kθ²` and `∫_θ sin(2θ)^{-η}`. -/
private lemma Ktheta_sq_integral_le :
    (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) ≤ 18 := by
  have hKth : ∀ θ ∈ Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 ≤ 9 := by
    intro θ hθ
    have h1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
    have h2 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
    have h3 : |Work.Elliptic.Ktheta θ| ≤ 3 := by
      rw [Work.Elliptic.Ktheta]
      calc |3 * Real.sin θ * Real.cos θ ^ 2|
          = 3 * |Real.sin θ| * |Real.cos θ| ^ 2 := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3), abs_pow]
        _ ≤ 3 * 1 * 1 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) ?_ ?_ (by norm_num)
            · calc |Real.cos θ| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
                _ = 1 := by norm_num
            · positivity
        _ = 3 := by norm_num
    calc Work.Elliptic.Ktheta θ ^ 2 = |Work.Elliptic.Ktheta θ| ^ 2 := (sq_abs _).symm
      _ ≤ 3 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
      _ = 9 := by norm_num
  have hvol : MeasureTheory.volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hint : MeasureTheory.IntegrableOn (fun _ : ℝ => (9 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (μ := MeasureTheory.volume) (s := Work.Spaces.Iθ)
      (C := (9 : ℝ)) hvol
  calc (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      ≤ ∫ _θ in Work.Spaces.Iθ, (9 : ℝ) := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun θ => sq_nonneg _)) hint ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact hKth θ hθ
    _ = 9 * (Real.pi / 2) := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def,
          Work.Spaces.Iθ, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2 - 0)]
        ring
    _ ≤ 18 := by have := Real.pi_lt_four; linarith

private lemma sin_rpow_integral_le :
    (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ≤ 10 ^ 4 := by
  have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
    (by rw [Work.Spaces.eta]; norm_num) (by rw [Work.Spaces.eta]; norm_num)).2
  have hval : (-(Work.Spaces.eta)) + 1 = (1 : ℝ) / 100 := by rw [Work.Spaces.eta]; norm_num
  rw [hval] at h
  norm_num at h
  linarith

/-! ## The Leibniz rule for the product `Qang g 0 · hKer` -/

/-- `z ↦ hKer z = z/(1+z)²` is `SmoothQuad`. -/
private lemma hker_smoothQuad :
    Work.FTS.LocData.SmoothQuad (fun z (θ : ℝ) => Work.Spaces.hKer z) :=
  hker_smoothInt.1.of_le le_top

/-- **The pure `D_z`-slots of `Qang g 0 · hKer` expand by the binomial Leibniz rule**,
pointwise on `Ioi 0`.  This is the first conjunct of `dzIter_mixed_mul_rad`
(`R = Qang g 0`, `h = hKer`), evaluated at a fixed angle `θ = π/4`. -/
theorem qang_hker_dzdIter (g : ℝ → ℝ → ℝ)
    (hR : ContDiffOn ℝ 4 (fun z => Work.Elliptic.Qang g 0 z) (Set.Ioi (0 : ℝ))) :
    ∀ i : ℕ, i ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z) z
        = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
                * Work.Elliptic.DzdIter (i - b) (fun z => Work.Spaces.hKer z) z) := by
  have hDz := (Work.FTS.Nonlinear.Pieces.RNP.RNP24.dzIter_mixed_mul_rad
    (R := fun z => Work.Elliptic.Qang g 0 z) (h := fun z (θ : ℝ) => Work.Spaces.hKer z)
    hR hker_smoothQuad).1
  intro i hi
  have hθ0 : (Real.pi / 4) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hpoint : ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z) z
        = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
                * Work.Elliptic.DzdIter (i - b) (fun z => Work.Spaces.hKer z) z) := by
    intro z hz
    have h := hDz i hi z (Set.mem_Ioi.mpr hz) (Real.pi / 4) hθ0
    rw [show Work.Spaces.DzIter i
          (fun z (θ : ℝ) => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z) z (Real.pi / 4)
        = Work.Elliptic.DzdIter i
            (fun z => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z) z from by
      rw [Work.Elliptic.DzIter_rad]] at h
    rw [h]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [show Work.Spaces.DzIter (i - b) (fun z (θ : ℝ) => Work.Spaces.hKer z) z (Real.pi / 4)
        = Work.Elliptic.DzdIter (i - b) (fun z => Work.Spaces.hKer z) z from by
      rw [Work.Elliptic.DzIter_rad]]
  intro z hz
  exact hpoint z hz
/-- **The weighted `L²`-bound for the `D_z`-iterates of `Qang g 0`.**

`Work.FTS.Nonlinear.N4Fields.Qang_sq_w_sq_integral` gives the bound for the angular moments
`Qang g b`; the pointwise identity `DzdIter b (Qang g 0) = Qang g b` holds almost everywhere
(`Work.FTS.Nonlinear.N4Fields.DzdIter_Qang_ae`), so it transfers to the `D_z`-iterates. -/
theorem qang_dzdIter_sq_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ b : ℕ, b ≤ 4 → MeasureTheory.IntegrableOn
        (fun z => (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      ∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z) ^ 2
          * (Work.Spaces.w z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 4 g := by
  intro b hb
  have hae : ∀ᵐ z ∂(MeasureTheory.volume), z ∈ Work.Spaces.Iz → ∀ i ∈ Finset.range 5,
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z) z
        = Work.Elliptic.Qang g i z := by
    filter_upwards [Work.FTS.Nonlinear.N4Fields.DzdIter_Qang_ae hsm hmem,
      MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)] with z hz hne hzI
    exact hz (lt_of_le_of_ne hzI (Ne.symm hne))
  have haeIz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), ∀ i ∈ Finset.range 5,
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z) z
        = Work.Elliptic.Qang g i z := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [hae] with z hz hzI
    exact hz hzI
  have htrans : (fun z => (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z) ^ 2
        * (Work.Spaces.w z) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      fun z => (Work.Elliptic.Qang g b z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    filter_upwards [haeIz] with z hz
    rw [hz b (Finset.mem_range.mpr (by omega))]
  obtain ⟨hint, hbd⟩ :=
    Work.FTS.Nonlinear.N4Fields.Qang_sq_w_sq_integral hα hα1 hsm hmem (i := b) hb
  refine ⟨hint.congr htrans.symm, ?_⟩
  rw [MeasureTheory.integral_congr_ae htrans]
  exact hbd

/-! ## The smoothness shift `f ↦ Dzd f` -/

/-- `Dzd = z ∂_z` lowers the smoothness order by one on `(0,∞)`. -/
private lemma contDiffOn_Dzd_of_contDiffOn {u : ℝ → ℝ} {m : ℕ}
    (hu : ContDiffOn ℝ (m + 1) u (Set.Ioi (0:ℝ))) :
    ContDiffOn ℝ m (Work.Elliptic.Dzd u) (Set.Ioi (0:ℝ)) := by
  have hderiv : ContDiffOn ℝ m (deriv u) (Set.Ioi (0:ℝ)) :=
    (ContDiffOn.derivWithin hu (uniqueDiffOn_Ioi 0) (le_refl _)).congr
      (fun x hx => (derivWithin_of_isOpen isOpen_Ioi hx).symm)
  show ContDiffOn ℝ m (fun z => z * deriv u z) (Set.Ioi (0:ℝ))
  simpa only [id_eq] using
    (contDiffOn_id (𝕜 := ℝ) (n := (m : WithTop ℕ∞)) (s := Set.Ioi (0:ℝ))).mul hderiv

/-- The `Dzd`-iterates of a `C^n` function of `z` alone are continuous up to order `n`. -/
private lemma continuousOn_dzdIter_of_contDiffOn {f : ℝ → ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ n f (Set.Ioi (0:ℝ))) :
    ∀ i : ℕ, i ≤ n → ContinuousOn (Work.Elliptic.DzdIter i f) (Set.Ioi (0:ℝ)) := by
  have hmain : ∀ i : ℕ, i ≤ n →
      ContDiffOn ℝ (((n - i : ℕ) : WithTop ℕ∞)) (Work.Elliptic.DzdIter i f)
        (Set.Ioi (0:ℝ)) := by
    intro i
    induction i with
    | zero => intro _; simpa using hf
    | succ i ih =>
        intro hi
        have hi' : i ≤ n := by omega
        have hni : 1 ≤ n - i := by omega
        have hprev : ContDiffOn ℝ (((n - i : ℕ) : WithTop ℕ∞)) (Work.Elliptic.DzdIter i f)
            (Set.Ioi (0:ℝ)) := ih hi'
        have hprev' : ContDiffOn ℝ (((n - i - 1 : ℕ) : WithTop ℕ∞) + 1)
            (Work.Elliptic.DzdIter i f) (Set.Ioi (0:ℝ)) := by
          have hcast : (((n - i - 1 : ℕ) : WithTop ℕ∞) + 1
              = (((n - i - 1) + 1 : ℕ) : WithTop ℕ∞)) := by push_cast; ring
          rw [hcast, Nat.sub_add_cancel hni]
          exact hprev
        have hstep := contDiffOn_Dzd_of_contDiffOn (u := Work.Elliptic.DzdIter i f)
          (m := n - i - 1) hprev'
        have hidx : (n - (i + 1) : ℕ) = n - i - 1 := Nat.sub_succ n i
        rw [Work.Elliptic.DzdIter_succ, hidx]
        exact hstep
  intro i hi
  exact (hmain i hi).continuousOn

/-- `hKer` is `C^k` on `(0,∞)` for every `k`. -/
private lemma hker_contDiffOn (k : ℕ) :
    ContDiffOn ℝ k (fun z => Work.Spaces.hKer z) (Set.Ioi (0:ℝ)) :=
  ((hker_smoothInt.2 0 Work.Spaces.zero_mem_Iθ).of_le
    (le_top : ((k : ℕ) : WithTop ℕ∞) ≤ ⊤)).mono
    (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0))

/-! ## The product bound -/

/-- **The radial product `FK g · hKer` is in `ℋ⁴` with norm `≤ 10^12 |g|_{ℋ⁴}`.**

`r z = FK(g)(z)·hKer(z)` with `hKer z = z/(1+z)²`.  Writing `FK g = Qang g 0` (`u`) and
`hKer` (`hv`), the pure `D_z`-slots of `r` expand by the binomial Leibniz rule
(`qang_hker_dzdIter`); each `|DzdIter b u|` is controlled in the weighted `L²`-norm by
`Qang_sq_w_sq_integral` (`qang_dzdIter_sq_le`) and each `|DzdIter m hv|` is bounded by `3000`
(`hker_dzdIter_le`), which gives `HkSq α 4 r ≤ (25·(5·256·3000²)·Kθ·Cθ)·HkSq α 4 g` and hence
the stated bound (`Kθ = ∫_θ Kθ² ≤ 18`, `Cθ = ∫_θ sin(2θ)^{-η} ≤ 10^4`). -/
theorem FKhKerProd {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 6 g)
    (hR : ContDiffOn ℝ 4 (fun z => Work.Construction.FK g z) (Set.Ioi (0 : ℝ))) :
    Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.FK g z * Work.Spaces.hKer z) ∧
    Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK g z * Work.Spaces.hKer z)
      ≤ 10 ^ 12 * Work.FTS.Nonlin.Xn α g := by
  have hmem5 : Work.Spaces.HkMem α 5 g := Work.GalerkinFix.RegQ.HkMem_mono_Q hsm hmem
  have hmem4 : Work.Spaces.HkMem α 4 g := Work.GalerkinFix.RegQ.HkMem_mono_Q hsm hmem5
  -- ## `FK g = Qang g 0`
  have hFKu : (fun z => Work.Construction.FK g z) = fun z => Work.Elliptic.Qang g 0 z := by
    funext z
    rw [Work.Construction.FK, Work.Elliptic.Qang]
    refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    rw [Work.Elliptic.Ktheta_eq_K]
    simp only [Work.Spaces.DzIter_zero]
    ring
  have hfun : (fun z (θ : ℝ) => Work.Construction.FK g z * Work.Spaces.hKer z)
      = fun z (θ : ℝ) => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z := by
    funext z θ; rw [congrFun hFKu z]
  have hRu : ContDiffOn ℝ 4 (fun z => Work.Elliptic.Qang g 0 z) (Set.Ioi (0 : ℝ)) :=
    hR.congr (fun z _ => (congrFun hFKu z).symm)
  rw [hfun]
  have hpure := qang_hker_dzdIter g hRu
  have hintb := qang_dzdIter_sq_le hα hα1 hsm hmem4
  have haz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)] with z hne hz
    exact lt_of_le_of_ne hz (Ne.symm hne)
  -- ## the pointwise bound for one slot
  have hpt : ∀ i : ℕ, i ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z) z
          * Work.Spaces.w z) ^ 2
      ≤ (5 * (256 * 3000 ^ 2)) * ∑ b ∈ Finset.range (i + 1),
            (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
              * Work.Spaces.w z) ^ 2 := by
    intro i hi z hz
    have hzI : z ∈ Work.Spaces.Iz := by
      simpa only [Work.Spaces.Iz, Set.mem_Ici] using le_of_lt hz
    rw [hpure i hi z hz]
    set X : ℕ → ℝ := fun b => (i.choose b : ℝ)
      * (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
          * Work.Elliptic.DzdIter (i - b) (fun z => Work.Spaces.hKer z) z) with hX
    have hsumw : (∑ b ∈ Finset.range (i + 1), X b) * Work.Spaces.w z
        = ∑ b ∈ Finset.range (i + 1), X b * Work.Spaces.w z := Finset.sum_mul _ _ _
    rw [hsumw]
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
      (f := fun b => X b * Work.Spaces.w z)
    have hcard : ((Finset.range (i + 1)).card : ℝ) ≤ 5 := by
      rw [Finset.card_range]; exact_mod_cast (by omega : i + 1 ≤ 5)
    have hterm : ∀ b ∈ Finset.range (i + 1), (X b * Work.Spaces.w z) ^ 2
        ≤ (256 * 3000 ^ 2) * ((Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
            * Work.Spaces.w z) ^ 2) := by
      intro b hb
      have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
      have hib : i - b ≤ 4 := by omega
      have hc : (((i.choose b : ℕ) : ℝ)) ^ 2 ≤ 256 := by
        have h1 := Work.FTS.Nonlinear.RadialProd.choose_le_sixteen (i := i) (b := b) hi
        have h2 : (0 : ℝ) ≤ ((i.choose b : ℕ) : ℝ) := Nat.cast_nonneg _
        nlinarith [h1, h2]
      have hk : (Work.Elliptic.DzdIter (i - b) (fun z => Work.Spaces.hKer z) z) ^ 2
          ≤ 3000 ^ 2 := by
        have h1 := hker_dzdIter_le hα hib hzI
        have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        rwa [sq_abs] at h2
      have hXb : X b = ((i.choose b : ℕ) : ℝ)
          * (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
              * Work.Elliptic.DzdIter (i - b) (fun z => Work.Spaces.hKer z) z) := rfl
      have hkey : (((i.choose b : ℕ) : ℝ)) ^ 2
            * (Work.Elliptic.DzdIter (i - b) (fun z => Work.Spaces.hKer z) z) ^ 2
          ≤ 256 * 3000 ^ 2 := by
        have hnn1 : (0 : ℝ) ≤ (((i.choose b : ℕ) : ℝ)) ^ 2 := sq_nonneg _
        have hnn2 : (0 : ℝ) ≤
          (Work.Elliptic.DzdIter (i - b) (fun z => Work.Spaces.hKer z) z) ^ 2 := sq_nonneg _
        nlinarith [hc, hk, hnn1, hnn2]
      rw [hXb]
      have hgoal : (((i.choose b : ℕ) : ℝ)
            * (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
              * Work.Elliptic.DzdIter (i - b) (fun z => Work.Spaces.hKer z) z)
            * Work.Spaces.w z) ^ 2
          = ((((i.choose b : ℕ) : ℝ)) ^ 2
              * (Work.Elliptic.DzdIter (i - b) (fun z => Work.Spaces.hKer z) z) ^ 2)
            * ((Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
                * Work.Spaces.w z) ^ 2) := by ring
      rw [hgoal]
      exact mul_le_mul_of_nonneg_right hkey (sq_nonneg _)
    have hsum_le := Finset.sum_le_sum hterm
    have h1 : (∑ b ∈ Finset.range (i + 1), X b * Work.Spaces.w z) ^ 2
        ≤ 5 * ∑ b ∈ Finset.range (i + 1), (X b * Work.Spaces.w z) ^ 2 :=
      hcs.trans (mul_le_mul_of_nonneg_right hcard
        (Finset.sum_nonneg (fun b _ => sq_nonneg _)))
    have h2 : 5 * ∑ b ∈ Finset.range (i + 1), (X b * Work.Spaces.w z) ^ 2
        ≤ 5 * ((256 * 3000 ^ 2) * ∑ b ∈ Finset.range (i + 1),
            (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
              * Work.Spaces.w z) ^ 2) := by
      have h := mul_le_mul_of_nonneg_left hsum_le (by norm_num : (0 : ℝ) ≤ 5)
      rwa [← Finset.mul_sum] at h
    exact h1.trans (h2.trans (le_of_eq (by ring)))

  -- ## the pointwise bound for the whole sum
  have hpl : ∀ z ∈ Set.Ioi (0 : ℝ),
      ∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i
            (fun z => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z) z
          * Work.Spaces.w z) ^ 2
      ≤ 5 * (5 * (256 * 3000 ^ 2)) * ∑ b ∈ Finset.range 5,
            (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
              * Work.Spaces.w z) ^ 2 := by
    intro z hz
    have hstep : ∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i
            (fun z => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z) z
          * Work.Spaces.w z) ^ 2
        ≤ ∑ i ∈ Finset.range 5, (5 * (256 * 3000 ^ 2)) * ∑ b ∈ Finset.range (i + 1),
            (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
              * Work.Spaces.w z) ^ 2 :=
      Finset.sum_le_sum (fun i hi =>
        hpt i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) z hz)
    have hinner : ∀ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
          (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
            * Work.Spaces.w z) ^ 2
        ≤ ∑ b ∈ Finset.range 5,
          (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
            * Work.Spaces.w z) ^ 2 := by
      intro i hi
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro x hx
        have hi5 : i < 5 := Finset.mem_range.mp hi
        exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)
      · intro x _ _; exact sq_nonneg _
    calc ∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i
            (fun z => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z) z
          * Work.Spaces.w z) ^ 2
        ≤ ∑ i ∈ Finset.range 5, (5 * (256 * 3000 ^ 2)) * ∑ b ∈ Finset.range (i + 1),
            (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
              * Work.Spaces.w z) ^ 2 := hstep
      _ = (5 * (256 * 3000 ^ 2)) * ∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
            (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
              * Work.Spaces.w z) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (5 * (256 * 3000 ^ 2)) * ∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range 5,
            (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
              * Work.Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hinner) (by norm_num)
      _ = (5 * (256 * 3000 ^ 2)) * (5 * ∑ b ∈ Finset.range 5,
            (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
              * Work.Spaces.w z) ^ 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ = 5 * (5 * (256 * 3000 ^ 2)) * ∑ b ∈ Finset.range 5,
            (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
              * Work.Spaces.w z) ^ 2 := by ring
  -- ## integrability of the dominating sum
  have hintQu : MeasureTheory.IntegrableOn (fun z => ∑ b ∈ Finset.range 5,
      (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
        * Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    refine MeasureTheory.integrable_finsetSum (Finset.range 5) (fun b hb => ?_)
    have hb4 : b ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    exact (hintb b hb4).1.congr (Filter.Eventually.of_forall (fun z => by ring))
  -- ## the `HkSq`-bound
  have hSumInt : ∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 5,
        (Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z) z
          * Work.Spaces.w z) ^ 2
      ≤ 25 * (5 * (256 * 3000 ^ 2)) * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.Spaces.HkSq α 4 g) := by
    refine (MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun z => Finset.sum_nonneg (fun i _ => sq_nonneg _)))
      (hintQu.const_mul (5 * (5 * (256 * 3000 ^ 2)))) ?_).trans ?_
    · filter_upwards [haz] with z hz
      exact hpl z hz
    · have hIntb : ∀ b ∈ Finset.range 5, MeasureTheory.Integrable (fun z =>
          (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
            * Work.Spaces.w z) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
        intro b hb
        have hb4 : b ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
        exact (hintb b hb4).1.congr (Filter.Eventually.of_forall (fun z => by ring))
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_finsetSum (Finset.range 5) hIntb]
      have hsum5 : ∑ b ∈ Finset.range 5, ∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
              * Work.Spaces.w z) ^ 2
          ≤ 5 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * Work.Spaces.HkSq α 4 g) := by
        calc ∑ b ∈ Finset.range 5, ∫ z in Work.Spaces.Iz,
              (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
                * Work.Spaces.w z) ^ 2
            ≤ ∑ _b ∈ Finset.range 5, ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
                * Work.Spaces.HkSq α 4 g) := by
              refine Finset.sum_le_sum (fun b hb => ?_)
              have hb4 : b ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
              simpa only [mul_pow] using (hintb b hb4).2
          _ = 5 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
                * Work.Spaces.HkSq α 4 g) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              push_cast
              ring
      have h := mul_le_mul_of_nonneg_left hsum5
        (by norm_num : (0 : ℝ) ≤ 5 * (5 * (256 * 3000 ^ 2)))
      have harith : (5 * (5 * (256 * 3000 ^ 2)))
            * (5 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * Work.Spaces.HkSq α 4 g))
          = 25 * (5 * (256 * 3000 ^ 2)) * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * Work.Spaces.HkSq α 4 g) := by ring
      rwa [harith] at h

  have hHkSq_le : Work.Spaces.HkSq α 4
        (fun z θ => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z)
      ≤ (25 * (5 * (256 * 3000 ^ 2))
            * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))))
          * Work.Spaces.HkSq α 4 g := by
    have hEq : Work.Spaces.HkSq α 4
          (fun z θ => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z)
        = (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 5,
            (Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z) z
              * Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      rw [Work.Elliptic.HkSq_rad]
      congr 1
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [hEq]
    refine (mul_le_mul_of_nonneg_right hSumInt ?_).trans (le_of_eq ?_)
    · exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => Real.rpow_nonneg
          (Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ) _)
    · ring_nf
  -- ## the `Xn`-bound
  have hXn : Work.FTS.Nonlin.Xn α (fun z θ => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z)
      ≤ 10 ^ 12 * Work.FTS.Nonlin.Xn α g := by
    have hKbnn : 0 ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
    have hCtnn : 0 ≤ (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => Real.rpow_nonneg
          (Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ) _)
    have hbig : 0 ≤ 25 * (5 * (256 * 3000 ^ 2))
        * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) :=
      mul_nonneg (by norm_num) (mul_nonneg hKbnn hCtnn)
    have hfin : Real.sqrt (25 * (5 * (256 * 3000 ^ 2))
        * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))))
        ≤ 10 ^ 12 := by
      have h1 : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) ≤ 18 :=
        Ktheta_sq_integral_le
      have h2 : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ≤ 10 ^ 4 :=
        sin_rpow_integral_le
      have h3 : 25 * (5 * (256 * 3000 ^ 2))
          * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
          ≤ 10 ^ 24 := by nlinarith [h1, h2, hKbnn, hCtnn]
      calc Real.sqrt (25 * (5 * (256 * 3000 ^ 2))
            * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))))
          ≤ Real.sqrt ((10 : ℝ) ^ 24) := Real.sqrt_le_sqrt h3
        _ = 10 ^ 12 := by
            rw [show ((10 : ℝ) ^ 24) = ((10 : ℝ) ^ 12) ^ 2 from by norm_num,
              Real.sqrt_sq (by norm_num)]
    calc Work.FTS.Nonlin.Xn α (fun z θ => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z)
        = Real.sqrt (Work.Spaces.HkSq α 4
            (fun z θ => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z)) := rfl
      _ ≤ Real.sqrt ((25 * (5 * (256 * 3000 ^ 2))
            * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))))
            * Work.Spaces.HkSq α 4 g) := Real.sqrt_le_sqrt hHkSq_le
      _ = Real.sqrt (25 * (5 * (256 * 3000 ^ 2))
            * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))))
          * Real.sqrt (Work.Spaces.HkSq α 4 g) := Real.sqrt_mul hbig _
      _ = Real.sqrt (25 * (5 * (256 * 3000 ^ 2))
            * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))))
          * Work.FTS.Nonlin.Xn α g := rfl
      _ ≤ 10 ^ 12 * Work.FTS.Nonlin.Xn α g :=
          mul_le_mul_of_nonneg_right hfin (Work.Spaces.HkNorm_nonneg α 4 g)
  -- ## `HkMem`
  constructor
  · have hUsm : ContDiffOn ℝ 4
        (fun z => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z) (Set.Ioi (0:ℝ)) :=
      hRu.mul (hker_contDiffOn 4)
    have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4
        (fun z θ => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      refine ContinuousOn.congr (f := fun p : ℝ × ℝ => (∑ i ∈ Finset.range 5,
            (Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z)
                p.1) ^ 2 * (Work.Spaces.w p.1) ^ 2)
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) ?_ ?_
      · have hsum : ContinuousOn (fun p : ℝ × ℝ => ∑ i ∈ Finset.range 5,
            (Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z)
                p.1) ^ 2 * (Work.Spaces.w p.1) ^ 2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
          refine continuousOn_finsetSum (Finset.range 5) (fun i hi => ?_)
          have hi4 : i ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.DzdIter i
              (fun z => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z) p.1)
              (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
            (continuousOn_dzdIter_of_contDiffOn hUsm i hi4).comp continuousOn_fst
              (fun p hp => hp.1)
          exact (h1.pow 2).mul (Work.FTS.Nonlinear.RadialProd.continuousOn_w_fst.pow 2)
        exact hsum.mul Work.FTS.Nonlinear.RadialProd.continuousOn_smE_snd
      · intro p hp
        exact Work.FTS.H2.HkIntegrand_rad' α 4
          (fun z => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z) p.1
          ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩
    refine Work.FTS.LocData.HkMem_of_majorant α 4 hcont
      (M := fun z θ => (5 * (5 * (256 * 3000 ^ 2)))
        * ((∑ b ∈ Finset.range 5,
              (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
                * Work.Spaces.w z) ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) ?_ ?_ ?_
    · intro z hz
      have hsm : MeasureTheory.Integrable (fun θ : ℝ =>
          (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
          (by rw [Work.Spaces.eta]; norm_num)
          (by rw [Work.Spaces.eta]; norm_num)).1
      exact (hsm.const_mul ((5 * (5 * (256 * 3000 ^ 2))) * ∑ b ∈ Finset.range 5,
          (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
            * Work.Spaces.w z) ^ 2)).congr
        (Filter.Eventually.of_forall (fun θ => by ring))
    · have hcongr : (fun z => ∫ θ in Work.Spaces.Iθ,
            (5 * (5 * (256 * 3000 ^ 2))) * ((∑ b ∈ Finset.range 5,
                (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
                  * Work.Spaces.w z) ^ 2)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
          = fun z => ((5 * (5 * (256 * 3000 ^ 2)))
              * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
            * ∑ b ∈ Finset.range 5,
                (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
                  * Work.Spaces.w z) ^ 2 := by
        funext z
        rw [show (fun θ : ℝ => (5 * (5 * (256 * 3000 ^ 2))) * ((∑ b ∈ Finset.range 5,
                (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
                  * Work.Spaces.w z) ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
            = fun θ : ℝ => ((5 * (5 * (256 * 3000 ^ 2))) * (∑ b ∈ Finset.range 5,
                (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
                  * Work.Spaces.w z) ^ 2)) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) from by
          funext θ; ring]
        rw [MeasureTheory.integral_const_mul]
        ring
      rw [hcongr]
      have hI : MeasureTheory.Integrable (fun z => ∑ b ∈ Finset.range 5,
          (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
            * Work.Spaces.w z) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iz) := hintQu
      exact hI.const_mul ((5 * (5 * (256 * 3000 ^ 2)))
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
    · intro z hz θ hθ
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hpos
      · subst h0
        rw [Work.FTS.LocData.HkIntegrand_zero_fst]
        have hw0 : Work.Spaces.w (0:ℝ) = 0 := by simp [Work.Spaces.w]
        simp [hw0, mul_zero]
      · rw [Work.FTS.H2.HkIntegrand_rad' α 4
          (fun z => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z) z hθ]
        have hnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          Real.rpow_nonneg (Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ) _
        have hkey := hpl z hpos
        have h2 : (∑ i ∈ Finset.range 5,
              (Work.Elliptic.DzdIter i
                  (fun z => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z) z) ^ 2
                * (Work.Spaces.w z) ^ 2)
            ≤ 5 * (5 * (256 * 3000 ^ 2)) * ∑ b ∈ Finset.range 5,
                (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z) ^ 2
                  * (Work.Spaces.w z) ^ 2 := by
          have e1 : ∑ i ∈ Finset.range 5,
                (Work.Elliptic.DzdIter i
                  (fun z => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z) z) ^ 2
                  * (Work.Spaces.w z) ^ 2
              = (∑ i ∈ Finset.range 5,
                  (Work.Elliptic.DzdIter i
                    (fun z => Work.Elliptic.Qang g 0 z * Work.Spaces.hKer z) z
                    * Work.Spaces.w z) ^ 2) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            ring
          have e2 : ∑ b ∈ Finset.range 5,
                (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z) ^ 2
                  * (Work.Spaces.w z) ^ 2
              = (∑ b ∈ Finset.range 5,
                  (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z
                    * Work.Spaces.w z) ^ 2) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            ring
          rw [e1, e2]
          exact hkey
        refine (mul_le_mul_of_nonneg_right h2 hnn).trans (le_of_eq ?_)
        have hS : (∑ b ∈ Finset.range 5,
              (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z) ^ 2
              * (Work.Spaces.w z) ^ 2)
            = ∑ b ∈ Finset.range 5, (Work.Spaces.w z) ^ 2
              * (Work.Elliptic.DzdIter b (fun z => Work.Elliptic.Qang g 0 z) z) ^ 2 :=
          Finset.sum_congr rfl (fun b _ => by ring)
        rw [hS]
        ring
  · exact hXn

theorem row21 {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4gs α g)
        ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨K₂, hK₂pos, hK₂⟩ := XnAngProfHKer
  refine ⟨10 ^ 12 * K₂ + 1, by positivity, ?_⟩
  intro α g Φs Φg hgal hstar hell hα hα1 hαα₂
  have hsm : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 g := hgal.reg.2.1
  have hR : ContDiffOn ℝ 4 (fun z => Work.Construction.FK g z) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.Nonlinear.Pieces.RNP.RNP24.fk_contDiffOn_four hα hα1 hsm hmem6
  obtain ⟨hmemR, hXnR⟩ := FKhKerProd hα hα1 hsm hmem6 hR
  have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hstep : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4gs α g)
      ≤ α ^ 2 * K₂ * (10 ^ 12 * Work.FTS.Nonlin.Xn α g) := by
    rw [N4gs_factor α g]
    refine (hK₂ α hα hα1 (fun z => Work.Construction.FK g z * Work.Spaces.hKer z)
      hmemR).trans ?_
    exact mul_le_mul_of_nonneg_left hXnR (by positivity)
  have hα32 : α ^ 2 ≤ α ^ (3 / 2 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num : (3 / 2 : ℝ) ≤ 2)
    simpa using h
  refine hstep.trans ?_
  calc α ^ 2 * K₂ * (10 ^ 12 * Work.FTS.Nonlin.Xn α g)
      = (10 ^ 12 * K₂) * (α ^ 2 * Work.FTS.Nonlin.Xn α g) := by ring
    _ ≤ (10 ^ 12 * K₂) * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hα32 hXn0) (by positivity)
    _ ≤ (10 ^ 12 * K₂ + 1) * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) :=
        mul_le_mul_of_nonneg_right (by linarith)
          (mul_nonneg (Real.rpow_nonneg hα.le _) hXn0)

end Work.FTS.Nonlinear.Pieces.RNP
