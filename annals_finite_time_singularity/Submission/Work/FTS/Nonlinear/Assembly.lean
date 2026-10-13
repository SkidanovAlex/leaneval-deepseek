/-
# N4 — `pairing_bound`: the assembly of the paper's §8 estimate (design L-N4.11)

This module proves the main theorem of the chapter from the per-piece estimates of
`RowInputs` (the table of design §3.4) and the two interfaces `UnifIP` (N2) and `N4Extra`
(N2/N3, the `IP`-level transport facts):

  `|IP α (gRHS α μ (lamfun μ) F Φ g) g| ≤ C · Pbd α X`,
  `|μ| ≤ C (α + α⁻¹X + α^{-5/2}X²)`,  `|μ| ≤ 1/2`  when `X ≤ α^{7/4}`.

Every contribution of the design's table is one of the monomials `α²`, `α²X`, `√αX²`,
`α^{3/2}X²`, `α^{-1/2}X³`, `α^{-1}X³`, `α^{-3/2}X³`, `X³`, each of which is `≤ Pbd α X`
(`Defs.lean`, `RowInputs.lean`); the `N_*`-contribution uses the *lossless* `D_z`-self-pairing
`N4Extra.dz` (design §5 T5) and is `≤ 72·Ct·Pbd α X`, i.e. `≤ K₀·Pbd α X` with
`K₀ = 4096(Ct + Ccs + 4)`.  There are at most `28` contributions, so the total is
`≤ 28·K₀·(1+C)·Pbd α X`, and the final constant `C₀ = 4096·K₀/C + 4096·K₀` satisfies
`C₀·C ≥ 4096·K₀·(1+C)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.RowInputs
import Submission.Work.Construction.MufunS

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlin

open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  muDyn lamDyn dynLin dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- `α^{-3/2}X³ ≤ Pbd α X`. -/
theorem rpow_neg_three_half_mul_cube_le_Pbd {α X : ℝ} (hα : 0 < α) (hX : 0 ≤ X) :
    α ^ (-(3 / 2 : ℝ)) * X ^ 3 ≤ Pbd α X := by
  rw [Pbd]
  have h1 : (0 : ℝ) ≤ α ^ 2 * X := mul_nonneg (by positivity) hX
  have h2 : (0 : ℝ) ≤ Real.sqrt α * X ^ 2 := mul_nonneg (Real.sqrt_nonneg α) (by positivity)
  have h3 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 4 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
  linarith

/-- **The assembly.**  Under the interfaces `UnifIP` (N2) and `N4Extra` (N2/N3) and the
per-piece estimates of the design's table (`RowInputs`), the paper's §8 estimate holds. -/
theorem pairing_bound_of_rows (IP : ℝ → Fn → Fn → ℝ) {α₂ cc clo Cup Ccs Ct Ce Cs C : ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hE : N4Extra IP α₂ Ct)
    (hCe : 0 < Ce) (hCs : 0 < Cs) (hC : 0 < C) :
    ∃ C₀ α₄ : ℝ, 0 < C₀ ∧ 0 < α₄ ∧ ∀ α : ℝ, 0 < α → α ≤ α₄ →
      ∀ g Φs Φg : Fn, GalClass α g → StarPkg α Cs Φs → EllPkgG α Ce g Φg →
        Xn α g ≤ α ^ (7 / 4 : ℝ) → RowInputs IP α C g Φs Φg →
        let F := Work.Construction.Ftot α g
        let Φ : Fn := fun z θ => Φs z θ + Φg z θ
        let μ := Work.Construction.mufunS α (Work.Construction.N0 α F g)
          (Work.Construction.N α F Φ) g
        |μ| ≤ C₀ * C * (α + α ^ (-(1 : ℝ)) * Xn α g + α ^ (-(5 / 2 : ℝ)) * Xn α g ^ 2) ∧
        |μ| ≤ 1 / 2 ∧
        |IP α (Work.Construction.gRHS α μ (Work.Construction.lamfun μ) F Φ g) g|
          ≤ C₀ * C * Pbd α (Xn α g) := by
  have hCt : 0 < Ct := hE.pos.1
  have hCcs : 0 < Ccs := hIP.pos.2.2.2.2
  obtain ⟨α₄μ, hα₄μ_pos, hα₄μ⟩ := mu_le_half (4 * C) (by positivity)
  set K₀ : ℝ := 4096 * (Ct + Ccs + 4) with hK₀def
  have hK₀pos : 0 < K₀ := by rw [hK₀def]; positivity
  have hK₀Ct : Ct ≤ K₀ := by rw [hK₀def]; nlinarith [hCt.le, hCcs.le]
  have hK₀one : (1 : ℝ) ≤ K₀ := by rw [hK₀def]; nlinarith [hCt.le, hCcs.le]
  have hK₀K : (28 : ℝ) ≤ K₀ := by rw [hK₀def]; nlinarith [hCt.le, hCcs.le]
  set C₀ : ℝ := 4096 * K₀ * (C + 1) + 4096 * K₀ / C with hC₀def
  have hC₀pos : 0 < C₀ := by rw [hC₀def]; positivity
  have hC₀Ceq : C₀ * C = 4096 * K₀ * (C * (C + 1)) + 4096 * K₀ := by
    rw [hC₀def]; field_simp; try ring
  have hbig : 6 * K₀ * C ^ 2 + 58 * (K₀ * (C + 1)) ≤ C₀ * C := by
    rw [hC₀Ceq]; nlinarith [hK₀pos.le, hC.le]
  have hbigK : K₀ * (C + 1) ≤ C₀ * C := by
    nlinarith [hbig, hK₀pos.le, hC.le]
  refine ⟨C₀, min α₂ (min 1 α₄μ), hC₀pos,
    lt_min hIP.pos.1 (lt_min one_pos hα₄μ_pos), ?_⟩
  intro α hα hαle g Φs Φg hgal hstar hell hX74 hR
  have hαα₂ : α ≤ α₂ := le_trans hαle (min_le_left _ _)
  have hαle' : α ≤ min 1 α₄μ := le_trans hαle (min_le_right _ _)
  have hα1 : α ≤ 1 := le_trans hαle' (min_le_left _ _)
  have hαα₄μ : α ≤ α₄μ := le_trans hαle' (min_le_right _ _)
  have hαIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hg4 : RegQ α 4 g := hR.reg4
  set X := Xn α g with hXdef
  have hX0 : 0 ≤ X := Work.Spaces.HkNorm_nonneg α 4 g
  have hX74' : X ≤ α ^ (7 / 4 : ℝ) := hX74
  have hPbd0 : 0 ≤ Pbd α X := Pbd_nonneg hα.le hX0
  -- ## the piece bounds
  have hpiece_bd : ∀ (f : Fn) (B : ℝ), Xn α f ≤ C * B → B * X ≤ Pbd α X →
      |IP α f g| ≤ K₀ * (C + 1) * Pbd α X := by
    intro f B hf hB
    have h1 : |IP α f g| ≤ Ct * Xn α f * X := hE.cs α hαIoc f g hg4
    have h2 : Ct * Xn α f * X ≤ Ct * (C * B) * X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf hCt.le) hX0
    have h3 : Ct * (C * B) * X = Ct * C * (B * X) := by ring
    have h4 : Ct * C * (B * X) ≤ Ct * C * Pbd α X :=
      mul_le_mul_of_nonneg_left hB (by positivity)
    have h5 : Ct * C * Pbd α X ≤ K₀ * C * Pbd α X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK₀Ct hC.le) hPbd0
    have h6 : K₀ * C * Pbd α X ≤ K₀ * (C + 1) * Pbd α X := by
      have h := mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1) hPbd0
      nlinarith [h, hK₀pos.le, hPbd0]
    linarith [h1, h2, h3.le, h3.ge, h4, h5, h6]
  have hpiece_dir : ∀ (f : Fn) (m : ℝ), |IP α f g| ≤ C * m → m ≤ Pbd α X →
      |IP α f g| ≤ K₀ * (C + 1) * Pbd α X := by
    intro f m hf hm
    have h1 : C * m ≤ C * Pbd α X := mul_le_mul_of_nonneg_left hm hC.le
    have h2 : C * Pbd α X ≤ K₀ * C * Pbd α X := by
      have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK₀one hC.le) hPbd0
      nlinarith [h]
    have h3 : K₀ * C * Pbd α X ≤ K₀ * (C + 1) * Pbd α X := by
      have h := mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1) hPbd0
      nlinarith [h, hK₀pos.le, hPbd0]
    linarith [hf, h1, h2, h3]
  have hconv : K₀ * (C + 1) * Pbd α X ≤ C₀ * C * Pbd α X := by
    have h := mul_le_mul_of_nonneg_right hbigK hPbd0
    linarith [h]
  -- ## the `μ` bound
  have hmu4 := mu_bound_mul hα hα1 hX0 hC.le hR.rl0 hR.rl1 hR.rl2
  have hM0 : 0 ≤ α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2 := by
    have h1 : (0 : ℝ) ≤ α ^ (-(1 : ℝ)) * X :=
      mul_nonneg (Real.rpow_nonneg hα.le _) hX0
    have h2 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
    linarith [hα.le]
  have hmu4' : |Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
        (Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ)) g|
      ≤ 4 * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) := by
    rw [mul_assoc]; exact hmu4
  have hmuC : |Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
        (Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ)) g|
      ≤ C₀ * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) := by
    have h4C : 4 * C ≤ C₀ * C := by nlinarith [hbig, hK₀pos.le, hC.le]
    have h1 : 4 * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2)
        ≤ C₀ * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) :=
      mul_le_mul_of_nonneg_right h4C hM0
    linarith [hmu4', h1]
  have hmu_half : |Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
        (Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ)) g| ≤ 1 / 2 :=
    hα₄μ α hα hαα₄μ X hX0 hX74' _ hmu4'
  refine ⟨hmuC, hmu_half, ?_⟩
  -- ## the pairing
  set A := Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
      (Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ))
    with hAdef
  set N0v := Work.Construction.N0 α (Work.Construction.Ftot α g) g with hN0v
  set Nv := Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)
    with hNv
  set μ := Work.Construction.mufunS α N0v Nv g with hμdef
  have hμ4 : |μ| ≤ 4 * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) := by
    rw [hμdef]; exact hmu4'
  have hμ1 : μ ≠ -1 := by
    intro h
    have hh : |μ| ≤ 1 / 2 := hα₄μ α hα hαα₄μ X hX0 hX74' μ (by rw [hμdef]; exact hmu4')
    rw [h] at hh; norm_num at hh
  set Ns := Work.Construction.Nstar μ (Work.Construction.lamfun μ) g with hNs
  have hgr : Work.Construction.gRHS α μ (Work.Construction.lamfun μ)
        (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) g
      = (fun z θ => -A * Work.Construction.AK α z θ) + N0v + Nv + Ns := by
    funext z θ
    simp only [Work.Construction.gRHS, Pi.add_apply, hAdef, hN0v, hNv, hNs]
    try ring
  have hIPsplit : IP α (Work.Construction.gRHS α μ (Work.Construction.lamfun μ)
        (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) g) g
      = IP α (fun z θ => -A * Work.Construction.AK α z θ) g + IP α N0v g + IP α Nv g
        + IP α Ns g := by
    rw [hgr, IP_add4 hE hαIoc hg4]
  -- ## the `-μ̄AK` term
  have hAKterm : |IP α (fun z θ => -A * Work.Construction.AK α z θ) g|
      ≤ 6 * K₀ * C ^ 2 * Pbd α X := by
    have hsm : IP α (fun z θ => -A * Work.Construction.AK α z θ) g
        = -A * IP α (Work.Construction.AK α) g :=
      hE.smul α hαIoc (-A) (Work.Construction.AK α) g hg4
    have hAK : |IP α (Work.Construction.AK α) g| ≤ Ct * Xn α (Work.Construction.AK α) * X :=
      hE.cs α hαIoc _ g hg4
    have hAK' : |IP α (Work.Construction.AK α) g| ≤ K₀ * C * X := by
      have h1 : Ct * Xn α (Work.Construction.AK α) * X ≤ Ct * C * X :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR.rak hCt.le) hX0
      have h2 : Ct * C * X ≤ K₀ * C * X :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK₀Ct hC.le) hX0
      linarith [hAK, h1, h2]
    have hA : |A| ≤ 2 * (C * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2)) := by
      rw [hAdef]; exact mubar_bound_mul hC.le hR.rl0 hR.rl1
    have hm1 : α ^ 2 * X ≤ Pbd α X := alpha_sq_mul_le_Pbd hα hX0
    have hm2 : Real.sqrt α * X * X ≤ Pbd α X := by
      have he : Real.sqrt α * X * X = Real.sqrt α * X ^ 2 := by ring
      rw [he]; exact sqrt_mul_sq_le_Pbd hα hX0
    have hm3 : α ^ (-(3 / 2 : ℝ)) * X * X * X ≤ Pbd α X := by
      have he : α ^ (-(3 / 2 : ℝ)) * X * X * X = α ^ (-(3 / 2 : ℝ)) * X ^ 3 := by ring
      rw [he]; exact rpow_neg_three_half_mul_cube_le_Pbd hα hX0
    have hprod : |A| * |IP α (Work.Construction.AK α) g|
        ≤ 2 * (C * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2)) * (K₀ * C * X) :=
      mul_le_mul hA hAK' (abs_nonneg _) (by positivity)
    have hexp : 2 * (C * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2)) * (K₀ * C * X)
        = 2 * K₀ * C ^ 2 * (α ^ 2 * X + Real.sqrt α * X * X
            + α ^ (-(3 / 2 : ℝ)) * X * X * X) := by ring
    have hsum : α ^ 2 * X + Real.sqrt α * X * X + α ^ (-(3 / 2 : ℝ)) * X * X * X
        ≤ 3 * Pbd α X := by linarith [hm1, hm2, hm3]
    have hfin : 2 * K₀ * C ^ 2 * (α ^ 2 * X + Real.sqrt α * X * X
          + α ^ (-(3 / 2 : ℝ)) * X * X * X) ≤ 6 * K₀ * C ^ 2 * Pbd α X := by
      have h1 : 2 * K₀ * C ^ 2 * (α ^ 2 * X + Real.sqrt α * X * X
            + α ^ (-(3 / 2 : ℝ)) * X * X * X) ≤ 2 * K₀ * C ^ 2 * (3 * Pbd α X) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      have h2 : 2 * K₀ * C ^ 2 * (3 * Pbd α X) = 6 * K₀ * C ^ 2 * Pbd α X := by ring
      linarith [h1, h2.le, h2.ge]
    rw [hsm, abs_mul, abs_neg]
    exact hprod.trans (hexp.le.trans hfin)
  -- ## the `N_*` term
  have hNsterm : |IP α Ns g| ≤ 24 * (K₀ * (C + 1) * Pbd α X) := by
    have hcollapse : Ns = NstarLam μ g := by
      funext z θ
      rw [hNs]
      exact hR.hNs μ hμ1 z θ
    have hdecomp : NstarLam μ g = (fun z θ => μ * Work.Spaces.Dz g z θ)
        + (fun z θ => (-μ) * g z θ) := by
      funext z θ; simp only [NstarLam, Pi.add_apply]; ring
    have hIPs : IP α (NstarLam μ g) g
        = μ * IP α (Work.Spaces.Dz g) g + (-μ) * IP α g g := by
      rw [hdecomp, hE.add α hαIoc _ _ g hg4, hE.smul α hαIoc μ (Work.Spaces.Dz g) g hg4,
        hE.smul α hαIoc (-μ) g g hg4]
    have hdz : |IP α (Work.Spaces.Dz g) g| ≤ Ct * X ^ 2 := hE.dz α hαIoc g hg4
    have hgg : |IP α g g| ≤ Ct * X ^ 2 := by
      have h1 : |IP α g g| ≤ Ct * Xn α g * Xn α g := hE.cs α hαIoc g g hg4
      have h2 : Ct * Xn α g * Xn α g = Ct * X ^ 2 := by rw [hXdef]; ring
      linarith [h1, h2.le, h2.ge]
    have htri : |IP α (NstarLam μ g) g| ≤ |μ| * (|IP α (Work.Spaces.Dz g) g| + |IP α g g|) := by
      rw [hIPs]
      have he : μ * IP α (Work.Spaces.Dz g) g + (-μ) * IP α g g
          = μ * (IP α (Work.Spaces.Dz g) g - IP α g g) := by ring
      rw [he, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg μ)
      simpa [sub_eq_add_neg] using abs_add_le (IP α (Work.Spaces.Dz g) g)
        (-(IP α g g))
    have hmid : |μ| * (|IP α (Work.Spaces.Dz g) g| + |IP α g g|)
        ≤ 8 * K₀ * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) * X ^ 2 := by
      have h1 : |IP α (Work.Spaces.Dz g) g| + |IP α g g| ≤ 2 * Ct * X ^ 2 := by
        have := add_le_add hdz hgg
        linarith [this]
      have h2 : |μ| * (|IP α (Work.Spaces.Dz g) g| + |IP α g g|)
          ≤ (4 * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2))
            * (2 * Ct * X ^ 2) :=
        mul_le_mul hμ4 h1 (by positivity) (by positivity)
      have h3 : (4 * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2))
            * (2 * Ct * X ^ 2)
          ≤ 8 * K₀ * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) * X ^ 2 := by
        have h8 : (0 : ℝ) ≤ 4 * C
            * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) * X ^ 2 :=
          mul_nonneg (mul_nonneg (by positivity) hM0) (by positivity)
        nlinarith [hK₀Ct, h8, hC.le]
      linarith [h2, h3]
    have hm1 : α * X ^ 2 ≤ Pbd α X := by
      have hαle_sqrt : α ≤ Real.sqrt α := by
        have hle1 : Real.sqrt α ≤ 1 := Real.sqrt_le_one.mpr hα1
        have hsq : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
        nlinarith [Real.sqrt_nonneg α, hle1, hsq]
      exact le_trans (mul_le_mul_of_nonneg_right hαle_sqrt (by positivity))
        (sqrt_mul_sq_le_Pbd hα hX0)
    have hm2 : α ^ (-(1 : ℝ)) * X ^ 3 ≤ Pbd α X := rpow_neg_one_mul_cube_le_Pbd hα hα1 hX0
    have hm3 : α ^ (-(5 / 2 : ℝ)) * X ^ 4 ≤ Pbd α X := by
      rw [Pbd]
      have h1 : (0 : ℝ) ≤ α ^ 2 * X := mul_nonneg (by positivity) hX0
      have h2 : (0 : ℝ) ≤ Real.sqrt α * X ^ 2 := mul_nonneg (Real.sqrt_nonneg α) (by positivity)
      have h3 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 3 :=
        mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
      linarith
    have hfin : 8 * K₀ * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) * X ^ 2
        ≤ 24 * (K₀ * (C + 1) * Pbd α X) := by
      have hexp : 8 * K₀ * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) * X ^ 2
          = 8 * K₀ * C * (α * X ^ 2 + α ^ (-(1 : ℝ)) * X ^ 3
              + α ^ (-(5 / 2 : ℝ)) * X ^ 4) := by ring
      have hsum : α * X ^ 2 + α ^ (-(1 : ℝ)) * X ^ 3 + α ^ (-(5 / 2 : ℝ)) * X ^ 4
          ≤ 3 * Pbd α X := by linarith [hm1, hm2, hm3]
      have hsum' : 8 * K₀ * C * (α * X ^ 2 + α ^ (-(1 : ℝ)) * X ^ 3
            + α ^ (-(5 / 2 : ℝ)) * X ^ 4) ≤ 8 * K₀ * C * (3 * Pbd α X) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      have h3P : 8 * K₀ * C * (3 * Pbd α X) ≤ 24 * (K₀ * (C + 1) * Pbd α X) := by
        have h1 : 8 * K₀ * C * (3 * Pbd α X) = 24 * K₀ * C * Pbd α X := by ring
        have h2 : 24 * (K₀ * (C + 1) * Pbd α X) = 24 * K₀ * C * Pbd α X + 24 * K₀ * Pbd α X := by
          ring
        have h3 : (0 : ℝ) ≤ 24 * K₀ * Pbd α X := by positivity
        linarith [h1.le, h1.ge, h2.le, h2.ge, h3]
      linarith [hexp.le, hexp.ge, hsum', h3P]
    calc |IP α Ns g| = |IP α (NstarLam μ g) g| := by rw [hcollapse]
      _ ≤ |μ| * (|IP α (Work.Spaces.Dz g) g| + |IP α g g|) := htri
      _ ≤ 8 * K₀ * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) * X ^ 2 := hmid
      _ ≤ 24 * (K₀ * (C + 1) * Pbd α X) := hfin
  -- ## the `N₀` term (6 pieces)
  have hN0term : |IP α N0v g| ≤ 7 * (K₀ * (C + 1) * Pbd α X) := by
    have hcongr : IP α N0v g = IP α (N0fix α + N03g α g + N04aF α g + N04bF α g
        + N05aF α g + N05bF α g + N06F α g) g := by
      apply hE.congr α hαIoc N0v _ g hg4
      intro z θ hzθ
      rw [hN0v, hR.hN0 z θ hzθ]
      simp only [Pi.add_apply]
      ring
    have hsum : IP α N0v g = IP α (N0fix α) g + IP α (N03g α g) g + IP α (N04aF α g) g
        + IP α (N04bF α g) g + IP α (N05aF α g) g + IP α (N05bF α g) g
        + IP α (N06F α g) g := by
      rw [hcongr]
      exact IP_add7 (g := g) (f₁ := N0fix α) (f₂ := N03g α g) (f₃ := N04aF α g)
        (f₄ := N04bF α g) (f₅ := N05aF α g) (f₆ := N05bF α g) (f₇ := N06F α g)
        hE hαIoc hg4
    have h1 := hpiece_bd (N0fix α) (α ^ 2) hR.r1 (alpha_sq_mul_le_Pbd hα hX0)
    have h2 := hpiece_bd (N03g α g) (α ^ (-(1 : ℝ)) * X ^ 2) hR.r2 (by
      have he : α ^ (-(1 : ℝ)) * X ^ 2 * X = α ^ (-(1 : ℝ)) * X ^ 3 := by ring
      rw [he]; exact rpow_neg_one_mul_cube_le_Pbd hα hα1 hX0)
    have h3 := hpiece_bd (N04aF α g) (Real.sqrt α * X) hR.r3 (by
      have he : Real.sqrt α * X * X = Real.sqrt α * X ^ 2 := by ring
      rw [he]; exact sqrt_mul_sq_le_Pbd hα hX0)
    have h4 := hpiece_dir (N04bF α g) (α ^ (-(3 / 2 : ℝ)) * X ^ 3) hR.r4
      (rpow_neg_three_half_mul_cube_le_Pbd hα hX0)
    have h5 := hpiece_bd (N05aF α g) (Real.sqrt α * X) hR.r5 (by
      have he : Real.sqrt α * X * X = Real.sqrt α * X ^ 2 := by ring
      rw [he]; exact sqrt_mul_sq_le_Pbd hα hX0)
    have h6 := hpiece_dir (N05bF α g) (α ^ (-(1 / 2 : ℝ)) * X ^ 3) hR.r6
      (rpow_neg_half_mul_cube_le_Pbd hα hα1 hX0)
    have h7 := hpiece_dir (N06F α g) (Real.sqrt α * X ^ 2) hR.r7 (sqrt_mul_sq_le_Pbd hα hX0)
    have htri : |IP α (N0fix α) g + IP α (N03g α g) g + IP α (N04aF α g) g
        + IP α (N04bF α g) g + IP α (N05aF α g) g + IP α (N05bF α g) g
        + IP α (N06F α g) g|
        ≤ |IP α (N0fix α) g| + |IP α (N03g α g) g| + |IP α (N04aF α g) g|
        + |IP α (N04bF α g) g| + |IP α (N05aF α g) g| + |IP α (N05bF α g) g|
        + |IP α (N06F α g) g| := by
      have h8 := abs_add_le (IP α (N0fix α) g + IP α (N03g α g) g + IP α (N04aF α g) g
        + IP α (N04bF α g) g + IP α (N05aF α g) g + IP α (N05bF α g) g)
        (IP α (N06F α g) g)
      have h9 := Work.Construction.abs_sum_le_five (IP α (N0fix α) g) (IP α (N03g α g) g)
        (IP α (N04aF α g) g) (IP α (N04bF α g) g) (IP α (N05aF α g) g)
      have h10 := abs_add_le (IP α (N0fix α) g + IP α (N03g α g) g + IP α (N04aF α g) g
        + IP α (N04bF α g) g + IP α (N05aF α g) g) (IP α (N05bF α g) g)
      linarith [h8, h9, h10]
    have hfin : 7 * (K₀ * (C + 1) * Pbd α X) ≤ 7 * (K₀ * (C + 1) * Pbd α X) := le_refl _
    rw [hsum]
    linarith [htri, h1, h2, h3, h4, h5, h6, h7, hfin,
      abs_nonneg (IP α (N0fix α) g), abs_nonneg (IP α (N03g α g) g),
      abs_nonneg (IP α (N04aF α g) g), abs_nonneg (IP α (N04bF α g) g),
      abs_nonneg (IP α (N05aF α g) g), abs_nonneg (IP α (N05bF α g) g),
      abs_nonneg (IP α (N06F α g) g)]
  -- ## the `N` term (20 pieces)
  have hNterm : |IP α Nv g| ≤ 20 * (K₀ * (C + 1) * Pbd α X) := by
    set G1 : Fn := N1gg α g Φg + N1gs α g Φg + N1sg α Φs g + N1ss α Φs with hG1def
    set G2 : Fn := N2gg α g Φg + N2gs α g Φg + N2sg α Φs g + N2ss α Φs with hG2def
    set G3 : Fn := N3gg α g Φg + N3gs α g Φg + N3sg α Φs g + N3ss α Φs with hG3def
    set G4 : Fn := N4gg α g + N4gs α g + N4sg α g + N4ss α with hG4def
    set G5 : Fn := N5gg g + N5gs α g + N5sg α g + N5ss α with hG5def
    have hcongr : IP α Nv g = IP α (G1 + G2 + G3 + G4 + G5) g := by
      apply hE.congr α hαIoc Nv _ g hg4
      intro z θ hzθ
      rw [hNv, hR.hN z θ hzθ, hG1def, hG2def, hG3def, hG4def, hG5def]
      simp only [Pi.add_apply]
      try ring
    have h1 := hpiece_bd (N1gg α g Φg) (α ^ (-(1 / 2 : ℝ)) * X ^ 2) hR.r8 (by
      have he : α ^ (-(1 / 2 : ℝ)) * X ^ 2 * X = α ^ (-(1 / 2 : ℝ)) * X ^ 3 := by ring
      rw [he]; exact rpow_neg_half_mul_cube_le_Pbd hα hα1 hX0)
    have h2 := hpiece_bd (N1gs α g Φg) (Real.sqrt α * X) hR.r9 (by
      have he : Real.sqrt α * X * X = Real.sqrt α * X ^ 2 := by ring
      rw [he]; exact sqrt_mul_sq_le_Pbd hα hX0)
    have h3 := hpiece_bd (N1sg α Φs g) (Real.sqrt α * X) hR.r10 (by
      have he : Real.sqrt α * X * X = Real.sqrt α * X ^ 2 := by ring
      rw [he]; exact sqrt_mul_sq_le_Pbd hα hX0)
    have h4 := hpiece_bd (N1ss α Φs) (α ^ 2) hR.r11 (alpha_sq_mul_le_Pbd hα hX0)
    have h5 := hpiece_dir (N2gg α g Φg) (α ^ (-(1 / 2 : ℝ)) * X ^ 3) hR.r12
      (rpow_neg_half_mul_cube_le_Pbd hα hα1 hX0)
    have h6 := hpiece_bd (N2gs α g Φg) (α ^ (3 / 2 : ℝ) * X) hR.r13 (by
      have he : α ^ (3 / 2 : ℝ) * X * X = α ^ (3 / 2 : ℝ) * X ^ 2 := by ring
      rw [he]; exact rpow_three_half_mul_sq_le_Pbd hα hα1 hX0)
    have h7 := hpiece_dir (N2sg α Φs g) (Real.sqrt α * X ^ 2) hR.r14 (sqrt_mul_sq_le_Pbd hα hX0)
    have h8 := hpiece_bd (N2ss α Φs) (α ^ 2) hR.r15 (alpha_sq_mul_le_Pbd hα hX0)
    have h9 := hpiece_dir (N3gg α g Φg) (Real.sqrt α * X ^ 3) hR.r16
      (sqrt_mul_cube_le_Pbd hα hα1 hX0)
    have h10 := hpiece_bd (N3gs α g Φg) (α ^ (3 / 2 : ℝ) * X) hR.r17 (by
      have he : α ^ (3 / 2 : ℝ) * X * X = α ^ (3 / 2 : ℝ) * X ^ 2 := by ring
      rw [he]; exact rpow_three_half_mul_sq_le_Pbd hα hα1 hX0)
    have h11 := hpiece_dir (N3sg α Φs g) (α ^ (3 / 2 : ℝ) * X ^ 2) hR.r18
      (rpow_three_half_mul_sq_le_Pbd hα hα1 hX0)
    have h12 := hpiece_bd (N3ss α Φs) (α ^ 3) hR.r19 (cube_alpha_mul_le_Pbd hα hα1 hX0)
    have h13 := hpiece_dir (N4gg α g) (α ^ (-(1 / 2 : ℝ)) * X ^ 3) hR.r20
      (rpow_neg_half_mul_cube_le_Pbd hα hα1 hX0)
    have h14 := hpiece_bd (N4gs α g) (α ^ (3 / 2 : ℝ) * X) hR.r21 (by
      have he : α ^ (3 / 2 : ℝ) * X * X = α ^ (3 / 2 : ℝ) * X ^ 2 := by ring
      rw [he]; exact rpow_three_half_mul_sq_le_Pbd hα hα1 hX0)
    have h15 := hpiece_dir (N4sg α g) (Real.sqrt α * X ^ 2) hR.r22 (sqrt_mul_sq_le_Pbd hα hX0)
    have h16 := hpiece_bd (N4ss α) (α ^ 3) hR.r23 (cube_alpha_mul_le_Pbd hα hα1 hX0)
    have h17 := hpiece_bd (N5gg g) (X ^ 2) hR.r24 (cube_le_Pbd hα hα1 hX0)
    have h18 : |IP α (N5gs α g) g| + |IP α (N5sg α g) g| ≤ K₀ * (C + 1) * Pbd α X := by
      have hgs : |IP α (N5gs α g) g| ≤ Ct * Xn α (N5gs α g) * X := hE.cs α hαIoc _ g hg4
      have hsg : |IP α (N5sg α g) g| ≤ Ct * Xn α (N5sg α g) * X := hE.cs α hαIoc _ g hg4
      have hsum : Xn α (N5gs α g) + Xn α (N5sg α g) ≤ C * (Real.sqrt α * X) := hR.r25
      have hb : Ct * Xn α (N5gs α g) * X + Ct * Xn α (N5sg α g) * X
          ≤ Ct * (C * (Real.sqrt α * X)) * X := by
        have he : Ct * Xn α (N5gs α g) * X + Ct * Xn α (N5sg α g) * X
            = Ct * (Xn α (N5gs α g) + Xn α (N5sg α g)) * X := by ring
        rw [he]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hCt.le) hX0
      have hs : Real.sqrt α * X * X = Real.sqrt α * X ^ 2 := by ring
      have hPB : Real.sqrt α * X ^ 2 ≤ Pbd α X := sqrt_mul_sq_le_Pbd hα hX0
      have heq : Ct * (C * (Real.sqrt α * X)) * X = Ct * C * (Real.sqrt α * X * X) := by ring
      have hfin : Ct * C * (Real.sqrt α * X * X) ≤ K₀ * (C + 1) * Pbd α X := by
        rw [hs]
        have h1 : Ct * C * Pbd α X ≤ K₀ * C * Pbd α X :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK₀Ct hC.le) hPbd0
        have h2 : K₀ * C * Pbd α X ≤ K₀ * (C + 1) * Pbd α X := by
          have h := mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1) hPbd0
          nlinarith [h, hK₀pos.le, hPbd0]
        exact le_trans (mul_le_mul_of_nonneg_left hPB (by positivity)) (le_trans h1 h2)
      linarith [hgs, hsg, hb, le_of_eq heq, hfin]
    have h19 := hpiece_bd (N5ss α) (α ^ 2) hR.r26 (alpha_sq_mul_le_Pbd hα hX0)
    have hG1 : |IP α G1 g| ≤ 4 * (K₀ * (C + 1) * Pbd α X) := by
      have hsum : IP α G1 g = IP α (N1gg α g Φg) g + IP α (N1gs α g Φg) g
          + IP α (N1sg α Φs g) g + IP α (N1ss α Φs) g := by
        rw [hG1def]; exact IP_add4 hE hαIoc hg4
      rw [hsum]
      linarith [Work.Construction.abs_sum_le_four (IP α (N1gg α g Φg) g)
        (IP α (N1gs α g Φg) g) (IP α (N1sg α Φs g) g) (IP α (N1ss α Φs) g),
        h1, h2, h3, h4, hconv,
        abs_nonneg (IP α (N1gg α g Φg) g), abs_nonneg (IP α (N1gs α g Φg) g),
        abs_nonneg (IP α (N1sg α Φs g) g), abs_nonneg (IP α (N1ss α Φs) g)]
    have hG2 : |IP α G2 g| ≤ 4 * (K₀ * (C + 1) * Pbd α X) := by
      have hsum : IP α G2 g = IP α (N2gg α g Φg) g + IP α (N2gs α g Φg) g
          + IP α (N2sg α Φs g) g + IP α (N2ss α Φs) g := by
        rw [hG2def]; exact IP_add4 hE hαIoc hg4
      rw [hsum]
      linarith [Work.Construction.abs_sum_le_four (IP α (N2gg α g Φg) g)
        (IP α (N2gs α g Φg) g) (IP α (N2sg α Φs g) g) (IP α (N2ss α Φs) g),
        h5, h6, h7, h8, hconv,
        abs_nonneg (IP α (N2gg α g Φg) g), abs_nonneg (IP α (N2gs α g Φg) g),
        abs_nonneg (IP α (N2sg α Φs g) g), abs_nonneg (IP α (N2ss α Φs) g)]
    have hG3 : |IP α G3 g| ≤ 4 * (K₀ * (C + 1) * Pbd α X) := by
      have hsum : IP α G3 g = IP α (N3gg α g Φg) g + IP α (N3gs α g Φg) g
          + IP α (N3sg α Φs g) g + IP α (N3ss α Φs) g := by
        rw [hG3def]; exact IP_add4 hE hαIoc hg4
      rw [hsum]
      linarith [Work.Construction.abs_sum_le_four (IP α (N3gg α g Φg) g)
        (IP α (N3gs α g Φg) g) (IP α (N3sg α Φs g) g) (IP α (N3ss α Φs) g),
        h9, h10, h11, h12, hconv,
        abs_nonneg (IP α (N3gg α g Φg) g), abs_nonneg (IP α (N3gs α g Φg) g),
        abs_nonneg (IP α (N3sg α Φs g) g), abs_nonneg (IP α (N3ss α Φs) g)]
    have hG4 : |IP α G4 g| ≤ 4 * (K₀ * (C + 1) * Pbd α X) := by
      have hsum : IP α G4 g = IP α (N4gg α g) g + IP α (N4gs α g) g
          + IP α (N4sg α g) g + IP α (N4ss α) g := by
        rw [hG4def]; exact IP_add4 hE hαIoc hg4
      rw [hsum]
      linarith [Work.Construction.abs_sum_le_four (IP α (N4gg α g) g) (IP α (N4gs α g) g)
        (IP α (N4sg α g) g) (IP α (N4ss α) g), h13, h14, h15, h16, hconv,
        abs_nonneg (IP α (N4gg α g) g), abs_nonneg (IP α (N4gs α g) g),
        abs_nonneg (IP α (N4sg α g) g), abs_nonneg (IP α (N4ss α) g)]
    have hG5 : |IP α G5 g| ≤ 4 * (K₀ * (C + 1) * Pbd α X) := by
      have hsum : IP α G5 g = IP α (N5gg g) g + IP α (N5gs α g) g
          + IP α (N5sg α g) g + IP α (N5ss α) g := by
        rw [hG5def]; exact IP_add4 hE hαIoc hg4
      rw [hsum]
      linarith [Work.Construction.abs_sum_le_four (IP α (N5gg g) g) (IP α (N5gs α g) g)
        (IP α (N5sg α g) g) (IP α (N5ss α) g), h17, h18, h19, hconv,
        abs_nonneg (IP α (N5gg g) g), abs_nonneg (IP α (N5gs α g) g),
        abs_nonneg (IP α (N5sg α g) g), abs_nonneg (IP α (N5ss α) g)]
    have hsplitN : IP α Nv g = IP α G1 g + IP α G2 g + IP α G3 g + IP α G4 g + IP α G5 g := by
      rw [hcongr]
      exact IP_add5 (g := g) (f₁ := G1) (f₂ := G2) (f₃ := G3) (f₄ := G4) (f₅ := G5)
        hE hαIoc hg4
    have htri : |IP α G1 g + IP α G2 g + IP α G3 g + IP α G4 g + IP α G5 g|
        ≤ |IP α G1 g| + |IP α G2 g| + |IP α G3 g| + |IP α G4 g| + |IP α G5 g| := by
      have h8 := abs_add_le (IP α G1 g + IP α G2 g + IP α G3 g + IP α G4 g) (IP α G5 g)
      have h9 := Work.Construction.abs_sum_le_four (IP α G1 g) (IP α G2 g) (IP α G3 g)
        (IP α G4 g)
      linarith [h8, h9]
    have h20 : |IP α G1 g| + |IP α G2 g| + |IP α G3 g| + |IP α G4 g| + |IP α G5 g|
        ≤ 20 * (K₀ * (C + 1) * Pbd α X) := by
      linarith [hG1, hG2, hG3, hG4, hG5,
        abs_nonneg (IP α G1 g), abs_nonneg (IP α G2 g), abs_nonneg (IP α G3 g),
        abs_nonneg (IP α G4 g), abs_nonneg (IP α G5 g)]
    rw [hsplitN]
    linarith [htri, h20]
  -- ## the final combination
  rw [hIPsplit]
  have htri : |IP α (fun z θ => -A * Work.Construction.AK α z θ) g + IP α N0v g
      + IP α Nv g + IP α Ns g|
      ≤ |IP α (fun z θ => -A * Work.Construction.AK α z θ) g| + |IP α N0v g|
        + |IP α Nv g| + |IP α Ns g| := Work.Construction.abs_sum_le_four _ _ _ _
  have hfinal : |IP α (fun z θ => -A * Work.Construction.AK α z θ) g| + |IP α N0v g|
      + |IP α Nv g| + |IP α Ns g| ≤ C₀ * C * Pbd α X := by
    have h56 : 6 * K₀ * C ^ 2 * Pbd α X + 58 * (K₀ * (C + 1) * Pbd α X)
        ≤ C₀ * C * Pbd α X := by
      have h := mul_le_mul_of_nonneg_right hbig hPbd0
      have he : (6 * K₀ * C ^ 2 + 58 * (K₀ * (C + 1))) * Pbd α X
          = 6 * K₀ * C ^ 2 * Pbd α X + 58 * (K₀ * (C + 1) * Pbd α X) := by ring
      rw [he] at h
      exact h
    linarith [hAKterm, hN0term, hNterm, hNsterm, h56,
      abs_nonneg (IP α (fun z θ => -A * Work.Construction.AK α z θ) g),
      abs_nonneg (IP α N0v g), abs_nonneg (IP α Nv g), abs_nonneg (IP α Ns g)]
  linarith [htri, hfinal]

end Work.FTS.Nonlin
