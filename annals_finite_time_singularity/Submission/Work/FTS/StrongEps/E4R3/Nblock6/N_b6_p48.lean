import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Stmts
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Route
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.Defs
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNDefs
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.shiftProdDth
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.ptBoundDz
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.shiftProdDz_of
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.N_b6_star.Tools
import Submission.Work.FTS.StrongEps.HkSq_const_mul
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.StrongPersist.H6Rows.MismatchSummand

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Nblock6.N_b6_p48` — the level-`6` bounds of the two pieces `NBlk 4` and `NBlk 8`

The two pieces of the level-six `N`-block whose second factor is a *slot* of `w` of order one
above the norm (`(Uop(Phig)/sin 2t)·D_tw` and `-2a·Vop(Phig)·D_zw`).  The mathematics is in
`Tools/shiftProdDth.lean` / `Tools/shiftProdDz_of.lean`; here the two *elliptic* atoms are
instantiated at the hypotheses of the statement:

* `MA`: the pointwise bound `|A| <= C(gam-1)^{-1/2}|A|_{H4}` (`TransportS.sup_dz_le_hk`);
* `KA`: the flat price `|d_t A8| <= Ce a^{-1/2}Xn w` of `EllPkgGo.Vth`;
* `HkSq a 6 A <= Ce^2·HkSq a 6 w` from `EllPkgK`.

The bookkeeping of the constants: with `Gm = (gam a - 1)^{-1} >= 0`, `E := HkSq a 6 w >= 0`,
`E7 := HkSq a 7 w >= 0`, both product bounds give (atoms `A4 = Uop/sin 2t`, `A8 = Vop`)

  `(1 + Gm·(HkSq 6 A4 + E))·(HkSq 6 A4 + E) <= KB·(1+E)^2`,
  `(1 + KA8^2)·(1 + Gm·(HkSq 6 A8 + E))·(HkSq 6 A8 + E) <= KB·(1+E)^2`,

with `KB := (1+KMA)·(1+Ce^2C0^2)·(1+Ce^2)·(1+Gm·(1+Ce^2))` and
`KMA := 1 + Gm·Csup^2·Ce^2·C0^2` — every factor is `>= 1`, so `KB` dominates each of the two
products of factors.  The final constant is `K := (4C4 + 4C8 + 1)·(1 + KMA + KB)`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Nblock6

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

private theorem absSq_eq (x : ℝ) : |x| ^ 2 = x ^ 2 := by
  rw [pow_two, pow_two, abs_mul_abs_self]

private theorem sq_le_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  nlinarith only [h, ha]

private theorem one_le_mul_aux {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  nlinarith only [ha, hb]

private theorem sum_le_one_add {a E Ce2 : ℝ} (h : a ≤ Ce2 * E) (hE : 0 ≤ E) (hCe : 0 ≤ Ce2) :
    a + E ≤ (1 + Ce2) * (1 + E) := by
  nlinarith only [h, hE, hCe]

private theorem one_add_mul_le {Gm S E Ce2 : ℝ} (hG : 0 ≤ Gm) (hS : S ≤ (1 + Ce2) * (1 + E))
    (hE : 0 ≤ E) (hC : 0 ≤ Ce2) : 1 + Gm * S ≤ (1 + Gm * (1 + Ce2)) * (1 + E) := by
  nlinarith only [hG, hS, hE, hC]

private theorem mul_sq_le {M K E : ℝ} (h : M ≤ K) (hE : 0 ≤ E) (hK : 0 ≤ K) :
    M * E ≤ K * (1 + E) := by
  nlinarith only [h, hE, hK]

private theorem bracket_le {Gm A E Ce2 KB : ℝ} (hG : 0 ≤ Gm)
    (hfac : 1 + Gm * A ≤ (1 + Gm * (1 + Ce2)) * (1 + E))
    (hsum : A ≤ (1 + Ce2) * (1 + E)) (hA : 0 ≤ A) (hE : 0 ≤ E) (hC : 0 ≤ Ce2)
    (hP : (1 + Ce2) * (1 + Gm * (1 + Ce2)) ≤ KB) :
    (1 + Gm * A) * A ≤ KB * (1 + E) ^ 2 := by
  have hb : (0 : ℝ) ≤ (1 + Gm * (1 + Ce2)) * (1 + E) :=
    mul_nonneg (by nlinarith only [hG, hC]) (by linarith only [hE])
  have h1 : (1 + Gm * A) * A
      ≤ ((1 + Gm * (1 + Ce2)) * (1 + E)) * ((1 + Ce2) * (1 + E)) :=
    mul_le_mul hfac hsum hA hb
  have h2 : ((1 + Gm * (1 + Ce2)) * (1 + E)) * ((1 + Ce2) * (1 + E))
      = ((1 + Ce2) * (1 + Gm * (1 + Ce2))) * (1 + E) ^ 2 := by ring
  rw [h2] at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_right hP (sq_nonneg _))

private theorem bracket_le_KA {Gm A E Ce2 Cq KA2 KB : ℝ} (hG : 0 ≤ Gm)
    (hKA : 1 + KA2 ≤ 1 + Ce2 * Cq) (hfac : 1 + Gm * A ≤ (1 + Gm * (1 + Ce2)) * (1 + E))
    (hsum : A ≤ (1 + Ce2) * (1 + E)) (hA : 0 ≤ A) (hE : 0 ≤ E) (hC : 0 ≤ Ce2)
    (hKA0 : 0 ≤ 1 + KA2) (hCq : 0 ≤ 1 + Ce2 * Cq)
    (hP : (1 + Ce2 * Cq) * ((1 + Ce2) * (1 + Gm * (1 + Ce2))) ≤ KB) :
    (1 + KA2) * (1 + Gm * A) * A ≤ KB * (1 + E) ^ 2 := by
  have hGA : (0 : ℝ) ≤ 1 + Gm * A := by
    have := mul_nonneg hG hA
    linarith only [this]
  have hb : (0 : ℝ) ≤ (1 + Gm * (1 + Ce2)) * (1 + E) :=
    mul_nonneg (by nlinarith only [hG, hC]) (by linarith only [hE])
  have hc : (0 : ℝ) ≤ (1 + Ce2 * Cq) * ((1 + Gm * (1 + Ce2)) * (1 + E)) :=
    mul_nonneg hCq hb
  have h1 : (1 + KA2) * (1 + Gm * A) * A
      ≤ ((1 + Ce2 * Cq) * ((1 + Gm * (1 + Ce2)) * (1 + E))) * ((1 + Ce2) * (1 + E)) :=
    mul_le_mul (mul_le_mul hKA hfac hGA hCq) hsum hA hc
  have h2 : ((1 + Ce2 * Cq) * ((1 + Gm * (1 + Ce2)) * (1 + E))) * ((1 + Ce2) * (1 + E))
      = ((1 + Ce2 * Cq) * ((1 + Ce2) * (1 + Gm * (1 + Ce2)))) * (1 + E) ^ 2 := by ring
  rw [h2] at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_right hP (sq_nonneg _))

private theorem absorb_le {C X A B K1 K2 : ℝ} (hC : 0 ≤ C) (h1 : A ≤ K1) (h2 : B ≤ K2)
    (h : X ≤ C * (A + B)) : X ≤ C * (K1 + K2) :=
  le_trans h (mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC)

/-- **The `D_z` shift-product bound**, instantiated at `ptBoundDz`. -/
theorem shiftProdDz (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A f : ℝ → ℝ → ℝ) (MA KA : ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f → Work.Spaces.HkMem α 7 f →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.pth A z θ| ≤ KA) →
      Work.Spaces.HkSq α 6 (fun z θ => A z θ * Work.Spaces.Dz f z θ)
        ≤ C * (MA ^ 2 * Work.Spaces.HkSq α 7 f
            + (1 + KA ^ 2) * (1 + (Work.Spaces.gam α - 1)⁻¹
                * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)) :=
  Work.FTS.StrongEps.E4R3.Nblock6.Tools.shiftProdDz_of α hα hα1
    (Work.FTS.StrongEps.E4R3.Nblock6.Tools.ptBoundDz α hα hα1)

/-- **The level-`6` bounds of the two pieces `NBlk 4` and `NBlk 8`.** -/
theorem N_b6_p48 : Work.FTS.StrongEps.E4R3.Nblock6.P48Stmt := by
  intro C₀ Ce Cs α hαmem
  have hα0 : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  obtain ⟨C4, hC4pos, h4⟩ := Work.FTS.StrongEps.E4R3.Nblock6.Tools.shiftProdDth α hα0 hα1
  obtain ⟨C8, hC8pos, h8⟩ := shiftProdDz α hα0 hα1
  obtain ⟨Csup, hCsuppos, hsup⟩ := Work.FTS.TransportS.sup_dz_le_hk
  have hγ : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith only [hα0]
  have hGnn : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ := inv_nonneg.mpr hγ.le
  -- ## the constants
  set KMA : ℝ := 1 + (Work.Spaces.gam α - 1)⁻¹ * Csup ^ 2 * Ce ^ 2 * C₀ ^ 2 with hKMAdef
  have hKMA1 : 1 ≤ KMA := by
    rw [hKMAdef]
    have hnn : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ * Csup ^ 2 * Ce ^ 2 * C₀ ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg hGnn (sq_nonneg Csup)) (sq_nonneg Ce)) (sq_nonneg C₀)
    linarith only [hnn]
  have hCe20 : (0 : ℝ) ≤ Ce ^ 2 := sq_nonneg Ce
  have hCq0 : (0 : ℝ) ≤ Ce ^ 2 * C₀ ^ 2 := mul_nonneg hCe20 (sq_nonneg C₀)
  have hCeQ : (0 : ℝ) ≤ 1 + Ce ^ 2 * C₀ ^ 2 := by linarith only [hCq0]
  have hCe1 : (0 : ℝ) ≤ 1 + Ce ^ 2 := by linarith only [hCe20]
  have hGc : (0 : ℝ) ≤ (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2) :=
    mul_nonneg hGnn hCe1
  set KB : ℝ := (1 + KMA) * (1 + Ce ^ 2 * C₀ ^ 2) * (1 + Ce ^ 2)
      * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2)) with hKBdef
  have hKB1 : 1 ≤ KB := by
    rw [hKBdef]
    have h1 : (1 : ℝ) ≤ 1 + KMA := by linarith only [hKMA1]
    have h2 : (1 : ℝ) ≤ 1 + Ce ^ 2 * C₀ ^ 2 := by linarith only [hCq0]
    have h3 : (1 : ℝ) ≤ 1 + Ce ^ 2 := by linarith only [hCe20]
    have h4 : (1 : ℝ) ≤ 1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2) := by
      linarith only [hGc]
    have h5 := one_le_mul_aux (one_le_mul_aux h1 h2) (one_le_mul_aux h3 h4)
    calc (1 : ℝ) ≤ ((1 + KMA) * (1 + Ce ^ 2 * C₀ ^ 2))
            * ((1 + Ce ^ 2) * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2))) := h5
      _ = (1 + KMA) * (1 + Ce ^ 2 * C₀ ^ 2) * (1 + Ce ^ 2)
            * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2)) := by ring
  set K : ℝ := (4 * C4 + 4 * C8 + 1) * (1 + KMA + KB) with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    exact mul_pos (by linarith only [hC4pos, hC8pos]) (by linarith only [hKMA1, hKB1])
  -- the data-independent inequalities of the statement
  have hP12 : (1 : ℝ) ≤ (1 + KMA) * (1 + Ce ^ 2 * C₀ ^ 2) := by
    have h1 : (1 : ℝ) ≤ 1 + KMA := by linarith only [hKMA1]
    have h2 : (1 : ℝ) ≤ 1 + Ce ^ 2 * C₀ ^ 2 := by linarith only [hCq0]
    nlinarith only [h1, h2]
  have hP34 : (1 + Ce ^ 2) * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2)) ≤ KB := by
    rw [hKBdef]
    have hx : (0 : ℝ) ≤ (1 + Ce ^ 2) * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2)) :=
      mul_nonneg hCe1 (by linarith only [hGc])
    calc (1 + Ce ^ 2) * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2))
        = 1 * ((1 + Ce ^ 2) * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2))) := by ring
      _ ≤ ((1 + KMA) * (1 + Ce ^ 2 * C₀ ^ 2))
            * ((1 + Ce ^ 2) * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2))) :=
          mul_le_mul_of_nonneg_right hP12 hx
      _ = (1 + KMA) * (1 + Ce ^ 2 * C₀ ^ 2) * (1 + Ce ^ 2)
            * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2)) := by ring
  have hP234 : (1 + Ce ^ 2 * C₀ ^ 2) * ((1 + Ce ^ 2)
      * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2))) ≤ KB := by
    rw [hKBdef]
    have hx : (0 : ℝ) ≤ (1 + Ce ^ 2) * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2)) :=
      mul_nonneg hCe1 (by linarith only [hGc])
    have hy : (0 : ℝ) ≤ (1 + Ce ^ 2 * C₀ ^ 2)
        * ((1 + Ce ^ 2) * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2))) :=
      mul_nonneg hCeQ hx
    calc (1 + Ce ^ 2 * C₀ ^ 2) * ((1 + Ce ^ 2)
          * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2)))
        = 1 * ((1 + Ce ^ 2 * C₀ ^ 2) * ((1 + Ce ^ 2)
            * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2)))) := by ring
      _ ≤ (1 + KMA) * ((1 + Ce ^ 2 * C₀ ^ 2) * ((1 + Ce ^ 2)
            * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2)))) :=
          mul_le_mul_of_nonneg_right (by linarith only [hKMA1]) hy
      _ = (1 + KMA) * (1 + Ce ^ 2 * C₀ ^ 2) * (1 + Ce ^ 2)
            * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2)) := by ring
  have hK4KMA : 4 * C4 * KMA ≤ K := by
    rw [hKdef]
    have h1 : 4 * C4 ≤ 4 * C4 + 4 * C8 + 1 := by linarith only [hC8pos]
    have h2 : KMA ≤ 1 + KMA + KB := by linarith only [hKB1]
    exact mul_le_mul h1 h2 (by linarith only [hKMA1]) (by linarith only [hC4pos, hC8pos])
  have hK4KB : 4 * C4 * KB ≤ K := by
    rw [hKdef]
    have h1 : 4 * C4 ≤ 4 * C4 + 4 * C8 + 1 := by linarith only [hC8pos]
    have h2 : KB ≤ 1 + KMA + KB := by linarith only [hKMA1]
    exact mul_le_mul h1 h2 (by linarith only [hKB1]) (by linarith only [hC4pos, hC8pos])
  have hK8KMA : 4 * C8 * KMA ≤ K := by
    rw [hKdef]
    have h1 : 4 * C8 ≤ 4 * C4 + 4 * C8 + 1 := by linarith only [hC4pos]
    have h2 : KMA ≤ 1 + KMA + KB := by linarith only [hKB1]
    exact mul_le_mul h1 h2 (by linarith only [hKMA1]) (by linarith only [hC4pos, hC8pos])
  have hK8KB : 4 * C8 * KB ≤ K := by
    rw [hKdef]
    have h1 : 4 * C8 ≤ 4 * C4 + 4 * C8 + 1 := by linarith only [hC4pos]
    have h2 : KB ≤ 1 + KMA + KB := by linarith only [hKMA1]
    exact mul_le_mul h1 h2 (by linarith only [hKB1]) (by linarith only [hC4pos, hC8pos])
  refine ⟨K, hKpos, ?_⟩
  intro Φs w Φg hw hXw hz' hell hK6 hstar
  -- ## the datum `w`
  have hXwnn : 0 ≤ Work.FTS.Nonlin.Xn α w := Real.sqrt_nonneg _
  have h6w : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 6 (by norm_num) hw.mem
  have hα2 : α ^ 2 ≤ 1 := by
    have h := pow_le_one₀ hα0.le hα1 (n := 2)
    nlinarith only [h, sq_nonneg α]
  have hXw' : Work.FTS.Nonlin.Xn α w ≤ |C₀| * α ^ 2 := by
    have h1 : Work.FTS.Nonlin.Xn α w ≤ |C₀ * α ^ 2| := le_trans hXw (le_abs_self _)
    rwa [abs_mul, abs_of_nonneg (sq_nonneg α)] at h1
  have hwsq : (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ C₀ ^ 2 := by
    have ha : (0 : ℝ) ≤ |C₀| * α ^ 2 := by positivity
    have hle : |C₀| * α ^ 2 ≤ |C₀| := by nlinarith only [hα2, abs_nonneg C₀]
    have h3 : (|C₀| * α ^ 2) ^ 2 ≤ C₀ ^ 2 := by
      have h := sq_le_sq_of_nonneg ha hle
      simpa only [absSq_eq C₀] using h
    exact le_trans (sq_le_sq_of_nonneg hXwnn hXw') h3
  -- ## the two elliptic atoms
  set A4 : ℝ → ℝ → ℝ := fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg)
      z θ / Work.Construction.s2 θ with hA4def
  set A8 : ℝ → ℝ → ℝ := Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg) with hA8def
  have hA4sm : Work.FTS.EllipticEst.SmoothOpen A4 := by
    rw [hA4def]; simpa only [Work.FTS.Nonlin.PhiTg] using hK6.U.1.1
  have hA4mem : Work.Spaces.HkMem α 6 A4 := by
    rw [hA4def]; simpa only [Work.FTS.Nonlin.PhiTg] using hK6.U.1.2
  have hA4mem4 : Work.Spaces.HkMem α 4 A4 :=
    Work.FTS.OpenPkg.HkMem_mono_open hA4sm 4 (by norm_num) hA4mem
  have hA8sm : Work.FTS.EllipticEst.SmoothOpen A8 := by
    rw [hA8def]; simpa only [Work.FTS.Nonlin.PhiTg] using hK6.V.1.1
  have hA8mem : Work.Spaces.HkMem α 6 A8 := by
    rw [hA8def]; simpa only [Work.FTS.Nonlin.PhiTg] using hK6.V.1.2
  have hA8mem4 : Work.Spaces.HkMem α 4 A8 :=
    Work.FTS.OpenPkg.HkMem_mono_open hA8sm 4 (by norm_num) hA8mem
  have hXn4 : Work.FTS.Nonlin.Xn α A4 ≤ Ce * Work.FTS.Nonlin.Xn α w := by
    rw [hA4def]; simpa only [Work.FTS.Nonlin.PhiTg] using hell.U.2
  have hXn8 : Work.FTS.Nonlin.Xn α A8 ≤ Ce * Work.FTS.Nonlin.Xn α w := by
    rw [hA8def]; simpa only [Work.FTS.Nonlin.PhiTg] using hell.V.2
  have hN4 : Work.Spaces.HkNorm α 6 A4 ≤ Ce * Work.Spaces.HkNorm α 6 w := by
    rw [hA4def]; simpa only [Work.FTS.Nonlin.PhiTg] using hK6.U.2
  have hN8 : Work.Spaces.HkNorm α 6 A8 ≤ Ce * Work.Spaces.HkNorm α 6 w := by
    rw [hA8def]; simpa only [Work.FTS.Nonlin.PhiTg] using hK6.V.2
  have hsq4 : Work.Spaces.HkSq α 6 A4 ≤ Ce ^ 2 * Work.Spaces.HkSq α 6 w :=
    hkSq_le_of_hkNorm_le 6 hN4
  have hsq8 : Work.Spaces.HkSq α 6 A8 ≤ Ce ^ 2 * Work.Spaces.HkSq α 6 w :=
    hkSq_le_of_hkNorm_le 6 hN8
  have hMA4 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |A4 z θ| ≤ Csup / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α A4 := by
    intro z θ hz0 hθ hθ'
    have h := hsup α A4 hα0 hα1 hA4sm hA4mem4 0 (by norm_num) z θ hz0 hθ hθ'
    simpa using h
  have hMA8 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |A8 z θ| ≤ Csup / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α A8 := by
    intro z θ hz0 hθ hθ'
    have h := hsup α A8 hα0 hα1 hA8sm hA8mem4 0 (by norm_num) z θ hz0 hθ hθ'
    simpa using h
  have hKA8 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.pth A8 z θ| ≤ Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w := by
    intro z θ hz0 hθ hθ'
    have hmem : Work.FTS.VocabO.CoefThMem 1 A8 := by
      rw [hA8def]
      simpa only [Work.FTS.Nonlin.PhiTg] using hell.Vth.1
    have hbd : Work.FTS.VocabO.CoefTh 1 A8
        ≤ Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w := by
      rw [hA8def]
      simpa only [Work.FTS.Nonlin.PhiTg] using hell.Vth.2
    exact le_trans
      (Work.FTS.StrongPersist.H6Rows.abs_pth_le_coefTh hmem z θ hz0 hθ hθ') hbd
  -- ## the constant prices
  have hMAgen : ∀ B : ℝ → ℝ → ℝ, (Work.FTS.Nonlin.Xn α B) ^ 2 ≤ Ce ^ 2 * C₀ ^ 2 →
      (Csup / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α B) ^ 2 ≤ KMA := by
    intro B hB
    have h2 : (Csup / Real.sqrt (Work.Spaces.gam α - 1)) ^ 2
        = Csup ^ 2 * (Work.Spaces.gam α - 1)⁻¹ := by
      rw [div_pow, Real.sq_sqrt hγ.le, div_eq_mul_inv]
    have h1 : (Csup / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α B) ^ 2
        = (Csup / Real.sqrt (Work.Spaces.gam α - 1)) ^ 2 * (Work.FTS.Nonlin.Xn α B) ^ 2 :=
      mul_pow _ _ 2
    rw [h1, h2]
    refine le_trans (mul_le_mul_of_nonneg_left hB (mul_nonneg (sq_nonneg Csup) hGnn)) ?_
    rw [hKMAdef]
    have h7 : Csup ^ 2 * (Work.Spaces.gam α - 1)⁻¹ * (Ce ^ 2 * C₀ ^ 2)
        = (Work.Spaces.gam α - 1)⁻¹ * Csup ^ 2 * Ce ^ 2 * C₀ ^ 2 := by ring
    rw [h7]
    have hnn : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ * Csup ^ 2 * Ce ^ 2 * C₀ ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg hGnn (sq_nonneg Csup)) (sq_nonneg Ce)) (sq_nonneg C₀)
    linarith only [hnn]
  have hatom4 : (Work.FTS.Nonlin.Xn α A4) ^ 2 ≤ Ce ^ 2 * C₀ ^ 2 := by
    have h1 : Work.FTS.Nonlin.Xn α A4 ≤ |Ce| * Work.FTS.Nonlin.Xn α w := by
      refine le_trans hXn4 (le_trans (le_abs_self _) ?_)
      rw [abs_mul, abs_of_nonneg hXwnn]
    have h2 : (Work.FTS.Nonlin.Xn α A4) ^ 2 ≤ (|Ce| * Work.FTS.Nonlin.Xn α w) ^ 2 :=
      sq_le_sq_of_nonneg (Real.sqrt_nonneg _) h1
    have h3 : (|Ce| * Work.FTS.Nonlin.Xn α w) ^ 2 ≤ Ce ^ 2 * C₀ ^ 2 := by
      rw [mul_pow, absSq_eq Ce]
      exact mul_le_mul_of_nonneg_left hwsq (sq_nonneg Ce)
    linarith only [h2, h3]
  have hatom8 : (Work.FTS.Nonlin.Xn α A8) ^ 2 ≤ Ce ^ 2 * C₀ ^ 2 := by
    have h1 : Work.FTS.Nonlin.Xn α A8 ≤ |Ce| * Work.FTS.Nonlin.Xn α w := by
      refine le_trans hXn8 (le_trans (le_abs_self _) ?_)
      rw [abs_mul, abs_of_nonneg hXwnn]
    have h2 : (Work.FTS.Nonlin.Xn α A8) ^ 2 ≤ (|Ce| * Work.FTS.Nonlin.Xn α w) ^ 2 :=
      sq_le_sq_of_nonneg (Real.sqrt_nonneg _) h1
    have h3 : (|Ce| * Work.FTS.Nonlin.Xn α w) ^ 2 ≤ Ce ^ 2 * C₀ ^ 2 := by
      rw [mul_pow, absSq_eq Ce]
      exact mul_le_mul_of_nonneg_left hwsq (sq_nonneg Ce)
    linarith only [h2, h3]
  have hKA8sq : (Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w) ^ 2 ≤ Ce ^ 2 * C₀ ^ 2 := by
    have hrw : α ^ (-(1 / 2 : ℝ)) * α ^ 2 = α ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast α 2, ← Real.rpow_add hα0]
      norm_num
    have hstep : α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w ≤ |C₀| * α ^ (3 / 2 : ℝ) := by
      calc α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w
          ≤ α ^ (-(1 / 2 : ℝ)) * (|C₀| * α ^ 2) :=
            mul_le_mul_of_nonneg_left hXw' (Real.rpow_nonneg hα0.le _)
        _ = |C₀| * (α ^ (-(1 / 2 : ℝ)) * α ^ 2) := by ring
        _ = |C₀| * α ^ (3 / 2 : ℝ) := by rw [hrw]
    have h1 : |Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w|
        ≤ |Ce| * (|C₀| * α ^ (3 / 2 : ℝ)) := by
      have hA : |Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w|
          = |Ce| * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hα0.le _),
          abs_of_nonneg hXwnn]
        ring
      rw [hA]
      exact mul_le_mul_of_nonneg_left hstep (abs_nonneg Ce)
    have h2 : (Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w) ^ 2
        ≤ (|Ce| * (|C₀| * α ^ (3 / 2 : ℝ))) ^ 2 := by
      have h := sq_le_sq_of_nonneg (abs_nonneg _) h1
      rwa [absSq_eq] at h
    have h3 : (|Ce| * (|C₀| * α ^ (3 / 2 : ℝ))) ^ 2 ≤ Ce ^ 2 * C₀ ^ 2 := by
      have hα32 : (α ^ (3 / 2 : ℝ)) ^ 2 ≤ 1 := by
        have h5 : α ^ (3 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hα0.le hα1 (by norm_num)
        nlinarith only [h5, Real.rpow_nonneg hα0.le (3 / 2 : ℝ)]
      rw [mul_pow, mul_pow, absSq_eq Ce, absSq_eq C₀]
      have h4 : C₀ ^ 2 * (α ^ (3 / 2 : ℝ)) ^ 2 ≤ C₀ ^ 2 := by
        nlinarith only [hα32, sq_nonneg C₀]
      nlinarith only [h4, sq_nonneg Ce]
    linarith only [h2, h3]
  have hMA4sq := hMAgen A4 hatom4
  have hMA8sq := hMAgen A8 hatom8
  -- ## the bracket bounds
  have hE6 : 0 ≤ Work.Spaces.HkSq α 6 w := Work.Spaces.HkSq_nonneg α 6 w
  have hE7 : 0 ≤ Work.Spaces.HkSq α 7 w := Work.Spaces.HkSq_nonneg α 7 w
  have hA7 : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 7 w := by linarith only [hE7]
  have hsum4 := sum_le_one_add hsq4 hE6 (sq_nonneg Ce)
  have hsum8 := sum_le_one_add hsq8 hE6 (sq_nonneg Ce)
  have hfac4 := one_add_mul_le hGnn hsum4 hE6 (sq_nonneg Ce)
  have hfac8 := one_add_mul_le hGnn hsum8 hE6 (sq_nonneg Ce)
  have hA40 : 0 ≤ Work.Spaces.HkSq α 6 A4 + Work.Spaces.HkSq α 6 w := by
    have h := Work.Spaces.HkSq_nonneg α 6 A4; linarith only [h, hE6]
  have hA80 : 0 ≤ Work.Spaces.HkSq α 6 A8 + Work.Spaces.HkSq α 6 w := by
    have h := Work.Spaces.HkSq_nonneg α 6 A8; linarith only [h, hE6]
  have hbr4 := bracket_le hGnn hfac4 hsum4 hA40 hE6 (sq_nonneg Ce) hP34
  have hKA8b : 1 + (Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w) ^ 2
      ≤ 1 + Ce ^ 2 * C₀ ^ 2 := by linarith only [hKA8sq]
  have hKA80 : (0 : ℝ)
      ≤ 1 + (Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w) ^ 2 := by
    have := sq_nonneg (Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w)
    linarith only [this]
  have hbr8 := bracket_le_KA hGnn hKA8b hfac8 hsum8 hA80 hE6 (sq_nonneg Ce) hKA80 hCeQ hP234
  -- ## the two product estimates
  have hbound4 : Work.Spaces.HkSq α 6 (fun z θ => A4 z θ * Work.Spaces.Dth w z θ)
      ≤ C4 * (KMA * (1 + Work.Spaces.HkSq α 7 w)
          + KB * (1 + Work.Spaces.HkSq α 6 w) ^ 2) :=
    absorb_le hC4pos.le (mul_sq_le hMA4sq hE7 (by linarith only [hKMA1])) hbr4
      (h4 A4 w _ hA4sm hw.reg hA4mem h6w hw.mem hMA4)
  have hbound8 : Work.Spaces.HkSq α 6 (fun z θ => A8 z θ * Work.Spaces.Dz w z θ)
      ≤ C8 * (KMA * (1 + Work.Spaces.HkSq α 7 w)
          + KB * (1 + Work.Spaces.HkSq α 6 w) ^ 2) :=
    absorb_le hC8pos.le (mul_sq_le hMA8sq hE7 (by linarith only [hKMA1])) hbr8
      (h8 A8 w _ _ hA8sm hw.reg hA8mem h6w hw.mem hMA8 hKA8)
  -- ## the two pieces
  constructor
  · have hself : Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 4
        = fun z θ => (-2 : ℝ) * (A4 z θ * Work.Spaces.Dth w z θ) := by
      funext z θ
      simp only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTg, hA4def]
    rw [hself, Work.FTS.StrongEps.HkSq_const_mul α 6 (-2)
      (fun z θ => A4 z θ * Work.Spaces.Dth w z θ)]
    calc (-2 : ℝ) ^ 2 * Work.Spaces.HkSq α 6 (fun z θ => A4 z θ * Work.Spaces.Dth w z θ)
        ≤ 4 * (C4 * (KMA * (1 + Work.Spaces.HkSq α 7 w)
            + KB * (1 + Work.Spaces.HkSq α 6 w) ^ 2)) := by
          rw [show (-2 : ℝ) ^ 2 = 4 by norm_num]
          exact mul_le_mul_of_nonneg_left hbound4 (by norm_num)
      _ = (4 * C4 * KMA) * (1 + Work.Spaces.HkSq α 7 w)
          + (4 * C4 * KB) * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by ring
      _ ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_right hK4KMA hA7)
            (mul_le_mul_of_nonneg_right hK4KB (sq_nonneg _))
  · have hself : Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 8
        = fun z θ => (-(2 * α)) * (A8 z θ * Work.Spaces.Dz w z θ) := by
      funext z θ
      simp only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTg, hA8def]
    rw [hself, Work.FTS.StrongEps.HkSq_const_mul α 6 (-(2 * α))
      (fun z θ => A8 z θ * Work.Spaces.Dz w z θ)]
    calc (-(2 * α)) ^ 2 * Work.Spaces.HkSq α 6 (fun z θ => A8 z θ * Work.Spaces.Dz w z θ)
        ≤ 4 * (C8 * (KMA * (1 + Work.Spaces.HkSq α 7 w)
            + KB * (1 + Work.Spaces.HkSq α 6 w) ^ 2)) :=
          mul_le_mul (by nlinarith only [hα0, hα1]) hbound8
            (Work.Spaces.HkSq_nonneg α 6 _) (by norm_num)
      _ = (4 * C8 * KMA) * (1 + Work.Spaces.HkSq α 7 w)
          + (4 * C8 * KB) * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by ring
      _ ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_right hK8KMA hA7)
            (mul_le_mul_of_nonneg_right hK8KB (sq_nonneg _))

end Work.FTS.StrongEps.E4R3.Nblock6
