/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `(i,m)`-block decomposition of the `ℋ^k`-integrand, for the radial Agmon estimate

This module is the bookkeeping layer of `Work.FTS.EllipticEst.HkSq_Dz_le`.  The `ℋ^k`-integrand
of the paper is written as a single sum over the pairs `(i,m)` of *angular order* `i` and
*radial order* `m` with `i + m ≤ k`, each block being the product

  `hblk (i,m) = (D_z^m D_θ^i φ)² · w(z)² · angw i θ`

of a purely radial square and the angular weight `angw 0 = sin(2θ)^{-η}` (the pure radial
summands), `angw i = sin(2θ)^{-γ}` for `i ≥ 1` (the mixed summands).

The point of this grouping is that the radial Agmon inequality applies block by block with the
radial order shifted by one: the `(i,m)`-block of `D_z φ` is the `(i,m)`-block of `φ` with `m`
replaced by `m+1`, and the second radial derivative of that block is the `(i,m)`-block of `z²∂_z²φ`
(using that `z²∂_z²` commutes with both `D_z` and `D_θ`).

The vocabulary of the module:

* `angw`, `hblk`, `hblkR` — the angular weight and the blocks (with and without it);
* `angw_nonneg`, `hblk_nonneg`, `hblkR_nonneg` — nonnegativity (on the angular interval);
* `HkIntegrand_eq_hblk` — the decomposition itself, on the angular interval.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.GbarSetup
import Submission.Work.FTS.EllipticEst.zAMGM_Hk_le
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.HkSq_eq_lintegral
import Submission.Work.Stability.Cutoff
import Submission.Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_mixed_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

set_option autoImplicit false

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

/-! ## The angular weight and its nonnegativity on `[0,π/2]` -/

/-- On the angular interval the argument of the weights lies in `[0,π]`. -/
theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [hθ.2, Real.pi_pos]⟩

/-- The angular weight of the `i`-th family: `sEta θ = sin(2θ)^{-η}` for `i = 0` (the pure
radial summands), `sGam α θ = sin(2θ)^{-γ}` for `i ≥ 1` (the mixed summands). -/
def angw (α : ℝ) (i : ℕ) (θ : ℝ) : ℝ := if i = 0 then sEta θ else sGam α θ

theorem angw_nonneg (α : ℝ) (i : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ angw α i θ := by
  unfold angw
  split
  · exact Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _
  · exact Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

/-! ## The blocks -/

/-- The `(i,m)`-block of the `ℋ^k`-pattern of `φ`: the radial square `(D_z^m D_θ^i φ)² w²`
multiplied by the angular weight of the family, and `0` outside the index set `i + m ≤ k`. -/
def hblk (α : ℝ) (k : ℕ) (φ : ℝ → ℝ → ℝ) (p : ℕ × ℕ) (z θ : ℝ) : ℝ :=
  if p.1 + p.2 ≤ k then
    (Work.Spaces.DzIter p.2 (Work.Spaces.DthIter p.1 φ) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      * angw α p.1 θ
  else 0

theorem hblk_nonneg (α : ℝ) (k : ℕ) (φ : ℝ → ℝ → ℝ) (p : ℕ × ℕ) (z θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ hblk α k φ p z θ := by
  unfold hblk
  split
  · exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (angw_nonneg α p.1 hθ)
  · exact le_rfl

/-- The radial part of the `(i,m)`-block: `(D_z^m D_θ^i φ)² w(z)²`, as a function of `z`. -/
def hblkR (φ : ℝ → ℝ → ℝ) (p : ℕ × ℕ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.DzIter p.2 (Work.Spaces.DthIter p.1 φ) z θ) ^ 2 * (Work.Spaces.w z) ^ 2

theorem hblkR_nonneg (φ : ℝ → ℝ → ℝ) (p : ℕ × ℕ) (z θ : ℝ) : 0 ≤ hblkR φ p z θ :=
  mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Outside the index set the block vanishes. -/
theorem hblk_eq_zero (α : ℝ) (k : ℕ) (φ : ℝ → ℝ → ℝ) (p : ℕ × ℕ) (z θ : ℝ)
    (h : ¬ p.1 + p.2 ≤ k) : hblk α k φ p z θ = 0 := by
  unfold hblk
  exact if_neg h

/-- Inside the index set the block is the radial part times the angular weight. -/
theorem hblk_eq (α : ℝ) (k : ℕ) (φ : ℝ → ℝ → ℝ) (p : ℕ × ℕ) (z θ : ℝ)
    (h : p.1 + p.2 ≤ k) :
    hblk α k φ p z θ = hblkR φ p z θ * angw α p.1 θ := by
  unfold hblk hblkR
  exact if_pos h

/-! ## The decomposition of the `ℋ^k`-integrand -/

/-- **The block decomposition of the `ℋ^k`-integrand.**  On the angular interval the integrand is
the sum over the pairs `(i,m)` with `i, m ≤ k` and `i + m ≤ k` of the blocks `hblk (i,m)`: the
pure radial summands `(D_z^mφ)² w² sin(2θ)^{-η}` are the `i = 0` row and the mixed summands
`(D_z^m D_θ^i φ)² w² sin(2θ)^{-γ}` (with `1 ≤ i`) are the rows `i ≥ 1`, re-indexed. -/
theorem HkIntegrand_eq_hblk (α : ℝ) (k : ℕ) (φ : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k φ z θ
      = ∑ i ∈ Finset.range (k + 1), ∑ m ∈ Finset.range (k + 1), hblk α k φ (i, m) z θ := by
  rw [Work.Spaces.HkIntegrand]
  -- the `i = 0` row is the pure radial family
  have hA : (∑ m ∈ Finset.range (k + 1), hblk α k φ (0, m) z θ)
      = ∑ m ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter m φ z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [Finset.mem_range] at hm
    rw [hblk_eq α k φ (0, m) z θ (by omega)]
    have hD : Work.Spaces.DthIter 0 φ = φ := Work.Spaces.DthIter_zero φ
    have hA0 : angw α 0 θ = sEta θ := by simp [angw]
    rw [hA0]
    simp only [hblkR]
    rw [hD, rad_term_eq hθ z (Work.Spaces.DzIter m φ z θ)]
    ring
  -- the rows `i ≥ 1` are the mixed family
  have hB : (∑ i ∈ Finset.range k, ∑ m ∈ Finset.range (k + 1), hblk α k φ (i + 1, m) z θ)
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i φ z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    rw [Finset.sum_range_succ']
    have hzero : (∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ (0 : ℕ) ∧ 0 + j ≤ k then
          (Work.Spaces.mixed j 0 φ z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [if_neg (by omega)]
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    refine Finset.sum_congr rfl (fun j hj => ?_)
    by_cases hc : i + 1 + j ≤ k
    · rw [if_pos (show 1 ≤ i + 1 ∧ i + 1 + j ≤ k from ⟨by omega, hc⟩)]
      rw [hblk_eq α k φ (i + 1, j) z θ (by omega)]
      have hg : angw α (i + 1) θ = sGam α θ := by
        simp only [angw]; rw [if_neg (by omega)]
      rw [hg]
      simp only [hblkR]
      rw [mix_term_eq hθ α z (Work.Spaces.mixed j (i + 1) φ z θ)]
      simp only [Work.Spaces.mixed]
      ring
    · rw [if_neg (show ¬ (1 ≤ i + 1 ∧ i + 1 + j ≤ k) from by omega)]
      exact hblk_eq_zero α k φ (i + 1, j) z θ (by omega)
  -- assemble
  have hS : (∑ i ∈ Finset.range (k + 1), ∑ m ∈ Finset.range (k + 1), hblk α k φ (i, m) z θ)
      = (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i φ z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i φ z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    rw [Finset.sum_range_succ', hB, hA, add_comm]
  exact hS.symm

/-! ## The blocks are continuous on the open quadrant -/

theorem continuousOn_w_Q0 : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.w q.1) Q0 := by
  have hfun : (fun q : ℝ × ℝ => Work.Spaces.w q.1)
      = fun q : ℝ × ℝ => (1 + q.1) ^ 2 / q.1 ^ 2 := by funext q; rfl
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun q hq => ?_)
  exact pow_ne_zero 2 (ne_of_gt (mem_Q0.mp hq).1)

theorem continuousOn_sinQ0 : ContinuousOn (fun q : ℝ × ℝ => Real.sin (2 * q.2)) Q0 :=
  (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn

theorem sin_two_pos_Q0 {q : ℝ × ℝ} (hq : q ∈ Q0) : 0 < Real.sin (2 * q.2) := by
  obtain ⟨-, h0, h1⟩ := mem_Q0.mp hq
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

theorem continuousOn_angw_Q0 (α : ℝ) (i : ℕ) :
    ContinuousOn (fun q : ℝ × ℝ => angw α i q.2) Q0 := by
  have hs : ContinuousOn (fun q : ℝ × ℝ => (Real.sin (2 * q.2)) ^ (-(Work.Spaces.eta))) Q0 :=
    continuousOn_sinQ0.rpow_const (fun q hq => Or.inl (ne_of_gt (sin_two_pos_Q0 hq)))
  have hg : ContinuousOn (fun q : ℝ × ℝ => (Real.sin (2 * q.2)) ^ (-(Work.Spaces.gam α))) Q0 :=
    continuousOn_sinQ0.rpow_const (fun q hq => Or.inl (ne_of_gt (sin_two_pos_Q0 hq)))
  unfold angw
  split
  · simpa only [sEta] using hs
  · simpa only [sGam] using hg

/-- The `(i,m)`-block of a function smooth on the open quadrant is continuous there. -/
theorem continuousOn_hblk_Q0 (α : ℝ) (k : ℕ) (φ : ℝ → ℝ → ℝ)
    (hφ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) (i m : ℕ) :
    ContinuousOn (fun q : ℝ × ℝ => hblk α k φ (i, m) q.1 q.2) Q0 := by
  have hsm : SmoothOpen φ := smoothOpen_of_forall hφ
  by_cases h : i + m ≤ k
  · have hfun : (fun q : ℝ × ℝ => hblk α k φ (i, m) q.1 q.2)
        = fun q : ℝ × ℝ => (Work.Spaces.DzIter m (Work.Spaces.DthIter i φ) q.1 q.2) ^ 2
            * (Work.Spaces.w q.1) ^ 2 * angw α i q.2 := by
      funext q
      exact hblk_eq α k φ (i, m) q.1 q.2 h
    rw [hfun]
    have hD : ContinuousOn (fun q : ℝ × ℝ =>
        Work.Spaces.DzIter m (Work.Spaces.DthIter i φ) q.1 q.2) Q0 :=
      (hsm.mixed m i).continuousOn
    exact ((hD.pow 2).mul (continuousOn_w_Q0.pow 2)).mul (continuousOn_angw_Q0 α i)
  · have hfun : (fun q : ℝ × ℝ => hblk α k φ (i, m) q.1 q.2)
        = fun _ : ℝ × ℝ => (0 : ℝ) := by
      funext q
      exact hblk_eq_zero α k φ (i, m) q.1 q.2 h
    rw [hfun]
    exact continuousOn_const

/-- A.e. strong measurability of the blocks for the product measure. -/
theorem hblk_aesm (α : ℝ) (k : ℕ) (φ : ℝ → ℝ → ℝ)
    (hφ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) (i m : ℕ) :
    AEStronglyMeasurable (fun q : ℝ × ℝ => hblk α k φ (i, m) q.1 q.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    ((continuousOn_hblk_Q0 α k φ hφ i m).mono (fun q hq => mem_Q0.mpr hq))

theorem hblk_ofReal_aemeasurable (α : ℝ) (k : ℕ) (φ : ℝ → ℝ → ℝ)
    (hφ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) (i m : ℕ) :
    AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (hblk α k φ (i, m) q.1 q.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  ENNReal.measurable_ofReal.comp_aemeasurable (hblk_aesm α k φ hφ i m).aemeasurable

/-! ## The block functionals -/

/-- The `z`-`lintegral` of the radial part of the `(i,m)`-block of `φ`. -/
def blkZ (φ : ℝ → ℝ → ℝ) (p : ℕ × ℕ) (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (hblkR φ p z θ)

/-- The product `lintegral` of one block of the `ℋ^k`-integrand pattern of `φ`: the `θ`-integral
of `w_θ · ∫⁻_z`, and `0` outside the index set `i + m ≤ k`. -/
def blkP (α : ℝ) (k : ℕ) (φ : ℝ → ℝ → ℝ) (p : ℕ × ℕ) : ℝ≥0∞ :=
  if p.1 + p.2 ≤ k then
    ∫⁻ θ in Work.Spaces.Iθ, blkZ φ p θ * ENNReal.ofReal (angw α p.1 θ)
  else 0

/-- The product `lintegral` of the `ℋ^k`-integrand of `φ`. -/
def Lk (α : ℝ) (k : ℕ) (φ : ℝ → ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α k φ p.1 p.2)
    ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))

theorem blkZ_nonneg (φ : ℝ → ℝ → ℝ) (p : ℕ × ℕ) (θ : ℝ) : 0 ≤ blkZ φ p θ :=
  bot_le

/-- The second coordinate is a.e. in `Iθ`. -/
theorem ae_snd_mem_Iθ :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p.2 ∈ Work.Spaces.Iθ := by
  rw [MeasureTheory.Measure.prod_restrict]
  filter_upwards [MeasureTheory.ae_restrict_mem
    (measurableSet_Ici.prod measurableSet_Icc)] with p hp
  exact hp.2

/-- The pointwise identity of the block integrand with `ofReal (hblkR) * ofReal (angw)`. -/
theorem hblk_ofReal_eq (α : ℝ) (k : ℕ) (φ : ℝ → ℝ → ℝ) (i m : ℕ) {z θ : ℝ}
    (h : i + m ≤ k) :
    ENNReal.ofReal (hblk α k φ (i, m) z θ)
      = ENNReal.ofReal (hblkR φ (i, m) z θ) * ENNReal.ofReal (angw α i θ) := by
  rw [hblk_eq α k φ (i, m) z θ h, ENNReal.ofReal_mul (hblkR_nonneg φ (i, m) z θ)]

/-! ## The product `lintegral` of a single block -/

/-- The product `lintegral` of a single block is `blkP`: integrate the radial part in `z` and the
angular weight in `θ`. -/
theorem blk_integral (α : ℝ) (k : ℕ) (φ : ℝ → ℝ → ℝ)
    (hφ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) (i m : ℕ) :
    (∫⁻ p, ENNReal.ofReal (hblk α k φ (i, m) p.1 p.2)
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = blkP α k φ (i, m) := by
  by_cases h : i + m ≤ k
  · rw [blkP, if_pos h]
    have hfun : (fun p : ℝ × ℝ => ENNReal.ofReal (hblk α k φ (i, m) p.1 p.2))
        = fun p : ℝ × ℝ => ENNReal.ofReal (hblkR φ (i, m) p.1 p.2)
            * ENNReal.ofReal (angw α i p.2) := by
      funext p
      exact hblk_ofReal_eq α k φ i m h
    have hmeas : AEMeasurable
        (fun p : ℝ × ℝ => ENNReal.ofReal (hblkR φ (i, m) p.1 p.2)
          * ENNReal.ofReal (angw α i p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      rw [← hfun]
      exact hblk_ofReal_aemeasurable α k φ hφ i m
    rw [hfun, MeasureTheory.lintegral_prod _ hmeas]
    rw [MeasureTheory.lintegral_lintegral_swap (f := fun x y : ℝ =>
      ENNReal.ofReal (hblkR φ (i, m) x y) * ENNReal.ofReal (angw α i y)) hmeas]
    refine lintegral_congr (fun θ => ?_)
    rw [MeasureTheory.lintegral_mul_const' _ _ ENNReal.ofReal_lt_top.ne]
    rfl
  · rw [blkP, if_neg h]
    have hfun : (fun p : ℝ × ℝ => ENNReal.ofReal (hblk α k φ (i, m) p.1 p.2))
        = fun _ : ℝ × ℝ => 0 := by
      funext p
      rw [hblk_eq_zero α k φ (i, m) p.1 p.2 h]
      simp
    rw [hfun, lintegral_zero]

/-- **The block decomposition of the product `lintegral` of the `ℋ^k`-integrand.** -/
theorem Lk_eq_blocks (α : ℝ) (k : ℕ) (φ : ℝ → ℝ → ℝ)
    (hφ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    Lk α k φ = ∑ i ∈ Finset.range (k + 1), ∑ m ∈ Finset.range (k + 1), blkP α k φ (i, m) := by
  have hpt : (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k φ p.1 p.2))
      =ᵐ[((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))]
      (fun p : ℝ × ℝ => ∑ i ∈ Finset.range (k + 1), ∑ m ∈ Finset.range (k + 1),
          ENNReal.ofReal (hblk α k φ (i, m) p.1 p.2)) := by
    filter_upwards [ae_snd_mem_Iθ] with p hp
    rw [HkIntegrand_eq_hblk α k φ hp]
    rw [ENNReal.ofReal_sum_of_nonneg
      (fun i _ => Finset.sum_nonneg (fun m _ => hblk_nonneg α k φ (i, m) p.1 p.2 hp))]
    exact Finset.sum_congr rfl (fun i _ =>
      ENNReal.ofReal_sum_of_nonneg (fun m _ => hblk_nonneg α k φ (i, m) p.1 p.2 hp))
  have hsum_meas : ∀ i : ℕ, AEMeasurable (fun p : ℝ × ℝ =>
      ∑ m ∈ Finset.range (k + 1), ENNReal.ofReal (hblk α k φ (i, m) p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    intro i
    refine (Finset.aemeasurable_sum (Finset.range (k + 1))
      (fun m _ => hblk_ofReal_aemeasurable α k φ hφ i m)).congr ?_
    filter_upwards with p
    rw [Finset.sum_apply]
  have houter : (∫⁻ p, ∑ i ∈ Finset.range (k + 1),
        ∑ m ∈ Finset.range (k + 1), ENNReal.ofReal (hblk α k φ (i, m) p.1 p.2)
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∑ i ∈ Finset.range (k + 1), ∫⁻ p,
          ∑ m ∈ Finset.range (k + 1), ENNReal.ofReal (hblk α k φ (i, m) p.1 p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    MeasureTheory.lintegral_finsetSum' (Finset.range (k + 1)) (fun i _ => hsum_meas i)
  have hinner : ∀ i : ℕ, (∫⁻ p, ∑ m ∈ Finset.range (k + 1),
          ENNReal.ofReal (hblk α k φ (i, m) p.1 p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∑ m ∈ Finset.range (k + 1), blkP α k φ (i, m) := by
    intro i
    rw [MeasureTheory.lintegral_finsetSum' (Finset.range (k + 1)) (fun m _ =>
      hblk_ofReal_aemeasurable α k φ hφ i m)]
    exact Finset.sum_congr rfl (fun m _ => blk_integral α k φ hφ i m)
  rw [Lk, lintegral_congr_ae hpt, houter]
  exact Finset.sum_congr rfl (fun i _ => hinner i)

/-! ## Measurability of the angular weights and of the block functionals -/

/-- A function of `θ` continuous on `(0,π/2)` is a.e. strongly measurable for `Iθ`. -/
theorem aesm_slice_theta {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have h1 : AEStronglyMeasurable g (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hg.aestronglyMeasurable measurableSet_Ioo
  have hset : (Set.Ioo (0 : ℝ) (Real.pi / 2)) =ᵐ[MeasureTheory.volume] Work.Spaces.Iθ :=
    MeasureTheory.Ioo_ae_eq_Icc
  rw [← MeasureTheory.Measure.restrict_congr_set hset]
  exact h1

/-- A function of `z` continuous on `(0,∞)` is a.e. strongly measurable for `Iz`. -/
theorem aesm_slice_z {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioi (0 : ℝ))) :
    AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
  exact hg.aestronglyMeasurable measurableSet_Ioi

theorem continuousOn_angw_theta (α : ℝ) (i : ℕ) :
    ContinuousOn (fun θ : ℝ => angw α i θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h1 : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hpos θ hθ)))
  have h2 : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hpos θ hθ)))
  unfold angw
  split
  · simpa only [sEta] using h1
  · simpa only [sGam] using h2

theorem continuousOn_hblkR_Q0 (φ : ℝ → ℝ → ℝ)
    (hφ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) (i m : ℕ) :
    ContinuousOn (fun q : ℝ × ℝ => hblkR φ (i, m) q.1 q.2) Q0 := by
  have hsm : SmoothOpen φ := smoothOpen_of_forall hφ
  have hD : ContinuousOn (fun q : ℝ × ℝ =>
      Work.Spaces.DzIter m (Work.Spaces.DthIter i φ) q.1 q.2) Q0 :=
    (hsm.mixed m i).continuousOn
  exact (hD.pow 2).mul (continuousOn_w_Q0.pow 2)

/-- The block functional `blkZ` is a.e. strongly measurable in `θ`. -/
theorem blkZ_aemeasurable (φ : ℝ → ℝ → ℝ)
    (hφ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) (i m : ℕ) :
    AEMeasurable (blkZ φ (i, m)) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hprod : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (hblkR φ (i, m) q.1 q.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((Work.Spaces.aesm_of_continuousOn_Qd _
        ((continuousOn_hblkR_Q0 φ hφ i m).mono (fun q hq => mem_Q0.mpr hq))).aemeasurable)
  exact hprod.lintegral_prod_left'

/-- `ofReal ∘ angw` is a.e. strongly measurable in `θ`. -/
theorem angw_ofReal_aemeasurable (α : ℝ) (i : ℕ) :
    AEMeasurable (fun θ : ℝ => ENNReal.ofReal (angw α i θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  ENNReal.measurable_ofReal.comp_aemeasurable
    ((aesm_slice_theta (continuousOn_angw_theta α i)).aemeasurable)

/-! ## The two one-dimensional interfaces -/

/-- **Interface: the one-dimensional weighted Agmon estimate** (delivered by
`Work.FTS.EllipticEst.AgmonSlice.rDz_agmon_sq`). -/
def AgmonInterface (C : ℝ) : Prop :=
  ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (h : ℝ → ℝ),
    ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi 0) →
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (h z) ^ 2) Work.Spaces.Iz →
    MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2) Work.Spaces.Iz →
    α ^ 2 * (∫ z in Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDz h z) ^ 2)
      ≤ C * ((∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (h z) ^ 2)
        + α ^ 4 * (∫ z in Work.Spaces.Iz,
            (Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2))

/-- **Interface: finiteness of the middle weighted integral** (delivered by
`Work.FTS.EllipticEst.AgmonSlice.rDz_lintegral_ne_top`). -/
def FinInterface : Prop :=
  ∀ (h : ℝ → ℝ), ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi 0) →
    (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2)) ≠ ⊤ →
    (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2)) ≠ ⊤ →
    (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDz h z) ^ 2)) ≠ ⊤

/-! ## The bridges between `HkSq` and the product `lintegral` -/

/-- **The product `lintegral` of the `ℋ^k`-integrand is `ofReal (HkSq)`** for honest data. -/
theorem Lk_eq_ofReal_HkSq (α : ℝ) (k : ℕ) (φ : ℝ → ℝ → ℝ)
    (hφ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hm : Work.Spaces.HkMem α k φ) :
    Lk α k φ = ENNReal.ofReal (Work.Spaces.HkSq α k φ) := by
  have hnn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α k φ z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α k φ z θ
  have hmeas : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k φ p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((Work.Spaces.aesm_of_continuousOn_Qd _
        ((smoothOpen_of_forall hφ).continuousOn_HkIntegrand α k)).aemeasurable)
  have h1 : ∀ z ∈ Work.Spaces.Iz,
      ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k φ z θ)
        = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k φ z θ) :=
    fun z hz => MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hm.1 z hz)
      (Filter.Eventually.of_forall (fun θ => hnn z θ))
  have h2 : ENNReal.ofReal (∫ z in Work.Spaces.Iz,
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k φ z θ)
      = ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k φ z θ) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hm.2
      (Filter.Eventually.of_forall (fun z => integral_nonneg (fun θ => hnn z θ)))
  rw [Lk, Work.Spaces.HkSq, h2]
  have h3 : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k φ z θ))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k φ z θ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    exact h1 z hz
  rw [h3]
  exact MeasureTheory.lintegral_prod
    (f := fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k φ p.1 p.2)) hmeas

/-- **`HkSq` is dominated by the `toReal` of the product `lintegral`** (assuming the latter is
finite, which will be the case in the application). -/
theorem HkSq_le_toReal_Lk (α : ℝ) (k : ℕ) (φ : ℝ → ℝ → ℝ)
    (hφ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hne : Lk α k φ ≠ ⊤) :
    Work.Spaces.HkSq α k φ ≤ (Lk α k φ).toReal := by
  have hmeas : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k φ p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((Work.Spaces.aesm_of_continuousOn_Qd _
        ((smoothOpen_of_forall hφ).continuousOn_HkIntegrand α k)).aemeasurable)
  rw [HkSq_eq_lintegral α k φ hφ]
  refine ENNReal.toReal_mono hne ?_
  rw [Lk]
  refine (lintegral_mono_ae ?_).trans_eq (MeasureTheory.lintegral_prod
    (f := fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k φ p.1 p.2)) hmeas).symm
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
  by_cases hz0 : z = 0
  · subst hz0
    simp [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt]
  · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.HkIntegrand α k φ z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _
        ((smoothOpen_of_forall hφ).continuousOn_HkIntegrand α k) hzpos
    have hbr := MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun θ => Work.Spaces.HkIntegrand_nonneg α k φ z θ)) haesm
    rw [hbr]
    exact ENNReal.ofReal_toReal_le

/-! ## Auxiliary: continuity of the slices, and `lintegral`/integral bridges -/

theorem continuousOn_w_Ioi : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi (0 : ℝ)) := by
  have hfun : (fun z : ℝ => Work.Spaces.w z) = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := by
    funext z; rfl
  rw [hfun]
  exact ((continuousOn_const.add continuousOn_id).pow 2).div (continuousOn_id.pow 2)
    (fun z hz => pow_ne_zero 2 (ne_of_gt hz))

/-- The `z`-slice of an iterated plain `z`-derivative of a smooth function is continuous. -/
theorem SmoothOpen.continuousOn_slice_pzIter {ψ : ℝ → ℝ → ℝ} (hψ : SmoothOpen ψ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (j : ℕ) :
    ContinuousOn (fun z : ℝ => Work.Spaces.pzIter j ψ z θ) (Set.Ioi 0) :=
  ((hψ.pzIter j).continuousOn).comp (continuousOn_id.prodMk continuousOn_const)
    (fun z hz => mem_Q0.mpr ⟨hz, hθ⟩)

/-- The iterated `D_z` of two functions which agree on `(0,∞)` agree there. -/
theorem DzIter_congr_of_eqOn_Q0 {u v : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → u z θ = v z θ) :
    ∀ m : ℕ, ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.DzIter m u z θ = Work.Spaces.DzIter m v z θ := by
  intro m
  induction m with
  | zero => intro z θ hz hθ; exact h z θ hz hθ
  | succ m ih =>
      intro z θ hz hθ
      have hev : (fun z' : ℝ => Work.Spaces.DzIter m u z' θ)
          =ᶠ[nhds z] (fun z' : ℝ => Work.Spaces.DzIter m v z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' hθ
      show z * deriv (fun z' : ℝ => Work.Spaces.DzIter m u z' θ) z
        = z * deriv (fun z' : ℝ => Work.Spaces.DzIter m v z' θ) z
      rw [hev.deriv_eq]

/-- The `lintegral` of `ofReal` of a continuous nonnegative function on `(0,∞)`, in terms of the
Bochner integral (when finite). -/
theorem ofReal_integral_eq_lintegral_Iz {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioi 0))
    (hnn : ∀ z, 0 ≤ g z) (hne : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (g z)) ≠ ⊤) :
    ENNReal.ofReal (∫ z in Work.Spaces.Iz, g z) = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (g z) := by
  have haesm : AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    aesm_slice_z hg
  have hint : MeasureTheory.IntegrableOn g Work.Spaces.Iz :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable haesm
      (Filter.Eventually.of_forall hnn)).mp hne
  exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall hnn)

/-! ## The integration step: from the per-angle inequality to the blocks -/

theorem blkP_int_step {α C : ℝ} (hα : 0 < α) (hC : 0 < C) {i m : ℕ} {f F : ℝ → ℝ → ℝ}
    (hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      ENNReal.ofReal (α ^ 2) * blkZ (Work.Spaces.Dz f) (i, m) θ
        ≤ ENNReal.ofReal C * (blkZ f (i, m) θ + ENNReal.ofReal (α ^ 4) * blkZ F (i, m) θ))
    (hameas : AEMeasurable (fun θ : ℝ => blkZ f (i, m) θ * ENNReal.ofReal (angw α i θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    ENNReal.ofReal (α ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            blkZ (Work.Spaces.Dz f) (i, m) θ * ENNReal.ofReal (angw α i θ))
      ≤ ENNReal.ofReal C
        * ((∫⁻ θ in Work.Spaces.Iθ, blkZ f (i, m) θ * ENNReal.ofReal (angw α i θ))
          + ENNReal.ofReal (α ^ 4)
            * (∫⁻ θ in Work.Spaces.Iθ, blkZ F (i, m) θ * ENNReal.ofReal (angw α i θ))) := by
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    have h1 : (Set.Ioo (0 : ℝ) (Real.pi / 2)) =ᵐ[MeasureTheory.volume] Work.Spaces.Iθ :=
      MeasureTheory.Ioo_ae_eq_Icc
    rw [← MeasureTheory.Measure.restrict_congr_set h1]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  calc ENNReal.ofReal (α ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            blkZ (Work.Spaces.Dz f) (i, m) θ * ENNReal.ofReal (angw α i θ))
      = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (α ^ 2)
          * (blkZ (Work.Spaces.Dz f) (i, m) θ * ENNReal.ofReal (angw α i θ)) :=
        (lintegral_const_mul' (ENNReal.ofReal (α ^ 2)) _ ENNReal.ofReal_lt_top.ne).symm
    _ ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal C
          * ((blkZ f (i, m) θ * ENNReal.ofReal (angw α i θ))
            + ENNReal.ofReal (α ^ 4)
              * (blkZ F (i, m) θ * ENNReal.ofReal (angw α i θ))) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with θ hθ
        have hmem : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
        have hw : 0 ≤ angw α i θ := angw_nonneg α i hmem
        calc ENNReal.ofReal (α ^ 2) * (blkZ (Work.Spaces.Dz f) (i, m) θ
                * ENNReal.ofReal (angw α i θ))
            = (ENNReal.ofReal (α ^ 2) * blkZ (Work.Spaces.Dz f) (i, m) θ)
                * ENNReal.ofReal (angw α i θ) := by ring
          _ ≤ (ENNReal.ofReal C * (blkZ f (i, m) θ
                  + ENNReal.ofReal (α ^ 4) * blkZ F (i, m) θ))
                * ENNReal.ofReal (angw α i θ) := mul_le_mul_left (hpt θ hθ) _
          _ = ENNReal.ofReal C * ((blkZ f (i, m) θ * ENNReal.ofReal (angw α i θ))
                + ENNReal.ofReal (α ^ 4)
                  * (blkZ F (i, m) θ * ENNReal.ofReal (angw α i θ))) := by ring
    _ = ENNReal.ofReal C
        * ((∫⁻ θ in Work.Spaces.Iθ, blkZ f (i, m) θ * ENNReal.ofReal (angw α i θ))
          + ENNReal.ofReal (α ^ 4)
            * (∫⁻ θ in Work.Spaces.Iθ, blkZ F (i, m) θ * ENNReal.ofReal (angw α i θ))) := by
        rw [lintegral_const_mul' (ENNReal.ofReal C) _ ENNReal.ofReal_lt_top.ne]
        congr 1
        rw [lintegral_add_left' hameas]
        rw [lintegral_const_mul' (ENNReal.ofReal (α ^ 4)) _ ENNReal.ofReal_lt_top.ne]

/-! ## The per-block Agmon inequality -/

/-- **The per-block Agmon inequality.**  For every block index `(i,m)` the weighted `ℋ^k`-block
of `D_z f` is dominated by the corresponding blocks of `f` and of `z²∂_z²f` (with the same
angular weight), with the `α²/α⁴/1` scaling. -/
theorem blkP_agmon (C : ℝ) (hC : 0 < C) (hag : AgmonInterface C) (hfin : FinInterface)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (f : ℝ → ℝ → ℝ)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) (i m : ℕ) :
    ENNReal.ofReal (α ^ 2) * blkP α k (Work.Spaces.Dz f) (i, m)
      ≤ ENNReal.ofReal C * (blkP α k f (i, m)
        + ENNReal.ofReal (α ^ 4)
          * blkP α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) (i, m)) := by
  set F : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ with hF
  have hsm : SmoothOpen f := smoothOpen_of_forall hf
  by_cases hk : i + m ≤ k
  · rw [blkP, if_pos hk, blkP, if_pos hk, blkP, if_pos hk]
    refine blkP_int_step hα hC ?_ ?_
    · -- the per-angle inequality
      intro θ hθ
      have hmem : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      set h1 : ℝ → ℝ := fun z => Work.Spaces.DzIter m (Work.Spaces.DthIter i f) z θ with h1def
      have hslice : ContDiffOn ℝ Work.Stability.smoothOrder h1 (Set.Ioi 0) := by
        have h := (hsm.mixed m i).curry_z hθ
        simpa only [h1def, Work.Spaces.mixed] using h
      have hderiv1 : deriv h1
          = fun z : ℝ => Work.Spaces.pz (Work.Spaces.DzIter m (Work.Spaces.DthIter i f)) z θ := by
        funext z
        rw [h1def]
        rfl
      have hderiv2 : deriv (deriv h1)
          = fun z : ℝ => Work.Spaces.pzIter 2
              (Work.Spaces.DzIter m (Work.Spaces.DthIter i f)) z θ := by
        funext z
        rw [h1def]
        simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
      have hrDz : ∀ z : ℝ, Work.FTS.EllipticEst.rDz h1 z
          = Work.Spaces.DzIter (m + 1) (Work.Spaces.DthIter i f) z θ := by
        intro z
        show z * deriv h1 z = Work.Spaces.DzIter (m + 1) (Work.Spaces.DthIter i f) z θ
        rw [hderiv1]
        rfl
      -- the identification of the three `z`-`lintegrals`
      have hPid : blkZ f (i, m) θ
          = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h1 z) ^ 2) := by
        unfold blkZ hblkR
        refine lintegral_congr (fun z => ?_)
        rw [h1def]
        congr 1
        ring
      have hQid : blkZ F (i, m) θ
          = ∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h1) z) ^ 2) := by
        unfold blkZ hblkR
        refine lintegral_congr_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
        by_cases hz0 : z = 0
        · subst hz0
          simp [Work.Spaces.w]
        · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
          have h3 : z ^ 2 * Work.Spaces.pzIter 2
                (Work.Spaces.DzIter m (Work.Spaces.DthIter i f)) z θ
              = Work.Spaces.DzIter m (Work.Spaces.DthIter i F) z θ := by
            rw [show Work.Spaces.DzIter m (Work.Spaces.DthIter i f)
                = Work.Spaces.mixed m i f from rfl]
            rw [AgmonSlice.zsq_pzIter2_mixed_open f hf m i hzpos hθ]
            rfl
          rw [show (Work.Spaces.DzIter m (Work.Spaces.DthIter i F) z θ) ^ 2
                = (z ^ 2 * deriv (deriv h1) z) ^ 2 from by
              rw [hderiv2, h3]]
          ring
      have hXid : blkZ (Work.Spaces.Dz f) (i, m) θ
          = ∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDz h1 z) ^ 2) := by
        unfold blkZ hblkR
        refine lintegral_congr_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
        by_cases hz0 : z = 0
        · subst hz0
          simp [Work.Spaces.w]
        · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
          have hcomm : ∀ z' θ', 0 < z' → θ' ∈ Set.Ioo 0 (Real.pi / 2) →
              Work.Spaces.DthIter i (Work.Spaces.Dz f) z' θ'
                = Work.Spaces.Dz (Work.Spaces.DthIter i f) z' θ' := by
            intro z' θ' hz' hθ'
            have h := DthIter_DzIter_eq_mixed_open hf 1 i hz' hθ'
            rwa [show Work.Spaces.DzIter 1 f = Work.Spaces.Dz f from rfl,
              show Work.Spaces.mixed 1 i f = Work.Spaces.Dz (Work.Spaces.DthIter i f) from rfl]
              at h
          have h2 : Work.Spaces.DzIter m (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
              = Work.Spaces.DzIter (m + 1) (Work.Spaces.DthIter i f) z θ := by
            rw [show Work.Spaces.DzIter m (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
                = Work.Spaces.DzIter m (Work.Spaces.Dz (Work.Spaces.DthIter i f)) z θ from
              DzIter_congr_of_eqOn_Q0 hcomm m z θ hzpos hθ]
            rw [show (m + 1) = m + 1 from rfl, Work.Spaces.DzIter_add_right]
            rfl
          rw [h2, hrDz z]
          congr 1
          ring
      -- the three `z`-`lintegrals`
      have hC0 : ENNReal.ofReal C ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hC)
      by_cases hPf : (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h1 z) ^ 2)) = ⊤
      · rw [hXid, hPid, hPf, top_add, ENNReal.mul_top hC0]
        exact le_top
      by_cases hQf : (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h1) z) ^ 2)) = ⊤
      · rw [hXid, hPid, hQid, hQf,
          ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hα 4))), add_top,
          ENNReal.mul_top hC0]
        exact le_top
      · -- both siblings are finite: the finiteness interface and the Agmon
        have hXf : (∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDz h1 z) ^ 2)) ≠ ⊤ :=
          hfin h1 hslice hPf hQf
        have hcontP : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (h1 z) ^ 2)
            (Set.Ioi 0) :=
          (continuousOn_w_Ioi.pow 2).mul (hslice.continuousOn.pow 2)
        have hcontQ : ContinuousOn
            (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h1) z) ^ 2)
            (Set.Ioi 0) := by
          rw [hderiv2]
          have h1c : ContinuousOn (fun z : ℝ => z ^ 2) (Set.Ioi 0) := continuousOn_id.pow 2
          have h2c : ContinuousOn (fun z : ℝ => Work.Spaces.pzIter 2
              (Work.Spaces.DzIter m (Work.Spaces.DthIter i f)) z θ) (Set.Ioi 0) :=
            (hsm.mixed m i).continuousOn_slice_pzIter hθ 2
          exact (continuousOn_w_Ioi.pow 2).mul ((h1c.mul h2c).pow 2)
        have hcontX : ContinuousOn
            (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDz h1 z) ^ 2)
            (Set.Ioi 0) := by
          rw [show (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDz h1 z) ^ 2)
              = fun z : ℝ => (Work.Spaces.w z) ^ 2
                  * (z * Work.Spaces.pz (Work.Spaces.DzIter m (Work.Spaces.DthIter i f)) z θ) ^ 2
              from by
                funext z
                rw [show Work.FTS.EllipticEst.rDz h1 z
                    = z * Work.Spaces.pz (Work.Spaces.DzIter m (Work.Spaces.DthIter i f)) z θ from by
                  show z * deriv h1 z = _
                  rw [hderiv1]]]
          have h1c : ContinuousOn (fun z : ℝ => z) (Set.Ioi 0) := continuousOn_id
          have h2c : ContinuousOn (fun z : ℝ => Work.Spaces.pz
              (Work.Spaces.DzIter m (Work.Spaces.DthIter i f)) z θ) (Set.Ioi 0) :=
            (hsm.mixed m i).continuousOn_slice_pzIter hθ 1
          exact (continuousOn_w_Ioi.pow 2).mul ((h1c.mul h2c).pow 2)
        have hPint : MeasureTheory.IntegrableOn
            (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (h1 z) ^ 2) Work.Spaces.Iz :=
          (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
            (aesm_slice_z hcontP) (Filter.Eventually.of_forall (fun z => by positivity))).mp hPf
        have hQint : MeasureTheory.IntegrableOn
            (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h1) z) ^ 2)
            Work.Spaces.Iz :=
          (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
            (aesm_slice_z hcontQ) (Filter.Eventually.of_forall (fun z => by positivity))).mp hQf
        have hreal := hag α hα hα1 h1 hslice hPint hQint
        have hXeq := ofReal_integral_eq_lintegral_Iz hcontX (fun z => by positivity) hXf
        have hPeq := ofReal_integral_eq_lintegral_Iz hcontP (fun z => by positivity) hPf
        have hQeq := ofReal_integral_eq_lintegral_Iz hcontQ (fun z => by positivity) hQf
        rw [hXid, hPid, hQid, ← hXeq, ← hPeq, ← hQeq]
        rw [← ENNReal.ofReal_mul (sq_nonneg α), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (le_of_lt hC)]
        exact ENNReal.ofReal_le_ofReal hreal
    · -- measurability of the `θ`-integrand
      exact (blkZ_aemeasurable f hf i m).mul (angw_ofReal_aemeasurable α i)
  · rw [blkP, if_neg hk, blkP, if_neg hk, blkP, if_neg hk]
    simp

/-- Distributivity of a double `Finset`-sum of `ℝ≥0∞`-valued terms. -/
theorem sum_sum_mul_add (c a : ℝ≥0∞) (n : ℕ) (A B : ℕ → ℕ → ℝ≥0∞) :
    (∑ i ∈ Finset.range n, ∑ m ∈ Finset.range n, c * (A i m + a * B i m))
      = c * ((∑ i ∈ Finset.range n, ∑ m ∈ Finset.range n, A i m)
          + a * (∑ i ∈ Finset.range n, ∑ m ∈ Finset.range n, B i m)) := by
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]

/-- **Interface: the unconditional `ℝ≥0∞` Agmon estimate** (delivered by
`Work.FTS.EllipticEst.AgmonSlice.rDz_agmon_lintegral`). -/
def AgmonLinInterface (C : ℝ) : Prop :=
  ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (h : ℝ → ℝ),
    ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi 0) →
    ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDz h z) ^ 2))
      ≤ ENNReal.ofReal C * ((∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2))
          + ENNReal.ofReal (α ^ 4) * (∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2)))

/-- **The per-block Agmon inequality, from the unconditional one-dimensional estimate.**

This is the companion of `blkP_agmon`: same conclusion, but the input is the unconditional
`ℝ≥0∞` estimate, so no case analysis on the finiteness of the sibling integrals is needed. -/
theorem blkP_agmon_lin (C : ℝ) (hC : 0 < C) (hag : AgmonLinInterface C)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (f : ℝ → ℝ → ℝ)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) (i m : ℕ) :
    ENNReal.ofReal (α ^ 2) * blkP α k (Work.Spaces.Dz f) (i, m)
      ≤ ENNReal.ofReal C * (blkP α k f (i, m)
        + ENNReal.ofReal (α ^ 4)
          * blkP α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) (i, m)) := by
  set F : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ with hF
  have hsm : SmoothOpen f := smoothOpen_of_forall hf
  by_cases hk : i + m ≤ k
  · rw [blkP, if_pos hk, blkP, if_pos hk, blkP, if_pos hk]
    refine blkP_int_step hα hC ?_ ?_
    · intro θ hθ
      have hmem : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      set h1 : ℝ → ℝ := fun z => Work.Spaces.DzIter m (Work.Spaces.DthIter i f) z θ with h1def
      have hslice : ContDiffOn ℝ Work.Stability.smoothOrder h1 (Set.Ioi 0) := by
        have h := (hsm.mixed m i).curry_z hθ
        simpa only [h1def, Work.Spaces.mixed] using h
      have hderiv1 : deriv h1
          = fun z : ℝ => Work.Spaces.pz (Work.Spaces.DzIter m (Work.Spaces.DthIter i f)) z θ := by
        funext z
        rw [h1def]
        rfl
      have hderiv2 : deriv (deriv h1)
          = fun z : ℝ => Work.Spaces.pzIter 2
              (Work.Spaces.DzIter m (Work.Spaces.DthIter i f)) z θ := by
        funext z
        rw [h1def]
        simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
      have hrDz : ∀ z : ℝ, Work.FTS.EllipticEst.rDz h1 z
          = Work.Spaces.DzIter (m + 1) (Work.Spaces.DthIter i f) z θ := by
        intro z
        show z * deriv h1 z = Work.Spaces.DzIter (m + 1) (Work.Spaces.DthIter i f) z θ
        rw [hderiv1]
        rfl
      have hPid : blkZ f (i, m) θ
          = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h1 z) ^ 2) := by
        unfold blkZ hblkR
        refine lintegral_congr (fun z => ?_)
        rw [h1def]
        congr 1
        ring
      have hQid : blkZ F (i, m) θ
          = ∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h1) z) ^ 2) := by
        unfold blkZ hblkR
        refine lintegral_congr_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
        by_cases hz0 : z = 0
        · subst hz0
          simp [Work.Spaces.w]
        · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
          have h3 : z ^ 2 * Work.Spaces.pzIter 2
                (Work.Spaces.DzIter m (Work.Spaces.DthIter i f)) z θ
              = Work.Spaces.DzIter m (Work.Spaces.DthIter i F) z θ := by
            rw [show Work.Spaces.DzIter m (Work.Spaces.DthIter i f)
                = Work.Spaces.mixed m i f from rfl]
            rw [AgmonSlice.zsq_pzIter2_mixed_open f hf m i hzpos hθ]
            rfl
          rw [show (Work.Spaces.DzIter m (Work.Spaces.DthIter i F) z θ) ^ 2
                = (z ^ 2 * deriv (deriv h1) z) ^ 2 from by
              rw [hderiv2, h3]]
          ring
      have hXid : blkZ (Work.Spaces.Dz f) (i, m) θ
          = ∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDz h1 z) ^ 2) := by
        unfold blkZ hblkR
        refine lintegral_congr_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
        by_cases hz0 : z = 0
        · subst hz0
          simp [Work.Spaces.w]
        · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
          have hcomm : ∀ z' θ', 0 < z' → θ' ∈ Set.Ioo 0 (Real.pi / 2) →
              Work.Spaces.DthIter i (Work.Spaces.Dz f) z' θ'
                = Work.Spaces.Dz (Work.Spaces.DthIter i f) z' θ' := by
            intro z' θ' hz' hθ'
            have h := DthIter_DzIter_eq_mixed_open hf 1 i hz' hθ'
            rwa [show Work.Spaces.DzIter 1 f = Work.Spaces.Dz f from rfl,
              show Work.Spaces.mixed 1 i f = Work.Spaces.Dz (Work.Spaces.DthIter i f) from rfl]
              at h
          have h2 : Work.Spaces.DzIter m (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
              = Work.Spaces.DzIter (m + 1) (Work.Spaces.DthIter i f) z θ := by
            rw [show Work.Spaces.DzIter m (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
                = Work.Spaces.DzIter m (Work.Spaces.Dz (Work.Spaces.DthIter i f)) z θ from
              DzIter_congr_of_eqOn_Q0 hcomm m z θ hzpos hθ]
            rw [show (m + 1) = m + 1 from rfl, Work.Spaces.DzIter_add_right]
            rfl
          rw [h2, hrDz z]
          congr 1
          ring
      rw [hXid, hPid, hQid]
      exact hag α hα hα1 h1 hslice
    · exact (blkZ_aemeasurable f hf i m).mul (angw_ofReal_aemeasurable α i)
  · rw [blkP, if_neg hk, blkP, if_neg hk, blkP, if_neg hk]
    simp

/-! ## The assembly of the `ℋ^k` estimate from the per-block inequality -/

theorem HkSq_Dz_le_assembly (C0 : ℝ) (hC0 : 0 < C0) (k : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : ℝ → ℝ → ℝ)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmf : Work.Spaces.HkMem α k f)
    (hmF : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ))
    (hsum : ∀ i m : ℕ,
      ENNReal.ofReal (α ^ 2) * blkP α k (Work.Spaces.Dz f) (i, m)
        ≤ ENNReal.ofReal C0 * (blkP α k f (i, m)
          + ENNReal.ofReal (α ^ 4)
            * blkP α k (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) (i, m))) :
    α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz f)
      ≤ C0 * (Work.Spaces.HkSq α k f
          + α ^ 4 * Work.Spaces.HkSq α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)) := by
  have hsmf : SmoothOpen f := smoothOpen_of_forall hf
  have hzsqmul : SmoothOpen (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) := by
    change ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)) Q0
    have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => p.1 ^ 2) Q0 := contDiffOn_fst.pow 2
    have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
        (Function.uncurry (Work.Spaces.pzIter 2 f)) Q0 := hsmf.pzIter 2
    rw [show Function.uncurry (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)
        = (fun p : ℝ × ℝ => p.1 ^ 2) * (Function.uncurry (Work.Spaces.pzIter 2 f))
        from rfl]
    exact h2.mul h3
  have hFs : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hzsqmul.forall
  have hDzs : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (Work.Spaces.Dz f)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hsmf.Dz.forall
  have hLkf : Lk α k f = ENNReal.ofReal (Work.Spaces.HkSq α k f) :=
    Lk_eq_ofReal_HkSq α k f hf hmf
  have hLkF : Lk α k (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)
      = ENNReal.ofReal (Work.Spaces.HkSq α k
          (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)) :=
    Lk_eq_ofReal_HkSq α k (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) hFs hmF
  have hLk : ENNReal.ofReal (α ^ 2) * Lk α k (Work.Spaces.Dz f)
      ≤ ENNReal.ofReal C0 * (Lk α k f
        + ENNReal.ofReal (α ^ 4)
          * Lk α k (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)) := by
    calc ENNReal.ofReal (α ^ 2) * Lk α k (Work.Spaces.Dz f)
        = ∑ i ∈ Finset.range (k + 1), ∑ m ∈ Finset.range (k + 1),
            ENNReal.ofReal (α ^ 2) * blkP α k (Work.Spaces.Dz f) (i, m) := by
          rw [Lk_eq_blocks α k (Work.Spaces.Dz f) hDzs, Finset.mul_sum]
          congr 1 with i
          rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range (k + 1), ∑ m ∈ Finset.range (k + 1),
            ENNReal.ofReal C0 * (blkP α k f (i, m)
              + ENNReal.ofReal (α ^ 4)
                * blkP α k (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) (i, m)) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun m _ => hsum i m))
      _ = ENNReal.ofReal C0 * (Lk α k f
            + ENNReal.ofReal (α ^ 4)
              * Lk α k (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)) := by
          rw [Lk_eq_blocks α k f hf, Lk_eq_blocks α k
            (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) hFs]
          exact sum_sum_mul_add (ENNReal.ofReal C0) (ENNReal.ofReal (α ^ 4)) (k + 1)
            (fun i m => blkP α k f (i, m))
            (fun i m => blkP α k (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) (i, m))
  have hRHS : ENNReal.ofReal C0 * (Lk α k f
      + ENNReal.ofReal (α ^ 4)
        * Lk α k (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)) ≠ ⊤ := by
    rw [hLkf, hLkF]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    refine (ENNReal.add_ne_top).mpr ⟨ENNReal.ofReal_ne_top, ?_⟩
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hFinLk : Lk α k (Work.Spaces.Dz f) ≠ ⊤ := by
    intro htop
    rw [htop] at hLk
    rw [ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hα 2)))] at hLk
    exact hRHS (top_le_iff.mp hLk)
  have hHkSq : Work.Spaces.HkSq α k (Work.Spaces.Dz f)
      ≤ (Lk α k (Work.Spaces.Dz f)).toReal :=
    HkSq_le_toReal_Lk α k (Work.Spaces.Dz f) hDzs hFinLk
  have hfin1 : Lk α k f ≠ ⊤ := by rw [hLkf]; exact ENNReal.ofReal_ne_top
  have hfin2 : ENNReal.ofReal (α ^ 4)
      * Lk α k (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) ≠ ⊤ := by
    rw [hLkF]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  calc α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz f)
      ≤ α ^ 2 * (Lk α k (Work.Spaces.Dz f)).toReal :=
        mul_le_mul_of_nonneg_left hHkSq (by positivity)
    _ = (ENNReal.ofReal (α ^ 2) * Lk α k (Work.Spaces.Dz f)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg α)]
    _ ≤ (ENNReal.ofReal C0 * (Lk α k f
          + ENNReal.ofReal (α ^ 4)
            * Lk α k (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ))).toReal :=
        ENNReal.toReal_mono hRHS hLk
    _ = C0 * (Work.Spaces.HkSq α k f
          + α ^ 4 * Work.Spaces.HkSq α k (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt hC0),
          ENNReal.toReal_add hfin1 hfin2, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (by positivity), hLkf, hLkF,
          ENNReal.toReal_ofReal (Work.Spaces.HkSq_nonneg α k f),
          ENNReal.toReal_ofReal (Work.Spaces.HkSq_nonneg α k
            (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ))]

end

end Work.FTS.EllipticEst
