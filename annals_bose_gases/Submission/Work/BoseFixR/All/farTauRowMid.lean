import ChallengeDeps
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Submission.Work.BoseFixR.All.FarEnvPos
import Submission.Work.BoseFixR.All.FarKernelRowsB
import Submission.Work.BoseFixR.All.farTauArith
import Submission.Work.BoseFixR.All.sharpRowLabNAe
import Submission.Work.BoseFixR.All.tauSmFloor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/All/farTauRowMid.lean` — the `τ'`-weighted sharp lattice row

The target (`Work.BoseFixR.All.farTauRowMid`) is the `τ'`-weighted sharp lattice row of the
`All`-vocabulary far leg, with `τ'_k = (1−ε)τ_k + ρε^{-1/2}a` and the floor `μ ≤ 10ρ` on the
density (the floor removes the `ρ ↓ 0` branch on which the un-floored sibling
`All/farTauRowProv` is false).

## The proof

It is *pointwise*: one shows that for **every** momentum `q`

  `‖q‖²/(1 + 100√ε) ≤ (1−ε)·tauSm eT s d ℓ q + ρ·ε^{-1/2}·a`     (★)

and then multiplies by the (nonnegative) numerator `Ŵ₁(q_k)²` and sums against the *sharp*
lattice row (constant `1`), which converts the `‖q‖²`-weighted lattice sum into the continuum
integral of the right-hand side.

* `Work.BoseFixR.All.tauSmFloor` is (★).  With `c₁ = (2sℓ)⁻¹`, `c₂ = (2dsℓ)⁻¹`,
  `S = (1−eT)c₁ + eT c₂`, `B = ρε^{-1/2}a` and `τ̃(r) ≥ (max 0 (r−2))²`
  (`farTauAux.max_kink_le_smul_tauProf`): for `‖q‖ ≥ 2c₂` one has `τ(q) ≥ ‖q‖² − 4S‖q‖`, so
  `τ'(q) ≥ ‖q‖² − 4S‖q‖ − ε‖q‖² + B ≥ ‖q‖²(1−δ) + (δ‖q‖²/2 − 4S‖q‖ + B)`, which is
  `≥ ‖q‖²/(1+100√ε)` once the quadratic `(100√ε/2)‖q‖² − 4S‖q‖ + B` is nonnegative, i.e. once
  `8S² ≤ 100√ε·B`; for `‖q‖ ≤ 2c₂` the floor alone dominates (`4c₂² ≤ B`).
* `Work.BoseFixR.All.farTauArith` supplies those two numeric conditions (`hC5`, `hC4`) at FS's
  parameters: both are monomial comparisons in `X = (μa³)^{1/323}` (with
  `μℓ³ = X^{-166}`, `d = X⁶`, `ε_T = X^{23/4}`, `ℓ = (a v)X^{-163}`, and `ε ≤ X^{323/8}` from
  `bigMV_div_ell_cube_le_quarter`), using `ρ ≥ μ/10` and `X ≤ 1`.
* `Work.BoseFixR.All.sharpRowLabNAe` is the constant-`1` cube row
  `Σ_{k≠0} Ŵ₁(q_k)²/‖q_k‖² ≤ 2(2π)^{-3}ℓ³∫Ŵ₁²/(2‖q‖²)`, in the *a.e.*-nonnegativity form of `W₁`
  (the only form available: `W1fun = wScaled ℓ (g0 v h)` is nonnegative only a.e.).
-/

namespace Work.BoseFixR.All

/-- The elementary division step: `f/τ ≤ (1+δ)·(f/s)` as soon as `s/(1+δ) ≤ τ`, `f ≥ 0` and
`s > 0`. -/
private lemma term_le_aux {f τ s δ : ℝ} (hf : 0 ≤ f) (hs : 0 < s) (hδ : 0 ≤ δ)
    (h : s / (1 + δ) ≤ τ) : f / τ ≤ (1 + δ) * (f / s) := by
  have h1δ : 0 < 1 + δ := by linarith
  have hs1 : 0 < s / (1 + δ) := div_pos hs h1δ
  have hτ : 0 < τ := lt_of_lt_of_le hs1 h
  have hkey : (1 + δ) * (f / s) * (s / (1 + δ)) = f := by
    field_simp
  rw [div_le_iff₀ hτ]
  calc f = (1 + δ) * (f / s) * (s / (1 + δ)) := hkey.symm
    _ ≤ (1 + δ) * (f / s) * τ :=
        mul_le_mul_of_nonneg_left h (mul_nonneg h1δ.le (div_nonneg hf hs.le))

theorem farTauRowMid {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    {ε₀ μ : ℝ} (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ))) (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0)
    (hreg : 100 * R ≤ Work.BoseFixR.ell v μ)
    (ρ : ℝ) (hρ : 0 < ρ) (hρm : μ ≤ 10 * ρ)
    (hfar : Work.BoseBoxFock.FarCondFS v μ ρ) :
    (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
            (Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) (HM μ).N k)) ^ 2
          / ((1 - Work.BoseFixR.All.epsFar v μ ρ)
                * Work.BoseBoxFock.tauSm (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
                    (Work.BoseFixR.ell v μ)
                    (Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) (HM μ).N k)
              + ρ * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v))
      ≤ (1 + 100 * Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ))
          * (2 * (((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3
            * ∫ q : EuclideanSpace ℝ (Fin 3),
                (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) q) ^ 2
                  / (2 * ‖q‖ ^ 2))) := by
  classical
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < Work.BoseFixR.ell v μ := Work.BoseFixR.ell_pos' v hμ hav
  have hε0 : 0 < Work.BoseFixR.All.epsFar v μ ρ :=
    Work.BoseFixR.All.farEnvPos_eps_pos hμ hav hρ
  have hε8 : Work.BoseFixR.All.epsFar v μ ρ ≤ 1 / 10 ^ 8 :=
    Work.BoseFixR.All.FarResidBaux.epsFar_le_inv_eight hAdm hε₀ hav hρ.le hfar
  have hε1 : Work.BoseFixR.All.epsFar v μ ρ ≤ 1 / 4 := by linarith
  have hδ1 : 100 * Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ) ≤ 1 := by
    have h4 : Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ) ≤ 1 / 100 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 100)]
      exact Real.sqrt_le_sqrt (by linarith)
    linarith
  -- the parameter facts at `t = μ (a v)³ ≤ 1`
  have ht0 : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
  have ht1 : μ * (BoseGases.a v) ^ 3 ≤ 1 := by
    have h1 : (10 : ℝ) ^ (-(4000 : ℤ)) ≤ 1 := by
      rw [show (10 : ℝ) ^ (-(4000 : ℤ)) = 1 / 10 ^ 4000 by norm_num]
      exact div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
    linarith [hAdm.2.1, hε₀, h1]
  obtain ⟨hC5, hC4⟩ := farTauArith (v := v) hav hε₀ hAdm ρ hρ hρm
  -- the pointwise floor comparison (★)
  have hpt : ∀ q : EuclideanSpace ℝ (Fin 3),
      ‖q‖ ^ 2 / (1 + 100 * Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ))
        ≤ (1 - Work.BoseFixR.All.epsFar v μ ρ)
            * Work.BoseBoxFock.tauSm (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
                (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
                (Work.BoseBox.paramsAt μ (BoseGases.a v)).d (Work.BoseFixR.ell v μ) q
          + ρ * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v := by
    intro q
    exact tauSmFloor (eT := (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT)
      (s := (Work.BoseBox.paramsAt μ (BoseGases.a v)).s)
      (d := (Work.BoseBox.paramsAt μ (BoseGases.a v)).d)
      (ℓ := Work.BoseFixR.ell v μ) (a := BoseGases.a v) (ρ := ρ)
      (ε := Work.BoseFixR.All.epsFar v μ ρ)
      (by rw [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]; exact Work.BoseBox.fsXp_pos ht0)
      (by rw [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]; exact Work.BoseBox.fsXp_pos ht0)
      (by rw [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
          exact Work.BoseBox.fsXp_le_one ht0 ht1 (by norm_num))
      hℓ
      (by rw [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]; exact (Work.BoseBox.fsXp_pos ht0).le)
      (by rw [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
          exact Work.BoseBox.fsXp_le_one ht0 ht1 (by norm_num))
      hav hε0 hε1 hδ1 hC5 hC4 q
  -- the sharp lattice row
  have hW : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  have hWae : 0 ≤ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))]
      (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) :=
    Submission.BoseGases.wScaled_g0_nonneg_ae hR hv hvrad hv_supp h
  have hsharp := sharpRowLabNAe (ℓ := Work.BoseFixR.ell v μ) h hv hvrad hR hℓ hv_supp
    hRℓ hreg hW hWae (HM μ).N
  -- the labels of `excited (Lab N)` are nonzero, so `‖kmomLab ·‖ > 0`
  have hq_ne : ∀ k : Work.BoseBoxFock.Lab (HM μ).N, k ≠ 0 →
      Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) (HM μ).N k ≠ 0 := by
    intro k hk h0
    rw [Work.BoseBoxFock.GramLab.kmomLab_eq_smul_vec] at h0
    have h1 : Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N k) = 0 := by
      rcases smul_eq_zero.mp h0 with h' | h'
      · exact absurd h' (inv_ne_zero (ne_of_gt hℓ))
      · exact h'
    have h2 : Work.BoseBoxFock.labVec (HM μ).N k = 0 := by
      funext i
      have hi : (Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N k)
          : EuclideanSpace ℝ (Fin 3)) i = 0 := by
        rw [h1]; rfl
      simp only [Work.BoseB4.vec, WithLp.ofLp_toLp] at hi
      have h3 : ((Work.BoseBoxFock.labVec (HM μ).N k i : ℤ) : ℝ) = 0 := by
        have h4 := mul_left_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0)
          (show (2 * Real.pi) * ((Work.BoseBoxFock.labVec (HM μ).N k i : ℤ) : ℝ)
              = (2 * Real.pi) * 0 by rw [mul_zero]; exact hi)
        simpa using h4
      exact_mod_cast h3
    exact hk (Work.BoseBoxFock.GramLab.labVec_injective (HM μ).N
      (by rw [h2, Work.BoseBoxFock.GramLab.labVec_zero]))
  -- the termwise bound `Ŵ₁(q_k)²/τ'_k ≤ (1+100√ε)·Ŵ₁(q_k)²/‖q_k‖²`
  have hsum1 : (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
            (Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) (HM μ).N k)) ^ 2
          / ((1 - Work.BoseFixR.All.epsFar v μ ρ)
                * Work.BoseBoxFock.tauSm (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
                    (Work.BoseFixR.ell v μ)
                    (Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) (HM μ).N k)
              + ρ * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v))
      ≤ ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
          (1 + 100 * Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ))
            * ((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
                (Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) (HM μ).N k)) ^ 2
              / ‖Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) (HM μ).N k‖ ^ 2) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hk0 : k ≠ 0 := by
      simp only [Work.BoseB7.excited, Finset.mem_erase] at hk
      exact hk.1
    have hq : 0 < ‖Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) (HM μ).N k‖ ^ 2 := by
      have h1 : 0 < ‖Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) (HM μ).N k‖ :=
        norm_pos_iff.mpr (hq_ne k hk0)
      positivity
    exact term_le_aux (sq_nonneg _) hq (by positivity) (hpt _)
  calc (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
            (Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) (HM μ).N k)) ^ 2
          / ((1 - Work.BoseFixR.All.epsFar v μ ρ)
                * Work.BoseBoxFock.tauSm (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
                    (Work.BoseFixR.ell v μ)
                    (Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) (HM μ).N k)
              + ρ * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v))
      ≤ ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
          (1 + 100 * Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ))
            * ((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
                (Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) (HM μ).N k)) ^ 2
              / ‖Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) (HM μ).N k‖ ^ 2) := hsum1
    _ = (1 + 100 * Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ))
          * ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
              (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
                  (Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) (HM μ).N k)) ^ 2
                / ‖Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) (HM μ).N k‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ (1 + 100 * Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ))
          * (2 * (((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3
            * ∫ q : EuclideanSpace ℝ (Fin 3),
                (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) q) ^ 2
                  / (2 * ‖q‖ ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h2 : 2 * ((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3
              * (∫ q : EuclideanSpace ℝ (Fin 3),
                  (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) q) ^ 2
                    / (2 * ‖q‖ ^ 2))
            = 2 * (((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3
              * ∫ q : EuclideanSpace ℝ (Fin 3),
                  (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) q) ^ 2
                    / (2 * ‖q‖ ^ 2)) := by ring
        rw [h2] at hsharp
        exact hsharp

end Work.BoseFixR.All
