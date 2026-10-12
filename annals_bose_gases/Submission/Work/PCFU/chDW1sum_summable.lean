import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.BoseBoxFock.frame_lattice_ball
import Submission.Work.PCFU.chDaliasSum_summable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.PCFU.chDW1sum_summable` — summability of the `(D)`-slot alias family of `W₁`

The `(D)`-channel alias slot needs the `d`-family

    `d ↦ ‖(χ_ℓ ⋆ W₁)(z + ℓ•d)‖`,     `χ_ℓ = corpusBox.chiLam ℓ`, `W₁ = W1fun v h ℓ`

to be summable over the lattice `Fin 3 → ℤ` (the sum is *not* punctured at `d = 0`).

This is the sibling of `Work.PCFU.chDaliasSum_summable`, which treats the same family *weighted*
by the constant `χ_ℓ(z)`; here no such factor is present, so the degenerate case `χ_ℓ(z) = 0`
disappears and the argument is purely finite support:

* `χ_ℓ` vanishes off `ball 0 (ℓ/2)` (`chiLam_supp`, from the corpus bump `BoseGases.chi`);
* `W₁ = wScaled ℓ (g₀)` is supported in `ball 0 R` (`Work.BoseFixR.tsupport_W1fun_subset`, from
  `h : ScatSol v` and `hv_supp`).

Hence `(χ_ℓ ⋆ W₁)(u) = 0` whenever `R + ℓ/2 ≤ ‖u‖` (`chDconv_eq_zero_far` — pointwise, and no
relation between `ℓ` and `R` is required), so the only contributing indices satisfy
`‖z + ℓ•d‖ < R + ℓ/2`, i.e. `‖d‖ < (R + ℓ/2 + ‖z‖)/ℓ`; integer vectors in that ball are finite.
Finite support gives `Summable` via `summable_of_hasFiniteSupport`.

`hR` is not needed (it is part of the requested interface).
-/

namespace Work.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `χ_ℓ = corpusBox.chiLam ℓ` vanishes off `ball 0 (ℓ/2)`. -/
private lemma chiLam_supp_of_ne_zero {ℓ : ℝ} (hℓ : 0 < ℓ) (x : E3)
    (hx : Work.BoseK15.corpusBox.chiLam ℓ x ≠ 0) : ‖x‖ < ℓ / 2 := by
  have hx' : Submission.BoseGases.chi (ℓ⁻¹ • x) ≠ 0 := hx
  have h1 : ‖ℓ⁻¹ • x‖ < (1 : ℝ) / 2 := by
    by_contra hc
    have hb : Submission.BoseGases.chiBase (ℓ⁻¹ • x) = 0 := by
      apply Submission.BoseGases.chiBump.zero_of_le_dist
      simpa [Submission.BoseGases.chiBump, dist_eq_norm] using le_of_not_gt hc
    exact hx' (by simp [Submission.BoseGases.chi, hb])
  have h2 : ‖ℓ⁻¹ • x‖ = ℓ⁻¹ * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le)]
  rw [h2] at h1
  have : ‖x‖ < ℓ * (1 / 2) := by
    calc ‖x‖ = ℓ * (ℓ⁻¹ * ‖x‖) := by rw [mul_inv_cancel_left₀ (ne_of_gt hℓ)]
      _ < ℓ * (1 / 2) := mul_lt_mul_of_pos_left h1 hℓ
  linarith

/-- If `R + ℓ/2 ≤ ‖u‖` then the convolution `(χ_ℓ ⋆ W₁)(u)` vanishes: the `χ_ℓ`-factor forces
`‖w‖ < ℓ/2`, and then `‖u − w‖ > R` puts `u − w` outside the support of `W₁`. -/
private lemma chDconv_eq_zero_far {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {ℓ : ℝ} (hℓ : 0 < ℓ) (u : E3)
    (hu : R + ℓ / 2 ≤ ‖u‖) :
    Work.BoseBoxFock.PCFU.chDconv ℓ (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ)) u = 0 := by
  rw [Work.BoseBoxFock.PCFU.chDconv]
  have hzero : (fun w : E3 => (((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ)) : ℂ)
      * ((Work.BoseFixR.W1fun v h ℓ (u - w) : ℝ) : ℂ)) = fun _ => (0 : ℂ) := by
    funext w
    by_cases hw : Work.BoseK15.corpusBox.chiLam ℓ w = 0
    · have hw' : Submission.BoseGases.chi (ℓ⁻¹ • w) = 0 := hw
      simp [hw']
    · have hwn : ‖w‖ < ℓ / 2 := chiLam_supp_of_ne_zero hℓ w hw
      have hlt : R < ‖u - w‖ := by
        have h1 : ‖u‖ ≤ ‖u - w‖ + ‖w‖ := by
          have h2 := norm_add_le (u - w) w
          rwa [sub_add_cancel] at h2
        linarith
      have hW : Work.BoseFixR.W1fun v h ℓ (u - w) = 0 := by
        by_contra hc
        have hmem : u - w ∈ Function.support (Work.BoseFixR.W1fun v h ℓ) := by
          simpa [Function.mem_support] using hc
        have hball := Work.BoseFixR.tsupport_W1fun_subset h hv_supp ℓ (subset_tsupport _ hmem)
        rw [Metric.mem_ball, dist_zero_right] at hball
        linarith
      have hW' : ((Work.BoseFixR.W1fun v h ℓ (u - w) : ℝ) : ℂ) = 0 := by simp [hW]
      simp [hW']
  rw [hzero]
  simp

theorem chDW1sum_summable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R ℓ : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hℓ : 0 < ℓ) (z : EuclideanSpace ℝ (Fin 3)) :
    Summable (fun d : Fin 3 → ℤ => ‖Work.BoseBoxFock.PCFU.chDconv ℓ
      (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
      (z + ℓ • Work.BoseBoxFock.latVec d)‖) := by
  set T : Set (Fin 3 → ℤ) := {d | ‖z + ℓ • Work.BoseBoxFock.latVec d‖ < R + ℓ / 2} with hTdef
  set K : ℝ := (R + ℓ / 2 + ‖z‖) / ℓ with hKdef
  set N : ℕ := ⌈K⌉₊ with hNdef
  have hNle : K ≤ (N : ℝ) := by
    rw [hNdef]; exact Nat.le_ceil K
  -- the contributing indices form a subset of the integer cube `[-N, N]³`
  have hTsub : T ⊆ ↑(Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(N : ℤ)) (N : ℤ))) := by
    intro d hd
    simp only [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hd' : ‖z + ℓ • Work.BoseBoxFock.latVec d‖ < R + ℓ / 2 := hd
    have hdK : ‖Work.BoseBoxFock.latVec d‖ < K := by
      have h2 : ℓ * ‖Work.BoseBoxFock.latVec d‖
          ≤ ‖z + ℓ • Work.BoseBoxFock.latVec d‖ + ‖z‖ := by
        have h3 := norm_add_le (z + ℓ • Work.BoseBoxFock.latVec d) (-z)
        have h4 : (z + ℓ • Work.BoseBoxFock.latVec d) + (-z)
            = ℓ • Work.BoseBoxFock.latVec d := by abel
        rw [h4, norm_neg, norm_smul, Real.norm_of_nonneg hℓ.le] at h3
        exact h3
      rw [hKdef, lt_div_iff₀ hℓ, mul_comm]
      linarith
    have hdi : |(((d i : ℤ)) : ℝ)| < K := by
      have h1 : |(((d i : ℤ)) : ℝ)| ≤ ‖Work.BoseBoxFock.latVec d‖ := by
        have h2 := PiLp.norm_apply_le (Work.BoseBoxFock.latVec d) i
        simpa [Real.norm_eq_abs, Work.BoseBoxFock.latVec_apply] using h2
      linarith
    have hcast : (((|d i| : ℤ)) : ℝ) < ((N : ℤ) : ℝ) := by
      rw [Int.cast_abs]
      exact lt_of_lt_of_le hdi (by simpa using hNle)
    have hlt : (|d i| : ℤ) < (N : ℤ) := by exact_mod_cast hcast
    have hlt' : -(N : ℤ) < d i ∧ d i < (N : ℤ) := abs_lt.mp hlt
    exact ⟨le_of_lt hlt'.1, le_of_lt hlt'.2⟩
  have hTfin : T.Finite := (Finset.finite_toSet _).subset hTsub
  refine summable_of_hasFiniteSupport ?_
  refine hTfin.subset ?_
  intro d hd
  rw [Function.mem_support] at hd
  by_contra hcon
  rw [hTdef, Set.mem_ofPred_eq, not_lt] at hcon
  have hvv := chDconv_eq_zero_far (h := h) hv_supp hℓ (z + ℓ • Work.BoseBoxFock.latVec d) hcon
  exact hd (by rw [hvv, norm_zero])

end Work.PCFU
