import Mathlib
import Submission.Work.Hormander.Weights.Rint
import Submission.Work.Hormander.Weights.rpair0_delta_right
import Submission.Work.Hormander.Weights.rpair0_dbar_right
import Submission.Work.Hormander.Weights.hessPhi_delta
import Submission.Work.Hormander.Weights.Expand
import Submission.Work.Hormander.Weights.hasCompactSupport_delta
import Submission.Work.Hormander.Weights.contDiff_delta
import Submission.Work.Hormander.Weights.contDiff_dbarCoord
import Submission.Work.Hormander.Weights.normSq0_dbarStar

/-!
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The double-sum form of the Kohn–Morrey commutator identity

This is the algebraic heart of the Kohn–Morrey identity
(`Work.Hormander.Weights.kohnMorrey_identity`).  Writing
`X_j = ∂_j f_j - f_j ∂_j φ` for the `j`-th coefficient of `∂̄*_φ f`, the double sum
`Σ_{j,k} rpair0 φ X_j X_k` of the real weighted pairings of the coefficients equals

  `Σ_{j,k} rpair0 φ (∂̄_k f_j) (∂̄_j f_k)  +  Σ_{j,k} rpair0 φ (f_j ∂_j∂̄_kφ) f_k`.

The proof is termwise.  For fixed `j`, `k`:

* `rpair0 φ X_j X_k = -rpair0 φ (∂̄_k X_j) f_k`            (`rpair0_delta_right`);
* the commutator identity `hessPhi_delta` gives
  `∂̄_k X_j = ∂_j ∂̄_k f_j - (∂̄_k f_j) ∂_j φ - f_j ∂_j∂̄_k φ`
  pointwise;
* `rpair0_delta_left` turns the first two terms of that sum back into
  `-rpair0 φ (∂̄_k f_j) (∂̄_j f_k)`.

Summing over `j` and `k` gives the claim.  The only integrability input needed for
the linearity of `rpair0` is that the integrands are continuous with compact
support, which is supplied by `integrable_rpair0_integrand`.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.Hormander.Weights

theorem rpair0_delta_sum {n : ℕ} (φ : Cn n → ℝ) (f : Form1 n) (hφ : ContDiff ℝ 2 φ)
    (hf : ∀ j, ContDiff ℝ 2 (f j)) (hfs : ∀ j, HasCompactSupport (f j)) :
    (∑ j, ∑ k, rpair0 φ (fun z => dCoord n j (f j) z - f j z * dPhi n j φ z)
        (fun z => dCoord n k (f k) z - f k z * dPhi n k φ z))
      = (∑ j, ∑ k, rpair0 φ (fun z => dbarCoord n k (f j) z)
            (fun z => dbarCoord n j (f k) z))
        + ∑ j, ∑ k, rpair0 φ (fun z => f j z * hessPhi n j k φ z) (f k) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hf1 : ∀ j : Fin n, ContDiff ℝ 1 (f j) := fun j => (hf j).of_le (by norm_num)
  have hdPhi : ∀ j : Fin n, Continuous (fun z => dPhi n j φ z) :=
    fun j => continuous_dCoord (contDiff_ofReal_comp hφ1) j
  have hhess : ∀ j k : Fin n, Continuous (fun z => hessPhi n j k φ z) := by
    intro j k
    have hφc : ContDiff ℝ 2 (fun w : Cn n => (φ w : ℂ)) :=
      (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).contDiff.comp hφ
    have h1 : ContDiff ℝ 1 (fun z => dbarPhi n k φ z) := contDiff_dbarCoord k hφc
    have h2 : Continuous (fun z => dCoord n j (fun w => dbarPhi n k φ w) z) :=
      continuous_dCoord h1 j
    simpa only [hessPhi] using h2
  have hterm : ∀ j k : Fin n,
      rpair0 φ (fun z => dCoord n j (f j) z - f j z * dPhi n j φ z)
        (fun z => dCoord n k (f k) z - f k z * dPhi n k φ z)
      = rpair0 φ (fun z => dbarCoord n k (f j) z) (fun z => dbarCoord n j (f k) z)
        + rpair0 φ (fun z => f j z * hessPhi n j k φ z) (f k) := by
    intro j k
    have hX1 : ContDiff ℝ 1 (fun z => dCoord n j (f j) z - f j z * dPhi n j φ z) :=
      contDiff_delta j (hf j) hφ
    have hsX : HasCompactSupport (fun z => dCoord n j (f j) z - f j z * dPhi n j φ z) :=
      hasCompactSupport_delta j (hfs j)
    have hY1 : ContDiff ℝ 1 (fun z => dbarCoord n k (f j) z) := contDiff_dbarCoord k (hf j)
    have hsY : HasCompactSupport (fun z => dbarCoord n k (f j) z) :=
      hasCompactSupport_dbarCoord (hfs j) k
    -- the pointwise commutator identity `∂̄_k X_j = ∂_j ∂̄_k f_j - (∂̄_k f_j)∂_jφ - f_j ∂_j∂̄_kφ`
    have hpt_pt : ∀ z : Cn n,
        dbarCoord n k (fun w => dCoord n j (f j) w - f j w * dPhi n j φ w) z
          = dCoord n j (fun w => dbarCoord n k (f j) w) z
            - dbarCoord n k (f j) z * dPhi n j φ z - f j z * hessPhi n j k φ z := by
      intro z
      have h := hessPhi_delta φ hφ f hf j k z
      linear_combination (norm := ring_nf) -h
    have hpt : (fun z => dbarCoord n k (fun w => dCoord n j (f j) w - f j w * dPhi n j φ w) z)
        = (fun z => dCoord n j (fun w => dbarCoord n k (f j) w) z
              - dbarCoord n k (f j) z * dPhi n j φ z)
          - (fun z => f j z * hessPhi n j k φ z) := by
      funext z
      rw [Pi.sub_apply]
      exact hpt_pt z
    rw [rpair0_delta_right φ hφ1 k (fun z => dCoord n j (f j) z - f j z * dPhi n j φ z)
      (f k) hX1 (hf1 k) hsX (hfs k), hpt]
    have hA1 : Integrable (fun z => ((fun z => dCoord n j (fun w => dbarCoord n k (f j) w) z
        - dbarCoord n k (f j) z * dPhi n j φ z) z * star (f k z)).re * wn n φ z) :=
      integrable_rpair0_integrand hφ1.continuous
        ((continuous_dCoord hY1 j).sub (hY1.continuous.mul (hdPhi j)))
        ((hasCompactSupport_dCoord hsY j).sub (hsY.mul_right (f' := fun z => dPhi n j φ z)))
        (hf1 k).continuous
    have hA2 : Integrable (fun z => ((fun z => f j z * hessPhi n j k φ z) z
        * star (f k z)).re * wn n φ z) :=
      integrable_rpair0_integrand hφ1.continuous
        ((hf1 j).continuous.mul (hhess j k)) ((hfs j).mul_right) (hf1 k).continuous
    rw [rpair0_sub_left hA1 hA2,
      rpair0_delta_left φ hφ1 j (fun z => dbarCoord n k (f j) z) (f k) hY1 (hf1 k) hsY (hfs k)]
    ring
  have hsum : (∑ j, ∑ k, rpair0 φ (fun z => dCoord n j (f j) z - f j z * dPhi n j φ z)
        (fun z => dCoord n k (f k) z - f k z * dPhi n k φ z))
      = ∑ j, ∑ k, (rpair0 φ (fun z => dbarCoord n k (f j) z)
            (fun z => dbarCoord n j (f k) z)
          + rpair0 φ (fun z => f j z * hessPhi n j k φ z) (f k)) := by
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    exact hterm j k
  rw [hsum]
  simp only [Finset.sum_add_distrib]

end Work.Hormander.Weights
