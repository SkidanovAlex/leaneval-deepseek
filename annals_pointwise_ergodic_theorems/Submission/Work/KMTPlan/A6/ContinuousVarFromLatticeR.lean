/-
# The continuous (`ℝ`) lacunary variational estimate from its lattice form, at every exponent `r ≥ 1`

`Work.A7Hi2.continuousVariationFromLattice` proves the *`ℝ ≤ lattice`* transfer

  `∫⁻_ℝ (V²_{n≥κ}(h n ·))^p  ≤  C · Σ'_m (V²_{n≥κ}(h n (m)))^p`

for a band-limited family `h : ℕ → SchwartzMap ℝ ℂ` (band `[-c₀,c₀]`, `c₀ < 1/2`), i.e. the
converse of the Maxwell–Stein–Wainger sampling comparison, **at the exponent `2`**.

Its proof consumes the *general-`r`* lemma
`Work.KMTAreas.A7Hi.integral_le_latticeVrSampling` (which is stated for `variationalNorm r`,
`1 ≤ r`), and the three elementary comparisons `varRhoFrom_le_varPart_shift`,
`varPart_shift_le_varRhoFrom`, `iSup_enorm_sub_le_varRhoFrom`, which are stated there at `2` and
are re-proved here at an arbitrary `r : ℝ≥0`.

This file therefore provides the missing piece of the route
`(ℝ ≤ lattice at r) + (Work.KMTAreas.A7Hi2.dilVarRealScale at r > 2) ⟹" the continuous narrowing
lacunary dilation variational estimate` of `NOTES_A6_SupDilate_SESSION.md` §2: the `r`-version of
the transfer, needed because the lattice step `dilVarRealScale` is only available for `2 < r`
(while the transfer `Work.A7Hi2.continuousVariationFromLattice` is only stated at `r = 2`).
-/
import Mathlib
import Submission.Work.BourgainPlan.Maximal.kmsz_major_defs
import Submission.Work.KMTAreas.A7Hi.integral_le_latticeVrSampling
import Submission.Work.KMTAreas.A7G.variationalBookkeeping
import Submission.Work.KMTAreas.A7Rep.SamplingKernelDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The `WithLp r`-norm of the increments of a chain equals `chainLp r`. -/
theorem ofReal_norm_toLp_eq_ofReal_chainLp (r : NNReal) (hr : 1 ≤ r) (J : ℕ) (a : ℕ → ℂ)
    (t : ℕ → ℕ) :
    ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J => a (t (i + 1)) - a (t i))‖
      = ENNReal.ofReal (Work.BourgainPlan.Maximal.chainLp (r : ℝ) J a t) := by
  rw [Work.KMTAreas.A7G.ofReal_norm_toLp_eq_sum r hr
      (F := fun i : Fin J => a (t (i + 1)) - a (t i))]
  rw [Work.KMTAreas.A7G.ofReal_chainLp_eq_sum (r : ℝ) (by positivity) J a t]
  apply congrArg (fun x : ℝ≥0∞ => x ^ (1 / (r : ℝ)))
  rw [Fin.sum_univ_eq_sum_range
    (f := fun j : ℕ => ‖a (t (j + 1)) - a (t j)‖ₑ ^ (r : ℝ)) (n := J)]

/-- **Adding a constant does not change the variation part**: the increments along a chain are
unchanged.  (General `r`; the proof only uses that the two increment vectors are equal.) -/
theorem varPart_sub_const (r : NNReal) (b : ℕ → ℂ) (c : ℂ) :
    Submission.PointwiseErgodicTheorems.varPart r (fun n : ℕ => b n - c)
      = Submission.PointwiseErgodicTheorems.varPart r b := by
  rw [Submission.PointwiseErgodicTheorems.varPart, Submission.PointwiseErgodicTheorems.varPart]
  apply le_antisymm
  · refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
    refine le_trans (le_of_eq ?_)
      (le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl)))
    rw [show (fun i : Fin J => (fun n : ℕ => b n - c) (N (i + 1))
          - (fun n : ℕ => b n - c) (N i))
        = (fun i : Fin J => b (N (i + 1)) - b (N i)) from by
      funext i
      simp only
      ring]
  · refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
    refine le_trans (le_of_eq ?_)
      (le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl)))
    rw [show (fun i : Fin J => b (N (i + 1)) - b (N i))
        = (fun i : Fin J => (fun n : ℕ => b n - c) (N (i + 1))
          - (fun n : ℕ => b n - c) (N i)) from by
      funext i
      simp only
      ring]

/-- **The supremum of the increments of a shifted sequence is bounded by the tail `r`-variation.** -/
theorem iSup_enorm_sub_le_varRhoFrom (r : NNReal) (hr : 1 ≤ r) (κ : ℕ) (a : ℕ → ℂ) :
    (⨆ n : ℕ, ‖a (n + κ) - a κ‖ₑ) ≤ Work.BourgainPlan.Maximal.varRhoFrom (r : ℝ) κ a := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by positivity
  refine iSup_le fun n => ?_
  refine (Work.BourgainPlan.Maximal.enorm_sub_le_varRho (ρ := (r : ℝ)) hr0
    (lo := κ) (hi := n + κ) (n := n + κ) (Nat.le_add_left κ n) le_rfl a).trans ?_
  exact le_iSup (fun hi => Work.BourgainPlan.Maximal.varRho (r : ℝ) κ hi a) (n + κ)

/-- **Reindexing a chain by `-κ`.**  A monotone chain with values in `[κ, hi]` becomes a chain for
the shifted sequence, so the `r`-variation in the index tail `{n ≥ κ}` is bounded by the variation
part of the shifted sequence. -/
theorem varRhoFrom_le_varPart_shift (r : NNReal) (hr : 1 ≤ r) (κ : ℕ) (a : ℕ → ℂ) :
    Work.BourgainPlan.Maximal.varRhoFrom (r : ℝ) κ a
      ≤ Submission.PointwiseErgodicTheorems.varPart r (fun n : ℕ => a (n + κ)) := by
  rw [Work.BourgainPlan.Maximal.varRhoFrom]
  refine iSup_le fun hi => ?_
  rw [Work.BourgainPlan.Maximal.varRho]
  refine iSup_le fun J => iSup_le fun t => iSup_le fun ht => iSup_le fun hb => ?_
  set N : ℕ → ℕ := fun j => t (min j J) - κ with hN
  have hNval : ∀ j : ℕ, N j + κ = t (min j J) := fun j =>
    Nat.sub_add_cancel (hb (min j J) (min_le_right _ _)).1
  have hNmono : Monotone N := by
    intro i j hij
    have h1 : t (min i J) ≤ t (min j J) := ht (min_le_min hij le_rfl)
    simp only [hN]
    exact Nat.sub_le_sub_right h1 κ
  have hchain : Work.BourgainPlan.Maximal.chainLp (r : ℝ) J (fun n : ℕ => a (n + κ)) N
      = Work.BourgainPlan.Maximal.chainLp (r : ℝ) J a t := by
    rw [Work.BourgainPlan.Maximal.chainLp, Work.BourgainPlan.Maximal.chainLp]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjJ : j + 1 ≤ J := by
      simp only [Finset.mem_range] at hj
      omega
    rw [hNval (j + 1), hNval j, min_eq_left hjJ, min_eq_left (by omega : j ≤ J)]
  calc ENNReal.ofReal (Work.BourgainPlan.Maximal.chainLp (r : ℝ) J a t)
      = ENNReal.ofReal (Work.BourgainPlan.Maximal.chainLp (r : ℝ) J
          (fun n : ℕ => a (n + κ)) N) := by rw [hchain]
    _ = ENNReal.ofReal ‖WithLp.toLp r
          (fun i : Fin J => (fun n : ℕ => a (n + κ)) (N (i + 1))
            - (fun n : ℕ => a (n + κ)) (N i))‖ :=
        (ofReal_norm_toLp_eq_ofReal_chainLp r hr J (fun n : ℕ => a (n + κ)) N).symm
    _ ≤ Submission.PointwiseErgodicTheorems.varPart r (fun n : ℕ => a (n + κ)) :=
        le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hNmono le_rfl))

/-- **Reindexing a chain by `+κ`.**  Conversely, a chain `N` for the shifted sequence gives the
chain `N + κ` in the tail `{n ≥ κ}`, so the variation part of the shifted sequence is bounded by
the tail `r`-variation. -/
theorem varPart_shift_le_varRhoFrom (r : NNReal) (hr : 1 ≤ r) (κ : ℕ) (a : ℕ → ℂ) :
    Submission.PointwiseErgodicTheorems.varPart r (fun n : ℕ => a (n + κ))
      ≤ Work.BourgainPlan.Maximal.varRhoFrom (r : ℝ) κ a := by
  rw [Submission.PointwiseErgodicTheorems.varPart]
  refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
  have ht : Monotone fun j : ℕ => N j + κ := fun i j hij => Nat.add_le_add_right (hN hij) κ
  have hb : ∀ j ≤ J, κ ≤ N j + κ ∧ N j + κ ≤ N J + κ := fun j hj =>
    ⟨Nat.le_add_left κ (N j), Nat.add_le_add_right (hN hj) κ⟩
  have hchain : Work.BourgainPlan.Maximal.chainLp (r : ℝ) J (fun n : ℕ => a (n + κ)) N
      = Work.BourgainPlan.Maximal.chainLp (r : ℝ) J a (fun j : ℕ => N j + κ) := rfl
  rw [ofReal_norm_toLp_eq_ofReal_chainLp r hr J (fun n : ℕ => a (n + κ)) N,
    hchain, Work.BourgainPlan.Maximal.varRhoFrom]
  have h1 : ENNReal.ofReal (Work.BourgainPlan.Maximal.chainLp (r : ℝ) J a (fun j : ℕ => N j + κ))
      ≤ Work.BourgainPlan.Maximal.varRho (r : ℝ) κ (N J + κ) a :=
    le_iSup_of_le J (le_iSup_of_le (fun j : ℕ => N j + κ)
      (le_iSup_of_le ht (le_iSup_of_le hb le_rfl)))
  exact h1.trans (le_iSup (fun hi => Work.BourgainPlan.Maximal.varRho (r : ℝ) κ hi a) (N J + κ))

/-- **The Fourier transform of a difference of Schwartz functions** is the difference of the
transforms, pointwise. -/
theorem fourier_sub_apply (f g : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    FourierTransform.fourier ((f - g : SchwartzMap ℝ ℂ) : ℝ → ℂ) ξ
      = FourierTransform.fourier ((f : SchwartzMap ℝ ℂ) : ℝ → ℂ) ξ
        - FourierTransform.fourier ((g : SchwartzMap ℝ ℂ) : ℝ → ℂ) ξ := by
  have h : (FourierTransform.fourier (f - g) : SchwartzMap ℝ ℂ)
      = FourierTransform.fourier f - FourierTransform.fourier g :=
    map_sub (FourierTransform.fourierₗ ℂ (SchwartzMap ℝ ℂ)) f g
  rw [← SchwartzMap.fourier_coe (f - g), ← SchwartzMap.fourier_coe f,
    ← SchwartzMap.fourier_coe g]
  rw [h]
  rfl

end

end Work.KMTPlan.A6
