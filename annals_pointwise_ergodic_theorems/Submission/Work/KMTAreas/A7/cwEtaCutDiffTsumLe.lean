import Mathlib
import Submission.Work.KMTAreas.A7.cwEtaCutDefs
import Submission.Work.KMTAreas.A7.cw_etaCut_decay
import Submission.Commons.Analysis.Fourier.poisson_summation_scaled
import Submission.Work.KMTAreas.A7.kmtEta_deriv_bounds

/-!
# The `ℓ¹`-norm of the `M`-difference of the coefficients of `η_{≤k}`

For the KMT cutoff `η_{≤k} = etaCut kmtEta k` (i.e. `η_{≤k}(θ) = η(θ / 2^k)`, with `η = kmtEta`
the paper's smooth bump) and its coefficient sequence
`cw (η_{≤k}) j = ∫ θ, η_{≤k}(θ) e(-jθ) dθ`, we prove

`∑_j ‖cw (η_{≤k}) j − cw (η_{≤k}) (j − M)‖ ≤ C · |M| · 2^k`

with a constant `C` independent of `k` and `M`.

## Proof

* **Dilation.**  The substitution `θ = 2^k u` in the defining integral shows that the coefficient
  sequence is the dilate of the fixed profile `φ = 𝓕η = kmtPhi`:
  `cw (η_{≤k}) j = 2^k · φ (2^k j)`
  (`cwEtaCutDiff_dilate`, from `cw_eq_fourierTransform` and the scaling rule `fourier_comp_div`
  for the Fourier transform).
* **Shift-difference bound.**  For a function with derivative `f' ∈ L¹`, the `ℓ¹`-norm of the
  lattice difference `j ↦ f(aj) − f(a(j−M))` is at most `|M| ‖f'‖_{L¹}`: this is
  `cwESC_tsum_shift_le`, proved below by telescoping the fundamental theorem of calculus over the
  disjoint intervals `(a k, a(k+1)]` (the `M` overlapping windows `(a(j−M), a j]` cover the line
  with multiplicity exactly `|M|`).
* Applying it to `φ` — whose derivative is `φ' = 𝓕 (v ↦ -2πi v η(v)) = kmtPhi'`
  (`kmtPhi_hasDerivAt`, of the sibling module) and which is integrable
  (`kmtPhi_prime_integrable`, from `integrable_fourier_of_contDiff_hasCompactSupport`) — and
  choosing `C = ‖φ'‖_{L¹} + 1` completes the proof.

The dilation is what produces the sharp factor `2^k |M|`; note that the trivial bound
`2 ∑_j ‖cw (η_{≤k}) j‖` is of size `2^k` for `k ≥ 0` but of size `1` as `k → -∞`.
-/

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped BigOperators FourierTransform

/-! ## The `ℓ¹`-shift lemma on the lattice `aℤ` -/

/-- Fundamental theorem of calculus: `‖f y − f x‖ ≤ ∫ x..y ‖f'‖` for `x ≤ y`. -/
private lemma cwESC_norm_sub_le_intervalIntegral_norm {f f' : ℝ → ℂ}
    (hf : ∀ x : ℝ, HasDerivAt f (f' x) x) (hint : MeasureTheory.Integrable f')
    {x y : ℝ} (hxy : x ≤ y) : ‖f y - f x‖ ≤ ∫ t in x..y, ‖f' t‖ := by
  have hFTC : ∫ t in x..y, f' t = f y - f x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hf t) hint.intervalIntegrable
  rw [← hFTC]
  exact intervalIntegral.norm_integral_le_integral_norm hxy

/-- For any finite set of indices and any shift `d`, the single steps
`‖f (a(k+d+1)) − f (a(k+d))‖` sum to at most `∫ ‖f'‖`: the intervals
`(a(k+d), a(k+d+1)]` are pairwise disjoint. -/
private lemma cwESC_finset_step_le {f f' : ℝ → ℂ} (a : ℝ) (ha : 0 < a)
    (hf : ∀ x : ℝ, HasDerivAt f (f' x) x) (hint : MeasureTheory.Integrable f')
    (d : ℤ) (t : Finset ℤ) :
    (∑ k ∈ t, ‖f (a * ((k + d + 1 : ℤ) : ℝ)) - f (a * ((k + d : ℤ) : ℝ))‖)
      ≤ ∫ x : ℝ, ‖f' x‖ := by
  have hstep : ∀ k ∈ t, ‖f (a * ((k + d + 1 : ℤ) : ℝ)) - f (a * ((k + d : ℤ) : ℝ))‖
      ≤ ∫ x in Set.Ioc (a * ((k + d : ℤ) : ℝ)) (a * ((k + d + 1 : ℤ) : ℝ)), ‖f' x‖ := by
    intro k _
    have hle : a * ((k + d : ℤ) : ℝ) ≤ a * ((k + d + 1 : ℤ) : ℝ) := by
      have h : ((k + d : ℤ) : ℝ) ≤ ((k + d + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact mul_le_mul_of_nonneg_left h ha.le
    rw [← intervalIntegral.integral_of_le hle]
    exact cwESC_norm_sub_le_intervalIntegral_norm hf hint hle
  have hdisj : (t : Set ℤ).Pairwise (Function.onFun Disjoint
      (fun k => Set.Ioc (a * ((k + d : ℤ) : ℝ)) (a * ((k + d + 1 : ℤ) : ℝ)))) := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with h | h
    · have h1 : i + d + 1 ≤ j + d := by omega
      have h2 : a * ((i + d + 1 : ℤ) : ℝ) ≤ a * ((j + d : ℤ) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast h1) ha.le
      exact Set.Ioc_disjoint_Ioc_of_le h2
    · have h1 : j + d + 1 ≤ i + d := by omega
      have h2 : a * ((j + d + 1 : ℤ) : ℝ) ≤ a * ((i + d : ℤ) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast h1) ha.le
      exact (Set.Ioc_disjoint_Ioc_of_le h2).symm
  have hunion :
      (∑ k ∈ t, ∫ x in Set.Ioc (a * ((k + d : ℤ) : ℝ)) (a * ((k + d + 1 : ℤ) : ℝ)), ‖f' x‖)
      = ∫ x in ⋃ k ∈ t, Set.Ioc (a * ((k + d : ℤ) : ℝ)) (a * ((k + d + 1 : ℤ) : ℝ)), ‖f' x‖ :=
    (integral_biUnion_finset t (fun i _ => measurableSet_Ioc) hdisj
      (fun i _ => hint.norm.integrableOn)).symm
  calc (∑ k ∈ t, ‖f (a * ((k + d + 1 : ℤ) : ℝ)) - f (a * ((k + d : ℤ) : ℝ))‖)
      ≤ ∑ k ∈ t, ∫ x in Set.Ioc (a * ((k + d : ℤ) : ℝ)) (a * ((k + d + 1 : ℤ) : ℝ)), ‖f' x‖ :=
        Finset.sum_le_sum hstep
    _ = ∫ x in ⋃ k ∈ t, Set.Ioc (a * ((k + d : ℤ) : ℝ)) (a * ((k + d + 1 : ℤ) : ℝ)), ‖f' x‖ :=
        hunion
    _ ≤ ∫ x : ℝ, ‖f' x‖ :=
        setIntegral_le_integral hint.norm (Filter.Eventually.of_forall fun x => norm_nonneg _)

/-- **The `ℓ¹`-shift lemma on a finite index set.**  For every nonnegative integer `N` and every
pair of shifts `c, d` with `c - d = N`, the `N`-step differences sum to at most `N ∫ ‖f'‖`.
(Proved by induction on `N`, splitting off one step and using `cwESC_finset_step_le`.) -/
private lemma cwESC_finset_pair_le {f f' : ℝ → ℂ} (a : ℝ) (ha : 0 < a)
    (hf : ∀ x : ℝ, HasDerivAt f (f' x) x) (hint : MeasureTheory.Integrable f') :
    ∀ (N : ℤ), 0 ≤ N → ∀ (c d : ℤ), c - d = N → ∀ s : Finset ℤ,
      (∑ j ∈ s, ‖f (a * ((j + c : ℤ) : ℝ)) - f (a * ((j + d : ℤ) : ℝ))‖)
        ≤ |(N : ℝ)| * ∫ x : ℝ, ‖f' x‖ := by
  intro N hN
  refine Int.leInduction (m := 0)
    (motive := fun n _ => ∀ (c d : ℤ), c - d = n → ∀ s : Finset ℤ,
      (∑ j ∈ s, ‖f (a * ((j + c : ℤ) : ℝ)) - f (a * ((j + d : ℤ) : ℝ))‖)
        ≤ |(n : ℝ)| * ∫ x : ℝ, ‖f' x‖) ?_ ?_ N hN
  · -- `N = 0`: equal shifts, all differences vanish
    intro c d hcd s
    have hcd' : c = d := sub_eq_zero.mp hcd
    have hzero : (∑ j ∈ s, ‖f (a * ((j + c : ℤ) : ℝ)) - f (a * ((j + d : ℤ) : ℝ))‖) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [hcd', sub_self, norm_zero]
    rw [hzero]
    simp
  · -- the induction step: split off one step, `|n| * B + B = |n + 1| * B`
    intro n hn ih c d hcd s
    obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∫ x : ℝ, ‖f' x‖ := ⟨_, rfl⟩
    have htri : (∑ j ∈ s, ‖f (a * ((j + c : ℤ) : ℝ)) - f (a * ((j + d : ℤ) : ℝ))‖)
        ≤ (∑ j ∈ s, ‖f (a * ((j + c : ℤ) : ℝ)) - f (a * ((j + (c - 1) : ℤ) : ℝ))‖)
          + (∑ j ∈ s, ‖f (a * ((j + (c - 1) : ℤ) : ℝ)) - f (a * ((j + d : ℤ) : ℝ))‖) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun j _ => ?_)
      calc ‖f (a * ((j + c : ℤ) : ℝ)) - f (a * ((j + d : ℤ) : ℝ))‖
          = dist (f (a * ((j + c : ℤ) : ℝ))) (f (a * ((j + d : ℤ) : ℝ))) := by
            rw [dist_eq_norm]
        _ ≤ dist (f (a * ((j + c : ℤ) : ℝ))) (f (a * ((j + (c - 1) : ℤ) : ℝ)))
              + dist (f (a * ((j + (c - 1) : ℤ) : ℝ))) (f (a * ((j + d : ℤ) : ℝ))) :=
            dist_triangle _ _ _
        _ = ‖f (a * ((j + c : ℤ) : ℝ)) - f (a * ((j + (c - 1) : ℤ) : ℝ))‖
              + ‖f (a * ((j + (c - 1) : ℤ) : ℝ)) - f (a * ((j + d : ℤ) : ℝ))‖ := by
            rw [dist_eq_norm, dist_eq_norm]
    have h1 : (∑ j ∈ s, ‖f (a * ((j + (c - 1) : ℤ) : ℝ)) - f (a * ((j + d : ℤ) : ℝ))‖)
        ≤ |(n : ℝ)| * B := by
      have h := ih (c - 1) d (by omega) s
      rwa [← hB] at h
    have h2 : (∑ j ∈ s, ‖f (a * ((j + c : ℤ) : ℝ)) - f (a * ((j + (c - 1) : ℤ) : ℝ))‖) ≤ B := by
      have h := cwESC_finset_step_le a ha hf hint (c - 1) s
      rw [← hB] at h
      refine le_trans (le_of_eq ?_) h
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [show (((j + (c - 1) + 1 : ℤ)) : ℝ) = ((j + c : ℤ) : ℝ) from by push_cast; ring]
    have hR : B + |(n : ℝ)| * B = |(((n + 1 : ℤ)) : ℝ)| * B := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      rw [show (((n + 1 : ℤ)) : ℝ) = (n : ℝ) + 1 from by push_cast; ring,
        abs_of_nonneg hn0, abs_of_nonneg (by linarith)]
      ring
    rw [← hB]
    calc (∑ j ∈ s, ‖f (a * ((j + c : ℤ) : ℝ)) - f (a * ((j + d : ℤ) : ℝ))‖)
        ≤ (∑ j ∈ s, ‖f (a * ((j + c : ℤ) : ℝ)) - f (a * ((j + (c - 1) : ℤ) : ℝ))‖)
          + (∑ j ∈ s, ‖f (a * ((j + (c - 1) : ℤ) : ℝ)) - f (a * ((j + d : ℤ) : ℝ))‖) := htri
      _ ≤ B + |(n : ℝ)| * B := add_le_add h2 h1
      _ = |(((n + 1 : ℤ)) : ℝ)| * B := hR

/-- **The `ℓ¹`-shift lemma**, all `M : ℤ` (in the finite-set form). -/
private lemma cwESC_finset_shift_le {f f' : ℝ → ℂ} (a : ℝ) (ha : 0 < a)
    (hf : ∀ x : ℝ, HasDerivAt f (f' x) x) (hint : MeasureTheory.Integrable f') (M : ℤ)
    (s : Finset ℤ) :
    (∑ j ∈ s, ‖f (a * (j : ℝ)) - f (a * ((j - M : ℤ) : ℝ))‖)
      ≤ |(M : ℝ)| * ∫ x : ℝ, ‖f' x‖ := by
  rcases lt_or_ge 0 M with hM | hM
  · have h := cwESC_finset_pair_le a ha hf hint M hM.le 0 (-M) (by ring) s
    have hgoal : (∑ j ∈ s, ‖f (a * ((j : ℤ) : ℝ)) - f (a * ((j - M : ℤ) : ℝ))‖)
        = ∑ j ∈ s, ‖f (a * ((j + 0 : ℤ) : ℝ)) - f (a * ((j + (-M) : ℤ) : ℝ))‖ := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [show (((j + (0 : ℤ) : ℤ)) : ℝ) = ((j : ℤ) : ℝ) from by push_cast; ring,
        show (((j + (-M) : ℤ)) : ℝ) = ((j - M : ℤ) : ℝ) from by push_cast; ring]
    rw [hgoal]
    exact h
  · have hM' : 0 ≤ -M := by omega
    have h := cwESC_finset_pair_le a ha hf hint (-M) hM' (-M) 0 (by ring) s
    have hgoal : (∑ j ∈ s, ‖f (a * ((j : ℤ) : ℝ)) - f (a * ((j - M : ℤ) : ℝ))‖)
        = ∑ j ∈ s, ‖f (a * ((j + (-M) : ℤ) : ℝ)) - f (a * ((j + 0 : ℤ) : ℝ))‖ := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [norm_sub_rev,
        show (((j + (0 : ℤ) : ℤ)) : ℝ) = ((j : ℤ) : ℝ) from by push_cast; ring,
        show (((j + (-M) : ℤ)) : ℝ) = ((j - M : ℤ) : ℝ) from by push_cast; ring]
    rw [hgoal]
    refine le_trans h ?_
    rw [Int.cast_neg, abs_neg]

/-- **The `ℓ¹`-shift lemma**, in the summed form. -/
private lemma cwESC_tsum_shift_le {f f' : ℝ → ℂ} (a : ℝ) (ha : 0 < a)
    (hf : ∀ x : ℝ, HasDerivAt f (f' x) x) (hint : MeasureTheory.Integrable f') (M : ℤ) :
    (∑' j : ℤ, ‖f (a * (j : ℝ)) - f (a * ((j - M : ℤ) : ℝ))‖)
      ≤ |(M : ℝ)| * ∫ x : ℝ, ‖f' x‖ :=
  Real.tsum_le_of_sum_le (fun j : ℤ => norm_nonneg _)
    (fun s => cwESC_finset_shift_le a ha hf hint M s)

/-! ## The dilate identity for the coefficients of `η_{≤k}` -/

/-- **The coefficient sequence of the rescaled cutoff is the dilate of the profile `φ = 𝓕η`.**
The substitution `θ = 2^k u` in `cw (η_{≤k}) j = ∫ θ, η(θ/2^k) e(-jθ) dθ` gives
`2^k · 𝓕η (2^k j)`. -/
lemma cwEtaCutDiff_dilate (k : ℤ) (j : ℤ) :
    cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) j
      = ((2:ℂ)^k) * kmtPhi ((2:ℝ)^k * (j:ℝ)) := by
  rw [cw_eq_fourierTransform, kmtPhi]
  have ht : (0:ℝ) < (2:ℝ)^k := zpow_pos (by norm_num) k
  have hfun : Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k
      = fun x : ℝ => Work.KMTContract.kmtEta (x / (2:ℝ)^k) := by
    funext x; exact (Work.KMTContract.etaCutRegular k).2.1 x
  rw [hfun, Commons.Analysis.Fourier.fourier_comp_div Work.KMTContract.kmtEta ht (j:ℝ)]
  congr 1
  · exact (by push_cast; ring : Complex.ofReal ((2:ℝ)^k) = (2:ℂ)^k)
  · rw [mul_comm]

/-- The `M`-difference of the coefficients is the dilate of the difference of the profile. -/
lemma cwEtaCutDiff_diff_eq (k M j : ℤ) :
    cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) j
        - cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) (j - M)
      = ((2:ℂ)^k) * (kmtPhi ((2:ℝ)^k * (j:ℝ))
          - kmtPhi ((2:ℝ)^k * (((j - M : ℤ)) : ℝ))) := by
  rw [cwEtaCutDiff_dilate k j, cwEtaCutDiff_dilate k (j - M), mul_sub]

/-- Norm form of the same identity: the factor `2^k` comes out of the norm. -/
lemma cwEtaCutDiff_norm_eq (k M j : ℤ) :
    ‖cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) j
        - cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) (j - M)‖
      = (2:ℝ)^k * ‖kmtPhi ((2:ℝ)^k * (j:ℝ))
          - kmtPhi ((2:ℝ)^k * (((j - M : ℤ)) : ℝ))‖ := by
  rw [cwEtaCutDiff_diff_eq, norm_mul, norm_zpow]
  norm_num

end Work.KMTAreas.A7
