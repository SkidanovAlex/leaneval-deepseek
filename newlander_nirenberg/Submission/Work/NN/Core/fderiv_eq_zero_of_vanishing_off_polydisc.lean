import Mathlib
import Submission.Work.NN.Core.CnPert

/-!
# The derivative vanishes at every point where the function already vanishes

Let `χ : ℂⁿ → ℂ` be `C¹` and vanish outside the open polydisc of radii `ρ` (i.e. on every point
having a coordinate of modulus `≥ ρ j`).  Then `dχ` vanishes at every such point as well.

The point is that at a point `z` with `ρ j ≤ ‖z j‖`, for **every** direction `v` one can find a
sequence `t_k → 0`, `t_k ≠ 0`, with `z + t_k v` still off the polydisc: the parabola
`t ↦ ‖z j + t v j‖² = ‖z j‖² + t (2⟪z j, v j⟫ + t ‖v j‖²)` stays at least `‖z j‖` on one of the two
halves of the real line.  Along that sequence the difference quotient of `χ` in the direction `v`
is constantly `0`, and since it converges (to `dχ z v`) the limit is `0`.
-/

namespace Work.NN.Core

open Filter
open scoped Topology

/-- The squared modulus of `a + t b` expanded as an upward parabola in `t`. -/
private lemma norm_add_smul_sq {n : ℕ} (z v : Cn n) (j : Fin n) (t : ℝ) :
    ‖z j + t • v j‖ ^ 2
      = ‖z j‖ ^ 2 + t * (2 * inner ℝ (z j) (v j) + t * ‖v j‖^2) := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- If the parabola stays non-negative at `t`, then `‖z j‖ ≤ ‖z j + t • v j‖`. -/
private lemma norm_le_norm_add_smul {n : ℕ} (z v : Cn n) (j : Fin n) (t : ℝ)
    (hmul : 0 ≤ t * (2 * inner ℝ (z j) (v j) + t * ‖v j‖^2)) :
    ‖z j‖ ≤ ‖z j + t • v j‖ := by
  have h := norm_add_smul_sq z v j t
  have h2 : ‖z j‖ ^ 2 ≤ ‖z j + t • v j‖ ^ 2 := by rw [h]; linarith
  nlinarith [norm_nonneg (z j), norm_nonneg (z j + t • v j)]

/-- For every direction `v` there is a sequence `u k → 0` (`u k ≠ 0`) with `ρ j ≤ ‖(z + u k • v) j‖`
as soon as `ρ j ≤ ‖z j‖`. -/
private lemma exists_seq_norm_ge {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n}
    {z : Cn n} (hzj : ρ j ≤ ‖z j‖) (v : Cn n) :
    ∃ u : ℕ → ℝ, Tendsto u atTop (𝓝[≠] (0:ℝ)) ∧ ∀ k, ρ j ≤ ‖(z + u k • v) j‖ := by
  have hne_inv : ∀ k : ℕ, (((k:ℝ)+1)⁻¹ : ℝ) ≠ 0 := fun k => inv_ne_zero (by positivity)
  have hmem : ∀ᶠ k : ℕ in atTop, (((k:ℝ)+1)⁻¹ : ℝ) ∈ ({0}ᶜ : Set ℝ) :=
    Eventually.of_forall (fun k => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact hne_inv k)
  have hmem' : ∀ᶠ k : ℕ in atTop, (-(((k:ℝ)+1)⁻¹) : ℝ) ∈ ({0}ᶜ : Set ℝ) :=
    Eventually.of_forall (fun k => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact neg_ne_zero.mpr (hne_inv k))
  have hbase : Tendsto (fun k : ℕ => (((k:ℝ)+1)⁻¹ : ℝ)) atTop (𝓝 (0:ℝ)) := by
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  by_cases hb : v j = 0
  · refine ⟨fun k => ((k:ℝ)+1)⁻¹, ?_, ?_⟩
    · exact tendsto_nhdsWithin_iff.mpr ⟨hbase, hmem⟩
    · intro k
      have h1 : (z + ((k:ℝ)+1)⁻¹ • v) j = z j := by simp [hb]
      rw [h1]; exact hzj
  · by_cases hI : 0 ≤ inner ℝ (z j) (v j)
    · refine ⟨fun k => ((k:ℝ)+1)⁻¹, ?_, ?_⟩
      · exact tendsto_nhdsWithin_iff.mpr ⟨hbase, hmem⟩
      · intro k
        have ht : (0:ℝ) < ((k:ℝ)+1)⁻¹ := by positivity
        have hq : (0:ℝ) ≤ ‖v j‖^2 := sq_nonneg _
        have hnn : 0 ≤ ((k:ℝ)+1)⁻¹ * (2 * inner ℝ (z j) (v j) + ((k:ℝ)+1)⁻¹ * ‖v j‖^2) := by
          apply mul_nonneg ht.le
          have : 0 ≤ ((k:ℝ)+1)⁻¹ * ‖v j‖^2 := mul_nonneg ht.le hq
          linarith
        have hkey := norm_le_norm_add_smul z v j ((k:ℝ)+1)⁻¹ hnn
        rw [show (z + ((k:ℝ)+1)⁻¹ • v) j = z j + ((k:ℝ)+1)⁻¹ • v j from by simp]
        exact le_trans hzj hkey
    · have hIneg : inner ℝ (z j) (v j) < 0 := not_le.mp hI
      refine ⟨fun k => -((k:ℝ)+1)⁻¹, ?_, ?_⟩
      · refine tendsto_nhdsWithin_iff.mpr ⟨?_, hmem'⟩
        simpa using hbase.neg
      · intro k
        have hspos : (0:ℝ) < ((k:ℝ)+1)⁻¹ := by positivity
        have hq : (0:ℝ) ≤ ‖v j‖^2 := sq_nonneg _
        have hEq : (-((k:ℝ)+1)⁻¹) * (2 * inner ℝ (z j) (v j) + (-((k:ℝ)+1)⁻¹) * ‖v j‖^2)
            = ((k:ℝ)+1)⁻¹ * ((((k:ℝ)+1)⁻¹) * ‖v j‖^2 - 2 * inner ℝ (z j) (v j)) := by ring
        have hnn : 0 ≤ (-((k:ℝ)+1)⁻¹)
            * (2 * inner ℝ (z j) (v j) + (-((k:ℝ)+1)⁻¹) * ‖v j‖^2) := by
          rw [hEq]
          apply mul_nonneg hspos.le
          have : 0 ≤ ((k:ℝ)+1)⁻¹ * ‖v j‖^2 := mul_nonneg hspos.le hq
          linarith [hIneg]
        have hkey := norm_le_norm_add_smul z v j (-((k:ℝ)+1)⁻¹) hnn
        rw [show (z + (-((k:ℝ)+1)⁻¹) • v) j = z j + (-((k:ℝ)+1)⁻¹) • v j from by simp]
        exact le_trans hzj hkey

lemma fderiv_eq_zero_of_vanishing_off_polydisc {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {χ : Work.NN.Core.Cn n → ℂ} (hχ : ContDiff ℝ 1 χ)
    (hχsub : ∀ z, (∃ j, ρ j ≤ ‖z j‖) → χ z = 0) :
    ∀ z, (∃ j, ρ j ≤ ‖z j‖) → fderiv ℝ χ z = 0 := by
  have _hρ := hρ
  intro z hz
  obtain ⟨j, hzj⟩ := hz
  have hz0 : χ z = 0 := hχsub z ⟨j, hzj⟩
  have hfd : HasFDerivAt χ (fderiv ℝ χ z) z :=
    (hχ.differentiable_one.differentiableAt).hasFDerivAt
  apply ContinuousLinearMap.ext
  intro v
  show fderiv ℝ χ z v = 0
  obtain ⟨u, hu_tendsto, hu_norm⟩ := exists_seq_norm_ge hzj v
  set γ : ℝ → Cn n := fun t => z + t • v with hγ
  have hγ0 : γ 0 = z := by simp [hγ]
  have hγderiv : HasDerivAt γ v 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).smul_const v
    simpa [hγ] using h1.const_add z
  have hfd' : HasFDerivAt χ (fderiv ℝ χ z) (γ 0) := by rw [hγ0]; exact hfd
  have hcomp : HasDerivAt (χ ∘ γ) (fderiv ℝ χ z v) 0 :=
    HasFDerivAt.comp_hasDerivAt (f := γ) (f' := v) (x := 0) hfd' hγderiv
  set S : ℝ → ℂ := fun t => t⁻¹ • ((χ ∘ γ) (0 + t) - (χ ∘ γ) 0) with hS
  have hslope : Tendsto S (𝓝[≠] (0:ℝ)) (𝓝 (fderiv ℝ χ z v)) := by
    simpa [hS] using hcomp.tendsto_slope_zero
  have hk : ∀ k : ℕ, S (u k) = 0 := by
    intro k
    have h1 : (χ ∘ γ) (0 + u k) = 0 := by
      have hsub : ∃ j', ρ j' ≤ ‖(z + u k • v) j'‖ := ⟨j, hu_norm k⟩
      have := hχsub (z + u k • v) hsub
      simpa [hγ] using this
    have h2 : (χ ∘ γ) 0 = 0 := by simpa [hγ] using hz0
    have hSval : S (u k) = (u k)⁻¹ • ((χ ∘ γ) (0 + u k) - (χ ∘ γ) 0) := by
      rw [hS]
    rw [hSval, h1, h2, sub_zero, smul_zero]
  have hlim : Tendsto (S ∘ u) atTop (𝓝 (fderiv ℝ χ z v)) := hslope.comp hu_tendsto
  have hlim0 : Tendsto (S ∘ u) atTop (𝓝 (0:ℂ)) := by
    rw [show S ∘ u = fun _ => (0:ℂ) from funext hk]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hlim0

end Work.NN.Core
