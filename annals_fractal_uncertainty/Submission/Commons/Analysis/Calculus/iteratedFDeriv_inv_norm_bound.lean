import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.GDelta.MetrizableSpace

namespace Commons.Analysis.Calculus

open scoped ContDiff
open Set Metric

/-- **Homogeneity (scaling) estimate for `y ↦ ‖y‖⁻¹`.**
On a real inner product space, the iterated Fréchet derivatives of `y ↦ ‖y‖⁻¹` rescale as
`‖D^i f y‖ ≤ c^{i+1} ‖D^i f (c • y)‖` for every `c > 0` and `y ≠ 0`. -/
theorem norm_iteratedFDeriv_inv_norm_smul_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (i : ℕ) {c : ℝ} (hc : 0 < c) {y : E} (hy : y ≠ 0) :
    ‖iteratedFDeriv ℝ i (fun z : E => (‖z‖)⁻¹) y‖
      ≤ c ^ (i + 1) * ‖iteratedFDeriv ℝ i (fun z : E => (‖z‖)⁻¹) (c • y)‖ := by
  set f : E → ℝ := fun z => (‖z‖)⁻¹ with hfdef
  set s : Set E := {0}ᶜ with hsdef
  have hsopen : IsOpen s := isOpen_compl_singleton
  have hs : UniqueDiffOn ℝ s := hsopen.uniqueDiffOn
  have hf : ContDiffOn ℝ ⊤ f s := by
    intro z hz
    simp only [hsdef, mem_compl_iff, mem_singleton_iff] at hz
    exact ((contDiffAt_norm ℝ hz).inv (by simpa using hz)).contDiffWithinAt
  set g : E →L[ℝ] E := c • (1 : E →L[ℝ] E) with hgdef
  have hgapp : ∀ z : E, g z = c • z := by intro z; simp [g]
  have hgnorm : ‖g‖ ≤ c := by
    simp only [hgdef, norm_smul, Real.norm_of_nonneg hc.le]
    calc c * ‖(1 : E →L[ℝ] E)‖ ≤ c * 1 := by
          gcongr; exact ContinuousLinearMap.norm_id_le
      _ = c := mul_one c
  have hgne : ∀ z : E, g z = 0 ↔ z = 0 := by
    intro z; rw [hgapp z, smul_eq_zero]
    exact ⟨fun h => h.resolve_left (ne_of_gt hc), fun h => Or.inr h⟩
  have hpre : g ⁻¹' s = s := by
    ext z; simp only [mem_preimage, hsdef, mem_compl_iff, mem_singleton_iff, hgne z]
  have hy_s : y ∈ s := by simpa [hsdef] using hy
  have hgy_s : g y ∈ s := by
    simp only [hsdef, mem_compl_iff, mem_singleton_iff]
    exact fun h => hy ((hgne y).mp h)
  have hcr := g.iteratedFDerivWithin_comp_right (f := f) hf hs
      (by rw [hpre]; exact hs) (x := y) hgy_s (i := i) le_top
  have hcongr : (f ∘ g) = fun z => c⁻¹ • f z := by
    funext z
    simp only [Function.comp_apply, hgapp z, hfdef]
    rw [norm_smul, Real.norm_of_nonneg hc.le, smul_eq_mul, mul_inv]
  have hf_i : ContDiffOn ℝ (i : ℕ∞ω) f s := hf.of_le le_top
  have hlhs : iteratedFDerivWithin ℝ i (f ∘ g) (g ⁻¹' s) y
      = c⁻¹ • iteratedFDerivWithin ℝ i f s y := by
    rw [hpre, hcongr]
    exact iteratedFDerivWithin_const_smul_apply (i := i) (a := c⁻¹) (f := f)
      (hf_i y hy_s) hs hy_s
  have hE1 : c⁻¹ • iteratedFDerivWithin ℝ i f s y
      = (iteratedFDerivWithin ℝ i f s (g y)).compContinuousLinearMap (fun _ => g) :=
    hlhs.symm.trans hcr
  have hwy : iteratedFDerivWithin ℝ i f s y = iteratedFDeriv ℝ i f y :=
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) i hsopen hy_s
  have hwgy : iteratedFDerivWithin ℝ i f s (g y) = iteratedFDeriv ℝ i f (g y) :=
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) i hsopen hgy_s
  rw [hwy, hwgy, hgapp y] at hE1
  have hnorm_le : c⁻¹ * ‖iteratedFDeriv ℝ i f y‖
      ≤ ‖iteratedFDeriv ℝ i f (c • y)‖ * c ^ i := by
    calc c⁻¹ * ‖iteratedFDeriv ℝ i f y‖
        = ‖c⁻¹ • iteratedFDeriv ℝ i f y‖ := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le)]
      _ = ‖(iteratedFDeriv ℝ i f (c • y)).compContinuousLinearMap (fun _ => g)‖ := by
          rw [hE1]
      _ ≤ ‖iteratedFDeriv ℝ i f (c • y)‖ * ∏ _ : Fin i, ‖g‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ ‖iteratedFDeriv ℝ i f (c • y)‖ * c ^ i := by
          gcongr
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          exact pow_le_pow_left₀ (norm_nonneg _) hgnorm i
  have h1 : c * (c⁻¹ * ‖iteratedFDeriv ℝ i f y‖)
      ≤ c * (‖iteratedFDeriv ℝ i f (c • y)‖ * c ^ i) :=
    mul_le_mul_of_nonneg_left hnorm_le hc.le
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul] at h1
  calc ‖iteratedFDeriv ℝ i f y‖
      ≤ c * (‖iteratedFDeriv ℝ i f (c • y)‖ * c ^ i) := h1
    _ = c ^ (i + 1) * ‖iteratedFDeriv ℝ i f (c • y)‖ := by
        rw [pow_succ']; ring

/-- **Uniform bound on the unit sphere.**  For every order `i` the iterated derivative of
`y ↦ ‖y‖⁻¹` is bounded on the unit sphere by a nonnegative constant. -/
theorem exists_iteratedFDeriv_inv_norm_sphere_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [ProperSpace E] (i : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E, ‖u‖ = 1 →
      ‖iteratedFDeriv ℝ i (fun z : E => (‖z‖)⁻¹) u‖ ≤ K := by
  set f : E → ℝ := fun z => (‖z‖)⁻¹ with hfdef
  have hcont : ContinuousOn (fun u : E => ‖iteratedFDeriv ℝ i f u‖) (sphere 0 1) := by
    intro u hu
    rw [mem_sphere, dist_zero_right] at hu
    have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu; norm_num at hu
    have hcd : ContDiffAt ℝ ⊤ f u :=
      (contDiffAt_norm ℝ hu0).inv (by rw [hu]; norm_num)
    exact (hcd.continuousAt_iteratedFDeriv le_top).norm.continuousWithinAt
  obtain ⟨K, hK⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn hcont
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro u hu
  have hu_sphere : u ∈ sphere (0 : E) 1 := by rw [mem_sphere, dist_zero_right]; exact hu
  have h1 := hK u hu_sphere
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h1
  exact h1.trans (le_max_left _ _)

/-- Bound on the iterated Fréchet derivatives of `y ↦ ‖y‖⁻¹` in `ℝᵈ`. -/
theorem iteratedFDeriv_inv_norm_bound {d : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : EuclideanSpace ℝ (Fin d)) (n : ℕ), n ≤ 3 → x ≠ 0 →
      ‖iteratedFDeriv ℝ n (fun y : EuclideanSpace ℝ (Fin d) => (‖y‖)⁻¹) x‖
        ≤ C * (‖x‖ ^ (n + 1))⁻¹ := by
  have hKi : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
      ‖iteratedFDeriv ℝ i (fun z : EuclideanSpace ℝ (Fin d) => (‖z‖)⁻¹) u‖ ≤ K :=
    fun i => exists_iteratedFDeriv_inv_norm_sphere_bound i
  obtain ⟨K0, hK0nn, hK0⟩ := hKi 0
  obtain ⟨K1, hK1nn, hK1⟩ := hKi 1
  obtain ⟨K2, hK2nn, hK2⟩ := hKi 2
  obtain ⟨K3, hK3nn, hK3⟩ := hKi 3
  refine ⟨K0 + K1 + K2 + K3 + 1, by linarith, ?_⟩
  intro x n hn hx
  have hrpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set u : EuclideanSpace ℝ (Fin d) := (‖x‖)⁻¹ • x with hudef
  have hun : ‖u‖ = 1 := by
    rw [hudef, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hrpos.le),
      inv_mul_cancel₀ hrpos.ne']
  have hscale := norm_iteratedFDeriv_inv_norm_smul_le (E := EuclideanSpace ℝ (Fin d)) n
    (inv_pos.mpr hrpos) hx
  have hCn : ‖iteratedFDeriv ℝ n (fun z : EuclideanSpace ℝ (Fin d) => (‖z‖)⁻¹) u‖
      ≤ K0 + K1 + K2 + K3 + 1 := by
    interval_cases n
    · exact (hK0 u hun).trans (by linarith)
    · exact (hK1 u hun).trans (by linarith)
    · exact (hK2 u hun).trans (by linarith)
    · exact (hK3 u hun).trans (by linarith)
  calc ‖iteratedFDeriv ℝ n (fun z : EuclideanSpace ℝ (Fin d) => (‖z‖)⁻¹) x‖
      ≤ (‖x‖⁻¹) ^ (n + 1) *
          ‖iteratedFDeriv ℝ n (fun z : EuclideanSpace ℝ (Fin d) => (‖z‖)⁻¹) u‖ := by
        rw [hudef]; exact hscale
    _ ≤ (‖x‖⁻¹) ^ (n + 1) * (K0 + K1 + K2 + K3 + 1) :=
        mul_le_mul_of_nonneg_left hCn (pow_nonneg (inv_nonneg.mpr hrpos.le) _)
    _ = (K0 + K1 + K2 + K3 + 1) * (‖x‖ ^ (n + 1))⁻¹ := by
        rw [inv_pow]; ring

end Commons.Analysis.Calculus