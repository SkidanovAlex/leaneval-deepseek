import Mathlib
import Submission.Work.Embedding.uniform_lower_bound_fderiv

namespace Work.Drive.EpsForm

/-- The Hessian of the perturbed function `q ↦ f q + t * g q` is the corresponding linear
perturbation of the Hessian of `f`. -/
private lemma fderiv_hessian (f g : ℝ × ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (t : ℝ) (p : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => f q + t * g q)) p
      = fderiv ℝ (fderiv ℝ f) p + t • fderiv ℝ (fderiv ℝ g) p := by
  have h1 : fderiv ℝ (fun y : ℝ × ℝ => f y + t * g y)
      = fun y => fderiv ℝ f y + t • fderiv ℝ g y := by
    funext y
    rw [show (fun y : ℝ × ℝ => f y + t * g y) = f + (fun y => t * g y) from rfl]
    rw [fderiv_add ((hf.differentiable (by norm_num)) y)
      (((hg.differentiable (by norm_num)) y).const_mul t)]
    rw [fderiv_const_mul ((hg.differentiable (by norm_num)) y) t]
  rw [h1]
  have hdF : DifferentiableAt ℝ (fderiv ℝ f) p :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) p
  have hdG : DifferentiableAt ℝ (fderiv ℝ g) p :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) p
  rw [show (fun y : ℝ × ℝ => fderiv ℝ f y + t • fderiv ℝ g y)
        = fderiv ℝ f + t • fderiv ℝ g from rfl]
  rw [fderiv_add hdF (hdG.const_smul t), fderiv_const_smul hdG t]

/-- **One-point version.** At a point where the Hessian of `f` is injective, the Hessians of the
perturbed functions `q ↦ f q + t * g q` are injective at all nearby points, for all small `t`. -/
private lemma injective_perturb_nhds (f g : ℝ × ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (x : ℝ × ℝ)
    (hx : Function.Injective (fderiv ℝ (fderiv ℝ f) x)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (t : ℝ) (p : ℝ × ℝ), |t| < δ → ‖p - x‖ < δ →
      Function.Injective (fderiv ℝ (fderiv ℝ f) p + t • fderiv ℝ (fderiv ℝ g) p) := by
  classical
  -- A uniform lower bound for the injective Hessian of `f` at `x`.
  obtain ⟨κ, hκpos, hκ⟩ :=
    Work.Embedding.uniform_lower_bound_fderiv (E := ℝ × ℝ) (F := (ℝ × ℝ) →L[ℝ] ℝ)
      (ψ := fderiv ℝ f) (s := {x}) isCompact_singleton (Set.singleton_nonempty x)
      (fun u _ => (hf.contDiffAt (x := u)).fderiv_right (m := 1) (by norm_num))
      (fun u hu => by rw [Set.mem_singleton_iff.mp hu]; exact hx)
  -- Continuity of the two Hessians.
  have hAc : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hBc : Continuous (fderiv ℝ (fderiv ℝ g)) :=
    (hg.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :=
    (Metric.continuousAt_iff (f := fderiv ℝ (fderiv ℝ f)) (a := x)).mp
      hAc.continuousAt (κ / 2) (by linarith)
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ :=
    (Metric.continuousAt_iff (f := fderiv ℝ (fderiv ℝ g)) (a := x)).mp
      hBc.continuousAt 1 one_pos
  set M : ℝ := ‖fderiv ℝ (fderiv ℝ g) x‖ + 1 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  refine ⟨min δ₁ (min δ₂ (κ / (2 * M))), ?_, ?_⟩
  · exact lt_min hδ₁pos (lt_min hδ₂pos (by positivity))
  · intro t p ht hp
    have hp₁ : ‖p - x‖ < δ₁ := lt_of_lt_of_le hp (min_le_left _ _)
    have hp₂ : ‖p - x‖ < δ₂ :=
      lt_of_lt_of_le hp (le_trans (min_le_right _ _) (min_le_left _ _))
    have ht₂ : |t| < κ / (2 * M) :=
      lt_of_lt_of_le ht (le_trans (min_le_right _ _) (min_le_right _ _))
    -- How far the two Hessians move.
    have hAp : ‖fderiv ℝ (fderiv ℝ f) p - fderiv ℝ (fderiv ℝ f) x‖ < κ / 2 := by
      have h := hδ₁ (x := p) (by rw [dist_eq_norm p x]; exact hp₁)
      rw [dist_eq_norm (fderiv ℝ (fderiv ℝ f) p) (fderiv ℝ (fderiv ℝ f) x)] at h
      exact h
    have hBp : ‖fderiv ℝ (fderiv ℝ g) p‖ ≤ M := by
      have h := hδ₂ (x := p) (by rw [dist_eq_norm p x]; exact hp₂)
      rw [dist_eq_norm (fderiv ℝ (fderiv ℝ g) p) (fderiv ℝ (fderiv ℝ g) x)] at h
      have htri := norm_add_le (fderiv ℝ (fderiv ℝ g) p - fderiv ℝ (fderiv ℝ g) x)
        (fderiv ℝ (fderiv ℝ g) x)
      have hc : ‖(fderiv ℝ (fderiv ℝ g) p - fderiv ℝ (fderiv ℝ g) x)
            + fderiv ℝ (fderiv ℝ g) x‖
          = ‖fderiv ℝ (fderiv ℝ g) p‖ :=
        congrArg norm (sub_add_cancel (fderiv ℝ (fderiv ℝ g) p) (fderiv ℝ (fderiv ℝ g) x))
      have h2 : ‖fderiv ℝ (fderiv ℝ g) x‖ + 1 ≤ M := by rw [hMdef]
      linarith
    -- Injectivity: a nonzero vector in the kernel would contradict the lower bound.
    intro u v huv
    by_contra hne
    have hwne : u - v ≠ 0 := sub_ne_zero.mpr hne
    have hwpos : 0 < ‖u - v‖ := norm_pos_iff.mpr hwne
    have hT : (fderiv ℝ (fderiv ℝ f) p + t • fderiv ℝ (fderiv ℝ g) p) (u - v) = 0 := by
      rw [map_sub, huv, sub_self]
    have hT' : fderiv ℝ (fderiv ℝ f) p (u - v)
        + t • (fderiv ℝ (fderiv ℝ g) p (u - v)) = 0 := by
      rw [add_apply, smul_apply] at hT
      exact hT
    have hApv : fderiv ℝ (fderiv ℝ f) p (u - v)
        = -(t • (fderiv ℝ (fderiv ℝ g) p (u - v))) :=
      eq_neg_of_add_eq_zero_left hT'
    have hAx : fderiv ℝ (fderiv ℝ f) x (u - v)
        = (fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) p) (u - v)
          - t • (fderiv ℝ (fderiv ℝ g) p (u - v)) := by
      rw [sub_apply, hApv]
      abel
    -- The two halves of the displacement.
    have h6 : |t| * ‖fderiv ℝ (fderiv ℝ g) p‖ < κ / 2 := by
      calc |t| * ‖fderiv ℝ (fderiv ℝ g) p‖ ≤ |t| * M :=
            mul_le_mul_of_nonneg_left hBp (abs_nonneg t)
        _ < (κ / (2 * M)) * M := mul_lt_mul_of_pos_right ht₂ hMpos
        _ = κ / 2 := by field_simp
    have h7 : ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) p‖ < κ / 2 := by
      have hrev := norm_sub_rev (fderiv ℝ (fderiv ℝ f) x) (fderiv ℝ (fderiv ℝ f) p)
      linarith
    have hstrict : ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) p‖
        + |t| * ‖fderiv ℝ (fderiv ℝ g) p‖ < κ := by linarith
    -- Bound the value of the reference Hessian on `u - v`.
    have hle1 : ‖(fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) p) (u - v)‖
        ≤ ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) p‖ * ‖u - v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have hle2 : ‖fderiv ℝ (fderiv ℝ g) p (u - v)‖
        ≤ ‖fderiv ℝ (fderiv ℝ g) p‖ * ‖u - v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have hchain : ‖fderiv ℝ (fderiv ℝ f) x (u - v)‖
        ≤ (‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) p‖
            + |t| * ‖fderiv ℝ (fderiv ℝ g) p‖) * ‖u - v‖ := by
      calc ‖fderiv ℝ (fderiv ℝ f) x (u - v)‖
          = ‖(fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) p) (u - v)
              - t • (fderiv ℝ (fderiv ℝ g) p (u - v))‖ := by rw [hAx]
        _ ≤ ‖(fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) p) (u - v)‖
              + ‖t • (fderiv ℝ (fderiv ℝ g) p (u - v))‖ :=
              norm_sub_le ((fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) p) (u - v))
                (t • (fderiv ℝ (fderiv ℝ g) p (u - v)))
        _ = ‖(fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) p) (u - v)‖
              + |t| * ‖fderiv ℝ (fderiv ℝ g) p (u - v)‖ := by
              rw [norm_smul, Real.norm_eq_abs]
        _ ≤ ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) p‖ * ‖u - v‖
              + |t| * (‖fderiv ℝ (fderiv ℝ g) p‖ * ‖u - v‖) :=
              add_le_add hle1 (mul_le_mul_of_nonneg_left hle2 (abs_nonneg t))
        _ = (‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) p‖
              + |t| * ‖fderiv ℝ (fderiv ℝ g) p‖) * ‖u - v‖ := by ring
    have hlt : κ * ‖u - v‖ < κ * ‖u - v‖ :=
      lt_of_le_of_lt (hκ x (by simp) (u - v))
        (lt_of_le_of_lt hchain (mul_lt_mul_of_pos_right hstrict hwpos))
    exact absurd hlt (lt_irrefl _)

/-- **Nondegeneracy of critical points is stable under small linear perturbations.** Let `f g : ℝ² → ℝ` be `C²` and let every `x ∈ X` have injective Hessian `fderiv ℝ (fderiv ℝ f) x`. Then, uniformly for `x ∈ X`, the Hessian of the perturbed function `q ↦ f q + t * g q` stays injective at every point near `x`, for small `t`.

Route: `fderiv ℝ (fderiv ℝ (fun q => f q + t * g q)) p = fderiv ℝ (fderiv ℝ f) p + t • fderiv ℝ (fderiv ℝ g) p`, so the map `(t, p) ↦` (Hessian of the perturbed function at `p`) is continuous; an injective (hence, by finite dimension, invertible) continuous linear map `ℝ² →L[ℝ] (ℝ² →L[ℝ] ℝ)` stays `IsInvertible` in a neighbourhood of itself (`Work.Embedding.isOpen_isInvertible`, importable as `Submission.Work.Embedding.smooth_implicit_function_nhd`, proves that the invertible continuous linear maps between two real Banach spaces form an open set; `ContinuousLinearMap.IsInvertible.injective` gives the conclusion). This needs injective ⟹ IsInvertible, which follows from `LinearMap.injective_iff_surjective_of_finrank_eq_finrank` (both spaces have dimension 2) and `ContinuousLinearEquiv.ofBijective`. Alternative route avoiding `IsInvertible`: an injective continuous linear map `H` satisfies `∃ c > 0, ∀ v, c * ‖v‖ ≤ ‖H v‖` (compactness of the unit sphere, `isCompact_sphere`), and this lower bound survives small perturbations. Finitely many `x ∈ X`: take the minimum of the resulting `δ`'s (`X = ∅`: any `δ`). -/
theorem hessian_inj_nhds {f g : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (X : Finset (ℝ × ℝ)) (hX : ∀ x ∈ X, Function.Injective (fderiv ℝ (fderiv ℝ f) x)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ X, ∀ t : ℝ, |t| < δ → ∀ p : ℝ × ℝ, ‖p - x‖ < δ →
      Function.Injective (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => f q + t * g q)) p) := by
  classical
  have hident : ∀ (t : ℝ) (p : ℝ × ℝ),
      fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => f q + t * g q)) p
        = fderiv ℝ (fderiv ℝ f) p + t • fderiv ℝ (fderiv ℝ g) p :=
    fun t p => fderiv_hessian f g hf hg t p
  let d : ℝ × ℝ → ℝ := fun x => if h : x ∈ X then
    Classical.choose (injective_perturb_nhds f g hf hg x (hX x h)) else 1
  have hdx : ∀ x (hx : x ∈ X), d x
      = Classical.choose (injective_perturb_nhds f g hf hg x (hX x hx)) := by
    intro x hx
    unfold d
    rw [dif_pos hx]
  have hdpos : ∀ x ∈ X, 0 < d x := by
    intro x hx
    rw [hdx x hx]
    exact (Classical.choose_spec (injective_perturb_nhds f g hf hg x (hX x hx))).1
  have hdspec : ∀ x ∈ X, ∀ t : ℝ, |t| < d x → ∀ p : ℝ × ℝ, ‖p - x‖ < d x →
      Function.Injective (fderiv ℝ (fderiv ℝ f) p + t • fderiv ℝ (fderiv ℝ g) p) := by
    intro x hx t ht p hp
    rw [hdx x hx] at ht hp
    exact (Classical.choose_spec (injective_perturb_nhds f g hf hg x (hX x hx))).2 t p ht hp
  by_cases hne : X.Nonempty
  · refine ⟨X.inf' hne d, ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      exact hdpos
    · intro x hx t ht p hp
      have hle : X.inf' hne d ≤ d x := Finset.inf'_le d hx
      rw [hident t p]
      exact hdspec x hx t (lt_of_lt_of_le ht hle) p (lt_of_lt_of_le hp hle)
  · refine ⟨1, one_pos, ?_⟩
    intro x hx
    exact absurd ⟨x, hx⟩ hne

end Work.Drive.EpsForm
