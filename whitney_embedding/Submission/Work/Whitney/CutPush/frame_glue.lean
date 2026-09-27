import Mathlib
import Submission.Work.Whitney.CutPush.contDiff_gramSchmidt

/-!
# Ingredients for gluing two local frames along a parameter interval

`NOTES_STATE_S56.md` §3/§6 (bricks G1-a and its gluing step).  Two frame fields of the *same* family
of `k`-planes can be glued by normalising the blend `(1 - φ) • c₁ + φ • c₂` with `φ < 1/2`: the blend
is again a pointwise basis of the same plane, because the two frames are isometric parametrisations of
that plane, and `(1 - φ) x + φ T x = 0` with `T` an isometry forces `φ ≥ 1/2` unless `x = 0`.

This file supplies the two analytic ingredients of that argument.

* `sum_smul_norm_sq_orthonormal` — the norm formula `‖∑ α i • v i‖² = ∑ (α i)²` for an orthonormal
  family, which is what makes "the two frames have the same norm" true.
* `contDiff_gramSchmidt_fin` / `contDiff_gramSchmidtNormed_fin` — the `Fin k` form of the smoothness
  of Gram–Schmidt (`CutPush/contDiff_gramSchmidt.lean` proves the `Fin (k+1)` form; the difference is
  only the index type, and Mathlib's `gramSchmidt` is stated for any linearly ordered index type with
  `LocallyFiniteOrderBot` and `WellFoundedLT`, so the proof is the same strong induction).
-/

open scoped BigOperators ContDiff
open InnerProductSpace

namespace Work.Whitney.CutPush

/-- **The norm of an orthonormal combination.**  For an orthonormal family `v` and coefficients `α`,
`‖∑ α i • v i‖ ^ 2 = ∑ (α i) ^ 2`. -/
theorem sum_smul_norm_sq_orthonormal {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v : Fin k → E} (hv : Orthonormal ℝ v) (α : Fin k → ℝ) :
    ‖∑ i, α i • v i‖ ^ 2 = ∑ i, (α i) ^ 2 := by
  have hite : ∀ i j : Fin k, inner ℝ (v i) (v j) = if i = j then (1 : ℝ) else 0 :=
    (orthonormal_iff_ite.mp hv)
  rw [← real_inner_self_eq_norm_sq]
  have h2 : inner ℝ (∑ i, α i • v i) (∑ i, α i • v i)
      = ∑ i, ∑ j, (α i * α j) * inner ℝ (v i) (v j) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  rw [h2]
  have h3 : ∀ i : Fin k, ∑ j, (α i * α j) * inner ℝ (v i) (v j) = (α i) ^ 2 := by
    intro i
    rw [Finset.sum_congr rfl fun j _ => by rw [hite i j], Finset.sum_eq_single i]
    · rw [if_pos rfl]; ring
    · intro j _ hj; rw [if_neg (Ne.symm hj)]; ring
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [Finset.sum_congr rfl fun i _ => h3 i]

/-- **Smoothness of Gram–Schmidt, `Fin k` form.** -/
theorem contDiff_gramSchmidt_fin {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (v : ℝ → Fin k → E)
    (hv : ∀ i : Fin k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => v t i))
    (hli : ∀ t : ℝ, LinearIndependent ℝ (v t)) (n : Fin k) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => InnerProductSpace.gramSchmidt ℝ (v t) n) := by
  have key : ∀ m : ℕ, ∀ hm : m < k,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => InnerProductSpace.gramSchmidt ℝ (v t) ⟨m, hm⟩) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      have hstep : (fun t : ℝ => InnerProductSpace.gramSchmidt ℝ (v t) ⟨m, hm⟩)
          = fun t : ℝ => v t ⟨m, hm⟩ - ∑ i ∈ Finset.Iio (⟨m, hm⟩ : Fin k),
              (inner ℝ (InnerProductSpace.gramSchmidt ℝ (v t) i) (v t ⟨m, hm⟩)
                / (‖InnerProductSpace.gramSchmidt ℝ (v t) i‖ : ℝ) ^ 2)
              • InnerProductSpace.gramSchmidt ℝ (v t) i := by
        funext t
        rw [eq_sub_iff_add_eq]
        exact (InnerProductSpace.gramSchmidt_def'' ℝ (v t) ⟨m, hm⟩).symm
      rw [hstep]
      refine (hv ⟨m, hm⟩).sub ?_
      refine ContDiff.sum fun i hi => ?_
      have hi' : (i : ℕ) < m := by
        have h : i < (⟨m, hm⟩ : Fin k) := Finset.mem_Iio.mp hi
        exact h
      have hig : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun t : ℝ => InnerProductSpace.gramSchmidt ℝ (v t) i) := ih (i : ℕ) hi' i.isLt
      have hne : ∀ t : ℝ, InnerProductSpace.gramSchmidt ℝ (v t) i ≠ 0 :=
        fun t => InnerProductSpace.gramSchmidt_ne_zero i (hli t)
      have hden : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun t : ℝ => (‖InnerProductSpace.gramSchmidt ℝ (v t) i‖ : ℝ) ^ 2) :=
        ((ContDiff.norm ℝ hig fun t => hne t).pow 2)
      have hnum : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun t : ℝ => inner ℝ (InnerProductSpace.gramSchmidt ℝ (v t) i) (v t ⟨m, hm⟩)) :=
        (isBoundedBilinearMap_inner (𝕜 := ℝ) (E := E)).contDiff.comp
          (hig.prodMk (hv ⟨m, hm⟩))
      have hden_ne : ∀ t : ℝ,
          (‖InnerProductSpace.gramSchmidt ℝ (v t) i‖ : ℝ) ^ 2 ≠ 0 :=
        fun t => pow_ne_zero 2 (by exact_mod_cast norm_ne_zero_iff.mpr (hne t))
      exact (hnum.div hden hden_ne).smul hig
  exact key n.val n.isLt

/-- **Smoothness of the normalised Gram–Schmidt, `Fin k` form.** -/
theorem contDiff_gramSchmidtNormed_fin {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (v : ℝ → Fin k → E)
    (hv : ∀ i : Fin k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => v t i))
    (hli : ∀ t : ℝ, LinearIndependent ℝ (v t)) (n : Fin k) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => InnerProductSpace.gramSchmidtNormed (𝕜 := ℝ) (v t) n) := by
  have hgs := contDiff_gramSchmidt_fin v hv hli n
  have hne : ∀ t : ℝ, InnerProductSpace.gramSchmidt ℝ (v t) n ≠ 0 :=
    fun t => InnerProductSpace.gramSchmidt_ne_zero n (hli t)
  have hnorm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => ‖InnerProductSpace.gramSchmidt ℝ (v t) n‖) := ContDiff.norm ℝ hgs hne
  have hinv := hnorm.inv fun t => norm_ne_zero_iff.mpr (hne t)
  have hfun : (fun t : ℝ => InnerProductSpace.gramSchmidtNormed (𝕜 := ℝ) (v t) n)
      = fun t : ℝ => (‖InnerProductSpace.gramSchmidt ℝ (v t) n‖)⁻¹
          • InnerProductSpace.gramSchmidt ℝ (v t) n := by
    funext t
    simp [InnerProductSpace.gramSchmidtNormed]
  rw [hfun]
  exact hinv.smul hgs


/-- **Gluing two local frames of the same planes.**  If `c₁` and `c₂` are two smooth orthonormal
`k`-frames spanning the *same* `k`-plane at every `t`, and `φ < 1/2` is smooth, then the normalised
blend `(1 - φ) • c₁ + φ • c₂` is pointwise a basis of that same plane: if `(1 - φ) x + φ y = 0` with
`‖y‖ = ‖x‖` then `|1 - φ| ‖x‖ = |φ| ‖x‖`, and `|1 - φ| = |φ|` forces `φ = 1/2` (or `1 = 0`), so
`x = 0`.  The hypothesis is `φ ≠ 1/2` (not `φ < 1/2`), which is what lets a chain of gluings switch
from one frame to the other. -/
theorem exists_smooth_frame_of_blend {m k : ℕ}
    (c₁ c₂ : Fin k → ℝ → EuclideanSpace ℝ (Fin m))
    (hc₁ : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (c₁ i))
    (hc₂ : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (c₂ i))
    (horth₁ : ∀ t, Orthonormal ℝ (fun i => c₁ i t))
    (horth₂ : ∀ t, Orthonormal ℝ (fun i => c₂ i t))
    (hspan : ∀ t, Submodule.span ℝ (Set.range (fun i => c₁ i t))
      = Submodule.span ℝ (Set.range (fun i => c₂ i t)))
    (φ : ℝ → ℝ) (hφc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφne : ∀ t, φ t ≠ 1 / 2) :
    ∃ B : Fin k → ℝ → EuclideanSpace ℝ (Fin m),
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B i)) ∧
      (∀ t, Orthonormal ℝ (fun i => B i t)) ∧
      (∀ t, Submodule.span ℝ (Set.range (fun i => B i t))
        = Submodule.span ℝ (Set.range (fun i => c₁ i t))) := by
  classical
  set w : ℝ → Fin k → EuclideanSpace ℝ (Fin m) :=
    fun t i => (1 - φ t) • c₁ i t + φ t • c₂ i t with hw
  have hwsm : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => w t i) := by
    intro i
    rw [hw]
    exact (((contDiff_const.sub hφc).smul (hc₁ i)).add (hφc.smul (hc₂ i)))
  have hwli : ∀ t, LinearIndependent ℝ (w t) := by
    intro t
    rw [Fintype.linearIndependent_iff]
    intro g hg
    set x : EuclideanSpace ℝ (Fin m) := ∑ i, g i • c₁ i t with hx
    set y : EuclideanSpace ℝ (Fin m) := ∑ i, g i • c₂ i t with hy
    have hkey : ∑ i, g i • w t i = (1 - φ t) • x + φ t • y := by
      have h1 : ∀ i : Fin k, g i • w t i
          = (1 - φ t) • (g i • c₁ i t) + φ t • (g i • c₂ i t) := by
        intro i
        show g i • ((1 - φ t) • c₁ i t + φ t • c₂ i t) = _
        rw [smul_add, smul_comm (g i) (1 - φ t) (c₁ i t),
          smul_comm (g i) (φ t) (c₂ i t)]
      rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_add_distrib, ← Finset.smul_sum,
        ← Finset.smul_sum, ← hx, ← hy]
    have hrel : (1 - φ t) • x + φ t • y = 0 := by rw [← hkey]; exact hg
    have hxn : ‖x‖ ^ 2 = ∑ i, (g i) ^ 2 := by
      rw [hx]; exact sum_smul_norm_sq_orthonormal (horth₁ t) g
    have hyn : ‖y‖ ^ 2 = ∑ i, (g i) ^ 2 := by
      rw [hy]; exact sum_smul_norm_sq_orthonormal (horth₂ t) g
    have hnorms : ‖x‖ = ‖y‖ := by nlinarith [norm_nonneg x, norm_nonneg y]
    have hsmul : (1 - φ t) • x = -(φ t • y) := by
      rw [eq_neg_iff_add_eq_zero]
      exact hrel
    have hnorm : |1 - φ t| * ‖x‖ = |φ t| * ‖x‖ := by
      have h := congrArg norm hsmul
      rw [norm_neg, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at h
      rw [← hnorms] at h
      exact h
    have hne : |1 - φ t| ≠ |φ t| := by
      intro habs
      rcases abs_eq_abs.mp habs with h' | h'
      · exact hφne t (by linarith)
      · linarith
    have hx0 : x = 0 := by
      rw [← norm_eq_zero]
      by_contra hxne
      exact hne (mul_right_cancel₀ hxne hnorm)
    have hsum : ∑ i, g i • c₁ i t = 0 := by rw [← hx]; exact hx0
    intro i
    exact Fintype.linearIndependent_iff.mp (horth₁ t).linearIndependent g hsum i
  refine ⟨fun i => fun t => InnerProductSpace.gramSchmidtNormed (𝕜 := ℝ) (w t) i, ?_, ?_, ?_⟩
  · intro i
    exact contDiff_gramSchmidtNormed_fin w hwsm hwli i
  · intro t
    exact InnerProductSpace.gramSchmidtNormed_orthonormal (hwli t)
  · intro t
    have h1 : Submodule.span ℝ
          (Set.range (fun i => InnerProductSpace.gramSchmidtNormed (𝕜 := ℝ) (w t) i))
        = Submodule.span ℝ (Set.range (w t)) := by
      have hA := InnerProductSpace.span_gramSchmidtNormed (𝕜 := ℝ) (w t) Set.univ
      have hB := InnerProductSpace.span_gramSchmidt (𝕜 := ℝ) (w t)
      simp only [Set.image_univ] at hA
      rw [hA, hB]
    rw [h1]
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      have hc₂mem : c₂ i t ∈ Submodule.span ℝ (Set.range (fun i => c₁ i t)) := by
        rw [hspan t]
        exact Submodule.subset_span ⟨i, rfl⟩
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
        (Submodule.smul_mem _ _ hc₂mem)
    · rw [finrank_span_eq_card (hwli t), finrank_span_eq_card (horth₁ t).linearIndependent]

/-- **Gluing two local frames, on a set where their spans agree.**  The variant of
`exists_smooth_frame_of_blend` used when *chaining*: along the transition between two local frames the
two families span the same plane only on the overlap of the two domains, so the span hypothesis and
the span conclusion are both localised to a set `U` (the independence part is pointwise and needs
nothing). -/
theorem exists_smooth_frame_of_blend_on {m k : ℕ}
    (c₁ c₂ : Fin k → ℝ → EuclideanSpace ℝ (Fin m))
    (hc₁ : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (c₁ i))
    (hc₂ : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (c₂ i))
    (horth₁ : ∀ t, Orthonormal ℝ (fun i => c₁ i t))
    (horth₂ : ∀ t, Orthonormal ℝ (fun i => c₂ i t))
    (U : Set ℝ)
    (hspan : ∀ t ∈ U, Submodule.span ℝ (Set.range (fun i => c₁ i t))
      = Submodule.span ℝ (Set.range (fun i => c₂ i t)))
    (φ : ℝ → ℝ) (hφc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφne : ∀ t, φ t ≠ 1 / 2) :
    ∃ B : Fin k → ℝ → EuclideanSpace ℝ (Fin m),
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B i)) ∧
      (∀ t, Orthonormal ℝ (fun i => B i t)) ∧
      (∀ t ∈ U, Submodule.span ℝ (Set.range (fun i => B i t))
        = Submodule.span ℝ (Set.range (fun i => c₁ i t))) := by
  classical
  set w : ℝ → Fin k → EuclideanSpace ℝ (Fin m) :=
    fun t i => (1 - φ t) • c₁ i t + φ t • c₂ i t with hw
  have hwsm : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => w t i) := by
    intro i
    rw [hw]
    exact (((contDiff_const.sub hφc).smul (hc₁ i)).add (hφc.smul (hc₂ i)))
  have hwli : ∀ t, LinearIndependent ℝ (w t) := by
    intro t
    rw [Fintype.linearIndependent_iff]
    intro g hg
    set x : EuclideanSpace ℝ (Fin m) := ∑ i, g i • c₁ i t with hx
    set y : EuclideanSpace ℝ (Fin m) := ∑ i, g i • c₂ i t with hy
    have hkey : ∑ i, g i • w t i = (1 - φ t) • x + φ t • y := by
      have h1 : ∀ i : Fin k, g i • w t i
          = (1 - φ t) • (g i • c₁ i t) + φ t • (g i • c₂ i t) := by
        intro i
        show g i • ((1 - φ t) • c₁ i t + φ t • c₂ i t) = _
        rw [smul_add, smul_comm (g i) (1 - φ t) (c₁ i t),
          smul_comm (g i) (φ t) (c₂ i t)]
      rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_add_distrib, ← Finset.smul_sum,
        ← Finset.smul_sum, ← hx, ← hy]
    have hrel : (1 - φ t) • x + φ t • y = 0 := by rw [← hkey]; exact hg
    have hxn : ‖x‖ ^ 2 = ∑ i, (g i) ^ 2 := by
      rw [hx]; exact sum_smul_norm_sq_orthonormal (horth₁ t) g
    have hyn : ‖y‖ ^ 2 = ∑ i, (g i) ^ 2 := by
      rw [hy]; exact sum_smul_norm_sq_orthonormal (horth₂ t) g
    have hnorms : ‖x‖ = ‖y‖ := by nlinarith [norm_nonneg x, norm_nonneg y]
    have hsmul : (1 - φ t) • x = -(φ t • y) := by
      rw [eq_neg_iff_add_eq_zero]
      exact hrel
    have hnorm : |1 - φ t| * ‖x‖ = |φ t| * ‖x‖ := by
      have h := congrArg norm hsmul
      rw [norm_neg, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at h
      rw [← hnorms] at h
      exact h
    have hne : |1 - φ t| ≠ |φ t| := by
      intro habs
      rcases abs_eq_abs.mp habs with h' | h'
      · exact hφne t (by linarith)
      · linarith
    have hx0 : x = 0 := by
      rw [← norm_eq_zero]
      by_contra hxne
      exact hne (mul_right_cancel₀ hxne hnorm)
    have hsum : ∑ i, g i • c₁ i t = 0 := by rw [← hx]; exact hx0
    intro i
    exact Fintype.linearIndependent_iff.mp (horth₁ t).linearIndependent g hsum i
  refine ⟨fun i => fun t => InnerProductSpace.gramSchmidtNormed (𝕜 := ℝ) (w t) i, ?_, ?_, ?_⟩
  · intro i
    exact contDiff_gramSchmidtNormed_fin w hwsm hwli i
  · intro t
    exact InnerProductSpace.gramSchmidtNormed_orthonormal (hwli t)
  · intro t ht
    have h1 : Submodule.span ℝ
          (Set.range (fun i => InnerProductSpace.gramSchmidtNormed (𝕜 := ℝ) (w t) i))
        = Submodule.span ℝ (Set.range (w t)) := by
      have hA := InnerProductSpace.span_gramSchmidtNormed (𝕜 := ℝ) (w t) Set.univ
      have hB := InnerProductSpace.span_gramSchmidt (𝕜 := ℝ) (w t)
      simp only [Set.image_univ] at hA
      rw [hA, hB]
    rw [h1]
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      have hc₂mem : c₂ i t ∈ Submodule.span ℝ (Set.range (fun i => c₁ i t)) := by
        rw [hspan t ht]
        exact Submodule.subset_span ⟨i, rfl⟩
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
        (Submodule.smul_mem _ _ hc₂mem)
    · rw [finrank_span_eq_card (hwli t), finrank_span_eq_card (horth₁ t).linearIndependent]

end Work.Whitney.CutPush
