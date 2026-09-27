import Mathlib

/-!
# Smoothness of Mathlib's Gram–Schmidt along a smooth pointwise-independent family

The GS leg of the frame-field brick (`CutPush/NOTES_hasFingerData_S51.md` §5b).  For a smooth family
`v : ℝ → Fin (k+1) → E` that is pointwise linearly independent, each Gram–Schmidt vector
`t ↦ gramSchmidt ℝ (v t) n` is smooth.

The recursion is available **already unfolded** as `InnerProductSpace.gramSchmidt_def''`:

  `v t n = gramSchmidt ℝ (v t) n + ∑ i < n, (⟪g_i t, v t n⟫ / ‖g_i t‖²) • g_i t`,

so the proof is a strong induction on `n`: each term of the sum is a quotient of smooth functions
whose denominator `‖g_i t‖²` is pointwise nonzero by `InnerProductSpace.gramSchmidt_ne_zero`
(which consumes exactly the pointwise independence — this is where `hli` is load-bearing).
-/

open scoped ContDiff
open InnerProductSpace

namespace Work.Whitney.CutPush

/-- **Smoothness of Gram–Schmidt.** -/
theorem contDiff_gramSchmidt {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] (v : ℝ → Fin (k + 1) → E)
    (hv : ∀ i : Fin (k + 1), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => v t i))
    (hli : ∀ t : ℝ, LinearIndependent ℝ (v t)) (n : Fin (k + 1)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => InnerProductSpace.gramSchmidt ℝ (v t) n) := by
  have key : ∀ m : ℕ, ∀ hm : m < k + 1,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => InnerProductSpace.gramSchmidt ℝ (v t) ⟨m, hm⟩) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      have hstep : (fun t : ℝ => InnerProductSpace.gramSchmidt ℝ (v t) ⟨m, hm⟩)
          = fun t : ℝ => v t ⟨m, hm⟩ - ∑ i ∈ Finset.Iio (⟨m, hm⟩ : Fin (k + 1)),
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
        have h : i < (⟨m, hm⟩ : Fin (k + 1)) := Finset.mem_Iio.mp hi
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

/-- **Smoothness of the normalized Gram–Schmidt**, i.e. of the frame leg itself: the normalisation
divides by `‖gramSchmidt ℝ (v t) n‖`, which is smooth (`ContDiff.norm`) and pointwise nonzero by
`gramSchmidt_ne_zero` — the same input that drives `contDiff_gramSchmidt`. -/
theorem contDiff_gramSchmidtNormed {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (v : ℝ → Fin (k + 1) → E)
    (hv : ∀ i : Fin (k + 1), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => v t i))
    (hli : ∀ t : ℝ, LinearIndependent ℝ (v t)) (n : Fin (k + 1)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => InnerProductSpace.gramSchmidtNormed (𝕜 := ℝ) (v t) n) := by
  have hgs := contDiff_gramSchmidt v hv hli n
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

end Work.Whitney.CutPush
