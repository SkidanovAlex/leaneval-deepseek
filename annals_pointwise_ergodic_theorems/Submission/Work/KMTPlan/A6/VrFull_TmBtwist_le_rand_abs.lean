import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallIngredients
import Submission.Work.Analysis.Variation.rmVarBound_uniform

set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6

/-!
# The Rademacher--Menshov reduction with an absolute constant

`Work.KMTPlan.A6.VrFull_TmBtwist_le_rand` (`LowSmallModelVar.lean`) bounds the `ℓ¹(ℤ)` norm of the
full truncated `2`-variation of the twisted bilinear family `k ↦ BtwistEx … (Tm … (Φ k) f)
(Tm … (Ψ k) g)` by the corresponding uniform bound over the randomised cutoffs
`Tm … (randSymb Φ ε K)`, at the price of a factor `⟨log₂ K + 2⟩²`; there the constant `C_RM` is
produced only *after* the parameters `ρ, P, l₁, l₂, m₁, m₂`.

The present lemma is the same statement with `l₁ l₂ m₁ m₂` moved *inside* the quantifier, so that
one constant `C_RM` serves the whole scale pair and the whole twist.  This is what the A6 assembly
needs.  The underlying engine is `Work.Analysis.Variation.rmVarBound_uniform`, whose constant is
independent of the bilinear form, so the argument of the parametrised version applies verbatim.
-/

theorem VrFull_TmBtwist_le_rand_abs (ρ : ℝ) (P : Polynomial ℤ) :
    ∃ C_RM : ℝ, 0 < C_RM ∧ ∀ (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
      (hm₁ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₁ j‖)
      (hm₂ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₂ j‖)
      (K : ℕ) (Φ Ψ : ℕ → ℝ → ℂ) (f g : ℤ → ℂ) (C : ENNReal),
      Φ 0 = 0 → Ψ 0 = 0 →
      MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
      MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
      Work.KMTPlan.A6.TmSide ρ l₁ K Φ → Work.KMTPlan.A6.TmSide ρ l₂ K Ψ →
      (∀ k : ℕ, ∃ D : ℝ, ∀ y : ℤ,
        ‖Work.KMTAreas.A7.Tm ρ l₁ (Φ k) f y‖ ≤ D) →
      (∀ k : ℕ, ∃ D : ℝ, ∀ y : ℤ,
        ‖Work.KMTAreas.A7.Tm ρ l₂ (Ψ k) g y‖ ≤ D) →
      (∀ (ε ε' : ℕ → ℂ), (∀ k, ‖ε k‖ ≤ 1) → (∀ k, ‖ε' k‖ ≤ 1) →
        MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂ m₁ m₂
          (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTAreas.A7.randSymb Φ ε K) f)
          (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.randSymb Ψ ε' K) g) x)
          1 MeasureTheory.Measure.count ≤ C) →
      MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.Variation.VrFull 2 K (fun k : ℕ =>
          Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂ m₁ m₂
            (Work.KMTAreas.A7.Tm ρ l₁ (Φ k) f)
            (Work.KMTAreas.A7.Tm ρ l₂ (Ψ k) g) x))
        1 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C_RM * ((Nat.log2 K : ℝ) + 2) ^ (2 : ℝ)) * C := by
  -- The absolute Rademacher--Menshov engine at `L¹`.  Its constant is independent of the
  -- bilinear form, and the bilinear form used below is always the same (`BtwistEx` on `bddSub`),
  -- so a single `C_RM` serves every scale pair and every twist.
  obtain ⟨C_RM, hC_RM, hgen⟩ :=
    Work.Analysis.Variation.rmVarBound_uniform 1 (by norm_num) (by norm_num)
      (V := bddSub) (W := bddSub) (X := ℤ) (μ := MeasureTheory.Measure.count)
  refine ⟨C_RM, hC_RM, ?_⟩
  intro l₁ l₂ m₁ m₂ hm₁ hm₂ K Φ Ψ f g C hΦ0 hΨ0 hf hg hside₁ hside₂ hbd₁ hbd₂ hSS
  obtain ⟨hper₁, hI₁, hκ₁⟩ := hside₁
  obtain ⟨hper₂, hI₂, hκ₂⟩ := hside₂
  let U : ℕ → bddSub := fun k => ⟨Work.KMTAreas.A7.Tm ρ l₁ (Φ k) f, hbd₁ k⟩
  let W : ℕ → bddSub := fun k => ⟨Work.KMTAreas.A7.Tm ρ l₂ (Ψ k) g, hbd₂ k⟩
  have hU0 : U 0 = 0 := by
    apply Subtype.ext
    show Work.KMTAreas.A7.Tm ρ l₁ (Φ 0) f = (0 : ℤ → ℂ)
    rw [hΦ0]
    exact Tm_zero ρ l₁ f hf
  have hW0 : W 0 = 0 := by
    apply Subtype.ext
    show Work.KMTAreas.A7.Tm ρ l₂ (Ψ 0) g = (0 : ℤ → ℂ)
    rw [hΨ0]
    exact Tm_zero ρ l₂ g hg
  -- The Rademacher--Menshov reduction, stated with the sequence `U`/`W` (which is definitionally
  -- the family of twisted images) and with hgen's exponent `ENNReal.ofReal 1`.
  have hmain : MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.Variation.VrFull 2 K
        (fun k : ℕ => BtwistEx ρ P l₁ l₂ m₁ m₂ (U k).1 (W k).1 x))
        (ENNReal.ofReal 1) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C_RM * ((Nat.log2 K : ℝ) + 2) ^ (2 : ℕ)) * C := by
    refine hgen (fun u v x => BtwistEx ρ P l₁ l₂ m₁ m₂ u.1 v.1 x)
      (BtwistEx_bdd_add₁ ρ P l₁ l₂ m₁ m₂ hm₁ hm₂)
      (BtwistEx_bdd_smul₁ ρ P l₁ l₂ m₁ m₂ hm₁ hm₂)
      (BtwistEx_bdd_add₂ ρ P l₁ l₂ m₁ m₂ hm₁ hm₂)
      (BtwistEx_bdd_smul₂ ρ P l₁ l₂ m₁ m₂ hm₁ hm₂)
      K U W C hU0 hW0
      (fun k k' => (measurable_of_countable (fun x : ℤ =>
        BtwistEx ρ P l₁ l₂ m₁ m₂ (U k).1 (W k').1 x)).aemeasurable) ?_
    intro ε ε' hε hε'
    have h1 : (∑ k ∈ Finset.range K, ε k • (U (k + 1) - U k)).1
        = Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTAreas.A7.randSymb Φ ε K) f := by
      have hstep : (∑ k ∈ Finset.range K, ε k • (U (k + 1) - U k)).1
          = ∑ k ∈ Finset.range K, ε k • (Work.KMTAreas.A7.Tm ρ l₁ (Φ (k + 1)) f
              - Work.KMTAreas.A7.Tm ρ l₁ (Φ k) f) := by
        rw [Submodule.coe_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        funext y
        simp only [Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply, Pi.sub_apply,
          smul_eq_mul, U]
      rw [hstep]
      exact (Work.KMTPlan.A6.Tm_randSymb_eq ρ l₁ K Φ ε f hf hper₁ hI₁ hκ₁).symm
    have h2 : (∑ k ∈ Finset.range K, ε' k • (W (k + 1) - W k)).1
        = Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.randSymb Ψ ε' K) g := by
      have hstep : (∑ k ∈ Finset.range K, ε' k • (W (k + 1) - W k)).1
          = ∑ k ∈ Finset.range K, ε' k • (Work.KMTAreas.A7.Tm ρ l₂ (Ψ (k + 1)) g
              - Work.KMTAreas.A7.Tm ρ l₂ (Ψ k) g) := by
        rw [Submodule.coe_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        funext y
        simp only [Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply, Pi.sub_apply,
          smul_eq_mul, W]
      rw [hstep]
      exact (Work.KMTPlan.A6.Tm_randSymb_eq ρ l₂ K Ψ ε' g hg hper₂ hI₂ hκ₂).symm
    rw [h1, h2, ENNReal.ofReal_one]
    exact hSS ε ε' hε hε'
  -- `⟨log₂ K + 2⟩²` is the same number whether the exponent is the natural or the real `2`.
  have hexp : ((Nat.log2 K : ℝ) + 2) ^ (2 : ℕ) = ((Nat.log2 K : ℝ) + 2) ^ (2 : ℝ) :=
    (Real.rpow_natCast ((Nat.log2 K : ℝ) + 2) 2).symm
  rw [hexp] at hmain
  rw [ENNReal.ofReal_one] at hmain
  exact hmain

end Work.KMTPlan.A6
