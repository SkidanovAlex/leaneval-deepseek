import Mathlib
import Submission.Work.Analysis.InverseTheory.Transpose
import Submission.Work.Analysis.InverseTheory.AhalfZAPI
import Submission.Port.Aesm

/-!
# The `ℓ²` bound for `Ã_N^*(φ,g)` when `‖φ‖_∞ ≤ 1`

The first dual function of the halved average (paper §6, equation `(bkhg)`) is

`Ã_N^*(h,g)(x) = (1/N) ∑_{N/2 < n ≤ N} h (x-n) g (x + P(n) - n)`.

If `‖h‖_∞ ≤ 1` then each summand is pointwise dominated by `|g (x + P(n) - n)|`, and since the
map `x ↦ x + P(n) - n` preserves counting measure on `ℤ`, the `ℓ²` seminorm of each summand is at
most `‖g‖₂`.  Minkowski's inequality for `eLpNorm` bounds the `ℓ²` norm of a finite sum by the sum
of the `ℓ²` norms, so `‖Ã_N^*(φ,g)‖₂ ≤ (♯{N/2 < n ≤ N} / N) ‖g‖₂ ≤ ‖g‖₂`.

This is the estimate that puts the transposed single-scale averages into `ℓ²` *uniformly* in `N`,
`P` and `φ ∈ ℓ^∞_{≤1}`, with no support hypothesis on `g`.  It complements
`Work.KMTAreas.A4.eLpNorm_AhalfTranspose_le` (the finite-support case, where `g` is supported in
`[-N₀,N₀]`); both feed the §5 (`A4`) estimates for the second dual function.

The two elementary inputs are isolated as private lemmas below:

* `measurePreserving_add_count` — translation preserves `Measure.count` on `ℤ`;
* `eLpNorm_shift`, `eLpNorm_shift_sub` — the resulting translation invariance of `eLpNorm`.
-/

namespace Work.KMTAreas.A4

open MeasureTheory

/-- Translation by a fixed `a : ℤ` preserves counting measure on `ℤ`. -/
private lemma measurePreserving_add_count (a : ℤ) :
    MeasureTheory.MeasurePreserving (fun x : ℤ => x + a) MeasureTheory.Measure.count
      MeasureTheory.Measure.count := by
  refine MeasureTheory.MeasurePreserving.mk (MeasurableAdd.measurable_add_const a) ?_
  refine MeasureTheory.Measure.ext fun t ht => ?_
  rw [MeasureTheory.Measure.map_apply (MeasurableAdd.measurable_add_const a) ht]
  have hpre : (fun x : ℤ => x + a) ⁻¹' t = (fun y : ℤ => y - a) '' t := by
    ext y
    rw [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hy
      exact ⟨y + a, hy, by ring⟩
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
  rw [hpre]
  exact MeasureTheory.Measure.count_injective_image sub_left_injective t

/-- The `ℒᵖ` seminorm for counting measure on `ℤ` is invariant under translations. -/
private lemma eLpNorm_shift (f : ℤ → ℂ) (p : ENNReal) (a : ℤ) :
    MeasureTheory.eLpNorm (fun x : ℤ => f (x + a)) p MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  have h := MeasureTheory.eLpNorm_comp_measurePreserving
    (μ := MeasureTheory.Measure.count) (ν := MeasureTheory.Measure.count)
    (f := fun x : ℤ => x + a) (g := f) (p := p)
    (_root_.measurable_of_countable f).aestronglyMeasurable (measurePreserving_add_count a)
  simpa [Function.comp_def] using h

/-- The `ℒᵖ` seminorm for counting measure on `ℤ` is invariant under the affine shift
`x ↦ x + a - b`. -/
private lemma eLpNorm_shift_sub (f : ℤ → ℂ) (p : ENNReal) (a b : ℤ) :
    MeasureTheory.eLpNorm (fun x : ℤ => f (x + a - b)) p MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  have hfun : (fun x : ℤ => f (x + a - b)) = (fun y : ℤ => f (y + (a - b))) := by
    funext x
    congr 1
    ring
  rw [hfun, eLpNorm_shift]

theorem eLpNorm_ahalfTranspose_le_of_bdd (N : ℕ) (P : Polynomial ℤ) {φ g : ℤ → ℂ}
    (hφ : ∀ x : ℤ, ‖φ x‖ ≤ 1) :
    MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.InverseTheory.AhalfTranspose N P φ g x) 2
        MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  set s : Finset ℕ := Finset.Ioc (N / 2) N with hs
  -- the number of terms is at most `N`
  have hcard : (s.card : ℝ) ≤ (N : ℝ) := by
    rw [hs]
    have h1 : (Finset.Ioc (N / 2) N).card ≤ N := by
      calc (Finset.Ioc (N / 2) N).card ≤ (Finset.Ioc 0 N).card :=
            Finset.card_le_card fun m hm => by
              simp only [Finset.mem_Ioc] at hm ⊢
              omega
        _ = N := by simp
    exact_mod_cast h1
  -- hence the normalising factor is at most `1`
  have hNinv : (N : ℝ)⁻¹ * (N : ℝ) ≤ 1 := by
    rcases eq_or_ne N 0 with hN | hN
    · rw [hN]
      norm_num
    · have hNpos : (0 : ℝ) < (N : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hN
      rw [inv_mul_cancel₀ hNpos.ne']
  have hcoef : (N : ℝ)⁻¹ * (s.card : ℝ) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hcard (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹)).trans hNinv
  -- rewrite `Ã_N^*` as a scalar multiple of the pointwise sum
  have hAhalf : (fun x : ℤ => Work.Analysis.InverseTheory.AhalfTranspose N P φ g x)
      = (((N : ℝ)⁻¹ : ℝ) : ℂ)
        • (fun x : ℤ => ∑ n ∈ s, φ (x - (n : ℤ)) * g (x + P.eval (n : ℤ) - (n : ℤ))) := by
    funext x
    simp only [Work.Analysis.InverseTheory.AhalfTranspose, Pi.smul_apply, smul_eq_mul, hs]
  -- each summand has `ℓ²` norm at most `‖g‖₂`
  have hterm : ∀ n ∈ s,
      MeasureTheory.eLpNorm
          (fun x : ℤ => φ (x - (n : ℤ)) * g (x + P.eval (n : ℤ) - (n : ℤ))) 2
          MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    intro n hn
    have h1 : MeasureTheory.eLpNorm
          (fun x : ℤ => φ (x - (n : ℤ)) * g (x + P.eval (n : ℤ) - (n : ℤ))) 2
          MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm
          (fun x : ℤ => g (x + P.eval (n : ℤ) - (n : ℤ))) 2
          MeasureTheory.Measure.count :=
      MeasureTheory.eLpNorm_mono (hf := by pw_aesm) fun x => by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hφ _)
    exact h1.trans (le_of_eq (eLpNorm_shift_sub g 2 (P.eval (n : ℤ)) (n : ℤ)))
  -- Minkowski's inequality for the finite sum
  have hsum : MeasureTheory.eLpNorm
        (fun x : ℤ => ∑ n ∈ s, φ (x - (n : ℤ)) * g (x + P.eval (n : ℤ) - (n : ℤ))) 2
        MeasureTheory.Measure.count
      ≤ (s.card : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    have hle := MeasureTheory.eLpNorm_sum_le
      (μ := MeasureTheory.Measure.count) (p := (2 : ENNReal)) (s := s)
      (f := fun n : ℕ => fun x : ℤ => φ (x - (n : ℤ)) * g (x + P.eval (n : ℤ) - (n : ℤ)))
      (by norm_num : (1 : ENNReal) ≤ 2)
    have hFs : (fun x : ℤ => ∑ n ∈ s, φ (x - (n : ℤ)) * g (x + P.eval (n : ℤ) - (n : ℤ)))
        = ∑ n ∈ s,
            (fun x : ℤ => φ (x - (n : ℤ)) * g (x + P.eval (n : ℤ) - (n : ℤ))) := by
      funext x
      exact (Finset.sum_apply x s
        (fun n : ℕ => fun y : ℤ => φ (y - (n : ℤ)) * g (y + P.eval (n : ℤ) - (n : ℤ)))).symm
    rw [hFs]
    refine hle.trans ?_
    calc ∑ n ∈ s, MeasureTheory.eLpNorm
          (fun x : ℤ => φ (x - (n : ℤ)) * g (x + P.eval (n : ℤ) - (n : ℤ))) 2
          MeasureTheory.Measure.count
        ≤ ∑ n ∈ s, MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
          Finset.sum_le_sum hterm
      _ = (s.card : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- the norm of the normalising scalar
  have hnorm : ‖(((N : ℝ)⁻¹ : ℝ) : ℂ)‖ = (N : ℝ)⁻¹ := by
    rw [show (((N : ℝ)⁻¹ : ℝ) : ℂ) = ((N : ℂ))⁻¹ by push_cast; ring]
    rw [norm_inv, Complex.norm_natCast]
  have hcoefnorm : ‖(((N : ℝ)⁻¹ : ℝ) : ℂ)‖ₑ * (s.card : ENNReal)
      = ENNReal.ofReal ((N : ℝ)⁻¹ * (s.card : ℝ)) := by
    rw [← _root_.ofReal_norm, hnorm, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹)]
  calc MeasureTheory.eLpNorm
        (fun x : ℤ => Work.Analysis.InverseTheory.AhalfTranspose N P φ g x) 2
        MeasureTheory.Measure.count
      = ‖(((N : ℝ)⁻¹ : ℝ) : ℂ)‖ₑ * MeasureTheory.eLpNorm
          (fun x : ℤ => ∑ n ∈ s, φ (x - (n : ℤ)) * g (x + P.eval (n : ℤ) - (n : ℤ))) 2
          MeasureTheory.Measure.count := by
        rw [hAhalf, MeasureTheory.eLpNorm_const_smul]
    _ ≤ ‖(((N : ℝ)⁻¹ : ℝ) : ℂ)‖ₑ * ((s.card : ENNReal) *
          MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) :=
        mul_le_mul_right hsum _
    _ = (‖(((N : ℝ)⁻¹ : ℝ) : ℂ)‖ₑ * (s.card : ENNReal)) *
          MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by rw [mul_assoc]
    _ = ENNReal.ofReal ((N : ℝ)⁻¹ * (s.card : ℝ)) *
          MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by rw [hcoefnorm]
    _ ≤ 1 * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
        mul_le_mul_left (ENNReal.ofReal_le_one.mpr hcoef) _
    _ = MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := one_mul _

end Work.KMTAreas.A4
