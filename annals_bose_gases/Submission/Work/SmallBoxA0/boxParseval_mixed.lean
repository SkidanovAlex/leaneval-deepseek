import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.SmallBoxA0.mixedCoeff_cons
import Submission.Work.SmallBoxA0.sin_parseval_shifted_hasSum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The mixed (per-coordinate cosine/sine) box Parseval identity

`Work.SmallBoxA0.boxParseval_mixed` is the `n`-dimensional Parseval/Plancherel identity
for the mixed tensor basis `∏ᵢ mixedMode ℓ (ε i) (k i)` (a Dirichlet sine mode in the
coordinates with `ε i = true`, a Neumann cosine mode in those with `ε i = false`), with
the normalising weights `∏ᵢ mixedWgt ℓ (ε i) (k i)`.

The proof is by induction on `n`, in exact analogy with the corpus's all-cosine generator
`Commons.Analysis.Fourier.boxParseval_hasSum`: peel off the first coordinate with Fubini
(`setIntegral_boxSet_succ_swap`), use the one-dimensional mixed Parseval for the outer
coordinate and the induction hypothesis for the remaining `n` coordinates, and glue the
two with `HasSum.sigma_of_hasSum` + dominated convergence.  The two ingredients that do
not depend on the induction are proved separately (`sin_parseval_shifted_hasSum`, the
`HasSum` form of the one-dimensional sine Parseval, and `mixedCoeff_cons`, the Fubini
factorisation of a mixed coefficient).
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology BigOperators
open Commons.Analysis.Fourier

namespace Work.SmallBoxA0

/-- `mixedMode ℓ b k` is continuous in `x`. -/
lemma continuous_mixedMode (ℓ : ℝ) (b : Bool) (k : ℕ) :
    Continuous (fun x : ℝ => mixedMode ℓ b k x) := by
  cases b <;> simp [mixedMode] <;> fun_prop

/-- The one-dimensional mixed Parseval identity: for a continuous `g` on `[-ℓ/2, ℓ/2]`
and either a sine (`b = true`) or a cosine (`b = false`) mode family. -/
lemma mixed_parseval_1d {ℓ : ℝ} (hℓ : 0 < ℓ) (b : Bool) {g : ℝ → ℝ} (hg : Continuous g) :
    HasSum (fun k : ℕ => (∫ a in (-(ℓ / 2))..(ℓ / 2), g a * mixedMode ℓ b k a) ^ 2
        / mixedWgt ℓ b k)
      (∫ a in (-(ℓ / 2))..(ℓ / 2), (g a) ^ 2) := by
  cases b
  · simpa [mixedMode, mixedWgt, boxMode, boxWgt] using cos_parseval_scaled_hasSum hℓ hg
  · simpa [mixedMode, mixedWgt] using sin_parseval_shifted_hasSum hℓ hg

/-- The `n`-dimensional mixed box Parseval identity for the box `boxSet n ℓ`. -/
theorem boxParseval_mixed_gen (n : ℕ) :
    ∀ (ℓ : ℝ), 0 < ℓ → ∀ (ε : Fin n → Bool) (F : (Fin n → ℝ) → ℝ), Continuous F →
      HasSum (fun k : Fin n → ℕ =>
          (∫ x in boxSet n ℓ, F x * ∏ i : Fin n, mixedMode ℓ (ε i) (k i) (x i)) ^ 2
            / ∏ i : Fin n, mixedWgt ℓ (ε i) (k i))
        (∫ x in boxSet n ℓ, (F x) ^ 2) := by
  induction n with
  | zero =>
      intro ℓ hℓ ε F hF
      have hg : ∀ k : Fin 0 → ℕ,
          (∫ x in boxSet 0 ℓ, F x * ∏ i : Fin 0, mixedMode ℓ (ε i) (k i) (x i)) ^ 2
              / ∏ i : Fin 0, mixedWgt ℓ (ε i) (k i)
            = (∫ x in boxSet 0 ℓ, F x) ^ 2 := by
        intro k
        simp only [Fin.prod_univ_zero, mul_one, div_one]
      rw [show (fun k : Fin 0 → ℕ =>
            (∫ x in boxSet 0 ℓ, F x * ∏ i : Fin 0, mixedMode ℓ (ε i) (k i) (x i)) ^ 2
              / ∏ i : Fin 0, mixedWgt ℓ (ε i) (k i)) = fun _ => (∫ x in boxSet 0 ℓ, F x) ^ 2
            from funext hg]
      rw [integral_boxSet_zero (fun x => (F x) ^ 2), integral_boxSet_zero F]
      exact hasSum_const_unique
  | succ n ih =>
      intro ℓ hℓ ε F hF
      set A : ℕ → (Fin n → ℝ) → ℝ :=
        fun k0 rest => ∫ a in (-(ℓ / 2))..(ℓ / 2), F (Fin.cons a rest) * mixedMode ℓ (ε 0) k0 a
        with hA
      have hAcont : ∀ k0, Continuous (A k0) := by
        intro k0
        change Continuous (fun rest : Fin n → ℝ =>
          ∫ a in (-(ℓ / 2))..(ℓ / 2), F (Fin.cons a rest) * mixedMode ℓ (ε 0) k0 a)
        exact continuous_parametric_intervalIntegral_general
          (g := fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2) * mixedMode ℓ (ε 0) k0 p.1) (by
            apply Continuous.mul
            · exact hF.comp continuous_cons_prod
            · exact (continuous_mixedMode ℓ (ε 0) k0).comp continuous_fst)
      have hfiber : ∀ k0, HasSum (fun k : Fin n → ℕ =>
          (∫ rest in boxSet n ℓ, A k0 rest * ∏ i : Fin n, mixedMode ℓ (ε i.succ) (k i) (rest i)) ^ 2
            / ∏ i : Fin n, mixedWgt ℓ (ε i.succ) (k i))
          (∫ rest in boxSet n ℓ, (A k0 rest) ^ 2) :=
        fun k0 => ih ℓ hℓ (fun i => ε i.succ) (A k0) (hAcont k0)
      have hlim : ∀ rest : Fin n → ℝ,
          HasSum (fun k0 : ℕ => (A k0 rest) ^ 2 / mixedWgt ℓ (ε 0) k0)
            (∫ a in (-(ℓ / 2))..(ℓ / 2), (F (Fin.cons a rest)) ^ 2) := by
        intro rest
        have hg : Continuous (fun a : ℝ => F (Fin.cons a rest)) :=
          hF.comp (continuous_cons_right rest)
        simpa [hA] using mixed_parseval_1d hℓ (ε 0) hg
      have hval : (∫ x in boxSet (n+1) ℓ, (F x) ^ 2)
          = ∫ rest in boxSet n ℓ, ∫ a in (-(ℓ / 2))..(ℓ / 2), (F (Fin.cons a rest)) ^ 2 := by
        rw [setIntegral_boxSet_succ_swap (n := n) (s := ℓ) (f := fun x => (F x) ^ 2) (hF.pow 2)]
        apply setIntegral_congr_fun (measurableSet_boxSet n ℓ)
        intro rest _
        dsimp only
        exact setIntegral_boxB_eq_interval hℓ (fun a => (F (Fin.cons a rest)) ^ 2)
      have hInt : Integrable (fun rest => ∑' k0 : ℕ, (A k0 rest) ^ 2 / mixedWgt ℓ (ε 0) k0)
          (volume.restrict (boxSet n ℓ)) := by
        have htsum : (fun rest => ∑' k0 : ℕ, (A k0 rest) ^ 2 / mixedWgt ℓ (ε 0) k0)
            = fun rest => ∫ a in (-(ℓ / 2))..(ℓ / 2), (F (Fin.cons a rest)) ^ 2 := by
          funext rest
          exact (hlim rest).tsum_eq
        rw [htsum]
        apply ContinuousOn.integrableOn_compact (isCompact_boxSet n ℓ)
        apply (continuous_parametric_intervalIntegral_general
          (g := fun p : ℝ × (Fin n → ℝ) => (F (Fin.cons p.1 p.2)) ^ 2)
          ((hF.comp continuous_cons_prod).pow 2)).continuousOn
      have hbase : HasSum (fun k0 : ℕ =>
            ∫ rest in boxSet n ℓ, (A k0 rest) ^ 2 / mixedWgt ℓ (ε 0) k0)
          (∫ rest in boxSet n ℓ, ∫ a in (-(ℓ / 2))..(ℓ / 2), (F (Fin.cons a rest)) ^ 2) := by
        refine hasSum_integral_of_dominated_convergence
          (μ := volume.restrict (boxSet n ℓ))
          (F := fun k0 rest => (A k0 rest) ^ 2 / mixedWgt ℓ (ε 0) k0)
          (bound := fun k0 rest => (A k0 rest) ^ 2 / mixedWgt ℓ (ε 0) k0)
          (f := fun rest => ∫ a in (-(ℓ / 2))..(ℓ / 2), (F (Fin.cons a rest)) ^ 2)
          (fun k0 => (((hAcont k0).pow 2).div_const _).aestronglyMeasurable)
          (fun k0 => Filter.Eventually.of_forall (fun rest => le_of_eq (Real.norm_of_nonneg
              (div_nonneg (sq_nonneg _) (le_of_lt (mixedWgt_pos hℓ (ε 0) k0))))))
          (Filter.Eventually.of_forall (fun rest => (hlim rest).summable))
          hInt
          (Filter.Eventually.of_forall hlim)
      have hterm1 : ∀ k0 : ℕ, (1/mixedWgt ℓ (ε 0) k0) * ∫ rest in boxSet n ℓ, (A k0 rest) ^ 2
          = ∫ rest in boxSet n ℓ, (A k0 rest) ^ 2 / mixedWgt ℓ (ε 0) k0 := by
        intro k0
        rw [integral_div]
        ring
      have h1 : HasSum (fun k0 : ℕ =>
            (1/mixedWgt ℓ (ε 0) k0) * ∫ rest in boxSet n ℓ, (A k0 rest) ^ 2)
          (∫ rest in boxSet n ℓ, ∫ a in (-(ℓ / 2))..(ℓ / 2), (F (Fin.cons a rest)) ^ 2) :=
        hbase.congr_fun (fun k0 => hterm1 k0)
      have hnonneg : ∀ p : (Σ _ : ℕ, Fin n → ℕ),
          0 ≤ (1/mixedWgt ℓ (ε 0) p.1) * ((∫ rest in boxSet n ℓ,
              A p.1 rest * ∏ i : Fin n, mixedMode ℓ (ε i.succ) (p.2 i) (rest i)) ^ 2
                / ∏ i : Fin n, mixedWgt ℓ (ε i.succ) (p.2 i)) := by
        intro p
        apply mul_nonneg
        · exact le_of_lt (one_div_pos.mpr (mixedWgt_pos hℓ (ε 0) p.1))
        · exact div_nonneg (sq_nonneg _)
            (le_of_lt (Finset.prod_pos (fun i _ => mixedWgt_pos hℓ (ε i.succ) (p.2 i))))
      have hsigma : HasSum (fun p : (Σ _ : ℕ, Fin n → ℕ) =>
          (1/mixedWgt ℓ (ε 0) p.1) * ((∫ rest in boxSet n ℓ,
              A p.1 rest * ∏ i : Fin n, mixedMode ℓ (ε i.succ) (p.2 i) (rest i)) ^ 2
                / ∏ i : Fin n, mixedWgt ℓ (ε i.succ) (p.2 i)))
          (∫ rest in boxSet n ℓ, ∫ a in (-(ℓ / 2))..(ℓ / 2), (F (Fin.cons a rest)) ^ 2) := by
        refine HasSum.sigma_of_hasSum (f := fun p : (Σ _ : ℕ, Fin n → ℕ) =>
          (1/mixedWgt ℓ (ε 0) p.1) * ((∫ rest in boxSet n ℓ,
              A p.1 rest * ∏ i : Fin n, mixedMode ℓ (ε i.succ) (p.2 i) (rest i)) ^ 2
                / ∏ i : Fin n, mixedWgt ℓ (ε i.succ) (p.2 i))) h1 ?_ ?_
        · intro k0
          exact (hfiber k0).mul_left (1/mixedWgt ℓ (ε 0) k0)
        · refine (summable_sigma_of_nonneg hnonneg).mpr ⟨fun k0 => ?_, ?_⟩
          · exact (hfiber k0).summable.mul_left (1/mixedWgt ℓ (ε 0) k0)
          · refine h1.summable.congr (fun k0 => ?_)
            have heq : (fun y : Fin n → ℕ =>
                (1 / mixedWgt ℓ (ε 0) (⟨k0, y⟩ : (Σ _ : ℕ, Fin n → ℕ)).1) *
                  ((∫ rest in boxSet n ℓ, A (⟨k0, y⟩ : (Σ _ : ℕ, Fin n → ℕ)).1 rest
                    * ∏ i : Fin n, mixedMode ℓ (ε i.succ)
                        ((⟨k0, y⟩ : (Σ _ : ℕ, Fin n → ℕ)).2 i) (rest i)) ^ 2
                    / ∏ i : Fin n, mixedWgt ℓ (ε i.succ)
                        ((⟨k0, y⟩ : (Σ _ : ℕ, Fin n → ℕ)).2 i)))
              = fun y : Fin n → ℕ => (1 / mixedWgt ℓ (ε 0) k0) *
                  ((∫ rest in boxSet n ℓ, A k0 rest
                    * ∏ i : Fin n, mixedMode ℓ (ε i.succ) (y i) (rest i)) ^ 2
                    / ∏ i : Fin n, mixedWgt ℓ (ε i.succ) (y i)) := by
              funext y; rfl
            rw [heq, tsum_mul_left, (hfiber k0).tsum_eq]
      have hprod : HasSum (fun p : ℕ × (Fin n → ℕ) =>
          (1/mixedWgt ℓ (ε 0) p.1) * ((∫ rest in boxSet n ℓ,
              A p.1 rest * ∏ i : Fin n, mixedMode ℓ (ε i.succ) (p.2 i) (rest i)) ^ 2
                / ∏ i : Fin n, mixedWgt ℓ (ε i.succ) (p.2 i)))
          (∫ rest in boxSet n ℓ, ∫ a in (-(ℓ / 2))..(ℓ / 2), (F (Fin.cons a rest)) ^ 2) :=
        (Equiv.hasSum_iff (Equiv.sigmaEquivProd ℕ (Fin n → ℕ)).symm).mpr hsigma
      have hfin : HasSum (fun K : Fin (n+1) → ℕ =>
          (1/mixedWgt ℓ (ε 0) (K 0)) * ((∫ rest in boxSet n ℓ,
              A (K 0) rest * ∏ i : Fin n, mixedMode ℓ (ε i.succ) (K i.succ) (rest i)) ^ 2
                / ∏ i : Fin n, mixedWgt ℓ (ε i.succ) (K i.succ)))
          (∫ rest in boxSet n ℓ, ∫ a in (-(ℓ / 2))..(ℓ / 2), (F (Fin.cons a rest)) ^ 2) :=
        (Equiv.hasSum_iff (Fin.insertNthEquiv (fun _ : Fin (n+1) => ℕ) 0)).mp hprod
      rw [hval]
      refine hfin.congr_fun (fun K => ?_)
      have hK : (Fin.cons (K 0) (fun i => K i.succ) : Fin (n+1) → ℕ) = K := Fin.cons_self_tail K
      have hKe : (Fin.cons (ε 0) (fun i => ε i.succ) : Fin (n+1) → Bool) = ε :=
        Fin.cons_self_tail ε
      have hc := mixedCoeff_cons hℓ (ε 0) (fun i => ε i.succ) (K 0) (fun i => K i.succ) F hF
      have hw := mixedWgt_prod_cons (ℓ := ℓ) (ε 0) (fun i => ε i.succ) (K 0)
        (fun i => K i.succ)
      rw [hK, hKe] at hc hw
      rw [hc, hw]
      simp only [hA]
      have hw0 : mixedWgt ℓ (ε 0) (K 0) ≠ 0 := mixedWgt_ne_zero hℓ _ _
      have hP : (∏ i : Fin n, mixedWgt ℓ (ε i.succ) (K i.succ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i _ => mixedWgt_ne_zero hℓ _ _)
      field_simp

/-- **The mixed box Parseval identity** (the requested statement). -/
theorem boxParseval_mixed (n : ℕ) (ℓ : ℝ) (hℓ : 0 < ℓ) (ε : Fin n → Bool)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    HasSum (fun k : Fin n → ℕ =>
        (∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (-(ℓ / 2)) (ℓ / 2)),
            F x * ∏ i : Fin n, Work.SmallBoxA0.mixedMode ℓ (ε i) (k i) (x i)) ^ 2
          / ∏ i : Fin n, Work.SmallBoxA0.mixedWgt ℓ (ε i) (k i))
      (∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (-(ℓ / 2)) (ℓ / 2)), (F x) ^ 2) := by
  simpa [boxSet, boxB] using boxParseval_mixed_gen n ℓ hℓ ε F hF

end Work.SmallBoxA0
