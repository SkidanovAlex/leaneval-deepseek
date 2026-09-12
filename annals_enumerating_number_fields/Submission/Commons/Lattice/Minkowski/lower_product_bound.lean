import Mathlib
import Submission.Commons.Lattice.SuccessiveMinima.Basic
import Submission.Commons.Lattice.SuccessiveMinima.realisation_linearIndependent
import Submission.Commons.Lattice.Minkowski.covol_span_wedge
import Submission.Commons.Lattice.Minkowski.covolume_le_covolume_of_le
import Submission.Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
import Submission.Commons.Lattice.Discrete.discreteTopology_span_linIndep

noncomputable section

open Set Filter Metric MeasureTheory Module BigOperators
open scoped ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Commons.Lattice.Minkowski

/-- Finite-product bound: `∏ᵢ(bᵢ+ε) ≤ ∏ᵢbᵢ + ε·m·∏ᵢ(bᵢ+1)` for `0 ≤ bᵢ`, `0 ≤ ε ≤ 1`,
by induction on `m` (`Fin.prod_univ_succ`). -/
private lemma fin_prod_add_le_add : ∀ (m : ℕ) (b : Fin m → ℝ) (ε : ℝ),
    (∀ i : Fin m, 0 ≤ b i) → 0 ≤ ε → ε ≤ 1 →
      (∏ i : Fin m, (b i + ε)) ≤
        (∏ i : Fin m, b i) + ε * (m : ℝ) * (∏ i : Fin m, (b i + 1)) := by
  intro m
  induction m with
  | zero =>
      intro b ε hb hε0 hε1
      simp
  | succ m ih =>
      intro b ε hb hε0 hε1
      let b0 : ℝ := b 0
      let c : Fin m → ℝ := fun i => b i.succ
      let S : ℝ := ∏ i : Fin m, (c i + ε)
      let B : ℝ := ∏ i : Fin m, c i
      let D : ℝ := ∏ i : Fin m, (c i + 1)
      have hc : ∀ i : Fin m, 0 ≤ c i := by
        intro i
        exact hb i.succ
      have hih := ih c ε hc hε0 hε1
      have hSD : S ≤ D := by
        dsimp [S, D]
        refine Finset.prod_le_prod ?_ ?_
        · intro i hi
          exact add_nonneg (hc i) hε0
        · intro i hi
          linarith [hε1]
      have hD0 : 0 ≤ D := by
        dsimp [D]
        exact Finset.prod_nonneg (fun i hi => by linarith [hc i])
      have hb00 : 0 ≤ b0 := by
        dsimp [b0]
        exact hb 0
      rw [Fin.prod_univ_succ]
      rw [Fin.prod_univ_succ]
      rw [Fin.prod_univ_succ]
      change (b0 + ε) * S ≤ b0 * B + ε * ((m + 1 : ℕ) : ℝ) * ((b0 + 1) * D)
      rw [Nat.cast_add, Nat.cast_one]
      calc
        (b0 + ε) * S = b0 * S + ε * S := by ring
        _ ≤ (b0 * B + (b0 * ε) * (m : ℝ) * D) + ε * D := by
              have hA : b0 * S ≤ b0 * B + (b0 * ε) * (m : ℝ) * D := by
                have h := mul_le_mul_of_nonneg_left hih hb00
                nlinarith
              have hB : ε * S ≤ ε * D := mul_le_mul_of_nonneg_left hSD hε0
              nlinarith
        _ = b0 * B + ε * (((m : ℝ) * b0) + 1) * D := by ring
        _ ≤ b0 * B + ε * (((m : ℝ) + 1) * (b0 + 1)) * D := by
              have hcoef : (m : ℝ) * b0 + 1 ≤ ((m : ℝ) + 1) * (b0 + 1) := by
                have hM0 : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
                nlinarith [hM0, hb00]
              have hεD : 0 ≤ ε * D := mul_nonneg hε0 hD0
              nlinarith
        _ = b0 * B + ε * ((m : ℝ) + 1) * ((b0 + 1) * D) := by ring

/-! Prove the LOWER (Hadamard/trivial) half of Minkowski's second theorem:
`covol(L) ≤ ∏ᵢ λᵢ(L)` for a full lattice in `EuclideanSpace ℝ (Fin n)`.
Hints: realise independent vectors with `exists_linearIndependent_of_successiveMinimum` at
radius λᵢ + ε; let L₀ = ℤ-span of their ambient images; chain
`covol L ≤ covol L₀` (`covolume_le_covolume_of_le`, L₀ = ℤ-span of the ℝ-basis, instances for
the span-of-basis via `Basis.mk` + `span_top_of_linearIndependent`), `covol L₀ = ‖ιMulti v‖`
(`covol_span_wedge`), `≤ ∏ᵢ‖vᵢ‖` (`exteriorPower_norm_wedge_le_prod`), `≤ ∏ᵢ (λᵢ+ε)`; then
take ε → 0: prove the finite-product bound `∏ᵢ(bᵢ+ε) ≤ ∏ᵢbᵢ + ε·n·∏ᵢ(bᵢ+1)` for
0 ≤ bᵢ, 0 ≤ ε ≤ 1 by induction on n (`Fin.prod_univ_succ`), then feed ε := min 1 (δ/(C+1))
and finish with `le_of_forall_pos_le_add`. λᵢ ≥ 0 via `successiveMinimum_nonneg`. -/
theorem lower_product_bound (n : ℕ) (hn : 0 < n)
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : Module.finrank ℤ L = n) :
    ZLattice.covolume L ≤
      ∏ i : Fin n, Commons.Lattice.SuccessiveMinima.successiveMinimum L (i.val + 1) := by
  classical
  let b : Fin n → ℝ := fun i => Commons.Lattice.SuccessiveMinima.successiveMinimum L (i.val + 1)
  let C : ℝ := (Fintype.card (Fin n) : ℝ) * ∏ i : Fin n, (b i + 1)
  have hb_nonneg : ∀ i : Fin n, 0 ≤ b i := by
    intro i
    exact Commons.Lattice.SuccessiveMinima.successiveMinimum_nonneg L (i.val + 1)
      (by rw [hL]; omega)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Nat.cast_nonneg _)
      (Finset.prod_nonneg (fun i hi => by linarith [hb_nonneg i]))
  have hCpos : 0 < C + 1 := by linarith
  -- For every 0 < ε ≤ 1 the covolume is bounded by the product of the perturbed minima.
  have hmain : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ZLattice.covolume L ≤ ∏ i : Fin n, (b i + ε) := by
    intro ε hε hε1
    obtain ⟨v, hvLI, hvbd⟩ :=
      Commons.Lattice.SuccessiveMinima.exists_linearIndependent_of_successiveMinimum
        (E := Euclid n) L n hL (ε := ε) hε
    let w : Fin n → Euclid n := fun j => (v j : Euclid n)
    have hwLI : LinearIndependent ℝ w := by simpa [w] using hvLI
    have hvbd' : ∀ j : Fin n, ‖w j‖ ≤ b j + ε := by
      intro j
      simpa [w, b] using hvbd j
    let L₀ : Submodule ℤ (Euclid n) := Submodule.span ℤ (Set.range w)
    have hL0_le_L : L₀ ≤ L := by
      apply Submodule.span_le.mpr
      rintro x ⟨j, rfl⟩
      exact (v j).2
    letI : DiscreteTopology L₀ := by
      exact Commons.Lattice.Discrete.discreteTopology_span_linIndep (n := n) (k := n) w hwLI
    have hspan_top : ⊤ ≤ Submodule.span ℝ ((L₀ : Submodule ℤ (Euclid n)) : Set (Euclid n)) := by
      calc
        ⊤ ≤ Submodule.span ℝ (Set.range w) :=
              Commons.Lattice.Minkowski.span_top_of_linearIndependent w hwLI
        _ ≤ Submodule.span ℝ ((L₀ : Submodule ℤ (Euclid n)) : Set (Euclid n)) := by
              apply Submodule.span_mono
              intro x hx
              exact Submodule.subset_span hx
    have hspan_eq : Submodule.span ℝ ((L₀ : Submodule ℤ (Euclid n)) : Set (Euclid n)) = ⊤ :=
      eq_top_iff.mpr hspan_top
    letI : IsZLattice ℝ L₀ := ⟨hspan_eq⟩
    have hcov0 : ZLattice.covolume L ≤ ZLattice.covolume L₀ := by
      exact Commons.Lattice.Minkowski.covolume_le_covolume_of_le (L₁ := L₀) (L₂ := L) hL0_le_L
    have hcovw : ZLattice.covolume L₀ = ‖exteriorPower.ιMulti ℝ n w‖ := by
      simpa [L₀] using (Commons.Lattice.Minkowski.covol_span_wedge n hn w hwLI)
    have hwedge : ‖exteriorPower.ιMulti ℝ n w‖ ≤ ∏ i : Fin n, ‖w i‖ :=
      Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod w
    have hnorm : (∏ i : Fin n, ‖w i‖) ≤ ∏ i : Fin n, (b i + ε) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro i hi
        exact norm_nonneg (w i)
      · intro i hi
        exact hvbd' i
    calc
      ZLattice.covolume L ≤ ZLattice.covolume L₀ := hcov0
      _ = ‖exteriorPower.ιMulti ℝ n w‖ := hcovw
      _ ≤ ∏ i : Fin n, ‖w i‖ := hwedge
      _ ≤ ∏ i : Fin n, (b i + ε) := hnorm
  -- feed ε := min 1 (δ / (C + 1)) and finish with `le_of_forall_pos_le_add`
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε : ℝ := min 1 (δ / (C + 1))
  have hε0 : 0 < ε := by
    dsimp [ε]
    exact lt_min (by norm_num) (div_pos hδ hCpos)
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    exact min_le_left _ _
  have hεle : ε ≤ δ / (C + 1) := by
    dsimp [ε]
    exact min_le_right _ _
  have hcov := hmain ε hε0 hε1
  have hprod := fin_prod_add_le_add n b ε hb_nonneg hε0.le hε1
  have hcard : (Fintype.card (Fin n) : ℝ) = (n : ℝ) := by simp
  rw [← hcard] at hprod
  have hεC : ε * C ≤ δ := by
    have h1 : ε * C ≤ ε * (C + 1) := by
      exact mul_le_mul_of_nonneg_left (by linarith) hε0.le
    have h2 : ε * (C + 1) ≤ δ := by
      exact (le_div_iff₀ hCpos).mp hεle
    exact le_trans h1 h2
  calc
    ZLattice.covolume L ≤ ∏ i : Fin n, (b i + ε) := hcov
    _ ≤ (∏ i : Fin n, b i) + ε * C := by
          -- hprod : ∏(b+ε) ≤ ∏b + ε·(n:ℝ)·∏(b+1); C = (Fintype.card : ℝ)·∏(b+1)
          dsimp [C]
          simpa [mul_assoc] using hprod
    _ ≤ (∏ i : Fin n, b i) + δ := by linarith

end Commons.Lattice.Minkowski
