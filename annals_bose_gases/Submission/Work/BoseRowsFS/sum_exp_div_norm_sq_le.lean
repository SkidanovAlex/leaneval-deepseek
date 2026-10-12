import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Submission.Work.BoseRowsFS.card_shell_boxZ_le
import Submission.Work.BoseRowsFS.gauss_tsum_exp_neg_sq_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The mode sum `∑_{j ≠ 0} e^{-‖k_j‖²}/‖k_j‖²` at the box lattice `k_j = (2π/ℓ)·j`

This module proves

`∑'_{j ≠ 0} exp (-‖kvec ℓ j‖²) / ‖kvec ℓ j‖² ≤ 100 ℓ³`   for `ℓ ≥ 1`,

which is the `ℓ³`-gain over the naive `1/‖k‖²` divergence used in the honest-lattice
rows of the dilute Bose-gas development.

The proof notes that `‖kvec ℓ j‖ = c ‖vecZ j‖` with `c = 2π/ℓ`, and that the weight
`1/‖vecZ j‖²` is bounded by `1/maxNat j²`; grouping the lattice points by their
max-norm `k = max_i |j_i|` turns the sum into `Σ_k card(k-shell)·e^{-c²k²}/(c²k²)`,
where the shell has `≤ 26 k²` elements and `∑_k e^{-c²k²} ≤ 1 + 1/c` (integral test
against the Gaussian).  This gives `≤ (26/c²)(1 + 1/c)`, and `c = 2π/ℓ` converts the
latter into `≲ ℓ³`.

The pointwise/grouping argument (`sum_exp_div_norm_sq_partial_le`) bounds *every*
finite partial sum by the same constant, so Weyl's criterion
(`Real.tsum_le_of_sum_le`) gives the bound for the full `tsum`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseRowsFS

set_option autoImplicit false

/-- The Gaussian theta summand is summable for `c > 0` (integral test). -/
lemma summable_exp_neg_sq_nat {c : ℝ} (hcpos : 0 < c) :
    Summable (fun n : ℕ => Real.exp (-(c ^ 2 * (n : ℝ) ^ 2))) := by
  have hanti : AntitoneOn (fun x : ℝ => Real.exp (-(c ^ 2 * x ^ 2))) (Set.Ici 0) := by
    intro x hx y hy hxy
    apply Real.exp_le_exp.mpr
    have hx0 : (0 : ℝ) ≤ x := hx
    have h2 : x ^ 2 ≤ y ^ 2 := by nlinarith [hx0, hxy]
    have h3 : c ^ 2 * x ^ 2 ≤ c ^ 2 * y ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg c)
    linarith
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-(c ^ 2 * x ^ 2))) (Set.Ioi 0) := by
    have hb : (0 : ℝ) < c ^ 2 := by positivity
    refine ((integrable_exp_neg_mul_sq (b := c ^ 2) hb).congr
      (Filter.Eventually.of_forall fun x => ?_)).integrableOn
    simp only [neg_mul]
  exact AntitoneOn.summable_of_integrableOn_Ioi_zero hanti hint (fun t _ => (Real.exp_pos _).le)

/-- **Every finite partial sum is bounded by `(26/c²)(1 + 1/c)`.**

Grouping the nonzero lattice vectors of a finite set `u` by their max-norm `k`,
the shell `{maxNat = k}` injects into `boxZ k \ boxZ (k-1)` (which has `≤ 26k²`
elements), and on the shell the summand is at most `e^{-c²k²}/(c²k²)`. -/
lemma sum_exp_div_norm_sq_partial_le {ℓ c : ℝ} (hℓ0 : 0 < ℓ) (hc : c = 2 * Real.pi / ℓ)
    (u : Finset {j : Fin 3 → ℤ // j ≠ 0}) :
    ∑ j ∈ u, Real.exp (-(‖kvec ℓ j.1‖ ^ 2)) / ‖kvec ℓ j.1‖ ^ 2
      ≤ 26 / c ^ 2 * (1 + 1 / c) := by
  have hcpos : 0 < c := by rw [hc]; positivity
  have hsumm : Summable (fun n : ℕ => Real.exp (-(c ^ 2 * (n : ℝ) ^ 2))) :=
    summable_exp_neg_sq_nat hcpos
  have hpt : ∀ j ∈ u, Real.exp (-(‖kvec ℓ j.1‖ ^ 2)) / ‖kvec ℓ j.1‖ ^ 2
      ≤ Real.exp (-(c ^ 2 * (maxNat j.1 : ℝ) ^ 2)) / (c ^ 2 * (maxNat j.1 : ℝ) ^ 2) := by
    intro j _
    have hk : 1 ≤ maxNat j.1 := maxNat_pos j.2
    have hnorm : ‖kvec ℓ j.1‖ = c * ‖vecZ j.1‖ := by
      rw [hc]; exact norm_kvec hℓ0.le j.1
    have hge : (maxNat j.1 : ℝ) ≤ ‖vecZ j.1‖ := norm_vecZ_ge_maxNat j.1
    have h1 : c * (maxNat j.1 : ℝ) ≤ ‖kvec ℓ j.1‖ := by
      rw [hnorm]; exact mul_le_mul_of_nonneg_left hge hcpos.le
    have h2 : (c * (maxNat j.1 : ℝ)) ^ 2 ≤ ‖kvec ℓ j.1‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have h2' : c ^ 2 * (maxNat j.1 : ℝ) ^ 2 ≤ ‖kvec ℓ j.1‖ ^ 2 := by
      rwa [mul_pow] at h2
    have hexp : Real.exp (-(‖kvec ℓ j.1‖ ^ 2)) ≤ Real.exp (-(c ^ 2 * (maxNat j.1 : ℝ) ^ 2)) := by
      apply Real.exp_le_exp.mpr; linarith
    exact div_le_div₀ (Real.exp_pos _).le hexp (by positivity) h2'
  have hfib := Finset.sum_fiberwise_of_maps_to (s := u)
      (t := u.image (fun j : {j : Fin 3 → ℤ // j ≠ 0} => maxNat j.1))
      (g := fun j : {j : Fin 3 → ℤ // j ≠ 0} => maxNat j.1)
      (f := fun j : {j : Fin 3 → ℤ // j ≠ 0} =>
        Real.exp (-(c ^ 2 * (maxNat j.1 : ℝ) ^ 2)) / (c ^ 2 * (maxNat j.1 : ℝ) ^ 2))
      (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  calc ∑ j ∈ u, Real.exp (-(‖kvec ℓ j.1‖ ^ 2)) / ‖kvec ℓ j.1‖ ^ 2
      ≤ ∑ j ∈ u, Real.exp (-(c ^ 2 * (maxNat j.1 : ℝ) ^ 2)) / (c ^ 2 * (maxNat j.1 : ℝ) ^ 2) :=
        Finset.sum_le_sum hpt
    _ = ∑ k ∈ u.image (fun j : {j : Fin 3 → ℤ // j ≠ 0} => maxNat j.1),
          ∑ j ∈ u.filter (fun j : {j : Fin 3 → ℤ // j ≠ 0} => maxNat j.1 = k),
            Real.exp (-(c ^ 2 * (maxNat j.1 : ℝ) ^ 2)) / (c ^ 2 * (maxNat j.1 : ℝ) ^ 2) :=
        hfib.symm
    _ = ∑ k ∈ u.image (fun j : {j : Fin 3 → ℤ // j ≠ 0} => maxNat j.1),
          ((u.filter (fun j : {j : Fin 3 → ℤ // j ≠ 0} => maxNat j.1 = k)).card : ℝ)
            * (Real.exp (-(c ^ 2 * (k : ℝ) ^ 2)) / (c ^ 2 * (k : ℝ) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2])]
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ u.image (fun j : {j : Fin 3 → ℤ // j ≠ 0} => maxNat j.1),
          (26 * (k : ℝ) ^ 2)
            * (Real.exp (-(c ^ 2 * (k : ℝ) ^ 2)) / (c ^ 2 * (k : ℝ) ^ 2)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk1 : 1 ≤ k := by
          obtain ⟨j, _, hjk⟩ := Finset.mem_image.mp hk
          rw [← hjk]; exact maxNat_pos j.2
        have hsub : (u.filter (fun j : {j : Fin 3 → ℤ // j ≠ 0} => maxNat j.1 = k)).image
              Subtype.val ⊆ (boxZ k) \ (boxZ (k - 1)) := by
          intro x hx
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
          have hjk : maxNat j.1 = k := (Finset.mem_filter.mp hj).2
          rw [Finset.mem_sdiff]
          exact ⟨by rw [mem_boxZ_iff_maxNat_le, hjk],
            by intro hcon; rw [mem_boxZ_iff_maxNat_le] at hcon; omega⟩
        have hcard : (u.filter (fun j : {j : Fin 3 → ℤ // j ≠ 0} => maxNat j.1 = k)).card
            ≤ 26 * k ^ 2 := by
          have h1 := Finset.card_le_card hsub
          rw [Finset.card_image_of_injective _ Subtype.val_injective] at h1
          exact h1.trans (card_shell_boxZ_le k hk1)
        have hcardR : ((u.filter (fun j : {j : Fin 3 → ℤ // j ≠ 0} => maxNat j.1 = k)).card : ℝ)
            ≤ 26 * (k : ℝ) ^ 2 := by exact_mod_cast hcard
        exact mul_le_mul_of_nonneg_right hcardR (by positivity)
    _ = ∑ k ∈ u.image (fun j : {j : Fin 3 → ℤ // j ≠ 0} => maxNat j.1),
          26 / c ^ 2 * Real.exp (-(c ^ 2 * (k : ℝ) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk1 : 1 ≤ k := by
          obtain ⟨j, _, hjk⟩ := Finset.mem_image.mp hk
          rw [← hjk]; exact maxNat_pos j.2
        have hk0 : (k : ℝ) ≠ 0 := by positivity
        have hc0 : c ≠ 0 := ne_of_gt hcpos
        field_simp
    _ = 26 / c ^ 2 * ∑ k ∈ u.image (fun j : {j : Fin 3 → ℤ // j ≠ 0} => maxNat j.1),
          Real.exp (-(c ^ 2 * (k : ℝ) ^ 2)) := by
        rw [Finset.mul_sum]
    _ ≤ 26 / c ^ 2 * (1 + 1 / c) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (hsumm.sum_le_tsum _ (fun i _ => (Real.exp_pos _).le)).trans
          (gauss_tsum_exp_neg_sq_le hcpos)

/-- The numerical endgame: `(26/c²)(1 + 1/c) ≤ 100 ℓ³` for `c = 2π/ℓ`, `ℓ ≥ 1`. -/
lemma const_bound {ℓ c : ℝ} (hℓ : 1 ≤ ℓ) (hℓ0 : 0 < ℓ) (hc : c = 2 * Real.pi / ℓ) :
    26 / c ^ 2 * (1 + 1 / c) ≤ 100 * ℓ ^ 3 := by
  have hcpos : 0 < c := by rw [hc]; positivity
  have hc0 : c ≠ 0 := ne_of_gt hcpos
  have hpi3 : (27 : ℝ) ≤ Real.pi ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) (Real.pi_gt_three.le) 3
    norm_num at h ⊢
    exact h
  have h1 : 26 / c ^ 2 * (1 + 1 / c) = 26 * (c + 1) / c ^ 3 := by field_simp
  rw [h1]
  have hcl : c ≤ 2 * Real.pi := by rw [hc, div_le_iff₀ hℓ0]; nlinarith [Real.pi_pos, hℓ]
  have h2 : 26 * (c + 1) / c ^ 3 ≤ 234 / c ^ 3 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [hcl, Real.pi_lt_four]
  refine h2.trans ?_
  rw [hc, div_le_iff₀ (by positivity)]
  have h3 : 100 * ℓ ^ 3 * (2 * Real.pi / ℓ) ^ 3 = 800 * Real.pi ^ 3 := by
    rw [div_pow]; field_simp; ring
  rw [h3]
  nlinarith [hpi3]

theorem sum_exp_div_norm_sq_le {ℓ : ℝ} (hℓ : 1 ≤ ℓ) :
    (∑' j : {j : Fin 3 → ℤ // j ≠ 0},
        Real.exp (-(‖Work.BoseRowsFS.kvec ℓ j.1‖ ^ 2)) / ‖Work.BoseRowsFS.kvec ℓ j.1‖ ^ 2)
      ≤ 100 * ℓ ^ 3 := by
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le zero_lt_one hℓ
  set c : ℝ := 2 * Real.pi / ℓ with hc
  refine le_trans (Real.tsum_le_of_sum_le
    (f := fun j : {j : Fin 3 → ℤ // j ≠ 0} =>
      Real.exp (-(‖kvec ℓ j.1‖ ^ 2)) / ‖kvec ℓ j.1‖ ^ 2) ?_ ?_)
    (const_bound hℓ hℓ0 hc)
  · intro j
    exact div_nonneg (Real.exp_pos _).le (sq_nonneg _)
  · intro u
    exact sum_exp_div_norm_sq_partial_le hℓ0 hc u

end Work.BoseRowsFS
