import Mathlib
import Submission.Work.Peluse.UControl.peluseFamily

/-!
# The trivial `ℓ¹`-bound for the multilinear progression average `LambdaMD`

`LambdaMD N M P F` is the multilinear average of Peluse's §3 for the full polynomial progression
`(x, x + y, x + y², …, x + y^{d-1}, x + P(y))` (`d = P.natDegree`):

`Λ = (N M)⁻¹ ∑_x F_0(x) ∑_{y ∈ [M]} (∏_{i<d-1} F_{i+1}(x + y^{i+1})) · F_d(x + P(y))`.

This file proves the elementary `ℓ¹`-bound `‖Λ‖ ≤ ‖F_d‖_{ℓ¹} / N`, which is the "trivial" input
`(anf)` of the PET step: the normalisation `(N M)⁻¹` is cleared by the `M` terms of the `y`-sum, and
the remaining `N⁻¹` is paid by the `x`-sum, all the factors other than `F_d` being `1`-bounded.

The argument is the triangle inequality, in the form used by `Work.Peluse.Pairing.lambdaZ_l1_mass`:
all the `F_i` (`i ≠ d`) are `1`-bounded, each `y` contributes at most `∑_x ‖F_d x‖` (the shift
`x ↦ x + P(y)` is injective and `F_d` is supported in `[-N,N]`), and there are `M` values of `y`.
-/

open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-- The `x`-integrand of `LambdaMD`: the inner multilinear average along the progression
`(x, x + y, x + y², …, x + y^{d-1}, x + P(y))`, `d = P.natDegree`. -/
def mdIntegrand (M : ℕ) (P : Polynomial ℤ) (F : Fin (P.natDegree + 1) → ℤ → ℂ) (x : ℤ) : ℂ :=
  F ⟨0, Nat.succ_pos _⟩ x * ∑ y ∈ Finset.Icc 1 M,
    (∏ i : Fin (P.natDegree - 1), F ⟨i.val + 1, by omega⟩ (x + (y : ℤ) ^ (i.val + 1))) *
    F ⟨P.natDegree, Nat.lt_succ_self _⟩ (x + P.eval (y : ℤ))

/-- `LambdaMD` is its normalisation times the `ℓ¹`-sum of `mdIntegrand`. -/
lemma lambdaMD_eq (N M : ℕ) (P : Polynomial ℤ) (F : Fin (P.natDegree + 1) → ℤ → ℂ) :
    LambdaMD N M P F = ((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, mdIntegrand M P F x := rfl

/-- `symIcc L` is the set of integers of `natAbs ≤ L`. -/
private lemma mem_symIcc_iff_natAbs {L : ℕ} {x : ℤ} :
    x ∈ symIcc L ↔ x.natAbs ≤ L := by
  rw [symIcc, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h : |x| ≤ (L : ℤ) := abs_le.mpr ⟨h1, h2⟩
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  · intro h
    have h' : |x| ≤ (L : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h
    exact abs_le.mp h'

/-- Shifting the argument by `q` maps `symIcc N` into the support of `g`, so the `ℓ¹`-mass over the
support is bounded by the total `ℓ¹`-mass: `∑_{x ∈ symIcc N} ‖g (x + q)‖ ≤ ∑' x, ‖g x‖`. -/
private lemma sum_shift_le_tsum {g : ℤ → ℂ} {N : ℕ} (hg : SupportIn g N) (q : ℤ) :
    ∑ x ∈ symIcc N, ‖g (x + q)‖ ≤ ∑' x : ℤ, ‖g x‖ := by
  have hfin : (∑' x : ℤ, ‖g x‖) = ∑ x ∈ symIcc N, ‖g x‖ := by
    rw [tsum_eq_sum (s := symIcc N)]
    intro x hx
    have h1 : ¬ (x.natAbs ≤ N) := fun h2 => hx (mem_symIcc_iff_natAbs.mpr h2)
    rw [hg x (not_le.mp h1), norm_zero]
  rw [hfin]
  set T : Finset ℤ := (symIcc N).filter (fun x => (x + q).natAbs ≤ N) with hT
  have hTsub : T ⊆ symIcc N := Finset.filter_subset _ _
  have h_eq : ∑ x ∈ T, ‖g (x + q)‖ = ∑ x ∈ symIcc N, ‖g (x + q)‖ := by
    apply Finset.sum_subset hTsub
    intro x hxA hxT
    have hxq : ¬ ((x + q).natAbs ≤ N) := by
      intro hp
      exact hxT (by rw [hT]; exact Finset.mem_filter.mpr ⟨hxA, hp⟩)
    rw [hg (x + q) (not_le.mp hxq), norm_zero]
  have hinj : Set.InjOn (fun x : ℤ => x + q) (↑T : Set ℤ) := by
    intro a _ b _ hab
    exact add_right_cancel hab
  have himg : T.image (fun x : ℤ => x + q) ⊆ symIcc N := by
    intro z hz
    obtain ⟨x, hxT, rfl⟩ := Finset.mem_image.mp hz
    rw [mem_symIcc_iff_natAbs]
    exact (Finset.mem_filter.mp hxT).2
  calc ∑ x ∈ symIcc N, ‖g (x + q)‖ = ∑ x ∈ T, ‖g (x + q)‖ := h_eq.symm
    _ = ∑ z ∈ T.image (fun x : ℤ => x + q), ‖g z‖ := by rw [Finset.sum_image hinj]
    _ ≤ ∑ z ∈ symIcc N, ‖g z‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun z _ _ => norm_nonneg _)

/-- The arithmetic of the normalisation: `(a m)⁻¹ (m s) ≤ s / a` for `a > 0`, `m, s ≥ 0`.  (For
`m > 0` this is an equality, for `m = 0` both sides are `0` resp. nonnegative.) -/
private lemma inv_mul_mul_le_div {a m s : ℝ} (ha : 0 < a) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    (a * m)⁻¹ * (m * s) ≤ s / a := by
  rcases eq_or_lt_of_le hm with h | h
  · subst h
    rw [mul_zero, inv_zero, zero_mul]
    exact div_nonneg hs ha.le
  · have hm0 : m ≠ 0 := ne_of_gt h
    rw [div_eq_mul_inv]
    field_simp
    exact le_refl s

/-- **The trivial `ℓ¹`-bound for `LambdaMD`.**  If all the functions are `1`-bounded and supported in
`[-N,N]`, then `‖LambdaMD‖ ≤ N⁻¹ ∑_x ‖F_d(x)‖`: the `M` values of `y` cancel the normalisation
`M⁻¹`, and the injective shift `x ↦ x + P(y)` turns the `x`-sum into at most the full `ℓ¹`-mass of
`F_d`. -/
theorem lambdaMD_le_l1 (N M : ℕ) (P : Polynomial ℤ) (F : Fin (P.natDegree + 1) → ℤ → ℂ)
    (hN : 0 < N) (hFb : ∀ i x, ‖F i x‖ ≤ 1) (hFs : ∀ i, SupportIn (F i) N) :
    ‖LambdaMD N M P F‖
      ≤ (∑' x : ℤ, ‖F ⟨P.natDegree, Nat.lt_succ_self P.natDegree⟩ x‖) / N := by
  set S : ℝ := ∑' x : ℤ, ‖F ⟨P.natDegree, Nat.lt_succ_self P.natDegree⟩ x‖ with hSdef
  have hSnn : 0 ≤ S := by rw [hSdef]; exact tsum_nonneg fun x => norm_nonneg _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [lambdaMD_eq, norm_mul, norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have htsum : ‖∑' x : ℤ, mdIntegrand M P F x‖ ≤ (M : ℝ) * S := by
    rw [tsum_eq_sum (s := symIcc N) (by
      intro x hx
      have hxN : N < x.natAbs := not_le.mp fun h => hx (mem_symIcc_iff_natAbs.mpr h)
      rw [mdIntegrand, hFs ⟨0, Nat.succ_pos _⟩ x hxN, zero_mul])]
    calc ‖∑ x ∈ symIcc N, mdIntegrand M P F x‖
        ≤ ∑ x ∈ symIcc N, ‖mdIntegrand M P F x‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ symIcc N, ∑ y ∈ Finset.Icc 1 M,
            ‖F ⟨P.natDegree, Nat.lt_succ_self P.natDegree⟩ (x + P.eval (y : ℤ))‖ := by
          apply Finset.sum_le_sum
          intro x _
          unfold mdIntegrand
          rw [norm_mul]
          refine le_trans (mul_le_mul_of_nonneg_right (hFb _ _) (norm_nonneg _)) ?_
          rw [one_mul]
          refine le_trans (norm_sum_le _ _) ?_
          apply Finset.sum_le_sum
          intro y _
          rw [norm_mul]
          refine le_trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) (le_of_eq (one_mul _))
          rw [norm_prod]
          exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hFb _ _)
      _ = ∑ y ∈ Finset.Icc 1 M, ∑ x ∈ symIcc N,
            ‖F ⟨P.natDegree, Nat.lt_succ_self P.natDegree⟩ (x + P.eval (y : ℤ))‖ :=
          Finset.sum_comm
      _ ≤ ∑ y ∈ Finset.Icc 1 M, ∑' x : ℤ,
            ‖F ⟨P.natDegree, Nat.lt_succ_self P.natDegree⟩ x‖ :=
          Finset.sum_le_sum fun y _ => sum_shift_le_tsum (hFs _) (P.eval (y : ℤ))
      _ = (M : ℝ) * S := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
          rw [show M + 1 - 1 = M from by omega, hSdef]
  refine le_trans (mul_le_mul_of_nonneg_left htsum (inv_nonneg.mpr (by positivity))) ?_
  exact inv_mul_mul_le_div hNpos (by positivity) hSnn

end

end Work.Peluse.UControl
