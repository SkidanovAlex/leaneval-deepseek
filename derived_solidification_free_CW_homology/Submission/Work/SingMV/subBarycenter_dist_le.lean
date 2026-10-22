import Mathlib
import Submission.Work.SINGMV.Defs

/-!
# The mesh of the barycentric subdivision shrinks: `subBarycenter_dist_le`

Let `q : Fin m → Δⁿ` be a tuple of points of the standard `n`-simplex which are pairwise at
distance at most `d` in the sup metric on `ℝ^{n+1}` (i.e. after applying `toE`). For nonempty
`A ⊆ B ⊆ Fin m` let `b_A`, `b_B` be the barycenters of the corresponding subsets of the tuple,
i.e. the convex combinations of the `q i` with weights `1/|A|` on `A` and `1/|B|` on `B`. Then

  `dist (toE b_A) (toE b_B) ≤ (|B| - 1)/|B| * d`.

This is the elementary metric estimate behind the fact that the mesh of a singular simplex shrinks
by a factor `n/(n+1)` under one barycentric subdivision step, hence tends to `0` under iteration.

## Proof

Writing `c i` for the `j`-th coordinate of `toE (q i)`, the `j`-th coordinate of `toE b_A` is the
average `(1/|A|) ∑_{i ∈ A} c i` of `c` over `A`, and similarly for `B`; so it suffices to bound
the difference of the two averages coordinatewise. The key identity is

  `avg_B - avg_A = (1/|B|) ∑_{i ∈ B \ A} (c i - avg_A)`,

because `∑_{i ∈ B} (c i - avg_A) = ∑_{i ∈ B \ A} (c i - avg_A)` (the terms over `A` cancel, as
`avg_A` is their average). Since every `c i` with `i ∈ B` is within `d` of `avg_A` — the latter is
the average of the `c j`, `j ∈ A ⊆ B`, all of which are within `d` of `c i` — the triangle
inequality gives `|avg_B - avg_A| ≤ (|B| - |A|)/|B| * d ≤ (|B| - 1)/|B| * d`, using `A ≠ ∅`.
-/

noncomputable section

open Convexity

namespace Work.SingMV

/-- Coordinates of the barycenter of a finite set: the weight that
`Convexity.StdSimplex.subBarycenter A hA` puts on `i` is `1/|A|` for `i ∈ A` and `0` otherwise. -/
private lemma subBarycenter_weights_apply {m : ℕ} (A : Finset (Fin m)) (hA : A.Nonempty)
    (i : Fin m) :
    (Convexity.StdSimplex.subBarycenter A hA).weights i
      = if i ∈ A then (A.card : ℝ)⁻¹ else 0 := by
  rw [Convexity.StdSimplex.weights_subBarycenter]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

/-- The `j`-th coordinate of the convex combination with weights the barycenter of `A` is the
average of the `j`-th coordinates of the `q i` over `i ∈ A`. -/
private lemma toE_iConvexComb_subBarycenter {m n : ℕ}
    (q : Fin m → Convexity.StdSimplex ℝ (Fin (n+1)))
    (A : Finset (Fin m)) (hA : A.Nonempty) (j : Fin (n+1)) :
    Work.SingMV.toE (Convexity.iConvexComb (R := ℝ) (Convexity.StdSimplex.subBarycenter A hA) q) j
      = (A.card : ℝ)⁻¹ * ∑ i ∈ A, Work.SingMV.toE (q i) j := by
  show (Convexity.iConvexComb (R := ℝ) (Convexity.StdSimplex.subBarycenter A hA) q).weights j = _
  rw [Work.SingMV.weights_iConvexComb_apply]
  simp only [subBarycenter_weights_apply, Work.SingMV.toE, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

/-- **Difference of averages of a pairwise close family of reals.** If all elements indexed by a
finite set `B` are pairwise at distance at most `d`, then the average of `c` over a nonempty
subset `A ⊆ B` is within `(|B| - 1)/|B| * d` of the average over `B`. -/
private lemma abs_avg_sub_avg_le {ι : Type*} [DecidableEq ι] (A B : Finset ι) (hA : A.Nonempty)
    (hB : B.Nonempty) (hAB : A ⊆ B) (c : ι → ℝ) (d : ℝ)
    (hclose : ∀ i ∈ B, ∀ j ∈ B, |c i - c j| ≤ d) :
    |(A.card : ℝ)⁻¹ * ∑ i ∈ A, c i - (B.card : ℝ)⁻¹ * ∑ i ∈ B, c i|
      ≤ ((B.card : ℝ) - 1) / B.card * d := by
  have hd0 : 0 ≤ d := by
    obtain ⟨i, hi⟩ := hB
    exact le_trans (abs_nonneg _) (hclose i hi i hi)
  have ha1 : 1 ≤ A.card := Finset.card_pos.mpr hA
  have haR : ((A.card : ℕ) : ℝ) ≠ 0 := by
    have h : (0 : ℕ) < A.card := Finset.card_pos.mpr hA
    exact_mod_cast (Nat.pos_iff_ne_zero.mp h)
  have hkR : ((B.card : ℕ) : ℝ) ≠ 0 := by
    have h : (0 : ℕ) < B.card := Finset.card_pos.mpr hB
    exact_mod_cast (Nat.pos_iff_ne_zero.mp h)
  set bA : ℝ := (A.card : ℝ)⁻¹ * ∑ i ∈ A, c i with hbA
  set bB : ℝ := (B.card : ℝ)⁻¹ * ∑ i ∈ B, c i with hbB
  have hbA' : ∑ i ∈ A, c i = (A.card : ℝ) * bA := by
    rw [hbA]; field_simp
  -- Every `c i`, `i ∈ B`, is within `d` of the average `bA` over `A`.
  have hstep1 : ∀ i ∈ B, |c i - bA| ≤ d := by
    intro i hi
    have hci : c i - bA = (A.card : ℝ)⁻¹ * ∑ j ∈ A, (c i - c j) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hbA]
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ haR, one_mul]
    rw [hci, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
    calc (A.card : ℝ)⁻¹ * |∑ j ∈ A, (c i - c j)|
        ≤ (A.card : ℝ)⁻¹ * ∑ j ∈ A, |c i - c j| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
            (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ ≤ (A.card : ℝ)⁻¹ * ∑ j ∈ A, d :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun j hj => hclose i hi j (hAB hj))
            (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = d := by rw [Finset.sum_const, nsmul_eq_mul]; field_simp
  -- The averages differ by the average of `c i - bA` over `B \ A`.
  have hsub : bB - bA = (B.card : ℝ)⁻¹ * ∑ i ∈ B \ A, (c i - bA) := by
    have h1 : ∑ i ∈ A, (c i - bA) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hbA']
      ring
    have h2 : ∑ i ∈ B, (c i - bA) = ∑ i ∈ B \ A, (c i - bA) := by
      have hs := Finset.sum_sdiff (s₁ := A) (s₂ := B) (f := fun i => c i - bA) hAB
      rw [h1, add_zero] at hs
      exact hs.symm
    have h3 : ∑ i ∈ B, c i = ∑ i ∈ B \ A, (c i - bA) + (B.card : ℝ) * bA := by
      have h4 := Finset.sum_sub_distrib (s := B) c (fun _ => bA)
      rw [Finset.sum_const, nsmul_eq_mul] at h4
      rw [h2] at h4
      linarith
    rw [hbB, h3]
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hkR, one_mul]
    ring
  have hca : ((B \ A).card : ℝ) = (B.card : ℝ) - A.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAB, Nat.cast_sub (Finset.card_le_card hAB)]
  have hka : ((B.card : ℝ) - A.card) ≤ ((B.card : ℝ) - 1) := by
    have : (1 : ℝ) ≤ A.card := by exact_mod_cast ha1
    linarith
  have hkinv : 0 ≤ (B.card : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  rw [abs_sub_comm, hsub, abs_mul, abs_of_nonneg hkinv]
  calc (B.card : ℝ)⁻¹ * |∑ i ∈ B \ A, (c i - bA)|
      ≤ (B.card : ℝ)⁻¹ * ∑ i ∈ B \ A, |c i - bA| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hkinv
    _ ≤ (B.card : ℝ)⁻¹ * ∑ i ∈ B \ A, d :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i hi => hstep1 i (Finset.sdiff_subset hi))
          hkinv
    _ = (B.card : ℝ)⁻¹ * (((B \ A).card : ℝ) * d) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((B.card : ℝ) - A.card) * (B.card : ℝ)⁻¹ * d := by
        rw [hca]; ring
    _ ≤ ((B.card : ℝ) - 1) * (B.card : ℝ)⁻¹ * d :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hka hkinv) hd0
    _ = ((B.card : ℝ) - 1) / B.card * d := by rw [div_eq_mul_inv]

/-- **The mesh shrinks under a barycentric subdivision step.** If the vertices `q i` of a simplex
of the subdivision are pairwise at distance at most `d`, then the barycenters of two nested
nonempty vertex sets `A ⊆ B` are at distance at most `(B.card - 1)/B.card * d`. Applied to the
full subdivision simplex (whose vertex sets are the increasing chains in the barycentric
subdivision) this gives the classical factor `n/(n+1)` for an `n`-simplex. -/
theorem subBarycenter_dist_le {m n : ℕ} (q : Fin m → Convexity.StdSimplex ℝ (Fin (n+1))) (d : ℝ)
    (hd : ∀ i j, dist (Work.SingMV.toE (q i)) (Work.SingMV.toE (q j)) ≤ d)
    {A B : Finset (Fin m)} (hA : A.Nonempty) (hB : B.Nonempty) (hAB : A ⊆ B) :
    dist (Work.SingMV.toE (Convexity.iConvexComb (R := ℝ) (Convexity.StdSimplex.subBarycenter A hA) q))
        (Work.SingMV.toE (Convexity.iConvexComb (R := ℝ) (Convexity.StdSimplex.subBarycenter B hB) q))
      ≤ ((B.card : ℝ) - 1) / B.card * d := by
  have hne := hA
  obtain ⟨i₀, hi₀⟩ := hne
  have hd0 : 0 ≤ d := le_trans dist_nonneg (hd i₀ i₀)
  have hk1 : 1 ≤ B.card := Finset.card_pos.mpr hB
  have hkR : (1 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hk1
  have hc : 0 ≤ ((B.card : ℝ) - 1) / B.card * d := by
    have h1 : 0 ≤ (B.card : ℝ) - 1 := by linarith
    have h2 : (0 : ℝ) < (B.card : ℝ) := by linarith
    exact mul_nonneg (div_nonneg h1 (le_of_lt h2)) hd0
  -- compare the two points coordinatewise in the sup metric on `ℝ^{n+1}`
  refine (dist_pi_le_iff hc).2 fun j => ?_
  rw [Real.dist_eq, toE_iConvexComb_subBarycenter q A hA j,
    toE_iConvexComb_subBarycenter q B hB j]
  refine abs_avg_sub_avg_le A B hA hB hAB (fun i => Work.SingMV.toE (q i) j) d fun i hi j' hj' => ?_
  have h := (dist_pi_le_iff hd0).1 (hd i j') j
  rwa [Real.dist_eq] at h

end Work.SingMV
