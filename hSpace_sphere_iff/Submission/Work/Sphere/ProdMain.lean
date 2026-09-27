/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: hSpace_sphere_iff team

# The cohomology of a product of two spheres

This file contains the main induction computing the rational cohomology of `S^p × S^q` for
`1 ≤ p < q`: it is `ℚ` in degrees `p` and `q` and vanishes in all other positive degrees except
`p + q`.  The induction is on `p + q` and uses the two degree shifts `prod_fst_shift` and
`prod_snd_shift` of `Submission/Work/Sphere/ProdRec.lean`, together with the five "base cases" that
the shifts cannot reach (they are supplied as explicit hypotheses of `prod_sph_main_of_bases`):

* `baseA` : `H¹(S^p × S^q) = 0` for `2 ≤ p < q`,
* `baseB` : `H¹(S¹ × S^q) ≅ ℚ` for `2 ≤ q`,
* `baseC` : `H^{p+1}(S^p × S^{p+1}) ≅ ℚ` for `1 ≤ p`,
* `baseD` : `H^j(S⁰ × S^q) = 0` for `1 ≤ j`, `j ≠ q`,
* `baseE` : `H^{p+1}(S^p × S^p) = 0` for `2 ≤ p`.
-/
import Mathlib
import Submission.Work.Sphere.ProdSetup
import Submission.Work.Sphere.ProdRec
import Submission.Work.Sphere.Values

open CategoryTheory Simplicial Opposite
open scoped CategoryTheory.MonoidalCategory

namespace Work.Sphere

open Submission.Cohomology Submission.Sphere

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000

/-- The degree `k` cohomology of `S^p × S^q`. -/
abbrev PH (p q k : ℕ) : Type :=
  Submission.Cohomology.H (TopCat.toSSet.obj (TopProd (Sph p) (Sph q))) ℚ k

/-- The degree shift `H^{k+1}(S^{n+1} × S^q) ≅ H^k(S^n × S^q)` in the form used by the induction,
with the acyclicity of `S^q` supplied by the values of the cohomology of the spheres. -/
theorem prod_fst_shift_nat (n q k : ℕ) (hk : 1 ≤ k) (hkq : k ≠ q) (hk1q : k + 1 ≠ q) :
    Nonempty (PH (n+1) q (k+1) ≃ₗ[ℚ] PH n q k) :=
  prod_fst_shift n q k hk (sphere_subsingleton q k (by omega) hkq)
    (sphere_subsingleton q (k+1) (by omega) hk1q)

/-- The degree shift `H^{k+1}(S^p × S^{m+1}) ≅ H^k(S^p × S^m)` in the form used by the
induction. -/
theorem prod_snd_shift_nat (p m k : ℕ) (hk : 1 ≤ k) (hkp : k ≠ p) (hk1p : k + 1 ≠ p) :
    Nonempty (PH p (m+1) (k+1) ≃ₗ[ℚ] PH p m k) :=
  prod_snd_shift p m k hk (sphere_subsingleton p k (by omega) hkp)
    (sphere_subsingleton p (k+1) (by omega) hk1p)

/-- `Subsingleton` transfers across a linear equivalence (in either direction). -/
theorem subs_trans {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (h1 : Nonempty (V ≃ₗ[ℚ] W)) (h2 : Subsingleton W) :
    Subsingleton V :=
  subsingleton_of_linearEquiv (Classical.choice h1) h2

/-- Composition of cohomology isomorphisms. -/
theorem ne_trans {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (h1 : Nonempty (V ≃ₗ[ℚ] W)) (h2 : Nonempty (W ≃ₗ[ℚ] ℚ)) :
    Nonempty (V ≃ₗ[ℚ] ℚ) :=
  ⟨(Classical.choice h1).trans (Classical.choice h2)⟩

/-- **The cohomology of a product of spheres**, from the five base cases. -/
theorem prod_sph_main_of_bases
    (baseA : ∀ p q : ℕ, 2 ≤ p → p < q → Subsingleton (PH p q 1))
    (baseB : ∀ q : ℕ, 2 ≤ q → Nonempty (PH 1 q 1 ≃ₗ[ℚ] ℚ))
    (baseC : ∀ p : ℕ, 1 ≤ p → Nonempty (PH p (p+1) (p+1) ≃ₗ[ℚ] ℚ))
    (baseD : ∀ q j : ℕ, 1 ≤ j → j ≠ q → Subsingleton (PH 0 q j))
    (baseE : ∀ p : ℕ, 2 ≤ p → Subsingleton (PH p p (p+1))) :
    ∀ p q : ℕ, 1 ≤ p → p < q →
      Nonempty (PH p q p ≃ₗ[ℚ] ℚ) ∧ Nonempty (PH p q q ≃ₗ[ℚ] ℚ) ∧
        (∀ k, 0 < k → k ≠ p → k ≠ q → k ≠ p + q → Subsingleton (PH p q k)) := by
  intro p q hp hpq
  suffices h : ∀ N : ℕ, ∀ p q : ℕ, p + q ≤ N → 1 ≤ p → p < q →
      Nonempty (PH p q p ≃ₗ[ℚ] ℚ) ∧ Nonempty (PH p q q ≃ₗ[ℚ] ℚ) ∧
        (∀ k, 0 < k → k ≠ p → k ≠ q → k ≠ p + q → Subsingleton (PH p q k)) from
    h _ p q le_rfl hp hpq
  intro N
  induction N with
  | zero => intro p q hsum _ _; omega
  | succ N ih =>
      intro p q hsum hp hpq
      have ih' : ∀ p' q' : ℕ, 1 ≤ p' → p' < q' → p' + q' ≤ N →
          Nonempty (PH p' q' p' ≃ₗ[ℚ] ℚ) ∧ Nonempty (PH p' q' q' ≃ₗ[ℚ] ℚ) ∧
            (∀ k, 0 < k → k ≠ p' → k ≠ q' → k ≠ p' + q' → Subsingleton (PH p' q' k)) :=
        fun p' q' hp' hpq' hle => ih p' q' hle hp' hpq'
      rcases p with _ | i
      · omega
      rcases q with _ | m
      · omega
      -- from now on `p = i + 1` and `q = m + 1`
      have hipq : i < m := by omega
      have hI : Nonempty (PH (i+1) (m+1) (i+1) ≃ₗ[ℚ] ℚ) := by
        rcases Nat.eq_zero_or_pos i with hi0 | hipos
        · rw [hi0]
          exact baseB (m+1) (by omega)
        · refine ne_trans (prod_fst_shift_nat i (m+1) i (by omega) (by omega) (by omega))
            (ih' i (m+1) (by omega) (by omega) (by omega)).1
      have hII : Nonempty (PH (i+1) (m+1) (m+1) ≃ₗ[ℚ] ℚ) := by
        by_cases hm : m = i + 1
        · rw [hm]
          exact baseC (i+1) (by omega)
        · refine ne_trans (prod_snd_shift_nat (i+1) m m (by omega) (by omega) (by omega))
            (ih' (i+1) m (by omega) (by omega) (by omega)).2.1
      refine ⟨hI, hII, ?_⟩
      intro k hk hkp hkq hkpq
      rcases k with _ | j
      · omega
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · rw [hj0]
        exact baseA (i+1) (m+1) (by omega) (by omega)
      -- from now on `k = j + 1 ≥ 2`
      by_cases h1 : j < i
      · -- `k < p`: shift the first factor down
        refine subs_trans (prod_fst_shift_nat i (m+1) j (by omega) (by omega) (by omega))
          ((ih' i (m+1) (by omega) (by omega) (by omega)).2.2 j (by omega) (by omega)
            (by omega) (by omega))
      · -- `k ≥ p`, and `k ≠ p`, so `k > p`
        by_cases h2 : j ≤ i
        · omega
        by_cases h3 : j < m
        · -- `p < k < q`
          by_cases h4 : j = i + 1
          · -- `k = p + 1`
            rw [h4]
            rcases Nat.eq_zero_or_pos i with hi0 | hipos
            · rw [hi0]
              refine subs_trans
                (prod_fst_shift_nat 0 (m+1) 1 (by omega) (by omega) (by omega))
                (baseD (m+1) 1 (by omega) (by omega))
            · refine subs_trans
                (prod_fst_shift_nat i (m+1) (i+1) (by omega) (by omega) (by omega))
                ((ih' i (m+1) (by omega) (by omega) (by omega)).2.2 (i+1) (by omega)
                  (by omega) (by omega) (by omega))
          · -- `k ≥ p + 2`
            refine subs_trans (prod_snd_shift_nat (i+1) m j (by omega) (by omega) (by omega))
              ((ih' (i+1) m (by omega) (by omega) (by omega)).2.2 j (by omega) (by omega)
                (by omega) (by omega))
        · -- `k ≥ q`, and `k ≠ q`, so `k > q`
          by_cases h5 : j ≤ m
          · omega
          by_cases h6 : j < i + m + 1
          · -- `q < k < p + q`
            by_cases h7 : j = m + 1
            · -- `k = q + 1`
              rw [h7]
              by_cases h8 : m = i + 1
              · rw [h8]
                refine subs_trans
                  (prod_snd_shift_nat (i+1) (i+1) (i+2) (by omega) (by omega) (by omega))
                  (baseE (i+1) (by omega))
              · refine subs_trans
                  (prod_snd_shift_nat (i+1) m (m+1) (by omega) (by omega) (by omega))
                  ((ih' (i+1) m (by omega) (by omega) (by omega)).2.2 (m+1) (by omega)
                    (by omega) (by omega) (by omega))
            · -- `k ≥ q + 2`
              refine subs_trans (prod_fst_shift_nat i (m+1) j (by omega) (by omega) (by omega))
                ((ih' i (m+1) (by omega) (by omega) (by omega)).2.2 j (by omega) (by omega)
                  (by omega) (by omega))
          · -- `k ≥ p + q + 1`
            rcases Nat.eq_zero_or_pos i with hi0 | hipos
            · rw [hi0]
              refine subs_trans
                (prod_fst_shift_nat 0 (m+1) j (by omega) (by omega) (by omega))
                (baseD (m+1) j (by omega) (by omega))
            · refine subs_trans
                (prod_fst_shift_nat i (m+1) j (by omega) (by omega) (by omega))
                ((ih' i (m+1) (by omega) (by omega) (by omega)).2.2 j (by omega) (by omega)
                  (by omega) (by omega))

end

end Work.Sphere
