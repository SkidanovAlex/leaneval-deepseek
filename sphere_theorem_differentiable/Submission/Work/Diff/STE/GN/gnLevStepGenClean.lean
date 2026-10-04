import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.GN.tools
import Submission.Work.Diff.STE.GN.holder3_int
import Submission.Work.Diff.STE.GN.holder3RpowMiddleClean

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The general Nirenberg step of the Gagliardo–Nirenberg inequality on the torus

This file proves `Work.Diff.STE.GN.gnLevStepGenClean`, the discrete-log-convexity step

`(gnLev m f (k'+1))^2 ≤ gnC m (k'+1) * gnLev m f k' * gnLev m f (k'+2)`   (`1 ≤ k'`, `k'+2 ≤ m`),

**given** the periodic integration-by-parts inequality `hibp` (which is proved separately, in
`ibpRpowComplexClean`); the point of the "Clean" variant is that the integration by parts -- the one
piece of the argument that needs the regularity of `x ↦ |x|^(p-2) x` at the zeros of the derivative
-- is taken as a hypothesis, so that the rest of the Nirenberg step is unconditional.

The levels are `gnLev m f k = (∑_{l : Fin k → ι} ∫_{cube} ‖∂^l f‖ ^ (gnP m k)) ^ (1 / gnP m k)`
with `gnP m k = 2m/k` (`Work.Diff.STE.GN.tools`).

Proof route (per summand `l : Fin (k'+1) → ι`, then power-mean over the summands).

* Write `p := gnP m (k'+1)`, `h := pdVec k' (Fin.tail l) f`, `w := pd (l 0) h`,
  `w' := pd (l 0) w`.  Since `List.ofFn` peels the head, `pdVec (k+1) (Fin.cons i l) f = pd i
  (pdVec k l f)`, hence `w = pdVec (k'+1) l f` and `w' = pdVec (k'+2) (Fin.cons (l 0) l) f`.
* Integration by parts (`hibp` at `g := h`, `i := l 0`) gives
  `A_l := ∫ ‖w‖^p ≤ (p-1) ∫ ‖h‖ ‖w‖^(p-2) ‖w'‖`.
* Three-function Hölder (`holder3RpowMiddleClean`) with the exponents `gnP m k'`,
  `gnB m (k'+1)`, `gnP m (k'+2)` (reciprocals summing to `1` by `gnB_holder_sum`, and
  `(p-2) * gnB m (k'+1) = p` by `gnB_mul`) bounds the last integral by
  `(∫‖h‖^{gnP m k'})^{1/gnP m k'} * A_l^{(p-2)/p} * (∫‖w'‖^{gnP m (k'+2)})^{1/gnP m (k'+2)}`.
* Each outer factor is a single summand of the level `gnLev m f k'` resp. `gnLev m f (k'+2)`
  (`gnLevSummandLe`), so `A_l ≤ ((p-1) V₁ V₂) A_l^{(p-2)/p}` with `V₁ = gnLev m f k'`,
  `V₂ = gnLev m f (k'+2)`; multiplying by `A_l^{2/p}` and dividing by `A_l^{(p-2)/p}` gives
  `A_l^{2/p} ≤ (p-1) V₁ V₂`.
* Power-mean (`gnSumRpowLeCard`): `(∑_l A_l)^{2/p} ≤ ((p-1) V₁ V₂) · N^{2/p}` with
  `N := Fintype.card (Fin (k'+1) → ι)`.
* `(gnLev m f (k'+1))^2 = (∑_l A_l)^{2/p}` (the defining identity of the level), and
  `(p-1) N^{2/p} ≤ gnC m (k'+1)` by definition of `gnC`.
-/

noncomputable section

namespace Work.Diff.STE.GN

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Elementary supporting lemmas -/

/-- **The decomposition of `pdVec` along the first direction.**  `pdVec` is `List.foldr` over
`List.ofFn`, which peels the *head* of the list, so prepending a direction with `Fin.cons` adds the
outermost derivative. -/
lemma pdVec_cons_eq (k : ℕ) (i : ι) (l : Fin k → ι) (f : (ι → ℝ) → ℂ) :
    pdVec (k + 1) (Fin.cons i l) f = pd i (pdVec k l f) := by
  simp only [pdVec, pdList, List.ofFn_cons, List.foldr_cons]

/-- **A single summand of a Nirenberg level is bounded by the level.**

`(∫_{cube} ‖∂^l f‖ ^ (p k)) ^ (1 / (p k)) ≤ gnLev m f k` for `1 ≤ k ≤ m`, where
`p k = gnP m k = 2m/k` and `gnLev m f k = (∑_{l' : Fin k → ι} ∫_{cube} ‖∂^{l'} f‖ ^ (p k)) ^ (1/(p k))`.

Immediate from `Work.Diff.STE.gnLev_rpow` (the defining identity) and `Finset.single_le_sum`,
using the nonnegativity of the summands and the monotonicity of `x ↦ x^(1/(p k))` on `[0,∞)`. -/
lemma gnLevSummandLe (m : ℕ) (f : (ι → ℝ) → ℂ) (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m)
    (l : Fin k → ι) :
    (∫ x in unitCube (ι := ι), ‖pdVec k l f x‖ ^ gnP m k) ^ (1 / gnP m k)
      ≤ gnLev m f k := by
  have hmem : ∀ l' ∈ (Finset.univ : Finset (Fin k → ι)),
      0 ≤ ∫ x in unitCube (ι := ι), ‖pdVec k l' f x‖ ^ gnP m k :=
    fun l' _ => integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have h1 : (∫ x in unitCube (ι := ι), ‖pdVec k l f x‖ ^ gnP m k)
      ≤ ∑ l' : Fin k → ι,
          ∫ x in unitCube (ι := ι), ‖pdVec k l' f x‖ ^ gnP m k :=
    Finset.single_le_sum hmem (Finset.mem_univ l)
  have h2 := gnLev_rpow (ι := ι) m f hk hkm
  have hI0 : 0 ≤ ∫ x in unitCube (ι := ι), ‖pdVec k l f x‖ ^ gnP m k := hmem l (Finset.mem_univ l)
  have hp0 : 0 < 1 / gnP m k := div_pos one_pos (gnP_pos hk hkm)
  calc (∫ x in unitCube (ι := ι), ‖pdVec k l f x‖ ^ gnP m k) ^ (1 / gnP m k)
      ≤ (∑ l' : Fin k → ι,
          ∫ x in unitCube (ι := ι), ‖pdVec k l' f x‖ ^ gnP m k) ^ (1 / gnP m k) :=
        Real.rpow_le_rpow hI0 h1 hp0.le
    _ = ((gnLev m f k) ^ gnP m k) ^ (1 / gnP m k) := by rw [h2]
    _ = gnLev m f k := by
        rw [← Real.rpow_mul (gnLev_nonneg m f k) (gnP m k) (1 / gnP m k)]
        rw [mul_one_div, div_self (gnP_ne_zero hk hkm), Real.rpow_one]

/-- **Power-mean / Young step.**  If `a ≥ 0`, `t > 0` and `a i ^ t ≤ C` for every `i`, then
`(∑ i, a i) ^ t ≤ C * (card α) ^ t`.

(No hypothesis `t ≤ 1` is needed: the estimate is the trivial consequence of
`a i ≤ C ^ (1/t)` and `card α` summands.) -/
lemma gnSumRpowLeCard {α : Type*} [Fintype α] (a : α → ℝ) (ha : ∀ i, 0 ≤ a i)
    (C t : ℝ) (ht : 0 < t) (h : ∀ i, a i ^ t ≤ C) :
    (∑ i, a i) ^ t ≤ C * (Fintype.card α : ℝ) ^ t := by
  rcases isEmpty_or_nonempty α with hα | hα
  · have hsum : (∑ i, a i) = 0 := Finset.sum_eq_zero (fun i _ => by
      have : IsEmpty α := hα; exact isEmptyElim i)
    have hc : (Fintype.card α : ℝ) = 0 := by have : IsEmpty α := hα; simp
    rw [hsum, hc, Real.zero_rpow (ne_of_gt ht), mul_zero]
  · obtain ⟨i0⟩ := hα
    have hC0 : 0 ≤ C := le_trans (Real.rpow_nonneg (ha i0) t) (h i0)
    have hsq : ∀ i, a i ≤ C ^ (1 / t) := by
      intro i
      have h1 : (a i ^ t) ^ (1 / t) ≤ C ^ (1 / t) :=
        Real.rpow_le_rpow (Real.rpow_nonneg (ha i) t) (h i) (by positivity)
      rwa [← Real.rpow_mul (ha i) t (1 / t), mul_one_div, div_self (ne_of_gt ht),
        Real.rpow_one] at h1
    have hsum : (∑ i, a i) ≤ (Fintype.card α : ℝ) * C ^ (1 / t) := by
      calc (∑ i, a i) ≤ ∑ _i : α, C ^ (1 / t) := Finset.sum_le_sum (fun i _ => hsq i)
        _ = (Fintype.card α : ℝ) * C ^ (1 / t) := by simp [Finset.sum_const, nsmul_eq_mul]
    have h1t : 1 / t * t = 1 := by rw [one_div, inv_mul_cancel₀ (ne_of_gt ht)]
    calc (∑ i, a i) ^ t
        ≤ ((Fintype.card α : ℝ) * C ^ (1 / t)) ^ t :=
          Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => ha i)) hsum ht.le
      _ = (Fintype.card α : ℝ) ^ t * (C ^ (1 / t)) ^ t :=
          Real.mul_rpow (by positivity) (Real.rpow_nonneg hC0 _)
      _ = (Fintype.card α : ℝ) ^ t * C ^ (1 / t * t) := by rw [Real.rpow_mul hC0 (1 / t) t]
      _ = (Fintype.card α : ℝ) ^ t * C := by rw [h1t, Real.rpow_one]
      _ = C * (Fintype.card α : ℝ) ^ t := by ring

/-- **The per-summand Nirenberg estimate.**  For every tuple `l : Fin (k'+1) → ι`,

`(∫_{cube} ‖∂^l f‖ ^ p) ^ (2/p) ≤ (p-1) * gnLev m f k' * gnLev m f (k'+2)`,  `p = gnP m (k'+1)`,

obtained from the integration-by-parts inequality `hibp` (applied to `pdVec k' (Fin.tail l) f` in
the direction `l 0`) followed by three-function Hölder's inequality. -/
lemma gnLevStepSummandClean (m : ℕ) (hm : 2 ≤ m)
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : Periodic1 f)
    (k' : ℕ) (hk' : 1 ≤ k') (hkm : k' + 2 ≤ m)
    (hibp : ∀ (g : (ι → ℝ) → ℂ) (i : ι), ContDiff ℝ (⊤ : ℕ∞) g → Periodic1 g →
      ∫ x in unitCube (ι := ι),
          ‖pd i g x‖ ^ gnP m (k' + 1)
        ≤ (gnP m (k' + 1) - 1) * ∫ x in unitCube (ι := ι),
            ‖g x‖ * ‖pd i g x‖ ^ (gnP m (k' + 1) - 2)
              * ‖pd i (pd i g) x‖)
    (l : Fin (k' + 1) → ι) :
    (∫ x in unitCube (ι := ι), ‖pdVec (k' + 1) l f x‖ ^ gnP m (k' + 1))
        ^ (2 / gnP m (k' + 1))
      ≤ (gnP m (k' + 1) - 1) * gnLev (ι := ι) m f k' * gnLev (ι := ι) m f (k' + 2) := by
  have hp_pos : 0 < gnP m (k' + 1) := gnP_pos (by omega) (by omega)
  have hp2 : 2 ≤ gnP m (k' + 1) := gnP_two_le (by omega) (by omega)
  have hk'' : 2 ≤ k' + 1 := by omega
  have hkm' : k' + 1 + 1 ≤ m := by omega
  have hk'm : k' ≤ m := by omega
  -- the two index identities
  have hw_eq : pd (l 0) (pdVec k' (Fin.tail l) f) = pdVec (k' + 1) l f := by
    rw [← pdVec_cons_eq k' (l 0) (Fin.tail l) f, Fin.cons_self_tail]
  have hw_eq2 : pd (l 0) (pd (l 0) (pdVec k' (Fin.tail l) f))
      = pdVec (k' + 2) (Fin.cons (l 0) l) f := by
    rw [hw_eq, pdVec_cons_eq (k' + 1) (l 0) l f]
  -- the integral whose power we bound
  set A : ℝ := ∫ x in unitCube (ι := ι), ‖pdVec (k' + 1) l f x‖ ^ gnP m (k' + 1) with hAdef
  have hAeq : A = ∫ x in unitCube (ι := ι),
      ‖pd (l 0) (pdVec k' (Fin.tail l) f) x‖ ^ gnP m (k' + 1) := by
    rw [hAdef, ← hw_eq]
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  -- smoothness of the three functions
  have hFsm : ContDiff ℝ (⊤ : ℕ∞) (pdVec k' (Fin.tail l) f) := contDiff_pdVec_top (Fin.tail l) f hf
  have hFper : Periodic1 (pdVec k' (Fin.tail l) f) := periodic1_pdVec (Fin.tail l) f hf hper
  have hGsm : ContDiff ℝ (⊤ : ℕ∞) (pd (l 0) (pdVec k' (Fin.tail l) f)) := by
    rw [← pdVec_cons_eq k' (l 0) (Fin.tail l) f]
    exact contDiff_pdVec_top (Fin.cons (l 0) (Fin.tail l)) f hf
  have hHsm : ContDiff ℝ (⊤ : ℕ∞) (pd (l 0) (pd (l 0) (pdVec k' (Fin.tail l) f))) := by
    rw [hw_eq2]
    exact contDiff_pdVec_top (Fin.cons (l 0) l) f hf
  -- integration by parts
  have hIBP := hibp (pdVec k' (Fin.tail l) f) (l 0) hFsm hFper
  -- three-function Hölder
  have hHolder := holder3RpowMiddleClean (ι := ι) (gnP m k') (gnB m (k' + 1)) (gnP m (k' + 2))
      (gnP m (k' + 1)) (gnP_ge_one hk' hk'm) (gnB_ge_one m (k' + 1) hk'' hkm')
      (gnP_ge_one (by omega) hkm) hp2
      (gnB_holder_sum m (k' + 1) hk'' hkm') (gnB_mul m (k' + 1) hk'' hkm')
      (fun x : ι → ℝ => ‖pdVec k' (Fin.tail l) f x‖)
      (fun x : ι → ℝ => ‖pd (l 0) (pdVec k' (Fin.tail l) f) x‖)
      (fun x : ι → ℝ => ‖pd (l 0) (pd (l 0) (pdVec k' (Fin.tail l) f)) x‖)
      hFsm.continuous.norm hGsm.continuous.norm hHsm.continuous.norm
      (fun x => norm_nonneg _) (fun x => norm_nonneg _) (fun x => norm_nonneg _)
  -- the two outer factors are bounded by the levels
  have hL1 : (∫ x in unitCube (ι := ι), ‖pdVec k' (Fin.tail l) f x‖ ^ gnP m k') ^ (1 / gnP m k')
      ≤ gnLev (ι := ι) m f k' := gnLevSummandLe m f k' hk' hk'm (Fin.tail l)
  have hL2 : (∫ x in unitCube (ι := ι),
        ‖pd (l 0) (pd (l 0) (pdVec k' (Fin.tail l) f)) x‖ ^ gnP m (k' + 2))
        ^ (1 / gnP m (k' + 2)) ≤ gnLev (ι := ι) m f (k' + 2) := by
    rw [hw_eq2]
    exact gnLevSummandLe m f (k' + 2) (by omega) hkm (Fin.cons (l 0) l)
  -- the middle factor is `A ^ ((p-2)/p)`
  have hmid : (∫ x in unitCube (ι := ι),
      ‖pd (l 0) (pdVec k' (Fin.tail l) f) x‖ ^ gnP m (k' + 1)) = A := by
    rw [hAeq]
  rw [hmid] at hHolder
  have hX0 : 0 ≤ A ^ ((gnP m (k' + 1) - 2) / gnP m (k' + 1)) := Real.rpow_nonneg hA0 _
  have hV1 : 0 ≤ gnLev (ι := ι) m f k' := gnLev_nonneg m f k'
  have hV2 : 0 ≤ gnLev (ι := ι) m f (k' + 2) := gnLev_nonneg m f (k' + 2)
  have hL20 : 0 ≤ (∫ x in unitCube (ι := ι),
        ‖pd (l 0) (pd (l 0) (pdVec k' (Fin.tail l) f)) x‖ ^ gnP m (k' + 2))
        ^ (1 / gnP m (k' + 2)) :=
    Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _
  have hcomb : (∫ x in unitCube (ι := ι), ‖pdVec k' (Fin.tail l) f x‖
        * ‖pd (l 0) (pdVec k' (Fin.tail l) f) x‖ ^ (gnP m (k' + 1) - 2)
        * ‖pd (l 0) (pd (l 0) (pdVec k' (Fin.tail l) f)) x‖)
      ≤ gnLev (ι := ι) m f k' * A ^ ((gnP m (k' + 1) - 2) / gnP m (k' + 1))
        * gnLev (ι := ι) m f (k' + 2) :=
    le_trans hHolder (le_trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL1 hX0) hL20)
      (mul_le_mul_of_nonneg_left hL2 (mul_nonneg hV1 hX0)))
  -- the key inequality `A ≤ B * A^((p-2)/p)`
  have hD : 0 ≤ gnP m (k' + 1) - 1 := by linarith
  have hstep1 : (∫ x in unitCube (ι := ι),
        ‖pd (l 0) (pdVec k' (Fin.tail l) f) x‖ ^ gnP m (k' + 1))
      ≤ (gnP m (k' + 1) - 1) * (gnLev (ι := ι) m f k'
          * A ^ ((gnP m (k' + 1) - 2) / gnP m (k' + 1)) * gnLev (ι := ι) m f (k' + 2)) :=
    le_trans hIBP (mul_le_mul_of_nonneg_left hcomb hD)
  have hstep2 : (gnP m (k' + 1) - 1) * (gnLev (ι := ι) m f k'
        * A ^ ((gnP m (k' + 1) - 2) / gnP m (k' + 1)) * gnLev (ι := ι) m f (k' + 2))
      = ((gnP m (k' + 1) - 1) * gnLev (ι := ι) m f k' * gnLev (ι := ι) m f (k' + 2))
          * A ^ ((gnP m (k' + 1) - 2) / gnP m (k' + 1)) := by ring
  have hkey : A ≤ ((gnP m (k' + 1) - 1) * gnLev (ι := ι) m f k' * gnLev (ι := ι) m f (k' + 2))
      * A ^ ((gnP m (k' + 1) - 2) / gnP m (k' + 1)) := by
    conv_lhs => rw [hAeq]
    exact hstep2 ▸ hstep1
  -- divide by `A ^ ((p-2)/p)`
  have hsumexp : 2 / gnP m (k' + 1) + (gnP m (k' + 1) - 2) / gnP m (k' + 1) = 1 := by
    rw [← add_div, div_eq_one_iff_eq (ne_of_gt hp_pos)]
    ring
  have ht0 : 0 < 2 / gnP m (k' + 1) := div_pos two_pos hp_pos
  by_cases hAz : A = 0
  · rw [hAz, Real.zero_rpow (ne_of_gt ht0)]
    exact mul_nonneg (mul_nonneg (by linarith) hV1) hV2
  · have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAz)
    have hXpos : 0 < A ^ ((gnP m (k' + 1) - 2) / gnP m (k' + 1)) := Real.rpow_pos_of_pos hApos _
    have hne : 2 / gnP m (k' + 1) + (gnP m (k' + 1) - 2) / gnP m (k' + 1) ≠ 0 := by
      rw [hsumexp]; norm_num
    have hmul : A ^ (2 / gnP m (k' + 1)) * A ^ ((gnP m (k' + 1) - 2) / gnP m (k' + 1))
        ≤ ((gnP m (k' + 1) - 1) * gnLev (ι := ι) m f k' * gnLev (ι := ι) m f (k' + 2))
          * A ^ ((gnP m (k' + 1) - 2) / gnP m (k' + 1)) := by
      rw [← Real.rpow_add' hA0 hne, hsumexp, Real.rpow_one]
      exact hkey
    exact le_of_mul_le_mul_right hmul hXpos

theorem gnLevStepGenClean {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) (hm : 2 ≤ m)
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : Work.Diff.STE.Periodic1 f)
    (k' : ℕ) (hk' : 1 ≤ k') (hkm : k' + 2 ≤ m)
    (hibp : ∀ (g : (ι → ℝ) → ℂ) (i : ι), ContDiff ℝ (⊤ : ℕ∞) g → Work.Diff.STE.Periodic1 g →
      ∫ x in Work.Diff.STE.unitCube (ι := ι),
          ‖Work.Diff.STE.pd i g x‖ ^ Work.Diff.STE.gnP m (k' + 1)
        ≤ (Work.Diff.STE.gnP m (k' + 1) - 1) * ∫ x in Work.Diff.STE.unitCube (ι := ι),
            ‖g x‖ * ‖Work.Diff.STE.pd i g x‖ ^ (Work.Diff.STE.gnP m (k' + 1) - 2)
              * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i g) x‖) :
    (Work.Diff.STE.gnLev (ι := ι) m f (k' + 1)) ^ 2
      ≤ Work.Diff.STE.gnC (ι := ι) m (k' + 1) * Work.Diff.STE.gnLev (ι := ι) m f k'
        * Work.Diff.STE.gnLev (ι := ι) m f (k' + 2) := by
  have hp_pos : 0 < gnP m (k' + 1) := gnP_pos (by omega) (by omega)
  have ht0 : 0 < 2 / gnP m (k' + 1) := div_pos two_pos hp_pos
  set A : (Fin (k' + 1) → ι) → ℝ :=
    fun l => ∫ x in unitCube (ι := ι), ‖pdVec (k' + 1) l f x‖ ^ gnP m (k' + 1) with hAdef
  have hA0 : ∀ l, 0 ≤ A l :=
    fun l => integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hstep : ∀ l : Fin (k' + 1) → ι,
      A l ^ (2 / gnP m (k' + 1))
        ≤ (gnP m (k' + 1) - 1) * gnLev (ι := ι) m f k' * gnLev (ι := ι) m f (k' + 2) :=
    fun l => gnLevStepSummandClean m hm f hf hper k' hk' hkm hibp l
  have hsq : (gnLev (ι := ι) m f (k' + 1)) ^ 2 = (∑ l, A l) ^ (2 / gnP m (k' + 1)) := by
    have hgl : gnLev (ι := ι) m f (k' + 1) = (∑ l, A l) ^ (1 / gnP m (k' + 1)) := rfl
    rw [hgl, pow_two]
    have hS0 : 0 ≤ ∑ l, A l := Finset.sum_nonneg (fun l _ => hA0 l)
    have hadd : 1 / gnP m (k' + 1) + 1 / gnP m (k' + 1) = 2 / gnP m (k' + 1) := by
      rw [← add_div]; norm_num
    rw [← Real.rpow_add' hS0 (by rw [hadd]; exact ne_of_gt ht0), hadd]
  have hmain := gnSumRpowLeCard A hA0
    ((gnP m (k' + 1) - 1) * gnLev (ι := ι) m f k' * gnLev (ι := ι) m f (k' + 2))
    (2 / gnP m (k' + 1)) ht0 hstep
  rw [hsq]
  refine le_trans hmain ?_
  have hgnC : (gnP m (k' + 1) - 1) * (Fintype.card (Fin (k' + 1) → ι) : ℝ) ^ (2 / gnP m (k' + 1))
      ≤ gnC (ι := ι) m (k' + 1) := by
    rw [gnC]
    have hcomm : (gnP m (k' + 1) - 1) * (Fintype.card (Fin (k' + 1) → ι) : ℝ)
          ^ (2 / gnP m (k' + 1))
        = (Fintype.card (Fin (k' + 1) → ι) : ℝ) ^ (2 / gnP m (k' + 1)) * (gnP m (k' + 1) - 1) :=
      by ring
    rw [hcomm]
    exact le_max_right _ _
  calc ((gnP m (k' + 1) - 1) * gnLev (ι := ι) m f k' * gnLev (ι := ι) m f (k' + 2))
        * (Fintype.card (Fin (k' + 1) → ι) : ℝ) ^ (2 / gnP m (k' + 1))
      = (gnLev (ι := ι) m f k' * gnLev (ι := ι) m f (k' + 2))
          * ((gnP m (k' + 1) - 1)
              * (Fintype.card (Fin (k' + 1) → ι) : ℝ) ^ (2 / gnP m (k' + 1))) := by ring
    _ ≤ (gnLev (ι := ι) m f k' * gnLev (ι := ι) m f (k' + 2)) * gnC (ι := ι) m (k' + 1) :=
        mul_le_mul_of_nonneg_left hgnC
          (mul_nonneg (gnLev_nonneg m f k') (gnLev_nonneg m f (k' + 2)))
    _ = gnC (ι := ι) m (k' + 1) * gnLev (ι := ι) m f k' * gnLev (ι := ι) m f (k' + 2) := by ring

end Work.Diff.STE.GN
