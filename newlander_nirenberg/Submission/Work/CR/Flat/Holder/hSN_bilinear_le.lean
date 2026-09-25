import Mathlib
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.CR.Flat.Holder.BilinRHS

namespace Work.CR.Flat.Holder

open scoped NNReal ENNReal
open Set

universe u

/-! ### Combinatorial identity -/

/-- Pascal's rule for the two-term convolution sums appearing in `bilinRHS`:
`∑_{i≤k} C(k,i) a_i b_{k+1-i} + ∑_{i≤k} C(k,i) a_{i+1} b_{k-i} = ∑_{i≤k+1} C(k+1,i) a_i b_{k+1-i}`. -/
lemma pascal_pair (A B : ℕ → ℝ≥0∞) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), (Nat.choose k i : ℝ≥0∞) * (A i * B (k + 1 - i)))
      + (∑ i ∈ Finset.range (k + 1), (Nat.choose k i : ℝ≥0∞) * (A (i + 1) * B (k - i)))
    = ∑ i ∈ Finset.range (k + 2), (Nat.choose (k + 1) i : ℝ≥0∞) * (A i * B (k + 1 - i)) := by
  have hS1 : (∑ i ∈ Finset.range (k + 1), (Nat.choose k i : ℝ≥0∞) * (A i * B (k + 1 - i)))
      = A 0 * B (k + 1)
        + ∑ i ∈ Finset.range (k + 1), (Nat.choose k (i + 1) : ℝ≥0∞) * (A (i + 1) * B (k - i)) := by
    rw [Finset.sum_range_succ' (fun i => (Nat.choose k i : ℝ≥0∞) * (A i * B (k + 1 - i))) k,
      Finset.sum_range_succ (fun i => (Nat.choose k (i + 1) : ℝ≥0∞) * (A (i + 1) * B (k - i))) k]
    simp only [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self k), Nat.cast_zero, zero_mul, add_zero,
      Nat.cast_one, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.add_sub_add_right]
    exact add_comm _ _
  have hV : (∑ i ∈ Finset.range (k + 2), (Nat.choose (k + 1) i : ℝ≥0∞) * (A i * B (k + 1 - i)))
      = A 0 * B (k + 1)
        + (∑ i ∈ Finset.range (k + 1), (Nat.choose k i : ℝ≥0∞) * (A (i + 1) * B (k - i)))
        + (∑ i ∈ Finset.range (k + 1), (Nat.choose k (i + 1) : ℝ≥0∞) * (A (i + 1) * B (k - i))) := by
    rw [Finset.sum_range_succ' (fun i => (Nat.choose (k + 1) i : ℝ≥0∞) * (A i * B (k + 1 - i)))
      (k + 1)]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.add_sub_add_right, Nat.sub_zero]
    rw [Finset.sum_congr rfl (fun x _ => by rw [Nat.choose_succ_succ, Nat.cast_add, add_mul]),
      Finset.sum_add_distrib]
    ac_rfl
  rw [hS1, hV]
  ac_rfl

/-- The `bilinRHS`-shaped version of `pascal_pair`, with two pairs of sequences. -/
lemma pascal_four (A B C D : ℕ → ℝ≥0∞) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1),
        (Nat.choose k i : ℝ≥0∞) * (A i * B (k + 1 - i) + C i * D (k + 1 - i)))
      + (∑ i ∈ Finset.range (k + 1),
        (Nat.choose k i : ℝ≥0∞) * (A (i + 1) * B (k - i) + C (i + 1) * D (k - i)))
    = ∑ i ∈ Finset.range (k + 2),
        (Nat.choose (k + 1) i : ℝ≥0∞) * (A i * B (k + 1 - i) + C i * D (k + 1 - i)) := by
  have h1 : (∑ i ∈ Finset.range (k + 1),
        (Nat.choose k i : ℝ≥0∞) * (A i * B (k + 1 - i) + C i * D (k + 1 - i)))
      = (∑ i ∈ Finset.range (k + 1), (Nat.choose k i : ℝ≥0∞) * (A i * B (k + 1 - i)))
        + (∑ i ∈ Finset.range (k + 1), (Nat.choose k i : ℝ≥0∞) * (C i * D (k + 1 - i))) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => mul_add _ _ _
  have h2 : (∑ i ∈ Finset.range (k + 1),
        (Nat.choose k i : ℝ≥0∞) * (A (i + 1) * B (k - i) + C (i + 1) * D (k - i)))
      = (∑ i ∈ Finset.range (k + 1), (Nat.choose k i : ℝ≥0∞) * (A (i + 1) * B (k - i)))
        + (∑ i ∈ Finset.range (k + 1), (Nat.choose k i : ℝ≥0∞) * (C (i + 1) * D (k - i))) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => mul_add _ _ _
  have h3 : (∑ i ∈ Finset.range (k + 2),
        (Nat.choose (k + 1) i : ℝ≥0∞) * (A i * B (k + 1 - i) + C i * D (k + 1 - i)))
      = (∑ i ∈ Finset.range (k + 2), (Nat.choose (k + 1) i : ℝ≥0∞) * (A i * B (k + 1 - i)))
        + (∑ i ∈ Finset.range (k + 2), (Nat.choose (k + 1) i : ℝ≥0∞) * (C i * D (k + 1 - i))) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => mul_add _ _ _
  rw [h1, h2, h3, ← pascal_pair A B k, ← pascal_pair C D k]
  ac_rfl

/-! ### Base case -/

/-- The case `n = 0` of the Leibniz-type bound: no differentiability of `Ω` is needed. -/
lemma hSN_zero_bilinear_le {D E F G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) (B : E →L[ℝ] F →L[ℝ] G) {f : D → E}
    {g : D → F} {Ω : Set D} :
    hSN 0 α (fun x => B (f x) (g x)) Ω ≤ ENNReal.ofReal ‖B‖ * bilinRHS α 0 f g Ω := by
  rw [bilinRHS_zero, hSN_zero_deriv]
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  have hd : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  have hdecomp : B (f x) (g x) - B (f y) (g y)
      = B (f x - f y) (g x) + B (f y) (g x - g y) := by
    rw [map_sub, sub_apply, map_sub]
    abel
  have hbound : ‖B (f x) (g x) - B (f y) (g y)‖ ≤
      ‖B‖ * (‖f x - f y‖ * ‖g x‖ + ‖f y‖ * ‖g x - g y‖) := by
    rw [hdecomp]
    calc ‖B (f x - f y) (g x) + B (f y) (g x - g y)‖
        ≤ ‖B (f x - f y) (g x)‖ + ‖B (f y) (g x - g y)‖ := norm_add_le _ _
      _ ≤ ‖B‖ * ‖f x - f y‖ * ‖g x‖ + ‖B‖ * ‖f y‖ * ‖g x - g y‖ :=
          add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
      _ = ‖B‖ * (‖f x - f y‖ * ‖g x‖ + ‖f y‖ * ‖g x - g y‖) := by ring
  have hdiv : ‖B (f x) (g x) - B (f y) (g y)‖ / ‖x - y‖ ^ α ≤
      ‖B‖ * ((‖f x - f y‖ / ‖x - y‖ ^ α) * ‖g x‖
        + ‖f y‖ * (‖g x - g y‖ / ‖x - y‖ ^ α)) := by
    refine (div_le_div_of_nonneg_right hbound hd).trans ?_
    have heq : ‖B‖ * (‖f x - f y‖ * ‖g x‖ + ‖f y‖ * ‖g x - g y‖) / ‖x - y‖ ^ α
        = ‖B‖ * ((‖f x - f y‖ / ‖x - y‖ ^ α) * ‖g x‖
            + ‖f y‖ * (‖g x - g y‖ / ‖x - y‖ ^ α)) := by
      ring
    exact heq.le
  refine (ENNReal.ofReal_le_ofReal hdiv).trans ?_
  rw [ENNReal.ofReal_mul (norm_nonneg B),
    ENNReal.ofReal_add (mul_nonneg (div_nonneg (norm_nonneg _) hd) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (div_nonneg (norm_nonneg _) hd)),
    ENNReal.ofReal_mul (div_nonneg (norm_nonneg _) hd),
    ENNReal.ofReal_mul (norm_nonneg _)]
  gcongr
  · rw [← norm_iteratedFDerivWithin_zero_sub f Ω x y]
    exact le_hSN 0 α hx hy hxy
  · simpa using le_iDN (i := 0) (f := g) hx
  · simpa using le_iDN (i := 0) (f := f) hy
  · rw [← norm_iteratedFDerivWithin_zero_sub g Ω x y]
    exact le_hSN 0 α hx hy hxy

/-! ### The inductive step of the sum -/

/-- `bilinRHS` at order `k + 1` splits into the two `bilinRHS` at order `k` for the pairs
`(f, fderivWithin g)` and `(fderivWithin f, g)`. -/
lemma bilinRHS_fderiv_step {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (α : ℝ) (k : ℕ) {f : D → E} {g : D → F} {Ω : Set D} (hΩ : UniqueDiffOn ℝ Ω) :
    bilinRHS α k f (fun z => fderivWithin ℝ g Ω z) Ω
      + bilinRHS α k (fun z => fderivWithin ℝ f Ω z) g Ω
      = bilinRHS α (k + 1) f g Ω := by
  have h1 : bilinRHS α k f (fun z => fderivWithin ℝ g Ω z) Ω
      = ∑ i ∈ Finset.range (k + 1), (Nat.choose k i : ℝ≥0∞) *
          (hSN i α f Ω * iDN (k + 1 - i) g Ω + iDN i f Ω * hSN (k + 1 - i) α g Ω) := by
    simp only [bilinRHS]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hidx : k - i + 1 = k + 1 - i := by omega
    rw [iDN_fderivWithin (k - i) g Ω hΩ, hSN_fderivWithin (k - i) α g Ω hΩ, hidx]
  have h2 : bilinRHS α k (fun z => fderivWithin ℝ f Ω z) g Ω
      = ∑ i ∈ Finset.range (k + 1), (Nat.choose k i : ℝ≥0∞) *
          (hSN (i + 1) α f Ω * iDN (k - i) g Ω + iDN (i + 1) f Ω * hSN (k - i) α g Ω) := by
    simp only [bilinRHS]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hSN_fderivWithin i α f Ω hΩ, iDN_fderivWithin i f Ω hΩ]
  have h3 : bilinRHS α (k + 1) f g Ω
      = ∑ i ∈ Finset.range (k + 2), (Nat.choose (k + 1) i : ℝ≥0∞) *
          (hSN i α f Ω * iDN (k + 1 - i) g Ω + iDN i f Ω * hSN (k + 1 - i) α g Ω) := by
    simp only [bilinRHS]
  rw [h1, h2, h3, pascal_four (fun i => hSN i α f Ω) (fun i => iDN i g Ω)
    (fun i => iDN i f Ω) (fun i => hSN i α g Ω) k]

/-! ### The inductive step -/

lemma hSN_bilinear_aux (α : ℝ) :
    ∀ (n : ℕ) {D : Type u} {E F G : Type u} [NormedAddCommGroup D] [NormedSpace ℝ D]
      [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
      [NormedAddCommGroup G] [NormedSpace ℝ G] (B : E →L[ℝ] F →L[ℝ] G) {f : D → E} {g : D → F}
      {Ω : Set D}, ContDiffOn ℝ n f Ω → ContDiffOn ℝ n g Ω → UniqueDiffOn ℝ Ω →
      hSN n α (fun x => B (f x) (g x)) Ω ≤ ENNReal.ofReal ‖B‖ * bilinRHS α n f g Ω := by
  intro n
  induction n with
  | zero =>
    intro D E F G _ _ _ _ _ _ _ _ B f g Ω _ _ _
    exact hSN_zero_bilinear_le α B
  | succ k ih =>
    intro D E F G _ _ _ _ _ _ _ _ B f g Ω hf hg hΩ
    have hderiv : (k : WithTop ℕ∞) + 1 ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by
      simp only [Nat.cast_succ, le_refl]
    have hfk : ContDiffOn ℝ k f Ω := hf.of_le (Nat.cast_le.2 (Nat.le_succ k))
    have hgk : ContDiffOn ℝ k g Ω := hg.of_le (Nat.cast_le.2 (Nat.le_succ k))
    have hDg : ContDiffOn ℝ k (fun z => fderivWithin ℝ g Ω z) Ω := hg.fderivWithin hΩ hderiv
    have hDf : ContDiffOn ℝ k (fun z => fderivWithin ℝ f Ω z) Ω := hf.fderivWithin hΩ hderiv
    have hG1 : ContDiffOn ℝ k (fun z => (B.precompR D) (f z) (fderivWithin ℝ g Ω z)) Ω :=
      (B.precompR D).isBoundedBilinearMap.contDiff.comp₂_contDiffOn hfk hDg
    have hG2 : ContDiffOn ℝ k (fun z => (B.precompL D) (fderivWithin ℝ f Ω z) (g z)) Ω :=
      (B.precompL D).isBoundedBilinearMap.contDiff.comp₂_contDiffOn hDf hgk
    have hI1 : hSN k α (fun z => (B.precompR D) (f z) (fderivWithin ℝ g Ω z)) Ω
        ≤ ENNReal.ofReal ‖B‖ * bilinRHS α k f (fun z => fderivWithin ℝ g Ω z) Ω :=
      (ih (F := D →L[ℝ] F) (G := D →L[ℝ] G) (B := B.precompR D) hfk hDg hΩ).trans (by
        gcongr
        exact B.norm_precompR_le D)
    have hI2 : hSN k α (fun z => (B.precompL D) (fderivWithin ℝ f Ω z) (g z)) Ω
        ≤ ENNReal.ofReal ‖B‖ * bilinRHS α k (fun z => fderivWithin ℝ f Ω z) g Ω :=
      (ih (E := D →L[ℝ] E) (G := D →L[ℝ] G) (B := B.precompL D) hDf hgk hΩ).trans (by
        gcongr
        exact B.norm_precompL_le D)
    calc hSN (k + 1) α (fun x => B (f x) (g x)) Ω
        = hSN k α (fun z => fderivWithin ℝ (fun x => B (f x) (g x)) Ω z) Ω :=
          (hSN_fderivWithin k α (fun x => B (f x) (g x)) Ω hΩ).symm
      _ = hSN k α ((fun z => (B.precompR D) (f z) (fderivWithin ℝ g Ω z))
            + (fun z => (B.precompL D) (fderivWithin ℝ f Ω z) (g z))) Ω := by
          refine hSN_congr fun z hz => ?_
          exact B.fderivWithin_of_bilinear (hf.differentiableOn (by positivity) z hz)
            (hg.differentiableOn (by positivity) z hz) (hΩ z hz)
      _ ≤ hSN k α (fun z => (B.precompR D) (f z) (fderivWithin ℝ g Ω z)) Ω
            + hSN k α (fun z => (B.precompL D) (fderivWithin ℝ f Ω z) (g z)) Ω :=
          hSN_add_le (φ := fun z => (B.precompR D) (f z) (fderivWithin ℝ g Ω z))
            (ψ := fun z => (B.precompL D) (fderivWithin ℝ f Ω z) (g z)) k α hG1 hG2 hΩ
      _ ≤ ENNReal.ofReal ‖B‖ * bilinRHS α k f (fun z => fderivWithin ℝ g Ω z) Ω
            + ENNReal.ofReal ‖B‖ * bilinRHS α k (fun z => fderivWithin ℝ f Ω z) g Ω :=
          add_le_add hI1 hI2
      _ = ENNReal.ofReal ‖B‖ * bilinRHS α (k + 1) f g Ω := by
          rw [← mul_add, bilinRHS_fderiv_step α k hΩ]

theorem hSN_bilinear_le {D : Type u} {E F G : Type u} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (n : ℕ) (α : ℝ) (B : E →L[ℝ] F →L[ℝ] G) {f : D → E} {g : D → F} {Ω : Set D} (hf : ContDiffOn ℝ n f Ω) (hg : ContDiffOn ℝ n g Ω) (hΩ : UniqueDiffOn ℝ Ω) : hSN n α (fun x => B (f x) (g x)) Ω ≤ ENNReal.ofReal ‖B‖ * ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ENNReal) * (hSN i α f Ω * iDN (n - i) g Ω + iDN i f Ω * hSN (n - i) α g Ω) := by
  change hSN n α (fun x => B (f x) (g x)) Ω
    ≤ ENNReal.ofReal ‖B‖ * bilinRHS α n f g Ω
  exact hSN_bilinear_aux α n B hf hg hΩ

end Work.CR.Flat.Holder
