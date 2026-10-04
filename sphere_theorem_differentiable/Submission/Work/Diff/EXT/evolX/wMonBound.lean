/-
# The bound on a single monomial of the shuffle decomposition

This module proves `Work.Diff.EXT.evolX.wMonBound`: the monomial
`wMon g K₁ K₂ A B j w F`, i.e. the product of the `(wCntT w)`-th jet of the first operator `A` on its
sub-tuple with the `(wCntF w)`-th jet of the second operator `B` on its sub-tuple
(`Submission/Work/Diff/EXT/evolX/mulOpJetsDefs.lean`), is bounded by
`CA (wCntT w) · CB (wCntF w) · Shape g x (p + q + j)` times the product of the metric norms of the
entries of the level-`j` tuple.

The two factors are controlled by the single-level strengths `StrongAt g x p CA A` and
`StrongAt g x q CB B` (`Submission/Work/Diff/EXT/evolX/jetCalcDefs.lean`), which give

`|jetAll g (wCntT w) K₁ A (wTupA …) x| ≤ CA (wCntT w) · √(|∇^{p + wCntT w} Rm|²) · ∏_A √⟪·,·⟫`,
`|jetAll g (wCntF w) K₂ B (wTupB …) x| ≤ CB (wCntF w) · √(|∇^{q + wCntF w} Rm|²) · ∏_B √⟪·,·⟫`.

The level arithmetic is `sqrt_mul_sqrt_le_Shape`: the product of the two curvature norms is the
`(p + wCntT w)`-th term of the defining sum `Shape g x (p + q + j)`, because
`wCntT w + wCntF w = j`.  The remaining content is the *splitting of the product of the metric
norms* of the tuple into the `A`-part and the `B`-part, which is the product companion of
`Work.Diff.EXT.evolX.sumSplitWPos`: it follows from the injectivity of the position maps `wPA`,
`wPB` and their disjointness (`prod_split_of_inj` of
`Submission/Work/Diff/EXT/evolX/mulOpJetsPos.lean`).

Everything used here is sorry-free: `mulOpJetsPos`, `wPA_injective`, `wTupUntouchedA` (the
disjointness `wPosA_ne_wPosB_of_lt`), `wTupUpdateB` (the injectivity of `wPosB`), and `reactDefs`
(`Shape`, `sqrt_mul_sqrt_le_Shape`).
-/
import Mathlib
import Submission.Work.Diff.EXT.reactDefs
import Submission.Work.Diff.EXT.evolX.mulOpJetsDefs
import Submission.Work.Diff.EXT.evolX.mulOpJetsPos
import Submission.Work.Diff.EXT.evolX.wTupUpdateA
import Submission.Work.Diff.EXT.evolX.wTupUntouchedA
import Submission.Work.Diff.EXT.evolX.wTupUpdateB

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology BigOperators

namespace Work.Diff.EXT.evolX

open Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Injectivity of the two position maps

The content of `wPA` injectivity is the strict monotonicity
`Work.Diff.EXT.evolX.wTupUpdateA_wPosA_inj`, that of `wPB` injectivity the strict monotonicity
`Work.Diff.EXT.evolX.wTupUpdateB_wPosB_ne_val`.  At level `0` (the empty word) the two maps are
`Fin.castAdd K₂` resp. `Fin.natAdd K₁`. -/

theorem wMonBound_wPA_injective (K₁ K₂ n : ℕ) (w : Word n) :
    Function.Injective (wPA K₁ K₂ n w) := by
  cases n with
  | zero =>
    cases w with
    | nil =>
      intro i j hij
      apply Fin.ext
      have hv : (Fin.castAdd K₂ i).val = (Fin.castAdd K₂ j).val := by
        simpa only [wPA_nil] using congrArg Fin.val hij
      rwa [Fin.val_castAdd, Fin.val_castAdd] at hv
  | succ m =>
    intro i j hij
    apply Fin.ext
    simp only [wPA_succ] at hij
    exact wTupUpdateA_wPosA_inj m w K₁ K₂ i.isLt j.isLt hij

theorem wMonBound_wPB_injective (K₁ K₂ n : ℕ) (w : Word n) :
    Function.Injective (wPB K₁ K₂ n w) := by
  cases n with
  | zero =>
    cases w with
    | nil =>
      intro i q hiq
      apply Fin.ext
      have hv : (Fin.natAdd K₁ i).val = (Fin.natAdd K₁ q).val := by
        simpa only [wPB_nil] using congrArg Fin.val hiq
      rw [Fin.val_natAdd, Fin.val_natAdd] at hv
      omega
  | succ m =>
    intro i q hiq
    apply Fin.ext
    by_contra hne
    refine wTupUpdateB_wPosB_ne_val K₁ K₂ m w i.val q.val i.isLt q.isLt hne ?_
    simp only [wPB_succ] at hiq
    exact congrArg Fin.val hiq

/-! ## Disjointness of the two position maps

The companion of the injectivity statement: an `A`-position is never a `B`-position.  At level
`0` (the word is empty) the two maps are `Fin.castAdd K₂` and `Fin.natAdd K₁`, whose values lie in
`[0, K₁)` resp. `[K₁, K₁ + K₂)`; at level `n + 1` the statement is
`Work.Diff.EXT.evolX.wPosA_ne_wPosB_of_lt`. -/

theorem wMonBound_wPA_ne_wPB (K₁ K₂ n : ℕ) (w : Word n)
    (r : Fin (K₁ + wCntT w)) (q : Fin (K₂ + wCntF w)) :
    wPA K₁ K₂ n w r ≠ wPB K₁ K₂ n w q := by
  cases n with
  | zero =>
    cases w with
    | nil =>
      intro hcon
      have hv : (Fin.castAdd K₂ r).val = (Fin.natAdd K₁ q).val := by
        simpa only [wPA_nil, wPB_nil] using congrArg Fin.val hcon
      rw [Fin.val_castAdd, Fin.val_natAdd] at hv
      have hr : r.val < K₁ := by
        have h := r.isLt
        have hw : wCntT (Word.nil : Word 0) = 0 := rfl
        omega
      omega
  | succ m =>
    intro hcon
    rw [wPA_succ, wPB_succ] at hcon
    exact wPosA_ne_wPosB_of_lt K₁ K₂ m w r.val q.val r.isLt q.isLt hcon

/-! ## The splitting of the product of the metric norms -/

/-- **The product of the metric norms of the level-`j` tuple splits into the `A`-product and the
`B`-product.**  This is the product companion of `Work.Diff.EXT.evolX.sumSplitWPos`; it follows from
`prod_split_of_inj` applied to the position maps `wPA`, `wPB`, which are injective and disjoint. -/
theorem wMonBound_prodSplitTup (g : Submission.Diff.SMet I M) (K₁ K₂ j : ℕ) (w : Word j)
    (F : Fin (K₁ + K₂ + j) → TField (I := I) (M := M)) (x : M) :
    (∏ r : Fin (K₁ + wCntT w),
        Real.sqrt (g.inner x ((wTupA (I := I) (M := M) K₁ K₂ j w F) r x)
          ((wTupA (I := I) (M := M) K₁ K₂ j w F) r x)))
      * (∏ r : Fin (K₂ + wCntF w),
        Real.sqrt (g.inner x ((wTupB (I := I) (M := M) K₁ K₂ j w F) r x)
          ((wTupB (I := I) (M := M) K₁ K₂ j w F) r x)))
      = ∏ r : Fin (K₁ + K₂ + j), Real.sqrt (g.inner x (F r x) (F r x)) := by
  have hsplit := prod_split_of_inj (wPA K₁ K₂ j w) (wPB K₁ K₂ j w)
    (wMonBound_wPA_injective K₁ K₂ j w) (wMonBound_wPB_injective K₁ K₂ j w)
    (wMonBound_wPA_ne_wPB K₁ K₂ j w)
    (by have h := wCntT_add_wCntF w; omega)
    (fun s : Fin (K₁ + K₂ + j) => Real.sqrt (g.inner x (F s x) (F s x)))
  rw [hsplit]
  congr 1
  · exact Finset.prod_congr rfl (fun r _ => by rw [wTupA_eq_comp_wPA])
  · exact Finset.prod_congr rfl (fun r _ => by rw [wTupB_eq_comp_wPB])

/-! ## The elementary four-factor arithmetic -/

/-- **The arithmetic core of the monomial bound.**  From two bounds with nonnegative factors, the
comparison `yA * yB ≤ S` of the two middle factors and the identification `zA * zB = R` of the
two products, one gets the product bound. -/
private theorem wMonBound_arith {ja jb xA yA zA xB yB zB S R : ℝ}
    (ha : |ja| ≤ xA * yA * zA) (hb : |jb| ≤ xB * yB * zB)
    (hxA : 0 ≤ xA) (hyA : 0 ≤ yA) (hzA : 0 ≤ zA)
    (hxB : 0 ≤ xB) (hyB : 0 ≤ yB) (hzB : 0 ≤ zB)
    (hS : yA * yB ≤ S) (hPQ : zA * zB = R) :
    |ja * jb| ≤ xA * xB * S * R := by
  have hxA' : 0 ≤ xA * xB := mul_nonneg hxA hxB
  have hnn : 0 ≤ xA * yA * zA := mul_nonneg (mul_nonneg hxA hyA) hzA
  calc
    |ja * jb| = |ja| * |jb| := abs_mul ja jb
    _ ≤ (xA * yA * zA) * (xB * yB * zB) := mul_le_mul ha hb (abs_nonneg jb) hnn
    _ = xA * xB * (yA * yB) * (zA * zB) := by ring
    _ ≤ xA * xB * S * (zA * zB) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS hxA') (mul_nonneg hzA hzB)
    _ = xA * xB * S * R := by rw [hPQ]

/-- **The definitional unfolding of `wMon`**: the monomial is the product of the two jets. -/
private theorem wMonBound_wMon_eq (g : Submission.Diff.SMet I M) (K₁ K₂ j : ℕ)
    (A : (Fin K₁ → TField (I := I) (M := M)) → M → ℝ)
    (B : (Fin K₂ → TField (I := I) (M := M)) → M → ℝ) (w : Word j)
    (F : Fin (K₁ + K₂ + j) → TField (I := I) (M := M)) (x : M) :
    wMon (I := I) (M := M) g K₁ K₂ A B j w F x
      = jetAll g (wCntT w) K₁ A (wTupA (I := I) (M := M) K₁ K₂ j w F) x
        * jetAll g (wCntF w) K₂ B (wTupB (I := I) (M := M) K₁ K₂ j w F) x := rfl

theorem wMonBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x : M) (K₁ K₂ j p q : ℕ) (CA CB : ℕ → ℝ)
    (hCA : ∀ a, 0 ≤ CA a) (hCB : ∀ a, 0 ≤ CB a)
    (A : (Fin K₁ → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ)
    (B : (Fin K₂ → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ)
    (hA : Work.Diff.EXT.evolX.StrongAt g x p CA A)
    (hB : Work.Diff.EXT.evolX.StrongAt g x q CB B)
    (w : Work.Diff.EXT.evolX.Word j)
    (F : Fin (K₁ + K₂ + j) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) :
    |Work.Diff.EXT.evolX.wMon (I := I) (M := M) g K₁ K₂ A B j w F x|
      ≤ CA (Work.Diff.EXT.evolX.wCntT w) * CB (Work.Diff.EXT.evolX.wCntF w)
        * Work.Diff.EXT.Shape g x (p + q + j)
        * Finset.univ.prod (fun r : Fin (K₁ + K₂ + j) =>
            Real.sqrt (g.inner x (F r x) (F r x))) := by
  have hja := hA (wCntT w) (wTupA (I := I) (M := M) K₁ K₂ j w F)
    (wTupA_smooth (I := I) (M := M) w F hF)
  have hjb := hB (wCntF w) (wTupB (I := I) (M := M) K₁ K₂ j w F)
    (wTupB_smooth (I := I) (M := M) w F hF)
  have hprod := wMonBound_prodSplitTup (I := I) (M := M) g K₁ K₂ j w F x
  have hPnn : 0 ≤ ∏ r : Fin (K₁ + wCntT w),
      Real.sqrt (g.inner x ((wTupA (I := I) (M := M) K₁ K₂ j w F) r x)
        ((wTupA (I := I) (M := M) K₁ K₂ j w F) r x)) :=
    Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _
  have hQnn : 0 ≤ ∏ r : Fin (K₂ + wCntF w),
      Real.sqrt (g.inner x ((wTupB (I := I) (M := M) K₁ K₂ j w F) r x)
        ((wTupB (I := I) (M := M) K₁ K₂ j w F) r x)) :=
    Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _
  have hShape : Real.sqrt (curvNormK g x (p + wCntT w))
      * Real.sqrt (curvNormK g x (q + wCntF w)) ≤ Shape g x (p + q + j) :=
    sqrt_mul_sqrt_le_Shape g x (by have h := wCntT_add_wCntF w; omega)
  rw [wMonBound_wMon_eq]
  exact wMonBound_arith hja hjb (hCA _) (Real.sqrt_nonneg _) hPnn
    (hCB _) (Real.sqrt_nonneg _) hQnn hShape hprod

end Work.Diff.EXT.evolX
