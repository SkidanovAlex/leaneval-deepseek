import Mathlib
import Submission.Work.Diff.EXT.evolX.substB.Defs

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The per-word recursion of the composition ladder

This module proves `Work.Diff.EXT.evolX.Stw_extStep`: the per-word recursion of the composition
ladder of `Submission.Work.Diff.EXT.evolX.substB`.  The ladder states `Stw g V U a w` pair the
`wCntT w`-fold covariant derivative of the vector-valued operator `U` (on the `A`-sub-tuple of the
word `w`) with the `wCntF w`-fold covariant derivative of `V` (on the `B`-sub-tuple).  The recursion
says that the packed covariant derivative `extStep` of the state of `w` is the sum of the states of
`cons true w` and `cons false w` (the new derivative direction goes to the `U`-side resp. the
`V`-side).

## The proof

Everything is reduced to the pointwise identity

`Stw_core` :
`mvfderiv (⟪dvc^t U(A), dvc^f V(B)⟫) (X) − ∑_ρ ⟪dvc^t U(A[ρ ← ∇_{A ρ}X]), dvc^f V(B)⟫
   − ∑_σ ⟪dvc^t U(A), dvc^f V(B[σ ← ∇_{B σ}X])⟫
 = ⟪dvc^{t+1} U(X :: A), dvc^f V(B)⟫ + ⟪dvc^t U(A), dvc^{f+1} V(X :: B)⟫`

which is the metric-compatibility (Leibniz) rule `pairingSplitNB` for the pairing of the two
sections, combined with the definitional rearrangement `stb_dvcStep_eq` of `dvStep`.

The two cases of the recursion are then pure bookkeeping:

* `Stw_extStep_zero` — the empty word (`a = 0`), where the correction sum over `Fin (K+2)` is split
  by `Fin.sum_univ_add`;
* `Stw_extStep_cons` — a word `cons b w` (`a = n+1`), where the correction sum is split by
  `sumSplitWPos` along the `A`/`B`-positions `wPosA`/`wPosB`, using the update/untouched lemmas
  `wTupUpdateA`/`wTupUntouchedA`/`wTupUpdateB`/`wTupUntouchedB`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## Linearity of the metric pairing -/

theorem ginner_add_left {g : Submission.Diff.SMet I M} {y : M} (a b c : TangentSpace I y) :
    g.inner y (a + b) c = g.inner y a c + g.inner y b c := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  change inner ℝ (a + b) c = inner ℝ a c + inner ℝ b c
  rw [inner_add_left]

theorem ginner_add_right {g : Submission.Diff.SMet I M} {y : M} (a b c : TangentSpace I y) :
    g.inner y a (b + c) = g.inner y a b + g.inner y a c := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  change inner ℝ a (b + c) = inner ℝ a b + inner ℝ a c
  rw [inner_add_right]

theorem ginner_sum_left {g : Submission.Diff.SMet I M} {y : M} {ι : Type*}
    (s : Finset ι) (f : ι → TangentSpace I y) (c : TangentSpace I y) :
    g.inner y (∑ i ∈ s, f i) c = ∑ i ∈ s, g.inner y (f i) c := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  change inner ℝ (∑ i ∈ s, f i) c = ∑ i ∈ s, inner ℝ (f i) c
  rw [sum_inner]

theorem ginner_sum_right {g : Submission.Diff.SMet I M} {y : M} {ι : Type*}
    (s : Finset ι) (f : ι → TangentSpace I y) (c : TangentSpace I y) :
    g.inner y c (∑ i ∈ s, f i) = ∑ i ∈ s, g.inner y c (f i) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  change inner ℝ c (∑ i ∈ s, f i) = ∑ i ∈ s, inner ℝ c (f i)
  rw [inner_sum]

/-! ## The core identity -/

/-- **The Leibniz step, in the form in which the two cases use it.**  Differentiating the pairing
of the `t`-fold derivative of `U` with the `f`-fold derivative of `V` along `X` produces the two
terms where the direction hits one of the two factors; the correction sums of `extStep` are exactly
the two sums on the left. -/
theorem Stw_core (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) {K : ℕ}
    (V : (Fin 2 → TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (U : (Fin K → TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    {t f : ℕ} (A : Fin (K + t) → TField (I := I) (M := M))
    (B : Fin (2 + f) → TField (I := I) (M := M))
    (X : TField (I := I) (M := M)) {y : M}
    (hα : MDifferentiableAt I I.tangent
      (fun z : M => Bundle.TotalSpace.mk' E z (dvc g K U t A z)) y)
    (hβ : MDifferentiableAt I I.tangent
      (fun z : M => Bundle.TotalSpace.mk' E z (dvc g 2 V f B z)) y) :
    mvfderiv I (fun z : M => g.inner z (dvc g K U t A z) (dvc g 2 V f B z)) y (X y)
      - (∑ ρ : Fin (K + t), g.inner y
          (dvc g K U t (Function.update A ρ (dirF g (A ρ) X)) y) (dvc g 2 V f B y))
      - (∑ σ : Fin (2 + f), g.inner y (dvc g K U t A y)
          (dvc g 2 V f (Function.update B σ (dirF g (B σ) X)) y))
      = g.inner y (dvc g K U (t + 1) (Fin.cons X A) y) (dvc g 2 V f B y)
        + g.inner y (dvc g K U t A y) (dvc g 2 V (f + 1) (Fin.cons X B) y) := by
  have hα' : (Submission.Diff.lcOf g) (dvc g K U t A) y (X y)
      = dvc g K U (t + 1) (Fin.cons X A) y
        + ∑ ρ : Fin (K + t), dvc g K U t (Function.update A ρ (dirF g (A ρ) X)) y := by
    have h := congrFun (stb_dvcStep_eq (I := I) (M := M) g U t A X) y
    simpa using h
  have hβ' : (Submission.Diff.lcOf g) (dvc g 2 V f B) y (X y)
      = dvc g 2 V (f + 1) (Fin.cons X B) y
        + ∑ σ : Fin (2 + f), dvc g 2 V f (Function.update B σ (dirF g (B σ) X)) y := by
    have h := congrFun (stb_dvcStep_eq (I := I) (M := M) g V f B X) y
    simpa using h
  have hpair := pairingSplitNB (I := I) (M := M) hLC g (v := X y) hα hβ
  rw [hpair, hα', hβ']
  rw [ginner_add_left, ginner_add_right, ginner_sum_left, ginner_sum_right]
  ring

/-! ## The level-`0` sub-tuples -/

private theorem wTupA_zero_eq (K₁ K₂ : ℕ) (F : Fin (K₁ + K₂) → TField (I := I) (M := M)) :
    wTupA (I := I) (M := M) K₁ K₂ 0 Word.nil F
      = fun i : Fin K₁ => F (Fin.castAdd K₂ i) := by
  funext i
  rw [wTupA.eq_1]
  exact congrArg F (Fin.ext rfl)

private theorem wTupB_zero_eq (K₁ K₂ : ℕ) (F : Fin (K₁ + K₂) → TField (I := I) (M := M)) :
    wTupB (I := I) (M := M) K₁ K₂ 0 Word.nil F
      = fun i : Fin K₂ => F (Fin.natAdd K₁ i) := by
  funext i
  rw [wTupB.eq_1]
  exact congrArg F (Fin.ext rfl)

theorem wTupA_zero_update_castAdd (K₁ K₂ : ℕ) (F : Fin (K₁ + K₂) → TField (I := I) (M := M))
    (v : TField (I := I) (M := M)) (ρ : Fin K₁) :
    wTupA (I := I) (M := M) K₁ K₂ 0 Word.nil (Function.update F (Fin.castAdd K₂ ρ) v)
      = Function.update (wTupA (I := I) (M := M) K₁ K₂ 0 Word.nil F) ρ v := by
  rw [wTupA_zero_eq, wTupA_zero_eq]
  funext i
  rw [Function.update_apply, Function.update_apply]
  by_cases h : i = ρ
  · rw [ite_eq_left h, ite_eq_left (congrArg (Fin.castAdd K₂) h)]
  · rw [ite_eq_right h, ite_eq_right (fun hc => h (Fin.castAdd_injective K₁ K₂ hc))]

theorem wTupB_zero_untouched_castAdd (K₁ K₂ : ℕ) (F : Fin (K₁ + K₂) → TField (I := I) (M := M))
    (v : TField (I := I) (M := M)) (ρ : Fin K₁) :
    wTupB (I := I) (M := M) K₁ K₂ 0 Word.nil (Function.update F (Fin.castAdd K₂ ρ) v)
      = wTupB (I := I) (M := M) K₁ K₂ 0 Word.nil F := by
  rw [wTupB_zero_eq, wTupB_zero_eq]
  funext i
  rw [Function.update_apply]
  rw [ite_eq_right]
  intro hc
  have hv := congrArg Fin.val hc
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

theorem wTupA_zero_untouched_natAdd (K₁ K₂ : ℕ) (F : Fin (K₁ + K₂) → TField (I := I) (M := M))
    (v : TField (I := I) (M := M)) (σ : Fin K₂) :
    wTupA (I := I) (M := M) K₁ K₂ 0 Word.nil (Function.update F (Fin.natAdd K₁ σ) v)
      = wTupA (I := I) (M := M) K₁ K₂ 0 Word.nil F := by
  rw [wTupA_zero_eq, wTupA_zero_eq]
  funext i
  rw [Function.update_apply]
  rw [ite_eq_right]
  intro hc
  have hv := congrArg Fin.val hc
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

theorem wTupB_zero_update_natAdd (K₁ K₂ : ℕ) (F : Fin (K₁ + K₂) → TField (I := I) (M := M))
    (v : TField (I := I) (M := M)) (σ : Fin K₂) :
    wTupB (I := I) (M := M) K₁ K₂ 0 Word.nil (Function.update F (Fin.natAdd K₁ σ) v)
      = Function.update (wTupB (I := I) (M := M) K₁ K₂ 0 Word.nil F) σ v := by
  rw [wTupB_zero_eq, wTupB_zero_eq]
  funext i
  rw [Function.update_apply, Function.update_apply]
  by_cases h : i = σ
  · rw [ite_eq_left h, ite_eq_left (congrArg (Fin.natAdd K₁) h)]
  · rw [ite_eq_right h, ite_eq_right (fun hc => h (Fin.natAdd_injective K₂ K₁ hc))]

/-! ## The splitting of the correction sum -/

/-- **The correction sum of `extStep`, split along the `A`/`B`-positions of the word.** -/
theorem Stw_corrSplit_cons (g : Submission.Diff.SMet I M) {K : ℕ}
    (V : (Fin 2 → TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (U : (Fin K → TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (n : ℕ) (w : Word (n + 1))
    (F : Fin (K + 2 + (n + 1)) → TField (I := I) (M := M))
    (X : TField (I := I) (M := M)) (y : M) :
    (∑ s : Fin (K + 2 + (n + 1)),
        Stw (I := I) (M := M) g V U (n + 1) w (Function.update F s (dirF g (F s) X)) y)
      = (∑ ρ : Fin (K + wCntT w), g.inner y
          (dvc g K U (wCntT w) (Function.update (wTupA K 2 (n + 1) w F) ρ
            (dirF g (wTupA K 2 (n + 1) w F ρ) X)) y)
          (dvc g 2 V (wCntF w) (wTupB K 2 (n + 1) w F) y))
        + (∑ σ : Fin (2 + wCntF w), g.inner y
          (dvc g K U (wCntT w) (wTupA K 2 (n + 1) w F) y)
          (dvc g 2 V (wCntF w) (Function.update (wTupB K 2 (n + 1) w F) σ
            (dirF g (wTupB K 2 (n + 1) w F σ) X)) y)) := by
  rw [sumSplitWPos K 2 n w (fun s => Stw (I := I) (M := M) g V U (n + 1) w
        (Function.update F s (dirF g (F s) X)) y)]
  congr 1
  · refine Finset.sum_congr rfl (fun ρ _ => ?_)
    simp only [Stw]
    rw [wTupUpdateA K 2 n w F _ ρ, wTupUntouchedA K 2 n w F _ ρ]
    rfl
  · refine Finset.sum_congr rfl (fun σ _ => ?_)
    simp only [Stw]
    rw [wTupUntouchedB K 2 n w F _ σ, wTupUpdateB K 2 n w F _ σ]
    rfl

/-- **The correction sum of `extStep`, split along the `A`/`B`-positions of the empty word.** -/
theorem Stw_corrSplit_zero (g : Submission.Diff.SMet I M) {K : ℕ}
    (V : (Fin 2 → TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (U : (Fin K → TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (F : Fin (K + 2 + 0) → TField (I := I) (M := M))
    (X : TField (I := I) (M := M)) (y : M) :
    (∑ s : Fin (K + 2 + 0),
        Stw (I := I) (M := M) g V U 0 Word.nil (Function.update F s (dirF g (F s) X)) y)
      = (∑ ρ : Fin (K + 0), g.inner y
          (dvc g K U 0 (Function.update (wTupA K 2 0 Word.nil F) ρ
            (dirF g (wTupA K 2 0 Word.nil F ρ) X)) y)
          (dvc g 2 V 0 (wTupB K 2 0 Word.nil F) y))
        + (∑ σ : Fin (2 + 0), g.inner y
          (dvc g K U 0 (wTupA K 2 0 Word.nil F) y)
          (dvc g 2 V 0 (Function.update (wTupB K 2 0 Word.nil F) σ
            (dirF g (wTupB K 2 0 Word.nil F σ) X)) y)) := by
  rw [Fin.sum_univ_add (a := K) (b := 2)
    (f := fun s => Stw (I := I) (M := M) g V U 0 Word.nil
      (Function.update F s (dirF g (F s) X)) y)]
  congr 1
  · refine Finset.sum_congr rfl (fun ρ _ => ?_)
    simp only [Stw]
    rw [wTupA_zero_update_castAdd K 2 F _ ρ, wTupB_zero_untouched_castAdd K 2 F _ ρ]
    rfl
  · refine Finset.sum_congr rfl (fun σ _ => ?_)
    simp only [Stw]
    rw [wTupA_zero_untouched_natAdd K 2 F _ σ, wTupB_zero_update_natAdd K 2 F _ σ]
    rfl

/-! ## The two cases of the recursion -/

/-- **The empty-word case** (`a = 0`) of `Stw_extStep`. -/
theorem Stw_extStep_zero
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M) {K : ℕ}
    (V : (Fin 2 → TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (U : (Fin K → TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (hVs : JetSmoothOp (I := I) (M := M) g 3 (pairVec (I := I) (M := M) g V) x)
    (hUs : JetSmoothOp (I := I) (M := M) g (K + 1) (pairVec (I := I) (M := M) g U) x)
    (F : Fin (K + 2 + (0 + 1)) → TField (I := I) (M := M))
    (hF : ∀ i, SmoothF (I := I) (M := M) (F i)) :
    Filter.EventuallyEq (nhds x)
      (fun y : M => extStep (I := I) (M := M) g
        (Stw (I := I) (M := M) g V U 0 Word.nil) F y)
      (fun y : M => Stw (I := I) (M := M) g V U (0 + 1) (Word.cons true Word.nil) F y
        + Stw (I := I) (M := M) g V U (0 + 1) (Word.cons false Word.nil) F y) := by
  have hFs : ∀ i, SmoothF (I := I) (M := M)
      ((fun i : Fin (K + 2 + 0) => F i.succ) i) := fun i => hF i.succ
  have hmdA := dvcFieldSmooth (I := I) (M := M) hLC g x U hUs 0
    (wTupA (I := I) (M := M) K 2 0 Word.nil (fun i : Fin (K + 2 + 0) => F i.succ))
    (wTupA_smooth (I := I) (M := M) Word.nil _ hFs)
  have hmdB := dvcFieldSmooth (I := I) (M := M) hLC g x V hVs 0
    (wTupB (I := I) (M := M) K 2 0 Word.nil (fun i : Fin (K + 2 + 0) => F i.succ))
    (wTupB_smooth (I := I) (M := M) Word.nil _ hFs)
  filter_upwards [hmdA, hmdB] with y hyA hyB
  calc extStep (I := I) (M := M) g (Stw (I := I) (M := M) g V U 0 Word.nil) F y
      = mvfderiv I (fun z : M => g.inner z
            (dvc g K U 0 (wTupA (I := I) (M := M) K 2 0 Word.nil
              (fun i : Fin (K + 2 + 0) => F i.succ)) z)
            (dvc g 2 V 0 (wTupB (I := I) (M := M) K 2 0 Word.nil
              (fun i : Fin (K + 2 + 0) => F i.succ)) z)) y (F 0 y)
          - (∑ ρ : Fin (K + 0), g.inner y
              (dvc g K U 0 (Function.update (wTupA (I := I) (M := M) K 2 0 Word.nil
                (fun i : Fin (K + 2 + 0) => F i.succ)) ρ
                (dirF g (wTupA (I := I) (M := M) K 2 0 Word.nil
                  (fun i : Fin (K + 2 + 0) => F i.succ) ρ) (F 0))) y)
              (dvc g 2 V 0 (wTupB (I := I) (M := M) K 2 0 Word.nil
                (fun i : Fin (K + 2 + 0) => F i.succ)) y))
          - (∑ σ : Fin (2 + 0), g.inner y
              (dvc g K U 0 (wTupA (I := I) (M := M) K 2 0 Word.nil
                (fun i : Fin (K + 2 + 0) => F i.succ)) y)
              (dvc g 2 V 0 (Function.update (wTupB (I := I) (M := M) K 2 0 Word.nil
                (fun i : Fin (K + 2 + 0) => F i.succ)) σ
                (dirF g (wTupB (I := I) (M := M) K 2 0 Word.nil
                  (fun i : Fin (K + 2 + 0) => F i.succ) σ) (F 0))) y)) := by
        rw [show extStep (I := I) (M := M) g (Stw (I := I) (M := M) g V U 0 Word.nil) F y
            = mvfderiv I (Stw (I := I) (M := M) g V U 0 Word.nil
                (fun i : Fin (K + 2 + 0) => F i.succ)) y (F 0 y)
              - ∑ s : Fin (K + 2 + 0), Stw (I := I) (M := M) g V U 0 Word.nil
                  (Function.update (fun i : Fin (K + 2 + 0) => F i.succ) s
                    (dirF g ((fun i : Fin (K + 2 + 0) => F i.succ) s) (F 0))) y
            from rfl]
        rw [Stw_corrSplit_zero (I := I) (M := M) g V U
          (fun i : Fin (K + 2 + 0) => F i.succ) (F 0) y]
        rw [sub_add_eq_sub_sub]
        have hStw : Stw (I := I) (M := M) g V U 0 Word.nil (fun i : Fin (K + 2 + 0) => F i.succ)
            = fun z : M => g.inner z
                (dvc g K U 0 (wTupA (I := I) (M := M) K 2 0 Word.nil
                  (fun i : Fin (K + 2 + 0) => F i.succ)) z)
                (dvc g 2 V 0 (wTupB (I := I) (M := M) K 2 0 Word.nil
                  (fun i : Fin (K + 2 + 0) => F i.succ)) z) := rfl
        rw [hStw]
    _ = g.inner y
          (dvc g K U (0 + 1) (Fin.cons (F 0) (wTupA (I := I) (M := M) K 2 0 Word.nil
            (fun i : Fin (K + 2 + 0) => F i.succ))) y)
          (dvc g 2 V 0 (wTupB (I := I) (M := M) K 2 0 Word.nil
            (fun i : Fin (K + 2 + 0) => F i.succ)) y)
        + g.inner y
          (dvc g K U 0 (wTupA (I := I) (M := M) K 2 0 Word.nil
            (fun i : Fin (K + 2 + 0) => F i.succ)) y)
          (dvc g 2 V (0 + 1) (Fin.cons (F 0) (wTupB (I := I) (M := M) K 2 0 Word.nil
            (fun i : Fin (K + 2 + 0) => F i.succ))) y) :=
        Stw_core (I := I) (M := M) hLC g V U _ _ (F 0) hyA hyB
    _ = Stw (I := I) (M := M) g V U (0 + 1) (Word.cons true Word.nil) F y
        + Stw (I := I) (M := M) g V U (0 + 1) (Word.cons false Word.nil) F y := by
        simp only [Stw, wTupConsTrue, wTupBConsTrue, wTupConsFalse, wTupBConsFalse,
          wCntT_cons_true, wCntF_cons_true, wCntT_cons_false, wCntF_cons_false]
        rfl

/-- **The `cons` case** (`a = n + 1`) of `Stw_extStep`. -/
theorem Stw_extStep_cons
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M) {K : ℕ}
    (V : (Fin 2 → TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (U : (Fin K → TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (hVs : JetSmoothOp (I := I) (M := M) g 3 (pairVec (I := I) (M := M) g V) x)
    (hUs : JetSmoothOp (I := I) (M := M) g (K + 1) (pairVec (I := I) (M := M) g U) x)
    (n : ℕ) (w : Word (n + 1))
    (F : Fin (K + 2 + ((n + 1) + 1)) → TField (I := I) (M := M))
    (hF : ∀ i, SmoothF (I := I) (M := M) (F i)) :
    Filter.EventuallyEq (nhds x)
      (fun y : M => extStep (I := I) (M := M) g
        (Stw (I := I) (M := M) g V U (n + 1) w) F y)
      (fun y : M => Stw (I := I) (M := M) g V U ((n + 1) + 1) (Word.cons true w) F y
        + Stw (I := I) (M := M) g V U ((n + 1) + 1) (Word.cons false w) F y) := by
  have hFs : ∀ i, SmoothF (I := I) (M := M)
      ((fun i : Fin (K + 2 + (n + 1)) => F i.succ) i) := fun i => hF i.succ
  have hmdA := dvcFieldSmooth (I := I) (M := M) hLC g x U hUs (wCntT w)
    (wTupA (I := I) (M := M) K 2 (n + 1) w (fun i : Fin (K + 2 + (n + 1)) => F i.succ))
    (wTupA_smooth (I := I) (M := M) w _ hFs)
  have hmdB := dvcFieldSmooth (I := I) (M := M) hLC g x V hVs (wCntF w)
    (wTupB (I := I) (M := M) K 2 (n + 1) w (fun i : Fin (K + 2 + (n + 1)) => F i.succ))
    (wTupB_smooth (I := I) (M := M) w _ hFs)
  filter_upwards [hmdA, hmdB] with y hyA hyB
  calc extStep (I := I) (M := M) g (Stw (I := I) (M := M) g V U (n + 1) w) F y
      = mvfderiv I (fun z : M => g.inner z
            (dvc g K U (wCntT w) (wTupA (I := I) (M := M) K 2 (n + 1) w
              (fun i : Fin (K + 2 + (n + 1)) => F i.succ)) z)
            (dvc g 2 V (wCntF w) (wTupB (I := I) (M := M) K 2 (n + 1) w
              (fun i : Fin (K + 2 + (n + 1)) => F i.succ)) z)) y (F 0 y)
          - (∑ ρ : Fin (K + wCntT w), g.inner y
              (dvc g K U (wCntT w) (Function.update (wTupA (I := I) (M := M) K 2 (n + 1) w
                (fun i : Fin (K + 2 + (n + 1)) => F i.succ)) ρ
                (dirF g (wTupA (I := I) (M := M) K 2 (n + 1) w
                  (fun i : Fin (K + 2 + (n + 1)) => F i.succ) ρ) (F 0))) y)
              (dvc g 2 V (wCntF w) (wTupB (I := I) (M := M) K 2 (n + 1) w
                (fun i : Fin (K + 2 + (n + 1)) => F i.succ)) y))
          - (∑ σ : Fin (2 + wCntF w), g.inner y
              (dvc g K U (wCntT w) (wTupA (I := I) (M := M) K 2 (n + 1) w
                (fun i : Fin (K + 2 + (n + 1)) => F i.succ)) y)
              (dvc g 2 V (wCntF w) (Function.update (wTupB (I := I) (M := M) K 2 (n + 1) w
                (fun i : Fin (K + 2 + (n + 1)) => F i.succ)) σ
                (dirF g (wTupB (I := I) (M := M) K 2 (n + 1) w
                  (fun i : Fin (K + 2 + (n + 1)) => F i.succ) σ) (F 0))) y)) := by
        rw [show extStep (I := I) (M := M) g (Stw (I := I) (M := M) g V U (n + 1) w) F y
            = mvfderiv I (Stw (I := I) (M := M) g V U (n + 1) w
                (fun i : Fin (K + 2 + (n + 1)) => F i.succ)) y (F 0 y)
              - ∑ s : Fin (K + 2 + (n + 1)), Stw (I := I) (M := M) g V U (n + 1) w
                  (Function.update (fun i : Fin (K + 2 + (n + 1)) => F i.succ) s
                    (dirF g ((fun i : Fin (K + 2 + (n + 1)) => F i.succ) s) (F 0))) y
            from rfl]
        rw [Stw_corrSplit_cons (I := I) (M := M) g V U n w
          (fun i : Fin (K + 2 + (n + 1)) => F i.succ) (F 0) y]
        rw [sub_add_eq_sub_sub]
        have hStw : Stw (I := I) (M := M) g V U (n + 1) w
            (fun i : Fin (K + 2 + (n + 1)) => F i.succ)
            = fun z : M => g.inner z
                (dvc g K U (wCntT w) (wTupA (I := I) (M := M) K 2 (n + 1) w
                  (fun i : Fin (K + 2 + (n + 1)) => F i.succ)) z)
                (dvc g 2 V (wCntF w) (wTupB (I := I) (M := M) K 2 (n + 1) w
                  (fun i : Fin (K + 2 + (n + 1)) => F i.succ)) z) := rfl
        rw [hStw]
    _ = g.inner y
          (dvc g K U (wCntT w + 1) (Fin.cons (F 0) (wTupA (I := I) (M := M) K 2 (n + 1) w
            (fun i : Fin (K + 2 + (n + 1)) => F i.succ))) y)
          (dvc g 2 V (wCntF w) (wTupB (I := I) (M := M) K 2 (n + 1) w
            (fun i : Fin (K + 2 + (n + 1)) => F i.succ)) y)
        + g.inner y
          (dvc g K U (wCntT w) (wTupA (I := I) (M := M) K 2 (n + 1) w
            (fun i : Fin (K + 2 + (n + 1)) => F i.succ)) y)
          (dvc g 2 V (wCntF w + 1) (Fin.cons (F 0) (wTupB (I := I) (M := M) K 2 (n + 1) w
            (fun i : Fin (K + 2 + (n + 1)) => F i.succ))) y) :=
        Stw_core (I := I) (M := M) hLC g V U _ _ (F 0) hyA hyB
    _ = Stw (I := I) (M := M) g V U ((n + 1) + 1) (Word.cons true w) F y
        + Stw (I := I) (M := M) g V U ((n + 1) + 1) (Word.cons false w) F y := by
        simp only [Stw, wTupConsTrue, wTupBConsTrue, wTupConsFalse, wTupBConsFalse,
          wCntT_cons_true, wCntF_cons_true, wCntT_cons_false, wCntF_cons_false]

/-! ## The target -/

theorem Stw_extStep
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M) {K : ℕ}
    (V : (Fin 2 → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (hVs : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g 3
      (Work.Diff.EXT.evolX.pairVec (I := I) (M := M) g V) x)
    (hUs : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g (K + 1)
      (Work.Diff.EXT.evolX.pairVec (I := I) (M := M) g U) x)
    (a : ℕ) (w : Work.Diff.EXT.evolX.Word a)
    (F : Fin (K + 2 + (a + 1)) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) :
    Filter.EventuallyEq (nhds x)
      (fun y : M => Work.Diff.EXT.extStep (I := I) (M := M) g
        (Work.Diff.EXT.evolX.Stw (I := I) (M := M) g V U a w) F y)
      (fun y : M => Work.Diff.EXT.evolX.Stw (I := I) (M := M) g V U (a + 1)
          (Work.Diff.EXT.evolX.Word.cons true w) F y
        + Work.Diff.EXT.evolX.Stw (I := I) (M := M) g V U (a + 1)
          (Work.Diff.EXT.evolX.Word.cons false w) F y) := by
  cases a with
  | zero =>
      cases w with
      | nil => exact Stw_extStep_zero (I := I) (M := M) hLC g x V U hVs hUs F hF
  | succ n => exact Stw_extStep_cons (I := I) (M := M) hLC g x V U hVs hUs n w F hF

end Work.Diff.EXT.evolX
