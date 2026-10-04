import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.OSubKit
import Submission.Work.Diff.EXT.ConnCov.RicFlip.towerSlotAddSmValDep

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `deltaTowerM_bndV`: the moving `δ`-tower bound from the moving `aOf`-tower bound

Let `G : ℝ → SMet I M`, `δ := covDiff G t = ∇^{G t} − ∇^{G 0}` (a `(1,2)`-tensor, `Kit.lean`) and
`δ_c := ∇^{G t,c} δ = deltaTowerM G t c` the `c`-th covariant derivative of `δ` with respect to the
**moving** connection `∇^{G t}`.

The metric-compatibility collapse `Work.Diff.EXT.ConnCov.RicFlip.towerEqLoweringDeltaTowerM` reads

  `tower (lcOf (G t)) (aOf G t) c v A B C y = (G t).inner y (δ_c v B A y) (C y)`,

so a `ValBound` on the moving `aOf`-tower `∇^{G t,c} aOf` (the bound `hAm` of the target) is
*exactly* a bound on the pairing of `δ_c` with the moving metric, evaluated on the canonical smooth
extensions `smoothExt x ·` of pointwise vectors.  Since `δ_c` is a tensor (`c`-fold covariant
derivative of a tensor field), its value at `x` depends only on the values at `x` of its slots
(`aOfTower_valDep`, obtained from the value-dependence machinery
`Work.Diff.EXT.ConnCov.RicFlip.towerSlotAddSmValDep` applied to the base `aOf G t`, whose
value-dependence/linearity/smoothness are the pointwise properties of the difference one-form
`CovariantDerivative.difference (lcOf (G t)) (lcOf (G 0))`), one may replace an arbitrary smooth
tuple by the `smoothExt`-tuple at `x` and read off

  `|⟪δ_c v X Z x, w⟫| ≤ Bm c · (∏ ‖v i x‖) · ‖Z x‖ · ‖X x‖ · ‖w‖`

for `w := δ_c v X Z x`.  Taking `w` as the last slot and using `‖w‖² = ⟪w,w⟫` gives the stated
`AMB.BndV` bound (`(∏ ‖·‖) ≤ (∏ (1 + ‖·‖))`).

**Import hygiene.**  The files of the `ConnCov` area that carry the level-`0` `aOf` calculus
(`deltaTower.lean`, `slotAdd_aOf_local.lean`, `gtTower_succ_eq_swap.lean`) declare the same names as
`RicTowerKit.lean` (e.g. `Work.Diff.EXT.ConnCov.vstep`) and can therefore *not* be imported
together with it.  All the level-`0` facts about `aOf` needed here are therefore restated and proved
in this file from Mathlib's difference one-form `CovariantDerivative.difference` and the
smoothness API `Work.Diff.EXT.ATower.lcOf_apply_smE`, `Work.Diff.GE.katoMetricPairingSmooth`.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

namespace RicFlip

open Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

lemma inner_self_nonneg_M (g : SMet I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with h | h
  · subst h; simp
  · exact le_of_lt (g.pos x v h)

theorem covDiff_eq_difference_M (G : ℝ → SMet I M) (t : ℝ)
    (X Z : TF (I := I) (M := M)) (x : M) (hX : SmE I M X) :
    covDiff G t X Z x
      = (CovariantDerivative.difference (lcOf (G t)) (lcOf (G 0))) x (X x) (Z x) := by
  rw [show covDiff G t X Z x
      = ((lcOf (G t)) X x) (Z x) - ((lcOf (G 0)) X x) (Z x) from rfl]
  rw [← sub_apply]
  exact congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L (Z x))
    (IsCovariantDerivativeOn.difference_apply
      (hcov := (Submission.Diff.lcOf (G t)).isCovariantDerivativeOnUniv)
      (hcov' := (Submission.Diff.lcOf (G 0)).isCovariantDerivativeOnUniv)
      (x := x) (hx := trivial) (σ := X) (hX.mdifferentiableAt (by simp))).symm

theorem aOf_eq_difference_inner (G : ℝ → SMet I M) (t : ℝ)
    (A B C : TF (I := I) (M := M)) (x : M) (hB : SmE I M B) :
    aOf G t A B C x = (G t).inner x
      ((CovariantDerivative.difference (lcOf (G t)) (lcOf (G 0))) x (B x) (A x)) (C x) := by
  have h1 : aOf G t A B C x = (G t).inner x (covDiff G t B A x) (C x) := by
    simp only [Work.Diff.EXT.aOf, Work.Diff.EXT.ConnCov.covDiff, Pi.sub_apply]
  rw [h1, covDiff_eq_difference_M (I := I) (M := M) G t B A x hB]

theorem aOf_valDep (G : ℝ → SMet I M) (t : ℝ)
    (A A' B B' C C' : TF (I := I) (M := M)) (x : M) (hB : SmE I M B) (hB' : SmE I M B')
    (hAA : A x = A' x) (hBB : B x = B' x) (hCC : C x = C' x) :
    aOf G t A B C x = aOf G t A' B' C' x := by
  rw [aOf_eq_difference_inner (I := I) (M := M) G t A B C x hB,
    aOf_eq_difference_inner (I := I) (M := M) G t A' B' C' x hB', hBB, hAA, hCC]

theorem aOf_add_dir (G : ℝ → SMet I M) (t : ℝ) (A A' B C : TF (I := I) (M := M)) :
    aOf G t (A + A') B C = aOf G t A B C + aOf G t A' B C := by
  funext y
  simp only [Work.Diff.EXT.aOf, Pi.add_apply, sub_apply, add_apply, map_add, map_sub]
  ring

theorem aOf_add_sec (G : ℝ → SMet I M) (t : ℝ) (A B B' C : TF (I := I) (M := M))
    (hB : SmE I M B) (hB' : SmE I M B') :
    aOf G t A (B + B') C = aOf G t A B C + aOf G t A B' C := by
  funext x
  rw [aOf_eq_difference_inner (I := I) (M := M) G t A (B + B') C x (hB.add_section hB')]
  simp only [Pi.add_apply]
  rw [aOf_eq_difference_inner (I := I) (M := M) G t A B C x hB,
    aOf_eq_difference_inner (I := I) (M := M) G t A B' C x hB']
  simp only [Pi.add_apply, add_apply, map_add]

theorem aOf_add_res (G : ℝ → SMet I M) (t : ℝ) (A B C C' : TF (I := I) (M := M)) :
    aOf G t A B (C + C') = aOf G t A B C + aOf G t A B C' := by
  funext y
  simp only [Work.Diff.EXT.aOf, Pi.add_apply, add_apply, map_add]

theorem aOf_lin_dir (G : ℝ → SMet I M) (t : ℝ)
    (X₁ X₂ : TF (I := I) (M := M)) (f₁ f₂ : M → ℝ) (B C : TF (I := I) (M := M)) (x : M) :
    aOf G t (f₁ • X₁ + f₂ • X₂) B C x = f₁ x * aOf G t X₁ B C x + f₂ x * aOf G t X₂ B C x := by
  have hpt : (f₁ • X₁ + f₂ • X₂) x = f₁ x • X₁ x + f₂ x • X₂ x := rfl
  simp only [Work.Diff.EXT.aOf, hpt, sub_apply, add_apply, smul_apply, map_add, map_sub,
    map_smul, smul_eq_mul]
  ring

theorem aOf_lin_sec (G : ℝ → SMet I M) (t : ℝ)
    (A : TF (I := I) (M := M)) (X₁ X₂ : TF (I := I) (M := M)) (f₁ f₂ : M → ℝ) (C : TF (I := I) (M := M)) (x : M)
    (hf₁ : SmF I M f₁) (hf₂ : SmF I M f₂) (hX₁ : SmE I M X₁) (hX₂ : SmE I M X₂) :
    aOf G t A (f₁ • X₁ + f₂ • X₂) C x = f₁ x * aOf G t A X₁ C x + f₂ x * aOf G t A X₂ C x := by
  have hcomb : SmE I M (f₁ • X₁ + f₂ • X₂) :=
    (ContMDiff.smul_section hf₁ hX₁).add_section (ContMDiff.smul_section hf₂ hX₂)
  have hpt : (f₁ • X₁ + f₂ • X₂) x = f₁ x • X₁ x + f₂ x • X₂ x := rfl
  rw [aOf_eq_difference_inner (I := I) (M := M) G t A (f₁ • X₁ + f₂ • X₂) C x hcomb,
    aOf_eq_difference_inner (I := I) (M := M) G t A X₁ C x hX₁,
    aOf_eq_difference_inner (I := I) (M := M) G t A X₂ C x hX₂]
  simp only [hpt, add_apply, smul_apply, map_add, map_smul, smul_eq_mul]

theorem aOf_lin_res (G : ℝ → SMet I M) (t : ℝ)
    (A B : TF (I := I) (M := M)) (X₁ X₂ : TF (I := I) (M := M)) (f₁ f₂ : M → ℝ) (x : M) :
    aOf G t A B (f₁ • X₁ + f₂ • X₂) x = f₁ x * aOf G t A B X₁ x + f₂ x * aOf G t A B X₂ x := by
  have hpt : (f₁ • X₁ + f₂ • X₂) x = f₁ x • X₁ x + f₂ x • X₂ x := rfl
  simp only [Work.Diff.EXT.aOf, hpt, add_apply, smul_apply, map_add, map_smul, smul_eq_mul]

theorem aOf_smF_M (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → SMet I M) (t : ℝ)
    (A B C : TF (I := I) (M := M)) (hA : SmE I M A) (hB : SmE I M B) (hC : SmE I M C) :
    SmF I M (fun y : M => aOf G t A B C y) := by
  have hU : SmE I M ((fun y : M => (lcOf (G t)) B y (A y))
      - (fun y : M => (lcOf (G 0)) B y (A y))) :=
    (lcOf_apply_smE hLC (G t) B A hB hA).sub_section (lcOf_apply_smE hLC (G 0) B A hB hA)
  have hfun : (fun y : M => aOf G t A B C y)
      = fun y : M => (G t).inner y
          (((fun y : M => (lcOf (G t)) B y (A y))
            - (fun y : M => (lcOf (G 0)) B y (A y))) y) (C y) := by
    funext y
    simp only [Work.Diff.EXT.aOf, Pi.sub_apply]
  rw [hfun]
  exact Work.Diff.GE.katoMetricPairingSmooth (G t) hU hC

theorem slotAdd_aOf_M (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → SMet I M) (t : ℝ) :
    SlotAdd (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) ∧
      ∀ (v : Fin 0 → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)), SmE I M A → SmE I M B → SmE I M C →
        SmF I M (aOf G t A B C) := by
  refine ⟨⟨fun i => i.elim0, ?_, ?_, ?_⟩, ?_⟩
  · intro v A A' B C _ _ _ _ _
    exact aOf_add_dir (I := I) (M := M) G t A A' B C
  · intro v A B B' C _ _ hB hB' _
    exact aOf_add_sec (I := I) (M := M) G t A B B' C hB hB'
  · intro v A B C C' _ _ _ _ _
    exact aOf_add_res (I := I) (M := M) G t A B C C'
  · intro v A B C hA hB hC
    exact aOf_smF_M (I := I) (M := M) hLC G t A B C hA hB hC

theorem aOfTower_valDep (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → SMet I M) (t : ℝ) :
    ∀ (c : ℕ) (v v' : Fin c → TF (I := I) (M := M)) (A A' B B' C C' : TF (I := I) (M := M)) (x : M),
      (∀ j, SmE I M (v j)) → (∀ j, SmE I M (v' j)) → (∀ j, v j x = v' j x) →
      SmE I M A → SmE I M A' → SmE I M B → SmE I M B' → SmE I M C → SmE I M C' →
      A x = A' x → B x = B' x → C x = C' x →
      tower (lcOf (G t)) (fun _ => aOf G t) c v A B C x
        = tower (lcOf (G t)) (fun _ => aOf G t) c v' A' B' C' x := by
  intro c
  have hbase := slotAdd_aOf_M (I := I) (M := M) hLC G t
  exact (towerSlotAddSmValDep (I := I) (M := M) hLC (G t)
    (base := fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) hbase.1 hbase.2
    (fun b0 A A' B B' C C' x _ _ hB hB' _ _ hAA hBB hCC =>
      aOf_valDep (I := I) (M := M) G t A A' B B' C C' x hB hB' hAA hBB hCC)
    (fun b0 X₁ X₂ f₁ f₂ _ _ _ _ B C x =>
      aOf_lin_dir (I := I) (M := M) G t X₁ X₂ f₁ f₂ B C x)
    (fun b0 X₁ X₂ f₁ f₂ hf₁ hf₂ hX₁ hX₂ A C x =>
      aOf_lin_sec (I := I) (M := M) G t A X₁ X₂ f₁ f₂ C x hf₁ hf₂ hX₁ hX₂)
    (fun b0 X₁ X₂ f₁ f₂ _ _ _ _ A B x =>
      aOf_lin_res (I := I) (M := M) G t A B X₁ X₂ f₁ f₂ x) c).2.2

theorem deltaTowerM_bndV
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (k : ℕ) (Bm : ℕ → ℝ) (hBm : ∀ j, 0 ≤ Bm j)
    (hAm : ∀ j, j < k → Work.Diff.EXT.ATower.ValBound G t j
      (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G t))
        (fun _ => Work.Diff.EXT.aOf G t) j) (Bm j)) :
    ∀ c, c < k → Work.Diff.EXT.ConnCov.AMB.BndV (I := I) (M := M) G t
      (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t c) (Bm c) := by
  intro c hc v X Z hv hX hZ x
  -- the moving `aOf`-tower bound at level `c`, and the value dependence of that tower
  have hVb : ValBound G t c (tower (lcOf (G t)) (fun _ => aOf G t) c) (Bm c) := hAm c hc
  have hdep := aOfTower_valDep (I := I) (M := M) hLC G t c
  -- the value of the `δ`-tower
  let w : TangentSpace I x := deltaTowerM G t c v X Z x
  -- the canonical smooth extension of `w`
  have hex : SmE I M (Submission.Diff.smoothExt x w) := Work.Diff.GE.smoothExt_cmdiff x w
  have hex_apply : Submission.Diff.smoothExt x w x = w := Work.Diff.GE.smoothExt_apply x w
  -- the tower value on the canonical tuple is the metric pairing of `w` with itself
  have hkey : (G t).inner x w w
      = valOp (tower (lcOf (G t)) (fun _ => aOf G t) c) x (fun i => v i x) (Z x) (X x) w := by
    simp only [Work.Diff.EXT.ATower.valOp]
    rw [hdep (fun j : Fin c => Submission.Diff.smoothExt x (v j x)) v
        (Submission.Diff.smoothExt x (Z x)) Z (Submission.Diff.smoothExt x (X x)) X
        (Submission.Diff.smoothExt x w) (Submission.Diff.smoothExt x w) x
        (fun j => Work.Diff.GE.smoothExt_cmdiff x (v j x)) hv
        (fun j => Work.Diff.GE.smoothExt_apply x (v j x))
        (Work.Diff.GE.smoothExt_cmdiff x (Z x)) hZ
        (Work.Diff.GE.smoothExt_cmdiff x (X x)) hX hex hex
        (Work.Diff.GE.smoothExt_apply x (Z x)) (Work.Diff.GE.smoothExt_apply x (X x))
        (by rfl)]
    rw [towerEqLoweringDeltaTowerM (I := I) (M := M) hLC G t c v Z X
      (Submission.Diff.smoothExt x w) hv hZ hX hex x, hex_apply]
  -- the pointwise bound from `ValBound`
  have hb := hVb x (fun i => v i x) (Z x) (X x) w
  rw [← hkey] at hb
  have hinn : 0 ≤ (G t).inner x w w := inner_self_nonneg_M (G t) x w
  rw [abs_of_nonneg hinn] at hb
  -- nonnegativity of the factors
  have hC0 : 0 ≤ Bm c := hBm c
  have hP0 : 0 ≤ ∏ i : Fin c, Real.sqrt ((G t).inner x (v i x) (v i x)) :=
    Finset.prod_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hZ0 : 0 ≤ Real.sqrt ((G t).inner x (Z x) (Z x)) := Real.sqrt_nonneg _
  have hX0 : 0 ≤ Real.sqrt ((G t).inner x (X x) (X x)) := Real.sqrt_nonneg _
  have hN0 : 0 ≤ Bm c * (∏ i : Fin c, Real.sqrt ((G t).inner x (v i x) (v i x)))
      * Real.sqrt ((G t).inner x (Z x) (Z x)) * Real.sqrt ((G t).inner x (X x) (X x)) := by
    have h := mul_nonneg (mul_nonneg (mul_nonneg hC0 hP0) hZ0) hX0
    linarith [h]
  -- the pairing bound gives `‖w‖ ≤ Bm c · ∏ ‖v i x‖ · ‖Z x‖ · ‖X x‖`
  have hs_le : Real.sqrt ((G t).inner x w w)
      ≤ Bm c * (∏ i : Fin c, Real.sqrt ((G t).inner x (v i x) (v i x)))
        * Real.sqrt ((G t).inner x (Z x) (Z x)) * Real.sqrt ((G t).inner x (X x) (X x)) := by
    rcases eq_or_lt_of_le (Real.sqrt_nonneg ((G t).inner x w w)) with h0 | hpos
    · rw [← h0]
      exact hN0
    · refine le_of_mul_le_mul_right ?_ hpos
      rw [Real.mul_self_sqrt hinn]
      exact hb
  -- the elementary product comparison
  have hPle : (∏ i : Fin c, Real.sqrt ((G t).inner x (v i x) (v i x)))
      ≤ ∏ i : Fin c, (1 + Real.sqrt ((G t).inner x (v i x) (v i x))) := by
    refine Finset.prod_le_prod₀ (fun i _ => Real.sqrt_nonneg _) (fun i _ => ?_)
    linarith [Real.sqrt_nonneg ((G t).inner x (v i x) (v i x))]
  have hZle : Real.sqrt ((G t).inner x (Z x) (Z x))
      ≤ 1 + Real.sqrt ((G t).inner x (Z x) (Z x)) := by
    linarith [Real.sqrt_nonneg ((G t).inner x (Z x) (Z x))]
  have hXle : Real.sqrt ((G t).inner x (X x) (X x))
      ≤ 1 + Real.sqrt ((G t).inner x (X x) (X x)) := by
    linarith [Real.sqrt_nonneg ((G t).inner x (X x) (X x))]
  have hP10 : 0 ≤ ∏ i : Fin c, (1 + Real.sqrt ((G t).inner x (v i x) (v i x))) :=
    Finset.prod_nonneg (fun i _ => by
      linarith [Real.sqrt_nonneg ((G t).inner x (v i x) (v i x))])
  have hQX0 : 0 ≤ 1 + Real.sqrt ((G t).inner x (X x) (X x)) := by
    linarith [Real.sqrt_nonneg ((G t).inner x (X x) (X x))]
  have hQZ0 : 0 ≤ 1 + Real.sqrt ((G t).inner x (Z x) (Z x)) := by
    linarith [Real.sqrt_nonneg ((G t).inner x (Z x) (Z x))]
  have hfinal : Bm c * (∏ i : Fin c, Real.sqrt ((G t).inner x (v i x) (v i x)))
        * Real.sqrt ((G t).inner x (Z x) (Z x)) * Real.sqrt ((G t).inner x (X x) (X x))
      ≤ Bm c * (∏ i : Fin c, (1 + Real.sqrt ((G t).inner x (v i x) (v i x))))
        * (1 + Real.sqrt ((G t).inner x (X x) (X x)))
        * (1 + Real.sqrt ((G t).inner x (Z x) (Z x))) := by
    have hA : Bm c * (∏ i : Fin c, Real.sqrt ((G t).inner x (v i x) (v i x)))
          * Real.sqrt ((G t).inner x (X x) (X x)) * Real.sqrt ((G t).inner x (Z x) (Z x))
        ≤ Bm c * (∏ i : Fin c, (1 + Real.sqrt ((G t).inner x (v i x) (v i x))))
          * Real.sqrt ((G t).inner x (X x) (X x)) * Real.sqrt ((G t).inner x (Z x) (Z x)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPle hC0) hX0) hZ0
    have hB : Bm c * (∏ i : Fin c, (1 + Real.sqrt ((G t).inner x (v i x) (v i x))))
          * Real.sqrt ((G t).inner x (X x) (X x)) * Real.sqrt ((G t).inner x (Z x) (Z x))
        ≤ Bm c * (∏ i : Fin c, (1 + Real.sqrt ((G t).inner x (v i x) (v i x))))
          * (1 + Real.sqrt ((G t).inner x (X x) (X x))) * Real.sqrt ((G t).inner x (Z x) (Z x)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hXle (mul_nonneg hC0 hP10)) hZ0
    have hD : Bm c * (∏ i : Fin c, (1 + Real.sqrt ((G t).inner x (v i x) (v i x))))
          * (1 + Real.sqrt ((G t).inner x (X x) (X x))) * Real.sqrt ((G t).inner x (Z x) (Z x))
        ≤ Bm c * (∏ i : Fin c, (1 + Real.sqrt ((G t).inner x (v i x) (v i x))))
          * (1 + Real.sqrt ((G t).inner x (X x) (X x)))
          * (1 + Real.sqrt ((G t).inner x (Z x) (Z x))) :=
      mul_le_mul_of_nonneg_left hZle (mul_nonneg (mul_nonneg hC0 hP10) hQX0)
    calc Bm c * (∏ i : Fin c, Real.sqrt ((G t).inner x (v i x) (v i x)))
          * Real.sqrt ((G t).inner x (Z x) (Z x)) * Real.sqrt ((G t).inner x (X x) (X x))
        = Bm c * (∏ i : Fin c, Real.sqrt ((G t).inner x (v i x) (v i x)))
          * Real.sqrt ((G t).inner x (X x) (X x)) * Real.sqrt ((G t).inner x (Z x) (Z x)) := by
          ring
      _ ≤ Bm c * (∏ i : Fin c, (1 + Real.sqrt ((G t).inner x (v i x) (v i x))))
          * Real.sqrt ((G t).inner x (X x) (X x)) * Real.sqrt ((G t).inner x (Z x) (Z x)) := hA
      _ ≤ Bm c * (∏ i : Fin c, (1 + Real.sqrt ((G t).inner x (v i x) (v i x))))
          * (1 + Real.sqrt ((G t).inner x (X x) (X x))) * Real.sqrt ((G t).inner x (Z x) (Z x)) :=
          hB
      _ ≤ Bm c * (∏ i : Fin c, (1 + Real.sqrt ((G t).inner x (v i x) (v i x))))
          * (1 + Real.sqrt ((G t).inner x (X x) (X x)))
          * (1 + Real.sqrt ((G t).inner x (Z x) (Z x))) := hD
  exact le_trans hs_le hfinal


end RicFlip

end Work.Diff.EXT.ConnCov
