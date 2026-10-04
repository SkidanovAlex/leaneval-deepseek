import Mathlib
import Submission.Work.Diff.EXT.ATower.Defs
import Submission.Work.Diff.EXT.ATower.tower_value_defs
import Submission.Work.Diff.EXT.ATower.tvd_germs_step
import Submission.Work.Diff.EXT.ATower.value_dep_of_germs_lin
import Submission.Work.Diff.EXT.ATower.connDiff_flip_input
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Value-dependence of the connection-difference tower

`Work.Diff.EXT.ATower.tower cov base k` is the `k`-th iterated covariant derivative of the base
operator `base`; `Work.Diff.EXT.ATower.tvdP g base k` is the same object with the `k+3` slots packed
into one `Fin (k+3)`-tuple (see `tower_value_defs.lean`).

This file proves `tower_value_dep`: for a base operator which is smooth, value-dependent and
`C^∞`-linear in its three value slots (hypotheses `hsm`, `hvd`, `hlinA/B/C`), the tower is
*value-dependent*: its value at `x` depends only on the values at `x` of the `k+3` slot fields.

The proof is the following chain (the invariants are stated in `tower_value_defs.lean`):

* `tvdSmT_zero`, `tvdLinT_zero`, `tvdGermTs_zero`: the base cases `k = 0`, from `hsm`, `hlinA/B/C`
  and `hvd` (`tvd_lin_sum` converts the two-term linearity of the hypotheses into the finite-sum
  form used by the tower);
* `tvd_sm_lin_step` and `tvd_germs_step` (proved in the sibling files): the induction steps for
  smoothness + slotwise `C^∞`-linearity, and for germ-locality on smooth tuples;
* `tvdStepP_eq_step`, `tvdP_eq_tvdTp`: one recursion step of the packed recursion `tvdP` is the
  unpacked `step`, so that `tvdP` is the frozen `tower`;
* `value_dep_of_germs_lin` (proved in a sibling file): germ-locality on smooth tuples together with
  slotwise `C^∞`-linearity implies value-dependence (frame decomposition + additivity chain).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## The finite-sum form of slotwise linearity, and the base case `k = 0` -/

/-- The finite-sum form of `C^∞`-linearity for a one-slot functional, from the two-term form
(exactly the shape of `hlinA`/`hlinB`/`hlinC`). -/
theorem tvd_lin_sum {Ψ : TF (I := I) (M := M) → M → ℝ}
    (hΨ : ∀ (f₁ f₂ : M → ℝ) (X₁ X₂ : TF (I := I) (M := M)), SmF I M f₁ → SmF I M f₂ →
      SmE I M X₁ → SmE I M X₂ → ∀ y, Ψ (f₁ • X₁ + f₂ • X₂) y = f₁ y * Ψ X₁ y + f₂ y * Ψ X₂ y)
    {ι : Type*} [Fintype ι] (X : ι → TF (I := I) (M := M)) (f : ι → M → ℝ)
    (S : TF (I := I) (M := M))
    (hX : ∀ q, SmE I M (X q)) (hf : ∀ q, SmF I M (f q)) (hS : SmE I M S)
    (hrep : ∀ y, S y = ∑ q, f q y • X q y) :
    ∀ y, Ψ S y = ∑ q, f q y * Ψ (X q) y := by
  classical
  have hadd : ∀ (X₁ X₂ : TF (I := I) (M := M)), SmE I M X₁ → SmE I M X₂ → ∀ y,
      Ψ (X₁ + X₂) y = Ψ X₁ y + Ψ X₂ y := by
    intro X₁ X₂ h₁ h₂ y
    have h := hΨ (fun _ : M => (1 : ℝ)) (fun _ : M => (1 : ℝ)) X₁ X₂
      contMDiff_const contMDiff_const h₁ h₂ y
    rw [show ((fun _ : M => (1 : ℝ)) • X₁ + (fun _ : M => (1 : ℝ)) • X₂) = (X₁ + X₂) from by
      funext y'; simp] at h
    simpa using h
  have hsmul : ∀ (f₀ : M → ℝ) (X₀ : TF (I := I) (M := M)), SmF I M f₀ → SmE I M X₀ → ∀ y,
      Ψ (f₀ • X₀) y = f₀ y * Ψ X₀ y := by
    intro f₀ X₀ hf₀ hX₀ y
    have h := hΨ f₀ (fun _ : M => (0 : ℝ)) X₀ X₀ hf₀ contMDiff_const hX₀ hX₀ y
    rw [show (f₀ • X₀ + (fun _ : M => (0 : ℝ)) • X₀) = (f₀ • X₀) from by funext y'; simp] at h
    simpa using h
  have key : ∀ s : Finset ι, ∀ (T : TF (I := I) (M := M)), SmE I M T →
      (∀ y, T y = ∑ q ∈ s, f q y • X q y) → ∀ y, Ψ T y = ∑ q ∈ s, f q y * Ψ (X q) y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro T hT hrepT y
        have h0 : T = (fun _ : M => (0 : ℝ)) • T := by funext y'; rw [hrepT y']; simp
        rw [h0, hsmul (fun _ : M => (0 : ℝ)) T contMDiff_const hT y]
        simp
    | insert q s hq ih =>
        intro T hT hrepT y
        have htail : SmE I M (fun y' : M => ∑ q' ∈ s, f q' y' • X q' y') :=
          tvd_smE_sum s f X (fun q' _ => hf q') (fun q' _ => hX q')
        have hsplit : T = (f q • X q) + (fun y' : M => ∑ q' ∈ s, f q' y' • X q' y') := by
          funext y'
          rw [hrepT y', Finset.sum_insert hq, Pi.add_apply]
          rfl
        rw [hsplit, hadd (f q • X q) (fun y' : M => ∑ q' ∈ s, f q' y' • X q' y')
            (tvd_smE_smul (hf q) (hX q)) htail y,
          hsmul (f q) (X q) (hf q) (hX q) y,
          ih (fun y' : M => ∑ q' ∈ s, f q' y' • X q' y') htail (fun _ => rfl) y,
          Finset.sum_insert hq]
  exact key Finset.univ S hS (fun y => hrep y)

/-- Base case of the smoothness invariant. -/
theorem tvdSmT_zero (g : SMet I M) (base : Op3 (I := I) (M := M) 0)
    (hsm : ∀ (v : Fin 0 → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      SmE I M A → SmE I M B → SmE I M C → SmF I M (base v A B C)) :
    tvdSmT g base 0 := by
  intro F hF
  exact hsm _ _ _ _ (hF (Fin.natAdd 0 0)) (hF (Fin.natAdd 0 1)) (hF (Fin.natAdd 0 2))

/-- Base case of the slotwise `C^∞`-linearity invariant. -/
theorem tvdLinT_zero (g : SMet I M) (base : Op3 (I := I) (M := M) 0)
    (hlinA : ∀ (b0 : Fin 0 → TF (I := I) (M := M)) (X₁ X₂ : TF (I := I) (M := M)) (f₁ f₂ : M → ℝ),
      SmF I M f₁ → SmF I M f₂ → SmE I M X₁ → SmE I M X₂ → ∀ (B C : TF (I := I) (M := M)) (x : M),
      base b0 (f₁ • X₁ + f₂ • X₂) B C x = f₁ x * base b0 X₁ B C x + f₂ x * base b0 X₂ B C x)
    (hlinB : ∀ (b0 : Fin 0 → TF (I := I) (M := M)) (X₁ X₂ : TF (I := I) (M := M)) (f₁ f₂ : M → ℝ),
      SmF I M f₁ → SmF I M f₂ → SmE I M X₁ → SmE I M X₂ → ∀ (A C : TF (I := I) (M := M)) (x : M),
      base b0 A (f₁ • X₁ + f₂ • X₂) C x = f₁ x * base b0 A X₁ C x + f₂ x * base b0 A X₂ C x)
    (hlinC : ∀ (b0 : Fin 0 → TF (I := I) (M := M)) (X₁ X₂ : TF (I := I) (M := M)) (f₁ f₂ : M → ℝ),
      SmF I M f₁ → SmF I M f₂ → SmE I M X₁ → SmE I M X₂ → ∀ (A B : TF (I := I) (M := M)) (x : M),
      base b0 A B (f₁ • X₁ + f₂ • X₂) x = f₁ x * base b0 A B X₁ x + f₂ x * base b0 A B X₂ x) :
    tvdLinT g base 0 := by
  intro F j ι _ X f S hF hX hf hS hrep y
  fin_cases j
  · exact tvd_lin_sum (Ψ := fun W => base (fun i : Fin 0 => i.elim0) W (F 1) (F 2))
      (fun f₁ f₂ X₁ X₂ h₁ h₂ hX₁ hX₂ y' => hlinA _ X₁ X₂ f₁ f₂ h₁ h₂ hX₁ hX₂ (F 1) (F 2) y')
      X f S hX hf hS hrep y
  · exact tvd_lin_sum (Ψ := fun W => base (fun i : Fin 0 => i.elim0) (F 0) W (F 2))
      (fun f₁ f₂ X₁ X₂ h₁ h₂ hX₁ hX₂ y' => hlinB _ X₁ X₂ f₁ f₂ h₁ h₂ hX₁ hX₂ (F 0) (F 2) y')
      X f S hX hf hS hrep y
  · exact tvd_lin_sum (Ψ := fun W => base (fun i : Fin 0 => i.elim0) (F 0) (F 1) W)
      (fun f₁ f₂ X₁ X₂ h₁ h₂ hX₁ hX₂ y' => hlinC _ X₁ X₂ f₁ f₂ h₁ h₂ hX₁ hX₂ (F 0) (F 1) y')
      X f S hX hf hS hrep y

/-- Base case of germ-locality (on smooth tuples), from value-dependence of `base`. -/
theorem tvdGermTs_zero (g : SMet I M) (base : Op3 (I := I) (M := M) 0)
    (hvd : ∀ (b0 : Fin 0 → TF (I := I) (M := M))
      (A A' B B' C C' : TF (I := I) (M := M)) (x : M),
      SmE I M A → SmE I M A' → SmE I M B → SmE I M B' → SmE I M C → SmE I M C' →
      A x = A' x → B x = B' x → C x = C' x → base b0 A B C x = base b0 A' B' C' x) :
    tvdGermTs g base 0 := by
  intro F F' x hF hF' h
  exact hvd _ _ _ _ _ _ _ x (hF _) (hF' _) (hF _) (hF' _) (hF _) (hF' _)
    (h _).eq_of_nhds (h _).eq_of_nhds (h _).eq_of_nhds

/-! ## The induction step: smoothness and slotwise linearity

The two ingredients of the induction step (`tvd_sm_lin_step`) are proved here directly (the sibling
file `tvd_sm_lin_step.lean` states the same induction step): smoothness follows from the smoothness
of the previous level together with `mvfderiv_apply_contMDiff` and the smoothness of
`y ↦ lcOf g Y y (Z y)`; slotwise linearity is the Leibniz cancellation, isolated in the two lemmas
`tvdStepP_dir_lin` (the differentiation slot) and `tvdStepP_slot_lin` (a `τ`-slot). -/

/-- Sum algebra: moving a sum inside a subtraction (the direction-slot case). -/
theorem tvd_sum_mul_sub {ι κ : Type*} [Fintype ι] (s : Finset κ) (a : ι → ℝ) (A : ι → ℝ)
    (D : ι → κ → ℝ) :
    (∑ q, a q * A q) - (∑ q, ∑ j ∈ s, a q * D q j) = ∑ q, a q * (A q - ∑ j ∈ s, D q j) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [mul_sub, Finset.mul_sum]

/-- Sum algebra: the variant with an extra `Z`-term (the Leibniz cancellation in a `τ`-slot). -/
theorem tvd_sum_lin_sub {ι κ : Type*} [Fintype ι] (s : Finset κ) (a : ι → ℝ) (A Z : ι → ℝ)
    (D : ι → κ → ℝ) :
    (∑ q, a q * A q) - (∑ q, a q * Z q) - (∑ q, ∑ j ∈ s, a q * D q j)
      = ∑ q, a q * (A q - (Z q + ∑ j ∈ s, D q j)) := by
  have h1 : (∑ q, ∑ j ∈ s, a q * D q j) = ∑ q, a q * ∑ j ∈ s, D q j := by
    refine Finset.sum_congr rfl (fun q _ => ?_); rw [Finset.mul_sum]
  rw [h1, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  ring

/-- **Linearity in the differentiation slot** (packed recursion step). -/
theorem tvdStepP_dir_lin (g : SMet I M) (hLC : Submission.Diff.LCSmooth I M) {k : ℕ}
    (τ : (Fin (k + 3) → TF (I := I) (M := M)) → M → ℝ)
    (hτlin : ∀ (W : Fin (k + 3) → TF (I := I) (M := M)) (ia : Fin (k + 3)) {ι : Type} [Fintype ι]
      (X : ι → TF (I := I) (M := M)) (f : ι → M → ℝ) (S : TF (I := I) (M := M)),
      (∀ j, SmE I M (W j)) → (∀ q, SmE I M (X q)) → (∀ q, SmF I M (f q)) → SmE I M S →
      (∀ z, S z = ∑ q, f q z • X q z) →
      ∀ y, τ (Function.update W ia S) y = ∑ q, f q y * τ (Function.update W ia (X q)) y)
    (G : Fin (k + 3) → TF (I := I) (M := M)) (hG : ∀ j, SmE I M (G j))
    {ι : Type} [Fintype ι] (X : ι → TF (I := I) (M := M)) (f : ι → M → ℝ)
    (S : TF (I := I) (M := M)) (hX : ∀ q, SmE I M (X q)) (hf : ∀ q, SmF I M (f q))
    (hS : SmE I M S) (hrep : ∀ z, S z = ∑ q, f q z • X q z) (y : M) :
    mvfderiv I (τ G) y (S y)
        - ∑ j'' : Fin (k + 3), τ (Function.update G j''
            (fun z => lcOf g (G j'') z (S z))) y
      = ∑ q, f q y * (mvfderiv I (τ G) y (X q y)
        - ∑ j'' : Fin (k + 3), τ (Function.update G j''
            (fun z => lcOf g (G j'') z (X q z))) y) := by
  have h1 : mvfderiv I (τ G) y (S y) = ∑ q, f q y * mvfderiv I (τ G) y (X q y) := by
    rw [hrep y, tvd_mvfderiv_dir_sum]
  have h2 : ∀ j'' : Fin (k + 3),
      τ (Function.update G j'' (fun z => lcOf g (G j'') z (S z))) y
        = ∑ q, f q y * τ (Function.update G j'' (fun z => lcOf g (G j'') z (X q z))) y := by
    intro j''
    refine hτlin G j'' (fun q => fun z => lcOf g (G j'') z (X q z)) f
      (fun z => lcOf g (G j'') z (S z)) hG ?_ hf ?_ ?_ y
    · intro q; exact lcOf_apply_smE hLC g (G j'') (X q) (hG j'') (hX q)
    · exact lcOf_apply_smE hLC g (G j'') S (hG j'') hS
    · intro z
      rw [hrep z, map_sum]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [map_smul]
  rw [h1]
  simp only [h2]
  rw [Finset.sum_comm]
  exact tvd_sum_mul_sub Finset.univ (fun q => f q y) (fun q => mvfderiv I (τ G) y (X q y))
    (fun q j'' => τ (Function.update G j'' (fun z => lcOf g (G j'') z (X q z))) y)

/-- **Linearity in a `τ`-slot** (packed recursion step): the Leibniz terms produced by
differentiating `τ` cancel against the connection correction in the same slot. -/
theorem tvdStepP_slot_lin (g : SMet I M) (hLC : Submission.Diff.LCSmooth I M) {k : ℕ}
    (τ : (Fin (k + 3) → TF (I := I) (M := M)) → M → ℝ)
    (hτsm : ∀ (W : Fin (k + 3) → TF (I := I) (M := M)), (∀ j, SmE I M (W j)) → SmF I M (τ W))
    (hτlin : ∀ (W : Fin (k + 3) → TF (I := I) (M := M)) (ia : Fin (k + 3)) {ι : Type} [Fintype ι]
      (X : ι → TF (I := I) (M := M)) (f : ι → M → ℝ) (S : TF (I := I) (M := M)),
      (∀ j, SmE I M (W j)) → (∀ q, SmE I M (X q)) → (∀ q, SmF I M (f q)) → SmE I M S →
      (∀ z, S z = ∑ q, f q z • X q z) →
      ∀ y, τ (Function.update W ia S) y = ∑ q, f q y * τ (Function.update W ia (X q)) y)
    (G : Fin (k + 3) → TF (I := I) (M := M)) (i : Fin (k + 3)) (F0 : TF (I := I) (M := M))
    (hG : ∀ j, SmE I M (G j)) (hF0 : SmE I M F0)
    {ι : Type} [Fintype ι] (X : ι → TF (I := I) (M := M)) (f : ι → M → ℝ)
    (S : TF (I := I) (M := M)) (hX : ∀ q, SmE I M (X q)) (hf : ∀ q, SmF I M (f q))
    (hS : SmE I M S) (hrep : ∀ z, S z = ∑ q, f q z • X q z) (y : M) :
    mvfderiv I (τ (Function.update G i S)) y (F0 y)
        - ∑ j'' : Fin (k + 3), τ (Function.update (Function.update G i S) j''
            (fun z => lcOf g ((Function.update G i S) j'') z (F0 z))) y
      = ∑ q, f q y * (mvfderiv I (τ (Function.update G i (X q))) y (F0 y)
        - ∑ j'' : Fin (k + 3), τ (Function.update (Function.update G i (X q)) j''
            (fun z => lcOf g ((Function.update G i (X q)) j'') z (F0 z))) y) := by
  have hupdsm : ∀ (W : TF (I := I) (M := M)), SmE I M W → ∀ j' : Fin (k + 3),
      SmE I M (Function.update G i W j') := by
    intro W hW j'
    by_cases h : j' = i
    · subst h; rw [Function.update_self]; exact hW
    · rw [Function.update_of_ne h]; exact hG j'
  have hsmG : ∀ (W : TF (I := I) (M := M)), SmE I M W →
      SmF I M (τ (Function.update G i W)) := by
    intro W hW
    exact hτsm _ (hupdsm W hW)
  -- (1) linearity of `τ` in slot `i`
  have hLinS : τ (Function.update G i S)
      = fun y' : M => ∑ q, f q y' * τ (Function.update G i (X q)) y' :=
    funext (fun y' => hτlin G i X f S hG hX hf hS hrep y')
  -- (2) the Leibniz expansion of the derivative term
  have hmvf : mvfderiv I (τ (Function.update G i S)) y (F0 y)
      = ∑ q, (f q y * mvfderiv I (τ (Function.update G i (X q))) y (F0 y)
          + mvfderiv I (f q) y (F0 y) * τ (Function.update G i (X q)) y) := by
    rw [hLinS]
    rw [tvd_mvfderiv_sum Finset.univ (fun q y' => f q y' * τ (Function.update G i (X q)) y')
      (fun q _ => ((hf q).mdifferentiableAt (by simp)).mul
        ((hsmG (X q) (hX q)).mdifferentiableAt (by simp)))]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [tvd_mvfderiv_mul ((hf q).mdifferentiableAt (by simp))
      ((hsmG (X q) (hX q)).mdifferentiableAt (by simp))]
  -- (3) the correction term at `j'' = i`
  have hterm_i : τ (Function.update (Function.update G i S) i
        (fun z => lcOf g ((Function.update G i S) i) z (F0 z))) y
      = (∑ q, f q y * τ (Function.update G i (fun z => lcOf g (X q) z (F0 z))) y)
        + ∑ q, mvfderiv I (f q) y (F0 y) * τ (Function.update G i (X q)) y := by
    have hcollapse : Function.update (Function.update G i S) i
        (fun z => lcOf g ((Function.update G i S) i) z (F0 z))
        = Function.update G i (fun z => lcOf g S z (F0 z)) := by
      rw [Function.update_self, Function.update_idem]
    rw [hcollapse]
    rw [hτlin G i (Sum.elim (fun q => fun z => lcOf g (X q) z (F0 z)) X)
      (Sum.elim f (fun q z => mvfderiv I (f q) z (F0 z)))
      (fun z => lcOf g S z (F0 z)) hG ?_ ?_ ?_ ?_ y]
    · rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
    · intro p; cases p with
      | inl q => exact lcOf_apply_smE hLC g (X q) F0 (hX q) hF0
      | inr q => exact hX q
    · intro p; cases p with
      | inl q => exact hf q
      | inr q =>
          exact Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff (hf q) hF0
    · exact lcOf_apply_smE hLC g S F0 hS hF0
    · intro z
      have hSfun : S = (fun z' : M => ∑ q, f q z' • X q z') := funext hrep
      rw [hSfun, Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [tvd_cov_sum (lcOf g) Finset.univ f X
        (fun q _ => (hX q).mdifferentiableAt (by simp))
        (fun q _ => (hf q).mdifferentiableAt (by simp)), _root_.sum_apply]
      exact (Finset.sum_congr rfl (fun q _ =>
        tvd_cov_leibniz_app (lcOf g) ((hX q).mdifferentiableAt (by simp))
          ((hf q).mdifferentiableAt (by simp)))).trans Finset.sum_add_distrib
  -- (4) the correction terms at `j'' ≠ i`
  have hterm_ne : ∀ j'' : Fin (k + 3), j'' ≠ i →
      τ (Function.update (Function.update G i S) j''
          (fun z => lcOf g ((Function.update G i S) j'') z (F0 z))) y
        = ∑ q, f q y * τ (Function.update (Function.update G i (X q)) j''
          (fun z => lcOf g ((Function.update G i (X q)) j'') z (F0 z))) y := by
    intro j'' hj
    have hcomm : Function.update (Function.update G i S) j''
          (fun z => lcOf g ((Function.update G i S) j'') z (F0 z))
        = Function.update (Function.update G j'' (fun z => lcOf g (G j'') z (F0 z))) i S := by
      rw [Function.update_comm (Ne.symm hj)]
      have hins : (fun z => lcOf g ((Function.update G i S) j'') z (F0 z))
          = (fun z => lcOf g (G j'') z (F0 z)) := by
        funext z; rw [Function.update_of_ne hj]
      rw [hins]
    have hcomm' : ∀ q, Function.update (Function.update G i (X q)) j''
          (fun z => lcOf g ((Function.update G i (X q)) j'') z (F0 z))
        = Function.update (Function.update G j'' (fun z => lcOf g (G j'') z (F0 z))) i (X q) := by
      intro q
      rw [Function.update_comm (Ne.symm hj)]
      have hins : (fun z => lcOf g ((Function.update G i (X q)) j'') z (F0 z))
          = (fun z => lcOf g (G j'') z (F0 z)) := by
        funext z; rw [Function.update_of_ne hj]
      rw [hins]
    rw [hcomm]
    simp only [hcomm']
    have hsmr : ∀ j' : Fin (k + 3),
        SmE I M (Function.update G j'' (fun z => lcOf g (G j'') z (F0 z)) j') := by
      intro j'
      by_cases h : j' = j''
      · rw [← h, Function.update_self]
        exact lcOf_apply_smE hLC g (G j') F0 (hG j') hF0
      · rw [Function.update_of_ne h]; exact hG j'
    exact hτlin (Function.update G j'' (fun z => lcOf g (G j'') z (F0 z))) i X f S
      hsmr hX hf hS hrep y
  -- (5) assemble
  have hsplitS : (∑ j'' : Fin (k + 3), τ (Function.update (Function.update G i S) j''
        (fun z => lcOf g ((Function.update G i S) j'') z (F0 z))) y)
      = τ (Function.update (Function.update G i S) i
          (fun z => lcOf g ((Function.update G i S) i) z (F0 z))) y
        + ∑ j'' ∈ Finset.univ.erase i, τ (Function.update (Function.update G i S) j''
            (fun z => lcOf g ((Function.update G i S) j'') z (F0 z))) y := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  have herase : (∑ j'' ∈ Finset.univ.erase i, τ (Function.update (Function.update G i S) j''
        (fun z => lcOf g ((Function.update G i S) j'') z (F0 z))) y)
      = ∑ j'' ∈ Finset.univ.erase i, ∑ q, f q y * τ (Function.update (Function.update G i (X q)) j''
          (fun z => lcOf g ((Function.update G i (X q)) j'') z (F0 z))) y := by
    refine Finset.sum_congr rfl (fun j'' hj => ?_)
    exact hterm_ne j'' (Finset.mem_erase.mp hj).1
  have hsplitX : ∀ q : ι, (∑ j'' : Fin (k + 3), τ (Function.update (Function.update G i (X q)) j''
        (fun z => lcOf g ((Function.update G i (X q)) j'') z (F0 z))) y)
      = τ (Function.update (Function.update G i (X q)) i
          (fun z => lcOf g ((Function.update G i (X q)) i) z (F0 z))) y
        + ∑ j'' ∈ Finset.univ.erase i, τ (Function.update (Function.update G i (X q)) j''
            (fun z => lcOf g ((Function.update G i (X q)) j'') z (F0 z))) y := by
    intro q
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  have hTi : ∀ q : ι, τ (Function.update (Function.update G i (X q)) i
        (fun z => lcOf g ((Function.update G i (X q)) i) z (F0 z))) y
      = τ (Function.update G i (fun z => lcOf g (X q) z (F0 z))) y := by
    intro q
    rw [Function.update_self, Function.update_idem]
  rw [hmvf, hsplitS, hterm_i, herase]
  simp only [hsplitX, hTi]
  refine Eq.trans ?_ (tvd_sum_lin_sub (Finset.univ.erase i) (fun q => f q y)
    (fun q => mvfderiv I (τ (Function.update G i (X q))) y (F0 y))
    (fun q => τ (Function.update G i (fun z => lcOf g (X q) z (F0 z))) y)
    (fun q j'' => τ (Function.update (Function.update G i (X q)) j''
      (fun z => lcOf g ((Function.update G i (X q)) j'') z (F0 z))) y))
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  ring

/-- **The induction step** for smoothness and slotwise `C^∞`-linearity. -/
theorem tvd_sm_lin_step_self (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M)
    (base : Op3 (I := I) (M := M) 0) (k : ℕ)
    (hS : tvdSmT g base k) (hL : tvdLinT g base k) :
    tvdSmT g base (k + 1) ∧ tvdLinT g base (k + 1) := by
  refine ⟨?_, ?_⟩
  · intro F hF
    change SmF I M (fun x : M =>
      mvfderiv I (tvdP g base k (fun j : Fin (k + 3) => F (Fin.succ j))) x (F 0 x)
        - ∑ j : Fin (k + 3), tvdP g base k (Function.update (fun j' : Fin (k + 3) => F (Fin.succ j')) j
            (fun y => lcOf g (F (Fin.succ j)) y (F 0 y))) x)
    refine ContMDiff.sub ?_ ?_
    · exact Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff
        (hS _ (fun j => hF (Fin.succ j))) (hF 0)
    · refine tvd_smF_sum Finset.univ
        (fun j : Fin (k + 3) => tvdP g base k (Function.update (fun j' : Fin (k + 3) => F (Fin.succ j')) j
          (fun y => lcOf g (F (Fin.succ j)) y (F 0 y)))) ?_
      intro j _
      refine hS _ ?_
      intro i
      by_cases h : i = j
      · subst h; rw [Function.update_self]
        exact lcOf_apply_smE hLC g (F (Fin.succ i)) (F 0) (hF _) (hF _)
      · rw [Function.update_of_ne h]; exact hF _
  · intro F j ι _ X f S hF hX hf hS' hrep
    rw [tvdP_succ]
    refine Fin.cases (motive := fun j => ∀ y, tvdStepP g (tvdP g base k) (Function.update F j S) y
        = ∑ q, f q y * tvdStepP g (tvdP g base k) (Function.update F j (X q)) y) ?_ ?_ j
    · intro y
      simp only [tvdStepP]
      have hsh0 : ∀ (W : TF (I := I) (M := M)) (j' : Fin (k + 3)),
          (Function.update F 0 W) (Fin.succ j')
            = (fun j'' : Fin (k + 3) => F (Fin.succ j'')) j' := by
        intro W j'; rw [Function.update_of_ne (Fin.succ_ne_zero j')]
      have hd0 : ∀ W : TF (I := I) (M := M), (Function.update F 0 W) 0 = W := by
        intro W; exact Function.update_self 0 W F
      simp only [hsh0, hd0]
      exact tvdStepP_dir_lin g hLC (tvdP g base k)
        (fun W ia {ι} _ X f S hW hX hf hS hrep y => hL W ia ι X f S hW hX hf hS hrep y)
        (fun j' : Fin (k + 3) => F (Fin.succ j')) (fun j' => hF (Fin.succ j')) X f S hX hf hS' hrep y
    · intro i y
      simp only [tvdStepP]
      have hsh : ∀ (W : TF (I := I) (M := M)) (j' : Fin (k + 3)),
          (Function.update F (Fin.succ i) W) (Fin.succ j')
            = Function.update (fun j'' : Fin (k + 3) => F (Fin.succ j'')) i W j' := by
        intro W j'
        by_cases h : j' = i
        · subst h; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne h,
            Function.update_of_ne (fun hh => h (Fin.succ_injective (k + 3) hh))]
      have hdir : ∀ (W : TF (I := I) (M := M)),
          (Function.update F (Fin.succ i) W) 0 = F 0 := by
        intro W; rw [Function.update_of_ne (Fin.succ_ne_zero i).symm]
      simp only [hsh, hdir]
      exact tvdStepP_slot_lin g hLC (tvdP g base k)
        (fun W hW => hS W hW)
        (fun W ia {ι} _ X f S hW hX hf hS hrep y => hL W ia ι X f S hW hX hf hS hrep y)
        (fun j' : Fin (k + 3) => F (Fin.succ j')) i (F 0) (fun j' => hF (Fin.succ j')) (hF 0)
        X f S hX hf hS' hrep y

/-! ## The packed recursion is the frozen tower -/

/-- **One recursion step, packed vs unpacked** (packed form). -/
theorem tvdStepP_eq_step_pack (g : SMet I M) {k : ℕ}
    (τ : (Fin (k + 3) → TF (I := I) (M := M)) → M → ℝ)
    (v : Fin (k + 1) → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)) :
    tvdStepP g τ (tvdPack v A B C)
      = step (lcOf g) (fun (v' : Fin k → TF (I := I) (M := M)) (A' B' C' : TF (I := I) (M := M)) =>
          τ (tvdPack v' A' B' C')) v A B C := by
  funext x
  simp only [tvdStepP, step, tvdShift_pack4, tvdPack_zero, tvdPack_castAdd, tvdPack_natAdd,
    tvdPack_update_castAdd, tvdPack_update_natAdd0, tvdPack_update_natAdd1,
    tvdPack_update_natAdd2, tvdPack_succ_castAdd, tvdPack_succ_natAdd0, tvdPack_succ_natAdd1,
    tvdPack_succ_natAdd2, Fin.sum_univ_add, Fin.sum_univ_three]
  ring

/-- **One recursion step, packed vs unpacked.** -/
theorem tvdStepP_eq_step (g : SMet I M) {k : ℕ} (τ : (Fin (k + 3) → TF (I := I) (M := M)) → M → ℝ)
    (F : Fin (k + 4) → TF (I := I) (M := M)) :
    tvdStepP g τ F
      = step (lcOf g) (fun (v : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)) =>
          τ (tvdPack v A B C))
          (fun j : Fin (k + 1) => F (Fin.castAdd 3 j))
          (F (Fin.natAdd (k + 1) (0 : Fin 3))) (F (Fin.natAdd (k + 1) (1 : Fin 3)))
          (F (Fin.natAdd (k + 1) (2 : Fin 3))) := by
  conv_lhs => rw [tvdPack_unpack F]
  exact tvdStepP_eq_step_pack g τ (fun j : Fin (k + 1) => F (Fin.castAdd 3 j))
    (F (Fin.natAdd (k + 1) (0 : Fin 3))) (F (Fin.natAdd (k + 1) (1 : Fin 3)))
    (F (Fin.natAdd (k + 1) (2 : Fin 3)))

/-- The packed recursion `tvdP` is the frozen `tower`. -/
theorem tvdP_eq_tvdTp (g : SMet I M) (base : Op3 (I := I) (M := M) 0) :
    ∀ k : ℕ, ∀ F : Fin (k + 3) → TF (I := I) (M := M), tvdP g base k F = tvdTp g base k F := by
  intro k
  induction k with
  | zero =>
      intro F
      funext x
      simp only [tvdP, tvdTp, tower]
      congr 2
      funext i
      exact i.elim0
  | succ k ih =>
      intro F
      rw [tvdP_succ]
      rw [show tvdP g base k = tvdTp g base k from funext (fun G => ih G)]
      rw [tvdStepP_eq_step]
      have hτ : (fun (v : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)) =>
            tvdTp g base k (tvdPack v A B C)) = tower (lcOf g) base k := by
        funext v A B C
        exact tvdTp_pack g base v A B C
      rw [hτ, tvdTp, tower]

/-! ## The three invariants for all `k` -/

theorem tvdSmLinT_all (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M)
    (base : Op3 (I := I) (M := M) 0)
    (hsm : ∀ (v : Fin 0 → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      SmE I M A → SmE I M B → SmE I M C → SmF I M (base v A B C))
    (hlinA : ∀ (b0 : Fin 0 → TF (I := I) (M := M)) (X₁ X₂ : TF (I := I) (M := M)) (f₁ f₂ : M → ℝ),
      SmF I M f₁ → SmF I M f₂ → SmE I M X₁ → SmE I M X₂ → ∀ (B C : TF (I := I) (M := M)) (x : M),
      base b0 (f₁ • X₁ + f₂ • X₂) B C x = f₁ x * base b0 X₁ B C x + f₂ x * base b0 X₂ B C x)
    (hlinB : ∀ (b0 : Fin 0 → TF (I := I) (M := M)) (X₁ X₂ : TF (I := I) (M := M)) (f₁ f₂ : M → ℝ),
      SmF I M f₁ → SmF I M f₂ → SmE I M X₁ → SmE I M X₂ → ∀ (A C : TF (I := I) (M := M)) (x : M),
      base b0 A (f₁ • X₁ + f₂ • X₂) C x = f₁ x * base b0 A X₁ C x + f₂ x * base b0 A X₂ C x)
    (hlinC : ∀ (b0 : Fin 0 → TF (I := I) (M := M)) (X₁ X₂ : TF (I := I) (M := M)) (f₁ f₂ : M → ℝ),
      SmF I M f₁ → SmF I M f₂ → SmE I M X₁ → SmE I M X₂ → ∀ (A B : TF (I := I) (M := M)) (x : M),
      base b0 A B (f₁ • X₁ + f₂ • X₂) x = f₁ x * base b0 A B X₁ x + f₂ x * base b0 A B X₂ x) :
    ∀ k : ℕ, tvdSmT g base k ∧ tvdLinT g base k := by
  intro k
  induction k with
  | zero => exact ⟨tvdSmT_zero g base hsm, tvdLinT_zero g base hlinA hlinB hlinC⟩
  | succ k ih => exact tvd_sm_lin_step_self hLC g base k ih.1 ih.2

theorem tvdGermTs_all (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M)
    (base : Op3 (I := I) (M := M) 0)
    (hvd : ∀ (b0 : Fin 0 → TF (I := I) (M := M))
      (A A' B B' C C' : TF (I := I) (M := M)) (x : M),
      SmE I M A → SmE I M A' → SmE I M B → SmE I M B' → SmE I M C → SmE I M C' →
      A x = A' x → B x = B' x → C x = C' x → base b0 A B C x = base b0 A' B' C' x) :
    ∀ k : ℕ, tvdGermTs g base k := by
  intro k
  induction k with
  | zero => exact tvdGermTs_zero g base hvd
  | succ k ih => exact tvd_germs_step hLC g base k ih

theorem tower_value_dep
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    {base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0}
    (hvd : ∀ (b0 : Fin 0 → (Π y : M, TangentSpace I y))
      (A A' B B' C C' : Π y : M, TangentSpace I y) (x : M),
      Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M A' →
      Work.Diff.EXT.ATower.SmE I M B → Work.Diff.EXT.ATower.SmE I M B' →
      Work.Diff.EXT.ATower.SmE I M C → Work.Diff.EXT.ATower.SmE I M C' →
      A x = A' x → B x = B' x → C x = C' x →
      base b0 A B C x = base b0 A' B' C' x)
    (hsm : ∀ (b0 : Fin 0 → (Π y : M, TangentSpace I y))
      (A B C : Π y : M, TangentSpace I y),
      Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M B →
      Work.Diff.EXT.ATower.SmE I M C →
      Work.Diff.EXT.ATower.SmF I M (fun y : M => base b0 A B C y))
    (hlinA : ∀ (b0 : Fin 0 → (Π y : M, TangentSpace I y))
      (X₁ X₂ : Π y : M, TangentSpace I y) (f₁ f₂ : M → ℝ),
      Work.Diff.EXT.ATower.SmF I M f₁ → Work.Diff.EXT.ATower.SmF I M f₂ →
      Work.Diff.EXT.ATower.SmE I M X₁ → Work.Diff.EXT.ATower.SmE I M X₂ →
      ∀ (B C : Π y : M, TangentSpace I y) (x : M),
      base b0 (f₁ • X₁ + f₂ • X₂) B C x
        = f₁ x * base b0 X₁ B C x + f₂ x * base b0 X₂ B C x)
    (hlinB : ∀ (b0 : Fin 0 → (Π y : M, TangentSpace I y))
      (X₁ X₂ : Π y : M, TangentSpace I y) (f₁ f₂ : M → ℝ),
      Work.Diff.EXT.ATower.SmF I M f₁ → Work.Diff.EXT.ATower.SmF I M f₂ →
      Work.Diff.EXT.ATower.SmE I M X₁ → Work.Diff.EXT.ATower.SmE I M X₂ →
      ∀ (A C : Π y : M, TangentSpace I y) (x : M),
      base b0 A (f₁ • X₁ + f₂ • X₂) C x
        = f₁ x * base b0 A X₁ C x + f₂ x * base b0 A X₂ C x)
    (hlinC : ∀ (b0 : Fin 0 → (Π y : M, TangentSpace I y))
      (X₁ X₂ : Π y : M, TangentSpace I y) (f₁ f₂ : M → ℝ),
      Work.Diff.EXT.ATower.SmF I M f₁ → Work.Diff.EXT.ATower.SmF I M f₂ →
      Work.Diff.EXT.ATower.SmE I M X₁ → Work.Diff.EXT.ATower.SmE I M X₂ →
      ∀ (A B : Π y : M, TangentSpace I y) (x : M),
      base b0 A B (f₁ • X₁ + f₂ • X₂) x
        = f₁ x * base b0 A B X₁ x + f₂ x * base b0 A B X₂ x) :
    ∀ k : ℕ, ∀ (v v' : Fin k → (Π y : M, TangentSpace I y))
      (A A' B B' C C' : Π y : M, TangentSpace I y) (x : M),
      (∀ j, Work.Diff.EXT.ATower.SmE I M (v j)) →
      (∀ j, Work.Diff.EXT.ATower.SmE I M (v' j)) → (∀ j, v j x = v' j x) →
      Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M A' →
      Work.Diff.EXT.ATower.SmE I M B → Work.Diff.EXT.ATower.SmE I M B' →
      Work.Diff.EXT.ATower.SmE I M C → Work.Diff.EXT.ATower.SmE I M C' →
      A x = A' x → B x = B' x → C x = C' x →
      Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf g) base k v A B C x
        = Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf g) base k v' A' B' C' x := by
  intro k v v' A A' B B' C C' x hv hv' hvv' hA hA' hB hB' hC hC' hAx hBx hCx
  -- the packed tuples and their agreement at `x`
  have hpack : ∀ j : Fin (k + 3),
      tvdPack v A B C j x = tvdPack v' A' B' C' j x := by
    intro j
    refine Fin.addCases (motive := fun j => tvdPack v A B C j x = tvdPack v' A' B' C' j x) ?_ ?_ j
    · intro i
      rw [tvdPack_castAdd, tvdPack_castAdd]
      exact hvv' i
    · intro j'
      rw [tvdPack_natAdd, tvdPack_natAdd]
      fin_cases j' <;> [exact hAx; exact hBx; exact hCx]
  have hpack_sm : ∀ j : Fin (k + 3), SmE I M (tvdPack v A B C j) := by
    intro j
    refine Fin.addCases (motive := fun j => SmE I M (tvdPack v A B C j)) ?_ ?_ j
    · intro i; rw [tvdPack_castAdd]; exact hv i
    · intro j'; rw [tvdPack_natAdd]
      fin_cases j' <;> [exact hA; exact hB; exact hC]
  have hpack_sm' : ∀ j : Fin (k + 3), SmE I M (tvdPack v' A' B' C' j) := by
    intro j
    refine Fin.addCases (motive := fun j => SmE I M (tvdPack v' A' B' C' j)) ?_ ?_ j
    · intro i; rw [tvdPack_castAdd]; exact hv' i
    · intro j'; rw [tvdPack_natAdd]
      fin_cases j' <;> [exact hA'; exact hB'; exact hC']
  -- the assembly
  have hSmLin := tvdSmLinT_all hLC g base hsm hlinA hlinB hlinC k
  have hGerm := tvdGermTs_all hLC g base hvd k
  have hVD := value_dep_of_germs_lin (Φ := tvdP g base k)
    (fun F F' y hF hF' h => hGerm F F' y hF hF' h)
    (fun F j ι _ X f S hF hX hf hS hrep => hSmLin.2 F j ι X f S hF hX hf hS hrep)
    hpack_sm hpack_sm' (fun j => hpack j)
  -- convert back to `tower`
  rw [← tvdTp_pack g base v A B C, ← tvdTp_pack g base v' A' B' C']
  rw [← tvdP_eq_tvdTp g base k (tvdPack v A B C),
    ← tvdP_eq_tvdTp g base k (tvdPack v' A' B' C')]
  exact hVD

end Work.Diff.EXT.ATower
