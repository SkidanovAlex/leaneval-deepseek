import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.TInvDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Commons.Geometry.Manifold.VectorField

namespace Work.Diff.EXT.ConnCov.RicFlip

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- The recursion of the packed tower, unfolded into the explicit `packStep` shape. -/
lemma packTower_succ_unfold (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ)
    (F : Fin (k + 4) → (Π y : M, TangentSpace I y)) :
    packTower g base (k + 1) F
      = fun y : M =>
          (mvfderiv I (packTower g base k (fun i : Fin (k + 3) => F i.succ)) y) (F 0 y)
          - ∑ s : Fin (k + 3), packTower g base k
              (Function.update (fun i : Fin (k + 3) => F i.succ) s
                (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 3) => F i.succ) s) (F 0))) y := rfl

-- Linearity step of the induction `PInv g base k → PInv g base (k+1)`, in the *tail* slot `j.succ`
-- (`j : Fin (k+3)`), i.e. in a slot which the recursion sees both as a slot of the inner tower and
-- (through `dirFA`) as the *section* being differentiated.  This is the slot where the Leibniz
-- terms of `mvfderiv` and of `dirFA` have to cancel.
-- Route: `(update F j.succ W) ∘ Fin.succ = Function.update (F ∘ Fin.succ) j W` (prove by `funext`
-- and `Fin.succ_inj`), then unfold `packStep`:
--   * the `mvfderiv` term: rewrite the function with the induction hypothesis `h` at slot `j`, then
--     apply the Leibniz rule for `mvfderiv` of a sum of two scalar multiples,
--     `Work.Diff.EXT.mvfderiv_two_smulA` (`Submission/Work/Diff/EXT/ATens/Defs.lean`);
--   * the sum: split `s = j` from `s ≠ j` (`Finset.add_sum_erase`);
--       - for `s ≠ j` the inserted field does not depend on `W` and `Function.update_comm`
--         reorders the two updates, after which the induction hypothesis at slot `j` applies;
--       - for `s = j` the inserted field is `dirFA g W (F 0)`, rewritten by the Leibniz rule
--         `Work.Diff.EXT.dirFA_leibniz` (in its *section* argument; `Submission/Work/Diff/EXT/ATens/Kit.lean`)
--         and `Function.update_idem`, after which the induction hypothesis applies twice (once to
--         each of the two scalar terms);
--   * the two Leibniz-type remainders cancel exactly against each other: close with `ring`.
-- The same computation is the PROVED `Work.Diff.EXT.ka_lin_tail` in
-- `Submission/Work/Diff/EXT/covKAExt_frame_eq_smoothExt.lean` (specialised case); copy its proof.
-- Smoothness of the relevant `dirFA` fields is `Work.Diff.EXT.dirFA_smooth hLC g`.

theorem packTower_lin_tail
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ)
    (h : Work.Diff.EXT.ConnCov.RicFlip.PInv g base k)
    {F : Fin (k + 4) → (Π y : M, TangentSpace I y)}
    (hF : ∀ s, Work.Diff.EXT.ATower.SmE I M (F s))
    (j : Fin (k + 3))
    {X₁ X₂ : Π y : M, TangentSpace I y}
    (hX₁ : Work.Diff.EXT.ATower.SmE I M X₁) (hX₂ : Work.Diff.EXT.ATower.SmE I M X₂)
    {f₁ f₂ : M → ℝ} (hf₁ : Work.Diff.EXT.ATower.SmF I M f₁) (hf₂ : Work.Diff.EXT.ATower.SmF I M f₂) :
    Work.Diff.EXT.ConnCov.RicFlip.packTower g base (k + 1)
        (Function.update F j.succ (f₁ • X₁ + f₂ • X₂))
      = f₁ • Work.Diff.EXT.ConnCov.RicFlip.packTower g base (k + 1) (Function.update F j.succ X₁)
        + f₂ • Work.Diff.EXT.ConnCov.RicFlip.packTower g base (k + 1) (Function.update F j.succ X₂) := by
  -- the shifted tuple, and the smoothness data in the `ATens` spelling used by the kit lemmas
  have hFsucc : ∀ i : Fin (k + 3),
      Work.Diff.EXT.SmA (I := I) (M := M) ((fun i : Fin (k + 3) => F i.succ) i) := fun i => hF i.succ
  have hF0 : Work.Diff.EXT.SmA (I := I) (M := M) (F 0) := hF 0
  -- `Fin.cons` bookkeeping for the tuple `Function.update F j.succ W`
  have hconsF : ∀ (W : Fin (k + 3) → (Π y : M, TangentSpace I y)),
      (fun i : Fin (k + 3) =>
        (Fin.cons (F 0) W : Fin (k + 4) → (Π y : M, TangentSpace I y)) i.succ) = W := by
    intro W; funext i
    exact Fin.cons_succ (α := fun _ : Fin (k + 4) => (Π y : M, TangentSpace I y)) (F 0) W i
  have hconsP : ∀ (W : Fin (k + 3) → (Π y : M, TangentSpace I y)) (i : Fin (k + 3)),
      (Fin.cons (F 0) W : Fin (k + 4) → (Π y : M, TangentSpace I y)) i.succ = W i :=
    fun W i => Fin.cons_succ (α := fun _ : Fin (k + 4) => (Π y : M, TangentSpace I y)) (F 0) W i
  have hzero : ∀ (W : Fin (k + 3) → (Π y : M, TangentSpace I y)),
      (Fin.cons (F 0) W : Fin (k + 4) → (Π y : M, TangentSpace I y)) 0 = F 0 :=
    fun W => Fin.cons_zero (α := fun _ : Fin (k + 4) => (Π y : M, TangentSpace I y)) (F 0) W
  rw [Work.Diff.EXT.update_succ_eq_consA, Work.Diff.EXT.update_succ_eq_consA,
    Work.Diff.EXT.update_succ_eq_consA]
  rw [packTower_succ_unfold, packTower_succ_unfold, packTower_succ_unfold]
  simp only [hconsF, hconsP, hzero]
  funext y
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply', Finset.sum_apply]
  -- the induction hypothesis at slot `j`
  have hAW : packTower g base k (Function.update (fun i : Fin (k + 3) => F i.succ) j
        (f₁ • X₁ + f₂ • X₂))
      = f₁ • packTower g base k (Function.update (fun i : Fin (k + 3) => F i.succ) j X₁)
        + f₂ • packTower g base k (Function.update (fun i : Fin (k + 3) => F i.succ) j X₂) :=
    (h (fun i : Fin (k + 3) => F i.succ) hFsucc).2.1 j X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂
  -- additivity at slot `j`, derived from the induction hypothesis
  have hadd : ∀ {A B : Π y : M, TangentSpace I y},
      Work.Diff.EXT.SmA (I := I) (M := M) A → Work.Diff.EXT.SmA (I := I) (M := M) B →
      packTower g base k (Function.update (fun i : Fin (k + 3) => F i.succ) j (A + B))
        = packTower g base k (Function.update (fun i : Fin (k + 3) => F i.succ) j A)
          + packTower g base k (Function.update (fun i : Fin (k + 3) => F i.succ) j B) := by
    intro A B hA hB
    have h1 := (h (fun i : Fin (k + 3) => F i.succ) hFsucc).2.1 j A B (fun _ : M => (1 : ℝ))
      (fun _ : M => (1 : ℝ)) hA hB (contMDiff_const (c := (1 : ℝ)))
      (contMDiff_const (c := (1 : ℝ)))
    have hAB : (fun _ : M => (1 : ℝ)) • A + (fun _ : M => (1 : ℝ)) • B = A + B := by
      funext z; simp
    have hA' : (fun _ : M => (1 : ℝ)) •
        packTower g base k (Function.update (fun i : Fin (k + 3) => F i.succ) j A)
        = packTower g base k (Function.update (fun i : Fin (k + 3) => F i.succ) j A) := by
      funext z; simp
    have hB' : (fun _ : M => (1 : ℝ)) •
        packTower g base k (Function.update (fun i : Fin (k + 3) => F i.succ) j B)
        = packTower g base k (Function.update (fun i : Fin (k + 3) => F i.succ) j B) := by
      funext z; simp
    rw [hAB, hA', hB'] at h1
    exact h1
  have hS1 : Work.Diff.EXT.SmFunM (I := I) (M := M)
      (packTower g base k (Function.update (fun i : Fin (k + 3) => F i.succ) j X₁)) :=
    (h _ (Work.Diff.EXT.smA_update hFsucc hX₁)).1
  have hS2 : Work.Diff.EXT.SmFunM (I := I) (M := M)
      (packTower g base k (Function.update (fun i : Fin (k + 3) => F i.succ) j X₂)) :=
    (h _ (Work.Diff.EXT.smA_update hFsucc hX₂)).1
  -- the `mvfderiv` Leibniz term
  have hT : (mvfderiv I (packTower g base k
        (Function.update (fun i : Fin (k + 3) => F i.succ) j (f₁ • X₁ + f₂ • X₂))) y) ((F 0) y)
      = f₁ y * ((mvfderiv I (packTower g base k
            (Function.update (fun i : Fin (k + 3) => F i.succ) j X₁)) y) ((F 0) y))
        + ((mvfderiv I f₁ y) ((F 0) y)) *
            (packTower g base k (Function.update (fun i : Fin (k + 3) => F i.succ) j X₁) y)
        + f₂ y * ((mvfderiv I (packTower g base k
            (Function.update (fun i : Fin (k + 3) => F i.succ) j X₂)) y) ((F 0) y))
        + ((mvfderiv I f₂ y) ((F 0) y)) *
            (packTower g base k (Function.update (fun i : Fin (k + 3) => F i.succ) j X₂) y) := by
    rw [hAW]
    rw [Work.Diff.EXT.mvfderiv_two_smulA f₁ f₂
      (packTower g base k (Function.update (fun i : Fin (k + 3) => F i.succ) j X₁))
      (packTower g base k (Function.update (fun i : Fin (k + 3) => F i.succ) j X₂)) y ((F 0) y)
      (hf₁.mdifferentiableAt (by simp)) (hf₂.mdifferentiableAt (by simp))
      (hS1.mdifferentiableAt (by simp)) (hS2.mdifferentiableAt (by simp))]
  -- the `s ≠ j` terms of the correction sum
  have hstep : ∀ q : Fin (k + 3), q ≠ j →
      packTower g base k
        (Function.update (Function.update (fun i : Fin (k + 3) => F i.succ) j
          (f₁ • X₁ + f₂ • X₂)) q
          (dirFA g ((Function.update (fun i : Fin (k + 3) => F i.succ) j
              (f₁ • X₁ + f₂ • X₂)) q) (F 0)))
      = f₁ • packTower g base k
            (Function.update (Function.update (fun i : Fin (k + 3) => F i.succ) j X₁) q
              (dirFA g ((Function.update (fun i : Fin (k + 3) => F i.succ) j X₁) q) (F 0)))
        + f₂ • packTower g base k
            (Function.update (Function.update (fun i : Fin (k + 3) => F i.succ) j X₂) q
              (dirFA g ((Function.update (fun i : Fin (k + 3) => F i.succ) j X₂) q) (F 0))) := by
    intro q hqj
    have h1 : Function.update
        (Function.update (fun i : Fin (k + 3) => F i.succ) j (f₁ • X₁ + f₂ • X₂)) q
        (dirFA g ((Function.update (fun i : Fin (k + 3) => F i.succ) j
          (f₁ • X₁ + f₂ • X₂)) q) (F 0))
        = Function.update
            (Function.update (fun i : Fin (k + 3) => F i.succ) q
              (dirFA g ((fun i : Fin (k + 3) => F i.succ) q) (F 0))) j
            (f₁ • X₁ + f₂ • X₂) := by
      rw [Function.update_of_ne hqj (f₁ • X₁ + f₂ • X₂) (fun i : Fin (k + 3) => F i.succ)]
      exact (Function.update_comm hqj (dirFA g ((fun i : Fin (k + 3) => F i.succ) q) (F 0))
        (f₁ • X₁ + f₂ • X₂) (fun i : Fin (k + 3) => F i.succ)).symm
    have h2 : Function.update
        (Function.update (fun i : Fin (k + 3) => F i.succ) q
          (dirFA g ((fun i : Fin (k + 3) => F i.succ) q) (F 0))) j X₁
        = Function.update
            (Function.update (fun i : Fin (k + 3) => F i.succ) j X₁) q
            (dirFA g ((Function.update (fun i : Fin (k + 3) => F i.succ) j X₁) q) (F 0)) := by
      rw [Function.update_of_ne hqj X₁ (fun i : Fin (k + 3) => F i.succ)]
      exact Function.update_comm hqj (dirFA g ((fun i : Fin (k + 3) => F i.succ) q) (F 0)) X₁
        (fun i : Fin (k + 3) => F i.succ)
    have h3 : Function.update
        (Function.update (fun i : Fin (k + 3) => F i.succ) q
          (dirFA g ((fun i : Fin (k + 3) => F i.succ) q) (F 0))) j X₂
        = Function.update
            (Function.update (fun i : Fin (k + 3) => F i.succ) j X₂) q
            (dirFA g ((Function.update (fun i : Fin (k + 3) => F i.succ) j X₂) q) (F 0)) := by
      rw [Function.update_of_ne hqj X₂ (fun i : Fin (k + 3) => F i.succ)]
      exact Function.update_comm hqj (dirFA g ((fun i : Fin (k + 3) => F i.succ) q) (F 0)) X₂
        (fun i : Fin (k + 3) => F i.succ)
    rw [h1]
    have hlin := (h (Function.update (fun i : Fin (k + 3) => F i.succ) q
        (dirFA g ((fun i : Fin (k + 3) => F i.succ) q) (F 0)))
      (Work.Diff.EXT.smA_update hFsucc
        (Work.Diff.EXT.dirFA_smooth hLC g (hFsucc q) hF0))).2.1 j X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂
    rw [hlin, h2, h3]
  -- the `s = j` term of the correction sum
  have hjterm : packTower g base k
        (Function.update (Function.update (fun i : Fin (k + 3) => F i.succ) j
          (f₁ • X₁ + f₂ • X₂)) j
          (dirFA g ((Function.update (fun i : Fin (k + 3) => F i.succ) j
            (f₁ • X₁ + f₂ • X₂)) j) (F 0))) y
      = f₁ y • (packTower g base k
            (Function.update (Function.update (fun i : Fin (k + 3) => F i.succ) j X₁) j
              (dirFA g ((Function.update (fun i : Fin (k + 3) => F i.succ) j X₁) j) (F 0))) y)
        + f₂ y • (packTower g base k
            (Function.update (Function.update (fun i : Fin (k + 3) => F i.succ) j X₂) j
              (dirFA g ((Function.update (fun i : Fin (k + 3) => F i.succ) j X₂) j) (F 0))) y)
        + ((mvfderiv I f₁ y) ((F 0) y)) •
            (packTower g base k (Function.update (fun i : Fin (k + 3) => F i.succ) j X₁) y)
        + ((mvfderiv I f₂ y) ((F 0) y)) •
            (packTower g base k (Function.update (fun i : Fin (k + 3) => F i.succ) j X₂) y) := by
    have hidem : Function.update
        (Function.update (fun i : Fin (k + 3) => F i.succ) j (f₁ • X₁ + f₂ • X₂)) j
        (dirFA g (Function.update (fun i : Fin (k + 3) => F i.succ) j (f₁ • X₁ + f₂ • X₂) j)
          (F 0))
        = Function.update (fun i : Fin (k + 3) => F i.succ) j
            (dirFA g (f₁ • X₁ + f₂ • X₂) (F 0)) := by
      rw [Function.update_self]
      exact Function.update_idem (α := Fin (k + 3))
        (β := fun _ : Fin (k + 3) => (Π y : M, TangentSpace I y)) (a := j)
        (f₁ • X₁ + f₂ • X₂) (dirFA g (f₁ • X₁ + f₂ • X₂) (F 0))
        (fun i : Fin (k + 3) => F i.succ)
    rw [hidem, Work.Diff.EXT.dirFA_leibniz (g := g) (X₁ := X₁) (X₂ := X₂) (f₁ := f₁) (f₂ := f₂)
      (v0 := F 0) hX₁ hX₂ hf₁ hf₂]
    have hE1 : Work.Diff.EXT.SmFunM (I := I) (M := M) (fun z : M => (mvfderiv I f₁ z) ((F 0) z)) :=
      Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hf₁ hF0
    have hE2 : Work.Diff.EXT.SmFunM (I := I) (M := M) (fun z : M => (mvfderiv I f₂ z) ((F 0) z)) :=
      Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hf₂ hF0
    rw [add_assoc (f₁ • dirFA g X₁ (F 0) + (fun z : M => (mvfderiv I f₁ z) ((F 0) z)) • X₁)
        (f₂ • dirFA g X₂ (F 0)) ((fun z : M => (mvfderiv I f₂ z) ((F 0) z)) • X₂)]
    rw [hadd (Work.Diff.EXT.SmA_add
          (Work.Diff.EXT.SmA_smul hf₁ (Work.Diff.EXT.dirFA_smooth hLC g hX₁ hF0))
          (Work.Diff.EXT.SmA_smul hE1 hX₁))
        (Work.Diff.EXT.SmA_add
          (Work.Diff.EXT.SmA_smul hf₂ (Work.Diff.EXT.dirFA_smooth hLC g hX₂ hF0))
          (Work.Diff.EXT.SmA_smul hE2 hX₂))]
    rw [(h (fun i : Fin (k + 3) => F i.succ) hFsucc).2.1 j (dirFA g X₁ (F 0)) X₁ f₁
        (fun z : M => (mvfderiv I f₁ z) ((F 0) z))
        (Work.Diff.EXT.dirFA_smooth hLC g hX₁ hF0) hX₁ hf₁ hE1]
    rw [(h (fun i : Fin (k + 3) => F i.succ) hFsucc).2.1 j (dirFA g X₂ (F 0)) X₂ f₂
        (fun z : M => (mvfderiv I f₂ z) ((F 0) z))
        (Work.Diff.EXT.dirFA_smooth hLC g hX₂ hF0) hX₂ hf₂ hE2]
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply', Function.update_idem,
      Function.update_self, smul_eq_mul]
    ring
  -- the `s ≠ j` part of the correction sum, after the induction hypothesis
  have hne : (∑ q ∈ Finset.univ.erase j, packTower g base k
        (Function.update (Function.update (fun i : Fin (k + 3) => F i.succ) j
          (f₁ • X₁ + f₂ • X₂)) q
          (dirFA g ((Function.update (fun i : Fin (k + 3) => F i.succ) j
            (f₁ • X₁ + f₂ • X₂)) q) (F 0))) y)
      = f₁ y * (∑ q ∈ Finset.univ.erase j, packTower g base k
            (Function.update (Function.update (fun i : Fin (k + 3) => F i.succ) j X₁) q
              (dirFA g ((Function.update (fun i : Fin (k + 3) => F i.succ) j X₁) q) (F 0))) y)
        + f₂ y * (∑ q ∈ Finset.univ.erase j, packTower g base k
            (Function.update (Function.update (fun i : Fin (k + 3) => F i.succ) j X₂) q
              (dirFA g ((Function.update (fun i : Fin (k + 3) => F i.succ) j X₂) q) (F 0))) y) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    have hqj : q ≠ j := (Finset.mem_erase.mp hq).1
    rw [hstep q hqj]
    simp only [Pi.add_apply, Pi.mul_apply, smul_eq_mul]
  -- the full correction sum
  have hS : (∑ q : Fin (k + 3), packTower g base k
        (Function.update (Function.update (fun i : Fin (k + 3) => F i.succ) j
          (f₁ • X₁ + f₂ • X₂)) q
          (dirFA g ((Function.update (fun i : Fin (k + 3) => F i.succ) j
            (f₁ • X₁ + f₂ • X₂)) q) (F 0))) y)
      = f₁ y • (∑ q : Fin (k + 3), packTower g base k
            (Function.update (Function.update (fun i : Fin (k + 3) => F i.succ) j X₁) q
              (dirFA g ((Function.update (fun i : Fin (k + 3) => F i.succ) j X₁) q) (F 0))) y)
        + f₂ y • (∑ q : Fin (k + 3), packTower g base k
            (Function.update (Function.update (fun i : Fin (k + 3) => F i.succ) j X₂) q
              (dirFA g ((Function.update (fun i : Fin (k + 3) => F i.succ) j X₂) q) (F 0))) y)
        + ((mvfderiv I f₁ y) ((F 0) y)) •
            (packTower g base k (Function.update (fun i : Fin (k + 3) => F i.succ) j X₁) y)
        + ((mvfderiv I f₂ y) ((F 0) y)) •
            (packTower g base k (Function.update (fun i : Fin (k + 3) => F i.succ) j X₂) y) := by
    rw [← Finset.add_sum_erase Finset.univ _ (a := j) (Finset.mem_univ j),
      ← Finset.add_sum_erase Finset.univ _ (a := j) (Finset.mem_univ j),
      ← Finset.add_sum_erase Finset.univ _ (a := j) (Finset.mem_univ j)]
    rw [hjterm, hne]
    simp only [smul_add, smul_eq_mul]
    ring
  rw [hT, hS]
  simp only [smul_sub, smul_add, smul_eq_mul]
  ring

end Work.Diff.EXT.ConnCov.RicFlip
