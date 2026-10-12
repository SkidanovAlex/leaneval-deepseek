import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Sector.secProj_nPlusPow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Recomb.nPlusPow_secProj_sum`

The excitation-number operator `n₊ = ΣᵢQᵢ` (`Work.BoseBox.nPlusFun`) is **linear** on
continuous states, so its iterates `nPlusPow ℓ n m` distribute over finite linear
combinations of sectors:

    n₊^m (Σ_k c_k 1_{n₊=k}Φ) = Σ_k (c_k k^m) 1_{n₊=k}Φ .

This is the `Σ`-form of the eigenvalue statement `Sector.secProj_nPlusPow`
(`n₊^m (secProj ℓ k Φ) = k^m · secProj ℓ k Φ`, each sector being a common eigenvector of
the `k` "occupied" slots): linearity brings `n₊^m` inside the finite sum, homogeneity
pulls the scalars `c k` out, and the eigenvalue identity evaluates the rest.

The linearity is genuinely needed at every iterate: `n₊ = Σᵢ(1 − Pᵢ)` distributes over
finite sums of *continuous* functions (the mean `Pᵢ` is an integral, so `aP_add` carries
`Continuous` hypotheses), and iterating preserves continuity.

## Contents

* `nPlusFun_continuous`, `continuous_nPlusPow` — continuity of `n₊` and its iterates;
* `secProj_continuous` — the sector of a smooth state is continuous;
* `aP_finset_sum`, `aQ_finset_sum`, `nPlusFun_finset_sum` — linearity of the slot
  operators and of `n₊` over finite sums of continuous functions;
* `nPlusPow_finset_sum` — linearity of every iterate `n₊^m` over finite sums;
* `nPlusPow_const_mul` — homogeneity of every iterate under a constant factor;
* `nPlusPow_secProj_sum` — the target.
-/

noncomputable section

namespace Work.BoseFixB2.Recomb

open Submission.BoseGases
open scoped BigOperators

set_option autoImplicit false

/-! ## 1. Continuity of the iterates and of the sectors -/

/-- The two defining equations of `Work.BoseBox.nPlusPow`, as rewrite rules. -/
lemma nPlusPow_zero_eq (ℓ : ℝ) (N : ℕ) (Φ : X N → ℝ) :
    Work.BoseBox.nPlusPow ℓ N 0 Φ = Φ := rfl

lemma nPlusPow_succ_eq (ℓ : ℝ) (N m : ℕ) (Φ : X N → ℝ) :
    Work.BoseBox.nPlusPow ℓ N (m + 1) Φ
      = Work.BoseBox.nPlusFun ℓ (Work.BoseBox.nPlusPow ℓ N m Φ) := rfl

/-- `n₊ = ΣᵢQᵢ` preserves continuity (finite sum of the slot operators `aQ ℓ i`, which
are continuous on continuous states). -/
lemma nPlusFun_continuous {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} {f : X N → ℝ}
    (hf : Continuous f) : Continuous (Work.BoseBox.nPlusFun ℓ f) := by
  show Continuous (fun x => ∑ i : Fin N, aQ ℓ i f x)
  exact continuous_finsetSum Finset.univ (fun i _ => aQ_continuous hℓ i hf)

/-- Every iterate `n₊^m` preserves continuity. -/
lemma continuous_nPlusPow {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} {f : X N → ℝ} (hf : Continuous f) :
    ∀ m : ℕ, Continuous (Work.BoseBox.nPlusPow ℓ N m f) := by
  intro m
  induction m with
  | zero => rw [nPlusPow_zero_eq]; exact hf
  | succ m ih => rw [nPlusPow_succ_eq]; exact nPlusFun_continuous hℓ ih

/-- The `n₊ = k` sector of a smooth state is continuous (finite sum of the continuous
joint sectors `jointProj ℓ S Φ`). -/
lemma secProj_continuous {ℓ : ℝ} (hℓ : 0 < ℓ) {n k : ℕ} {Φ : X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) : Continuous (Work.BoseFixB2.secProj ℓ k Φ) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB2.secProj ℓ k Φ) := by
    rw [Work.BoseFixB2.secProj, Finset.sum_fn]
    exact ContDiff.sum (fun S _ => Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ)
  exact h.continuous

/-! ## 2. Linearity over finite sums of continuous functions -/

/-- `Pᵢ` distributes over a `Finset`-sum of continuous functions (induction on the
`Finset`, from `aP_add`; continuity of the partial sums comes from
`continuous_finsetSum`). -/
lemma aP_finset_sum {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {ι : Type*}
    (s : Finset ι) {f : ι → X N → ℝ} (hf : ∀ j ∈ s, Continuous (f j)) (x : X N) :
    aP ℓ i (fun y : X N => ∑ j ∈ s, f j y) x = ∑ j ∈ s, aP ℓ i (f j) x := by
  classical
  induction s using Finset.induction with
  | empty => simp [aP]
  | insert a s has ih =>
      have hfa : Continuous (f a) := hf a (by simp)
      have hfs : ∀ j ∈ s, Continuous (f j) := fun j hj => hf j (by simp [hj])
      have hIH := ih hfs
      have hfun : (fun y : X N => ∑ j ∈ insert a s, f j y)
          = fun y : X N => f a y + (∑ j ∈ s, f j y) := by
        funext y; rw [Finset.sum_insert has]
      have hcontS : Continuous (fun y : X N => ∑ j ∈ s, f j y) :=
        continuous_finsetSum s (fun j hj => hfs j hj)
      calc
        aP ℓ i (fun y : X N => ∑ j ∈ insert a s, f j y) x
            = aP ℓ i (fun y : X N => f a y + (∑ j ∈ s, f j y)) x := by rw [hfun]
        _ = aP ℓ i (f a) x + aP ℓ i (fun y : X N => ∑ j ∈ s, f j y) x :=
              aP_add hℓ i hfa hcontS x
        _ = aP ℓ i (f a) x + (∑ j ∈ s, aP ℓ i (f j) x) := by rw [hIH]
        _ = ∑ j ∈ insert a s, aP ℓ i (f j) x := by rw [Finset.sum_insert has]

/-- `Qᵢ = 1 − Pᵢ` distributes over a `Finset`-sum of continuous functions, since both
terms of `Qᵢ` do. -/
lemma aQ_finset_sum {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {ι : Type*}
    (s : Finset ι) {f : ι → X N → ℝ} (hf : ∀ j ∈ s, Continuous (f j)) (x : X N) :
    aQ ℓ i (fun y : X N => ∑ j ∈ s, f j y) x = ∑ j ∈ s, aQ ℓ i (f j) x := by
  have hP := aP_finset_sum hℓ i s hf x
  simp only [aQ]
  rw [hP, Finset.sum_sub_distrib]

/-- The excitation-number operator `n₊ = ΣᵢQᵢ` distributes over a `Finset`-sum of
continuous functions (sum over the slots of `aQ_finset_sum`, then swap the two finite
sums). -/
lemma nPlusFun_finset_sum {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {ι : Type*}
    (s : Finset ι) {f : ι → X N → ℝ} (hf : ∀ j ∈ s, Continuous (f j)) :
    Work.BoseBox.nPlusFun ℓ (fun y : X N => ∑ j ∈ s, f j y)
      = fun x => ∑ j ∈ s, Work.BoseBox.nPlusFun ℓ (f j) x := by
  funext x
  have hQ : ∀ i : Fin N,
      aQ ℓ i (fun y : X N => ∑ j ∈ s, f j y) x = ∑ j ∈ s, aQ ℓ i (f j) x :=
    fun i => aQ_finset_sum hℓ i s hf x
  simp only [Work.BoseBox.nPlusFun]
  refine (Finset.sum_congr rfl (fun i _ => hQ i)).trans ?_
  exact Finset.sum_comm

/-- **Every iterate `n₊^m` is linear over finite sums of continuous functions.** -/
lemma nPlusPow_finset_sum {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {ι : Type*}
    (s : Finset ι) {f : ι → X N → ℝ} (hf : ∀ j ∈ s, Continuous (f j)) (m : ℕ) :
    Work.BoseBox.nPlusPow ℓ N m (fun y : X N => ∑ j ∈ s, f j y)
      = fun x => ∑ j ∈ s, Work.BoseBox.nPlusPow ℓ N m (f j) x := by
  induction m with
  | zero =>
      funext x
      simp only [nPlusPow_zero_eq]
  | succ m ih =>
      rw [nPlusPow_succ_eq, ih, nPlusFun_finset_sum hℓ s
        (fun j hj => continuous_nPlusPow hℓ (hf j hj) m)]
      funext x
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [nPlusPow_succ_eq]

/-- **Every iterate `n₊^m` is homogeneous** under multiplication by a constant. -/
lemma nPlusPow_const_mul {N : ℕ} {ℓ : ℝ} (c : ℝ) (Ψ : X N → ℝ) (m : ℕ) :
    Work.BoseBox.nPlusPow ℓ N m (fun x => c * Ψ x)
      = fun x => c * Work.BoseBox.nPlusPow ℓ N m Ψ x := by
  induction m with
  | zero => simp only [nPlusPow_zero_eq]
  | succ m ih =>
      rw [nPlusPow_succ_eq, ih, Work.BoseFixB2.Sector.nPlusFun_smul, nPlusPow_succ_eq]

/-! ## 3. The target -/

theorem nPlusPow_secProj_sum {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (c : ℕ → ℝ) (m : ℕ) : Work.BoseBox.nPlusPow ℓ n m (fun x => ∑ k ∈ Finset.range (n + 1), c k * Work.BoseFixB2.secProj ℓ k Φ x) = fun x => ∑ k ∈ Finset.range (n + 1), (c k * (k : ℝ) ^ m) * Work.BoseFixB2.secProj ℓ k Φ x := by
  have hcont : ∀ k ∈ Finset.range (n + 1),
      Continuous (fun x : X n => c k * Work.BoseFixB2.secProj ℓ k Φ x) :=
    fun k _ => (secProj_continuous hℓ hΦ).const_mul (c k)
  rw [nPlusPow_finset_sum hℓ (Finset.range (n + 1)) hcont m]
  funext x
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [nPlusPow_const_mul (c := c k) (Ψ := Work.BoseFixB2.secProj ℓ k Φ) (N := n) (ℓ := ℓ) m,
    Work.BoseFixB2.Sector.secProj_nPlusPow hℓ hΦ m]
  simp only []
  ring

end Work.BoseFixB2.Recomb
