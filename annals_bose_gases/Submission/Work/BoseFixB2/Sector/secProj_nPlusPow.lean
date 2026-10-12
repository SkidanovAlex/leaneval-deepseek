import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Sector.jointProj_contDiff
import Submission.Work.BoseFixB2.Sector.nPlusPow_jointProj
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Sector.secProj_nPlusPow`

The `n₊ = k` sector `secProj ℓ k Φ = Σ_{|S| = k} E_S Φ` (`Work.BoseFixB2.secProj`) of a
smooth state is an eigenvector of every iterate of the excitation-number operator
`n₊ = Σᵢ Qᵢ` (`Work.BoseBox.nPlusPow`) with eigenvalue `k`:

    n₊^m (secProj ℓ k Φ) = k^m · secProj ℓ k Φ        (all m ≥ 0, Φ smooth).

This is the `secProj`-analogue of `Sector.nPlusPow_jointProj`, which proves the same
statement for a single joint sector `E_S` with eigenvalue `|S|`: the sector
`secProj ℓ k Φ` is the finite sum of the `E_S Φ` over the `k`-element subsets of
`{0,…,n−1}`, so every summand has the *same* eigenvalue `k`.  Since `n₊` is linear
(`aQ i` distributes over a finite sum of continuous functions — proved here from
`aP_add`), the eigenvalue comes out of the sum, and the `m`-induction is the same as
for a single sector (`nPlusFun_smul` + the `m = 1` eigenvalue identity).

## Contents

* `aP_finset_sum`, `aQ_finset_sum` (private) — the slot operators distribute over
  finite sums of continuous functions;
* `nPlusFun_finset_sum` (private) — the same for `n₊ = Σᵢ Qᵢ`;
* `nPlusFun_secProj` (private) — the `m = 1` identity `n₊(secProj ℓ k Φ) = k·secProj ℓ k Φ`;
* `secProj_nPlusPow` — the target, by induction on `m`.
-/

noncomputable section

namespace Work.BoseFixB2.Sector

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Linearity of the slot operators over finite sums -/

/-- `Pᵢ` distributes over a `Finset`-sum of continuous functions (induction on the
`Finset`, from `aP_add`; continuity of the partial sums comes from
`continuous_finsetSum`). -/
private lemma aP_finset_sum {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {ι : Type*}
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
private lemma aQ_finset_sum {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {ι : Type*}
    (s : Finset ι) {f : ι → X N → ℝ} (hf : ∀ j ∈ s, Continuous (f j)) (x : X N) :
    aQ ℓ i (fun y : X N => ∑ j ∈ s, f j y) x = ∑ j ∈ s, aQ ℓ i (f j) x := by
  have hP := aP_finset_sum hℓ i s hf x
  simp only [aQ]
  rw [hP, Finset.sum_sub_distrib]

/-- The excitation-number operator `n₊ = Σᵢ Qᵢ` distributes over a `Finset`-sum of
continuous functions (sum over the slots of `aQ_finset_sum`, then swap the two
finite sums). -/
private lemma nPlusFun_finset_sum {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {ι : Type*}
    (s : Finset ι) {f : ι → X N → ℝ} (hf : ∀ j ∈ s, Continuous (f j)) (x : X N) :
    Work.BoseBox.nPlusFun ℓ (fun y : X N => ∑ j ∈ s, f j y) x
      = ∑ j ∈ s, Work.BoseBox.nPlusFun ℓ (f j) x := by
  have hQ : ∀ i : Fin N,
      aQ ℓ i (fun y : X N => ∑ j ∈ s, f j y) x = ∑ j ∈ s, aQ ℓ i (f j) x :=
    fun i => aQ_finset_sum hℓ i s hf x
  simp only [Work.BoseBox.nPlusFun]
  refine (Finset.sum_congr rfl (fun i _ => hQ i)).trans ?_
  exact Finset.sum_comm

/-! ## 2. The eigenvalue identity for the whole sector -/

/-- **The `n₊ = k` sector is an eigenvector of `n₊` with eigenvalue `k`.**  Writing
`secProj ℓ k Φ = Σ_{|S| = k} E_S Φ`, linearity of `n₊` (`nPlusFun_finset_sum`) brings
the sum out, each `E_S Φ` contributes its own eigenvalue `|S| = k`
(`nPlusFun_jointProj`), and the common scalar `k` comes back out of the sum. -/
private lemma nPlusFun_secProj {ℓ : ℝ} (hℓ : 0 < ℓ) {n k : ℕ} {Φ : X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    Work.BoseBox.nPlusFun ℓ (secProj ℓ k Φ) = fun x => (k : ℝ) * secProj ℓ k Φ x := by
  have hcont : ∀ S ∈ (Finset.range n).powersetCard k, Continuous (jointProj ℓ S Φ) :=
    fun S _ => (jointProj_contDiff hℓ S hΦ).continuous
  have hsum : secProj ℓ k Φ
      = fun x => ∑ S ∈ (Finset.range n).powersetCard k, jointProj ℓ S Φ x := by
    rw [secProj, Finset.sum_fn]
  funext x
  calc Work.BoseBox.nPlusFun ℓ (secProj ℓ k Φ) x
      = ∑ S ∈ (Finset.range n).powersetCard k,
          Work.BoseBox.nPlusFun ℓ (jointProj ℓ S Φ) x := by
          rw [hsum]
          exact nPlusFun_finset_sum hℓ _ hcont x
    _ = ∑ S ∈ (Finset.range n).powersetCard k, (k : ℝ) * jointProj ℓ S Φ x := by
          refine Finset.sum_congr rfl (fun S hS => ?_)
          have hSsub : S ⊆ Finset.range n := (Finset.mem_powersetCard.mp hS).1
          have hScard : S.card = k := (Finset.mem_powersetCard.mp hS).2
          rw [congrFun (nPlusFun_jointProj (ℓ := ℓ) (n := n) (S := S) hℓ hSsub hΦ.continuous) x,
            hScard]
    _ = (k : ℝ) * secProj ℓ k Φ x := by
          have h2 : secProj ℓ k Φ x
              = ∑ S ∈ (Finset.range n).powersetCard k, jointProj ℓ S Φ x := by
            rw [secProj, Finset.sum_apply]
          rw [h2, ← Finset.mul_sum]

/-! ## 3. The iterates of `n₊` on a sector -/

/-- The two defining equations of `Work.BoseBox.nPlusPow`, as rewrite rules. -/
private lemma nPlusPow_zero (ℓ : ℝ) (N : ℕ) (Φ : X N → ℝ) :
    Work.BoseBox.nPlusPow ℓ N 0 Φ = Φ := rfl

private lemma nPlusPow_succ (ℓ : ℝ) (N m : ℕ) (Φ : X N → ℝ) :
    Work.BoseBox.nPlusPow ℓ N (m + 1) Φ
      = Work.BoseBox.nPlusFun ℓ (Work.BoseBox.nPlusPow ℓ N m Φ) := rfl

theorem secProj_nPlusPow {ℓ : ℝ} (hℓ : 0 < ℓ) {n k : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (m : ℕ) : Work.BoseBox.nPlusPow ℓ n m (Work.BoseFixB2.secProj ℓ k Φ) = fun x => (k : ℝ) ^ m * Work.BoseFixB2.secProj ℓ k Φ x := by
  have key := nPlusFun_secProj (ℓ := ℓ) (n := n) (k := k) (Φ := Φ) hℓ hΦ
  induction m with
  | zero =>
      rw [nPlusPow_zero]
      funext x
      simp
  | succ m ih =>
      rw [nPlusPow_succ, ih,
        nPlusFun_smul ℓ ((k : ℝ) ^ m) (Work.BoseFixB2.secProj ℓ k Φ), key]
      funext x
      simp only []
      rw [pow_succ]
      ring

end Work.BoseFixB2.Sector
