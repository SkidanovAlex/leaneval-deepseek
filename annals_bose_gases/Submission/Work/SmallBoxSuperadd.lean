import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.Work.AboxBlockSplit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Per-sector superadditivity of the small-box analysis energy (e_B layer)

FS thm:smallbox's group trick needs `e_B(n, μ) ≥ m·e_B(n′, μ) + e_B(n″, μ)`
(`e_B` = the n-particle ground-state energy of the μ-dependent box
Hamiltonian), which is a superadditivity in the *particle number at a fixed
box*.  It follows by splitting the `n₁+n₂` particles into two groups (label
splitting, not spatial), dropping the (nonnegative) cross-group pair
interaction, and bounding each group's energy by its own ground-state energy
(`E_g ≥ e_B(n_g)·‖Φ‖²` slicewise).

This module contains the *pointwise / index* half of that structure for the
corpus analysis words `kinWord N s Φ` and
`qLHSword(N, s, μ, wPairC s v, wPairC s (g0 v h)) Φ`:

  * the ordered-distinct-pair (`pairSet`) block-split identities
    (`pairSet_split`, `pairSet_split_ge`), the exact transcription for the
    qLHSword diagonal density (`qLHSden`, `qLHSden_split`,
    `qLHSdenCross_nonneg`, `qLHSden_blocks_le`);
  * the merge-coordinate identities (`merge_apply_castAdd`, ...).

The slice/Fubini half (expectation level: `E_{n₁+n₂}(Φ) ≥ E₁(Φ) + E₂(Φ)`
with `E_g(Φ) = ∫_{abox N_g s} E_{n_g}(slice)`), and the `e_B` infimum
definition + superadditivity theorem itself are the next layer
(`AboxBlockSplit.lean` carries the measure infrastructure).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Ordered-distinct-pair block split (pure index combinatorics) -/

@[simp] lemma castAdd_ne_natAdd {a b : ℕ} (i : Fin a) (j : Fin b) :
    Fin.castAdd b i ≠ Fin.natAdd a j := by
  intro h
  have hv := congrArg Fin.val h
  have h1 : (Fin.castAdd b i).val < a := by simp
  have h2 : a ≤ (Fin.natAdd a j).val := by simp
  omega

@[simp] lemma natAdd_ne_castAdd {a b : ℕ} (j : Fin b) (i : Fin a) :
    Fin.natAdd a j ≠ Fin.castAdd b i := by
  exact (castAdd_ne_natAdd (a := a) (b := b) i j).symm

/-- A sum over ordered distinct pairs equals the double sum with an
`i ≠ j`-guard. -/
private lemma sbs_sum_pairSet_eq_double {N : ℕ} (g : Fin N → Fin N → ℝ) :
    (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 ≠ p.2)), g p.1 p.2)
    = ∑ i : Fin N, ∑ j : Fin N, (if i ≠ j then g i j else 0) := by
  rw [Finset.sum_filter]
  simpa using (Fintype.sum_prod_type (γ := ℝ)
    (f := fun p : Fin N × Fin N => if p.1 ≠ p.2 then g p.1 p.2 else 0))

/-- A double sum over `Fin (a+b) × Fin (a+b)` splits into the four blocks
(first, first), (first, second), (second, first) and (second, second). -/
private lemma sbs_double_sum_split4 {a b : ℕ} (F : Fin (a+b) → Fin (a+b) → ℝ) :
    (∑ x : Fin (a+b), ∑ y : Fin (a+b), F x y)
    = (∑ i₁ : Fin a, ∑ i₂ : Fin a, F (Fin.castAdd b i₁) (Fin.castAdd b i₂))
    + (∑ i₁ : Fin a, ∑ j₂ : Fin b, F (Fin.castAdd b i₁) (Fin.natAdd a j₂))
    + (∑ j₁ : Fin b, ∑ i₂ : Fin a, F (Fin.natAdd a j₁) (Fin.castAdd b i₂))
    + (∑ j₁ : Fin b, ∑ j₂ : Fin b, F (Fin.natAdd a j₁) (Fin.natAdd a j₂)) := by
  rw [Fin.sum_univ_add (f := fun x : Fin (a+b) => ∑ y : Fin (a+b), F x y)]
  have hA : (∑ i₁ : Fin a, ∑ y : Fin (a+b), F (Fin.castAdd b i₁) y)
      = (∑ i₁ : Fin a, ∑ i₂ : Fin a, F (Fin.castAdd b i₁) (Fin.castAdd b i₂))
        + (∑ i₁ : Fin a, ∑ j₂ : Fin b, F (Fin.castAdd b i₁) (Fin.natAdd a j₂)) := by
    calc
      (∑ i₁ : Fin a, ∑ y : Fin (a+b), F (Fin.castAdd b i₁) y)
          = ∑ i₁ : Fin a, ((∑ i₂ : Fin a, F (Fin.castAdd b i₁) (Fin.castAdd b i₂))
              + (∑ j₂ : Fin b, F (Fin.castAdd b i₁) (Fin.natAdd a j₂))) := by
            apply Finset.sum_congr rfl
            intro i₁ _
            exact Fin.sum_univ_add (a := a) (b := b)
              (f := fun y : Fin (a+b) => F (Fin.castAdd b i₁) y)
      _ = (∑ i₁ : Fin a, ∑ i₂ : Fin a, F (Fin.castAdd b i₁) (Fin.castAdd b i₂))
          + (∑ i₁ : Fin a, ∑ j₂ : Fin b, F (Fin.castAdd b i₁) (Fin.natAdd a j₂)) := by
            exact Finset.sum_add_distrib (s := Finset.univ)
  have hB : (∑ j₁ : Fin b, ∑ y : Fin (a+b), F (Fin.natAdd a j₁) y)
      = (∑ j₁ : Fin b, ∑ i₂ : Fin a, F (Fin.natAdd a j₁) (Fin.castAdd b i₂))
        + (∑ j₁ : Fin b, ∑ j₂ : Fin b, F (Fin.natAdd a j₁) (Fin.natAdd a j₂)) := by
    calc
      (∑ j₁ : Fin b, ∑ y : Fin (a+b), F (Fin.natAdd a j₁) y)
          = ∑ j₁ : Fin b, ((∑ i₂ : Fin a, F (Fin.natAdd a j₁) (Fin.castAdd b i₂))
              + (∑ j₂ : Fin b, F (Fin.natAdd a j₁) (Fin.natAdd a j₂))) := by
            apply Finset.sum_congr rfl
            intro j₁ _
            exact Fin.sum_univ_add (a := a) (b := b)
              (f := fun y : Fin (a+b) => F (Fin.natAdd a j₁) y)
      _ = (∑ j₁ : Fin b, ∑ i₂ : Fin a, F (Fin.natAdd a j₁) (Fin.castAdd b i₂))
          + (∑ j₁ : Fin b, ∑ j₂ : Fin b, F (Fin.natAdd a j₁) (Fin.natAdd a j₂)) := by
            exact Finset.sum_add_distrib (s := Finset.univ)
  calc
    (∑ i₁ : Fin a, ∑ y : Fin (a+b), F (Fin.castAdd b i₁) y)
        + (∑ i₁ : Fin b, ∑ y : Fin (a+b), F (Fin.natAdd a i₁) y)
        = (∑ i₁ : Fin a, ∑ i₂ : Fin a, F (Fin.castAdd b i₁) (Fin.castAdd b i₂))
          + (∑ i₁ : Fin a, ∑ j₂ : Fin b, F (Fin.castAdd b i₁) (Fin.natAdd a j₂))
          + (∑ j₁ : Fin b, ∑ i₂ : Fin a, F (Fin.natAdd a j₁) (Fin.castAdd b i₂))
          + (∑ j₁ : Fin b, ∑ j₂ : Fin b, F (Fin.natAdd a j₁) (Fin.natAdd a j₂)) := by
            rw [hA, hB]
            ring

/-- The ordered-distinct-pair sum over `Fin (a+b)` splits into the two
within-block pair sums plus the two cross-block sums (both orderings). -/
lemma pairSet_split {a b : ℕ} (g : Fin (a+b) → Fin (a+b) → ℝ) :
    (∑ p ∈ (Finset.univ.filter (fun p : Fin (a+b) × Fin (a+b) => p.1 ≠ p.2)), g p.1 p.2)
    = (∑ p ∈ (Finset.univ.filter (fun p : Fin a × Fin a => p.1 ≠ p.2)),
        g (Fin.castAdd b p.1) (Fin.castAdd b p.2))
    + (∑ p ∈ (Finset.univ.filter (fun p : Fin b × Fin b => p.1 ≠ p.2)),
        g (Fin.natAdd a p.1) (Fin.natAdd a p.2))
    + (∑ i₁ : Fin a, ∑ j₂ : Fin b, g (Fin.castAdd b i₁) (Fin.natAdd a j₂))
    + (∑ i₁ : Fin a, ∑ j₂ : Fin b, g (Fin.natAdd a j₂) (Fin.castAdd b i₁)) := by
  rw [sbs_sum_pairSet_eq_double]
  calc
    (∑ x : Fin (a+b), ∑ y : Fin (a+b), (if x ≠ y then g x y else 0))
        = (∑ i₁ : Fin a, ∑ i₂ : Fin a, (if Fin.castAdd b i₁ ≠ Fin.castAdd b i₂ then g (Fin.castAdd b i₁) (Fin.castAdd b i₂) else 0))
        + (∑ i₁ : Fin a, ∑ j₂ : Fin b, (if Fin.castAdd b i₁ ≠ Fin.natAdd a j₂ then g (Fin.castAdd b i₁) (Fin.natAdd a j₂) else 0))
        + (∑ j₁ : Fin b, ∑ i₂ : Fin a, (if Fin.natAdd a j₁ ≠ Fin.castAdd b i₂ then g (Fin.natAdd a j₁) (Fin.castAdd b i₂) else 0))
        + (∑ j₁ : Fin b, ∑ j₂ : Fin b, (if Fin.natAdd a j₁ ≠ Fin.natAdd a j₂ then g (Fin.natAdd a j₁) (Fin.natAdd a j₂) else 0)) := by
          exact sbs_double_sum_split4 (a := a) (b := b)
            (F := fun x y : Fin (a + b) => if x ≠ y then g x y else 0)
    _ = (∑ i₁ : Fin a, ∑ i₂ : Fin a, (if i₁ ≠ i₂ then g (Fin.castAdd b i₁) (Fin.castAdd b i₂) else 0))
        + (∑ i₁ : Fin a, ∑ j₂ : Fin b, g (Fin.castAdd b i₁) (Fin.natAdd a j₂))
        + (∑ i₁ : Fin a, ∑ j₂ : Fin b, g (Fin.natAdd a j₂) (Fin.castAdd b i₁))
        + (∑ j₁ : Fin b, ∑ j₂ : Fin b, (if j₁ ≠ j₂ then g (Fin.natAdd a j₁) (Fin.natAdd a j₂) else 0)) := by
          -- cross-guards vanish; within-block guards simplified by injectivity;
          -- the (second,first) block is reordered to the (i₁,j₂)-binder shape
          simp [Fin.castAdd_inj, Fin.natAdd_inj]
          rw [Finset.sum_comm]
    _ = (∑ p ∈ (Finset.univ.filter (fun p : Fin a × Fin a => p.1 ≠ p.2)),
        g (Fin.castAdd b p.1) (Fin.castAdd b p.2))
        + (∑ p ∈ (Finset.univ.filter (fun p : Fin b × Fin b => p.1 ≠ p.2)),
        g (Fin.natAdd a p.1) (Fin.natAdd a p.2))
        + (∑ i₁ : Fin a, ∑ j₂ : Fin b, g (Fin.castAdd b i₁) (Fin.natAdd a j₂))
        + (∑ i₁ : Fin a, ∑ j₂ : Fin b, g (Fin.natAdd a j₂) (Fin.castAdd b i₁)) := by
          rw [← sbs_sum_pairSet_eq_double (N := a) (g := fun i j => g (Fin.castAdd b i) (Fin.castAdd b j))]
          rw [← sbs_sum_pairSet_eq_double (N := b) (g := fun i j => g (Fin.natAdd a i) (Fin.natAdd a j))]
          ring

/-- If the pair kernel is nonnegative pointwise, the full ordered-pair sum is
at least the sum of the two within-block pair sums (dropping the two
nonnegative cross-block sums). -/
lemma pairSet_split_ge {a b : ℕ} {g : Fin (a+b) → Fin (a+b) → ℝ}
    (hg : ∀ p : Fin (a+b) × Fin (a+b), 0 ≤ g p.1 p.2) :
    (∑ p ∈ (Finset.univ.filter (fun p : Fin a × Fin a => p.1 ≠ p.2)),
        g (Fin.castAdd b p.1) (Fin.castAdd b p.2))
    + (∑ p ∈ (Finset.univ.filter (fun p : Fin b × Fin b => p.1 ≠ p.2)),
        g (Fin.natAdd a p.1) (Fin.natAdd a p.2))
    ≤ (∑ p ∈ (Finset.univ.filter (fun p : Fin (a+b) × Fin (a+b) => p.1 ≠ p.2)), g p.1 p.2) := by
  rw [pairSet_split (a := a) (b := b) g]
  have hc1 : 0 ≤ ∑ i₁ : Fin a, ∑ j₂ : Fin b, g (Fin.castAdd b i₁) (Fin.natAdd a j₂) := by
    exact Finset.sum_nonneg (fun i₁ _ => Finset.sum_nonneg
      (fun j₂ _ => hg (Fin.castAdd b i₁, Fin.natAdd a j₂)))
  have hc2 : 0 ≤ ∑ i₁ : Fin a, ∑ j₂ : Fin b, g (Fin.natAdd a j₂) (Fin.castAdd b i₁) := by
    exact Finset.sum_nonneg (fun i₁ _ => Finset.sum_nonneg
      (fun j₂ _ => hg (Fin.natAdd a j₂, Fin.castAdd b i₁)))
  linarith

/-! ## qLHSword diagonal densities and their block split -/

/-- The coordinate of the merged configuration on the first block is the
first-block coordinate. -/
lemma merge_castAdd_coord {N1 N2 : ℕ} (u : X N1) (w : X N2) (i : Fin N1) :
    mergeBlock N1 N2 (u, w) (Fin.castAdd N2 i) = u i := by
  simp [mergeBlock]

/-- The coordinate of the merged configuration on the second block is the
second-block coordinate. -/
lemma merge_natAdd_coord {N1 N2 : ℕ} (u : X N1) (w : X N2) (j : Fin N2) :
    mergeBlock N1 N2 (u, w) (Fin.natAdd N1 j) = w j := by
  simp [mergeBlock]

/-- The diagonal density of `qLHSword` (the parenthesised integrand). -/
noncomputable def qLHSden (N : ℕ) (ℓ μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ) (x : X N) : ℝ :=
  - μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i)) + (1 / 2 : ℝ) * (∑ p ∈ pairSet N, w (x p.1) (x p.2))

/-- The block-1 part of the qLHSword density (kinetic handled separately). -/
noncomputable def qLHSden1 {N1 N2 : ℕ} (ℓ μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ)
    (x : X (N1+N2)) : ℝ :=
  - μ * (∑ i1 : Fin N1, w1Fibre ℓ w1 (x (Fin.castAdd N2 i1)))
    + (1 / 2 : ℝ) * (∑ p ∈ pairSet N1, w (x (Fin.castAdd N2 p.1)) (x (Fin.castAdd N2 p.2)))

/-- The block-2 part of the qLHSword density. -/
noncomputable def qLHSden2 {N1 N2 : ℕ} (ℓ μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ)
    (x : X (N1+N2)) : ℝ :=
  - μ * (∑ j2 : Fin N2, w1Fibre ℓ w1 (x (Fin.natAdd N1 j2)))
    + (1 / 2 : ℝ) * (∑ p ∈ pairSet N2, w (x (Fin.natAdd N1 p.1)) (x (Fin.natAdd N1 p.2)))

/-- The cross-block part of the qLHSword density (both orderings; this is
dropped in the superadditivity direction since `w ≥ 0`). -/
noncomputable def qLHSdenCross {N1 N2 : ℕ} (w : ℝ³ → ℝ³ → ℝ) (x : X (N1+N2)) : ℝ :=
  (1 / 2 : ℝ) * (∑ i1 : Fin N1, ∑ j2 : Fin N2,
    (w (x (Fin.castAdd N2 i1)) (x (Fin.natAdd N1 j2))
      + w (x (Fin.natAdd N1 j2)) (x (Fin.castAdd N2 i1))))

/-- The full qLHSword density equals block1 + block2 + cross (exactly). -/
lemma qLHSden_split {N1 N2 : ℕ} (ℓ μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ) (x : X (N1+N2)) :
    qLHSden (N1+N2) ℓ μ w w1 x
      = qLHSden1 (N1 := N1) (N2 := N2) ℓ μ w w1 x
        + qLHSden2 (N1 := N1) (N2 := N2) ℓ μ w w1 x
        + qLHSdenCross (N1 := N1) (N2 := N2) w x := by
  simp only [qLHSden, qLHSden1, qLHSden2, qLHSdenCross, pairSet]
  rw [Fin.sum_univ_add (f := fun i : Fin (N1+N2) => w1Fibre ℓ w1 (x i))]
  rw [pairSet_split (a := N1) (b := N2) (g := fun i j : Fin (N1+N2) => w (x i) (x j))]
  -- recombine the two cross double sums into one double sum of sums
  have hI : (∑ i₁ : Fin N1, ∑ j₂ : Fin N2,
        (w (x (Fin.castAdd N2 i₁)) (x (Fin.natAdd N1 j₂))
          + w (x (Fin.natAdd N1 j₂)) (x (Fin.castAdd N2 i₁))))
      = (∑ i₁ : Fin N1, ∑ j₂ : Fin N2, w (x (Fin.castAdd N2 i₁)) (x (Fin.natAdd N1 j₂)))
        + (∑ i₁ : Fin N1, ∑ j₂ : Fin N2, w (x (Fin.natAdd N1 j₂)) (x (Fin.castAdd N2 i₁))) := by
        calc
          (∑ i₁ : Fin N1, ∑ j₂ : Fin N2,
              (w (x (Fin.castAdd N2 i₁)) (x (Fin.natAdd N1 j₂))
                + w (x (Fin.natAdd N1 j₂)) (x (Fin.castAdd N2 i₁))))
              = ∑ i₁ : Fin N1, ((∑ j₂ : Fin N2, w (x (Fin.castAdd N2 i₁)) (x (Fin.natAdd N1 j₂)))
                  + (∑ j₂ : Fin N2, w (x (Fin.natAdd N1 j₂)) (x (Fin.castAdd N2 i₁)))) := by
                apply Finset.sum_congr rfl
                intro i₁ _
                exact Finset.sum_add_distrib (s := Finset.univ)
          _ = (∑ i₁ : Fin N1, ∑ j₂ : Fin N2, w (x (Fin.castAdd N2 i₁)) (x (Fin.natAdd N1 j₂)))
              + (∑ i₁ : Fin N1, ∑ j₂ : Fin N2, w (x (Fin.natAdd N1 j₂)) (x (Fin.castAdd N2 i₁))) := by
                exact Finset.sum_add_distrib (s := Finset.univ)
  rw [hI]
  ring

/-- The cross-block density is nonnegative when the pair kernel is. -/
lemma qLHSdenCross_nonneg {N1 N2 : ℕ} {w : ℝ³ → ℝ³ → ℝ} (hw : ∀ x y : ℝ³, 0 ≤ w x y) :
    ∀ x : X (N1+N2), 0 ≤ qLHSdenCross (N1 := N1) (N2 := N2) w x := by
  intro x
  unfold qLHSdenCross
  have hsum : 0 ≤ ∑ i₁ : Fin N1, ∑ j₂ : Fin N2,
      (w (x (Fin.castAdd N2 i₁)) (x (Fin.natAdd N1 j₂))
        + w (x (Fin.natAdd N1 j₂)) (x (Fin.castAdd N2 i₁))) := by
    exact Finset.sum_nonneg (fun i₁ _ => Finset.sum_nonneg (fun j₂ _ =>
      add_nonneg (hw _ _) (hw _ _)))
  exact mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) hsum

/-- The two within-block densities together are bounded by the full qLHSword
density (dropping the nonnegative cross-block part). -/
lemma qLHSden_blocks_le {N1 N2 : ℕ} (ℓ μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ)
    (hw : ∀ x y : ℝ³, 0 ≤ w x y) (x : X (N1+N2)) :
    qLHSden1 (N1 := N1) (N2 := N2) ℓ μ w w1 x
      + qLHSden2 (N1 := N1) (N2 := N2) ℓ μ w w1 x
      ≤ qLHSden (N1+N2) ℓ μ w w1 x := by
  have hs := qLHSden_split (N1 := N1) (N2 := N2) ℓ μ w w1 x
  have hc : 0 ≤ qLHSdenCross (N1 := N1) (N2 := N2) w x := qLHSdenCross_nonneg hw x
  linarith

/-- Block-1 density at a merged configuration equals the full density of the
first-block configuration. -/
lemma qLHSden1_merge {N1 N2 : ℕ} (ℓ μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ) (u : X N1) (wv : X N2) :
    qLHSden1 (N1 := N1) (N2 := N2) ℓ μ w w1 (mergeBlock N1 N2 (u, wv))
      = qLHSden N1 ℓ μ w w1 u := by
  simp [qLHSden1, qLHSden, merge_castAdd_coord]

/-- Block-2 density at a merged configuration equals the full density of the
second-block configuration. -/
lemma qLHSden2_merge {N1 N2 : ℕ} (ℓ μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ) (u : X N1) (wv : X N2) :
    qLHSden2 (N1 := N1) (N2 := N2) ℓ μ w w1 (mergeBlock N1 N2 (u, wv))
      = qLHSden N2 ℓ μ w w1 wv := by
  simp [qLHSden2, qLHSden, merge_natAdd_coord]

/-! ## The small-box energy and its block parts -/

/-- The corpus small-box analysis energy at scale `s` (the object whose
lower bound is `SmallBoxQ0.smallBoxEnergy_fs_form`): kinetic word plus the
`μ`-potential word. -/
noncomputable def sboxE (N : ℕ) (s μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ) (Φ : X N → ℝ) : ℝ :=
  kinWord N s Φ + qLHSword (N := N) s μ w w1 Φ

/-- The block-1 part of the small-box energy (particles `Fin N1` embedded by
`Fin.castAdd N2`), as an expectation over the full box. -/
noncomputable def sboxE1 {N1 N2 : ℕ} (s μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ)
    (Φ : X (N1+N2) → ℝ) : ℝ :=
  (∑ i₁ : Fin N1, ∑ k : Fin 3, ∫ x in abox (N1+N2) s,
      (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.castAdd N2 i₁) k)) ^ 2)
  + ∫ x in abox (N1+N2) s, (Φ x) ^ 2 * qLHSden1 (N1 := N1) (N2 := N2) s μ w w1 x

/-- The block-2 part of the small-box energy (particles `Fin N2` embedded by
`Fin.natAdd N1`). -/
noncomputable def sboxE2 {N1 N2 : ℕ} (s μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ)
    (Φ : X (N1+N2) → ℝ) : ℝ :=
  (∑ j₂ : Fin N2, ∑ k : Fin 3, ∫ x in abox (N1+N2) s,
      (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.natAdd N1 j₂) k)) ^ 2)
  + ∫ x in abox (N1+N2) s, (Φ x) ^ 2 * qLHSden2 (N1 := N1) (N2 := N2) s μ w w1 x

/-- The kinetic word splits into the two particle blocks. -/
lemma kinWord_block_split {N1 N2 : ℕ} (s : ℝ) (Φ : X (N1+N2) → ℝ) :
    kinWord (N1+N2) s Φ
      = (∑ i₁ : Fin N1, ∑ k : Fin 3, ∫ x in abox (N1+N2) s,
          (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.castAdd N2 i₁) k)) ^ 2)
        + (∑ j₂ : Fin N2, ∑ k : Fin 3, ∫ x in abox (N1+N2) s,
          (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.natAdd N1 j₂) k)) ^ 2) := by
  unfold kinWord
  rw [Fin.sum_univ_add (f := fun i : Fin (N1+N2) => ∑ k : Fin 3,
      ∫ x in abox (N1+N2) s, (fderiv ℝ Φ x (kcDir (N1+N2) i k)) ^ 2)]

/-- `qLHSword` is the integral of `(Φx)²` against the diagonal density
`qLHSden`. -/
lemma qLHSword_eq_integral_qLHSden (N : ℕ) (s μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ)
    (Φ : X N → ℝ) :
    qLHSword (N := N) s μ w w1 Φ = ∫ x in abox N s, (Φ x) ^ 2 * qLHSden N s μ w w1 x := by
  rfl

/-- The squared-`L²`-norm of a state over the full centred box equals the
integral over the second block of the squared norms of the first-block
slices (Fubini along the block split). -/
lemma slice_norm_integral {N1 N2 : ℕ} {s : ℝ} (hs : 0 < s) {Φ : X (N1+N2) → ℝ}
    (hΦ : Continuous Φ) :
    (∫ w in abox N2 s, ∫ u in abox N1 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2)
      = ∫ x in abox (N1+N2) s, (Φ x) ^ 2 := by
  have hG : IntegrableOn (fun x : X (N1+N2) => (Φ x) ^ 2) (abox (N1+N2) s) volume :=
    integrableOn_abox_of_continuous hs (hΦ.pow 2)
  exact (aboxFubini_swapped (N1 := N1) (N2 := N2) s (fun x : X (N1+N2) => (Φ x) ^ 2) hG)

/-- The first-block slice of a smooth `(N1+N2)`-particle state at frozen
second-block configuration `w` (matches `EneuSuperadd.es_slice1`). -/
noncomputable def sbs_slice {N1 N2 : ℕ} (Φ : X (N1+N2) → ℝ) (w : X N2) : X N1 → ℝ :=
  fun u => Φ (mergeBlock N1 N2 (u, w))

/-- The second-block slice of a smooth `(N1+N2)`-particle state at frozen
first-block configuration `u`. -/
noncomputable def sbs_slice2 {N1 N2 : ℕ} (Φ : X (N1+N2) → ℝ) (u : X N1) : X N2 → ℝ :=
  fun w => Φ (mergeBlock N1 N2 (u, w))

/-- Slice integral identity for the potential part of the block-1 energy:
the expectation of the block-1 diagonal density over the full box equals the
integral (over the frozen second block) of the `qLHSword` of the slices. -/
lemma qLHSden1_expect_eq_slice {N1 N2 : ℕ} {s μ : ℝ} (w w1 : ℝ³ → ℝ³ → ℝ)
    (Φ : X (N1+N2) → ℝ)
    (hG : IntegrableOn (fun x : X (N1+N2) => (Φ x) ^ 2 *
        qLHSden1 (N1 := N1) (N2 := N2) s μ w w1 x) (abox (N1+N2) s) volume) :
    (∫ x in abox (N1+N2) s, (Φ x) ^ 2 * qLHSden1 (N1 := N1) (N2 := N2) s μ w w1 x)
      = ∫ wv in abox N2 s, qLHSword (N := N1) s μ w w1 (sbs_slice Φ wv) := by
  have hF := aboxFubini_swapped (N1 := N1) (N2 := N2) s
    (fun x : X (N1+N2) => (Φ x) ^ 2 * qLHSden1 (N1 := N1) (N2 := N2) s μ w w1 x) hG
  calc
    (∫ x in abox (N1+N2) s, (Φ x) ^ 2 * qLHSden1 (N1 := N1) (N2 := N2) s μ w w1 x)
        = ∫ wv in abox N2 s, ∫ u in abox N1 s,
            (Φ (mergeBlock N1 N2 (u, wv))) ^ 2
              * qLHSden1 (N1 := N1) (N2 := N2) s μ w w1 (mergeBlock N1 N2 (u, wv)) := hF.symm
    _ = ∫ wv in abox N2 s, ∫ u in abox N1 s,
        (sbs_slice Φ wv u) ^ 2 * qLHSden N1 s μ w w1 u := by
          apply integral_congr_ae
          filter_upwards with wv
          apply integral_congr_ae
          filter_upwards with u
          rw [qLHSden1_merge (N1 := N1) (N2 := N2) s μ w w1 u wv]
          rfl
    _ = ∫ wv in abox N2 s, qLHSword (N := N1) s μ w w1 (sbs_slice Φ wv) := by
          apply integral_congr_ae
          filter_upwards with wv
          exact (qLHSword_eq_integral_qLHSden (N := N1) s μ w w1 (sbs_slice Φ wv)).symm

end BoseGases

end Submission
