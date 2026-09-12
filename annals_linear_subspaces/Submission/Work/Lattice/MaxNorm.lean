import Mathlib
import Submission.Work.Lattice.FlowRateAsymptotic

/-!
# The sup norm on Plücker coordinates and its behaviour under the diagonal flow

The paper (de Saxcé, §3) deliberately uses the **max norm** on `⋀^k ℝᵈ`,
`‖x‖ = max_I |x_I|` (coordinates in the standard basis `e_I`), instead of the Euclidean norm:
"the behaviour of that norm with respect to differentiation is particularly simple".  The reason
is that a diagonal flow acts on the coordinate `x_I` by the *product* of its diagonal
coefficients, so with the max norm the flow of a `k`-vector has the exact value

    ‖⋀^k a_t w‖_max = max_u ( exp (t·σ_u) · ‖blockElem w u‖_max ),

a max of *finitely many exponentials* (hence piecewise affine in `t`), whose right derivative at
`t = 0⁺` is `σ_{u*}` where `u*` is the largest block index achieving the maximum.  With the
Euclidean norm the same derivative is the weighted average `Σ_u σ_u ‖block_u w‖²/‖w‖²`, which does
not even see the position.

This module provides the coordinate sup norm (`cnorm`), its basic API, the coordinate formula for
a diagonally flowed `k`-vector, and the exact flow identity (`cnorm_map_flow`).
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.WedgeBlocks

namespace Submission.MaxNorm

variable {d : ℕ}

/-- The index set `IDX d k = Set.powersetCard (Fin d) k` is nonempty for `k ≤ d`. -/
lemma idx_nonempty {k : ℕ} (hk : k ≤ d) : (Finset.univ : Finset (IDX d k)).Nonempty :=
  ⟨⟨Finset.univ.filter (fun i : Fin d => i.val < k), by
      simp only [Set.powersetCard, Set.mem_ofPred_eq]
      exact Submission.FlowLattice.card_filter_val_lt (d := d) (ℓ := k) hk⟩,
    Finset.mem_univ _⟩

/-- The sup norm on the Plücker coordinates of a `k`-vector: the paper's norm on `⋀^k ℝᵈ`. -/
def cnorm {k : ℕ} (hk : k ≤ d) (w : WK d k) : ℝ :=
  (Finset.univ : Finset (IDX d k)).sup' (idx_nonempty hk)
    (fun I => |wcoord (d := d) (k := k) w I|)

lemma le_cnorm {k : ℕ} (hk : k ≤ d) (w : WK d k) (I : IDX d k) :
    |wcoord (d := d) (k := k) w I| ≤ cnorm hk w :=
  Finset.le_sup' (fun I => |wcoord (d := d) (k := k) w I|) (Finset.mem_univ I)

lemma cnorm_nonneg {k : ℕ} (hk : k ≤ d) (w : WK d k) : 0 ≤ cnorm hk w :=
  le_trans (abs_nonneg _) (le_cnorm hk w (idx_nonempty hk).choose)

lemma cnorm_le_of_forall {k : ℕ} (hk : k ≤ d) (w : WK d k) {M : ℝ}
    (h : ∀ I : IDX d k, |wcoord (d := d) (k := k) w I| ≤ M) : cnorm hk w ≤ M :=
  Finset.sup'_le _ _ (fun I _ => h I)

lemma cnorm_zero {k : ℕ} (hk : k ≤ d) : cnorm hk (0 : WK d k) = 0 := by
  refine le_antisymm (cnorm_le_of_forall hk 0 (fun I => by simp)) (cnorm_nonneg hk 0)

/-- The sup norm vanishes exactly on the zero vector. -/
lemma cnorm_eq_zero_iff {k : ℕ} (hk : k ≤ d) (w : WK d k) : cnorm hk w = 0 ↔ w = 0 := by
  constructor
  · intro h
    refine wk_ext (fun I => ?_)
    rw [wcoord_zero]
    have h1 : |wcoord (d := d) (k := k) w I| ≤ cnorm hk w := le_cnorm hk w I
    rw [h] at h1
    exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
  · intro h
    rw [h]
    exact cnorm_zero hk

lemma cnorm_pos_of_ne_zero {k : ℕ} (hk : k ≤ d) (w : WK d k) (hw : w ≠ 0) :
    0 < cnorm hk w := by
  rcases lt_or_eq_of_le (cnorm_nonneg hk w) with h | h
  · exact h
  · exact absurd ((cnorm_eq_zero_iff hk w).mp h.symm) hw

/-! ## Coordinates of a diagonally flowed vector -/

/-- The coordinates of a standard basis vector form a Dirac delta. -/
lemma wcoord_basis {k : ℕ} (J I : IDX d k) :
    wcoord (d := d) (k := k) (((Bk d k) J) : WK d k) I = if I = J then 1 else 0 := by
  rw [wcoord_eq_inner]
  exact basis_inner_dirac I J

/-- Coordinates are additive over finite linear combinations. -/
lemma wcoord_sum {k : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ) (x : ι → WK d k)
    (I : IDX d k) :
    wcoord (d := d) (k := k) (s.sum (fun i => c i • x i)) I =
      s.sum (fun i => c i * wcoord (d := d) (k := k) (x i) I) := by
  classical
  induction s using Finset.induction with
  | empty => simp [wcoord]
  | insert a s hnot ih => simp [Finset.sum_insert hnot, wcoord_add, wcoord_smul, ih]

/-- **Coordinate formula for a diagonal flow**: the Plücker coordinate at `I` is multiplied by
the product of the diagonal coefficients over `I`. -/
lemma wcoord_map_scaleMap {k : ℕ} (s : Fin d → ℝ) (w : WK d k) (I : IDX d k) :
    wcoord (d := d) (k := k) (exteriorPower.map k (scaleMap s) w) I =
      ((I : Finset (Fin d)).prod s) * wcoord (d := d) (k := k) w I := by
  classical
  have hsum : exteriorPower.map k (scaleMap s) w =
      (Finset.univ : Finset (IDX d k)).sum (fun J =>
        (wcoord (d := d) (k := k) w J * ((J : Finset (Fin d)).prod s)) •
          (((Bk d k) J) : WK d k)) := by
    conv_lhs => rw [← sum_wcoord_smul_basis (d := d) (k := k) w]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [map_smul, map_scaleMap_basis, smul_smul, mul_comm]
  rw [hsum, wcoord_sum]
  rw [Finset.sum_eq_single I]
  · rw [wcoord_basis I I, if_pos rfl, mul_one]
    ring
  · intro J _ hJI
    rw [wcoord_basis J I]
    have hne : ¬ (I = J) := fun h => hJI h.symm
    rw [if_neg hne, mul_zero]
  · intro hnot
    exact absurd (Finset.mem_univ I) hnot

/-- The coordinate formula in exponential-flow form: for a subset `I` with `u` indices `≥ ℓ` the
flow multiplies the coordinate by `exp (t·σ_u)`. -/
lemma wcoord_map_flow {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (t : ℝ) (w : WK d k) {u : ℕ}
    (hu : u ≤ k) (I : IDX d k)
    (hI : ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card = u) :
    wcoord (d := d) (k := k)
        (exteriorPower.map k
          (scaleMap (twoScale (Real.exp (-t / ↑ℓ)) (Real.exp (t / ↑(d - ℓ))) ℓ)) w) I =
      Real.exp (t * Submission.FlowRateAsymptotic.sig (d := d) k ℓ u) *
        wcoord (d := d) (k := k) w I := by
  rw [wcoord_map_scaleMap,
    twoScale_prod (d := d) (Real.exp (-t / ↑ℓ)) (Real.exp (t / ↑(d - ℓ))) ℓ
      (I : Finset (Fin d)) k u (show (I : Finset (Fin d)).card = k from I.2) hI,
    Submission.FlowRate.eigen_exp (d := d) (k := k) (u := u) (ℓ := ℓ) hℓ0 hℓd t,
    Submission.FlowRateAsymptotic.sig_eq_eigen (d := d) hℓ0 hℓd hu]

/-! ## The exact flow identity for the sup norm -/

/-- `blockElem` vanishes on empty blocks. -/
lemma blockElem_of_blockFinset_eq_empty {k ℓ u : ℕ} (w : WK d k)
    (h : blockFinset (d := d) (k := k) (ℓ := ℓ) u = ∅) :
    blockElem (d := d) (k := k) (ℓ := ℓ) w u = 0 := by
  rw [blockElem, h, Finset.sum_empty]

/-- The number of high indices of a `k`-subset is at most `k`. -/
lemma card_filter_high_le {k ℓ : ℕ} (I : IDX d k) :
    ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card ≤ k :=
  calc ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card
      ≤ (I : Finset (Fin d)).card := Finset.card_filter_le _ _
    _ = k := I.2

/-- The sup norm of a block is the supremum of the coordinates inside the block. -/
lemma cnorm_blockElem_eq_sup' {k ℓ u : ℕ} (hk : k ≤ d) (w : WK d k)
    (hne : (blockFinset (d := d) (k := k) (ℓ := ℓ) u).Nonempty) :
    cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u) =
      (blockFinset (d := d) (k := k) (ℓ := ℓ) u).sup' hne
        (fun I => |wcoord (d := d) (k := k) w I|) := by
  refine le_antisymm ?_ ?_
  · refine cnorm_le_of_forall hk _ (fun I => ?_)
    rw [wcoord_blockElem]
    by_cases hI : I ∈ blockFinset (d := d) (k := k) (ℓ := ℓ) u
    · rw [if_pos hI]
      exact Finset.le_sup' (fun I => |wcoord (d := d) (k := k) w I|) hI
    · rw [if_neg hI, abs_zero]
      exact le_trans (abs_nonneg _)
        (Finset.le_sup' (fun I => |wcoord (d := d) (k := k) w I|) hne.choose_spec)
  · refine Finset.sup'_le _ _ (fun I hI => ?_)
    have h1 : wcoord (d := d) (k := k) (blockElem (d := d) (k := k) (ℓ := ℓ) w u) I =
        wcoord (d := d) (k := k) w I := by
      rw [wcoord_blockElem, if_pos hI]
    rw [← h1]
    exact le_cnorm hk _ I

/-- **Upper half of the exact flow identity** for the sup norm: the sup norm of the flowed
`k`-vector is at most the maximum over blocks of the eigenvalue times the block's sup norm. -/
lemma cnorm_map_flow_le {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (t : ℝ) (hk : k ≤ d)
    (w : WK d k) :
    cnorm hk (exteriorPower.map k
        (scaleMap (twoScale (Real.exp (-t / ↑ℓ)) (Real.exp (t / ↑(d - ℓ))) ℓ)) w) ≤
      (Finset.range (k + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩
        (fun u => Real.exp (t * Submission.FlowRateAsymptotic.sig (d := d) k ℓ u) *
          cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u)) := by
  refine cnorm_le_of_forall hk _ (fun I => ?_)
  have hIle : ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card ≤ k :=
    card_filter_high_le I
  have hIrange : ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card ∈
      Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hIle)
  rw [wcoord_map_flow (d := d) hℓ0 hℓd t w hIle I rfl, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (le_of_lt (Real.exp_pos _)))
    (Finset.le_sup' (fun u => Real.exp (t * Submission.FlowRateAsymptotic.sig (d := d) k ℓ u) *
      cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u)) hIrange)
  have hmem : I ∈ blockFinset (d := d) (k := k) (ℓ := ℓ)
      ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card := by
    simp [blockFinset]
  have h1 : wcoord (d := d) (k := k)
      (blockElem (d := d) (k := k) (ℓ := ℓ) w
        ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card) I =
      wcoord (d := d) (k := k) w I := by
    rw [wcoord_blockElem, if_pos hmem]
  rw [← h1]
  exact le_cnorm hk _ I

/-- **Lower half of the exact flow identity** for the sup norm: the maximum over blocks of the
eigenvalue times the block's sup norm is attained by the flowed vector. -/
lemma cnorm_map_flow_ge {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (t : ℝ) (hk : k ≤ d)
    (w : WK d k) :
    (Finset.range (k + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩
      (fun u => Real.exp (t * Submission.FlowRateAsymptotic.sig (d := d) k ℓ u) *
        cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u)) ≤
    cnorm hk (exteriorPower.map k
      (scaleMap (twoScale (Real.exp (-t / ↑ℓ)) (Real.exp (t / ↑(d - ℓ))) ℓ)) w) := by
  obtain ⟨u₀, -, hu₀eq⟩ := Finset.exists_mem_eq_sup'
    (⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩ :
      (Finset.range (k + 1)).Nonempty)
    (fun u => Real.exp (t * Submission.FlowRateAsymptotic.sig (d := d) k ℓ u) *
      cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u))
  rw [hu₀eq]
  by_cases hb : (blockFinset (d := d) (k := k) (ℓ := ℓ) u₀).Nonempty
  · obtain ⟨I₀, hI₀mem, hI₀eq⟩ := Finset.exists_mem_eq_sup' hb
      (fun I => |wcoord (d := d) (k := k) w I|)
    have hcard : ((I₀ : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card = u₀ := by
      simpa [blockFinset] using hI₀mem
    have hsup : cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u₀) =
        |wcoord (d := d) (k := k) w I₀| := by
      rw [cnorm_blockElem_eq_sup' hk w hb, hI₀eq]
    calc Real.exp (t * Submission.FlowRateAsymptotic.sig (d := d) k ℓ u₀) *
          cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u₀)
        = |Real.exp (t * Submission.FlowRateAsymptotic.sig (d := d) k ℓ u₀) *
            wcoord (d := d) (k := k) w I₀| := by
          rw [hsup, abs_mul, abs_of_pos (Real.exp_pos _)]
      _ = |wcoord (d := d) (k := k)
            (exteriorPower.map k
              (scaleMap (twoScale (Real.exp (-t / ↑ℓ)) (Real.exp (t / ↑(d - ℓ))) ℓ)) w) I₀| := by
          rw [wcoord_map_flow (d := d) (k := k) (ℓ := ℓ) (u := u₀)
            hℓ0 hℓd t w (by rw [← hcard]; exact card_filter_high_le I₀) I₀ hcard]
      _ ≤ cnorm hk (exteriorPower.map k
            (scaleMap (twoScale (Real.exp (-t / ↑ℓ)) (Real.exp (t / ↑(d - ℓ))) ℓ)) w) :=
          le_cnorm hk _ I₀
  · rw [blockElem_of_blockFinset_eq_empty w (Finset.not_nonempty_iff_eq_empty.mp hb),
      cnorm_zero, mul_zero]
    exact cnorm_nonneg hk _

/-- **The exact flow identity for the paper's norm**: the sup norm of a flowed `k`-vector is
the maximum over blocks of `exp (t·σ_u)` times the block's sup norm. -/
theorem cnorm_map_flow {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (t : ℝ) (hk : k ≤ d)
    (w : WK d k) :
    cnorm hk (exteriorPower.map k
        (scaleMap (twoScale (Real.exp (-t / ↑ℓ)) (Real.exp (t / ↑(d - ℓ))) ℓ)) w) =
      (Finset.range (k + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩
        (fun u => Real.exp (t * Submission.FlowRateAsymptotic.sig (d := d) k ℓ u) *
          cnorm hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u)) :=
  le_antisymm (cnorm_map_flow_le hℓ0 hℓd t hk w) (cnorm_map_flow_ge hℓ0 hℓd t hk w)

end Submission.MaxNorm
