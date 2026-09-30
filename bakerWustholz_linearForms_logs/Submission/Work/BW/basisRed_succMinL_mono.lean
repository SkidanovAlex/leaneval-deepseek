import Mathlib
import Submission.Work.BW.basisRed_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Monotonicity of the successive minima `succMinL` in the index

`Work.BW.succMinL F j` is the `j`-th successive minimum of `ℤⁿ` with respect to the unit ball
of `F` (see `Submission.Work.BW.basisRed_defs`).  It is the infimum over the levels `t` for
which the `ℝ`-span of the lattice points of `F`-norm at most `t` has dimension at least `j`.

Enlarging `j` shrinks the set of admissible levels, so the infimum can only increase; this file
proves that `succMinL F ·` is monotone, which is used when comparing successive minima of
different indices.  The auxiliary objects are the span `succSpanL F t` of the lattice points of
norm at most `t` and the set `succSetL F j` of levels whose span has dimension at least `j`;
by definition `succMinL F j = sInf (succSetL F j)`.

The only hypotheses really used are the nonnegativity and finiteness of `F`; in particular the
statement holds for any `F` satisfying `IsLatticeNorm`.
-/

namespace Work.BW

variable {n : ℕ}

/-- The `ℝ`-span of the lattice points of `F`-norm at most `t`. -/
noncomputable def basisRed_succSpanL (F : (Fin n → ℝ) → ℝ) (t : ℝ) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ {x : Fin n → ℝ | (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ F x ≤ t}

/-- The set of levels `t` for which the span of the lattice points of `F`-norm at most `t` has
dimension at least `j`.  Its infimum is `succMinL F j`. -/
noncomputable def basisRed_succSetL (F : (Fin n → ℝ) → ℝ) (j : ℕ) : Set ℝ :=
  {t : ℝ | j ≤ Module.finrank ℝ (basisRed_succSpanL F t)}

/-- `succMinL` is the infimum of `basisRed_succSetL`, by definition. -/
theorem basisRed_succMinL_eq_sInf (F : (Fin n → ℝ) → ℝ) (j : ℕ) :
    succMinL F j = sInf (basisRed_succSetL F j) := rfl

/-- Enlarging the index shrinks `basisRed_succSetL`. -/
theorem basisRed_succSetL_antitone {F : (Fin n → ℝ) → ℝ} {i j : ℕ} (hij : i ≤ j) :
    basisRed_succSetL F j ⊆ basisRed_succSetL F i := fun _ ht => le_trans hij ht

/-- Below the level `0` the spanning set is empty, so the span is trivial: for `1 ≤ k` every
level in `basisRed_succSetL F k` is nonnegative. -/
theorem basisRed_succSetL_nonneg {F : (Fin n → ℝ) → ℝ} (hF : IsLatticeNorm F) {k : ℕ}
    (hk : 1 ≤ k) {t : ℝ} (ht : t ∈ basisRed_succSetL F k) : 0 ≤ t := by
  by_contra h
  rw [not_le] at h
  have hempty : {x : Fin n → ℝ | (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ F x ≤ t} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨-, hx⟩
    have hx0 := hF.nonneg x
    linarith
  have hbot : basisRed_succSpanL F t = ⊥ := by
    rw [basisRed_succSpanL, hempty, Submodule.span_empty]
  have hfr : Module.finrank ℝ (basisRed_succSpanL F t) = 0 := by rw [hbot, finrank_bot]
  change k ≤ Module.finrank ℝ (basisRed_succSpanL F t) at ht
  omega

/-- The span of the standard basis vectors of `ℝⁿ` is everything. -/
theorem basisRed_span_single_one_eq_top (n : ℕ) :
    Submodule.span ℝ (Set.range (fun k : Fin n => (Pi.single k (1:ℝ) : Fin n → ℝ))) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  rw [← Finset.univ_sum_single x]
  apply Submodule.sum_mem
  intro k _
  rw [show (Pi.single k (x k) : Fin n → ℝ) = (x k) • (Pi.single k (1:ℝ) : Fin n → ℝ) by
    ext i; simp [Pi.single_apply]]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- For `j ≤ n` the set `basisRed_succSetL F j` is nonempty: the level
`∑ k, F (e_k)` is large enough that the span of the lattice points of norm at most it contains
all the standard basis vectors. -/
theorem basisRed_succSetL_nonempty {F : (Fin n → ℝ) → ℝ} (hF : IsLatticeNorm F) {j : ℕ}
    (hj : j ≤ n) : (basisRed_succSetL F j).Nonempty := by
  set t : ℝ := ∑ k : Fin n, F (Pi.single k (1:ℝ) : Fin n → ℝ) with ht
  refine ⟨t, ?_⟩
  have hgen : ∀ k : Fin n, (Pi.single k (1:ℝ) : Fin n → ℝ) ∈ basisRed_succSpanL F t := by
    intro k
    refine Submodule.subset_span ⟨?_, ?_⟩
    · exact ⟨(Pi.single k (1:ℤ) : Fin n → ℤ), by ext i; simp [Pi.single_apply]⟩
    · rw [ht]
      have hs := Finset.single_le_sum
        (f := fun x : Fin n => F (Pi.single x (1:ℝ) : Fin n → ℝ))
        (fun i _ => hF.nonneg _) (Finset.mem_univ k)
      simpa using hs
  have htop : (⊤ : Submodule ℝ (Fin n → ℝ)) ≤ basisRed_succSpanL F t := by
    rw [← basisRed_span_single_one_eq_top n, Submodule.span_le]
    rintro x ⟨k, rfl⟩
    exact hgen k
  have hfin := Submodule.finrank_mono htop
  rw [finrank_top, Module.finrank_fin_fun] at hfin
  change j ≤ Module.finrank ℝ (basisRed_succSpanL F t)
  exact le_trans hj hfin

/-- The `0`-th successive minimum is `0`: the condition `0 ≤ dim` is vacuous. -/
theorem basisRed_succMinL_zero (F : (Fin n → ℝ) → ℝ) : succMinL F 0 = 0 := by
  have hA : basisRed_succSetL F 0 = Set.univ := Set.eq_univ_of_forall (fun t => Nat.zero_le _)
  rw [basisRed_succMinL_eq_sInf, hA, csInf_of_not_bddBelow not_bddBelow_univ, Real.sInf_empty]

theorem basisRed_succMinL_mono {n : ℕ} {F : (Fin n → ℝ) → ℝ} (hF : Work.BW.IsLatticeNorm F)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    Work.BW.succMinL F i ≤ Work.BW.succMinL F j := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    rw [basisRed_succMinL_zero F]
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0; rw [basisRed_succMinL_zero F]
    · rw [basisRed_succMinL_eq_sInf]
      exact le_csInf (basisRed_succSetL_nonempty hF hj)
        (fun b hb => basisRed_succSetL_nonneg hF hjpos hb)
  · rw [basisRed_succMinL_eq_sInf, basisRed_succMinL_eq_sInf]
    exact csInf_le_csInf ⟨0, fun t ht => basisRed_succSetL_nonneg hF hi ht⟩
      (basisRed_succSetL_nonempty hF hj) (basisRed_succSetL_antitone hij)

end Work.BW
