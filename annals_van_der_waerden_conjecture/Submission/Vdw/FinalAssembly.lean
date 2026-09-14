import Mathlib
import Submission.Vdw.CaseIDirectAssembly
import Submission.Vdw.CaseIFourier
import Submission.Vdw.PrimitiveCase

open Polynomial Asymptotics
open scoped BigOperators
open Filter
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Final assembly of `theorem_1`: the exact remaining obligations

This module performs the bookkeeping that reduces the challenge statement

    `(fun H ↦ (E n H : ℝ)) =O[atTop] (fun H ↦ (H^(n-1) : ℝ))`   (`n ≥ 3`)

to FOUR explicit region bounds, all of them the genuinely research-level inputs
of Bhargava's paper (Annals 2025, Theorem 1):

* `SubcaseI_P1resid` — the Case-I slice `H < C_f ≤ H^(1+δ)`,
  `D_f > H^(2+2δ)`;
* `SubcaseI_P2` — `D_f ≤ H^(2+2δ)` (Case II: counting number fields of bounded
  discriminant — Schmidt, Lemke Oliver–Thorne; exact counts for `n = 4, 5`);
* `SubcaseI_P3` — `C_f > H^(1+δ)` (Case III subcase (i): the same Case-I
  argument with an intermediate divisor `B ∈ [H^(1+δ/2), H^(1+δ)]`);
* `ImprimitiveBad` — imprimitive Galois group (Widmer's bound
  `O(H^(n/2+2))`; `≤ H^(n-1)` only for `n ≥ 6`, small `n` needs separate
  treatment).

Both Case-I slices (`SubcaseI_P1resid` and `SubcaseI_P3`) are discharged from
the §4 Fourier input in `FourierDequi` (`theorem_1_of_dequi_three`,
`theorem_1_of_dequi_one_prime`), where the input is the paper's Corollary
`Dequi2` (`DequiBound`); this module still contains the *elementary* half of
the split (`SubcaseI_direct_isBigO` is unconditional).

Everything else is done: the reducible half (`redBox_isBigO`), the
primitive/`DD = 0`/subcase-(ii) slice (`PrimBadCaseIII_isBigO`), and the
elementary part `SubcaseI_direct` of the Case-I slice
(`SubcaseI_direct_isBigO`).

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-- **Case-I residual slice of `SubcaseI`**: `H < C_f ≤ H^(1+δ)`,
`D_f > H^(2+2δ)`. -/
def SubcaseI_P1resid (n H : ℕ) : Set ℤ[X] :=
  {f | f ∈ SubcaseI n H ∧ ∃ h : Irreducible (f.map φℚ),
      (radical (fieldDiscExp f h) : ℝ) ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) ∧
      H < radical (fieldDiscExp f h) ∧
      (H : ℝ) ^ (2 + 1 / (n : ℝ)) < (fieldDiscExp f h : ℝ)}

/-- **Case-II slice of `SubcaseI`**: `D_f ≤ H^(2+2δ)`. -/
def SubcaseI_P2 (n H : ℕ) : Set ℤ[X] :=
  {f | f ∈ SubcaseI n H ∧ ∃ h : Irreducible (f.map φℚ),
      (fieldDiscExp f h : ℝ) ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ))}

/-- **Case-III-subcase-(i) slice of `SubcaseI`**: `C_f > H^(1+δ)`. -/
def SubcaseI_P3 (n H : ℕ) : Set ℤ[X] :=
  {f | f ∈ SubcaseI n H ∧ ∃ h : Irreducible (f.map φℚ),
      (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) < (radical (fieldDiscExp f h) : ℝ)}

/-- If `f ≤ g` eventually and both are eventually nonnegative, then
`f =O[atTop] g`. -/
lemma isBigO_of_eventually_le_real {f g : ℕ → ℝ} (hf : ∀ᶠ H : ℕ in atTop, 0 ≤ f H)
    (hg : ∀ᶠ H : ℕ in atTop, 0 ≤ g H) (h : ∀ᶠ H : ℕ in atTop, f H ≤ g H) :
    f =O[atTop] g :=
  IsBigO.of_bound 1 (by
    filter_upwards [h, hf, hg] with H h1 h2 h3
    rw [Real.norm_of_nonneg h2, Real.norm_of_nonneg h3, one_mul]
    exact h1)

/-- **Cover of `SubcaseI`** by the elementary Case-I slice and the three
residual slices. -/
theorem SubcaseI_subset_cover (n H : ℕ) :
    SubcaseI n H ⊆ SubcaseI_direct n H ∪ SubcaseI_P1resid n H ∪
      SubcaseI_P2 n H ∪ SubcaseI_P3 n H := by
  intro f hf
  have hf' : f ∈ SubcaseI n H := hf
  obtain ⟨_, h, _, _⟩ := hf
  simp only [Set.mem_union]
  by_cases hD : (fieldDiscExp f h : ℝ) ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ))
  · exact Or.inl (Or.inr ⟨hf', h, hD⟩)
  · push_neg at hD
    by_cases hC1 : (radical (fieldDiscExp f h) : ℝ) ≤
        (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ)))
    · by_cases hC0 : radical (fieldDiscExp f h) ≤ H
      · exact Or.inl (Or.inl (Or.inl ⟨hf', h, hC0, hD⟩))
      · push_neg at hC0
        exact Or.inl (Or.inl (Or.inr ⟨hf', h, hC1, hC0, hD⟩))
    · push_neg at hC1
      exact Or.inr ⟨hf', h, hC1⟩

/-- The finiteness of `SubcaseI` (it sits inside the finite box). -/
theorem SubcaseI_finite (n H : ℕ) : (SubcaseI n H).Finite :=
  (box_finite n H).subset (fun f hf => Bad_subset_Box n H (irreducibleBad_subset_Bad n H hf.1))

/-- Finiteness of the four-piece union (all pieces sit inside the box). -/
theorem cover_union_finite (n H : ℕ) :
    (SubcaseI_direct n H ∪ SubcaseI_P1resid n H ∪
      SubcaseI_P2 n H ∪ SubcaseI_P3 n H).Finite :=
  (box_finite n H).subset (fun f hf => hf.elim
    (fun hf => hf.elim
      (fun hf => hf.elim (fun hf => Bad_subset_Box n H (irreducibleBad_subset_Bad n H hf.1.1))
        (fun hf => Bad_subset_Box n H (irreducibleBad_subset_Bad n H hf.1.1)))
      (fun hf => Bad_subset_Box n H (irreducibleBad_subset_Bad n H hf.1.1)))
    (fun hf => Bad_subset_Box n H (irreducibleBad_subset_Bad n H hf.1.1)))

/-- **Counting cover**: `#SubcaseI ≤ #direct + #P1resid + #P2 + #P3`. -/
theorem ncard_SubcaseI_le (n H : ℕ) :
    (SubcaseI n H).ncard ≤ (SubcaseI_direct n H).ncard + (SubcaseI_P1resid n H).ncard +
      (SubcaseI_P2 n H).ncard + (SubcaseI_P3 n H).ncard := by
  have h1 : (SubcaseI n H).ncard ≤ (SubcaseI_direct n H ∪ SubcaseI_P1resid n H ∪
      SubcaseI_P2 n H ∪ SubcaseI_P3 n H).ncard :=
    Set.ncard_le_ncard (SubcaseI_subset_cover n H) (cover_union_finite n H)
  have h2 : (SubcaseI_direct n H ∪ SubcaseI_P1resid n H ∪
      SubcaseI_P2 n H ∪ SubcaseI_P3 n H).ncard ≤
      (SubcaseI_direct n H ∪ SubcaseI_P1resid n H ∪ SubcaseI_P2 n H).ncard +
        (SubcaseI_P3 n H).ncard := Set.ncard_union_le _ _
  have h3 : (SubcaseI_direct n H ∪ SubcaseI_P1resid n H ∪ SubcaseI_P2 n H).ncard ≤
      (SubcaseI_direct n H ∪ SubcaseI_P1resid n H).ncard + (SubcaseI_P2 n H).ncard :=
    Set.ncard_union_le _ _
  have h4 : (SubcaseI_direct n H ∪ SubcaseI_P1resid n H).ncard ≤
      (SubcaseI_direct n H).ncard + (SubcaseI_P1resid n H).ncard := Set.ncard_union_le _ _
  omega

/-- **`#SubcaseI = O(H^(n-1))` given the three residual bounds.** -/
theorem SubcaseI_isBigO_of_residual (n : ℕ) (hn : 3 ≤ n)
    (h1 : (fun H : ℕ => ((SubcaseI_P1resid n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h3 : (fun H : ℕ => ((SubcaseI_P3 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => ((SubcaseI n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  have hg : ∀ᶠ H : ℕ in atTop, (0 : ℝ) ≤ (SubcaseI_direct n H).ncard +
      (SubcaseI_P1resid n H).ncard + (SubcaseI_P2 n H).ncard + (SubcaseI_P3 n H).ncard :=
    Eventually.of_forall (fun H => by positivity)
  refine (isBigO_of_eventually_le_real (f := fun H : ℕ => ((SubcaseI n H).ncard : ℝ))
    (g := fun H : ℕ => (SubcaseI_direct n H).ncard + (SubcaseI_P1resid n H).ncard +
      (SubcaseI_P2 n H).ncard + (SubcaseI_P3 n H).ncard)
    (Eventually.of_forall (fun H => Nat.cast_nonneg _)) hg ?_).trans ?_
  · refine Eventually.of_forall (fun H => ?_)
    have h := ncard_SubcaseI_le n H
    calc ((SubcaseI n H).ncard : ℝ)
        ≤ ((((SubcaseI_direct n H).ncard + (SubcaseI_P1resid n H).ncard) +
            (SubcaseI_P2 n H).ncard + (SubcaseI_P3 n H).ncard : ℕ) : ℝ) := by
          exact_mod_cast h
      _ = (SubcaseI_direct n H).ncard + (SubcaseI_P1resid n H).ncard +
            (SubcaseI_P2 n H).ncard + (SubcaseI_P3 n H).ncard := by push_cast; ring
  · exact ((((SubcaseI_direct_isBigO n hn).add h1).add h2).add h3)

/-- **`#IrreducibleBad = O(H^(n-1))` given the four residual bounds.** -/
theorem irreducibleBad_isBigO_of_residual (n : ℕ) (hn : 3 ≤ n)
    (h1 : (fun H : ℕ => ((SubcaseI_P1resid n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h3 : (fun H : ℕ => ((SubcaseI_P3 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => ((IrreducibleBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  have hg : ∀ᶠ H : ℕ in atTop, (0 : ℝ) ≤ (PrimBadCaseIII n H).ncard + (SubcaseI n H).ncard :=
    Eventually.of_forall (fun H => by positivity)
  have hprim : (fun H : ℕ => ((PrimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
    refine (isBigO_of_eventually_le_real (f := fun H : ℕ => ((PrimitiveBad n H).ncard : ℝ))
      (g := fun H : ℕ => (PrimBadCaseIII n H).ncard + (SubcaseI n H).ncard)
      (Eventually.of_forall (fun H => Nat.cast_nonneg _)) hg ?_).trans ?_
    · refine Eventually.of_forall (fun H => ?_)
      have h := ncard_primitiveBad_le n H
      calc ((PrimitiveBad n H).ncard : ℝ)
          ≤ ((((PrimBadCaseIII n H).ncard + (SubcaseI n H).ncard : ℕ)) : ℝ) := by
            exact_mod_cast h
        _ = (PrimBadCaseIII n H).ncard + (SubcaseI n H).ncard := by push_cast; ring
    · exact (PrimBadCaseIII_isBigO n hn).add (SubcaseI_isBigO_of_residual n hn h1 h2 h3)
  have hg2 : ∀ᶠ H : ℕ in atTop, (0 : ℝ) ≤ (PrimitiveBad n H).ncard + (ImprimitiveBad n H).ncard :=
    Eventually.of_forall (fun H => by positivity)
  refine (isBigO_of_eventually_le_real (f := fun H : ℕ => ((IrreducibleBad n H).ncard : ℝ))
    (g := fun H : ℕ => (PrimitiveBad n H).ncard + (ImprimitiveBad n H).ncard)
    (Eventually.of_forall (fun H => Nat.cast_nonneg _)) hg2 ?_).trans ?_
  · refine Eventually.of_forall (fun H => ?_)
    have h := Set.ncard_union_le (PrimitiveBad n H) (ImprimitiveBad n H)
    rw [← irrBad_eq_prim_union_imprim n H] at h
    calc ((IrreducibleBad n H).ncard : ℝ)
        ≤ ((((PrimitiveBad n H).ncard + (ImprimitiveBad n H).ncard : ℕ)) : ℝ) := by
          exact_mod_cast h
      _ = (PrimitiveBad n H).ncard + (ImprimitiveBad n H).ncard := by push_cast; ring
  · exact hprim.add h4

/-- **`theorem_1` given the four residual bounds**: the challenge statement
follows from the four region bounds (the reducible half and the
primitive/`DD = 0`/subcase-(ii) slice are already unconditional). -/
theorem theorem_1_of_residual (n : ℕ) (hn : 3 ≤ n)
    (h1 : (fun H : ℕ => ((SubcaseI_P1resid n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h3 : (fun H : ℕ => ((SubcaseI_P3 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  E_isBigO_of_irrBad n hn (irreducibleBad_isBigO_of_residual n hn h1 h2 h3 h4)

/-- The Case-I residual slice lies in the Case-I region `CaseIFull`. -/
theorem SubcaseI_P1resid_subset_CaseIFull (n H : ℕ) (hn : 3 ≤ n) :
    SubcaseI_P1resid n H ⊆ CaseIFull n H := by
  intro f hf
  obtain ⟨hsub, h'⟩ := hf
  have hprim := SubcaseI_subset_PrimitiveBad n H hsub
  obtain ⟨h, _, hsq⟩ := PrimitiveBad_exists_squarefull_fieldDisc n H f hprim
  obtain ⟨h', hC', _, hD'⟩ := h'
  exact ⟨h, Bad_subset_Box n H (irreducibleBad_subset_Bad n H hprim.1), hsq, hC', hD'⟩

/-- **The Case-I residual slice is `O(H^(n-1))` given the per-discriminant
Fourier bound** (paper §4, Corollary 33). -/
theorem SubcaseI_P1resid_isBigO_of_perD (n c : ℕ) (hn : 3 ≤ n) (hc : 1 ≤ c)
    (hper : PerDDiscBound n c) :
    (fun H : ℕ => ((SubcaseI_P1resid n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  have hle : ∀ᶠ H : ℕ in atTop, (SubcaseI_P1resid n H).ncard ≤ (CaseIFull n H).ncard := by
    refine Eventually.of_forall (fun H => ?_)
    have hfin : (CaseIFull n H).Finite := by
      refine (box_finite n H).subset ?_
      intro f hf
      obtain ⟨h, hbox, _⟩ := hf
      exact hbox
    exact Set.ncard_le_ncard (SubcaseI_P1resid_subset_CaseIFull n H hn) hfin
  exact (Commons.Analysis.Asymptotics.isBigO_of_eventually_le _ _ hle).trans
    (CaseIFull_isBigO n c hn hc hper)

/-- **`theorem_1` given the per-discriminant Fourier bound plus the three
residual region bounds** — the sharpest form of the final assembly: the whole
paper's Case I (the range `C_f ≤ H^(1+δ)`) is handled by the single
per-discriminant estimate `PerDDiscBound` (paper §4, Corollary 33), whose
`C_f ≤ H` part is already proved unconditionally (`CaseIRegion`). -/
theorem theorem_1_of_perD (n c : ℕ) (hn : 3 ≤ n) (hc : 1 ≤ c) (hper : PerDDiscBound n c)
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h3 : (fun H : ℕ => ((SubcaseI_P3 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_residual n hn (SubcaseI_P1resid_isBigO_of_perD n c hn hc hper) h2 h3 h4

end

end Submission.Vdw
