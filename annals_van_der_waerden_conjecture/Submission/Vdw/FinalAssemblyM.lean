import Mathlib
import Submission.Vdw.FinalAssembly
import Submission.Vdw.PrimitiveCaseM
import Submission.Vdw.CaseIRegionM
import Submission.Vdw.CaseIFourierM
import Submission.Vdw.SubcaseI_P3BoundM
import Submission.Vdw.CaseIIIBound
import Submission.Vdw.CaseIIIThreshold
import Submission.Vdw.PerIrrTheta
import Submission.Vdw.PerIrrWeyl
import Submission.Vdw.PerDDiscTheta

open Polynomial Asymptotics
open scoped BigOperators
open Filter
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Final assembly: `theorem_1` from Case II and the imprimitive bound

This module closes the final assembly loop.  The §4 Fourier input (the
paper's Corollary `Dequi2` / Proposition `ftgen2`) is now **unconditional**:
the complete Weyl-bound chapter (`WeylBridge` → `WeylExpSum` → the
θ-generic multi-prime sieve of `MultiPrime*` → `PerIrrTheta` →
`PerIrrWeyl.perIrrBoundTheta_weyl`) yields, for every `3 ≤ n`, a constant
`c` with

  `PerIrrBoundTheta n (weylδ n) c`.

Parameterising the whole region analysis by `M` (`δ = 2/M`) and taking

  `weylM n := 4 * n * 2^n`   (so that `2 / weylM n = weylδ n`)

turns this into the input of the `M`-generic region chapters
(`CaseIRegionM`, `CaseIFourierM`, `SubcaseI_P3BoundM`, `PrimitiveCaseM`), and
the remaining work is pure bookkeeping:

* `SubcaseIM_P2` — the `D_f ≤ H^{2+2δ}` slice of the subcase-(i) remainder;
* `SubcaseIM_subset_cover` — every member of `SubcaseIM n M H` lies in one of
  the four regions `CaseIDirectM`, `CaseIFullM`, `SubcaseIM_P2`,
  `SubcaseI_P3M` (using squarefullness of `D_f` for primitive-proper
  irreducible bad polynomials, `PrimitiveBad_exists_squarefull_fieldDisc`);
* `SubcaseIM_isBigO_of_residual` — `#SubcaseIM = O(H^{n-1})` from the
  per-discriminant Fourier bound at `δ = 2/M` and the Case-II bound;
* `PrimitiveBad_isBigO_of_M` / `theorem_1_of_M` — the `O(H^{n-1})` bound for
  the primitive part and finally for `IrreducibleBad` and `E`.

The endpoint `theorem_1_of_caseII_imprimitive` reduces the challenge
statement `theorem_1` to exactly TWO named inputs, both research-level and
classical:

* `SubcaseI_P2 n H = O(H^(n-1))` — Case II (number-field counting: Schmidt's
  `O(X^{(n+2)/4})`, Lemke Oliver–Thorne fibre bounds, exact quartic/quintic
  counts);
* `ImprimitiveBad n H = O(H^(n-1))` — Widmer's `O(H^{n/2+2})` bound on
  imprimitive Galois groups (`n ≥ 6`; vacuous for prime `n`; `n = 4` needs a
  separate argument).

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-! ## Elementary order/antitonicity lemmas for `largePart` and `lowerThr` -/

/-- `largePart` is antitone in the threshold: raising the threshold can only
remove prime factors. -/
lemma largePart_mono_thr (C B₁ B₂ : ℕ) (h : B₂ ≤ B₁) :
    largePart C B₁ ≤ largePart C B₂ := by
  classical
  unfold largePart
  refine Finset.prod_le_prod_of_subset_of_one_le' ?_ ?_
  · intro p hp
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hp).1, le_trans h (Finset.mem_filter.mp hp).2⟩
  · intro p hp _
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).one_lt.le

/-- `lowerThr M H = ⌈H^(1/M)⌉` is antitone in `M`. -/
lemma lowerThr_anti (M M' H : ℕ) (hM : 1 ≤ M) (h : M ≤ M') (hH : 1 ≤ H) :
    lowerThr M' H ≤ lowerThr M H := by
  simp only [lowerThr, Commons.Analysis.ExpLog.lowerThreshold]
  apply Nat.ceil_mono
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hH)
  exact one_div_le_one_div_of_le (by exact_mod_cast hM) (by exact_mod_cast h)

/-- With `4n ≤ M` the subcase-(i) split variable of `SubcaseIM n M H` is at
most the one of `SubcaseI n H` at `M = 4n`. -/
lemma A_large_le_A_largeM (n M H : ℕ) (hn : 3 ≤ n) (hM4 : 4 * n ≤ M) (hH : 1 ≤ H)
    (f : ℤ[X]) (h : Irreducible (f.map φℚ)) :
    A_large n H f h ≤ A_largeM n M H f h := by
  unfold A_large A_largeM
  exact largePart_mono_thr _ _ _ (lowerThr_anti (4 * n) M H (by omega) hM4 hH)

/-! ## The subcase-(i) remainder and its cover -/

/-- The `D_f ≤ H^(2+2δ)` (`δ = 2/M`) slice of the subcase-(i) remainder
`SubcaseIM` — the `M`-generic Case-II region. -/
def SubcaseIM_P2 (n M H : ℕ) : Set ℤ[X] :=
  {f | f ∈ SubcaseIM n M H ∧ ∃ h : Irreducible (f.map φℚ),
      (fieldDiscExp f h : ℝ) ≤ (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ))}

/-- For `M ≥ 4n` the remainder `SubcaseIM n M H` is contained in
`SubcaseI n H` (the `A`-threshold only decreases when `M` grows). -/
lemma SubcaseIM_subset_SubcaseI (n M H : ℕ) (hn : 3 ≤ n) (hM4 : 4 * n ≤ M)
    (hH : 1 ≤ H) :
    SubcaseIM n M H ⊆ SubcaseI n H := by
  intro f hf
  rcases hf with ⟨hbad, h, hprim, hdd, hA⟩
  refine ⟨hbad, h, hprim, hdd, ?_⟩
  intro hA'
  exact hA (lt_of_lt_of_le hA' (A_large_le_A_largeM n M H hn hM4 hH f h))

/-- The `M`-generic Case-II region is contained in the `δ = 1/(2n)` Case-II
region `SubcaseI_P2` (both conditions weaken as `M ≥ 4n`). -/
lemma SubcaseIM_P2_subset_SubcaseI_P2 (n M H : ℕ) (hn : 3 ≤ n) (hM4 : 4 * n ≤ M)
    (hH : 1 ≤ H) :
    SubcaseIM_P2 n M H ⊆ SubcaseI_P2 n H := by
  intro f hf
  rcases hf with ⟨hf1, h, hD⟩
  refine ⟨SubcaseIM_subset_SubcaseI n M H hn hM4 hH hf1, h, ?_⟩
  refine le_trans hD (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hH) ?_)
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have : 0 < M := by omega
    exact_mod_cast this
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h4M : (4 : ℝ) / (M : ℝ) ≤ 1 / (n : ℝ) := by
    rw [div_le_div_iff₀ hMpos hnR, one_mul]
    exact_mod_cast hM4
  linarith

/-- **Cover of the subcase-(i) remainder.**  Every member of
`SubcaseIM n M H` (`M ≥ 4n`, `H ≥ 1`) lies in one of the four regions:
the Case-I direct regime `CaseIDirectM`, the Case-I full region `CaseIFullM`,
the Case-II region `SubcaseIM_P2`, or the subcase-(i) proper
`SubcaseI_P3M`. -/
theorem SubcaseIM_subset_cover (n M H : ℕ) (hn : 3 ≤ n) (hM4 : 4 * n ≤ M)
    (hH : 1 ≤ H) :
    SubcaseIM n M H ⊆ CaseIDirectM n M H ∪ CaseIFullM n M H ∪
      SubcaseIM_P2 n M H ∪ SubcaseI_P3M n M H := by
  classical
  intro f hf
  have hfmem := hf
  rcases hf with ⟨hbad, h, hprim, hdd, hA⟩
  obtain ⟨h', _, hsq0⟩ := PrimitiveBad_exists_squarefull_fieldDisc n H f ⟨hbad, h, hprim⟩
  have hsq : Squarefull (fieldDiscExp f h) := by simpa [fieldDiscExp] using hsq0
  have hfbox : f ∈ Box n H := Bad_subset_Box n H (irreducibleBad_subset_Bad n H hbad)
  by_cases hC : (H : ℝ) ^ (1 + 2 / (M : ℝ)) < (radical (fieldDiscExp f h) : ℝ)
  · exact Or.inr (show f ∈ SubcaseI_P3M n M H from ⟨hfmem, h, hC⟩)
  · push_neg at hC
    by_cases hDbig : (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) < (fieldDiscExp f h : ℝ)
    · by_cases hR : radical (fieldDiscExp f h) ≤ H
      · exact Or.inl (Or.inl (Or.inl
          (show f ∈ CaseIDirectM n M H from ⟨h, hfbox, hsq, hR, hDbig⟩)))
      · exact Or.inl (Or.inl (Or.inr
          (show f ∈ CaseIFullM n M H from ⟨h, hfbox, hsq, hC, hDbig⟩)))
    · push_neg at hDbig
      exact Or.inl (Or.inr (show f ∈ SubcaseIM_P2 n M H from ⟨hfmem, h, hDbig⟩))

/-- Finiteness of the four-piece union (all pieces sit inside the box). -/
theorem coverM_union_finite (n M H : ℕ) :
    (CaseIDirectM n M H ∪ CaseIFullM n M H ∪
      SubcaseIM_P2 n M H ∪ SubcaseI_P3M n M H).Finite :=
  (box_finite n H).subset (fun _ hf => hf.elim
    (fun h1 => h1.elim
      (fun h2 => h2.elim (fun h2a => h2a.2.1) (fun h2b => h2b.2.1))
      (fun h2 => Bad_subset_Box n H (irreducibleBad_subset_Bad n H h2.1.1)))
    (fun h2 => Bad_subset_Box n H (irreducibleBad_subset_Bad n H h2.1.1)))

/-- **Counting cover**: `#SubcaseIM ≤ #CaseIDirectM + #CaseIFullM +
#SubcaseIM_P2 + #SubcaseI_P3M`. -/
theorem ncard_SubcaseIM_le_M (n M H : ℕ) (hn : 3 ≤ n) (hM4 : 4 * n ≤ M) (hH : 1 ≤ H) :
    (SubcaseIM n M H).ncard ≤ (CaseIDirectM n M H).ncard + (CaseIFullM n M H).ncard +
      (SubcaseIM_P2 n M H).ncard + (SubcaseI_P3M n M H).ncard := by
  have h1 : (SubcaseIM n M H).ncard ≤ (CaseIDirectM n M H ∪ CaseIFullM n M H ∪
      SubcaseIM_P2 n M H ∪ SubcaseI_P3M n M H).ncard :=
    Set.ncard_le_ncard (SubcaseIM_subset_cover n M H hn hM4 hH) (coverM_union_finite n M H)
  have h2 : (CaseIDirectM n M H ∪ CaseIFullM n M H ∪
      SubcaseIM_P2 n M H ∪ SubcaseI_P3M n M H).ncard ≤
      (CaseIDirectM n M H ∪ CaseIFullM n M H ∪ SubcaseIM_P2 n M H).ncard +
        (SubcaseI_P3M n M H).ncard := Set.ncard_union_le _ _
  have h3 : (CaseIDirectM n M H ∪ CaseIFullM n M H ∪ SubcaseIM_P2 n M H).ncard ≤
      (CaseIDirectM n M H ∪ CaseIFullM n M H).ncard + (SubcaseIM_P2 n M H).ncard :=
    Set.ncard_union_le _ _
  have h4 : (CaseIDirectM n M H ∪ CaseIFullM n M H).ncard ≤
      (CaseIDirectM n M H).ncard + (CaseIFullM n M H).ncard := Set.ncard_union_le _ _
  omega

/-! ## The subcase-(i) remainder is `O(H^(n-1))` -/

/-- **`#SubcaseIM = O(H^(n-1))`** given the per-discriminant Fourier bound at
`δ = 2/M` and the Case-II bound. -/
theorem SubcaseIM_isBigO_of_P2M (n M c : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M)
    (hnM : n ≤ M) (hM4 : 4 * n ≤ M)
    (hMn : (2 : ℝ) + 4 / (M : ℝ) < 2 * (n : ℝ) - 1)
    (hMn2 : (2 : ℝ) + 2 / (M : ℝ) < 2 * (n : ℝ) - 1)
    (hc : 1 ≤ c) (hper : PerIrrBoundTheta n ((2 : ℝ) / (M : ℝ)) c)
    (h2 : (fun H : ℕ => ((SubcaseIM_P2 n M H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => ((SubcaseIM n M H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  classical
  -- the per-discriminant Fourier bound at `δ = 2/M`
  have hδneg : (-1 : ℝ) < (2 : ℝ) / (M : ℝ) := by
    have h : (0 : ℝ) ≤ (2 : ℝ) / (M : ℝ) :=
      div_nonneg (by norm_num) (Nat.cast_nonneg M)
    linarith
  have hδ0 : (0 : ℝ) ≤ (2 : ℝ) / (M : ℝ) :=
    div_nonneg (by norm_num) (Nat.cast_nonneg M)
  set cf : ℕ := max (c * smallConst n + 1) (smallConst n * (2 * smallConst n + 1) ^ n) with hcf
  have hcf1 : 1 ≤ cf := le_trans (Nat.le_add_left 1 (c * smallConst n)) (le_max_left _ _)
  have hperDD : PerDDiscBoundTheta n ((2 : ℝ) / (M : ℝ)) cf :=
    perDDiscBoundTheta_of_perIrrBoundTheta n c hn hc ((2 : ℝ) / (M : ℝ)) hδneg hδ0 hper
  have hfull : (fun H : ℕ => ((CaseIFullM n M H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
    CaseIFullM_isBigO n M cf hn hM hcf1 hMn hperDD
  have hdir : (fun H : ℕ => ((CaseIDirectM n M H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
    CaseIDirectM_isBigO n M hn hM hMn
  have hP3 : (fun H : ℕ => ((SubcaseI_P3M n M H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
    SubcaseI_P3M_isBigO_of_perIrrBoundTheta n M c hn hM hnM hMn2 hc hper
  -- the pointwise cover bound
  have hle : ∀ᶠ H : ℕ in atTop,
      ((SubcaseIM n M H).ncard : ℝ) ≤ (CaseIDirectM n M H).ncard + (CaseIFullM n M H).ncard +
        (SubcaseIM_P2 n M H).ncard + (SubcaseI_P3M n M H).ncard := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with H hH
    exact_mod_cast ncard_SubcaseIM_le_M n M H hn hM4 hH
  refine (isBigO_of_eventually_le_real (Eventually.of_forall fun H => Nat.cast_nonneg _)
    (Eventually.of_forall fun H => by positivity) hle).trans ?_
  exact (((hdir.add hfull).add h2).add hP3)

/-- **`#SubcaseIM = O(H^(n-1))`** given the *paper's* Case-II bound
`#SubcaseI_P2 = O(H^(n-1))` (the version used by `theorem_1_of_M`).  The
parametrised form `SubcaseIM_isBigO_of_P2M` is the sharper statement. -/
theorem SubcaseIM_isBigO_of_residual (n M c : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M)
    (hnM : n ≤ M) (hM4 : 4 * n ≤ M)
    (hMn : (2 : ℝ) + 4 / (M : ℝ) < 2 * (n : ℝ) - 1)
    (hMn2 : (2 : ℝ) + 2 / (M : ℝ) < 2 * (n : ℝ) - 1)
    (hc : 1 ≤ c) (hper : PerIrrBoundTheta n ((2 : ℝ) / (M : ℝ)) c)
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => ((SubcaseIM n M H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  have h2' : (fun H : ℕ => ((SubcaseIM_P2 n M H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
    have hpoint : ∀ᶠ H : ℕ in atTop,
        ((SubcaseIM_P2 n M H).ncard : ℝ) ≤ ((SubcaseI_P2 n H).ncard : ℝ) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with H hH
      have hfin : (SubcaseI_P2 n H).Finite :=
        (box_finite n H).subset (fun f hf =>
          Bad_subset_Box n H (irreducibleBad_subset_Bad n H hf.1.1))
      exact_mod_cast Set.ncard_le_ncard (SubcaseIM_P2_subset_SubcaseI_P2 n M H hn hM4 hH) hfin
    exact (isBigO_of_eventually_le_real (Eventually.of_forall fun H => Nat.cast_nonneg _)
      (Eventually.of_forall fun H => Nat.cast_nonneg _) hpoint).trans h2
  exact SubcaseIM_isBigO_of_P2M n M c hn hM hnM hM4 hMn hMn2 hc hper h2'

/-! ## Case III subcase (ii) at the parameter threshold `M` -/

/-- **Partial Case-III union bound at the parameter threshold.**  The
`DD(u_f) = 0` piece plus the subcase-(ii) region at threshold `⌈H^(1/M)⌉`
together are `O(H^(n-1))`. -/
theorem ddzero_add_subcase2M_isBigO (n M : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M) (hnM : n ≤ M) :
    (fun H : ℕ =>
        (((DDzeroBox n H).ncard + (CaseIIISubcase2 n H (lowerThr M H)).ncard : ℕ) : ℝ))
      =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  classical
  rcases caseIII_subcase2_bound_pointwise n M hn hM hnM with ⟨C2, hC2⟩
  let C0 : ℕ := (n - 1) * ((4 * n - 3) * (2 * n - 1))
  have hle0 : ∀ᶠ H : ℕ in atTop,
      (DDzeroBox n H).ncard ≤ C0 * (2 * H + 1) ^ (n - 1) := by
    filter_upwards with H
    exact DDzeroBox_ncard_le n H hn
  let C : ℕ := C0 * 3 ^ (n - 1) + C2
  have hpoint : ∀ᶠ H : ℕ in atTop,
      (DDzeroBox n H).ncard + (CaseIIISubcase2 n H (lowerThr M H)).ncard ≤ C * H ^ (n - 1) := by
    filter_upwards [hle0, hC2, eventually_ge_atTop (1 : ℕ)] with H hz hc2 hH
    have hz' : (DDzeroBox n H).ncard ≤ (C0 * 3 ^ (n - 1)) * H ^ (n - 1) := by
      calc
        (DDzeroBox n H).ncard ≤ C0 * (2 * H + 1) ^ (n - 1) := hz
        _ ≤ C0 * (3 * H) ^ (n - 1) := by
          exact Nat.mul_le_mul_left C0 (pow_le_pow_left₀ (by omega) (by omega) (n - 1))
        _ = (C0 * 3 ^ (n - 1)) * H ^ (n - 1) := by
          rw [mul_pow]; ring
    calc
      (DDzeroBox n H).ncard + (CaseIIISubcase2 n H (lowerThr M H)).ncard
          ≤ (C0 * 3 ^ (n - 1)) * H ^ (n - 1) + C2 * H ^ (n - 1) := by
            exact Nat.add_le_add hz' hc2
      _ = (C0 * 3 ^ (n - 1) + C2) * H ^ (n - 1) := by rw [add_mul]
  exact Commons.Analysis.Asymptotics.isBigO_of_natCast_le_mul_pow (n - 1) C
    (fun H : ℕ => (DDzeroBox n H).ncard + (CaseIIISubcase2 n H (lowerThr M H)).ncard) hpoint

/-! ## `O(H^(n-1))` for the primitive part from the subcase-(i) bound -/

/-- **The primitive Case-III-side slice at the parameter threshold is
`O(H^(n-1))`.** -/
theorem PrimBadCaseIIIM_isBigO (n M : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M) (hnM : n ≤ M) :
    (fun H : ℕ => ((PrimBadCaseIIIM n M H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  classical
  have hle : ∀ᶠ H : ℕ in atTop,
      (PrimBadCaseIIIM n M H).ncard ≤
        (DDzeroBox n H).ncard + (CaseIIISubcase2 n H (lowerThr M H)).ncard := by
    filter_upwards with H
    have hfinD : (DDzeroBox n H).Finite := (box_finite n H).subset (fun f hf => hf.1)
    have hfinS : (CaseIIISubcase2 n H (lowerThr M H)).Finite :=
      CaseIIISubcase2_finite n H (lowerThr M H)
    have hfinU : (DDzeroBox n H ∪ CaseIIISubcase2 n H (lowerThr M H)).Finite :=
      Set.Finite.union hfinD hfinS
    calc
      (PrimBadCaseIIIM n M H).ncard
          ≤ (DDzeroBox n H ∪ CaseIIISubcase2 n H (lowerThr M H)).ncard :=
        Set.ncard_le_ncard (PrimBadCaseIIIM_subset_DDzero_add_subcase2 n M H hn) hfinU
      _ ≤ (DDzeroBox n H).ncard + (CaseIIISubcase2 n H (lowerThr M H)).ncard :=
        Set.ncard_union_le _ _
  exact (Commons.Analysis.Asymptotics.isBigO_of_eventually_le
      (fun H : ℕ => (PrimBadCaseIIIM n M H).ncard)
      (fun H : ℕ => (DDzeroBox n H).ncard + (CaseIIISubcase2 n H (lowerThr M H)).ncard)
      hle).trans (ddzero_add_subcase2M_isBigO n M hn hM hnM)

/-- **`#PrimitiveBad = O(H^(n-1))`** given the subcase-(i) remainder bound. -/
theorem PrimitiveBad_isBigO_of_M (n M : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M) (hnM : n ≤ M)
    (hSub : (fun H : ℕ => ((SubcaseIM n M H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => ((PrimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  classical
  have hIII := PrimBadCaseIIIM_isBigO n M hn hM hnM
  have h2 : (fun H : ℕ => ((PrimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => (((PrimBadCaseIIIM n M H).ncard + (SubcaseIM n M H).ncard : ℕ) : ℝ)) :=
    Commons.Analysis.Asymptotics.isBigO_of_eventually_le
      (fun H : ℕ => (PrimitiveBad n H).ncard)
      (fun H : ℕ => (PrimBadCaseIIIM n M H).ncard + (SubcaseIM n M H).ncard)
      (Eventually.of_forall (fun H => ncard_primitiveBadM_le n M H))
  refine h2.trans ?_
  have hsum : (fun H : ℕ =>
        (((PrimBadCaseIIIM n M H).ncard + (SubcaseIM n M H).ncard : ℕ) : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
    have hle : ∀ᶠ H : ℕ in atTop,
        (((PrimBadCaseIIIM n M H).ncard + (SubcaseIM n M H).ncard : ℕ) : ℝ) ≤
          ((PrimBadCaseIIIM n M H).ncard : ℝ) + ((SubcaseIM n M H).ncard : ℝ) := by
      filter_upwards with H
      push_cast
      exact le_refl _
    exact (isBigO_of_eventually_le_real (Eventually.of_forall fun H => Nat.cast_nonneg _)
      (Eventually.of_forall fun H => by positivity) hle).trans (hIII.add hSub)
  exact hsum

/-! ## `theorem_1` from the per-discriminant Fourier input and Case II -/

/-- **`#IrreducibleBad = O(H^(n-1))`** from the subcase-(i) bound and the
imprimitive bound. -/
theorem irreducibleBad_isBigO_of_M (n M : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M) (hnM : n ≤ M)
    (hSub : (fun H : ℕ => ((SubcaseIM n M H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => ((IrreducibleBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  classical
  have hprim := PrimitiveBad_isBigO_of_M n M hn hM hnM hSub
  have hg : ∀ᶠ H : ℕ in atTop,
      (0 : ℝ) ≤ (PrimitiveBad n H).ncard + (ImprimitiveBad n H).ncard :=
    Eventually.of_forall (fun H => by positivity)
  refine (isBigO_of_eventually_le_real (f := fun H : ℕ => ((IrreducibleBad n H).ncard : ℝ))
    (g := fun H : ℕ => (PrimitiveBad n H).ncard + (ImprimitiveBad n H).ncard)
    (Eventually.of_forall (fun H => Nat.cast_nonneg _)) hg ?_).trans (hprim.add h4)
  refine Eventually.of_forall (fun H => ?_)
  have h := Set.ncard_union_le (PrimitiveBad n H) (ImprimitiveBad n H)
  rw [← irrBad_eq_prim_union_imprim n H] at h
  calc ((IrreducibleBad n H).ncard : ℝ)
      ≤ ((((PrimitiveBad n H).ncard + (ImprimitiveBad n H).ncard : ℕ)) : ℝ) := by
        exact_mod_cast h
    _ = (PrimitiveBad n H).ncard + (ImprimitiveBad n H).ncard := by push_cast; ring

/-- **The challenge statement given the two remaining inputs** (`M`-generic
form): the per-discriminant Fourier bound at `δ = 2/M`, the Case-II bound, and
the imprimitive bound. -/
theorem theorem_1_of_M (n M c : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M) (hnM : n ≤ M) (hM4 : 4 * n ≤ M)
    (hMn : (2 : ℝ) + 4 / (M : ℝ) < 2 * (n : ℝ) - 1)
    (hMn2 : (2 : ℝ) + 2 / (M : ℝ) < 2 * (n : ℝ) - 1)
    (hc : 1 ≤ c) (hper : PerIrrBoundTheta n ((2 : ℝ) / (M : ℝ)) c)
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  E_isBigO_of_irrBad n hn (irreducibleBad_isBigO_of_M n M hn hM hnM
    (SubcaseIM_isBigO_of_residual n M c hn hM hnM hM4 hMn hMn2 hc hper h2) h4)

/-! ## The Weyl instantiation: `M = 4n·2^n`, so that `2/M = weylδ n` -/

/-- The parameter value at which the Fourier exponent `2/M` equals the Weyl
threshold `weylδ n`, i.e. `M = 2/weylδ n = 4n·2^n`. -/
def weylM (n : ℕ) : ℕ := 4 * n * 2 ^ n

lemma le_weylM (n : ℕ) : n ≤ weylM n := by
  unfold weylM
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 1 ≤ 4 * 2 ^ n := by nlinarith
  calc n = n * 1 := (Nat.mul_one n).symm
    _ ≤ n * (4 * 2 ^ n) := Nat.mul_le_mul_left n h2
    _ = 4 * n * 2 ^ n := by ring

lemma four_mul_le_weylM (n : ℕ) : 4 * n ≤ weylM n := by
  unfold weylM
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  calc 4 * n = 4 * n * 1 := (Nat.mul_one _).symm
    _ ≤ 4 * n * 2 ^ n := Nat.mul_le_mul_left _ h1

lemma one_le_weylM (n : ℕ) (hn : 3 ≤ n) : 1 ≤ weylM n :=
  le_trans (by omega : 1 ≤ 4 * n) (four_mul_le_weylM n)

/-- The Weyl parameter gives the Weyl exponent: `2 / (4n·2^n) = weylδ n`. -/
lemma two_div_weylM (n : ℕ) (hn : 3 ≤ n) :
    (2 : ℝ) / (weylM n : ℝ) = weylδ n := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : 0 < n := by omega
    exact_mod_cast (Nat.pos_iff_ne_zero.mp this)
  have hcast : (weylM n : ℝ) = 4 * (n : ℝ) * (2 : ℝ) ^ n := by
    simp only [weylM]
    push_cast
    ring
  have hx : (2 : ℝ) ^ (-(n : ℝ)) = (((2 : ℝ)) ^ n)⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  rw [hcast, weylδ, weylθ, hx]
  field_simp
  ring

lemma weylM_exponentM (n : ℕ) (hn : 3 ≤ n) :
    (2 : ℝ) + 4 / (weylM n : ℝ) < 2 * (n : ℝ) - 1 := by
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h4n : (4 : ℝ) ≤ (weylM n : ℝ) := by
    have h : 4 * 1 ≤ 4 * n := Nat.mul_le_mul_left 4 (by omega)
    have h' : 4 ≤ weylM n := le_trans (by simpa using h) (four_mul_le_weylM n)
    exact_mod_cast h'
  have hMpos : (0 : ℝ) < (weylM n : ℝ) := by linarith
  have hdiv : 4 / (weylM n : ℝ) ≤ 1 := (div_le_one hMpos).mpr h4n
  linarith

lemma weylM_exponentM2 (n : ℕ) (hn : 3 ≤ n) :
    (2 : ℝ) + 2 / (weylM n : ℝ) < 2 * (n : ℝ) - 1 := by
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2n : (2 : ℝ) ≤ (weylM n : ℝ) := by
    have h : 4 * 1 ≤ 4 * n := Nat.mul_le_mul_left 4 (by omega)
    have h' : 4 ≤ weylM n := le_trans (by simpa using h) (four_mul_le_weylM n)
    have : (4 : ℝ) ≤ (weylM n : ℝ) := by exact_mod_cast h'
    linarith
  have hMpos : (0 : ℝ) < (weylM n : ℝ) := by linarith
  have hdiv : 2 / (weylM n : ℝ) ≤ 1 := (div_le_one hMpos).mpr h2n
  linarith

/-- **`theorem_1` from Case II and the imprimitive bound.**  The §4 Fourier
input is unconditional (Weyl), so the challenge statement follows from

* the Case-II region bound `#SubcaseI_P2 n H = O(H^(n-1))` (number-field
  counting), and
* the imprimitive bound `#ImprimitiveBad n H = O(H^(n-1))` (Widmer). -/
theorem theorem_1_of_caseII_imprimitive (n : ℕ) (hn : 3 ≤ n)
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  obtain ⟨c, hc, hper⟩ := perIrrBoundTheta_weyl n hn
  refine theorem_1_of_M n (weylM n) c hn (one_le_weylM n hn) (le_weylM n)
    (four_mul_le_weylM n) (weylM_exponentM n hn) (weylM_exponentM2 n hn) hc ?_ h2 h4
  rw [two_div_weylM n hn]
  exact hper

end

end Submission.Vdw
