import Mathlib
import Submission.Vdw.PrimitiveCase
import Submission.Vdw.CaseIIISubcase2Entry

open Polynomial
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The primitive split with the large-prime threshold as a parameter

`PrimitiveCase` splits the primitive proper irreducible bad polynomials at the
fixed threshold `B = ⌈H^{1/(4n)}⌉` (`δ = 1/(2n)`, `δ/2 = 1/(4n)`), i.e.
`A_f = ∏_{p | C_f, p ≥ B} p`, into the Case-III side `A_f > H` and the
subcase-(i) remainder `A_f ≤ H`.  Here the same definitions and structural
lemmas are provided with the threshold `lowerThr M H` of a parameter `M`
(instantiated at `M = 4n·2^n` for the Weyl-based endgame):

* `mem_caseIIISubcase2M_of_ramified_data` — entry of the `A_f > H` data into
  the `M`-generic Case-III region `CaseIIISubcase2 n H (lowerThr M H)`;
* `A_largeM`, `PrimBadCaseIIIM`, `SubcaseIM`;
* the cover `PrimitiveBad = PrimBadCaseIIIM ∪ SubcaseIM`, disjointness, and the
  counting-level split `ncard_primitiveBadM_le`.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-- **Entry into the subcase-(ii) region.**  Irreducible box polynomial `f`
(degree `n ≥ 3`) with squarefull `D_f`, `DD(u_f) ≠ 0`, and
`H < largePart C_f (lowerThr (4n) H)` (subcase (ii): the large-prime part of
the ramified product `C_f` above the canonical threshold `⌈H^(1/(4n))⌉`
exceeds `H`) lies in the region `CaseIIISubcase2 n H (lowerThr (4n) H)`. -/
theorem mem_caseIIISubcase2M_of_ramified_data (n M H : ℕ) (_hn : 3 ≤ n) (f : ℤ[X])
    (h : Irreducible (f.map φℚ)) (hfbox : f ∈ Box n H)
    (hsq : Squarefull (fieldDiscExp f h))
    (hdd : concDDZ n (upperCoeffs n f) ≠ 0)
    (hA : H < largePart (@ramifiedProduct f (Fact.mk h)) (lowerThr M H)) :
    f ∈ CaseIIISubcase2 n H (lowerThr M H) := by
  classical
  refine ⟨h, hfbox, hsq, hdd, ?_⟩
  -- the region's largePart is computed from D_f; the hypothesis from C_f:
  -- ramifiedProduct f = radical (fieldDisc f), same prime factors
  have hlg : largePart (@ramifiedProduct f (Fact.mk h)) (lowerThr M H) =
      largePart (fieldDiscExp f h) (lowerThr M H) := by
    haveI : Fact (Irreducible (f.map φℚ)) := ⟨h⟩
    dsimp [fieldDiscExp]
    exact ramifiedProduct_largePart_eq f (lowerThr M H)
  exact (by simpa [hlg] using hA)

/-- **The primitive-proper, Case-III-side slice of `IrreducibleBad`.**  An
irreducible bad polynomial whose Galois group (natural action on the roots)
is primitive, and which lies on the Case-III side of the eventual case
analysis in the strong (counting-region) sense: either `DD(u_f) = 0`, or
`DD(u_f) ≠ 0` and the large-prime part of the ramified product `C_f` above
the canonical threshold `⌈H^(1/(4n))⌉` exceeds `H` (paper subcase (ii),
with `A` computed from `C_f`). -/
noncomputable def PrimBadCaseIIIM (n M H : ℕ) : Set ℤ[X] :=
  {f | f ∈ IrreducibleBad n H ∧
    ∃ h : Irreducible (f.map φℚ),
      galPrimitive f h ∧
        (concDDZ n (upperCoeffs n f) = 0 ∨
          (concDDZ n (upperCoeffs n f) ≠ 0 ∧
            H < largePart (@ramifiedProduct f (Fact.mk h)) (lowerThr M H)))}

/-- **Entry of the primitive Case-III-side irreducible bad polynomials into
the counting regions.**  For `n ≥ 3`, every member of `PrimBadCaseIIIM n M H`
lies in `DDzeroBox n H ∪ CaseIIISubcase2 n H (lowerThr (4n) H)`: the
`DD(u_f) = 0` members are the `DDzeroBox` polys (they are in `Box` since
`IrreducibleBad ⊆ Bad ⊆ Box`); the other members are primitive proper
(squarefull `D_f` by Jordan + Case I) with `DD(u_f) ≠ 0` and
`A_f > H`, hence lie in the subcase-(ii) region via
`mem_caseIIISubcase2_of_ramified_data`. -/
theorem PrimBadCaseIIIM_subset_DDzero_add_subcase2 (n M H : ℕ) (hn : 3 ≤ n) :
    PrimBadCaseIIIM n M H ⊆
      DDzeroBox n H ∪ CaseIIISubcase2 n H (lowerThr M H) := by
  classical
  intro f hf
  rcases hf with ⟨hbad, h⟩
  rcases h with ⟨hirr, hprim, hcases⟩
  -- f is in the box (IrreducibleBad ⊆ Bad ⊆ Box) and monic of degree n
  have hfbox : f ∈ Box n H := Bad_subset_Box n H (irreducibleBad_subset_Bad n H hbad)
  have hmon : f.Monic := hfbox.1
  have hdegbox : f.degree = n := hfbox.2.1
  have hnat : f.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some hdegbox
  haveI : Fact (Irreducible (f.map φℚ)) := ⟨hirr⟩
  by_cases hdd0 : concDDZ n (upperCoeffs n f) = 0
  · -- DD(u_f) = 0 : straight into DDzeroBox
    left
    exact ⟨hfbox, hdd0⟩
  · right
    rcases hcases with hcases0 | hcases1
    · exact False.elim (hdd0 hcases0)
    · rcases hcases1 with ⟨hddnz, hA⟩
      -- primitive + |Gal| < n!  ⟹  squarefull D_f
      have hnd : (f.map φℚ).natDegree = n := by
        rw [monic_natDegree_map_rat f hmon, hnat]
      have hcard : Nat.card (f.map φℚ).Gal < ((f.map φℚ).natDegree).factorial := by
        rw [hnd]
        change Nat.card (f.map (algebraMap ℤ ℚ)).Gal < n.factorial
        exact hbad.1.2.2.2
      have hsq : Squarefull (fieldDisc f) :=
        squarefull_fieldDisc_of_primitive_card_lt f hmon hprim hcard
      -- fieldDiscExp with the explicit witness agrees with fieldDisc
      have hsq' : Squarefull (fieldDiscExp f hirr) := by
        simpa [fieldDiscExp] using hsq
      -- entry lemma (subcase-(ii) data on the C_f side, canonical threshold)
      exact mem_caseIIISubcase2M_of_ramified_data n M H hn f hirr hfbox hsq' hddnz hA

/-- `PrimBadCaseIIIM` is a subset of the primitive part. -/
theorem PrimBadCaseIIIM_subset_PrimitiveBad (n M H : ℕ) :
    PrimBadCaseIIIM n M H ⊆ PrimitiveBad n H := by
  intro f hf
  rcases hf with ⟨hbad, h, hprim, hcases⟩
  exact ⟨hbad, h, hprim⟩

/-- **`A_f` (instance-free): the large-prime part of the ramified product
`C_f` above the canonical threshold `⌈H^(1/(4n))⌉`** — the paper's
`A = ∏_{p | C_f, p > H^(1/(4n))} p` with `δ = 1/(2n)`, `δ/2 = 1/(4n)`
(integers `p`: `p > H^(1/(4n))` ⟺ `⌈H^(1/(4n))⌉ ≤ p`).  This is the
subcase-(i)/(ii) split variable of Case III: `A_f > H` is subcase (ii)
(counted by `PrimBadCaseIIIM`/`CaseIIISubcase2`), `A_f ≤ H` is subcase (i). -/
noncomputable def A_largeM (n M H : ℕ) (f : ℤ[X]) (h : Irreducible (f.map φℚ)) : ℕ :=
  largePart (@ramifiedProduct f (Fact.mk h)) (lowerThr M H)

/-- **The subcase-(i)-side slice of the primitive part (the cover
complement of `PrimBadCaseIIIM`).**  An irreducible bad polynomial whose
Galois group is primitive, with `DD(u_f) ≠ 0` and `A_f ≤ H` (the paper's
Case-III subcase (i), but stated without the Case-III inequality `C_f >
H^(1+δ)`, so that together with `PrimBadCaseIIIM` it covers the *whole*
primitive part: every primitive-proper irreducible bad polynomial either has
`DD(u_f) = 0`, or subcase (ii) `A_f > H` (both in `PrimBadCaseIIIM`, already
`O(H^(n-1))`), or subcase (i) `A_f ≤ H` with `DD(u_f) ≠ 0` (here).  The
numerical bound of `SubcaseIM` is exactly where the still-open research
threads enter: its members split (by the eventual `(C_f, D_f)`-region
analysis) into the Case-I side (`C_f ≤ H^(1+δ)`, `D_f > H^(2+2δ)` — needs
the Fourier extension `fbound2` for the per-D bound when `H < C_f ≤
H^(1+δ)`), the Case-II side (`D_f ≤ H^(2+2δ)` — field counting,
Schmidt/Lemke Oliver–Thorne), and the Case-III subcase (i) proper (Case I
argument with the intermediate divisor `B ∈ [H^(1+δ/2), H^(1+δ)]` of `C_f`
and `D' := ∏_{p | B} p^(v_p(D_f)) > H^(2+δ)` — again Fourier-gated since
`B > H`).  See the Roadmap Session-41 block for the full analysis. -/
noncomputable def SubcaseIM (n M H : ℕ) : Set ℤ[X] :=
  {f | f ∈ IrreducibleBad n H ∧
    ∃ h : Irreducible (f.map φℚ),
      galPrimitive f h ∧ concDDZ n (upperCoeffs n f) ≠ 0 ∧
        ¬ (H < A_largeM n M H f h)}

/-- `SubcaseIM` lies in the primitive part. -/
theorem SubcaseIM_subset_PrimitiveBad (n M H : ℕ) : SubcaseIM n M H ⊆ PrimitiveBad n H := by
  intro f hf
  rcases hf with ⟨hbad, h, hprim, hdd, hA⟩
  exact ⟨hbad, h, hprim⟩

/-- **Complete cover of the primitive part.**  `PrimitiveBad n H` splits
into the counted slice `PrimBadCaseIIIM n M H` (DD = 0 or subcase (ii)
`A_f > H`) and the remainder `SubcaseIM n M H` (DD ≠ 0, subcase (i)
`A_f ≤ H`).  Together with the reducible count (`redBox_isBigO`) and the
future imprimitive bound (Widmer), bounding `SubcaseIM` is what remains of
the irreducible half. -/
theorem PrimitiveBad_eq_primCaseIIIM_union_subcaseIM (n M H : ℕ) :
    PrimitiveBad n H = PrimBadCaseIIIM n M H ∪ SubcaseIM n M H := by
  classical
  ext f
  constructor
  · intro hf
    rcases hf with ⟨hbad, h, hprim⟩
    by_cases hdd0 : concDDZ n (upperCoeffs n f) = 0
    · left
      exact ⟨hbad, h, hprim, Or.inl hdd0⟩
    · by_cases hA : H < A_largeM n M H f h
      · left
        exact ⟨hbad, h, hprim, Or.inr ⟨hdd0, (by simpa [A_largeM] using hA)⟩⟩
      · right
        exact ⟨hbad, h, hprim, hdd0, hA⟩
  · intro hf
    rcases hf with hf | hf
    · exact PrimBadCaseIIIM_subset_PrimitiveBad n M H hf
    · exact SubcaseIM_subset_PrimitiveBad n M H hf

/-- The two slices are disjoint (a member cannot be both counted by the
subcase-(ii)/DD-zero machinery and be in the subcase-(i) remainder). -/
theorem PrimBadCaseIIIM_disjoint_SubcaseIM (n M H : ℕ) :
    ∀ f : ℤ[X], f ∈ PrimBadCaseIIIM n M H → f ∈ SubcaseIM n M H → False := by
  classical
  intro f hf1 hf2
  rcases hf2 with ⟨hbad2, h2, hprim2, hdd2, hA2⟩
  rcases hf1 with ⟨hbad1, h1⟩
  rcases h1 with ⟨hirr1, hprim1, hcases1⟩
  rcases hcases1 with hdd0 | hsub2
  · exact hdd2 hdd0
  · rcases hsub2 with ⟨hddnz, hA1⟩
    exact hA2 (by simpa [A_largeM] using hA1)

/-- **Counting-level split of the primitive part:** the number of
primitive-proper irreducible bad polynomials is at most the (counted)
`PrimBadCaseIIIM` slice plus the subcase-(i) remainder `SubcaseIM`. -/
theorem ncard_primitiveBadM_le (n M H : ℕ) :
    (PrimitiveBad n H).ncard ≤ (PrimBadCaseIIIM n M H).ncard + (SubcaseIM n M H).ncard := by
  classical
  calc
    (PrimitiveBad n H).ncard = (PrimBadCaseIIIM n M H ∪ SubcaseIM n M H).ncard := by
      rw [PrimitiveBad_eq_primCaseIIIM_union_subcaseIM]
    _ ≤ (PrimBadCaseIIIM n M H).ncard + (SubcaseIM n M H).ncard := Set.ncard_union_le _ _
end
end Submission.Vdw
