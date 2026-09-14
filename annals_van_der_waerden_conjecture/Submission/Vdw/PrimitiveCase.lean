import Mathlib
import Submission.Vdw.Reducible
import Submission.Vdw.CaseIIIField
import Submission.Vdw.CaseIIIDDZero
import Submission.Vdw.CaseIIISubcase2Entry
import Submission.Vdw.CaseIIIBound
import Submission.Commons.Analysis.Asymptotics.isBigO_of_eventually_le

open Polynomial Asymptotics
open scoped BigOperators
open Filter

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# The primitive-proper part of `IrreducibleBad`, Case-III side: entry into the
counting regions

Bhargava, *Galois groups of random integer polynomials* (Annals of Math
201(2) (2025)), Theorem 1.  Every member of `IrreducibleBad n H` is
irreducible over `ℚ` (`irreducibleBad_mem_irreducible_rat`), so its Galois
group acts transitively on the roots (`irrGalFinHom_pretransitive`) and the
*primitive / imprimitive* dichotomy applies.  This module formalizes the
first chunk of the eventual irreducible-bad case analysis: the members whose
Galois group is **primitive** (hence, with `|Gal| < n!`, a proper primitive
permutation group) have squarefull field discriminant
(`squarefull_fieldDisc_of_primitive_card_lt` — Jordan + the Case-I
squarefullness theorem), and — when additionally the double discriminant
vanishes or the subcase-(ii) size condition holds — they lie in the already
counted regions `DDzeroBox` ∪ `CaseIIISubcase2` at the canonical threshold
`⌈H^(1/(4n))⌉` (`lowerThr (4n) H`):

    PrimBadCaseIII n H ⊆ DDzeroBox n H ∪ CaseIIISubcase2 n H (lowerThr (4n) H)

hence (with `ddzero_add_subcase2_isBigO`)

    #(PrimBadCaseIII n H) = O(H^(n-1))        (n ≥ 3).

`PrimBadCaseIII n H` is precisely the *Case-III subcase-(ii) + DD-zero* slice
of the primitive-proper irreducible bad polynomials: it collects exactly
those members `f` of `IrreducibleBad n H` whose Galois group is primitive
and which either have `DD(u_f) = 0`, or have `DD(u_f) ≠ 0` and the
large-prime part `A_f = ∏_{p | C_f, p ≥ ⌈H^(1/(4n))⌉} p` of the ramified
product `C_f` exceeds `H` (the paper's subcase (ii)).  (The remaining
subcase (i), `A_f ≤ H`, together with Case I and Case II, needs the Fourier
extension `fbound2` / field counting — see `Roadmap.lean`.)  Note the region
does **not** test the paper's Case-III inequality `C_f > H^(1+δ)`: the
bound applies to every primitive-proper irreducible bad polynomial with
`DD(u_f) = 0` or `A_f > H`, regardless of its Case I/II/III assignment —
which is what the eventual union bound needs (extra assumptions can only
shrink the counted set).

Membership plumbing used here (all previously proved elsewhere):

* `f ∈ IrreducibleBad n H` ⟹ `f ∈ Bad n H` (`Bad` = monic, degree `n`,
  coefficients `|·| ≤ H`, `|Gal(f.map φℚ)| < n!`) and `¬ Reducible f`;
* `irreducibleBad_mem_irreducible_rat` — `Irreducible (f.map φℚ)`
  (Gauss: irreducible over ℤ with monic, degree ≥ 1 ⟺ over ℚ);
* `squarefull_fieldDisc_of_primitive_card_lt` — primitive + `|Gal| < n!`
  ⟹ `Squarefull (fieldDisc f)`;
* `mem_caseIIISubcase2_of_ramified_data` — irreducible box `f`, squarefull
  `D_f`, `DD(u_f) ≠ 0`, `H < largePart C_f (lowerThr (4n) H)` ⟹
  `f ∈ CaseIIISubcase2 n H (lowerThr (4n) H)`.
-/

namespace Submission.Vdw

/-- **Primitivity of the Galois group of an irreducible `ℤ`-polynomial** (with
an explicit irreducibility witness `h`, so the predicate can appear inside
set comprehensions): the image of `Gal(f)` in `S_n` (`irrGalFinHom`, the
natural action on the roots) is a preprimitive permutation group. -/
def galPrimitive (f : ℤ[X]) (h : Irreducible (f.map φℚ)) : Prop :=
  MulAction.IsPreprimitive ((@irrGalFinHom f (Fact.mk h)).range)
    (Fin ((f.map φℚ).natDegree))

/-- **The primitive-proper, Case-III-side slice of `IrreducibleBad`.**  An
irreducible bad polynomial whose Galois group (natural action on the roots)
is primitive, and which lies on the Case-III side of the eventual case
analysis in the strong (counting-region) sense: either `DD(u_f) = 0`, or
`DD(u_f) ≠ 0` and the large-prime part of the ramified product `C_f` above
the canonical threshold `⌈H^(1/(4n))⌉` exceeds `H` (paper subcase (ii),
with `A` computed from `C_f`). -/
noncomputable def PrimBadCaseIII (n H : ℕ) : Set ℤ[X] :=
  {f | f ∈ IrreducibleBad n H ∧
    ∃ h : Irreducible (f.map φℚ),
      galPrimitive f h ∧
        (concDDZ n (upperCoeffs n f) = 0 ∨
          (concDDZ n (upperCoeffs n f) ≠ 0 ∧
            H < largePart (@ramifiedProduct f (Fact.mk h)) (lowerThr (4 * n) H)))}

/-- **Entry of the primitive Case-III-side irreducible bad polynomials into
the counting regions.**  For `n ≥ 3`, every member of `PrimBadCaseIII n H`
lies in `DDzeroBox n H ∪ CaseIIISubcase2 n H (lowerThr (4n) H)`: the
`DD(u_f) = 0` members are the `DDzeroBox` polys (they are in `Box` since
`IrreducibleBad ⊆ Bad ⊆ Box`); the other members are primitive proper
(squarefull `D_f` by Jordan + Case I) with `DD(u_f) ≠ 0` and
`A_f > H`, hence lie in the subcase-(ii) region via
`mem_caseIIISubcase2_of_ramified_data`. -/
theorem PrimBadCaseIII_subset_DDzero_add_subcase2 (n H : ℕ) (hn : 3 ≤ n) :
    PrimBadCaseIII n H ⊆
      DDzeroBox n H ∪ CaseIIISubcase2 n H (lowerThr (4 * n) H) := by
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
      exact mem_caseIIISubcase2_of_ramified_data n H hn f hirr hfbox hsq' hddnz hA

/-- **The primitive Case-III-side slice is `O(H^(n-1))`.**  Members of
`PrimBadCaseIII` are contained in `DDzeroBox ∪ CaseIIISubcase2` (canonical
threshold), whose count is `O(H^(n-1))` by
`ddzero_add_subcase2_isBigO`; hence so is the slice itself. -/
theorem PrimBadCaseIII_isBigO (n : ℕ) (hn : 3 ≤ n) :
    (fun H : ℕ => ((PrimBadCaseIII n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  classical
  have hle : ∀ᶠ H : ℕ in atTop,
      (PrimBadCaseIII n H).ncard ≤
        (DDzeroBox n H).ncard + (CaseIIISubcase2 n H (lowerThr (4 * n) H)).ncard := by
    filter_upwards with H
    -- union is finite (both pieces sit inside the finite Box)
    have hfinD : (DDzeroBox n H).Finite := by
      apply (box_finite n H).subset
      intro f hf
      exact hf.1
    have hfinS : (CaseIIISubcase2 n H (lowerThr (4 * n) H)).Finite :=
      CaseIIISubcase2_finite n H (lowerThr (4 * n) H)
    have hfinU : (DDzeroBox n H ∪ CaseIIISubcase2 n H (lowerThr (4 * n) H)).Finite :=
      Set.Finite.union hfinD hfinS
    calc
      (PrimBadCaseIII n H).ncard
          ≤ (DDzeroBox n H ∪ CaseIIISubcase2 n H (lowerThr (4 * n) H)).ncard :=
        Set.ncard_le_ncard (PrimBadCaseIII_subset_DDzero_add_subcase2 n H hn) hfinU
      _ ≤ (DDzeroBox n H).ncard + (CaseIIISubcase2 n H (lowerThr (4 * n) H)).ncard :=
        Set.ncard_union_le _ _
  exact (Commons.Analysis.Asymptotics.isBigO_of_eventually_le
      (fun H : ℕ => (PrimBadCaseIII n H).ncard)
      (fun H : ℕ => (DDzeroBox n H).ncard + (CaseIIISubcase2 n H (lowerThr (4 * n) H)).ncard)
      hle).trans (ddzero_add_subcase2_isBigO n hn)


/-- **The primitive part of `IrreducibleBad`:** members whose Galois group
(natural action on the roots, via `irrGalFinHom`) is primitive.  (For such
members the group is automatically a *proper* subgroup of `Sₙ`: the natural
representation is faithful and `|Gal| < n!` from `Bad` membership, so
`range ≠ ⊤` — this is exactly the hypothesis under which the Case-I
squarefullness theorem applies, `squarefull_fieldDisc_of_primitive_card_lt`.) -/
noncomputable def PrimitiveBad (n H : ℕ) : Set ℤ[X] :=
  {f | f ∈ IrreducibleBad n H ∧ ∃ h : Irreducible (f.map φℚ), galPrimitive f h}

/-- **The imprimitive part of `IrreducibleBad`:** members whose Galois group
is not primitive.  (Every irreducible member's group is *transitive* on the
roots — `irrGalFinHom_pretransitive` — so "not primitive" is exactly
"imprimitive" here, the class covered by Widmer's bound
`O(H^(n/2+2))` in the eventual assembly.) -/
noncomputable def ImprimitiveBad (n H : ℕ) : Set ℤ[X] :=
  {f | f ∈ IrreducibleBad n H ∧ ¬ ∃ h : Irreducible (f.map φℚ), galPrimitive f h}

/-- **Primitive / imprimitive dichotomy of the irreducible bad polynomials.**
`IrreducibleBad n H = PrimitiveBad n H ∪ ImprimitiveBad n H` — the formal
split that organizes the remaining case analysis (primitive proper:
Cases I–III; imprimitive: Widmer). -/
theorem irrBad_eq_prim_union_imprim (n H : ℕ) :
    IrreducibleBad n H = PrimitiveBad n H ∪ ImprimitiveBad n H := by
  classical
  ext f
  constructor
  · intro hf
    by_cases hprim : ∃ h : Irreducible (f.map φℚ), galPrimitive f h
    · exact Or.inl ⟨hf, hprim⟩
    · exact Or.inr ⟨hf, hprim⟩
  · intro hf
    rcases hf with hf | hf <;> exact hf.1

/-- `PrimBadCaseIII` is a subset of the primitive part. -/
theorem PrimBadCaseIII_subset_PrimitiveBad (n H : ℕ) :
    PrimBadCaseIII n H ⊆ PrimitiveBad n H := by
  intro f hf
  rcases hf with ⟨hbad, h, hprim, hcases⟩
  exact ⟨hbad, h, hprim⟩


/-- **`A_f` (instance-free): the large-prime part of the ramified product
`C_f` above the canonical threshold `⌈H^(1/(4n))⌉`** — the paper's
`A = ∏_{p | C_f, p > H^(1/(4n))} p` with `δ = 1/(2n)`, `δ/2 = 1/(4n)`
(integers `p`: `p > H^(1/(4n))` ⟺ `⌈H^(1/(4n))⌉ ≤ p`).  This is the
subcase-(i)/(ii) split variable of Case III: `A_f > H` is subcase (ii)
(counted by `PrimBadCaseIII`/`CaseIIISubcase2`), `A_f ≤ H` is subcase (i). -/
noncomputable def A_large (n H : ℕ) (f : ℤ[X]) (h : Irreducible (f.map φℚ)) : ℕ :=
  largePart (@ramifiedProduct f (Fact.mk h)) (lowerThr (4 * n) H)

/-- **The subcase-(i)-side slice of the primitive part (the cover
complement of `PrimBadCaseIII`).**  An irreducible bad polynomial whose
Galois group is primitive, with `DD(u_f) ≠ 0` and `A_f ≤ H` (the paper's
Case-III subcase (i), but stated without the Case-III inequality `C_f >
H^(1+δ)`, so that together with `PrimBadCaseIII` it covers the *whole*
primitive part: every primitive-proper irreducible bad polynomial either has
`DD(u_f) = 0`, or subcase (ii) `A_f > H` (both in `PrimBadCaseIII`, already
`O(H^(n-1))`), or subcase (i) `A_f ≤ H` with `DD(u_f) ≠ 0` (here).  The
numerical bound of `SubcaseI` is exactly where the still-open research
threads enter: its members split (by the eventual `(C_f, D_f)`-region
analysis) into the Case-I side (`C_f ≤ H^(1+δ)`, `D_f > H^(2+2δ)` — needs
the Fourier extension `fbound2` for the per-D bound when `H < C_f ≤
H^(1+δ)`), the Case-II side (`D_f ≤ H^(2+2δ)` — field counting,
Schmidt/Lemke Oliver–Thorne), and the Case-III subcase (i) proper (Case I
argument with the intermediate divisor `B ∈ [H^(1+δ/2), H^(1+δ)]` of `C_f`
and `D' := ∏_{p | B} p^(v_p(D_f)) > H^(2+δ)` — again Fourier-gated since
`B > H`).  See the Roadmap Session-41 block for the full analysis. -/
noncomputable def SubcaseI (n H : ℕ) : Set ℤ[X] :=
  {f | f ∈ IrreducibleBad n H ∧
    ∃ h : Irreducible (f.map φℚ),
      galPrimitive f h ∧ concDDZ n (upperCoeffs n f) ≠ 0 ∧
        ¬ (H < A_large n H f h)}

/-- `SubcaseI` lies in the primitive part. -/
theorem SubcaseI_subset_PrimitiveBad (n H : ℕ) : SubcaseI n H ⊆ PrimitiveBad n H := by
  intro f hf
  rcases hf with ⟨hbad, h, hprim, hdd, hA⟩
  exact ⟨hbad, h, hprim⟩

/-- **Complete cover of the primitive part.**  `PrimitiveBad n H` splits
into the counted slice `PrimBadCaseIII n H` (DD = 0 or subcase (ii)
`A_f > H`) and the remainder `SubcaseI n H` (DD ≠ 0, subcase (i)
`A_f ≤ H`).  Together with the reducible count (`redBox_isBigO`) and the
future imprimitive bound (Widmer), bounding `SubcaseI` is what remains of
the irreducible half. -/
theorem PrimitiveBad_eq_primCaseIII_union_subcaseI (n H : ℕ) :
    PrimitiveBad n H = PrimBadCaseIII n H ∪ SubcaseI n H := by
  classical
  ext f
  constructor
  · intro hf
    rcases hf with ⟨hbad, h, hprim⟩
    by_cases hdd0 : concDDZ n (upperCoeffs n f) = 0
    · left
      exact ⟨hbad, h, hprim, Or.inl hdd0⟩
    · by_cases hA : H < A_large n H f h
      · left
        exact ⟨hbad, h, hprim, Or.inr ⟨hdd0, (by simpa [A_large] using hA)⟩⟩
      · right
        exact ⟨hbad, h, hprim, hdd0, hA⟩
  · intro hf
    rcases hf with hf | hf
    · exact PrimBadCaseIII_subset_PrimitiveBad n H hf
    · exact SubcaseI_subset_PrimitiveBad n H hf

/-- The two slices are disjoint (a member cannot be both counted by the
subcase-(ii)/DD-zero machinery and be in the subcase-(i) remainder). -/
theorem PrimBadCaseIII_disjoint_SubcaseI (n H : ℕ) :
    ∀ f : ℤ[X], f ∈ PrimBadCaseIII n H → f ∈ SubcaseI n H → False := by
  classical
  intro f hf1 hf2
  rcases hf2 with ⟨hbad2, h2, hprim2, hdd2, hA2⟩
  rcases hf1 with ⟨hbad1, h1⟩
  rcases h1 with ⟨hirr1, hprim1, hcases1⟩
  rcases hcases1 with hdd0 | hsub2
  · exact hdd2 hdd0
  · rcases hsub2 with ⟨hddnz, hA1⟩
    exact hA2 (by simpa [A_large] using hA1)

/-- **Counting-level split of the primitive part:** the number of
primitive-proper irreducible bad polynomials is at most the (counted)
`PrimBadCaseIII` slice plus the subcase-(i) remainder `SubcaseI`. -/
theorem ncard_primitiveBad_le (n H : ℕ) :
    (PrimitiveBad n H).ncard ≤ (PrimBadCaseIII n H).ncard + (SubcaseI n H).ncard := by
  classical
  calc
    (PrimitiveBad n H).ncard = (PrimBadCaseIII n H ∪ SubcaseI n H).ncard := by
      rw [PrimitiveBad_eq_primCaseIII_union_subcaseI]
    _ ≤ (PrimBadCaseIII n H).ncard + (SubcaseI n H).ncard := Set.ncard_union_le _ _

/-- **Squarefullness of every primitive-proper irreducible bad polynomial**
(instance-free membership form): the field discriminant `D_f` of a member of
`PrimitiveBad` is squarefull (Jordan + Case I: primitive + `|Gal| < n!`
forces no transposition on the roots, and a once-dividing prime would give
one).  This is the shared structural input of the Case I / Case III
counting for the whole primitive half. -/
theorem PrimitiveBad_exists_squarefull_fieldDisc (n H : ℕ) (f : ℤ[X])
    (hf : f ∈ PrimitiveBad n H) :
    ∃ h : Irreducible (f.map φℚ),
      galPrimitive f h ∧ Squarefull (fieldDiscExp f h) := by
  classical
  rcases hf with ⟨hbad, h, hprim⟩
  have hfbox : f ∈ Box n H := Bad_subset_Box n H (irreducibleBad_subset_Bad n H hbad)
  have hmon : f.Monic := hfbox.1
  have hnat : f.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some hfbox.2.1
  haveI : Fact (Irreducible (f.map φℚ)) := ⟨h⟩
  have hnd : (f.map φℚ).natDegree = n := by
    rw [monic_natDegree_map_rat f hmon, hnat]
  have hcard : Nat.card (f.map φℚ).Gal < ((f.map φℚ).natDegree).factorial := by
    rw [hnd]
    change Nat.card (f.map (algebraMap ℤ ℚ)).Gal < n.factorial
    exact hbad.1.2.2.2
  have hsq : Squarefull (fieldDisc f) :=
    squarefull_fieldDisc_of_primitive_card_lt f hmon hprim hcard
  exact ⟨h, hprim, (by simpa [fieldDiscExp] using hsq)⟩

end Submission.Vdw
