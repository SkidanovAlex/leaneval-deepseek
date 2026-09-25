import Mathlib
import Submission.Commons.NumberTheory.NumberField.abs_discr_le_of_rootDiscr_le
import Submission.Work.CMRealSubfield.Defs
import Submission.Work.CMRealSubfield.Archimedean
import Submission.Work.CMRealSubfield.Walls
import Submission.Work.CMRealSubfield.RootDiscr.rootDiscr_le_of_abs_discr_le
import Submission.Work.CMRealSubfield.RootDiscr.rootDiscr_maximalRealSubfield_le_rootDiscr
import Submission.Work.CMRealSubfield.RealSubfield.le_finrank_maximalRealSubfield_of_two_mul_le

/-!
# The real-subfield reduction: from bounded-root-discriminant families to the benchmark

This is the main module of the subproject.  It proves that the benchmark statement

  `∃ C > 0, ∀ N, ∃ d ≥ N, ∃ K totally real, [K : ℚ] = d ∧ |discr K| ≤ C ^ d`

follows from a bounded-root-discriminant family of **CM** fields (or, more generally, of
fields whose maximal real subfield has at least half the degree — `HalfRealSubfieldWall`).

## The argument

Let `L` be a CM number field of degree `≥ 2N` with `|discr L| ≤ C ^ [L : ℚ]`, and let
`L⁺ = NumberField.maximalRealSubfield L` be its maximal real subfield.

1. `L⁺` is totally real (Mathlib's `isTotallyReal_maximalRealSubfield`), and
   `[L : ℚ] = 2 * [L⁺ : ℚ]` (`RealSubfield.finrank_eq_two_mul_finrank_maximalRealSubfield`),
   so `[L⁺ : ℚ] ≥ N`.
2. `rootDiscr L⁺ ≤ rootDiscr L` (`RealSubfield.rootDiscr_maximalRealSubfield_le_of_isCMField`,
   from `(discr L⁺) ^ 2 ∣ discr L`), and `rootDiscr L ≤ C`
   (`RootDiscr.rootDiscr_le_of_abs_discr_le`, using `C > 0`).
3. `|discr L⁺| ≤ C ^ [L⁺ : ℚ]`
   (`Commons.NumberTheory.NumberField.abs_discr_le_of_rootDiscr_le`).

So the *same* constant `C` works: no total-reality was needed in the hypothesis, and no
constant is lost.  If the witnesses are totally real instead, we simply take `K = L`.

## What is *not* claimed

The bare `WeakWall` (no CM hypothesis, no structural hypothesis on the real subfield) is
**not** enough for this argument, and the module makes the gap explicit rather than hiding it:
`benchmark_of_weakWall_of_halfDegreeRealSubfieldInput` reduces the bare wall using the input
`HalfDegreeRealSubfieldInput` (a totally real subfield of at least half the degree with no
larger root discriminant), which is exactly what CM witnesses supply.  That input is *false*
in general — e.g. for `ℚ(∜2, i)`, of degree `8`, whose maximal real subfield is `ℚ(√2)` of
degree `2`.  So the arithmetic input the benchmark really consumes is a family of CM fields
(or a family whose maximal real subfields are of half degree), not an arbitrary bounded
root-discriminant family.
-/

open NumberField

set_option linter.style.haveILetI false

namespace Work.CMRealSubfield

/-- Root-discriminant form of the benchmark implies the benchmark (the commons bridge
`Commons.NumberTheory.NumberField.abs_discr_le_of_rootDiscr_le`). -/
theorem benchmark_of_rootDiscrBenchmark (h : RootDiscrBenchmark) : Benchmark := by
  obtain ⟨C, hC, hfam⟩ := h
  refine ⟨C, hC, fun N => ?_⟩
  obtain ⟨d, hd, K, hF, hNF, hTR, hfin, hrd⟩ := hfam N
  exact ⟨d, hd, K, hF, hNF, hTR, hfin,
    Commons.NumberTheory.NumberField.abs_discr_le_of_rootDiscr_le hfin hrd⟩

/-- The benchmark implies its root-discriminant form. -/
theorem rootDiscrBenchmark_of_benchmark (h : Benchmark) : RootDiscrBenchmark := by
  obtain ⟨C, hC, hfam⟩ := h
  refine ⟨C, hC, fun N => ?_⟩
  obtain ⟨d, hd, K, hF, hNF, hTR, hfin, hdisc⟩ := hfam N
  exact ⟨d, hd, K, hF, hNF, hTR, hfin,
    RootDiscr.rootDiscr_le_of_abs_discr_le K hfin hC hdisc⟩

/-- The two shapes of the benchmark are equivalent. -/
theorem benchmark_iff_rootDiscrBenchmark : Benchmark ↔ RootDiscrBenchmark :=
  ⟨rootDiscrBenchmark_of_benchmark, benchmark_of_rootDiscrBenchmark⟩

/-- **The engine of the reduction.**  A bounded-root-discriminant family whose members have a
maximal real subfield of at least half the degree (`HalfRealSubfieldWall`) yields the
root-discriminant benchmark, with the same constant. -/
theorem rootDiscrBenchmark_of_halfRealSubfieldWall (h : HalfRealSubfieldWall) :
    RootDiscrBenchmark := by
  obtain ⟨C, hC, hfam⟩ := h
  refine ⟨C, hC, fun N => ?_⟩
  obtain ⟨L, hF, hNF, hdeg, hdisc, hhalf⟩ := hfam (2 * N)
  letI := hF
  letI := hNF
  have hN : N ≤ Module.finrank ℚ (NumberField.maximalRealSubfield L) := by omega
  refine ⟨Module.finrank ℚ (NumberField.maximalRealSubfield L), hN,
    NumberField.maximalRealSubfield L, inferInstance, inferInstance, inferInstance, rfl, ?_⟩
  exact le_trans (RootDiscr.rootDiscr_maximalRealSubfield_le_rootDiscr L)
    (RootDiscr.rootDiscr_le_of_abs_discr_le L rfl hC hdisc)

/-- The half-degree-real-subfield wall implies the benchmark. -/
theorem benchmark_of_halfRealSubfieldWall (h : HalfRealSubfieldWall) : Benchmark :=
  benchmark_of_rootDiscrBenchmark (rootDiscrBenchmark_of_halfRealSubfieldWall h)

/-- **The reduction from the CM wall.**  Bounded-root-discriminant families of **CM** fields of
unbounded degree give the benchmark, with the same constant `C`: the maximal real subfield of a
CM field has half the degree, is totally real, and does not increase the root discriminant. -/
theorem rootDiscrBenchmark_of_cmWall (h : CMWall) : RootDiscrBenchmark := by
  obtain ⟨C, hC, hfam⟩ := h
  refine ⟨C, hC, fun N => ?_⟩
  obtain ⟨L, hF, hNF, hCM, hdeg, hdisc⟩ := hfam (2 * N)
  letI := hF
  letI := hNF
  letI := hCM
  refine ⟨Module.finrank ℚ (NumberField.maximalRealSubfield L),
    RealSubfield.le_finrank_maximalRealSubfield_of_two_mul_le L hdeg,
    NumberField.maximalRealSubfield L, inferInstance, inferInstance, inferInstance, rfl, ?_⟩
  exact le_trans (RootDiscr.rootDiscr_maximalRealSubfield_le_rootDiscr L)
    (RootDiscr.rootDiscr_le_of_abs_discr_le L rfl hC hdisc)

/-- The CM wall implies the benchmark. -/
theorem benchmark_of_cmWall (h : CMWall) : Benchmark :=
  benchmark_of_rootDiscrBenchmark (rootDiscrBenchmark_of_cmWall h)

/-- **The reduction from the totally-real-or-CM wall.**  Here the totally real witnesses are
used directly (`K = L`) and the CM witnesses are halved. -/
theorem benchmark_of_realOrCMWall (h : RealOrCMWall) : Benchmark := by
  obtain ⟨C, hC, hfam⟩ := h
  refine ⟨C, hC, fun N => ?_⟩
  obtain ⟨L, hF, hNF, hTRorCM, hdeg, hdisc⟩ := hfam (2 * N)
  letI := hF
  letI := hNF
  have hN : N ≤ Module.finrank ℚ L := by omega
  rcases hTRorCM with hTR | hCM
  · exact ⟨Module.finrank ℚ L, hN, L, hF, hNF, hTR, rfl, hdisc⟩
  · letI := hCM
    refine ⟨Module.finrank ℚ (NumberField.maximalRealSubfield L),
      RealSubfield.le_finrank_maximalRealSubfield_of_two_mul_le L hdeg,
      NumberField.maximalRealSubfield L, inferInstance, inferInstance, inferInstance, rfl, ?_⟩
    refine Commons.NumberTheory.NumberField.abs_discr_le_of_rootDiscr_le rfl ?_
    exact le_trans (RootDiscr.rootDiscr_maximalRealSubfield_le_rootDiscr L)
      (RootDiscr.rootDiscr_le_of_abs_discr_le L rfl hC hdisc)

/-- **The bare weak wall with the missing input made explicit.**  If a bounded-root-discriminant
family of arbitrary number fields exists (`WeakWall`) *and* every number field has a totally real
subfield of at least half the degree with no larger root discriminant
(`HalfDegreeRealSubfieldInput`), then the benchmark follows (with the same constant).  The second
hypothesis is what the CM hypothesis supplies; it is false in general, which is why the bare
`WeakWall` alone does not feed the elementary real-subfield reduction. -/
theorem benchmark_of_weakWall_of_halfDegreeRealSubfieldInput
    (hw : WeakWall) (hsub : HalfDegreeRealSubfieldInput) : Benchmark := by
  obtain ⟨C, hC, hfam⟩ := hw
  refine ⟨C, hC, fun N => ?_⟩
  obtain ⟨L, hF, hNF, hdeg, hdisc⟩ := hfam (4 * N)
  letI := hF
  letI := hNF
  obtain ⟨E, hEF, hENF, hTR, hhalf, hrd⟩ := hsub L
  letI := hEF
  letI := hENF
  have hE : N ≤ Module.finrank ℚ E := by omega
  have hrdC : NumberField.rootDiscr E ≤ C :=
    le_trans hrd (RootDiscr.rootDiscr_le_of_abs_discr_le L rfl hC hdisc)
  exact ⟨Module.finrank ℚ E, hE, E, hEF, hENF, hTR, rfl,
    Commons.NumberTheory.NumberField.abs_discr_le_of_rootDiscr_le rfl hrdC⟩

/-- **Tower interface (absolute-discriminant form).**  A sequence of CM number fields of
degree `≥ n` with `|discr| ≤ C ^ [F n : ℚ]` gives the benchmark.  This is the form in which a
tower construction (e.g. an unramified or CM pro-`2` tower with bounded root discriminant)
supplies the arithmetic input. -/
theorem benchmark_of_cm_tower {F : ℕ → Type} [∀ n : ℕ, Field (F n)]
    [∀ n : ℕ, NumberField (F n)] [∀ n : ℕ, NumberField.IsCMField (F n)]
    (C : ℝ) (hC : 0 < C) (hdeg : ∀ n : ℕ, n ≤ Module.finrank ℚ (F n))
    (hdisc : ∀ n : ℕ, |(NumberField.discr (F n) : ℝ)| ≤ C ^ Module.finrank ℚ (F n)) :
    Benchmark :=
  benchmark_of_cmWall
    ⟨C, hC, fun N => ⟨F N, inferInstance, inferInstance, inferInstance, hdeg N, hdisc N⟩⟩

/-- **Tower interface (root-discriminant form).**  A sequence of CM number fields of degree
`≥ n` with `rootDiscr (F n) ≤ C` (equivalently: a CM tower with root discriminant bounded by
a fixed constant, the situation of the source paper) gives the benchmark, with the same
constant `C`. -/
theorem rootDiscrBenchmark_of_cm_tower {F : ℕ → Type} [∀ n : ℕ, Field (F n)]
    [∀ n : ℕ, NumberField (F n)] [∀ n : ℕ, NumberField.IsCMField (F n)]
    (C : ℝ) (hC : 0 < C) (hdeg : ∀ n : ℕ, n ≤ Module.finrank ℚ (F n))
    (hrd : ∀ n : ℕ, NumberField.rootDiscr (F n) ≤ C) :
    RootDiscrBenchmark :=
  rootDiscrBenchmark_of_cmWall
    ⟨C, hC, fun N => ⟨F N, inferInstance, inferInstance, inferInstance, hdeg N,
      Commons.NumberTheory.NumberField.abs_discr_le_of_rootDiscr_le rfl (hrd N)⟩⟩

/-- The tower form of the reduction, in the shape of the benchmark itself. -/
theorem benchmark_of_cm_tower_rootDiscr {F : ℕ → Type} [∀ n : ℕ, Field (F n)]
    [∀ n : ℕ, NumberField (F n)] [∀ n : ℕ, NumberField.IsCMField (F n)]
    (C : ℝ) (hC : 0 < C) (hdeg : ∀ n : ℕ, n ≤ Module.finrank ℚ (F n))
    (hrd : ∀ n : ℕ, NumberField.rootDiscr (F n) ≤ C) : Benchmark :=
  benchmark_of_rootDiscrBenchmark (rootDiscrBenchmark_of_cm_tower C hC hdeg hrd)

/-- **Tower interface for totally complex towers with half-degree real subfields.**  A tower
whose levels are totally complex and satisfy `2 * [F n⁺ : ℚ] = [F n : ℚ]` is a CM tower
(`cmWall_of_totallyComplexHalfWall`), hence gives the benchmark.  This is the interface for the
towers coming out of the source construction: the arithmetic input is *only* that the complex
conjugation of each level has an index-two fixed field, i.e. that the level is CM. -/
theorem benchmark_of_totallyComplexHalf_tower {F : ℕ → Type} [∀ n : ℕ, Field (F n)]
    [∀ n : ℕ, NumberField (F n)] [∀ n : ℕ, NumberField.IsTotallyComplex (F n)]
    (C : ℝ) (hC : 0 < C) (hdeg : ∀ n : ℕ, n ≤ Module.finrank ℚ (F n))
    (hhalf : ∀ n : ℕ, 2 * Module.finrank ℚ (NumberField.maximalRealSubfield (F n)) =
      Module.finrank ℚ (F n))
    (hdisc : ∀ n : ℕ, |(NumberField.discr (F n) : ℝ)| ≤ C ^ Module.finrank ℚ (F n)) :
    Benchmark :=
  benchmark_of_cmWall
    (cmWall_of_totallyComplexHalfWall
      ⟨C, hC, fun N => ⟨F N, inferInstance, inferInstance,
        ⟨inferInstance, hhalf N⟩, hdeg N, hdisc N⟩⟩)

/-- **Tower interface for totally complex towers with bounded root discriminant.**  Same as
`benchmark_of_totallyComplexHalf_tower`, with the arithmetic input given in the shape of a
constant root-discriminant bound along the tower. -/
theorem benchmark_of_totallyComplexHalf_tower_rootDiscr {F : ℕ → Type} [∀ n : ℕ, Field (F n)]
    [∀ n : ℕ, NumberField (F n)] [∀ n : ℕ, NumberField.IsTotallyComplex (F n)]
    (C : ℝ) (hC : 0 < C) (hdeg : ∀ n : ℕ, n ≤ Module.finrank ℚ (F n))
    (hhalf : ∀ n : ℕ, 2 * Module.finrank ℚ (NumberField.maximalRealSubfield (F n)) =
      Module.finrank ℚ (F n))
    (hrd : ∀ n : ℕ, NumberField.rootDiscr (F n) ≤ C) : Benchmark :=
  benchmark_of_cmWall
    (cmWall_of_totallyComplexHalfWall
      ⟨C, hC, fun N => ⟨F N, inferInstance, inferInstance,
        ⟨inferInstance, hhalf N⟩, hdeg N,
        Commons.NumberTheory.NumberField.abs_discr_le_of_rootDiscr_le rfl (hrd N)⟩⟩)

/-- **The reduction from the CM-extension wall.**  Bounded-root-discriminant quadratic totally
complex extensions of totally real fields of unbounded degree give the benchmark, with the same
constant (the totally real field at level `N` is the base of a witness of degree `≥ 2N`). -/
theorem rootDiscrBenchmark_of_cmExtensionWall (h : CMExtensionWall) : RootDiscrBenchmark :=
  rootDiscrBenchmark_of_cmWall (cmWall_of_cmExtensionWall h)

/-- The CM-extension wall implies the benchmark. -/
theorem benchmark_of_cmExtensionWall (h : CMExtensionWall) : Benchmark :=
  benchmark_of_rootDiscrBenchmark (rootDiscrBenchmark_of_cmExtensionWall h)

end Work.CMRealSubfield
