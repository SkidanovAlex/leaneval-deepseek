import Mathlib
import Submission.Work.DSM5b.H0Defs
import Submission.Work.DSM5b.HCd_comp
import Submission.Work.DSM5b.honestVanishingDefs
import Submission.Work.DSM5b.honestVanishingBlock
import Submission.Work.DSM5b.honestVanishingRaise

namespace Work.DSM5b

open DSMap DSMap.Mix DSMap.Mix2

universe a

set_option linter.unusedSectionVars false

/-!
# Vanishing of the honest chart Čech cohomology above the number of charts

The honest coordinate complex `HCX t •` / `HCd t •` (`Submission/Work/DSM5b/H0Defs.lean`) is the
unnormalized (tuples with repetitions) chart Čech complex of the cover `{D₊(t_i)}` of
`Bl_J (Spec R)`, `J = (t_i)`.  The theorem `Work.DSM5b.honestCohomologyVanishing` below says that
its cohomology vanishes in all degrees `≥ ♯ι`.

The proof is the *image-size filtration*, mirroring `Submission/Work/DSEQ0/cech_raise.lean`:

* `Work.DSM5b.honestVanishingBlock` (`Submission/Work/DSM5b/honestVanishingBlock.lean`): for a
  `j`-element set `S ⊆ ι`, the restriction of a cocycle `z` (which vanishes on tuples of
  range-cardinality `< j`) to the block of tuples with range exactly `S` is a coboundary — the
  block is the *surjection complex* of the finite type `↥S` with **constant** coefficients
  `chartRing t S`, so `Work.DSEQ0.surj_tuple_vanishing` applies;
* `Work.DSM5b.honestVanishingRaise` (`Submission/Work/DSM5b/honestVanishingRaise.lean`): the sum of
  the block solutions over all `S` with `card S = j` raises the support level of `z` by one;
* `cocycle_is_coboundary` below: the descending induction on the support level, starting from `♯ι`
  (where the support condition is vacuous), gives the vanishing.
-/

/-- **The descending induction of the image-size filtration.**  For a finite index type `ι` with
`Nat.card ι ≤ K+1`, every cycle of the honest chart Čech complex in degree `K+1` is a coboundary.

The level-`j` statement `P j` says that this holds for every cocycle supported on tuples whose range
has at least `j` elements.  `P (♯ι)` is the base case (every range has at most `♯ι` elements, so the
support condition is vacuous); the step `P (j+1) → P j` uses `honestVanishingRaise` with the block
solutions supplied by `honestVanishingBlock` to subtract a coboundary, reducing the support level by
one.  Descending to `P 0` gives the claim. -/
theorem cocycle_is_coboundary {ι : Type a} [Fintype ι] [DecidableEq ι] {R : Type a} [CommRing R]
    (t : ι → R) (K : ℕ) (hK : Nat.card ι ≤ K + 1) (z : HCX t (K + 1))
    (hz : HCd t (K + 1) z = 0) : ∃ y : HCX t K, HCd t K y = z := by
  classical
  let P : ℕ → Prop := fun j => ∀ z : HCX t (K + 1), HCd t (K + 1) z = 0 → SuppAbove j z →
    ∃ y : HCX t K, HCd t K y = z
  have hbase : P (Nat.card ι) := by
    intro z hz hsupp
    obtain ⟨y, hy⟩ := honestVanishingRaise t hK z hsupp
      (fun S hS => honestVanishingBlock t hS hK z hsupp hz)
    refine ⟨y, ?_⟩
    have hzero : z - HCd t K y = 0 := by
      funext τ
      exact hy τ (lt_of_le_of_lt (card_tupRng_le τ) (lt_add_one _))
    exact (sub_eq_zero.mp hzero).symm
  have hstep : ∀ j, j ≤ K + 1 → P (j + 1) → P j := by
    intro j hj hnext z hz hsupp
    obtain ⟨y, hy⟩ := honestVanishingRaise t hj z hsupp
      (fun S hS => honestVanishingBlock t hS hj z hsupp hz)
    have hcomp : HCd t (K + 1) (HCd t K y) = 0 := by
      have h := LinearMap.congr_fun (HCd_comp t K) y
      rwa [LinearMap.comp_apply, LinearMap.zero_apply] at h
    have hz' : HCd t (K + 1) (z - HCd t K y) = 0 := by
      rw [map_sub, hz, hcomp, sub_zero]
    obtain ⟨y', hy'⟩ := hnext (z - HCd t K y) hz' hy
    exact ⟨y + y', by rw [map_add, hy']; abel⟩
  have hkey : P 0 := by
    have hchain : ∀ d : ℕ, ∀ j : ℕ, j + d = Nat.card ι → P j := by
      intro d
      induction d with
      | zero =>
        intro j hj
        rw [show j = Nat.card ι from by omega]
        exact hbase
      | succ d ih =>
        intro j hj
        exact hstep j (by omega) (ih (j + 1) (by omega))
    exact hchain (Nat.card ι) 0 (by omega)
  exact hkey z hz (suppAbove_zero_eq)

/-- **Vanishing of the honest chart Čech cohomology above the number of charts.**
`HCX t m = ∀ τ : Fin (m+1) → ι, chartRing t (tupRng τ)` and `HCd t m` are the coordinates of the
honest chart Čech complex (`Submission/Work/DSM5b/H0Defs.lean`), the (unnormalized, tuples with
repetitions) Čech complex of the chart cover `{D₊(t_i)}` of `Bl_J (Spec R)`, `J = (t_i)`.  Claim:
in every degree `n+1 ≥ ♯ι` every cycle is a boundary.

Suggested routes (both reviewers confirm the statement, that its threshold is sharp, and that it is
not vacuous; note Mathlib's Dold–Kan is *simplicial*, so the cosimplicial version has to be
instantiated or redone):
* **Route A (normalization, integral homotopy).**  Show that the honest complex is quasi-isomorphic
  to the alternating/subset-indexed one, e.g. via the degenerate-part acyclicity; the
  subset-indexed complex has no terms in degrees `≥ ♯ι`, so `H^{n+1} = 0` for `n+1 ≥ ♯ι`.
  Concretely, the codegeneracies `X(σ^i) : C^m → C^{m-1}`, `(X(σ) z) τ := rhoH (...) (z (τ ∘ σ))`
  exist and satisfy the cosimplicial identities, so (dual `DoldKan.alternatingCofaceMapComplex` /
  `ExtraDegeneracy`) the unnormalized complex has the homology of the normalized one.
* **Route B (elementary, by induction on `♯ι`, no normalization needed).**  Fix `j₀ : ι`.  The
  complex `Ĉ^m = ∏_{τ : Fin (m+1) → ι} chartRing t (tupRng τ ∪ {j₀})` (larger chart rings, *same*
  index rings on both sides of the degeneracy `tupIns j₀`) has the contraction `h : Ĉ^m → Ĉ^{m-1}`,
  `(hy) τ := y (tupIns j₀ τ)`, with `HCd ∘ h + h ∘ HCd = id` in positive degrees (check
  `(tupIns j₀ τ) ∘ δ^0 = τ` and `tupIns j₀ (τ ∘ δ^i) = (tupIns j₀ τ) ∘ δ^{i+1}`, no localization
  isomorphism is needed); combined with the inclusion of complexes `C ↪ Ĉ` it yields
  `H^{m+1}(C) ≅ H^m(Ĉ/C)` for `m ≥ 1`, and `Ĉ/C` is the honest complex of `ι \ {j₀}` with the
  coefficient system `S ↦ chartRing t (S ∪ {j₀})/chartRing t S`.  Iterating `♯ι` times gives the
  vanishing.  (This iteration needs the statement for general coefficient systems of the shape
  arising, but that is again elementary homological algebra over `R`-modules.)

The proof formalised here is neither of the two suggested routes: it is the *image-size filtration*
of `Submission/Work/DSEQ0/cech_raise.lean` (which replaces Route B's induction on `♯ι` by the
filtration whose graded pieces are the surjection complexes with constant coefficients), with the
purely combinatorial input `Work.DSEQ0.surj_tuple_vanishing`.  Its two filtration ingredients are
`Work.DSM5b.honestVanishingBlock` and `Work.DSM5b.honestVanishingRaise`; the descending induction is
`Work.DSM5b.cocycle_is_coboundary` above. -/
theorem honestCohomologyVanishing {R : Type a} [CommRing R] {ι : Type a} [Finite ι] [DecidableEq ι]
    (t : ι → R) (n : ℕ) (hn : Nat.card ι ≤ n + 1) :
    ∀ z : HCX t (n + 1), HCd t (n + 1) z = 0 → z ∈ LinearMap.range (HCd t n) := by
  intro z hz
  haveI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨y, hy⟩ := cocycle_is_coboundary t n hn z hz
  exact LinearMap.mem_range.mpr ⟨y, hy⟩

end Work.DSM5b
