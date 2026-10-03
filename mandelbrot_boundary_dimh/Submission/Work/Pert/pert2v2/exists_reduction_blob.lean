import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.basin_iface
import Submission.Work.Pert.pert2v2.DE_add_one

/-!
# `exists_reduction_blob` — reduction of a compact subset of `d.DE` modulo `ℤ`

For a parabolic germ `f₀` with §4.1 data `d : ParabData f₀ D₀`, the domain of the lifted horn map
`d.DE = d.Dφ ∩ φ₀⁻¹(Basin)` is invariant under every integer translation
(`Work.L62.basin_iface`: forward invariance of the basin from `orbit_avoid` + `d.φ_abel`,
backward invariance from the definition of the basin).  Hence a compact set `K ⊆ d.DE` can be
"reduced" into the unit vertical strip `|Re z| ≤ 1` by translating each of its points by an
integer, and the resulting set is again a compact subset of `d.DE`:

  `∃ Z, IsCompact Z ∧ Z ⊆ d.DE ∧ (∀ z ∈ Z, |z.re| ≤ 1) ∧ ∀ k ∈ K, ∃ z ∈ Z, ∃ n : ℤ, k = z + n`.

This is the reduction blob used to move the compact `K` of the two-piece return-map design
(`NOTES_pert2v2_session40_assembly.md` §1 d) into the `Re`-window of the low chart, where the
cover of `K ∪ {y₁ ≤ |Im ·|}` is stated.

The reduction is the explicit set

  `Z = ⋃ n ∈ Icc (-(N+1)) (N+1), ((· - n) '' K ∩ {|Re ·| ≤ 1})`,

where `N` bounds `|Re k|` for `k ∈ K`; the integer attached to `k` is `⌊Re k⌋ + 1`, which puts
`(k - n).re ∈ [-1, 0]`.  The `Re`-bound makes the union finite, hence `Z` compact.
-/

namespace Work.Pert.pert2v2

open MandelDim Set

/-- **`d.DE` is closed under every integer translation.**  Immediate from
`Work.L62.basin_iface` (`d.DE` is `ℤ`-invariant) and `MandelDim.IsTInvariant.add_int`. -/
theorem DE_sub_int {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀) {w : ℂ} (hw : w ∈ d.DE) (n : ℤ) :
    w - (n : ℂ) ∈ d.DE := by
  have hT : MandelDim.IsTInvariant d.DE :=
    (Work.L62.basin_iface f₀ D₀ d hd d.orbit_avoid).2.2.2.1
  have h : w + ((-n : ℤ) : ℂ) ∈ d.DE := Work.Horn.MandelDim.IsTInvariant.add_int hT hw (-n)
  have hcast : w + ((-n : ℤ) : ℂ) = w - (n : ℂ) := by push_cast; ring
  rwa [hcast] at h

theorem exists_reduction_blob {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀) {K : Set ℂ} (hK : IsCompact K) (hKDE : K ⊆ d.DE) :
    ∃ Z : Set ℂ, IsCompact Z ∧ Z ⊆ d.DE ∧ (∀ z ∈ Z, |z.re| ≤ 1) ∧
      ∀ k ∈ K, ∃ z ∈ Z, ∃ n : ℤ, k = z + (n : ℂ) := by
  -- `K` is bounded, so its real parts are bounded by a natural number
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨N, hN⟩ := exists_nat_ge R
  set B : ℤ := (N : ℤ) + 1 with hB
  refine ⟨⋃ n ∈ (Finset.Icc (-B) B : Set ℤ),
      ((fun z : ℂ => z - (n : ℂ)) '' K ∩ {z : ℂ | |z.re| ≤ 1}), ?_, ?_, ?_, ?_⟩
  · -- compactness: a finite union of compact pieces
    refine (Finset.finite_toSet (Finset.Icc (-B) B)).isCompact_biUnion ?_
    intro n _
    exact (hK.image (continuous_id.sub continuous_const)).inter_right
      (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const)
  · -- the blob stays in `d.DE`
    rintro z hz
    obtain ⟨n, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨-, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hkz, -⟩ := hz
    obtain ⟨k, hkK, hkz⟩ := hkz
    rw [← hkz]
    exact DE_sub_int d hd (hKDE hkK) n
  · -- the blob lies in the unit strip
    rintro z hz
    obtain ⟨n, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨-, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨-, hzre⟩ := hz
    exact hzre
  · -- every `k ∈ K` has a translate in the blob
    intro k hkK
    have hkn : ‖k‖ ≤ R := hR k hkK
    have hkre : |k.re| ≤ (N : ℝ) :=
      calc |k.re| ≤ ‖k‖ := Complex.abs_re_le_norm k
        _ ≤ R := hkn
        _ ≤ (N : ℝ) := hN
    set n : ℤ := ⌊k.re⌋ + 1 with hn
    have hncast : (n : ℝ) = (⌊k.re⌋ : ℝ) + 1 := by simp [hn]
    have hn_le : n ≤ B := by
      have h1 : (⌊k.re⌋ : ℝ) ≤ k.re := Int.floor_le k.re
      have h2 : k.re ≤ (N : ℝ) := le_trans (le_abs_self k.re) hkre
      have h3 : (n : ℝ) ≤ (B : ℝ) := by rw [hncast, hB]; push_cast; linarith
      exact_mod_cast h3
    have hn_ge : -B ≤ n := by
      have h1 : k.re < (⌊k.re⌋ : ℝ) + 1 := Int.lt_floor_add_one k.re
      have h2 : -(N : ℝ) ≤ k.re := (abs_le.mp hkre).1
      have h3 : ((-B - 1 : ℤ) : ℝ) < (n : ℝ) := by rw [hncast, hB]; push_cast; linarith
      have h4 : (-B - 1 : ℤ) < n := by exact_mod_cast h3
      omega
    have hzre : |(k - (n : ℂ)).re| ≤ 1 := by
      have h1 : (k - (n : ℂ)).re = k.re - (n : ℝ) := by
        rw [Complex.sub_re]
        simp
      have h2 : (n : ℝ) - k.re ≤ 1 := by
        have h := Int.floor_le k.re
        rw [hncast]; linarith
      have h3 : 0 ≤ (n : ℝ) - k.re := by
        have h := Int.lt_floor_add_one k.re
        rw [hncast]; linarith
      rw [h1, abs_of_nonpos (by linarith)]
      linarith
    refine ⟨k - (n : ℂ), ?_, n, by ring⟩
    refine Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · show n ∈ (Finset.Icc (-B) B : Set ℤ)
      rw [Finset.mem_coe, Finset.mem_Icc]
      exact ⟨hn_ge, hn_le⟩
    · exact ⟨⟨k, hkK, rfl⟩, hzre⟩

end Work.Pert.pert2v2
