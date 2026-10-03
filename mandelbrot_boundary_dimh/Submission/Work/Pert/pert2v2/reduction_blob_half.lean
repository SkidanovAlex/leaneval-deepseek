import Mathlib
import Submission.Work.Pert.pert2v2.exists_reduction_blob

namespace Work.Pert.pert2v2

open MandelDim Set

/-!
# `reduction_blob_half` — reduction of a compact subset of `d.DE` into the half strip

Strengthening of `Work.Pert.pert2v2.exists_reduction_blob`: a compact `K ⊆ d.DE` can be reduced
modulo `ℤ` into the *half* unit strip `|Re z| ≤ 1/2` (rather than `|Re z| ≤ 1`), the blob again
being a compact subset of `d.DE`.

`d.DE` is invariant under every integer translation (`Work.Pert.pert2v2.DE_sub_int`, from
`Work.L62.basin_iface` + `MandelDim.IsTInvariant.add_int`), so the reduction is the explicit set

  `Z = ⋃ n ∈ Icc (-B) B, ((· - n) '' K ∩ {|Re ·| ≤ 1/2}),`

with `B = N + 1` bounding `|Re k|` for `k ∈ K`; the integer attached to `k` is `⌊Re k + 1/2⌋`,
which is the nearest integer to `Re k`, so `|Re(k - n)| ≤ 1/2`.  The half-width makes the union
finite, hence `Z` compact.
-/

theorem reduction_blob_half {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀) {K : Set ℂ} (hK : IsCompact K) (hKDE : K ⊆ d.DE) :
    ∃ Z : Set ℂ, IsCompact Z ∧ Z ⊆ d.DE ∧ (∀ z ∈ Z, |z.re| ≤ 1 / 2) ∧
      ∀ k ∈ K, ∃ z ∈ Z, ∃ n : ℤ, k = z + (n : ℂ) := by
  -- `K` is bounded, so its real parts are bounded by a natural number
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨N, hN⟩ := exists_nat_ge R
  set B : ℤ := (N : ℤ) + 1 with hB
  refine ⟨⋃ n ∈ (Finset.Icc (-B) B : Set ℤ),
      ((fun z : ℂ => z - (n : ℂ)) '' K ∩ {z : ℂ | |z.re| ≤ 1 / 2}), ?_, ?_, ?_, ?_⟩
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
  · -- the blob lies in the half strip
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
    set n : ℤ := ⌊k.re + 1 / 2⌋ with hn
    have hf_le : (n : ℝ) ≤ k.re + 1 / 2 := by
      rw [hn]; exact Int.floor_le _
    have hf_lt : k.re + 1 / 2 < (n : ℝ) + 1 := by
      rw [hn]; exact Int.lt_floor_add_one _
    have hn_le : n ≤ B := by
      have h1 : k.re ≤ (N : ℝ) := le_trans (le_abs_self k.re) hkre
      have h2 : (n : ℝ) < (B : ℝ) := by rw [hB]; push_cast; linarith
      have h3 : n < B := by exact_mod_cast h2
      omega
    have hn_ge : -B ≤ n := by
      have h1 : -(N : ℝ) ≤ k.re := (abs_le.mp hkre).1
      have h2 : ((-B : ℤ) : ℝ) < (n : ℝ) := by rw [hB]; push_cast; linarith
      have h3 : (-B : ℤ) < n := by exact_mod_cast h2
      omega
    have hzre : |(k - (n : ℂ)).re| ≤ 1 / 2 := by
      have h1 : (k - (n : ℂ)).re = k.re - (n : ℝ) := by
        rw [Complex.sub_re]
        simp
      have h2 : k.re - (n : ℝ) ≤ 1 / 2 := by linarith
      have h3 : -(1 / 2 : ℝ) ≤ k.re - (n : ℝ) := by linarith
      rw [h1]
      exact abs_le.mpr ⟨h3, h2⟩
    refine ⟨k - (n : ℂ), ?_, n, by ring⟩
    refine Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · show n ∈ (Finset.Icc (-B) B : Set ℤ)
      rw [Finset.mem_coe, Finset.mem_Icc]
      exact ⟨hn_ge, hn_le⟩
    · exact ⟨⟨k, hkK, rfl⟩, hzre⟩

end Work.Pert.pert2v2
