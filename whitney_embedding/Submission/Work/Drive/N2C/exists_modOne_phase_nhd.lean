import Mathlib
import Submission.Work.Drive.N2C.circlePhase

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set

/-- **The phase patch can be shrunk to make the phase an honest "parameter mod 1".**

A continuous curve `γ : ℝ → M` of period `1` which is injective on `Ico 0 1` (equivalently: the
induced map of the circle is injective) is locally, modulo the period, injective.  Hence if `φ` is a
smooth function on a neighbourhood `U` of `γ t₀` which equals the parameter `t` on `Ioo (t₀-δ) (t₀+δ)`
(with `2δ ≤ 1`, so that this interval is at most a fundamental domain), then `φ` computes the
parameter modulo `1` on a (smaller) neighbourhood `U'` of `γ t₀`: every parameter `t` with
`γ t ∈ U'` differs from `φ (γ t)` by an integer.

The proof is purely topological: the complement of the compact image of the closed interval
`Icc (t₀+δ) (t₀+1-δ)` (which misses `γ t₀` by injectivity) is an open neighbourhood of `γ t₀` whose
points, pulled back to a fundamental domain `[t₀, t₀+1)`, can only be hit near `t₀` or near `t₀+1`,
i.e. at parameters congruent to `t₀` modulo `1`. -/
theorem exists_modOne_phase_nhd {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
    {γ : ℝ → M} (hγc : Continuous γ) (hper : Function.Periodic γ 1)
    (hinj : Set.InjOn γ (Set.Ico 0 1))
    {t₀ : ℝ} {U : Set M} {φ : M → ℝ} (hU : IsOpen U) (hUt : γ t₀ ∈ U)
    (hφ : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) φ U)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : 2 * δ ≤ 1)
    (hφγ : ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), φ (γ t) = t) :
    ∃ U' : Set M, IsOpen U' ∧ γ t₀ ∈ U' ∧ U' ⊆ U ∧
      ∀ y ∈ U', ∀ t : ℝ, γ t = y → ∃ k : ℤ, φ y = t + k := by
  classical
  -- the compact "far" piece of the fundamental domain `[t₀, t₀+1)`
  set C : Set ℝ := Set.Icc (t₀ + δ) (t₀ + 1 - δ) with hCdef
  have hCcomp : IsCompact C := isCompact_Icc
  have hCclosed : IsClosed (γ '' C) := hCcomp.image hγc |>.isClosed
  refine ⟨(γ '' C)ᶜ ∩ U, hCclosed.isOpen_compl.inter hU, ⟨?_, hUt⟩, Set.inter_subset_right, ?_⟩
  · -- `γ t₀ ∉ γ '' C`
    rintro ⟨c, hc, hcγ⟩
    obtain ⟨k, hk⟩ := eq_add_int_of_eq_of_periodic hper hinj hcγ
    -- `hk : c = t₀ + k`, and `c ∈ C` forces `δ ≤ k ≤ 1 - δ`
    have hk1 : (0 : ℝ) < (k : ℝ) := by
      have := hc.1; linarith
    have hk2 : (k : ℝ) < 1 := by
      have := hc.2; linarith
    have hk1' : (0 : ℤ) < k := by exact_mod_cast hk1
    have hk2' : k < 1 := by exact_mod_cast hk2
    omega
  · -- the phase property on the smaller neighbourhood
    intro y hy t hyt
    have hyV : y ∉ γ '' C := hy.1
    -- move `t` into the fundamental domain `[t₀, t₀+1)` by an integer shift
    set u : ℝ := Int.fract (t - t₀) with hudef
    set n : ℤ := ⌊t - t₀⌋ with hndef
    have hu0 : 0 ≤ u := Int.fract_nonneg _
    have hu1 : u < 1 := Int.fract_lt_one _
    have hnu : (n : ℝ) + u = t - t₀ := by
      rw [hudef, hndef]; exact Int.floor_add_fract _
    have hs't : γ (t₀ + u) = γ t := by
      have h1 : γ (t₀ + u) = γ ((t₀ + u) + (n • (1:ℝ))) := ((hper.zsmul n) (t₀ + u)).symm
      rw [zsmul_one] at h1
      rwa [show t₀ + u + (n : ℝ) = t from by linarith] at h1
    rcases lt_or_ge u δ with huδ | huδ
    · -- `t₀ + u` itself lies in the good interval
      have hs : t₀ + u ∈ Set.Ioo (t₀ - δ) (t₀ + δ) := ⟨by linarith, by linarith⟩
      obtain ⟨k, hk⟩ := eq_add_int_of_eq_of_periodic hper hinj hs't
      have hφy : φ y = t₀ + u := by
        rw [← hyt, ← hs't]
        exact hφγ (t₀ + u) hs
      exact ⟨k, by rw [hφy, hk]⟩
    · -- `u ≥ δ`: the shifted parameter `t₀ + u` is outside the bad compact set `C`
      have huC : ¬ (u ≤ 1 - δ) := by
        intro hu
        have : γ (t₀ + u) ∈ γ '' C := ⟨t₀ + u, ⟨by linarith, by linarith⟩, rfl⟩
        exact hyV (by rw [hs't, hyt] at this; exact this)
      have hu' : 1 - δ < u := not_le.mp huC
      have hs : t₀ + u - 1 ∈ Set.Ioo (t₀ - δ) (t₀ + δ) := ⟨by linarith, by linarith⟩
      have hper1 : γ (t₀ + u - 1) = γ (t₀ + u) := by
        have h1 := (hper (t₀ + u - 1)).symm
        rwa [show (t₀ + u - 1) + 1 = t₀ + u from by ring] at h1
      have hγs : γ (t₀ + u - 1) = γ t := by rw [hper1, hs't]
      obtain ⟨k, hk⟩ := eq_add_int_of_eq_of_periodic hper hinj hγs
      have hφy : φ y = t₀ + u - 1 := by
        rw [← hyt, ← hs't, ← hper1]
        exact hφγ (t₀ + u - 1) hs
      exact ⟨k, by rw [hφy, hk]⟩

end Work.Drive.N2C
