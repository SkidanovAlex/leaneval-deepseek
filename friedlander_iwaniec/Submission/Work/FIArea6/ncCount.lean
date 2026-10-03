/-
# `Submission.Work.FIArea6.ncCount` — the counting step of the coprimality removal

The estimate
`ncPairCount Pa φ d ≤ Σ_{g ∈ ncGset Pa} (2√(2N/|g|²) + 1)² (8(2N/|g|²)/(4d) + 8√(2N/|g|²) + 8)`
which is the combinatorial content of the coprimality removal of (16.4): for a pair `(z₁,z₂)` of the
polar box that is free of small primes (5.8) and non-coprime, the gcd `g = (z₁,z₂)` satisfies
`Pz < |g|² ≤ 2N` (5.8), and writing `zᵢ = g uᵢ` the pair `(u₁,u₂)` has `4d ∣ |Δ(u₁,u₂)|` because
`(|g|², 4d) = 1`; the coset count `ncFiberCount` at the scaled box of radius `√(2N/|g|²)` bounds
the number of `u₂` for each `u₁`, while the number of `u₁` is `(2√(2N/|g|²)+1)²` because
`|gu₁|² = |g|²|u₁|² ≤ 2N`.
-/
import Mathlib
import Submission.Work.FIArea6.S16UDefs
import Submission.Work.FIArea6.ncHelpers

set_option autoImplicit false

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- A Gaussian integer of norm `≤ r` lies in the box of radius `⌈√r⌉₊`. -/
lemma ncMem_gBox_sqrt {z : GaussianInt} {r : ℝ}
    (hr : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ r) :
    z ∈ Work.FIPlan.gBox (⌈Real.sqrt r⌉₊ : ℤ) := by
  have hle : Real.sqrt r ≤ ((⌈Real.sqrt r⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hgn : ∀ w : ℤ, (w = z.re ∨ w = z.im) → |(w:ℝ)| ≤ ((⌈Real.sqrt r⌉₊ : ℕ) : ℝ) := by
    intro w hw
    have h1 : ((w:ℝ))^2 ≤ ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
      have hcoords := ncGnorm_coords z
      rcases hw with rfl | rfl
      · have h3 : z.re ^ 2 ≤ (Work.FIPlan.gnorm z : ℤ) := by
          rw [hcoords]; nlinarith [sq_nonneg z.im]
        exact_mod_cast h3
      · have h3 : z.im ^ 2 ≤ (Work.FIPlan.gnorm z : ℤ) := by
          rw [hcoords]; nlinarith [sq_nonneg z.re]
        exact_mod_cast h3
    calc |(w:ℝ)| = Real.sqrt ((w:ℝ)^2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt r := Real.sqrt_le_sqrt (le_trans h1 hr)
      _ ≤ ((⌈Real.sqrt r⌉₊ : ℕ) : ℝ) := hle
  rw [Work.FIPlan.gBox, Finset.mem_image]
  refine ⟨(z.re, z.im), Finset.mem_product.mpr ⟨?_, ?_⟩, by cases z; rfl⟩
  · rw [Finset.mem_Icc]
    have h := hgn z.re (Or.inl rfl)
    rw [abs_le] at h
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  · rw [Finset.mem_Icc]
    have h := hgn z.im (Or.inr rfl)
    rw [abs_le] at h
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- The number of `z₁ ∈ ncBox` that are multiples of a fixed `g ∈ ncGset` is at most the number of
Gaussian integers of norm `≤ 2N/|g|²`. -/
lemma ncMultCount (Pa : Work.FITop.Params) (φ : ℝ) {g : GaussianInt} (hg : g ∈ ncGset Pa) :
    (((ncBox Pa φ).filter (fun z => g ∣ z)).card : ℝ)
      ≤ (2 * Real.sqrt (2 * Pa.N / ((Work.FIPlan.gnorm g : ℕ) : ℝ)) + 1) ^ 2 := by
  classical
  set G : ℝ := ((Work.FIPlan.gnorm g : ℕ) : ℝ) with hGdef
  have hG1 : (1:ℝ) ≤ G := ncGset_one_le hg
  have hGpos : (0:ℝ) < G := lt_of_lt_of_le zero_lt_one hG1
  have h2N : (0:ℝ) ≤ 2 * Pa.N := by have := Pa.hN1; linarith
  have hsub : ((ncBox Pa φ).filter (fun z => g ∣ z)) ⊆
      ((Work.FIPlan.gBox (⌈Real.sqrt (2 * Pa.N / G)⌉₊ : ℤ)).filter
        (fun u => ((Work.FIPlan.gnorm u : ℕ) : ℝ) ≤ 2 * Pa.N / G)).image (fun u => g * u) := by
    intro z hz
    obtain ⟨hzA, hgdz⟩ := Finset.mem_filter.mp hz
    obtain ⟨u, rfl⟩ := hgdz
    have hgu : ((Work.FIPlan.gnorm (g * u) : ℕ) : ℝ) ≤ 2 * Pa.N := ncBox_gnorm_le Pa φ hzA
    have hmul : ((Work.FIPlan.gnorm (g * u) : ℕ) : ℝ) = G * ((Work.FIPlan.gnorm u : ℕ) : ℝ) := by
      rw [hGdef, ncga_gnorm_mul]; push_cast; ring
    have huG : ((Work.FIPlan.gnorm u : ℕ) : ℝ) ≤ 2 * Pa.N / G := by
      rw [le_div_iff₀ hGpos]
      rw [hmul] at hgu
      linarith
    exact Finset.mem_image.mpr
      ⟨u, Finset.mem_filter.mpr ⟨ncMem_gBox_sqrt huG, huG⟩, rfl⟩
  calc (((ncBox Pa φ).filter (fun z => g ∣ z)).card : ℝ)
      ≤ ((((Work.FIPlan.gBox (⌈Real.sqrt (2 * Pa.N / G)⌉₊ : ℤ)).filter
        (fun u => ((Work.FIPlan.gnorm u : ℕ) : ℝ) ≤ 2 * Pa.N / G)).image
          (fun u => g * u)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (((Work.FIPlan.gBox (⌈Real.sqrt (2 * Pa.N / G)⌉₊ : ℤ)).filter
        (fun u => ((Work.FIPlan.gnorm u : ℕ) : ℝ) ≤ 2 * Pa.N / G)).card : ℝ) := by
        exact_mod_cast Finset.card_image_le
    _ ≤ (2 * Real.sqrt (2 * Pa.N / G) + 1) ^ 2 := ncCardGn_le (2 * Pa.N / G)

end

end Work.FIArea6
