import Mathlib

/-!
# Shared multiset / multiplicity lemmas for the sequential cluster argument

This module collects the small, self-contained facts about roots and root multiplicities that the
cluster argument uses.  It imports nothing but `Mathlib`, so it can be imported cheaply by the
lemmas that build on it.
-/

namespace Work.WilE4.CAD

open Polynomial

/-- If all roots of `p` in the disk of radius `ρ` about `t₀` are equal to `z`, and the number of
roots in that disk is `μ`, then the multiplicity of `z` is `μ`. -/
theorem rootMultiplicity_eq_of_filter_card {p : Polynomial ℂ} {z t₀ : ℂ} {ρ : ℝ} {μ : ℕ}
    (hzroot : p.IsRoot z) (hzdisk : dist z t₀ < ρ)
    (huniq : ∀ w : ℂ, p.IsRoot w → dist w t₀ < ρ → w = z)
    (hcard : (p.roots.filter (fun w => dist w t₀ < ρ)).card = μ) :
    p.rootMultiplicity z = μ := by
  by_cases hp : p = 0
  · subst hp
    have hcard0 : μ = 0 := by
      rw [← hcard]
      simp
    rw [hcard0, Polynomial.rootMultiplicity_zero]
  · have hEq : p.roots.filter (Eq z) = p.roots.filter (fun w => dist w t₀ < ρ) := by
      refine Multiset.filter_congr fun w hw => ?_
      constructor
      · intro hwz
        simpa [hwz] using hzdisk
      · intro hwd
        exact (huniq w ((Polynomial.mem_roots hp).mp hw) hwd).symm
    calc p.rootMultiplicity z = p.roots.count z := (Polynomial.count_roots p).symm
      _ = (p.roots.filter (Eq z)).card := Multiset.count_eq_card_filter_eq p.roots z
      _ = (p.roots.filter (fun w => dist w t₀ < ρ)).card := by rw [hEq]
      _ = μ := hcard

/-- The multiplicity of a root of the gcd of two complex polynomials is the minimum of the
multiplicities. -/
theorem rootMultiplicity_gcdC (f g : Polynomial ℂ) (hf : f ≠ 0) (hg : g ≠ 0) (z : ℂ) :
    (gcd f g).rootMultiplicity z = min (f.rootMultiplicity z) (g.rootMultiplicity z) := by
  have hgcd : gcd f g ≠ 0 := by
    intro h
    have hd : gcd f g ∣ f := gcd_dvd_left f g
    rw [h] at hd
    exact hf (zero_dvd_iff.mp hd)
  have ha : (Polynomial.X - Polynomial.C z) ^ (gcd f g).rootMultiplicity z ∣ gcd f g :=
    Polynomial.pow_rootMultiplicity_dvd (gcd f g) z
  apply le_antisymm
  · apply le_min
    · exact (Polynomial.le_rootMultiplicity_iff hf).mpr (ha.trans (gcd_dvd_left f g))
    · exact (Polynomial.le_rootMultiplicity_iff hg).mpr (ha.trans (gcd_dvd_right f g))
  · refine (Polynomial.le_rootMultiplicity_iff hgcd).mpr ?_
    exact dvd_gcd
      (dvd_trans (pow_dvd_pow _ (min_le_left _ _)) (Polynomial.pow_rootMultiplicity_dvd f z))
      (dvd_trans (pow_dvd_pow _ (min_le_right _ _)) (Polynomial.pow_rootMultiplicity_dvd g z))

/-- A non-zero real polynomial has `conj`-stable roots after embedding into `ℂ`. -/
theorem isRoot_conj_of_isRoot {f : Polynomial ℝ} {z : ℂ}
    (hz : (f.map (algebraMap ℝ ℂ)).IsRoot z) :
    (f.map (algebraMap ℝ ℂ)).IsRoot (starRingEnd ℂ z) := by
  have hmap : (f.map (algebraMap ℝ ℂ)).map (starRingEnd ℂ) = f.map (algebraMap ℝ ℂ) := by
    rw [Polynomial.map_map]
    congr 1
    ext r
    simp
  have := Polynomial.IsRoot.map (f := starRingEnd ℂ) hz
  rwa [hmap] at this

/-- The conjugation is an isometry of `ℂ`. -/
theorem dist_conj (z w : ℂ) : dist (starRingEnd ℂ z) (starRingEnd ℂ w) = dist z w := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, Complex.norm_conj]

/-- A complex number fixed by the conjugation is the embedding of its real part. -/
theorem ofReal_re_of_conj_eq (z : ℂ) (h : starRingEnd ℂ z = z) : ((z.re : ℂ) = z) := by
  have him : z.im = 0 := by
    have h1 : (starRingEnd ℂ z).im = z.im := by rw [h]
    simp only [Complex.conj_im] at h1
    linarith
  exact Complex.ext rfl (by simp [him])

end Work.WilE4.CAD
