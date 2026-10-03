import Mathlib
import Submission.Work.FIPlan.Interface

namespace Work.FIArea2

/-! ### Auxiliary facts for `coprime_re_absDelta`

The proof is the prime-divisor argument of the sketch: a rational prime `p` dividing both
`Re(z̄₁z₂)` and `Im(z̄₁z₂)` divides the Gaussian integer `z̄₁z₂`, hence also each Gaussian prime
`π | p`; splitting `π | z̄₁z₂` and `π̄ | z̄₁z₂` and using that `π` is not a unit (it divides both
members of a coprime pair) leaves only contradictions with `(z₁,z₂) = (z₁,z̄₁) = (z₂,z̄₂) = 1`. -/

/-- **A common divisor of a coprime pair is a unit.**  If `IsCoprime x y` (i.e. `a * x + b * y = 1`
for some `a`, `b`) and `d` divides both `x` and `y`, then `d ∣ 1`. -/
lemma gaussCoprimeAux_isUnit_of_dvd {R : Type*} [CommSemiring R] {d x y : R}
    (h : IsCoprime x y) (hx : d ∣ x) (hy : d ∣ y) : IsUnit d := by
  obtain ⟨a, b, hab⟩ := h
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hy
  exact isUnit_of_dvd_one ⟨a * x' + b * y', by rw [← hab]; ring⟩

/-- **Conjugation under divisibility in `ℤ[i]`**: `star a ∣ b ↔ a ∣ star b`. -/
lemma gaussStar_dvd_iff {a b : GaussianInt} : star a ∣ b ↔ a ∣ star b := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨star c, ?_⟩
    have h := congrArg star hc
    simp only [star_mul, star_star] at h
    rw [h, mul_comm]
  · rintro ⟨c, hc⟩
    refine ⟨star c, ?_⟩
    have h := congrArg star hc
    simp only [star_mul, star_star] at h
    rw [h, mul_comm]

/-- **Conjugation preserves divisibility in `ℤ[i]`**: `star a ∣ star b ↔ a ∣ b`. -/
lemma gaussStar_dvd_star_iff {a b : GaussianInt} : star a ∣ star b ↔ a ∣ b := by
  rw [gaussStar_dvd_iff, star_star]

/-- **The conjugate of a Gaussian prime is a Gaussian prime.** -/
lemma gaussPrime_star {π : GaussianInt} (hπ : Prime π) : Prime (star π) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    refine hπ.ne_zero ?_
    rw [← star_star π, h, star_zero]
  · intro h
    exact hπ.not_isUnit (by simpa using h.star)
  · intro a b hab
    obtain ⟨c, hc⟩ := hab
    have h : π ∣ star b * star a := by
      refine ⟨star c, ?_⟩
      have hh := congrArg star hc
      simp only [star_mul, star_star] at hh
      rw [hh, mul_comm]
    rcases hπ.dvd_or_dvd h with hb | ha
    · exact Or.inr (gaussStar_dvd_iff.mpr hb)
    · exact Or.inl (gaussStar_dvd_iff.mpr ha)

/-- **The automatic coprimality of `Re(z̄₁z₂)` and `|Δ|`**: if `(z₁,z₂) = (z₁,z̄₁) = (z₂,z̄₂) = 1` then no rational prime divides both `Re(z̄₁z₂)` and `Im(z̄₁z₂)`.  This is the hypothesis `(a,|Δ|) = 1` that Corollary 8.3 / the corrected (8.16) (`Cnt_eq_two_sum`) needs, since the residue `a` of `z₂/z₁` satisfies `a·|z₁|² ≡ Re(z̄₁z₂) (mod |Δ|)` while `(|z₁|²,|Δ|) = 1` (`coprime_gnorm_absDelta`).

**Both** primitivity hypotheses are needed: `z₁ = 3+2i`, `z₂ = 5` satisfies `(z₁,z₂) = 1` and `(z₁,z̄₁) = 1` but gives `Re(z̄₁z₂) = 15`, `|Δ| = 10`; there `5 ∣ z₂` and `(z₂,z̄₂) ≠ 1`.  With `(z₂,z̄₂) = 1` no rational prime divides `z₂`, and the argument closes (see the sketch).

Sketch: `z̄₁z₂ = Re(z̄₁z₂) + iΔ`, so a prime `p` dividing both divides the Gaussian integer `z̄₁z₂`; hence `π | z̄₁z₂` for every `π | p`.  `π | z̄₁` forces `π̄ | z₁` and then `π̄ | z₂` (the other alternative `π̄ | z̄₁` would make `p | z₁z̄₁`), so `π̄` divides both `z₁` and `z₂`, contradicting `(z₁,z₂) = 1`.  Symmetrically `π | z₂` leads to `π | z₁` or to `π, π̄ | z₂`, contradicting `(z₁,z₂) = 1` or `(z₂,z̄₂) = 1`.  (The degenerate `Δ = 0` case has `z₁, z₂` both units, hence `|Re(z̄₁z₂)| = 1`.) -/
theorem coprime_re_absDelta {z1 z2 : GaussianInt}
    (h12 : Work.FIPlan.GaussCoprime z1 z2) (h1 : IsCoprime z1 (star z1))
    (h2 : IsCoprime z2 (star z2)) :
    Nat.Coprime ((star z1 * z2).re).natAbs (Work.FIPlan.absDelta z1 z2) := by
  refine Nat.coprime_of_dvd ?_
  intro p hp hpre hpd
  -- `p` divides both coordinates of `N = z̄₁z₂`
  set N : GaussianInt := star z1 * z2 with hN
  have hpim : p ∣ N.im.natAbs := hpd
  have hpre' : p ∣ N.re.natAbs := hpre
  have hzre : (p : ℤ) ∣ N.re := by
    rw [← Int.dvd_natAbs]
    exact_mod_cast hpre'
  have hzim : (p : ℤ) ∣ N.im := by
    rw [← Int.dvd_natAbs]
    exact_mod_cast hpim
  have hpdN : (p : GaussianInt) ∣ N := by
    have h := (Zsqrtd.intCast_dvd (p : ℤ) N).mpr ⟨hzre, hzim⟩
    simpa using h
  -- `p` is not a unit of `ℤ[i]`, and not zero
  have hpunit : ¬ IsUnit (p : GaussianInt) := by
    intro hu
    have h1' : (p : GaussianInt).norm.natAbs = 1 := Zsqrtd.norm_eq_one_iff.mpr hu
    rw [Zsqrtd.norm_natCast, Int.natAbs_mul, Int.natAbs_natCast] at h1'
    nlinarith [hp.two_le]
  have hpzero : (p : GaussianInt) ≠ 0 := by
    intro h
    have hre : (p : GaussianInt).re = 0 := by rw [h]; rfl
    rw [Zsqrtd.re_natCast] at hre
    exact hp.ne_zero (by exact_mod_cast hre)
  -- a Gaussian prime `π` dividing `p`
  obtain ⟨π, hπirr, hπdvd⟩ := WfDvdMonoid.exists_irreducible_factor hpunit hpzero
  have hπprime : Prime π := irreducible_iff_prime.mp hπirr
  -- the two splittings
  have hπN : π ∣ N := hπdvd.trans hpdN
  have hsplit1 : π ∣ star z1 ∨ π ∣ z2 := by
    rw [hN] at hπN
    exact hπprime.dvd_or_dvd hπN
  have hπstarP : star π ∣ (p : GaussianInt) := by
    have h := gaussStar_dvd_star_iff.mpr hπdvd
    simpa using h
  have hπstarN : star π ∣ N := hπstarP.trans hpdN
  have hπstarprime : Prime (star π) := gaussPrime_star hπprime
  have hsplit2 : π ∣ z1 ∨ star π ∣ z2 := by
    rw [hN] at hπstarN
    rcases hπstarprime.dvd_or_dvd hπstarN with hh | hh
    · exact Or.inl (gaussStar_dvd_star_iff.mp hh)
    · exact Or.inr hh
  -- case analysis
  rcases hsplit2 with hA | hE
  · rcases hsplit1 with hB | hC
    · exact hπprime.not_isUnit (gaussCoprimeAux_isUnit_of_dvd h1 hA hB)
    · exact hπprime.not_isUnit (gaussCoprimeAux_isUnit_of_dvd h12 hA hC)
  · rcases hsplit1 with hB | hC
    · have hspz1 : star π ∣ z1 := gaussStar_dvd_iff.mpr hB
      have hunit : IsUnit (star π) := gaussCoprimeAux_isUnit_of_dvd h12 hspz1 hE
      exact hπprime.not_isUnit (by simpa using hunit.star)
    · have hspz2 : π ∣ star z2 := gaussStar_dvd_iff.mp hE
      exact hπprime.not_isUnit (gaussCoprimeAux_isUnit_of_dvd h2 hC hspz2)

end Work.FIArea2
