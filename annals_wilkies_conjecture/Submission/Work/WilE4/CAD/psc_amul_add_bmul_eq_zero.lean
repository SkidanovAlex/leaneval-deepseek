import Mathlib

namespace Work.WilE4.CAD

/-- **Triviality of the kernel of `(A, B) ↦ A * f + B * g` modulo low-degree terms.**

For nonzero `f g : ℝ[X]`, write `G = gcd f g`.  If `A * f + B * g` has degree `< deg G`, while
`deg A < deg (g / G)` and `deg B < deg (f / G)`, then `A = 0` and `B = 0`.

Indeed `A * f + B * g = G * (A * (f / G) + B * (g / G))`, so the degree hypothesis forces
`A * (f / G) + B * (g / G) = 0`; coprimality of `f / G` and `g / G` then gives `g / G ∣ A`,
say `A = (g / G) * s`, and `deg A < deg (g / G)` forces `s = 0`, whence `B = 0` as well. -/
theorem psc_amul_add_bmul_eq_zero {f g : Polynomial ℝ} (hf : f ≠ 0) (hg : g ≠ 0)
    {A B : Polynomial ℝ}
    (hA : A ∈ Polynomial.degreeLT ℝ (g / gcd f g).natDegree)
    (hB : B ∈ Polynomial.degreeLT ℝ (f / gcd f g).natDegree)
    (h : A * f + B * g ∈ Polynomial.degreeLT ℝ (gcd f g).natDegree) : A = 0 ∧ B = 0 := by
  have hGne : gcd f g ≠ 0 := by
    intro h0
    exact hf ((gcd_eq_zero_iff f g).mp h0).1
  have hGf : gcd f g * (f / gcd f g) = f :=
    EuclideanDomain.mul_div_cancel' hGne (gcd_dvd_left f g)
  have hGg : gcd f g * (g / gcd f g) = g :=
    EuclideanDomain.mul_div_cancel' hGne (gcd_dvd_right f g)
  have hgf_ne : g / gcd f g ≠ 0 := right_div_gcd_ne_zero hg
  -- `A * f + B * g = gcd f g * (A * (f / gcd) + B * (g / gcd))`.
  have hkey : A * f + B * g
      = gcd f g * (A * (f / gcd f g) + B * (g / gcd f g)) := by
    calc A * f + B * g
        = A * (gcd f g * (f / gcd f g)) + B * (gcd f g * (g / gcd f g)) := by
            rw [hGf, hGg]
      _ = gcd f g * (A * (f / gcd f g) + B * (g / gcd f g)) := by ring
  -- Hence the inner combination must vanish: otherwise the degree of the product would
  -- be at least the degree of `gcd f g`.
  have hC : A * (f / gcd f g) + B * (g / gcd f g) = 0 := by
    by_contra hCne
    rw [hkey, Polynomial.mem_degreeLT] at h
    rw [Polynomial.degree_eq_natDegree (mul_ne_zero hGne hCne),
        Polynomial.natDegree_mul hGne hCne] at h
    have h2 : (gcd f g).natDegree
        + (A * (f / gcd f g) + B * (g / gcd f g)).natDegree < (gcd f g).natDegree :=
      WithBot.coe_lt_coe.mp h
    omega
  -- The cofactors are coprime, so `g / gcd` divides `A`.
  have hcop : IsCoprime (g / gcd f g) (f / gcd f g) :=
    (isCoprime_div_gcd_div_gcd (p := f) (q := g) hg).symm
  have hdiv : g / gcd f g ∣ A := by
    refine hcop.dvd_of_dvd_mul_right ?_
    have hAeq : A * (f / gcd f g) = -(B * (g / gcd f g)) := eq_neg_of_add_eq_zero_left hC
    rw [hAeq]
    exact dvd_neg.mpr (dvd_mul_of_dvd_right (dvd_refl _) B)
  obtain ⟨s, hs⟩ := hdiv
  -- `deg A < deg (g / gcd)` and `g / gcd ∣ A` force `A = 0`.
  have hA0 : A = 0 := by
    by_contra hAne
    have hsne : s ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hs; exact hAne hs
    have hdeg : A.natDegree = (g / gcd f g).natDegree + s.natDegree := by
      rw [hs, Polynomial.natDegree_mul hgf_ne hsne]
    have hlt : A.natDegree < (g / gcd f g).natDegree :=
      (Polynomial.natDegree_lt_iff_degree_lt hAne).mpr (Polynomial.mem_degreeLT.mp hA)
    omega
  refine ⟨hA0, ?_⟩
  -- Then `B * (g / gcd) = 0` with `g / gcd ≠ 0` gives `B = 0`.
  have hB0 : B * (g / gcd f g) = 0 := by
    rw [hA0, zero_mul, zero_add] at hC
    exact hC
  exact (mul_eq_zero.mp hB0).resolve_right hgf_ne

end Work.WilE4.CAD
