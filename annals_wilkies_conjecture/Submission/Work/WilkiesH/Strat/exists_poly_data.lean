import Mathlib

namespace Work.WilkiesH.Strat

open Polynomial

/-- Clearing denominators of `p ∈ S[X]` via `integerNormalization`. -/
private lemma intNorm_data {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (p : Polynomial S) :
    ∃ b ∈ M, (IsLocalization.integerNormalization M p).map (algebraMap R S)
      = Polynomial.C (algebraMap R S b) * p := by
  obtain ⟨b, hb, hb_eq⟩ := IsLocalization.integerNormalization_spec M p
  exact ⟨b, hb, by rw [hb_eq, Algebra.smul_def, Polynomial.algebraMap_apply]⟩

theorem exists_poly_data {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (f : Polynomial R) (hf : f ≠ 0) :
    ∃ (G D A B W : Polynomial R) (n : ℕ) (c γ lam : R),
      c ≠ 0 ∧ γ ≠ 0 ∧ lam ≠ 0 ∧
      Polynomial.C c * f = D * G ∧
      D * W = Polynomial.C γ * G ^ n ∧
      Polynomial.C lam = A * G + B * Polynomial.derivative G := by
  classical
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  have hφinj : Function.Injective φ := IsFractionRing.injective R K
  have hfK : f.map φ ≠ 0 := fun h => hf ((Polynomial.map_eq_zero_iff hφinj).mp h)
  let g : Polynomial K := UniqueFactorizationMonoid.radical (f.map φ)
  have hg_ne : g ≠ 0 := UniqueFactorizationMonoid.radical_ne_zero
  have hg_dvd : g ∣ f.map φ := UniqueFactorizationMonoid.radical_dvd_self
  obtain ⟨m, hm⟩ := UniqueFactorizationMonoid.exists_dvd_radical_self_pow hfK
  have hsep : g.Separable := (PerfectField.separable_iff_squarefree).mpr
    (UniqueFactorizationMonoid.squarefree_radical (a := f.map φ))
  have hcop : IsCoprime g (Polynomial.derivative g) := (Polynomial.separable_def g).mp hsep
  obtain ⟨al, bl, hab⟩ := hcop
  -- Clear denominators of the radical and of its cofactor in `f`.
  let G : Polynomial R := IsLocalization.integerNormalization (nonZeroDivisors R) g
  obtain ⟨b, hb_mem, hG_K₀⟩ := intNorm_data (nonZeroDivisors R) g
  have hG_K : G.map φ = Polynomial.C (φ b) * g := hG_K₀
  have hb_ne : b ≠ 0 := nonZeroDivisors.ne_zero hb_mem
  obtain ⟨h, hh⟩ := hg_dvd
  let H : Polynomial R := IsLocalization.integerNormalization (nonZeroDivisors R) h
  obtain ⟨c, hc_mem, hH_K₀⟩ := intNorm_data (nonZeroDivisors R) h
  have hH_K : H.map φ = Polynomial.C (φ c) * h := hH_K₀
  have hc_ne : c ≠ 0 := nonZeroDivisors.ne_zero hc_mem
  have h1 : Polynomial.C (c * b) * f = G * H := by
    apply Polynomial.map_injective φ hφinj
    simp only [Polynomial.map_mul, Polynomial.map_C]
    rw [hG_K, hH_K, hh, map_mul, Polynomial.C_mul]
    ring
  -- The exponent `m + 1` and the cleared cofactor of `G ^ (m+1)` in `f`.
  have hm1 : f.map φ ∣ g ^ (m + 1) := hm.trans (pow_dvd_pow g (Nat.le_succ m))
  obtain ⟨h2q, hh2q⟩ := hm1
  have hG2 : (G.map φ) ^ (m + 1) = (f.map φ) * (Polynomial.C (φ b) ^ (m + 1) * h2q) := by
    rw [hG_K, mul_pow, hh2q]
    ring
  let e2 : Polynomial K := Polynomial.C (φ b) ^ (m + 1) * h2q
  let H2 : Polynomial R := IsLocalization.integerNormalization (nonZeroDivisors R) e2
  obtain ⟨d, hd_mem, hH2_K₀⟩ := intNorm_data (nonZeroDivisors R) e2
  have hH2_K : H2.map φ = Polynomial.C (φ d) * e2 := hH2_K₀
  have hd_ne : d ≠ 0 := nonZeroDivisors.ne_zero hd_mem
  have h2 : Polynomial.C d * G ^ (m + 1) = f * H2 := by
    apply Polynomial.map_injective φ hφinj
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C]
    rw [hG2, hH2_K]
    ring
  -- Bézout relation between `G` and its derivative over `K[X]`.
  let u : K := (φ b)⁻¹
  have hbK_ne : φ b ≠ 0 := fun h0 => hb_ne (hφinj (by simpa using h0))
  have hgK_ne : g ≠ 0 := hg_ne
  have hG_ne : G ≠ 0 := by
    intro h0
    have hmap : G.map φ = 0 := by rw [h0, Polynomial.map_zero]
    rw [hG_K] at hmap
    exact (mul_ne_zero (Polynomial.C_ne_zero.mpr hbK_ne) hgK_ne) hmap
  have hg_eq : g = Polynomial.C u * (G.map φ) := by
    change g = Polynomial.C ((φ b)⁻¹) * (G.map φ)
    rw [hG_K, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hbK_ne, Polynomial.C_1, one_mul]
  have hdG_K : Polynomial.derivative (G.map φ) = Polynomial.C (φ b) * Polynomial.derivative g := by
    rw [hG_K, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add]
  have hdg_eq : Polynomial.derivative g = Polynomial.C u * Polynomial.derivative (G.map φ) := by
    change Polynomial.derivative g = Polynomial.C ((φ b)⁻¹) * Polynomial.derivative (G.map φ)
    rw [hdG_K, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hbK_ne, Polynomial.C_1, one_mul]
  have hab2 : (al * Polynomial.C u) * (G.map φ)
      + (bl * Polynomial.C u) * Polynomial.derivative (G.map φ) = 1 := by
    have key : (al * Polynomial.C u) * (G.map φ)
          + (bl * Polynomial.C u) * Polynomial.derivative (G.map φ)
        = al * (Polynomial.C u * (G.map φ))
          + bl * (Polynomial.C u * Polynomial.derivative (G.map φ)) := by
      ring
    rw [key, ← hg_eq, ← hdg_eq]
    exact hab
  -- Clear denominators of the Bézout witnesses.
  let A0 : Polynomial R :=
    IsLocalization.integerNormalization (nonZeroDivisors R) (al * Polynomial.C u)
  let B0 : Polynomial R :=
    IsLocalization.integerNormalization (nonZeroDivisors R) (bl * Polynomial.C u)
  obtain ⟨eA, heA_mem, hA_K₀⟩ := intNorm_data (nonZeroDivisors R) (al * Polynomial.C u)
  obtain ⟨eB, heB_mem, hB_K₀⟩ := intNorm_data (nonZeroDivisors R) (bl * Polynomial.C u)
  have hA_K : A0.map φ = Polynomial.C (φ eA) * (al * Polynomial.C u) := hA_K₀
  have hB_K : B0.map φ = Polynomial.C (φ eB) * (bl * Polynomial.C u) := hB_K₀
  have heA_ne : eA ≠ 0 := nonZeroDivisors.ne_zero heA_mem
  have heB_ne : eB ≠ 0 := nonZeroDivisors.ne_zero heB_mem
  have hK : (Polynomial.C (φ eB) * A0.map φ) * (G.map φ)
      + (Polynomial.C (φ eA) * B0.map φ) * Polynomial.derivative (G.map φ)
      = Polynomial.C (φ (eA * eB)) := by
    rw [hA_K, hB_K]
    have hC : Polynomial.C (φ (eA * eB)) = Polynomial.C (φ eA) * Polynomial.C (φ eB) := by
      rw [map_mul, Polynomial.C_mul]
    rw [hC]
    have key : (Polynomial.C (φ eB) * (Polynomial.C (φ eA) * (al * Polynomial.C u)))
            * (G.map φ)
          + (Polynomial.C (φ eA) * (Polynomial.C (φ eB) * (bl * Polynomial.C u)))
            * Polynomial.derivative (G.map φ)
        = Polynomial.C (φ eA) * Polynomial.C (φ eB)
          * ((al * Polynomial.C u) * (G.map φ)
            + (bl * Polynomial.C u) * Polynomial.derivative (G.map φ)) := by
      ring
    rw [key, hab2, mul_one]
  have hbez : (Polynomial.C eB * A0) * G + (Polynomial.C eA * B0) * Polynomial.derivative G
      = Polynomial.C (eA * eB) := by
    apply Polynomial.map_injective φ hφinj
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      ← Polynomial.derivative_map]
    exact hK
  refine ⟨G, H, Polynomial.C eB * A0, Polynomial.C eA * B0, H2, m, c * b, d * c * b,
    eA * eB, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_ne_zero hc_ne hb_ne
  · exact mul_ne_zero (mul_ne_zero hd_ne hc_ne) hb_ne
  · exact mul_ne_zero heA_ne heB_ne
  · exact h1.trans (mul_comm G H)
  · have hstep : Polynomial.C ((c * b) * d) * G ^ (m + 1) = G * (H * H2) := by
      calc Polynomial.C ((c * b) * d) * G ^ (m + 1)
          = (Polynomial.C (c * b) * Polynomial.C d) * G ^ (m + 1) := by rw [Polynomial.C_mul]
        _ = Polynomial.C (c * b) * (Polynomial.C d * G ^ (m + 1)) := by ring
        _ = Polynomial.C (c * b) * (f * H2) := by rw [h2]
        _ = (Polynomial.C (c * b) * f) * H2 := by ring
        _ = (G * H) * H2 := by rw [h1]
        _ = G * (H * H2) := by ring
    have hstep' : G * (Polynomial.C ((c * b) * d) * G ^ m) = G * (H * H2) := by
      rw [← hstep, pow_succ']
      ring
    have heq : Polynomial.C ((c * b) * d) * G ^ m = H * H2 := mul_left_cancel₀ hG_ne hstep'
    have hconst : d * c * b = (c * b) * d := by ring
    rw [hconst]
    exact heq.symm
  · exact hbez.symm

end Work.WilkiesH.Strat
