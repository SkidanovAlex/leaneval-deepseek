import Mathlib
import Submission.Work.MotA.Spread
import Submission.Work.MotA.SpreadAux
import Submission.Work.MotA.spreadMap_injective

set_option linter.unusedVariables false -- v435-speed

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Work.MotV5

/-- **Residue field and height of the horizontal lift of a point of `𝔸³_K`.**

`Work.MotA.spreadMap 𝕜 3 : 𝕜[x₀,…,x₃] →ₐ[𝕜] K[x₀,x₁,x₂]` (`K = RatFunc 𝕜`) sends `x₀ ↦ t` and
`x_{i+1} ↦ x_i`; it is a localization at the nonzero polynomials in `x₀` alone (its image is
`𝕜[t][x₀,x₁,x₂]`, and `K[x] = 𝕜(t)[x]`).  Consequently, for a prime `P` of `K[x₀,x₁,x₂]`
(`= MvPolynomial (Fin 3) (RatFunc 𝕜)`), its contraction `q := Ideal.comap (spreadMap 𝕜 3) P` is a
prime of height `P.height` (a prime never meets the image of the `x₀`-polynomials, since those are
units of the field `K`), and the fraction field of `𝕜[Fin 4] ⧸ q` is that of `K[x] ⧸ P`: the latter
is the localization of the former at the (non-zero-divisor) images of the `x₀`-polynomials, and
localizing at non-zero-divisors does not change the fraction field
(`IsFractionRing.isFractionRing_of_isLocalization`).

Route (sketch).  Give `K[x₀,x₁,x₂]` the `𝕜[Fin 4]`-algebra structure
`RingHom.toAlgebra (Work.MotA.spreadMap 𝕜 3).toRingHom` (so that `algebraMap` *is* the spread map)
and prove `IsLocalization ((nonZeroDivisors (Polynomial 𝕜)).map (Work.MotA.tPoly 𝕜 3))
(K[x₀,x₁,x₂])` with `IsLocalization.isLocalization_iff`: units come from
`Work.MotA.spreadMap_tPoly`, the "every element is `r/m`" clause is exactly
`Work.MotA.exists_clearing`, and the "equal images" clause is injectivity of the spread map
(`Work.MotA.spreadMap_injective`).  Then the height is `IsLocalization.height_under` (`J.under
𝕜[Fin 4]`), and the fraction field statement is the localization-of-a-quotient fact: the canonical
injection `𝕜[Fin 4] ⧸ q → K[x] ⧸ P` exhibits the target as a localization of the source at the image
submonoid (again `Work.MotA.exists_clearing` for surjectivity, and primality of `q` for
non-zero-divisor-ness), so `IsFractionRing.isFractionRing_of_isLocalization` and
`IsLocalization.algEquiv` give the required `𝕜`-algebra isomorphism.  Alternatively construct the two
maps by hand with `IsFractionRing.liftAlgHom` and check bijectivity. -/
theorem class_of_comap_spread (𝕜 : Type) [Field 𝕜]
    (P : Ideal (MvPolynomial (Fin 3) (RatFunc 𝕜))) [P.IsPrime] :
    (Ideal.comap (Work.MotA.spreadMap 𝕜 3) P).height = P.height ∧
    Nonempty (FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸
        Ideal.comap (Work.MotA.spreadMap 𝕜 3) P) ≃ₐ[𝕜]
      FractionRing (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P)) := by
  -- The `𝕜[Fin 4]`-algebra structure on `K[x₀,x₁,x₂]` (`K = RatFunc 𝕜`) is the spread map itself,
  -- so that `algebraMap` is `Work.MotA.spreadMap 𝕜 3`.
  letI algAB : Algebra (MvPolynomial (Fin 4) 𝕜) (MvPolynomial (Fin 3) (RatFunc 𝕜)) :=
    (Work.MotA.spreadMap 𝕜 3).toRingHom.toAlgebra
  -- The "vertical" submonoid: the nonzero polynomials in `t = x₀` alone.
  let Sall : Submonoid (MvPolynomial (Fin 4) 𝕜) :=
    (nonZeroDivisors (Polynomial 𝕜)).map (Work.MotA.tPoly 𝕜 3)
  -- The contraction of `P`: the horizontal prime above `P`.
  let q : Ideal (MvPolynomial (Fin 4) 𝕜) := Ideal.comap (Work.MotA.spreadMap 𝕜 3) P
  -- Its image submonoid in `𝕜[Fin 4] ⧸ q`.
  let Sbar : Submonoid (MvPolynomial (Fin 4) 𝕜 ⧸ q) := Sall.map (Ideal.Quotient.mk q)
  -- **Step 1.** `K[x₀,x₁,x₂]` is the localization of `𝕜[x₀,…,x₃]` at the `t`-polynomials.
  haveI hloc : IsLocalization Sall (MvPolynomial (Fin 3) (RatFunc 𝕜)) := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · -- the image of a nonzero `t`-polynomial is a nonzero constant of the field `K`, hence a unit
      rintro ⟨x, hx⟩
      obtain ⟨c, hc, rfl⟩ := hx
      rw [show algebraMap (MvPolynomial (Fin 4) 𝕜) (MvPolynomial (Fin 3) (RatFunc 𝕜))
          (Work.MotA.tPoly 𝕜 3 c) = Work.MotA.spreadMap 𝕜 3 (Work.MotA.tPoly 𝕜 3 c) from rfl]
      rw [Work.MotA.spreadMap_tPoly]
      refine IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr ?_)
      exact fun h => mem_nonZeroDivisors_iff_ne_zero.mp hc
        (IsFractionRing.injective (Polynomial 𝕜) (RatFunc 𝕜) (by simpa using h))
    · -- every element of `K[x]` acquires polynomial coefficients after clearing denominators
      intro z
      obtain ⟨c, hc, b, hb⟩ := Work.MotA.exists_clearing 𝕜 3 z
      refine ⟨(b, ⟨Work.MotA.tPoly 𝕜 3 c, ⟨c, mem_nonZeroDivisors_iff_ne_zero.mpr hc, rfl⟩⟩), ?_⟩
      change z * Work.MotA.spreadMap 𝕜 3 (Work.MotA.tPoly 𝕜 3 c) = Work.MotA.spreadMap 𝕜 3 b
      rw [Work.MotA.spreadMap_tPoly, hb, mul_comm]
    · -- the spread map is injective
      intro x y hxy
      refine ⟨1, ?_⟩
      simp only [Submonoid.coe_one, one_mul]
      exact Work.MotA.spreadMap_injective 𝕜 3 hxy
  -- **Step 2.** The height of the contraction is the height of `P`.
  have hheight : q.height = P.height := by
    have h := IsLocalization.height_under Sall P
    rw [Ideal.under] at h
    exact h
  refine ⟨hheight, ?_⟩
  -- `q` is prime since `P` is.
  haveI hqprime : q.IsPrime := Ideal.comap_isPrime (Work.MotA.spreadMap 𝕜 3) P
  -- The algebra structure on `K[x] ⧸ P` over `𝕜[Fin 4] ⧸ q` induced by the spread map.
  letI algRS : Algebra (MvPolynomial (Fin 4) 𝕜 ⧸ q)
      (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P) :=
    (Ideal.Quotient.lift q
      ((Ideal.Quotient.mk P).comp (algebraMap (MvPolynomial (Fin 4) 𝕜) (MvPolynomial (Fin 3) (RatFunc 𝕜))))
      (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr ha)).toAlgebra
  -- **Step 3.** `K[x] ⧸ P` is the localization of `𝕜[Fin 4] ⧸ q` at the image of the
  -- `t`-polynomials (localization commutes with the quotient by `q = spreadMap⁻¹ P`).
  haveI hQ : IsLocalization Sbar (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P) := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨x, hx⟩
      obtain ⟨m, hm, rfl⟩ := hx
      exact IsUnit.map (Ideal.Quotient.mk P) (IsLocalization.map_units _ ⟨m, hm⟩)
    · intro z
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨⟨x, m⟩, e⟩ := IsLocalization.surj Sall y
      refine ⟨(Ideal.Quotient.mk q x, ⟨Ideal.Quotient.mk q ↑m, ⟨m, m.2, rfl⟩⟩), ?_⟩
      change Ideal.Quotient.mk P y * Ideal.Quotient.mk P
            (algebraMap (MvPolynomial (Fin 4) 𝕜) (MvPolynomial (Fin 3) (RatFunc 𝕜)) ↑m)
          = Ideal.Quotient.mk P (algebraMap (MvPolynomial (Fin 4) 𝕜) (MvPolynomial (Fin 3) (RatFunc 𝕜)) x)
      rw [← map_mul, e]
    · rintro x y hxy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      have h : a - b ∈ Ideal.comap (algebraMap (MvPolynomial (Fin 4) 𝕜)
          (MvPolynomial (Fin 3) (RatFunc 𝕜))) P := by
        simpa [Ideal.mem_comap, map_sub] using (Ideal.Quotient.eq.mp hxy)
      refine ⟨1, ?_⟩
      simp only [Submonoid.coe_one, one_mul]
      exact Ideal.Quotient.eq.mpr h
  -- **Step 4.** The images of the `t`-polynomials are non-zero-divisors in the domain `𝕜[Fin 4] ⧸ q`:
  -- they are nonzero, since a `t`-polynomial maps to a nonzero constant of `K`, which is not in `P`.
  have hM : Sbar ≤ nonZeroDivisors (MvPolynomial (Fin 4) 𝕜 ⧸ q) := by
    rintro x ⟨s, hs, rfl⟩
    obtain ⟨c, hc, rfl⟩ := hs
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h
    have hmem : Work.MotA.tPoly 𝕜 3 c ∈ q := Ideal.Quotient.eq_zero_iff_mem.mp h
    rw [Ideal.mem_comap] at hmem
    refine (inferInstance : P.IsPrime).ne_top (P.eq_top_of_isUnit_mem hmem ?_)
    rw [Work.MotA.spreadMap_tPoly]
    refine IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr fun h0 => ?_)
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hc)
      (IsFractionRing.injective (Polynomial 𝕜) (RatFunc 𝕜) (by simpa using h0))
  -- The `K[x] ⧸ P`-algebra structure on `FractionRing (𝕜[Fin 4] ⧸ q)`: localizing at the
  -- nonzero divisors of `𝕜[Fin 4] ⧸ q` after localizing at `Sbar`.
  letI algST : Algebra (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P)
      (FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸ q)) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe (R := MvPolynomial (Fin 4) 𝕜 ⧸ q)
      (S := MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P) (T := FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸ q))
      Sbar (nonZeroDivisors (MvPolynomial (Fin 4) 𝕜 ⧸ q)) hM
  haveI hST : IsScalarTower (MvPolynomial (Fin 4) 𝕜 ⧸ q) (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P)
      (FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸ q)) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le (R := MvPolynomial (Fin 4) 𝕜 ⧸ q)
      (S := MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P) (T := FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸ q))
      Sbar (nonZeroDivisors (MvPolynomial (Fin 4) 𝕜 ⧸ q)) hM
  -- **Step 5.** The scalar tower `𝕜 → 𝕜[Fin 4] ⧸ q → K[x] ⧸ P`.
  haveI hRS : IsScalarTower 𝕜 (MvPolynomial (Fin 4) 𝕜 ⧸ q)
      (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P) := by
    refine @IsScalarTower.of_algebraMap_eq 𝕜 (MvPolynomial (Fin 4) 𝕜 ⧸ q)
      (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P) _ _ _
      (inferInstance : Algebra 𝕜 (MvPolynomial (Fin 4) 𝕜 ⧸ q)) algRS
      (inferInstance : Algebra 𝕜 (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P)) fun c => ?_
    rw [← Ideal.Quotient.mk_algebraMap 𝕜 P c]
    rw [← Ideal.Quotient.mk_algebraMap 𝕜 q c]
    change Ideal.Quotient.mk P (algebraMap 𝕜 (MvPolynomial (Fin 3) (RatFunc 𝕜)) c)
      = (Ideal.Quotient.lift q
          ((Ideal.Quotient.mk P).comp (algebraMap (MvPolynomial (Fin 4) 𝕜) (MvPolynomial (Fin 3) (RatFunc 𝕜))))
          (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr ha))
          (Ideal.Quotient.mk q (algebraMap 𝕜 (MvPolynomial (Fin 4) 𝕜) c))
    rw [Ideal.Quotient.lift_mk, RingHom.comp_apply]
    congr 1
    exact ((Work.MotA.spreadMap 𝕜 3).commutes' c).symm
  -- **Step 6.** Localizing at non-zero-divisors does not change the fraction field:
  -- `FractionRing (𝕜[Fin 4] ⧸ q)` is a fraction ring of `K[x] ⧸ P`.
  haveI hfrac : IsFractionRing (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P)
      (FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸ q)) :=
    IsFractionRing.isFractionRing_of_isLocalization (R := MvPolynomial (Fin 4) 𝕜 ⧸ q)
      (S := MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P)
      (T := FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸ q)) Sbar hM
  -- **Step 7.** The scalar tower `𝕜 → K[x] ⧸ P → FractionRing (𝕜[Fin 4] ⧸ q)`.
  haveI hktower : IsScalarTower 𝕜 (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P)
      (FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸ q)) := by
    refine @IsScalarTower.of_algebraMap_eq 𝕜 (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P)
      (FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸ q)) _ _ _
      (inferInstance : Algebra 𝕜 (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P)) algST
      (inferInstance : Algebra 𝕜 (FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸ q))) fun c => ?_
    rw [IsScalarTower.algebraMap_apply 𝕜 (MvPolynomial (Fin 4) 𝕜 ⧸ q)
      (FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸ q))]
    rw [IsScalarTower.algebraMap_apply 𝕜 (MvPolynomial (Fin 4) 𝕜 ⧸ q)
      (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P)]
    rw [← IsScalarTower.algebraMap_apply (MvPolynomial (Fin 4) 𝕜 ⧸ q)
      (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P) (FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸ q))]
  -- **Step 8.** Both `FractionRing (𝕜[Fin 4] ⧸ q)` and `FractionRing (K[x] ⧸ P)` are fraction rings
  -- of `K[x] ⧸ P`, hence are isomorphic; restricting scalars from `K[x] ⧸ P` to `𝕜` gives the
  -- required `𝕜`-algebra isomorphism.
  exact ⟨(IsLocalization.algEquiv (nonZeroDivisors (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P))
    (FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸ q))
    (FractionRing (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P))).restrictScalars 𝕜⟩

end Work.MotV5
