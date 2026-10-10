import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotA.Spread
import Submission.Work.MotA.SpreadAux
import Submission.Work.MotA.spreadMap_injective
import Submission.Work.MotA.dvd_spread_iff
import Submission.Work.MotA.quotient_vertical
import Submission.Work.MotV5.class_of_comap_spread
import Submission.Work.MotV5.census_G
import Submission.Work.MotV5.fractionRing_mvPoly_fin_add
import Submission.Work.MotV5.fractionRing_mvPoly_one
import Submission.Work.MotV5.fractionRing_mvPoly_three_ratFunc_fractionRing_two
import Submission.Work.MotV5.exists_prime_tPoly_eq_of_not_disjoint
import Submission.Work.CrauderKatz.BlowUp.fractionRing_mvPolynomial_finTwo

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.MotV5

/-! ## Private auxiliary lemmas for `census_F_alt`

Everything in this section is `private`, so no name here can clash with the auxiliary declarations
of the sibling modules `MotV5/census_G` and `MotV5/census_F`. -/

/-- **The spread map is the localization at the vertical monoid.**  For the `𝕜[t,x₁,…,xₙ]`-algebra
structure on `K[x₁,…,xₙ]` (`K = RatFunc 𝕜`) given by `RingHom.toAlgebra (spreadMap 𝕜 n).toRingHom`. -/
private theorem cf_isLocalization_spreadMap (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    letI : Algebra (MvPolynomial (Fin (n+1)) 𝕜) (MvPolynomial (Fin n) (RatFunc 𝕜)) :=
      RingHom.toAlgebra (Work.MotA.spreadMap 𝕜 n).toRingHom
    IsLocalization ((nonZeroDivisors (Polynomial 𝕜)).map (Work.MotA.tPoly 𝕜 n))
      (MvPolynomial (Fin n) (RatFunc 𝕜)) := by
  letI : Algebra (MvPolynomial (Fin (n+1)) 𝕜) (MvPolynomial (Fin n) (RatFunc 𝕜)) :=
    RingHom.toAlgebra (Work.MotA.spreadMap 𝕜 n).toRingHom
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- every element of the monoid becomes a unit: it is the nonzero constant `C c`
    rintro ⟨y, hy⟩
    rw [Submonoid.mem_map] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    have hc0 : c ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hc
    have hmap : algebraMap (MvPolynomial (Fin (n+1)) 𝕜) (MvPolynomial (Fin n) (RatFunc 𝕜))
        (Work.MotA.tPoly 𝕜 n c) =
        MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) c) :=
      Work.MotA.spreadMap_tPoly 𝕜 n c
    rw [hmap]
    exact IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr (Work.MotA.algebraMap_ne_zero hc0))
  · -- clearing denominators: `Work.MotA.exists_clearing`
    intro z
    obtain ⟨c, hc, b, hb⟩ := Work.MotA.exists_clearing 𝕜 n z
    refine ⟨(b, ⟨Work.MotA.tPoly 𝕜 n c,
        Submonoid.mem_map.mpr ⟨c, mem_nonZeroDivisors_iff_ne_zero.mpr hc, rfl⟩⟩), ?_⟩
    show z * Work.MotA.spreadMap 𝕜 n (Work.MotA.tPoly 𝕜 n c) =
      Work.MotA.spreadMap 𝕜 n b
    rw [Work.MotA.spreadMap_tPoly, hb, mul_comm]
  · -- the spread map is injective
    intro x y hxy
    exact ⟨1, by rw [Work.MotA.spreadMap_injective 𝕜 n hxy]⟩

/-- `RatFunc.X` is transcendental over `M`, hence never a constant. -/
private theorem cf_ratFunc_algebraMap_ne_X {M : Type} [Field M] (c : M) :
    algebraMap M (RatFunc M) c ≠ (RatFunc.X : RatFunc M) := by
  intro h
  refine RatFunc.transcendental_X ⟨Polynomial.X - Polynomial.C c, ?_, ?_⟩
  · simpa using sub_ne_zero.mpr (Polynomial.X_ne_C c)
  · rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, h, sub_self]

/-- **Vertical census, second half.**  If a height-one prime `p` of `𝕜[x₀,x₁,x₂,x₃]` is generated
by the image `q(x₀)` of a prime `q ∈ 𝕜[t]`, then `Frac(𝕜[Fin 4]/p) ≅ RatFunc F₀` for the field
`F₀ := Frac ((𝕜[t]/(q))[y,z])`, which is not constants-only. -/
private theorem cf_vert_of_prime_tPoly {𝕜 : Type} [Field 𝕜]
    (p : Ideal (MvPolynomial (Fin 4) 𝕜)) [p.IsPrime]
    (q : Polynomial 𝕜) (hq : Prime q)
    (hp : p = Ideal.span {(Work.MotA.tPoly 𝕜 3 q : MvPolynomial (Fin 4) 𝕜)}) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Algebra 𝕜 F₀), ¬ Work.MotV.ConstantsOnly 𝕜 F₀ ∧
      Nonempty (FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸ p) ≃ₐ[𝕜] RatFunc F₀) := by
  classical
  -- The residue ring `R = 𝕜[t] ⧸ (q)` is a field (`q` is a nonzero prime in the PID `𝕜[t]`).
  haveI hqprime : (Ideal.span {q} : Ideal (Polynomial 𝕜)).IsPrime :=
    (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  have hqne : (Ideal.span {q} : Ideal (Polynomial 𝕜)) ≠ ⊥ := by
    simpa [hq.ne_zero] using (Ideal.span_singleton_eq_bot.not.mpr hq.ne_zero)
  haveI hqmax : (Ideal.span {q} : Ideal (Polynomial 𝕜)).IsMaximal :=
    Ideal.IsPrime.isMaximal_of_ne_bot inferInstance hqne
  let R := Polynomial 𝕜 ⧸ Ideal.span {q}
  letI : Field R := Ideal.Quotient.field (Ideal.span {q})
  -- The quotient isomorphism `𝕜[Fin 4] ⧸ (q(x₀)) ≃ₐ 𝕜[Fin 3] ⧸ (q)`.
  obtain ⟨e_q⟩ := Work.MotA.quotient_vertical 𝕜 3 q hq
  -- The field `F₀ := Frac (R[y,z])` is not constants-only.
  refine ⟨FractionRing (MvPolynomial (Fin 2) R), inferInstance, inferInstance, ?_, ?_⟩
  · intro hco
    obtain ⟨g⟩ := Work.CrauderKatz.BlowUp.fractionRing_mvPolynomial_finTwo R
    let g' : FractionRing (MvPolynomial (Fin 2) R) ≃ₐ[𝕜] RatFunc (RatFunc R) :=
      g.restrictScalars 𝕜
    obtain ⟨c, hc⟩ := hco (RatFunc R) (g' : FractionRing (MvPolynomial (Fin 2) R) →ₐ[𝕜]
      RatFunc (RatFunc R)) (g'.symm (RatFunc.X : RatFunc (RatFunc R)))
    refine cf_ratFunc_algebraMap_ne_X c ?_
    rw [hc]
    simp
  · -- `Frac (𝕜[Fin 4] ⧸ p) ≅ Frac (𝕜[Fin 3] ⧸ (q)) ≅ RatFunc F₀`.
    have h2 : (MvPolynomial (Fin 4) 𝕜 ⧸ p) ≃ₐ[𝕜] MvPolynomial (Fin 3) R :=
      (Ideal.quotientEquivAlgOfEq 𝕜 hp).trans e_q
    have h3 : FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸ p) ≃ₐ[𝕜]
        FractionRing (MvPolynomial (Fin 3) R) :=
      IsFractionRing.algEquivOfAlgEquiv h2
    obtain ⟨h4⟩ :=
      Work.MotV5.fractionRing_mvPoly_three_ratFunc_fractionRing_two (𝕜 := 𝕜) (F := R)
    exact ⟨h3.trans h4⟩

/-- **Node `SPREAD`, the `F`-side census at the level of `𝔸⁴_𝕜`** (second, name-disjoint copy of
`MotV5/census_F`, needed because that file's internal auxiliary names clash with `MotV5/census_G`'s).

Setting: `K = RatFunc 𝕜`, `L : LinkCert K F₁ F₂` with `L.F, L.G ∈ K[x₀,x₁,x₂]` and `L.F_all`: every
height-one prime of `K[x₀,x₁,x₂]` containing `L.F` has residue field `RatFunc F₂` or is junk.  Let
`F' ∈ 𝕜[x₀,…,x₃]`, `cF ∈ 𝕜[t]` with `cF ≠ 0` and `spreadMap 𝕜 3 F' = C cF * L.F`.

Conclusion: for every height-one prime `p` of `𝕜[x₀,…,x₃]` with `F' ∈ p`, the fraction field
`FractionRing (𝕜[Fin 4] ⧸ p)` is either `RatFunc F₂` or `RatFunc F₀` with `¬ ConstantsOnly 𝕜 F₀`.

ROUTE — read `Submission/Work/MotV5/census_G.lean` (the sibling node, whose top-level statement is
proved, with the vertical case split off into `census_G_vert.lean`) and copy its structure, replacing
`G' ↦ F'`, `cG ↦ cF`, `L.G_other ↦ L.F_all` and the first disjunct
(`p = comap (spreadMap 𝕜 3) L.zP.asIdeal`) by the disjunct `Nonempty (FractionRing (𝕜[Fin 4] ⧸ p)
≃ₐ[𝕜] RatFunc F₂)` (which in the horizontal case comes from the first half of `L.F_all`, viewed over
`𝕜` by composing with the `K`-`AlgEquiv`; the `IsScalarTower 𝕜 K F₂` hypothesis is available).
Also read `Submission/Work/MotV5/census_F.lean` for the same adaptation (but do not import it).
The vertical case is identical to `census_G`'s.

IMPORTANT: every auxiliary declaration you introduce must be *name-disjoint* from those of
`MotV5/census_G` and `MotV5/census_F` (e.g. prefix them `cf_`), because `MotV5/census_G` and
`MotV5/census_F` currently define clashing auxiliary names and any module importing both fails to
build.  Do NOT import `Submission.Work.MotV5.census_F`.  You may import
`Submission.Work.MotV5.census_G` and `Submission.Work.MotV5.class_of_comap_spread`
(the latter's statement is exactly the localization fact needed: `spreadMap 𝕜 3` is the
localization at `(nonZeroDivisors 𝕜[t]).map (tPoly 𝕜 3)`, with height preservation and the residue
field isomorphism `FractionRing (𝕜[Fin 4] ⧸ comap spreadMap P) ≃ₐ[𝕜] FractionRing (K[x] ⧸ P)`). -/
theorem census_F_alt {𝕜 : Type} [Field 𝕜] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    [Algebra (RatFunc 𝕜) F₁] [Algebra (RatFunc 𝕜) F₂] [Algebra 𝕜 F₁] [Algebra 𝕜 F₂]
    [IsScalarTower 𝕜 (RatFunc 𝕜) F₁] [IsScalarTower 𝕜 (RatFunc 𝕜) F₂]
    (L : Work.MotV.LinkCert (RatFunc 𝕜) F₁ F₂)
    (F' : MvPolynomial (Fin 4) 𝕜) (cF : Polynomial 𝕜) (hcF : cF ≠ 0)
    (hF : Work.MotA.spreadMap 𝕜 3 F' =
      MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) cF) * L.F)
    (p : Ideal (MvPolynomial (Fin 4) 𝕜)) [p.IsPrime] (hp1 : p.height = 1) (hFp : F' ∈ p) :
    Nonempty (FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸ p) ≃ₐ[𝕜] RatFunc F₂) ∨
      ∃ (F₀ : Type) (_ : Field F₀) (_ : Algebra 𝕜 F₀), ¬ Work.MotV.ConstantsOnly 𝕜 F₀ ∧
        Nonempty (FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸ p) ≃ₐ[𝕜] RatFunc F₀) := by
  classical
  -- The submonoid of "vertical" elements and the localization structure of `spreadMap 𝕜 3`.
  let M : Submonoid (MvPolynomial (Fin 4) 𝕜) :=
    (nonZeroDivisors (Polynomial 𝕜)).map (Work.MotA.tPoly 𝕜 3)
  letI : Algebra (MvPolynomial (Fin 4) 𝕜) (MvPolynomial (Fin 3) (RatFunc 𝕜)) :=
    RingHom.toAlgebra (Work.MotA.spreadMap 𝕜 3).toRingHom
  haveI hloc : IsLocalization M (MvPolynomial (Fin 3) (RatFunc 𝕜)) :=
    cf_isLocalization_spreadMap 𝕜 3
  by_cases hdisj : Disjoint (M : Set (MvPolynomial (Fin 4) 𝕜))
      (p : Set (MvPolynomial (Fin 4) 𝕜))
  · -- ## Horizontal case: `p` does not meet the vertical elements.
    let P : Ideal (MvPolynomial (Fin 3) (RatFunc 𝕜)) :=
      Ideal.map (algebraMap (MvPolynomial (Fin 4) 𝕜) (MvPolynomial (Fin 3) (RatFunc 𝕜))) p
    have hp_prime : p.IsPrime := ‹p.IsPrime›
    have hPprime : P.IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint M (MvPolynomial (Fin 3) (RatFunc 𝕜)) p
        hp_prime hdisj
    have hPheight : P.height = 1 := by
      have h := IsLocalization.height_map_of_disjoint (S := MvPolynomial (Fin 3) (RatFunc 𝕜))
        M p hdisj
      rw [h, hp1]
    have hunder : Ideal.comap (algebraMap (MvPolynomial (Fin 4) 𝕜)
        (MvPolynomial (Fin 3) (RatFunc 𝕜))) P = p := by
      have h := IsLocalization.under_map_of_isPrime_disjoint M
        (MvPolynomial (Fin 3) (RatFunc 𝕜)) hp_prime hdisj
      simpa [P, Ideal.under_def] using h
    have hcomap : Ideal.comap (Work.MotA.spreadMap 𝕜 3) P = p := hunder
    -- `C cF = spreadMap (tPoly cF)` is not in `P`, since `P` does not meet the vertical elements.
    have hCnotmem : MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) cF) ∉ P := by
      intro hmem
      have h2 : Work.MotA.tPoly 𝕜 3 cF ∈ Ideal.comap (algebraMap (MvPolynomial (Fin 4) 𝕜)
          (MvPolynomial (Fin 3) (RatFunc 𝕜))) P := by
        rw [Ideal.mem_comap]
        show Work.MotA.spreadMap 𝕜 3 (Work.MotA.tPoly 𝕜 3 cF) ∈ P
        rw [Work.MotA.spreadMap_tPoly]
        exact hmem
      rw [hunder] at h2
      exact (Set.disjoint_left.mp hdisj)
        (Submonoid.mem_map.mpr ⟨cF, mem_nonZeroDivisors_iff_ne_zero.mpr hcF, rfl⟩) h2
    -- `L.F ∈ P`: it is the second factor of `C cF * L.F = spreadMap F' ∈ P`.
    have hFP : L.F ∈ P := by
      have h1 : MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) cF) * L.F ∈ P := by
        rw [← hF]
        exact Ideal.mem_map_of_mem (Work.MotA.spreadMap 𝕜 3) hFp
      rcases hPprime.mem_or_mem h1 with h | h
      · exact absurd h hCnotmem
      · exact h
    -- The point of `𝔸³_K` defined by `P`.
    let x : Work.MotA.polySpec (RatFunc 𝕜) 3 := ⟨P, hPprime⟩
    have hxcoheight : Order.coheight x = 1 := by
      rw [← AlgebraicGeometry.idealHeight_eq_coheight]
      exact hPheight
    rcases L.F_all x hxcoheight hFP with hF2 | hjunk
    · -- The residue field is the `F`-side class of the link: transfer along
      -- `Frac(𝕜[Fin 4]/p) ≅ Frac(K[x]/P)` and restrict scalars from `K` to `𝕜`.
      left
      obtain ⟨e₂⟩ := hF2
      haveI hstS : IsScalarTower 𝕜 (RatFunc 𝕜)
          (FractionRing (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P)) := inferInstance
      obtain ⟨e₂'⟩ := nonempty_algEquiv_restrictScalars (𝕜 := 𝕜) (K := RatFunc 𝕜) e₂
      obtain ⟨-, ⟨e₁⟩⟩ := Work.MotV5.class_of_comap_spread 𝕜 P
      rw [hcomap] at e₁
      exact ⟨e₁.trans e₂'⟩
    · -- The point is junk: `JunkClass` gives `F₀` with `GeomRuled` (hence not constants-only).
      right
      obtain ⟨F₀, hF₀field, hF₀alg, hGeo, he⟩ := hjunk
      letI : Algebra 𝕜 F₀ := Algebra.compHom F₀ (algebraMap 𝕜 (RatFunc 𝕜))
      haveI hstF : IsScalarTower 𝕜 (RatFunc 𝕜) F₀ :=
        IsScalarTower.of_algebraMap_eq'
          (Algebra.compHom_algebraMap_eq F₀ (algebraMap 𝕜 (RatFunc 𝕜)))
      have hNC : ¬ Work.MotV.ConstantsOnly 𝕜 F₀ :=
        not_constantsOnly_of_geomRuled (K := RatFunc 𝕜) hGeo
      obtain ⟨e₂⟩ := he
      haveI hstS : IsScalarTower 𝕜 (RatFunc 𝕜)
          (FractionRing (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P)) := inferInstance
      obtain ⟨e₂'⟩ := nonempty_algEquiv_restrictScalars (𝕜 := 𝕜) (K := RatFunc 𝕜) e₂
      obtain ⟨-, ⟨e₁⟩⟩ := Work.MotV5.class_of_comap_spread 𝕜 P
      rw [hcomap] at e₁
      exact ⟨F₀, hF₀field, ‹Algebra 𝕜 F₀›, hNC, ⟨e₁.trans e₂'⟩⟩
  · -- ## Vertical case: `p` meets the vertical elements, hence is itself a vertical prime.
    right
    obtain ⟨q, hq, hpq⟩ := Work.MotV5.exists_prime_tPoly_eq_of_not_disjoint 𝕜 p hp1 hdisj
    exact cf_vert_of_prime_tPoly p q hq hpq

end Work.MotV5
