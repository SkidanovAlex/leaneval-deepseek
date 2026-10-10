import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotA.Spread
import Submission.Work.MotA.SpreadAux
import Submission.Work.MotA.spreadMap_injective
import Submission.Work.MotA.dvd_spread_iff
import Submission.Work.MotA.quotient_vertical
import Submission.Work.MotV5.class_of_comap_spread
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

/-! ## Private auxiliary lemmas for `census_G_alt`

Everything in this section is `private`, so no name here can clash with the auxiliary declarations
of the sibling modules `MotV5/census_G`, `MotV5/census_F` and `MotV5/census_F_alt`.  The code is
copied (and re-proved) from `MotV5/census_F_alt` so that this module does *not* import the stubs
`MotV5/census_G_vert`, `MotV5/census_G_vertical` or `MotV5/isLocalization_spreadMap` (which contain
`sorry` and would pollute importers with `sorryAx`). -/

/-- **The spread map is the localization at the vertical monoid.**  For the `𝕜[t,x₁,…,xₙ]`-algebra
structure on `K[x₁,…,xₙ]` (`K = RatFunc 𝕜`) given by `RingHom.toAlgebra (spreadMap 𝕜 n).toRingHom`. -/
private theorem cg_isLocalization_spreadMap (𝕜 : Type) [Field 𝕜] (n : ℕ) :
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
private theorem cg_ratFunc_algebraMap_ne_X {M : Type} [Field M] (c : M) :
    algebraMap M (RatFunc M) c ≠ (RatFunc.X : RatFunc M) := by
  intro h
  refine RatFunc.transcendental_X ⟨Polynomial.X - Polynomial.C c, ?_, ?_⟩
  · simpa using sub_ne_zero.mpr (Polynomial.X_ne_C c)
  · rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, h, sub_self]

/-- **Vertical census, second half.**  If a height-one prime `p` of `𝕜[x₀,x₁,x₂,x₃]` is generated
by the image `q(x₀)` of a prime `q ∈ 𝕜[t]`, then `Frac(𝕜[Fin 4]/p) ≅ RatFunc F₀` for the field
`F₀ := Frac ((𝕜[t]/(q))[y,z])`, which is not constants-only. -/
private theorem cg_vert_of_prime_tPoly {𝕜 : Type} [Field 𝕜]
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
    refine cg_ratFunc_algebraMap_ne_X c ?_
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

/-- **Restricting scalars of an algebra isomorphism.**  If `A` and `B` are `K`-algebras which are
also `𝕜`-algebras with scalar towers through `K`, then a `K`-algebra isomorphism is automatically a
`𝕜`-algebra isomorphism (the `𝕜`-structure map factors through `K`). -/
private theorem cg_nonempty_algEquiv_restrictScalars {𝕜 K A B : Type} [Field 𝕜] [CommSemiring K]
    [Semiring A] [Semiring B] [Algebra 𝕜 K] [Algebra K A] [Algebra K B] [Algebra 𝕜 A]
    [Algebra 𝕜 B] [IsScalarTower 𝕜 K A] [IsScalarTower 𝕜 K B] (e : A ≃ₐ[K] B) :
    Nonempty (A ≃ₐ[𝕜] B) := by
  refine ⟨AlgEquiv.ofRingEquiv (f := (e : A ≃+* B)) ?_⟩
  intro a
  show e (algebraMap 𝕜 A a) = algebraMap 𝕜 B a
  rw [IsScalarTower.algebraMap_apply 𝕜 K A, IsScalarTower.algebraMap_apply 𝕜 K B, e.commutes]

/-- **A geometrically ruled field is not constants-only.**  `GeomRuled K F₀` supplies a field `M'`
with a non-constant `K`-embedding `F₀ →ₐ[K] RatFunc M'`; viewing `M'` as a `𝕜`-algebra through
`𝕜 → K → M'` (and `F₀` likewise) turns it into a witness for `¬ ConstantsOnly 𝕜 F₀`. -/
private theorem cg_not_constantsOnly_of_geomRuled {𝕜 K : Type} [Field 𝕜] [Field K] [Algebra 𝕜 K]
    {F₀ : Type} [Field F₀] [Algebra K F₀] (h : Work.MotV.GeomRuled K F₀) :
    letI : Algebra 𝕜 F₀ := Algebra.compHom F₀ (algebraMap 𝕜 K)
    ¬ Work.MotV.ConstantsOnly 𝕜 F₀ := by
  letI : Algebra 𝕜 F₀ := Algebra.compHom F₀ (algebraMap 𝕜 K)
  haveI hstF : IsScalarTower 𝕜 K F₀ :=
    IsScalarTower.of_algebraMap_eq' (Algebra.compHom_algebraMap_eq F₀ (algebraMap 𝕜 K))
  obtain ⟨M', hM'field, hM'alg, ι, x, hx⟩ := h
  letI : Algebra 𝕜 M' := Algebra.compHom M' (algebraMap 𝕜 K)
  haveI : IsScalarTower 𝕜 K M' :=
    IsScalarTower.of_algebraMap_eq' (Algebra.compHom_algebraMap_eq M' (algebraMap 𝕜 K))
  haveI : IsScalarTower 𝕜 K (RatFunc M') := inferInstance
  intro hco
  obtain ⟨c, hc⟩ := hco M' (AlgHom.restrictScalars 𝕜 ι) x
  rw [AlgHom.restrictScalars_apply] at hc
  exact hx c hc

/-- **Node `SPREAD`, the `G`-side census at the level of `𝔸⁴_𝕜`** (a *clean*, name-disjoint copy of
`MotV5/census_G`, which imports the unfinished stubs `MotV5/census_G_vert` and
`MotV5/isLocalization_spreadMap` and therefore pollutes importers with `sorryAx`).

Setting: `K = RatFunc 𝕜`, `L : LinkCert K F₁ F₂` with `L.F, L.G ∈ K[x₀,x₁,x₂]`, `L.zP` a height-one
point of `𝔸³_K` with `L.G ∈ L.zP.asIdeal`, and `L.G_other`: every other height-one prime of
`K[x₀,x₁,x₂]` containing `L.G` is junk.  Let `G' ∈ 𝕜[x₀,…,x₃]`, `cG ∈ 𝕜[t]` with `cG ≠ 0` and
`spreadMap 𝕜 3 G' = C cG * L.G`.

Conclusion: for every height-one prime `p` of `𝕜[x₀,…,x₃]` with `G' ∈ p`, either `p` is the
horizontal lift `Ideal.comap (spreadMap 𝕜 3) L.zP.asIdeal`, or `FractionRing (𝕜[Fin 4] ⧸ p)` is
`RatFunc F₀` with `¬ ConstantsOnly 𝕜 F₀`. -/
theorem census_G_alt {𝕜 : Type} [Field 𝕜] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    [Algebra (RatFunc 𝕜) F₁] [Algebra (RatFunc 𝕜) F₂] [Algebra 𝕜 F₁] [Algebra 𝕜 F₂]
    [IsScalarTower 𝕜 (RatFunc 𝕜) F₁] [IsScalarTower 𝕜 (RatFunc 𝕜) F₂]
    (L : Work.MotV.LinkCert (RatFunc 𝕜) F₁ F₂)
    (G' : MvPolynomial (Fin 4) 𝕜) (cG : Polynomial 𝕜) (hcG : cG ≠ 0)
    (hG : Work.MotA.spreadMap 𝕜 3 G' =
      MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) cG) * L.G)
    (p : Ideal (MvPolynomial (Fin 4) 𝕜)) [p.IsPrime] (hp1 : p.height = 1) (hGp : G' ∈ p) :
    p = Ideal.comap (Work.MotA.spreadMap 𝕜 3) L.zP.asIdeal ∨
      ∃ (F₀ : Type) (_ : Field F₀) (_ : Algebra 𝕜 F₀), ¬ Work.MotV.ConstantsOnly 𝕜 F₀ ∧
        Nonempty (FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸ p) ≃ₐ[𝕜] RatFunc F₀) := by
  classical
  -- The submonoid of "vertical" elements and the localization structure of `spreadMap 𝕜 3`.
  let M : Submonoid (MvPolynomial (Fin 4) 𝕜) :=
    (nonZeroDivisors (Polynomial 𝕜)).map (Work.MotA.tPoly 𝕜 3)
  letI : Algebra (MvPolynomial (Fin 4) 𝕜) (MvPolynomial (Fin 3) (RatFunc 𝕜)) :=
    RingHom.toAlgebra (Work.MotA.spreadMap 𝕜 3).toRingHom
  haveI hloc : IsLocalization M (MvPolynomial (Fin 3) (RatFunc 𝕜)) :=
    cg_isLocalization_spreadMap 𝕜 3
  by_cases hdisj : Disjoint (M : Set (MvPolynomial (Fin 4) 𝕜))
      (p : Set (MvPolynomial (Fin 4) 𝕜))
  · -- ## Horizontal case: `p` does not meet the vertical elements.
    let P : Ideal (MvPolynomial (Fin 3) (RatFunc 𝕜)) :=
      Ideal.map (algebraMap (MvPolynomial (Fin 4) 𝕜) (MvPolynomial (Fin 3) (RatFunc 𝕜))) p
    have hp_prime : p.IsPrime := ‹p.IsPrime›
    have hPprime : P.IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint M (MvPolynomial (Fin 3) (RatFunc 𝕜)) p hp_prime
        hdisj
    have hPheight : P.height = 1 := by
      have h := IsLocalization.height_map_of_disjoint
        (S := MvPolynomial (Fin 3) (RatFunc 𝕜)) M p hdisj
      rw [h, hp1]
    have hunder : Ideal.comap (algebraMap (MvPolynomial (Fin 4) 𝕜)
        (MvPolynomial (Fin 3) (RatFunc 𝕜))) P = p := by
      have h := IsLocalization.under_map_of_isPrime_disjoint M
        (MvPolynomial (Fin 3) (RatFunc 𝕜)) hp_prime hdisj
      simpa [P, Ideal.under_def] using h
    have hcomap : Ideal.comap (Work.MotA.spreadMap 𝕜 3) P = p := hunder
    -- `C cG`, the image of the vertical element `tPoly cG`, is not in `P`.
    have hCnotmem : MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) cG) ∉ P := by
      intro hmem
      have h2 : Work.MotA.tPoly 𝕜 3 cG ∈ Ideal.comap (algebraMap (MvPolynomial (Fin 4) 𝕜)
          (MvPolynomial (Fin 3) (RatFunc 𝕜))) P := by
        rw [Ideal.mem_comap]
        show Work.MotA.spreadMap 𝕜 3 (Work.MotA.tPoly 𝕜 3 cG) ∈ P
        rw [Work.MotA.spreadMap_tPoly]
        exact hmem
      rw [hunder] at h2
      exact (Set.disjoint_left.mp hdisj)
        (Submonoid.mem_map.mpr ⟨cG, mem_nonZeroDivisors_iff_ne_zero.mpr hcG, rfl⟩) h2
    -- `L.G ∈ P`.
    have hGP : L.G ∈ P := by
      have h1 : MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) cG) * L.G ∈ P := by
        rw [← hG]
        exact Ideal.mem_map_of_mem (Work.MotA.spreadMap 𝕜 3) hGp
      rcases hPprime.mem_or_mem h1 with h | h
      · exact absurd h hCnotmem
      · exact h
    -- The point of `𝔸³_K` defined by `P`.
    let x : Work.MotA.polySpec (RatFunc 𝕜) 3 := ⟨P, hPprime⟩
    have hxcoheight : Order.coheight x = 1 := by
      rw [← AlgebraicGeometry.idealHeight_eq_coheight]
      exact hPheight
    by_cases hPzP : P = L.zP.asIdeal
    · -- The horizontal lift of `zP` itself.
      left
      rw [← hPzP]
      exact hcomap.symm
    · -- Any other horizontal prime is junk.
      right
      have hxne : x ≠ L.zP := by
        intro hEq
        apply hPzP
        rw [← hEq]
      obtain ⟨F₀, hF₀field, hF₀alg, hGeo, he⟩ :=
        L.G_other x hxcoheight hGP hxne
      -- View `F₀` as a `𝕜`-algebra through `𝕜 → K`, and restrict the `K`-iso to `𝕜`.
      letI alg𝕜 : Algebra 𝕜 F₀ := Algebra.compHom F₀ (algebraMap 𝕜 (RatFunc 𝕜))
      haveI hstF : IsScalarTower 𝕜 (RatFunc 𝕜) F₀ :=
        IsScalarTower.of_algebraMap_eq'
          (Algebra.compHom_algebraMap_eq F₀ (algebraMap 𝕜 (RatFunc 𝕜)))
      have hNC : ¬ Work.MotV.ConstantsOnly 𝕜 F₀ :=
        cg_not_constantsOnly_of_geomRuled (K := RatFunc 𝕜) hGeo
      obtain ⟨e₁ : FractionRing (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P) ≃ₐ[RatFunc 𝕜] RatFunc F₀⟩ :=
        he
      haveI hstS : IsScalarTower 𝕜 (RatFunc 𝕜)
          (FractionRing (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P)) := inferInstance
      obtain ⟨e₁'⟩ := cg_nonempty_algEquiv_restrictScalars (𝕜 := 𝕜) (K := RatFunc 𝕜) e₁
      obtain ⟨-, ⟨e₂⟩⟩ := Work.MotV5.class_of_comap_spread 𝕜 P
      rw [hcomap] at e₂
      exact ⟨F₀, hF₀field, alg𝕜, hNC, ⟨e₂.trans e₁'⟩⟩
  · -- ## Vertical case: `p` meets the vertical elements, hence is itself a vertical prime.
    right
    obtain ⟨q, hq, hpq⟩ := Work.MotV5.exists_prime_tPoly_eq_of_not_disjoint 𝕜 p hp1 hdisj
    exact cg_vert_of_prime_tPoly p q hq hpq

end Work.MotV5
