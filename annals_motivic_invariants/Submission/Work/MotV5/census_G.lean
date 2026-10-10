import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotA.Spread
import Submission.Work.MotA.SpreadAux
import Submission.Work.MotA.spreadMap_injective
import Submission.Work.MotA.dvd_spread_iff
import Submission.Work.MotA.quotient_vertical
import Submission.Work.MotA.prime_aeval_X0
import Submission.Work.MotV5.class_of_comap_spread
import Submission.Work.MotV5.fractionRing_mvPoly_fin_add
import Submission.Work.MotV5.fractionRing_mvPoly_one
import Submission.Work.MotV5.isLocalization_spreadMap
import Submission.Work.MotV5.census_G_vert

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.MotV5

/-- **Restricting scalars of an algebra isomorphism.**  If `A` and `B` are `K`-algebras which are
also `𝕜`-algebras with scalar towers through `K`, then a `K`-algebra isomorphism is automatically a
`𝕜`-algebra isomorphism (the `𝕜`-structure map factors through `K`). -/
theorem nonempty_algEquiv_restrictScalars {𝕜 K A B : Type} [Field 𝕜] [CommSemiring K]
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
theorem not_constantsOnly_of_geomRuled {𝕜 K : Type} [Field 𝕜] [Field K] [Algebra 𝕜 K]
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

/-- **Node `SPREAD`, the `G`-side census at the level of `𝔸⁴_𝕜`.**

Setting: `K = RatFunc 𝕜`, `L : LinkCert K F₁ F₂` a `K`-level link certificate with `L.F`, `L.G ∈ K[x₀,x₁,x₂]`,
`L.zP` a height-one point of `𝔸³_K` with `L.G ∈ L.zP.asIdeal` and residue field `RatFunc F₁`, and
`G' ∈ 𝕜[x₀,…,x₃]`, `cG ∈ 𝕜[t]` with `cG ≠ 0` and `spreadMap 𝕜 3 G' = C cG * L.G` (exactly what
`Work.MotA.exists_spread_awayAlgEquiv` produces).

Conclusion: for every height-one prime `p` of `𝕜[x₀,…,x₃]` with `G' ∈ p`, either `p` is the
*horizontal lift* `q := Ideal.comap (spreadMap 𝕜 3) L.zP.asIdeal` of `L.zP` — the distinguished
point of the link — or the fraction field `FractionRing (𝕜[Fin 4] ⧸ p)` is `RatFunc F₀` for a
`𝕜`-field `F₀` that is *not* constants-only (`¬ ConstantsOnly 𝕜 F₀`, i.e. `F₀` is geometrically ruled:
it has a non-constant `𝕜`-embedding into a rational function field).  In other words: all prime
divisors of `G'` other than the lift of `zP` have "junk" class. -/
theorem census_G {𝕜 : Type} [Field 𝕜] {F₁ F₂ : Type} [Field F₁] [Field F₂]
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
    Work.MotV5.isLocalization_spreadMap 𝕜 3
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
        not_constantsOnly_of_geomRuled (K := RatFunc 𝕜) hGeo
      obtain ⟨e₁ : FractionRing (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P) ≃ₐ[RatFunc 𝕜] RatFunc F₀⟩ :=
        he
      haveI hstS : IsScalarTower 𝕜 (RatFunc 𝕜)
          (FractionRing (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ P)) := inferInstance
      obtain ⟨e₁'⟩ := nonempty_algEquiv_restrictScalars (𝕜 := 𝕜) (K := RatFunc 𝕜) e₁
      obtain ⟨-, ⟨e₂⟩⟩ := Work.MotV5.class_of_comap_spread 𝕜 P
      rw [hcomap] at e₂
      exact ⟨F₀, hF₀field, alg𝕜, hNC, ⟨e₂.trans e₁'⟩⟩
  · -- ## Vertical case: `p` meets the vertical elements.
    exact Or.inr (Work.MotV5.census_G_vert p hp1 hdisj)

end Work.MotV5
