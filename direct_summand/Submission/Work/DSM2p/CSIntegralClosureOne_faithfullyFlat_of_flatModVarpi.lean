import Mathlib
import Submission.Work.DSM2p.One
import Submission.Work.DSM2p.flat_quot_ideal_of_flat
import Submission.Work.DSM2p.flat_quot_p_of_flat_quot_varpi_CSIntegralClosurePos
import Submission.Work.DSM2p.flat_quot_p_of_flat_quot_varpi_CSIntegralClosureOne
import Submission.Work.DSM2p.exists_ringHom_Lam1Loc_to_RootAlgLocPos
import Submission.Work.DSM2p.CSCompletionPos_faithfullyFlat
import Submission.Work.DSM2p.smul_top_ne_top_CSIntegralClosurePos
import Submission.Work.DSM2p.exists_model_field_of_prime
import Submission.Work.DSM2p.CSIntegralClosurePos_isSMulRegular
import Submission.Work.DSM2p.CSIntegralClosureOne_isSMulRegular
import Submission.Work.DSM2p.CSIntegralClosurePos_quot_integral
import Submission.Work.DSM2p.SMulTopAux
import Submission.Work.DSM2p.ker_algebraMap_quot_le_maximal_via_model
import Submission.Work.DSM2p.CSAlgPosAux

namespace Work.DSM2p

universe u

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

/-! ## The general last-mile criterion

The two inputs of the target are

* *flatness* of `A'_F ⧸ pA'_F` over `A ⧸ (p)` for the single-polynomial `p`-integral closure
  `A'_F = CSIntegralClosureOne A p ϖ F` of `Λ[1/ϖ]` (`flat_quot_p_of_flat_quot_varpi_CSIntegralClosureOne`,
  obtained from the hypothesis `h` — flatness modulo `ϖ` — by the nilpotent-thickening criterion
  for `(ϖ) ⊆ A ⧸ (ϖ ^ p) = A ⧸ (p)`), and
* *nonvanishing of the fibres* of `A'_F` over the maximal ideals of `A` containing `p`
  (`smul_top_ne_top_CSIntegralClosureOne`, obtained by embedding the one-polynomial construction
  into the Česnavičius–Scholze one and using
  `Work.DSM2p.smul_top_ne_top_CSIntegralClosurePos`).

This file records the general lemma that assembles them: a flat module whose fibres over all
maximal ideals of the base are nonzero is faithfully flat. -/

/-- **Nonvanishing of the fibres is insensitive to pushing forward along an `A`-algebra map.**

Let `g : E →+* E'` be a ring homomorphism compatible with the `A`-algebra structures
(`g ∘ algebraMap A E = algebraMap A E'`).  If `𝔪 • ⊤ ≠ ⊤` in `E'`, then `𝔪 • ⊤ ≠ ⊤` in `E`:
`𝔪 • ⊤ = ⊤` in `E` means `1 ∈ 𝔪 E`, and applying `g` (which is not required to be injective)
gives `1 ∈ 𝔪 E'`.

This is the device by which the one-polynomial fibre statement is reduced to the
Česnavičius–Scholze one (`Work.DSM2p.smul_top_ne_top_CSIntegralClosurePos`). -/
private theorem smul_top_ne_top_of_ringHom {A E E' : Type u} [CommRing A] [CommRing E] [CommRing E']
    [Algebra A E] [Algebra A E'] (𝔪 : Ideal A) (g : E →+* E')
    (hg : g.comp (algebraMap A E) = algebraMap A E')
    (h : 𝔪 • (⊤ : Submodule A E') ≠ ⊤) : 𝔪 • (⊤ : Submodule A E) ≠ ⊤ := by
  intro htop
  apply h
  have hmap : Ideal.map (algebraMap A E) 𝔪 = ⊤ := by
    have h' := htop
    rw [Ideal.smul_top_eq_map] at h'
    exact (Submodule.restrictScalars_eq_top_iff A _ _).mp h'
  have hmap' : Ideal.map (algebraMap A E') 𝔪 = ⊤ := by
    have h2 : Ideal.map g (Ideal.map (algebraMap A E) 𝔪) = ⊤ := by rw [hmap, Ideal.map_top]
    rwa [Ideal.map_map, hg] at h2
  rw [Ideal.smul_top_eq_map, hmap']
  exact Submodule.restrictScalars_top A A E'

/-- **A flat module with nonzero fibres over every maximal ideal is faithfully flat.**

Let `E` be an `A`-algebra, `p : A`, and suppose that `E ⧸ pE` is flat over `A ⧸ (p)` and that
`𝔫 • ⊤ ≠ ⊤` in `E` for every maximal ideal `𝔫 ∋ p` of `A`.  Then `E ⧸ pE` is faithfully flat
over `A ⧸ (p)`.

This is `Module.FaithfullyFlat.iff_flat_and_proper_ideal` combined with the correspondence
between the ideals of `A ⧸ (p)` and the ideals of `A` containing `p`: a proper ideal of `A ⧸ (p)`
is contained in a maximal ideal `𝔪`, whose preimage `𝔫` is a maximal ideal of `A` containing
`p`; if `𝔪` generated the unit ideal of `E ⧸ pE`, then `𝔫` would generate the unit ideal of `E`,
contradicting the hypothesis. -/
private theorem faithfullyFlat_of_flat_of_smul_top_ne_top {A E : Type u} [CommRing A] [CommRing E]
    [Algebra A E] (p : ℕ)
    (hflat : Module.Flat (A ⧸ Ideal.span {(p : A)})
      (E ⧸ (Ideal.span {(p : A)}).map (algebraMap A E)))
    (hne : ∀ 𝔫 : Ideal A, 𝔫.IsMaximal → (p : A) ∈ 𝔫 →
      𝔫 • (⊤ : Submodule A E) ≠ ⊤) :
    Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A)})
      (E ⧸ (Ideal.span {(p : A)}).map (algebraMap A E)) := by
  let I : Ideal A := Ideal.span {(p : A)}
  let M := E ⧸ (Ideal.span {(p : A)}).map (algebraMap A E)
  have hflat' : Module.Flat (A ⧸ I) M := hflat
  haveI : IsScalarTower A (A ⧸ I) M := inferInstance
  rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
  refine ⟨hflat', ?_⟩
  intro J hJ htop
  obtain ⟨𝔪, h𝔪, hJ𝔪⟩ := Ideal.exists_le_maximal J hJ
  set 𝔫 : Ideal A := 𝔪.comap (Ideal.Quotient.mk I) with h𝔫def
  have h𝔫 : 𝔫.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hI𝔫 : I ≤ 𝔫 := fun a ha => by
    rw [h𝔫def, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact 𝔪.zero_mem
  have hmap : Ideal.map (Ideal.Quotient.mk I) 𝔫 = 𝔪 := by
    rw [h𝔫def, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have h𝔪top : 𝔪 • (⊤ : Submodule (A ⧸ I) M) = ⊤ := by
    refine le_antisymm le_top ?_
    calc ⊤ = J • (⊤ : Submodule (A ⧸ I) M) := htop.symm
      _ ≤ 𝔪 • (⊤ : Submodule (A ⧸ I) M) := Submodule.smul_mono_left hJ𝔪
  have hsmul : 𝔫 • (⊤ : Submodule A M)
      = (𝔪 • (⊤ : Submodule (A ⧸ I) M)).restrictScalars A := by
    rw [Ideal.smul_top_eq_map, Ideal.smul_top_eq_map,
      IsScalarTower.algebraMap_eq A (A ⧸ I) M, Ideal.Quotient.algebraMap_eq,
      ← Ideal.map_map, hmap]
    rfl
  have hntop : 𝔫 • (⊤ : Submodule A M) = ⊤ := by
    rw [hsmul, h𝔪top, Submodule.restrictScalars_top]
  have hp𝔫 : (p : A) ∈ 𝔫 := hI𝔫 (Ideal.mem_span_singleton_self _)
  have hchild := hne 𝔫 h𝔫 hp𝔫
  -- the quotient map `π : E → M` and its comap
  set K : Ideal E := (Ideal.span {(p : A)}).map (algebraMap A E) with hKdef
  have hker : LinearMap.ker (Ideal.Quotient.mkₐ A K).toLinearMap = K.restrictScalars A := by
    ext x
    rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hKle : (K.restrictScalars A) ≤ 𝔫 • (⊤ : Submodule A E) := by
    rw [Ideal.smul_top_eq_map, hKdef]
    exact Submodule.restrictScalars_mono (S := A) (Ideal.map_mono hI𝔫)
  have hcomap := Submodule.comap_smul_top_of_surjective (R := A) 𝔫
    (Ideal.Quotient.mkₐ A K).toLinearMap
    (fun x => Ideal.Quotient.mkₐ_surjective A K x)
  rw [hntop, Submodule.comap_top, hker, sup_eq_left.mpr hKle] at hcomap
  exact hchild hcomap.symm

/-! ## The fibre nonvanishing for the one-polynomial construction

`A'_F = CSIntegralClosureOne A p (P.ϖ 0) F` is the `p`-integral closure of
`A_∞^{(F)} = Λ[F(T)/ϖ^m]` inside `Λ[1/ϖ]`, `Λ = A[T^{1/p^∞}]`.  Sending the single root variable
`T` to the root variable `T_F` of the Česnavičius–Scholze ring defines an `A`-algebra map
`Λ[1/ϖ] → Λ[1/ϖ]` (`Work.DSM2p.exists_ringHom_Lam1Loc_to_RootAlgLocPos`) which carries `A'_F`
into the full `A' = CSIntegralClosurePos A p (P.ϖ 0)`.  Hence a maximal ideal `𝔪 ∋ p` that
*does* generate the unit ideal of `A'_F` would also generate the unit ideal of `A'`, which is
excluded by `Work.DSM2p.smul_top_ne_top_CSIntegralClosurePos`. -/
private theorem smul_top_ne_top_CSIntegralClosureOne_aux (p : ℕ) [Fact p.Prime] (A : Type*)
    [CommRing A] (P : DSMap.PerfectoidData p A) (F : Polynomial A) (hF : F.Monic)
    (hFd : 0 < F.natDegree) (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) (hp : (p : A) ∈ 𝔪) :
    𝔪 • (⊤ : Submodule A ↥(CSIntegralClosureOne A p (P.ϖ 0) F)) ≠ ⊤ := by
  obtain ⟨φ, hφA, hφle⟩ := exists_ringHom_Lam1Loc_to_RootAlgLocPos A p (P.ϖ 0) F hF hFd
  -- the induced ring hom `A'_F →+* A'`
  let g : ↥(CSIntegralClosureOne A p (P.ϖ 0) F) →+* ↥(CSIntegralClosurePos A p (P.ϖ 0)) :=
    RingHom.codRestrict (φ.comp (Subring.subtype _)) _
      (fun x => Subring.mem_comap.mp (hφle x.2))
  have hg : g.comp (algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F))
      = algebraMap A ↥(CSIntegralClosurePos A p (P.ϖ 0)) := by
    ext a
    simp only [RingHom.comp_apply, g, RingHom.codRestrict_apply]
    exact hφA a
  exact smul_top_ne_top_of_ringHom 𝔪 g hg (smul_top_ne_top_CSIntegralClosurePos p A P 𝔪 h𝔪 hp)

set_option synthInstance.maxHeartbeats 1600000 in
theorem CSIntegralClosureOne_faithfullyFlat_of_flatModVarpi (A : Type*) [CommRing A] (p : ℕ)
    [Fact p.Prime] (P : DSMap.PerfectoidData p A) (F : Polynomial A) (hF : F.Monic)
    (hFd : 0 < F.natDegree)
    (h : Module.Flat (A ⧸ Ideal.span {(P.ϖ 0 : A)})
      (↥(CSIntegralClosureOne A p (P.ϖ 0) F) ⧸
        (Ideal.span {(P.ϖ 0 : A)}).map (algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F)))) :
    Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A)})
      (↥(CSIntegralClosureOne A p (P.ϖ 0) F) ⧸
        (Ideal.span {(p : A)}).map (algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F))) :=
  faithfullyFlat_of_flat_of_smul_top_ne_top (A := A)
    (E := ↥(CSIntegralClosureOne A p (P.ϖ 0) F)) p
    (flat_quot_p_of_flat_quot_varpi_CSIntegralClosureOne p A P F h)
    (fun 𝔫 h𝔫 hp => smul_top_ne_top_CSIntegralClosureOne_aux p A P F hF hFd 𝔫 h𝔫 hp)

end Work.DSM2p
