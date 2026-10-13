/-
Area DSCOH — the deliverable: `DSMap.area_COH_proved`.

`DSMap.area_COH_proved` has *exactly* the type of the frozen area statement `DSMap.area_COH`
(`Submission/Work/DSMap/Map.lean`), checked at the bottom of this file with `rfl`:

    ∃ N : ℤ, ∀ i : ℤ,
      Module.Finite A (H^i (ι (RΓ(X, 𝒪_X)))) ∧ (N < i → IsZero (H^i (ι (RΓ(X, 𝒪_X)))))

for `A` Noetherian and `X` projective over `A` (`DSMap.IsProjOver A f`), i.e. a closed subscheme
of some `ℙᴺ_A`.

## The proof

`f` factors through a closed immersion `i : X ↪ ℙᴺ_A`, giving the finite affine chart cover
`U_k = X ∩ D₊(x_k)` (`DSMap.Mix2.chartCover i`, affine and covering by DSCHART's
`chartCover_affine_proved` / `chartCover_iSup_proved`).  Three inputs, each proved axiom-clean,
are combined:

1. **The Čech model of `RΓ` (area F1, `DSMap.area_F1_cech_proved`).**  For the chart cover,
   `ι(RΓ(X, 𝒪_X)) ≅ Q(cechZ A X f U)` (an isomorphism in `D(A)`).
2. **The geometric bridge.**  The Čech complex of the cover is identified with the *chart* Čech
   complex of a finitely generated graded module `M = A[x₀,…,x_N] ⧸ J` (the saturation of the
   vanishing ideal of `X`), i.e. `H^q(cechZ) ≅ H^q(chartCech M)`:
   * `Work.DSEQP.chartCechTerm_iso` (area DSEQP): the chart Čech term `degZero (Mg i) S` is the
     module of sections of `𝒪_X` over the chart `U_S`, compatibly with the restriction maps;
   * `Work.DSCOH.altCech_iso_chartCech_of_termwise`: a termwise comparison compatible with the
     restrictions induces an isomorphism `altCech ≅ chartCech` of complexes;
   * `Work.DSCOH.altCech_reindex_ulift`: the reindexing `ULift (Fin (N+1)) ≃o Fin (N+1)` (the
     `ULift` is forced by the universe of F1's cover);
   * `Work.DSCOH.cechComplexFunctor_homology_iso` (this area, `(1c)`): Mathlib's unnormalized
     Čech complex `cechComplexFunctor` is quasi-isomorphic to the alternating complex `altCech`
     (Stacks Tag 01FG §20.23: all tuples = semi-ordered = ordered = subsets, through the explicit
     homotopies `Work.DSCOH.Norm.allT_homotopy_semiT` and `Work.DSCOH.Norm.semiHom_homotopy`);
   * `Work.DSCOH.cechZ_homology_iso_chartCech`: the composition, at the level of `ℤ`-indexed
     homology (including the extension `cechZ = cech.extend embeddingUpNat`).
3. **Coherence of the chart Čech complex (this area's theorem
   `Work.DSCOH.chartCech_finite_vanishing`).**  Its cohomology is a finitely generated `A`-module
   and vanishes above `N`; together with 2. this gives the finiteness and vanishing of
   `H^q(cechZ A X f U)`.

The assembly `Work.DSCOH.area_COH_of_F1_and_bridge_proj` (`ConditionalMain.lean`) combines 1.–3.
into the frozen conclusion, with `N = the number of charts`; the vanishing for `i < 0` comes from
`Work.DSCOH.RG_homology_isZero_of_neg` (needed because the frozen statement asks for
`Module.Finite` in *all* degrees).

See `DESIGN.md` for the full account and `Interface.lean` for the axiom check of every module.
-/
import Submission.Work.DSCOH.cechZ_homology_iso_chartCech
import Submission.Work.DSCOH.cechComplexFunctor_homology_iso
import Submission.Work.DSCOH.chartCech_finite_vanishing
import Submission.Work.DSCOH.ConditionalMain
import Submission.Work.DSCOH.Assembly
import Submission.Work.DSF1.Main
import Submission.Work.DSEQP.gf_isProjOver_isProper
import Submission.Work.DSEQP.gf_bridge
import Submission.Work.DSCHART.Main
import Submission.Work.DSMap.Map

open CategoryTheory AlgebraicGeometry Limits

set_option linter.style.haveILetI false

namespace DSMap

universe a b c

/-- **Area COH of `#direct_summand`**: for `A` Noetherian and `X` projective over `A`
(a closed subscheme of some `ℙᴺ_A`), the cohomology `H^i(X, 𝒪_X)` is a finitely generated
`A`-module, and vanishes for all sufficiently large `i`. -/
theorem area_COH_proved (A : Type a) [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{b} (ModuleCat.{a} A)] (X : Scheme.{a}) (f : X ⟶ Spec (.of A))
    [HasDerivedCategory.{c} (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)] (hp : IsProjOver A f) :
    ∃ N : ℤ, ∀ i : ℤ,
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{a} A) i).obj
        (DerivedCategory.Plus.ι.obj (RG A X f))) ∧
      (N < i → Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{a} A) i).obj
        (DerivedCategory.Plus.ι.obj (RG A X f)))) := by
  classical
  -- A closed immersion `i : X ⊆ ℙᴺ_A` with `i ≫ ℙᴺ_A ⟶ Spec A = f`.
  obtain ⟨N, i, hi, hif⟩ := hp
  -- `X` is projective over `A`, hence `f` is proper (area DSEQP), hence separated and
  -- quasi-compact, as required by area F1's Čech model.
  haveI : IsProper f := Work.DSEQP.gf_isProjOver_isProper A X f ⟨N, i, hi, hif⟩
  haveI : IsSeparated f := inferInstance
  haveI : QuasiCompact f := by
    have h := (inferInstance : IsProper f)
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.2
  -- The chart cover of `X`: finite, affine, covering (area DSCHART).
  have hU : ∀ k, IsAffineOpen (Mix2.chartCover i k) := Mix2.chartCover_affine_proved i hi
  have hcov : ⨆ k, Mix2.chartCover i k = ⊤ := Mix2.chartCover_iSup_proved i
  -- Input 1: the Čech model of `RΓ(X, 𝒪_X)` for that cover (area F1).
  obtain ⟨cc, e, -, -⟩ := area_F1_cech_proved (A := A) X f (Mix2.chartCover i) hU hcov
  -- Input 2: the geometric bridge `H^q(cechZ A X f U) ≅ H^q(chartCech (A[x₀,…,x_N]/J))`,
  -- obtained from `(1b)` (area DSEQP) and `(1c)` (this area) via the two matching lemmas.
  have hbridge := fun {N' : ℕ} (i' : X ⟶ PSpace A N') (hi' : IsClosedImmersion i')
      (hif' : i' ≫ PSpace.toSpec A N' = f) =>
    Work.DSCOH.cechZ_homology_iso_chartCech (A := A) N' i' hi' f hif'
      (fun q => Work.DSCOH.cechComplexFunctor_homology_iso (A := A) (X := X)
        (ι := ULift.{a} (Fin (N' + 1))) (P := cechPresheaf A X f)
        (U := Mix2.chartCover i') (q := q))
  -- The graded-module structure of `M = A[x₀,…,x_N] ⧸ J` (area DSEQP).
  haveI : DirectSum.Decomposition (Work.DSEQP.Mg i) := Work.DSEQP.MgDecomposition i
  haveI : Module.Finite (Work.DSCOH.Poly A (N + 1)) (Work.DSEQP.Mmod i) :=
    Work.DSEQP.finite_Mmod i
  -- Input 3 is the area theorem `Work.DSCOH.chartCech_finite_vanishing`, used by the assembly.
  exact Work.DSCOH.area_COH_of_F1_and_bridge_proj A X f i hi hif e (hbridge i hi hif)

/-- The type of `area_COH_proved` is definitionally identical to the type of the frozen
`DSMap.area_COH`. -/
example : type_of% (@area_COH_proved.{a, b, c}) = type_of% (@area_COH.{a, b, c}) := rfl

end DSMap
