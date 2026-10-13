import Submission.Work.DSM8m2.Setup
import Submission.Work.DSM8m2.Assemble
import Submission.Work.DSM8m2.Chart.finiteType_phiU
import Submission.Work.DSM8m2.Basic.injective_phi_functionField
import Submission.Work.DSM8m2.Algebra.exists_integral_primitive
import Submission.Work.DSM8m2.Algebra.ker_aeval_eq_span_minpoly
import Submission.Work.DSM8m2.Algebra.exists_clearing_denominator
import Submission.Work.DSM8m2.Normalize.exists_notMem_span_dvd
import Submission.Work.DSREG.Main

/-!
# DSM8m2 — the body of `area_M8mpos`

Everything in the proof of `Work.DSM8m2.area_M8mpos` except the single geometric input that the
function field `K(X)` is a *finite* extension of `K = Frac A`, which is supplied by
`Work.DSM8m2.Zariski.functionField_finiteDimensional` (from `IsGenFinite A f`).  Keeping it
separate isolates that input; `Main.lean` is then a short gluing.

The `A`- and `K`-algebra structures on `X.functionField` are hypotheses here, pinned down by `hφL`
(that the `A`-structure is `germToFunctionField X ⊤ ∘ DSMap.phi`), together with the finiteness and
separability of `K(X)/K`.
-/

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Work.DSM8m2

universe a

/-- `area_M8mpos`, with the finiteness and separability of `K(X)/K` as hypotheses. -/
theorem area_M8mpos_of_finiteDimensional (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [IsDomain A] (p : ℕ) [Fact p.Prime] [CharZero A]
    [CharP (ResidueField A) p] (X : Scheme.{a}) [IsIntegral X] [Nonempty (⊤ : X.Opens)]
    (f : X ⟶ Spec (.of A))
    [IsProper f] (hs : Function.Surjective f) (hg : DSMap.IsGenFinite A f)
    (hp : DSMap.IsProjOver A f)
    [Algebra A (X.functionField)]
    (hφL : ∀ a : A, algebraMap A (X.functionField) a =
      (Scheme.germToFunctionField X ⊤).hom (DSMap.phi A X f a))
    [Algebra (FractionRing A) (X.functionField)]
    [IsScalarTower A (FractionRing A) (X.functionField)]
    [FiniteDimensional (FractionRing A) (X.functionField)]
    [Algebra.IsSeparable (FractionRing A) (X.functionField)] :
    ∃ (g : A) (N : ℕ) (i : X ⟶ DSMap.PSpace A N) (j : Fin (N + 1)) (F : Polynomial A)
      (θ : Γ(X, DSMap.Mix2.chartCover i ⟨j⟩) →+*
        Localization.Away (algebraMap A (AdjoinRoot F) ((p : A) * g))),
      g ∉ Ideal.span {(p : A)} ∧ IsClosedImmersion i ∧ i ≫ DSMap.PSpace.toSpec A N = f ∧
      F.Monic ∧
      0 < F.natDegree ∧
      θ.comp (DSMap.phiU A X f (DSMap.Mix2.chartCover i ⟨j⟩)) =
        (algebraMap (AdjoinRoot F) _).comp (algebraMap A (AdjoinRoot F)) := by
  classical
  -- ## 0. `X` is nonempty, and the structure map `A → K(X)` is injective
  have hXne : Nonempty X := by
    obtain ⟨𝔭⟩ : Nonempty (Spec (CommRingCat.of A)) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
    obtain ⟨x, -⟩ := hs 𝔭
    exact ⟨x⟩
  let L := X.functionField
  have hφLinj : Function.Injective (algebraMap A L) := by
    intro x y hxy
    apply Basic.injective_phi_functionField f hs
    simp only [RingHom.comp_apply]
    rw [← hφL x, ← hφL y, hxy]
  -- ## 1. a primitive element `η`, integral over `A`, with `K`-minimal polynomial over `A`
  obtain ⟨η, hηint, hηgen, hηmap⟩ :=
    Algebra.exists_integral_primitive (A := A) (K := FractionRing A) (L := L) hφLinj
  -- ## 2. the chart
  obtain ⟨N, i, hi, hif⟩ := hp
  have hcov : ⨆ k, DSMap.Mix2.chartCover i k = ⊤ := DSMap.Mix2.chartCover_iSup_proved i
  obtain ⟨j, hj⟩ : ∃ j : Fin (N + 1), Nonempty ↥(DSMap.Mix2.chartCover i ⟨j⟩) :=
    exists_nonempty_chart i hcov hXne
  haveI hUj : Nonempty ↥(DSMap.Mix2.chartCover i ⟨j⟩) := hj
  set U : X.Opens := DSMap.Mix2.chartCover i ⟨j⟩ with hU
  haveI hUj' : Nonempty U := hUj
  letI hAlgB : Algebra A Γ(X, U) := (DSMap.phiU A X f U).toAlgebra
  have hBfin : Algebra.FiniteType A Γ(X, U) := by
    have h1 : (DSMap.phiU A X f U).FiniteType :=
      Chart.finiteType_phiU f (DSMap.Mix2.chartCover i)
        (fun k => DSMap.Mix2.chartCover_affine_proved i hi k) ⟨j⟩
    have h2 : (algebraMap A Γ(X, U)).FiniteType := h1
    exact RingHom.finiteType_algebraMap.mp h2
  -- the germ map `Γ(X,U) → K(X)`, as an `A`-algebra map
  let φ : Γ(X, U) →ₐ[A] L :=
    { toFun := (Scheme.germToFunctionField X U).hom
      map_one' := map_one _
      map_mul' := map_mul _
      map_zero' := map_zero _
      map_add' := map_add _
      commutes' := fun a => by
        change (Scheme.germToFunctionField X U).hom (DSMap.phiU A X f U a) = algebraMap A L a
        rw [hφL a]
        exact phiL_phiU A f U a }
  have hφinj : Function.Injective φ := fun x y hxy =>
    Scheme.germToFunctionField_injective X U hxy
  -- ## 3. clear the denominators, and the kernel statement
  obtain ⟨c, hc, hclear⟩ :=
    Algebra.exists_clearing_denominator (A := A) (K := FractionRing A) (L := L)
      (B := Γ(X, U)) φ hBfin hηint hηgen
  have hker : RingHom.ker (Polynomial.aeval η).toRingHom = Ideal.span {minpoly A η} :=
    Algebra.ker_aeval_eq_span_minpoly (A := A) (K := FractionRing A) (L := L) hηint hηmap
  -- ## 4. normalise the denominator to `p * g` with `g ∉ (p)`, and assemble
  obtain ⟨g, hgnotin, m, hdiv⟩ := Normalize.exists_notMem_span_dvd (A := A) p hc
  obtain ⟨θ', hθ'⟩ := exists_algHom_target (A := A) (L := L) (B := Γ(X, U)) φ hφinj
    (minpoly.monic hηint) hker c hc hclear ((p : A) * g) m hdiv
  exact ⟨g, N, i, j, minpoly A η, θ', hgnotin, hi, hif, minpoly.monic hηint,
    minpoly.natDegree_pos hηint, hθ'⟩

end Work.DSM8m2
