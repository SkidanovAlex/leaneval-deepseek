import Mathlib
import Submission.Work.SSGRoute.PT.finHalfData
import Submission.Work.SSGRoute.PT.vf_aux
import Submission.Work.SSGRoute.PT.exists_smul_ofFinite_finQW_eq
import Submission.Work.SSGRoute.glue_fin_decomp_ex
import Submission.Work.SSGRoute.exists_smul_eq_of_liesOver_under
import Submission.Work.SSGRoute.E7cOmega.exists_transversal_containing
import Submission.Work.SSGRoute.place_basics
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise
open NumberField IsDedekindDomain

namespace Work.SSGRoute.PT

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-! ## The orbit decomposition of the places of a level -/

/-- The orbit relation of `Gal(L/k)` on the places of `L`. -/
def placeOrbitRel (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    [NumberField L] (x y : NK.GlobalCFT.Place ↥L) : Prop :=
  ∃ σ : ↥L ≃ₐ[k] ↥L, σ • x = y

/-- The setoid of `Gal(L/k)`-orbits of the places of `L`. -/
def placeOrbitSetoid (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    [NumberField L] : Setoid (NK.GlobalCFT.Place ↥L) where
  r := placeOrbitRel L
  iseqv := ⟨fun x => ⟨1, one_smul _ x⟩,
    fun {x y} h => by
      obtain ⟨σ, hσ⟩ := h
      exact ⟨σ⁻¹, by rw [← hσ, inv_smul_smul]⟩,
    fun {x y z} hxy hyz => by
      obtain ⟨σ, hσ⟩ := hxy
      obtain ⟨τ, hτ⟩ := hyz
      exact ⟨τ * σ, by rw [mul_smul, hσ, hτ]⟩⟩

/-- **The finite part of the transversal**: the places of `L` cut out by the elements of `R`. -/
def finPart (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L] [NumberField L]
    (R : Set (ValuationSubring Ω)) (hRfin : ∀ v ∈ R, SSGRoute.IsFinPlace k v) :
    Set (NK.GlobalCFT.Place ↥L) :=
  {x | ∃ (v : ValuationSubring Ω) (hv : v ∈ R),
    x = NK.GlobalCFT.Place.ofFinite (finQW L v (hRfin v hv))}

/-- **The transversal of the places of `L`**: the finite part, together with `Quotient.out` of
every remaining (necessarily infinite) orbit. -/
noncomputable def transvSet (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    [NumberField L] (R : Set (ValuationSubring Ω))
    (hRfin : ∀ v ∈ R, SSGRoute.IsFinPlace k v) : Set (NK.GlobalCFT.Place ↥L) :=
  finPart L R hRfin ∪
    {x | ¬ x.IsFinite ∧ x = Quotient.out (Quotient.mk (placeOrbitSetoid L) x)}

/-- The place `ofFinite (finQW L v)` does not depend on the proof that `v` is a finite place. -/
theorem ofFinite_finQW_congr (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    [NumberField L] {v : ValuationSubring Ω} (h1 h2 : SSGRoute.IsFinPlace k v) :
    NK.GlobalCFT.Place.ofFinite (finQW L v h1) = NK.GlobalCFT.Place.ofFinite (finQW L v h2) :=
  congrArg (fun h => NK.GlobalCFT.Place.ofFinite (finQW L v h)) (Subsingleton.elim h1 h2)

/-- **The finite part is injective (in conjugate form).**  Two elements of `R` whose traces on `L`
are `Gal(L/k)`-conjugate are equal.  The conjugating element of `Gal(L/k)` lifts to `Ω`; the
translated place and the second one then have the same trace on `L`, hence are `Gal(Ω/L)`-conjugate,
which exhibits the two finite places of `Ω` as `Gal(Ω/k)`-conjugate. -/
theorem finQW_smul_injective (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    [NumberField L] (R : Set (ValuationSubring Ω)) (hRfin : ∀ v ∈ R, SSGRoute.IsFinPlace k v)
    (hRdisj : ∀ v ∈ R, ∀ w ∈ R, SSGRoute.IsConjPlace k v w → v = w)
    (v w : ValuationSubring Ω) (hv : v ∈ R) (hw : w ∈ R) (σ : ↥L ≃ₐ[k] ↥L)
    (h : σ • NK.GlobalCFT.Place.ofFinite (finQW L v (hRfin v hv)) =
      NK.GlobalCFT.Place.ofFinite (finQW L w (hRfin w hw))) :
    v = w := by
  obtain ⟨τ, hτ⟩ := exists_restrictNormal_eq_of_isAlgClosure L σ
  have hv' : SSGRoute.IsFinPlace k (τ • v) :=
    (Work.SSGRoute.isFinPlace_smul_iff v τ).mpr (hRfin v hv)
  have h1 : NK.GlobalCFT.Place.ofFinite (finQW L (τ • v) hv') =
      NK.GlobalCFT.Place.ofFinite (finQW L w (hRfin w hw)) := by
    rw [ofFinite_finQW_smul L v (hRfin v hv) τ hv', hτ]
    exact h
  have hq : finQW L (τ • v) hv' = finQW L w (hRfin w hw) :=
    NK.GlobalCFT.Place.ofFinite_inj.mp h1
  have hcomap : (τ • v).comap (algebraMap ↥L Ω) = w.comap (algebraMap ↥L Ω) := by
    rw [finQW_comap L (τ • v) hv', finQW_comap L w (hRfin w hw), hq]
  obtain ⟨ρ, hρ⟩ := exists_smul_eq_of_comap_eq_of_isAlgClosure L (τ • v) w hcomap
  exact hRdisj v hv w hw (isConjPlace_of_smul_smul L (A := v) (B := w) τ ρ hρ)

/-- **Transversal of the places of a level, from a transversal of the finite places of `Ω`.**

Given `k ⊆ K ⊆ L ⊆ Ω` with `K/k` and `L/k` finite Galois, and a set `R` of finite places of `Ω`
meeting every `Gal(Ω/k)`-orbit of finite places exactly once (i.e. one place per prime of `k`), the
places `ofFinite (finQW L v hA)` (the prime of `𝓞 L` under `v`) form part of a transversal of the
`Gal(L/k)`-orbits of the places of `L`.  Concretely there is `R'' : Set (Place ↥L)` which

* contains `ofFinite (finQW L v hA)` for every `v ∈ R`;
* meets every `Gal(L/k)`-orbit of places of `L` in exactly one point;
* has injective restriction map `v ↦ ofFinite (finQW L v hA)` on `R`;
* has no finite places other than those, i.e. a finite `w ∈ R''` is `ofFinite (finQW L v hA)` for
  some `v ∈ R` (so `R` is in bijection with the finite part of `R''`).

Proof ingredients (all on disk): every place of `L` lies over a place of `K`
(`NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder`); every prime of `𝓞 K` is the trace of a
finite place of `Ω` (`Work.SSGRoute.exists_isFinPlace_comap_eq` in
`Submission/Work/SSGRoute/glue_fin_decomp_ex.lean`); `hRcov`/`hRdisj` then produce the unique
`v ∈ R`; `Gal(L/k)` is transitive on the places above a place of `K`
(`NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver`,
`Work.SSGRoute.exists_smul_eq_of_liesOver_under`); "conjugate ⟺ same trace on `k`" is
`Work.SSGRoute.isConjPlace_iff_comap_eq_of_isFinPlace` (which can be re-derived from
`Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq`).  A finite-place transversal is extended
to a full one by adding `Quotient.out` of the finitely many infinite orbits (see
`Work.SSGRoute.E7cOmega.exists_transversal_containing`). -/
theorem vf_transverse {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K L : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] [FiniteDimensional k L] [IsGalois k L] [NumberField L] (hKL : K ≤ L)
    (R : Set (ValuationSubring Ω)) (hRfin : ∀ v ∈ R, SSGRoute.IsFinPlace k v)
    (hRdisj : ∀ v ∈ R, ∀ w ∈ R, SSGRoute.IsConjPlace k v w → v = w)
    (hRcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → ∃ v ∈ R, SSGRoute.IsConjPlace k v B) :
    ∃ R'' : Set (NK.GlobalCFT.Place ↥L),
      (∀ (v : ValuationSubring Ω) (hv : v ∈ R),
        NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L v (hRfin v hv)) ∈ R'') ∧
      (∀ w : NK.GlobalCFT.Place ↥L, ∃! w' : R'', ∃ σ : ↥L ≃ₐ[k] ↥L, σ • w = w'.1) ∧
      (∀ (v w : ValuationSubring Ω) (hv : v ∈ R) (hw : w ∈ R),
        NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L v (hRfin v hv)) =
        NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L w (hRfin w hw)) → v = w) ∧
      (∀ (w : R''), (∃ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L),
          w.1 = NK.GlobalCFT.Place.ofFinite q) →
        ∃ (v : ValuationSubring Ω) (hv : v ∈ R),
          w.1 = NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L v (hRfin v hv))) := by
  classical
  refine ⟨transvSet L R hRfin, ?_, ?_, ?_, ?_⟩
  · -- the finite part is contained in the transversal
    intro v hv
    exact Or.inl ⟨v, hv, rfl⟩
  · -- existence and uniqueness of the representative of an orbit
    intro w
    by_cases hw : w.IsFinite
    · -- `w` is finite: it is conjugate to the place below an element of `R`
      obtain ⟨q, hwq⟩ := NK.GlobalCFT.Place.isFinite_iff.mp hw
      obtain ⟨v, hv, σ, hσ⟩ := exists_smul_ofFinite_finQW_eq L R hRfin hRcov q
      refine ⟨⟨NK.GlobalCFT.Place.ofFinite (finQW L v (hRfin v hv)),
        Or.inl ⟨v, hv, rfl⟩⟩, ⟨σ, ?_⟩, ?_⟩
      · rw [hwq]
        exact hσ
      · rintro ⟨y, hy⟩ ⟨τ, hτ⟩
        have hτ' : τ • w = y := hτ
        rcases hy with hy | hy
        · -- `y` is the place below an element `u ∈ R`: then `u = v` by injectivity
          obtain ⟨u, hu, hyu⟩ := hy
          have hconj : ∃ ρ : ↥L ≃ₐ[k] ↥L,
              ρ • NK.GlobalCFT.Place.ofFinite (finQW L v (hRfin v hv)) =
                NK.GlobalCFT.Place.ofFinite (finQW L u (hRfin u hu)) := by
            refine ⟨(σ * τ⁻¹)⁻¹, ?_⟩
            have h1 : NK.GlobalCFT.Place.ofFinite (finQW L v (hRfin v hv)) =
                (σ * τ⁻¹) • NK.GlobalCFT.Place.ofFinite (finQW L u (hRfin u hu)) := by
              rw [← hσ, ← hwq, ← hyu, ← hτ', mul_smul, inv_smul_smul]
            rw [h1, inv_smul_smul]
          obtain ⟨ρ, hρ⟩ := hconj
          have hvu : v = u := finQW_smul_injective L R hRfin hRdisj v u hv hu ρ hρ
          have key : NK.GlobalCFT.Place.ofFinite (finQW L u (hRfin u hu)) =
              NK.GlobalCFT.Place.ofFinite (finQW L v (hRfin v hv)) :=
            congrArg NK.GlobalCFT.Place.ofFinite
              (finQW_congr L hvu.symm (hRfin u hu) (hRfin v hv))
          apply Subtype.ext
          show y = NK.GlobalCFT.Place.ofFinite (finQW L v (hRfin v hv))
          exact hyu.trans key
        · -- `y` is infinite, but it is conjugate to the finite place `w`
          obtain ⟨hyinf, -⟩ := hy
          have hfin : y.IsFinite := by
            rw [← hτ']
            exact (isFinite_smul_iff L τ w).mpr hw
          exact absurd hfin hyinf
    · -- `w` is infinite: take the canonical representative `Quotient.out` of its orbit
      let x₀ : NK.GlobalCFT.Place ↥L := Quotient.out (Quotient.mk (placeOrbitSetoid L) w)
      have hx₀orbit : placeOrbitRel L w x₀ :=
        Quotient.exact (Quotient.out_eq (Quotient.mk (placeOrbitSetoid L) w)).symm
      have hx₀inf : ¬ x₀.IsFinite := by
        rintro hfin
        obtain ⟨σ, hσ⟩ := hx₀orbit
        rw [← hσ] at hfin
        exact hw ((isFinite_smul_iff L σ w).mp hfin)
      have hx₀out : x₀ = Quotient.out (Quotient.mk (placeOrbitSetoid L) x₀) :=
        (congrArg Quotient.out (Quotient.out_eq (Quotient.mk (placeOrbitSetoid L) w))).symm
      refine ⟨⟨x₀, Or.inr ⟨hx₀inf, hx₀out⟩⟩, hx₀orbit, ?_⟩
      rintro ⟨y, hy⟩ ⟨τ, hτ⟩
      have hτ' : τ • w = y := hτ
      rcases hy with hy | hy
      · -- `y` is finite, but it is conjugate to the infinite place `w`
        obtain ⟨u, hu, hyu⟩ := hy
        have hfin : y.IsFinite := by
          rw [hyu]
          exact NK.GlobalCFT.Place.isFinite_ofFinite _
        rw [← hτ'] at hfin
        exact absurd ((isFinite_smul_iff L τ w).mp hfin) hw
      · -- `y` is the canonical representative of its own orbit, which is the orbit of `w`
        obtain ⟨-, hyout⟩ := hy
        have hqw : Quotient.mk (placeOrbitSetoid L) w = Quotient.mk (placeOrbitSetoid L) y :=
          Quotient.sound ⟨τ, hτ'⟩
        apply Subtype.ext
        show y = Quotient.out (Quotient.mk (placeOrbitSetoid L) w)
        rw [hyout, ← hqw]
  · -- injectivity of `v ↦ ofFinite (finQW L v)`
    intro v w hv hw h
    exact finQW_smul_injective L R hRfin hRdisj v w hv hw 1 (by simpa using h)
  · -- the finite places of the transversal are exactly the places below elements of `R`
    rintro ⟨y, hy⟩ ⟨q, hq⟩
    have hq' : y = NK.GlobalCFT.Place.ofFinite q := hq
    rcases hy with hy | hy
    · exact hy
    · obtain ⟨hyinf, -⟩ := hy
      exact absurd (hq' ▸ NK.GlobalCFT.Place.isFinite_ofFinite q) hyinf

end Work.SSGRoute.PT
