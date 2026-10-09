import Mathlib
import Submission.NK.GlobalCFT.Inclusion
import Submission.NK.GlobalCFT.Idele
import Submission.NK.GlobalCFT.GaloisIdeles
import Submission.NK.GlobalCFT.GaloisIdelesAction
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_smul
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_mem_localUnits
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
import Submission.NK.GlobalCFT.Galois.globalCFT_localRingEquiv_localAlgebraMapUnits
import Submission.NK.GlobalCFT.Galois.globalCFT_localRingEquiv_comp
import Submission.NK.GlobalCFT.Galois.globalCFT_localFixed_finite
import Submission.NK.GlobalCFT.Galois.globalCFT_localFixed_infinite
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_mem_integers_iff
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.Galois

open NK.GlobalCFT

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- If an idèle is fixed by `Gal(L/K)` then its components are equivariant for the local
isomorphisms: `(σ • x)_w = σ_*(x_w)`. -/
theorem globalCFT_unitsMap_localRingEquiv_of_fixed [FiniteDimensional K L] [IsGalois K L]
    (x : 𝕀[L]) (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x) (σ : L ≃ₐ[K] L) (w : Place L) :
    Units.map (Place.localRingEquiv σ w).toMonoidHom (x w) = x (σ • w) := by
  have h := congrArg (fun y : 𝕀[L] => y w) (hx σ⁻¹)
  rw [Idele.smul_apply] at h
  rw [inv_inv] at h
  rw [← h]
  ext
  simp

end NK.GlobalCFT.Galois

namespace NK.GlobalCFT.Inclusion

open NK.GlobalCFT

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- Extract `q.asIdeal.LiesOver Q.asIdeal` from a `Place`-level `LiesOver` at finite places. -/
lemma globalCFT_asIdeal_liesOver_of_liesOver_ofFinite {q : HeightOneSpectrum (𝓞 L)}
    {Q : HeightOneSpectrum (𝓞 K)}
    (h : Place.LiesOver (Place.ofFinite q) (Place.ofFinite Q)) :
    q.asIdeal.LiesOver Q.asIdeal := by
  rcases (Place.liesOver_iff _ _).mp h with ⟨w', v', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
  · exact absurd h1 (Ne.symm (Place.ofInfinite_ne_ofFinite w' q))
  · rw [Place.ofFinite_inj] at h1 h2
    rw [← h1, ← h2] at h3
    exact h3

/-- **The local fixed point lemma.**  If a unit `y` of the local field `L_w` is fixed by the whole
decomposition group of `w` (acting through the canonical local isomorphisms
`Place.localRingEquiv`), then it is the image of a unit of `K_v` under the local algebra map. -/
theorem globalCFT_localFixed_mem_range [FiniteDimensional K L] [IsGalois K L]
    {w : Place L} {v : Place K} (h : Place.LiesOver w v)
    (y : (Place.localField L w)ˣ)
    (hy : ∀ σ : L ≃ₐ[K] L, ∀ (hσ : σ • w = w),
      Units.map (Place.localRingEquiv σ w).toMonoidHom y = hσ.symm ▸ y) :
    ∃ a : (Place.localField K v)ˣ, Place.localAlgebraMapUnits w v h a = y := by
  rcases w with w | q <;> rcases v with v | Q
  · have hwv : w.LiesOver v := by
      rcases (Place.liesOver_iff _ _).mp h with
        ⟨w', v', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
      · rw [Place.ofInfinite_inj] at h1 h2
        rw [← h1, ← h2] at h3
        exact h3
      · exact absurd h1 (Place.ofInfinite_ne_ofFinite w q')
    simpa using Galois.globalCFT_localFixed_infinite hwv y hy
  · rcases (Place.liesOver_iff _ _).mp h with ⟨w', v', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
    · exact absurd h2 (Ne.symm (Place.ofInfinite_ne_ofFinite v' Q))
    · exact absurd h1 (Place.ofInfinite_ne_ofFinite w q')
  · rcases (Place.liesOver_iff _ _).mp h with ⟨w', v', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
    · exact absurd h1 (Ne.symm (Place.ofInfinite_ne_ofFinite w' q))
    · exact absurd h2 (Place.ofInfinite_ne_ofFinite v Q')
  · have hqQ := globalCFT_asIdeal_liesOver_of_liesOver_ofFinite h
    simpa using Galois.globalCFT_localFixed_finite hqQ y hy

/-- A place of `L` above a given place of `K`; chosen using `globalCFT_exists_placeOver`. -/
theorem globalCFT_exists_placeOver [FiniteDimensional K L] (v : Place K) :
    ∃ w : Place L, Place.LiesOver w v := by
  rcases v with v | Q
  · haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v
    refine ⟨Place.ofInfinite w, Place.liesOver_ofInfinite ⟨?_⟩⟩
    have hh : (w.comap (algebraMap K L)).1 = v.1 := congrArg Subtype.val hw
    rw [← hh]
    rfl
  · obtain ⟨q, hq⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
      (K := K) (L := L) Q
    exact ⟨Place.ofFinite q, Place.liesOver_ofFinite hq⟩

/-- The converse of `globalCFT_localAlgebraMapUnits_mapsTo_localUnits`. -/
theorem globalCFT_mem_localUnits_of_localAlgebraMapUnits [FiniteDimensional K L]
    {w : Place L} {v : Place K} (h : Place.LiesOver w v) {a : (Place.localField K v)ˣ}
    (ha : Place.localAlgebraMapUnits w v h a ∈ Place.localUnits L w) :
    a ∈ Place.localUnits K v := by
  rcases w with w | q <;> rcases v with v | Q
  · exact Subgroup.mem_top _
  · rcases (Place.liesOver_iff _ _).mp h with ⟨w', v', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
    · exact absurd h2 (Ne.symm (Place.ofInfinite_ne_ofFinite v' Q))
    · exact absurd h1 (Place.ofInfinite_ne_ofFinite w q')
  · rcases (Place.liesOver_iff _ _).mp h with ⟨w', v', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
    · exact absurd h1 (Ne.symm (Place.ofInfinite_ne_ofFinite w' q))
    · exact absurd h2 (Place.ofInfinite_ne_ofFinite v Q')
  · have hqQ := globalCFT_asIdeal_liesOver_of_liesOver_ofFinite h
    have hmap : Place.localAlgebraMapUnits (Place.ofFinite q) (Place.ofFinite Q) h
        = Units.map (Commons.RingTheory.Henselian.adicCompletionMap Q q hqQ).toMonoidHom := by
      rw [Place.localAlgebraMapUnits]
      simp only [Sum.casesOn]
      rw [dif_pos hqQ]
    rw [hmap] at ha
    have key : ∀ b : (Q.adicCompletion K)ˣ,
        Units.map (Commons.RingTheory.Henselian.adicCompletionMap Q q hqQ).toMonoidHom b ∈
          (q.adicCompletionIntegers L).units → b ∈ (Q.adicCompletionIntegers K).units := by
      intro b hb
      have hb1 : Commons.RingTheory.Henselian.adicCompletionMap Q q hqQ
          (b : Q.adicCompletion K) ∈ (q.adicCompletionIntegers L) :=
        (Submonoid.mem_units_iff _ _).mp hb |>.1
      have hbinv : Units.map (Commons.RingTheory.Henselian.adicCompletionMap Q q hqQ).toMonoidHom
          b⁻¹ ∈ (q.adicCompletionIntegers L).units := by
        simpa only [map_inv] using
          Subgroup.inv_mem ((q.adicCompletionIntegers L).units) hb
      have hb2 : Commons.RingTheory.Henselian.adicCompletionMap Q q hqQ
          ((b⁻¹ : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) ∈
            (q.adicCompletionIntegers L) :=
        (Submonoid.mem_units_iff _ _).mp hbinv |>.1
      rw [Submonoid.mem_units_iff]
      exact ⟨(Commons.NumberTheory.NumberField.Completion.adicCompletionMap_mem_integers_iff
          Q q hqQ (b : Q.adicCompletion K)).mp hb1,
        (Commons.NumberTheory.NumberField.Completion.adicCompletionMap_mem_integers_iff
          Q q hqQ ((b⁻¹ : (Q.adicCompletion K)ˣ) : Q.adicCompletion K)).mp hb2⟩
    rw [Place.localUnits_ofFinite] at ⊢
    exact key a ha

/-- Transport of an idèle component along an equality of places. -/
lemma globalCFT_idele_component_transport {K : Type*} [Field K] [NumberField K] (x : 𝕀[K])
    {a b : Place K} (h : a = b) : x b = h ▸ x a := by
  cases h; rfl

theorem globalCFT_idele_smul_eq_self_iff {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (u : Place L → Place K) (hu : ∀ w : Place L, Place.LiesOver w (u w))
    (φ : 𝕀[K] →* 𝕀[L])
    (hφ : ∀ (x : 𝕀[K]) (w : Place L),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w))) (x : 𝕀[L]) :
    (∀ σ : L ≃ₐ[K] L, σ • x = x) ↔ x ∈ φ.range := by
  classical
  constructor
  · intro hx
    let w₀ : Place K → Place L :=
      fun v => Classical.choose (globalCFT_exists_placeOver (K := K) (L := L) v)
    have hw₀ : ∀ v : Place K, Place.LiesOver (w₀ v) v :=
      fun v => Classical.choose_spec (globalCFT_exists_placeOver (K := K) (L := L) v)
    have hfix : ∀ (σ : L ≃ₐ[K] L) (w : Place L),
        Units.map (Place.localRingEquiv σ w).toMonoidHom (x w) = x (σ • w) :=
      fun σ w => Galois.globalCFT_unitsMap_localRingEquiv_of_fixed x hx σ w
    have hloc : ∀ v : Place K, ∃ a : (Place.localField K v)ˣ,
        Place.localAlgebraMapUnits (w₀ v) v (hw₀ v) a = x (w₀ v) := by
      intro v
      refine globalCFT_localFixed_mem_range (hw₀ v) (x (w₀ v)) ?_
      intro σ hσ
      rw [hfix σ (w₀ v)]
      exact globalCFT_idele_component_transport x hσ.symm
    let yFun : (v : Place K) → (Place.localField K v)ˣ := fun v => Classical.choose (hloc v)
    have hyFun : ∀ v : Place K,
        Place.localAlgebraMapUnits (w₀ v) v (hw₀ v) (yFun v) = x (w₀ v) :=
      fun v => Classical.choose_spec (hloc v)
    have hbad : {w : Place L | x w ∉ Place.localUnits L w}.Finite :=
      (Filter.eventually_cofinite).mp x.2
    have hy_mem : ∀ᶠ v in Filter.cofinite, yFun v ∈ Place.localUnits K v := by
      rw [Filter.eventually_cofinite]
      refine Set.Finite.subset (hbad.image u) ?_
      rintro v hv
      refine ⟨w₀ v, ?_, ?_⟩
      · intro hxw
        exact hv (globalCFT_mem_localUnits_of_localAlgebraMapUnits (hw₀ v) (by
          rw [hyFun v]; exact hxw))
      · exact globalCFT_liesOver_unique (hu (w₀ v)) (hw₀ v)
    have hy_eq : ∀ (v : Place K) (w : Place L) (h : Place.LiesOver w v),
        Place.localAlgebraMapUnits w v h (yFun v) = x w := by
      intro v w h
      obtain ⟨σ, hσ⟩ := globalCFT_exists_smul_eq_of_liesOver (hw₀ v) h
      subst hσ
      have h1 := Galois.globalCFT_localRingEquiv_localAlgebraMapUnits σ (hw₀ v) h (yFun v)
      rw [hyFun v, hfix σ (w₀ v)] at h1
      exact h1.symm
    refine ⟨(⟨yFun, hy_mem⟩ : 𝕀[K]), Idele.ext fun w => ?_⟩
    rw [hφ]
    exact hy_eq (u w) w (hu w)
  · rintro ⟨y, rfl⟩ σ
    exact globalCFT_ideleInclusion_smul u hu φ hφ σ y

end NK.GlobalCFT.Inclusion
