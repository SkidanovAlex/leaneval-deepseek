import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.Work.SSGRoute.PT.e1a_beta_can
import Submission.Work.sha2_hasse.exists_norm_witness_infinitePlace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The *linked* archimedean seam

`Submission/Work/SSGRoute/E1aClean/NOTE_infLocalCriterion_frontier.md` records that the
archimedean comparison square of node `E1a` needs a seam `e : Ω →+* ℂ` intertwining the involution
`σ ∈ Gal(Ω/k)` with the *local* action of `τ = res k K σ` on `ℂ = K_w`, and that the *bare*
statement (`res k K σ = τ` only) is **false**: two reviews produced counterexamples (e.g.
`k = ℚ(√2)`, `K = ℚ(ζ₈)`, `σ` additionally sending `√3 ↦ -√3`), because `hle` does not tie `σ` to a
place of `Ω` above `w`.  The missing hypothesis is the **link**: `σ` is the conjugation of a
complex embedding `φ` of `Ω` extending `w.embedding`.

This file states the seam **with the link as a hypothesis** and proves it.  The arithmetic content
is entirely in the already-proved

* `Work.sha2_hasse.localAutHom_ringEquivComplex` — at a complex place, the local action of an
  element of the decomposition group *which acts by complex conjugation on the level* is complex
  conjugation under the identification `L_w ≃+* ℂ`;
* `Work.sha2_hasse.algEquivUnitsMap_ringEquivComplex` — the link descends to units.

The companion combinatorial input, i.e. that a linked `(σ, φ)` *exists* for every element `τ` of
the decomposition group (and how it is produced from a level / place), is recorded separately:
`Work.sha2_hasse.exists_involution_extension` and `Work.SSGRoute.glue_infinite_place` construct it
for the nontrivial `τ₀`, exposing the link internally in
`Work.SSGRoute.exists_involution_extension_omega_aux`.
-/

open NumberField

noncomputable section

namespace Work.SSGRoute.E1aClean

open SSGRoute.PTExt

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **The archimedean local action.**  The action of an element `τ` of the decomposition group of a
complex infinite place `w` on `ℂ = K_w`, transported along the ring isomorphism
`w.Completion ≃+* ℂ`. -/
noncomputable def localActionC (K : IntermediateField k Ω) [NumberField ↥K]
    (w : NumberField.InfinitePlace ↥K) (hw : w.IsComplex)
    (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w))) : ℂ ≃+* ℂ :=
  let e : w.Completion ≃+* ℂ := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  e.symm.trans ((NK.HassePrinciple.localAutHom (K := k) (L := ↥K)
      (NK.GlobalCFT.Place.ofInfinite w) τ).trans e)

/-- Computation rule of `localActionC`: it is the transport of `localAutHom` along
`ringEquivComplexOfIsComplex`. -/
theorem localActionC_apply (K : IntermediateField k Ω) [NumberField ↥K]
    (w : NumberField.InfinitePlace ↥K) (hw : w.IsComplex)
    (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w))) (u : ℂ) :
    localActionC K w hw τ u =
      NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
        (NK.HassePrinciple.localAutHom (K := k) (L := ↥K)
          (NK.GlobalCFT.Place.ofInfinite w) τ
          ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm u)) := rfl

/-- **The level form of the link.**  The place compatibility and the link (an intertwining of `σ`
with complex conjugation) force the *level* form of the link on `K`, which is the hypothesis that
`Work.sha2_hasse.localAutHom_ringEquivComplex` consumes. -/
theorem seamLevelConj (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] (w : NumberField.InfinitePlace ↥K)
    (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w)))
    (σ : Ω ≃ₐ[k] Ω) (hres : SSGRoute.res k K σ = (τ : ↥K ≃ₐ[k] ↥K))
    (φ : Ω →+* ℂ)
    (hφK : ∀ y : ↥K, φ (algebraMap ↥K Ω y) = NumberField.InfinitePlace.embedding w y)
    (hlink : ∀ x : Ω, φ (σ x) = starRingEnd ℂ (φ x)) :
    ∀ x : ↥K, NumberField.InfinitePlace.embedding w ((τ : ↥K ≃ₐ[k] ↥K) x) =
      starRingEnd ℂ (NumberField.InfinitePlace.embedding w x) := by
  intro x
  have h1 : ((τ : ↥K ≃ₐ[k] ↥K) x : Ω) = σ (algebraMap ↥K Ω x) := by
    have h : (SSGRoute.res k K σ) x = (τ : ↥K ≃ₐ[k] ↥K) x :=
      congrFun (congrArg DFunLike.coe hres) x
    rw [← h]
    exact AlgEquiv.restrictNormalHom_apply K σ x
  calc NumberField.InfinitePlace.embedding w ((τ : ↥K ≃ₐ[k] ↥K) x)
      = φ (((τ : ↥K ≃ₐ[k] ↥K) x : Ω)) := (hφK _).symm
    _ = φ (σ (algebraMap ↥K Ω x)) := by rw [h1]
    _ = starRingEnd ℂ (φ (algebraMap ↥K Ω x)) := hlink _
    _ = starRingEnd ℂ (NumberField.InfinitePlace.embedding w x) := by rw [hφK x]

/-- **The linked archimedean seam.**  Let `w` be a complex infinite place of `K`, `σ ∈ Gal(Ω/k)` an
involution whose restriction to `K` is `τ`, and `φ : Ω →+* ℂ` a complex embedding which
(i) extends the place embedding `w.embedding` of `K` (the "place compatibility") and
(ii) intertwines `σ` with complex conjugation (the "link").  Then `φ` intertwines `σ` with the
*local* action of `τ` on `ℂ = K_w`.

This is the seam the archimedean comparison square consumes: clause (ii) is exactly the hypothesis
whose absence makes the bare statement (`res k K σ = τ` only) false. -/
theorem linkedSeamAction (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] (w : NumberField.InfinitePlace ↥K) (hw : w.IsComplex)
    (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w)))
    (σ : Ω ≃ₐ[k] Ω) (hres : SSGRoute.res k K σ = (τ : ↥K ≃ₐ[k] ↥K))
    (φ : Ω →+* ℂ)
    (hφK : ∀ y : ↥K, φ (algebraMap ↥K Ω y) = NumberField.InfinitePlace.embedding w y)
    (hlink : ∀ x : Ω, φ (σ x) = starRingEnd ℂ (φ x)) :
    ∀ x : Ω, φ (σ x) = localActionC K w hw τ (φ x) := by
  have hconj := seamLevelConj K w τ σ hres φ hφK hlink
  intro x
  rw [hlink x, localActionC_apply,
    Work.sha2_hasse.localAutHom_ringEquivComplex (K := k) (L := ↥K) w hw τ hconj
      ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm (φ x)),
    RingEquiv.apply_symm_apply]

/-- **The unit-level form of the linked seam, with the local action.**  This is the exact shape in
which the seam enters the archimedean comparison square: pushing `Ωˣ` into `ℂˣ` along `φ` is
`⟨σ⟩`-equivariant, the `⟨σ⟩`-action on `Ωˣ` being the Galois action and the `⟨σ⟩`-action on `ℂˣ`
being the *local* action of `τ = res k K σ` (not complex conjugation itself, which is only its
`φ`-conjugate). -/
theorem linkedSeamUnitsMap (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] (w : NumberField.InfinitePlace ↥K) (hw : w.IsComplex)
    (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w)))
    (σ : Ω ≃ₐ[k] Ω) (hres : SSGRoute.res k K σ = (τ : ↥K ≃ₐ[k] ↥K))
    (φ : Ω →+* ℂ)
    (hφK : ∀ y : ↥K, φ (algebraMap ↥K Ω y) = NumberField.InfinitePlace.embedding w y)
    (hlink : ∀ x : Ω, φ (σ x) = starRingEnd ℂ (φ x)) (U : Ωˣ) :
    Units.map φ.toMonoidHom (Work.SSGRoute.algEquivUnitsMapΩ k Ω σ U) =
      Units.map (localActionC K w hw τ).toMonoidHom (Units.map φ.toMonoidHom U) := by
  apply Units.ext
  simp only [Units.coe_map, Work.SSGRoute.algEquivUnitsMapΩ_coe]
  exact linkedSeamAction K w hw τ σ hres φ hφK hlink (U : Ω)

/-- **Existence of the linked data (gap (ii) of the note).**  For a complex infinite place `w` of `K`
and a **nontrivial** element `τ` of its decomposition group there are an involution `σ ∈ Gal(Ω/k)`
with `res k K σ = τ` and a complex embedding `φ : Ω →+* ℂ` extending the place embedding
`w.embedding` and intertwining `σ` with complex conjugation — i.e. exactly the hypotheses of
`linkedSeamAction`.

The hypothesis `τ ≠ 1` is essential: the link forces `σ = id` when `τ = 1` (see the note). -/
theorem linkedInvolution_exists (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] (w : NumberField.InfinitePlace ↥K)
    (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w))) (hτ : τ ≠ 1) :
    ∃ (σ : Ω ≃ₐ[k] Ω) (φ : Ω →+* ℂ),
      σ ^ 2 = 1 ∧ SSGRoute.res k K σ = (τ : ↥K ≃ₐ[k] ↥K) ∧
      (∀ y : ↥K, φ (algebraMap ↥K Ω y) = NumberField.InfinitePlace.embedding w y) ∧
      (∀ x : Ω, φ (σ x) = starRingEnd ℂ (φ x)) := by
  -- `τ ≠ 1` forces `w` to be ramified over `k`
  have hmem : (τ : ↥K ≃ₐ[k] ↥K) ∈ MulAction.stabilizer (↥K ≃ₐ[k] ↥K) w :=
    MulAction.mem_stabilizer_iff.mpr (by
      have h := MulAction.mem_stabilizer_iff.mp τ.2
      rwa [NK.GlobalCFT.Place.smul_ofInfinite, NK.GlobalCFT.Place.ofInfinite_inj] at h)
  have hram : NumberField.InfinitePlace.IsRamified k w :=
    (NumberField.InfinitePlace.isUnramified_or_isRamified k w).resolve_left (fun hunr => by
      refine hτ (Subtype.ext ?_)
      have hbot := NumberField.InfinitePlace.IsUnramified.stabilizer_eq_bot (k := k) hunr
      rw [hbot] at hmem
      simpa using hmem)
  -- the nontrivial element of the stabiliser is the conjugation at `w`, so `τ` is
  obtain ⟨σ₀, hσ₀⟩ := NumberField.InfinitePlace.exists_isConj_of_isRamified (k := k)
    (φ := w.embedding) (by rwa [NumberField.InfinitePlace.mk_embedding])
  have hstab : (MulAction.stabilizer (↥K ≃ₐ[k] ↥K) w : Set (↥K ≃ₐ[k] ↥K)) = {1, σ₀} := by
    rw [← NumberField.InfinitePlace.mk_embedding w]
    exact hσ₀.coe_stabilizer_mk
  have hτσ₀ : (τ : ↥K ≃ₐ[k] ↥K) = σ₀ := by
    have h2 : (τ : ↥K ≃ₐ[k] ↥K) ∈ ({1, σ₀} : Set (↥K ≃ₐ[k] ↥K)) := by
      rw [← hstab]; exact hmem
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h2
    rcases h2 with h | h
    · exact absurd (Subtype.ext h) hτ
    · exact h
  have hconjτ : NumberField.ComplexEmbedding.IsConj (k := k) w.embedding
      (τ : ↥K ≃ₐ[k] ↥K) := by rw [hτσ₀]; exact hσ₀
  -- the lift construction
  let φ : Ω →+* ℂ := NumberField.ComplexEmbedding.lift Ω w.embedding
  have hφc : ∀ y : ↥K, φ (algebraMap ↥K Ω y) = NumberField.InfinitePlace.embedding w y :=
    fun y => NumberField.ComplexEmbedding.lift_algebraMap_apply Ω w.embedding y
  have hφc' : ∀ y : ↥K, φ (y : Ω) = NumberField.InfinitePlace.embedding w y := by
    intro y
    rw [← IntermediateField.algebraMap_apply K y]
    exact hφc y
  have hreal : NumberField.ComplexEmbedding.IsReal (φ.comp (algebraMap k Ω)) := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    rw [← NumberField.ComplexEmbedding.conjugate_comp]
    ext a
    simp only [RingHom.comp_apply]
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    have h1 : φ (algebraMap k Ω a) = w.embedding (algebraMap k ↥K a) := by
      rw [IsScalarTower.algebraMap_apply k ↥K Ω]
      exact hφc _
    rw [h1]
    have hc := hconjτ.eq (algebraMap k ↥K a)
    rw [AlgEquiv.commutes] at hc
    exact hc.symm
  obtain ⟨σ₁, hσ₁⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (K := Ω) (k := k)
    φ (NumberField.ComplexEmbedding.conjugate φ) (by
      rw [NumberField.ComplexEmbedding.conjugate_comp]
      exact hreal.symm)
  have hσ : φ.comp (↑(σ₁.symm) : Ω →+* Ω) = NumberField.ComplexEmbedding.conjugate φ := hσ₁
  have hIsConj : NumberField.ComplexEmbedding.IsConj (k := k) (K := Ω) φ σ₁.symm := hσ.symm
  refine ⟨σ₁.symm, φ, ?_, ?_, fun y => hφc y, fun x => ?_⟩
  · -- `σ₁.symm` is an involution
    rw [pow_two]
    ext x
    rw [AlgEquiv.mul_apply, AlgEquiv.one_apply]
    exact NumberField.ComplexEmbedding.isConj_apply_apply hIsConj x
  · -- it restricts to `τ`
    ext x
    apply φ.injective
    rw [AlgEquiv.restrictNormalHom_apply]
    have h1 : φ ((σ₁.symm) ((x : ↥K) : Ω)) = starRingEnd ℂ (φ ((x : ↥K) : Ω)) :=
      RingHom.congr_fun hσ ((x : ↥K) : Ω)
    have h2 : φ (((τ : ↥K ≃ₐ[k] ↥K) x : ↥K) : Ω) = starRingEnd ℂ (φ ((x : ↥K) : Ω)) := by
      rw [hφc' ((τ : ↥K ≃ₐ[k] ↥K) x), hφc' x]
      exact hconjτ.eq x
    rw [h2]
    exact h1
  · -- the link
    exact (NumberField.ComplexEmbedding.IsConj.eq hIsConj x).trans
      (starRingEnd_apply (φ x)).symm

/-- **Under the link the archimedean local action *is* complex conjugation.**  Given the level form
of the link, the transported local action of `τ` equals `starRingEnd ℂ` as a ring equivalence — this
is what identifies the local Galois group with `Gal(ℂ/ℝ)` and the coefficient module `K_wˣ` with
`ℂˣ`. -/
theorem localActionC_eq_conj (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] (w : NumberField.InfinitePlace ↥K) (hw : w.IsComplex)
    (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w)))
    (hconj : ∀ x : ↥K, NumberField.InfinitePlace.embedding w ((τ : ↥K ≃ₐ[k] ↥K) x) =
      starRingEnd ℂ (NumberField.InfinitePlace.embedding w x)) :
    localActionC K w hw τ = starRingEnd ℂ := by
  ext y
  change localActionC K w hw τ y = starRingEnd ℂ y
  rw [localActionC_apply,
    Work.sha2_hasse.localAutHom_ringEquivComplex (K := k) (L := ↥K) w hw τ hconj
      ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm y),
    RingEquiv.apply_symm_apply]

/-- **Under the linked data, the local action of a nontrivial `τ` is complex conjugation.**  This is
the form in which the identification of the *local* Galois group at `w` — the image of `D_w` under
`τ ↦ localActionC τ` — with `Gal(ℂ/ℝ) = {1, starRingEnd ℂ}`, and hence of the local units `K_wˣ`
with `ℂˣ`, is consumed. -/
theorem linkedLocalAction_eq_conj (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (w : NumberField.InfinitePlace ↥K) (hw : w.IsComplex)
    (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w)))
    (σ : Ω ≃ₐ[k] Ω) (hres : SSGRoute.res k K σ = (τ : ↥K ≃ₐ[k] ↥K))
    (φ : Ω →+* ℂ)
    (hφK : ∀ y : ↥K, φ (algebraMap ↥K Ω y) = NumberField.InfinitePlace.embedding w y)
    (hlink : ∀ x : Ω, φ (σ x) = starRingEnd ℂ (φ x)) :
    localActionC K w hw τ = starRingEnd ℂ :=
  localActionC_eq_conj K w hw τ (seamLevelConj K w τ σ hres φ hφK hlink)

end Work.SSGRoute.E1aClean
