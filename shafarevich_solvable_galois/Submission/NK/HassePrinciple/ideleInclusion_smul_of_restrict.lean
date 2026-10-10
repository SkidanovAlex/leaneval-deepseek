import Mathlib.Topology.Connected.Separation
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Submission.NK.GlobalCFT.GaloisIdelesAction
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The idèle inclusion is equivariant for a normal intermediate field

Let `K ⊆ F ⊆ L` be number fields with `F/K` normal, `L/F` finite, and let
`u : Place L → Place F` be the restriction of places (`hu : w` lies over `u w`).  For the monoid
homomorphism `φ : 𝕀[F] →* 𝕀[L]` whose `w`-component is the canonical local embedding
`F_{u w}ˣ →* L_wˣ`, and for `τ : Gal(L/K)` with restriction `A = restrictNormalHom F τ` to the
normal subfield `F`, the image is equivariant:

`τ • φ x = φ (A • x)`,   `x : 𝕀[F]`.

Unlike the same-base statement (`NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_smul`, where
`σ` acts trivially on the base), the automorphism `τ` does *not* fix `F` pointwise here; it acts
on the places of `F` through its restriction `A`, and the place `u w` below `w` is moved to
`A • u w` below `τ • w`.  The local input is the twisted `Gal(L/K)`-equivariance of the local
algebra maps, proved here by the density arguments in the archimedean and the nonarchimedean
case.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped NumberField NumberField.LiesOver
open NumberField IsDedekindDomain

namespace NK.HassePrinciple

noncomputable section

/-! ### Elementary transport lemmas -/

/-- The local algebra map is insensitive to the place of the base, up to the identification of
the local fields given by the equality of places. -/
private lemma aux_localAlgebraMapUnits_cast {K₀ L₀ : Type*} [Field K₀] [NumberField K₀]
    [Field L₀] [NumberField L₀] [Algebra K₀ L₀] (w₀ : NK.GlobalCFT.Place L₀)
    {a b : NK.GlobalCFT.Place K₀} (h : a = b)
    (ha : NK.GlobalCFT.Place.LiesOver w₀ a) (hb : NK.GlobalCFT.Place.LiesOver w₀ b)
    (y : (NK.GlobalCFT.Place.localField K₀ a)ˣ) :
    NK.GlobalCFT.Place.localAlgebraMapUnits w₀ a ha y =
      NK.GlobalCFT.Place.localAlgebraMapUnits w₀ b hb (h ▸ y) := by
  cases h
  rfl

/-- The `apd` identity: transporting the value of a dependent function along an equality of the
arguments gives the value at the other argument. -/
private lemma aux_eqRec_apply {α : Type*} {β : α → Type*} (f : (i : α) → β i) {a b : α}
    (h : a = b) : h ▸ f a = f b := by
  cases h
  rfl

variable {K F L : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Field L]
  [NumberField L] [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]

/-! ### The twisted "lies over" relation -/

/-- The archimedean case of the twisted `LiesOver`: `w | v` implies `τ • w | A • v`, where the
place of `F` is moved by the restriction `A` of `τ`. -/
private lemma aux_infiniteLiesOver {τ : L ≃ₐ[K] L} {A : F ≃ₐ[K] F}
    (hA : ∀ y : F, algebraMap F L (A y) = τ (algebraMap F L y))
    {w : NumberField.InfinitePlace L} {v : NumberField.InfinitePlace F}
    (h : w.LiesOver v) : (τ • w).LiesOver (A • v) := by
  have key : ∀ (w : NumberField.InfinitePlace L) (v : NumberField.InfinitePlace F),
      w.LiesOver v ↔ w.comap (algebraMap F L) = v := by
    intro w v
    refine ⟨fun _ => NumberField.InfinitePlace.LiesOver.comap_eq w v, fun h => ?_⟩
    refine ⟨?_⟩
    have hh : (w.comap (algebraMap F L)).1 = v.1 := congrArg Subtype.val h
    rw [← hh]
    rfl
  have hv : w.comap (algebraMap F L) = v := (key w v).mp h
  refine (key (τ • w) (A • v)).mpr ?_
  have hcomp : (τ.symm).toRingHom.comp (algebraMap F L) =
      (algebraMap F L).comp (A.symm).toRingHom := by
    ext y
    rw [RingHom.comp_apply, RingHom.comp_apply]
    have h := hA (A.symm y)
    rw [AlgEquiv.apply_symm_apply] at h
    rw [h]
    exact AlgEquiv.symm_apply_apply τ _
  calc (τ • w).comap (algebraMap F L)
      = w.comap ((τ.symm).toRingHom.comp (algebraMap F L)) := rfl
    _ = w.comap ((algebraMap F L).comp (A.symm).toRingHom) := by rw [hcomp]
    _ = (w.comap (algebraMap F L)).comap (A.symm).toRingHom := rfl
    _ = v.comap (A.symm).toRingHom := by rw [hv]
    _ = A • v := rfl

/-- The nonarchimedean case of the twisted `LiesOver`: `q | Q` implies `τ q | A Q`. -/
private lemma aux_finiteLiesOver {τ : L ≃ₐ[K] L} {A : F ≃ₐ[K] F}
    (hA : ∀ y : F, algebraMap F L (A y) = τ (algebraMap F L y))
    {q : HeightOneSpectrum (𝓞 L)} {Q : HeightOneSpectrum (𝓞 F)}
    (h : q.asIdeal.LiesOver Q.asIdeal) :
    (NK.GlobalCFT.Place.smulHeightOneSpectrum τ q).asIdeal.LiesOver
      (NK.GlobalCFT.Place.smulHeightOneSpectrum A Q).asIdeal := by
  rw [NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal,
    NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal]
  have hsq : ∀ z : 𝓞 F,
      NK.GlobalCFT.Place.ringOfIntegersEquiv τ
          (algebraMap (𝓞 F) (𝓞 L) z) =
        algebraMap (𝓞 F) (𝓞 L) (NK.GlobalCFT.Place.ringOfIntegersEquiv A z) := by
    intro z
    apply NumberField.RingOfIntegers.ext
    change τ ((algebraMap F L) (z : F)) = (algebraMap F L) (A (z : F))
    exact (hA (z : F)).symm
  refine ⟨?_⟩
  have hover : Q.asIdeal = Ideal.comap (algebraMap (𝓞 F) (𝓞 L)) q.asIdeal :=
    Ideal.LiesOver.over (p := Q.asIdeal) (P := q.asIdeal)
  rw [hover]
  refine Ideal.ext fun x => ?_
  constructor
  · intro hx
    obtain ⟨z, hz, hzx⟩ :=
      (Ideal.mem_map_iff_of_surjective (NK.GlobalCFT.Place.ringOfIntegersEquiv A)
        (RingEquiv.bijective _).2).mp hx
    have hzq : algebraMap (𝓞 F) (𝓞 L) z ∈ q.asIdeal := Ideal.mem_comap.mp hz
    refine Ideal.mem_comap.mpr ?_
    refine (Ideal.mem_map_iff_of_surjective (NK.GlobalCFT.Place.ringOfIntegersEquiv τ)
      (RingEquiv.bijective _).2).mpr ⟨algebraMap (𝓞 F) (𝓞 L) z, hzq, ?_⟩
    rw [← hzx]
    exact hsq z
  · intro hx
    have hxq : algebraMap (𝓞 F) (𝓞 L) x ∈ Ideal.map (NK.GlobalCFT.Place.ringOfIntegersEquiv τ)
        q.asIdeal := Ideal.mem_comap.mp hx
    obtain ⟨y, hy, hyx⟩ :=
      (Ideal.mem_map_iff_of_surjective (NK.GlobalCFT.Place.ringOfIntegersEquiv τ)
        (RingEquiv.bijective _).2).mp hxq
    refine (Ideal.mem_map_iff_of_surjective (NK.GlobalCFT.Place.ringOfIntegersEquiv A)
      (RingEquiv.bijective _).2).mpr
      ⟨(NK.GlobalCFT.Place.ringOfIntegersEquiv A).symm x, ?_, ?_⟩
    · refine Ideal.mem_comap.mpr ?_
      have h1 : algebraMap (𝓞 F) (𝓞 L)
          ((NK.GlobalCFT.Place.ringOfIntegersEquiv A).symm x) = y := by
        apply (NK.GlobalCFT.Place.ringOfIntegersEquiv τ).injective
        rw [hsq ((NK.GlobalCFT.Place.ringOfIntegersEquiv A).symm x), hyx,
          RingEquiv.apply_symm_apply]
      rw [h1]
      exact hy
    · exact (NK.GlobalCFT.Place.ringOfIntegersEquiv A).apply_symm_apply x

/-- **The twisted `LiesOver`.**  If the place `w` of `L` lies over the place `v` of `F` and
`A : F ≃ₐ[K] F` is the restriction of `τ : L ≃ₐ[K] L`, then `τ • w` lies over `A • v`. -/
private theorem aux_liesOver_smul_of_restrict (τ : L ≃ₐ[K] L) (A : F ≃ₐ[K] F)
    (hA : ∀ y : F, algebraMap F L (A y) = τ (algebraMap F L y))
    {w : NK.GlobalCFT.Place L} {v : NK.GlobalCFT.Place F}
    (h : NK.GlobalCFT.Place.LiesOver w v) :
    NK.GlobalCFT.Place.LiesOver (τ • w) (A • v) := by
  rcases w with w | q
  · rcases v with v | Q
    · exact NK.GlobalCFT.Place.liesOver_ofInfinite
        (aux_infiniteLiesOver hA
          ((NK.GlobalCFT.Galois.globalCFT_liesOver_ofInfinite_iff w v).mp h))
    · rcases h with ⟨w', v', h1, h2, _⟩ | ⟨q', Q', h1, _, _⟩
      · exact absurd h2 Sum.inr_ne_inl
      · exact absurd h1 Sum.inl_ne_inr
  · rcases v with v | Q
    · rcases h with ⟨w', v', h1, _, _⟩ | ⟨q', Q', h1, h2, _⟩
      · exact absurd h1 Sum.inr_ne_inl
      · exact absurd h2 Sum.inl_ne_inr
    · exact NK.GlobalCFT.Place.liesOver_ofFinite
        (aux_finiteLiesOver hA
          ((NK.GlobalCFT.Galois.globalCFT_liesOver_ofFinite_iff q Q).mp h))

/-! ### The local equivariance in the tower `K ⊆ F ⊆ L` -/

/-- The archimedean local isomorphism, evaluated on the image of the `WithAbs`-copy of `L`. -/
private lemma aux_infiniteCongrEquiv_coe (σ : L ≃ₐ[K] L) (w : NumberField.InfinitePlace L)
    (y : WithAbs (w.1)) :
    NK.GlobalCFT.Galois.globalCFT_infiniteCongrEquiv σ w (y : w.Completion) =
      (NK.GlobalCFT.Galois.globalCFT_withAbsCongrEquiv σ w y : (σ • w).Completion) := by
  rw [NK.GlobalCFT.Galois.globalCFT_infiniteCongrEquiv, RingEquiv.trans_apply,
    RingEquiv.trans_apply, NumberField.InfinitePlace.Completion.equiv_apply,
    UniformSpace.Completion.mapRingEquiv_apply]
  rw [show ((y : w.Completion).toCompletion) = (y : w.1.Completion) from rfl]
  rw [UniformSpace.Completion.map_coe
    (NK.GlobalCFT.Galois.globalCFT_isometry_withAbsCongrEquiv σ w).uniformContinuous]
  rfl

/-- At the level of the `WithAbs`-copies of the fields, the archimedean isomorphism attached to
`τ` intertwines the algebra maps `F → L` and `F → L` twisted by the restriction `A` of `τ`. -/
private lemma aux_withAbsCongrEquiv_algebraMap {τ : L ≃ₐ[K] L} {A : F ≃ₐ[K] F}
    (hA : ∀ y : F, algebraMap F L (A y) = τ (algebraMap F L y))
    (v : NumberField.InfinitePlace F) (w : NumberField.InfinitePlace L)
    [hv : w.LiesOver v] [hv' : (τ • w).LiesOver (A • v)] (a : WithAbs (v.1)) :
    NK.GlobalCFT.Galois.globalCFT_withAbsCongrEquiv τ w
        (algebraMap (WithAbs (v.1)) (WithAbs (w.1)) a) =
      algebraMap (WithAbs ((A • v).1)) (WithAbs ((τ • w).1))
        (NK.GlobalCFT.Galois.globalCFT_withAbsCongrEquiv A v a) := by
  rw [NK.GlobalCFT.Galois.globalCFT_withAbsCongrEquiv, WithAbs.congr_apply,
    WithAbs.ofAbs_algebraMap, WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply,
    NK.GlobalCFT.Galois.globalCFT_withAbsCongrEquiv, WithAbs.congr_apply, WithAbs.ofAbs_toAbs]
  congr 1
  rw [WithAbs.ofAbs_toAbs]
  exact (hA a.ofAbs).symm

/-- The archimedean case of the local equivariance in the tower: the local isomorphism
`L_w ≃+* L_{τ w}` intertwines the completion maps `F_v →+* L_w` and `F_{A v} →+* L_{τ w}`. -/
private lemma aux_infiniteCongrEquiv_completionMap_twist
    {τ : L ≃ₐ[K] L} {A : F ≃ₐ[K] F}
    (hA : ∀ y : F, algebraMap F L (A y) = τ (algebraMap F L y))
    {v : NumberField.InfinitePlace F} {w : NumberField.InfinitePlace L}
    (hv : w.LiesOver v) (hv' : (τ • w).LiesOver (A • v)) (x : v.Completion) :
    NK.GlobalCFT.Galois.globalCFT_infiniteCongrEquiv τ w
        (NumberField.LiesOver.completionMap (v := v) (w := w) x) =
      NumberField.LiesOver.completionMap (v := A • v) (w := τ • w)
        (NK.GlobalCFT.Galois.globalCFT_infiniteCongrEquiv A v x) := by
  haveI := hv
  haveI := hv'
  induction x using NumberField.InfinitePlace.Completion.induction_on
  · exact isClosed_eq
      ((NK.GlobalCFT.Galois.continuous_localRingEquiv τ
          (NK.GlobalCFT.Place.ofInfinite w)).comp
        (NumberField.LiesOver.continuous_completionMap (v := v) (w := w)))
      ((NumberField.LiesOver.continuous_completionMap (v := A • v) (w := τ • w)).comp
        (NK.GlobalCFT.Galois.continuous_localRingEquiv A
          (NK.GlobalCFT.Place.ofInfinite v)))
  · rename_i y
    rw [NumberField.LiesOver.completionMap_coe (v := v) (w := w),
      aux_infiniteCongrEquiv_coe τ w (algebraMap (WithAbs (v.1)) (WithAbs (w.1)) y),
      aux_withAbsCongrEquiv_algebraMap hA v w y,
      aux_infiniteCongrEquiv_coe A v y,
      NumberField.LiesOver.completionMap_coe (v := A • v) (w := τ • w)]

/-- The nonarchimedean completion map on the dense image of the base field. -/
private lemma aux_adicCompletionMap_coe {q : HeightOneSpectrum (𝓞 L)} {Q : HeightOneSpectrum (𝓞 F)}
    (h : q.asIdeal.LiesOver Q.asIdeal) (y : F) :
    Commons.RingTheory.Henselian.adicCompletionMap Q q h (algebraMap F (Q.adicCompletion F) y) =
      algebraMap L (q.adicCompletion L) (algebraMap F L y) := by
  rw [NK.GlobalCFT.Galois.globalCFT_algebraMap_eq_coe Q y,
    Commons.RingTheory.Henselian.adicCompletionMap_apply Q q h y,
    NK.GlobalCFT.Galois.globalCFT_algebraMap_eq_coe q (algebraMap F L y)]

/-- The adic local isomorphism on the image of the top field. -/
private lemma aux_adicCongrEquiv_algebraMap (σ : L ≃ₐ[K] L) (q : HeightOneSpectrum (𝓞 L))
    (x : L) :
    NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv σ q (algebraMap L (q.adicCompletion L) x) =
      algebraMap L ((NK.GlobalCFT.Place.smulHeightOneSpectrum σ q).adicCompletion L) (σ x) :=
  NK.GlobalCFT.Place.localRingEquiv_algebraMap σ (NK.GlobalCFT.Place.ofFinite q) x

/-- The nonarchimedean case of the local equivariance in the tower: the local isomorphism
`L_q ≃+* L_{τ q}` intertwines the adic completion maps `F_Q →+* L_q` and `F_{A Q} →+* L_{τ q}`. -/
private lemma aux_adicCongrEquiv_adicCompletionMap_twist
    {τ : L ≃ₐ[K] L} {A : F ≃ₐ[K] F}
    (hA : ∀ y : F, algebraMap F L (A y) = τ (algebraMap F L y))
    {q : HeightOneSpectrum (𝓞 L)} {Q : HeightOneSpectrum (𝓞 F)}
    (h : q.asIdeal.LiesOver Q.asIdeal)
    (h' : (NK.GlobalCFT.Place.smulHeightOneSpectrum τ q).asIdeal.LiesOver
      (NK.GlobalCFT.Place.smulHeightOneSpectrum A Q).asIdeal)
    (x : Q.adicCompletion F) :
    NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv τ q
        (Commons.RingTheory.Henselian.adicCompletionMap Q q h x) =
      Commons.RingTheory.Henselian.adicCompletionMap
        (NK.GlobalCFT.Place.smulHeightOneSpectrum A Q)
        (NK.GlobalCFT.Place.smulHeightOneSpectrum τ q) h'
        (NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv A Q x) := by
  haveI := h
  haveI := h'
  have key : ∀ y : F,
      NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv τ q
          (Commons.RingTheory.Henselian.adicCompletionMap Q q h
            (algebraMap F (Q.adicCompletion F) y)) =
        Commons.RingTheory.Henselian.adicCompletionMap
          (NK.GlobalCFT.Place.smulHeightOneSpectrum A Q)
          (NK.GlobalCFT.Place.smulHeightOneSpectrum τ q) h'
          (NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv A Q
            (algebraMap F (Q.adicCompletion F) y)) := by
    intro y
    rw [aux_adicCompletionMap_coe h y,
      aux_adicCongrEquiv_algebraMap τ q (algebraMap F L y),
      aux_adicCongrEquiv_algebraMap A Q y,
      aux_adicCompletionMap_coe h' (A y), hA y]
  have hfun := DenseRange.equalizer
    (f := algebraMap F (Q.adicCompletion F))
    (g := fun z => NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv τ q
      (Commons.RingTheory.Henselian.adicCompletionMap Q q h z))
    (h := fun z => Commons.RingTheory.Henselian.adicCompletionMap
      (NK.GlobalCFT.Place.smulHeightOneSpectrum A Q)
      (NK.GlobalCFT.Place.smulHeightOneSpectrum τ q) h'
      (NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv A Q z))
    (NK.GlobalCFT.Galois.denseRange_algebraMap_localField (v := NK.GlobalCFT.Place.ofFinite Q))
    ((NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv_continuous τ q).comp
      (Commons.RingTheory.Henselian.adicCompletionMap_continuous Q q h))
    ((Commons.RingTheory.Henselian.adicCompletionMap_continuous _ _ h').comp
      (NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv_continuous A Q))
    (by funext y; exact key y)
  exact congrFun hfun x

/-- The units form of the local equivariance in the tower: the canonical local isomorphism
`L_w ≃+* L_{τ w}` intertwines the local algebra maps `F_vˣ →* L_wˣ` and `F_{A v}ˣ →* L_{τ w}ˣ`. -/
private theorem aux_forward
    (τ : L ≃ₐ[K] L) (A : F ≃ₐ[K] F)
    (hA : ∀ y : F, algebraMap F L (A y) = τ (algebraMap F L y))
    {w : NK.GlobalCFT.Place L} {v : NK.GlobalCFT.Place F}
    (h : NK.GlobalCFT.Place.LiesOver w v)
    (h' : NK.GlobalCFT.Place.LiesOver (τ • w) (A • v))
    (a : (NK.GlobalCFT.Place.localField F v)ˣ) :
    Units.map (NK.GlobalCFT.Place.localRingEquiv τ w).toMonoidHom
        (NK.GlobalCFT.Place.localAlgebraMapUnits w v h a) =
      NK.GlobalCFT.Place.localAlgebraMapUnits (τ • w) (A • v) h'
        (Units.map (NK.GlobalCFT.Place.localRingEquiv A v).toMonoidHom a) := by
  rcases w with w | q
  · rcases v with v | Q
    · simp only [NK.GlobalCFT.Place.smul_ofInfinite] at h' ⊢
      haveI : w.LiesOver v :=
        (NK.GlobalCFT.Galois.globalCFT_liesOver_ofInfinite_iff w v).mp h
      haveI : (τ • w).LiesOver (A • v) :=
        (NK.GlobalCFT.Galois.globalCFT_liesOver_ofInfinite_iff _ _).mp h'
      simp only [NK.GlobalCFT.Place.localAlgebraMapUnits, NK.GlobalCFT.Place.localRingEquiv]
      rw [dif_pos (show w.LiesOver v from inferInstance),
        dif_pos (show (τ • w).LiesOver (A • v) from inferInstance)]
      apply Units.ext
      simp only [Units.coe_map]
      exact aux_infiniteCongrEquiv_completionMap_twist hA _ _ (a : v.Completion)
    · rcases h with ⟨w', v', h1, h2, _⟩ | ⟨q', Q', h1, _, _⟩
      · exact absurd h2 Sum.inr_ne_inl
      · exact absurd h1 Sum.inl_ne_inr
  · rcases v with v | Q
    · rcases h with ⟨w', v', h1, _, _⟩ | ⟨q', Q', h1, h2, _⟩
      · exact absurd h1 Sum.inr_ne_inl
      · exact absurd h2 Sum.inl_ne_inr
    · simp only [NK.GlobalCFT.Place.smul_ofFinite] at h' ⊢
      haveI : q.asIdeal.LiesOver Q.asIdeal :=
        (NK.GlobalCFT.Galois.globalCFT_liesOver_ofFinite_iff q Q).mp h
      haveI : (NK.GlobalCFT.Place.smulHeightOneSpectrum τ q).asIdeal.LiesOver
          (NK.GlobalCFT.Place.smulHeightOneSpectrum A Q).asIdeal :=
        (NK.GlobalCFT.Galois.globalCFT_liesOver_ofFinite_iff _ _).mp h'
      simp only [NK.GlobalCFT.Place.localAlgebraMapUnits, NK.GlobalCFT.Place.localRingEquiv]
      rw [dif_pos (show q.asIdeal.LiesOver Q.asIdeal from inferInstance),
        dif_pos (show (NK.GlobalCFT.Place.smulHeightOneSpectrum τ q).asIdeal.LiesOver
          (NK.GlobalCFT.Place.smulHeightOneSpectrum A Q).asIdeal from inferInstance)]
      apply Units.ext
      simp only [Units.coe_map]
      exact aux_adicCongrEquiv_adicCompletionMap_twist hA _ _ (a : Q.adicCompletion F)

/-- The inverse form of the local equivariance: the inverse local isomorphism sends the local
algebra map at `τ • w` back to the one at `w`. -/
private lemma aux_symm {τ : L ≃ₐ[K] L} {A : F ≃ₐ[K] F}
    (hA : ∀ y : F, algebraMap F L (A y) = τ (algebraMap F L y))
    {w : NK.GlobalCFT.Place L} {v : NK.GlobalCFT.Place F}
    (h : NK.GlobalCFT.Place.LiesOver w v)
    (h' : NK.GlobalCFT.Place.LiesOver (τ • w) (A • v))
    (a : (NK.GlobalCFT.Place.localField F (A • v))ˣ) :
    Units.map (NK.GlobalCFT.Place.localRingEquiv τ w).symm.toMonoidHom
        (NK.GlobalCFT.Place.localAlgebraMapUnits (τ • w) (A • v) h' a) =
      NK.GlobalCFT.Place.localAlgebraMapUnits w v h
        (Units.map (NK.GlobalCFT.Place.localRingEquiv A v).symm.toMonoidHom a) := by
  have key : ∀ u : (NK.GlobalCFT.Place.localField F (A • v))ˣ,
      Units.map (NK.GlobalCFT.Place.localRingEquiv A v).toMonoidHom
        (Units.map (NK.GlobalCFT.Place.localRingEquiv A v).symm.toMonoidHom u) = u := by
    intro u
    apply Units.ext
    simp only [Units.coe_map]
    exact RingEquiv.apply_symm_apply (NK.GlobalCFT.Place.localRingEquiv A v) _
  have hF := aux_forward τ A hA h h'
    (Units.map (NK.GlobalCFT.Place.localRingEquiv A v).symm.toMonoidHom a)
  rw [key a] at hF
  rw [← hF]
  apply Units.ext
  simp only [Units.coe_map]
  exact RingEquiv.symm_apply_apply (NK.GlobalCFT.Place.localRingEquiv τ w) _

end

/-! ### The equivariance of the idèle inclusion -/

/-- **Equivariance of the idèle inclusion for a normal intermediate field.**  Let `K ⊆ F ⊆ L`
be number fields with `F/K` normal, let `u : Place L → Place F` be the restriction of places and
let `φ : 𝕀[F] →* 𝕀[L]` be the inclusion whose `w`-component is the canonical local embedding.
Then for `τ : Gal(L/K)` and `x : 𝕀[F]`, with `A = restrictNormalHom F τ` the restriction of `τ`
to `F`, one has `τ • φ x = φ (A • x)`. -/
theorem ideleInclusion_smul_of_restrict {K F L : Type*} [Field K] [NumberField K] [Field F]
    [NumberField F] [Field L] [NumberField L] [Algebra K F] [Algebra F L] [Algebra K L]
    [IsScalarTower K F L] [Normal K F] [FiniteDimensional F L]
    (u : NK.GlobalCFT.Place L → NK.GlobalCFT.Place F)
    (hu : ∀ w : NK.GlobalCFT.Place L, NK.GlobalCFT.Place.LiesOver w (u w))
    (φ : NK.GlobalCFT.Idele F →* NK.GlobalCFT.Idele L)
    (hφ : ∀ (x : NK.GlobalCFT.Idele F) (w : NK.GlobalCFT.Place L),
      φ x w = NK.GlobalCFT.Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
    (τ : L ≃ₐ[K] L) (x : NK.GlobalCFT.Idele F) :
    τ • φ x = φ ((AlgEquiv.restrictNormalHom F τ) • x) := by
  set A : F ≃ₐ[K] F := AlgEquiv.restrictNormalHom F τ with hAdef
  have hA : ∀ y : F, algebraMap F L (A y) = τ (algebraMap F L y) :=
    fun y => AlgEquiv.restrictNormal_commutes (χ := τ) (E := F) y
  have hAinv : ∀ y : F, algebraMap F L (A⁻¹ y) = τ⁻¹ (algebraMap F L y) := by
    intro y
    have h := hA (A⁻¹ y)
    rw [show A (A⁻¹ y) = y from AlgEquiv.apply_symm_apply A y] at h
    rw [h]
    simp
  apply NK.GlobalCFT.Idele.ext
  intro w
  rw [NK.GlobalCFT.Idele.smul_apply τ (φ x) w, hφ, hφ,
    NK.GlobalCFT.Idele.smul_apply A x (u w)]
  -- the place of `F` below `τ⁻¹ • w` is `A⁻¹ • u w`
  have hsw : τ • (τ⁻¹ • w) = w := by rw [← mul_smul, mul_inv_cancel, one_smul]
  have h1 : NK.GlobalCFT.Place.LiesOver (τ • (τ⁻¹ • w)) (A • u (τ⁻¹ • w)) :=
    aux_liesOver_smul_of_restrict τ A hA (hu (τ⁻¹ • w))
  rw [hsw] at h1
  have huw : A • u (τ⁻¹ • w) = u w :=
    NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique h1 (hu w)
  have huw2 : u (τ⁻¹ • w) = A⁻¹ • u w := by
    rw [← inv_smul_smul A (u (τ⁻¹ • w)), huw]
  have hb : NK.GlobalCFT.Place.LiesOver (τ⁻¹ • w) (A⁻¹ • u w) := huw2 ▸ hu (τ⁻¹ • w)
  -- rewrite the component at `τ⁻¹ • w` in terms of the place `A⁻¹ • u w`
  have hcast : NK.GlobalCFT.Place.localAlgebraMapUnits (τ⁻¹ • w) (u (τ⁻¹ • w))
        (hu (τ⁻¹ • w)) (x (u (τ⁻¹ • w))) =
      NK.GlobalCFT.Place.localAlgebraMapUnits (τ⁻¹ • w) (A⁻¹ • u w) hb (x (A⁻¹ • u w)) := by
    rw [aux_localAlgebraMapUnits_cast (τ⁻¹ • w) huw2 (hu (τ⁻¹ • w)) hb (x (u (τ⁻¹ • w)))]
    congr 1
    exact aux_eqRec_apply x huw2
  rw [hcast]
  exact aux_symm hAinv (hu w) hb (x (A⁻¹ • u w))

end NK.HassePrinciple
