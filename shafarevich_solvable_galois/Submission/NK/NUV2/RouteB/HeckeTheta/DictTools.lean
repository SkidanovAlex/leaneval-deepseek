import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Submission.NK.NUV2.HeckeAnalytic.Dict
import Submission.NK.NUV2.RouteB.Sharp3.halfspaceCosetCount_sharp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors BigOperators

noncomputable section

namespace NK.NUV2.RouteB.HeckeTheta

variable {K : Type} [Field K] [NumberField K]

/-- The real infinite places at which the modulus `𝔪` imposes a positivity condition. -/
abbrev PosPlace (𝔪 : NK.NUV2.RouteB.Modulus K) : Type :=
  {w : InfinitePlace K // w ∈ 𝔪.pos ∧ w.IsReal}

instance instFintypePosPlace (𝔪 : NK.NUV2.RouteB.Modulus K) : Fintype (PosPlace 𝔪) :=
  inferInstanceAs (Fintype {w : InfinitePlace K // w ∈ 𝔪.pos ∧ w.IsReal})

/-- Evaluation at a real infinite place, as a continuous linear functional on the mixed space. -/
noncomputable def realCoord (w : {w : InfinitePlace K // w.IsReal}) :
    mixedSpace K →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj w).comp (ContinuousLinearMap.fst ℝ _ _)

@[simp]
theorem realCoord_apply (w : {w : InfinitePlace K // w.IsReal}) (y : mixedSpace K) :
    realCoord w y = y.1 w := rfl

/-- The part of the fundamental cone whose real coordinates have the same signs as those of `γ`
at the places of `𝔪.pos`. -/
noncomputable def sgnRegion (𝔪 : NK.NUV2.RouteB.Modulus K) (γ : K) : Set (mixedSpace K) :=
  fundamentalCone K ∩ {y : mixedSpace K | ∀ w : PosPlace 𝔪,
    ((mixedEmbedding K γ).1 ⟨w.1, w.2.2⟩ > 0 ∧ y.1 ⟨w.1, w.2.2⟩ > 0) ∨
    ((mixedEmbedding K γ).1 ⟨w.1, w.2.2⟩ < 0 ∧ y.1 ⟨w.1, w.2.2⟩ < 0)}

/-- The volume of the sign region of `γ`, truncated by the norm ball of radius one. -/
noncomputable def sgnRegionVol (𝔪 : NK.NUV2.RouteB.Modulus K) (γ : K) : ℝ :=
  (MeasureTheory.volume (sgnRegion 𝔪 γ ∩ {y : mixedSpace K | mixedEmbedding.norm y ≤ 1})).toReal

/-- The covolume of the lattice `𝔪·𝔡⁻¹` of the dictionary. -/
noncomputable def dictCovol (𝔪 : NK.NUV2.RouteB.Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) : ℝ :=
  ZLattice.covolume (idealLattice K (NK.NUV2.RouteB.Modulus.fracIdeal 𝔪 𝔡)) MeasureTheory.volume

/-- A coordinate of the mixed embedding at a real place does not vanish for a nonzero element. -/
theorem mixedEmbedding_coord_ne_zero (x : K) (hx : x ≠ 0) (w : InfinitePlace K) (hw : w.IsReal) :
    (mixedEmbedding K x).1 ⟨w, hw⟩ ≠ 0 := by
  have h1 : (mixedEmbedding K x).1 ⟨w, hw⟩
      = (NumberField.InfinitePlace.embedding_of_isReal hw) x := rfl
  have hinj : Function.Injective (NumberField.InfinitePlace.embedding_of_isReal hw) :=
    RingHom.injective _
  intro h0
  exact hx (hinj (by rw [h1] at h0; simpa using h0))

/-- The half-space functional cutting out the sign region of `γ` at a place of `𝔪.pos`. -/
noncomputable def signFun (𝔪 : NK.NUV2.RouteB.Modulus K) (γ : K) (w : PosPlace 𝔪) :
    mixedSpace K →L[ℝ] ℝ :=
  if 0 < (mixedEmbedding K γ).1 ⟨w.1, w.2.2⟩ then - realCoord ⟨w.1, w.2.2⟩
    else realCoord ⟨w.1, w.2.2⟩

theorem signFun_lt_zero_iff (𝔪 : NK.NUV2.RouteB.Modulus K) (γ : K)
    (hγ : ∀ w : PosPlace 𝔪, (mixedEmbedding K γ).1 ⟨w.1, w.2.2⟩ ≠ 0)
    (w : PosPlace 𝔪) (y : mixedSpace K) :
    signFun 𝔪 γ w y < 0 ↔
      ((mixedEmbedding K γ).1 ⟨w.1, w.2.2⟩ > 0 ∧ y.1 ⟨w.1, w.2.2⟩ > 0) ∨
      ((mixedEmbedding K γ).1 ⟨w.1, w.2.2⟩ < 0 ∧ y.1 ⟨w.1, w.2.2⟩ < 0) := by
  unfold signFun
  by_cases h : 0 < (mixedEmbedding K γ).1 ⟨w.1, w.2.2⟩
  · rw [if_pos h]
    simp only [neg_apply, realCoord_apply, neg_lt_zero]
    constructor
    · intro hy; exact Or.inl ⟨h, hy⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact h2
      · exact absurd h1 (not_lt.mpr h.le)
  · rw [if_neg h]
    have hneg : (mixedEmbedding K γ).1 ⟨w.1, w.2.2⟩ < 0 :=
      lt_of_le_of_ne (le_of_not_gt h) (hγ w)
    simp only [realCoord_apply]
    constructor
    · intro hy; exact Or.inr ⟨hneg, hy⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact absurd h1 h
      · exact h2

/-- The sign region is the trace of the fundamental cone in the half-spaces `signFun 𝔪 γ w < 0`. -/
theorem sgnRegion_eq (𝔪 : NK.NUV2.RouteB.Modulus K) (γ : K)
    (hγ : ∀ w : PosPlace 𝔪, (mixedEmbedding K γ).1 ⟨w.1, w.2.2⟩ ≠ 0) :
    sgnRegion 𝔪 γ = fundamentalCone K ∩
      {a : mixedSpace K | ∀ i : PosPlace 𝔪, signFun 𝔪 γ i a < 0} := by
  ext y
  simp only [sgnRegion, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i => (signFun_lt_zero_iff 𝔪 γ hγ i y).mpr (h2 i)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i => (signFun_lt_zero_iff 𝔪 γ hγ i y).mp (h2 i)⟩

/-- **The sharp asymptotic of the coset count.**  For a nonzero `γ` (more precisely: for `γ` whose
real coordinates at `𝔪.pos` do not vanish), the number of points of the lattice coset
`γ + 𝔪𝔡⁻¹` in the fundamental cone, with the sign conditions of `γ`, of norm `≤ t`, is
`t · vol(sign region)/covol` up to `O(t^{1-1/[K:ℚ]})`. -/
theorem cosetConeCnt_sharp (𝔪 : NK.NUV2.RouteB.Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) (γ : K) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      |((NK.NUV2.HeckeAnalytic.cosetConeCnt 𝔪 𝔡 γ t : ℝ)
        - t * sgnRegionVol 𝔪 γ / dictCovol 𝔪 𝔡)|
      ≤ C * t ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)) := by
  by_cases hγ : ∀ w : PosPlace 𝔪, (mixedEmbedding K γ).1 ⟨w.1, w.2.2⟩ ≠ 0
  swap
  · -- degenerate case: both the count and the volume vanish
    push Not at hγ
    obtain ⟨w, hw⟩ := hγ
    refine ⟨1, one_pos, fun t ht => ?_⟩
    have hvol0 : sgnRegionVol 𝔪 γ = 0 := by
      unfold sgnRegionVol
      have hempty : sgnRegion 𝔪 γ = ∅ := by
        ext y
        rw [Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, h2⟩
        have h3 := h2 w
        rcases h3 with ⟨h4, -⟩ | ⟨h4, -⟩
        · rw [hw] at h4; exact absurd h4 (lt_irrefl 0)
        · rw [hw] at h4; exact absurd h4 (lt_irrefl 0)
      rw [hempty, Set.empty_inter]
      simp
    have hcount0 : NK.NUV2.HeckeAnalytic.cosetConeCnt 𝔪 𝔡 γ t = 0 := by
      rw [NK.NUV2.HeckeAnalytic.cosetConeCnt]
      refine Nat.card_eq_zero.mpr (Or.inl ⟨fun a => ?_⟩)
      have h3 := a.2.2.2.1 w
      rcases h3 with ⟨h4, -⟩ | ⟨h4, -⟩
      · rw [hw] at h4; exact absurd h4 (lt_irrefl 0)
      · rw [hw] at h4; exact absurd h4 (lt_irrefl 0)
    rw [hcount0, Nat.cast_zero, hvol0, mul_zero, zero_div, sub_zero, abs_zero]
    have ht0 : (0 : ℝ) ≤ t ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)) :=
      Real.rpow_nonneg (by linarith) _
    linarith
  · obtain ⟨C, hCpos, hC⟩ :=
      NK.NUV2.RouteB.Sharp3.halfspaceCosetCount_sharp K
        (NK.NUV2.HeckeAnalytic.dictLattice 𝔪 𝔡) (mixedEmbedding K γ) (PosPlace 𝔪)
        (signFun 𝔪 γ)
    refine ⟨C, hCpos, fun t ht => ?_⟩
    have hvol : sgnRegionVol 𝔪 γ =
        (MeasureTheory.volume (fundamentalCone.normLeOne K ∩
          {a : mixedSpace K | ∀ i : PosPlace 𝔪, signFun 𝔪 γ i a < 0})).toReal := by
      have hset : sgnRegion 𝔪 γ ∩ {y : mixedSpace K | mixedEmbedding.norm y ≤ 1} =
          fundamentalCone.normLeOne K ∩
            {a : mixedSpace K | ∀ i : PosPlace 𝔪, signFun 𝔪 γ i a < 0} := by
        rw [sgnRegion_eq 𝔪 γ hγ]
        ext y
        simp only [Set.mem_inter_iff, fundamentalCone.mem_normLeOne, Set.mem_ofPred_eq]
        tauto
      unfold sgnRegionVol
      rw [hset]
    have hcount : NK.NUV2.HeckeAnalytic.cosetConeCnt 𝔪 𝔡 γ t =
        Nat.card {a : mixedSpace K //
          a - mixedEmbedding K γ ∈ (idealLattice K (NK.NUV2.HeckeAnalytic.dictLattice 𝔪 𝔡) :
            Set (mixedSpace K)) ∧
          a ∈ fundamentalCone K ∧ (∀ i : PosPlace 𝔪, signFun 𝔪 γ i a < 0) ∧
          mixedEmbedding.norm a ≤ t} := by
      rw [NK.NUV2.HeckeAnalytic.cosetConeCnt]
      refine Nat.card_congr (Equiv.subtypeEquivProp (funext fun a => propext ?_))
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨h1, h2, fun i => (signFun_lt_zero_iff 𝔪 γ hγ i a).mpr (h3 i), h4⟩
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨h1, h2, fun i => (signFun_lt_zero_iff 𝔪 γ hγ i a).mp (h3 i), h4⟩
    have h := hC t ht
    unfold dictCovol
    rw [hcount, hvol]
    simpa [NK.NUV2.HeckeAnalytic.dictLattice] using h

/-- The absolute norm of the dictionary lattice `𝔪·𝔡⁻¹`. -/
theorem fracIdeal_absNorm (𝔪 : NK.NUV2.RouteB.Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) :
    (FractionalIdeal.absNorm ((NK.NUV2.RouteB.Modulus.fracIdeal 𝔪 𝔡 :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
      = (Ideal.absNorm 𝔪.ideal : ℝ) / (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ) := by
  rw [NK.NUV2.RouteB.Modulus.fracIdeal, Units.val_mul, Units.val_inv_eq_inv_val,
    map_mul, map_inv₀, FractionalIdeal.coe_mk0, FractionalIdeal.coe_mk0,
    FractionalIdeal.coeIdeal_absNorm, FractionalIdeal.coeIdeal_absNorm]
  push_cast
  simp only [NK.NUV2.RouteB.Modulus.ideal0]
  ring

/-- **The covolume of the dictionary lattice.**  `N𝔡 · covol(𝔪𝔡⁻¹) = N𝔪 · κ`, the quantity that
is independent of the base ideal `𝔡`. -/
theorem absNorm_mul_dictCovol (𝔪 : NK.NUV2.RouteB.Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) :
    (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ) * dictCovol 𝔪 𝔡
      = (Ideal.absNorm 𝔪.ideal : ℝ) *
          (2⁻¹ ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(NumberField.discr K : ℝ)|) := by
  rw [dictCovol, NumberField.mixedEmbedding.covolume_idealLattice K
    (NK.NUV2.RouteB.Modulus.fracIdeal 𝔪 𝔡), fracIdeal_absNorm]
  have hne : (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ) ≠ 0 := by
    have h : (𝔡 : Ideal (𝓞 K)) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp 𝔡.2
    exact_mod_cast (Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mpr h)).ne'
  field_simp

/-- The preimage of the positive reals under a real place has finite index in the units. -/
theorem finiteIndex_comap_posSubgroup (w : InfinitePlace K) (hw : w.IsReal) :
    ((Units.posSubgroup ℝ).comap (NK.NUV2.HeckeAnalytic.unitToReal K w hw)).FiniteIndex := by
  haveI : (Units.posSubgroup ℝ).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, Units.index_posSubgroup ℝ]
    norm_num
  rw [Subgroup.finiteIndex_iff, Subgroup.index_comap]
  exact Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mp
    (Subgroup.isFiniteRelIndex_of_finiteIndex (H := Units.posSubgroup ℝ))

/-- The group of units which are positive at the real places of `pos` has finite index. -/
theorem finiteIndex_posUnits (𝔪 : NK.NUV2.RouteB.Modulus K) :
    (NK.NUV2.HeckeAnalytic.posUnits K 𝔪.pos).FiniteIndex := by
  rw [NK.NUV2.HeckeAnalytic.posUnits]
  exact Subgroup.finiteIndex_iInf (fun w => finiteIndex_comap_posSubgroup w.1 w.2.2)

/-- The group `congUnit 𝔪` of units congruent to `1` modulo the modulus and positive at the
places of `𝔪.pos` has finite index in the units. -/
theorem finiteIndex_congUnit (𝔪 : NK.NUV2.RouteB.Modulus K) :
    (NK.NUV2.HeckeAnalytic.congUnit 𝔪).FiniteIndex := by
  haveI := finiteIndex_posUnits 𝔪
  haveI : (NK.NUV2.RouteB.unitCongOne 𝔪.ideal).FiniteIndex :=
    NK.NUV2.RouteB.finiteIndex_unitCongOne 𝔪.ideal
  rw [NK.NUV2.HeckeAnalytic.congUnit]
  infer_instance

instance instFintypeQuotCongUnit (𝔪 : NK.NUV2.RouteB.Modulus K) :
    Fintype ((𝓞 K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪) :=
  haveI : (NK.NUV2.HeckeAnalytic.congUnit 𝔪).FiniteIndex := finiteIndex_congUnit 𝔪
  haveI : Finite ((𝓞 K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪) := inferInstance
  Fintype.ofFinite _


end NK.NUV2.RouteB.HeckeTheta
