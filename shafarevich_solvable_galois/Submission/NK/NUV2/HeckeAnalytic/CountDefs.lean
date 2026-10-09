import Mathlib
import Submission.NK.NUV2.HeckeAnalytic.Dict
import Submission.NK.NUV2.RouteB.RayModulus.CosetCountDefs
import Submission.NK.NUV2.RouteB.RayModulus.classOfIdeal_eq_iff
import Submission.NK.NUV2.RouteB.RayModulus.exists_ideal_of_class
import Submission.NK.NUV2.RouteB.Dict.latticeCosetCount_halfspaces_isBigO
import Submission.NK.NUV2.idealCount_eq_class_sub_isBigO
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The vocabulary of the sharp ray-class count for a congruence subgroup

Definitions and bookkeeping for `NK.NUV2.HeckeAnalytic.sharpSub_congSubgroup`:

* `posRealPlace 𝔪` — the real infinite places carrying a positivity condition of the modulus `𝔪`;
* `signRegion 𝔪 γ` — the fundamental cone cut by the sign conditions of `γ` at those places (the
  region in which `cosetConeCnt` counts the lattice points of `γ + 𝔪.ideal·𝔡⁻¹`);
* `signRegionVolume 𝔪 γ` — its volume truncated by the norm ball of radius one;
* `dictCovolume 𝔪 𝔡` — the covolume of the lattice `𝔪.ideal·𝔡⁻¹`;
* the finiteness of the quotient `(𝓞 K)ˣ ⧸ congUnit 𝔪` (the index set of the dictionary sum).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open NumberField IsDedekindDomain NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors

namespace NK.NUV2.HeckeAnalytic

variable {K : Type} [Field K] [NumberField K]

/-- The real infinite places at which a modulus imposes a positivity condition. -/
abbrev posRealPlace (𝔪 : NK.NUV2.RouteB.Modulus K) : Type :=
  {w : InfinitePlace K // w ∈ 𝔪.pos ∧ w.IsReal}

instance instFintypePosRealPlace (𝔪 : NK.NUV2.RouteB.Modulus K) :
    Fintype (posRealPlace 𝔪) :=
  inferInstanceAs (Fintype {w : InfinitePlace K // w ∈ 𝔪.pos ∧ w.IsReal})

/-- The region of the mixed space attached to a modulus `𝔪` and an element `γ`: the fundamental
cone, cut by the condition that the real coordinates at the places of `𝔪.pos` have the same sign
as the corresponding coordinates of `γ`. -/
noncomputable def signRegion (𝔪 : NK.NUV2.RouteB.Modulus K) (γ : K) : Set (mixedSpace K) :=
  fundamentalCone K ∩ {y : mixedSpace K | ∀ w : {w : InfinitePlace K // w ∈ 𝔪.pos ∧ w.IsReal},
    ((mixedEmbedding K γ).1 ⟨w.1, w.2.2⟩ > 0 ∧ y.1 ⟨w.1, w.2.2⟩ > 0) ∨
    ((mixedEmbedding K γ).1 ⟨w.1, w.2.2⟩ < 0 ∧ y.1 ⟨w.1, w.2.2⟩ < 0)}

/-- The unit transversal element attached to a class of units modulo `congUnit 𝔪`: the inverse of
the representative `Quotient.out`. -/
noncomputable def unitTrans (𝔪 : NK.NUV2.RouteB.Modulus K)
    (q : (𝓞 K)ˣ ⧸ congUnit 𝔪) : K := (((Quotient.out q : (𝓞 K)ˣ) : K))⁻¹

@[simp] theorem unitTrans_def (𝔪 : NK.NUV2.RouteB.Modulus K)
    (q : (𝓞 K)ˣ ⧸ congUnit 𝔪) : unitTrans 𝔪 q = (((Quotient.out q : (𝓞 K)ˣ) : K))⁻¹ := rfl

/-- The volume of the sign region of `γ` truncated by the norm ball of radius one. -/
noncomputable def signRegionVolume (𝔪 : NK.NUV2.RouteB.Modulus K) (γ : K) : ℝ :=
  (MeasureTheory.volume (signRegion 𝔪 γ ∩ {y : mixedSpace K | mixedEmbedding.norm y ≤ 1})).toReal

/-- The covolume of the lattice `𝔪.ideal · 𝔡⁻¹` of the dictionary. -/
noncomputable def dictCovolume (𝔪 : NK.NUV2.RouteB.Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) : ℝ :=
  ZLattice.covolume (idealLattice K (dictLattice 𝔪 𝔡)) MeasureTheory.volume

/-- The covolume of the ideal lattice of a fractional ideal `I` is `|N I| · κ`. -/
theorem covolume_idealLattice_units (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (idealLattice K I) MeasureTheory.volume =
      (FractionalIdeal.absNorm ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) : ℝ) * NK.NUV2.kappa K := by
  rw [covolume_idealLattice, NK.NUV2.kappa]
  ring

/-- The absolute norm of the lattice `𝔪.ideal·𝔡⁻¹` is `N𝔪 / N𝔡`. -/
theorem absNorm_dictLattice (𝔪 : NK.NUV2.RouteB.Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) :
    FractionalIdeal.absNorm ((dictLattice 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K)
      = (Ideal.absNorm 𝔪.ideal : ℚ) * (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℚ)⁻¹ := by
  rw [dictLattice, NK.NUV2.RouteB.Modulus.fracIdeal, Units.val_mul, Units.val_inv_eq_inv_val,
    map_mul, map_inv₀, FractionalIdeal.coe_mk0, FractionalIdeal.coe_mk0,
    FractionalIdeal.coeIdeal_absNorm, FractionalIdeal.coeIdeal_absNorm]
  rfl

/-- The covolume of `𝔪.ideal·𝔡⁻¹` is `(N𝔪/N𝔡)·κ`. -/
theorem dictCovolume_eq (𝔪 : NK.NUV2.RouteB.Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) :
    dictCovolume 𝔪 𝔡
      = ((Ideal.absNorm 𝔪.ideal : ℝ) / (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ)) *
        NK.NUV2.kappa K := by
  rw [dictCovolume, covolume_idealLattice_units, absNorm_dictLattice]
  push_cast
  ring

/-- A unit of `𝓞 K` has nonzero real coordinate at every real infinite place. -/
theorem mixedEmbedding_unit_ne_zero (𝔪 : NK.NUV2.RouteB.Modulus K) (u : (𝓞 K)ˣ)
    (w : {w : InfinitePlace K // w ∈ 𝔪.pos ∧ w.IsReal}) :
    (mixedEmbedding K (((u : (𝓞 K)ˣ) : K)⁻¹)).1 ⟨w.1, w.2.2⟩ ≠ 0 := by
  have h0 : NumberField.InfinitePlace.embedding_of_isReal w.2.2 ((u : (𝓞 K)ˣ) : K) ≠ 0 := by
    intro hc
    have h1 : (((u : (𝓞 K)ˣ) : 𝓞 K) : K) = 0 :=
      RingHom.injective (NumberField.InfinitePlace.embedding_of_isReal w.2.2)
        (by rw [hc, map_zero])
    exact Units.ne_zero u (RingOfIntegers.coe_injective h1)
  rw [mixedEmbedding_apply_isReal, map_inv₀]
  exact inv_ne_zero h0

/-- The preimage under `unitToReal` of the positive reals has finite index in the units. -/
theorem finiteIndex_comap_posSubgroup (𝔪 : NK.NUV2.RouteB.Modulus K)
    (w : posRealPlace 𝔪) :
    ((Units.posSubgroup ℝ).comap (unitToReal K w.1 w.2.2)).FiniteIndex := by
  haveI : (Units.posSubgroup ℝ).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, Units.index_posSubgroup ℝ]
    norm_num
  rw [Subgroup.finiteIndex_iff, Subgroup.index_comap]
  exact Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mp
    (Subgroup.isFiniteRelIndex_of_finiteIndex (K := (unitToReal K w.1 w.2.2).range))

/-- The group of units which are positive at the places of `𝔪.pos` has finite index. -/
theorem finiteIndex_posUnits (𝔪 : NK.NUV2.RouteB.Modulus K) :
    (posUnits K 𝔪.pos).FiniteIndex := by
  rw [posUnits]
  exact Subgroup.finiteIndex_iInf fun w => finiteIndex_comap_posSubgroup 𝔪 w

/-- The group `congUnit 𝔪` of units congruent to `1` modulo the ideal of the modulus and positive
at the places of `𝔪.pos` has finite index in the units. -/
theorem finiteIndex_congUnit (𝔪 : NK.NUV2.RouteB.Modulus K) :
    (congUnit 𝔪).FiniteIndex := by
  haveI := finiteIndex_posUnits 𝔪
  haveI : (NK.NUV2.RouteB.unitCongOne 𝔪.ideal).FiniteIndex := inferInstance
  rw [congUnit]
  infer_instance

instance instFiniteQuotCongUnit (𝔪 : NK.NUV2.RouteB.Modulus K) :
    Finite ((𝓞 K)ˣ ⧸ congUnit 𝔪) :=
  haveI := finiteIndex_congUnit 𝔪
  Subgroup.finite_quotient_of_finiteIndex

instance instFintypeQuotCongUnit (𝔪 : NK.NUV2.RouteB.Modulus K) :
    Fintype ((𝓞 K)ˣ ⧸ congUnit 𝔪) := Fintype.ofFinite _

end NK.NUV2.HeckeAnalytic
