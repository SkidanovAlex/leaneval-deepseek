import Mathlib
import Submission.NK.NUV2.RouteB.RayModulus.Defs
import Submission.NK.NUV2.RouteB.RayModulus.CosetCountDefs
import Submission.NK.NUV2.RouteB.RayModulus.classOfIdeal_eq_iff
import Submission.NK.NUV2.RouteB.RayModulus.exists_ideal_of_class
import Submission.NK.NUV2.RouteB.CongCount.finite_rayClassGroup_congSubgroup
import Submission.NK.NUV2.RouteB.CongCount.cosetConeCount_of_geoHyp
import Submission.NK.NUV2.RouteB.CongCountDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Counting the ray classes of a congruence subgroup: the auxiliary vocabulary

For a number field `K` and a modulus `𝔪` this file fixes the objects used in the proof of
`NK.NUV2.RouteB.SharpSub K (CongSubgroup K 𝔪) S θ` (the sharp ray class count for the
congruence subgroup `U(𝔪) = CongSubgroup K 𝔪`):

* `congUnitReps 𝔪` — a transversal of the unit group `(𝓞 K)ˣ` modulo the units congruent to `1`
  modulo the integral ideal `𝔪.ideal` of the modulus (`unitCongOne 𝔪.ideal`);
* `enlargeModulus 𝔪 S` — the modulus obtained from `𝔪` by imposing, in addition, a congruence
  condition of exponent `1` at every prime of `S`: its support contains `S` and
  `U(enlargeModulus 𝔪 S) ≤ U(𝔪)`;
* `congSubgroup_le_of_exps_le` — `U(𝔫) ≤ U(𝔪)` when `𝔫` has larger exponents;
* `rayBase 𝔫 c` — an integral ideal, coprime to the support of `𝔫`, in the class `c`;
* `cosetConeCountF_bound` — the power saving bound for the mixed space coset count
  `NK.NUV2.RouteB.cosetConeCountF`, with the sharp exponent `1 - 1/[K:ℚ]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open NumberField IsDedekindDomain
open scoped Classical BigOperators nonZeroDivisors

noncomputable section

namespace NK.NUV2.RouteB.CongCount

open NK.GlobalCFT (Idele IdeleClassGroup Place)

variable {K : Type} [Field K] [NumberField K]

/-! ## The transversal of the units modulo the congruence units -/

/-- The congruence units of a modulus: the units of `𝓞 K` which are congruent to `1` modulo the
integral ideal of the modulus. -/
abbrev congUnits (𝔪 : NK.NUV2.RouteB.Modulus K) : Subgroup (𝓞 K)ˣ :=
  NK.NUV2.RouteB.unitCongOne 𝔪.ideal

theorem mem_congUnits {𝔪 : NK.NUV2.RouteB.Modulus K} {u : (𝓞 K)ˣ} :
    u ∈ congUnits 𝔪 ↔ (u : 𝓞 K) - 1 ∈ 𝔪.ideal :=
  NK.NUV2.RouteB.mem_unitCongOne_iff

noncomputable def congUnitReps (𝔪 : NK.NUV2.RouteB.Modulus K) : Finset (𝓞 K)ˣ :=
  (Finset.univ : Finset ((𝓞 K)ˣ ⧸ NK.NUV2.RouteB.unitCongOne 𝔪.ideal)).image
    (Quotient.out : (𝓞 K)ˣ ⧸ NK.NUV2.RouteB.unitCongOne 𝔪.ideal → (𝓞 K)ˣ)

/-- **The transversal property.**  Every unit `u` has a unique representative `γ` in
`congUnitReps 𝔪` with `u * γ⁻¹` a congruence unit. -/
theorem existsUnique_congUnitReps (𝔪 : NK.NUV2.RouteB.Modulus K) (u : (𝓞 K)ˣ) :
    ∃! γ : (𝓞 K)ˣ, γ ∈ congUnitReps 𝔪 ∧ u * γ⁻¹ ∈ congUnits 𝔪 := by
  classical
  let q : (𝓞 K)ˣ ⧸ NK.NUV2.RouteB.unitCongOne 𝔪.ideal := QuotientGroup.mk u
  have hmem : Quotient.out q ∈ congUnitReps 𝔪 := by
    have hq : q ∈ (Finset.univ : Finset ((𝓞 K)ˣ ⧸ NK.NUV2.RouteB.unitCongOne 𝔪.ideal)) :=
      Finset.mem_univ _
    exact Finset.mem_image_of_mem Quotient.out hq
  have hspec : u * (Quotient.out q)⁻¹ ∈ congUnits 𝔪 := by
    have h2 : (↑(Quotient.out q) : (𝓞 K)ˣ ⧸ NK.NUV2.RouteB.unitCongOne 𝔪.ideal) = ↑u := by
      rw [QuotientGroup.out_eq']
    rw [mul_comm, ← QuotientGroup.eq]
    exact h2
  refine ⟨Quotient.out q, ⟨hmem, hspec⟩, ?_⟩
  · intro γ hγ
    obtain ⟨q', -, hq'⟩ := Finset.mem_image.mp hγ.1
    have h2 : (↑γ : (𝓞 K)ˣ ⧸ NK.NUV2.RouteB.unitCongOne 𝔪.ideal)
        = (↑u : (𝓞 K)ˣ ⧸ NK.NUV2.RouteB.unitCongOne 𝔪.ideal) := by
      rw [QuotientGroup.eq]
      simpa [mul_comm] using hγ.2
    have h1 : q' = q := by
      calc q' = (↑(Quotient.out q') : (𝓞 K)ˣ ⧸ NK.NUV2.RouteB.unitCongOne 𝔪.ideal) :=
            (QuotientGroup.out_eq' q').symm
        _ = ↑γ := by rw [hq']
        _ = ↑u := h2
        _ = q := rfl
    exact hq'.symm.trans (congrArg Quotient.out h1)

/-- The transversal is nonempty. -/
theorem congUnitReps_nonempty (𝔪 : NK.NUV2.RouteB.Modulus K) :
    (congUnitReps 𝔪).Nonempty := by
  obtain ⟨γ, hγ, -⟩ := existsUnique_congUnitReps 𝔪 (1 : (𝓞 K)ˣ)
  exact ⟨γ, hγ.1⟩

/-! ## Enlarging a modulus -/

/-- The modulus obtained from `𝔪` by increasing by `1` the congruence exponent at every prime of
the finite set `S` (and keeping the archimedean part empty). -/
noncomputable def enlargeModulus (𝔪 : NK.NUV2.RouteB.Modulus K)
    (S : Finset (NK.HeckeL.PrimeIdeal K)) : NK.NUV2.RouteB.Modulus K where
  exps q := 𝔪.exps q + if q ∈ S then 1 else 0
  finite_support := by
    classical
    rw [NK.NUV2.RouteB.HasFiniteSupport]
    have h1 : ∀ᶠ q in Filter.cofinite, (if q ∈ S then (1 : ℕ) else 0) = 0 := by
      rw [Filter.eventually_cofinite]
      refine S.finite_toSet.subset (fun q hq => ?_)
      simp only [Set.mem_ofPred_eq] at hq
      by_contra hmem
      have hmem' : ¬ (q ∈ S) := by simpa using hmem
      exact hq (by rw [if_neg hmem'])
    refine (𝔪.finite_support.and h1).mono ?_
    rintro q ⟨hq1, hq2⟩
    rw [hq1, hq2, add_zero]
  pos := ∅

@[simp]
theorem enlargeModulus_exps (𝔪 : NK.NUV2.RouteB.Modulus K)
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (q : NK.HeckeL.PrimeIdeal K) :
    (enlargeModulus 𝔪 S).exps q = 𝔪.exps q + if q ∈ S then 1 else 0 := rfl

@[simp]
theorem enlargeModulus_pos (𝔪 : NK.NUV2.RouteB.Modulus K)
    (S : Finset (NK.HeckeL.PrimeIdeal K)) : (enlargeModulus 𝔪 S).pos = ∅ := rfl

theorem enlargeModulus_exps_ne_zero_iff (𝔪 : NK.NUV2.RouteB.Modulus K)
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (q : NK.HeckeL.PrimeIdeal K) :
    (enlargeModulus 𝔪 S).exps q ≠ 0 ↔ q ∈ S ∨ 𝔪.exps q ≠ 0 := by
  rw [enlargeModulus_exps]
  by_cases hq : q ∈ S <;> simp [hq]

theorem le_enlargeModulus_exps (𝔪 : NK.NUV2.RouteB.Modulus K)
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (q : NK.HeckeL.PrimeIdeal K) :
    𝔪.exps q ≤ (enlargeModulus 𝔪 S).exps q := by
  rw [enlargeModulus_exps]
  by_cases hq : q ∈ S <;> simp [hq]

/-! ## Monotonicity of the congruence subgroup in the modulus -/

/-- The congruence subgroup decreases when the congruence exponents increase. -/
theorem congSubgroup_le_of_exps_le {𝔪 𝔫 : NK.NUV2.RouteB.Modulus K}
    (hexp : ∀ q : NK.HeckeL.PrimeIdeal K, 𝔪.exps q ≤ 𝔫.exps q) (hpos : 𝔫.pos = 𝔪.pos) :
    NK.NUV2.RouteB.CongSubgroup K 𝔫 ≤ NK.NUV2.RouteB.CongSubgroup K 𝔪 := by
  intro x hx
  rw [NK.NUV2.RouteB.Modulus.mem_congSubgroup_iff] at hx ⊢
  refine ⟨fun q => ⟨(hx.1 q).1, ?_⟩, fun w hw hmem => ?_⟩
  · have hq := (hx.1 q).2
    unfold NK.NUV2.RouteB.IsCongAt at hq ⊢
    refine le_trans hq ?_
    refine WithZero.exp_le_exp.mpr ?_
    rw [neg_le_neg_iff]
    exact_mod_cast hexp q
  · exact hx.2 w hw (by rw [hpos]; exact hmem)

theorem congSubgroup_enlargeModulus_le (𝔪 : NK.NUV2.RouteB.Modulus K)
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (hpos : 𝔪.pos = ∅) :
    NK.NUV2.RouteB.CongSubgroup K (enlargeModulus 𝔪 S) ≤
      NK.NUV2.RouteB.CongSubgroup K 𝔪 :=
  congSubgroup_le_of_exps_le (le_enlargeModulus_exps 𝔪 S)
    (by rw [enlargeModulus_pos, hpos])

/-! ## A base ideal in a ray class -/

/-- A chosen integral ideal, coprime to the support of the modulus, in a given ray class of
`U(𝔪)` (exists by `NK.NUV2.RouteB.RayModulus.exists_ideal_of_class`). -/
noncomputable def rayBase (𝔪 : NK.NUV2.RouteB.Modulus K)
    (c : IdeleClassGroup.rayClassGroup K (NK.NUV2.RouteB.CongSubgroup K 𝔪)) : Ideal (𝓞 K) :=
  Classical.choose (NK.NUV2.RouteB.RayModulus.exists_ideal_of_class K 𝔪 c)

theorem rayBase_ne_zero (𝔪 : NK.NUV2.RouteB.Modulus K)
    (c : IdeleClassGroup.rayClassGroup K (NK.NUV2.RouteB.CongSubgroup K 𝔪)) :
    rayBase 𝔪 c ≠ 0 := by
  rw [rayBase]
  exact (Classical.choose_spec (NK.NUV2.RouteB.RayModulus.exists_ideal_of_class K 𝔪 c)).1

theorem rayBase_coprime (𝔪 : NK.NUV2.RouteB.Modulus K)
    (c : IdeleClassGroup.rayClassGroup K (NK.NUV2.RouteB.CongSubgroup K 𝔪))
    (q : NK.HeckeL.PrimeIdeal K) (hq : 𝔪.exps q ≠ 0) : ¬ q.asIdeal ∣ rayBase 𝔪 c := by
  rw [rayBase]
  exact (Classical.choose_spec (NK.NUV2.RouteB.RayModulus.exists_ideal_of_class K 𝔪 c)).2.1 q hq

theorem classOfIdeal_rayBase (𝔪 : NK.NUV2.RouteB.Modulus K)
    (c : IdeleClassGroup.rayClassGroup K (NK.NUV2.RouteB.CongSubgroup K 𝔪)) :
    NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) (rayBase 𝔪 c) = c := by
  rw [rayBase]
  exact (Classical.choose_spec (NK.NUV2.RouteB.RayModulus.exists_ideal_of_class K 𝔪 c)).2.2

/-! ## The geometry: the bound for the coset cone counts -/

/-- **The lattice coset count in the fundamental cone**, with the sharp exponent `1 - 1/[K:ℚ]`.
This is `NK.NUV2.RouteB.latticeCosetCount_cone_isBigO` with the exponent rewritten using
`NumberField.mixedEmbedding.finrank`. -/
theorem latticeCosetCount_cone_sharp (K : Type) [Field K] [NumberField K]
    (I : (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ)
    (x₀ : mixedEmbedding.mixedSpace K) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      |((Nat.card {a : mixedEmbedding.mixedSpace K //
          a - x₀ ∈ (mixedEmbedding.idealLattice K I : Set (mixedEmbedding.mixedSpace K)) ∧
          a ∈ mixedEmbedding.fundamentalCone K ∧
          mixedEmbedding.norm a ≤ X} : ℝ)
        - X * NK.NUV2.RouteB.coneMainTerm K I)|
      ≤ C * X ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)) := by
  have hbd := NK.NUV2.RouteB.CongCount.frontierNormLeOne_cthickening_le K
  have hmain :=
    NK.NUV2.Geom.latticeCosetCount_sub_volume_isBigO
      (mixedEmbedding.mixedSpace K) (mixedEmbedding.idealLattice K I)
      (mixedEmbedding.fundamentalCone.normLeOne K)
      (NumberField.mixedEmbedding.fundamentalCone.isBounded_normLeOne K)
      (NumberField.mixedEmbedding.fundamentalCone.measurableSet_normLeOne K) hbd x₀
  obtain ⟨C₁, hC₁pos, hC₁⟩ := hmain
  refine ⟨C₁, hC₁pos, fun X hX => ?_⟩
  rw [NK.NUV2.RouteB.natCard_cone_coset_eq_routeB I x₀ hX,
    NumberField.mixedEmbedding.finrank]
  have hX' := hC₁ X hX
  rw [mul_div_assoc, NK.NUV2.RouteB.volume_normLeOne_div_covolume I,
    NumberField.mixedEmbedding.finrank] at hX'
  simpa [one_div, NK.NUV2.RouteB.coneMainTerm] using hX'

/-- **The bound for the coset cone count** (the mixed space count of
`NK.NUV2.RouteB.cosetConeCountF`) with the sharp exponent. -/
theorem cosetConeCountF_bound (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ)
    (x₀ : mixedEmbedding.mixedSpace K) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y →
      |((NK.NUV2.RouteB.cosetConeCountF K I x₀ Y : ℝ) - Y * NK.NUV2.RouteB.coneMainTerm K I)|
        ≤ C * Y ^ (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)) :=
  latticeCosetCount_cone_sharp K I x₀

end NK.NUV2.RouteB.CongCount
