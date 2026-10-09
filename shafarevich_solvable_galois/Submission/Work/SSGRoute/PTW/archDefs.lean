import Mathlib
import Submission.NK.GlobalCFT.IdeleNorm
import Submission.NK.GlobalCFT.GlobalCFT
import Submission.Work.SSGRoute.PTW.localContentSection
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean building blocks for `p`-divisibility of `C_K^0`

This file introduces the subgroups of the idèle group `𝕀 K` used in the proof that the identity
component `C_K^0` of the idèle class group is `p`-divisible:

* `archCompIdele K` (`A`): idèles trivial at every finite place whose archimedean components lie in
  the identity components `(K_wˣ)⁰` of the local unit groups;
* `archUnitIdele K`: the same without the condition at the finite places;
* `archCompOpen K` (`W`): `archUnitIdele K ⊓ integralIdeles K`, the group
  `∏_{w | ∞} (K_wˣ)⁰ × ∏_{q} 𝒪_qˣ`;
* `normOneArchComp K` (`V¹`): `A ⊓ 𝕀¹K`;
* `archPlaceIdele K`: the map `∏_{w | ∞} (K_wˣ) ↪ 𝕀 K` filling in `1` at the finite places, whose
  range is `A`;
* `secVal`/`secBal`: the idèle section of the content map, with archimedean components
  `t w (c ^ 1/N)` (`N = #InfinitePlace K`), where `t w` is a local content section.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.PTW

open NK.GlobalCFT

/-- **`A`**: the idèles which are `1` at every finite place and whose archimedean components lie in
the identity components of the local unit groups. -/
def archCompIdele (K : Type*) [Field K] [NumberField K] : Subgroup (Idele K) where
  carrier := {a : Idele K | (∀ q : HeightOneSpectrum (𝓞 K), a (Place.ofFinite q) = 1) ∧
    ∀ w : InfinitePlace K,
      a (Place.ofInfinite w) ∈ Subgroup.connectedComponentOfOne ((w.Completion)ˣ)}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · intro q
      rfl
    · intro w
      rw [Idele.one_apply]
      exact Subgroup.one_mem _
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩
    · intro q
      rw [Idele.mul_apply, ha1 q, hb1 q, one_mul]
    · intro w
      rw [Idele.mul_apply]
      exact Subgroup.mul_mem _ (ha2 w) (hb2 w)
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨?_, ?_⟩
    · intro q
      rw [Idele.inv_apply, ha1 q, inv_one]
    · intro w
      rw [Idele.inv_apply]
      exact Subgroup.inv_mem _ (ha2 w)

/-- The idèles whose archimedean components lie in the identity components of the local unit
groups (no condition at the finite places). -/
def archUnitIdele (K : Type*) [Field K] [NumberField K] : Subgroup (Idele K) where
  carrier := {a : Idele K | ∀ w : InfinitePlace K,
    a (Place.ofInfinite w) ∈ Subgroup.connectedComponentOfOne ((w.Completion)ˣ)}
  one_mem' := by
    intro w
    rw [Idele.one_apply]
    exact Subgroup.one_mem _
  mul_mem' := by
    intro a b ha hb w
    rw [Idele.mul_apply]
    exact Subgroup.mul_mem _ (ha w) (hb w)
  inv_mem' := by
    intro a ha w
    rw [Idele.inv_apply]
    exact Subgroup.inv_mem _ (ha w)

/-- **`W`**: the open subgroup `∏_{w | ∞} (K_wˣ)⁰ × ∏_{q} 𝒪_qˣ` of the idèle group. -/
def archCompOpen (K : Type*) [Field K] [NumberField K] : Subgroup (Idele K) :=
  archUnitIdele K ⊓ Idele.integralIdeles K

/-- **`V¹`**: the content-one archimedean idèles: `A ⊓ 𝕀¹K`. -/
def normOneArchComp (K : Type*) [Field K] [NumberField K] : Subgroup (Idele K) :=
  archCompIdele K ⊓ Idele.normOne K

theorem mem_archCompIdele {K : Type*} [Field K] [NumberField K] {a : Idele K} :
    a ∈ archCompIdele K ↔ (∀ q : HeightOneSpectrum (𝓞 K), a (Place.ofFinite q) = 1) ∧
      ∀ w : InfinitePlace K,
        a (Place.ofInfinite w) ∈ Subgroup.connectedComponentOfOne ((w.Completion)ˣ) := Iff.rfl

theorem mem_archUnitIdele {K : Type*} [Field K] [NumberField K] {a : Idele K} :
    a ∈ archUnitIdele K ↔ ∀ w : InfinitePlace K,
      a (Place.ofInfinite w) ∈ Subgroup.connectedComponentOfOne ((w.Completion)ˣ) := Iff.rfl

theorem mem_archCompOpen {K : Type*} [Field K] [NumberField K] {a : Idele K} :
    a ∈ archCompOpen K ↔ a ∈ archUnitIdele K ∧ a ∈ Idele.integralIdeles K := Iff.rfl

theorem archCompOpen_le_archUnitIdele {K : Type*} [Field K] [NumberField K] :
    archCompOpen K ≤ archUnitIdele K := inf_le_left

theorem mem_normOneArchComp {K : Type*} [Field K] [NumberField K] {a : Idele K} :
    a ∈ normOneArchComp K ↔ a ∈ archCompIdele K ∧ a ∈ Idele.normOne K := Iff.rfl

/-- The idèle with prescribed archimedean components and `1` at every finite place, as a family of
local units. -/
def archPlaceVal (K : Type*) [Field K] [NumberField K]
    (b : ∀ w : InfinitePlace K, (w.Completion)ˣ) :
    (v : Place K) → ↥(Place.localUnits K v) :=
  fun v => match v with
    | Sum.inl w => ⟨b w, by rw [Place.localUnits_ofInfinite]; exact Subgroup.mem_top _⟩
    | Sum.inr _ => ⟨1, Subgroup.one_mem _⟩

/-- The idèle with prescribed archimedean components and `1` at every finite place. -/
def archPlaceIdele (K : Type*) [Field K] [NumberField K]
    (b : ∀ w : InfinitePlace K, (w.Completion)ˣ) : Idele K :=
  RestrictedProduct.structureMap (fun v : Place K => (Place.localField K v)ˣ)
    (fun v : Place K => (Place.localUnits K v : Set ((Place.localField K v)ˣ))) Filter.cofinite
    (archPlaceVal K b)

theorem archPlaceIdele_infinite (K : Type*) [Field K] [NumberField K]
    (b : ∀ w : InfinitePlace K, (w.Completion)ˣ) (w : InfinitePlace K) :
    archPlaceIdele K b (Place.ofInfinite w) = b w := by
  change (archPlaceVal K b (Place.ofInfinite w)).1 = b w
  simp [archPlaceVal]

theorem archPlaceIdele_finite (K : Type*) [Field K] [NumberField K]
    (b : ∀ w : InfinitePlace K, (w.Completion)ˣ) (q : HeightOneSpectrum (𝓞 K)) :
    archPlaceIdele K b (Place.ofFinite q) = 1 := by
  change (archPlaceVal K b (Place.ofFinite q)).1 = 1
  simp [archPlaceVal]

theorem mem_archCompIdele_iff_exists {K : Type*} [Field K] [NumberField K] {a : Idele K} :
    a ∈ archCompIdele K ↔ ∃ b : ∀ w : InfinitePlace K, (w.Completion)ˣ,
      (∀ w, b w ∈ Subgroup.connectedComponentOfOne ((w.Completion)ˣ)) ∧
        archPlaceIdele K b = a := by
  constructor
  · intro ha
    refine ⟨fun w => a (Place.ofInfinite w), ha.2, ?_⟩
    ext v
    rcases v with w | q
    · rw [archPlaceIdele_infinite]
    · rw [archPlaceIdele_finite, ha.1 q]
  · rintro ⟨b, hb, rfl⟩
    exact ⟨fun q => archPlaceIdele_finite K b q,
      fun w => by rw [archPlaceIdele_infinite]; exact hb w⟩


/-! ## The local sections and the archimedean idèle section -/

/-- The local content section at an infinite place, chosen once and for all. -/
noncomputable def localSec (K : Type*) [Field K] [NumberField K] (w : InfinitePlace K) :
    ℝˣ → (w.Completion)ˣ :=
  Classical.choose (localContentSection K w)

theorem localSec_continuous (K : Type*) [Field K] [NumberField K] (w : InfinitePlace K) :
    Continuous (localSec K w) :=
  (Classical.choose_spec (localContentSection K w)).1

theorem localSec_one (K : Type*) [Field K] [NumberField K] (w : InfinitePlace K) :
    localSec K w 1 = 1 :=
  (Classical.choose_spec (localContentSection K w)).2.1

theorem localSec_mem (K : Type*) [Field K] [NumberField K] (w : InfinitePlace K) (c : ℝˣ) :
    localSec K w c ∈ Subgroup.connectedComponentOfOne ((w.Completion)ˣ) :=
  (Classical.choose_spec (localContentSection K w)).2.2.1 c

theorem localSec_localAbs (K : Type*) [Field K] [NumberField K] (w : InfinitePlace K) (c : ℝˣ)
    (hc : 0 < (c : ℝ)) :
    NK.GlobalCFT.Idele.localAbs K (NK.GlobalCFT.Place.ofInfinite w) (localSec K w c) = c :=
  (Classical.choose_spec (localContentSection K w)).2.2.2.1 c hc

theorem localSec_mul (K : Type*) [Field K] [NumberField K] (w : InfinitePlace K) (c c' : ℝˣ)
    (hc : 0 < (c : ℝ)) (hc' : 0 < (c' : ℝ)) :
    localSec K w (c * c') = localSec K w c * localSec K w c' :=
  (Classical.choose_spec (localContentSection K w)).2.2.2.2 c c' hc hc'

/-- The archimedean component family of the idèle section. -/
noncomputable def archSecVal (K : Type*) [Field K] [NumberField K] (w₀ : InfinitePlace K)
    (c : ℝˣ) : (w : InfinitePlace K) → (w.Completion)ˣ := by
  classical
  exact fun w => if h : w = w₀ then h.symm ▸ localSec K w₀ c else 1

/-- The idèle section of the content map at the infinite place `w₀`. -/
noncomputable def archSec (K : Type*) [Field K] [NumberField K] (w₀ : InfinitePlace K)
    (c : ℝˣ) : Idele K :=
  archPlaceIdele K (archSecVal K w₀ c)

theorem archSec_infinite (K : Type*) [Field K] [NumberField K] (w₀ : InfinitePlace K)
    (c : ℝˣ) (w : InfinitePlace K) :
    archSec K w₀ c (Place.ofInfinite w) = archSecVal K w₀ c w :=
  archPlaceIdele_infinite K (archSecVal K w₀ c) w

theorem archSec_finite (K : Type*) [Field K] [NumberField K] (w₀ : InfinitePlace K) (c : ℝˣ)
    (q : HeightOneSpectrum (𝓞 K)) : archSec K w₀ c (Place.ofFinite q) = 1 :=
  archPlaceIdele_finite K (archSecVal K w₀ c) q

theorem archSec_self (K : Type*) [Field K] [NumberField K] (w₀ : InfinitePlace K) (c : ℝˣ) :
    archSec K w₀ c (Place.ofInfinite w₀) = localSec K w₀ c := by
  classical
  rw [archSec_infinite]
  simp [archSecVal]

theorem archSec_of_ne (K : Type*) [Field K] [NumberField K] (w₀ : InfinitePlace K)
    {w : InfinitePlace K} (h : w ≠ w₀) (c : ℝˣ) :
    archSec K w₀ c (Place.ofInfinite w) = 1 := by
  classical
  rw [archSec_infinite, archSecVal]
  exact dif_neg h

theorem archSec_mem_archUnitIdele (K : Type*) [Field K] [NumberField K] (w₀ : InfinitePlace K)
    (c : ℝˣ) : archSec K w₀ c ∈ archUnitIdele K := by
  intro w
  by_cases h : w = w₀
  · rw [h, archSec_self]
    exact localSec_mem K w₀ c
  · rw [archSec_of_ne K w₀ h]
    exact Subgroup.one_mem _

theorem archSec_mem_archCompIdele (K : Type*) [Field K] [NumberField K] (w₀ : InfinitePlace K)
    (c : ℝˣ) : archSec K w₀ c ∈ archCompIdele K :=
  ⟨fun q => archSec_finite K w₀ c q, archSec_mem_archUnitIdele K w₀ c⟩

/-- The content of the idèle section is the prescribed positive unit. -/
theorem abs_archSec (K : Type*) [Field K] [NumberField K] (w₀ : InfinitePlace K) {c : ℝˣ}
    (hc : 0 < (c : ℝ)) : Idele.abs K (archSec K w₀ c) = c := by
  classical
  have hsingle : ∀ v : Place K, v ≠ Place.ofInfinite w₀ →
      Idele.localAbs K v (archSec K w₀ c v) = 1 := by
    intro v hv
    rcases v with w | q
    · rw [archSec_infinite]
      by_cases h : w = w₀
      · exact absurd (by rw [h]) hv
      · rw [archSecVal, dif_neg h, Idele.localAbs_ofInfinite]
        simp
    · rw [archSec_finite K w₀ c q, Idele.localAbs_ofFinite]
      simp
  rw [Idele.abs_apply, finprod_eq_single _ (Place.ofInfinite w₀) hsingle, archSec_self]
  exact localSec_localAbs K w₀ c hc

theorem archSec_one (K : Type*) [Field K] [NumberField K] (w₀ : InfinitePlace K) :
    archSec K w₀ 1 = 1 := by
  ext v
  rcases v with w | q
  · rw [archSec_infinite]
    by_cases h : w = w₀
    · classical
      rw [h, show archSecVal K w₀ 1 w₀ = localSec K w₀ 1 from by simp [archSecVal],
        localSec_one]
      rfl
    · rw [archSecVal, dif_neg h]
      rfl
  · rw [archSec_finite K w₀ 1 q]
    rfl

/-- The section is multiplicative on positive units. -/
theorem archSec_mul (K : Type*) [Field K] [NumberField K] (w₀ : InfinitePlace K) {c c' : ℝˣ}
    (hc : 0 < (c : ℝ)) (hc' : 0 < (c' : ℝ)) :
    archSec K w₀ (c * c') = archSec K w₀ c * archSec K w₀ c' := by
  ext v
  rcases v with w | q
  · rw [archSec_infinite, Idele.mul_apply, archSec_infinite, archSec_infinite]
    by_cases h : w = w₀
    · classical
      rw [h, show archSecVal K w₀ (c * c') w₀ = localSec K w₀ (c * c') from by simp [archSecVal],
        show archSecVal K w₀ c w₀ = localSec K w₀ c from by simp [archSecVal],
        show archSecVal K w₀ c' w₀ = localSec K w₀ c' from by simp [archSecVal],
        localSec_mul K w₀ c c' hc hc']
    · rw [archSecVal, dif_neg h, archSecVal, dif_neg h, archSecVal, dif_neg h, one_mul]
  · rw [archSec_finite K w₀ (c * c') q, Idele.mul_apply, archSec_finite K w₀ c q,
      archSec_finite K w₀ c' q, mul_one]

/-- The section of a power is the power of the section. -/
theorem archSec_pow (K : Type*) [Field K] [NumberField K] (w₀ : InfinitePlace K) (c : ℝˣ)
    (hc : 0 < (c : ℝ)) (n : ℕ) : archSec K w₀ (c ^ n) = (archSec K w₀ c) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, archSec_one]
  | succ m ih =>
      have hcm : 0 < ((c ^ m : ℝˣ) : ℝ) := by
        rw [Units.val_pow_eq_pow_val]
        exact pow_pos hc m
      rw [pow_succ, archSec_mul K w₀ hcm hc, ih, pow_succ]

/-! ## Continuity -/

theorem continuous_archPlaceIdele (K : Type*) [Field K] [NumberField K] :
    Continuous (fun b : (w : InfinitePlace K) → (w.Completion)ˣ => archPlaceIdele K b) := by
  have hemb := RestrictedProduct.isOpenEmbedding_structureMap
    (R := fun v : Place K => (Place.localField K v)ˣ)
    (A := fun v : Place K => ↑(Place.localUnits K v))
    (fun v => Place.isOpen_localUnits v)
  have hval : Continuous (fun b : (w : InfinitePlace K) → (w.Completion)ˣ => archPlaceVal K b) := by
    refine continuous_pi fun v => ?_
    rcases v with w | q
    · exact (continuous_apply w).subtype_mk fun _ => Subgroup.mem_top _
    · exact continuous_const
  exact hemb.isEmbedding.continuous.comp hval

theorem continuous_archSec (K : Type*) [Field K] [NumberField K] (w₀ : InfinitePlace K) :
    Continuous (fun c : ℝˣ => archSec K w₀ c) := by
  have hval : Continuous (fun c : ℝˣ => archSecVal K w₀ c) := by
    refine continuous_pi fun w => ?_
    by_cases h : w = w₀
    · classical
      rw [h]
      have hfun : (fun c : ℝˣ => archSecVal K w₀ c w₀) = fun c => localSec K w₀ c := by
        funext c
        simp [archSecVal]
      rw [hfun]
      exact localSec_continuous K w₀
    · have hfun : (fun c : ℝˣ => archSecVal K w₀ c w) = fun _ => (1 : (w.Completion)ˣ) := by
        funext c
        simp [archSecVal, h]
      rw [hfun]
      exact continuous_const
  exact (continuous_archPlaceIdele K).comp hval

/-- **The class of the section at a positive content lies in the identity component of `C_K`.** -/
theorem mk_archSec_mem_connectedComponentOfOne (K : Type*) [Field K] [NumberField K]
    (w₀ : InfinitePlace K) (c : ℝˣ) (hc : 0 < (c : ℝ)) :
    IdeleClassGroup.mk K (archSec K w₀ c) ∈
      Subgroup.connectedComponentOfOne (IdeleClassGroup K) := by
  classical
  haveI hpc : PreconnectedSpace (Set.Ioi (0 : ℝ)) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioi
  have hu : Continuous fun y : Set.Ioi (0 : ℝ) => Units.mk0 (y : ℝ) (ne_of_gt (Set.mem_Ioi.mp y.2)) :=
    Units.isEmbedding_val₀.continuous_iff.mpr continuous_subtype_val
  have hFcont : Continuous fun y : Set.Ioi (0 : ℝ) =>
      IdeleClassGroup.mk K (archSec K w₀ (Units.mk0 (y : ℝ) (ne_of_gt (Set.mem_Ioi.mp y.2)))) :=
    (QuotientGroup.continuous_mk (N := Idele.principalSubgroup K)).comp
      ((continuous_archSec K w₀).comp hu)
  have hpre : IsPreconnected (Set.range fun y : Set.Ioi (0 : ℝ) =>
      IdeleClassGroup.mk K (archSec K w₀ (Units.mk0 (y : ℝ) (ne_of_gt (Set.mem_Ioi.mp y.2))))) :=
    isPreconnected_range hFcont
  have h1 : (1 : IdeleClassGroup K) ∈ Set.range fun y : Set.Ioi (0 : ℝ) =>
      IdeleClassGroup.mk K (archSec K w₀ (Units.mk0 (y : ℝ) (ne_of_gt (Set.mem_Ioi.mp y.2)))) := by
    refine ⟨⟨1, by norm_num⟩, ?_⟩
    show IdeleClassGroup.mk K (archSec K w₀ (Units.mk0 ((1 : ℝ)) (by norm_num))) = 1
    rw [show Units.mk0 ((1 : ℝ)) (ne_of_gt (by norm_num : (0:ℝ) < 1)) = 1 from Units.ext rfl,
      archSec_one, map_one]
  have hmem : IdeleClassGroup.mk K (archSec K w₀ c) ∈ Set.range fun y : Set.Ioi (0 : ℝ) =>
      IdeleClassGroup.mk K (archSec K w₀ (Units.mk0 (y : ℝ) (ne_of_gt (Set.mem_Ioi.mp y.2)))) := by
    refine ⟨⟨(c : ℝ), hc⟩, ?_⟩
    show IdeleClassGroup.mk K (archSec K w₀ (Units.mk0 ((c : ℝ)) (ne_of_gt hc))) = _
    rw [show Units.mk0 ((c : ℝ)) (ne_of_gt hc) = c from Units.ext rfl]
  exact hpre.subset_connectedComponent h1 hmem

end Work.SSGRoute.PTW
