import Mathlib
import Submission.Work.Serre.RangeOne.towerDefs
import Submission.Work.Serre.RangeOne.towerCompact
import Submission.Work.Serre.RangeOne.towerCompress
import Submission.Work.Serre.RangeOne.rangeWhitehead
import Submission.Work.Serre.RangeOne.piMap_bijective_of_compress
import Submission.Work.Serre.serrePostnikovTower
import Submission.Work.RatHurewicz.towerStepData
import Submission.Work.Serre.AttachCompress.Assemble
import Submission.Work.Serre.attachIncl_piMap_bijective_of_compress

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The homotopy groups of the colimit of the truncation tower

With `Z` the colimit of the tower `chain W w₀` (`Work.Serre.RangeOne.towerDefs`) and
`pt = ι 0 (wK w₀)`, this file computes:

* `Z` is connected (`subsingleton_zerothHomotopy_colim`) and `π₀(Z,pt)` is a singleton;
* `πᵢ(Z,pt) = 0` for `i ≥ 2` (`subsingleton_pi_of_two_le`) — the stagewise killing
  `Work.RatHurewicz.TowerState.killed` transported through the π-isomorphism of the stage inclusion;
* `π₁(Z,pt) ≅ π₁(W,w₀)` (`piOneMulEquiv`);
* the inclusion `inclChain : W → Z` is a `πᵢ`-bijection at *every* base point for `i ≤ N`
  (`bijective_piMapN`), which is the input of `Work.Serre.RangeModelComparison`.
-/

open scoped Topology

namespace Work.Serre.RangeOne

open Work.RatHurewicz

noncomputable section

variable {W : Type} [TopologicalSpace W] {w₀ : W}

/-! ## Elementary transport lemmas -/

/-- A topological space all of whose `π₀` classes are equal is path connected. -/
theorem joined_of_subsingleton_pi0 {X : Type} [TopologicalSpace X] {x : X}
    (h : Subsingleton (HomotopyGroup (Fin 0) X x)) (y : X) : Joined x y := by
  have hZ : Subsingleton (ZerothHomotopy X) :=
    (HomotopyGroup.pi0EquivZerothHomotopy (x := x)).surjective.subsingleton
  have h1 : ZerothHomotopy.mk x = ZerothHomotopy.mk y := Subsingleton.elim _ _
  show Joined x y
  exact Quotient.exact h1

/-- The unshifted index `piMapN` agrees with the shifted `πmap`. -/
theorem piMapN_succ_eq_piMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) (x : X) :
    Work.Serre.piMapN f (n + 1) x = Work.StemsB.πmap f n x := rfl

/-- Triviality of `π₀` at one point gives triviality at every point. -/
theorem subsingleton_pi_zero_of {X : Type} [TopologicalSpace X] {x y : X}
    (hx : Subsingleton (HomotopyGroup (Fin 0) X x)) :
    Subsingleton (HomotopyGroup (Fin 0) X y) := by
  haveI : Subsingleton (ZerothHomotopy X) :=
    (HomotopyGroup.pi0EquivZerothHomotopy (x := x)).surjective.subsingleton
  exact (HomotopyGroup.pi0EquivZerothHomotopy (x := y)).injective.subsingleton

/-- Triviality of `πᵢ` transports along a path (for `i ≥ 1`). -/
theorem subsingleton_homotopyGroup_of_joined' {X : Type} [TopologicalSpace X] {x y : X}
    (h : Joined x y) (i : ℕ) (hi : 1 ≤ i) (hx : Subsingleton (HomotopyGroup (Fin i) X x)) :
    Subsingleton (HomotopyGroup (Fin i) X y) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  exact Work.Serre.subsingleton_homotopyGroup_of_joined h k hx

/-- Every homotopy group is inhabited (by the class of the constant cube). -/
theorem nonempty_homotopyGroup (i : ℕ) (X : Type) [TopologicalSpace X] (x : X) :
    Nonempty (HomotopyGroup (Fin i) X x) :=
  ⟨⟦(GenLoop.const : GenLoop (Fin i) X x)⟧⟩

/-- A map between subsingletons with inhabited domain is bijective. -/
theorem bijective_of_subsingleton {α β : Type*} [Subsingleton α] [Subsingleton β] (f : α → β)
    (a : α) : Function.Bijective f :=
  ⟨fun x y _ => Subsingleton.elim x y, fun b => ⟨a, Subsingleton.elim (f a) b⟩⟩

/-! ## The colimit -/

/-- The inclusion of `W` into the colimit of the tower. -/
def inclChain (W : Type) [TopologicalSpace W] (w₀ : W) : C(W, (chain W w₀).Z) where
  toFun x := (chain W w₀).iota 0 (inclK W w₀ x)
  continuous_toFun := ((chain W w₀).continuous_iota 0).comp (inclK W w₀).continuous

/-- The base point of the colimit. -/
def pt (w₀ : W) : (chain W w₀).Z := (chain W w₀).iota 0 (wK w₀)

theorem inclChain_apply (x : W) : inclChain W w₀ x = (chain W w₀).iota 0 (inclK W w₀ x) := rfl

@[simp] theorem inclChain_apply_w₀ : inclChain W w₀ w₀ = pt w₀ := rfl

/-- The compression property of the colimit in dimensions `≤ 3`, for the first stage. -/
theorem compressRel_colim_zero (W : Type) [TopologicalSpace W] (w₀ : W) (d : ℕ) (hd : d ≤ 3) :
    CompressRel ((chain W w₀).Z) (Set.range ((chain W w₀).iota 0)) d :=
  compressRel_colim_chain W w₀ 0 d (by omega)

/-! ## Connectedness -/

/-- The pre-kill of `π₂` preserves connectedness. -/
theorem preKill_connected (h0 : Subsingleton (HomotopyGroup (Fin 0) W w₀)) :
    Subsingleton (ZerothHomotopy (preKill W w₀)) := by
  have h0' : Subsingleton (ZerothHomotopy W) :=
    (HomotopyGroup.pi0EquivZerothHomotopy (x := w₀)).surjective.subsingleton
  have hA : Subsingleton (ZerothHomotopy ↥(Set.range (inclK W w₀))) :=
    subsingleton_zerothHomotopy_of_homotopyEquiv
      (rangeHomeo 1 W (HomotopyGroup (Fin 2) W w₀) (killFamily 1 W w₀)).symm.toHomotopyEquiv h0'
  exact subsingleton_zerothHomotopy_of_compressRel_zero
    (compressRel_attachCells_range 1 W (HomotopyGroup (Fin 2) W w₀) (killFamily 1 W w₀) 0
      (by norm_num)) hA

/-- The colimit of the tower is connected. -/
theorem subsingleton_zerothHomotopy_colim (h0 : Subsingleton (HomotopyGroup (Fin 0) W w₀)) :
    Subsingleton (ZerothHomotopy (chain W w₀).Z) := by
  have hX : Subsingleton (ZerothHomotopy ((chain W w₀).X 0)) :=
    preKill_connected (W := W) (w₀ := w₀) h0
  have hA : Subsingleton (ZerothHomotopy ↥(Set.range ((chain W w₀).iota 0))) :=
    subsingleton_zerothHomotopy_of_homotopyEquiv
      (((chain W w₀).isEmbedding_iota 0).toHomeomorph).symm.toHomotopyEquiv hX
  exact subsingleton_zerothHomotopy_of_compressRel_zero
    (compressRel_colim_zero W w₀ 0 (by norm_num)) hA

/-- `π₀` of the colimit at the base point is trivial. -/
theorem subsingleton_pi_zero (h0 : Subsingleton (HomotopyGroup (Fin 0) W w₀)) :
    Subsingleton (HomotopyGroup (Fin 0) (chain W w₀).Z (pt w₀)) := by
  haveI := subsingleton_zerothHomotopy_colim (W := W) (w₀ := w₀) h0
  exact (HomotopyGroup.pi0EquivZerothHomotopy (x := pt w₀)).injective.subsingleton

/-! ## The second homotopy group of the colimit vanishes -/

/-- **`π₂(Z,pt) = 0`**, using the fact that `π₂` is already killed at the first stage. -/
theorem subsingleton_pi_two :
    Subsingleton (HomotopyGroup (Fin 2) (chain W w₀).Z (pt w₀)) := by
  have hcomp : ∀ d ≤ 3, CompressRel ((chain W w₀).Z)
      (Set.range ((chain W w₀).iota 0)) d :=
    fun d hd => compressRel_colim_zero W w₀ d hd
  have hpt : pt w₀ ∈ Set.range ((chain W w₀).iota 0) := ⟨wK w₀, rfl⟩
  let a₀ : ↥(Set.range ((chain W w₀).iota 0)) := ⟨pt w₀, hpt⟩
  have hbij := bijective_πmap_setIncl_of_compressRel
    (A := Set.range ((chain W w₀).iota 0)) a₀ 3 hcomp 1 (by norm_num)
  have hk : Subsingleton (HomotopyGroup (Fin 2) ((chain W w₀).X 0) (wK w₀)) := preKill_kills
  have hbase : (((chain W w₀).isEmbedding_iota 0).toHomeomorph) (wK w₀) = a₀ :=
    Subtype.ext rfl
  have hhom : Subsingleton (HomotopyGroup (Fin 2)
      (↥(Set.range ((chain W w₀).iota 0))) a₀) := by
    have h := subsingleton_homotopyGroup_of_homeo
      (((chain W w₀).isEmbedding_iota 0).toHomeomorph) (wK w₀) 2 hk
    rwa [hbase] at h
  haveI := hhom
  exact hbij.surjective.subsingleton

/-- **`πᵢ(Z,pt) = 0` for `i ≥ 2`.** -/
theorem subsingleton_pi_of_two_le (i : ℕ) (hi : 2 ≤ i) :
    Subsingleton (HomotopyGroup (Fin i) (chain W w₀).Z (pt w₀)) := by
  rcases i with _ | _ | k
  · exfalso; omega
  · exfalso; omega
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      exact subsingleton_pi_two (W := W) (w₀ := w₀)
    · have hcomp : ∀ d ≤ (k + 1) + 3, CompressRel ((chain W w₀).Z)
          (Set.range ((chain W w₀).iota (k + 1))) d :=
        fun d hd => compressRel_colim_chain W w₀ (k + 1) d hd
      have hpt : pt w₀ ∈ Set.range ((chain W w₀).iota (k + 1)) :=
        ⟨(chain W w₀).upAt 0 (k + 1) (Nat.zero_le _) (wK w₀), by
          rw [← (chain W w₀).iota_compat (Nat.zero_le _) (wK w₀)]
          rfl⟩
      let a₀ : ↥(Set.range ((chain W w₀).iota (k + 1))) := ⟨pt w₀, hpt⟩
      have harith : k + 1 + 2 ≤ (k + 1) + 3 := by omega
      have hbij := bijective_πmap_setIncl_of_compressRel
        (A := Set.range ((chain W w₀).iota (k + 1))) a₀ ((k + 1) + 3) hcomp (k + 1) harith
      have hkilled : Subsingleton (HomotopyGroup (Fin (k + 2)) ((chain W w₀).X (k + 1))
          ((St W w₀ (k + 1)).incl (wK w₀))) :=
        (St W w₀ (k + 1)).killed (k + 2) (by omega : 2 < k + 2)
          (by omega : k + 2 ≤ 2 + (k + 1))
      have hbase : (((chain W w₀).isEmbedding_iota (k + 1)).toHomeomorph)
          ((St W w₀ (k + 1)).incl (wK w₀)) = a₀ := by
        refine Subtype.ext ?_
        show (chain W w₀).iota (k + 1) ((St W w₀ (k + 1)).incl (wK w₀)) = pt w₀
        rw [incl_apply_eq_upAt (k + 1) (wK w₀)]
        exact ((chain W w₀).iota_compat (Nat.zero_le (k + 1)) (wK w₀)).symm
      have hhom : Subsingleton (HomotopyGroup (Fin ((k + 1) + 1))
          (↥(Set.range ((chain W w₀).iota (k + 1)))) a₀) := by
        have h := subsingleton_homotopyGroup_of_homeo
          (((chain W w₀).isEmbedding_iota (k + 1)).toHomeomorph)
          ((St W w₀ (k + 1)).incl (wK w₀)) ((k + 1) + 1) hkilled
        rwa [hbase] at h
      haveI := hhom
      exact hbij.surjective.subsingleton

/-! ## `π₁` of the colimit -/

/-- The inclusion of the first stage into the colimit, as a continuous map. -/
def iotaZero (W : Type) [TopologicalSpace W] (w₀ : W) :
    C((chain W w₀).X 0, (chain W w₀).Z) :=
  ⟨(chain W w₀).iota 0, (chain W w₀).continuous_iota 0⟩

theorem iotaZero_apply (Y : (chain W w₀).X 0) : iotaZero W w₀ Y = (chain W w₀).iota 0 Y := rfl

/-- The inclusion `W → Z` induces a bijection on `π₁` at every base point. -/
theorem piOne_bijective (x : W) :
    Function.Bijective (Work.Serre.piMapN (inclChain W w₀) 1 x) := by
  have hcomp : ∀ d ≤ 3, CompressRel ((chain W w₀).Z)
      (Set.range ((chain W w₀).iota 0)) d :=
    fun d hd => compressRel_colim_zero W w₀ d hd
  have hcomp' : ∀ d ≤ 3, CompressRel ((chain W w₀).Z)
      (Set.range (⇑(iotaZero W w₀))) d := hcomp
  have hf : Topology.IsEmbedding ⇑(iotaZero W w₀) := (chain W w₀).isEmbedding_iota 0
  have h1 : ∀ j : ℕ, j + 2 ≤ 3 → ∀ y : (chain W w₀).X 0,
      Function.Bijective (Work.StemsB.πmap (iotaZero W w₀) j y) :=
    piMap_bijective_of_compress (iotaZero W w₀) hf 3 hcomp'
  have h1x : Function.Bijective
      (Work.StemsB.πmap (iotaZero W w₀) 0 (inclK W w₀ x)) :=
    h1 0 (by norm_num) (inclK W w₀ x)
  have h2 : Function.Bijective (Work.StemsB.πmap (inclK W w₀) 0 x) := preKill_piMap x
  have hcomp2 : (fun a : HomotopyGroup (Fin 1) W x =>
        Work.StemsB.πmap (inclChain W w₀) 0 x a)
      = fun a => Work.StemsB.πmap (iotaZero W w₀) 0 (inclK W w₀ x)
          (Work.StemsB.πmap (inclK W w₀) 0 x a) := by
    funext a
    exact Work.StemsB.πmap_comp_apply (inclK W w₀) (iotaZero W w₀) 0 x a
  rw [piMapN_succ_eq_piMap (inclChain W w₀) 0 x]
  show Function.Bijective (fun a : HomotopyGroup (Fin 1) W x =>
    Work.StemsB.πmap (inclChain W w₀) 0 x a)
  rw [hcomp2]
  exact h1x.comp h2

/-- **`π₁` of the colimit is `π₁(W,w₀)`.** -/
theorem piOneMulEquiv (w₀ : W) :
    Nonempty (HomotopyGroup (Fin 1) (chain W w₀).Z (pt w₀) ≃*
      HomotopyGroup (Fin 1) W w₀) := by
  letI : Group (HomotopyGroup (Fin 1) W w₀) := HomotopyGroup.group (Fin 1)
  letI : Group (HomotopyGroup (Fin 1) (chain W w₀).Z (pt w₀)) := HomotopyGroup.group (Fin 1)
  letI : Group (HomotopyGroup (Fin 1) (chain W w₀).Z (inclChain W w₀ w₀)) :=
    HomotopyGroup.group (Fin 1)
  obtain ⟨F, hF⟩ := Work.Serre.piMapN_monoidHom (inclChain W w₀) 1 w₀
  have hbij : Function.Bijective F := by
    have h : Function.Bijective (Work.Serre.piMapN (inclChain W w₀) 1 w₀) :=
      piOne_bijective (W := W) (w₀ := w₀) w₀
    refine ⟨fun a b hab => h.1 ?_, fun b => ?_⟩
    · rw [← hF a, ← hF b]
      exact hab
    · obtain ⟨a, ha⟩ := h.2 b
      exact ⟨a, by rw [hF a]; exact ha⟩
  exact ⟨(MulEquiv.ofBijective F hbij).symm⟩

/-! ## The `πᵢ`-bijectivity of the inclusion -/

/-- **The inclusion `W → Z` is a `πᵢ`-bijection at every base point for `i ≤ N`.** -/
theorem bijective_piMapN (N : ℕ) (h0 : Subsingleton (HomotopyGroup (Fin 0) W w₀))
    (hvan : ∀ i : ℕ, 2 ≤ i → i ≤ N → Subsingleton (HomotopyGroup (Fin i) W w₀))
    (i : ℕ) (hiN : i ≤ N) (x : W) :
    Function.Bijective (Work.Serre.piMapN (inclChain W w₀) i x) := by
  rcases Nat.eq_zero_or_pos i with h0i | hpos
  · subst h0i
    haveI hW : Subsingleton (HomotopyGroup (Fin 0) W x) := subsingleton_pi_zero_of (X := W) h0
    haveI hZ : Subsingleton (HomotopyGroup (Fin 0) (chain W w₀).Z (inclChain W w₀ x)) :=
      subsingleton_pi_zero_of (X := (chain W w₀).Z)
        (subsingleton_pi_zero (W := W) (w₀ := w₀) h0)
    exact bijective_of_subsingleton _ (nonempty_homotopyGroup 0 W x).some
  · rcases eq_or_lt_of_le (show 1 ≤ i from hpos) with h1 | h2
    · subst h1
      exact piOne_bijective (W := W) (w₀ := w₀) x
    · have hi2 : 2 ≤ i := h2
      haveI hW : Subsingleton (HomotopyGroup (Fin i) W x) :=
        subsingleton_homotopyGroup_of_joined' (joined_of_subsingleton_pi0 h0 x) i
          (by omega) (hvan i hi2 hiN)
      haveI hZ : Subsingleton (HomotopyGroup (Fin i) (chain W w₀).Z (inclChain W w₀ x)) :=
        subsingleton_homotopyGroup_of_joined'
          (joined_of_subsingleton_pi0 (subsingleton_pi_zero (W := W) (w₀ := w₀) h0)
            (inclChain W w₀ x)) i (by omega)
          (subsingleton_pi_of_two_le (W := W) (w₀ := w₀) i hi2)
      exact bijective_of_subsingleton _ (nonempty_homotopyGroup i W x).some

end

end Work.Serre.RangeOne
