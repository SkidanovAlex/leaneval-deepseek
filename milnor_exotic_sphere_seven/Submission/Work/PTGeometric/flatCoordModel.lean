import Submission.Work.PTGeometric.flatCoordAux
import Submission.Work.PTGeometric.genLoopListConcat_eq_block
import Submission.Work.PTGeometric.genLoopListConcat_eq_basepoint_of_wall

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the local smooth model of the coordinate field on the collar

The collar identity (`Work.PTGeometric.flatSourceHomotopy8_eq_collapse`) exhibits the flat source
homotopy on `{x 0 ≤ 1/2}` as the explicit concatenation `alphaFamily` of the pieces' collapse loops,
read at the cube coordinates `collPt` of the source.  The concatenation is a two-level dyadic
concatenation, and on the interior of a dyadic block it reads one piece's collapse at an *affine*
reparametrisation of the cube point: this is the block formula
(`Work.PTGeometric.genLoopListConcat_eq_block`), whose two hypotheses
(`1 < 2 ^ (d+1) * t i` and `2 ^ d * t i < 1`) say exactly that the cube point lies in the *open*
`d`-th dyadic block.

Consequently, near a point `y₀` whose value is not the base point, the coordinate reading of the
field is TUBULAR's tube data (`tubeNormalProj`, `tubeNormalCoord`, which are `C^∞` on the open tube)
applied to an *ordinary* smooth function of `y`: the tube point is the affine expression
`2 ^ (d+1) (t i) - 1` on the two concatenation coordinates and the cube coordinate elsewhere.

This file builds that local model.  The two hypotheses of the model are the block conditions in the
two levels and the tube membership; the block formula and the tube identity then identify the
coordinate field with the model on the set where they hold.

## Main results

* `Work.PTGeometric.upd`, `Work.PTGeometric.collPt`
* `Work.PTGeometric.modelPoint`, `Work.PTGeometric.modelEuc`, `Work.PTGeometric.contMDiff_modelEuc`
* `Work.PTGeometric.clipPt_eq_modelPoint`
* `Work.PTGeometric.alphaFamily_eq_collapse_of_block`
* `Work.PTGeometric.coord_eq_model`
* `Work.PTGeometric.exists_local_smooth_model`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology unitInterval
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom

variable {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι] {Fam : ι → Man8}

/-! ## The two concatenation coordinates of the cube `Fin (k+8)` -/

/-- The first concatenation coordinate (`Fin (k+8)`, so that two coordinates are available). -/
def cZero (k : ℕ) : Fin (k + 8) := ⟨0, by omega⟩

/-- The second concatenation coordinate. -/
def cOne (k : ℕ) : Fin (k + 8) := ⟨1, by omega⟩

theorem cZero_ne_cOne (k : ℕ) : cZero k ≠ cOne k := by simp [cZero, cOne]

/-! ## The block reparametrisation as a total function of the cube point -/

/-- The `d`-th block reparametrisation along the coordinate `i`, as a total function of the cube
point: the coordinate `i` is sent to the affine expression `2 ^ (d+1) t i - 1`, *clipped* to the
unit interval (so that the map is total and continuous); on the open `d`-th dyadic block the
clipping is inactive and the reparametrisation is the affine map of the block formula. -/
def upd {N : Type*} [DecidableEq N] (i : N) (d : ℕ) (t : N → Set.Icc (0 : ℝ) 1) :
    N → Set.Icc (0 : ℝ) 1 :=
  Function.update t i (ptProj ((2 : ℝ) ^ (d + 1) * (t i : ℝ) - 1))

theorem upd_apply_coe {N : Type*} [DecidableEq N] (i : N) (d : ℕ)
    (t : N → Set.Icc (0 : ℝ) 1) (m : N) :
    ((upd i d t m : Set.Icc (0 : ℝ) 1) : ℝ)
      = if m = i then max 0 (min 1 ((2 : ℝ) ^ (d + 1) * (t i : ℝ) - 1)) else (t m : ℝ) := by
  rw [upd, Function.update_apply]
  split
  · rw [ptProj_coe]
  · rfl

theorem upd_apply_of_ne {N : Type*} [DecidableEq N] (i : N) (d : ℕ)
    (t : N → Set.Icc (0 : ℝ) 1) {m : N} (hm : m ≠ i) :
    ((upd i d t m : Set.Icc (0 : ℝ) 1) : ℝ) = (t m : ℝ) := by
  rw [upd_apply_coe, if_neg hm]

/-- The block reparametrisation of `Work.PTGeometric.blockPt` is the total one. -/
theorem blockPt_eq_upd {N : Type*} [DecidableEq N] (i : N) (d : ℕ)
    (t : N → Set.Icc (0 : ℝ) 1) (hlo : 1 < (2 : ℝ) ^ (d + 1) * (t i : ℝ))
    (hhi : (2 : ℝ) ^ d * (t i : ℝ) < 1) :
    blockPt i d t hlo hhi = upd i d t := rfl

theorem max_min_eq_of_mem {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) : max 0 (min 1 v) = v := by
  rw [min_eq_right h1, max_eq_right h0]

/-! ## The clipped and unclipped block points of the two-level concatenation -/

/-- The outer block point: the `k₀`-th block of the concatenation along the coordinate `i₀`. -/
def outerPt (k : ℕ) (i₀ : Fin (k + 8)) (k₀ : ℕ)
    (y : EuclideanSpace ℝ (Fin ((8 + k) + 1))) : Fin (k + 8) → Set.Icc (0 : ℝ) 1 :=
  upd i₀ k₀ (collPt k y)

/-- The full block point of the two-level concatenation: the `j₀`-th sub-block of the `k₀`-th block,
along the coordinate `i₁`. -/
def clipPt (k : ℕ) (i₀ i₁ : Fin (k + 8)) (k₀ j₀ : ℕ)
    (y : EuclideanSpace ℝ (Fin ((8 + k) + 1))) : Fin (k + 8) → Set.Icc (0 : ℝ) 1 :=
  upd i₁ j₀ (outerPt k i₀ k₀ y)

theorem outerPt_apply_coe (i₀ : Fin (k + 8)) (k₀ : ℕ)
    (y : EuclideanSpace ℝ (Fin ((8 + k) + 1))) (m : Fin (k + 8)) :
    ((outerPt k i₀ k₀ y m : Set.Icc (0 : ℝ) 1) : ℝ)
      = if m = i₀ then max 0 (min 1 ((2 : ℝ) ^ (k₀ + 1) * ((collPt k y i₀ : Set.Icc (0 : ℝ) 1) : ℝ) - 1))
        else ((collPt k y m : Set.Icc (0 : ℝ) 1) : ℝ) :=
  upd_apply_coe i₀ k₀ (collPt k y) m

theorem outerPt_apply_of_ne (k₀ : ℕ) (y : EuclideanSpace ℝ (Fin ((8 + k) + 1)))
    {i₀ : Fin (k + 8)} (m : Fin (k + 8)) (hm : m ≠ i₀) :
    ((outerPt k i₀ k₀ y m : Set.Icc (0 : ℝ) 1) : ℝ)
      = ((collPt k y m : Set.Icc (0 : ℝ) 1) : ℝ) :=
  upd_apply_of_ne i₀ k₀ (collPt k y) hm

theorem clipPt_apply_coe (i₀ i₁ : Fin (k + 8)) (k₀ j₀ : ℕ)
    (y : EuclideanSpace ℝ (Fin ((8 + k) + 1))) (m : Fin (k + 8)) :
    ((clipPt k i₀ i₁ k₀ j₀ y m : Set.Icc (0 : ℝ) 1) : ℝ)
      = if m = i₁ then max 0 (min 1 ((2 : ℝ) ^ (j₀ + 1) * ((outerPt k i₀ k₀ y i₁ : Set.Icc (0 : ℝ) 1) : ℝ) - 1))
        else ((outerPt k i₀ k₀ y m : Set.Icc (0 : ℝ) 1) : ℝ) :=
  upd_apply_coe i₁ j₀ (outerPt k i₀ k₀ y) m

theorem clipPt_apply_of_ne (i₀ : Fin (k + 8)) (k₀ j₀ : ℕ)
    (y : EuclideanSpace ℝ (Fin ((8 + k) + 1))) {i₁ : Fin (k + 8)} (m : Fin (k + 8))
    (hm : m ≠ i₁) :
    ((clipPt k i₀ i₁ k₀ j₀ y m : Set.Icc (0 : ℝ) 1) : ℝ)
      = ((outerPt k i₀ k₀ y m : Set.Icc (0 : ℝ) 1) : ℝ) :=
  upd_apply_of_ne i₁ j₀ (outerPt k i₀ k₀ y) hm

/-! ## The unclipped model point and the tube point -/

/-- **The (unclipped) model cube point**: the affine block reparametrisation of the collar cube
point, as a real-valued function.  Its smoothness is the whole point: the clipping of
`Work.PTGeometric.clipPt` is inactive exactly when the cube point lies in the open dyadic block, and
there the two agree. -/
def modelPoint (k : ℕ) (i₀ i₁ : Fin (k + 8)) (k₀ j₀ : ℕ)
    (y : EuclideanSpace ℝ (Fin ((8 + k) + 1))) : Fin (k + 8) → ℝ :=
  fun m =>
    if m = i₀ then (2 : ℝ) ^ (k₀ + 1) * ((collPt k y i₀ : Set.Icc (0 : ℝ) 1) : ℝ) - 1
    else if m = i₁ then (2 : ℝ) ^ (j₀ + 1) * ((collPt k y i₁ : Set.Icc (0 : ℝ) 1) : ℝ) - 1
    else ((collPt k y m : Set.Icc (0 : ℝ) 1) : ℝ)

theorem modelPoint_apply (i₀ i₁ : Fin (k + 8)) (k₀ j₀ : ℕ)
    (y : EuclideanSpace ℝ (Fin ((8 + k) + 1))) (m : Fin (k + 8)) :
    modelPoint k i₀ i₁ k₀ j₀ y m =
      (if m = i₀ then (2 : ℝ) ^ (k₀ + 1) * ((collPt k y i₀ : Set.Icc (0 : ℝ) 1) : ℝ) - 1
       else if m = i₁ then (2 : ℝ) ^ (j₀ + 1) * ((collPt k y i₁ : Set.Icc (0 : ℝ) 1) : ℝ) - 1
       else ((collPt k y m : Set.Icc (0 : ℝ) 1) : ℝ)) := rfl

/-- The tube point of the model: the cube point read through the affine realisation of the cube of
radius `G.R` and the reindexing `finKRInv`. -/
def modelEuc (G : GenuineTubeGeometry k D ι Fam) (i₀ i₁ : Fin (k + 8)) (k₀ j₀ : ℕ)
    (y : EuclideanSpace ℝ (Fin ((8 + k) + 1))) : EuclideanSpace ℝ (Fin (8 + k)) :=
  eucOfReal (8 + k) G.R (fun l => modelPoint k i₀ i₁ k₀ j₀ y (finKRInv k l))

theorem modelPoint_contMDiff (i₀ i₁ : Fin (k + 8)) (k₀ j₀ : ℕ) (m : Fin (k + 8)) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin ((8 + k) + 1))) 𝓘(ℝ, ℝ) ∞
      (fun y => modelPoint k i₀ i₁ k₀ j₀ y m) := by
  by_cases h1 : m = i₀
  · rw [show (fun y => modelPoint k i₀ i₁ k₀ j₀ y m)
        = fun y => (2 : ℝ) ^ (k₀ + 1) * ((collPt k y i₀ : Set.Icc (0 : ℝ) 1) : ℝ) - 1 from
      funext fun y => by rw [modelPoint_apply, if_pos h1]]
    exact (contMDiff_const.mul (contMDiff_collPt_apply k i₀)).sub_const 1
  · by_cases h2 : m = i₁
    · rw [show (fun y => modelPoint k i₀ i₁ k₀ j₀ y m)
          = fun y => (2 : ℝ) ^ (j₀ + 1) * ((collPt k y i₁ : Set.Icc (0 : ℝ) 1) : ℝ) - 1 from
        funext fun y => by rw [modelPoint_apply, if_neg h1, if_pos h2]]
      exact (contMDiff_const.mul (contMDiff_collPt_apply k i₁)).sub_const 1
    · rw [show (fun y => modelPoint k i₀ i₁ k₀ j₀ y m)
          = fun y => ((collPt k y m : Set.Icc (0 : ℝ) 1) : ℝ) from
        funext fun y => by rw [modelPoint_apply, if_neg h1, if_neg h2]]
      exact contMDiff_collPt_apply k m

theorem contMDiff_modelEuc (G : GenuineTubeGeometry k D ι Fam) (i₀ i₁ : Fin (k + 8))
    (k₀ j₀ : ℕ) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin ((8 + k) + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (8 + k))) ∞ (modelEuc G i₀ i₁ k₀ j₀) := by
  refine (contMDiff_eucOfReal (8 + k) G.R).comp ?_
  rw [contMDiff_pi_space]
  intro l
  exact modelPoint_contMDiff i₀ i₁ k₀ j₀ (finKRInv k l)

/-! ## The two agree on the open dyadic blocks -/

/-- **On the open dyadic blocks the clipped block point is the model point.**  This is the
arithmetic content of the block conditions: the two clips in `clipPt` are inactive. -/
theorem clipPt_eq_modelPoint (hne : cZero k ≠ cOne k) (k₀ j₀ : ℕ)
    (y : EuclideanSpace ℝ (Fin ((8 + k) + 1)))
    (hξlo : 1 < (2 : ℝ) ^ (k₀ + 1) * ((collPt k y (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ))
    (hξhi : (2 : ℝ) ^ k₀ * ((collPt k y (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1)
    (hηlo : 1 < (2 : ℝ) ^ (j₀ + 1) * ((collPt k y (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ))
    (hηhi : (2 : ℝ) ^ j₀ * ((collPt k y (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1)
    (m : Fin (k + 8)) :
    ((clipPt k (cZero k) (cOne k) k₀ j₀ y m : Set.Icc (0 : ℝ) 1) : ℝ)
      = modelPoint k (cZero k) (cOne k) k₀ j₀ y m := by
  have hξmem : (2 : ℝ) ^ (k₀ + 1) * ((collPt k y (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) - 1
      ∈ Set.Icc (0 : ℝ) 1 := by
    have hp : (2 : ℝ) ^ (k₀ + 1) = 2 * 2 ^ k₀ := by rw [pow_succ]; ring
    refine ⟨by linarith, ?_⟩
    rw [hp]; nlinarith [hξhi]
  have hηmem : (2 : ℝ) ^ (j₀ + 1) * ((collPt k y (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) - 1
      ∈ Set.Icc (0 : ℝ) 1 := by
    have hp : (2 : ℝ) ^ (j₀ + 1) = 2 * 2 ^ j₀ := by rw [pow_succ]; ring
    refine ⟨by linarith, ?_⟩
    rw [hp]; nlinarith [hηhi]
  have hξval : max 0 (min 1 ((2 : ℝ) ^ (k₀ + 1) *
      ((collPt k y (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) - 1))
      = (2 : ℝ) ^ (k₀ + 1) * ((collPt k y (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) - 1 :=
    max_min_eq_of_mem hξmem.1 hξmem.2
  have hηval : max 0 (min 1 ((2 : ℝ) ^ (j₀ + 1) *
      ((collPt k y (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) - 1))
      = (2 : ℝ) ^ (j₀ + 1) * ((collPt k y (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) - 1 :=
    max_min_eq_of_mem hηmem.1 hηmem.2
  have h01 : cOne k ≠ cZero k := Ne.symm hne
  by_cases hm1 : m = cOne k
  · have h0 : m ≠ cZero k := fun hh => hne (by rw [← hh, hm1])
    rw [modelPoint_apply, if_neg h0, if_pos hm1]
    rw [clipPt_apply_coe, if_pos hm1, outerPt_apply_of_ne k₀ y (cOne k) (Ne.symm hne), hηval]
  · by_cases hm0 : m = cZero k
    · rw [modelPoint_apply, if_pos hm0]
      rw [clipPt_apply_coe, if_neg hm1, outerPt_apply_coe, if_pos hm0, hξval]
    · rw [modelPoint_apply, if_neg hm0, if_neg hm1]
      rw [clipPt_apply_coe, if_neg hm1, outerPt_apply_of_ne k₀ y m hm0]

/-- The tube point of the model is the ordinary cube point of the clipped block point, on the open
dyadic blocks. -/
theorem modelEuc_eq_cubeToEuc (G : GenuineTubeGeometry k D ι Fam) (hne : cZero k ≠ cOne k)
    (k₀ j₀ : ℕ) (y : EuclideanSpace ℝ (Fin ((8 + k) + 1)))
    (hξlo : 1 < (2 : ℝ) ^ (k₀ + 1) * ((collPt k y (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ))
    (hξhi : (2 : ℝ) ^ k₀ * ((collPt k y (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1)
    (hηlo : 1 < (2 : ℝ) ^ (j₀ + 1) * ((collPt k y (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ))
    (hηhi : (2 : ℝ) ^ j₀ * ((collPt k y (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1) :
    modelEuc G (cZero k) (cOne k) k₀ j₀ y
      = Work.Tubular.cubeToEuc (8 + k) G.R
          (reIdx k (clipPt k (cZero k) (cOne k) k₀ j₀ y)) := by
  rw [modelEuc]
  rw [show reIdx k (clipPt k (cZero k) (cOne k) k₀ j₀ y)
      = fun l => clipPt k (cZero k) (cOne k) k₀ j₀ y (finKRInv k l) from rfl]
  rw [← eucOfReal_coll (8 + k) G.R (fun l => clipPt k (cZero k) (cOne k) k₀ j₀ y (finKRInv k l))]
  congr 1
  funext l
  exact (clipPt_eq_modelPoint hne k₀ j₀ y hξlo hξhi hηlo hηhi (finKRInv k l)).symm

/-! ## The block chain -/

/-- The outer block point in the `outerPt` form, from the `collPt` form. -/
theorem outerPt_apply_cOne (k₀ : ℕ) (y : EuclideanSpace ℝ (Fin ((8 + k) + 1))) :
    ((outerPt k (cZero k) k₀ y (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ)
      = ((collPt k y (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) :=
  outerPt_apply_of_ne k₀ y (cOne k) (Ne.symm (cZero_ne_cOne k))

/-- **The collar value is the collapse of one piece at the block point**, on the open blocks. -/
theorem alphaFamily_eq_collapse_of_block (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (k₀ j₀ : ℕ) (hk₀ : k₀ < m) (hj₀ : j₀ < Fintype.card ι)
    (y : EuclideanSpace ℝ (Fin ((8 + k) + 1)))
    (hξlo : 1 < (2 : ℝ) ^ (k₀ + 1) * ((collPt k y (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ))
    (hξhi : (2 : ℝ) ^ k₀ * ((collPt k y (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1)
    (hηlo : 1 < (2 : ℝ) ^ (j₀ + 1) * ((collPt k y (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ))
    (hηhi : (2 : ℝ) ^ j₀ * ((collPt k y (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1) :
    alphaFamily (D := D) (Fam := Fam) G m (collPt k y)
      = (G.rep ((Fintype.equivFin ι).symm ⟨j₀, hj₀⟩)).collapse
          (clipPt k (cZero k) (cOne k) k₀ j₀ y) := by
  have hdef : alphaFamily (D := D) (Fam := Fam) G m
      = genLoopListConcat (cZero k)
          (List.ofFn (fun _ : Fin m => blockInner (D := D) (Fam := Fam) G)) := rfl
  have hdef2 : blockInner (D := D) (Fam := Fam) G
      = genLoopListConcat (cOne k)
          (List.ofFn (blockLoop (D := D) (Fam := Fam) G)) := rfl
  have hlen1 : (List.ofFn (fun _ : Fin m => blockInner (D := D) (Fam := Fam) G)).length = m :=
    List.length_ofFn
  have hlen2 : (List.ofFn (blockLoop (D := D) (Fam := Fam) G)).length =
      Fintype.card ι := List.length_ofFn
  have hk₀' : k₀ < (List.ofFn (fun _ : Fin m => blockInner (D := D) (Fam := Fam) G)).length := by
    rw [hlen1]; exact hk₀
  have hj₀' : j₀ < (List.ofFn (blockLoop (D := D) (Fam := Fam) G)).length := by
    rw [hlen2]; exact hj₀
  have hηlo' : 1 < (2 : ℝ) ^ (j₀ + 1) *
      ((outerPt k (cZero k) k₀ y (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) := by
    rw [outerPt_apply_cOne k₀ y]; exact hηlo
  have hηhi' : (2 : ℝ) ^ j₀ *
      ((outerPt k (cZero k) k₀ y (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1 := by
    rw [outerPt_apply_cOne k₀ y]; exact hηhi
  have houter := genLoopListConcat_eq_block (cZero k)
    (List.ofFn (fun _ : Fin m => blockInner (D := D) (Fam := Fam) G)) (collPt k y) k₀ hk₀'
      hξlo hξhi
  have hget1 : (List.ofFn (fun _ : Fin m => blockInner (D := D) (Fam := Fam) G))[k₀]
      = blockInner (D := D) (Fam := Fam) G := by
    rw [get_ofFn_eq _ _ hk₀']
  have hpt1 : blockPt (cZero k) k₀ (collPt k y) hξlo hξhi = outerPt k (cZero k) k₀ y :=
    blockPt_eq_upd (cZero k) k₀ (collPt k y) hξlo hξhi
  have hinner := genLoopListConcat_eq_block (cOne k)
    (List.ofFn (blockLoop (D := D) (Fam := Fam) G)) (outerPt k (cZero k) k₀ y) j₀ hj₀' hηlo' hηhi'
  have hget2 : (List.ofFn (blockLoop (D := D) (Fam := Fam) G))[j₀]
      = blockLoop (D := D) (Fam := Fam) G ⟨j₀, hj₀⟩ := by
    rw [get_ofFn_eq _ _ hj₀']
  have hpt2 : blockPt (cOne k) j₀ (outerPt k (cZero k) k₀ y) hηlo' hηhi'
      = clipPt k (cZero k) (cOne k) k₀ j₀ y :=
    blockPt_eq_upd (cOne k) j₀ (outerPt k (cZero k) k₀ y) hηlo' hηhi'
  rw [hdef, houter, hget1, hpt1, hdef2, hinner, hget2, hpt2, blockLoop_apply]

/-! ## The tube chain and the coordinate field -/

/-- **The coordinate field is the tube data of the model tube point**, under the block conditions
and the tube membership.  The hypothesis `hblock` is the block chain
(`Work.PTGeometric.alphaFamily_eq_collapse_of_block`). -/
theorem coord_eq_model {G : GenuineTubeGeometry k D ι Fam} {m : ℕ}
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1)
    (k₀ j₀ : ℕ) (iχ : ι)
    (y : EuclideanSpace ℝ (Fin ((8 + k) + 1))) (hcol : y 0 < 1 / 2)
    (htube : modelEuc G (cZero k) (cOne k) k₀ j₀ y ∈ (G.chart iχ).openTube)
    (hblock : alphaFamily (D := D) (Fam := Fam) G m (collPt k y)
      = (G.rep iχ).collapse (clipPt k (cZero k) (cOne k) k₀ j₀ y))
    (hξlo : 1 < (2 : ℝ) ^ (k₀ + 1) * ((collPt k y (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ))
    (hξhi : (2 : ℝ) ^ k₀ * ((collPt k y (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1)
    (hηlo : 1 < (2 : ℝ) ^ (j₀ + 1) * ((collPt k y (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ))
    (hηhi : (2 : ℝ) ^ j₀ * ((collPt k y (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1)
    (h : flatSourceHomotopy8 (k := k) (familySource (D := D) (Fam := Fam) G m hpow).H
      (familySource (D := D) (Fam := Fam) G m hpow).φ y ≠ D.t₀) :
    G.coord ⟨flatSourceHomotopy8 (k := k) (familySource (D := D) (Fam := Fam) G m hpow).H
        (familySource (D := D) (Fam := Fam) G m hpow).φ y, h⟩
      = (padEndEuc k G.mU G.hmU (tubeNormalProj (G.emb iχ) (G.chart iχ)
            (modelEuc G (cZero k) (cOne k) k₀ j₀ y)),
         padEuc k G.mU G.hmU (tubeNormalCoord (G.emb iχ) (G.chart iχ)
            (modelEuc G (cZero k) (cOne k) k₀ j₀ y))) := by
  set S := familySource (D := D) (Fam := Fam) G m hpow with hS
  have hcollar : flatSourceHomotopy8 (k := k) S.H S.φ y
      = alphaFamily (D := D) (Fam := Fam) G m (collPt k y) :=
    flatSourceHomotopy8_eq_collapse (k := k) S.H S.φ (alphaFamily (D := D) (Fam := Fam) G m)
      S.collar (le_of_lt hcol)
  have hval : flatSourceHomotopy8 (k := k) S.H S.φ y
      = (G.rep iχ).collapse (fun j => reIdx k (clipPt k (cZero k) (cOne k) k₀ j₀ y) (finKR k j)) := by
    rw [hcollar, hblock]
    exact congrArg (fun s => (G.rep iχ).collapse s)
      (reIdx_comp_finKR k (clipPt k (cZero k) (cOne k) k₀ j₀ y)).symm
  have htube' : Work.Tubular.cubeToEuc (8 + k) G.R
      (reIdx k (clipPt k (cZero k) (cOne k) k₀ j₀ y)) ∈ (G.chart iχ).openTube := by
    rw [← modelEuc_eq_cubeToEuc G (cZero_ne_cOne k) k₀ j₀ y hξlo hξhi hηlo hηhi]
    exact htube
  have hrep : (G.rep iχ).collapse
      (fun j => reIdx k (clipPt k (cZero k) (cOne k) k₀ j₀ y) (finKR k j)) ≠ D.t₀ :=
    fun hh => h (hval ▸ hh)
  have key : (⟨flatSourceHomotopy8 (k := k) S.H S.φ y, h⟩ : {x : D.T // x ≠ D.t₀})
      = ⟨(G.rep iχ).collapse
          (fun j => reIdx k (clipPt k (cZero k) (cOne k) k₀ j₀ y) (finKR k j)), hrep⟩ :=
    Subtype.ext hval
  rw [key, coord_collapse_of_isGeom G iχ
    (reIdx k (clipPt k (cZero k) (cOne k) k₀ j₀ y)) htube' hrep]
  rw [modelEuc_eq_cubeToEuc G (cZero_ne_cOne k) k₀ j₀ y hξlo hξhi hηlo hηhi]

/-! ## The local smooth model -/

/-- The hypotheses of the model, as a set: the collar, the two open dyadic blocks and the tube. -/
def localSet (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ) (iχ : ι) :
    Set (EuclideanSpace ℝ (Fin ((8 + k) + 1))) :=
  {y | y 0 < 1 / 2 ∧
    1 < (2 : ℝ) ^ (k₀ + 1) * ((collPt k y (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) ∧
    (2 : ℝ) ^ k₀ * ((collPt k y (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1 ∧
    1 < (2 : ℝ) ^ (j₀ + 1) * ((collPt k y (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) ∧
    (2 : ℝ) ^ j₀ * ((collPt k y (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1 ∧
    modelEuc G (cZero k) (cOne k) k₀ j₀ y ∈ (G.chart iχ).openTube}

theorem isOpen_localSet (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ) (iχ : ι) :
    IsOpen (localSet G k₀ j₀ iχ) := by
  have h0 : Continuous (fun y : EuclideanSpace ℝ (Fin ((8 + k) + 1)) => y 0) :=
    (continuous_apply 0).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin ((8 + k) + 1) => ℝ)).continuous
  have hξ : Continuous (fun y : EuclideanSpace ℝ (Fin ((8 + k) + 1)) =>
      ((collPt k y (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ)) :=
    (contMDiff_collPt_apply k (cZero k)).continuous
  have hη : Continuous (fun y : EuclideanSpace ℝ (Fin ((8 + k) + 1)) =>
      ((collPt k y (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ)) :=
    (contMDiff_collPt_apply k (cOne k)).continuous
  have htube : IsOpen {y : EuclideanSpace ℝ (Fin ((8 + k) + 1)) |
      modelEuc G (cZero k) (cOne k) k₀ j₀ y ∈ (G.chart iχ).openTube} :=
    (G.chart iχ).openTube_isOpen.preimage
      (contMDiff_modelEuc G (cZero k) (cOne k) k₀ j₀).continuous
  have hA : IsOpen {y : EuclideanSpace ℝ (Fin ((8 + k) + 1)) | y 0 < 1 / 2} :=
    isOpen_lt h0 continuous_const
  have hB : IsOpen {y : EuclideanSpace ℝ (Fin ((8 + k) + 1)) |
      1 < (2 : ℝ) ^ (k₀ + 1) * ((collPt k y (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ)} :=
    isOpen_lt continuous_const (continuous_const.mul hξ)
  have hC : IsOpen {y : EuclideanSpace ℝ (Fin ((8 + k) + 1)) |
      (2 : ℝ) ^ k₀ * ((collPt k y (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1} :=
    isOpen_lt (continuous_const.mul hξ) continuous_const
  have hD : IsOpen {y : EuclideanSpace ℝ (Fin ((8 + k) + 1)) |
      1 < (2 : ℝ) ^ (j₀ + 1) * ((collPt k y (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ)} :=
    isOpen_lt continuous_const (continuous_const.mul hη)
  have hE : IsOpen {y : EuclideanSpace ℝ (Fin ((8 + k) + 1)) |
      (2 : ℝ) ^ j₀ * ((collPt k y (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1} :=
    isOpen_lt (continuous_const.mul hη) continuous_const
  exact hA.inter (hB.inter (hC.inter (hD.inter (hE.inter htube))))

/-- **The local smooth model of the coordinate field on the collar.** -/
theorem exists_local_smooth_model (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1)
    (y₀ : EuclideanSpace ℝ (Fin ((8 + k) + 1))) (hy₀ : y₀ 0 < 1 / 2)
    (hne₀ : flatSourceHomotopy8 (k := k) (familySource (D := D) (Fam := Fam) G m hpow).H
      (familySource (D := D) (Fam := Fam) G m hpow).φ y₀ ≠ D.t₀) :
    ∃ V : Set (EuclideanSpace ℝ (Fin ((8 + k) + 1))), IsOpen V ∧ y₀ ∈ V ∧
      ∃ Ψ : EuclideanSpace ℝ (Fin ((8 + k) + 1)) → (EndOp (k + G.mU) × Amb (k + G.mU)),
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin ((8 + k) + 1)))
          𝓘(ℝ, EndOp (k + G.mU) × Amb (k + G.mU)) ∞ Ψ V ∧
        ∀ y ∈ V, ∀ (h : flatSourceHomotopy8 (k := k)
            (familySource (D := D) (Fam := Fam) G m hpow).H
            (familySource (D := D) (Fam := Fam) G m hpow).φ y ≠ D.t₀),
          G.coord ⟨flatSourceHomotopy8 (k := k) (familySource (D := D) (Fam := Fam) G m hpow).H
            (familySource (D := D) (Fam := Fam) G m hpow).φ y, h⟩ = Ψ y := by
  set S := familySource (D := D) (Fam := Fam) G m hpow with hS
  have hcollar₀ : flatSourceHomotopy8 (k := k) S.H S.φ y₀
      = alphaFamily (D := D) (Fam := Fam) G m (collPt k y₀) :=
    flatSourceHomotopy8_eq_collapse (k := k) S.H S.φ (alphaFamily (D := D) (Fam := Fam) G m)
      S.collar (le_of_lt hy₀)
  have hα : alphaFamily (D := D) (Fam := Fam) G m (collPt k y₀) ≠ D.t₀ :=
    fun hh => hne₀ (hcollar₀.trans hh)
  have hα' : genLoopListConcat (cZero k)
      (List.ofFn (fun _ : Fin m => blockInner (D := D) (Fam := Fam) G))
      (collPt k y₀) ≠ D.t₀ := hα
  obtain ⟨k₀, hk₀', hξlo, hξhi⟩ := exists_block_interval (cZero k)
    (List.ofFn (fun _ : Fin m => blockInner (D := D) (Fam := Fam) G)) (collPt k y₀) hα'
  have hk₀ : k₀ < m := by rwa [List.length_ofFn] at hk₀'
  have hget1 : (List.ofFn (fun _ : Fin m => blockInner (D := D) (Fam := Fam) G))[k₀]
      = blockInner (D := D) (Fam := Fam) G := by
    rw [get_ofFn_eq _ _ hk₀']
  have hpt1 : blockPt (cZero k) k₀ (collPt k y₀) hξlo hξhi = outerPt k (cZero k) k₀ y₀ :=
    blockPt_eq_upd (cZero k) k₀ (collPt k y₀) hξlo hξhi
  have houterval : alphaFamily (D := D) (Fam := Fam) G m (collPt k y₀)
      = blockInner (D := D) (Fam := Fam) G (outerPt k (cZero k) k₀ y₀) := by
    rw [show alphaFamily (D := D) (Fam := Fam) G m
        = genLoopListConcat (cZero k)
            (List.ofFn (fun _ : Fin m => blockInner (D := D) (Fam := Fam) G)) from rfl,
      genLoopListConcat_eq_block (cZero k) _ (collPt k y₀) k₀ hk₀' hξlo hξhi, hget1, hpt1]
  have hbi : blockInner (D := D) (Fam := Fam) G (outerPt k (cZero k) k₀ y₀) ≠ D.t₀ :=
    fun hh => hα (houterval.trans hh)
  have hbi' : genLoopListConcat (cOne k) (List.ofFn (blockLoop (D := D) (Fam := Fam) G))
      (outerPt k (cZero k) k₀ y₀) ≠ D.t₀ := hbi
  obtain ⟨j₀, hj₀', hηlo', hηhi'⟩ := exists_block_interval (cOne k)
    (List.ofFn (blockLoop (D := D) (Fam := Fam) G)) (outerPt k (cZero k) k₀ y₀) hbi'
  have hj₀ : j₀ < Fintype.card ι := by rwa [List.length_ofFn] at hj₀'
  have hηlo : 1 < (2 : ℝ) ^ (j₀ + 1) * ((collPt k y₀ (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) := by
    rw [← outerPt_apply_cOne k₀ y₀]; exact hηlo'
  have hηhi : (2 : ℝ) ^ j₀ * ((collPt k y₀ (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1 := by
    rw [← outerPt_apply_cOne k₀ y₀]; exact hηhi'
  set iχ := (Fintype.equivFin ι).symm ⟨j₀, hj₀⟩ with hiχ
  have hblock₀ : alphaFamily (D := D) (Fam := Fam) G m (collPt k y₀)
      = (G.rep iχ).collapse (clipPt k (cZero k) (cOne k) k₀ j₀ y₀) :=
    alphaFamily_eq_collapse_of_block (G := G) m k₀ j₀ hk₀ hj₀ y₀ hξlo hξhi hηlo hηhi
  have hrep₀ : (G.rep iχ).collapse (clipPt k (cZero k) (cOne k) k₀ j₀ y₀) ≠ D.t₀ := by
    intro hh
    exact hne₀ (by rw [hcollar₀, hblock₀]; exact hh)
  have htube₀ : modelEuc G (cZero k) (cOne k) k₀ j₀ y₀ ∈ (G.chart iχ).openTube := by
    have h1 : (G.rep iχ).collapse
        (fun j => (reIdx k (clipPt k (cZero k) (cOne k) k₀ j₀ y₀)) (finKR k j)) ≠ D.t₀ := by
      rw [reIdx_comp_finKR k (clipPt k (cZero k) (cOne k) k₀ j₀ y₀)]
      exact hrep₀
    have h2 : Work.Tubular.alphaV (G.chart iχ) G.hR (G.hbox iχ) D.t₀ (G.J iχ) (G.hJ iχ)
        (G.g iχ) (G.hg iχ) (reIdx k (clipPt k (cZero k) (cOne k) k₀ j₀ y₀)) ≠ D.t₀ := by
      rw [← G.isGeom iχ (reIdx k (clipPt k (cZero k) (cOne k) k₀ j₀ y₀))]
      exact h1
    have hmem := mem_openTube_of_alphaV_ne (G.chart iχ) G.hR (G.hbox iχ) D.t₀ (G.J iχ) (G.hJ iχ)
      (G.g iχ) (G.hg iχ) (t := reIdx k (clipPt k (cZero k) (cOne k) k₀ j₀ y₀)) h2
    rw [modelEuc_eq_cubeToEuc G (cZero_ne_cOne k) k₀ j₀ y₀ hξlo hξhi hηlo hηhi]
    exact hmem
  refine ⟨localSet G k₀ j₀ iχ, isOpen_localSet G k₀ j₀ iχ, ?_, ?_⟩
  · exact ⟨hy₀, hξlo, hξhi, hηlo, hηhi, htube₀⟩
  · refine ⟨fun y => (padEndEuc k G.mU G.hmU
          (tubeNormalProj (G.emb iχ) (G.chart iχ) (modelEuc G (cZero k) (cOne k) k₀ j₀ y)),
        padEuc k G.mU G.hmU
          (tubeNormalCoord (G.emb iχ) (G.chart iχ) (modelEuc G (cZero k) (cOne k) k₀ j₀ y))),
      ?_, ?_⟩
    · rw [contMDiffOn_iff_contDiffOn]
      refine ContDiffOn.prodMk ?_ ?_
      · refine ((padEndEucCLM k G.mU G.hmU).contDiff.contDiffOn).comp ?_
          (fun y _ => Set.mem_univ _)
        exact contMDiffOn_iff_contDiffOn.mp
          ((contMDiffOn_tubeNormalProj (G.emb iχ) (G.chart iχ)).comp
            (contMDiff_modelEuc G (cZero k) (cOne k) k₀ j₀).contMDiffOn
            (fun y hy => hy.2.2.2.2.2))
      · refine ((padEuc k G.mU G.hmU).contDiff.contDiffOn).comp ?_
          (fun y _ => Set.mem_univ _)
        exact contMDiffOn_iff_contDiffOn.mp
          ((contMDiffOn_tubeNormalCoord (G.emb iχ) (G.chart iχ)).comp
            (contMDiff_modelEuc G (cZero k) (cOne k) k₀ j₀).contMDiffOn
            (fun y hy => hy.2.2.2.2.2))
    · intro y hy h
      have hblock : alphaFamily (D := D) (Fam := Fam) G m (collPt k y)
          = (G.rep iχ).collapse (clipPt k (cZero k) (cOne k) k₀ j₀ y) :=
        alphaFamily_eq_collapse_of_block (G := G) m k₀ j₀ hk₀ hj₀ y
          hy.2.1 hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2.1
      exact coord_eq_model (G := G) hpow k₀ j₀ iχ y hy.1 hy.2.2.2.2.2 hblock
        hy.2.1 hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2.1 h

end

end Work.PTGeometric
