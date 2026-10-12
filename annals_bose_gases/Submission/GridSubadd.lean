import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.SubaddVol
import Submission.Superadd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Layer 2 — multi-cell (grid) subadditivity of the box energy.

`SubaddVol.boxEnergy_subadd` compares the energy in one big box with the sum of
the energies in TWO small boxes placed at opposite corners.  The thermodynamic
limit needs the same comparison with arbitrarily many cells (`m³` cells on a
grid with pairwise separation `≥ R`), because corner-pair splittings waste too
much volume to cover the particle capacity of the large box.

This file proves the general statement: a finite family of axis-parallel cells
of side `ℓ`, pairwise separated by at least `R`, sitting inside a cube of side
`L`, satisfies

    E(Σ_j n_j , L)  ≤  Σ_j E(n_j , ℓ).

The proof is a direct generalization of the two-cell construction in
`SubaddVol.lean`: form the product of the (translated) trial states of the
individual cells; cross-cell interaction terms vanish because the cells are
separated by `≥ R` and the support of `v` is contained in `ball 0 R`, and the
kinetic energy and the norm split over the product.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real
open MeasureTheory InnerProductSpace

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

local notation "𝓗" => _root_.BoseGases.𝓗



/-! ## 0. Vector cell translations -/

/-- Translation of a configuration by the *same* vector `c` applied to every
particle (`(cellShift N c w) a = w a - c`). -/
noncomputable def cellShift (N : ℕ) (c : ℝ³) : X N → X N :=
  fun w => w + (fun _ : Fin N => -c)

@[simp] lemma neg_fun_const (N : ℕ) (c : ℝ³) :
    -(fun _ : Fin N => c) = (fun _ : Fin N => -c) := by
  funext a
  rfl

@[simp] lemma cellShift_coord (N : ℕ) (c : ℝ³) (w : X N) (a : Fin N) (k : Fin 3) :
    (cellShift N c w a) k = (w a) k - c k := by
  simp [cellShift, sub_eq_add_neg]

lemma cellShift_contDiff (N : ℕ) (c : ℝ³) {n : ℕ∞ω} : ContDiff ℝ n (cellShift N c) := by
  unfold cellShift
  fun_prop

/-- `cellShift` is translation by the constant configuration `-c`. -/
lemma cellShift_eq_translate (N : ℕ) (c : ℝ³) :
    cellShift N c = fun w : X N => w + (fun _ : Fin N => -c) := by
  rfl

lemma cellShift_continuous (N : ℕ) (c : ℝ³) : Continuous (cellShift N c) :=
  (cellShift_contDiff (N := N) (n := 0) c).continuous

/-- `cellShift` is a translation, hence measure preserving. -/
lemma cellShift_measurePreserving (N : ℕ) (c : ℝ³) :
    MeasurePreserving (cellShift N c) := by
  unfold cellShift
  exact (measurePreserving_add_right (μ := (volume : Measure (X N))) (fun _ : Fin N => -c) :
    MeasurePreserving (fun w : X N => w + (fun _ : Fin N => -c)))

lemma cellShift_measurableEmbedding (N : ℕ) (c : ℝ³) :
    MeasurableEmbedding (cellShift N c) := by
  rw [cellShift_eq_translate]
  exact (translateEquiv (N := N) (fun _ : Fin N => -c)).measurableEmbedding

/-- Whole-space integrals are invariant under `cellShift`. -/
lemma integral_cellShift {N : ℕ} (c : ℝ³) (h : X N → ℝ) :
    (∫ w : X N, h (cellShift N c w)) = ∫ z : X N, h z :=
  (cellShift_measurePreserving N c).integral_comp (cellShift_measurableEmbedding N c) h

/-- The `partialLaplacian` commutes with the vector cell shift. -/
lemma partialLaplacian_cellShift {N : ℕ} (c : ℝ³) {f : X N → ℝ} (j : Fin N) (x : X N) :
    partialLaplacian j (fun y : X N => f (cellShift N c y)) x =
      partialLaplacian j f (cellShift N c x) := by
  simpa [cellShift, sub_eq_add_neg] using
    (partialLaplacian_translate (N := N) (c := (fun _ : Fin N => c)) (f := f) j x)

/-- Relative coordinates are unchanged by the cell shift. -/
lemma cellShift_sub (N : ℕ) (c : ℝ³) (w : X N) (p q : Fin N) :
    cellShift N c w p - cellShift N c w q = w p - w q := by
  ext k
  simp

/-- `pairSum` is invariant under the cell shift. -/
lemma pairSum_cellShift {N : ℕ} (v : ℝ³ → ℝ) (c : ℝ³) (w : X N) :
    pairSum N v (cellShift N c w) = pairSum N v w := by
  unfold pairSum
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  exact cellShift_sub N c w p.1 p.2

/-- The shifted (by the vector `c`) state: `f (w - c)`. -/
noncomputable def shiftedCell (N : ℕ) (c : ℝ³) (f : X N → ℝ) : X N → ℝ :=
  fun w => f (cellShift N c w)

lemma shiftedCell_contDiff {N : ℕ} (c : ℝ³) {f : X N → ℝ} {n : ℕ∞ω} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (shiftedCell N c f) := by
  exact hf.comp (cellShift_contDiff (N := N) c)

lemma shiftedCell_support_preimage {N : ℕ} (c : ℝ³) {f : X N → ℝ} :
    Function.support (shiftedCell N c f) ⊆ (cellShift N c) ⁻¹' Function.support f := by
  intro w hw
  change f (cellShift N c w) ≠ 0
  by_contra h2
  apply hw
  simp [shiftedCell, h2]

/-- Nonzero states stay nonzero after the shift. -/
lemma shiftedCell_nezero {N : ℕ} (c : ℝ³) {f : X N → ℝ} (hf : f ≠ 0) :
    shiftedCell N c f ≠ 0 := by
  intro hz
  apply hf
  funext x
  let y : X N := x + (fun _ : Fin N => c)
  have hy : cellShift N c y = x := by
    ext a k
    simp [y, cellShift]
  calc
    f x = f (cellShift N c y) := by rw [hy]
    _ = shiftedCell N c f y := rfl
    _ = 0 := congrFun hz y

/-! ## 1. Shifted single-cell states -/

/-- Coordinatewise containment of the shifted cube in the interval `[0, L]`. -/
lemma cube_in_box_coord {ℓ L : ℝ} {c : ℝ³}
    (hlo : ∀ k, 0 ≤ c k) (hhi : ∀ k, c k + ℓ ≤ L) (y : ℝ³) (k : Fin 3)
    (hy : c k ≤ y k ∧ y k ≤ c k + ℓ) : y k ∈ Set.Icc 0 L := by
  constructor <;> linarith [hlo k, hhi k, hy.1, hy.2]

/-- If the unshifted state is supported in the box of side `ℓ`, the shifted one is
supported in the shifted cube (per particle, per coordinate). -/
lemma shiftedCell_support_cube {N : ℕ} {ℓ : ℝ} (Φ : CInfty0Box N ℓ) (c : ℝ³) {w : X N}
    (hw : shiftedCell N c (Φ : X N → ℝ) w ≠ 0) (a : Fin N) (k : Fin 3) :
    c k ≤ (w a) k ∧ (w a) k ≤ c k + ℓ := by
  have hcs : cellShift N c w ∈ Function.support (Φ : X N → ℝ) := by
    simpa [shiftedCell] using hw
  have hb : cellShift N c w ∈ box N ℓ := support_subset_box_state Φ hcs
  have hcoord : ((cellShift N c w) a) k ∈ Set.Icc 0 ℓ := ((mem_box_iff N ℓ (cellShift N c w)).mp hb) a k
  have hd : 0 ≤ (w a) k - c k ∧ (w a) k - c k ≤ ℓ := by
    simpa using hcoord
  constructor <;> linarith [hd.1, hd.2]

/-- The shifted cell state lies in `CInfty0Box N L` when the shifted cube fits in
`[0,L]³`. -/
noncomputable def shiftedState (N : ℕ) {ℓ L : ℝ} (c : ℝ³)
    (hlo : ∀ k : Fin 3, 0 ≤ c k) (hhi : ∀ k : Fin 3, c k + ℓ ≤ L)
    (Φ : CInfty0Box N ℓ) : CInfty0Box N L where
  toFun := shiftedCell N c (Φ : X N → ℝ)
  contDiff := (shiftedCell_contDiff c (psi_contDiff Φ)).contDiffOn
  support := by
    have hopen : IsOpen ((cellShift N c) ⁻¹' interior (box N ℓ)) :=
      IsOpen.preimage (cellShift_continuous N c) isOpen_interior
    have hsub : (cellShift N c) ⁻¹' interior (box N ℓ) ⊆ box N L := by
      intro w hw
      rw [mem_box_iff]
      intro a k
      have hb : cellShift N c w ∈ box N ℓ := interior_subset hw
      have hcoord : ((cellShift N c w) a) k ∈ Set.Icc 0 ℓ := ((mem_box_iff N ℓ (cellShift N c w)).mp hb) a k
      have hd : 0 ≤ (w a) k - c k ∧ (w a) k - c k ≤ ℓ := by
        simpa using hcoord
      have hck : c k ≤ (w a) k ∧ (w a) k ≤ c k + ℓ := by
        constructor <;> linarith [hd.1, hd.2]
      exact cube_in_box_coord (ℓ := ℓ) hlo hhi (w a) k hck
    have hO : (cellShift N c) ⁻¹' interior (box N ℓ) ⊆ interior (box N L) :=
      interior_maximal hsub hopen
    calc
      tsupport (shiftedCell N c (Φ : X N → ℝ))
          ⊆ closure ((cellShift N c) ⁻¹' Function.support (Φ : X N → ℝ)) := closure_mono
              (shiftedCell_support_preimage (N := N) c (f := (Φ : X N → ℝ)))
      _ ⊆ (cellShift N c) ⁻¹' (closure (Function.support (Φ : X N → ℝ))) :=
            (cellShift_continuous N c).closure_preimage_subset _
      _ ⊆ (cellShift N c) ⁻¹' interior (box N ℓ) := by
            exact Set.preimage_mono Φ.support
      _ ⊆ interior (box N L) := hO
  nezero := shiftedCell_nezero c Φ.nezero

@[simp] lemma shiftedState_toFun {N : ℕ} {ℓ L : ℝ} (c : ℝ³)
    (hlo : ∀ k : Fin 3, 0 ≤ c k) (hhi : ∀ k : Fin 3, c k + ℓ ≤ L)
    (Φ : CInfty0Box N ℓ) :
    ((shiftedState N c hlo hhi Φ : CInfty0Box N L) : X N → ℝ) =
      shiftedCell N c (Φ : X N → ℝ) := by
  rfl
/-! ## 2. Binary tensor of two states in the same big box -/

/-- The support of the tensor product is the intersection of the preimages of the
two supports. -/
lemma support_prodState {N1 N2 : ℕ} (f1 : X N1 → ℝ) (f2 : X N2 → ℝ) (x : X (N1+N2)) :
    prodState N1 N2 f1 f2 x ≠ 0 → f1 (firstBlock N1 N2 x) ≠ 0 ∧ f2 (lastBlock N1 N2 x) ≠ 0 := by
  intro h
  constructor
  · intro hz
    apply h
    simp [prodState, hz]
  · intro hz
    apply h
    simp [prodState, hz]

/-- `tsupport` of the tensor is inside the preimages of the individual `tsupport`s. -/
lemma tsupport_tensor_subset {N1 N2 : ℕ} {f1 : X N1 → ℝ} {f2 : X N2 → ℝ} :
    tsupport (prodState N1 N2 f1 f2) ⊆
      (firstBlock N1 N2 ⁻¹' tsupport f1) ∩ (lastBlock N1 N2 ⁻¹' tsupport f2) := by
  have hsupp : Function.support (prodState N1 N2 f1 f2) ⊆
      (firstBlock N1 N2 ⁻¹' Function.support f1) ∩ (lastBlock N1 N2 ⁻¹' Function.support f2) := by
    intro x hx
    have h := support_prodState f1 f2 x hx
    constructor
    · change f1 (firstBlock N1 N2 x) ≠ 0
      exact h.1
    · change f2 (lastBlock N1 N2 x) ≠ 0
      exact h.2
  calc
    tsupport (prodState N1 N2 f1 f2)
        ⊆ closure ((firstBlock N1 N2 ⁻¹' Function.support f1) ∩
            (lastBlock N1 N2 ⁻¹' Function.support f2)) := closure_mono hsupp
    _ ⊆ closure (firstBlock N1 N2 ⁻¹' Function.support f1) ∩
          closure (lastBlock N1 N2 ⁻¹' Function.support f2) := closure_inter_subset
    _ ⊆ (firstBlock N1 N2 ⁻¹' (closure (Function.support f1))) ∩
          (lastBlock N1 N2 ⁻¹' (closure (Function.support f2))) := by
          exact Set.inter_subset_inter
            ((firstBlock_continuous N1 N2).closure_preimage_subset (Function.support f1))
            ((lastBlock_continuous N1 N2).closure_preimage_subset (Function.support f2))
    _ ⊆ (firstBlock N1 N2 ⁻¹' tsupport f1) ∩ (lastBlock N1 N2 ⁻¹' tsupport f2) := by
          exact Set.inter_subset_inter subset_rfl subset_rfl

/-- The open set where both blocks are in the interiors of their boxes, inside the
big box. -/
lemma tensor_prebox_subset_box {N1 N2 : ℕ} (L : ℝ) :
    ((firstBlock N1 N2 ⁻¹' interior (box N1 L)) ∩ (lastBlock N1 N2 ⁻¹' interior (box N2 L)))
      ⊆ box (N1+N2) L := by
  intro x hx
  rw [mem_box_split]
  constructor
  · exact interior_subset hx.1
  · exact interior_subset hx.2

lemma tensor_prebox_open {N1 N2 : ℕ} (L : ℝ) :
    IsOpen ((firstBlock N1 N2 ⁻¹' interior (box N1 L)) ∩ (lastBlock N1 N2 ⁻¹' interior (box N2 L))) := by
  exact IsOpen.inter
    (IsOpen.preimage (firstBlock_continuous N1 N2) isOpen_interior)
    (IsOpen.preimage (lastBlock_continuous N1 N2) isOpen_interior)

/-- The tensor of two nonzero functions is nonzero. -/
lemma prodState_nezero {N1 N2 : ℕ} {f1 : X N1 → ℝ} {f2 : X N2 → ℝ}
    (h1 : f1 ≠ 0) (h2 : f2 ≠ 0) : prodState N1 N2 f1 f2 ≠ 0 := by
  intro hzero
  have h1' : ∃ u : X N1, f1 u ≠ 0 := by
    by_contra h
    have hz : f1 = 0 := by
      funext u
      by_contra hu
      exact h ⟨u, hu⟩
    exact h1 hz
  have h2' : ∃ w : X N2, f2 w ≠ 0 := by
    by_contra h
    have hz : f2 = 0 := by
      funext w
      by_contra hw
      exact h ⟨w, hw⟩
    exact h2 hz
  rcases h1' with ⟨u0, hu0⟩
  rcases h2' with ⟨w0, hw0⟩
  let x0 : X (N1+N2) := mergeBlock N1 N2 (u0, w0)
  have hfirst : firstBlock N1 N2 x0 = u0 := by simp [x0, mergeBlock_first]
  have hlast : lastBlock N1 N2 x0 = w0 := by simp [x0, mergeBlock_last]
  have hval : prodState N1 N2 f1 f2 x0 ≠ 0 := by
    intro hz
    have hpt : f1 (firstBlock N1 N2 x0) * f2 (lastBlock N1 N2 x0) = 0 := by
      simpa [prodState] using hz
    rcases mul_eq_zero.mp hpt with hL | hR
    · exact hu0 (by simpa [hfirst] using hL)
    · exact hw0 (by simpa [hlast] using hR)
  exact hval (congrFun hzero x0)

/-- The tensor product of two `CInfty0Box` states in the same box side `L`. -/
noncomputable def tensorState (N1 N2 : ℕ) {L : ℝ} (hL : 0 < L)
    (Ψ1 : CInfty0Box N1 L) (Ψ2 : CInfty0Box N2 L) : CInfty0Box (N1+N2) L where
  toFun := prodState N1 N2 (Ψ1 : X N1 → ℝ) (Ψ2 : X N2 → ℝ)
  contDiff := by
    have h1 : ContDiff ℝ ∞ (fun x : X (N1+N2) => (Ψ1 : X N1 → ℝ) (firstBlock N1 N2 x)) :=
      (psi_contDiff Ψ1).comp (fstCLM N1 N2).contDiff
    have h2 : ContDiff ℝ ∞ (fun x : X (N1+N2) => (Ψ2 : X N2 → ℝ) (lastBlock N1 N2 x)) :=
      (psi_contDiff Ψ2).comp (lstCLM N1 N2).contDiff
    exact (ContDiff.mul h1 h2).contDiffOn
  support := by
    have hts := tsupport_tensor_subset (f1 := (Ψ1 : X N1 → ℝ)) (f2 := (Ψ2 : X N2 → ℝ))
    have h1 : firstBlock N1 N2 ⁻¹' tsupport (Ψ1 : X N1 → ℝ) ⊆
        firstBlock N1 N2 ⁻¹' interior (box N1 L) := Set.preimage_mono Ψ1.support
    have h2 : lastBlock N1 N2 ⁻¹' tsupport (Ψ2 : X N2 → ℝ) ⊆
        lastBlock N1 N2 ⁻¹' interior (box N2 L) := Set.preimage_mono Ψ2.support
    have hO : ((firstBlock N1 N2 ⁻¹' interior (box N1 L)) ∩
        (lastBlock N1 N2 ⁻¹' interior (box N2 L))) ⊆ interior (box (N1+N2) L) :=
      interior_maximal (tensor_prebox_subset_box (N1 := N1) (N2 := N2) L)
        (tensor_prebox_open (N1 := N1) (N2 := N2) L)
    calc
      tsupport (prodState N1 N2 (Ψ1 : X N1 → ℝ) (Ψ2 : X N2 → ℝ))
          ⊆ (firstBlock N1 N2 ⁻¹' tsupport (Ψ1 : X N1 → ℝ)) ∩
              (lastBlock N1 N2 ⁻¹' tsupport (Ψ2 : X N2 → ℝ)) := hts
      _ ⊆ (firstBlock N1 N2 ⁻¹' interior (box N1 L)) ∩
            (lastBlock N1 N2 ⁻¹' interior (box N2 L)) := Set.inter_subset_inter h1 h2
      _ ⊆ interior (box (N1+N2) L) := hO
  nezero := prodState_nezero Ψ1.nezero Ψ2.nezero

@[simp] lemma tensorState_toFun {N1 N2 : ℕ} {L : ℝ} (hL : 0 < L)
    (Ψ1 : CInfty0Box N1 L) (Ψ2 : CInfty0Box N2 L) :
    ((tensorState N1 N2 hL Ψ1 Ψ2 : CInfty0Box (N1+N2) L) : X (N1+N2) → ℝ) =
      prodState N1 N2 (Ψ1 : X N1 → ℝ) (Ψ2 : X N2 → ℝ) := by
  rfl


/-! ## 3. The tensor quotient identity (same side, separated supports) -/

/-- Cross-cell terms of the tensor state vanish (hypothesis version). -/
lemma tensor_crossSum_zero {N1 N2 : ℕ} {v : ℝ³ → ℝ} {f1 : X N1 → ℝ} {f2 : X N2 → ℝ}
    (hcross : ∀ u w, f1 u ≠ 0 → f2 w ≠ 0 → ∀ i : Fin N1, ∀ j : Fin N2, v (u i - w j) = 0)
    (x : X (N1+N2)) :
    (prodState N1 N2 f1 f2 x)^2 * crossSum N1 N2 v (firstBlock N1 N2 x) (lastBlock N1 N2 x) = 0 := by
  let u : X N1 := firstBlock N1 N2 x
  let w : X N2 := lastBlock N1 N2 x
  by_cases hx : prodState N1 N2 f1 f2 x = 0
  · simp [hx]
  · have hf : f1 u ≠ 0 ∧ f2 w ≠ 0 := by
      simpa [u, w] using (support_prodState f1 f2 x hx)
    have hz : ∀ i : Fin N1, ∀ j : Fin N2, v (u i - w j) = 0 := hcross u w hf.1 hf.2
    calc
      (prodState N1 N2 f1 f2 x)^2 * crossSum N1 N2 v u w
          = (f1 u * f2 w)^2 * crossSum N1 N2 v u w := by
            simp [prodState, u, w]
      _ = 0 := by
            unfold crossSum
            simp [hz]

/-- Pointwise: on the product state the pair sum splits into the two blocks. -/
lemma tensor_int_pointwise {N1 N2 : ℕ} {v : ℝ³ → ℝ} {f1 : X N1 → ℝ} {f2 : X N2 → ℝ}
    (hcross : ∀ u w, f1 u ≠ 0 → f2 w ≠ 0 → ∀ i : Fin N1, ∀ j : Fin N2, v (u i - w j) = 0)
    (x : X (N1+N2)) :
    (prodState N1 N2 f1 f2 x)^2 * pairSum (N1+N2) v x =
      (prodState N1 N2 f1 f2 x)^2 *
        (pairSum N1 v (firstBlock N1 N2 x) + pairSum N2 v (lastBlock N1 N2 x)) := by
  have hz := tensor_crossSum_zero (N1 := N1) (N2 := N2) (v := v) hcross x
  calc
    (prodState N1 N2 f1 f2 x)^2 * pairSum (N1+N2) v x
        = (prodState N1 N2 f1 f2 x)^2 *
            (pairSum N1 v (firstBlock N1 N2 x) + pairSum N2 v (lastBlock N1 N2 x) +
              crossSum N1 N2 v (firstBlock N1 N2 x) (lastBlock N1 N2 x)) := by
          rw [pairSum_block_split]
    _ = (prodState N1 N2 f1 f2 x)^2 *
          (pairSum N1 v (firstBlock N1 N2 x) + pairSum N2 v (lastBlock N1 N2 x)) := by
          nlinarith [hz]

/-- The Rayleigh quotient of the tensor of two separated states (both in the box of
side `L`) is the sum of the two quotients. -/
lemma tensorQuot {N1 N2 : ℕ} {L : ℝ} (hL : 0 < L) {v : ℝ³ → ℝ} (hv1 : MemLp v 1)
    (Ψ1 : CInfty0Box N1 L) (Ψ2 : CInfty0Box N2 L)
    (hcross : ∀ u w, (Ψ1 : X N1 → ℝ) u ≠ 0 → (Ψ2 : X N2 → ℝ) w ≠ 0 →
      ∀ i : Fin N1, ∀ j : Fin N2, v (u i - w j) = 0) :
    boxQuot (N1+N2) L v (tensorState N1 N2 hL Ψ1 Ψ2) =
      boxQuot N1 L v Ψ1 + boxQuot N2 L v Ψ2 := by
  let Ψ : CInfty0Box (N1+N2) L := tensorState N1 N2 hL Ψ1 Ψ2
  let f1 : X N1 → ℝ := (Ψ1 : X N1 → ℝ)
  let f2 : X N2 → ℝ := (Ψ2 : X N2 → ℝ)
  let g : X (N1+N2) → ℝ := prodState N1 N2 f1 f2
  have hg : (Ψ : X (N1+N2) → ℝ) = g := by
    simp [Ψ, g, f1, f2]
  have h2c1 : ContDiff ℝ 2 f1 := contDiff_two_of_infty (psi_contDiff Ψ1)
  have h2c2 : ContDiff ℝ 2 f2 := contDiff_two_of_infty (psi_contDiff Ψ2)
  -- -------- kinetic energy of the trial state --------
  have hsum1 : (∑ i1 : Fin N1, ∫ x in box (N1+N2) L,
          g x * (-(partialLaplacian (Fin.castAdd N2 i1) g x))) =
      (∑ i1 : Fin N1, ∫ u in box N1 L, f1 u * (-(partialLaplacian i1 f1 u))) *
        (∫ w in box N2 L, f2 w * f2 w) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i1 hi1
    have ht := kinetic_term_first (L := L) (f1 := f1) (f2 := f2) h2c1 i1
    simpa [g, prodState, f1, f2] using ht
  have hsum2 : (∑ j2 : Fin N2, ∫ x in box (N1+N2) L,
          g x * (-(partialLaplacian (Fin.natAdd N1 j2) g x))) =
      (∫ u in box N1 L, f1 u * f1 u) *
        (∑ j2 : Fin N2, ∫ w in box N2 L, f2 w * (-(partialLaplacian j2 f2 w))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j2 hj2
    have ht := kinetic_term_last (L := L) (f1 := f1) (f2 := f2) h2c2 j2
    simpa [g, prodState, f1, f2] using ht
  have hK3 : kineticEnergy (N1+N2) L Ψ =
      (∑ i1 : Fin N1, ∫ u in box N1 L, f1 u * (-(partialLaplacian i1 f1 u))) *
        (∫ w in box N2 L, f2 w * f2 w) +
      (∫ u in box N1 L, f1 u * f1 u) *
        (∑ j2 : Fin N2, ∫ w in box N2 L, f2 w * (-(partialLaplacian j2 f2 w))) := by
    calc
      kineticEnergy (N1+N2) L Ψ
          = ∑ i : Fin (N1+N2), ∫ x in box (N1+N2) L,
              (Ψ : X (N1+N2)→ℝ) x * (-(partialLaplacian i (Ψ : X (N1+N2)→ℝ) x)) := rfl
      _ = (∑ i1 : Fin N1, ∫ x in box (N1+N2) L,
              (Ψ : X (N1+N2)→ℝ) x * (-(partialLaplacian (Fin.castAdd N2 i1) (Ψ : X (N1+N2)→ℝ) x))) +
          (∑ j2 : Fin N2, ∫ x in box (N1+N2) L,
              (Ψ : X (N1+N2)→ℝ) x * (-(partialLaplacian (Fin.natAdd N1 j2) (Ψ : X (N1+N2)→ℝ) x))) := by
            rw [Fin.sum_univ_add]
      _ = (∑ i1 : Fin N1, ∫ x in box (N1+N2) L,
              g x * (-(partialLaplacian (Fin.castAdd N2 i1) g x))) +
          (∑ j2 : Fin N2, ∫ x in box (N1+N2) L,
              g x * (-(partialLaplacian (Fin.natAdd N1 j2) g x))) := by
            rw [hg]
      _ = (∑ i1 : Fin N1, ∫ u in box N1 L, f1 u * (-(partialLaplacian i1 f1 u))) *
            (∫ w in box N2 L, f2 w * f2 w) +
          (∫ u in box N1 L, f1 u * f1 u) *
            (∑ j2 : Fin N2, ∫ w in box N2 L, f2 w * (-(partialLaplacian j2 f2 w))) := by
            rw [hsum1, hsum2]
  -- --------- interaction energy of the trial state ---------
  have hIint : (fun x : X (N1+N2) => intIntegrand (N1+N2) L v Ψ x) =
      fun x : X (N1+N2) => (g x)^2 * pairSum (N1+N2) v x := by
    funext x
    simp [intIntegrand, pairSum, hg]
  have hptI : (fun x : X (N1+N2) => (g x)^2 * pairSum (N1+N2) v x) =
      fun x : X (N1+N2) => (g x)^2 *
        (pairSum N1 v (firstBlock N1 N2 x) + pairSum N2 v (lastBlock N1 N2 x)) := by
    funext x
    have h := tensor_int_pointwise (N1 := N1) (N2 := N2) (v := v)
      (f1 := f1) (f2 := f2) (by
        intro u w hu hw i j
        exact hcross u w hu hw i j) x
    simpa [g, prodState, f1, f2] using h
  have hc1 : Continuous f1 := (psi_contDiff Ψ1).continuous
  have hc2 : Continuous f2 := (psi_contDiff Ψ2).continuous
  have hintegrable_a1 : IntegrableOn (fun u : X N1 => (f1 u)^2 * pairSum N1 v u) (box N1 L) volume := by
    simpa [f1] using (integrableOn_state_int (N := N1) hL (v := v) hv1 Ψ1)
  have hintegrable_b1 : IntegrableOn (fun w : X N2 => (f2 w)^2) (box N2 L) volume := by
    have hc : Continuous (fun w : X N2 => (f2 w)^2) := hc2.pow 2
    exact ContinuousOn.integrableOn_compact (box_compact hL) hc.continuousOn
  have hintegrable_a2 : IntegrableOn (fun u : X N1 => (f1 u)^2) (box N1 L) volume := by
    have hc : Continuous (fun u : X N1 => (f1 u)^2) := hc1.pow 2
    exact ContinuousOn.integrableOn_compact (box_compact hL) hc.continuousOn
  have hintegrable_b2 : IntegrableOn (fun w : X N2 => (f2 w)^2 * pairSum N2 v w) (box N2 L) volume := by
    simpa [f2] using (integrableOn_state_int (N := N2) hL (v := v) hv1 Ψ2)
  have hPint : IntegrableOn (fun x : X (N1+N2) => (g x)^2 * pairSum N1 v (firstBlock N1 N2 x))
      (box (N1+N2) L) volume := by
    have hprod := integrableOn_prod_box (N1 := N1) (N2 := N2) L
      (a := fun u : X N1 => (f1 u)^2 * pairSum N1 v u) (b := fun w : X N2 => (f2 w)^2)
      hintegrable_a1 hintegrable_b1
    convert hprod using 1
    · funext x
      simp [g, prodState]
      ring
  have hQint : IntegrableOn (fun x : X (N1+N2) => (g x)^2 * pairSum N2 v (lastBlock N1 N2 x))
      (box (N1+N2) L) volume := by
    have hprod := integrableOn_prod_box (N1 := N1) (N2 := N2) L
      (a := fun u : X N1 => (f1 u)^2) (b := fun w : X N2 => (f2 w)^2 * pairSum N2 v w)
      hintegrable_a2 hintegrable_b2
    convert hprod using 1
    · funext x
      simp [g, prodState]
      ring
  have hI3 : interactionEnergy (N1+N2) L v Ψ =
      (∫ x in box (N1+N2) L, (g x)^2 * pairSum N1 v (firstBlock N1 N2 x)) +
      (∫ x in box (N1+N2) L, (g x)^2 * pairSum N2 v (lastBlock N1 N2 x)) := by
    calc
      interactionEnergy (N1+N2) L v Ψ
          = ∫ x in box (N1+N2) L, intIntegrand (N1+N2) L v Ψ x := by rw [boxInt_intIntegrand]
      _ = ∫ x in box (N1+N2) L, (g x)^2 * pairSum (N1+N2) v x := by rw [hIint]
      _ = ∫ x in box (N1+N2) L, (g x)^2 *
            (pairSum N1 v (firstBlock N1 N2 x) + pairSum N2 v (lastBlock N1 N2 x)) := by rw [hptI]
      _ = ∫ x in box (N1+N2) L,
            ((g x)^2 * pairSum N1 v (firstBlock N1 N2 x)) +
              ((g x)^2 * pairSum N2 v (lastBlock N1 N2 x)) := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = (∫ x in box (N1+N2) L, (g x)^2 * pairSum N1 v (firstBlock N1 N2 x)) +
          (∫ x in box (N1+N2) L, (g x)^2 * pairSum N2 v (lastBlock N1 N2 x)) := by
            rw [integral_add (μ := volume.restrict (box (N1+N2) L)) hPint hQint]
  have hPval : (∫ x in box (N1+N2) L, (g x)^2 * pairSum N1 v (firstBlock N1 N2 x)) =
      (∫ u in box N1 L, (f1 u)^2 * pairSum N1 v u) * (∫ w in box N2 L, f2 w * f2 w) := by
    calc
      (∫ x in box (N1+N2) L, (g x)^2 * pairSum N1 v (firstBlock N1 N2 x))
          = ∫ x in box (N1+N2) L,
              ((f1 (firstBlock N1 N2 x))^2 * pairSum N1 v (firstBlock N1 N2 x)) *
                ((f2 (lastBlock N1 N2 x))^2) := by
            apply integral_congr_ae
            filter_upwards with x
            simp [g, prodState]
            ring
      _ = (∫ u in box N1 L, (f1 u)^2 * pairSum N1 v u) * (∫ w in box N2 L, (f2 w)^2) := by
            exact boxIntegral_prod_fun L (fun u : X N1 => (f1 u)^2 * pairSum N1 v u)
              (fun w : X N2 => (f2 w)^2)
      _ = (∫ u in box N1 L, (f1 u)^2 * pairSum N1 v u) * (∫ w in box N2 L, f2 w * f2 w) := by
            have hp : (∫ w in box N2 L, (f2 w)^2) = ∫ w in box N2 L, f2 w * f2 w := by
              congr 1
              funext w
              rw [pow_two]
            rw [hp]
  have hQval : (∫ x in box (N1+N2) L, (g x)^2 * pairSum N2 v (lastBlock N1 N2 x)) =
      (∫ u in box N1 L, f1 u * f1 u) * (∫ w in box N2 L, (f2 w)^2 * pairSum N2 v w) := by
    calc
      (∫ x in box (N1+N2) L, (g x)^2 * pairSum N2 v (lastBlock N1 N2 x))
          = ∫ x in box (N1+N2) L,
              ((f1 (firstBlock N1 N2 x))^2) *
                ((f2 (lastBlock N1 N2 x))^2 * pairSum N2 v (lastBlock N1 N2 x)) := by
            apply integral_congr_ae
            filter_upwards with x
            simp [g, prodState]
            ring
      _ = (∫ u in box N1 L, (f1 u)^2) * (∫ w in box N2 L, (f2 w)^2 * pairSum N2 v w) := by
            exact boxIntegral_prod_fun L (fun u : X N1 => (f1 u)^2)
              (fun w : X N2 => (f2 w)^2 * pairSum N2 v w)
      _ = (∫ u in box N1 L, f1 u * f1 u) * (∫ w in box N2 L, (f2 w)^2 * pairSum N2 v w) := by
            have hp : (∫ u in box N1 L, (f1 u)^2) = ∫ u in box N1 L, f1 u * f1 u := by
              congr 1
              funext u
              rw [pow_two]
            rw [hp]
  -- --------- denominator ---------
  have hden3 : (∫ x in box (N1+N2) L, (g x) * (g x)) =
      (∫ u in box N1 L, f1 u * f1 u) * (∫ w in box N2 L, f2 w * f2 w) := by
    calc
      (∫ x in box (N1+N2) L, (g x) * (g x))
          = ∫ x in box (N1+N2) L, ((f1 (firstBlock N1 N2 x)) * (f1 (firstBlock N1 N2 x))) *
              ((f2 (lastBlock N1 N2 x)) * (f2 (lastBlock N1 N2 x))) := by
            apply integral_congr_ae
            filter_upwards with x
            simp [g, prodState]
            ring
      _ = (∫ u in box N1 L, f1 u * f1 u) * (∫ w in box N2 L, f2 w * f2 w) := by
            exact boxIntegral_prod_fun L (fun u : X N1 => f1 u * f1 u) (fun w : X N2 => f2 w * f2 w)
  -- -------- numerator and quotient --------
  let num1 : ℝ := ∫ u in box N1 L, f1 u * 𝓗 N1 v f1 u
  let den1 : ℝ := ∫ u in box N1 L, f1 u * f1 u
  let num2 : ℝ := ∫ w in box N2 L, f2 w * 𝓗 N2 v f2 w
  let den2 : ℝ := ∫ w in box N2 L, f2 w * f2 w
  let num3 : ℝ := ∫ x in box (N1+N2) L, g x * 𝓗 (N1+N2) v g x
  let den3 : ℝ := ∫ x in box (N1+N2) L, g x * g x
  have hdec1 : num1 = kineticEnergy N1 L Ψ1 + interactionEnergy N1 L v Ψ1 := by
    have h := energy_decomposition_admissible N1 hL (v := v) hv1 Ψ1
    simpa [num1, f1] using h
  have hdec2 : num2 = kineticEnergy N2 L Ψ2 + interactionEnergy N2 L v Ψ2 := by
    have h := energy_decomposition_admissible N2 hL (v := v) hv1 Ψ2
    simpa [num2, f2] using h
  have hdec3 : num3 = kineticEnergy (N1+N2) L Ψ + interactionEnergy (N1+N2) L v Ψ := by
    have h := energy_decomposition_admissible (N1+N2) hL (v := v) hv1 Ψ
    simpa [num3, hg] using h
  have hnum3 : num3 = num1 * den2 + den1 * num2 := by
    calc
      num3 = kineticEnergy (N1+N2) L Ψ + interactionEnergy (N1+N2) L v Ψ := hdec3
      _ = ((∑ i1 : Fin N1, ∫ u in box N1 L, f1 u * (-(partialLaplacian i1 f1 u))) *
            (∫ w in box N2 L, f2 w * f2 w) +
          (∫ u in box N1 L, f1 u * f1 u) *
            (∑ j2 : Fin N2, ∫ w in box N2 L, f2 w * (-(partialLaplacian j2 f2 w)))) +
          ((∫ u in box N1 L, (f1 u)^2 * pairSum N1 v u) * (∫ w in box N2 L, f2 w * f2 w) +
            (∫ u in box N1 L, f1 u * f1 u) * (∫ w in box N2 L, (f2 w)^2 * pairSum N2 v w)) := by
            rw [hK3, hI3, hPval, hQval]
      _ = (kineticEnergy N1 L Ψ1 * den2 + den1 * kineticEnergy N2 L Ψ2) +
            (interactionEnergy N1 L v Ψ1 * den2 + den1 * interactionEnergy N2 L v Ψ2) := by
            have hk1 : (∑ i1 : Fin N1, ∫ u in box N1 L, f1 u * (-(partialLaplacian i1 f1 u))) =
                kineticEnergy N1 L Ψ1 := by
              unfold kineticEnergy
              simp [f1]
            have hk2 : (∑ j2 : Fin N2, ∫ w in box N2 L, f2 w * (-(partialLaplacian j2 f2 w))) =
                kineticEnergy N2 L Ψ2 := by
              unfold kineticEnergy
              simp [f2]
            have hi1 : (∫ u in box N1 L, (f1 u)^2 * pairSum N1 v u) = interactionEnergy N1 L v Ψ1 := by
              unfold interactionEnergy
              simp [f1, pairSum]
            have hi2 : (∫ w in box N2 L, (f2 w)^2 * pairSum N2 v w) = interactionEnergy N2 L v Ψ2 := by
              unfold interactionEnergy
              simp [f2, pairSum]
            rw [hk1, hk2, hi1, hi2]
      _ = (kineticEnergy N1 L Ψ1 + interactionEnergy N1 L v Ψ1) * den2 +
            den1 * (kineticEnergy N2 L Ψ2 + interactionEnergy N2 L v Ψ2) := by
            ring
      _ = num1 * den2 + den1 * num2 := by
            rw [hdec1, hdec2]
  have hden3E : den3 = den1 * den2 := by
    change (∫ x in box (N1+N2) L, g x * g x) =
      (∫ u in box N1 L, f1 u * f1 u) * (∫ w in box N2 L, f2 w * f2 w)
    rw [hden3]
  have hpos1 : 0 < den1 := by
    have h := box_sq_integral_pos (N := N1) hL Ψ1
    simpa [den1, f1] using h
  have hpos2 : 0 < den2 := by
    have h := box_sq_integral_pos (N := N2) hL Ψ2
    simpa [den2, f2] using h
  have hq3 : boxQuot (N1+N2) L v Ψ = num3 / den3 := by
    unfold boxQuot
    have hn : (∫ x in box (N1+N2) L, (Ψ : X (N1+N2)→ℝ) x * 𝓗 (N1+N2) v (Ψ : X (N1+N2)→ℝ) x) = num3 := by
      simp [hg, num3]
    have hd : (∫ x in box (N1+N2) L, (Ψ : X (N1+N2)→ℝ) x * (Ψ : X (N1+N2)→ℝ) x) = den3 := by
      simp [hg, den3]
    have hpos : 0 ≤ den3 := by
      rw [hden3E]
      exact mul_nonneg (le_of_lt hpos1) (le_of_lt hpos2)
    rw [hn, hd]
    rw [Real.sq_sqrt hpos]
  have hq1 : boxQuot N1 L v Ψ1 = num1 / den1 := by
    unfold boxQuot
    have hn : (∫ u in box N1 L, (Ψ1 : X N1 → ℝ) u * 𝓗 N1 v (Ψ1 : X N1 → ℝ) u) = num1 := by
      simp [num1, f1]
    have hd : (∫ u in box N1 L, (Ψ1 : X N1 → ℝ) u * (Ψ1 : X N1 → ℝ) u) = den1 := by
      simp [den1, f1]
    rw [hn, hd]
    rw [Real.sq_sqrt (le_of_lt hpos1)]
  have hq2 : boxQuot N2 L v Ψ2 = num2 / den2 := by
    unfold boxQuot
    have hn : (∫ w in box N2 L, (Ψ2 : X N2 → ℝ) w * 𝓗 N2 v (Ψ2 : X N2 → ℝ) w) = num2 := by
      simp [num2, f2]
    have hd : (∫ w in box N2 L, (Ψ2 : X N2 → ℝ) w * (Ψ2 : X N2 → ℝ) w) = den2 := by
      simp [den2, f2]
    rw [hn, hd]
    rw [Real.sq_sqrt (le_of_lt hpos2)]
  have hq : num3 / den3 = num1 / den1 + num2 / den2 := by
    rw [hnum3, hden3E]
    field_simp [ne_of_gt hpos1, ne_of_gt hpos2]
  rw [hq3, hq1, hq2, hq]


/-! ## 4. Translation invariance of the quotient of a single cell -/

/-- The shifted cell state and the original one have the same Rayleigh quotient. -/
lemma boxQuot_cellShift_eq {N : ℕ} {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (c : ℝ³)
    (hlo : ∀ k : Fin 3, 0 ≤ c k) (hhi : ∀ k : Fin 3, c k + ℓ ≤ L)
    {v : ℝ³ → ℝ} (hv1 : MemLp v 1) (Φ : CInfty0Box N ℓ) :
    boxQuot N L v (shiftedState N c hlo hhi Φ) = boxQuot N ℓ v Φ := by
  let φ : CInfty0Box N L := shiftedState N c hlo hhi Φ
  let f : X N → ℝ := (Φ : X N → ℝ)
  have hφfun : (φ : X N → ℝ) = shiftedCell N c f := by
    simp [φ, f]
  have hdecφ : (∫ x in box N L, (φ : X N → ℝ) x * 𝓗 N v (φ : X N → ℝ) x) =
      kineticEnergy N L φ + interactionEnergy N L v φ :=
    energy_decomposition_admissible N hL (v := v) hv1 φ
  have hdecΦ : (∫ x in box N ℓ, f x * 𝓗 N v f x) =
      kineticEnergy N ℓ Φ + interactionEnergy N ℓ v Φ := by
    have h := energy_decomposition_admissible N hℓ (v := v) hv1 Φ
    simpa [f] using h
  -- per-particle kinetic integrals are invariant
  have hkin_i : ∀ i : Fin N,
      (∫ x in box N L, (φ : X N → ℝ) x * (-(partialLaplacian i (φ : X N → ℝ) x))) =
      (∫ x in box N ℓ, f x * (-(partialLaplacian i f x))) := by
    intro i
    calc
      (∫ x in box N L, (φ : X N → ℝ) x * (-(partialLaplacian i (φ : X N → ℝ) x)))
          = ∫ x : X N, (φ : X N → ℝ) x * (-(partialLaplacian i (φ : X N → ℝ) x)) := by
            apply setIntegral_eq_integral_of_forall_compl_eq_zero
            intro x hx
            have hz : (φ : X N → ℝ) x = 0 := by
              by_contra h2
              exact hx (psi_support_box φ h2)
            simp [hz]
      _ = ∫ x : X N, shiftedCell N c f x * (-(partialLaplacian i (shiftedCell N c f) x)) := by
            rw [hφfun]
      _ = ∫ x : X N, f (cellShift N c x) * (-(partialLaplacian i f (cellShift N c x))) := by
            apply integral_congr_ae
            filter_upwards with x
            have hpl : partialLaplacian i (shiftedCell N c f) x = partialLaplacian i f (cellShift N c x) := by
              change partialLaplacian i (fun y : X N => f (cellShift N c y)) x = partialLaplacian i f (cellShift N c x)
              exact partialLaplacian_cellShift (N := N) c (j := i) (x := x)
            rw [hpl]
            simp [shiftedCell]
      _ = ∫ x : X N, f x * (-(partialLaplacian i f x)) := by
            exact integral_cellShift (N := N) c (fun x => f x * (-(partialLaplacian i f x)))
      _ = (∫ x in box N ℓ, f x * (-(partialLaplacian i f x))) := by
            exact (box_eq_whole_of_state Φ (fun x hz => by simp [f, hz])).symm
  have hkin : kineticEnergy N L φ = kineticEnergy N ℓ Φ := by
    unfold kineticEnergy
    apply Finset.sum_congr rfl
    intro i hi
    simpa [f] using hkin_i i
  -- interaction integrals are invariant
  have hint : interactionEnergy N L v φ = interactionEnergy N ℓ v Φ := by
    calc
      interactionEnergy N L v φ
          = ∫ x in box N L, ((φ : X N → ℝ) x)^2 * pairSum N v x := by
            unfold interactionEnergy pairSum
            rfl
      _ = ∫ x : X N, ((φ : X N → ℝ) x)^2 * pairSum N v x := by
            apply setIntegral_eq_integral_of_forall_compl_eq_zero
            intro x hx
            have hz : (φ : X N → ℝ) x = 0 := by
              by_contra h2
              exact hx (psi_support_box φ h2)
            simp [hz]
      _ = ∫ x : X N, (shiftedCell N c f x)^2 * pairSum N v x := by
            rw [hφfun]
      _ = ∫ x : X N, (fun x => (f x)^2 * pairSum N v x) (cellShift N c x) := by
            apply integral_congr_ae
            filter_upwards with x
            rw [shiftedCell]
            rw [show pairSum N v x = pairSum N v (cellShift N c x) from
              (pairSum_cellShift (N := N) v c x).symm]
      _ = ∫ x : X N, (f x)^2 * pairSum N v x := by
            exact integral_cellShift (N := N) c (fun x => (f x)^2 * pairSum N v x)
      _ = ∫ x in box N ℓ, (f x)^2 * pairSum N v x := by
            exact (box_eq_whole_of_state Φ (fun x hz => by simp [f, hz])).symm
      _ = interactionEnergy N ℓ v Φ := by
            unfold interactionEnergy pairSum
            rfl
  have hden : (∫ x in box N L, (φ : X N → ℝ) x * (φ : X N → ℝ) x) =
      (∫ x in box N ℓ, f x * f x) := by
    calc
      (∫ x in box N L, (φ : X N → ℝ) x * (φ : X N → ℝ) x)
          = ∫ x : X N, (φ : X N → ℝ) x * (φ : X N → ℝ) x := by
            apply setIntegral_eq_integral_of_forall_compl_eq_zero
            intro x hx
            have hz : (φ : X N → ℝ) x = 0 := by
              by_contra h2
              exact hx (psi_support_box φ h2)
            simp [hz]
      _ = ∫ x : X N, shiftedCell N c f x * shiftedCell N c f x := by
            rw [hφfun]
      _ = ∫ x : X N, f (cellShift N c x) * f (cellShift N c x) := rfl
      _ = ∫ x : X N, f x * f x := by
            exact integral_cellShift (N := N) c (fun x => f x * f x)
      _ = (∫ x in box N ℓ, f x * f x) := by
            exact (box_eq_whole_of_state Φ (fun x hz => by simp [f, hz])).symm
  have hnum : (∫ x in box N L, (φ : X N → ℝ) x * 𝓗 N v (φ : X N → ℝ) x) =
      (∫ x in box N ℓ, f x * 𝓗 N v f x) := by
    calc
      (∫ x in box N L, (φ : X N → ℝ) x * 𝓗 N v (φ : X N → ℝ) x)
          = kineticEnergy N L φ + interactionEnergy N L v φ := hdecφ
      _ = kineticEnergy N ℓ Φ + interactionEnergy N ℓ v Φ := by rw [hkin, hint]
      _ = (∫ x in box N ℓ, f x * 𝓗 N v f x) := hdecΦ.symm
  unfold boxQuot
  change ((∫ x in box N L, (φ : X N → ℝ) x * 𝓗 N v (φ : X N → ℝ) x) /
      (Real.sqrt (∫ x in box N L, (φ : X N → ℝ) x * (φ : X N → ℝ) x)) ^ 2) =
    ((∫ x in box N ℓ, f x * 𝓗 N v f x) /
      (Real.sqrt (∫ x in box N ℓ, f x * f x)) ^ 2)
  rw [hnum, hden]


/-! ## 5. The family over `Fin m` -/

/-- `famTotal m n` is the total particle number of the cells `c : Fin m` with counts
`n c`, computed by recursively splitting off the last cell. -/
def famTotal : (m : ℕ) → (Fin m → ℕ) → ℕ
| 0, n => 0
| m+1, n => famTotal m (fun c => n c.castSucc) + n (Fin.last m)

lemma famTotal_eq_sum (m : ℕ) (n : Fin m → ℕ) : famTotal m n = ∑ c : Fin m, n c := by
  induction m with
  | zero => simp [famTotal]
  | succ m ih =>
      calc
        famTotal (m+1) n = famTotal m (fun c => n c.castSucc) + n (Fin.last m) := rfl
        _ = (∑ c : Fin m, n c.castSucc) + n (Fin.last m) := by
              rw [ih (fun c => n c.castSucc)]
        _ = ∑ c : Fin (m+1), n c := by
              rw [Fin.sum_univ_castSucc]

/-- Cell states separated in one coordinate have their `v`-values vanishing
pointwise. -/
lemma v_zero_cell_cell {ℓ R : ℝ} {v : ℝ³ → ℝ} (hR : 0 ≤ R)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R)
    {c d : ℝ³} (hcd : ∃ k : Fin 3, ℓ + R ≤ c k - d k ∨ ℓ + R ≤ d k - c k)
    {x y : ℝ³} (hx : ∀ k : Fin 3, c k ≤ x k ∧ x k ≤ c k + ℓ)
    (hy : ∀ k : Fin 3, d k ≤ y k ∧ y k ≤ d k + ℓ) :
    v (x - y) = 0 := by
  rcases hcd with ⟨k, hk⟩
  rcases hk with hk | hk
  · -- ℓ + R ≤ c k - d k
    have hxmy : R ≤ (x k) - (y k) := by
      have h1 : c k ≥ d k + ℓ + R := by linarith
      have hxlo : c k ≤ x k := (hx k).1
      have hyhi : y k ≤ d k + ℓ := (hy k).2
      nlinarith
    have hxy : R ≤ ‖x - y‖ := by
      have hc : |((x - y) k)| ≤ ‖x - y‖ := abs_coord_le_norm (x - y) k
      have hn : |x k - y k| ≤ ‖x - y‖ := by
        simpa using hc
      have hnonneg : 0 ≤ x k - y k := by linarith
      have habs : |x k - y k| = x k - y k := abs_of_nonneg hnonneg
      rw [habs] at hn
      exact le_trans hxmy hn
    exact v_eq_zero_of_norm_ge hsupp hxy
  · -- ℓ + R ≤ d k - c k
    have hymx : R ≤ (y k) - (x k) := by
      have h1 : d k ≥ c k + ℓ + R := by linarith
      have hylo : d k ≤ y k := (hy k).1
      have hxhi : x k ≤ c k + ℓ := (hx k).2
      nlinarith
    have hyx : R ≤ ‖y - x‖ := by
      have hc : |((y - x) k)| ≤ ‖y - x‖ := abs_coord_le_norm (y - x) k
      have hn : |y k - x k| ≤ ‖y - x‖ := by
        simpa using hc
      have hnonneg : 0 ≤ y k - x k := by linarith
      have habs : |y k - x k| = y k - x k := abs_of_nonneg hnonneg
      rw [habs] at hn
      exact le_trans hymx hn
    have hxy : R ≤ ‖x - y‖ := by
      simpa [norm_sub_rev] using hyx
    exact v_eq_zero_of_norm_ge hsupp hxy

/-- Any particle index in a binary sum lies in the first or in the second block. -/
lemma fin_block_cases (N1 N2 : ℕ) (i : Fin (N1+N2)) :
    (∃ i' : Fin N1, i = Fin.castAdd N2 i') ∨ (∃ j : Fin N2, i = Fin.natAdd N1 j) := by
  by_cases h : i.val < N1
  · left
    refine ⟨⟨i.val, h⟩, ?_⟩
    ext
    simp
  · right
    refine ⟨⟨i.val - N1, by omega⟩, ?_⟩
    ext
    simp
    omega

/-- The constant `1` is an admissible state for the zero-particle box. -/
noncomputable def zeroState (L : ℝ) : CInfty0Box 0 L where
  toFun := fun _ => (1 : ℝ)
  contDiff := (contDiff_const : ContDiff ℝ ∞ (fun _ : X 0 => (1 : ℝ))).contDiffOn
  support := by
    intro x hx
    rw [show box 0 L = (Set.univ : Set (X 0)) by ext y; simp [box]]
    simp
  nezero := by
    intro h
    have hx := congrFun h (fun _ : Fin 0 => (0 : ℝ³))
    norm_num at hx

/-- The recursive raw trial state of the family over `Fin m`. -/
noncomputable def famRaw (ℓ : ℝ) : (m : ℕ) → (n : Fin m → ℕ) → (off : Fin m → ℝ³) →
    (Φ : (c : Fin m) → CInfty0Box (n c) ℓ) → X (famTotal m n) → ℝ
| 0, n, off, Φ => fun _ => 1
| m+1, n, off, Φ =>
    prodState (famTotal m (fun c => n c.castSucc)) (n (Fin.last m))
      (famRaw ℓ m (fun c => n c.castSucc) (fun c => off c.castSucc) (fun c => Φ c.castSucc))
      (shiftedCell (n (Fin.last m)) (off (Fin.last m)) ((Φ (Fin.last m)) : X (n (Fin.last m)) → ℝ))


/-- `boxQuot` depends only on the underlying function. -/
lemma boxQuot_congr {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (Φ1 Φ2 : CInfty0Box N L)
    (h : (Φ1 : X N → ℝ) = (Φ2 : X N → ℝ)) : boxQuot N L v Φ1 = boxQuot N L v Φ2 := by
  unfold boxQuot
  rw [h]

/-- The family property for `Fin m`: existence of the product state, its support
structure (each particle in some cell cube) and the quotient identity. -/
def famGood (m : ℕ) (ℓ L R : ℝ) (v : ℝ³ → ℝ) (hv1 : MemLp v 1)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) (hℓ : 0 < ℓ) (hL : 0 < L) (hR : 0 ≤ R) : Prop :=
  ∀ (n : Fin m → ℕ) (off : Fin m → ℝ³) (Φ : ∀ c : Fin m, CInfty0Box (n c) ℓ),
    (∀ c k, 0 ≤ off c k ∧ off c k + ℓ ≤ L) →
    (∀ ⦃c d : Fin m⦄, c ≠ d →
      ∃ k : Fin 3, ℓ + R ≤ off c k - off d k ∨ ℓ + R ≤ off d k - off c k) →
      (∃ Ψ : CInfty0Box (famTotal m n) L, (Ψ : X (famTotal m n) → ℝ) = famRaw ℓ m n off Φ) ∧
      (∀ x : X (famTotal m n), famRaw ℓ m n off Φ x ≠ 0 →
        ∀ i : Fin (famTotal m n), ∃ c : Fin m,
          ∀ k : Fin 3, off c k ≤ (x i) k ∧ (x i) k ≤ off c k + ℓ) ∧
      (∀ Ψ : CInfty0Box (famTotal m n) L, (Ψ : X (famTotal m n) → ℝ) = famRaw ℓ m n off Φ →
        boxQuot (famTotal m n) L v Ψ = ∑ c : Fin m, boxQuot (n c) ℓ v (Φ c))

/-- `famGood` holds for every `m`. -/
lemma famTotal_succ (m : ℕ) (n : Fin (m+1) → ℕ) :
    famTotal (m+1) n = famTotal m (fun c => n c.castSucc) + n (Fin.last m) := rfl

lemma famRaw_succ (ℓ : ℝ) (m : ℕ) (n : Fin (m+1) → ℕ) (off : Fin (m+1) → ℝ³)
    (Φ : (c : Fin (m+1)) → CInfty0Box (n c) ℓ) :
    famRaw ℓ (m+1) n off Φ =
      prodState (famTotal m (fun c => n c.castSucc)) (n (Fin.last m))
        (famRaw ℓ m (fun c => n c.castSucc) (fun c => off c.castSucc) (fun c => Φ c.castSucc))
        (shiftedCell (n (Fin.last m)) (off (Fin.last m)) ((Φ (Fin.last m)) : X (n (Fin.last m)) → ℝ)) := rfl

/-- `famGood` holds for every `m`. -/
lemma famGood_all (m : ℕ) (ℓ L R : ℝ) (v : ℝ³ → ℝ) (hv1 : MemLp v 1)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) (hℓ : 0 < ℓ) (hL : 0 < L) (hR : 0 ≤ R) :
    famGood m ℓ L R v hv1 hsupp hℓ hL hR := by
  induction m with
  | zero =>
      intro n off Φ hoff hsep
      simp [famTotal]
      constructor
      · refine ⟨zeroState L, ?_⟩
        rfl
      · intro Ψ hΨ
        have hnum : (∫ x in box 0 L, (Ψ : X 0 → ℝ) x * 𝓗 0 v (Ψ : X 0 → ℝ) x) = 0 := by
          have hz : (fun x : X 0 => (Ψ : X 0 → ℝ) x * 𝓗 0 v (Ψ : X 0 → ℝ) x) =ᵐ[volume.restrict (box 0 L)] (fun _ : X 0 => 0) := by
            filter_upwards with x
            have h𝓗 : 𝓗 0 v (Ψ : X 0 → ℝ) x = 0 := by
              unfold _root_.BoseGases.𝓗
              simp
            simp [h𝓗]
          have hc := integral_congr_ae (μ := volume.restrict (box 0 L)) hz
          rw [hc]
          simp
        unfold boxQuot
        rw [hnum]
        simp
  | succ m ih =>
      intro n off Φ hoff hsep
      simp [famTotal]
      have hoff' : ∀ (c : Fin m) (k : Fin 3), 0 ≤ off (c.castSucc) k ∧ off (c.castSucc) k + ℓ ≤ L := by
        intro c k
        exact hoff (c.castSucc) k
      have hsep' : ∀ ⦃c d : Fin m⦄, c ≠ d →
          ∃ k : Fin 3, ℓ + R ≤ off (c.castSucc) k - off (d.castSucc) k ∨
            ℓ + R ≤ off (d.castSucc) k - off (c.castSucc) k := by
        intro c d hcd
        have hne : c.castSucc ≠ d.castSucc := by
          intro h
          apply hcd
          have hv := congrArg Fin.val h
          simp at hv
          exact Fin.ext hv
        exact hsep (c := c.castSucc) (d := d.castSucc) hne
      rcases ih (fun c => n c.castSucc) (fun c => off c.castSucc) (fun c => Φ c.castSucc) hoff' hsep'
        with ⟨hT1, hT2, hT3⟩
      rcases hT1 with ⟨Ψt, hΨt⟩
      let Ψlast : CInfty0Box (n (Fin.last m)) L :=
        shiftedState (n (Fin.last m)) (off (Fin.last m))
          (fun k => (hoff (Fin.last m) k).1) (fun k => (hoff (Fin.last m) k).2) (Φ (Fin.last m))
      have hΨlast : (Ψlast : X (n (Fin.last m)) → ℝ) =
          shiftedCell (n (Fin.last m)) (off (Fin.last m)) ((Φ (Fin.last m)) : X (n (Fin.last m)) → ℝ) := by
        simp [Ψlast]
      let Ψtensor : CInfty0Box (famTotal m (fun c => n c.castSucc) + n (Fin.last m)) L :=
        tensorState (famTotal m (fun c => n c.castSucc)) (n (Fin.last m)) hL Ψt Ψlast
      have hΨtensor : (Ψtensor : X (famTotal m (fun c => n c.castSucc) + n (Fin.last m)) → ℝ) =
          famRaw ℓ (m+1) n off Φ := by
        rw [famRaw_succ]
        simp [Ψtensor, hΨt, Ψlast]
      -- ---- cross separation ----
      have hcross : ∀ u w, (Ψt : X (famTotal m (fun c => n c.castSucc)) → ℝ) u ≠ 0 →
          (Ψlast : X (n (Fin.last m)) → ℝ) w ≠ 0 →
          ∀ i : Fin (famTotal m (fun c => n c.castSucc)), ∀ j : Fin (n (Fin.last m)),
            v (u i - w j) = 0 := by
        intro u w hu hw i j
        have hu' : famRaw ℓ m (fun c => n c.castSucc) (fun c => off c.castSucc) (fun c => Φ c.castSucc) u ≠ 0 := by
          simpa [hΨt] using hu
        rcases hT2 u hu' i with ⟨c', hc'⟩
        have hw' : shiftedCell (n (Fin.last m)) (off (Fin.last m)) ((Φ (Fin.last m)) : X (n (Fin.last m)) → ℝ) w ≠ 0 := by
          simpa [hΨlast] using hw
        have hwj : ∀ k : Fin 3, off (Fin.last m) k ≤ (w j) k ∧ (w j) k ≤ off (Fin.last m) k + ℓ :=
          shiftedCell_support_cube (Φ (Fin.last m)) (off (Fin.last m)) hw' j
        have hne : c'.castSucc ≠ Fin.last m := by
          intro h
          have hv := congrArg Fin.val h
          simp at hv
          omega
        rcases hsep hne with ⟨k, hk⟩
        exact v_zero_cell_cell (ℓ := ℓ) hR hsupp (c := off (c'.castSucc)) (d := off (Fin.last m))
          ⟨k, hk⟩ (fun kk => hc' kk) hwj
      -- ---- quotient identity ----
      have hqT : boxQuot (famTotal m (fun c => n c.castSucc) + n (Fin.last m)) L v Ψtensor =
          boxQuot (famTotal m (fun c => n c.castSucc)) L v Ψt +
            boxQuot (n (Fin.last m)) L v Ψlast := by
        simpa [Ψtensor] using
          (tensorQuot (N1 := famTotal m (fun c => n c.castSucc)) (N2 := n (Fin.last m)) hL (v := v) hv1 Ψt Ψlast hcross)
      have hqT3 : boxQuot (famTotal m (fun c => n c.castSucc)) L v Ψt =
          ∑ c : Fin m, boxQuot (n (c.castSucc)) ℓ v (Φ (c.castSucc)) := by
        simpa using (hT3 Ψt hΨt)
      have hqL : boxQuot (n (Fin.last m)) L v Ψlast =
          boxQuot (n (Fin.last m)) ℓ v (Φ (Fin.last m)) := by
        have h := boxQuot_cellShift_eq (N := n (Fin.last m)) hℓ hL (off (Fin.last m))
          (fun k => (hoff (Fin.last m) k).1) (fun k => (hoff (Fin.last m) k).2) (v := v) hv1 (Φ (Fin.last m))
        simpa [Ψlast] using h
      constructor
      · refine ⟨Ψtensor, ?_⟩
        simpa using hΨtensor
      · constructor
        · intro x hx i
          rcases fin_block_cases (famTotal m (fun c => n c.castSucc)) (n (Fin.last m)) i with hi | hj
          · rcases hi with ⟨i', hi⟩
            have hfirst : famRaw ℓ m (fun c => n c.castSucc) (fun c => off c.castSucc) (fun c => Φ c.castSucc)
                  (firstBlock (famTotal m (fun c => n c.castSucc)) (n (Fin.last m)) x) ≠ 0 ∧
                shiftedCell (n (Fin.last m)) (off (Fin.last m)) ((Φ (Fin.last m)) : X (n (Fin.last m)) → ℝ)
                  (lastBlock (famTotal m (fun c => n c.castSucc)) (n (Fin.last m)) x) ≠ 0 := by
              have hz := support_prodState
                (famRaw ℓ m (fun c => n c.castSucc) (fun c => off c.castSucc) (fun c => Φ c.castSucc))
                (shiftedCell (n (Fin.last m)) (off (Fin.last m)) ((Φ (Fin.last m)) : X (n (Fin.last m)) → ℝ)) x hx
              simpa [famRaw] using hz
            rcases hT2 (firstBlock (famTotal m (fun c => n c.castSucc)) (n (Fin.last m)) x) hfirst.1 i' with ⟨c', hc'⟩
            refine ⟨c'.castSucc, ?_⟩
            intro kk
            have hc := hc' kk
            simpa [hi, firstBlock] using hc
          · rcases hj with ⟨j, hj⟩
            have hlast : shiftedCell (n (Fin.last m)) (off (Fin.last m)) ((Φ (Fin.last m)) : X (n (Fin.last m)) → ℝ)
                (lastBlock (famTotal m (fun c => n c.castSucc)) (n (Fin.last m)) x) ≠ 0 := by
              have h := support_prodState
                (famRaw ℓ m (fun c => n c.castSucc) (fun c => off c.castSucc) (fun c => Φ c.castSucc))
                (shiftedCell (n (Fin.last m)) (off (Fin.last m)) ((Φ (Fin.last m)) : X (n (Fin.last m)) → ℝ)) x hx
              exact h.2
            refine ⟨Fin.last m, ?_⟩
            intro kk
            have hw := shiftedCell_support_cube (Φ (Fin.last m)) (off (Fin.last m)) hlast j
            simpa [hj, lastBlock] using hw kk
        · intro Ψ hΨ
          have hqΨ : boxQuot (famTotal (m+1) n) L v Ψ = boxQuot (famTotal m (fun c => n c.castSucc) + n (Fin.last m)) L v Ψtensor := by
            apply boxQuot_congr
            rw [hΨ]
            exact hΨtensor.symm
          calc
            boxQuot (famTotal (m+1) n) L v Ψ
                = boxQuot (famTotal m (fun c => n c.castSucc) + n (Fin.last m)) L v Ψtensor := hqΨ
            _ = boxQuot (famTotal m (fun c => n c.castSucc)) L v Ψt +
                  boxQuot (n (Fin.last m)) L v Ψlast := hqT
            _ = (∑ c : Fin m, boxQuot (n (c.castSucc)) ℓ v (Φ (c.castSucc))) +
                  boxQuot (n (Fin.last m)) ℓ v (Φ (Fin.last m)) := by
                  rw [hqT3, hqL]
            _ = ∑ c : Fin (m+1), boxQuot (n c) ℓ v (Φ c) := by
                  have hsumsplit := Fin.sum_univ_castSucc (f := fun c : Fin (m+1) => boxQuot (n c) ℓ v (Φ c))
                  simpa using hsumsplit.symm


/-! ## 6. Closing the inequality -/

/-- Extend a tail family (cells `c.castSucc`) with a state for the last cell. -/
noncomputable def famLast (ℓ : ℝ) (m : ℕ) (n : Fin (m+1) → ℕ)
    (Φ' : (c : Fin m) → CInfty0Box (n c.castSucc) ℓ) (Φ0 : CInfty0Box (n (Fin.last m)) ℓ) :
    (c : Fin (m+1)) → CInfty0Box (n c) ℓ :=
  fun c => if h : c = Fin.last m then (h ▸ Φ0) else Φ' ⟨c.val, by
    have hle : c.val ≤ m := Nat.le_of_lt_succ c.isLt
    have hne : c.val ≠ m := by
      intro hcm
      apply h
      ext
      exact hcm
    exact Nat.lt_of_le_of_ne hle hne⟩

lemma famLast_castSucc (ℓ : ℝ) (m : ℕ) (n : Fin (m+1) → ℕ)
    (Φ' : (c : Fin m) → CInfty0Box (n c.castSucc) ℓ) (Φ0 : CInfty0Box (n (Fin.last m)) ℓ)
    (c : Fin m) :
    famLast ℓ m n Φ' Φ0 (c.castSucc) = Φ' c := by
  unfold famLast
  rw [dif_neg]
  · congr
  · intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega

lemma famLast_last (ℓ : ℝ) (m : ℕ) (n : Fin (m+1) → ℕ)
    (Φ' : (c : Fin m) → CInfty0Box (n c.castSucc) ℓ) (Φ0 : CInfty0Box (n (Fin.last m)) ℓ) :
    famLast ℓ m n Φ' Φ0 (Fin.last m) = Φ0 := by
  unfold famLast
  rw [dif_pos rfl]

/-- One particle space at a time: if a constant is bounded by every sum of
quotients, it is bounded by the sum of the energies. -/
lemma peel_fin (ℓ : ℝ) (hℓ : 0 < ℓ) (v : ℝ³ → ℝ) :
    ∀ (m : ℕ) (n : Fin m → ℕ) (A : ℝ),
      (∀ Φ : (c : Fin m) → CInfty0Box (n c) ℓ,
        A ≤ ∑ c : Fin m, boxQuot (n c) ℓ v (Φ c)) →
      A ≤ ∑ c : Fin m, boxEnergy (n c) ℓ v := by
  intro m
  induction m with
  | zero =>
      intro n A hmain
      have hz := hmain (fun c : Fin 0 => (nonempty_CInfty0Box (n c) hℓ).some)
      simpa using hz
  | succ m ih =>
      intro n A hmain
      let n' : Fin m → ℕ := fun c => n (c.castSucc)
      let E_last : ℝ := boxEnergy (n (Fin.last m)) ℓ v
      have hA0 : ∀ Φ' : (c : Fin m) → CInfty0Box (n' c) ℓ,
          A - E_last ≤ ∑ c : Fin m, boxQuot (n' c) ℓ v (Φ' c) := by
        intro Φ'
        have hle1 : A - (∑ c : Fin m, boxQuot (n' c) ℓ v (Φ' c)) ≤ E_last := by
          dsimp [E_last]
          haveI : Nonempty (CInfty0Box (n (Fin.last m)) ℓ) := nonempty_CInfty0Box (n (Fin.last m)) hℓ
          rw [boxEnergy_eq_ciInf_boxQuot]
          apply le_ciInf
          intro Φ0
          have hfull := hmain (famLast ℓ m n (fun c => Φ' c) Φ0)
          have hsplit := Fin.sum_univ_castSucc
            (f := fun c : Fin (m+1) => boxQuot (n c) ℓ v (famLast ℓ m n (fun c => Φ' c) Φ0 c))
          -- hsplit : Σ over Fin(m+1) = Σ over Fin m + last
          have hrew : (∑ c : Fin m, boxQuot (n (c.castSucc)) ℓ v (famLast ℓ m n (fun c => Φ' c) Φ0 (c.castSucc))) +
                boxQuot (n (Fin.last m)) ℓ v (famLast ℓ m n (fun c => Φ' c) Φ0 (Fin.last m)) =
              (∑ c : Fin m, boxQuot (n' c) ℓ v (Φ' c)) + boxQuot (n (Fin.last m)) ℓ v Φ0 := by
            congr 1
            · apply Finset.sum_congr rfl
              intro c hc
              rw [famLast_castSucc]
            · rw [famLast_last]
          have hfull' : A ≤ (∑ c : Fin m, boxQuot (n' c) ℓ v (Φ' c)) + boxQuot (n (Fin.last m)) ℓ v Φ0 := by
            linarith [hfull, hsplit, hrew]
          linarith
        linarith
      have ihn' := ih n' (A - E_last) hA0
      -- ihn' : A - E_last ≤ ∑ c : Fin m, boxEnergy (n' c) ℓ v
      have hsplit2 := Fin.sum_univ_castSucc (f := fun c : Fin (m+1) => boxEnergy (n c) ℓ v)
      -- conclusion: A ≤ Σ over Fin (m+1) boxEnergy (n c) ℓ v
      rw [hsplit2]
      dsimp [E_last] at ihn' ⊢
      linarith


/-- For a family over `Fin m`: the energy of the whole box is at most the sum of
the cell energies. -/
lemma fam_energy_le (m : ℕ) {ℓ L R : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hR : 0 ≤ R)
    {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R)
    (n : Fin m → ℕ) (off : Fin m → ℝ³)
    (hoff : ∀ c k, 0 ≤ off c k ∧ off c k + ℓ ≤ L)
    (hsep : ∀ ⦃c d : Fin m⦄, c ≠ d →
      ∃ k : Fin 3, ℓ + R ≤ off c k - off d k ∨ ℓ + R ≤ off d k - off c k) :
    boxEnergy (famTotal m n) L v ≤ ∑ c : Fin m, boxEnergy (n c) ℓ v := by
  have hmain : ∀ (Φ : (c : Fin m) → CInfty0Box (n c) ℓ),
      boxEnergy (famTotal m n) L v ≤ ∑ c : Fin m, boxQuot (n c) ℓ v (Φ c) := by
    intro Φ
    have hg := famGood_all m ℓ L R v hv1 hsupp hℓ hL hR n off Φ hoff hsep
    rcases hg with ⟨hT1, hT2, hT3⟩
    rcases hT1 with ⟨Ψ, hΨ⟩
    have hbdd : BddBelow (Set.range (boxQuot (famTotal m n) L v)) := by
      refine ⟨0, ?_⟩
      rintro y ⟨Ψ0, rfl⟩
      exact boxQuot_nonneg hL hv Ψ0
    have hinf : boxEnergy (famTotal m n) L v ≤ boxQuot (famTotal m n) L v Ψ := by
      rw [boxEnergy_eq_ciInf_boxQuot]
      exact ciInf_le hbdd Ψ
    calc
      boxEnergy (famTotal m n) L v ≤ boxQuot (famTotal m n) L v Ψ := hinf
      _ = ∑ c : Fin m, boxQuot (n c) ℓ v (Φ c) := hT3 Ψ hΨ
  exact peel_fin ℓ hℓ v m n (boxEnergy (famTotal m n) L v) hmain

/-- The cells-subadditivity statement for cells enumerated by `Fin m`. -/
lemma cells_subadd_fin (m : ℕ) {L ℓ R : ℝ} {off : Fin m → ℝ³}
    (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hL : 0 < L)
    (hoff : ∀ c k, 0 ≤ off c k ∧ off c k + ℓ ≤ L)
    (hsep : ∀ ⦃c d : Fin m⦄, c ≠ d →
      ∃ k : Fin 3, ℓ + R ≤ off c k - off d k ∨ ℓ + R ≤ off d k - off c k)
    {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) (n : Fin m → ℕ) :
    boxEnergy (∑ c : Fin m, n c) L v ≤ ∑ c : Fin m, boxEnergy (n c) ℓ v := by
  have htot : famTotal m n = ∑ c : Fin m, n c := famTotal_eq_sum m n
  rw [← htot]
  exact fam_energy_le m hℓ hL hR hv hv1 hsupp n off hoff hsep


/-- The general multi-cell statement, reduced to an arbitrary finite index type. -/
lemma boxEnergy_cells_subadd_general {ι : Type*} [Fintype ι]
    (n : ι → ℕ) {L ℓ R : ℝ} {off : ι → ℝ³}
    (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hL : 0 < L)
    (hoff : ∀ j k, 0 ≤ off j k ∧ off j k + ℓ ≤ L)
    (hsep : ∀ ⦃j j' : ι⦄, j ≠ j' →
      ∃ k : Fin 3, ℓ + R ≤ off j k - off j' k ∨ ℓ + R ≤ off j' k - off j k)
    {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) :
    boxEnergy (∑ j : ι, n j) L v ≤ ∑ j : ι, boxEnergy (n j) ℓ v := by
  let m : ℕ := Fintype.card ι
  let e : ι ≃ Fin m := Fintype.equivFin ι
  let n' : Fin m → ℕ := fun c => n (e.symm c)
  let off' : Fin m → ℝ³ := fun c => off (e.symm c)
  have hoff' : ∀ c k, 0 ≤ off' c k ∧ off' c k + ℓ ≤ L := by
    intro c k
    simpa [off'] using (hoff (e.symm c) k)
  have hsep' : ∀ ⦃c d : Fin m⦄, c ≠ d →
      ∃ k : Fin 3, ℓ + R ≤ off' c k - off' d k ∨ ℓ + R ≤ off' d k - off' c k := by
    intro c d hcd
    have hne : e.symm c ≠ e.symm d := by
      intro h
      apply hcd
      exact (Equiv.injective (e.symm)) h
    have hh := hsep (j := e.symm c) (j' := e.symm d) hne
    simpa [off'] using hh
  have hineq := cells_subadd_fin m hℓ hR hL hoff' hsep' hv hv1 hsupp n'
  have hsum1 : (∑ c : Fin m, n' c) = ∑ j : ι, n j := by
    -- ∑ over Fin m of n (e.symm c) = ∑ over ι of n j (reindex by e)
    symm
    -- ∑ j : ι, n j = ∑ c : Fin m, n' c
    apply Finset.sum_bij (s := (Finset.univ : Finset ι)) (t := (Finset.univ : Finset (Fin m)))
      (i := fun j hj => e j)
    · intro j hj
      simp
    · intro j hj j' hj' h
      exact e.injective h
    · intro c hc
      refine ⟨e.symm c, by simp, ?_⟩
      simp
    · intro j hj
      simp [n']
  have hsum2 : (∑ c : Fin m, boxEnergy (n' c) ℓ v) = ∑ j : ι, boxEnergy (n j) ℓ v := by
    apply Finset.sum_bij (s := (Finset.univ : Finset (Fin m))) (t := (Finset.univ : Finset ι))
      (i := fun c hc => e.symm c)
    · intro c hc
      simp
    · intro c hc d hd h
      exact (Equiv.injective (e.symm)) h
    · intro j hj
      refine ⟨e j, by simp, ?_⟩
      simp
    · intro c hc
      simp [n']
  rw [hsum1, hsum2] at hineq
  exact hineq
/-- Multi-cell (grid) subadditivity.

Let `ι` be a finite nonempty index type for the cells.  Each cell `j` is an
open cube of side `ℓ` placed at the offset `off j` (its `k`-th coordinate
interval is `[off j k, off j k + ℓ]`).  Hypotheses:

* `hoff`: every cell fits inside the cube `[0, L]³` (`0 ≤ off j k` and
  `off j k + ℓ ≤ L`);
* `hsep`: any two distinct cells are separated by at least `ℓ + R` in some
  coordinate, so that the distance between points of distinct cells is `≥ R`;
* `0 ≤ v`, `MemLp v 1`, support of `v` inside `ball 0 R`.

Then the energy of `Σ_j n j` particles in the large cube of side `L` is at
most the sum over the cells of the energies of `n j` particles in a cube of
side `ℓ`. -/
lemma boxEnergy_cells_subadd {ι : Type*} [Fintype ι] [Nonempty ι]
    (n : ι → ℕ) {L ℓ R : ℝ} {off : ι → EuclideanSpace ℝ (Fin 3)}
    (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hL : 0 < L)
    (hoff : ∀ j k, 0 ≤ off j k ∧ off j k + ℓ ≤ L)
    (hsep : ∀ ⦃j j' : ι⦄, j ≠ j' →
      ∃ k : Fin 3, ℓ + R ≤ off j k - off j' k ∨ ℓ + R ≤ off j' k - off j k)
    {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) :
    boxEnergy (∑ j : ι, n j) L v ≤ ∑ j : ι, boxEnergy (n j) ℓ v := by
  exact boxEnergy_cells_subadd_general (ι := ι) n hℓ hR hL hoff hsep hv hv1 hsupp

end BoseGases

end Submission
