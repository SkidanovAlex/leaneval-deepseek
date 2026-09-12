import Mathlib
import Submission.CorAc2
import Submission.Section5DProd
import Submission.MagicVector
import Submission.NormalSplit
import Submission.IncompReduction
import Submission.Commons.LinearAlgebra.Net.spread_permutations
import Submission.NetInvariance
import Submission.Commons.Probability.Independence.tensorization_linear

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Measure Filter unitInterval

namespace Submission.NetArgument

attribute [local instance] Classical.propDecidable

open Submission.Admissible
open Submission.Section5D
open Submission.MagicVector
open Commons.LinearAlgebra.Net

/-!
# Section 5e: the net argument for Theorem A

This module formalizes the counting part of the net argument in the proof of
Tikhomirov's Theorem A: the good lattice points `Dset`, the covering property
of the special-permutation net, the cardinality bound, and (later) the
per-annulus probability bound.
-/

/-- Slope constant of the net points (`40 · 3`). -/
noncomputable def cSlope : ℝ := 120

/-- The small-ball slope condition on a lattice point `y`: the Bernoulli sum
`Σ b_i y_i` has concentration at most `(C·L·T/√n)·τ` for all `τ ≥ √n`,
with the center `-s·Σ y_i`. -/
def slopeOk {n : ℕ} (p : unitInterval) (s L T : ℝ) (y : Fin n → ℤ) : Prop :=
  ∀ τ : ℝ, Real.sqrt (n : ℝ) ≤ τ →
    bMass p (slabB (fun i : Fin n => (y i : ℝ))
        (-(s * ∑ i : Fin n, (y i : ℝ))) τ)
      ≤ (cSlope * L * T / Real.sqrt (n : ℝ)) * τ

/-- The lattice points whose concentration at `√n` is at least `LAC/N`. -/
def cfGood {n : ℕ} (p : unitInterval) (LAC : ℝ) (N : ℕ) (A : Fin n → Finset ℤ) :
    Finset (Fin n → ℤ) :=
  @Finset.filter (Fin n → ℤ)
    (fun y : Fin n → ℤ => ENNReal.ofReal (LAC / (N : ℝ)) ≤
      Submission.Threshold.cfP (n := n) p (fun i : Fin n => (y i : ℝ)) (Real.sqrt (n : ℝ)))
    (Classical.decPred _) (Submission.ProdCount.prodFinset n A)

/-- The set `D` of good lattice points in the family `A`: those whose
concentration at `√n` is at least `LAC/N` and whose Bernoulli sum obeys the
slope bound. -/
def Dset {n : ℕ} (p : unitInterval) (s L T LAC : ℝ) (N : ℕ) (A : Fin n → Finset ℤ) :
    Finset (Fin n → ℤ) :=
  @Finset.filter (Fin n → ℤ)
    (fun y : Fin n → ℤ => slopeOk p s L T y) (Classical.decPred _) (cfGood p LAC N A)

/-- Unfolding of `cfCount` with a canonical decidability instance. -/
lemma cfCount_eq {n : ℕ} (LAC : ℝ) (N : ℕ) (p : unitInterval) (A : Fin n → Finset ℤ) :
    Submission.CorAc2.cfCount LAC N n p A
      = (@Finset.filter (Fin n → ℤ)
          (fun x : Fin n → ℤ => ENNReal.ofReal (LAC / (N : ℝ)) ≤
            Submission.Threshold.cfP (n := n) p (fun i : Fin n => (x i : ℝ))
              (Real.sqrt (n : ℝ))) (Classical.decPred _)
          (Submission.ProdCount.prodFinset n A)).card := by
  unfold Submission.CorAc2.cfCount
  rw [Finset.filter_congr_decidable]

/-- `Dset` is contained in the `cfCount` set of `cor: anticoncentration`. -/
lemma Dset_card_le_cfCount {n : ℕ} (p : unitInterval) (s L T LAC : ℝ) (N : ℕ)
    (A : Fin n → Finset ℤ) :
    (Dset p s L T LAC N A).card ≤ Submission.CorAc2.cfCount LAC N n p A := by
  have h1 : (Dset p s L T LAC N A).card ≤ (cfGood p LAC N A).card := by
    rw [Dset]
    apply Finset.card_le_card
    intro y hy
    exact (Finset.mem_filter.mp hy).1
  have h2 : (cfGood p LAC N A).card ≤ Submission.CorAc2.cfCount LAC N n p A := by
    rw [cfCount_eq, cfGood]
  exact le_trans h1 h2

/-- **Cardinality of the good set**: for `N = holeN ν T` in the admissible
range, the number of good lattice points is at most
`exp(-M·n)·(K_A·N)^n`. -/
theorem Dset_card_le {p : unitInterval} {ε : ℝ} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    (hε₀ : 0 < ε) (hεp : ε < (p : ℝ))
    {δ ν : ℝ} (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2) (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    {M : ℝ} (hM : 1 ≤ M) :
    ∃ LAC : ℝ, 0 < LAC ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∃ K_A : ℝ, 1 ≤ K_A ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ T : ℝ, 0 < T → T ≤ ν / 2 →
        ((holeN ν T : ℝ) ≤ (1 / (1 - (p : ℝ) + ε)) ^ n) → ∀ (s L : ℝ),
          ((Dset p s L T LAC (holeN ν T) (Acoord n δ ν T)).card : ℝ)
            ≤ Real.exp (-M * (n : ℝ)) * (K_A * (holeN ν T : ℝ)) ^ n := by
  rcases Submission.CorAc2.cor_anticoncentration hp₀ hp₁ hδ0 hδ12 hε₀ hεp with
    ⟨LAC, hLACpos, hbody⟩
  rcases hbody M hM with ⟨η, nAC, hη, hnAC1, hAC⟩
  rcases Submission.Section5D.Acoord_hrad hδ0 hδ12 hν0 hν1 with ⟨nrad, hnrad1, hradb⟩
  rcases Submission.Section5D.Acoord_prod_bound hδ0 hδ12 hν0 hν1 with
    ⟨KA, hKA1, nprod, hnprod1, hprodb⟩
  refine ⟨LAC, hLACpos, max (max nAC nrad) nprod, ?_, KA, hKA1, ?_⟩
  · omega
  · intro n hn T hT0 hTν hNa s L
    have hnAC : nAC ≤ n := le_trans (le_trans (le_max_left nAC nrad) (le_max_left _ _)) hn
    have hnrad : nrad ≤ n := le_trans (le_trans (le_max_right nAC nrad) (le_max_left _ _)) hn
    have hnprod : nprod ≤ n := le_trans (le_max_right _ _) hn
    have hN1 : 1 ≤ holeN ν T := Submission.Section5D.holeN_ge_one hT0 hν0 hTν
    have hAdm : Admissible (holeN ν T) n n δ (Acoord n δ ν T) :=
      Submission.Section5D.Acoord_admissible hδ0 hδ12 hν0 hν1 n T hT0 hTν
    have hrad : ∀ j : Fin n, ∀ a : ℤ, a ∈ Acoord n δ ν T j →
        |a| ≤ ((n * holeN ν T : ℕ) : ℤ) := by
      intro j a ha
      exact hradb n hnrad T hT0 hTν j a ha
    have hsym : ∀ j : Fin n, ∀ a : ℤ, a ∈ Acoord n δ ν T j → -a ∈ Acoord n δ ν T j := by
      intro j a ha
      exact Submission.Section5D.Acoord_symm ha
    have hcf := hAC n hnAC (holeN ν T) hN1 hNa (Acoord n δ ν T) hAdm hrad hsym
    have hcard : ((Dset p s L T LAC (holeN ν T) (Acoord n δ ν T)).card : ℝ)
        ≤ (Submission.CorAc2.cfCount LAC (holeN ν T) n p (Acoord n δ ν T) : ℝ) := by
      exact_mod_cast Dset_card_le_cfCount p s L T LAC (holeN ν T) (Acoord n δ ν T)
    have hprod := hprodb n hnprod T hT0 hTν
    have hexp0 : (0 : ℝ) ≤ Real.exp (-M * (n : ℝ)) := le_of_lt (Real.exp_pos _)
    calc ((Dset p s L T LAC (holeN ν T) (Acoord n δ ν T)).card : ℝ)
        ≤ (Submission.CorAc2.cfCount LAC (holeN ν T) n p (Acoord n δ ν T) : ℝ) := hcard
      _ ≤ Real.exp (-M * (n : ℝ)) * (∏ j : Fin n, (((Acoord n δ ν T j).card : ℕ) : ℝ)) := hcf
      _ ≤ Real.exp (-M * (n : ℝ)) * (KA * (holeN ν T : ℝ)) ^ n :=
          mul_le_mul_of_nonneg_left hprod hexp0

/-- The slope condition is invariant under coordinate permutations. -/
lemma slopeOk_comp_perm {n : ℕ} (π : Equiv.Perm (Fin n)) (p : unitInterval) (s L T : ℝ)
    (y : Fin n → ℤ) :
    slopeOk p s L T (fun i : Fin n => y (π i)) ↔ slopeOk p s L T y := by
  have hsum : (∑ i : Fin n, ((y (π i) : ℤ) : ℝ)) = ∑ i : Fin n, ((y i : ℤ) : ℝ) := by
    exact_mod_cast Submission.NetInvariance.sum_comp_perm π y
  unfold slopeOk
  constructor
  · intro h τ hτ
    have h' := h τ hτ
    rw [hsum] at h'
    rwa [Submission.NetInvariance.bMass_slabB_comp_perm p π
      (fun j : Fin n => ((y j : ℤ) : ℝ)) (-(s * ∑ i : Fin n, ((y i : ℤ) : ℝ))) τ] at h'
  · intro h τ hτ
    have h' := h τ hτ
    rw [← Submission.NetInvariance.bMass_slabB_comp_perm p π
      (fun j : Fin n => ((y j : ℤ) : ℝ)) (-(s * ∑ i : Fin n, ((y i : ℤ) : ℝ))) τ] at h'
    rwa [← hsum] at h'

/-- The integer sub-sum cast as a real sub-sum. -/
lemma rSub_cast_eq {n : ℕ} (z : Fin n → ℤ) (B : Finset (Fin n)) :
    rSub (fun i : Fin n => (z i : ℝ)) B = ((Submission.Sec3.subSum z B : ℤ) : ℝ) := by
  rw [Submission.SlabBridge.cast_subSum]
  rfl

/-- membership in `goodSubsets` via the subset-sum. -/
lemma mem_goodSubsets {n : ℕ} {z : Fin n → ℤ} {lam R : ℝ} {B : Finset (Fin n)} :
    B ∈ Submission.SlabBridge.goodSubsets (x := z) lam R ↔
      |((Submission.Sec3.subSum z B : ℤ) : ℝ) - lam| ≤ R := by
  unfold Submission.SlabBridge.goodSubsets
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ B), h⟩

/-- the Bernoulli mass of a slab family equals the slab weight. -/
lemma bMass_slabB_eq_slabWeight {n : ℕ} (p : unitInterval) (z : Fin n → ℤ) (lam R : ℝ) :
    bMass p (slabB (fun i : Fin n => (z i : ℝ)) lam R)
      = Submission.SlabBridge.slabWeight p z lam R := by
  have hF : slabB (fun i : Fin n => (z i : ℝ)) lam R
      = Submission.SlabBridge.goodSubsets (x := z) lam R := by
    ext B
    rw [Submission.NetInvariance.mem_slabB, mem_goodSubsets, rSub_cast_eq]
  unfold Submission.SlabBridge.slabWeight bMass
  rw [hF]

/-- The concentration function is invariant under coordinate permutations. -/
lemma cfP_comp_perm {n : ℕ} (π : Equiv.Perm (Fin n)) (p : unitInterval) (z : Fin n → ℤ)
    (t : ℝ) :
    Submission.Threshold.cfP p (fun i : Fin n => (z (π i) : ℝ)) t
      = Submission.Threshold.cfP p (fun i : Fin n => (z i : ℝ)) t := by
  have hpoint : ∀ l : ℝ,
      (Submission.Threshold.berP (n := n) p)
          (Submission.ThresholdMeas.slabEvent (fun i : Fin n => (z (π i) : ℝ)) l t)
        = (Submission.Threshold.berP (n := n) p)
          (Submission.ThresholdMeas.slabEvent (fun i : Fin n => (z i : ℝ)) l t) := by
    intro l
    rw [Submission.SlabBridge.slab_enn_eq_weight p (fun i : Fin n => z (π i)) l t,
      Submission.SlabBridge.slab_enn_eq_weight p z l t]
    congr 1
    rw [← bMass_slabB_eq_slabWeight p (fun i : Fin n => z (π i)) l t,
      ← bMass_slabB_eq_slabWeight p z l t]
    exact Submission.NetInvariance.bMass_slabB_comp_perm p π
      (fun j : Fin n => (z j : ℝ)) l t
  unfold Submission.Threshold.cfP Submission.Helpers.levyConcentration
  congr 1
  ext a
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨l, hpoint l⟩
  · rintro ⟨l, rfl⟩
    exact ⟨l, (hpoint l).symm⟩

/-- The law of the row map is the canonical Bernoulli product measure. -/
lemma map_row_eq_berP {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {p : unitInterval} {b : Fin n → Ω → ℝ}
    (hmeas : ∀ j : Fin n, Measurable (b j)) (hind : ProbabilityTheory.iIndepFun b P)
    (hlaw : ∀ j : Fin n, HasLaw (b j) (bernoulliMeasure 1 0 p) P) :
    P.map (fun ω : Ω => fun j : Fin n => b j ω) = Submission.Threshold.berP (n := n) p := by
  have h := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (f := fun j : Fin n => fun ω : Ω => b j ω)
    (fun j => (hmeas j).aemeasurable)).1 hind
  rw [h]
  unfold Submission.Threshold.berP
  congr 1
  funext j
  exact (hlaw j).map_eq

/-- Per-row small-ball bound coming from the slope condition on `y`. -/
lemma row_smallball {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {p : unitInterval} {s L T : ℝ} {y : Fin n → ℤ}
    (hslope : slopeOk p s L T y) {b : Fin n → Ω → ℝ}
    (hmeas : ∀ j : Fin n, Measurable (b j)) (hind : ProbabilityTheory.iIndepFun b P)
    (hlaw : ∀ j : Fin n, HasLaw (b j) (bernoulliMeasure 1 0 p) P) {τ : ℝ}
    (hτ : Real.sqrt (n : ℝ) ≤ τ) :
    P.real {ω : Ω | |(∑ j : Fin n, (b j ω + s) * (y j : ℝ))| ≤ τ}
      ≤ (cSlope * L * T / Real.sqrt (n : ℝ)) * τ := by
  set rowMap : Ω → (Fin n → ℝ) := fun ω j => b j ω with hrowMap
  have hrowmeas : Measurable rowMap := measurable_pi_iff.mpr (fun j => hmeas j)
  have hlawrow : P.map rowMap = Submission.Threshold.berP (n := n) p := by
    simpa [rowMap] using map_row_eq_berP (n := n) P hmeas hind hlaw
  set lam : ℝ := -(s * ∑ j : Fin n, (y j : ℝ)) with hlam
  let E : Set (Fin n → ℝ) := Submission.ThresholdMeas.slabEvent (fun j : Fin n => (y j : ℝ)) lam τ
  have hmeasE : MeasurableSet E := Submission.ThresholdMeas.measurable_slabEvent _ _ _
  have hsum_split : ∀ ω : Ω, (∑ j : Fin n, (b j ω + s) * (y j : ℝ))
      = (∑ j : Fin n, b j ω * (y j : ℝ)) + s * (∑ j : Fin n, (y j : ℝ)) := by
    intro ω
    calc (∑ j : Fin n, (b j ω + s) * (y j : ℝ))
        = ∑ j : Fin n, (b j ω * (y j : ℝ) + s * (y j : ℝ)) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = (∑ j : Fin n, b j ω * (y j : ℝ)) + ∑ j : Fin n, (s * (y j : ℝ)) := by
          rw [Finset.sum_add_distrib]
      _ = (∑ j : Fin n, b j ω * (y j : ℝ)) + s * (∑ j : Fin n, (y j : ℝ)) := by
          rw [Finset.mul_sum]
  have hpre : rowMap ⁻¹' E = {ω : Ω | |(∑ j : Fin n, (b j ω + s) * (y j : ℝ))| ≤ τ} := by
    ext ω
    have hval : (∑ j : Fin n, rowMap ω j * (y j : ℝ)) - lam
        = ∑ j : Fin n, (b j ω + s) * (y j : ℝ) := by
      dsimp only [rowMap, lam]
      rw [hsum_split ω]
      ring
    simp only [E, Submission.ThresholdMeas.slabEvent, Set.mem_preimage, Set.mem_setOf_eq]
    rw [hval]
  have h1 : P.real {ω : Ω | |(∑ j : Fin n, (b j ω + s) * (y j : ℝ))| ≤ τ}
      = (P.map rowMap).real E := by
    rw [Measure.real_def, Measure.real_def, Measure.map_apply hrowmeas hmeasE, hpre]
  calc P.real {ω : Ω | |(∑ j : Fin n, (b j ω + s) * (y j : ℝ))| ≤ τ}
      = (P.map rowMap).real E := h1
    _ = (Submission.Threshold.berP (n := n) p).real E := by rw [hlawrow]
    _ = Submission.SlabBridge.slabWeight p y lam τ := by
        dsimp [E]
        exact Submission.SlabBridge.slab_real_eq_weight p y lam τ
    _ = bMass p (slabB (fun j : Fin n => (y j : ℝ)) lam τ) :=
        (bMass_slabB_eq_slabWeight p y lam τ).symm
    _ ≤ (cSlope * L * T / Real.sqrt (n : ℝ)) * τ := hslope τ hτ

/-- Membership in `cfGood`. -/
lemma mem_cfGood {n : ℕ} {p : unitInterval} {LAC : ℝ} {N : ℕ} {A : Fin n → Finset ℤ}
    {y : Fin n → ℤ} :
    y ∈ cfGood p LAC N A ↔
      y ∈ Submission.ProdCount.prodFinset n A ∧
        ENNReal.ofReal (LAC / (N : ℝ)) ≤
          Submission.Threshold.cfP (n := n) p (fun i : Fin n => (y i : ℝ))
            (Real.sqrt (n : ℝ)) := by
  unfold cfGood
  rw [Finset.mem_filter]

/-- Membership in `Dset`. -/
lemma mem_Dset {n : ℕ} {p : unitInterval} {s L T LAC : ℝ} {N : ℕ}
    {A : Fin n → Finset ℤ} {y : Fin n → ℤ} :
    y ∈ Dset p s L T LAC N A ↔ (y ∈ cfGood p LAC N A ∧ slopeOk p s L T y) := by
  unfold Dset
  rw [Finset.mem_filter]

/-- Widening the window of a slab family. -/
lemma slabB_subset_of_center {n : ℕ} (z : Fin n → ℝ) {c c' R R' : ℝ}
    (h : |c - c'| + R ≤ R') : slabB z c R ⊆ slabB z c' R' := by
  intro B hB
  rw [Submission.NetInvariance.mem_slabB] at hB ⊢
  have h1 : |rSub z B - c'| ≤ |rSub z B - c| + |c - c'| := by
    rw [show rSub z B - c' = (rSub z B - c) + (c - c') by ring]
    exact abs_add_le _ _
  linarith

/-- **Covering by the special-permutation net**: the lattice approximation
`spv` of an incompressible unit vector with threshold in `(T/2, T]` lies in the
net built from the good set `Dset`. -/
lemma cover_mem_Dset {n : ℕ} (hn2 : 2 ≤ n) {p : unitInterval} (hp1 : (p : ℝ) < 1)
    {δ ν T s L LAC : ℝ} (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2) (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (hT0 : 0 < T) (hTν : T ≤ ν / 2) (hL1 : 1 ≤ L) (hLAC : LAC ≤ L * ν / 256)
    {x : Fin n → ℝ} (hx : sqNorm x = 1) (hinc : ¬ compressible δ ν x)
    (hth1 : T / 2 ≤ Submission.Threshold.threshold p x L)
    (hth2 : Submission.Threshold.threshold p x L ≤ T) {spv : Fin n → ℤ}
    (hspv : ∀ i : Fin n, |(Real.sqrt (n : ℝ) / Submission.Threshold.threshold p x L) * x i
      - (spv i : ℝ)| ≤ 1)
    (hslope : ∀ t : ℝ, Real.sqrt (n : ℝ) ≤ t →
      bMass p (slabB (fun i : Fin n => (spv i : ℝ))
        (-s * (∑ i : Fin n, (Real.sqrt (n : ℝ) / Submission.Threshold.threshold p x L) * x i)) t)
        ≤ (40 * L * Submission.Threshold.threshold p x L / Real.sqrt (n : ℝ)) * t)
    (hcf : (1 / 32 : ℝ) * (L * Submission.Threshold.threshold p x L)
      ≤ (Submission.Threshold.cfP p (fun i : Fin n => (spv i : ℝ))
          (Real.sqrt (n : ℝ))).toReal)
    (hdiff : |(∑ i : Fin n, (Real.sqrt (n : ℝ) / Submission.Threshold.threshold p x L) * x i)
      - (∑ i : Fin n, (spv i : ℝ))| ≤ Real.sqrt ((12 : ℝ) * (n : ℝ) / 11))
    (hs : |s| ≤ 1)
    {PiSet : Finset (Equiv.Perm (Fin n))}
    (hPi : ∀ (y : Fin n → ℝ), sqNorm y = 1 → ¬ compressible δ ν y →
      ∀ (th : ℝ), 0 < th → T / 2 ≤ th → th ≤ T → ∀ (w : Fin n → ℤ),
        (∀ i : Fin n, |(Real.sqrt (n : ℝ) / th) * y i - (w i : ℝ)| ≤ 1) →
        ∃ π ∈ PiSet, ∀ i : Fin n, w (π i) ∈ Acoord n δ ν T i) :
    ∃ π ∈ PiSet, (fun i : Fin n => spv (π i))
      ∈ Dset p s L T LAC (holeN ν T) (Acoord n δ ν T) := by
  have hn1 : 1 ≤ n := by omega
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn1)
  have hth0 : 0 < Submission.Threshold.threshold p x L :=
    Submission.Threshold.threshold_pos p x hp1 (by linarith)
  have hN1 : (1 : ℝ) ≤ (holeN ν T : ℝ) := by
    exact_mod_cast Submission.Section5D.holeN_ge_one hT0 hν0 hTν
  have hNpos : (0 : ℝ) < (holeN ν T : ℝ) := by linarith
  have hNT : (ν / 4 : ℝ) ≤ (holeN ν T : ℝ) * T :=
    Submission.Section5D.holeN_mul_T_ge_quarter hT0 hν0 hTν
  obtain ⟨π, hπmem, hπA⟩ := hPi x hx hinc (Submission.Threshold.threshold p x L) hth0 hth1 hth2
    spv hspv
  refine ⟨π, hπmem, ?_⟩
  have hzA : (fun i : Fin n => spv (π i)) ∈
      Submission.ProdCount.prodFinset n (Acoord n δ ν T) := by
    rw [Submission.ProdCount.mem_prodFinset]
    intro i
    exact hπA i
  have hLACN : LAC / (holeN ν T : ℝ) ≤ (1 / 32 : ℝ) * (L * Submission.Threshold.threshold p x L) := by
    have hth_ge : ν / (8 * (holeN ν T : ℝ)) ≤ Submission.Threshold.threshold p x L := by
      have h1 : ν / (4 * (holeN ν T : ℝ)) ≤ T := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (holeN ν T : ℝ))]
        nlinarith [hNT]
      have h2' : ν / (8 * (holeN ν T : ℝ)) = (ν / (4 * (holeN ν T : ℝ))) / 2 := by ring
      rw [h2']
      linarith
    have h2 : LAC / (holeN ν T : ℝ) ≤ L * ν / (256 * (holeN ν T : ℝ)) := by
      rw [show L * ν / (256 * (holeN ν T : ℝ)) = (L * ν / 256) / (holeN ν T : ℝ) by ring]
      rw [div_le_div_iff_of_pos_right hNpos]
      linarith [hLAC]
    have h3 : L * ν / (256 * (holeN ν T : ℝ))
        ≤ (1 / 32 : ℝ) * (L * Submission.Threshold.threshold p x L) := by
      have h4 : L * (ν / (8 * (holeN ν T : ℝ))) ≤ L * Submission.Threshold.threshold p x L :=
        mul_le_mul_of_nonneg_left hth_ge (by linarith)
      calc L * ν / (256 * (holeN ν T : ℝ)) = (1 / 32 : ℝ) * (L * (ν / (8 * (holeN ν T : ℝ)))) := by
            first | ring | (field_simp; ring)
        _ ≤ (1 / 32 : ℝ) * (L * Submission.Threshold.threshold p x L) :=
            mul_le_mul_of_nonneg_left h4 (by norm_num)
    linarith
  have hcfz : ENNReal.ofReal (LAC / (holeN ν T : ℝ))
      ≤ Submission.Threshold.cfP p (fun i : Fin n => ((fun j => spv (π j)) i : ℝ))
          (Real.sqrt (n : ℝ)) := by
    rw [cfP_comp_perm π p spv (Real.sqrt (n : ℝ))]
    rw [ENNReal.ofReal_le_iff_le_toReal
      (Submission.Threshold.cfP_ne_top p (fun i : Fin n => (spv i : ℝ)) (Real.sqrt (n : ℝ)))]
    exact le_trans hLACN hcf
  have hslope_spv : slopeOk p s L T spv := by
    intro τ hτ
    have hcenter : |(-(s * ∑ i : Fin n, (spv i : ℝ)))
        - (-s * (∑ i : Fin n, (Real.sqrt (n : ℝ) / Submission.Threshold.threshold p x L) * x i))|
        ≤ 2 * Real.sqrt (n : ℝ) := by
      have heq : -(s * ∑ i : Fin n, (spv i : ℝ))
          - (-s * (∑ i : Fin n, (Real.sqrt (n : ℝ) / Submission.Threshold.threshold p x L) * x i))
          = s * ((∑ i : Fin n, (Real.sqrt (n : ℝ) / Submission.Threshold.threshold p x L) * x i)
              - ∑ i : Fin n, (spv i : ℝ)) := by ring
      rw [heq, abs_mul]
      have h3 : Real.sqrt ((12 : ℝ) * (n : ℝ) / 11) ≤ 2 * Real.sqrt (n : ℝ) := by
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
        have hle : (12 : ℝ) * (n : ℝ) / 11 ≤ 4 * (n : ℝ) := by nlinarith
        calc Real.sqrt ((12 : ℝ) * (n : ℝ) / 11) ≤ Real.sqrt (4 * (n : ℝ)) := Real.sqrt_le_sqrt hle
          _ = 2 * Real.sqrt (n : ℝ) := by
              rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
              norm_num
      calc |s| * |(∑ i : Fin n, (Real.sqrt (n : ℝ) / Submission.Threshold.threshold p x L) * x i)
            - ∑ i : Fin n, (spv i : ℝ)|
          ≤ 1 * (2 * Real.sqrt (n : ℝ)) :=
            mul_le_mul hs (le_trans hdiff h3) (abs_nonneg _) (by norm_num)
        _ = 2 * Real.sqrt (n : ℝ) := by ring
    have hsub := slabB_subset_of_center (fun i : Fin n => (spv i : ℝ))
      (c := -(s * ∑ i : Fin n, (spv i : ℝ)))
      (c' := -s * (∑ i : Fin n, (Real.sqrt (n : ℝ) / Submission.Threshold.threshold p x L) * x i))
      (R := τ) (R' := 3 * τ) (by linarith)
    have hbm := bMass_mono p hsub
    have hslope3 := hslope (3 * τ) (by linarith)
    have hfinal : (40 * L * Submission.Threshold.threshold p x L / Real.sqrt (n : ℝ)) * (3 * τ)
        ≤ (cSlope * L * T / Real.sqrt (n : ℝ)) * τ := by
      have h4 : (40 * L * Submission.Threshold.threshold p x L / Real.sqrt (n : ℝ)) * (3 * τ)
          = (120 * L * Submission.Threshold.threshold p x L / Real.sqrt (n : ℝ)) * τ := by ring
      rw [h4]
      have h5 : (120 : ℝ) * L * Submission.Threshold.threshold p x L ≤ cSlope * L * T := by
        dsimp [cSlope]
        nlinarith [hth2, hL1]
      have hτ0 : (0 : ℝ) ≤ τ := le_trans (le_of_lt hsqrtpos) hτ
      have h6 : (0 : ℝ) ≤ τ / Real.sqrt (n : ℝ) := div_nonneg hτ0 (le_of_lt hsqrtpos)
      calc (120 * L * Submission.Threshold.threshold p x L / Real.sqrt (n : ℝ)) * τ
          = (120 * L * Submission.Threshold.threshold p x L) * (τ / Real.sqrt (n : ℝ)) := by ring
        _ ≤ (cSlope * L * T) * (τ / Real.sqrt (n : ℝ)) := mul_le_mul_of_nonneg_right h5 h6
        _ = (cSlope * L * T / Real.sqrt (n : ℝ)) * τ := by ring
    calc bMass p (slabB (fun i : Fin n => (spv i : ℝ)) (-(s * ∑ i : Fin n, (spv i : ℝ))) τ)
        ≤ bMass p (slabB (fun i : Fin n => (spv i : ℝ))
            (-s * (∑ i : Fin n, (Real.sqrt (n : ℝ) / Submission.Threshold.threshold p x L) * x i))
            (3 * τ)) := hbm
      _ ≤ (40 * L * Submission.Threshold.threshold p x L / Real.sqrt (n : ℝ)) * (3 * τ) := hslope3
      _ ≤ (cSlope * L * T / Real.sqrt (n : ℝ)) * τ := hfinal
  have hslope_z : slopeOk p s L T (fun i : Fin n => spv (π i)) :=
    (slopeOk_comp_perm π p s L T spv).mpr hslope_spv
  rw [mem_Dset, mem_cfGood]
  exact ⟨⟨hzA, hcfz⟩, hslope_z⟩

/-- The `k`-th row of the `(n−1)×n` matrix formed by the first `n−1` columns of
`B + s·J` (read via the transpose), applied to the integer vector `y`. -/
def qSum {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (y : Fin n → ℤ)
    (k : Fin (n - 1)) : ℝ :=
  ∑ i : Fin n, (B i (Submission.GeoBridge.emb k) + s) * (y i : ℝ)

/-- The `k`-th row sum depends only on the `(emb k)`-th column of `B`. -/
lemma qSum_eq {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (y : Fin n → ℤ)
    (k : Fin (n - 1)) :
    qSum B s y k = ∑ i : Fin n, (B i (Submission.GeoBridge.emb k) + s) * (y i : ℝ) := rfl

/-- The event `|qSum| ≤ τ` as a preimage under the column map. -/
lemma qSum_measurable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {s : ℝ} {y : Fin n → ℤ}
    {k : Fin (n - 1)} : Measurable (fun M : Matrix (Fin n) (Fin n) ℝ => qSum M s y k) := by
  unfold qSum
  fun_prop

/-- Per-row small-ball estimate coming from the slope condition. -/
lemma qSum_smallball {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {p : unitInterval} {s L T : ℝ} {y : Fin n → ℤ}
    (hslope : slopeOk p s L T y) {C : Ω → Matrix (Fin n) (Fin n) ℝ}
    (hCmeas : ∀ i j : Fin n, Measurable (fun ω => C ω i j))
    (hCind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (C · x.1 x.2)) P)
    (hClaw : ∀ i j : Fin n, HasLaw (C · i j) (bernoulliMeasure 1 0 p) P)
    {k : Fin (n - 1)} {τ : ℝ} (hτ : Real.sqrt (n : ℝ) ≤ τ) :
    P.real {ω : Ω | |qSum (C ω) s y k| ≤ τ}
      ≤ (cSlope * L * T / Real.sqrt (n : ℝ)) * τ := by
  have hbind : ProbabilityTheory.iIndepFun
      (fun i : Fin n => fun ω : Ω => C ω i (Submission.GeoBridge.emb k)) P := by
    have hg : Function.Injective (fun i : Fin n => (i, Submission.GeoBridge.emb k)) := by
      intro a b h
      exact congrArg Prod.fst h
    have hpre := ProbabilityTheory.iIndepFun.precomp
      (f := fun x : Fin n × Fin n => (C · x.1 x.2))
      (g := fun i : Fin n => (i, Submission.GeoBridge.emb k)) hg hCind
    simpa using hpre
  have hmeas : ∀ i : Fin n, Measurable (fun ω : Ω => C ω i (Submission.GeoBridge.emb k)) :=
    fun i => hCmeas i _
  have hlaw : ∀ i : Fin n, HasLaw (fun ω : Ω => C ω i (Submission.GeoBridge.emb k))
      (bernoulliMeasure 1 0 p) P := fun i => hClaw i _
  have hmain := row_smallball (n := n) P hslope hmeas hbind hlaw hτ
  have hev : {ω : Ω | |(∑ i : Fin n, (C ω i (Submission.GeoBridge.emb k) + s) * (y i : ℝ))| ≤ τ}
      = {ω : Ω | |qSum (C ω) s y k| ≤ τ} := by
    ext ω
    rfl
  rwa [hev] at hmain

/-- Independence of the row sums, in the row index. -/
lemma qSum_iIndepFun {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {C : Ω → Matrix (Fin n) (Fin n) ℝ}
    (hCmeas : ∀ i j : Fin n, Measurable (fun ω => C ω i j))
    (hCind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (C · x.1 x.2)) P)
    {s : ℝ} {y : Fin n → ℤ} :
    ProbabilityTheory.iIndepFun (fun k : Fin (n - 1) => fun ω : Ω => qSum (C ω) s y k) P := by
  have hflat : ProbabilityTheory.iIndepFun
      (fun a : Fin (n - 1) × Fin n => fun ω : Ω => C ω a.2 (Submission.GeoBridge.emb a.1)) P := by
    have hg : Function.Injective
        (fun a : Fin (n - 1) × Fin n => (a.2, Submission.GeoBridge.emb a.1)) := by
      intro a b h
      have h1 : a.2 = b.2 := congrArg Prod.fst h
      have h2 : Submission.GeoBridge.emb a.1 = Submission.GeoBridge.emb b.1 :=
        congrArg Prod.snd h
      have h3 : a.1 = b.1 := Submission.GeoBridge.emb_injective h2
      exact Prod.ext h3 h1
    have hpre := ProbabilityTheory.iIndepFun.precomp
      (f := fun x : Fin n × Fin n => (C · x.1 x.2))
      (g := fun a : Fin (n - 1) × Fin n => (a.2, Submission.GeoBridge.emb a.1)) hg hCind
    simpa using hpre
  have hcur := Commons.Probability.Independence.iIndepFun_curry_flat_real
    (fun (k : Fin (n - 1)) (i : Fin n) (ω : Ω) => C ω i (Submission.GeoBridge.emb k))
    (fun k i => hCmeas i (Submission.GeoBridge.emb k)) hflat
  have hcomp := ProbabilityTheory.iIndepFun.comp hcur
    (fun k : Fin (n - 1) => fun v : Fin n → ℝ => ∑ i : Fin n, (v i + s) * (y i : ℝ))
    (fun k => by fun_prop)
  have hfun : (fun k : Fin (n - 1) =>
        ((fun v : Fin n → ℝ => ∑ i : Fin n, (v i + s) * (y i : ℝ)) ∘
          (fun ω : Ω => fun j : Fin n => C ω j (Submission.GeoBridge.emb k))))
      = (fun k : Fin (n - 1) => fun ω : Ω => qSum (C ω) s y k) := by
    funext k ω
    simp only [Function.comp_apply, qSum]
  rwa [hfun] at hcomp

/-- **Per-vector bound**: for a good lattice point `y` (satisfying the slope
condition), the probability that the `(n−1)×n` random matrix sends `y` to a
vector of norm `≤ R` is at most `(Ct·(C·L·T/√n)·(R/√(n−1)))^(n−1)`. -/
lemma qsum_sq_bound {n : ℕ} (hn2 : 2 ≤ n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {p : unitInterval} {s L T Θ R : ℝ} {y : Fin n → ℤ}
    (hslope : slopeOk p s L T y) {C : Ω → Matrix (Fin n) (Fin n) ℝ}
    (hCmeas : ∀ i j : Fin n, Measurable (fun ω => C ω i j))
    (hCind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (C · x.1 x.2)) P)
    (hClaw : ∀ i j : Fin n, HasLaw (C · i j) (bernoulliMeasure 1 0 p) P)
    (hΘ : 1 ≤ Θ) (hK : 0 < cSlope * L * T / Real.sqrt (n : ℝ))
    (hε₀ : 0 < R / Real.sqrt ((n - 1 : ℕ) : ℝ))
    (h1 : Real.sqrt (n : ℝ) ≤ R / Real.sqrt ((n - 1 : ℕ) : ℝ))
    (h2 : R / Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ Θ * Real.sqrt (n : ℝ)) :
    ∃ Ct : ℝ, 0 < Ct ∧
      P.real {ω : Ω | (∑ k : Fin (n - 1), (qSum (C ω) s y k) ^ 2) ≤ R ^ 2}
        ≤ (Ct * (cSlope * L * T / Real.sqrt (n : ℝ))
            * (R / Real.sqrt ((n - 1 : ℕ) : ℝ))) ^ (n - 1) := by
  rcases Commons.Probability.Independence.tensorization_linear hΘ with ⟨Ct, hCtpos, hTens⟩
  refine ⟨Ct, hCtpos, ?_⟩
  have hnm1 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    have : 1 ≤ n - 1 := by omega
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one this)
  have hsqrt_m : Real.sqrt (((n - 1 : ℕ) : ℝ)) ^ 2 = ((n - 1 : ℕ) : ℝ) :=
    Real.sq_sqrt (le_of_lt hnm1)
  have hεsq : (R / Real.sqrt ((n - 1 : ℕ) : ℝ)) ^ 2 * ((n - 1 : ℕ) : ℝ) = R ^ 2 := by
    rw [div_pow, hsqrt_m]
    field_simp
  have hsmall : ∀ k : Fin (n - 1), ∀ t : ℝ, Real.sqrt (n : ℝ) ≤ t →
      P.real {x : Ω | |qSum (C x) s y k| ≤ t}
        ≤ (cSlope * L * T / Real.sqrt (n : ℝ)) * t := by
    intro k t ht
    exact qSum_smallball P hslope hCmeas hCind hClaw ht
  have hmain := hTens (P := P) (ξ := fun k : Fin (n - 1) => fun ω : Ω => qSum (C ω) s y k)
    (K := cSlope * L * T / Real.sqrt (n : ℝ)) (ε₀ := Real.sqrt (n : ℝ))
    (ε := R / Real.sqrt ((n - 1 : ℕ) : ℝ))
    (qSum_iIndepFun (s := s) (y := y) P hCmeas hCind) hK
    (Real.sqrt_pos.2 (by exact_mod_cast (by omega : 1 ≤ n))) h1 h2 hsmall
  rw [hεsq] at hmain
  exact hmain

end Submission.NetArgument
