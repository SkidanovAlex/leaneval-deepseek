import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FockBridge.Defs
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.sectorStratum` — the slot-set stratification of the box sectors

The residual of the Fock/particle-number bridge (`Submission/Work/FockBridge/README.md`
§6, piece 1) is the **fibre decomposition of the sector piece**: the count-`k` sector
piece `Φ_k = 1_{n_{B(u)} = k}·Φ` of a big-box state is a function supported where
*exactly* `k` slots lie in the box `B(u)` — but the set of those slots *varies* with
the configuration.  To Fubini over the `k` in-box and the `N−k` outside coordinates one
first has to stratify the sector by the *slot set*:

    sectorSet B k = ⋃_{S : Finset (Fin N), S.card = k} stratum B S

(a *disjoint* finite union), where

    stratum B S = {x : X N | ∀ i, x i ∈ B ↔ i ∈ S}

is the configuration space with in-box slot set exactly `S`.  This module proves that
stratification, its measurability, and the two *locality* consequences that make the
fibre decomposition usable:

* the sector piece is the sum of its stratum pieces,
  `sectorPiece B k Φ = ∑_{S.card = k} (stratum B S).indicator Φ`;
* **the box projections vanish off their slot**: on `stratum B S` with `i ∉ S` one has
  `B.indicator 1 (x i) = 0`, hence `boxPInd volA B i Ψ x = 0` and
  `boxQInd volA B i Ψ x = 0`.

The second fact is what makes the sector word *see only the in-box slots*: every term of
`qLHSwordB` carries `χ_{B(u)}(x_i)` (which vanishes off `B(u)`, `DLInfra.chiB_support_mem`)
and every term of `tBwordInd` carries `boxQInd (B(u)) i`, so on a stratum `S` all
contributions from the slots `i ∉ S` drop out.  That is the point at which the `N`-particle
sector word becomes a `k`-particle box word — the reduction the count-indexed delivered
bound (`Work.BlockBound4.diagWeBAt`) is applied to (`Work.FockBridge.PerSectorBound`).

## Vocabulary

`X N = Fin N → ℝ³` is the corpus configuration space (`Submission.BoseGases.X`),
`boxOccupancy B x = #{i | x i ∈ B}`, `sectorSet B k = {x | boxOccupancy B x = k}` and
`sectorPiece B k Φ = (sectorSet B k).indicator Φ`, all from
`Submission.Work.FockBridge.Defs`; `boxPInd`/`boxQInd` are FS's box projections
(`Submission.Work.UBBInputs8.Defs`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

open Classical

namespace Work.BoseFixB1B

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open Work.FockBridge

set_option autoImplicit false
set_option linter.unusedVariables false

variable {N : ℕ}

/-! ## 1. The strata -/

/-- **The slot-set stratum of a box.**  `stratum B S` is the set of configurations whose set
of in-box slots is *exactly* `S`. -/
def stratum (B : Set ℝ³) (S : Finset (Fin N)) : Set (X N) :=
  {x : X N | ∀ i : Fin N, x i ∈ B ↔ i ∈ S}

lemma mem_stratum_iff (B : Set ℝ³) (S : Finset (Fin N)) (x : X N) :
    x ∈ stratum B S ↔ ∀ i : Fin N, x i ∈ B ↔ i ∈ S := Iff.rfl

/-- The in-box slot set of a configuration, as a `Finset`. -/
def boxSlotSet (B : Set ℝ³) (x : X N) : Finset (Fin N) :=
  Finset.univ.filter (fun i : Fin N => x i ∈ B)

lemma mem_boxSlotSet (B : Set ℝ³) (x : X N) (i : Fin N) :
    i ∈ boxSlotSet B x ↔ x i ∈ B := by
  simp [boxSlotSet]

lemma boxOccupancy_eq_card_boxSlotSet (B : Set ℝ³) (x : X N) :
    boxOccupancy B x = (boxSlotSet B x).card := rfl

/-- Every configuration lies in the stratum of its own in-box slot set. -/
lemma mem_stratum_boxSlotSet (B : Set ℝ³) (x : X N) : x ∈ stratum B (boxSlotSet B x) := by
  intro i
  rw [mem_boxSlotSet]

lemma stratum_eq_empty_of_card_ne (B : Set ℝ³) {S : Finset (Fin N)} {k : ℕ}
    (h : S.card ≠ k) : stratum B S ∩ sectorSet B k = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨hxS, hxk⟩ := hx
  have hc : (boxSlotSet B x).card = k := by
    rw [← boxOccupancy_eq_card_boxSlotSet, (mem_sectorSet_iff B k x).mp hxk]
  have hSS : boxSlotSet B x = S := by
    ext i
    rw [mem_boxSlotSet, (mem_stratum_iff B S x).mp hxS i]
  exact h (by rw [← hSS]; exact hc)

/-! ## 2. Measurability and disjointness -/

/-- The stratum is measurable for a measurable box: it is a finite intersection of
coordinate conditions. -/
lemma stratum_measurable {B : Set ℝ³} (hB : MeasurableSet B) (S : Finset (Fin N)) :
    MeasurableSet (stratum B S) := by
  have hset : stratum B S
      = (⋂ i : Fin N, (fun x : X N => x i) ⁻¹' (if i ∈ S then B else Bᶜ)) := by
    ext x
    constructor
    · intro hx
      simp only [Set.mem_iInter, Set.mem_preimage]
      intro i
      by_cases hi : i ∈ S
      · simp only [if_pos hi]
        exact (hx i).mpr hi
      · simp only [if_neg hi, Set.mem_compl_iff]
        intro hxB
        exact hi ((hx i).mp hxB)
    · intro hx
      simp only [Set.mem_iInter, Set.mem_preimage] at hx
      intro i
      by_cases hi : i ∈ S
      · exact ⟨fun _ => hi, fun _ => by simpa [if_pos hi] using hx i⟩
      · refine ⟨fun hxB => ?_, fun hmem => absurd hmem hi⟩
        have hc := hx i
        rw [if_neg hi] at hc
        exact absurd hxB hc
  rw [hset]
  refine MeasurableSet.iInter fun i => ?_
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    exact hB.preimage (measurable_pi_apply i)
  · rw [if_neg hi]
    exact hB.compl.preimage (measurable_pi_apply i)

/-- Distinct strata are disjoint. -/
lemma stratum_disjoint (B : Set ℝ³) {S S' : Finset (Fin N)} (h : S ≠ S') :
    Disjoint (stratum B S) (stratum B S') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  refine h (Finset.ext fun i => ?_)
  exact (((mem_stratum_iff B S x).mp hx i).symm).trans ((mem_stratum_iff B S' x).mp hx' i)

/-! ## 3. The stratification of the sectors -/

/-- A stratum of cardinality `k` sits inside the count-`k` sector. -/
lemma stratum_subset_sectorSet (B : Set ℝ³) {S : Finset (Fin N)} {k : ℕ} (hS : S.card = k) :
    stratum B S ⊆ sectorSet B k := by
  intro x hx
  rw [mem_sectorSet_iff, boxOccupancy_eq_card_boxSlotSet]
  have h : boxSlotSet B x = S :=
    Finset.ext fun i => by rw [mem_boxSlotSet, (mem_stratum_iff B S x).mp hx i]
  rw [h, hS]

/-- **The sector is the disjoint union of its slot-set strata** (membership form). -/
theorem mem_sectorSet_iff_exists_stratum (B : Set ℝ³) (k : ℕ) (x : X N) :
    x ∈ sectorSet B k ↔ ∃ S : Finset (Fin N), S.card = k ∧ x ∈ stratum B S := by
  constructor
  · intro hx
    exact ⟨boxSlotSet B x,
      by rw [← boxOccupancy_eq_card_boxSlotSet]; exact (mem_sectorSet_iff B k x).mp hx,
      mem_stratum_boxSlotSet B x⟩
  · rintro ⟨S, hS, hxS⟩
    exact stratum_subset_sectorSet B hS hxS

/-- The strata cover the whole configuration space. -/
theorem iUnion_stratum_eq_univ (B : Set ℝ³) :
    (⋃ S : Finset (Fin N), stratum B S) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨boxSlotSet B x, mem_stratum_boxSlotSet B x⟩

/-- **The sector is the union of its slot-set strata.** -/
theorem sectorSet_eq_iUnion_stratum (B : Set ℝ³) (k : ℕ) :
    sectorSet B k = ⋃ S : {S : Finset (Fin N) // S.card = k}, stratum B S.1 := by
  ext x
  constructor
  · intro hx
    refine Set.mem_iUnion.mpr ⟨⟨boxSlotSet B x, ?_⟩, mem_stratum_boxSlotSet B x⟩
    rw [← boxOccupancy_eq_card_boxSlotSet]
    exact (mem_sectorSet_iff B k x).mp hx
  · intro hx
    obtain ⟨S, hxS⟩ := Set.mem_iUnion.mp hx
    exact stratum_subset_sectorSet B S.2 hxS

/-- **The sector piece is the sum of its stratum pieces.** -/
theorem sectorPiece_eq_sum_stratum (B : Set ℝ³) (k : ℕ) (Φ : X N → ℝ) (x : X N) :
    sectorPiece B k Φ x
      = ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin N) => S.card = k)),
          (stratum B S).indicator Φ x := by
  classical
  by_cases hx : x ∈ sectorSet B k
  · have hcard : (boxSlotSet B x).card = k := by
      rw [← boxOccupancy_eq_card_boxSlotSet]
      exact (mem_sectorSet_iff B k x).mp hx
    have hmem : boxSlotSet B x ∈ Finset.univ.filter (fun S : Finset (Fin N) => S.card = k) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard⟩
    have hsingle : (∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin N) => S.card = k)),
          (stratum B S).indicator Φ x)
        = (stratum B (boxSlotSet B x)).indicator Φ x :=
      Finset.sum_eq_single (boxSlotSet B x)
        (fun S _ hSne => by
          rw [Set.indicator_of_notMem]
          intro hxS
          exact hSne (by
            have h1 : boxSlotSet B x = S :=
              Finset.ext fun i => by rw [mem_boxSlotSet, (mem_stratum_iff B S x).mp hxS i]
            exact h1.symm))
        (fun hnot => absurd hmem hnot)
    rw [sectorPiece, Set.indicator_of_mem hx, hsingle,
      Set.indicator_of_mem (mem_stratum_boxSlotSet B x)]
  · have hzero : (∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin N) => S.card = k)),
          (stratum B S).indicator Φ x) = 0 :=
      Finset.sum_eq_zero fun S hS => by
        rw [Set.indicator_of_notMem]
        intro hxS
        exact hx (stratum_subset_sectorSet B (Finset.mem_filter.mp hS).2 hxS)
    rw [sectorPiece, Set.indicator_of_notMem hx, hzero]

/-! ## 4. Locality of the box projections on a stratum -/

/-- On the stratum of `S`, the slot indicator of a slot outside `S` vanishes. -/
lemma indicator_eq_zero_of_mem_stratum_of_notMem {B : Set ℝ³} {S : Finset (Fin N)} {i : Fin N}
    (hi : i ∉ S) {x : X N} (hx : x ∈ stratum B S) :
    B.indicator (fun _ => (1 : ℝ)) (x i) = 0 := by
  rw [Set.indicator_of_notMem]
  intro hmem
  exact hi (((mem_stratum_iff B S x).mp hx i).mp hmem)

/-- On the stratum of `S`, every slot *inside* `S` lies in the box. -/
lemma mem_of_mem_stratum {B : Set ℝ³} {S : Finset (Fin N)} {i : Fin N} (hi : i ∈ S) {x : X N}
    (hx : x ∈ stratum B S) : x i ∈ B :=
  ((mem_stratum_iff B S x).mp hx i).mpr hi

/-- **FS's box condensate projection `P_{B,i}` vanishes off the slot's stratum**: if
`x i ∉ B` then `boxPInd volA B i Ψ x = 0`. -/
theorem boxPInd_eq_zero_of_mem_stratum_of_notMem {volA : ℝ} {B : Set ℝ³}
    {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) {x : X N} (hx : x ∈ stratum B S)
    (Ψ : X N → ℝ) :
    Work.UBBInputs8.boxPInd volA B i Ψ x = 0 := by
  unfold Work.UBBInputs8.boxPInd
  rw [indicator_eq_zero_of_mem_stratum_of_notMem hi hx]
  ring

/-- **FS's mean-free box projection `Q_{B,i} = 1_{B,i} − P_{B,i}` vanishes off the slot's
stratum**: if `x i ∉ B` then `boxQInd volA B i Ψ x = 0`. -/
theorem boxQInd_eq_zero_of_mem_stratum_of_notMem {volA : ℝ} {B : Set ℝ³}
    {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) {x : X N} (hx : x ∈ stratum B S)
    (Ψ : X N → ℝ) :
    Work.UBBInputs8.boxQInd volA B i Ψ x = 0 := by
  unfold Work.UBBInputs8.boxQInd
  rw [indicator_eq_zero_of_mem_stratum_of_notMem hi hx,
    boxPInd_eq_zero_of_mem_stratum_of_notMem hi hx]
  ring

/-- The excited-count summand of FS's `n₊` vanishes for a slot outside the stratum. -/
theorem boxQInd_sq_eq_zero_of_mem_stratum_of_notMem {volA : ℝ} {B : Set ℝ³}
    {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) {x : X N} (hx : x ∈ stratum B S)
    (Ψ : X N → ℝ) :
    (Work.UBBInputs8.boxQInd volA B i Ψ x) ^ 2 = 0 := by
  rw [boxQInd_eq_zero_of_mem_stratum_of_notMem hi hx]
  ring

/-- **The counting function is stratum-local**: on `stratum B S` the count is the fixed
cardinality `S.card`. -/
lemma boxCount_eq_card_of_mem_stratum {B : Set ℝ³} {S : Finset (Fin N)} {x : X N}
    (hx : x ∈ stratum B S) : boxCount B x = (S.card : ℝ) := by
  have h : boxSlotSet B x = S :=
    Finset.ext fun i => by rw [mem_boxSlotSet, (mem_stratum_iff B S x).mp hx i]
  have h1 : boxCount B x = ((boxSlotSet B x).card : ℝ) := by
    rw [boxCount, boxOccupancy_eq_card_boxSlotSet]
  rw [h1, h]

/-! ## 5. Locality of the box projections on the strata, function level

The stratum pieces are supported on their stratum, and on a stratum `S` the slots outside `S`
contribute nothing at all: the mean-free box projection `Q_{B,i}` of a stratum-`S`-supported
function *vanishes identically* for `i ∉ S`.  The point is that both terms of

    boxQInd volA B i Ψ x = 1_B(x i)·Ψ x − (1/volA)(∫_{z∈B}Ψ(x_{i←z})dz)·1_B(x i)

die for `i ∉ S`: the first because `Ψ` is supported on the stratum (where `x i ∉ B`), the second
because for `z ∈ B` the updated configuration `x_{i←z}` lies in a stratum with `i` in its slot set
(`z ∈ B`), so a function supported on the stratum of `S` (which does *not* contain `i`) vanishes
there.

This is what makes the `N`-particle sector word a `k`-particle box word: FS's excited count
`n₊ = Σ_i ‖Q_{B,i}Ψ‖²` only receives the contributions of the in-box slots `i ∈ S`. -/

/-- **The mean-free box projection kills the off-stratum slots.**  For `i ∉ S` and a function
supported on `stratum B S`, the slot-`i` projection `Q_{B,i}` vanishes identically. -/
theorem boxQInd_indicator_stratum_eq_zero {volA : ℝ} {B : Set ℝ³} (hB : MeasurableSet B)
    {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) (Φ : X N → ℝ) :
    Work.UBBInputs8.boxQInd volA B i ((stratum B S).indicator Φ) = 0 := by
  funext x
  change Work.UBBInputs8.boxQInd volA B i ((stratum B S).indicator Φ) x = (0 : ℝ)
  by_cases hx : x ∈ stratum B S
  · exact boxQInd_eq_zero_of_mem_stratum_of_notMem hi hx _
  · have h1 : B.indicator (fun _ => (1 : ℝ)) (x i)
        * (stratum B S).indicator Φ x = 0 := by
      rw [Set.indicator_of_notMem hx]
      ring
    have h2 : (∫ z in B, (stratum B S).indicator Φ (Function.update x i z)) = 0 := by
      refine MeasureTheory.integral_eq_zero_of_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hB] with z hz
      refine Set.indicator_of_notMem ?_ Φ
      intro hmem
      have hsi := ((mem_stratum_iff B S (Function.update x i z)).mp hmem i)
      rw [Function.update_self] at hsi
      exact hi (hsi.mp hz)
    unfold Work.UBBInputs8.boxQInd Work.UBBInputs8.boxPInd
    rw [h1, h2]
    ring

/-- The same for FS's box condensate projection `P_{B,i}`. -/
theorem boxPInd_indicator_stratum_eq_zero {volA : ℝ} {B : Set ℝ³} (hB : MeasurableSet B)
    {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) (Φ : X N → ℝ) :
    Work.UBBInputs8.boxPInd volA B i ((stratum B S).indicator Φ) = 0 := by
  funext x
  change Work.UBBInputs8.boxPInd volA B i ((stratum B S).indicator Φ) x = (0 : ℝ)
  by_cases hx : x ∈ stratum B S
  · exact boxPInd_eq_zero_of_mem_stratum_of_notMem hi hx _
  · have h2 : (∫ z in B, (stratum B S).indicator Φ (Function.update x i z)) = 0 := by
      refine MeasureTheory.integral_eq_zero_of_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hB] with z hz
      refine Set.indicator_of_notMem ?_ Φ
      intro hmem
      have hsi := ((mem_stratum_iff B S (Function.update x i z)).mp hmem i)
      rw [Function.update_self] at hsi
      exact hi (hsi.mp hz)
    unfold Work.UBBInputs8.boxPInd
    rw [h2]
    ring

/-- **The off-stratum slots do not contribute to FS's excited count `n₊`**: for a function
supported on `stratum B S` the projection sum runs only over the in-box slots `i ∈ S`. -/
theorem cnPlusBoxInd_indicator_stratum_eq_sum {volA : ℝ} {B : Set ℝ³} (hB : MeasurableSet B)
    {S : Finset (Fin N)} (a : ℝ) (Φ : X N → ℝ) :
    Work.UBBInputs8.cnPlusBoxInd a B volA ((stratum B S).indicator Φ)
      = ∑ i ∈ S, ∫ x in abox N a,
          (Work.UBBInputs8.boxQInd volA B i ((stratum B S).indicator Φ) x) ^ 2 := by
  rw [Work.UBBInputs8.cnPlusBoxInd]
  have hzero : ∀ i ∈ (Finset.univ : Finset (Fin N)), i ∉ S →
      (∫ x in abox N a, (Work.UBBInputs8.boxQInd volA B i ((stratum B S).indicator Φ) x) ^ 2)
        = 0 := by
    intro i _ hiS
    rw [boxQInd_indicator_stratum_eq_zero hB hiS Φ]
    simp
  exact (Finset.sum_subset (Finset.subset_univ S) hzero).symm

/-- The off-stratum slots do not contribute to the `χ_{B(u)}`-weighted (fibre) slot sums
either: the entries are killed by the projection. -/
theorem boxQInd_indicator_stratum_apply_eq_zero {volA : ℝ} {B : Set ℝ³} (hB : MeasurableSet B)
    {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) (Φ : X N → ℝ) (x : X N) :
    Work.UBBInputs8.boxQInd volA B i ((stratum B S).indicator Φ) x = 0 := by
  rw [boxQInd_indicator_stratum_eq_zero hB hi Φ]
  rfl

/-! ## 6. The localised kernels vanish off the box

The potential word `qLHSwordB` of the sliding box carries the localised kernels
`wSmallPair M ℓ d u f`, `wSmall1Pair h M ℓ d u`, whose first and last factors are the product
cutoff `χ_{B(u)} = χ(x/ℓ)·χ_M(x/(ℓd) − u)`.  That cutoff is supported in the box `B(u)`: it
carries the corner factor `χ(x/ℓ)` (supported in the big cube `acube ℓ`) and the face-factor
`χ_M(x/(ℓd) − u)` (supported in the small cube `acube(ℓd)`).  Hence the localised kernels vanish
whenever one of their arguments leaves `B(u)`, and the fibre/pair sums of the potential word are
stratum-local exactly as the projection sums of the kinetic word are. -/

/-- **The product cutoff vanishes off the box**: `χ_{B(u)}(x) = 0` whenever `x ∉ B(u)`. -/
theorem chiSmallB_eq_zero_of_notMem_dlBox {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) {u x : ℝ³} (hx : x ∉ dlBox ℓ d u) : chiSmallB M ℓ d u x = 0 := by
  by_contra h
  apply hx
  have h1 : chiScale ℓ x ≠ 0 := fun h0 => h (by rw [chiSmallB, h0, zero_mul])
  have h2 : chiSmall M ((ℓ * d)⁻¹ • x - u) ≠ 0 := fun h0 => h (by rw [chiSmallB, h0, mul_zero])
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  have hshift : (ℓ * d)⁻¹ • x - u = (ℓ * d)⁻¹ • (x - (ℓ * d) • u) := by
    rw [smul_sub]
    congr 1
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hld), one_smul]
  rw [hshift] at h2
  refine ⟨chiScale_mem_acube hℓ h1, ?_⟩
  intro j
  have hcoord : |(x - (ℓ * d) • u).ofLp j| ≤ (ℓ * d) / 2 :=
    chiSmall_scale_support_mem_abs_le hM hld h2 j
  rw [abs_le] at hcoord
  exact ⟨by linarith [hcoord.1], by linarith [hcoord.2]⟩

/-- The localised pair kernel vanishes when its **left** argument leaves the box. -/
theorem wSmallPair_eq_zero_of_notMem_dlBox_left {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) {u x y : ℝ³} {f : ℝ³ → ℝ} (hx : x ∉ dlBox ℓ d u) :
    wSmallPair M ℓ d u f x y = 0 := by
  rw [wSmallPair, chiSmallB_eq_zero_of_notMem_dlBox hM hℓ hd hx]
  ring

/-- The localised pair kernel vanishes when its **right** argument leaves the box. -/
theorem wSmallPair_eq_zero_of_notMem_dlBox_right {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) {u x y : ℝ³} {f : ℝ³ → ℝ} (hy : y ∉ dlBox ℓ d u) :
    wSmallPair M ℓ d u f x y = 0 := by
  rw [wSmallPair, chiSmallB_eq_zero_of_notMem_dlBox hM hℓ hd hy]
  ring

/-- The localised one-body kernel vanishes when its **left** argument leaves the box. -/
theorem wSmall1Pair_eq_zero_of_notMem_dlBox_left {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, _root_.BoseGases.IsRadial w ∧
      _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u x y : ℝ³}
    (hx : x ∉ dlBox ℓ d u) : wSmall1Pair h M ℓ d u x y = 0 := by
  rw [wSmall1Pair]
  exact wSmallPair_eq_zero_of_notMem_dlBox_left hM hℓ hd hx

/-! ## 7. The sector mass splits over the strata

The FockBridge residual `Work.FockBridge.PerSectorBound` carries the sector mass
`m_k = sectorMass L (dlBox L d u) Φ k` as the weight of the count-`k` threshold.  Once the word
is refined to the strata (§4–§6), the *mass* has to be refined in the same way: the strata of
cardinality `k` partition the count-`k` sector, so

    m_k = Σ_{S.card = k} (mass of stratum S) .

This is the identity that turns the per-stratum bound into the weighted sector bound. -/

/-- The mass of a **stratum**: `∫⁻_{abox} 1_{stratum B S}·Φ²`. -/
noncomputable def stratumMassENN (L : ℝ) (B : Set ℝ³) (S : Finset (Fin N))
    (Φ : X N → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in abox N L, (stratum B S).indicator (fun x => ENNReal.ofReal ((Φ x) ^ 2)) x

/-- **The sector mass is the sum of the stratum masses.** -/
theorem sectorMassENN_eq_sum_stratumMassENN {B : Set ℝ³} {Φ : X N → ℝ}
    (hB : MeasurableSet B) (hΦ : Measurable Φ) (L : ℝ) (k : ℕ) :
    sectorMassENN L B Φ k
      = ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin N) => S.card = k)),
          stratumMassENN L B S Φ := by
  classical
  have hpt : (fun x : X N => (sectorSet B k).indicator
        (fun x => ENNReal.ofReal ((Φ x) ^ 2)) x)
      = fun x : X N => ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin N) => S.card = k)),
          (stratum B S).indicator (fun x => ENNReal.ofReal ((Φ x) ^ 2)) x := by
    funext x
    by_cases hx : x ∈ sectorSet B k
    · have hcard : (boxSlotSet B x).card = k := by
        rw [← boxOccupancy_eq_card_boxSlotSet]
        exact (mem_sectorSet_iff B k x).mp hx
      have hmem : boxSlotSet B x ∈ Finset.univ.filter (fun S : Finset (Fin N) => S.card = k) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard⟩
      rw [Set.indicator_of_mem hx, Finset.sum_eq_single (boxSlotSet B x)]
      · rw [Set.indicator_of_mem (mem_stratum_boxSlotSet B x)]
      · intro S _ hSne
        rw [Set.indicator_of_notMem]
        intro hxS
        exact hSne (by
          have h1 : boxSlotSet B x = S :=
            Finset.ext fun i => by rw [mem_boxSlotSet, (mem_stratum_iff B S x).mp hxS i]
          exact h1.symm)
      · intro hnot
        exact absurd hmem hnot
    · rw [Set.indicator_of_notMem hx]
      refine (Finset.sum_eq_zero fun S hS => ?_).symm
      rw [Set.indicator_of_notMem]
      intro hxS
      exact hx (stratum_subset_sectorSet B (Finset.mem_filter.mp hS).2 hxS)
  have h1 : sectorMassENN L B Φ k
      = ∫⁻ x in abox N L,
          ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin N) => S.card = k)),
            (stratum B S).indicator (fun x => ENNReal.ofReal ((Φ x) ^ 2)) x := by
    simp only [sectorMassENN]
    exact lintegral_congr fun x => congrFun hpt x
  rw [h1, lintegral_finsetSum]
  · refine Finset.sum_congr rfl fun S _ => ?_
    rw [stratumMassENN]
  · intro S _
    exact (ENNReal.measurable_ofReal.comp (hΦ.pow_const 2)).indicator (stratum_measurable hB S)

end Work.BoseFixB1B
