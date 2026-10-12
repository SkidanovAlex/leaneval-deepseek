import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import ChallengeDeps
import Submission.BracketSum
import Submission.FiberMeas
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The complement-parameterized slice and the INT1/INT2 identities

With the occupied-fiber measure identification (`Submission.FiberMeas`), the
slice of a state is most cleanly parameterised by the *complement* (frozen
background) configuration:

  * `sliceFull a j z φ : X (cellCount a j) → ℝ`, `y ↦ φ (fullInsert a j y z)`
    — `φ` read with the occupied coordinates free (`y`) and the complement
    frozen at `z`; smooth in `y` for smooth `φ` (`sliceFull_contDiff`);
  * the `fderiv` chain rule `sliceFull_fderiv` — differentiating the slice in
    the occupied coordinate `t` equals differentiating `φ` in the particle
    `occEquiv t` (the insertion map is affine on the occupied fiber);
  * **INT1** `sliceFull_sq_integral` — `∫_x φ² = ∫_y ∫_z (sliceFull z φ y)²`;
  * the within-cell gradient energy `cellGradEnergy` (gradient form of the
    per-cell kinetic + intra-cell pairs);
  * **INT2** `cellGradEnergy_integral` — the within-cell-j energy of `φ` is the
    integral over the frozen background of `sliceWsE (cellCount a j) v
    (sliceFull z φ)` (the pair order `t < t′ ⟺ occEquiv t < occEquiv t′` is
    where `occEquiv_strictMono` is used).

With INT1 and INT2, L1 closes: `cellOpEnergy ≥ eNeu(n_j)(2ℓ)·‖φ‖²` via
`SliceEnergy.sliceWsE_ge_eNeu` integrated over the background.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The slice of `φ` with the complement (frozen background) coordinates `z`. -/
noncomputable def sliceFull {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (z : X (N - cellCount a j)) (φ : X N → ℝ) : X (cellCount a j) → ℝ :=
  fun y : X (cellCount a j) => φ (fullInsert a j y z)

/-- The slice is smooth in the occupied coordinates for smooth `φ` (the
insertion map is affine). -/
lemma sliceFull_contDiff {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (z : X (N - cellCount a j)) {φ : X N → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (sliceFull a j z φ) := by
  unfold sliceFull
  exact hφ.comp (by
    -- the insertion map `y ↦ fullInsert a j y z` is affine in `y` (occupied slots)
    have hg : ContDiff ℝ ∞ (fun y : X (cellCount a j) => fullInsert a j y z) := by
      simpa [fullInsert] using (occInsert_contDiff a j (complInsert a j z (0 : X N)))
    exact hg)

/-- Reading off the occupied slot `i` of the full insertion. -/
lemma fullInsert_apply_occ {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (y : X (cellCount a j)) (z : X (N - cellCount a j)) {i : Fin N} (hi : i ∈ occSet a j) :
    fullInsert a j y z i = y (((occEquiv a j).symm) ⟨i, hi⟩) := by
  unfold fullInsert occInsert complInsert
  rw [dif_pos hi]

/-- Reading off the complement slot `i` of the full insertion (independent of
the occupied coordinates). -/
lemma fullInsert_apply_compl {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (y : X (cellCount a j)) (z : X (N - cellCount a j)) {i : Fin N} (hi : i ∉ occSet a j) :
    fullInsert a j y z i = (complInsert a j z (0 : X N)) i := by
  unfold fullInsert occInsert complInsert
  rw [dif_neg hi]

/-- Moving the occupied coordinates of the full insertion along the `t`-th
standard direction only moves the particle `occEquiv t`, by the same amount. -/
lemma fullInsert_path {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (z : X (N - cellCount a j)) (y : X (cellCount a j)) (t : Fin (cellCount a j))
    (k : Fin 3) (s : ℝ) :
    fullInsert a j (y + s • kcDir (cellCount a j) t k) z =
      fullInsert a j y z + s • kcDir N
        (((occEquiv a j) t : {i : Fin N // i ∈ occSet a j}) : Fin N) k := by
  classical
  funext i
  let e : {i : Fin N // i ∈ occSet a j} := occEquiv a j t
  let i' : Fin N := (e : Fin N)
  have he_mem : i' ∈ occSet a j := by
    dsimp [i']
    exact e.property
  have hsymm : (occEquiv a j).symm ⟨i', he_mem⟩ = t := by
    change (occEquiv a j).symm e = t
    exact (occEquiv a j).symm_apply_apply t
  by_cases hi : i ∈ occSet a j
  · have hdir : (kcDir (cellCount a j) t k) ((occEquiv a j).symm ⟨i, hi⟩) = (kcDir N i' k) i := by
      by_cases hii' : i = i'
      · have hsame : (⟨i, hi⟩ : {r : Fin N // r ∈ occSet a j}) = e := by
          apply Subtype.ext
          simpa [i'] using hii'
        have h1 : (occEquiv a j).symm ⟨i, hi⟩ = t := by
          rw [hsame]
          exact hsymm
        rw [h1]
        rw [kcDir_apply_eq]
        rw [hii']
        rw [kcDir_apply_eq]
      · have hne : (occEquiv a j).symm ⟨i, hi⟩ ≠ t := by
          intro hs
          apply hii'
          have hc := congrArg (fun q : Fin (cellCount a j) =>
            ((occEquiv a j) q : {r : Fin N // r ∈ occSet a j})) hs
          have hmem : (⟨i, hi⟩ : {r : Fin N // r ∈ occSet a j}) = e := by
            rw [← (occEquiv a j).apply_symm_apply (x := ⟨i, hi⟩)]
            change (occEquiv a j) ((occEquiv a j).symm ⟨i, hi⟩) = (occEquiv a j) t
            exact hc
          exact congrArg (fun q : {r : Fin N // r ∈ occSet a j} => (q : Fin N)) hmem
        have hleft : (kcDir (cellCount a j) t k) ((occEquiv a j).symm ⟨i, hi⟩) = 0 := by
          exact kcDir_apply_ne t k (j := (occEquiv a j).symm ⟨i, hi⟩) hne
        have hright : (kcDir N i' k) i = 0 := by
          exact kcDir_apply_ne i' k (j := i) hii'
        rw [hleft, hright]
    calc
      (fullInsert a j (y + s • kcDir (cellCount a j) t k) z) i
          = (y + s • kcDir (cellCount a j) t k) ((occEquiv a j).symm ⟨i, hi⟩) := by
            exact fullInsert_apply_occ a j (y + s • kcDir (cellCount a j) t k) z hi
      _ = y ((occEquiv a j).symm ⟨i, hi⟩) + s • (kcDir (cellCount a j) t k) ((occEquiv a j).symm ⟨i, hi⟩) := by
            simp [Pi.add_apply, Pi.smul_apply]
      _ = (fullInsert a j y z) i + s • (kcDir N i' k) i := by
            rw [hdir]
            congr 1
            exact (fullInsert_apply_occ a j y z hi).symm
  · calc
      (fullInsert a j (y + s • kcDir (cellCount a j) t k) z) i
          = (complInsert a j z (0 : X N)) i := by
            exact fullInsert_apply_compl a j (y + s • kcDir (cellCount a j) t k) z hi
      _ = (fullInsert a j y z) i := by
            exact (fullInsert_apply_compl a j y z hi).symm
      _ = (fullInsert a j y z) i + s • (kcDir N i' k) i := by
            have hzero : (kcDir N i' k) i = 0 := by
              exact kcDir_apply_ne i' k (j := i) (by
                intro hii'
                apply hi
                rw [hii']
                exact he_mem)
            simp [hzero]

/-- Chain rule: differentiating the slice in the occupied coordinate `t` equals
differentiating `φ` in the particle `occEquiv t`. -/
lemma sliceFull_fderiv {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (z : X (N - cellCount a j)) {φ : X N → ℝ} (hφ : ContDiff ℝ 1 φ)
    (y : X (cellCount a j)) (t : Fin (cellCount a j)) (k : Fin 3) :
    fderiv ℝ (sliceFull a j z φ) y (kcDir (cellCount a j) t k) =
      fderiv ℝ φ (fullInsert a j y z)
        (kcDir N (((occEquiv a j) t : {i : Fin N // i ∈ occSet a j}) : Fin N) k) := by
  let d : X (cellCount a j) := kcDir (cellCount a j) t k
  let i' : Fin N := ((occEquiv a j) t : {i : Fin N // i ∈ occSet a j})
  have hg_cd : ContDiff ℝ ∞ (fun w : X (cellCount a j) => fullInsert a j w z) := by
    simpa [fullInsert] using (occInsert_contDiff a j (complInsert a j z (0 : X N)))
  have hslice_cd : ContDiff ℝ 1 (fun w : X (cellCount a j) => φ (fullInsert a j w z)) := by
    exact hφ.comp (hg_cd.of_le (by norm_num : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω)))
  have hdiff : DifferentiableAt ℝ (fun w : X (cellCount a j) => φ (fullInsert a j w z)) y :=
    ContDiff.differentiable hslice_cd (by norm_num : (1 : ℕ∞ω) ≠ 0) y
  have hφdiff : DifferentiableAt ℝ φ (fullInsert a j y z) :=
    ContDiff.differentiable hφ (by norm_num : (1 : ℕ∞ω) ≠ 0) (fullInsert a j y z)
  calc
    fderiv ℝ (sliceFull a j z φ) y (kcDir (cellCount a j) t k)
        = fderiv ℝ (fun w : X (cellCount a j) => φ (fullInsert a j w z)) y d := by
          dsimp [d]
          rfl
    _ = lineDeriv ℝ (fun w : X (cellCount a j) => φ (fullInsert a j w z)) y d := by
          exact (DifferentiableAt.lineDeriv_eq_fderiv hdiff).symm
    _ = deriv (fun s : ℝ => φ (fullInsert a j (y + s • d) z)) 0 := by
          rfl
    _ = deriv (fun s : ℝ => φ (fullInsert a j y z + s • kcDir N i' k)) 0 := by
          congr 1
          funext s
          dsimp [d]
          rw [fullInsert_path a j z y t k s]
    _ = lineDeriv ℝ φ (fullInsert a j y z) (kcDir N i' k) := by
          rfl
    _ = fderiv ℝ φ (fullInsert a j y z) (kcDir N i' k) := by
          exact DifferentiableAt.lineDeriv_eq_fderiv hφdiff
    _ = fderiv ℝ φ (fullInsert a j y z)
        (kcDir N (((occEquiv a j) t : {i : Fin N // i ∈ occSet a j}) : Fin N) k) := by
          rfl

/-- **INT1**: the total mass of `φ` is the double integral of the squared
slices over the occupied and complement fibers. -/
lemma sliceFull_sq_integral {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    {φ : X N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcs : HasCompactSupport φ) :
    (∫ x : X N, (φ x) ^ 2) =
      ∫ y : X (cellCount a j), ∫ z : X (N - cellCount a j),
        (sliceFull a j z φ y) ^ 2 := by
  have hφc : Continuous φ := hφ.continuous
  have hI : Integrable (fun x : X N => φ x * φ x) volume := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hφc.mul hφc
    · exact hcs.mul_right
  have hAe : AEMeasurable (fun x : X N => φ x * φ x) volume :=
    hI.aestronglyMeasurable.aemeasurable
  calc
    (∫ x : X N, (φ x) ^ 2)
        = ∫ x : X N, φ x * φ x := by
          apply integral_congr_ae
          filter_upwards with x
          rw [pow_two]
    _ = ∫ y : X (cellCount a j), ∫ z : X (N - cellCount a j),
            φ (fullInsert a j y z) * φ (fullInsert a j y z) := by
          exact integral_fullInsert a j hAe hI
    _ = ∫ y : X (cellCount a j), ∫ z : X (N - cellCount a j),
            (sliceFull a j z φ y) ^ 2 := by
          apply integral_congr_ae
          filter_upwards with y
          apply integral_congr_ae
          filter_upwards with z
          rw [pow_two]
          rfl

/-- The within-cell-j gradient energy of `φ` (kinetic in the occupied
particles plus intra-cell pairs). -/
noncomputable def cellGradEnergy {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (v : ℝ³ → ℝ) {φ : X N → ℝ} : ℝ :=
  (∫ x : X N, ∑ i ∈ occSet a j, ∑ k : Fin 3, (fderiv ℝ φ x (kcDir N i k)) ^ 2) +
    ∫ x : X N, (φ x) ^ 2 * (∑ p ∈ cellPairs a j, v (x p.1 - x p.2))

/-- A sum over the occupied set equals the corresponding sum over the
enumerating indices. -/
lemma sum_occSet_eq_sum_fin {m N : ℕ} (a : Assign m N) (j : CellIdx m) (C : Fin N → ℝ) :
    (∑ i ∈ occSet a j, C i) =
      ∑ t : Fin (cellCount a j), C (((occEquiv a j) t : {i : Fin N // i ∈ occSet a j}) : Fin N) := by
  classical
  calc
    (∑ i ∈ occSet a j, C i)
        = ∑ s : {i : Fin N // i ∈ occSet a j}, C (s : Fin N) := by
          exact (Finset.sum_coe_sort (occSet a j) C).symm
    _ = ∑ t : Fin (cellCount a j), C (((occEquiv a j) t : {i : Fin N // i ∈ occSet a j}) : Fin N) := by
          exact (Equiv.sum_comp (occEquiv a j).toEquiv (fun s : {i : Fin N // i ∈ occSet a j} => C (s : Fin N))).symm

/-- Pointwise: the kinetic density of the full configuration is the
slice-gradient density in the occupied coordinates. -/
lemma slice_kin_density {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (z : X (N - cellCount a j)) {φ : X N → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (y : X (cellCount a j)) :
    (∑ i ∈ occSet a j, ∑ k : Fin 3, (fderiv ℝ φ (fullInsert a j y z) (kcDir N i k)) ^ 2) =
      ∑ t : Fin (cellCount a j), ∑ k : Fin 3,
        (fderiv ℝ (sliceFull a j z φ) y (kcDir (cellCount a j) t k)) ^ 2 := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  rw [sum_occSet_eq_sum_fin a j (fun i =>
    ∑ k : Fin 3, (fderiv ℝ φ (fullInsert a j y z) (kcDir N i k)) ^ 2)]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro k hk
  rw [sliceFull_fderiv a j z hφ1 y t k]

/-- value-injectivity of the enumeration -/
lemma occEquiv_val_inj {m N : ℕ} (a : Assign m N) (j : CellIdx m) {t₁ t₂ : Fin (cellCount a j)}
    (h : (((occEquiv a j) t₁ : {i : Fin N // i ∈ occSet a j}) : Fin N) =
          (((occEquiv a j) t₂ : {i : Fin N // i ∈ occSet a j}) : Fin N)) :
    t₁ = t₂ := by
  apply (occEquiv a j).injective
  apply Subtype.ext
  exact h

/-- The enumeration preserves the strict order (both directions). -/
lemma occEquiv_val_lt_iff {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    {t₁ t₂ : Fin (cellCount a j)} :
    ((((occEquiv a j) t₁ : {i : Fin N // i ∈ occSet a j}) : Fin N) <
      (((occEquiv a j) t₂ : {i : Fin N // i ∈ occSet a j}) : Fin N)) ↔ t₁ < t₂ := by
  constructor
  · intro h
    have hs := (occEquiv a j).symm.strictMono h
    rwa [(occEquiv a j).symm_apply_apply t₁, (occEquiv a j).symm_apply_apply t₂] at hs
  · intro h
    exact occEquiv_strictMono a j h

/-- cellPairs membership -/
lemma cellPairs_mem_iff {m N : ℕ} (a : Assign m N) (j : CellIdx m) (p : Fin N × Fin N) :
    p ∈ cellPairs a j ↔ p.1 < p.2 ∧ a p.1 = j ∧ a p.2 = j := by
  simp [cellPairs]

/-- the full-insertion of an enumerated occupied particle reads the index back -/
lemma fullInsert_occEquiv_apply {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (y : X (cellCount a j)) (z : X (N - cellCount a j)) (t : Fin (cellCount a j)) :
    fullInsert a j y z (((occEquiv a j) t : {i : Fin N // i ∈ occSet a j}) : Fin N) = y t := by
  rw [fullInsert_apply_occ a j y z ((occEquiv a j) t).property]
  congr 1
  exact (occEquiv a j).symm_apply_apply t

/-- Ordered index pairs are in bijection with the cell pairs (via σ). -/
lemma cellPairs_eq_image {m N : ℕ} (a : Assign m N) (j : CellIdx m) :
    cellPairs a j =
      ((Finset.univ.filter (fun q : Fin (cellCount a j) × Fin (cellCount a j) => q.1 < q.2))).image
        (fun q : Fin (cellCount a j) × Fin (cellCount a j) =>
          ((((occEquiv a j) q.1 : {i : Fin N // i ∈ occSet a j}) : Fin N),
           (((occEquiv a j) q.2 : {i : Fin N // i ∈ occSet a j}) : Fin N))) := by
  classical
  ext p
  constructor
  · intro hp
    rw [Finset.mem_image]
    have hc := (cellPairs_mem_iff a j p).mp hp
    let hm1 : p.1 ∈ occSet a j := by simpa [occSet] using hc.2.1
    let hm2 : p.2 ∈ occSet a j := by simpa [occSet] using hc.2.2
    refine ⟨((occEquiv a j).symm ⟨p.1, hm1⟩, (occEquiv a j).symm ⟨p.2, hm2⟩), ?mem, ?eq⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (occEquiv a j).symm.strictMono hc.1
    · congr 1
      · change (((occEquiv a j) ((occEquiv a j).symm ⟨p.1, hm1⟩) : {i : Fin N // i ∈ occSet a j}) : Fin N) = p.1
        have h := (occEquiv a j).apply_symm_apply (x := ⟨p.1, hm1⟩)
        rw [h]
      · change (((occEquiv a j) ((occEquiv a j).symm ⟨p.2, hm2⟩) : {i : Fin N // i ∈ occSet a j}) : Fin N) = p.2
        have h := (occEquiv a j).apply_symm_apply (x := ⟨p.2, hm2⟩)
        rw [h]
  · intro hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨q, hq, hσ⟩
    have hltq : q.1 < q.2 := by simpa using (Finset.mem_filter.mp hq).2
    rw [cellPairs_mem_iff]
    constructor
    · have hp1 : p.1 = (((occEquiv a j) q.1 : {i : Fin N // i ∈ occSet a j}) : Fin N) := (congrArg Prod.fst hσ).symm
      have hp2 : p.2 = (((occEquiv a j) q.2 : {i : Fin N // i ∈ occSet a j}) : Fin N) := (congrArg Prod.snd hσ).symm
      rw [hp1, hp2]
      exact occEquiv_strictMono a j hltq
    · constructor
      · rw [← congrArg Prod.fst hσ]
        exact occEquiv_mem a j q.1
      · rw [← congrArg Prod.snd hσ]
        exact occEquiv_mem a j q.2

/-- σ is injective on the index pairs. -/
lemma occEquiv_pair_inj {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    {q₁ q₂ : Fin (cellCount a j) × Fin (cellCount a j)}
    (h : (((((occEquiv a j) q₁.1 : {i : Fin N // i ∈ occSet a j}) : Fin N),
       (((occEquiv a j) q₁.2 : {i : Fin N // i ∈ occSet a j}) : Fin N)) =
      ((((occEquiv a j) q₂.1 : {i : Fin N // i ∈ occSet a j}) : Fin N),
       (((occEquiv a j) q₂.2 : {i : Fin N // i ∈ occSet a j}) : Fin N)))) :
    q₁ = q₂ := by
  apply Prod.ext
  · apply occEquiv_val_inj
    exact congrArg Prod.fst h
  · apply occEquiv_val_inj
    exact congrArg Prod.snd h

/-- Reindexing the cell-pair sum: ordered `Fin`-pairs vs. cell pairs. -/
lemma cellPairs_sum_fullInsert {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (z : X (N - cellCount a j)) (y : X (cellCount a j)) (v : ℝ³ → ℝ) :
    (∑ p ∈ cellPairs a j, v (fullInsert a j y z p.1 - fullInsert a j y z p.2)) =
      intPairSum (cellCount a j) v y := by
  classical
  let pairSet : Finset (Fin (cellCount a j) × Fin (cellCount a j)) :=
    Finset.univ.filter (fun q : Fin (cellCount a j) × Fin (cellCount a j) => q.1 < q.2)
  let σ : Fin (cellCount a j) × Fin (cellCount a j) → Fin N × Fin N := fun q =>
    ((((occEquiv a j) q.1 : {i : Fin N // i ∈ occSet a j}) : Fin N),
     (((occEquiv a j) q.2 : {i : Fin N // i ∈ occSet a j}) : Fin N))
  calc
    (∑ p ∈ cellPairs a j, v (fullInsert a j y z p.1 - fullInsert a j y z p.2))
        = ∑ p ∈ (pairSet.image σ), v (fullInsert a j y z p.1 - fullInsert a j y z p.2) := by
          rw [show cellPairs a j = pairSet.image σ by
            dsimp [pairSet, σ]
            exact cellPairs_eq_image a j]
    _ = ∑ q ∈ pairSet, v (fullInsert a j y z (σ q).1 - fullInsert a j y z (σ q).2) := by
          refine Finset.sum_image ?_
          intro q₁ hq₁ q₂ hq₂ h
          dsimp [σ] at h
          exact occEquiv_pair_inj a j h
    _ = ∑ q ∈ pairSet, v (y q.1 - y q.2) := by
          apply Finset.sum_congr rfl
          intro q hq
          congr 1
          dsimp [σ]
          rw [fullInsert_occEquiv_apply, fullInsert_occEquiv_apply]
    _ = intPairSum (cellCount a j) v y := by
          dsimp [pairSet]
          unfold intPairSum
          rfl

/-- The full-space integral is the integral over the complement of the
integral over the occupied fiber (Fubini after the change of variables). -/
lemma integral_fullInsert_swap {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    {G : X N → ℝ} (hG : Integrable G volume)
    {H : X (cellCount a j) → X (N - cellCount a j) → ℝ}
    (hH : ∀ y z, H y z = G (fullInsert a j y z)) :
    (∫ x : X N, G x) = ∫ z : X (N - cellCount a j), ∫ y : X (cellCount a j), H y z := by
  let f : X (cellCount a j) × X (N - cellCount a j) → ℝ := fun p =>
    G (fullInsert a j p.1 p.2)
  have hFint : Integrable (fun p : X (cellCount a j) × X (N - cellCount a j) =>
      H p.1 p.2) volume := by
    have hfInt : Integrable f volume :=
      (measurePreserving_fullEquiv a j).integrable_comp_of_integrable hG
    apply hfInt.congr
    filter_upwards with p
    dsimp [f]
    exact (hH p.1 p.2).symm
  calc
    (∫ x : X N, G x)
        = ∫ p : X (cellCount a j) × X (N - cellCount a j), f p := by
          have hemb : MeasurableEmbedding (⇑(fullEquiv a j)) := by
            rw [fullEquiv_eq_fmEins a j]
            exact (fmEins a j).measurableEmbedding
          exact (MeasurePreserving.integral_comp (measurePreserving_fullEquiv a j) hemb G).symm
    _ = ∫ p : X (cellCount a j) × X (N - cellCount a j), H p.1 p.2 := by
          apply integral_congr_ae
          filter_upwards with p
          dsimp [f]
          exact (hH p.1 p.2).symm
    _ = ∫ z : X (N - cellCount a j), ∫ y : X (cellCount a j), H y z := by
          exact integral_prod_symm
            (μ := (volume : Measure (X (cellCount a j))))
            (ν := (volume : Measure (X (N - cellCount a j))))
            (f := fun p : X (cellCount a j) × X (N - cellCount a j) => H p.1 p.2) hFint

/-- The partial integral over the occupied fiber is integrable in the
complement coordinate (Fubini consequence). -/
lemma zIntegrable_fullInsert {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    {G : X N → ℝ} (hG : Integrable G volume)
    {H : X (cellCount a j) → X (N - cellCount a j) → ℝ}
    (hH : ∀ y z, H y z = G (fullInsert a j y z)) :
    Integrable (fun z : X (N - cellCount a j) => ∫ y : X (cellCount a j), H y z) volume := by
  let f : X (cellCount a j) × X (N - cellCount a j) → ℝ := fun p =>
    G (fullInsert a j p.1 p.2)
  have hFint : Integrable (fun p : X (cellCount a j) × X (N - cellCount a j) =>
      H p.1 p.2) volume := by
    have hfInt : Integrable f volume :=
      (measurePreserving_fullEquiv a j).integrable_comp_of_integrable hG
    apply hfInt.congr
    filter_upwards with p
    dsimp [f]
    exact (hH p.1 p.2).symm
  have hFsw : Integrable (fun q : X (N - cellCount a j) × X (cellCount a j) =>
      H q.2 q.1) (volume.prod volume) := by
    simpa [Function.comp_def] using hFint.swap
  exact hFsw.integral_prod_left

/-- The squared gradient density is integrable. -/
lemma integrable_kinDensity {N : ℕ} {φ : X N → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hcs : HasCompactSupport φ) (s : Finset (Fin N)) :
    Integrable (fun x : X N => ∑ i ∈ s, ∑ k : Fin 3,
      (fderiv ℝ φ x (kcDir N i k)) ^ 2) volume := by
  have hcont : Continuous (fun x : X N => ∑ i ∈ s, ∑ k : Fin 3,
      (fderiv ℝ φ x (kcDir N i k)) ^ 2) := by
    refine continuous_finsetSum (s := s) ?_ -- hmm this needs f : Fin N → X N → ℝ and sums ∑ x ∈ s
    intro i hi
    refine continuous_finsetSum (s := Finset.univ) (f := fun k : Fin 3 => fun x => (fderiv ℝ φ x (kcDir N i k)) ^ 2) ?_
    intro k hk
    exact (firstDir_contDiff hφ (kcDir N i k)).continuous.pow 2
  have hcsS : HasCompactSupport (fun x : X N => ∑ i ∈ s, ∑ k : Fin 3,
      (fderiv ℝ φ x (kcDir N i k)) ^ 2) := by
    refine IsCompact.of_isClosed_subset hcs (isClosed_tsupport _) ?_
    refine closure_minimal ?_ (isClosed_tsupport φ)
    intro x hx
    by_contra hxφ
    -- each term vanishes at x
    have hzero : (∑ i ∈ s, ∑ k : Fin 3, (fderiv ℝ φ x (kcDir N i k)) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro k hk
      have hder : fderiv ℝ φ x (kcDir N i k) = 0 := by
        by_contra hd
        have hd0 : x ∈ Function.support (fun y : X N => fderiv ℝ φ y (kcDir N i k)) := by
          exact Function.mem_support.mpr hd
        have hs2 := tsupport_firstDir_subset (f := φ) (kcDir N i k) (subset_tsupport _ hd0)
        exact hxφ hs2
      simp [hder]
    exact hx (by simp [Function.mem_support] at hx ⊢; simp [hzero])
  exact Continuous.integrable_of_hasCompactSupport hcont hcsS


/-- **INT2**: the within-cell-`j` energy of `φ` equals the integral over the
frozen background of the whole-space slice energies. -/
lemma cellGradEnergy_integral {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    {v : ℝ³ → ℝ} (hv1 : MemLp v 1) {φ : X N → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hcs : HasCompactSupport φ) :
    cellGradEnergy a j v (φ := φ) =
      ∫ z : X (N - cellCount a j), sliceWsE (cellCount a j) v (sliceFull a j z φ) := by
  classical
  let K : X N → ℝ := fun x =>
    ∑ i ∈ occSet a j, ∑ k : Fin 3, (fderiv ℝ φ x (kcDir N i k)) ^ 2
  let P : X N → ℝ := fun x =>
    (φ x) ^ 2 * (∑ p ∈ cellPairs a j, v (x p.1 - x p.2))
  let C : X (cellCount a j) → X (N - cellCount a j) → ℝ := fun y z =>
    ∑ t : Fin (cellCount a j), ∑ k : Fin 3,
      (fderiv ℝ (sliceFull a j z φ) y (kcDir (cellCount a j) t k)) ^ 2
  let D : X (cellCount a j) → X (N - cellCount a j) → ℝ := fun y z =>
    (sliceFull a j z φ y) ^ 2 * intPairSum (cellCount a j) v y
  have hK : Integrable K volume := by
    dsimp [K]
    exact integrable_kinDensity hφ hcs (occSet a j)
  have hP : Integrable P volume := by
    have hP' : P = fun x : X N =>
        ∑ p ∈ cellPairs a j, (φ x) ^ 2 * v (x p.1 - x p.2) := by
      funext x
      dsimp [P]
      rw [Finset.mul_sum]
    rw [hP']
    exact integrable_finsetSum (s := cellPairs a j)
      (f := fun p : Fin N × Fin N => fun x : X N =>
        (φ x) ^ 2 * v (x p.1 - x p.2)) (fun p hp => pairInt_sq hv1 hφ.continuous hcs p.1 p.2)
  have hCK : ∀ y z, C y z = K (fullInsert a j y z) := by
    intro y z
    dsimp [C, K]
    exact (slice_kin_density a j z hφ y).symm
  have hPD : ∀ y z, D y z = P (fullInsert a j y z) := by
    intro y z
    dsimp [D, P]
    rw [cellPairs_sum_fullInsert a j z y v]
    rfl
  calc
    cellGradEnergy a j v (φ := φ)
        = (∫ x : X N, K x) + ∫ x : X N, P x := by
          dsimp [cellGradEnergy, K, P]
    _ = (∫ z : X (N - cellCount a j), ∫ y : X (cellCount a j), C y z) +
          (∫ z : X (N - cellCount a j), ∫ y : X (cellCount a j), D y z) := by
          congr 1
          · exact integral_fullInsert_swap a j hK hCK
          · exact integral_fullInsert_swap a j hP hPD
    _ = ∫ z : X (N - cellCount a j),
          (∫ y : X (cellCount a j), C y z) + (∫ y : X (cellCount a j), D y z) := by
          exact (integral_add (zIntegrable_fullInsert a j hK hCK)
            (zIntegrable_fullInsert a j hP hPD)).symm
    _ = ∫ z : X (N - cellCount a j), sliceWsE (cellCount a j) v (sliceFull a j z φ) := by
          apply integral_congr_ae
          filter_upwards with z
          dsimp [sliceWsE, C, D]



end BoseGases

end Submission
