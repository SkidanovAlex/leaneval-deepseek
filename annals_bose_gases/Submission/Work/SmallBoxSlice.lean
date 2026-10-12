import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import ChallengeDeps
import Submission.PotWords
import Submission.Work.SmallBoxL2Modes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
/-!
# Session-260 — the per-particle excitation slice layer (L²(acube s) slices
of `Q_iΦ` over the rest-coordinates)

The D1 `tBword` construction (Session-232/259 notes: "Σ_i ∫ over
rest-coordinates of `tBmode(s,c, χ_B·(Q_iΦ)-slice)`") needs, as its
foundation, the per-particle EXCITATION SLICE: for an `(n+1)`-particle
state `Φ` and particle `i`, the function of particle-`i`'s coordinate `y`
obtained by freezing the other `n` particles at the rest-configuration
`r ∈ X n`, with the condensate part removed (`aQ`):

    excSliceFun s i Φ r y := (aQ s i Φ)(kcInsN n i (y, r))          (pointwise)
    excSlice    s i Φ r    := toLp of the above in L²(acube s)       (Hilbert)

(`kcInsN n i (y, r)` inserts particle `i` at `y`, the others at `r`; the
`aQ`-fibre = `Q_i`-fibre because `aP` = the cube-mean projection onto
constants, matching the FS `Q_{B,i} = 1_{B} − P_{B,i}`).  Contents:

  * `excSliceFun_continuous` — the fibre is continuous in `y` (via
    `kcInsN_update_zero` + `fun_prop` on the `Function.update` insertion);
  * `excSliceFun_bddOn_cube` — bounded on the (compact) cube
    (`IsCompact.exists_isMaxOn` extreme-value theorem);
  * `excSlice_memLp` — the `MemLp` certificate over `boxVol s`
    (`MemLp.of_bound` with the cube bound, `ae_restrict_mem`);
  * `excSlice` — the slice as an `Lp ℝ 2 (boxVol s)` element;
  * `toLp_inner_self_eq_integral` / `toLp_normSq_eq_integral` —
    `‖toLp g‖² = ∫ (g y)²` over the box (`L2.inner_def` +
    `MemLp.coeFn_toLp` + `real_inner_self_eq_norm_sq`);
  * `excSlice_normSq_eq_integral` — `‖slice r‖² = ∫_{acube s} (Q_iΦ-fibre)²`;
  * **`excSlice_normSq_integral_excited`** — Fubini along the peel at
    particle `i` (`Q0Sector.abox_integral_peel`): the integral over the
    rest-coordinates of the slice squared norm equals the per-particle
    excited norm over the full box:
    `∫_{r ∈ abox n s} ‖excSlice s i Φ r‖² = ∫_{x ∈ abox (n+1) s} (aQ s i Φ x)²`.

The next module (the `tBword` word proper) consumes these: summing the
`tBmode(s,c,·)`-weighted values over the particles with
`tBmode ≤ (headSum + tailC)·‖·‖²` (`SmallBoxTBmode.tBmode_const_le`) gives
the per-particle bound by `∫‖slice‖²` = the excited norm — the
D1-diagonalisation's input.
-/


noncomputable section
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
namespace Submission
open _root_.BoseGases
namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- the excitation fibre over particle `i` at rest-configuration `r`: the
pointwise function `y ↦ (Q_iΦ)(insert_i (y,r))` on the single-particle
coordinate space. -/
noncomputable def excSliceFun (s : ℝ) {n : ℕ} (i : Fin (n+1)) (Φ : X (n+1) → ℝ)
    (r : X n) (y : ℝ³) : ℝ :=
  aQ s i Φ (kcInsN n i (y, r))

-- continuity of the fibre in y
lemma excSliceFun_continuous (s : ℝ) (hs : 0 < s) {n : ℕ} (i : Fin (n+1))
    (Φ : X (n+1) → ℝ) (hΦc : Continuous Φ) (r : X n) :
    Continuous (excSliceFun s i Φ r) := by
  have hcQ : Continuous (aQ s i Φ) := aQ_continuous hs i hΦc
  -- insertion map continuous via update
  have hins : Continuous (fun y : ℝ³ => kcInsN n i (y, r)) := by
    have h1 : (fun y : ℝ³ => kcInsN n i (y, r)) =
        (fun y : ℝ³ => Function.update (kcInsN n i (0, r)) i y) := by
      funext y
      exact kcInsN_update_zero i y r
    rw [h1]
    fun_prop
  exact hcQ.comp hins

-- boundedness on the cube: |fibre| ≤ B for all y ∈ acube s
lemma excSliceFun_bddOn_cube (s : ℝ) (hs : 0 < s) {n : ℕ} (i : Fin (n+1))
    (Φ : X (n+1) → ℝ) (hΦc : Continuous Φ) (r : X n) :
    ∃ B : ℝ, (∀ y : ℝ³, y ∈ acube s → |excSliceFun s i Φ r y| ≤ B) ∧ 0 ≤ B := by
  have hc : Continuous (fun y : ℝ³ => |excSliceFun s i Φ r y|) :=
    (excSliceFun_continuous s hs i Φ hΦc r).norm
  have hne : (acube s).Nonempty := by
    refine ⟨0, ?_⟩
    rw [mem_acube_iff]
    intro j
    have hz : (0 : ℝ³) j = 0 := by simp
    rw [hz]
    constructor <;> nlinarith
  rcases IsCompact.exists_isMaxOn (acube_compact hs) hne hc.continuousOn with ⟨y0, hy0, hmax⟩
  refine ⟨|excSliceFun s i Φ r y0|, ?_, abs_nonneg _⟩
  intro y hy
  exact (isMaxOn_iff.mp hmax) y hy

-- MemLp certificate
lemma excSlice_memLp (s : ℝ) (hs : 0 < s) {n : ℕ} (i : Fin (n+1))
    (Φ : X (n+1) → ℝ) (hΦc : Continuous Φ) (r : X n) :
    MemLp (excSliceFun s i Φ r) (2 : ℝ≥0∞) (boxVol s) := by
  have hmeas : AEStronglyMeasurable (excSliceFun s i Φ r) (boxVol s) :=
    (excSliceFun_continuous s hs i Φ hΦc r).aestronglyMeasurable
  rcases excSliceFun_bddOn_cube s hs i Φ hΦc r with ⟨B, hB, hB0⟩
  refine MemLp.of_bound (p := (2 : ℝ≥0∞)) hmeas (C := B) ?_
  -- |fibre y| ≤ B a.e. wrt boxVol s  (holds pointwise on acube s)
  have hmem : ∀ᵐ y ∂(boxVol s), y ∈ acube s :=
    MeasureTheory.ae_restrict_mem (acube_measurable s)
  filter_upwards [hmem] with y hy
  exact hB y hy

/-- the excitation slice as an L²(acube s) element. -/
noncomputable def excSlice (s : ℝ) (hs : 0 < s) {n : ℕ} (i : Fin (n+1))
    (Φ : X (n+1) → ℝ) (hΦc : Continuous Φ) (r : X n) : Lp ℝ 2 (boxVol s) :=
  MemLp.toLp (excSliceFun s i Φ r) (excSlice_memLp s hs i Φ hΦc r)



/-- the real L² inner product of a `toLp`-slice with itself equals the box
integral of its pointwise square. -/
lemma toLp_inner_self_eq_integral {s : ℝ} (g : ℝ³ → ℝ) (hg : MemLp g 2 (boxVol s)) :
    inner ℝ (MemLp.toLp g hg) (MemLp.toLp g hg) =
      ∫ y : ℝ³, (g y) ^ 2 ∂(boxVol s) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  have hg' : (((MemLp.toLp g hg : Lp ℝ 2 (boxVol s)) : ℝ³ → ℝ)) =ᵐ[boxVol s] g := by
    simpa using (MemLp.coeFn_toLp hg)
  filter_upwards [hg'] with y hy
  rw [hy, Real.inner_apply]
  ring

/-- the `toLp`-L²-norm squared equals the box integral of the pointwise
square of the function. -/
lemma toLp_normSq_eq_integral {s : ℝ} (g : ℝ³ → ℝ) (hg : MemLp g 2 (boxVol s)) :
    ‖MemLp.toLp g hg‖ ^ 2 = ∫ y : ℝ³, (g y) ^ 2 ∂(boxVol s) := by
  have hns : ‖MemLp.toLp g hg‖ ^ 2 =
      inner ℝ (MemLp.toLp g hg) (MemLp.toLp g hg) := by
    exact (real_inner_self_eq_norm_sq (MemLp.toLp g hg)).symm
  rw [hns]
  exact toLp_inner_self_eq_integral g hg

/-- the slice L²-norm squared equals the box integral of the pointwise
square of the excitation fibre. -/
lemma excSlice_normSq_eq_integral (s : ℝ) (hs : 0 < s) {n : ℕ} (i : Fin (n+1))
    (Φ : X (n+1) → ℝ) (hΦc : Continuous Φ) (r : X n) :
    ‖excSlice s hs i Φ hΦc r‖ ^ 2 =
      ∫ y : ℝ³, (aQ s i Φ (kcInsN n i (y, r))) ^ 2 ∂(boxVol s) := by
  unfold excSlice
  exact toLp_normSq_eq_integral (g := fun y : ℝ³ => aQ s i Φ (kcInsN n i (y, r)))
    (excSlice_memLp s hs i Φ hΦc r)



/-- the integral over the rest-coordinates of the slice squared norm equals
the per-particle excited norm over the full box (Fubini along the peel at
particle `i`). -/
lemma excSlice_normSq_integral_excited (s : ℝ) (hs : 0 < s) {n : ℕ} (i : Fin (n+1))
    (Φ : X (n+1) → ℝ) (hΦc : Continuous Φ) :
    (∫ r in abox n s, ‖excSlice s hs i Φ hΦc r‖ ^ 2)
      = ∫ x in abox (n + 1) s, (aQ s i Φ x) ^ 2 := by
  have hF : IntegrableOn (fun x : X (n + 1) => (aQ s i Φ x) ^ 2) (abox (n + 1) s) volume :=
    integrableOn_abox_of_continuous hs ((aQ_continuous hs i hΦc).pow 2)
  have hpeel := abox_integral_peel (n := n) (ℓ := s) i (fun x : X (n + 1) => (aQ s i Φ x) ^ 2) hF
  calc
    (∫ r in abox n s, ‖excSlice s hs i Φ hΦc r‖ ^ 2)
        = ∫ r in abox n s, (∫ y : ℝ³, (aQ s i Φ (kcInsN n i (y, r))) ^ 2 ∂(boxVol s)) := by
            apply integral_congr_ae
            filter_upwards with r
            exact excSlice_normSq_eq_integral s hs i Φ hΦc r
    _ = ∫ x in abox (n + 1) s, (aQ s i Φ x) ^ 2 := by
            simpa using hpeel.symm

/-! ## Session-260 part 2 — continuity certificates (the `tBword` h2/h1
inputs): the insertion, the fibre and the slices are continuous over the
compact rest-box.

`kcInsN_continuous` (componentwise via `continuous_pi` + `kc_insN_apply_same`
/`kc_insN_apply_succ`), `fibre_joint_continuous` (composition with
`aQ_continuous`), `fibre_cont_y` / `fibre_cont_r` (partial maps of the joint
fibre), `fibre_bddOn_rest_cube` (bound of the fibre on
`acube s × abox n s` via `IsCompact.exists_bound_of_continuousOn`), and the
two headline continuity certificates:

  * `slice_normSq_continuousOn` — `r ↦ ‖slice r‖²` is continuous on the
    compact `abox n s` (dominated convergence
    `MeasureTheory.continuousOn_of_dominated` on `(r,y) ↦ (fibre r y)²`
    with the constant bound `M²`, `M` from `fibre_bddOn_rest_cube`; the
    pointwise identity `‖slice r‖² = ∫_y (fibre)²` is
    `excSlice_normSq_eq_integral`);
  * `slice_sub_normSq` — the squared `L²`-distance between two slices is the
    box integral of the squared pointwise fibre difference (`MemLp.toLp_sub`
    + `toLp_normSq_eq_integral` on the difference);
  * **`excSlice_continuousOn`** — the slice map `r ↦ slice r : X n →
    Lp ℝ 2 (boxVol s)` is continuous on `abox n s`: fix `r₀`; the squared
    distance `J(r) := ∫_y (Δfibre)²` is continuous within `s` at `r₀`
    (`MeasureTheory.continuousWithinAt_of_dominated`, constant bound
    `(2M)²`), vanishes at `r₀`, and `√` transfers the limit to the norm
    (`Metric.tendsto_iff_dist_tendsto_zero` via the root-namespace
    `tendsto_iff_dist_tendsto_zero`).

These give `h2` of `SmallBoxTBword.tBwordI_le_of_integrable` by
`ContinuousOn.integrableOn_compact` (and are the continuity input for `h1`,
the integrability of `r ↦ tBmode(s,c,slice r)`). -/

/-- the insertion `(y, r) ↦ kcInsN n i (y, r)` is continuous. -/
lemma kcInsN_continuous {n : ℕ} (i : Fin (n+1)) :
    Continuous (fun p : (ℝ³ × X n) => kcInsN n i p) := by
  refine continuous_pi ?_
  intro j
  by_cases hj : j = i
  · subst j
    have h : (fun p : (ℝ³ × X n) => (kcInsN n i p) i) = Prod.fst := by
      funext p
      rcases p with ⟨y, r⟩
      exact kc_insN_apply_same n i y r
    rw [h]
    exact continuous_fst
  · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
    have h : (fun p : (ℝ³ × X n) => (kcInsN n i p) (i.succAbove j')) =
        fun p : (ℝ³ × X n) => p.2 j' := by
      funext p
      rcases p with ⟨y, r⟩
      exact kc_insN_apply_succ n i y r j'
    rw [h]
    exact (by fun_prop : Continuous fun p : (ℝ³ × X n) => p.2 j')

/-- joint continuity of the fibre map `(y, r) ↦ aQ s i Φ (kcInsN n i (y, r))`. -/
lemma fibre_joint_continuous (s : ℝ) (hs : 0 < s) {n : ℕ} (i : Fin (n+1))
    (Φ : X (n+1) → ℝ) (hΦc : Continuous Φ) :
    Continuous (fun p : (ℝ³ × X n) => aQ s i Φ (kcInsN n i p)) := by
  exact (aQ_continuous hs i hΦc).comp (kcInsN_continuous i)

/-- the fibre is continuous in the single-particle coordinate `y` (fixed
rest-configuration `r`). -/
lemma fibre_cont_y (s : ℝ) (hs : 0 < s) {n : ℕ} (i : Fin (n+1))
    (Φ : X (n+1) → ℝ) (hΦc : Continuous Φ) (r : X n) :
    Continuous (fun y : ℝ³ => aQ s i Φ (kcInsN n i (y, r))) := by
  have hp : Continuous (fun y : ℝ³ => (y, r)) := by fun_prop
  exact (fibre_joint_continuous s hs i Φ hΦc).comp hp

/-- the fibre is continuous in the rest-coordinate `r` (fixed coordinate `y`). -/
lemma fibre_cont_r (s : ℝ) (hs : 0 < s) {n : ℕ} (i : Fin (n+1))
    (Φ : X (n+1) → ℝ) (hΦc : Continuous Φ) (y : ℝ³) :
    Continuous (fun r : X n => aQ s i Φ (kcInsN n i (y, r))) := by
  have hp : Continuous (fun r : X n => (y, r)) := by fun_prop
  exact (fibre_joint_continuous s hs i Φ hΦc).comp hp

/-- the fibre is bounded on `acube s × abox n s` by a nonnegative constant. -/
lemma fibre_bddOn_rest_cube (s : ℝ) (hs : 0 < s) {n : ℕ} (i : Fin (n+1))
    (Φ : X (n+1) → ℝ) (hΦc : Continuous Φ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (r : X n) (y : ℝ³), r ∈ abox n s → y ∈ acube s →
      |aQ s i Φ (kcInsN n i (y, r))| ≤ M := by
  let g : (ℝ³ × X n) → ℝ := fun p => aQ s i Φ (kcInsN n i p)
  let D : Set (ℝ³ × X n) := (acube s).prod (abox n s)
  have hg : Continuous g := fibre_joint_continuous s hs i Φ hΦc
  have hDc : IsCompact D := (acube_compact hs).prod (abox_compact n hs)
  rcases IsCompact.exists_bound_of_continuousOn hDc hg.continuousOn with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro r y hr hy
  exact le_trans (by simpa [Real.norm_eq_abs] using hC (y, r) ⟨hy, hr⟩) (le_max_left C 0)

/-- **continuity of `r ↦ ‖slice r‖²` on the rest-box** (the `h2`-certificate
of `SmallBoxTBword`): the squared `L²`-norm of the excitation slice is
continuous in the frozen rest-configuration over the compact box (dominated
convergence with the constant bound from `fibre_bddOn_rest_cube`). -/
lemma slice_normSq_continuousOn (s : ℝ) (hs : 0 < s) {n : ℕ} (i : Fin (n+1))
    (Φ : X (n+1) → ℝ) (hΦc : Continuous Φ) :
    ContinuousOn (fun r : X n => ‖excSlice s hs i Φ hΦc r‖ ^ 2) (abox n s) := by
  rcases fibre_bddOn_rest_cube s hs i Φ hΦc with ⟨M, hM0, hM⟩
  let F : X n → ℝ³ → ℝ := fun r y => (aQ s i Φ (kcInsN n i (y, r))) ^ 2
  have h1 : ContinuousOn (fun r : X n => ∫ y : ℝ³, F r y ∂(boxVol s)) (abox n s) := by
    refine MeasureTheory.continuousOn_of_dominated (μ := boxVol s) (s := abox n s)
      (bound := fun _y : ℝ³ => M ^ 2) ?_ ?_ ?_ ?_
    · intro r hr
      exact (fibre_cont_y s hs i Φ hΦc r).pow 2 |>.aestronglyMeasurable
    · intro r hr
      have hmem : ∀ᵐ y ∂(boxVol s), y ∈ acube s :=
        MeasureTheory.ae_restrict_mem (acube_measurable s)
      filter_upwards [hmem] with y hy
      have hb := hM r y hr hy
      have hsq : (aQ s i Φ (kcInsN n i (y, r))) ^ 2 ≤ M ^ 2 := by
        calc
          (aQ s i Φ (kcInsN n i (y, r))) ^ 2 = |aQ s i Φ (kcInsN n i (y, r))| ^ 2 := by rw [sq_abs]
          _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
      dsimp [F]
      have hnon : 0 ≤ (aQ s i Φ (kcInsN n i (y, r))) ^ 2 := sq_nonneg _
      rw [abs_of_nonneg hnon]
      exact hsq
    · exact integrable_const (μ := boxVol s) (c := M ^ 2)
    · filter_upwards with y
      have hc : Continuous (fun r : X n => (aQ s i Φ (kcInsN n i (y, r))) ^ 2) :=
        (fibre_cont_r s hs i Φ hΦc y).pow 2
      dsimp [F]
      exact hc.continuousOn
  have hEq : (fun r : X n => ‖excSlice s hs i Φ hΦc r‖ ^ 2)
      = fun r : X n => ∫ y : ℝ³, F r y ∂(boxVol s) := by
    funext r
    dsimp [F]
    exact (excSlice_normSq_eq_integral s hs i Φ hΦc r)
  rwa [hEq]

/-- the squared `L²`-distance between two slices equals the box integral of
the squared pointwise fibre difference. -/
lemma slice_sub_normSq (s : ℝ) (hs : 0 < s) {n : ℕ} (i : Fin (n+1))
    (Φ : X (n+1) → ℝ) (hΦc : Continuous Φ) (r r₀ : X n) :
    ‖excSlice s hs i Φ hΦc r - excSlice s hs i Φ hΦc r₀‖ ^ 2
      = ∫ y : ℝ³,
          ((aQ s i Φ (kcInsN n i (y, r))) - (aQ s i Φ (kcInsN n i (y, r₀)))) ^ 2
        ∂(boxVol s) := by
  let cf := excSlice_memLp s hs i Φ hΦc
  have hsub : excSlice s hs i Φ hΦc r - excSlice s hs i Φ hΦc r₀ =
      MemLp.toLp (excSliceFun s i Φ r - excSliceFun s i Φ r₀) ((cf r).sub (cf r₀)) := by
    unfold excSlice
    exact MemLp.toLp_sub (cf r) (cf r₀)
  calc
    ‖excSlice s hs i Φ hΦc r - excSlice s hs i Φ hΦc r₀‖ ^ 2
        = ‖MemLp.toLp (excSliceFun s i Φ r - excSliceFun s i Φ r₀)
              ((cf r).sub (cf r₀))‖ ^ 2 := by rw [hsub]
    _ = ∫ y : ℝ³, (excSliceFun s i Φ r y - excSliceFun s i Φ r₀ y) ^ 2 ∂(boxVol s) := by
          exact toLp_normSq_eq_integral (g := excSliceFun s i Φ r - excSliceFun s i Φ r₀)
            ((cf r).sub (cf r₀))
    _ = ∫ y : ℝ³,
          ((aQ s i Φ (kcInsN n i (y, r))) - (aQ s i Φ (kcInsN n i (y, r₀)))) ^ 2
        ∂(boxVol s) := by rfl

/-- **continuity of the excitation slice in the frozen rest-coordinate over
the compact rest-box** (`Lp`-valued): `r ↦ excSlice s i Φ r` is continuous
on `abox n s`.  Proof: fix `r₀`; the squared distance to the fixed slice is
`J(r) := ∫_y (Δfibre)²` (`slice_sub_normSq`), continuous at `r₀` by
dominated convergence (constant bound `(2M)²`), vanishes at `r₀`, and `√`
transfers the limit to the norm. -/
lemma excSlice_continuousOn (s : ℝ) (hs : 0 < s) {n : ℕ} (i : Fin (n+1))
    (Φ : X (n+1) → ℝ) (hΦc : Continuous Φ) :
    ContinuousOn (fun r : X n => excSlice s hs i Φ hΦc r) (abox n s) := by
  rcases fibre_bddOn_rest_cube s hs i Φ hΦc with ⟨M, hM0, hM⟩
  intro r₀ hr₀
  let j : (ℝ³ × X n) → ℝ := fun p => aQ s i Φ (kcInsN n i p)
  let J : X n → ℝ := fun r => ∫ y : ℝ³, (j (y, r) - j (y, r₀)) ^ 2 ∂(boxVol s)
  have hJcont : ContinuousWithinAt J (abox n s) r₀ := by
    refine MeasureTheory.continuousWithinAt_of_dominated (μ := boxVol s) (s := abox n s)
      (x₀ := r₀) (bound := fun _y : ℝ³ => (2 * M) ^ 2) ?_ ?_ ?_ ?_
    · filter_upwards with r
      have h1 : Continuous (fun y : ℝ³ => j (y, r)) := by
        dsimp [j]
        exact fibre_cont_y s hs i Φ hΦc r
      have h2 : Continuous (fun y : ℝ³ => j (y, r₀)) := by
        dsimp [j]
        exact fibre_cont_y s hs i Φ hΦc r₀
      exact ((h1.sub h2).pow 2).aestronglyMeasurable
    · have hall : ∀ r : X n, r ∈ abox n s → ∀ᵐ y ∂(boxVol s),
          ‖(j (y, r) - j (y, r₀)) ^ 2‖ ≤ (2 * M) ^ 2 := by
        intro r hr
        have hmem : ∀ᵐ y ∂(boxVol s), y ∈ acube s :=
          MeasureTheory.ae_restrict_mem (acube_measurable s)
        filter_upwards [hmem] with y hy
        have ha := hM r y hr hy
        have hb := hM r₀ y hr₀ hy
        have habs : |j (y, r) - j (y, r₀)| ≤ 2 * M := by
          have htri := norm_sub_le (j (y, r)) (j (y, r₀))
          calc
            |j (y, r) - j (y, r₀)| ≤ |j (y, r)| + |j (y, r₀)| := by
                  simpa [Real.norm_eq_abs] using htri
            _ ≤ M + M := add_le_add ha hb
            _ = 2 * M := by ring
        have hsq : (j (y, r) - j (y, r₀)) ^ 2 ≤ (2 * M) ^ 2 := by
          calc
            (j (y, r) - j (y, r₀)) ^ 2 = |j (y, r) - j (y, r₀)| ^ 2 := by rw [sq_abs]
            _ ≤ (2 * M) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
        dsimp
        have hnon : 0 ≤ (j (y, r) - j (y, r₀)) ^ 2 := sq_nonneg _
        rw [abs_of_nonneg hnon]
        exact hsq
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact hall r hr
    · exact integrable_const (μ := boxVol s) (c := (2 * M) ^ 2)
    · filter_upwards with y
      have h1 : Continuous (fun r : X n => j (y, r)) := by
        dsimp [j]
        exact fibre_cont_r s hs i Φ hΦc y
      have h2 : Continuous (fun r : X n => j (y, r₀)) := continuous_const
      exact (((h1.sub h2).pow 2)).continuousWithinAt
  have hJ0 : J r₀ = 0 := by
    dsimp [J]
    have hz : (fun y : ℝ³ => (j (y, r₀) - j (y, r₀)) ^ 2) = 0 := by
      funext y
      simp
    rw [hz]
    simp
  have hJt : Tendsto J (𝓝[abox n s] r₀) (𝓝 0) := by
    have hJc : Tendsto J (𝓝[abox n s] r₀) (𝓝 (J r₀)) := by
      exact hJcont
    rw [hJ0] at hJc
    exact hJc
  have hId : ∀ r : X n, r ∈ abox n s →
      ‖excSlice s hs i Φ hΦc r - excSlice s hs i Φ hΦc r₀‖ = Real.sqrt (J r) := by
    intro r hr
    have hsq := slice_sub_normSq s hs i Φ hΦc r r₀
    have hnorm : Real.sqrt (‖excSlice s hs i Φ hΦc r - excSlice s hs i Φ hΦc r₀‖ ^ 2)
        = ‖excSlice s hs i Φ hΦc r - excSlice s hs i Φ hΦc r₀‖ := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    calc
      ‖excSlice s hs i Φ hΦc r - excSlice s hs i Φ hΦc r₀‖
          = Real.sqrt (‖excSlice s hs i Φ hΦc r - excSlice s hs i Φ hΦc r₀‖ ^ 2) := hnorm.symm
      _ = Real.sqrt (J r) := by
            have hJ : J r = ‖excSlice s hs i Φ hΦc r - excSlice s hs i Φ hΦc r₀‖ ^ 2 := by
              dsimp [J]
              exact hsq.symm
            rw [hJ]
  have hsqrt : Tendsto (fun r : X n => Real.sqrt (J r)) (𝓝[abox n s] r₀) (𝓝 0) := by
    have hc := Real.continuous_sqrt.continuousAt.tendsto.comp hJt
    simpa [Function.comp_def] using hc
  have hdt : Tendsto (fun r : X n => dist (excSlice s hs i Φ hΦc r) (excSlice s hs i Φ hΦc r₀))
      (𝓝[abox n s] r₀) (𝓝 0) := by
    refine hsqrt.congr' ?_
    have hmem : (abox n s) ∈ 𝓝[abox n s] r₀ := self_mem_nhdsWithin
    refine Filter.mem_of_superset hmem ?_
    intro r hr
    change Real.sqrt (J r) = dist (excSlice s hs i Φ hΦc r) (excSlice s hs i Φ hΦc r₀)
    rw [dist_eq_norm]
    exact (hId r hr).symm
  exact (tendsto_iff_dist_tendsto_zero).2 hdt


/-! ## Session-260 part 3 — measurability of the per-mode Fourier
coefficients of the slice (the `h1` input)

For fixed mode `k`, the coefficient `r ↦ ‖⟨ê_k, slice r⟩‖²` is continuous on
the rest-box (`slice_inner_continuousOn` = inner-right-continuous composed
with `excSlice_continuousOn`), hence Borel-measurable on the box; the
piecewise-extension lemma (`ContinuousOn.measurable_piecewise`, `0` outside
the measurable box) makes it `AEMeasurable` w.r.t. the rest-restricted
measure (`slice_inner_sq_aemeasurable`).  Combined with
`AEMeasurable.tsum` (countable mode family) this yields
`SmallBoxTBword.tBmode_slice_aemeasurable` and discharges `h1`. -/

lemma norm_sq_eq_sq (x : ℝ) : ‖x‖ ^ 2 = x ^ 2 := by
  calc
    ‖x‖ ^ 2 = |x| ^ 2 := by rw [Real.norm_eq_abs]
    _ = x ^ 2 := sq_abs x

/-- inner with a fixed mode is continuous in the slice (over the rest-box). -/
lemma slice_inner_continuousOn (s : ℝ) (hs : 0 < s) {n : ℕ} (i : Fin (n+1))
    (Φ : X (n+1) → ℝ) (hΦc : Continuous Φ) (k : Fin 3 → ℕ) :
    ContinuousOn (fun r : X n =>
        inner ℝ (boxModeOrtho s hs k) (excSlice s hs i Φ hΦc r)) (abox n s) := by
  have h1 := excSlice_continuousOn s hs i Φ hΦc
  have hc : Continuous (fun f : Lp ℝ 2 (boxVol s) =>
      inner ℝ (boxModeOrtho s hs k) f) := (innerSL ℝ (boxModeOrtho s hs k)).continuous
  have hmap : Set.MapsTo (fun r : X n => excSlice s hs i Φ hΦc r) (abox n s) Set.univ := by
    intro r hr
    trivial
  exact hc.continuousOn.comp h1 hmap

/-- the squared coefficient `‖⟨ê_k, slice r⟩‖²` is measurable a.e. over the
rest-box (piecewise: continuous on the box, `0` outside). -/
lemma slice_inner_sq_aemeasurable (s : ℝ) (hs : 0 < s) {n : ℕ} (i : Fin (n+1))
    (Φ : X (n+1) → ℝ) (hΦc : Continuous Φ) (k : Fin 3 → ℕ) :
    AEMeasurable (fun r : X n => ‖inner ℝ (boxModeOrtho s hs k) (excSlice s hs i Φ hΦc r)‖ ^ 2)
      ((volume : Measure (X n)).restrict (abox n s)) := by
  classical
  let f : X n → ℝ := fun r =>
    ‖inner ℝ (boxModeOrtho s hs k) (excSlice s hs i Φ hΦc r)‖ ^ 2
  let g : X n → ℝ := fun _ => 0
  let S : Set (X n) := abox n s
  have hfcont : ContinuousOn f S := by
    dsimp [f, S]
    have hsq : ContinuousOn (fun r : X n => (inner ℝ (boxModeOrtho s hs k)
        (excSlice s hs i Φ hΦc r)) ^ 2) (abox n s) :=
      (slice_inner_continuousOn s hs i Φ hΦc k).pow 2
    refine hsq.congr ?_
    intro r hr
    exact norm_sq_eq_sq (inner ℝ (boxModeOrtho s hs k) (excSlice s hs i Φ hΦc r))
  have hpc : Measurable (S.piecewise f g) := by
    refine ContinuousOn.measurable_piecewise (f := f) (g := g) (s := S) ?_ ?_ ?_
    · simpa [S] using hfcont
    · dsimp [g]
      exact continuous_const.continuousOn
    · dsimp [S]
      exact abox_measurable n s
  refine ⟨S.piecewise f g, hpc, ?_⟩
  have hmem : ∀ᵐ r ∂((volume : Measure (X n)).restrict S), r ∈ S :=
    MeasureTheory.ae_restrict_mem (by dsimp [S]; exact abox_measurable n s)
  filter_upwards [hmem] with r hr
  simp [S, f, hr]

end BoseGases
end Submission