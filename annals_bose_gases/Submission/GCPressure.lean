import ChallengeDeps
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Convex.Continuous
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.DiagLimit
import Submission.GCBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Grand canonical layer — the pressure window comparison.

With `gcDensity v μ ρmax L := gcBox v μ ρmax L / L³` and the extremal limits

    gcLiminf v μ ρmax := liminf_L gcDensity,   gcLimsup v μ ρmax := limsup_L gcDensity,

this module proves the grid-window comparison (mirroring the canonical
`diagLimsup_le_cell`): a box of side `L ∈ [G_m, G_{m+1}]` (`G_m := mℓ+(m−1)R`)
costs no more than `m³` copies of the `ℓ`-box, so letting `m → ∞` gives, for
every cell size `ℓ`:

    gcLimsup v μ ρmax ≤ gcBox v μ ρmax ℓ / (ℓ+R)³            (gcLimsup_le_cell)

The proof splits on the sign of `gcBox v μ ρmax ℓ` (the grid subadditivity
bound can be divided through by either `G_m³` or `G_{m+1}³` depending on the
sign of the cell value) and reuses the grid-window covering machinery of
`DiagLimits` (`gridWinIdx`).  Together with the two-sided bounds on the
density this is the input to the corridor-absorption step that produces the
pressure limit `p(μ)`.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Definitions and two-sided boundedness -/

/-- The grand-canonical energy density of a box of side `L`. -/
noncomputable def gcDensity (v : ℝ³ → ℝ) (μ ρmax : ℝ) (L : ℝ) : ℝ :=
  gcBox v μ ρmax L / L ^ 3

/-- The liminf of the grand-canonical energy density as `L → ∞`. -/
noncomputable def gcLiminf (v : ℝ³ → ℝ) (μ ρmax : ℝ) : ℝ :=
  Filter.liminf (fun L : ℝ => gcDensity v μ ρmax L) atTop

/-- The limsup of the grand-canonical energy density as `L → ∞`. -/
noncomputable def gcLimsup (v : ℝ³ → ℝ) (μ ρmax : ℝ) : ℝ :=
  Filter.limsup (fun L : ℝ => gcDensity v μ ρmax L) atTop

/-- Eventually the gc density is bounded above (product trial state). -/
lemma gcDensity_eventually_bdd_above {v : ℝ³ → ℝ} {μ ρmax : ℝ} (hμ : 0 ≤ μ)
    (hv : 0 ≤ v) (hv1 : MemLp v 1) (hρmax : 0 ≤ ρmax) :
    ∃ B : ℝ, ∀ᶠ L : ℝ in atTop, gcDensity v μ ρmax L ≤ B := by
  rcases gcBox_density_le_bound (μ := μ) (ρmax := ρmax) hμ hv hv1 hρmax with ⟨C, hCpos, hbd⟩
  refine ⟨C * (ρmax ^ 2 * vL1 v + ρmax), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL1
  exact hbd hL1

/-- Eventually the gc density is bounded below by `−μρmax`. -/
lemma gcDensity_eventually_bdd_below {v : ℝ³ → ℝ} {μ ρmax : ℝ} (hμ : 0 ≤ μ)
    (hρmax : 0 ≤ ρmax) (hv : 0 ≤ v) :
    ∃ b : ℝ, ∀ᶠ L : ℝ in atTop, b ≤ gcDensity v μ ρmax L := by
  refine ⟨-(μ * ρmax), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL1
  have hLpos : 0 < L := by linarith
  exact gcBox_density_ge (μ := μ) (ρmax := ρmax) (L := L) hμ hρmax hLpos hv

/-! ## Generic limsup with an arbitrary lower bound -/

/-- `limsup u ≤ B` from an eventual upper bound, provided `u` is eventually
bounded below by some `b`. -/
lemma limsup_le_of_eventually_le_lb {u : ℝ → ℝ} {B b : ℝ}
    (hB : ∀ᶠ L : ℝ in atTop, u L ≤ B)
    (hb : ∀ᶠ L : ℝ in atTop, b ≤ u L) : limsup u atTop ≤ B := by
  rw [limsup_eq]
  apply csInf_le
  · refine ⟨b, ?_⟩
    intro a ha
    exact atTop_le_of_eventually hb ha
  · simpa using hB

/-- The gc limsup is `≤` any eventual upper bound of the density. -/
lemma gcLimsup_le_of_eventually_le {v : ℝ³ → ℝ} {μ ρmax : ℝ} (hμ : 0 ≤ μ)
    (hρmax : 0 ≤ ρmax) (hv : 0 ≤ v) {B : ℝ}
    (hB : ∀ᶠ L : ℝ in atTop, gcDensity v μ ρmax L ≤ B) :
    gcLimsup v μ ρmax ≤ B := by
  unfold gcLimsup
  rcases gcDensity_eventually_bdd_below (μ := μ) (ρmax := ρmax) hμ hρmax hv with ⟨b, hb⟩
  exact limsup_le_of_eventually_le_lb hB hb

/-! ## Shifted rescaling factor -/

/-- `m³/G_{m+1}³ → (ℓ+R)^{-3}` (for `ℓ > 0`). -/
lemma tendsto_grid_cube_shift_inv {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ 3 / gridSide (m + 1) ℓ R ^ 3) atTop
      (𝓝 ((ℓ + R) ^ 3)⁻¹) := by
  have hℓdiv : Tendsto (fun m : ℕ => ℓ / (m : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ℓ
  have hs : Tendsto (fun m : ℕ => (ℓ + R) + ℓ / (m : ℝ)) atTop (𝓝 (ℓ + R)) := by
    simpa using (tendsto_const_nhds.add hℓdiv)
  have hsc : Tendsto (fun m : ℕ => ((ℓ + R) + ℓ / (m : ℝ)) ^ 3) atTop (𝓝 ((ℓ + R) ^ 3)) := by
    simpa using hs.pow 3
  have hne : (ℓ + R) ^ 3 ≠ 0 := pow_ne_zero 3 (by linarith : ℓ + R ≠ 0)
  have hinv : Tendsto (fun m : ℕ => (((ℓ + R) + ℓ / (m : ℝ)) ^ 3)⁻¹) atTop
      (𝓝 (((ℓ + R) ^ 3)⁻¹)) := hsc.inv₀ hne
  apply hinv.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) hm))
  have hG : gridSide (m + 1) ℓ R ≠ 0 := ne_of_gt (gridSide_pos (m := m + 1) (by omega) hℓ hR)
  have hsm : (ℓ + R) + ℓ / (m : ℝ) = gridSide (m + 1) ℓ R / (m : ℝ) := by
    unfold gridSide
    push_cast
    field_simp [hmne]
    ring
  rw [hsm]
  rw [div_pow]
  field_simp [hmne, hG]

/-! ## From per-window bounds to eventual bounds -/

/-- An eventual-in-`m` upper bound on the window maxima transfers to an
eventual upper bound on the density itself. -/
lemma gcDensity_eventually_le_of_window {v : ℝ³ → ℝ} {μ ρmax ℓ R : ℝ} (hμ : 0 ≤ μ)
    (hρmax : 0 ≤ ρmax) (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) {w : ℕ → ℝ} {t : ℝ} {B0 : ℝ}
    (hwin : ∀ m : ℕ, 1 ≤ m →
      ∀ L : ℝ, gridSide m ℓ R ≤ L → L ≤ gridSide (m + 1) ℓ R →
        gcDensity v μ ρmax L ≤ w m * t)
    (hw : ∀ᶠ m : ℕ in atTop, w m * t ≤ B0) :
    ∀ᶠ L : ℝ in atTop, gcDensity v μ ρmax L ≤ B0 := by
  rcases eventually_atTop.mp hw with ⟨M₀, hM₀⟩
  refine eventually_atTop.mpr ⟨gridSide (M₀ + 1) ℓ R, ?_⟩
  intro L hLbig
  let m := gridWinIdx ℓ R L
  have hG1 : gridSide 1 ℓ R = ℓ := gridSide_one
  have hLge1 : ℓ ≤ L := by
    have hmono := gridSide_mono (m := 1) (n := M₀ + 1) hℓ.le hR (by omega)
    rw [gridSide_one] at hmono
    exact le_trans hmono hLbig
  have hmM : M₀ + 1 ≤ m := by
    have hmm := gridWinIdx_ge_of_gridSide (ℓ := ℓ) (R := R) (L := L) hℓ hR hLbig
    dsimp [m]
    exact hmm
  have hm1 : 1 ≤ m := by
    have hge := gridWinIdx_ge_one (ℓ := ℓ) (R := R) (L := L) hℓ hR hLge1
    dsimp [m]
    exact hge
  have hlo : gridSide m ℓ R ≤ L := gridWinIdx_lower hℓ hR hLge1
  have hhi : L ≤ gridSide (m + 1) ℓ R := gridWinIdx_upper hℓ hR hLge1
  have hb := hwin m hm1 L hlo hhi
  have hs := hM₀ m (by dsimp [m]; omega)
  exact le_trans hb hs

/-! ## The window comparison -/

/-- Grid-cell upper bound on the gc limsup: `gcLimsup ≤ gcBox(ℓ)/(ℓ+R)³`. -/
lemma gcLimsup_le_cell {v : ℝ³ → ℝ} {μ ρmax ℓ R : ℝ} (hμ : 0 ≤ μ) (hρmax : 0 ≤ ρmax)
    (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) :
    gcLimsup v μ ρmax ≤ gcBox v μ ρmax ℓ / (ℓ + R) ^ 3 := by
  let t : ℝ := gcBox v μ ρmax ℓ
  have hG1 : gridSide 1 ℓ R = ℓ := gridSide_one
  apply le_of_forall_pos_le_add
  intro ε hε
  by_cases ht : 0 ≤ t
  · -- sign-free branch: divide by G_m³ (window lower end)
    let w : ℕ → ℝ := fun m => (m : ℝ) ^ 3 / gridSide m ℓ R ^ 3
    have hwin : ∀ m : ℕ, 1 ≤ m →
        ∀ L : ℝ, gridSide m ℓ R ≤ L → L ≤ gridSide (m + 1) ℓ R →
          gcDensity v μ ρmax L ≤ w m * t := by
      intro m hm L hLlo hLhi
      have hGpos : 0 < gridSide m ℓ R := gridSide_pos hm hℓ hR
      have hLpos : 0 < L := lt_of_lt_of_le hGpos hLlo
      have hant := gcBox_antitone (μ := μ) (ρmax := ρmax) (L1 := gridSide m ℓ R) (L2 := L)
        hμ hρmax hGpos hLpos hLlo hv
      have hsub := gcBox_grid_subadd (μ := μ) (ρmax := ρmax) (ℓ := ℓ) (R := R)
        hμ hρmax hℓ hR hv hv1 hsupp hm
      have hle1 : gcBox v μ ρmax L ≤ gcBox v μ ρmax (gridSide m ℓ R) := hant
      have hle2 : gcBox v μ ρmax (gridSide m ℓ R) ≤ (m : ℝ) ^ 3 * t := by
        dsimp [t]
        exact hsub
      have hm3t : 0 ≤ (m : ℝ) ^ 3 * t := mul_nonneg (by positivity : 0 ≤ (m : ℝ) ^ 3) ht
      calc
        gcDensity v μ ρmax L = gcBox v μ ρmax L / L ^ 3 := rfl
        _ ≤ ((m : ℝ) ^ 3 * t) / L ^ 3 := by
          exact div_le_div_of_nonneg_right (le_trans hle1 hle2) (pow_nonneg hLpos.le 3)
        _ ≤ ((m : ℝ) ^ 3 * t) / gridSide m ℓ R ^ 3 := by
          have hpow : gridSide m ℓ R ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hGpos.le hLlo 3
          exact div_le_div_of_nonneg_left hm3t (pow_pos hGpos 3) hpow
        _ = w m * t := by
          dsimp [w]
          ring
    -- sequence bound: w_m·t → (ℓ+R)^{-3}·t = t/(ℓ+R)³
    have hlim := tendsto_grid_cube_inv hℓ hR
    have hlimt : Tendsto (fun m : ℕ => w m * t) atTop (𝓝 (t / (ℓ + R) ^ 3)) := by
      have hc := hlim.const_mul t
      -- hc : w m · t → ((ℓ+R)^3)⁻¹ · t
      convert hc using 1
      · ext m; ring
      · ring
    have hlimt' : Tendsto (fun m : ℕ => w m * t) atTop (𝓝 (t / (ℓ + R) ^ 3)) := hlimt
    have hmem : t / (ℓ + R) ^ 3 < t / (ℓ + R) ^ 3 + ε := by linarith
    have hevseq : ∀ᶠ m : ℕ in atTop, w m * t ≤ t / (ℓ + R) ^ 3 + ε :=
      (hlimt'.eventually (isOpen_Iio.mem_nhds hmem)).mono (fun m hm => le_of_lt hm)
    have hev := gcDensity_eventually_le_of_window (v := v) (μ := μ) (ρmax := ρmax)
      (ℓ := ℓ) (R := R) hμ hρmax hℓ hR hv hv1 hsupp
      (w := w) (t := t) (B0 := t / (ℓ + R) ^ 3 + ε) hwin hevseq
    exact gcLimsup_le_of_eventually_le (v := v) (μ := μ) (ρmax := ρmax) hμ hρmax hv hev
  · -- negative branch: divide by G_{m+1}³ (window upper end)
    let w : ℕ → ℝ := fun m => (m : ℝ) ^ 3 / gridSide (m + 1) ℓ R ^ 3
    have hwin : ∀ m : ℕ, 1 ≤ m →
        ∀ L : ℝ, gridSide m ℓ R ≤ L → L ≤ gridSide (m + 1) ℓ R →
          gcDensity v μ ρmax L ≤ w m * t := by
      intro m hm L hLlo hLhi
      have hGpos : 0 < gridSide m ℓ R := gridSide_pos hm hℓ hR
      have hG1pos : 0 < gridSide (m + 1) ℓ R := gridSide_pos (m := m + 1) (by omega) hℓ hR
      have hLpos : 0 < L := lt_of_lt_of_le hGpos hLlo
      have hant := gcBox_antitone (μ := μ) (ρmax := ρmax) (L1 := gridSide m ℓ R) (L2 := L)
        hμ hρmax hGpos hLpos hLlo hv
      have hsub := gcBox_grid_subadd (μ := μ) (ρmax := ρmax) (ℓ := ℓ) (R := R)
        hμ hρmax hℓ hR hv hv1 hsupp hm
      have hle2 : gcBox v μ ρmax (gridSide m ℓ R) ≤ (m : ℝ) ^ 3 * t := by
        dsimp [t]
        exact hsub
      have hm3t : (m : ℝ) ^ 3 * t < 0 := mul_neg_of_pos_of_neg (by positivity : 0 < (m : ℝ) ^ 3)
        (lt_of_not_ge ht)
      calc
        gcDensity v μ ρmax L = gcBox v μ ρmax L / L ^ 3 := rfl
        _ ≤ ((m : ℝ) ^ 3 * t) / L ^ 3 := by
          exact div_le_div_of_nonneg_right (le_trans hant hle2) (pow_nonneg hLpos.le 3)
        _ ≤ ((m : ℝ) ^ 3 * t) / gridSide (m + 1) ℓ R ^ 3 := by
          have hpow : L ^ 3 ≤ gridSide (m + 1) ℓ R ^ 3 := pow_le_pow_left₀ hLpos.le hLhi 3
          have hpos1 : 0 < L ^ 3 := pow_pos hLpos 3
          have hpos2 : 0 < gridSide (m + 1) ℓ R ^ 3 := pow_pos hG1pos 3
          rw [div_le_div_iff₀ hpos1 hpos2]
          exact mul_le_mul_of_nonpos_left hpow hm3t.le
        _ = w m * t := by
          dsimp [w]
          ring
    have hlim := tendsto_grid_cube_shift_inv hℓ hR
    have hlimt : Tendsto (fun m : ℕ => w m * t) atTop (𝓝 (t / (ℓ + R) ^ 3)) := by
      have hc := hlim.const_mul t
      convert hc using 1
      · ext m; ring
      · ring
    have hmem : t / (ℓ + R) ^ 3 < t / (ℓ + R) ^ 3 + ε := by linarith
    have hevseq : ∀ᶠ m : ℕ in atTop, w m * t ≤ t / (ℓ + R) ^ 3 + ε :=
      (hlimt.eventually (isOpen_Iio.mem_nhds hmem)).mono (fun m hm => le_of_lt hm)
    have hev := gcDensity_eventually_le_of_window (v := v) (μ := μ) (ρmax := ρmax)
      (ℓ := ℓ) (R := R) hμ hρmax hℓ hR hv hv1 hsupp
      (w := w) (t := t) (B0 := t / (ℓ + R) ^ 3 + ε) hwin hevseq
    exact gcLimsup_le_of_eventually_le (v := v) (μ := μ) (ρmax := ρmax) hμ hρmax hv hev

/-! ## The pressure limit (`gcLimsup ≤ gcLiminf`) -/

/-- The corridor factor is `≤ 1`: `(ℓ/(ℓ+R))³ ≤ 1` for `0 < ℓ`, `0 ≤ R`. -/
lemma corridor_cube_le (ℓ R : ℝ) (hℓ : 0 < ℓ) (hR : 0 ≤ R) :
    (ℓ / (ℓ + R)) ^ 3 ≤ 1 := by
  have hpos : 0 < ℓ + R := by linarith
  have hle1 : ℓ / (ℓ + R) ≤ 1 := by
    rw [div_le_one₀ hpos]
    linarith
  exact pow_le_one₀ (by positivity) hle1

/-- The corridor gap: `1 − (ℓ/(ℓ+R))³ ≤ 4R/(ℓ+R)`. -/
lemma one_sub_corridor_cube_le (ℓ R : ℝ) (hℓ : 0 < ℓ) (hR : 0 ≤ R) :
    1 - (ℓ / (ℓ + R)) ^ 3 ≤ 4 * R / (ℓ + R) := by
  have hne : ℓ + R ≠ 0 := by linarith
  rw [div_pow]
  field_simp [hne]
  have hdiff : 4 * R * (ℓ + R) ^ 2 - ((ℓ + R) ^ 3 - ℓ ^ 3) = R * (ℓ ^ 2 + 5 * R * ℓ + 3 * R ^ 2) := by ring
  have hnonneg : 0 ≤ 4 * R * (ℓ + R) ^ 2 - ((ℓ + R) ^ 3 - ℓ ^ 3) := by
    rw [hdiff]
    have h1 : 0 ≤ R * ℓ ^ 2 := mul_nonneg hR (sq_nonneg ℓ)
    have h2 : 0 ≤ R * (R * ℓ) := mul_nonneg hR (mul_nonneg hR hℓ.le)
    have h3 : 0 ≤ R * R ^ 2 := mul_nonneg hR (sq_nonneg R)
    nlinarith
  nlinarith

/-- Eventually the corridor cost `(μρmax)·(1 − c(ℓ))` is below any positive `η`. -/
lemma corridor_cost_eventually_le {μ ρmax R : ℝ} (hμ : 0 ≤ μ) (hρmax : 0 ≤ ρmax)
    (hR : 0 ≤ R) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ℓ : ℝ in atTop, (μ * ρmax) * (1 - (ℓ / (ℓ + R)) ^ 3) ≤ η := by
  let M : ℝ := μ * ρmax
  have hM0 : 0 ≤ M := by dsimp [M]; exact mul_nonneg hμ hρmax
  by_cases hM : M = 0
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with ℓ hℓ1
    have hℓpos : 0 < ℓ := by linarith
    have hc : 0 ≤ 1 - (ℓ / (ℓ + R)) ^ 3 := sub_nonneg.mpr (corridor_cube_le ℓ R hℓpos hR)
    have hμρ : μ * ρmax = 0 := by simpa [M] using hM
    rw [hμρ]
    nlinarith
  · have hMpos : 0 < M := lt_of_le_of_ne hM0 (Ne.symm hM)
    let thresh : ℝ := 4 * R * M / η
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop thresh] with ℓ hℓ1 hth
    have hℓpos : 0 < ℓ := by linarith
    have h1c := one_sub_corridor_cube_le ℓ R hℓpos hR
    have hmul : M * (1 - (ℓ / (ℓ + R)) ^ 3) ≤ M * (4 * R / (ℓ + R)) := by
      dsimp [M]
      exact mul_le_mul_of_nonneg_left h1c hM0
    have hden : 0 < ℓ + R := by linarith
    have hle : M * (4 * R / (ℓ + R)) ≤ η := by
      have hth' : 4 * R * M / η ≤ ℓ + R := by
        dsimp [thresh] at hth
        exact le_trans hth (by linarith)
      have hstep : 4 * R * M ≤ (ℓ + R) * η := (div_le_iff₀ hη).mp hth'
      have h4 : 4 * R * M / (ℓ + R) ≤ η := by
        rw [div_le_iff₀ hden]
        simpa [mul_comm] using hstep
      have hEq : M * (4 * R / (ℓ + R)) = 4 * R * M / (ℓ + R) := by ring
      rwa [hEq]
    exact le_trans hmul hle

/-- The liminf is at least any eventual lower bound of the density. -/
lemma gcLiminf_ge_of_eventually_ge {v : ℝ³ → ℝ} {μ ρmax : ℝ} (hμ : 0 ≤ μ) (hv : 0 ≤ v)
    (hv1 : MemLp v 1) (hρmax : 0 ≤ ρmax) {a : ℝ}
    (h : ∀ᶠ L : ℝ in atTop, a ≤ gcDensity v μ ρmax L) : a ≤ gcLiminf v μ ρmax := by
  unfold gcLiminf
  exact liminf_ge_of_eventually_ge h (gcDensity_eventually_bdd_above (v := v) (μ := μ)
    (ρmax := ρmax) hμ hv hv1 hρmax)

/-- The gc liminf is at least the limsup (corridor absorption). -/
lemma gcLimsup_le_gcLiminf {v : ℝ³ → ℝ} {μ ρmax R : ℝ} (hμ : 0 ≤ μ) (hρmax : 0 ≤ ρmax)
    (hR : 0 ≤ R) (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) :
    gcLimsup v μ ρmax ≤ gcLiminf v μ ρmax := by
  apply le_of_forall_pos_le_add
  intro η hη
  let ε2 : ℝ := η / 2
  have hε2 : 0 < ε2 := by dsimp [ε2]; linarith
  have hcorr := corridor_cost_eventually_le (μ := μ) (ρmax := ρmax) (R := R) hμ hρmax hR hε2
  have hevG : ∀ᶠ ℓ : ℝ in atTop,
      gcLimsup v μ ρmax ≤ gcDensity v μ ρmax ℓ + ε2 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), hcorr] with ℓ hℓ1 hMbd
    have hℓpos : 0 < ℓ := by linarith
    have hcell := gcLimsup_le_cell (v := v) (μ := μ) (ρmax := ρmax) (ℓ := ℓ) (R := R)
      hμ hρmax hℓpos hR hv hv1 hsupp
    have hEq : gcBox v μ ρmax ℓ / (ℓ + R) ^ 3 =
        gcDensity v μ ρmax ℓ * (ℓ / (ℓ + R)) ^ 3 := by
      dsimp [gcDensity]
      have hne : (ℓ + R) ≠ 0 := by linarith
      field_simp [pow_ne_zero 3 hne, pow_ne_zero 3 (ne_of_gt hℓpos)]
    have hb : gcDensity v μ ρmax ℓ * (ℓ / (ℓ + R)) ^ 3 ≤
        gcDensity v μ ρmax ℓ + (μ * ρmax) * (1 - (ℓ / (ℓ + R)) ^ 3) := by
      have hg : -(μ * ρmax) ≤ gcDensity v μ ρmax ℓ :=
        gcBox_density_ge (μ := μ) (ρmax := ρmax) (L := ℓ) hμ hρmax hℓpos hv
      have hc1 : (ℓ / (ℓ + R)) ^ 3 ≤ 1 := corridor_cube_le ℓ R hℓpos hR
      have h1c : 0 ≤ 1 - (ℓ / (ℓ + R)) ^ 3 := sub_nonneg.mpr hc1
      have hneg : -gcDensity v μ ρmax ℓ ≤ μ * ρmax := by nlinarith [hg]
      have hmul := mul_le_mul_of_nonneg_right hneg h1c
      -- (−g)(1−c) ≤ M(1−c); and (−g)(1−c) = gc − g
      have hmain : gcDensity v μ ρmax ℓ * (ℓ / (ℓ + R)) ^ 3 -
          gcDensity v μ ρmax ℓ ≤ (μ * ρmax) * (1 - (ℓ / (ℓ + R)) ^ 3) := by
        have hrew : gcDensity v μ ρmax ℓ * (ℓ / (ℓ + R)) ^ 3 - gcDensity v μ ρmax ℓ =
            -(gcDensity v μ ρmax ℓ) * (1 - (ℓ / (ℓ + R)) ^ 3) := by ring
        rwa [hrew]
      nlinarith
    calc
      gcLimsup v μ ρmax ≤ gcBox v μ ρmax ℓ / (ℓ + R) ^ 3 := hcell
      _ = gcDensity v μ ρmax ℓ * (ℓ / (ℓ + R)) ^ 3 := hEq
      _ ≤ gcDensity v μ ρmax ℓ + (μ * ρmax) * (1 - (ℓ / (ℓ + R)) ^ 3) := hb
      _ ≤ gcDensity v μ ρmax ℓ + ε2 := by
        nlinarith [hMbd]
  have hev : ∀ᶠ ℓ : ℝ in atTop,
      gcLimsup v μ ρmax - ε2 ≤ gcDensity v μ ρmax ℓ := by
    filter_upwards [hevG] with ℓ h
    linarith
  have hge := gcLiminf_ge_of_eventually_ge (v := v) (μ := μ) (ρmax := ρmax) hμ hv hv1 hρmax
    (a := gcLimsup v μ ρmax - ε2) hev
  have : gcLimsup v μ ρmax ≤ gcLiminf v μ ρmax + η := by
    dsimp [ε2] at hge
    nlinarith
  simpa using this

/-- `liminf ≤ limsup` for the gc density (two-sided bounded). -/
lemma gcLiminf_le_gcLimsup {v : ℝ³ → ℝ} {μ ρmax : ℝ} (hμ : 0 ≤ μ) (hρmax : 0 ≤ ρmax)
    (hv : 0 ≤ v) (hv1 : MemLp v 1) : gcLiminf v μ ρmax ≤ gcLimsup v μ ρmax := by
  unfold gcLiminf gcLimsup
  rw [liminf_eq, limsup_eq]
  apply le_csInf
  · rcases gcDensity_eventually_bdd_above (v := v) (μ := μ) (ρmax := ρmax) hμ hv hv1 hρmax
      with ⟨B, hB⟩
    exact ⟨B, hB⟩
  · intro a ha
    rcases gcDensity_eventually_bdd_below (v := v) (μ := μ) (ρmax := ρmax) hμ hρmax hv
      with ⟨b, hb⟩
    apply csSup_le
    · exact ⟨b, hb⟩
    · intro c hc
      exact atTop_le_of_eventually hc ha

/-- The grand-canonical pressure limit exists at each `μ` (and equals the
liminf of the density). -/
lemma gcDensity_tendsto {v : ℝ³ → ℝ} {μ ρmax R : ℝ} (hμ : 0 ≤ μ) (hρmax : 0 ≤ ρmax)
    (hR : 0 ≤ R) (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) :
    Tendsto (fun L : ℝ => gcDensity v μ ρmax L) atTop (𝓝 (gcLiminf v μ ρmax)) := by
  have hlo : gcLimsup v μ ρmax ≤ gcLiminf v μ ρmax :=
    gcLimsup_le_gcLiminf (v := v) (μ := μ) (ρmax := ρmax) (R := R) hμ hρmax hR hv hv1 hsupp
  have hle : gcLiminf v μ ρmax ≤ gcLimsup v μ ρmax :=
    gcLiminf_le_gcLimsup (v := v) (μ := μ) (ρmax := ρmax) hμ hρmax hv hv1
  have heq : gcLiminf v μ ρmax = gcLimsup v μ ρmax := le_antisymm hle hlo
  have hinf : gcLiminf v μ ρmax ≤ Filter.liminf (fun L : ℝ => gcDensity v μ ρmax L) atTop := le_rfl
  have hsup : Filter.limsup (fun L : ℝ => gcDensity v μ ρmax L) atTop ≤ gcLiminf v μ ρmax := by
    exact heq.symm.le
  rcases gcDensity_eventually_bdd_above (v := v) (μ := μ) (ρmax := ρmax) hμ hv hv1 hρmax
    with ⟨B, hB⟩
  rcases gcDensity_eventually_bdd_below (v := v) (μ := μ) (ρmax := ρmax) hμ hρmax hv
    with ⟨b, hb⟩
  have hBdd1 : atTop.IsBoundedUnder (· ≤ ·) (fun L : ℝ => gcDensity v μ ρmax L) := by
    refine ⟨B, ?_⟩
    simpa [Filter.eventually_map] using hB
  have hBdd2 : atTop.IsBoundedUnder (· ≥ ·) (fun L : ℝ => gcDensity v μ ρmax L) := by
    refine ⟨b, ?_⟩
    simpa [Filter.eventually_map] using hb
  exact tendsto_of_le_liminf_of_limsup_le hinf hsup hBdd1 hBdd2





/-! ## Concavity of `gcBox` in the chemical potential -/

/-- For a fixed box, `gcBox(μ,ρmax,L)` is concave in `μ ≥ 0`: an infimum of
affine functions `E(N,L) − μN`. -/
lemma gcBox_concave_ineq {v : ℝ³ → ℝ} {ρmax L μ₁ μ₂ t : ℝ} (hv : 0 ≤ v)
    (hρmax : 0 ≤ ρmax) (hL : 0 < L) (hμ₁ : 0 ≤ μ₁) (hμ₂ : 0 ≤ μ₂)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * gcBox v μ₁ ρmax L + (1 - t) * gcBox v μ₂ ρmax L ≤
      gcBox v (t * μ₁ + (1 - t) * μ₂) ρmax L := by
  let μ : ℝ := t * μ₁ + (1 - t) * μ₂
  apply le_gcBox_of_forall (μ := μ) hρmax hL.le
  intro y hy
  rcases hy with ⟨N, hNad, rfl⟩
  have h1 := gcBox_le_value (μ := μ₁) (ρmax := ρmax) (L := L) hμ₁ hρmax hL hv hNad
  have h2 := gcBox_le_value (μ := μ₂) (ρmax := ρmax) (L := L) hμ₂ hρmax hL hv hNad
  have h3 : t * gcBox v μ₁ ρmax L ≤ t * (boxEnergy N L v - μ₁ * (N : ℝ)) :=
    mul_le_mul_of_nonneg_left h1 ht0
  have h4 : (1 - t) * gcBox v μ₂ ρmax L ≤ (1 - t) * (boxEnergy N L v - μ₂ * (N : ℝ)) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have hsum : t * gcBox v μ₁ ρmax L + (1 - t) * gcBox v μ₂ ρmax L ≤
      t * (boxEnergy N L v - μ₁ * (N : ℝ)) + (1 - t) * (boxEnergy N L v - μ₂ * (N : ℝ)) :=
    add_le_add h3 h4
  have hrhs : t * (boxEnergy N L v - μ₁ * (N : ℝ)) + (1 - t) * (boxEnergy N L v - μ₂ * (N : ℝ))
      = boxEnergy N L v - μ * (N : ℝ) := by
    dsimp [μ]
    ring
  exact hsum.trans (le_of_eq hrhs)

/-- `gcBox(·,ρmax,L)` is concave on `[0,∞)` in the chemical potential. -/
lemma gcBox_concaveOn {v : ℝ³ → ℝ} {ρmax L : ℝ} (hv : 0 ≤ v) (hρmax : 0 ≤ ρmax)
    (hL : 0 < L) : ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun μ : ℝ => gcBox v μ ρmax L) := by
  refine ⟨convex_Ici (0 : ℝ), ?_⟩
  intro x hx y hy a b ha hb hab
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have ha1 : a ≤ 1 := by linarith
  have hb' : b = 1 - a := by linarith
  rw [hb']
  simpa [smul_eq_mul] using
    gcBox_concave_ineq (v := v) (ρmax := ρmax) (L := L) (μ₁ := x) (μ₂ := y) (t := a)
      hv hρmax hL hx0 hy0 ha ha1

/-- For a fixed box, the gc density is concave in `μ ≥ 0` (same inequality,
divided by `L³`). -/
lemma gcDensity_concave_ineq {v : ℝ³ → ℝ} {ρmax L t μ₁ μ₂ : ℝ} (hv : 0 ≤ v)
    (hρmax : 0 ≤ ρmax) (hL : 0 < L) (hμ₁ : 0 ≤ μ₁) (hμ₂ : 0 ≤ μ₂)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * gcDensity v μ₁ ρmax L + (1 - t) * gcDensity v μ₂ ρmax L ≤
      gcDensity v (t * μ₁ + (1 - t) * μ₂) ρmax L := by
  have h1 := gcBox_concave_ineq (v := v) (ρmax := ρmax) (L := L) (μ₁ := μ₁) (μ₂ := μ₂) (t := t)
    hv hρmax hL hμ₁ hμ₂ ht0 ht1
  dsimp [gcDensity]
  have hL3 : L ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hL)
  field_simp [hL3]
  exact h1


/-! ## The pressure is concave in the chemical potential -/

/-- The grand-canonical pressure at chemical potential `μ`: the limit of the
gc density (exists by `gcDensity_tendsto`). -/
noncomputable def gcPressure (v : ℝ³ → ℝ) (ρmax : ℝ) (μ : ℝ) : ℝ :=
  gcLiminf v μ ρmax

/-- The gc density converges to the pressure at every `0 ≤ μ`. -/
lemma gcDensity_tendsto_pressure {v : ℝ³ → ℝ} {μ ρmax R : ℝ} (hμ : 0 ≤ μ)
    (hρmax : 0 ≤ ρmax) (hR : 0 ≤ R) (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) :
    Tendsto (fun L : ℝ => gcDensity v μ ρmax L) atTop (𝓝 (gcPressure v ρmax μ)) := by
  unfold gcPressure
  exact gcDensity_tendsto (v := v) (μ := μ) (ρmax := ρmax) (R := R) hμ hρmax hR hv hv1 hsupp

/-- The pressure is concave in `μ ≥ 0` (a pointwise limit of the concave
finite-box densities). -/
lemma gcPressure_concave_ineq {v : ℝ³ → ℝ} {ρmax μ₁ μ₂ t : ℝ} (hv : 0 ≤ v)
    (hv1 : MemLp v 1) (hρmax : 0 ≤ ρmax) {R : ℝ} (hR : 0 ≤ R)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) (hμ₁ : 0 ≤ μ₁) (hμ₂ : 0 ≤ μ₂)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * gcPressure v ρmax μ₁ + (1 - t) * gcPressure v ρmax μ₂ ≤
      gcPressure v ρmax (t * μ₁ + (1 - t) * μ₂) := by
  let μ : ℝ := t * μ₁ + (1 - t) * μ₂
  let q : ℝ := t * gcPressure v ρmax μ₁ + (1 - t) * gcPressure v ρmax μ₂
  have hμ0 : 0 ≤ μ := by
    dsimp [μ]
    nlinarith [mul_nonneg ht0 hμ₁, mul_nonneg (by linarith) hμ₂]
  have ha : Tendsto (fun L : ℝ => t * gcDensity v μ₁ ρmax L + (1 - t) * gcDensity v μ₂ ρmax L)
      atTop (𝓝 q) := by
    have h1 := gcDensity_tendsto_pressure (v := v) (μ := μ₁) (ρmax := ρmax) (R := R)
      hμ₁ hρmax hR hv hv1 hsupp
    have h2 := gcDensity_tendsto_pressure (v := v) (μ := μ₂) (ρmax := ρmax) (R := R)
      hμ₂ hρmax hR hv hv1 hsupp
    have h1' : Tendsto (fun L : ℝ => t * gcDensity v μ₁ ρmax L) atTop
        (𝓝 (t * gcPressure v ρmax μ₁)) := h1.const_mul t
    have h2' : Tendsto (fun L : ℝ => (1 - t) * gcDensity v μ₂ ρmax L) atTop
        (𝓝 ((1 - t) * gcPressure v ρmax μ₂)) := h2.const_mul (1 - t)
    dsimp [q]
    exact h1'.add h2'
  have hb : Tendsto (fun L : ℝ => gcDensity v μ ρmax L) atTop
      (𝓝 (gcPressure v ρmax μ)) :=
    gcDensity_tendsto_pressure (v := v) (μ := μ) (ρmax := ρmax) (R := R)
      hμ0 hρmax hR hv hv1 hsupp
  have hle : ∀ᶠ L : ℝ in atTop,
      t * gcDensity v μ₁ ρmax L + (1 - t) * gcDensity v μ₂ ρmax L ≤ gcDensity v μ ρmax L := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL1
    dsimp [μ]
    exact gcDensity_concave_ineq (v := v) (ρmax := ρmax) (L := L) (t := t) (μ₁ := μ₁) (μ₂ := μ₂)
      hv hρmax (by linarith : 0 < L) hμ₁ hμ₂ ht0 ht1
  have hsub : Tendsto (fun L : ℝ =>
      gcDensity v μ ρmax L - (t * gcDensity v μ₁ ρmax L + (1 - t) * gcDensity v μ₂ ρmax L))
      atTop (𝓝 (gcPressure v ρmax μ - q)) := hb.sub ha
  have hnonneg : ∀ᶠ L : ℝ in atTop,
      0 ≤ gcDensity v μ ρmax L - (t * gcDensity v μ₁ ρmax L + (1 - t) * gcDensity v μ₂ ρmax L) := by
    filter_upwards [hle] with L h
    exact sub_nonneg.mpr h
  have h0 : 0 ≤ gcPressure v ρmax μ - q := ge_of_tendsto hsub hnonneg
  dsimp [q] at h0
  nlinarith

/-- The pressure is concave on `[0,∞)` in the chemical potential. -/
lemma gcPressure_concaveOn {v : ℝ³ → ℝ} {ρmax : ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hρmax : 0 ≤ ρmax) {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) :
    ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun μ : ℝ => gcPressure v ρmax μ) := by
  refine ⟨convex_Ici (0 : ℝ), ?_⟩
  intro x hx y hy a b ha hb hab
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have ha1 : a ≤ 1 := by linarith
  have hb' : b = 1 - a := by linarith
  rw [hb']
  simpa [smul_eq_mul] using
    gcPressure_concave_ineq (v := v) (ρmax := ρmax) (μ₁ := x) (μ₂ := y) (t := a)
      hv hv1 hρmax hR hsupp hx0 hy0 ha ha1


/-! ## The canonical is at least the grand-canonical value -/

/-- Every admissible `N`-particle box energy is at least the truncated
grand-canonical value plus `μN`. -/
lemma boxEnergy_ge_gcBox_add {v : ℝ³ → ℝ} {μ ρmax L : ℝ} (hμ : 0 ≤ μ) (hρmax : 0 ≤ ρmax)
    (hL : 0 < L) (hv : 0 ≤ v) {N : ℕ} (hNad : gcAdmissible ρmax L N) :
    gcBox v μ ρmax L + μ * (N : ℝ) ≤ boxEnergy N L v := by
  have h := gcBox_le_value (μ := μ) (ρmax := ρmax) (L := L) hμ hρmax hL hv hNad
  nlinarith

/-- `μ/L³ → 0` as `L → ∞` (for `0 ≤ μ`). -/
lemma tendsto_const_div_cube_nhds_zero {μ : ℝ} (hμ : 0 ≤ μ) :
    Tendsto (fun L : ℝ => μ / L ^ 3) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  let th : ℝ := max 1 (μ / δ + 1)
  have hth1 : 1 ≤ th := le_max_left _ _
  have hth2 : μ / δ + 1 ≤ th := le_max_right _ _
  filter_upwards [eventually_ge_atTop th] with L hL
  have hLge1 : 1 ≤ L := le_trans hth1 hL
  have hLpos : 0 < L := by linarith
  have hLgd : μ / δ + 1 ≤ L := le_trans hth2 hL
  have hμδ : μ < δ * L := by
    have hmm' : δ * (μ / δ + 1) ≤ δ * L := mul_le_mul_of_nonneg_left hLgd hδ.le
    have hrew : δ * (μ / δ + 1) = μ + δ := by
      field_simp [ne_of_gt hδ]
    have hmm : μ + δ ≤ δ * L := by
      rwa [hrew] at hmm'
    nlinarith
  have hμδ3 : μ < δ * L ^ 3 := by
    have hL2 : 1 ≤ L ^ 2 := by
      have hmm := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1) hLge1
      simpa [pow_two] using hmm
    have hLe : L ≤ L * L ^ 2 := by
      simpa using mul_le_mul_of_nonneg_left hL2 hLpos.le
    have hpow3 : L * L ^ 2 = L ^ 3 := by ring
    have hδL : δ * L ≤ δ * L ^ 3 := by
      have hL3 : L ≤ L ^ 3 := by
        calc
          L ≤ L * L ^ 2 := hLe
          _ = L ^ 3 := hpow3
      exact mul_le_mul_of_nonneg_left hL3 hδ.le
    nlinarith
  have hL3 : 0 < L ^ 3 := pow_pos hLpos 3
  have hlt : μ / L ^ 3 < δ := by
    rw [div_lt_iff₀ hL3]
    nlinarith
  have hnon : 0 ≤ μ / L ^ 3 := div_nonneg hμ (pow_nonneg hLpos.le 3)
  rw [Real.dist_eq]
  rw [sub_zero, abs_of_nonneg hnon]
  exact hlt


/-- Along the diagonal at density `ρ ≤ ρmax`, the canonical density is at least
the gc density plus `μρ`, up to the boundary term `μ/L³`. -/
lemma diag_ge_gc_affine_bound {v : ℝ³ → ℝ} {ρ ρmax μ L : ℝ} (hv : 0 ≤ v)
    (hρmax : 0 ≤ ρmax) (hL : 0 < L) (hρ0 : 0 ≤ ρ) (hρmax_ge : ρ ≤ ρmax) (hμ : 0 ≤ μ) :
    gcDensity v μ ρmax L + μ * ρ - μ / L ^ 3 ≤ diag v ρ L := by
  let N : ℕ := Nat.floor (ρ * L ^ 3)
  have hx0 : 0 ≤ ρ * L ^ 3 := mul_nonneg hρ0 (pow_nonneg hL.le 3)
  have hNad : gcAdmissible ρmax L N := by
    dsimp [gcAdmissible, N]
    have hfl : (Nat.floor (ρ * L ^ 3) : ℝ) ≤ ρ * L ^ 3 := Nat.floor_le hx0
    have hle : ρ * L ^ 3 ≤ ρmax * L ^ 3 := mul_le_mul_of_nonneg_right hρmax_ge (pow_nonneg hL.le 3)
    exact le_trans hfl hle
  have hge := boxEnergy_ge_gcBox_add (μ := μ) (ρmax := ρmax) (L := L) hμ hρmax hL hv hNad
  have hd := div_le_div_of_nonneg_right hge (pow_nonneg hL.le 3)
  have hL3 : L ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hL)
  have hsplit : gcDensity v μ ρmax L + μ * (N : ℝ) / L ^ 3 ≤ diag v ρ L := by
    have hEq1 : gcBox v μ ρmax L / L ^ 3 + μ * (N : ℝ) / L ^ 3 =
        (gcBox v μ ρmax L + μ * (N : ℝ)) / L ^ 3 := by ring
    change gcBox v μ ρmax L / L ^ 3 + μ * (N : ℝ) / L ^ 3 ≤
      boxEnergy (Nat.floor (ρ * L ^ 3)) L v / L ^ 3
    rw [hEq1]
    exact hd
  have hbig : μ * ρ - μ / L ^ 3 ≤ μ * (N : ℝ) / L ^ 3 := by
    have hNgt : ρ * L ^ 3 - 1 < (N : ℝ) := by
      have hf := Nat.lt_floor_add_one (ρ * L ^ 3)
      change ρ * L ^ 3 - 1 < (Nat.floor (ρ * L ^ 3) : ℝ)
      nlinarith
    have hμN : μ * (ρ * L ^ 3 - 1) ≤ μ * (N : ℝ) := mul_le_mul_of_nonneg_left (le_of_lt hNgt) hμ
    have hdv := div_le_div_of_nonneg_right hμN (pow_nonneg hL.le 3)
    have hEq2 : μ * (ρ * L ^ 3 - 1) / L ^ 3 = μ * ρ - μ / L ^ 3 := by
      field_simp [hL3]
    rwa [hEq2] at hdv
  calc
    gcDensity v μ ρmax L + μ * ρ - μ / L ^ 3 = gcDensity v μ ρmax L + (μ * ρ - μ / L ^ 3) := by ring
    _ ≤ gcDensity v μ ρmax L + μ * (N : ℝ) / L ^ 3 := by nlinarith [hbig]
    _ ≤ diag v ρ L := hsplit

/-- Canonical liminf is at least the affine grand-canonical line: for
`0 ≤ ρ ≤ ρmax` and `0 ≤ μ`, `x̲(ρ) ≥ p(μ) + μρ`. -/
lemma diagLiminf_ge_gc_affine {v : ℝ³ → ℝ} {ρ ρmax μ : ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hρmax : 0 ≤ ρmax) (hρ0 : 0 ≤ ρ) (hρmax_ge : ρ ≤ ρmax) (hμ : 0 ≤ μ)
    {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) :
    gcPressure v ρmax μ + μ * ρ ≤ diagLiminf v ρ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hd := gcDensity_tendsto_pressure (v := v) (μ := μ) (ρmax := ρmax) (R := R)
    hμ hρmax hR hv hv1 hsupp
  have hzero := tendsto_const_div_cube_nhds_zero hμ
  have hconst : Tendsto (fun L : ℝ => μ * ρ) atTop (𝓝 (μ * ρ)) := tendsto_const_nhds
  have hc : Tendsto (fun L : ℝ => gcDensity v μ ρmax L + μ * ρ - μ / L ^ 3) atTop
      (𝓝 (gcPressure v ρmax μ + μ * ρ)) := by
    simpa using (hd.add hconst).sub hzero
  have hge : ∀ᶠ L : ℝ in atTop,
      gcPressure v ρmax μ + μ * ρ - ε ≤ gcDensity v μ ρmax L + μ * ρ - μ / L ^ 3 := by
    have hmem : gcPressure v ρmax μ + μ * ρ - ε < gcPressure v ρmax μ + μ * ρ := by nlinarith
    have hset : {y : ℝ | gcPressure v ρmax μ + μ * ρ - ε < y} ∈
        𝓝 (gcPressure v ρmax μ + μ * ρ) := isOpen_Ioi.mem_nhds hmem
    exact (hc.eventually hset).mono (fun L h => le_of_lt h)
  have hpt : ∀ᶠ L : ℝ in atTop, gcDensity v μ ρmax L + μ * ρ - μ / L ^ 3 ≤ diag v ρ L := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL1
    exact diag_ge_gc_affine_bound (v := v) (ρ := ρ) (ρmax := ρmax) (μ := μ) (L := L)
      hv hρmax (by linarith : 0 < L) hρ0 hρmax_ge hμ
  have hev : ∀ᶠ L : ℝ in atTop, gcPressure v ρmax μ + μ * ρ - ε ≤ diag v ρ L := by
    filter_upwards [hge, hpt] with L hgeL hptL
    exact le_trans hgeL hptL
  have hlim := liminf_ge_of_eventually_ge (u := fun L : ℝ => diag v ρ L)
    (a := gcPressure v ρmax μ + μ * ρ - ε) hev (diag_eventually_bdd_above (v := v) (ρ := ρ) hv1 hρ0)
  have hlin : gcPressure v ρmax μ + μ * ρ - ε ≤ diagLiminf v ρ := by
    simpa [diagLiminf] using hlim
  have hfin : gcPressure v ρmax μ + μ * ρ ≤ diagLiminf v ρ + ε := by nlinarith [hlin]
  exact hfin


/-! ## The pressure decays linearly at large chemical potential -/

/-- Pressure upper bound from the trial box: for all `0 ≤ μ`,
`p(μ) ≤ C(ρmax²‖v‖₁+ρmax) − μρmax` with a uniform `C` (the truncation caps
the particle number, so the pressure cannot beat the linear decay `−μρmax`). -/
lemma gcPressure_le_density_bound {v : ℝ³ → ℝ} {ρmax : ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hρmax : 0 ≤ ρmax) {R : ℝ} (hR : 0 ≤ R)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) :
    ∃ C : ℝ, 0 < C ∧ ∀ {μ : ℝ}, 0 ≤ μ →
      gcPressure v ρmax μ ≤ C * (ρmax ^ 2 * vL1 v + ρmax) - μ * ρmax := by
  rcases boxDensity_upper_bound hv1 with ⟨C, hCpos, hbd⟩
  refine ⟨C, hCpos, ?_⟩
  intro μ hμ
  -- per-box: gcDensity(μ,L) ≤ C(..) − μρmax + μ/L³ for L ≥ 1
  have hpt : ∀ᶠ L : ℝ in atTop,
      gcDensity v μ ρmax L ≤ C * (ρmax ^ 2 * vL1 v + ρmax) - μ * ρmax + μ / L ^ 3 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL1
    have hL : 0 < L := by linarith
    let N : ℕ := Nat.floor (ρmax * L ^ 3)
    have hx0 : 0 ≤ ρmax * L ^ 3 := mul_nonneg hρmax (pow_nonneg hL.le 3)
    have hNad : gcAdmissible ρmax L N := by
      dsimp [gcAdmissible, N]
      exact Nat.floor_le hx0
    have hgcle := gcBox_le_value (μ := μ) (ρmax := ρmax) (L := L) hμ hρmax hL hv hNad
    have hNdens : (N : ℝ) / L ^ 3 ≤ ρmax := by
      dsimp [N]
      have hfl : (Nat.floor (ρmax * L ^ 3) : ℝ) ≤ ρmax * L ^ 3 := Nat.floor_le hx0
      rwa [div_le_iff₀ (pow_pos hL 3)]
    have hEbd := hbd ρmax N (L := L) hL1 hρmax hNdens
    -- gcDensity(μ,L) ≤ E(N,L)/L³ − μN/L³ ≤ C(..) − μρmax + μ/L³
    have hle1 : gcDensity v μ ρmax L ≤ (boxEnergy N L v - μ * (N : ℝ)) / L ^ 3 := by
      dsimp [gcDensity]
      have hdv := div_le_div_of_nonneg_right hgcle (pow_nonneg hL.le 3)
      -- (gcBox + ... hmm hgcle : gcBox ≤ E − μN: div: gcBox/L³ ≤ (E−μN)/L³
      simpa using hdv
    have hNgt : ρmax * L ^ 3 - 1 < (N : ℝ) := by
      have hf := Nat.lt_floor_add_one (ρmax * L ^ 3)
      change ρmax * L ^ 3 - 1 < (Nat.floor (ρmax * L ^ 3) : ℝ)
      nlinarith
    have hμN : μ * (ρmax * L ^ 3 - 1) ≤ μ * (N : ℝ) :=
      mul_le_mul_of_nonneg_left (le_of_lt hNgt) hμ
    have hbig' : boxEnergy N L v - μ * (N : ℝ) ≤ boxEnergy N L v - μ * ρmax * L ^ 3 + μ := by
      nlinarith [hμN]
    have hmain : gcDensity v μ ρmax L ≤ boxEnergy N L v / L ^ 3 - μ * ρmax + μ / L ^ 3 := by
      have hL3 : L ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hL)
      have hd1 := div_le_div_of_nonneg_right hbig' (pow_nonneg hL.le 3)
      calc
        gcDensity v μ ρmax L ≤ (boxEnergy N L v - μ * (N : ℝ)) / L ^ 3 := hle1
        _ ≤ (boxEnergy N L v - μ * ρmax * L ^ 3 + μ) / L ^ 3 := hd1
        _ = boxEnergy N L v / L ^ 3 - μ * ρmax + μ / L ^ 3 := by
          field_simp [hL3]
    calc
      gcDensity v μ ρmax L ≤ boxEnergy N L v / L ^ 3 - μ * ρmax + μ / L ^ 3 := hmain
      _ ≤ C * (ρmax ^ 2 * vL1 v + ρmax) - μ * ρmax + μ / L ^ 3 := by
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
          add_le_add_right hEbd (-(μ * ρmax) + μ / L ^ 3)
  -- p(μ) = lim gcDensity ≤ lim of the RHS = C(..) − μρmax
  have ht := gcDensity_tendsto_pressure (v := v) (μ := μ) (ρmax := ρmax) (R := R)
    hμ hρmax hR hv hv1 hsupp
  have hz := tendsto_const_div_cube_nhds_zero hμ
  have hconst : Tendsto (fun L : ℝ => C * (ρmax ^ 2 * vL1 v + ρmax) - μ * ρmax) atTop
      (𝓝 (C * (ρmax ^ 2 * vL1 v + ρmax) - μ * ρmax)) := tendsto_const_nhds
  have hrhs : Tendsto (fun L : ℝ => C * (ρmax ^ 2 * vL1 v + ρmax) - μ * ρmax + μ / L ^ 3)
      atTop (𝓝 (C * (ρmax ^ 2 * vL1 v + ρmax) - μ * ρmax)) := by
    simpa using hconst.add hz
  have hsub : Tendsto (fun L : ℝ =>
      (C * (ρmax ^ 2 * vL1 v + ρmax) - μ * ρmax + μ / L ^ 3) - gcDensity v μ ρmax L)
      atTop (𝓝 ((C * (ρmax ^ 2 * vL1 v + ρmax) - μ * ρmax) - gcPressure v ρmax μ)) :=
    hrhs.sub ht
  have hnonneg : ∀ᶠ L : ℝ in atTop,
      0 ≤ (C * (ρmax ^ 2 * vL1 v + ρmax) - μ * ρmax + μ / L ^ 3) - gcDensity v μ ρmax L := by
    filter_upwards [hpt] with L h
    exact sub_nonneg.mpr h
  have h0 := ge_of_tendsto hsub hnonneg
  nlinarith


/-! ## The Legendre supremum `S(ρ) := sup_μ (p(μ) + μρ)` -/

/-- The set of affine grand-canonical values at density `ρ` (`μ ≥ 0`). -/
def gcSupSet (v : ℝ³ → ℝ) (ρmax : ℝ) (ρ : ℝ) : Set ℝ :=
  {y : ℝ | ∃ μ : ℝ, 0 ≤ μ ∧ y = gcPressure v ρmax μ + μ * ρ}

/-- `S(ρ) := sSup { p(μ) + μρ | μ ≥ 0 }`. -/
noncomputable def gcSup (v : ℝ³ → ℝ) (ρmax : ℝ) (ρ : ℝ) : ℝ :=
  sSup (gcSupSet v ρmax ρ)

/-- The set is nonempty (`μ = 0`). -/
lemma gcSupSet_nonempty (v : ℝ³ → ℝ) (ρmax ρ : ℝ) : (gcSupSet v ρmax ρ).Nonempty := by
  refine ⟨gcPressure v ρmax 0, 0, le_rfl, ?_⟩
  simp

/-- The set is bounded above for `ρ < ρmax` (the pressure decays linearly). -/
lemma gcSupSet_bddAbove {v : ℝ³ → ℝ} {ρmax ρ : ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hρmax : 0 ≤ ρmax) (hρρmax : ρ < ρmax) {R : ℝ} (hR : 0 ≤ R)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) : BddAbove (gcSupSet v ρmax ρ) := by
  rcases gcPressure_le_density_bound (v := v) (ρmax := ρmax) hv hv1 hρmax hR hsupp
    with ⟨C, hCpos, hbd⟩
  refine ⟨C * (ρmax ^ 2 * vL1 v + ρmax), ?_⟩
  intro y hy
  rcases hy with ⟨μ, hμ, rfl⟩
  have hle := hbd hμ
  have h2 : C * (ρmax ^ 2 * vL1 v + ρmax) - μ * ρmax + μ * ρ ≤
      C * (ρmax ^ 2 * vL1 v + ρmax) := by
    have hsub : μ * ρ - μ * ρmax ≤ 0 := by
      have hh : μ * (ρ - ρmax) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hμ (by linarith)
      have hrew : μ * (ρ - ρmax) = μ * ρ - μ * ρmax := by ring
      rwa [hrew] at hh
    nlinarith
  calc
    gcPressure v ρmax μ + μ * ρ ≤ C * (ρmax ^ 2 * vL1 v + ρmax) - μ * ρmax + μ * ρ := by
      simpa [add_comm, add_assoc, add_left_comm] using add_le_add_right hle (μ * ρ)
    _ ≤ C * (ρmax ^ 2 * vL1 v + ρmax) := h2

/-- Every affine GC line is below `S`. -/
lemma le_gcSup {v : ℝ³ → ℝ} {ρmax ρ μ : ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hρmax : 0 ≤ ρmax) (hρρmax : ρ < ρmax) (hμ : 0 ≤ μ) {R : ℝ} (hR : 0 ≤ R)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) :
    gcPressure v ρmax μ + μ * ρ ≤ gcSup v ρmax ρ := by
  unfold gcSup
  exact le_csSup (gcSupSet_bddAbove (v := v) (ρmax := ρmax) (ρ := ρ) hv hv1 hρmax hρρmax hR hsupp)
    ⟨μ, hμ, rfl⟩

/-- If a real `B` dominates every affine GC line then it dominates `S`. -/
lemma gcSup_le_of_forall {v : ℝ³ → ℝ} {ρmax ρ B : ℝ}
    (h : ∀ μ : ℝ, 0 ≤ μ → gcPressure v ρmax μ + μ * ρ ≤ B) : gcSup v ρmax ρ ≤ B := by
  unfold gcSup
  apply csSup_le (gcSupSet_nonempty v ρmax ρ)
  intro y hy
  rcases hy with ⟨μ, hμ, rfl⟩
  exact h μ hμ

/-- Convexity of `S`: the value at a mixture of densities is at most the mixture
of the values (valid on the half-line `ρ < ρmax`). -/
lemma gcSup_convex_ineq {v : ℝ³ → ℝ} {ρmax ρ₁ ρ₂ t : ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hρmax : 0 ≤ ρmax) (hρ1m : ρ₁ < ρmax) (hρ2m : ρ₂ < ρmax)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {R : ℝ} (hR : 0 ≤ R)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) :
    gcSup v ρmax (t * ρ₁ + (1 - t) * ρ₂) ≤ t * gcSup v ρmax ρ₁ + (1 - t) * gcSup v ρmax ρ₂ := by
  apply gcSup_le_of_forall
  intro μ hμ
  have h1 := le_gcSup (v := v) (ρmax := ρmax) (ρ := ρ₁) (μ := μ) hv hv1 hρmax hρ1m hμ hR hsupp
  have h2 := le_gcSup (v := v) (ρmax := ρmax) (ρ := ρ₂) (μ := μ) hv hv1 hρmax hρ2m hμ hR hsupp
  have hw : t * (gcPressure v ρmax μ + μ * ρ₁) + (1 - t) * (gcPressure v ρmax μ + μ * ρ₂) ≤
      t * gcSup v ρmax ρ₁ + (1 - t) * gcSup v ρmax ρ₂ := by
    exact add_le_add (mul_le_mul_of_nonneg_left h1 ht0) (mul_le_mul_of_nonneg_left h2 (by linarith))
  have hEq : gcPressure v ρmax μ + μ * (t * ρ₁ + (1 - t) * ρ₂) =
      t * (gcPressure v ρmax μ + μ * ρ₁) + (1 - t) * (gcPressure v ρmax μ + μ * ρ₂) := by
    ring
  rwa [hEq]

/-- `S` is convex on `(-∞, ρmax)`, in particular on `(0,ρmax)`. -/
lemma gcSup_convexOn {v : ℝ³ → ℝ} {ρmax : ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hρmax : 0 ≤ ρmax) {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) :
    ConvexOn ℝ (Set.Iio ρmax) (fun ρ : ℝ => gcSup v ρmax ρ) := by
  refine ⟨convex_Iio ρmax, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxm : x < ρmax := hx
  have hym : y < ρmax := hy
  have ha1 : a ≤ 1 := by linarith
  have hb' : b = 1 - a := by linarith
  rw [hb']
  simpa [smul_eq_mul] using gcSup_convex_ineq (v := v) (ρmax := ρmax) (ρ₁ := x) (ρ₂ := y) (t := a)
    hv hv1 hρmax hxm hym ha ha1 hR hsupp

/-- `S` is continuous on `(-∞, ρmax)`. -/
lemma gcSup_continuousOn {v : ℝ³ → ℝ} {ρmax : ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hρmax : 0 ≤ ρmax) {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) :
    ContinuousOn (fun ρ : ℝ => gcSup v ρmax ρ) (Set.Iio ρmax) := by
  exact (gcSup_convexOn (v := v) (ρmax := ρmax) hv hv1 hρmax hR hsupp).continuousOn isOpen_Iio

/-- `S` is continuous on `(0,ρmax)`. -/
lemma gcSup_continuousOn_Ioo {v : ℝ³ → ℝ} {ρmax : ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hρmax : 0 ≤ ρmax) {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) :
    ContinuousOn (fun ρ : ℝ => gcSup v ρmax ρ) (Set.Ioo (0 : ℝ) ρmax) := by
  exact (gcSup_continuousOn (v := v) (ρmax := ρmax) hv hv1 hρmax hR hsupp).mono (fun ρ hρ => hρ.2)

/-- The canonical liminf dominates `S` on `[0, ρmax)`. -/
lemma diagLiminf_ge_gcSup {v : ℝ³ → ℝ} {ρ ρmax : ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hρmax : 0 ≤ ρmax) (hρ0 : 0 ≤ ρ) (hρρmax : ρ < ρmax) {R : ℝ} (hR : 0 ≤ R)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) : gcSup v ρmax ρ ≤ diagLiminf v ρ := by
  apply gcSup_le_of_forall
  intro μ hμ
  exact diagLiminf_ge_gc_affine (v := v) (ρ := ρ) (ρmax := ρmax) (μ := μ) hv hv1 hρmax hρ0
    (le_of_lt hρρmax) hμ hR hsupp


/-! ## From the upper equivalence bound to the thermodynamic limit -/

/-- The residual upper-side hypothesis of Layer 2 (equivalence of ensembles):
for densities `0 < ρ < ρmax` the diagonal limsup does not exceed the Legendre
supremum `S(ρ)`.  (Together with `x̲ ≥ S` this forces `x̲ = x̄ = S` and hence
continuity of the canonical energy density on `(0,ρmax)`.) -/
def gcSup_upper (v : ℝ³ → ℝ) (ρmax : ℝ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ρ < ρmax → diagLimsup v ρ ≤ gcSup v ρmax ρ

/-- Under the upper bound, the diagonal limit at `ρ ∈ (0,ρmax)` exists and
equals `S(ρ)`. -/
lemma diag_tendsto_of_gcSup_upper {v : ℝ³ → ℝ} {ρ ρmax : ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hρmax : 0 ≤ ρmax) {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hρ : 0 < ρ) (hρm : ρ < ρmax) (hupper : gcSup_upper v ρmax) :
    Tendsto (fun L : ℝ => diag v ρ L) atTop (𝓝 (gcSup v ρmax ρ)) := by
  have hlow : gcSup v ρmax ρ ≤ diagLiminf v ρ :=
    diagLiminf_ge_gcSup (v := v) (ρ := ρ) (ρmax := ρmax) hv hv1 hρmax hρ.le hρm hR hsupp
  have hle1 : diagLiminf v ρ ≤ diagLimsup v ρ := diagLiminf_le_diagLimsup hv hv1 hρ.le
  have hle2 : diagLimsup v ρ ≤ gcSup v ρmax ρ := hupper ρ hρ hρm
  have hx : diagLiminf v ρ = gcSup v ρmax ρ := le_antisymm (le_trans hle1 hle2) hlow
  have heq : diagLiminf v ρ = diagLimsup v ρ := le_antisymm hle1 (le_trans hle2 hlow)
  have ht := diag_tendsto_of_liminf_eq_limsup (v := v) (ρ := ρ) hv hv1 hρ.le heq
  simpa [hx] using ht

/-- `gcSup` is continuous at every density of `(0,ρmax)`. -/
lemma gcSup_continuousAt {v : ℝ³ → ℝ} {ρ ρmax : ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hρmax : 0 ≤ ρmax) {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hρ : 0 < ρ) (hρm : ρ < ρmax) : ContinuousAt (fun ρ : ℝ => gcSup v ρmax ρ) ρ := by
  exact (gcSup_continuousOn_Ioo (v := v) (ρmax := ρmax) hv hv1 hρmax hR hsupp).continuousAt
    (isOpen_Ioo.mem_nhds ⟨hρ, hρm⟩)

/-- The `hconv` hypothesis follows from the upper equivalence bound: if
`diagLimsup v ρ ≤ S(ρ)` on `(0,ρmax)` then the box densities converge along
the joint filter at every small density. -/
lemma eventually_hconv_of_gcSup_upper {v : ℝ³ → ℝ} {ρmax : ℝ} (hv : 0 ≤ v)
    (hv1 : MemLp v 1) (hρmax : 0 < ρmax) {R : ℝ} (hR : 0 ≤ R)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) (hupper : gcSup_upper v ρmax) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ x : ℝ, Tendsto (boxDensity v) (jointFilter ρ) (𝓝 x) := by
  have hlt : ∀ᶠ ρ : ℝ in 𝓝[>] (0 : ℝ), ρ < ρmax := by
    have hio : ∀ᶠ y : ℝ in 𝓝 (0 : ℝ), y < ρmax := isOpen_Iio.mem_nhds hρmax
    exact hio.filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hlt] with ρ hρpos hρlt
  refine ⟨gcSup v ρmax ρ, ?_⟩
  exact tendsto_boxDensity_of_diag_limits_on (v := v) (ρ := ρ) (ρ₀ := ρmax)
    (x := fun ρ : ℝ => gcSup v ρmax ρ) hv hv1 hρpos hρlt
    (gcSup_continuousAt (v := v) (ρ := ρ) (ρmax := ρmax) hv hv1 hρmax.le hR hsupp hρpos hρlt)
    (fun ρ' hρ'0 hρ'lt =>
      diag_tendsto_of_gcSup_upper (v := v) (ρ := ρ') (ρmax := ρmax) hv hv1 hρmax.le hR hsupp
        hρ'0 hρ'lt hupper)


/-! ## The density is controlled at `μ = 0` (boundary strip of the sup) -/

/-- `gcDensity(μ,L) ≤ gcDensity(0,L)` for `μ ≥ 0` (larger chemical potentials
only lower the grand-canonical optimum). -/
lemma gcDensity_le_gcDensity_zero {v : ℝ³ → ℝ} {μ ρmax L : ℝ} (hμ : 0 ≤ μ)
    (hρmax : 0 ≤ ρmax) (hL : 0 < L) (hv : 0 ≤ v) :
    gcDensity v μ ρmax L ≤ gcDensity v 0 ρmax L := by
  have hle : gcBox v μ ρmax L ≤ gcBox v 0 ρmax L := by
    unfold gcBox
    apply sInf_le_sInf_of_le (A := gcSet v 0 ρmax L) (B := gcSet v μ ρmax L)
    · exact gcSet_nonempty (μ := 0) hρmax hL.le
    · exact gcSet_bddBelow (μ := μ) (ρmax := ρmax) (L := L) hμ hρmax hL hv
    · intro a ha
      rcases ha with ⟨N, hNad, rfl⟩
      refine ⟨boxEnergy N L v - μ * (N : ℝ), ⟨N, hNad, rfl⟩, ?_⟩
      nlinarith
  dsimp [gcDensity]
  exact div_le_div_of_nonneg_right hle (pow_nonneg hL.le 3)

/-- Boundary lower bound: `gcDensity(0,L) − gcDensity(μ,L) ≤ μρmax`. -/
lemma gcDensity_zero_sub_le {v : ℝ³ → ℝ} {μ ρmax L : ℝ} (hμ : 0 ≤ μ)
    (hρmax : 0 ≤ ρmax) (hL : 0 < L) (hv : 0 ≤ v) :
    gcDensity v 0 ρmax L - gcDensity v μ ρmax L ≤ μ * ρmax := by
  have hle : gcBox v 0 ρmax L - gcBox v μ ρmax L ≤ μ * ρmax * L ^ 3 := by
    unfold gcBox
    have hc : sInf (gcSet v 0 ρmax L) - μ * ρmax * L ^ 3 ≤ sInf (gcSet v μ ρmax L) := by
      apply le_csInf (gcSet_nonempty (μ := μ) hρmax hL.le)
      intro z hz
      rcases hz with ⟨N, hNad, rfl⟩
      have hE : sInf (gcSet v 0 ρmax L) ≤ boxEnergy N L v := by
        apply csInf_le (gcSet_bddBelow (μ := 0) (ρmax := ρmax) (L := L) (by norm_num) hρmax hL hv)
        exact ⟨N, hNad, by simp⟩
      have hNad' : (N : ℝ) ≤ ρmax * L ^ 3 := by
        dsimp [gcAdmissible] at hNad
        exact hNad
      have h1 : μ * (N : ℝ) ≤ μ * (ρmax * L ^ 3) := mul_le_mul_of_nonneg_left hNad' hμ
      nlinarith
    nlinarith
  dsimp [gcDensity]
  have hd := div_le_div_of_nonneg_right hle (pow_nonneg hL.le 3)
  have hL3 : L ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hL)
  rw [sub_div] at hd
  have hr : (μ * ρmax * L ^ 3) / L ^ 3 = μ * ρmax := by field_simp [hL3]
  rwa [hr] at hd

/-- Lipschitz control of the density at `μ = 0`:
`|gcDensity(μ,L) − gcDensity(0,L)| ≤ μρmax`. -/
lemma gcDensity_lipschitz_at_zero {v : ℝ³ → ℝ} {μ ρmax L : ℝ} (hμ : 0 ≤ μ)
    (hρmax : 0 ≤ ρmax) (hL : 0 < L) (hv : 0 ≤ v) :
    |gcDensity v μ ρmax L - gcDensity v 0 ρmax L| ≤ μ * ρmax := by
  have h1 := gcDensity_zero_sub_le (μ := μ) (ρmax := ρmax) (L := L) hμ hρmax hL hv
  have h2 := gcDensity_le_gcDensity_zero (μ := μ) (ρmax := ρmax) (L := L) hμ hρmax hL hv
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

end BoseGases

end Submission
