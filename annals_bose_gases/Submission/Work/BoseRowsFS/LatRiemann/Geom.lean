import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseRowsFS.LatRiemannDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.LatRiemann.Geom` — the half-open cells of the lattice `h·ℤ³`

Infrastructure for `Work.BoseRowsFS.LatRiemann.lattice_riemann_core`.

The comparison of the continuum integral `∫ Φ(p)/‖p‖² dp` with the Riemann-type
sum `Σ_{m ∈ K} h³ Φ(latPt h m)/‖latPt h m‖²` is organised around the *half-open*
cells

    `hbox h m = {p | ∀ i, h * m i - h/2 ≤ p i ∧ p i < h * m i + h/2}`

of side `h` centred at `latPt h m = h • zvec m`.  Half-open cells (rather than the
closed cells `Work.BoseRowsFS.cell`) have two decisive advantages:

* they are pairwise **disjoint** (no a.e.-disjointness / null-set bookkeeping),
  so `∫_{⋃ hbox} = Σ ∫_{hbox}` with no measure-theoretic caveat;
* every `p` lies in exactly one of them, namely `hbox h (rnd h p)`, where
  `rnd h p` is the coordinatewise rounding index — no "pick a cell containing
  `p`" ambiguity.

Everything here is elementary: the volume of a cell (`volume_hbox`), the
rounding membership (`mem_hbox_rnd`), the coordinate/eulidean size bounds
(`hbox_coord_bound`, `norm_sub_latPt_le`) and the fact that a non-central cell
stays at distance `≥ h/2` from the origin (`norm_ge_of_mem_hbox`).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseRowsFS.LatRiemann

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The half-open cell of side `h` centred at the lattice point `latPt h m`:
`{p | ∀ i, h·m i - h/2 ≤ p i < h·m i + h/2}`. -/
def hbox (h : ℝ) (m : Fin 3 → ℤ) : Set ℝ³ :=
  {p | ∀ i : Fin 3, h * (m i : ℝ) - h / 2 ≤ p i ∧ p i < h * (m i : ℝ) + h / 2}

/-- The rounding map: for `h ≠ 0` and every `p`, the index of the (unique) half-open
cell containing `p` is `rnd h p`. -/
def rnd (h : ℝ) (p : ℝ³) : Fin 3 → ℤ := fun i => ⌊p i / h + 1 / 2⌋

lemma measurableSet_hbox (h : ℝ) (m : Fin 3 → ℤ) : MeasurableSet (hbox h m) := by
  simp only [hbox]
  measurability

lemma mem_hbox_rnd {h : ℝ} (hh : 0 < h) (p : ℝ³) : p ∈ hbox h (rnd h p) := by
  intro i
  have hne : h ≠ 0 := ne_of_gt hh
  have h1 : ((⌊p i / h + 1 / 2⌋ : ℤ) : ℝ) ≤ p i / h + 1 / 2 := Int.floor_le _
  have h2 : p i / h + 1 / 2 < ((⌊p i / h + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  simp only [rnd]
  constructor
  · have hmul : h * ((⌊p i / h + 1 / 2⌋ : ℤ) : ℝ) ≤ h * (p i / h + 1 / 2) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hh)
    have h3 : h * (p i / h + 1 / 2) = p i + h / 2 := by field_simp
    linarith
  · have hmul : h * (p i / h + 1 / 2) < h * (((⌊p i / h + 1 / 2⌋ : ℤ) : ℝ) + 1) :=
      mul_lt_mul_of_pos_left h2 hh
    have h3 : h * (p i / h + 1 / 2) = p i + h / 2 := by field_simp
    have h4 : h * (((⌊p i / h + 1 / 2⌋ : ℤ) : ℝ) + 1)
        = h * ((⌊p i / h + 1 / 2⌋ : ℤ) : ℝ) + h := by ring
    linarith

/-- Coordinatewise size bound: on `hbox h m` every coordinate is within `h/2` of the
corresponding coordinate of `latPt h m`. -/
lemma hbox_coord_bound {h : ℝ} {m : Fin 3 → ℤ} {p : ℝ³}
    (hp : p ∈ hbox h m) (i : Fin 3) : |p i - h * (m i : ℝ)| ≤ h / 2 := by
  have h1 : h * (m i : ℝ) - h / 2 ≤ p i := (hp i).1
  have h2 : p i < h * (m i : ℝ) + h / 2 := (hp i).2
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- `latPt` differs from `p` by at most half the diagonal of the cell. -/
lemma norm_sub_latPt_le {h : ℝ} (hh : 0 < h) {m : Fin 3 → ℤ} {p : ℝ³}
    (hp : p ∈ hbox h m) : ‖p - Work.BoseRowsFS.latPt h m‖ ≤ h * Real.sqrt 3 / 2 := by
  have hcoord : ∀ i : Fin 3, ‖(p - Work.BoseRowsFS.latPt h m) i‖ ≤ h / 2 := by
    intro i
    have h1 : h * (m i : ℝ) - h / 2 ≤ p i := (hp i).1
    have h2 : p i < h * (m i : ℝ) + h / 2 := (hp i).2
    have h3 : (Work.BoseRowsFS.latPt h m) i = h * (m i : ℝ) := rfl
    rw [PiLp.sub_apply, h3, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hsum : (∑ i : Fin 3, ‖(p - Work.BoseRowsFS.latPt h m) i‖ ^ 2) ≤ 3 * (h / 2) ^ 2 := by
    have hstep : ∀ i : Fin 3, ‖(p - Work.BoseRowsFS.latPt h m) i‖ ^ 2 ≤ (h / 2) ^ 2 := by
      intro i
      have := hcoord i
      have h4 : (0 : ℝ) ≤ h / 2 := by linarith
      nlinarith [norm_nonneg ((p - Work.BoseRowsFS.latPt h m) i)]
    refine (Finset.sum_le_sum (fun i _ => hstep i)).trans (le_of_eq ?_)
    simp [Finset.sum_const, Fintype.card_fin]
  rw [EuclideanSpace.norm_eq]
  refine (Real.sqrt_le_sqrt hsum).trans (le_of_eq ?_)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ h / 2)]
  ring

/-- A cell of a lattice point `m ≠ 0` stays at distance `≥ h/2` from the origin. -/
lemma norm_ge_of_mem_hbox {h : ℝ} {m : Fin 3 → ℤ} (hm : m ≠ 0) (hh : 0 < h)
    {p : ℝ³} (hp : p ∈ hbox h m) : h / 2 ≤ ‖p‖ := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hm (funext hc)
  have hmi : (1 : ℤ) ≤ |m i| := Int.one_le_abs hi
  have hmiR : (1 : ℝ) ≤ |(m i : ℝ)| := by exact_mod_cast hmi
  have h1 : h * (m i : ℝ) - h / 2 ≤ p i := (hp i).1
  have h2 : p i < h * (m i : ℝ) + h / 2 := (hp i).2
  have hle : h / 2 ≤ |p i| := by
    rcases lt_trichotomy (m i) 0 with hneg | hzero | hpos
    · have hc : (m i : ℝ) ≤ -1 := by
        have h' : m i ≤ -1 := by omega
        exact_mod_cast h'
      have hlt : p i < -h / 2 := by nlinarith
      rw [abs_of_neg (by linarith)]
      linarith
    · exact absurd hzero hi
    · have hc : (1 : ℝ) ≤ (m i : ℝ) := by
        have h' : (1 : ℤ) ≤ m i := by omega
        exact_mod_cast h'
      have hle' : h / 2 ≤ p i := by nlinarith
      rw [abs_of_nonneg (by linarith)]
      linarith
  calc h / 2 ≤ |p i| := hle
    _ = ‖p i‖ := by rw [Real.norm_eq_abs]
    _ ≤ ‖p‖ := PiLp.norm_apply_le p i

/-- The half-open cells are pairwise disjoint. -/
lemma disjoint_hbox {h : ℝ} (hh : 0 < h) {m m' : Fin 3 → ℤ} (hne : m ≠ m') :
    Disjoint (hbox h m) (hbox h m') := by
  rw [Set.disjoint_left]
  intro p hp hp'
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ m' i := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  rcases lt_or_gt_of_ne hi with hlt | hlt
  · have h1 : m i + 1 ≤ m' i := Int.add_one_le_iff.mpr hlt
    have h1' : ((m i : ℝ) + 1) ≤ (m' i : ℝ) := by exact_mod_cast h1
    have h2 : h * ((m i : ℝ) + 1) ≤ h * (m' i : ℝ) :=
      mul_le_mul_of_nonneg_left h1' (le_of_lt hh)
    have h3 : p i < h * (m i : ℝ) + h / 2 := (hp i).2
    have h4 : h * (m' i : ℝ) - h / 2 ≤ p i := (hp' i).1
    linarith
  · have h1 : m' i + 1 ≤ m i := Int.add_one_le_iff.mpr hlt
    have h1' : ((m' i : ℝ) + 1) ≤ (m i : ℝ) := by exact_mod_cast h1
    have h2 : h * ((m' i : ℝ) + 1) ≤ h * (m i : ℝ) :=
      mul_le_mul_of_nonneg_left h1' (le_of_lt hh)
    have h3 : p i < h * (m' i : ℝ) + h / 2 := (hp' i).2
    have h4 : h * (m i : ℝ) - h / 2 ≤ p i := (hp i).1
    linarith

/-- The volume of a half-open cell. -/
lemma volume_hbox (h : ℝ) (m : Fin 3 → ℤ) :
    volume (hbox h m) = ENNReal.ofReal h ^ 3 := by
  set a : Fin 3 → ℝ := fun i => h * (m i : ℝ) - h / 2 with ha
  set b : Fin 3 → ℝ := fun i => h * (m i : ℝ) + h / 2 with hb
  have hmeas : MeasurableSet (hbox h m) := measurableSet_hbox h m
  have hmeas' : Measurable (WithLp.toLp 2 : (Fin 3 → ℝ) → (ℝ³)) :=
    (PiLp.volume_preserving_toLp (Fin 3)).measurable
  have heq : (WithLp.toLp 2 : (Fin 3 → ℝ) → (ℝ³)) ⁻¹' (hbox h m)
      = Set.pi Set.univ (fun i : Fin 3 => Set.Ico (a i) (b i)) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico, hbox,
      Set.mem_setOf_eq, ha, hb]
  have hmap : Measure.map (WithLp.toLp 2 : (Fin 3 → ℝ) → (ℝ³)) volume
      = (volume : Measure (ℝ³)) := (PiLp.volume_preserving_toLp (Fin 3)).map_eq
  calc volume (hbox h m)
      = Measure.map (WithLp.toLp 2 : (Fin 3 → ℝ) → (ℝ³)) volume (hbox h m) := by rw [hmap]
    _ = volume ((WithLp.toLp 2 : (Fin 3 → ℝ) → (ℝ³)) ⁻¹' (hbox h m)) :=
        Measure.map_apply hmeas' hmeas
    _ = volume (Set.pi Set.univ (fun i : Fin 3 => Set.Ico (a i) (b i))) := by rw [heq]
    _ = ∏ i : Fin 3, ENNReal.ofReal (b i - a i) := Real.volume_pi_Ico
    _ = ∏ _i : Fin 3, ENNReal.ofReal h := by
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [hb, ha]; ring_nf
    _ = ENNReal.ofReal h ^ 3 := by simp [Finset.prod_const, Fintype.card_fin]

/-- The volume of a half-open cell, as a real number. -/
lemma real_volume_hbox {h : ℝ} (hh : 0 ≤ h) (m : Fin 3 → ℤ) :
    (volume : Measure ℝ³).real (hbox h m) = h ^ 3 := by
  rw [measureReal_def, volume_hbox]
  have : ENNReal.ofReal h ^ 3 = ENNReal.ofReal (h ^ 3) := (ENNReal.ofReal_pow hh 3).symm
  rw [this, ENNReal.toReal_ofReal (by positivity)]

lemma norm_latPt_eq (h : ℝ) (m : Fin 3 → ℤ) :
    ‖Work.BoseRowsFS.latPt h m‖ = |h| * ‖Work.BoseRowsFS.zvec m‖ := by
  rw [Work.BoseRowsFS.zvec_smul, norm_smul, Real.norm_eq_abs]

lemma norm_latPt_eq_of_nonneg {h : ℝ} (hh : 0 ≤ h) (m : Fin 3 → ℤ) :
    ‖Work.BoseRowsFS.latPt h m‖ = h * ‖Work.BoseRowsFS.zvec m‖ := by
  rw [norm_latPt_eq, abs_of_nonneg hh]

lemma zvec_ne_zero {m : Fin 3 → ℤ} (hm : m ≠ 0) : Work.BoseRowsFS.zvec m ≠ 0 := by
  intro h
  apply hm
  funext i
  have := congrArg (fun v : ℝ³ => v i) h
  simpa [Work.BoseRowsFS.zvec] using this

lemma one_le_norm_zvec {m : Fin 3 → ℤ} (hm : m ≠ 0) : 1 ≤ ‖Work.BoseRowsFS.zvec m‖ := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hm (funext hc)
  have h1 : (1 : ℝ) ≤ |(m i : ℝ)| := by
    have h' : (1 : ℤ) ≤ |m i| := Int.one_le_abs hi
    exact_mod_cast h'
  calc (1 : ℝ) ≤ |(m i : ℝ)| := h1
    _ = ‖(Work.BoseRowsFS.zvec m) i‖ := by
        simp [Work.BoseRowsFS.zvec, Real.norm_eq_abs]
    _ ≤ ‖Work.BoseRowsFS.zvec m‖ := PiLp.norm_apply_le _ _

lemma latPt_ne_zero {h : ℝ} (hh : 0 < h) {m : Fin 3 → ℤ} (hm : m ≠ 0) :
    Work.BoseRowsFS.latPt h m ≠ 0 := by
  have h1 : ‖Work.BoseRowsFS.latPt h m‖ = h * ‖Work.BoseRowsFS.zvec m‖ :=
    norm_latPt_eq_of_nonneg (le_of_lt hh) m
  have h2 : 0 < ‖Work.BoseRowsFS.zvec m‖ := lt_of_lt_of_le zero_lt_one (one_le_norm_zvec hm)
  intro hzero
  rw [hzero, norm_zero] at h1
  nlinarith [h1, h2]

lemma norm_latPt_ge {h : ℝ} (hh : 0 < h) {m : Fin 3 → ℤ} (hm : m ≠ 0) :
    h ≤ ‖Work.BoseRowsFS.latPt h m‖ := by
  rw [norm_latPt_eq_of_nonneg (le_of_lt hh) m]
  nlinarith [one_le_norm_zvec hm, hh]

/-- The ball containing the central cell. -/
lemma hbox_zero_subset {h : ℝ} (hh : 0 < h) {p : ℝ³} (hp : p ∈ hbox h 0) :
    ‖p‖ ≤ h * Real.sqrt 3 / 2 := by
  have hcoord : ∀ i : Fin 3, |p i| ≤ h / 2 := by
    intro i
    have h1 : h * ((0 : Fin 3 → ℤ) i : ℝ) - h / 2 ≤ p i := (hp i).1
    have h2 : p i < h * ((0 : Fin 3 → ℤ) i : ℝ) + h / 2 := (hp i).2
    simp only [Pi.zero_apply, Int.cast_zero, mul_zero] at h1 h2
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hsum : (∑ i : Fin 3, ‖p i‖ ^ 2) ≤ 3 * (h / 2) ^ 2 := by
    have hstep : ∀ i : Fin 3, ‖p i‖ ^ 2 ≤ (h / 2) ^ 2 := by
      intro i
      have := hcoord i
      rw [Real.norm_eq_abs]
      nlinarith [abs_nonneg (p i)]
    refine (Finset.sum_le_sum (fun i _ => hstep i)).trans (le_of_eq ?_)
    simp [Finset.sum_const, Fintype.card_fin]
  rw [EuclideanSpace.norm_eq]
  refine (Real.sqrt_le_sqrt hsum).trans (le_of_eq ?_)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ h / 2)]
  ring

end Work.BoseRowsFS.LatRiemann
