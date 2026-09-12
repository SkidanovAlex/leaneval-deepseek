import Mathlib
import Submission.PolyaCore
import Submission.XTransfer
import Submission.DirSet
import Submission.DirCycle
import Submission.E2bAssembly

/-!
# E2c geometry: the deformed contour lies in the fattened hedgehog

`Submission.E2c` (the Pólya/Hankel wiring) bounds the pieces of the
deformed contour of `Submission.DStar.deformation_star` using the
`HedgehogBound`-polynomials, which are only small on the ε-fattening
`FatStar S ε` of the hedgehog `star S`.  This module supplies the pure
metric geometry: every point of the contour (window caps at radius
`e^{u_j}` over direction `x_j`, radial sides at `x_j ± δ`, origin-near gap
arcs at radius `e^A`) is within `ε` of `star S`, provided the parameters
satisfy the growth conditions

    e^{u_j} − ℓ_j < ε      and      2·e^{u_j}·δ < ε      and      e^A < ε

where `ℓ_j` is the length of the spike of `star S` in direction `x_j`.
-/

noncomputable section

open scoped Real Polynomial Topology BigOperators

namespace Submission.E2cGeom

open Submission.XTransfer
open Submission.DirSet
open Submission.PolyaCore

/-- The spike endpoints of `star S` lying on the ray of argument `x`. -/
def dirEndpoints (S : Finset ℂ) (x : ℝ) : Finset ℂ :=
  (spikeEndpoints S).filter (fun w : ℂ => Complex.arg w = x)

lemma mem_dirEndpoints_iff (S : Finset ℂ) (x : ℝ) (w : ℂ) :
    w ∈ dirEndpoints S x ↔ w ∈ spikeEndpoints S ∧ Complex.arg w = x := by
  simp [dirEndpoints]

/-- Nonempty if `x` is a spike direction. -/
lemma dirEndpoints_nonempty_of_mem_dirSet (S : Finset ℂ) {x : ℝ} (hx : x ∈ dirSet S) :
    (dirEndpoints S x).Nonempty := by
  classical
  rw [dirSet] at hx
  rcases Finset.mem_image.mp hx with ⟨w, hw, rfl⟩
  refine ⟨w, ?_⟩
  exact (mem_dirEndpoints_iff S (Complex.arg w) w).2 ⟨hw, rfl⟩

/-- The direction-`x` endpoints form a finite set equal to the preimage of
`x` in `dirSet`. -/
lemma dirEndpoints_image_eq (S : Finset ℂ) (x : ℝ) :
    (dirEndpoints S x).image (fun w : ℂ => ‖w‖) =
      ((spikeEndpoints S).filter (fun w : ℂ => Complex.arg w = x)).image (fun w : ℂ => ‖w‖) := by
  rfl

/-- Membership in `dirSet` is equivalent to the existence of an endpoint on
that ray. -/
lemma mem_dirSet_iff_endpoint (S : Finset ℂ) (x : ℝ) :
    x ∈ dirSet S ↔ (dirEndpoints S x).Nonempty := by
  classical
  constructor
  · intro hx
    exact dirEndpoints_nonempty_of_mem_dirSet S hx
  · intro hne
    rcases hne with ⟨w, hw⟩
    have hwS : w ∈ spikeEndpoints S := ((mem_dirEndpoints_iff S x w).1 hw).1
    have harg : Complex.arg w = x := ((mem_dirEndpoints_iff S x w).1 hw).2
    rw [dirSet, Finset.mem_image]
    exact ⟨w, hwS, harg⟩

/-- The length of the spike of `star S` in direction `x`: the maximal norm
of the direction-`x` endpoints. -/
def dirSpikeLen (S : Finset ℂ) (x : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ w ∈ dirEndpoints S x, r = ‖w‖}

/-- A direction-`x` endpoint realizes the spike length. -/
lemma dirSpikeLen_mem (S : Finset ℂ) {x : ℝ} (hx : x ∈ dirSet S) :
    ∃ w ∈ dirEndpoints S x, ‖w‖ = dirSpikeLen S x := by
  classical
  let E : Finset ℝ := (dirEndpoints S x).image (fun w : ℂ => ‖w‖)
  have hEne : E.Nonempty := by
    rcases dirEndpoints_nonempty_of_mem_dirSet S hx with ⟨w, hw⟩
    exact Finset.image_nonempty.mpr ⟨w, hw⟩
  have hEq : ({r : ℝ | ∃ w ∈ dirEndpoints S x, r = ‖w‖} : Set ℝ) = (E : Set ℝ) := by
    ext r
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
    · intro hr
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hr) with ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
  have hmax_mem : E.max' hEne ∈ E := Finset.max'_mem E hEne
  have hsup_le : sSup (E : Set ℝ) ≤ E.max' hEne := by
    refine csSup_le ?_ ?_
    · exact ⟨E.max' hEne, Finset.mem_coe.mpr hmax_mem⟩
    · intro r hr
      exact Finset.le_max' E r (Finset.mem_coe.mp hr)
  have hle_sup : E.max' hEne ≤ sSup (E : Set ℝ) :=
    le_csSup E.bddAbove (Finset.mem_coe.mpr hmax_mem)
  have hsup : sSup (E : Set ℝ) = E.max' hEne := le_antisymm hsup_le hle_sup
  rcases Finset.mem_image.mp hmax_mem with ⟨w, hw, hnorm⟩
  refine ⟨w, hw, ?_⟩
  dsimp [dirSpikeLen]
  rw [hEq, hsup]
  exact hnorm

/-- Every direction-`x` endpoint has norm at most the spike length. -/
lemma norm_le_dirSpikeLen (S : Finset ℂ) {x : ℝ} {w : ℂ} (hw : w ∈ dirEndpoints S x) :
    ‖w‖ ≤ dirSpikeLen S x := by
  classical
  let E : Finset ℝ := (dirEndpoints S x).image (fun w : ℂ => ‖w‖)
  have hEq : ({r : ℝ | ∃ w ∈ dirEndpoints S x, r = ‖w‖} : Set ℝ) = (E : Set ℝ) := by
    ext r
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
    · intro hr
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hr) with ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
  unfold dirSpikeLen
  rw [hEq]
  exact le_csSup E.bddAbove (Finset.mem_image.mpr ⟨w, hw, rfl⟩)

/-- The spike length in a direction is positive when all spike endpoints
are nonzero. -/
lemma dirSpikeLen_pos (S : Finset ℂ) {x : ℝ} (hx : x ∈ dirSet S)
    (hw0 : ∀ w ∈ spikeEndpoints S, w ≠ 0) : 0 < dirSpikeLen S x := by
  rcases dirSpikeLen_mem S hx with ⟨w, hw, hnorm⟩
  have hwne : w ≠ 0 := hw0 w ((mem_dirEndpoints_iff S x w).1 hw).1
  have hnormpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  rwa [hnorm] at hnormpos

/-- The star contains the whole spike `[0, w]` of any spike endpoint `w`. -/
lemma segment_subset_star_of_mem_spikeEndpoints {S : Finset ℂ} {w : ℂ}
    (hw : w ∈ spikeEndpoints S) : segment ℝ 0 w ⊆ XTransfer.star S := by
  classical
  intro X hX
  rw [spikeEndpoints, Finset.mem_union] at hw
  rcases hw with hw | hw
  · rcases Finset.mem_image.mp hw with ⟨z, hz, rfl⟩
    exact ⟨z, hz, Or.inl hX⟩
  · rcases Finset.mem_image.mp hw with ⟨z, hz, rfl⟩
    exact ⟨z, hz, Or.inr hX⟩

/-- The maximal direction-`x` spike of length `ℓ := dirSpikeLen S x` is
contained in the star: `[0, ℓ·e^{i·x}] ⊆ star S`. -/
lemma segment_spikeLen_subset_star (S : Finset ℂ) {x : ℝ} (hx : x ∈ dirSet S) :
    segment ℝ 0 ((dirSpikeLen S x : ℂ) * Complex.exp (x * Complex.I)) ⊆ XTransfer.star S := by
  classical
  intro X hX
  rcases dirSpikeLen_mem S hx with ⟨w, hw, hnorm⟩
  have hwS : w ∈ spikeEndpoints S := ((mem_dirEndpoints_iff S x w).1 hw).1
  have hargw : Complex.arg w = x := ((mem_dirEndpoints_iff S x w).1 hw).2
  have hw_eq : (dirSpikeLen S x : ℂ) * Complex.exp (x * Complex.I) = w := by
    rw [← hnorm]
    calc
      (‖w‖ : ℂ) * Complex.exp (x * Complex.I) = (‖w‖ : ℂ) * Complex.exp (Complex.arg w * Complex.I) := by rw [hargw]
      _ = w := by simpa using (Complex.norm_mul_exp_arg_mul_I w).symm
  have hXw : X ∈ segment ℝ 0 w := by
    simpa [hw_eq] using hX
  exact segment_subset_star_of_mem_spikeEndpoints (S := S) (w := w) hwS hXw

/-- The real norm of a real number embedded in `ℂ` is its absolute value. -/
lemma norm_ofReal_complex (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  calc
    ‖(r : ℂ)‖ = ‖(algebraMap ℝ ℂ) r‖ := rfl
    _ = ‖r‖ * ‖(1 : ℂ)‖ := norm_algebraMap (𝕜 := ℝ) (𝕜' := ℂ) r
    _ = ‖r‖ := by simp
    _ = |r| := Real.norm_eq_abs r

/-- `‖e^{iΔ} − 1‖ ≤ 2·|Δ|` for `|Δ| ≤ 1`. -/
lemma norm_exp_mul_I_sub_one_le_two_abs {Δ : ℝ} (hΔ : |Δ| ≤ 1) :
    ‖Complex.exp (Δ * Complex.I) - 1‖ ≤ 2 * |Δ| := by
  have hx : ‖((Δ : ℂ) * Complex.I)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, norm_ofReal_complex]
    exact hΔ
  have hb := Complex.norm_exp_sub_one_le (x := (Δ : ℂ) * Complex.I) hx
  simpa using hb

/-- For real `r ≥ 0`, `|r - min r ℓ| = max (r - ℓ) 0`. -/
lemma abs_sub_min_eq_max (r ℓ : ℝ) (hr : 0 ≤ r) :
    |r - min r ℓ| = max (r - ℓ) 0 := by
  by_cases hrl : r ≤ ℓ
  · have hmin : min r ℓ = r := min_eq_left hrl
    rw [hmin, sub_self, abs_zero]
    have hneg : r - ℓ ≤ 0 := sub_nonpos.mpr hrl
    exact (max_eq_right hneg).symm
  · have hmin : min r ℓ = ℓ := min_eq_right (le_of_not_ge hrl)
    rw [hmin]
    have hnonneg : 0 ≤ r - ℓ := sub_nonneg.mpr (le_of_not_ge hrl)
    rw [abs_of_nonneg hnonneg]
    exact (max_eq_left hnonneg).symm

/-- A point on the ray of argument `x + Δ` at radius `r ≥ 0`, projected
radially onto the segment `[0, ℓ·e^{ix}]` (`m := min r ℓ`), stays within
`max (r − ℓ) 0 + 2·r·|Δ|` of it. -/
lemma dist_rot_to_ray_le {r ℓ : ℝ} (hr : 0 ≤ r) {x Δ : ℝ} (hΔ1 : |Δ| ≤ 1) :
    ‖(r : ℂ) * Complex.exp ((x + Δ) * Complex.I) -
        ((min r ℓ : ℝ) : ℂ) * Complex.exp (x * Complex.I)‖
      ≤ max (r - ℓ) 0 + 2 * r * |Δ| := by
  have h1 : ‖Complex.exp (Δ * Complex.I) - 1‖ ≤ 2 * |Δ| := norm_exp_mul_I_sub_one_le_two_abs hΔ1
  have hnormr : ‖(r : ℂ)‖ = r := by
    rw [norm_ofReal_complex, abs_of_nonneg hr]
  have hE : Complex.exp ((x + Δ) * Complex.I) =
      Complex.exp (x * Complex.I) * Complex.exp (Δ * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  let m : ℂ := ((min r ℓ : ℝ) : ℂ)
  let X1 : ℂ := (r : ℂ) * (Complex.exp (Δ * Complex.I) - 1)
  let X2 : ℂ := (r : ℂ) - m
  have hfac : (r : ℂ) * Complex.exp ((x + Δ) * Complex.I) - m * Complex.exp (x * Complex.I)
      = (X1 + X2) * Complex.exp (x * Complex.I) := by
    dsimp [X1, X2]
    rw [hE]
    ring
  have hX1 : ‖X1‖ ≤ 2 * r * |Δ| := by
    dsimp [X1]
    rw [norm_mul, hnormr]
    calc
      r * ‖Complex.exp (Δ * Complex.I) - 1‖ ≤ r * (2 * |Δ|) := mul_le_mul_of_nonneg_left h1 hr
      _ = 2 * r * |Δ| := by ring
  have hX2 : ‖X2‖ ≤ max (r - ℓ) 0 := by
    dsimp [X2, m]
    have hsub : ‖(r : ℂ) - ((min r ℓ : ℝ) : ℂ)‖ = |r - min r ℓ| := by
      rw [← Complex.ofReal_sub]
      exact norm_ofReal_complex (r - min r ℓ)
    calc
      ‖(r : ℂ) - ((min r ℓ : ℝ) : ℂ)‖ = |r - min r ℓ| := hsub
      _ = max (r - ℓ) 0 := abs_sub_min_eq_max r ℓ hr
      _ ≤ max (r - ℓ) 0 := le_rfl
  calc
    ‖(r : ℂ) * Complex.exp ((x + Δ) * Complex.I) -
        ((min r ℓ : ℝ) : ℂ) * Complex.exp (x * Complex.I)‖
        = ‖(X1 + X2) * Complex.exp (x * Complex.I)‖ := by
          have hEq : (r : ℂ) * Complex.exp ((x + Δ) * Complex.I) -
                ((min r ℓ : ℝ) : ℂ) * Complex.exp (x * Complex.I)
              = (X1 + X2) * Complex.exp (x * Complex.I) := by
                dsimp [X1, X2, m]
                rw [hE]
                ring
          rw [hEq]
    _ = ‖X1 + X2‖ := by
          rw [norm_mul, Complex.norm_exp_ofReal_mul_I]
          simp
    _ ≤ ‖X1‖ + ‖X2‖ := norm_add_le _ _
    _ ≤ 2 * r * |Δ| + max (r - ℓ) 0 := add_le_add hX1 hX2
    _ = max (r - ℓ) 0 + 2 * r * |Δ| := by rw [add_comm]
    _ ≤ max (r - ℓ) 0 + 2 * r * |Δ| := le_rfl

/-- The point `m·e^{ix}` with `0 ≤ m ≤ ℓ` lies on the segment
`[0, ℓ·e^{ix}]`. -/
lemma mem_segment_ray_of_le {ℓ m : ℝ} (hℓ0 : 0 ≤ ℓ) (hm0 : 0 ≤ m) (hmℓ : m ≤ ℓ) (x : ℝ) :
    (m : ℂ) * Complex.exp (x * Complex.I) ∈
      segment ℝ 0 ((ℓ : ℂ) * Complex.exp (x * Complex.I)) := by
  by_cases hℓ0' : ℓ = 0
  · have hmℓ0 : m ≤ 0 := by
      rw [hℓ0'] at hmℓ
      exact hmℓ
    have hm0' : m = 0 := le_antisymm hmℓ0 hm0
    simp [hℓ0', hm0']
  · have hℓpos : 0 < ℓ := lt_of_le_of_ne hℓ0 (Ne.symm hℓ0')
    rw [XTransfer.mem_segment_zero_iff]
    refine ⟨m / ℓ, ⟨div_nonneg hm0 (le_of_lt hℓpos), div_le_one_of_le₀ hmℓ (le_of_lt hℓpos)⟩, ?_⟩
    rw [Algebra.smul_def]
    have hmul : (m / ℓ : ℝ) * ℓ = m := by field_simp [hℓ0']
    calc
      (m : ℂ) * Complex.exp (x * Complex.I)
          = (((m / ℓ) * ℓ : ℝ) : ℂ) * Complex.exp (x * Complex.I) := by rw [hmul]
      _ = ((m / ℓ : ℝ) : ℂ) * ((ℓ : ℂ) * Complex.exp (x * Complex.I)) := by
            rw [← mul_assoc]
            rw [← Complex.ofReal_mul]

/-- `max a 0 ≤ c` when `a ≤ c` and `c ≥ 0`. -/
lemma max_zero_le_of_le {a c : ℝ} (hac : a ≤ c) (hc0 : 0 ≤ c) : max a 0 ≤ c := by
  rw [max_le_iff]
  exact ⟨hac, hc0⟩

/-- **Radial-side / window-cap points lie in the fattened hedgehog.**  For a
direction `x ∈ dirSet S` with spike length `ℓ := dirSpikeLen S x > 0`, any
point `r·e^{i(x+Δ)}` with `0 ≤ r ≤ e^u` and `|Δ| ≤ δ ≤ 1` is within `ε` of
`star S` provided `e^u − ℓ ≤ ε/2` and `2·e^u·δ ≤ ε/2`. -/
lemma fatStar_of_rot_point (S : Finset ℂ) {x : ℝ} (hx : x ∈ dirSet S) {ε δ u : ℝ}
    (hε0 : 0 < ε) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hug : Real.exp u - dirSpikeLen S x ≤ ε / 2)
    (huδ : 2 * Real.exp u * δ ≤ ε / 2)
    (hw0 : ∀ w ∈ spikeEndpoints S, w ≠ 0)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ Real.exp u) {Δ : ℝ} (hΔ : |Δ| ≤ δ) :
    (r : ℂ) * Complex.exp ((x + Δ) * Complex.I) ∈ FatStar S ε := by
  classical
  let ℓ : ℝ := dirSpikeLen S x
  let m : ℝ := min r ℓ
  let Y : ℂ := (m : ℂ) * Complex.exp (x * Complex.I)
  have hℓpos : 0 < ℓ := dirSpikeLen_pos S hx hw0
  have hYseg : Y ∈ segment ℝ 0 ((ℓ : ℂ) * Complex.exp (x * Complex.I)) := by
    dsimp [Y, m, ℓ]
    exact mem_segment_ray_of_le (ℓ := ℓ) (m := min r ℓ) (le_of_lt hℓpos)
      (le_min hr0 (le_of_lt hℓpos)) (min_le_right r ℓ) x
  have hYstar : Y ∈ XTransfer.star S := by
    dsimp [Y, m, ℓ]
    exact segment_spikeLen_subset_star S hx hYseg
  have hdist : ‖(r : ℂ) * Complex.exp ((x + Δ) * Complex.I) - Y‖
      ≤ max (r - ℓ) 0 + 2 * r * |Δ| := by
    dsimp [Y, m, ℓ]
    exact dist_rot_to_ray_le (r := r) (ℓ := dirSpikeLen S x) hr0 (le_trans hΔ hδ1)
  have hmax : max (r - ℓ) 0 ≤ ε / 2 := by
    have hrm : max (r - ℓ) 0 ≤ max (Real.exp u - ℓ) 0 := by
      exact max_le_max (sub_le_sub_right hr ℓ) (le_rfl)
    have hmain : max (Real.exp u - ℓ) 0 ≤ ε / 2 := by
      exact max_zero_le_of_le (by simpa [ℓ] using hug) (half_pos hε0).le
    exact le_trans hrm hmain
  have hd2 : 2 * r * |Δ| ≤ ε / 2 := by
    calc
      2 * r * |Δ| ≤ 2 * Real.exp u * |Δ| := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2)) (abs_nonneg Δ)
      _ ≤ 2 * Real.exp u * δ := by
            exact mul_le_mul_of_nonneg_left hΔ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos u).le)
      _ ≤ ε / 2 := by simpa [ℓ] using huδ
  have htot : max (r - ℓ) 0 + 2 * r * |Δ| ≤ ε := by linarith
  refine ⟨Y, hYstar, ?_⟩
  exact le_trans hdist htot

/-- **Origin-near gap arcs lie in the fattened hedgehog**: any point at
radius `e^A ≤ ε` is within `ε` of `0 ∈ star S`. -/
lemma fatStar_gap_point (S : Finset ℂ) (hSne : S.Nonempty) {ε A : ℝ}
    (hε0 : 0 < ε) (hA : Real.exp A ≤ ε) (θ : ℝ) :
    (Real.exp A : ℂ) * Complex.exp (θ * Complex.I) ∈ FatStar S ε := by
  refine ⟨(0 : ℂ), XTransfer.zero_mem_star hSne, ?_⟩
  calc
    ‖(Real.exp A : ℂ) * Complex.exp (θ * Complex.I) - 0‖
        = Real.exp A := by
          rw [sub_zero, norm_mul, Complex.norm_exp_ofReal_mul_I]
          rw [norm_ofReal_complex, abs_of_nonneg (Real.exp_pos A).le]
          simp
    _ ≤ ε := hA

end Submission.E2cGeom

end
