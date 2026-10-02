import Mathlib
import Submission.Work.PTGeometric.FlatSource

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The far behaviour of the flat source homotopy

The flat source homotopy `flatSourceHomotopy n H φ : ℝ^{n+1} → D.T` of
`Submission/Work/PTGeometric/FlatSource.lean` is

`x ↦ H (φ (cubeCoord n (tail x)), 1 + clamp (head x))`.

As `‖tail x‖ → ∞` the cube point `cubeCoord n (tail x)` tends to the boundary of the cube `I^n`, and
the loop `φ` is constant on that boundary.  Consequently the homotopy takes values arbitrarily close
to `H (φ y₀, τ) = D.t₀`, and since `D.t₀` is outside the closed set `core`, it eventually avoids
`core` altogether: this is the statement `exists_tailBound_flatSourceHomotopy_notMem`.

The mathematical content is the lemma `cubeCoord_eventually_mem` about the explicit chart
`cubeCoord : ℝ^n ≅ int I^n`, proved here from scratch:

* for `W ⊆ I^n` open containing the boundary, the complement `Wᶜ` is compact and disjoint from the
  boundary, so for each coordinate `i` the values `(y i : ℝ)`, `y ∈ Wᶜ`, stay `δ i` away from `0`
  and `1` (compactness of the projection);
* `|z i| ≥ 1/(δ i)` forces `(cubeCoord n z i : ℝ)` to leave the strip `[δ i, 1 - δ i]`, by the
  elementary estimate `min (c t) (1 - c t) ≤ 1/(2|t|)` for the sigmoid `c t = (1 + t/√(1+t²))/2`;
* so with `R := (∑ i, (δ i)⁻¹ + 1) * √n` every `z` with `‖z‖ ≥ R` has some coordinate of
  `cubeCoord n z` in the "escaping" region, hence lands in `W`.

The remaining step is a tube-lemma argument: `H` is continuous on the compact source, and is
identically `D.t₀` on `{φ y₀} × [1,2]`, so it is `core`-free on a product neighbourhood of that set.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Topology
open Set Filter

namespace Work.PTGeometric

noncomputable section

/-! The auxiliary lemmas on the far behaviour of the cube chart, kept in their own namespace so
that they do not collide with the (independently delegated) lemma of the same mathematical
content `Work.PTGeometric.cubeCoord_eventually_mem`. -/
namespace Far

/-! ## The one-dimensional estimate for the sigmoid chart -/

/-- For `t > 0`, `1 - t/√(1+t²) ≤ 1/t`. -/
theorem one_sub_div_sqrt_le {t : ℝ} (ht : 0 < t) :
    1 - t / Real.sqrt (1 + t ^ 2) ≤ 1 / t := by
  have hs : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hsq : (Real.sqrt (1 + t ^ 2)) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  have hle : t ≤ (Real.sqrt (1 + t ^ 2) + t) * Real.sqrt (1 + t ^ 2) := by
    nlinarith [hsq, sq_nonneg t, Real.sqrt_nonneg (1 + t ^ 2),
      mul_nonneg (Real.sqrt_nonneg (1 + t ^ 2)) (le_of_lt ht)]
  have h1 : 1 - t / Real.sqrt (1 + t ^ 2)
      = (Real.sqrt (1 + t ^ 2) - t) / Real.sqrt (1 + t ^ 2) := by
    rw [eq_div_iff (ne_of_gt hs), sub_mul, one_mul, div_mul_cancel₀ t (ne_of_gt hs)]
  rw [h1]
  have h2 : Real.sqrt (1 + t ^ 2) - t = 1 / (Real.sqrt (1 + t ^ 2) + t) := by
    rw [eq_div_iff (by positivity)]
    nlinarith [hsq]
  rw [h2, div_div]
  exact one_div_le_one_div_of_le ht hle

/-- The sigmoid chart is odd about `(1/2, 1/2)`: `c (-u) = 1 - c u`. -/
theorem cubeCoord_neg_val (u : ℝ) :
    (1 + (-u) / Real.sqrt (1 + (-u) ^ 2)) / 2
      = 1 - (1 + u / Real.sqrt (1 + u ^ 2)) / 2 := by
  have h : Real.sqrt (1 + (-u) ^ 2) = Real.sqrt (1 + u ^ 2) := by
    rw [show (1 : ℝ) + (-u) ^ 2 = 1 + u ^ 2 by ring]
  rw [h]
  have hs : Real.sqrt (1 + u ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  field_simp
  ring

/-- For `t > 0` the sigmoid is within `1/(2t)` of `1`. -/
theorem one_sub_half_le {t : ℝ} (ht : 0 < t) :
    1 - (1 + t / Real.sqrt (1 + t ^ 2)) / 2 ≤ 1 / (2 * t) := by
  have h := one_sub_div_sqrt_le ht
  have h2 : (1 - (1 + t / Real.sqrt (1 + t ^ 2)) / 2) * (2 * t)
      = (1 - t / Real.sqrt (1 + t ^ 2)) * t := by ring
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * t), h2]
  have h4 : (1 - t / Real.sqrt (1 + t ^ 2)) * t ≤ (1 / t) * t :=
    mul_le_mul_of_nonneg_right h (le_of_lt ht)
  rwa [div_mul_cancel₀ 1 (ne_of_gt ht)] at h4

/-- For `t < 0` the sigmoid is within `1/(2|t|)` of `0`. -/
theorem half_le_of_neg {t : ℝ} (ht : t < 0) :
    (1 + t / Real.sqrt (1 + t ^ 2)) / 2 ≤ 1 / (2 * |t|) := by
  have hpos : 0 < |t| := abs_pos.mpr (ne_of_lt ht)
  have h := one_sub_half_le hpos
  have h2 : (1 + t / Real.sqrt (1 + t ^ 2)) / 2
      = 1 - (1 + |t| / Real.sqrt (1 + |t| ^ 2)) / 2 := by
    have h3 := cubeCoord_neg_val |t|
    have h4 : -|t| = t := by rw [abs_of_neg ht, neg_neg]
    rwa [h4] at h3
  rwa [h2]

/-! ## The coordinate bound for `EuclideanSpace` -/

/-- If all coordinates of `z : ℝ^n` are `< A` in absolute value then `‖z‖ < A √n`. -/
theorem norm_lt_mul_sqrt_card {n : ℕ} (hn : 0 < n) {A : ℝ} (hA : 0 < A)
    {z : EuclideanSpace ℝ (Fin n)} (hz : ∀ i, |z i| < A) : ‖z‖ < A * Real.sqrt n := by
  have hsq : ‖z‖ ^ 2 = ∑ i : Fin n, (z i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have hlt : (∑ i : Fin n, (z i) ^ 2) < ∑ _ : Fin n, A ^ 2 := by
    refine Finset.sum_lt_sum_of_nonempty ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i _ => ?_)
    rw [sq_lt_sq, abs_of_pos hA]
    exact hz i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
  rw [← hsq] at hlt
  have hsqrt : ‖z‖ < Real.sqrt ((n : ℝ) * A ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg z)]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hlt
  rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq (le_of_lt hA), mul_comm] at hsqrt

/-! ## The uniform strip around the boundary of the cube -/

/-- If `W ⊆ I^n` is open and contains the boundary of the cube, then for every coordinate `i` there
is `δ > 0` such that every `y ∉ W` has `δ < y i < 1 - δ`.  (Compactness of `Wᶜ`.) -/
theorem exists_coord_strip {n : ℕ} {W : Set (Fin n → Set.Icc (0 : ℝ) 1)}
    (hW : IsOpen W) (hbd : _root_.Cube.boundary (Fin n) ⊆ W) (i : Fin n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : Fin n → Set.Icc (0 : ℝ) 1,
      y ∉ W → δ < (y i : ℝ) ∧ (y i : ℝ) < 1 - δ := by
  have hK : IsCompact (Wᶜ : Set (Fin n → Set.Icc (0 : ℝ) 1)) := hW.isClosed_compl.isCompact
  have hcont : Continuous (fun y : Fin n → Set.Icc (0 : ℝ) 1 => (y i : ℝ)) :=
    continuous_subtype_val.comp (continuous_apply i)
  have hcomp : IsCompact ((fun y : Fin n → Set.Icc (0 : ℝ) 1 => (y i : ℝ)) '' Wᶜ) :=
    hK.image hcont
  have hsub : ((fun y : Fin n → Set.Icc (0 : ℝ) 1 => (y i : ℝ)) '' Wᶜ)
      ⊆ Set.Ioo (0 : ℝ) 1 := by
    rintro v ⟨y, hyW, rfl⟩
    have hyb : y ∉ _root_.Cube.boundary (Fin n) := fun h => hyW (hbd h)
    simp only [_root_.Cube.boundary, Set.mem_setOf_eq, not_exists, not_or] at hyb
    have hy0 : (0 : ℝ) ≤ (y i : ℝ) := (y i).2.1
    have hy1 : (y i : ℝ) ≤ 1 := (y i).2.2
    have hne0 : (y i : ℝ) ≠ 0 := fun h => (hyb i).1 (Subtype.ext h)
    have hne1 : (y i : ℝ) ≠ 1 := fun h => (hyb i).2 (Subtype.ext h)
    exact ⟨lt_of_le_of_ne hy0 (Ne.symm hne0), lt_of_le_of_ne hy1 hne1⟩
  obtain ⟨δ, hδpos, hδsub⟩ := hcomp.exists_thickening_subset_open isOpen_Ioo hsub
  refine ⟨δ / 2, by positivity, fun y hyW => ?_⟩
  have hyv : (y i : ℝ) ∈ ((fun y : Fin n → Set.Icc (0 : ℝ) 1 => (y i : ℝ)) '' Wᶜ) :=
    ⟨y, hyW, rfl⟩
  constructor
  · by_contra hcon
    push_neg at hcon
    have hmem : (0 : ℝ) ∈ Metric.thickening δ
        ((fun y : Fin n → Set.Icc (0 : ℝ) 1 => (y i : ℝ)) '' Wᶜ) := by
      rw [Metric.mem_thickening_iff]
      exact ⟨(y i : ℝ), hyv, by
        rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (y i).2.1]; linarith⟩
    exact absurd (hδsub hmem).1 (lt_irrefl 0)
  · by_contra hcon
    push_neg at hcon
    have hmem : (1 : ℝ) ∈ Metric.thickening δ
        ((fun y : Fin n → Set.Icc (0 : ℝ) 1 => (y i : ℝ)) '' Wᶜ) := by
      rw [Metric.mem_thickening_iff]
      exact ⟨(y i : ℝ), hyv, by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [(y i).2.2] : (0 : ℝ) ≤ 1 - (y i : ℝ))]
        linarith⟩
    exact absurd (hδsub hmem).2 (lt_irrefl 1)

/-! ## The far behaviour of the cube chart -/

/-- **The cube chart tends to the boundary of the cube at infinity.**  If `W ⊆ I^n` (`n > 0`) is
open and contains the combinatorial boundary of the cube, then `cubeCoord n z ∈ W` for all `z` of
sufficiently large norm. -/
theorem cubeCoord_eventually_mem {n : ℕ} (hn : 0 < n)
    {W : Set (Fin n → Set.Icc (0 : ℝ) 1)} (hW : IsOpen W)
    (hbd : _root_.Cube.boundary (Fin n) ⊆ W) :
    ∃ R : ℝ, ∀ z : EuclideanSpace ℝ (Fin n), R ≤ ‖z‖ → cubeCoord n z ∈ W := by
  choose δ hδpos hδb using fun i => exists_coord_strip hW hbd i
  have hApos : 0 < (∑ i : Fin n, (δ i)⁻¹) + 1 := by
    have h : 0 ≤ ∑ i : Fin n, (δ i)⁻¹ :=
      Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (le_of_lt (hδpos i)))
    linarith
  refine ⟨((∑ i : Fin n, (δ i)⁻¹) + 1) * Real.sqrt n, fun z hz => ?_⟩
  by_contra hzW
  have hex : ∃ i : Fin n, (∑ j : Fin n, (δ j)⁻¹) + 1 ≤ |z i| := by
    by_contra hcon
    push_neg at hcon
    have hlt := norm_lt_mul_sqrt_card hn hApos (z := z) hcon
    linarith
  obtain ⟨i, hi⟩ := hex
  have hle : (δ i)⁻¹ ≤ |z i| :=
    le_trans (le_trans (Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin n => (δ j)⁻¹)
      (fun j _ => inv_nonneg.mpr (le_of_lt (hδpos j))) (Finset.mem_univ i)) (by linarith)) hi
  have hmul : 1 ≤ δ i * |z i| := by
    have h := mul_le_mul_of_nonneg_left hle (le_of_lt (hδpos i))
    rwa [mul_inv_cancel₀ (ne_of_gt (hδpos i))] at h
  have hzi : z i ≠ 0 := by
    intro h0
    have hle0 : (δ i)⁻¹ ≤ 0 := by simpa [h0] using hle
    have := hδpos i
    have := inv_pos.mpr this
    linarith
  have hkey := hδb i (cubeCoord n z) hzW
  rcases lt_or_gt_of_ne hzi with hneg | hpos
  · have h1 : (cubeCoord n z i : ℝ) ≤ 1 / (2 * |z i|) := by
      rw [cubeCoord_apply_coe]
      exact half_le_of_neg hneg
    have h2 : 1 / (2 * |z i|) < δ i := by
      rw [div_lt_iff₀ (by positivity)]
      have hpos' : 0 < |z i| := abs_pos.mpr hzi
      nlinarith [hmul, hpos']
    linarith [hkey.1]
  · have h1 : 1 - (cubeCoord n z i : ℝ) ≤ 1 / (2 * z i) := by
      rw [cubeCoord_apply_coe]
      exact one_sub_half_le hpos
    have h2 : 1 / (2 * z i) < δ i := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [hmul, hpos, abs_of_pos hpos]
    linarith [hkey.2]

end Far

/-! ## The statement -/

theorem exists_tailBound_flatSourceHomotopy_notMem {k n : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    (H : C(Work.PTGeometric.SourceModel n, D.T))
    (φ : C(Fin n → Set.Icc (0 : ℝ) 1, Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (y₀ : Fin n → Set.Icc (0 : ℝ) 1) (hy₀ : y₀ ∈ _root_.Cube.boundary (Fin n))
    (hbd : ∀ y ∈ _root_.Cube.boundary (Fin n), φ y = φ y₀)
    (ht : ∀ τ : Set.Icc (1 : ℝ) 2, H (φ y₀, τ) = D.t₀)
    (core : Set D.T) (hclosed : IsClosed core) (ht0 : D.t₀ ∉ core) :
    ∃ R : ℝ, ∀ x : EuclideanSpace ℝ (Fin (n + 1)), R ≤ ‖Work.PTGeometric.tail n x‖ →
      Work.PTGeometric.flatSourceHomotopy (k := k) n H φ x ∉ core := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- `Fin 0` carries no coordinate, so the cube has no boundary at all
    subst hn0
    obtain ⟨i, -⟩ := hy₀
    exact i.elim0
  · -- the open neighbourhood of `φ y₀` on which `H` avoids `core`
    have hpre : IsOpen (H ⁻¹' coreᶜ) := by
      simpa only [Set.preimage_compl] using (hclosed.preimage H.continuous).isOpen_compl
    have hsub : ({φ y₀} : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) ×ˢ
        (Set.univ : Set (Set.Icc (1 : ℝ) 2)) ⊆ H ⁻¹' coreᶜ := by
      rintro ⟨z, τ⟩ ⟨hz, -⟩
      rw [Set.mem_singleton_iff] at hz
      subst hz
      change H (φ y₀, τ) ∉ core
      rw [ht τ]
      exact ht0
    obtain ⟨u, v, hu, hv, hsu, huv, huvsub⟩ :=
      generalized_tube_lemma (isCompact_singleton (x := φ y₀)) isCompact_univ hpre hsub
    have hpu : φ y₀ ∈ u := hsu rfl
    have hW : IsOpen (φ ⁻¹' u) := hu.preimage φ.continuous
    have hbdW : _root_.Cube.boundary (Fin n) ⊆ φ ⁻¹' u := by
      intro y hy
      show φ y ∈ u
      rw [hbd y hy]
      exact hpu
    obtain ⟨R, hR⟩ := Far.cubeCoord_eventually_mem hnpos hW hbdW
    refine ⟨R, fun x hx => ?_⟩
    have h1 : φ (cubeCoord n (tail n x)) ∈ u := hR (tail n x) hx
    have h2 : (φ (cubeCoord n (tail n x)), srcTime n x) ∈ u ×ˢ v :=
      ⟨h1, huv (Set.mem_univ _)⟩
    exact huvsub h2

end

end Work.PTGeometric
