import Mathlib
import Submission.Work.RatHurewicz.avoidAux

/-!
# The punctured relative interior of a face of the standard simplex is path connected

Area **RATHUREWICZ**.  The relative interior of the face of `Δ^{m+1} = stdSimplex ℝ (Fin (m+2))`
spanned by a finite set `S` of vertices is the set of points whose support (`suppOf`, the set of
non-zero coordinates) is exactly `S`.  In dimension `≥ 2` (i.e. `3 ≤ S.card`) this relative interior
is path connected, and therefore so is its intersection with any ball around one of its points,
with that point removed.

The proof reduces to the elementary Euclidean statement that a relatively open convex subset of an
affine subspace of dimension `≥ 2`, with one point removed, is path connected
(`isPathConnected_relOpen_convex_diff`).  The reduction uses the chart `v ↦ v - x₀` of the face,
whose direction space is `faceDir m S`.
-/

open scoped Topology
open Set Metric

namespace Work.RatHurewicz

noncomputable section

/-! ### A relatively open convex set minus one of its points is path connected -/

/-- **A relatively open convex set minus one of its points, in relative dimension `≥ 2`, is path
connected.**  Here `M` is the direction space of the affine subspace `u + M` containing `U`,
`hopen` expresses that `U` is open in `u + M`, and `h2` says that `M` has dimension `≥ 2`.

The proof uses the sphere of radius `ρ/2` around `u` inside the affine subspace: it is path
connected (it is the image of the sphere of a normed space of dimension `≥ 2`), it is contained in
`U \ {u}`, and every point of `U \ {u}` is joined to it by a segment of the convex set `U`, which
avoids `u` because the segment lies on a ray leaving `u` at positive distance. -/
theorem isPathConnected_relOpen_convex_diff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Submodule ℝ E} {u : E} {U : Set E}
    (hsub : U ⊆ {z : E | z - u ∈ M})
    (hconv : Convex ℝ U)
    (hu : u ∈ U)
    (hopen : ∀ x ∈ U, ∃ r > 0, ∀ z : E, z - u ∈ M → dist z x < r → z ∈ U)
    (h2 : ∃ f : Fin 2 → M, LinearIndependent ℝ f) :
    IsPathConnected (U \ {u}) := by
  have hrank : 1 < Module.rank ℝ M := by
    have h : ((2 : ℕ) : Cardinal) ≤ Module.rank ℝ M := Module.le_rank_iff.mpr h2
    exact lt_of_lt_of_le (by norm_num) h
  obtain ⟨ρ, hρ, hρU⟩ := hopen u hu
  set r : ℝ := ρ / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  have hsphere : IsPathConnected ((fun Z : M => u + (Z : E)) '' Metric.sphere (0 : M) r) :=
    (isPathConnected_sphere hrank (0 : M) hr.le).image
      (continuous_const.add continuous_subtype_val)
  have himg : (fun Z : M => u + (Z : E)) '' Metric.sphere (0 : M) r
      = {z : E | z - u ∈ M ∧ dist z u = r} := by
    ext z
    constructor
    · rintro ⟨Z, hZ, rfl⟩
      refine ⟨by simpa using Z.2, ?_⟩
      rw [dist_eq_norm, add_sub_cancel_left]
      simpa [dist_eq_norm] using hZ
    · rintro ⟨hzM, hzr⟩
      refine ⟨⟨z - u, hzM⟩, ?_, by simp⟩
      rw [mem_sphere, dist_eq_norm, sub_zero]
      simpa [dist_eq_norm] using hzr
  have hSconn : IsPathConnected {z : E | z - u ∈ M ∧ dist z u = r} := by
    rw [← himg]; exact hsphere
  have hSU : {z : E | z - u ∈ M ∧ dist z u = r} ⊆ U \ {u} := by
    rintro z ⟨hzM, hzr⟩
    refine ⟨hρU z hzM ?_, ?_⟩
    · rw [hzr, hrdef]; linarith
    · intro hzu
      rw [hzu, dist_self] at hzr
      exact hr.ne' hzr.symm
  have hPmem : ∀ x ∈ U \ {u}, (u + (r / dist x u) • (x - u)) ∈
      {z : E | z - u ∈ M ∧ dist z u = r} := by
    intro x hx
    obtain ⟨hxU, hxu⟩ := hx
    have hxu' : x ≠ u := by simpa using hxu
    have hdx : 0 < dist x u := dist_pos.mpr hxu'
    have hxdn : dist x u = ‖x - u‖ := dist_eq_norm x u
    refine ⟨?_, ?_⟩
    · show (u + (r / dist x u) • (x - u)) - u ∈ M
      rw [add_sub_cancel_left]
      exact M.smul_mem _ (hsub hxU)
    · rw [dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg (le_of_lt (div_pos hr hdx)), hxdn]
      rw [div_mul_cancel₀ r (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxu'))]
  have hPseg : ∀ x ∈ U \ {u}, JoinedIn (U \ {u}) x (u + (r / dist x u) • (x - u)) := by
    intro x hx
    have hxS : (u + (r / dist x u) • (x - u)) ∈ U \ {u} := hSU (hPmem x hx)
    obtain ⟨hxU, hxu⟩ := hx
    have hxu' : x ≠ u := by simpa using hxu
    have hdx : 0 < dist x u := dist_pos.mpr hxu'
    refine JoinedIn.of_segment_subset fun z hz => ⟨hconv.segment_subset hxU hxS.1 hz, ?_⟩
    intro hzu
    rw [segment_eq_image] at hz
    obtain ⟨θ, hθ, hθz⟩ := hz
    rw [hzu] at hθz
    have hcoef : 0 < (1 - θ) + θ * (r / dist x u) := by
      have hr' : 0 < r / dist x u := div_pos hr hdx
      have hm : 0 < min 1 (r / dist x u) := lt_min_iff.mpr ⟨one_pos, hr'⟩
      have hm1 : min 1 (r / dist x u) ≤ 1 := min_le_left _ _
      have hm2 : min 1 (r / dist x u) ≤ r / dist x u := min_le_right _ _
      calc (1 - θ) + θ * (r / dist x u) = (1 - θ) * 1 + θ * (r / dist x u) := by ring
        _ ≥ (1 - θ) * min 1 (r / dist x u) + θ * min 1 (r / dist x u) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left hm1 (by linarith [hθ.1, hθ.2])
              · exact mul_le_mul_of_nonneg_left hm2 hθ.1
        _ = min 1 (r / dist x u) := by ring
        _ > 0 := hm
    have hkey : ((1 - θ) + θ * (r / dist x u)) • (x - u) = 0 := by
      have h1 : (1 - θ) • x + θ • (u + (r / dist x u) • (x - u))
          = u + ((1 - θ) + θ * (r / dist x u)) • (x - u) := by
        module
      have h2 : u + ((1 - θ) + θ * (r / dist x u)) • (x - u) = u := by rw [← h1]; exact hθz
      have h3 := congrArg (fun w : E => w - u) h2
      simpa using h3
    have hxu0 : x - u = 0 := by
      rcases smul_eq_zero.mp hkey with h | h
      · exact absurd h (ne_of_gt hcoef)
      · exact h
    exact sub_ne_zero.mpr hxu' hxu0
  rw [isPathConnected_iff]
  refine ⟨hSconn.nonempty.mono hSU, ?_⟩
  intro x hx y hy
  exact (hPseg x hx).trans
    (((hSconn.joinedIn (u + (r / dist x u) • (x - u)) (hPmem x hx)
      (u + (r / dist y u) • (y - u)) (hPmem y hy)).mono hSU).trans (hPseg y hy).symm)

/-! ### The face of the standard simplex -/

/-- The space of directions tangent to the face of `stdSimplex ℝ (Fin (m+2))` spanned by `S`:
the vectors vanishing outside `S` and whose sum vanishes. -/
def faceDir (m : ℕ) (S : Finset (Fin (m + 2))) : Submodule ℝ (Fin (m + 2) → ℝ) where
  carrier := {v | (∀ i ∉ S, v i = 0) ∧ ∑ i, v i = 0}
  add_mem' := by
    intro a b ha hb
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [Pi.add_apply, ha.1 i hi, hb.1 i hi, add_zero]
    · have h : ∑ i, (a + b) i = ∑ i, (a i + b i) :=
        Finset.sum_congr rfl fun i _ => Pi.add_apply a b i
      rw [h, Finset.sum_add_distrib, ha.2, hb.2, add_zero]
  zero_mem' := by
    refine ⟨fun i _ => rfl, ?_⟩
    simp
  smul_mem' := by
    intro c a ha
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [Pi.smul_apply, ha.1 i hi, smul_eq_mul, mul_zero]
    · have h : ∑ i, (c • a) i = ∑ i, c * a i :=
        Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul]
      rw [h, ← Finset.mul_sum, ha.2, mul_zero]

theorem mem_faceDir {m : ℕ} {S : Finset (Fin (m + 2))} {v : Fin (m + 2) → ℝ} :
    v ∈ faceDir m S ↔ (∀ i ∉ S, v i = 0) ∧ ∑ i, v i = 0 := Iff.rfl

/-- The elementary sum-zero vector `e_a - e_b` inside `faceDir m S` (for `a, b ∈ S`). -/
def faceVec (m : ℕ) (a b : Fin (m + 2)) : Fin (m + 2) → ℝ := Pi.single a 1 - Pi.single b 1

/-- The relatively open set inside the face: points of the face spanned by `S` whose distance to
`u` is `< ε`, with strictly positive `S`-coordinates. -/
def faceU {m : ℕ} (S : Finset (Fin (m + 2))) (u : Fin (m + 2) → ℝ) (ε : ℝ) :
    Set (Fin (m + 2) → ℝ) :=
  {v | (∀ i ∈ S, 0 < v i) ∧ (∀ i ∉ S, v i = 0) ∧ (∑ i, v i = 1) ∧ dist v u < ε}

theorem mem_faceU {m : ℕ} {S : Finset (Fin (m + 2))} {u : Fin (m + 2) → ℝ} {ε : ℝ}
    {v : Fin (m + 2) → ℝ} :
    v ∈ faceU S u ε ↔
      (∀ i ∈ S, 0 < v i) ∧ (∀ i ∉ S, v i = 0) ∧ (∑ i, v i = 1) ∧ dist v u < ε := Iff.rfl

/-- For a point of the standard simplex, "support `S`" means "positive on `S` and vanishing off
`S`". -/
theorem suppOf_eq_iff {m : ℕ} {S : Finset (Fin (m + 2))} (x : stdSimplex ℝ (Fin (m + 2))) :
    suppOf x = S ↔ (∀ i ∈ S, 0 < (x : Fin (m + 2) → ℝ) i) ∧
      (∀ i ∉ S, (x : Fin (m + 2) → ℝ) i = 0) := by
  constructor
  · intro h
    constructor
    · intro i hi
      have hne : (x : Fin (m + 2) → ℝ) i ≠ 0 := mem_suppOf.mp (h ▸ hi)
      exact lt_of_le_of_ne (x.2.1 i) (Ne.symm hne)
    · intro i hi
      by_contra hne
      exact hi (h ▸ mem_suppOf.mpr hne)
  · rintro ⟨hpos, hzero⟩
    ext i
    rw [mem_suppOf]
    constructor
    · intro hne
      by_contra hi
      exact hne (hzero i hi)
    · intro hi
      exact ne_of_gt (hpos i hi)

theorem faceU_subset_simplex {m : ℕ} {S : Finset (Fin (m + 2))} {u : Fin (m + 2) → ℝ}
    {ε : ℝ} : faceU S u ε ⊆ stdSimplex ℝ (Fin (m + 2)) := by
  intro v hv
  obtain ⟨hpos, hzero, hsum, -⟩ := mem_faceU.mp hv
  exact ⟨fun i => by
    by_cases hi : i ∈ S
    · exact le_of_lt (hpos i hi)
    · rw [hzero i hi], hsum⟩

theorem convex_faceU {m : ℕ} {S : Finset (Fin (m + 2))} {u : Fin (m + 2) → ℝ} {ε : ℝ}
    (_hε : 0 < ε) : Convex ℝ (faceU S u ε) := by
  intro v hv w hw a b ha hb hab
  obtain ⟨hv1, hv2, hv3, hv4⟩ := mem_faceU.mp hv
  obtain ⟨hw1, hw2, hw3, hw4⟩ := mem_faceU.mp hw
  refine mem_faceU.mpr ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    have hcoe : (a • v + b • w) i = a * v i + b * w i := by
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [hcoe]
    rcases eq_or_lt_of_le ha with h | h
    · rw [← h, zero_mul, zero_add]
      have hb1 : b = 1 := by linarith
      rw [hb1, one_mul]
      exact hw1 i hi
    · exact add_pos_of_pos_of_nonneg (mul_pos h (hv1 i hi)) (mul_nonneg hb (le_of_lt (hw1 i hi)))
  · intro i hi
    have hcoe : (a • v + b • w) i = a * v i + b * w i := by
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [hcoe, hv2 i hi, hw2 i hi, mul_zero, mul_zero, add_zero]
  · have hsum : ∑ i, (a • v + b • w) i = a * ∑ i, v i + b * ∑ i, w i := by
      have h1 : ∑ i, (a • v + b • w) i = ∑ i, (a * v i + b * w i) :=
        Finset.sum_congr rfl fun i _ => by
          rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
      rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hsum, hv3, hw3, mul_one, mul_one, hab]
  · exact mem_ball.mp (convex_ball u ε (mem_ball.mpr hv4) (mem_ball.mpr hw4) ha hb hab)

theorem faceU_sub_faceDir {m : ℕ} {S : Finset (Fin (m + 2))} {x₀ : stdSimplex ℝ (Fin (m + 2))}
    (hx₀ : suppOf x₀ = S) {ε : ℝ} :
    faceU S (x₀ : Fin (m + 2) → ℝ) ε ⊆ {z : Fin (m + 2) → ℝ | z - x₀ ∈ faceDir m S} := by
  have hx0zero : ∀ i ∉ S, (x₀ : Fin (m + 2) → ℝ) i = 0 := by
    intro i hi
    by_contra hne
    exact hi (hx₀ ▸ mem_suppOf.mpr hne)
  intro v hv
  obtain ⟨hv1, hv2, hv3, hv4⟩ := mem_faceU.mp hv
  show v - (x₀ : Fin (m + 2) → ℝ) ∈ faceDir m S
  rw [mem_faceDir]
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [Pi.sub_apply, hv2 i hi, hx0zero i hi, sub_zero]
  · have h : ∑ i, (v - (x₀ : Fin (m + 2) → ℝ)) i
        = ∑ i, v i - ∑ i, (x₀ : Fin (m + 2) → ℝ) i := by
      rw [show (∑ i, (v - (x₀ : Fin (m + 2) → ℝ)) i)
          = ∑ i, (v i - (x₀ : Fin (m + 2) → ℝ) i) from
        Finset.sum_congr rfl fun i _ => rfl]
      rw [Finset.sum_sub_distrib]
    have hx0sum : ∑ i, (x₀ : Fin (m + 2) → ℝ) i = 1 := x₀.2.2
    rw [h, hv3, hx0sum, sub_self]

theorem faceU_relOpen {m : ℕ} {S : Finset (Fin (m + 2))} {x₀ : stdSimplex ℝ (Fin (m + 2))}
    (hx₀ : suppOf x₀ = S) {ε : ℝ} :
    ∀ x ∈ faceU S (x₀ : Fin (m + 2) → ℝ) ε, ∃ r > 0, ∀ z : Fin (m + 2) → ℝ,
      z - (x₀ : Fin (m + 2) → ℝ) ∈ faceDir m S → dist z x < r →
        z ∈ faceU S (x₀ : Fin (m + 2) → ℝ) ε := by
  have hx0zero : ∀ i ∉ S, (x₀ : Fin (m + 2) → ℝ) i = 0 := by
    intro i hi
    by_contra hne
    exact hi (hx₀ ▸ mem_suppOf.mpr hne)
  have hV0 : IsOpen ({z : Fin (m + 2) → ℝ | ∀ i ∈ S, 0 < z i} ∩
      ball (x₀ : Fin (m + 2) → ℝ) ε) := by
    refine IsOpen.inter ?_ isOpen_ball
    rw [show {z : Fin (m + 2) → ℝ | ∀ i ∈ S, 0 < z i}
        = ⋂ i ∈ S, {z : Fin (m + 2) → ℝ | 0 < z i} by ext z; simp]
    exact isOpen_biInter_finset fun i _ => isOpen_lt continuous_const (continuous_apply i)
  intro x hx
  obtain ⟨hx1, hx2, hx3, hx4⟩ := mem_faceU.mp hx
  have hxV : x ∈ ({z : Fin (m + 2) → ℝ | ∀ i ∈ S, 0 < z i} ∩
      ball (x₀ : Fin (m + 2) → ℝ) ε) := ⟨hx1, mem_ball.mpr hx4⟩
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (hV0.mem_nhds hxV)
  refine ⟨r, hr, fun z hzM hzd => ?_⟩
  obtain ⟨hzpos, hzball⟩ := hrsub (mem_ball.mpr hzd)
  refine mem_faceU.mpr ⟨hzpos, fun i hi => ?_, ?_, mem_ball.mp hzball⟩
  · have h := (mem_faceDir.mp hzM).1 i hi
    rwa [Pi.sub_apply, hx0zero i hi, sub_zero] at h
  · have hsum := (mem_faceDir.mp hzM).2
    have h : ∑ i, (z - (x₀ : Fin (m + 2) → ℝ)) i
        = ∑ i, z i - ∑ i, (x₀ : Fin (m + 2) → ℝ) i := by
      rw [show (∑ i, (z - (x₀ : Fin (m + 2) → ℝ)) i)
          = ∑ i, (z i - (x₀ : Fin (m + 2) → ℝ) i) from
        Finset.sum_congr rfl fun i _ => rfl]
      rw [Finset.sum_sub_distrib]
    have hx0sum : ∑ i, (x₀ : Fin (m + 2) → ℝ) i = 1 := x₀.2.2
    rw [h, hx0sum] at hsum
    linarith

theorem mem_faceU_self {m : ℕ} {S : Finset (Fin (m + 2))} {x₀ : stdSimplex ℝ (Fin (m + 2))}
    (hx₀ : suppOf x₀ = S) {ε : ℝ} (hε : 0 < ε) :
    (x₀ : Fin (m + 2) → ℝ) ∈ faceU S (x₀ : Fin (m + 2) → ℝ) ε := by
  obtain ⟨hpos, hzero⟩ := (suppOf_eq_iff x₀).mp hx₀
  exact mem_faceU.mpr ⟨hpos, hzero, x₀.2.2, by rw [dist_self]; exact hε⟩

/-- The direction space of the face spanned by `S` has dimension `≥ 2` when `3 ≤ S.card`: the two
vectors `e_A - e_B` and `e_A - e_C` for three distinct vertices `A, B, C ∈ S` are independent. -/
theorem exists_linearIndependent_pair_faceDir {m : ℕ} {S : Finset (Fin (m + 2))}
    (hS : 3 ≤ S.card) : ∃ f : Fin 2 → faceDir m S, LinearIndependent ℝ f := by
  have h0 : (0 : ℕ) < S.card := by omega
  have h1 : (1 : ℕ) < S.card := by omega
  have h2 : (2 : ℕ) < S.card := by omega
  set A : Fin (m + 2) := (S.equivFin.symm ⟨0, h0⟩ : ↥S).1 with hAdef
  set B : Fin (m + 2) := (S.equivFin.symm ⟨1, h1⟩ : ↥S).1 with hBdef
  set C : Fin (m + 2) := (S.equivFin.symm ⟨2, h2⟩ : ↥S).1 with hCdef
  have hAS : A ∈ S := (S.equivFin.symm ⟨0, h0⟩ : ↥S).2
  have hBS : B ∈ S := (S.equivFin.symm ⟨1, h1⟩ : ↥S).2
  have hCS : C ∈ S := (S.equivFin.symm ⟨2, h2⟩ : ↥S).2
  have hAB : A ≠ B := by
    intro h
    have h' : (S.equivFin.symm ⟨0, h0⟩ : ↥S) = S.equivFin.symm ⟨1, h1⟩ := Subtype.ext h
    have h'' := congrArg (fun x : ↥S => (S.equivFin x : Fin S.card)) h'
    simp only [Equiv.apply_symm_apply] at h''
    exact absurd (congrArg Fin.val h'') (by norm_num)
  have hac : A ≠ C := by
    intro h
    have h' : (S.equivFin.symm ⟨0, h0⟩ : ↥S) = S.equivFin.symm ⟨2, h2⟩ := Subtype.ext h
    have h'' := congrArg (fun x : ↥S => (S.equivFin x : Fin S.card)) h'
    simp only [Equiv.apply_symm_apply] at h''
    exact absurd (congrArg Fin.val h'') (by norm_num)
  have hbc : B ≠ C := by
    intro h
    have h' : (S.equivFin.symm ⟨1, h1⟩ : ↥S) = S.equivFin.symm ⟨2, h2⟩ := Subtype.ext h
    have h'' := congrArg (fun x : ↥S => (S.equivFin x : Fin S.card)) h'
    simp only [Equiv.apply_symm_apply] at h''
    exact absurd (congrArg Fin.val h'') (by norm_num)
  have hV1 : faceVec m A B ∈ faceDir m S := by
    rw [mem_faceDir]
    refine ⟨fun i hi => ?_, ?_⟩
    · have h1 : ¬ (i = A) := by intro h; exact hi (h.symm ▸ hAS)
      have h2 : ¬ (i = B) := by intro h; exact hi (h.symm ▸ hBS)
      rw [faceVec, Pi.sub_apply, Pi.single_eq_of_ne (M := fun _ => ℝ) h1 (1 : ℝ),
        Pi.single_eq_of_ne (M := fun _ => ℝ) h2 (1 : ℝ), sub_zero]
    · have h : ∑ i, faceVec m A B i
          = ∑ i, Pi.single A (1 : ℝ) i - ∑ i, Pi.single B (1 : ℝ) i := by
        rw [show (∑ i : Fin (m + 2), faceVec m A B i)
            = ∑ i, (Pi.single A (1 : ℝ) i - Pi.single B (1 : ℝ) i) from
          Finset.sum_congr rfl fun i _ => rfl]
        rw [Finset.sum_sub_distrib]
      rw [h]
      simp
  have hV2 : faceVec m A C ∈ faceDir m S := by
    rw [mem_faceDir]
    refine ⟨fun i hi => ?_, ?_⟩
    · have h1 : ¬ (i = A) := by intro h; exact hi (h.symm ▸ hAS)
      have h2 : ¬ (i = C) := by intro h; exact hi (h.symm ▸ hCS)
      rw [faceVec, Pi.sub_apply, Pi.single_eq_of_ne (M := fun _ => ℝ) h1 (1 : ℝ),
        Pi.single_eq_of_ne (M := fun _ => ℝ) h2 (1 : ℝ), sub_zero]
    · have h : ∑ i, faceVec m A C i
          = ∑ i, Pi.single A (1 : ℝ) i - ∑ i, Pi.single C (1 : ℝ) i := by
        rw [show (∑ i : Fin (m + 2), faceVec m A C i)
            = ∑ i, (Pi.single A (1 : ℝ) i - Pi.single C (1 : ℝ) i) from
          Finset.sum_congr rfl fun i _ => rfl]
        rw [Finset.sum_sub_distrib]
      rw [h]
      simp
  refine ⟨![(⟨faceVec m A B, hV1⟩ : faceDir m S), ⟨faceVec m A C, hV2⟩], ?_⟩
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have h1 : (faceVec m A C) C = 0 := by
      have hc := congrArg (fun v : faceDir m S => (v : Fin (m + 2) → ℝ) C) h
      simpa [Matrix.cons_val_one] using hc
    have h2 : (faceVec m A C) C = -1 := by simp [faceVec, Pi.sub_apply, hac.symm]
    rw [h2] at h1
    norm_num at h1
  · intro a h
    have h1 : a * (faceVec m A C) B = (faceVec m A B) B := by
      have hc := congrArg (fun v : faceDir m S => (v : Fin (m + 2) → ℝ) B) h
      simpa [Submodule.coe_smul, Pi.smul_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
        using hc
    have h2 : (faceVec m A C) B = 0 := by simp [faceVec, Pi.sub_apply, hAB, hbc]
    have h3 : (faceVec m A B) B = -1 := by simp [faceVec, Pi.sub_apply, hAB]
    rw [h2, h3, mul_zero] at h1
    norm_num at h1

/-! ### The main theorem -/

theorem pathConnected_punctured_simplex {m : ℕ} (S : Finset (Fin (m + 2)))
    (hS : 3 ≤ S.card) (x₀ : stdSimplex ℝ (Fin (m + 2)))
    (hx₀ : Work.RatHurewicz.suppOf x₀ = S)
    {ε : ℝ} (hε : 0 < ε) :
    IsPathConnected (({x | Work.RatHurewicz.suppOf x = S ∧ dist x x₀ < ε} :
        Set (stdSimplex ℝ (Fin (m + 2)))) \ {x₀}) := by
  have hmain : IsPathConnected
      (faceU S (x₀ : Fin (m + 2) → ℝ) ε \ {(x₀ : Fin (m + 2) → ℝ)}) :=
    isPathConnected_relOpen_convex_diff (M := faceDir m S) (u := (x₀ : Fin (m + 2) → ℝ))
      (U := faceU S (x₀ : Fin (m + 2) → ℝ) ε)
      (faceU_sub_faceDir hx₀) (convex_faceU hε) (mem_faceU_self hx₀ hε) (faceU_relOpen hx₀)
      (exists_linearIndependent_pair_faceDir hS)
  have htrans := IsPathConnected.preimage_coe hmain
    (fun v hv => faceU_subset_simplex (u := (x₀ : Fin (m + 2) → ℝ)) (ε := ε) hv.1)
  have hset : (Subtype.val ⁻¹'
        (faceU S (x₀ : Fin (m + 2) → ℝ) ε \ {(x₀ : Fin (m + 2) → ℝ)}))
      = (({x | suppOf x = S ∧ dist x x₀ < ε} : Set (stdSimplex ℝ (Fin (m + 2)))) \ {x₀}) := by
    ext x
    rw [Set.mem_preimage, Set.mem_sdiff, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hxU, hxne⟩
      obtain ⟨h1, h2, -, h4⟩ := mem_faceU.mp hxU
      refine ⟨⟨(suppOf_eq_iff x).mpr ⟨h1, h2⟩, h4⟩, ?_⟩
      intro hx0
      exact hxne (congrArg Subtype.val hx0)
    · rintro ⟨⟨h1, h2⟩, hxne⟩
      obtain ⟨hp, hz⟩ := (suppOf_eq_iff x).mp h1
      refine ⟨mem_faceU.mpr ⟨hp, hz, x.2.2, h2⟩, ?_⟩
      intro h
      exact hxne (Subtype.ext h)
  rw [hset] at htrans
  exact htrans

end

end Work.RatHurewicz
