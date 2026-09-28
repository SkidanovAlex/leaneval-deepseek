import Mathlib
import Submission.Work.Serre.E2dEngine

/-!
# The compression property of the slab pair `(↥(slabU n), ↥(slabU n ∩ ∂I^{n+1}))`

`Work.Serre.compressRel_slabU` is the geometric input of the Mayer–Vietoris step of the `E2(d)`
computation of `Submission/Work/Serre/E2dEngine.lean`: the pair
`(↥(slabU n), {x : ↥(slabU n) | (x : I^{n+1}) ∈ slabU n ∩ ∂I^{n+1}})` has the compression property
in every dimension.

The proof exhibits an explicit strong deformation retraction of the slab
`slabU n = {x ∈ I^{n+1} | x_last < 3/4}` onto its boundary part
`A = (∂Iⁿ × [0,3/4)) ∪ (Iⁿ × {0})`, fixing `A` pointwise, and applies
`Work.Serre.compressRel_of_deformation`.

The retraction is the radial projection from the point `p = (1/2,…,1/2,1)` (the centre of the top
face of the cube, which lies strictly beyond the slab): at time `t` the point `x` is sent to
`p + λ_t (x - p)`, where `λ = 1/γ`, `γ` is the "radial parameter"

  `γ = max (max_{j<n} |2 x_j - 1|) (1 - x_last) ∈ (0,1]`,

and `λ_t = 1 + t (λ - 1) ∈ [1, λ]` interpolates from `x` (at `t = 0`) to the point where the ray
from `p` through `x` leaves the slab (at `t = 1`).  The parameter `γ` equals `1` exactly on `A`,
so points of `A` do not move, and the point reached at time `1` always lies in `A`: either some
coordinate of `x` already attains the maximum `γ` (then the corresponding coordinate of the
end point is `0` or `1`), or `γ = 1 - x_last` (then the last coordinate of the end point is `0`).
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-! ## The elementary geometry of the slab -/

/-- The last coordinate of a point of the slab, as a real number. -/
def slabLast (n : ℕ) (x : ↥(slabU n)) : ℝ := ((x.1 (Fin.last n) : unitInterval) : ℝ)

/-- The `j`-th coordinate (`j < n`) of a point of the slab, as a real number. -/
def slabCoord (n : ℕ) (x : ↥(slabU n)) (j : Fin n) : ℝ :=
  ((x.1 (Fin.castSucc j) : unitInterval) : ℝ)

theorem slabLast_lt (n : ℕ) (x : ↥(slabU n)) : slabLast n x < 3/4 := by
  have h : lastCoord x.1 < 3/4 := x.2
  rw [lastCoord] at h
  exact h

theorem slabLast_nonneg (n : ℕ) (x : ↥(slabU n)) : 0 ≤ slabLast n x :=
  (x.1 (Fin.last n)).2.1

theorem slabLast_le_one (n : ℕ) (x : ↥(slabU n)) : slabLast n x ≤ 1 :=
  (x.1 (Fin.last n)).2.2

theorem one_sub_slabLast_pos (n : ℕ) (x : ↥(slabU n)) : 0 < 1 - slabLast n x := by
  have := slabLast_lt n x
  linarith

theorem one_sub_slabLast_nonneg (n : ℕ) (x : ↥(slabU n)) : 0 ≤ 1 - slabLast n x :=
  le_of_lt (one_sub_slabLast_pos n x)

theorem slabCoord_nonneg (n : ℕ) (x : ↥(slabU n)) (j : Fin n) : 0 ≤ slabCoord n x j :=
  (x.1 (Fin.castSucc j)).2.1

theorem slabCoord_le_one (n : ℕ) (x : ↥(slabU n)) (j : Fin n) : slabCoord n x j ≤ 1 :=
  (x.1 (Fin.castSucc j)).2.2

/-- `Fin (n+1)` is nonempty. -/
theorem slabNonempty (n : ℕ) : (Finset.univ : Finset (Fin (n+1))).Nonempty :=
  ⟨⟨0, Nat.succ_pos n⟩, Finset.mem_univ _⟩

/-- The `i`-th "radial term" of a point of the slab: `1 - x_last` for the last coordinate and
`|2 x_j - 1|` for the others. -/
def slabTerm (n : ℕ) (x : ↥(slabU n)) (i : Fin (n+1)) : ℝ :=
  Fin.lastCases (1 - slabLast n x) (fun j => |2 * slabCoord n x j - 1|) i

/-- The radial parameter of a point of the slab: the maximum of the radial terms `slabTerm`.
It lies in `(0,1]` and equals `1` exactly on the boundary part of the slab. -/
def slabGamma (n : ℕ) (x : ↥(slabU n)) : ℝ :=
  (Finset.univ : Finset (Fin (n+1))).sup' (slabNonempty n) (slabTerm n x)

/-- The reciprocal radial parameter `λ = γ⁻¹ ≥ 1`. -/
def slabLam (n : ℕ) (x : ↥(slabU n)) : ℝ := 1 / slabGamma n x

/-- The time-`t` interpolation parameter `λ_t = 1 + t (λ - 1)`. -/
def slabLamT (n : ℕ) (x : ↥(slabU n)) (t : unitInterval) : ℝ :=
  1 + (t : ℝ) * (slabLam n x - 1)

@[simp] theorem slabTerm_last (n : ℕ) (x : ↥(slabU n)) :
    slabTerm n x (Fin.last n) = 1 - slabLast n x := by
  rw [slabTerm, Fin.lastCases_last]

@[simp] theorem slabTerm_castSucc (n : ℕ) (x : ↥(slabU n)) (j : Fin n) :
    slabTerm n x (Fin.castSucc j) = |2 * slabCoord n x j - 1| := by
  rw [slabTerm, Fin.lastCases_castSucc]

theorem one_sub_slabLast_le_slabGamma (n : ℕ) (x : ↥(slabU n)) :
    1 - slabLast n x ≤ slabGamma n x := by
  have h := Finset.le_sup' (s := (Finset.univ : Finset (Fin (n+1)))) (slabTerm n x)
    (Finset.mem_univ (Fin.last n))
  rw [slabTerm_last] at h
  rwa [slabGamma]

theorem slabGamma_pos (n : ℕ) (x : ↥(slabU n)) : 0 < slabGamma n x :=
  lt_of_lt_of_le (one_sub_slabLast_pos n x) (one_sub_slabLast_le_slabGamma n x)

theorem slabGamma_le_one (n : ℕ) (x : ↥(slabU n)) : slabGamma n x ≤ 1 := by
  rw [slabGamma]
  refine Finset.sup'_le (slabNonempty n) (slabTerm n x) (fun i _ => ?_)
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [slabTerm_castSucc, abs_le]
    constructor
    · have := slabCoord_nonneg n x j; linarith
    · have := slabCoord_le_one n x j; linarith
  · rw [slabTerm_last]
    have := slabLast_nonneg n x
    linarith

theorem abs_slabCoord_le_slabGamma (n : ℕ) (x : ↥(slabU n)) (j : Fin n) :
    |2 * slabCoord n x j - 1| ≤ slabGamma n x := by
  have h := Finset.le_sup' (s := (Finset.univ : Finset (Fin (n+1)))) (slabTerm n x)
    (Finset.mem_univ (Fin.castSucc j))
  rw [slabTerm_castSucc] at h
  rwa [slabGamma]

theorem slabLamT_zero (n : ℕ) (x : ↥(slabU n)) : slabLamT n x 0 = 1 := by
  simp [slabLamT]

theorem slabLamT_one (n : ℕ) (x : ↥(slabU n)) : slabLamT n x 1 = slabLam n x := by
  simp [slabLamT]

theorem one_le_slabLam (n : ℕ) (x : ↥(slabU n)) : 1 ≤ slabLam n x := by
  rw [slabLam, one_le_div (slabGamma_pos n x)]
  exact slabGamma_le_one n x

theorem slabLam_pos (n : ℕ) (x : ↥(slabU n)) : 0 < slabLam n x :=
  lt_of_lt_of_le zero_lt_one (one_le_slabLam n x)

theorem slabLam_mul_slabGamma (n : ℕ) (x : ↥(slabU n)) : slabLam n x * slabGamma n x = 1 := by
  rw [slabLam]
  exact div_mul_cancel₀ 1 (ne_of_gt (slabGamma_pos n x))

theorem slabLam_mul_abs_slabCoord_le_one (n : ℕ) (x : ↥(slabU n)) (j : Fin n) :
    slabLam n x * |2 * slabCoord n x j - 1| ≤ 1 := by
  calc slabLam n x * |2 * slabCoord n x j - 1|
      ≤ slabLam n x * slabGamma n x :=
        mul_le_mul_of_nonneg_left (abs_slabCoord_le_slabGamma n x j) (le_of_lt (slabLam_pos n x))
    _ = 1 := slabLam_mul_slabGamma n x

theorem slabLam_mul_one_sub_slabLast_le_one (n : ℕ) (x : ↥(slabU n)) :
    slabLam n x * (1 - slabLast n x) ≤ 1 := by
  calc slabLam n x * (1 - slabLast n x)
      ≤ slabLam n x * slabGamma n x :=
        mul_le_mul_of_nonneg_left (one_sub_slabLast_le_slabGamma n x) (le_of_lt (slabLam_pos n x))
    _ = 1 := slabLam_mul_slabGamma n x

theorem slabLamT_ge_one (n : ℕ) (x : ↥(slabU n)) (t : unitInterval) : 1 ≤ slabLamT n x t := by
  have ht : (0:ℝ) ≤ (t : ℝ) := t.2.1
  have h : 0 ≤ slabLam n x - 1 := by have := one_le_slabLam n x; linarith
  rw [slabLamT]
  nlinarith

theorem slabLamT_le (n : ℕ) (x : ↥(slabU n)) (t : unitInterval) :
    slabLamT n x t ≤ slabLam n x := by
  have ht : (t : ℝ) ≤ 1 := t.2.2
  have h : 0 ≤ slabLam n x - 1 := by have := one_le_slabLam n x; linarith
  rw [slabLamT]
  nlinarith

theorem slabLamT_nonneg (n : ℕ) (x : ↥(slabU n)) (t : unitInterval) :
    0 ≤ slabLamT n x t := le_trans zero_le_one (slabLamT_ge_one n x t)

theorem abs_slabCoord_sub_half (n : ℕ) (x : ↥(slabU n)) (j : Fin n) :
    |slabCoord n x j - 1/2| = |2 * slabCoord n x j - 1| / 2 := by
  have h : 2 * (slabCoord n x j - 1/2) = 2 * slabCoord n x j - 1 := by ring
  rw [← h, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  ring

/-! ## The deformation -/

/-- The first `n` coordinates of the radial deformation at time `t`. -/
def slabCore (n : ℕ) (x : ↥(slabU n)) (t : unitInterval) : Work.Stems.Cubical.IC n :=
  fun j => ⟨1/2 + slabLamT n x t * (slabCoord n x j - 1/2), by
    have ht1 : 1 ≤ slabLamT n x t := slabLamT_ge_one n x t
    have ht : slabLamT n x t ≤ slabLam n x := slabLamT_le n x t
    have ht0 : 0 ≤ slabLamT n x t := le_trans zero_le_one ht1
    have hcoord : |slabCoord n x j - 1/2| = |2 * slabCoord n x j - 1| / 2 :=
      abs_slabCoord_sub_half n x j
    have hr : slabLam n x * |2 * slabCoord n x j - 1| ≤ 1 :=
      slabLam_mul_abs_slabCoord_le_one n x j
    have hb : |slabLamT n x t * (slabCoord n x j - 1/2)| ≤ 1/2 := by
      rw [abs_mul, abs_of_nonneg ht0, hcoord]
      calc slabLamT n x t * (|2 * slabCoord n x j - 1| / 2)
          ≤ slabLam n x * (|2 * slabCoord n x j - 1| / 2) :=
            mul_le_mul_of_nonneg_right ht (by positivity)
        _ ≤ 1/2 := by linarith
    have hb' := abs_le.mp hb
    exact ⟨by linarith [hb'.1], by linarith [hb'.2]⟩⟩

/-- The last coordinate of the radial deformation at time `t`. -/
def slabLastCoord (n : ℕ) (x : ↥(slabU n)) (t : unitInterval) : unitInterval :=
  ⟨1 - slabLamT n x t * (1 - slabLast n x), by
    have ht1 : 1 ≤ slabLamT n x t := slabLamT_ge_one n x t
    have ht : slabLamT n x t ≤ slabLam n x := slabLamT_le n x t
    have ht0 : 0 ≤ slabLamT n x t := le_trans zero_le_one ht1
    have h1s : 0 ≤ 1 - slabLast n x := one_sub_slabLast_nonneg n x
    have hle : slabLamT n x t * (1 - slabLast n x) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_right ht h1s)
        (slabLam_mul_one_sub_slabLast_le_one n x)
    have hprod : 0 ≤ slabLamT n x t * (1 - slabLast n x) := mul_nonneg ht0 h1s
    exact ⟨by linarith, by linarith⟩⟩

/-- The radial deformation of the slab at time `t`, as a point of `I^{n+1}`. -/
def slabPt (n : ℕ) (x : ↥(slabU n)) (t : unitInterval) : Work.Stems.Cubical.IC (n+1) :=
  Fin.snoc (slabCore n x t) (slabLastCoord n x t)

@[simp] theorem slabPt_castSucc (n : ℕ) (x : ↥(slabU n)) (t : unitInterval) (j : Fin n) :
    slabPt n x t (Fin.castSucc j) = slabCore n x t j := by
  rw [slabPt, Fin.snoc_castSucc]

@[simp] theorem slabPt_last (n : ℕ) (x : ↥(slabU n)) (t : unitInterval) :
    slabPt n x t (Fin.last n) = slabLastCoord n x t := by
  rw [slabPt, Fin.snoc_last]

@[simp] theorem slabCore_coe (n : ℕ) (x : ↥(slabU n)) (t : unitInterval) (j : Fin n) :
    ((slabCore n x t j : unitInterval) : ℝ)
      = 1/2 + slabLamT n x t * (slabCoord n x j - 1/2) := rfl

@[simp] theorem slabLastCoord_coe (n : ℕ) (x : ↥(slabU n)) (t : unitInterval) :
    ((slabLastCoord n x t : unitInterval) : ℝ)
      = 1 - slabLamT n x t * (1 - slabLast n x) := rfl

theorem slabPt_mem_slabU (n : ℕ) (x : ↥(slabU n)) (t : unitInterval) :
    slabPt n x t ∈ slabU n := by
  show lastCoord (slabPt n x t) < 3/4
  have ht1 : 1 ≤ slabLamT n x t := slabLamT_ge_one n x t
  have h1s : 0 ≤ 1 - slabLast n x := one_sub_slabLast_nonneg n x
  have hmono : 1 * (1 - slabLast n x) ≤ slabLamT n x t * (1 - slabLast n x) :=
    mul_le_mul_of_nonneg_right ht1 h1s
  have hlt := slabLast_lt n x
  rw [lastCoord, slabPt_last, slabLastCoord_coe]
  linarith

theorem slabPt_zero (n : ℕ) (x : ↥(slabU n)) : slabPt n x 0 = x.1 := by
  have hcore : slabCore n x 0 = Fin.init x.1 := by
    funext j
    apply Subtype.ext
    show 1/2 + slabLamT n x 0 * (slabCoord n x j - 1/2)
      = ((x.1 (Fin.castSucc j) : unitInterval) : ℝ)
    rw [slabLamT_zero, slabCoord]
    ring
  have hlast : slabLastCoord n x 0 = x.1 (Fin.last n) := by
    apply Subtype.ext
    show 1 - slabLamT n x 0 * (1 - slabLast n x) = ((x.1 (Fin.last n) : unitInterval) : ℝ)
    rw [slabLamT_zero, slabLast]
    ring
  rw [slabPt, hcore, hlast, Fin.snoc_init_self]

theorem slabGamma_eq_one_of_mem_cubeBdry (n : ℕ) (x : ↥(slabU n))
    (hx : (x.1 : Work.Stems.Cubical.IC (n+1)) ∈ cubeBdryS (n+1)) :
    slabGamma n x = 1 := by
  have h1 : 1 ≤ slabGamma n x := by
    rcases hx with ⟨i, hi | hi⟩
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, hj⟩ | hj
      · subst hj
        have hcoord : slabCoord n x j = 0 := by rw [slabCoord, hi]; rfl
        have habs : |2 * slabCoord n x j - 1| = 1 := by rw [hcoord]; norm_num
        calc (1:ℝ) = |2 * slabCoord n x j - 1| := habs.symm
          _ ≤ slabGamma n x := abs_slabCoord_le_slabGamma n x j
      · subst hj
        have hlast : slabLast n x = 0 := by rw [slabLast, hi]; rfl
        calc (1:ℝ) = 1 - slabLast n x := by rw [hlast]; ring
          _ ≤ slabGamma n x := one_sub_slabLast_le_slabGamma n x
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, hj⟩ | hj
      · subst hj
        have hcoord : slabCoord n x j = 1 := by rw [slabCoord, hi]; rfl
        have habs : |2 * slabCoord n x j - 1| = 1 := by rw [hcoord]; norm_num
        calc (1:ℝ) = |2 * slabCoord n x j - 1| := habs.symm
          _ ≤ slabGamma n x := abs_slabCoord_le_slabGamma n x j
      · subst hj
        have hlast : slabLast n x = 1 := by rw [slabLast, hi]; rfl
        have hlt := slabLast_lt n x
        rw [hlast] at hlt
        norm_num at hlt
  exact le_antisymm (slabGamma_le_one n x) h1

theorem slabLam_eq_one_of_mem_cubeBdry (n : ℕ) (x : ↥(slabU n))
    (hx : (x.1 : Work.Stems.Cubical.IC (n+1)) ∈ cubeBdryS (n+1)) : slabLam n x = 1 := by
  rw [slabLam, slabGamma_eq_one_of_mem_cubeBdry n x hx]
  simp

theorem slabPt_eq_self_of_mem_cubeBdry (n : ℕ) (x : ↥(slabU n))
    (hx : (x.1 : Work.Stems.Cubical.IC (n+1)) ∈ cubeBdryS (n+1)) (t : unitInterval) :
    slabPt n x t = x.1 := by
  have hlam : slabLam n x = 1 := slabLam_eq_one_of_mem_cubeBdry n x hx
  have hlamt : slabLamT n x t = 1 := by
    rw [slabLamT, hlam]; ring
  have hcore : slabCore n x t = Fin.init x.1 := by
    funext j
    apply Subtype.ext
    show 1/2 + slabLamT n x t * (slabCoord n x j - 1/2)
      = ((x.1 (Fin.castSucc j) : unitInterval) : ℝ)
    rw [hlamt, slabCoord]
    ring
  have hlast : slabLastCoord n x t = x.1 (Fin.last n) := by
    apply Subtype.ext
    show 1 - slabLamT n x t * (1 - slabLast n x) = ((x.1 (Fin.last n) : unitInterval) : ℝ)
    rw [hlamt, slabLast]
    ring
  rw [slabPt, hcore, hlast, Fin.snoc_init_self]

theorem slabPt_one_mem_cubeBdry (n : ℕ) (x : ↥(slabU n)) :
    slabPt n x 1 ∈ cubeBdryS (n+1) := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Fin (n+1))))
    (slabNonempty n) (slabTerm n x)
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · -- the maximum is attained at the coordinate `j < n`
    have hγ : slabGamma n x = |2 * slabCoord n x j - 1| := by
      rw [slabGamma]
      rw [hi, slabTerm_castSucc]
    have hpos : 0 < |2 * slabCoord n x j - 1| := hγ ▸ slabGamma_pos n x
    have hval : |2 * ((slabPt n x 1 (Fin.castSucc j) : unitInterval) : ℝ) - 1| = 1 := by
      rw [slabPt_castSucc, slabCore_coe, slabLamT_one, slabLam, hγ]
      rw [show 2 * (1/2 + 1 / |2 * slabCoord n x j - 1| * (slabCoord n x j - 1/2)) - 1
          = 1 / |2 * slabCoord n x j - 1| * (2 * slabCoord n x j - 1) by ring]
      rw [abs_mul, abs_of_pos (one_div_pos.mpr hpos)]
      exact div_mul_cancel₀ 1 (ne_of_gt hpos)
    have hgoal : ((slabPt n x 1 (Fin.castSucc j) : unitInterval) : ℝ) = 0 ∨
        ((slabPt n x 1 (Fin.castSucc j) : unitInterval) : ℝ) = 1 := by
      have h2 := (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hval
      rcases h2 with h2 | h2 <;> [right; left] <;> linarith
    rcases hgoal with h0 | h1
    · exact ⟨Fin.castSucc j, Or.inl (Subtype.ext h0)⟩
    · exact ⟨Fin.castSucc j, Or.inr (Subtype.ext h1)⟩
  · -- the maximum is attained at the last coordinate
    have hγ : slabGamma n x = 1 - slabLast n x := by
      rw [slabGamma]
      rw [hi, slabTerm_last]
    have hval : ((slabPt n x 1 (Fin.last n) : unitInterval) : ℝ) = 0 := by
      rw [slabPt_last, slabLastCoord_coe, slabLamT_one, slabLam, hγ]
      rw [div_mul_cancel₀ 1 (ne_of_gt (one_sub_slabLast_pos n x))]
      ring
    exact ⟨Fin.last n, Or.inl (Subtype.ext hval)⟩

/-! ## Continuity -/

theorem continuous_slabCoord (n : ℕ) (j : Fin n) :
    Continuous fun x : ↥(slabU n) => slabCoord n x j :=
  continuous_subtype_val.comp ((continuous_apply (Fin.castSucc j)).comp continuous_subtype_val)

theorem continuous_slabLast (n : ℕ) :
    Continuous fun x : ↥(slabU n) => slabLast n x :=
  continuous_subtype_val.comp ((continuous_apply (Fin.last n)).comp continuous_subtype_val)

theorem continuous_slabTerm (n : ℕ) (i : Fin (n+1)) :
    Continuous fun x : ↥(slabU n) => slabTerm n x i := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · have h : (fun x : ↥(slabU n) => slabTerm n x (Fin.castSucc j))
        = fun x => |2 * slabCoord n x j - 1| := by
      funext x; rw [slabTerm_castSucc]
    rw [h]
    exact ((continuous_const.mul (continuous_slabCoord n j)).sub continuous_const).abs
  · have h : (fun x : ↥(slabU n) => slabTerm n x (Fin.last n))
        = fun x => 1 - slabLast n x := by
      funext x; rw [slabTerm_last]
    rw [h]
    exact continuous_const.sub (continuous_slabLast n)

theorem continuous_slabGamma (n : ℕ) :
    Continuous fun x : ↥(slabU n) => slabGamma n x := by
  have h : (fun x : ↥(slabU n) => slabGamma n x)
      = fun x => (Finset.univ : Finset (Fin (n+1))).sup' (slabNonempty n) (slabTerm n x) := rfl
  rw [h]
  exact Continuous.finset_sup'_apply (slabNonempty n) (fun i _ => continuous_slabTerm n i)

theorem continuous_slabLam (n : ℕ) :
    Continuous fun x : ↥(slabU n) => slabLam n x := by
  have h : (fun x : ↥(slabU n) => slabLam n x) = fun x => 1 / slabGamma n x := rfl
  rw [h]
  exact Continuous.div₀ continuous_const (continuous_slabGamma n)
    (fun x => ne_of_gt (slabGamma_pos n x))

theorem continuous_slabLamT (n : ℕ) :
    Continuous fun z : ↥(slabU n) × unitInterval => slabLamT n z.1 z.2 := by
  have h : (fun z : ↥(slabU n) × unitInterval => slabLamT n z.1 z.2)
      = fun z => 1 + (z.2 : ℝ) * (slabLam n z.1 - 1) := rfl
  rw [h]
  refine continuous_const.add ((continuous_subtype_val.comp continuous_snd).mul ?_)
  exact ((continuous_slabLam n).comp continuous_fst).sub continuous_const

theorem continuous_slabCore (n : ℕ) :
    Continuous fun z : ↥(slabU n) × unitInterval => slabCore n z.1 z.2 := by
  refine continuous_pi fun j => Continuous.subtype_mk ?_ _
  show Continuous fun z : ↥(slabU n) × unitInterval =>
    1/2 + slabLamT n z.1 z.2 * (slabCoord n z.1 j - 1/2)
  exact continuous_const.add ((continuous_slabLamT n).mul
    (((continuous_slabCoord n j).comp continuous_fst).sub continuous_const))

theorem continuous_slabLastCoord (n : ℕ) :
    Continuous fun z : ↥(slabU n) × unitInterval => slabLastCoord n z.1 z.2 := by
  refine Continuous.subtype_mk ?_ _
  show Continuous fun z : ↥(slabU n) × unitInterval =>
    1 - slabLamT n z.1 z.2 * (1 - slabLast n z.1)
  exact continuous_const.sub ((continuous_slabLamT n).mul
    (continuous_const.sub ((continuous_slabLast n).comp continuous_fst)))

theorem continuous_snocSlab (n : ℕ) :
    Continuous fun p : Work.Stems.Cubical.IC n × unitInterval =>
      (Fin.snoc p.1 p.2 : Work.Stems.Cubical.IC (n+1)) := by
  refine continuous_pi fun i => ?_
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp only [Fin.snoc_castSucc]
    exact (continuous_apply j).comp continuous_fst
  · simp only [Fin.snoc_last]
    exact continuous_snd

theorem continuous_slabPt (n : ℕ) :
    Continuous fun z : ↥(slabU n) × unitInterval => slabPt n z.1 z.2 := by
  have h : (fun z : ↥(slabU n) × unitInterval => slabPt n z.1 z.2)
      = fun z => Fin.snoc (slabCore n z.1 z.2) (slabLastCoord n z.1 z.2) := rfl
  rw [h]
  exact (continuous_snocSlab n).comp
    ((continuous_slabCore n).prodMk (continuous_slabLastCoord n))

/-! ## The deformation retraction and the compression property -/

/-- The radial strong deformation retraction of the slab onto its boundary part. -/
def slabHom (n : ℕ) : C(↥(slabU n) × unitInterval, ↥(slabU n)) where
  toFun z := ⟨slabPt n z.1 z.2, slabPt_mem_slabU n z.1 z.2⟩
  continuous_toFun := Continuous.subtype_mk (continuous_slabPt n) _

theorem compressRel_slabU (n : ℕ) :
    ∀ d, Work.RatHurewicz.CompressRel ↥(Work.Serre.slabU n)
      {x : ↥(Work.Serre.slabU n) |
        (x : Work.Stems.Cubical.IC (n+1)) ∈ Work.Serre.slabU n ∩ Work.Serre.cubeBdryS (n+1)} d := by
  intro d
  refine compressRel_of_deformation (slabHom n) ?_ ?_ ?_ d
  · intro y
    exact Subtype.ext (slabPt_zero n y)
  · intro y
    exact ⟨slabPt_mem_slabU n y 1, slabPt_one_mem_cubeBdry n y⟩
  · intro y hy t
    have hy2 : (y : Work.Stems.Cubical.IC (n+1)) ∈ Work.Serre.cubeBdryS (n+1) := hy.2
    exact Subtype.ext (slabPt_eq_self_of_mem_cubeBdry n y hy2 t)

end

end Work.Serre
