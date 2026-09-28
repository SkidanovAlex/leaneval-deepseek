import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.detgam_span_pair_wedgeNorm
import Submission.Work.HP.HP3.dual_proj_int_vec
import Submission.Work.HP.HP3.dual_mem_dotR_eq_zero
import Submission.Work.HP.HP3.wedgeNorm_eq_of_sub

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.HP.HP3

open Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `dmin r S ≤ detL L` for a rank-`r` lattice `L` containing `S`. -/
lemma dmin_le_detL {r : ℕ} {S : Set (ι → ℤ)} {L : Submodule ℤ (ι → ℤ)}
    (hr : rk L = r) (hS : S ⊆ L) : dmin r S ≤ detL L := by
  rw [dmin]
  refine csInf_le ⟨0, fun D ⟨M, _, _, hM⟩ => hM ▸ detL_nonneg M⟩ ⟨L, hr, hS, rfl⟩

/-- The covolume of the `ℤ`-span of `![x,w]` is `wedgeNorm x w`. -/
lemma detL_span_range_pair (x w : ι → ℤ) (h : LinearIndependent ℤ ![x, w]) :
    detL (Submodule.span ℤ (Set.range ![x, w])) = wedgeNorm x w := by
  rw [Matrix.range_cons_cons_empty]
  exact detgam_span_pair_wedgeNorm x w h

/-- If `toR w = u - s • toR x` with `u ⊥ x`, then `x` and `w` are `ℤ`-linearly independent,
provided `x ≠ 0` and `u ≠ 0`. -/
lemma linearIndependent_pair_of_sub (x w : ι → ℤ) (u : ι → ℝ) (s : ℝ)
    (hx0 : x ≠ 0) (hu0 : u ≠ 0) (hwx : toR w = u - s • toR x)
    (horth : dotR u (toR x) = 0) : LinearIndependent ℤ ![x, w] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  -- Coordinatewise form of `a • x + b • w = 0`, cast to `ℝ`.
  have hcoord : ∀ i, (a : ℝ) * (x i : ℝ) + (b : ℝ) * (w i : ℝ) = 0 := by
    intro i
    have h := congrFun hab i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h
    have h' := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at h'
    simpa using h'
  -- `(w i : ℝ) = u i - s * (x i : ℝ)`.
  have hw : ∀ i, (w i : ℝ) = u i - s * (x i : ℝ) := by
    intro i
    have h := congrFun hwx i
    simpa [toR, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h
  -- `∑ i, (x i : ℝ) * u i = 0`.
  have horth' : ∑ i, (x i : ℝ) * u i = 0 := by
    rw [← horth]
    simp only [dotR, toR]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  -- Sum of the coordinate relations against `u`.
  have hsum : ∑ i, u i * ((a : ℝ) * (x i : ℝ) + (b : ℝ) * (w i : ℝ)) = 0 := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [hcoord i, mul_zero])]
    simp
  have hmain : ((a : ℝ) - (b : ℝ) * s) * (∑ i, (x i : ℝ) * u i)
      + (b : ℝ) * (∑ i, (u i) ^ 2) = 0 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← hsum]
    exact Finset.sum_congr rfl (fun i _ => by rw [hw i]; ring)
  -- The norm of `u` is positive.
  have hu2pos : 0 < ∑ i, (u i) ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hu0
    exact lt_of_lt_of_le (sq_pos_of_ne_zero hi)
      (Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i))
  have hb0 : (b : ℝ) = 0 := by
    rw [horth', mul_zero, zero_add] at hmain
    rcases mul_eq_zero.mp hmain with h | h
    · exact h
    · exact absurd h (ne_of_gt hu2pos)
  have hb : b = 0 := by exact_mod_cast hb0
  refine ⟨?_, hb⟩
  have ha0 : (a : ℝ) = 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
    have h := hcoord i
    rw [hb] at h
    simp only [Int.cast_zero, zero_mul, add_zero] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd (show x i = 0 by exact_mod_cast h') hi
  exact_mod_cast ha0

/-- For a primitive `x`, every nonzero vector `u` of the dual of `latOrth x` satisfies
`𝔡₂(x) ≤ ‖x‖ · ‖u‖`, i.e. `λ₁(dualLat (realify (latOrth x))) ≥ 𝔡₂(x)/‖x‖`.

Suggested route (paper, the "one vector" bound, case `d = 1`).  `latOrth x = x^⊥ ∩ ℤ^{n+1}` and
`u ∈ span ℤ (x^⊥)`.  For every `i, j` the vector `x i • e_j - x j • e_i` lies in `latOrth x`, so
`x i * u j - x j * u i ∈ ℤ` (`u ∈ dualLat`), i.e. `b_i := x i • u - u i • x ∈ ℤ^{n+1}` has integer
coordinates; also `proj(b_i) = x i • u` where `proj` is the orthogonal projection onto `x^⊥`.
Pick integers `α_i` with `∑ i, α_i * x i = 1` (Bézout, `IsPrim x`); then `w := ∑ i, α_i • b_i ∈
ℤ^{n+1}` satisfies `proj(w) = u`, so `dist(w, ℝx) = ‖u‖`.  The rank-`2` submodule
`L := ℤ x ⊕ ℤ w ⊆ ℤ^{n+1}` contains `x` and has `detL L = ‖x‖ * dist(w, ℝx) = eNorm x * rNorm u`
(covolume = area of the parallelogram).  As `dmin 2 {x}` is the infimum of `detL` over rank-`2`
sublattices containing `x`, the claim follows. -/
theorem dmin_le_norm_mul_dual (n : ℕ) (x : Fin (n + 1) → ℤ) (hx : IsPrim x)
    (u : Fin (n + 1) → ℝ) (hu : u ∈ dualLat (realify (latOrth x))) (hu0 : u ≠ 0) :
    dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ eNorm x * rNorm u := by
  have horth : dotR u (toR x) = 0 := dual_mem_dotR_eq_zero x u hu
  obtain ⟨w, s, hwx⟩ := dual_proj_int_vec n x hx u hu
  have hx0 : x ≠ 0 := by
    intro h
    obtain ⟨α, hα⟩ := Work.HP.Lat.prim_bezout x hx
    rw [h] at hα
    simp at hα
  have hind : LinearIndependent ℤ ![x, w] :=
    linearIndependent_pair_of_sub x w u s hx0 hu0 hwx horth
  have hdet : detL (Submodule.span ℤ (Set.range ![x, w])) = eNorm x * rNorm u := by
    rw [detL_span_range_pair x w hind, wedgeNorm_eq_of_sub x w u s hwx horth]
  have hrk : rk (Submodule.span ℤ (Set.range ![x, w])) = 2 := by
    rw [rk, Module.finrank_eq_card_basis (Module.Basis.span hind)]
    simp
  have hxL : x ∈ Submodule.span ℤ (Set.range ![x, w]) :=
    Submodule.subset_span ⟨0, rfl⟩
  have hsub : ({x} : Set (Fin (n + 1) → ℤ)) ⊆ Submodule.span ℤ (Set.range ![x, w]) :=
    Set.singleton_subset_iff.mpr hxL
  exact le_trans (dmin_le_detL hrk hsub) (le_of_eq hdet)

end Work.HP.HP3
