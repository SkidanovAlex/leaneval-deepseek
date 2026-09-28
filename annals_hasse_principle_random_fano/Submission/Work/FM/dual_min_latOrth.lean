import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.Lat.detLAux
import Submission.Work.HP.Vero.LamAux
import Submission.Work.HP.Vero.dualLat_nonempty
import Submission.Work.HP.HP3.dmin_le_norm_mul_dual

/-!
# `𝔡₂(x)/‖x‖ ≤ λ₁(Λ_x^*)`

For a primitive integer vector `x : Fin (n+1) → ℤ` (with `n ≥ 1`), the ratio
`𝔡₂(x)/‖x‖ = dmin 2 {x} / eNorm x` — where `𝔡₂(x)` is the least covolume of a rank-`2`
sublattice of `ℤ^{n+1}` containing `x` — is at most the first successive minimum of the dual
lattice `Λ_x^* = dualLat (realify (latOrth x))`.

The content is contained in

* `Work.HP.HP3.dmin_le_norm_mul_dual`: every nonzero vector `u` of the dual satisfies
  `𝔡₂(x) ≤ ‖x‖ · ‖u‖` (the paper's `d = 1` "one vector bound"), obtained by lifting `u` to an
  integer vector `w` with `u = π(w)`, so that `ℤx + ℤw` is an admissible rank-`2` lattice of
  covolume `‖x‖·dist(w, ℝx) = ‖x‖‖u‖`;
* `Work.HP.Vero.le_lamR_one`: `λ₁` of a lattice is at least any constant that bounds from below
  the norm of every nonzero element, provided the lattice is nonzero.
-/

set_option autoImplicit false
noncomputable section

namespace Work.FM

open Work.HP

/-- Pairing an integer vector against a coordinate vector `e_a`. -/
private lemma sum_single_mul_int {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) (b : ℤ)
    (f : ι → ℤ) : ∑ i, (Pi.single a b : ι → ℤ) i * f i = b * f a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    rw [Pi.single_eq_of_ne hx, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- A nonzero integer vector in at least two coordinates admits a nonzero integral vector
orthogonal to it. -/
lemma exists_ne_zero_latOrth {n : ℕ} (hn : 1 ≤ n) (c : Fin (n + 1) → ℤ) (hc : c ≠ 0) :
    ∃ z ∈ latOrth c, z ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
  have hcard : 1 < Fintype.card (Fin (n + 1)) := by simp only [Fintype.card_fin]; omega
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hcard i
  refine ⟨(Pi.single j (c i) : Fin (n + 1) → ℤ) - Pi.single i (c j), ?_, ?_⟩
  · rw [mem_latOrth, pdot, dotZ_apply]
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [sum_single_mul_int j (c i) c, sum_single_mul_int i (c j) c]
    ring
  · intro h
    have hh := congrFun h j
    rw [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hj, sub_zero] at hh
    exact hi hh

theorem dual_min_latOrth (n : ℕ) (hn : 1 ≤ n) (x : Fin (n + 1) → ℤ) (hx : Work.HP.IsPrim x) :
    Work.HP.dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) / Work.HP.eNorm x
      ≤ Work.HP.lamR (Work.HP.dualLat (Work.HP.realify (Work.HP.latOrth x))) 1 := by
  have hx0 : x ≠ 0 := isPrim_ne_zero hx
  have hxpos : 0 < eNorm x := eNorm_pos_of_ne_zero hx0
  -- The dual lattice contains a nonzero vector.
  have hne : ∃ v ∈ dualLat (realify (latOrth x)), v ≠ 0 := by
    obtain ⟨z, hz, hz0⟩ := exists_ne_zero_latOrth hn x hx0
    refine ⟨intCastPi z, Work.HP.Vero.realify_le_dualLat (latOrth x)
      (Submodule.mem_map_of_mem hz), ?_⟩
    intro h
    apply hz0
    funext i
    have hi := congrFun h i
    simp only [intCastPi_apply, Pi.zero_apply] at hi
    exact_mod_cast hi
  -- It suffices to bound below the norm of every nonzero dual vector.
  refine Work.HP.Vero.le_lamR_one (dualLat (realify (latOrth x))) hne ?_
  intro u hu hu0
  have hdu := Work.HP.HP3.dmin_le_norm_mul_dual n x hx u hu hu0
  rw [div_le_iff₀ hxpos]
  calc dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ eNorm x * rNorm u := hdu
    _ = rNorm u * eNorm x := by ring

end Work.FM
