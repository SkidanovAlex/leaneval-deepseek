import Mathlib
import Submission.FeketeLim
import Submission.Step3Defs
import Submission.Step3Bridge
import Submission.XTransfer
import Submission.RegularSlit

/-!
# Step3Decomp -- first decomposition lemmas for Step3.sym_maximality
# (Dubinin's symmetric-maximality / hedgehog capacity bound)

STATUS: verified module — all declarations axiom-clean [propext,
Classical.choice, Quot.sound] EXCEPT the single marked statement skeleton
`star_fekete_limsup_le_regular` (`:= by sorry`; unimported research
isolate, NOT imported by Submission.lean, does not affect the comparator).
No dependency on the `sorry` `Step3.sym_maximality` (imported only for the
definitions `Step3.dirStar`, `Step3Bridge.rootSeq`).

## The gate and its decomposition
`Step3.sym_maximality` (statement FIXED): for unit directions `u`
(`1 ≤ u.card =: s`), `0 ≤ L`:
    limsup_n (feketeNumber (dirStar u L) (n+1))^(2/((n+1)n)) ≤ L·4^(-1/s),
`dirStar u L = ⋃_{w ∈ u} [0, L·w]`.  By `Step3Bridge.sym_maximality_of_unit`
(PROVED) it suffices to prove the case L = 1 for every finite unit
direction set.  The remaining content is the NON-EQUIANGULAR EXTREMAL
(Dubinin/Gonchar): among s-direction stars of unit spike length, the
equiangular one MAXIMISES the Fekete-root limsup, and its value is
4^{-1/s} (equiangular value/upper side: RegularSlit spine, route B
sharp side; the converse side for arbitrary configurations is open).

NATURAL DECOMPOSITION of the L = 1 case (each item a permanent lemma):
  (1) ROTATION INVARIANCE (this module, PROVED): the Fekete numbers, hence
      the root-limsup, are invariant under rotating the whole star (an
      isometry).  So the direction set may be freely rotated (WLOG one
      direction = 1); the RHS 4^{-1/s} depends only on u.card.
  (2) (future) a comparison/covering step relating an arbitrary star to
      the equiangular one (or the dual radial-slit extremal) — OPEN.
  (3) (future) the equiangular value computation on the Fekete/Chebyshev
      side for arbitrary (not just regular) configurations — OPEN.
This module proves (1) fully: `vdm_rotation` (Vandermonde product
invariance), `feketeSet_rotation` / `feketeNumber_rotation` (Fekete number
invariance under `z ↦ ρ·z`, ‖ρ‖ = 1), `dirStar_rotation` (the star of the
rotated directions is the rotated star), `rootSeq_rotation` (the
Step3-root sequence is invariant), and the limsup corollary
`rootLimsup_rotation` — the reduction lemma any extremal/symmetry argument
needs in order to normalise configurations.
-/

noncomputable section

open scoped Real Topology BigOperators
open Set Filter Metric

namespace Submission.Step3Decomp

open Submission.FeketeLim
open Submission.Step3
open Submission.Step3Bridge

/-- A unit complex number is nonzero (rotation by it is injective). -/
lemma rotation_ne_zero {ρ : ℂ} (hρ : ‖ρ‖ = 1) : ρ ≠ 0 := by
  intro hz
  rw [hz, norm_zero] at hρ
  norm_num at hρ

/-- Vandermonde products are invariant under rotating every point by a
unit complex number: `ρ·x`. -/
lemma vdm_rotation (ρ : ℂ) (hρ : ‖ρ‖ = 1) (x : ℕ → ℂ) (n : ℕ) :
    vdm (fun i : ℕ => ρ * x i) n = vdm x n := by
  unfold vdm
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  have hnorm : ‖ρ * x j - ρ * x i‖ = ‖x j - x i‖ := by
    have hfac : ρ * x j - ρ * x i = ρ * (x j - x i) := by ring
    rw [hfac, norm_mul, hρ, one_mul]
  rw [hnorm]

/-- If two configurations agree on the first `n` points then their
Vandermonde products agree. -/
lemma vdm_congr_of_forall_lt {x y : ℕ → ℂ} {n : ℕ}
    (h : ∀ i : ℕ, i < n → x i = y i) : vdm x n = vdm y n := by
  unfold vdm
  apply Finset.prod_congr rfl
  intro i hi
  have hi' : i < n := by simpa using hi
  apply Finset.prod_congr rfl
  intro j hj
  have hj' : j < i := by simpa using hj
  rw [h i hi', h j (lt_trans hj' hi')]

/-- The rotation map on configurations preserves the Fekete-set values:
`feketeSet (ρ·K) n = feketeSet K n` for unit ρ. -/
lemma feketeSet_rotation (ρ : ℂ) (hρ : ‖ρ‖ = 1) (K : Set ℂ) (n : ℕ) :
    feketeSet ((fun z : ℂ => ρ * z) '' K) n = feketeSet K n := by
  classical
  ext d
  constructor
  · -- a configuration in ρ·K pulls back to a configuration in K
    rintro ⟨x, hx, hxd⟩
    let y : ℕ → ℂ := fun i : ℕ => if hi : i < n then
      Classical.choose (show ∃ z : ℂ, z ∈ K ∧ ρ * z = x i from hx i hi)
    else 0
    have hyK : ∀ i : ℕ, i < n → y i ∈ K := by
      intro i hi
      dsimp [y]
      rw [dif_pos hi]
      exact (Classical.choose_spec (show ∃ z : ℂ, z ∈ K ∧ ρ * z = x i from hx i hi)).1
    have hxy : ∀ i : ℕ, i < n → ρ * y i = x i := by
      intro i hi
      dsimp [y]
      rw [dif_pos hi]
      exact (Classical.choose_spec (show ∃ z : ℂ, z ∈ K ∧ ρ * z = x i from hx i hi)).2
    refine ⟨y, hyK, ?_⟩
    calc
      d = vdm x n := hxd
      _ = vdm (fun i : ℕ => ρ * y i) n := by
            exact vdm_congr_of_forall_lt (fun i hi => (hxy i hi).symm)
      _ = vdm y n := vdm_rotation ρ hρ y n
  · -- a configuration in K maps into ρ·K
    rintro ⟨y, hy, hyd⟩
    have hx : ∀ i : ℕ, i < n → ρ * y i ∈ (fun z : ℂ => ρ * z) '' K := by
      intro i hi
      refine ⟨y i, hy i hi, rfl⟩
    refine ⟨(fun i : ℕ => ρ * y i), hx, ?_⟩
    rw [hyd]
    exact (vdm_rotation ρ hρ y n).symm

/-- Fekete numbers are invariant under rotating the set by a unit complex
number: `feketeNumber (ρ·K) n = feketeNumber K n`. -/
lemma feketeNumber_rotation (ρ : ℂ) (hρ : ‖ρ‖ = 1) (K : Set ℂ) (n : ℕ) :
    feketeNumber ((fun z : ℂ => ρ * z) '' K) n = feketeNumber K n := by
  unfold feketeNumber
  rw [feketeSet_rotation ρ hρ K n]

/-- The star of the rotated directions equals the rotated star:
`dirStar (u.image (·*ρ)) L = ρ·(dirStar u L)` for unit ρ (and any L). -/
private lemma smul_rotation (ρ : ℂ) (t : ℝ) (L : ℝ) (w : ℂ) :
    ρ * (t • ((L : ℂ) * w)) = t • ((L : ℂ) * (ρ * w)) := by
  rw [Algebra.smul_def, Algebra.smul_def]
  ring

/-- The star of the rotated directions equals the rotated star:
`dirStar (u.image (·*ρ)) L = ρ·(dirStar u L)` for unit ρ (and any L). -/
lemma dirStar_rotation (ρ : ℂ) (hρ : ‖ρ‖ = 1) (u : Finset ℂ) (L : ℝ) :
    dirStar (u.image (fun w : ℂ => ρ * w)) L =
      (fun z : ℂ => ρ * z) '' (dirStar u L) := by
  ext X
  constructor
  · rintro ⟨w, hw, hseg⟩
    rcases Finset.mem_image.mp hw with ⟨v, hv, rfl⟩
    rcases (Submission.XTransfer.mem_segment_zero_iff ((L : ℂ) * (ρ * v)) X).1 hseg with ⟨t, ht, hXt⟩
    refine ⟨t • ((L : ℂ) * v), ?mem, ?eq⟩
    · refine ⟨v, hv, (Submission.XTransfer.mem_segment_zero_iff ((L : ℂ) * v)
        (t • ((L : ℂ) * v))).2 ⟨t, ht, rfl⟩⟩
    · rw [hXt]
      exact smul_rotation ρ t L v
  · rintro ⟨z, hz, hX⟩
    rcases hz with ⟨w, hw, hseg⟩
    rcases (Submission.XTransfer.mem_segment_zero_iff ((L : ℂ) * w) z).1 hseg with ⟨t, ht, hzt⟩
    refine ⟨ρ * w, Finset.mem_image.mpr ⟨w, hw, rfl⟩, ?_⟩
    refine (Submission.XTransfer.mem_segment_zero_iff ((L : ℂ) * (ρ * w)) X).2 ⟨t, ht, ?_⟩
    rw [← hX, hzt]
    exact smul_rotation ρ t L w

/-- The Step3-root sequence is invariant under rotating the direction set. -/
lemma rootSeq_rotation (ρ : ℂ) (hρ : ‖ρ‖ = 1) (u : Finset ℂ) (L : ℝ) (n : ℕ) :
    rootSeq (u.image (fun w : ℂ => ρ * w)) L n = rootSeq u L n := by
  unfold rootSeq
  have hf : Submission.FeketeLim.feketeNumber
        (dirStar (u.image (fun w : ℂ => ρ * w)) L) (n + 1) =
      Submission.FeketeLim.feketeNumber (dirStar u L) (n + 1) := by
    rw [dirStar_rotation ρ hρ u L]
    exact feketeNumber_rotation ρ hρ (dirStar u L) (n + 1)
  rw [hf]

/-- **Root-limsup invariance (first decomposition lemma).**  The
Step3.limsup of the Fekete-root sequence of a star is unchanged when the
direction set is rotated by a unit complex number.  Consequently the
L = 1 case of `Step3.sym_maximality` for `u` is equivalent to the same
statement for any rotated direction set (the right-hand side
`4^(-1/u.card)` is unchanged since the rotation image has the same
cardinality).  This is the reduction that lets an extremal/symmetry
argument normalise a configuration (e.g. put one direction at 1). -/
theorem rootLimsup_rotation (ρ : ℂ) (hρ : ‖ρ‖ = 1) (u : Finset ℂ) (L : ℝ) :
    Filter.limsup (fun n : ℕ => rootSeq (u.image (fun w : ℂ => ρ * w)) L n)
        Filter.atTop =
      Filter.limsup (fun n : ℕ => rootSeq u L n) Filter.atTop := by
  apply Filter.limsup_congr
  exact Filter.Eventually.of_forall (fun n => rootSeq_rotation ρ hρ u L n)

/-- The equiangular direction set with `s` directions (the s-th roots of
unity, `k = 0..s-1`).  The regular s-star `dirStar (regularDirSet s) 1`
is the symmetric hedgehog whose Fekete/Chebyshev value is `4^(-1/s)`
(decomposition item (3) — the value computation — is a separate future
lemma; the RegularSlit module banks the dual conformal-map side). -/
def regularDirSet (s : ℕ) : Finset ℂ :=
  (Finset.range s).image (fun k : ℕ => Submission.RegularSlit.unitRoot s k)

/-- **Keystone skeleton (DEEP — Dubinin's symmetric maximality in
comparison form).**  For any finite nonempty set `u` of unit directions,
the L = 1 Fekete-root limsup of the hedgehog `dirStar u 1` (all spikes of
length 1) is at most the same quantity for the EQUIANGULAR hedgehog with
the same number of spikes:

    limsup_n rootSeq u 1 n  ≤  limsup_n rootSeq (regularDirSet u.card) 1 n .

This is decomposition item (2) of the module header: an arbitrary
s-direction star has Fekete root limsup no larger than the regular one
(the extremal configuration is the symmetric star — Dubinin's theorem,
book §4.4 / the radial-slit dual `rad(D,0) ≥ 4^(1/s)` of RegularSlit's
`equiangular_conformal_data`).  Together with the regular-value lemma
(item (3), `limsup rootSeq (regularDirSet s) 1 = 4^(-1/s)`) and
`Step3Bridge.sym_maximality_of_unit` (L-reduction, PROVED) this theorem
gives `Step3.sym_maximality` verbatim (the RHS of Step3 is
`(L:ℝ)·4^(-1/u.card)`; normalization freedom is `rootLimsup_rotation`,
PROVED above).  OPEN (research-level: the extremal inequality side of the
Dubinin/Gonchar hedgehog theorem for ALL `s ≥ 3`; s = 1 is
`MaximalityOne`, s = 2 is `Step3Two`, the L-reduction is banked). -/
theorem star_fekete_limsup_le_regular (u : Finset ℂ)
    (hu : ∀ w ∈ u, ‖w‖ = 1) (hne : u.Nonempty) :
    Filter.limsup (fun n : ℕ => rootSeq u 1 n) Filter.atTop ≤
      Filter.limsup (fun n : ℕ => rootSeq (regularDirSet u.card) 1 n) Filter.atTop := by
  sorry

end Submission.Step3Decomp
