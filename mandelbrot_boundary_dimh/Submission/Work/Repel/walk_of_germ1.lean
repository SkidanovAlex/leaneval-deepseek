import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.Spec

/-!
# REPEL area: the walk of a germ iterate lifts

`germ1 s R ζ = s · pushdown R (ζ/s)` is the rescaled pushdown of a lifted `T`-equivariant map `R`
(Shishikura §6).  The coordinate change `ζ = s · π w` conjugates it to `R` on the universal cover:
`germ1 s R (s · π w) = s · π (R w)` whenever `w ∈ DR`.

This file proves `Work.Repel.walk_of_germ1`: if the orbit of `s · π w` under `germ1 s R` stays in
the image of `{0} ∪ π(DR)` under `ζ ↦ s·ζ` for `i < n`, then the lifted orbit `R^[i] w` stays in
`DR` and the two orbits correspond, `(germ1 s R)^[i] (s · π w) = s · π (R^[i] w)`.  The key point
is that `π`-preimages of different lifts differ by integers, and `DR` is `T`-invariant, so the
`π`-image of a point determines `DR`-membership.
-/

namespace Work.Repel

open MandelDim
open Work.Horn.MandelDim

noncomputable section

/-- Evaluation of `germ1` at a point of the form `s * piExp v`. -/
lemma germ1_mul_piExp {R : ℂ → ℂ} {s : ℂ} (hs : s ≠ 0) (v : ℂ) :
    germ1 s R (s * piExp v) = s * pushdown R (piExp v) := by
  rw [germ1_apply, mul_div_cancel_left₀ _ hs]

/-- For a `T`-invariant set `D`, membership of a point is decided by its `π`-image: if the
`π`-image of `y` is the `π`-image of some point of `D`, then `y ∈ D` (the two points differ by an
integer, and `D` is invariant under integer translations). -/
lemma mem_of_piExp_mem_image {D : Set ℂ} (hD : IsTInvariant D) {y : ℂ}
    (hy : piExp y ∈ piExp '' D) : y ∈ D := by
  obtain ⟨d, hd, hde⟩ := hy
  obtain ⟨k, hk⟩ := piExp_eq_iff.mp hde.symm
  rw [hk]
  exact IsTInvariant.add_int hD hd k

theorem walk_of_germ1 {R : ℂ → ℂ} {DR : Set ℂ} (hDR : MandelDim.IsTInvariant DR)
    (hReq : ∀ w ∈ DR, R (w + 1) = R w + 1) {s : ℂ} (hs : s ≠ 0) {w : ℂ} {n : ℕ}
    (hw : w ∈ DR)
    (horbit : ∀ i < n,
      (Work.Repel.germ1 s R)^[i] (s * MandelDim.piExp w) ∈ (fun ζ => s * ζ) '' (insert 0 (MandelDim.piExp '' DR)))
    (hne : ∀ i < n, (Work.Repel.germ1 s R)^[i] (s * MandelDim.piExp w) ≠ 0) :
    (∀ i < n, R^[i] w ∈ DR) ∧
      ∀ i < n, (Work.Repel.germ1 s R)^[i] (s * MandelDim.piExp w) = s * MandelDim.piExp (R^[i] w) := by
  have hE : ∀ u ∈ DR, u + 1 ∈ DR → R (u + 1) = R u + 1 := fun u hu _ => hReq u hu
  have key : ∀ i, i < n → R^[i] w ∈ DR ∧
      (germ1 s R)^[i] (s * piExp w) = s * piExp (R^[i] w) := by
    intro i
    induction i with
    | zero => intro _; exact ⟨hw, rfl⟩
    | succ i ih =>
      intro hi
      have hi' : i < n := Nat.lt_of_succ_lt hi
      obtain ⟨hQi, hPi⟩ := ih hi'
      have hiter : (germ1 s R)^[i + 1] (s * piExp w) = s * piExp (R^[i + 1] w) := by
        rw [Function.iterate_succ_apply', hPi, germ1_mul_piExp hs (R^[i] w),
          Work.Horn.MandelDim.pushdown_piExp hDR hE hQi, Function.iterate_succ_apply' R i w]
      refine ⟨?_, hiter⟩
      -- membership of `R^[i+1] w` in `DR`, from the orbit condition at index `i+1`
      have hmem := horbit (i + 1) hi
      rw [hiter] at hmem
      obtain ⟨u, hu, hue⟩ := hmem
      have hup : piExp (R^[i + 1] w) = u := (mul_left_cancel₀ hs hue).symm
      have hune : u ≠ 0 := by
        intro h0
        refine hne (i + 1) hi ?_
        rw [hiter, hup, h0, mul_zero]
      have hu' : u ∈ piExp '' DR := (Set.mem_insert_iff.mp hu).resolve_left hune
      exact mem_of_piExp_mem_image hDR (by rw [hup]; exact hu')
  exact ⟨fun i hi => (key i hi).1, fun i hi => (key i hi).2⟩

end

end Work.Repel
