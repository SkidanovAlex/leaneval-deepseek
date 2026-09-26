import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_peel

/-!
# Unpacking a null-homotopy of `LWalk.loopNat` into one of `LWalk.loop`

`LWalk.loopNat hval` is the realization of a closed lattice walk `W` as a loop in the subtype
`↥U` (the `joinNat` of the clamped lifted edges `W.edgeUNat hval`).  The present file converts a
null-homotopy of `W.loopNat hval` *inside* `↥U` into a null-homotopy of the ambient loop
`W.loop : Path (W.pt 0) (W.pt 0)` in `ℂ` whose image lies in `U`.

The mathematical content is that `W.loopNat hval` is the loop `W.loop` lifted to `↥U`: the coercions
of the two paths agree pointwise (`loopNat_coe_apply`).  That is proved by an induction over the
`joinNat` recursion (`joinNat_coe_lt`), comparing the lifted edges `W.edgeU` with the ambient edges
`W.edge`.  The homotopy is then obtained by composing `H' : (W.loopNat hval).Homotopy (refl _)` with
the inclusion `↥U ↪ ℂ`, which is written out by hand so that its underlying function is manifestly
`fun s => (H' s : ℂ)` and hence lands in `U`.
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

/-- **Coercion of a `joinNat`.**  If a family of paths `F` in `↥U` and a family of paths `G` in `ℂ`
agree pointwise after coercion over the index range `k < N`, and the base points agree up to `N`,
then the corresponding `joinNat`s agree pointwise after coercion, as long as the number of glued
pieces is at most `N`. -/
theorem joinNat_coe_lt {U : Set ℂ} {p : ℕ → ↥U} {q : ℕ → ℂ} {N : ℕ}
    (hpq : ∀ k ≤ N, ((p k : ↥U) : ℂ) = q k)
    (F : ∀ k, Path (p k) (p (k + 1))) (G : ∀ k, Path (q k) (q (k + 1)))
    (hFG : ∀ k < N, ∀ t, ((F k t : ↥U) : ℂ) = G k t) :
    ∀ j ≤ N, ∀ t, ((joinNat F j) t : ℂ) = (joinNat G j) t := by
  intro j
  induction j with
  | zero =>
    intro _ t
    rw [joinNat, joinNat, Path.refl_apply, Path.refl_apply]
    exact hpq 0 (Nat.zero_le _)
  | succ i ih =>
    intro hle t
    rw [show joinNat F (i + 1) = (joinNat F i).trans (F i) from rfl,
        show joinNat G (i + 1) = (joinNat G i).trans (G i) from rfl,
        Path.trans_apply, Path.trans_apply]
    split_ifs with h
    · exact ih (by omega) _
    · exact hFG i (by omega) _

/-- **`W.loopNat hval` is the lift of `W.loop`.**  The values of the two paths agree pointwise in
`ℂ`. -/
theorem loopNat_coe_apply {U : Set ℂ} (W : LWalk) (hval : ∀ t, W.path t ∈ U)
    (t : unitInterval) : ((W.loopNat hval) t : ℂ) = W.loop t := by
  have h2 : ((joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n) t : ℂ)
      = (joinNat (p := W.pt) (fun k => W.edge k) W.n) t :=
    joinNat_coe_lt (fun k hk => by rw [W.ptMin_apply, Nat.min_eq_left hk])
      (W.edgeUNat hval) (fun k => W.edge k)
      (fun k hk t => by rw [W.edgeUNat_apply hval k t, dif_pos hk]) W.n (le_refl _) t
  rw [show ((W.loopNat hval) t : ℂ)
        = ((joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n) t : ℂ) from rfl, h2]
  show (joinNat (p := W.pt) (fun k => W.edge k) W.n) t = W.loop t
  rw [show W.loop t = (joinNat (p := W.pt) (fun k => W.edge k) W.n) t from rfl]

/-- **Unpacking.**  A null-homotopy of the lifted loop `W.loopNat hval` inside `↥U` yields a
null-homotopy of `W.loop` in `ℂ` whose image is contained in `U`. -/
theorem loopNat_homotopy_unpack {U : Set ℂ} (W : LWalk) (hval : ∀ t, W.path t ∈ U)
    (h : Path.Homotopic (W.loopNat hval) (Path.refl (W.ptMin hval 0))) :
    ∃ H : Path.Homotopy W.loop (Path.refl (W.pt 0)), ∀ s, H s ∈ U := by
  obtain ⟨H'⟩ := h
  refine ⟨{ toContinuousMap :=
              { toFun := fun s => (H' s : ℂ)
                continuous_toFun := continuous_subtype_val.comp H'.continuous }
            map_zero_left := fun x => ?_
            map_one_left := fun x => ?_
            prop' := fun t x hx => ?_ }, fun s => (H' s).2⟩
  · have h0 : H' (0, x) = (W.loopNat hval) x := H'.map_zero_left x
    show (H' (0, x) : ℂ) = W.loop x
    rw [h0]
    exact loopNat_coe_apply W hval x
  · have h1 : H' (1, x) = (Path.refl (W.ptMin hval 0)) x := H'.map_one_left x
    show (H' (1, x) : ℂ) = (Path.refl (W.pt 0)) x
    rw [h1]
    rfl
  · have hp : H' (t, x) = (W.loopNat hval) x := H'.prop' t x hx
    show (H' (t, x) : ℂ) = W.loop x
    rw [hp]
    exact loopNat_coe_apply W hval x

end

end Work.Smooth.JordanSeparation
