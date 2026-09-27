/-
A6 `Geo/DualStretch` — the stretch is also a *right* inverse of the stretch with the reciprocal taper.

`Work.Geo.DualStretch.stretch_inv` shows that the map
`x ↦ stretchM β p P hP (fun z => (taperM … z)⁻¹) (stretch P hP β p α M x)`
is the identity on `P.space`.  This file proves the other composition:
for `y ∈ P.space`, applying the stretch of `y` by the reciprocal taper and then the stretch again
returns `y`.

The argument is the mirror image of `stretch_inv`, run with the *inverse* stretch in the role of the
forward one.  Writing `c = taperM β p P hP α M y` and `z = stretchM β p P hP (fun _ => c⁻¹) y`
(the inverse stretch of `y`, which is a constant-factor stretch at `y`), the constant-factor
bookkeeping of `stretchConst_aux` and `stretchConst_relations` gives

* `z ∈ P.space`, with barycentric mass decomposition `wtC β p P hP c⁻¹ y` on `posCands P hP y`;
* `S(z) = c⁻¹ * S(y) / D`, `A(z) = D⁻¹ • A(y)`, `B(z) = (c⁻¹ / D) • B(y)` with
  `D = 1 + (c⁻¹ - 1) * S(y)`;
* `segOf z = segOf y`, so `taperM z = c`.

The composition `stretch … z` then expands to
`(1 + (c - 1) * (c⁻¹ S(y) / D))⁻¹ • (D⁻¹ • A(y) + c • ((c⁻¹ / D) • B(y)))`, which is exactly the
identity `inv_algebra` for the factor `c⁻¹` applied to `A(y) + B(y) = y`.
-/
import Mathlib
import Submission.Work.Geo.DualStretch.Defs
import Submission.Work.Geo.DualStretch.stretch_defs
import Submission.Work.Geo.DualStretch.massG_api
import Submission.Work.Geo.DualStretch.Basic
import Submission.Work.Geo.DualStretch.stretch_aux
import Submission.Work.Geo.DualStretch.stretch_relations
import Submission.Work.Geo.DualStretch.stretch_inv
import Submission.Work.Geo.DualStretch.massG_of_chain_repr
import Submission.Work.Geo.DualStretch.const_defs
import Submission.Work.Geo.DualStretch.stretchConst_aux
import Submission.Work.Geo.DualStretch.stretchConst_relations

namespace Work.Geo.DualStretch

open _root_.PL (E Cx)

/-- `stretchM` depends on the rescaling function only through its value at the point. -/
theorem stretchM_congr_val {n : ℕ} (P : Cx n) (hP : P.faces.Finite) {β : ℝ} {p : ℕ}
    {Mb Mb' : E n → ℝ} {x : E n} (h : Mb x = Mb' x) :
    stretchM β p P hP Mb x = stretchM β p P hP Mb' x := by
  unfold stretchM
  rw [h]

theorem stretch_inv_right {n : ℕ} (P : PL.Cx n) (hP : P.faces.Finite) {β α M : ℝ}
    (hM : 0 < M) {p : ℕ} {y : PL.E n} (hy : y ∈ P.space) :
    Work.Geo.DualStretch.stretch P hP β p α M
        (Work.Geo.DualStretch.stretchM β p P hP
          (fun z => (Work.Geo.DualStretch.taperM β p P hP α M z)⁻¹) y) = y := by
  classical
  have hcy0 : 0 < taperM β p P hP α M y := taperM_pos hM p P hP y
  set z : PL.E n := stretchM β p P hP (fun z => (taperM β p P hP α M z)⁻¹) y with hz
  have hzeq : z = stretchM β p P hP (fun _ => (taperM β p P hP α M y)⁻¹) y := by
    rw [hz]; exact stretchM_congr_val P hP rfl
  obtain ⟨hdenCpos, hfacesC, hneC, hchainC, hwtCpos, hwtCsum, hzmem, hzrepr⟩ :=
    stretchConst_aux P hP (m := (taperM β p P hP α M y)⁻¹) (inv_pos.mpr hcy0) hy hzeq
  obtain ⟨hwtC, hwtOff⟩ :=
    massG_of_chain_repr P hP (posCands P hP y) hfacesC hneC hchainC
      (wtC β p P hP (taperM β p P hP α M y)⁻¹ y) hwtCpos hwtCsum (y := z) hzrepr
  have hwtG : ∀ τ : Finset (PL.E n), massG P hP z τ =
      if τ ∈ posCands P hP y then wtC β p P hP (taperM β p P hP α M y)⁻¹ y τ else 0 := by
    intro τ
    by_cases hτ : τ ∈ posCands P hP y
    · rw [ite_eq_left hτ]; exact hwtC τ hτ
    · rw [ite_eq_right hτ]
      by_cases hτc : τ ∈ cands P hP
      · exact hwtOff τ hτc hτ
      · exact (massG_api P hP hzmem).2.2.2.1 τ
          (fun hsub => hτc (mem_cands_of_subset_carrier P hP hzmem hsub))
  obtain ⟨hSrel, hArel, hBrel, hsegrel⟩ :=
    stretchConst_relations P hP (m := (taperM β p P hP α M y)⁻¹) (inv_pos.mpr hcy0) hy hzeq hwtG
  have hcy : taperM β p P hP α M z = taperM β p P hP α M y := taperM_congr hsegrel
  have hAB : AOf β p P hP y + BOf β p P hP y = y := AOf_add_BOf P hP hy
  have hc0 : taperM β p P hP α M y ≠ 0 := ne_of_gt hcy0
  have hd0 : denC β p P hP (taperM β p P hP α M y)⁻¹ y ≠ 0 := ne_of_gt hdenCpos
  have hmain : (1 + (taperM β p P hP α M z - 1) * SOf β p P hP z)⁻¹ •
      (AOf β p P hP z + taperM β p P hP α M z • BOf β p P hP z)
        = AOf β p P hP y + BOf β p P hP y := by
    rw [hcy, hSrel, hArel, hBrel]
    simpa using (inv_algebra (c := (taperM β p P hP α M y)⁻¹) (S := SOf β p P hP y)
      (d := denC β p P hP (taperM β p P hP α M y)⁻¹ y) rfl hd0 (inv_ne_zero hc0))
  have hstr : stretch P hP β p α M z =
      (1 + (taperM β p P hP α M z - 1) * SOf β p P hP z)⁻¹ •
        (AOf β p P hP z + taperM β p P hP α M z • BOf β p P hP z) := by
    unfold Work.Geo.DualStretch.stretch Work.Geo.DualStretch.stretchM
    rw [ite_eq_left hzmem]
  rw [hstr]
  exact hmain.trans hAB

end Work.Geo.DualStretch
