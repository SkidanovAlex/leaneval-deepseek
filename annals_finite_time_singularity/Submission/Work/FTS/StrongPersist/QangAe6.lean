import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.QangOpen
import Submission.Work.FTS.StrongPersist.QangDiff6
import Submission.Work.FTS.StrongPersist.QangSq6
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `QangAe6` — the level-six `z`-calculus of the angular moments, almost everywhere

`Work.Elliptic.Qang g i z = ∫_θ Kθ(θ)·(D_z^i g)(z,θ) dθ` is the `i`-th angular moment of `g`.
The level-four chain of `Work.FTS.OpenPkg.QangOpen` proves, for a datum which is `C^∞` on the
open quadrant and lies in `ℋ⁴`, that

  `D_z^i (Qang g 0) = Qang g i`  almost everywhere, for `i ≤ 4`

(`DzdIter_Qang_ae_open`), while `QangDiff6` of this directory upgrades the two ingredients of
that chain — the `z`-differentiation of the moments and their continuity on `(0,∞)` — to
levels `j ≤ 4` and `j ≤ 5` respectively, for a datum in `ℋ⁶`.

Here we assemble the two: the *pointwise* identity `D_z^i (Qang g 0) = Qang g i` for `i ≤ 5`
is the abstract induction `DzdIter_eq_of_hasDerivAt'` run on the level-`j ≤ 4` derivative
facts, and the last level `i = 6` follows by transporting the *level-four* a.e. statement to
the shift `D_z²g` (via `Qang g (k+2) = Qang (D_z²g) k`, `Qang_DzIter_two_shift`), which reads

  `D_z⁴ (Qang g 2) = Qang g 6`  a.e.,

and then replacing `Qang g 2` by `D_z²(Qang g 0)` on `(0,∞)` (the pointwise identity at level
`i = 2`), i.e. `D_z⁴(Qang g 2) = D_z⁶(Qang g 0)`.

The only Fubini/Hardy input is inherited: `HkMem α 6 g` gives `HkMem α 4 (D_z²g)`
(`HkMem_Dz_of_smoothOpen` twice), which is exactly what `DzdIter_Qang_ae_open` consumes.
-/

namespace Work.FTS.StrongPersist

open scoped Topology

/-! ## Transport of the `z ∂_z`-calculus along an equality on `(0,∞)` -/

/-- If two functions of `z` agree on the open half-line `(0,∞)`, then their `z∂_z`-derivatives
agree at every point of `(0,∞)` (the half-line is a neighbourhood). -/
theorem Dzd_congr_Ioi {u v : ℝ → ℝ} (h : ∀ y, 0 < y → u y = v y) {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.Dzd u z = Work.Elliptic.Dzd v z := by
  have hev : u =ᶠ[nhds z] v := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact h y hy
  rw [Work.Elliptic.Dzd, Work.Elliptic.Dzd, hev.deriv_eq]

/-- If two functions of `z` agree on the open half-line `(0,∞)`, then so do all their
iterated `z∂_z`-derivatives. -/
theorem DzdIter_congr_Ioi {u v : ℝ → ℝ} (h : ∀ y, 0 < y → u y = v y) :
    ∀ k : ℕ, ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter k u z = Work.Elliptic.DzdIter k v z := by
  intro k
  induction k with
  | zero => intro z hz; exact h z hz
  | succ k ih =>
      intro z hz
      rw [Work.Elliptic.DzdIter_succ]
      exact Dzd_congr_Ioi (fun y hy => ih y hy) hz

/-- `DzdIter` is additive in its order: `DzdIter (m+n) u = DzdIter m (DzdIter n u)`. -/
theorem DzdIter_add (m n : ℕ) (u : ℝ → ℝ) :
    Work.Elliptic.DzdIter (m + n) u
      = Work.Elliptic.DzdIter m (Work.Elliptic.DzdIter n u) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show (m + 1) + n = (m + n) + 1 from Nat.succ_add m n]
      show Work.Elliptic.Dzd (Work.Elliptic.DzdIter (m + n) u)
        = Work.Elliptic.Dzd (Work.Elliptic.DzdIter m (Work.Elliptic.DzdIter n u))
      rw [ih]

/-! ## The abstract induction: a divided derivative at every `z > 0` gives all iterates -/

/-- **Pointwise `z∂_z`-calculus from divided derivatives.**  If `u = Φ 0` and
`(Φ j)' z = Φ (j+1) z / z` for every `j ≤ N` and every `z > 0`, then
`D_z^i u = Φ i` for every `i ≤ N+1` at every `z > 0`.

(`D_z = z∂_z`, so `D_z^{i+1} u = z∂_z(D_z^i u)`; the induction step replaces `D_z^i u` by `Φ i`
in a neighbourhood of `z` — which is legitimate because `z > 0` — and then uses the divided
derivative of `Φ i`, the division by `z` being undone by the multiplication by `z`.) -/
theorem DzdIter_eq_of_hasDerivAt' {u : ℝ → ℝ} {Φ : ℕ → ℝ → ℝ} (N : ℕ)
    (h0 : ∀ z, u z = Φ 0 z)
    (hder : ∀ j ≤ N, ∀ z, 0 < z → HasDerivAt (Φ j) (Φ (j + 1) z / z) z) :
    ∀ i ≤ N + 1, ∀ z, 0 < z → Work.Elliptic.DzdIter i u z = Φ i z := by
  intro i
  induction i with
  | zero => intro _ z _; exact h0 z
  | succ i ih =>
      intro hi z hz
      have hprev : Work.Elliptic.DzdIter i u =ᶠ[nhds z] Φ i := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact ih (by omega) w hw
      rw [Work.Elliptic.DzdIter_succ, Work.Elliptic.Dzd]
      rw [hprev.deriv_eq, (hder i (by omega) z hz).deriv]
      rw [mul_comm z, div_mul_cancel₀ _ (ne_of_gt hz)]

/-! ## The two level-six inputs -/

/-- The angular moments of the level-six datum are differentiable at every `z > 0` up to order
`j ≤ 4`, so the identity `D_z^i (Qang g 0) = Qang g i` holds **pointwise** for `i ≤ 5`. -/
theorem Qang_DzdIter_pointwise {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 6 g) :
    ∀ i ≤ 5, ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z) z
        = Work.Elliptic.Qang g i z :=
  DzdIter_eq_of_hasDerivAt' 4 (fun _ => rfl)
    (fun j hj z hz => (QangDiff6 hO hmem).1 j hj z hz)

/-- **The level-six identity transported to the shift `D_z²g`.**  The level-four a.e. theorem
`DzdIter_Qang_ae_open` applied to `D_z²g ∈ ℋ⁴` (which is `HkMem_Dz_of_smoothOpen` twice) gives
`D_z^i (Qang (D_z²g) 0) = Qang (D_z²g) i` a.e.; rewriting both sides with
`Qang_DzIter_two_shift` (`Qang g (k+2) = Qang (D_z²g) k`) yields the identity for the moments of
`g` shifted by two. -/
theorem Qang_DzdIter_shift_ae {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 6 g) :
    ∀ᵐ z ∂(MeasureTheory.volume), 0 < z → ∀ i ∈ Finset.range 5,
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 2 z) z
        = Work.Elliptic.Qang g (i + 2) z := by
  -- `D_z²g` lies in `ℋ⁴`: descend twice along the `D_z`-shift.
  have hmem5 : Work.Spaces.HkMem α 5 (Work.Spaces.Dz g) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 5 hO hmem
  have hmem4₂ : Work.Spaces.HkMem α 4 (Work.Spaces.DzIter 2 g) := by
    have h : Work.Spaces.HkMem α 4 (Work.Spaces.Dz (Work.Spaces.Dz g)) :=
      Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hO.Dz hmem5
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using h
  have hO₂ : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 2 g) := hO.DzIter 2
  filter_upwards [Work.FTS.OpenPkg.QangOpen.DzdIter_Qang_ae_open hO₂ hmem4₂] with z hz
  intro hzpos i hi
  have h1 := hz hzpos i hi
  have hfun : (fun z => Work.Elliptic.Qang (Work.Spaces.DzIter 2 g) 0 z)
      = fun z => Work.Elliptic.Qang g 2 z :=
    funext (fun z => (congrFun (Qang_DzIter_two_shift g 0) z).symm)
  rw [hfun] at h1
  rw [← congrFun (Qang_DzIter_two_shift g i) z] at h1
  exact h1

/-! ## The target -/

theorem QangAe6 {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 6 g) :
    ∀ᵐ z ∂(MeasureTheory.volume), 0 < z → ∀ i ∈ Finset.range 7,
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z) z = Work.Elliptic.Qang g i z := by
  -- the pointwise identity at every level `i ≤ 5`
  have hpoint := Qang_DzdIter_pointwise hO hmem
  -- `Qang g 2` agrees on `(0,∞)` with `D_z²(Qang g 0)`, whence the fourth iterate of the
  -- former is the sixth iterate of the latter
  have htransfer : ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter 4 (fun w => Work.Elliptic.Qang g 2 w) z
        = Work.Elliptic.DzdIter 6 (fun w => Work.Elliptic.Qang g 0 w) z := by
    intro z hz
    have h2 : ∀ y, 0 < y → (fun w => Work.Elliptic.Qang g 2 w) y
        = Work.Elliptic.DzdIter 2 (fun w => Work.Elliptic.Qang g 0 w) y :=
      fun y hy => (hpoint 2 (by norm_num) y hy).symm
    calc Work.Elliptic.DzdIter 4 (fun w => Work.Elliptic.Qang g 2 w) z
        = Work.Elliptic.DzdIter 4
            (Work.Elliptic.DzdIter 2 (fun w => Work.Elliptic.Qang g 0 w)) z :=
          DzdIter_congr_Ioi h2 4 z hz
      _ = Work.Elliptic.DzdIter (4 + 2) (fun w => Work.Elliptic.Qang g 0 w) z :=
          congrFun (DzdIter_add 4 2 (fun w => Work.Elliptic.Qang g 0 w)).symm z
      _ = Work.Elliptic.DzdIter 6 (fun w => Work.Elliptic.Qang g 0 w) z := by norm_num
  filter_upwards [Qang_DzdIter_shift_ae hO hmem] with z hz
  intro hzpos i hi
  have hi6 : i ≤ 6 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rcases Nat.lt_or_ge i 6 with hlt | hge
  · exact hpoint i (by omega) z hzpos
  · have hieq : i = 6 := by omega
    subst hieq
    exact (htransfer z hzpos).symm.trans (hz hzpos 4 (by decide))

end Work.FTS.StrongPersist
