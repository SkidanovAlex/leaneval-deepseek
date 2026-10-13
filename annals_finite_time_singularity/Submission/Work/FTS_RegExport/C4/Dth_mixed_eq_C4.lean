import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.Blocks.alphaDz_pth_core_clean
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.StrongEps.HkMem_of_tendsto
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.C4

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 800000

/-!
# `D_θ` of a mixed derivative, at the finite order `C⁴`

The curvilinear operators `D_z f = z ∂_z f` and `D_θ f = sin(2θ) ∂_θ f` commute wherever the
datum is `C²` (Clairaut), so `D_θ (D_z^b D_θ^a f) = D_z^b D_θ^{a+1} f` — the identity behind
the definition `D_θ^{i+1} = D_θ ∘ D_θ^i` of `mixed`.

The existing proofs of this identity in the workspace (`Work.Spaces.Dth_DzIter_comm_eqOn`,
`Work.FTS.CoercivityFix.QuadPorts.DzIter_DthIter_comm_quad`, …) are stated for a datum which
is `C^∞` (or analytic) on an open set.  Here only the *finite* order is available: the datum
is `C⁴` on the open quadrant `Q0` and the total order `a + b + 1` of the derivatives involved
is `≤ 4`.  Since the proof of the identity only ever differentiates the datum `a + b + 1`
times, the same argument runs verbatim at the finite order, provided the `D`-calculus is
available at finite order — which it is, in
`Work.FTS.StrongEps.contDiffOn_uncurry_{pz,pth,Dz,Dth,DzIter,DthIter}_*`.

The key auxiliary is `Dth_DzIter_comm_fin`: `D_θ` commutes with `D_z^b` on an open set on
which the datum is `C^{b+1}`.  The induction on `b` moves one `D_z` past the `D_θ` by Clairaut
(which needs `C²` of `D_z^b g`, i.e. `C^{b+2}` of `g`), and the two sides of the resulting
identity `D_z (D_θ (D_z^b g)) = D_z (D_z^b (D_θ g))` are compared by the induction hypothesis
for the *same* open set, using `pz_congr_of_isOpen`.
-/

/-- **Commutation of `D_θ` with the radial iterates, at the finite order `b + 1`.**

If `g` is `C^{b+1}` on an open set `V`, then `D_θ (D_z^b g) = D_z^b (D_θ g)` on `V`.

(The induction uses `C^{b+2}` of `g` at the step `b ↦ b+1` — Clairaut for `D_z^b g` — which is
more than the hypothesis of the statement needs; the statement itself is phrased with the
minimal order `b + 1` so that it can be applied to `g = D_θ^a f` of a `C⁴` datum.) -/
theorem Dth_DzIter_comm_fin (b : ℕ) {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ (b + 1) (Function.uncurry g) V) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DzIter b g)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.Dth g))) V := by
  induction b with
  | zero => intro y hy; rfl
  | succ b ih =>
      -- `g` is `C^{b+1}` as well, and `D_z^b g` is `C²`
      have hb : ContDiffOn ℝ (b + 1) (Function.uncurry g) V :=
        h.of_le (by exact_mod_cast (show (b + 1 : ℕ) ≤ b + 1 + 1 by omega))
      have hih : Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DzIter b g)))
          (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.Dth g))) V := ih hb
      have h2b : ContDiffOn ℝ (2 + b) (Function.uncurry g) V := by
        have key : ((2 : WithTop ℕ∞) + (b : WithTop ℕ∞)) = ((b : WithTop ℕ∞) + 1 + 1) := by
          exact_mod_cast (show (2 + b : ℕ) = b + 1 + 1 by omega)
        rw [key]
        exact h
      have hC2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.DzIter b g)) V :=
        Work.FTS.StrongEps.contDiffOn_uncurry_DzIter_shift hV b 2 h2b
      intro y hy
      have hcy : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter b g)) y :=
        hC2.contDiffAt (hV.mem_nhds hy)
      -- Clairaut at `y` for `D_z^b g`
      have hcomm : Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b g)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DzIter b g)) y.1 y.2 :=
        (Work.Spaces.Dz_Dth_comm hcy).symm
      show Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b g)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.Dth g)) y.1 y.2
      rw [hcomm]
      -- the two functions inside the outer `D_z` agree on the open set `V`
      show y.1 * Work.Spaces.pz (Work.Spaces.Dth (Work.Spaces.DzIter b g)) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.Dth g)) y.1 y.2
      rw [Work.Spaces.pz_congr_of_isOpen hV hih hy]

/-- **The `C⁴` shift identity**: for a datum `f` of class `C⁴` on the open quadrant `Q0` and
`a + b + 1 ≤ 4`, the operator `D_θ` shifts the angular index of the mixed derivative,
`D_θ (D_z^b D_θ^a f) = D_z^b D_θ^{a+1} f`, at every interior point of `Q0`. -/
theorem Dth_mixed_eq_C4 {f : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (b a : ℕ) (hab : a + b + 1 ≤ 4) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ = Work.Spaces.mixed b (a + 1) f z θ := by
  have hy : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ⟩
  -- `D_θ^a f` is `C^{b+1}`, since `f` is `C^{a+b+1}`
  have hab2 : (b + 1 + a : ℕ) ≤ 4 := by omega
  have h1 : ContDiffOn ℝ (b + 1 + a) (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    hF.of_le (Nat.cast_le.mpr hab2)
  have hfin : ContDiffOn ℝ (b + 1) (Function.uncurry (Work.Spaces.DthIter a f))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_DthIter_shift
      Work.FTS.EllipticEst.isOpen_Q0 a (b + 1) h1
  have hpt := (Dth_DzIter_comm_fin b Work.FTS.EllipticEst.isOpen_Q0 hfin) hy
  rw [show Work.Spaces.mixed b a f
      = Work.Spaces.DzIter b (Work.Spaces.DthIter a f) from rfl]
  rw [show Work.Spaces.mixed b (a + 1) f
      = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter a f)) from rfl]
  simpa only [Function.uncurry] using hpt

end Work.FTS_RegExport.C4
