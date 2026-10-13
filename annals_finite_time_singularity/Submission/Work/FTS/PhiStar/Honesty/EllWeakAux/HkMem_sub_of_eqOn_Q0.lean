import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.Cores.DiagEstEllT.HkMem_of_add_dominated_open
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.HkIntegrand_add_le_open
import Submission.Work.FTS.LocData.HkIntegrand_neg
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.EllWeakAux

open MeasureTheory Set Filter
open scoped Real Topology

/-! ## `ℋ^k`-membership is a property of the values on the open quadrant

The lemma requested here is a bookkeeping statement about `Work.Spaces.HkMem`: the `ℋ^k`-integrand
is built from the *local* operators `D_z^i` and `D_z^j D_θ^i` together with weights depending only
on `(z,θ)`, so two functions which agree on the open quadrant `Q0 = (0,∞) × (0,π/2)` have the same
integrand at every interior point, and the boundary lines `z = 0`, `sin(2θ) = 0` are null.

The proof therefore has two halves:

* **the difference is in `ℋ^k`**: with `SmoothOpen` data the `ℋ^k`-integrand is subadditive for
  differences, `HkIntegrand α k (u - v) ≤ 2·HkIntegrand α k u + 2·HkIntegrand α k v` on the closed
  quadrant (`HkIntegrand_sub_le_open` below, obtained from the public addition form
  `Work.FTS.EllipticEst.HkIntegrand_add_le_open` together with the sign invariance
  `Work.FTS.EllipticEst.HkIntegrand_neg` and the equivalence of the difference with `u + (-v)`);
  the closure of `ℋ^k` under an a.e. angular domination
  (`Work.FTS.EllipticEst.Cores.DiagEstEllT.HkMem_of_add_dominated_open`) then gives `u - v ∈ ℋ^k`;
* **the transfer to `w`**: `w` agrees with `u - v` on `Q0`, so
  `Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0` carries the membership across.

Note that `w` is completely arbitrary off `Q0`; only its values there are used.
-/

/-- **Pointwise subadditivity of the `ℋ^k`-integrand for a difference**, on the closed quadrant
`Iz ×ˢ Iθ`, for data which are `C^∞` on the open quadrant:

`HkIntegrand α k (f - g) ≤ 2·HkIntegrand α k f + 2·HkIntegrand α k g`.

(The boundary lines are trivial: at `z = 0` and at `sin(2θ) = 0` the integrand vanishes
identically, and it is nonnegative everywhere.  On the interior, `f - g = f + (-g)` and the
addition form of the subadditivity applies, the sign invariance killing the `-g`.) -/
theorem HkIntegrand_sub_le_open (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ - g z θ) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ
          + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  -- the signed `-g` summand has the same integrand as `g`
  have hneg : Work.Spaces.HkIntegrand α k (fun z θ => -g z θ)
      = Work.Spaces.HkIntegrand α k g := by
    funext z θ
    exact Work.FTS.LocData.HkIntegrand_neg α k g z θ
  intro z hz θ hθ
  by_cases hz0 : z = 0
  · -- radial boundary: the weight `w 0 = 0` kills the integrand
    rw [hz0, Work.FTS.LocData.HkIntegrand_zero_fst]
    have h1 := Work.Spaces.HkIntegrand_nonneg α k f 0 θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α k g 0 θ
    linarith
  by_cases hs : Real.sin (2 * θ) = 0
  · -- angular boundary: every summand carries a factor `sin(2θ)`
    rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k
      (fun z θ => f z θ - g z θ) z θ hs]
    have h1 := Work.Spaces.HkIntegrand_nonneg α k f z θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α k g z θ
    linarith
  · -- interior point of the quadrant
    have hzge : 0 ≤ z := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hz
    have hzpos : 0 < z := lt_of_le_of_ne hzge (Ne.symm hz0)
    have hbnd : 0 ≤ θ ∧ θ ≤ Real.pi / 2 := by
      simpa only [Work.Spaces.Iθ, Set.mem_Icc] using hθ
    have hθ1 : 0 < θ := by
      rcases eq_or_lt_of_le hbnd.1 with h | h
      · exact absurd (by rw [← h]; simp) hs
      · exact h
    have hθ2 : θ < Real.pi / 2 := by
      rcases lt_or_eq_of_le hbnd.2 with h | h
      · exact h
      · exact absurd (by rw [h, show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring,
            Real.sin_pi]) hs
    -- the difference is the sum with the negated second summand
    have he : (fun z θ => f z θ - g z θ)
        = fun z θ => f z θ + (fun z θ => -g z θ) z θ := by
      funext z θ; exact sub_eq_add_neg _ _
    rw [he]
    have h := Work.FTS.EllipticEst.HkIntegrand_add_le_open α k hf
      (Work.FTS.EllipticEst.Cert.smoothOpen_neg_bsl hg) hz hθ
    rw [hneg] at h
    exact h

theorem HkMem_sub_of_eqOn_Q0 (α : ℝ) (k : ℕ) {u v w : ℝ → ℝ → ℝ}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v)
    (hmu : Work.Spaces.HkMem α k u) (hmv : Work.Spaces.HkMem α k v)
    (hw : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → w z θ = u z θ - v z θ) :
    Work.Spaces.HkMem α k w := by
  have hpt := HkIntegrand_sub_le_open (α := α) (k := k) hu hv
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => u z θ - v z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl hu hv
  -- the a.e. angular domination by the (integrable) majorant `2·HkIntegrand u + 2·HkIntegrand v`
  have hle : ∀ z ∈ Work.Spaces.Iz,
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α k (fun z θ => u z θ - v z θ) z θ
          ≤ 2 * Work.Spaces.HkIntegrand α k u z θ
            + 2 * Work.Spaces.HkIntegrand α k v z θ :=
    fun z hz => MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => hpt z hz θ hθ)
  have hdd : Work.Spaces.HkMem α k (fun z θ => u z θ - v z θ) :=
    Work.FTS.EllipticEst.Cores.DiagEstEllT.HkMem_of_add_dominated_open α k hsm hmu hmv hle
  -- transfer along the agreement on the open quadrant
  exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k hdd
    (fun z hz θ hθ => (hw z hz θ hθ.1 hθ.2).symm)

end Work.FTS.PhiStar.Honesty.EllWeakAux
