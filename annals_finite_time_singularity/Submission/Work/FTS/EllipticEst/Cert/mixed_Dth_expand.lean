import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.pz_aux
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.FTS.EllipticEst.LopIterSinDefs
import Submission.Work.FTS.EllipticEst.Lop_iter_mul
import Submission.Work.FTS.EllipticEst.sd_lop_iter_sin_bound
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le
import Submission.Work.FTS.H2.STSigma

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The expansion of the `D_θ`-iterates of `D_θ f` in the `θ`-jets of `f`.**

`D_θ f = sin(2θ)·∂_θ f`, and `D_θ` is a derivation, so the iterated Leibniz rule gives

  `D_θ^n (D_θ f) = Σ_a C(n,a) · D_θ^a(sin 2θ) · D_θ^{n-a}(∂_θ f)`,

and `D_θ^a (sin 2θ) = sin(2θ)·hfun a θ` (`sd_LopIter_sin_factor`).  Applying `D_z^j` (which
commutes with `D_θ` and does not see the `θ`-only coefficients, `DzIter_sum_const_mul_eqOn`)
gives the stated expansion, indexed by `m = n - a`. -/
theorem mixed_Dth_expand (n j : ℕ) {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f)
    {z θ : ℝ} (hz : (z, θ) ∈ Work.Spaces.nbhU) :
    Work.Spaces.mixed j n (Work.Spaces.Dth f) z θ
      = ∑ m ∈ Finset.range (n + 1),
          (n.choose (n - m) : ℝ) * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun (n - m) θ)
            * Work.Spaces.mixed j m (Work.Spaces.pth f) z θ := by
  have hUo : IsOpen (Work.Spaces.nbhU) := isOpen_Ioi.prod isOpen_Ioo
  have hA : ContDiffOn ℝ ⊤ (fun θ' : ℝ => Real.sin (2 * θ'))
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
    (Real.contDiff_sin (n := ⊤)).comp_contDiffOn
      ((contDiffOn_const (c := (2 : ℝ))).mul contDiffOn_id)
  -- `D_θ^a (sin 2θ) = sin(2θ)·hfun a θ`
  have hcoef : ∀ a : ℕ, ∀ z' θ' : ℝ,
      Work.Spaces.DthIter a (fun _ θ'' : ℝ => Real.sin (2 * θ'')) z' θ'
        = Real.sin (2 * θ') * Work.FTS.EllipticEst.hfun a θ' := by
    intro a z' θ'
    rw [Work.FTS.LocData.DthIter_rad_eq]
    exact congrFun (Work.FTS.EllipticEst.sd_LopIter_sin_factor a) θ'
  -- the `D_θ`-expansion, as an identity on the strip
  have hfunc : Set.EqOn (Function.uncurry (Work.Spaces.DthIter n (Work.Spaces.Dth f)))
      (Function.uncurry (fun z θ' => ∑ a ∈ Finset.range (n + 1),
        (n.choose a : ℝ) * (Real.sin (2 * θ') * Work.FTS.EllipticEst.hfun a θ')
          * Work.Spaces.DthIter (n - a) (Work.Spaces.pth f) z θ')) Work.Spaces.nbhU := by
    intro p hp
    obtain ⟨z', θ'⟩ := p
    have hB : ContDiffOn ℝ ⊤ (fun θ'' : ℝ => Work.Spaces.pth f z' θ'')
        (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
      (hsm.pth).comp ((contDiffOn_const (c := z')).prodMk contDiffOn_id)
        (fun θ'' hθ'' => ⟨hp.1, hθ''⟩)
    have h := Work.Spaces.DthIter_mul n (fun _ θ'' : ℝ => Real.sin (2 * θ''))
      (Work.Spaces.pth f) z' (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) isOpen_Ioo hA hB θ' hp.2
    have key : Work.Spaces.DthIter n (Work.Spaces.Dth f) z' θ'
        = ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
            * (Work.Spaces.DthIter a (fun _ θ'' : ℝ => Real.sin (2 * θ'')) z' θ'
              * Work.Spaces.DthIter (n - a) (Work.Spaces.pth f) z' θ') := by
      have heq : Work.Spaces.DthIter n (Work.Spaces.Dth f) z' θ'
          = Work.Spaces.DthIter n
              (fun z θ'' => Real.sin (2 * θ'') * Work.Spaces.pth f z θ'') z' θ' := rfl
      rw [heq]
      exact h
    change Work.Spaces.DthIter n (Work.Spaces.Dth f) z' θ'
      = ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
          * (Real.sin (2 * θ') * Work.FTS.EllipticEst.hfun a θ')
            * Work.Spaces.DthIter (n - a) (Work.Spaces.pth f) z' θ'
    rw [key]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoef a z' θ']
    ring
  -- `D_z^j` distributes over the sum with its `θ`-only coefficients
  have hF : ∀ a ∈ Finset.range (n + 1),
      ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DthIter (n - a) (Work.Spaces.pth f)))
        Work.Spaces.nbhU :=
    fun a _ => Work.Spaces.smoothNbhd_DthIter (hsm.pth) (n - a)
  have hstep1 := Work.FTS.H2.DzIter_congr_of_isOpen hUo hfunc j
  have hstep2 := Work.FTS.H2.DzIter_sum_const_mul_eqOn (Finset.range (n + 1))
    (fun a θ' => (n.choose a : ℝ) * (Real.sin (2 * θ') * Work.FTS.EllipticEst.hfun a θ'))
    (fun a => Work.Spaces.DthIter (n - a) (Work.Spaces.pth f)) hUo hF j
  -- assemble at the point `(z,θ)`
  have hpoint : Work.Spaces.mixed j n (Work.Spaces.Dth f) z θ
      = ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
          * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun a θ)
            * Work.Spaces.mixed j (n - a) (Work.Spaces.pth f) z θ := by
    have h1 : Work.Spaces.DzIter j (Work.Spaces.DthIter n (Work.Spaces.Dth f)) z θ
        = Work.Spaces.DzIter j (fun z θ' => ∑ a ∈ Finset.range (n + 1),
            (n.choose a : ℝ) * (Real.sin (2 * θ') * Work.FTS.EllipticEst.hfun a θ')
              * Work.Spaces.DthIter (n - a) (Work.Spaces.pth f) z θ') z θ :=
      hstep1 hz
    have h2 : Work.Spaces.DzIter j (fun z θ' => ∑ a ∈ Finset.range (n + 1),
            (n.choose a : ℝ) * (Real.sin (2 * θ') * Work.FTS.EllipticEst.hfun a θ')
              * Work.Spaces.DthIter (n - a) (Work.Spaces.pth f) z θ') z θ
        = ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
            * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun a θ)
              * Work.Spaces.DzIter j (Work.Spaces.DthIter (n - a) (Work.Spaces.pth f)) z θ :=
      hstep2 hz
    rw [Work.Spaces.mixed, h1, h2]
    exact Finset.sum_congr rfl (fun a _ => rfl)
  -- reindex `a ↦ m = n - a`
  rw [hpoint, ← Finset.sum_range_reflect (fun a => (n.choose a : ℝ)
        * (Real.sin (2 * θ) * Work.FTS.EllipticEst.hfun a θ)
          * Work.Spaces.mixed j (n - a) (Work.Spaces.pth f) z θ) (n + 1)]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hm' : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hidx : n + 1 - 1 - m = n - m := by omega
  rw [hidx, Nat.sub_sub_self hm']

end Work.FTS.EllipticEst.Cert
