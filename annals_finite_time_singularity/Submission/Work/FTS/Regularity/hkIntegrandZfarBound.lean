import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.sin2_parseval_aesm
import Submission.Work.FTS.LocData.DzIter_FM_Fstar_abs_le
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.Spaces.bt_f_bound
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.mixed_Dth_expand =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.FinalClock.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

namespace Work.FTS.FinalClock

/-! ## Squeezing the integrals -/





/-! ## Exponential squeezing of the amplitudes -/







/-! ## Integrability: the blow-up time is finite -/



/-! ## The product identity and the `lamfun` relation -/




end Work.FTS.FinalClock
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_FstarRadial =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false










end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
end
-- ===== merged: Submission.Work.FTS.Regularity.hkIntegrandZfarBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Regularity

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 1. The far cut-off at scale `4` and its separated product structure -/



/-- The angular factor `-(β/c(β))·Γ(θ)` of the profile `F_*(β)`. -/
noncomputable def angF (β : ℝ) (θ : ℝ) : ℝ :=
  -(β / Work.Spaces.c β) * Work.Spaces.Gam β θ

/-- The far part of the profile `F_*(β)` at scale `4`, as a function of `(z,θ)`. -/
noncomputable def fcut (β : ℝ) (z θ : ℝ) : ℝ :=
  -Work.Construction.Fstar β z θ * (1 - Work.Stability.chi (z / 4))



theorem angF_apply (β θ : ℝ) : angF β θ = -(β / Work.Spaces.c β) * Work.Spaces.Gam β θ := rfl



/-! ## 2. Separation of variables for `D_z` and `D_θ` -/

/-- `Z = z∂_z` commutes with multiplication by a constant. -/
theorem Zop_const_mul (c : ℝ) (B : ℝ → ℝ) :
    Work.Spaces.Zop (fun z => c * B z) = fun z => c * Work.Spaces.Zop B z := by
  funext z
  simp only [Work.Spaces.Zop]
  rw [deriv_const_mul_field]
  ring

/-- The iterates of `Z = z∂_z` commute with multiplication by a constant. -/
theorem Zop_iter_const_mul (j : ℕ) (c : ℝ) (B : ℝ → ℝ) :
    (Work.Spaces.Zop^[j]) (fun z => c * B z) = fun z => c * (Work.Spaces.Zop^[j]) B z := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', Zop_const_mul]

/-- **`D_θ` on a separated product** acts on the `θ`-factor. -/
theorem DthIter_sep (i : ℕ) (A B : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun z θ => A θ * B z) z θ = (Work.Spaces.dthU^[i]) A θ * B z :=
  Work.Spaces.DthIter_decomp i A B z θ

/-- **`D_z` on a separated product** acts on the `z`-factor. -/
theorem DzIter_sep (j : ℕ) (C B : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z θ => C θ * B z) z θ = C θ * (Work.Spaces.Zop^[j]) B z := by
  have h1 : (fun z' => Work.Spaces.DzIter j (fun z θ => C θ * B z) z' θ)
      = (fun z' => (Work.Spaces.Zop^[j]) (fun z => C θ * B z) z') := by
    funext z'
    exact congrFun (Work.FTS.LocData.Zop_iterate_slice j (fun z θ => C θ * B z) θ) z'
  rw [congrFun h1 z, congrFun (Zop_iter_const_mul j (C θ) B) z]



/-! ## 3. Smoothness of the two radial factors on `(-1,∞)` -/



/-! ## 4. The radial bound `|Z^j ψ(z)| ≤ K/z` for `z ≥ 4`, `j ≤ 4` -/


/-! ## 5. Angular bounds -/

/-- The iterates of `d_θ = sin(2θ)∂_θ` commute with multiplication by a constant. -/
theorem dthU_iter_const_mul (i : ℕ) (c : ℝ) (B : ℝ → ℝ) :
    (Work.Spaces.dthU^[i]) (fun θ => c * B θ) = fun θ => c * (Work.Spaces.dthU^[i]) B θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply',
        Work.Spaces.dthU_const_mul]


/-! ## 6. Elementary weight inequalities -/


/-! ## 7. The two sum bounds -/



/-! ## 8. Assembly -/



/-! ## 9. The requested lemma -/


end Work.FTS.Regularity
end
end
