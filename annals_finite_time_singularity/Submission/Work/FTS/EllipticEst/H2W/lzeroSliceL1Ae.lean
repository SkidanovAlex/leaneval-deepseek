import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Cores.pPureShiftAux.MajEst
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.pzIterSliceIntegrable
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.aSlotsTwoDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## The two analytic inputs -/



/-! ## The identification of the shifted `A`-slot -/



/-! ## The (clean) level-`0` slots of the radially shifted datum

`Cores/Pieces/TL2/shiftZeroSlots` proves the level-`0` slots of `D_z^j Ψ` for every `j ≤ k`, but
its *instantiation* passes the still-`sorry` dilation estimate `Dil.HkMem_dq_le`, so that module
is `sorryAx`-tainted.  The underlying proof `shiftZeroSlots_bound`/`shiftZeroSlots_aux` is
*parameterised* over the dilation estimate, and the estimate is proved (cleanly, elsewhere) as
`Cores.dilEstimate_fts` (`Cores/pPureShiftTwoAlpha4.lean`, from
`Cores.pPureShiftAux.HkMem_dq_and_HkSq_dq_le_self`).  Feeding the proved one gives an
axiom-clean version of the whole interface. -/

/-- **The level-`0` slots of the `j`-times radially shifted datum**, axiom-clean. -/
theorem shiftZeroSlots_clean (k j : ℕ) (hj : j ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      (∃ C₀ : ℝ, 0 < C₀ ∧ Work.FTS.EllipticEst.TT.EllWeak0 C₀) →
      α ^ 4 * Work.Spaces.HkSq α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ)
        + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
        ≤ C * Work.Spaces.HkSq α k F :=
  Work.FTS.EllipticEst.Cores.Pieces.TL2.shiftZeroSlots_aux
    (Work.FTS.EllipticEst.Cores.dilEstimate_fts)
    (Work.FTS.EllipticEst.Cores.Dil.dqIterTendsto) k j hj

/-- **The twice shifted level-`0` `B`-slot** (`j = 2`, `k = 2`), axiom-clean: this is the input
`X₂` of the route through `Mine.Tk_le_two_split`. -/
theorem HkSq_zero_pthIter_two_DzIter_two_le
    (h0 : ∃ C₀ : ℝ, 0 < C₀ ∧ Work.FTS.EllipticEst.TT.EllWeak0 C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
        ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨C, hCpos, hC⟩ := shiftZeroSlots_clean 2 2 le_rfl
  refine ⟨C, hCpos, ?_⟩
  intro α F Ψ hα hα4 hwk
  have h := hC α F Ψ hα hα4 hwk h0
  have hnn : 0 ≤ α ^ 4 * Work.Spaces.HkSq α 0
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) :=
    mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg _ _ _)
  linarith

/-- **The once shifted level-`0` `B`-slot** (`j = 1`, `k = 2`), axiom-clean: the input `X₁`. -/
theorem HkSq_zero_pthIter_two_DzIter_one_le
    (h0 : ∃ C₀ : ℝ, 0 < C₀ ∧ Work.FTS.EllipticEst.TT.EllWeak0 C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨C, hCpos, hC⟩ := shiftZeroSlots_clean 2 1 (by norm_num)
  refine ⟨C, hCpos, ?_⟩
  intro α F Ψ hα hα4 hwk
  have h := hC α F Ψ hα hα4 hwk h0
  have hnn : 0 ≤ α ^ 4 * Work.Spaces.HkSq α 0
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) :=
    mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg _ _ _)
  linarith

/-! ## Plumbing for the `Tk α 2 A`-reduction: a.e.-measurability of the slots

The forward comparison `Mine.Tk_le_two_split` / `Mine.Tk_le_two_terms` needs the (slice and
outer) integrability of the majorant `2 w(z)² (∂_θ²A)² σ₄(θ) + 8 (D_θ A · Wt)²`, i.e.
`a.e.`-strong measurability of the two pieces together with domination by honest `ℋ`-slots.
The mixed piece is handled by the *proved* `Mine.B_top_slot_bound.aesm_mixed_slot` /
`integrableOn_mixed_slot_of_HkMem`; the radial piece `(∂_θ²A)² w² σ₄` is handled here: `A` is
`C^∞` on the open quadrant, hence so is `∂_θ²A` *jointly*, and
`Work.Spaces.aesm_of_continuousOn_Qd` / `aesm_slice_of_continuousOn_Qd` apply. -/

/-- `∂_θ²A = pth (pth A)` is smooth on the open quadrant when `A` is. -/
theorem smoothOpen_pthIter_two {A : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 A) := by
  rw [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  exact (Work.FTS.EllipticEst.SmoothOpen.pth hA).pth



/-! ## A local weight identity (clean cone)

`sin(2θ)²·Wt(α,z,θ)² = w(z)²·sin(2θ)^{2-γ}`, i.e. `sin(2θ)²·Wt² = w²·σ₂` where
`σ₂ = sig2 γ`.  A local copy so that the integrability plumbing depends on no module outside
this file's own (clean) import cone; the identity is the one used to identify the `σ₂`-weighted
plain `θ`-derivative slot with `(D_θA·Wt)²`. -/

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_Iθ' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩


/-! ## Item 2: the reverse comparison of the second-order `θ`-slot

`(∂_θ²f)² · sin(2θ)^{4-γ} · w² ≤ 2 (D_θ²f · Wt)² + 8 (D_θf · Wt)²`, from the expansion
`D_θ²f = 2 cos(2θ) · D_θ f + sin(2θ)² · ∂_θ²f` and `cos² ≤ 1`.  A local copy (both the
expansion and the comparison) so that the integrability plumbing below depends on no module
outside this file's own clean import cone. -/



/-! ## The assembly -/


end

end Work.FTS.EllipticEst.Cores
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.lzeroSliceL1Ae =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H2W/lzeroSliceL1Ae` — the `L¹_θ`-control of the slices of `Lzero (∂_z^j Ψ)`

Target (`Work.FTS.EllipticEst.H2W.lzeroSliceL1Ae`): for a datum `(F, Ψ)` of the weak class
`WeakPos2 α F Ψ` (`0 < α ≤ 1/4`) and every `j ≤ 2`,

  `θ ↦ sinθ cos²θ · Lzero (∂_z^j Ψ)(z,θ)`

is integrable on `Iθ = [0,π/2]` for almost every `z > 0`.

## The route, and what is proved here

For `z > 0`, `θ ∈ (0,π/2)` the equation `bslOp α Ψ = F` is equivalent to

  `Lzero Ψ = F + α²z²∂_z²Ψ + α(5+α)z∂_zΨ`     (`lzero_level0`, proved here),

and `Lzero` has `θ`-only coefficients, so `∂_z` commutes with it on the open quadrant
(`Lzero_pz_eqOn`; by Clairaut `H2W.pz_pthIter_two_eqOn` and `Spaces.pz_pth_comm`).  Hence
`Lzero (∂_z^jΨ) = ∂_z^j(lev0)` on the open quadrant, which the Leibniz rules
`Work.FTS.H2.Q.pzIter_mul_local_sm` / `pzIter_sq_mul_sm` expand into a finite combination of
the slices `∂_z^mΨ` (`m ≤ 4`) and `∂_z^iF` (`i ≤ 2`) with polynomial-in-`z` coefficients:

  `j = 0`: `F + α²z²∂_z²Ψ + α(5+α)z∂_zΨ`;
  `j = 1`: `∂_zF + α²(2z∂_z²Ψ + z²∂_z³Ψ) + α(5+α)(∂_zΨ + z∂_z²Ψ)`;
  `j = 2`: `∂_z²F + α²(2∂_z²Ψ + 4z∂_z³Ψ + z²∂_z⁴Ψ) + α(5+α)(2∂_z²Ψ + z∂_z³Ψ)`.

Those two families are `sinθcos²θ`-integrable for a.e. `z > 0`:

* the source's slices (`i ≤ 2`) — `H2W.lzeroSliceFiber` (delivered),
  from the slicewise honesty `HkMem α 2 F` (`Work.Spaces.HkMem`);
* the datum's slices (`m ≤ 4`) — `H2W.PsiSlices.pzIterSliceIntegrable` (the chapter's open
  endpoint-rigidity input, imported below through the wrapper `pzIterSliceIntegrableInput`), the
  `θ`-endpoint structure of the weak class, i.e. the hard input of this node.

`Lzero (∂_z^jΨ)` therefore has `sinθcos²θ`-integrable slices, which is the target.
-/ 

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unnecessarySimpa false

noncomputable section

/-! ## The one analytic input of this node (the chapter's open bottleneck)

Everything below is proved; the target `lzeroSliceL1Ae` is assembled from it and from the single
input `pzIterSliceIntegrableInput`, which is imported (verbatim the same statement) from

  `Submission.Work.FTS.EllipticEst.H2W.PsiSlices.pzIterSliceIntegrable`
  (`Work.FTS.EllipticEst.H2W.PsiSlices.pzIterSliceIntegrable`):

for a.e. `z > 0` and every `m ≤ 4` the angular slice `θ ↦ ∂_z^mΨ(z,θ)·sinθcos²θ` is integrable on
`Iθ`.  It is the datum-side (`Ψ`-side) endpoint statement of the weak class `WeakPos2`; the
source-side (`F`-side) analogue is the delivered, `sorry`-free `H2W.lzeroSliceFiber` (used below).

**The statement is *not* obtained from the current tree.**  It is the chapter's documented open
bottleneck ("endpoint rigidity of the weak class", see `H2W/NOTES_lzeroSliceL1Ae.md` §3 and
`H2W/WeakPureAux/NOTES_weakPzPoleBound.md`, `H2W/NOTES_pzIterSliceGrowth3Loc.md`): the weak class
`WeakPos2` constrains only the *source* (`HkMem α 2 F`, and slicewise, for *every* `z > 0`), the
left-hand slots being deliberately absent, so the `θ`-endpoint behaviour of the slices has to be
extracted from the indicial structure of `Lzero1` (exponents `±1` at `π/2`, with the `t log t`
mode; ordinary point at `0`).  The statement is *strictly weaker* than the pole bound
`|∂_z^mΨ(z,θ)| ≤ C(θ⁻¹ + (π/2-θ)⁻¹)` pursued in the siblings: `φ(θ) = sinθcos²θ` dies like
`t²` at `π/2` and like `θ` at `0`, so any slice growth `o(t^{-3})` (resp. `o(θ^{-2})`) satisfies
it, while the pole bound is equivalent to boundedness of the slices.  It is *not* refuted by the
"mixture" datum of `NOTES_pzIterSliceGrowth3Loc.md` §3 (a `t^{-1}` pole whose source coefficient
is cancelled by a hidden `t log t` mode): that datum satisfies it, since
`∫ sinθcos²θ·t^{-1} = ∫ t < ∞`.

The dedicated module holds the whole reduction of this input (the `D_z`-shifted level identities,
the source-side slices `H2W.lzeroSliceFiber`, the "bad slice propagates to a `z`-derivative
neighbour" cascade lemmas, the variation-of-parameters bridge from an honest source, and the
covariance reduction to the single point `z = 1`); its last step is the same open endpoint
rigidity, so the input is *not* `sorry`-free yet.  As soon as it is, this node is done with no
further edit.  See `H2W/NOTES_lzeroSliceL1Ae.md` for the full account. -/

/-! ## Clairaut for `∂_z` against `∂_θ²` (local copy)

`Work.FTS.EllipticEst.H2W.pz_pthIter_two_eqOn` in `H2W/HkMem_zero_slices.lean` is the same
statement; it is reproduced here because that module (through `RPFresh.excess_finite`) does not
elaborate in the current tree, and this node needs only this one Clairaut step.  The proof is the
standard two-step one: the first-order Clairaut `Work.Spaces.pz_pth_comm` for `g` and for
`pth g`, glued by `Work.Spaces.pth_congr_of_isOpen` on the open quadrant `Q0`. -/


/-! ## Differentiability of the `z`-slices on the open quadrant -/

theorem differentiableAt_zslice {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    DifferentiableAt ℝ (fun z' => g z' θ) z :=
  (Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice hg hθ hz).differentiableAt

/-! ## The level-`0` form of the equation -/


/-! ## `∂_z` commutes with `Lzero` on the open quadrant -/



/-! ## Product rules (used by the Leibniz expansion of `Lzero (∂_z^jΨ)`) -/


/-- `∂_z(z²·u) = 2zu + z²∂_zu` on the open quadrant. -/
theorem pz_zsq_mul {u : ℝ → ℝ → ℝ} (hu : Work.FTS.EllipticEst.SmoothOpen u)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pz (fun z θ => z ^ 2 * u z θ) z θ
      = 2 * z * u z θ + z ^ 2 * Work.Spaces.pz u z θ := by
  have hd1 : DifferentiableAt ℝ (fun z' : ℝ => z' ^ 2) z := by fun_prop
  have hd2 : DifferentiableAt ℝ (fun z' : ℝ => u z' θ) z := differentiableAt_zslice hu hz hθ
  have hmul : deriv ((fun z' : ℝ => z' ^ 2) * (fun z' : ℝ => u z' θ)) z
      = deriv (fun z' : ℝ => z' ^ 2) z * u z θ + z ^ 2 * deriv (fun z' : ℝ => u z' θ) z :=
    deriv_mul hd1 hd2
  have hpow : deriv (fun z' : ℝ => z' ^ 2) z = 2 * z := by
    simpa using (hasDerivAt_pow 2 z).deriv
  show deriv (fun z' : ℝ => z' ^ 2 * u z' θ) z = 2 * z * u z θ + z ^ 2 * Work.Spaces.pz u z θ
  rw [show (fun z' : ℝ => z' ^ 2 * u z' θ)
      = (fun z' : ℝ => z' ^ 2) * (fun z' : ℝ => u z' θ) from rfl, hmul, hpow]
  simp only [Work.Spaces.pz]

/-! ## Linearity of `∂_z^j` on the open quadrant -/

/-- Congruence of `pzIter` on open sets. -/
theorem pzIter_congr_of_isOpen {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (k : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pzIter k f))
      (Function.uncurry (Work.Spaces.pzIter k g)) V := by
  induction k with
  | zero => exact h
  | succ k ih =>
      intro p hp
      show deriv (fun z' => Work.Spaces.pzIter k f z' p.2) p.1
        = deriv (fun z' => Work.Spaces.pzIter k g z' p.2) p.1
      exact Work.Spaces.pz_congr_of_isOpen hV ih hp

/-- `∂_z^j` commutes with multiplication by a constant. -/
theorem pzIter_const_mul (c : ℝ) (g : ℝ → ℝ → ℝ) (k : ℕ) :
    Work.Spaces.pzIter k (fun z θ => c * g z θ)
      = fun z θ => c * Work.Spaces.pzIter k g z θ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, ih, Work.Spaces.pzIter_succ]
      funext z θ
      exact deriv_const_mul_field c




/-! ## Pointwise product/linearity helpers and the level identities -/




/-! ## Pointwise forms of the three level identities -/




/-! ## The reduction -/


/-! ## The target -/

/-! ## The target -/


end

end Work.FTS.EllipticEst.H2W
end
