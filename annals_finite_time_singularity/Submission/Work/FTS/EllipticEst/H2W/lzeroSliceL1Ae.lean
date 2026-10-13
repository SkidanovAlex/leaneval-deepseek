import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.PropH2Base
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm
import Submission.Work.FTS.H2.Q.Base
import Submission.Work.FTS.EllipticEst.H2W.lzeroSliceFiber
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.pzIterSliceIntegrable
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen

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
theorem pzIterSliceIntegrableInput : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.WeakPos2 α F Ψ →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∀ m : ℕ, m ≤ 4 →
        MeasureTheory.IntegrableOn
          (fun θ : ℝ => Work.Spaces.pzIter m Ψ z θ * Work.Elliptic.sinCos2 θ)
          Work.Spaces.Iθ :=
  Work.FTS.EllipticEst.H2W.PsiSlices.pzIterSliceIntegrable

/-! ## Clairaut for `∂_z` against `∂_θ²` (local copy)

`Work.FTS.EllipticEst.H2W.pz_pthIter_two_eqOn` in `H2W/HkMem_zero_slices.lean` is the same
statement; it is reproduced here because that module (through `RPFresh.excess_finite`) does not
elaborate in the current tree, and this node needs only this one Clairaut step.  The proof is the
standard two-step one: the first-order Clairaut `Work.Spaces.pz_pth_comm` for `g` and for
`pth g`, glued by `Work.Spaces.pth_congr_of_isOpen` on the open quadrant `Q0`. -/

theorem lzs_pz_pthIter_two_eqOn {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Set.EqOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pthIter 2 g)))
      (Function.uncurry (Work.Spaces.pthIter 2 (Work.Spaces.pz g)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have h2 : ∀ p ∈ Work.FTS.EllipticEst.Q0,
      ContDiffAt ℝ 2 (Function.uncurry g) p := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Work.FTS.EllipticEst.DzAmgm.contDiffAt_two_of_mem hg hz ⟨hθ0, hθ1⟩
  have h2' : ∀ p ∈ Work.FTS.EllipticEst.Q0,
      ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth g)) p := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Work.FTS.EllipticEst.DzAmgm.contDiffAt_two_of_mem (hg.pth) hz ⟨hθ0, hθ1⟩
  have hEqOn : Set.EqOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth g)))
      (Function.uncurry (Work.Spaces.pth (Work.Spaces.pz g))) Work.FTS.EllipticEst.Q0 :=
    fun p hp => Work.Spaces.pz_pth_comm (h2 p hp)
  intro p hp
  have e2 : Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth g)) p.1 p.2
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth g)) p.1 p.2 :=
    Work.Spaces.pz_pth_comm (h2' p hp)
  have e1 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth g)) p.1 p.2
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz g)) p.1 p.2 :=
    Work.Spaces.pth_congr_of_isOpen (f := Work.Spaces.pz (Work.Spaces.pth g))
      (f' := Work.Spaces.pth (Work.Spaces.pz g)) Work.FTS.EllipticEst.isOpen_Q0 hEqOn hp
  show Work.Spaces.pz (Work.Spaces.pthIter 2 g) p.1 p.2
      = Work.Spaces.pthIter 2 (Work.Spaces.pz g) p.1 p.2
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  exact e2.trans e1

/-! ## Differentiability of the `z`-slices on the open quadrant -/

theorem differentiableAt_zslice {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    DifferentiableAt ℝ (fun z' => g z' θ) z :=
  (Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice hg hθ hz).differentiableAt

/-! ## The level-`0` form of the equation -/

/-- **The level-`0` equation on the open quadrant**: `Lzero Ψ = F + α²z²∂_z²Ψ + α(5+α)z∂_zΨ`
wherever `bslOp α Ψ = F` (the first clause of `WeakPos2`). -/
theorem lzero_level0 {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Elliptic.Lzero Ψ z θ
      = F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
        + (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ := by
  have h := heq z hz θ hθ.1 hθ.2
  rw [Work.Elliptic.bslOp_apply] at h
  nlinarith [h]

/-! ## `∂_z` commutes with `Lzero` on the open quadrant -/

/-- **The commutation `Lzero ∘ ∂_z = ∂_z ∘ Lzero`** on the open quadrant, for a `C^∞` function
there.  Both sides involve only `θ`-derivatives and the `θ`-only factor `tan θ`, so Clairaut
(`H2W.pz_pthIter_two_eqOn` for the `∂_θ²` term, `Spaces.pz_pth_comm` for the mixed term with
`tan θ · u`) applies. -/
theorem Lzero_pz_eqOn {u : ℝ → ℝ → ℝ} (hu : Work.FTS.EllipticEst.SmoothOpen u) :
    Set.EqOn (Function.uncurry (Work.Elliptic.Lzero (Work.Spaces.pz u)))
      (Function.uncurry (Work.Spaces.pz (Work.Elliptic.Lzero u)))
      Work.FTS.EllipticEst.Q0 := by
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have hθ : p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hso_tan : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * u z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl hu
  have hso_pth2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 u) := hu.pth.pth
  have hC : Work.Spaces.pthIter 2 (Work.Spaces.pz u) p.1 p.2
      = Work.Spaces.pz (Work.Spaces.pthIter 2 u) p.1 p.2 :=
    (lzs_pz_pthIter_two_eqOn hu hp).symm
  have htan : (fun z θ => Real.tan θ * Work.Spaces.pz u z θ)
      = Work.Spaces.pz (fun z θ => Real.tan θ * u z θ) := by
    funext z θ
    exact (deriv_const_mul_field (u := Real.tan θ) (v := fun z' => u z' θ) (x := z)).symm
  have hmixed : Work.Spaces.pth (fun z θ => Real.tan θ * Work.Spaces.pz u z θ) p.1 p.2
      = Work.Spaces.pz (Work.Spaces.pth (fun z θ => Real.tan θ * u z θ)) p.1 p.2 := by
    rw [htan]
    exact (Work.Spaces.pz_pth_comm ((hso_tan.contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)).of_le (by norm_num))).symm
  have hdA : DifferentiableAt ℝ (fun z' => Work.Spaces.pthIter 2 u z' p.2) p.1 :=
    differentiableAt_zslice hso_pth2 hz hθ
  have hdB : DifferentiableAt ℝ
      (fun z' => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z' p.2) p.1 :=
    differentiableAt_zslice hso_tan.pth hz hθ
  have hdC : DifferentiableAt ℝ (fun z' => u z' p.2) p.1 := differentiableAt_zslice hu hz hθ
  have hlin : Work.Spaces.pz (fun z θ => -(Work.Spaces.pthIter 2 u z θ)
        + Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ - 6 * u z θ) p.1 p.2
      = -(Work.Spaces.pz (Work.Spaces.pthIter 2 u) p.1 p.2)
        + Work.Spaces.pz (Work.Spaces.pth (fun z θ => Real.tan θ * u z θ)) p.1 p.2
        - 6 * Work.Spaces.pz u p.1 p.2 := by
    show deriv (fun z' => -(Work.Spaces.pthIter 2 u z' p.2)
        + Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z' p.2 - 6 * u z' p.2) p.1 = _
    rw [(Filter.EventuallyEq.deriv_eq (f₁ := fun z' => (Work.Spaces.pth
            (fun z θ => Real.tan θ * u z θ) z' p.2 - 6 * u z' p.2)
          - (Work.Spaces.pthIter 2 u z' p.2)) (Filter.Eventually.of_forall
        (fun y => by ring))).symm]
    rw [show (fun z' : ℝ => (Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z' p.2
            - 6 * u z' p.2) - (Work.Spaces.pthIter 2 u z' p.2))
        = ((fun z' : ℝ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z' p.2)
            - (fun z' : ℝ => 6 * u z' p.2))
          - (fun z' : ℝ => Work.Spaces.pthIter 2 u z' p.2) from rfl]
    rw [deriv_sub (hdB.sub (hdC.const_mul 6)) hdA]
    rw [deriv_sub hdB (hdC.const_mul 6), deriv_const_mul_field]
    simp only [Work.Spaces.pz]
    ring
  show -(Work.Spaces.pthIter 2 (Work.Spaces.pz u) p.1 p.2)
      + Work.Spaces.pth (fun z θ => Real.tan θ * Work.Spaces.pz u z θ) p.1 p.2
      - 6 * Work.Spaces.pz u p.1 p.2
    = Work.Spaces.pz (fun z θ => -(Work.Spaces.pthIter 2 u z θ)
        + Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ - 6 * u z θ) p.1 p.2
  rw [hlin, hC, hmixed]

/-- **The commutation for the iterated derivative**: `Lzero (∂_z^j u) = ∂_z^j (Lzero u)` on the
open quadrant, by induction on `j` from `Lzero_pz_eqOn` and the congruence of `∂_z` on open
sets (`Spaces.pz_congr_of_isOpen`). -/
theorem Lzero_pzIter_eqOn {u : ℝ → ℝ → ℝ} (hu : Work.FTS.EllipticEst.SmoothOpen u) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Elliptic.Lzero (Work.Spaces.pzIter j u)))
      (Function.uncurry (Work.Spaces.pzIter j (Work.Elliptic.Lzero u)))
      Work.FTS.EllipticEst.Q0 := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
      intro p hp
      have h1 : Work.Elliptic.Lzero (Work.Spaces.pzIter (j + 1) u) p.1 p.2
          = Work.Spaces.pz (Work.Elliptic.Lzero (Work.Spaces.pzIter j u)) p.1 p.2 := by
        show Work.Elliptic.Lzero (Work.Spaces.pz (Work.Spaces.pzIter j u)) p.1 p.2 = _
        exact Lzero_pz_eqOn (hu.pzIter j) hp
      have h2 : Work.Spaces.pz (Work.Elliptic.Lzero (Work.Spaces.pzIter j u)) p.1 p.2
          = Work.Spaces.pz (Work.Spaces.pzIter j (Work.Elliptic.Lzero u)) p.1 p.2 :=
        Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 ih hp
      show Work.Elliptic.Lzero (Work.Spaces.pzIter (j + 1) u) p.1 p.2
          = Work.Spaces.pzIter (j + 1) (Work.Elliptic.Lzero u) p.1 p.2
      rw [h1, h2]
      rfl

/-! ## Product rules (used by the Leibniz expansion of `Lzero (∂_z^jΨ)`) -/

/-- `∂_z(z·u) = u + z·∂_zu` on the open quadrant. -/
theorem pz_z_mul {u : ℝ → ℝ → ℝ} (hu : Work.FTS.EllipticEst.SmoothOpen u)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pz (fun z θ => z * u z θ) z θ = u z θ + z * Work.Spaces.pz u z θ := by
  have hd1 : DifferentiableAt ℝ (fun z' : ℝ => z') z := by fun_prop
  have hd2 : DifferentiableAt ℝ (fun z' : ℝ => u z' θ) z := differentiableAt_zslice hu hz hθ
  have hmul : deriv ((fun z' : ℝ => z') * (fun z' : ℝ => u z' θ)) z
      = deriv (fun z' : ℝ => z') z * u z θ + z * deriv (fun z' : ℝ => u z' θ) z :=
    deriv_mul hd1 hd2
  have hid : deriv (fun z' : ℝ => z') z = 1 := by simpa using (hasDerivAt_id z).deriv
  show deriv (fun z' : ℝ => z' * u z' θ) z = u z θ + z * Work.Spaces.pz u z θ
  rw [show (fun z' : ℝ => z' * u z' θ)
      = (fun z' : ℝ => z') * (fun z' : ℝ => u z' θ) from rfl, hmul, hid]
  simp only [Work.Spaces.pz, one_mul]

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

/-- Additivity of `∂_z^k` on the open quadrant, for `SmoothOpen` data. -/
theorem pzIter_add_of_smooth {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (k : ℕ) :
    Work.Spaces.pzIter k (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.pzIter k f z θ + Work.Spaces.pzIter k g z θ := by
  induction k generalizing z θ with
  | zero => rfl
  | succ k ih =>
      have hev : (fun z' => Work.Spaces.pzIter k (fun z θ => f z θ + g z θ) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.pzIter k f z' θ + Work.Spaces.pzIter k g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih hz' hθ
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter k f z' θ) z :=
        ((hf.pzIter k).hasDerivAt_slice hθ hz).differentiableAt
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter k g z' θ) z :=
        ((hg.pzIter k).hasDerivAt_slice hθ hz).differentiableAt
      show deriv (fun z' => Work.Spaces.pzIter k (fun z θ => f z θ + g z θ) z' θ) z = _
      rw [hev.deriv_eq]
      rw [show (fun z' : ℝ => Work.Spaces.pzIter k f z' θ + Work.Spaces.pzIter k g z' θ)
          = (fun z' : ℝ => Work.Spaces.pzIter k f z' θ)
            + (fun z' : ℝ => Work.Spaces.pzIter k g z' θ) from rfl]
      rw [deriv_add hd1 hd2]
      rfl

/-- `∂_z²(zu) = 2∂_zu + z∂_z²u`. -/
theorem pzIter_two_z_mul {u : ℝ → ℝ → ℝ} (hu : Work.FTS.EllipticEst.SmoothOpen u)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pzIter 2 (fun z θ => z * u z θ) z θ
      = 2 * Work.Spaces.pz u z θ + z * Work.Spaces.pzIter 2 u z θ := by
  have hev : (fun z' => Work.Spaces.pz (fun z θ => z * u z θ) z' θ)
      =ᶠ[𝓝 z] (fun z' => u z' θ + z' * Work.Spaces.pz u z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact pz_z_mul hu hz' hθ
  have hd1 : DifferentiableAt ℝ (fun z' : ℝ => u z' θ) z := differentiableAt_zslice hu hz hθ
  have hd2 : DifferentiableAt ℝ (fun z' : ℝ => z' * Work.Spaces.pz u z' θ) z :=
    (differentiableAt_id (x := z)).mul (differentiableAt_zslice hu.pz hz hθ)
  have hderiv : deriv ((fun z' : ℝ => u z' θ) + (fun z' : ℝ => z' * Work.Spaces.pz u z' θ)) z
      = Work.Spaces.pz u z θ
        + (Work.Spaces.pz u z θ + z * Work.Spaces.pzIter 2 u z θ) := by
    rw [deriv_add hd1 hd2]
    rw [show (fun z' : ℝ => z' * Work.Spaces.pz u z' θ)
        = (fun z' : ℝ => z') * (fun z' : ℝ => Work.Spaces.pz u z' θ) from rfl]
    rw [deriv_mul (by fun_prop) (differentiableAt_zslice hu.pz hz hθ)]
    rw [show deriv (fun z' : ℝ => z') z = 1 from by simpa using (hasDerivAt_id z).deriv]
    simp only [Work.Spaces.pz, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]
    ring
  show deriv (fun z' => Work.Spaces.pz (fun z θ => z * u z θ) z' θ) z = _
  rw [hev.deriv_eq]
  rw [show (fun z' : ℝ => u z' θ + z' * Work.Spaces.pz u z' θ)
      = (fun z' : ℝ => u z' θ) + (fun z' : ℝ => z' * Work.Spaces.pz u z' θ) from rfl, hderiv]
  simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
  ring

/-- `∂_z²(z²u) = 2u + 4z∂_zu + z²∂_z²u`. -/
theorem pzIter_two_zsq_mul {u : ℝ → ℝ → ℝ} (hu : Work.FTS.EllipticEst.SmoothOpen u)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pzIter 2 (fun z θ => z ^ 2 * u z θ) z θ
      = 2 * u z θ + 4 * z * Work.Spaces.pz u z θ + z ^ 2 * Work.Spaces.pzIter 2 u z θ := by
  have hev : (fun z' => Work.Spaces.pz (fun z θ => z ^ 2 * u z θ) z' θ)
      =ᶠ[𝓝 z] (fun z' => 2 * z' * u z' θ + z' ^ 2 * Work.Spaces.pz u z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact pz_zsq_mul hu hz' hθ
  have hd1 : DifferentiableAt ℝ (fun z' : ℝ => 2 * z' * u z' θ) z :=
    (by fun_prop : DifferentiableAt ℝ (fun z' : ℝ => 2 * z') z).mul (differentiableAt_zslice hu hz hθ)
  have hd2 : DifferentiableAt ℝ (fun z' : ℝ => z' ^ 2 * Work.Spaces.pz u z' θ) z :=
    (by fun_prop : DifferentiableAt ℝ (fun z' : ℝ => z' ^ 2) z).mul
      (differentiableAt_zslice hu.pz hz hθ)
  have hderivA : deriv ((fun z' : ℝ => 2 * z') * (fun z' : ℝ => u z' θ)) z
      = 2 * u z θ + 2 * z * Work.Spaces.pz u z θ := by
    rw [deriv_mul (by fun_prop) (differentiableAt_zslice hu hz hθ)]
    rw [show deriv (fun z' : ℝ => 2 * z') z = 2 from by
      simpa using (hasDerivAt_id z).const_mul (2 : ℝ) |>.deriv]
    simp only [Work.Spaces.pz]
    try ring
  have hderivB : deriv ((fun z' : ℝ => z' ^ 2) * (fun z' : ℝ => Work.Spaces.pz u z' θ)) z
      = 2 * z * Work.Spaces.pz u z θ + z ^ 2 * Work.Spaces.pzIter 2 u z θ := by
    rw [deriv_mul (by fun_prop) (differentiableAt_zslice hu.pz hz hθ)]
    rw [show deriv (fun z' : ℝ => z' ^ 2) z = 2 * z from by
      simpa using (hasDerivAt_pow 2 z).deriv]
    simp only [Work.Spaces.pz, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]
  have hderiv : deriv ((fun z' : ℝ => 2 * z' * u z' θ) + (fun z' : ℝ => z' ^ 2 * Work.Spaces.pz u z' θ)) z
      = (2 * u z θ + 2 * z * Work.Spaces.pz u z θ)
        + (2 * z * Work.Spaces.pz u z θ + z ^ 2 * Work.Spaces.pzIter 2 u z θ) := by
    rw [deriv_add hd1 hd2]
    rw [show (fun z' : ℝ => 2 * z' * u z' θ)
        = (fun z' : ℝ => 2 * z') * (fun z' : ℝ => u z' θ) from rfl, hderivA]
    rw [show (fun z' : ℝ => z' ^ 2 * Work.Spaces.pz u z' θ)
        = (fun z' : ℝ => z' ^ 2) * (fun z' : ℝ => Work.Spaces.pz u z' θ) from rfl, hderivB]
  show deriv (fun z' => Work.Spaces.pz (fun z θ => z ^ 2 * u z θ) z' θ) z = _
  rw [hev.deriv_eq]
  rw [show (fun z' : ℝ => 2 * z' * u z' θ + z' ^ 2 * Work.Spaces.pz u z' θ)
      = (fun z' : ℝ => 2 * z' * u z' θ) + (fun z' : ℝ => z' ^ 2 * Work.Spaces.pz u z' θ) from rfl,
    hderiv]
  simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
  ring

/-! ## Pointwise product/linearity helpers and the level identities -/

/-- Pointwise form of `pzIter_const_mul`. -/
theorem pzIter_const_mul_pt (c : ℝ) (g : ℝ → ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (fun z θ => c * g z θ) z θ = c * Work.Spaces.pzIter k g z θ :=
  congrFun (congrFun (pzIter_const_mul c g k) z) θ

/-- **The level-`1` identity** on the open quadrant. -/
theorem lzero_level1 {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hFsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) :
    Set.EqOn (Function.uncurry (Work.Elliptic.Lzero (Work.Spaces.pz Ψ)))
      (Function.uncurry (fun z θ => Work.Spaces.pz F z θ
        + α ^ 2 * (2 * z * Work.Spaces.pzIter 2 Ψ z θ + z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ)
        + (α * (5 + α)) * (Work.Spaces.pz Ψ z θ + z * Work.Spaces.pzIter 2 Ψ z θ)))
      Work.FTS.EllipticEst.Q0 := by
  set c : ℝ := α * (5 + α) with hc
  have hso2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl (hsm.pzIter 2)
  have hso1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * Work.Spaces.pz Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl hsm.pz
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl hFsm
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α ^ 2) hso2)
  have hB : Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * (z * Work.Spaces.pz Ψ z θ)) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl c hso1
  have hlev : Set.EqOn (Function.uncurry (Work.Elliptic.Lzero Ψ))
      (Function.uncurry (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + c * (z * Work.Spaces.pz Ψ z θ))) Work.FTS.EllipticEst.Q0 := by
    intro q hq
    obtain ⟨hzq, hq0, hq1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hq
    have h := lzero_level0 heq hzq ⟨hq0, hq1⟩
    show Work.Elliptic.Lzero Ψ q.1 q.2
      = F q.1 q.2 + α ^ 2 * (q.1 ^ 2 * Work.Spaces.pzIter 2 Ψ q.1 q.2)
        + c * (q.1 * Work.Spaces.pz Ψ q.1 q.2)
    rw [h, hc]
    ring
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have hθ : p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  show Work.Elliptic.Lzero (Work.Spaces.pz Ψ) p.1 p.2
      = Work.Spaces.pz F p.1 p.2
        + α ^ 2 * (2 * p.1 * Work.Spaces.pzIter 2 Ψ p.1 p.2
            + p.1 ^ 2 * Work.Spaces.pzIter 3 Ψ p.1 p.2)
        + (α * (5 + α)) * (Work.Spaces.pz Ψ p.1 p.2
            + p.1 * Work.Spaces.pzIter 2 Ψ p.1 p.2)
  have e1 : Work.Elliptic.Lzero (Work.Spaces.pz Ψ) p.1 p.2
      = Work.Spaces.pzIter 1 (Work.Elliptic.Lzero Ψ) p.1 p.2 := Lzero_pzIter_eqOn hsm 1 hp
  have e2 : Work.Spaces.pzIter 1 (Work.Elliptic.Lzero Ψ) p.1 p.2
      = Work.Spaces.pzIter 1 (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + c * (z * Work.Spaces.pz Ψ z θ)) p.1 p.2 :=
    pzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hlev 1 hp
  have e3 : Work.Spaces.pzIter 1 (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + c * (z * Work.Spaces.pz Ψ z θ)) p.1 p.2
      = Work.Spaces.pzIter 1 (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) p.1 p.2
        + Work.Spaces.pzIter 1 (fun z θ => c * (z * Work.Spaces.pz Ψ z θ)) p.1 p.2 := by
    rw [show (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + c * (z * Work.Spaces.pz Ψ z θ))
        = (fun z θ => (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
            + (fun z θ => c * (z * Work.Spaces.pz Ψ z θ)) z θ) from rfl]
    exact pzIter_add_of_smooth hA hB hz hθ 1
  have e4 : Work.Spaces.pzIter 1 (fun z θ => c * (z * Work.Spaces.pz Ψ z θ)) p.1 p.2
      = c * Work.Spaces.pzIter 1 (fun z θ => z * Work.Spaces.pz Ψ z θ) p.1 p.2 :=
    pzIter_const_mul_pt c (fun z θ => z * Work.Spaces.pz Ψ z θ) 1 p.1 p.2
  have e5 : Work.Spaces.pzIter 1 (fun z θ => z * Work.Spaces.pz Ψ z θ) p.1 p.2
      = Work.Spaces.pz Ψ p.1 p.2 + p.1 * Work.Spaces.pzIter 2 Ψ p.1 p.2 := by
    rw [show Work.Spaces.pzIter 1 (fun z θ => z * Work.Spaces.pz Ψ z θ)
        = Work.Spaces.pz (fun z θ => z * Work.Spaces.pz Ψ z θ) from rfl]
    exact pz_z_mul hsm.pz hz hθ
  have e6 : Work.Spaces.pzIter 1 (fun z θ => F z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) p.1 p.2
      = Work.Spaces.pzIter 1 (fun z θ => F z θ) p.1 p.2
        + Work.Spaces.pzIter 1 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) p.1 p.2 := by
    rw [show (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        = (fun z θ => (fun z θ => F z θ) z θ
            + (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ) from rfl]
    exact pzIter_add_of_smooth hFsm
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α ^ 2) hso2) hz hθ 1
  have e7 : Work.Spaces.pzIter 1 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) p.1 p.2
      = α ^ 2 * Work.Spaces.pzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) p.1 p.2 :=
    pzIter_const_mul_pt (α ^ 2) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) 1 p.1 p.2
  have e8 : Work.Spaces.pzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) p.1 p.2
      = 2 * p.1 * Work.Spaces.pzIter 2 Ψ p.1 p.2
        + p.1 ^ 2 * Work.Spaces.pzIter 3 Ψ p.1 p.2 := by
    rw [show Work.Spaces.pzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        = Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) from rfl]
    exact pz_zsq_mul (hsm.pzIter 2) hz hθ
  have e9 : Work.Spaces.pzIter 1 (fun z θ => F z θ) p.1 p.2 = Work.Spaces.pz F p.1 p.2 := rfl
  rw [e1, e2, e3, e6, e7, e8, e9, e4, e5]

/-- **The level-`2` identity** on the open quadrant. -/
theorem lzero_level2 {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hFsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) :
    Set.EqOn (Function.uncurry (Work.Elliptic.Lzero (Work.Spaces.pzIter 2 Ψ)))
      (Function.uncurry (fun z θ => Work.Spaces.pzIter 2 F z θ
        + α ^ 2 * (2 * Work.Spaces.pzIter 2 Ψ z θ + 4 * z * Work.Spaces.pzIter 3 Ψ z θ
            + z ^ 2 * Work.Spaces.pzIter 4 Ψ z θ)
        + (α * (5 + α)) * (2 * Work.Spaces.pzIter 2 Ψ z θ
            + z * Work.Spaces.pzIter 3 Ψ z θ)))
      Work.FTS.EllipticEst.Q0 := by
  set c : ℝ := α * (5 + α) with hc
  have hso2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl (hsm.pzIter 2)
  have hso1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * Work.Spaces.pz Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl hsm.pz
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl hFsm
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α ^ 2) hso2)
  have hB : Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * (z * Work.Spaces.pz Ψ z θ)) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl c hso1
  have hlev : Set.EqOn (Function.uncurry (Work.Elliptic.Lzero Ψ))
      (Function.uncurry (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + c * (z * Work.Spaces.pz Ψ z θ))) Work.FTS.EllipticEst.Q0 := by
    intro q hq
    obtain ⟨hzq, hq0, hq1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hq
    have h := lzero_level0 heq hzq ⟨hq0, hq1⟩
    show Work.Elliptic.Lzero Ψ q.1 q.2
      = F q.1 q.2 + α ^ 2 * (q.1 ^ 2 * Work.Spaces.pzIter 2 Ψ q.1 q.2)
        + c * (q.1 * Work.Spaces.pz Ψ q.1 q.2)
    rw [h, hc]
    ring
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have hθ : p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  show Work.Elliptic.Lzero (Work.Spaces.pzIter 2 Ψ) p.1 p.2
      = Work.Spaces.pzIter 2 F p.1 p.2
        + α ^ 2 * (2 * Work.Spaces.pzIter 2 Ψ p.1 p.2
            + 4 * p.1 * Work.Spaces.pzIter 3 Ψ p.1 p.2
            + p.1 ^ 2 * Work.Spaces.pzIter 4 Ψ p.1 p.2)
        + (α * (5 + α)) * (2 * Work.Spaces.pzIter 2 Ψ p.1 p.2
            + p.1 * Work.Spaces.pzIter 3 Ψ p.1 p.2)
  have e1 : Work.Elliptic.Lzero (Work.Spaces.pzIter 2 Ψ) p.1 p.2
      = Work.Spaces.pzIter 2 (Work.Elliptic.Lzero Ψ) p.1 p.2 := Lzero_pzIter_eqOn hsm 2 hp
  have e2 : Work.Spaces.pzIter 2 (Work.Elliptic.Lzero Ψ) p.1 p.2
      = Work.Spaces.pzIter 2 (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + c * (z * Work.Spaces.pz Ψ z θ)) p.1 p.2 :=
    pzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hlev 2 hp
  have e3 : Work.Spaces.pzIter 2 (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + c * (z * Work.Spaces.pz Ψ z θ)) p.1 p.2
      = Work.Spaces.pzIter 2 (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) p.1 p.2
        + Work.Spaces.pzIter 2 (fun z θ => c * (z * Work.Spaces.pz Ψ z θ)) p.1 p.2 := by
    rw [show (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + c * (z * Work.Spaces.pz Ψ z θ))
        = (fun z θ => (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
            + (fun z θ => c * (z * Work.Spaces.pz Ψ z θ)) z θ) from rfl]
    exact pzIter_add_of_smooth hA hB hz hθ 2
  have e4 : Work.Spaces.pzIter 2 (fun z θ => c * (z * Work.Spaces.pz Ψ z θ)) p.1 p.2
      = c * Work.Spaces.pzIter 2 (fun z θ => z * Work.Spaces.pz Ψ z θ) p.1 p.2 :=
    pzIter_const_mul_pt c (fun z θ => z * Work.Spaces.pz Ψ z θ) 2 p.1 p.2
  have e5 : Work.Spaces.pzIter 2 (fun z θ => z * Work.Spaces.pz Ψ z θ) p.1 p.2
      = 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2 + p.1 * Work.Spaces.pzIter 3 Ψ p.1 p.2 := by
    have h := pzIter_two_z_mul hsm.pz hz hθ
    rw [show Work.Spaces.pzIter 2 (fun z θ => z * Work.Spaces.pz Ψ z θ) p.1 p.2
        = 2 * Work.Spaces.pz (Work.Spaces.pz Ψ) p.1 p.2
          + p.1 * Work.Spaces.pzIter 2 (Work.Spaces.pz Ψ) p.1 p.2 from h]
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]
  have e6 : Work.Spaces.pzIter 2 (fun z θ => F z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) p.1 p.2
      = Work.Spaces.pzIter 2 (fun z θ => F z θ) p.1 p.2
        + Work.Spaces.pzIter 2 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) p.1 p.2 := by
    rw [show (fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        = (fun z θ => (fun z θ => F z θ) z θ
            + (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ) from rfl]
    exact pzIter_add_of_smooth hFsm
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α ^ 2) hso2) hz hθ 2
  have e7 : Work.Spaces.pzIter 2 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) p.1 p.2
      = α ^ 2 * Work.Spaces.pzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) p.1 p.2 :=
    pzIter_const_mul_pt (α ^ 2) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) 2 p.1 p.2
  have e8 : Work.Spaces.pzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) p.1 p.2
      = 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2 + 4 * p.1 * Work.Spaces.pzIter 3 Ψ p.1 p.2
        + p.1 ^ 2 * Work.Spaces.pzIter 4 Ψ p.1 p.2 := by
    have h := pzIter_two_zsq_mul (hsm.pzIter 2) hz hθ
    rw [show Work.Spaces.pzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) p.1 p.2
        = 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2
          + 4 * p.1 * Work.Spaces.pz (Work.Spaces.pzIter 2 Ψ) p.1 p.2
          + p.1 ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pzIter 2 Ψ) p.1 p.2 from h]
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]
  have e9 : Work.Spaces.pzIter 2 (fun z θ => F z θ) p.1 p.2
      = Work.Spaces.pzIter 2 F p.1 p.2 := rfl
  rw [e1, e2, e3, e6, e7, e8, e9, e4, e5]

/-! ## Pointwise forms of the three level identities -/

theorem lzero_level0_pt {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Elliptic.Lzero Ψ z θ = F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
      + (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ :=
  lzero_level0 heq hz hθ

theorem lzero_level1_pt {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hFsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Elliptic.Lzero (Work.Spaces.pz Ψ) z θ = Work.Spaces.pz F z θ
      + α ^ 2 * (2 * z * Work.Spaces.pzIter 2 Ψ z θ + z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ)
      + (α * (5 + α)) * (Work.Spaces.pz Ψ z θ + z * Work.Spaces.pzIter 2 Ψ z θ) :=
  lzero_level1 hFsm hsm heq (x := (z, θ)) ⟨hz, hθ.1, hθ.2⟩

theorem lzero_level2_pt {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hFsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Elliptic.Lzero (Work.Spaces.pzIter 2 Ψ) z θ = Work.Spaces.pzIter 2 F z θ
      + α ^ 2 * (2 * Work.Spaces.pzIter 2 Ψ z θ + 4 * z * Work.Spaces.pzIter 3 Ψ z θ
          + z ^ 2 * Work.Spaces.pzIter 4 Ψ z θ)
      + (α * (5 + α)) * (2 * Work.Spaces.pzIter 2 Ψ z θ
          + z * Work.Spaces.pzIter 3 Ψ z θ) :=
  lzero_level2 hFsm hsm heq (x := (z, θ)) ⟨hz, hθ.1, hθ.2⟩

/-! ## The reduction -/

/-- **The reduction.** -/
theorem lzeroSliceL1Ae_of_levels {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hFsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hF : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ m : ℕ, m ≤ 2 →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Spaces.pzIter m F z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hΨ : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), ∀ m : ℕ, m ≤ 4 →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Spaces.pzIter m Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (j : ℕ) (hj : j ≤ 2) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 *
        Work.Elliptic.Lzero (Work.Spaces.pzIter j Ψ) z θ) Work.Spaces.Iθ := by
  filter_upwards [hΨ, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hzS hz
  have hz0 : 0 < z := hz
  have hterm : ∀ (c : ℝ) (f : ℝ → ℝ),
      MeasureTheory.IntegrableOn (fun θ : ℝ => f θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 * (c * f θ)) Work.Spaces.Iθ := by
    intro c f hf
    refine (hf.const_mul c).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp only [Work.Elliptic.sinCos2]
    ring
  interval_cases j
  · -- `j = 0`: `Lzero Ψ = F + α²z²∂_z²Ψ + α(5+α)z∂_zΨ`
    have h1 := hterm 1 (fun θ => F z θ) (hF z hz0 0 (by norm_num))
    have h2 := hterm (α ^ 2 * z ^ 2) (fun θ => Work.Spaces.pzIter 2 Ψ z θ)
      (hzS 2 (by norm_num))
    have h3 := hterm (α * (5 + α) * z) (fun θ => Work.Spaces.pz Ψ z θ) (hzS 1 (by norm_num))
    refine ((h1.add h2).add h3).congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθI => ?_)
    simp only [Pi.add_apply]
    by_cases hlt : θ < Real.pi / 2
    · by_cases hpos : 0 < θ
      · rw [show Work.Elliptic.Lzero (Work.Spaces.pzIter 0 Ψ) z θ
            = Work.Elliptic.Lzero Ψ z θ from rfl, lzero_level0_pt heq hz0 ⟨hpos, hlt⟩]
        ring
      · have hzθ : θ = 0 := le_antisymm (le_of_not_gt hpos) hθI.1
        rw [hzθ]; norm_num
    · have hzθ : θ = Real.pi / 2 := le_antisymm hθI.2 (le_of_not_gt hlt)
      rw [hzθ]; norm_num
  · -- `j = 1`
    have h1 := hterm 1 (fun θ => Work.Spaces.pz F z θ) (hF z hz0 1 (by norm_num))
    have h2 := hterm (α ^ 2 * (2 * z)) (fun θ => Work.Spaces.pzIter 2 Ψ z θ)
      (hzS 2 (by norm_num))
    have h3 := hterm (α ^ 2 * z ^ 2) (fun θ => Work.Spaces.pzIter 3 Ψ z θ)
      (hzS 3 (by norm_num))
    have h4 := hterm (α * (5 + α)) (fun θ => Work.Spaces.pz Ψ z θ) (hzS 1 (by norm_num))
    have h5 := hterm (α * (5 + α) * z) (fun θ => Work.Spaces.pzIter 2 Ψ z θ)
      (hzS 2 (by norm_num))
    refine ((((h1.add h2).add h3).add h4).add h5).congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθI => ?_)
    simp only [Pi.add_apply]
    by_cases hlt : θ < Real.pi / 2
    · by_cases hpos : 0 < θ
      · rw [show Work.Elliptic.Lzero (Work.Spaces.pzIter 1 Ψ) z θ
            = Work.Elliptic.Lzero (Work.Spaces.pz Ψ) z θ from rfl,
          lzero_level1_pt hFsm hsm heq hz0 ⟨hpos, hlt⟩]
        ring
      · have hzθ : θ = 0 := le_antisymm (le_of_not_gt hpos) hθI.1
        rw [hzθ]; norm_num
    · have hzθ : θ = Real.pi / 2 := le_antisymm hθI.2 (le_of_not_gt hlt)
      rw [hzθ]; norm_num
  · -- `j = 2`
    have h1 := hterm 1 (fun θ => Work.Spaces.pzIter 2 F z θ) (hF z hz0 2 (by norm_num))
    have h2 := hterm (α ^ 2 * 2) (fun θ => Work.Spaces.pzIter 2 Ψ z θ) (hzS 2 (by norm_num))
    have h3 := hterm (α ^ 2 * (4 * z)) (fun θ => Work.Spaces.pzIter 3 Ψ z θ)
      (hzS 3 (by norm_num))
    have h4 := hterm (α ^ 2 * z ^ 2) (fun θ => Work.Spaces.pzIter 4 Ψ z θ)
      (hzS 4 (by norm_num))
    have h5 := hterm (α * (5 + α) * 2) (fun θ => Work.Spaces.pzIter 2 Ψ z θ)
      (hzS 2 (by norm_num))
    have h6 := hterm (α * (5 + α) * z) (fun θ => Work.Spaces.pzIter 3 Ψ z θ)
      (hzS 3 (by norm_num))
    refine (((((h1.add h2).add h3).add h4).add h5).add h6).congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθI => ?_)
    simp only [Pi.add_apply]
    by_cases hlt : θ < Real.pi / 2
    · by_cases hpos : 0 < θ
      · rw [lzero_level2_pt hFsm hsm heq hz0 ⟨hpos, hlt⟩]
        ring
      · have hzθ : θ = 0 := le_antisymm (le_of_not_gt hpos) hθI.1
        rw [hzθ]; norm_num
    · have hzθ : θ = Real.pi / 2 := le_antisymm hθI.2 (le_of_not_gt hlt)
      rw [hzθ]; norm_num

/-! ## The target -/

/-! ## The target -/

theorem lzeroSliceL1Ae : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.WeakPos2 α F Ψ →
    ∀ j : ℕ, j ≤ 2 →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn
          (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 *
            Work.Elliptic.Lzero (Work.Spaces.pzIter j Ψ) z θ) Work.Spaces.Iθ := by
  intro α F Ψ hα hα4 h
  obtain ⟨hEq, h0, hpi, hdec, hOF, hOP, hsm, hmF⟩ := h
  have hsm' : Work.FTS.EllipticEst.SmoothOpen Ψ := Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hFsm : Work.FTS.EllipticEst.SmoothOpen F := by
    have hb : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
      Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hsm'
    refine hb.congr (fun q hq => ?_)
    obtain ⟨hzq, hq0, hq1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hq
    exact (hEq q.1 hzq q.2 hq0 hq1).symm
  intro j hj
  exact lzeroSliceL1Ae_of_levels hFsm hsm' hEq
    (lzeroSliceFiber α F Ψ hα hα4 ⟨hEq, h0, hpi, hdec, hOF, hOP, hsm, hmF⟩)
    (pzIterSliceIntegrableInput α F Ψ hα hα4 ⟨hEq, h0, hpi, hdec, hOF, hOP, hsm, hmF⟩) j hj

end

end Work.FTS.EllipticEst.H2W
