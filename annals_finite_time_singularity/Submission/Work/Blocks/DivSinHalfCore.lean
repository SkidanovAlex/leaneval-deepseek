/-
Copyright: work module for the Elgindi finite-time singularity project.

# Slice-level core for the half-open `sin 2θ`-division

The division estimate `Work.FTS.EllipticEst.divSin_Hk_gen` and its slice companions
(`Blocks.DivSinHkMemSlice_gen`, `Elliptic.dtwTermwiseZ_of_iter`,
`Elliptic.dtwTermwiseMixed_of_iter`, `Elliptic.pz_cont_DzIter_div`,
`Elliptic.pz_cont_mixed_div`) assume `Work.Spaces.SmoothNbhd Φ`, i.e. smoothness on an open
neighbourhood of the *closed* quadrant.  For the elliptic residual
`Ξ = Ψ - (1/(4α)) sin 2θ L₁₂(F)` that hypothesis is unavailable; what is available is

* `Work.FTS.EllipticEst.SmoothOpen Φ`, i.e. `C^∞` (the smoothness order
  `Work.Stability.smoothOrder = ((⊤ : ℕ∞) : WithTop ℕ∞)`) on the *open* quadrant `Q0`, and
* for every `z > 0` analyticity of the angular slices `θ ↦ D_z^j Φ z θ` on a
  neighbourhood `(-1, π/2+1)` of `[0, π/2]` (`Work.Elliptic.SmoothSlice`).

Every slicewise argument of the division chain is run at a *fixed* level `z > 0`, and at such a
level the two angular endpoints are null sets for `dθ`; so it suffices to have the local
identities at the points of the *open* quadrant `Q0` (where `Φ` is `C^∞`), together with the
slice data (analyticity and vanishing at the endpoints).  This module collects the resulting
local identities and continuity statements:

* `sliceFacts` — smoothness and vanishing of the slices `θ ↦ D_z^j Φ z θ` for `j ≤ k`,
  directly from the two standing hypotheses of `Blocks.divSin_Hk_half`;
* `pth_DzIter_eqOn_Q0`, `deriv_DzIter_slice_Q0` — `∂_θ` commutes with the iterates of `D_z`;
* `divSinMixedExpansion_Q0`, `mixed_div_eq_Dth1Iter_Q0` — `D_z^j D_θ^i` commutes with the
  division by `sin 2θ` (`1/sin 2θ` is a function of `θ` alone);
* `Dth1Iter_deriv_eq_mixed_Q0` — the `m`-th angular iterate of `∂_θ(D_z^j Φ)` is
  `D_z^j D_θ^m (∂_θΦ)`;
* `pz_cont_DzIter_div_of_slice`, `pz_cont_mixed_div_of_slice` — the slices of the quotient
  `Φ / sin 2θ` and of its mixed derivatives are continuous on `(0, π/2)`.

Everything here is `sorry`-free; the analytic content is in the imported lemmas.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Elliptic.DivSinFactor
import Submission.Work.Elliptic.DivSinSliceIdent
import Submission.Work.Elliptic.DthIter_slice
import Submission.Work.Blocks.HalfInfra

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.DivSinHalf

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## 0. Elementary angular facts -/

/-- `sin(2θ) > 0` on `(0, π/2)`. -/
theorem sin_two_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-! ## 1. The slice facts

These are exactly the per-slice inputs the division machinery consumes at a fixed level
`z > 0`: smoothness of the slices of the `D_z`-iterates and their vanishing at the two
angular endpoints.  They come from the two standing hypotheses of `Blocks.divSin_Hk_half`
(the `SmoothSlice`-hypothesis and `VanishTheta Φ`), not from `SmoothNbhd Φ`. -/

/-- The slice facts for `D_z^j Φ` at a level `z > 0`, for `j ≤ k`. -/
theorem sliceFacts {k : ℕ} {Φ : ℝ → ℝ → ℝ}
    (hsl : ∀ z ∈ Work.Spaces.Iz, 0 < z → ∀ j : ℕ, j ≤ k →
      Work.Elliptic.SmoothSlice (fun θ => Work.Spaces.DzIter j Φ z θ))
    (hv : Work.Spaces.VanishTheta Φ) {j : ℕ} (hj : j ≤ k) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) (hzpos : 0 < z) :
    Work.Elliptic.SmoothSlice (fun θ => Work.Spaces.DzIter j Φ z θ) ∧
      (fun θ => Work.Spaces.DzIter j Φ z θ) 0 = 0 ∧
      (fun θ => Work.Spaces.DzIter j Φ z θ) (Real.pi / 2) = 0 :=
  ⟨hsl z hz hzpos j hj, (Work.Elliptic.vanish_DzIter hv j).1 z,
    (Work.Elliptic.vanish_DzIter hv j).2 z⟩

/-! ## 2. The generic commutations on an open set

`∂_θ` (resp. its iterates) can be moved across the iterates of `D_z` at any point of an open
set on which the function is `C^∞` (the class of `SmoothOpen`).  These are the proofs of
`HalfU.Dth_DzIter_comm_eqOn`, `HalfU.DthIter_DzIter_comm_eqOn`, `HalfU.pth_DzIter_eqOn` and
`Work.Spaces.mixed_div_comm` with joint analyticity replaced by `C^∞`-regularity; they are
recorded here because the estimates below are run on the open quadrant `Q0`, where only
`SmoothOpen Φ` is available. -/

/-- `D_z (F · c(θ)) = (D_z F) · c(θ)`: the angular factor is a constant as far as `D_z` is
concerned (the multiplication counterpart of `Work.Elliptic.Dz_div_const`). -/
theorem Dz_mul_const_arg (F : ℝ → ℝ → ℝ) (c : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.Dz (fun z θ => F z θ * c θ) z θ = Work.Spaces.Dz F z θ * c θ := by
  show z * deriv (fun z' => F z' θ * c θ) z = z * deriv (fun z' => F z' θ) z * c θ
  rw [show (fun z' => F z' θ * c θ) = fun z' => c θ * F z' θ from by funext z'; ring,
    deriv_const_mul_field]
  ring

/-- `D_θ` can be moved across any iterate of `D_z` on an open set of `C^∞`-regularity. -/
theorem Dth_DzIter_comm_eqOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V) (b : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DzIter b f)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.Dth f))) V := by
  induction b with
  | zero => intro y hy; rfl
  | succ b ih =>
      intro y hy
      have hc : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b f)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (((Work.FTS.LocData.contDiffOn_DzIter hV h b).contDiffAt
          (hV.mem_nhds hy)).of_le (by rw [Work.Stability.smoothOrder]; norm_num))
      have hpz := Work.Spaces.pz_congr_of_isOpen hV ih hy
      show Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.Dth f)) y.1 y.2
      rw [← hc]
      show y.1 * Work.Spaces.pz (Work.Spaces.Dth (Work.Spaces.DzIter b f)) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.Dth f)) y.1 y.2
      rw [hpz]

/-- The iterates of `D_θ` can be moved across any iterate of `D_z` on an open set of
`C^∞`-regularity. -/
theorem DthIter_DzIter_comm_eqOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V) (b i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.DzIter b f)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.DthIter i f))) V := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hDth : Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter i f)) y.1 y.2 :=
        Work.Blocks.Half.Dth_congrOn hV ih hy
      have hstep : Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter i f)) y.1 y.2
          = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter i f)) y.1 y.2 :=
        Dth_DzIter_comm_eqOn hV
          (Work.FTS.LocData.contDiffOn_DthIter hV h i) b hy
      show Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter i f)) y.1 y.2
      rw [hDth, hstep]

/-- `∂_θ (D_z^j f) = D_z^j (∂_θ f)` on an open set of `C^∞`-regularity. -/
theorem pth_DzIter_eqOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j f)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth f))) V := by
  induction j with
  | zero => intro y hy; rfl
  | succ j ih =>
      intro y hy
      have hs : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DzIter j f)) V :=
        Work.FTS.LocData.contDiffOn_DzIter hV h j
      have hstep : Function.uncurry (Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j f))) y
          = Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j f))) y :=
        Work.Blocks.Half.pth_Dz_apply_of ((hs.contDiffAt (hV.mem_nhds hy)).of_le
          (by rw [Work.Stability.smoothOrder]; norm_num))
      have hcongr : Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j f))) y
          = Function.uncurry (Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth f))) y :=
        Work.Blocks.Half.Dz_congrOn hV ih hy
      show Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter (j+1) f)) y
          = Function.uncurry (Work.Spaces.DzIter (j+1) (Work.Spaces.pth f)) y
      rw [show Work.Spaces.DzIter (j+1) f = Work.Spaces.Dz (Work.Spaces.DzIter j f) from rfl,
          show Work.Spaces.DzIter (j+1) (Work.Spaces.pth f)
            = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth f)) from rfl]
      exact hstep.trans hcongr

/-- `D_z^j` commutes with `D_θ^i` followed by multiplication by a function of `θ` alone, on an
open set of `C^∞`-regularity (the `C^∞`-analogue of `Work.Spaces.mixed_div_comm`, which
assumes joint *analyticity*). -/
theorem mixed_mul_comm_eqOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ} {c : ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V)
    (hc : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => c p.2) V) :
    ∀ j i : ℕ,
      Set.EqOn (Function.uncurry (Work.Spaces.DzIter j
          (Work.Spaces.DthIter i (fun z θ => f z θ * c θ))))
        (Function.uncurry (Work.Spaces.DthIter i
          (fun z θ => Work.Spaces.DzIter j f z θ * c θ))) V := by
  intro j
  induction j with
  | zero => intro i; exact fun p hp => rfl
  | succ j ih =>
      intro i p hp
      have hg : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (fun z θ => Work.Spaces.DzIter j f z θ * c θ)) V :=
        (Work.FTS.LocData.contDiffOn_DzIter hV hf j).mul hc
      have hstep2 : Work.Spaces.Dz
            (Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => f z θ * c θ))) p.1 p.2
          = Work.Spaces.Dz
            (Work.Spaces.DthIter i (fun z θ => Work.Spaces.DzIter j f z θ * c θ)) p.1 p.2 :=
        Work.Blocks.Half.Dz_congrOn hV (ih i) hp
      have hstep3 : Work.Spaces.Dz
            (Work.Spaces.DthIter i (fun z θ => Work.Spaces.DzIter j f z θ * c θ)) p.1 p.2
          = Work.Spaces.DthIter i
            (Work.Spaces.Dz (fun z θ => Work.Spaces.DzIter j f z θ * c θ)) p.1 p.2 :=
        (DthIter_DzIter_comm_eqOn hV hg 1 i hp).symm
      have hstep4 : Set.EqOn
          (Function.uncurry (Work.Spaces.Dz (fun z θ => Work.Spaces.DzIter j f z θ * c θ)))
          (Function.uncurry (fun z θ => Work.Spaces.DzIter (j + 1) f z θ * c θ)) V := by
        intro q hq
        simpa only [Function.uncurry, Work.Spaces.DzIter_succ] using
          Dz_mul_const_arg (Work.Spaces.DzIter j f) c q.1 q.2
      have hstep5 := Work.Blocks.Half.DthIter_congrOn hV hstep4 i hp
      calc Work.Spaces.DzIter (j + 1)
            (Work.Spaces.DthIter i (fun z θ => f z θ * c θ)) p.1 p.2
          = Work.Spaces.Dz
            (Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => f z θ * c θ))) p.1 p.2 :=
            rfl
        _ = Work.Spaces.Dz
            (Work.Spaces.DthIter i (fun z θ => Work.Spaces.DzIter j f z θ * c θ)) p.1 p.2 :=
            hstep2
        _ = Work.Spaces.DthIter i
            (Work.Spaces.Dz (fun z θ => Work.Spaces.DzIter j f z θ * c θ)) p.1 p.2 := hstep3
        _ = Work.Spaces.DthIter i
            (fun z θ => Work.Spaces.DzIter (j + 1) f z θ * c θ) p.1 p.2 := hstep5

/-! ## 3. The specialisations to the open quadrant `Q0` -/

/-- `∂_θ` commutes with the iterates of `D_z` on the open quadrant. -/
theorem pth_DzIter_eqOn_Q0 {Φ : ℝ → ℝ → ℝ} (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ)
    (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j Φ)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth Φ)))
      Work.FTS.EllipticEst.Q0 :=
  pth_DzIter_eqOn Work.FTS.EllipticEst.isOpen_Q0 hΦ j

/-- The `θ`-derivative of the slice of `D_z^j Φ` is the slice of `D_z^j (∂_θΦ)`, for `(z,θ)`
in the open quadrant. -/
theorem deriv_DzIter_slice_Q0 {Φ : ℝ → ℝ → ℝ} (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ)
    (j : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' => Work.Spaces.DzIter j Φ z θ') θ
      = Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ :=
  pth_DzIter_eqOn_Q0 hΦ j (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)

/-- The open set on which the quotient `Φ / sin 2θ` may be differentiated: the open quadrant
inside the complement of the two lines `sin 2θ = 0` (there are none inside `(0, π/2)`). -/
def VQ : Set (ℝ × ℝ) :=
  Work.FTS.EllipticEst.Q0
    ∩ (fun p : ℝ × ℝ => Real.sin (2 * p.2)) ⁻¹' {y : ℝ | y ≠ 0}

theorem isOpen_VQ : IsOpen VQ := by
  rw [VQ]
  exact Work.FTS.EllipticEst.isOpen_Q0.inter
    (isOpen_ne.preimage (by continuity : Continuous fun p : ℝ × ℝ => Real.sin (2 * p.2)))

theorem mem_VQ {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (z, θ) ∈ VQ := by
  refine ⟨Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩, ?_⟩
  exact ne_of_gt (sin_two_pos_Ioo hθ)

/-- `D_z^j` commutes with `D_θ^i` across division by `sin 2θ`, in the open quadrant. -/
theorem divSinMixedExpansion_Q0 {Φ : ℝ → ℝ → ℝ}
    (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ) (j i : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter j
        (Work.Spaces.DthIter i (fun z θ => Φ z θ / Real.sin (2 * θ))) z θ
      = Work.Spaces.DthIter i
          (fun z θ => Work.Spaces.DzIter j Φ z θ / Real.sin (2 * θ)) z θ := by
  have hp : (z, θ) ∈ VQ := mem_VQ hz hθ
  have hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry Φ) VQ :=
    hΦ.mono (fun p hp => hp.1)
  have hc : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => (fun θ : ℝ => (Real.sin (2 * θ))⁻¹) p.2) VQ := by
    have hsin_s : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2)) VQ :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hne : ∀ p ∈ VQ, Real.sin (2 * p.2) ≠ 0 := fun p hp => hp.2
    exact hsin_s.inv hne
  have key := mixed_mul_comm_eqOn (c := fun θ : ℝ => (Real.sin (2 * θ))⁻¹) isOpen_VQ hf hc j i hp
  simpa only [div_eq_mul_inv, Function.uncurry] using key

/-- The mixed derivative of the quotient `Φ/sin 2θ`, as an angular iterate of the slice of
`D_z^j Φ`, in the open quadrant. -/
theorem mixed_div_eq_Dth1Iter_Q0 {Φ : ℝ → ℝ → ℝ}
    (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ) (j i : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.mixed j i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
      = Work.Elliptic.Dth1Iter i
          (Work.Elliptic.SinQ (fun θ' => Work.Spaces.DzIter j Φ z θ')) θ := by
  have h1 := divSinMixedExpansion_Q0 hΦ j i hz hθ
  have h2 := Work.Elliptic.dtw_DthIter_slice_at
      (fun z' θ' => Work.Spaces.DzIter j Φ z' θ' / Real.sin (2 * θ')) i z θ
  show Work.Spaces.DzIter j
      (Work.Spaces.DthIter i (fun z θ => Φ z θ / Real.sin (2 * θ))) z θ = _
  rw [h1, h2]
  exact Work.Elliptic.DivSinSliceIdent (fun θ' => Work.Spaces.DzIter j Φ z θ') i z θ hθ

/-- The `m`-th angular iterate of the derivative of the slice of `D_z^j Φ` is the mixed
derivative `D_z^j D_θ^m (∂_θΦ)`, in the open quadrant. -/
theorem Dth1Iter_deriv_eq_mixed_Q0 {Φ : ℝ → ℝ → ℝ}
    (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ) (j m : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Elliptic.Dth1Iter m
        (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j Φ z θ'') θ') θ
      = Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ := by
  have hy : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hfun : (fun (_ : ℝ) θ' => deriv (fun θ'' => Work.Spaces.DzIter j Φ z θ'') θ')
      = fun (_ : ℝ) θ' => Work.Spaces.pth (Work.Spaces.DzIter j Φ) z θ' := by
    funext a θ'; rfl
  calc Work.Elliptic.Dth1Iter m
        (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j Φ z θ'') θ') θ
      = Work.Spaces.DthIter m
          (fun (_ : ℝ) θ' => deriv (fun θ'' => Work.Spaces.DzIter j Φ z θ'') θ') z θ :=
        (Work.Elliptic.DthIter_const m
          (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j Φ z θ'') θ') z θ).symm
    _ = Work.Spaces.DthIter m
          (fun (_ : ℝ) θ' => Work.Spaces.pth (Work.Spaces.DzIter j Φ) z θ') z θ := by rw [hfun]
    _ = Work.Spaces.DthIter m (Work.Spaces.pth (Work.Spaces.DzIter j Φ)) z θ :=
        (Work.Elliptic.dtw_DthIter_slice_at (Work.Spaces.pth (Work.Spaces.DzIter j Φ)) m z θ).symm
    _ = Work.Spaces.DthIter m (Work.Spaces.DzIter j (Work.Spaces.pth Φ)) z θ :=
        Work.Blocks.Half.DthIter_congrOn Work.FTS.EllipticEst.isOpen_Q0
          (pth_DzIter_eqOn_Q0 hΦ j) m hy
    _ = Work.Spaces.DzIter j (Work.Spaces.DthIter m (Work.Spaces.pth Φ)) z θ :=
        DthIter_DzIter_comm_eqOn Work.FTS.EllipticEst.isOpen_Q0 hΦ.pth j m hy
    _ = Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ := rfl

/-! ## 4. Continuity of the slices of the quotient on `(0, π/2)` -/

/-- The slices `θ ↦ D_z^i (Φ/sin 2θ) z θ` are continuous on `(0, π/2)`.  Only the slice
smoothness of `D_z^i Φ` is used (via `DivSinFactor`). -/
theorem pz_cont_DzIter_div_of_slice {k : ℕ} {Φ : ℝ → ℝ → ℝ} {z : ℝ}
    (hsl : ∀ j : ℕ, j ≤ k → Work.Elliptic.SmoothSlice (fun θ => Work.Spaces.DzIter j Φ z θ))
    {i : ℕ} (hi : i ≤ k) :
    ContinuousOn
      (fun θ => Work.Spaces.DzIter i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hsm := hsl i hi
  have hcont : ContinuousOn (fun θ => Work.Spaces.DzIter i Φ z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.continuousOn.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩)
  refine (hcont.div (by fun_prop) (fun x hx => ne_of_gt (sin_two_pos_Ioo hx))).congr ?_
  intro θ hθ
  exact Work.Elliptic.DivSinFactor Φ i z θ hθ

/-- The mixed slices `θ ↦ D_z^j D_θ^i (Φ/sin 2θ) z θ` are continuous on `(0, π/2)`, for
`z > 0`: they are the `D_θ`-iterates of the smooth quotient `SinQ (D_z^j Φ z ·)`. -/
theorem pz_cont_mixed_div_of_slice {k : ℕ} {Φ : ℝ → ℝ → ℝ} {z : ℝ}
    (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ) (hzpos : 0 < z)
    (hsl : ∀ j : ℕ, j ≤ k → Work.Elliptic.SmoothSlice (fun θ => Work.Spaces.DzIter j Φ z θ))
    {j i : ℕ} (hj : j ≤ k) :
    ContinuousOn
      (fun θ => Work.Spaces.mixed j i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hsm := hsl j hj
  have hcd : ContDiffOn ℝ ⊤
      (Work.Elliptic.Dth1Iter i (Work.Elliptic.SinQ (fun θ => Work.Spaces.DzIter j Φ z θ)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.Blocks.Half.contDiffOn_Dth1Iter_of isOpen_Ioo
      (Work.Blocks.Half.contDiffOn_SinQ_of hsm) i
  refine hcd.continuousOn.congr ?_
  intro θ hθ
  exact mixed_div_eq_Dth1Iter_Q0 hΦ j i hzpos hθ

end Work.Blocks.DivSinHalf
