/-
# `FTS/StrongPersist/StarPkg6Aux.lean` — locality, vanishing and constant-raising lemmas

Support for `StarPkg6OfCore`.  Three groups of elementary facts:

* **Locality on the open quadrant**: `FlatW` only ever looks at `Q0 = (0,∞) × (0,π/2)`, so two
  functions agreeing there have the same `FlatW`-bounds.  (`FlatW_congr`.)
* **Vanishing on the complement of `Q0`** in the disjunctive form produced by
  `Work.FTS.PhiStar.CoreAux.fields_vanish` gives the shape consumed by the
  `WlInf`-transfer (`zeroOff_of_vanish`).
* **Monotonicity in the star constant**: all the quantitative fields of `StarPkgo` /
  `StarPkgo2` are of the form `T ≤ Cs * α`, so they are preserved when `Cs` is enlarged
  (`StarPkgo_raise_Cs`, `StarPkgo2_raise_Cs`).  This is what lets the order-six star package
  be assembled from the order-four one proved in `FTS/PhiStar` at a possibly smaller constant.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.PhiStar.CoreAux.FieldsDefs
import Submission.Work.FTS.PhiStar.CoreAux.Fb_basic
import Submission.Work.FTS.PhiStar.CoreAux.Fb_mul_theta_free
import Submission.Work.FTS.H2.STFacts
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Locality of `∂_θ` on the open quadrant**: two functions agreeing on `Q0` have the same
`θ`-derivative there.  (`deriv` is local and `(0,π/2)` is a neighbourhood of every interior
angle.) -/
theorem pth_congr_Q0 {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth f z θ = Work.Spaces.pth g z θ := by
  intro z θ hz hθ hθ'
  have heq : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => g z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (Real.pi / 2) from ⟨hθ, hθ'⟩)]
      with θ' hθ''
    exact h z θ' hz hθ''.1 hθ''.2
  simp only [Work.Spaces.pth]
  exact heq.deriv_eq

/-- **Monotonicity of `FlatW` in its constant.** -/
theorem FlatW_mono {l : ℕ} {f : ℝ → ℝ → ℝ} {K K' : ℝ}
    (h : Work.FTS.VocabO2.FlatW l f K) (hle : K ≤ K') :
    Work.FTS.VocabO2.FlatW l f K' := by
  intro z θ hz hθ hθ2
  obtain ⟨h1, h2⟩ := h z θ hz hθ hθ2
  exact ⟨fun k hk => le_trans (h1 k hk) hle, fun k i hki => le_trans (h2 k i hki) hle⟩

/-- **Locality of the flat class `FlatW`**: `FlatW n f K` is a statement about the open
quadrant only, and all the operators occurring in it (`∂_z^k`, `D_θ^i`, `∂_θ`) are local. -/
theorem FlatW_congr {n : ℕ} {K : ℝ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ)
    (hg : Work.FTS.VocabO2.FlatW n g K) : Work.FTS.VocabO2.FlatW n f K := by
  have hp : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth f z θ = Work.Spaces.pth g z θ := pth_congr_Q0 h
  intro z θ hz hθ hθ'
  obtain ⟨h1, h2⟩ := hg z θ hz hθ hθ'
  refine ⟨fun k hk => ?_, fun k i hki => ?_⟩
  · rw [Work.FTS.PhiStar.CoreAux.Fbq_pzIter_congr h k z θ hz hθ hθ']
    exact h1 k hk
  · have hD : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.DthIter i (Work.Spaces.pth f) z θ
          = Work.Spaces.DthIter i (Work.Spaces.pth g) z θ :=
      fun z θ hz hθ hθ' => Work.FTS.PhiStar.CoreAux.Fbq_DthIter_congr hp i z θ hz hθ hθ'
    rw [Work.FTS.PhiStar.CoreAux.Fbq_pzIter_congr hD k z θ hz hθ hθ']
    exact h2 k i hki

/-- The vanishing hypothesis of the `WlInf`-transfer, from the disjunctive form produced by
`fields_vanish`. -/
theorem zeroOff_of_vanish_Q0 {f : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → f z θ = 0) :
    ∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → f z θ = 0 := by
  intro z θ hmem
  refine h z θ ?_
  by_contra hcon
  push_neg at hcon
  exact hmem (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hcon.1, hcon.2.1, hcon.2.2⟩)

/-- **Monotonicity of `StarPkgo` in the star constant.**  Every quantitative field is a bound
`… ≤ Cs * α`; enlarging `Cs` (with `0 ≤ α`) preserves them. -/
theorem StarPkgo_raise_Cs {α Cs Cs' : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 ≤ α)
    (hle : Cs ≤ Cs') (h : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.VocabO.StarPkgo α Cs' Φs := by
  have hkey : Cs * α ≤ Cs' * α := mul_le_mul_of_nonneg_right hle hα
  exact
    { sol := h.sol
      smooth := h.smooth
      R := ⟨h.R.1, le_trans h.R.2 hkey⟩
      dU := ⟨h.dU.1, le_trans h.dU.2 hkey⟩
      V := ⟨h.V.1, le_trans h.V.2 hkey⟩
      vanishU := h.vanishU
      Vth := ⟨h.Vth.1, le_trans h.Vth.2 hkey⟩ }

/-- **Monotonicity of `StarPkgo2` in the star constant.** -/
theorem StarPkgo2_raise_Cs {α Cs Cs' : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 ≤ α)
    (hle : Cs ≤ Cs') (h : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.FTS.VocabO2.StarPkgo2 α Cs' Φs := by
  have hkey : Cs * α ≤ Cs' * α := mul_le_mul_of_nonneg_right hle hα
  exact
    { toStarPkgo := StarPkgo_raise_Cs hα hle h.toStarPkgo
      RW := ⟨h.RW.1, le_trans h.RW.2 hkey⟩
      VW := ⟨h.VW.1, le_trans h.VW.2 hkey⟩
      VzW := ⟨h.VzW.1, le_trans h.VzW.2 hkey⟩
      UsW := ⟨h.UsW.1, le_trans h.UsW.2 hkey⟩
      UszW := ⟨h.UszW.1, le_trans h.UszW.2 hkey⟩ }

/-! ## Congruence of `Fb` on the open quadrant -/

/-- `Fb` only looks at the open quadrant. -/
theorem Fb_congr_Q0 {n : ℕ} {K : ℝ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ)
    (hg : Work.FTS.PhiStar.Fb n K g) : Work.FTS.PhiStar.Fb n K f :=
  ⟨Work.FTS.PhiStar.CoreAux.Fbq_F0_congr h hg.f0,
    Work.FTS.PhiStar.CoreAux.Fbq_F0_congr (pth_congr_Q0 h) hg.fd⟩

/-! ## `pth` of functions of one variable -/

/-- `∂_θ` of a `z`-only function vanishes. -/
theorem pth_z_only (c : ℝ → ℝ) :
    Work.Spaces.pth (fun z _ : ℝ => c z) = fun _ _ => 0 := by
  funext z θ
  exact deriv_const θ (c z)

/-- `∂_θ` of a constant function vanishes. -/
theorem pth_const (c : ℝ) : Work.Spaces.pth (fun _ _ : ℝ => c) = fun _ _ => 0 := by
  funext z θ
  exact deriv_const θ c

/-- `∂_θ` of a `θ`-only function is its `ℝ`-derivative. -/
theorem pth_theta_only (c : ℝ → ℝ) :
    Work.Spaces.pth (fun _ θ : ℝ => c θ) = fun _ θ => deriv c θ := rfl

/-! ## Elementary `F0` facts -/

/-- The zero function is in every `F0 n`, with constant `0`. -/
theorem F0_zero (n : ℕ) : Work.FTS.PhiStar.F0 n 0 (fun _ _ : ℝ => 0) := by
  have hD : ∀ i : ℕ, Work.Spaces.DthIter i (fun _ _ : ℝ => 0) = fun _ _ => 0 := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
        rw [Work.Spaces.DthIter_succ, ih]
        funext z θ
        simp [Work.Spaces.Dth, Work.Spaces.pth]
  have hP : ∀ k : ℕ, Work.Spaces.pzIter k (fun _ _ : ℝ => 0) = fun _ _ => 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Work.Spaces.pzIter_succ, ih]
        funext z θ
        simp [Work.Spaces.pz]
  intro k i hki z θ hz hθ hθ'
  rw [hD i, hP k]
  simp

/-- **The `D_θ`-shift**: `F0 n` of `D_θ g` follows from `F0 (n+1)` of `g`. -/
theorem F0_Dth_shift {n : ℕ} {K : ℝ} {g : ℝ → ℝ → ℝ}
    (h : Work.FTS.PhiStar.F0 (n + 1) K g) : Work.FTS.PhiStar.F0 n K (Work.Spaces.Dth g) := by
  have key : ∀ i : ℕ, Work.Spaces.DthIter i (Work.Spaces.Dth g)
      = Work.Spaces.DthIter (i + 1) g := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [Work.Spaces.DthIter_succ, ih]; rfl
  intro k i hki x y hx hy hy'
  rw [key i]
  exact h k (i + 1) (by omega) x y hx hy hy'

/-- `SmoothOpen` of a constant function. -/
theorem smoothOpen_const (c : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ _ : ℝ => c) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall fun n => ?_
  have h : Function.uncurry (fun _ _ : ℝ => c) = fun _ : ℝ × ℝ => c := rfl
  rw [h]
  exact (contDiffOn_const : ContDiffOn ℝ (n : WithTop ℕ∞) (fun _ : ℝ × ℝ => (c : ℝ))
    Work.FTS.EllipticEst.Q0)

/-- `SmoothOpen` of a smooth `θ`-only function. -/
theorem smoothOpen_theta_only {c : ℝ → ℝ} (hc : ContDiff ℝ Work.Stability.smoothOrder c) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => c θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun _ θ : ℝ => c θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun _ θ : ℝ => c θ) = fun p : ℝ × ℝ => c p.2 := rfl
  rw [h]
  exact hc.comp_contDiffOn contDiff_snd.contDiffOn

/-- `SmoothOpen` of a smooth `z`-only function. -/
theorem smoothOpen_z_only {r : ℝ → ℝ} (hr : ContDiffOn ℝ Work.Stability.smoothOrder r (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => r z) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z _ : ℝ => r z)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z _ : ℝ => r z) = fun p : ℝ × ℝ => r p.1 := rfl
  rw [h]
  exact hr.comp contDiffOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

/-- `SmoothOpen` is closed under addition. -/
theorem smoothOpen_add {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall fun n => ?_
  have h : Function.uncurry (fun z θ => f z θ + g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p + Function.uncurry g p := rfl
  rw [h]
  exact (hf.forall n).add (hg.forall n)

/-- `SmoothOpen` is closed under negation. -/
theorem smoothOpen_neg {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -f z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall fun n => ?_
  have h : Function.uncurry (fun z θ => -f z θ)
      = fun p : ℝ × ℝ => -Function.uncurry f p := rfl
  rw [h]
  exact (hf.forall n).neg

/-- `SmoothOpen` is closed under multiplication by a constant. -/
theorem smoothOpen_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) :=
  Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul (smoothOpen_const c) hf

/-! ## The `ℝ`-derivative identities of the four angular coefficients -/

theorem deriv_sin_sq : deriv (fun θ : ℝ => Real.sin θ ^ 2) = fun θ => Real.sin (2 * θ) := by
  funext θ
  have h : HasDerivAt (fun θ : ℝ => Real.sin θ ^ 2)
      (2 * Real.sin θ ^ (2 - 1) * Real.cos θ) θ := (Real.hasDerivAt_sin θ).pow 2
  rw [h.deriv]
  have : 2 * Real.sin θ ^ (2 - 1) * Real.cos θ = 2 * Real.sin θ * Real.cos θ := by norm_num
  rw [this, ← Real.sin_two_mul]

theorem deriv_cos_sq_sub_two_sin_sq :
    deriv (fun θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)
      = fun θ => -3 * Real.sin (2 * θ) := by
  funext θ
  have h1 : HasDerivAt (fun θ : ℝ => Real.cos θ ^ 2)
      (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ)) θ := (Real.hasDerivAt_cos θ).pow 2
  have h2 : HasDerivAt (fun θ : ℝ => 2 * Real.sin θ ^ 2)
      (2 * (2 * Real.sin θ ^ (2 - 1) * Real.cos θ)) θ :=
    ((Real.hasDerivAt_sin θ).pow 2).const_mul 2
  have h := h1.sub h2
  have hd : deriv (fun θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) θ
      = 2 * Real.cos θ ^ (2 - 1) * -Real.sin θ
        - 2 * (2 * Real.sin θ ^ (2 - 1) * Real.cos θ) := by
    convert h.deriv using 1
  rw [hd]
  have hkey : 2 * Real.cos θ ^ (2 - 1) * -Real.sin θ
      - 2 * (2 * Real.sin θ ^ (2 - 1) * Real.cos θ)
      = -3 * (2 * Real.sin θ * Real.cos θ) := by norm_num; ring
  rw [hkey, ← Real.sin_two_mul]

theorem deriv_sin_two :
    deriv (fun θ : ℝ => Real.sin (2 * θ)) = fun θ => 2 * Real.cos (2 * θ) :=
  funext fun θ => (Work.FTS.H2.hasDerivAt_sin_two θ).deriv

theorem deriv_cos_two :
    deriv (fun θ : ℝ => Real.cos (2 * θ)) = fun θ => -2 * Real.sin (2 * θ) := by
  funext θ
  rw [(Work.FTS.H2.hasDerivAt_cos_two θ).deriv]
  ring


/-- `SmoothOpen` of the `θ`-derivative of the four angular coefficients of the star fields,
in the shape in which the product rules produce them. -/
theorem smoothOpen_pth_sin_sq :
    Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.pth (fun _ θ : ℝ => Real.sin θ ^ 2)) := by
  have heq : Work.Spaces.pth (fun _ θ : ℝ => Real.sin θ ^ 2)
      = fun _ θ : ℝ => Real.sin (2 * θ) := by
    rw [pth_theta_only, deriv_sin_sq]
  rw [heq]
  exact smoothOpen_theta_only (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id))

/-- The `θ`-derivative of `cos²θ - 2sin²θ` is smooth. -/
theorem smoothOpen_pth_cos_sq_sub :
    Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.pth (fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) := by
  have heq : Work.Spaces.pth (fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)
      = fun _ θ : ℝ => -3 * Real.sin (2 * θ) := by
    rw [pth_theta_only, deriv_cos_sq_sub_two_sin_sq]
  rw [heq]
  exact smoothOpen_theta_only
    (contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)))

/-- The `θ`-derivative of `sin 2θ` is smooth. -/
theorem smoothOpen_pth_sin_two :
    Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.pth (fun _ θ : ℝ => Real.sin (2 * θ))) := by
  have heq : Work.Spaces.pth (fun _ θ : ℝ => Real.sin (2 * θ))
      = fun _ θ : ℝ => 2 * Real.cos (2 * θ) := by
    rw [pth_theta_only, deriv_sin_two]
  rw [heq]
  exact smoothOpen_theta_only
    (contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)))

/-- The `θ`-derivative of `cos 2θ` is smooth. -/
theorem smoothOpen_pth_cos_two :
    Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.pth (fun _ θ : ℝ => Real.cos (2 * θ))) := by
  have heq : Work.Spaces.pth (fun _ θ : ℝ => Real.cos (2 * θ))
      = fun _ θ : ℝ => -2 * Real.sin (2 * θ) := by
    rw [pth_theta_only, deriv_cos_two]
  rw [heq]
  exact smoothOpen_theta_only
    (contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)))

/-- Multiplication of an `F0`-bound by a constant. -/
theorem F0_const_mul {n : ℕ} {K : ℝ} {f : ℝ → ℝ → ℝ} (h : Work.FTS.PhiStar.F0 n K f)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (c : ℝ) :
    Work.FTS.PhiStar.F0 n (2 ^ n * |c| * K) (fun z θ => c * f z θ) := by
  have hK0 : 0 ≤ K := Work.FTS.PhiStar.CoreAux.Fbq_nonneg_of_F0 h
  have hc : Work.FTS.PhiStar.F0 n |c| (fun _ _ : ℝ => c) := Work.FTS.PhiStar.F0.const n c
  have := Work.FTS.PhiStar.CoreAux.F0_mul (n := n) (K := |c|) (K' := K) (abs_nonneg c) hK0
    (smoothOpen_const c) hsm hc h
  simpa using this

/-- Multiplication of an `Fb`-bound by a constant. -/
theorem Fb_const_mul {n : ℕ} {K : ℝ} {f : ℝ → ℝ → ℝ} (h : Work.FTS.PhiStar.Fb n K f)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (c : ℝ) :
    Work.FTS.PhiStar.Fb n (2 ^ (n + 1) * K * |c|) (fun z θ => c * f z θ) := by
  have hK0 : 0 ≤ K := Work.FTS.PhiStar.CoreAux.Fbq_nonneg_of_F0 h.f0
  have hc : Work.FTS.PhiStar.F0 n |c| (fun _ _ : ℝ => c) := Work.FTS.PhiStar.F0.const n c
  have hcd : Work.FTS.PhiStar.F0 n |c|
      (Work.Spaces.pth (fun _ _ : ℝ => c)) := by
    rw [pth_const]
    exact Work.FTS.PhiStar.F0.mono le_rfl (abs_nonneg c) (F0_zero n)
  have h1 := Work.FTS.PhiStar.CoreAux.Fb_mul_theta_free (n := n) (K := K) (A := |c|) hK0
    (abs_nonneg c) hsm (smoothOpen_const c) h hc hcd
  exact Fb_congr_Q0 (fun z θ _ _ _ => by ring) h1

/-- `FlatW n f K` and `FlatW n f K'` are the same statement at the same order when the
constants agree. -/
theorem FlatW_mono' {l : ℕ} {f : ℝ → ℝ → ℝ} {K K' : ℝ} (h : Work.FTS.VocabO2.FlatW l f K)
    (hle : K ≤ K') : Work.FTS.VocabO2.FlatW l f K' := FlatW_mono h hle

/-- **`FlatW 6` from the two `F0` components**: the radial clause is the `i = 0` slot of
`F0 6`, and the angular clause is exactly `F0 5` of `∂_θ f`. -/
theorem flatW6_of_F0 {K : ℝ} {f : ℝ → ℝ → ℝ} (h1 : Work.FTS.PhiStar.F0 6 K f)
    (h2 : Work.FTS.PhiStar.F0 5 K (Work.Spaces.pth f)) :
    Work.FTS.VocabO2.FlatW 6 f K := by
  intro z θ hz hθ hθ'
  refine ⟨fun k hk => ?_, fun k i hki => h2 k i (by omega) z θ hz hθ hθ'⟩
  simpa using h1 k 0 (by omega) z θ hz hθ hθ'

end Work.FTS.StrongPersist
