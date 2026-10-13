/-
Copyright: work module for the Elgindi finite-time singularity project.

# The seven-slot honesty transfer from a plain family

The elliptic `ℋ^k`-estimate of the paper is applied on the class `ClassC` to the three
derivatives appearing in the equation,

  `z²∂_z²Ψ`,   `∂_θ²Ψ`,   `z ∂_z∂_θ²Ψ`

(`Work.FTS.ClassC.ellClassOk_hkEstimate`), so the corresponding `HkNorm` must be honest, i.e.
each of the three functions must be in `ℋ⁷` (`Work.Spaces.HkMem α 7`).  This module derives
that from the *plain* family

  `hfam : ∀ j m, j ≤ 9 → m ≤ 9 → HkMem α 0 (D_z^j ∂_θ^m Ψ)`.

The reduction `HkMem_of_plain_slots` (`Submission/Work/FTS/ClassC/HkMem_of_plain_slots.lean`)
turns `HkMem α 7 f` (for `f` smooth on the open quadrant) into the level-`0` honesty of the
plain slots `D_z^j f` and `D_z^j ∂_θ^r f` (`r ≥ 1`) of `f` itself.  It therefore suffices to
express the plain slots of each of the three functions above through the plain family of `Ψ`:

* `D_z^i (z²∂_z²Ψ) = z²∂_z²(D_z^i Ψ)` and `D_z^j ∂_θ^r (z²∂_z²Ψ) = z²∂_z²(D_z^j ∂_θ^r Ψ)` on the
  open quadrant (the operator `z²∂_z² = D_z² − D_z` is a polynomial in `D_z`, and `∂_θ`
  commutes with `z²∂_z²` by Clairaut);
* `∂_θ` commutes with the `D_z`-iterates (Clairaut for `∂_θ` and `∂_z`);
* at level `0`, `z²∂_z²h = D_z²h − D_zh` is honest as soon as `D_zh` and `D_z²h` are
  (`HkIntegrand α 0 g = (g·w/ sin(2θ)^{η/2})²` and `(x−y)² ≤ 2x² + 2y²`).

The slot indices never exceed the family bounds: e.g. the angular slot `(j,r)` of conjunct 1
uses `D_z^{j+2}∂_θ^rΨ` with `r + j ≤ 7`, so `j + 2 ≤ 9` and `r ≤ 9`, and the radial slot `(i)`
uses `D_z^{i+2}Ψ` with `i ≤ 7`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.HkMem_of_plain_slots
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.ClassC.NormPiecesAux.zsqPz2_DzIter_eqOn
import Submission.Work.Blocks.HalfInfra
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## 1. The operator algebra on the open quadrant -/

/-- `∂_θ` is local on an open set. -/
theorem seven_pth_congrOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) :
    Set.EqOn (Function.uncurry (Work.Spaces.pth g)) (Function.uncurry (Work.Spaces.pth g')) V := by
  intro p hp
  have hnb : ∀ᶠ θ' in 𝓝 p.2, (p.1, θ') ∈ V :=
    (Continuous.prodMk_right p.1).continuousAt.eventually (hV.mem_nhds hp)
  have hslice : (fun θ' => g p.1 θ') =ᶠ[𝓝 p.2] (fun θ' => g' p.1 θ') := by
    filter_upwards [hnb] with θ' hθ'
    exact h hθ'
  simpa only [Work.Spaces.pth, Function.uncurry] using hslice.deriv_eq

/-- The iterates of `∂_θ` compose. -/
theorem seven_pthIter_add (m n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter (m + n) f = Work.Spaces.pthIter m (Work.Spaces.pthIter n f) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_add, Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]

/-- The iterates of `D_z` compose. -/
theorem seven_DzIter_add (j b : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter (j + b) f = Work.Spaces.DzIter j (Work.Spaces.DzIter b f) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Nat.succ_add]
      show Work.Spaces.Dz (Work.Spaces.DzIter (j + b) f)
        = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.DzIter b f))
      rw [ih]

/-- **Clairaut for `∂_θ` and the `D_z`-iterates**: on the open quadrant the plain angular
derivative commutes with `D_z^b` for data which are `C^∞` there. -/
theorem seven_pth_DzIter_eqOn_Q0 {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (b : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (Work.Spaces.DzIter b f) z θ
        = Work.Spaces.DzIter b (Work.Spaces.pth f) z θ := by
  induction b with
  | zero => intro z θ _ _ _; rfl
  | succ b ih =>
      intro z θ hz hθ hπ
      have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hπ⟩
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter b f)) (z, θ) :=
        ((hf.DzIter b).forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)
      have h1 : Work.Spaces.pth (Work.Spaces.DzIter (b + 1) f) z θ
          = Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter b f)) z θ := by
        show Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter b f)) z θ = _
        exact Work.Blocks.Half.pth_Dz_apply_of hcd
      rw [h1]
      have h2 : Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter b f)) z θ
          = Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.pth f)) z θ :=
        Work.Blocks.Half.Dz_congrOn (g := Work.Spaces.pth (Work.Spaces.DzIter b f))
          (g' := Work.Spaces.DzIter b (Work.Spaces.pth f))
          Work.FTS.EllipticEst.isOpen_Q0
          (fun p hp' => ih p.1 p.2 hp'.1 hp'.2.1 hp'.2.2) hp
      rw [h2]
      rfl

/-- **Clairaut for the whole `∂_θ`-iterates and `D_z^b`**: `∂_θ^r` commutes with `D_z^b` on
the open quadrant. -/
theorem seven_pthIter_DzIter_eqOn_Q0 {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (r b : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pthIter r (Work.Spaces.DzIter b f) z θ
        = Work.Spaces.DzIter b (Work.Spaces.pthIter r f) z θ := by
  induction r with
  | zero => intro z θ _ _ _; rfl
  | succ r ih =>
      intro z θ hz hθ hπ
      have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hπ⟩
      have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ Work.FTS.EllipticEst.Q0 :=
        (Continuous.prodMk_right z).continuousAt.eventually
          (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)
      have hslice : (fun θ' => Work.Spaces.pthIter r (Work.Spaces.DzIter b f) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DzIter b (Work.Spaces.pthIter r f) z θ') := by
        filter_upwards [hnb] with θ' hθ'
        exact ih z θ' hz hθ'.2.1 hθ'.2.2
      have h1 : Work.Spaces.pthIter (r + 1) (Work.Spaces.DzIter b f) z θ
          = Work.Spaces.pth (Work.Spaces.DzIter b (Work.Spaces.pthIter r f)) z θ := by
        show Work.Spaces.pth (Work.Spaces.pthIter r (Work.Spaces.DzIter b f)) z θ = _
        exact hslice.deriv_eq
      rw [h1]
      exact seven_pth_DzIter_eqOn_Q0 (SmoothOpen_pthIter_classC hf r) b z θ hz hθ hπ

/-- **Clairaut for `∂_z` and the `∂_θ`-iterates**: `∂_z ∂_θ^r = ∂_θ^r ∂_z` on the open
quadrant. -/
theorem seven_pz_pthIter_eqOn_Q0 {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (r : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pz (Work.Spaces.pthIter r f) z θ
        = Work.Spaces.pthIter r (Work.Spaces.pz f) z θ := by
  induction r with
  | zero => intro z θ _ _ _; rfl
  | succ r ih =>
      intro z θ hz hθ hπ
      have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hπ⟩
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pthIter r f)) (z, θ) :=
        (((SmoothOpen_pthIter_classC hf r).forall 2)).contDiffAt
          (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)
      have h1 : Work.Spaces.pz (Work.Spaces.pthIter (r + 1) f) z θ
          = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pthIter r f)) z θ := by
        show Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pthIter r f)) z θ = _
        exact Work.Spaces.pz_pth_comm hcd
      rw [h1]
      have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ Work.FTS.EllipticEst.Q0 :=
        (Continuous.prodMk_right z).continuousAt.eventually
          (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)
      have hslice : (fun θ' => Work.Spaces.pz (Work.Spaces.pthIter r f) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pthIter r (Work.Spaces.pz f) z θ') := by
        filter_upwards [hnb] with θ' hθ'
        exact ih z θ' hz hθ'.2.1 hθ'.2.2
      have h2 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pthIter r f)) z θ
          = Work.Spaces.pth (Work.Spaces.pthIter r (Work.Spaces.pz f)) z θ := hslice.deriv_eq
      rw [h2]
      rfl

/-- **`∂_θ` commutes with `z²∂_z²`** on the open quadrant. -/
theorem seven_pzIter_two_pthIter_eqOn_Q0 {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (r : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pzIter 2 (Work.Spaces.pthIter r f) z θ
        = Work.Spaces.pthIter r (Work.Spaces.pzIter 2 f) z θ := by
  intro z θ hz hθ hπ
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hπ⟩
  have h1 : Work.Spaces.pzIter 2 (Work.Spaces.pthIter r f) z θ
      = Work.Spaces.pz (Work.Spaces.pthIter r (Work.Spaces.pz f)) z θ := by
    show Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.pthIter r f)) z θ = _
    exact Work.Blocks.Half.pz_congrOn (g := Work.Spaces.pz (Work.Spaces.pthIter r f))
      (g' := Work.Spaces.pthIter r (Work.Spaces.pz f)) Work.FTS.EllipticEst.isOpen_Q0
      (fun p hp' => seven_pz_pthIter_eqOn_Q0 hf r p.1 p.2 hp'.1 hp'.2.1 hp'.2.2) hp
  rw [h1]
  have h2 : Work.Spaces.pz (Work.Spaces.pthIter r (Work.Spaces.pz f)) z θ
      = Work.Spaces.pthIter r (Work.Spaces.pz (Work.Spaces.pz f)) z θ :=
    seven_pz_pthIter_eqOn_Q0 hf.pz r z θ hz hθ hπ
  rw [h2]
  rfl

/-- `∂_θ^r` commutes with multiplication by the `z`-only factor `z²` (identically, no
smoothness needed). -/
theorem seven_pthIter_zsq_mul (r : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter r (fun z θ => z ^ 2 * g z θ)
      = fun z θ => z ^ 2 * Work.Spaces.pthIter r g z θ := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]
      funext z θ
      show deriv (fun θ' => z ^ 2 * Work.Spaces.pthIter r g z θ') θ
        = z ^ 2 * deriv (fun θ' => Work.Spaces.pthIter r g z θ') θ
      rw [deriv_const_mul_field]

/-- **`∂_θ^r` commutes with `z²∂_z²`** on the open quadrant. -/
theorem seven_pthIter_zsqPz2_eqOn_Q0 {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (r : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pthIter r (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z θ
        = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter r f) z θ := by
  intro z θ hz hθ hπ
  rw [congrFun (congrFun (seven_pthIter_zsq_mul r (Work.Spaces.pzIter 2 f)) z) θ,
    seven_pzIter_two_pthIter_eqOn_Q0 hf r z θ hz hθ hπ]

/-! ## 2. The level-`0` identity `z²∂_z²h = D_z²h − D_zh` and its honesty transfer -/

/-- `(x − y)²c² ≤ 2(xc)² + 2(yc)²`. -/
theorem seven_sq_sub_mul_sq_le (x y c : ℝ) :
    ((x - y) * c) ^ 2 ≤ 2 * (x * c) ^ 2 + 2 * (y * c) ^ 2 := by
  nlinarith [sq_nonneg ((x + y) * c)]

/-- On the open quadrant, `z²∂_z²h = D_z²h − D_zh`. -/
theorem seven_zsq_pzIter_two_eq (h : ℝ → ℝ → ℝ) (hh : Work.FTS.EllipticEst.SmoothOpen h) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      z ^ 2 * Work.Spaces.pzIter 2 h z θ
        = Work.Spaces.DzIter 2 h z θ - Work.Spaces.DzIter 1 h z θ := by
  intro z θ hz hθ hπ
  have hd : HasDerivAt (fun z' => Work.Spaces.pzIter 1 h z' θ)
      (Work.Spaces.pzIter 2 h z θ) z := hh.hasDerivAt_slice_pzIter 1 ⟨hθ, hπ⟩ hz
  have e2 : Work.Spaces.DzIter 2 h z θ
      = z * (Work.Spaces.pzIter 1 h z θ + z * Work.Spaces.pzIter 2 h z θ) := by
    show z * deriv (fun z' => z' * Work.Spaces.pzIter 1 h z' θ) z = _
    have hmul : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pzIter 1 h z' θ)
        (1 * Work.Spaces.pzIter 1 h z θ + z * Work.Spaces.pzIter 2 h z θ) z :=
      (hasDerivAt_id z).mul hd
    rw [hmul.deriv]
    ring
  have e1 : Work.Spaces.DzIter 1 h z θ = z * Work.Spaces.pzIter 1 h z θ := rfl
  rw [e1, e2]
  ring

/-- **Level-`0` honesty of `z²∂_z²h`** from the level-`0` honesty of `D_zh` and `D_z²h`. -/
theorem seven_HkMem_zero_zsqPz2 {α : ℝ} {h : ℝ → ℝ → ℝ}
    (hh : Work.FTS.EllipticEst.SmoothOpen h)
    (h1 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 h))
    (h2 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 h)) :
    Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 h z θ) := by
  refine Work.FTS.EllipticEst.HkMem_of_majorant_ae α 0
    (f := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 h z θ)
    (M := fun z θ => 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 2 h) z θ
      + 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 1 h) z θ)
    (((hh.pzIter 2).zsq_mul).continuousOn_HkIntegrand α 0) ?_ ?_ ?_
  · intro z hz
    exact ((h2.1 z hz).const_mul 2).add ((h1.1 z hz).const_mul 2)
  · refine IntegrableOn.congr_fun ((h2.2.const_mul 2).add (h1.2.const_mul 2)) ?_ measurableSet_Ici
    intro z hz
    show 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 2 h) z θ)
        + 2 * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 1 h) z θ)
      = ∫ θ in Work.Spaces.Iθ, (2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 2 h) z θ
          + 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 1 h) z θ)
    rw [MeasureTheory.integral_add ((h2.1 z hz).const_mul 2) ((h1.1 z hz).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  · intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · subst hz0
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun θ _ => by
        rw [Work.FTS.LocData.HkIntegrand_zero_fst, Work.FTS.LocData.HkIntegrand_zero_fst,
          Work.FTS.LocData.HkIntegrand_zero_fst]
        norm_num
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      refine Filter.Eventually.of_forall fun θ hθ => ?_
      have hid := seven_zsq_pzIter_two_eq h hh z θ hzpos hθ.1 hθ.2
      have hsq := seven_sq_sub_mul_sq_le (Work.Spaces.DzIter 2 h z θ)
        (Work.Spaces.DzIter 1 h z θ)
        (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      rw [HkIntegrand_zero_eq_classC, HkIntegrand_zero_eq_classC, HkIntegrand_zero_eq_classC, hid]
      exact hsq

/-! ## 3. The three conjuncts -/

/-- **The seven-slot honesty transfer from a plain family.**  If all the plain slots
`D_z^j ∂_θ^m Ψ` (`j ≤ 9`, `m ≤ 9`) are honest at level `0` and `Ψ` is `C^∞` on the open
quadrant, then the three derivatives `z²∂_z²Ψ`, `∂_θ²Ψ` and `z∂_z∂_θ²Ψ` are in `ℋ⁷`. -/
theorem HkMem_seven_slots_of_plain_family {α : ℝ} (hα : 0 < α)
    (hγ : Work.Spaces.gam α ≤ 3 / 2) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hfam : ∀ j m : ℕ, j ≤ 9 → m ≤ 9 →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter j (Work.Spaces.pthIter m Ψ))) :
    Work.Spaces.HkMem α 7 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ∧
    Work.Spaces.HkMem α 7 (Work.Spaces.pthIter 2 Ψ) ∧
    Work.Spaces.HkMem α 7 (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) := by
  refine ⟨?_, ?_, ?_⟩
  · -- conjunct 1: `z²∂_z²Ψ`
    refine HkMem_of_plain_slots (k := 7) hα hγ ((hΨ.pzIter 2).zsq_mul) ?_ ?_
    · intro i hi
      refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0
        (u := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter i Ψ) z θ)
        (seven_HkMem_zero_zsqPz2 (hΨ.DzIter i) ?_ ?_) ?_
      · rw [← seven_DzIter_add 1 i Ψ]
        exact hfam (1 + i) 0 (by omega) (by norm_num)
      · rw [← seven_DzIter_add 2 i Ψ]
        exact hfam (2 + i) 0 (by omega) (by norm_num)
      · intro z hz θ hθ
        exact (Work.FTS.ClassC.NormPiecesAux.zsqPz2_DzIter_eqOn Ψ hΨ i z θ hz hθ.1 hθ.2).symm
    · intro j r hr hrj
      refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0
        (u := fun z θ => z ^ 2 * Work.Spaces.pzIter 2
          (Work.Spaces.DzIter j (Work.Spaces.pthIter r Ψ)) z θ)
        (seven_HkMem_zero_zsqPz2 ((SmoothOpen_pthIter_classC hΨ r).DzIter j) ?_ ?_) ?_
      · rw [← seven_DzIter_add 1 j (Work.Spaces.pthIter r Ψ)]
        exact hfam (1 + j) r (by omega) (by omega)
      · rw [← seven_DzIter_add 2 j (Work.Spaces.pthIter r Ψ)]
        exact hfam (2 + j) r (by omega) (by omega)
      · intro z hz θ hθ
        have hC : Work.Spaces.DzIter j
              (Work.Spaces.pthIter r (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
            = Work.Spaces.DzIter j
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter r Ψ) z θ) z θ := by
          refine Work.FTS.EllipticEst.SmoothOpen.DzIter_congr (F := Work.Spaces.pthIter r
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
            (G := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter r Ψ) z θ)
            (fun z' θ' hz' hθ' hπ' => ?_) j z θ hz hθ.1 hθ.2
          rw [congrFun (congrFun (seven_pthIter_zsq_mul r (Work.Spaces.pzIter 2 Ψ)) z') θ',
            seven_pzIter_two_pthIter_eqOn_Q0 hΨ r z' θ' hz' hθ' hπ']
        have hD : Work.Spaces.DzIter j
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter r Ψ) z θ) z θ
            = z ^ 2 * Work.Spaces.pzIter 2
              (Work.Spaces.DzIter j (Work.Spaces.pthIter r Ψ)) z θ :=
          Work.FTS.ClassC.NormPiecesAux.zsqPz2_DzIter_eqOn (Work.Spaces.pthIter r Ψ)
            (SmoothOpen_pthIter_classC hΨ r) j z θ hz hθ.1 hθ.2
        exact hD.symm.trans hC.symm
  · -- conjunct 2: `∂_θ²Ψ`
    refine HkMem_of_plain_slots (k := 7) hα hγ (SmoothOpen_pthIter_classC hΨ 2) ?_ ?_
    · intro i hi
      exact hfam i 2 (by omega) (by norm_num)
    · intro j r hr hrj
      have h1 : Work.Spaces.pthIter r (Work.Spaces.pthIter 2 Ψ)
          = Work.Spaces.pthIter (r + 2) Ψ := (seven_pthIter_add r 2 Ψ).symm
      have h2 : Work.Spaces.DzIter j (Work.Spaces.pthIter r (Work.Spaces.pthIter 2 Ψ))
          = Work.Spaces.DzIter j (Work.Spaces.pthIter (r + 2) Ψ) := by rw [h1]
      rw [h2]
      exact hfam j (r + 2) (by omega) (by omega)
  · -- conjunct 3: `z∂_z∂_θ²Ψ`
    refine HkMem_of_plain_slots (k := 7) hα hγ ((SmoothOpen_pthIter_classC hΨ 2).Dz) ?_ ?_
    · intro i hi
      have h1 : Work.Spaces.DzIter i (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)
          = Work.Spaces.DzIter (i + 1) (Work.Spaces.pthIter 2 Ψ) :=
        (seven_DzIter_add i 1 (Work.Spaces.pthIter 2 Ψ)).symm
      rw [h1]
      exact hfam (i + 1) 2 (by omega) (by norm_num)
    · intro j r hr hrj
      refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0
        (u := Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter (r + 2) Ψ))
        (hfam (j + 1) (r + 2) (by omega) (by omega)) ?_
      intro z hz θ hθ
      have hC : Work.Spaces.DzIter j
            (Work.Spaces.pthIter r (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ))) z θ
          = Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.pthIter (r + 2) Ψ)) z θ := by
        refine Work.FTS.EllipticEst.SmoothOpen.DzIter_congr
          (F := Work.Spaces.pthIter r (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)))
          (G := Work.Spaces.Dz (Work.Spaces.pthIter (r + 2) Ψ))
          (fun z' θ' hz' hθ' hπ' => ?_) j z θ hz hθ.1 hθ.2
        have hA : Work.Spaces.pthIter r (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) z' θ'
            = Work.Spaces.Dz (Work.Spaces.pthIter r (Work.Spaces.pthIter 2 Ψ)) z' θ' :=
          seven_pthIter_DzIter_eqOn_Q0 (SmoothOpen_pthIter_classC hΨ 2) r 1 z' θ' hz' hθ' hπ'
        rw [hA, (seven_pthIter_add r 2 Ψ).symm]
      have hD : Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.pthIter (r + 2) Ψ)) z θ
          = Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter (r + 2) Ψ) z θ :=
        congrFun (congrFun (seven_DzIter_add j 1 (Work.Spaces.pthIter (r + 2) Ψ)).symm z) θ
      exact hD.symm.trans hC.symm

end Work.FTS.ClassC
