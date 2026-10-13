/-
NOTE (added by the agent of `Work.FTS.EllSol.Shift2Flat.mixedSlotFiniteness`).

This module is a *verbatim copy* of `Submission/Work/FTS/EllSol/Shift2Flat/mixedSlotOfNice.lean`
with a single change: its import of `…ShiftFT.uTr_Athree` is re-pointed at
`Submission/Work/FTS/EllSol/Shift2Flat/uTrAthreeE.lean`, a copy of `…ShiftFT/uTr_Athree.lean`
whose (otherwise unnecessary) import of `…FlatFT.flatNiceAssembly` is replaced by the definition
of `nfStrip` and a local copy of `aesm_prod_of_continuousOn'`.

Reason: the tree contains two *different* lemmas under the same fully qualified name
`Work.FTS.EllSol.FlatFT.continuousOn_slice_joint` — one in `FlatFT/continuousOn_slice_joint.lean`
(used by `SpecAux.ShiftSlot11Lin`, hence by `Shift2Flat.niceSlotBoundHE`) and one in
`FlatFT/flatNiceAssembly.lean` (pulled in by `ShiftFT/uTr_Athree`).  Lean refuses to import both
into one environment, so the heavy `NiceFlat` bound `niceSlotBoundHE` and the truncation passage
`mixedSlotOfNice` cannot be combined directly.  The two copies above break that spurious clash on
the `uTr_Athree` side without touching any colleague's file.
-/

/-
Copyright: work module for the Elgindi finite-time singularity project.

# Finiteness of the heavy mixed slot from its "nice" (compactly supported) case

The target `Work.FTS.EllSol.Shift2Flat.mixedSlotOfNice` is the *general passage* for the
heavy (`σ_η = sin(2θ)^{-η}`) mixed slot of the shifted operator `L_b = ∂_t - b`:

* input: the bound `hNice` in the class `Work.FTS.EllSol.FlatFT.NiceFlat` (uniformly compact
  support in `t`) of `L_b`-data with the three heavy slots `(L_b f)²`, `(L_b²f)²` and
  `f_{θθ}²` integrable;
* output: the *finiteness* of the heavy mixed slot `∫⁻ (∂_θL_b u)²σ_η` for general data
  (`C²` on the open strip, vanishing at `θ = 0, π/2` as *values*, the same three slots
  integrable).

## Route

The naive cutoff `(t,θ) ↦ χ_N(t)·u(t,θ)` is *unusable* for `b ≠ 0`: the kernel of `L_b`
contains the growing "harmonic" modes `e^{bt}·A(θ)` (`A` affine), which are invisible to the
three slots but produce the cutoff error `χ_N'·u` of size `≈ N^{-1}e^{2bN}`.  Instead we use
the truncation of the *junk-free* quantity `v = L_b u` and solve the ODE exactly
(`Work.FTS.EllSol.ShiftFT.uTr N b u = phiTr N · Gc N b u`, with `L_b(uTr N b u) = χ_N·v` up to
the tail cutoff); the three slots of `uTr N b u` are then controlled by those of `u`
(`uTr_Aone`, `uTr_Atwo`, `uTr_Athree`, all proved), uniformly in `N`.

For `b ≥ 0` the construction `uTr` (backward solution) applies directly; for `b ≤ 0` we apply
the `b ≥ 0` result to the time-reflected datum `(t,θ) ↦ u(-t,θ)` with the reflected shift
`-b ≥ 0` (`Work.FTS.EllSol.Shift2Flat.reflectData`, `…reflectMixed`), the reflection
`(t,θ) ↦ (-t,θ)` being measure preserving on `ℝ × Iθ`.

The passage to the limit is Fatou's lemma: on `|t| < N` the mixed slot of `uTr N b u` is
*exactly* `∂_θL_b u` (`uTr_slotM_eq`), so the integrands converge pointwise to the target
integrand, while every truncation bound is bounded by one fixed real number `B`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.FTS.EllSol.Trunc.PassAux
import Submission.Work.FTS.EllSol.Trunc.PassAux2
import Submission.Work.FTS.EllSol.Trunc.chiMulDerivs
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPassDefs
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs
import Submission.Work.FTS.EllSol.ShiftFT.Gc_sh
import Submission.Work.FTS.EllSol.ShiftFT.Gc_pth
import Submission.Work.FTS.EllSol.ShiftFT.uTr_Aone
import Submission.Work.FTS.EllSol.ShiftFT.uTr_Atwo
import Submission.Work.FTS.EllSol.Shift2Flat.uTrAthreeE
import Submission.Work.FTS.EllSol.ShiftFT.uTr_niceFlat
import Submission.Work.FTS.EllSol.Shift2Flat.reflectData
import Submission.Work.FTS.EllSol.Shift2Flat.reflectMixed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Shift2Flat

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

noncomputable section

set_option autoImplicit false

/-! ## The integration domain and the four slot integrands -/

/-- The half-strip `ℝ × Iθ` carrying all the slot integrals. -/
abbrev slotI : Set (ℝ × ℝ) := (Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ

/-- The open strip `ℝ × (0, π/2)` on which the data is assumed `C²`. -/
abbrev slotStrip : Set (ℝ × ℝ) := (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)

theorem measurableSet_slotI : MeasurableSet slotI :=
  MeasurableSet.univ.prod (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)

theorem isOpen_slotStrip : IsOpen slotStrip := isOpen_univ.prod isOpen_Ioo

theorem slotI_eq_SI : slotI = Work.FTS.EllSol.Trunc.SI := rfl

theorem slotStrip_eq_strip : slotStrip = Work.FTS.EllSol.Trunc.strip := rfl

/-- The heavy `L_b`-slot `(∂_t f - b f)²·σ_η`. -/
def slotV (b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Work.Spaces.pz f p.1 p.2 - b * f p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2

/-- The heavy `L_b²`-slot `(∂_t²f - 2b ∂_tf + b²f)²·σ_η`. -/
def slotZ (b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Work.Spaces.pz (Work.Spaces.pz f) p.1 p.2 - 2 * b * Work.Spaces.pz f p.1 p.2
    + b ^ 2 * f p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2

/-- The heavy angular slot `(∂_θ²f)²·σ_η`. -/
def slotQ (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Work.Spaces.pth (Work.Spaces.pth f) p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2

/-- The heavy mixed slot `(∂_θL_b f)²·σ_η = (∂_θ∂_tf - b ∂_θf)²·σ_η`. -/
def slotM (b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Work.Spaces.pth (Work.Spaces.pz f) p.1 p.2 - b * Work.Spaces.pth f p.1 p.2) ^ 2
    * Work.FTS.EllipticEst.sEta p.2

@[simp] theorem slotV_apply (b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    slotV b f p = (Work.Spaces.pz f p.1 p.2 - b * f p.1 p.2) ^ 2
      * Work.FTS.EllipticEst.sEta p.2 := rfl

@[simp] theorem slotZ_apply (b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    slotZ b f p = (Work.Spaces.pz (Work.Spaces.pz f) p.1 p.2 - 2 * b * Work.Spaces.pz f p.1 p.2
      + b ^ 2 * f p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2 := rfl

@[simp] theorem slotQ_apply (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    slotQ f p = (Work.Spaces.pth (Work.Spaces.pth f) p.1 p.2) ^ 2
      * Work.FTS.EllipticEst.sEta p.2 := rfl

@[simp] theorem slotM_apply (b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    slotM b f p = (Work.Spaces.pth (Work.Spaces.pz f) p.1 p.2 - b * Work.Spaces.pth f p.1 p.2) ^ 2
      * Work.FTS.EllipticEst.sEta p.2 := rfl

theorem slotV_nonneg {b : ℝ} {f : ℝ → ℝ → ℝ} {p : ℝ × ℝ} (hp : p ∈ slotI) : 0 ≤ slotV b f p :=
  mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.FlatFT.wE_nonneg hp.2)

theorem slotZ_nonneg {b : ℝ} {f : ℝ → ℝ → ℝ} {p : ℝ × ℝ} (hp : p ∈ slotI) : 0 ≤ slotZ b f p :=
  mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.FlatFT.wE_nonneg hp.2)

theorem slotQ_nonneg {f : ℝ → ℝ → ℝ} {p : ℝ × ℝ} (hp : p ∈ slotI) : 0 ≤ slotQ f p :=
  mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.FlatFT.wE_nonneg hp.2)

theorem slotM_nonneg {b : ℝ} {f : ℝ → ℝ → ℝ} {p : ℝ × ℝ} (hp : p ∈ slotI) : 0 ≤ slotM b f p :=
  mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.FlatFT.wE_nonneg hp.2)

variable {b : ℝ} {u : ℝ → ℝ → ℝ}

/-! ## The mixed slot of the truncation is the mixed slot of the datum on the plateau -/

/-- On the plateau `|t| < N` the mixed slot `∂_θL_b` of the truncation `uTr N b u` agrees
pointwise with that of the datum `u`.  (The point is that `L_b (uTr N b u) = χ_N·L_b u` there,
and differentiating in `θ` commutes with the `t`-only cutoff.) -/
theorem uTr_slotM_eq (hu : ContDiffOn ℝ 2 (Function.uncurry u) slotStrip)
    (h0 : ∀ t : ℝ, u t 0 = 0) (hπ : ∀ t : ℝ, u t (Real.pi / 2) = 0)
    {N t θ : ℝ} (hN : (2 : ℝ) ≤ N) (ht : |t| < N) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    slotM b (Work.FTS.EllSol.ShiftFT.uTr N b u) (t, θ) = slotM b u (t, θ) := by
  have hNpos : 0 < N := lt_of_le_of_lt (abs_nonneg t) ht
  have hmem : (t, θ) ∈ slotStrip := ⟨trivial, hθ⟩
  have hstrip : IsOpen slotStrip := isOpen_slotStrip
  -- `uTr N b u` is `C²` on the strip
  have hUcd : ContDiffOn ℝ 2 (Function.uncurry (Work.FTS.EllSol.ShiftFT.uTr N b u)) slotStrip :=
    (Work.FTS.EllSol.ShiftFT.uTr_niceFlat N b u hN hu h0 hπ).1
  -- the `θ`-slices which occur below are differentiable at `θ`
  have hdPzU : DifferentiableAt ℝ
      (fun θ' => Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u) t θ') θ :=
    (Work.FTS.EllSol.Trunc.curry_differentiableAt_of_contDiffOn hstrip (n := 1) (by norm_num)
      (Work.FTS.EllSol.Trunc.contDiffOn_uncurry_pz_succ hstrip 1 hUcd) hmem).2
  have hdU : DifferentiableAt ℝ (fun θ' => Work.FTS.EllSol.ShiftFT.uTr N b u t θ') θ :=
    (Work.FTS.EllSol.Trunc.curry_differentiableAt_of_contDiffOn hstrip (n := 2) (by norm_num)
      hUcd hmem).2
  have hdPzu : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz u t θ') θ :=
    (Work.FTS.EllSol.Trunc.curry_differentiableAt_of_contDiffOn hstrip (n := 1) (by norm_num)
      (Work.FTS.EllSol.Trunc.contDiffOn_uncurry_pz_succ hstrip 1 hu) hmem).2
  have hdu : DifferentiableAt ℝ (fun θ' => u t θ') θ :=
    (Work.FTS.EllSol.Trunc.curry_differentiableAt_of_contDiffOn hstrip (n := 2) (by norm_num)
      hu hmem).2
  -- write both sides as derivatives
  have hleft : Work.Spaces.pth (Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u)) t θ
      - b * Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.uTr N b u) t θ
      = deriv (fun θ' => Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u) t θ'
          - b * Work.FTS.EllSol.ShiftFT.uTr N b u t θ') θ := by
    rw [show (fun θ' => Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u) t θ'
          - b * Work.FTS.EllSol.ShiftFT.uTr N b u t θ')
        = (fun θ' => Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u) t θ')
          - (fun θ' => b * Work.FTS.EllSol.ShiftFT.uTr N b u t θ') from rfl,
      deriv_sub hdPzU (hdU.const_mul b), deriv_const_mul b hdU]
    rfl
  have hright : Work.Spaces.pth (Work.Spaces.pz u) t θ - b * Work.Spaces.pth u t θ
      = deriv (fun θ' => Work.Spaces.pz u t θ' - b * u t θ') θ := by
    rw [show (fun θ' => Work.Spaces.pz u t θ' - b * u t θ')
        = (fun θ' => Work.Spaces.pz u t θ') - (fun θ' => b * u t θ') from rfl,
      deriv_sub hdPzu (hdu.const_mul b), deriv_const_mul b hdu]
    rfl
  -- the two functions of `θ` agree on the open interval
  have hev : (fun θ' => Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u) t θ'
        - b * Work.FTS.EllSol.ShiftFT.uTr N b u t θ')
      =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pz u t θ' - b * u t θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    rw [Work.FTS.EllSol.ShiftFT.uTrAone_uTr_sh N b u hu t θ' hθ',
      Work.FTS.EllSol.ShiftFT.uTrAone.deriv_phiTr_eq_zero_of_lt N t hNpos
        (by nlinarith [abs_nonneg t, ht]),
      Work.FTS.EllSol.ShiftFT.phiTr_eq_one hNpos (by linarith),
      Work.FTS.EllSol.Trunc.chi_eq_one hNpos (le_of_lt ht)]
    ring
  rw [slotM_apply, slotM_apply, hleft, hright, hev.deriv_eq]

/-! ## A.e. strong measurability of the truncation's mixed slot -/

/-- The mixed slot of `uTr N b u` is a.e. strongly measurable for `volume.restrict slotI`
(it is continuous on the open strip, which differs from `slotI` by the null set `θ = 0, π/2`). -/
theorem aesm_slotM_uTr (hu : ContDiffOn ℝ 2 (Function.uncurry u) slotStrip)
    (h0 : ∀ t : ℝ, u t 0 = 0) (hπ : ∀ t : ℝ, u t (Real.pi / 2) = 0)
    {N : ℝ} (hN : (2 : ℝ) ≤ N) :
    AEStronglyMeasurable (slotM b (Work.FTS.EllSol.ShiftFT.uTr N b u))
      (volume.restrict slotI) := by
  have hstrip : IsOpen slotStrip := isOpen_slotStrip
  have hUcd : ContDiffOn ℝ 2 (Function.uncurry (Work.FTS.EllSol.ShiftFT.uTr N b u)) slotStrip :=
    (Work.FTS.EllSol.ShiftFT.uTr_niceFlat N b u hN hu h0 hπ).1
  have h1 : ContDiffOn ℝ 0 (Function.uncurry
      (Work.Spaces.pth (Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u)))) slotStrip :=
    Work.FTS.EllSol.Trunc.contDiffOn_uncurry_pth_succ hstrip 0
      (Work.FTS.EllSol.Trunc.contDiffOn_uncurry_pz_succ hstrip 1 hUcd)
  have h2 : ContDiffOn ℝ 1 (Function.uncurry
      (Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.uTr N b u))) slotStrip :=
    Work.FTS.EllSol.Trunc.contDiffOn_uncurry_pth_succ hstrip 1 hUcd
  have hcont : ContinuousOn (slotM b (Work.FTS.EllSol.ShiftFT.uTr N b u)) slotStrip := by
    have hc1 : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.pth (Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u)) p.1 p.2)
        slotStrip := h1.continuousOn
    have hc2 : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.uTr N b u) p.1 p.2) slotStrip := h2.continuousOn
    have hW : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2) slotStrip :=
      Work.FTS.EllSol.Trunc.continuousOn_wE_comp
    have hsub : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.pth (Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u)) p.1 p.2
          - b * Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.uTr N b u) p.1 p.2) slotStrip :=
      hc1.sub (hc2.const_mul b)
    show ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pth (Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u)) p.1 p.2
        - b * Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.uTr N b u) p.1 p.2) ^ 2
        * Work.FTS.EllipticEst.sEta p.2) slotStrip
    exact (hsub.pow 2).mul hW
  exact Work.FTS.EllSol.Trunc.aesm_strip hcont

/-! ## The core: `b ≥ 0` -/

theorem slotFiniteness_nonneg
    (C : ℝ) (hCpos : 0 < C)
    (hC : ∀ (b : ℝ) (w : ℝ → ℝ → ℝ), Work.FTS.EllSol.FlatFT.NiceFlat w →
      MeasureTheory.IntegrableOn (slotV b w) slotI →
      MeasureTheory.IntegrableOn (slotZ b w) slotI →
      MeasureTheory.IntegrableOn (slotQ w) slotI →
      (∫⁻ p in slotI, ENNReal.ofReal (slotM b w p))
        ≤ ENNReal.ofReal (C * ((∫ p in slotI, slotV b w p)
            + Real.sqrt ((∫ p in slotI, slotZ b w p) * (∫ p in slotI, slotQ w p)))))
    (b : ℝ) (hb : 0 ≤ b) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) slotStrip)
    (h0 : ∀ t : ℝ, u t 0 = 0) (hπ : ∀ t : ℝ, u t (Real.pi / 2) = 0)
    (hV : MeasureTheory.IntegrableOn (slotV b u) slotI)
    (hZ : MeasureTheory.IntegrableOn (slotZ b u) slotI)
    (hQ : MeasureTheory.IntegrableOn (slotQ u) slotI) :
    (∫⁻ p in slotI, ENNReal.ofReal (slotM b u p)) < ⊤ := by
  -- the three slot bounds for the truncation family
  obtain ⟨K₁, hK₁pos, hK₁⟩ := Work.FTS.EllSol.ShiftFT.uTr_Aone b u hb hu h0 hπ hV
  obtain ⟨K₂, hK₂pos, hK₂⟩ := Work.FTS.EllSol.ShiftFT.uTr_Atwo b u hb hu h0 hπ hZ hV
  obtain ⟨K₃, hK₃pos, hK₃⟩ := Work.FTS.EllSol.ShiftFT.uTr_Athree b u hb hu h0 hπ hQ
  set A₁ : ℝ := ∫ p in slotI, slotV b u p with hA₁
  set A₂ : ℝ := ∫ p in slotI, slotZ b u p with hA₂
  set A₃ : ℝ := ∫ p in slotI, slotQ u p with hA₃
  have hA₁nn : 0 ≤ A₁ := by
    rw [hA₁]; exact MeasureTheory.setIntegral_nonneg measurableSet_slotI
      (fun p hp => slotV_nonneg hp)
  have hA₂nn : 0 ≤ A₂ := by
    rw [hA₂]; exact MeasureTheory.setIntegral_nonneg measurableSet_slotI
      (fun p hp => slotZ_nonneg hp)
  have hA₃nn : 0 ≤ A₃ := by
    rw [hA₃]; exact MeasureTheory.setIntegral_nonneg measurableSet_slotI
      (fun p hp => slotQ_nonneg hp)
  set B : ℝ := C * (K₁ * A₁ + Real.sqrt ((K₂ * A₂ + K₂ * A₁) * (K₃ * A₃))) with hB
  -- the uniform truncation bound
  have key : ∀ N : ℝ, 2 ≤ N →
      (∫⁻ p in slotI, ENNReal.ofReal
        (slotM b (Work.FTS.EllSol.ShiftFT.uTr N b u) p)) ≤ ENNReal.ofReal B := by
    intro N hN
    have hNF : Work.FTS.EllSol.FlatFT.NiceFlat (Work.FTS.EllSol.ShiftFT.uTr N b u) :=
      Work.FTS.EllSol.ShiftFT.uTr_niceFlat N b u hN hu h0 hπ
    obtain ⟨hI₁, hle₁⟩ := hK₁ N hN
    obtain ⟨hI₂, hle₂⟩ := hK₂ N hN
    obtain ⟨hI₃, hle₃⟩ := hK₃ N hN
    have hmain := hC b (Work.FTS.EllSol.ShiftFT.uTr N b u) hNF hI₁ hI₂ hI₃
    refine le_trans hmain (ENNReal.ofReal_le_ofReal ?_)
    set X : ℝ := ∫ p in slotI, slotV b (Work.FTS.EllSol.ShiftFT.uTr N b u) p with hX
    set Y : ℝ := ∫ p in slotI, slotZ b (Work.FTS.EllSol.ShiftFT.uTr N b u) p with hY
    set Z : ℝ := ∫ p in slotI, slotQ (Work.FTS.EllSol.ShiftFT.uTr N b u) p with hZ
    have hXle : X ≤ K₁ * A₁ := by rw [hX, hA₁]; exact hle₁
    have hYle : Y ≤ K₂ * A₂ + K₂ * A₁ := by
      have h1 : Y ≤ K₂ * A₂ + (K₂ / N) * A₁ := by rw [hY, hA₂, hA₁]; exact hle₂
      have h2 : (K₂ / N) * A₁ ≤ K₂ * A₁ := by
        have hN1 : (1 : ℝ) ≤ N := by linarith
        have : K₂ / N ≤ K₂ := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < N)]
          nlinarith [hK₂pos, hN1]
        exact mul_le_mul_of_nonneg_right this hA₁nn
      linarith
    have hZle : Z ≤ K₃ * A₃ := by rw [hZ, hA₃]; exact hle₃
    have hZnn : 0 ≤ Z := by
      rw [hZ]; exact MeasureTheory.setIntegral_nonneg measurableSet_slotI
        (fun p hp => slotQ_nonneg hp)
    have hK2A : 0 ≤ K₂ * A₂ + K₂ * A₁ := by nlinarith [hK₂pos, hA₁nn, hA₂nn]
    have hs : Real.sqrt (Y * Z) ≤ Real.sqrt ((K₂ * A₂ + K₂ * A₁) * (K₃ * A₃)) :=
      Real.sqrt_le_sqrt (mul_le_mul hYle hZle hZnn hK2A)
    have hsum : X + Real.sqrt (Y * Z)
        ≤ K₁ * A₁ + Real.sqrt ((K₂ * A₂ + K₂ * A₁) * (K₃ * A₃)) := add_le_add hXle hs
    calc C * (X + Real.sqrt (Y * Z))
        ≤ C * (K₁ * A₁ + Real.sqrt ((K₂ * A₂ + K₂ * A₁) * (K₃ * A₃))) :=
          mul_le_mul_of_nonneg_left hsum hCpos.le
      _ = B := by rw [hB]
  -- the truncation scale
  set Nf : ℕ → ℝ := fun n => (n : ℝ) + 2 with hNf
  have hNf2 : ∀ n : ℕ, 2 ≤ Nf n := by
    intro n; rw [hNf]; push_cast; have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
  -- a.e. strong measurability of every truncation integrand
  have hAE : ∀ n : ℕ, AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (slotM b (Work.FTS.EllSol.ShiftFT.uTr (Nf n) b u) p))
      (volume.restrict slotI) :=
    fun n => (aesm_slotM_uTr hu h0 hπ (hNf2 n)).aemeasurable.ennreal_ofReal
  -- the pointwise liminf
  have hlim : ∀ᵐ p ∂(volume.restrict slotI),
      ENNReal.ofReal (slotM b u p)
        = Filter.liminf (fun n : ℕ =>
            ENNReal.ofReal (slotM b (Work.FTS.EllSol.ShiftFT.uTr (Nf n) b u) p)) Filter.atTop := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_slotI]
    refine Filter.Eventually.of_forall (fun p hp => ?_)
    rcases lt_or_eq_of_le hp.2.1 with hpos | hzero
    · rcases lt_or_eq_of_le hp.2.2 with hlt | hpi
      · obtain ⟨n₀, hn₀⟩ := exists_nat_gt |p.1|
        have hev : (fun n : ℕ => ENNReal.ofReal
              (slotM b (Work.FTS.EllSol.ShiftFT.uTr (Nf n) b u) p))
            =ᶠ[Filter.atTop] (fun _ => ENNReal.ofReal (slotM b u p)) := by
          filter_upwards [Filter.eventually_atTop.mpr ⟨n₀, fun n hn => hn⟩] with n hn
          have hlt' : |p.1| < Nf n := by
            have h1 : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            rw [hNf]; push_cast; linarith
          rw [uTr_slotM_eq hu h0 hπ (hNf2 n) hlt' ⟨hpos, hlt⟩]
        rw [Filter.liminf_congr hev, Filter.liminf_const]
      · have hz : Work.FTS.EllipticEst.sEta p.2 = 0 := by
          rw [hpi]; exact Work.FTS.EllSol.Trunc.wE_pi_div_two
        have hzu : slotM b u p = 0 := by rw [slotM_apply, hz, mul_zero]
        have hzn : ∀ n : ℕ, slotM b (Work.FTS.EllSol.ShiftFT.uTr (Nf n) b u) p = 0 := by
          intro n; rw [slotM_apply, hz, mul_zero]
        rw [hzu]
        simp only [hzn, ENNReal.ofReal_zero]
        rw [Filter.liminf_const]
    · have hz : Work.FTS.EllipticEst.sEta p.2 = 0 := by
        rw [← hzero]; exact Work.FTS.EllSol.Trunc.wE_zero
      have hzu : slotM b u p = 0 := by rw [slotM_apply, hz, mul_zero]
      have hzn : ∀ n : ℕ, slotM b (Work.FTS.EllSol.ShiftFT.uTr (Nf n) b u) p = 0 := by
        intro n; rw [slotM_apply, hz, mul_zero]
      rw [hzu]
      simp only [hzn, ENNReal.ofReal_zero]
      rw [Filter.liminf_const]
  -- the Fatou chain
  have hstep : ∀ n : ℕ, (∫⁻ p in slotI, ENNReal.ofReal
      (slotM b (Work.FTS.EllSol.ShiftFT.uTr (Nf n) b u) p)) ≤ ENNReal.ofReal B :=
    fun n => key (Nf n) (hNf2 n)
  have hlimle : Filter.liminf (fun n : ℕ => ∫⁻ p in slotI, ENNReal.ofReal
      (slotM b (Work.FTS.EllSol.ShiftFT.uTr (Nf n) b u) p)) Filter.atTop ≤ ENNReal.ofReal B := by
    refine Filter.liminf_le_of_le ⟨0, Filter.Eventually.of_forall (fun n => bot_le)⟩ ?_
    intro x hx
    obtain ⟨n, hn⟩ := hx.exists
    exact le_trans hn (hstep n)
  calc (∫⁻ p in slotI, ENNReal.ofReal (slotM b u p))
      = ∫⁻ p in slotI, Filter.liminf (fun n : ℕ => ENNReal.ofReal
          (slotM b (Work.FTS.EllSol.ShiftFT.uTr (Nf n) b u) p)) Filter.atTop :=
        MeasureTheory.lintegral_congr_ae hlim
    _ ≤ Filter.liminf (fun n : ℕ => ∫⁻ p in slotI, ENNReal.ofReal
          (slotM b (Work.FTS.EllSol.ShiftFT.uTr (Nf n) b u) p)) Filter.atTop :=
        MeasureTheory.lintegral_liminf_le' hAE
    _ ≤ ENNReal.ofReal B := hlimle
    _ < ⊤ := ENNReal.ofReal_lt_top

end

theorem mixedSlotOfNice
    (hNice : ∃ C : ℝ, 0 < C ∧ ∀ (b : ℝ) (u : ℝ → ℝ → ℝ), Work.FTS.EllSol.FlatFT.NiceFlat u →
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ) →
      (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pz u) p.1 p.2 - b * Work.Spaces.pth u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2))
        ≤ ENNReal.ofReal (C * ((∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
            + Real.sqrt ((∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)))))
    (b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h0 : ∀ t : ℝ, u t 0 = 0) (hπ : ∀ t : ℝ, u t (Real.pi / 2) = 0)
    (hV : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ))
    (hZ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ))
    (hQ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ)) :
    (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pz u) p.1 p.2 - b * Work.Spaces.pth u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)) < ⊤ := by
  obtain ⟨C, hCpos, hC⟩ := hNice
  by_cases hb : 0 ≤ b
  · exact slotFiniteness_nonneg C hCpos hC b hb u hu h0 hπ hV hZ hQ
  · push_neg at hb
    -- for `b < 0` reflect the time variable: the reflected datum satisfies the same
    -- hypotheses with the shift `-b ≥ 0`
    have hb' : 0 ≤ -b := by linarith
    obtain ⟨hu', h0', hπ', hV', hZ', hQ'⟩ := reflectData b u hu h0 hπ hV hZ hQ
    have hcore := slotFiniteness_nonneg C hCpos hC (-b) hb' (fun t θ => u (-t) θ)
      hu' h0' hπ' hV' hZ' hQ'
    have hcore' : (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal
        ((Work.Spaces.pth (Work.Spaces.pz (fun t θ => u (-t) θ)) p.1 p.2
            - (-b) * Work.Spaces.pth (fun t θ => u (-t) θ) p.1 p.2) ^ 2
          * Work.FTS.EllipticEst.sEta p.2)) < ⊤ := hcore
    rw [← reflectMixed b u hu] at hcore'
    exact hcore'

end Work.FTS.EllSol.Shift2Flat
