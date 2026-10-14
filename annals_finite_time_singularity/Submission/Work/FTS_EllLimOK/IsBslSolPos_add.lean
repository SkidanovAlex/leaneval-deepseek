import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.weakSliceRegular
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.FTS.ClassC.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.dupNamespace false

/-! ## The angular normalisation -/

/-- canonical angular normalisation: kills the junk at θ ∉ (0,π/2). -/
def normTh (g : Fn) : Fn := fun z θ => if θ ∈ Set.Ioo 0 (π / 2) then g z θ else 0

/-- `normTh` as a linear map (it is the identity on the class, but it is a genuine projection). -/
def normThL : Fn →ₗ[ℝ] Fn where
  toFun := normTh
  map_add' f g := by
    funext z θ; by_cases h : θ ∈ Set.Ioo 0 (π / 2) <;> simp [normTh, h]
  map_smul' c f := by
    funext z θ; by_cases h : θ ∈ Set.Ioo 0 (π / 2) <;> simp [normTh, h]

@[simp] theorem normThL_apply (g : Fn) : normThL g = normTh g := rfl

@[simp] theorem normTh_apply_of_mem {g : Fn} {z θ : ℝ} (h : θ ∈ Set.Ioo 0 (π / 2)) :
    normTh g z θ = g z θ := by simp [normTh, h]

@[simp] theorem normTh_apply_of_not_mem {g : Fn} {z θ : ℝ} (h : θ ∉ Set.Ioo 0 (π / 2)) :
    normTh g z θ = 0 := by simp [normTh, h]

/-! ## The class `ClassC` -/

/-- **The source class `C`** (design (A)): open-quadrant smoothness and `ℋ⁷`-honesty, the
`BdryTraces`-vanishing of the integration-by-parts boundary terms up to order `6`, all-order
smoothness of the angular moment `F_*(g)`, an axis condition, and the vanishing of the `L₁₂`
mode at `z = 0`.

Every field is either an open-quadrant value, a limit, or an integral of `g`, so the class is
closed under `+` and `c • ·` (`classC_add`, `classC_smul` in `A1`).

## The two extra fields `mem8`, `tr7` (lead ruling, 2026-10-08 09:50)

The level-`6` `U`-slot of `EllPkgK` is `HkMem α 6 (Uop α Ξ / sin 2θ)`, whose top summand
`α·D_z⁷Ξ/sin 2θ` needs the trace of `D_z⁷Ξ` at the angular boundary for **every** `z`: the
`ℋ⁷`-honesty of the class supplies the traces only up to `j = 6`, so the frozen class is one
order short.  The lead's ruling adds `HkMem α 8 g` and `BdryTraces α 7 g` (the level-`8` weak
class supplies the `j = 7` trace), and the level-`6` slots are then stated over
`EllClassOk 8`; the level-`4` slots stay over `EllClassOk 7` by `EllClassOk`-monotonicity.
`ExistsEllSolC` is unchanged.

## The field `mem10` (lead ruling, 2026-10-11)

`PhiStar.bslOp_sol_exists` (`HkMem α k F ⇒ EllWeakPos α k`) is false at `k = 8` (top-order
counterexample, `cbc/fts_phistar_REVIEW.md` §2), and one order of slack is not enough either
(§3).  The repaired node `bslOp_sol_exists_pp` assumes `HkMem α (k+2) F`; A2 uses it at `k = 8`,
so the class carries `HkMem α 10 g`.  `EllClassOk 8` and everything downstream are unchanged.

## The field `thTr` (lead install R6, 2026-10-11)

`cbc/fts_ellnode_ruling.md` §4.4 + review fixes: `bslOp_sol_exists_pp 8` cannot be proved with the
in-tree machinery (compact-source density needs vanishing θ-traces, which do not follow from
`HkMem`).  The node on the path is now `PhiStar.EllNode8tr`, which also assumes
`ThetaTraces α 10` of the orthogonalised source; the class carries `ThetaTraces α 10 g` as its
LAST field (positional destructurings stay valid). -/
structure ClassC (α : ℝ) (g : Fn) : Prop where
  /-- `g` is already normalised in the angular variable: the only field that is not
  automatic for a general element of the ambient space. -/
  norm : normTh g = g
  /-- open-quadrant `C^∞` -/
  reg : Work.FTS.EllipticEst.SmoothOpen g
  /-- honesty of the `ℋ⁷`-integrand -/
  mem : Work.Spaces.HkMem α 7 g
  /-- honesty of the `ℋ⁸`-integrand (needed by the level-`6` slots) -/
  mem8 : Work.Spaces.HkMem α 8 g
  /-- honesty of the `ℋ¹⁰`-integrand (lead ruling 2026-10-11, `cbc/fts_phistar_REVIEW.md` §3):
  the repaired existence node `PhiStar.bslOp_sol_exists_pp 8` needs `HkMem α 10` of the
  orthogonalised source — two orders of slack over `EllWeakPos α 8`. -/
  mem10 : Work.Spaces.HkMem α 10 g
  /-- vanishing of the integration-by-parts boundary terms up to order `6` -/
  tr : Work.FTS.Nonlin.BdryTraces α 6 g
  /-- vanishing of the integration-by-parts boundary terms up to order `7` -/
  tr7 : Work.FTS.Nonlin.BdryTraces α 7 g
  /-- all-order smoothness of the angular moment `F_*(g)` on `(0,∞)` (`EllExist` proved this to be
  *necessary* for the existence node `EllClassO`, and it is the field the old class lacked) -/
  fsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar g) (Set.Ioi 0)
  /-- the axis condition `g(z,θ)/z → 0` as `z → 0⁺` -/
  axis : ∀ θ ∈ Set.Ioo 0 (π / 2), Tendsto (fun z => g z θ / z) (𝓝[>] 0) (𝓝 0)
  /-- the zero mode of `L₁₂` vanishes -/
  l12 : Work.Construction.L12 g 0 = 0
  /-- θ-traces of `D_z^s g`, `s ≤ 9` (lead install R6, 2026-10-11): the input of
  `PhiStar.EllNode8tr` beyond `mem10` (via `PhiStar.thetaTraces_orthSource`). -/
  thTr : Work.FTS.PhiStar.ThetaTraces α 10 g

/-! ## The package `EllPkgK` -/

/-- **The elliptic package at order `k`** (perturbation part only; the star part stays of
`StarPkgo`-type): the solution law, open-quadrant smoothness, and the `ℋ^k`-estimates for the
three operators `ℛ`, `U/sin 2θ`, `V` of §Modulation applied to `Φ̃ = PhiTil α g Φg`. -/
structure EllPkgK (α : ℝ) (k : ℕ) (Ce : ℝ) (g Φg : Fn) : Prop where
  sol : Work.FTS.StrongGlobal.IsBslSolPos α g Φg
  smooth : Work.FTS.EllipticEst.SmoothOpen Φg
  R : Work.FTS.VocabO.HQo α k (Work.Construction.Rop α (Work.Construction.PhiTil α g Φg)) ∧
      Work.Spaces.HkNorm α k (Work.Construction.Rop α (Work.Construction.PhiTil α g Φg))
        ≤ Ce * Work.Spaces.HkNorm α k g
  U : Work.FTS.VocabO.HQo α k (fun z θ => Work.Construction.Uop α
        (Work.Construction.PhiTil α g Φg) z θ / Work.Construction.s2 θ) ∧
      Work.Spaces.HkNorm α k (fun z θ => Work.Construction.Uop α
        (Work.Construction.PhiTil α g Φg) z θ / Work.Construction.s2 θ)
        ≤ Ce * Work.Spaces.HkNorm α k g
  V : Work.FTS.VocabO.HQo α k (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) ∧
      Work.Spaces.HkNorm α k (Work.Construction.Vop (Work.Construction.PhiTil α g Φg))
        ≤ Ce * Work.Spaces.HkNorm α k g


/-! ## Elementary API of the class -/

theorem ClassC.smoothOpen {α : ℝ} {g : Fn} (h : ClassC α g) :
    Work.FTS.EllipticEst.SmoothOpen g := h.reg




theorem ClassC.bdry {α : ℝ} {g : Fn} (h : ClassC α g) :
    Work.FTS.Nonlin.BdryTraces α 6 g := h.tr




theorem ClassC.l12_zero {α : ℝ} {g : Fn} (h : ClassC α g) :
    Work.Construction.L12 g 0 = 0 := h.l12

/-- The `BdryTraces` clause of the class at any level `≤ 6`. -/
theorem ClassC.bdry_le_six {α : ℝ} {g : Fn} (h : ClassC α g) {k : ℕ} (hk : k ≤ 6) :
    Work.FTS.Nonlin.BdryTraces α k g := fun a b hab => h.tr a b (le_trans hab hk)

/-- **`BdryTraces` is monotone in the level.** -/
theorem bdryTraces_mono {α : ℝ} {f : Fn} {k l : ℕ} (hkl : k ≤ l)
    (h : Work.FTS.Nonlin.BdryTraces α l f) : Work.FTS.Nonlin.BdryTraces α k f :=
  fun a b hab => h a b (le_trans hab hkl)

/-- **The class is inhabited**: `0` satisfies every field. -/
theorem classC_zero (α : ℝ) : ClassC α (0 : Fn) := by
  have htr : ∀ k : ℕ, Work.FTS.Nonlin.BdryTraces α k (0 : Fn) := by
    intro k a b hab
    have hmix : Work.Spaces.mixed b a (0 : Fn) = 0 := Work.FTS.EllipticEst.mixed_zero_fun b a
    refine ⟨?_, ?_⟩
    · intro θ hθ
      have h1 : (fun z => z * (Work.Spaces.mixed b a (0 : Fn) z θ * Work.Spaces.w z) ^ 2)
          = fun _ : ℝ => (0 : ℝ) := by
        funext z; rw [hmix]; simp
      rw [h1]; exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩
    · intro z hz
      have h1 : (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (0 : Fn) z θ) ^ 2) = fun _ : ℝ => (0 : ℝ) := by
        funext θ; rw [hmix]; simp
      rw [h1]; exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩
  refine ⟨?_, ?_, Work.FTS.EllipticEst.HkMem_zero α 7, Work.FTS.EllipticEst.HkMem_zero α 8,
    Work.FTS.EllipticEst.HkMem_zero α 10, htr 6, htr 7, ?_, ?_, ?_,
    fun s hs z hz => (htr 10 0 s (by omega)).2 z hz⟩
  · funext z θ
    by_cases h : θ ∈ Set.Ioo 0 (π / 2) <;> simp [normTh, h]
  · rw [Work.FTS.EllipticEst.SmoothOpen]
    change ContDiffOn ℝ Work.Stability.smoothOrder
      (fun _ : ℝ × ℝ => (0 : ℝ)) Work.FTS.EllipticEst.Q0
    exact contDiffOn_const
  · intro m
    have h1 : Work.Elliptic.Fstar (0 : Fn) = fun _ : ℝ => (0 : ℝ) := by
      funext z
      simp [Work.Elliptic.Fstar]
    rw [h1]
    exact contDiffOn_const
  · intro θ hθ
    have h1 : (fun z => (0 : Fn) z θ / z) = fun _ : ℝ => (0 : ℝ) := by
      funext z; simp
    rw [h1]; exact tendsto_const_nhds
  · simp [Work.Construction.L12, Work.Construction.L12dens, Work.FM.L12, Work.FM.L12dens]



end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.EllSol.VthAux.AeClean.SliceThree =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VthAux.AeClean

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθ" => Work.Spaces.Iθ
local notation "sEta" => Work.FTS.EllipticEst.sEta
local notation "SmoothOpen" => Work.FTS.EllipticEst.SmoothOpen


/-- Slice regularity of the weak class (the `ContinuousOn` conjunct of
`remov.weakSliceRegular`, whose `α ≤ 1/4` hypothesis is never used). -/
theorem sliceContinuous_of_weakPos_fts (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hα : 0 < α) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → ContinuousOn (fun θ => Ψ z θ) (Set.Icc 0 (Real.pi / 2)) := by
  intro z hz
  have hΨ : SmoothOpen Ψ := Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hsm : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.remov.ws_contDiffOn_slice hΨ hz
  have h7 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2 * sEta θ) Iθ :=
    Work.FTS.EllipticEst.remov.ws_slot_slice (hΨ.pth).pth h.memB 0 (by omega) hz
  obtain ⟨C, _hCpos, hC⟩ :=
    Work.FTS.EllipticEst.remov.abs_le_of_sq_mul_sEta hsm (by simpa using h7)
  have h5 : MeasureTheory.IntegrableOn (fun θ => (Ψ z θ) ^ 2) Iθ := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (C := C ^ 2)
        (Work.FTS.EllipticEst.remov.ws_vol_Iθ_ne_top) (by simp))
      ((Work.FTS.EllipticEst.remov.ws_aesm_slice hΨ hz).pow 2) ?_
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h1 : 0 ≤ (C - Ψ z θ) * (C + Ψ z θ) :=
      mul_nonneg (by linarith [le_abs_self (Ψ z θ), (hC θ hθ).2])
        (by linarith [neg_le_abs (Ψ z θ), (hC θ hθ).2])
    nlinarith [h1]
  have hL : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ) ^ 2 * sEta θ) Iθ :=
    Work.FTS.EllipticEst.remov.ws_Lzero1_energy_integrable hα hk h hz
  have hmom : (∫ θ in Iθ,
      Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ * Work.Elliptic.sinCos2 θ) = 0 :=
    (Work.FTS.EllipticEst.remov.wsMomentIdentity h hk
      (Work.FTS.EllipticEst.remov.wsMomentChain α k F Ψ hα hk h)
      (fun z' hz' => by
        have hpz := Work.FTS.EllipticEst.remov.ws_pz_energy_integrable
          (α := α) (k := k) (F := F) hk h hz'
        have h1 : MeasureTheory.IntegrableOn
            (fun θ => Work.Spaces.pz Ψ z' θ * Work.Elliptic.sinCos2 θ) Iθ :=
          (Work.FTS.EllipticEst.remov.ws_absMoment
            (Work.FTS.EllipticEst.remov.ws_aesm_slice (hΨ.pz) hz') hpz).1
        exact (h1.const_mul z').congr
          (Filter.Eventually.of_forall (fun θ => by
            simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
            ring)))
      (fun z' hz' θ hθ' => Work.FTS.EllipticEst.remov.DzIter_two_eq hΨ hz' hθ'))
      z hz
  exact Work.FTS.EllipticEst.remov.ws_continuousOn_Icc hsm.continuousOn (h.zero z) (h.pi_half z)
    (Work.FTS.EllipticEst.remov.wsSliceLeft hsm h7 hL hmom)
    (Work.FTS.EllipticEst.remov.sliceTendstoRight_fts hsm h7 hL h5)


end

end Work.FTS.EllSol.VthAux.AeClean
end
-- ===== merged: Submission.Work.FTS.StrongEps.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS)

set_option autoImplicit false

/-! ## The log coordinates and the two shifts -/

/-- The open quadrant of the paper's variables. -/
def Quad : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

theorem mem_Quad {z θ : ℝ} : (z, θ) ∈ Quad ↔ 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2) := Iff.rfl

/-- The `z`-shift of the mollifier: `s ↦ s - p`, i.e. `z ↦ z e^{-p}` in the variable `z`. -/
def zShift (z p : ℝ) : ℝ := z * Real.exp (-p)

/-- The `θ`-shift of the mollifier: `ζ ↦ ζ - p`, i.e. `θ ↦ arctan (tan θ · e^{-p})`. -/
def thShift (θ p : ℝ) : ℝ := Real.arctan (Real.tan θ * Real.exp (-p))

/-- The log-coordinate `s = log z`. -/
def sOf (z : ℝ) : ℝ := Real.log z


/-- The log-coordinate `ζ = log tan θ`. -/
def zetaOf (θ : ℝ) : ℝ := Real.log (Real.tan θ)


/-- The pull-back of a profile to the log-coordinates `(s,ζ) = (log z, log tan θ)`:
`Jeps` is, in these coordinates, the convolution of `logPull f` with `Jker ρ ε`. -/
def logPull (f : Fn) : ℝ × ℝ → ℝ := fun x => f (Real.exp x.1) (Real.arctan (Real.exp x.2))

/-! ## The mollifier kernel

`IsMollKernel ρ` is the class of admissible kernels: `ρ` is continuous, supported in the closed
unit ball of `ℝ²`, nonnegative, with total mass `1`.  Every statement of the `E1` chapter carries
it, and it is the only hypothesis on `ρ` anywhere in the area. -/

/-- **The admissible mollifier kernels.**  `ρ` is continuous, supported in the closed unit ball,
nonnegative and has total mass `1`.  (The support condition makes every `p`-integral below an
integral over the compact ball of radius `ε`; the mass condition makes `J_ε` approximate the
identity.) -/
structure IsMollKernel (ρ : ℝ × ℝ → ℝ) : Prop where
  /-- continuity of the kernel. -/
  cont : Continuous ρ
  /-- the support is contained in the closed unit ball. -/
  support : ∀ p : ℝ × ℝ, ρ p ≠ 0 → p.1 ^ 2 + p.2 ^ 2 ≤ 1
  /-- nonnegativity. -/
  nonneg : ∀ p : ℝ × ℝ, 0 ≤ ρ p
  /-- total mass one. -/
  mass : ∫ p : ℝ × ℝ, ρ p = 1

/-- **The smooth mollifier kernels**: the class needed by the *smoothing* property of `J_ε`
(`E1` of the design, `Jeps_contDiffOn`).  A merely continuous admissible kernel does *not*
suffice: in the log coordinates `J_ε` is the convolution with `Jker ρ ε`, and the derivatives can
only be pushed onto the kernel (the profile being mollified is merely locally integrable), so the
kernel itself must be `C^∞`. -/
structure IsSmoothKernel (ρ : ℝ × ℝ → ℝ) : Prop where
  /-- smoothness at every finite order (the order `⊤` of this Mathlib is *analyticity*). -/
  smooth : ∀ n : ℕ, ContDiff ℝ n ρ
  /-- the mass, support and nonnegativity conditions. -/
  moll : IsMollKernel ρ

/-- The rescaled kernel `k_ε(p) = ε^{-2} ρ(p/ε)` of `Jeps`, i.e. the density of `ρ` at scale
`ε` in the two log-coordinates. -/
def Jker (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (p : ℝ × ℝ) : ℝ := ε⁻¹ ^ 2 * ρ (ε⁻¹ • p)

/-! ## The mollifier `Jeps`, the family `Jfam`, the `ε`-scheme `IsEpsSol` and its uniform bound
`EpsUniform` (verbatim from `FTS_HARD_STMTS.lean.txt`) -/

/-- **(B) the log-coordinate mollifier** `J_ε`, verbatim from the lead's statement file.

In the log coordinates `s = log z`, `ζ = log tan θ` this is the convolution of `logPull f` with
the kernel `Jker ρ ε`; on the boundary of the quadrant (where the log coordinates degenerate) it
is defined to be `0`. -/
def Jeps (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (f : Fn) : Fn := fun z θ =>
  if 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2) then
    ∫ p : ℝ × ℝ, ε⁻¹ ^ 2 * ρ (ε⁻¹ • p) *
      f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2)))
  else 0

/-- The same, applied slicewise to a family (verbatim). -/
def Jfam (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (g : Fam) : Fam := fun z θ τ => Jeps ρ ε (slice g τ) z θ

/-- **the `ε`-scheme on `[0,T]`**: `∂_τ g = J_ε[𝓛-part + RHS](J_ε g)`, with
`Ψ = Φs + EllSol(J_ε g)` (verbatim). -/
def IsEpsSol (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε T : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn) (g : Fam) :
    Prop :=
  (∀ z θ, g z θ 0 = g₀ z θ) ∧
  ∀ z θ τ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → τ ∈ Set.Icc 0 T →
    HasDerivWithinAt (fun s => g z θ s)
      (Jeps ρ ε (fun z' θ' => dynLin α (Jfam ρ ε g) τ z' θ'
          + dynRHS α (Work.FTS.Nonlin.PsiCan Φs E (Jfam ρ ε g)) (Jfam ρ ε g) τ z' θ') z θ)
      (Set.Icc 0 T) τ


/-! ## Elementary consequences -/

@[simp] theorem Jfam_apply (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (g : Fam) (z θ τ : ℝ) :
    Jfam ρ ε g z θ τ = Jeps ρ ε (slice g τ) z θ := rfl

@[simp] theorem slice_Jfam (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (g : Fam) (τ : ℝ) :
    slice (Jfam ρ ε g) τ = Jeps ρ ε (slice g τ) := rfl

/-- The value of `Jeps` on the open quadrant: the log-coordinate convolution. -/
theorem Jeps_eq_integral (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (f : Fn) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Jeps ρ ε f z θ
      = ∫ p : ℝ × ℝ, Jker ρ ε p * f (zShift z p.1) (thShift θ p.2) := by
  simp only [Jeps, Jker, zShift, thShift, if_pos (show 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2) from ⟨hz, hθ⟩)]

/-- The value of `Jeps` at the boundary of the quadrant is `0`. -/
theorem Jeps_eq_zero (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (f : Fn) {z θ : ℝ}
    (h : ¬(0 < z ∧ θ ∈ Set.Ioo 0 (π / 2))) : Jeps ρ ε f z θ = 0 := by
  simp only [Jeps, if_neg h]

theorem Jeps_eq_zero_of_le (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (f : Fn) {z θ : ℝ} (hz : z ≤ 0) :
    Jeps ρ ε f z θ = 0 :=
  Jeps_eq_zero ρ ε f (fun h => absurd h.1 (not_lt.2 hz))

theorem Jeps_eq_zero_of_theta (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (f : Fn) {z θ : ℝ}
    (hθ : θ ∉ Set.Ioo 0 (π / 2)) : Jeps ρ ε f z θ = 0 :=
  Jeps_eq_zero ρ ε f (fun h => hθ h.2)


/-- `Jeps` of the zero profile. -/
@[simp] theorem Jeps_zero (ρ : ℝ × ℝ → ℝ) (ε : ℝ) :
    Jeps ρ ε (fun _ _ => 0) = fun _ _ => 0 := by
  funext z θ
  by_cases hc : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
  · rw [Jeps_eq_integral ρ ε _ hc.1 hc.2]
    simp
  · rw [Jeps_eq_zero ρ ε _ hc]

/-! ## The log coordinates -/

theorem zShift_pos {z p : ℝ} (hz : 0 < z) : 0 < zShift z p := by
  simpa only [zShift] using mul_pos hz (Real.exp_pos (-p))





theorem thShift_mem {θ p : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    thShift θ p ∈ Set.Ioo 0 (π / 2) := by
  have ht : 0 < Real.tan θ * Real.exp (-p) :=
    mul_pos (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2) (Real.exp_pos _)
  exact ⟨(Real.arctan_pos (x := Real.tan θ * Real.exp (-p))).2 ht,
    Real.arctan_lt_pi_div_two _⟩


/-- **The shift is the translation `(s,ζ) ↦ (s - p₁, ζ - p₂)` in the log coordinates**: this is
the identity that makes `Jeps` a convolution. -/
theorem logPull_shift (f : Fn) {z θ : ℝ} {p : ℝ × ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    logPull f (sOf z - p.1, zetaOf θ - p.2) = f (zShift z p.1) (thShift θ p.2) := by
  have h1 : Real.exp (sOf z - p.1) = zShift z p.1 := by
    rw [sOf, Real.exp_sub, Real.exp_log hz, zShift, div_eq_mul_inv, ← Real.exp_neg]
  have h2 : Real.exp (zetaOf θ - p.2) = Real.tan θ * Real.exp (-p.2) := by
    rw [zetaOf, Real.exp_sub, Real.exp_log (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2),
      div_eq_mul_inv, ← Real.exp_neg]
  simp only [logPull, thShift, h1, h2]


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongGlobal.Apriori =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.StrongGlobal

open Work.FTS.Nonlin
open Work.FTS.Apriori
open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS)

set_option autoImplicit false
set_option maxHeartbeats 1000000


end Work.FTS.StrongGlobal
end
end
-- ===== merged: Submission.Work.FTS.StrongGlobal.continuousAt_ite_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongGlobal



end Work.FTS.StrongGlobal
end
-- ===== merged: Submission.Work.FTS.StrongGlobal.dynRHS_congr =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongGlobal

/-- **`dynRHS` depends on a family only through its slice.**  With the canonical stream function
`PsiCan Φs EllSol`, the nonlinear right-hand side `dynRHS α Φ g τ` depends on `g` only through
`slice g τ`.

Proof: unfold `dynRHS`, `muDyn`, `lamDyn` and rewrite with the slice-congruences already proved in
`Submission/Work/FTS/StrongGlobal/Defs` (`Work.FTS.StrongGlobal.muDyn_congr`,
`Work.FTS.StrongGlobal.Ftau_congr`, `Work.FTS.StrongGlobal.slice_PsiCan_congr`, and the hypothesis
`h` itself). -/
theorem dynRHS_congr {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {EllSol : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g g' : Work.FTS.Galerkin.Fam}
    {τ : ℝ} (h : Work.FTS.Galerkin.slice g τ = Work.FTS.Galerkin.slice g' τ) :
    Work.FTS.Galerkin.dynRHS α (Work.FTS.Nonlin.PsiCan Φs EllSol g) g τ
      = Work.FTS.Galerkin.dynRHS α (Work.FTS.Nonlin.PsiCan Φs EllSol g') g' τ := by
  have hmu : Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs EllSol g) g τ
      = Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs EllSol g') g' τ :=
    muDyn_congr h
  simp only [Work.FTS.Galerkin.dynRHS, Work.FTS.Galerkin.lamDyn, hmu, Ftau_congr h,
    slice_PsiCan_congr h, h]

end Work.FTS.StrongGlobal
end
-- ===== merged: Submission.Work.FTS.StrongGlobal.exists_box_subset_slab =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongGlobal


end Work.FTS.StrongGlobal
end
-- ===== merged: Submission.Work.FTS.StrongGlobal.isDynGSolOnIcc_concat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongGlobal

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS muDyn lamDyn)
open Work.FTS.Nonlin (PsiCan)

set_option autoImplicit false

/-! ## Congruence lemmas for the gluing

The equation of the dynamic modulated problem depends on a family only through its slice; the
pointwise-in-time companion of `Work.FTS.Galerkin.dynRHS_congr` (which is stated for two families
whose *all* slices agree) is what the junction argument needs.  The two relative-neighbourhood
lemmas then let a within-derivative on `Icc a τ₀` be read as one on `Icc a b` (and symmetrically),
whenever `τ` is strictly inside the appropriate half. -/





end Work.FTS.StrongGlobal
end
-- ===== merged: Submission.Work.FTS.StrongGlobal.junction_fderiv_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongGlobal

open Work.FTS.Galerkin (Fam)

/-! ## Coordinates of the Fréchet derivative of a curried family

For a family `F : Fam = ℝ → ℝ → ℝ → ℝ` the uncurried map `uncurry3 F : P3 → ℝ`,
`p ↦ F p.1 p.2.1 p.2.2`, has at a point `(z,θ,τ)` at which it is differentiable the Fréchet
derivative whose value on `v = (v₁, v₂, v₃)` is the linear combination of the three partial
derivatives with coefficients `v₁`, `v₂`, `v₃`.  The three lemmas below compute the three
coordinate directions, and `fderiv_uncurry3_apply` packages them.

The proof of each coordinate direction is the chain rule along the (affine) curve
`s ↦ (s,θ,τ)` / `s ↦ (z,s,τ)` / `s ↦ (z,θ,s)`, whose derivative is the corresponding basis
vector; this is `HasFDerivAt.comp_hasDerivAt`. -/

/-- The first coordinate direction of the Fréchet derivative of `uncurry3 F` is the `z`-partial
derivative of `F`. -/
theorem fderiv_uncurry3_apply_fst {F : Fam} {z θ τ : ℝ}
    (hF : DifferentiableAt ℝ (uncurry3 F) (z, θ, τ)) :
    fderiv ℝ (uncurry3 F) (z, θ, τ) ((1 : ℝ), 0, 0) = deriv (fun s => F s θ τ) z := by
  have hc : HasDerivAt (fun s : ℝ => (s, θ, τ)) ((1 : ℝ), (0 : ℝ), (0 : ℝ)) z :=
    (hasDerivAt_id z).prodMk
      ((hasDerivAt_const (c := θ) (x := z)).prodMk (hasDerivAt_const (c := τ) (x := z)))
  have h := HasFDerivAt.comp_hasDerivAt (x := z) hF.hasFDerivAt hc
  rw [← h.deriv]
  simp [Function.comp_def]

/-- The second coordinate direction of the Fréchet derivative of `uncurry3 F` is the `θ`-partial
derivative of `F`. -/
theorem fderiv_uncurry3_apply_snd {F : Fam} {z θ τ : ℝ}
    (hF : DifferentiableAt ℝ (uncurry3 F) (z, θ, τ)) :
    fderiv ℝ (uncurry3 F) (z, θ, τ) ((0 : ℝ), 1, 0) = deriv (fun s => F z s τ) θ := by
  have hc : HasDerivAt (fun s : ℝ => (z, s, τ)) ((0 : ℝ), (1 : ℝ), (0 : ℝ)) θ :=
    (hasDerivAt_const (c := z) (x := θ)).prodMk
      ((hasDerivAt_id θ).prodMk (hasDerivAt_const (c := τ) (x := θ)))
  have h := HasFDerivAt.comp_hasDerivAt (x := θ) hF.hasFDerivAt hc
  rw [← h.deriv]
  simp [Function.comp_def]

/-- The third coordinate direction of the Fréchet derivative of `uncurry3 F` is the `τ`-partial
derivative of `F`. -/
theorem fderiv_uncurry3_apply_thd {F : Fam} {z θ τ : ℝ}
    (hF : DifferentiableAt ℝ (uncurry3 F) (z, θ, τ)) :
    fderiv ℝ (uncurry3 F) (z, θ, τ) ((0 : ℝ), 0, 1) = deriv (fun s => F z θ s) τ := by
  have hc : HasDerivAt (fun s : ℝ => (z, θ, s)) ((0 : ℝ), (0 : ℝ), (1 : ℝ)) τ :=
    (hasDerivAt_const (c := z) (x := τ)).prodMk
      ((hasDerivAt_const (c := θ) (x := τ)).prodMk (hasDerivAt_id τ))
  have h := HasFDerivAt.comp_hasDerivAt (x := τ) hF.hasFDerivAt hc
  rw [← h.deriv]
  simp [Function.comp_def]

/-- **The Fréchet derivative of a curried family, in coordinates.**  If `uncurry3 F` is
differentiable at `(z,θ,τ)` then its derivative there is the linear combination of the three
partial derivatives. -/
theorem fderiv_uncurry3_apply {F : Fam} {z θ τ : ℝ}
    (hF : DifferentiableAt ℝ (uncurry3 F) (z, θ, τ)) (v : P3) :
    fderiv ℝ (uncurry3 F) (z, θ, τ) v =
      v.1 * deriv (fun s => F s θ τ) z + v.2.1 * deriv (fun s => F z s τ) θ
        + v.2.2 * deriv (fun s => F z θ s) τ := by
  have h1 := fderiv_uncurry3_apply_fst (F := F) hF
  have h2 := fderiv_uncurry3_apply_snd (F := F) hF
  have h3 := fderiv_uncurry3_apply_thd (F := F) hF
  have hv : v = v.1 • (((1 : ℝ), 0, 0) : P3) + v.2.1 • (((0 : ℝ), 1, 0) : P3)
      + v.2.2 • (((0 : ℝ), 0, 1) : P3) := by
    ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_add, map_smul, map_smul, map_smul, h1, h2, h3]
  simp only [smul_eq_mul]


end Work.FTS.StrongGlobal
end
-- ===== merged: Submission.Work.FTS_EllLimOK.IsBslSolPos_add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_EllLimOK.IsBslSolPos_add` — additivity of the elliptic law `IsBslSolPos`

The law `IsBslSolPos α F Ψ` reads

  `∀ z > 0, ∀ θ ∈ (0, π/2), bslOp α Ψ z θ = F z θ`,  `Ψ z 0 = 0`,  `Ψ z (π/2) = 0` for `z ≥ 0`,
  `∀ θ ∈ Iθ, Ψ z θ → 0` as `z → ∞`.

Since `bslOp α` is a *linear* second order operator (`Work.Elliptic.bslOp_add`, whose only
extra hypothesis is joint `C²`-regularity of the two summands on the open quadrant), the first
clause is additive; the two Dirichlet clauses are values at `θ = 0` and `θ = π/2`, hence
additive; and the far-field decay is additive by `Filter.Tendsto.add`.

The pointwise form of the operator additivity on the open quadrant is recorded here as
`bslOp_add_of_contDiffOn` (it is the only `C²`-regularity bootstrap needed), and the open
quadrant is a neighbourhood of each of its points (`qd_mem_nhds`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Two elementary preliminaries -/

/-- The open quadrant is a neighbourhood of each of its points (`Qd` is `Ioi 0 ×ˢ Ioo 0 (π/2)`
by definition). -/
theorem qd_mem_nhds {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Construction.Qd ∈ 𝓝 (z, θ) :=
  (isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hz, hθ, hθ2⟩

/-- **Pointwise additivity of `bslOp` on the open quadrant**, from `C²`-regularity there.

This is `Work.Elliptic.bslOp_add` with the differentiability hypotheses discharged from the
`ContDiffOn` assumption on the open quadrant (where `cos θ ≠ 0` holds automatically). -/
theorem bslOp_add_of_contDiffOn {α : ℝ} {Ψ Φ : Fn}
    (hsΨ : ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.Construction.Qd)
    (hsΦ : ContDiffOn ℝ 2 (Function.uncurry Φ) Work.Construction.Qd)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Elliptic.bslOp α (fun z θ => Ψ z θ + Φ z θ) z θ
      = Work.Elliptic.bslOp α Ψ z θ + Work.Elliptic.bslOp α Φ z θ := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ2⟩)
  exact Work.Elliptic.bslOp_add α Ψ Φ z θ hcos
    (hsΨ.contDiffAt (qd_mem_nhds hz hθ hθ2)) (hsΦ.contDiffAt (qd_mem_nhds hz hθ hθ2))

/-! ## The additivity of the law -/

/-- **`IsBslSolPos` is additive**: the sum of two solutions of the (PolarBSL) problem solves the
(PolarBSL) problem for the sum of the data.  All four clauses are handled by the corresponding
linearity: the equation by `bslOp_add_of_contDiffOn`, the two Dirichlet values by `add`, and the
far-field decay by `Filter.Tendsto.add`. -/
theorem IsBslSolPos_add {α : ℝ} {F₁ F₂ Ψ₁ Ψ₂ : Work.FTS.Galerkin.Fn}
    (h₁ : Work.FTS.StrongGlobal.IsBslSolPos α F₁ Ψ₁)
    (h₂ : Work.FTS.StrongGlobal.IsBslSolPos α F₂ Ψ₂)
    (hs₁ : ContDiffOn ℝ 2 (Function.uncurry Ψ₁) Work.Construction.Qd)
    (hs₂ : ContDiffOn ℝ 2 (Function.uncurry Ψ₂) Work.Construction.Qd) :
    Work.FTS.StrongGlobal.IsBslSolPos α (fun z θ => F₁ z θ + F₂ z θ)
      (fun z θ => Ψ₁ z θ + Ψ₂ z θ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz θ hθ hθ2
    rw [bslOp_add_of_contDiffOn hs₁ hs₂ hz hθ hθ2, h₁.1 z hz θ hθ hθ2, h₂.1 z hz θ hθ hθ2]
  · intro z hz
    show Ψ₁ z 0 + Ψ₂ z 0 = 0
    rw [h₁.2.1 z hz, h₂.2.1 z hz, add_zero]
  · intro z hz
    show Ψ₁ z (π / 2) + Ψ₂ z (π / 2) = 0
    rw [h₁.2.2.1 z hz, h₂.2.2.1 z hz, add_zero]
  · intro θ hθ
    simpa using (h₁.2.2.2 θ hθ).add (h₂.2.2.2 θ hθ)

end Work.FTS_EllLimOK
end
end
