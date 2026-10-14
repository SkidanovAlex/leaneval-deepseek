import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.c2mGam_Wt_bound
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS_RegExport.Vz7Eslot

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.FinalV2.ESlot` — producer of `Work.FTS_RegExport.ESlotBd` for the wire
(design `cbc/fts_hvop_design.md`, 2026-10-11)

* `vopE_le_of_classC` — one slice: `|V(E f)| ≤ K (Ce+1) Xn f / αG` on the open quadrant, from
  `EllPkgGo` (`V`-slot of `Φ̃` + the sup lemma `TransportS.sup_dz_le_hk`, `b = 0`) and the
  `Θ`-part `2αG V(Θ f) = L₁₂ f · c2m` with `E5Aux2.L12XnBound`.
* `vopE_slice_le` — the dynamic family: `|V(E (slice g τ))| ≤ K (Ce+1) C₀ · pExp α`, through the
  `LimApprox` approximants (class C, `Xn ≤ C₀ αG²`) and `EllLimOK3` jet convergence (order ≤ 1).
* `eSlotBd_of_wire` — `ESlotBd α Cs g E` given the tie with `CE := K (Ce+1) C₀`.
* `tie_of_small` — the tie from `x ≤ 1/16`, `x (|Cs| + |CE|) ≤ 1/8`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS.FinalV2.ESlot

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp)

set_option autoImplicit false

theorem abs_c2m_le (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 := by
  simp only [Work.Construction.c2m]
  have h1 := Real.abs_cos_le_one (2 * θ)
  have h2 : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
  have h3 : Real.sin θ ^ 2 ≤ 1 := by nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)]
  rw [abs_le] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]

/-- `√x ≥ x` on `[0,1]`, in the form used below. -/
theorem inv_sqrt_le {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : 1 / Real.sqrt x ≤ 1 / x := by
  have hs : x ≤ Real.sqrt x := by
    have := Real.sqrt_le_sqrt hx1
    rw [Real.sqrt_one] at this
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  exact one_div_le_one_div_of_le hx hs

/-- **One slice.** -/
theorem vopE_le_of_classC : ∃ K : ℝ, 0 < K ∧ ∀ (αG Ce : ℝ) (E : Fn → Fn) (f : Fn),
    0 < αG → αG ≤ 1 → 0 ≤ Ce →
    Work.FTS.ClassC.ClassC αG f → Work.FTS.VocabO.EllPkgGo αG Ce f (E f) →
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop (E f) z θ|
        ≤ K * (Ce + 1) * (Work.FTS.Nonlin.Xn αG f / αG) := by
  obtain ⟨C₁, hC₁, hsup⟩ := Work.FTS.TransportS.sup_dz_le_hk
  obtain ⟨C₂, hC₂, hL12⟩ := Work.FTS.StrongEps.E5Aux2.L12XnBound
  refine ⟨10 * C₁ + C₂, by positivity, ?_⟩
  intro αG Ce E f hα hα1 hCe hf hE z θ hz hθ hθ2
  set X := Work.FTS.Nonlin.Xn αG f with hX
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  -- the decomposition `E f = Φ̃ + Θ`
  set A : ℝ → ℝ → ℝ := Work.Construction.PhiTil αG f (E f) with hA
  set B : ℝ → ℝ → ℝ := Work.Construction.Theta αG f with hB
  have hEf : E f = fun z θ => A z θ + B z θ := by
    funext a b; simp only [hA, hB, Work.Construction.PhiTil]; ring
  have hsm : ContDiffOn ℝ 3 (Function.uncurry (E f)) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (E f)).mp hE.smooth 3
  have hdE : DifferentiableAt ℝ (fun θ' => E f z θ') θ :=
    Work.FTS_RegExport.RXVP.NoHdat.vz7_differentiableAt_tslice hsm hz hθ hθ2
  have hdB : DifferentiableAt ℝ (fun θ' => B z θ') θ :=
    Work.FTS_RegExport.differentiableAt_thetaslice_Theta z θ
  have hdA : DifferentiableAt ℝ (fun θ' => A z θ') θ := by
    simp only [hA, Work.Construction.PhiTil]; exact hdE.sub hdB
  have hsplit : Work.Construction.Vop (E f) z θ
      = Work.Construction.Vop A z θ + Work.Construction.Vop B z θ := by
    rw [hEf]; exact Work.FTS_RegExport.Vop_add_point hdA hdB
  -- the `Φ̃` part
  have hγ : Work.Spaces.gam αG - 1 = αG / 10 := Work.Spaces.gam_sub_one αG
  have hVA : |Work.Construction.Vop A z θ| ≤ 10 * C₁ * Ce * (X / αG) := by
    have h0 := hsup αG (Work.Construction.Vop A) hα hα1 hE.V.1.1 hE.V.1.2 0 (by norm_num)
      z θ hz hθ hθ2
    simp only [Work.Spaces.DzIter_zero] at h0
    have hXV : Work.FTS.Nonlin.Xn αG (Work.Construction.Vop A) ≤ Ce * X := hE.V.2
    have hXV0 : 0 ≤ Work.FTS.Nonlin.Xn αG (Work.Construction.Vop A) := Real.sqrt_nonneg _
    rw [hγ] at h0
    have hq : 1 / Real.sqrt (αG / 10) ≤ 1 / (αG / 10) :=
      inv_sqrt_le (by positivity) (by linarith)
    have hc : C₁ / Real.sqrt (αG / 10) ≤ 10 * C₁ / αG := by
      have : C₁ / Real.sqrt (αG / 10) = C₁ * (1 / Real.sqrt (αG / 10)) := by ring
      rw [this]
      calc C₁ * (1 / Real.sqrt (αG / 10)) ≤ C₁ * (1 / (αG / 10)) :=
            mul_le_mul_of_nonneg_left hq hC₁.le
        _ = 10 * C₁ / αG := by field_simp
    calc |Work.Construction.Vop A z θ|
        ≤ C₁ / Real.sqrt (αG / 10) * Work.FTS.Nonlin.Xn αG (Work.Construction.Vop A) := h0
      _ ≤ 10 * C₁ / αG * (Ce * X) :=
          mul_le_mul hc hXV hXV0 (by positivity)
      _ = 10 * C₁ * Ce * (X / αG) := by ring
  -- the `Θ` part
  have hVB : |Work.Construction.Vop B z θ| ≤ C₂ * (X / αG) := by
    have hid := Work.FTS_RegExport.two_mul_Vop_Theta (αG := αG) hα (F := f) (z := z) hθ hθ2
    have hHQ : Work.FTS.VocabO.HQo αG 4 f :=
      ⟨hf.reg, Work.FTS.OpenPkg.HkMem_mono_open hf.reg 4 (by norm_num) hf.mem⟩
    have hL := hL12 αG hα f hHQ z hz.le
    have hc := abs_c2m_le θ
    have heq : Work.Construction.Vop B z θ
        = Work.Construction.L12 f z * Work.Construction.c2m θ / (2 * αG) := by
      rw [hB, ← hid]; field_simp
    rw [heq, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * αG)]
    have h1 : |Work.Construction.L12 f z| * |Work.Construction.c2m θ| ≤ C₂ * X * 2 :=
      mul_le_mul hL hc (abs_nonneg _) (by positivity)
    calc |Work.Construction.L12 f z| * |Work.Construction.c2m θ| / (2 * αG)
        ≤ C₂ * X * 2 / (2 * αG) := div_le_div_of_nonneg_right h1 (by positivity)
      _ = C₂ * (X / αG) := by field_simp
  have hXa : 0 ≤ X / αG := div_nonneg hX0 hα.le
  rw [hsplit]
  calc |Work.Construction.Vop A z θ + Work.Construction.Vop B z θ|
      ≤ |Work.Construction.Vop A z θ| + |Work.Construction.Vop B z θ| := abs_add_le _ _
    _ ≤ 10 * C₁ * Ce * (X / αG) + C₂ * (X / αG) := add_le_add hVA hVB
    _ ≤ (10 * C₁ + C₂) * (Ce + 1) * (X / αG) := by
        nlinarith [mul_nonneg (mul_nonneg hC₁.le hCe) hXa, mul_nonneg hC₂.le hXa,
          mul_nonneg hC₁.le hXa, mul_nonneg (mul_nonneg hC₂.le hCe) hXa]

/-- `V` at a point of the quadrant through the order-`≤ 1` jets. -/
theorem vop_eq_mixed {Ψ : Fn} {z θ : ℝ} (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Construction.Vop Ψ z θ
      = Work.Spaces.mixed 0 1 Ψ z θ / Real.sin (2 * θ) - Real.tan θ * Work.Spaces.mixed 0 0 Ψ z θ := by
  have hs : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  simp only [Work.Construction.Vop, Work.Spaces.mixed, Work.Spaces.DzIter_zero,
    Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.Dth]
  field_simp

/-- **The dynamic family**: the uniform `pExp α`-rate bound on `V(E (slice g τ))`. -/
theorem vopE_slice_le : ∃ K : ℝ, 0 < K ∧ ∀ {α C₀ Ce : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam},
    0 < α → α ≤ 1 / 3 → 0 ≤ Ce →
    (∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u)) →
    EllLimOK3 (pExp α) E → DynOK' (pExp α) C₀ Φs E g →
    ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop (E (slice g τ)) z θ| ≤ K * (Ce + 1) * C₀ * pExp α := by
  obtain ⟨K, hK, hone⟩ := vopE_le_of_classC
  refine ⟨K, hK, ?_⟩
  intro α C₀ Ce Φs E g hα hα13 hCe hEll hEL3 hOK τ z θ hτ hz hθ hθ2
  have hαG : 0 < pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨gn, B, L, hC, -, hjet, -⟩ := hOK.2 (τ + 1) (by linarith)
  have hτT : τ ∈ Set.Icc (0 : ℝ) (τ + 1) := ⟨hτ, by linarith⟩
  have hlim := (hEL3 (fun n => slice (gn n) τ) (slice g τ) B
      (fun n => (hC n τ hτT).1) (fun n => (hC n τ hτT).2.2)
      (hOK.1.1.c4 τ hτ) (fun j i hji z θ hzθ => hjet τ hτT j i hji z θ hzθ)).2.2
  have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ, hθ2⟩
  have h01 := hlim 0 1 (by norm_num) z θ hzθ
  have h00 := hlim 0 0 (by norm_num) z θ hzθ
  have hT : Tendsto (fun n => Work.Construction.Vop (E (slice (gn n) τ)) z θ) atTop
      (𝓝 (Work.Construction.Vop (E (slice g τ)) z θ)) := by
    simp only [vop_eq_mixed hθ hθ2]
    exact (h01.div_const _).sub (h00.const_mul _)
  have hbd : ∀ n, |Work.Construction.Vop (E (slice (gn n) τ)) z θ|
      ≤ K * (Ce + 1) * C₀ * pExp α := by
    intro n
    obtain ⟨hCn, hXn, -⟩ := hC n τ hτT
    have h1 := hone (pExp α) Ce E (slice (gn n) τ) hαG hαG1 hCe hCn (hEll _ hCn).1 z θ hz hθ hθ2
    have hX : Work.FTS.Nonlin.Xn (pExp α) (slice (gn n) τ) / pExp α ≤ C₀ * pExp α := by
      rw [div_le_iff₀ hαG]; nlinarith
    calc _ ≤ K * (Ce + 1) * (Work.FTS.Nonlin.Xn (pExp α) (slice (gn n) τ) / pExp α) := h1
      _ ≤ K * (Ce + 1) * (C₀ * pExp α) :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ = K * (Ce + 1) * C₀ * pExp α := by ring
  exact le_of_tendsto' (hT.abs) hbd

/-- **The producer of `ESlotBd`**, given the tie at `CE := K (Ce+1) C₀`. -/
theorem eSlotBd_of_wire : ∃ K : ℝ, 0 < K ∧ ∀ {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam},
    0 < α → α ≤ 1 / 3 → 0 ≤ Ce →
    (∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u)) →
    EllLimOK3 (pExp α) E → DynOK' (pExp α) C₀ Φs E g →
    4 * pExp α + 2 * Cs * pExp α ^ 2 + 2 * (K * (Ce + 1) * C₀) * pExp α ^ 2 ≤ 1 / 2 →
    Work.FTS_RegExport.ESlotBd α Cs g ⇑E := by
  obtain ⟨K, hK, hV⟩ := vopE_slice_le
  refine ⟨K, hK, ?_⟩
  intro α C₀ Ce Cs Φs E g hα hα13 hCe hEll hEL3 hOK htie
  exact ⟨K * (Ce + 1) * C₀, fun τ z θ hτ hz hθ hθ2 =>
    hV (Φs := Φs) hα hα13 hCe hEll hEL3 hOK τ z θ hτ hz hθ hθ2, htie⟩

/-- **The tie from smallness** (for the wire's choice of `α`). -/
theorem tie_of_small {x Cs CE : ℝ} (hx : 0 < x) (hx16 : x ≤ 1 / 16)
    (hxC : x * (|Cs| + |CE|) ≤ 1 / 8) :
    4 * x + 2 * Cs * x ^ 2 + 2 * CE * x ^ 2 ≤ 1 / 2 := by
  have h1 : Cs * x ^ 2 ≤ |Cs| * x ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
  have h2 : CE * x ^ 2 ≤ |CE| * x ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
  have h3 : (|Cs| + |CE|) * x ^ 2 ≤ x / 8 := by nlinarith
  nlinarith

end Work.FTS.FinalV2.ESlot
