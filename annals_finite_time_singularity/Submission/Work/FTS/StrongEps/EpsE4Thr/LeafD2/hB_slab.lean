import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.XStep
import Submission.Work.FTS.StrongEps.EpsE4Thr.LeafD2.continuousOn_slab_of_lipschitz
import Submission.Work.FTS.StrongEps.EpsE4Thr.LeafD2.fderivFeps_sub_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `EpsE4Thr/LeafD2/hB_slab.lean` — the `hB` conjunct of LEAF-D2

`E4R5.RegDataD` asks for the joint continuity of the spatial `fderiv` of the projected right-hand
side along the Picard limit curve,

  `p ↦ fderiv ℝ (uncurry (Feps α ρ ε Φs E (slice (limFam (Feps …) h₀) p.2.2))) (p.1, p.2.1)`,

on the slab `(0,∞) × (0,π/2) × [0,δ]`.

**Status of the requested statement `hB_slab`.**  The hypotheses `hlim` (the `X`-ball clause for the
*limit* slices at every fake time) and `hvol` (the pointwise Volterra identity) are **not
sufficient**: the conclusion is a statement about the dependence of the *spatial derivative* of the
right-hand side on the fake time, and the only channel between different fake times in those two
hypotheses is the pointwise identity `hvol`, whose Bochner integrals are `0` (junk) whenever the
integrand is not a.e. strongly measurable in the fake time — a situation that is compatible with the
hypotheses and that *jumps*.  Formally the estimate needs

  `EpsSq α (slice σ − slice τ) ≤ L' (σ − τ)²`   (`hLips` below),

or equivalently the joint a.e. strong measurability of `(s,p) ↦ Feps … (slice s) p · epsW p`, which
the in-tree machinery produces only from the **Picard iterate** data (the iterate `X`-ball clause
`hiter`, the two gates and the room `δ √L < 1`) — none of which follows from `hlim` + `hvol`; the
proved sibling `LeafD2.limEpsSq_lipschitz` is exactly the same estimate *with* that data.
`LeafD2/NOTES_hB_plan.md` and `LeafD2/NOTES_limEpsSq_lip_hvol_verdict.md` record the full analysis;
`EpsE4Thr/RegDataWired.lean` is the consumer route that uses the strengthened hypothesis list.

What is proved here (all axiom-clean, no unproven imports):

* `hB_slab_of_lipschitz_bundle` — the requested *conclusion*, from `hlim` + `hvol` **plus** the two
  missing inputs: the fake-time `EpsSq`-Lipschitz bundle `hLips` of the limit curve and the
  quantitative bound `hDeriv` for the spatial derivative of the difference of two right-hand sides
  on the `X`-ball (the latter is the proved-by-a-sibling statement
  `LeafD2.fderivFeps_sub_le`, taken here as a hypothesis so that this file depends on nothing
  unproven);
* the elementary glue facts used by that assembly.

Everything is confined to the open quadrant, where `Feps (slice τ)` is `C^∞` (`XBall.classC` +
`smoothOpen_Feps_of_classC`), so `fderiv` is the honest derivative.
-/

namespace Work.FTS.StrongEps.EpsE4Thr.LeafD2

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Two elementary `fderiv` facts -/

/-- `fderiv` of a smooth profile is continuous on the open quadrant. -/
theorem continuousOn_fderiv_uncurry_of_smoothOpen {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun q : ℝ × ℝ => fderiv ℝ (Function.uncurry f) q)
      Work.FTS.EllipticEst.Q0 :=
  (hf.forall 1).continuousOn_fderiv_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 le_rfl

/-- **The `fderiv` of an uncurried difference is the difference of the `fderiv`s** (on the open
quadrant, where both profiles are honestly differentiable). -/
theorem fderiv_uncurry_sub_of_smoothOpen {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    fderiv ℝ (Function.uncurry (fun z θ => f z θ - g z θ)) (z, θ)
      = fderiv ℝ (Function.uncurry f) (z, θ) - fderiv ℝ (Function.uncurry g) (z, θ) := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hd : ∀ h : ℝ → ℝ → ℝ, Work.FTS.EllipticEst.SmoothOpen h →
      DifferentiableAt ℝ (Function.uncurry h) (z, θ) := fun h hh =>
    (((hh.forall 1).differentiableOn (by norm_num)).differentiableAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem))
  have hfun : Function.uncurry (fun z θ => f z θ - g z θ)
      = Function.uncurry f - Function.uncurry g := by
    funext q
    rcases q with ⟨z', θ'⟩
    rfl
  rw [hfun, fderiv_sub (hd f hf) (hd g hg)]

/-- The elementary angular lower bound: for `0 < b < θ < c < π/2` one has
`2 sin b cos c ≤ sin (2θ)`. -/
theorem two_sin_mul_cos_le_sin_two {b θ c : ℝ} (hb : 0 < b) (hbθ : b < θ) (hθc : θ < c)
    (hc : c < Real.pi / 2) : 2 * Real.sin b * Real.cos c ≤ Real.sin (2 * θ) := by
  have hθ0 : 0 < θ := lt_trans hb hbθ
  have hθπ : θ < Real.pi / 2 := lt_trans hθc hc
  rw [Real.sin_two_mul]
  have hs : Real.sin b < Real.sin θ :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      hbθ
  have hcs : Real.cos c < Real.cos θ :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hθ0.le (by linarith [Real.pi_pos]) hθc
  have hposc : 0 < Real.cos c :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hposθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hkey : Real.sin b * Real.cos c < Real.sin θ * Real.cos θ := by
    calc Real.sin b * Real.cos c < Real.sin θ * Real.cos c :=
          mul_lt_mul_of_pos_right hs hposc
      _ < Real.sin θ * Real.cos θ := mul_lt_mul_of_pos_left hcs hposθ
  linarith

/-! ## The assembly, conditional on the two fake-time inputs -/

/-- **The `hB` conjunct of `RegDataD`, from `hlim` + `hvol` plus the two fake-time inputs.**

`hLips` is the `EpsSq`-Lipschitz property of the limit curve in the fake time.  It is the **only**
missing input: the quantitative bound for the spatial `fderiv` of the difference of two right-hand
sides on the `X`-ball is the proved sibling `LeafD2.fderivFeps_sub_le`, used below.  `hLips` itself
is *not* a consequence of `hlim` + `hvol`: see the module docstring and
`LeafD2/NOTES_limEpsSq_lip_hvol_verdict.md`. -/
theorem hB_slab_of_lipschitz_bundle {α C₀ Ce Cs R ε δ : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {h₀ : Work.FTS.Galerkin.Fn}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hC₀ : 0 < C₀)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α (2 * C₀) Φs E)
    (hδ : 0 < δ) (hR : 0 < R)
    (hlim : ∀ τ ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀)
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ))
    (hLips : ∃ L' : ℝ, 0 < L' ∧ ∀ σ ∈ Set.Icc 0 δ, ∀ τ ∈ Set.Icc 0 δ,
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) σ z θ
        - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ z θ)
      ≤ L' * (σ - τ) ^ 2)
    :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        fderiv ℝ (Function.uncurry
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) p.2.2)))
          (p.1, p.2.1))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 δ) := by
  classical
  -- the limit curve, as a profile-valued map
  set w : ℝ → Work.FTS.Galerkin.Fn := fun τ => Work.FTS.Galerkin.slice
    (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ with hw
  have hwX : ∀ τ ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) (w τ) :=
    fun τ hτ => hlim τ hτ
  -- ## (1) the `τ`-Lipschitz property of the curve in `EpsSq` (the first input)
  obtain ⟨L', hL'pos, hLip⟩ := hLips
  -- ## (2) the quantitative derivative bound on the `X`-ball (the proved sibling)
  obtain ⟨C₂, hC₂pos, hC₂⟩ := fderivFeps_sub_le (C₀ := C₀) (Ce := Ce) (Cs := Cs) (R := R)
    (ε := ε) (ρ := ρ) (Φs := Φs) (E := E) hα hρ hε hε1 hC₀ hEll hstar hml hR
  -- ## (3) per-slice regularity
  have hso : ∀ τ ∈ Set.Icc 0 δ,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EpsEngine.Feps α ρ ε Φs E (w τ)) :=
    fun τ hτ => Work.FTS.EpsEngine.smoothOpen_Feps_of_classC (ρ := ρ) (Φs := Φs) (E := E)
      (ε := ε) (u := w τ) hα hρ hε hEll hstar (hwX τ hτ).classC
  have hcont : ∀ τ ∈ Set.Icc 0 δ,
      ContinuousOn (fun q : ℝ × ℝ =>
        fderiv ℝ (Function.uncurry (Work.FTS.EpsEngine.Feps α ρ ε Φs E (w τ))) q)
        Work.FTS.EllipticEst.Q0 :=
    fun τ hτ => continuousOn_fderiv_uncurry_of_smoothOpen (hso τ hτ)
  -- ## (4) the local `τ`-Lipschitz bound of the `fderiv` family
  have hlip : ∀ q ∈ Work.FTS.EllipticEst.Q0, ∃ K : ℝ, 0 ≤ K ∧
      ∃ U : Set (ℝ × ℝ), IsOpen U ∧ q ∈ U ∧
        ∀ q' ∈ U, ∀ τ ∈ Set.Icc 0 δ, ∀ τ' ∈ Set.Icc 0 δ,
          ‖fderiv ℝ (Function.uncurry (Work.FTS.EpsEngine.Feps α ρ ε Φs E (w τ))) q'
            - fderiv ℝ (Function.uncurry (Work.FTS.EpsEngine.Feps α ρ ε Φs E (w τ'))) q'‖
            ≤ K * |τ - τ'| := by
    intro q hq
    obtain ⟨z₀, θ₀⟩ := q
    obtain ⟨hz₀, hθ₀0, hθ₀1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hq
    set a : ℝ := z₀ / 2 with ha
    set b : ℝ := θ₀ / 2 with hb
    set c : ℝ := (θ₀ + Real.pi / 2) / 2 with hc
    have hb0 : 0 < b := by rw [hb]; linarith
    have hbθ₀ : b < θ₀ := by rw [hb]; linarith
    have hθ₀c : θ₀ < c := by rw [hc]; linarith
    have hc2 : c < Real.pi / 2 := by rw [hc]; linarith [Real.pi_pos]
    have hsinb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb0 (by linarith [Real.pi_pos])
    have hcosc : 0 < Real.cos c :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    set K : ℝ := C₂ * (1 + 1 / (2 * Real.sin b * Real.cos c)) * Real.sqrt L' with hK
    have hden : 0 < 2 * Real.sin b * Real.cos c := mul_pos (mul_pos (by norm_num) hsinb) hcosc
    have hKpos : 0 < K := by
      rw [hK]
      exact mul_pos (mul_pos hC₂pos (by positivity)) (Real.sqrt_pos.mpr hL'pos)
    refine ⟨K, hKpos.le, Set.Ioo a (z₀ + 1) ×ˢ Set.Ioo b c,
      isOpen_Ioo.prod isOpen_Ioo, ?_, ?_⟩
    · -- the base point is in the box
      have haz : a < z₀ := by rw [ha]; linarith
      exact ⟨⟨haz, by linarith⟩, hbθ₀, hθ₀c⟩
    · intro q' hq' τ hτ τ' hτ'
      obtain ⟨z', θ'⟩ := q'
      obtain ⟨hz'l, hz'u⟩ := hq'.1
      obtain ⟨hθ'l, hθ'u⟩ := hq'.2
      have hz'0 : 0 < z' := by rw [ha] at hz'l; linarith
      have hθ'0 : 0 < θ' := by rw [hb] at hθ'l; linarith
      have hθ'1 : θ' < Real.pi / 2 := by rw [hc] at hθ'u; linarith
      -- the difference of the two `fderiv`s is the `fderiv` of the difference
      rw [← fderiv_uncurry_sub_of_smoothOpen (hso τ hτ) (hso τ' hτ') hz'0 ⟨hθ'0, hθ'1⟩]
      have h1 := hC₂ (w τ) (w τ') (hwX τ hτ) (hwX τ' hτ') z' θ' hz'0 ⟨hθ'0, hθ'1⟩
      have h2 : Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => w τ z θ - w τ' z θ))
          ≤ Real.sqrt L' * |τ - τ'| := by
        refine le_trans (Real.sqrt_le_sqrt (hLip τ hτ τ' hτ')) ?_
        rw [Real.sqrt_mul hL'pos.le, Real.sqrt_sq_eq_abs]
      have h3 : 1 + 1 / Real.sin (2 * θ') ≤ 1 + 1 / (2 * Real.sin b * Real.cos c) := by
        have hlow : 2 * Real.sin b * Real.cos c ≤ Real.sin (2 * θ') :=
          two_sin_mul_cos_le_sin_two hb0 hθ'l (by rw [hc] at hθ'u; linarith) hc2
        have := one_div_le_one_div_of_le hden hlow
        linarith
      have hfac : 0 < 1 + 1 / (2 * Real.sin b * Real.cos c) := by positivity
      calc ‖fderiv ℝ (Function.uncurry (fun z θ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (w τ) z θ
              - Work.FTS.EpsEngine.Feps α ρ ε Φs E (w τ') z θ)) (z', θ')‖
          ≤ C₂ * (1 + 1 / Real.sin (2 * θ'))
              * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => w τ z θ - w τ' z θ)) := h1
        _ ≤ C₂ * (1 + 1 / (2 * Real.sin b * Real.cos c))
              * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => w τ z θ - w τ' z θ)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h3 hC₂pos.le) (Real.sqrt_nonneg _)
        _ ≤ C₂ * (1 + 1 / (2 * Real.sin b * Real.cos c))
              * (Real.sqrt L' * |τ - τ'|) :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg hC₂pos.le hfac.le)
        _ = K * |τ - τ'| := by rw [hK]; ring
  -- ## (5) the abstract slab lemma
  have hfinal := continuousOn_slab_of_lipschitz (E := (ℝ × ℝ) →L[ℝ] ℝ) (δ := δ) hδ.le
    (g := fun τ q => fderiv ℝ (Function.uncurry (Work.FTS.EpsEngine.Feps α ρ ε Φs E (w τ))) q)
    (Z := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0 hcont hlip
  -- ## (6) identify the abstract slab with the target slab
  have hset : ({p : ℝ × (ℝ × ℝ) | (p.1, p.2.1) ∈ Work.FTS.EllipticEst.Q0 ∧ p.2.2 ∈ Set.Icc 0 δ})
      = (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 δ) := by
    ext p
    simp only [Set.mem_ofPred_eq, Work.FTS.EllipticEst.mem_Q0, Set.mem_prod, Set.mem_Ioi,
      Set.mem_Ioo, Set.mem_Icc]
    tauto
  rw [← hset]
  exact hfinal.congr (fun p _ => rfl)

/-! ## The requested statement (not derivable from its hypotheses)

Kept verbatim for the record.  It is **not** provable from `hlim` + `hvol` alone: the fake-time
`EpsSq`-Lipschitz bundle `hLips` of `hB_slab_of_lipschitz_bundle` is not a consequence of those two
hypotheses (the in-tree producers of the required joint a.e. strong measurability all take it — or
the Picard iterate data that supply it — as input).  See `NOTES_hB_plan.md` and
`NOTES_limEpsSq_lip_hvol_verdict.md`; the consuming route with the correct hypothesis list is
`EpsE4Thr/RegDataWired.lean`. -/

theorem hB_slab {α C₀ Ce Cs R ε δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {h₀ : Work.FTS.Galerkin.Fn}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hC₀ : 0 < C₀)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α (2 * C₀) Φs E)
    (hδ : 0 < δ) (hR : 0 < R) (hsm0 : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hlim : ∀ τ ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀)
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ))
    (hvol : ∀ z θ τ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → τ ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ z θ τ
        = h₀ z θ + ∫ s in (0 : ℝ)..τ,
            Work.FTS.EpsEngine.Feps α ρ ε Φs E
              (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) s) z θ) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        fderiv ℝ (Function.uncurry
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) p.2.2)))
          (p.1, p.2.1))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 δ) := by
  -- NOT DERIVABLE from `hlim` + `hvol`: the missing hypothesis is the fake-time `EpsSq`-Lipschitz
  -- bundle of the limit curve (equivalently the joint a.e. strong measurability of the right-hand
  -- side along it, which the tree produces only from the Picard iterate data).  The full
  -- argument, the candidate route and its obstruction are in `NOTES_hB_plan.md` and
  -- `NOTES_limEpsSq_lip_hvol_verdict.md`; the proved conditional assembly is
  -- `hB_slab_of_lipschitz_bundle` in this file.
  sorry

end Work.FTS.StrongEps.EpsE4Thr.LeafD2
