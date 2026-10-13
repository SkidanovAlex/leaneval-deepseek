/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.BoxReg_of_uniform`

The closed-box regularity of the pointwise limit of a sequence of functions which are `C^∞` on a
neighbourhood of the closed quadrant and whose jets of order `≤ 3` are uniformly bounded on every
box `[a,b] × [0,π/2]` (`0 < a ≤ b`):

`Work.FTS_EllLimOK.BoxReg_of_uniform : Work.FTS_EllLimOK.BoxReg Ψ`.

## The route

1. *Extraction.*  The `2`-jet family of `Ψn n`, clamped in the angle by the `1`-Lipschitz
   retraction `clampθ` onto `[0,π/2]`, is uniformly bounded and uniformly Lipschitz on the open
   set `U = (a/2,2b) × (-1/2,π/2+1/2)`, with constants coming from the box bounds on
   `cbox (a/2) (2b)`; the Arzelà–Ascoli extraction of
   `Work.FTS.StrongEps.LocUnif.exists_subseq_tendstoLocallyUniformlyOn_fin` therefore produces a
   strictly monotone subsequence `φ` and a limit `G` of the six jet components, *locally
   uniformly on `U`* — hence uniformly on the closed box `cbox a b ⊆ U`, **including on the
   angular boundary** `θ = 0, π/2` (this is the point of the clamping: the clamped family is
   controlled on the whole open neighbourhood, while clamping is the identity on the closed
   quadrant).
2. *Staircase.*  On the box, `Ψ` and the six limits `A, B, A₁, A₂, B₁, B₂` of the partials
   satisfy the hypotheses of `hasFDerivWithinAt_of_uniform_slice_partials`: the sequence members
   are smooth, their partials converge uniformly on the box, and the limits are continuous there.
   This gives, *within* the box, that `Ψ` has derivative `ellCop A B`, that `A` has derivative
   `ellCop A₁ A₂` and that `B` has derivative `ellCop B₁ B₂`.
3. *Assembly.*  `y ↦ ellCop (A y) (B y)` is the composition of the pair `(A,B)` with the
   continuous linear map `copBilin`; it is `C¹` within the box by the second staircase instance,
   with derivative `copBilin ∘ (ellCop A₁ A₂ × ellCop B₁ B₂)`, which is continuous on the box.
   Two applications of `contDiffWithinAt_succ_iff_hasFDerivWithinAt'` then give
   `ContDiffWithinAt ℝ 2 (Function.uncurry Ψ) (cbox a b) p`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.BoxReg
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.FTS_EllLimOK.BoxRegAux.Defs
import Submission.Work.FTS.StrongEps.LocUnif.exists_subseq_tendstoLocallyUniformlyOn_fin
import Submission.Work.FTS_EllLimOK.BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials
import Submission.Work.FTS_EllLimOK.BoxRegAux.jet_partials_facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Auxiliary: uniform convergence transferred across an equality on the set -/

theorem tendstoUniformlyOn_congr_of_eqOn {ι α : Type*} [PseudoMetricSpace α]
    {F G : ι → α → ℝ} {f : α → ℝ} {l : Filter ι} {s : Set α}
    (h : TendstoUniformlyOn F f l s) (hFG : ∀ n x, x ∈ s → G n x = F n x) :
    TendstoUniformlyOn G f l s := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with n hn x hx
  rw [hFG n x hx]
  exact hn x hx

/-! ## The main theorem -/

theorem BoxReg_of_uniform {Ψn : ℕ → ℝ → ℝ → ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hstr : ∀ n, Work.Spaces.SmoothStrip (Ψn n))
    (hbdd : ∀ a b : ℝ, 0 < a → a ≤ b → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      |Function.uncurry (Ψn n) p| ≤ C
        ∧ ‖iteratedFDeriv ℝ 1 (Function.uncurry (Ψn n)) p‖ ≤ C
        ∧ ‖iteratedFDeriv ℝ 2 (Function.uncurry (Ψn n)) p‖ ≤ C
        ∧ ‖iteratedFDeriv ℝ 3 (Function.uncurry (Ψn n)) p‖ ≤ C)
    (hconv : ∀ a b : ℝ, 0 < a → a ≤ b → ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      Filter.Tendsto (fun n => Ψn n p.1 p.2) Filter.atTop (nhds (Ψ p.1 p.2))) :
    Work.FTS_EllLimOK.BoxReg Ψ := by
  intro a b ha hab
  -- ## 1. The two box constants and the open set `U`
  have ha2 : (0 : ℝ) < a / 2 := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hab2 : a / 2 ≤ 2 * b := by linarith
  obtain ⟨C₀, hC₀pos, hC₀bnd⟩ := hbdd a b ha hab
  obtain ⟨C₁, hC₁pos, hC₁bnd⟩ := hbdd (a / 2) (2 * b) ha2 hab2
  set U : Set (ℝ × ℝ) := Set.Ioo (a / 2) (2 * b) ×ˢ Set.Ioo (-(1 / 2)) (Real.pi / 2 + 1 / 2)
    with hUdef
  have hUopen : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hboxU : cbox a b ⊆ U := by
    intro p hp
    rw [mem_cbox] at hp
    exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
      ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩⟩
  have hboxcpt : IsCompact (cbox a b) := isCompact_Icc.prod isCompact_Icc
  -- ## 2. The jet facts on the box `(a/2, 2b)`
  have hbndBox : ∀ n : ℕ, ∀ k : ℕ, k ≤ 3 → ∀ p ∈ cbox (a / 2) (2 * b),
      ‖iteratedFDeriv ℝ k (Function.uncurry (Ψn n)) p‖ ≤ C₁ := by
    intro n k hk p hp
    interval_cases k
    · simpa using (hC₁bnd n p hp).1
    · exact (hC₁bnd n p hp).2.1
    · exact (hC₁bnd n p hp).2.2.1
    · exact (hC₁bnd n p hp).2.2.2
  have hjetB : ∀ n : ℕ,
      (∀ p ∈ cbox (a / 2) (2 * b),
        |Work.Spaces.pz (Ψn n) p.1 p.2| ≤ C₁ ∧
        |Work.Spaces.pth (Ψn n) p.1 p.2| ≤ C₁ ∧
        |Work.Spaces.pz (Work.Spaces.pz (Ψn n)) p.1 p.2| ≤ C₁ ∧
        |Work.Spaces.pth (Work.Spaces.pz (Ψn n)) p.1 p.2| ≤ C₁ ∧
        |Work.Spaces.pz (Work.Spaces.pth (Ψn n)) p.1 p.2| ≤ C₁ ∧
        |Work.Spaces.pth (Work.Spaces.pth (Ψn n)) p.1 p.2| ≤ C₁) ∧
      (∀ p ∈ cbox (a / 2) (2 * b), ∀ q ∈ cbox (a / 2) (2 * b),
        |Work.Spaces.pz (Ψn n) p.1 p.2 - Work.Spaces.pz (Ψn n) q.1 q.2| ≤ C₁ * ‖p - q‖ ∧
        |Work.Spaces.pth (Ψn n) p.1 p.2 - Work.Spaces.pth (Ψn n) q.1 q.2| ≤ C₁ * ‖p - q‖ ∧
        |Work.Spaces.pz (Work.Spaces.pz (Ψn n)) p.1 p.2
          - Work.Spaces.pz (Work.Spaces.pz (Ψn n)) q.1 q.2| ≤ C₁ * ‖p - q‖ ∧
        |Work.Spaces.pth (Work.Spaces.pz (Ψn n)) p.1 p.2
          - Work.Spaces.pth (Work.Spaces.pz (Ψn n)) q.1 q.2| ≤ C₁ * ‖p - q‖ ∧
        |Work.Spaces.pz (Work.Spaces.pth (Ψn n)) p.1 p.2
          - Work.Spaces.pz (Work.Spaces.pth (Ψn n)) q.1 q.2| ≤ C₁ * ‖p - q‖ ∧
        |Work.Spaces.pth (Work.Spaces.pth (Ψn n)) p.1 p.2
          - Work.Spaces.pth (Work.Spaces.pth (Ψn n)) q.1 q.2| ≤ C₁ * ‖p - q‖) :=
    fun n => (Work.FTS_EllLimOK.BoxRegAux.jet_partials_facts (f := Ψn n) (a := a / 2) (b := 2 * b) (C := C₁)
      (le_of_lt hC₁pos) ha2 hab2 (Work.Spaces.smoothStrip_uncurry_nat (hstr n) 4)
      (hbndBox n)).2
  -- ## 3. The clamped jet family
  set F : ℕ → ℝ × ℝ → (Fin 6 → ℝ) := fun n p => jetVec (Ψn n) (boxClamp p) with hFdef
  have hclampBox : ∀ p ∈ U, boxClamp p ∈ cbox (a / 2) (2 * b) := by
    intro p hp
    rw [mem_cbox]
    exact ⟨⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩, ⟨clampθ_nonneg _, clampθ_le _⟩⟩
  -- boundedness on `U`
  have hFbdd : ∀ n p, p ∈ U → ‖F n p‖ ≤ C₁ := by
    intro n p hp
    have hmem := hclampBox p hp
    obtain ⟨hb, -⟩ := hjetB n
    rw [pi_norm_le_iff_of_nonneg (le_of_lt hC₁pos)]
    intro m
    rw [Real.norm_eq_abs]
    exact abs_jetVec_le (hb (boxClamp p) hmem) m
  -- Lipschitz on `U`
  have hFlip : ∀ n p q, p ∈ U → q ∈ U → ‖F n p - F n q‖ ≤ C₁ * dist p q := by
    intro n p q hp hq
    have hmem := hclampBox p hp
    have hmem' := hclampBox q hq
    obtain ⟨-, hl⟩ := hjetB n
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg (le_of_lt hC₁pos) dist_nonneg)]
    intro m
    rw [Real.norm_eq_abs]
    have hd : ‖boxClamp p - boxClamp q‖ ≤ dist p q := by
      rw [← dist_eq_norm (boxClamp p) (boxClamp q)]
      exact dist_boxClamp_le p q
    refine le_trans (abs_jetVec_sub_le (C := C₁ * ‖boxClamp p - boxClamp q‖)
      (hl (boxClamp p) hmem (boxClamp q) hmem') m) ?_
    exact mul_le_mul_of_nonneg_left hd (le_of_lt hC₁pos)
  -- ## 4. The Arzelà–Ascoli extraction
  obtain ⟨φ, hφ, G, hGlim⟩ :=
    Work.FTS.StrongEps.LocUnif.exists_subseq_tendstoLocallyUniformlyOn_fin (k := 6) hUopen
      (F := F)
      (fun K _ hKU => ⟨C₁, fun n p hp => hFbdd n p (hKU hp)⟩)
      (fun K _ hKU ε hε => ⟨ε / (2 * (C₁ + 1)), div_pos hε (by positivity),
        fun n p hp q hq hpq => by
          have h1 := hFlip n p q (hKU hp) (hKU hq)
          have h2 : C₁ * dist p q < C₁ * (ε / (2 * (C₁ + 1))) :=
            mul_lt_mul_of_pos_left hpq hC₁pos
          have h3 : C₁ * (ε / (2 * (C₁ + 1))) ≤ ε / 2 := by
            have h4 : C₁ / (2 * (C₁ + 1)) ≤ 1 / 2 := by
              rw [div_le_iff₀ (by positivity)]
              linarith
            calc C₁ * (ε / (2 * (C₁ + 1))) = ε * (C₁ / (2 * (C₁ + 1))) := by ring
              _ ≤ ε * (1 / 2) := mul_le_mul_of_nonneg_left h4 (le_of_lt hε)
              _ = ε / 2 := by ring
          calc ‖F n p - F n q‖ ≤ C₁ * dist p q := h1
            _ < C₁ * (ε / (2 * (C₁ + 1))) := h2
            _ ≤ ε / 2 := h3
            _ < ε := by linarith⟩)
  -- ## 5. The limit functions
  set A : ℝ → ℝ → ℝ := fun z θ => G (z, θ) 0 with hAdef
  set B : ℝ → ℝ → ℝ := fun z θ => G (z, θ) 1 with hBdef
  set A₁ : ℝ → ℝ → ℝ := fun z θ => G (z, θ) 2 with hA₁def
  set A₂ : ℝ → ℝ → ℝ := fun z θ => G (z, θ) 3 with hA₂def
  set B₁ : ℝ → ℝ → ℝ := fun z θ => G (z, θ) 4 with hB₁def
  set B₂ : ℝ → ℝ → ℝ := fun z θ => G (z, θ) 5 with hB₂def
  have hunif : TendstoUniformlyOn (fun n p => F (φ n) p) G Filter.atTop (cbox a b) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hUopen).mp hGlim (cbox a b) hboxU hboxcpt
  have hcompUnif : ∀ m : Fin 6,
      TendstoUniformlyOn (fun n p => F (φ n) p m) (fun p => G p m) Filter.atTop (cbox a b) :=
    fun m => tendstoUniformlyOn_jetVec_component hunif m
  -- the six uniform convergence statements for the unclamped partials
  have hUz : TendstoUniformlyOn (fun n p => Work.Spaces.pz (Ψn (φ n)) p.1 p.2)
      (fun p => A p.1 p.2) Filter.atTop (cbox a b) := by
    refine tendstoUniformlyOn_congr_of_eqOn (hcompUnif 0) ?_
    intro n p hp
    change Work.Spaces.pz (Ψn (φ n)) p.1 p.2 = jetVec (Ψn (φ n)) (boxClamp p) (0 : Fin 6)
    rw [jetVec_zero, boxClamp_eq_of_mem_cbox hp]
  have hUth : TendstoUniformlyOn (fun n p => Work.Spaces.pth (Ψn (φ n)) p.1 p.2)
      (fun p => B p.1 p.2) Filter.atTop (cbox a b) := by
    refine tendstoUniformlyOn_congr_of_eqOn (hcompUnif 1) ?_
    intro n p hp
    change Work.Spaces.pth (Ψn (φ n)) p.1 p.2 = jetVec (Ψn (φ n)) (boxClamp p) (1 : Fin 6)
    rw [jetVec_one, boxClamp_eq_of_mem_cbox hp]
  have hUzz : TendstoUniformlyOn (fun n p => Work.Spaces.pz (Work.Spaces.pz (Ψn (φ n))) p.1 p.2)
      (fun p => A₁ p.1 p.2) Filter.atTop (cbox a b) := by
    refine tendstoUniformlyOn_congr_of_eqOn (hcompUnif 2) ?_
    intro n p hp
    change Work.Spaces.pz (Work.Spaces.pz (Ψn (φ n))) p.1 p.2 = jetVec (Ψn (φ n)) (boxClamp p) (2 : Fin 6)
    rw [jetVec_two, boxClamp_eq_of_mem_cbox hp]
  have hUthz : TendstoUniformlyOn (fun n p => Work.Spaces.pth (Work.Spaces.pz (Ψn (φ n))) p.1 p.2)
      (fun p => A₂ p.1 p.2) Filter.atTop (cbox a b) := by
    refine tendstoUniformlyOn_congr_of_eqOn (hcompUnif 3) ?_
    intro n p hp
    change Work.Spaces.pth (Work.Spaces.pz (Ψn (φ n))) p.1 p.2 = jetVec (Ψn (φ n)) (boxClamp p) (3 : Fin 6)
    rw [jetVec_three, boxClamp_eq_of_mem_cbox hp]
  have hUzth : TendstoUniformlyOn (fun n p => Work.Spaces.pz (Work.Spaces.pth (Ψn (φ n))) p.1 p.2)
      (fun p => B₁ p.1 p.2) Filter.atTop (cbox a b) := by
    refine tendstoUniformlyOn_congr_of_eqOn (hcompUnif 4) ?_
    intro n p hp
    change Work.Spaces.pz (Work.Spaces.pth (Ψn (φ n))) p.1 p.2 = jetVec (Ψn (φ n)) (boxClamp p) (4 : Fin 6)
    rw [jetVec_four, boxClamp_eq_of_mem_cbox hp]
  have hUthth : TendstoUniformlyOn (fun n p => Work.Spaces.pth (Work.Spaces.pth (Ψn (φ n))) p.1 p.2)
      (fun p => B₂ p.1 p.2) Filter.atTop (cbox a b) := by
    refine tendstoUniformlyOn_congr_of_eqOn (hcompUnif 5) ?_
    intro n p hp
    change Work.Spaces.pth (Work.Spaces.pth (Ψn (φ n))) p.1 p.2 = jetVec (Ψn (φ n)) (boxClamp p) (5 : Fin 6)
    rw [jetVec_five, boxClamp_eq_of_mem_cbox hp]
  -- ## 6. Continuity on the box of the six partials of the sequence and of the limits
  have hjetBox : ∀ n : ℕ,
      (ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz (Ψn n) p.1 p.2) (cbox a b) ∧
       ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth (Ψn n) p.1 p.2) (cbox a b) ∧
       ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pz (Ψn n)) p.1 p.2)
         (cbox a b) ∧
       ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pz (Ψn n)) p.1 p.2)
         (cbox a b) ∧
       ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pth (Ψn n)) p.1 p.2)
         (cbox a b) ∧
       ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pth (Ψn n)) p.1 p.2)
         (cbox a b)) := by
    intro n
    have hbndBox₀ : ∀ k : ℕ, k ≤ 3 → ∀ p ∈ cbox a b,
        ‖iteratedFDeriv ℝ k (Function.uncurry (Ψn n)) p‖ ≤ C₀ := by
      intro k hk p hp
      interval_cases k
      · simpa using (hC₀bnd n p hp).1
      · exact (hC₀bnd n p hp).2.1
      · exact (hC₀bnd n p hp).2.2.1
      · exact (hC₀bnd n p hp).2.2.2
    exact (Work.FTS_EllLimOK.BoxRegAux.jet_partials_facts (f := Ψn n) (a := a) (b := b) (C := C₀) (le_of_lt hC₀pos) ha hab
      (Work.Spaces.smoothStrip_uncurry_nat (hstr n) 4) hbndBox₀).1
  have hcontA : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2) (cbox a b) :=
    hUz.continuousOn (Frequently.of_forall fun n => (hjetBox (φ n)).1)
  have hcontB : ContinuousOn (fun p : ℝ × ℝ => B p.1 p.2) (cbox a b) :=
    hUth.continuousOn (Frequently.of_forall fun n => (hjetBox (φ n)).2.1)
  have hcontA₁ : ContinuousOn (fun p : ℝ × ℝ => A₁ p.1 p.2) (cbox a b) :=
    hUzz.continuousOn (Frequently.of_forall fun n => (hjetBox (φ n)).2.2.1)
  have hcontA₂ : ContinuousOn (fun p : ℝ × ℝ => A₂ p.1 p.2) (cbox a b) :=
    hUthz.continuousOn (Frequently.of_forall fun n => (hjetBox (φ n)).2.2.2.1)
  have hcontB₁ : ContinuousOn (fun p : ℝ × ℝ => B₁ p.1 p.2) (cbox a b) :=
    hUzth.continuousOn (Frequently.of_forall fun n => (hjetBox (φ n)).2.2.2.2.1)
  have hcontB₂ : ContinuousOn (fun p : ℝ × ℝ => B₂ p.1 p.2) (cbox a b) :=
    hUthth.continuousOn (Frequently.of_forall fun n => (hjetBox (φ n)).2.2.2.2.2)
  -- ## 7. The pointwise convergence of the sequence on the box
  have hH0 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      Filter.Tendsto (fun n => Ψn (φ n) z θ) Filter.atTop (nhds (Ψ z θ)) := by
    intro z hz θ hθ
    exact (hconv a b ha hab (z, θ) ⟨hz, hθ⟩).comp hφ.tendsto_atTop
  -- ## 8. The slice-derivative hypotheses for the sequence members
  have hslice_z : ∀ (f : ℝ → ℝ → ℝ), Work.Spaces.SmoothStrip f → ∀ z ∈ Set.Icc a b,
      ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      HasDerivWithinAt (fun z' => f z' θ) (Work.Spaces.pz f z θ) (Set.Icc a b) z := by
    intro f hf z hz θ hθ
    have hzmem : z ∈ Set.Ioi (-1 : ℝ) := by
      rw [Set.mem_Ioi]
      linarith [hz.1, ha]
    have hCd : ContDiffOn ℝ 1 (fun z' : ℝ => f z' θ) (Set.Ioi (-1 : ℝ)) :=
      (Work.Spaces.smoothStrip_zSlice hf hθ).of_le (Work.Spaces.natCast_le_smoothOrder 1)
    have hd : DifferentiableAt ℝ (fun z' : ℝ => f z' θ) z :=
      (hCd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hzmem)
    exact hd.hasDerivAt.hasDerivWithinAt
  have hslice_th : ∀ (f : ℝ → ℝ → ℝ), Work.Spaces.SmoothStrip f → ∀ z ∈ Set.Icc a b,
      ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      HasDerivWithinAt (fun θ' => f z θ') (Work.Spaces.pth f z θ) (Set.Icc 0 (Real.pi / 2)) θ := by
    intro f hf z hz θ hθ
    have hzmem : z ∈ Set.Ioi (-1 : ℝ) := by
      rw [Set.mem_Ioi]
      linarith [hz.1, ha]
    have hpt : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hCd : ContDiffOn ℝ 1 (fun θ' : ℝ => f z θ') (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
      Work.Spaces.smoothStrip_thetaSlice_nat hf hzmem 1
    have hd : DifferentiableAt ℝ (fun θ' : ℝ => f z θ') θ :=
      (hCd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hpt)
    exact hd.hasDerivAt.hasDerivWithinAt
  -- ## 9. The three staircase applications
  have hcontSeq : ∀ n : ℕ,
      ContinuousOn (Function.uncurry (Ψn (φ n))) (Set.Icc a b ×ˢ Set.Icc 0 (Real.pi / 2)) := by
    intro n
    refine ((Work.Spaces.smoothStrip_uncurry (hstr (φ n))).mono ?_).continuousOn
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_cbox.mp hp
    rw [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
    exact ⟨by linarith [hp1.1, ha],
      ⟨by linarith [hp2.1], by linarith [hp2.2, Real.pi_pos]⟩⟩
  have hS0 := Work.FTS_EllLimOK.BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials (a := a) (b := b) (c := 0)
    (d := Real.pi / 2) (hab := hab) (hcd := by positivity)
    (H := fun n => Ψn (φ n)) (H₀ := Ψ)
    (P := fun n => Work.Spaces.pz (Ψn (φ n))) (P₀ := fun z θ => A z θ)
    (Q := fun n => Work.Spaces.pth (Ψn (φ n))) (Q₀ := fun z θ => B z θ)
    hcontSeq
    (fun n z hz θ hθ => hslice_z (Ψn (φ n)) (hstr (φ n)) z hz θ hθ)
    (fun n z hz θ hθ => hslice_th (Ψn (φ n)) (hstr (φ n)) z hz θ hθ)
    (fun n => (hjetBox (φ n)).1) (fun n => (hjetBox (φ n)).2.1)
    hH0 hUz hUth hcontA hcontB
  have hS1 := Work.FTS_EllLimOK.BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials (a := a) (b := b) (c := 0)
    (d := Real.pi / 2) (hab := hab) (hcd := by positivity)
    (H := fun n => Work.Spaces.pz (Ψn (φ n))) (H₀ := fun z θ => A z θ)
    (P := fun n => Work.Spaces.pz (Work.Spaces.pz (Ψn (φ n)))) (P₀ := fun z θ => A₁ z θ)
    (Q := fun n => Work.Spaces.pth (Work.Spaces.pz (Ψn (φ n)))) (Q₀ := fun z θ => A₂ z θ)
    (fun n => (hjetBox (φ n)).1)
    (fun n z hz θ hθ => hslice_z (Work.Spaces.pz (Ψn (φ n)))
      (Work.Spaces.smoothStrip_pz (hstr (φ n))) z hz θ hθ)
    (fun n z hz θ hθ => hslice_th (Work.Spaces.pz (Ψn (φ n)))
      (Work.Spaces.smoothStrip_pz (hstr (φ n))) z hz θ hθ)
    (fun n => (hjetBox (φ n)).2.2.1) (fun n => (hjetBox (φ n)).2.2.2.1)
    (fun z hz θ hθ => hUz.tendsto_at (x := (z, θ)) ⟨hz, hθ⟩)
    hUzz hUthz hcontA₁ hcontA₂
  have hS2 := Work.FTS_EllLimOK.BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials (a := a) (b := b) (c := 0)
    (d := Real.pi / 2) (hab := hab) (hcd := by positivity)
    (H := fun n => Work.Spaces.pth (Ψn (φ n))) (H₀ := fun z θ => B z θ)
    (P := fun n => Work.Spaces.pz (Work.Spaces.pth (Ψn (φ n)))) (P₀ := fun z θ => B₁ z θ)
    (Q := fun n => Work.Spaces.pth (Work.Spaces.pth (Ψn (φ n)))) (Q₀ := fun z θ => B₂ z θ)
    (fun n => (hjetBox (φ n)).2.1)
    (fun n z hz θ hθ => hslice_z (Work.Spaces.pth (Ψn (φ n)))
      (Work.Spaces.smoothStrip_pth (hstr (φ n))) z hz θ hθ)
    (fun n z hz θ hθ => hslice_th (Work.Spaces.pth (Ψn (φ n)))
      (Work.Spaces.smoothStrip_pth (hstr (φ n))) z hz θ hθ)
    (fun n => (hjetBox (φ n)).2.2.2.2.1) (fun n => (hjetBox (φ n)).2.2.2.2.2)
    (fun z hz θ hθ => hUth.tendsto_at (x := (z, θ)) ⟨hz, hθ⟩)
    hUzth hUthth hcontB₁ hcontB₂
  -- ## 10. The assembly
  -- `A` is `C¹` within the box (with derivative `ellCop A₁ A₂`)
  have hA_c1 : ∀ q ∈ cbox a b,
      ContDiffWithinAt ℝ 1 (fun y : ℝ × ℝ => A y.1 y.2) (cbox a b) q := by
    intro q hq
    have haux : ContDiffWithinAt ℝ ((0 : ℕ∞ω) + 1) (fun y : ℝ × ℝ => A y.1 y.2)
        (cbox a b) q := by
      refine (contDiffWithinAt_succ_iff_hasFDerivWithinAt' (n := 0) (by simp)).mpr ?_
      refine ⟨insert q (cbox a b), self_mem_nhdsWithin, subset_rfl, fun h => absurd h (by simp),
        (fun y : ℝ × ℝ => ellCop (A₁ y.1 y.2) (A₂ y.1 y.2)), ?_, ?_⟩
      · intro y hy
        have hy' : y ∈ cbox a b := by
          rcases Set.mem_insert_iff.mp hy with h | h
          · rw [h]; exact hq
          · exact h
        obtain ⟨hyz, hyθ⟩ := mem_cbox.mp hy'
        exact hS1 y.1 hyz y.2 hyθ
      · refine (contDiffWithinAt_zero hq).2 ⟨cbox a b, self_mem_nhdsWithin, ?_⟩
        intro y hy
        exact continuousWithinAt_ellCop
          ((hcontA₁.continuousWithinAt hy.1).mono Set.inter_subset_left)
          ((hcontA₂.continuousWithinAt hy.1).mono Set.inter_subset_left)
    simpa using haux
  -- `B` is `C¹` within the box (with derivative `ellCop B₁ B₂`)
  have hB_c1 : ∀ q ∈ cbox a b,
      ContDiffWithinAt ℝ 1 (fun y : ℝ × ℝ => B y.1 y.2) (cbox a b) q := by
    intro q hq
    have haux : ContDiffWithinAt ℝ ((0 : ℕ∞ω) + 1) (fun y : ℝ × ℝ => B y.1 y.2)
        (cbox a b) q := by
      refine (contDiffWithinAt_succ_iff_hasFDerivWithinAt' (n := 0) (by simp)).mpr ?_
      refine ⟨insert q (cbox a b), self_mem_nhdsWithin, subset_rfl, fun h => absurd h (by simp),
        (fun y : ℝ × ℝ => ellCop (B₁ y.1 y.2) (B₂ y.1 y.2)), ?_, ?_⟩
      · intro y hy
        have hy' : y ∈ cbox a b := by
          rcases Set.mem_insert_iff.mp hy with h | h
          · rw [h]; exact hq
          · exact h
        obtain ⟨hyz, hyθ⟩ := mem_cbox.mp hy'
        exact hS2 y.1 hyz y.2 hyθ
      · refine (contDiffWithinAt_zero hq).2 ⟨cbox a b, self_mem_nhdsWithin, ?_⟩
        intro y hy
        exact continuousWithinAt_ellCop
          ((hcontB₁.continuousWithinAt hy.1).mono Set.inter_subset_left)
          ((hcontB₂.continuousWithinAt hy.1).mono Set.inter_subset_left)
    simpa using haux
  -- the derivative family `y ↦ ellCop (A y) (B y)` is `C¹` within the box
  have hf'_c1 : ∀ q ∈ cbox a b,
      ContDiffWithinAt ℝ 1 (fun u : ℝ × ℝ => ellCop (A u.1 u.2) (B u.1 u.2))
        (cbox a b) q := by
    intro q hq
    have hpair : ContDiffWithinAt ℝ 1 (fun y : ℝ × ℝ => (A y.1 y.2, B y.1 y.2))
        (cbox a b) q := (hA_c1 q hq).prodMk (hB_c1 q hq)
    have hg : ContDiffWithinAt ℝ 1 (fun w : ℝ × ℝ => copBilin w) (Set.univ : Set (ℝ × ℝ))
        (A q.1 q.2, B q.1 q.2) :=
      (ContinuousLinearMap.contDiff copBilin).contDiffWithinAt
    have h2 : ContDiffWithinAt ℝ 1
        (fun y : ℝ × ℝ => copBilin (A y.1 y.2, B y.1 y.2)) (cbox a b) q :=
      hg.comp q hpair (fun y _ => Set.mem_univ _)
    refine h2.congr (fun y _ => (copBilin_apply (A y.1 y.2) (B y.1 y.2)).symm)
      (copBilin_apply (A q.1 q.2) (B q.1 q.2)).symm
  -- the second-order conclusion, in the `n + 1` form
  have hmain : ∀ q ∈ cbox a b, ContDiffWithinAt ℝ ((1 : ℕ∞ω) + 1)
      (Function.uncurry Ψ) (cbox a b) q := by
    intro q hq
    refine (contDiffWithinAt_succ_iff_hasFDerivWithinAt' (n := 1) (by simp)).mpr ?_
    refine ⟨insert q (cbox a b), self_mem_nhdsWithin, subset_rfl, fun h => absurd h (by simp),
      (fun u : ℝ × ℝ => ellCop (A u.1 u.2) (B u.1 u.2)), ?_, hf'_c1 q hq⟩
    intro y hy
    have hy' : y ∈ cbox a b := by
      rcases Set.mem_insert_iff.mp hy with h | h
      · rw [h]; exact hq
      · exact h
    obtain ⟨hyz, hyθ⟩ := mem_cbox.mp hy'
    exact hS0 y.1 hyz y.2 hyθ
  intro p hp
  simpa [show ((1 : ℕ∞ω) + 1 : ℕ∞ω) = 2 from by norm_num] using hmain p hp

end Work.FTS_EllLimOK
