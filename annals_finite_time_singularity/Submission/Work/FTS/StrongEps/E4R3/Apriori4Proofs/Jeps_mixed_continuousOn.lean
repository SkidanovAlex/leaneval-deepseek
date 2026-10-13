/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Apriori4Proofs/Jeps_mixed_continuousOn.lean` — joint continuity of the *mixed* slots of the
# mollified fake-time family on the closed slab

The level-four a-priori machinery consumes the joint (`(τ,z,θ)`-) regularity, on the closed slab
`S = Icc 0 T ×ˢ Quad`, of the framed derivatives `D_z^a D_θ^b (J_ε (slice g τ))`, for **all**
orders `a, b` (`Jeps_slots_continuousOn_fakeTime.lean` only treats `a + b ≤ 1`).  The hypotheses of
the a-priori chapter (`EpsRegP`: joint `C¹` of the family, and `C^∞` of each *slice*) do **not**
give joint smoothness of the family, so the higher slots cannot be differentiated directly.  What
saves the statement is the *log-coordinate* structure of `J_ε`: all the derivatives can be routed
onto the (smooth, compactly supported) kernel, leaving on the profile only the values of `g` — which
are jointly continuous.

## The route

`mixed_Jeps_kernel_partial` (from `Submission/Work/FTS/StrongEps/mixed_Jeps_kernel_partial.lean`)
expresses an arbitrary slot through the partially routed integral `Xi`.  Taking the routing
indices `j' = i' = 0` gives the clean form

  `D_z^a D_θ^b (J_ε f) z θ = 2^b · ∫ p, ∂₁^a ∂₂^b (Jker ρ ε) p · f (zShift z p.1) (thShift θ p.2)`

for `(z,θ) ∈ Quad` and `f` smooth on `Quad` (`mixed_Jeps_kd` below; the factor `2^b` is the
`2^{-1}` of each routed `θ`-derivative).  Inserting `f = slice g τ` and reordering the three
variables, the right-hand side becomes the parametric integral

  `q ↦ ∫ p, Kd (Jker ρ ε) a b p · g (zShift q.2.1 p.1) (thShift q.2.2 p.2) q.1`

whose integrand is the product of the (globally continuous) kernel derivative `Kd (Jker ρ ε) a b`
with a *shift* of the jointly continuous family `g`.

## Why this is continuous on the **closed** slab

Two facts make the parametric argument work, and both use the compact support of the kernel rather
than any regularity of the family in `τ`:

* the shift map `(q,p) ↦ (q.1, (zShift q.2.1 p.1, thShift q.2.2 p.2))` maps the **whole**
  `slab × univ` into the slab — `zShift z p > 0` and `thShift θ p ∈ (0, π/2)` for *every*
  `p ∈ ℝ²` — so `g ∘ shift` is continuous on `slab × univ`, which is exactly the hypothesis of
  Mathlib's `continuousOn_integral_of_compact_support`;
* outside the ball of radius `ε` the kernel derivative `Kd (Jker ρ ε) a b` vanishes: `Jker ρ ε`
  vanishes on the *open* complement of that ball, and one `∂₁`/`∂₂` of a function that vanishes on
  an open set again vanishes there (`Kd_eqOn_zero`), by induction.

Together these give the continuity of the routed integral on the closed slab, and the statement
follows by pointwise rewriting (`mixed_Jeps_kd`).

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.FakeTimeSlots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## The kernel-side iterates vanish off an open set on which the kernel vanishes -/

/-- `∂₂` of a function vanishing on an open set vanishes there. -/
theorem partSnd_eqOn_zero {A : ℝ × ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hA : EqOn A 0 V) : EqOn (Work.FTS.StrongEps.partSnd A) 0 V := by
  intro u hu
  have hslice : (fun t : ℝ => A (u.1, t)) =ᶠ[𝓝 u.2] 0 := by
    have hmem : V ∈ 𝓝 u := hV.mem_nhds hu
    have ht : ∀ᶠ t : ℝ in 𝓝 u.2, (u.1, t) ∈ V :=
      (continuous_const.prodMk continuous_id :
        Continuous fun t : ℝ => (u.1, t)).continuousAt.tendsto.eventually hmem
    filter_upwards [ht] with t ht'
    exact hA ht'
  show deriv (fun t : ℝ => A (u.1, t)) u.2 = 0
  rw [hslice.deriv_eq]
  simp

/-- `∂₁` of a function vanishing on an open set vanishes there. -/
theorem partFst_eqOn_zero {A : ℝ × ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hA : EqOn A 0 V) : EqOn (Work.FTS.StrongEps.partFst A) 0 V := by
  intro u hu
  have hslice : (fun s : ℝ => A (s, u.2)) =ᶠ[𝓝 u.1] 0 := by
    have hmem : V ∈ 𝓝 u := hV.mem_nhds hu
    have ht : ∀ᶠ s : ℝ in 𝓝 u.1, (s, u.2) ∈ V :=
      (continuous_id.prodMk continuous_const :
        Continuous fun s : ℝ => (s, u.2)).continuousAt.tendsto.eventually hmem
    filter_upwards [ht] with s hs
    exact hA hs
  show deriv (fun s : ℝ => A (s, u.2)) u.1 = 0
  rw [hslice.deriv_eq]
  simp

/-- **The mixed iterates of the kernel vanish where the kernel does**: this is what turns the
compact support of `Jker ρ ε` into the compact support of every `∂₁^a ∂₂^b (Jker ρ ε)`, hence
into the cut-off needed by the parametric integral. -/
theorem Kd_eqOn_zero {K : ℝ × ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) (hK : EqOn K 0 V) :
    ∀ a b : ℕ, EqOn (Work.FTS.StrongEps.Kd K a b) 0 V := by
  intro a
  induction a with
  | zero =>
    intro b
    induction b with
    | zero =>
      simpa only [Work.FTS.StrongEps.Kd_zero_eq, Function.iterate_zero_apply] using hK
    | succ b ih =>
      rw [Work.FTS.StrongEps.Kd_zero_succ]
      exact partSnd_eqOn_zero hV ih
  | succ a ih =>
    intro b
    rw [Work.FTS.StrongEps.Kd_succ_eq]
    exact partFst_eqOn_zero hV (ih b)

/-- **The kernel derivative vanishes off the ball of radius `ε`.**  This supplies the vanishing
hypothesis of `continuousOn_integral_of_compact_support` for the routed integral. -/
theorem Kd_Jker_eq_zero_of_not_mem {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {p : ℝ × ℝ} (hp : p ∉ Metric.closedBall (0 : ℝ × ℝ) ε) (a b : ℕ) :
    Work.FTS.StrongEps.Kd (Work.FTS.StrongEps.Jker ρ ε) a b p = 0 := by
  have hlt : ε < ‖p‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hp
  have hV : IsOpen {q : ℝ × ℝ | ε < ‖q‖} := isOpen_lt continuous_const continuous_norm
  have hK : EqOn (Work.FTS.StrongEps.Jker ρ ε) 0 {q : ℝ × ℝ | ε < ‖q‖} := by
    intro q hq
    exact Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact not_le.mpr hq)
  exact Kd_eqOn_zero hV hK a b hlt

/-! ## Continuity of the routed integral on the closed slab -/

/-- **The routed integral is continuous on the closed slab.**  The integrand is
`Kd (Jker ρ ε) a b p · g (zShift z p.1) (thShift θ p.2) τ`, i.e. the (continuous, compactly
supported) kernel derivative times a *shift* of the jointly continuous family; the shift maps the
slab into itself for every `p`, so Mathlib's parametric-integral lemma applies with the compact
support of the kernel derivative as the cut-off. -/
theorem continuousOn_kd_integral {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε T : ℝ} (hε : 0 < ε) {g : Fam}
    (hg : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => g q.2.1 q.2.2 q.1)
      (Set.Icc 0 T ×ˢ Work.FTS.StrongEps.Quad)) (a b : ℕ) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Kd (Work.FTS.StrongEps.Jker ρ ε) a b p *
        g (Work.FTS.StrongEps.zShift q.2.1 p.1) (Work.FTS.StrongEps.thShift q.2.2 p.2) q.1)
      (Set.Icc 0 T ×ˢ Work.FTS.StrongEps.Quad) := by
  refine continuousOn_integral_of_compact_support (isCompact_closedBall (0 : ℝ × ℝ) ε) ?_ ?_
  · have hK : ContinuousOn (fun z : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) =>
        Work.FTS.StrongEps.Kd (Work.FTS.StrongEps.Jker ρ ε) a b z.2)
        ((Set.Icc 0 T ×ˢ Work.FTS.StrongEps.Quad) ×ˢ Set.univ) :=
      (((Work.FTS.StrongEps.Kd_smooth _ (fun n => Work.FTS.StrongEps.Jker_smooth hρ ε) a b
        0).continuous).comp continuous_snd).continuousOn
    have hΨ : ContinuousOn (fun z : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) =>
        (z.1.1, (Work.FTS.StrongEps.zShift z.1.2.1 z.2.1,
          Work.FTS.StrongEps.thShift z.1.2.2 z.2.2)))
        ((Set.Icc 0 T ×ˢ Work.FTS.StrongEps.Quad) ×ˢ Set.univ) := by
      refine ContinuousOn.prodMk (continuous_fst.fst).continuousOn ?_
      refine ContinuousOn.prodMk ?_ ?_
      · exact ((continuous_fst.snd.fst).mul
          (Real.continuous_exp.comp (continuous_neg.comp continuous_snd.fst))).continuousOn
      · have htan : ContinuousOn (fun z : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) => Real.tan z.1.2.2)
            ((Set.Icc 0 T ×ˢ Work.FTS.StrongEps.Quad) ×ˢ Set.univ) :=
          Real.continuousOn_tan.comp (continuous_fst.snd.snd).continuousOn
            (fun z hz => (Real.cos_pos_of_mem_Ioo
              ⟨by linarith [hz.1.2.2.1, Real.pi_pos], hz.1.2.2.2⟩).ne')
        have h1 : ContinuousOn (fun z : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) =>
            Real.tan z.1.2.2 * Real.exp (-z.2.2))
            ((Set.Icc 0 T ×ˢ Work.FTS.StrongEps.Quad) ×ˢ Set.univ) :=
          htan.mul (Real.continuous_exp.comp (continuous_neg.comp continuous_snd.snd)).continuousOn
        simpa only [Work.FTS.StrongEps.thShift, Function.comp_def] using
          Real.continuous_arctan.comp_continuousOn h1
    have hmap : MapsTo (fun z : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) =>
        (z.1.1, (Work.FTS.StrongEps.zShift z.1.2.1 z.2.1,
          Work.FTS.StrongEps.thShift z.1.2.2 z.2.2)))
        ((Set.Icc 0 T ×ˢ Work.FTS.StrongEps.Quad) ×ˢ Set.univ)
        (Set.Icc 0 T ×ˢ Work.FTS.StrongEps.Quad) :=
      fun z hz =>
        ⟨hz.1.1, Work.FTS.StrongEps.JepsHkMem.shift_mem_Quad' hz.1.2⟩
    have hg' : ContinuousOn (fun z : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) =>
        g (Work.FTS.StrongEps.zShift z.1.2.1 z.2.1)
          (Work.FTS.StrongEps.thShift z.1.2.2 z.2.2) z.1.1)
        ((Set.Icc 0 T ×ˢ Work.FTS.StrongEps.Quad) ×ˢ Set.univ) := by
      have h := hg.comp hΨ hmap
      simpa only [Function.comp_def] using h
    exact hK.mul hg'
  · intro q p _ hp
    rw [Kd_Jker_eq_zero_of_not_mem hρ.moll hε hp a b, zero_mul]

/-! ## The routed form of the mixed slots -/

/-- **The mixed slot of `J_ε f`, with every derivative routed onto the kernel.**  Specialising
`mixed_Jeps_kernel_partial` to the routing indices `j' = i' = 0` turns the slot into a single
`p`-integral of the kernel derivative `∂₁^a ∂₂^b (Jker ρ ε)` against the *undifferentiated*
profile along the shift. -/
theorem mixed_Jeps_kd {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {f : Fn}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (a b : ℕ) :
    Work.Spaces.mixed a b (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      = (2 : ℝ) ^ b * ∫ p : ℝ × ℝ,
          Work.FTS.StrongEps.Kd (Work.FTS.StrongEps.Jker ρ ε) a b p *
            f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) := by
  rw [Work.FTS.StrongEps.mixed_Jeps_kernel_partial ρ hρ hε hf hz hθ a b 0 0
    (Nat.zero_le a) (Nat.zero_le b)]
  have hpt : ∀ p : ℝ × ℝ, iteratedDeriv a
      (fun s : ℝ => iteratedDeriv b
        (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, t)) p.2) p.1
      = Work.FTS.StrongEps.Kd (Work.FTS.StrongEps.Jker ρ ε) a b p :=
    fun p => (congrFun (Work.FTS.StrongEps.Kd_eq (Work.FTS.StrongEps.Jker ρ ε) a b) p).symm
  simp only [Nat.sub_zero]
  have hI : (∫ p : ℝ × ℝ, iteratedDeriv a
        (fun s : ℝ => iteratedDeriv b
          (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, t)) p.2) p.1
        * Work.Spaces.mixed 0 0 f (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2))
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Kd (Work.FTS.StrongEps.Jker ρ ε) a b p
          * f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) := by
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [hpt p, Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero]
  simp only [hI]

/-! ## The target -/

theorem Jeps_mixed_continuousOn {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α ε T : ℝ} (hε : 0 < ε) {g : Work.FTS.Galerkin.Fam}
    (hregP : Work.FTS.StrongEps.EpsRegP α ρ ε T g) (a b : ℕ) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.mixed a b (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g q.1))
        q.2.1 q.2.2)
      (Set.Icc 0 T ×ˢ Work.FTS.StrongEps.Quad) := by
  have hcont : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      (2 : ℝ) ^ b * ∫ p : ℝ × ℝ,
        Work.FTS.StrongEps.Kd (Work.FTS.StrongEps.Jker ρ ε) a b p *
          g (Work.FTS.StrongEps.zShift q.2.1 p.1)
            (Work.FTS.StrongEps.thShift q.2.2 p.2) q.1)
      (Set.Icc 0 T ×ˢ Work.FTS.StrongEps.Quad) :=
    (continuousOn_kd_integral hρ hε
      (Work.FTS.StrongEps.EpsE4Thr.continuousOn_slice_fam_reorder hregP.1) a b).const_mul _
  refine hcont.congr (fun q hq => ?_)
  rcases q with ⟨τ, z, θ⟩
  have hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (slice g τ)) Work.FTS.StrongEps.Quad :=
    fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall (slice g τ)).mp
      ((hregP.2 τ hq.1).1) n
  exact mixed_Jeps_kd hρ hε hf hq.2.1 hq.2.2 a b

end Work.FTS.StrongEps.E4R3.Apriori4Proofs
