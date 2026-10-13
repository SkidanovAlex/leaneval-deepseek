import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.JepsJoint.Jeps_fam_continuous
import Submission.Work.FTS.StrongEps.EpsE4Thr.continuousOn_slice_fam_reorder
import Submission.Work.FTS.StrongEps.PZero
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Spaces.c_bounds
import Submission.Work.FTS.StrongEps.EpsE4Thr.ProjSlotDeriv
import Submission.Work.FTS.StrongEps.mixed_Jeps

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Proofs/FakeTimeSlots.lean` — fake-time (`τ`-)regularity of the `ε`-scheme's
# families, by induction on the slot order

The level-four (and level-six) a-priori machinery consumes the *joint* regularity of the slots
`mixed a b (slice g τ)` and `mixed a b (epsRHSP α ρ ε Φs E g τ)` in `(τ, z, θ)`.  The tree carries
the strong form of that regularity (`ContDiffOn ℝ n … (Icc 0 T ×ˢ Quad)`) as an *interface
hypothesis* (`DiagCurveISolution`, items (I)–(IV)), and the hypotheses of the a-priori chapter
(`EpsRegP` = joint `C¹` on the open quadrant plus per-slice `EpsDatumP`, `IsEpsSolP` = the
pointwise ODE, and `Xn6 ≤ M`) do not yield it directly — see
`NOTES_fourthChapterB_leaf_proof.md` §3–§5.

This file starts the *honest* producer of that regularity, by induction on the slot order `n`:

* **order 0 (`n = 0`, this file).**  `EpsRegP` gives joint continuity of the flow on the open
  slab (`continuousOn_slice_fam_reorder`), and the mollifier preserves it
  (`JepsJoint.Jeps_fam_continuous` — continuity of `g` is the *only* input).  Hence the mollified
  family, and (with the `L₁₂`-zero-mode scalar's continuity, isolated as the interface
  `hL12` below) its projection `Pz`, are jointly continuous.
* **order `n → n + 1` (next).**  From the ODE's integral form
  `slice g τ = slice g σ + ∫_σ^τ epsRHSP … u du` the order-`(n+1)` slots of the flow are the
  τ-primitives of the order-`(n+1)` slots of the right-hand side; exchanging `∂_z`, `∂_θ` with the
  τ-integral is Clairaut plus the parametric-derivative lemma, whose inputs are exactly the joint
  continuity of the order-`(n+1)` right-hand-side slots (the induction hypothesis at the next
  order) and a τ-uniform domination.  The right-hand-side slots themselves are *finite smooth
  combinations* of the flow's slots (through `dynLin`, `dynRHS`, the mollifier and the projection),
  so the step is `flow ≤ n ⟹ RHS ≤ n` for the orders the operators do not raise, and the two
  chains interleave.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **Base case (order 0), mollified family.**

The family `(τ, z, θ) ↦ J_ε (slice g τ) z θ` is jointly continuous on the slab, from the flow's
joint continuity alone (`EpsRegP`) — no smoothness of the kernel beyond `IsMollKernel`, and no
`ℋ⁶`-bound, is used. -/
theorem Jeps_slice_continuousOn_fakeTime {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α ε T : ℝ} (hε : 0 < ε) {g : Fam} (hregP : Work.FTS.StrongEps.EpsRegP α ρ ε T g) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
        Work.FTS.StrongEps.Jeps ρ ε (slice g q.1) q.2.1 q.2.2)
      (Set.Icc 0 T ×ˢ Work.FTS.StrongEps.Quad) := by
  have hcont : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => g q.2.1 q.2.2 q.1)
      (Set.Icc 0 T ×ˢ Work.FTS.StrongEps.Quad) :=
    Work.FTS.StrongEps.EpsE4Thr.continuousOn_slice_fam_reorder hregP.1
  exact Work.FTS.StrongEps.EpsE4Thr.JepsJoint.Jeps_fam_continuous hρ.moll hε
    (g := fun z θ τ => g z θ τ) hcont

/-- **Base case (order 0), projected mollified family.**

`Pz (J_ε (slice g τ)) = J_ε (slice g τ) − (L₁₂(J_ε (slice g τ))(0)/pzNorm) • bump`, so the
projection's joint continuity follows from the mollified family's (previous lemma) and the
*continuity of the scalar* `τ ↦ L₁₂ (J_ε (slice g τ)) 0`, which is isolated here as the interface
`hL12` (its producer is the dominated-convergence statement on the `L₁₂`-density,
`EpsE4Thr.tendsto_L12dens_Jeps_fam` together with a τ-uniform envelope). -/
theorem Pz_Jeps_slice_continuousOn_fakeTime {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α ε T : ℝ} (hε : 0 < ε) {g : Fam} (hregP : Work.FTS.StrongEps.EpsRegP α ρ ε T g)
    (hL12 : ContinuousOn (fun τ : ℝ =>
      Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε (slice g τ)) 0) (Set.Icc 0 T)) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
        Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (slice g q.1)) q.2.1 q.2.2)
      (Set.Icc 0 T ×ˢ Work.FTS.StrongEps.Quad) := by
  have hmoll := Jeps_slice_continuousOn_fakeTime hρ hε hregP
  -- the `τ`-scalar, pulled back to the slab
  have hscal : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε (slice g q.1)) 0
        / Work.FTS.StrongEps.pzNorm) (Set.Icc 0 T ×ˢ Work.FTS.StrongEps.Quad) :=
    (hL12.div_const Work.FTS.StrongEps.pzNorm).comp continuous_fst.continuousOn
      (fun q hq => hq.1)
  -- `bump` is continuous on the whole plane
  have hbump : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.FTS.StrongEps.bump q.2.1 q.2.2) (Set.Icc 0 T ×ˢ Work.FTS.StrongEps.Quad) :=
    (((Work.FTS.StrongEps.contDiff_bump 0).continuous).comp continuous_snd).continuousOn
  have hprod : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε (slice g q.1)) 0
        / Work.FTS.StrongEps.pzNorm) * Work.FTS.StrongEps.bump q.2.1 q.2.2)
      (Set.Icc 0 T ×ˢ Work.FTS.StrongEps.Quad) := hscal.mul hbump
  have hsub := hmoll.sub hprod
  refine hsub.congr (fun q _ => ?_)
  rcases q with ⟨τ, z, θ⟩
  exact (Work.FTS.StrongEps.Pz_apply (Work.FTS.StrongEps.Jeps ρ ε (slice g τ)) z θ)

/-- the slab of the fake-time chain. -/
abbrev slab (T : ℝ) : Set (ℝ × (ℝ × ℝ)) := Set.Icc 0 T ×ˢ Work.FTS.StrongEps.Quad

/-- **Order-0 (`dynLin`)**: the linear part of the scheme's right-hand side is jointly continuous
on the slab, from the order-`≤ 1` slots of the projected mollified family, its radial `L₁₂`-image
and the `L₁₂`-scalar of its transport. -/
theorem dynLin_JfamP_continuousOn_fakeTime {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α ε T : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hε : 0 < ε)
    {g : Fam} (hregP : Work.FTS.StrongEps.EpsRegP α ρ ε T g)
    (hL12 : ContinuousOn (fun τ : ℝ =>
      Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε (slice g τ)) 0) (Set.Icc 0 T))
    (hslot1 : ∀ a b : ℕ, a + b ≤ 1 → ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.mixed a b (slice (Work.FTS.StrongEps.JfamP ρ ε g) q.1) q.2.1 q.2.2)
      (slab T))
    (hL12x : ContinuousOn (fun q : ℝ × ℝ =>
      Work.Coercivity.L12f (slice (Work.FTS.StrongEps.JfamP ρ ε g) q.1) q.2)
      (Set.Icc 0 T ×ˢ Set.Ici 0))
    (hL12T : ContinuousOn (fun τ : ℝ =>
      Work.Coercivity.L12f (Work.Coercivity.Transport
        (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)) 0) (Set.Icc 0 T)) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.FTS.Galerkin.dynLin α (Work.FTS.StrongEps.JfamP ρ ε g) q.1 q.2.1 q.2.2)
      (slab T) := by
  -- ## the pieces
  have hx : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      slice (Work.FTS.StrongEps.JfamP ρ ε g) q.1 q.2.1 q.2.2) (slab T) :=
    Pz_Jeps_slice_continuousOn_fakeTime hρ hε hregP hL12
  have hdz : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.Dz (slice (Work.FTS.StrongEps.JfamP ρ ε g) q.1) q.2.1 q.2.2) (slab T) := by
    have h := hslot1 1 0 (by norm_num)
    simpa [Work.Spaces.mixed] using h
  have hdth : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.Dth (slice (Work.FTS.StrongEps.JfamP ρ ε g) q.1) q.2.1 q.2.2) (slab T) := by
    have h := hslot1 0 1 (by norm_num)
    simpa [Work.Spaces.mixed] using h
  have hz : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => q.2.1) (slab T) :=
    (continuous_snd.fst).continuousOn
  have hzw : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => (1 : ℝ) + q.2.1) (slab T) :=
    continuous_const.continuousOn.add hz
  have h1z : ∀ q ∈ slab T, (1 : ℝ) + q.2.1 ≠ 0 := by
    intro q hq
    have h : (0 : ℝ) < q.2.1 := hq.2.1
    positivity
  have hGam : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => Work.Spaces.Gam α q.2.2) (slab T) := by
    refine ContinuousOn.rpow_const ?_ ?_
    · fun_prop
    · intro q hq
      left
      have hθ : q.2.2 ∈ Set.Ioo 0 (Real.pi / 2) := hq.2.2
      have hs : 0 < Real.sin q.2.2 :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
      have hc : 0 < Real.cos q.2.2 :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos],
          by linarith [hθ.2, Real.pi_pos]⟩
      positivity
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  -- the radial image as a function of the slab variable
  have hl12 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Coercivity.L12f (slice (Work.FTS.StrongEps.JfamP ρ ε g) q.1) q.2.1) (slab T) :=
    hL12x.comp ((continuous_fst.prodMk continuous_snd.fst).continuousOn)
      (fun q hq => ⟨hq.1, le_of_lt (show (0:ℝ) < q.2.1 from hq.2.1)⟩)
  have hl12T : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Coercivity.L12f (Work.Coercivity.Transport
        (slice (Work.FTS.StrongEps.JfamP ρ ε g) q.1)) 0) (slab T) :=
    hL12T.comp continuous_fst.continuousOn (fun q hq => hq.1)
  -- ## the two coefficient functions
  have hcoef1 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      2 * q.2.1 * Work.Spaces.Gam α q.2.2 / (Work.Spaces.c α * (1 + q.2.1) ^ 2))
      (slab T) := by
    refine ((continuous_const.continuousOn.mul hz).mul hGam).div (continuous_const.continuousOn.mul (hzw.pow 2)) ?_
    intro q hq
    exact mul_ne_zero hc (pow_ne_zero 2 (h1z q hq))
  have hcoef2 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.Gam α q.2.2 / Work.Spaces.c α * (2 * q.2.1 ^ 2 / (1 + q.2.1) ^ 3))
      (slab T) := by
    refine (hGam.div_const (Work.Spaces.c α)).mul ?_
    refine (continuous_const.continuousOn.mul (hz.pow 2)).div (hzw.pow 3) ?_
    intro q hq
    exact pow_ne_zero 3 (h1z q hq)
  -- ## the assembly
  have hTransport : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Coercivity.Transport (slice (Work.FTS.StrongEps.JfamP ρ ε g) q.1) q.2.1 q.2.2)
      (slab T) :=
    (continuous_const.continuousOn.mul hdth).div hzw h1z
  have hmain : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      (slice (Work.FTS.StrongEps.JfamP ρ ε g) q.1 q.2.1 q.2.2
          + Work.Spaces.Dz (slice (Work.FTS.StrongEps.JfamP ρ ε g) q.1) q.2.1 q.2.2
          - 2 * slice (Work.FTS.StrongEps.JfamP ρ ε g) q.1 q.2.1 q.2.2 / (1 + q.2.1))
        - (2 * q.2.1 * Work.Spaces.Gam α q.2.2 / (Work.Spaces.c α * (1 + q.2.1) ^ 2))
            * Work.Coercivity.L12f (slice (Work.FTS.StrongEps.JfamP ρ ε g) q.1) q.2.1
        - (Work.Coercivity.Transport (slice (Work.FTS.StrongEps.JfamP ρ ε g) q.1) q.2.1 q.2.2
            - Work.Spaces.Gam α q.2.2 / Work.Spaces.c α * (2 * q.2.1 ^ 2 / (1 + q.2.1) ^ 3)
                * Work.Coercivity.L12f (Work.Coercivity.Transport
                    (slice (Work.FTS.StrongEps.JfamP ρ ε g) q.1)) 0))
      (slab T) := by
    have h1 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
        slice (Work.FTS.StrongEps.JfamP ρ ε g) q.1 q.2.1 q.2.2
          + Work.Spaces.Dz (slice (Work.FTS.StrongEps.JfamP ρ ε g) q.1) q.2.1 q.2.2
          - 2 * slice (Work.FTS.StrongEps.JfamP ρ ε g) q.1 q.2.1 q.2.2 / (1 + q.2.1))
        (slab T) :=
      (hx.add hdz).sub ((hx.const_mul 2).div hzw h1z)
    exact ((h1.sub (hcoef1.mul hl12)).sub
      (hTransport.sub (hcoef2.mul hl12T)))
  refine hmain.neg.congr (fun q hq => ?_)
  have hz0 : (1 : ℝ) + q.2.1 ≠ 0 := h1z q hq
  simp only [Work.FTS.Galerkin.dynLin, Work.Coercivity.LGammaT, Work.Coercivity.LGamma,
    Work.Coercivity.L, Work.Coercivity.Proj, Work.Coercivity.Transport, Pi.neg_apply]


/-- **`hslot1` (the order-`≤ 1` slots of the projected mollified family) from the unprojected
slots and the `Pz`-correction.**  The projection is `Pz w = w − (L₁₂ w 0 / pzNorm) • bump`, and on
the slab `Pz (J_ε (slice g τ)) = (J_ε (slice g τ)) − c(τ) • bump` pointwise
(`ProjSlotDeriv.mixed_Pz_Jeps_eq`), so the slot continuity follows from
* the unprojected slots `mixed a b (J_ε (slice g ·))` (`Jeps_slots_continuousOn_fakeTime`, in
  flight) — where `EpsDatumP`'s `SmoothOpen` supplies the per-slice `C^∞` that `mixed_Jeps` needs,
* the τ-scalar `τ ↦ L₁₂ (J_ε (slice g τ)) 0` (`hL12`),
* the slot functions of `bump`, which is *globally* `C^∞` (`contDiff_bump`). -/
theorem JfamP_slots_continuousOn_fakeTime {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α ε T : ℝ} (hε : 0 < ε) {g : Fam} (hregP : Work.FTS.StrongEps.EpsRegP α ρ ε T g)
    (hL12 : ContinuousOn (fun τ : ℝ =>
      Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε (slice g τ)) 0) (Set.Icc 0 T))
    (hJeps : ∀ a b : ℕ, a + b ≤ 1 → ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.mixed a b (Work.FTS.StrongEps.Jeps ρ ε (slice g q.1)) q.2.1 q.2.2)
      (slab T))
    (hbump : ∀ a b : ℕ, a + b ≤ 1 → Continuous (fun p : ℝ × ℝ =>
      Work.Spaces.mixed a b Work.FTS.StrongEps.bump p.1 p.2)) :
    ∀ a b : ℕ, a + b ≤ 1 → ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.mixed a b (slice (Work.FTS.StrongEps.JfamP ρ ε g) q.1) q.2.1 q.2.2)
      (slab T) := by
  intro a b hab
  -- the scalar factor and the `bump` slot factor
  have hscal : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε (slice g q.1)) 0
        / Work.FTS.StrongEps.pzNorm) (slab T) :=
    (hL12.div_const Work.FTS.StrongEps.pzNorm).comp continuous_fst.continuousOn
      (fun q hq => hq.1)
  have hb : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.mixed a b Work.FTS.StrongEps.bump q.2.1 q.2.2) (slab T) :=
    ((hbump a b hab).comp continuous_snd).continuousOn
  have hmoll := hJeps a b hab
  have hprod := hscal.mul hb
  refine (hmoll.sub hprod).congr (fun q hq => ?_)
  rcases q with ⟨τ, z, θ⟩
  have hzθ : (z, θ) ∈ Work.FTS.StrongEps.Quad := hq.2
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (slice g τ))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.smoothOpen_iff_forall (slice g τ) |>.mp ((hregP.2 τ hq.1).1)
  have hz : 0 < z := hzθ.1
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := hzθ.2
  show Work.Spaces.mixed a b (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (slice g τ))) z θ
      = Work.Spaces.mixed a b (Work.FTS.StrongEps.Jeps ρ ε (slice g τ)) z θ
        - Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε (slice g τ)) 0
          / Work.FTS.StrongEps.pzNorm * Work.Spaces.mixed a b Work.FTS.StrongEps.bump z θ
  rw [Work.FTS.StrongEps.EpsE4Thr.mixed_Pz_Jeps_eq ρ hρ hε hsm hz hθ (by omega)]
  rw [← Work.FTS.StrongEps.mixed_Jeps ρ hρ.moll hε hsm hz hθ a b]


end Work.FTS.StrongEps.E4R3.Apriori4Proofs
