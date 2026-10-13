import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.smoothOpen_epsWP
import Submission.Work.FTS.StrongEps.JepsSmoothOpen
import Submission.Work.FTS.StrongEps.EpsStructP
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.Jeps_mixed_continuousOn
import Submission.Work.FTS.StrongEps.PZeroAux.PzJepsHkMem
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Apriori4Proofs/WeakRHS.lean` — the *weak-input* regularity of the scheme's right-hand side

The interface item **(V)** of the level-four chapter (`NOTES_fourthChapterB_leaf_proof3.md` §3)
asks for the per-slice regularity of `epsRHSP α ρ ε Φs E g s`.  The point of this module is that

* **(V) is free** from `EpsRegP` + the packages (`smoothOpen_epsRHSP_fam`), and
* the **joint** (`(τ,z,θ)`)-continuity of `epsRHSP` — which the `C^∞`-on-the-closed-slab interface
  item (I) was supplying — is *also* free: `epsRHSP α ρ ε Φs E g τ = ∂_τ g(·,·,τ)` by
  `IsEpsSolP`, and `∂_τ g` is continuous on the (interior) slab because `EpsRegP` makes the family
  jointly `C¹` (`continuousOn_epsRHSP_joint_Ioo`).

Once the joint continuity of `epsRHSP` is available, the mixed slots of its mollified projection
are jointly continuous *by the compact-`p`-window argument of* `Jeps_mixed_continuousOn` — with the
raw family replaced by the (jointly continuous) right-hand side
(`Jeps_mixed_continuousOn_fam`, the family-level form of that lemma).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The per-slice smoothness of the scheme's right-hand side** — interface item (V), discharged.

`epsRHSP = Pz ∘ J_ε ∘ epsWP`, the pre-mollified right-hand side is `C^∞` on the open quadrant at
every class-`C` profile (`StrongEps.smoothOpen_epsWP`), `J_ε` preserves that
(`StrongEps.smoothOpen_Jeps`) and `Pz` is a rank-one correction by the fixed smooth profile `bump`
(`EpsSqTools.LinAux.smoothOpen_Pz`).  The only datum used from the flow is the class-`C`
membership of the *projected mollified* slice, i.e. the class-`C` conjunct of `EpsDatumP`. -/
theorem smoothOpen_epsRHSP_fam {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α ε T Cs Ce : ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam}
    (hα : α ∈ Set.Ioc 0 1) (hε : 0 < ε)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hregP : Work.FTS.StrongEps.EpsRegP α ρ ε T g) :
    ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) := by
  intro s hs
  have hC : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.ClassC.ClassC α
      (slice (Work.FTS.StrongEps.JfamP ρ ε g) s) :=
    fun s hs => (hregP.2 s hs).2.2
  have hW : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) :=
    Work.FTS.StrongEps.smoothOpen_epsWP (C₀ := 0) hα hEll hstar hC s hs
  have hW' : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s))
      Work.FTS.StrongEps.Quad :=
    fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hW n
  exact Work.FTS.StrongEps.EpsSqTools.LinAux.smoothOpen_Pz
    (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hW')

/-! ## Joint continuity of `epsRHSP` from the `C¹`-regularity of the flow

The scheme's right-hand side *is* the fake-time derivative of the flow (`IsEpsSolP.eq`), and
`EpsRegP` makes the uncurried family jointly `C¹` on the slab.  Hence `epsRHSP` agrees, on the
interior slab, with the (continuous) third partial derivative of the family — no smoothness of
`epsRHSP` as a *functional* of the profile, and in particular no continuity of `E` in the profile, is
used.  This is the substitute for interface item (I) of `NOTES_fourthChapterB_leaf_proof3.md` §3. -/

/-- **Joint continuity of `epsRHSP` on the interior slab** (with the `(τ,(z,θ))`-order of the
consumers). -/
theorem continuousOn_epsRHSP_joint_Ioo {ρ : ℝ × ℝ → ℝ}
    {α ε T : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam}
    (hregP : Work.FTS.StrongEps.EpsRegP α ρ ε T g)
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g q.1 q.2.1 q.2.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) := by
  -- the uncurried family, in `(z, θ, τ)`-order
  set Φ : ℝ × (ℝ × ℝ) → ℝ := fun p => g p.1 p.2.1 p.2.2 with hΦ
  -- the interior slab, in `(z, θ, τ)`-order (open, so `fderiv` and `fderivWithin` agree)
  set u : Set (ℝ × (ℝ × ℝ)) :=
    Set.Ioi 0 ×ˢ (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo 0 T) with hu
  have huopen : IsOpen u := isOpen_Ioi.prod (isOpen_Ioo.prod isOpen_Ioo)
  have hu_sub : u ⊆ Set.Ioi 0 ×ˢ (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 T) := by
    intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.1.le, hp.2.2.2.le⟩
  have hCd : ContDiffOn ℝ 1 Φ u := hregP.1.mono hu_sub
  have hcont : ContinuousOn (fderiv ℝ Φ) u :=
    hCd.continuousOn_fderiv_of_isOpen huopen le_rfl
  -- the value of `fderiv` in the `τ`-direction is the fake-time derivative
  have hkey : ∀ q ∈ Set.Ioo (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad,
      Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g q.1 q.2.1 q.2.2
        = fderiv ℝ Φ (q.2.1, (q.2.2, q.1)) (0, (0, 1)) := by
    intro q hq
    obtain ⟨hqτ1, hqτ2⟩ := hq.1
    obtain ⟨hz, hθ⟩ := hq.2
    have hmem : (q.2.1, (q.2.2, q.1)) ∈ u :=
      ⟨hz, ⟨hθ.1, hθ.2⟩, hqτ1, hqτ2⟩
    have hfder : HasFDerivAt Φ (fderiv ℝ Φ (q.2.1, (q.2.2, q.1)))
        (q.2.1, (q.2.2, q.1)) :=
      (((hCd.contDiffWithinAt hmem).contDiffAt (huopen.mem_nhds hmem)).differentiableAt
        one_ne_zero).hasFDerivAt
    have hcurve : HasDerivAt (fun s : ℝ => (q.2.1, (q.2.2, s))) (0, (0, 1)) q.1 :=
      (hasDerivAt_const (c := q.2.1) (x := q.1)).prodMk
        ((hasDerivAt_const (c := q.2.2) (x := q.1)).prodMk (hasDerivAt_id q.1))
    have hcomp : HasDerivAt (fun s : ℝ => Φ (q.2.1, (q.2.2, s)))
        ((fderiv ℝ Φ (q.2.1, (q.2.2, q.1))) (0, (0, 1))) q.1 :=
      hfder.comp_hasDerivAt (f := fun s : ℝ => (q.2.1, (q.2.2, s))) q.1 hcurve
    have hsol' : HasDerivAt (fun s : ℝ => Φ (q.2.1, (q.2.2, s)))
        (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g q.1 q.2.1 q.2.2) q.1 := by
      have hh : (fun s : ℝ => Φ (q.2.1, (q.2.2, s)))
          = fun s : ℝ => g q.2.1 q.2.2 s := rfl
      rw [hh]
      exact (hsol.2 q.2.1 q.2.2 q.1 hz hθ ⟨hqτ1.le, hqτ2.le⟩).hasDerivAt
        (Icc_mem_nhds hqτ1 hqτ2)
    exact (hcomp.unique hsol').symm
  -- assemble: the composite of `fderiv Φ` with the (continuous) relabelling and evaluation
  have hreorder : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => (q.2.1, (q.2.2, q.1)))
      (Set.Ioo (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) :=
    ((continuous_snd.fst).prodMk ((continuous_snd.snd).prodMk continuous_fst)).continuousOn
  have hmaps : Set.MapsTo (fun q : ℝ × (ℝ × ℝ) => (q.2.1, (q.2.2, q.1)))
      (Set.Ioo (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) u := by
    intro q hq
    obtain ⟨hqτ1, hqτ2⟩ := hq.1
    obtain ⟨hz, hθ⟩ := hq.2
    exact ⟨hz, ⟨hθ.1, hθ.2⟩, hqτ1, hqτ2⟩
  have hcomp2 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      fderiv ℝ Φ (q.2.1, (q.2.2, q.1)) (0, (0, 1)))
      (Set.Ioo (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) := by
    have h1 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
        fderiv ℝ Φ (q.2.1, (q.2.2, q.1)))
        (Set.Ioo (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) :=
      hcont.comp hreorder hmaps
    exact ((ContinuousLinearMap.apply ℝ ℝ (0, (0, 1))).continuous.comp_continuousOn h1)
  refine hcomp2.congr (fun q hq => ?_)
  exact hkey q hq

/-! ## The closed-slab form

The interior form above is enough for the *a.e.* statements (the τ-endpoints are null), but the
closed-slab form is what the interface items consume, and it is available as well: the third partial
derivative of a jointly `C¹` function is continuous **on the closed slab**, because the slab is a
product of two open sets with `Icc 0 T` (a set with `UniqueDiffOn`, for `0 < T`), so
`fderivWithin ℝ Φ s` is continuous on `s` (`ContDiffOn.continuousOn_fderivWithin`) and equals the
within-derivative in the `τ`-direction there. -/

/-- **Joint continuity of `epsRHSP` on the closed slab.** -/
theorem continuousOn_epsRHSP_joint {ρ : ℝ × ℝ → ℝ}
    {α ε T : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam} (hT : 0 < T)
    (hregP : Work.FTS.StrongEps.EpsRegP α ρ ε T g)
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g q.1 q.2.1 q.2.2)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) := by
  set Φ : ℝ × (ℝ × ℝ) → ℝ := fun p => g p.1 p.2.1 p.2.2 with hΦ
  set s : Set (ℝ × (ℝ × ℝ)) :=
    Set.Ioi 0 ×ˢ (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 T) with hs
  have hCd : ContDiffOn ℝ 1 Φ s := hregP.1
  have hUdif : UniqueDiffOn ℝ s :=
    UniqueDiffOn.prod (IsOpen.uniqueDiffOn isOpen_Ioi)
      (UniqueDiffOn.prod (IsOpen.uniqueDiffOn isOpen_Ioo) (uniqueDiffOn_Icc hT))
  have hcont : ContinuousOn (fderivWithin ℝ Φ s) s :=
    hCd.continuousOn_fderivWithin hUdif le_rfl
  -- the value of the within-derivative in the `τ`-direction
  have hkey : ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad,
      Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g q.1 q.2.1 q.2.2
        = fderivWithin ℝ Φ s (q.2.1, (q.2.2, q.1)) (0, (0, 1)) := by
    intro q hq
    obtain ⟨hz, hθ⟩ := hq.2
    have hmem : (q.2.1, (q.2.2, q.1)) ∈ s := ⟨hz, ⟨hθ.1, hθ.2⟩, hq.1⟩
    have hfder : HasFDerivWithinAt Φ
        (fderivWithin ℝ Φ s (q.2.1, (q.2.2, q.1))) s (q.2.1, (q.2.2, q.1)) :=
      (((hCd.contDiffWithinAt hmem).differentiableWithinAt one_ne_zero)).hasFDerivWithinAt
    have hcurve : HasDerivWithinAt (fun t : ℝ => (q.2.1, (q.2.2, t))) (0, (0, 1))
        (Set.Icc (0 : ℝ) T) q.1 :=
      (hasDerivWithinAt_const (x := q.1) _ q.2.1).prodMk
        ((hasDerivWithinAt_const (x := q.1) _ q.2.2).prodMk (hasDerivWithinAt_id q.1 _))
    have hmap : Set.MapsTo (fun t : ℝ => (q.2.1, (q.2.2, t))) (Set.Icc (0 : ℝ) T) s :=
      fun t ht => ⟨hz, ⟨hθ.1, hθ.2⟩, ht⟩
    have hcomp := hfder.comp_hasDerivWithinAt (q.1)
      (f := fun t : ℝ => (q.2.1, (q.2.2, t))) hcurve hmap
    have hsol' : HasDerivWithinAt (fun t : ℝ => Φ (q.2.1, (q.2.2, t)))
        (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g q.1 q.2.1 q.2.2) (Set.Icc (0 : ℝ) T) q.1 := by
      have hh : (fun t : ℝ => Φ (q.2.1, (q.2.2, t))) = fun t : ℝ => g q.2.1 q.2.2 t := rfl
      rw [hh]
      exact hsol.2 q.2.1 q.2.2 q.1 hz hθ hq.1
    have hUd : UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) T) q.1 :=
      uniqueDiffOn_Icc hT q.1 hq.1
    exact UniqueDiffWithinAt.eq_deriv _ hUd hsol' hcomp
  have hreorder : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => (q.2.1, (q.2.2, q.1)))
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) :=
    ((continuous_snd.fst).prodMk ((continuous_snd.snd).prodMk continuous_fst)).continuousOn
  have hmaps : Set.MapsTo (fun q : ℝ × (ℝ × ℝ) => (q.2.1, (q.2.2, q.1)))
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) s := by
    intro q hq
    obtain ⟨hz, hθ⟩ := hq.2
    exact ⟨hz, ⟨hθ.1, hθ.2⟩, hq.1⟩
  have hcomp2 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      fderivWithin ℝ Φ s (q.2.1, (q.2.2, q.1)) (0, (0, 1)))
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) := by
    have h1 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
        fderivWithin ℝ Φ s (q.2.1, (q.2.2, q.1)))
        (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) :=
      hcont.comp hreorder hmaps
    exact ((ContinuousLinearMap.apply ℝ ℝ (0, (0, 1))).continuous.comp_continuousOn h1)
  refine hcomp2.congr (fun q hq => ?_)
  exact hkey q hq

end Work.FTS.StrongEps.E4R3.Apriori4Proofs
