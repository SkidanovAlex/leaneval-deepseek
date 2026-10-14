import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongGlobal

open Work.FTS.Nonlin
open Work.FTS.Apriori
open Work.FTS.Galerkin (Fn Fam slice galFun galFam galField galRHS coeffOf IsSolOn IsGalFam
  ConvLocUnif ConvPoint Slab muDyn lamDyn dynLin dynRHS prof gdot IsDynEqOn IsDynGSolWith
  IsDynGSolWithStrong IsDynGSol IsDynGSolOn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The size `|g|_{ℋ⁶}` and the slabs of the fake-time quadrant -/

/-- The size `|g|_{ℋ⁶} = Xn₆(g)`, the `ℋ⁶`-analogue of `Work.FTS.Nonlin.Xn = HkNorm α 4`. -/
abbrev Xn6 (α : ℝ) (g : Fn) : ℝ := Work.Spaces.HkNorm α 6 g

/-- The cube `(z,θ,τ)` on which the families of this chapter are read, right-associated so that
`p.1 = z`, `p.2.1 = θ`, `p.2.2 = τ`. -/
abbrev P3 : Type := ℝ × ℝ × ℝ

/-- The uncurried family `(z,θ,τ) ↦ g z θ τ`. -/
def uncurry3 (g : Fam) : P3 → ℝ := fun p => g p.1 p.2.1 p.2.2

@[simp] theorem uncurry3_apply (g : Fam) (z θ τ : ℝ) : uncurry3 g (z, θ, τ) = g z θ τ := rfl


/-- The *slab* `(0,∞) × (0,π/2) × (a,b)` of fake time: the domain of the joint `C¹`-clause of a
local strong solution on `[a,b]`. -/
def slab (a b : ℝ) : Set P3 := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) ×ˢ Set.Ioo a b




theorem mem_slab {z θ τ a b : ℝ} :
    (z, θ, τ) ∈ slab a b ↔ 0 < z ∧ 0 < θ ∧ θ < π / 2 ∧ a < τ ∧ τ < b := by
  simp [slab, and_assoc]


/-! ## The concatenation of two families, and the slice-congruence of the equation

The continuation of S5 builds the global family by *concatenating* local pieces at the junction
times: `concat G H τ₀` is `G` for `τ ≤ τ₀` and `H` for `τ > τ₀`.  Everything the glue needs is
that the two right-hand sides of the equation (`dynLin`, `dynRHS`) and the canonical stream
function `PsiCan` depend on a family only through its slice. -/

/-- **The concatenation of two families at the fake time `τ₀`**: `G` before `τ₀`, `H` after. -/
def concat (G H : Fam) (τ₀ : ℝ) : Fam := fun z θ τ => if τ ≤ τ₀ then G z θ τ else H z θ τ

@[simp] theorem concat_apply_of_le {G H : Fam} {τ₀ τ z θ : ℝ} (hτ : τ ≤ τ₀) :
    concat G H τ₀ z θ τ = G z θ τ := if_pos hτ

@[simp] theorem concat_apply_of_gt {G H : Fam} {τ₀ τ z θ : ℝ} (hτ : τ₀ < τ) :
    concat G H τ₀ z θ τ = H z θ τ := if_neg (not_le.mpr hτ)

theorem slice_concat_of_le {G H : Fam} {τ₀ τ : ℝ} (hτ : τ ≤ τ₀) :
    slice (concat G H τ₀) τ = slice G τ := by
  funext z θ; exact concat_apply_of_le hτ

theorem slice_concat_of_gt {G H : Fam} {τ₀ τ : ℝ} (hτ : τ₀ < τ) :
    slice (concat G H τ₀) τ = slice H τ := by
  funext z θ; exact concat_apply_of_gt hτ






/-- `dynLin` depends on a family only through its slice. -/
theorem dynLin_congr {α : ℝ} {g g' : Fam} {τ : ℝ} (h : slice g τ = slice g' τ) :
    dynLin α g τ = dynLin α g' τ := by
  funext z θ
  simp only [dynLin, h]

/-- `PsiCan` depends on a family only through its slice. -/
theorem slice_PsiCan_congr {Φs : Fn} {EllSol : Fn → Fn} {g g' : Fam} {τ : ℝ}
    (h : slice g τ = slice g' τ) :
    slice (PsiCan Φs EllSol g) τ = slice (PsiCan Φs EllSol g') τ := by
  funext z θ
  simp only [PsiCan, slice]
  rw [h]

/-- `Ftau` depends on a family only through its slice. -/
theorem Ftau_congr {α : ℝ} {g g' : Fam} {τ : ℝ} (h : slice g τ = slice g' τ) :
    Work.Construction.Ftau α g τ = Work.Construction.Ftau α g' τ := by
  funext z θ
  have hzθ : g z θ τ = g' z θ τ := congrFun (congrFun h z) θ
  simp only [Work.Construction.Ftau, hzθ]

/-- `muDyn` depends on a family only through its slice. -/
theorem muDyn_congr {α : ℝ} {Φs : Fn} {EllSol : Fn → Fn} {g g' : Fam} {τ : ℝ}
    (h : slice g τ = slice g' τ) :
    muDyn α (PsiCan Φs EllSol g) g τ = muDyn α (PsiCan Φs EllSol g') g' τ := by
  simp only [muDyn, Ftau_congr h, slice_PsiCan_congr h, h]

/-! ## The elliptic law `IsBslSolPos` (the design's `Law`) -/

/-- **The elliptic law on the open quadrant, with the boundary conditions only for `z ≥ 0`.**

This is `Work.Elliptic.IsBslSol` with its two Dirichlet clauses restricted to `z ≥ 0` (the design's
`Law := IsBslSolPos`, `FTS_ELL_GALERKIN.md` §4): the stream function is only ever *used* on
`z ≥ 0`, and the delivered `IsBslSol` asks for the values at `z < 0` as well, which no solution
produced by this route satisfies (the profiles are extended by `0` there). -/
def IsBslSolPos (α : ℝ) (F Ψ : Fn) : Prop :=
  (∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) ∧
    (∀ z, 0 ≤ z → Ψ z 0 = 0) ∧ (∀ z, 0 ≤ z → Ψ z (π / 2) = 0) ∧
      (∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => Ψ z θ) atTop (𝓝 0))

/-- The delivered `Work.Elliptic.IsBslSol` is the `IsBslSolPos` with the boundary conditions for
all `z`. -/
theorem IsBslSol.toPos {α : ℝ} {F Ψ : Fn} (h : Work.Elliptic.IsBslSol α F Ψ) :
    IsBslSolPos α F Ψ :=
  ⟨h.1, fun z _ => h.2.1 z, fun z _ => h.2.2.1 z, h.2.2.2⟩

/-- `IsBslSolPos` depends only on the two functions: it is transported along *equalities* of the
source and of the stream function.  (This is the form in which the continuation uses it: the
concatenated family agrees with a piece on a whole interval, hence its slices are equal as
functions.) -/
theorem IsBslSolPos.congr {α : ℝ} {F F' Ψ Ψ' : Fn} (h : IsBslSolPos α F Ψ) (hF : F = F')
    (hΨ : Ψ = Ψ') : IsBslSolPos α F' Ψ' := by
  subst hF; subst hΨ; exact h

/-! ## The interval forms of the equation -/

/-- **The dynamic modulated equation on a closed interval `[a,b]` of fake time**: for every
`τ ∈ [a,b]` and every point of the open quadrant the family `g` has the within-`[a,b]`-derivative
given by `dynLin + dynRHS`, the stream function being the canonical `PsiCan Φs EllSol g`. -/
def IsDynEqOnIcc (α : ℝ) (a b : ℝ) (Φs : Fn) (EllSol : Fn → Fn) (g : Fam) : Prop :=
  ∀ z θ τ, τ ∈ Set.Icc a b → (z, θ) ∈ Work.Construction.Qd →
    HasDerivWithinAt (fun s => g z θ s)
      (dynLin α g τ z θ + dynRHS α (PsiCan Φs EllSol g) g τ z θ) (Set.Icc a b) τ


/-- The half-line form (`τ ≥ 0`): the canonical stream function solves the elliptic problem at
every `τ ≥ 0` and the equation holds in the within-`Ici 0` sense.  This is exactly
`Work.FTS.Galerkin.IsDynGSolWith (IsBslSolPos α) α (PsiCan Φs EllSol g) g`. -/
def IsDynGSolHalf (α : ℝ) (Φs : Fn) (EllSol : Fn → Fn) (g : Fam) : Prop :=
  IsDynGSolWith (IsBslSolPos α) α (PsiCan Φs EllSol g) g


theorem IsDynGSolHalf.law {α : ℝ} {Φs : Fn} {EllSol : Fn → Fn} {g : Fam}
    (h : IsDynGSolHalf α Φs EllSol g) :
    ∀ τ, 0 ≤ τ → IsBslSolPos α (Work.Construction.Ftau α g τ)
      (slice (PsiCan Φs EllSol g) τ) := h.1

theorem IsDynGSolHalf.eq {α : ℝ} {Φs : Fn} {EllSol : Fn → Fn} {g : Fam}
    (h : IsDynGSolHalf α Φs EllSol g) : IsDynEqOn α (PsiCan Φs EllSol g) g := h.2

/-! ## The class of strong solutions -/

/-- **A strong solution of the dynamic modulated equation on the interval `[a,b]` of fake time.**
This is the class in which S2, S4 and S6 are stated; it carries

* the equation on `[a,b]` (`eq`) and the elliptic law at every `τ ∈ [a,b]` (`law`);
* the frozen Galerkin regularity class `Work.FTS.Nonlin.GalClass` of the slice at every time
  (`gal`) — from which `RegQ α 4`, `CoerAdm`, the vanishing at the angular boundaries and the
  zero-mode condition `L₁₂(g)(0) = 0` all follow, `strongSolOn_coerAdm` and
  `StrongSolOn.reg4` below;
* the joint `C¹`-regularity on the open slab `(0,∞)×(0,π/2)×(a-1,b+1)` (`c1`), i.e. the `c1`
  clause of `RegPkgMin` on the *slackened* slab: one unit of fake time of slack on either side of
  the interval.  The slack is what makes the continuation S5 glue: at the junction `b` of two
  consecutive pieces the fake time `b` is *interior* to both pieces' `c1`-slabs, so both pieces are
  (two-sided) `C¹` there and the junction lemma `Work.FTS.StrongGlobal.contDiffAt_concat_1`
  applies.  The local existence theorem of S1 provides this: its construction produces a solution
  on a slightly longer interval than `[a,b]` and claims the *equation* only on `[a,b]`.  Nothing in
  the a-priori bound S4, the persistence S2 or the `H³`-bound S6 uses the slack;
* the `RegQ 4`-membership of the two right-hand sides `dynLin` and `dynRHS` (`regLin`, `regRHS`),
  which is what makes the inner product `IP` additive along the equation (the structural input of
  the energy algebra of S4). -/
structure StrongSolOn (α : ℝ) (Φs : Fn) (EllSol : Fn → Fn) (a b : ℝ) (g : Fam) : Prop where
  hle : a ≤ b
  eq : IsDynEqOnIcc α a b Φs EllSol g
  law : ∀ τ ∈ Set.Icc a b, IsBslSolPos α (Work.Construction.Ftau α g τ)
    (slice (PsiCan Φs EllSol g) τ)
  gal : ∀ τ ∈ Set.Icc a b, GalClass α (slice g τ)
  c1 : ContDiffOn ℝ 1 (uncurry3 g) (slab (a - 1) (b + 1))
  regLin : ∀ τ ∈ Set.Icc a b, RegQ α 4 (dynLin α g τ)
  regRHS : ∀ τ ∈ Set.Icc a b, RegQ α 4 (dynRHS α (PsiCan Φs EllSol g) g τ)


/-- `StrongSolOn` gives `RegQ α 6` of every slice (via `GalClass`). -/
theorem StrongSolOn.reg6 {α : ℝ} {Φs : Fn} {EllSol : Fn → Fn} {a b : ℝ} {g : Fam}
    (h : StrongSolOn α Φs EllSol a b g) :
    ∀ τ ∈ Set.Icc a b, RegQ α 6 (slice g τ) :=
  fun τ hτ => (h.gal τ hτ).reg

/-- `StrongSolOn` gives `RegQ α 4` of every slice (`RegQ` descends in the order). -/
theorem StrongSolOn.reg4 {α : ℝ} {Φs : Fn} {EllSol : Fn → Fn} {a b : ℝ} {g : Fam}
    (h : StrongSolOn α Φs EllSol a b g) :
    ∀ τ ∈ Set.Icc a b, RegQ α 4 (slice g τ) :=
  fun τ hτ => Work.FTS.Apriori.regQ_mono (α := α) (k := 6) (l := 4) (by norm_num) (h.reg6 τ hτ)

/-- `StrongSolOn` gives `HkMem α 4` of every slice. -/
theorem StrongSolOn.hmem4 {α : ℝ} {Φs : Fn} {EllSol : Fn → Fn} {a b : ℝ} {g : Fam}
    (h : StrongSolOn α Φs EllSol a b g) :
    ∀ τ ∈ Set.Icc a b, Work.Spaces.HkMem α 4 (slice g τ) :=
  fun τ hτ => (h.reg4 τ hτ).2.1

/-- `StrongSolOn` gives `HkMem α 6` of every slice. -/
theorem StrongSolOn.hmem6 {α : ℝ} {Φs : Fn} {EllSol : Fn → Fn} {a b : ℝ} {g : Fam}
    (h : StrongSolOn α Φs EllSol a b g) :
    ∀ τ ∈ Set.Icc a b, Work.Spaces.HkMem α 6 (slice g τ) :=
  fun τ hτ => (h.reg6 τ hτ).2.1

/-- **The Galerkin class refines the coercivity class**: the profile of a strong solution is
admissible for the coercivity estimates, with the order dropping from `6` to `5`.  (This is
`Work.FTS.OpenPkg.AprioriOpen.coerAdm_of_galClass`, restated here so that the assembly does not
have to import the whole a-priori chapter.) -/
theorem coerAdm_of_galClass {α : ℝ} {f : Fn} (h : GalClass α f) : CoerAdm α f :=
  ⟨Work.FTS.Apriori.regQ_mono (α := α) (k := 6) (l := 5) (by norm_num) h.reg,
    h.vanish, h.axis, h.l12⟩

/-- `StrongSolOn` gives `CoerAdm α` of every slice. -/
theorem StrongSolOn.coer {α : ℝ} {Φs : Fn} {EllSol : Fn → Fn} {a b : ℝ} {g : Fam}
    (h : StrongSolOn α Φs EllSol a b g) :
    ∀ τ ∈ Set.Icc a b, CoerAdm α (slice g τ) :=
  fun τ hτ => coerAdm_of_galClass (h.gal τ hτ)

/-- `StrongSolOn` gives the vanishing on the two angular boundaries at every time. -/
theorem StrongSolOn.vanish {α : ℝ} {Φs : Fn} {EllSol : Fn → Fn} {a b : ℝ} {g : Fam}
    (h : StrongSolOn α Φs EllSol a b g) :
    ∀ τ ∈ Set.Icc a b, Work.Spaces.VanishTheta (slice g τ) :=
  fun τ hτ => (h.gal τ hτ).vanish

/-! ## Restriction of a strong solution -/

/-- A strong solution on `[a,b]` restricts to any subinterval `[a',b']`. -/
theorem StrongSolOn.mono {α : ℝ} {Φs : Fn} {EllSol : Fn → Fn} {a b a' b' : ℝ} {g : Fam}
    (h : StrongSolOn α Φs EllSol a b g) (ha : a ≤ a') (hb : b' ≤ b) (hab : a' ≤ b') :
    StrongSolOn α Φs EllSol a' b' g := by
  have hsub : Set.Icc a' b' ⊆ Set.Icc a b := Set.Icc_subset_Icc ha hb
  refine ⟨hab, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z θ τ hτ hz
    exact (h.eq z θ τ (hsub hτ) hz).mono (Set.Icc_subset_Icc ha hb)
  · exact fun τ hτ => h.law τ (hsub hτ)
  · exact fun τ hτ => h.gal τ (hsub hτ)
  · exact h.c1.mono (fun p hp => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := mem_slab.mp hp
      exact mem_slab.mpr ⟨h1, h2, h3, by linarith, by linarith⟩)
  · exact fun τ hτ => h.regLin τ (hsub hτ)
  · exact fun τ hτ => h.regRHS τ (hsub hτ)


/-! ## The regularity package `RegPkgMin` (design §1, verbatim) -/

/-- **THE REGULARITY PACKAGE `RegPkgMin`** (design `FTS_STRONG_ROUTE.md` §1, copied verbatim):
the finite-order replacement of `Work.FTS.Galerkin.RegPkg` that the physical bridge
`Work.FTS.RegPkgGal` consumes.  It drops `mem5`, the two-sided `deriv3` at `τ = 0`, the `smooth`
field on `τ ∈ (-1,0)` and the vanishing for `z < 0`; all four were pinned off the slab by the
frozen `Slab`-based vocabulary and are not satisfied by the solution of this route. -/
structure RegPkgMin (α : ℝ) (g : Fam) : Prop where
  /-- joint `C¹`-regularity on the interior of the quadrant, for all fake times `> 0` -/
  c1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
    (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioi 0)
  /-- `C⁴`-regularity in space at every fake time `τ ≥ 0` -/
  c4 : ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0
  /-- continuity in fake time up to `τ = 0`, at every point of the open quadrant -/
  cont : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ContinuousOn (fun τ => g z θ τ) (Set.Ici 0)
  /-- honest `ℋ⁴`-membership at every fake time `τ ≥ 0` -/
  mem4 : ∀ τ, 0 ≤ τ → Work.Spaces.HkMem α 4 (slice g τ)
  /-- an `ℋ³`-bound on the fake-time derivative, uniform on every horizon `(0,S)` (ruling
  cbc/fts_strong_iface_v2.md: the constant may depend on the horizon) -/
  dbd : ∀ S, 0 < S → ∃ Cd, ∀ τ, 0 < τ → τ < S →
    Work.Spaces.HkMem α 3 (gdot g τ) ∧ Work.Spaces.HkNorm α 3 (gdot g τ) ≤ Cd
  /-- vanishing on the two angular boundaries for `z ≥ 0` -/
  vanish : ∀ τ, 0 ≤ τ → ∀ z, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0

/-- The horizon-local `ℋ³` bound on `∂_τ g` (the shape of `RegPkgMin.dbd`). -/
def DbdLoc (α : ℝ) (g : Fam) : Prop :=
  ∀ S, 0 < S → ∃ Cd, ∀ τ, 0 < τ → τ < S →
    Work.Spaces.HkMem α 3 (gdot g τ) ∧ Work.Spaces.HkNorm α 3 (gdot g τ) ≤ Cd


/-- Gluing: agreement on `(0,S)` with a piece carrying a bound for `0 < τ < S`, for every `S`. -/
theorem DbdLoc.of_local {α : ℝ} {G : Fam}
    (h : ∀ S : ℝ, 0 < S → ∃ (g : Fam) (Cd : ℝ),
      (∀ z θ τ, τ ∈ Set.Ioo 0 S → G z θ τ = g z θ τ) ∧
      ∀ τ, 0 < τ → τ < S →
        Work.Spaces.HkMem α 3 (gdot g τ) ∧ Work.Spaces.HkNorm α 3 (gdot g τ) ≤ Cd) :
    DbdLoc α G := by
  intro S hS
  obtain ⟨g, Cd, hag, hb⟩ := h S hS
  refine ⟨Cd, fun τ hτ hτS => ?_⟩
  have hd : gdot G τ = gdot g τ := by
    funext z θ
    simp only [gdot]
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hτ, hτS⟩] with τ' hτ'
    exact hag z θ τ' hτ'
  rw [hd]
  exact hb τ hτ hτS

/-! ## The four hypotheses S1, S2, S3, S6

Each of these is the *statement* of a design item of `FTS_STRONG_ROUTE.md` §3, recorded here as a
named `Prop` so that the continuation S5 can be stated against it while the item's own subproject
is being built. -/

/-- **S1 (`lwp_H6`) — uniform local existence for the dynamic modulated equation**, in the form
needed by the continuation: a time step `δ = δ(K)` and a local theory uniform in the starting time
`τ₀ ≥ 0`, in the datum `g₀` (of the frozen class `RegQ α 6` with `Xn₆(g₀) ≤ K·α²`) and in
`α ∈ (0,α₀]`.  The design's S1 ("for data in `RegQ α 6`, ∃ T>0 and g on `[0,T]` with
`IsDynGSolWith (IsBslSolPos α)`, `HkMem α 6`, and `Xn₆` bounded") is the case `τ₀ = 0` of this,
without the uniformity; the uniformity in `τ₀` and in the datum is what the stepping of S5 uses,
and it is exactly what the IP₆-Galerkin + Gronwall proof of S1 delivers (the time step depends
only on the constants and on the bound `K`). -/
def LWPStrong (α : ℝ) (Φs : Fn) (EllSol : Fn → Fn) (α₀ K δ : ℝ) : Prop :=
  0 < δ ∧ 0 < K ∧ 0 < α₀ ∧
    ∀ α : ℝ, 0 < α → α ≤ α₀ → ∀ τ₀ : ℝ, 0 ≤ τ₀ → ∀ g₀ : Fn,
      RegQ α 6 g₀ → Xn6 α g₀ ≤ K * α ^ 2 →
        ∃ g : Fam, (∀ z θ, g z θ τ₀ = g₀ z θ) ∧ StrongSolOn α Φs EllSol τ₀ (τ₀ + δ) g

/-- **S2 (`persist_H6`) — the `ℋ⁶`-bound is preserved as long as the `ℋ⁴`-bound holds**: for a
strong solution on `[0,T]` whose slices have `Xn₄ ≤ C₀α²` and whose datum has `Xn₆ ≤ Kα²`, the
`ℋ⁶`-size stays below the *same* `Kα²` on the whole interval, independently of `T`.  (This is the
`k = 6` Gronwall argument of the design: the nonlinear terms of the `k = 6` energy inequality are
dominated by the `ℋ⁴`-dissipation once `Xn₄ ≤ C₀α²` and `α` is small, so the constant does not
grow.  Keeping the *same* constant is what lets the continuation restart with the *same* local
existence step `δ = δ(K)` at every junction.) -/
def PersistStrong (α : ℝ) (Φs : Fn) (EllSol : Fn → Fn) (C₀ K : ℝ) : Prop :=
  0 < K ∧ ∀ (g : Fam) (T : ℝ), 0 ≤ T → StrongSolOn α Φs EllSol 0 T g →
    (∀ τ ∈ Set.Icc 0 T, Xn α (slice g τ) ≤ C₀ * α ^ 2) →
    Xn6 α (slice g 0) ≤ K * α ^ 2 →
      ∀ τ ∈ Set.Icc 0 T, Xn6 α (slice g τ) ≤ K * α ^ 2



/-! ## The two inputs of the energy bootstrap S4 -/

/-- **The exact energy identity for a strong solution** (the `Pₙ = id` version of
`Work.FTS.OpenPkg.AprioriOpen.energy_deriv_within`): the fake-time derivative of the energy
`E(τ) = IP α (g(τ)) (g(τ))` is twice the pairing of the right-hand side with `g`.
It is *not* a consequence of `UnifIP` (which carries no formula for `IP`): for the paper's
concrete inner product it is the differentiation-under-the-integral-sign statement, and it is
recorded here as a hypothesis. -/
def EnergyId (IP : ℝ → Fn → Fn → ℝ) (α : ℝ) (Φs : Fn) (EllSol : Fn → Fn) : Prop :=
  ∀ (g : Fam) (T : ℝ), 0 ≤ T → StrongSolOn α Φs EllSol 0 T g →
    ∀ τ ∈ Set.Icc 0 T,
      HasDerivWithinAt (fun s => IP α (slice g s) (slice g s))
        (2 * (IP α (dynLin α g τ) (slice g τ)
          + IP α (dynRHS α (PsiCan Φs EllSol g) g τ) (slice g τ))) (Set.Icc 0 T) τ

/-- **N4's pairing estimate along the strong solution**: at every time at which the slice is small
enough for the pairing estimate to apply (`Xn₄ ≤ α^{7/4}`), the pairing of the nonlinear right-hand
side with `g` is bounded by `CcN·Pbd α (Xn₄)`.  Its proof from `Open2.PairData2` (with the star
package `StarPkgo2` and the elliptic package `EllPkgGo`) is
`Work.FTS.StrongGlobal.pairBndStrong_of_pairData2`; it is recorded as a hypothesis here so that S4
does not have to import the N4 row bundle. -/
def PairBndStrong (IP : ℝ → Fn → Fn → ℝ) (α : ℝ) (CcN : ℝ) (Φs : Fn) (EllSol : Fn → Fn) : Prop :=
  ∀ (g : Fam) (T : ℝ), 0 ≤ T → StrongSolOn α Φs EllSol 0 T g →
    ∀ τ ∈ Set.Icc 0 T, Xn α (slice g τ) ≤ α ^ (7 / 4 : ℝ) →
      IP α (dynRHS α (PsiCan Φs EllSol g) g τ) (slice g τ)
        ≤ CcN * Pbd α (Xn α (slice g τ))

end Work.FTS.StrongGlobal
