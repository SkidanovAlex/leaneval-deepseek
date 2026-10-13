/-
# `E2_blocks` — block continuity of the `D_z`-transfer defect `E₂`

The transfer between the clean operator `𝓛̂` and the paper's `𝓛_Γ^T` uses the defect identity

  `D_z (𝓛_Γ^T f) = 𝓛̂ (D_z f) + E₂ α f`,  `E₂ α f = Ê₂ f + Γ(θ)·radS α f z`

(`Work.FTS.CoercivityFix.Transfer.Profiles`).  The weakened additivity package `Comm2w`
(`Assembly.Comm2w`) consumes `BlocksCont n (E₂ α f)` — continuity on the open quadrant `Qd` of
every mixed block `D_z^b D_θ^a (E₂ α f)` with `a + b ≤ n` — instead of the *refuted* `RegQ`
(which would require `C^∞` through `z = 0`, hence on `z < 0`, where `CoerAdm` says nothing).

**Why `BlocksCont 3` holds.**  The two summands of `E₂ α f` have different regularity:

* `Ê₂ f = (2 z f + 3 z D_θ f)/(1+z)²` is built from the partials `f`, `D_θ f` of the `C^∞`
  datum (`SmoothQuad f`) only, so it is `C^∞` on the open quadrant
  (`AuxE2.E2hat_contDiffOn_three`);
* `Γ(θ)·radS α f z` *separates*: the angular factor `Γ α` is `C^∞` on `(0,π/2)`
  (`contDiffOn_Gam_Qd`) and the radial factor `radS α f` is `C³` on `(0,∞)`.  The
  latter is the analytic content of the transfer: writing `a(z) = 2z/(c(1+z)²)`,
  `b(z) = 2z²/(1+z)³` and `A = L₁₂ f`,

    `radS = −(D_z a)·A − a·z·A' + (b'/c)·L₁₂(Transport f)(0)`,

  so `radS ∈ C³` as soon as `A ∈ C⁴` (`AuxE2.radS_contDiffOn_three`), and `A = L₁₂ f ∈ C⁴` on
  `(0,∞)` follows from the angular-moment tower for `SmoothQuad` data with `HkMem α 5 f`
  (`AuxE2.L12_contDiffOn_four_of_five`), exactly the regularity that
  `CoerAdm α f = RegQ α 5 f ∧ …` supplies.

So `E₂ α f` itself is jointly `C³` on the open quadrant (a *sum* of a `C^∞` and a `C³`
function — the mixed blocks of the separated product are exactly
`(D_θ^a Γ)(θ)·(D_z^b radS)(z)`), and the general finite-order fact
`contDiffOn_mixed_nat` — joint `C^m` on an open set gives continuity of every block of total
order `≤ m` — finishes.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.CoercivityFix.Assembly.Comm2w
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.CoercivityFix.Transfer.GamSmooth
import Submission.Work.FTS.CoercivityFix.Transfer.AuxE2.radS_contDiffOn_three
import Submission.Work.FTS.CoercivityFix.Transfer.AuxE2.L12_contDiffOn_four_of_five
import Submission.Work.FTS.CoercivityFix.Transfer.AuxE2.E2hat_contDiffOn_three

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Joint differentiability of finite order implies block continuity

The operators `D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ` are first-order with smooth coefficients,
so `mixed b a g = D_z^b D_θ^a g` costs `a + b` derivatives.  The following finite-order
companion of `Work.FTS.LocData.contDiffOn_mixed` (which is stated at the top order
`smoothOrder`) is what the block bookkeeping needs; it is independent of the `α`-ledger.

The three one-step lemmas express `pz`, `pth` as the first partial of `fderiv ℝ (uncurry ·)`
(`Work.Spaces.pz_eq_fderiv`, `Work.Spaces.pth_eq_fderiv`) and differentiate under `fderiv`
(`ContDiffOn.fderivWithin`, with `fderivWithin = fderiv` on the open set). -/

theorem contDiffOn_pth_nat {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {N : ℕ}
    (h : ContDiffOn ℝ (((N + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V) :
    ContDiffOn ℝ (((N : ℕ)) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Function.uncurry (Work.Spaces.pth G) p
      = (fderiv ℝ (Function.uncurry G) p) (0, 1) := by
    intro p hp
    exact Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ (((N : ℕ)) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := ((N : ℕ) : WithTop ℕ∞)) hV.uniqueDiffOn
      (by rw [Nat.cast_add, Nat.cast_one])
    refine h'.congr (fun p hp => ?_)
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ (((N : ℕ)) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

theorem contDiffOn_pz_nat {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {N : ℕ}
    (h : ContDiffOn ℝ (((N + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V) :
    ContDiffOn ℝ (((N : ℕ)) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Function.uncurry (Work.Spaces.pz G) p
      = (fderiv ℝ (Function.uncurry G) p) (1, 0) := by
    intro p hp
    exact Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ (((N : ℕ)) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := ((N : ℕ) : WithTop ℕ∞)) hV.uniqueDiffOn
      (by rw [Nat.cast_add, Nat.cast_one])
    refine h'.congr (fun p hp => ?_)
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ (((N : ℕ)) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

theorem contDiffOn_Dth_nat {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {N : ℕ}
    (h : ContDiffOn ℝ (((N + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V) :
    ContDiffOn ℝ (((N : ℕ)) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.Dth G)) V := by
  have hpth := contDiffOn_pth_nat hV h
  have hsin : ContDiffOn ℝ (((N : ℕ)) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => Real.sin (2 * p.2)) V := by fun_prop
  have := hsin.mul hpth
  refine this.congr (fun p hp => ?_)
  simp only [Function.uncurry, Work.Spaces.Dth]

theorem contDiffOn_Dz_nat {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {N : ℕ}
    (h : ContDiffOn ℝ (((N + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V) :
    ContDiffOn ℝ (((N : ℕ)) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.Dz G)) V := by
  have hpz := contDiffOn_pz_nat hV h
  have hfst : ContDiffOn ℝ (((N : ℕ)) : WithTop ℕ∞) (fun p : ℝ × ℝ => p.1) V := contDiffOn_fst
  have := hfst.mul hpz
  refine this.congr (fun p hp => ?_)
  simp only [Function.uncurry, Work.Spaces.Dz]

/-- `D_θ`-iterates cost one order each. -/
theorem contDiffOn_DthIter_nat {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    ∀ (i t : ℕ), ContDiffOn ℝ (((i + t : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V →
      ContDiffOn ℝ (((t : ℕ)) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.DthIter i G)) V := by
  intro i
  induction i with
  | zero =>
      intro t h
      simpa using h
  | succ i ih =>
      intro t h
      have h' : ContDiffOn ℝ (((i + (t + 1) : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V := by
        have heq : (((i + (t + 1) : ℕ)) : WithTop ℕ∞) = ((((i + 1) + t : ℕ)) : WithTop ℕ∞) := by
          rw [Nat.add_assoc, Nat.add_comm t 1, ← Nat.add_assoc]
        rw [heq]; exact h
      have hi := ih (t + 1) h'
      have := contDiffOn_Dth_nat (G := Work.Spaces.DthIter i G) hV (N := t) hi
      simpa only [Work.Spaces.DthIter_succ] using this

/-- `D_z`-iterates cost one order each. -/
theorem contDiffOn_DzIter_nat {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    ∀ (j t : ℕ), ContDiffOn ℝ (((j + t : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V →
      ContDiffOn ℝ (((t : ℕ)) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.DzIter j G)) V := by
  intro j
  induction j with
  | zero =>
      intro t h
      simpa using h
  | succ j ih =>
      intro t h
      have h' : ContDiffOn ℝ (((j + (t + 1) : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V := by
        have heq : (((j + (t + 1) : ℕ)) : WithTop ℕ∞) = ((((j + 1) + t : ℕ)) : WithTop ℕ∞) := by
          rw [Nat.add_assoc, Nat.add_comm t 1, ← Nat.add_assoc]
        rw [heq]; exact h
      have hj := ih (t + 1) h'
      have := contDiffOn_Dz_nat (G := Work.Spaces.DzIter j G) hV (N := t) hj
      simpa only [Work.Spaces.DzIter_succ] using this

/-- **Joint `C^m` on an open set gives continuity of every mixed block of total order `≤ m`.**
Since each of `D_z`, `D_θ` is a first-order operator with smooth coefficients (`z` resp.
`sin 2θ`), the block `mixed b a g = D_z^b D_θ^a g` costs `a + b` derivatives. -/
theorem contDiffOn_mixed_nat {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {m : ℕ}
    (h : ContDiffOn ℝ (((m : ℕ)) : WithTop ℕ∞) (Function.uncurry g) V) {a b : ℕ}
    (hab : a + b ≤ m) :
    ContinuousOn (Function.uncurry (Work.Spaces.mixed b a g)) V := by
  obtain ⟨t, ht⟩ : ∃ t, m = a + b + t := ⟨m - (a + b), (Nat.add_sub_of_le hab).symm⟩
  subst ht
  have h1 : ContDiffOn ℝ (((a + (b + t) : ℕ)) : WithTop ℕ∞) (Function.uncurry g) V := by
    have heq : ((((a + b) + t : ℕ)) : WithTop ℕ∞) = (((a + (b + t) : ℕ)) : WithTop ℕ∞) := by
      rw [Nat.add_assoc]
    rw [heq] at h; exact h
  have h2 := contDiffOn_DthIter_nat (G := g) hV a (b + t) h1
  have h3 := contDiffOn_DzIter_nat (G := Work.Spaces.DthIter a g) hV b t h2
  exact h3.continuousOn

/-! ## The theorem -/

theorem E2_blocks (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) (hn : n ≤ 3) :
    ∀ f : ℝ → ℝ → ℝ, Work.FTS.Nonlin.CoerAdm α f →
      Work.FTS.CoercivityFix.Assembly.BlocksCont n (Work.FTS.CoercivityFix.Transfer.E2 α f) := by
  intro f hf
  -- the `CoerAdm` ledger: `SmoothQuad f`, `HkMem α 5 f` and `L₁₂(f)(0) = 0`
  obtain ⟨hreg, hvan, haxis, hl12⟩ := hf
  obtain ⟨hsm, hmem5, hbdry⟩ := hreg
  -- the radial profile `radS α f` is `C³` on `(0,∞)`
  have hA : ContDiffOn ℝ 4 (fun z => Work.Coercivity.L12f f z) (Set.Ioi 0) :=
    AuxE2.L12_contDiffOn_four_of_five α hα hα1 hsm hmem5 hl12
  have hradS : ContDiffOn ℝ 3 (fun z => radS α f z) (Set.Ioi 0) :=
    AuxE2.radS_contDiffOn_three α hα hα1 hA
  -- the clean defect `Ê₂ f` is `C³` on the open quadrant
  have hE2hat : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => E2hat f p.1 p.2) Work.Construction.Qd :=
    AuxE2.E2hat_contDiffOn_three hsm
  -- the angular factor `Γ α` is `C³` on `(0,π/2)`
  have hGam : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2) Work.Construction.Qd :=
    contDiffOn_Gam_Qd α 3
  have hR : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => radS α f p.1) Work.Construction.Qd :=
    hradS.comp contDiffOn_fst (fun p hp => hp.1)
  have hGR : ContDiffOn ℝ 3
      (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2 * radS α f p.1) Work.Construction.Qd :=
    hGam.mul hR
  have hsum : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => E2hat f p.1 p.2
      + Work.Spaces.Gam α p.2 * radS α f p.1) Work.Construction.Qd := hE2hat.add hGR
  have hE2 : ContDiffOn ℝ 3 (Function.uncurry (E2 α f)) Work.Construction.Qd := by
    refine hsum.congr ?_
    intro p hp
    simp only [Function.uncurry, E2]
  -- descend to the order `n ≤ 3` and apply the block lemma
  intro a b hab
  have hEn : ContDiffOn ℝ (((n : ℕ)) : WithTop ℕ∞) (Function.uncurry (E2 α f))
      Work.Construction.Qd :=
    hE2.of_le (by exact_mod_cast hn)
  exact contDiffOn_mixed_nat (isOpen_Ioi.prod isOpen_Ioo) hEn hab

end Work.FTS.CoercivityFix.Transfer
