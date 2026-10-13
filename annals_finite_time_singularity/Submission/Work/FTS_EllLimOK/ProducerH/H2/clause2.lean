/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.ProducerH.H2.clause2` — the closed-box jet bounds of `E g`

Clause 2 of `RulingELF.PkgBoxH`: on a non-degenerate box `cbox a b` (so that
`iteratedFDerivWithin` is the unique within-jet), the operator norms of the first two
within-Fréchet derivatives of `Function.uncurry (E g)` are bounded by `K · Xn6 α g`, uniformly
over `g` of the source class.

The proof is the one intended in `ProducerH/BoxAux/pkgBoxH_clause2_of_lt.lean` (which does not
compile, and consumes the `sorry`ed `second_partials_le_Xn6`), with `BoxData.bounds` in place of
that lemma:

* `k = 0`: on the open strip by the mixed-jet bound of `E g` itself (`mixed 0 0 (E g) = E g`),
  and on the two boundary lines the value is `0` by `IsBslSol`;
* `k = 1, 2`: on the relative interior `(a,b) × (0,π/2)` the within-jet is the ordinary jet
  (`iteratedFDerivWithin_inter_open` + `iteratedFDerivWithin_of_isOpen`), whose norm is bounded
  by the plain partials (`BoxAux.jet_fderiv_partial_bound`), themselves bounded by `C · Xn6`
  (`BoxData.bounds`); continuity of `iteratedFDerivWithin ℝ k` on the box
  (`ContDiffOn.continuousOn_iteratedFDerivWithin`, using `UniqueDiffOn` — this is where `a < b`
  enters) and density of the relative interior propagate the bound to the closed box.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Basic
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Data
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.jet_fderiv_partial_bound
import Submission.Work.FTS_EllLimOK.ProducerH.MixedJets.mixed_jets_le_Xn6
import Submission.Work.FTS_EllLimOK.BoxDataH.WithinVec

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

theorem clause2 {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Fn →ₗ[ℝ] Fn}
    (hE : Ctx α Ce E) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hdata : BoxData α Ce E a b)
    (hc1 : ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
      ContDiffOn ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b)) :
    ∃ K : ℝ, 0 < K ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
      ∀ k : ℕ, k ≤ 2 → ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
        ‖iteratedFDerivWithin ℝ k (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b) p‖
          ≤ K * Work.FTS.StrongGlobal.Xn6 α g := by
  obtain ⟨C, hCpos, hC⟩ := hdata.bounds
  obtain ⟨Km, hKmpos, hKm⟩ :=
    Work.FTS_EllLimOK.ProducerH.MixedJets.mixed_jets_le_Xn6 hα hα4 hE
  refine ⟨max (4 * C) Km + 1, by positivity, ?_⟩
  intro g hg k hk p hp
  obtain ⟨z, θ⟩ := p
  have hX : (0 : ℝ) ≤ Work.FTS.StrongGlobal.Xn6 α g := Xn6_nonneg α g
  have hsm : ContDiffOn ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b) := hc1 g hg
  have hU : UniqueDiffOn ℝ (Work.FTS_EllLimOK.cbox a b) :=
    Work.FTS_EllLimOK.BoxDataH.uniqueDiffOn_cbox hab
  have hso_sub : Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (π / 2)
      ⊆ Work.FTS_EllLimOK.cbox a b := by
    intro q hq
    rw [Work.FTS_EllLimOK.mem_cbox]
    exact ⟨⟨le_of_lt hq.1.1, le_of_lt hq.1.2⟩, ⟨le_of_lt hq.2.1, le_of_lt hq.2.2⟩⟩
  have hso_open : IsOpen (Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    isOpen_Ioo.prod isOpen_Ioo
  have hclos : closure (Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (π / 2))
      = Work.FTS_EllLimOK.cbox a b := by
    rw [closure_prod_eq, closure_Ioo (ne_of_lt hab),
      closure_Ioo (by linarith [Real.pi_pos]), Work.FTS_EllLimOK.cbox]
  have hmemc : ((z, θ) : ℝ × ℝ) ∈ Work.FTS_EllLimOK.cbox a b := hp
  rw [Work.FTS_EllLimOK.mem_cbox] at hp
  -- ## the main bound, with the constant `max (4*C) Km`
  have hbound : ‖iteratedFDerivWithin ℝ k (Function.uncurry (E g))
        (Work.FTS_EllLimOK.cbox a b) (z, θ)‖
      ≤ max (4 * C) Km * Work.FTS.StrongGlobal.Xn6 α g := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- ## `k = 0`
      subst hk0
      simp only [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs, Function.uncurry]
      have hle : Km ≤ max (4 * C) Km := le_max_right _ _
      rcases lt_or_ge (0 : ℝ) θ with h1 | h1
      · rcases lt_or_ge θ (π / 2) with h2 | h2
        · -- the open strip: the mixed-jet bound of `E g` itself
          have hj := hKm g hg 0 0 (by norm_num) z θ
            ⟨lt_of_lt_of_le ha hp.1.1, h1, h2⟩
          rw [show Work.Spaces.mixed 0 0 (E g) = E g from by funext z θ; rfl] at hj
          exact le_trans hj (mul_le_mul_of_nonneg_right hle hX)
        · -- the line `θ = π/2`
          have hθeq : θ = π / 2 := le_antisymm hp.2.2 h2
          rw [hθeq, (hE g hg).1.1.2.2.1 z, abs_zero]
          exact mul_nonneg (le_trans hKmpos.le hle) hX
      · -- the line `θ = 0`
        have hθeq : θ = 0 := le_antisymm h1 hp.2.1
        rw [hθeq, (hE g hg).1.1.2.1 z, abs_zero]
        exact mul_nonneg (le_trans hKmpos.le hle) hX
    · -- ## `k = 1, 2`
      have hk12 : k = 1 ∨ k = 2 := by omega
      have hcontnorm : ContinuousOn
          (fun q : ℝ × ℝ =>
            ‖iteratedFDerivWithin ℝ k (Function.uncurry (E g))
              (Work.FTS_EllLimOK.cbox a b) q‖)
          (Work.FTS_EllLimOK.cbox a b) :=
        continuous_norm.comp_continuousOn
          (hsm.continuousOn_iteratedFDerivWithin (m := k) (by exact_mod_cast hk) hU)
      -- the value on the relative interior is the ordinary jet
      have hiff : ∀ q ∈ Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (π / 2),
          iteratedFDerivWithin ℝ k (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b) q
            = iteratedFDeriv ℝ k (Function.uncurry (E g)) q := by
        intro q hq
        have h2 := iteratedFDerivWithin_inter_open (𝕜 := ℝ) (s := Work.FTS_EllLimOK.cbox a b)
          (u := Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (π / 2))
          (f := Function.uncurry (E g)) (x := q) (n := k) hso_open hq
        rw [← h2, Set.inter_eq_right.mpr hso_sub]
        exact (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) k hso_open) hq
      -- the interior bound
      have hint : ∀ q ∈ Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (π / 2),
          ‖iteratedFDerivWithin ℝ k (Function.uncurry (E g))
            (Work.FTS_EllLimOK.cbox a b) q‖ ≤ 4 * C * Work.FTS.StrongGlobal.Xn6 α g := by
        intro q hq
        have hqz : q.1 ∈ Set.Icc a b := ⟨le_of_lt hq.1.1, le_of_lt hq.1.2⟩
        have hqθ : q.2 ∈ Set.Ioo (0 : ℝ) (π / 2) := hq.2
        have hcd : ContDiffAt ℝ 2 (Function.uncurry (E g)) q :=
          (hsm.mono hso_sub).contDiffAt (hso_open.mem_nhds hq)
        rw [hiff q hq]
        have hjet := Work.FTS_EllLimOK.ProducerH.BoxAux.jet_fderiv_partial_bound
          (f := E g) hcd
        have hpart := hC g hg q.1 hqz q.2 hqθ
        rcases hpart with ⟨h1, h2, h3, h4, h5, h6, -, -⟩
        have hCX : (0 : ℝ) ≤ C * Work.FTS.StrongGlobal.Xn6 α g := mul_nonneg hCpos.le hX
        rcases hk12 with hk1 | hk2
        · subst hk1
          calc ‖iteratedFDeriv ℝ 1 (Function.uncurry (E g)) q‖
              ≤ |Work.Spaces.pz (E g) q.1 q.2| + |Work.Spaces.pth (E g) q.1 q.2| := hjet.1
            _ ≤ 2 * (C * Work.FTS.StrongGlobal.Xn6 α g) := by linarith
            _ ≤ 4 * C * Work.FTS.StrongGlobal.Xn6 α g := by nlinarith [hX, hCpos]
        · subst hk2
          calc ‖iteratedFDeriv ℝ 2 (Function.uncurry (E g)) q‖
              ≤ |Work.Spaces.pz (Work.Spaces.pz (E g)) q.1 q.2|
                + |Work.Spaces.pth (Work.Spaces.pz (E g)) q.1 q.2|
                + |Work.Spaces.pz (Work.Spaces.pth (E g)) q.1 q.2|
                + |Work.Spaces.pth (Work.Spaces.pth (E g)) q.1 q.2| := hjet.2
            _ ≤ 4 * (C * Work.FTS.StrongGlobal.Xn6 α g) := by linarith
            _ = 4 * C * Work.FTS.StrongGlobal.Xn6 α g := by ring
      -- propagation to the closure of the relative interior
      have key : ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
          ‖iteratedFDerivWithin ℝ k (Function.uncurry (E g))
            (Work.FTS_EllLimOK.cbox a b) q‖ ≤ 4 * C * Work.FTS.StrongGlobal.Xn6 α g := by
        intro q hq
        by_contra hcon
        rw [not_le] at hcon
        have hqc : q ∈ closure (Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
          rw [hclos]; exact hq
        have hcwa : ContinuousWithinAt
            (fun u : ℝ × ℝ =>
              ‖iteratedFDerivWithin ℝ k (Function.uncurry (E g))
                (Work.FTS_EllLimOK.cbox a b) u‖)
            (Work.FTS_EllLimOK.cbox a b) q := hcontnorm q hq
        rw [Metric.continuousWithinAt_iff] at hcwa
        obtain ⟨δ, hδpos, hδ⟩ := hcwa
          (‖iteratedFDerivWithin ℝ k (Function.uncurry (E g))
              (Work.FTS_EllLimOK.cbox a b) q‖
            - 4 * C * Work.FTS.StrongGlobal.Xn6 α g) (by linarith)
        obtain ⟨u, hu, huδ⟩ := Metric.mem_closure_iff.mp hqc δ hδpos
        have huδ' : dist u q < δ := by rwa [dist_comm] at huδ
        have hu' := hδ (x := u) (hso_sub hu) huδ'
        rw [Real.dist_eq] at hu'
        have h3 : ‖iteratedFDerivWithin ℝ k (Function.uncurry (E g))
                (Work.FTS_EllLimOK.cbox a b) q‖
              - ‖iteratedFDerivWithin ℝ k (Function.uncurry (E g))
                (Work.FTS_EllLimOK.cbox a b) u‖
            ≤ |‖iteratedFDerivWithin ℝ k (Function.uncurry (E g))
                  (Work.FTS_EllLimOK.cbox a b) u‖
                - ‖iteratedFDerivWithin ℝ k (Function.uncurry (E g))
                  (Work.FTS_EllLimOK.cbox a b) q‖| := by
          rw [abs_sub_comm]
          exact le_abs_self _
        have := hint u hu
        linarith
      exact le_trans (key (z, θ) hmemc) (mul_le_mul_of_nonneg_right (le_max_left _ _) hX)
  -- ## the requested constant
  calc ‖iteratedFDerivWithin ℝ k (Function.uncurry (E g))
        (Work.FTS_EllLimOK.cbox a b) (z, θ)‖
      ≤ max (4 * C) Km * Work.FTS.StrongGlobal.Xn6 α g := hbound
    _ ≤ (max (4 * C) Km + 1) * Work.FTS.StrongGlobal.Xn6 α g :=
        mul_le_mul_of_nonneg_right (by linarith) hX

end Work.FTS_EllLimOK.ProducerH.H2
