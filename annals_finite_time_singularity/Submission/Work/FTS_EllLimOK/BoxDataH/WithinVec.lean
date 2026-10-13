/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.BoxDataH.WithinVec` — the within-partial vector on a closed box

The producer `boxDataH_of_hasPkgH` of the closed-box data over the honest hypothesis `HasPkgH`
must extract a `C²`-limit from the `PkgBoxH` data, which is stated **within** the closed box
`cbox a b = [a,b] × [0,π/2]`:

```
ContDiffOn ℝ 2 (uncurry (E g)) (cbox a b) ∧
(∀ k ≤ 2, ∀ p ∈ cbox a b, ‖iteratedFDerivWithin ℝ k (uncurry (E g)) (cbox a b) p‖ ≤ K * Xn6 α g) ∧
(∀ p q ∈ cbox a b, ‖iteratedFDerivWithin ℝ 2 … p - … q‖ ≤ K * Xn6 α g * ‖p - q‖ ^ β)
```

(with `K, β` *outside* the `∀ g`, i.e. uniform along a `LimSeq4`).  Because the functions are not
known to be smooth on a *neighbourhood* of the box (`PkgStrip` is false), the previous producer
`BoxReg_of_uniform` — which consumes `SmoothStrip` members and *plain* partials — does not apply,
and neither does its Arzelà–Ascoli set-up (the family is only controlled on the box itself).

The repair carried out here is the standard one: run the extraction on the **within**-partials of
the members on the box, together with the `1`-Lipschitz retraction `clampB a b` of the plane onto
`cbox a b` (so that the family is defined, bounded and equicontinuous on an *open* set containing
the box), and feed the result to the staircase
`BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials` three times.

This module holds the vocabulary:

* `wPz`, `wPth`, `wPzz`, `wPtz`, `wPzt`, `wPtt` — the six within-partials of a function
  `F : ℝ × ℝ → ℝ` on a set `s`, as entries of `iteratedFDerivWithin ℝ 1 F s` and
  `iteratedFDerivWithin ℝ 2 F s` evaluated on the coordinate direction families `dir1 dz`,
  `consD dz (dir1 dz)`, … (so that the operator-norm bounds of `PkgBoxH` apply verbatim);
* `wJet` — the six components as one `Fin 6 → ℝ`-valued map (the Arzelà–Ascoli family);
* the bridges to the `fderivWithin` form (`wPz_eq_fderivWithin`, `wPzz_eq_fderivWithin`, …), which
  are what the staircase consumes;
* the retraction `clampB` of the plane onto the box and its `1`-Lipschitz property;
* the elementary consequences of the `PkgBoxH` bounds: boundedness, continuity, and the Hölder
  bound on the second-order components.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.BoxReg
import Submission.Work.FTS_EllLimOK.BoxRegAux.Defs
import Submission.Work.FTS_EllLimOK.BoxRegAux.jet_partials_facts
import Submission.Work.FTS_EllLimOK.BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials
import Submission.Work.FTS.StrongEps.LocUnif.exists_subseq_tendstoLocallyUniformlyOn_fin

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.BoxDataH

open Work.FTS_EllLimOK.BoxRegAux (dz dth dir1 consD prod_dir1_le_one prod_consD_dir1_le_one
  norm_dz_le_one norm_dth_le_one)

set_option autoImplicit false

/-! ## The six within-partials -/

/-- The `z`-partial, within the set `s`. -/
def wPz (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  iteratedFDerivWithin ℝ 1 F s p (dir1 dz)

/-- The `θ`-partial, within the set `s`. -/
def wPth (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  iteratedFDerivWithin ℝ 1 F s p (dir1 dth)

/-- The `∂_z∂_z`-partial, within the set `s`. -/
def wPzz (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  iteratedFDerivWithin ℝ 2 F s p (consD dz (dir1 dz))

/-- The `∂_z∂_θ`-partial, within the set `s`. -/
def wPzt (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  iteratedFDerivWithin ℝ 2 F s p (consD dz (dir1 dth))

/-- The `∂_θ∂_z`-partial, within the set `s`. -/
def wPtz (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  iteratedFDerivWithin ℝ 2 F s p (consD dth (dir1 dz))

/-- The `∂_θ∂_θ`-partial, within the set `s`. -/
def wPtt (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  iteratedFDerivWithin ℝ 2 F s p (consD dth (dir1 dth))

/-- The six within-partials as one `Fin 6 → ℝ`-valued map (the Arzelà–Ascoli family). -/
def wJet (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Fin 6 → ℝ :=
  ![wPz s F p, wPth s F p, wPzz s F p, wPtz s F p, wPzt s F p, wPtt s F p]

@[simp] theorem wJet_apply_zero (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    wJet s F p 0 = wPz s F p := rfl

@[simp] theorem wJet_apply_one (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    wJet s F p 1 = wPth s F p := rfl

@[simp] theorem wJet_apply_two (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    wJet s F p 2 = wPzz s F p := rfl

@[simp] theorem wJet_apply_three (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    wJet s F p 3 = wPtz s F p := rfl

@[simp] theorem wJet_apply_four (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    wJet s F p 4 = wPzt s F p := rfl

@[simp] theorem wJet_apply_five (s : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    wJet s F p 5 = wPtt s F p := rfl

/-! ## Unique differentiability of a non-degenerate box -/

/-- The closed box `cbox a b = [a,b] × [0,π/2]` with `a < b` is a set of unique differentiability
(a product of two non-degenerate closed intervals). -/
theorem uniqueDiffOn_cbox {a b : ℝ} (hab : a < b) : UniqueDiffOn ℝ (cbox a b) :=
  (uniqueDiffOn_Icc hab).prod (uniqueDiffOn_Icc (by linarith [Real.pi_pos]))

/-! ## Bridges to the `fderivWithin` form -/

theorem wPz_eq_fderivWithin {s : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hs : UniqueDiffWithinAt ℝ s p) :
    wPz s F p = fderivWithin ℝ F s p dz := by
  rw [wPz, iteratedFDerivWithin_one_apply hs]
  rfl

theorem wPth_eq_fderivWithin {s : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hs : UniqueDiffWithinAt ℝ s p) :
    wPth s F p = fderivWithin ℝ F s p dth := by
  rw [wPth, iteratedFDerivWithin_one_apply hs]
  rfl

theorem wPzz_eq_fderivWithin {s : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hs : UniqueDiffOn ℝ s) (hp : p ∈ s) :
    wPzz s F p = fderivWithin ℝ (fderivWithin ℝ F s) s p dz dz := by
  rw [wPzz, iteratedFDerivWithin_two_apply F hs hp]
  rfl

theorem wPzt_eq_fderivWithin {s : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hs : UniqueDiffOn ℝ s) (hp : p ∈ s) :
    wPzt s F p = fderivWithin ℝ (fderivWithin ℝ F s) s p dz dth := by
  rw [wPzt, iteratedFDerivWithin_two_apply F hs hp]
  rfl

theorem wPtz_eq_fderivWithin {s : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hs : UniqueDiffOn ℝ s) (hp : p ∈ s) :
    wPtz s F p = fderivWithin ℝ (fderivWithin ℝ F s) s p dth dz := by
  rw [wPtz, iteratedFDerivWithin_two_apply F hs hp]
  rfl

theorem wPtt_eq_fderivWithin {s : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hs : UniqueDiffOn ℝ s) (hp : p ∈ s) :
    wPtt s F p = fderivWithin ℝ (fderivWithin ℝ F s) s p dth dth := by
  rw [wPtt, iteratedFDerivWithin_two_apply F hs hp]
  rfl

/-! ## Componentwise bounds from the operator-norm bounds -/

/-- Componentwise bound of `wJet` from the operator-norm bounds of `iteratedFDerivWithin`. -/
theorem abs_wJet_le {s : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {K : ℝ}
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ p ∈ s, ‖iteratedFDerivWithin ℝ k F s p‖ ≤ K) :
    ∀ p ∈ s, ∀ m : Fin 6, |wJet s F p m| ≤ K := by
  intro p hp m
  have key1 : ∀ (u : ℝ × ℝ), ‖u‖ ≤ 1 →
      |iteratedFDerivWithin ℝ 1 F s p (dir1 u)| ≤ K := by
    intro u hu
    have h1 : ‖iteratedFDerivWithin ℝ 1 F s p (dir1 u)‖
        ≤ ‖iteratedFDerivWithin ℝ 1 F s p‖ * ∏ i : Fin 1, ‖dir1 u i‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    have h2 : ∏ i : Fin 1, ‖dir1 u i‖ ≤ 1 := prod_dir1_le_one u hu
    have h4 : (0 : ℝ) ≤ ∏ i : Fin 1, ‖dir1 u i‖ := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
    rw [Real.norm_eq_abs] at h1
    calc |iteratedFDerivWithin ℝ 1 F s p (dir1 u)|
        ≤ ‖iteratedFDerivWithin ℝ 1 F s p‖ * ∏ i : Fin 1, ‖dir1 u i‖ := h1
      _ ≤ K * ∏ i : Fin 1, ‖dir1 u i‖ :=
          mul_le_mul_of_nonneg_right (hb 1 (by norm_num) p hp) h4
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left h2
          (le_trans (norm_nonneg _) (hb 1 (by norm_num) p hp))
      _ = K := mul_one K
  have key2 : ∀ (u v : ℝ × ℝ), ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
      |iteratedFDerivWithin ℝ 2 F s p (consD v (dir1 u))| ≤ K := by
    intro u v hu hv
    have h1 : ‖iteratedFDerivWithin ℝ 2 F s p (consD v (dir1 u))‖
        ≤ ‖iteratedFDerivWithin ℝ 2 F s p‖ * ∏ i : Fin 2, ‖consD v (dir1 u) i‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    have h2 : ∏ i : Fin 2, ‖consD v (dir1 u) i‖ ≤ 1 := prod_consD_dir1_le_one u v hu hv
    have h4 : (0 : ℝ) ≤ ∏ i : Fin 2, ‖consD v (dir1 u) i‖ :=
      Finset.prod_nonneg (fun _ _ => norm_nonneg _)
    rw [Real.norm_eq_abs] at h1
    calc |iteratedFDerivWithin ℝ 2 F s p (consD v (dir1 u))|
        ≤ ‖iteratedFDerivWithin ℝ 2 F s p‖ * ∏ i : Fin 2, ‖consD v (dir1 u) i‖ := h1
      _ ≤ K * ∏ i : Fin 2, ‖consD v (dir1 u) i‖ :=
          mul_le_mul_of_nonneg_right (hb 2 (by norm_num) p hp) h4
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left h2
          (le_trans (norm_nonneg _) (hb 2 (by norm_num) p hp))
      _ = K := mul_one K
  fin_cases m
  · show |wJet s F p 0| ≤ K
    rw [wJet_apply_zero, wPz]
    exact key1 dz norm_dz_le_one
  · show |wJet s F p 1| ≤ K
    rw [wJet_apply_one, wPth]
    exact key1 dth norm_dth_le_one
  · show |wJet s F p 2| ≤ K
    rw [wJet_apply_two, wPzz]
    exact key2 dz dz norm_dz_le_one norm_dz_le_one
  · show |wJet s F p 3| ≤ K
    rw [wJet_apply_three, wPtz]
    exact key2 dz dth norm_dz_le_one norm_dth_le_one
  · show |wJet s F p 4| ≤ K
    rw [wJet_apply_four, wPzt]
    exact key2 dth dz norm_dth_le_one norm_dz_le_one
  · show |wJet s F p 5| ≤ K
    rw [wJet_apply_five, wPtt]
    exact key2 dth dth norm_dth_le_one norm_dth_le_one

/-- The `Fin 6`-norm of the within-jet vector is bounded by the operator-norm bound. -/
theorem norm_wJet_le {s : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {K : ℝ} {p : ℝ × ℝ} (hp : p ∈ s)
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ q ∈ s, ‖iteratedFDerivWithin ℝ k F s q‖ ≤ K) :
    ‖wJet s F p‖ ≤ K := by
  have hK : 0 ≤ K := le_trans (norm_nonneg _) (hb 0 (by norm_num) p hp)
  rw [pi_norm_le_iff_of_nonneg hK]
  intro m
  rw [Real.norm_eq_abs]
  exact abs_wJet_le hb p hp m

/-- The Hölder bound for the four second-order components of `wJet`. -/
theorem abs_wJet_sub_le_hölder {s : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {K β : ℝ}
    (hh : ∀ p ∈ s, ∀ q ∈ s,
      ‖iteratedFDerivWithin ℝ 2 F s p - iteratedFDerivWithin ℝ 2 F s q‖
        ≤ K * ‖p - q‖ ^ β)
    (hK : 0 ≤ K) :
    ∀ p ∈ s, ∀ q ∈ s, ∀ m : Fin 6, 2 ≤ m →
      |wJet s F p m - wJet s F q m| ≤ K * ‖p - q‖ ^ β := by
  intro p hp q hq m hm
  have hprod : ∀ (u v : ℝ × ℝ), ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
      |iteratedFDerivWithin ℝ 2 F s p (consD v (dir1 u))
        - iteratedFDerivWithin ℝ 2 F s q (consD v (dir1 u))| ≤ K * ‖p - q‖ ^ β := by
    intro u v hu hv
    have h4 : (0 : ℝ) ≤ K * ‖p - q‖ ^ β :=
      mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) _)
    have h5 : (0 : ℝ) ≤ ∏ i : Fin 2, ‖consD v (dir1 u) i‖ :=
      Finset.prod_nonneg (fun _ _ => norm_nonneg _)
    have h2 : ∏ i : Fin 2, ‖consD v (dir1 u) i‖ ≤ 1 := prod_consD_dir1_le_one u v hu hv
    have key : ‖(iteratedFDerivWithin ℝ 2 F s p - iteratedFDerivWithin ℝ 2 F s q)
        (consD v (dir1 u))‖ ≤ K * ‖p - q‖ ^ β := by
      refine le_trans (ContinuousMultilinearMap.le_opNorm _ _) ?_
      calc ‖iteratedFDerivWithin ℝ 2 F s p - iteratedFDerivWithin ℝ 2 F s q‖
            * ∏ i : Fin 2, ‖consD v (dir1 u) i‖
          ≤ (K * ‖p - q‖ ^ β) * ∏ i : Fin 2, ‖consD v (dir1 u) i‖ :=
            mul_le_mul_of_nonneg_right (hh p hp q hq) h5
        _ ≤ (K * ‖p - q‖ ^ β) * 1 := mul_le_mul_of_nonneg_left h2 h4
        _ = K * ‖p - q‖ ^ β := mul_one _
    rw [sub_apply, Real.norm_eq_abs] at key
    exact key
  fin_cases m
  · exact absurd hm (by decide)
  · exact absurd hm (by decide)
  · show |wJet s F p 2 - wJet s F q 2| ≤ K * ‖p - q‖ ^ β
    rw [wJet_apply_two, wJet_apply_two, wPzz, wPzz]
    exact hprod dz dz norm_dz_le_one norm_dz_le_one
  · show |wJet s F p 3 - wJet s F q 3| ≤ K * ‖p - q‖ ^ β
    rw [wJet_apply_three, wJet_apply_three, wPtz, wPtz]
    exact hprod dz dth norm_dz_le_one norm_dth_le_one
  · show |wJet s F p 4 - wJet s F q 4| ≤ K * ‖p - q‖ ^ β
    rw [wJet_apply_four, wJet_apply_four, wPzt, wPzt]
    exact hprod dth dz norm_dth_le_one norm_dz_le_one
  · show |wJet s F p 5 - wJet s F q 5| ≤ K * ‖p - q‖ ^ β
    rw [wJet_apply_five, wJet_apply_five, wPtt, wPtt]
    exact hprod dth dth norm_dth_le_one norm_dth_le_one

/-! ## Continuity of the components on the box -/

/-- Continuity on the box of the six components of `wJet`, from `C²`-smoothness within the box. -/
theorem continuousOn_wJet {a b : ℝ} {F : ℝ × ℝ → ℝ} (hab : a < b)
    (hsm : ContDiffOn ℝ 2 F (cbox a b)) :
    ∀ m : Fin 6, ContinuousOn (fun p : ℝ × ℝ => wJet (cbox a b) F p m) (cbox a b) := by
  have hU : UniqueDiffOn ℝ (cbox a b) := uniqueDiffOn_cbox hab
  have h1 : ContinuousOn (iteratedFDerivWithin ℝ 1 F (cbox a b)) (cbox a b) :=
    hsm.continuousOn_iteratedFDerivWithin (m := 1) (by norm_num) hU
  have h2 : ContinuousOn (iteratedFDerivWithin ℝ 2 F (cbox a b)) (cbox a b) :=
    hsm.continuousOn_iteratedFDerivWithin (m := 2) (by norm_num) hU
  intro m
  fin_cases m
  · refine (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => ℝ × ℝ) ℝ
      (dir1 dz)).continuous).comp_continuousOn h1).congr (fun p _ => ?_)
    rfl
  · refine (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => ℝ × ℝ) ℝ
      (dir1 dth)).continuous).comp_continuousOn h1).congr (fun p _ => ?_)
    rfl
  · refine (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ × ℝ) ℝ
      (consD dz (dir1 dz))).continuous).comp_continuousOn h2).congr (fun p _ => ?_)
    rfl
  · refine (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ × ℝ) ℝ
      (consD dth (dir1 dz))).continuous).comp_continuousOn h2).congr (fun p _ => ?_)
    rfl
  · refine (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ × ℝ) ℝ
      (consD dz (dir1 dth))).continuous).comp_continuousOn h2).congr (fun p _ => ?_)
    rfl
  · refine (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ × ℝ) ℝ
      (consD dth (dir1 dth))).continuous).comp_continuousOn h2).congr (fun p _ => ?_)
    rfl

/-! ## The retraction of the plane onto the box -/

/-- The clamping of a real number onto the interval `[a,b]`. -/
def clampI (a b t : ℝ) : ℝ := max a (min t b)

theorem clampI_mem {a b t : ℝ} (hab : a ≤ b) : clampI a b t ∈ Set.Icc a b :=
  ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem clampI_eq_of_mem {a b t : ℝ} (h : t ∈ Set.Icc a b) : clampI a b t = t := by
  rw [clampI, min_eq_left h.2, max_eq_right h.1]

theorem abs_clampI_sub_le (a b x y : ℝ) : |clampI a b x - clampI a b y| ≤ |x - y| := by
  have h1 : |min x b - min y b| ≤ |x - y| := by
    refine le_trans (abs_min_sub_min_le_max x b y b) ?_
    rw [max_le_iff]
    exact ⟨le_rfl, by simp⟩
  have h2 : |max a (min x b) - max a (min y b)| ≤ |min x b - min y b| := by
    refine le_trans (abs_max_sub_max_le_max a (min x b) a (min y b)) ?_
    rw [max_le_iff]
    exact ⟨by simp, le_rfl⟩
  calc |clampI a b x - clampI a b y| = |max a (min x b) - max a (min y b)| := rfl
    _ ≤ |min x b - min y b| := h2
    _ ≤ |x - y| := h1

/-- The `1`-Lipschitz retraction of the plane onto the box `cbox a b`. -/
def clampB (a b : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (clampI a b p.1, clampθ p.2)

theorem clampB_snd (a b : ℝ) (p : ℝ × ℝ) : (clampB a b p).2 = clampθ p.2 := rfl

theorem dist_clampB_le (a b : ℝ) (p q : ℝ × ℝ) :
    dist (clampB a b p) (clampB a b q) ≤ dist p q := by
  rw [Prod.dist_eq, Prod.dist_eq, sup_le_iff]
  constructor
  · refine le_trans ?_ le_sup_left
    rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs, Real.norm_eq_abs]
    exact abs_clampI_sub_le a b p.1 q.1
  · refine le_trans ?_ le_sup_right
    rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs, Real.norm_eq_abs]
    exact abs_clampθ_sub_clampθ_le p.2 q.2

theorem clampB_mem_cbox {a b : ℝ} {p : ℝ × ℝ} (hab : a ≤ b) : clampB a b p ∈ cbox a b :=
  ⟨clampI_mem hab, ⟨clampθ_nonneg _, clampθ_le _⟩⟩

theorem clampB_eq_of_mem_cbox {a b : ℝ} {p : ℝ × ℝ} (hp : p ∈ cbox a b) :
    clampB a b p = p := by
  obtain ⟨hp1, hp2⟩ := mem_cbox.mp hp
  simp only [clampB, clampI_eq_of_mem hp1, clampθ_eq_of_mem hp2]

end Work.FTS_EllLimOK.BoxDataH
