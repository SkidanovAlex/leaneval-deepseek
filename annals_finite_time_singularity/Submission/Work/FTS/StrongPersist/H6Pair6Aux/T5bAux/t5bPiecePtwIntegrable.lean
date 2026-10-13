/-
Copyright: work module for the Elgindi finite-time singularity project.

# `T5bAux/t5bPiecePtwIntegrable` — the pointwise bound and the product integrability of the
Leibniz summands `t5bPiece` of the row `T5bRow`

The analytic input is `T5bAux.t5bPiece_abs_le_quad` (in the sibling module
`T5bAux.t5bPiecePtwAux`), the pointwise bound of a single summand on the open quadrant by the
weighted `ℋ⁷`/`ℋ⁶` integrands of `f`.  Here it is upgraded to

* the corresponding a.e. bound for the product measure
  `(volume|Iz).prod (volume|Iθ)` (the complement of the open quadrant inside `Iz × Iθ` is the
  union of the coordinate hyperplane `z = 0` and the two boundary lines `θ = 0`, `θ = π/2`, a
  null set), and
* the `L¹`-integrability of the summand for that product measure (the dominating function is
  continuous on the open quadrant and has integrable `θ`-slices and an integrable `z`-marginal
  by `HkMem α 7 f` and `HkMem α 6 f`, so `integrable_prod_iff` produces its integrability and
  `Integrable.mono'` finishes).

Everything is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Ip6DzAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.t5bPiecePtwAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem t5bPiecePtwIntegrable {α : ℝ} {f : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ}
    {C4 C6 Cc : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hCsm : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Work.Construction.c2m θ))
    (hm6 : Work.Spaces.HkMem α 6 f) (hm7 : Work.Spaces.HkMem α 7 f)
    (hab : a + b ≤ 6) (hleaf : Work.FTS.TransportS.IsLeafW α a ρ)
    (hC4 : 0 ≤ C4) (hC6 : 0 ≤ C6) (hCc : 0 ≤ Cc)
    (hsup4 : ∀ k : ℕ, k ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        ≤ C4 * Work.Spaces.HkNorm α 4 f)
    (hsup6 : ∀ k : ℕ, k ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        ≤ C6 * Work.Spaces.HkNorm α 6 f)
    (hCcbd : ∀ θ ∈ Work.Spaces.Iθ, |Work.Construction.c2m θ| ≤ Cc)
    (hCcg : ∀ i : ℕ, 1 ≤ i → i ≤ 8 → ∀ (z θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|
        ≤ Cc * Real.sin (2 * θ))
    {k i : ℕ} (hk : k ≤ b) (hi : i ≤ a) :
    (∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      |Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece f ρ a b k i p|
        ≤ ((b.choose k : ℝ) * (a.choose i : ℝ))
            * ((if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
                else C6 * Work.Spaces.HkNorm α 6 f) * Cc)
            * (Work.Spaces.HkIntegrand α 7 f p.1 p.2
                + Work.Spaces.HkIntegrand α 6 f p.1 p.2)) ∧
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece f ρ a b k i p)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  set M : ℝ := (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
      else C6 * Work.Spaces.HkNorm α 6 f) with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    split_ifs
    · exact mul_nonneg hC4 (Work.Spaces.HkNorm_nonneg α 4 f)
    · exact mul_nonneg hC6 (Work.Spaces.HkNorm_nonneg α 6 f)
  have hA : ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z| ≤ M := by
    intro z hz
    rw [hMdef]
    by_cases hk4 : k ≤ 4
    · rw [if_pos hk4]; exact hsup4 k hk4 z hz
    · rw [if_neg hk4]; exact hsup6 k (by omega) z hz
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |t5bPiece f ρ a b k i (z, θ)| ≤
        ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
          * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ) :=
    t5bPiece_abs_le_quad (α := α) (f := f) (a := a) (b := b) (ρ := ρ) (M := M) (Cc := Cc)
      (k := k) (i := i) hα hα1 hab hleaf hMnn hCc hA hCcbd hCcg hk hi
  refine ⟨?_, ?_⟩
  · simpa only [Prod.mk.eta] using
      (Work.FTS.StrongPersist.H6Pair6Aux.ae_prod_Ioo
        (p := fun z θ => |t5bPiece f ρ a b k i (z, θ)| ≤
          ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
            * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ))
        (fun θ hθ z hz => hpt z θ hz hθ.1 hθ.2))
  · -- ## integrability
    have hconst : 0 ≤ ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (mul_nonneg hMnn hCc)
    have hdom_cont : ContinuousOn
        (fun p : ℝ × ℝ => ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
          * (Work.Spaces.HkIntegrand α 7 f p.1 p.2 + Work.Spaces.HkIntegrand α 6 f p.1 p.2))
        Work.FTS.EllipticEst.Q0 :=
      (((hso.continuousOn_HkIntegrand α 7).add (hso.continuousOn_HkIntegrand α 6)).const_mul _)
    have hdom_aesm : AEStronglyMeasurable
        (fun p : ℝ × ℝ => ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
          * (Work.Spaces.HkIntegrand α 7 f p.1 p.2 + Work.Spaces.HkIntegrand α 6 f p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _ hdom_cont
    have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        Integrable (fun θ : ℝ => ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
          * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz =>
        (((hm7.1 z hz).add (hm6.1 z hz)).const_mul
          (((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)))
    have hmarg : Integrable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
          * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have hbase : Integrable (fun z : ℝ => ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
          * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 7 f z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)))
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
        (hm7.2.add hm6.2).const_mul _
      refine hbase.congr ?_
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => by
        simp only [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_add (hm7.1 z hz) (hm6.1 z hz)]
    have hnorm : Integrable (fun z : ℝ => ∫ θ, ‖((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
          * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ)‖
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      refine hmarg.congr ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
      refine MeasureTheory.integral_congr_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_)
      exact (Real.norm_of_nonneg (mul_nonneg hconst
        (add_nonneg (Work.Spaces.HkIntegrand_nonneg α 7 f z θ)
          (Work.Spaces.HkIntegrand_nonneg α 6 f z θ)))).symm
    have hgint : Integrable
        (fun p : ℝ × ℝ => ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
          * (Work.Spaces.HkIntegrand α 7 f p.1 p.2 + Work.Spaces.HkIntegrand α 6 f p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      (MeasureTheory.integrable_prod_iff hdom_aesm).mpr ⟨hslice, hnorm⟩
    have hbd : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
        ‖t5bPiece f ρ a b k i p‖
          ≤ ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
            * (Work.Spaces.HkIntegrand α 7 f p.1 p.2 + Work.Spaces.HkIntegrand α 6 f p.1 p.2) := by
      simpa only [Prod.mk.eta] using
        (Work.FTS.StrongPersist.H6Pair6Aux.ae_prod_Ioo
          (p := fun z θ => ‖t5bPiece f ρ a b k i (z, θ)‖
            ≤ ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
              * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ))
          (fun θ hθ z hz => by
            rw [Real.norm_eq_abs]
            exact hpt z θ hz hθ.1 hθ.2))
    have hpiece_cont : ContinuousOn (fun p : ℝ × ℝ => t5bPiece f ρ a b k i p)
        Work.FTS.EllipticEst.Q0 := by
      have hAc : ContinuousOn
          (fun p : ℝ × ℝ => Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) p.1)
          Work.FTS.EllipticEst.Q0 := by
        have hc := continuousOn_DzdIter_L12 hα hα1 hso hm7 (k := k) (by omega)
        exact hc.comp continuousOn_fst (fun p hp => (Set.mem_prod.mp hp).1)
      have hBc : ContinuousOn
          (fun p : ℝ × ℝ => Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ)
            p.1 p.2) Work.FTS.EllipticEst.Q0 :=
        (hCsm.DthIter i).continuousOn
      have hXc : ContinuousOn
          (fun p : ℝ × ℝ => Work.Spaces.mixed (b - k + 1) (a - i) f p.1 p.2)
          Work.FTS.EllipticEst.Q0 :=
        (hso.mixed (b - k + 1) (a - i)).continuousOn
      have hYc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b a f p.1 p.2)
          Work.FTS.EllipticEst.Q0 :=
        (hso.mixed b a).continuousOn
      have hρc := continuousOn_leaf_Q0 hleaf
      have h := ((((hρc.mul hAc).mul hBc).mul hXc).mul hYc)
      exact h.congr (fun p _ => by simp only [Pi.mul_apply, t5bPiece])
    exact hgint.mono' (Work.Spaces.aesm_of_continuousOn_Qd _ hpiece_cont) hbd

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
