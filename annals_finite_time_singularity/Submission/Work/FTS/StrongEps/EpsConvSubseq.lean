/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsConvSubseq.lean`

The extraction lemma `Work.FTS.StrongEps.EpsConvSubseq`: from a sequence of profiles `G n` with a
uniform `ℋ⁶`-bound (and `C^∞` regularity on the open quadrant) there is a strictly increasing
subsequence `φ` and a limit `f` such that the full convergence package `ConvLocUnifH6 α B` of
`Submission/Work/FTS/StrongEps/EpsConv.lean` holds for `fun n => G (φ n)`:

* local uniform convergence of every slot `D_z^j D_θ^i` with `j + i ≤ 4` on every compact subset
  of the open quadrant `Q0 = (0,∞) × (0,π/2)`,
* `C⁴`-regularity of the limit `f` on `Q0`,
* the `ℋ⁶`-bound `HkNorm α 6 f ≤ B` of the limit.

This is the assembly of the two extraction bricks of the `E5` limit:

* `LocUnif.exists_subseq_deriv4_of_uniform_H6` — the `C⁴`-extraction with the slot convergence;
* `LocUnif.exists_subseq_deriv5_ae` — the a.e. level-`5` extraction, used only to pass the
  `ℋ⁶`-energy bound to the limit through `LocUnif.HkSq_le`.

Both bricks are restricted to the open quadrant, and the diagonal composition of the two
subsequences is `Φ = φ ∘ ψ`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsConv
import Submission.Work.FTS.StrongEps.exists_locUnif_subseq_of_uniform_H6
import Submission.Work.FTS.StrongEps.LocUnif.exists_subseq_deriv4_of_uniform_H6
import Submission.Work.FTS.StrongEps.LocUnif.exists_subseq_deriv5_ae
import Submission.Work.FTS.StrongEps.LocUnif.FinalAssembly3

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

theorem EpsConvSubseq {α B : ℝ} (hα : 0 < α) {G : ℕ → Work.FTS.Galerkin.Fn}
    (hsm : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry (G n))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 6 (G n) ≤ B) :
    ∃ (φ : ℕ → ℕ) (f : Work.FTS.Galerkin.Fn), StrictMono φ ∧
      Work.FTS.StrongEps.ConvLocUnifH6 α B (fun n => G (φ n)) f := by
  classical
  -- the `C⁴`-extraction, with the slot convergence at levels `≤ 4`
  obtain ⟨φ, hφ, f, hconv0, hf4, hconv4⟩ :=
    LocUnif.exists_subseq_deriv4_of_uniform_H6 hα hsm hmem hb
  -- the a.e. level-`5` extraction, needed for the energy bound
  obtain ⟨ψ, hψ, hconv5⟩ :=
    LocUnif.exists_subseq_deriv5_ae hα hφ hsm hmem hb hconv0 hconv4 hf4
  let Φ : ℕ → ℕ := fun n => φ (ψ n)
  have hΦmono : StrictMono Φ := fun a b hab => hφ (hψ hab)
  -- the a.e. level-`5` convergence along the composed subsequence, in the quantifier order that
  -- `LocUnif.HkSq_le` consumes
  have hconv5' : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))),
      ∀ (j i : ℕ), j + i = 5 →
        Filter.Tendsto (fun n => Work.Spaces.mixed j i (G (Φ n)) p.1 p.2) Filter.atTop
          (nhds (Work.Spaces.mixed j i f p.1 p.2)) := by
    have hfin : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))),
        ∀ t : Fin 6, Filter.Tendsto
          (fun n => Work.Spaces.mixed (5 - (t : ℕ)) (t : ℕ) (G (Φ n)) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed (5 - (t : ℕ)) (t : ℕ) f p.1 p.2)) := by
      rw [Filter.eventually_all]
      intro t
      have h := hconv5 (5 - (t : ℕ)) (t : ℕ) (by have := t.isLt; omega)
      simpa only [Φ] using h
    filter_upwards [hfin] with p hp j i hji
    have hi : i < 6 := by omega
    have hj : j = 5 - i := by omega
    subst hj
    exact hp ⟨i, hi⟩
  -- the slot convergence at levels `≤ 4` along the composed subsequence
  have hconv4' : ∀ (j i : ℕ), j + i ≤ 4 → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Work.FTS.EllipticEst.Q0 →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => Work.Spaces.mixed j i (G (Φ n)) p.1 p.2)
        (fun p => Work.Spaces.mixed j i f p.1 p.2) Filter.atTop K := by
    intro j i hji K hK hKQ
    have h := hconv4 j i hji K hK hKQ
    simpa only [Φ] using tendstoUniformlyOn_comp_strictMono h hψ
  -- the hypotheses of `LocUnif.HkSq_le` for the composed subsequence
  have hmem' : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G (Φ n)) := fun n => hmem _
  have hbsq' : ∀ n : ℕ, Work.Spaces.HkSq α 6 (G (Φ n)) ≤ B ^ 2 := by
    intro n
    have hn := hb (Φ n)
    have hknn : 0 ≤ Work.Spaces.HkSq α 6 (G (Φ n)) :=
      integral_nonneg fun z => integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 6 (G (Φ n)) z θ
    rw [Work.Spaces.HkNorm] at hn
    calc Work.Spaces.HkSq α 6 (G (Φ n))
        = (Real.sqrt (Work.Spaces.HkSq α 6 (G (Φ n)))) ^ 2 :=
          (Real.sq_sqrt hknn).symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hn 2
  have hSq : Work.Spaces.HkSq α 6 f ≤ B ^ 2 :=
    LocUnif.HkSq_le (α := α) (B := B) (G := G) (Φ := Φ) (f := f)
      hsm hconv4' hconv5' hmem' hbsq'
  have hBnn : 0 ≤ B := le_trans (Real.sqrt_nonneg _) (hb 0)
  have hNorm : Work.Spaces.HkNorm α 6 f ≤ B := by
    rw [Work.Spaces.HkNorm]
    exact (Real.sqrt_le_left hBnn).mpr hSq
  -- the package `ConvLocUnifH6` lists the compact sets before the slot indices
  refine ⟨Φ, f, hΦmono, ?_, hf4, hNorm⟩
  intro K hK hKQ j i hji
  exact hconv4' j i hji K hK hKQ

end Work.FTS.StrongEps
