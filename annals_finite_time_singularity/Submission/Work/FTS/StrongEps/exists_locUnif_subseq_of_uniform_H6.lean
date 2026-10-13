import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.LocUnif.exists_subseq_deriv4_of_uniform_H6
import Submission.Work.FTS.StrongEps.LocUnif.exists_subseq_deriv5_ae
import Submission.Work.FTS.StrongEps.LocUnif.FinalAssembly3

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongEps

/-- A subsequence of a uniformly convergent sequence converges uniformly on the same set. -/
theorem tendstoUniformlyOn_comp_strictMono {ι β : Type*} [UniformSpace β] {F : ℕ → ι → β}
    {g : ι → β} {K : Set ι} {ψ : ℕ → ℕ} (h : TendstoUniformlyOn F g Filter.atTop K)
    (hψ : StrictMono ψ) :
    TendstoUniformlyOn (fun n => F (ψ n)) g Filter.atTop K := by
  intro u hu
  exact hψ.tendsto_atTop.eventually (h u hu)

theorem exists_locUnif_subseq_of_uniform_H6 {α B : ℝ} (hα : 0 < α)
    {G : ℕ → ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry (G n))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 6 (G n) ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℝ → ℝ → ℝ,
      (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) →
        TendstoUniformlyOn (fun n (p : ℝ × ℝ) => G (φ n) p.1 p.2) (fun p => f p.1 p.2)
          Filter.atTop K) ∧
      ContDiffOn ℝ 4 (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) ∧
      Work.Spaces.HkNorm α 6 f ≤ B := by
  obtain ⟨φ, hφ, f, hconv0, hf4, hconv4⟩ :=
    LocUnif.exists_subseq_deriv4_of_uniform_H6 hα hsm hmem hb
  obtain ⟨ψ, hψ, hconv5⟩ :=
    LocUnif.exists_subseq_deriv5_ae hα hφ hsm hmem hb hconv0 hconv4 hf4
  have hBnn : 0 ≤ B := le_trans (Real.sqrt_nonneg _) (hb 0)
  -- the level-5 a.e. convergence, in the quantifier order needed for the energy bound
  have hconv5' : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))),
      ∀ (j i : ℕ), j + i = 5 →
        Filter.Tendsto (fun n => Work.Spaces.mixed j i (G ((φ ∘ ψ) n)) p.1 p.2) Filter.atTop
          (nhds (Work.Spaces.mixed j i f p.1 p.2)) := by
    have hfin : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))),
        ∀ t : Fin 6, Filter.Tendsto
          (fun n => Work.Spaces.mixed (5 - (t : ℕ)) (t : ℕ) (G ((φ ∘ ψ) n)) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed (5 - (t : ℕ)) (t : ℕ) f p.1 p.2)) := by
      rw [Filter.eventually_all]
      intro t
      exact hconv5 (5 - (t : ℕ)) (t : ℕ) (by have := t.isLt; omega)
    filter_upwards [hfin] with p hp j i hji
    have hi : i < 6 := by omega
    have hj : j = 5 - i := by omega
    subst hj
    exact hp ⟨i, hi⟩
  -- the uniform convergence of the level `≤ 4` slots along the composed subsequence
  have hconv4' : ∀ (j i : ℕ), j + i ≤ 4 → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) =>
          Work.Spaces.mixed j i (G ((φ ∘ ψ) n)) p.1 p.2)
        (fun p => Work.Spaces.mixed j i f p.1 p.2) Filter.atTop K := by
    intro j i hji K hK hKQ
    exact tendstoUniformlyOn_comp_strictMono (hconv4 j i hji K hK hKQ) hψ
  have hmem' : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G ((φ ∘ ψ) n)) := fun n => hmem _
  have hbsq' : ∀ n : ℕ, Work.Spaces.HkSq α 6 (G ((φ ∘ ψ) n)) ≤ B ^ 2 := by
    intro n
    have hn := hb ((φ ∘ ψ) n)
    have hknn : 0 ≤ Work.Spaces.HkSq α 6 (G ((φ ∘ ψ) n)) :=
      integral_nonneg fun z => integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 6 (G ((φ ∘ ψ) n)) z θ
    rw [Work.Spaces.HkNorm] at hn
    calc Work.Spaces.HkSq α 6 (G ((φ ∘ ψ) n))
        = (Real.sqrt (Work.Spaces.HkSq α 6 (G ((φ ∘ ψ) n)))) ^ 2 :=
          (Real.sq_sqrt hknn).symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hn 2
  have hSq : Work.Spaces.HkSq α 6 f ≤ B ^ 2 :=
    LocUnif.HkSq_le (α := α) (B := B) (G := G) (Φ := φ ∘ ψ) (f := f)
      hsm hconv4' hconv5' hmem' hbsq'
  refine ⟨φ ∘ ψ, hφ.comp hψ, f, ?_, hf4, ?_⟩
  · intro K hK hKQ
    exact tendstoUniformlyOn_comp_strictMono (hconv0 K hK hKQ) hψ
  · rw [Work.Spaces.HkNorm]
    exact (Real.sqrt_le_left hBnn).mpr hSq

end Work.FTS.StrongEps
