import Mathlib
import Submission.Work.Normal.Basic
import Submission.Work.Normal.exists_compact_exhaustion
import Submission.Work.Normal.exists_subseq_tendstoUniformlyOn_of_locallyBounded
import Submission.Work.Normal.exists_subseq_tendstoLocallyUniformlyOn_of_exhaustion

open Filter Topology

namespace Work.Normal

/-- **Montel's theorem**, locally bounded form: a family of holomorphic (complex differentiable)
functions on an open set `U ⊆ ℂ`, which is uniformly bounded on every compact subset of `U`,
is normal on `U`: every sequence of members has a subsequence converging locally uniformly on
`U` to a holomorphic function.

Route: `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` (Cauchy's estimate) bounds `‖f'‖` on
a compact `K ⊆ U` in terms of the bound for `f` on a fixed neighbourhood of `K`; the mean value
inequality then yields equicontinuity on `K`.  Finish with `ArzelaAscoli` (Mathlib's Arzela–Ascoli
theorems for the compact-open topology) or with a diagonal argument over a compact exhaustion of
`U` using completeness of the sup-norm space on a compact set. -/
theorem montel_locallyBounded {Fam : Set (ℂ → ℂ)} {U : Set ℂ} (hU : IsOpen U)
    (hhol : ∀ f ∈ Fam, DifferentiableOn ℂ f U) (hbdd : IsLocallyBoundedOn Fam U) :
    IsNormalFamily Fam U := by
  intro u hu
  -- a compact exhaustion of `U`
  obtain ⟨K, hKc, hKU, hcover⟩ := exists_compact_exhaustion U hU
  -- on each `K n` we may extract a further subsequence converging uniformly
  have hsub : ∀ (ψ : ℕ → ℕ), StrictMono ψ → ∀ n : ℕ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ g : ℂ → ℂ, TendstoUniformlyOn (fun k => u (ψ (σ k))) g atTop (K n) := by
    intro ψ _hψ n
    refine exists_subseq_tendstoUniformlyOn_of_locallyBounded hU (hKc n) (hKU n)
      (fun k => u (ψ k)) (fun k => hhol _ (hu _)) ?_
    exact hbdd.mono_family (by rintro f ⟨k, rfl⟩; exact hu _)
  -- diagonal extraction over the exhaustion
  obtain ⟨φ, hφ, g, hg⟩ :=
    exists_subseq_tendstoLocallyUniformlyOn_of_exhaustion hU u K hcover hsub
  exact ⟨φ, hφ, Or.inl ⟨g, hg⟩⟩

end Work.Normal
