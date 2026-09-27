import Mathlib

open scoped Manifold ContDiff

namespace Work.Drive

/-- **Local-to-global glueing.**  If every point `p` of a compact set `K ⊆ ℝ × ℝ` has a
`C^∞` extension `g_p` agreeing with `u` on `K ∩ ball p (r_p)` for some `r_p > 0`, then `u`
has a global `C^∞` extension agreeing with `u` on `K`. -/
theorem exists_contDiff_of_isCompact_local {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {u : ℝ × ℝ → E} {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (h : ∀ p ∈ K, ∃ r : ℝ, 0 < r ∧ ∃ g : ℝ × ℝ → E,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ ∀ x ∈ K, dist x p < r → g x = u x) :
    ∃ g : ℝ × ℝ → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ ∀ x ∈ K, g x = u x := by
  classical
  -- Skolemize: for each `p : K` pick a positive radius `r p` and an extension `g p`.
  choose r hr g hg using fun p : K => h p.1 p.2
  -- The balls `ball (p : ℝ × ℝ) (r p)` cover `K`.
  have hcov : K ⊆ ⋃ p : K, Metric.ball (p : ℝ × ℝ) (r p) := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    simpa [Metric.mem_ball] using hr ⟨x, hx⟩
  -- A smooth partition of unity subordinate to that cover.
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, ℝ × ℝ)) hK.isClosed
    (fun p : K => Metric.ball (p : ℝ × ℝ) (r p)) (fun _ => Metric.isOpen_ball) hcov
  refine ⟨fun x => ∑ᶠ p : K, f p x • g p x, ?_, ?_⟩
  · -- Smoothness of the glued function.
    exact (f.contMDiff_finsum_smul (g := g)
      (fun p x _ => (hg p).1.contMDiff.contMDiffAt)).contDiff
  · -- The glued function agrees with `u` on `K`.
    intro x hx
    calc ∑ᶠ p : K, f p x • g p x
        = ∑ p ∈ f.finsupport x, f p x • g p x :=
          (f.sum_finsupport_smul_eq_finsum x g).symm
      _ = ∑ p ∈ f.finsupport x, f p x • u x := by
          refine Finset.sum_congr rfl fun p hp => ?_
          have hfp : f p x ≠ 0 := by
            have hmem := (f.mem_finsupport (x₀ := x)).mp hp
            simpa [Function.mem_support] using hmem
          have hxt : x ∈ tsupport (f p) := subset_tsupport _ (Function.mem_support.mpr hfp)
          have hxU := hf p hxt
          rw [Metric.mem_ball] at hxU
          rw [(hg p).2 x hx hxU]
      _ = (∑ p ∈ f.finsupport x, f p x) • u x :=
          (Finset.sum_smul (s := f.finsupport x) (f := fun p => f p x) (x := u x)).symm
      _ = (1 : ℝ) • u x := by rw [f.sum_finsupport x hx]
      _ = u x := one_smul ℝ (u x)

end Work.Drive
