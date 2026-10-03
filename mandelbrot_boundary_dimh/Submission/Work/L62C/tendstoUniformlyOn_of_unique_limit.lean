import Mathlib
import Submission.Work.Normal.Basic

namespace Work.L62C

open Set Filter Topology Function

/-- **From a normal family with a unique subsequential limit to locally uniform convergence.**
Let `U ⊆ ℂ` be open, `F : ℕ → ℂ → ℂ` a sequence of functions whose family of terms is normal on
`U` and whose values on `U` are bounded by `M` (so that the `∞` alternative of `IsNormalFamily`
cannot occur), and let `g : ℂ → ℂ`.  If every locally uniform limit of a subsequence of `F` agrees
with `g` on `U`, then `F n → g` uniformly on every compact subset of `U`. -/
theorem tendstoUniformlyOn_of_unique_limit {U : Set ℂ} (hU : IsOpen U) {F : ℕ → ℂ → ℂ}
    {g : ℂ → ℂ} {M : ℝ} (hnormal : Work.Normal.IsNormalFamily (Set.range F) U)
    (hbdd : ∀ n z, z ∈ U → ‖F n z‖ ≤ M)
    (hlim : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ h : ℂ → ℂ,
      TendstoLocallyUniformlyOn (fun n => F (φ n)) h atTop U → Set.EqOn h g U) :
    ∀ δ : ℝ, 0 < δ → ∀ S : Set ℂ, S ⊆ U → IsCompact S →
      ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ S, dist (F n z) (g z) < δ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨δ, hδpos, S, hSU, hScomp, hbad⟩ := hcon
  -- `hbad : ∀ N, ∃ n, N ≤ n ∧ ∃ z, z ∈ S ∧ δ ≤ dist (F n z) (g z)`
  -- Extract a strictly increasing sequence of "bad" indices, each with a bad point of `S`.
  have hfreq : ∃ᶠ n in atTop, ∃ z, z ∈ S ∧ δ ≤ dist (F n z) (g z) := by
    rw [frequently_atTop]
    intro a
    obtain ⟨n, hn, hz⟩ := hbad a
    exact ⟨n, hn, hz⟩
  obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hfreq
  choose w hwS hwdist using hφP
  -- Normality of the (bad) subsequence gives a locally uniform limit `h` on `U`.
  obtain ⟨ψ, hψ, hcase⟩ := hnormal (fun k => F (φ k)) (fun k => ⟨φ k, rfl⟩)
  rcases hcase with ⟨h, hconv⟩ | htop
  · -- The limit `h` agrees with `g` on `U`, hence the convergence is uniform on `S`.
    have heq : Set.EqOn h g U := hlim (fun k => φ (ψ k)) (hφ.comp hψ) h hconv
    have hunif : TendstoUniformlyOn (fun k => F (φ (ψ k))) h atTop S :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hconv S hSU hScomp
    rw [Metric.tendstoUniformlyOn_iff] at hunif
    obtain ⟨N, hN⟩ := (eventually_atTop.mp (hunif δ hδpos))
    have h1 := hN N le_rfl (w (ψ N)) (hwS (ψ N))
    rw [heq (hSU (hwS (ψ N))), dist_comm] at h1
    have h3 := hwdist (ψ N)
    linarith
  · -- The `∞` alternative is excluded by the uniform bound.
    exfalso
    have hK : ({w 0} : Set ℂ) ⊆ U := by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hSU (hwS 0)
    obtain ⟨N, hN⟩ := htop ({w 0} : Set ℂ) hK isCompact_singleton (M + 1)
    have h4 : M + 1 ≤ ‖F (φ (ψ N)) (w 0)‖ := hN N le_rfl (w 0) (Set.mem_singleton (w 0))
    have h5 : ‖F (φ (ψ N)) (w 0)‖ ≤ M := hbdd (φ (ψ N)) (w 0) (hSU (hwS 0))
    linarith

end Work.L62C
