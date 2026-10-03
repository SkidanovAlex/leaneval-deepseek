import Mathlib
import Submission.Lib.Unif2.Work.Kernel.pairing_pole_singular_aux
import Submission.Lib.Unif2.Work.Kernel.aeStronglyMeasurable_pairIntegrand_plateau

/-!
# The pole identity for a test function with a logarithmic singularity at the *other* pole

`Work.Kernel.pairing_pole_singular` extends `Work.Kernel.pairing_pole_smooth` (the pole identity
`pairing f Ψ = 2π Ψ(pole)` for a *smooth* test function) to the test function `χ · gA`, which is
singular at a second pole `a` at which the integration function `gB` is harmonic.

Route: apply `pairing_pole_smooth` to the *smooth* test functions `Ψ n = χ · Θ n (gA)`, where `Θ n`
is a plateau profile equal to the identity near `0` and constant (value `(M₀+n)/2`) above the level
`M₀ + n`; since `gA → +∞` at `a`, the profile cuts off the singularity of `χ · gA` at `a`, and each
`Ψ n` pairs to `2π χ b gA b`.  A chart-by-chart dominated-convergence argument
(`Work.Drive.pairTerm_tendsto_of_dominated`) then identifies the pairing of `χ · gA` with the
common value of the family.
-/

open Set Metric MeasureTheory Filter
open scoped Manifold Topology Gradient ContDiff

noncomputable section

set_option linter.unusedSectionVars false

namespace Work.Kernel

open scoped Manifold Topology in
theorem pairing_pole_singular {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X} (hab : a ≠ b)
    (E : Work.Kernel.GreenCover ι Ω K a b)
    (hKc : IsCompact K) (haK : a ∈ K) (hbK : b ∈ K) (hΩo : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {gA gB : X → ℝ} (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA)
    (hgB : Work.SimplyConnected.ABS.IsGreenOn Ω b gB)
    {H : ℂ → ℝ} {r : ℝ} (hrpos : 0 < r) (hrρ : r ≤ E.ρ E.ib)
    (hpmem : (chartAt ℂ (E.y E.ib)) b ∈
      Metric.ball ((chartAt ℂ (E.y E.ib)) (E.y E.ib)) (E.ρ E.ib))
    (hH : InnerProductSpace.HarmonicOnNhd H (Metric.ball ((chartAt ℂ (E.y E.ib)) b) r))
    (hueq : ∀ z ∈ Metric.ball ((chartAt ℂ (E.y E.ib)) b) r,
      gB ((chartAt ℂ (E.y E.ib)).symm z)
        = -Real.log ‖z - (chartAt ℂ (E.y E.ib)) b‖ + H z)
    (hgBdiff : ∀ k, Work.Drive.ChartDiff (chartAt ℂ (E.y k)) gB (Ω \ ({a, b} : Set X)))
    (hψc1 : ∀ k i, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((E.ψ i) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hβc1 : ∀ k i, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((E.β i) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    {χ : X → ℝ}
    (hχdiff : ∀ k, Work.Drive.ChartDiff (chartAt ℂ (E.y k)) χ Ω)
    (hχc1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 (χ ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hχK : tsupport χ ⊆ K) (hχΩ : tsupport χ ⊆ Ω) (hχ1 : χ =ᶠ[𝓝 a] 1) :
    Work.Drive.pairing E.y E.ρ E.σ E.ψ gB (fun x : X => χ x * gA x)
      = 2 * Real.pi * (χ b * gA b) := by
  classical
  have haΩ : a ∈ Ω := hKΩ haK
  have hbΩ : b ∈ Ω := hKΩ hbK
  have hba : b ≠ a := fun h => hab h.symm
  have hgAbpos : 0 < gA b := hgA.1 b hbΩ hba
  -- the level parameter and the plateau profiles
  set Mb : ℝ := max (4 * gA b) 1 with hMb
  have hMbpos : 0 < Mb := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hMble : 4 * gA b ≤ Mb := by rw [hMb]; exact le_max_left _ _
  obtain ⟨Θ, hΘc1, -, hΘid, hΘplat, hΘder, hΘabs⟩ := exists_plateau_seq Mb hMbpos
  -- the test functions
  set Ψ : ℕ → X → ℝ := fun n x => if x = a then Θ n (Mb + n) else χ x * Θ n (gA x) with hΨ
  -- the cover with the two pole charts interchanged
  let E' : Work.Kernel.GreenCover ι Ω K b a :=
    { y := E.y, s := E.s, σ := E.σ, ρ := E.ρ, ψ := E.ψ, β := E.β, ia := E.ib, ib := E.ia,
      hspos := E.hspos, hsσ := E.hsσ, hσρ := E.hσρ, htgt := E.htgt, hballΩ := E.hballΩ,
      hψnonneg := E.hψnonneg, hψsupp := E.hψsupp, hsum := E.hsum, hψdiff := E.hψdiff,
      ha_mem := E.hb_mem, ha_nmem := E.hb_nmem, hb_mem := E.ha_mem, hb_nmem := E.ha_nmem,
      hβone := E.hβone, hβsupp := E.hβsupp, hβdiff := E.hβdiff }
  -- ## the test function data
  have htest : ∀ n : ℕ,
      (∀ k, Work.Drive.ChartDiff (chartAt ℂ (E.y k)) (Ψ n) Ω) ∧
      (∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
        ContDiffAt ℝ 1 ((Ψ n) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x)) ∧
      tsupport (Ψ n) ⊆ K ∧ tsupport (Ψ n) ⊆ Ω := by
    intro n
    -- `Ψ n` is chartwise `C¹` away from `a`
    have hoff : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source, x ≠ a →
        ContDiffAt ℝ 1 ((Ψ n) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x) := by
      intro k x hx hxne
      have hbase := contDiffAt_chartPullback_mul_comp_of_harmonic (Ω := Ω) (K := K) E
        hχc1 hχΩ hgA (hΘc1 n) k x hx hxne
      have hev : ((fun y : X => χ y * Θ n (gA y)) ∘ (chartAt ℂ (E.y k)).symm)
          =ᶠ[𝓝 ((chartAt ℂ (E.y k)) x)] ((Ψ n) ∘ (chartAt ℂ (E.y k)).symm) := by
        have hxtgt : (chartAt ℂ (E.y k)) x ∈ (chartAt ℂ (E.y k)).target :=
          (chartAt ℂ (E.y k)).map_source hx
        have hset : ({a} : Set X)ᶜ ∈ 𝓝 ((chartAt ℂ (E.y k)).symm ((chartAt ℂ (E.y k)) x)) := by
          rw [(chartAt ℂ (E.y k)).left_inv hx]
          exact (isClosed_singleton.isOpen_compl).mem_nhds (by simpa using hxne)
        have hpre : (chartAt ℂ (E.y k)).symm ⁻¹' ({a} : Set X)ᶜ ∈ 𝓝 ((chartAt ℂ (E.y k)) x) :=
          ((chartAt ℂ (E.y k)).continuousAt_symm hxtgt).preimage_mem_nhds hset
        filter_upwards [hpre] with w hw
        have hw' : (chartAt ℂ (E.y k)).symm w ≠ a := by simpa using hw
        simp only [Function.comp_apply, hΨ, if_neg hw']
      exact hbase.congr_of_eventuallyEq hev.symm
    -- `Ψ n` is constant near `a`
    have hconst : Ψ n =ᶠ[𝓝 a] (fun _ => Θ n (Mb + n)) := by
      have hgt : ∀ᶠ x in 𝓝 a, x ≠ a → Mb + n ≤ gA x :=
        eventually_le_green_near_pole hΩo haΩ hgA (Mb + n)
      filter_upwards [hgt, hχ1] with x hx1 hx2
      by_cases hxa : x = a
      · simp [hΨ, hxa]
      · have hx2' : χ x = 1 := hx2
        simp only [hΨ, if_neg hxa]
        rw [hx2', one_mul, hΘplat n (gA x) (hx1 hxa), hΘplat n (Mb + n) le_rfl]
    -- the support
    have hsupp : tsupport (Ψ n) ⊆ tsupport χ := by
      have ha1 : χ a = 1 := hχ1.self_of_nhds
      have hsub : Function.support (Ψ n) ⊆ Function.support χ := by
        intro x hx
        rw [Function.mem_support] at hx ⊢
        by_cases hxa : x = a
        · subst hxa
          rw [ha1]
          exact one_ne_zero
        · intro h0
          exact hx (by simp only [hΨ, if_neg hxa, h0, zero_mul])
      calc tsupport (Ψ n) = closure (Function.support (Ψ n)) := rfl
        _ ⊆ closure (Function.support χ) := closure_mono hsub
        _ = tsupport χ := rfl
    have hΨΩ' : tsupport (Ψ n) ⊆ Ω := fun x hx => hχΩ (hsupp hx)
    have hΨK' : tsupport (Ψ n) ⊆ K := fun x hx => hχK (hsupp hx)
    obtain ⟨hdiff, hc1⟩ := chartDiff_and_contDiffAt_of_plateau (Ω := Ω) (K := K) E hoff
      hΨΩ' hconst
    exact ⟨hdiff, hc1, hΨK', hΨΩ'⟩
  -- ## the pole identity for the smooth test functions
  have hP : ∀ n : ℕ, Work.Drive.pairing E.y E.ρ E.σ E.ψ gB (Ψ n) = 2 * Real.pi * (χ b * gA b) := by
    intro n
    have hgd : ∀ k, Work.Drive.ChartDiff (chartAt ℂ (E'.y k)) gB (Ω \ ({b, a} : Set X)) := by
      intro k
      have h1 := hgBdiff k
      have h2 : ({b, a} : Set X) = {a, b} := by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [h2]
      exact h1
    have hmain := Work.Kernel.pairing_pole_smooth (Ω := Ω) (K := K) (a := b) (b := a) E'
      hKc hbK hΩo hKΩ hgB hgd hrpos hrρ hpmem hH hueq hψc1 hβc1
      (htest n).1 (htest n).2.1 (htest n).2.2.1 (htest n).2.2.2
    have hbval : (Ψ n) b = χ b * gA b := by
      have h1 : ¬ (b = a) := hba
      simp only [hΨ, if_neg h1]
      have h2 : gA b ≤ (Mb + n) / 4 := by
        have h3 : Mb ≤ Mb + (n : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg n)
        linarith
      rw [hΘid n (gA b) hgAbpos.le h2]
    rw [show Work.Drive.pairing E'.y E'.ρ E'.σ E'.ψ gB (Ψ n)
        = Work.Drive.pairing E.y E.ρ E.σ E.ψ gB (Ψ n) from rfl] at hmain
    rw [hbval] at hmain
    exact hmain
  -- ## the limit
  have hlim : Filter.Tendsto (fun n => Work.Drive.pairing E.y E.ρ E.σ E.ψ gB (Ψ n))
      Filter.atTop (𝓝 (Work.Drive.pairing E.y E.ρ E.σ E.ψ gB (fun x : X => χ x * gA x))) := by
    simp only [Work.Drive.pairing]
    refine tendsto_finset_sum Finset.univ (fun i _ => ?_)
    obtain ⟨g, hgint, hgdom⟩ := exists_integrable_domination (Ω := Ω) (K := K) E hab hΩo haK hbK
      hKΩ hgA hgB hχc1 hχ1 hψc1 hrpos hrρ hpmem hH hueq hΘc1 hΘder hΘabs i
    refine Work.Drive.pairTerm_tendsto_of_dominated (x := E.y i) (ρ := E.ρ i) (σ := E.σ i)
      (W := E.ψ i) (f := gB) (χlim := fun x : X => χ x * gA x) (χ := Ψ) (g := g)
      ?_ ?_ (fun n => hgdom n) hgint
    · exact Work.Analysis.tendsto_gradient_clampedPullback (x := E.y i) (ρ := E.ρ i)
        (u := Ψ) (w := fun x : X => χ x * gA x)
        (eventually_eventuallyEq_clampedPullback_plateau (Ω := Ω) (K := K) E hΩo haΩ hgA hχΩ
          hΘid i)
    · intro n
      exact aeStronglyMeasurable_pairIntegrand_plateau (Ω := Ω) (K := K) E hgB hgA hχc1 hχΩ
        hψc1 hΘc1 i n
  have hconst : Filter.Tendsto (fun n => Work.Drive.pairing E.y E.ρ E.σ E.ψ gB (Ψ n))
      Filter.atTop (𝓝 (2 * Real.pi * (χ b * gA b))) :=
    tendsto_const_nhds.congr' (Filter.Eventually.of_forall (fun n => (hP n).symm))
  exact tendsto_nhds_unique hlim hconst

end Work.Kernel
