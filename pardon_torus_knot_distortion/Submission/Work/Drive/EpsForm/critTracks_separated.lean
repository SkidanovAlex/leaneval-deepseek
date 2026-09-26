import Mathlib
import Submission.Work.Drive.EpsForm.goodHeight_exists

/-!
# Critical tracks stay separated

Let `ψ : Submission.Diffeo`, let `n₀` be a direction, and let `X` be a finite set of parameters in
the parameter plane `ℝ × ℝ`.  Suppose that for each `x ∈ X` a *track* `y x : ℝ³ → ℝ × ℝ` is given
which is continuous at `n₀` and satisfies `y x n₀ = x`.

Then for all directions `n` close enough to `n₀`, two tracks `y x n` and `y x' n` have distinct
images on the surface `ψ(F_standard)` — provided their base points `x` and `x'` are not congruent
modulo the `2π`-lattice of the parametrisation.

The mathematical content is entirely the discreteness of the lattice
`{(2πk, 2πl) | k l : ℤ}` of periods of the parametrisation `par ψ` (combined with
`par_eq_iff`), together with the continuity of the tracks.
-/

open scoped Topology

namespace Work.Drive.EpsForm

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-- The `2π`-lattice of the parameter plane is closed. -/
private theorem two_pi_lattice_closed :
    IsClosed (Set.range (fun kl : ℤ × ℤ =>
      ((2 : ℝ) * Real.pi * (kl.1 : ℝ), (2 : ℝ) * Real.pi * (kl.2 : ℝ)))) := by
  -- The one-dimensional factor `{2πk | k : ℤ}` is the preimage of `ℤ ⊂ ℝ` under the
  -- homeomorphism `t ↦ t/(2π)`.
  have hfac : IsClosed (Set.range (fun k : ℤ => (2 : ℝ) * Real.pi * (k : ℝ))) := by
    have h1 : IsClosed (Set.range ((↑) : ℤ → ℝ)) := Int.isClosedEmbedding_coe_real.isClosed_range
    have h2 : IsClosed ((fun t : ℝ => t / (2 * Real.pi)) ⁻¹' (Set.range ((↑) : ℤ → ℝ))) :=
      h1.preimage (continuous_id.div_const _)
    convert h2 using 1
    ext t
    rw [Set.mem_preimage, Set.mem_range, Set.mem_range]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, (mul_div_cancel_left₀ (k : ℝ) (by positivity : (2 : ℝ) * Real.pi ≠ 0)).symm⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [hk, ← mul_div_assoc]
      exact mul_div_cancel_left₀ t (by positivity : (2 : ℝ) * Real.pi ≠ 0)
  have hEq : Set.range (fun kl : ℤ × ℤ =>
        ((2 : ℝ) * Real.pi * (kl.1 : ℝ), (2 : ℝ) * Real.pi * (kl.2 : ℝ)))
      = (Set.range (fun k : ℤ => (2 : ℝ) * Real.pi * (k : ℝ))) ×ˢ
        (Set.range (fun k : ℤ => (2 : ℝ) * Real.pi * (k : ℝ))) := by
    ext p
    constructor
    · rintro ⟨⟨k, l⟩, rfl⟩
      exact ⟨⟨k, rfl⟩, ⟨l, rfl⟩⟩
    · intro hp
      rw [Set.mem_prod] at hp
      obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := hp
      exact ⟨(k, l), by ext <;> simp [hk, hl]⟩
  rw [hEq]
  exact hfac.prod hfac

theorem critTracks_separated (ψ : Submission.Diffeo) (n₀ : LeanEval.KnotTheory.PardonDistortion.R3)
    (X : Finset (ℝ × ℝ)) (y : ℝ × ℝ → LeanEval.KnotTheory.PardonDistortion.R3 → ℝ × ℝ)
    (hcont : ∀ x ∈ X, ContinuousAt (y x) n₀) (hy0 : ∀ x ∈ X, y x n₀ = x) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : LeanEval.KnotTheory.PardonDistortion.R3, ‖n - n₀‖ < ρ →
      ∀ x ∈ X, ∀ x' ∈ X,
        (∀ k l : ℤ, x - x' ≠ (2 * Real.pi * k, 2 * Real.pi * l)) →
        Work.BoxShrink.Pinch.par ψ (y x n) ≠ Work.BoxShrink.Pinch.par ψ (y x' n) := by
  classical
  -- The lattice of periods of the parametrisation.
  set Lat : Set (ℝ × ℝ) := Set.range (fun kl : ℤ × ℤ =>
    ((2 : ℝ) * Real.pi * (kl.1 : ℝ), (2 : ℝ) * Real.pi * (kl.2 : ℝ))) with hLatdef
  have hLatClosed : IsClosed Lat := two_pi_lattice_closed
  -- The (finite) set of pairs of base points whose difference is *not* a period.
  set P : Finset ((ℝ × ℝ) × (ℝ × ℝ)) :=
    (X.product X).filter (fun z => z.1 - z.2 ∉ Lat) with hPdef
  -- Each such pair separates in a whole neighbourhood of `n₀`.
  have hev : ∀ z ∈ P, ∀ᶠ n in 𝓝 n₀, y z.1 n - y z.2 n ∉ Lat := by
    intro z hz
    obtain ⟨hzX, hznot⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hzX
    have hg : ContinuousAt (fun n : R3 => y z.1 n - y z.2 n) n₀ :=
      (hcont z.1 hz1).sub (hcont z.2 hz2)
    have hg0 : (fun n : R3 => y z.1 n - y z.2 n) n₀ = z.1 - z.2 := by
      simp [hy0 z.1 hz1, hy0 z.2 hz2]
    have hmem : (fun n : R3 => y z.1 n - y z.2 n) n₀ ∈ Latᶜ := by
      rw [hg0]; exact hznot
    have hopen : Latᶜ ∈ 𝓝 ((fun n : R3 => y z.1 n - y z.2 n) n₀) :=
      hLatClosed.isOpen_compl.mem_nhds hmem
    exact hg.tendsto.eventually hopen
  -- Simultaneously, by finiteness of `P`.
  have hevAll : ∀ᶠ n in 𝓝 n₀, ∀ z ∈ P, y z.1 n - y z.2 n ∉ Lat :=
    eventually_forall_mem_finset hev
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hevAll
  refine ⟨ρ, hρpos, ?_⟩
  intro n hn x hx x' hx' h
  -- The pair `(x, x')` belongs to `P`, by the hypothesis on `x - x'`.
  have hzP : (x, x') ∈ P := by
    rw [hPdef, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨hx, hx'⟩, ?_⟩
    rw [hLatdef]
    rintro ⟨kl, hkl⟩
    exact h kl.1 kl.2 hkl.symm
  have hnot : y x n - y x' n ∉ Lat :=
    hρsub (Metric.mem_ball.mpr (by simpa [dist_eq_norm] using hn)) (x, x') hzP
  -- If the two images coincided, their preimages would differ by a period.
  intro hpar
  obtain ⟨k, m, hk, hm⟩ := (par_eq_iff ψ (y x n) (y x' n)).mp hpar
  apply hnot
  refine ⟨(k, m), ?_⟩
  have h1 : (y x n).1 - (y x' n).1 = (2 : ℝ) * Real.pi * (k : ℝ) := by rw [hk]; ring
  have h2 : (y x n).2 - (y x' n).2 = (2 : ℝ) * Real.pi * (m : ℝ) := by rw [hm]; ring
  ext <;> simp only [Prod.fst_sub, Prod.snd_sub, h1, h2]

end

end Work.Drive.EpsForm
