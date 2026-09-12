import ChallengeDeps
import Submission.Work.ModelStar.ModelStarHeight
import Submission.GeometryOfNumbers.PlaneFinrank
import Submission.GeometryOfNumbers.RationalSpan
import Submission.Bridge.Challenge
import Submission.Work.Interface.DirichletBoundSmall
import Submission.Work.Dani.Part2

/-!
# From the lattice Dirichlet statement to the ★-pair (and conjunct 1)

The Mathlib-level input on the critical path of de Saxcé's Theorem 9 is the following
**lattice Dirichlet statement** (Commons `Lattice.Minkowski.cone_basis_family`): for a lattice
`M ⊆ ℝᵈ` and an `ℓ`-plane `W`, and every `ε > 0`, there are `k ≤ ℓ` independent lattice vectors
`b₁,…,b_k` whose *whole plane* lies within relative angle `ε` of `W` and whose covolume
(`‖⋀ b‖`) is at most `C ε^{−k(d−ℓ)/d} covol(M)^{k/d}`.

This module shows that for the standard lattice `ℤᵈ` this statement *is* the ★-pair of the
interface layer, with all the "problem-side" vocabulary (`IsRational`, `height`,
`distSubspaces`) assembled from the existing glue:

* `RationalSpan.isRational_span_of_mem_intPoints` — the span of integer vectors is rational;
* `PlaneFinrank.finrank_span_range` — its dimension is `k`;
* `Bridge.distSubspaces_le_planeResidual_of_le` — the challenge distance is at most the
  residual `δ(V,x)`, and the cone condition bounds `δ(V,x) ≤ ε` directly;
* `ModelStarHeight.height_le_span_intPoints` — the height is at most the norm of the wedge of
  the integer family (applied through `norm_iMulti_reindex`).

Consequently `theorem_1`'s first conjunct follows from the lattice Dirichlet statement via
`Submission.conjunct1_of_dirichlet_bound_perX`.

Module `Submission.Work.Dani.StarPairAssembly`, namespace `Submission.DaniStarPair`.
-/

noncomputable section

open Module Real InnerProductGeometry LinearSubspaces ENNReal
open scoped LinearAlgebra.Projectivization ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Submission.DaniStarPair

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℤᵈ" => intPoints

/-- **The ★-pair from the lattice Dirichlet statement.**  For a plane `x` of dimension `l` and
`1 ≤ k ≤ l < d`, the cone-adapted integer family supplied by the hypothesis gives a rational
`k`-plane `v` with `distSubspaces v x ≤ η` and `height v ≤ C η^{−k(d−l)/d}` for every small
`η > 0`. -/
theorem star_pair_of_cone_family {l k : ℕ} (hk1 : 1 ≤ k) (hkl : k ≤ l) (hld : l < d)
    (hcf : ∀ (W : Submodule ℝ ℝᵈ), Module.finrank ℝ W = l →
      ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ b : Fin k → ℝᵈ,
        (∀ i, b i ∈ ℤᵈ) ∧ LinearIndependent ℝ b ∧
        (∀ v ∈ Submodule.span ℝ (Set.range b),
          ‖v - (W.starProjection v : ℝᵈ)‖ ≤ ε * ‖(W.starProjection v : ℝᵈ)‖) ∧
        ‖exteriorPower.ιMulti ℝ k b‖ ≤
          C * ε ^ (-((k : ℝ) * (((d - l : ℕ)) : ℝ)) / (d : ℝ)))
    (x : Submodule ℝ ℝᵈ) (hx : Module.finrank ℝ x = l) :
    ∃ η₀ C : ℝ, 0 < η₀ ∧ 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∃ v : Submodule ℝ ℝᵈ, ∃ hv : IsRational v, Module.finrank ℝ v = k ∧
        distSubspaces v x ≤ η ∧
        height v hv ≤ C * η ^ (-(((k : ℝ) * ((d : ℝ) - (l : ℝ))) / (d : ℝ))) := by
  classical
  have hk0 : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk1
  obtain ⟨C₀, hC₀, hfam⟩ := hcf x hx
  refine ⟨1, C₀, one_pos, hC₀, ?_⟩
  intro η hη hη1
  obtain ⟨b, hbmem, hbLI, hbcone, hbwedge⟩ := hfam η hη hη1
  have hcast : (((d - l) : ℕ) : ℝ) = (d : ℝ) - (l : ℝ) := Nat.cast_sub (le_of_lt hld)
  let V : Submodule ℝ ℝᵈ := Submodule.span ℝ (Set.range b)
  have hVrat : IsRational V :=
    Submission.RationalSpan.isRational_span_of_mem_intPoints (d := d) b hbmem
  have hfin : Module.finrank ℝ V = k := Submission.PlaneFinrank.finrank_span_range b hbLI
  have hVne : V ≠ ⊥ := Submission.PlaneFinrank.span_range_ne_bot (d := d) hk0 b hbLI
  have hxne : x ≠ ⊥ := by
    intro h
    rw [h] at hx
    simp at hx
    omega
  -- the cone condition bounds the plane residual by `η`
  have hres : Submission.ProjectionDistance.planeResidual V x ≤ η := by
    rw [Submission.ProjectionDistance.planeResidual]
    refine csSup_le ?hne ?hle
    · obtain ⟨w, hwV, hw1⟩ := Submission.Bridge.Core.exists_unit_of_ne_bot (E := ℝᵈ) V hVne
      exact ⟨‖w - ((x.orthogonalProjectionOnto w) : ℝᵈ)‖, w, hwV, hw1, rfl⟩
    · rintro r ⟨w, hwV, hw1, rfl⟩
      have hcone := hbcone w (by simpa [V] using hwV)
      have hcoe : ((x.orthogonalProjectionOnto w : ↥x) : ℝᵈ) = x.starProjection w := rfl
      have h1 : ‖w - ((x.orthogonalProjectionOnto w) : ℝᵈ)‖ ≤ η * ‖x.starProjection w‖ := by
        rw [hcoe]; exact hcone
      have h2 : ‖x.starProjection w‖ ≤ 1 := by
        rw [← hw1]; exact x.norm_starProjection_apply_le w
      nlinarith [norm_nonneg w, hη, h1, h2]
  have hfrle : Module.finrank ℝ V ≤ Module.finrank ℝ x :=
    calc Module.finrank ℝ V = k := hfin
      _ ≤ l := hkl
      _ = Module.finrank ℝ x := hx.symm
  have hdist : distSubspaces V x ≤ η :=
    le_trans (Submission.Bridge.distSubspaces_le_planeResidual_of_le V x hfrle hVne hxne) hres
  -- the height is bounded by the wedge of the integer basis
  have hH := Submission.ModelStarHeight.height_le_span_intPoints (d := d) V hVrat
    (m := b) rfl hbmem hbLI
  have hreindex : ‖exteriorPower.ιMulti ℝ (Module.finrank ℝ V)
      (fun i => b (Fin.cast hfin i))‖ = ‖exteriorPower.ιMulti ℝ k b‖ :=
    Submission.DaniPart2.norm_iMulti_reindex hfin b
  rw [hcast] at hbwedge
  refine ⟨V, hVrat, hfin, hdist, ?_⟩
  calc height V hVrat
      ≤ ‖exteriorPower.ιMulti ℝ (Module.finrank ℝ V) (fun i => b (Fin.cast hfin i))‖ := hH
    _ = ‖exteriorPower.ιMulti ℝ k b‖ := hreindex
    _ ≤ C₀ * η ^ (-((k : ℝ) * ((d : ℝ) - (l : ℝ))) / (d : ℝ)) := hbwedge
    _ = C₀ * η ^ (-(((k : ℝ) * ((d : ℝ) - (l : ℝ))) / (d : ℝ))) := by rw [neg_div]

/-- **First conjunct of `theorem_1` from the lattice Dirichlet statement.** -/
theorem conjunct1_of_cone_family (hd : 2 ≤ d) {l k : ℕ} (hl0 : 0 < l) (hld : l < d)
    (hk1 : 1 ≤ k) (hkl : k ≤ l)
    (hcf : ∀ (W : Submodule ℝ ℝᵈ), Module.finrank ℝ W = l →
      ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ b : Fin k → ℝᵈ,
        (∀ i, b i ∈ ℤᵈ) ∧ LinearIndependent ℝ b ∧
        (∀ v ∈ Submodule.span ℝ (Set.range b),
          ‖v - (W.starProjection v : ℝᵈ)‖ ≤ ε * ‖(W.starProjection v : ℝᵈ)‖) ∧
        ‖exteriorPower.ιMulti ℝ k b‖ ≤
          C * ε ^ (-((k : ℝ) * (((d - l : ℕ)) : ℝ)) / (d : ℝ))) :
    ∀ (x : Submodule ℝ ℝᵈ), Module.finrank ℝ x = l →
      diophantineExponent k x ≥ (d : ℝ≥0∞) / (k * (d - l)) :=
  Submission.conjunct1_of_dirichlet_bound_perX hd hl0 hld hk1 hkl
    (fun x hx => star_pair_of_cone_family hk1 hkl hld hcf x hx)

end Submission.DaniStarPair
