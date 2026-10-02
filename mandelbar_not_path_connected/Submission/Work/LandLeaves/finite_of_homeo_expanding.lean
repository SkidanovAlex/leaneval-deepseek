import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.LandLeaves

open Set

/-- If a homeomorphism `g` of a compact metric space is `λ`-Lipschitz and *exactly* expands
distances by the factor `λ > 1` whenever they are `< η`, then the space is finite.

Proof sketch.  Since `X` is compact, `g⁻¹` is uniformly continuous: there is `δ > 0` with
`dist a b < δ → dist (g⁻¹ a) (g⁻¹ b) < η`, hence (contrapositive) two points at distance `≥ η`
have `g`-images at distance `≥ δ`.  Consequently, whenever a set `W` has all pairwise distances
`≤ R < δ`, the set `g⁻¹ '' W` has all pairwise distances `≤ R/λ`: for `u, v ∈ g⁻¹ '' W`
the points `gu, gv` are `< δ` apart, so they cannot be `≥ η` apart, and then the exact
expansion applies.

A finite covering of the compact space by sets of pairwise distance `≤ δ/2` (given by total
boundedness) can therefore be shrunk by `g⁻¹` any number of times, always with the same number
of sets, and the diameters tend to `0`.  If the space had `m+2` distinct points, pigeonholing
them into the `m` smallest sets would exhibit two of them at distance `< R_k` for arbitrarily
small `R_k`, forcing two of them to coincide.  Hence the space has at most `m+1` points. -/
theorem finite_of_homeo_expanding {X : Type*} [MetricSpace X] [CompactSpace X]
    (g : X ≃ₜ X) {lam eta : ℝ} (hlam : 1 < lam) (heta : 0 < eta)
    (hlip : ∀ a b, dist (g a) (g b) ≤ lam * dist a b)
    (hexp : ∀ a b, dist a b < eta → dist (g a) (g b) = lam * dist a b) :
    Finite X := by
  have hlam0 : 0 < lam := lt_trans zero_lt_one hlam
  have hlam1 : 0 < 1 / lam := by positivity
  have hlt1 : 1 / lam < 1 := by rw [div_lt_one hlam0]; exact hlam
  -- uniform continuity of `g⁻¹`
  have hu : UniformContinuous (g.symm : X → X) :=
    CompactSpace.uniformContinuous_of_continuous g.symm.continuous
  rw [Metric.uniformContinuous_iff] at hu
  obtain ⟨δ, hδpos, hδ⟩ := hu eta heta
  -- contraction identity for `g⁻¹` on pairs closer than `δ`
  have hcontr : ∀ p q : X, dist p q < δ →
      dist (g.symm p) (g.symm q) = dist p q / lam := by
    intro p q hpq
    have h1 : dist (g.symm p) (g.symm q) < eta := hδ hpq
    have h2 := hexp (g.symm p) (g.symm q) h1
    rw [g.apply_symm_apply, g.apply_symm_apply] at h2
    rw [eq_div_iff (ne_of_gt hlam0), h2]
    ring
  -- total boundedness: a finite cover by balls of radius `δ/4`
  have hTB : TotallyBounded (univ : Set X) := isCompact_univ.totallyBounded
  rw [Metric.totallyBounded_iff] at hTB
  obtain ⟨t, htfin, ht⟩ := hTB (δ / 4) (by linarith)
  haveI : Fintype t := htfin.fintype
  let c : t → Set X := fun y => Metric.ball (y : X) (δ / 4)
  have hcov0 : univ ⊆ ⋃ y, c y := by
    intro x hx
    have hxt : x ∈ ⋃ y ∈ t, Metric.ball y (δ / 4) := ht hx
    simp only [Set.mem_iUnion] at hxt
    obtain ⟨y, hyt, hxy⟩ := hxt
    exact Set.mem_iUnion.mpr ⟨⟨y, hyt⟩, hxy⟩
  have hcdiam : ∀ y : t, ∀ u ∈ c y, ∀ v ∈ c y, dist u v ≤ δ / 2 := by
    intro y u hu v hv
    change u ∈ Metric.ball (y : X) (δ / 4) at hu
    change v ∈ Metric.ball (y : X) (δ / 4) at hv
    rw [Metric.mem_ball] at hu hv
    rw [dist_comm v (y : X)] at hv
    linarith [dist_triangle u (y : X) v, hu, hv]
  -- the shrinking covers
  let cov : ℕ → t → Set X := fun k => Nat.rec c (fun _ cs y => g.symm '' cs y) k
  have hcov0def : cov 0 = c := rfl
  let R : ℕ → ℝ := fun k => (δ / 2) * (1 / lam) ^ k
  have hRdef : ∀ k, R k = (δ / 2) * (1 / lam) ^ k := fun k => rfl
  have hRδ : ∀ k, R k < δ := by
    intro k
    have h1 : (1 / lam) ^ k ≤ 1 := pow_le_one₀ hlam1.le hlt1.le
    have h2 : R k ≤ δ / 2 := by rw [hRdef k]; nlinarith [h1, hδpos]
    linarith
  have hshrink : ∀ (W : Set X) (r : ℝ), r < δ →
      (∀ u ∈ W, ∀ v ∈ W, dist u v ≤ r) →
      (∀ u ∈ g.symm '' W, ∀ v ∈ g.symm '' W, dist u v ≤ r / lam) := by
    rintro W r hr hW u ⟨u', hu', rfl⟩ v ⟨v', hv', rfl⟩
    rw [hcontr u' v' (lt_of_le_of_lt (hW u' hu' v' hv') hr)]
    exact div_le_div_of_nonneg_right (hW u' hu' v' hv') hlam0.le
  have hcov : ∀ k, univ ⊆ ⋃ y, cov k y := by
    intro k
    induction k with
    | zero => exact hcov0
    | succ k ih =>
        intro x hx
        obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (ih (mem_univ (g x)))
        exact Set.mem_iUnion.mpr ⟨y, ⟨g x, hy, g.symm_apply_apply x⟩⟩
  have hcovdiam : ∀ k y, ∀ u ∈ cov k y, ∀ v ∈ cov k y, dist u v ≤ R k := by
    intro k
    induction k with
    | zero =>
        intro y u hu v hv
        have h := hcdiam y u hu v hv
        have hR0 : R 0 = δ / 2 := by rw [hRdef 0]; ring
        rw [hR0]; exact h
    | succ k ih =>
        intro y u hu v hv
        have h := hshrink (cov k y) (R k) (hRδ k) (ih y) u hu v hv
        have hRk : R (k + 1) = R k / lam := by
          rw [hRdef (k + 1), hRdef k, pow_succ]; ring
        rw [hRk]; exact h
  -- suppose `X` were infinite: pick `Fintype.card t + 2` distinct points
  by_contra hfin
  haveI : Infinite X := ⟨hfin⟩
  obtain ⟨S, -, hScard⟩ :=
    Infinite.exists_superset_card_eq (∅ : Finset X) (Fintype.card t + 2) (by simp)
  let x : Fin (Fintype.card t + 2) → X :=
    fun i => ((S.equivFin.symm (Fin.cast hScard.symm i) : S) : X)
  have hx : Function.Injective x := by
    intro i j hij
    have h1 : (S.equivFin.symm (Fin.cast hScard.symm i) : S) =
        (S.equivFin.symm (Fin.cast hScard.symm j) : S) := Subtype.ext hij
    exact Fin.cast_injective hScard.symm (S.equivFin.symm.injective h1)
  -- the minimal distance among the chosen points
  let P := {p : Fin (Fintype.card t + 2) × Fin (Fintype.card t + 2) // p.1 ≠ p.2}
  have hPne : (Finset.univ : Finset P).Nonempty := by
    refine ⟨⟨(0, 1), ?_⟩, Finset.mem_univ _⟩
    simp
  obtain ⟨p0, -, hp0⟩ := Finset.exists_min_image (Finset.univ : Finset P)
    (fun p : P => dist (x p.1.1) (x p.1.2)) hPne
  have hρpos : 0 < dist (x p0.1.1) (x p0.1.2) := by
    rw [dist_pos]; intro h; exact p0.2 (hx h)
  -- choose a cover finer than that minimal distance
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
    (x := dist (x p0.1.1) (x p0.1.2) / (δ / 2)) (y := 1 / lam) (by positivity) hlt1
  have hk' : R k < dist (x p0.1.1) (x p0.1.2) := by
    have h2 := mul_lt_mul_of_pos_left hk (by linarith : (0:ℝ) < δ / 2)
    rw [mul_div_cancel₀ _ (by linarith : (δ/2) ≠ 0)] at h2
    exact h2
  have hidx : ∀ a : Fin (Fintype.card t + 2), ∃ y : t, x a ∈ cov k y := fun a =>
    Set.mem_iUnion.mp (hcov k (mem_univ _))
  choose idx hidxmem using hidx
  have hcardlt : Fintype.card t < Fintype.card (Fin (Fintype.card t + 2)) := by simp
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt idx hcardlt
  have hle : dist (x a) (x b) ≤ R k := by
    have ha := hidxmem a
    have hb := hidxmem b
    rw [← heq] at hb
    exact hcovdiam k (idx a) (x a) ha (x b) hb
  exact absurd hle
    (not_le.mpr (lt_of_lt_of_le hk' (hp0 ⟨(a, b), hab⟩ (Finset.mem_univ _))))

end Work.LandLeaves
