import Mathlib

namespace Work.Geo.Radial

open Set Metric

/-- Every continuous map from a compact subset of `ℝᵐ` to `ℝⁿ` is uniformly approximated by a
smooth (`C^∞`) map of the whole space.

The intended fully-qualified name is `Work.Geo.Radial.exists_contDiff_near_of_compact` (file
`Submission/Work/Geo/Radial/exists_contDiff_near_of_compact.lean`). -/
theorem exists_contDiff_near_of_compact {m n : ℕ} {K : Set (EuclideanSpace ℝ (Fin m))}
    (hK : IsCompact K) (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    (hF : ContinuousOn F K) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n),
      ContDiff ℝ ⊤ P ∧ ∀ x ∈ K, dist (P x) (F x) < ε := by
  have hKc : CompactSpace K := isCompact_iff_compactSpace.mp hK
  -- The subalgebra of `C(K, ℝ)` consisting of restrictions to `K` of globally `C^⊤` functions
  -- on `EuclideanSpace ℝ (Fin m)`.
  let A : Subalgebra ℝ C(K, ℝ) :=
    { carrier := {g | ∃ h : EuclideanSpace ℝ (Fin m) → ℝ, ContDiff ℝ ⊤ h ∧ ∀ x : K, g x = h x}
      mul_mem' := by
        rintro a b ⟨ha, hca, hva⟩ ⟨hb, hcb, hvb⟩
        exact ⟨ha * hb, hca.mul hcb, fun x => by simp [ContinuousMap.mul_apply, hva x, hvb x]⟩
      one_mem' := ⟨1, contDiff_const, fun x => rfl⟩
      add_mem' := by
        rintro a b ⟨ha, hca, hva⟩ ⟨hb, hcb, hvb⟩
        exact ⟨ha + hb, hca.add hcb, fun x => by simp [ContinuousMap.add_apply, hva x, hvb x]⟩
      zero_mem' := ⟨0, contDiff_const, fun x => rfl⟩
      algebraMap_mem' := by
        intro r
        exact ⟨fun _ => r, contDiff_const, fun x => rfl⟩ }
  -- `A` separates points (the coordinate functions are `C^⊤`).
  have hA : A.SeparatesPoints := by
    intro x y hxy
    have hne : (x : EuclideanSpace ℝ (Fin m)) ≠ (y : EuclideanSpace ℝ (Fin m)) :=
      fun h => hxy (Subtype.ext h)
    have hne2 : (x : EuclideanSpace ℝ (Fin m)).ofLp ≠ (y : EuclideanSpace ℝ (Fin m)).ofLp :=
      fun h => hne (WithLp.ofLp_injective 2 h)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne2
    have hdiff : ContDiff ℝ ⊤ (fun z : EuclideanSpace ℝ (Fin m) => z.ofLp i) := by
      simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
    let g : C(K, ℝ) := ⟨fun z : K => (z : EuclideanSpace ℝ (Fin m)).ofLp i,
        hdiff.continuous.comp continuous_subtype_val⟩
    have hgA : g ∈ A := ⟨(fun z : EuclideanSpace ℝ (Fin m) => z.ofLp i), hdiff, fun z => rfl⟩
    exact ⟨(g : K → ℝ), ⟨g, hgA, rfl⟩, hi⟩
  -- Stone–Weierstrass coordinatewise.
  have key : ∀ i : Fin n, ∃ h : EuclideanSpace ℝ (Fin m) → ℝ,
      ContDiff ℝ ⊤ h ∧ ∀ x ∈ K, dist (h x) ((F x).ofLp i) < ε / (Real.sqrt (n:ℝ) + 1) := by
    intro i
    have hcont : Continuous (fun x : K => (F x).ofLp i) := by
      have h1 : Continuous (fun z : EuclideanSpace ℝ (Fin n) => z.ofLp i) := by
        simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).continuous
      exact h1.comp hF.domRestrict
    let Fc : C(K, ℝ) := ⟨fun x : K => (F x).ofLp i, hcont⟩
    have hδpos : 0 < ε / (Real.sqrt (n:ℝ) + 1) := by positivity
    obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
        A hA Fc (ε / (Real.sqrt (n:ℝ) + 1)) hδpos
    obtain ⟨h, hdiff, hgh⟩ := g.2
    refine ⟨h, hdiff, fun x hx => ?_⟩
    have h2 : dist (g.1 ⟨x, hx⟩) (Fc ⟨x, hx⟩) ≤ ‖g.1 - Fc‖ := by
      simpa [dist_eq_norm] using ContinuousMap.dist_apply_le_dist (f := g.1) (g := Fc) ⟨x, hx⟩
    have h6 : ‖g.1 - Fc‖ < ε / (Real.sqrt (n:ℝ) + 1) := hg
    have h7 : g.1 ⟨x, hx⟩ = h x := hgh ⟨x, hx⟩
    have h8 : Fc ⟨x, hx⟩ = (F x).ofLp i := rfl
    have h9 := lt_of_le_of_lt h2 h6
    rwa [h7, h8] at h9
  let hfun : Fin n → (EuclideanSpace ℝ (Fin m) → ℝ) := fun i => Classical.choose (key i)
  have hspec : ∀ i, ContDiff ℝ ⊤ (hfun i) ∧
      ∀ x ∈ K, dist (hfun i x) ((F x).ofLp i) < ε / (Real.sqrt (n:ℝ) + 1) :=
    fun i => Classical.choose_spec (key i)
  let P : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) :=
    fun x => WithLp.toLp 2 (fun i => hfun i x)
  refine ⟨P, ?_, ?_⟩
  · apply contDiff_piLp' 2
    intro i
    simpa [P] using (hspec i).1
  · intro x hx
    have hbound : ∀ i : Fin n, dist ((P x).ofLp i) ((F x).ofLp i) <
        ε / (Real.sqrt (n:ℝ) + 1) := by
      intro i
      simpa [P] using (hspec i).2 x hx
    rw [PiLp.dist_eq_of_L2]
    have hsq : (∑ i : Fin n, dist ((P x).ofLp i) ((F x).ofLp i) ^ 2)
        ≤ (n : ℝ) * (ε / (Real.sqrt (n:ℝ) + 1)) ^ 2 := by
      calc (∑ i : Fin n, dist ((P x).ofLp i) ((F x).ofLp i) ^ 2)
          ≤ ∑ _i : Fin n, (ε / (Real.sqrt (n:ℝ) + 1)) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            have hle : dist ((P x).ofLp i) ((F x).ofLp i) ≤ ε / (Real.sqrt (n:ℝ) + 1) :=
              le_of_lt (hbound i)
            have hdn : 0 ≤ dist ((P x).ofLp i) ((F x).ofLp i) := dist_nonneg
            nlinarith [hle, hdn]
        _ = (n : ℝ) * (ε / (Real.sqrt (n:ℝ) + 1)) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsqrt : Real.sqrt ((n : ℝ) * (ε / (Real.sqrt (n:ℝ) + 1)) ^ 2)
        = Real.sqrt (n : ℝ) * (ε / (Real.sqrt (n:ℝ) + 1)) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq]
      positivity
    have hfinal : Real.sqrt (n:ℝ) * (ε / (Real.sqrt (n:ℝ) + 1)) < ε := by
      have hden : 0 < Real.sqrt (n:ℝ) + 1 := by positivity
      have hr : Real.sqrt (n:ℝ) / (Real.sqrt (n:ℝ) + 1) < 1 := by
        rw [div_lt_one hden]
        linarith [Real.sqrt_nonneg (n:ℝ)]
      calc Real.sqrt (n:ℝ) * (ε / (Real.sqrt (n:ℝ) + 1))
          = ε * (Real.sqrt (n:ℝ) / (Real.sqrt (n:ℝ) + 1)) := by ring
        _ < ε * 1 := mul_lt_mul_of_pos_left hr hε
        _ = ε := by ring
    have h2 : Real.sqrt (∑ i : Fin n, dist ((P x).ofLp i) ((F x).ofLp i) ^ 2)
        ≤ Real.sqrt (n:ℝ) * (ε / (Real.sqrt (n:ℝ) + 1)) := by
      rw [← hsqrt]
      exact Real.sqrt_le_sqrt hsq
    exact lt_of_le_of_lt h2 hfinal

end Work.Geo.Radial
