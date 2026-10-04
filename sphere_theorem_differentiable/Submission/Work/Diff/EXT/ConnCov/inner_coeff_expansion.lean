import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov

theorem inner_coeff_expansion
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (e : Fin (Module.finrank ℝ V) → V)
    (he : Submodule.span ℝ (Set.range e) = ⊤) :
    ∀ q : V, q = ∑ i, (∑ j,
        (Matrix.of (fun i j => inner ℝ (e i) (e j)))⁻¹ i j * inner ℝ (e j) q) • e i := by
  -- `e` is a spanning family of `finrank ℝ V` vectors, hence a basis, so the Gram matrix `G`
  -- of `e` is positive definite and invertible.  Writing `c = G⁻¹ *ᵥ b` with `bⱼ = ⟪eⱼ, q⟫`,
  -- we get `⟪∑ᵢ cᵢ • eᵢ, eₖ⟫ = (G *ᵥ c)ₖ = bₖ = ⟪eₖ, q⟫`; since the `eₖ` span `V`, this forces
  -- `∑ᵢ cᵢ • eᵢ = q`.
  classical
  have hcard : Fintype.card (Fin (Module.finrank ℝ V)) = Module.finrank ℝ V := Fintype.card_fin _
  have hli : LinearIndependent ℝ e :=
    linearIndependent_of_top_le_span_of_card_eq_finrank he.ge hcard
  set G : Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ :=
    Matrix.of (fun i j => inner ℝ (e i) (e j)) with hGdef
  have hGapply : ∀ i j, G i j = inner ℝ (e i) (e j) := by
    intro i j; rw [hGdef, Matrix.of_apply]
  have hGram : G = Matrix.gram ℝ e := by
    rw [hGdef]; rfl
  have hpd : G.PosDef := hGram.symm ▸ Matrix.posDef_gram_of_linearIndependent hli
  have hunit : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hpd.isUnit
  have hmul : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hunit
  intro q
  have hkey : (∑ i, (∑ j, G⁻¹ i j * inner ℝ (e j) q) • e i) = q := by
    set S := ∑ i, (∑ j, G⁻¹ i j * inner ℝ (e j) q) • e i with hSdef
    -- the two key facts: `⟪S, eₖ⟫ = (G *ᵥ c)ₖ` and `G *ᵥ c = b`
    have hk : ∀ k, inner ℝ S (e k) = inner ℝ q (e k) := by
      intro k
      have h1 : inner ℝ S (e k) = ∑ i, (∑ j, G⁻¹ i j * inner ℝ (e j) q) * G i k := by
        rw [hSdef]
        rw [sum_inner]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [real_inner_smul_left, hGapply i k]
      have hval : ∑ i, G k i * (∑ j, G⁻¹ i j * inner ℝ (e j) q) = inner ℝ (e k) q := by
        have hGc : Matrix.mulVec G (fun i => ∑ j, G⁻¹ i j * inner ℝ (e j) q)
            = fun j => inner ℝ (e j) q := by
          have hc : (fun i => ∑ j, G⁻¹ i j * inner ℝ (e j) q)
              = Matrix.mulVec G⁻¹ (fun j => inner ℝ (e j) q) := rfl
          rw [hc, Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
        have h1' := congrFun hGc k
        simpa [Matrix.mulVec, dotProduct] using h1'
      have h2 : ∑ i, (∑ j, G⁻¹ i j * inner ℝ (e j) q) * G i k = inner ℝ (e k) q := by
        rw [show (∑ i, (∑ j, G⁻¹ i j * inner ℝ (e j) q) * G i k)
            = ∑ i, (∑ j, G⁻¹ i j * inner ℝ (e j) q) * G k i from by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [hGapply i k, hGapply k i, real_inner_comm (e i) (e k)]]
        rw [show (∑ i, (∑ j, G⁻¹ i j * inner ℝ (e j) q) * G k i)
            = ∑ i, G k i * (∑ j, G⁻¹ i j * inner ℝ (e j) q) from by
              refine Finset.sum_congr rfl fun i _ => mul_comm _ _]
        exact hval
      rw [h1, h2]
      exact (real_inner_comm (e k) q).symm
    -- `S - q` is orthogonal to the span of `e`, i.e. to all of `V`, hence is `0`
    have hxz : ∀ z ∈ Submodule.span ℝ (Set.range e), inner ℝ (S - q) z = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem w hw =>
          obtain ⟨k, rfl⟩ := hw
          rw [inner_sub_left, hk k, sub_self]
      | zero => simp
      | add u v hu hv ihu ihv => rw [inner_add_right, ihu, ihv, add_zero]
      | smul a u hu ihu => rw [real_inner_smul_right, ihu, mul_zero]
    have hxm : S - q = 0 := by
      have hmem : S - q ∈ Submodule.span ℝ (Set.range e) := by rw [he]; trivial
      have h := hxz _ hmem
      rwa [inner_self_eq_zero] at h
    exact sub_eq_zero.mp hxm
  exact hkey.symm

end Work.Diff.EXT.ConnCov
