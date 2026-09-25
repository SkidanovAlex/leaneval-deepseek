import Mathlib

namespace Work.CFT.Kummer

/-- If `loc : M → ∏ᵢ Nᵢ` lands in the kernel of the "sum of invariants" functional
`y ↦ ∑ᵢ invᵢ (yᵢ)`, where each `Nᵢ` is a `ZMod p`-module of dimension `≤ 1` whose invariant
`invᵢ` is nonzero whenever the dimension is `1`, then the range of `loc` has dimension at most
`card ι - 1`. -/
theorem finrank_range_le_of_sum_invariants {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
    {M : Type*} [AddCommGroup M] [Module (ZMod p) M] {N : ι → Type*}
    [∀ i, AddCommGroup (N i)] [∀ i, Module (ZMod p) (N i)] [∀ i, Module.Finite (ZMod p) (N i)]
    (loc : M →ₗ[ZMod p] ((i : ι) → N i)) (inv : (i : ι) → N i →ₗ[ZMod p] ZMod p)
    (h1 : ∀ i, Module.finrank (ZMod p) (N i) ≤ 1)
    (h2 : ∀ i, Module.finrank (ZMod p) (N i) = 1 → inv i ≠ 0)
    (hrec : ∀ x, (∑ i, inv i (loc x i)) = 0) :
    Module.finrank (ZMod p) (LinearMap.range loc) ≤ Fintype.card ι - 1 := by
  classical
  -- The "sum of invariants" functional on the product.
  let φ : ((i : ι) → N i) →ₗ[ZMod p] ZMod p := ∑ i, (inv i).comp (LinearMap.proj i)
  have hφdef : φ = ∑ i, (inv i).comp (LinearMap.proj i) := rfl
  have hφ_apply : ∀ y : ((i : ι) → N i), φ y = ∑ i, inv i (y i) := fun y => by
    simp [hφdef, LinearMap.sum_apply]
  -- Evaluating `φ` on an element supported at a single coordinate.
  have hsingle : ∀ (j : ι) (x : N j), φ (Pi.single j x) = inv j x := by
    intro j x
    rw [hφ_apply, Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      simp [Pi.single_eq_of_ne hi]
    · intro h
      simp at h
  -- The range of `loc` lies in the kernel of `φ`.
  have hrange : LinearMap.range loc ≤ LinearMap.ker φ := by
    rw [LinearMap.range_le_ker_iff]
    ext x
    simp [hφ_apply, hrec]
  -- The product has dimension `∑ᵢ finrank (N i) ≤ card ι`.
  have hV : Module.finrank (ZMod p) ((i : ι) → N i) ≤ Fintype.card ι := by
    rw [Module.finrank_pi_fintype]
    calc (∑ i, Module.finrank (ZMod p) (N i)) ≤ ∑ _i : ι, 1 := Finset.sum_le_sum fun i _ => h1 i
      _ = Fintype.card ι := by simp
  by_cases hA : ∃ j, Module.finrank (ZMod p) (N j) = 1
  · -- Some factor is one-dimensional: `φ` is nonzero, hence has rank one.
    obtain ⟨j, hj⟩ := hA
    have hinv : inv j ≠ 0 := h2 j hj
    rw [ne_eq, LinearMap.ext_iff] at hinv
    push Not at hinv
    obtain ⟨x, hx⟩ := hinv
    have hx' : inv j x ≠ 0 := by simpa using hx
    have hφx : φ (Pi.single j x) ≠ 0 := by rwa [hsingle]
    have hr : LinearMap.range φ ≠ ⊥ := by
      rw [ne_eq, LinearMap.range_eq_bot]
      intro h
      apply hφx
      rw [h]
      simp
    have hpos : 1 ≤ Module.finrank (ZMod p) (LinearMap.range φ) :=
      Submodule.one_le_finrank_iff.mpr hr
    -- Rank-nullity: `finrank (ker φ) = finrank V - finrank (range φ)`.
    have hRN := LinearMap.finrank_range_add_finrank_ker φ
    have hker : Module.finrank (ZMod p) (LinearMap.ker φ) =
        Module.finrank (ZMod p) ((i : ι) → N i) -
          Module.finrank (ZMod p) (LinearMap.range φ) := by
      have h := hRN
      rw [add_comm] at h
      exact Nat.eq_sub_of_add_eq h
    calc Module.finrank (ZMod p) (LinearMap.range loc)
        ≤ Module.finrank (ZMod p) (LinearMap.ker φ) := Submodule.finrank_mono hrange
      _ = Module.finrank (ZMod p) ((i : ι) → N i) -
            Module.finrank (ZMod p) (LinearMap.range φ) := hker
      _ ≤ Module.finrank (ZMod p) ((i : ι) → N i) - 1 := Nat.sub_le_sub_left hpos _
      _ ≤ Fintype.card ι - 1 := Nat.sub_le_sub_right hV 1
  · -- All factors are zero-dimensional: the whole product is zero.
    push Not at hA
    have h0 : ∀ i, Module.finrank (ZMod p) (N i) = 0 := fun i => by
      have ha := h1 i
      have hb := hA i
      omega
    have hV0 : Module.finrank (ZMod p) ((i : ι) → N i) = 0 := by
      rw [Module.finrank_pi_fintype]
      simp [h0]
    calc Module.finrank (ZMod p) (LinearMap.range loc)
        ≤ Module.finrank (ZMod p) ((i : ι) → N i) := Submodule.finrank_le _
      _ = 0 := hV0
      _ ≤ Fintype.card ι - 1 := Nat.zero_le _

end Work.CFT.Kummer
