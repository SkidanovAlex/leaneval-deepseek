import Mathlib

-- The hypothesis `hFfin` is part of the requested statement but turns out not to be
-- needed by the argument; silence the unused-variable linter for this file.
set_option linter.unusedVariables false

/-!
# Compactness of the preimage of the composite `φ ∘ f` away from the value `φ v`

Let `B ⊆ ℂ`, `f : ℂ → ℂ` with `f '' B ⊆ B` and such that `f` is *proper* on `B`
(preimages of compact subsets of `B` are compact, hypothesis `hproper`), and let
`φ : ℂ → ℂ` restrict to a homeomorphism `H : ↥B ≃ₜ 𝔻` of `B` onto the unit disc.
Then, for a compact `K ⊆ 𝔻` with `φ v ∉ K`, the set of points of
`B \ (B ∩ f ⁻¹' {v})` whose image under `φ ∘ f` lands in `K` is compact.

The point of removing the fibre of `v` is that `v` itself is *not* a value of `φ`
on `K` (i.e. `v` lies outside the compact piece
`T := {z ∈ B : φ z ∈ K}`), so no preimage of `v` under `f` can map into `T`.
Hence the preimage we are after is exactly `f ⁻¹' T` intersected with `B`, and
`T` being compact and `f` proper gives the result.

The auxiliary lemmas below are the two independent steps of the argument:
* `mem_image_homeomorph_unitBall_iff` identifies, inside `B`, the set where `φ`
  takes values in `K` with the image of `K` under `H.symm` (so that it *is*
  compact, as an image of `K`);
* `isCompact_preimage_of_isCompact_subset` is the purely topological step:
  for `T ⊆ B` compact with `v ∉ T`, the set
  `{z ∈ B \ (B ∩ f ⁻¹' {v}) : f z ∈ T}` is compact.
-/

namespace Work.HornSeq

/-- Inside `B`, `φ` takes its values in `K` exactly on the image of `K` under the
inverse of the uniformizing homeomorphism `H` (coerced back into `ℂ`). -/
lemma mem_image_homeomorph_unitBall_iff {B : Set ℂ} {φ : ℂ → ℂ}
    (H : ↥B ≃ₜ ↥(Metric.ball (0 : ℂ) 1)) (hH : ∀ z : ↥B, (H z : ℂ) = φ z) (K : Set ℂ)
    {z : ↥B} :
    φ z ∈ K ↔
      ((z : ℂ) ∈ ((fun x : ↥B => (x : ℂ)) ''
        (H.symm '' ((fun w : ↥(Metric.ball (0 : ℂ) 1) => (w : ℂ)) ⁻¹' K)))) := by
  constructor
  · intro hz
    refine ⟨H.symm (H z), ⟨H z, ?_, rfl⟩, ?_⟩
    · show (H z : ℂ) ∈ K
      rw [hH z]; exact hz
    · show ((H.symm (H z) : ↥B) : ℂ) = ((z : ↥B) : ℂ)
      rw [H.symm_apply_apply]
  · rintro ⟨y, ⟨u, hu, hy⟩, hyz⟩
    -- `u ∈ 𝔻` with `(u : ℂ) ∈ K`, and `y = H.symm u = z`
    have hzu : (H z : ℂ) = (u : ℂ) := by
      rw [show z = y from (Subtype.ext hyz).symm, ← hy]
      exact congrArg Subtype.val (H.apply_symm_apply u)
    rw [← hH z, hzu]
    show (u : ℂ) ∈ K
    exact hu

/-- Purely topological step: if `T ⊆ B` is compact and `v ∉ T`, then the set of
points of `B` outside the fibre `f ⁻¹' {v}` that are mapped by `f` into `T` is
compact (in the subspace `B \ (B ∩ f ⁻¹' {v})`), as soon as `f` is proper on `B`. -/
lemma isCompact_preimage_of_isCompact_subset {B : Set ℂ} {f : ℂ → ℂ} {v : ℂ}
    (hproper : ∀ L ⊆ B, IsCompact L → IsCompact (B ∩ f ⁻¹' L))
    {T : Set ℂ} (hTB : T ⊆ B) (hT : IsCompact T) (hvT : v ∉ T) :
    IsCompact ((fun z : ↥(B \ (B ∩ f ⁻¹' {v})) => f z.1) ⁻¹' T) := by
  rw [Subtype.isCompact_iff]
  -- the coerced image of the preimage is `B ∩ f ⁻¹' T`
  have hset : ((↑) '' ((fun z : ↥(B \ (B ∩ f ⁻¹' {v})) => f z.1) ⁻¹' T) : Set ℂ)
      = B ∩ f ⁻¹' T := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2.1, hz⟩
    · rintro ⟨hxB, hxT⟩
      -- such an `x` is not in the fibre of `v`
      have hne : x ∉ B ∩ f ⁻¹' {v} := by
        rintro ⟨-, hxv⟩
        have : v ∈ T := by rw [← hxv]; exact hxT
        exact hvT this
      exact ⟨⟨x, hxB, hne⟩, hxT, rfl⟩
  rw [hset]
  exact hproper T hTB hT

/-- The preimage of a compact `K ⊆ 𝔻` under `φ ∘ f`, restricted to `B` minus the
fibre of `v` (with `φ v ∉ K`), is compact. -/
theorem isCompact_preimage_phi_comp_of_notMem {B : Set ℂ} {f φ : ℂ → ℂ} {v : ℂ}
    (hmap : Set.MapsTo f B B)
    (hproper : ∀ L ⊆ B, IsCompact L → IsCompact (B ∩ f ⁻¹' L))
    (hFfin : (B ∩ f ⁻¹' {v}).Finite)
    (H : ↥B ≃ₜ ↥(Metric.ball (0 : ℂ) 1)) (hH : ∀ z : ↥B, (H z : ℂ) = φ z)
    {K : Set ℂ} (hK : IsCompact K) (hKball : K ⊆ Metric.ball (0 : ℂ) 1)
    (hvK : φ v ∉ K) :
    IsCompact ((fun z : ↥(B \ (B ∩ f ⁻¹' {v})) => φ (f z.1)) ⁻¹' K) := by
  -- the compact piece of `B` on which `φ` takes values in `K`
  let T : Set ℂ := (fun x : ↥B => (x : ℂ)) ''
    (H.symm '' ((fun w : ↥(Metric.ball (0 : ℂ) 1) => (w : ℂ)) ⁻¹' K))
  have hTchar : ∀ z : ↥B, φ z ∈ K ↔ (z : ℂ) ∈ T :=
    fun z => mem_image_homeomorph_unitBall_iff H hH K
  -- `T` is compact, being the image of `K ⊆ 𝔻` under `H.symm`
  have hK₁ : IsCompact ((fun w : ↥(Metric.ball (0 : ℂ) 1) => (w : ℂ)) ⁻¹' K) := by
    rw [Subtype.isCompact_iff]
    have hset : ((↑) '' ((fun w : ↥(Metric.ball (0 : ℂ) 1) => (w : ℂ)) ⁻¹' K) : Set ℂ)
        = K := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hx
        exact ⟨⟨x, hKball hx⟩, hx, rfl⟩
    rw [hset]
    exact hK
  have hT : IsCompact T := (hK₁.image H.symm.continuous).image continuous_subtype_val
  have hTB : T ⊆ B := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  -- `v ∉ T` because `φ v ∉ K`
  have hvT : v ∉ T := by
    intro hv
    exact hvK ((hTchar ⟨v, hTB hv⟩).mpr hv)
  have hmain := isCompact_preimage_of_isCompact_subset (f := f) (v := v) hproper hTB hT hvT
  -- replace `f ⁻¹' T` by `(φ ∘ f) ⁻¹' K`, using `f '' B ⊆ B`
  have hset2 : ((fun z : ↥(B \ (B ∩ f ⁻¹' {v})) => φ (f z.1)) ⁻¹' K)
      = ((fun z : ↥(B \ (B ∩ f ⁻¹' {v})) => f z.1) ⁻¹' T) := by
    ext z
    exact hTchar ⟨f z.1, hmap z.2.1⟩
  rw [hset2]
  exact hmain

end Work.HornSeq
