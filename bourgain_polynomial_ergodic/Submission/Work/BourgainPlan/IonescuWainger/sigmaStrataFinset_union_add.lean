import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.StrataFinsetDefs
import Submission.Work.BourgainPlan.IonescuWainger.opArc_l2_endpoint_strata

namespace Work.BourgainPlan.IonescuWainger

open Finset
open scoped BigOperators

set_option autoImplicit false

/-- **Surjectivity of the addition map on the strata.**  If `A₀, B ⊆ S` are disjoint subsets of a
pairwise coprime set `S` of integers `≥ 2`, then every point `x` of the stratum `Σ_{A₀ ∪ B}`
splits as `x = γ + α` with `γ ∈ Σ_{A₀}` and `α ∈ Σ_B`.

This is the Chinese-remainder decomposition of the strata at the level of the circle: with a Bézout
pair `u Q_{A₀} + v Q_B = 1` one takes `γ = v Q_B · x` and `α = u Q_{A₀} · x`.  The stratum conditions
are preserved because a proper subset `C ⊊ B` killing `α` would force `Q_C · α = 0` and (using
`x = γ + α`) `Q_{A₀ ∪ C} · x = Q_{A₀} · (Q_C · α) + Q_C · (Q_{A₀} · γ) = 0`, i.e. `x ∈ 𝕋[Q_{A₀ ∪ C}]`
with `A₀ ∪ C ⊊ A₀ ∪ B`, contradicting `x ∈ Σ_{A₀ ∪ B}`
(`not_mem_sigmaStrataFinset_of_mem_sigmaSubAFinset`); symmetrically for a proper `C ⊊ A₀` killing
`γ`. -/
lemma exists_decomp_mem_sigmaStrataFinset {S A₀ B : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA₀ : A₀ ⊆ S) (hB : B ⊆ S) (hdisj : Disjoint A₀ B)
    {x : Circle} (hx : x ∈ sigmaStrataFinset (A₀ ∪ B)) :
    ∃ γ ∈ sigmaStrataFinset A₀, ∃ α ∈ sigmaStrataFinset B, γ + α = x := by
  have hUsub : A₀ ∪ B ⊆ S := Finset.union_subset hA₀ hB
  have h2A₀ : ∀ q ∈ A₀, 2 ≤ q := fun q hq => h2 q (hA₀ hq)
  have h2B : ∀ q ∈ B, 2 ≤ q := fun q hq => h2 q (hB hq)
  have h2U : ∀ q ∈ A₀ ∪ B, 2 ≤ q := fun q hq => h2 q (hUsub hq)
  have hcross : ∀ p ∈ A₀, ∀ q ∈ B, Nat.Coprime p q := fun p hp q hq =>
    hS p (hA₀ hp) q (hB hq) (fun he => Finset.disjoint_left.mp hdisj hp (he ▸ hq))
  have hcop : Nat.Coprime (QA A₀) (QA B) := coprime_QA_of_disjoint hcross
  obtain ⟨u, v, huv⟩ := hcop.isCoprime
  have hxsub : x ∈ sigmaSubAFinset (A₀ ∪ B) := (mem_sigmaStrataFinset.mp hx).1
  have hxU : (QA (A₀ ∪ B) : ℤ) • x = 0 :=
    (mem_sigmaSubAFinset_iff_zsmul_eq_zero h2U x).mp hxsub
  have hQAcast : (QA (A₀ ∪ B) : ℤ) = (QA A₀ : ℤ) * (QA B : ℤ) := by
    rw [QA_union hdisj]; push_cast; ring
  -- the Bézout projections `γ ∈ Σ_{A₀}` and `α ∈ Σ_B`
  set α : Circle := (u * (QA A₀ : ℤ)) • x with hαdef
  set γ : Circle := (v * (QA B : ℤ)) • x with hγdef
  have hsum : γ + α = x := by
    rw [hγdef, hαdef, ← add_zsmul]
    rw [show v * (QA B : ℤ) + u * (QA A₀ : ℤ) = 1 by linarith]
    exact one_zsmul x
  have hαB : (QA B : ℤ) • α = 0 := by
    rw [hαdef, ← mul_zsmul,
      show (QA B : ℤ) * (u * (QA A₀ : ℤ)) = u * ((QA A₀ : ℤ) * (QA B : ℤ)) by ring,
      mul_zsmul, ← hQAcast, hxU, smul_zero]
  have hγA₀ : (QA A₀ : ℤ) • γ = 0 := by
    rw [hγdef, ← mul_zsmul,
      show (QA A₀ : ℤ) * (v * (QA B : ℤ)) = v * ((QA A₀ : ℤ) * (QA B : ℤ)) by ring,
      mul_zsmul, ← hQAcast, hxU, smul_zero]
  have hαstrata : α ∈ sigmaStrataFinset B := by
    rw [mem_sigmaStrataFinset]
    refine ⟨(mem_sigmaSubAFinset_iff_zsmul_eq_zero h2B α).mpr hαB, ?_⟩
    intro C hC hαC
    rw [Finset.mem_erase, Finset.mem_powerset] at hC
    obtain ⟨hCne, hCsub⟩ := hC
    have h2C : ∀ q ∈ C, 2 ≤ q := fun q hq => h2B q (hCsub hq)
    have hαCz : (QA C : ℤ) • α = 0 := (mem_sigmaSubAFinset_iff_zsmul_eq_zero h2C α).mp hαC
    have hACsub : A₀ ∪ C ⊆ S := Finset.union_subset hA₀ (hCsub.trans hB)
    have h2AC : ∀ q ∈ A₀ ∪ C, 2 ≤ q := fun q hq => h2 q (hACsub hq)
    have hdisjC : Disjoint A₀ C := Disjoint.mono_right hCsub hdisj
    have hxC : (QA (A₀ ∪ C) : ℤ) • x = 0 := by
      have hQC : (QA (A₀ ∪ C) : ℤ) = (QA A₀ : ℤ) * (QA C : ℤ) := by
        rw [QA_union hdisjC]; push_cast; ring
      rw [show x = γ + α from hsum.symm, smul_add, hQC]
      rw [show ((QA A₀ : ℤ) * (QA C : ℤ)) • γ = (QA C : ℤ) • ((QA A₀ : ℤ) • γ) by
            rw [mul_comm, mul_zsmul], hγA₀, smul_zero]
      rw [show ((QA A₀ : ℤ) * (QA C : ℤ)) • α = (QA A₀ : ℤ) • ((QA C : ℤ) • α) by
            rw [mul_zsmul], hαCz, smul_zero]
      rw [zero_add]
    have hxsubC : x ∈ sigmaSubAFinset (A₀ ∪ C) :=
      (mem_sigmaSubAFinset_iff_zsmul_eq_zero h2AC x).mpr hxC
    have hsubAC : A₀ ∪ C ⊆ A₀ ∪ B := Finset.union_subset_union_right hCsub
    have hneAC : A₀ ∪ C ≠ A₀ ∪ B := by
      intro heq
      refine hCne (Finset.Subset.antisymm hCsub ?_)
      intro q hq
      have hmem : q ∈ A₀ ∪ C := by rw [heq]; exact Finset.mem_union_right A₀ hq
      rcases Finset.mem_union.mp hmem with h | h
      · exact absurd hq (Finset.disjoint_left.mp hdisj h)
      · exact h
    exact not_mem_sigmaStrataFinset_of_mem_sigmaSubAFinset hsubAC hneAC hxsubC hx
  have hγstrata : γ ∈ sigmaStrataFinset A₀ := by
    rw [mem_sigmaStrataFinset]
    refine ⟨(mem_sigmaSubAFinset_iff_zsmul_eq_zero h2A₀ γ).mpr hγA₀, ?_⟩
    intro C hC hγC
    rw [Finset.mem_erase, Finset.mem_powerset] at hC
    obtain ⟨hCne, hCsub⟩ := hC
    have h2C : ∀ q ∈ C, 2 ≤ q := fun q hq => h2A₀ q (hCsub hq)
    have hγCz : (QA C : ℤ) • γ = 0 := (mem_sigmaSubAFinset_iff_zsmul_eq_zero h2C γ).mp hγC
    have hCBsub : C ∪ B ⊆ S := Finset.union_subset (hCsub.trans hA₀) hB
    have h2CB : ∀ q ∈ C ∪ B, 2 ≤ q := fun q hq => h2 q (hCBsub hq)
    have hdisjCB : Disjoint C B := Disjoint.mono_left hCsub hdisj
    have hxC : (QA (C ∪ B) : ℤ) • x = 0 := by
      have hQC : (QA (C ∪ B) : ℤ) = (QA C : ℤ) * (QA B : ℤ) := by
        rw [QA_union hdisjCB]; push_cast; ring
      rw [show x = γ + α from hsum.symm, smul_add, hQC]
      rw [show ((QA C : ℤ) * (QA B : ℤ)) • γ = (QA B : ℤ) • ((QA C : ℤ) • γ) by
            rw [mul_comm, mul_zsmul], hγCz, smul_zero]
      rw [show ((QA C : ℤ) * (QA B : ℤ)) • α = (QA C : ℤ) • ((QA B : ℤ) • α) by
            rw [mul_zsmul], hαB, smul_zero]
      rw [zero_add]
    have hxsubCB : x ∈ sigmaSubAFinset (C ∪ B) :=
      (mem_sigmaSubAFinset_iff_zsmul_eq_zero h2CB x).mpr hxC
    have hsubCB : C ∪ B ⊆ A₀ ∪ B := Finset.union_subset_union_left hCsub
    have hneCB : C ∪ B ≠ A₀ ∪ B := by
      intro heq
      refine hCne (Finset.Subset.antisymm hCsub ?_)
      intro q hq
      have hmem : q ∈ C ∪ B := by rw [heq]; exact Finset.mem_union_left B hq
      rcases Finset.mem_union.mp hmem with h | h
      · exact h
      · exact absurd hq (Finset.disjoint_left.mp hdisj.symm h)
    exact not_mem_sigmaStrataFinset_of_mem_sigmaSubAFinset hsubCB hneCB hxsubCB hx
  exact ⟨γ, hγstrata, α, hαstrata, hsum⟩

/-- The direct-sum decomposition `Σ_{A₀ ∪ B} = Σ_{A₀} ⊕ Σ_B` for Tao's strata
(`Σ_A = sigmaStrataFinset A = 𝕋[Q_A] \ ⋃_{B ⊊ A} 𝕋[Q_B]`): for disjoint `A₀, B ⊆ S`, `S` pairwise
coprime with all elements `≥ 2`, the addition map `(γ, α) ↦ γ + α` is a bijection from
`Σ_{A₀} × Σ_B` onto `Σ_{A₀ ∪ B}`.  This is the strata analogue of `sigmaAFinset_union_add` (which
holds for the exact-denominator sets), and is the summation step used to expand
`f_{Σ_{A₀ ∪ P}} = Σ_{α ∈ Σ_P} f_{α + Σ_{A₀}}` in Tao's `ortho-apply`(i).

Route.  Two halves, both available for the *Set* level in `opArc_l2_endpoint_strata.lean`:
`circle_strata_add_mem` gives `Σ_{A₀} + Σ_B ⊆ Σ_{A₀∪B}` and `circle_strata_decomp_unique` gives
that `+` is injective on `Σ_{A₀} × Σ_B`; so `(Σ_{A₀} ×ˢ Σ_B).image (·+·) ⊆ Σ_{A₀∪B}` and the sum
map is injective there.  What remains is *surjectivity*: for `x ∈ Σ_{A₀∪B}`, choose a Bézout pair
`u Q_{A₀} + v Q_B = 1` (`Nat.Coprime.isCoprime`, from `hS`, `hdisj`) and put
`α := (u Q_{A₀} : ℤ) • x`, `γ := (v Q_B : ℤ) • x`; then `α + γ = x`, `α ∈ Σ_B` and `γ ∈ Σ_{A₀}`.
For the stratum conditions: `Q_B • α = u (Q_{A₀} Q_B) • x = 0` (as `x ∈ 𝕋[Q_{A₀∪B}]`), and if
`C ⊊ B` killed `α` then `Q_C • α = 0` and `Q_{A₀} • γ = 0` give `Q_{A₀∪C} • x = 0`, i.e.
`x ∈ 𝕋[Q_{A₀∪C}]` with `A₀ ∪ C ⊊ A₀ ∪ B`, contradicting `x ∈ Σ_{A₀∪B}`
(`not_mem_sigmaStrataFinset_of_mem_sigmaSubAFinset`); symmetrically for `γ`.  (This mirrors the
already-proved `ZMod` counterpart `strata_add_sum`.)  Finally the Finset sum identity follows from
the image equality by `Finset.sum_image` (with the injectivity), `Finset.sum_product` and
`Finset.sum_comm`, exactly as in `sigmaAFinset_union_add`. -/
theorem sigmaStrataFinset_union_add {S A₀ B : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA₀ : A₀ ⊆ S) (hB : B ⊆ S) (hdisj : Disjoint A₀ B)
    (f : Work.BourgainPlan.IonescuWainger.Circle → ℤ → ℂ) (m : ℤ) :
    (∑ δ ∈ Work.BourgainPlan.IonescuWainger.sigmaStrataFinset (A₀ ∪ B), f δ m)
      = ∑ α ∈ Work.BourgainPlan.IonescuWainger.sigmaStrataFinset B,
          ∑ γ ∈ Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀, f (γ + α) m := by
  classical
  -- `+` is a bijection from `Σ_{A₀} × Σ_B` onto `Σ_{A₀ ∪ B}`: on the image by additivity and
  -- uniqueness of the decomposition, and surjective by `exists_decomp_mem_sigmaStrataFinset`
  have hIm : (sigmaStrataFinset A₀ ×ˢ sigmaStrataFinset B).image
      (fun p : Circle × Circle => p.1 + p.2) = sigmaStrataFinset (A₀ ∪ B) := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      rw [Finset.mem_product] at hp
      exact circle_strata_add_mem h2 hS hA₀ hB hdisj hp.1 hp.2
    · intro x hx
      obtain ⟨γ, hγ, α, hα, hsum⟩ := exists_decomp_mem_sigmaStrataFinset h2 hS hA₀ hB hdisj hx
      exact Finset.mem_image.mpr ⟨(γ, α), Finset.mem_product.mpr ⟨hγ, hα⟩, hsum⟩
  have hinj : Set.InjOn (fun p : Circle × Circle => p.1 + p.2)
      ↑(sigmaStrataFinset A₀ ×ˢ sigmaStrataFinset B) := by
    intro p hp q hq hpq
    rw [Finset.mem_coe, Finset.mem_product] at hp hq
    obtain ⟨hα, hγ⟩ := circle_strata_decomp_unique h2 hS hA₀ hB hdisj hp.2 hq.2 hp.1 hq.1
      (by simpa only [add_comm] using hpq)
    exact Prod.ext hγ hα
  rw [← hIm, Finset.sum_image hinj, Finset.sum_product, Finset.sum_comm]

end Work.BourgainPlan.IonescuWainger
