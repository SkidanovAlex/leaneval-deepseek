import Mathlib
import Submission.Work.Serre.E2dBase
import Submission.Work.Serre.middleSlab_to_slice
import Submission.Work.Serre.slice_pullback_iso

/-!
# The induction step of the E2(d) computation

The induction step from dimension `n` to dimension `n+1` composes five isomorphisms:

* the Mayer–Vietoris step `Work.Serre.mvStep_pullback`, which computes the relative homology of the
  pair `(τ^*E, τ^*E|_{∂I^{n+1}})` in terms of the *middle slab*
  `slabM n = {1/4 < last < 3/4}`, using the acyclicity of the two slab pairs
  (`Work.Serre.isZero_relChains_pbSub_slabU`, `..._slabV`);
* `Work.Serre.middleSlab_to_slice`, which deforms the middle slab onto the middle slice
  `sliceZ n = {last = 1/2}`;
* `Work.Serre.slice_pullback_iso`, which identifies the pullback over the middle slice with the
  pullback over the `n`-cube `Iⁿ`;
* the induction hypothesis `E2dAt n`;
* `Work.Serre.fibre_iso_pullback`, which compares the fibre over the chosen point of the slice with
  the fibre over the prescribed point `d₀`.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace Work.Serre

noncomputable section

/-- **The induction step of the E2(d) computation.** -/
theorem e2dAt_succ (n : ℕ) (ih : E2dAt n) : E2dAt (n+1) := by
  intro E B _ _ p hp τ d₀ K
  -- the acyclicity of the two slab pairs of the Mayer–Vietoris cover
  have hU : ∀ m, IsZero ((Work.Cohomology.relChains (TopCat.of ↥(pbPre p τ (slabU n)))
      (pbSub p τ (slabU n) (slabU n ∩ cubeBdryS (n+1)))).homology m) :=
    fun m => isZero_relChains_pbSub_slabU n p hp τ m
  have hV : ∀ m, IsZero ((Work.Cohomology.relChains (TopCat.of ↥(pbPre p τ (slabV n)))
      (pbSub p τ (slabV n) (slabV n ∩ cubeBdryS (n+1)))).homology m) :=
    fun m => isZero_relChains_pbSub_slabV n p hp τ m
  -- the chosen point of the middle slice
  set d' : Work.Stems.Cubical.IC n := fun _ => half with hd'
  obtain ⟨i₁⟩ := mvStep_pullback n p hp τ hU hV (K + n)
  obtain ⟨i₂⟩ := middleSlab_to_slice n p hp τ (K + n)
  obtain ⟨i₃⟩ := slice_pullback_iso n p τ (K + n)
  obtain ⟨i₄⟩ := ih E B p hp (τ.comp (sliceIncl n)) d' K
  obtain ⟨i₅⟩ := fibre_iso_pullback (n+1) p hp τ d₀ (sliceIncl n d') K
  exact ⟨i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ i₄ ≪≫ i₅⟩

/-- **The E2(d) statement in every dimension.** -/
theorem e2dAll : ∀ n, E2dAt n
  | 0 => e2dAt_zero
  | (n+1) => e2dAt_succ n (e2dAll n)

end

end Work.Serre
