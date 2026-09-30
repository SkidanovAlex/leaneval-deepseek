import Mathlib
import Submission.Work.Serre.cubePairDefs
import Submission.Work.Serre.mvStep_pullback
import Submission.Work.Serre.middleSlab_to_slice
import Submission.Work.Serre.slice_pullback_iso

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The relative homology of the pullback cube pair vanishes below the dimension

For a Serre fibration `p : E → B`, a map `τ : I^D → B`, and `m < D`,

  `H_m(τ^*E, τ^*E|_{∂I^D}) = 0`,

the *ambient* companion of `Work.Serre.cubeBdry_isZero` (`H_m(I^D, ∂I^D) = 0` for `m ≠ D`).

The proof is the induction of the E2(d) computation (`Work.Serre.SerreE2d`), stopped in the
range below the dimension:

* the Mayer–Vietoris step `Work.Serre.mvStep_pullback` (`H_{m+1}(τ^*E, τ^*E|_{∂I^{n+1}}) ≅
  H_m(slab pair)`), the deformation to the middle slice `Work.Serre.middleSlab_to_slice`, and
  `Work.Serre.slice_pullback_iso` (`H_m(slab/slice pair) ≅ H_m` of the pullback over `I^n`)
  give, for every `m`,
  `H_{m+1}(τ^*E_{n+1}, τ^*E_{n+1}|_{∂I^{n+1}}) ≅ H_m((τ ∘ sliceIncl n)^*E_n, ...|_∂I^n)`;
* this reduces the target in degree `m+1` to the inductive statement in degree `m` of the
  `n`-cube;
* the degree-zero case is proved directly from the relative Mayer–Vietoris sequence: the two
  slab chart terms are relatively acyclic (`Work.Serre.isZero_relChains_pbSub_slabU/V`), so the
  connecting map is an isomorphism in positive degrees and the sequence in degree zero starts
  `0 → H_1(X,A) → H_0(middle slab) → 0 → H_0(X,A) → 0`, forcing `H_0(X,A) = 0`.

Everything is reused from the E2(d) chapter; only the index bookkeeping is new here.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- **The one-step iso of the low-range induction.**  The relative homology of the pullback over
the `(n+1)`-cube pair in degree `m+1` is the relative homology of the pullback over the `n`-cube
pair along `τ ∘ sliceIncl n` in degree `m`.

Composition of the Mayer–Vietoris step `mvStep_pullback`, the deformation of the middle slab onto
the middle slice `middleSlab_to_slice`, and `slice_pullback_iso`. -/
theorem cubeStepIso (n : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (τ : C(Work.Stems.Cubical.IC (n+1), B)) (m : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback p τ))
        (pbPre p τ (cubeBdryS (n+1)))).homology (m+1)) ≅
      ((Work.Cohomology.relChains
        (TopCat.of (Work.StemsB.Pullback p (τ.comp (sliceIncl n))))
        (pbPre p (τ.comp (sliceIncl n)) (cubeBdryS n))).homology m)) := by
  obtain ⟨e₁⟩ := mvStep_pullback n p hp τ
    (fun m => isZero_relChains_pbSub_slabU n p hp τ m)
    (fun m => isZero_relChains_pbSub_slabV n p hp τ m) m
  obtain ⟨e₂⟩ := middleSlab_to_slice n p hp τ m
  obtain ⟨e₃⟩ := slice_pullback_iso n p τ m
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃⟩

/-- **The degree-zero case.**  The relative homology of the pullback over the `(n+1)`-cube pair
vanishes in degree `0`.

Proof by the relative Mayer–Vietoris sequence of the cover of the pullback by the two slabs
`U = pbPre p τ (slabU n)` and `V = pbPre p τ (slabV n)`: both chart pairs are relatively acyclic
(`isZero_relChains_pbSub_slabU/V`), so the middle term `relMVH₂` vanishes in every degree; the
long exact sequence in degree `0` then reads `0 → H_0(X,A) → 0`. -/
theorem cubeAmbientZero_isZero (n : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (τ : C(Work.Stems.Cubical.IC (n+1), B)) :
    IsZero ((Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback p τ))
      (pbPre p τ (cubeBdryS (n+1)))).homology 0) := by
  have hUo : IsOpen (pbPre p τ (slabU n)) := by
    rw [pbPre_eq_preimage]
    exact IsOpen.preimage (Work.StemsB.pullbackSnd p τ).continuous (isOpen_slabU n)
  have hVo : IsOpen (pbPre p τ (slabV n)) := by
    rw [pbPre_eq_preimage]
    exact IsOpen.preimage (Work.StemsB.pullbackSnd p τ).continuous (isOpen_slabV n)
  have hcov : pbPre p τ (slabU n) ∪ pbPre p τ (slabV n) = Set.univ := by
    rw [pbPre_eq_preimage, pbPre_eq_preimage, ← Set.preimage_union, slabU_union_slabV,
      Set.preimage_univ]
  -- the two chart terms are relatively acyclic
  have hU : ∀ m, IsZero ((Work.Cohomology.relChains
      (TopCat.of ↥(pbPre p τ (slabU n)))
      ((Subtype.val : ↥(pbPre p τ (slabU n)) →
        TopCat.of (Work.StemsB.Pullback p τ)) ⁻¹'
        (pbPre p τ (cubeBdryS (n+1))))).homology m) := by
    intro m
    have hset : pbSub p τ (slabU n) (slabU n ∩ cubeBdryS (n+1))
        = ((Subtype.val : ↥(pbPre p τ (slabU n)) →
            TopCat.of (Work.StemsB.Pullback p τ)) ⁻¹'
            (pbPre p τ (cubeBdryS (n+1)))) := by
      ext x
      simp only [mem_pbSub, Set.mem_preimage, mem_pbPre, Set.mem_inter_iff]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨x.2, h⟩
    rw [← hset]
    exact isZero_relChains_pbSub_slabU n p hp τ m
  have hV : ∀ m, IsZero ((Work.Cohomology.relChains
      (TopCat.of ↥(pbPre p τ (slabV n)))
      ((Subtype.val : ↥(pbPre p τ (slabV n)) →
        TopCat.of (Work.StemsB.Pullback p τ)) ⁻¹'
        (pbPre p τ (cubeBdryS (n+1))))).homology m) := by
    intro m
    have hset : pbSub p τ (slabV n) (slabV n ∩ cubeBdryS (n+1))
        = ((Subtype.val : ↥(pbPre p τ (slabV n)) →
            TopCat.of (Work.StemsB.Pullback p τ)) ⁻¹'
            (pbPre p τ (cubeBdryS (n+1)))) := by
      ext x
      simp only [mem_pbSub, Set.mem_preimage, mem_pbPre, Set.mem_inter_iff]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨x.2, h⟩
    rw [← hset]
    exact isZero_relChains_pbSub_slabV n p hp τ m
  -- the middle term of the relative Mayer–Vietoris sequence vanishes in degree zero
  set XT : TopCat := TopCat.of (Work.StemsB.Pullback p τ) with hXT
  have h₂ : IsZero (Work.Cohomology.relMVH₂ XT
      (pbPre p τ (cubeBdryS (n+1))) (pbPre p τ (slabU n)) (pbPre p τ (slabV n)) 0) := by
    refine Work.ThreeConnected.Excision.isZero_homology_biprod ?_ ?_
    · obtain ⟨e⟩ := Work.Cohomology.Endgame.relSmallChains_iso_relChains (X := XT)
        (pbPre p τ (slabU n)) (pbPre p τ (slabV n)) (pbPre p τ (slabU n))
        (pbPre p τ (slabU n) ∩ pbPre p τ (cubeBdryS (n+1)))
        Set.inter_subset_left (Or.inl (fun x hx => hx))
      have hset : ((Subtype.val : ↥(pbPre p τ (slabU n)) → XT) ⁻¹'
            (pbPre p τ (slabU n) ∩ pbPre p τ (cubeBdryS (n+1))))
          = ((Subtype.val : ↥(pbPre p τ (slabU n)) → XT) ⁻¹'
              (pbPre p τ (cubeBdryS (n+1)))) := by
        ext x
        exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
      rw [hset] at e
      exact IsZero.of_iso (hU 0)
        ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 0).mapIso e)
    · obtain ⟨e⟩ := Work.Cohomology.Endgame.relSmallChains_iso_relChains (X := XT)
        (pbPre p τ (slabU n)) (pbPre p τ (slabV n)) (pbPre p τ (slabV n))
        (pbPre p τ (slabV n) ∩ pbPre p τ (cubeBdryS (n+1)))
        Set.inter_subset_left (Or.inr (fun x hx => hx))
      have hset : ((Subtype.val : ↥(pbPre p τ (slabV n)) → XT) ⁻¹'
            (pbPre p τ (slabV n) ∩ pbPre p τ (cubeBdryS (n+1))))
          = ((Subtype.val : ↥(pbPre p τ (slabV n)) → XT) ⁻¹'
              (pbPre p τ (cubeBdryS (n+1)))) := by
        ext x
        exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
      rw [hset] at e
      exact IsZero.of_iso (hV 0)
        ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 0).mapIso e)
  -- the connecting map of the sequence is an isomorphism in every degree
  have h₁ : Epi (HomologicalComplex.homologyMap (Work.Cohomology.relMVShort XT
      (pbPre p τ (cubeBdryS (n+1))) (pbPre p τ (slabU n)) (pbPre p τ (slabV n))).f 0) :=
    h₂.epi _
  -- hence `H_0` of the third term vanishes
  have hex : (Work.Cohomology.relMVShort XT
      (pbPre p τ (cubeBdryS (n+1))) (pbPre p τ (slabU n))
      (pbPre p τ (slabV n))).X₃.ExactAt 0 :=
    (Work.Cohomology.relMVShort_shortExact _ _ _ _).exactAt_X₃ 0 h₁
      (fun j hj => absurd hj (by simp [ComplexShape.down]))
  have hz : IsZero (Work.Cohomology.relMVH₃ XT
      (pbPre p τ (cubeBdryS (n+1))) (pbPre p τ (slabU n))
      (pbPre p τ (slabV n)) 0) :=
    (HomologicalComplex.exactAt_iff_isZero_homology (Work.Cohomology.relMVShort XT
      (pbPre p τ (cubeBdryS (n+1))) (pbPre p τ (slabU n))
      (pbPre p τ (slabV n))).X₃ 0).mp hex
  exact IsZero.of_iso hz (Work.Cohomology.relMVSmallIso XT _ _ _ hUo hVo hcov 0).symm

/-- **The main induction.**  For every `D`, the relative homology of the pullback over the cube
pair `(I^D, ∂I^D)` vanishes in all degrees `m < D`. -/
theorem cubeAmbient_isZero (D : ℕ) :
    ∀ (E : Type) [TopologicalSpace E] (B : Type) [TopologicalSpace B] (p : C(E, B))
      (hp : Work.StemsB.IsSerreFibration p) (τ : C(Work.Stems.Cubical.IC D, B)) (m : ℕ),
      m < D →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback p τ))
        (Work.Serre.pbPre p τ (Work.Serre.cubeBdryS D))).homology m) := by
  induction D with
  | zero => intro E _ B _ p hp τ m hm; omega
  | succ n ih =>
      intro E _ B _ p hp τ m hm
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0
        exact cubeAmbientZero_isZero n p hp τ
      · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
        obtain ⟨e⟩ := cubeStepIso n p hp τ m'
        haveI := ih E B p hp (τ.comp (sliceIncl n)) m' (by omega)
        exact IsZero.of_iso this e

end

end Work.Serre
