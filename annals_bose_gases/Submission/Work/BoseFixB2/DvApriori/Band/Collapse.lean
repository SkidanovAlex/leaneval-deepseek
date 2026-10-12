import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.Band.Support
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.DvApriori.Band.Collapse`

The **free-slot collapse**: for a weight `W` that is constant along the slots of a list `L`
(and merely measurable/integrable), and smooth states `η, ζ`,

    Σ_{R ⊆ L} ∫_{abox} (X_R η) · W · (X_R ζ)  =  ∫_{abox} η · W · ζ,

where `X_R = slotProd ℓ L R` applies `aQ ℓ j` on the slots `j ∈ R ∩ L` and `aP ℓ j` on the
remaining slots of `L`.

This is the step that makes the FS §6 band analysis work: the weight is never
differentiated nor averaged, so no regularity of `W` (in particular of the potential
profile `potWordU`) is needed — only the elementary facts that a slot-mean pulls out a
factor constant along that slot and annihilates a mean-free factor.

The proof is an induction on the list `L`:

* the resolution `Σ_{R ⊆ insert j L'} X_R = X_{L'}` splits the sum at the new slot `j`;
* the new slot operators `aP ℓ j`, `aQ ℓ j` commute with the remaining ones;
* the induction hypothesis is applied to the two states `aP ℓ j η`, `aQ ℓ j η`;
* the two resulting terms recombine into `∫ η W ζ` because the *mixed* terms vanish
  (`integral_split_slot`): `aP ℓ j η` is constant along slot `j` while `W · aQ ℓ j ζ` is
  mean-free there, and symmetrically.
-/

namespace Work.BoseFixB2.DvApriori

open Submission.BoseGases MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-! ## 1. Sum of four integrals -/

theorem integral_add_four {n : ℕ} {ℓ : ℝ} {A B C D : X n → ℝ}
    (hA : IntegrableOn A (abox n ℓ)) (hB : IntegrableOn B (abox n ℓ))
    (hC : IntegrableOn C (abox n ℓ)) (hD : IntegrableOn D (abox n ℓ)) :
    (∫ x in abox n ℓ, (A x + B x) + (C x + D x))
      = ((∫ x in abox n ℓ, A x) + (∫ x in abox n ℓ, B x))
        + ((∫ x in abox n ℓ, C x) + (∫ x in abox n ℓ, D x)) := by
  have h1 : (∫ x in abox n ℓ, (A x + B x) + (C x + D x))
      = (∫ x in abox n ℓ, A x + B x) + (∫ x in abox n ℓ, C x + D x) := by
    simpa using MeasureTheory.integral_add (μ := MeasureTheory.volume.restrict (abox n ℓ))
      (hA.add hB) (hC.add hD)
  have h2 : (∫ x in abox n ℓ, A x + B x)
      = (∫ x in abox n ℓ, A x) + (∫ x in abox n ℓ, B x) := by
    simpa using MeasureTheory.integral_add (μ := MeasureTheory.volume.restrict (abox n ℓ)) hA hB
  have h3 : (∫ x in abox n ℓ, C x + D x)
      = (∫ x in abox n ℓ, C x) + (∫ x in abox n ℓ, D x) := by
    simpa using MeasureTheory.integral_add (μ := MeasureTheory.volume.restrict (abox n ℓ)) hC hD
  rw [h1, h2, h3]

/-! ## 2. The one-slot recombination -/

/-- **The one-slot recombination.**  Splitting a state at a single slot and pairing the
`P`-parts against each other and the `Q`-parts against each other reproduces the full
integral: the mixed terms vanish because one side is constant along the slot and the other
is mean-free there. -/
theorem integral_split_slot {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n) {W η ζ : X n → ℝ}
    (hW : ∀ (x : X n) (z : EuclideanSpace ℝ (Fin 3)), W (Function.update x j z) = W x)
    (hWi : IntegrableOn W (abox n ℓ)) (hη : Continuous η) (hζ : Continuous ζ) :
    (∫ x in abox n ℓ, aP ℓ j η x * W x * aP ℓ j ζ x)
      + (∫ x in abox n ℓ, aQ ℓ j η x * W x * aQ ℓ j ζ x)
      = ∫ x in abox n ℓ, η x * W x * ζ x := by
  have hPη : Continuous (aP ℓ j η) := aP_continuous hℓ j hη
  have hQη : Continuous (aQ ℓ j η) := aQ_continuous hℓ j hη
  have hPζ : Continuous (aP ℓ j ζ) := aP_continuous hℓ j hζ
  have hQζ : Continuous (aQ ℓ j ζ) := aQ_continuous hℓ j hζ
  have hA : IntegrableOn (fun x => aP ℓ j η x * W x * aP ℓ j ζ x) (abox n ℓ) :=
    integrableOn_mul_of_continuous_of_integrable hℓ hPη hPζ hWi
  have hB : IntegrableOn (fun x => aP ℓ j η x * W x * aQ ℓ j ζ x) (abox n ℓ) :=
    integrableOn_mul_of_continuous_of_integrable hℓ hPη hQζ hWi
  have hC : IntegrableOn (fun x => aQ ℓ j η x * W x * aP ℓ j ζ x) (abox n ℓ) :=
    integrableOn_mul_of_continuous_of_integrable hℓ hQη hPζ hWi
  have hD : IntegrableOn (fun x => aQ ℓ j η x * W x * aQ ℓ j ζ x) (abox n ℓ) :=
    integrableOn_mul_of_continuous_of_integrable hℓ hQη hQζ hWi
  -- the two mixed terms vanish
  have hcross1 : (∫ x in abox n ℓ, aP ℓ j η x * W x * aQ ℓ j ζ x) = 0 := by
    have hf : ∀ (x : X n) (z : EuclideanSpace ℝ (Fin 3)),
        (fun y => aP ℓ j η y * W y) (Function.update x j z)
          = (fun y => aP ℓ j η y * W y) x := by
      intro x z
      simp only []
      rw [aP_invariant_slot j η x z, hW x z]
    have hg : aP ℓ j (aQ ℓ j ζ) = 0 := aP_aQ_slot_eq_zero hℓ j hζ
    exact integral_mul_eq_zero_of_meanFree hℓ j hf hg hB
  have hcross2 : (∫ x in abox n ℓ, aQ ℓ j η x * W x * aP ℓ j ζ x) = 0 := by
    have hswap : (∫ x in abox n ℓ, aQ ℓ j η x * W x * aP ℓ j ζ x)
        = ∫ x in abox n ℓ, (fun y => W y * aP ℓ j ζ y) x * aQ ℓ j η x := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      simp only []
      ring
    have hC' : IntegrableOn (fun x => (fun y => W y * aP ℓ j ζ y) x * aQ ℓ j η x)
        (abox n ℓ) :=
      hC.congr (Filter.Eventually.of_forall (fun x => by
        simp only []
        ring))
    rw [hswap]
    have hf : ∀ (x : X n) (z : EuclideanSpace ℝ (Fin 3)),
        (fun y => W y * aP ℓ j ζ y) (Function.update x j z)
          = (fun y => W y * aP ℓ j ζ y) x := by
      intro x z
      simp only []
      rw [aP_invariant_slot j ζ x z, hW x z]
    have hg : aP ℓ j (aQ ℓ j η) = 0 := aP_aQ_slot_eq_zero hℓ j hη
    exact integral_mul_eq_zero_of_meanFree hℓ j hf hg hC'
  -- the pointwise expansion
  have hpt : (fun x => η x * W x * ζ x)
      = fun x => (aP ℓ j η x * W x * aP ℓ j ζ x + aP ℓ j η x * W x * aQ ℓ j ζ x)
          + (aQ ℓ j η x * W x * aP ℓ j ζ x + aQ ℓ j η x * W x * aQ ℓ j ζ x) := by
    funext x
    simp only [aQ]
    ring
  rw [hpt, integral_add_four hA hB hC hD, hcross1, hcross2]
  ring

/-! ## 3. The free-slot collapse -/

/-- **The free-slot collapse.**  For a list `L` of slots, a weight `W` constant along all of
them, and continuous states `η, ζ`, the sum over all patterns `R ⊆ L` of the pairing of the
corresponding slot projections collapses to the plain pairing. -/
theorem sum_slotProd_pairing {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} :
    ∀ (L : List ℕ), L.Nodup → (∀ j ∈ L, j < n) → ∀ {W η ζ : X n → ℝ},
      (∀ j ∈ L, ∀ (hj : j < n) (x : X n) (z : EuclideanSpace ℝ (Fin 3)),
        W (Function.update x ⟨j, hj⟩ z) = W x) →
      IntegrableOn W (abox n ℓ) → Continuous η → Continuous ζ →
      (∑ R ∈ L.toFinset.powerset,
        ∫ x in abox n ℓ, slotProd ℓ L R η x * W x * slotProd ℓ L R ζ x)
        = ∫ x in abox n ℓ, η x * W x * ζ x := by
  intro L
  induction L with
  | nil =>
      intro _ _ W η ζ _ _ hη hζ
      simp
  | cons j L ih =>
      intro hnd hlt W η ζ hW hWi hη hζ
      obtain ⟨hjL, hndL⟩ := List.nodup_cons.mp hnd
      have hltL : ∀ k ∈ L, k < n := fun k hk => hlt k (List.mem_cons_of_mem _ hk)
      have hjlt : j < n := hlt j (List.mem_cons_self)
      have hW' : ∀ k ∈ L, ∀ (hk : k < n) (x : X n) (z : EuclideanSpace ℝ (Fin 3)),
          W (Function.update x ⟨k, hk⟩ z) = W x :=
        fun k hk => hW k (List.mem_cons_of_mem _ hk)
      -- the powerset splitting at the new slot
      rw [List.toFinset_cons, Finset.powerset_insert]
      have hdisj : Disjoint (L.toFinset.powerset)
          ((L.toFinset.powerset).image (fun s => insert j s)) := by
        rw [Finset.disjoint_left]
        intro a ha hb
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hb
        exact hjL (List.mem_toFinset.mp ((Finset.mem_powerset.mp ha) (Finset.mem_insert_self j T)))
      have hinj : Set.InjOn (fun s : Finset ℕ => insert j s) ↑(L.toFinset.powerset) := by
        intro x hx y hy hxy
        have hx' : j ∉ x := fun h =>
          hjL (List.mem_toFinset.mp ((Finset.mem_powerset.mp hx) h))
        have hy' : j ∉ y := fun h =>
          hjL (List.mem_toFinset.mp ((Finset.mem_powerset.mp hy) h))
        calc x = (insert j x).erase j := (Finset.erase_insert hx').symm
          _ = (insert j y).erase j := by rw [show insert j x = insert j y from hxy]
          _ = y := Finset.erase_insert hy'
      rw [Finset.sum_union hdisj, Finset.sum_image hinj]
      -- first half: the `P`-terms
      have h1 : (∑ R ∈ L.toFinset.powerset,
            ∫ x in abox n ℓ, slotProd ℓ (j :: L) R η x * W x
              * slotProd ℓ (j :: L) R ζ x)
          = ∑ R ∈ L.toFinset.powerset,
              ∫ x in abox n ℓ, slotProd ℓ L R (aP ℓ ⟨j, hjlt⟩ η) x * W x
                * slotProd ℓ L R (aP ℓ ⟨j, hjlt⟩ ζ) x := by
        refine Finset.sum_congr rfl (fun R hR => ?_)
        have hjR : j ∉ R := fun h =>
          hjL (List.mem_toFinset.mp ((Finset.mem_powerset.mp hR) h))
        rw [slotProd_cons hjlt L R η, if_neg hjR, slotProd_cons hjlt L R ζ, if_neg hjR,
          slotProd_aP_comm hℓ hjlt L hjL R hη, slotProd_aP_comm hℓ hjlt L hjL R hζ]
      -- second half: the `Q`-terms
      have h2 : (∑ R ∈ L.toFinset.powerset,
            ∫ x in abox n ℓ, slotProd ℓ (j :: L) (insert j R) η x * W x
              * slotProd ℓ (j :: L) (insert j R) ζ x)
          = ∑ R ∈ L.toFinset.powerset,
              ∫ x in abox n ℓ, slotProd ℓ L R (aQ ℓ ⟨j, hjlt⟩ η) x * W x
                * slotProd ℓ L R (aQ ℓ ⟨j, hjlt⟩ ζ) x := by
        refine Finset.sum_congr rfl (fun R _ => ?_)
        rw [slotProd_cons hjlt L (insert j R) η, if_pos (Finset.mem_insert_self j R),
          slotProd_cons hjlt L (insert j R) ζ, if_pos (Finset.mem_insert_self j R)]
        have hc : ∀ k ∈ L, (k ∈ insert j R ↔ k ∈ R) := fun k hk => by
          rw [Finset.mem_insert]
          exact ⟨fun h => h.elim (fun h' => absurd h' (fun h'' => hjL (h'' ▸ hk))) id, Or.inr⟩
        rw [slotProd_congr L hltL hc η, slotProd_congr L hltL hc ζ,
          slotProd_aQ_comm hℓ hjlt L hjL R hη, slotProd_aQ_comm hℓ hjlt L hjL R hζ]
      rw [h1, h2, ih hndL hltL hW' hWi (aP_continuous hℓ ⟨j, hjlt⟩ hη)
        (aP_continuous hℓ ⟨j, hjlt⟩ hζ),
        ih hndL hltL hW' hWi (aQ_continuous hℓ ⟨j, hjlt⟩ hη)
        (aQ_continuous hℓ ⟨j, hjlt⟩ hζ)]
      exact integral_split_slot hℓ ⟨j, hjlt⟩ (hW j (List.mem_cons_self) hjlt) hWi hη hζ

end

end Work.BoseFixB2.DvApriori
