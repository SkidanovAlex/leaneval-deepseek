import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.Margulis.bdFix_size_of_no_fixed_point

/-!
# Propagation of the boundary fixed set

`Work.Mostow.Margulis.bd_set_prop`: if `a` has no fixed point in `ℍⁿ` and the commutator
`a * c * a⁻¹ * c⁻¹` maps `bdFix a` into itself, then `c` maps `bdFix a` into itself.

The proof uses `bdFix_size_of_no_fixed_point`, which says that for such an `a` the boundary
fixed set `bdFix a` is a singleton `{ξ}` or a pair `{ξ, η}` with `ξ ≠ η`; the two cases are
handled separately.  The pair case is the content of Margulis' argument: the relation
`bd a⁻¹ (bd c⁻¹ ζ) = bd c⁻¹ (bd d ζ)` (with `d = a c a⁻¹ c⁻¹`) propagated along the involution
`d` of the two-element set `bdFix a` shows that `bd c⁻¹` maps `bdFix a` into itself, and a
two-element set admits no injective-but-not-surjective self-map.
-/

namespace Work.Mostow.Margulis

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

set_option maxHeartbeats 1000000

variable {n : ℕ}

/-- `bd g⁻¹ (bd g ξ) = ξ` on the sphere. -/
lemma bd_inv_apply (hA : POActionProp n) {g : PO n 1} {ξ : E n} (hξ : ξ ∈ Sph n) :
    bd g⁻¹ (bd g ξ) = ξ := by
  have hbd1 : ∀ ξ : E n, ξ ∈ Sph n → bd (1 : PO n 1) ξ = ξ := hA.2.2.2.2.2.2.2.2.1
  have hbdmul : ∀ (g h : PO n 1) (ξ : E n), ξ ∈ Sph n → bd (g * h) ξ = bd g (bd h ξ) :=
    hA.2.2.2.2.2.2.2.2.2.1
  rw [← hbdmul g⁻¹ g ξ hξ, inv_mul_cancel, hbd1 ξ hξ]

/-- `bd g (bd g⁻¹ ξ) = ξ` on the sphere. -/
lemma bd_apply_inv (hA : POActionProp n) {g : PO n 1} {ξ : E n} (hξ : ξ ∈ Sph n) :
    bd g (bd g⁻¹ ξ) = ξ := by
  have hbd1 : ∀ ξ : E n, ξ ∈ Sph n → bd (1 : PO n 1) ξ = ξ := hA.2.2.2.2.2.2.2.2.1
  have hbdmul : ∀ (g h : PO n 1) (ξ : E n), ξ ∈ Sph n → bd (g * h) ξ = bd g (bd h ξ) :=
    hA.2.2.2.2.2.2.2.2.2.1
  rw [← hbdmul g g⁻¹ ξ hξ, mul_inv_cancel, hbd1 ξ hξ]

/-- Singleton case of the propagation: `bdFix a = {ξ}` and the commutator fixes `ξ`. -/
lemma bd_set_prop_single (hA : POActionProp n) {a c : PO n 1} {ξ : E n}
    (hF : bdFix a = {ξ}) (hmap : bd (a * c * a⁻¹ * c⁻¹) ξ = ξ) : bd c ξ = ξ := by
  have hbdSph : ∀ (g : PO n 1) (ξ : E n), ξ ∈ Sph n → bd g ξ ∈ Sph n := hA.2.2.2.2.2.2.2.1
  have hξF : ξ ∈ bdFix a := by rw [hF]; exact Set.mem_singleton_iff.mpr rfl
  have hξ : ξ ∈ Sph n := hξF.1
  have hx : bd c⁻¹ ξ ∈ Sph n := hbdSph c⁻¹ ξ hξ
  have hy : bd a⁻¹ (bd c⁻¹ ξ) ∈ Sph n := hbdSph a⁻¹ (bd c⁻¹ ξ) hx
  have hz : bd c (bd a⁻¹ (bd c⁻¹ ξ)) ∈ Sph n := hbdSph c (bd a⁻¹ (bd c⁻¹ ξ)) hy
  have hainvξ : bd a⁻¹ ξ = ξ := by
    have h := bd_inv_apply (g := a) hA hξ
    rwa [hξF.2] at h
  -- the commutator as a composition
  have hd : bd (a * c * a⁻¹ * c⁻¹) ξ = bd a (bd c (bd a⁻¹ (bd c⁻¹ ξ))) := by
    rw [hA.2.2.2.2.2.2.2.2.2.1 (a * c * a⁻¹) c⁻¹ ξ hξ,
      hA.2.2.2.2.2.2.2.2.2.1 (a * c) a⁻¹ (bd c⁻¹ ξ) hx,
      hA.2.2.2.2.2.2.2.2.2.1 a c (bd a⁻¹ (bd c⁻¹ ξ)) hy]
  -- peel off `bd a⁻¹`
  have h1 : bd a⁻¹ (bd (a * c * a⁻¹ * c⁻¹) ξ) = bd c (bd a⁻¹ (bd c⁻¹ ξ)) := by
    rw [hd]
    exact bd_inv_apply (g := a) hA hz
  have h2 : bd c (bd a⁻¹ (bd c⁻¹ ξ)) = ξ := by
    rw [← h1, hmap, hainvξ]
  -- peel off `bd c⁻¹`
  have h3 : bd a⁻¹ (bd c⁻¹ ξ) = bd c⁻¹ ξ := by
    have h := congrArg (bd c⁻¹) h2
    rwa [bd_inv_apply (g := c) hA hy] at h
  have h4 : bd a (bd c⁻¹ ξ) = bd c⁻¹ ξ := by
    have h := bd_apply_inv (g := a) hA hx
    rwa [h3] at h
  -- so `bd c⁻¹ ξ` is a fixed boundary point of `a`, i.e. `= ξ`
  have h5 : bd c⁻¹ ξ = ξ := by
    have hmem : bd c⁻¹ ξ ∈ bdFix a := ⟨hx, h4⟩
    rw [hF] at hmem
    exact Set.mem_singleton_iff.mp hmem
  calc bd c ξ = bd c (bd c⁻¹ ξ) := by rw [h5]
    _ = ξ := bd_apply_inv (g := c) hA hξ

/-- Pair case of the propagation: `bdFix a = {ξ, η}` with `ξ ≠ η`. -/
lemma bd_set_prop_pair (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n) (hn : 1 ≤ n)
    {a c : PO n 1} {ξ η : E n} (hne : ξ ≠ η) (hF : bdFix a = {ξ, η})
    (hnofix : ∀ u : E n, a • u ≠ u)
    (hmap : ∀ ζ ∈ bdFix a, bd (a * c * a⁻¹ * c⁻¹) ζ ∈ bdFix a) :
    ∀ ζ ∈ bdFix a, bd c ζ ∈ bdFix a := by
  have hbdSph : ∀ (g : PO n 1) (ξ : E n), ξ ∈ Sph n → bd g ξ ∈ Sph n := hA.2.2.2.2.2.2.2.1
  have hbdmul : ∀ (g h : PO n 1) (ξ : E n), ξ ∈ Sph n → bd (g * h) ξ = bd g (bd h ξ) :=
    hA.2.2.2.2.2.2.2.2.2.1
  have hmem : ∀ ζ : E n, ζ ∈ bdFix a ↔ (ζ = ξ ∨ ζ = η) := by
    intro ζ; rw [hF, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hξF : ξ ∈ bdFix a := (hmem ξ).2 (Or.inl rfl)
  have hηF : η ∈ bdFix a := (hmem η).2 (Or.inr rfl)
  -- `bd a⁻¹` fixes `bdFix a` pointwise
  have hainv : ∀ ζ ∈ bdFix a, bd a⁻¹ ζ = ζ := by
    intro ζ hζ
    have h := bd_inv_apply (g := a) hA hζ.1
    rwa [hζ.2] at h
  -- `a ^ 2` has no fixed point in `ℍⁿ`
  have hnofix2 : ∀ u : E n, (a ^ 2) • u ≠ u := by
    intro u hu
    have hone : ∀ u : E n, (1 : PO n 1) • u = u := hA.2.2.2.1
    have hmul : ∀ (g h : PO n 1) (u : E n), (g * h) • u = g • (h • u) := hA.2.2.2.2.1
    have hpar : ∀ m : ℕ, (a ^ m) • u = u ∨ (a ^ m) • u = a • u := by
      intro m
      induction m with
      | zero => exact Or.inl (by simpa using hone u)
      | succ m ih =>
        rw [pow_succ', hmul]
        rcases ih with h | h
        · rw [h]; exact Or.inr rfl
        · rw [h]
          exact Or.inl (by
            rw [show a • (a • u) = (a * a) • u from (hmul a a u).symm, ← pow_two, hu])
    have hbdd : ∃ R : ℝ, ∀ m : ℕ, hdist u ((a ^ m) • u) ≤ R := by
      refine ⟨hdist u (a • u), fun m => ?_⟩
      rcases hpar m with h | h
      · rw [h]
        exact le_trans (le_of_eq ((hI.2.2.1 u u).mpr rfl)) (hI.1 u (a • u))
      · exact le_of_eq (by rw [h])
    obtain ⟨v, hv⟩ := boundedOrbitFixed n hn hA hI a u hbdd
    exact hnofix v hv
  -- `bdFix (a ^ 2) = bdFix a`
  have hsub2 : bdFix a ⊆ bdFix (a ^ 2) := by
    intro ζ hζ
    refine ⟨hζ.1, ?_⟩
    rw [pow_two, hbdmul a a ζ hζ.1, hζ.2, hζ.2]
  have hcarda : (bdFix a).ncard = 2 := by rw [hF, Set.ncard_pair hne]
  have heq2 : bdFix (a ^ 2) = bdFix a := by
    rcases bdFix_size_of_no_fixed_point n hA hI (a ^ 2) hnofix2 with
      ⟨ζ, -, hζ⟩ | ⟨ζ, -, θ, -, hne', hθ⟩
    · have h1 : ξ ∈ bdFix (a ^ 2) := hsub2 hξF
      have h2 : η ∈ bdFix (a ^ 2) := hsub2 hηF
      rw [hζ] at h1 h2
      exact absurd ((Set.mem_singleton_iff.mp h1).trans (Set.mem_singleton_iff.mp h2).symm) hne
    · have hcard2 : (bdFix (a ^ 2)).ncard = 2 := by rw [hθ, Set.ncard_pair hne']
      have hfin2 : (bdFix (a ^ 2)).Finite := by rw [hθ]; exact (Set.finite_singleton θ).insert ζ
      exact (Set.eq_of_subset_of_ncard_le hsub2 (by rw [hcard2, hcarda]) hfin2).symm
  -- the key relation: `bd a⁻¹ (bd c⁻¹ ζ) = bd c⁻¹ ([a,c] ζ)` for `ζ ∈ bdFix a`
  have hrel : ∀ ζ ∈ bdFix a,
      bd a⁻¹ (bd c⁻¹ ζ) = bd c⁻¹ (bd (a * c * a⁻¹ * c⁻¹) ζ) := by
    intro ζ hζ
    have hζS : ζ ∈ Sph n := hζ.1
    have hc1 : bd c⁻¹ ζ ∈ Sph n := hbdSph c⁻¹ ζ hζS
    have ha1 : bd a⁻¹ (bd c⁻¹ ζ) ∈ Sph n := hbdSph a⁻¹ (bd c⁻¹ ζ) hc1
    have hx : bd c (bd a⁻¹ (bd c⁻¹ ζ)) ∈ Sph n := hbdSph c (bd a⁻¹ (bd c⁻¹ ζ)) ha1
    have hdf : bd (a * c * a⁻¹ * c⁻¹) ζ = bd a (bd c (bd a⁻¹ (bd c⁻¹ ζ))) := by
      rw [hbdmul (a * c * a⁻¹) c⁻¹ ζ hζS, hbdmul (a * c) a⁻¹ (bd c⁻¹ ζ) hc1,
        hbdmul a c (bd a⁻¹ (bd c⁻¹ ζ)) ha1]
    have hii : bd a⁻¹ (bd (a * c * a⁻¹ * c⁻¹) ζ) = bd c (bd a⁻¹ (bd c⁻¹ ζ)) := by
      rw [hdf]
      exact bd_inv_apply (g := a) hA hx
    have hiii : bd a⁻¹ (bd (a * c * a⁻¹ * c⁻¹) ζ) = bd (a * c * a⁻¹ * c⁻¹) ζ :=
      hainv _ (hmap ζ hζ)
    have hiv : bd c (bd a⁻¹ (bd c⁻¹ ζ)) = bd (a * c * a⁻¹ * c⁻¹) ζ :=
      hii.symm.trans hiii
    have hv := congrArg (bd c⁻¹) hiv
    rwa [bd_inv_apply (g := c) hA ha1] at hv
  -- the commutator is injective on `bdFix a`
  have hσinj : ∀ x ∈ bdFix a, ∀ y ∈ bdFix a,
      bd (a * c * a⁻¹ * c⁻¹) x = bd (a * c * a⁻¹ * c⁻¹) y → x = y := by
    intro x hx y hy hxy
    have h := congrArg (bd (a * c * a⁻¹ * c⁻¹)⁻¹) hxy
    rw [bd_inv_apply (g := a * c * a⁻¹ * c⁻¹) hA hx.1,
      bd_inv_apply (g := a * c * a⁻¹ * c⁻¹) hA hy.1] at h
    exact h
  -- the commutator is an involution on `bdFix a`
  have hsq : ∀ ζ ∈ bdFix a, bd (a * c * a⁻¹ * c⁻¹) (bd (a * c * a⁻¹ * c⁻¹) ζ) = ζ := by
    by_cases hcfix : bd (a * c * a⁻¹ * c⁻¹) ξ = ξ
    · have hcaseη : bd (a * c * a⁻¹ * c⁻¹) η = η := by
        have h := hmap η hηF
        rw [hF] at h
        rcases Set.mem_insert_iff.mp h with h' | h'
        · exact absurd (hσinj η hηF ξ hξF (h'.trans hcfix.symm)) (fun hc => hne hc.symm)
        · exact Set.mem_singleton_iff.mp h'
      intro ζ hζ
      rcases (hmem ζ).1 hζ with hz | hz
      · rw [hz, hcfix, hcfix]
      · rw [hz, hcaseη, hcaseη]
    · have hcaseξ : bd (a * c * a⁻¹ * c⁻¹) ξ = η := by
        have h := hmap ξ hξF
        rw [hF] at h
        rcases Set.mem_insert_iff.mp h with h' | h'
        · exact absurd h' hcfix
        · exact Set.mem_singleton_iff.mp h'
      have hcaseη : bd (a * c * a⁻¹ * c⁻¹) η = ξ := by
        have h := hmap η hηF
        rw [hF] at h
        rcases Set.mem_insert_iff.mp h with h' | h'
        · exact h'
        · exact absurd (hσinj ξ hξF η hηF (hcaseξ.trans h'.symm)) hne
      intro ζ hζ
      rcases (hmem ζ).1 hζ with hz | hz
      · rw [hz, hcaseξ, hcaseη]
      · rw [hz, hcaseη, hcaseξ]
  -- therefore `bd c⁻¹` maps `bdFix a` into itself
  have hmain : ∀ ζ ∈ bdFix a, bd c⁻¹ ζ ∈ bdFix a := by
    intro ζ hζ
    have hζS : ζ ∈ Sph n := hζ.1
    have hxs : bd c⁻¹ ζ ∈ Sph n := hbdSph c⁻¹ ζ hζS
    have hys : bd a⁻¹ (bd c⁻¹ ζ) ∈ Sph n := hbdSph a⁻¹ (bd c⁻¹ ζ) hxs
    have h1 : bd a⁻¹ (bd c⁻¹ ζ) = bd c⁻¹ (bd (a * c * a⁻¹ * c⁻¹) ζ) := hrel ζ hζ
    have h2 : bd a⁻¹ (bd c⁻¹ (bd (a * c * a⁻¹ * c⁻¹) ζ)) = bd c⁻¹ ζ := by
      have h := hrel (bd (a * c * a⁻¹ * c⁻¹) ζ) (hmap ζ hζ)
      rwa [hsq ζ hζ] at h
    have h4 : bd a⁻¹ (bd a⁻¹ (bd c⁻¹ ζ)) = bd c⁻¹ ζ := by
      rw [h1]
      exact h2
    have h6 : bd a (bd a (bd c⁻¹ ζ)) = bd c⁻¹ ζ := by
      have hA2 : bd a (bd a (bd a⁻¹ (bd a⁻¹ (bd c⁻¹ ζ)))) = bd c⁻¹ ζ := by
        rw [bd_apply_inv (g := a) hA hys, bd_apply_inv (g := a) hA hxs]
      have h := congrArg (fun y => bd a (bd a y)) h4
      rw [hA2] at h
      exact h.symm
    have h5 : bd (a ^ 2) (bd c⁻¹ ζ) = bd c⁻¹ ζ := by
      rw [pow_two, hbdmul a a (bd c⁻¹ ζ) hxs]
      exact h6
    rw [← heq2]
    exact ⟨hxs, h5⟩
  -- `bd c⁻¹` is injective on `bdFix a`, and `bdFix a` has two elements
  have hdist : bd c⁻¹ ξ ≠ bd c⁻¹ η := by
    intro h
    have h2 := congrArg (bd c) h
    rw [bd_apply_inv (g := c) hA hξF.1, bd_apply_inv (g := c) hA hηF.1] at h2
    exact hne h2
  have hval : (bd c⁻¹ ξ = ξ ∧ bd c⁻¹ η = η) ∨ (bd c⁻¹ ξ = η ∧ bd c⁻¹ η = ξ) := by
    have h1 := (hmem _).1 (hmain ξ hξF)
    have h2 := (hmem _).1 (hmain η hηF)
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hdist
      · exact Or.inl ⟨h1, h2⟩
    · rcases h2 with h2 | h2
      · exact Or.inr ⟨h1, h2⟩
      · exact absurd (h1.trans h2.symm) hdist
  have hcξ : bd c ξ ∈ bdFix a := by
    rcases hval with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · refine (hmem (bd c ξ)).2 (Or.inl ?_)
      calc bd c ξ = bd c (bd c⁻¹ ξ) := by rw [e1]
        _ = ξ := bd_apply_inv (g := c) hA hξF.1
    · refine (hmem (bd c ξ)).2 (Or.inr ?_)
      calc bd c ξ = bd c (bd c⁻¹ η) := by rw [e2]
        _ = η := bd_apply_inv (g := c) hA hηF.1
  have hcη : bd c η ∈ bdFix a := by
    rcases hval with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · refine (hmem (bd c η)).2 (Or.inr ?_)
      calc bd c η = bd c (bd c⁻¹ η) := by rw [e2]
        _ = η := bd_apply_inv (g := c) hA hηF.1
    · refine (hmem (bd c η)).2 (Or.inl ?_)
      calc bd c η = bd c (bd c⁻¹ ξ) := by rw [e1]
        _ = ξ := bd_apply_inv (g := c) hA hξF.1
  intro ζ hζ
  rcases (hmem ζ).1 hζ with hz | hz
  · rwa [hz]
  · rwa [hz]

/-- Propagation of the boundary fixed set: if `a` has no fixed point in `ℍⁿ` and the commutator
`a * c * a⁻¹ * c⁻¹` maps `bdFix a` into itself, then `c` maps `bdFix a` into itself.  Here `bd` is
the boundary action of `PO n 1` on `Sph n` and `bdFix a = {ξ | ξ ∈ Sph n ∧ bd a ξ = ξ}`. -/
theorem bd_set_prop (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n) (hn : 1 ≤ n)
    {a c : PO n 1} (hnofix : ∀ u : E n, a • u ≠ u)
    (hmap : ∀ ζ ∈ bdFix a, bd (a * c * a⁻¹ * c⁻¹) ζ ∈ bdFix a) :
    ∀ ζ ∈ bdFix a, bd c ζ ∈ bdFix a := by
  rcases bdFix_size_of_no_fixed_point n hA hI a hnofix with ⟨ξ, -, hF⟩ | ⟨ξ, -, η, -, hne, hF⟩
  · intro ζ hζ
    have hζξ : ζ = ξ := by rw [hF] at hζ; exact Set.mem_singleton_iff.mp hζ
    have hmap' : bd (a * c * a⁻¹ * c⁻¹) ξ = ξ := by
      have h := hmap ξ (by rw [hF]; exact Set.mem_singleton_iff.mpr rfl)
      rwa [hF] at h
    have hc := bd_set_prop_single hA hF hmap'
    rw [hζξ, hF]
    exact Set.mem_singleton_iff.mpr hc
  · exact bd_set_prop_pair n hA hI hn hne hF hnofix hmap

end Work.Mostow.Margulis
