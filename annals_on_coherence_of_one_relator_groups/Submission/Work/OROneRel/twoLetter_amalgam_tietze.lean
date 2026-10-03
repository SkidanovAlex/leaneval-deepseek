/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The two-letter Tietze transformation `⟨a, b | (a ^ p * b ^ q) ^ l⟩ ≅ ⟨a, b, c | c ^ l, b ^ q * c⁻¹ * a ^ p⟩`

For the two-letter one-relator group `⟨a, b | (a ^ p * b ^ q) ^ l⟩` the word `a ^ p * b ^ q` can be
made into a new generator, replacing the unique relator `(a ^ p * b ^ q) ^ l` by the two relators
`c ^ l` and `b ^ q * c⁻¹ * a ^ p` (with `c` the new generator).  This is the elementary Tietze
transformation underlying the amalgam decomposition of the two-letter case of the
Magnus--Moldavanskii step: it exhibits the group as the amalgam of
`⟨b, a ^ p * b ^ q⟩` (a free group on two generators, since `c` is new) and `⟨a, b | a ^ p⟩`
along `⟨a ^ p⟩`.

The isomorphism is the identity on the generators `a`, `b` (i.e. on `0`, `1 : Fin _`) and it sends
`a ^ p * b ^ q` to the new generator, so it carries the element `a ^ p * b ^ q` of the two-letter
group to the new generator `c = FreeGroup.of 2`.

This file is `sorry`-free.
-/
import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.wordOfDefs

namespace Work.OROneRel

/-- The universal property of `PresentedGroup` evaluated on an arbitrary word: the homomorphism
`PresentedGroup.toGroup h` sends the class of a word `z : FreeGroup α` to the image of `z` under
the lift `FreeGroup.lift f`. -/
theorem toGroup_mk_apply {α : Type} {G : Type} [Group G] {rels : Set (FreeGroup α)}
    {f : α → G} (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (z : FreeGroup α) :
    PresentedGroup.toGroup (f := f) h (PresentedGroup.mk rels z) = FreeGroup.lift f z := by
  rw [show PresentedGroup.toGroup (f := f) h
      = QuotientGroup.lift (Subgroup.normalClosure rels) (FreeGroup.lift f)
          (PresentedGroup.to_group_eq_one_of_mem_closure h) from rfl]
  exact QuotientGroup.lift_mk _ _ z

theorem twoLetter_amalgam_tietze (p q l : ℕ) :
    ∃ (e : PresentedGroup ({(FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q) ^ l} : Set (FreeGroup (Fin 2))) ≃*
        PresentedGroup ({FreeGroup.of (2 : Fin 3) ^ l,
          FreeGroup.of (1 : Fin 3) ^ q * (FreeGroup.of (2 : Fin 3))⁻¹ * FreeGroup.of (0 : Fin 3) ^ p} : Set (FreeGroup (Fin 3)))),
      e (PresentedGroup.mk _ (FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q)) =
        PresentedGroup.mk _ (FreeGroup.of (2 : Fin 3)) := by
  classical
  -- The two relator sets, named.
  set S1 : Set (FreeGroup (Fin 2)) :=
    ({(FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q) ^ l} : Set (FreeGroup (Fin 2)))
    with hS1
  set S2 : Set (FreeGroup (Fin 3)) :=
    ({FreeGroup.of (2 : Fin 3) ^ l,
      FreeGroup.of (1 : Fin 3) ^ q * (FreeGroup.of (2 : Fin 3))⁻¹ * FreeGroup.of (0 : Fin 3) ^ p} :
        Set (FreeGroup (Fin 3))) with hS2
  have hrel1 : ((FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q) ^ l) ∈ S1 := by
    rw [hS1]; simp
  have hrel2a : FreeGroup.of (2 : Fin 3) ^ l ∈ S2 := by rw [hS2]; simp
  have hrel2b : FreeGroup.of (1 : Fin 3) ^ q * (FreeGroup.of (2 : Fin 3))⁻¹ *
      FreeGroup.of (0 : Fin 3) ^ p ∈ S2 := by rw [hS2]; simp
  -- ## The relators of the second presentation hold in `PresentedGroup S2`
  -- `c ^ l = 1`
  have h2a : (PresentedGroup.of (2 : Fin 3) : PresentedGroup S2) ^ l = 1 := by
    have h : PresentedGroup.mk S2 (FreeGroup.of (2 : Fin 3) ^ l) = 1 :=
      PresentedGroup.one_of_mem hrel2a
    simpa [PresentedGroup.of, map_pow] using h
  -- `b ^ q * c⁻¹ * a ^ p = 1`
  have h2b : (PresentedGroup.of (1 : Fin 3) : PresentedGroup S2) ^ q *
      ((PresentedGroup.of (2 : Fin 3) : PresentedGroup S2))⁻¹ *
      (PresentedGroup.of (0 : Fin 3) : PresentedGroup S2) ^ p = 1 := by
    have h : PresentedGroup.mk S2 (FreeGroup.of (1 : Fin 3) ^ q * (FreeGroup.of (2 : Fin 3))⁻¹ *
        FreeGroup.of (0 : Fin 3) ^ p) = 1 := PresentedGroup.one_of_mem hrel2b
    simpa [PresentedGroup.of, map_mul, map_pow, map_inv] using h
  -- hence `c = a ^ p * b ^ q`
  have h2c : (PresentedGroup.of (2 : Fin 3) : PresentedGroup S2) =
      (PresentedGroup.of (0 : Fin 3) : PresentedGroup S2) ^ p *
      (PresentedGroup.of (1 : Fin 3) : PresentedGroup S2) ^ q := by
    have hBA : ((PresentedGroup.of (2 : Fin 3) : PresentedGroup S2))⁻¹ =
        ((PresentedGroup.of (1 : Fin 3) : PresentedGroup S2) ^ q)⁻¹ *
        ((PresentedGroup.of (0 : Fin 3) : PresentedGroup S2) ^ p)⁻¹ := by
      calc ((PresentedGroup.of (2 : Fin 3) : PresentedGroup S2))⁻¹
          = ((PresentedGroup.of (1 : Fin 3) : PresentedGroup S2) ^ q)⁻¹ *
            ((PresentedGroup.of (1 : Fin 3) : PresentedGroup S2) ^ q *
             ((PresentedGroup.of (2 : Fin 3) : PresentedGroup S2))⁻¹ *
             (PresentedGroup.of (0 : Fin 3) : PresentedGroup S2) ^ p) *
            ((PresentedGroup.of (0 : Fin 3) : PresentedGroup S2) ^ p)⁻¹ := by group
        _ = ((PresentedGroup.of (1 : Fin 3) : PresentedGroup S2) ^ q)⁻¹ * 1 *
            ((PresentedGroup.of (0 : Fin 3) : PresentedGroup S2) ^ p)⁻¹ := by rw [h2b]
        _ = ((PresentedGroup.of (1 : Fin 3) : PresentedGroup S2) ^ q)⁻¹ *
            ((PresentedGroup.of (0 : Fin 3) : PresentedGroup S2) ^ p)⁻¹ := by group
    calc (PresentedGroup.of (2 : Fin 3) : PresentedGroup S2)
        = (((PresentedGroup.of (2 : Fin 3) : PresentedGroup S2))⁻¹)⁻¹ := by group
      _ = (((PresentedGroup.of (1 : Fin 3) : PresentedGroup S2) ^ q)⁻¹ *
            ((PresentedGroup.of (0 : Fin 3) : PresentedGroup S2) ^ p)⁻¹)⁻¹ := by rw [hBA]
      _ = (PresentedGroup.of (0 : Fin 3) : PresentedGroup S2) ^ p *
          (PresentedGroup.of (1 : Fin 3) : PresentedGroup S2) ^ q := by group
  -- hence `(a ^ p * b ^ q) ^ l = 1`
  have h2d : ((PresentedGroup.of (0 : Fin 3) : PresentedGroup S2) ^ p *
      (PresentedGroup.of (1 : Fin 3) : PresentedGroup S2) ^ q) ^ l = 1 := by
    rw [← h2c]; exact h2a
  -- ## The relators of the second presentation hold in `PresentedGroup S1` after `a ↦ a, b ↦ b, c ↦ a ^ p * b ^ q`
  have h1a : ((PresentedGroup.of (0 : Fin 2) : PresentedGroup S1) ^ p *
      (PresentedGroup.of (1 : Fin 2) : PresentedGroup S1) ^ q) ^ l = 1 := by
    have h : PresentedGroup.mk S1
        ((FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q) ^ l) = 1 :=
      PresentedGroup.one_of_mem hrel1
    simpa [PresentedGroup.of, map_pow, map_mul] using h
  have h1b : (PresentedGroup.of (1 : Fin 2) : PresentedGroup S1) ^ q *
      ((PresentedGroup.of (0 : Fin 2) : PresentedGroup S1) ^ p *
       (PresentedGroup.of (1 : Fin 2) : PresentedGroup S1) ^ q)⁻¹ *
      (PresentedGroup.of (0 : Fin 2) : PresentedGroup S1) ^ p = 1 := by group
  -- ## The two homomorphisms
  -- `φ : PresentedGroup S1 →* PresentedGroup S2`, `a ↦ a`, `b ↦ b`
  let f : Fin 2 → PresentedGroup S2 := fun i => PresentedGroup.of (Fin.castSucc i)
  have hf : ∀ i : Fin 2, f i = PresentedGroup.of (Fin.castSucc i) := fun i => rfl
  have hf0 : f 0 = PresentedGroup.of (0 : Fin 3) := by simp [f]
  have hf1 : f 1 = PresentedGroup.of (1 : Fin 3) := by simp [f]
  have hφrel : ∀ r ∈ S1, FreeGroup.lift f r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    rw [hr]
    simp only [map_pow, map_mul, FreeGroup.lift_apply_of, hf0, hf1]
    exact h2d
  let φ : PresentedGroup S1 →* PresentedGroup S2 := PresentedGroup.toGroup (f := f) hφrel
  have hφ_of : ∀ i : Fin 2, φ (PresentedGroup.of i) = f i :=
    fun i => PresentedGroup.toGroup.of (f := f) hφrel (x := i)
  -- `ψ : PresentedGroup S2 →* PresentedGroup S1`, `a ↦ a`, `b ↦ b`, `c ↦ a ^ p * b ^ q`
  let g : Fin 3 → PresentedGroup S1 :=
    ![PresentedGroup.of (0 : Fin 2), PresentedGroup.of (1 : Fin 2),
      (PresentedGroup.of (0 : Fin 2)) ^ p * (PresentedGroup.of (1 : Fin 2)) ^ q]
  have hg0 : g 0 = PresentedGroup.of (0 : Fin 2) := by simp [g]
  have hg1 : g 1 = PresentedGroup.of (1 : Fin 2) := by simp [g]
  have hg2 : g 2 = (PresentedGroup.of (0 : Fin 2)) ^ p *
      (PresentedGroup.of (1 : Fin 2)) ^ q := by simp [g]
  have hψrel : ∀ r ∈ S2, FreeGroup.lift g r = 1 := by
    intro r hr
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · simp only [map_pow, FreeGroup.lift_apply_of, hg2]
      exact h1a
    · simp only [map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, hg0, hg1, hg2]
      exact h1b
  let ψ : PresentedGroup S2 →* PresentedGroup S1 := PresentedGroup.toGroup (f := g) hψrel
  have hψ_of : ∀ i : Fin 3, ψ (PresentedGroup.of i) = g i :=
    fun i => PresentedGroup.toGroup.of (f := g) hψrel (x := i)
  -- ## The two composites are the identities
  have hg_cast : ∀ i : Fin 2, g (Fin.castSucc i) = (PresentedGroup.of i : PresentedGroup S1) := by
    intro i
    fin_cases i <;> simp [g]
  have hψφ : ψ.comp φ = MonoidHom.id (PresentedGroup S1) := by
    apply PresentedGroup.ext
    intro i
    change ψ (φ (PresentedGroup.of i)) = PresentedGroup.of i
    rw [hφ_of i, hf i, hψ_of (Fin.castSucc i), hg_cast i]
  have hφg : ∀ i : Fin 3, φ (g i) = (PresentedGroup.of i : PresentedGroup S2) := by
    intro i
    fin_cases i <;> simp [g, hφ_of, hf, h2c]
  have hφψ : φ.comp ψ = MonoidHom.id (PresentedGroup S2) := by
    apply PresentedGroup.ext
    intro i
    change φ (ψ (PresentedGroup.of i)) = PresentedGroup.of i
    rw [hψ_of i]
    exact hφg i
  -- ## Assembly
  refine ⟨MonoidHom.toMulEquiv φ ψ hψφ hφψ, ?_⟩
  have hval : φ (PresentedGroup.mk S1
        (FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q)) =
      PresentedGroup.mk S2 (FreeGroup.of (2 : Fin 3)) := by
    rw [toGroup_mk_apply (f := f) hφrel]
    simp only [map_pow, map_mul, FreeGroup.lift_apply_of, hf0, hf1]
    simpa only [PresentedGroup.of] using h2c.symm
  exact hval

end Work.OROneRel
