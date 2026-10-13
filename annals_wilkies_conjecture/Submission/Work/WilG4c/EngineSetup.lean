import Mathlib
import Submission.Work.WilG4c.StepCleanDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## Index bookkeeping for the engine set-up -/

/-- `Fin.init` of an appended tuple, in the shape the engine set-up needs. -/
theorem es_init_append {p N : ℕ} (l : Fin p → ℝ) (y : Fin (N + 1) → ℝ) :
    Fin.init (Fin.append (n := N + 1) l y) = Fin.append l (Fin.init y) := by
  have h : (Fin.snoc (Fin.append l (Fin.init y)) (y (Fin.last N)) : Fin (p + N + 1) → ℝ)
      = Fin.append (n := N + 1) l y := by
    rw [← Fin.append_snoc l (Fin.init y) (y (Fin.last N)), Fin.snoc_init_self]
  rw [← h, Fin.init_snoc]

/-- The "drop the last coordinate" image of a set is its projection. -/
theorem es_image_init_eq_projLast {n : ℕ} (A : Set (Fin (n + 1) → ℝ)) :
    Fin.init '' A = WilkiesDesign.projLast A := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z (Fin.last n), by rw [Fin.snoc_init_self]; exact hz⟩
  · rintro ⟨t, ht⟩
    refine ⟨Fin.snoc x t, ht, ?_⟩
    simp

/-- Membership in the fibre part of the open cube. -/
theorem es_mem_inCubeSet_iff {p N : ℕ} (z : Fin (p + N) → ℝ) :
    z ∈ Work.WilG4c.inCubeSet p N ↔
      ∀ j : Fin N, z (Fin.natAdd p j) ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · intro h
    have h' := h
    rw [Work.WilG4c.inCubeSet, Set.mem_ofPred_eq, WilkiesDesign.openCube, Set.mem_ofPred_eq] at h'
    exact fun j => h' j
  · intro h
    rw [Work.WilG4c.inCubeSet, Set.mem_ofPred_eq, WilkiesDesign.openCube, Set.mem_ofPred_eq]
    exact fun j => h j

/-- **Engine set-up.**  Dropping the last coordinate of a cylindrical decomposition of
`ℝ^{p+(n+1)}` (and of one of its cells `κ` inside the open cube) produces a cylindrical
decomposition of `ℝ^{p+n}` with the expected membership/`Ω`/cube/non-empty-fibre properties;
the cell `κ` lies in the open interval `(0,1)` in its last coordinate. -/
theorem EngineSetup (S : WilkiesDesign.SOMin) (n p F0 D : ℕ) (Λ : Set (Fin p → ℝ))
    (C : Finset (Set (Fin (p + (n + 1)) → ℝ))) (κ : Set (Fin (p + (n + 1)) → ℝ))
    (hdec : WilkiesDesign.IsCylDecomp (p + (n + 1)) C)
    (hΩ : ∀ κ' ∈ C, κ' ∈ S.Ω F0 D (p + (n + 1)))
    (hκ : κ ∈ C) (hcube : κ ⊆ Work.WilG4c.inCubeSet p (n + 1))
    (hne : ∀ l ∈ Λ, ∃ y : Fin (n + 1) → ℝ, Fin.append l y ∈ κ) :
    WilkiesDesign.IsCylDecomp (p + n) (C.image (fun c => Fin.init '' c)) ∧
    (Fin.init '' κ) ∈ C.image (fun c => Fin.init '' c) ∧
    (∀ κ' ∈ C.image (fun c => Fin.init '' c), κ' ∈ S.Ω (F0 + 1) D (p + n)) ∧
    (Fin.init '' κ) ⊆ Work.WilG4c.inCubeSet p n ∧
    (∀ l ∈ Λ, ∃ y : Fin n → ℝ, Fin.append l y ∈ Fin.init '' κ) ∧
    (∀ z ∈ κ, z (Fin.last (p + n)) ∈ Set.Ioo (0 : ℝ) 1) ∧
    WilkiesDesign.IsCell (p + (n + 1)) κ ∧
    Fin.init '' κ = WilkiesDesign.projLast κ := by
  have hdec' := (WilkiesDesign.IsCylDecomp.eq_2 (p + n) C).mp hdec
  refine ⟨hdec'.2.2.2, ?_, ?_, ?_, ?_, ?_, (hdec'.1 κ hκ).1, es_image_init_eq_projLast κ⟩
  · exact Finset.mem_image.mpr ⟨κ, hκ, rfl⟩
  · intro κ' hκ'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hκ'
    rw [es_image_init_eq_projLast]
    exact S.proj (hΩ c hc)
  · rintro z ⟨z0, hz0, rfl⟩
    have hz := hcube hz0
    rw [es_mem_inCubeSet_iff (p := p) (N := n + 1)] at hz
    rw [es_mem_inCubeSet_iff (p := p) (N := n)]
    intro j
    have h1 : (Fin.castSucc (Fin.natAdd p j) : Fin (p + n + 1)) =
        Fin.natAdd p (Fin.castSucc j) := by
      apply Fin.ext
      simp
    simp only [Fin.init]
    rw [h1]
    exact hz (Fin.castSucc j)
  · intro l hl
    obtain ⟨y, hy⟩ := hne l hl
    exact ⟨Fin.init y, Fin.append (n := n + 1) l y, hy, es_init_append l y⟩
  · intro z hz
    have hz' := hcube hz
    rw [es_mem_inCubeSet_iff (p := p) (N := n + 1)] at hz'
    have h2 := hz' (Fin.last n)
    rwa [Fin.natAdd_last] at h2

end Work.WilG4c
