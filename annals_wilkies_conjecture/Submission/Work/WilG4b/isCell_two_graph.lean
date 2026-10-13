import Mathlib
import Submission.Work.Wilkies.Defs

set_option autoImplicit false

namespace Work.WilG4b

private lemma init_snoc_two (x : Fin 1 → ℝ) (t : ℝ) :
    Fin.init (Fin.snoc x t : Fin 2 → ℝ) = x :=
  Fin.init_snoc (n := 1) (α := fun _ => ℝ) t x

private lemma snoc_last_two (x : Fin 1 → ℝ) (t : ℝ) :
    (Fin.snoc x t : Fin 2 → ℝ) (Fin.last 1) = t :=
  Fin.snoc_last (n := 1) (α := fun _ => ℝ) t x

private lemma exists_two_reals_btwn {a b : EReal} (h : a < b) :
    ∃ y z : ℝ, y ≠ z ∧ a < (y : EReal) ∧ (y : EReal) < b ∧
      a < (z : EReal) ∧ (z : EReal) < b := by
  obtain ⟨y, hy1, hy2⟩ := EReal.lt_iff_exists_real_btwn.mp h
  obtain ⟨z, hz1, hz2⟩ := EReal.lt_iff_exists_real_btwn.mp hy1
  exact ⟨y, z, fun hzy => by rw [hzy] at hz2; exact lt_irrefl _ hz2,
    hy1, hy2, hz1, lt_trans hz2 hy2⟩

theorem isCell_two_graph {κ : Set (Fin 2 → ℝ)} {F : (Fin 1 → ℝ) → ℝ}
    (h : WilkiesDesign.IsCell 2 κ) (hne : κ.Nonempty)
    (hsub : κ ⊆ WilkiesDesign.graphOf F) :
    ∃ (C0 : Set (Fin 1 → ℝ)) (ψ : (Fin 1 → ℝ) → ℝ),
      WilkiesDesign.IsCell 1 C0 ∧ ContinuousOn ψ C0 ∧
      κ = {z : Fin 2 → ℝ | Fin.init z ∈ C0 ∧ z (Fin.last 1) = ψ (Fin.init z)} ∧
      (Fin.init '' κ = C0) ∧ (∀ p ∈ C0, ψ p = F p) := by
  cases h with
  | graph hC f hf =>
    rename_i C
    refine ⟨C, f, hC, hf, rfl, ?_, ?_⟩
    · ext p
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz.1
      · intro hp
        refine ⟨Fin.snoc p (f p), ?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · show Fin.init (Fin.snoc p (f p) : Fin 2 → ℝ) ∈ C
            rw [init_snoc_two p (f p)]
            exact hp
          · show (Fin.snoc p (f p) : Fin 2 → ℝ) (Fin.last 1) =
              f (Fin.init (Fin.snoc p (f p) : Fin 2 → ℝ))
            rw [init_snoc_two p (f p), snoc_last_two p (f p)]
        · show Fin.init (Fin.snoc p (f p) : Fin 2 → ℝ) = p
          exact init_snoc_two p (f p)
    · intro p hp
      have hmem : Fin.snoc p (f p) ∈
          {z : Fin 2 → ℝ | Fin.init z ∈ C ∧ z (Fin.last 1) = f (Fin.init z)} := by
        refine ⟨?_, ?_⟩
        · show Fin.init (Fin.snoc p (f p) : Fin 2 → ℝ) ∈ C
          rw [init_snoc_two p (f p)]
          exact hp
        · show (Fin.snoc p (f p) : Fin 2 → ℝ) (Fin.last 1) =
            f (Fin.init (Fin.snoc p (f p) : Fin 2 → ℝ))
          rw [init_snoc_two p (f p), snoc_last_two p (f p)]
      have h1 : (Fin.snoc p (f p) : Fin 2 → ℝ) (Fin.last 1) =
          F (Fin.init (Fin.snoc p (f p) : Fin 2 → ℝ)) := hsub hmem
      rw [init_snoc_two p (f p), snoc_last_two p (f p)] at h1
      exact h1
  | band hC a b ha hb hab =>
    rename_i C
    exfalso
    obtain ⟨z0, hz0⟩ := hne
    obtain ⟨hx0, -, -⟩ := hz0
    obtain ⟨y, z, hyz, hay, hyb, haz, hzb⟩ :=
      exists_two_reals_btwn (hab (Fin.init z0) hx0)
    have key : ∀ t : ℝ, a (Fin.init z0) < (t : EReal) → (t : EReal) < b (Fin.init z0) →
        t = F (Fin.init z0) := by
      intro t ht1 ht2
      have hmem : Fin.snoc (Fin.init z0) t ∈
          {z : Fin 2 → ℝ | Fin.init z ∈ C ∧
            a (Fin.init z) < ((z (Fin.last 1) : ℝ) : EReal) ∧
            ((z (Fin.last 1) : ℝ) : EReal) < b (Fin.init z)} := by
        refine ⟨?_, ?_, ?_⟩
        · show Fin.init (Fin.snoc (Fin.init z0) t : Fin 2 → ℝ) ∈ C
          rw [init_snoc_two (Fin.init z0) t]
          exact hx0
        · show a (Fin.init (Fin.snoc (Fin.init z0) t : Fin 2 → ℝ)) <
              (((Fin.snoc (Fin.init z0) t : Fin 2 → ℝ) (Fin.last 1) : ℝ) : EReal)
          rw [init_snoc_two (Fin.init z0) t, snoc_last_two (Fin.init z0) t]
          exact ht1
        · show (((Fin.snoc (Fin.init z0) t : Fin 2 → ℝ) (Fin.last 1) : ℝ) : EReal) <
              b (Fin.init (Fin.snoc (Fin.init z0) t : Fin 2 → ℝ))
          rw [init_snoc_two (Fin.init z0) t, snoc_last_two (Fin.init z0) t]
          exact ht2
      have h1 : (Fin.snoc (Fin.init z0) t : Fin 2 → ℝ) (Fin.last 1) =
          F (Fin.init (Fin.snoc (Fin.init z0) t : Fin 2 → ℝ)) := hsub hmem
      rw [init_snoc_two (Fin.init z0) t, snoc_last_two (Fin.init z0) t] at h1
      exact h1
    exact hyz ((key y hay hyb).trans (key z haz hzb).symm)

end Work.WilG4b
