import Mathlib
import Submission.Work.WilkiesH.Defs
import Submission.Work.WilkiesH.Count.exists_boxCover_openCube

namespace Work.WilkiesH.Interp

open WilkiesDesign

/-- Every grid box `Count.boxSet μ N c` is convex: it is the intersection of the
(convex) open cube with a product of closed intervals, one per coordinate. -/
lemma convex_boxSet (μ N : ℕ) (c : Fin μ → ℕ) :
    Convex ℝ (Work.WilkiesH.Count.boxSet μ N c) := by
  have hcube : Convex ℝ (WilkiesDesign.openCube μ) := by
    intro x hx y hy a b ha hb hab i
    have key := (convex_Ioo (0 : ℝ) 1) (hx i) (hy i) ha hb hab
    simpa [Pi.smul_apply, Pi.add_apply] using key
  rw [Work.WilkiesH.Count.boxSet]
  refine hcube.inter ?_
  intro x hx y hy a b ha hb hab l
  have key := (convex_Icc ((c l : ℝ) / N) (((c l : ℝ) + 1) / N)) (hx l) (hy l) ha hb hab
  simpa [Pi.smul_apply, Pi.add_apply] using key

theorem exists_convexBoxCover_openCube (μ : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : Finset (Set (Fin μ → ℝ)),
      (∀ b ∈ C, Convex ℝ b) ∧
      (∀ b ∈ C, b ⊆ WilkiesDesign.openCube μ) ∧
      (∀ b ∈ C, b.Nonempty) ∧
      (∀ b ∈ C, ∀ u ∈ b, ∀ v ∈ b, ∀ l : Fin μ, |u l - v l| ≤ ρ) ∧
      (∀ u ∈ WilkiesDesign.openCube μ, ∃ b ∈ C, u ∈ b) ∧
      C.card ≤ (Nat.ceil (1 / ρ)) ^ μ := by
  classical
  set N := Nat.ceil (1 / ρ) with hNdef
  have hρinv : (0 : ℝ) < 1 / ρ := by positivity
  have hNpos : 0 < N := Nat.ceil_pos.mpr hρinv
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNle : 1 / ρ ≤ (N : ℝ) := Nat.le_ceil (1 / ρ)
  have hNinv : (1 : ℝ) / N ≤ ρ := by
    rw [div_le_iff₀ hNposR]
    calc (1 : ℝ) = ρ * (1 / ρ) := by field_simp
      _ ≤ ρ * (N : ℝ) := mul_le_mul_of_nonneg_left hNle hρ.le
  refine ⟨((Finset.univ : Finset (Fin μ → Fin N)).image
      (fun c => Work.WilkiesH.Count.boxSet μ N (fun l => (c l : ℕ)))).filter
        (fun b => b.Nonempty), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    rcases Finset.mem_filter.mp hb with ⟨hb, _⟩
    rcases Finset.mem_image.mp hb with ⟨c, _, rfl⟩
    exact convex_boxSet μ N (fun l => (c l : ℕ))
  · intro b hb
    rcases Finset.mem_filter.mp hb with ⟨hb, _⟩
    rcases Finset.mem_image.mp hb with ⟨c, _, rfl⟩
    exact Work.WilkiesH.Count.boxSet_subset μ N _
  · intro b hb
    exact (Finset.mem_filter.mp hb).2
  · intro b hb u hu v hv l
    rcases Finset.mem_filter.mp hb with ⟨hb, _⟩
    rcases Finset.mem_image.mp hb with ⟨c, _, rfl⟩
    exact Work.WilkiesH.Count.boxSet_diam hNinv (fun l => (c l : ℕ)) hu hv l
  · intro u hu
    rcases Work.WilkiesH.Count.boxSet_cover (μ := μ) hNpos hu with ⟨c, hc⟩
    exact ⟨_, Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩, ⟨u, hc⟩⟩, hc⟩
  · calc (((Finset.univ : Finset (Fin μ → Fin N)).image
            (fun c => Work.WilkiesH.Count.boxSet μ N (fun l => (c l : ℕ)))).filter
            (fun b => b.Nonempty)).card
        ≤ ((Finset.univ : Finset (Fin μ → Fin N)).image
            (fun c => Work.WilkiesH.Count.boxSet μ N (fun l => (c l : ℕ)))).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ (Finset.univ : Finset (Fin μ → Fin N)).card := Finset.card_image_le
      _ = N ^ μ := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

end Work.WilkiesH.Interp
