import Mathlib
import Submission.Work.WilkiesH.Defs

namespace Work.WilkiesH.Count

open WilkiesDesign

/-- The axis-parallel box cut out of `openCube μ` by the grid of step `1/N` with
lower-left corner index `c`.  The first component of the intersection is `openCube μ`
itself, so every `boxSet` is *contained* in `openCube μ` (which is what the cover
lemma needs). -/
def boxSet (μ N : ℕ) (c : Fin μ → ℕ) : Set (Fin μ → ℝ) :=
  openCube μ ∩ {u | ∀ l, u l ∈ Set.Icc ((c l : ℝ) / N) (((c l : ℝ) + 1) / N)}

lemma boxSet_subset (μ N : ℕ) (c : Fin μ → ℕ) : boxSet μ N c ⊆ openCube μ :=
  Set.inter_subset_left

/-- Every `boxSet` has coordinate diameter at most `1/N`. -/
lemma boxSet_diam {μ N : ℕ} {ρ : ℝ} (hN : (1 : ℝ) / N ≤ ρ)
    (c : Fin μ → ℕ) {u v : Fin μ → ℝ} (hu : u ∈ boxSet μ N c) (hv : v ∈ boxSet μ N c)
    (l : Fin μ) : |u l - v l| ≤ ρ := by
  have hu' : u l ∈ Set.Icc ((c l : ℝ) / N) (((c l : ℝ) + 1) / N) := hu.2 l
  have hv' : v l ∈ Set.Icc ((c l : ℝ) / N) (((c l : ℝ) + 1) / N) := hv.2 l
  have hdiff : ((c l : ℝ) + 1) / N - (c l : ℝ) / N = 1 / (N : ℝ) := by
    rw [div_sub_div_same]
    congr 1
    ring
  have h1 : u l - v l ≤ (1 : ℝ) / N := by linarith [hu'.2, hv'.1, hdiff]
  have h2 : v l - u l ≤ (1 : ℝ) / N := by linarith [hv'.2, hu'.1, hdiff]
  exact (abs_sub_le_iff.mpr ⟨h1, h2⟩).trans hN

/-- The grid boxes with `N` steps in every coordinate cover `openCube μ`. -/
lemma boxSet_cover {μ N : ℕ} (hNpos : 0 < N) {u : Fin μ → ℝ} (hu : u ∈ openCube μ) :
    ∃ c : Fin μ → Fin N, u ∈ boxSet μ N (fun l => (c l : ℕ)) := by
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hlt : ∀ l : Fin μ, Nat.floor ((N : ℝ) * u l) < N := by
    intro l
    have h0 : (0 : ℝ) ≤ (N : ℝ) * u l := mul_nonneg hNposR.le (le_of_lt (hu l).1)
    rw [Nat.floor_lt h0]
    nlinarith [hNposR, (hu l).2]
  refine ⟨fun l => ⟨Nat.floor ((N : ℝ) * u l), hlt l⟩, hu, ?_⟩
  intro l
  have h0 : (0 : ℝ) ≤ (N : ℝ) * u l := mul_nonneg hNposR.le (le_of_lt (hu l).1)
  constructor
  · have h := Nat.floor_le h0
    rw [div_le_iff₀ hNposR]
    nlinarith [h]
  · have h := Nat.lt_floor_add_one ((N : ℝ) * u l)
    rw [le_div_iff₀ hNposR]
    nlinarith [h]

theorem exists_boxCover_openCube (μ : ℕ) {ρ : ℝ} (hρ : 0 < ρ) : ∃ C : Finset (Set (Fin μ → ℝ)), (∀ b ∈ C, b ⊆ WilkiesDesign.openCube μ) ∧ (∀ b ∈ C, ∀ u ∈ b, ∀ v ∈ b, ∀ l : Fin μ, |u l - v l| ≤ ρ) ∧ (∀ u ∈ WilkiesDesign.openCube μ, ∃ b ∈ C, u ∈ b) ∧ C.card ≤ (Nat.ceil (1 / ρ)) ^ μ := by
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
  refine ⟨(Finset.univ : Finset (Fin μ → Fin N)).image
      (fun c => boxSet μ N (fun l => (c l : ℕ))), ?_, ?_, ?_, ?_⟩
  · intro b hb
    rcases Finset.mem_image.mp hb with ⟨c, _, rfl⟩
    exact boxSet_subset μ N _
  · intro b hb u hu v hv l
    rcases Finset.mem_image.mp hb with ⟨c, _, rfl⟩
    exact boxSet_diam hNinv (fun l => (c l : ℕ)) hu hv l
  · intro u hu
    rcases boxSet_cover (μ := μ) hNpos hu with ⟨c, hc⟩
    exact ⟨_, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩, hc⟩
  · calc ((Finset.univ : Finset (Fin μ → Fin N)).image
          (fun c => boxSet μ N (fun l => (c l : ℕ)))).card
        ≤ (Finset.univ : Finset (Fin μ → Fin N)).card := Finset.card_image_le
      _ = N ^ μ := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

end Work.WilkiesH.Count
