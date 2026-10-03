import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.BasinSC.defs
import Submission.Work.BasinSC.cover_basic
import Submission.Work.BasinSC.step
import Submission.Work.HornTopo.horn_topo

/-!
# The tower of preimages of the petal

For the setup `IsF0Setup f₀ D₀ B c` with §4.1 data `d : ParabData f₀ D₀`, the immediate basin is
exhausted by the increasing sequence

`V n = {z | f₀^[n] z ∈ d.Ωp} ∩ B`

of sets whose connected components are simply connected.  The `n`-th approximation carries the
whole fundamental-group information of `B` up to level `n`, so `Hom(π₁ B, ℝ) = 0` follows from
`Hom(π₁ (component of V n), ℝ) = 0` for every `n`.
-/

open Set Metric Filter Topology MandelDim

namespace Work.BasinSC

variable {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}

/-- The `n`-th level of the tower: points of the immediate basin whose `n`-th iterate lies in the
attracting petal. -/
def tower (f₀ : ℂ → ℂ) (B Ωp : Set ℂ) (n : ℕ) : Set ℂ := {z : ℂ | (f₀^[n]) z ∈ Ωp} ∩ B

variable (hF0 : IsF0Setup f₀ D₀ B c) (d : ParabData f₀ D₀)

lemma tower_subset_B (n : ℕ) : tower f₀ B d.Ωp n ⊆ B := inter_subset_right

lemma tower_mono (n : ℕ) : tower f₀ B d.Ωp n ⊆ tower f₀ B d.Ωp (n + 1) := by
  intro z hz
  refine ⟨?_, hz.2⟩
  have h1 : (f₀^[n]) z ∈ d.Ωp := hz.1
  have h2 : f₀ ((f₀^[n]) z) ∈ d.Ωp := d.Ωp_maps h1
  simpa [Function.iterate_succ_apply'] using h2

lemma tower_mono_le {m n : ℕ} (h : m ≤ n) : tower f₀ B d.Ωp m ⊆ tower f₀ B d.Ωp n := by
  induction h with
  | refl => exact subset_rfl
  | step hle ih => exact ih.trans (tower_mono (d := d) _)

lemma tower_zero (hF0 : IsF0Setup f₀ D₀ B c) : tower f₀ B d.Ωp 0 = d.Ωp := by
  have hΩB : d.Ωp ⊆ B := Work.HornTopo.omega_subset_B hF0 d
  ext z
  simp only [tower, Set.mem_inter_iff, Function.iterate_zero, id_eq]
  exact ⟨fun h => h.1, fun h => ⟨h, hΩB h⟩⟩

/-- Every point of the immediate basin enters the petal, so the tower exhausts the basin. -/
lemma tower_exhaust (hF0 : IsF0Setup f₀ D₀ B c) :
    (⋃ n, tower f₀ B d.Ωp n) = B := by
  obtain ⟨hgerm, hB, -, -, -⟩ := hF0
  have hzero : (0 : ℂ) ∉ ParabolicBasin f₀ D₀ :=
    Work.Parab.basinEnters.zero_not_mem_parabolicBasin hgerm
  have hBbasin : B ⊆ ParabolicBasin f₀ D₀ := hB.2.2.1
  have hmap : MapsTo f₀ B B := hB.2.2.2.2.1
  ext z
  simp only [Set.mem_iUnion, tower, Set.mem_inter_iff]
  constructor
  · rintro ⟨n, h1, h2⟩; exact h2
  · intro hz
    have hne : ∀ n : ℕ, (f₀^[n]) z ≠ 0 := by
      intro n hn
      have hiterB : ∀ k : ℕ, (f₀^[k]) z ∈ B := by
        intro k
        induction k with
        | zero => simpa using hz
        | succ j ih => simpa [Function.iterate_succ_apply'] using hmap ih
      exact hzero (hn ▸ hBbasin (hiterB n))
    obtain ⟨m, hm⟩ := d.basin_enter z (hBbasin hz) hne
    exact ⟨m, hm, hz⟩

end Work.BasinSC
