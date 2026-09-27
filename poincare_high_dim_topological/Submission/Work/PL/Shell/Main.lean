import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Shell.Basic
import Submission.Work.PL.Shell.sd_iter_shelling_strong
import Submission.Work.PL.Shell.shellOrd_mem_sdIter

/-!
# A4 `PL/Shell`: G4 (shelling of the barycentric subdivision) and its corollaries

Main exports of the area (see `NOTES_Shell.md`):

* `Work.PL.Shell.sd_iter_shelling` — G4 of the blueprint §2, verbatim (existential form).
* `Work.PL.Shell.sd_iter_shelling_strong` — the explicit form with the concrete order
  `shellOrd`, the attaching sets `shellSplit`, together with `Nodup`, `card`, `⊆ simp Δ`
  and the covering identity (this is the form the engulfing area A9 consumes).
* `Work.PL.Shell.cone_shelling` — the cone `aσ` from its boundary `aσ̇`
  (deliverable item 4).
-/

open Set Metric Finset
open scoped BigOperators

namespace Work.PL.Shell

noncomputable section

/-- **G4 (statement of the blueprint §2).**  The `r`-fold barycentric subdivision of the
simplex `Δ` can be ordered so that each simplex attaches to the floor
`B = ⋃_{w ∈ τ₁} simp (Δ \ {w})` and the previous simplices along a non-empty proper union
of its facets, the union of the simplices being `simp Δ`. -/
theorem sd_iter_shelling {N : ℕ} (r : ℕ) (Δ : Finset (PL.E N))
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    (τ₁ : Finset (PL.E N)) (h₁ : τ₁.Nonempty) (h₂ : τ₁ ⊂ Δ) :
    let B : Set (PL.E N) := ⋃ w ∈ τ₁, PL.simp (Δ.erase w)
    ∃ ord : List (Finset (PL.E N)),
      (∀ i (hi : i < ord.length), ∃ τ₁' : Finset (PL.E N),
        τ₁'.Nonempty ∧ τ₁' ⊂ ord.get ⟨i, hi⟩ ∧
        PL.simp (ord.get ⟨i, hi⟩) ∩ (B ∪ preUnion ord i) =
          ⋃ w ∈ τ₁', PL.simp ((ord.get ⟨i, hi⟩).erase w)) ∧
      (⋃ τ ∈ ord.toFinset, PL.simp τ) = PL.simp Δ := by
  obtain ⟨_, hmain, hcov⟩ := sd_iter_shelling_strong r Δ hΔ τ₁ h₁ h₂
  refine ⟨shellOrd r Δ τ₁, ?_, hcov⟩
  intro i hi
  obtain ⟨_, _, hne, hprop, heq⟩ := hmain i hi
  exact ⟨shellSplit r Δ τ₁ i, hne, hprop, heq⟩

/-- The floor of the `r`-fold subdivision of the cone `aσ`, i.e. the union of the facets
opposite the vertices of `σ`, is `aσ̇` (the union of the cones `a * (σ \ {w})`). -/
theorem cone_floor {N : ℕ} (a : PL.E N) (σ : Finset (PL.E N)) (ha : a ∉ σ) :
    (⋃ w ∈ σ, PL.simp ((insert a σ).erase w)) =
      ⋃ w ∈ σ, PL.simp (insert a (σ.erase w)) := by
  refine iUnion₂_congr fun w hw => ?_
  congr 1
  ext x
  have haw : a ≠ w := fun h => ha (h ▸ hw)
  simp only [Finset.mem_erase, Finset.mem_insert]
  constructor
  · rintro ⟨hxw, hxa | hxs⟩
    · exact Or.inl hxa
    · exact Or.inr ⟨hxw, hxs⟩
  · rintro (hxa | ⟨hxw, hxs⟩)
    · exact ⟨by rw [hxa]; exact haw, Or.inl hxa⟩
    · exact ⟨hxw, Or.inr hxs⟩

/-- **Shelling of the cone `aσ` from its boundary `aσ̇`** (deliverable item 4): the pair
`(Δ, τ₁) = (insert a σ, σ)` gives the floor `⋃_{w ∈ σ} simp (insert a (σ \ {w})) = aσ̇`. -/
theorem cone_shelling {N : ℕ} (r : ℕ) (a : PL.E N) (σ : Finset (PL.E N))
    (ha : a ∉ σ) (hne : σ.Nonempty)
    (hΔ : AffineIndependent ℝ ((↑) : ↥(insert a σ) → PL.E N)) :
    let B : Set (PL.E N) := ⋃ w ∈ σ, PL.simp (insert a (σ.erase w))
    (shellOrd r (insert a σ) σ).Nodup ∧
    (∀ i (hi : i < (shellOrd r (insert a σ) σ).length),
        ((shellOrd r (insert a σ) σ).get ⟨i, hi⟩).card = (insert a σ).card ∧
        PL.simp ((shellOrd r (insert a σ) σ).get ⟨i, hi⟩) ⊆ PL.simp (insert a σ) ∧
        (shellSplit r (insert a σ) σ i).Nonempty ∧
        (shellSplit r (insert a σ) σ i) ⊂ (shellOrd r (insert a σ) σ).get ⟨i, hi⟩ ∧
        PL.simp ((shellOrd r (insert a σ) σ).get ⟨i, hi⟩) ∩
            (B ∪ preUnion (shellOrd r (insert a σ) σ) i)
          = ⋃ w ∈ shellSplit r (insert a σ) σ i,
              PL.simp (((shellOrd r (insert a σ) σ).get ⟨i, hi⟩).erase w)) ∧
    (⋃ τ ∈ (shellOrd r (insert a σ) σ).toFinset, PL.simp τ) = PL.simp (insert a σ) := by
  have hsub : σ ⊂ insert a σ := Finset.ssubset_insert ha
  obtain ⟨hnd, hmain, hcov⟩ := sd_iter_shelling_strong r (insert a σ) hΔ σ hne hsub
  rw [cone_floor a σ ha] at hmain
  exact ⟨hnd, hmain, hcov⟩

/-- The union over the members of a list is the union over its `toFinset`. -/
theorem iUnion_list_toFinset {N : ℕ} (ord : List (Finset (PL.E N))) :
    (⋃ τ ∈ ord, PL.simp τ) = ⋃ τ ∈ ord.toFinset, PL.simp τ := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨τ, hτ, hx⟩; exact ⟨τ, List.mem_toFinset.mpr hτ, hx⟩
  · rintro ⟨τ, hτ, hx⟩; exact ⟨τ, List.mem_toFinset.mp hτ, hx⟩

/-- **The `shell` field of the lead's `SubdivTools` (§7.2)**: with
`ord = shellOrd r Δ τ₁` and `τ₁' = shellSplit`, the ordered list consists of faces of the
`r`-fold subdivision of the ambient complex `K` of size `card Δ` inside `simp Δ`, covers
`simp Δ`, and attaches along `B ∪ (previous simplices)` in the prescribed way.
`preUnion ord i` is the union of the first `i` members of `ord` (the lead's
`⋃ j < i, simp ord[j]`). -/
theorem shell_form {N : ℕ} (r : ℕ) (K : PL.Cx N) (hK : K.faces.Finite)
    (Δ τ₁ : Finset (PL.E N)) (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    (hΔK : Δ ∈ K.faces) (h₁ : τ₁.Nonempty) (h₂ : τ₁ ⊂ Δ) :
    let B : Set (PL.E N) := ⋃ w ∈ τ₁, PL.simp (Δ.erase w)
    ∃ ord : List (Finset (PL.E N)), ord.Nodup ∧
      (∀ τ ∈ ord, τ ∈ (Work.PL.Subdiv.sdIter r K hK).faces ∧ τ.card = Δ.card ∧
        PL.simp τ ⊆ PL.simp Δ) ∧
      (⋃ τ ∈ ord, PL.simp τ) = PL.simp Δ ∧
      (∀ i (hi : i < ord.length), ∃ τ₁' : Finset (PL.E N), τ₁'.Nonempty ∧ τ₁' ⊂ ord.get ⟨i, hi⟩ ∧
        PL.simp (ord.get ⟨i, hi⟩) ∩ (B ∪ preUnion ord i)
          = ⋃ w ∈ τ₁', PL.simp ((ord.get ⟨i, hi⟩).erase w)) := by
  obtain ⟨hnd, hmain, hcov⟩ := sd_iter_shelling_strong r Δ hΔ τ₁ h₁ h₂
  refine ⟨shellOrd r Δ τ₁, hnd, ?_, ?_, ?_⟩
  · intro τ hτ
    obtain ⟨⟨i, hi⟩, rfl⟩ := List.mem_iff_get.mp hτ
    obtain ⟨hc, hs, -, -, -⟩ := hmain i hi
    exact ⟨shellOrd_mem_sdIter r K hK Δ τ₁ hΔK h₁ h₂ _ (List.get_mem _ _), hc, hs⟩
  · rw [iUnion_list_toFinset]; exact hcov
  · intro i hi
    obtain ⟨-, -, hne, hprop, heq⟩ := hmain i hi
    exact ⟨shellSplit r Δ τ₁ i, hne, hprop, heq⟩

end

end Work.PL.Shell
