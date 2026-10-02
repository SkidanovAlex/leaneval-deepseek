import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.Defs

/-!
# From Kahn's theorem in list form to the paper's Theorem 4.6

`ErdosFaberLovaszConjecture.KahnListStatement` is Kahn's asymptotic
list-edge-colouring theorem for linear hypergraphs in "available lists" form:
any list assignment whose lists have size at least `(1+β)D` (inside a colour
set of size at least `(1+β)D`) admits a proper edge colouring.
`ErdosFaberLovaszConjecture.KahnStatement` is the form used in the paper
(Theorem 4.6): any family `C` of *forbidden* lists of size at most `αD/2`
(inside a colour set of size at least `(1+α)D`) admits a proper edge colouring
avoiding every forbidden list.

The implication: given forbidden lists `C e` of size at most `α D / 2`, the
available colours `L e := univ \ C e` for `e` number at least
`c - α D / 2 ≥ (1+α)D - α D / 2 = (1 + α/2) D`, so the list statement with
`β := α/2` applies and yields a colouring whose labels avoid `C e`.
-/

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

theorem kahnStatement_of_kahnList (h : ErdosFaberLovaszConjecture.KahnListStatement) : ErdosFaberLovaszConjecture.KahnStatement := by
  intro α hα r hr
  -- run the list statement with list-slack β := α / 2
  obtain ⟨D₀, hD₀, hlist⟩ := h (α / 2) (div_pos hα (by norm_num)) r hr
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD n 𝓗 hlin hdeg hsize c hc C hC
  have hDpos : 0 < D := lt_of_lt_of_le hD₀ hD
  -- the colour set is large enough for β := α / 2
  have hcL : (1 + α / 2) * D ≤ (c : ℝ) := by
    have e : (1 + α / 2) * D + (α / 2) * D = (1 + α) * D := by ring
    have hp : (0 : ℝ) < (α / 2) * D := mul_pos (div_pos hα (by norm_num)) hDpos
    linarith
  -- the available lists univ \ C e are large enough
  have hLcard : ∀ e : 𝓗, (1 + α / 2) * D ≤ (((availableLists C) e).card : ℝ) := by
    intro e
    have hsub : C e ⊆ (Finset.univ : Finset (Fin c)) := Finset.subset_univ _
    have hcard : ((availableLists C) e).card = c - (C e).card := by
      simp [availableLists, Finset.card_sdiff, Finset.card_univ, Fintype.card_fin]
    have hcardle : (C e).card ≤ c := by
      simpa using Finset.card_le_card hsub
    have hcast : ((c - (C e).card : ℕ) : ℝ) = (c : ℝ) - ((C e).card : ℝ) :=
      Nat.cast_sub hcardle
    rw [hcard, hcast]
    have key : (1 + α) * D - α * D / 2 = (1 + α / 2) * D := by ring
    linarith [hC e, hc]
  -- the list statement colouring from the available lists avoids C
  obtain ⟨φ, hφ⟩ := hlist D hD n 𝓗 hlin hdeg hsize c hcL (availableLists C) hLcard
  refine ⟨φ, ?_⟩
  intro e
  have hmem : φ.labels e ∈ (availableLists C) e := hφ e
  simp only [availableLists] at hmem
  exact (Finset.mem_sdiff.mp hmem).2

end Work.Deep.Kahn
