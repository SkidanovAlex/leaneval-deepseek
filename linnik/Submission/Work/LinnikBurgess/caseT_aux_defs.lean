import Mathlib
import Submission.Work.LinnikBurgess.frame_count_prov_defs
import Submission.Work.LinnikBurgess.frame_count_prov_aux.caseT_defs

/-!
# Auxiliary definitions for the Case-T estimate (`sumT_le`)

`Afact g` is the finite set of ordered factorisations `g = a 0 * a 1 * a 2` of `g` into three
natural numbers (all of them divisors of `g` automatically).  It is the index set of the
divisor expansion of the divisibility condition `g ∣ |x₀-x₁|·|x₀-x₂|·|x₀-γ|` in the Case-T
estimate.
-/

open scoped BigOperators

namespace Work.LinnikBurgess

/-- The ordered factorisations of `g` into three factors. -/
def Afact (g : ℕ) : Finset (Fin 3 → ℕ) :=
  (Fintype.piFinset (fun _ : Fin 3 => g.divisors)).filter (fun a => ∏ k : Fin 3, a k = g)

lemma mem_Afact {g : ℕ} (hg : 0 < g) {a : Fin 3 → ℕ} :
    a ∈ Afact g ↔ (∏ k : Fin 3, a k = g) ∧ ∀ k : Fin 3, a k ∣ g := by
  rw [Afact, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, fun k => (Nat.mem_divisors.mp (h1 k)).1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun k => Nat.mem_divisors.mpr ⟨h2 k, hg.ne'⟩, h1⟩

end Work.LinnikBurgess
