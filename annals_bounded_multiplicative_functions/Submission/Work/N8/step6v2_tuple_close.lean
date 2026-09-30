import Mathlib
import Submission.Work.N8.step6v2_defs
import Submission.Work.N8.step6_defs
import Submission.Work.N8.walk_products_close
import Submission.Work.N8.walk_products_close_gen
import Submission.Work.N8.step6v2_close_arith
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Closeness of the two prime-tuple products along a closed walk (`200·L` variant)

Along a closed walk `j ↦ j + 1 (mod ℓ)` of the MRT graph on `T`, the vertices `pos (w j) ≥ D`
satisfy `pos (w j) ≈ (p₂ j / p₁ j) · pos (w (j+1))` with error at most `200 · L`, where the
primes `p₁ j, p₂ j` lie in `[P, 2P]`.  Multiplying the relations around the cycle (this is the
content of `walk_products_close_gen`, the constant-`c` version of `walk_products_close`) gives

`|∏ p₂ j - ∏ p₁ j| ≤ ℓ · (2P)^ℓ · (200 · L / D)`,

and the hypothesis `N · L ≤ 10 · D` converts the factor `200 · L / D` into `2000 / N`, which is
absorbed by the window constant `step6C0v2 ℓ = max 1 (4000·ℓ·2^ℓ)`:

`ℓ · (2P)^ℓ · (200·L/D) = 2000 · ℓ · 2^ℓ · P^ℓ / N ≤ step6C0v2 ℓ · P^ℓ / N`.

This is the `C₀·P^ℓ/N` proximity hypothesis of the counting lemma `step6_q0_bound_v2`, read off
from a genuine closed walk rather than assumed for an arbitrary pair of tuples.
-/

namespace Work.N8

theorem step6v2_tuple_close {V : Type} [Fintype V] [DecidableEq V]
    (Adj : V → V → Prop) [DecidableRel Adj]
    (T : Finset V) (pos : V → ℝ) (pr : V → V → ℕ × ℕ) (ℓ : ℕ) (hℓ2 : 2 ≤ ℓ)
    (P N L D : ℝ) (hD : 0 < D) (hL : 0 < L) (hP : 1 ≤ P) (hN : 0 < N)
    (hLDN : N * L ≤ 10 * D)
    (hedge : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' →
      Work.BMF.IsPrimeIn P (2 * P) (pr v v').1 ∧ Work.BMF.IsPrimeIn P (2 * P) (pr v v').2)
    (hgeo : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' →
      |pos v - (((pr v v').2 : ℕ) : ℝ) / (((pr v v').1 : ℕ) : ℝ) * pos v'| ≤ 200 * L)
    (hposD : ∀ v ∈ T, D ≤ pos v)
    (w : Fin ℓ → V) (hw : w ∈ Work.N8.step6Walks Adj T ℓ) :
    |((∏ i, Work.N8.step6Tuple2 ℓ pr w i : ℕ) : ℝ) -
        ((∏ i, Work.N8.step6Tuple1 ℓ pr w i : ℕ) : ℝ)|
      ≤ step6C0v2 ℓ * P ^ ℓ / N := by
  classical
  obtain ⟨hwT, hwAdj⟩ := mem_step6Walks.mp hw
  have hm : 1 ≤ ℓ := by omega
  -- the two spellings of the successor index `⟨(j+1) % ℓ, _⟩` and `step6next ℓ j` agree
  have hidx : ∀ j : Fin ℓ,
      (⟨((j : ℕ) + 1) % ℓ, Nat.mod_lt _ (by omega)⟩ : Fin ℓ) = step6next ℓ j :=
    fun j => Fin.ext rfl
  -- the products of the edge labels around the closed walk are within `ℓ · (2P)^ℓ · (200L/D)`
  have hb := walk_products_close_gen ℓ hm P L D 200 (by norm_num) (fun j => pos (w j))
    (fun j => (pr (w j) (w (step6next ℓ j))).1)
    (fun j => (pr (w j) (w (step6next ℓ j))).2)
    hD hL hP (fun j => hposD (w j) (hwT j))
    (fun j => hedge (w j) (hwT j) (w (step6next ℓ j)) (hwT _) (hwAdj j))
    (fun j => by
      rw [hidx j]
      exact hgeo (w j) (hwT j) (w (step6next ℓ j)) (hwT _) (hwAdj j))
  -- `200·L/D ≤ 2000/N` and the window constant absorb the rest
  exact le_trans hb (step6v2_close_arith ℓ P N L D hD hL hP hN hLDN)

end Work.N8
