/-
  WilE9 / Sharp — the corrected domain construction.

  `Main.lean`'s `DomSet` indexes the conjunction over *all* lists `L` with `|L| ≤ k`, which has
  `Σ_{l ≤ k} n^l` elements — exponential in `k` — while `Gen.inter` adds the per-index degree
  bounds.  Since the target `SharpDeriv` needs a degree bound *polynomial* in `(D,k)`, the index
  is replaced here by the **multi-indices** `μ : Fin n → Fin (k+1)` with `∑ μ ≤ k`, of which there
  are `binom(n+k,n)` — polynomial in `k` for fixed `n`.  Each multi-index is represented by the
  list `repL μ` which repeats the coordinate `i` exactly `μ i` times.

  The price is an order-independence hypothesis (`hperm` in `DomSet2_eq`): the sets `Eset S L` must
  be unchanged by permuting `L`, which is true because both are the graph of the same iterated
  derivative and follows from `SecSpec`/`exSemiPf_snd`.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.Main

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-- The multi-indices of order at most `k` in `n` variables, as a finite type (`binom(n+k,n)`
elements). -/
def Ord2 (n k : ℕ) : Type := {μ : Fin n → Fin (k + 1) // ∑ i, (μ i : ℕ) ≤ k}

/-- The list representing a multi-index: the coordinate `i` repeated `μ i` times, in increasing
order of `i`. -/
def repL {n k : ℕ} (μ : Ord2 n k) : List (Fin n) :=
  (List.finRange n).flatMap fun i => List.replicate ((μ.1 i : ℕ)) i

/-- **The domain of the E9 construction** (multi-index form): the interior of the set of points
at which `f` is continuous and, for the representative order of every multi-index `μ` with
`∑ μ ≤ k`, the set `Eset S (repL μ)` has a defined, unique, continuous section and — when
`|repL μ| < k` — a differentiable one whose derivative is attained by `Eset S (i :: repL μ)`. -/
def DomSet2 (n k : ℕ) (S : List (AEStratum n)) (G : Set (Fin (n + 1) → ℝ)) :
    Set (Fin n → ℝ) :=
  interior (WilkiesDesign.projLast (contPart G) ∩
    ⋂ μ : Ord2 n k,
      (WilkiesDesign.projLast (Eset n S (repL μ)) ∩
        WilkiesDesign.projLast (contPart (Eset n S (repL μ))) ∩
        (if (repL μ).length < k then
          ⋂ i : Fin n, WilkiesDesign.projLast
            (diffPart (Eset n S (repL μ)) i ∩ Eset n S (i :: repL μ))
         else Set.univ)))

end Work.WilE9.Sharp
