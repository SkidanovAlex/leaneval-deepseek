/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The Freiheitssatz of the domain for the two-letter case

This is the Freiheitssatz input of the target `Work.OROneRel.twoLetter_hnnData`: for the two-letter
relator `u = a ^ p * b ^ q` (coprime exponents) and a window satisfying the band and tree conditions,
the class map `winRho` of the window basis satisfies

    `winRho x ∈ ⟪u ^ l⟫  →  x ∈ ⟪v ^ l⟫`,   `v = winRoot Wt c lo hi u`,

i.e. the π₁-injectivity of the `Z`-domain of the two-letter case.  The proof is in
`Submission.Work.OROneRel.twoLetterFreiheitssatz`; this file only records it in the shape the target's
assembly consumes.
-/
import Mathlib
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.winAssembly
import Submission.Work.OROneRel.twoLetterFreiheitssatz

namespace Work.OROneRel

theorem tlFreiheitssatz (p q l : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hl : 1 ≤ l)
    (hcop : Nat.Coprime p q)
    {c : Fin 2 → ℤ} {τ : FreeGroup (Fin 2)} {lo hi : ℤ} {Wt : ℤ → FreeGroup (Fin 2)}
    (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i)
    (hcu : cohom c (tlU p q) = 1)
    (hτ : cohom c τ = Multiplicative.ofAdd 1)
    (hwin : ∀ e ∈ decor c 0 (wordOf (tlU p q)), coverEdge e ∈ winE c lo hi)
    (hone : ∀ k : ℤ, k ≠ 0 →
      ¬ (∀ e ∈ decor c 0 (wordOf (tlU p q)),
          lo ≤ e.1.2 + k ∧ lo ≤ e.1.2 + c e.1.1 + k ∧ e.1.2 + k ≤ hi ∧ e.1.2 + c e.1.1 + k ≤ hi))
    (htree : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ e ∈ decor c 0 (wordOf (Wt i)), coverEdge e ∈ winTree Wt c lo hi) :
    ∀ x : FreeGroup (winBeta Wt c lo hi),
      winRho Wt c lo hi x ∈
          Subgroup.normalClosure ({tlU p q ^ l} : Set (FreeGroup (Fin 2))) →
        x ∈ Subgroup.normalClosure
          ({winRoot Wt c lo hi (tlU p q) ^ l} : Set (FreeGroup (winBeta Wt c lo hi))) :=
  twoLetterFreiheitssatz p q l hp hq hl hcop hW0 hcoh hcu hτ hwin hone htree

end Work.OROneRel
