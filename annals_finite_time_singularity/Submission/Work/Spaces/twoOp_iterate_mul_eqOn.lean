/-
Copyright: work module for the Elgindi finite-time singularity project.

# Iterated Leibniz rule for two derivation-like operators

The two-operator iterated Leibniz rule requested by the `Spaces` area, proved
from the single-operator rule `DerivLike.iterate_mul` of
`Submission.Work.Spaces.DerivLikeBasic`.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.Spaces.DerivLikeBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

/-- Iterated Leibniz rule for two "derivation-like" operators `Z`, `Θ` acting on functions `X → ℝ`.
Each of `Z`, `Θ` satisfies the Leibniz rule for products of `P`-functions, is additive on
`P`-functions, commutes with multiplication by a constant, preserves `P`, and is local (respects
`EqOn`). The class `P` is closed under addition, multiplication and scalar multiplication.
Conclusion: `Z^[m] (Θ^[n] (F * G))` agrees on `s` with the double sum over all ways of splitting the
`n` applications of `Θ` and the `m` applications of `Z` between the two factors.

Proof sketch: prove the one-operator Leibniz rule `Z^[n] (F*G) = ∑ b, (n.choose b) * (Z^[b] F * Z^[n-b] G)`
by induction on `n` (the induction step needs additivity of `Z^[n]` on `P`-functions and the
binomial identity `(n.choose (b-1)) + (n.choose b) = (n+1).choose b`), apply it to `Θ` at level
`n`, then push `Z^[m]` through the resulting finite sum (linearity of iterates over `Finset` sums,
proved by `Finset.induction`), apply the one-operator rule for `Z` to each product, and regroup the
double sum using `Finset.mul_sum`. -/
theorem twoOp_iterate_mul_eqOn {X : Type*} (s : Set X) (P : (X → ℝ) → Prop)
    (Z Θ : (X → ℝ) → (X → ℝ))
    (hPadd : ∀ A B : X → ℝ, P A → P B → P (A + B))
    (hPmul : ∀ A B : X → ℝ, P A → P B → P (A * B))
    (hPsmul : ∀ (c : ℝ) (A : X → ℝ), P A → P (fun p => c * A p))
    (hZadd : ∀ A B : X → ℝ, P A → P B →
      Set.EqOn (Z (A + B)) (fun p => Z A p + Z B p) s)
    (hZmul : ∀ A B : X → ℝ, P A → P B →
      Set.EqOn (Z (A * B)) (fun p => Z A p * B p + A p * Z B p) s)
    (hZcongr : ∀ A B : X → ℝ, Set.EqOn A B s → Set.EqOn (Z A) (Z B) s)
    (hZP : ∀ A : X → ℝ, P A → P (Z A))
    (hZsmul : ∀ (c : ℝ) (A : X → ℝ), P A →
      Set.EqOn (Z (fun p => c * A p)) (fun p => c * Z A p) s)
    (hΘadd : ∀ A B : X → ℝ, P A → P B →
      Set.EqOn (Θ (A + B)) (fun p => Θ A p + Θ B p) s)
    (hΘmul : ∀ A B : X → ℝ, P A → P B →
      Set.EqOn (Θ (A * B)) (fun p => Θ A p * B p + A p * Θ B p) s)
    (hΘcongr : ∀ A B : X → ℝ, Set.EqOn A B s → Set.EqOn (Θ A) (Θ B) s)
    (hΘP : ∀ A : X → ℝ, P A → P (Θ A))
    (hΘsmul : ∀ (c : ℝ) (A : X → ℝ), P A →
      Set.EqOn (Θ (fun p => c * A p)) (fun p => c * Θ A p) s)
    (n m : ℕ) {F G : X → ℝ} (hF : P F) (hG : P G) :
    Set.EqOn ((Z^[m]) ((Θ^[n]) (F * G)))
      (fun p => ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (m + 1),
        ((n.choose a : ℝ) * (m.choose b : ℝ)) *
          ((Z^[b] (Θ^[a] F)) p * (Z^[m - b] (Θ^[n - a] G)) p)) s := by
  have hP : FunClass P := ⟨hPadd, hPmul, hPsmul⟩
  have hZ : DerivLike s P Z := ⟨hZadd, hZmul, hZcongr, hZP, hZsmul⟩
  have hΘ : DerivLike s P Θ := ⟨hΘadd, hΘmul, hΘcongr, hΘP, hΘsmul⟩
  -- Leibniz rule for `Θ` at level `n`.
  have hΘL := hΘ.iterate_mul hP n hF hG
  -- Push `Z^[m]` through the congruence.
  have step1 : Set.EqOn (Z^[m] (Θ^[n] (F * G)))
      (Z^[m] (fun p => ∑ a ∈ Finset.range (n + 1),
        (n.choose a : ℝ) * (Θ^[a] F p * Θ^[n - a] G p))) s :=
    hZ.iterate_congr m hΘL
  -- Each summand lies in `P`.
  have hA : ∀ a ≤ n, P (fun p => (n.choose a : ℝ) * (Θ^[a] F p * Θ^[n - a] G p)) :=
    fun a _ => hP.smul (n.choose a : ℝ) (Θ^[a] F * Θ^[n - a] G)
      (hP.mul (Θ^[a] F) (Θ^[n - a] G)
        (hΘ.preserve_iterate a hF) (hΘ.preserve_iterate (n - a) hG))
  -- Linearity of `Z^[m]` over the `a`-sum.
  have step2 := hZ.iterate_sum_range hP m n hA
  -- Term-by-term: `smul` then the Leibniz rule for `Z` at level `m`.
  have step3 : ∀ a ≤ n, Set.EqOn
      (Z^[m] (fun p => (n.choose a : ℝ) * (Θ^[a] F p * Θ^[n - a] G p)))
      (fun p => ∑ b ∈ Finset.range (m + 1),
        ((n.choose a : ℝ) * (m.choose b : ℝ)) *
          ((Z^[b] (Θ^[a] F)) p * (Z^[m - b] (Θ^[n - a] G)) p)) s := by
    intro a ha
    have hPA : P (Θ^[a] F * Θ^[n - a] G) :=
      hP.mul (Θ^[a] F) (Θ^[n - a] G)
        (hΘ.preserve_iterate a hF) (hΘ.preserve_iterate (n - a) hG)
    have hsm := hZ.iterate_smul m (n.choose a : ℝ) hPA
    have hzm := hZ.iterate_mul hP m (hΘ.preserve_iterate a hF) (hΘ.preserve_iterate (n - a) hG)
    refine hsm.trans ((eqOn_const_mul _ hzm).trans ?_)
    intro p hp
    show (n.choose a : ℝ) * (∑ b ∈ Finset.range (m + 1),
        (m.choose b : ℝ) * (Z^[b] (Θ^[a] F) p * Z^[m - b] (Θ^[n - a] G) p))
      = ∑ b ∈ Finset.range (m + 1),
        ((n.choose a : ℝ) * (m.choose b : ℝ)) *
          ((Z^[b] (Θ^[a] F)) p * (Z^[m - b] (Θ^[n - a] G)) p)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have frame : Set.EqOn
      (fun p => ∑ a ∈ Finset.range (n + 1),
        Z^[m] (fun p => (n.choose a : ℝ) * (Θ^[a] F p * Θ^[n - a] G p)) p)
      (fun p => ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (m + 1),
        ((n.choose a : ℝ) * (m.choose b : ℝ)) *
          ((Z^[b] (Θ^[a] F)) p * (Z^[m - b] (Θ^[n - a] G)) p)) s :=
    eqOn_sum _ (fun a ha => step3 a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)))
  exact step1.trans (step2.trans frame)

end Work.Spaces
