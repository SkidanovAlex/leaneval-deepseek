import Mathlib

namespace Work.WilC5

open FirstOrder Language

/-- **Finite satisfiability of one-variable types over a finite parameter set implies
elementary.**  A substructure `S ≤ N` is elementary as soon as every one-variable type over a
*finite* set `A ⊆ S` of parameters which is finitely satisfiable in `N` is realized in `S`
(the hypothesis `h`, stated for all parameter sets that are finite or of cardinality `< κ`).

The proof is Tarski–Vaught.  Given `φ : L.BoundedFormula Empty (n+1)`, `x : Fin n → S` and
`a : N` with `φ` true of `(x, a)` in `N`, take `A := Set.range x` (finite) and let `ψ` be the
`L`-formula with free variables `A ⊕ Fin 1` obtained from `φ` by turning the `n + 1` bound
variables into free variables (`BoundedFormula.toFormula`) and labelling the first `n` of them
by the parameters `x j` and the last one by the single variable.  Then `ψ` is realized in `N`
by `a`, and `p := {ψ}` is finitely satisfiable; `h` supplies `b : S` realizing `ψ`, which by
construction means `φ` is true of `(x, b)` in `N`. -/
theorem IsElementary_of_finSat {L : FirstOrder.Language.{0, 0}} {N : Type} [instN : L.Structure N]
    (S : L.Substructure N) (κ : Cardinal.{0})
    (h : ∀ (A : Set S), (A.Finite ∨ Cardinal.mk A < κ) →
        ∀ (p : Set (L.Formula (A ⊕ Fin 1))),
        (∀ F : Finset (L.Formula (A ⊕ Fin 1)), (∀ φ ∈ F, φ ∈ p) →
          ∃ a : N, ∀ φ ∈ F,
            @FirstOrder.Language.Formula.Realize L N instN (A ⊕ Fin 1) φ
              (Sum.elim (fun x : A => (x : N)) (fun _ : Fin 1 => a))) →
        ∃ a : S, ∀ φ ∈ p,
          @FirstOrder.Language.Formula.Realize L N instN (A ⊕ Fin 1) φ
            (Sum.elim (fun x : A => (x : N)) (fun _ : Fin 1 => a))) :
    S.IsElementary := by
  refine S.isElementary_of_exists fun n φ x a ha => ?_
  -- The finite (hence admissible) parameter set and the associated reindexing.
  let A : Set S := Set.range x
  let f : Fin n → A ⊕ Fin 1 := fun j => Sum.inl ⟨x j, Set.mem_range_self j⟩
  let y0 : A ⊕ Fin 1 := Sum.inr 0
  let sn : Fin (n + 1) → A ⊕ Fin 1 := @Fin.snoc n (fun _ => A ⊕ Fin 1) f y0
  let g : (Empty ⊕ Fin (n + 1)) → (A ⊕ Fin 1) := Sum.elim (fun e : Empty => Empty.elim e) sn
  let ψ : L.Formula (A ⊕ Fin 1) := (φ.toFormula).relabel g
  let xx : Fin n → N := fun j => (x j : N)
  -- Realization of `ψ` coincides with realization of `φ` for every value of the extra variable.
  have hreal : ∀ c : N, ψ.Realize (Sum.elim (fun y : A => (y : N)) (fun _ : Fin 1 => c))
      ↔ φ.Realize default (@Fin.snoc n (fun _ => N) xx c : Fin (n + 1) → N) := by
    intro c
    let w : A ⊕ Fin 1 → N := Sum.elim (fun y : A => (y : N)) (fun _ : Fin 1 => c)
    have key : ∀ i : Fin (n + 1), w (sn i) = @Fin.snoc n (fun _ => N) xx c i := by
      intro i
      induction i using Fin.lastCases with
      | last => simp [w, sn, f, y0, xx]
      | cast j => simp [w, sn, f, y0, xx]
    rw [Formula.realize_relabel, BoundedFormula.realize_toFormula]
    have h1 : (w ∘ g) ∘ Sum.inl = (default : Empty → N) := by
      funext e; exact Empty.elim e
    have h2 : (w ∘ g) ∘ Sum.inr = (@Fin.snoc n (fun _ => N) xx c : Fin (n + 1) → N) := by
      funext i; exact key i
    rw [h1, h2]
  have hAfin : A.Finite := Set.finite_range x
  -- The type `{ψ}` is finitely satisfiable in `N`.
  have hfin : ∀ F : Finset (L.Formula (A ⊕ Fin 1)),
      (∀ φ' ∈ F, φ' ∈ ({ψ} : Set (L.Formula (A ⊕ Fin 1)))) →
      ∃ c : N, ∀ φ' ∈ F,
        @Formula.Realize L N instN (A ⊕ Fin 1) φ'
          (Sum.elim (fun y : A => (y : N)) (fun _ : Fin 1 => c)) := by
    intro F hF
    refine ⟨a, fun φ' hφ' => ?_⟩
    have hiff : φ' = ψ := by simpa using hF φ' hφ'
    rw [hiff]
    exact (hreal a).mpr ha
  obtain ⟨b, hb⟩ := h A (Or.inl hAfin) ({ψ} : Set (L.Formula (A ⊕ Fin 1))) hfin
  refine ⟨b, ?_⟩
  have hbψ := hb ψ (by simp)
  exact (hreal b).mp hbψ

end Work.WilC5
