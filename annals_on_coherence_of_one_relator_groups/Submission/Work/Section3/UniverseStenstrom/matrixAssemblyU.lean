import Mathlib

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

universe u

namespace Work.Section3.UniverseStenstrom

open Matrix

/-- **Mazet matrix assembly.**  Given the Mazet data attached to a tensor relation
(`∑_s s * f (a μ s) + f (astar μ) = 0`, `t s = ∑_μ f (a μ s) * z μ`, `t s ∈ f(R)`,
`d = -∑_μ f (astar μ) * z μ`), the element `d` is the `(0,0)` entry of a product
`X * f(P) * Y` of matrices over `S` with `X * f(P)` a row over `f(R)` and `f(P) * Y` a column
over `f(R)`.

The construction: let `U` be the finite set of `s : S` on which some `a μ` is supported, index
the matrices by `U ⊕ Fin m` (via an enumeration of that finite type), and set

* `X 0 (inl i) = i`, `X 0 (inr μ) = 0`,
* `P (inl i) (inr μ) = a μ i` and `P = 0` on all other blocks,
* `Y (inr μ) 0 = z μ`, `Y (inl i) 0 = 0`.

Then `X * f(P) = [-∑_i i f (a μ i)]_μ = [-f (astar μ)]_μ` by the relation, and
`f(P) * Y = [∑_μ f (a μ i) z μ]_i = [t i]_i` lies over `f(R)` by `hfin`; the `(0,0)` entry of
the product is `-∑_μ f (astar μ) z μ = d`. -/
theorem matrixAssemblyU {R S : Type u} [Ring R] [Ring S] (f : R →+* S) (d : S) (m : ℕ)
    (a : Fin m → S →₀ R) (astar : Fin m → R) (z : Fin m → S) (t : S →₀ S)
    (hrel : ∀ mu, (a mu).sum (fun s r => s * f r) + f (astar mu) = 0)
    (hrow : ∀ s, t s = ∑ mu, f (a mu s) * z mu)
    (hfin : ∀ s, t s ∈ Set.range f)
    (hstar : d = - ∑ mu, f (astar mu) * z mu) :
    ∃ (n : ℕ) (X : Matrix (Fin 1) (Fin n) S) (P : Matrix (Fin n) (Fin n) R)
      (Y : Matrix (Fin n) (Fin 1) S),
      (∃ P' : Matrix (Fin 1) (Fin n) R, X * P.map f = P'.map f) ∧
      (∃ Q' : Matrix (Fin n) (Fin 1) R, P.map f * Y = Q'.map f) ∧
      d = (X * P.map f * Y) 0 0 := by
  classical
  -- The finite set of `s : S` on which one of the `a μ` is supported.
  set U : Finset S := Finset.univ.biUnion (fun μ : Fin m => (a μ).support) with hU
  have hUmem : ∀ s : S, s ∈ U ↔ ∃ μ : Fin m, a μ s ≠ 0 := by
    intro s
    rw [hU, Finset.mem_biUnion]
    exact ⟨fun ⟨μ, _, hs⟩ => ⟨μ, Finsupp.mem_support_iff.mp hs⟩,
      fun ⟨μ, hμ⟩ => ⟨μ, Finset.mem_univ μ, Finsupp.mem_support_iff.mpr hμ⟩⟩
  -- An enumeration of the double index set `↥U ⊕ Fin m`.
  set e : (↥U ⊕ Fin m) ≃ Fin (U.card + m) :=
    (Equiv.sumCongr (Finset.equivFin U) (Equiv.refl (Fin m))).trans finSumFinEquiv with he
  -- The relation `∑ i ∈ U, i * f (a μ i) = - f (astar μ)`.
  have hsum : ∀ μ : Fin m, (∑ i : ↥U, (i : S) * f (a μ (i : S))) = - f (astar μ) := by
    intro μ
    have hsub : (a μ).support ⊆ U :=
      fun s hs => (hUmem s).mpr ⟨μ, Finsupp.mem_support_iff.mp hs⟩
    rw [show (∑ i : ↥U, (i : S) * f (a μ (i : S))) = ∑ x ∈ U, x * f (a μ x) from by
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach U (fun x => x * f (a μ x))]
    rw [← Finset.sum_subset hsub (fun x _ hx => by
      have h0 : a μ x = 0 := by
        by_contra hne
        exact hx (Finsupp.mem_support_iff.mpr hne)
      simp [h0])]
    exact eq_neg_of_add_eq_zero_left (hrel μ)
  -- The matrices.
  let X : Matrix (Fin 1) (Fin (U.card + m)) S :=
    fun _ k => Sum.elim (fun i : ↥U => (i : S)) (fun _ : Fin m => (0 : S)) (e.symm k)
  let P : Matrix (Fin (U.card + m)) (Fin (U.card + m)) R :=
    fun k l => Sum.elim
      (fun i : ↥U => Sum.elim (fun _ : ↥U => (0 : R)) (fun μ : Fin m => a μ (i : S))
        (e.symm l))
      (fun _ : Fin m => (0 : R)) (e.symm k)
  let Y : Matrix (Fin (U.card + m)) (Fin 1) S :=
    fun k _ => Sum.elim (fun _ : ↥U => (0 : S)) (fun μ : Fin m => z μ) (e.symm k)
  let P' : Matrix (Fin 1) (Fin (U.card + m)) R :=
    fun _ l => Sum.elim (fun _ : ↥U => (0 : R)) (fun μ : Fin m => - astar μ) (e.symm l)
  let y : ↥U → R := fun i => Classical.choose (hfin (i : S))
  have hy : ∀ i : ↥U, f (y i) = t (i : S) := fun i => Classical.choose_spec (hfin (i : S))
  let Q' : Matrix (Fin (U.card + m)) (Fin 1) R :=
    fun k _ => Sum.elim (fun i : ↥U => y i) (fun _ : Fin m => (0 : R)) (e.symm k)
  -- `X * f(P)` is the row `(- f (astar μ))_μ` over `f(R)`.
  have h1 : X * P.map f = P'.map f := by
    ext i l
    fin_cases i
    obtain ⟨k, rfl⟩ := e.surjective l
    rcases k with j | μ
    · rw [Matrix.mul_apply, ← Equiv.sum_comp e, Fintype.sum_sum_type]
      simp only [Matrix.map_apply]
      simp [X, P, P']
    · rw [Matrix.mul_apply, ← Equiv.sum_comp e, Fintype.sum_sum_type]
      simp only [Matrix.map_apply]
      simp only [X, P, P', Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
      rw [hsum μ]
      simp [map_neg]
  -- `f(P) * Y` is the column `(t i)_i` over `f(R)`.
  have h2 : P.map f * Y = Q'.map f := by
    ext k i
    fin_cases i
    obtain ⟨x, rfl⟩ := e.surjective k
    rcases x with j | ν
    · rw [Matrix.mul_apply, ← Equiv.sum_comp e, Fintype.sum_sum_type]
      simp only [Matrix.map_apply]
      simp only [X, P, Y, Q', Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
      rw [← hrow (j : S), hy j]
      simp
    · rw [Matrix.mul_apply, ← Equiv.sum_comp e, Fintype.sum_sum_type]
      simp only [Matrix.map_apply]
      simp [X, P, Y, Q']
  refine ⟨U.card + m, X, P, Y, ⟨P', h1⟩, ⟨Q', h2⟩, ?_⟩
  rw [h1, Matrix.mul_apply, ← Equiv.sum_comp e, Fintype.sum_sum_type]
  simp only [Matrix.map_apply]
  simp only [X, P', Y, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
  rw [hstar]
  simp [map_neg, neg_mul, Finset.sum_neg_distrib]

end Work.Section3.UniverseStenstrom
