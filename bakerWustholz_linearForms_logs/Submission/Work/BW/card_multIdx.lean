import Mathlib
import Submission.Work.BW.auxpolydefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Cardinality of the multi-index set `MultIdx r T`

`MultIdx r T` is the set of tuples `(t₀, t₁, …, t_{r-1}) ∈ ℕ^r` with `t₀ + t₁ + ⋯ + t_{r-1} ≤ T`,
modelled as `{v : ℕ × (Fin (r-1) → ℕ) // v.1 + ∑ m, v.2 m ≤ T}`.  We show

`Fintype.card (MultIdx r T) = (T + r).choose r`

(the number of weak compositions of at most `T` into `r` parts).  The proof builds an explicit
bijection with the multisets of cardinality `T` over an alphabet of size `r + 1` ("stars and bars")
and applies `Sym.card_sym_eq_choose`.
-/

namespace Work.BW

/-- Regrouping a pair `(a, g) ∈ ℕ × (Fin n → ℕ)` into a tuple on `Fin (n+1)` via `Fin.cons`,
preserving the sum condition `∑ ≤ T`. -/
noncomputable def multIdxConsEquiv (n T : ℕ) :
    {v : ℕ × (Fin n → ℕ) // v.1 + ∑ m, v.2 m ≤ T} ≃
      {w : Fin (n + 1) → ℕ // ∑ i, w i ≤ T} :=
  (Fin.consEquiv (fun _ : Fin (n+1) => ℕ)).subtypeEquiv (fun a => by
    simp [Fin.sum_univ_succ])

/-- Sending a tuple `w : Fin (n+1) → ℕ` with `∑ w ≤ T` to the tuple `Fin.snoc w (T - ∑ w)` on
`Fin (n+2)`, whose entries sum to exactly `T` (adding the slack variable as last coordinate). -/
noncomputable def multIdxSnocEquiv (n T : ℕ) :
    {w : Fin (n + 1) → ℕ // ∑ i, w i ≤ T} ≃ {u : Fin (n + 2) → ℕ // ∑ i, u i = T} where
  toFun w := ⟨Fin.snoc w.1 (T - ∑ i, w.1 i), by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    omega⟩
  invFun u := ⟨Fin.init u.1, by
    have h := u.2
    rw [Fin.sum_univ_castSucc] at h
    have hc : (∑ i : Fin (n+1), Fin.init u.1 i) = ∑ i : Fin (n+1), u.1 i.castSucc := rfl
    rw [hc]
    omega⟩
  left_inv w := Subtype.ext (by simp [Fin.init_snoc])
  right_inv u := Subtype.ext (by
    show Fin.snoc (Fin.init u.1) (T - ∑ i : Fin (n+1), Fin.init u.1 i) = u.1
    have h := u.2
    rw [Fin.sum_univ_castSucc] at h
    have hc : (∑ i : Fin (n+1), Fin.init u.1 i) = ∑ i : Fin (n+1), u.1 i.castSucc := rfl
    rw [hc]
    have hc2 : T - ∑ i : Fin (n+1), u.1 i.castSucc = u.1 (Fin.last (n+1)) := by omega
    rw [hc2]
    exact Fin.snoc_init_self (α := fun _ => ℕ) u.1)

/-- The number of multi-indices `(t₀, …, t_{r-1}) ∈ ℕ^r` with `∑ tᵢ ≤ T` is `(T + r).choose r`. -/
theorem card_multIdx (r T : ℕ) (hr : 1 ≤ r) :
    Fintype.card (MultIdx r T) = (T + r).choose r := by
  have e : MultIdx r T ≃ Sym (Fin ((r-1)+2)) T :=
    (multIdxConsEquiv (r-1) T).trans ((multIdxSnocEquiv (r-1) T).trans
      (Sym.equivNatSumOfFintype (Fin ((r-1)+2)) T).symm)
  rw [Fintype.card_congr e, Sym.card_sym_eq_choose, Fintype.card_fin]
  rw [show ((r-1)+2) + T - 1 = T + r by omega]
  have hh := Nat.choose_symm (n := T + r) (k := r) (by omega)
  rw [show T + r - r = T by omega] at hh
  exact hh

end Work.BW
