import Mathlib
import Submission.Commons.Analysis.Walsh.exists_khintchine_hilbert

namespace Work.BourgainPlan.IonescuWainger

/-- **Khintchine's inequality (lower half) for an arbitrary finite index type.**  For every `p ≥ 1`
there is `c > 0` such that for every finite type `ι`, every Hilbert space `H` over `ℂ` and every
`x : ι → H`,
`c (∑ᵢ ‖xᵢ‖²)^{1/2} ≤ ( avg_{ε : ι→Bool} ‖∑ᵢ εᵢ • xᵢ‖^p )^{1/p}`,
the average being the sum over all `2^|ι|` sign choices divided by `card (ι → Bool)`.  The constant
is uniform in `ι` and `H`.  (`DecidableEq ι` is only there so that `Fintype (ι → Bool)` is
available.)

TOOL: `Submission.Commons.Analysis.Walsh.exists_khintchine_hilbert` (namespace
`Commons.Analysis.Walsh`) proves the lower bound for `x : Fin n → H` with normaliser `2^n`; this
statement is its general-`Fintype` form, obtained by reindexing with
`Fintype.equivFin ι : ι ≃ Fin (Fintype.card ι)`, `Equiv.sum_comp` / `Fintype.sum_equiv` (and
`Equiv.arrowCongr` for the sign vectors), `Fintype.card_fun`, `Fintype.card_bool`. -/
theorem khintchine_hilbert_lower_fintype (p : ℝ) (hp : 1 ≤ p) :
    ∃ c : ℝ, 0 < c ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Type*}
      [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x : ι → H),
      c * (∑ i, ‖x i‖ ^ 2) ^ ((1 : ℝ) / 2) ≤
        ((∑ ε : ι → Bool, ‖∑ i, (if ε i then (1 : ℂ) else -1) • x i‖ ^ p) /
          (Fintype.card (ι → Bool) : ℝ)) ^ ((1 : ℝ) / p) := by
  obtain ⟨c, _C, hcpos, _hCpos, hc⟩ := Commons.Analysis.Walsh.exists_khintchine_hilbert p hp
  refine ⟨c, hcpos, ?_⟩
  intro ι _instι _instD H _instH _instIPS x
  classical
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  set x' : Fin (Fintype.card ι) → H := fun j => x (e.symm j) with hx'
  have hsum_sq : (∑ j : Fin (Fintype.card ι), ‖x' j‖ ^ 2) = ∑ i : ι, ‖x i‖ ^ 2 := by
    simpa [hx'] using Equiv.sum_comp e.symm (fun i : ι => ‖x i‖ ^ 2)
  have hcard : (Fintype.card (ι → Bool) : ℝ) = (2 : ℝ) ^ Fintype.card ι := by
    rw [Fintype.card_fun, Fintype.card_bool]
    push_cast
    ring
  have hsum_sign :
      (∑ ε' : Fin (Fintype.card ι) → Bool,
          ‖∑ i : Fin (Fintype.card ι), (if ε' i then (1 : ℂ) else -1) • x' i‖ ^ p)
        = ∑ ε : ι → Bool, ‖∑ i : ι, (if ε i then (1 : ℂ) else -1) • x i‖ ^ p := by
    rw [← Equiv.sum_comp (e.symm.arrowCongr (Equiv.refl Bool))
        (fun ε : ι → Bool => ‖∑ i : ι, (if ε i then (1 : ℂ) else -1) • x i‖ ^ p)]
    refine Finset.sum_congr rfl fun ε' _ => ?_
    have h1 : ((e.symm.arrowCongr (Equiv.refl Bool)) ε') = fun i => ε' (e i) := by
      ext i; simp
    have h2 : (∑ i : ι,
          (if ((e.symm.arrowCongr (Equiv.refl Bool)) ε') i then (1 : ℂ) else -1) • x i)
        = ∑ j : Fin (Fintype.card ι), (if ε' j then (1 : ℂ) else -1) • x' j := by
      simpa [h1, hx'] using
        (Equiv.sum_comp e.symm
          (fun i : ι => (if ε' (e i) then (1 : ℂ) else -1) • x i)).symm
    rw [h2]
  have h := (hc (H := H) (Fintype.card ι) x').1
  rw [hsum_sq] at h
  rw [hcard, ← hsum_sign]
  exact h

end Work.BourgainPlan.IonescuWainger
