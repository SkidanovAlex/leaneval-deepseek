import Mathlib

/-!
# A finitely generated `ℚ`-submodule of `ℚ⟦X⟧` has bounded order

If `E ⊆ ℚ⟦X⟧` is a finitely generated `ℚ`-submodule (equivalently, a finite-dimensional
`ℚ`-subspace), then the orders of the non-zero elements of `E` are bounded.

The proof is the standard "vanishing filtration" argument.  For `N : ℕ` let

`K N := trunc E N).ker`,   `trunc E N : E →ₗ[ℚ] (Fin N → ℚ)`, `x ↦ (coeff 0 x, …, coeff (N-1) x)`,

so that `K N` is the subspace of elements of `E` vanishing to order at least `N`.  The `K N` are a
decreasing chain of subspaces of the finite-dimensional space `E`, hence the sequence of their
`finrank`s is eventually constant; if `K M = K N` for all `N ≥ M` then any `x ∈ K M` has *all* its
coefficients zero (look at a truncation larger than any prescribed index), so `K M = ⊥`.  Hence no
non-zero element of `E` vanishes to order `≥ M`.

This is the finite-dimensionality input used to bound the order of polynomial combinations of the
entries of a `D`-closed family of power series (`Work.ZeroEst.fixed_deg_order_bound`).
-/

namespace Work.ZeroEst

open PowerSeries

/-- An antitone sequence of natural numbers is eventually constant. -/
private lemma antitone_nat_stabilize (d : ℕ → ℕ) (hd : Antitone d) :
    ∃ M, ∀ n ≥ M, d n = d M := by
  obtain ⟨M, hM⟩ := Nat.sInf_mem (s := Set.range d) ⟨d 0, Set.mem_range_self 0⟩
  refine ⟨M, fun n hn => ?_⟩
  have h1 : d n ≤ d M := hd hn
  have h2 : d M ≤ d n := by rw [hM]; exact Nat.sInf_le (Set.mem_range_self n)
  omega

/-- Truncation of an element of `E` to its first `N` Taylor coefficients. -/
noncomputable def trunc (E : Submodule ℚ (PowerSeries ℚ)) (N : ℕ) :
    E →ₗ[ℚ] (Fin N → ℚ) :=
  LinearMap.pi fun n : Fin N => (PowerSeries.coeff (R := ℚ) (n : ℕ)).comp E.subtype

lemma trunc_apply (E : Submodule ℚ (PowerSeries ℚ)) (N : ℕ) (x : E) (n : Fin N) :
    trunc E N x n = PowerSeries.coeff (n : ℕ) (x : PowerSeries ℚ) := by
  rw [trunc, LinearMap.pi_apply]
  rfl

/-- The kernel of the truncation map consists of the elements vanishing to order at least `N`. -/
lemma mem_ker_trunc (E : Submodule ℚ (PowerSeries ℚ)) (N : ℕ) (x : E) :
    x ∈ LinearMap.ker (trunc E N) ↔
      ∀ n : Fin N, PowerSeries.coeff (n : ℕ) (x : PowerSeries ℚ) = 0 := by
  rw [LinearMap.mem_ker, funext_iff]
  simp [trunc_apply]

/-- The kernels of the truncation maps form a decreasing chain. -/
lemma ker_trunc_anti (E : Submodule ℚ (PowerSeries ℚ)) :
    Antitone (fun N => LinearMap.ker (trunc E N)) := by
  apply antitone_nat_of_succ_le
  intro N x hx
  rw [mem_ker_trunc] at hx ⊢
  intro n
  exact hx ⟨n.1, Nat.lt_succ_of_lt n.2⟩

theorem fg_order_bound (E : Submodule ℚ (PowerSeries ℚ)) (hE : E.FG) :
    ∃ N : ℕ, ∀ g ∈ E, g ≠ 0 → g.order ≤ (N : ℕ∞) := by
  classical
  have : FiniteDimensional ℚ E := (Submodule.fg_iff_finiteDimensional E).mp hE
  -- the finrank of the vanishing subspaces is antitone
  have hd : Antitone (fun N => Module.finrank ℚ ↥(LinearMap.ker (trunc E N))) :=
    fun a b hab => Submodule.finrank_mono (ker_trunc_anti E hab)
  obtain ⟨M, hM⟩ := antitone_nat_stabilize _ hd
  -- the chain has stabilised past `M`
  have hM_eq : ∀ N ≥ M, LinearMap.ker (trunc E N) = LinearMap.ker (trunc E M) := by
    intro N hN
    refine Submodule.eq_of_le_of_finrank_eq (ker_trunc_anti E hN) ?_
    exact hM N hN
  -- hence `K M = ⊥`
  have hbot : LinearMap.ker (trunc E M) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    apply Subtype.ext
    rw [Submodule.coe_zero]
    apply PowerSeries.ext
    intro n
    have hn : n < max M (n + 1) := lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _)
    have hxm : x ∈ LinearMap.ker (trunc E (max M (n + 1))) := by
      rw [hM_eq (max M (n + 1)) (le_max_left _ _)]
      exact hx
    have hxm' := (mem_ker_trunc E (max M (n + 1)) x).mp hxm
    simpa using hxm' ⟨n, hn⟩
  refine ⟨M, fun g hg hgne => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hx : (⟨g, hg⟩ : E) ∈ LinearMap.ker (trunc E M) := by
    rw [mem_ker_trunc]
    intro n
    apply PowerSeries.coeff_of_lt_order
    have hn : ((n : ℕ) : ℕ∞) < (M : ℕ∞) := by
      rw [ENat.natCast_lt_natCast]; exact n.2
    exact lt_trans hn hlt
  rw [hbot] at hx
  have hz : (⟨g, hg⟩ : E) = 0 := by simpa using hx
  exact hgne (by simpa using congrArg Subtype.val hz)

end Work.ZeroEst
