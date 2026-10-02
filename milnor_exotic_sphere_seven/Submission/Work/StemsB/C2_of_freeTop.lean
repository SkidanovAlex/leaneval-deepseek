import Mathlib
import Submission.Work.StemsB.RangeModelPlan
import Submission.Work.StemsB.rangeModel_ratH_iso
import Submission.Work.Serre.serreC0Range
import Submission.Work.Stems.Engine.C2FreeTop

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `C2RatSphereRange` from the *free-top* `C2` interfaces

`Work.StemsB.C2RatSphereRange` (`Submission/Work/StemsB/RangeModelPlan.lean`) is the input of
`Work.StemsB.rangeModelRatAcyclic_of_serre` that the Eilenberg–MacLane computation has to supply:
for `k ≥ 1`, a range model `X` of `K(ℤ,k)` through a degree `N ≥ 2k-1` satisfies
`H_k(X;ℚ) ≅ ℚ` and `H_i(X;ℚ) = 0` for `0 < i ≤ 2k-1`, `i ≠ k`.

That statement carries a **fixed** top `2k-1`.  The producer side, however, cannot be phrased with a
fixed top: `Submission/Work/Stems/C2ODD_PLAN.md` and `SERRE_BLUEPRINT.md` ADDENDUM 3 (B), (C)
record that the mutual induction (even step: the Gysin/periodicity for the path–loop fibration of
`K(ℤ,2j)`; odd step: the cover `Eₙ = hofib(Sⁿ → K(ℤ,n))` and E3(a)) loses a number of *degrees*
**linear** in the level `n`, while the range models exist to **any** top `N`
(`Work.Serre.SerreC0Range`, proved).  The conclusion of the induction is therefore necessarily of
the form "agrees with the rational homology of `Sⁿ` through degree `N - c·n`", which is exactly the
interface `Work.Stems.Engine.C2evenFree c` / `C2oddFree c` of
`Submission/Work/Stems/Engine/C2FreeTop.lean`.

This file **closes the gap between the two**: with a *free* top and a linear allowance `c`, the
fixed-top statement `C2RatSphereRange` follows, by choosing the top `N' = N + 2k + c·k` — large
enough that `N' - c·k ≥ N + 2k > 2k-1` — and transporting along the comparison of two range models
of `K(ℤ,k)` (`Work.StemsB.rangeModel_ratH_iso`, proved).

The proof is pure bookkeeping; no geometry is used.  Together with
`Submission/Work/StemsB/contractInputs.lean` it makes the contract follow from

  K5 (`SerreExactRangeCorrected`) + C0 + C3 (SERRE) + `C2evenFree c` + `C2oddFree c` (area STEMS).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.StemsB

noncomputable section

/-- **The comparison of two range models of `K(ℤ,k)` with different tops.**  If `X` is a range
model through `N` and `P` one through `M ≥ N`, their rational homology agrees in degrees `≤ N`.
This is `Work.StemsB.rangeModel_ratH_iso` with the second model weakened to the range `N`. -/
theorem rangeModel_ratH_iso_le {k N M : ℕ} (hk : 2 ≤ k) (hNM : N ≤ M)
    {X P : Type} [TopologicalSpace X] [TopologicalSpace P] (x₀ : X) (p₀ : P)
    (hX : Work.Serre.IsEMSpaceUpTo ℤ k (by omega) N X x₀)
    (hP : Work.Serre.IsEMSpaceUpTo ℤ k (by omega) M P p₀) :
    ∀ i : ℕ, i ≤ N →
      Nonempty (Work.Serre.ratH (TopCat.of X) i ≅ Work.Serre.ratH (TopCat.of P) i) :=
  rangeModel_ratH_iso ℤ k N hk X x₀ hX P p₀
    ⟨hP.1, fun i hi hc => hP.2 i hi (hc.imp (fun h => h) (fun h => le_trans h hNM))⟩

/-- **`C2` for `K(ℤ,2j)` with a fixed top, from the free-top interface.**  For `j ≥ 1` and a range
model `X` of `K(ℤ,2j)` through `N ≥ 4j-1`, `H_{2j}(X;ℚ) ≅ ℚ` and `H_i(X;ℚ) = 0` for
`0 < i ≤ 4j-1`, `i ≠ 2j`. -/
theorem C2RatSphereRange_even (c : ℕ) (h : Work.Stems.Engine.C2evenFree c) (j : ℕ) (hj : 1 ≤ j) :
    ∀ (N : ℕ), 2 * (2 * j) - 1 ≤ N → ∀ (X : Type) [TopologicalSpace X] (pt : X),
      Work.Serre.IsEMSpaceUpTo ℤ (2 * j) (by omega) N X pt →
      Nonempty (Work.Serre.ratH (TopCat.of X) (2 * j) ≅ ModuleCat.of ℚ ℚ) ∧
        ∀ i : ℕ, 0 < i → i ≤ 2 * (2 * j) - 1 → i ≠ 2 * j →
          IsZero (Work.Serre.ratH (TopCat.of X) i) := by
  intro N hN X _ pt hX
  have hk : 2 ≤ 2 * j := by omega
  -- `2j < 2·(2j)`: the only nonlinear fact needed
  have h24 : 2 * j < 2 * (2 * j) := by
    have hm : 2 * (2 * j) = 2 * j + 2 * j := by ring
    omega
  have h2jN : 2 * j ≤ N := by omega
  -- a range model of `K(ℤ,2j)` with the large top `N + 2*(2j) + c*(2j)`
  obtain ⟨P, tP, p₀, hP⟩ :=
    Work.Serre.serreC0Range ℤ (2 * j) (N + 2 * (2 * j) + c * (2 * j)) (by omega) (by omega)
  letI : TopologicalSpace P := tP
  have hPmod := h j hj (N + 2 * (2 * j) + c * (2 * j)) P p₀ hP
  have hNle : N ≤ N + 2 * (2 * j) + c * (2 * j) := by omega
  have hsub : N + 2 * (2 * j) + c * (2 * j) - c * (2 * j) = N + 2 * (2 * j) := by omega
  constructor
  · -- the generator `H_{2j}(X;ℚ) ≅ ℚ`
    obtain ⟨e⟩ := rangeModel_ratH_iso_le hk hNle pt p₀ hX hP (2 * j) h2jN
    obtain ⟨eP⟩ := hPmod.1 1 (by rw [hsub, Nat.mul_one]; omega)
    exact ⟨e ≪≫ (by simpa using eP)⟩
  · -- the vanishing
    intro i hi hi2 hin
    have hiN : i ≤ N := by omega
    obtain ⟨e⟩ := rangeModel_ratH_iso_le hk hNle pt p₀ hX hP i hiN
    refine IsZero.of_iso (hPmod.2 i (by rw [hsub]; omega) ?_) e
    intro k' hk'
    -- `i = 2j·k'` with `0 < i ≤ 4j-1 < 4j` forces `k' = 1`, i.e. `i = 2j`
    have hk'1 : 1 ≤ k' := by
      rcases Nat.eq_zero_or_pos k' with h0 | h0
      · subst h0
        rw [Nat.mul_zero] at hk'
        omega
      · exact h0
    have h2jpos : 0 < 2 * j := by omega
    have hlt : k' < 2 := by
      have h1 : 2 * j * k' < 2 * j * 2 := by
        calc 2 * j * k' = i := hk'.symm
          _ ≤ 2 * (2 * j) - 1 := hi2
          _ < 2 * (2 * j) := by omega
          _ = 2 * j * 2 := by ring
      exact (Nat.mul_lt_mul_left h2jpos).mp h1
    have hk'one : k' = 1 := by omega
    subst hk'one
    rw [Nat.mul_one] at hk'
    exact hin hk'

/-- **`C2` for `K(ℤ,n)` with `n ≥ 2` odd and a fixed top, from the free-top interface.**  For `n ≥ 2`
odd and a range model `X` of `K(ℤ,n)` through `N ≥ 2n-1`, `H_n(X;ℚ) ≅ ℚ` and `H_i(X;ℚ) = 0` for
`0 < i ≤ 2n-1`, `i ≠ n`. -/
theorem C2RatSphereRange_odd (c : ℕ) (h : Work.Stems.Engine.C2oddFree c) (n : ℕ) (hn : 2 ≤ n)
    (hno : Odd n) :
    ∀ (N : ℕ), 2 * n - 1 ≤ N → ∀ (X : Type) [TopologicalSpace X] (pt : X),
      Work.Serre.IsEMSpaceUpTo ℤ n (by omega) N X pt →
      Nonempty (Work.Serre.ratH (TopCat.of X) n ≅ ModuleCat.of ℚ ℚ) ∧
        ∀ i : ℕ, 0 < i → i ≤ 2 * n - 1 → i ≠ n →
          IsZero (Work.Serre.ratH (TopCat.of X) i) := by
  intro N hN X _ pt hX
  have hnN : n ≤ N := by
    have hm : 2 * n = n + n := Nat.two_mul n
    omega
  obtain ⟨P, tP, p₀, hP⟩ :=
    Work.Serre.serreC0Range ℤ n (N + 2 * n + c * n) (by omega) (by omega)
  letI : TopologicalSpace P := tP
  have hPmod := h n (by omega) hno (N + 2 * n + c * n) P p₀ hP
  have hNle : N ≤ N + 2 * n + c * n := by omega
  have hsub : N + 2 * n + c * n - c * n = N + 2 * n := by omega
  constructor
  · obtain ⟨e⟩ := rangeModel_ratH_iso_le (by omega : 2 ≤ n) hNle pt p₀ hX hP n hnN
    obtain ⟨eP⟩ := hPmod.1
    exact ⟨e ≪≫ eP⟩
  · intro i hi hi2 hin
    have hiN : i ≤ N := by omega
    obtain ⟨e⟩ := rangeModel_ratH_iso_le (by omega : 2 ≤ n) hNle pt p₀ hX hP i hiN
    exact IsZero.of_iso (hPmod.2 i hi (by rw [hsub]; omega) hin) e

/-- **`C2RatSphereRange` from the free-top `C2` interfaces.** -/
theorem C2RatSphereRange_of_freeTop (c : ℕ) (heven : Work.Stems.Engine.C2evenFree c)
    (hodd : Work.Stems.Engine.C2oddFree c) : C2RatSphereRange := by
  intro k hk N hN X _ pt hX
  rcases Nat.even_or_odd k with hkE | hkO
  · -- `k` even: `k = 2j`, `j ≥ 1`
    obtain ⟨j₀, hj₀⟩ := hkE
    obtain ⟨j, rfl⟩ := (show ∃ j, k = 2 * j from ⟨j₀, by rw [hj₀, Nat.two_mul]⟩)
    exact C2RatSphereRange_even c heven j (by omega) N hN X pt hX
  · -- `k` odd
    by_cases hk1 : k = 1
    · -- `k = 1`: the vanishing conjunct is vacuous, and the generator conjunct is supplied by
      -- `C2oddFree` applied to `X` itself (no comparison is needed, and none is available: the
      -- comparison `rangeModel_ratH_iso` needs `2 ≤ k`)
      subst k
      have hgen := (hodd 1 (by omega) ⟨0, by norm_num⟩ N X pt hX).1
      exact ⟨hgen, fun i hi hi2 hin => absurd (by omega) hin⟩
    · exact C2RatSphereRange_odd c hodd k (by omega) hkO N hN X pt hX

end

end Work.StemsB
