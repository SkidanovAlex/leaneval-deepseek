import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.EMM2.twoRowKit
import Submission.Work.Pi6.EMM2.kOneFibre
import Submission.Work.Pi6.EMM2.finiteType
import Submission.Work.Pi6.EMM2.pathFib
import Submission.Work.Cohomology.contractible
import Submission.Work.Pi6.K2Z.transfer
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# `K2Z` — the field half of `K2ZFacts`

For a range model `X` of `K(ℤ,2)` through degree `N ≥ 10` and any field `𝕜`, there is
`w ∈ H²(X;𝕜)` with `w^k ≠ 0` (`k ≤ 4`), `dim H^{2k}(X;𝕜) = 1` and `H^{2k+1}(X;𝕜) = 0`
(`k ≤ 4`).

The proof is the two-row forcing argument for the path–loop fibration `ΩX → PX → X` of `X`
(`Work.Serre.mpathQ` of the constant map `PUnit → X`): the total space is contractible
(`Work.Pi6.EMM2.pathFib`), the fibre is the loop space, a `K(ℤ,1)` range model through `N - 1 ≥ 9`
whose `𝕜`-cohomology is that of the circle (`Work.Pi6.EMM2.kOneFibre`), the base has finite type
through `N - 1` (`Work.Pi6.EMM2.finiteType`, from `Work.EMFG.emHomologyFG`), and the multiplicative
spectral sequence over `𝕜` is supplied by the hypothesis `MSSHolds`.  The forcing argument itself is
`Work.Pi6.EMM2.k2f_twoRow` (`Submission/Work/Pi6/EMM2/twoRowKit.lean`).
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.K2Z

noncomputable section

/-- **The field half of `K2ZFacts`.** -/
theorem fieldHalf (hM : Work.Pi6.MSSHolds) (X : Type) [TopologicalSpace X] (x₀ : X) (N : ℕ)
    (hN : 10 ≤ N) (hX : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) N X x₀)
    (𝕜 : Type) [Field 𝕜] :
    ∃ w : Work.Pi6.Coh 𝕜 X 2, ∀ k : ℕ, k ≤ 4 → Work.Pi6.cpow w k ≠ 0 ∧
      Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 X (2 * k)) = 1 ∧
        Subsingleton (Work.Pi6.Coh 𝕜 X (2 * k + 1)) := by
  classical
  -- shrink the range to `10`
  have hX10 : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) 10 X x₀ :=
    Work.EMFG.isEMSpaceUpTo_mono hX (by omega)
  -- connectivity and `H⁰`
  have hpi0 : Subsingleton (HomotopyGroup (Fin 0) X x₀) :=
    hX.2 0 (by norm_num) (Or.inl (by norm_num))
  have hpi1 : Subsingleton (HomotopyGroup (Fin 1) X x₀) :=
    hX.2 1 (by norm_num) (Or.inl (by norm_num))
  have hsc : Work.PiS.SimplyConn X x₀ := ⟨hpi0, hpi1⟩
  haveI : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x₀ hpi0
  have hB0 : Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 X 0) = 1 :=
    Work.Pi6.finrank_coh_zero_of_pathConnected 𝕜 X
  -- finiteness of `H^*(X;𝕜)` through degree `9`
  have hBfin : ∀ s : ℕ, s ≤ 9 → FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 X s) := by
    have h' : Work.Serre.IsEMSpaceUpTo ℤ 2 (by omega) (9 + 1) X x₀ :=
      Work.EMFG.isEMSpaceUpTo_congr hX10
    exact Work.Pi6.EMM2.finiteType 𝕜 (A := ℤ) (by infer_instance) (m := 2) (N := 9)
      (by norm_num) x₀ h'
  -- the path fibration
  set p : C(Work.Serre.mpath (ContinuousMap.const PUnit x₀), X) :=
    Work.Serre.mpathQ (ContinuousMap.const PUnit x₀) with hp
  set e₀ : Work.Serre.mpath (ContinuousMap.const PUnit x₀) :=
    Work.Serre.mpathOf (ContinuousMap.const PUnit x₀) PUnit.unit with he
  have hpe : p e₀ = x₀ := rfl
  obtain ⟨hcontr, hserre, hFEM⟩ :=
    (Work.Pi6.EMM2.pathFib (A := ℤ) (m := 2) (M := 10) (by norm_num) x₀
      (Work.EMFG.isEMSpaceUpTo_congr hX10))
  -- the fibre is a `K(ℤ,1)` range model through `9`
  have hF9 : Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) 9
      (Work.StemsB.fibre p (p e₀)) (Work.StemsB.fibrePoint p e₀) := hFEM
  obtain ⟨hF0, hF1, hFq⟩ :=
    Work.Pi6.EMM2.kOneFibre (𝕜 := 𝕜) (Work.StemsB.fibre p (p e₀))
      (Work.StemsB.fibrePoint p e₀) 9 hF9
  have hFfin : ∀ q : ℕ, q ≤ 9 → FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) := by
    intro q hq
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h
      exact FiniteDimensional.of_finrank_pos (by rw [hF0]; norm_num)
    · rcases eq_or_lt_of_le (show 1 ≤ q by omega) with h1 | h1
      · subst h1
        exact FiniteDimensional.of_finrank_pos (by rw [hF1]; norm_num)
      · haveI : Subsingleton (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) :=
          ModuleCat.subsingleton_of_isZero (hFq q (by omega) hq)
        infer_instance
  -- the Serre spectral sequence in range `9`
  obtain ⟨S, hS⟩ := hM 𝕜 (Work.Serre.mpath (ContinuousMap.const PUnit x₀)) X p e₀ 9
    hserre hsc hFfin hBfin
  -- the total space is acyclic above degree `0`
  have hE : ∀ n : ℕ, 1 ≤ n → n ≤ 9 →
      IsZero (Work.Pi6.Coh 𝕜 (Work.Serre.mpath (ContinuousMap.const PUnit x₀)) n) := by
    intro n hn1 _
    haveI : ContractibleSpace (Work.Serre.mpath (ContinuousMap.const PUnit x₀)) := hcontr
    have h := Work.Cohomology.contractible 𝕜
      (TopCat.of (Work.Serre.mpath (ContinuousMap.const PUnit x₀))) (n - 1)
    simpa [Nat.sub_add_cancel hn1] using h
  -- the two-row forcing argument
  obtain ⟨w, hpow, hdim, hodd⟩ :=
    Work.Pi6.EMM2.k2f_twoRow p e₀ 9 S hS (by norm_num) hB0 hBfin hF0 hF1 hFq hE
  refine ⟨w, fun k hk => ⟨?_, ?_, ?_⟩⟩
  · exact hpow k (by omega)
  · exact hdim k (by omega)
  · exact hodd k (by omega)

end

end Work.Pi6.K2Z
