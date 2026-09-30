import Mathlib
import Submission.Work.Pi6.EMM2.Defs
import Submission.Work.Pi6.EMM2.Statements
import Submission.Work.Pi6.EMM2.SerreKit
import Submission.Work.Pi6.EMM2.finiteType
import Submission.Work.Pi6.EMM2.lowDegree
import Submission.Work.Pi6.EMM2.pathFib
import Submission.Work.Pi6.EMM2.twoRowFive
import Submission.Work.Pi6.EMM2.HRbaseChangeTF
import Submission.Work.Pi6.EMODD.kOneIntegralHomology
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.Pi6.K2Z.transfer
import Submission.Work.Pi6.K2Z.baseChangeFlat
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-!
# `Work.Pi6.EMM2.k2fieldLow`

The field facts for a `K(ℤ,2)` range model through degree `6`, in degrees `≤ 5`: there is
`w ∈ H²(X;𝕜)` with `w^k ≠ 0` for `k ≤ 2`, `H^{2k}(X;𝕜)` one-dimensional and `H^{2k+1}(X;𝕜) = 0`
for `k ≤ 2`.

The proof is the path–loop fibration `ΩX → PX → X`:

* the total space `PX` is contractible (`Work.Pi6.EMM2.pathFib`), hence `𝕜`-acyclic above degree
  `0` (`Work.Cohomology.contractible`);
* the base `X` is a range model of `K(ℤ,2)` through `6`: `H⁰(X;𝕜) = 𝕜`, `X` simply connected
  (`Work.Pi6.EMM2.lowDegree`) and `H^s(X;𝕜)` is finite dimensional for `s ≤ 5`
  (`Work.Pi6.EMM2.finiteType`);
* the fibre is a range model of `K(ℤ,1)` through `5`, so its `𝕜`-cohomology is that of `S¹`
  (`Work.Pi6.EMM2.kOneFieldLow`);
* the multiplicative Serre spectral sequence over `𝕜` in range `5` is supplied by the hypothesis
  `Work.Pi6.MSSHolds`, and the two-row forcing argument (`Work.Pi6.EMM2.twoRowFive`) concludes.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.EMM2

noncomputable section

section FibreFacts

/-! The change of coefficients `H_{m+1}(X;𝕜) ≅ H_{m+1}(X;ℤ) ⊗ 𝕜` above a torsion-free group
(the universal coefficient theorem with vanishing `Tor`-term) is proved in
`Submission/Work/Pi6/EMM2/HRbaseChangeTF.lean` as `Work.Pi6.EMM2.HRbaseChangeTF`. -/

/-- **A `ℤ`-module isomorphic to a free one is torsion free.**  `ℤ` is a domain, so free modules are
flat and flat modules are torsion free; flatness transfers along a linear isomorphism. -/
theorem k2fl_isTorsionFree_of_free_iso {M N : Type} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) [Module.Free ℤ M] :
    Module.IsTorsionFree ℤ N := by
  haveI : Module.Flat ℤ M := Module.Flat.of_free
  haveI : Module.Flat ℤ N := Module.Flat.of_linearEquiv e.symm
  exact Module.Flat.isTorsionFree

/-- Extension of scalars sends a zero module to a zero module. -/
theorem k2fl_isZero_extendScalars {𝕜 : Type} [CommRing 𝕜] {M : ModuleCat ℤ} (h : IsZero M) :
    IsZero ((ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj M) :=
  Functor.map_isZero _ h

/-- **The `𝕜`-cohomology of a range model of `K(ℤ,1)` is that of `S¹`.**  The integral homology of
`Y` is that of the circle (`Work.Pi6.EMODD.kOneIntegralHomology`), and the change of coefficients
`ℤ → 𝕜` is available above a torsion-free group (`k2fl_baseChange_step`), which is all that is
needed since the integral homology below the degree in question is `ℤ` or `0`. -/
theorem k2fl_kOneFacts {𝕜 : Type} [Field 𝕜] (Y : Type) [TopologicalSpace Y] (y₀ : Y) (M : ℕ)
    (hM1 : 1 ≤ M) (hY : Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) M Y y₀) :
    Module.finrank 𝕜 (Coh 𝕜 Y 0) = 1 ∧
      Module.finrank 𝕜 (Coh 𝕜 Y 1) = 1 ∧
      (∀ q : ℕ, 2 ≤ q → q ≤ M → IsZero (Coh 𝕜 Y q)) := by
  classical
  haveI hpc : PathConnectedSpace Y :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero y₀
      (hY.2 0 (by norm_num) (Or.inl (by norm_num)))
  obtain ⟨hInt0, hInt2⟩ := Work.Pi6.EMODD.kOneIntegralHomology M Y y₀ hY
  refine ⟨Work.Pi6.finrank_coh_zero_of_pathConnected 𝕜 Y, ?_, ?_⟩
  · -- degree `1`: `H¹(Y;𝕜) ≅ Hom_𝕜(H₁(Y;𝕜),𝕜)` and `H₁(Y;𝕜) ≅ 𝕜`
    have htf0 : Module.IsTorsionFree ℤ (Work.Pi6.HR ℤ Y 0) := by
      obtain ⟨e⟩ := hInt0 0 (by norm_num) (Nat.zero_le _)
      exact k2fl_isTorsionFree_of_free_iso e.symm.toLinearEquiv
    obtain ⟨ebc⟩ := HRbaseChangeTF 𝕜 0 htf0
    obtain ⟨e1⟩ := hInt0 1 le_rfl hM1
    obtain ⟨efin⟩ : Nonempty (Work.Pi6.HR 𝕜 Y 1 ≅ ModuleCat.of 𝕜 𝕜) :=
      ⟨ebc ≪≫ (ModuleCat.extendScalars (Int.castRingHom 𝕜)).mapIso e1 ≪≫
        Work.Pi6.K2Z.extendScalarsIntFieldIso 𝕜⟩
    obtain ⟨edual⟩ := Work.StemsB.fieldDualUCT 𝕜
      (Work.Cohomology.singularChains 𝕜 (TopCat.of Y)) 1
    calc Module.finrank 𝕜 (Coh 𝕜 Y 1)
        = Module.finrank 𝕜 (↥(Work.Pi6.HR 𝕜 Y 1) →ₗ[𝕜] 𝕜) :=
          LinearEquiv.finrank_eq edual.toLinearEquiv
      _ = Module.finrank 𝕜 (Work.Pi6.HR 𝕜 Y 1) := Subspace.dual_finrank_eq
      _ = 1 := by rw [efin.toLinearEquiv.finrank_eq]; simp
  · -- degrees `≥ 2`: `H^q(Y;𝕜) ≅ Hom_𝕜(H_q(Y;𝕜),𝕜)` with `H_q(Y;𝕜) = 0`
    intro q hq2 hqM
    have hq1 : 1 ≤ q := by omega
    have hz : IsZero (Work.Pi6.HR ℤ Y q) := hInt2 q hq2 hqM
    have htf : Module.IsTorsionFree ℤ (Work.Pi6.HR ℤ Y (q - 1)) := by
      by_cases hq : q - 1 < 2
      · have h1 : q - 1 = 1 := by omega
        rw [h1]
        obtain ⟨e⟩ := hInt0 1 le_rfl hM1
        exact k2fl_isTorsionFree_of_free_iso e.symm.toLinearEquiv
      · have h2 : 2 ≤ q - 1 := by omega
        haveI : Subsingleton (Work.Pi6.HR ℤ Y (q - 1)) :=
          ModuleCat.subsingleton_of_isZero (hInt2 (q - 1) h2 (by omega))
        infer_instance
    obtain ⟨ebc⟩ := HRbaseChangeTF 𝕜 (q - 1) htf
    rw [Nat.sub_add_cancel hq1] at ebc
    haveI : Subsingleton (Work.Pi6.HR 𝕜 Y q) :=
      ModuleCat.subsingleton_of_isZero
        (IsZero.of_iso (k2fl_isZero_extendScalars hz) ebc)
    exact LowDegree.isZero_Coh_of_subsingleton_HR q ‹Subsingleton (Work.Pi6.HR 𝕜 Y q)›

end FibreFacts

/-- The field facts for a `K(ℤ,2)` range model through degree `6` (unfolded form of
`Work.Pi6.EMM2.K2FieldLowStatement`). -/
theorem k2fieldLow_aux (hM : Work.Pi6.MSSHolds) (𝕜 : Type) [Field 𝕜] {X : Type}
    [TopologicalSpace X] (x : X) {M : ℕ} (hM6 : 6 ≤ M)
    (hX : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) M X x) :
    ∃ w : Coh 𝕜 X 2,
      w ≠ 0 ∧
      (∀ k : ℕ, k ≤ 2 → cpow w k ≠ 0) ∧
      (∀ k : ℕ, k ≤ 2 → Module.finrank 𝕜 (Coh 𝕜 X (2 * k)) = 1) ∧
      (∀ k : ℕ, k ≤ 2 → Subsingleton (Coh 𝕜 X (2 * k + 1))) := by
  classical
  -- 1. shrink the range model to degree `6`
  have hX6 : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) 6 X x :=
    Work.EMFG.isEMSpaceUpTo_mono hX hM6
  -- 2. low-degree facts about `X`: simply connected, `H⁰(X;𝕜) = 𝕜`
  -- (`Work.Pi6.EMM2.lowDegree` itself is not used: only its two ingredients that carry no
  --  placeholder proof)
  have hsc : Work.PiS.SimplyConn X x :=
    LowDegree.simplyConn_of_isEMSpaceUpTo (A := ℤ) (m := 2) (M := 6) (by norm_num) x hX6
  have hB0 : Module.finrank 𝕜 (Coh 𝕜 X 0) = 1 :=
    LowDegree.finrank_Coh_zero x (hX6.2 0 (by omega) (Or.inl (by omega)))
  -- 3. finiteness of the cohomology of `X` through degree `5`
  have hBfin : ∀ s : ℕ, s ≤ 5 → FiniteDimensional 𝕜 (Coh 𝕜 X s) :=
    finiteType 𝕜 (A := ℤ) (by infer_instance) (m := 2) (N := 5) (by norm_num) x hX6
  -- 4. the path–loop fibration of `X` at `x`
  obtain ⟨hcontr, hserre, hFEM⟩ :=
    pathFib (A := ℤ) (m := 2) (M := 6) (by norm_num) x hX6
  let p : C(Work.Serre.mpath (ContinuousMap.const PUnit x), X) :=
    Work.Serre.mpathQ (ContinuousMap.const PUnit x)
  let e₀ : Work.Serre.mpath (ContinuousMap.const PUnit x) :=
    Work.Serre.mpathOf (ContinuousMap.const PUnit x) PUnit.unit
  -- the fibre is a range model of `K(ℤ,1)` through `5`
  have hF5 : Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) 5
      (Work.StemsB.fibre p (p e₀)) (Work.StemsB.fibrePoint p e₀) := hFEM
  -- 5. the fibre's `𝕜`-cohomology is that of `S¹` (`k2fl_kOneFacts`)
  obtain ⟨hF0, hF1, hFq⟩ :=
    k2fl_kOneFacts (𝕜 := 𝕜) (Work.StemsB.fibre p (p e₀)) (Work.StemsB.fibrePoint p e₀) 5
      (by norm_num) hF5
  -- 6. finiteness of the fibre's cohomology through degree `5`
  have hFfin : ∀ q : ℕ, q ≤ 5 → FiniteDimensional 𝕜 (Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) := by
    intro q hq
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h
      exact FiniteDimensional.of_finrank_pos (by rw [hF0]; norm_num)
    · rcases eq_or_lt_of_le (show 1 ≤ q by omega) with h1 | h1
      · subst h1
        exact FiniteDimensional.of_finrank_pos (by rw [hF1]; norm_num)
      · haveI : Subsingleton (Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) :=
          ModuleCat.subsingleton_of_isZero (hFq q (by omega) hq)
        infer_instance
  -- 7. the multiplicative Serre spectral sequence in range `5`
  obtain ⟨S, hS⟩ := hM 𝕜 (Work.Serre.mpath (ContinuousMap.const PUnit x)) X p e₀ 5
    hserre hsc hFfin hBfin
  -- 8. the total space is contractible, hence acyclic above degree `0`
  have hE : ∀ n : ℕ, 1 ≤ n → n ≤ 5 →
      IsZero (Coh 𝕜 (Work.Serre.mpath (ContinuousMap.const PUnit x)) n) := by
    intro n hn1 _
    haveI : ContractibleSpace (Work.Serre.mpath (ContinuousMap.const PUnit x)) := hcontr
    have h := Work.Cohomology.contractible 𝕜
      (TopCat.of (Work.Serre.mpath (ContinuousMap.const PUnit x))) (n - 1)
    simpa [Nat.sub_add_cancel hn1] using h
  -- 9. the two-row forcing argument (`Work.Pi6.EMM2.twoRowFive`)
  have htwo : ∃ w : Coh 𝕜 X 2,
      w ≠ 0 ∧
      (∀ k : ℕ, 2 * k ≤ 5 → cpow w k ≠ 0) ∧
      (∀ k : ℕ, 2 * k ≤ 5 → Module.finrank 𝕜 (Coh 𝕜 X (2 * k)) = 1) ∧
      (∀ k : ℕ, 2 * k + 1 ≤ 5 → Subsingleton (Coh 𝕜 X (2 * k + 1))) :=
    twoRowFive p e₀ S hS hB0 hBfin hF0 hF1 hFq hE
  obtain ⟨w, hw0, hpow, hdim, hodd⟩ := htwo
  exact ⟨w, hw0, fun k hk => hpow k (by omega), fun k hk => hdim k (by omega),
    fun k hk => hodd k (by omega)⟩

theorem k2fieldLow : Work.Pi6.EMM2.K2FieldLowStatement := k2fieldLow_aux

end

end Work.Pi6.EMM2
