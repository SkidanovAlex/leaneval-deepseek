import Submission.Work.EKLContract.Diag

/-!
# EKL contract — GLUE (proved)

The composition of the frozen component `Prop`s of `Work.EKLContract.Defs` into the challenge
statement, together with everything it needs.  Everything in this file is proved
(`#print axioms` clean; see `NOTES.md`).

Main results:
* `Work.EKLContract.rigidity_of`      — the `k = 3` case analysis (glue G).
* `Work.EKLContract.posEntMeasure_of` — `P_X3 → P_Misiurewicz → P_ErgodicMax → P_PosEntMeasure`.
* `Work.EKLContract.lowEntropy_of`    — `P_RelCross → P_NonExc → P_LowEntropyCore → P_LowEntropy`.
* `Work.EKLContract.ekl_of_components`, `Work.EKLContract.ekl_challenge` — the composition.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

namespace Work.EKLContract

/-! ## 9.b Monotonicity of `Thick` and `Drho` -/

theorem hasShortVec_mono {x : X3} {ρ ρ' : ℝ} (h : ρ' ≤ ρ) (hx : HasShortVec x ρ') :
    HasShortVec x ρ := by
  obtain ⟨g, hg, m, hm, hlt⟩ := hx
  exact ⟨g, hg, m, hm, fun i => lt_of_lt_of_le (hlt i) h⟩

theorem Drho_anti {ρ ρ' : ℝ} (h : ρ' ≤ ρ) : Drho ρ ⊆ Drho ρ' := by
  intro x hx r s hr hs hsv
  exact hx r s hr hs (hasShortVec_mono h hsv)

theorem Drho_subset_thick (ρ : ℝ) : Drho ρ ⊆ Thick ρ := by
  intro x hx
  simp only [Drho] at hx
  have h := hx 0 0 le_rfl le_rfl
  rwa [aPlus_zero, one_smul] at h

/-! ## 9.c `Drho ρ` is compact and `a₀`-forward-invariant -/

theorem isClosed_Drho (h2 : P_X3) {ρ : ℝ} (hρ : 0 < ρ) : IsClosed (Drho ρ) := by
  haveI : T2Space X3 := h2.1
  have hT : IsClosed (Thick ρ) := (h2.2.2.1 ρ hρ).isClosed
  have hEq : Drho ρ = ⋂ (r : {r : ℝ // 0 ≤ r}) (s : {s : ℝ // 0 ≤ s}),
      (fun x : X3 => aPlus (r : ℝ) (s : ℝ) • x) ⁻¹' (Thick ρ) := by
    ext x
    simp only [Drho, Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h r s; exact h r s r.2 s.2
    · intro h r s hr hs; exact h ⟨r, hr⟩ ⟨s, hs⟩
  rw [hEq]
  exact isClosed_iInter fun r => isClosed_iInter fun s =>
    hT.preimage (continuous_const_smul _)

theorem isCompact_Drho (h2 : P_X3) {ρ : ℝ} (hρ : 0 < ρ) : IsCompact (Drho ρ) :=
  (h2.2.2.1 ρ hρ).of_isClosed_subset (isClosed_Drho h2 hρ) (Drho_subset_thick ρ)

theorem a0_maps_Drho {ρ : ℝ} {x : X3} (hx : x ∈ Drho ρ) : a0 • x ∈ Drho ρ := by
  intro r s hr hs
  rw [← mul_smul, aPlus_mul_a0]
  exact hx (r + 1) (s + 1) (by linarith) (by linarith)

/-! ## 9.d `posEntMeasure_of` -/

theorem posEntMeasure_of (h2 : P_X3) (h4a : P_Misiurewicz) (h4c : P_ErgodicMax) :
    P_PosEntMeasure := by
  intro ρ hρ hpos
  obtain ⟨ν, hνprob, hνK, hνmp, hνent⟩ :=
    h4a a0 (Drho ρ) (isCompact_Drho h2 hρ) (fun x hx => a0_maps_Drho hx) hpos
  exact h4c ρ hρ ν hνprob hνK hνmp hνent

/-! ## 9.e `lowEntropy_of` -/

theorem lowEntropy_of (hR : P_RelCross) (hN : P_NonExc) (hC : P_LowEntropyCore) :
    P_LowEntropy := by
  intro μ hμ hE a b c hab hac hcb hn h1 h2
  haveI := hμ
  exact hC μ hE a b c hab hac hcb (hR μ hE a b c hab hac hcb h1 h2) hn
    (hN μ hE.1 a b c hab hac hcb)

/-! ## 9.f The `k = 3` case analysis (`rigidity_of`) -/

/-- The six diagonal one-parameter vectors appearing in the case analysis. -/
def tA : Fin 3 → ℝ := ![-2, 1, 1]
def tB : Fin 3 → ℝ := ![2, -1, -1]
def tC : Fin 3 → ℝ := ![1, 2, 1]
def tD : Fin 3 → ℝ := ![-1, -2, -1]
def tE : Fin 3 → ℝ := ![1, 1, 2]
def tF : Fin 3 → ℝ := ![-1, -1, -2]

theorem tB_eq_neg_tA : tB = -tA := by funext i; fin_cases i <;> simp [tA, tB]
theorem tD_eq_neg_tC : tD = -tC := by funext i; fin_cases i <;> simp [tC, tD]
theorem tF_eq_neg_tE : tF = -tE := by funext i; fin_cases i <;> simp [tE, tF]

/-- `tA = ![-2,1,1]` contracts `U_01` and `U_02` (and nothing else). -/
theorem lt_tA {i j : Fin 3} (h : tA i < tA j) : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) := by
  fin_cases i <;> fin_cases j <;> simp_all [tA] <;> try linarith

/-- `tB = ![2,-1,-1]` contracts `U_10` and `U_20`. -/
theorem lt_tB {i j : Fin 3} (h : tB i < tB j) : (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 0) := by
  fin_cases i <;> fin_cases j <;> simp_all [tB] <;> try linarith

/-- `tC = ![1,2,1]` contracts `U_01` and `U_21`. -/
theorem lt_tC {i j : Fin 3} (h : tC i < tC j) : (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 1) := by
  fin_cases i <;> fin_cases j <;> simp_all [tC] <;> try linarith

/-- `tD = ![-1,-2,-1]` contracts `U_10` and `U_12`. -/
theorem lt_tD {i j : Fin 3} (h : tD i < tD j) : (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 2) := by
  fin_cases i <;> fin_cases j <;> simp_all [tD] <;> try linarith

/-- `tE = ![1,1,2]` contracts `U_02` and `U_12`. -/
theorem lt_tE {i j : Fin 3} (h : tE i < tE j) : (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by
  fin_cases i <;> fin_cases j <;> simp_all [tE] <;> try linarith

/-- `tF = ![-1,-1,-2]` contracts `U_20` and `U_21`. -/
theorem lt_tF {i j : Fin 3} (h : tF i < tF j) : (i = 2 ∧ j = 0) ∨ (i = 2 ∧ j = 1) := by
  fin_cases i <;> fin_cases j <;> simp_all [tF] <;> try linarith

/-- The six distinctness proofs used to name the root groups `U_ij`. -/
theorem h01 : (0 : Fin 3) ≠ 1 := by decide
theorem h02 : (0 : Fin 3) ≠ 2 := by decide
theorem h10 : (1 : Fin 3) ≠ 0 := by decide
theorem h12 : (1 : Fin 3) ≠ 2 := by decide
theorem h20 : (2 : Fin 3) ≠ 0 := by decide
theorem h21 : (2 : Fin 3) ≠ 1 := by decide

/-- C6 read as an extraction principle. -/
theorem pairs_of_ent (h6 : P_EntropyLeaf) (μ : Measure X3) [IsProbabilityMeasure μ]
    (hErg : IsAErgodic μ) {s : Fin 3 → ℝ}
    (hs : 0 < ent μ (fun x : X3 => aDiag s • x)) :
    ∃ (i j : Fin 3) (hij : i ≠ j), s i < s j ∧ ¬ CrossSection μ (Uij hij) :=
  (h6 μ hErg s).mp hs

/-- (E1) of C3 for the inverse of a diagonal element: the entropy of `α^{-t}` equals that of
`α^t`, since `α^{-t}` inverts the measure-preserving map `α^t`. -/
theorem ent_inv (h3 : P_EntropyBasics) (μ : Measure X3) [IsProbabilityMeasure μ]
    (hA : IsAInvariant μ) (s : Fin 3 → ℝ) :
    ent μ (fun x : X3 => aDiag (-s) • x) = ent μ (fun x : X3 => aDiag s • x) := by
  have h1 : Measurable (fun x : X3 => aDiag s • x) := (continuous_const_smul (aDiag s)).measurable
  have h2 : Measurable (fun x : X3 => aDiag (-s) • x) :=
    (continuous_const_smul (aDiag (-s))).measurable
  exact (h3 μ).1 _ _ h1 h2 (hA s)
    (fun x => aDiag_neg_smul s x) (fun x => aDiag_mul_neg_smul s x)

/-- **The `k = 3` case analysis (GLUE G).**  If the `A`-ergodic `μ` has positive entropy for
`a₀ = aDiag ![-2,1,1]`, then `μ` is invariant under one of the root groups `U_ij`. -/
theorem rigidity_of (h6 : P_EntropyLeaf) (h3 : P_EntropyBasics) (h7 : P_Commutator)
    (h8 : P_LowEntropy) (μ : Measure X3) [IsProbabilityMeasure μ] (hErg : IsAErgodic μ)
    (hent : 0 < ent μ (fun x : X3 => a0 • x)) :
    ∃ (i j : Fin 3) (hij : i ≠ j), IsUInvariant μ (Uij hij) := by
  have hA : IsAInvariant μ := hErg.1
  have hTA : 0 < ent μ (fun x : X3 => aDiag tA • x) := hent
  -- C6 at `a₀`: some `U_01` or `U_02` is not a cross-section.
  have hNA : ¬ CrossSection μ (Uij h01) ∨ ¬ CrossSection μ (Uij h02) := by
    obtain ⟨i, j, hij, hlt, hN⟩ := pairs_of_ent h6 μ hErg hTA
    rcases lt_tA hlt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hN
    · exact Or.inr hN
  -- In the "both N(0,1) and N(0,2)" case, `α^{tB} = (α^{tA})⁻¹` also has positive entropy.
  have caseA : ¬ CrossSection μ (Uij h01) → ¬ CrossSection μ (Uij h02) →
      ∃ (i j : Fin 3) (hij : i ≠ j), IsUInvariant μ (Uij hij) := by
    intro hN01 hN02
    have hTB : 0 < ent μ (fun x : X3 => aDiag tB • x) := by
      rw [tB_eq_neg_tA, ent_inv h3 μ hA tA]
      exact hTA
    obtain ⟨i, j, hij, hlt, hN⟩ := pairs_of_ent h6 μ hErg hTB
    rcases lt_tB hlt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨1, 2, h12, h7 μ hErg 1 0 2 h10 h02 h12 hN hN02⟩
    · exact ⟨2, 1, h21, h7 μ hErg 2 0 1 h20 h01 h21 hN hN01⟩
  rcases hNA with hN01 | hN02
  · by_cases hCS02 : CrossSection μ (Uij h02)
    · -- `N(0,1)` and `CS(0,2)`
      by_cases hCS21 : CrossSection μ (Uij h21)
      · exact ⟨0, 1, h01, h8 μ hErg 0 1 2 h01 h02 h21 hN01 hCS02 hCS21⟩
      · have hTC : 0 < ent μ (fun x : X3 => aDiag tC • x) :=
          (h6 μ hErg tC).mpr ⟨0, 1, h01, by simp [tC], hN01⟩
        have hTD : 0 < ent μ (fun x : X3 => aDiag tD • x) := by
          rw [tD_eq_neg_tC, ent_inv h3 μ hA tC]
          exact hTC
        obtain ⟨i, j, hij, hlt, hN⟩ := pairs_of_ent h6 μ hErg hTD
        rcases lt_tD hlt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨2, 0, h20, h7 μ hErg 2 1 0 h21 h10 h20 hCS21 hN⟩
        · exact ⟨0, 2, h02, h7 μ hErg 0 1 2 h01 h12 h02 hN01 hN⟩
    · exact caseA hN01 hCS02
  · by_cases hCS01 : CrossSection μ (Uij h01)
    · -- `CS(0,1)` and `N(0,2)`
      by_cases hCS12 : CrossSection μ (Uij h12)
      · exact ⟨0, 2, h02, h8 μ hErg 0 2 1 h02 h01 h12 hN02 hCS01 hCS12⟩
      · have hTE : 0 < ent μ (fun x : X3 => aDiag tE • x) :=
          (h6 μ hErg tE).mpr ⟨0, 2, h02, by simp [tE], hN02⟩
        have hTF : 0 < ent μ (fun x : X3 => aDiag tF • x) := by
          rw [tF_eq_neg_tE, ent_inv h3 μ hA tE]
          exact hTE
        obtain ⟨i, j, hij, hlt, hN⟩ := pairs_of_ent h6 μ hErg hTF
        rcases lt_tF hlt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨1, 0, h10, h7 μ hErg 1 2 0 h12 h20 h10 hCS12 hN⟩
        · exact ⟨0, 1, h01, h7 μ hErg 0 2 1 h02 h21 h01 hN02 hN⟩
    · exact caseA hCS01 hN02

/-! ## 9.g The composition -/

/-- **Step 1 of the composition, extracted**: no `Drho ρ` carries positive topological
entropy.  This is exactly the hypothesis `¬ PosEnt a0 (Drho ρ)` of `P_BoxDim`, obtained from the
components C4, C3, C6, C7, the low entropy theorem and C10. -/
theorem not_posEnt_Drho (h4 : P_PosEntMeasure) (h3 : P_EntropyBasics) (h6 : P_EntropyLeaf)
    (h7 : P_Commutator) (h8 : P_LowEntropy) (h10 : P_Endgame)
    (ρ : ℝ) (hρ : 0 < ρ) : ¬ PosEnt a0 (Drho ρ) := by
  intro hpos
  obtain ⟨μ, hμ, hErg, hD, hent⟩ := h4 ρ hρ hpos
  haveI := hμ
  obtain ⟨i, j, hij, hU⟩ := rigidity_of h6 h3 h7 h8 μ hErg hent
  have hthick : μ (Thick ρ) = 1 :=
    le_antisymm prob_le_one (by rw [← hD]; exact measure_mono (Drho_subset_thick ρ))
  exact h10 μ hErg.1 i j hij hU ρ hρ hthick

/-- **The composition.**  Given the frozen components C1a, C1b, C4 (assembled), C3, C6, C7,
the low entropy theorem and C10, the exceptional set has Hausdorff dimension zero. -/
theorem ekl_of_components (h1 : P_Dioph) (h1b : P_BoxDim) (h4 : P_PosEntMeasure)
    (h3 : P_EntropyBasics) (h6 : P_EntropyLeaf) (h7 : P_Commutator) (h8 : P_LowEntropy)
    (h10 : P_Endgame) : dimH Xi = 0 := by
  -- Step 1: no `Drho ρ` carries positive topological entropy.
  have hNoPos : ∀ ρ : ℝ, 0 < ρ → ¬ PosEnt a0 (Drho ρ) := fun ρ hρ =>
    not_posEnt_Drho h4 h3 h6 h7 h8 h10 ρ hρ
  -- Step 2: `Xi` is covered by countably many `tau ⁻¹' Drho ρ`.
  have hcover : Xi ⊆ ⋃ n : ℕ, tau ⁻¹' Drho (1 / ((n : ℝ) + 1)) := by
    intro p hp
    obtain ⟨ρ, hρ, hD⟩ := h1 p hp
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hρ
    exact Set.mem_iUnion.2 ⟨n, Drho_anti (le_of_lt hn) hD⟩
  -- Step 3: each piece has Hausdorff dimension zero.
  have hdim : ∀ n : ℕ, dimH (tau ⁻¹' Drho (1 / ((n : ℝ) + 1))) = 0 := fun n =>
    h1b _ (by positivity) (hNoPos _ (by positivity))
  refine le_antisymm ?_ zero_le
  calc dimH Xi ≤ dimH (⋃ n : ℕ, tau ⁻¹' Drho (1 / ((n : ℝ) + 1))) := dimH_mono hcover
    _ = ⨆ n : ℕ, dimH (tau ⁻¹' Drho (1 / ((n : ℝ) + 1))) := dimH_iUnion _
    _ = 0 := iSup_eq_bot.mpr (fun n => by simpa using hdim n)

/-- **The challenge statement from the components.** -/
theorem ekl_challenge (h1 : P_Dioph) (h1b : P_BoxDim) (h2 : P_X3) (h3 : P_EntropyBasics)
    (h4a : P_Misiurewicz) (h4c : P_ErgodicMax) (h6 : P_EntropyLeaf) (h6b : P_RelCross)
    (h7 : P_Commutator) (h8 : P_LowEntropyCore) (h9 : P_NonExc) (h10 : P_Endgame) :
    dimH {(α, β) : ℝ × ℝ | Filter.atTop.liminf
      (fun n : ℕ ↦ n * distToNearestInt (n * α) * distToNearestInt (n * β)) > 0} = 0 :=
  ekl_of_components h1 h1b (posEntMeasure_of h2 h4a h4c) h3 h6 h7
    (lowEntropy_of h6b h9 h8) h10

end Work.EKLContract
