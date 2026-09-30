import Submission.Work.Pi6.EMM2.Statements
import Submission.Work.Pi6.EMM2.SerreKit
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-!
# The final assembly of area EMM2

Conversions from the `finrank` bounds produced by the forcing arguments to the `Module.rank` bounds
of the interface `Work.Pi6.EMMod2`, and the assembly of the three parts from the interfaces
collected in `Pi6/EMM2/Statements.lean`.
-/

namespace Work.Pi6.EMM2

noncomputable section

open CategoryTheory CategoryTheory.Limits

/-- A finite-dimensional module of dimension `≤ n` has rank `≤ n`. -/
theorem rank_le_of_finrank_le {𝕜 : Type} [Field 𝕜] {M : Type} [AddCommGroup M]
    [Module 𝕜 M] [Module.Finite 𝕜 M] {n : ℕ} (h : Module.finrank 𝕜 M ≤ n) :
    Module.rank 𝕜 M ≤ n := by
  rw [← Module.finrank_eq_rank]
  exact_mod_cast h

/-- `IsEMSpaceUpTo` is monotone in the range (and does not depend on the proof of `0 < m`). -/
theorem emIsEMSpaceUpTo_mono {A : Type} [AddCommGroup A] {m N N' : ℕ} {hm : 0 < m} {hm' : 0 < m}
    (h : N ≤ N') {X : Type} [TopologicalSpace X] {x : X}
    (hX : Work.Serre.IsEMSpaceUpTo A m hm N' X x) :
    Work.Serre.IsEMSpaceUpTo A m hm' N X x :=
  ⟨hX.1, fun i hi hc => hX.2 i hi (hc.elim Or.inl (fun h' => Or.inr (le_trans h' h)))⟩

/-- **The assembly of `Work.Pi6.EMMod2`** from the interfaces of the EMM2 areas. -/
theorem emMod2_assembly (_hM : Work.Pi6.MSSHolds) (_hZ : Work.Pi6.K2ZFacts)
    (hK2 : K2Facts9Statement) (hK3 : K3Facts9Statement) (hK4 : K4FactsLowStatement)
    (hKZ : KZModelLowStatement) (hFT : FiniteTypeStatement) (hLD : LowDegreeStatement)
    (h2f : K2FieldLowStatement) (h2c : SecondCohZModTwoStatement) (hmc : MulCommStatement)
    (hco : CupOneStatement) (hPF : PathFibStatement) :
    Work.Pi6.EMMod2 := by
  refine ⟨?_, ?_, ?_⟩
  · -- ## `K(ℤ/2,2)`
    intro X _inst x₀ N hN hX
    obtain ⟨h3, h4, hsq2, hsq3⟩ :=
      hK2 _hM hKZ hFT hLD h2f h2c hmc hco (X := X) x₀ (N := N) (by omega) hX
    have hmod3 : Module.Finite (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 3) :=
      hFT (ZMod 2) (A := ZMod 2) (by infer_instance) (m := 2) (by norm_num) (N := 3)
        (X := X) x₀ (emIsEMSpaceUpTo_mono (by omega : 4 ≤ N) hX) 3 (by norm_num)
    exact ⟨rank_le_of_finrank_le h3, hsq2, hsq3⟩
  · -- ## `K(ℤ/2,3)`
    intro X _inst x₀ N hN hX
    obtain ⟨h3, h4, h5, h6, h7, hsq3⟩ :=
      hK3 _hM hKZ hFT hLD h2f h2c hmc hco hPF hK2 (X := X) x₀ (N := N) (by omega) hX
    have hmod4 : Module.Finite (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 4) :=
      hFT (ZMod 2) (A := ZMod 2) (by infer_instance) (m := 3) (by norm_num) (N := 4)
        (X := X) x₀ (emIsEMSpaceUpTo_mono (by omega : 5 ≤ N) hX) 4 (by norm_num)
    have hmod5 : Module.Finite (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 5) :=
      hFT (ZMod 2) (A := ZMod 2) (by infer_instance) (m := 3) (by norm_num) (N := 5)
        (X := X) x₀ (emIsEMSpaceUpTo_mono (by omega : 6 ≤ N) hX) 5 (by norm_num)
    exact ⟨rank_le_of_finrank_le (by omega), rank_le_of_finrank_le (by omega), hsq3⟩
  · -- ## `K(ℤ/2,4)`
    intro X _inst x₀ N hN hX
    obtain ⟨h7, h8⟩ :=
      hK4 _hM hKZ hFT hLD h2f h2c hmc hco hPF hK2 hK3 (X := X) x₀ (N := N) (by omega) hX
    have hmod7 : Module.Finite (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 7) :=
      hFT (ZMod 2) (A := ZMod 2) (by infer_instance) (m := 4) (by norm_num) (N := 7)
        (X := X) x₀ (emIsEMSpaceUpTo_mono (by omega : 8 ≤ N) hX) 7 (by norm_num)
    have hmod8 : Module.Finite (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 8) :=
      hFT (ZMod 2) (A := ZMod 2) (by infer_instance) (m := 4) (by norm_num) (N := 8)
        (X := X) x₀ (emIsEMSpaceUpTo_mono (by omega : 9 ≤ N) hX) 8 (by norm_num)
    exact ⟨rank_le_of_finrank_le h7, rank_le_of_finrank_le h8⟩

end

end Work.Pi6.EMM2
