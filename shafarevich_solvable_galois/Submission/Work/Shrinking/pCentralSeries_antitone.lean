import Mathlib.FieldTheory.Normal.Defs
import Submission.Work.Shrinking.PCentral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Shrinking

/-- The descending `p`-central series is antitone (`m ≤ n` implies `P_n ≤ P_m`).

Follows from the single-step case `pCentralSeries p P (n+1) ≤ pCentralSeries p P n`
(which is proved in `Submission.Work.Shrinking.pCentralSeries_le_succ`; if that module is not
importable yet, prove it here: `pCentralStep p H = powSubgroup p H ⊔ ⁅H, ⊤⁆ ≤ H` using
`Work.Shrinking.powSubgroup_le` and `Work.Shrinking.commutator_le_self_of_normal` together with
normality of the terms — which itself can be proved simultaneously by induction).  Conclude with
`antitone_nat_of_succ_le`. -/
theorem pCentralSeries_antitone (p : ℕ) (P : Type*) [Group P] :
    Antitone (pCentralSeries p P) := by
  apply antitone_nat_of_succ_le
  -- Simultaneous induction: every term is normal, and the series is step-wise descending.
  have key : ∀ n, (pCentralSeries p P n).Normal ∧
      pCentralSeries p P (n + 1) ≤ pCentralSeries p P n := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [pCentralSeries_zero]; exact Subgroup.normal_top
      · rw [pCentralSeries_succ]; exact le_top
    | succ n ih =>
      obtain ⟨hnorm, _⟩ := ih
      -- `H^p` is normal whenever `H` is: conjugation sends the generating set to itself.
      have pownormal : ∀ {H : Subgroup P}, H.Normal → (powSubgroup p H).Normal := by
        intro H hH
        refine Subgroup.Normal.mk fun x hx g => ?_
        have hφy : ∀ y : P, (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ := by
          intro y
          change (MulAut.conj g) y = g * y * g⁻¹
          rw [MulAut.conj_apply]
        have hS : (MulAut.conj g).toMonoidHom '' ((fun x : P => x ^ p) '' (H : Set P))
            ⊆ ((fun x : P => x ^ p) '' (H : Set P)) := by
          rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
          refine ⟨(MulAut.conj g).toMonoidHom y, ?_, ?_⟩
          · rw [hφy y]; exact hH.conj_mem y hy g
          · rw [map_pow]
        have hmap : Subgroup.map (MulAut.conj g).toMonoidHom
              (Subgroup.closure ((fun x : P => x ^ p) '' (H : Set P)))
            ≤ Subgroup.closure ((fun x : P => x ^ p) '' (H : Set P)) := by
          rw [MonoidHom.map_closure]
          exact Subgroup.closure_mono hS
        have hmem := hmap (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx)
        simpa [hφy x, powSubgroup] using hmem
      have hpow : (powSubgroup p (pCentralSeries p P n)).Normal := pownormal hnorm
      have hcom : (⁅pCentralSeries p P n, ⊤⁆ : Subgroup P).Normal :=
        Subgroup.commutator_normal _ _
      have hKn : (pCentralSeries p P (n + 1)).Normal := by
        rw [pCentralSeries_succ]
        unfold pCentralStep
        exact @Subgroup.sup_normal P _ _ _ hpow hcom
      refine ⟨hKn, ?_⟩
      rw [pCentralSeries_succ]
      unfold pCentralStep
      apply sup_le
      · exact powSubgroup_le p _
      · exact @commutator_le_self_of_normal P _ _ hKn
  intro n
  exact (key n).2

end Work.Shrinking
