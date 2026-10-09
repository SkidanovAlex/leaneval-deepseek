import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.Instance
import Submission.NK.LocalReciprocityLubinTate.Unramified.TowerSymbol
import Submission.NK.LocalReciprocityLubinTate.Units.higherUnits_cofinal
import Submission.NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion
import Submission.NK.LocalReciprocityLubinTate.Unramified.exists_level_ge_of_symbolTower
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocityLubinTate.Unramified

theorem exists_level_ge_of_towerCover {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {π : (Q.adicCompletion K)ˣ}
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer (Q.adicCompletion K) (π : Q.adicCompletion K))
    {a : ℕ → ℕ} (hgrow : ∀ d : ℕ, d ≠ 0 → ∃ m : ℕ, d ∣ a m)
    (T : NK.LocalReciprocityLubinTate.LubinTateTowerGen (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K)) π a
      (NK.LocalReciprocityLubinTate.higherUnits (Q.adicCompletion K))
      (NK.LocalReciprocityLubinTate.residueCard (Q.adicCompletion K)))
    (hcov : ∀ (m n : ℕ)
      (L : IntermediateField (Q.adicCompletion K)
        (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
          (SeparableClosure (Q.adicCompletion K))))
      [FiniteDimensional (Q.adicCompletion K) L] [Normal (Q.adicCompletion K) L],
      NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥(T.level m n) ≤
        NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L →
      L ≤ T.level m n)
    (L : IntermediateField (Q.adicCompletion K)
      (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
        (SeparableClosure (Q.adicCompletion K))))
    [FiniteDimensional (Q.adicCompletion K) L] [Normal (Q.adicCompletion K) L]
    (hcomm : ∀ σ τ : ↥L ≃ₐ[Q.adicCompletion K] ↥L, σ * τ = τ * σ) :
    ∃ m n : ℕ, L ≤ T.level m n := by
  classical
  -- the norm group of `L`
  let N : Subgroup (Q.adicCompletion K)ˣ :=
    NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L
  -- the norm index theorem: `[Fˣ : N] = [L : F]`
  have hIdx : N.index = Module.finrank (Q.adicCompletion K) ↥L :=
    NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion Q L
  have hne : N.index ≠ 0 := by rw [hIdx]; exact ne_of_gt Module.finrank_pos
  have hfin : N.FiniteIndex := Subgroup.finiteIndex_iff.mpr hne
  -- cofinality of the higher unit filtration
  obtain ⟨n₀, hn₀⟩ := NK.LocalReciprocityLubinTate.Units.higherUnits_cofinal
    (Q.adicCompletion K) N hfin
  -- the unramified divisor of the norm index occurs among the `a m`
  obtain ⟨m, hm⟩ := hgrow N.index hne
  refine ⟨m, n₀, ?_⟩
  -- the covering hypothesis reduces the claim to a containment of norm groups
  refine hcov m n₀ L ?_
  show NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥(T.level m n₀) ≤ N
  -- the explicit reciprocity law: the norm group of the level is `⟨π^{a m}⟩ · U^{n₀+1}`
  rw [T.normGroup_eq]
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le]
    obtain ⟨k, hk⟩ := hm
    rw [hk, pow_mul]
    exact N.pow_mem (Subgroup.pow_index_mem N π) k
  · exact le_trans (NK.LocalReciprocityLubinTate.higherUnits_antitone (Q.adicCompletion K)
      (Nat.le_succ n₀)) hn₀

end NK.LocalReciprocityLubinTate.Unramified
