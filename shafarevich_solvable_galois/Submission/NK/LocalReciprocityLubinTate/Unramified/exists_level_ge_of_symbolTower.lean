import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.LocalReciprocityLubinTate.Units.higherUnits_cofinal
import Submission.NK.LocalReciprocityLubinTate.Unramified.Instance
import Submission.NK.LocalReciprocityLubinTate.Unramified.TowerSymbol
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.LocalReciprocityLubinTate.Unramified

theorem exists_level_ge_of_symbolTower {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {π : (Q.adicCompletion K)ˣ}
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer (Q.adicCompletion K) (π : Q.adicCompletion K))
    {a : ℕ → ℕ} (hgrow : ∀ d : ℕ, d ≠ 0 → ∃ m : ℕ, d ∣ a m)
    (T : NK.LocalReciprocityLubinTate.LubinTateTowerGen (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K)) π a
      (NK.LocalReciprocityLubinTate.higherUnits (Q.adicCompletion K))
      (NK.LocalReciprocityLubinTate.residueCard (Q.adicCompletion K)))
    (hcorr : NK.LocalReciprocityLubinTate.NormCorrespondence (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K)))
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
  -- choose the level with these parameters
  refine ⟨m, n₀, ?_⟩
  haveI hfdL : FiniteDimensional (Q.adicCompletion K) ↥(T.level m n₀) :=
    T.finiteDimensional _ _
  haveI hnorL : Normal (Q.adicCompletion K) ↥(T.level m n₀) := T.normal _ _
  -- the norm correspondence reduces the claim to a containment of norm groups
  refine hcorr (T.level m n₀) L (T.commutative _ _) hcomm ?_
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
