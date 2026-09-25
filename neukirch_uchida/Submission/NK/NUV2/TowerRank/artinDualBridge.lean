import Submission.NK.NUV2.TowerRank.towerIso
import Submission.NK.NUV2.TowerRank.towerCompatible
import Submission.NK.NUV2.TowerRank.le_dualRank_idele_of_gamma
import Submission.NK.NUV2.TowerRank.le_dualRank_gamma_of_levelPairIso
import Submission.NK.NUV2.TowerRank.levelPairIso_of_artinReciprocityIdeal
import Submission.NK.RankTheoryDeep.IdeleFinal
import Submission.NK.NUV2.localUnits_two
import Submission.NK.CFTLib.fundamentalClassElement

/-!
# `ArtinDualBridge Ω 2` from the level-pair correspondence, with `hFC` discharged

The module `Submission/Work/NUV2/TowerRank/assembly.lean` assembles the requested lemma
`NK.NUV2.hausRank_lowerBound_two` from three inputs: `hFC` (the global fundamental class),
Takagi's existence theorem and the levelwise norm-group/Galois-subgroup correspondence
`NK.NUV2.ArtinBridge.LevelPairIso`.

Since this workspace's `NK.CFTLib.fundamentalClassElement` **is now a theorem**
(axiom-clean, `Submission/Work/CFTLib/fundamentalClassElement.lean`), the `hFC` hypothesis is no
longer an input: this module records the resulting sharper reduction

  `ArtinReciprocityIdeal`  +  `ExistenceTheorem`   ⟹   `ArtinDualBridge Ω 2`,

with *no* hypothesised fundamental class.  It is placed in a module of its own (and not in
`assembly.lean`, which imports the target file `Submission.NK.NUV2.hausRank_lowerBound_two`) so
that the target file itself can import it — the target's final proof will be
`hausRank_lowerBound_two_of_artin Ω (Bridge.artinDualBridge_of_artinReciprocityIdeal h hEx Ω) M`.

## The mathematics

`ArtinDualBridge Ω 2` is half (A) + half (B):

* **(A)** `dualRank Γ_K 2 ≤ dualRank C_K 2`, from `hFC` alone
  (`NK.NUV2.TowerRank.le_dualRank_idele_of_gamma`, via the tower-compatibility crux
  `NK.NUV2.TowerRank.towerCompatible` and the finiteness of the idèle side);
* **(B)** `dualRank C_K 2 ≤ dualRank Γ_K 2`, from `hFC`, the existence theorem and
  `LevelPairIso` (`NK.NUV2.TowerRank.le_dualRank_gamma_of_levelPairIso`): the pair condition
  yields the coherence of the Artin isomorphisms, which transports a tower of quotients of `C_K`
  to a compatible tower of surjections of `Γ_K`.

`LevelPairIso K Ω ℓ` is itself *derived* from the ideal-theoretic reciprocity law
(`NK.NUV2.TowerRank.levelPairIso_of_artinReciprocityIdeal`), so the reduction above has the
reciprocity law as its only non-trivial input.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Cardinal

namespace NK.NUV2.TowerRank

open NK.RankTheoryDeep

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **A cardinal is determined by its natural-number approximations, when it is finite**: if
`b < ℵ₀` and every natural number `≤ a` is `≤ b`, then `a ≤ b`. -/
theorem le_of_forall_natCast_le {a b : Cardinal} (hb : b < ℵ₀)
    (h : ∀ n : ℕ, (n : Cardinal) ≤ a → (n : Cardinal) ≤ b) : a ≤ b := by
  have key : ∀ n : ℕ, b = (n : Cardinal) → a ≤ b := by
    intro n hbn
    by_contra hcon
    push Not at hcon
    have hlt : (n : Cardinal) < a := by rw [← hbn]; exact hcon
    have h1 : ((n + 1 : ℕ) : Cardinal) ≤ a := by
      rcases lt_or_ge a Cardinal.aleph0 with ha | ha
      · obtain ⟨k, hk⟩ : ∃ k : ℕ, a = ((k : ℕ) : Cardinal) :=
          ⟨a.toNat, (Cardinal.cast_toNat_of_lt_aleph0 ha).symm⟩
        have hlt' : ((n : ℕ) : Cardinal) < ((k : ℕ) : Cardinal) := by rw [← hk]; exact hlt
        have : ((n + 1 : ℕ) : Cardinal) ≤ ((k : ℕ) : Cardinal) := by
          have h' : n + 1 ≤ k := by
            have hnk : n < k := by exact_mod_cast hlt'
            omega
          exact_mod_cast h'
        rw [hk]; exact this
      · have h2 : ((n + 1 : ℕ) : Cardinal) ≤ Cardinal.aleph0 :=
          le_of_lt Cardinal.natCast_lt_aleph0
        exact le_trans h2 ha
    have h3 : ((n + 1 : ℕ) : Cardinal) ≤ (n : Cardinal) := by
      rw [← hbn]; exact h (n + 1) h1
    have h4 : n + 1 ≤ n := Nat.cast_le.mp h3
    omega
  exact key b.toNat (Cardinal.cast_toNat_of_lt_aleph0 hb).symm

/-- **The full rank equality from the two halves.**  Given the idèle-side finiteness (a theorem of
the workspace) and the two natural-number half-inequalities, the `ℤ_2`-ranks agree. -/
theorem dualRank_gamma_eq_dualRank_idele_of_halves {K : Type} [Field K] [NumberField K]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (hfin : dualRank (NK.GlobalCFT.IdeleClassGroup K) 2 < ℵ₀)
    (hA : ∀ r : ℕ, (r : Cardinal) ≤ dualRank (NK.Reconstruct.Gamma K Ω 2) 2 →
      (r : Cardinal) ≤ dualRank (NK.GlobalCFT.IdeleClassGroup K) 2)
    (hB : ∀ r : ℕ, (r : Cardinal) ≤ dualRank (NK.GlobalCFT.IdeleClassGroup K) 2 →
      (r : Cardinal) ≤ dualRank (NK.Reconstruct.Gamma K Ω 2) 2) :
    dualRank (NK.Reconstruct.Gamma K Ω 2) 2
      = dualRank (NK.GlobalCFT.IdeleClassGroup K) 2 := by
  refine le_antisymm (le_of_forall_natCast_le hfin hA) ?_
  have hnat : (((dualRank (NK.GlobalCFT.IdeleClassGroup K) 2).toNat : ℕ) : Cardinal)
      ≤ dualRank (NK.GlobalCFT.IdeleClassGroup K) 2 :=
    le_of_eq (Cardinal.cast_toNat_of_lt_aleph0 hfin)
  rw [← Cardinal.cast_toNat_of_lt_aleph0 hfin]
  exact hB _ hnat

/-- **The idèle side is finite** (unconditional in the workspace): the `ℤ_2`-rank of
`Hom_cts(C_K, ℤ_2)` is at most `[K : ℚ]`. -/
theorem dualRank_idele_lt_aleph0 (K : Type) [Field K] [NumberField K] :
    dualRank (NK.GlobalCFT.IdeleClassGroup K) 2 < ℵ₀ :=
  lt_of_le_of_lt
    (NK.RankTheoryDeep.ideleDualRankBound_of_localUnits (ℓ := 2)
      NK.NUV2.localUnits_two K)
    (by exact_mod_cast Cardinal.natCast_lt_aleph0)

namespace Bridge

/-- **`ArtinDualBridge Ω 2` with the fundamental class discharged**: from the existence theorem
and the level-pair correspondence alone.  The fundamental class is the *proved*
`NK.CFTLib.fundamentalClassElement`. -/
theorem artinDualBridge_of_levelPairIso
    (hEx : ∀ (K : Type) [Field K] [NumberField K], NK.GlobalCFT.ExistenceTheorem K)
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (hPair : ∀ (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsGalois K Ω],
      NK.NUV2.ArtinBridge.LevelPairIso K Ω 2) :
    ArtinDualBridge Ω 2 := by
  intro K _ _ _ _
  exact dualRank_gamma_eq_dualRank_idele_of_halves Ω (dualRank_idele_lt_aleph0 K)
    (fun r h => le_dualRank_idele_of_gamma r (towerCompatible r)
      NK.CFTLib.fundamentalClassElement Ω K h)
    (fun r h => le_dualRank_gamma_of_levelPairIso r (towerCompatible r)
      NK.CFTLib.fundamentalClassElement hEx Ω K (hPair K) h)

/-- **`ArtinDualBridge Ω 2` from the ideal-theoretic reciprocity law alone** (plus the existence
theorem): the canonicity input `LevelPairIso` is *derived* from the reciprocity law by
`NK.NUV2.TowerRank.levelPairIso_of_artinReciprocityIdeal`, and the fundamental class is the
proved `NK.CFTLib.fundamentalClassElement`. -/
theorem artinDualBridge_of_artinReciprocityIdeal (h : NK.CFTLib.ArtinReciprocityIdeal)
    (hEx : ∀ (K : Type) [Field K] [NumberField K], NK.GlobalCFT.ExistenceTheorem K)
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω] :
    ArtinDualBridge Ω 2 :=
  artinDualBridge_of_levelPairIso hEx Ω
    (fun K _ _ _ _ => by
      haveI : IsSepClosure K Ω := ⟨IsSepClosure.sep_closed ℚ, inferInstance⟩
      exact levelPairIso_of_artinReciprocityIdeal h K Ω 2)

end Bridge

end NK.NUV2.TowerRank
