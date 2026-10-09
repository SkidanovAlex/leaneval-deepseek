import Mathlib
import Submission.Work.SSGRoute.CC.MagFourDefs
import Submission.Work.SSGRoute.CC.MagFourMap
import Submission.Work.SSGRoute.CC.MagFourFreeGroup
import Submission.Work.SSGRoute.CC.Mag4EqZeroMemPSeries
import Submission.Work.SSGRoute.CC.Mag4Surjective
import Submission.Work.SSGRoute.CC.Mag4MemWsub
import Submission.Work.SSGRoute.CC.Mag4DoubleWordProved
import Submission.Work.SSGRoute.CC.Mag2CommutatorOf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Port of `Submission/Work/SSGRoute/magFourRealize.lean` using the proved double-word class

The chain-`B` file `magFourRealize.lean` invokes `Work.SSGRoute.mag4_doubleWord`, whose proof in
`Submission/Work/SSGRoute/mag4_doubleWord.lean` was still a `sorry`.  This module is a verbatim
copy of `magFourRealize.lean`, wrapped in the fresh namespace `Work.SSGRoute.LNS3B` and with that
invocation replaced by the (independently proved) `Work.SSGRoute.CC.LNS3.mag4_doubleWord_proved`, so
that the `(4,4)` graded step can be used without inheriting the `sorry`.
-/

namespace Work.SSGRoute.CC.LNS3B

/-!
# Realisation of the three subspaces `flgDeltaW`, `selfSpan`, `brkSpan` by norms

Every element of `flgDeltaW X (sigAL X σ) = (σA + id)(Wsub X)` is `mag4 X (ν z)` for some
`z ∈ γ₄`; every element of `selfSpan X σ` is `mag4 X (ν e)` for a product of self-pair witnesses;
every element of `brkSpan X σ` is `mag4 X (ν e)` for a product of double witnesses.  The norms
combine additively under products (`normG_mul_mag4`), which is what the final assembly uses.
-/

open scoped commutatorElement


open Work.SSGRoute.prop5

noncomputable section

variable {X : Type}

/-! ## Additivity of `mag4 ∘ ν` under products -/

/-- **The norm of a product, modulo `P₅ ∩ γ₄`.**  If `ν u` and `ν v` both lie in `γ₄`, then so does
`ν (u * v)`, and `mag4` of it is the sum of the `mag4`'s of the two factors. -/
theorem normG_mul_mag4 (X : Type) (σ : X ≃ X) (u v : FreeGroup X)
    (hu : normG X σ u ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3)
    (hv : normG X σ v ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3) :
    normG X σ (u * v) ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3 ∧
      mag4 X (normG X σ (u * v)) = mag4 X (normG X σ v) + mag4 X (normG X σ u) := by
  have h1 : normG X σ (u * v) = normG X σ v * (v⁻¹ * normG X σ u * v) := normG_mul X σ u v
  have hk : v⁻¹ * normG X σ u * v = normG X σ u * ⁅(normG X σ u)⁻¹, v⁻¹⁆ := by
    rw [commutatorElement_def]
    group
  have hkγ : ⁅(normG X σ u)⁻¹, v⁻¹⁆ ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 4 := by
    have hb := prop5.commutator_lowerCentralSeries_le (FreeGroup X) 3 0
      (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hu) (Subgroup.mem_top (v⁻¹)))
    simpa using hb
  have hkγ3 : ⁅(normG X σ u)⁻¹, v⁻¹⁆ ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3 :=
    (Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup (FreeGroup X)))
      (by norm_num : 3 ≤ 4) hkγ
  have hkP : ⁅(normG X σ u)⁻¹, v⁻¹⁆ ∈ Work.Shrinking.pCentralSeries 2 (FreeGroup X) 4 :=
    Work.ProP.lowerCentralSeries_le_pCentralSeries 2 (FreeGroup X) 4 hkγ
  have hk0 : mag4 X ⁅(normG X σ u)⁻¹, v⁻¹⁆ = 0 :=
    mag4_eq_zero_of_mem_pSeries hkγ3 hkP
  have huk : normG X σ u * ⁅(normG X σ u)⁻¹, v⁻¹⁆
      ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3 :=
    Subgroup.mul_mem _ hu hkγ3
  refine ⟨?_, ?_⟩
  · rw [h1, hk]
    exact Subgroup.mul_mem _ hv huk
  · rw [h1, hk]
    rw [mag4_mul hv huk, mag4_mul hu hkγ3, hk0, add_zero]

/-! ## The three realisations -/

/-- Every element of `flgDeltaW X (sigAL X σ) = (σA + id)(Wsub X)` is the `mag4`-class of the norm
of an element of `γ₄`. -/
theorem realize_flgDeltaW (X : Type) (σ : X ≃ X)
    (w : MonoidAlgebra (ZMod 2) (FreeMonoid X)) (hw : w ∈ flgDeltaW X (sigAL X σ)) :
    ∃ z : FreeGroup X, normG X σ z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3 ∧
      mag4 X (normG X σ z) = w := by
  rw [flgDeltaW, Submodule.mem_map] at hw
  obtain ⟨v, hv, hvw⟩ := hw
  obtain ⟨z, hzγ, hzmag⟩ := mag4_surjective hv
  have hγ : FreeGroup.freeGroupCongr σ z
      ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3 :=
    freeGroupCongr_mem_lowerCentralSeries_three X σ hzγ
  have h2 : sigA X σ v + v = w := by
    have h := hvw
    rwa [LinearMap.add_apply, LinearMap.id_apply] at h
  refine ⟨z, ?_, ?_⟩
  · rw [normG]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hγ) hzγ
  · rw [normG, mag4_mul (Subgroup.inv_mem _ hγ) hzγ, mag4_inv hγ, mag4_congr, hzmag, h2]

/-- Every element of `selfSpan X σ` is the `mag4`-class of the norm of a product of self-pair
witnesses. -/
theorem realize_selfSpan (X : Type) (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x)
    (hfree : ∀ x, σ x ≠ x) (s : MonoidAlgebra (ZMod 2) (FreeMonoid X))
    (hs : s ∈ selfSpan X σ) :
    ∃ e : FreeGroup X, normG X σ e ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3 ∧
      mag4 X (normG X σ e) = s := by
  refine Submodule.span_induction (p := fun s _ => ∃ e : FreeGroup X,
      normG X σ e ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3 ∧
      mag4 X (normG X σ e) = s) ?_ ?_ ?_ ?_ hs
  · rintro _ ⟨x, rfl⟩
    refine ⟨selfPairElt X σ x, ?_, ?_⟩
    · rw [← selfPairWord_eq_normG]
      exact selfPairWord_mem X σ hσ hfree x
    · rw [← selfPairWord_eq_normG]
      exact mag4_selfPairWord X σ hσ hfree x
  · refine ⟨1, ?_, ?_⟩
    · simp [normG]
    · rw [normG_one, mag4_one]
  · rintro a b _ _ ⟨ea, hma, hmaeq⟩ ⟨eb, hmb, hmbeq⟩
    refine ⟨ea * eb, ?_, ?_⟩
    · exact (normG_mul_mag4 X σ ea eb hma hmb).1
    · rw [(normG_mul_mag4 X σ ea eb hma hmb).2, hmaeq, hmbeq, add_comm]
  · intro c a _ ⟨ea, hma, hmaeq⟩
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with hc | hc
    · subst hc
      refine ⟨1, ?_, ?_⟩
      · simp [normG]
      · rw [normG_one, mag4_one, zero_smul]
    · subst hc
      simpa using ⟨ea, hma, hmaeq⟩

/-- Every element of `brkSpan X σ` is the `mag4`-class of the norm of a product of double
witnesses. -/
theorem realize_brkSpan (X : Type) (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x)
    (s : MonoidAlgebra (ZMod 2) (FreeMonoid X)) (hs : s ∈ brkSpan X σ) :
    ∃ e : FreeGroup X, normG X σ e ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3 ∧
      mag4 X (normG X σ e) = s := by
  refine Submodule.span_induction (p := fun s _ => ∃ e : FreeGroup X,
      normG X σ e ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3 ∧
      mag4 X (normG X σ e) = s) ?_ ?_ ?_ ?_ hs
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    refine ⟨⁅FreeGroup.of x, FreeGroup.of y⁆ * FreeGroup.freeGroupCongr σ ⁅FreeGroup.of x, FreeGroup.of y⁆, ?_, ?_⟩
    · rw [← doubleWord_eq_normG]
      refine double_witness_four X σ hσ _ ?_
      rw [Subgroup.lowerCentralSeries_one]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    · rw [← doubleWord_eq_normG]
      rw [Work.SSGRoute.CC.LNS3.mag4_doubleWord_proved X σ hσ _ (by
        rw [Subgroup.lowerCentralSeries_one]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))]
      simp only [commutatorElement_def, mag2_commutator_of]
  · refine ⟨1, ?_, ?_⟩
    · simp [normG]
    · rw [normG_one, mag4_one]
  · rintro a b _ _ ⟨ea, hma, hmaeq⟩ ⟨eb, hmb, hmbeq⟩
    refine ⟨ea * eb, ?_, ?_⟩
    · exact (normG_mul_mag4 X σ ea eb hma hmb).1
    · rw [(normG_mul_mag4 X σ ea eb hma hmb).2, hmaeq, hmbeq, add_comm]
  · intro c a _ ⟨ea, hma, hmaeq⟩
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with hc | hc
    · subst hc
      refine ⟨1, ?_, ?_⟩
      · simp [normG]
      · rw [normG_one, mag4_one, zero_smul]
    · subst hc
      simpa using ⟨ea, hma, hmaeq⟩

end

end Work.SSGRoute.CC.LNS3B
