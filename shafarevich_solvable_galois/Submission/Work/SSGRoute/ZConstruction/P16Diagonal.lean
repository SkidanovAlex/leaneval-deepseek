import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.inv
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.preTwoExists
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_dictionary
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_squareAtSBlock
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_localNormalise
import Submission.Work.SSGRoute.H9.swTwoPlacePairingTwo
import Submission.Work.SSGRoute.NodeS37.claimOfPreTwo
import Submission.Work.SSGRoute.ZConstruction.HilbertSymbolTransitivity
import Submission.Work.SSGRoute.ZConstruction.LocalSquares
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.pinnedValue_diagonal_proved
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The p. 16 Claim of Schmidt–Wingberg (the `p = 2` diagonal case), a twin

`Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_diagonal` is the paper's Claim for the corrected
`p = 2` §4 recursion: for a history `s` with `PreTwo n s` for all `n`, the Kummer cochain of `b_m`
kills the local group of the `σ`-sibling of its *own* escape prime `Q_m` — the value there is
prescribed by neither the rule (4) nor the confinement, and must come from the arithmetic of
`b_m` (Schmidt–Wingberg, p. 16).

This file proves a *statement-identical twin* of it in this lane, so that the node's chain
(`ZConstruction/P2CoreTwin.lean` → `NodeS37.mu2ThreeHalvesProved` → `NodeS37.claimOfPreTwo` →
the diagonal case) can be re-pointed at this file without editing the lane that owns the original.

The proof has the same shape as the proved `m < l` case (`NodeS37.claimOfPreTwo_lt`): strong
confinement, a pinned Frobenius at the sibling, the passage from the pinned value to the whole
local group (`NodeS37.pinnedZeroImpLocalGroup`), and the `gesKConj` transport.  The one input
which the `m < l` case replaces by the two-place chain — the vanishing of the *pinned value* at the
sibling — is the p. 16 computation, isolated below as `pinnedValueAtSibling_eq_zero_diag`.
-/

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]

/-- The `PreTwo`-finiteness helper (identical to `NodeS37.preTwo_finPlace`): every escape prime of a
history satisfying the prefix invariant is a finite place. -/
theorem preTwo_finPlace_diag {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] [IsSepClosure ↥K Ω]
    {Λ : IntermediateField k Ω} [FiniteDimensional k Λ] [IsGalois k Λ]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s) (n : ℕ) :
    SSGRoute.IsFinPlace k ((s.f n).1) :=
  NodeS37.preTwo_finPlace (K := K) ζ hζ hζK S y s hs n

/-- **The p. 16 computation**: the pinned value of `χ_{b_m}` at the `t`-sibling of the escape prime
`Q_m` (`t = res k K σ` an involution `≠ 1`) vanishes.

This is the diagonal case of Schmidt–Wingberg's Claim, the irreducible arithmetic core: the value is
`(z, σz)_{K_{σQ}}` for a normalised representative `z` of `b_m`, and the product formula over
`Σ ∪ {σQ}` (together with the local dichotomy on `Σ`) kills it. -/
theorem pinnedValueAtSibling_eq_zero_diag {K Λ : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K] [IsSepClosure ↥K Ω]
    [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s)
    (m : ℕ) (t : K ≃ₐ[k] K) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) :
    Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
      (fun _ => ((s.f m).1, (s.f m).2))
      (fun _ => preTwo_finPlace_diag (K := K) ζ hζ hζK S y s hs m) 0 t = 0 := by
  -- Re-pointed (session 42) at the proved p. 16 computation
  -- `Work.SSGRoute.ZDataTwo.TwoRec.pinnedValue_diagonal_proved`
  -- (`ZDataTwo/TwoRec/pinnedValue_diagonal_proved.lean`, axiom-clean): the two statements agree
  -- up to the (proof-irrelevant) finiteness argument of `NodeS35.pinValue`.
  exact Work.SSGRoute.ZDataTwo.TwoRec.pinnedValue_diagonal_proved (K := K) (Λ := Λ) hKΛ ζ hζ hζK
    S hSfin hSdisj hSram y hy hyc hyS hyT hy0 hyinf s hs m t ht1 ht2

/-- **The p. 16 Claim** (statement-identical twin of `Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_diagonal`):
for a history satisfying `PreTwo` at every prefix, and every involution `res k K σ` of `Gal(K|k)`,
the Kummer cochain of `b_m` kills the local group of the `σ`-sibling of `Q_m`. -/
theorem claimOfPreTwoDiagonalTwin {K Λ : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K] [IsSepClosure ↥K Ω]
    [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s) :
    ∀ m : ℕ, ∀ σ : Ω ≃ₐ[k] Ω, σ ∉ K.fixingSubgroup → (SSGRoute.res k K σ) ^ 2 = 1 →
      ∀ u ∈ SSGRoute.decomp k (σ • (s.f m).1) ⊓ K.fixingSubgroup,
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (s.f m).2 u = 0 := by
  intro m σ hσK hσ2 u hu
  obtain ⟨hfin, hsplit, hdisjG, hdisjC, hexcl, hreal, hinv, hconf9, hnorm⟩ := hs (m + 1)
  have hm : m < m + 1 := Nat.lt_succ_self m
  set t : K ≃ₐ[k] K := SSGRoute.res k K σ with ht
  have ht1 : t ≠ 1 := by
    intro h1
    have hmem : σ ∈ (SSGRoute.res k K).ker := by
      rw [MonoidHom.mem_ker, ← ht]
      exact h1
    exact hσK (by rwa [IntermediateField.restrictNormalHom_ker K] at hmem)
  have ht2 : t ^ 2 = 1 := by
    rw [ht]
    exact hσ2
  -- the strong confinement of the recursion's classes outside their own escape prime
  have hconf : ∀ j : ℕ, ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K ((s.f j).1) B) →
      ∀ τ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f j).2 τ = 0 :=
    Work.SSGRoute.NodeS37.claimOfPreTwoConfined.claimOfPreTwoConfined (K := K) (Λ := Λ) hKΛ
      ζ hζ hζK S y hy hyT s hs
  -- the sibling of `Q_m` at `res σ`, and the `K`-conjugacy `σ • Q_m ∼ sibling`
  have hAtt : Work.SSGRoute.gesKConj K (σ • (s.f m).1)
      (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1) := by
    refine ⟨Work.SSGRoute.ZDataMup.galLift K t * σ⁻¹, ?_, ?_⟩
    · rw [← IntermediateField.restrictNormalHom_ker K, MonoidHom.mem_ker, map_mul, map_inv,
        Work.SSGRoute.ZDataMup.galLift_spec, ht, mul_inv_cancel]
    · show (Work.SSGRoute.ZDataMup.galLift K t * σ⁻¹) • (σ • (s.f m).1)
        = Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1
      rw [mul_smul, inv_smul_smul, Work.SSGRoute.ZDataMup.siblingPlace]
  have hQfin : SSGRoute.IsFinPlace k ((s.f m).1) := hfin m hm
  have hAfin : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1) :=
    (SSGRoute.isFinPlace_smul_iff (s.f m).1 (Work.SSGRoute.ZDataMup.galLift K t)).mpr hQfin
  have hQsplit : SSGRoute.IsSplitIn k K ((s.f m).1) :=
    Work.SSGRoute.NodeS35.isSplitIn_of_le (K := K) (N := Λ) hKΛ (hsplit m hm)
  have hsep : ¬ Work.SSGRoute.gesKConj K ((s.f m).1)
      (Work.SSGRoute.ZDataMup.galLift K t • (s.f m).1) :=
    Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj K ht1 hQsplit
  have hkillA : ∀ τ ∈ K.fixingSubgroup,
      SSGRoute.IsInertia k (Work.SSGRoute.ZDataMup.galLift K t • (s.f m).1) τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 τ = 0 :=
    fun τ hτK hτI => hconf m _ hAfin hsep τ hτK hτI
  -- the Kummer-pinned Frobenius at the sibling
  haveI : FiniteDimensional ↥K
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) (s.f m).2) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2)
      (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (s.f m).2
  haveI : IsGalois ↥K
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) (s.f m).2) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_isGalois (Ω := Ω) (K := K) (p := 2)
      (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (s.f m).2
  haveI : NumberField
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) (s.f m).2) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_numberField (Ω := Ω) (K := K) (p := 2)
      (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (s.f m).2
  obtain ⟨⟨ψ, hψ⟩, hpin⟩ := Work.SSGRoute.NodeS35.exists_pinned (K := K) (p := 2) ζ hζ hζK
    (fun _ => ((s.f m).1, (s.f m).2)) 0
    (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1) hAfin hkillA
  have hpinv : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 ψ
      = Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
          (fun _ => ((s.f m).1, (s.f m).2))
          (fun _ => preTwo_finPlace_diag (K := K) ζ hζ hζK S y s hs m) 0 t :=
    Work.SSGRoute.NodeS35.pinValue_eq (K := K) (p := 2) ζ hζ hζK
      (fun _ => ((s.f m).1, (s.f m).2))
      (fun _ => preTwo_finPlace_diag (K := K) ζ hζ hζK S y s hs m) 0 t ht1 ψ hψ hpin
  have hpinVal : Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
      (fun _ => ((s.f m).1, (s.f m).2))
      (fun _ => preTwo_finPlace_diag (K := K) ζ hζ hζK S y s hs m) 0 t = 0 :=
    pinnedValueAtSibling_eq_zero_diag (K := K) (Λ := Λ) hKΛ ζ hζ hζK S hSfin hSdisj hSram
      y hy hyc hyS hyT hy0 hyinf s hs m t ht1 ht2
  have h0 : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 ψ = 0 := by
    rw [hpinv, hpinVal]
  -- the whole local group at the sibling vanishes
  have hmain := Work.SSGRoute.NodeS37.pinnedZeroImpLocalGroup (K := K) ζ hζ hζK (s.f m).2
    (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1) hAfin hkillA ψ hψ hpin h0
  -- transport the local group of `σ • Q_m` to the sibling
  obtain ⟨w, hwK, hwA⟩ := hAtt
  have huK : u ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hu).2
  have huD : u ∈ SSGRoute.decomp k (σ • (s.f m).1) := (Subgroup.mem_inf.mp hu).1
  have hu'K : w * u * w⁻¹ ∈ K.fixingSubgroup :=
    K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem hwK huK) (K.fixingSubgroup.inv_mem hwK)
  have hu'D : w * u * w⁻¹ ∈ SSGRoute.decomp k
      (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1) := by
    show (w * u * w⁻¹) • (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1)
      = Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1
    rw [mul_smul, mul_smul, show w⁻¹ • (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1)
        = σ • (s.f m).1 from by rw [← hwA, inv_smul_smul],
      show u • (σ • (s.f m).1) = σ • (s.f m).1 from MulAction.mem_stabilizer_iff.mp huD, ← hwA]
  have hval : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 (w * u * w⁻¹)
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 u :=
    Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj K ζ hζ hζK (s.f m).2 hwK u
  have hfinal : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 u = 0 := by
    rw [← hval]
    exact hmain _ (Subgroup.mem_inf.mpr ⟨hu'D, hu'K⟩)
  rw [Work.SSGRoute.H9.CV2.nodeKummerCochar_eq_nodeKummerCocharZMod_two (K := K) ζ hζ hζK
    (s.f m).2 u]
  exact hfinal

end Work.SSGRoute.ZConstruction
