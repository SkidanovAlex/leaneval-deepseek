import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.Fiber
import Submission.NK.GlobalCFTdeep.Herbrand.FiniteIndex
import Submission.NK.GlobalCFTdeep.Herbrand.SupportedIdelesInsert
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT

theorem herbrandEq_supportedIdeles_of_insert {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]
    (S S' : Finset (NK.GlobalCFT.Place K)) (v₀ : NK.GlobalCFT.Place K) (hv₀ : v₀ ∉ S)
    (hS' : ∀ v : NK.GlobalCFT.Place K, v ∈ S' ↔ v = v₀ ∨ v ∈ S)
    (T : Set (NK.GlobalCFT.Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : NK.GlobalCFT.Place L⦄, w ∈ T → σ • w ∈ T)
    (T' : Set (NK.GlobalCFT.Place L))
    (hT' : ∀ (σ : L ≃ₐ[K] L) ⦃w : NK.GlobalCFT.Place L⦄, w ∈ T' → σ • w ∈ T')
    (hTT' : T = {w : NK.GlobalCFT.Place L | ∃ v ∈ S, NK.GlobalCFT.Place.LiesOver w v})
    (hT'T : T' = {w : NK.GlobalCFT.Place L | ∃ v ∈ S', NK.GlobalCFT.Place.LiesOver w v})
    (n m : ℕ)
    (hfib : NK.GlobalCFTdeep.HerbrandEq
      (NK.GlobalCFTdeep.fiberIdelesRep (L := L) v₀) n)
    (hT_herb : NK.GlobalCFTdeep.HerbrandEq
      (NK.GlobalCFTdeep.supportedIdelesRep (L := L) T hT) m)
    (hf1 : NK.GlobalCFTdeep.FiniteTate (NK.GlobalCFTdeep.fiberIdelesRep (L := L) v₀))
    (hf2 : NK.GlobalCFTdeep.FiniteTate (NK.GlobalCFTdeep.supportedIdelesRep (L := L) T hT))
    (hf3 : NK.GlobalCFTdeep.FiniteTate (NK.GlobalCFTdeep.supportedIdelesRep (L := L) T' hT')) :
    NK.GlobalCFTdeep.HerbrandEq (NK.GlobalCFTdeep.supportedIdelesRep (L := L) T' hT')
      (n * m) := by
  classical
  -- the place `v₀` belongs to `S'`, and `S ⊆ S'`
  have hv₀S' : v₀ ∈ S' := (hS' v₀).mpr (Or.inl rfl)
  have hSS' : ∀ v : Place K, v ∈ S → v ∈ S' := fun v hv => (hS' v).mpr (Or.inr hv)
  -- membership in `T` and in `T'`
  have hT_mem : ∀ {w : Place L}, w ∈ T → ∃ v ∈ S, Place.LiesOver w v := by
    intro w hw
    have h := hw
    rw [hTT'] at h
    exact h
  have hT'_mem : ∀ {w : Place L}, w ∈ T' → ∃ v ∈ S', Place.LiesOver w v := by
    intro w hw
    have h := hw
    rw [hT'T] at h
    exact h
  -- `T ⊆ T'`
  have hsub : T ⊆ T' := by
    intro w hw
    obtain ⟨v, hv, hvw⟩ := hT_mem hw
    rw [hT'T]
    exact ⟨v, hSS' v hv, hvw⟩
  -- the fibre of `v₀` is contained in `T'`
  have hfiberT' : ∀ w : Place L, Place.LiesOver w v₀ → w ∈ T' := by
    intro w hw
    rw [hT'T]
    exact ⟨v₀, hv₀S', hw⟩
  -- no place of `T` lies above `v₀`
  have hdisj : ∀ w : Place L, w ∈ T → ¬ Place.LiesOver w v₀ := by
    intro w hw hwv
    obtain ⟨v, hv, hvw⟩ := hT_mem hw
    have hvv₀ : v = v₀ := Inclusion.globalCFT_liesOver_unique hvw hwv
    exact hv₀ (hvv₀ ▸ hv)
  -- every place of `T'` lies in `T` or above `v₀`
  have hcomp : ∀ w : Place L, w ∈ T' → w ∈ T ∨ Place.LiesOver w v₀ := by
    intro w hw
    obtain ⟨v, hv, hvw⟩ := hT'_mem hw
    rcases (hS' v).mp hv with hv₀' | hvS
    · exact Or.inr (hv₀' ▸ hvw)
    · refine Or.inl ?_
      rw [hTT']
      exact ⟨v, hvS, hvw⟩
  have hmain := herbrandEq_supportedIdeles_of_shortExact (K := K) (L := L) T T' v₀
    hT hT' hsub hdisj hcomp hfiberT' n m hfib hT_herb hf1 hf2 hf3
  have hmul : m * n = n * m := Nat.mul_comm m n
  rwa [hmul] at hmain

end NK.GlobalCFTdeep.Herbrand
