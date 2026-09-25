import Mathlib
import Submission.NK.GlobalCFT.Place
import Submission.NK.GlobalCFT.Idele
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFTdeep.Herbrand.SIdeles

/-!
# Vocabulary for the Kummer case of the second inequality (Milne, *CFT*, VII §6)

This file fixes the objects used in the proof of
`NK.GlobalCFTdeep.SecondInequality.secondInequality_of_isCyclic_prime_kummerCase`:
Milne's subgroup `E` of chapter VII §6, Lemma 6.4, together with its local building blocks.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

open NK.GlobalCFT

variable {K : Type} [Field K] [NumberField K]

/-- The subgroup `(K_vˣ)^p` of `p`-th powers in the local multiplicative group at a place `v`. -/
def localPow (p : ℕ) (v : Place K) : Subgroup ((Place.localField K v)ˣ) :=
  (powMonoidHom p : ((Place.localField K v)ˣ) →* ((Place.localField K v)ˣ)).range

/-- **Milne's subgroup `E`** (*CFT* VII §6, Lemma 6.4):
`E := ∏_{v∈S} K_v^{×p} · ∏_{v∈T} K_v^× · ∏_{v∉S∪T} U_v ≤ 𝕀 K`. -/
def kummerE (p : ℕ) (S T : Finset (Place K)) : Subgroup (Idele K) where
  carrier := {x | (∀ v ∈ S, x v ∈ localPow (K := K) p v) ∧
      (∀ v : Place K, v ∉ S → v ∉ T → x v ∈ Place.localUnits K v)}
  one_mem' := ⟨fun v _ => Subgroup.one_mem _, fun v _ _ => Subgroup.one_mem _⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨fun v hv => by rw [Idele.mul_apply]; exact Subgroup.mul_mem _ (hx1 v hv) (hy1 v hv),
      fun v hv hv' => by
        rw [Idele.mul_apply]
        exact Subgroup.mul_mem _ (hx2 v hv hv') (hy2 v hv hv')⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨fun v hv => by rw [Idele.inv_apply]; exact Subgroup.inv_mem _ (hx1 v hv),
      fun v hv hv' => by rw [Idele.inv_apply]; exact Subgroup.inv_mem _ (hx2 v hv hv')⟩

@[simp] theorem mem_kummerE {p : ℕ} {S T : Finset (Place K)} {x : Idele K} :
    x ∈ kummerE (K := K) p S T ↔ (∀ v ∈ S, x v ∈ localPow (K := K) p v) ∧
      (∀ v : Place K, v ∉ S → v ∉ T → x v ∈ Place.localUnits K v) := Iff.rfl


/-- The principal idèles of the `p`-th powers of the `T`-units: the subgroup
`((U(T))^p) ≤ 𝕀 K`.  Milne's Lemma 6.7 identifies it with `Kˣ ∩ E`. -/
def tUnitsPowIdele (p : ℕ) (T : Set (Place K)) : Subgroup (Idele K) :=
  Subgroup.map (Idele.principalIdele K) (Subgroup.map (powMonoidHom p) (TUnits (L := K) T))

/-- The embedding of the finite places into the places of `K`. -/
def placeOfFiniteEmb (K : Type) [Field K] [NumberField K] :
    HeightOneSpectrum (𝓞 K) ↪ Place K :=
  ⟨Place.ofFinite, fun _ _ h => Place.ofFinite_inj.mp h⟩

@[simp] theorem placeOfFiniteEmb_apply (q : HeightOneSpectrum (𝓞 K)) :
    placeOfFiniteEmb K q = Place.ofFinite q := rfl

end NK.GlobalCFTdeep.SecondInequality.KummerCase
