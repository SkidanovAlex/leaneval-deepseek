import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.SIdeles

/-!
# Milne's subgroup `E` of the idèle group

In the algebraic proof of the second inequality for cyclic `L/K` of prime degree `p` (Milne,
*Class Field Theory*, VII §6) one fixes a finite set `S` of places of `K` (containing the infinite
places, the primes over `p`, the places where a Kummer generator of `L/K` is not a unit, and a
generating set for the ideal class group) and a finite set `T` of primes outside `S` splitting
completely in `L`, and considers the subgroup

`E := ∏_{v∈S} K_v^{×p} · ∏_{v∈T} K_v^× · ∏_{v∉S∪T} U_v ≤ 𝕀 K`

of the idèle group.  Its two properties that drive the proof are

* `E ≤ N_{L/K} 𝕀_L` (Lemma 6.4), because the local extension is trivial at the primes in `T`,
  unramified outside `S ∪ T`, and of degree dividing `p` at the places of `S`;
* `[𝕀_K : Kˣ·E] = p` (Lemmas 6.5–6.7), a computation with `[TIdeles (S∪T) : E] = p^{2|S|}` and
  `Kˣ ∩ E = U(S∪T)^p`.

This file only fixes the vocabulary; the index computations are in the neighbouring files.
-/

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality

open NK.GlobalCFT

/-- The subgroup of `p`-th powers in the local multiplicative group `K_vˣ` at a place `v`. -/
def localPowSubgroup {K : Type} [Field K] [NumberField K] (p : ℕ) (v : Place K) :
    Subgroup ((Place.localField K v)ˣ) :=
  (powMonoidHom p : ((Place.localField K v)ˣ) →* ((Place.localField K v)ˣ)).range

/-- **Milne's subgroup `E`** (CFT, VII §6, Lemma 6.4):

`E := ∏_{v∈S} K_v^{×p} · ∏_{v∈T} K_v^× · ∏_{v∉S∪T} U_v`,

as a subgroup of the idèle group `𝕀 K`.  The components at the places of `T` are unconstrained,
because a prime of `T` is meant to split completely in `L`, so that *every* element of `K_v` is a
local norm there. -/
def milneE {K : Type} [Field K] [NumberField K] (p : ℕ) (S T : Finset (Place K)) :
    Subgroup (Idele K) where
  carrier := {x | (∀ v ∈ S, x v ∈ localPowSubgroup p v) ∧
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

theorem mem_milneE {K : Type} [Field K] [NumberField K] {p : ℕ} {S T : Finset (Place K)}
    {x : Idele K} :
    x ∈ milneE p S T ↔ (∀ v ∈ S, x v ∈ localPowSubgroup p v) ∧
      (∀ v : Place K, v ∉ S → v ∉ T → x v ∈ Place.localUnits K v) := Iff.rfl

end NK.GlobalCFTdeep.SecondInequality
