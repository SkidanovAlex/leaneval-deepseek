import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.asmDefs

/-!
# Colours using the singleton object `{w}`

At most `𝓜.singles w` of the object matchings `N i` can contain an object with
vertex set `{w}`: such an object is a copy of the singleton edge, there are
`𝓜.singles w` copies, each matching uses at most one of them, and distinct
values of `i` use distinct objects.
-/

set_option autoImplicit false

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

theorem EdgeObj.eq_singleton_copy {n : ℕ} {𝓜 : MultiHypergraph n}
    (hlin : 𝓜.IsLinear) {x : EdgeObj 𝓜} {w : Fin n}
    (hx : EdgeObj.toSet x = ({w} : Set (Fin n))) :
    ∃ k : Fin (𝓜.singles w), x = copyObj 𝓜 w k := by
  cases x with
  | inl a =>
    exfalso
    have h2 : 2 ≤ (a.1).ncard := by
      have h := hlin.1 a.1 a.2
      rwa [edgeSize_eq_ncard] at h
    have h1 : (a.1 : Set (Fin n)) = {w} := hx
    rw [h1, Set.ncard_singleton] at h2
    omega
  | inr p =>
    have hp : p.1.1 = w := by
      have h := hx
      rw [EdgeObj.toSet_inr, Set.singleton_eq_singleton_iff] at h
      exact h
    refine ⟨⟨p.1.2, hp ▸ p.2⟩, ?_⟩
    rw [copyObj]
    congr 1
    exact Subtype.ext (Prod.ext hp rfl)

theorem ncard_colours_singleton_le {n : ℕ} {ι : Type*} [Fintype ι]
    {𝓜 : MultiHypergraph n}
    (hlin : 𝓜.IsLinear)
    (N : ι → Set (EdgeObj 𝓜))
    (hmatch : ∀ i, IsObjMatching (N i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (N i) (N j)) (w : Fin n) :
    ({i : ι | ({w} : Set (Fin n)) ∈ objFam (N i)} : Set ι).ncard ≤
      𝓜.singles w := by
  classical
  set A : Set ι := {i | ({w} : Set (Fin n)) ∈ objFam (N i)} with hA
  have hex : ∀ i ∈ A, ∃ k : Fin (𝓜.singles w), copyObj 𝓜 w k ∈ N i := by
    rintro i hi
    obtain ⟨x, hx, hxe⟩ := hi
    obtain ⟨k, rfl⟩ := EdgeObj.eq_singleton_copy hlin hxe
    exact ⟨k, hx⟩
  choose f hf using hex
  have hiff : ∀ (i j : ι) (hi : i ∈ A) (hj : j ∈ A), f i hi = f j hj → i = j := by
    intro i j hi hj h
    by_contra hne
    have h1 : copyObj 𝓜 w (f i hi) ∈ N i := hf i hi
    have h2 : copyObj 𝓜 w (f i hi) ∈ N j := by rw [h]; exact hf j hj
    exact (Set.disjoint_left.mp (hdisj i j hne) h1) h2
  have hinj : Function.Injective (fun i : A => f i.1 i.2) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    exact Subtype.ext (hiff i j hi hj h)
  have hc := Nat.card_le_card_of_injective (fun i : A => f i.1 i.2) hinj
  have hcard : Nat.card (Fin (𝓜.singles w)) = 𝓜.singles w := by simp
  rw [hcard] at hc
  exact hc

end Work.Deep.Nibble
