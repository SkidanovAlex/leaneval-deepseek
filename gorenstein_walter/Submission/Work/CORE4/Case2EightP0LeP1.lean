import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.ConjSubOrbitNcard

namespace Work.CORE4

/-- Bender 1981, §4 (8), p. 225, "obviously `p₀ ≤ p₁`": if `P ≤ A` and `N_U(P) ≤ N_G(A)`, then
`p₀ = |N_U(A) : N_U(P)|` is at most `p₁` = the number of `G`-conjugates of `P` lying in `A`
(the orbit of `P` under `N_U(A)`). -/
theorem Case2EightP0LeP1 {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (p : ℕ) (P A : Subgroup G)
    (hPA : P ≤ A)
    (h4 : B.U ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (A : Set G)) :
    Work.GW2.Case2EightP0 B P A ≤ Work.GW2.Case2EightP1 P A := by
  -- `p₁` counts the conjugates of `P` inside `A`, and `N_U(A)` permutes these (it normalizes
  -- `A`, while `P ≤ A`); so `p₁` is at least the length of the `N_U(A)`-orbit of `P`, which is
  -- `|N_U(A) : N_U(A) ⊓ N_G(P)| = |N_U(A) : N_U(P)| = p₀` (the last step is `h4`).
  classical
  -- `A₀ = N_U(A) = U ⊓ N_G(A)` and `P₀ = N_U(P) = U ⊓ N_G(P)`.
  let A₀ : Subgroup G := B.U ⊓ Subgroup.normalizer (A : Set G)
  let P₀ : Subgroup G := B.U ⊓ Subgroup.normalizer (P : Set G)
  -- the `N_U(A)`-orbit of `P`, and the set of `G`-conjugates of `P` inside `A` counted by `p₁`.
  let O : Set (Subgroup G) := {X : Subgroup G | ∃ h : G, h ∈ A₀ ∧ X = Work.GW2.conjSub h P}
  let S : Set (Subgroup G) := {X : Subgroup G | X ≤ A ∧ ∃ g : G, X = Work.GW2.conjSub g P}
  -- `h4` says exactly that `P₀ ≤ A₀`, hence the stabiliser of `P` in `A₀` is `P₀`
  -- (the inclusion `⊇` is the trivial `A₀ ⊓ N_G(P) ≤ U ⊓ N_G(P) = P₀`).
  have hstab : P₀ = A₀ ⊓ Subgroup.normalizer (P : Set G) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      exact ⟨⟨hx.1, h4 hx⟩, hx.2⟩
    · intro x hx
      exact ⟨hx.1.1, hx.2⟩
  -- every element of the orbit lies in `A`, i.e. is counted by `p₁`.
  have hsub : O ⊆ S := by
    rintro X ⟨h, hh, rfl⟩
    have hhA : Work.GW2.conjSub h A = A := by
      have hnA : h ∈ Subgroup.normalizer (A : Set G) := hh.2
      simpa [Work.GW2.conjSub] using (Subgroup.mem_normalizer_iff_map_conj_eq.mp hnA)
    refine ⟨?_, h, rfl⟩
    calc Work.GW2.conjSub h P ≤ Work.GW2.conjSub h A := Subgroup.map_mono hPA
      _ = A := hhA
  -- orbit–stabiliser: the orbit has `|A₀ : P₀| = p₀` elements.
  have horbit : O.ncard = (A₀ ⊓ Subgroup.normalizer (P : Set G)).relIndex A₀ :=
    ConjSubOrbitNcard A₀ P
  calc Work.GW2.Case2EightP0 B P A
      = P₀.relIndex A₀ := rfl
    _ = (A₀ ⊓ Subgroup.normalizer (P : Set G)).relIndex A₀ := by rw [hstab]
    _ = O.ncard := horbit.symm
    _ ≤ S.ncard := Set.ncard_le_ncard hsub
    _ = Work.GW2.Case2EightP1 P A := rfl

end Work.CORE4
