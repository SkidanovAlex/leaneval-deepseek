import Mathlib
import Submission.Work.CORE4.Defs27
import Submission.Work.CORE4.Case2NormalizerP
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.ConjSub.conjSub_mul
import Submission.Work.CORE4.ConjSub.normalizer_conjSub

set_option linter.unusedVariables false

namespace Work.CORE4

/-! ## `Work.CORE4.PerZConjLayer`

**Mathematical content.**  In the `Case2Ctx` of §4, let `E = E(M) = layerIn h.D.M` be the layer
of `M`, and let `p` be a prime with an order-`p` subgroup `P ≤ h.D.F ≤ M`.  Then `E` is normal in
`M` (`layerIn_le_normalizer`), and `P` detects `M`:  `N_G(P) = M` (`Case2NormalizerP`, using that
`F` is cyclic and the TI-property of `F`).

Hence if `P^g = P^{h'}`, the element `u = g h'⁻¹` normalises `P^{h'}`, so
`u ∈ N_G(P^{h'}) = (N_G P)^{h'} = M^{h'} ⊆ (N_G E)^{h'} = N_G(E^{h'})`, where the last step is
`ConjSub.normalizer_conjSub` and the containment is `M ≤ N_G E`.  Therefore `E^u = E` after
conjugating by `h'`, i.e. `E^g = E^{h'}`. -/

/-- A subgroup whose cardinality is a prime is nontrivial. -/
lemma ne_bot_of_card_eq_prime_c4 {G : Type*} [Group G] {P : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hcard : Nat.card ↥P = p) : P ≠ ⊥ := by
  intro hbot
  have h1 : Nat.card ↥P = 1 := by rw [hbot]; exact Subgroup.card_bot
  rw [hcard] at h1
  exact hp.ne_one h1

theorem PerZConjLayer (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) (p : ℕ) (P : Subgroup G)
        (g h' : G),
        p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
        Work.GW2.conjSub g P = Work.GW2.conjSub h' P →
        Work.GW2.conjSub g (Work.GW2.layerIn h.D.M) =
          Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M) := by
  intro G _ _ hbc B h p P g h' hp hPF hcard hconj
  -- `P ≠ ⊥`, since `|P| = p` is prime.
  have hPne : P ≠ ⊥ := ne_bot_of_card_eq_prime_c4 hp hcard
  -- Bender §4 (11)/(12): `P` detects `M`, i.e. `N_G(P) = M`.
  have hNP : Subgroup.normalizer (P : Set G) = h.D.M :=
    Case2NormalizerP G B h P hPF hPne
  set E : Subgroup G := Work.GW2.layerIn h.D.M with hE
  -- `u := g h'⁻¹` conjugates `P^{h'}` to `P^g = P^{h'}`, so it normalises `P^{h'}`.
  set u : G := g * h'⁻¹ with hu
  have hu_h : u * h' = g := by rw [hu]; group
  have hconj2 : Work.GW2.conjSub u (Work.GW2.conjSub h' P) = Work.GW2.conjSub h' P := by
    rw [← ConjSub.conjSub_mul, hu_h]
    exact hconj
  have hmem : u ∈ Subgroup.normalizer (Work.GW2.conjSub h' P : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hconj2
  -- `N_G(P^{h'}) = (N_G P)^{h'} = M^{h'}`.
  have hmu : u ∈ Work.GW2.conjSub h' h.D.M := by
    rwa [ConjSub.normalizer_conjSub, hNP] at hmem
  -- `M` normalises `E = E(M)`.
  have hME : h.D.M ≤ Subgroup.normalizer (E : Set G) := by
    rw [hE]; exact layerIn_le_normalizer h.D.M
  -- hence `u` normalises `E^{h'}`.
  have hmemE : u ∈ Subgroup.normalizer (Work.GW2.conjSub h' E : Set G) := by
    rw [ConjSub.normalizer_conjSub]
    exact Subgroup.map_mono hME hmu
  have hfix : Work.GW2.conjSub u (Work.GW2.conjSub h' E) = Work.GW2.conjSub h' E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hmemE
  calc Work.GW2.conjSub g E = Work.GW2.conjSub (u * h') E := by rw [hu_h]
    _ = Work.GW2.conjSub u (Work.GW2.conjSub h' E) := ConjSub.conjSub_mul u h' E
    _ = Work.GW2.conjSub h' E := hfix

end Work.CORE4
