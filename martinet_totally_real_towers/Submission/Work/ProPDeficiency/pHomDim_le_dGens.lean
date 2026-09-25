import Mathlib
import Submission.Work.ProPDeficiency.Basic
import Submission.Work.ProPDeficiency.HomRank

set_option linter.style.haveILetI false

namespace Work.ProPDeficiency

-- File: Submission/Work/ProPDeficiency/pHomDim_le_dGens.lean, namespace `Work.ProPDeficiency`.
-- `pHomDim p G = Nat.log p (Nat.card (G →* Multiplicative (ZMod p)))` is the `𝔽_p`-dimension of
-- `H¹(G, 𝔽_p)`, and `dGens G` is the minimal number of generators (both defined in
-- `Submission.Work.ProPDeficiency.Basic` / `HomRank`).
-- A hom is determined by its values on a generating finset `S` of size `dGens G`
-- (`exists_minimalGeneratingSet`), so `HomFp p G ↪ (S → Multiplicative (ZMod p))`, giving
-- `Nat.card (HomFp p G) ≤ p ^ dGens G`; then `Nat.log_mono_right` and `Nat.log_pow`.
theorem pHomDim_le_dGens {p : ℕ} (hp : 1 < p) {G : Type*} [Group G] [Group.FG G] :
    pHomDim p G ≤ dGens G := by
  classical
  haveI : NeZero p := ⟨by omega⟩
  obtain ⟨S, hSmin, hScard⟩ := exists_minimalGeneratingSet (G := G) (inferInstance : Group.FG G)
  have hgen : Subgroup.closure (S : Set G) = ⊤ := hSmin.1
  have hinj : Function.Injective (fun φ : HomFp p G => fun s : S => φ s) := by
    intro φ ψ h
    ext g
    have hEq : ∀ s : G, s ∈ (S : Set G) → φ s = ψ s := fun s hs => congrFun h ⟨s, hs⟩
    let E : Subgroup G :=
      { carrier := {g | φ g = ψ g}
        one_mem' := by show φ 1 = ψ 1; simp
        mul_mem' := by
          intro a b ha hb
          show φ (a * b) = ψ (a * b)
          rw [map_mul, map_mul, ha, hb]
        inv_mem' := by
          intro a ha
          show φ a⁻¹ = ψ a⁻¹
          rw [map_inv, map_inv, ha] }
    have hsub : (S : Set G) ⊆ (E : Set G) := fun s hs => hEq s hs
    have htop : (⊤ : Subgroup G) ≤ E := by
      rw [← hgen]; exact (Subgroup.closure_le E).mpr hsub
    exact htop (Subgroup.mem_top g)
  have hcard : Nat.card (HomFp p G) ≤ Nat.card (S → Multiplicative (ZMod p)) :=
    Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_fun, natCard_multiplicative_zmod] at hcard
  have hScardNat : Nat.card (↥S) = S.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hScardNat, hScard] at hcard
  rw [pHomDim]
  exact le_trans (Nat.log_mono_right hcard) (le_of_eq (Nat.log_pow hp (dGens G)))

end Work.ProPDeficiency
