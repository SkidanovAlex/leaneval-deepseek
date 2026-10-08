import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.bender26c_key

namespace Work.CORE2A

open Subgroup
open Work.GW2

/-- The conjugation automorphism `x ↦ g * x * g⁻¹`, in the shape of a monoid homomorphism,
acts as `MulAut.conj_apply`. -/
theorem coe_mulAut_conj_apply {G : Type*} [Group G] (g x : G) :
    (↑(MulAut.conj g) : G →* G) x = g * x * g⁻¹ := by
  simp [MulAut.conj_apply]

theorem P_eq_iSup_centralizer_conj (T : Work.GW2.LocalToolkit) {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (P : Subgroup G)
    (hP : IsPGroup p P) (hHN : B.H ≤ Subgroup.normalizer (P : Set G))
    (hmin : ∀ Q : Subgroup G, Q < P → IsPGroup p Q → B.H ≤ Subgroup.normalizer (Q : Set G) → Q ≤ Subgroup.centralizer ({B.t} : Set G))
    (hnot : ¬ P ≤ Subgroup.centralizer ({B.t} : Set G))
    (V : Subgroup G) (hV4 : Work.GW2.IsFourGroup V) (hVS : V ≤ (B.S : Subgroup G)) (htV : B.t ∈ V)
    (s : G) (hsV : s ∈ V) (hs1 : s ≠ 1) (hst : s ≠ B.t)
    (hbig : ¬ (P ⊓ Subgroup.centralizer ({s} : Set G) ≤ P ⊓ Subgroup.centralizer ({B.t} : Set G))) :
    P = ⨆ (h : G) (_ : h ∈ B.H), (P ⊓ Subgroup.centralizer ({(h * s * h⁻¹)} : Set G)) := by
  let F : G → Subgroup G := fun h => P ⊓ Subgroup.centralizer ({(h * s * h⁻¹)} : Set G)
  let J : Subgroup G := ⨆ (h : G) (_ : h ∈ B.H), F h
  change P = J
  -- every term of the family lies in `P`, so `J ≤ P`
  have hJle : J ≤ P := by
    dsimp only [J]
    refine iSup_le fun h => iSup_le fun _ => ?_
    exact inf_le_left
  -- the term `h = 1` is `P ⊓ C(s)`
  have h1 : P ⊓ Subgroup.centralizer ({s} : Set G) ≤ J := by
    have hmem : (1 : G) ∈ B.H := B.H.one_mem
    have hle : F (1 : G) ≤ J :=
      le_iSup₂ (f := fun (h : G) (_ : h ∈ B.H) => F h) (1 : G) hmem
    simpa [F] using hle
  -- conjugation by `h' ∈ H` moves each term of the family to another term of the family
  have hmapF_le : ∀ (h' i : G), h' ∈ B.H → Subgroup.map (MulAut.conj h') (F i) ≤ F (h' * i) := by
    intro h' i hh'
    refine le_inf ?_ ?_
    · have hp : Subgroup.map (MulAut.conj h') P = P :=
        (Subgroup.mem_normalizer_iff_map_conj_eq (H := P) (g := h')).mp (hHN hh')
      calc Subgroup.map (MulAut.conj h') (F i)
          ≤ Subgroup.map (MulAut.conj h') P := Subgroup.map_mono inf_le_left
        _ = P := hp
    · calc Subgroup.map (MulAut.conj h') (F i)
          ≤ Subgroup.map (MulAut.conj h') (Subgroup.centralizer ({(i * s * i⁻¹)} : Set G)) :=
            Subgroup.map_mono inf_le_right
        _ ≤ Subgroup.centralizer ({(h' * i) * s * (h' * i)⁻¹} : Set G) := by
            refine le_trans (Subgroup.map_centralizer_le_centralizer_image _ _) ?_
            rw [Set.image_singleton]
            apply Subgroup.centralizer_le
            rw [Set.singleton_subset_iff, Set.mem_singleton_iff, coe_mulAut_conj_apply]
            group
  -- `H` normalizes `J`
  have hJnorm : B.H ≤ Subgroup.normalizer (J : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro h' hh' k hk
    have hmap : Subgroup.map (MulAut.conj h') J ≤ J := by
      dsimp only [J]
      rw [Subgroup.map_iSup]
      refine iSup_le fun i => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hi => ?_
      exact le_trans (hmapF_le h' i hh')
        (le_iSup₂ (f := fun (h : G) (_ : h ∈ B.H) => F h) (h' * i) (B.H.mul_mem hh' hi))
    have hmem : (↑(MulAut.conj h') : G →* G) k ∈ J :=
      hmap (Subgroup.mem_map_of_mem (↑(MulAut.conj h') : G →* G) hk)
    simpa [coe_mulAut_conj_apply] using hmem
  -- minimality: a proper `H`-invariant `p`-subgroup of `P` is centralized by `t`
  refine le_antisymm ?_ hJle
  by_contra hcon
  have hne : J ≠ P := fun h => hcon (le_of_eq h.symm)
  have hlt : J < P := lt_of_le_of_ne hJle hne
  have hPJ : IsPGroup p J := IsPGroup.to_le hP hJle
  have hJcent : J ≤ Subgroup.centralizer ({B.t} : Set G) := hmin J hlt hPJ hJnorm
  exact hbig (le_inf inf_le_left (le_trans h1 hJcent))

end Work.CORE2A
