import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.PSL.ti_pslUnipotent
import Submission.Work.L2F.PSL.normalizer_pslUnipotent_card
import Submission.Work.L2F.PSL.normalizer_le_normalizer_of_ti
import Submission.Work.L2F.PSL.natCard_normalizer_conj
import Submission.Work.L2F.PSL.exists_map_conj_eq_of_sylow
import Submission.Work.L2F.PSL.pslUnipotent_sylow
import Submission.Work.L2F.PSL.natCard_normalizer_pslUnipotent
import Submission.Work.PSL2.Card

namespace Work.L2F.PSL

/-- **The normalizer of a nontrivial `p`-subgroup of `PSL(2,GF(p,k))`.**  For `p` an odd prime with
`5 ≤ p^k` and `⊥ ≠ P ≤ PSL(2,GF(p,k))` a `p`-subgroup, the order of `N(P)` divides
`q(q-1)/2`, `q = p^k` — this is the bound used to rule out `C(t) ≤ N(P)` for `C(t)` dihedral of
order `q ∓ 1`.

Intended proof.  `P` is contained in a Sylow `p`-subgroup `U` of `G := PSL(2,GF(p,k))` (Sylow's
theorem, `IsPGroup`); `P ≠ ⊥` forces `U` to be the unique Sylow `p`-subgroup containing `P`: if
`U ≠ U'` are Sylow `p`-subgroups then `U ⊓ U' = ⊥` — this is the TI property of the Sylow
`p`-subgroups, obtained from `PSL.ti_pslUnipotent` for `pslUnipotent` (which is a Sylow
`p`-subgroup of order `q = p^k`: `PSL.pslUnipotent_card` plus
`2 * |PSL(2,GF(p,k))| = p^k (p^{2k} - 1)`, cf. `PSL2.card_PSL2_galoisField`) together with Sylow
conjugacy.  Hence for `g ∈ N(P)`, both `U` and `g U g⁻¹` are Sylow `p`-subgroups containing
`P ≠ ⊥`, so `U = g U g⁻¹` and `N(P) ≤ N(U)`.  Finally `|N(U)| = q(q-1)/2`: `U` is conjugate to
`pslUnipotent`, and `PSL.normalizer_pslUnipotent_card` computes `2 * |N(pslUnipotent)| =
q(q-1)`.  All Sylow `p`-subgroups of `G` have the same order (`q`, as `p ∤ |G|/q`), so
`|N(P)| ∣ |N(U)| = q(q-1)/2`. -/
theorem card_normalizer_pSubgroup_dvd {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hk : 5 ≤ p ^ k)
    (P : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)))
    (hP : IsPGroup p P) (hne : P ≠ ⊥) :
    Nat.card (Subgroup.normalizer (P : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)))) ∣
      p ^ k * (p ^ k - 1) / 2 := by
  -- `Q = pslUnipotent` is a Sylow `p`-subgroup of `G = PSL(2, p^k)`.
  obtain ⟨Q, hQ⟩ := pslUnipotent_sylow (p := p) (k := k) hp hk
  -- `P` lies in a Sylow `p`-subgroup `S`, which is conjugate to `Q`.
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_map_conj_eq_of_sylow Q S
  have hQg : (S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) =
      (Work.L2F.pslUnipotent (GaloisField p k)).map (MulAut.conj g).toMonoidHom := by
    rw [hg, hQ]
  have hPg : P ≤ (Work.L2F.pslUnipotent (GaloisField p k)).map
      (MulAut.conj g).toMonoidHom := by
    rw [← hQg]; exact hPS
  -- Conjugating back, `P' := P^{g⁻¹}` is a nontrivial subgroup of `pslUnipotent`.
  set P' : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
    P.map (MulAut.conj g⁻¹).toMonoidHom with hP'def
  have hP'le : P' ≤ Work.L2F.pslUnipotent (GaloisField p k) := by
    intro y hy
    rw [hP'def, Subgroup.mem_map] at hy
    obtain ⟨x, hxP, hxy⟩ := hy
    rw [← hxy]
    obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp (hPg hxP)
    rw [← hqx]
    have hkey : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom q) = q := by
      show (MulAut.conj g⁻¹) ((MulAut.conj g) q) = q
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [hkey]
    exact hq
  have hP'ne : P' ≠ ⊥ := by
    intro hbot
    rw [hP'def, Subgroup.map_eq_bot_iff] at hbot
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hxker : (MulAut.conj g⁻¹).toMonoidHom x = 1 := hbot hx
    rw [Subgroup.mem_bot]
    exact (MulAut.conj g⁻¹).injective (by simpa using hxker)
  -- Odd characteristic: `(2 : GF(p,k)) ≠ 0`, needed for the TI property of `pslUnipotent`.
  have h2 : (2 : GaloisField p k) ≠ 0 := by
    intro h
    have hpdiv : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p k) p 2).mp h
    have hle2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpdiv
    have hge2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hp2 : p = 2 := le_antisymm hle2 hge2
    rw [hp2] at hp
    obtain ⟨m, hm⟩ := hp
    omega
  -- TI gives `N(P') ≤ N(pslUnipotent)`.
  have hNP' : Subgroup.normalizer (P' : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) ≤
      Subgroup.normalizer ((Work.L2F.pslUnipotent (GaloisField p k)) :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) :=
    normalizer_le_normalizer_of_ti _ _ hP'le hP'ne
      (fun x hx => ti_pslUnipotent (GaloisField p k) h2 x hx)
  -- Conjugation preserves the order of the normalizer, so `|N(P)| = |N(P')|`.
  have hcardP : Nat.card (Subgroup.normalizer (P : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)))) =
      Nat.card (Subgroup.normalizer (P' : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)))) := by
    rw [hP'def]
    exact (natCard_normalizer_conj P g⁻¹).symm
  rw [hcardP, ← natCard_normalizer_pslUnipotent (p := p) (k := k) hp hk]
  exact Subgroup.card_dvd_of_le hNP'

end Work.L2F.PSL
