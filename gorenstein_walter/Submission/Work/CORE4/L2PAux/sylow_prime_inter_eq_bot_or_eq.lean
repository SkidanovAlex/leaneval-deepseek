import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.PSL.pslUnipotent_sylow
import Submission.Work.L2F.PSL.ti_pslUnipotent
import Submission.Work.L2F.PSL.exists_map_conj_eq_of_sylow
import Submission.Work.CORE4.L2PAux.factorization_card_psl2

open scoped MatrixGroups

namespace Work.CORE4.L2PAux

/-- **Distinct Sylow `ρ`-subgroups of `PSL(2, GF(ρ,k))` meet trivially.**

Here `ρ` is an odd prime and `5 ≤ ρ ^ k`, so that `|PSL(2, GF(ρ,k))|` has `ρ`-part exactly `ρ ^ k`
(`factorization_card_psl2`).  Any subgroup of that order is therefore a Sylow `ρ`-subgroup, and two
Sylow `ρ`-subgroups of `PSL(2, GF(ρ,k))` either coincide or meet trivially: this is the TI property
of the unipotent subgroup `Work.L2F.pslUnipotent` (`Work.L2F.PSL.ti_pslUnipotent`), transported to
an arbitrary pair of Sylow subgroups by Sylow conjugacy
(`Work.L2F.PSL.exists_map_conj_eq_of_sylow`).

Proof:  the unipotent subgroup `Q` is a Sylow `ρ`-subgroup; `R` and `R'` are Sylow by their order,
so `R = Q ^ g` and `R' = Q ^ (g')` for suitable `g, g'`.  If `1 ≠ x ∈ R ⊓ R'`, then
`g⁻¹ x g` is a nontrivial element of `Q ⊓ Q ^ (g⁻¹ g')`; the TI property then forces
`g⁻¹ g' ∈ N_G(Q)`, whence `Q ^ (g') = Q ^ g` and `R = R'`. -/
theorem sylow_prime_inter_eq_bot_or_eq {ρ k : ℕ} [Fact ρ.Prime] (hρ : Odd ρ) (hk : 5 ≤ ρ ^ k)
    (R R' : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField ρ k)))
    (hR : Nat.card R = ρ ^ k) (hR' : Nat.card R' = ρ ^ k) (hne : R ⊓ R' ≠ ⊥) : R = R' := by
  classical
  haveI : Fintype (GaloisField ρ k) := Fintype.ofFinite _
  have h2 : (2 : GaloisField ρ k) ≠ 0 := Work.L2F.PSL.two_ne_zero_galois hρ
  -- `Q` is a Sylow `ρ`-subgroup of `PSL(2, GF(ρ,k))`.
  obtain ⟨Q₀, hQ₀⟩ := Work.L2F.PSL.pslUnipotent_sylow (p := ρ) (k := k) hρ hk
  -- the `ρ`-part of the group order is `ρ ^ k`.
  have hfac : (Nat.card (Matrix.ProjectiveSpecialLinearGroup
        (Fin 2) (GaloisField ρ k))).factorization ρ = k :=
    (Work.CORE4.L2PAux.factorization_card_psl2 ρ k hρ hk).1
  -- hence the subgroups `R`, `R'` of order `ρ ^ k` are Sylow `ρ`-subgroups.
  have hRE : Nat.card R = ρ ^ (Nat.card (Matrix.ProjectiveSpecialLinearGroup
        (Fin 2) (GaloisField ρ k))).factorization ρ := by
    rw [hR, hfac]
  have hR'E : Nat.card R' = ρ ^ (Nat.card (Matrix.ProjectiveSpecialLinearGroup
        (Fin 2) (GaloisField ρ k))).factorization ρ := by
    rw [hR', hfac]
  -- Sylow conjugacy: `R = Q ^ g`, `R' = Q ^ (g')`.
  obtain ⟨g, hg⟩ := Work.L2F.PSL.exists_map_conj_eq_of_sylow Q₀ (Sylow.ofCard R hRE)
  obtain ⟨g', hg'⟩ := Work.L2F.PSL.exists_map_conj_eq_of_sylow Q₀ (Sylow.ofCard R' hR'E)
  have hRg : R = (Work.L2F.pslUnipotent (GaloisField ρ k)).map (MulAut.conj g).toMonoidHom := by
    rw [← hQ₀, ← hg, Sylow.coe_ofCard]
  have hR'g : R' = (Work.L2F.pslUnipotent (GaloisField ρ k)).map (MulAut.conj g').toMonoidHom := by
    rw [← hQ₀, ← hg', Sylow.coe_ofCard]
  -- pick a nontrivial element of `R ⊓ R'`.
  have hne' : ∃ y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField ρ k),
      y ∈ R ⊓ R' ∧ y ≠ 1 := by
    by_contra h
    push Not at h
    exact hne ((Subgroup.eq_bot_iff_forall (R ⊓ R')).mpr (fun y hy => h y hy))
  obtain ⟨x, hx, hx1⟩ := hne'
  obtain ⟨hxR, hxR'⟩ := Subgroup.mem_inf.mp hx
  rw [hRg] at hxR
  rw [hR'g] at hxR'
  obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hxR
  obtain ⟨q', hq', hq'x⟩ := Subgroup.mem_map.mp hxR'
  have hqx' : g * q * g⁻¹ = x := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hqx
  have hq'x' : g' * q' * g'⁻¹ = x := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hq'x
  -- `g⁻¹ x g` lies both in `Q` and in `Q ^ (g⁻¹ g')`.
  have hqe : g⁻¹ * x * g = q := by rw [← hqx']; group
  have hmemQ : g⁻¹ * x * g ∈ Work.L2F.pslUnipotent (GaloisField ρ k) := by
    rw [hqe]; exact hq
  have hmemQ' : g⁻¹ * x * g ∈
      (Work.L2F.pslUnipotent (GaloisField ρ k)).map (MulAut.conj (g⁻¹ * g')).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨q', hq', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hq'x']; group
  have hneTI : (Work.L2F.pslUnipotent (GaloisField ρ k)) ⊓
      (Work.L2F.pslUnipotent (GaloisField ρ k)).map (MulAut.conj (g⁻¹ * g')).toMonoidHom ≠ ⊥ := by
    intro h
    have hb : g⁻¹ * x * g ∈ (⊥ : Subgroup _) := by rw [← h]; exact ⟨hmemQ, hmemQ'⟩
    rw [Subgroup.mem_bot] at hb
    refine hx1 ?_
    rw [show x = g * (g⁻¹ * x * g) * g⁻¹ from by group, hb]; group
  -- the TI property forces `g⁻¹ g' ∈ N_G(Q)`.
  have hnorm : g⁻¹ * g' ∈ Subgroup.normalizer
      ((Work.L2F.pslUnipotent (GaloisField ρ k)) : Set
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField ρ k))) := by
    by_contra hh
    exact hneTI (Work.L2F.PSL.ti_pslUnipotent (GaloisField ρ k) h2 (g⁻¹ * g') hh)
  have hconj : (Work.L2F.pslUnipotent (GaloisField ρ k)).map
        (MulAut.conj (g⁻¹ * g')).toMonoidHom =
      Work.L2F.pslUnipotent (GaloisField ρ k) := by
    simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.mp hnorm)
  -- hence `Q ^ (g') = Q ^ g`, i.e. `R = R'`.
  have key : (Work.L2F.pslUnipotent (GaloisField ρ k)).map (MulAut.conj g').toMonoidHom =
      (Work.L2F.pslUnipotent (GaloisField ρ k)).map (MulAut.conj g).toMonoidHom := by
    have hmg : MulAut.conj g' = MulAut.conj g * MulAut.conj (g⁻¹ * g') := by
      rw [← map_mul, show g * (g⁻¹ * g') = g' from by group]
    rw [hmg]
    rw [show (MulAut.conj g * MulAut.conj (g⁻¹ * g')).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp (MulAut.conj (g⁻¹ * g')).toMonoidHom from rfl,
      ← Subgroup.map_map, hconj]
  rw [hRg, hR'g, key]

end Work.CORE4.L2PAux
