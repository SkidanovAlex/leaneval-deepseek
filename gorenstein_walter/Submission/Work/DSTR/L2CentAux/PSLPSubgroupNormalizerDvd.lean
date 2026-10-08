import Mathlib
import Submission.Work.PSL2.Basic
import Submission.Work.PSL2.Card
import Submission.Work.L2F.Defs
import Submission.Work.L2F.PSL.pslUnipotent_card
import Submission.Work.L2F.PSL.ti_pslUnipotent
import Submission.Work.L2F.PSL.normalizer_pslUnipotent_card
import Submission.Work.L2F.PSL.pslMap_eq_iff
import Submission.Work.DSTR.L2CentAux.not_dvd_index_pslUnipotent

namespace Work.DSTR.L2CentAux

open scoped MatrixGroups

/-- Conjugating a subgroup by a fixed element does not change the order of its normalizer. -/
private lemma card_normalizer_map_conj {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    Nat.card (Subgroup.normalizer (H.map (MulAut.conj g).toMonoidHom : Set G)) =
      Nat.card (Subgroup.normalizer (H : Set G)) := by
  rw [← Subgroup.map_equiv_normalizer_eq H (MulAut.conj g)]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

/-- **Sylow conjugacy, subgroup form**: any two Sylow `p`-subgroups of a finite group are
conjugate. -/
private lemma exists_map_conj_eq_of_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (Q S : Sylow p G) :
    ∃ g : G, (S : Subgroup G) = (Q : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
  exact ⟨g, by rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]; congr 1⟩

/-- **TI property implies `N(P) ≤ N(U)` for `⊥ ≠ P ≤ U`.** -/
private lemma normalizer_le_normalizer_of_ti {G : Type*} [Group G] (U P : Subgroup G)
    (hP : P ≤ U) (hne : P ≠ ⊥)
    (hti : ∀ x : G, x ∉ Subgroup.normalizer (U : Set G) →
      U ⊓ U.map (MulAut.conj x).toMonoidHom = ⊥) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (U : Set G) := by
  intro x hx
  by_contra hxU
  have hdisj := hti x hxU
  have hle : P ≤ U ⊓ U.map (MulAut.conj x).toMonoidHom := by
    refine le_inf hP ?_
    intro p hp
    have hconj : x⁻¹ * p * x ∈ P := (Subgroup.mem_normalizer_iff''.mp hx p).mp hp
    refine ⟨x⁻¹ * p * x, hP hconj, ?_⟩
    show (MulAut.conj x) (x⁻¹ * p * x) = p
    rw [MulAut.conj_apply]
    group
  have : P ≤ ⊥ := hle.trans (le_of_eq hdisj)
  exact hne (le_bot_iff.mp this)

/-- For an odd prime `p` the field `GF(p,k)` has characteristic `p ≠ 2`, so `2 ≠ 0`. -/
private lemma two_ne_zero_galois {p k : ℕ} [Fact p.Prime] (hp : Odd p) :
    (2 : GaloisField p k) ≠ 0 := by
  intro h
  have hpdiv : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p k) p 2).mp h
  have hle2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpdiv
  have hge2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp2 : p = 2 := le_antisymm hle2 hge2
  rw [hp2] at hp
  obtain ⟨m, hm⟩ := hp
  omega

/-- The normalizer of `pslUnipotent (GF(p,k))` in `PSL(2,GF(p,k))` has order `q(q-1)/2`. -/
private lemma card_normalizer_pslUnipotent {p k : ℕ} [Fact p.Prime] (hp : Odd p)
    (hk : 5 ≤ p ^ k) :
    Nat.card (Subgroup.normalizer (Work.L2F.pslUnipotent (GaloisField p k) :
        Set (PSL(2, GaloisField p k)))) = p ^ k * (p ^ k - 1) / 2 := by
  letI : Fintype (GaloisField p k) := Fintype.ofFinite _
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hF : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk0
  have h := Work.L2F.PSL.normalizer_pslUnipotent_card (GaloisField p k)
    (two_ne_zero_galois (k := k) hp)
  rw [hF] at h
  exact Nat.eq_div_of_mul_eq_left (by norm_num : (2 : ℕ) ≠ 0) (by rw [mul_comm]; exact h)

/-- **The normalizer of a nontrivial `p`-subgroup of `PSL(2,GF(p,k))` has order dividing
`q(q-1)/2`, `q = p^k`.** -/
theorem PSLPSubgroupNormalizerDvd {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hk : 5 ≤ p ^ k)
    (P : Subgroup (PSL(2, GaloisField p k))) (hP : IsPGroup p P) (hne : P ≠ ⊥) :
    Nat.card (Subgroup.normalizer (P : Set (PSL(2, GaloisField p k)))) ∣
      p ^ k * (p ^ k - 1) / 2 := by
  -- `U = pslUnipotent (GF(p,k))` is a Sylow `p`-subgroup of `G = PSL(2, GF(p,k))`.
  set U : Subgroup (PSL(2, GaloisField p k)) := Work.L2F.pslUnipotent (GaloisField p k)
    with hUdef
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have h2 := two_ne_zero_galois (k := k) hp
  have hUcard : Nat.card U = p ^ k := by
    rw [hUdef]
    haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
    rw [Work.L2F.PSL.pslUnipotent_card (GaloisField p k) h2]
    exact GaloisField.card p k hk0
  have hUp : IsPGroup p U := IsPGroup.of_card hUcard
  have hUidx : ¬ p ∣ U.index := by
    rw [hUdef]
    exact not_dvd_index_pslUnipotent hp hk
  let Q : Sylow p (PSL(2, GaloisField p k)) := hUp.toSylow hUidx
  have hQcoe : (Q : Subgroup (PSL(2, GaloisField p k))) = U := IsPGroup.toSylow_coe hUp hUidx
  -- `P` lies in a Sylow `p`-subgroup `S`, which is a conjugate of `U`.
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_map_conj_eq_of_sylow Q S
  have hQg : (S : Subgroup (PSL(2, GaloisField p k))) =
      U.map (MulAut.conj g).toMonoidHom := by
    rw [hg, hQcoe]
  have hPg : P ≤ U.map (MulAut.conj g).toMonoidHom := by
    rw [← hQg]; exact hPS
  -- Conjugating back, `P' := P^(g⁻¹)` is a nontrivial subgroup of `U`.
  set P' : Subgroup (PSL(2, GaloisField p k)) := P.map (MulAut.conj g⁻¹).toMonoidHom
    with hP'def
  have hP'le : P' ≤ U := by
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
  -- TI gives `N(P') ≤ N(U)`.
  have hNP' : Subgroup.normalizer (P' : Set (PSL(2, GaloisField p k))) ≤
      Subgroup.normalizer (U : Set (PSL(2, GaloisField p k))) :=
    normalizer_le_normalizer_of_ti U P' hP'le hP'ne
      (fun x hx => Work.L2F.PSL.ti_pslUnipotent (GaloisField p k) h2 x hx)
  -- Conjugation preserves the order of the normalizer, so `|N(P)| = |N(P')|`.
  have hcardP : Nat.card (Subgroup.normalizer (P : Set (PSL(2, GaloisField p k)))) =
      Nat.card (Subgroup.normalizer (P' : Set (PSL(2, GaloisField p k)))) := by
    rw [hP'def]
    exact (card_normalizer_map_conj P g⁻¹).symm
  rw [hcardP]
  have hdvd : Nat.card (Subgroup.normalizer (P' : Set (PSL(2, GaloisField p k)))) ∣
      Nat.card (Subgroup.normalizer (U : Set (PSL(2, GaloisField p k)))) :=
    Subgroup.card_dvd_of_le hNP'
  rw [hUdef] at hdvd
  rw [← card_normalizer_pslUnipotent (p := p) (k := k) hp hk]
  exact hdvd

end Work.DSTR.L2CentAux
