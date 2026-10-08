import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Counting.EConjPrime

namespace Work.CORE4.Counting

/-- Conjugation commutes with the image of a monoid homomorphism: the image of the conjugate of
`Y` by `g` is the conjugate of the image of `Y` by the image of `g`. -/
private lemma map_conj_conj {G N : Type*} [Group G] [Group N] (f : G →* N) (Y : Subgroup G)
    (g : G) :
    (Y.map (MulAut.conj g).toMonoidHom).map f =
      (Y.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

/-- For `g ∈ L ≤ G`, conjugating inside `L` by `g` and then passing to `G` is conjugating
inside `G` by the image of `g`. -/
private lemma subtype_comp_conj {G : Type*} [Group G] (L : Subgroup G) (g : L) :
    L.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (L.subtype g)).toMonoidHom.comp L.subtype := by
  ext x
  simp [MulAut.conj_apply]

/-- Arithmetic input: if `p` divides the even half `k` of `pF ^ kF ∓ 1`, then `p ≠ pF`.
(Indeed `pF ∣ k` would force `pF ∣ pF ^ kF` and `pF ∣ 2 * k = pF ^ kF ∓ 1`.) -/
private lemma ne_pF_of_dvd_half {pF kF k p : ℕ} (hpF : pF.Prime) (hq5 : 5 ≤ pF ^ kF)
    (hdiv : p ∣ k) (hdisj : 2 * k = pF ^ kF + 1 ∨ 2 * k = pF ^ kF - 1) : p ≠ pF := by
  intro hpeq
  -- `kF ≠ 0`, since `pF ^ kF ≥ 5 > 1`.
  have hkF : 1 ≤ kF := by
    by_contra hlt
    have h0 : kF = 0 := Nat.eq_zero_of_not_pos hlt
    rw [h0] at hq5
    norm_num at hq5
  have hd1 : pF ∣ pF ^ kF := ⟨pF ^ (kF - 1), by rw [← pow_succ', Nat.sub_add_cancel hkF]⟩
  have hdiv' : pF ∣ k := hpeq ▸ hdiv
  have hd2 : pF ∣ 2 * k := Dvd.dvd.mul_left hdiv' 2
  have hX1 : 1 ≤ pF ^ kF := le_trans (by norm_num) hq5
  have hone : pF ∣ 1 := by
    rcases hdisj with h | h
    · have hd2' : pF ∣ pF ^ kF + 1 := by rw [← h]; exact hd2
      have hsub : pF ∣ (pF ^ kF + 1) - pF ^ kF := Nat.dvd_sub hd2' hd1
      rwa [Nat.add_sub_cancel_left] at hsub
    · have hX : pF ^ kF = 2 * k + 1 := by
        rw [h]
        exact (Nat.sub_add_cancel hX1).symm
      have hsub : pF ∣ pF ^ kF - 2 * k := Nat.dvd_sub hd1 hd2
      rw [hX] at hsub
      rwa [Nat.add_sub_cancel_left] at hsub
  have h1 : pF = 1 := Nat.dvd_one.mp hone
  have h2 : 2 ≤ pF := hpF.two_le
  omega

/-- **Transitivity of `layerIn D.M` on its order-`p` subgroups.**  Transport of `Work.CORE4.Counting.EConjPrime` along the §4 (9) isomorphism `φ : E(M) ≃* PSL(2, GF pF kF)`: if `p` is an odd prime dividing the even half `k` of `pF^kF ∓ 1`, then any two order-`p` subgroups `Y, Y' ≤ layerIn h.D.M` are conjugate by an element of `layerIn h.D.M`.

Proof route: `Y.map φ.toMonoidHom` and `Y'.map φ.toMonoidHom` are order-`p` subgroups of `PSL(2, GF pF kF)`, so `EConjPrime` gives `e : PSL(2, GF pF kF)` with `Y'.map φ.toMonoidHom = (Y.map φ.toMonoidHom).map (MulAut.conj e).toMonoidHom`.  Transferring the conjugation identity across `φ` (conjugation commutes with multiplicative equivalences: `(Y.map φ).map (conj e) = (conjSub (φ.symm e) Y).map φ`) and using injectivity of `Subgroup.map φ.toMonoidHom` gives `Y' = conjSub (φ.symm e) Y`, with `φ.symm e ∈ layerIn h.D.M`.  (`p ≠ pF` is automatic since `p ∣ k` and `2k = pF^kF ∓ 1`.) -/
theorem EConjLayerIn (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
      (pF kF k k' : ℕ) (_ : Fact pF.Prime)
      (φ : (Work.GW2.layerIn h.D.M) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF))
      (p : ℕ),
      Odd pF → 5 ≤ pF ^ kF → Even k → Odd k' →
      ((2 * k = pF ^ kF + 1 ∧ 2 * k' = pF ^ kF - 1) ∨
       (2 * k = pF ^ kF - 1 ∧ 2 * k' = pF ^ kF + 1)) →
      p.Prime → Odd p → p ∣ k →
      ∀ Y Y' : Subgroup G, Y ≤ Work.GW2.layerIn h.D.M → Y' ≤ Work.GW2.layerIn h.D.M →
        Nat.card ↥Y = p → Nat.card ↥Y' = p →
        ∃ e ∈ Work.GW2.layerIn h.D.M, Y' = Work.GW2.conjSub e Y := by
  intro G _ _ B h pF kF k k' hpFfact φ p hodd hq5 hk hk' hdisj hp hoddp hpdivk
    Y Y' hY hY' hcardY hcardY'
  haveI : Fact pF.Prime := hpFfact
  -- `p ≠ pF` and `p ≠ 2`.
  have hpF_ne_p : p ≠ pF :=
    ne_pF_of_dvd_half hpFfact.out hq5 hpdivk (hdisj.imp (fun hh => hh.1) (fun hh => hh.1))
  have hp2 : p ≠ 2 := by rintro rfl; exact absurd hoddp (by decide)
  -- Work inside `L = E(M) = layerIn D.M`.
  let L : Subgroup G := Work.GW2.layerIn h.D.M
  have hYL : Y ≤ L := hY
  have hY'L : Y' ≤ L := hY'
  have hcardA : Nat.card ↥(Y.subgroupOf L) = p := by
    rw [← Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hYL, hcardY]
  have hcardA' : Nat.card ↥(Y'.subgroupOf L) = p := by
    rw [← Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hY'L, hcardY']
  -- Conjugacy in `PSL(2, GF pF kF)`, from the §4 (11) count.
  have key := EConjPrime I.l2primeCount I.l2torusNorm pF kF k k' p
    hodd hq5 hk hk' hdisj hp hp2 hpF_ne_p hpdivk
  obtain ⟨e, he⟩ := key ((Y.subgroupOf L).map φ.toMonoidHom)
    ((Y'.subgroupOf L).map φ.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective φ.injective, hcardA])
    (by rw [Subgroup.card_map_of_injective φ.injective, hcardA'])
  -- Transport back along `φ`: `φ (φ.symm e) = e`, so conjugating by `φ.symm e` inside `L`
  -- is conjugating by `e` after applying `φ`.
  let g : L := φ.symm e
  have hφg : φ.toMonoidHom g = e := φ.apply_symm_apply e
  have h1 : (Y'.subgroupOf L).map φ.toMonoidHom =
      ((Y.subgroupOf L).map (MulAut.conj g).toMonoidHom).map φ.toMonoidHom := by
    rw [map_conj_conj φ.toMonoidHom (Y.subgroupOf L) g, hφg]
    exact he
  have hAeq : Y'.subgroupOf L = (Y.subgroupOf L).map (MulAut.conj g).toMonoidHom :=
    Subgroup.map_injective φ.injective h1
  -- Push the equality back into `G`.
  have h2 : (Y'.subgroupOf L).map L.subtype =
      ((Y.subgroupOf L).map (MulAut.conj g).toMonoidHom).map L.subtype := by rw [hAeq]
  rw [Subgroup.map_map, subtype_comp_conj L g, ← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le hY'L, Subgroup.map_subgroupOf_eq_of_le hYL] at h2
  exact ⟨L.subtype g, g.2, h2⟩

end Work.CORE4.Counting
