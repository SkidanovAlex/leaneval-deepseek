import Mathlib
import Submission.Work.ZASS.Defs

namespace Work.ZASS

/-- **Z4/Z5 counting, general form.** Let `H` act on a subgroup `W` by conjugation (so `H`
normalizes `W` elementwise), fixed-point-freely: no nonidentity element of `H` centralizes a
nonidentity element of `W`.  Then `|H|` divides `|W| - 1`.

Indeed `H` acts on the finite type `S = W \ {1}` of nonidentity elements, and the action is
free (all point stabilizers are trivial), so Burnside's lemma
(`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`) reads
`|S| = #{orbits} · |H|`. -/
theorem card_sub_one_dvd_of_conjFree {G : Type} [Group G] [Finite G] {H W : Subgroup G}
    (hfix : Work.ZASS.FixedPointFreeConj W H) (hWinv : Work.ZASS.IsConjInvariant H W) :
    Nat.card H ∣ Nat.card W - 1 := by
  classical
  -- The conjugation action of `H` on `W`.
  letI actW : MulAction H W :=
    { smul := fun h w => ⟨Work.ZASS.conjBy (h : G) (w : G), hWinv h h.2 w w.2⟩
      one_smul := fun x => Subtype.ext (by
        show Work.ZASS.conjBy (1 : G) (x : G) = (x : G); simp [Work.ZASS.conjBy])
      mul_smul := fun a b x => Subtype.ext (by
        show Work.ZASS.conjBy ((a : G) * (b : G)) (x : G) =
          Work.ZASS.conjBy (a : G) (Work.ZASS.conjBy (b : G) (x : G))
        simp only [Work.ZASS.conjBy, mul_inv_rev]; group) }
  -- The induced action on the nonidentity elements of `W`.
  let S := {w : W // w ≠ 1}
  letI actS : MulAction H S :=
    { smul := fun h s => ⟨h • s.1, by
        intro hx
        exact s.2 (by
          have h1 : s.1 = (h⁻¹ : H) • ((h : H) • s.1) := (inv_smul_smul (h : H) s.1).symm
          rw [hx] at h1
          rw [h1]
          apply Subtype.ext
          show Work.ZASS.conjBy ((h⁻¹ : H) : G) (1 : G) = (1 : G)
          simp [Work.ZASS.conjBy])⟩
      one_smul := fun s => Subtype.ext (by
        show ((1 : H) • s.1 : W) = s.1
        exact one_smul H s.1)
      mul_smul := fun a b s => Subtype.ext (by
        show ((a * b : H) • s.1 : W) = (a • (b • s.1) : W)
        exact mul_smul a b s.1) }
  haveI hH : Fintype H := Fintype.ofFinite H
  haveI hW : Fintype W := Fintype.ofFinite W
  haveI hS : Fintype S := Fintype.ofFinite S
  -- Freely acting: every nonidentity element of `H` has empty fixed-point set on `S`.
  have hf0 : ∀ b : H, b ≠ 1 → Fintype.card (MulAction.fixedBy S b) = 0 := by
    intro b hb
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun s => ?_⟩
    have hs : b • s.1 = s.1 := (MulAction.mem_fixedBy (α := S)).mp s.2
    have hh : Work.ZASS.conjBy (b : G) (s.1.1 : G) = (s.1.1 : G) :=
      Subtype.ext_iff.mp (Subtype.ext_iff.mp hs)
    have hb' : (b : G) ≠ 1 := fun hg => hb (Subtype.ext hg)
    have hfix' : (s.1.1 : G) = 1 := hfix (b : G) b.2 hb' (s.1.1 : G) s.1.1.2 hh
    exact s.1.2 (Subtype.ext hfix')
  -- Burnside: the sum of fixed-point counts is `|S|`, hence `|S| = #{orbits} * |H|`.
  have hsum : (∑ b : H, Fintype.card (MulAction.fixedBy S b)) = Fintype.card S := by
    rw [Finset.sum_eq_single_of_mem (1 : H) (Finset.mem_univ 1) (fun b _ hb => hf0 b hb)]
    exact Fintype.card_congr
      { toFun := fun x => x.1
        invFun := fun s => ⟨s, by rw [MulAction.mem_fixedBy]; exact one_smul H s⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun s => rfl }
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group H S
  have hmain : Fintype.card S =
      Fintype.card (Quotient (MulAction.orbitRel H S)) * Fintype.card H := by
    rw [← hsum, hburn]
  have hScard : Fintype.card S = Nat.card W - 1 := by
    show Fintype.card {w : W // w ≠ 1} = Nat.card W - 1
    rw [Fintype.card_subtype_compl (fun w : W => w = 1), Fintype.card_subtype_eq]
    congr 1
    exact (Nat.card_eq_fintype_card).symm
  refine ⟨Fintype.card (Quotient (MulAction.orbitRel H S)), ?_⟩
  rw [← hScard, hmain, Nat.card_eq_fintype_card, mul_comm]

/-- **Z4/Z5 arithmetic.** Let `h = (p^k-1)/2`, so `p^k = 2h + 1`.  If `d ∣ p^k`, `d ≥ 2` and
`h ∣ d - 1`, then `d = p^k`: writing `d = hc + 1` we get `hc + 1 ∣ 2h + 1` and `c ≤ 2`; `c = 1`
would force `h + 1 ∣ 1` hence `h = 0`, and `c = 2` gives `d = 2h + 1 = p^k`. -/
theorem eq_pow_of_dvd_of_dvd {p k d h : ℕ} (hpk2 : 2 ≤ p ^ k)
    (h2 : 2 * h = p ^ k - 1) (hdvd : d ∣ p ^ k) (hbig : 2 ≤ d) (hcnt : h ∣ d - 1) :
    d = p ^ k := by
  have hpkeq : p ^ k = 2 * h + 1 := by omega
  have hpos : 0 < h := by omega
  obtain ⟨c, hc⟩ := hcnt
  have hd : d = h * c + 1 := by omega
  have hdvd' : h * c + 1 ∣ 2 * h + 1 := by rw [← hpkeq, ← hd]; exact hdvd
  have hdle : d ≤ p ^ k := Nat.le_of_dvd (by omega) hdvd
  have hcle : c ≤ 2 := by
    have hlc : h * c ≤ h * 2 := by
      calc h * c = d - 1 := hc.symm
        _ ≤ p ^ k - 1 := Nat.sub_le_sub_right hdle 1
        _ = 2 * h := h2.symm
        _ = h * 2 := by ring
    exact Nat.le_of_mul_le_mul_left hlc hpos
  have hcge : 1 ≤ c := by
    by_contra hcon
    have : c = 0 := by omega
    rw [this, mul_zero] at hc
    omega
  have hcases : c = 1 ∨ c = 2 := by omega
  rcases hcases with hc1 | hc2
  · subst hc1
    exfalso
    have hdiv : (h + 1) ∣ 2 * h + 1 := by simpa using hdvd'
    have hd1 : d = h + 1 := by rw [hd]; ring
    have hone : (h + 1) ∣ 1 := by
      have h2' := Nat.dvd_sub (dvd_mul_right (h + 1) 2) hdiv
      convert h2' using 1
      omega
    have := Nat.le_of_dvd (by norm_num : 0 < 1) hone
    omega
  · subst hc2
    rw [hd, hpkeq]
    ring

/-- **Z4/Z5 (blueprint §ZASS).** Master lemma: if `H ≤ N(U)` acts fixed-point-freely on a
`p`-group `U` of order `p^k` by conjugation, `|H| = (p^k-1)/2`, and `W ≤ U` is a nontrivial
`H`-invariant subgroup, then `W = U`.  Proof: `|W| = p^m ≤ p^k` and
`ZASS/dvd_card_sub_one_of_isConjInvariant` give `(p^k-1)/2 ∣ p^m - 1`, so
`p^m ∈ {1, (p^k+1)/2, p^k}`; the first is excluded by `W ≠ ⊥` and the second by
`ZASS/two_mul_pow_ne_pow_add_one`, hence `|W| = p^k = |U|`.
Instantiated with `W = Z(U)` this gives that `U` is abelian (Z4), and with arbitrary `W` it is
the irreducibility of `U` as an `H`-module (Z5). -/
theorem eq_top_of_isConjInvariant {G : Type} [Group G] [Finite G] {p k : ℕ} [Fact p.Prime]
    (hp : Odd p) (hk : 1 ≤ k) {U H W : Subgroup G} (hWU : W ≤ U) (hUP : IsPGroup p U)
    (hcardU : Nat.card U = p ^ k) (hHle : H ≤ Subgroup.normalizer (U : Set G))
    (hfix : Work.ZASS.FixedPointFreeConj U H) (hcardH : Nat.card H = (p ^ k - 1) / 2)
    (hWne : W ≠ ⊥) (hWinv : Work.ZASS.IsConjInvariant H W) : W = U := by
  have hpprime : p.Prime := Fact.out
  have hpk2 : 2 ≤ p ^ k := by
    have h1 : 2 ≤ p := hpprime.two_le
    have h2 : p ≤ p ^ k := Nat.le_self_pow (by omega) p
    exact le_trans h1 h2
  -- `H` acts fixed-point-freely on `W ≤ U` as well.
  have hfixW : Work.ZASS.FixedPointFreeConj W H :=
    fun h hh hne w hw hcw => hfix h hh hne w (hWU hw) hcw
  have hcnt0 : Nat.card H ∣ Nat.card W - 1 := card_sub_one_dvd_of_conjFree hfixW hWinv
  have hcnt : (p ^ k - 1) / 2 ∣ Nat.card W - 1 := by rw [← hcardH]; exact hcnt0
  have hdvd : Nat.card W ∣ p ^ k := by rw [← hcardU]; exact Subgroup.card_dvd_of_le hWU
  have hbig : 2 ≤ Nat.card W := by
    haveI : Fintype W := Fintype.ofFinite W
    rw [Nat.card_eq_fintype_card]
    obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWne
    have : 1 < Fintype.card W := Fintype.one_lt_card_iff.mpr ⟨w, 1, hw⟩
    omega
  have h2 : 2 * ((p ^ k - 1) / 2) = p ^ k - 1 := by
    have hodd : Odd (p ^ k) := hp.pow
    obtain ⟨m, hm⟩ := hodd
    have hdvd2 : 2 ∣ p ^ k - 1 := ⟨m, by omega⟩
    rw [mul_comm]
    exact Nat.div_mul_cancel hdvd2
  have hcardW : Nat.card W = p ^ k := eq_pow_of_dvd_of_dvd hpk2 h2 hdvd hbig hcnt
  exact Subgroup.eq_of_le_of_card_ge hWU (by rw [hcardU, hcardW])

end Work.ZASS
