import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.ZASS.Basic

open scoped MatrixGroups

namespace Work.ZASS

open Work.GW2 (ZassHyps2)
open Work.Zassenhaus (borel pairStab fixesOnly fixesSome)

/-- **Z6.2 refinement** (HB III XI 1.7c, last sentence; blueprint design pass 2 §13, Z6.4).
When `d = (q-1)/2` is even, there is an involution interchanging `a` and `b` with exactly two
fixed points.  Route: `H = G_{ab}` has order `d`, which is even, so `H` contains an involution
`t` (Cauchy's theorem); `t ≠ 1` fixes `a` and `b`, hence its fixed-point set is exactly
`{a,b}`.  Pick `c ∉ {a,b}` and let `e := t • c ≠ c`; by 2-pretransitivity choose `g` with
`g • c = a`, `g • e = b`.  Then `g * t * g⁻¹` is an involution interchanging `a` and `b`,
whose fixed-point set is `g '' {a,b}`, of size `2`. -/
theorem exists_swap_two_fixed {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
    {q : ℕ} (h : ZassHyps2 G X q) (hodd : Odd q) (hd : Even ((q - 1) / 2))
    {a b : X} (hab : a ≠ b) :
    ∃ s : G, orderOf s = 2 ∧ s • a = b ∧ s • b = a ∧ {x : X | s • x = x}.ncard = 2 := by
  have hpre := h.2.2.1
  have hfix2 := h.2.2.2.1
  have hcardH : Nat.card ↥(pairStab G a b) = (q - 1) / 2 := card_pairStab h hab
  -- a third point exists
  have hc3 : ∃ c : X, c ≠ a ∧ c ≠ b := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Set.univ : Set X) ⊆ ({a, b} : Set X) := by
      intro x _
      by_cases hxa : x = a
      · rw [hxa]; simp
      · rw [hcon x hxa]; simp
    have hle := Set.ncard_le_ncard hsub
    rw [Set.ncard_univ, Set.ncard_pair hab, h.2.1] at hle
    have hst : 2 * Nat.card ↥(MulAction.stabilizer G a ⊓ MulAction.stabilizer G b) = q - 1 :=
      h.2.2.2.2 a b hab
    have hpos : 1 ≤ Nat.card ↥(MulAction.stabilizer G a ⊓ MulAction.stabilizer G b) :=
      Nat.card_pos
    omega
  -- Cauchy in the two-point stabilizer `G_{ab}`, of even order `d`
  have hdvd : 2 ∣ Nat.card ↥(pairStab G a b) := by
    rw [hcardH]
    exact even_iff_two_dvd.mp hd
  obtain ⟨t, htord⟩ := exists_prime_orderOf_dvd_card' 2 (G := ↥(pairStab G a b)) hdvd
  have htord' : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact htord
  have ht1 : (t : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at htord'
    exact absurd htord' (by norm_num)
  obtain ⟨htb, hta⟩ := Work.Zassenhaus.mem_pairStab_iff.mp t.2
  -- the fixed-point set of `t` is exactly `{a, b}`
  have hfix_t : {x : X | (t : G) • x = x} = {a, b} := by
    refine (Set.eq_of_subset_of_ncard_le ?_ ?_).symm
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hta
      · exact htb
    · rw [Set.ncard_pair hab]
      exact hfix2 (t : G) ht1
  obtain ⟨c, hca, hcb⟩ := hc3
  have htc : (t : G) • c ≠ c := by
    intro hc
    have hmem : c ∈ ({a, b} : Set X) := by rw [← hfix_t]; exact hc
    rcases hmem with h | h
    · exact hca h
    · exact hcb h
  -- 2-transitivity moves `(c, t • c)` to `(a, b)`
  obtain ⟨g, hgc, hgd⟩ :=
    (MulAction.is_two_pretransitive_iff.mp hpre) (Ne.symm htc) hab
  have hgcinv : g⁻¹ • b = (t : G) • c := by
    have h := congrArg (fun y : X => g⁻¹ • y) hgd
    simpa using h.symm
  have hgcc : g⁻¹ • a = c := by
    have h := congrArg (fun y : X => g⁻¹ • y) hgc
    simpa using h.symm
  have htt : (t : G) • ((t : G) • c) = c := by
    have h2 : (t : G) * (t : G) = 1 := by
      have h3 := pow_orderOf_eq_one (t : G)
      rw [htord', pow_two] at h3
      exact h3
    rw [← mul_smul, h2, one_smul]
  refine ⟨g * (t : G) * g⁻¹, ?_, ?_, ?_, ?_⟩
  · have h1 : (MulAut.conj g) (t : G) = g * (t : G) * g⁻¹ := by
      simp [MulAut.conj_apply]
    rw [← h1, (MulAut.conj g).orderOf_eq (t : G), htord']
  · calc (g * (t : G) * g⁻¹) • a = g • ((t : G) • (g⁻¹ • a)) := by simp only [mul_smul]
      _ = g • ((t : G) • c) := by rw [hgcc]
      _ = b := hgd
  · calc (g * (t : G) * g⁻¹) • b = g • ((t : G) • (g⁻¹ • b)) := by simp only [mul_smul]
      _ = g • ((t : G) • ((t : G) • c)) := by rw [hgcinv]
      _ = g • c := by rw [htt]
      _ = a := hgc
  · -- the fixed-point set is the image of `{a,b}` under `g •`
    have hfix_s : {x : X | (g * (t : G) * g⁻¹) • x = x} =
        (fun y : X => g • y) '' {x : X | (t : G) • x = x} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · intro hx
        refine ⟨g⁻¹ • x, ?_, by rw [smul_inv_smul]⟩
        have h1 : g⁻¹ • ((g * (t : G) * g⁻¹) • x) = g⁻¹ • x := by rw [hx]
        simpa [mul_smul, mul_assoc] using h1
      · rintro ⟨y, hy, rfl⟩
        show (g * (t : G) * g⁻¹) • (g • y) = g • y
        rw [mul_smul, mul_smul, inv_smul_smul, hy]
    rw [hfix_s, Set.ncard_image_of_injective _
        (fun x y hxy => by simpa using congrArg (fun z => g⁻¹ • z) hxy),
      hfix_t, Set.ncard_pair hab]

end Work.ZASS
