import Mathlib
import Submission.Work.BSW.Cases.K4.mem_of_orderOf_eq_three_or_nine
import Submission.Work.BSW.Cases.K4.inverts_of_orderOf_eq_two

namespace Work.BSW.Cases.K4

/-- An element of a subgroup has order dividing the order of that subgroup. -/
theorem orderOf_dvd_card_of_mem_aux {G : Type} [Group G] {H : Subgroup G} {x : G}
    (hx : x ∈ H) : orderOf x ∣ Nat.card ↥H := by
  have h1 := orderOf_dvd_natCard (⟨x, hx⟩ : ↥H)
  have h2 : orderOf (⟨x, hx⟩ : ↥H) = orderOf x :=
    (Subgroup.orderOf_coe (⟨x, hx⟩ : ↥H)).symm
  rwa [h2] at h1

/-- Let `N` be a group of order `36` with a normal Sylow `3`-subgroup `Q` of order `9` which is
self-centralizing in `G` (`C_G(Q) = Q`), and suppose `G` has no element of order `6` or `18`.  Then
`N` contains an element of order `4`.

Sketch (contradiction): assume `N` has no element of order `4`, and let `z ∈ N \ Q`.  Since `Q` is
the unique Sylow `3`-subgroup of `N`, an element of `N` of order `3` or `9` lies in `Q` (its cyclic
subgroup has order `3` or `9` and is a `3`-subgroup, hence lies in a Sylow `3`-subgroup, i.e. in
`Q`); orders `6` and `18` are excluded, and orders `12` and `36` have a cube or ninth power of
order `4`.  As `orderOf z ∣ 36`, this forces every `z ∈ N \ Q` to be an involution.  Then for
`z ∈ N \ Q` and `q ∈ Q` also `z * q ∈ N \ Q`, so `(z*q)² = 1`, i.e. `z * q * z⁻¹ = q⁻¹`: every
element of `N \ Q` inverts `Q`.  But the conjugation map `φ : ↥N →* MulAut ↥Q` (well defined using
`hQnorm`) has kernel `C_G(Q) ∩ N = Q` (using `hC` and `hQN`), so its image has order `36/9 = 4`,
whereas `φ(q) = 1` for `q ∈ Q` and `φ(z)` is inversion (an involution) for all `z ∈ N \ Q`; indeed
`φ(q * z) = φ(q) * φ(z)` forces `φ(q) = 1` because `q * z ∈ N \ Q`, so the image is contained in
`{1, inversion}` of order at most `2`, a contradiction.

The final count is carried out directly instead of through the conjugation map: fixing
`z₀ ∈ N \ Q`, the map `z ↦ z₀⁻¹ * z` sends `N \ Q` into `C_G(Q) ∩ N = Q` (both `z₀` and `z` invert
`Q`, hence so does `z₀⁻¹ * z`), with inverse `q ↦ z₀ * q`, which lands back in `N \ Q`.  Hence
`N \ Q ≃ Q`, so `|N| = |Q| + |Q| = 18`, contradicting `|N| = 36`. -/
theorem exists_orderOf_eq_four_of_card_eq_thirtysix {G : Type} [Group G] [Finite G]
    (N Q : Subgroup G) (hN : Nat.card ↥N = 36) (hQ : Nat.card ↥Q = 9) (hQN : Q ≤ N)
    (hQnorm : (Q.subgroupOf N).Normal) (hC : Subgroup.centralizer (Q : Set G) = Q)
    (h6 : ∀ x : G, orderOf x ≠ 6) (h18 : ∀ x : G, orderOf x ≠ 18) :
    ∃ d ∈ N, orderOf d = 4 := by
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ d, d ∈ N → orderOf d ≠ 4`
  -- Step 1: every element of `N \ Q` is an involution.
  have h2 : ∀ z ∈ N, z ∉ Q → orderOf z = 2 := by
    intro z hzN hzQ
    have hdvd : orderOf z ∣ 36 := by
      have h' := orderOf_dvd_card_of_mem_aux (H := N) hzN
      rwa [hN] at h'
    have hmem : orderOf z ∈ Nat.divisors 36 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hd36 : Nat.divisors 36 = {1, 2, 3, 4, 6, 9, 12, 18, 36} := by decide
    rw [hd36] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h | h | h | h
    · exact absurd (by rw [orderOf_eq_one_iff.mp h]; exact Q.one_mem) hzQ
    · exact h
    · exact absurd (mem_of_orderOf_eq_three_or_nine N Q hQN hN hQ hQnorm hzN (Or.inl h)) hzQ
    · exact absurd h (hcon z hzN)
    · exact absurd h (h6 z)
    · exact absurd (mem_of_orderOf_eq_three_or_nine N Q hQN hN hQ hQnorm hzN (Or.inr h)) hzQ
    · have hz3 : orderOf (z ^ 3) = 4 := by rw [orderOf_pow, h]; norm_num
      exact absurd hz3 (hcon (z ^ 3) (N.pow_mem hzN 3))
    · exact absurd h (h18 z)
    · have hz9 : orderOf (z ^ 9) = 4 := by rw [orderOf_pow, h]; norm_num
      exact absurd hz9 (hcon (z ^ 9) (N.pow_mem hzN 9))
  -- Step 2: `N` contains an element outside `Q`.
  have hproper : ∃ z0 : G, z0 ∈ N ∧ z0 ∉ Q := by
    by_contra hc
    push_neg at hc
    let hmap : ↥N → ↥Q := fun z => ⟨(z : G), hc (z : G) z.2⟩
    have hinj : Function.Injective hmap := by
      intro a b hab
      exact Subtype.ext (congrArg (fun x : ↥Q => (x : G)) hab)
    have hcard := Nat.card_le_card_of_injective hmap hinj
    rw [hN, hQ] at hcard
    omega
  obtain ⟨z0, hz0N, hz0Q⟩ := hproper
  -- Step 3: every element of `N` outside `Q` is sent into `Q` by `z ↦ z0⁻¹ * z`.
  have hkey : ∀ z : G, z ∈ N → z ∉ Q → z0⁻¹ * z ∈ Q := by
    intro z hzN hzQ
    have hmem : z0⁻¹ * z ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hz0inv : z0 * q * z0⁻¹ = q⁻¹ :=
        inverts_of_orderOf_eq_two N Q hQN hz0N hz0Q h2 q hq
      have hzinv : z * q * z⁻¹ = q⁻¹ :=
        inverts_of_orderOf_eq_two N Q hQN hzN hzQ h2 q hq
      have h1 : (z0⁻¹ * z) * q * (z0⁻¹ * z)⁻¹ = q := by
        calc (z0⁻¹ * z) * q * (z0⁻¹ * z)⁻¹
            = z0⁻¹ * (z * q * z⁻¹) * z0 := by group
          _ = z0⁻¹ * q⁻¹ * z0 := by rw [hzinv]
          _ = q := by
                have hh : z0⁻¹ * q⁻¹ * z0 = z0⁻¹ * (z0 * q * z0⁻¹) * z0 := by rw [hz0inv]
                rw [hh]
                group
      calc q * (z0⁻¹ * z) = ((z0⁻¹ * z) * q * (z0⁻¹ * z)⁻¹) * (z0⁻¹ * z) := by rw [h1]
        _ = (z0⁻¹ * z) * q := by group
    exact hC ▸ hmem
  -- Step 4: counting — `N \ Q` is in bijection with `Q`.
  classical
  let p : ↥N → Prop := fun z => ((z : G) ∈ Q)
  have hqa : Nat.card {z : ↥N // p z} = Nat.card ↥Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv
  have hqb : Nat.card {z : ↥N // ¬ p z} = Nat.card ↥Q := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun z => ⟨z0⁻¹ * (z.1 : G), hkey (z.1 : G) z.1.2 z.2⟩
        invFun := fun q => ⟨⟨z0 * (q : G), N.mul_mem hz0N (hQN q.2)⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro hmem
      apply hz0Q
      have h : z0 = (z0 * (q : G)) * (q : G)⁻¹ := by group
      rw [h]
      exact Q.mul_mem hmem (Q.inv_mem q.2)
    · intro z
      apply Subtype.ext
      apply Subtype.ext
      show z0 * (z0⁻¹ * (z.1 : G)) = (z.1 : G)
      group
    · intro q
      apply Subtype.ext
      show z0⁻¹ * (z0 * (q : G)) = (q : G)
      group
  have hcount : Nat.card ↥N = Nat.card ↥Q + Nat.card ↥Q := by
    have hsum : Nat.card ↥N = Nat.card {z : ↥N // p z} + Nat.card {z : ↥N // ¬ p z} := by
      rw [Nat.card_congr (Equiv.sumCompl p).symm, Nat.card_sum]
    rw [hsum, hqa, hqb]
  rw [hN, hQ] at hcount
  omega

end Work.BSW.Cases.K4
