import Mathlib
import Submission.Work.ZASS.Leaf9
import Submission.Work.ZASS.Z5
import Submission.Work.ZASS.EvenSetup
import Submission.Work.ZASS.bruhat_decomposition
import Submission.Work.ZASS.conjBy_mem_pairStab
import Submission.Work.ZASS.zassInvolutionSwapProp
import Submission.Work.ZASS.zassCentralInv
import Submission.Work.ZASS.exists_swap_two_fixed

namespace Work.ZASS2

/-! # ZASS2 leaf: HB III.XI 1.11, the even-`d` case (`Work.GW2.ZassInvertEvenProp`)

Statement (fixed in `Submission/Work/ZASS/Leaf9.lean`): in the Zassenhaus setting with
`Even ((p^k-1)/2)` and `a ≠ b`, every `s` interchanging `a` and `b` inverts `G_{ab}`.

The route used here **bypasses** the functional equation HB 1.9–1.10 entirely; the essential
input is the involution `s₁` with exactly two fixed points supplied by
`Work.ZASS.exists_swap_two_fixed` (HB 1.8b).  Write

* `H = G_{a,b} = pairStab G a b`, of order `d = (p^k-1)/2`;
* `S = X ∖ {a,b}`, of cardinality `p^k - 1 = 2·|H|`.

1. `H` acts *freely* on `S` (a nonidentity element of `H` fixing a point of `S` fixes the
   three distinct points `a, b, x`, so is `1` by `Work.ZASS.eq_one_of_fixes_three`).
   Hence every `H`-orbit on `S` has exactly `|H|` elements, so there are exactly two of them.
2. `s₁` normalizes `H` (`conjBy_mem_pairStab`), so it permutes the `H`-orbits on `S`.  It has
   a fixed point `pt ∈ S` (its fixed-point set has cardinality `2` and contains neither `a`
   nor `b`), hence it fixes the orbit `O = H·pt`, and — there being only one further orbit —
   it fixes every `H`-orbit on `S` too.  Consequently `s₁` maps every `x ∈ S` into its own
   `H`-orbit, i.e. for every `x ∈ S` there is a **unique** `h ∈ H` with `h·(s₁·x) = x`.
3. Double count the pairs `(h,x) ∈ H × S` with `h·(s₁·x) = x`.  Grouping by `h` gives
   `Σ_h |Fix(h s₁) ∩ S|`, grouping by `x` gives `|S|` (each `x` has exactly one partner), so
   `Σ_h |Fix(h s₁) ∩ S| = 2·|H|`.  Since `h s₁ ≠ 1` swaps `a` and `b`, each term is at most
   `2` (`ZassHyps2`), so every term equals `2`: **every** `h s₁` has two fixed points in `S`.
4. For `h ∈ H`, a fixed point `x ∈ S` of `h s₁` is fixed by `(h s₁)²`, which also fixes `a`
   and `b`; the three points `a, b, x` are distinct, so `(h s₁)² = 1`, i.e. `s₁ h s₁ = h⁻¹`.
   Thus `Inverts s₁ H`, and `H` is abelian (`Work.GW2.isMulCommutative_of_inverts`).
5. A general `s` interchanging `a` and `b` satisfies `s = (s * s₁) * s₁` with `s * s₁ ∈ H`
   (`s * s₁` fixes `a` and `b`), and `H` is abelian, so `s h s⁻¹ = h⁻¹` for all `h ∈ H` as
   well. -/

set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open Work.GW2
open Work.Zassenhaus (borel pairStab)


theorem zassInvertEven : Work.GW2.ZassInvertEvenProp := by
  intro G X _ _ _ _ p k hpF hp hq h hd a b hab s hsa hsb
  classical
  haveI : Fintype X := Fintype.ofFinite X
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨s1, hs1ord, hs1a, hs1b, hs1fix⟩ :=
    Work.ZASS.exists_swap_two_fixed (q := p ^ k) h hp.pow hd hab
  have hs1sq : s1 * s1 = 1 := by
    simpa [pow_two, hs1ord] using pow_orderOf_eq_one s1
  have hs1inv : s1⁻¹ = s1 := inv_eq_of_mul_eq_one_right hs1sq
  let Hsub : Subgroup G := pairStab G a b
  have hcardH : Nat.card Hsub = (p ^ k - 1) / 2 := Work.ZASS.card_pairStab h hab
  have hHmem : ∀ (hh : Hsub), (hh : G) • a = a ∧ (hh : G) • b = b := by
    intro hh
    have hh' := Work.Zassenhaus.mem_pairStab_iff.mp hh.2
    exact ⟨hh'.2, hh'.1⟩
  let S : Set X := {x : X | x ≠ a ∧ x ≠ b}
  have hScard : S.ncard = p ^ k - 1 := by
    have hSc : S = ({a, b} : Set X)ᶜ := by
      ext x
      simp only [S, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or]
    rw [hSc, Set.ncard_compl, Set.ncard_pair hab, h.2.1]
    omega
  have hfree : ∀ (hh : Hsub) (x : X), x ∈ S → (hh : G) • x = x → hh = 1 := by
    intro hh x hxS hfix
    obtain ⟨hxa, hxb⟩ := hxS
    obtain ⟨ha', hb'⟩ := hHmem hh
    exact Subtype.ext (Work.ZASS.eq_one_of_fixes_three h hab hxa.symm hxb.symm ha' hb' hfix)
  have hSinv : ∀ (hh : Hsub) {x : X}, x ∈ S → (hh : G) • x ∈ S := by
    intro hh x hxS
    obtain ⟨hxa, hxb⟩ := hxS
    obtain ⟨ha', hb'⟩ := hHmem hh
    have h2a : (hh : G)⁻¹ • a = a := by
      have h := congrArg (fun y => (hh : G)⁻¹ • y) ha'
      simpa using h.symm
    have h2b : (hh : G)⁻¹ • b = b := by
      have h := congrArg (fun y => (hh : G)⁻¹ • y) hb'
      simpa using h.symm
    refine ⟨?_, ?_⟩
    · intro hcon
      exact hxa (by
        have h1 : x = (hh : G)⁻¹ • ((hh : G) • x) := (inv_smul_smul (hh : G) x).symm
        rw [hcon, h2a] at h1
        exact h1)
    · intro hcon
      exact hxb (by
        have h1 : x = (hh : G)⁻¹ • ((hh : G) • x) := (inv_smul_smul (hh : G) x).symm
        rw [hcon, h2b] at h1
        exact h1)
  have hSinv_s1 : ∀ {x : X}, x ∈ S → s1 • x ∈ S := by
    intro x hxS
    obtain ⟨hxa, hxb⟩ := hxS
    refine ⟨?_, ?_⟩
    · intro hcon
      exact hxb (by
        have h1 : x = s1 • (s1 • x) := by rw [← mul_smul, hs1sq, one_smul]
        rw [hcon, hs1a] at h1
        exact h1)
    · intro hcon
      exact hxa (by
        have h1 : x = s1 • (s1 • x) := by rw [← mul_smul, hs1sq, one_smul]
        rw [hcon, hs1b] at h1
        exact h1)
  obtain ⟨pt, hptS, hptfix⟩ : ∃ pt : X, pt ∈ S ∧ s1 • pt = pt := by
    have hsub : {x : X | s1 • x = x} ⊆ S := by
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      refine ⟨?_, ?_⟩
      · intro hcon; rw [hcon, hs1a] at hx; exact hab hx.symm
      · intro hcon; rw [hcon, hs1b] at hx; exact hab hx
    have hpos : 0 < ({x : X | s1 • x = x} : Set X).ncard := by rw [hs1fix]; norm_num
    obtain ⟨q, hq⟩ := (Set.ncard_pos (s := {x : X | s1 • x = x}) (Set.toFinite _)).mp hpos
    exact ⟨q, hsub hq, hq⟩
  -- orbit facts
  have horbcard : ∀ x : X, x ∈ S → (MulAction.orbit Hsub x).ncard = Nat.card Hsub := by
    intro x hxS
    have hcard' : Nat.card ↥(MulAction.orbit Hsub x) = Nat.card ↥Hsub := by
      refine Nat.card_congr (Equiv.ofBijective
        (fun hh : Hsub => (⟨(hh : G) • x, by
          rw [MulAction.mem_orbit_iff]; exact ⟨hh, rfl⟩⟩ : ↥(MulAction.orbit Hsub x)))
        ⟨?_, ?_⟩).symm
      · intro h1 h2 h12
        have h12' : (h1 : G) • x = (h2 : G) • x := Subtype.ext_iff.mp h12
        have hmem : ((h1 : G)⁻¹ * (h2 : G)) • x = x := by
          rw [mul_smul, ← h12', inv_smul_smul]
        have hbot : (⟨(h1 : G)⁻¹ * (h2 : G),
            Hsub.mul_mem (Hsub.inv_mem h1.2) h2.2⟩ : Hsub) = 1 := hfree _ x hxS hmem
        have hone : (h1 : G)⁻¹ * (h2 : G) = 1 := congrArg Subtype.val hbot
        exact Subtype.ext (inv_mul_eq_one.mp hone)
      · intro y
        have hy : (y : X) ∈ MulAction.orbit Hsub x := y.2
        rw [MulAction.mem_orbit_iff] at hy
        obtain ⟨hh, hhh⟩ := hy
        exact ⟨hh, Subtype.ext hhh⟩
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact hcard'
  let O : Set X := MulAction.orbit Hsub pt
  have hOeq : O = MulAction.orbit Hsub pt := rfl
  have hOS : O ⊆ S := by
    intro x hx
    rw [hOeq, MulAction.mem_orbit_iff] at hx
    obtain ⟨hh, rfl⟩ := hx
    exact hSinv hh hptS
  have hOcard : O.ncard = Nat.card Hsub := by
    rw [hOeq]; exact horbcard pt hptS
  have hO_Hinv : ∀ (hh : Hsub) {y : X}, y ∈ O → (hh : G) • y ∈ O := by
    intro hh y hy
    rw [hOeq, MulAction.mem_orbit_iff] at hy ⊢
    obtain ⟨hh', rfl⟩ := hy
    refine ⟨hh * hh', ?_⟩
    change ((hh : G) * (hh' : G)) • pt = (hh : G) • ((hh' : G) • pt)
    rw [mul_smul]
  have hO_Hinv' : ∀ (hh : Hsub) {y : X}, (hh : G) • y ∈ O → y ∈ O := by
    intro hh y hy
    have h1 : ((hh⁻¹ : Hsub) : G) • ((hh : G) • y) ∈ O := hO_Hinv (y := (hh : G) • y) hh⁻¹ hy
    have h2 : ((hh⁻¹ : Hsub) : G) • ((hh : G) • y) = y := by
      rw [Subgroup.coe_inv, inv_smul_smul]
    rwa [h2] at h1
  have hnorm : ∀ hh : Hsub, s1 * (hh : G) * s1⁻¹ ∈ Hsub :=
    fun hh => Work.ZASS.conjBy_mem_pairStab hs1a hs1b hh.2
  have hkey : ∀ (hh : Hsub),
      s1 • ((hh : G) • pt) = (s1 * (hh : G) * s1⁻¹) • pt := by
    intro hh
    have h3 : s1⁻¹ • pt = pt := by
      have h := congrArg (fun y => s1⁻¹ • y) hptfix
      simpa using h.symm
    rw [show (s1 * (hh : G) * s1⁻¹) • pt = s1 • ((hh : G) • (s1⁻¹ • pt)) by
      rw [mul_smul, mul_smul], h3]
  have hO_smul : ∀ {y : X}, y ∈ O → s1 • y ∈ O := by
    intro y hy
    rw [hOeq, MulAction.mem_orbit_iff] at hy ⊢
    obtain ⟨hh, rfl⟩ := hy
    exact ⟨⟨s1 * (hh : G) * s1⁻¹, hnorm hh⟩, (hkey hh).symm⟩
  have hO_smul_inv : ∀ {y : X}, s1 • y ∈ O → y ∈ O := by
    intro y hy
    have hy' : y = s1 • (s1 • y) := by rw [← mul_smul, hs1sq, one_smul]
    rw [hy']
    exact hO_smul hy
  have hScardm : S.ncard = 2 * Nat.card Hsub := by
    rw [hScard, hcardH]
    have heven : 2 ∣ (p ^ k - 1) := by
      obtain ⟨m, hm⟩ := hp.pow
      refine ⟨m, ?_⟩
      rw [hm]
      omega
    rw [Nat.mul_comm, Nat.div_mul_cancel heven]
  have hdiffcard : (S \ O).ncard = Nat.card Hsub := by
    have h1 : (S \ O).ncard = S.ncard - O.ncard := Set.ncard_sdiff hOS
    rw [h1, hScardm, hOcard]
    have h2 : 2 * Nat.card ↥Hsub = Nat.card ↥Hsub + Nat.card ↥Hsub := by ring
    rw [h2, Nat.add_sub_cancel]
  have hdiff_single : ∀ x : X, x ∈ S \ O → MulAction.orbit Hsub x = S \ O := by
    intro x hx
    obtain ⟨hxS, hxO⟩ := hx
    have hsub : MulAction.orbit Hsub x ⊆ S \ O := by
      intro y hy
      rw [MulAction.mem_orbit_iff] at hy
      obtain ⟨hh, rfl⟩ := hy
      refine ⟨hSinv hh hxS, ?_⟩
      intro hyO
      exact hxO (hO_Hinv' hh hyO)
    exact Set.eq_of_subset_of_ncard_le hsub (by rw [hdiffcard, horbcard x hxS])
  have horb_s1 : ∀ x : X, x ∈ S →
      MulAction.orbit Hsub (s1 • x) = MulAction.orbit Hsub x := by
    intro x hxS
    by_cases hxO : x ∈ O
    · have hs1xO : s1 • x ∈ O := hO_smul hxO
      have hxO' : x ∈ MulAction.orbit Hsub pt := hxO
      have hs1xO' : s1 • x ∈ MulAction.orbit Hsub pt := hs1xO
      rw [MulAction.orbit_eq_iff.mpr hs1xO', MulAction.orbit_eq_iff.mpr hxO']
    · have hxd : x ∈ S \ O := ⟨hxS, hxO⟩
      have hxd_orb : MulAction.orbit Hsub x = S \ O := hdiff_single x hxd
      have hs1x_diff : s1 • x ∈ S \ O :=
        ⟨hSinv_s1 hxS, fun hcon => hxO (hO_smul_inv hcon)⟩
      have hs1x_in : s1 • x ∈ MulAction.orbit Hsub x := by
        rw [hxd_orb]; exact hs1x_diff
      exact MulAction.orbit_eq_iff.mpr hs1x_in
  -- existence and uniqueness of the fixing element
  have hex : ∀ x : X, x ∈ S → ∃! hh : Hsub, ((hh : G) * s1) • x = x := by
    intro x hxS
    have hmem : x ∈ MulAction.orbit Hsub (s1 • x) := by
      rw [horb_s1 x hxS]
      exact MulAction.mem_orbit_self x
    rw [MulAction.mem_orbit_iff] at hmem
    obtain ⟨h0, hh0⟩ := hmem
    have hh0' : (h0 : G) • (s1 • x) = x := hh0
    refine ⟨h0, ?_, ?_⟩
    · show ((h0 : G) * s1) • x = x
      rw [mul_smul]
      exact hh0'
    · intro h1 hh1
      have hh1' : (h1 : G) • (s1 • x) = x := by
        rw [mul_smul] at hh1; exact hh1
      have hx1 : (h1 : G)⁻¹ • x = s1 • x := by
        calc (h1 : G)⁻¹ • x = (h1 : G)⁻¹ • ((h1 : G) • (s1 • x)) := by rw [hh1']
          _ = s1 • x := inv_smul_smul _ _
      have hx0 : (h0 : G)⁻¹ • x = s1 • x := by
        calc (h0 : G)⁻¹ • x = (h0 : G)⁻¹ • ((h0 : G) • (s1 • x)) := by rw [hh0']
          _ = s1 • x := inv_smul_smul _ _
      have hfixx : (h1 * h0⁻¹ : Hsub) • x = x := by
        change ((h1 : G) * ((h0 : G))⁻¹) • x = x
        rw [mul_smul, hx0]
        exact hh1'
      have hbot : (h1 * h0⁻¹ : Hsub) = 1 := hfree _ x hxS hfixx
      have : h1 = h0 := by
        have h := congrArg (fun z : Hsub => z * h0) hbot
        simpa using h
      exact this
  -- the counting
  let Sf : Finset X := Finset.univ.filter (fun x : X => x ∈ S)
  have hSf : Sf = S.toFinset := by
    ext x; simp [Sf, Set.mem_toFinset]
  have hSf_card : Sf.card = S.ncard := by
    rw [hSf, ← Set.ncard_eq_toFinset_card']
  let c : Hsub → ℕ := fun hh => (Sf.filter (fun x : X => ((hh : G) * s1) • x = x)).card
  have hle : ∀ hh : Hsub, c hh ≤ 2 := by
    intro hh
    have hne : (hh : G) * s1 ≠ 1 := by
      intro hcon
      have h1 : (hh : G) • b = a := by
        have h2 : ((hh : G) * s1) • a = a := by rw [hcon, one_smul]
        rw [mul_smul, hs1a] at h2
        exact h2
      rw [(hHmem hh).2] at h1
      exact hab h1.symm
    have hsub : Sf.filter (fun x : X => ((hh : G) * s1) • x = x)
        ⊆ Finset.univ.filter (fun x : X => ((hh : G) * s1) • x = x) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ x, hx.2⟩
    calc c hh = (Sf.filter (fun x : X => ((hh : G) * s1) • x = x)).card := rfl
      _ ≤ (Finset.univ.filter (fun x : X => ((hh : G) * s1) • x = x)).card :=
            Finset.card_le_card hsub
      _ ≤ 2 := by
          have hset : ({x : X | ((hh : G) * s1) • x = x} : Set X).ncard
              = (Finset.univ.filter (fun x : X => ((hh : G) * s1) • x = x)).card := by
            rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
          rw [← hset]
          exact h.2.2.2.1 ((hh : G) * s1) hne
  have hsum : ∑ hh : Hsub, c hh = S.ncard := by
    have h1 : ∑ hh : Hsub, c hh
        = ∑ hh : Hsub, ∑ x ∈ Sf, (if ((hh : G) * s1) • x = x then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro hh _
      dsimp only [c]
      rw [Finset.card_filter]
    rw [h1, Finset.sum_comm]
    have h2 : ∀ x ∈ Sf, (∑ hh : Hsub, (if ((hh : G) * s1) • x = x then 1 else 0)) = 1 := by
      intro x hx
      have hxS : x ∈ S := by
        rw [← Set.mem_toFinset, ← hSf]; exact hx
      obtain ⟨h0, hh0, huniq⟩ := hex x hxS
      rw [Finset.sum_eq_single h0]
      · simp [hh0]
      · intro b1 _ hb1
        by_cases hb0 : ((b1 : G) * s1) • x = x
        · exact absurd (huniq b1 hb0) hb1
        · simp [hb0]
      · intro h
        exact absurd (Finset.mem_univ h0) h
    have h3 : (∑ x ∈ Sf, (1 : ℕ)) = Sf.card * 1 :=
      Finset.sum_const_nat (s := Sf) (m := 1) (f := fun _ : X => 1) (fun _ _ => rfl)
    rw [Finset.sum_congr rfl h2, h3, Nat.mul_one, hSf_card]
  have hsum2 : ∑ hh : Hsub, c hh = ∑ _ : Hsub, 2 := by
    rw [hsum, hScardm]
    have h3 : (∑ _ : Hsub, (2 : ℕ)) = Finset.univ.card * 2 :=
      Finset.sum_const_nat (s := Finset.univ) (m := 2) (f := fun _ : Hsub => 2) (fun _ _ => rfl)
    rw [h3, Finset.card_univ, Nat.card_eq_fintype_card]
    ring
  have hall : ∀ hh : Hsub, c hh = 2 := by
    have hiff := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := c)
      (g := fun _ : Hsub => 2) (fun hh _ => hle hh)).mp hsum2
    exact fun hh => hiff hh (Finset.mem_univ hh)
  have hfixall : ∀ hh : Hsub, ∃ x ∈ S, ((hh : G) * s1) • x = x := by
    intro hh
    have hpos : 0 < c hh := by rw [hall hh]; norm_num
    dsimp only [c] at hpos
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hx
    exact ⟨x, by rw [← Set.mem_toFinset, ← hSf]; exact hx.1, hx.2⟩
  -- conclusion
  have hinv1 : ∀ hh : Hsub, ((hh : G) * s1) ^ 2 = 1 := by
    intro hh
    obtain ⟨x, hxS, hxfix⟩ := hfixall hh
    obtain ⟨hxa, hxb⟩ := hxS
    obtain ⟨ha', hb'⟩ := hHmem hh
    have hga : ((hh : G) * s1) • a = b := by rw [mul_smul, hs1a, hb']
    have hgb : ((hh : G) * s1) • b = a := by rw [mul_smul, hs1b, ha']
    have hpa : ((hh : G) * s1) ^ 2 • a = a := by rw [pow_two, mul_smul, hga, hgb]
    have hpb : ((hh : G) * s1) ^ 2 • b = b := by rw [pow_two, mul_smul, hgb, hga]
    have hpx : ((hh : G) * s1) ^ 2 • x = x := by rw [pow_two, mul_smul, hxfix, hxfix]
    exact Work.ZASS.eq_one_of_fixes_three h hab hxa.symm hxb.symm hpa hpb hpx
  have hinvH : Work.GW2.Inverts s1 Hsub := by
    intro hh hhm
    have := hinv1 ⟨hh, hhm⟩
    have key : s1 * hh * s1 = hh⁻¹ := by
      have h1 : hh * (s1 * hh * s1) = 1 := by
        calc hh * (s1 * hh * s1) = (hh * s1) * (hh * s1) := by group
          _ = (hh * s1) ^ 2 := by rw [pow_two]
          _ = 1 := this
      have h2 := congrArg (fun z => hh⁻¹ * z) h1
      simpa [mul_assoc] using h2
    rw [hs1inv]; exact key
  have hcomm : IsMulCommutative Hsub := Work.GW2.isMulCommutative_of_inverts hinvH
  have hs1H : s * s1 ∈ Hsub := by
    rw [Work.Zassenhaus.mem_pairStab_iff]
    refine ⟨?_, ?_⟩
    · show (s * s1) • b = b
      rw [mul_smul, hs1b, hsa]
    · show (s * s1) • a = a
      rw [mul_smul, hs1a, hsb]
  have hfinal : Work.GW2.Inverts s Hsub := by
    intro hh hhm
    have hcomm' : (⟨s * s1, hs1H⟩ : Hsub) * ⟨hh, hhm⟩ = ⟨hh, hhm⟩ * ⟨s * s1, hs1H⟩ :=
      hcomm.is_comm.comm _ _
    have hcc : (s * s1) * hh = hh * (s * s1) := congrArg Subtype.val hcomm'
    have hshs : s1 * hh * s1 = hh⁻¹ := by
      have := hinvH hh hhm
      rwa [hs1inv] at this
    have hs : s = (s * s1) * s1 := by rw [mul_assoc, hs1sq, mul_one]
    have hA : s * hh * s⁻¹ = ((s * s1) * s1) * hh * (((s * s1) * s1))⁻¹ := by
      conv_lhs => rw [hs]
    have hB : (((s * s1) * s1))⁻¹ = s1 * (s * s1)⁻¹ := by rw [mul_inv_rev, hs1inv]
    have hkey : s * hh * s⁻¹ = (s * s1) * hh⁻¹ * (s * s1)⁻¹ := by
      rw [hA, hB]
      have hstep : ((s * s1) * s1) * hh * (s1 * (s * s1)⁻¹)
          = (s * s1) * (s1 * hh * s1) * (s * s1)⁻¹ := by group
      rw [hstep, hshs]
    have hconj : (s * s1) * hh⁻¹ * (s * s1)⁻¹ = hh⁻¹ := by
      have h1 : (s * s1) * hh⁻¹ = hh⁻¹ * (s * s1) := by
        have h2 := congrArg (fun z => hh⁻¹ * z * hh⁻¹) hcc
        have h2' : hh⁻¹ * (s * s1) = (s * s1) * hh⁻¹ := by simpa [mul_assoc] using h2
        exact h2'.symm
      calc (s * s1) * hh⁻¹ * (s * s1)⁻¹ = hh⁻¹ * (s * s1) * (s * s1)⁻¹ := by rw [h1]
        _ = hh⁻¹ := by group
    rw [hkey, hconj]
  have hHsub : Hsub = MulAction.stabilizer G a ⊓ MulAction.stabilizer G b :=
    Work.GW2.pairStab_eq_inf_stabilizer a b
  rw [← hHsub]
  exact hfinal

end Work.ZASS2
