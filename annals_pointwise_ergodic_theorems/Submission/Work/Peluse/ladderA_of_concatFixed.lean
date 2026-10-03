import Mathlib
import Submission.Work.Peluse.Holds.Corrected
import Submission.Work.Peluse.ladderA_main

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators

/-!
# `Work.Peluse.C46.PeluseLadderA` from the corrected Theorem 3.5

The target (`PeluseLadderA`, `Submission/Work/Peluse/Holds/Corrected.lean`) is
Peluse's Lemma 5.7 in its corrected form.  This file derives it from the corrected
coefficient-uniform concatenation theorem `PeluseConcatFixed`
(`Submission/Work/Peluse/UControl/peluseLadderStrong.lean`).

The mathematics is the source's §5 proof: the ladder's peel of the hypothesis's family
into the `A`-part (the slots of the index subsets containing the peeled slot `s₀`) and the
`B`-part (those avoiding it).  The `A`-part is averaged along the peeled parameter with the
common coefficient `p s₀.1 a`; the `B`-part is absorbed into the differenced function.  The
assembly of the two branches is:

* `Work.Peluse.LadderA.mainBranch` — the case `card (AIdx k kω s₀) ≠ 0`: the peel plus
  Markov's inequality on the good parameter sets, consuming Theorem 3.5 (`midPerQ`),
  `Work.Peluse.LadderA.midBound`, `Work.Peluse.LadderA.concl_avg_sum`;
* `Work.Peluse.LadderA.zeroBranch` — the case `card (AIdx k kω s₀) = 0`: there the peel is
  trivial and the conclusion is the hypothesis with the `t'` long directions appended.

The only work here is the *uniform* choice of the datum-level constants `(K, C₀, t', c)`:
for each level `r` the concatenation theorem supplies a witness pack `(s', C', A, K)`
depending only on `r`, and the constants are chosen as the running sum (and, for `c`, the
running infimum) of those, so that they are independent of the instance.  The witnesses are
indexed by the subtype of slots `s₀` for which the peel's `A`-part is nonempty, which lets
them be built by `Classical.choose` *transparently* (as local `let`-definitions), so that the
clause of Theorem 3.5 they carry matches definitionally the clause `mainBranch` consumes.
-/

namespace Work.Peluse.LadderA

noncomputable section

open Work.Peluse Work.Peluse.UControl

/-- The witness pack of Theorem 3.5 in its *symmetric* form (`concatFixed_symm`): for each
shift constant `C` and level `s ≥ 1` a quadruple `(s', C', A, K)` satisfying the conclusion of
`PeluseConcatFixed` and the a-priori bounds. -/
theorem concatWitnessPack (h : Work.Peluse.UControl.PeluseConcatFixed) (C s : ℕ) (hs : 1 ≤ s) :
    ∃ w : ℕ × ℝ × ℝ × ℕ, 1 ≤ w.1 ∧ 0 < w.2.1 ∧ 1 ≤ w.2.2.1 ∧ 1 ≤ w.2.2.2 ∧
      ∀ (c : ℤ), 0 < c → ∀ (N M₁ M₂ : ℕ) (d : Fin s → ℤ) (δ δ' : ℝ) (f : ℤ → ℂ),
        1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ) →
        (∀ i : Fin s, |d i| ≤ (C : ℤ) * (N : ℤ) / (M₁ : ℤ)) →
        Work.Peluse.SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
        0 < δ → δ ≤ 1 → 0 < δ' → w.2.2.1 * δ' ≤ δ ^ w.2.2.2 →
        w.2.2.1 ≤ (M₂ : ℝ) * (δ * δ') ^ w.2.2.2 →
        δ ≤ (((Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).card : ℝ))⁻¹ *
              ∑ a ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ),
                Work.Peluse.boxNorm s (fun i : Fin s => Work.Peluse.arithIcc (c * a + d i) M₁)
                  (Work.Peluse.symIcc N) f →
        w.2.1 * (δ * δ') ^ w.2.2.2 ≤
          Work.Peluse.uNorm w.1 (Work.Peluse.arithIcc c (⌊δ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
            (Work.Peluse.symIcc N) f := by
  obtain ⟨s', hs', C', hC', A', hA', K', hK', hrest⟩ := concatFixed_symm h C s hs
  exact ⟨⟨s', C', A', K'⟩, hs', hC', hA', hK', hrest⟩

end

end Work.Peluse.LadderA

namespace Work.Peluse

open Work.Peluse.UControl Work.Peluse.LadderA

theorem ladderA_of_concatFixed (h : Work.Peluse.UControl.PeluseConcatFixed) :
    Work.Peluse.C46.PeluseLadderA := by
  intro n ι hF hD k kω p D
  classical
  by_cases hslot : Fintype.card (Work.Peluse.UControl.Slot ι k) = 0
  · -- no slots: the conclusion's `∀ s₀` is vacuous, every constant works
    refine ⟨1, 1, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    intro A M₁ M₂ N γ γ' f h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 s₀
    exfalso
    have hpos : 0 < Fintype.card (Work.Peluse.UControl.Slot ι k) :=
      Fintype.card_pos_iff.mpr ⟨s₀⟩
    omega
  · -- the slot type is nonempty
    haveI : Nonempty (Work.Peluse.UControl.Slot ι k) :=
      Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hslot)
    -- the witness pack of Theorem 3.5 at level `r`, as a transparent local definition
    let Wp := fun (r : ℕ) (hr : 1 ≤ r) =>
      Classical.choose
        (concatWitnessPack h (Fintype.card (Work.Peluse.UControl.Slot ι k) * D + 3) r hr)
    have Wspec := fun (r : ℕ) (hr : 1 ≤ r) =>
      Classical.choose_spec
        (concatWitnessPack h (Fintype.card (Work.Peluse.UControl.Slot ι k) * D + 3) r hr)
    -- the slots whose peel has a nontrivial `A`-part
    let Good := {s₀ : Work.Peluse.UControl.Slot ι k // 1 ≤ Fintype.card (AIdx k kω s₀)}
    -- the witness data, indexed by `Good`; transparent, so that it unfolds to the raw
    -- `Classical.choose` projections of `Wspec`
    let sfl : Good → ℕ := fun x => (Wp (Fintype.card (AIdx k kω x.1)) x.2).1
    let Cfl : Good → ℝ := fun x => (Wp (Fintype.card (AIdx k kω x.1)) x.2).2.1
    let Afl : Good → ℝ := fun x => (Wp (Fintype.card (AIdx k kω x.1)) x.2).2.2.1
    let Kfl : Good → ℕ := fun x => (Wp (Fintype.card (AIdx k kω x.1)) x.2).2.2.2
    have hsfl1 : ∀ x : Good, 1 ≤ sfl x := fun x => (Wspec _ x.2).1
    have hCfl0 : ∀ x : Good, 0 < Cfl x := fun x => (Wspec _ x.2).2.1
    have hAfl1 : ∀ x : Good, 1 ≤ Afl x := fun x => (Wspec _ x.2).2.2.1
    have hKfl1 : ∀ x : Good, 1 ≤ Kfl x := fun x => (Wspec _ x.2).2.2.2.1
    have hAflnn : ∀ x : Good, 0 ≤ Afl x := fun x => le_trans zero_le_one (hAfl1 x)
    -- the datum-level constants
    set m : ℕ := Fintype.card (FamIdx kω) with hmdef
    set Kh : ℕ := 1 + ∑ x : Good, Kfl x with hKhdef
    set tbig : ℕ := m + 1 + ∑ x : Good, sfl x with htbigdef
    set Kb : ℕ := m * (Fintype.card (Work.Peluse.UControl.Slot ι k) * D + 1) + 1 with hKbdef
    set c₁ : ℝ := 1 / (2 ^ (2 ^ m + 1) * (((Kb : ℕ) : ℝ) + 1) ^ (2 ^ m)) with hc₁def
    set Cbig : ℝ := 2 + ∑ x : Good, Afl x / c₁ ^ Kfl x with hCbigdef
    set Kbig : ℕ := max (2 ^ (m + 1) * Kh + 1) (1 + 2 ^ m * (1 + Kh * 2 ^ tbig)) with hKbigdef
    have hc₁pos : 0 < c₁ := by
      rw [hc₁def]
      positivity
    have hpowpos : ∀ x : Good, 0 < c₁ ^ Kfl x := fun x => pow_pos hc₁pos _
    have hCbig2 : 2 ≤ Cbig := by
      rw [hCbigdef]
      have h : 0 ≤ ∑ x : Good, Afl x / c₁ ^ Kfl x :=
        Finset.sum_nonneg (fun x _ => div_nonneg (hAflnn x) (le_of_lt (hpowpos x)))
      linarith
    have hCbigpos : 0 < Cbig := lt_of_lt_of_le two_pos hCbig2
    have hKbig1 : 1 ≤ Kbig := by
      rw [hKbigdef]
      exact le_trans (Nat.le_add_left 1 (2 ^ (m + 1) * Kh)) (le_max_left _ _)
    have hKbigle : 2 ^ (m + 1) * Kh + 1 ≤ Kbig := by
      rw [hKbigdef]
      exact le_max_left _ _
    have htbig1 : 1 ≤ tbig := by
      rw [htbigdef]; omega
    have htm : m ≤ tbig := by
      rw [htbigdef]; omega
    have hδ₀ge : ∀ γ : ℝ, 0 < γ → c₁ * γ ^ (2 ^ m) ≤
        ((γ / (((Kb : ℕ) : ℝ) + 1)) / 2) ^ (2 ^ m) / 2 := by
      intro γ hγ
      have h2 : ((2 : ℝ) ^ (2 ^ m + 1)) = (2 : ℝ) ^ (2 ^ m) * 2 := by rw [pow_succ]
      have h1 : ((2 : ℝ) ^ (2 ^ m) * 2 * (((Kb : ℕ) : ℝ) + 1) ^ (2 ^ m)) ≠ 0 := by positivity
      have h2' : ((2 : ℝ) ^ (2 ^ m)) ≠ 0 := by positivity
      have h3 : (((Kb : ℕ) : ℝ) + 1) ^ (2 ^ m) ≠ 0 := by positivity
      rw [hc₁def, h2, div_pow, div_pow]
      field_simp
      norm_num
    rw [hKbdef] at hδ₀ge
    -- the per-`s₀` obligation, uniform in the constants already chosen
    have hex : ∀ s₀ : Work.Peluse.UControl.Slot ι k, ∃ cc : ℝ, 0 < cc ∧
        ∀ (A : Finset (Fin n → ℤ)) (M₁ M₂ N : ℕ) (γ γ' : ℝ) (f : (Fin n → ℤ) → ℤ → ℂ),
        1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → ((M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ)) →
        0 < γ → γ ≤ 1 → 0 < γ' → Cbig * γ' ≤ γ ^ Kbig →
        (∀ i a, a ∈ A → 0 < p i a) →
        (∀ i a, a ∈ A → p i a * (M₁ : ℤ) * (M₂ : ℤ) ≤ (N : ℤ)) →
        (∀ i a, a ∈ A → |p i a| * (M₁ : ℤ) * (M₂ : ℤ) ≤ (D : ℤ) * (N : ℤ)) →
        (∀ a ∈ A, ∀ x : ℤ, ‖f a x‖ ≤ 1) → (∀ a ∈ A, SupportIn (f a) N) →
        Cbig * (γ * γ') ^ (-(Kbig : ℤ)) ≤ (M₂ : ℝ) →
        γ ≤ ((A.card : ℝ))⁻¹ * ((paramBox (k := k) M₂).card : ℝ)⁻¹ *
              ∑ a ∈ A, ∑ a' ∈ paramBox (k := k) M₂,
                boxNorm (Fintype.card (FamIdx kω))
                  (fun j => pDirFam p M₁ a a' ((Fintype.equivFin (FamIdx kω)).symm j))
                  (symIcc N) (f a) →
        cc * (γ * γ') ^ Kbig ≤
            ((A.card : ℝ))⁻¹ * ((paramBox (k := k) M₂).card : ℝ)⁻¹ *
              ∑ a ∈ A, ∑ b ∈ paramBox (k := k) M₂,
                boxNorm (Fintype.card (ConclIdx s₀ kω tbig))
                  (fun j => conclDir p M₁ M₂ γ' s₀ tbig a b
                    ((Fintype.equivFin (ConclIdx s₀ kω tbig)).symm j))
                  (symIcc N) (f a) := by
      intro s₀
      by_cases hs0 : Fintype.card (AIdx k kω s₀) = 0
      · -- the zero branch
        obtain ⟨cc, hcc, hmain⟩ :=
          zeroBranch k kω p D s₀ m hmdef.symm hs0 tbig htm Kbig hKbig1
        refine ⟨cc, hcc, ?_⟩
        intro A M₁ M₂ N γ γ' f h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
        have hγ'1 : γ' ≤ 1 := by
          have h1' : Cbig * γ' ≤ 1 := le_trans h8 (by
            calc γ ^ Kbig ≤ γ ^ 1 := pow_le_pow_of_le_one (le_of_lt h5) h6 (by omega)
              _ = γ := pow_one γ
              _ ≤ 1 := h6)
          nlinarith [h7, h1', hCbig2]
        have hnondeg' : Cbig ≤ (M₂ : ℝ) * (γ * γ') ^ Kbig := by
          have hx : (0 : ℝ) < (γ * γ') ^ Kbig := by positivity
          have hz : (γ * γ') ^ (-(Kbig : ℤ)) = ((γ * γ') ^ Kbig)⁻¹ := by
            rw [zpow_neg, zpow_natCast]
          rw [hz] at h14
          calc Cbig = Cbig * ((γ * γ') ^ Kbig)⁻¹ * (γ * γ') ^ Kbig := by field_simp
            _ ≤ (M₂ : ℝ) * (γ * γ') ^ Kbig := mul_le_mul_of_nonneg_right h14 (le_of_lt hx)
        have hL1 : 1 ≤ γ' * (M₁ : ℝ) * (M₂ : ℝ) :=
          L_ge_one h5 h6 h7 hCbig2 hKbig1 (by exact_mod_cast h1) (by exact_mod_cast h2)
            h8 hnondeg'
        exact hmain A M₁ M₂ N γ γ' f h1 h2 h3 h4 h5 h6 h7 hγ'1 hL1 h9 h10 h11 h12 h13 h15
      · -- the main branch
        have hs1 : 1 ≤ Fintype.card (AIdx k kω s₀) := Nat.one_le_iff_ne_zero.mpr hs0
        have hmem : (⟨s₀, hs1⟩ : Good) ∈ (Finset.univ : Finset Good) := Finset.mem_univ _
        have hKc_le : Kfl ⟨s₀, hs1⟩ ≤ Kh := by
          have h1 : Kfl ⟨s₀, hs1⟩ ≤ ∑ x : Good, Kfl x :=
            Finset.single_le_sum (f := Kfl) (fun x _ => Nat.zero_le _) hmem
          rw [hKhdef]; omega
        have ht : sfl ⟨s₀, hs1⟩ + 1 ≤ tbig := by
          have h1 : sfl ⟨s₀, hs1⟩ ≤ ∑ x : Good, sfl x :=
            Finset.single_le_sum (f := sfl) (fun x _ => Nat.zero_le _) hmem
          rw [htbigdef]; omega
        have hCbigle : Afl ⟨s₀, hs1⟩ / c₁ ^ Kfl ⟨s₀, hs1⟩ ≤ Cbig := by
          have h1 : Afl ⟨s₀, hs1⟩ / c₁ ^ Kfl ⟨s₀, hs1⟩ ≤ ∑ x : Good, Afl x / c₁ ^ Kfl x :=
            Finset.single_le_sum (f := fun x : Good => Afl x / c₁ ^ Kfl x)
              (fun x _ => div_nonneg (hAflnn x) (le_of_lt (hpowpos x))) hmem
          rw [hCbigdef]; linarith
        have hlev1 : (1 : ℝ) ≤ (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig)) :=
          one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
        have hKexp2 : (Kfl ⟨s₀, hs1⟩ : ℝ) * (2 : ℝ) ^ tbig /
              (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig)) ≤ (Kbig : ℝ) := by
          have h1 : (Kfl ⟨s₀, hs1⟩ : ℝ) * (2 : ℝ) ^ tbig /
                (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig))
              ≤ (Kfl ⟨s₀, hs1⟩ : ℝ) * (2 : ℝ) ^ tbig :=
            div_le_self (by positivity) hlev1
          have h2 : (Kfl ⟨s₀, hs1⟩ : ℝ) ≤ (Kh : ℝ) := by exact_mod_cast hKc_le
          have h3 : (Kfl ⟨s₀, hs1⟩ : ℝ) * (2 : ℝ) ^ tbig
              ≤ (Kh : ℝ) * (2 : ℝ) ^ tbig :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
          have h4 : (Kh : ℝ) * (2 : ℝ) ^ tbig
              ≤ 1 + (2 : ℝ) ^ m * (1 + (Kh : ℝ) * (2 : ℝ) ^ tbig) := by
            have h5 : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
            have h7 : (1 : ℝ) + (Kh : ℝ) * (2 : ℝ) ^ tbig
                ≤ (2 : ℝ) ^ m * (1 + (Kh : ℝ) * (2 : ℝ) ^ tbig) := by
              calc (1 : ℝ) + (Kh : ℝ) * (2 : ℝ) ^ tbig
                  = 1 * (1 + (Kh : ℝ) * (2 : ℝ) ^ tbig) := by ring
                _ ≤ (2 : ℝ) ^ m * (1 + (Kh : ℝ) * (2 : ℝ) ^ tbig) :=
                    mul_le_mul_of_nonneg_right h5 (by positivity)
            linarith
          have h5 : (1 : ℝ) + (2 : ℝ) ^ m * (1 + (Kh : ℝ) * (2 : ℝ) ^ tbig) ≤ (Kbig : ℝ) := by
            rw [hKbigdef]
            exact_mod_cast le_max_right (2 ^ (m + 1) * Kh + 1) (1 + 2 ^ m * (1 + Kh * 2 ^ tbig))
          linarith
        have hKexp1 : 1 + (2 : ℝ) ^ m * (1 + (Kfl ⟨s₀, hs1⟩ : ℝ)
              * (2 : ℝ) ^ tbig) / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig)) ≤ (Kbig : ℝ) := by
          have h1 : (1 + (Kfl ⟨s₀, hs1⟩ : ℝ) * (2 : ℝ) ^ tbig)
                / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig))
              ≤ 1 + (Kfl ⟨s₀, hs1⟩ : ℝ) * (2 : ℝ) ^ tbig :=
            div_le_self (by positivity) hlev1
          have h2 : 1 + (Kfl ⟨s₀, hs1⟩ : ℝ) * (2 : ℝ) ^ tbig
              ≤ 1 + (Kh : ℝ) * (2 : ℝ) ^ tbig := by
            have h3 : (Kfl ⟨s₀, hs1⟩ : ℝ) ≤ (Kh : ℝ) := by exact_mod_cast hKc_le
            linarith [mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ tbig)]
          have h4 : (2 : ℝ) ^ m * ((1 + (Kfl ⟨s₀, hs1⟩ : ℝ) * (2 : ℝ) ^ tbig)
                / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig)))
              ≤ (2 : ℝ) ^ m * (1 + (Kh : ℝ) * (2 : ℝ) ^ tbig) := by
            have h5 : (2 : ℝ) ^ m * ((1 + (Kfl ⟨s₀, hs1⟩ : ℝ) * (2 : ℝ) ^ tbig)
                  / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig)))
                ≤ (2 : ℝ) ^ m * (1 + (Kfl ⟨s₀, hs1⟩ : ℝ) * (2 : ℝ) ^ tbig) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
            have h6 : (2 : ℝ) ^ m * (1 + (Kfl ⟨s₀, hs1⟩ : ℝ) * (2 : ℝ) ^ tbig)
                ≤ (2 : ℝ) ^ m * (1 + (Kh : ℝ) * (2 : ℝ) ^ tbig) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
            linarith
          have h5 : (1 : ℝ) + (2 : ℝ) ^ m * (1 + (Kh : ℝ) * (2 : ℝ) ^ tbig) ≤ (Kbig : ℝ) := by
            rw [hKbigdef]
            exact_mod_cast le_max_right (2 ^ (m + 1) * Kh + 1) (1 + 2 ^ m * (1 + Kh * 2 ^ tbig))
          rw [mul_div_assoc]
          linarith
        have hconc := (Wspec (Fintype.card (AIdx k kω s₀)) hs1).2.2.2.2
        obtain ⟨cc, hcc, hmain⟩ := mainBranch k kω p D s₀ m hmdef.symm hs1 tbig
          (sfl ⟨s₀, hs1⟩) (hsfl1 ⟨s₀, hs1⟩) (Cfl ⟨s₀, hs1⟩) (Afl ⟨s₀, hs1⟩)
          (hCfl0 ⟨s₀, hs1⟩) (hAfl1 ⟨s₀, hs1⟩) (Kfl ⟨s₀, hs1⟩) (hKfl1 ⟨s₀, hs1⟩)
          ht htm hconc
          Kbig Cbig c₁ Kh hKc_le hKbigle hCbigle hc₁pos hCbig2 hδ₀ge hKexp1 hKexp2
        exact ⟨cc, hcc, hmain⟩
    -- the uniform constant `c` is the infimum of the per-`s₀` constants
    set cfin : ℝ := (Finset.univ : Finset (Work.Peluse.UControl.Slot ι k)).inf'
      (Finset.univ_nonempty) (fun s₀ => Classical.choose (hex s₀)) with hcfin
    have hcfinpos : 0 < cfin := by
      rw [hcfin, Finset.lt_inf'_iff]
      intro b _
      exact (Classical.choose_spec (hex b)).1
    refine ⟨Kbig, Cbig, tbig, cfin, hKbig1, hCbigpos, htbig1, hcfinpos, ?_⟩
    intro A M₁ M₂ N γ γ' f h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 s₀
    have hcc := (Classical.choose_spec (hex s₀)).2 A M₁ M₂ N γ γ' f
      h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    have hle : cfin ≤ Classical.choose (hex s₀) := by
      rw [hcfin, Finset.inf'_le_iff]
      exact ⟨s₀, Finset.mem_univ s₀, le_refl _⟩
    exact le_trans (mul_le_mul_of_nonneg_right hle (by positivity)) hcc

end Work.Peluse
