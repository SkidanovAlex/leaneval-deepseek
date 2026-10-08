import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.VUInvSetTrivial
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.CosetInvCountNeFive
import Submission.Work.CORE3.CosetInvCountNeSix
import Submission.Work.CORE3.CosetPairCountFour
import Submission.Work.CORE3.CommutingPairTallyCosets
import Submission.Work.CORE3.CommutingPairTallyCentralizers
import Submission.Work.CORE3.InvolutionCentralizerCount
import Submission.Work.CORE3.CommutingInvolsVsharp
import Submission.Work.CORE3.CommutingInvolsOutsideV
import Submission.Work.CORE3.BenderSevenU3
import Submission.Work.CORE3.J4.J4CosetStep
import Submission.Work.CORE3.J4.Case1bSixEightClean

/-!
# `Work.CORE3.Case1bEightNine`

Bender 1981 §3, pp. 223–224, items (6)–(9): the counting results of Case (1), subcase (1b)
(`V = O₂(Ĥ)` of type `(2,2)`) from which the subsequent leaves compute the whole `b`-data.

* **(6)–(9)(1):** `bₙ = 0` for `n ≥ 5`.  Every coset of `Ĥ` containing an involution carries at
  most four involutions: `n ≤ 6` (Bender (5), `CosetInvCountLeSix`), `n ≠ 5`
  (`CosetInvCountNeFive`), `n ≠ 6` (`J4.cosetInvCountNeSixClean`, the counting exclusion of (6)
  in a form that does not consume step (7)) — then `bCount_eq_zero_of_involution_bound` of
  `Case1bEightNineDefs` converts the pointwise bound `n ≤ 4` into the vanishing of `bₙ`
  for `n ≥ 5`.
* **(8):** `3 b₄ + b₂ = 6 k²`, `k = |K|`.  The tally `T` of commuting pairs `(z,s)` with `z ∉ Ĥ`
  and `s ∈ Ĥ` an involution is computed twice: coset by coset as `2b₂ + 6b₄`
  (`CommutingPairTallyCosets`) and by centralizers as `12 k²` (`CommutingPairTallyCentralizers`,
  using `(z,s) ↦ (s,z)` and the three structural inputs `InvolutionCentralizerCount`,
  `CommutingInvolsVsharp`, `CommutingInvolsOutsideV`).
* **(7):** `b₄ ≠ 0 → |U| = |K| = 3`.  A coset contributing to `b₄` contains an involution `y`; by
  Bender (6), some involution `z` of that coset inverts an odd-order `X ≤ Ĥ` with even
  `G`-centralizer *and* with an involution `s ∈ Ĥ` inverting `X` (`J4.J4CosetStep`); Bender (7)
  in its correct form — the hypothesis is `N_Ĥ(X)`, i.e. the existence of such an `s`, not
  `N_G(X)`, which is automatic from `y` — is `BenderSevenU3` (design pass 23 §A) and gives
  `|U| = 3`; `K ≤ U` with `K ≠ ⊥` then forces `|K| = 3`.
-/

namespace Work.CORE3

open Work.GW2

/-- Bender 1981 §3, p. 224, (6)–(9).  Deliverable `Work.GW2.Case1bEightNineProp`, with the
involution-count identities of `Case1bCountProp` available as the hypothesis `hCount`.

`b_n = 0` for `n ≥ 5`; the count of commuting pairs `(z,s)` (`z ∉ Ĥ` an involution, `s ∈ Ĥ` an
involution, `zs = sz`), computed two ways, gives `3b₄ + b₂ = 6k²` with `k = |K|`; and `b₄ ≠ 0`
forces `|U| = k = 3` (the Case (7) analysis: a `y ∈ J₄` inverts a `2'`-subgroup `X ≠ 1` of `Ĥ`
with `C_Ĥ(X)`, `N_Ĥ(X)` of even order only when `|U| = k = 3`). -/
theorem Case1bEightNine (I : Case1Inputs) (hCount : Case1bCountProp) : Case1bEightNineProp := by
  intro G _ _ hFT hBc B h1 D
  classical
  -- Bender (5): no involution outside `Ĥ` inverts a nontrivial element of `VU = O₂(Ĥ)·O(Ĥ)`.
  have h5 : ∀ z : G, orderOf z = 2 → z ∉ B.Hhat →
      invSet (pCoreIn 2 B.Hhat ⊔ B.U) z = {1} :=
    VUInvSetTrivial G I hBc B h1 D
  -- Bender (6): at most four involutions per coset.
  have hA : ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → cosetInvCount B.Hhat y ≤ 4 := by
    intro y hy2 hyH
    have h6 := cosetInvCount_le_six G I hBc B h1 D h5 y hy2 hyH
    have hne5 := CosetInvCountNeFive G I hBc B h1 D h5 y hy2 hyH
    -- Bender (6) for `n ≠ 6`: `Work.CORE3.J4.cosetInvCountNeSixClean` (no step-(7) input)
    have hne6 := Work.CORE3.J4.cosetInvCountNeSixClean I hBc B h1 D y hy2 hyH
    omega
  -- Bender (7)/(8): a four-involution coset contributes six commuting pairs.
  have hB : ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → cosetInvCount B.Hhat y = 4 →
      Work.CORE3.cosetPairCount B.Hhat y = 6 :=
    fun y hy hyH h4 => CosetPairCountFour G I hBc B h1 D y hy hyH h4
  -- The three structural inputs of the centralizer-side tally.
  have hCent : ∀ s : G, orderOf s = 2 →
      (involutionSet (⊤ : Subgroup G) ∩ Subgroup.centralizer ({s} : Set G)).ncard
        = 3 + 2 * Nat.card D.K :=
    fun s hs => InvolutionCentralizerCount G I hBc B h1 D s hs
  have hVsharp : ∀ s : G, s ∈ pCoreIn 2 B.Hhat → orderOf s = 2 →
      (involutionSet B.Hhat ∩ Subgroup.centralizer ({s} : Set G)).ncard
        = 3 + 2 * Nat.card D.K :=
    fun s hsV hs => CommutingInvolsVsharp G I hBc B h1 D s hsV hs
  have hOut : ∀ s : G, s ∈ B.Hhat → orderOf s = 2 → s ∉ pCoreIn 2 B.Hhat →
      (involutionSet B.Hhat ∩ Subgroup.centralizer ({s} : Set G)).ncard = 3 :=
    fun s hsH hs hsV => CommutingInvolsOutsideV G I hBc B h1 D s hsH hs hsV
  refine ⟨?_, ?_, ?_⟩
  · -- (9)/(1): `bₙ = 0` for `n ≥ 5`
    intro n hn
    exact bCount_eq_zero_of_involution_bound B.Hhat hA n hn
  · -- (8): `3 b₄ + b₂ = 6 k²`, by comparing the two tallies
    have hT1 := CommutingPairTallyCosets G I hBc B h1 D hA hB
    have hT2 := CommutingPairTallyCentralizers G I hBc B h1 D hCount hCent hVsharp hOut
    have hmain : 2 * bCount B.Hhat 2 + 6 * bCount B.Hhat 4 = 12 * Nat.card D.K ^ 2 :=
      hT1.symm.trans hT2
    have hmain' : 2 * (3 * bCount B.Hhat 4 + bCount B.Hhat 2) = 12 * Nat.card D.K ^ 2 := by
      rw [show 2 * (3 * bCount B.Hhat 4 + bCount B.Hhat 2)
          = 2 * bCount B.Hhat 2 + 6 * bCount B.Hhat 4 by ring]
      exact hmain
    have h2 : 12 * Nat.card D.K ^ 2 = 2 * (6 * Nat.card D.K ^ 2) := by ring
    exact Nat.mul_left_cancel (by norm_num : (0 : ℕ) < 2) (by rw [hmain', h2])
  · -- (7): `b₄ ≠ 0 → |U| = |K| = 3`
    intro hb4
    -- a coset contributing to `b₄`, with representative the involution `y`
    obtain ⟨c, hc1, hc2⟩ : ∃ c : G ⧸ B.Hhat, c ≠ ((1 : G) : G ⧸ B.Hhat) ∧
        cosetInvCount B.Hhat (Quotient.out c) = 4 := by
      by_contra hcon
      apply hb4
      rw [bCount, Set.ncard_eq_zero, Set.eq_empty_iff_forall_notMem]
      rintro c ⟨hc1, hc2⟩
      exact hcon ⟨c, hc1, hc2⟩
    -- an involution in that coset
    obtain ⟨y, hy2, hymem⟩ : ∃ y : G, orderOf y = 2 ∧
        (Quotient.out c)⁻¹ * y ∈ B.Hhat := by
      by_contra hcon
      have hempty : ({x : G | orderOf x = 2 ∧ (Quotient.out c)⁻¹ * x ∈ B.Hhat} : Set G) = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr (fun x hx => hcon ⟨x, hx.1, hx.2⟩)
      rw [cosetInvCount, hempty, Set.ncard_empty] at hc2
      exact absurd hc2 (by norm_num)
    have hyH : y ∉ B.Hhat := by
      intro hyh
      have h2 : Quotient.out c = y * ((Quotient.out c)⁻¹ * y)⁻¹ := by group
      have hout : Quotient.out c ∈ B.Hhat := by
        rw [h2]
        exact B.Hhat.mul_mem hyh (B.Hhat.inv_mem hymem)
      exact quotient_out_notMem (Hh := B.Hhat) hc1 hout
    have hy4 : cosetInvCount B.Hhat y = 4 := by
      rw [← hc2]
      exact (cosetInvCount_eq_of_leftCoset_eq (x := Quotient.out c) (y := y) (by
        rw [leftCoset_eq_iff]
        exact mem_leftCoset.mpr hymem)).symm
    -- Bender (6) produces an involution `z` of the coset inverting a suitable odd `X`, together
    -- with Bender's `N_Ĥ(X)`-witness `s ∈ Ĥ` (design pass 23 §A)
    obtain ⟨z, hz2, ⟨h, hhH, hzy⟩, X, hXle, hXne, hXodd, hXinv, hCeven, _hNeven,
      ⟨s, hsH, hs2, hsX⟩⟩ :=
      Work.CORE3.J4.J4CosetStep (G := G) I hBc B h1 D hy2 hyH hy4
    have hzH : z ∉ B.Hhat := by
      intro hcon
      apply hyH
      have h1 : h⁻¹ * z ∈ B.Hhat := B.Hhat.mul_mem (B.Hhat.inv_mem hhH) hcon
      rw [hzy] at h1
      simpa using h1
    -- Bender (7), in the corrected form of design pass 23 §A (`s ∈ Ĥ` inverts `X`)
    have hU3 := BenderSevenU3 G I hBc B h1 D hz2 hzH X hXle hXne hXodd hXinv hCeven hsH hs2 hsX
    refine ⟨hU3, ?_⟩
    -- `|K|` divides `|U| = 3` and is not `1`
    have hKU : D.K ≤ B.U :=
      (Work.CORE2A.isHallIn_le D.hall).trans (Subgroup.map_subtype_le _)
    have hdvd : Nat.card D.K ∣ Nat.card B.U := Subgroup.card_dvd_of_le hKU
    rw [hU3] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1' | h3'
    · exact absurd (Subgroup.card_eq_one.mp h1') D.ne
    · exact h3'

end Work.CORE3
