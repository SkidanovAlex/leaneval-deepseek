import Mathlib
import Submission.Work.CORE4.Defs27
import Submission.Work.CORE4.EightTrich9Holds
import Submission.Work.CORE4.EightN9U
import Submission.Work.CORE4.EightN9Inf
import Submission.Work.CORE4.Case2EightQfacts
import Submission.Work.CORE4.Case2EightCase3U9plus
import Submission.Work.CORE4.Case2EightN9Sup
import Submission.Work.CORE4.Case2EightObjExists
import Submission.Work.CORE4.Case2Eight
import Submission.Work.CORE4.Case2EightP1Le
import Submission.Work.CORE4.Case2EightP0LeP1
import Submission.Work.CORE4.Case2EightA_le_FsupK0

namespace Work.CORE4

open Work.GW2 Subgroup

/-- Bender 1981, §4 (8) (p. 226): the index bound `|U : B₀ K F(U)| ≤ p` (the second-to-last
conjunct of `Case2EightFacts`, i.e. `Work.CORE4.EightIndexLeafProp`) from the ONE remaining input
of the case-3 branch.

The hypothesis is exactly the extra antecedent of `Work.CORE4.Case2EightCase3U9plus` (α):
`s` inverts every element of `B.U ⊓ C_G(Qsub p B)`.  Everything else is on disk and proved:

* `hTrich` — the trichotomy: `Work.CORE4.EightTrich9Holds` (`Work.GW2.C27.EightTrich9Prop I`),
  assembled from `Work.CORE4.TrichCore`, `Work.CORE4.TrichCs`, `Work.CORE4.TrichCP` by design 27's
  `eightTrich9_of_leaves`; its disjunction has exactly the shape the assembly wants;
* `hQnc` (`¬ IsCyclic ↥(Qsub p B)`) and the exponent of `Qsub p B` — `Work.CORE4.Case2EightQfacts`;
* `hCase2` (`N_U(A) = (U ⊓ M) ⊔ F(U)` and `u ≤ p`) — `Work.CORE4.EightN9U` +
  `Work.CORE4.EightN9Inf` + `Work.CORE4.Case2EightN9Sup` (the body of
  `Work.CORE4.Case2EightCase2N9`, which is tainted by the old case-2 stubs, so rebuild it from
  these three);
* `hCase3` (`U = (U ⊓ M) ⊔ F(U)`) — `Work.CORE4.Case2EightCase3U9plus` fed by the hypothesis (α);
* the branch `U ≤ N_G(A)` is handled by the assembly's first case (`u = 1`, index `≤ p₀ ≤ p`) using
  only `Work.CORE4.Case2Eight_*` / `Work.CORE4.Case2EightP0LeP1` / `Work.CORE4.Case2EightP1Le`.

The proof is therefore a copy of the private `Work.CORE4.case2EightIndex_assembly`
(`Submission/Work/CORE4/Case2EightIndex9.lean`, not importable) with those four inputs supplied —
do NOT cite `Work.CORE4.Case2EightIndex9`, `Work.CORE4.Case2EightIndex` or
`Work.CORE4.Case2EightCase2N9`, all of which rest on `sorry`.  Must be sorry-free:
`#print axioms Work.CORE4.EightIndexOfAlpha` = `[propext, Classical.choice, Quot.sound]`.

Caveat for the caller: (α) is NOT derivable from the recorded hypotheses alone
(`CORE4/EightExCase3.lean`: it needs §4 (5), `C_U(s) = B₀`), so this is the honest conditional form
of `Work.CORE4.EightIndexLeafProp`. -/
theorem EightIndexOfAlpha (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case2 B → ∀ C : Work.GW2.Case2Ctx6 B, Work.GW2.Case2PrePlus B C.D →
        Work.GW2.Case2SevenFacts B C.D →
        ∀ (p : ℕ) (P : Subgroup G), p.Prime → P ≤ C.D.F → Nat.card P = p →
          (∀ A : Subgroup G, Work.GW2.Case2EightObj C.D p P A →
            ¬ IsCyclic ↥(Work.CORE4.Qsub p B) →
            (∀ x ∈ Work.CORE4.Qsub p B, C.D.s * x * C.D.s⁻¹ = x⁻¹) →
            (∀ x ∈ B.U ⊓ Subgroup.centralizer ((Work.CORE4.Qsub p B : Subgroup G) : Set G),
              C.D.s * x * C.D.s⁻¹ = x⁻¹)) →
          (C.D.B0 ⊔ C.D.K ⊔ Work.GW2.fittingIn B.U).relIndex B.U ≤ p := by
  intro G _ _ hbc B h2 C hplus h7 p P hp hPF hPcard hAlpha
  -- `B₀ ⊔ K = U ⊓ M` (§4 (5)), so the target index is `|U : (U ⊓ M) ⊔ F(U)|`.
  have hD : C.D.B0 ⊔ C.D.K ⊔ Work.GW2.fittingIn B.U
      = (B.U ⊓ C.D.M) ⊔ Work.GW2.fittingIn B.U := by
    rw [sup_comm C.D.B0 C.D.K, ← C.pre.U_eq]
  rw [hD]
  -- the `(p,p)`-subgroup `A`
  obtain ⟨A, hobj⟩ := Case2EightObjExists I G hbc B h2 C hplus h7 p P hp hPF hPcard
  have hAle : A ≤ C.D.F ⊔ C.D.K := hobj.2.2.2.1
  have hAcard : Nat.card ↥A = p ^ 2 := hobj.2.2.2.2.1
  have hAexp : ∀ x ∈ A, x ^ p = 1 := hobj.2.2.2.2.2.1
  have hPA : P ≤ A := hobj.2.2.2.2.2.2.1
  -- `P ≠ ⊥`
  have hpne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hPcard
    have := hp.two_le
    omega
  -- `N_U(P) = U ⊓ M` and `N_U(P) ≤ N_G(A)`
  have hNU : B.U ⊓ Subgroup.normalizer (P : Set G) = B.U ⊓ C.D.M :=
    Case2Eight_NU B C P hPF hpne
  have h4 : B.U ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (A : Set G) := by
    rw [hNU]; exact Case2Eight_le_normalizer_A I B C p P A hobj
  have hp0odd := Case2Eight_odd_p0 B p P A h4
  have h6a := Case2EightP0LeP1 B p P A hPA h4
  have hAcomm := Case2Eight_A_comm I B C A hAle
  have h6b := Case2EightP1Le p P A hp hPA hAcard hAexp hAcomm hPcard
  have hpodd : Odd p := by
    have h1 : p ∣ Nat.card ↥C.D.F := by rw [← hPcard]; exact Subgroup.card_dvd_of_le hPF
    exact Odd.of_dvd_nat B.U_odd (h1.trans (Subgroup.card_dvd_of_le (Case2Data.F_le_U B C.D)))
  have hp0lep := Case2Eight_p0_le_p B p P A hp0odd h6a h6b hpodd
  by_cases hUNA : B.U ≤ Subgroup.normalizer (A : Set G)
  · -- `U ≤ N_G(A)`: the index is at most `p₀`
    have hmono : ((B.U ⊓ C.D.M) ⊔ Work.GW2.fittingIn B.U).relIndex B.U
        ≤ (B.U ⊓ C.D.M).relIndex B.U := by
      refine Subgroup.relIndex_le_of_le_left le_sup_left ?_
      intro hzero
      have h := Subgroup.relIndex_mul_card (B.U ⊓ C.D.M) B.U
      rw [hzero, zero_mul] at h
      exact (Nat.card_pos (α := ↥B.U)).ne' h.symm
    have hp0eq : Work.GW2.Case2EightP0 B P A = (B.U ⊓ C.D.M).relIndex B.U := by
      show (B.U ⊓ Subgroup.normalizer (P : Set G)).relIndex
        (B.U ⊓ Subgroup.normalizer (A : Set G)) = (B.U ⊓ C.D.M).relIndex B.U
      rw [hNU, inf_eq_left.mpr hUNA]
    calc ((B.U ⊓ C.D.M) ⊔ Work.GW2.fittingIn B.U).relIndex B.U
        ≤ (B.U ⊓ C.D.M).relIndex B.U := hmono
      _ = Work.GW2.Case2EightP0 B P A := hp0eq.symm
      _ ≤ p := hp0lep
  · -- Bender's trichotomy
    rcases EightTrich9Holds I G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj hUNA with
      hinv | ⟨hAleQ, hQltA, hAltQ, hrelQA⟩
    · -- case 3: `s` inverts `Q`, so `U = (U ⊓ M) ⊔ F(U)`
      rw [← Case2EightCase3U9plus I G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj
            (Case2EightQfacts I G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj).2.2.2 hinv
            (hAlpha A hobj (Case2EightQfacts I G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj).2.2.2
              hinv),
        Subgroup.relIndex_self]
      exact le_of_lt (by have := hp.two_le; omega)
    · -- case 2: `N_U(A) = (U ⊓ M) ⊔ F(U)` and the index is `u ≤ p`
      have hu : Work.GW2.Case2EightU B A ≤ p :=
        EightN9U I G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj hAleQ hQltA hAltQ hrelQA
      have hNUA : B.U ⊓ Subgroup.normalizer (A : Set G)
          = (B.U ⊓ C.D.M) ⊔ Work.GW2.fittingIn B.U :=
        le_antisymm
          (EightN9Inf I G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj hAleQ hQltA hAltQ hrelQA)
          (Case2EightN9Sup I G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj
            hAleQ hQltA hAltQ hrelQA)
      rw [← hNUA]
      exact hu

end Work.CORE4
