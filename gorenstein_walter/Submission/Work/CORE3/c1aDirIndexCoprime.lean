import Mathlib
import Submission.Work.CORE3.Case1aThmCInputs
import Submission.Work.CORE3.SylowFromLocalControl
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.relIndex_of_factorization_eq
import Submission.Work.CORE3.H_eq_U_sup_S
import Submission.Work.CORE3.Case1aPpart

/-!
# `(|F_{3'}(U)|, |G : H|) = 1` in Bender 1981 §3, subcase `Ĥ = H`

Bender's Theorem C application (`Work.CORE3.Case1aThmCInputsProp`) needs the coprimality
`(|K|, |G : H|) = 1` for `K = F_{3'}(U) ∩ F(U) = F_{3'}(U)`, and the design
(`NOTES_LEAD_gw_design4.md` §1) routes it through `SylowFromLocalControlProp`:

for a prime `r ∣ |F_{3'}(U)|` the subgroup `R := O_r(F(U))` is, on the one hand, locally
controlled (`N_G(X) ≤ H` for every `1 ≠ X ≤ R`, since `R ≤ F(U)` and `Case1`), and on the other
hand a Sylow `r`-subgroup of `H`.  Hence `R` is a Sylow `r`-subgroup of `G` and `r ∤ |G : R|`,
whence `r ∤ |G : H|` because `H.index ∣ R.index`.

`O_r(F(U))` is a Sylow subgroup of `H = U ⋊ S` (`H/U` is a `2`-group, `r` odd) as soon as it is
a Sylow subgroup of `U`, and `U = F(U) · C_U(S)` with `r ∤ |C_U(S)|` (the hypothesis) gives for
the cardinality of the Sylow part

`[U : O_r(F(U))] · |F(U) ⊓ C_U(S)| = [F(U) : O_r(F(U))] · |C_U(S)|`,

the cardinality shadow of the second isomorphism theorem
(`Work.CORE3.card_sup_mul_card_inf_of_le_normalizer`).  Both factors on the right are prime to
`r`: `[F(U) : O_r(F(U))]` because `F(U)` is nilpotent
(`Work.CORE3.not_dvd_relIndex_pCoreIn_fittingIn`) and `|C_U(S)|` by hypothesis.  This is the
content of `not_dvd_relIndex_pCoreIn_sup_of_not_dvd_card` below.
-/

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- **The Sylow `r`-subgroup of `F` is Sylow in `F ⊔ C` when `r ∤ |C|`.**

If `F` is finite nilpotent (as a subgroup of `G`), `C ≤ N_G(F)` and `r ∤ |C|`, then `O_r(F)` has
`r`-prime index in `F ⊔ C`: the quotient `(F ⊔ C)/F ≅ C/(C ⊓ F)` has order dividing `|C|`, so
`O_r(F)` carries the full `r`-part of `|F ⊔ C|`. -/
theorem not_dvd_relIndex_pCoreIn_sup_of_not_dvd_card {G : Type} [Group G] [Finite G]
    (F C : Subgroup G) [Group.IsNilpotent ↥F]
    (hC : C ≤ Subgroup.normalizer (F : Set G))
    (r : ℕ) [Fact r.Prime] (hrC : ¬ r ∣ Nat.card ↥C) :
    ¬ r ∣ (pCoreIn r F).relIndex (F ⊔ C) := by
  have hr : Nat.Prime r := Fact.out
  -- `[F ⊔ C : F] · |F ⊓ C| = |C|`, so `r ∤ [F ⊔ C : F]`.
  have hnotF : ¬ r ∣ F.relIndex (F ⊔ C) := by
    have h1 : F.relIndex (F ⊔ C) * Nat.card ↥F = Nat.card ↥(F ⊔ C) := by
      have h := Subgroup.relIndex_mul_card (H := F) (K := F ⊔ C)
      rwa [inf_of_le_left le_sup_left] at h
    have h2 : Nat.card ↥(F ⊔ C) * Nat.card ↥(F ⊓ C) = Nat.card ↥F * Nat.card ↥C :=
      card_sup_mul_card_inf_of_le_normalizer hC
    have h3 : F.relIndex (F ⊔ C) * Nat.card ↥(F ⊓ C) = Nat.card ↥C := by
      refine Nat.mul_left_cancel (Nat.card_pos (α := ↥F)) ?_
      calc Nat.card ↥F * (F.relIndex (F ⊔ C) * Nat.card ↥(F ⊓ C))
          = (F.relIndex (F ⊔ C) * Nat.card ↥F) * Nat.card ↥(F ⊓ C) := by ring
        _ = Nat.card ↥(F ⊔ C) * Nat.card ↥(F ⊓ C) := by rw [h1]
        _ = Nat.card ↥F * Nat.card ↥C := h2
    intro hdvd
    exact hrC (h3 ▸ dvd_mul_of_dvd_left hdvd _)
  -- `O_r(F)` is Sylow in `F`, hence also in `F ⊔ C`.
  intro hdvd
  rw [← Subgroup.relIndex_mul_relIndex (H := pCoreIn r F) (K := F) (L := F ⊔ C)
    (c1aPcoreIn_le_self r F) le_sup_left] at hdvd
  rcases hr.dvd_mul.mp hdvd with h | h
  · exact absurd h (not_dvd_relIndex_pCoreIn_self F r)
  · exact hnotF h

theorem c1aDirIndexCoprime (I : Work.CORE3.Case1Inputs) (hFr : Work.GW2.Case1aFrattiniProp)
    (hAb : Work.GW2.Case1aAbelianProp) (hA7 : Work.GW2.Case1aA7Prop)
    (hBpf : Work.CORE3.Case1aBFpfProp) (hMD : Work.CORE3.Case1aMDataProp)
    (hDir : Work.CORE3.Case1aDirectProp) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G, Work.GW2.Case1 B → B.Hhat = B.H →
      (∀ r : ℕ, Nat.Prime r → r ∣ Nat.card (Work.GW2.fittingPiIn ({3}ᶜ) B.U) →
        ¬ r ∣ Nat.card (B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) : Subgroup G)) →
      Nat.Coprime (Nat.card (Work.GW2.fittingPiIn ({3}ᶜ) B.U ⊓ Work.GW2.fittingIn B.U : Subgroup G))
        B.H.index := by
  intro G _instG _finG hFT hCtx B hCase1 hHhat hBc
  classical
  set C : Subgroup G := B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) with hCdef
  set F : Subgroup G := Work.GW2.fittingIn B.U with hFdef
  set F3 : Subgroup G := Work.GW2.fittingPiIn ({3}ᶜ) B.U with hF3def
  -- A prime common divisor of the two orders contradicts the local-control argument.
  by_contra hnc
  obtain ⟨r, hr, hrA, hrH⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  haveI : Fact (Nat.Prime r) := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- ## Inclusions and divisibility facts
  have hF3leF : F3 ≤ F := by
    rw [hF3def, hFdef]
    exact bfpf_fittingPiIn_le_fittingIn _ _
  have hFleU : F ≤ B.U := by rw [hFdef]; exact c1aFittingIn_le B.U
  have hUleH : B.U ≤ B.H := Work.CORE2A.bSetup_U_le_H B
  have hrF3 : r ∣ Nat.card ↥F3 := hrA.trans (Subgroup.card_dvd_of_le inf_le_left)
  have hrF : r ∣ Nat.card ↥F := hrA.trans (Subgroup.card_dvd_of_le inf_le_right)
  have hrC : ¬ r ∣ Nat.card ↥C := hBc r hr hrF3
  have hrU : r ∣ Nat.card ↥B.U := hrF3.trans (Subgroup.card_dvd_of_le (hF3leF.trans hFleU))
  -- `F(U)` is nilpotent (it is the Fitting subgroup of `U`).
  haveI hFnil : Group.IsNilpotent ↥F := by
    rw [hFdef, Work.GW2.fittingIn, Work.CORE2A.fitting_eq_isaacsFitting]
    exact (Group.isNilpotent_congr (Subgroup.equivMapOfInjective
      (OddOrder.Isaacs.Ch01.fitting ↥B.U) B.U.subtype B.U.subtype_injective)).mp
      OddOrder.Isaacs.Ch01.fitting.isNilpotent
  -- `r` is odd, since `|U|` is odd: `U = O(H)`.
  have hr2 : r ≠ 2 := by
    intro h2
    exact (Nat.not_even_iff_odd.mpr (Work.CORE2A.bSetup_U_odd B))
      (even_iff_two_dvd.mpr (h2 ▸ hrU))
  -- ## Normalizers, and `U ⊔ S = H`
  have hHnormU : B.H ≤ Subgroup.normalizer (B.U : Set G) :=
    le_normalizer_map_subtype_of_normal' (K := B.H) (N := Work.GW2.oddCore ↥B.H) inferInstance
  have hSnormU : (B.S : Subgroup G) ≤ Subgroup.normalizer (B.U : Set G) :=
    (Work.CORE2A.bSetup_S_le_H B).trans hHnormU
  have hUnormF : B.U ≤ Subgroup.normalizer (F : Set G) := by
    rw [hFdef, Work.GW2.fittingIn, Work.CORE2A.fitting_eq_isaacsFitting]
    exact le_normalizer_map_subtype_of_normal' (N := OddOrder.Isaacs.Ch01.fitting ↥B.U)
      (OddOrder.Isaacs.Ch01.fitting.normal ↥B.U)
  have hCnormF : C ≤ Subgroup.normalizer (F : Set G) := inf_le_left.trans hUnormF
  have hUeq : B.U = F ⊔ C := by
    rw [hFdef, hCdef]
    exact c1aU_eq_fitting_sup_B I G hFT hCtx B hCase1
  have hcardH : Nat.card ↥B.H = Nat.card ↥B.U * Nat.card ↥(B.S : Subgroup G) := by
    rw [← H_eq_U_sup_S G I.T hCtx B]
    exact Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot hSnormU
      (Work.CORE2A.inf_U_S_eq_bot B)
  -- `|H : U| = |S|` is a power of two, hence prime to `r`.
  have hHU : B.U.relIndex B.H = Nat.card ↥(B.S : Subgroup G) := by
    have h := Subgroup.relIndex_mul_card (H := B.U) (K := B.H)
    rw [inf_of_le_left hUleH, hcardH] at h
    exact Nat.mul_right_cancel (Nat.card_pos (α := ↥B.U)) (h.trans (mul_comm _ _))
  have hnotdvdHU : ¬ r ∣ B.U.relIndex B.H := by
    rw [hHU]
    intro h
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp B.S.isPGroup'
    rw [hk] at h
    rcases (Nat.dvd_prime Nat.prime_two).mp (hr.dvd_of_dvd_pow h) with h1 | h1
    · exact hr.ne_one h1
    · exact hr2 h1
  -- ## The subgroup `R = O_r(F(U))` is locally controlled
  set R : Subgroup G := Work.GW2.pCoreIn r F with hRdef
  have hRF : R ≤ F := by rw [hRdef]; exact c1aPcoreIn_le_self r F
  have hRU : R ≤ B.U := hRF.trans hFleU
  have hRH : R ≤ B.H := hRU.trans hUleH
  have hpR : IsPGroup r R := by rw [hRdef]; exact c1aIsPGroup_pCoreIn r F
  have hRne : R ≠ ⊥ := by
    intro hbot
    have hnotdvd : ¬ r ∣ R.relIndex F := by
      rw [hRdef]
      exact not_dvd_relIndex_pCoreIn_self F r
    refine hnotdvd ?_
    have hcardR : Nat.card ↥R = 1 := by rw [hbot, Subgroup.card_bot]
    have h := Subgroup.relIndex_mul_card (H := R) (K := F)
    rw [inf_of_le_left hRF, hcardR, mul_one] at h
    rw [h]
    exact hrF
  have hN : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ R → Subgroup.normalizer (X : Set G) ≤ B.H := by
    intro X hXne hXR
    have hXF : X ≤ F := hXR.trans hRF
    have h := hCase1.2 X hXne (show X ≤ Work.GW2.fittingIn B.U from hXF)
    rwa [hHhat] at h
  -- ## `R` is a Sylow `r`-subgroup of `H`
  have hrel : ¬ r ∣ R.relIndex B.H := by
    have hrelU : ¬ r ∣ R.relIndex B.U := by
      have heq : R.relIndex B.U = R.relIndex (F ⊔ C) := by rw [hUeq]
      rw [heq, hRdef]
      exact not_dvd_relIndex_pCoreIn_sup_of_not_dvd_card F C hCnormF r hrC
    have hprod : R.relIndex B.H = R.relIndex B.U * B.U.relIndex B.H :=
      (Subgroup.relIndex_mul_relIndex (H := R) (K := B.U) (L := B.H) hRU hUleH).symm
    rw [hprod]
    intro h
    rcases hr.dvd_mul.mp h with h1 | h1
    · exact hrelU h1
    · exact hnotdvdHU h1
  -- ## Sylow in `G`, and `H.index ∣ R.index`
  exact absurd (hrH.trans (Subgroup.index_dvd_of_le hRH))
    (SylowFromLocalControl G r B.H R hRH hRne hpR hrel hN)

end Work.CORE3
