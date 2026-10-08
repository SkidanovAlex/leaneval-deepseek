import Mathlib
import Submission.Work.CORE4.NotA7Defs
import Submission.Work.CORE4.NotA7.A3UU3
import Submission.Work.CORE4.NotA7.A3UOddCore
import Submission.Work.CORE4.NotA7.A3UBound
import Submission.Work.CORE4.fittingIn_eq_self_of_isPGroup

namespace Work.CORE4.NotA7

open Work.GW2 Subgroup

set_option linter.style.haveILetI false

-- LEAF C10.A3' — `A7Facts3` minus the contested `K = Z(U)` conjunct.  This is the corrected
-- interface of `Submission/Work/CORE4/NotA7Defs.lean` (`Work.CORE4.A7UData` = `IsPGroup 3 B.U ∧
-- C.D.B0 = C.D.F ∧ oddCoreIn C.D.M = C.D.F ∧ ∀ X ≤ C.D.M, Odd |X| → |X| ≤ 21 * |X ⊓ C.D.F|`),
-- which every later leaf of the `A₇` chain of Bender 1981 §4, p. 226 actually uses.  The circle
-- documented in `CORE4/A7U.lean` ("Verdict": `K = Z(U)` needs `|U : U ∩ M| = 3`, which comes from
-- (8) only after the exceptional case `I_U(s) ⊴ Ĥ` is excluded, and A4 was designed to consume
-- `K = Z(U)`) is broken by the `NotA7Defs` module docstring and by design pass 15: A4 needs only
-- `K ⊴ U ⊴ Ĥ`, and in the exceptional case `K = Z(U)` is proved directly (leaf A4a).
-- Route (Bender p. 226: "by (7) and (8), U is a 3-group. Then O(M) = B = F"):
-- * |U : B₀ ⊔ K ⊔ F(U)| ≤ p = 3 (the `I`-free conjunct of Case2EightFacts); B₀ is a 3-group
--   (B₀ ≤ C_U(K₀F), whose prime set is `B.piFU = {3}` by Case2SevenFacts 3 and A7Facts1), K is a
--   3-group (|K| = 3, A7Facts1), and F(U) is a 3-group (Case2SevenFacts 2 with |K₀| = 3), so U is
--   a 3-group; then F(U) = U;
-- * oddCoreIn M ≤ C_U(E) ≤ C_U(K₀F) is a 3-group, and F ≤ oddCoreIn M (F ≤ C(E), F ≤ F(U)) with
--   |F| = 3, so oddCoreIn M = F = B₀;
-- * M/F ≅ A₇ (M = E·C_M(t), C_M(t) = K F (S ⊓ M), E ⊓ F = Z(E)), so an odd X ≤ M has
--   |X : X ⊓ F| ≤ 21 (`I.toolkit.a7`, clause 4), giving |X| ≤ 21|X ⊓ F|.
-- Useful already-proved helpers in the area: `SixThree` (`F(U) ⊓ M = K₀ ⊔ F`), `A7CMtFourGroup`,
-- `Case2Seven`/`Case2SevenAux`, `CountSetup` (`M = E·C_M(t)`), `LayerCtx6`,
-- `Case2LayerOneInvClass`, `SevenX.piFU_le_pi_K0F`, `A7S4`.
-- IMPORTANT: import ONLY modules that do not declare clashing `Work.GW2.*` names:
-- `Submission.Work.CORE4.*`, `Submission.Work.FUS.*`, `Submission.Work.RED.*`,
-- `Submission.Work.Dihedral.Defs`, `Submission.OddOrder.*`.

/-! ## A pure group-theoretic helper

The conjugation action of the normalizer of a subgroup `K` of order `3` on `K` is a homomorphism
into `MulAut ↥K`, whose order is `Nat.totient 3 = 2` (`IsCyclic.card_mulAut`).  An odd-order
subgroup `H ≤ N_G(K)` therefore acts trivially: the image has order dividing both `|H|` (odd) and
`2`.  This is the step that makes `B₀ = C_{U⊓M}(s)` (of odd order, normalizing the two subgroups
`K` and `F` of order `3`) centralize them, hence lie in the `3`-group `C_U(K₀F)`. -/
theorem A3UMinus_aux_centralizer_of_card_three {G : Type} [Group G] [Finite G]
    {H K : Subgroup G} (hK : Nat.card ↥K = 3)
    (hN : H ≤ Subgroup.normalizer (K : Set G)) (hodd : Odd (Nat.card ↥H)) :
    H ≤ Subgroup.centralizer (K : Set G) := by
  intro x hx
  haveI : IsCyclic ↥K := isCyclic_of_prime_card hK
  have hcardAut : Nat.card (MulAut ↥K) = 2 := by
    rw [IsCyclic.card_mulAut, hK, Nat.totient_prime Nat.prime_three]
  have hmemN : x ∈ Subgroup.normalizer (K : Set G) := hN hx
  -- it suffices that the conjugation map `N_G(K) →* MulAut ↥K` kills `x`
  have hφx : (Subgroup.normalizerMonoidHom K) ⟨x, hmemN⟩ = 1 := by
    have h2 : orderOf ((Subgroup.normalizerMonoidHom K) ⟨x, hmemN⟩) ∣ 2 := by
      have := Subgroup.orderOf_dvd_natCard (⊤ : Subgroup (MulAut ↥K))
        (Subgroup.mem_top ((Subgroup.normalizerMonoidHom K) ⟨x, hmemN⟩))
      rw [Subgroup.card_top, hcardAut] at this
      exact this
    have h1 : orderOf ((Subgroup.normalizerMonoidHom K) ⟨x, hmemN⟩) ∣ orderOf x := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow]
      have hpow : (⟨x, hmemN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ orderOf x = 1 := by
        rw [← Subgroup.orderOf_mk x hmemN, pow_orderOf_eq_one]
      rw [hpow, map_one]
    have h3 : orderOf ((Subgroup.normalizerMonoidHom K) ⟨x, hmemN⟩) ∣ Nat.card ↥H :=
      h1.trans (Subgroup.orderOf_dvd_natCard H hx)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h ▸ h3))
  have hker : (⟨x, hmemN⟩ : Subgroup.normalizer (K : Set G)) ∈
      (Subgroup.normalizerMonoidHom K).ker :=
    MonoidHom.mem_ker.mpr hφx
  rw [Subgroup.normalizerMonoidHom_ker] at hker
  exact Subgroup.mem_subgroupOf.mp hker

/-- The three mathematical pieces of `A7UData`, proved in the sibling modules
`A3UU3` (`U` is a `3`-group), `A3UOddCore` (`O(M) = F`) and `A3UBound` (the `21`-bound), together
with the two steps that glue them: `B₀ = F` follows from `F(U) = U` for the `3`-group `U`
(`fittingIn_eq_self_of_isPGroup`), and `A3UMinus` is their conjunction. -/
theorem A3UMinus (I : Work.GW2.C4Inputs) : ∀ (G : Type) [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
    Work.GW2.Hyp9 G B C → Work.GW2.IsA7Case C.D → Work.GW2.A7Facts1 C.D →
      Work.GW2.A7Facts2 B C.D → Work.CORE4.A7UData B C.D := by
  intro G _ _ B C hHyp hA7 h1F h2F
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  -- (1) `U = O(H)` is a `3`-group (Bender: "by (7) and (8), `U` is a 3-group")
  have hU3 : IsPGroup 3 B.U := A3UU3 I G B C hHyp h1F
  -- (2) `B₀ = F`: `F = B₀ ⊓ F(U)` and `F(U) = U` for the `3`-group `U`
  have hB0F : C.D.B0 = C.D.F := by
    have hfit : Work.GW2.fittingIn B.U = B.U := fittingIn_eq_self_of_isPGroup hU3
    rw [C.D.F_def, hfit, inf_eq_left.mpr (le_trans (C.D.B0_le B) inf_le_left)]
  -- (3) `O(M) = F` (Bender: "Then `O(M) = B = F`")
  have hcore : Work.GW2.oddCoreIn C.D.M = C.D.F :=
    A3UOddCore I G B C hHyp hA7 h1F h2F hU3
  -- (4) `M/F ≅ A₇`, so odd `X ≤ M` has `|X| ≤ 21 · |X ⊓ F|`
  exact ⟨hU3, hB0F, hcore, A3UBound I G B C hHyp hA7 h1F h2F hU3 hcore⟩

end Work.CORE4.NotA7
