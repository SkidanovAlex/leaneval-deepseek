import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2PrePlusOfCtx
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2SevenAux
import Submission.Work.CORE4.SevenX.piFU_le_pi_K0F
import Submission.Work.CORE4.Case2K1_ne_bot
import Submission.Work.CORE4.Case2SevenCentralizer
import Submission.Work.CORE4.SevenO2HM
import Submission.Work.CORE4.SevenX.sevenX_le_centralizer_of_isNilpotent
import Submission.Work.CORE4.SevenX.sevenX_fittingIn_inf_centralizer_sup_le
import Submission.Work.CORE4.SevenRemain.pCore_ne_bot_of_isNilpotent_of_dvd
import Submission.Work.CORE4.SevenRemain.fittingIn_M_le_and_odd
import Submission.Work.CORE4.SevenRemain.odd_le_U_inf_M
import Submission.Work.CORE4.SevenRemain.fittingIn_M_pi_subset

namespace Work.CORE4

open Subgroup

/-- `C(A) ⊓ C(B) ≤ C(A ⊔ B)`.  (Conjugating a product multiplies the conjugates, so an element
centralizing `A` and `B` separately centralizes every product.) -/
theorem centralizer_inf_le_centralizer_sup {G : Type} [Group G] (A Bc : Subgroup G) :
    Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (Bc : Set G) ≤
      Subgroup.centralizer (((A ⊔ Bc : Subgroup G)) : Set G) := by
  refine Subgroup.le_centralizer_iff.mpr ?_
  refine sup_le ?_ ?_
  · exact Subgroup.le_centralizer_iff.mpr inf_le_left
  · exact Subgroup.le_centralizer_iff.mpr inf_le_right

/-- `K` centralizes `K₀ ⊔ F`: `K₀ ≤ K` and `K` is cyclic (hence abelian) by §4 (1), while
`K ≤ E(M)` and `F ≤ C_G(E(M))` by §4 (4)/(5). -/
theorem Case2Data.K_le_centralizer_K0supF {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} (h : Work.GW2.Case2Ctx B) :
    h.D.K ≤ Subgroup.centralizer (((h.D.K0 ⊔ h.D.F : Subgroup G)) : Set G) := by
  have hcyc : IsCyclic ↥h.D.K := Work.GW2.Case2Pre.K_cyclic B h.D h.pre
  have hKleCK : h.D.K ≤ Subgroup.centralizer ((h.D.K : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr IsCyclic.isMulCommutative
  have hCKleCK0 : Subgroup.centralizer ((h.D.K : Subgroup G) : Set G) ≤
      Subgroup.centralizer ((h.D.K0 : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (inf_le_right : h.D.K0 ≤ h.D.K)
  have hKleCF : h.D.K ≤ Subgroup.centralizer ((h.D.F : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact ((Subgroup.mem_centralizer_iff.mp
      (Work.GW2.Case2Pre.F_cent B h.D h.pre hf)) k (K_le_layerIn B h hk)).symm
  exact (le_inf (hKleCK.trans hCKleCK0) hKleCF).trans
    (centralizer_inf_le_centralizer_sup h.D.K0 h.D.F)

/-- Bender 1981, §4 (7) (p. 225) at the `Case2Ctx` level, given the centralizer conjunct
(`Work.CORE4.Case2SevenCentralizer`): the remaining conjuncts

* `O₂(H ⊓ M) = O₂(H)`;
* `π(K₀) ⊆ π` (`= π(F(U))`), and `π(K) ⊆ π` — note `K₀ ⊆ K`, so the first is a consequence of the
  second; the *equality* `π(K₀) = π` needs in addition Bender's (6)-witness
  (`Submission.Work.CORE4.Case2SixEmbed`);
* `π(F(M)) ⊆ π`.

Hypotheses: `BenderCtx G`, `B : BenderSetup G`, `h : Case2Ctx B` (so §4 (9)'s `S ≤ E(M) ≤ M` and
Bender's `X` are available as fields of `h.D`), and the equality `π(C_U(K₀F)) = π`.

Route.  `Case2PrePlusOfCtx` gives Bender's (1),(2) for this `B`; from (1), `K = [S ⊓ E(M), U ⊓ M]`
with `S ⊓ M = S`, so `K ⊴ H ⊓ M` (both `S` and `U ⊓ M` normalise the commutator inside
`H ⊓ M = (U ⊓ M) ⊔ S`).

* `π(K) ⊆ π`: `K ⊴ H ⊓ M` and `K ≤ U`, so `K ≤ (H ⊓ M)' ∩ U ≤ C_U(K₀F)` (as `(H ⊓ M)'` centralizes
  `K₀F = N_{F(U)}(F)`), and the hypothesis gives `π(C_U(K₀F)) = π`.
* `π(F(M)) ⊆ π`: `F(M)` is odd, and `M = E(M)·C_M(t)` gives `F(M) ≤ C_M(E(M)) ≤ H ⊓ M`, whence
  `F(M) ≤ O(H ⊓ M) = U ⊓ M`; its `π'`-part centralizes `K₀F`, hence lies in the `π`-group
  `C_U(K₀F)`.
* `O₂(H ⊓ M) = O₂(H)`: with `S ≤ M`, `S ⊓ M = S` is a Sylow 2-subgroup of `M`, and
  `O₂(H ⊓ M) ≥ S ∩ H = S`; a normal 2-subgroup of `H ⊓ M` lies in `S`, and `S ≤ H ⊓ M` with
  `H ⊓ M = (U ⊓ M) ⊔ S` normalises `S ∩ H = S`, giving `O₂(H ⊓ M) = S = O₂(H)` (using
  `h.H_eq_U_sup_S`, `h.S_le_M`, `Case2KB0`). -/
theorem Case2SevenRemainingOfCtx (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        Work.GW2.primesOf (B.U ⊓ Subgroup.centralizer
            (((Work.GW2.Case2Data.K0 h.D ⊔ h.D.F : Subgroup G)) : Set G)) = B.piFU →
          Work.GW2.pCoreIn 2 (B.H ⊓ h.D.M) = Work.GW2.pCoreIn 2 B.H ∧
          Work.GW2.primesOf (Work.GW2.Case2Data.K0 h.D) ⊆ B.piFU ∧
          Work.GW2.primesOf h.D.K ⊆ B.piFU ∧
          Work.GW2.primesOf (Work.GW2.fittingIn h.D.M) ⊆ B.piFU := by
  intro G _ _ hbc B h hC
  refine ⟨SevenO2HM I G hbc B h, ?_, ?_, ?_⟩
  · -- `π(K₀) ⊆ π`: `K₀ = F(U) ⊓ K ≤ F(U)`.
    exact Work.CORE4.SevenX.PiFU.primesOf_mono
      (inf_le_left : Work.GW2.Case2Data.K0 h.D ≤ Work.GW2.fittingIn B.U)
  · -- `π(K) ⊆ π`: `K ≤ U ⊓ C_G(K₀ ⊔ F)`.
    have hKle : h.D.K ≤ B.U ⊓ Subgroup.centralizer
        (((h.D.K0 ⊔ h.D.F : Subgroup G)) : Set G) :=
      le_inf (Work.GW2.Case2Data.K_le_U B h.D) (Case2Data.K_le_centralizer_K0supF h)
    exact (Work.CORE4.SevenX.PiFU.primesOf_mono hKle).trans (le_of_eq hC)
  · -- `π(F(M)) ⊆ π`.
    obtain ⟨hFMleHM, hFM2⟩ := Work.CORE4.SevenRemain.fittingIn_M_le_and_odd I G hbc B h
    have hFModd : Odd (Nat.card ↥(Work.GW2.fittingIn h.D.M)) :=
      Nat.not_even_iff_odd.mp (by rw [even_iff_two_dvd]; exact hFM2)
    have hFMleUM : Work.GW2.fittingIn h.D.M ≤ B.U ⊓ h.D.M :=
      Work.CORE4.SevenRemain.odd_le_U_inf_M I G hbc B h _ hFMleHM hFModd
    refine Work.CORE4.SevenRemain.fittingIn_M_pi_subset I G hbc B h hFMleUM ?_
    intro p hp hpdvd
    haveI : Fact p.Prime := ⟨hp⟩
    exact Work.CORE4.SevenRemain.pCore_ne_bot_of_isNilpotent_of_dvd G p (Work.GW2.fittingIn h.D.M)
      (Work.CORE4.SevenX.PiFU.isNilpotent_fittingIn h.D.M) hpdvd

end Work.CORE4
