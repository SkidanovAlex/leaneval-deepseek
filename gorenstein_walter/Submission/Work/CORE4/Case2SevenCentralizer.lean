import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2SevenAux
import Submission.Work.CORE4.SevenX.piFU_le_pi_K0F
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.SevenX.sevenX_le_centralizer_of_isNilpotent
import Submission.Work.CORE4.SevenX.sevenX_sup_K0_F_le_centralizer
import Submission.Work.CORE4.SevenX.sevenX_fittingIn_inf_centralizer_sup_le
import Submission.OddOrder.GroupTheory.FittingSelfCentralizing

namespace Work.CORE4

open Work.GW2 Subgroup

set_option linter.style.haveILetI false

variable {G : Type} [Group G] [Finite G]

/-- `A ≤ N_G(F(A))`: the Fitting subgroup of `A` is characteristic in `A`. -/
theorem le_normalizer_fittingIn (A : Subgroup G) :
    A ≤ Subgroup.normalizer (Work.GW2.fittingIn A : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (H := Work.GW2.fittingIn A) (K := A)
      (Subgroup.map_subtype_le (Work.GW2.fitting ↥A))).mp
    (fittingIn_subgroupOf_normal A)

/-- Bender 1.2 / P. Hall for a subgroup: for a finite solvable `A`, `C_A(F(A)) ≤ F(A)`.  This is
`OddOrder.GroupTheory.centralizer_fitting_le_fitting` applied in the group `↥A`, transported to the
ambient group via `SevenX.PiFU.fitting_eq_isaacsFitting`. -/
theorem sevenX_centralizer_fittingIn_inf_le_fittingIn {G : Type} [Group G] [Finite G]
    (A : Subgroup G) (hsol : Group.IsSolvable ↥A) :
    Subgroup.centralizer (Work.GW2.fittingIn A : Set G) ⊓ A ≤ Work.GW2.fittingIn A := by
  haveI : Group.IsSolvable ↥A := hsol
  have hF : Work.GW2.fitting ↥A = OddOrder.Isaacs.Ch01.fitting ↥A :=
    SevenX.PiFU.fitting_eq_isaacsFitting
  have hsc := OddOrder.GroupTheory.centralizer_fitting_le_fitting (G := ↥A)
  intro x hx
  obtain ⟨hxC, hxA⟩ := Subgroup.mem_inf.mp hx
  rw [Work.GW2.fittingIn]
  refine Subgroup.mem_map.mpr ⟨⟨x, hxA⟩, ?_, rfl⟩
  rw [hF]
  apply hsc
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyF : (y : G) ∈ Work.GW2.fittingIn A := by
    rw [Work.GW2.fittingIn]
    exact Subgroup.mem_map.mpr ⟨y, hF ▸ hy, rfl⟩
  have hcomm := (Subgroup.mem_centralizer_iff.mp hxC) (y : G) hyF
  exact Subtype.ext hcomm

/-- Bender 1981, §4 (7) (p. 225), the core conjunct: `π(C_U(K₀F)) = π = π(F(U))`, where
`K₀ = F(U) ⊓ K` and `F = B₀ ⊓ F(U)`, `C_U(K₀F) = B.U ⊓ C_G(K₀ ⊔ F)` and `π = B.piFU = π(F(U))`.

Route (Bender p. 225).  `K₀ ⊴ U ⊓ M` and `F ⊴ M`, so `(H ⊓ M)'` centralizes `K₀F`:

* `⊇`: `K₀ ≤ C_U(K₀F)` by definition and `F ≤ C(K)` (as `K ≤ E(M)` by `Case2PrePlus`'s (1) and
  `F ≤ C_G(E(M))`), so `K₀F ≤ C_U(K₀F)` and `π(K₀F) ⊆ π(C_U(K₀F))`; `SevenX.piFU_le_pi_K0F` gives
  `π(F(U)) ⊆ π(K₀F)`;
* `⊆`: a `π'`-subgroup of `H` centralizing `K₀F = N_{F(U)}(F)` (`Case2SevenAux.K1F_eq_normalizer`)
  lies in `C_H(F(U))` by `I.toolkit.c11iv`, hence in `M` (as `F(U) ≤ N_G(X)` for Bender's `X`),
  hence in `F(U) ⊓ M = K₀F` (`SixThree`), so it is trivial; a `π'`-part argument on the `π`-group
  `U` gives `π(C_U(K₀F)) ⊆ π`.

This is conjunct 3 of `Case2SevenFacts`; it does not by itself give the leaf `Case2SevenImpl`
(conjunct 2 `π(K₀) = π(F(U))` also needs Bender's (6)-witness `∃ g ∉ M, F^g ≤ F(U) ⊓ M`, available
in the workspace as `Submission.Work.CORE4.Case2SixEmbed`). -/
theorem Case2SevenCentralizer (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
        Work.GW2.Case2 B → Work.GW2.Case2PrePlus B C.D →
          Work.GW2.primesOf (B.U ⊓ Subgroup.centralizer
              (((C.D.K0 ⊔ C.D.F : Subgroup G)) : Set G)) = B.piFU := by
  intro G _ _ hbc B C hcase2 hplus
  obtain ⟨D, hpre, hFti, hFcyc⟩ := C
  set KF : Subgroup G := D.K0 ⊔ D.F with hKF
  have hSix : Work.GW2.fittingIn B.U ⊓ D.M = KF := by
    rw [hKF]; exact SixThree I G hbc B D hpre
  have hK0le : KF ≤ Work.GW2.fittingIn B.U := by
    rw [hKF]; exact sup_le inf_le_left (D.F_le_fitting B)
  apply le_antisymm
  · -- ⊆ : `π(C_U(K₀F)) ⊆ π`
    intro p hp
    rw [Work.GW2.primesOf] at hp
    obtain ⟨hpprime, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp
    show p ∈ Work.GW2.primesOf (Work.GW2.fittingIn B.U)
    rw [Work.GW2.primesOf]
    refine Nat.mem_primeFactors.mpr ⟨hpprime, ?_, Nat.card_pos.ne'⟩
    by_contra hndvd
    haveI : Fact p.Prime := ⟨hpprime⟩
    -- an element of order `p` in `R = U ⊓ C_G(K₀F)`
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(B.U ⊓ Subgroup.centralizer (KF : Set G))) p hpdvd
    set P : Subgroup G := Subgroup.zpowers ((x : G)) with hPdef
    have hxmem : (x : G) ∈ B.U ⊓ Subgroup.centralizer (KF : Set G) := x.2
    have hPU : P ≤ B.U := by
      rw [hPdef, Subgroup.zpowers_le]; exact hxmem.1
    have hPC : P ≤ Subgroup.centralizer (KF : Set G) := by
      rw [hPdef, Subgroup.zpowers_le]; exact hxmem.2
    have hord : orderOf ((x : G)) = p := by
      rw [Subgroup.orderOf_coe]; exact hxord
    have hPcard : Nat.card ↥P = p := by
      rw [hPdef, Nat.card_zpowers]; exact hord
    have hPgroup : IsPGroup p P := IsPGroup.of_card (by rw [hPcard, pow_one])
    have hKcop : Nat.Coprime p (Nat.card ↥(Work.GW2.fittingIn B.U)) :=
      hpprime.coprime_iff_not_dvd.mpr hndvd
    have hKN : P ≤ Subgroup.normalizer (Work.GW2.fittingIn B.U : Set G) :=
      le_trans hPU (le_normalizer_fittingIn B.U)
    have hKsc : Work.GW2.fittingIn B.U ⊓ Subgroup.centralizer (KF : Set G) ≤ KF :=
      SevenX.sevenX_fittingIn_inf_centralizer_sup_le B D hpre hSix
    -- `P` centralizes the nilpotent `F(U)`
    have hcen := SevenX.sevenX_le_centralizer_of_isNilpotent I.toolkit.c11iv (Work.GW2.fittingIn B.U) KF P
      (SevenX.PiFU.isNilpotent_fittingIn B.U) hK0le hKsc hpprime hPgroup hKcop hKN hPC
    -- `U` is solvable (odd order, Feit–Thompson), so `C_U(F(U)) ≤ F(U)` (Bender 1.2)
    have hsolv : Group.IsSolvable ↥B.U := I.toolkit.ft ↥B.U B.U_odd
    have hle : P ≤ Work.GW2.fittingIn B.U := fun y hy =>
      sevenX_centralizer_fittingIn_inf_le_fittingIn B.U hsolv ⟨hcen hy, hPU hy⟩
    exact hndvd (dvd_trans (by rw [hPcard]) (Subgroup.card_dvd_of_le hle))
  · -- ⊇ : `π ⊆ π(C_U(K₀F))`
    intro p hp
    have hp' : p ∈ Work.GW2.primesOf (D.K0 ⊔ D.F) :=
      SevenX.piFU_le_pi_K0F I G hbc B hcase2 D hpre hp
    refine SevenX.PiFU.primesOf_mono ?_ hp'
    refine le_inf ?_ ?_
    · exact le_trans hK0le (Subgroup.map_subtype_le (Work.GW2.fitting ↥B.U))
    · exact SevenX.sevenX_sup_K0_F_le_centralizer I B D hpre hFcyc

end Work.CORE4
