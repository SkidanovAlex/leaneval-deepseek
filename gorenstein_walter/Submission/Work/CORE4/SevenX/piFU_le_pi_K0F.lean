import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2Seven
import Submission.OddOrder.Isaacs.Ch01_Sylow.Basic

namespace Work.CORE4.SevenX

open Work.GW2 Subgroup

set_option linter.style.haveILetI false

/-!
# §4 (7), the `X`-argument: `π(F(U)) ⊆ π(K₀F)`

Bender 1981, §4 (7) (p. 225) contains the chain

  `π(K F(M) [S∩M, B]) = π(C_U(K₀F)) = π = π(K₀)`,   `π := π(F(U))`,  `K₀ := F(U) ∩ K`,

and the first ingredient of `π = π(K₀)` is the *`X`-argument*: every prime dividing `|F(U)|`
already divides `|F(U) ∩ M| = |K₀F|`.  Its proof uses only the data `Case2Data`/`Case2Pre`, the
subgroup `X` (with `X ≤ F(U)` and `N_G(X) ≤ M`), and the fact that the Fitting subgroup is
nilpotent:

> for a prime `r ∤ |K₀F|`, take `y ∈ F(U)` of order `r` (Cauchy's theorem) and `x ∈ X`; then
> `X ≤ F(U) ∩ M = K₀F`, so `r ∤ orderOf x`, and in the nilpotent group `F(U)` the elements `x`
> and `y` (coprime orders) commute.  Hence `y ∈ C_G(X) ≤ N_G(X) ≤ M`, so
> `y ∈ F(U) ∩ M = K₀F`, contradicting `r ∤ |K₀F|`.

The auxiliary lemmas established here (in the sub-namespace `PiFU`)

* `PiFU.primesOf_mono` — `π` is monotone in the subgroup;
* `PiFU.fitting_eq_isaacsFitting`, `PiFU.isNilpotent_fitting`, `PiFU.isNilpotent_fittingIn` —
  Fitting's theorem in this area's vocabulary (`Work.GW2.fitting` is the odd-order library's
  Fitting subgroup, hence nilpotent), the one piece of group theory not already available here;
* `piFU_le_pi_K0F` — the target inclusion.
-/

namespace PiFU

variable {G : Type*} [Group G] [Finite G]

/-- `π` is monotone in the subgroup: `A ≤ B → π(A) ⊆ π(B)`. -/
theorem primesOf_mono {A B : Subgroup G} (h : A ≤ B) :
    Work.GW2.primesOf A ⊆ Work.GW2.primesOf B := by
  intro p hp
  rw [Work.GW2.primesOf] at hp ⊢
  exact Nat.mem_primeFactors.mpr
    ⟨(Nat.mem_primeFactors.mp hp).1,
      (Nat.mem_primeFactors.mp hp).2.1.trans (Subgroup.card_dvd_of_le h), Nat.card_pos.ne'⟩

/-- `Work.GW2.fitting G` (the normal core of the join of the normal nilpotent subgroups) is the
odd-order library's Fitting subgroup `OddOrder.Isaacs.Ch01.fitting G` (the join of the
`O_p(G)`).  Every normal nilpotent subgroup lies in the latter
(`OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting`), and the latter is itself normal and
nilpotent, so it is the greatest member of the indexing family; as it is normal, the
`normalCore` wrapper is the identity. -/
theorem fitting_eq_isaacsFitting : Work.GW2.fitting G = OddOrder.Isaacs.Ch01.fitting G := by
  have hS : sSup {N : Subgroup G | N.Normal ∧ Group.IsNilpotent N}
      = OddOrder.Isaacs.Ch01.fitting G := by
    refine le_antisymm (sSup_le ?_) (le_sSup ?_)
    · rintro N ⟨hN, hnil⟩
      haveI : N.Normal := hN
      haveI : Group.IsNilpotent ↥N := hnil
      exact OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
    · exact ⟨OddOrder.Isaacs.Ch01.fitting.normal G,
        OddOrder.Isaacs.Ch01.fitting.isNilpotent⟩
  rw [Work.GW2.fitting, hS]
  exact Subgroup.normalCore_eq_self _

/-- The Fitting subgroup (in this area's vocabulary) is nilpotent — Fitting's theorem. -/
theorem isNilpotent_fitting : Group.IsNilpotent ↥(Work.GW2.fitting G) := by
  rw [fitting_eq_isaacsFitting]
  exact OddOrder.Isaacs.Ch01.fitting.isNilpotent

/-- `F(A)` (in this area's vocabulary) is nilpotent. -/
theorem isNilpotent_fittingIn (A : Subgroup G) : Group.IsNilpotent ↥(Work.GW2.fittingIn A) := by
  haveI : Group.IsNilpotent ↥(Work.GW2.fitting ↥A) := isNilpotent_fitting
  rw [show Work.GW2.fittingIn A = (Work.GW2.fitting ↥A).map A.subtype from rfl]
  exact (Group.isNilpotent_congr (Subgroup.equivMapOfInjective (Work.GW2.fitting ↥A)
    A.subtype A.subtype_injective)).mp inferInstance

end PiFU

/-! ## The target -/

theorem piFU_le_pi_K0F (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case2 B → ∀ D : Work.GW2.Case2Data B, Work.GW2.Case2Pre B D →
        Work.GW2.primesOf (Work.GW2.fittingIn B.U) ⊆ Work.GW2.primesOf (D.K0 ⊔ D.F) := by
  intro G _ _ hbc B _hcase2 D hpre r hr
  -- Bender §4 (3): `F(U) ∩ M = K₀ ⊔ F`
  have hFU : Work.GW2.fittingIn B.U ⊓ D.M = D.K0 ⊔ D.F :=
    Work.CORE4.SixThree I G hbc B D hpre
  obtain ⟨hrprime, hrdvd, -⟩ := Nat.mem_primeFactors.mp hr
  -- suppose `r ∉ π(K₀F)`
  by_contra hnot
  haveI : Fact r.Prime := ⟨hrprime⟩
  -- `X ≤ M` (since `X ≤ N_G(X) ≤ M`), hence `X ≤ F(U) ∩ M = K₀ ⊔ F`
  have hXM : D.X ≤ D.M := (Subgroup.le_normalizer (H := D.X)).trans D.NX_le
  have hXK0F : D.X ≤ D.K0 ⊔ D.F := by
    rw [← hFU]
    exact le_inf D.X_le hXM
  -- so no prime of `|X|` is `r`
  have hrX : r ∉ Work.GW2.primesOf D.X := fun h => hnot (PiFU.primesOf_mono hXK0F h)
  have hrXdvd : ¬ r ∣ Nat.card ↥D.X := fun hdvd =>
    hrX (by rw [Work.GW2.primesOf]
            exact Nat.mem_primeFactors.mpr ⟨hrprime, hdvd, Nat.card_pos.ne'⟩)
  -- Cauchy: an element of `F(U)` of order `r`
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Work.GW2.fittingIn B.U)) r hrdvd
  -- `y` commutes with every `x ∈ X` (nilpotency of `F(U)`, coprime orders)
  have hcomm : ∀ x ∈ D.X, x * (y : G) = (y : G) * x := by
    intro x hx
    have hxA : x ∈ Work.GW2.fittingIn B.U := D.X_le hx
    haveI : Group.IsNilpotent ↥(Work.GW2.fittingIn B.U) := PiFU.isNilpotent_fittingIn B.U
    have hdvdX : orderOf (⟨x, hxA⟩ : ↥(Work.GW2.fittingIn B.U)) ∣ Nat.card ↥D.X := by
      rw [Subgroup.orderOf_mk]
      exact Subgroup.orderOf_dvd_natCard D.X hx
    have hcop : (orderOf (⟨x, hxA⟩ : ↥(Work.GW2.fittingIn B.U))).Coprime (orderOf y) := by
      rw [hy, Nat.coprime_comm]
      exact hrprime.coprime_iff_not_dvd.mpr fun hd => hrXdvd (hd.trans hdvdX)
    have hc := Group.IsNilpotent.commute_of_orderOf_coprime hcop
    simpa using congrArg (fun z : ↥(Work.GW2.fittingIn B.U) => (z : G)) hc.eq
  -- hence `y ∈ C_G(X) ≤ N_G(X) ≤ M`
  have hyM : (y : G) ∈ D.M :=
    D.NX_le (Subgroup.centralizer_le_normalizer (D.X : Set G)
      (Subgroup.mem_centralizer_iff.mpr hcomm))
  -- so `y ∈ F(U) ∩ M = K₀ ⊔ F` and `r = orderOf y` divides `|K₀ ⊔ F|`: contradiction
  have hyK0F : (y : G) ∈ D.K0 ⊔ D.F := by
    rw [← hFU]
    exact Subgroup.mem_inf.mpr ⟨y.2, hyM⟩
  have hyord : orderOf (y : G) = r := by
    rw [Subgroup.orderOf_coe]
    exact hy
  exact hnot (by
    rw [Work.GW2.primesOf]
    exact Nat.mem_primeFactors.mpr
      ⟨hrprime, hyord ▸ Subgroup.orderOf_dvd_natCard (D.K0 ⊔ D.F) hyK0F,
        Nat.card_pos.ne'⟩)

end Work.CORE4.SevenX
