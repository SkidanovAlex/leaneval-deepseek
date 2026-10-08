import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.Case2NormalizerP
import Submission.Work.CORE4.OneInvClassM
import Submission.Work.CORE4.ConjInAH
import Submission.Work.CORE4.EightAeqOmega
import Submission.Work.CORE4.Case2SixThreeRaw

namespace Work.CORE4

open Subgroup

section Helpers

variable {G : Type} [Group G]

/-- `conjSub g` commutes with `⊓`. -/
private theorem conjSub_inf_c4 (g : G) (A B : Subgroup G) :
    Work.GW2.conjSub g (A ⊓ B) = Work.GW2.conjSub g A ⊓ Work.GW2.conjSub g B := by
  simp only [Work.GW2.conjSub]
  rw [Subgroup.map_inf_eq]
  exact (MulAut.conj g).injective

/-- `conjSub g` commutes with `Ω₁`. -/
private theorem conjSub_omega1_c4 (g : G) (p : ℕ) (X : Subgroup G) :
    Work.GW2.conjSub g (omega1 p X) = omega1 p (Work.GW2.conjSub g X) := by
  let f : G →* G := (MulAut.conj g).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj g).injective
  change (omega1 p X).map f = omega1 p (X.map f)
  rw [omega1, omega1, MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext x
  constructor
  · rintro ⟨y, ⟨hyW, hyp⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem f hyW, by rw [← map_pow, hyp, map_one]⟩
  · rintro ⟨hxW, hxp⟩
    obtain ⟨y, hyW, rfl⟩ := Subgroup.mem_map.mp hxW
    refine ⟨y, ⟨hyW, ?_⟩, rfl⟩
    exact hf (by simpa only [map_pow, map_one] using hxp)

/-- `N_G(P^g) = (N_G P)^g`. -/
private theorem normalizer_conjSub_c4 (g : G) (P : Subgroup G) :
    Subgroup.normalizer ((Work.GW2.conjSub g P : Subgroup G) : Set G) =
      Work.GW2.conjSub g (Subgroup.normalizer (P : Set G)) := by
  rw [Work.GW2.conjSub]
  exact (Subgroup.map_equiv_normalizer_eq P (MulAut.conj g)).symm

/-- `h ∈ H = C_G(t)` normalizes `U = O(H)`. -/
private theorem conjSub_U_eq_of_mem_H {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} {h' : G} (hh : h' ∈ B.H) :
    Work.GW2.conjSub h' B.U = B.U := by
  have hnorm : h' ∈ Subgroup.normalizer ((B.U : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨fun hu => (Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal u h' hu hh, fun hu => ?_⟩
    have h2 : h'⁻¹ * (h' * u * h'⁻¹) * h'⁻¹⁻¹ ∈ B.U :=
      (Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal (h' * u * h'⁻¹) h'⁻¹ hu
        (B.H.inv_mem hh)
    have h3 : h'⁻¹ * (h' * u * h'⁻¹) * h'⁻¹⁻¹ = u := by group
    rwa [h3] at h2
  rw [Work.GW2.conjSub]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hnorm

/-- `h ∈ H = C_G(t)` fixes `F(U)`. -/
private theorem conjSub_fittingIn_of_mem_H {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} {h' : G} (hh : h' ∈ B.H) :
    Work.GW2.conjSub h' (Work.GW2.fittingIn B.U) = Work.GW2.fittingIn B.U := by
  rw [Work.CORE4.conjSub_fittingIn, conjSub_U_eq_of_mem_H hh]

end Helpers

/-- **Bender 1981, §4, p. 227: the amalgam setup at the representative `X ≤ A`.**

Bender, verbatim: *"Fix such a conjugate `X`, say `X = P^g ≤ A`.  As `N_G(X) = M^g` has only one
class of involutions, we can choose `g` subject to `t^g = t`.  Then `A^g = A` because
`C_{F(U)}(P) = F × K₁ ⊴ C_{P·E}(P^g) = (F K₁)^g`."*

Formalised: for the §4 configuration `h : Case2Ctx B`, the odd prime `p` of §4 (8), Bender's
`(p,p)`-subgroup `A` of `F ⊔ K` containing `P ≤ F` of order `p`, and every conjugate `X ≤ A`
(`X ≠ P`, `X ~ P`) of `P` inside `A`, there is `h' ∈ B.H = C_G(t)` with both
`conjSub h' P = X` **and** `conjSub h' A = A`.

This is exactly the data Bender's p. 227 computation starts from: after it, `M^{h'}` contains `A`
and `W := P ⊔ E(M)`, and the displayed identities
`M^{h'} ⊓ W = N_W(X) = P K S₀ = C_W(A)` are single-copy statements in `W = P × E(M)`
(`C_W(A) = P ⊔ K ⊔ S₀` is **PROVED**: `Work.CORE4.CentAPE`).

## Route

* the first conjunct is `Work.CORE4.ConjInAH` (the `t^g = t` transport, whose involution-class
  input `Work.GW2.OneInvClassIn h.D.M` is now **PROVED** in `Work.CORE4.OneInvClassM`);
* for the second: with `h' ∈ B.H` one has `U^{h'} = U` and `F(U)^{h'} = F(U)`, and
  `A = Ω₁(F(U) ⊓ h.D.M)` (`Work.CORE4.EightAeqOmega` + `Work.CORE4.Case2SixThreeRaw`), so
  `A^{h'} = Ω₁(F(U) ⊓ M^{h'})`; moreover `A ≤ C_G(X)` (as `X ≤ A` and `A` is abelian) and
  `C_G(X) = C_G(P)^{h'} ≤ M^{h'}` (`N_G(P) = h.D.M`, `Work.CORE4.Case2NormalizerP`), so
  `A ≤ F(U) ⊓ M^{h'} ⊆ Ω₁(F(U) ⊓ M^{h'}) = A^{h'}`, and `|A^{h'}| = |A| = p²` gives
  `A^{h'} = A`. -/
theorem Case2AmalgamSetup (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
        (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
        Work.GW2.Case2EightObj h.D p P A →
        ∀ X : Subgroup G, X ≤ A → X ≠ P → (∃ g : G, X = Work.GW2.conjSub g P) →
          ∃ h' ∈ B.H, Work.GW2.conjSub h' P = X ∧ Work.GW2.conjSub h' A = A := by
  intro G _ _ hbc B h p P A hp hPF hPcard hObj X hXA hXPne hconj
  -- The first conjunct: Bender's involution argument.
  obtain ⟨h', hhh, hhP⟩ :=
    ConjInAH I G hbc B h (OneInvClassM I G hbc B h) p P A hp hPF hPcard hObj X hXA hXPne hconj
  refine ⟨h', hhh, hhP, ?_⟩
  -- `A = Ω₁(F(U) ⊓ M)`
  have hAeqΩ : A = omega1 p (Work.GW2.fittingIn B.U ⊓ h.D.M) := by
    obtain ⟨-, hAeq⟩ := EightAeqOmega I G hbc B h p P A hp hPF hPcard hObj
    have hSix := SixThree I G hbc B h.D h.pre
    have hM : Work.GW2.fittingIn B.U ⊓ h.D.M
        = h.D.F ⊔ Work.GW2.Case2Data.K0 h.D := by
      rw [hSix, Work.GW2.Case2Data.K0]
      exact sup_comm _ _
    rw [hAeq, hM]
  -- `A ≤ F(U)`
  have hAfit : A ≤ Work.GW2.fittingIn B.U := by
    rw [hAeqΩ, omega1]
    refine (Subgroup.closure_le (Work.GW2.fittingIn B.U)).mpr ?_
    intro x hx
    simp only [omega1Set] at hx
    exact hx.1.1
  obtain ⟨-, -, -, -, hAcard, hAexp, -, -⟩ := hObj
  -- `A` is abelian (a group of order `p²`), so `A ≤ C_G(X)`
  haveI : Fact p.Prime := ⟨hp⟩
  have hAcomm : IsMulCommutative ↥A := IsPGroup.isMulCommutative_of_card_eq_prime_sq hAcard
  have hACX : A ≤ Subgroup.centralizer (X : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    simpa using hAcomm.is_comm.comm ⟨x, hXA hx⟩ ⟨a, ha⟩
  -- `N_G(X) = M^{h'}`
  have hPne : P ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hPcard
    exact hp.ne_one hPcard.symm
  have hNP : Subgroup.normalizer (P : Set G) = h.D.M := Case2NormalizerP G B h P hPF hPne
  have hNX : Subgroup.normalizer (X : Set G) = Work.GW2.conjSub h' h.D.M := by
    rw [← hhP, normalizer_conjSub_c4, hNP]
  have hAM : A ≤ Work.GW2.conjSub h' h.D.M := by
    rw [← hNX]
    exact le_trans hACX (Subgroup.centralizer_le_normalizer (X : Set G))
  -- `A ≤ Ω₁(F(U) ⊓ M^{h'}) = A^{h'}`
  have hAle : A ≤ omega1 p (Work.GW2.fittingIn B.U ⊓ Work.GW2.conjSub h' h.D.M) := by
    intro x hx
    refine Subgroup.subset_closure ⟨⟨hAfit hx, hAM hx⟩, ?_⟩
    exact hAexp x hx
  have hconjA : Work.GW2.conjSub h' A
      = omega1 p (Work.GW2.fittingIn B.U ⊓ Work.GW2.conjSub h' h.D.M) := by
    rw [hAeqΩ, conjSub_omega1_c4, conjSub_inf_c4, conjSub_fittingIn_of_mem_H hhh]
  have hcard : Nat.card ↥(Work.GW2.conjSub h' A) = Nat.card ↥A := by
    rw [Work.GW2.conjSub]
    exact Subgroup.card_map_of_injective (MulAut.conj h').injective
  refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · rw [hconjA]; exact hAle
  · rw [hcard]

end Work.CORE4
