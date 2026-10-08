import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.rem31StabCard
import Submission.Work.BG.rem31IndexUin
import Submission.Work.BG.lamCF_fixed_eq_neg_one

/-!
# Area BG: the `Λ`-orbit of a class function `κ` that is `1` on `S₀` has size `n`

Bender–Glauberman's `Λ` is the group `Hom(H₀/U, ℂˣ)` of linear characters of `H₀/U`,
inflated to class functions on `H₀`; it acts on the class functions of `H₀` by pointwise
multiplication, `β • f = λ_β · f`, and `Λν` denotes the orbit of `ν`.

The point of this file (BG §3–§4, the `κ₁`-bookkeeping of Theorem C) is that an admissible
`κ` — a class function of `H₀` that is `1` on `S₀`, hence has `κ(t) = 1` — has *trivial*
stabiliser in `Λ`, so its orbit is as large as `Λ` itself:

* `Work.BG.lamStab_eq_bot_of_eq_one_on_S0` — the stabiliser `Λ_κ = {λ : λκ = κ}` is trivial;
* `Work.BG.c3LamOrbitKappa` — hence `|Λκ| = [H₀ : U] = n` by orbit–stabiliser
  (`Work.BG.rem31StabCard`) and the index bookkeeping `[H₀ : U] = n`
  (`Work.BG.rem31IndexUin`).

The mathematics of the stabiliser computation: `λ_β κ = κ` evaluated at an `h ∈ S₀` gives
`λ_β(h) = 1` (as `κ h = 1`).  Every element of `H₀/U` is the image of an element of `S₀`,
because `H₀ = U ⊔ S₀` (`Compat D C`) with `U ⊴ H₀`, i.e. `H₀ = U·S₀` pointwise; and `λ_β` is
trivial on `U`.  So `β = 1`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-- **The stabiliser in `Λ` of a class function `κ` that is `1` on `S₀` is trivial.**

`Λ = Hom(H₀/U, ℂˣ)` acts on the class functions of `H₀` by `β • f = λ_β · f`.  If
`κ h = 1` for every `h ∈ H₀` with `h ∈ S₀`, then `λ_β · κ = κ` forces `β = 1`: evaluating at
`h ∈ S₀` gives `λ_β(h) = 1`, and `H₀ = U · S₀` (`H₀ = U ⊔ S₀` with `U ⊴ H₀`), while every
`λ ∈ Λ` is trivial on `U`; so `β` vanishes on all of `H₀/U`. -/
theorem lamStab_eq_bot_of_eq_one_on_S0 (D : Work.GW2.BGData G) (C : Sec2Ctx G)
    (hC : Work.GW2.C16.Compat D C) (κ : ClassFunction ↥C.P.H0 ℂ)
    (hκS0 : ∀ h : ↥C.P.H0, (h : G) ∈ D.S0 → κ h = 1) :
    lamStab C κ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro β hβ
  rw [mem_lamStab] at hβ
  -- `H₀ = U ⊔ S₀` in the compatible data `D`
  have hPC : C.P.H0 = C.P.U ⊔ D.S0 := by
    rw [hC.H0_eq, Work.BG.H1, hC.U_eq]
  -- `U ⊔ S₀ = H₀` inside `↥H₀`: `U` is normal in `H₀`, so `H₀ = U · S₀` pointwise
  have hsup : (C.P.U.subgroupOf C.P.H0) ⊔ (D.S0.subgroupOf C.P.H0) = ⊤ := by
    have hA : C.P.U ≤ C.P.H0 := by rw [hPC]; exact le_sup_left
    have hA' : D.S0 ≤ C.P.H0 := by rw [hPC]; exact le_sup_right
    rw [← Subgroup.subgroupOf_sup hA hA', hPC, Subgroup.subgroupOf_self]
  -- `β` is trivial on the image of `S₀` in `H₀/U`
  have hunit : ∀ s : ↥C.P.H0, (s : G) ∈ D.S0 → β (quotMk C.P s) = 1 := by
    intro s hs
    -- `λ_β(s) = 1` because `κ s = 1 = (λ_β κ) s = λ_β(s) κ(s)`
    have hval : lamCF C β s = 1 := by
      have h := congrArg (fun f : ClassFunction ↥C.P.H0 ℂ => f s) hβ
      rw [ClassFunction.mul_apply, hκS0 s hs, mul_one] at h
      exact h
    have h1 : ((β (quotMk C.P s) : ℂˣ) : ℂ) = 1 := by
      rw [← lamCF_apply C β s]
      exact hval
    exact Units.ext h1
  -- `β = 1`: `quotMk C.P` is surjective, and every element of `H₀` is `u · s` with
  -- `u ∈ U` (where `β` is trivial, as `U` is the kernel of the projection) and `s ∈ S₀`
  refine MonoidHom.ext fun y => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (C.P.U.subgroupOf C.P.H0) y
  have hx : x ∈ (C.P.U.subgroupOf C.P.H0) ⊔ (D.S0.subgroupOf C.P.H0) := by
    rw [hsup]; exact Subgroup.mem_top x
  rw [Subgroup.mem_sup_of_normal_left] at hx
  obtain ⟨u, hu, s, hs, hus⟩ := hx
  have hu1 : quotMk C.P u = 1 :=
    (QuotientGroup.eq_one_iff (N := C.P.U.subgroupOf C.P.H0) u).mpr hu
  have key : β (quotMk C.P x) = 1 := by
    rw [← hus, map_mul, hu1, one_mul]
    exact hunit s hs
  simpa only [MonoidHom.one_apply] using key

open OddOrder.RepresentationTheory Work.GW2 Work.BG in
theorem c3LamOrbitKappa {G : Type} [Group G] [Finite G]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    (hC : Work.GW2.C16.Compat D C) (κ : ClassFunction ↥C.P.H0 ℂ)
    (hκS0 : ∀ h : ↥C.P.H0, (h : G) ∈ D.S0 → κ h = 1) :
    (Work.BG.lamOrbit C κ).ncard = D.n := by
  -- the stabiliser is trivial, so orbit–stabiliser gives the full size `[H₀ : U] = n`
  have hstab : Nat.card ↥(lamStab C κ) = 1 := by
    rw [lamStab_eq_bot_of_eq_one_on_S0 D C hC κ hκS0, Subgroup.card_bot]
  have h := rem31StabCard C κ
  rw [hstab, one_mul, rem31IndexUin D C hC] at h
  exact h

end Work.BG
