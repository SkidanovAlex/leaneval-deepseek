/-
# The `C₄` shape: the squaring dichotomy on a minimal cover

Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), 79--96.

Setting: `P` is a Suzuki 2-group and `A ⊴ P` is abelian `ξ`-invariant with `Ω₁(P) ≤ A`,
`⁅⊤,⊤⁆ = A`, every square of `P` in `A`, `A² = Ω₁(P)` and `|A| = |Ω₁(P)|²` (the `C₄` setting).
`C ⊴ P` is a `ξ`-invariant normal cover of `A`, minimal among the `ξ`-invariant normal
subgroups strictly above `A` (`hcover`), with `⁅C,C⁆ = A²`.

The keystone is the subgroup

`D := {x ∈ C | x² ∈ A²}`

(the preimage in `C` of the kernel of the squaring map `C/A → A/A²`, `xA ↦ x²A²`, which is a
group homomorphism because `[C,C] = A²` kills the polar form).  `D` is `ξ`-invariant and normal
in `P`, contains `A`, and lies in `C`; minimality of `C` (`hcover`) therefore forces `D = A` or
`D = C`, which is the dichotomy below:

* `D = C`  : `C² ⊆ A²`, so `C` is of class two with `C' = A²` — the configuration to which the
  Chevalley–Warning bound `|C/Z| ≤ |Z|²` applies (with `Z = A² = Ω₁(P)`);
* `D = A`  : the induced map `C/A → A/A²` is injective, so `|C/A| ≤ |A/A²|`.

Both branches yield `|C| ≤ |A| · |Ω₁(P)|`.
-/
import Mathlib
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.chevalley_warning
import Submission.Work.Higman.center_eq_omega1_new
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.H8.cw_cube_bound

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman.C4Cover

variable {P : Type} [Group P] [Finite P]

/-- `A` is `ξ`-invariant when it is the derived subgroup. -/
theorem map_xi_of_eq_commutator (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) : A.map (h.xi : MulAut P).toMonoidHom = A := by
  simp only [← hGs, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective (h.xi : MulAut P).toMonoidHom (h.xi : MulAut P).surjective]

/-- `(x * y)² = ⁅y,x⁆ * x² * y²` when the commutator `⁅y,x⁆` commutes with `x`. -/
theorem sq_mul_of_commutator_comm {G : Type*} [Group G] {x y : G}
    (h : x * ⁅y, x⁆ = ⁅y, x⁆ * x) : (x * y) ^ 2 = ⁅y, x⁆ * x ^ 2 * y ^ 2 := by
  have h1 : y * x = ⁅y, x⁆ * x * y := by
    rw [commutatorElement_def]; group
  calc (x * y) ^ 2 = x * (y * x) * y := by rw [pow_two]; group
    _ = x * (⁅y, x⁆ * x * y) * y := by rw [h1]
    _ = (x * ⁅y, x⁆) * (x * (y * y)) := by group
    _ = (⁅y, x⁆ * x) * (x * (y * y)) := by rw [h]
    _ = ⁅y, x⁆ * x ^ 2 * y ^ 2 := by rw [pow_two, pow_two]; group

/-- **The squaring kernel of a minimal cover is `A` or `C`.**

In the `C₄` setting with `⁅C,C⁆ = A²`, the subgroup `D = {x ∈ C | x² ∈ A²}` is `ξ`-invariant
and normal in `P`, with `A ≤ D ≤ C`; minimality of `C` forces `D = A` or `D = C`. -/
theorem c4_sq_dichotomy (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E ≤ C → E = A ∨ E = C)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2) :
    (∀ x ∈ C, x ^ 2 ∈ Work.Higman.powSub A 2) ∨
      (∀ x ∈ C, x ^ 2 ∈ Work.Higman.powSub A 2 → x ∈ A) := by
  classical
  have hAxi : A.map (h.xi : MulAut P).toMonoidHom = A := map_xi_of_eq_commutator h hGs
  have hAn : A.Normal := hGs ▸ Subgroup.commutator_normal (⊤ : Subgroup P) ⊤
  have hZ2n : (Work.Higman.powSub A 2).Normal := Work.Higman.powSub_normal hAn 2
  have hZ2c : Work.Higman.powSub A 2 ≤ Subgroup.center P := htop ▸ h.omega1_le_center
  have hZ2inv : (Work.Higman.powSub A 2).map (h.xi : MulAut P).toMonoidHom
      = Work.Higman.powSub A 2 := Work.Higman.map_powSub h.xi hAxi 2
  -- `D` is the squaring kernel
  let D : Subgroup P :=
    { carrier := {x | x ∈ C ∧ x ^ 2 ∈ Work.Higman.powSub A 2}
      one_mem' := ⟨C.one_mem, by rw [one_pow]; exact (Work.Higman.powSub A 2).one_mem⟩
      mul_mem' := by
        rintro x y ⟨hxC, hx2⟩ ⟨hyC, hy2⟩
        refine ⟨C.mul_mem hxC hyC, ?_⟩
        have hc : ⁅y, x⁆ ∈ Work.Higman.powSub A 2 := by
          rw [← hCd]
          exact Subgroup.commutator_mem_commutator hyC hxC
        have hcomm : x * ⁅y, x⁆ = ⁅y, x⁆ * x :=
          Subgroup.mem_center_iff.mp (hZ2c hc) x
        rw [sq_mul_of_commutator_comm hcomm]
        exact (Work.Higman.powSub A 2).mul_mem ((Work.Higman.powSub A 2).mul_mem hc hx2) hy2
      inv_mem' := by
        rintro x ⟨hxC, hx2⟩
        refine ⟨C.inv_mem hxC, ?_⟩
        rw [inv_pow]
        exact (Work.Higman.powSub A 2).inv_mem hx2 }
  have hAD : A ≤ D := by
    intro a ha
    exact ⟨hAC ha, Work.Higman.pow_mem_powSub ha⟩
  have hDC : D ≤ C := fun x hx => hx.1
  have hDn : D.Normal := by
    refine Subgroup.Normal.mk ?_
    intro x hx g
    obtain ⟨hxC, hx2⟩ := hx
    refine ⟨hCn.conj_mem x hxC g, ?_⟩
    have h2 : (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := by
      rw [pow_two, pow_two]; group
    rw [h2]
    exact hZ2n.conj_mem (x ^ 2) hx2 g
  have hDinv_le : D.map (h.xi : MulAut P).toMonoidHom ≤ D := by
    rintro y ⟨x, ⟨hxC, hx2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have h1 : h.xi x ∈ C.map (h.xi : MulAut P).toMonoidHom := ⟨x, hxC, rfl⟩
      rwa [hCinv] at h1
    · rw [← map_pow]
      have h1 : h.xi (x ^ 2) ∈ (Work.Higman.powSub A 2).map (h.xi : MulAut P).toMonoidHom :=
        ⟨x ^ 2, hx2, rfl⟩
      rwa [hZ2inv] at h1
  have hDinv : D.map (h.xi : MulAut P).toMonoidHom = D := by
    refine Subgroup.eq_of_le_of_card_ge hDinv_le ?_
    exact le_of_eq (Nat.card_congr (Subgroup.equivMapOfInjective D
      (h.xi : MulAut P).toMonoidHom (h.xi : MulAut P).injective).toEquiv)
  rcases hcover D hDn hDinv hAD hDC with hD | hD
  · right
    intro x hx hx2
    have hmem : x ∈ D := ⟨hx, hx2⟩
    rwa [hD] at hmem
  · left
    intro x hx
    have hmem : x ∈ D := hD ▸ hx
    exact hmem.2

/-- **The `D = C` branch.**  If every square of `C` lies in `A² = Ω₁(P)` and `⁅C,C⁆ = A²`, then
`C` satisfies `Ω₁(P) ≤ C`, `C² ≤ Ω₁(P)`, `⁅C,C⁆ ≤ Ω₁(P)`, so the Chevalley–Warning bound
`Work.Higman.card_le_cube_of_sq_le_omega1` gives `|C| ≤ |Ω₁(P)|³ = |Ω₁(P)| · |A|` (as
`|A| = |Ω₁(P)|²`). -/
theorem c4_cover_card_le_of_sq (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    (hsq2 : ∀ x ∈ C, x ^ 2 ∈ Work.Higman.powSub A 2) :
    Nat.card ↥C ≤ Nat.card ↥(Work.Higman.omega1 P) * Nat.card ↥A := by
  have hM : Work.Higman.omega1 P ≤ C := by
    intro a ha
    rw [← htop, ← hCd] at ha
    exact (Subgroup.commutator_le (H₁ := C) (H₂ := C) (H₃ := C)).mpr
      (fun x hx y hy => by
        rw [commutatorElement_def]
        exact C.mul_mem (C.mul_mem (C.mul_mem hx hy) (C.inv_mem hx)) (C.inv_mem hy)) ha
  have hM2 : Work.Higman.powSub C 2 ≤ Work.Higman.omega1 P := by
    rw [Work.Higman.powSub, Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    rw [← htop]
    exact hsq2 x hx
  have hMd : ⁅C, C⁆ ≤ Work.Higman.omega1 P := by
    rw [hCd, htop]
  have hcube := Work.Higman.H8.card_le_cube_of_sq_le_omega1 h hM hM2 hMd
  calc Nat.card ↥C ≤ (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 := hcube
    _ = Nat.card ↥(Work.Higman.omega1 P) * Nat.card ↥A := by
        rw [hcard]; ring

end Work.Higman.C4Cover
