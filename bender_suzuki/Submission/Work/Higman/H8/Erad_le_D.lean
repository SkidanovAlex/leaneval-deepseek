import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.center_eq_omega1_new
import Submission.Work.Higman.HS.erad_mem_iff
import Submission.Work.Higman.H8.cw_cube_bound
import Submission.Work.Higman.H8.c4_erad
import Submission.Work.Higman.H8.powSub_sup_zpowers_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.style.longLine false

namespace Work.Higman.H8

open scoped commutatorElement

variable {P : Type} [Group P]

/-- In the `C₄` residual setting (`P` a Suzuki 2-group, `A ⊴ P` abelian `ξ`-invariant with `Ω₁(P) ≤ A`, `⁅⊤,⊤⁆ = A`, `A⁴ = 1`, `A² = Ω₁(P)`, `D ⊴ P` with `A ≤ D`, `D² ⊆ A²`, `⁅D,D⁆ = A²`, `|D| = |Ω₁(P)|³` and `⁅⊤,D⁆ ⊄ A²`), the subgroup `Erad := {x : ⁅x,y⁆ ∈ A² for all y}` (the preimage of the centre of `P/A²`) is contained in `D`.  Route: `Erad · D` satisfies `(Erad·D)² ⊆ Ω₁(P)`, `⁅Erad·D, Erad·D⁆ ⊆ Ω₁(P)` and `Ω₁(P) ≤ Erad·D`, so `Work.Higman.H8.card_le_cube_of_sq_le_omega1` gives `|Erad·D| ≤ |Ω₁(P)|³ = |D|`; since `Erad·D ⊇ D` this forces `Erad·D = D`. -/
theorem Erad_le_D {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A D : Subgroup P} (hAn : A.Normal)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ = A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hDn : D.Normal)
    (hAD : A ≤ D)
    (hD2 : Work.Higman.powSub D 2 ≤ Work.Higman.powSub A 2)
    (hDd : Bracket.bracket D D = Work.Higman.powSub A 2)
    (hDcard : Nat.card ↥D = (Nat.card ↥(Work.Higman.omega1 P)) ^ 3)
    (hCP : ¬ (Bracket.bracket (⊤ : Subgroup P) D ≤ Work.Higman.powSub A 2))
    {x : P} (hx : ∀ y : P, x * y * x⁻¹ * y⁻¹ ∈ Work.Higman.powSub A 2) : x ∈ D := by
  classical
  haveI : A.Normal := hAn
  -- `Z := A² = Ω₁(P)` is the centre of `P`
  have hZc : Work.Higman.powSub A 2 ≤ Subgroup.center P := by
    rw [htop]
    exact h.omega1_le_center
  have hcenter : Subgroup.center P = Work.Higman.powSub A 2 := by
    rw [Work.Higman.center_eq_omega1_new h, htop]
  -- every `x` with `⁅x,⊤⁆ ⊆ A²` has `x * x ∈ A²`
  have hx2 : x * x ∈ Work.Higman.powSub A 2 := by
    have hmem : x * x ∈ Subgroup.center P := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hxy : ⁅x, y⁆ ∈ Work.Higman.powSub A 2 := by
        simpa [commutatorElement_def] using hx y
      have h1 : ⁅x, ⁅x, y⁆⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact Subgroup.mem_center_iff.mp (hZc hxy) x
      have h2 : ⁅x, y⁆ ^ 2 = 1 := h.mem_omega1.mp (htop ▸ hxy)
      have h3 : ⁅x ^ 2, y⁆ = 1 := by rw [comm_sq_self x y, h1, h2, mul_one]
      simpa [pow_two] using (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
    rwa [hcenter] at hmem
  -- the generation lemma applies with `H := D`
  have hD2' : ∀ d ∈ D, d * d ∈ Work.Higman.powSub A 2 := by
    intro d hd
    have h1 : d ^ 2 ∈ Work.Higman.powSub D 2 := Work.Higman.pow_mem_powSub hd
    rw [pow_two] at h1
    exact hD2 h1
  have hDd' : ∀ d₁ ∈ D, ∀ d₂ ∈ D, d₁ * d₂ * d₁⁻¹ * d₂⁻¹ ∈ Work.Higman.powSub A 2 := by
    intro d₁ hd₁ d₂ hd₂
    have hmem : ⁅d₁, d₂⁆ ∈ ⁅D, D⁆ := Subgroup.commutator_mem_commutator hd₁ hd₂
    rw [hDd] at hmem
    simpa [commutatorElement_def] using hmem
  -- every element of `M := D ⊔ ⟨x⟩` has its square in `A²` and `⁅M,M⁆ ⊆ A²`
  obtain ⟨hM2', hMd'⟩ :=
    powSub_sup_zpowers_le (P := P) (Work.Higman.powSub A 2) hZc hD2' hDd'
      hx2 (fun d _ => hx d)
  -- apply the Chevalley–Warning bound to `M := D ⊔ ⟨x⟩`
  have hOM : Work.Higman.omega1 P ≤ D ⊔ Subgroup.zpowers x := by
    rw [← htop]
    exact le_trans (le_trans (Work.Higman.powSub_le (A := A) (n := 2) (by norm_num)) hAD)
      le_sup_left
  have hOM2 : Work.Higman.powSub (D ⊔ Subgroup.zpowers x) 2 ≤ Work.Higman.omega1 P :=
    hM2'.trans (le_of_eq htop)
  have hOMd : ⁅D ⊔ Subgroup.zpowers x, D ⊔ Subgroup.zpowers x⁆ ≤ Work.Higman.omega1 P := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    simpa [commutatorElement_def, htop] using hMd' a ha b hb
  have hcard := card_le_cube_of_sq_le_omega1 h hOM hOM2 hOMd
  have hle : Nat.card ↥(D ⊔ Subgroup.zpowers x) ≤ Nat.card ↥D := by
    rw [← hDcard] at hcard
    exact hcard
  have hEq : D = D ⊔ Subgroup.zpowers x := Subgroup.eq_of_le_of_card_ge le_sup_left hle
  rw [hEq]
  exact (le_sup_right : Subgroup.zpowers x ≤ D ⊔ Subgroup.zpowers x) (Subgroup.mem_zpowers x)

end Work.Higman.H8
