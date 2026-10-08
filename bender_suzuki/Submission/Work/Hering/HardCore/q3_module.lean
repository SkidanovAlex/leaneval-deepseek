import Mathlib
import Submission.Work.Hering.HardCore.Defs
import Submission.Work.Higman.Class
import Submission.Work.Hering.GL32.AppIXDefs
import Submission.Work.Hering.HardCore.appIX_card_dichotomy
import Submission.Work.Hering.HardCore.exists_simple_stable_subgroup
import Submission.Work.Hering.HardCore.SixtyfourSetup
import Submission.Work.Hering.HardCore.exists_normal_sixtyfour_min

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.HardCore

open scoped commutatorElement

/-- In the reduced configuration with `|C| = |Z(C)|³ = 512`, there is a subgroup `D` of `G`
with `V ≤ D ≤ C`, `D ⊴ G` and `|D| = 64`.

Proof route: `Ω₁(C) = Z(C) = V`, `[C,C] = V` and `x² ∈ Z(C)` come from `hHig.1`
(`HigmanProp`); so `Q = C/V` is an elementary abelian 2-group of order 64 carrying the
conjugation action of `G/C ≅ Aut(V) ≅ GL(3,2) = Work.Hering.GL32` (build ρ : GL32 →* MulAut Q
from `hAut`, as in `exists_GL32_rep_conj`). By `AppIXProp` every irreducible
`F₂[GL(3,2)]`-submodule has `|S| ∈ {2,8,256}` (see `appIX_card_dichotomy`); `|S| = 2` would give
`x ∈ C ∖ V` with `x` fixed mod `V`, whence `x² ∈ V#` is fixed by `Aut(V)` (transitive on `V#`),
so `x² = 1` and `x ∈ Ω₁(C) = V`, contradiction; `|S| = 256 > 64` is impossible. So take a
minimal non-zero stable `S` with `|S| = 8` and `D =` its preimage in `C`. (A minimality clause
`∀ E, E.Normal → V ≤ E → E ≤ D → E ≠ D → E = V` may be added — it is not needed here.) -/
theorem q3_module {G : Type} [Group G] [Finite G]
    (hHig : Work.Higman.HigmanClassProp) (hIX : Work.Hering.AppIXProp)
    (V C : Subgroup G) (hV : V.Normal) (hcard : Nat.card V = 8)
    (hexp : ∀ x ∈ V, x * x = 1) (hC : C = Subgroup.centralizer ((V : Set G)))
    (hC2 : IsPGroup 2 ↥C) (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V)
    (hAut : Work.Hering.ActsAsAut V hV)
    (hnotab : ¬ ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hSuz : Work.Hering.IsSuzukiTwoGroup ↥C)
    (hZcard : Nat.card ↥(Subgroup.center ↥C) = 8)
    (hcard3 : Nat.card ↥C = Nat.card ↥(Subgroup.center ↥C) ^ 3) :
    ∃ D : Subgroup G, D.Normal ∧ D ≤ C ∧ V ≤ D ∧ Nat.card D = 64 := by
  classical
  -- `V` is elementary abelian, hence abelian.
  have commV : ∀ {x y : G}, x ∈ V → y ∈ V → x * y = y * x := by
    intro x y hx hy
    have hx1 : x * x = 1 := hexp x hx
    have hxy : (x * y) * (x * y) = 1 := hexp (x * y) (V.mul_mem hx hy)
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx1
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hexp y hy)
    have h2 : x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
    rw [mul_inv_rev, hxinv, hyinv] at h2
    exact h2
  have hVC : V ≤ C := by
    intro x hx
    rw [hC, Subgroup.mem_centralizer_iff]
    intro v hv
    exact commV hv hx
  -- ## `V ≤ Z(C)`
  have hVleZ : V.subgroupOf C ≤ Subgroup.center ↥C := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    have hzv : (z : G) ∈ V := Subgroup.mem_subgroupOf.mp hz
    have h1 : (c : G) ∈ Subgroup.centralizer ((V : Set G)) := by
      rw [← hC]; exact c.2
    have h2 := (Subgroup.mem_centralizer_iff.mp h1) (z : G) hzv
    exact h2.symm
  have hcardVsub : Nat.card ↥(V.subgroupOf C) = 8 := by
    have h1 : Nat.card ↥(V.subgroupOf C) = Nat.card ↥V :=
      Nat.card_congr
        { toFun := fun x => ⟨((x : ↥C) : G), Subgroup.mem_subgroupOf.mp x.2⟩
          invFun := fun v => ⟨⟨(v : G), hVC v.2⟩, Subgroup.mem_subgroupOf.mpr v.2⟩
          left_inv := fun x => Subtype.ext rfl
          right_inv := fun v => Subtype.ext rfl }
    rw [h1, hcard]
  -- ## `Z(C) = V`, hence `|C| = 512`
  have hZeq : Subgroup.center ↥C = V.subgroupOf C :=
    (Subgroup.eq_of_le_of_card_ge hVleZ
      (le_of_eq (by rw [hZcard, hcardVsub]))).symm
  have hcardC : Nat.card ↥C = 512 := by
    rw [hcard3, hZcard]; norm_num
  -- ## Higman's theorem applied to the Suzuki 2-group `C`
  have hSuz' : Submission.Blueprint.IsSuzukiTwoGroup ↥C := hSuz
  obtain ⟨-, hsqC, hcommC, -, -⟩ := hHig.1 ↥C hSuz'
  have hsq : ∀ x ∈ C, x * x ∈ V := by
    intro x hx
    have h1 := hsqC ⟨x, hx⟩
    rw [hZeq, Subgroup.mem_subgroupOf] at h1
    simpa [pow_two] using h1
  have hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y * x⁻¹ * y⁻¹ ∈ V := by
    intro x hx y hy
    have h1 : ⁅(⟨x, hx⟩ : ↥C), (⟨y, hy⟩ : ↥C)⁆ ∈ commutator ↥C :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [hcommC, hZeq, Subgroup.mem_subgroupOf, commutatorElement_def] at h1
    simpa using h1
  -- ## Peterfalvi I §4 via Appendix IX
  obtain ⟨D, hDn, hDleC, hVD, hDcard, -⟩ :=
    exists_normal_sixtyfour_min hIX V C hV hcard hexp hC hC2 hinv hAut hcardC hsq hcomm
  exact ⟨D, hDn, hDleC, hVD, hDcard⟩

end Work.Hering.HardCore
