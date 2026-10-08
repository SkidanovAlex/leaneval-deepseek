import Mathlib
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.S_le_H
import Submission.Work.BG.splitglue.Split
import Submission.Work.BG.invJCard
import Submission.Work.BG.kappaExists
import Submission.Work.BG.thmCSmallAux
import Submission.Work.BG.l41vBInv

set_option linter.style.haveILetI false

namespace Work.BG

open Subgroup
open scoped Pointwise

/-- Group-theoretic input for `Work.GW2.C23.NOrbProp` when `D.n = 2` (so `S ≅ V₄`).

`B = B₁ ⊓ B₂` with `Bᵢ = D.U ⊓ C_G(tᵢ)` (so `B = C_U(S)`) is normalized by `N_G(S)`, and every
element of `C_G(S)` acts on `B` as an *inner* automorphism of `B`.

Route sketch: with `C = C_G(S)` and `N = N_G(S)`, `C ⊆ C_G(t) = H = U·S` by
`Work.BG.SplitGlue.centralizerSplitProp`; an element of `C` of odd order lies in `U` (its image
in `H/U`, a group of order `|S| = 4`, has order dividing its odd order), so
`C = S·B = S ⋊ B`, and every coset of `B` in `C` has a representative centralising `S`. -/
theorem nOrbBInv {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) (hn : D.n = 2) :
    (∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
        ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B) ∧
    (∀ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), ∀ b ∈ D.B,
        ∃ b₀ ∈ D.B, c⁻¹ * b * c = b₀ * b * b₀⁻¹) := by
  haveI : Fintype G := Fintype.ofFinite G
  refine ⟨l41vBInv D hn, ?_⟩
  -- The `|S| = 4` shape of `S ≅ V₄`: `t = t₁t₂` and `S ≤ C_G(t₁)`, `S ≤ C_G(t₂)`.
  obtain ⟨-, -, -, hSleC1, hSleC2⟩ := thmCSmallAux D hn
  -- `S` is abelian, i.e. `S ≤ C_G(S)` (both `t₁` and `t₂` generate `S`).
  have hS_le_C : (D.S : Subgroup G) ≤ Subgroup.centralizer ((D.S : Subgroup G) : Set G) := by
    rw [S_eq_closure D, Subgroup.centralizer_closure]
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    have hs' : s ∈ (D.S : Subgroup G) := (S_eq_closure D).symm ▸ hs
    rcases hh with rfl | rfl
    · exact Subgroup.mem_centralizer_iff.mp (hSleC1 hs') D.t1 (Set.mem_singleton D.t1)
    · exact Subgroup.mem_centralizer_iff.mp (hSleC2 hs') D.t2 (Set.mem_singleton D.t2)
  -- `C = C_G(S) ≤ C_G(t) = H`, and `H = U ⊔ S` (Bender's centralizer splitting).
  have hC_le_H : Subgroup.centralizer ((D.S : Subgroup G) : Set G) ≤ D.H :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (D.S0_le D.t_mem))
  have hcentr : ∀ x ∈ (D.S : Subgroup G), x * D.t = D.t * x := fun x hx =>
    ((Subgroup.mem_centralizer_iff.mp (show x ∈ Subgroup.centralizer ({D.t} : Set G) from
      S_le_H D hx)) D.t (Set.mem_singleton D.t)).symm
  have hUS : D.U ⊔ (D.S : Subgroup G) = D.H :=
    SplitGlue.centralizerSplitProp G D.S D.n D.two_le D.dih D.t (D.S0_le D.t_mem) D.t_order hcentr
  -- `C_G(S) ≤ C_G(tᵢ)` since `tᵢ ∈ S`.
  have hC_le_CGt1 : Subgroup.centralizer ((D.S : Subgroup G) : Set G) ≤
      Subgroup.centralizer ({D.t1} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr D.t1_mem)
  have hC_le_CGt2 : Subgroup.centralizer ((D.S : Subgroup G) : Set G) ≤
      Subgroup.centralizer ({D.t2} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr D.t2_mem)
  intro c hc b hb
  -- Write `c = u * s` with `u ∈ U`, `s ∈ S`, using `H = U ⊔ S` and `↑(U ⊔ S) = ↑U * ↑S`.
  have hcH : c ∈ D.H := hC_le_H hc
  have hcU : c ∈ D.U ⊔ (D.S : Subgroup G) := by rw [hUS]; exact hcH
  have hcProd : c ∈ (↑D.U : Set G) * (↑(D.S : Subgroup G) : Set G) := by
    rw [← coe_U_sup_S D]; exact hcU
  obtain ⟨u, huU, s, hsS, hus⟩ := hcProd
  -- `s ∈ S ⊆ C_G(S)`, hence `u = c * s⁻¹ ∈ C_G(S)` as well.
  have huC : u ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G) := by
    have hu_eq : u = c * s⁻¹ := by rw [← hus]; group
    rw [hu_eq]
    exact mul_mem hc (hS_le_C ((D.S : Subgroup G).inv_mem hsS))
  -- so `u ∈ U ⊓ C_G(t₁) ⊓ C_G(t₂) = B`.
  have huB : u ∈ D.B := ⟨⟨huU, hC_le_CGt1 huC⟩, huU, hC_le_CGt2 huC⟩
  -- And `s⁻¹ * x * s = x` for `x ∈ B`, because `B ≤ C_G(S)`: so conjugation by `c = u·s` on
  -- `B` is conjugation by `u ∈ B`, which is inner (with `b₀ = u⁻¹`).
  refine ⟨u⁻¹, (D.B).inv_mem huB, ?_⟩
  have hX : u⁻¹ * b * u ∈ D.B :=
    (D.B).mul_mem ((D.B).mul_mem ((D.B).inv_mem huB) hb) huB
  have hcomm : s * (u⁻¹ * b * u) = (u⁻¹ * b * u) * s :=
    Subgroup.mem_centralizer_iff.mp (B_le_centralizer_S D hX) s hsS
  rw [show c = u * s from hus.symm]
  calc (u * s)⁻¹ * b * (u * s) = s⁻¹ * (u⁻¹ * b * u) * s := by group
    _ = s⁻¹ * ((u⁻¹ * b * u) * s) := by group
    _ = s⁻¹ * (s * (u⁻¹ * b * u)) := by rw [hcomm]
    _ = u⁻¹ * b * (u⁻¹)⁻¹ := by group

end Work.BG
