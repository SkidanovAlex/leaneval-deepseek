import Mathlib
import Submission.Work.ZassenhausSuzuki.SL2ModelClass
import Submission.Work.BSLit.BenderFacts2.centralizer_diagUnit_eq_D
import Submission.Work.BSLit.BenderFacts2.isCyclic_card_conj_centralizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.BenderFacts2

open Matrix

/-- The trace of the diagonal unit `diag(u, u⁻¹)` is `u + u⁻¹`. -/
private lemma trace_diagUnit {F : Type*} [Field F] [CharP F 2] (u : Fˣ) :
    (Work.Models.PSL2.diagUnit u : Matrix (Fin 2) (Fin 2) F).trace
      = (u : F) + ((u⁻¹ : Fˣ) : F) := by
  rw [Work.Models.PSL2.diagUnit, Matrix.trace_fin_two]
  simp [Units.val_inv_eq_inv_val]

/-- **The centraliser of an element of `SL(2,F)` (`F` a finite field of characteristic `2`)
of non-zero trace is cyclic, of order `|F| - 1` or `|F| + 1`** (hence at least `|F| - 1`).

`x ∈ Work.Models.SL2 F = Matrix.SpecialLinearGroup (Fin 2) F` with
`(x : Matrix (Fin 2) (Fin 2) F).trace ≠ 0`; `x` is then conjugate to the companion matrix of
`X² + τX + 1` (`τ = trace x`), which either splits over `F` (then `x` is conjugate to
`Work.Models.PSL2.diagUnit (Units.mk0 z)`, `z + z⁻¹ = τ`, and its centraliser is the diagonal
torus `Work.Models.PSL2.D`, cyclic of order `|F| - 1` by `Work.Models.PSL2.D_facts`) or is
irreducible (then `Anisotropic F τ` holds, `x` is conjugate to
`Work.ZassenhausSuzuki.SingerModelCycle.alphaSL τ` and its centraliser is the Singer cycle
`singerSubgroup τ`, cyclic of order `|F| + 1` by
`Work.ZassenhausSuzuki.SingerModelCycle.{isCyclic_singerSubgroup, card_singerSubgroup}`).

Available ingredients: `Work.ZassenhausSuzuki.sl2_conj_of_trace_eq` (equal non-zero trace ⇒
conjugate), `Work.ZassenhausSuzuki.sl2_conj_companion`, `Work.ZassenhausSuzuki.centralizer_alphaSL`,
`Work.ZassenhausSuzuki.exists_root_iff_sum_inv`,
`Work.ZassenhausSuzuki.SingerModelCycle.alphaSL_coe` (`alphaSL τ` is the companion matrix
`!![0,1;1,τ]`), the characterisation `(¬ ∃ z, z * z + τ * z + 1 = 0) → Anisotropic F τ`
(proved inline in `Work.ZassenhausSuzuki.sl2_classify`), and the centraliser transport
`Work.BSLit.BenderFacts2.centralizer_map_mulEquiv` plus `Subgroup.card_map_of_injective` and
`MulEquiv.isCyclic`. In the split case one needs `C(diagUnit u) = D` for `u ≠ 1` (direct entry
computation: `A * diag(a,a⁻¹) = diag(a,a⁻¹) * A` forces the two off-diagonal entries of `A` to
vanish because `a + a⁻¹ ≠ 0`, and `D` is abelian). -/
theorem sl2_centralizer_isCyclic_of_trace_ne_zero {F : Type*} [Field F] [Finite F] [CharP F 2]
    {x : Work.Models.SL2 F} (htr : (x : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) :
    IsCyclic ↥(Subgroup.centralizer ({x} : Set (Work.Models.SL2 F))) ∧
      Nat.card F - 1 ≤ Nat.card ↥(Subgroup.centralizer ({x} : Set (Work.Models.SL2 F))) := by
  set τ : F := (x : Matrix (Fin 2) (Fin 2) F).trace with hτ
  have hτne : τ ≠ 0 := by rw [hτ]; exact htr
  -- conjugation transports the two conclusions from a conjugate of `x`
  have key : ∀ (a c : Work.Models.SL2 F) (N : ℕ), c⁻¹ * a * c = x →
      IsCyclic ↥(Subgroup.centralizer ({a} : Set (Work.Models.SL2 F))) →
      Nat.card ↥(Subgroup.centralizer ({a} : Set (Work.Models.SL2 F))) = N →
      IsCyclic ↥(Subgroup.centralizer ({x} : Set (Work.Models.SL2 F))) ∧
        Nat.card ↥(Subgroup.centralizer ({x} : Set (Work.Models.SL2 F))) = N := by
    intro a c N hx hcyc hcard
    have h1 : IsCyclic ↥(Subgroup.centralizer ({c⁻¹ * a * c} :
        Set (Work.Models.SL2 F))) := by
      have h := (isCyclic_card_conj_centralizer a c⁻¹).1.mp hcyc
      rw [inv_inv] at h
      exact h
    have h2 : Nat.card ↥(Subgroup.centralizer ({c⁻¹ * a * c} : Set (Work.Models.SL2 F)))
        = Nat.card ↥(Subgroup.centralizer ({a} : Set (Work.Models.SL2 F))) := by
      have h := (isCyclic_card_conj_centralizer a c⁻¹).2
      rw [inv_inv] at h
      exact h
    rw [hx] at h1 h2
    exact ⟨h1, h2.trans hcard⟩
  by_cases hroot : ∃ z : F, z * z + τ * z + 1 = 0
  · -- `X ^ 2 + τX + 1` splits: `x` is conjugate into the split torus
    obtain ⟨w, hw0, hw⟩ := (Work.ZassenhausSuzuki.exists_root_iff_sum_inv τ).mp hroot
    set u : Fˣ := Units.mk0 w hw0 with hu
    have hu_val : (u : F) = w := by rw [hu]; exact Units.val_mk0 hw0
    have hu_inv : ((u⁻¹ : Fˣ) : F) = w⁻¹ := by
      rw [hu, Units.val_inv_eq_inv_val, Units.val_mk0]
    have hsum : (u : F) + ((u⁻¹ : Fˣ) : F) = τ := by rw [hu_val, hu_inv, ← hw]
    have hwne : (u : F) + ((u⁻¹ : Fˣ) : F) ≠ 0 := by rw [hsum]; exact hτne
    have htrdiag : (Work.Models.PSL2.diagUnit u : Matrix (Fin 2) (Fin 2) F).trace
        = (x : Matrix (Fin 2) (Fin 2) F).trace := by
      rw [trace_diagUnit, hsum, hτ]
    obtain ⟨c, hc⟩ := Work.ZassenhausSuzuki.sl2_conj_of_trace_eq (A := x)
      (B := Work.Models.PSL2.diagUnit u) htrdiag.symm htr
    have hx : c⁻¹ * Work.Models.PSL2.diagUnit u * c = x := by rw [← hc]; group
    have hcyc : IsCyclic ↥(Subgroup.centralizer
        ({Work.Models.PSL2.diagUnit u} : Set (Work.Models.SL2 F))) := by
      rw [centralizer_diagUnit_eq_D u hwne]
      exact (Work.Models.PSL2.D_facts (F := F)).2
    have hcard : Nat.card ↥(Subgroup.centralizer
        ({Work.Models.PSL2.diagUnit u} : Set (Work.Models.SL2 F))) = Nat.card F - 1 := by
      rw [centralizer_diagUnit_eq_D u hwne]
      exact (Work.Models.PSL2.D_facts (F := F)).1
    obtain ⟨h1, h2⟩ := key (Work.Models.PSL2.diagUnit u) c (Nat.card F - 1) hx hcyc hcard
    exact ⟨h1, le_of_eq h2.symm⟩
  · -- `X ^ 2 + τX + 1` is irreducible: `x` is conjugate into a Singer cycle
    have hanis : Work.Hering.AppVIII.Anisotropic F τ := by
      by_contra h
      exact hroot (Work.ZassenhausSuzuki.exists_root_of_not_anisotropic h)
    obtain ⟨c, hc⟩ := Work.ZassenhausSuzuki.sl2_conj_companion x htr
    have hc' : c * x * c⁻¹ = Work.ZassenhausSuzuki.SingerModelCycle.alphaSL τ := by
      rw [hc]
      apply Subtype.ext
      rw [Work.ZassenhausSuzuki.SingerModelCycle.alphaSL_coe, ← hτ]
    have hx : c⁻¹ * Work.ZassenhausSuzuki.SingerModelCycle.alphaSL τ * c = x := by
      rw [← hc']; group
    have hcyc : IsCyclic ↥(Subgroup.centralizer
        ({Work.ZassenhausSuzuki.SingerModelCycle.alphaSL τ} :
          Set (Work.Models.SL2 F))) := by
      rw [Work.ZassenhausSuzuki.centralizer_alphaSL hanis]
      exact Work.ZassenhausSuzuki.SingerModelCycle.isCyclic_singerSubgroup hanis
    have hcard : Nat.card ↥(Subgroup.centralizer
        ({Work.ZassenhausSuzuki.SingerModelCycle.alphaSL τ} :
          Set (Work.Models.SL2 F))) = Nat.card F + 1 := by
      rw [Work.ZassenhausSuzuki.centralizer_alphaSL hanis,
        Work.ZassenhausSuzuki.SingerModelCycle.card_singerSubgroup hanis]
    obtain ⟨h1, h2⟩ := key (Work.ZassenhausSuzuki.SingerModelCycle.alphaSL τ) c
      (Nat.card F + 1) hx hcyc hcard
    exact ⟨h1, by rw [h2]; omega⟩

end Work.BSLit.BenderFacts2
