import Mathlib
import Submission.Work.Grun.Basic
import Submission.Work.BSHallW.WeakClosure
import Submission.Work.BSHallW.exists_sylow_le_sup
import Submission.Work.BSHallW.le_smul_sylow_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSHallW.CosetKernel.not_le_cosetKernel_of_not_mem_normalizer`

Let `G` be a finite group, `p` a prime, `S` a Sylow `p`-subgroup of `G` and `A ≤ S` a subgroup that
is *weakly closed* in `S` with respect to `G`:

`hwc : ∀ g : G, A^g ≤ S → A^g = A`   (`A^g = A.map (MulAut.conj g).toMonoidHom = g A g⁻¹`).

Then Hall's coset kernel `K(x) = cosetKernel N_G(A) S x` (the kernel of the action of `S` on the
cosets of `N_G(A)` inside the double coset `S x N_G(A)`) does **not** contain `A` as soon as
`x ∉ N_G(A)`.

The proof: if `A ≤ K(x)` then, testing the defining condition with the coset `1 * x`, one has
`x⁻¹ A x ≤ N_G(A)`.  Put `B := x⁻¹ A x`, so that `B ≤ N_G(A)` and `B` is again a `p`-group.  Then
`A ⊔ B` is a `p`-subgroup (because `B` normalizes `A`), so it lies in a Sylow `p`-subgroup `T`; by
Sylow's conjugacy theorem `T = g • S` for some `g`.  Descending along the conjugation,
`A^{g⁻¹} ≤ S` and `A^{g⁻¹ x⁻¹} ≤ S`, so weak closure gives `g⁻¹ ∈ N_G(A)` and `g⁻¹ x⁻¹ ∈ N_G(A)`;
hence `x ∈ N_G(A)`, a contradiction.
-/

open scoped Pointwise

namespace Work.BSHallW.CosetKernel

theorem not_le_cosetKernel_of_not_mem_normalizer {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (S : Sylow p G) {A : Subgroup G} (hAS : A ≤ (S : Subgroup G))
    (hwc : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) →
      A.map (MulAut.conj g).toMonoidHom = A)
    {x : G} (hx : x ∉ Subgroup.normalizer (A : Set G)) :
    ¬ A ≤ Work.Grun.cosetKernel (Subgroup.normalizer (A : Set G)) (S : Subgroup G) x := by
  intro hle
  -- Step 1: testing `A ≤ K(x)` against the coset `1 * x` gives `x⁻¹ A x ≤ N_G(A)`.
  have hBleN : A.map (MulAut.conj x⁻¹).toMonoidHom ≤ Subgroup.normalizer (A : Set G) := by
    intro b hb
    rw [Subgroup.mem_map] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    have hk := (Work.Grun.mem_cosetKernel.mp (hle ha)).2 1 S.one_mem
    simpa [MulAut.conj_apply] using hk
  -- `x⁻¹ A x` is a conjugate of `A ≤ S`, hence a `p`-subgroup.
  have hBp : IsPGroup p (A.map (MulAut.conj x⁻¹).toMonoidHom) :=
    (S.isPGroup'.to_le hAS).map (MulAut.conj x⁻¹).toMonoidHom
  -- Step 2: `A` and `x⁻¹ A x` lie in a common Sylow `p`-subgroup `T`, i.e. `T = g • S`.
  obtain ⟨T, hAT, hBT⟩ := Work.BSHallW.exists_sylow_le_sup S hAS hBp hBleN
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  have hgA : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ (S : Subgroup G) :=
    (Work.BSHallW.le_smul_sylow_iff S g A).mp (by rwa [hg])
  have hgB : (A.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom
      ≤ (S : Subgroup G) :=
    (Work.BSHallW.le_smul_sylow_iff S g _).mp (by rwa [hg])
  -- Step 3: weak closure turns these inclusions into normality statements.
  have hgn : g⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hwc g⁻¹ hgA)
  have hcomp : (A.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom
      = A.map (MulAut.conj (g⁻¹ * x⁻¹)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext a
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have hgB' : A.map (MulAut.conj (g⁻¹ * x⁻¹)).toMonoidHom ≤ (S : Subgroup G) := by
    rwa [← hcomp]
  have hgxn : g⁻¹ * x⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hwc (g⁻¹ * x⁻¹) hgB')
  -- Step 4: conclude `x ∈ N_G(A)`, contradicting `hx`.
  have hxinv : x⁻¹ ∈ Subgroup.normalizer (A : Set G) := by
    have h : x⁻¹ = (g⁻¹)⁻¹ * (g⁻¹ * x⁻¹) := by group
    rw [h]
    exact mul_mem (inv_mem hgn) hgxn
  exact hx (by simpa using inv_mem hxinv)

end Work.BSHallW.CosetKernel
