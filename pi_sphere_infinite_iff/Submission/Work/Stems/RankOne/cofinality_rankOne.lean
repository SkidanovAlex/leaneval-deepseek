import Mathlib
import Submission.Work.Stems.RankOneClauses
import Submission.Work.Stems.HurewiczFirstDegree
import Submission.Work.Serre.OneCell.RatAdditivity
import Submission.Work.Stems.RankOne.torsion_of_one_tmul_eq_zero
import Submission.Work.Stems.RankOne.exists_nsmul_eq_zsmul_of_ker_torsion

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Cofinality of a rank-one homotopy group

`Work.Stems.RankOne.cofinality_rankOne`: if `X` has vanishing homotopy groups in degrees `< n`
(`n ≥ 2`) and `Hₙ(X;ℚ) ≅ ℚ`, then every class of `πₙ(X,x₀)` is *commensurable* with any class of
infinite order: for `α` of infinite order and every `γ` there are `m > 0` and `k : ℤ` with
`γ ^ m = α ^ k`.

The route is the rational Hurewicz theorem in the first non-vanishing degree:
`Work.Stems.hurewiczMapN` is an isomorphism `πₙ(X,x₀) → Hₙ(X;ℤ)` in degree `n ≥ 2`
(`Work.Stems.hurewicz_first_degree`), and `Hₙ(X;ℤ)` is transported to `ℚ` by the rank-one
rational homology (`Work.Serre.OneCell.ratHomologyBaseChange` together with `hH`), giving an
additive functional `φ` whose kernel is exactly the torsion subgroup
(`Work.Stems.RankOne.torsion_of_one_tmul_eq_zero`).  The rank-one commensurability statement for
such a functional is `Work.Stems.RankOne.exists_nsmul_eq_zsmul_of_ker_torsion`, applied to the
Hurewicz images of `α` and `γ`; the conclusion is transported back to `πₙ(X,x₀)` through the
additivity of the Hurewicz map.
-/

open TensorProduct CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Stems.RankOne

noncomputable section

theorem cofinality_rankOne {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n) {X : Type} [TopologicalSpace X]
    (x₀ : X)
    (hconn : ∀ i : ℕ, i < n → Subsingleton (HomotopyGroup (Fin i) X x₀))
    (hH : Nonempty (Work.Serre.ratH (TopCat.of X) n ≅ ModuleCat.of ℚ ℚ))
    {α : HomotopyGroup (Fin n) X x₀} (hα : ∀ m : ℕ, 0 < m → α ^ m ≠ 1) :
    ∀ γ : HomotopyGroup (Fin n) X x₀, ∃ m : ℕ, 0 < m ∧ ∃ k : ℤ, γ ^ m = α ^ k := by
  -- work in the successor degree `n = p + 1`, so that the Hurewicz additivity statements apply
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = p + 1 :=
    ⟨n - 1, (Nat.sub_add_cancel (by omega : 1 ≤ n)).symm⟩
  intro γ
  -- the integral homology of `X` in degree `p + 1`, and the rank-one functional on it
  let Hn : ModuleCat ℤ := (Work.Cohomology.singularChains ℤ (TopCat.of X)).homology (p + 1)
  obtain ⟨hHiso⟩ := hH
  let e : Work.Serre.OneCell.ratF.obj Hn ≅ ModuleCat.of ℚ ℚ :=
    (Work.Serre.OneCell.ratHomologyBaseChange (TopCat.of X) (p + 1)).symm ≪≫ hHiso
  let psi : ↥Hn →ₗ[ℤ] ↥(Work.Serre.OneCell.ratF.obj Hn) := TensorProduct.mk ℤ ℚ ↥Hn (1 : ℚ)
  let phi : ↥Hn →+ ℚ := ((e.hom.hom.restrictScalars ℤ).comp psi).toAddMonoidHom
  -- the Hurewicz map in degree `p + 1`
  let hN : HomotopyGroup (Fin (p + 1)) X x₀ → ↥Hn :=
    Work.Stems.hurewiczMapN (p + 1) (Nat.succ_le_succ (Nat.zero_le p)) x₀
  have hN_one : hN 1 = 0 := by
    have h2 := Work.Stems.hurewiczMapN_mul p x₀ (1 : HomotopyGroup (Fin (p + 1)) X x₀) 1
    simp only [mul_one] at h2
    exact add_left_cancel (by rw [add_zero]; exact h2.symm)
  have hinj : Function.Injective hN :=
    Work.Stems.Hur2c.hurewiczMapN_injective_firstDegree (p + 1) hn x₀ hconn
  let hHom : Additive (HomotopyGroup (Fin (p + 1)) X x₀) →+ ↥Hn :=
    { toFun := fun a => hN a.toMul
      map_zero' := hN_one
      map_add' := fun a b => Work.Stems.hurewiczMapN_mul p x₀ a.toMul b.toMul }
  have hHom_inj : Function.Injective hHom := by
    intro a b hab
    have h : a.toMul = b.toMul := hinj hab
    rw [← ofMul_toMul a, ← ofMul_toMul b, h]
  -- the kernel of `phi` is the torsion subgroup of `Hₙ(X;ℤ)`
  have hker : ∀ b : ↥Hn, phi b = 0 → ∃ N : ℕ, 0 < N ∧ N • b = 0 := by
    intro b hb
    have hinj_e : Function.Injective e.hom.hom := by
      have hmono : Mono e.hom := inferInstance
      rwa [ModuleCat.mono_iff_injective] at hmono
    have h2 : e.hom.hom (psi b) = e.hom.hom 0 := by rw [map_zero]; exact hb
    have h3 : psi b = 0 := hinj_e h2
    have h3' : (1 : ℚ) ⊗ₜ[ℤ] b = 0 := h3
    -- align the two `ℤ`-module structures (`ModuleCat`'s and the canonical one)
    rw [show Hn.isModule = AddCommGroup.toIntModule ↥Hn from Subsingleton.elim _ _] at h3'
    exact torsion_of_one_tmul_eq_zero b h3'
  -- `phi` does not vanish on the Hurewicz image of `α`, which is therefore not torsion
  have hne : phi (hHom (Additive.ofMul α)) ≠ 0 := by
    intro h0
    obtain ⟨N, hNpos, hNzero⟩ := hker (hHom (Additive.ofMul α)) h0
    have h4 : hHom (N • Additive.ofMul α) = 0 := by rw [map_nsmul, hNzero]
    have h5 : N • Additive.ofMul α = 0 := hHom_inj (by rw [h4, map_zero])
    have h6 : α ^ N = 1 := by
      apply Additive.ofMul.injective
      rw [ofMul_pow, ofMul_one, h5]
    exact hα N hNpos h6
  -- the commensurability statement in `Hₙ(X;ℤ)`
  obtain ⟨m, hm, k, hk⟩ :=
    exists_nsmul_eq_zsmul_of_ker_torsion phi hker hne (hHom (Additive.ofMul γ))
  refine ⟨m, hm, k, ?_⟩
  have h9 : m • Additive.ofMul γ = k • Additive.ofMul α := by
    apply hHom_inj
    rw [map_nsmul, map_zsmul]
    exact hk
  have h10 : Additive.ofMul (γ ^ m) = Additive.ofMul (α ^ k) := by
    rw [ofMul_pow, ofMul_zpow, h9]
  exact Additive.ofMul.injective h10

end

end Work.Stems.RankOne
