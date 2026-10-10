import Mathlib.GroupTheory.Nilpotent
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Submission.Work.Sha2Lib.coindValueFormula_singleOrbit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGcrux

open Work.SSGRoute.C6ValueFormula

/-!
# Detection is invariant under the double coset `D · N`

Two group-theoretic facts about the Dirac elements `δ_{x,a}` of the coinduced module
`coInd_N^Γ W` are needed:

* `diracApply` — for a coefficient module `W` on which `↥N` acts trivially, the Dirac at `x` with
  value `a` is the function `g ↦ if g * x⁻¹ ∈ N then a else 0` (the pointwise form of
  `Work.SSGcrux.diracSubtypeApply`, with the `KerActsTrivially` witness kept as a parameter);
* `diracCosetEq` — consequently two Diracs with the same value and the same left `N`-coset
  coincide: `δ_{x',a} = δ_{x,a}` as soon as `x' * x⁻¹ ∈ N`.

Together with the `D`-equivariance of a functional with trivial coefficients
(`Work.Sha2Lib.coind_rho_dirac` plus `Rep.hom_comm_apply`) these give the target
`Work.SSGcrux.muDirac_ne_zero_of_doubleCoset`.
-/

/-- **The value of a Dirac at a coset.**  For a subgroup `H ≤ Γ`, a representation `W` of `↥H` on
which `↥H` acts trivially, and any witness `hker` of `KerActsTrivially H.subtype W`, the Dirac
element of `coInd_H^Γ W` at `x` with value `a` takes the value `a` exactly on the left coset
`H x` (spelled `g * x⁻¹ ∈ H`) and `0` elsewhere. -/
theorem diracApply {Γ : Type} [Group Γ] [Fintype Γ] [DecidableEq Γ] {H : Subgroup Γ}
    [DecidablePred (· ∈ H)]
    (W : Rep.{0} SSGRoute.PTExt.Coeff ↥H) (htriv : ∀ (n : ↥H) (x : W.V), W.ρ n x = x)
    (hker : KerActsTrivially H.subtype W) (x : Γ) (a : W.V) (g : Γ) :
    (Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker x a).1 g
      = if g * x⁻¹ ∈ H then a else 0 := by
  by_cases hg : g * x⁻¹ ∈ H
  · rw [if_pos hg]
    have hd : H.subtype ⟨g * x⁻¹, hg⟩ * x = g := by
      rw [Subgroup.subtype_apply]; group
    rw [dirac_apply_eq H.subtype W hker x a hd]
    exact htriv ⟨g * x⁻¹, hg⟩ a
  · rw [if_neg hg]
    rw [dirac_apply_of_not H.subtype W hker x a]
    rintro ⟨d, hd⟩
    refine hg ?_
    have hgd : g * x⁻¹ = (d : Γ) := by rw [← hd, Subgroup.subtype_apply]; group
    rw [hgd]; exact d.2

/-- **The Dirac depends only on the left `H`-coset of its index** (and its value), for a coefficient
module with trivial `↥H`-action: if `x' * x⁻¹ ∈ H` then `δ_{x',a} = δ_{x,a}`. -/
theorem diracCosetEq {Γ : Type} [Group Γ] [Fintype Γ] [DecidableEq Γ] {H : Subgroup Γ}
    [DecidablePred (· ∈ H)]
    (W : Rep.{0} SSGRoute.PTExt.Coeff ↥H) (htriv : ∀ (n : ↥H) (x : W.V), W.ρ n x = x)
    (hker : KerActsTrivially H.subtype W) {x x' : Γ} (hx : x' * x⁻¹ ∈ H) (a : W.V) :
    Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker x' a
      = Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker x a := by
  apply Subtype.ext
  funext γ
  rw [diracApply W htriv hker x' a γ, diracApply W htriv hker x a γ]
  by_cases hg : γ * x⁻¹ ∈ H
  · have hgt : γ * x'⁻¹ ∈ H := by
      have he : γ * x'⁻¹ = γ * x⁻¹ * (x * x'⁻¹) := by group
      rw [he]
      exact H.mul_mem hg (by simpa using H.inv_mem hx)
    rw [if_pos hg, if_pos hgt]
  · have hgt : ¬ γ * x'⁻¹ ∈ H := by
      intro hh
      refine hg ?_
      have he : γ * x⁻¹ = γ * x'⁻¹ * (x' * x⁻¹) := by group
      rw [he]
      exact H.mul_mem hh hx
    rw [if_neg hg, if_neg hgt]

/-- **Detection is invariant under the double coset `D · N` of `Γ`.** For `N ⊴ Γ`, a subgroup
`D ≤ Γ`, a trivial coefficient module `𝔽_p` for `↥N` and a `D`-equivariant functional
`μ : res_D (coInd_N^Γ 𝔽_p) ⟶ trivial`, the value of `μ` at the coset Dirac `δ_{N g, 1}` is non-zero
whenever `μ` is non-zero at `δ_{N γ₀, 1}` and `g = γ₀ δ n` with `δ ∈ D`, `n ∈ N`. -/
theorem muDirac_ne_zero_of_doubleCoset {Γ : Type} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    {p : ℕ} [Fact p.Prime] (N : Subgroup Γ) [N.Normal] (D : Subgroup Γ)
    {M : Type} [AddCommGroup M] [Module SSGRoute.PTExt.Coeff M]
    (μ : Rep.res D.subtype (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p))) ⟶
      Rep.trivial SSGRoute.PTExt.Coeff ↥D M)
    (γ₀ g : Γ)
    (hμ : μ.hom (Work.SSGRoute.C6ValueFormula.dirac N.subtype
        (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)) (fun _ _ _ => rfl) γ₀ 1) ≠ 0)
    (h : ∃ δ ∈ D, ∃ n ∈ N, γ₀ * (δ * n) = g) :
    μ.hom (Work.SSGRoute.C6ValueFormula.dirac N.subtype
        (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)) (fun _ _ _ => rfl) g 1) ≠ 0 := by
  classical
  obtain ⟨δ, hδD, n, hnN, hgn⟩ := h
  -- **Step 1.** the factor `n ∈ N` can be absorbed into the left `N`-coset of the index `γ₀ * δ`
  have hcoset : Work.SSGRoute.C6ValueFormula.dirac N.subtype
        (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)) (fun _ _ _ => rfl)
        (γ₀ * (δ * n)) 1
      = Work.SSGRoute.C6ValueFormula.dirac N.subtype
        (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)) (fun _ _ _ => rfl)
        (γ₀ * δ) 1 := by
    refine diracCosetEq _ (fun _ _ => rfl) _ ?_ 1
    have he : γ₀ * (δ * n) * (γ₀ * δ)⁻¹ = γ₀ * (δ * n * δ⁻¹) * γ₀⁻¹ := by group
    rw [he]
    exact (inferInstance : N.Normal).conj_mem _
      ((inferInstance : N.Normal).conj_mem _ hnN δ) γ₀
  -- **Step 2.** `μ` cannot distinguish the Diracs along a `D`-orbit: the `D`-action on the
  -- coinduced module translates the index, and the target carries the trivial action
  have hshift : μ.hom (Work.SSGRoute.C6ValueFormula.dirac N.subtype
        (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)) (fun _ _ _ => rfl)
        (γ₀ * δ) 1)
      = μ.hom (Work.SSGRoute.C6ValueFormula.dirac N.subtype
        (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)) (fun _ _ _ => rfl) γ₀ 1) := by
    have hcomm : ∀ v : (Rep.coind N.subtype
        (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p))).V,
        μ.hom ((Rep.res D.subtype (Rep.coind N.subtype
          (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)))).ρ ⟨δ, hδD⟩ v) = μ.hom v := by
      intro v
      rw [Rep.hom_comm_apply]
      rfl
    calc μ.hom (Work.SSGRoute.C6ValueFormula.dirac N.subtype
          (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)) (fun _ _ _ => rfl) (γ₀ * δ) 1)
        = μ.hom ((Rep.res D.subtype (Rep.coind N.subtype
            (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)))).ρ ⟨δ, hδD⟩
            (Work.SSGRoute.C6ValueFormula.dirac N.subtype
              (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)) (fun _ _ _ => rfl) (γ₀ * δ) 1)) :=
          (hcomm _).symm
      _ = μ.hom (Work.SSGRoute.C6ValueFormula.dirac N.subtype
            (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)) (fun _ _ _ => rfl) γ₀ 1) := by
          congr 1
          change (Rep.coind N.subtype
              (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p))).ρ ((⟨δ, hδD⟩ : ↥D) : Γ)
              (Work.SSGRoute.C6ValueFormula.dirac N.subtype
                (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)) (fun _ _ _ => rfl) (γ₀ * δ) 1)
            = Work.SSGRoute.C6ValueFormula.dirac N.subtype
                (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)) (fun _ _ _ => rfl) γ₀ 1
          rw [Work.Sha2Lib.coind_rho_dirac
            (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)) (fun _ _ _ => rfl)
            ((⟨δ, hδD⟩ : ↥D) : Γ) (γ₀ * δ) 1]
          rw [show ((⟨δ, hδD⟩ : ↥D) : Γ) = δ from rfl, mul_inv_cancel_right]
  rw [← hgn, hcoset, hshift]
  exact hμ

end Work.SSGcrux
