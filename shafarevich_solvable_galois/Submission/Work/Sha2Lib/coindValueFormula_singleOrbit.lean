import Mathlib
import Submission.Work.SSGRoute.C6ValueFormula.coset_sum
import Submission.Work.SSGRoute.C6ValueFormula.detection_value
import Submission.Work.Sha2Lib.telescoping_pow
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.Sha2Lib.shapiroCocycle_mem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Sha2Lib

open CategoryTheory

/-! ## Auxiliary lemmas for the orbit value formula

The orbit formula is assembled from three pieces:

* `coind_rho_dirac` — the translation rule `γ • δ_{x,a} = δ_{x γ⁻¹, a}` for the Dirac elements of
  the coinduced module;
* `nu_rho` / `nu_dirac_shift` — the `D`-equivariance of a functional with trivial coefficients makes
  its value on a Dirac independent of the point of the `D`-orbit;
* `diracHom` — the Dirac at a fixed point is additive in its value, so it commutes with finite sums.
-/

/-- **The translation rule for Dirac elements.**  In the coinduced `Γ`-module
`Rep.coind H.subtype W` the action of `γ : Γ` is right translation of the argument,
`(γ • f) g = f (g * γ)`, so it sends the Dirac at the coset of `x` to the Dirac at the coset of
`x * γ⁻¹` (with the same value). -/
lemma coind_rho_dirac {Γ : Type} [Group Γ] [Fintype Γ] [DecidableEq Γ] {H : Subgroup Γ}
    (W : Rep.{0} SSGRoute.PTExt.Coeff ↥H)
    (hker : Work.SSGRoute.C6ValueFormula.KerActsTrivially H.subtype W)
    (g x : Γ) (a : W.V) :
    (Rep.coind H.subtype W).ρ g (Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker x a)
      = Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker (x * g⁻¹) a := by
  ext γ
  rw [Work.Sha2Lib.coind_subtype_ρ_apply]
  by_cases h : ∃ e : ↥H, H.subtype e * x = γ * g
  · obtain ⟨e, he⟩ := h
    have h2 : H.subtype e * (x * g⁻¹) = γ := by
      rw [← mul_assoc, he, mul_inv_cancel_right]
    rw [Work.SSGRoute.C6ValueFormula.dirac_apply_eq H.subtype W hker x a he,
        Work.SSGRoute.C6ValueFormula.dirac_apply_eq H.subtype W hker (x * g⁻¹) a h2]
  · have h' : ¬∃ e : ↥H, H.subtype e * (x * g⁻¹) = γ := by
      rintro ⟨e, he⟩
      refine h ⟨e, ?_⟩
      calc H.subtype e * x = (H.subtype e * (x * g⁻¹)) * g := by group
        _ = γ * g := by rw [he]
    rw [Work.SSGRoute.C6ValueFormula.dirac_apply_of_not H.subtype W hker x a h,
        Work.SSGRoute.C6ValueFormula.dirac_apply_of_not H.subtype W hker (x * g⁻¹) a h']

/-- **A `D`-equivariant functional with trivial coefficients is invariant under the `D`-action.**
Indeed `ν (d • v) = d • ν v = ν v` because the target module carries the trivial action. -/
lemma nu_rho {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ] [Fintype Γ] {H : Subgroup Γ}
    (W : Rep.{0} SSGRoute.PTExt.Coeff ↥H)
    (D : Subgroup Γ)
    (ν : Rep.res D.subtype (Rep.coind H.subtype W) ⟶
      Rep.trivial SSGRoute.PTExt.Coeff ↥D (ZMod p))
    (dd : ↥D) (v : (Rep.coind H.subtype W).V) :
    ν ((Rep.res D.subtype (Rep.coind H.subtype W)).ρ dd v) = ν v := by
  rw [Rep.hom_comm_apply]
  rfl

/-- **The value of `ν` on a Dirac is constant along a `D`-orbit.**  Combining the translation rule
`coind_rho_dirac` with the invariance `nu_rho`: for `dd : D` and `x : Γ`,

`ν (δ_{x * dd, a}) = ν (δ_{x, a})`. -/
lemma nu_dirac_shift {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    {H : Subgroup Γ}
    (W : Rep.{0} SSGRoute.PTExt.Coeff ↥H)
    (hker : Work.SSGRoute.C6ValueFormula.KerActsTrivially H.subtype W)
    (D : Subgroup Γ)
    (ν : Rep.res D.subtype (Rep.coind H.subtype W) ⟶
      Rep.trivial SSGRoute.PTExt.Coeff ↥D (ZMod p))
    (dd : ↥D) (x : Γ) (a : W.V) :
    ν (Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker (x * (dd : Γ)) a)
      = ν (Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker x a) := by
  calc ν (Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker (x * (dd : Γ)) a)
      = ν ((Rep.res D.subtype (Rep.coind H.subtype W)).ρ dd
            (Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker (x * (dd : Γ)) a)) :=
          (nu_rho W D ν dd _).symm
    _ = ν (Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker x a) := by
          congr 1
          have hρ : (Rep.coind H.subtype W).ρ (dd : Γ)
              (Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker (x * (dd : Γ)) a)
              = Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker x a := by
            rw [coind_rho_dirac W hker (dd : Γ) (x * (dd : Γ)) a]
            congr 1
            rw [mul_inv_cancel_right]
          exact hρ

/-- The Dirac at a fixed point `x`, as an additive map in its value. -/
noncomputable def diracHom {Γ : Type} [Group Γ] [Fintype Γ] [DecidableEq Γ] {H : Subgroup Γ}
    (W : Rep.{0} SSGRoute.PTExt.Coeff ↥H)
    (hker : Work.SSGRoute.C6ValueFormula.KerActsTrivially H.subtype W) (x : Γ) :
    W.V →+ (Rep.coind H.subtype W).V where
  toFun := Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker x
  map_zero' := Work.SSGRoute.C6ValueFormula.dirac_zero H.subtype W hker x
  map_add' := Work.SSGRoute.C6ValueFormula.dirac_add H.subtype W hker x

/-- **The value formula of the unramified detector on one orbit of the coinduced coordinate set.**

Let `Γ` be a finite group, `H ≤ Γ` a subgroup, `W` a finite `H`-module on which `H` acts
*trivially*, `c : Γ → Γ → ↥H` the multiplication cocycle of a section of `Γ → H\Γ` (hypotheses
`hcmul`, `hcunit`, as in `Work.Sha2Lib.shapiroCocycle_mem` / `Work.Sha2Lib.telescoping_pow`), and
`y : ↥H →* Multiplicative W.V` a character.  Let `D ≤ Γ` be a subgroup with `d ∈ D` and let
`ν : Rep.res D.subtype (Rep.coind H.subtype W) ⟶ trivial (ZMod p)` be a `D`-equivariant functional
with values in the trivial module.

Then for every `x ∈ Γ` and every `f`, the sum of the values of `ν` on the Dirac elements along the
`d`-orbit of `x` collapses to the single Dirac at `x` evaluated at the *telescoped* character value
`y (c x (d ^ f))`:

`Σ_{j<f} ν (δ_{x d^j, y (c (x d^j) d)}) = ν (δ_{x, y (c x (d^f))})`.

This is the algebra of the `d ↦ μ (h d)` value formula of node `C6`: the Dirac decomposition
`Work.SSGRoute.C6ValueFormula.coind_functional_eq_cosetSum` writes `ν` applied to a coinduced element
as a sum of Dirac values, the `D`-equivariance of `ν` makes the Dirac coefficients constant along the
`d`-orbits, and `Work.Sha2Lib.telescoping_pow` collapses the orbit sum. -/
theorem coindValueFormula_singleOrbit {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ] [Fintype Γ]
    {H : Subgroup Γ} (W : Rep.{0} SSGRoute.PTExt.Coeff ↥H) [Finite W]
    (htriv : ∀ (n : ↥H) (x : W), W.ρ n x = x)
    (c : Γ → Γ → ↥H)
    (hcmul : ∀ g γ γ' : Γ,
      ((c g (γ * γ') : ↥H) : Γ) = ((c g γ : ↥H) : Γ) * ((c (g * γ) γ' : ↥H) : Γ))
    (hcunit : ∀ g : Γ, ((c g 1 : ↥H) : Γ) = 1)
    (y : ↥H →* Multiplicative W.V)
    (hker : Work.SSGRoute.C6ValueFormula.KerActsTrivially H.subtype W)
    (D : Subgroup Γ) (d : ↥D)
    (ν : Rep.res D.subtype (Rep.coind H.subtype W) ⟶
      Rep.trivial SSGRoute.PTExt.Coeff ↥D (ZMod p))
    (x : Γ) (f : ℕ) :
    (∑ j ∈ Finset.range f,
        ν (Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker (x * (d : Γ) ^ j)
            (Multiplicative.toAdd (y (c (x * (d : Γ) ^ j) (d : Γ))))))
      = ν (Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker x
            (Multiplicative.toAdd (y (c x ((d : Γ) ^ f))))) := by
  classical
  -- Step 1: the `D`-equivariance identifies each orbit term with the term at the base point `x`.
  have hterm : ∀ j ∈ Finset.range f,
      ν (Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker (x * (d : Γ) ^ j)
            (Multiplicative.toAdd (y (c (x * (d : Γ) ^ j) (d : Γ)))))
        = ν (Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker x
            (Multiplicative.toAdd (y (c (x * (d : Γ) ^ j) (d : Γ))))) := by
    intro j _
    exact nu_dirac_shift W hker D ν ((d : ↥D) ^ j) x
      (Multiplicative.toAdd (y (c (x * (d : Γ) ^ j) (d : Γ))))
  rw [Finset.sum_congr rfl hterm]
  -- Step 2: telescoping of the Shapiro cocycle along the orbit, in `↥H`.
  have htelH : ((List.range f).map (fun j => c (x * (d : Γ) ^ j) (d : Γ))).prod
      = c x ((d : Γ) ^ f) := by
    apply Subtype.val_injective
    change H.subtype ((List.range f).map (fun j => c (x * (d : Γ) ^ j) (d : Γ))).prod
      = H.subtype (c x ((d : Γ) ^ f))
    rw [map_list_prod, List.map_map]
    exact Work.Sha2Lib.telescoping_pow c hcmul hcunit x (d : Γ) f
  have htelY : ((List.range f).map
        (fun j => y (c (x * (d : Γ) ^ j) (d : Γ)))).prod
      = y (c x ((d : Γ) ^ f)) := by
    rw [show (List.map (fun j => y (c (x * (d : Γ) ^ j) (d : Γ))) (List.range f))
        = (List.map (⇑y ∘ fun j => c (x * (d : Γ) ^ j) (d : Γ)) (List.range f)) from rfl]
    rw [List.prod_map_hom]
    exact congrArg y htelH
  have htelA : (∑ j ∈ Finset.range f,
        Multiplicative.toAdd (y (c (x * (d : Γ) ^ j) (d : Γ))))
      = Multiplicative.toAdd (y (c x ((d : Γ) ^ f))) := by
    have key : (∏ j ∈ Finset.range f, y (c (x * (d : Γ) ^ j) (d : Γ)))
        = y (c x ((d : Γ) ^ f)) := by
      rw [← List.toFinset_range f]
      rw [List.prod_toFinset (fun j => y (c (x * (d : Γ) ^ j) (d : Γ))) (List.nodup_range)]
      exact htelY
    have := congrArg Multiplicative.toAdd key
    rwa [toAdd_prod] at this
  -- Step 3: `ν` is additive and the Dirac at a fixed point is additive in its value, so the sum of
  -- the Dirac values is the Dirac of the sum, which the telescoping evaluates.
  have hdirac_sum : (∑ j ∈ Finset.range f,
        Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker x
          (Multiplicative.toAdd (y (c (x * (d : Γ) ^ j) (d : Γ)))))
      = Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker x
          (∑ j ∈ Finset.range f,
            Multiplicative.toAdd (y (c (x * (d : Γ) ^ j) (d : Γ)))) := by
    exact (map_sum (diracHom W hker x)
      (fun j => Multiplicative.toAdd (y (c (x * (d : Γ) ^ j) (d : Γ))))
      (Finset.range f)).symm
  have h2 : (∑ j ∈ Finset.range f,
        ν (Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker x
          (Multiplicative.toAdd (y (c (x * (d : Γ) ^ j) (d : Γ))))))
      = ν (∑ j ∈ Finset.range f,
        Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker x
          (Multiplicative.toAdd (y (c (x * (d : Γ) ^ j) (d : Γ))))) := by
    exact (map_sum ν.hom
      (fun j => Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker x
        (Multiplicative.toAdd (y (c (x * (d : Γ) ^ j) (d : Γ)))))
      (Finset.range f)).symm
  rw [h2, hdirac_sum, htelA]

end Work.Sha2Lib
