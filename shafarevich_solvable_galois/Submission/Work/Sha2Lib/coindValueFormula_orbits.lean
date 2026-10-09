import Mathlib
import Submission.Work.Sha2Lib.shapiroCocycle_mem
import Submission.Work.Sha2Lib.coindValueFormula_singleOrbit
import Submission.Work.SSGRoute.C6ValueFormula.detection_value
import Submission.Work.Sha2Lib.telescoping_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node `C6`: the orbital value formula of the Shapiro cocycle

This is the "`Σ_u c_u(χ(Frob_u))`" computation of the unramified detector, in the coinduced model
`Rep.coind H.subtype W` (functions on the left `H`-cosets of `Γ`, `H ⊴ Γ`, `W` a trivial `H`-module).

Statement proved here (`Work.Sha2Lib.coindValueFormula_orbits`): if

* `c : Γ → Γ → ↥H` is the multiplication cocycle of a section of `Γ → H\Γ` (`hcmul`, `hcunit`,
  `hcoinv`, as in `Work.Sha2Lib.shapiroCocycle_mem`),
* `y : ↥H →* Multiplicative W.V` is a character,
* `D ≤ Γ`, `d : ↥D`, `f > 0` with `d^f ∈ H`, and the blocks `{x d^j H : j < f}` (`x ∈ X`) partition
  `Γ`,
* `μ` is a `D`-equivariant functional on `Rep.coind H.subtype W` (trivial target),

then `μ` decomposes as one coefficient functional `cw x : W.V →+ M` per block,

  `μ v = Σ_{x ∈ X} cw x (Σ_{j < f} v (x d^j))`,

and the value of `μ` at the Shapiro `1`-cocycle `z_χ = (fun g => y (c g d))` of `y` is the sum of
the telescoped character values, one term per block:

  `μ (z_χ) = Σ_{x ∈ X} cw x (y (c x (d^f)))`.

The single-block instance of the second identity (the telescoping itself) is the proved
`Work.Sha2Lib.coindValueFormula_singleOrbit`; the content added here is the *first* identity — the
orbit decomposition of the functional `μ`, which is what turns a single telescoped value into the
sum over the `D`-orbits of the coordinate set (= the places of the base field `K₁` over the prime).
-/

open CategoryTheory

namespace Work.Sha2Lib

noncomputable section

attribute [local instance 10000] Rep.hV2 Rep.hV1

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-- **The orbital value formula of the Shapiro cocycle** (node `C6`, the `Σ_u c_u(χ(Frob_u))`
computation). -/
theorem coindValueFormula_orbits {Γ : Type} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    {H : Subgroup Γ} (hH : H.Normal)
    (W : Rep.{0} SSGRoute.PTExt.Coeff ↥H) [Finite W]
    (htriv : ∀ (n : ↥H) (x : W.V), W.ρ n x = x)
    (c : Γ → Γ → ↥H)
    (hcmul : ∀ g γ γ' : Γ,
      ((c g (γ * γ') : ↥H) : Γ) = ((c g γ : ↥H) : Γ) * ((c (g * γ) γ' : ↥H) : Γ))
    (hcunit : ∀ g : Γ, ((c g 1 : ↥H) : Γ) = 1)
    (hcoinv : ∀ (g γ : Γ) (n : ↥H), c ((n : Γ) * g) γ = c g γ)
    (y : ↥H →* Multiplicative W.V)
    (D : Subgroup Γ) (d : ↥D) (f : ℕ) (hf : 0 < f)
    (hdH : ((d : Γ)) ^ f ∈ H)
    (X : Finset Γ)
    (hpart : ∀ γ : Γ, ∃! q : Γ × Fin f, q.1 ∈ X ∧ γ * (q.1 * (d : Γ) ^ (q.2 : ℕ))⁻¹ ∈ H)
    (hblock : ∀ x ∈ X, ∀ δ : ↥D, ∃ j : Fin f,
      (x * (δ : Γ)) * (x * (d : Γ) ^ (j : ℕ))⁻¹ ∈ H)
    {M : Type} [AddCommGroup M] [Module SSGRoute.PTExt.Coeff M]
    (μ : Rep.res D.subtype (Rep.coind H.subtype W) ⟶
      Rep.trivial SSGRoute.PTExt.Coeff ↥D M) :
    ∃ cw : Γ → (W.V →+ M),
      (∀ x ∉ X, cw x = 0) ∧
      (∀ v : (Rep.coind H.subtype W).V,
        μ.hom v
          = ∑ x ∈ X, cw x (∑ j ∈ Finset.range f, (v : Γ → W.V) (x * (d : Γ) ^ j))) ∧
      (μ.hom
          (⟨fun g : Γ => Multiplicative.toAdd (y (c g (d : Γ))), by
            intro n g
            show Multiplicative.toAdd (y (c ((n : Γ) * g) (d : Γ)))
              = W.ρ n (Multiplicative.toAdd (y (c g (d : Γ))))
            rw [hcoinv g (d : Γ) n]
            exact (htriv n _).symm⟩ : (Rep.coind H.subtype W).V)
        = ∑ x ∈ X, cw x (Multiplicative.toAdd (y (c x ((d : Γ) ^ f))))) := by
  classical
  -- the kernel of `H.subtype` acts trivially, so the Diracs are available
  have hker : Work.SSGRoute.C6ValueFormula.KerActsTrivially H.subtype W :=
    fun n _ a => htriv n a
  -- ## the value of a Dirac
  have hdirac_val : ∀ (x : Γ) (a : W.V) (g : Γ),
      (Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker x a : Γ → W.V) g
        = if g * x⁻¹ ∈ H then a else 0 := by
    intro x a g
    by_cases h : g * x⁻¹ ∈ H
    · have hwit : H.subtype ⟨g * x⁻¹, h⟩ * x = g := by
        show (g * x⁻¹) * x = g
        group
      rw [Work.SSGRoute.C6ValueFormula.dirac_apply_eq H.subtype W hker x a hwit, if_pos h]
      exact htriv _ a
    · have hnot : ¬ ∃ dd : ↥H, H.subtype dd * x = g := by
        rintro ⟨dd, hdd⟩
        refine h ?_
        have h3 : H.subtype dd = g * x⁻¹ := by
          conv_rhs => rw [← hdd]
          rw [mul_assoc, mul_inv_cancel, mul_one]
        rw [← h3]
        exact dd.2
      rw [Work.SSGRoute.C6ValueFormula.dirac_apply_of_not H.subtype W hker x a hnot,
        if_neg h]
  -- ## invariance of a coinduced element under the left `H`-action
  have hinv : ∀ (v : (Rep.coind H.subtype W).V) (h : ↥H) (g : Γ),
      (v : Γ → W.V) (H.subtype h * g) = (v : Γ → W.V) g := by
    intro v h g
    have hmem := (Representation.mem_coindV H.subtype W.ρ v).mp v.2 h g
    rw [hmem, htriv]
  -- ## the Dirac decomposition of an arbitrary element
  have hdecomp : ∀ v : (Rep.coind H.subtype W).V,
      v = ∑ x ∈ X, ∑ j ∈ Finset.range f,
        Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker (x * (d : Γ) ^ j)
          ((v : Γ → W.V) (x * (d : Γ) ^ j)) := by
    intro v
    apply Subtype.ext
    funext g
    rw [Submodule.coe_sum]
    simp only [Finset.sum_apply, Submodule.coe_sum, hdirac_val]
    obtain ⟨q, hq, huniq⟩ := hpart g
    obtain ⟨x₀, j₀⟩ := q
    obtain ⟨hq1, hq2⟩ := hq
    rw [Finset.sum_eq_single x₀]
    · rw [Finset.sum_eq_single (j₀ : ℕ)]
      · -- the surviving term, and `v` is constant on the left `H`-coset
        rw [if_pos hq2]
        have hgall : H.subtype
              ⟨g * (x₀ * (d : Γ) ^ (j₀ : ℕ))⁻¹, hq2⟩ *
            (x₀ * (d : Γ) ^ (j₀ : ℕ)) = g := by
          show (g * (x₀ * (d : Γ) ^ (j₀ : ℕ))⁻¹) * (x₀ * (d : Γ) ^ (j₀ : ℕ)) = g
          group
        rw [← hgall]
        exact hinv v ⟨g * (x₀ * (d : Γ) ^ (j₀ : ℕ))⁻¹, hq2⟩ (x₀ * (d : Γ) ^ (j₀ : ℕ))
      · intro j hj hne
        rw [if_neg]
        intro hmem
        refine hne (congrArg Fin.val (congrArg Prod.snd
          (huniq (x₀, ⟨j, Finset.mem_range.mp hj⟩) ⟨hq1, hmem⟩)))
      · intro hmem
        exact absurd (Finset.mem_range.mpr j₀.isLt) hmem
    · intro x hx hne
      rw [Finset.sum_eq_zero]
      intro j hj
      rw [if_neg]
      intro hmem
      refine hne (by
        simpa using congrArg Prod.fst
          (huniq (x, ⟨j, Finset.mem_range.mp hj⟩) ⟨hx, hmem⟩))
    · intro hmem
      exact absurd hq1 hmem
  -- ## `μ` on a shifted Dirac only depends on the block
  have hshift : ∀ (x : Γ) (j : ℕ) (a : W.V),
      μ.hom (Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker (x * (d : Γ) ^ j) a)
        = μ.hom (Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker x a) := by
    intro x j a
    have hmem : (d : Γ) ^ j ∈ D := Subgroup.pow_mem D d.2 j
    have h1 : (Rep.res D.subtype (Rep.coind H.subtype W)).ρ ⟨(d : Γ) ^ j, hmem⟩⁻¹
        (Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker x a)
        = Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker (x * (d : Γ) ^ j) a := by
      show (Rep.coind H.subtype W).ρ ((d : Γ) ^ j)⁻¹
        (Work.SSGRoute.C6ValueFormula.dirac H.subtype W hker x a) = _
      rw [coind_rho_dirac W hker ((d : Γ) ^ j)⁻¹ x a, inv_inv]
    rw [← h1, Rep.hom_comm_apply]
    rfl
  -- ## the coefficient functionals, one per block
  let cwf : Γ → (W.V →+ M) := fun x =>
    if x ∈ X then (μ.hom.toAddMonoidHom).comp (diracHom W hker x) else 0
  have hcwf : ∀ x ∈ X, cwf x = (μ.hom.toAddMonoidHom).comp (diracHom W hker x) := by
    intro x hx
    simp only [cwf, if_pos hx]
  -- ## the orbit decomposition of `μ`
  have hmain : ∀ v : (Rep.coind H.subtype W).V,
      μ.hom v = ∑ x ∈ X, cwf x
        (∑ j ∈ Finset.range f, (v : Γ → W.V) (x * (d : Γ) ^ j)) := by
    intro v
    conv_lhs => rw [hdecomp v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [map_sum]
    rw [hcwf x hx, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hshift x j]
    rfl
  refine ⟨cwf, fun x hx => by simp only [cwf, if_neg hx], hmain, ?_⟩
  -- ## the value at the Shapiro cocycle
  rw [hmain]
  refine Finset.sum_congr rfl fun x hx => ?_
  congr 1
  -- the telescoping, exactly as in `coindValueFormula_singleOrbit`
  have htelH : ((List.range f).map (fun j => c (x * (d : Γ) ^ j) (d : Γ))).prod
      = c x ((d : Γ) ^ f) := by
    apply Subtype.val_injective
    change H.subtype ((List.range f).map (fun j => c (x * (d : Γ) ^ j) (d : Γ))).prod
      = H.subtype (c x ((d : Γ) ^ f))
    rw [map_list_prod, List.map_map]
    exact Work.Sha2Lib.telescoping_pow c hcmul hcunit x (d : Γ) f
  have htelY : ((List.range f).map
      (fun j => y (c (x * (d : Γ) ^ j) (d : Γ)))).prod = y (c x ((d : Γ) ^ f)) := by
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
    have h2 := congrArg Multiplicative.toAdd key
    rwa [toAdd_prod] at h2
  exact htelA

end

end Work.Sha2Lib
