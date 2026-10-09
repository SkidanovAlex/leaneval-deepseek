import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.Sha2Lib.shapiroCocycle_mem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.TatePoitouRoute

open Classical

/-!
# Existence of the Shapiro cocycle datum `(c, z)`

For a finite group `Γ`, a subgroup `H ≤ Γ`, and an `H`-representation `W` on which `H` acts
trivially, this file constructs:

* a function `c : Γ → Γ → ↥H` obtained from a *normalised left transversal* `sect : Γ → Γ`
  of `H \ Γ` by `c g γ = κ g * (κ (g * γ))⁻¹`, where `κ x = ⟨sect x * x⁻¹, _⟩`.  It satisfies
  the multiplicative telescoping identity `c g (γ * γ') = c g γ * c (g * γ) γ'`, the unit
  condition `c g 1 = 1`, invariance `c (n * g) γ = c g γ` under left multiplication by `n ∈ H`,
  and surjectivity `∀ n, ∃ g γ, c g γ = n`;
* the associated `1`-cocycle `z` of the coinduced `Γ`-module `Rep.coind H.subtype W` with
  `(z γ) g = y (c g γ)`, using `Work.Sha2Lib.shapiroCocycle_mem`.

The transversal `sect` is built from the setoid of left cosets `H x`; it is normalised so that
`sect x = 1` for `x ∈ H` (in particular `sect 1 = 1`), which is what makes the surjectivity
statement true.
-/

section Construction

variable {Γ : Type} [Group Γ] (H : Subgroup Γ)

/-- The left-coset relation `y ∈ H x`. -/
def cosetRel (x y : Γ) : Prop := ∃ n : ↥H, (n : Γ) * x = y

/-- The setoid whose classes are the left cosets `H x`. -/
def cosetSetoid : Setoid Γ where
  r := cosetRel H
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x; exact ⟨1, by simp⟩
    · intro x y h; obtain ⟨n, hn⟩ := h
      exact ⟨n⁻¹, by rw [Subgroup.coe_inv, ← hn]; group⟩
    · intro x y z h1 h2; obtain ⟨n, hn⟩ := h1; obtain ⟨m, hm⟩ := h2
      exact ⟨m * n, by rw [Subgroup.coe_mul, mul_assoc, hn, hm]⟩

/-- A normalised left transversal of `H \ Γ`: `sect x` is a representative of the coset `H x`,
equal to `1` whenever `x ∈ H`. -/
noncomputable def sect (x : Γ) : Γ :=
  if x ∈ H then 1 else Quotient.out (Quotient.mk (cosetSetoid H) x)

/-- Elements in the same left coset have the same image under `sect`. -/
lemma mk_const (n : ↥H) (x : Γ) :
    Quotient.mk (cosetSetoid H) ((n : Γ) * x) = Quotient.mk (cosetSetoid H) x := by
  apply Quotient.sound
  exact ⟨n⁻¹, by rw [Subgroup.coe_inv]; group⟩

/-- `sect` is `1` on `H`. -/
lemma sect_of_mem {x : Γ} (hx : x ∈ H) : sect H x = 1 := by
  unfold sect; rw [if_pos hx]

/-- The defining property of `sect x`: it represents the coset of `x`, so `sect x * x⁻¹ ∈ H`. -/
lemma sect_mul_inv_mem (x : Γ) : sect H x * x⁻¹ ∈ H := by
  unfold sect
  split_ifs with hx
  · simpa using H.inv_mem hx
  · have hmk : Quotient.mk (cosetSetoid H) (Quotient.out (Quotient.mk (cosetSetoid H) x))
        = Quotient.mk (cosetSetoid H) x := Quotient.out_eq _
    obtain ⟨n, hn⟩ := Quotient.exact hmk
    have hout : Quotient.out (Quotient.mk (cosetSetoid H) x) = ((n⁻¹ : ↥H) : Γ) * x := by
      rw [Subgroup.coe_inv, eq_inv_mul_iff_mul_eq]; exact hn
    have : Quotient.out (Quotient.mk (cosetSetoid H) x) * x⁻¹ = ((n⁻¹ : ↥H) : Γ) := by
      rw [hout, Subgroup.coe_inv]; group
    rw [this]; exact (n⁻¹).2

/-- `sect` is constant on left cosets. -/
lemma sect_const (n : ↥H) (x : Γ) : sect H ((n : Γ) * x) = sect H x := by
  unfold sect
  rw [mk_const H n x]
  have hiff : (n : Γ) * x ∈ H ↔ x ∈ H := by
    constructor
    · intro h
      have hxH : x = ((n⁻¹ : ↥H) : Γ) * ((n : Γ) * x) := by rw [Subgroup.coe_inv]; group
      exact (congrArg (· ∈ H) hxH).mpr (H.mul_mem (n⁻¹).2 h)
    · intro h; exact H.mul_mem n.2 h
  by_cases hx : x ∈ H
  · rw [if_pos (hiff.mpr hx), if_pos hx]
  · rw [if_neg (fun h => hx (hiff.mp h)), if_neg hx]

/-- The `H`-valued "defect" `κ x = sect x * x⁻¹` of the transversal. -/
noncomputable def kappa (x : Γ) : ↥H := ⟨sect H x * x⁻¹, sect_mul_inv_mem H x⟩

lemma kappa_coe (x : Γ) : ((kappa H x : ↥H) : Γ) = sect H x * x⁻¹ := rfl

/-- The Shapiro transition function `c g γ = κ g * (κ (g * γ))⁻¹`. -/
noncomputable def cfunc (g γ : Γ) : ↥H := kappa H g * (kappa H (g * γ))⁻¹

lemma coe_cfunc (g γ : Γ) :
    ((cfunc H g γ : ↥H) : Γ) = sect H g * γ * (sect H (g * γ))⁻¹ := by
  rw [cfunc, Subgroup.coe_mul, Subgroup.coe_inv, kappa_coe, kappa_coe]; group

/-- The multiplicative telescoping identity for `cfunc`. -/
lemma cfunc_mul (g γ γ' : Γ) :
    ((cfunc H g (γ * γ') : ↥H) : Γ)
      = ((cfunc H g γ : ↥H) : Γ) * ((cfunc H (g * γ) γ' : ↥H) : Γ) := by
  rw [coe_cfunc, coe_cfunc, coe_cfunc, mul_assoc g γ γ']; group

/-- The unit (normalisation) condition for `cfunc`. -/
lemma cfunc_one (g : Γ) : ((cfunc H g 1 : ↥H) : Γ) = 1 := by
  rw [coe_cfunc]; simp

/-- Left `H`-invariance of `cfunc`. -/
lemma cfunc_inv (g γ : Γ) (n : ↥H) : cfunc H ((n : Γ) * g) γ = cfunc H g γ := by
  apply Subtype.ext
  rw [coe_cfunc, coe_cfunc, sect_const H n g, mul_assoc (n : Γ) g γ, sect_const H n (g * γ)]

/-- Surjectivity of `cfunc` onto `H`. -/
lemma cfunc_cover (n : ↥H) : ∃ g γ : Γ, cfunc H g γ = n := by
  refine ⟨1, (n : Γ), ?_⟩
  apply Subtype.ext
  rw [coe_cfunc, sect_of_mem H H.one_mem, one_mul, sect_of_mem H n.2]
  simp

end Construction

theorem exists_shapiro_c {Γ : Type} [Group Γ] [Fintype Γ] (H : Subgroup Γ)
    (W : Rep.{0} SSGRoute.PTExt.Coeff ↥H)
    (htriv : ∀ (n : ↥H) (x : W.V), W.ρ n x = x)
    (y : ↥H →* Multiplicative W.V) :
    ∃ (c : Γ → Γ → ↥H) (z : Γ → (Rep.coind H.subtype W).V),
      (∀ g γ γ' : Γ,
        ((c g (γ * γ') : ↥H) : Γ) = ((c g γ : ↥H) : Γ) * ((c (g * γ) γ' : ↥H) : Γ)) ∧
      (∀ g : Γ, ((c g 1 : ↥H) : Γ) = 1) ∧
      (∀ (g γ : Γ) (n : ↥H), c ((n : Γ) * g) γ = c g γ) ∧
      (∀ n : ↥H, ∃ g γ : Γ, c g γ = n) ∧
      z ∈ groupCohomology.cocycles₁ (Rep.coind H.subtype W) ∧
      (∀ (γ g : Γ), (z γ).1 g = Multiplicative.toAdd (y (c g γ))) := by
  refine ⟨cfunc H, fun γ => ⟨fun g => Multiplicative.toAdd (y (cfunc H g γ)), ?_⟩,
    cfunc_mul H, cfunc_one H, fun g γ n => cfunc_inv H g γ n, cfunc_cover H, ?_, ?_⟩
  · intro n g
    show Multiplicative.toAdd (y (cfunc H ((n : Γ) * g) γ))
      = W.ρ n (Multiplicative.toAdd (y (cfunc H g γ)))
    rw [cfunc_inv H g γ n]
    exact (htriv n _).symm
  · exact Work.Sha2Lib.shapiroCocycle_mem W htriv (cfunc H) (cfunc_mul H) (cfunc_one H)
      (fun g γ n => cfunc_inv H g γ n) y
  · intro γ g; rfl

end Work.SSGRoute.TatePoitouRoute
