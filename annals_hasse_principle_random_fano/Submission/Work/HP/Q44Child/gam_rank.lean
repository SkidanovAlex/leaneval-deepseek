import Mathlib
import Submission.Work.HP.Q44Setup
import Submission.Work.HP.MDBasic.mem_Gam_iff

/-!
# Rank of `Γ_{x,y} = Gam 4 4 x y`

`Γ_{x,y} = Λ_{ν(x)} ∩ Λ_{ν(y)} ⊆ ℤ^{70}` is the kernel of the pair of linear forms
`Φ_{x,y} : a ↦ (⟨a, ν(x)⟩, ⟨a, ν(y)⟩)`, a linear map into `ℤ²`.  Rank–nullity over `ℤ`
(`Submodule.finrank_quotient_add_finrank` together with
`LinearMap.quotKerEquivRange`, using `IsDomain.hasRankNullity` for `ℤ`) gives
`finrank Γ = finrank ℤ^{70} - finrank (range Φ) ≥ 70 - 2 = 68 ≥ 56`.

The statement proved here is the weak bound `56 ≤ rk Γ` needed downstream; it holds for
*every* pair `x y` (no independence hypothesis on `ν(x), ν(y)` is needed).
-/

set_option maxRecDepth 100000

namespace Work.HP.Q44Child

open Work.HP

/-- The pair of linear forms `Φ_{x,y}(a) = (⟨a, ν_{d,n}(x)⟩, ⟨a, ν_{d,n}(y)⟩)` attached to a
pair of vectors `x y : ℤ^{n+1}`.  Its kernel is `Gam d n x y`. -/
noncomputable def pairForm (d n : ℕ) (x y : Fin (n + 1) → ℤ) :
    (Mon d n → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) :=
  LinearMap.pi (fun i : Fin 2 =>
    if i = 0 then Fintype.linearCombination ℤ (veronese d n x)
    else Fintype.linearCombination ℤ (veronese d n y))

/-- `⟨a, ν_{d,n}(x)⟩`, written as a linear combination of the coefficients of `a`. -/
theorem linearCombination_veronese_eq_formEval (d n : ℕ) (x : Fin (n + 1) → ℤ)
    (a : Mon d n → ℤ) :
    Fintype.linearCombination ℤ (veronese d n x) a = formEval d n a x := by
  simp [formEval, Fintype.linearCombination_apply]

/-- Membership in the kernel of `Φ_{x,y}`: vanishing of the two linear forms. -/
theorem mem_pairForm_ker_iff (d n : ℕ) (x y : Fin (n + 1) → ℤ) (a : Mon d n → ℤ) :
    a ∈ (pairForm d n x y).ker ↔ formEval d n a x = 0 ∧ formEval d n a y = 0 := by
  rw [LinearMap.mem_ker, funext_iff, Fin.forall_fin_two]
  simp only [Pi.zero_apply]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨by simpa [pairForm, linearCombination_veronese_eq_formEval] using h0,
           by simpa [pairForm, linearCombination_veronese_eq_formEval] using h1⟩
  · rintro ⟨h0, h1⟩
    exact ⟨by simpa [pairForm, linearCombination_veronese_eq_formEval] using h0,
           by simpa [pairForm, linearCombination_veronese_eq_formEval] using h1⟩

/-- `Gam d n x y` is the kernel of the pair of linear forms `Φ_{x,y}`. -/
theorem Gam_eq_pairForm_ker (d n : ℕ) (x y : Fin (n + 1) → ℤ) :
    Gam d n x y = (pairForm d n x y).ker :=
  Submodule.ext fun a => by
    rw [Work.HP.MDBasic.mem_Gam_iff, mem_pairForm_ker_iff]

/-- There are `70` degree-`4` monomials in `5` variables, i.e. `N_{4,4} = 70`. -/
theorem card_Mon_four_four : Fintype.card (Mon 4 4) = 70 := by decide

/-- `ℤ^{N_{4,4}} = ℤ^{70}`. -/
theorem finrank_pi_Mon_four_four : Module.finrank ℤ (Mon 4 4 → ℤ) = 70 := by
  rw [Module.finrank_fintype_fun_eq_card, card_Mon_four_four]

/-- `Γ_{x,y} = Gam 4 4 x y = Λ_{ν(x)} ∩ Λ_{ν(y)} ⊆ ℤ^{70}` has rank at least `56`
(in fact `rk (Gam 4 4 x y) = NN 4 4 - 2 = 68` for every `x y`).

Route: `Gam 4 4 x y = Φ.ker` where `Φ : (Mon 4 4 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ)` is
`a ↦ ![⟨a, ν(x)⟩, ⟨a, ν(y)⟩]` (`Work.HP.MDBasic.mem_Gam_iff` describes membership).
Rank–nullity over `ℤ` (`Submodule.finrank_quotient_add_finrank`, using `HasRankNullity ℤ`,
available since `ℤ` is a domain, and `Module.Finite ℤ (Mon 4 4 → ℤ)`) gives
`finrank (Φ.ker) = finrank (Mon 4 4 → ℤ) - finrank (Φ.range)` (`LinearMap.quotKerEquivRange`),
and `finrank (Φ.range) ≤ finrank (Fin 2 → ℤ) = 2` (`Submodule.finrank_mono`).
Finally `finrank ℤ (Mon 4 4 → ℤ) = Fintype.card (Mon 4 4) = 70`
(`Module.finrank_fintype_fun_eq_card`; `Fintype.card (Mon 4 4) = 70` by `decide`, which needs
`set_option maxRecDepth 100000`).  (Do not use the `DivisionRing` version of rank–nullity.) -/
theorem gam_rank (x y : Fin 5 → ℤ) : 56 ≤ Work.HP.rk (Work.HP.Gam 4 4 x y) := by
  have hker : Gam 4 4 x y = (pairForm 4 4 x y).ker := Gam_eq_pairForm_ker 4 4 x y
  -- rank–nullity for `Φ_{x,y}` over `ℤ`
  have hrn := Submodule.finrank_quotient_add_finrank (R := ℤ) (M := (Mon 4 4 → ℤ))
    (pairForm 4 4 x y).ker
  rw [LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange (pairForm 4 4 x y)),
    finrank_pi_Mon_four_four] at hrn
  -- the image has rank at most `2`
  have hle : Module.finrank ℤ (pairForm 4 4 x y).range ≤ 2 := by
    have h1 := Submodule.finrank_le (R := ℤ) (M := (Fin 2 → ℤ)) (pairForm 4 4 x y).range
    rwa [Module.finrank_fin_fun] at h1
  rw [Work.HP.rk, hker]
  omega

end Work.HP.Q44Child
