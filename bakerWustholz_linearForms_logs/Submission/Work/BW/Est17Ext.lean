import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.kummer_indep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Definitions for `est17`: the Kummer extension `L = ℚ(φ(K), ρ₁,…,ρ_r) ⊆ ℂ` with
`ρ_j² = φ(η_j)`, together with its number-field structure and the place `w₀` induced by the
inclusion `L ⊆ ℂ`. -/

namespace Work.BW

open Complex
open NumberField

/-- A `ℚ`-basis of `K`. -/
noncomputable def kbasis (K : Type*) [Field K] [NumberField K] :
    Module.Basis (Fin (Module.finrank ℚ K)) ℚ K :=
  Module.finBasis ℚ K

/-- An element of a number field is integral over `ℚ`, hence so is its image under any embedding. -/
theorem isIntegral_phi {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ) (x : K) :
    IsIntegral ℚ (φ x) := by
  refine isAlgebraic_iff_isIntegral.mp ?_
  have h := (Algebra.IsAlgebraic.isAlgebraic x).ringHom_of_comp_eq (RingHom.id ℚ) φ
    Function.injective_id ?_
  · exact h
  · ext q
    simpa using map_ratCast φ q

variable {K : Type*} [Field K] [NumberField K] {r : ℕ}

/-- `L = ℚ(φ(K), ρ₁, …, ρ_r)`, a subfield of `ℂ`. -/
noncomputable def EL (φ : K →+* ℂ) (ρ : Fin r → ℂ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ
    (Set.range (fun i => φ (kbasis K i)) ∪ Set.range ρ)

theorem EL_finite {φ : K →+* ℂ} {ρ : Fin r → ℂ} {η : Fin r → K}
    (hρ : ∀ j, ρ j ^ 2 = φ (η j)) : FiniteDimensional ℚ (EL φ ρ) := by
  rw [EL]
  refine IntermediateField.finiteDimensional_adjoin ?_
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨i, rfl⟩ := hx
    exact isIntegral_phi φ (kbasis K i)
  · obtain ⟨j, rfl⟩ := hx
    exact IsIntegral.of_pow (by norm_num) (hρ j ▸ isIntegral_phi φ (η j))

theorem EL_charZero {φ : K →+* ℂ} {ρ : Fin r → ℂ} : CharZero (EL φ ρ) :=
  charZero_of_inj_zero fun n hn => by
    have h2 : ((n : ℕ) : ℂ) = 0 := by
      have := congrArg (fun z : EL φ ρ => ((IntermediateField.val (EL φ ρ)).toRingHom z : ℂ)) hn
      simpa using this
    exact_mod_cast h2

theorem EL_numberField {φ : K →+* ℂ} {ρ : Fin r → ℂ} {η : Fin r → K}
    (hρ : ∀ j, ρ j ^ 2 = φ (η j)) : NumberField (EL φ ρ) := by
  haveI := EL_finite hρ
  haveI := EL_charZero (φ := φ) (ρ := ρ)
  exact NumberField.mk

/-- The natural map `K →+* L`. -/
noncomputable def inclE (φ : K →+* ℂ) (ρ : Fin r → ℂ) : K →+* EL φ ρ where
  toFun x := ⟨φ x, by
    rw [EL]
    have hxb : x = ∑ i, (kbasis K).repr x i • kbasis K i := ((kbasis K).sum_repr x).symm
    rw [hxb, map_sum]
    refine IntermediateField.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def, map_mul]
    have hq : φ (algebraMap ℚ K ((kbasis K).repr x i)) = algebraMap ℚ ℂ ((kbasis K).repr x i) := by
      simpa using map_ratCast φ ((kbasis K).repr x i)
    rw [hq]
    exact IntermediateField.mul_mem _
      (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨i, rfl⟩))⟩
  map_one' := by ext; simp
  map_mul' := by intro a b; ext; simp
  map_zero' := by ext; simp
  map_add' := by intro a b; ext; simp

@[simp] theorem inclE_coe {φ : K →+* ℂ} {ρ : Fin r → ℂ} (x : K) :
    ((inclE φ ρ x : EL φ ρ) : ℂ) = φ x := rfl

/-- `ρ_j` as an element of `L`. -/
noncomputable def rhoE (φ : K →+* ℂ) (ρ : Fin r → ℂ) (j : Fin r) : EL φ ρ :=
  ⟨ρ j, IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨j, rfl⟩)⟩

@[simp] theorem rhoE_coe {φ : K →+* ℂ} {ρ : Fin r → ℂ} (j : Fin r) :
    ((rhoE φ ρ j : EL φ ρ) : ℂ) = ρ j := rfl

theorem rhoE_sq {φ : K →+* ℂ} {ρ : Fin r → ℂ} {η : Fin r → K} (hρ : ∀ j, ρ j ^ 2 = φ (η j))
    (j : Fin r) : rhoE φ ρ j ^ 2 = inclE φ ρ (η j) := by
  ext
  simp [hρ j]

/-- The infinite place of `L` induced by the inclusion `L ⊆ ℂ`. -/
noncomputable def w0 (φ : K →+* ℂ) (ρ : Fin r → ℂ) : InfinitePlace (EL φ ρ) :=
  InfinitePlace.mk ((IntermediateField.val (EL φ ρ)).toRingHom)

@[simp] theorem w0_apply {φ : K →+* ℂ} {ρ : Fin r → ℂ} (x : EL φ ρ) :
    w0 φ ρ x = ‖(x : ℂ)‖ := rfl

/-! ### The points of the Kummer extension -/

variable {n : ℕ} (α : Fin n → K) (v : ℕ) (Lm : Fin r → Fin n → ℤ)

/-- `ρ_j = exp (lamP_j / 2)`, a square root of `φ(α'_j)` in `ℂ`. -/
noncomputable def rhoC (φ : K →+* ℂ) (α : Fin n → K) (v : ℕ) (Lm : Fin r → Fin n → ℤ)
    (j : Fin r) : ℂ :=
  Complex.exp (lamP φ α v Lm j / 2)

theorem rhoC_sq {φ : K →+* ℂ} {α' : Fin r → K}
    (hexp : ∀ j, Complex.exp (lamP φ α v Lm j) = φ (α' j)) (j : Fin r) :
    rhoC φ α v Lm j ^ 2 = φ (α' j) := by
  rw [rhoC, pow_two, ← Complex.exp_add, ← hexp j]
  congr 1
  ring

/-- `γ = acg … (s/2)` viewed as an element of `L`, given its membership in `L`. -/
noncomputable def gamE {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    (φ : K →+* ℂ) (b : Fin n → ℤ) (k : Fin n)
    (p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K)
    (J : ℕ) (μ : Fin r → ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ) (s : ℤ)
    (h : acg φ α b k Lm ι v σ p J μ t0 t ((s : ℂ) / 2) ∈ (EL φ (rhoC φ α v Lm) : Set ℂ)) :
    EL φ (rhoC φ α v Lm) :=
  ⟨acg φ α b k Lm ι v σ p J μ t0 t ((s : ℂ) / 2), h⟩

@[simp] theorem gamE_coe {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {φ : K →+* ℂ} {b : Fin n → ℤ} {k : Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    {J : ℕ} {μ : Fin r → ℕ} {t0 : ℕ} {t : Fin (r - 1) → ℕ} {s : ℤ}
    {h : acg φ α b k Lm ι v σ p J μ t0 t ((s : ℂ) / 2) ∈ (EL φ (rhoC φ α v Lm) : Set ℂ)} :
    ((gamE α v Lm φ b k p J μ t0 t s h : EL φ (rhoC φ α v Lm)) : ℂ)
      = acg φ α b k Lm ι v σ p J μ t0 t ((s : ℂ) / 2) := rfl

/-- `Ω_w = Σ_j D_j log⁺ w(α'_j)` for a place `w` of the Kummer extension
(`w` an arbitrary absolute value of `L`, so that this applies to finite and infinite places). -/
noncomputable def acOmega {σl : Fin r → ℝ} (φ : K →+* ℂ) (ρ : Fin r → ℂ) (α' : Fin r → K)
    (w : AbsoluteValue (EL φ ρ) ℝ) : ℝ :=
  ∑ j, (pDj r (dK K) σl j : ℝ) * (w (inclE φ ρ (α' j))).posLog

end Work.BW
