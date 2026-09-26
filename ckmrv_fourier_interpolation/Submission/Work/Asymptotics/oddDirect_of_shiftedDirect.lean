import Mathlib
import Submission.Work.Asymptotics.psiOdd
import Submission.Work.Asymptotics.monomial_of_psiM
import Submission.Work.Asymptotics.oddDirect_of_psiM

/-!
# The odd directness theorem transported from the shifted free-product statement

This file proves `Work.Asymptotics.oddDirect_of_shiftedDirect`: the directness of
`(T-I)²R + S(T-I)²R` **on the odd part** of `R = ℂ[SL(2,ℤ)]`, i.e.
`A z = -A → B z = -B → (T-1)²A + S(T-1)²B = 0 → A = 0 ∧ B = 0` (`z = -I`),
from the *shifted* free-product statement `hRR` in `RR = ℂ[ℤ/2 ∗ ℤ/3]`.

The transport uses `psiM : ℂ[ℤ/2 ∗ ℤ/3] → R`, the odd component `a ↦ psi a · e₋` of the
algebra homomorphism `psi` with `X ↦ u = i·(S e₋) + e₊`, `Y ↦ v = -(ST e₋) + e₊`
(see `Submission/Work/Asymptotics/psiOdd.lean`).  Since `psiM (Tnu ν) = i·(R_T e₋) - ν·e₋`,
the difference operator `T - 1` in `R e₋` is the image, up to the scalar `-i`, of `Tnu i`
in `RR`; injectivity and surjectivity of `psiM` onto `R e₋` therefore transport the
directness statement, and `hRR` is applied at the admissible value `ν = i`.
-/

namespace Work.Asymptotics

open Work.Kernels
open Work.FreeProduct (RR X Y Y2 TT Tnu x y y2)
open Work.Modular.PresGroup (Cyc C2 C3 FP gC2 gC3 ofFree)
open scoped MonoidAlgebra MatrixGroups

noncomputable section

/-! ## Coefficients of `single w 1 · e₋` -/

/-- `single w 1 · e₋ = 2⁻¹ • (single w 1 - single (-w) 1)`. -/
lemma single_mul_eMinus (w : SL(2,ℤ)) :
    MonoidAlgebra.single w (1 : ℂ) * eMinus
      = (2⁻¹ : ℂ) • (MonoidAlgebra.single w (1 : ℂ) - MonoidAlgebra.single (-w) (1 : ℂ)) := by
  rw [eMinus, Algebra.mul_smul_comm, mul_sub, mul_one, Work.Residues.Rneg,
    MonoidAlgebra.single_mul_single]
  rw [show (w * (-1 : SL(2,ℤ))) = -w from by rw [mul_neg, mul_one]]
  simp

lemma neg_self_ne (w : SL(2,ℤ)) : (-w : SL(2,ℤ)) ≠ w := by
  intro h
  have h1 : (-1 : SL(2,ℤ)) = 1 := by
    have h2 := congrArg (fun x : SL(2,ℤ) => x * w⁻¹) h
    simpa [mul_assoc] using h2
  exact absurd h1 (by decide)

lemma coeff_single_apply' (g δ : SL(2,ℤ)) (c : ℂ) :
    MonoidAlgebra.coeff (MonoidAlgebra.single g c) δ = if δ = g then c else 0 := by
  rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases h : δ = g
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hc => h hc.symm)]

lemma coeff_single_mul_eMinus_self (w : SL(2,ℤ)) :
    MonoidAlgebra.coeff (MonoidAlgebra.single w (1 : ℂ) * eMinus) w = (2 : ℂ)⁻¹ := by
  rw [single_mul_eMinus, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
    MonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_single_apply', coeff_single_apply',
    if_pos rfl, if_neg (fun h => neg_self_ne w h.symm)]
  ring

lemma coeff_single_mul_eMinus_ne_zero {w w₀ : SL(2,ℤ)}
    (h : MonoidAlgebra.coeff (MonoidAlgebra.single w (1 : ℂ) * eMinus) w₀ ≠ 0) :
    w = w₀ ∨ -w = w₀ := by
  have h1 : MonoidAlgebra.coeff (MonoidAlgebra.single w (1 : ℂ) * eMinus) w₀
      = 2⁻¹ * ((if w₀ = w then (1 : ℂ) else 0) - (if w₀ = -w then (1 : ℂ) else 0)) := by
    rw [single_mul_eMinus, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
      MonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_single_apply', coeff_single_apply']
  by_cases hw : w = w₀
  · exact Or.inl hw
  · by_cases hw2 : -w = w₀
    · exact Or.inr hw2
    · exfalso
      apply h
      rw [h1, if_neg (fun hh => hw hh.symm), if_neg (fun hh => hw2 hh.symm)]
      ring

lemma toGamma_neg (w : SL(2,ℤ)) : Work.Residues.toGamma (-w) = Work.Residues.toGamma w := by
  rw [show (-w : SL(2,ℤ)) = (-1) * w from by rw [neg_mul, one_mul], map_mul,
    Work.Residues.toGamma_neg_one, one_mul]

lemma toFree_ofFree (γ : FP) : Work.Modular.PresGroup.toFree (ofFree γ) = γ := by
  have h := DFunLike.congr_fun Work.Modular.PresGroup.toFree_comp_ofFree γ
  simpa using h

lemma ofFree_toFree (δ : Work.Modular.Gamma) :
    ofFree (Work.Modular.PresGroup.toFree δ) = δ := by
  have h := DFunLike.congr_fun Work.Modular.PresGroup.ofFree_comp_toFree δ
  simpa using h

lemma ofFree_injective : Function.Injective ofFree := by
  intro γ γ' h
  rw [← toFree_ofFree γ, ← toFree_ofFree γ', h]

/-- The coefficient functional `x ↦ x.coeff w` as a `ℂ`-linear map. -/
def coeffFun (w : SL(2,ℤ)) : R →ₗ[ℂ] ℂ where
  toFun x := MonoidAlgebra.coeff x w
  map_add' x y := by rw [MonoidAlgebra.coeff_add, Finsupp.add_apply]
  map_smul' c x := by
    rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, RingHom.id_apply, smul_eq_mul]

/-- Expansion of `psiM` in the basis `of γ`. -/
lemma psiM_eq_sum (a : RR) :
    psiM a = a.coeff.sum (fun γ c => c • psiM (MonoidAlgebra.of ℂ FP γ)) := by
  rw [psiM, MonoidAlgebra.lift_unique psi a, Finsupp.sum, Finset.sum_mul, Finsupp.sum]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  rw [Algebra.smul_mul_assoc, MonoidAlgebra.of_apply]
  rfl

/-- Coefficient expansion of `psiM`. -/
lemma coeff_psiM (a : RR) (w : SL(2,ℤ)) :
    MonoidAlgebra.coeff (psiM a) w
      = a.coeff.sum (fun γ c => c * MonoidAlgebra.coeff (psiM (MonoidAlgebra.of ℂ FP γ)) w) := by
  have h : coeffFun w (psiM a)
      = a.coeff.sum (fun γ c => c * MonoidAlgebra.coeff (psiM (MonoidAlgebra.of ℂ FP γ)) w) := by
    rw [psiM_eq_sum a, Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [map_smul, smul_eq_mul]
    rfl
  exact h

theorem psiM_eq_zero {a : RR} (ha : psiM a = 0) : a = 0 := by
  classical
  by_contra hne
  have hc : a.coeff ≠ 0 := by
    intro h
    exact hne (MonoidAlgebra.coeff_inj.mp (by rw [h, MonoidAlgebra.coeff_zero]))
  obtain ⟨γ₀, hγ₀⟩ := Finsupp.support_nonempty_iff.mpr hc
  have hγ₀ne : a.coeff γ₀ ≠ 0 := Finsupp.mem_support_iff.mp hγ₀
  obtain ⟨c₀, hc₀, w₀, hof₀, hmono₀⟩ := monomial_of_psiM γ₀
  have hsum : a.coeff.sum
      (fun γ c => c * MonoidAlgebra.coeff (psiM (MonoidAlgebra.of ℂ FP γ)) w₀) = 0 := by
    rw [← coeff_psiM a w₀, ha, MonoidAlgebra.coeff_zero]
    simp
  have hsingle : ∀ γ ∈ a.coeff.support, γ ≠ γ₀ →
      a.coeff γ * MonoidAlgebra.coeff (psiM (MonoidAlgebra.of ℂ FP γ)) w₀ = 0 := by
    intro γ _ hγ
    obtain ⟨c, hc, w, hof, hmono⟩ := monomial_of_psiM γ
    have hzero : MonoidAlgebra.coeff (psiM (MonoidAlgebra.of ℂ FP γ)) w₀ = 0 := by
      by_contra hne
      have h2 : MonoidAlgebra.coeff (MonoidAlgebra.single w (1 : ℂ) * eMinus) w₀ ≠ 0 := by
        intro h0
        apply hne
        rw [hmono, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, h0, mul_zero]
      rcases coeff_single_mul_eMinus_ne_zero h2 with h3 | h3
      · exact hγ (ofFree_injective (by rw [hof, h3, hof₀]))
      · exact hγ (ofFree_injective (by rw [hof, hof₀, ← h3, toGamma_neg]))
    rw [hzero, mul_zero]
  rw [Finsupp.sum] at hsum
  rw [Finset.sum_eq_single_of_mem γ₀ hγ₀ hsingle] at hsum
  rw [hmono₀, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
    coeff_single_mul_eMinus_self] at hsum
  exact hγ₀ne (mul_eq_zero.mp hsum |>.resolve_right (mul_ne_zero hc₀ (by norm_num)))

theorem psiM_injective : Function.Injective psiM := by
  intro a b h
  have hneg : psiM (-b) = -psiM b := by
    rw [show -b = (-1 : ℂ) • b by rw [neg_smul, one_smul], psiM_smul, neg_smul, one_smul]
  have hsub : psiM (a - b) = 0 := by
    rw [sub_eq_add_neg, psiM_add, hneg, h, add_neg_cancel]
  exact sub_eq_zero.mp (psiM_eq_zero hsub)

/-! ## Surjectivity of `psiM` onto the odd part -/

/-- `psiM` as a `ℂ`-linear map. -/
def psiMLin : RR →ₗ[ℂ] R where
  toFun := psiM
  map_add' := psiM_add
  map_smul' := psiM_smul

lemma single_neg_mul_eMinus (w : SL(2,ℤ)) :
    MonoidAlgebra.single (-w) (1 : ℂ) * eMinus
      = -(MonoidAlgebra.single w (1 : ℂ) * eMinus) := by
  have h : MonoidAlgebra.single (-w) (1 : ℂ)
      = Work.Residues.Rneg * MonoidAlgebra.single w (1 : ℂ) := by
    rw [Work.Residues.Rneg, MonoidAlgebra.single_mul_single, mul_one]
    congr 1
    rw [show (-1 : SL(2,ℤ)) * w = -w from by rw [neg_mul, one_mul]]
  rw [h, mul_assoc Work.Residues.Rneg (MonoidAlgebra.single w (1 : ℂ)) eMinus,
    ← mul_assoc Work.Residues.Rneg (MonoidAlgebra.single w (1 : ℂ)) eMinus]
  rw [Work.Residues.Rneg_comm, mul_assoc, Rneg_mul_eMinus, mul_neg]

/-- Every `single (sec δ) 1 · e₋` lies in the range of `psiM`. -/
lemma single_sec_mem_range (δ : Work.Modular.Gamma) :
    MonoidAlgebra.single (Work.Residues.sec δ) (1 : ℂ) * eMinus ∈ LinearMap.range psiMLin := by
  obtain ⟨c, hc, w, hof, hmono⟩ := monomial_of_psiM (Work.Modular.PresGroup.toFree δ)
  have hval : psiMLin (MonoidAlgebra.of ℂ FP (Work.Modular.PresGroup.toFree δ))
      = c • (MonoidAlgebra.single w (1 : ℂ) * eMinus) := hmono
  have hto : Work.Residues.toGamma w = δ := by rw [← hof, ofFree_toFree]
  rcases Work.Residues.eq_sec_or_eq_neg_sec w with hw | hw
  · have hw' : MonoidAlgebra.single w (1 : ℂ) * eMinus
        = MonoidAlgebra.single (Work.Residues.sec δ) (1 : ℂ) * eMinus := by
      rw [hw, hto]
    refine ⟨c⁻¹ • MonoidAlgebra.of ℂ FP (Work.Modular.PresGroup.toFree δ), ?_⟩
    rw [map_smul, hval, smul_smul, inv_mul_cancel₀ hc, one_smul, hw']
  · have hw' : w = -Work.Residues.sec δ := by rw [hw, hto]
    refine ⟨(-c⁻¹) • MonoidAlgebra.of ℂ FP (Work.Modular.PresGroup.toFree δ), ?_⟩
    rw [map_smul, hval, smul_smul]
    rw [show (-c⁻¹) * c = -1 by rw [neg_mul, inv_mul_cancel₀ hc], neg_smul, one_smul,
      hw', single_neg_mul_eMinus, neg_neg]

lemma single_mem_range (γ : SL(2,ℤ)) :
    MonoidAlgebra.single γ (1 : ℂ) * eMinus ∈ LinearMap.range psiMLin := by
  rcases Work.Residues.eq_sec_or_eq_neg_sec γ with h | h
  · rw [h]; exact single_sec_mem_range (Work.Residues.toGamma γ)
  · rw [h, single_neg_mul_eMinus]
    exact Submodule.neg_mem _ (single_sec_mem_range (Work.Residues.toGamma γ))

lemma mul_eMinus_mem_span (x : R) :
    x * eMinus ∈ Submodule.span ℂ {y : R | ∃ γ : SL(2,ℤ),
      y = MonoidAlgebra.single γ (1 : ℂ) * eMinus} := by
  induction x using MonoidAlgebra.induction_on with
  | of γ => exact Submodule.subset_span ⟨γ, by rw [MonoidAlgebra.of_apply]⟩
  | add x y hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x hx =>
    rw [Algebra.smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem psiM_surjective : ∀ A : R, A * Work.Residues.Rneg = -A → ∃ a : RR, psiM a = A := by
  intro A hA
  have hAe : A = A * eMinus := (mul_Rneg_eq_neg_iff A).mp hA
  have hspan : A ∈ Submodule.span ℂ {y : R | ∃ γ : SL(2,ℤ),
      y = MonoidAlgebra.single γ (1 : ℂ) * eMinus} := by
    rw [hAe]
    exact mul_eMinus_mem_span A
  have hle : Submodule.span ℂ {y : R | ∃ γ : SL(2,ℤ),
        y = MonoidAlgebra.single γ (1 : ℂ) * eMinus} ≤ LinearMap.range psiMLin :=
    Submodule.span_le.mpr (fun y hy => by
      obtain ⟨γ, rfl⟩ := hy
      exact single_mem_range γ)
  obtain ⟨a, ha⟩ := hle hspan
  exact ⟨a, ha⟩

/-! ## The final theorem -/

/-
Route: the odd part `R₋ = {A : R | A * Rneg = -A}` of `R = ℂ[SL(2,ℤ)]` equals `R * e₋` with
`e₋ = 2⁻¹ • (1 - Rneg)` (`Rneg = -I`, central).  Build `Ψ : RR → R` on the free-product
generators as the multiplicative extension of `X ↦ c₁ • (R_S * e₋)` and `Y ↦ c₂ • (R_T * e₋)`
(the images are units of `R e₋`; use `Monoid.CoprodI.lift` plus the relations `X² = 1`, `Y³ = 1`
in `RR`, i.e. `σ² = -1`, `τ³ = -1` inside `R e₋` with `σ = R_S e₋`, `τ = R_T e₋`).
Prove `Ψ` multiplicative, injective, and onto `R e₋` (the section `Work.Residues.sec` of
`Work.Residues.XiTransfer` gives a basis `{sec δ • e₋}` of `R e₋`, and `Ψ (of γ)` is a nonzero
multiple of such a basis element).  Then `Ψ (Tnu ν * x) = (R_T - 1) * Ψ x` for the value
`ν = ...` with `ν³ = ±i` (automatic from `c₁² = -1` and the consistency of the relations), and
instantiating `hRR` at that `ν` transports the directness statement.
-/
theorem oddDirect_of_shiftedDirect
    (hRR : ∀ {ν : ℂ}, ν ≠ 0 → ν ^ 3 ≠ 1 → ν ^ 3 ≠ -1 →
      ∀ a b : Work.FreeProduct.RR,
        Work.FreeProduct.Tnu ν ^ 2 * a + Work.FreeProduct.X * Work.FreeProduct.Tnu ν ^ 2 * b = 0 →
        a = 0 ∧ b = 0) :
    ∀ A B : Work.Kernels.R, A * Work.Residues.Rneg = -A → B * Work.Residues.Rneg = -B →
      (Work.Kernels.R_T - 1) ^ 2 * A + Work.Kernels.R_S * (Work.Kernels.R_T - 1) ^ 2 * B = 0 →
      A = 0 ∧ B = 0 := by
  exact oddDirect_of_psiM hRR psiM_injective psiM_surjective

end
end Work.Asymptotics
