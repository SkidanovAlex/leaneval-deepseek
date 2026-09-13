import Submission.Grassmann.RestrictProp
import Submission.Commons.Analysis.Inequalities.sum_pow_four_le_card_pow_three_mul_sum
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_le_le_pow
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_ge_le_pow
import Submission.Commons.LinearAlgebra.Submodule.card_ker_range_le

/-!
# `lem:bounds on composition` of arXiv:2209.04243 §8

The lemma bounds the 4-norm of the composition of the two basic Laplacians `L_{V₁}∘L_{W₁}` by a
sum of 4-norms of derivatives:

  `‖L_{V₁}∘L_{W₁}[f]‖₄⁴ ≤ q^{C(i²+j²)} Σ_{V₂≤V₁, W₂≥W₁} Σ_{X̃ : W₂/W₁ ≅ V₁/V₂}
     E_T ‖D_X ∘ D_{V₂,W₂,T}[f]‖₄⁴`,

where `i = dim V₁` and `j = codim W₁`.

* `l4q_eq_avg_restr` rewrites the left-hand side as the average over the shifts `T` of the
  restricted composition;
* Prop "taking restrictions of Laplacians" (`taking_restrictions`) expands the restriction as
  the sum of the summands `D_X ∘ D_{V₂,W₂,T}`;
* Hölder's inequality `(Σ a_i)⁴ ≤ #³ Σ a_i⁴` (`l4q_sum_le`) and the counting
  `#{triples} ≤ 2^{(i+j)²}` (`card_tripleOK_le`) give the result.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-! ## Holder's inequality for `l4q` -/

/-- **Holder's inequality `(Σ aᵢ)⁴ ≤ (#I)³ Σ aᵢ⁴` for `l4q`.** -/
theorem l4q_sum_le {m n : ℕ} {ι : Type*} [Fintype ι]
    (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l4q (∑ i, g i) ≤ (Fintype.card ι : ℝ) ^ 3 * ∑ i, l4q (g i) := by
  have hpt : ∀ A : Matrix (Fin m) (Fin n) 𝔽₂,
      ‖(∑ i, g i) A‖ ^ 4 ≤ (Fintype.card ι : ℝ) ^ 3 * ∑ i, ‖g i A‖ ^ 4 := by
    intro A
    have hsum : (∑ i, g i) A = ∑ i, g i A := Finset.sum_apply A Finset.univ g
    have h1 : ‖(∑ i, g i) A‖ ≤ ∑ i, ‖g i A‖ := by
      rw [hsum]; exact norm_sum_le _ _
    have h2 : ‖(∑ i, g i) A‖ ^ 4 ≤ (∑ i, ‖g i A‖) ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 4
    have h3 := Commons.Analysis.Inequalities.sum_pow_four_le_card_pow_three_mul_sum
      (Finset.univ) (fun i => ‖g i A‖) (fun i _ => norm_nonneg _)
    rw [Finset.card_univ] at h3
    exact le_trans h2 h3
  have hsumA : (∑ A, ‖(∑ i, g i) A‖ ^ 4) ≤
      (Fintype.card ι : ℝ) ^ 3 * ∑ A, ∑ i, ‖g i A‖ ^ 4 := by
    refine le_trans (Finset.sum_le_sum (fun A _ => hpt A)) ?_
    rw [Finset.mul_sum]
  have hR : (∑ i : ι, l4q (g i)) = ((2 : ℝ) ^ (m * n))⁻¹ * ∑ A, ∑ i, ‖g i A‖ ^ 4 := by
    unfold l4q
    rw [Finset.sum_comm, Finset.mul_sum]
  calc l4q (∑ i, g i) = ((2 : ℝ) ^ (m * n))⁻¹ * ∑ A, ‖(∑ i, g i) A‖ ^ 4 := rfl
    _ ≤ ((2 : ℝ) ^ (m * n))⁻¹ *
        ((Fintype.card ι : ℝ) ^ 3 * ∑ A, ∑ i, ‖g i A‖ ^ 4) :=
        mul_le_mul_of_nonneg_left hsumA (by positivity)
    _ = (Fintype.card ι : ℝ) ^ 3 * ∑ i, l4q (g i) := by
        rw [hR]; ring

/-! ## A sum with an indicator is a sum over the subtype -/

/-- A sum of `if p x then g x else 0` is the sum of `g` over the subtype `{x // p x}`. -/
theorem sum_ite_eq_sum_subtype {α M : Type*} [Fintype α] [AddCommMonoid M] (p : α → Prop)
    [DecidablePred p] [Fintype {x // p x}] (g : α → M) :
    (∑ x : α, (if p x then g x else 0)) = ∑ x : {x // p x}, g x := by
  rw [← Finset.sum_filter (s := Finset.univ) (p := p) (f := g)]
  exact Finset.sum_subtype (p := p) (Finset.univ.filter p) (fun x => by simp) g

/-! ## `lem:bounds on composition` -/

/-- **`lem:bounds on composition`**, reduced to the counting of the index set: if the number of
admissible triples is at most `K` then

  `‖L_{V₁}∘L_{W₁}[f]‖₄⁴ ≤ K³ Σ_{V₂≤V₁, W₂≥W₁, X̃} E_T ‖D_X D_{V₂,W₂,T}[f]‖₄⁴`. -/
theorem bounds_on_composition_of_card {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (K : ℝ)
    (hK : (Nat.card {t : Triple m n // TripleOK V₁ W₁ t} : ℝ) ≤ K) :
    l4q (Lup V₁ (Ldown W₁ f)) ≤ ((2 : ℝ) ^ (m * n))⁻¹ * (K ^ 3 *
      ∑ t : {t : Triple m n // TripleOK V₁ W₁ t}, ∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
        l4q (DopX V₁ W₁ t.1.1 t.1.2.1 t.1.2.2 T f)) := by
  have hstep : ∀ T : Matrix (Fin m) (Fin n) 𝔽₂,
      l4q (restr (Qp V₁) (Ip W₁) (shift T (Lup V₁ (Ldown W₁ f)))) ≤
        K ^ 3 * ∑ t : {t : Triple m n // TripleOK V₁ W₁ t},
          l4q (DopX V₁ W₁ t.1.1 t.1.2.1 t.1.2.2 T f) := by
    intro T
    have h1 : restr (Qp V₁) (Ip W₁) (shift T (Lup V₁ (Ldown W₁ f))) = DopSum V₁ W₁ T f :=
      taking_restrictions V₁ W₁ T f
    rw [h1, DopSum, sum_ite_eq_sum_subtype (TripleOK V₁ W₁)
      (fun t : Triple m n => DopX V₁ W₁ t.1 t.2.1 t.2.2 T f)]
    have hH := l4q_sum_le (fun t : {t : Triple m n // TripleOK V₁ W₁ t} =>
      DopX V₁ W₁ t.1.1 t.1.2.1 t.1.2.2 T f)
    have hcard : (Fintype.card {t : Triple m n // TripleOK V₁ W₁ t} : ℝ) ≤ K := by
      rw [Nat.card_eq_fintype_card] at hK
      exact hK
    refine le_trans hH ?_
    refine mul_le_mul_of_nonneg_right ?_
      (Finset.sum_nonneg (fun t _ => l4q_nonneg _))
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 3
  rw [l4q_eq_avg_restr V₁ W₁ (Qp V₁) (Ip W₁) (ker_Qp V₁) (range_Qp V₁) (range_Ip W₁)
    (ker_Ip W₁)]
  calc ((2 : ℝ) ^ (m * n))⁻¹ *
        ∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
          l4q (restr (Qp V₁) (Ip W₁) (shift T (Lup V₁ (Ldown W₁ f))))
      ≤ ((2 : ℝ) ^ (m * n))⁻¹ *
        ∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
          (K ^ 3 * ∑ t : {t : Triple m n // TripleOK V₁ W₁ t},
            l4q (DopX V₁ W₁ t.1.1 t.1.2.1 t.1.2.2 T f)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun T _ => hstep T)) (by positivity)
    _ = ((2 : ℝ) ^ (m * n))⁻¹ * (K ^ 3 *
        ∑ t : {t : Triple m n // TripleOK V₁ W₁ t}, ∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
          l4q (DopX V₁ W₁ t.1.1 t.1.2.1 t.1.2.2 T f)) := by
        congr 1
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]

/-! ## The counting of the index set -/

/-- `Σ_x (if p x then c else 0) = (#{x // p x}) * c`. -/
theorem sum_ite_const {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] (c : ℕ) :
    (∑ x : α, (if p x then c else 0)) = Nat.card {x // p x} * c := by
  rw [← Finset.sum_filter (s := Finset.univ) (p := p) (f := fun _ => c)]
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  exact (Fintype.card_subtype (p := p)).symm.trans (Nat.card_eq_fintype_card).symm

/-- **The number of admissible triples** `(V₂,W₂,X)` is at most `2^{(i+j)²}`, where `i = dim V₁`
and `j = codim W₁`. -/
theorem card_tripleOK_le (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) :
    Nat.card {t : Triple m n // TripleOK V₁ W₁ t} ≤
      2 ^ ((Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)) *
           (Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁))) := by
  set i := Module.finrank 𝔽₂ V₁
  set j := m - Module.finrank 𝔽₂ W₁
  have hdec : Nat.card {t : Triple m n // TripleOK V₁ W₁ t} =
      ∑ V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        Nat.card {X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂) //
          TripleOK V₁ W₁ (⟨V₂, ⟨W₂, X⟩⟩ : Triple m n)} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
    simp only [Fintype.sum_sigma]
    refine Finset.sum_congr rfl (fun V₂ _ => Finset.sum_congr rfl (fun W₂ _ => ?_))
    rw [← Finset.card_filter, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  rw [hdec]
  have hfiber : ∀ (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)),
      Nat.card {X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂) //
          TripleOK V₁ W₁ (⟨V₂, ⟨W₂, X⟩⟩ : Triple m n)} ≤
        (if V₂ ≤ V₁ ∧ W₁ ≤ W₂ then 2 ^ (i * j) else 0) := by
    intro V₂ W₂
    by_cases h : V₂ ≤ V₁ ∧ W₁ ≤ W₂
    · rw [if_pos h]
      refine le_trans (Nat.card_le_card_of_injective
        (f := fun x : {X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂) //
              TripleOK V₁ W₁ (⟨V₂, ⟨W₂, X⟩⟩ : Triple m n)} =>
            (⟨x.1, le_of_eq x.2.2.2.1.symm, le_of_eq x.2.2.2.2⟩ :
              {X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂) //
                Submodule.comap W₂.subtype W₁ ≤ LinearMap.ker X ∧
                LinearMap.range X ≤ Submodule.map (Submodule.mkQ V₂) V₁}))
        (fun a b hab => Subtype.ext (by simpa using hab))) ?_
      exact Commons.LinearAlgebra.Submodule.card_ker_range_le V₁ V₂ W₁ W₂ h.1 h.2
    · rw [if_neg h]
      haveI : IsEmpty {X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂) //
          TripleOK V₁ W₁ (⟨V₂, ⟨W₂, X⟩⟩ : Triple m n)} := ⟨fun x => h ⟨x.2.1, x.2.2.1⟩⟩
      have h0 : Nat.card {X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂) //
          TripleOK V₁ W₁ (⟨V₂, ⟨W₂, X⟩⟩ : Triple m n)} = 0 :=
        Nat.card_eq_zero.mpr (Or.inl inferInstance)
      rw [h0]
  refine le_trans (Finset.sum_le_sum
    (fun V₂ _ => Finset.sum_le_sum (fun W₂ _ => hfiber V₂ W₂))) ?_
  have hinner : ∀ V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂),
      (∑ W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂), (if V₂ ≤ V₁ ∧ W₁ ≤ W₂ then 2 ^ (i * j) else 0))
        = (if V₂ ≤ V₁ then 2 ^ (i * j) *
            Nat.card {W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂) // W₁ ≤ W₂} else 0) := by
    intro V₂
    by_cases hV : V₂ ≤ V₁
    · rw [if_pos hV]
      have hcongr : ∀ W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂),
          (if V₂ ≤ V₁ ∧ W₁ ≤ W₂ then 2 ^ (i * j) else 0)
            = (if W₁ ≤ W₂ then 2 ^ (i * j) else 0) := by
        intro W₂; by_cases hW : W₁ ≤ W₂ <;> simp [hV, hW]
      rw [Finset.sum_congr rfl (fun W₂ _ => hcongr W₂), sum_ite_const, Nat.mul_comm]
    · rw [if_neg hV]
      refine Finset.sum_eq_zero (fun W₂ _ => ?_)
      rw [if_neg (fun hc => hV hc.1)]
  rw [Finset.sum_congr rfl (fun V₂ _ => hinner V₂)]
  rw [sum_ite_const]
  calc Nat.card {V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂) // V₂ ≤ V₁} *
        (2 ^ (i * j) * Nat.card {W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂) // W₁ ≤ W₂})
      ≤ 2 ^ (i * i) * (2 ^ (i * j) * 2 ^ (j * j)) :=
        Nat.mul_le_mul (Commons.LinearAlgebra.Submodule.card_submodule_le_le_pow V₁)
          (Nat.mul_le_mul_left _ (Commons.LinearAlgebra.Submodule.card_submodule_ge_le_pow W₁))
    _ = 2 ^ (i * i + (i * j + j * j)) := by rw [← pow_add, ← pow_add]
    _ ≤ 2 ^ ((i + j) * (i + j)) :=
        Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- **`lem:bounds on composition`** of arXiv:2209.04243 §8. -/
theorem bounds_on_composition (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l4q (Lup V₁ (Ldown W₁ f)) ≤ ((2 : ℝ) ^ (m * n))⁻¹ *
      (2 ^ (3 * ((Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)) *
           (Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)))) *
        ∑ t : {t : Triple m n // TripleOK V₁ W₁ t}, ∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
          l4q (DopX V₁ W₁ t.1.1 t.1.2.1 t.1.2.2 T f)) := by
  refine le_trans (bounds_on_composition_of_card V₁ W₁ f
    (2 ^ ((Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)) *
           (Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁))))
    (by exact_mod_cast card_tripleOK_le V₁ W₁)) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← pow_mul, Nat.mul_comm]

end

end Submission.Grassmann
