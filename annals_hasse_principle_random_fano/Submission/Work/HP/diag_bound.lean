import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.DiagDefs
import Submission.Work.HP.isPrim_veronese
import Submission.Work.HP.bigW_le_pow
import Submission.Work.HP.latOrth_count_pivotal
import Submission.Work.HP.latOrth_count_degenerate
import Submission.Work.HP.Xi_sum_inv_veronese
import Submission.Work.HP.degen_sum
import Submission.Work.HP.mix_sum_le
import Submission.Work.HP.loc_sum_le
import Submission.Work.HP.lam_latOrth_veronese_le

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The diagonal bound for the variance computation

Browning--Le Boudec--Sawin, *The Hasse principle for random Fano hypersurfaces* (Annals 197 (3),
2023), proof of the Proposition "variance": the sum over the height ball of
`N_V(B) + 2 Δ_V^mix(B) + Δ_V^loc(B)` is `≪ A^{N_{d,n}} · B/A`.
-/

noncomputable section

open Filter Finset

namespace Work.HP



/-! ## Placeholders for the delegated auxiliary lemmas

The following statements are proved in separate files and will be imported once available. -/




/-! ## Plumbing -/

variable {ι : Type*} [Fintype ι]

/-- Membership in `latOrth c` is the vanishing of the Euclidean pairing with `c`. -/
lemma dg_mem_latOrth_iff (c a : ι → ℤ) : a ∈ latOrth c ↔ ∑ i, a i * c i = 0 := by
  rw [latOrth, LinearMap.mem_ker, Fintype.linearCombination_apply]
  constructor
  · intro h; simpa [smul_eq_mul] using h
  · intro h; simpa [smul_eq_mul] using h

lemma formEval_int_eq (d n : ℕ) (a : Mon d n → ℤ) (x : Fin (n + 1) → ℤ) :
    formEval d n a x = ∑ m, a m * veronese d n x m := rfl

lemma formEval_eq_zero_iff (d n : ℕ) (a : Mon d n → ℤ) (x : Fin (n + 1) → ℤ) :
    formEval d n a x = 0 ↔ a ∈ latOrth (veronese d n x) := by
  rw [dg_mem_latOrth_iff, ← formEval_int_eq]

namespace DiagNcard

variable {α β : Type*}

lemma ncard_filter_eq_sum (T : Set β) (hT : T.Finite) (P : β → Prop) [DecidablePred P] :
    (({x ∈ T | P x} : Set β).ncard : ℝ) = ∑ x ∈ hT.toFinset, (if P x then (1:ℝ) else 0) := by
  have hfin : ({x ∈ T | P x} : Set β).Finite := hT.subset (fun x hx => hx.1)
  rw [Set.ncard_eq_toFinset_card _ hfin, Finset.sum_boole]
  have hfins : hfin.toFinset = hT.toFinset.filter P := by
    apply Finset.ext
    intro x
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_filter]
  rw [hfins]

lemma sum_ncard_swap (S : Set α) (hS : S.Finite) (T : Set β) (hT : T.Finite)
    (P : α → β → Prop) [∀ a b, Decidable (P a b)] :
    (∑ᶠ a ∈ S, (({x ∈ T | P a x} : Set β).ncard : ℝ))
      = ∑ᶠ x ∈ T, (({a ∈ S | P a x} : Set α).ncard : ℝ) := by
  rw [finsum_mem_of_finite S hS, finsum_mem_of_finite T hT]
  have h1 : (∑ a ∈ hS.toFinset, (({x ∈ T | P a x} : Set β).ncard : ℝ))
      = ∑ a ∈ hS.toFinset, ∑ x ∈ hT.toFinset, (if P a x then (1:ℝ) else 0) :=
    Finset.sum_congr rfl fun a _ => ncard_filter_eq_sum T hT (P a)
  have h2 : (∑ x ∈ hT.toFinset, (({a ∈ S | P a x} : Set α).ncard : ℝ))
      = ∑ x ∈ hT.toFinset, ∑ a ∈ hS.toFinset, (if P a x then (1:ℝ) else 0) :=
    Finset.sum_congr rfl fun x _ => ncard_filter_eq_sum S hS (fun a => P a x)
  rw [h1, h2, Finset.sum_comm]

end DiagNcard

/-! ## Elementary bounds for the determinant and for `μ` -/

lemma dg_dmin_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) (S : Set (ι → ℤ)) :
    0 ≤ dmin r S := by
  refine Real.sInf_nonneg ?_
  rintro D ⟨L, -, -, hD⟩
  rw [← hD]
  exact detL_nonneg L

lemma mu1_nonneg (d n : ℕ) (x : Fin (n + 1) → ℤ) : 0 ≤ mu1 d n x := by
  rw [mu1]
  rcases eq_or_lt_of_le (dg_dmin_nonneg 2 {x}) with h | h
  · rw [← h, div_zero]
  · exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) (eNorm_nonneg x)) h.le

/-- The Veronese vector of a primitive `x` is nonzero. -/
lemma veronese_ne_zero_of_isPrim (d n : ℕ) (hd : 1 ≤ d) {x : Fin (n + 1) → ℤ} (hx : IsPrim x) :
    veronese d n x ≠ 0 := by
  intro h0
  have hx0 : x = 0 := by
    by_contra hne
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    have h1 : veronese d n x (monDiHP d n i) = 0 := by rw [h0]; rfl
    rw [veronese_monDiHP] at h1
    exact hi ((pow_eq_zero_iff (by omega : d ≠ 0)).mp h1)
  rw [hx0, IsPrim] at hx
  have h0 : Finset.univ.gcd (0 : Fin (n + 1) → ℤ) = 0 :=
    Finset.gcd_eq_zero_iff.mpr (fun _ _ => rfl)
  rw [h0] at hx
  norm_num at hx

lemma one_le_div_log {B : ℝ} (hB : 1 < B) : 1 ≤ B / Real.log B := by
  have h0 : 0 < Real.log B := Real.log_pos hB
  rw [one_le_div h0]
  linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < B)]


/-! ## The per-vector count bound -/


lemma monDiHP_injective (d n : ℕ) (hd : 1 ≤ d) : Function.Injective (monDiHP d n) := by
  intro i j hij
  by_contra hne
  have h := congrArg (fun m : Mon d n => ((m.1 i).val)) hij
  have h1 : ((monDiHP d n i).1 i).val = d := by simp [monDiHP]
  have h2 : ((monDiHP d n j).1 i).val = 0 := by
    simp only [monDiHP, Fin.val_mk]
    rw [if_neg]
    exact fun h => hne h
  rw [h1, h2] at h
  exact (by omega : (d : ℕ) ≠ 0) h

/-- `N_{d,n} = #Mon d n` is at least `n+1`. -/
lemma card_Mon_ge (d n : ℕ) (hd : 1 ≤ d) : n + 1 ≤ NN d n := by
  have := Fintype.card_le_of_injective (monDiHP d n) (monDiHP_injective d n hd)
  simpa [NN] using this

/-- The set of integer vectors of Euclidean norm at most `C` is finite. -/
lemma dg_finite_setOf_eNorm_le {ι : Type*} [Fintype ι] (C : ℝ) :
    {v : ι → ℤ | eNorm v ≤ C}.Finite := by
  refine (Set.Finite.pi fun _ : ι => Set.finite_Icc (-⌈C⌉) ⌈C⌉).subset ?_
  intro v hv
  rw [Set.mem_univ_pi]
  intro i
  rw [Set.mem_Icc]
  have h1 : |((v i : ℤ) : ℝ)| ≤ eNorm v := abs_coord_le_eNorm v i
  have h3 : ((v i : ℤ) : ℝ) ≤ ((⌈C⌉ : ℤ) : ℝ) :=
    le_trans (le_trans (le_abs_self ((v i : ℤ) : ℝ)) (le_trans h1 hv)) (Int.le_ceil C)
  have h4 : (((-⌈C⌉ : ℤ)) : ℝ) ≤ ((v i : ℤ) : ℝ) := by
    push_cast
    exact le_trans (le_trans (neg_le_neg (Int.le_ceil C)) (neg_le_neg hv))
      (le_trans (neg_le_neg h1) (neg_abs_le ((v i : ℤ) : ℝ)))
  exact ⟨Int.cast_le.mp h4, Int.cast_le.mp h3⟩

/-- Master bound for the number of coefficient vectors of norm `≤ A` vanishing at a primitive `x`:
in the non-degenerate regime it is `≪ A^{N-1}/‖ν(x)‖`, and in the degenerate regime it is
`≪ A^{N-n} μ(x)^{n-1}/‖ν(x)‖ + A^{N-n-1}`. -/
lemma ballCount_veronese_le (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ K B₀ : ℝ, 0 < K ∧ 0 < B₀ ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A →
      ∀ x : Fin (n + 1) → ℤ, IsPrim x →
        (ballCount (latOrth (veronese d n x)) A : ℝ) ≤
          K * (if mu1 d n x ≤ A then A ^ (NN d n - 1) / eNorm (veronese d n x)
               else A ^ (NN d n - n) * (mu1 d n x) ^ (n - 1) / eNorm (veronese d n x)
                    + A ^ (NN d n - n - 1)) := by
  classical
  obtain ⟨K₁, hK₁, hpiv⟩ := latOrth_count_pivotal (Mon d n)
  obtain ⟨K₂, hK₂, hdeg⟩ := latOrth_count_degenerate (Mon d n) n
  obtain ⟨K₃, hK₃, hlam⟩ := lam_latOrth_veronese_le d n hd hdn
  have hlam' := hlam
  have hK₃'1 : 1 ≤ max K₃ 1 := le_max_right _ _
  have hK₃'0 : 0 < max K₃ 1 := lt_of_lt_of_le zero_lt_one hK₃'1
  have hK₃'K : K₃ ≤ max K₃ 1 := le_max_left _ _
  have hpow1 : 0 ≤ (max K₃ 1) ^ (NN d n - 1) := pow_nonneg hK₃'0.le _
  have hpow2 : 0 ≤ (max K₃ 1) ^ (n - 1) := pow_nonneg hK₃'0.le _
  refine ⟨1 + K₁ * (max K₃ 1) ^ (NN d n - 1) + K₂ * (max K₃ 1) ^ (n - 1) + K₂, 10,
    by positivity, by norm_num, ?_⟩
  intro A B hB hA x hx
  have hB1 : 1 < B := lt_of_lt_of_le (by norm_num) hB
  have hA1 : 1 ≤ A := le_trans (one_le_div_log hB1) hA
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hc : IsPrim (veronese d n x) := isPrim_veronese d n hd1 hx
  have hnorm : 0 < eNorm (veronese d n x) :=
    eNorm_pos_of_ne_zero (veronese_ne_zero_of_isPrim d n hd1 hx)
  have hlamx : lam (latOrth (veronese d n x)) (Fintype.card (Mon d n) - 1)
      ≤ max K₃ 1 * mu1 d n x := by
    refine le_trans (hlam' x hx) ?_
    exact mul_le_mul_of_nonneg_right hK₃'K (mu1_nonneg d n x)
  have hmono : (ballCount (latOrth (veronese d n x)) A : ℝ)
      ≤ (ballCount (latOrth (veronese d n x)) (max K₃ 1 * A) : ℝ) := by
    have hsub : {v : Mon d n → ℤ | v ∈ latOrth (veronese d n x) ∧ eNorm v ≤ A}
        ⊆ {v : Mon d n → ℤ | v ∈ latOrth (veronese d n x) ∧ eNorm v ≤ max K₃ 1 * A} := by
      intro v hv
      exact ⟨hv.1, by nlinarith [hv.2, hK₃'1, hA0.le, eNorm_nonneg v]⟩
    have hfin : ({v : Mon d n → ℤ |
        v ∈ latOrth (veronese d n x) ∧ eNorm v ≤ max K₃ 1 * A} : Set _).Finite :=
      (dg_finite_setOf_eNorm_le (max K₃ 1 * A)).subset (fun v hv => hv.2)
    have := Set.ncard_le_ncard hsub hfin
    exact_mod_cast this
  have hKb1 : K₁ * (max K₃ 1) ^ (NN d n - 1)
      ≤ 1 + K₁ * (max K₃ 1) ^ (NN d n - 1) + K₂ * (max K₃ 1) ^ (n - 1) + K₂ := by
    linarith [mul_nonneg hK₂.le hpow2, hK₂]
  have hKb2 : K₂ * (max K₃ 1) ^ (n - 1)
      ≤ 1 + K₁ * (max K₃ 1) ^ (NN d n - 1) + K₂ * (max K₃ 1) ^ (n - 1) + K₂ := by
    linarith [mul_nonneg hK₁.le hpow1, hK₂]
  have hKb3 : K₂
      ≤ 1 + K₁ * (max K₃ 1) ^ (NN d n - 1) + K₂ * (max K₃ 1) ^ (n - 1) + K₂ := by
    linarith [mul_nonneg hK₁.le hpow1, mul_nonneg hK₂.le hpow2]
  by_cases hcase : mu1 d n x ≤ A
  · rw [if_pos hcase]
    have hT1 : 1 ≤ max K₃ 1 * A := by nlinarith [hK₃'1, hA1]
    have hlamT : lam (latOrth (veronese d n x)) (Fintype.card (Mon d n) - 1)
        ≤ max K₃ 1 * A := by
      refine le_trans hlamx ?_
      nlinarith [hK₃'0.le, hcase]
    have hp := hpiv (veronese d n x) hc (max K₃ 1 * A) hT1 hlamT
    refine le_trans (le_trans hmono hp) ?_
    have hY : 0 ≤ A ^ (NN d n - 1) / eNorm (veronese d n x) :=
      div_nonneg (pow_nonneg hA0.le _) hnorm.le
    have heq : K₁ * (max K₃ 1 * A) ^ (NN d n - 1) / eNorm (veronese d n x)
        = (K₁ * (max K₃ 1) ^ (NN d n - 1)) *
          (A ^ (NN d n - 1) / eNorm (veronese d n x)) := by
      rw [mul_pow]; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hKb1 hY
  · rw [if_neg hcase]
    have hlt : A < mu1 d n x := not_le.mp hcase
    have hAle : A ≤ max K₃ 1 * mu1 d n x := by
      nlinarith [hlt, hK₃'1, mu1_nonneg d n x]
    have hdT := hdeg (veronese d n x) hc (max K₃ 1 * mu1 d n x) A hA1 hAle hlamx
    refine le_trans hdT ?_
    have heq : K₂ * (A ^ (NN d n - n) * (max K₃ 1 * mu1 d n x) ^ (n - 1) /
            eNorm (veronese d n x) + A ^ (NN d n - n - 1))
        = (K₂ * (max K₃ 1) ^ (n - 1)) * (A ^ (NN d n - n) * (mu1 d n x) ^ (n - 1) /
            eNorm (veronese d n x)) + K₂ * A ^ (NN d n - n - 1) := by
      rw [mul_pow]; ring
    rw [heq]
    have hY : 0 ≤ A ^ (NN d n - n) * (mu1 d n x) ^ (n - 1) / eNorm (veronese d n x) :=
      div_nonneg (mul_nonneg (pow_nonneg hA0.le _) (pow_nonneg (mu1_nonneg d n x) _)) hnorm.le
    have hP : 0 ≤ A ^ (NN d n - n - 1) := pow_nonneg hA0.le _
    calc (K₂ * (max K₃ 1) ^ (n - 1)) *
            (A ^ (NN d n - n) * (mu1 d n x) ^ (n - 1) / eNorm (veronese d n x))
          + K₂ * A ^ (NN d n - n - 1)
        ≤ (1 + K₁ * (max K₃ 1) ^ (NN d n - 1) + K₂ * (max K₃ 1) ^ (n - 1) + K₂) *
            (A ^ (NN d n - n) * (mu1 d n x) ^ (n - 1) / eNorm (veronese d n x))
          + (1 + K₁ * (max K₃ 1) ^ (NN d n - 1) + K₂ * (max K₃ 1) ^ (n - 1) + K₂) *
            A ^ (NN d n - n - 1) :=
          add_le_add (mul_le_mul_of_nonneg_right hKb2 hY)
            (mul_le_mul_of_nonneg_right hKb3 hP)
      _ = (1 + K₁ * (max K₃ 1) ^ (NN d n - 1) + K₂ * (max K₃ 1) ^ (n - 1) + K₂) *
            (A ^ (NN d n - n) * (mu1 d n x) ^ (n - 1) / eNorm (veronese d n x)
              + A ^ (NN d n - n - 1)) := by ring


/-! ## More finsum plumbing -/

section Plumbing2
variable {α β : Type*}

lemma finsum_mem_add' (s : Set α) (hs : s.Finite) (f g : α → ℝ) :
    (∑ᶠ x ∈ s, (f x + g x)) = (∑ᶠ x ∈ s, f x) + ∑ᶠ x ∈ s, g x := by
  rw [finsum_mem_of_finite s hs, finsum_mem_of_finite s hs, finsum_mem_of_finite s hs,
    Finset.sum_add_distrib]

lemma finsum_mem_mul_left' (s : Set α) (hs : s.Finite) (c : ℝ) (f : α → ℝ) :
    (∑ᶠ x ∈ s, c * f x) = c * ∑ᶠ x ∈ s, f x := by
  rw [finsum_mem_of_finite s hs, finsum_mem_of_finite s hs, Finset.mul_sum]

lemma finsum_mem_const (s : Set α) (hs : s.Finite) (c : ℝ) :
    (∑ᶠ x ∈ s, c) = c * (s.ncard : ℝ) := by
  rw [finsum_mem_of_finite s hs, Finset.sum_const, Set.ncard_eq_toFinset_card _ hs,
    nsmul_eq_mul]
  ring

lemma finsum_mem_zero' (s : Set α) (hs : s.Finite) : (∑ᶠ x ∈ s, (0 : ℝ)) = 0 :=
  finsum_mem_zero s

end Plumbing2

/-- Exponent identity `A^{N-n}A^{n-1} = A^{N-1}`. -/
lemma pow_sub_mul_pow_sub' {A : ℝ} {N n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ N) :
    A ^ (N - n) * A ^ (n - 1) = A ^ (N - 1) := by
  rw [← pow_add]
  congr 1
  omega

/-- Exponent identity `A^{N-n-1}A^{n} = A^{N-1}`. -/
lemma pow_sub_mul_pow' {A : ℝ} {N n : ℕ} (h : n + 1 ≤ N) :
    A ^ (N - n - 1) * A ^ n = A ^ (N - 1) := by
  rw [← pow_add]
  congr 1
  omega


variable {α : Type*}

lemma finsum_mem_le' (s : Set α) (hs : s.Finite) {f g : α → ℝ} (h : ∀ x ∈ s, f x ≤ g x) :
    (∑ᶠ x ∈ s, f x) ≤ ∑ᶠ x ∈ s, g x := by
  rw [finsum_mem_of_finite s hs, finsum_mem_of_finite s hs]
  exact Finset.sum_le_sum fun x hx => h x (hs.mem_toFinset.mp hx)

lemma finsum_mem_le_of_subset' (s t : Set α) (hst : s ⊆ t) (ht : t.Finite)
    {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) : (∑ᶠ x ∈ s, f x) ≤ ∑ᶠ x ∈ t, f x := by
  have hs : s.Finite := ht.subset hst
  rw [finsum_mem_of_finite s hs, finsum_mem_of_finite t ht]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro x hx
    exact ht.mem_toFinset.mpr (hst (hs.mem_toFinset.mp hx))
  · intro x _ _; exact hf x

lemma finsum_mem_split_ite' (s : Set α) (hs : s.Finite) (P : α → Prop) [DecidablePred P]
    (f g : α → ℝ) :
    (∑ᶠ x ∈ s, (if P x then f x else g x))
      = (∑ᶠ x ∈ {x ∈ s | P x}, f x) + ∑ᶠ x ∈ {x ∈ s | ¬ P x}, g x := by
  have h1 : ({x ∈ s | P x} : Set α).Finite := hs.subset (fun x hx => hx.1)
  have h2 : ({x ∈ s | ¬ P x} : Set α).Finite := hs.subset (fun x hx => hx.1)
  rw [finsum_mem_of_finite s hs, finsum_mem_of_finite _ h1, finsum_mem_of_finite _ h2]
  have e1 : h1.toFinset = hs.toFinset.filter P := by
    apply Finset.ext; intro x
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_filter]
  have e2 : h2.toFinset = hs.toFinset.filter (fun x => ¬ P x) := by
    apply Finset.ext; intro x
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_filter]
  rw [e1, e2, Finset.sum_ite]


lemma mul_le_mul_of_nonneg_left' {a b c : ℝ} (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  nlinarith [mul_nonneg hc (sub_nonneg.mpr h)]

/-- The set `{x ∈ Ξ(B) : A < μ(x)}` written as the complement of `{x : μ(x) ≤ A}`. -/
lemma degen_set_eq (d n : ℕ) (A B : ℝ) :
    ({x ∈ Xi d n B | ¬ (mu1 d n x ≤ A)} : Set (Fin (n + 1) → ℤ))
      = {x ∈ Xi d n B | A < mu1 d n x} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h; exact ⟨h.1, not_le.mp h.2⟩
  · intro h; exact ⟨h.1, not_le.mpr h.2⟩

/-- **First moment.** The sum over the height ball of `N_V(B)` is `≪ A^{N-1} B`. -/
lemma nv_sum_le (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ K B₀ : ℝ, 0 < K ∧ 0 < B₀ ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A →
      (∑ᶠ a ∈ primSet d n A (fun _ => True), NV d n a B) ≤ K * A ^ (NN d n - 1) * B := by
  classical
  obtain ⟨KP, BP, hKP, hBP, hP⟩ := ballCount_veronese_le d n hd hdn
  obtain ⟨CS, BS, hCS, hBS, hS⟩ := Xi_sum_inv_veronese d n hd hdn
  obtain ⟨KD, BD, hKD, hBD, hD⟩ := degen_sum d n hd hdn
  have hd1 : 1 ≤ d := by omega
  have hN1 : n ≤ NN d n := le_trans (Nat.le_succ n) (card_Mon_ge d n hd1)
  have hN2 : n + 1 ≤ NN d n := card_Mon_ge d n hd1
  refine ⟨KP / 2 * (CS + 2 * KD), max (max BP BS) (max BD 10), by positivity, by positivity, ?_⟩
  intro A B hB hA
  have hB10 : 10 ≤ B := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hB)
  have hBBP : BP ≤ B := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hB)
  have hBBS : BS ≤ B := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hB)
  have hBBD : BD ≤ B := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hB)
  have hA0 : 0 < A :=
    lt_of_lt_of_le zero_lt_one (le_trans (one_le_div_log (by linarith)) hA)
  have hPSfin : (primSet d n A (fun _ => True)).Finite := primSet_finite d n A _
  have hXfin : (Xi d n B).Finite := Xi_finite d n B
  have hstep : (∑ᶠ a ∈ primSet d n A (fun _ => True), NV d n a B)
      = (1 / 2) * ∑ᶠ x ∈ Xi d n B,
          (({a ∈ primSet d n A (fun _ => True) | formEval d n a x = 0} :
            Set (Mon d n → ℤ)).ncard : ℝ) := by
    rw [finsum_mem_of_finite _ hPSfin]
    have h1 : (∑ a ∈ hPSfin.toFinset, NV d n a B)
        = ∑ a ∈ hPSfin.toFinset, (1/2 : ℝ) *
            (({x ∈ Xi d n B | formEval d n a x = 0} : Set (Fin (n+1) → ℤ)).ncard : ℝ) :=
      Finset.sum_congr rfl fun a _ => rfl
    rw [h1, ← Finset.mul_sum]
    rw [← finsum_mem_of_finite _ hPSfin
      (fun a => (({x ∈ Xi d n B | formEval d n a x = 0} : Set (Fin (n+1) → ℤ)).ncard : ℝ))]
    rw [DiagNcard.sum_ncard_swap _ hPSfin _ hXfin (fun a x => formEval d n a x = 0)]
  rw [hstep]
  set F : (Fin (n + 1) → ℤ) → ℝ := fun x =>
    if mu1 d n x ≤ A then A ^ (NN d n - 1) / eNorm (veronese d n x)
    else A ^ (NN d n - n) * (mu1 d n x) ^ (n - 1) / eNorm (veronese d n x)
      + A ^ (NN d n - n - 1) with hF
  have hbound : (∑ᶠ x ∈ Xi d n B,
        (({a ∈ primSet d n A (fun _ => True) | formEval d n a x = 0} :
          Set (Mon d n → ℤ)).ncard : ℝ)) ≤ ∑ᶠ x ∈ Xi d n B, KP * F x := by
    refine finsum_mem_le' _ hXfin ?_
    intro x hx
    have hxprim : IsPrim x := hx.1
    have hsub : ({a ∈ primSet d n A (fun _ => True) | formEval d n a x = 0} : Set (Mon d n → ℤ))
        ⊆ {a : Mon d n → ℤ | a ∈ latOrth (veronese d n x) ∧ eNorm a ≤ A} := by
      intro a ha
      exact ⟨(formEval_eq_zero_iff d n a x).mp ha.2, ha.1.2.1⟩
    have hfin : ({a : Mon d n → ℤ | a ∈ latOrth (veronese d n x) ∧ eNorm a ≤ A} :
        Set _).Finite := (dg_finite_setOf_eNorm_le A).subset (fun a ha => ha.2)
    have hle := Set.ncard_le_ncard hsub hfin
    have hleR : ((({a ∈ primSet d n A (fun _ => True) | formEval d n a x = 0} :
        Set (Mon d n → ℤ)).ncard : ℝ)) ≤ (ballCount (latOrth (veronese d n x)) A : ℝ) := by
      exact_mod_cast hle
    refine le_trans hleR ?_
    have h := hP A B hBBP hA x hxprim
    rw [hF]
    exact h
  refine le_trans (mul_le_mul_of_nonneg_left' hbound (by norm_num : (0:ℝ) ≤ 1 / 2)) ?_
  rw [finsum_mem_mul_left' _ hXfin, finsum_mem_split_ite' _ hXfin (fun x => mu1 d n x ≤ A)]
  have hpart1 : (∑ᶠ x ∈ {x ∈ Xi d n B | mu1 d n x ≤ A},
        A ^ (NN d n - 1) / eNorm (veronese d n x)) ≤ A ^ (NN d n - 1) * (CS * B) := by
    have hfin : ({x ∈ Xi d n B | mu1 d n x ≤ A} : Set (Fin (n+1) → ℤ)).Finite :=
      hXfin.subset (fun x hx => hx.1)
    have h1 : (∑ᶠ x ∈ {x ∈ Xi d n B | mu1 d n x ≤ A},
          A ^ (NN d n - 1) / eNorm (veronese d n x))
        = A ^ (NN d n - 1) * ∑ᶠ x ∈ {x ∈ Xi d n B | mu1 d n x ≤ A},
            1 / eNorm (veronese d n x) := by
      rw [finsum_mem_of_finite _ hfin, finsum_mem_of_finite _ hfin, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [h1]
    refine mul_le_mul_of_nonneg_left' ?_ (pow_nonneg hA0.le _)
    refine le_trans (finsum_mem_le_of_subset' {x ∈ Xi d n B | mu1 d n x ≤ A} (Xi d n B)
      (fun x hx => hx.1) hXfin (fun x => one_div_nonneg.mpr (eNorm_nonneg _))) ?_
    exact (hS B hBBS).1
  have hpart2 : (∑ᶠ x ∈ {x ∈ Xi d n B | ¬ (mu1 d n x ≤ A)},
        (A ^ (NN d n - n) * (mu1 d n x) ^ (n - 1) / eNorm (veronese d n x)
          + A ^ (NN d n - n - 1)))
      ≤ A ^ (NN d n - n) * (KD * A ^ (n - 1) * B)
        + A ^ (NN d n - n - 1) * (KD * A ^ n * B) := by
    have hfin : ({x ∈ Xi d n B | ¬ (mu1 d n x ≤ A)} : Set (Fin (n+1) → ℤ)).Finite :=
      hXfin.subset (fun x hx => hx.1)
    rw [finsum_mem_add' _ hfin]
    have hA1 : (∑ᶠ x ∈ {x ∈ Xi d n B | ¬ (mu1 d n x ≤ A)},
          A ^ (NN d n - n) * (mu1 d n x) ^ (n - 1) / eNorm (veronese d n x))
        ≤ A ^ (NN d n - n) * (KD * A ^ (n - 1) * B) := by
      have h1 : (∑ᶠ x ∈ {x ∈ Xi d n B | ¬ (mu1 d n x ≤ A)},
            A ^ (NN d n - n) * (mu1 d n x) ^ (n - 1) / eNorm (veronese d n x))
          = A ^ (NN d n - n) * ∑ᶠ x ∈ {x ∈ Xi d n B | ¬ (mu1 d n x ≤ A)},
              (mu1 d n x) ^ (n - 1) / eNorm (veronese d n x) := by
        rw [finsum_mem_of_finite _ hfin, finsum_mem_of_finite _ hfin, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [h1]
      refine mul_le_mul_of_nonneg_left' ?_ (pow_nonneg hA0.le _)
      rw [degen_set_eq]
      exact (hD A B hBBD hA).1
    have hA2 : (∑ᶠ x ∈ {x ∈ Xi d n B | ¬ (mu1 d n x ≤ A)}, A ^ (NN d n - n - 1))
        ≤ A ^ (NN d n - n - 1) * (KD * A ^ n * B) := by
      rw [finsum_mem_const _ hfin]
      refine mul_le_mul_of_nonneg_left' ?_ (pow_nonneg hA0.le _)
      rw [degen_set_eq]
      exact (hD A B hBBD hA).2
    linarith [hA1, hA2]
  have hident : A ^ (NN d n - n) * (KD * A ^ (n - 1) * B)
      + A ^ (NN d n - n - 1) * (KD * A ^ n * B)
      = KD * (A ^ (NN d n - 1) * B) + KD * (A ^ (NN d n - 1) * B) := by
    have e1 : A ^ (NN d n - n) * (KD * A ^ (n - 1) * B)
        = KD * (A ^ (NN d n - n) * A ^ (n - 1)) * B := by ring
    have e2 : A ^ (NN d n - n - 1) * (KD * A ^ n * B)
        = KD * (A ^ (NN d n - n - 1) * A ^ n) * B := by ring
    rw [e1, e2, pow_sub_mul_pow_sub' (A := A) (N := NN d n) (n := n) (by omega) hN1,
      pow_sub_mul_pow' (A := A) (N := NN d n) (n := n) hN2]
    ring
  have hmain : (∑ᶠ x ∈ {x ∈ Xi d n B | mu1 d n x ≤ A},
        A ^ (NN d n - 1) / eNorm (veronese d n x))
      + (∑ᶠ x ∈ {x ∈ Xi d n B | ¬ (mu1 d n x ≤ A)},
        (A ^ (NN d n - n) * (mu1 d n x) ^ (n - 1) / eNorm (veronese d n x)
          + A ^ (NN d n - n - 1)))
      ≤ (CS + 2 * KD) * (A ^ (NN d n - 1) * B) := by
    refine le_trans (add_le_add hpart1 hpart2) ?_
    rw [hident]
    nlinarith [hCS, hKD, pow_nonneg hA0.le (NN d n - 1), hA0.le, hB]
  have hfin1 : ((1 / 2) * (KP * ((∑ᶠ x ∈ {x ∈ Xi d n B | mu1 d n x ≤ A},
          A ^ (NN d n - 1) / eNorm (veronese d n x))
        + (∑ᶠ x ∈ {x ∈ Xi d n B | ¬ (mu1 d n x ≤ A)},
          (A ^ (NN d n - n) * (mu1 d n x) ^ (n - 1) / eNorm (veronese d n x)
            + A ^ (NN d n - n - 1))))))
      ≤ (1 / 2) * (KP * ((CS + 2 * KD) * (A ^ (NN d n - 1) * B))) := by
    refine mul_le_mul_of_nonneg_left' ?_ (by norm_num : (0:ℝ) ≤ 1 / 2)
    exact mul_le_mul_of_nonneg_left' hmain hKP.le
  refine le_trans hfin1 (le_of_eq ?_)
  ring

/-! ## The final assembly -/

/-- Diagonal bound for the variance computation: the sum over the height ball of
`N_V(B) + 2 Δ_V^mix(B) + Δ_V^loc(B)` is `≪ A^N · B/A` (Browning–Le Boudec–Sawin, proof of
Proposition "variance", the bounds for `K(A,B)`). -/
theorem diag_bound (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      (∑ᶠ a ∈ primSet d n A (fun _ => True),
        (NV d n a B + 2 * DeltaMix d n a B + DeltaLoc d n a B))
        ≤ K * A ^ NN d n * (B / A) := by
  classical
  obtain ⟨K₁, B₁, hK₁, hB₁, hNV⟩ := nv_sum_le d n hd hdn
  obtain ⟨K₂, B₂, hK₂, hB₂, hMX⟩ := mix_sum_le d n hd hdn
  obtain ⟨K₃, B₃, hK₃, hB₃, hLC⟩ := loc_sum_le d n hd hdn
  refine ⟨K₁ + 2 * K₂ + K₃, max B₁ (max B₂ (max B₃ 10)), by positivity, ?_⟩
  intro A B hB hA hA2
  have hBB₁ : B₁ ≤ B := le_trans (le_max_left _ _) hB
  have hBB₂ : B₂ ≤ B := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hB)
  have hBB₃ : B₃ ≤ B := le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) hB))
  have hB10 : 10 ≤ B := le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) hB))
  have hA0 : 0 < A :=
    lt_of_lt_of_le zero_lt_one (le_trans (one_le_div_log (by linarith)) hA)
  have hPS : (primSet d n A (fun _ => True)).Finite := primSet_finite d n A _
  have hsplit : (∑ᶠ a ∈ primSet d n A (fun _ => True),
        (NV d n a B + 2 * DeltaMix d n a B + DeltaLoc d n a B))
      = (∑ᶠ a ∈ primSet d n A (fun _ => True), NV d n a B)
        + 2 * (∑ᶠ a ∈ primSet d n A (fun _ => True), DeltaMix d n a B)
        + (∑ᶠ a ∈ primSet d n A (fun _ => True), DeltaLoc d n a B) := by
    rw [finsum_mem_of_finite _ hPS, finsum_mem_of_finite _ hPS, finsum_mem_of_finite _ hPS,
      finsum_mem_of_finite _ hPS, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.mul_sum]
  rw [hsplit]
  have h1 := hNV A B hBB₁ hA
  have h2 := hMX A B hBB₂ hA hA2
  have h3 := hLC A B hBB₃ hA hA2
  have hN1 : 1 ≤ NN d n := le_trans (by omega : 1 ≤ n) (le_trans (Nat.le_succ n) (card_Mon_ge d n (by omega)))
  have hkey : A ^ (NN d n - 1) * B = A ^ NN d n * (B / A) := by
    have hN : NN d n = (NN d n - 1) + 1 := (Nat.sub_add_cancel hN1).symm
    have hA' : A ^ NN d n = A ^ (NN d n - 1) * A := by
      conv_lhs => rw [hN, pow_succ]
    rw [hA']
    field_simp
  calc (∑ᶠ a ∈ primSet d n A (fun _ => True), NV d n a B)
        + 2 * (∑ᶠ a ∈ primSet d n A (fun _ => True), DeltaMix d n a B)
        + (∑ᶠ a ∈ primSet d n A (fun _ => True), DeltaLoc d n a B)
      ≤ (K₁ * A ^ (NN d n - 1) * B) + 2 * (K₂ * A ^ (NN d n - 1) * B)
        + (K₃ * A ^ (NN d n - 1) * B) :=
        add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_left' h2 (by norm_num : (0:ℝ) ≤ 2))) h3
    _ = (K₁ + 2 * K₂ + K₃) * (A ^ (NN d n - 1) * B) := by ring
    _ = (K₁ + 2 * K₂ + K₃) * (A ^ NN d n * (B / A)) := by rw [hkey]
    _ = (K₁ + 2 * K₂ + K₃) * A ^ NN d n * (B / A) := by ring


end Work.HP
