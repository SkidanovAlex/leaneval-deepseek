import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ℓ¹ ≤ C · (weighted ℓ²)`: Cauchy–Schwarz on the Fourier coefficient lattice `ℤ^ι`

For a coefficient family `c : (ι → ℤ) → ℂ` and the weight `⟨k⟩² = wt k`, the weighted `ℓ²`-sum
`Σ_k ⟨k⟩^{2s} ‖c k‖²` controls the `ℓ¹`-norm `Σ_k ‖c k‖` as soon as the *dual* weight
`Σ_k ⟨k⟩^{-2s}` converges, which happens precisely when `Fintype.card ι < 2 s`.

The proof is Cauchy–Schwarz (Hölder with `p = q = 2`) applied to the splitting
`‖c k‖ = √(⟨k⟩^{2s} ‖c k‖²) · √(⟨k⟩^{-2s})`, with constant `C = √(Σ_k ⟨k⟩^{-2s})`.
The convergence of `Σ_k ⟨k⟩^{-2s}` for `card ι < 2s` is the lattice-sum estimate: since
`∏_i (1 + k_i²) ≤ (wt k)^{card ι}` and `t = s / card ι` satisfies `1 < 2t`, the summand is
dominated by the product `∏_i (1 + k_i²)^{-t}`, whose sum factorises over the coordinates.

All auxiliary lemmas are `private`: they are proved here from scratch and the file depends
only on Mathlib and on the definition of the weight `wt` in `Torus.lean`.
-/

noncomputable section

namespace Work.Diff.STE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. Cauchy–Schwarz with the weight split as `√⟨k⟩^{2s} · √⟨k⟩^{-2s}` -/

/-- Cauchy–Schwarz in the form needed: the `ℓ¹`-norm of a coefficient family is bounded by
`√(Σ ⟨k⟩^{-2s}) · √(Σ ⟨k⟩^{2s}‖c k‖²)`. -/
private lemma l1_le_sqrt_CSq_of_summable (s : ℕ)
    (hB : Summable (fun k : ι → ℤ => ((wt k) ^ s)⁻¹)) (c : (ι → ℤ) → ℂ)
    (hA : Summable (fun k : ι → ℤ => (wt k) ^ s * ‖c k‖ ^ 2)) :
    (∑' k : ι → ℤ, ‖c k‖) ≤ Real.sqrt (∑' k : ι → ℤ, ((wt k) ^ s)⁻¹) *
      Real.sqrt (∑' k : ι → ℤ, (wt k) ^ s * ‖c k‖ ^ 2) := by
  have h22 : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hfs : Summable fun k : ι → ℤ => (Real.sqrt ((wt k) ^ s * ‖c k‖ ^ 2)) ^ (2 : ℝ) :=
    hA.congr fun k => by
      have hk : 0 ≤ (wt k) ^ s * ‖c k‖ ^ 2 :=
        mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) s) (sq_nonneg _)
      rw [Real.rpow_two, Real.sq_sqrt hk]
  have hgs : Summable fun k : ι → ℤ => (Real.sqrt (((wt k) ^ s)⁻¹)) ^ (2 : ℝ) :=
    hB.congr fun k => by
      have hk : 0 ≤ ((wt k) ^ s)⁻¹ := inv_nonneg.mpr (pow_nonneg (le_of_lt (wt_pos k)) s)
      rw [Real.rpow_two, Real.sq_sqrt hk]
  obtain ⟨_, hle⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg (p := 2) (q := 2) h22
    (fun k => Real.sqrt_nonneg _) (fun k => Real.sqrt_nonneg _) hfs hgs
  have hFA : (∑' k : ι → ℤ, (Real.sqrt ((wt k) ^ s * ‖c k‖ ^ 2)) ^ (2 : ℝ))
      = ∑' k : ι → ℤ, (wt k) ^ s * ‖c k‖ ^ 2 :=
    tsum_congr fun k => by
      have hk : 0 ≤ (wt k) ^ s * ‖c k‖ ^ 2 :=
        mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) s) (sq_nonneg _)
      rw [Real.rpow_two, Real.sq_sqrt hk]
  have hGB : (∑' k : ι → ℤ, (Real.sqrt (((wt k) ^ s)⁻¹)) ^ (2 : ℝ))
      = ∑' k : ι → ℤ, ((wt k) ^ s)⁻¹ :=
    tsum_congr fun k => by
      have hk : 0 ≤ ((wt k) ^ s)⁻¹ := inv_nonneg.mpr (pow_nonneg (le_of_lt (wt_pos k)) s)
      rw [Real.rpow_two, Real.sq_sqrt hk]
  have hpt : ∀ k : ι → ℤ,
      Real.sqrt ((wt k) ^ s * ‖c k‖ ^ 2) * Real.sqrt (((wt k) ^ s)⁻¹) = ‖c k‖ := by
    intro k
    have hZ : 0 ≤ (wt k) ^ s * ‖c k‖ ^ 2 :=
      mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) s) (sq_nonneg _)
    have hw : ((wt k) ^ s) ≠ 0 := pow_ne_zero _ (ne_of_gt (wt_pos k))
    rw [← Real.sqrt_mul hZ]
    have hcancel : (wt k) ^ s * ‖c k‖ ^ 2 * ((wt k) ^ s)⁻¹ = ‖c k‖ ^ 2 :=
      calc (wt k) ^ s * ‖c k‖ ^ 2 * ((wt k) ^ s)⁻¹
          = ‖c k‖ ^ 2 * ((wt k) ^ s * ((wt k) ^ s)⁻¹) := by ring
        _ = ‖c k‖ ^ 2 * 1 := by rw [mul_inv_cancel₀ hw]
        _ = ‖c k‖ ^ 2 := by rw [mul_one]
    rw [hcancel, Real.sqrt_sq (norm_nonneg _)]
  rw [show (∑' k : ι → ℤ, ‖c k‖) = ∑' k : ι → ℤ,
        Real.sqrt ((wt k) ^ s * ‖c k‖ ^ 2) * Real.sqrt (((wt k) ^ s)⁻¹) from
      tsum_congr fun k => (hpt k).symm]
  refine hle.trans (le_of_eq ?_)
  rw [hFA, hGB, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, mul_comm]

/-! ## 2. The pointwise comparison `⟨k⟩^{-2s} ≤ ∏_i (1 + k_i²)^{-t}` -/

/-- The elementary bound behind the lattice-sum estimate: for `t = s / card ι`,
`⟨k⟩^{-2s} ≤ ∏_i (1 + k_i²)^{-t}`. -/
private lemma inv_wt_pow_le_prod (s : ℕ) (hd0 : 0 < Fintype.card ι) (k : ι → ℤ) :
    ((wt k) ^ s)⁻¹ ≤
      ∏ i : ι, (1 + (((k i : ℤ)) : ℝ) ^ 2) ^ (-((s : ℝ) / (Fintype.card ι))) := by
  set t : ℝ := (s : ℝ) / (Fintype.card ι) with ht_def
  have hdpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hd0
  have ht : (Fintype.card ι : ℝ) * t = (s : ℝ) := by
    rw [ht_def, mul_div_cancel₀ (s : ℝ) (ne_of_gt hdpos)]
  have ht0 : 0 ≤ t := by
    have h1 : 0 ≤ (Fintype.card ι : ℝ) * t := by rw [ht]; positivity
    exact (mul_nonneg_iff_of_pos_left hdpos).mp h1
  have hprod_nonneg : 0 ≤ ∏ i : ι, (1 + (((k i : ℤ)) : ℝ) ^ 2) :=
    Finset.prod_nonneg fun i _ => by positivity
  -- `∏_i (1 + k_i²) ≤ (wt k)^{card ι}`
  have hle : ∏ i : ι, (1 + (((k i : ℤ)) : ℝ) ^ 2) ≤ (wt k) ^ (Fintype.card ι) := by
    calc ∏ i : ι, (1 + (((k i : ℤ)) : ℝ) ^ 2)
        ≤ ∏ _i : ι, wt k := by
          refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => ?_)
          have h : (((k i : ℤ)) : ℝ) ^ 2 ≤ ∑ j : ι, (((k j : ℤ)) : ℝ) ^ 2 :=
            Finset.single_le_sum (f := fun j : ι => (((k j : ℤ)) : ℝ) ^ 2)
              (fun j _ => sq_nonneg _) (Finset.mem_univ i)
          simp only [wt]
          linarith
      _ = (wt k) ^ (Fintype.card ι) := by simp [Finset.prod_const]
  -- raise to the power `t`
  have hraise : (∏ i : ι, (1 + (((k i : ℤ)) : ℝ) ^ 2)) ^ t
      ≤ ((wt k) ^ (Fintype.card ι)) ^ t :=
    Real.rpow_le_rpow hprod_nonneg hle ht0
  have hpow : ((wt k) ^ (Fintype.card ι) : ℝ) ^ t = (wt k) ^ s := by
    rw [← Real.rpow_natCast (wt k) (Fintype.card ι), ← Real.rpow_mul (le_of_lt (wt_pos k)),
      ht, Real.rpow_natCast (wt k) s]
  have hPt : 0 < (∏ i : ι, (1 + (((k i : ℤ)) : ℝ) ^ 2)) ^ t :=
    Real.rpow_pos_of_pos (Finset.prod_pos fun i _ => by positivity) t
  have hcmp : ((wt k) ^ s)⁻¹ ≤ ((∏ i : ι, (1 + (((k i : ℤ)) : ℝ) ^ 2)) ^ t)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hPt (hraise.trans (le_of_eq hpow))
  refine hcmp.trans (le_of_eq ?_)
  rw [← Real.finsetProd_rpow Finset.univ
      (fun i : ι => 1 + (((k i : ℤ)) : ℝ) ^ 2) (fun i _ => by positivity)]
  rw [← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [Real.rpow_neg (by positivity)]

/-! ## 3. Summability over `Fin d`, and Fubini for a finite product of weights -/

/-- A finite product of nonnegative summable families on `β` is summable as a function on
`Fin d → β`. -/
private lemma summable_fin_prod {β : Type*} : ∀ (d : ℕ) (F : Fin d → β → ℝ),
    (∀ j, Summable (F j)) → (∀ j n, 0 ≤ F j n) →
    Summable (fun k : Fin d → β => ∏ j, F j (k j))
  | 0, _, _, _ => by
      have : Subsingleton (Fin 0 → β) := ⟨fun a b => funext fun i => i.elim0⟩
      exact Summable.of_finite
  | d + 1, F, hF, h0 => by
      let e : β × (Fin d → β) ≃ (Fin (d + 1) → β) := Fin.consEquiv (fun _ : Fin (d + 1) => β)
      rw [← e.summable_iff]
      have hpt : ∀ x : β × (Fin d → β),
          (∏ j : Fin (d + 1), F j ((e x) j)) = F 0 x.1 * ∏ j : Fin d, F j.succ (x.2 j) := by
        intro x
        have hx : e x = Fin.cons (α := fun _ : Fin (d + 1) => β) x.1 x.2 := rfl
        rw [hx, Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
      have hg : Summable (fun k' : Fin d → β => ∏ j : Fin d, F j.succ (k' j)) :=
        summable_fin_prod d (fun j => F j.succ) (fun j => hF j.succ) (fun j n => h0 j.succ n)
      refine (Summable.mul_of_nonneg (hF 0) hg (h0 0)
        (fun k' => Finset.prod_nonneg fun j _ => h0 j.succ (k' j))).congr fun x => ?_
      exact (hpt x).symm

omit [DecidableEq ι] in
/-- Fubini (Tonelli) for a finite product of nonnegative summable families on `ℤ`. -/
private lemma summable_pi_prod {β : Type*} (f : ι → β → ℝ)
    (hf : ∀ i, Summable (f i)) (h0 : ∀ i n, 0 ≤ f i n) :
    Summable (fun k : ι → β => ∏ i, f i (k i)) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hG : Summable (fun k' : Fin (Fintype.card ι) → β => ∏ j, f (e.symm j) (k' j)) :=
    summable_fin_prod (Fintype.card ι) (fun j => f (e.symm j)) (fun j => hf (e.symm j))
      (fun j n => h0 (e.symm j) n)
  have hcomp : Summable ((fun k' : Fin (Fintype.card ι) → β => ∏ j, f (e.symm j) (k' j)) ∘
      (Equiv.arrowCongr e (Equiv.refl β))) :=
    (Equiv.summable_iff (Equiv.arrowCongr e (Equiv.refl β))).mpr hG
  refine hcomp.congr fun k => ?_
  simp only [Function.comp_apply, Equiv.arrowCongr_apply, Equiv.coe_refl]
  exact Equiv.prod_comp e.symm (fun i => f i (k i))

/-! ## 4. The one-dimensional `p`-series over `ℤ` -/

/-- `Σ_{n ∈ ℤ} (1 + n²)^{-t}` converges for `t > 1/2`. -/
private lemma summable_one_add_sq_rpow_neg (t : ℝ) (ht : 1 < 2 * t) :
    Summable (fun n : ℤ => (1 + (((n : ℤ)) : ℝ) ^ 2) ^ (-t)) := by
  have hdom : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ (-(2 * t))) :=
    (summable_nat_add_iff 1).mpr
      ((Real.summable_nat_rpow_inv.mpr ht).congr fun n =>
        (Real.rpow_neg (Nat.cast_nonneg n) (2 * t)).symm)
  have hpos : Summable (fun n : ℕ => (1 + (((n : ℕ)) : ℝ) ^ 2) ^ (-t)) := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (by positivity) _)
      (fun n => ?_) hdom
    have hx : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hle : (((n + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 + (((n + 1 : ℕ) : ℝ)) ^ 2 := by
      linarith [sq_nonneg (((n + 1 : ℕ) : ℝ))]
    calc (1 + (((n + 1 : ℕ) : ℝ)) ^ 2) ^ (-t)
        ≤ ((((n + 1 : ℕ) : ℝ)) ^ 2) ^ (-t) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
      _ = (((n + 1 : ℕ) : ℝ)) ^ (-(2 * t)) := by
          rw [← Real.rpow_natCast (((n + 1 : ℕ) : ℝ)) 2,
            ← Real.rpow_mul (le_of_lt hx) ((2 : ℕ) : ℝ) (-t)]
          congr 1
          push_cast
          ring
  refine Summable.of_nat_of_neg hpos ?_
  refine hpos.congr fun n => ?_
  rw [Int.cast_neg, Int.cast_natCast, neg_sq]

/-! ## 5. Summability of the product weights -/

omit [DecidableEq ι] in
/-- The product `∏_i (1 + k_i²)^{-t}` is summable over `ℤ^ι` when `t > 1/2`. -/
private lemma summable_prod_one_add_sq (t : ℝ) (ht : 1 < 2 * t) :
    Summable (fun k : ι → ℤ => ∏ i : ι, (1 + (((k i : ℤ)) : ℝ) ^ 2) ^ (-t)) :=
  summable_pi_prod (β := ℤ) (fun _ : ι => fun n : ℤ => (1 + (((n : ℤ)) : ℝ) ^ 2) ^ (-t))
    (fun _ => summable_one_add_sq_rpow_neg t ht)
    (fun _ n => Real.rpow_nonneg (by positivity) _)

/-! ## 6. Summability of `⟨k⟩^{-2s}` -/

/-- The lattice sum `Σ_k ⟨k⟩^{-2s}` converges when `card ι < 2s`. -/
private lemma summable_wt_inv (s : ℕ) (hs : Fintype.card ι < 2 * s) :
    Summable (fun k : ι → ℤ => ((wt k) ^ s)⁻¹) := by
  by_cases hd : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hd
    exact Summable.of_finite
  · have hd0 : 0 < Fintype.card ι := Nat.pos_of_ne_zero hd
    have hdpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hd0
    have ht : 1 < 2 * ((s : ℝ) / (Fintype.card ι)) := by
      have hcast : ((Fintype.card ι : ℕ) : ℝ) < 2 * (s : ℝ) := by
        rw [← Nat.cast_two, ← Nat.cast_mul]
        exact_mod_cast hs
      rw [← mul_div_assoc, lt_div_iff₀ hdpos, one_mul]
      exact hcast
    refine Summable.of_nonneg_of_le (fun k => ?_)
      (fun k => inv_wt_pow_le_prod s hd0 k) (summable_prod_one_add_sq _ ht)
    exact inv_nonneg.mpr (pow_nonneg (le_of_lt (wt_pos k)) s)

/-! ## 7. The main estimate -/

theorem l1_le_sqrt_CSq {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ)
    (hs : Fintype.card ι < 2 * s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : (ι → ℤ) → ℂ,
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖c k‖ ^ 2) →
      (∑' k : ι → ℤ, ‖c k‖)
        ≤ C * Real.sqrt (∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ s * ‖c k‖ ^ 2) := by
  refine ⟨Real.sqrt (∑' k : ι → ℤ, ((wt k) ^ s)⁻¹), Real.sqrt_nonneg _, ?_⟩
  intro c hc
  exact l1_le_sqrt_CSq_of_summable s (summable_wt_inv s hs) c hc

end Work.Diff.STE
