import Mathlib
import Submission.Work.BoseDict.Defs
import Submission.Work.BoseFixR.fibre_arith
import Submission.Work.BoseFixR.fibre_peel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDict.modeProd_cIPn` — orthonormality of the symmetric mode products

For a mode family `e : Fin m → ℝ³ → ℂ` orthonormal for the complex `L²(ℝ³)` inner product,

  `⟪M_α, M_β⟫_{L²((ℝ³)ⁿ)} = δ_{αβ} · n!/α!`,   `M_α := modeProd e n α`,

where the pairing is the complex one `Work.BoseDict.cIPn` (`∫ conj(·) · ·`) of
`Work.BoseDict.Defs`.  This is the complex companion of the (real-part) statement
`Work.BoseBoxFock.modeProd_realIP`; the module is written against `Work.BoseDict.Defs`
only, so that it stays inside the light import cone of the dictionary chapter.

## Proof

* `modeAux.conj_modeProd_mul` expands the integrand into the double sum over labellings;
* `modeAux.integrable_modeProd_pair` / `modeAux.integrable_star_mul` provide the
  integrability of the summands (each mode is `MemLp _ ⊤` and supported in the finite
  measure box `boxL ℓ`), which justifies pulling the finite sums out of the integral;
* `modeAux.integral_prodMode` evaluates each summand by Fubini over the product measure
  (`MeasureTheory.integral_fintype_prod_volume_eq_prod`, which is unconditional) using the
  orthonormality `he`;
* `modeAux.sum_indicator_collapse` collapses the double sum to the number of labellings
  realising `α` (or `0` when `α ≠ β`);
* `modeAux.card_modeMult` evaluates that count as the multinomial coefficient `n!/∏_k α_k!`
  (`Work.BoseFixR.fibre_peel` + `Work.BoseFixR.fibre_arith`).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseDict

/-- An a.e. bound for a `MemLp _ ⊤` function. -/
lemma exists_bound_of_memLp_top {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : MemLp f ⊤ μ) : ∃ C : ℝ, ∀ᵐ x ∂μ, ‖f x‖ ≤ C := by
  have hlt : eLpNormEssSup f μ < ⊤ := by
    rw [← eLpNorm_exponent_top hf.aestronglyMeasurable]
    exact hf.eLpNorm_lt_top
  obtain ⟨C, hC⟩ := (eLpNormEssSup_lt_top_iff_isBoundedUnder (f := f) (μ := μ)).mp hlt
  refine ⟨(C : ℝ), ?_⟩
  filter_upwards [hC] with x hx
  have hx' : (‖f x‖₊ : ℝ) ≤ (C : ℝ) := by exact_mod_cast hx
  simpa using hx'

namespace modeAux

variable {m n : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}

/-- A function that is a.e. bounded and vanishes off a set of finite measure is integrable. -/
lemma integrable_of_ae_bound_of_support {f : Sp → ℂ} {s : Set Sp} {C : ℝ}
    (hs : MeasurableSet s) (hfin : volume s < ⊤) (hmeas : AEStronglyMeasurable f volume)
    (hb : ∀ᵐ x ∂volume, ‖f x‖ ≤ C) (hsupp : Function.support f ⊆ s) : Integrable f := by
  have hind : f = s.indicator f := by
    funext x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      by_contra h
      exact hx (hsupp (Function.mem_support.mpr h))
  rw [hind]
  exact (IntegrableOn.of_bound hfin hmeas.restrict C
    (hb.filter_mono (ae_mono Measure.restrict_le_self))).integrable_indicator hs

/-! ## 1. Integrability of the mode factors -/

/-- The two-mode factor `conj (e l) * e l'` is integrable. -/
lemma integrable_star_mul (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ) (l l' : Fin m) :
    Integrable (fun y : Sp => (starRingEnd ℂ) (e l y) * e l' y) := by
  obtain ⟨C₁, hC₁⟩ := exists_bound_of_memLp_top (hbdd l)
  obtain ⟨C₂, hC₂⟩ := exists_bound_of_memLp_top (hbdd l')
  have hmeas : AEStronglyMeasurable
      (fun y : Sp => (starRingEnd ℂ) (e l y) * e l' y) volume :=
    (hbdd l).aestronglyMeasurable.star.mul (hbdd l').aestronglyMeasurable
  refine integrable_of_ae_bound_of_support (s := Work.BoseK15.corpusBox.boxL ℓ)
    (C := C₁ * C₂) (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)
    (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top hmeas ?_ ?_
  · filter_upwards [hC₁, hC₂] with y h1 h2
    rw [norm_mul, starRingEnd_apply, norm_star]
    exact mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
  · intro y hy
    exact hsupp l (Function.mem_support.mpr fun hel => hy (by simp [hel]))

/-- The `n`-fold product of two-mode factors is integrable on the `n`-particle space (the
product of the one-particle Lebesgue measures). -/
lemma integrable_modeProd_pair (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (σ τ : Fin n → Fin m) :
    Integrable (fun x : Xn n =>
      ∏ i : Fin n, ((starRingEnd ℂ) (e (σ i) (x i)) * e (τ i) (x i))) := by
  exact MeasureTheory.Integrable.fintype_prod_dep
    (E := fun _ : Fin n => Sp)
    (f := fun i : Fin n => fun y : Sp =>
      (starRingEnd ℂ) (e (σ i) y) * e (τ i) y)
    (μ := fun _ : Fin n => (volume : Measure Sp))
    (fun i => integrable_star_mul hbdd hsupp (σ i) (τ i))

/-! ## 2. The product integral (Fubini over the `n`-particle space) -/

/-- Fubini over the `n`-particle space plus orthonormality of the modes. -/
theorem integral_prodMode
    (he : ∀ l l', (∫ y : Sp, (starRingEnd ℂ) (e l y) * e l' y) = if l = l' then 1 else 0)
    (σ τ : Fin n → Fin m) :
    (∫ x : Xn n, ∏ i : Fin n, ((starRingEnd ℂ) (e (σ i) (x i)) * e (τ i) (x i)))
      = if σ = τ then 1 else 0 := by
  rw [MeasureTheory.integral_fintype_prod_volume_eq_prod
    (f := fun i : Fin n => fun y : Sp =>
      (starRingEnd ℂ) (e (σ i) y) * e (τ i) y)]
  simp only [he]
  by_cases h : σ = τ
  · subst h
    simp
  · have hex : ∃ i, σ i ≠ τ i := by
      by_contra hc
      exact h (funext fun i => by
        by_contra h2
        exact hc ⟨i, h2⟩)
    obtain ⟨i, hi⟩ := hex
    rw [if_neg h, Finset.prod_eq_zero (Finset.mem_univ i)]
    simp [hi]

/-! ## 3. The pointwise expansion of the product of two mode products -/

/-- The conjugate of `modeProd e n α` times `modeProd e n β`, expanded as the double sum over
labellings. -/
theorem conj_modeProd_mul (α β : Fin m →₀ ℕ) (x : Xn n) :
    (starRingEnd ℂ) (modeProd e n α x) * modeProd e n β x
      = ∑ σ : Fin n → Fin m, ∑ τ : Fin n → Fin m,
          ((if modeMult σ = α then (1 : ℂ) else 0)
              * (if modeMult τ = β then 1 else 0))
            * ∏ i : Fin n, ((starRingEnd ℂ) (e (σ i) (x i)) * e (τ i) (x i)) := by
  have hconj : (starRingEnd ℂ) (modeProd e n α x)
      = ∑ σ : Fin n → Fin m, (if modeMult σ = α then (1 : ℂ) else 0)
          * ∏ i : Fin n, (starRingEnd ℂ) (e (σ i) (x i)) := by
    rw [modeProd, map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [map_mul, map_prod]
    by_cases h : modeMult σ = α <;> simp [h]
  rw [hconj, modeProd, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

/-! ## 4. The multinomial count of the labellings -/

/-- The components of the occupation multi-index are the fibre cardinalities. -/
lemma modeMult_apply (σ : Fin n → Fin m) (i : Fin m) :
    modeMult σ i = (Finset.univ.filter fun d => σ d = i).card := by
  rw [modeMult, Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    exact Finsupp.single_eq_of_ne (Ne.symm hb)
  · intro h
    exact absurd (Finset.mem_univ i) h

lemma modeMult_eq_iff (σ : Fin n → Fin m) (α : Fin m →₀ ℕ) :
    modeMult σ = α ↔ ∀ i, (Finset.univ.filter fun d => σ d = i).card = α i := by
  constructor
  · intro h i
    rw [← modeMult_apply σ i, h]
  · intro h
    ext i
    rw [modeMult_apply, h i]

/-- **The multinomial fibre count** (the `Work.BoseFixR.card_fibre` statement, in the
`Work.BoseDict` namespace: the copy keeps this file clear of the heavy `Work.BoseBoxFock`
chapter). -/
theorem card_fibre_z {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∀ (n : ℕ) (α : ι →₀ ℕ), α.sum (fun _ j => j) = n →
      Fintype.card {σ : Fin n → ι // ∀ i, (Finset.univ.filter fun d => σ d = i).card = α i}
        = n.factorial / (α.prod fun _ j => j.factorial) := by
  intro n
  induction n with
  | zero =>
    intro α hα
    have hα0 : α = 0 := by
      rw [Finsupp.sum] at hα
      ext i
      by_contra hi
      have hmem : i ∈ α.support := Finsupp.mem_support_iff.mpr hi
      exact hi ((Finset.sum_eq_zero_iff.mp hα) i hmem)
    subst hα0
    have h : Fintype.card (Fin 0 → ι) = 1 := by simp
    rw [Fintype.card_congr (Equiv.subtypeUnivEquiv (fun σ : Fin 0 → ι => by intro i; simp)), h]
    simp
  | succ n ih =>
    intro α hα
    rw [Work.BoseFixR.fibre_peel n α]
    have hsum : ∀ k : {k : ι // α k ≠ 0},
        (α.update k.1 (α k.1 - 1)).sum (fun _ j => j) = n := by
      intro k
      have hk : 0 < α k.1 := Nat.pos_of_ne_zero k.2
      have h := Finsupp.sum_update_add (α := ℕ) (β := ℕ) α k.1 (α k.1 - 1) (fun _ j => j)
        (by intro i; rfl) (by intro i a b; rfl)
      omega
    have hterm : ∀ k : {k : ι // α k ≠ 0},
        Fintype.card {τ : Fin n → ι // ∀ i, (Finset.univ.filter fun d => τ d = i).card
            = (α.update k.1 (α k.1 - 1)) i}
          = n.factorial / ((α.update k.1 (α k.1 - 1)).prod fun _ j => j.factorial) :=
      fun k => ih (α.update k.1 (α k.1 - 1)) (hsum k)
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    rw [← Finset.sum_subtype (s := α.support) (h := fun x => Finsupp.mem_support_iff)
      (f := fun k => n.factorial / ((α.update k (α k - 1)).prod fun _ j => j.factorial))]
    have hpos : 0 < α.sum (fun _ j => j) := by omega
    have hn : n = α.sum (fun _ j => j) - 1 := by omega
    conv_lhs => rw [hn]
    rw [Work.BoseFixR.fibre_arith α hpos, hα]

/-- The same count in `Nat.card` form: instance-free, so it can be transported along
`Equiv.subtypeEquivRight` without decidability-instance diamonds. -/
theorem card_fibre_nat {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) (α : ι →₀ ℕ)
    (hα : α.sum (fun _ j => j) = n) :
    Nat.card {σ : Fin n → ι // ∀ i, (Finset.univ.filter fun d => σ d = i).card = α i}
      = n.factorial / (α.prod fun _ j => j.factorial) := by
  rw [Nat.card_eq_fintype_card]
  exact card_fibre_z n α hα

/-- The multinomial count in the normalisation used by `modeProd`: the number of labellings
realising the multi-index `α` is `n!/α!`. -/
theorem card_modeMult (α : Fin m →₀ ℕ) (hα : α.sum (fun _ k => k) = n) :
    ((Finset.univ.filter (fun σ : Fin n → Fin m => modeMult σ = α)).card : ℝ)
      = (n.factorial : ℝ) / Work.BoseB4.mfac α := by
  have hnat : (Finset.univ.filter (fun σ : Fin n → Fin m => modeMult σ = α)).card
      = n.factorial / ∏ k : Fin m, (α k).factorial := by
    rw [(Fintype.card_subtype (fun σ : Fin n → Fin m => modeMult σ = α)).symm,
      ← Nat.card_eq_fintype_card,
      Nat.card_congr (Equiv.subtypeEquivRight (fun σ => modeMult_eq_iff σ α)),
      card_fibre_nat n α hα,
      Finsupp.prod_fintype α (fun _ j => j.factorial) (fun i => by simp)]
  have hsupp : (∑ k ∈ α.support, α k) = n := by
    simpa only [Finsupp.sum] using hα
  have hdvd : (∏ k : Fin m, (α k).factorial) ∣ n.factorial := by
    have h1 : (∏ k : Fin m, (α k).factorial) = ∏ k ∈ α.support, (α k).factorial :=
      (Finset.prod_subset (Finset.subset_univ α.support) (fun x _ hx => by
        rw [Finsupp.notMem_support_iff.mp hx, Nat.factorial_zero])).symm
    rw [h1, ← hsupp]
    exact Nat.prod_factorial_dvd_factorial_sum α.support α
  have hmfac : Work.BoseB4.mfac α = ((∏ k : Fin m, (α k).factorial : ℕ) : ℝ) := by
    rw [Work.BoseB4.mfac, Finsupp.prod_fintype _ _ (fun i => by simp)]
    exact (Nat.cast_prod (fun k : Fin m => (α k).factorial) Finset.univ).symm
  have hne : ((∏ k : Fin m, (α k).factorial : ℕ) : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => Nat.factorial_ne_zero (α k))
  rw [hnat, hmfac]
  exact Nat.cast_div hdvd hne

/-! ## 5. The collapse of the double sum -/

/-- The double sum of occupation indicators against the `σ = τ`-indicator. -/
theorem sum_indicator_collapse (α β : Fin m →₀ ℕ) :
    (∑ σ : Fin n → Fin m, ∑ τ : Fin n → Fin m,
        ((if modeMult σ = α then (1 : ℂ) else 0)
            * (if modeMult τ = β then 1 else 0))
          * (if σ = τ then 1 else 0))
      = if α = β then
          ((Finset.univ.filter (fun σ : Fin n → Fin m => modeMult σ = α)).card : ℂ)
        else 0 := by
  have hinner : ∀ σ : Fin n → Fin m,
      (∑ τ : Fin n → Fin m,
        ((if modeMult σ = α then (1 : ℂ) else 0)
            * (if modeMult τ = β then 1 else 0))
          * (if σ = τ then 1 else 0))
        = (if modeMult σ = α then (1 : ℂ) else 0) * (if modeMult σ = β then 1 else 0) := by
    intro σ
    rw [Finset.sum_eq_single σ]
    · simp
    · intro b _ hb
      rw [if_neg (fun hh : σ = b => hb hh.symm), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ σ) h
  rw [Finset.sum_congr rfl (fun σ _ => hinner σ)]
  by_cases hαβ : α = β
  · rw [if_pos hαβ]
    have hpt : ∀ σ : Fin n → Fin m,
        (if modeMult σ = α then (1 : ℂ) else 0) * (if modeMult σ = β then 1 else 0)
          = (if modeMult σ = α then (1 : ℂ) else 0) := by
      intro σ
      rw [← hαβ]
      by_cases h : modeMult σ = α <;> simp [h]
    rw [← Finset.sum_boole (fun σ : Fin n → Fin m => modeMult σ = α)]
    exact Finset.sum_congr rfl (fun σ _ => hpt σ)
  · rw [if_neg hαβ]
    refine Finset.sum_eq_zero (fun σ _ => ?_)
    by_cases h : modeMult σ = α
    · have hb : ¬ (modeMult σ = β) := fun hh => hαβ (h ▸ hh)
      rw [if_pos h, if_neg hb, mul_zero]
    · rw [if_neg h, zero_mul]

end modeAux

/-! ## 6. The main theorem -/

theorem modeProd_cIPn {m n : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (he : ∀ l l', (∫ x : Work.BoseDict.Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {α β : Fin m →₀ ℕ} (hα : α.sum (fun _ k => k) = n) (hβ : β.sum (fun _ k => k) = n) :
    Work.BoseDict.cIPn n (Work.BoseDict.modeProd e n α) (Work.BoseDict.modeProd e n β)
      = if α = β then ((n.factorial : ℝ) / Work.BoseB4.mfac α : ℂ) else 0 := by
  classical
  -- the summands of the expansion of the integrand
  set Ψ : (Fin n → Fin m) → (Fin n → Fin m) → Xn n → ℂ := fun σ τ x =>
    ((if modeMult σ = α then (1 : ℂ) else 0) * (if modeMult τ = β then 1 else 0))
      * ∏ i : Fin n, ((starRingEnd ℂ) (e (σ i) (x i)) * e (τ i) (x i)) with hΨ
  have hint : ∀ σ τ : Fin n → Fin m, Integrable (Ψ σ τ) := fun σ τ =>
    (modeAux.integrable_modeProd_pair (e := e) hbdd hsupp σ τ).const_mul _
  have hpt : (fun x : Xn n => (starRingEnd ℂ) (modeProd e n α x) * modeProd e n β x)
      = fun x : Xn n => ∑ σ : Fin n → Fin m, ∑ τ : Fin n → Fin m, Ψ σ τ x := by
    funext x
    exact modeAux.conj_modeProd_mul (e := e) α β x
  -- the value of the integral
  have hval : ∀ σ τ : Fin n → Fin m,
      (∫ x : Xn n, Ψ σ τ x) = ((if modeMult σ = α then (1 : ℂ) else 0)
          * (if modeMult τ = β then 1 else 0)) * (if σ = τ then 1 else 0) := by
    intro σ τ
    have h1 : (∫ x : Xn n, Ψ σ τ x) = ((if modeMult σ = α then (1 : ℂ) else 0)
          * (if modeMult τ = β then 1 else 0))
          * ∫ x : Xn n, ∏ i : Fin n,
              ((starRingEnd ℂ) (e (σ i) (x i)) * e (τ i) (x i)) :=
      MeasureTheory.integral_const_mul _ _
    rw [h1, modeAux.integral_prodMode (e := e) he σ τ]
  have hInt : (∫ x : Xn n, (starRingEnd ℂ) (modeProd e n α x) * modeProd e n β x)
      = if α = β then
          ((Finset.univ.filter (fun σ : Fin n → Fin m => modeMult σ = α)).card : ℂ) else 0 := by
    rw [hpt]
    rw [integral_finsetSum _ (fun σ _ => integrable_finsetSum _ (fun τ _ => hint σ τ))]
    have h2 : ∀ σ : Fin n → Fin m,
        (∫ x : Xn n, ∑ τ : Fin n → Fin m, Ψ σ τ x)
          = ∑ τ : Fin n → Fin m, ∫ x : Xn n, Ψ σ τ x := fun σ =>
      integral_finsetSum _ (fun τ _ => hint σ τ)
    rw [Finset.sum_congr rfl (fun σ _ => h2 σ)]
    refine (Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun τ _ => hval σ τ))).trans ?_
    exact modeAux.sum_indicator_collapse α β
  -- the complex pairing is exactly that integral
  rw [cIPn, hInt]
  by_cases h : α = β
  · rw [if_pos h, if_pos h]
    exact_mod_cast modeAux.card_modeMult (n := n) α hα
  · rw [if_neg h, if_neg h]

end Work.BoseDict
