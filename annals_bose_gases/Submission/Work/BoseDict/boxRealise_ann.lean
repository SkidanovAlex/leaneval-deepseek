import Mathlib
import Submission.Work.BoseDict.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDict.boxRealise_ann` — the box ↔ model intertwining of annihilation

The dictionary half of the box→model correspondence (`BF3b`).  With `boxRealise e d` the
realisation of the model monomials on the box (`x^α ↦ (α!/√(d!)) • M_α`,
`M_α = modeProd e d α`) and `boxAnn e l d` the box annihilation of the mode `e l`
(`(boxAnn e l d Θ)(y) = √(d+1) ∫_z conj(e l z) Θ(z,y)`), the *intertwining identity*

    boxRealise e d (ann m l Ψ) = boxAnn e l d (boxRealise e (d+1) Ψ)

holds for every model vector `Ψ` (the hypothesis `hΨ` that `Ψ` is supported in degree
`d+1` is in fact not needed: on other degrees both sides are zero).

## Proof

Both sides are `ℝ`-linear in `Ψ`, so it suffices to check the identity on the basis
`Finsupp.single γ 1` (`Finsupp.induction_linear`).  The whole content is then the
one-variable integral identity (`integral_conj_mul_modeProd_cons`)

    ∫_z conj(e l z) · M_γ(z, y) = if γ l = 0 then 0 else M_{γ-e_l}(y)  (γ : Fin m →₀ ℕ),

obtained by expanding `modeProd e (d+1) γ` as the sum over labellings `σ : Fin (d+1) → Fin m`,
splitting off the first coordinate (`Fin.prod_univ_succ`, `Fin.consEquiv`) and using the
orthonormality `he`; the combinatorics of the occupation multi-index are in `modeMult_cons`
and `sum_ite_modeMult_shift`.  The linearity of `boxAnn` in the state (over the integrable
elements) is `boxAnn_add`/`boxAnn_smul`; the finite-sum induction is justified by
`integrable_conj_boxRealise`.  The scalar bookkeeping of the two normalisations
(`mfac`, `√(d!)`) is `scalar_key`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. Integrability helpers -/

private lemma exists_bound_of_memLp_top_aux {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : MemLp f ⊤ μ) : ∃ C : ℝ, ∀ᵐ x ∂μ, ‖f x‖ ≤ C := by
  have hlt : eLpNormEssSup f μ < ⊤ := by
    rw [← eLpNorm_exponent_top hf.aestronglyMeasurable]
    exact hf.eLpNorm_lt_top
  obtain ⟨C, hC⟩ := (eLpNormEssSup_lt_top_iff_isBoundedUnder (f := f) (μ := μ)).mp hlt
  refine ⟨(C : ℝ), ?_⟩
  filter_upwards [hC] with x hx
  have hx' : (‖f x‖₊ : ℝ) ≤ (C : ℝ) := by exact_mod_cast hx
  simpa using hx'

/-- A function that is a.e. bounded and vanishes off a set of finite measure is integrable. -/
private lemma integrable_of_ae_bound_of_support_aux {f : Sp → ℂ} {s : Set Sp} {C : ℝ}
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

/-- The two-mode factor `conj (e l) * e l'` is integrable. -/
private lemma integrable_star_mul_aux {m : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ) (l l' : Fin m) :
    Integrable (fun y : Sp => (starRingEnd ℂ) (e l y) * e l' y) := by
  obtain ⟨C₁, hC₁⟩ := exists_bound_of_memLp_top_aux (hbdd l)
  obtain ⟨C₂, hC₂⟩ := exists_bound_of_memLp_top_aux (hbdd l')
  have hmeas : AEStronglyMeasurable
      (fun y : Sp => (starRingEnd ℂ) (e l y) * e l' y) volume :=
    (hbdd l).aestronglyMeasurable.star.mul (hbdd l').aestronglyMeasurable
  refine integrable_of_ae_bound_of_support_aux (s := Work.BoseK15.corpusBox.boxL ℓ)
    (C := C₁ * C₂) (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)
    (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top hmeas ?_ ?_
  · filter_upwards [hC₁, hC₂] with y h1 h2
    rw [norm_mul, starRingEnd_apply, norm_star]
    exact mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
  · intro y hy
    exact hsupp l (Function.mem_support.mpr fun hel => hy (by simp [hel]))

/-! ## 1. The occupation multi-index of a `cons`-labelling -/

/-- `modeMult (Fin.cons l τ) = e_l + modeMult τ`. -/
private lemma modeMult_cons {m d : ℕ} (l : Fin m) (τ : Fin d → Fin m) :
    modeMult (Fin.cons l τ : Fin (d+1) → Fin m) = Finsupp.single l 1 + modeMult τ := by
  have hcard : ∀ k : Fin m,
      (Finset.univ.filter fun i : Fin (d+1) => (Fin.cons l τ : Fin (d+1) → Fin m) i = k).card
        = (Finset.univ.filter fun j : Fin d => τ j = k).card + (if l = k then 1 else 0) := by
    intro k
    rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    omega
  simp only [modeMult]
  rw [Finset.sum_congr rfl (fun k _ => by rw [hcard k])]
  simp only [Finsupp.single_add]
  rw [Finset.sum_add_distrib]
  have h2 : (∑ k : Fin m, Finsupp.single k (if l = k then (1:ℕ) else 0))
      = ∑ k : Fin m, (if l = k then Finsupp.single l 1 else 0) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : l = k
    · subst h; simp
    · simp [h]
  rw [h2, Finset.sum_ite_eq, if_pos (Finset.mem_univ l), add_comm]

/-- Collapsing the sum over labellings whose occupation is the shift of `γ` by one
quantum of the mode `l`. -/
private lemma sum_ite_modeMult_shift {m d : ℕ} (l : Fin m) (γ : Fin m →₀ ℕ)
    (g : (Fin d → Fin m) → ℂ) :
    (∑ τ : Fin d → Fin m, (if Finsupp.single l 1 + modeMult τ = γ then (1:ℂ) else 0) * g τ)
      = if γ l = 0 then 0
        else ∑ τ : Fin d → Fin m,
          (if modeMult τ = γ - Finsupp.single l 1 then (1:ℂ) else 0) * g τ := by
  have hsub : ∀ μ : Fin m →₀ ℕ, (Finsupp.single l 1 + μ) - Finsupp.single l 1 = μ :=
    fun μ => add_tsub_cancel_left _ _
  have hkey : γ l ≠ 0 → Finsupp.single l 1 + (γ - Finsupp.single l 1) = γ := by
    intro hγ
    rw [add_comm]
    exact tsub_add_cancel_of_le ((Finsupp.single_le_iff).mpr (Nat.pos_of_ne_zero hγ))
  have hiff : γ l ≠ 0 → ∀ τ : Fin d → Fin m,
      (Finsupp.single l 1 + modeMult τ = γ) ↔ (modeMult τ = γ - Finsupp.single l 1) := by
    intro hγ τ
    constructor
    · intro h
      rw [← hsub (modeMult τ), h]
    · intro h
      rw [h]
      exact hkey hγ
  by_cases hγ : γ l = 0
  · rw [if_pos hγ]
    refine Finset.sum_eq_zero fun τ _ => ?_
    rw [if_neg, zero_mul]
    intro hcon
    have hcoord := congrArg (fun f : Fin m →₀ ℕ => f l) hcon
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hcoord
    omega
  · rw [if_neg hγ]
    refine Finset.sum_congr rfl fun τ _ => ?_
    by_cases h : Finsupp.single l 1 + modeMult τ = γ
    · rw [if_pos h, if_pos ((hiff hγ τ).mp h)]
    · rw [if_neg h, if_neg (fun hh => h ((hiff hγ τ).mpr hh))]

/-! ## 2. The one-variable integral -/

/-- Integrability of `conj (e l) · modeProd e (d+1) α` in the first variable. -/
private lemma integrable_conj_mul_modeProd_cons {m d : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (l : Fin m) (α : Fin m →₀ ℕ) (y : Xn d) :
    Integrable (fun z : Sp => (starRingEnd ℂ) (e l z) * modeProd e (d+1) α (Fin.cons z y)) := by
  have hpt : (fun z : Sp => (starRingEnd ℂ) (e l z) * modeProd e (d + 1) α (Fin.cons z y))
      = fun z => ∑ σ : Fin (d+1) → Fin m,
          (starRingEnd ℂ) (e l z) * ((if modeMult σ = α then (1:ℂ) else 0)
            * ∏ i : Fin (d+1), e (σ i) ((Fin.cons z y : Xn (d+1)) i)) := by
    funext z
    rw [modeProd, Finset.mul_sum]
  rw [hpt]
  refine integrable_finsetSum _ (fun σ _ => ?_)
  have hfun : (fun z : Sp => (starRingEnd ℂ) (e l z) * ((if modeMult σ = α then (1:ℂ) else 0)
        * ∏ i : Fin (d+1), e (σ i) ((Fin.cons z y : Xn (d+1)) i)))
      = fun z => (((if modeMult σ = α then (1:ℂ) else 0) * ∏ i : Fin d, e (σ i.succ) (y i))
          * ((starRingEnd ℂ) (e l z) * e (σ 0) z)) := by
    funext z
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    ring
  rw [hfun]
  exact (integrable_star_mul_aux hbdd hsupp l (σ 0)).const_mul _

/-- **The one-variable integral identity**: contracting the first variable of the symmetric
mode product against `conj (e l)` annihilates the mode `l`. -/
private lemma integral_conj_mul_modeProd_cons {m d : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (l : Fin m) (γ : Fin m →₀ ℕ) (y : Xn d) :
    (∫ z : Sp, (starRingEnd ℂ) (e l z) * modeProd e (d + 1) γ (Fin.cons z y))
      = if γ l = 0 then 0 else modeProd e d (γ - Work.BoseB4.e m l) y := by
  classical
  have hpt : (fun z : Sp => (starRingEnd ℂ) (e l z) * modeProd e (d + 1) γ (Fin.cons z y))
      = fun z => ∑ σ : Fin (d+1) → Fin m,
          (starRingEnd ℂ) (e l z) * ((if modeMult σ = γ then (1:ℂ) else 0)
            * ∏ i : Fin (d+1), e (σ i) ((Fin.cons z y : Xn (d+1)) i)) := by
    funext z
    rw [modeProd, Finset.mul_sum]
  rw [hpt]
  have hσ : ∀ σ : Fin (d+1) → Fin m,
      Integrable (fun z : Sp => (starRingEnd ℂ) (e l z) * ((if modeMult σ = γ then (1:ℂ) else 0)
            * ∏ i : Fin (d+1), e (σ i) ((Fin.cons z y : Xn (d+1)) i))) ∧
      (∫ z : Sp, (starRingEnd ℂ) (e l z) * ((if modeMult σ = γ then (1:ℂ) else 0)
            * ∏ i : Fin (d+1), e (σ i) ((Fin.cons z y : Xn (d+1)) i)))
        = ((if modeMult σ = γ then (1:ℂ) else 0) * ∏ i : Fin d, e (σ i.succ) (y i))
            * (if l = σ 0 then 1 else 0) := by
    intro σ
    have hfun : (fun z : Sp => (starRingEnd ℂ) (e l z) * ((if modeMult σ = γ then (1:ℂ) else 0)
            * ∏ i : Fin (d+1), e (σ i) ((Fin.cons z y : Xn (d+1)) i)))
        = fun z => (((if modeMult σ = γ then (1:ℂ) else 0) * ∏ i : Fin d, e (σ i.succ) (y i))
            * ((starRingEnd ℂ) (e l z) * e (σ 0) z)) := by
      funext z
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      ring
    constructor
    · rw [hfun]
      exact (integrable_star_mul_aux hbdd hsupp l (σ 0)).const_mul _
    · rw [hfun, MeasureTheory.integral_const_mul, he l (σ 0)]
  rw [integral_finsetSum _ (fun σ _ => (hσ σ).1)]
  rw [Finset.sum_congr rfl (fun σ _ => (hσ σ).2)]
  let G : (Fin (d+1) → Fin m) → ℂ := fun σ =>
    ((if modeMult σ = γ then (1:ℂ) else 0) * ∏ i : Fin d, e (σ i.succ) (y i))
      * (if l = σ 0 then 1 else 0)
  show (∑ σ : Fin (d+1) → Fin m, G σ) = _
  have hA : (∑ σ : Fin (d+1) → Fin m, G σ)
      = ∑ p : Fin m × (Fin d → Fin m), G (Fin.cons p.1 p.2) :=
    (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (d+1) => Fin m))
      (fun p : Fin m × (Fin d → Fin m) => G (Fin.cons p.1 p.2)) G (fun p => rfl)).symm
  have hB : (∑ p : Fin m × (Fin d → Fin m), G (Fin.cons p.1 p.2))
      = ∑ a : Fin m, ∑ τ : Fin d → Fin m, G (Fin.cons a τ) :=
    Fintype.sum_prod_type _
  have hC : (∑ a : Fin m, ∑ τ : Fin d → Fin m, G (Fin.cons a τ))
      = ∑ τ : Fin d → Fin m, G (Fin.cons l τ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    refine Finset.sum_eq_single l (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ l) h)
    simp only [G, Fin.cons_zero, if_neg (Ne.symm hb), mul_zero]
  have hGl : ∀ τ : Fin d → Fin m, G (Fin.cons l τ)
      = (if Finsupp.single l 1 + modeMult τ = γ then (1:ℂ) else 0)
          * ∏ i : Fin d, e (τ i) (y i) := by
    intro τ
    simp only [G, Fin.cons_zero, Fin.cons_succ, modeMult_cons]
    simp
  rw [hA, hB, hC]
  rw [Finset.sum_congr rfl (fun τ _ => hGl τ)]
  rw [sum_ite_modeMult_shift l γ (fun τ => ∏ i : Fin d, e (τ i) (y i))]
  rw [modeProd]
  rfl

/-! ## 3. Linearity of `boxAnn` in the state -/

private lemma boxAnn_smul {m : ℕ} {e : Fin m → Sp → ℂ} {l : Fin m} {d : ℕ} (s : ℝ)
    (Θ : Xn (d+1) → ℂ) :
    boxAnn e l d (s • Θ) = s • boxAnn e l d Θ := by
  funext y
  show (Real.sqrt ((d:ℝ)+1) : ℂ) * (∫ z : Sp, (starRingEnd ℂ) (e l z) * (s • Θ) (Fin.cons z y))
      = (s : ℂ) * ((Real.sqrt ((d:ℝ)+1) : ℂ)
          * (∫ z : Sp, (starRingEnd ℂ) (e l z) * Θ (Fin.cons z y)))
  have hfun : (fun z : Sp => (starRingEnd ℂ) (e l z) * (s • Θ) (Fin.cons z y))
      = fun z => (s : ℂ) * ((starRingEnd ℂ) (e l z) * Θ (Fin.cons z y)) := by
    funext z
    rw [Pi.smul_apply, Complex.real_smul]
    ring
  rw [hfun, MeasureTheory.integral_const_mul]
  ring

private lemma boxAnn_add {m : ℕ} {e : Fin m → Sp → ℂ} {l : Fin m} {d : ℕ}
    {Θ Θ' : Xn (d+1) → ℂ}
    (hΘ : ∀ y : Xn d, Integrable (fun z : Sp => (starRingEnd ℂ) (e l z) * Θ (Fin.cons z y)))
    (hΘ' : ∀ y : Xn d, Integrable (fun z : Sp => (starRingEnd ℂ) (e l z) * Θ' (Fin.cons z y))) :
    boxAnn e l d (Θ + Θ') = boxAnn e l d Θ + boxAnn e l d Θ' := by
  funext y
  show (Real.sqrt ((d:ℝ)+1) : ℂ) * (∫ z : Sp, (starRingEnd ℂ) (e l z) * (Θ + Θ') (Fin.cons z y))
      = (Real.sqrt ((d:ℝ)+1) : ℂ) * (∫ z : Sp, (starRingEnd ℂ) (e l z) * Θ (Fin.cons z y))
        + (Real.sqrt ((d:ℝ)+1) : ℂ) * (∫ z : Sp, (starRingEnd ℂ) (e l z) * Θ' (Fin.cons z y))
  have hfun : (fun z : Sp => (starRingEnd ℂ) (e l z) * (Θ + Θ') (Fin.cons z y))
      = fun z => (starRingEnd ℂ) (e l z) * Θ (Fin.cons z y)
          + (starRingEnd ℂ) (e l z) * Θ' (Fin.cons z y) := by
    funext z
    rw [Pi.add_apply, mul_add]
  rw [hfun, MeasureTheory.integral_add (hΘ y) (hΘ' y)]
  ring

/-! ## 4. `boxRealise` of a basis vector, and integrability against `conj (e l)` -/

private lemma boxRealise_single_smul {m : ℕ} (e : Fin m → Sp → ℂ) (d : ℕ)
    (α : Fin m →₀ ℕ) (c : ℝ) :
    boxRealise e d (Finsupp.single α c) = c • boxRealise e d (Finsupp.single α 1) := by
  have h : (Finsupp.single α c : Work.BoseB4.RealFock m) = c • Finsupp.single α (1:ℝ) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [h, map_smul]

/-- `conj (e l) · boxRealise e (d+1) Ψ`, in the first variable, is integrable. -/
private lemma integrable_conj_boxRealise {m d : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (l : Fin m) (Ψ : Work.BoseB4.RealFock m) (y : Xn d) :
    Integrable (fun z : Sp => (starRingEnd ℂ) (e l z) * (boxRealise e (d+1) Ψ) (Fin.cons z y)) := by
  classical
  induction Ψ using Finsupp.induction_linear with
  | zero =>
      have h0 : (fun z : Sp => (starRingEnd ℂ) (e l z)
            * (boxRealise e (d+1) (0 : Work.BoseB4.RealFock m)) (Fin.cons z y)) = 0 := by
        funext z; simp
      rw [h0]
      exact integrable_zero _ _ _
  | add f g hf hg =>
      have hfun : (fun z : Sp => (starRingEnd ℂ) (e l z)
            * (boxRealise e (d+1) (f + g)) (Fin.cons z y))
          = fun z : Sp => (starRingEnd ℂ) (e l z) * (boxRealise e (d+1) f) (Fin.cons z y)
            + (starRingEnd ℂ) (e l z) * (boxRealise e (d+1) g) (Fin.cons z y) := by
        funext z; rw [map_add, Pi.add_apply, mul_add]
      rw [hfun]
      exact hf.add hg
  | single α c =>
      have hΦ : boxRealise e (d+1) (Finsupp.single α c)
          = ((c * (if α.sum (fun _ k => k) = d+1 then
                (Work.BoseB4.mfac α / Real.sqrt (((d+1).factorial : ℕ) : ℝ) : ℝ) else 0)) : ℝ)
              • modeProd e (d+1) α := by
        rw [boxRealise_single_smul, boxRealise_single, smul_smul]
      have hfun : (fun z : Sp => (starRingEnd ℂ) (e l z)
            * (boxRealise e (d+1) (Finsupp.single α c)) (Fin.cons z y))
          = fun z => (((c * (if α.sum (fun _ k => k) = d+1 then
                (Work.BoseB4.mfac α / Real.sqrt (((d+1).factorial : ℕ) : ℝ) : ℝ) else 0)) : ℝ) : ℂ)
              * ((starRingEnd ℂ) (e l z) * modeProd e (d+1) α (Fin.cons z y)) := by
        funext z
        rw [hΦ, Pi.smul_apply, Complex.real_smul]
        ring
      rw [hfun]
      exact (integrable_conj_mul_modeProd_cons hbdd hsupp l α y).const_mul _

/-! ## 5. Degree and normalisation arithmetic -/

/-- The total occupation (degree) of a multi-index. -/
private def dg {m : ℕ} (α : Fin m →₀ ℕ) : ℕ := α.sum (fun _ k => k)

private lemma dg_add {m : ℕ} (α β : Fin m →₀ ℕ) : dg (α + β) = dg α + dg β := by
  rw [dg, dg, dg]
  exact Finsupp.sum_add_index' (fun a => rfl) (fun a b₁ b₂ => rfl)

private lemma dg_e {m : ℕ} (l : Fin m) : dg (Work.BoseB4.e m l) = 1 := by
  rw [dg, Work.BoseB4.e]
  exact Finsupp.sum_single_index rfl

private lemma dg_sub_e {m : ℕ} (l : Fin m) (γ : Fin m →₀ ℕ) (h : γ l ≠ 0) :
    dg γ = dg (γ - Work.BoseB4.e m l) + 1 := by
  have hadd : (γ - Work.BoseB4.e m l) + Work.BoseB4.e m l = γ := by
    rw [Work.BoseB4.e]
    exact tsub_add_cancel_of_le ((Finsupp.single_le_iff).mpr (Nat.pos_of_ne_zero h))
  have h2 : dg ((γ - Work.BoseB4.e m l) + Work.BoseB4.e m l)
      = dg (γ - Work.BoseB4.e m l) + 1 := by
    rw [dg_add, dg_e]
  rwa [hadd] at h2

private lemma mfac_sub_e {m : ℕ} (l : Fin m) (γ : Fin m →₀ ℕ) (h : γ l ≠ 0) :
    Work.BoseB4.mfac γ = (γ l : ℝ) * Work.BoseB4.mfac (γ - Work.BoseB4.e m l) := by
  have hadd : (γ - Work.BoseB4.e m l) + Work.BoseB4.e m l = γ := by
    rw [Work.BoseB4.e]
    exact tsub_add_cancel_of_le ((Finsupp.single_le_iff).mpr (Nat.pos_of_ne_zero h))
  have h1 := Work.BoseB4.mfac_add_e l (γ - Work.BoseB4.e m l)
  rw [hadd] at h1
  have h2 : (((γ - Work.BoseB4.e m l) l : ℕ) : ℝ) + 1 = (γ l : ℝ) := by
    have hl : (γ - Work.BoseB4.e m l) l = γ l - 1 := by
      rw [Finsupp.tsub_apply, Work.BoseB4.e, Finsupp.single_eq_same]
    rw [hl, Nat.cast_sub (by omega : 1 ≤ γ l)]
    ring
  rw [h2] at h1
  exact h1

private lemma sqrt_succ_factorial (d : ℕ) :
    Real.sqrt (((d+1).factorial : ℕ) : ℝ)
      = Real.sqrt ((d : ℝ) + 1) * Real.sqrt ((d.factorial : ℕ) : ℝ) := by
  rw [Nat.factorial_succ, Nat.cast_mul]
  rw [show (((d + 1 : ℕ) : ℝ)) = (d:ℝ)+1 by push_cast; ring]
  rw [Real.sqrt_mul (by positivity)]

/-- The scalar bookkeeping of the two normalisations: the `mfac` factor and the `√(d!)`. -/
private lemma scalar_key {m : ℕ} (l : Fin m) (γ : Fin m →₀ ℕ) (d : ℕ) (hγ : γ l ≠ 0) :
    (γ l : ℝ) * (if (γ - Work.BoseB4.e m l).sum (fun _ k => k) = d then
        (Work.BoseB4.mfac (γ - Work.BoseB4.e m l) / Real.sqrt ((d.factorial : ℕ) : ℝ)) else 0)
      = (if γ.sum (fun _ k => k) = d+1 then
          (Work.BoseB4.mfac γ / Real.sqrt (((d+1).factorial : ℕ) : ℝ)) else 0)
        * Real.sqrt ((d:ℝ)+1) := by
  have hsub := dg_sub_e l γ hγ
  by_cases hdeg : γ.sum (fun _ k => k) = d + 1
  · have hd : (γ - Work.BoseB4.e m l).sum (fun _ k => k) = d := by
      change dg (γ - Work.BoseB4.e m l) = d
      rw [show dg γ = γ.sum (fun _ k => k) from rfl, hdeg] at hsub
      omega
    rw [if_pos hd, if_pos hdeg, mfac_sub_e l γ hγ, sqrt_succ_factorial d]
    have h1 : Real.sqrt ((d : ℝ) + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos (by positivity))
    have h2 : Real.sqrt ((d.factorial : ℕ) : ℝ) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos_of_pos (by exact_mod_cast Nat.factorial_pos d))
    field_simp
  · have hd : (γ - Work.BoseB4.e m l).sum (fun _ k => k) ≠ d := by
      intro hc
      apply hdeg
      change dg γ = d + 1
      have hc' : dg (γ - Work.BoseB4.e m l) = d := hc
      omega
    rw [if_neg hd, if_neg hdeg, mul_zero, zero_mul]

/-! ## 6. The intertwining identity -/

/-- The intertwining identity for an arbitrary model vector (no degree restriction: on
degrees other than `d+1` both sides vanish). -/
private lemma boxRealise_ann_aux {m d : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (l : Fin m) (Ψ : Work.BoseB4.RealFock m) :
    boxRealise e d (Work.BoseB4.ann m l Ψ)
      = boxAnn e l d (boxRealise e (d + 1) Ψ) := by
  classical
  induction Ψ using Finsupp.induction_linear with
  | zero =>
      simp only [map_zero]
      funext y
      simp [boxAnn]
  | add f g hf hg =>
      have hBf := integrable_conj_boxRealise (d := d) hbdd hsupp l f
      have hBg := integrable_conj_boxRealise (d := d) hbdd hsupp l g
      have h1 : boxRealise e d (Work.BoseB4.ann m l (f + g))
          = boxRealise e d (Work.BoseB4.ann m l f) + boxRealise e d (Work.BoseB4.ann m l g) := by
        rw [map_add, map_add]
      have h2 : boxRealise e (d + 1) (f + g)
          = boxRealise e (d + 1) f + boxRealise e (d + 1) g := map_add _ _ _
      rw [h1, h2, boxAnn_add hBf hBg, hf, hg]
  | single γ c =>
      have hL : boxRealise e d (Work.BoseB4.ann m l (Finsupp.single γ c))
          = (((γ l : ℝ) * c) * (if (γ - Work.BoseB4.e m l).sum (fun _ k => k) = d then
                (Work.BoseB4.mfac (γ - Work.BoseB4.e m l)
                  / Real.sqrt ((d.factorial : ℕ) : ℝ) : ℝ) else 0))
              • modeProd e d (γ - Work.BoseB4.e m l) := by
        rw [Work.BoseB4.ann_single_basis, map_smul, boxRealise_single, smul_smul]
      have hAnn : boxAnn e l d (modeProd e (d+1) γ)
          = fun y => (Real.sqrt ((d:ℝ)+1) : ℂ)
              * (if γ l = 0 then 0 else modeProd e d (γ - Work.BoseB4.e m l) y) := by
        funext y
        show (Real.sqrt ((d:ℝ)+1) : ℂ)
            * (∫ z : Sp, (starRingEnd ℂ) (e l z) * modeProd e (d + 1) γ (Fin.cons z y))
          = (Real.sqrt ((d:ℝ)+1) : ℂ)
              * (if γ l = 0 then 0 else modeProd e d (γ - Work.BoseB4.e m l) y)
        rw [integral_conj_mul_modeProd_cons he hbdd hsupp l γ y]
      have hR : boxAnn e l d (boxRealise e (d+1) (Finsupp.single γ c))
          = (c * (if γ.sum (fun _ k => k) = d+1 then
                (Work.BoseB4.mfac γ / Real.sqrt (((d+1).factorial : ℕ) : ℝ) : ℝ) else 0))
              • (fun y => (Real.sqrt ((d:ℝ)+1) : ℂ)
                  * (if γ l = 0 then 0 else modeProd e d (γ - Work.BoseB4.e m l) y)) := by
        rw [boxRealise_single_smul, boxRealise_single, boxAnn_smul, boxAnn_smul, hAnn, smul_smul]
      rw [hL, hR]
      funext y
      simp only [Pi.smul_apply, Complex.real_smul]
      by_cases hγ : γ l = 0
      · simp [hγ]
      · rw [if_neg hγ]
        have hsc' : (((γ l : ℝ) * c) * (if (γ - Work.BoseB4.e m l).sum (fun _ k => k) = d then
                (Work.BoseB4.mfac (γ - Work.BoseB4.e m l)
                  / Real.sqrt ((d.factorial : ℕ) : ℝ)) else 0))
            = (c * (if γ.sum (fun _ k => k) = d+1 then
                (Work.BoseB4.mfac γ / Real.sqrt (((d+1).factorial : ℕ) : ℝ)) else 0))
              * Real.sqrt ((d:ℝ)+1) := by
          linear_combination c * scalar_key l γ d hγ
        rw [hsc']
        push_cast
        ring

theorem boxRealise_ann {m d : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (he : ∀ l l', (∫ x : Work.BoseDict.Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (l : Fin m) (Ψ : Work.BoseB4.RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 1) :
    Work.BoseDict.boxRealise e d (Work.BoseB4.ann m l Ψ)
      = Work.BoseDict.boxAnn e l d (Work.BoseDict.boxRealise e (d + 1) Ψ) :=
  boxRealise_ann_aux he hbdd hsupp l Ψ

end Work.BoseDict
