import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseDict.Defs3
import Submission.Work.BoseDict.boxRealise_ann
import Submission.Work.BoseDict.modeProd_cIPn
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDict.boxRealise_annOf_annOf` — the dictionary intertwining of two superposed
annihilations

`Work.BoseDict.boxRealise e d` realises the model monomials `x^α` of degree `d` on the box
as `(α!/√(d!)) • M_α`, `M_α = modeProd e d α`.  The mode-wise intertwining

    boxRealise e d (ann m l Ψ) = boxAnn e l d (boxRealise e (d+1) Ψ)

is `Work.BoseDict.boxRealise_ann`.  The model's rows use the *superposed* annihilations
`annOf m w = Σ_l w_l · ann m l`, so the dictionary needs the superposition version

    boxRealise e d (annOf m w Ψ) = boxAnnOf e w d (boxRealise e (d+1) Ψ),

with `boxAnnOf e w d` the box annihilation of `η_w = Σ_l w_l e_l`
(`(boxAnnOf e w d Θ)(y) = √(d+1) ∫_z conj(η_w z) Θ(z,y)`).  The present module proves it
and then iterates it twice, which is the identity needed to transport the rows of the model
Hamiltonian that contain a *product* of two annihilations:

    boxRealise e d (annOf m w (annOf m v Ψ))
      = boxAnnOf e w d (boxAnnOf e v (d+1) (boxRealise e (d+2) Ψ)) .

## Proof

1. `integrable_conj_boxRealise` — for every model vector `Ψ` the function
   `z ↦ conj(e l z) · boxRealise e (d+1) Ψ (z, y)` is integrable (expand `Ψ` in the
   monomial basis and each `modeProd` in the labellings, then use that the one-particle
   two-mode factor `conj(e l)·e l'` is integrable: `modeAux.integrable_star_mul`);
2. `boxAnnOf_eq_sum` — with that integrability, the finite sum and the integral commute and
   `boxAnnOf e w d Θ = Σ_l w_l • boxAnn e l d Θ` (expand `conj(η_w) = Σ_l w_l conj(e_l)`);
3. `boxRealise_annOf'` — the superposition intertwining, by `annOf = Σ_l w_l ann m l`
   (`LinearMap.sum_apply`), linearity of `boxRealise` and `boxRealise_ann`;
4. `annOf_support_degree` — `annOf m v` lowers the degree by one
   (`Work.BoseB4.ann_apply` gives `(annOf m v Ψ) β = Σ_l v_l (β_l+1) Ψ(β+e_l)`),
   which supplies the degree hypothesis needed for the second application of (3).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. `boxRealise` of a scaled basis vector -/

/-- `boxRealise` of a scaled basis vector (linearity in the coefficient). -/
lemma boxRealise_single_smul' {m : ℕ} (e : Fin m → Sp → ℂ) (d : ℕ)
    (α : Fin m →₀ ℕ) (c : ℝ) :
    boxRealise e d (Finsupp.single α c) = c • boxRealise e d (Finsupp.single α 1) := by
  have h : (Finsupp.single α c : Work.BoseB4.RealFock m) = c • Finsupp.single α (1 : ℝ) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [h, map_smul]

/-! ## 1. Integrability of `conj (e l) · M_α(z, y)` in the first variable -/

/-- Integrability in the *first* variable of `conj (e l) · M_α` with the remaining variables
fixed (the `modeProd` is expanded in the labellings and the first coordinate split off). -/
lemma integrable_conj_mul_modeProd_cons {m d : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (l : Fin m) (α : Fin m →₀ ℕ) (y : Xn d) :
    Integrable (fun z : Sp => (starRingEnd ℂ) (e l z) * modeProd e (d + 1) α (Fin.cons z y)) := by
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
  exact (modeAux.integrable_star_mul (e := e) hbdd hsupp l (σ 0)).const_mul _

/-- Integrability in the *first* variable of `conj (e l) · boxRealise e (d+1) Ψ` with the
remaining variables fixed. -/
lemma integrable_conj_boxRealise {m d : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (l : Fin m) (Ψ : Work.BoseB4.RealFock m) (y : Xn d) :
    Integrable (fun z : Sp =>
      (starRingEnd ℂ) (e l z) * (boxRealise e (d + 1) Ψ) (Fin.cons z y)) := by
  classical
  induction Ψ using Finsupp.induction_linear with
  | zero =>
      have h0 : (fun z : Sp => (starRingEnd ℂ) (e l z)
            * (boxRealise e (d + 1) (0 : Work.BoseB4.RealFock m)) (Fin.cons z y)) = 0 := by
        funext z; simp
      rw [h0]
      exact integrable_zero _ _ _
  | add f g hf hg =>
      have hfun : (fun z : Sp => (starRingEnd ℂ) (e l z)
            * (boxRealise e (d + 1) (f + g)) (Fin.cons z y))
          = fun z : Sp => (starRingEnd ℂ) (e l z) * (boxRealise e (d + 1) f) (Fin.cons z y)
            + (starRingEnd ℂ) (e l z) * (boxRealise e (d + 1) g) (Fin.cons z y) := by
        funext z; rw [map_add, Pi.add_apply, mul_add]
      rw [hfun]
      exact hf.add hg
  | single α c =>
      have hΦ : boxRealise e (d + 1) (Finsupp.single α c)
          = ((c * (if α.sum (fun _ k => k) = d + 1 then
                (Work.BoseB4.mfac α / Real.sqrt (((d+1).factorial : ℕ) : ℝ) : ℝ) else 0)) : ℝ)
              • modeProd e (d + 1) α := by
        rw [boxRealise_single_smul', boxRealise_single, smul_smul]
      have hfun : (fun z : Sp => (starRingEnd ℂ) (e l z)
            * (boxRealise e (d + 1) (Finsupp.single α c)) (Fin.cons z y))
          = fun z => (((c * (if α.sum (fun _ k => k) = d + 1 then
                (Work.BoseB4.mfac α / Real.sqrt (((d+1).factorial : ℕ) : ℝ) : ℝ) else 0)) : ℝ) : ℂ)
              * ((starRingEnd ℂ) (e l z) * modeProd e (d + 1) α (Fin.cons z y)) := by
        funext z
        rw [hΦ, Pi.smul_apply, Complex.real_smul]
        ring
      rw [hfun]
      exact (integrable_conj_mul_modeProd_cons hbdd hsupp l α y).const_mul _

/-! ## 2. `boxAnnOf` is the sum of the mode-wise annihilations -/

/-- The annihilation of a superposition is the superposition of the annihilations:
`boxAnnOf e w d Θ = Σ_l w_l • boxAnn e l d Θ`.  (The integrability hypothesis is exactly
what is needed to commute the finite sum with the integral.) -/
lemma boxAnnOf_eq_sum {m d : ℕ} {e : Fin m → Sp → ℂ} (w : Fin m → ℝ) (Θ : Xn (d+1) → ℂ)
    (hΘ : ∀ (l : Fin m) (y : Xn d),
      Integrable (fun z : Sp => (starRingEnd ℂ) (e l z) * Θ (Fin.cons z y))) :
    boxAnnOf e w d Θ = ∑ l : Fin m, (w l) • boxAnn e l d Θ := by
  funext y
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Complex.real_smul, boxAnnOf, boxAnn]
  have hconj : ∀ z : Sp, (starRingEnd ℂ) (etaOf e w z)
      = ∑ l : Fin m, ((w l : ℝ) : ℂ) * (starRingEnd ℂ) (e l z) := by
    intro z
    rw [etaOf, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, Complex.conj_ofReal]
  have hpt : ∀ z : Sp, (starRingEnd ℂ) (etaOf e w z) * Θ (Fin.cons z y)
      = ∑ l : Fin m, ((w l : ℝ) : ℂ) * ((starRingEnd ℂ) (e l z) * Θ (Fin.cons z y)) := by
    intro z
    rw [hconj z, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun l _ => (hΘ l y).const_mul _)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul]
  ring

/-! ## 3. The superposition intertwining -/

/-- **The box ↔ model dictionary for a superposed annihilation**:
`boxRealise e d (annOf m w Ψ) = boxAnnOf e w d (boxRealise e (d+1) Ψ)` for `Ψ` of degree
`d+1`. -/
lemma boxRealise_annOf' {m d : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) (Ψ : Work.BoseB4.RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 1) :
    boxRealise e d (Work.BoseB4.annOf m w Ψ) = boxAnnOf e w d (boxRealise e (d + 1) Ψ) := by
  have h1 : boxRealise e d (Work.BoseB4.annOf m w Ψ)
      = ∑ l : Fin m, (w l) • boxRealise e d (Work.BoseB4.ann m l Ψ) := by
    rw [Work.BoseB4.annOf, LinearMap.sum_apply]
    rw [map_sum]
    exact Finset.sum_congr rfl fun l _ => by
      rw [LinearMap.smul_apply, map_smul]
  rw [h1]
  rw [Finset.sum_congr rfl (fun l _ => by rw [boxRealise_ann he hbdd hsupp l Ψ hΨ])]
  exact (boxAnnOf_eq_sum (e := e) w (boxRealise e (d + 1) Ψ)
    (fun l y => integrable_conj_boxRealise hbdd hsupp l Ψ y)).symm

/-! ## 4. The degree of a superposed annihilation -/

/-- The explicit coefficient of `annOf`: lowering the `l`-th occupation multiplies by the
old occupation `β_l + 1`. -/
lemma annOf_apply' {m : ℕ} (v : Fin m → ℝ) (Ψ : Work.BoseB4.RealFock m) (β : Fin m →₀ ℕ) :
    (Work.BoseB4.annOf m v Ψ) β
      = ∑ l : Fin m, v l * (((β l : ℝ) + 1) * Ψ (β + Work.BoseB4.e m l)) := by
  have h : (Work.BoseB4.annOf m v) Ψ
      = ∑ l : Fin m, (v l) • (Work.BoseB4.ann m l Ψ) := by
    rw [Work.BoseB4.annOf, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun l _ => LinearMap.smul_apply (v l) (Work.BoseB4.ann m l) Ψ
  rw [h, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, Work.BoseB4.ann_apply]

/-- The degree of a single mode multi-index. -/
lemma e_degree {m : ℕ} (l : Fin m) : (Work.BoseB4.e m l).sum (fun _ k => k) = 1 := by
  rw [Work.BoseB4.e]
  exact Finsupp.sum_single_index rfl

/-- **A superposed annihilation lowers the degree by one**: if every monomial of `Ψ` has
degree `n`, then every monomial of `annOf m v Ψ` has degree `n-1`. -/
lemma annOf_support_degree {m n : ℕ} (v : Fin m → ℝ) (Ψ : Work.BoseB4.RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = n) :
    ∀ β ∈ (Work.BoseB4.annOf m v Ψ).support, β.sum (fun _ k => k) = n - 1 := by
  intro β hβ
  rw [Finsupp.mem_support_iff] at hβ
  rw [annOf_apply'] at hβ
  obtain ⟨l, hl⟩ : ∃ l : Fin m, v l * (((β l : ℝ) + 1) * Ψ (β + Work.BoseB4.e m l)) ≠ 0 := by
    by_contra h
    rw [not_exists] at h
    exact hβ (Finset.sum_eq_zero fun l _ => by
      by_contra hc
      exact h l hc)
  have hz : Ψ (β + Work.BoseB4.e m l) ≠ 0 := by
    intro h0
    exact hl (by rw [h0, mul_zero, mul_zero])
  have hmem : (β + Work.BoseB4.e m l) ∈ Ψ.support := Finsupp.mem_support_iff.mpr hz
  have hdeg : (β + Work.BoseB4.e m l).sum (fun _ k => k) = n := hΨ _ hmem
  have hsplit : (β + Work.BoseB4.e m l).sum (fun _ k => k)
      = β.sum (fun _ k => k) + 1 := by
    rw [Finsupp.sum_add_index' (fun a => rfl) (fun a b₁ b₂ => rfl), e_degree l]
  omega

/-! ## 5. The target: two superposed annihilations -/

theorem boxRealise_annOf_annOf {m d : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (he : ∀ l l', (∫ x : Work.BoseDict.Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) (Ψ : Work.BoseB4.RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 2) :
    Work.BoseDict.boxRealise e d (Work.BoseB4.annOf m w (Work.BoseB4.annOf m v Ψ))
      = Work.BoseDict.boxAnnOf e w d
          (Work.BoseDict.boxAnnOf e v (d + 1) (Work.BoseDict.boxRealise e (d + 2) Ψ)) := by
  have hdeg : ∀ β ∈ (Work.BoseB4.annOf m v Ψ).support, β.sum (fun _ k => k) = d + 1 := by
    have h := annOf_support_degree (n := d + 2) v Ψ hΨ
    intro β hβ
    have h' := h β hβ
    omega
  have h1 := boxRealise_annOf' he hbdd hsupp w (Work.BoseB4.annOf m v Ψ) hdeg
  have h2 : Work.BoseDict.boxRealise e (d + 1) (Work.BoseB4.annOf m v Ψ)
      = Work.BoseDict.boxAnnOf e v (d + 1) (Work.BoseDict.boxRealise e (d + 2) Ψ) :=
    boxRealise_annOf' (d := d + 1) he hbdd hsupp v Ψ hΨ
  rw [h1, h2]

end Work.BoseDict
