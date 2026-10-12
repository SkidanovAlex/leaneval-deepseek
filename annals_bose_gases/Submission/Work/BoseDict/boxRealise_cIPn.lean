import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseDict.modeProd_cIPn
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDict.boxRealise_cIPn` — the box realisation is an isometry onto the model

This is identity (1) of `BoseBoxFock/BF3B_PLAN_S4.md` §1 (the **isometry** leg of the
box ↔ model dictionary): for the realisation

`boxRealise e d Ψ = Σ_α Ψ_α · (α!/√(d!)) · M_α`,  `M_α = modeProd e d α`

of the model monomials `x^α` (`|α| = d`) on the box, and for `Ψ, Ψ'` supported in degree
`d`,

`cIPn d (boxRealise e d Ψ) (boxRealise e d Ψ') = bomb m Ψ Ψ'`,

i.e. the `L²((ℝ³)^d)` pairing of the realised vectors is the Bombieri form of the model.

## Proof

* `boxRealise_eq_sum` expands `boxRealise e d Ψ` on `Ψ.support`, where the guard
  `|α| = d` of the definition is discharged by the hypothesis `hΨ`;
* `cIPn_sum_sum` pushes the complex pairing through the two finite sums of mode products
  (legitimate because `conj (M_α) * M_β` is integrable, `integrable_conj_modeProd_mul`,
  which itself is the labelling expansion `modeAux.conj_modeProd_mul` plus the
  integrability of the labelling products `modeAux.integrable_modeProd_pair`);
* the resulting double sum of `cIPn d (M_α) (M_β)` is evaluated with the orthonormality
  `modeProd_cIPn` (`= δ_{αβ} d!/α!`) and collapses onto the diagonal, where the constant
  `(α!/√(d!))² · d!/α! = α!` (`coeff_arith`) produces exactly the Bombieri weight of
  `bomb m Ψ Ψ' = Σ_α α! Ψ_α Ψ'_α` (`Work.BoseB4.bomb_apply`).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseDict

set_option autoImplicit false

/-! ## 1. The arithmetic of the normalisation constant -/

/-- `(mf/s)² · (D/mf) = mf` whenever `s² = D ≠ 0` and `mf ≠ 0`. -/
lemma coeff_arith {mf D s : ℝ} (hs : s * s = D) (hD : D ≠ 0) (hmf : mf ≠ 0) :
    (mf / s) * (mf / s) * (D / mf) = mf := by
  have hs0 : s ≠ 0 := fun h => hD (by rw [← hs, h, mul_zero])
  field_simp
  rw [← hs]
  ring

/-- The same with the coefficients of the two vectors: `(ψ·c)(ψ'·c)(D/mf) = mf·ψ·ψ'`. -/
lemma coeff_arith2 {mf D s ψ ψ' : ℝ} (hs : s * s = D) (hD : D ≠ 0) (hmf : mf ≠ 0) :
    (ψ * (mf / s)) * (ψ' * (mf / s)) * (D / mf) = mf * ψ * ψ' := by
  have h1 := coeff_arith (mf := mf) (D := D) (s := s) hs hD hmf
  calc (ψ * (mf / s)) * (ψ' * (mf / s)) * (D / mf)
      = ψ * ψ' * ((mf / s) * (mf / s) * (D / mf)) := by ring
    _ = ψ * ψ' * mf := by rw [h1]
    _ = mf * ψ * ψ' := by ring

/-! ## 2. Integrability of the products of two mode products -/

/-- `conj (M_α) · M_β` is integrable on the `n`-particle space: by
`modeAux.conj_modeProd_mul` it is a finite sum of products of two-mode factors, each
integrable by `modeAux.integrable_modeProd_pair`. -/
lemma integrable_conj_modeProd_mul {m n : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (α β : Fin m →₀ ℕ) :
    Integrable (fun x : Xn n => (starRingEnd ℂ) (modeProd e n α x) * modeProd e n β x) := by
  classical
  have hpt : (fun x : Xn n => (starRingEnd ℂ) (modeProd e n α x) * modeProd e n β x)
      = fun x : Xn n => ∑ σ : Fin n → Fin m, ∑ τ : Fin n → Fin m,
          ((if modeMult σ = α then (1 : ℂ) else 0) * (if modeMult τ = β then 1 else 0))
            * ∏ i : Fin n, ((starRingEnd ℂ) (e (σ i) (x i)) * e (τ i) (x i)) := by
    funext x
    exact modeAux.conj_modeProd_mul (e := e) α β x
  rw [hpt]
  exact integrable_finsetSum _ (fun σ _ => integrable_finsetSum _ (fun τ _ =>
    (modeAux.integrable_modeProd_pair (e := e) (n := n) hbdd hsupp σ τ).const_mul _))

/-! ## 3. The expansion of the realisation on the support -/

/-- On the degree-`d` part, `boxRealise e d Ψ = Σ_α Ψ_α (α!/√(d!)) M_α`. -/
lemma boxRealise_eq_sum {m d : ℕ} {e : Fin m → Sp → ℂ} (Ψ : Work.BoseB4.RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d) :
    boxRealise e d Ψ
      = fun x : Xn d => ∑ α ∈ Ψ.support,
          ((Ψ α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)) : ℝ) : ℂ)
            * modeProd e d α x := by
  funext x
  rw [boxRealise, Finsupp.lsum_apply, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [if_pos (hΨ α hα)]
  simp only [LinearMap.toSpanSingleton_apply, Pi.smul_apply, Complex.real_smul, smul_smul]
  push_cast
  ring

/-! ## 4. The pairing of two finite sums of mode products -/

/-- `cIPn` of two finite sums of mode products with real coefficients. -/
lemma cIPn_sum_sum {m n : ℕ} (s t : Finset (Fin m →₀ ℕ)) (a b : (Fin m →₀ ℕ) → ℝ)
    (F G : (Fin m →₀ ℕ) → Xn n → ℂ)
    (h : ∀ α ∈ s, ∀ β ∈ t, Integrable (fun x : Xn n => (starRingEnd ℂ) (F α x) * G β x)) :
    cIPn n (fun x => ∑ α ∈ s, (a α : ℂ) * F α x) (fun x => ∑ β ∈ t, (b β : ℂ) * G β x)
      = ∑ α ∈ s, ∑ β ∈ t, (a α : ℂ) * (b β : ℂ) * cIPn n (F α) (G β) := by
  rw [cIPn]
  have hpt : (fun x : Xn n => (starRingEnd ℂ) (∑ α ∈ s, (a α : ℂ) * F α x)
        * (∑ β ∈ t, (b β : ℂ) * G β x))
      = fun x : Xn n => ∑ α ∈ s, ∑ β ∈ t,
          ((a α : ℂ) * (b β : ℂ)) * ((starRingEnd ℂ) (F α x) * G β x) := by
    funext x
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    ring
  rw [hpt]
  rw [integral_finsetSum _ (fun α hα => integrable_finsetSum _
      (fun β hβ => (h α hα β hβ).const_mul ((a α : ℂ) * (b β : ℂ))))]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [integral_finsetSum _ (fun β hβ => (h α hα β hβ).const_mul ((a α : ℂ) * (b β : ℂ)))]
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [integral_const_mul]
  rfl

/-! ## 5. The main theorem -/

theorem boxRealise_cIPn {m d : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (he : ∀ l l', (∫ x : Work.BoseDict.Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (Ψ Ψ' : Work.BoseB4.RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d)
    (hΨ' : ∀ α ∈ Ψ'.support, α.sum (fun _ k => k) = d) :
    Work.BoseDict.cIPn d (Work.BoseDict.boxRealise e d Ψ) (Work.BoseDict.boxRealise e d Ψ')
      = ((Work.BoseB4.bomb m Ψ Ψ' : ℝ) : ℂ) := by
  classical
  have hA := boxRealise_eq_sum (e := e) (d := d) Ψ hΨ
  have hB := boxRealise_eq_sum (e := e) (d := d) Ψ' hΨ'
  have hmain : cIPn d (boxRealise e d Ψ) (boxRealise e d Ψ')
      = ∑ α ∈ Ψ.support, ∑ β ∈ Ψ'.support,
          (((Ψ α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)) : ℝ) : ℂ)
            * ((Ψ' β * (Work.BoseB4.mfac β / Real.sqrt (d.factorial : ℝ)) : ℝ) : ℂ))
            * cIPn d (modeProd e d α) (modeProd e d β) := by
    rw [hA, hB]
    exact cIPn_sum_sum Ψ.support Ψ'.support
      (fun α => Ψ α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)))
      (fun β => Ψ' β * (Work.BoseB4.mfac β / Real.sqrt (d.factorial : ℝ)))
      (fun α => modeProd e d α) (fun β => modeProd e d β)
      (fun α _ β _ => integrable_conj_modeProd_mul hbdd hsupp α β)
  rw [hmain]
  have hinner : ∀ α ∈ Ψ.support,
      (∑ β ∈ Ψ'.support,
          (((Ψ α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)) : ℝ) : ℂ)
            * ((Ψ' β * (Work.BoseB4.mfac β / Real.sqrt (d.factorial : ℝ)) : ℝ) : ℂ))
            * cIPn d (modeProd e d α) (modeProd e d β))
        = ((Work.BoseB4.mfac α * Ψ α * Ψ' α : ℝ) : ℂ) := by
    intro α hα
    rw [Finset.sum_congr rfl (fun β hβ => by
      rw [modeProd_cIPn he hbdd hsupp (hΨ α hα) (hΨ' β hβ)])]
    have hs : Real.sqrt (d.factorial : ℝ) * Real.sqrt (d.factorial : ℝ) = (d.factorial : ℝ) := by
      rw [← sq, Real.sq_sqrt (by positivity)]
    have hD : (d.factorial : ℝ) ≠ 0 := ne_of_gt (by positivity)
    have hmf : Work.BoseB4.mfac α ≠ 0 := ne_of_gt (Work.BoseB4.BombSelf.mfac_pos α)
    have harith := coeff_arith2 (mf := Work.BoseB4.mfac α) (D := (d.factorial : ℝ))
      (s := Real.sqrt (d.factorial : ℝ)) (ψ := Ψ α) (ψ' := Ψ' α) hs hD hmf
    by_cases hmem : α ∈ Ψ'.support
    · rw [Finset.sum_eq_single α]
      · rw [if_pos rfl]
        have hcast : ((Ψ α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)) : ℝ) : ℂ)
              * ((Ψ' α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)) : ℝ) : ℂ)
              * (((d.factorial : ℝ) : ℂ) / ((Work.BoseB4.mfac α : ℝ) : ℂ))
            = (((Ψ α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)))
                * (Ψ' α * (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ)))
                * ((d.factorial : ℝ) / Work.BoseB4.mfac α) : ℝ) : ℂ) := by
          push_cast
          ring
        rw [hcast, harith]
      · intro β hβ hne
        rw [if_neg (fun h : α = β => hne h.symm)]
        ring
      · intro hnot
        exact absurd hmem hnot
    · rw [Finset.sum_eq_zero]
      · rw [Finsupp.notMem_support_iff.mp hmem]
        simp
      · intro β hβ
        rw [if_neg (fun h : α = β => hmem (h ▸ hβ))]
        ring
  rw [Finset.sum_congr rfl hinner]
  rw [Work.BoseB4.bomb_apply, Finsupp.sum]
  exact (Complex.ofReal_sum (s := Ψ.support)
    (f := fun a => Work.BoseB4.mfac a * Ψ a * Ψ' a)).symm

end Work.BoseDict
