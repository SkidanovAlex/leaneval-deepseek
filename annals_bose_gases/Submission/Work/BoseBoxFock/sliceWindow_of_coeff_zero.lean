import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.sliceFCRealise
import Submission.Work.BoseDict.boxRealise_cIPn
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open scoped BigOperators
open MeasureTheory

/-! ## Auxiliary lemmas

The two lemmas below extract the action of the pairing `cIPn d (M_β) (·)` on a
`boxRealiseC`-expanded vector: `cIPn` is `ℂ`-linear in its *second* argument, and the
orthonormality `modeProd_cIPn` collapses the expansion onto the `β`-th coefficient. -/

/-- `cIPn n F (·)` is `ℂ`-linear on a finite sum of `ℂ`-multiples of vectors. -/
lemma cIPn_sum_right {n : ℕ} {ι : Type*} (s : Finset ι) (F : Work.BoseDict.Xn n → ℂ)
    (G : ι → Work.BoseDict.Xn n → ℂ) (c : ι → ℂ)
    (h : ∀ i ∈ s, Integrable (fun x => (starRingEnd ℂ) (F x) * G i x)) :
    Work.BoseDict.cIPn n F (fun x => ∑ i ∈ s, c i * G i x)
      = ∑ i ∈ s, c i * Work.BoseDict.cIPn n F (G i) := by
  simp only [Work.BoseDict.cIPn]
  rw [show (fun x => (starRingEnd ℂ) (F x) * ∑ i ∈ s, c i * G i x)
        = (fun x => ∑ i ∈ s, c i * ((starRingEnd ℂ) (F x) * G i x)) from by
      funext x; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
  rw [integral_finsetSum _ (fun i hi => (h i hi).const_mul (c i))]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul (c i) _

/-- **The coefficient functional.**  The pairing of the mode product `M_β` against a
`boxRealiseC`-realised vector `Ψc` (whose support has degree `d`, and with `|β| = d`) is the
`β`-th coefficient of `Ψc` times `mfac β / √(d!) · d!/mfac β = √(d!) ≠ 0`. -/
lemma cIPn_boxRealiseC_eq {m d : ℕ} {ℓ : ℝ} (e : Fin m → Work.BoseDict.Sp → ℂ)
    (he : ∀ l l', (∫ x : Work.BoseDict.Sp, (starRingEnd ℂ) (e l x) * e l' x)
      = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (Ψc : CFock m) (hdeg : ∀ α ∈ Ψc.support, α.sum (fun _ k => k) = d)
    (β : Fin m →₀ ℕ) (hβ : β.sum (fun _ k => k) = d) :
    Work.BoseDict.cIPn d (Work.BoseDict.modeProd e d β) (boxRealiseC e d Ψc)
      = Ψc β * (((Work.BoseB4.mfac β / Real.sqrt (d.factorial : ℝ) : ℝ) : ℂ)
          * ((((d.factorial : ℝ) : ℂ) / ((Work.BoseB4.mfac β : ℝ) : ℂ)))) := by
  classical
  rw [boxRealiseC_eq_sum (e := e) Ψc hdeg]
  rw [cIPn_sum_right Ψc.support (fun x => Work.BoseDict.modeProd e d β x)
        (fun α => fun x => Work.BoseDict.modeProd e d α x)
        (fun α => Ψc α * ((Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ) : ℝ) : ℂ))
        (fun α _ => Work.BoseDict.integrable_conj_modeProd_mul hbdd hsupp β α)]
  have hinner : ∀ α ∈ Ψc.support,
      (Ψc α * ((Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ) : ℝ) : ℂ))
          * Work.BoseDict.cIPn d (Work.BoseDict.modeProd e d β) (Work.BoseDict.modeProd e d α)
        = (Ψc α * ((Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ) : ℝ) : ℂ))
          * (if β = α then ((((d.factorial : ℝ) : ℂ) / ((Work.BoseB4.mfac β : ℝ) : ℂ)))
              else 0) := by
    intro α hα
    rw [Work.BoseDict.modeProd_cIPn (n := d) he hbdd hsupp hβ (hdeg α hα)]
  rw [Finset.sum_congr rfl hinner]
  have hcollapse : (∑ α ∈ Ψc.support,
      (Ψc α * ((Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ) : ℝ) : ℂ))
          * (if β = α then ((((d.factorial : ℝ) : ℂ) / ((Work.BoseB4.mfac β : ℝ) : ℂ)))
              else 0))
      = Ψc β * (((Work.BoseB4.mfac β / Real.sqrt (d.factorial : ℝ) : ℝ) : ℂ)
          * ((((d.factorial : ℝ) : ℂ) / ((Work.BoseB4.mfac β : ℝ) : ℂ)))) := by
    by_cases hmem : β ∈ Ψc.support
    · rw [Finset.sum_eq_single β]
      · simp only [if_true]; ring
      · intro α _ hne
        rw [if_neg (fun h : β = α => hne h.symm), mul_zero]
      · intro hnot; exact absurd hmem hnot
    · rw [Finset.sum_eq_zero]
      · rw [Finsupp.notMem_support_iff.mp hmem]; simp
      · intro α hα
        rw [if_neg (fun h : β = α => hmem (h ▸ hα)), mul_zero]
  rw [hcollapse]

/-- **`ExcWindow`, the final bookkeeping of step 6.**  A `CFock` vector `Ψc` whose realisation on the box is `Θ`, whose support has total degree `d` (`hdeg`), and whose monomial expansion has *no "bad" coefficient* — `cIPn d (M_α) Θ = 0` whenever `d − α 0 > ⌊M⌋₊` (`hzer`) — has its support inside the excited window: every `α ∈ Ψc.support` satisfies `|α| − α 0 ≤ ⌊M⌋₊`.

This is the step that converts the a.e. coefficient statement `Work.BoseBoxFock.sliceBadCoeff_zero` into the `ExcWindow` support condition, via the orthonormality `modeProd_cIPn he hbdd hsupp` (`cIPn d (M_α) (M_β) = δ_{αβ}·d!/α! ≠ 0`) and the expansion `boxRealiseC_eq_sum`. -/
theorem sliceWindow_of_coeff_zero {m d : ℕ} [NeZero m] {ℓ M : ℝ}
    (e : Fin m → Work.BoseDict.Sp → ℂ)
    (he : ∀ l l', (∫ x : Work.BoseDict.Sp, (starRingEnd ℂ) (e l x) * e l' x)
      = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (Ψc : Work.BoseBoxFock.CFock m) (Θ : Work.BoseDict.Xn d → ℂ)
    (hΘ : boxRealiseC e d Ψc = Θ)
    (hdeg : ∀ α ∈ Ψc.support, α.sum (fun _ k => k) = d)
    (hzer : ∀ α : Fin m →₀ ℕ, α.sum (fun _ k => k) = d →
      ((d - α 0 : ℕ) : ℝ) > (⌊M⌋₊ : ℝ) →
      Work.BoseDict.cIPn d (Work.BoseDict.modeProd e d α) Θ = 0) :
    ∀ α ∈ Ψc.support, ((d - α 0 : ℕ) : ℝ) ≤ (⌊M⌋₊ : ℝ) := by
  classical
  intro α hα
  by_contra hbad
  have hgt : ((d - α 0 : ℕ) : ℝ) > (⌊M⌋₊ : ℝ) := not_le.mp hbad
  have hdα : α.sum (fun _ k => k) = d := hdeg α hα
  have hkey := cIPn_boxRealiseC_eq (ℓ := ℓ) e he hbdd hsupp Ψc hdeg α hdα
  have hz : Work.BoseDict.cIPn d (Work.BoseDict.modeProd e d α) (boxRealiseC e d Ψc) = 0 := by
    rw [hΘ]
    exact hzer α hdα hgt
  rw [hkey] at hz
  have hfpos : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  have hnum : ((d.factorial : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hfpos)
  have hmfpos := Work.BoseB4.BombSelf.mfac_pos α
  have hmfc : ((Work.BoseB4.mfac α : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hmfpos)
  have hcf : ((Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_ne_zero (ne_of_gt hmfpos)
      (ne_of_gt (Real.sqrt_pos.mpr hfpos)))
  have hc : (((Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ) : ℝ) : ℂ)
      * ((((d.factorial : ℝ) : ℂ) / ((Work.BoseB4.mfac α : ℝ) : ℂ)))) ≠ 0 :=
    mul_ne_zero hcf (div_ne_zero hnum hmfc)
  have hzα : Ψc α = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · exact absurd h hc
  exact (Finsupp.mem_support_iff.mp hα) hzα

end Work.BoseBoxFock
