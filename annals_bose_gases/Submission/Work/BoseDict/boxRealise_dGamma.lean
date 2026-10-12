import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseDict.Defs3
import Submission.Work.BoseDict.boxCreOf_boxAnnOf_slot
import Submission.Work.BoseDict.boxRealise_ann
import Submission.Work.BoseDict.boxRealise_symm
import Submission.Work.BoseDict.mfac_sqrt_ratio
import Submission.Work.BoseDict.sum_cre_mode
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDict.boxRealise_dGamma` — second quantisation ↦ first quantisation
-/

namespace Work.BoseDict

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open MeasureTheory

private lemma single_eq_smul_single {m : ℕ} (α : Fin m →₀ ℕ) (c : ℝ) :
    (Finsupp.single α c : Work.BoseB4.RealFock m) = c • Finsupp.single α (1 : ℝ) := by
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

private lemma etaOf_evec {m : ℕ} (e : Fin m → Sp → ℂ) (l : Fin m) (z : Sp) :
    etaOf e (Work.BoseB4.evec m l) z = e l z := etaOf_pi_single e l z

private lemma boxRealise_cre_aux {m d : ℕ} {e : Fin m → Sp → ℂ} (l : Fin m)
    (Ψ : Work.BoseB4.RealFock m) :
    boxRealise e (d + 1) (Work.BoseB4.cre m l Ψ)
      = boxCreOf e (Work.BoseB4.evec m l) d (boxRealise e d Ψ) := by
  classical
  induction Ψ using Finsupp.induction_linear with
  | zero =>
      rw [map_zero, map_zero, map_zero]
      exact (boxCreOf_zero e (Work.BoseB4.evec m l) d).symm
  | add f g hf hg =>
      have h1 : boxRealise e (d + 1) (Work.BoseB4.cre m l (f + g))
          = boxRealise e (d + 1) (Work.BoseB4.cre m l f)
            + boxRealise e (d + 1) (Work.BoseB4.cre m l g) := by
        rw [map_add, map_add]
      have h2 : boxRealise e d (f + g)
          = boxRealise e d f + boxRealise e d g := map_add _ _ _
      rw [h1, h2, boxCreOf_add, hf, hg]
  | single α c =>
      have hshift : boxRealise e (d + 1) (Work.BoseB4.cre m l (Finsupp.single α c))
          = c • (boxRealise e (d + 1)
              (Finsupp.single (α + Work.BoseB4.e m l) (1 : ℝ))) := by
        rw [Work.BoseB4.cre_single]
        rw [single_eq_smul_single, map_smul]
      have hbase : boxRealise e d (Finsupp.single α c)
          = c • (boxRealise e d (Finsupp.single α (1 : ℝ))) := by
        rw [single_eq_smul_single, map_smul]
      rw [hshift, hbase]
      by_cases hα : α.sum (fun _ k => k) = d
      · have hα' : (α + Work.BoseB4.e m l).sum (fun _ k => k) = d + 1 := by
          rw [sum_add_e, hα]
        rw [boxRealise_single, if_pos hα', boxRealise_single, if_pos hα]
        rw [boxCreOf_smul, boxCreOf_smul]
        have hslot : boxCreOf e (Work.BoseB4.evec m l) d (modeProd e d α)
            = ((((α l : ℝ) + 1) / Real.sqrt ((d : ℝ) + 1)) : ℝ)
                • modeProd e (d + 1) (α + Work.BoseB4.e m l) := by
          funext x
          have hsum := sum_cre_mode (e := e) l α hα x
          simp only [boxCreOf, Pi.smul_apply, Complex.real_smul]
          rw [Finset.sum_congr rfl (fun j _ => by rw [etaOf_evec]), hsum]
          push_cast
          rw [div_eq_mul_inv]
          ring_nf
        rw [hslot]
        have hcoef : (Work.BoseB4.mfac α / Real.sqrt ((d.factorial : ℕ) : ℝ))
              * (((α l : ℝ) + 1) / Real.sqrt ((d : ℝ) + 1))
            = Work.BoseB4.mfac (α + Work.BoseB4.e m l)
                / Real.sqrt (((d + 1).factorial : ℕ) : ℝ) := by
          rw [← mul_div_assoc, ← mfac_sqrt_ratio l α]
        have hc : (c * (Work.BoseB4.mfac α / Real.sqrt ((d.factorial : ℕ) : ℝ)))
              * (((α l : ℝ) + 1) / Real.sqrt ((d : ℝ) + 1))
            = c * (Work.BoseB4.mfac (α + Work.BoseB4.e m l)
                / Real.sqrt (((d + 1).factorial : ℕ) : ℝ)) := by
          rw [mul_assoc, hcoef]
        rw [smul_smul, smul_smul, smul_smul, hc]
      · have hα' : (α + Work.BoseB4.e m l).sum (fun _ k => k) ≠ d + 1 := by
          intro hc
          rw [sum_add_e] at hc
          omega
        rw [boxRealise_single, if_neg hα', boxRealise_single, if_neg hα]
        simp [boxCreOf_zero]

end

/-- A multi-index of total degree `0` vanishes. -/
private lemma sum_eq_zero_imp {m : ℕ} (α : Fin m →₀ ℕ) (h : α.sum (fun _ k => k) = 0) :
    α = 0 := by
  ext i
  rw [Finsupp.zero_apply]
  by_contra hi
  have hmem : i ∈ α.support := Finsupp.mem_support_iff.mpr hi
  have hsum : α.sum (fun _ k => k) = ∑ j ∈ α.support, α j := rfl
  have hle : α i ≤ α.sum (fun _ k => k) := by
    rw [hsum]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le _) hmem
  omega

/-- `boxAnnOf` of the coordinate vector `evec j` is the mode-wise `boxAnn`. -/
private lemma boxAnnOf_evec {m : ℕ} (e : Fin m → Sp → ℂ) (j : Fin m) (D : ℕ) :
    boxAnnOf e (Work.BoseB4.evec m j) D = boxAnn e j D := by
  funext Θ y
  have hfun : (fun z : Sp => (starRingEnd ℂ) (etaOf e (Work.BoseB4.evec m j) z) * Θ (Fin.cons z y))
      = fun z : Sp => (starRingEnd ℂ) (e j z) * Θ (Fin.cons z y) := by
    funext z
    rw [etaOf_evec]
  simp only [boxAnn, boxAnnOf, hfun]

/-- **The box ↔ model dictionary for the second quantisation.** -/
theorem boxRealise_dGamma {m d : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (he : ∀ l l', (∫ x : Work.BoseDict.Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Ψ : Work.BoseB4.RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d) :
    Work.BoseDict.boxRealise e d (Work.BoseB4.dGamma m T Ψ)
      = Work.BoseDict.boxSlotSum e T (Work.BoseDict.boxRealise e d Ψ) := by
  classical
  rcases d with _ | D
  · -- degree `0`: every basis vector in the support is the vacuum
    have hΨ0 : Ψ = Finsupp.single (0 : Fin m →₀ ℕ) (Ψ 0) := by
      ext γ
      by_cases hγ : γ = 0
      · subst hγ
        rw [Finsupp.single_eq_same]
      · have hnotmem : γ ∉ Ψ.support := fun hmem =>
          hγ (sum_eq_zero_imp γ (hΨ γ hmem))
        have hsingle : (Finsupp.single (0 : Fin m →₀ ℕ) (Ψ 0) : (Fin m →₀ ℕ) →₀ ℝ) γ = 0 :=
          Finsupp.single_eq_of_ne (b := Ψ 0) hγ
        rw [Finsupp.notMem_support_iff.mp hnotmem, hsingle]
    have hdG : Work.BoseB4.dGamma m T Ψ = 0 := by
      rw [hΨ0, Work.BoseB4.dGamma]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
      simp [Work.BoseB4.ann_single_basis]
    rw [hdG, map_zero]
    simp [boxSlotSum]
  · -- degree `D + 1`: the `a_i† a_j` entries
    have hterm : ∀ i j : Fin m,
        boxRealise e (D + 1) (Work.BoseB4.cre m i (Work.BoseB4.ann m j Ψ))
          = ∑ j' : Fin (D + 1),
              boxSlotOf e (Work.BoseB4.evec m i) (Work.BoseB4.evec m j) j'
                (boxRealise e (D + 1) Ψ) := by
      intro i j
      rw [boxRealise_cre_aux (d := D) i (Work.BoseB4.ann m j Ψ),
        boxRealise_ann he hbdd hsupp j Ψ hΨ, ← boxAnnOf_evec e j D]
      exact boxCreOf_boxAnnOf_slot (Work.BoseB4.evec m i) (Work.BoseB4.evec m j)
        (boxRealise e (D + 1) Ψ) (fun σ x => boxRealise_symm Ψ σ x)
    have hexp : Work.BoseB4.dGamma m T Ψ
        = ∑ i : Fin m, ∑ j : Fin m,
            (T (Work.BoseB4.evec m j) i) • (Work.BoseB4.cre m i) (Work.BoseB4.ann m j Ψ) := by
      rw [Work.BoseB4.dGamma]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    rw [hexp]
    simp only [map_sum, map_smul, hterm, Finset.smul_sum]
    unfold boxSlotSum
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm]

end Work.BoseDict
