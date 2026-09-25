import Mathlib
import Submission.Work.NN.Core.DbarCnPertAux
import Submission.Work.NN.Core.dbarCn_dirDeriv_comm
import Submission.Work.NN.Core.holderNorm_fderiv_le_dir
import Submission.Work.NN.Core.holderNorm_ne_top_of_contDiff
import Submission.Work.NN.Core.holderNorm_fderiv_apply_le
import Submission.Work.NN.Core.contDiffOn_dbarCn_coeff
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le
import Submission.Work.CR.Flat.Holder.holderNorm_sum_le
import Submission.Work.CR.Flat.Holder.holderNorm_neg

namespace Work.NN.Core

open scoped NNReal ENNReal ContDiff
open Set

/-- The `j`-th component of the vector field `z ↦ d_z(y ↦ A y e_l)(b)` is smooth. -/
private lemma contDiff_fderiv_A_apply {n : ℕ} {A : Cn n → Cn n →L[ℝ] Cn n}
    (hA : ∀ q : ℕ, ContDiff ℝ q A) (l j : Fin n) (b : Cn n) (k : ℕ) :
    ContDiff ℝ k (fun z => fderiv ℝ (fun y => A y (Pi.single l (1:ℂ)) j) z b) := by
  have h1 : ContDiff ℝ (k+1) (fun y => A y (Pi.single l (1:ℂ))) :=
    (hA (k+1)).clm_apply contDiff_const
  have h2 : ContDiff ℝ (k+1) (fun y => (A y (Pi.single l (1:ℂ))) j) := by
    have h := (contDiff_const (c := (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ))).clm_apply h1
    simpa only [ContinuousLinearMap.proj_apply] using h
  have h3 : ContDiff ℝ k (fderiv ℝ (fun y => (A y (Pi.single l (1:ℂ))) j)) :=
    h2.fderiv_right (m := k) le_rfl
  exact h3.clm_apply contDiff_const

/-- The `C^{k,α}` norm of a smooth function on a polydisc is finite. -/
private lemma holderNorm_lt_top_of_contDiff {n k : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} {f : Cn n → ℂ} (hf : ContDiff ℝ (k+1) f) :
    Work.CR.Flat.holderNorm k α f (Work.CR.Flat.polydisc 0 ρ) < ⊤ :=
  lt_top_iff_ne_top.mpr (holderNorm_ne_top_of_contDiff hα0 hα1.le hf)

/-- Coercion bookkeeping: `↑(k+1) = ↑k + 1` in `WithTop ℕ∞`. -/
private lemma withTop_cast_add_one (k : ℕ) :
    (((k+1 : ℕ)) : WithTop ℕ∞) = ((k : ℕ) : WithTop ℕ∞) + 1 := by
  push_cast; ring

theorem dbarCn_dirDeriv_data_finite {n m : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ' : Fin n → ℝ}
    {A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)} (hA : ∀ q : ℕ, ContDiff ℝ q A)
    {W : (Fin n → ℂ) → ℂ} (hW : ContDiff ℝ (m + 2) W)
    (hdata : ∀ l : Fin n, Work.CR.Flat.holderNorm (m+1) α
        (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) W z (Pi.single l 1))
        (Work.CR.Flat.polydisc 0 ρ') < ⊤)
    (hWfin : Work.CR.Flat.holderNorm (m+1) α W (Work.CR.Flat.polydisc 0 ρ') < ⊤)
    (b : (Fin n → ℂ)) (l : Fin n) :
    Work.CR.Flat.holderNorm m α
      (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) (fun y => fderiv ℝ W y b) z
        (Pi.single l 1)) (Work.CR.Flat.polydisc 0 ρ') < ⊤ := by
  classical
  -- ## notation
  set Ω : Set (Cn n) := Work.CR.Flat.polydisc 0 ρ' with hΩdef
  have hΩopen : IsOpen Ω := by rw [hΩdef]; exact Work.CR.Flat.isOpen_polydisc 0 ρ'
  have hΩu : UniqueDiffOn ℝ Ω := hΩopen.uniqueDiffOn
  -- ## regularity of `W`
  have hWcd : ContDiffOn ℝ (((m+2 : ℕ)) : WithTop ℕ∞) W Ω :=
    (hW.contDiffOn).mono (subset_univ Ω)
  have hWm1 : ContDiffOn ℝ (((m+1 : ℕ)) : WithTop ℕ∞) W Ω :=
    hWcd.of_le (by exact_mod_cast (by omega : m+1 ≤ m+2))
  have hu2 : ContDiffOn ℝ (2 : WithTop ℕ∞) W Ω :=
    hWcd.of_le (by exact_mod_cast (by omega : 2 ≤ m+2))
  have hWfinΩ : Work.CR.Flat.holderNorm (m+1) α W Ω < ⊤ := by
    rw [hΩdef]; exact hWfin
  -- ## the datum `Φ z = ∂̄_{Jstd+A} W z (e_l)` and its regularity
  set Φ : Cn n → ℂ := fun z => dbarCn (JstdCn n + A) W z (Pi.single l 1) with hΦdef
  have hΦcd : ContDiffOn ℝ (((m+1 : ℕ)) : WithTop ℕ∞) Φ Ω := by
    rw [hΦdef]
    exact contDiffOn_dbarCn_coeff hΩopen (m+1) (hA (m+2)) (u := W) hWcd l
  -- ## the two pieces of the commutator identity
  set ψ : Cn n → Cn n :=
    fun z => fun j => fderiv ℝ (fun y => A y (Pi.single l (1:ℂ)) j) z b with hψdef
  set F : Cn n → ℂ := fun z => fderiv ℝ Φ z b with hFdef
  set G : Cn n → ℂ := fun z => fderiv ℝ W z (ψ z) with hGdef
  -- ## the pointwise commutator identity on `Ω`
  have hcongr : ∀ z ∈ Ω,
      dbarCn (JstdCn n + A) (fun y => fderiv ℝ W y b) z (Pi.single l 1)
        = F z - (Complex.I / 2) * G z := by
    intro z hz
    have hz' : z ∈ Work.CR.Flat.polydisc 0 ρ' := hΩdef ▸ hz
    have h := dbarCn_dirDeriv_comm hΩopen hu2 (hA 1) b l hz'
    rw [hFdef, hGdef, hψdef, hΦdef]
    exact h
  -- ## regularity of the pieces
  have hFcd : ContDiffOn ℝ (((m : ℕ)) : WithTop ℕ∞) F Ω := by
    rw [hFdef]
    have h1 : ContDiffOn ℝ (((m : ℕ)) : WithTop ℕ∞) (fderiv ℝ Φ) Ω :=
      hΦcd.fderiv_of_isOpen hΩopen (by rw [← withTop_cast_add_one m])
    exact h1.clm_apply contDiffOn_const
  have hψcd : ∀ j : Fin n, ContDiffOn ℝ (((m : ℕ)) : WithTop ℕ∞) (fun z => ψ z j) Ω := by
    intro j
    rw [hψdef]
    exact (contDiff_fderiv_A_apply hA l j b m).contDiffOn.mono (subset_univ Ω)
  have hψfin : ∀ j : Fin n, Work.CR.Flat.holderNorm m α (fun z => ψ z j) Ω < ⊤ := by
    intro j
    rw [hψdef, hΩdef]
    exact holderNorm_lt_top_of_contDiff hα0 hα1 (contDiff_fderiv_A_apply hA l j b (m+1))
  have hGcd : ContDiffOn ℝ (((m : ℕ)) : WithTop ℕ∞) G Ω := by
    rw [hGdef]
    have h1 : ContDiffOn ℝ (((m+1 : ℕ)) : WithTop ℕ∞) (fderiv ℝ W) Ω :=
      hWcd.fderiv_of_isOpen hΩopen (by rw [← withTop_cast_add_one (m+1)])
    have h1' : ContDiffOn ℝ (((m : ℕ)) : WithTop ℕ∞) (fderiv ℝ W) Ω :=
      h1.of_le (by exact_mod_cast (by omega : m ≤ m+1))
    exact h1'.clm_apply (contDiffOn_pi.mpr hψcd)
  -- ## finiteness of the first piece
  have hFbound : Work.CR.Flat.holderNorm m α F Ω
      ≤ ENNReal.ofReal ‖b‖ * Work.CR.Flat.holderNorm (m+1) α Φ Ω := by
    rw [hFdef]
    exact holderNorm_fderiv_le_dir hΩopen m hΦcd b
  have hFfin : Work.CR.Flat.holderNorm m α F Ω < ⊤ :=
    lt_of_le_of_lt hFbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by
      simpa only [hΦdef] using hdata l))
  -- ## finiteness of the second piece
  set ε : ℝ := ∑ j : Fin n, (Work.CR.Flat.holderNorm m α (fun z => ψ z j) Ω).toReal with hεdef
  have hε0 : 0 ≤ ε := by
    rw [hεdef]; exact Finset.sum_nonneg fun j _ => ENNReal.toReal_nonneg
  have hψb : ∀ j : Fin n, Work.CR.Flat.holderNorm m α (fun z => ψ z j) Ω ≤ ENNReal.ofReal ε := by
    intro j
    have h1 : (Work.CR.Flat.holderNorm m α (fun z => ψ z j) Ω).toReal ≤ ε := by
      rw [hεdef]
      exact Finset.single_le_sum
        (f := fun i : Fin n => (Work.CR.Flat.holderNorm m α (fun z => ψ z i) Ω).toReal)
        (fun i _ => ENNReal.toReal_nonneg) (Finset.mem_univ j)
    calc Work.CR.Flat.holderNorm m α (fun z => ψ z j) Ω
        = ENNReal.ofReal (Work.CR.Flat.holderNorm m α (fun z => ψ z j) Ω).toReal :=
          (ENNReal.ofReal_toReal (ne_of_lt (hψfin j))).symm
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal h1
  obtain ⟨C, hCpos, hC⟩ :=
    holderNorm_fderiv_apply_le (n := n) (α := α) hα0 (Ω := Ω) (hΩ := hΩopen)
      (k := m+1) (by omega)
  have hψcd' : ∀ j : Fin n, ContDiffOn ℝ ((((m+1) - 1 : ℕ)) : WithTop ℕ∞)
      (fun z => ψ z j) Ω := by
    intro j
    rw [show ((m+1) - 1 : ℕ) = m from by omega]
    exact hψcd j
  have hGbound : Work.CR.Flat.holderNorm m α G Ω
      ≤ ENNReal.ofReal C * (ENNReal.ofReal ε * Work.CR.Flat.holderNorm (m+1) α W Ω) := by
    rw [hGdef]
    exact hC (u := W) hWm1 (W := ψ) hψcd' hε0 hψb
  have hGfin : Work.CR.Flat.holderNorm m α G Ω < ⊤ :=
    lt_of_le_of_lt hGbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hWfinΩ))
  -- ## assembly
  have hGsmcd : ContDiffOn ℝ (((m : ℕ)) : WithTop ℕ∞) ((Complex.I / 2 : ℂ) • G) Ω :=
    hGcd.const_smul (Complex.I / 2 : ℂ)
  have hGnegcd : ContDiffOn ℝ (((m : ℕ)) : WithTop ℕ∞) (-((Complex.I / 2 : ℂ) • G)) Ω :=
    hGsmcd.neg
  have hsub : (fun z : Cn n => F z - (Complex.I / 2) * G z)
      = F + (-((Complex.I / 2 : ℂ) • G)) := by
    funext z
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg]
  rw [holderNorm_congr_eqOn hcongr, hsub]
  have hsplit : Work.CR.Flat.holderNorm m α (F + (-((Complex.I / 2 : ℂ) • G))) Ω
      ≤ Work.CR.Flat.holderNorm m α F Ω
        + ENNReal.ofReal ‖(Complex.I / 2 : ℂ)‖ * Work.CR.Flat.holderNorm m α G Ω := by
    calc Work.CR.Flat.holderNorm m α (F + (-((Complex.I / 2 : ℂ) • G))) Ω
        ≤ Work.CR.Flat.holderNorm m α F Ω
            + Work.CR.Flat.holderNorm m α (-((Complex.I / 2 : ℂ) • G)) Ω :=
          Work.CR.Flat.Holder.holderNorm_add_le hFcd hGnegcd hΩu
      _ = Work.CR.Flat.holderNorm m α F Ω
            + Work.CR.Flat.holderNorm m α ((Complex.I / 2 : ℂ) • G) Ω := by
          rw [Work.CR.Flat.Holder.holderNorm_neg hGsmcd hΩu]
      _ = Work.CR.Flat.holderNorm m α F Ω
            + ENNReal.ofReal ‖(Complex.I / 2 : ℂ)‖ * Work.CR.Flat.holderNorm m α G Ω := by
          rw [Work.CR.Flat.Holder.holderNorm_smul (Complex.I / 2) hGcd hΩu]
  refine lt_of_le_of_lt hsplit ?_
  rw [ENNReal.add_lt_top]
  exact ⟨hFfin, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hGfin⟩

end Work.NN.Core
