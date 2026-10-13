import Mathlib
import Submission.Work.WilE4.CAD.gcd_spec_natDegree_const_on_C
import Submission.Work.WilE4.CAD.gcd_spec_psc
import Submission.Work.WilE4.CAD.rootMultiplicity_gcd
import Submission.Work.WilE4.CAD.signConst_data
import Submission.Work.WilE4.CAD.gcd_eval_tendsto_of_deg_const
import Submission.Work.WilE4.CAD.exists_sign_eq_of_simple_root

set_option linter.unusedVariables false

namespace Work.WilE4.CAD

theorem gcd_root_along_sequence {m k : ℕ} (P : Fin k → MvPolynomial (Fin (m + 1)) ℝ) (D : ℕ)
    (hD : ∀ i : Fin k, (P i).degreeOf (Fin.last m) ≤ D)
    (C : Set (Fin m → ℝ))
    (hcoeff : ∀ i : Fin k, ∀ j : ℕ, j ≤ D → ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((Work.WilE4.spec (P i) x).coeff j)
        = SignType.sign ((Work.WilE4.spec (P i) x').coeff j))
    (hmin : PscSignConst P C)
    {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ C) (u : ℕ → Fin m → ℝ) (huC : ∀ n, u n ∈ C)
    (hulim : Filter.Tendsto u Filter.atTop (nhds x₀))
    {i₀ j : Fin k} {t₀ ρ : ℝ} (hρ : 0 < ρ)
    (hi₀ne : Work.WilE4.spec (P i₀) x₀ ≠ 0) (hjne : Work.WilE4.spec (P j) x₀ ≠ 0)
    (hi₀eval : (Work.WilE4.spec (P i₀) x₀).eval t₀ = 0)
    (hjeval : (Work.WilE4.spec (P j) x₀).eval t₀ = 0)
    (hi₀mult : (Work.WilE4.spec (P i₀) x₀).rootMultiplicity t₀ = 1)
    (huniq : ∀ t : ℝ, |t - t₀| ≤ ρ → (Work.WilE4.spec (P i₀) x₀).IsRoot t → t = t₀) :
    ∀ᶠ n in Filter.atTop, ∃ t ∈ Set.Ioo (t₀ - ρ) (t₀ + ρ),
      (gcd (Work.WilE4.spec (P i₀) (u n)) (Work.WilE4.spec (P j) (u n))).IsRoot t := by
  -- the sign-constancy hypothesis in the packaged form used by `signConst_data`
  have hcc : CoeffConst P C :=
    fun i jj hj x hx x' hx' => hcoeff i jj (le_trans hj (hD i)) x hx x' hx'
  -- the specialisations are non-zero on `C` (their leading coefficient has constant sign there)
  have hFne : ∀ x ∈ C, spec (P i₀) x ≠ 0 := by
    intro x hx h0
    have hle : (spec (P i₀) x₀).natDegree ≤ (P i₀).degreeOf (Fin.last m) :=
      natDegree_spec_le (P i₀) x₀
    have hcoef0 : (spec (P i₀) x₀).coeff ((spec (P i₀) x₀).natDegree) ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hi₀ne
    have hz : (spec (P i₀) x).coeff ((spec (P i₀) x₀).natDegree) = 0 := by
      rw [h0]; simp
    exact hcoef0 ((coeff_spec_eq_zero_iff hcc hle hx₀ hx).mpr hz)
  have hGne : ∀ x ∈ C, spec (P j) x ≠ 0 := by
    intro x hx h0
    have hle : (spec (P j) x₀).natDegree ≤ (P j).degreeOf (Fin.last m) :=
      natDegree_spec_le (P j) x₀
    have hcoef0 : (spec (P j) x₀).coeff ((spec (P j) x₀).natDegree) ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hjne
    have hz : (spec (P j) x).coeff ((spec (P j) x₀).natDegree) = 0 := by
      rw [h0]; simp
    exact hcoef0 ((coeff_spec_eq_zero_iff hcc hle hx₀ hx).mpr hz)
  -- degree data on `C`
  have hFdeg : ∀ x ∈ C, (spec (P i₀) x).natDegree = (spec (P i₀) x₀).natDegree :=
    fun x hx => natDegree_spec_const hcc hx hx₀
  have hGdeg : ∀ x ∈ C, (spec (P j) x).natDegree = (spec (P j) x₀).natDegree :=
    fun x hx => natDegree_spec_const hcc hx hx₀
  have hgcddeg : ∀ x ∈ C, (gcd (spec (P i₀) x) (spec (P j) x)).natDegree
      = (gcd (spec (P i₀) x₀) (spec (P j) x₀)).natDegree :=
    fun x hx => gcd_spec_natDegree_const_on_C_psc P D hD C hcoeff hmin i₀ j x x₀ hx hx₀
  -- `t₀` is a *simple* root of the gcd at `x₀`
  have hgcd_ne : gcd (spec (P i₀) x₀) (spec (P j) x₀) ≠ 0 := by
    intro hzero
    obtain ⟨c, hc⟩ := gcd_dvd_left (spec (P i₀) x₀) (spec (P j) x₀)
    rw [hzero, zero_mul] at hc
    exact hi₀ne hc
  have hGroot : (spec (P j) x₀).IsRoot t₀ := hjeval
  have hGmult : 1 ≤ (spec (P j) x₀).rootMultiplicity t₀ := by
    have hpos : 0 < (spec (P j) x₀).rootMultiplicity t₀ :=
      (Polynomial.rootMultiplicity_pos hjne).mpr hGroot
    omega
  have hmult : (gcd (spec (P i₀) x₀) (spec (P j) x₀)).rootMultiplicity t₀ = 1 := by
    rw [rootMultiplicity_gcd (spec (P i₀) x₀) (spec (P j) x₀) hi₀ne hjne t₀, hi₀mult]
    exact min_eq_left hGmult
  have hroot₀ : (gcd (spec (P i₀) x₀) (spec (P j) x₀)).IsRoot t₀ :=
    (Polynomial.rootMultiplicity_pos hgcd_ne).mp (by rw [hmult]; exact Nat.zero_lt_one)
  have hderiv : (gcd (spec (P i₀) x₀) (spec (P j) x₀)).derivative.eval t₀ ≠ 0 := by
    intro h0
    have h1 : 1 < (gcd (spec (P i₀) x₀) (spec (P j) x₀)).rootMultiplicity t₀ :=
      (Polynomial.one_lt_rootMultiplicity_iff_isRoot hgcd_ne).mpr
        ⟨hroot₀, Polynomial.IsRoot.def.mpr h0⟩
    rw [hmult] at h1
    exact absurd h1 (lt_irrefl 1)
  -- two points inside the isolating interval at which the gcd takes values of opposite sign
  obtain ⟨z₁, hz₁, hs₁⟩ :=
    exists_sign_eq_of_simple_root hroot₀ hderiv SignType.pos (by decide) hρ
  obtain ⟨z₂, hz₂, hs₂⟩ :=
    exists_sign_eq_of_simple_root hroot₀ hderiv SignType.neg (by decide) hρ
  have hz₁I : z₁ ∈ Set.Ioo (t₀ - ρ) (t₀ + ρ) := by
    have h := abs_lt.mp hz₁
    exact Set.mem_Ioo.mpr ⟨by linarith [h.2], by linarith [h.1]⟩
  have hz₂I : z₂ ∈ Set.Ioo (t₀ - ρ) (t₀ + ρ) := by
    have h := abs_lt.mp hz₂
    exact Set.mem_Ioo.mpr ⟨by linarith [h.2], by linarith [h.1]⟩
  -- the values of the gcds at these two points converge
  have heval₁ : Filter.Tendsto
      (fun n => (gcd (spec (P i₀) (u n)) (spec (P j) (u n))).eval z₁) Filter.atTop
      (nhds ((gcd (spec (P i₀) x₀) (spec (P j) x₀)).eval z₁)) :=
    gcd_eval_tendsto_of_deg_const (f := fun x => spec (P i₀) x) (g := fun x => spec (P j) x)
      hx₀ u huC hulim (fun kk => continuous_spec_coeff (P i₀) kk)
      (fun kk => continuous_spec_coeff (P j) kk) hFne hGne hFdeg hGdeg hgcddeg z₁
  have heval₂ : Filter.Tendsto
      (fun n => (gcd (spec (P i₀) (u n)) (spec (P j) (u n))).eval z₂) Filter.atTop
      (nhds ((gcd (spec (P i₀) x₀) (spec (P j) x₀)).eval z₂)) :=
    gcd_eval_tendsto_of_deg_const (f := fun x => spec (P i₀) x) (g := fun x => spec (P j) x)
      hx₀ u huC hulim (fun kk => continuous_spec_coeff (P i₀) kk)
      (fun kk => continuous_spec_coeff (P j) kk) hFne hGne hFdeg hGdeg hgcddeg z₂
  have hpos₁ : 0 < (gcd (spec (P i₀) x₀) (spec (P j) x₀)).eval z₁ := sign_eq_one_iff.mp hs₁
  have hneg₂ : (gcd (spec (P i₀) x₀) (spec (P j) x₀)).eval z₂ < 0 := sign_eq_neg_one_iff.mp hs₂
  have hev₁ : ∀ᶠ n in Filter.atTop,
      0 < (gcd (spec (P i₀) (u n)) (spec (P j) (u n))).eval z₁ :=
    heval₁.eventually (isOpen_Ioi.mem_nhds hpos₁)
  have hev₂ : ∀ᶠ n in Filter.atTop,
      (gcd (spec (P i₀) (u n)) (spec (P j) (u n))).eval z₂ < 0 :=
    heval₂.eventually (isOpen_Iio.mem_nhds hneg₂)
  -- the intermediate value theorem produces a root between `z₁` and `z₂`
  rcases le_total z₁ z₂ with hle | hle
  · filter_upwards [hev₁, hev₂] with n hn₁ hn₂
    obtain ⟨c, hc, hce⟩ := (intermediate_value_Icc' hle (Polynomial.continuous _).continuousOn)
      (show (0 : ℝ) ∈ Set.Icc ((gcd (spec (P i₀) (u n)) (spec (P j) (u n))).eval z₂)
          ((gcd (spec (P i₀) (u n)) (spec (P j) (u n))).eval z₁) from
        ⟨le_of_lt hn₂, le_of_lt hn₁⟩)
    exact ⟨c, ⟨lt_of_lt_of_le hz₁I.1 hc.1, lt_of_le_of_lt hc.2 hz₂I.2⟩,
      Polynomial.IsRoot.def.mpr hce⟩
  · filter_upwards [hev₁, hev₂] with n hn₁ hn₂
    obtain ⟨c, hc, hce⟩ := (intermediate_value_Icc hle (Polynomial.continuous _).continuousOn)
      (show (0 : ℝ) ∈ Set.Icc ((gcd (spec (P i₀) (u n)) (spec (P j) (u n))).eval z₂)
          ((gcd (spec (P i₀) (u n)) (spec (P j) (u n))).eval z₁) from
        ⟨le_of_lt hn₂, le_of_lt hn₁⟩)
    exact ⟨c, ⟨lt_of_lt_of_le hz₂I.1 hc.1, lt_of_le_of_lt hc.2 hz₁I.2⟩,
      Polynomial.IsRoot.def.mpr hce⟩

end Work.WilE4.CAD
