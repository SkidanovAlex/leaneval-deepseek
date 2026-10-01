import Mathlib
import Submission.Work.LinnikAreas.A7.WBox

namespace Work.A7

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

open Work.LinnikContract

/-- `‖F₂(K, x)‖ = ((1 - e^{-Kx})/x)²` for a real argument `x`. -/
private lemma F2_ofReal_norm (K x : ℝ) :
    ‖Work.LinnikContract.F2 K ((x : ℂ))‖ = ((1 - Real.exp (-(K*x)))/x)^2 := by
  rw [show Work.LinnikContract.F2 K ((x : ℂ)) =
      ((((1 - Real.exp (-(K*x)))/x)^2 : ℝ) : ℂ) from by
    simp only [Work.LinnikContract.F2]
    rw [show -↑K * (x:ℂ) = ((-(K*x) : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_exp]
    simp only [Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_sub]]
  rw [show ‖((((1 - Real.exp (-(K*x)))/x)^2 : ℝ) : ℂ)‖ = |((1 - Real.exp (-(K*x)))/x)^2|
      from RCLike.norm_ofReal _, abs_of_nonneg (sq_nonneg _)]

/-- The `WBox` integrand is the `boxAbs` integrand weighted by `e^{-aλ(ρ)}`. -/
private lemma wfun_eq_exp_mul_bfun {q : ℕ} [NeZero q] (K R : ℝ)
    (χ : DirichletCharacter ℂ q) (ρ : ℂ) :
    Work.LinnikAreas.A7.wfun q K R χ ρ =
      Real.exp (-(Work.LinnikAreas.A7.ac * lamOf q ρ)) * bfun q K R χ ρ := by
  simp only [Work.LinnikAreas.A7.wfun, bfun]
  split_ifs <;> ring

/-- The `boxAbs` integrand is non-negative. -/
private lemma bfun_nonneg {q : ℕ} [NeZero q] (K R : ℝ)
    (χ : DirichletCharacter ℂ q) (ρ : ℂ) : 0 ≤ bfun q K R χ ρ := by
  simp only [bfun]; split_ifs with h <;> [positivity; exact le_refl 0]

/-- The `χ₁`-refinement: with `WBox = Σ'_ρ e^{-aλ(ρ)}·b(ρ)` where `b` is the `boxAbs` integrand,
the zero `ρs` (simple, of parameter `lam`) carries weight `e^{-a·lam}`, while every other box zero
has parameter `≥ c` and hence weight at most `e^{-a·c}`.  The only point needing a genuine input is
that the single term `b(ρs)` is at most `‖F₂(K, lam)‖ = ((1-e^{-K·lam})/lam)²`, i.e. that
`‖F₂(K, z)‖ ≤ ‖F₂(K, Re z)‖` (`Work.LinnikContract.API.F2_norm_le_re`) together with
`Re ((1-ρs)𝓛) = lamOf q ρs = lam`. -/
theorem WBox_refined {q : ℕ} [NeZero q] {R lam c η : ℝ} {χ : DirichletCharacter ℂ q} {ρs : ℂ}
    (hbox : Work.LinnikContract.InBox q R ρs) (hmult : Work.LinnikContract.zeroMult χ ρs = 1)
    (hlam : Work.LinnikContract.lamOf q ρs = lam) (hlam0 : 0 < lam) (hlamc : lam ≤ c)
    (hsecond : ∀ ρ : ℂ, Work.LinnikContract.InBox q R ρ → Work.LinnikContract.zeroMult χ ρ ≠ 0 → ρ ≠ ρs → c ≤ Work.LinnikContract.lamOf q ρ)
    (hcert : Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η)) :
    Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi lam - Work.LinnikAreas.A7.Aref c lam) + ((9:ℝ)/100) * Real.exp (-(Work.LinnikAreas.A7.ac * c)) * η := by
  have hK : (0:ℝ) < (3:ℝ)/10 := by norm_num
  -- The zero `ρs` contributes at most `F2r = ‖F₂(K, lam)‖`.
  have hbfun_rho :
      bfun q ((3:ℝ)/10) R χ ρs ≤ ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2 := by
    have hz : 0 < ((1 - ρs) * (Real.log q : ℂ)).re := by
      rw [Work.LinnikAreas.A7.re_one_sub_mul_log, hlam]; exact hlam0
    have h1 : bfun q ((3:ℝ)/10) R χ ρs =
        ‖Work.LinnikContract.F2 ((3:ℝ)/10) ((1 - ρs) * Real.log q)‖ := by
      simp only [bfun, hbox, if_true, hmult, Nat.cast_one, one_mul]
    rw [h1]
    calc ‖Work.LinnikContract.F2 ((3:ℝ)/10) ((1 - ρs) * Real.log q)‖
        ≤ ‖Work.LinnikContract.F2 ((3:ℝ)/10) ((((1 - ρs) * Real.log q).re : ℂ))‖ :=
          Work.LinnikContract.API.F2_norm_le_re _ hK _ hz
      _ = ‖Work.LinnikContract.F2 ((3:ℝ)/10) ((lam : ℂ))‖ := by
          rw [Work.LinnikAreas.A7.re_one_sub_mul_log, hlam]
      _ = ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2 := F2_ofReal_norm _ lam
  have hE12 : Real.exp (-(Work.LinnikAreas.A7.ac * c)) ≤
      Real.exp (-(Work.LinnikAreas.A7.ac * lam)) := by
    rw [Real.exp_le_exp]; nlinarith [Work.LinnikAreas.A7.ac_pos, hlamc]
  have hE2nn : 0 ≤ Real.exp (-(Work.LinnikAreas.A7.ac * c)) := Real.exp_nonneg _
  have hCnonneg : 0 ≤ (Real.exp (-(Work.LinnikAreas.A7.ac * lam)) -
        Real.exp (-(Work.LinnikAreas.A7.ac * c))) *
      (((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2) :=
    mul_nonneg (sub_nonneg.mpr hE12) (sq_nonneg _)
  -- Pointwise domination of the `WBox` integrand.
  have hpt : ∀ ρ : ℂ, Work.LinnikAreas.A7.wfun q ((3:ℝ)/10) R χ ρ ≤
      Real.exp (-(Work.LinnikAreas.A7.ac * c)) * bfun q ((3:ℝ)/10) R χ ρ
        + (if ρ = ρs then (Real.exp (-(Work.LinnikAreas.A7.ac * lam)) -
              Real.exp (-(Work.LinnikAreas.A7.ac * c))) *
            (((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2) else 0) := by
    intro ρ
    rw [wfun_eq_exp_mul_bfun]
    by_cases hρ : ρ = ρs
    · subst ρ
      rw [if_pos rfl, hlam]
      have := mul_nonneg (sub_nonneg.mpr hE12) (sub_nonneg.mpr hbfun_rho)
      nlinarith [this]
    · rw [if_neg hρ, add_zero]
      by_cases hb : bfun q ((3:ℝ)/10) R χ ρ = 0
      · rw [hb, mul_zero, mul_zero]
      · have hInB : Work.LinnikContract.InBox q R ρ := by
          by_contra h
          exact hb (by rw [bfun, if_neg h])
        have hmul : Work.LinnikContract.zeroMult χ ρ ≠ 0 := by
          intro hz
          exact hb (by simp [bfun, hInB, hz])
        have hc_le : c ≤ Work.LinnikContract.lamOf q ρ := hsecond ρ hInB hmul hρ
        have hE : Real.exp (-(Work.LinnikAreas.A7.ac * Work.LinnikContract.lamOf q ρ)) ≤
            Real.exp (-(Work.LinnikAreas.A7.ac * c)) := by
          rw [Real.exp_le_exp]; nlinarith [Work.LinnikAreas.A7.ac_pos, hc_le]
        have hb0 : 0 ≤ bfun q ((3:ℝ)/10) R χ ρ := bfun_nonneg _ _ _ _
        exact mul_le_mul_of_nonneg_right hE hb0
  -- Algebra: the target bound equals `e^{-ac}(B + η) + (e^{-a·lam} - e^{-ac})·F2r`.
  have hkey : ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi lam - Work.LinnikAreas.A7.Aref c lam) +
        ((9:ℝ)/100) * Real.exp (-(Work.LinnikAreas.A7.ac * c)) * η
      = Real.exp (-(Work.LinnikAreas.A7.ac * c)) *
          (((9:ℝ)/100) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η))
        + (Real.exp (-(Work.LinnikAreas.A7.ac * lam)) - Real.exp (-(Work.LinnikAreas.A7.ac * c))) *
            (((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2) := by
    rw [Work.LinnikAreas.A7.Phi, Work.LinnikAreas.A7.Aref]
    simp only [Work.LinnikAreas.A7.Kc, Work.LinnikAreas.A7.K2]
    field_simp
    ring
  have hsum_eq : ∀ S : Finset ℂ, (∑ ρ ∈ S,
        (Real.exp (-(Work.LinnikAreas.A7.ac*c)) * bfun q ((3:ℝ)/10) R χ ρ
          + (if ρ = ρs then (Real.exp (-(Work.LinnikAreas.A7.ac * lam)) -
                Real.exp (-(Work.LinnikAreas.A7.ac * c))) *
              (((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2) else 0)))
      = Real.exp (-(Work.LinnikAreas.A7.ac*c)) *
            (∑ ρ ∈ S, bfun q ((3:ℝ)/10) R χ ρ)
        + (if ρs ∈ S then (Real.exp (-(Work.LinnikAreas.A7.ac * lam)) -
              Real.exp (-(Work.LinnikAreas.A7.ac * c))) *
            (((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2) else 0) := by
    intro S
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq']
  by_cases hfin : Function.HasFiniteSupport (bfun q ((3:ℝ)/10) R χ)
  · set S := hfin.toFinset
    have hsubf : Function.support (bfun q ((3:ℝ)/10) R χ) ⊆ (S : Set ℂ) :=
      fun i hi => hfin.mem_toFinset.mpr hi
    have hsubw : Function.support (Work.LinnikAreas.A7.wfun q ((3:ℝ)/10) R χ) ⊆ (S : Set ℂ) := by
      rw [Work.LinnikAreas.A7.support_wfun_eq_bfun]; exact hsubf
    have hW : Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ =
        ∑ ρ ∈ S, Work.LinnikAreas.A7.wfun q ((3:ℝ)/10) R χ ρ := by
      rw [Work.LinnikAreas.A7.WBox_eq_finsum, finsum_eq_sum_of_support_subset _ hsubw]
    have hB : Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ =
        ∑ ρ ∈ S, bfun q ((3:ℝ)/10) R χ ρ := by
      rw [show Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ =
            ∑ᶠ ρ : ℂ, bfun q ((3:ℝ)/10) R χ ρ from rfl,
          finsum_eq_sum_of_support_subset _ hsubf]
    have hmain : Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ ≤
        Real.exp (-(Work.LinnikAreas.A7.ac*c)) * Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ
          + (Real.exp (-(Work.LinnikAreas.A7.ac*lam)) -
              Real.exp (-(Work.LinnikAreas.A7.ac*c))) *
              (((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2) := by
      rw [hW, hB]
      calc ∑ ρ ∈ S, Work.LinnikAreas.A7.wfun q ((3:ℝ)/10) R χ ρ
          ≤ ∑ ρ ∈ S, (Real.exp (-(Work.LinnikAreas.A7.ac*c)) * bfun q ((3:ℝ)/10) R χ ρ
              + (if ρ = ρs then (Real.exp (-(Work.LinnikAreas.A7.ac * lam)) -
                    Real.exp (-(Work.LinnikAreas.A7.ac * c))) *
                  (((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2) else 0)) :=
            Finset.sum_le_sum (fun ρ _ => hpt ρ)
        _ = Real.exp (-(Work.LinnikAreas.A7.ac*c)) *
                (∑ ρ ∈ S, bfun q ((3:ℝ)/10) R χ ρ)
              + (if ρs ∈ S then (Real.exp (-(Work.LinnikAreas.A7.ac * lam)) -
                    Real.exp (-(Work.LinnikAreas.A7.ac * c))) *
                  (((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2) else 0) := hsum_eq S
        _ ≤ Real.exp (-(Work.LinnikAreas.A7.ac*c)) *
                (∑ ρ ∈ S, bfun q ((3:ℝ)/10) R χ ρ)
              + (Real.exp (-(Work.LinnikAreas.A7.ac * lam)) -
                    Real.exp (-(Work.LinnikAreas.A7.ac * c))) *
                  (((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2) := by
            refine add_le_add (le_refl _) ?_
            split_ifs with h
            · exact le_refl _
            · exact hCnonneg
    calc Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
        ≤ Real.exp (-(Work.LinnikAreas.A7.ac*c)) * Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ
            + (Real.exp (-(Work.LinnikAreas.A7.ac*lam)) -
                Real.exp (-(Work.LinnikAreas.A7.ac*c))) *
                (((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2) := hmain
      _ ≤ Real.exp (-(Work.LinnikAreas.A7.ac*c)) *
              (((9:ℝ)/100) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η))
            + (Real.exp (-(Work.LinnikAreas.A7.ac*lam)) -
                Real.exp (-(Work.LinnikAreas.A7.ac*c))) *
                (((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2) := by
            exact add_le_add (mul_le_mul_of_nonneg_left hcert hE2nn) (le_refl _)
      _ = ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi lam - Work.LinnikAreas.A7.Aref c lam) +
            ((9:ℝ)/100) * Real.exp (-(Work.LinnikAreas.A7.ac * c)) * η := hkey.symm
  · have hwf : ¬ Function.HasFiniteSupport (Work.LinnikAreas.A7.wfun q ((3:ℝ)/10) R χ) := by
      intro h
      apply hfin
      unfold Function.HasFiniteSupport
      rw [← Work.LinnikAreas.A7.support_wfun_eq_bfun ((3:ℝ)/10) R χ]
      exact h
    have hboxAbs0 : Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ = 0 := by
      rw [show Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ =
            ∑ᶠ ρ : ℂ, bfun q ((3:ℝ)/10) R χ ρ from rfl,
          finsum_of_not_hasFiniteSupport hfin]
    have hW0 : Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ = 0 := by
      rw [Work.LinnikAreas.A7.WBox_eq_finsum, finsum_of_not_hasFiniteSupport hwf]
    have hBh : 0 ≤ ((9:ℝ)/100) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η) := by
      simpa [hboxAbs0] using hcert
    rw [hW0, hkey]
    exact add_nonneg (mul_nonneg (Real.exp_nonneg _) hBh)
      (mul_nonneg (sub_nonneg.mpr hE12) (sq_nonneg _))

end

end Work.A7
