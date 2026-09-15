import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_bound_m_strip_continuousOn

namespace Commons.NumberTheory.Zeta

open Complex MeasureTheory Filter
open scoped Topology

/-- Green–Tao (10.4) on the SPECIFIC strip `-1/(6m) < Re z_j < 100` (Green–Tao's own choice for the §10 application), with the continuity hypothesis required only on the open strip.  IMPORTANT: this CANNOT be deduced from `Commons.NumberTheory.Zeta.zeta_bound_m_strip_continuousOn`, because shrinking `σ` makes the hypotheses WEAKER, not stronger (the claim is monotone the "wrong" way in `σ`).  It must be obtained by COPYING the proof of `zeta_bound_m_strip_continuousOn` and substituting the explicit value `σ := 1 / (6 * (m : ℝ))` everywhere.  In that proof one finds `set σ : ℝ := 1 / (6 * (m:ℝ)) with hσdef`, `have hσpos : 0 < σ`, `have hβσ : β / Real.log 2 < σ`, and finally `refine ⟨σ, 1, C, hσpos, one_pos, lt_of_lt_of_le one_pos hC1, ?_⟩`; the new proof is identical except that the last line becomes `refine ⟨1, C, one_pos, lt_of_lt_of_le one_pos hC1, ?_⟩` (the rest of the proof uses `σ` only through `hσpos` and `hβσ`). -/
theorem zeta_bound_m_strip_sixth (m : ℕ) (hm : 1 ≤ m) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ R : ℝ, 3 ≤ R → ∀ F : (Fin m → ℂ) → (Fin m → ℂ) → ℂ, ∀ B : ℝ, 0 ≤ B →
      ContinuousOn (Function.uncurry F)
        {p : (Fin m → ℂ) × (Fin m → ℂ) |
          (∀ i, -(1 / (6 * (m : ℝ))) < (p.1 i).re ∧ (p.1 i).re < 100) ∧
          (∀ i, -(1 / (6 * (m : ℝ))) < (p.2 i).re ∧ (p.2 i).re < 100)} →
      (∀ (j : Fin m) (z z' : Fin m → ℂ),
        (∀ i, -(1 / (6 * (m : ℝ))) < (z i).re ∧ (z i).re < 100) →
        (∀ i, -(1 / (6 * (m : ℝ))) < (z' i).re ∧ (z' i).re < 100) →
        DifferentiableAt ℂ (fun u : ℂ => F (Function.update z j u) z') (z j)) →
      (∀ (j : Fin m) (z z' : Fin m → ℂ),
        (∀ i, -(1 / (6 * (m : ℝ))) < (z i).re ∧ (z i).re < 100) →
        (∀ i, -(1 / (6 * (m : ℝ))) < (z' i).re ∧ (z' i).re < 100) →
        DifferentiableAt ℂ (fun u : ℂ => F z (Function.update z' j u)) (z' j)) →
      (∀ z z' : Fin m → ℂ,
        (∀ i, -(1 / (6 * (m : ℝ))) < (z i).re ∧ (z i).re < 100) →
        (∀ i, -(1 / (6 * (m : ℝ))) < (z' i).re ∧ (z' i).re < 100) →
        ‖F z z'‖ ≤ B) →
      ‖((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) *
          (∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
            F (fun j => Commons.NumberTheory.Zeta.zetaM1Eta R (t j))
              (fun j => Commons.NumberTheory.Zeta.zetaM1Eta R (t' j))
            * (∏ j, (riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta R (t j)
                    + Commons.NumberTheory.Zeta.zetaM1Eta R (t' j))
                  / (riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta R (t j))
                      * riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta R (t' j)))))
            * (R : ℂ) ^ (∑ j, (Commons.NumberTheory.Zeta.zetaM1Eta R (t j)
                + Commons.NumberTheory.Zeta.zetaM1Eta R (t' j)))
            * (∏ j, ((Commons.NumberTheory.Zeta.zetaM1Eta R (t j)) ^ 2
                  * (Commons.NumberTheory.Zeta.zetaM1Eta R (t' j)) ^ 2)⁻¹)
            * Complex.I ^ m * Complex.I ^ m)
        - F 0 0 * (Real.log R) ^ m‖
        ≤ C ^ m * B * (1 + (Real.log R) ^ (m - 1))
          + C ^ m * B * Real.exp (-(δ * Real.sqrt (Real.log R))) := by
  obtain ⟨β₀, D₀, hβ₀pos, hβ₀10⟩ := zetaAux_exists
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmR : (0:ℝ) < (m:ℝ) := Nat.cast_pos.mpr (by omega)
  set σ : ℝ := 1 / (6 * (m:ℝ)) with hσdef
  have hσpos : 0 < σ := by rw [hσdef]; positivity
  have hσle : σ ≤ 1 / 6 := by
    rw [hσdef]
    refine one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 6) ?_
    have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    linarith
  set β : ℝ := min β₀ (Real.log 2 / (12 * (m:ℝ))) with hβdef
  have hβpos : 0 < β := by
    rw [hβdef]; exact lt_min hβ₀pos (div_pos hlog2pos (by positivity))
  have hβle : β ≤ β₀ := by rw [hβdef]; exact min_le_left _ _
  have hβ10 : β ≤ 1 / 10 := le_trans hβle hβ₀10
  have hβσ : β / Real.log 2 < σ := by
    rw [hβdef, hσdef, div_lt_iff₀ hlog2pos]
    calc min β₀ (Real.log 2 / (12 * (m:ℝ))) ≤ Real.log 2 / (12 * (m:ℝ)) := min_le_right _ _
      _ < Real.log 2 / (6 * (m:ℝ)) :=
          div_lt_div_of_pos_left hlog2pos (by positivity) (by nlinarith [hmR])
      _ = (1 / (6 * (m:ℝ))) * Real.log 2 := by ring
  obtain ⟨hD⟩ : Nonempty (ZetaAux β) := zetaAux_le D₀ hβ₀pos hβ₀10 hβpos hβ10 hβle
  obtain ⟨C, hC1, hCbound⟩ := zetaMmf_bound hD hβpos hβ10
  refine ⟨1, C, one_pos, lt_of_lt_of_le one_pos hC1, ?_⟩
  intro R hR F B hB hcontOn hd1 hd2 hbound
  have hRne : (R : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : (0:ℝ) < R))
  have hβlog2pos : 0 < β / Real.log 2 := div_pos hβpos hlog2pos
  have hUopen := isOpen_stripSet m σ
  set θ : ℝ := (σ - β / Real.log 2) / 2 with hθdef
  have hθpos : 0 < θ := by rw [hθdef]; linarith
  set a : ℝ := -(β / Real.log 2) - θ with hadef
  set b : ℝ := 1 + θ with hbdef
  have hale : a ≤ -(β / Real.log 2) := by rw [hadef]; linarith
  have halt : a < -(β / Real.log 2) := by rw [hadef]; linarith
  have hbge : 1 ≤ b := by rw [hbdef]; linarith
  have hbgt : 1 < b := by rw [hbdef]; linarith
  have hagt : -σ < a := by rw [hadef, hθdef]; linarith
  have hblt : b < 100 := by rw [hbdef, hθdef]; linarith
  have hAclosed := isClosed_boxSet m a b
  have hAU : {p : (Fin m → ℂ) × (Fin m → ℂ) |
      (∀ i, a ≤ (p.1 i).re ∧ (p.1 i).re ≤ b) ∧
      (∀ i, a ≤ (p.2 i).re ∧ (p.2 i).re ≤ b)} ⊆
      {p : (Fin m → ℂ) × (Fin m → ℂ) |
        (∀ i, -σ < (p.1 i).re ∧ (p.1 i).re < 100) ∧
        (∀ i, -σ < (p.2 i).re ∧ (p.2 i).re < 100)} := by
    intro p hp
    exact ⟨fun i => ⟨lt_of_lt_of_le hagt (hp.1 i).1, lt_of_le_of_lt (hp.1 i).2 hblt⟩,
      fun i => ⟨lt_of_lt_of_le hagt (hp.2 i).1, lt_of_le_of_lt (hp.2 i).2 hblt⟩⟩
  have hUclosed : IsClosed {p : (Fin m → ℂ) × (Fin m → ℂ) |
      (∀ i, -σ < (p.1 i).re ∧ (p.1 i).re < 100) ∧
      (∀ i, -σ < (p.2 i).re ∧ (p.2 i).re < 100)}ᶜ := isClosed_compl_iff.mpr hUopen
  obtain ⟨χ, hχ0, hχ1, _⟩ := exists_continuous_zero_one_of_isClosed
    hUclosed hAclosed (disjoint_compl_right.mono_left hAU).symm
  let F' : (Fin m → ℂ) → (Fin m → ℂ) → ℂ := fun z z' => ((χ (z, z') : ℝ) : ℂ) * F z z'
  have hF'eq : Function.uncurry F'
      = fun p : (Fin m → ℂ) × (Fin m → ℂ) => ((χ p : ℝ) : ℂ) * F p.1 p.2 := by
    funext p
    simp only [Function.uncurry, F', Prod.mk.eta]
  have hAdm : ZetaAdm β m F' B := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hF'eq]
      refine continuous_ofReal_mul_of_continuousOn (fun p => (χ p : ℝ)) (fun p => F p.1 p.2)
        {p : (Fin m → ℂ) × (Fin m → ℂ) |
          (∀ i, -σ < (p.1 i).re ∧ (p.1 i).re < 100) ∧
          (∀ i, -σ < (p.2 i).re ∧ (p.2 i).re < 100)} B χ.continuous hcontOn hUopen ?_ ?_
      · intro p hp; exact hχ0 hp
      · intro p hp; exact hbound p.1 p.2 hp.1 hp.2
    · intro j z z' hz hz'
      have hzs : ∀ i, -σ < (z i).re ∧ (z i).re < 100 :=
        fun i => ZetaReg_subset_strip hβpos.le hβσ (hz i)
      have hz's : ∀ i, -σ < (z' i).re ∧ (z' i).re < 100 :=
        fun i => ZetaReg_subset_strip hβpos.le hβσ (hz' i)
      have hzA := ZetaRegVec_between hale hbge hβpos hz
      have hz'A := ZetaRegVec_between hale hbge hβpos hz'
      have hzS := ZetaRegVec_between_strict halt hbgt hβpos hz
      have heq : (fun u : ℂ => F (Function.update z j u) z') =ᶠ[𝓝 (z j)]
          (fun u : ℂ =>
            ((χ (Function.update z j u, z') : ℝ) : ℂ) * F (Function.update z j u) z') := by
        have hmem : Set.Ioo a b ∈ 𝓝 ((z j).re) := isOpen_Ioo.mem_nhds ⟨(hzS j).1, (hzS j).2⟩
        have hev : ∀ᶠ u : ℂ in 𝓝 (z j), u.re ∈ Set.Ioo a b :=
          (Complex.continuous_re.continuousAt (x := z j)).preimage_mem_nhds hmem
        filter_upwards [hev] with u hu
        have hinA : (Function.update z j u, z') ∈ {p : (Fin m → ℂ) × (Fin m → ℂ) |
            (∀ i, a ≤ (p.1 i).re ∧ (p.1 i).re ≤ b) ∧
            (∀ i, a ≤ (p.2 i).re ∧ (p.2 i).re ≤ b)} :=
          ⟨mem_boxSet_update hzA ⟨hu.1.le, hu.2.le⟩, hz'A⟩
        rw [hχ1 hinA]; simp
      exact (hd1 j z z' hzs hz's).congr_of_eventuallyEq heq.symm
    · intro j z z' hz hz'
      have hzs : ∀ i, -σ < (z i).re ∧ (z i).re < 100 :=
        fun i => ZetaReg_subset_strip hβpos.le hβσ (hz i)
      have hz's : ∀ i, -σ < (z' i).re ∧ (z' i).re < 100 :=
        fun i => ZetaReg_subset_strip hβpos.le hβσ (hz' i)
      have hzA := ZetaRegVec_between hale hbge hβpos hz
      have hz'A := ZetaRegVec_between hale hbge hβpos hz'
      have hz'S := ZetaRegVec_between_strict halt hbgt hβpos hz'
      have heq : (fun u : ℂ => F z (Function.update z' j u)) =ᶠ[𝓝 (z' j)]
          (fun u : ℂ =>
            ((χ (z, Function.update z' j u) : ℝ) : ℂ) * F z (Function.update z' j u)) := by
        have hmem : Set.Ioo a b ∈ 𝓝 ((z' j).re) := isOpen_Ioo.mem_nhds ⟨(hz'S j).1, (hz'S j).2⟩
        have hev : ∀ᶠ u : ℂ in 𝓝 (z' j), u.re ∈ Set.Ioo a b :=
          (Complex.continuous_re.continuousAt (x := z' j)).preimage_mem_nhds hmem
        filter_upwards [hev] with u hu
        have hinA : (z, Function.update z' j u) ∈ {p : (Fin m → ℂ) × (Fin m → ℂ) |
            (∀ i, a ≤ (p.1 i).re ∧ (p.1 i).re ≤ b) ∧
            (∀ i, a ≤ (p.2 i).re ∧ (p.2 i).re ≤ b)} :=
          ⟨hzA, mem_boxSet_update hz'A ⟨hu.1.le, hu.2.le⟩⟩
        rw [hχ1 hinA]; simp
      exact (hd2 j z z' hzs hz's).congr_of_eventuallyEq heq.symm
    · intro z z' hz hz'
      have hzs : ∀ i, -σ < (z i).re ∧ (z i).re < 100 :=
        fun i => ZetaReg_subset_strip hβpos.le hβσ (hz i)
      have hz's : ∀ i, -σ < (z' i).re ∧ (z' i).re < 100 :=
        fun i => ZetaReg_subset_strip hβpos.le hβσ (hz' i)
      have hzA := ZetaRegVec_between hale hbge hβpos hz
      have hz'A := ZetaRegVec_between hale hbge hβpos hz'
      have hχz : χ (z, z') = 1 := hχ1 ⟨hzA, hz'A⟩
      show ‖((χ (z, z') : ℝ) : ℂ) * F z z'‖ ≤ B
      rw [hχz]; simp only [Complex.ofReal_one, one_mul]
      exact hbound z z' hzs hz's
  have hz : zetaMmf R m F = zetaMmf R m F' := by
    refine zetaMmf_congr (fun t t' => ?_)
    have h1 := ZetaRegVec_between hale hbge hβpos (ZetaRegVec_eta (R := R) hβpos hR t)
    have h2 := ZetaRegVec_between hale hbge hβpos (ZetaRegVec_eta (R := R) hβpos hR t')
    have hχ1' : χ ((fun j => zetaM1Eta R (t j)), (fun j => zetaM1Eta R (t' j))) = 1 :=
      hχ1 ⟨h1, h2⟩
    show F (fun j => zetaM1Eta R (t j)) (fun j => zetaM1Eta R (t' j))
        = ((χ ((fun j => zetaM1Eta R (t j)), (fun j => zetaM1Eta R (t' j))) : ℝ) : ℂ)
          * F (fun j => zetaM1Eta R (t j)) (fun j => zetaM1Eta R (t' j))
    rw [hχ1']; simp
  have hz00 : F' 0 0 = F 0 0 := by
    have h0 : χ (((0 : Fin m → ℂ)), ((0 : Fin m → ℂ))) = 1 := by
      apply hχ1
      constructor
      · intro i
        simp only [Pi.zero_apply, Complex.zero_re]
        exact ⟨by linarith [hale, hβlog2pos], by linarith [hbge]⟩
      · intro i
        simp only [Pi.zero_apply, Complex.zero_re]
        exact ⟨by linarith [hale, hβlog2pos], by linarith [hbge]⟩
    show ((χ (((0 : Fin m → ℂ)), ((0 : Fin m → ℂ))) : ℝ) : ℂ) * F 0 0 = F 0 0
    rw [h0]; simp
  have hb := hCbound R hR m hm F' B hB hAdm
  rw [← zetaMmf_eq_explicit hRne m F, hz, ← hz00]
  exact le_trans hb (le_add_of_nonneg_right (mul_nonneg
    (mul_nonneg (pow_nonneg (le_of_lt (lt_of_lt_of_le one_pos hC1)) m) hB)
    (Real.exp_pos _).le))


end Commons.NumberTheory.Zeta
