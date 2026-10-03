/-
# Area A4: the fine-support form of Proposition `lip` (`LipL1Fine`)

`Work.KMTAreas.A4.peluseLipUniform` proves Proposition `lip` of Krause--Mirek--Tao with the
Fourier support of the dual function reported as the Ionescu--Wainger major arc
`𝓜_{≤l,≤k}`, a union of `#(ℚ/ℤ)_{≤l}` arcs.  That set is far too large for the reproduction step
of Proposition `lip-2` (`Work.KMTAreas.A4.lip2Reproduce`), which needs to extract a *single* arc;
`(ℚ/ℤ)_{≤l}` is super-polynomial in `δ⁻¹`, while the reproduction step can only afford
`δ^{-O(1)}`.

This file proves the finer statement `Work.KMTAreas.A4.LipL1Fine`, in which the dual function is
supported in the union of the `q` arcs of radius `2^k` around the `q`-torsion frequencies `a/q`,
where `q` is the modulus produced by Peluse's inverse theorem: `q ≤ C δ^{-K}` and
`2^k ≤ C δ^{-K} / N`.  The proof is the proof of `peluseLipUniform` with a sharper Fourier-support
argument.

The support argument is the crux.  The dual function is `F = λ · smoothOp w G q` with
`w = lipWeight ψ ε N'`, so its `ℤ`-Fourier transform factors as `𝓕G(ξ) · µ̂(ξ)`, and `µ̂` factors as
`(N')⁻¹ (∑_{m' ≤ N'} e(-q m' ξ)) · ε ∑_u ψ(ε u) e(-u · q ξ)`.  Poisson summation evaluates the
second factor as `∑_n 𝓕ψ((θ+n)/ε)` with `θ` a real representative of `q ξ`; since `𝓕ψ` vanishes off
`[-1,1]`, this factor is zero unless `|q ξ - n| ≤ ε` for some `n : ℤ`, i.e. unless `ξ` is within
`ε/q` of a `q`-torsion frequency.  This is the lemma `lipWeightFourierSupportFine`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2Defs

set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 20000

open scoped BigOperators FourierTransform
open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## The `q` torsion frequencies -/

/-- The `q` torsion frequencies of the frequency circle as a finite set: `{a/q : a < q}` (of
cardinality at most `q`). -/
noncomputable def lipTorsionArcs (q : ℕ) : Finset FreqCircle :=
  (Finset.range q).image fun a : ℕ => (((a : ℝ) / (q : ℝ) : ℝ) : FreqCircle)

theorem lipTorsionArcs_card_le (q : ℕ) : (lipTorsionArcs q).card ≤ q := by
  rw [lipTorsionArcs]
  exact le_trans Finset.card_image_le (le_of_eq (Finset.card_range q))

/-- The arc of radius `1` around `0` is the whole circle (every class has a representative in
`[-1,0]`). -/
theorem lipArcSet_zero_one : arcSet (0 : FreqCircle) (1 : ℝ) = Set.univ := by
  refine Set.eq_univ_of_forall fun γ => ?_
  obtain ⟨θ, hθ, hθγ⟩ : ∃ θ ∈ Set.Icc (-1 : ℝ) 0, ((θ : ℝ) : FreqCircle) = γ := by
    have h : γ ∈ ((↑) : ℝ → FreqCircle) '' Set.Icc (-1 : ℝ) 0 := by
      rw [surjOn_Icc_neg_one_zero]; exact Set.mem_univ γ
    exact h
  exact ⟨θ, by rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2], by rw [zero_add]; exact hθγ.symm⟩

/-- The class of `n/q` is the class of `a/q` for some `a < q`. -/
theorem exists_range_div_class (q : ℕ) (hq : 1 ≤ q) (n : ℤ) :
    ∃ a : ℕ, a ∈ Finset.range q ∧
      (((a : ℝ) / (q : ℝ) : ℝ) : FreqCircle) = (((n : ℝ) / (q : ℝ) : ℝ) : FreqCircle) := by
  have hqz : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  set m : ℤ := n % (q : ℤ) with hmdef
  have hm0 : 0 ≤ m := Int.emod_nonneg n (ne_of_gt hqz)
  have hmlt : m < (q : ℤ) := Int.emod_lt_of_pos n hqz
  have hto : ((m.toNat : ℤ)) = m := Int.toNat_of_nonneg hm0
  refine ⟨m.toNat, Finset.mem_range.mpr (by omega), ?_⟩
  have han : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast hto
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hdvd : (q : ℤ) * (n / (q : ℤ)) = n - m := by
    have h := Int.emod_add_mul_ediv n (q : ℤ)
    rw [← hmdef] at h
    linarith
  have hsplit : (n : ℝ) = (m : ℝ) + (q : ℝ) * (((n / (q : ℤ) : ℤ)) : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hdvd
    push_cast at h
    linarith
  have hk : (((((n / (q : ℤ) : ℤ)) : ℝ)) : FreqCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    refine ⟨n / (q : ℤ), ?_⟩
    rw [zsmul_eq_mul, mul_one]
  have hdiv : (n : ℝ) / (q : ℝ) = (m : ℝ) / (q : ℝ) + (((n / (q : ℤ) : ℤ)) : ℝ) := by
    field_simp
    linarith
  rw [han, hdiv, AddCircle.coe_add, hk, add_zero]

/-! ## The fine Fourier support of the smoothed dual function -/

/-- **The fine Fourier support of the smoothing operator.**  If `𝓕ψ` vanishes off `[-1,1]` then the
smoothed progression average `x ↦ ∑_m lipWeight ψ ε N' m · G (x - q m)` has its `ℤ`-Fourier
transform supported in the union of the `q` arcs of radius `ε/q` around the `q`-torsion
frequencies `a/q`. -/
theorem lipWeightFourierSupportFine (ψ : SchwartzR)
    (hη : ∀ s : ℝ, 1 < |s| → schFT ψ s = 0)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {N' : ℕ} (hN' : 1 ≤ N') {G : ℤ → ℂ} (hG : Summable fun x : ℤ => ‖G x‖)
    {q : ℕ} (hq : 1 ≤ q) {r : ℝ} (hr : ε / (q : ℝ) ≤ r) :
    FourierSupportIn (smoothOp (lipWeight ψ ε N') G (q : ℤ))
      (⋃ α ∈ (lipTorsionArcs q : Set FreqCircle), arcSet α r) := by
  intro ξ hξ
  obtain ⟨x, hx⟩ : ∃ x : ℝ, ((x : ℝ) : FreqCircle) = ξ :=
    ⟨(AddCircle.equivIco (1 : ℝ) 0 ξ).val, AddCircle.coe_equivIco⟩
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  -- outside the torsion arcs, `ε < |q x - n|` for every `n`
  have hfar : ∀ n : ℤ, ε < |(q : ℝ) * x - (n : ℝ)| := by
    intro n
    by_contra hcon
    have hcon' : |(q : ℝ) * x - (n : ℝ)| ≤ ε := not_lt.mp hcon
    obtain ⟨a, ha, hag⟩ := exists_range_div_class q hq n
    have hmemA : (((a : ℝ) / (q : ℝ) : ℝ) : FreqCircle) ∈ (lipTorsionArcs q : Set FreqCircle) := by
      rw [lipTorsionArcs]
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    have hdist : |x - (n : ℝ) / (q : ℝ)| ≤ r := by
      have h1 : x - (n : ℝ) / (q : ℝ) = ((q : ℝ) * x - (n : ℝ)) / (q : ℝ) := by
        field_simp
      have h2 : |((q : ℝ) * x - (n : ℝ)) / (q : ℝ)| ≤ ε / (q : ℝ) := by
        rw [abs_div, abs_of_pos hqpos]
        exact div_le_div_of_nonneg_right hcon' hqpos.le
      rw [h1]
      linarith
    have hxeq : ξ = (((a : ℝ) / (q : ℝ) : ℝ) : FreqCircle)
        + (((x - (n : ℝ) / (q : ℝ)) : ℝ) : FreqCircle) := by
      rw [hag, ← AddCircle.coe_add,
        show (n : ℝ) / (q : ℝ) + (x - (n : ℝ) / (q : ℝ)) = x by ring, hx]
    exact hξ (Set.mem_biUnion hmemA ⟨_, hdist, hxeq⟩)
  -- hence the multiplier vanishes
  have hzsmul : ((q : ℤ) • ξ) = (((q : ℝ) * x : ℝ) : FreqCircle) := by
    rw [← hx, ← AddCircle.coe_zsmul]
    congr 1
    rw [zsmul_eq_mul]; push_cast; ring
  have hvan : (ε : ℂ) * ∑' u : ℤ,
      ((ψ (ε * (u : ℝ)) : ℂ) * (fourier (-u) ((q : ℤ) • ξ) : ℂ)) = 0 := by
    rw [hzsmul]
    exact lipPoissonVanish ψ hη hε hfar
  have hwsum : Summable (fun m : ℤ => ‖lipWeight ψ ε N' m‖) := lipWeightSummable ψ hε hε1 hN'
  calc ZFourier (smoothOp (lipWeight ψ ε N') G (q : ℤ)) ξ
      = ZFourier G ξ * ∑' m : ℤ, lipWeight ψ ε N' m * (fourier (-((q : ℤ) * m)) ξ : ℂ) :=
        lipZFourierSmoothOp hwsum hG (q : ℤ) ξ
    _ = ZFourier G ξ * ((N' : ℝ)⁻¹ * (∑ m' ∈ Finset.Icc 1 N',
          (fourier (-((q : ℤ) * (m' : ℤ))) ξ : ℂ)) * ((ε : ℂ) * ∑' u : ℤ,
          (ψ (ε * (u : ℝ)) : ℂ) * (fourier (-u) ((q : ℤ) • ξ) : ℂ))) := by
        rw [lipWeightMultiplierFactor ψ hε hN' (q : ℤ) ξ]
    _ = 0 := by rw [hvan]; ring

theorem lipL1Fine (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) (hPel : Work.KMTContract.PeluseInverseKMT P) : Work.KMTAreas.A4.LipL1Fine P := by
  classical
  obtain ⟨ψ, hψint, hψsupp⟩ := lipSchwartzExists
  obtain ⟨Kw, hKwpos, hKw⟩ := lipWeightTsumLe ψ
  obtain ⟨C₀, K₀, hC₀pos, hK₀pos, hPel'⟩ := hPel 2 (by norm_num)
  -- the constants
  set u : ℕ := Nat.ceil K₀ + 1 with hudef
  have hu_ge : K₀ ≤ (u : ℝ) := by
    rw [hudef]; push_cast
    have := Nat.le_ceil K₀; linarith
  have hu1 : 1 ≤ u := by rw [hudef]; omega
  set Kc : ℕ := 5 * u + 6 with hKcdef
  have hKcu : u ≤ Kc := by rw [hKcdef]; omega
  have hKc2u : 2 * u ≤ Kc := by rw [hKcdef]; omega
  have hKc3u : 3 * u ≤ Kc := by rw [hKcdef]; omega
  have hKc4u : 4 * u ≤ Kc := by rw [hKcdef]; omega
  have hKc1 : 1 ≤ Kc := by rw [hKcdef]; omega
  have hKcpos : (0 : ℝ) < (Kc : ℝ) := by positivity
  set K' : ℝ := 5 + 2 * C₀ with hK'def
  have hK'pos : 0 < K' := by rw [hK'def]; linarith
  have hK'1 : 1 ≤ K' := by rw [hK'def]; linarith
  have hfour : 0 < 4 * C₀ * calcConst ψ * K' := by
    have h1 : 0 < 4 * C₀ := by linarith [hC₀pos]
    exact mul_pos (mul_pos h1 (calcConst_pos ψ)) hK'pos
  set c₁ : ℝ := 1 + 4 * C₀ * calcConst ψ * K' with hc₁def
  have hc₁pos : 0 < c₁ := by rw [hc₁def]; linarith
  have hc₁1 : 1 ≤ c₁ := by rw [hc₁def]; linarith
  have hc₁big : 4 * C₀ * calcConst ψ * K' ≤ c₁ ^ 10 := by
    have h2 : 4 * C₀ * calcConst ψ * K' ≤ c₁ := by rw [hc₁def]; linarith
    calc 4 * C₀ * calcConst ψ * K' ≤ c₁ := h2
      _ ≤ c₁ ^ 10 := le_self_pow₀ hc₁1 (by norm_num)
  set c₂ : ℝ := 4 * C₀ ^ 2 * calcConst ψ * K' with hc₂def
  have hc₂pos : 0 < c₂ := by rw [hc₂def]; nlinarith [hfour, hC₀pos]
  have hc₂pos' : 0 < 4 * C₀ * calcConst ψ * K' := hfour
  have hc₂div : 4 * C₀ * calcConst ψ * K' = c₂ / C₀ := by
    rw [hc₂def]; field_simp
  set C₁ : ℝ := 2 * C₀ ^ 2 * calcConst ψ * K' + 2 * Kw * K' + C₀ + 2 with hC₁def
  have hC₁pos : 0 < C₁ := by
    rw [hC₁def]; nlinarith [hfour, hKwpos, hC₀pos]
  set Cc : ℝ := (c₁ + c₂ + 10) ^ 2 + 2 * C₁ + 2 * C₀ * Kw * K' + 2 * c₂ + C₀ + 100 with hCcdef
  have hCcpos : 0 < Cc := by
    rw [hCcdef]
    have h1 : 0 ≤ (c₁ + c₂ + 10) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ 2 * C₁ := by linarith [hC₁pos]
    have h3 : 0 ≤ 2 * C₀ * Kw * K' := by positivity
    have h4 : 0 ≤ 2 * c₂ := by linarith [hc₂pos]
    have h5 : 0 ≤ C₀ := hC₀pos.le
    linarith
  have hCc2C₁ : 2 * C₁ ≤ Cc := by
    rw [hCcdef]
    have h1 : 0 ≤ (c₁ + c₂ + 10) ^ 2 := sq_nonneg _
    have h3 : 0 ≤ 2 * C₀ * Kw * K' := by positivity
    have h4 : 0 ≤ 2 * c₂ := by linarith [hc₂pos]
    have h5 : 0 ≤ C₀ := hC₀pos.le
    linarith
  have hCcC₀ : C₀ ≤ Cc := by
    rw [hCcdef]
    have h1 : 0 ≤ (c₁ + c₂ + 10) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ 2 * C₁ := by linarith [hC₁pos]
    have h3 : 0 ≤ 2 * C₀ * Kw * K' := by positivity
    have h4 : 0 ≤ 2 * c₂ := by linarith [hc₂pos]
    linarith
  have hCc7 : 7 ≤ Cc := by
    rw [hCcdef]
    have h1 : 0 ≤ (c₁ + c₂ + 10) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ 2 * C₁ := by linarith [hC₁pos]
    have h3 : 0 ≤ 2 * C₀ * Kw * K' := by positivity
    have h4 : 0 ≤ 2 * c₂ := by linarith [hc₂pos]
    have h5 : 0 ≤ C₀ := hC₀pos.le
    linarith
  have hCc2C₀ : 2 * C₀ ≤ Cc := by
    have h6 : (0 : ℝ) ≤ 2 * C₀ ^ 2 * calcConst ψ * K' :=
      mul_nonneg (mul_nonneg (by positivity) (calcConst_pos ψ).le) hK'pos.le
    have h7 : (0 : ℝ) ≤ 2 * Kw * K' := mul_nonneg (by positivity) hK'pos.le
    have h2 : 2 * C₀ ≤ 2 * C₁ := by
      rw [hC₁def]; linarith
    linarith [hCc2C₁]
  have hCcc₁c₂ : c₁ * c₂ ≤ Cc := by
    rw [hCcdef]
    have h1 : c₁ * c₂ ≤ (c₁ + c₂ + 10) ^ 2 := by nlinarith [hc₁pos, hc₂pos]
    have h3 : 0 ≤ 2 * C₁ := by linarith [hC₁pos]
    have h4 : 0 ≤ 2 * C₀ * Kw * K' := by positivity
    have h5 : 0 ≤ 2 * c₂ := by linarith [hc₂pos]
    have h6 : 0 ≤ C₀ := hC₀pos.le
    linarith
  have hCc2c₂ : 2 * c₂ ≤ Cc := by
    rw [hCcdef]
    have h1 : 0 ≤ (c₁ + c₂ + 10) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ 2 * C₁ := by linarith [hC₁pos]
    have h3 : 0 ≤ 2 * C₀ * Kw * K' := by positivity
    have h4 : 0 ≤ C₀ := hC₀pos.le
    linarith
  have hCcKw : 2 * C₀ * Kw * K' ≤ Cc := by
    rw [hCcdef]
    have h1 : 0 ≤ (c₁ + c₂ + 10) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ 2 * C₁ := by linarith [hC₁pos]
    have h4 : 0 ≤ 2 * c₂ := by linarith [hc₂pos]
    have h5 : 0 ≤ C₀ := hC₀pos.le
    linarith
  refine ⟨Cc, (Kc : ℝ), hCcpos, hKcpos, ?_⟩
  intro ρ hρpos hρle N N₀ δ f g h hN hδpos hδle hN₀lo hN₀hi hfs hgs hhs hfb hgb hhb hcorr
  have hD1 : 1 ≤ δ⁻¹ := by
    rw [one_le_inv₀ hδpos]
    exact hδle
  have hDpos : 0 < δ⁻¹ := inv_pos.mpr hδpos
  by_cases hcaseA : N ≤ Cc * δ⁻¹ ^ (Kc : ℝ)
  · -- #### Case A: `N` is small; the first dual function works
    set F₀ : ℤ → ℂ := AhalfTranspose N P h g with hF₀def
    have hF₀sup : ∀ x : ℤ, ‖F₀ x‖ ≤ 1 := fun x => lipNormAhalfTranspose hN P hhb hgb x
    have hF₀supp : SupportIn F₀ (N₀ + N) := lipSupportAhalfTranspose P hhs
    have hF₀one : ellOne F₀ ≤ 2 * ((N₀ + N : ℕ) : ℝ) + 1 := by
      simpa using ellOne_le_of_supportIn F₀ (N₀ + N) hF₀supp hF₀sup
    have hF₀summ : Summable fun x : ℤ => ‖F₀ x‖ := by
      refine summable_of_ne_finset_zero
        (s := Finset.Icc (-(((N₀ + N : ℕ) : ℤ))) (((N₀ + N : ℕ) : ℤ))) fun x hx => ?_
      have hx' : (N₀ + N) < x.natAbs := by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hx
        rcases hx with hh | hh <;> omega
      rw [hF₀supp x hx', norm_zero]
    have hF₀corr : δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair f F₀‖ := by
      have h1 : bilinPair f F₀ = bilinPair (AhalfZ N P f g) h := by
        rw [show bilinPair f F₀ = bilinPair F₀ f from lipBilinPairComm f F₀, hF₀def]
        exact (bilinPair_AhalfZ_eq_transpose (FinSupp.of_supportIn hfs)
          (FinSupp.of_supportIn hgs) (FinSupp.of_supportIn hhs) N P).symm
      rw [h1]; exact hcorr
    have hlam₀ : ‖(((Cc / 7 : ℝ)) : ℂ)‖ = Cc / 7 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hD3 : (1 : ℝ) ≤ δ⁻¹ ^ (Kc : ℝ) := Real.one_le_rpow hD1 hKcpos.le
    set A₀ : Finset FreqCircle := {0} with hA₀def
    refine ⟨(((Cc / 7 : ℝ)) : ℂ) • F₀, 0, A₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      rw [Pi.smul_apply, norm_smul, hlam₀]
      have h2 := hF₀sup x
      nlinarith [hCcpos, h2, hD3]
    · show Summable fun x : ℤ => ‖(((Cc / 7 : ℝ)) : ℂ) • F₀ x‖
      have hsum' : (fun x : ℤ => ‖(((Cc / 7 : ℝ)) : ℂ) • F₀ x‖)
          = fun x : ℤ => (Cc / 7) * ‖F₀ x‖ := by
        funext x
        rw [norm_smul, hlam₀]
      rw [hsum']
      exact hF₀summ.mul_left (Cc / 7)
    · show ellOne ((((Cc / 7 : ℝ)) : ℂ) • F₀) ≤ Cc * δ⁻¹ ^ (Kc : ℝ) * (N : ℝ) ^ P.natDegree
      rw [lipEllOneSmul, hlam₀]
      have hNd1 : (1 : ℝ) ≤ (N : ℝ) ^ P.natDegree := one_le_pow₀ (by exact_mod_cast hN)
      have hNle : (N : ℝ) ≤ (N : ℝ) ^ P.natDegree := by
        have h2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
          nlinarith [show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN]
        have h3 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ P.natDegree :=
          pow_le_pow_right₀ (by exact_mod_cast hN) (by omega)
        linarith
      have hM : 2 * ((N₀ + N : ℕ) : ℝ) + 1 ≤ 7 * (N : ℝ) ^ P.natDegree := by
        push_cast
        nlinarith [hN₀hi, hNle, hNd1]
      calc Cc / 7 * ellOne F₀ ≤ Cc / 7 * (2 * ((N₀ + N : ℕ) : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hF₀one (by positivity)
        _ ≤ Cc / 7 * (7 * (N : ℝ) ^ P.natDegree) :=
            mul_le_mul_of_nonneg_left hM (by positivity)
        _ = Cc * (N : ℝ) ^ P.natDegree := by ring
        _ ≤ Cc * δ⁻¹ ^ (Kc : ℝ) * (N : ℝ) ^ P.natDegree := by
            have hp : (0 : ℝ) ≤ (N : ℝ) ^ P.natDegree := by positivity
            calc Cc * (N : ℝ) ^ P.natDegree
                ≤ Cc * (δ⁻¹ ^ (Kc : ℝ) * (N : ℝ) ^ P.natDegree) :=
                  mul_le_mul_of_nonneg_left (by
                    simpa using mul_le_mul_of_nonneg_right hD3 hp) hCcpos.le
              _ = Cc * δ⁻¹ ^ (Kc : ℝ) * (N : ℝ) ^ P.natDegree := by ring
    · have hUniv : (⋃ α ∈ (A₀ : Set FreqCircle), arcSet α ((2 : ℝ) ^ (0 : ℤ))) = Set.univ := by
        refine Set.eq_univ_of_forall fun γ => ?_
        refine Set.mem_biUnion (x := (0 : FreqCircle)) ?_ ?_
        · rw [hA₀def]
          exact Finset.mem_coe.mpr (Finset.mem_singleton_self (0 : FreqCircle))
        · rw [show ((2 : ℝ) ^ (0 : ℤ)) = 1 by norm_num, lipArcSet_zero_one]
          exact Set.mem_univ γ
      rw [hUniv]
      intro ξ hξ
      exact absurd (Set.mem_univ ξ) hξ
    · have h6 : (1 : ℝ) ≤ Cc * δ⁻¹ ^ (Kc : ℝ) := by nlinarith [hCc7, hD3]
      rw [hA₀def, Finset.card_singleton]
      simpa using h6
    · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      have h1 : (2 : ℝ) ^ (0 : ℤ) = 1 := by norm_num
      rw [h1, one_le_div hNpos]
      exact hcaseA
    · show δ ^ (Kc : ℝ) * (N : ℝ) ^ P.natDegree
        ≤ ‖bilinPair f ((((Cc / 7 : ℝ)) : ℂ) • F₀)‖
      rw [lipBilinPairSmul, norm_mul, hlam₀]
      have h6 : δ ^ (Kc : ℝ) ≤ δ := by
        have h1' : (1 : ℝ) ≤ (Kc : ℝ) := by exact_mod_cast hKc1
        have h := Real.rpow_le_rpow_of_exponent_ge hδpos hδle h1'
        simpa using h
      have hNd0 : 0 < (N : ℝ) ^ P.natDegree := by positivity
      calc δ ^ (Kc : ℝ) * (N : ℝ) ^ P.natDegree
          ≤ δ * (N : ℝ) ^ P.natDegree := mul_le_mul_of_nonneg_right h6 hNd0.le
        _ ≤ (Cc / 7) * (δ * (N : ℝ) ^ P.natDegree) := by
            have h7 : (1 : ℝ) ≤ Cc / 7 := by linarith [hCc7]
            refine le_trans (le_of_eq (one_mul _).symm)
              (mul_le_mul_of_nonneg_right h7 (by positivity))
        _ ≤ (Cc / 7) * ‖bilinPair f F₀‖ :=
            mul_le_mul_of_nonneg_left hF₀corr (by positivity)
  · -- #### Case B: the smoothing argument
    push_neg at hcaseA
    rw [Real.rpow_natCast] at hcaseA
    have hanti : ∀ {m n : ℕ}, m ≤ n → δ ^ n ≤ δ ^ m := by
      intro m n hmn
      have h := Real.rpow_le_rpow_of_exponent_ge hδpos hδle
        (show (m : ℝ) ≤ (n : ℝ) by exact_mod_cast hmn)
      simpa [Real.rpow_natCast] using h
    have hδu_le : δ ^ u ≤ δ ^ K₀ := by
      have h2 := Real.rpow_le_rpow_of_exponent_ge hδpos hδle hu_ge
      simpa [Real.rpow_natCast] using h2
    have hD1u : (1 : ℝ) ≤ (δ⁻¹) ^ u := one_le_pow₀ hD1
    have hδinv_le : δ⁻¹ ^ K₀ ≤ (δ⁻¹) ^ u := by
      have h1 : 0 < δ ^ K₀ := Real.rpow_pos_of_pos hδpos K₀
      have h2 : 0 < δ ^ u := pow_pos hδpos u
      calc δ⁻¹ ^ K₀ = (δ ^ K₀)⁻¹ := Real.inv_rpow hδpos.le K₀
        _ ≤ (δ ^ u)⁻¹ := (inv_le_inv₀ h1 h2).mpr hδu_le
        _ = (δ⁻¹) ^ u := (inv_pow δ u).symm
    have hNbig : C₀ * δ⁻¹ ^ K₀ < N := by
      have h2 : C₀ * δ⁻¹ ^ K₀ ≤ Cc * (δ⁻¹) ^ Kc := by
        calc C₀ * δ⁻¹ ^ K₀ ≤ Cc * δ⁻¹ ^ K₀ :=
              mul_le_mul_of_nonneg_right hCcC₀ (Real.rpow_pos_of_pos hDpos K₀).le
          _ ≤ Cc * (δ⁻¹) ^ u := mul_le_mul_of_nonneg_left hδinv_le hCcpos.le
          _ ≤ Cc * (δ⁻¹) ^ Kc :=
              mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD1 hKcu) hCcpos.le
      linarith
    obtain ⟨q, N', hq1, hqle, hN'1, hN'le, hN'lb, hA1⟩ : ∃ q N' : ℕ,
        1 ≤ q ∧ (q : ℝ) ≤ C₀ * δ⁻¹ ^ K₀ ∧ 1 ≤ N' ∧ N' ≤ N ∧ δ ^ K₀ * N ≤ C₀ * N' ∧
        δ ^ K₀ * (N : ℝ) ^ P.natDegree ≤
          C₀ * ∑' x : ℤ, ‖(N' : ℂ)⁻¹ * ∑ m ∈ Finset.Icc 1 N',
            f (x + (q : ℤ) * (m : ℤ))‖ := by
      rcases hPel' N N₀ δ f g h hN hδpos hδle hN₀hi hfs hgs hhs hfb hgb hhb hcorr with hs | hbig
      · exfalso; linarith
      · exact hbig
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
    have hcoef : ((((N' : ℝ))⁻¹ : ℝ) : ℂ) = (N' : ℂ)⁻¹ := by
      norm_num [Complex.ofReal_inv]
    let A : ℤ → ℂ := fun x => ((((N' : ℝ))⁻¹ : ℝ) : ℂ) *
      ∑ m ∈ Finset.Icc 1 N', f (x + (q : ℤ) * (m : ℤ))
    have hAle : δ ^ u * (N : ℝ) ^ P.natDegree / C₀ ≤ ellOne A := by
      have h1 : δ ^ u * (N : ℝ) ^ P.natDegree ≤ δ ^ K₀ * (N : ℝ) ^ P.natDegree :=
        mul_le_mul_of_nonneg_right hδu_le (by positivity)
      have h3 : (∑' x : ℤ, ‖A x‖)
          = ∑' x : ℤ, ‖(N' : ℂ)⁻¹ * ∑ m ∈ Finset.Icc 1 N',
              f (x + (q : ℤ) * (m : ℤ))‖ := by
        refine tsum_congr fun x => ?_
        change ‖((((N' : ℝ))⁻¹ : ℝ) : ℂ) * ∑ m ∈ Finset.Icc 1 N',
          f (x + (q : ℤ) * (m : ℤ))‖ = _
        rw [hcoef]
      have h2 : δ ^ K₀ * (N : ℝ) ^ P.natDegree ≤ C₀ * ellOne A := by
        rw [ellOne, h3]; exact hA1
      rw [div_le_iff₀ hC₀pos]; linarith
    let M : ℕ := N₀ + q * N'
    have hMcast : (M : ℝ) = (N₀ : ℝ) + (q : ℝ) * (N' : ℝ) := by
      change ((N₀ + q * N' : ℕ) : ℝ) = _
      push_cast; ring
    have hMd : 2 * (M : ℝ) + 1 ≤ K' * (δ⁻¹) ^ u * (N : ℝ) ^ P.natDegree := by
      have hd1 : (1 : ℝ) ≤ (N : ℝ) ^ P.natDegree := one_le_pow₀ (by exact_mod_cast hN)
      have hNd : (N : ℝ) ≤ (N : ℝ) ^ P.natDegree := by
        have h2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
          nlinarith [show (1:ℝ) ≤ (N:ℝ) by exact_mod_cast hN]
        have h3 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ P.natDegree :=
          pow_le_pow_right₀ (by exact_mod_cast hN) (by omega)
        linarith
      have hqN' : (q : ℝ) * (N' : ℝ) ≤ C₀ * δ⁻¹ ^ K₀ * (N : ℝ) := by
        calc (q : ℝ) * (N' : ℝ) ≤ (C₀ * δ⁻¹ ^ K₀) * (N' : ℝ) :=
              mul_le_mul_of_nonneg_right hqle (by exact_mod_cast Nat.zero_le N')
          _ ≤ (C₀ * δ⁻¹ ^ K₀) * (N : ℝ) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact_mod_cast hN'le
          _ = C₀ * δ⁻¹ ^ K₀ * (N : ℝ) := rfl
      have hinv1 : (1 : ℝ) ≤ δ⁻¹ ^ K₀ := Real.one_le_rpow hD1 hK₀pos.le
      have hkey : 2 * (M : ℝ) + 1 ≤ K' * δ⁻¹ ^ K₀ * (N : ℝ) ^ P.natDegree := by
        rw [hMcast, hK'def]
        set Dk : ℝ := δ⁻¹ ^ K₀ with hDkdef
        set Nd : ℝ := (N : ℝ) ^ P.natDegree with hNddef
        have hDk1 : 1 ≤ Dk := by rw [hDkdef]; exact hinv1
        have hDk0 : 0 ≤ Dk := by rw [hDkdef]; exact Real.rpow_nonneg hDpos.le K₀
        have hNd0 : 0 ≤ Nd := by rw [hNddef]; positivity
        have hNd1 : 1 ≤ Nd := by rw [hNddef]; exact hd1
        have hNdle : (N : ℝ) ≤ Nd := by rw [hNddef]; exact hNd
        have h1 : (N₀ : ℝ) ≤ 2 * Nd := by rw [hNddef]; exact hN₀hi
        have h2 : (q : ℝ) * (N' : ℝ) ≤ C₀ * Dk * Nd := by
          calc (q : ℝ) * (N' : ℝ) ≤ C₀ * δ⁻¹ ^ K₀ * (N : ℝ) := hqN'
            _ = C₀ * Dk * (N : ℝ) := by rw [hDkdef]
            _ ≤ C₀ * Dk * Nd := mul_le_mul_of_nonneg_left hNdle (by positivity)
        have h3 : 1 ≤ Dk * Nd := by
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ Dk * Nd := mul_le_mul hDk1 hNd1 (by norm_num) (by positivity)
        have h4b : Nd ≤ Dk * Nd := by
          have h := mul_le_mul_of_nonneg_right hDk1 hNd0
          linarith
        have hfin : 4 * Nd + 2 * (C₀ * Dk * Nd) + Dk * Nd ≤ (5 + 2 * C₀) * Dk * Nd := by
          have he : (5 + 2 * C₀) * Dk * Nd = 5 * (Dk * Nd) + 2 * (C₀ * Dk * Nd) := by ring
          rw [he]
          linarith [h4b]
        have hsum : 2 * ((N₀ : ℝ) + (q : ℝ) * (N' : ℝ)) + 1
            ≤ 4 * Nd + 2 * (C₀ * Dk * Nd) + Dk * Nd := by linarith
        linarith [hsum, hfin]
      calc 2 * (M : ℝ) + 1 ≤ K' * δ⁻¹ ^ K₀ * (N : ℝ) ^ P.natDegree := hkey
        _ ≤ K' * (δ⁻¹) ^ u * (N : ℝ) ^ P.natDegree := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left hδinv_le hK'pos.le
    have hAsupp : SupportIn A M := by
      intro x hx
      have hx' : M < x.natAbs := hx
      show ((((N' : ℝ))⁻¹ : ℝ) : ℂ) * ∑ m ∈ Finset.Icc 1 N',
        f (x + (q : ℤ) * (m : ℤ)) = 0
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun m hm => ?_)
      rw [Finset.mem_Icc] at hm
      have hfm : f (x + (q : ℤ) * (m : ℤ)) = 0 := by
        apply hfs
        have h1 : x.natAbs ≤ (x + (q : ℤ) * (m : ℤ)).natAbs + q * m := by
          have h2 := Int.natAbs_add_le (x + (q : ℤ) * (m : ℤ)) (-((q : ℤ) * (m : ℤ)))
          have h3 : x + (q : ℤ) * (m : ℤ) + -((q : ℤ) * (m : ℤ)) = x := by ring
          rw [h3] at h2
          have h4 : (-((q : ℤ) * (m : ℤ))).natAbs = q * m := by
            rw [Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
          rw [h4] at h2
          exact h2
        change N₀ + q * N' < x.natAbs at hx'
        have h5 : q * m ≤ q * N' := Nat.mul_le_mul_left q hm.2
        omega
      exact hfm
    obtain ⟨G, hGsupp, hGbd, hGpair⟩ := lipCorrelationDual A M hAsupp
    have hGsum : Summable (fun x : ℤ => ‖G x‖) := by
      refine summable_of_ne_finset_zero (s := Finset.Icc (-(M : ℤ)) (M : ℤ)) fun x hx => ?_
      have hx' : M < x.natAbs := by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hx
        rcases hx with h | h <;> omega
      rw [hGsupp x hx', norm_zero]
    have hGone : ellOne G ≤ 2 * (M : ℝ) + 1 := by
      simpa using ellOne_le_of_supportIn G M hGsupp hGbd
    -- the smoothing scale
    let mr : ℕ := u
    let ε : ℝ := min (δ ^ mr / c₁) (Cc / 2 * (δ⁻¹) ^ Kc / N)
    have hεpos : 0 < ε := by
      refine lt_min ?_ ?_
      · exact div_pos (pow_pos hδpos mr) hc₁pos
      · exact div_pos (mul_pos (by linarith [hCcpos]) (pow_pos hDpos Kc))
          (by exact_mod_cast hN)
    have hεlemr : ε ≤ δ ^ mr / c₁ := min_le_left _ _
    have hεle2 : ε ≤ Cc / 2 * (δ⁻¹) ^ Kc / N := min_le_right _ _
    have hεle1 : ε ≤ 1 := by
      refine le_trans hεlemr ?_
      rw [div_le_one hc₁pos]
      have h1 : δ ^ mr ≤ 1 := pow_le_one₀ hδpos.le hδle
      linarith
    have hε10 : ε ^ 10 ≤ δ ^ (2 * u) / (4 * C₀ * calcConst ψ * K') := by
      have h1 : ε ^ 10 ≤ (δ ^ mr / c₁) ^ 10 := pow_le_pow_left₀ hεpos.le hεlemr 10
      have h2 : (δ ^ mr / c₁) ^ 10 = δ ^ (10 * mr) / c₁ ^ 10 := by
        rw [div_pow, ← pow_mul, mul_comm]
      have h3 : δ ^ (10 * mr) ≤ δ ^ (2 * u) := by
        have := hanti (m := 2 * u) (n := 10 * mr) (by simp only [mr]; omega)
        simpa using this
      have h4 : δ ^ (2 * u) / c₁ ^ 10 ≤ δ ^ (2 * u) / (4 * C₀ * calcConst ψ * K') :=
        div_le_div_of_nonneg_left (by positivity) hc₂pos' (by simpa using hc₁big)
      calc ε ^ 10 ≤ (δ ^ mr / c₁) ^ 10 := h1
        _ = δ ^ (10 * mr) / c₁ ^ 10 := h2
        _ ≤ δ ^ (2 * u) / c₁ ^ 10 := div_le_div_of_nonneg_right h3 (by positivity)
        _ ≤ δ ^ (2 * u) / (4 * C₀ * calcConst ψ * K') := h4
    have hεN'ge : 4 * C₀ * calcConst ψ * K' * (δ ^ (2 * u))⁻¹ ≤ ε * (N' : ℝ) := by
      have hN'ge : δ ^ u * (N : ℝ) / C₀ ≤ (N' : ℝ) := by
        have h1 : δ ^ u * (N : ℝ) ≤ δ ^ K₀ * (N : ℝ) :=
          mul_le_mul_of_nonneg_right hδu_le (by positivity)
        rw [div_le_iff₀ hC₀pos]
        linarith [hN'lb]
      have hδ1 : (δ ^ (2 * u))⁻¹ ≤ δ ^ mr * δ ^ u * (δ ^ Kc)⁻¹ := by
        have hpu : 0 < δ ^ (2 * u) := pow_pos hδpos _
        have hpk : 0 < δ ^ Kc := pow_pos hδpos _
        rw [inv_le_iff_one_le_mul₀ hpu]
        rw [show (δ ^ mr * δ ^ u * (δ ^ Kc)⁻¹) * δ ^ (2 * u)
              = δ ^ (mr + u + 2 * u) / δ ^ Kc by
          rw [pow_add, pow_add, inv_eq_one_div]; ring]
        rw [one_le_div hpk]
        rw [show δ ^ (mr + u + 2 * u) = δ ^ (4 * u) by
          congr 1; simp only [mr]; omega]
        exact hanti hKc4u
      have hδ2 : (δ ^ (2 * u))⁻¹ ≤ (δ ^ Kc)⁻¹ * δ ^ u := by
        have hpu : 0 < δ ^ (2 * u) := pow_pos hδpos _
        have hpk : 0 < δ ^ Kc := pow_pos hδpos _
        rw [inv_le_iff_one_le_mul₀ hpu]
        rw [show ((δ ^ Kc)⁻¹ * δ ^ u) * δ ^ (2 * u) = δ ^ (u + 2 * u) / δ ^ Kc by
          rw [pow_add, inv_eq_one_div]; ring]
        rw [one_le_div hpk]
        rw [show δ ^ (u + 2 * u) = δ ^ (3 * u) by congr 1; omega]
        exact hanti hKc3u
      rcases le_total (δ ^ mr / c₁) (Cc / 2 * (δ⁻¹) ^ Kc / N) with hle | hle
      · have hεv : ε = δ ^ mr / c₁ := min_eq_left hle
        rw [hεv]
        have hcc : 4 * C₀ * calcConst ψ * K' ≤ Cc / (c₁ * C₀) := by
          rw [le_div_iff₀ (by positivity)]
          calc 4 * C₀ * calcConst ψ * K' * (c₁ * C₀) = c₁ * c₂ := by rw [hc₂def]; ring
            _ ≤ Cc := hCcc₁c₂
        have hstep : Cc / (c₁ * C₀) * (δ ^ mr * δ ^ u * (δ ^ Kc)⁻¹)
            ≤ (δ ^ mr / c₁) * (δ ^ u * (N : ℝ) / C₀) := by
          have h1 : δ ^ u * (Cc * (δ⁻¹) ^ Kc) / C₀ ≤ δ ^ u * (N : ℝ) / C₀ := by
            apply div_le_div_of_nonneg_right _ hC₀pos.le
            exact mul_le_mul_of_nonneg_left hcaseA.le (by positivity)
          calc Cc / (c₁ * C₀) * (δ ^ mr * δ ^ u * (δ ^ Kc)⁻¹)
              = (δ ^ mr / c₁) * (δ ^ u * (Cc * (δ⁻¹) ^ Kc) / C₀) := by
                rw [inv_pow]; field_simp; try ring
            _ ≤ (δ ^ mr / c₁) * (δ ^ u * (N : ℝ) / C₀) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
        calc 4 * C₀ * calcConst ψ * K' * (δ ^ (2 * u))⁻¹
            ≤ Cc / (c₁ * C₀) * (δ ^ mr * δ ^ u * (δ ^ Kc)⁻¹) :=
              mul_le_mul hcc hδ1 (by positivity) (by positivity)
          _ ≤ (δ ^ mr / c₁) * (δ ^ u * (N : ℝ) / C₀) := hstep
          _ ≤ (δ ^ mr / c₁) * (N' : ℝ) := mul_le_mul_of_nonneg_left hN'ge (by positivity)
      · have hεv : ε = Cc / 2 * (δ⁻¹) ^ Kc / N := min_eq_right hle
        rw [hεv]
        have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
        have hcc2 : 4 * C₀ * calcConst ψ * K' ≤ Cc / (2 * C₀) := by
          rw [le_div_iff₀ (by positivity)]
          calc 4 * C₀ * calcConst ψ * K' * (2 * C₀) = 2 * c₂ := by rw [hc₂def]; ring
            _ ≤ Cc := hCc2c₂
        have hstep : 4 * C₀ * calcConst ψ * K' * (δ ^ (2 * u))⁻¹
            ≤ Cc / 2 * (δ⁻¹) ^ Kc / N * (δ ^ u * (N : ℝ) / C₀) := by
          have h1 : (δ ^ (2 * u))⁻¹ ≤ (δ⁻¹) ^ Kc * δ ^ u := by
            rw [inv_pow]; exact hδ2
          have h2 : Cc / (2 * C₀) * (δ ^ (2 * u))⁻¹
              ≤ Cc / 2 * (δ⁻¹) ^ Kc / N * (δ ^ u * (N : ℝ) / C₀) := by
            have hrw : Cc / 2 * (δ⁻¹) ^ Kc / N * (δ ^ u * (N : ℝ) / C₀)
                = Cc / (2 * C₀) * ((δ⁻¹) ^ Kc * δ ^ u) := by
              field_simp; try ring
            rw [hrw]
            exact mul_le_mul_of_nonneg_left h1 (by positivity)
          calc 4 * C₀ * calcConst ψ * K' * (δ ^ (2 * u))⁻¹
              ≤ Cc / (2 * C₀) * (δ ^ (2 * u))⁻¹ :=
                mul_le_mul_of_nonneg_right hcc2 (by positivity)
            _ ≤ Cc / 2 * (δ⁻¹) ^ Kc / N * (δ ^ u * (N : ℝ) / C₀) := h2
        calc 4 * C₀ * calcConst ψ * K' * (δ ^ (2 * u))⁻¹
            ≤ Cc / 2 * (δ⁻¹) ^ Kc / N * (δ ^ u * (N : ℝ) / C₀) := hstep
          _ ≤ Cc / 2 * (δ⁻¹) ^ Kc / N * (N' : ℝ) := mul_le_mul_of_nonneg_left hN'ge (by positivity)
    have hεN'inv : (ε * (N' : ℝ))⁻¹ ≤ δ ^ (2 * u) / (4 * C₀ * calcConst ψ * K') := by
      have hXpos : 0 < δ ^ (2 * u) / (4 * C₀ * calcConst ψ * K') :=
        div_pos (pow_pos hδpos _) hfour
      have h1 : (δ ^ (2 * u) / (4 * C₀ * calcConst ψ * K'))⁻¹ ≤ ε * (N' : ℝ) := by
        rw [inv_div, div_eq_mul_inv]
        exact hεN'ge
      have h2 : 0 < ε * (N' : ℝ) := mul_pos hεpos (by exact_mod_cast hN'1)
      calc (ε * (N' : ℝ))⁻¹
          ≤ ((δ ^ (2 * u) / (4 * C₀ * calcConst ψ * K'))⁻¹)⁻¹ :=
            (inv_le_inv₀ h2 (inv_pos.mpr hXpos)).mpr h1
        _ = δ ^ (2 * u) / (4 * C₀ * calcConst ψ * K') := inv_inv _
    -- the smoothed progression and the weighted dual function
    let w : ℤ → ℂ := lipWeight ψ ε N'
    let F : ℤ → ℂ := smoothOp w G (q : ℤ)
    have hwsum : Summable (fun m : ℤ => ‖w m‖) := lipWeightSummable ψ hεpos hεle1 hN'1
    have hFbound := lipSmoothOpTsumLe hwsum hGsum (q : ℤ)
    have hFone : (∑' x : ℤ, ‖F x‖) ≤ Kw * (2 * (M : ℝ) + 1) := by
      have h2 : (∑' m : ℤ, ‖w m‖) ≤ Kw := hKw hεpos hεle1 hN'1
      have h1 : (0 : ℝ) ≤ ∑' x : ℤ, ‖G x‖ := tsum_nonneg fun _ => norm_nonneg _
      have h0 : (0 : ℝ) ≤ ∑' m : ℤ, ‖w m‖ := tsum_nonneg fun _ => norm_nonneg _
      calc (∑' x : ℤ, ‖F x‖) ≤ (∑' m : ℤ, ‖w m‖) * (∑' x : ℤ, ‖G x‖) := hFbound.2
        _ ≤ Kw * (∑' x : ℤ, ‖G x‖) := mul_le_mul_of_nonneg_right h2 h1
        _ ≤ Kw * (2 * (M : ℝ) + 1) := mul_le_mul_of_nonneg_left hGone hKwpos.le
    have hFsup : ∀ x : ℤ, ‖F x‖ ≤ Kw := by
      intro x
      have hsumm : Summable (fun m : ℤ => ‖w m * G (x - (q : ℤ) * m)‖) := by
        refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hwsum
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hGbd _)
      calc ‖F x‖ = ‖∑' m : ℤ, w m * G (x - (q : ℤ) * m)‖ := rfl
        _ ≤ ∑' m : ℤ, ‖w m * G (x - (q : ℤ) * m)‖ := norm_tsum_le_tsum_norm hsumm
        _ ≤ ∑' m : ℤ, ‖w m‖ := by
            refine Real.tsum_le_of_sum_le (fun m => norm_nonneg _) (fun s => ?_)
            refine le_trans (Finset.sum_le_sum (fun m _ => ?_))
              (hwsum.sum_le_tsum s (fun m _ => norm_nonneg _))
            rw [norm_mul]
            exact mul_le_of_le_one_right (norm_nonneg _) (hGbd _)
        _ ≤ Kw := hKw hεpos hεle1 hN'1
    -- the pointwise smoothing error
    have hpt : ∀ x : ℤ, ‖(∑' m : ℤ, w m * f (x + (q : ℤ) * (m : ℤ))) - A x‖
        ≤ calcConst ψ * (ε ^ 10 + (ε * (N' : ℝ))⁻¹) := by
      intro x
      have hsm : (∑' m : ℤ, w m * f (x + (q : ℤ) * (m : ℤ)))
          = ε * ∑' m : ℤ, ((N' : ℝ)⁻¹ * ∑ m' ∈ Finset.Icc 1 N',
              (ψ : ℝ → ℂ) (ε * ((m : ℝ) - (m' : ℝ)))) * f (x + (q : ℤ) * (m : ℤ)) := by
        rw [← tsum_mul_left]
        refine tsum_congr fun m => ?_
        simp only [w, lipWeight]
        ring
      rw [hsm]
      simpa only [norm_sub_rev] using
        averaging_smooth ψ hψint hεpos hεle1 hN'1 f hfb (q : ℤ) x
    -- the dual correlation lower bound
    let Ψ : ℤ → ℂ := fun x => ∑' m : ℤ, w m * f (x + (q : ℤ) * (m : ℤ))
    have hGzero : ∀ x : ℤ, x ∉ Finset.Icc (-(M : ℤ)) (M : ℤ) → G x = 0 := by
      intro x hx
      apply hGsupp
      simp only [Finset.mem_Icc, not_and_or, not_le] at hx
      rcases hx with h | h <;> omega
    have hFcorr : δ ^ u * (N : ℝ) ^ P.natDegree / (2 * C₀) ≤ ‖bilinPair f F‖ := by
      have hFpair : bilinPair f F = ∑' x : ℤ, G x * Ψ x := by
        show bilinPair f (fun y => ∑' m : ℤ, w m * G (y - (q : ℤ) * m)) = _
        exact bilinPair_smoothOp' (FinSupp.of_supportIn hfs) (FinSupp.of_supportIn hGsupp)
          (by positivity : (q : ℤ) ≠ 0) w
      have hsumm1 : Summable (fun x : ℤ => G x * A x) :=
        summable_of_ne_finset_zero fun x hx => by rw [hGzero x hx, zero_mul]
      have hsumm2 : Summable (fun x : ℤ => G x * (Ψ x - A x)) :=
        summable_of_ne_finset_zero fun x hx => by rw [hGzero x hx, zero_mul]
      have hsplit : (∑' x : ℤ, G x * Ψ x) = (∑' x : ℤ, G x * A x) + ∑' x : ℤ, G x * (Ψ x - A x) := by
        rw [← Summable.tsum_add hsumm1 hsumm2]
        exact tsum_congr fun x => by ring
      have hellA : (∑' x : ℤ, G x * A x) = (ellOne A : ℂ) := by
        have h1 : (∑' x : ℤ, G x * A x) = bilinPair A G := by
          rw [bilinPair]
          exact tsum_congr fun x => mul_comm _ _
        rw [h1, hGpair]
      have hKpt : calcConst ψ * (ε ^ 10 + (ε * (N' : ℝ))⁻¹) ≤ δ ^ (2 * u) / (2 * C₀ * K') := by
        have h5 : δ ^ (2*u) / (4 * C₀ * calcConst ψ * K') + δ ^ (2*u) / (4 * C₀ * calcConst ψ * K')
            = δ ^ (2*u) / (2 * C₀ * calcConst ψ * K') := by
          field_simp
          ring
        calc calcConst ψ * (ε ^ 10 + (ε * (N' : ℝ))⁻¹)
            ≤ calcConst ψ * (δ^(2*u)/(4*C₀*calcConst ψ*K') + δ^(2*u)/(4*C₀*calcConst ψ*K')) := by
              have h6 := hε10
              have h7 := hεN'inv
              nlinarith
          _ = δ ^ (2*u) / (2 * C₀ * K') := by
              rw [h5]
              field_simp [(calcConst_pos ψ).ne']
              try ring
      have herr : ‖∑' x : ℤ, G x * (Ψ x - A x)‖ ≤ δ ^ u * (N : ℝ) ^ P.natDegree / (2 * C₀) := by
        have hsumm3 : Summable (fun x : ℤ => ‖G x * (Ψ x - A x)‖) :=
          summable_of_ne_finset_zero fun x hx => by rw [hGzero x hx, zero_mul, norm_zero]
        have hnorm : ‖∑' x : ℤ, G x * (Ψ x - A x)‖ ≤ ∑' x : ℤ, ‖G x * (Ψ x - A x)‖ :=
          norm_tsum_le_tsum_norm (summable_of_ne_finset_zero fun x hx => by
            rw [hGzero x hx, zero_mul, norm_zero])
        have hstep : ∑' x : ℤ, ‖G x * (Ψ x - A x)‖
            ≤ ∑' x : ℤ, ‖G x‖ * (calcConst ψ * (ε ^ 10 + (ε*(N':ℝ))⁻¹)) := by
          rw [tsum_eq_sum (s := Finset.Icc (-(M : ℤ)) (M : ℤ))
                (fun x hx => by rw [hGzero x hx, zero_mul, norm_zero]),
              tsum_eq_sum (s := Finset.Icc (-(M : ℤ)) (M : ℤ))
                (fun x hx => by rw [hGzero x hx, norm_zero, zero_mul])]
          exact Finset.sum_le_sum fun x _ => by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hpt x) (norm_nonneg _)
        have hstep2 : ∑' x : ℤ, ‖G x‖ * (calcConst ψ * (ε ^ 10 + (ε*(N':ℝ))⁻¹))
            ≤ δ ^ u * (N : ℝ) ^ P.natDegree / (2 * C₀) := by
          have h2 : ∑' x : ℤ, ‖G x‖ * (calcConst ψ * (ε ^ 10 + (ε*(N':ℝ))⁻¹))
              = calcConst ψ * (ε ^ 10 + (ε*(N':ℝ))⁻¹) * ellOne G := by
            rw [ellOne, ← tsum_mul_left]
            exact tsum_congr fun x => by ring
          rw [h2]
          have hKpt0 : 0 ≤ calcConst ψ * (ε ^ 10 + (ε * (N' : ℝ))⁻¹) :=
            mul_nonneg (calcConst_pos ψ).le (by positivity)
          have h3 : calcConst ψ * (ε ^ 10 + (ε*(N':ℝ))⁻¹) * ellOne G
              ≤ calcConst ψ * (ε ^ 10 + (ε*(N':ℝ))⁻¹) * (2 * (M:ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hGone hKpt0
          refine le_trans h3 ?_
          calc calcConst ψ * (ε ^ 10 + (ε*(N':ℝ))⁻¹) * (2 * (M:ℝ) + 1)
              ≤ (δ ^ (2*u) / (2*C₀*K')) * (2 * (M:ℝ) + 1) :=
                mul_le_mul_of_nonneg_right hKpt (by positivity)
            _ ≤ (δ ^ (2*u) / (2*C₀*K')) * (K' * (δ⁻¹)^u * (N:ℝ)^P.natDegree) :=
                mul_le_mul_of_nonneg_left hMd (by positivity)
            _ = δ ^ u * (N:ℝ)^P.natDegree / (2*C₀) := by
                rw [inv_pow]
                field_simp
                ring
        exact le_trans hnorm (le_trans hstep hstep2)
      rw [hFpair, hsplit, hellA]
      have h2 : ellOne A - ‖∑' x : ℤ, G x * (Ψ x - A x)‖
          ≤ ‖(ellOne A : ℂ) + ∑' x : ℤ, G x * (Ψ x - A x)‖ := by
        have h3 : ‖(ellOne A : ℂ)‖ = ellOne A := by
          rw [Complex.norm_real, Real.norm_of_nonneg (ellOne_nonneg A)]
        have h4 := norm_add_le ((ellOne A : ℂ) + (∑' x : ℤ, G x * (Ψ x - A x)))
          (-(∑' x : ℤ, G x * (Ψ x - A x)))
        rw [add_neg_cancel_right, norm_neg] at h4
        linarith
      have h8 : δ ^ u * (N : ℝ) ^ P.natDegree / C₀
          - δ ^ u * (N : ℝ) ^ P.natDegree / (2 * C₀)
          = δ ^ u * (N : ℝ) ^ P.natDegree / (2 * C₀) := by
        field_simp
        ring
      linarith [hAle, herr, h2, h8]
    -- the dyadic scale, the torsion arcs and the Fourier support
    obtain ⟨k, hk1, hk2⟩ := lipExistsZpowTwo (div_pos hεpos hqpos)
    have hk3 : (2 : ℝ) ^ k ≤ Cc * (δ⁻¹) ^ Kc / N := by
      have hεdiv : ε / (q : ℝ) ≤ ε := by
        have hq1' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
        rw [div_le_iff₀ hqpos]
        nlinarith [hεpos.le, hq1']
      have h2 : 2 * ε ≤ Cc * (δ⁻¹) ^ Kc / N := by
        calc 2 * ε ≤ 2 * (Cc / 2 * (δ⁻¹) ^ Kc / N) := by linarith [hεle2]
          _ = Cc * (δ⁻¹) ^ Kc / N := by ring
      linarith [hk2]
    have hsupp : FourierSupportIn F
        (⋃ α ∈ (lipTorsionArcs q : Set FreqCircle), arcSet α ((2 : ℝ) ^ k)) :=
      (lipWeightFourierSupportFine (r := ε / (q : ℝ)) ψ hψsupp hεpos hεle1 hN'1 hGsum hq1 le_rfl).mono
        (fun γ hγ => by
          obtain ⟨α, hα, harc⟩ := Set.mem_iUnion₂.mp hγ
          exact Set.mem_biUnion hα (arcSet_mono_radius hk1 harc))
    have hqcard : (q : ℝ) ≤ Cc * (δ⁻¹) ^ Kc := by
      calc (q : ℝ) ≤ C₀ * δ⁻¹ ^ K₀ := hqle
        _ ≤ Cc * δ⁻¹ ^ K₀ :=
            mul_le_mul_of_nonneg_right hCcC₀ (Real.rpow_pos_of_pos hDpos K₀).le
        _ ≤ Cc * (δ⁻¹) ^ u := mul_le_mul_of_nonneg_left hδinv_le hCcpos.le
        _ ≤ Cc * (δ⁻¹) ^ Kc :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD1 hKcu) hCcpos.le
    -- the normalisation of `F`
    set lam : ℝ := Cc * (δ⁻¹) ^ Kc / (Kw * K' * (δ⁻¹) ^ u) with hlamdef
    have hlamnn : 0 ≤ lam := by rw [hlamdef]; positivity
    have hlamnorm : ‖(((lam : ℝ)) : ℂ)‖ = lam := by
      rw [Complex.norm_real, Real.norm_of_nonneg hlamnn]
    have hlamKw : lam * Kw ≤ Cc * (δ⁻¹) ^ Kc := by
      have h1 : (1 : ℝ) ≤ K' * (δ⁻¹) ^ u := by nlinarith [hK'1, hD1u, hK'pos]
      have hden : 0 < Kw * K' * (δ⁻¹) ^ u := by positivity
      have h2 : lam * Kw = Cc * (δ⁻¹) ^ Kc * Kw / (Kw * K' * (δ⁻¹) ^ u) := by
        rw [hlamdef]; field_simp; try ring
      rw [h2, div_le_iff₀ hden]
      have hCcKc : 0 ≤ Cc * (δ⁻¹) ^ Kc := by positivity
      have hmul := mul_le_mul_of_nonneg_left h1 (mul_nonneg hCcKc hKwpos.le)
      calc Cc * (δ⁻¹) ^ Kc * Kw = Cc * (δ⁻¹) ^ Kc * Kw * 1 := by ring
        _ ≤ Cc * (δ⁻¹) ^ Kc * Kw * (K' * (δ⁻¹) ^ u) := hmul
        _ = Cc * (δ⁻¹) ^ Kc * (Kw * K' * (δ⁻¹) ^ u) := by ring
    refine ⟨(((lam : ℝ)) : ℂ) • F, k, lipTorsionArcs q, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      rw [Real.rpow_natCast]
      show ‖(((lam : ℝ)) : ℂ) • F x‖ ≤ Cc * (δ⁻¹) ^ Kc
      rw [norm_smul, hlamnorm]
      calc lam * ‖F x‖ ≤ lam * Kw := mul_le_mul_of_nonneg_left (hFsup x) hlamnn
        _ ≤ Cc * (δ⁻¹) ^ Kc := hlamKw
    · show Summable fun x : ℤ => ‖(((lam : ℝ)) : ℂ) • F x‖
      have hsum' : (fun x : ℤ => ‖(((lam : ℝ)) : ℂ) • F x‖) = fun x : ℤ => lam * ‖F x‖ := by
        funext x
        rw [norm_smul, hlamnorm]
      rw [hsum']
      exact hFbound.1.mul_left lam
    · rw [Real.rpow_natCast]
      show (∑' x : ℤ, ‖(((lam : ℝ)) : ℂ) • F x‖) ≤ Cc * (δ⁻¹) ^ Kc * (N : ℝ) ^ P.natDegree
      have h1 : (∑' x : ℤ, ‖(((lam : ℝ)) : ℂ) • F x‖) = lam * ∑' x : ℤ, ‖F x‖ := by
        rw [← tsum_mul_left]
        refine tsum_congr fun x => ?_
        rw [norm_smul, hlamnorm]
      rw [h1]
      calc lam * ∑' x : ℤ, ‖F x‖ ≤ lam * (Kw * (2 * (M : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hFone hlamnn
        _ ≤ lam * (Kw * (K' * (δ⁻¹) ^ u * (N : ℝ) ^ P.natDegree)) := by
            refine mul_le_mul_of_nonneg_left ?_ hlamnn
            exact mul_le_mul_of_nonneg_left hMd hKwpos.le
        _ = Cc * (δ⁻¹) ^ Kc * (N : ℝ) ^ P.natDegree := by
            rw [hlamdef]; field_simp; try ring
    · intro ξ hξ
      rw [ZFourier_smul, hsupp ξ hξ, mul_zero]
    · rw [Real.rpow_natCast]
      show ((((lipTorsionArcs q).card : ℕ) : ℝ)) ≤ Cc * (δ⁻¹) ^ Kc
      calc ((((lipTorsionArcs q).card : ℕ) : ℝ)) ≤ (q : ℝ) := by
            exact_mod_cast lipTorsionArcs_card_le q
        _ ≤ Cc * (δ⁻¹) ^ Kc := hqcard
    · rw [Real.rpow_natCast]; exact hk3
    · rw [Real.rpow_natCast]
      show δ ^ Kc * (N : ℝ) ^ P.natDegree
        ≤ ‖bilinPair f ((((lam : ℝ)) : ℂ) • F)‖
      rw [lipBilinPairSmul, norm_mul, hlamnorm]
      have hcore : δ ^ Kc * (δ⁻¹) ^ u ≤ (δ⁻¹) ^ Kc * δ ^ u := by
        have hpu : 0 < δ ^ u := pow_pos hδpos _
        have hpk : 0 < δ ^ Kc := pow_pos hδpos _
        rw [inv_pow, inv_pow, mul_comm ((δ ^ Kc)⁻¹) (δ ^ u)]
        rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ hpu hpk]
        have hc : δ ^ (2 * Kc) ≤ δ ^ (2 * u) := hanti (by omega)
        rwa [show δ ^ (2 * Kc) = δ ^ Kc * δ ^ Kc by rw [← pow_add]; congr 1; omega,
             show δ ^ (2 * u) = δ ^ u * δ ^ u by rw [← pow_add]; congr 1; omega] at hc
      have h1 : 2 * C₀ * δ ^ Kc ≤ lam * δ ^ u := by
        have hden : 0 < Kw * K' * (δ⁻¹) ^ u := by positivity
        have h2 : lam * δ ^ u = Cc * ((δ⁻¹) ^ Kc * δ ^ u) / (Kw * K' * (δ⁻¹) ^ u) := by
          rw [hlamdef]; field_simp; try ring
        rw [h2, le_div_iff₀ hden]
        calc 2 * C₀ * δ ^ Kc * (Kw * K' * (δ⁻¹) ^ u)
            = 2 * C₀ * Kw * K' * (δ ^ Kc * (δ⁻¹) ^ u) := by ring
          _ ≤ 2 * C₀ * Kw * K' * ((δ⁻¹) ^ Kc * δ ^ u) :=
              mul_le_mul_of_nonneg_left hcore (by positivity)
          _ ≤ Cc * ((δ⁻¹) ^ Kc * δ ^ u) :=
              mul_le_mul_of_nonneg_right hCcKw (by positivity)
      calc δ ^ Kc * (N : ℝ) ^ P.natDegree
          = (2 * C₀ * δ ^ Kc) * (N : ℝ) ^ P.natDegree / (2 * C₀) := by field_simp
        _ ≤ (lam * δ ^ u) * (N : ℝ) ^ P.natDegree / (2 * C₀) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = lam * (δ ^ u * (N : ℝ) ^ P.natDegree / (2 * C₀)) := by ring
        _ ≤ lam * ‖bilinPair f F‖ := mul_le_mul_of_nonneg_left hFcorr hlamnn

end Work.KMTAreas.A4

