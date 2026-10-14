import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.R1G.DecayInZ_gA
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces.cutCoeff_thShrink =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `(χ ζ − 1)`-coefficient against the shrinking angular region

`χ = chiR n` is a function of `z` alone, `ζ = zetaR n` a function of `θ` alone, and the
coefficient is `G = fun z θ => χ z * ζ θ - 1`.  Since `a ≥ 1`, all `a` angular derivatives
kill the constant `-1`, and since `D_z^b` only differentiates the radial factor, the mixed
derivative of `G` factorises:

  `mixed b a G z θ = (D_z^b χ)(z) · (D_θ^a ζ)(θ)`,

so it is the product of a radial and an angular derivative.  The radial factor is bounded by
`K b` and the angular one by `L a`; moreover `ζ` is constant on its plateau, so on
`[2/n, π/2 - 2/n]` the angular factor vanishes by `hpθ`.  Hence the square of the mixed
derivative is bounded by `(1 + K b²)(1 + L a²)` on the shrinking region (where `thShrink = 1`)
and is `0` off it (where `thShrink = 0`).
-/

namespace Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces

/-! ## Auxiliary facts about the iterated angular operator -/

/-- `D_θ^a` of a function of `θ` alone is independent of the `z`-variable (for `a = 0` the
statement is `rfl`; each step uses that `D_θ` acts on the `θ`-slice only). -/
private lemma DthIter_thetaOnly_z_indep (a : ℕ) (g : ℝ → ℝ) :
    ∀ z θ, Work.Spaces.DthIter a (fun _ θ' : ℝ => g θ') z θ
      = Work.Spaces.DthIter a (fun _ θ' : ℝ => g θ') 0 θ := by
  induction a with
  | zero => intro z θ; rfl
  | succ a ih =>
      intro z θ
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [show (fun θ' => Work.Spaces.DthIter a (fun _ θ' : ℝ => g θ') z θ')
            = (fun θ' => Work.Spaces.DthIter a (fun _ θ' : ℝ => g θ') 0 θ')
            from funext (fun θ' => ih z θ')]

/-- For `k + 1 ≥ 1` angular derivatives, subtracting a constant from the function is
invisible to `D_θ^{k+1}`: `deriv` applied to `u - c` computes `deriv u` (`deriv_sub_const`),
and the constant disappears for good after the first differentiation. -/
private lemma DthIter_sub_const_aux (k : ℕ) (f : ℝ → ℝ → ℝ) (c : ℝ) :
    Work.Spaces.DthIter (k + 1) (fun z θ => f z θ - c) = Work.Spaces.DthIter (k + 1) f := by
  induction k with
  | zero =>
      funext z θ
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.Dth,
        Work.Spaces.pth]
      rw [deriv_sub_const]
  | succ k ih =>
      show Work.Spaces.Dth (Work.Spaces.DthIter (k + 1) (fun z θ => f z θ - c))
        = Work.Spaces.Dth (Work.Spaces.DthIter (k + 1) f)
      rw [ih]

/-- `D_θ^a` is insensitive to an additive constant, for `a ≥ 1`. -/
private lemma DthIter_sub_const_prv (a : ℕ) (ha : 1 ≤ a) (f : ℝ → ℝ → ℝ) (c : ℝ) :
    Work.Spaces.DthIter a (fun z θ => f z θ - c) = Work.Spaces.DthIter a f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  exact DthIter_sub_const_aux k f c

/-! ## The factorisation of the mixed derivative -/

/-- `D_z^b` of a function of `z` alone, in the one-variable form `rDzIter`. -/
private lemma DzIter_chi_eq (n b : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ
      = Work.FTS.EllipticEst.rDzIter b (chiR n) z := by
  have h := Work.FTS.EllipticEst.DzIter_mul_of_radial b (fun z => chiR n z)
    (fun _ => (1 : ℝ)) z θ
  rw [show (fun z θ : ℝ => chiR n z * (fun _ : ℝ => (1 : ℝ)) θ)
      = (fun z (_ : ℝ) => chiR n z) from by funext z θ; simp] at h
  simpa using h

/-! ## The requested bound -/

theorem cutCoeff_thShrink (K L : ℕ → ℝ)
    (hKb : ∀ (N b : ℕ) (z θ : ℝ),
      |Work.Spaces.DzIter b (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR N z) z θ| ≤ K b)
    (hLb : ∀ (N a : ℕ) (z θ : ℝ),
      |Work.Spaces.DthIter a (fun _ θ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.zetaR N θ) z θ| ≤ L a)
    (hpθ : ∀ (N a : ℕ) (θ : ℝ), 2 ≤ N → 1 ≤ a → 2 / (N : ℝ) ≤ θ →
      θ ≤ Real.pi / 2 - 2 / (N : ℝ) →
      Work.Spaces.DthIter a (fun _ θ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.zetaR N θ) 0 θ = 0)
    (n a b : ℕ) (hn : 2 ≤ n) (ha : 1 ≤ a) (z θ : ℝ) :
    (Work.Spaces.mixed b a
        (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
      ≤ (1 + K b ^ 2) * (1 + L a ^ 2) * Work.FTS.PhiStar.Honesty.CptApp.thShrink n θ := by
  -- `Z` is the angular factor `(D_θ^a ζ)(θ)`, evaluated at `z = 0` by `hpθ`.
  have hDth : Work.Spaces.DthIter a (fun z θ => chiR n z * zetaR n θ - 1)
      = fun z θ => chiR n z
          * (Work.Spaces.DthIter a (fun _ θ' : ℝ => zetaR n θ') 0 θ) := by
    rw [DthIter_sub_const_prv a ha (fun z θ => chiR n z * zetaR n θ) 1]
    trans fun z θ => chiR n z * (Work.Spaces.DthIter a (fun _ θ' : ℝ => zetaR n θ') z θ)
    · exact Work.Coercivity.DthIter_mulZm a (chiR n) (fun z θ => zetaR n θ)
    · funext z θ
      rw [DthIter_thetaOnly_z_indep a (zetaR n) z θ]
  -- the factorisation of the mixed derivative
  have hmixed : Work.Spaces.mixed b a (fun z θ => chiR n z * zetaR n θ - 1) z θ
      = Work.FTS.EllipticEst.rDzIter b (chiR n) z
        * (Work.Spaces.DthIter a (fun _ θ' : ℝ => zetaR n θ') 0 θ) := by
    show Work.Spaces.DzIter b
      (Work.Spaces.DthIter a (fun z θ => chiR n z * zetaR n θ - 1)) z θ = _
    rw [hDth]
    exact Work.FTS.EllipticEst.DzIter_mul_of_radial b (chiR n)
      (fun θ => Work.Spaces.DthIter a (fun _ θ' : ℝ => zetaR n θ') 0 θ) z θ
  -- the two factors are bounded by `K b` and `L a`
  have hX : |Work.FTS.EllipticEst.rDzIter b (chiR n) z| ≤ K b := by
    have h := hKb n b z θ
    rw [DzIter_chi_eq n b z θ] at h
    exact h
  have hY : |Work.Spaces.DthIter a (fun _ θ' : ℝ => zetaR n θ') 0 θ| ≤ L a := hLb n a 0 θ
  have hX2 : (Work.FTS.EllipticEst.rDzIter b (chiR n) z) ^ 2 ≤ (K b) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hX 2
  have hY2 : (Work.Spaces.DthIter a (fun _ θ' : ℝ => zetaR n θ') 0 θ) ^ 2 ≤ (L a) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hY 2
  rcases Work.FTS.PhiStar.Honesty.CptApp.thShrink_eq_zero_or_one n θ with hshr | hshr
  · -- on the angular plateau the angular factor vanishes
    have hnot : ¬(θ < 2 / (n : ℝ) ∨ Real.pi / 2 - 2 / (n : ℝ) < θ) := by
      intro hc
      have h1 : thShrink n θ = 1 := Work.FTS.PhiStar.Honesty.CptApp.thShrink_eq_one_iff.mpr hc
      rw [h1] at hshr
      norm_num at hshr
    have h1 : 2 / (n : ℝ) ≤ θ := not_lt.mp (fun hc => hnot (Or.inl hc))
    have h2 : θ ≤ Real.pi / 2 - 2 / (n : ℝ) := not_lt.mp (fun hc => hnot (Or.inr hc))
    have hY0 : Work.Spaces.DthIter a (fun _ θ' : ℝ => zetaR n θ') 0 θ = 0 :=
      hpθ n a θ hn ha h1 h2
    rw [hmixed, hshr, hY0]
    simp
  · -- on the shrinking region both factors are bounded
    rw [hmixed, hshr]
    have hsq : (Work.FTS.EllipticEst.rDzIter b (chiR n) z
        * Work.Spaces.DthIter a (fun _ θ' : ℝ => zetaR n θ') 0 θ) ^ 2
        = (Work.FTS.EllipticEst.rDzIter b (chiR n) z) ^ 2
          * (Work.Spaces.DthIter a (fun _ θ' : ℝ => zetaR n θ') 0 θ) ^ 2 := by ring
    rw [hsq]
    nlinarith [hX2, hY2, sq_nonneg (K b), sq_nonneg (L a),
      sq_nonneg (Work.FTS.EllipticEst.rDzIter b (chiR n) z),
      sq_nonneg (Work.Spaces.DthIter a (fun _ θ' : ℝ => zetaR n θ') 0 θ)]

end Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.lamDzDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp

set_option maxHeartbeats 800000

/-! ## Elementary facts about the angular cutoff `zetaR` and the weight `sinθcos²θ` -/

theorem cut01_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : cut01 t = 0 :=
  Real.smoothTransition.zero_of_nonpos ht

theorem cut01_nonneg (t : ℝ) : 0 ≤ cut01 t := Real.smoothTransition.nonneg t

theorem cut01_le_one (t : ℝ) : cut01 t ≤ 1 := Real.smoothTransition.le_one t

theorem continuous_cut01 : Continuous cut01 := Real.smoothTransition.continuous

theorem abs_cut01_le_one (t : ℝ) : |cut01 t| ≤ 1 := by
  rw [abs_of_nonneg (cut01_nonneg t)]
  exact cut01_le_one t

/-- The angular cutoff vanishes to the left of `1/n` (`n ≥ 1`). -/
theorem zetaR_eq_zero_of_le {n : ℕ} (hn : 1 ≤ n) {θ : ℝ} (hθ : θ ≤ 1 / (n : ℝ)) :
    zetaR n θ = 0 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le one_pos hn1
  have h1 : (n : ℝ) * θ ≤ 1 := by
    calc (n : ℝ) * θ ≤ (n : ℝ) * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_left hθ hnpos.le
      _ = 1 := by rw [mul_one_div, div_self (ne_of_gt hnpos)]
  rw [zetaR, cut01_eq_zero_of_nonpos (show (n : ℝ) * θ - 1 ≤ 0 by linarith), zero_mul]

/-- The angular cutoff vanishes to the right of `π/2 - 1/n` (`n ≥ 1`). -/
theorem zetaR_eq_zero_of_ge {n : ℕ} (hn : 1 ≤ n) {θ : ℝ}
    (hθ : Real.pi / 2 - 1 / (n : ℝ) ≤ θ) : zetaR n θ = 0 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le one_pos hn1
  have h1 : (n : ℝ) * (Real.pi / 2 - θ) ≤ 1 := by
    calc (n : ℝ) * (Real.pi / 2 - θ) ≤ (n : ℝ) * (1 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hnpos.le
      _ = 1 := by rw [mul_one_div, div_self (ne_of_gt hnpos)]
  rw [zetaR, cut01_eq_zero_of_nonpos (show (n : ℝ) * (Real.pi / 2 - θ) - 1 ≤ 0 by linarith),
    mul_zero]

theorem continuous_zetaR (n : ℕ) : Continuous (zetaR n) := by
  change Continuous (fun θ : ℝ =>
    cut01 ((n : ℝ) * θ - 1) * cut01 ((n : ℝ) * (Real.pi / 2 - θ) - 1))
  refine Continuous.mul (continuous_cut01.comp ?_) (continuous_cut01.comp ?_) <;> fun_prop

theorem continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  change Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
  exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)

theorem abs_sinCos2_le_one (θ : ℝ) : |Work.Elliptic.sinCos2 θ| ≤ 1 := by
  rw [Work.Elliptic.sinCos2, abs_mul]
  have h2 : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.abs_cos_le_one θ, abs_nonneg (Real.cos θ), sq_abs (Real.cos θ)]
  calc |Real.sin θ| * |Real.cos θ ^ 2| ≤ 1 * 1 :=
        mul_le_mul (Real.abs_sin_le_one θ) h2 (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]
  exact measurableSet_Icc

/-! ## A uniform bound on a closed rectangle inside the open quadrant -/

/-- On a closed rectangle `[a,b] × [c,d]` strictly inside the open quadrant, a function
continuous on the open quadrant is bounded. -/
theorem exists_bound_rect {H : ℝ → ℝ → ℝ}
    (hH : ContinuousOn (Function.uncurry H) Work.FTS.EllipticEst.Q0)
    {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : d < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, ‖H x θ‖ ≤ C := by
  have hsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := by
    rintro ⟨x, θ⟩ ⟨hx, hθ⟩
    exact Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha hx.1, lt_of_lt_of_le hc hθ.1, lt_of_le_of_lt hθ.2 hd⟩
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc.prod isCompact_Icc) (hH.mono hsub)
  refine ⟨max C 1, le_trans zero_le_one (le_max_right C 1), fun x hx θ hθ => ?_⟩
  have h := hC (x, θ) ⟨hx, hθ⟩
  rw [Function.uncurry] at h
  exact le_trans h (le_max_left _ _)

/-! ## Differentiation under the angular integral -/

/-- **Differentiation of the truncated moment under the angular integral.**  For `z > 0`,
the function `x ↦ ∫_θ zetaR n θ · D_z^m F x θ · sinθcos²θ` is differentiable at `z` with
derivative `∫_θ zetaR n θ · ∂_z(D_z^m F) z θ · sinθcos²θ`. -/
theorem hasDerivAt_lamSlice {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    {n : ℕ} (hn : 1 ≤ n) (m : ℕ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun x => ∫ θ in Work.Spaces.Iθ,
        zetaR n θ * Work.Spaces.DzIter m F x θ * Work.Elliptic.sinCos2 θ)
      (∫ θ in Work.Spaces.Iθ,
        zetaR n θ * Work.Spaces.pz (Work.Spaces.DzIter m F) z θ * Work.Elliptic.sinCos2 θ) z := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le one_pos hn1
  have hcpos : (0 : ℝ) < 1 / (n : ℝ) := one_div_pos.mpr hnpos
  have hdlt : Real.pi / 2 - 1 / (n : ℝ) < Real.pi / 2 := by linarith
  have hV : IsOpen (Set.Ioo (z / 2) (2 * z)) := isOpen_Ioo
  have hzV : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
  have hVpos : ∀ x ∈ Set.Ioo (z / 2) (2 * z), 0 < x := fun x hx => by linarith [hx.1, hz]
  -- continuity of the angular factors
  have hζc : ContinuousOn (fun p : ℝ × ℝ => zetaR n p.2) Work.FTS.EllipticEst.Q0 :=
    (continuous_zetaR n).comp_continuousOn continuousOn_snd
  have hsc : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2)
      Work.FTS.EllipticEst.Q0 :=
    continuous_sinCos2.comp_continuousOn continuousOn_snd
  have hHc : ContinuousOn (Function.uncurry (Work.Spaces.DzIter m F))
      Work.FTS.EllipticEst.Q0 := (hsm.DzIter m).continuousOn
  have hHc' : ContinuousOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.DzIter m F)))
      Work.FTS.EllipticEst.Q0 := ((hsm.DzIter m).pz).continuousOn
  have hg : ContinuousOn (Function.uncurry (fun x θ =>
      zetaR n θ * Work.Spaces.DzIter m F x θ * Work.Elliptic.sinCos2 θ))
      Work.FTS.EllipticEst.Q0 := by
    have hfun : Function.uncurry (fun x θ => zetaR n θ * Work.Spaces.DzIter m F x θ *
        Work.Elliptic.sinCos2 θ)
        = fun p : ℝ × ℝ => zetaR n p.2 * Function.uncurry (Work.Spaces.DzIter m F) p *
            Work.Elliptic.sinCos2 p.2 := by
      funext p
      rcases p with ⟨x, θ⟩
      rfl
    rw [hfun]
    exact (hζc.mul hHc).mul hsc
  have hg' : ContinuousOn (Function.uncurry (fun x θ =>
      zetaR n θ * Work.Spaces.pz (Work.Spaces.DzIter m F) x θ * Work.Elliptic.sinCos2 θ))
      Work.FTS.EllipticEst.Q0 := by
    have hfun : Function.uncurry (fun x θ => zetaR n θ *
        Work.Spaces.pz (Work.Spaces.DzIter m F) x θ * Work.Elliptic.sinCos2 θ)
        = fun p : ℝ × ℝ => zetaR n p.2 *
            Function.uncurry (Work.Spaces.pz (Work.Spaces.DzIter m F)) p *
            Work.Elliptic.sinCos2 p.2 := by
      funext p
      rcases p with ⟨x, θ⟩
      rfl
    rw [hfun]
    exact (hζc.mul hHc').mul hsc
  -- integrability of the base slice: the integrand is supported on a compact subset of
  -- `(1/n, π/2 - 1/n)`, where `D_z^m F z ·` is bounded
  obtain ⟨C1, hC1n, hC1⟩ := exists_bound_rect hHc (a := z) (b := z)
    (c := 1 / (n : ℝ)) (d := Real.pi / 2 - 1 / (n : ℝ)) hz hcpos hdlt
  have hbnd1 : ∀ θ ∈ Work.Spaces.Iθ,
      ‖zetaR n θ * Work.Spaces.DzIter m F z θ * Work.Elliptic.sinCos2 θ‖ ≤ max C1 1 := by
    intro θ _
    rcases le_or_gt θ (1 / (n : ℝ)) with h | h
    · rw [zetaR_eq_zero_of_le hn h]
      simp only [zero_mul, norm_zero]
      exact le_trans zero_le_one (le_max_right C1 1)
    rcases le_or_gt (Real.pi / 2 - 1 / (n : ℝ)) θ with h2 | h2
    · rw [zetaR_eq_zero_of_ge hn h2]
      simp only [zero_mul, norm_zero]
      exact le_trans zero_le_one (le_max_right C1 1)
    · have hθmem : θ ∈ Set.Icc (1 / (n : ℝ)) (Real.pi / 2 - 1 / (n : ℝ)) := ⟨h.le, h2.le⟩
      have h1 : ‖Work.Spaces.DzIter m F z θ‖ ≤ C1 := hC1 z (by simp) θ hθmem
      calc ‖zetaR n θ * Work.Spaces.DzIter m F z θ * Work.Elliptic.sinCos2 θ‖
          = ‖zetaR n θ‖ * ‖Work.Spaces.DzIter m F z θ‖ * ‖Work.Elliptic.sinCos2 θ‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ 1 * (max C1 1) * 1 := by
            refine mul_le_mul
              (mul_le_mul (abs_zetaR_le_one n θ) (le_trans h1 (le_max_left C1 1))
                (norm_nonneg _) (by norm_num)) (abs_sinCos2_le_one θ) (norm_nonneg _) ?_
            have hmax : (0 : ℝ) ≤ max C1 1 := le_trans zero_le_one (le_max_right C1 1)
            exact mul_nonneg zero_le_one hmax
        _ = max C1 1 := by ring
  have hint : Integrable (fun θ => zetaR n θ * Work.Spaces.DzIter m F z θ *
      Work.Elliptic.sinCos2 θ) (volume.restrict Work.Spaces.Iθ) := by
    have hfin : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
      Work.FTS_RegExport.RXT.Slots.isFiniteMeasure_restrict_Iθ
    refine MeasureTheory.Integrable.of_bound
      (Work.FTS_RegExport.RXT.Slots.aesm_slice_Q0 hg hz) (max C1 1) ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Iθ hbnd1
  -- the uniform bound on the candidate derivative over the `z`-interval
  obtain ⟨C2, hC2n, hC2⟩ := exists_bound_rect hHc' (a := z / 2) (b := 2 * z)
    (c := 1 / (n : ℝ)) (d := Real.pi / 2 - 1 / (n : ℝ)) (by linarith) hcpos hdlt
  have hbnd2 : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ∀ x ∈ Set.Ioo (z / 2) (2 * z),
        ‖zetaR n θ * Work.Spaces.pz (Work.Spaces.DzIter m F) x θ *
          Work.Elliptic.sinCos2 θ‖ ≤ max C2 1 := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Iθ (fun θ _ x hx => ?_)
    rcases le_or_gt θ (1 / (n : ℝ)) with h | h
    · rw [zetaR_eq_zero_of_le hn h]
      simp only [zero_mul, norm_zero]
      exact le_trans zero_le_one (le_max_right C2 1)
    rcases le_or_gt (Real.pi / 2 - 1 / (n : ℝ)) θ with h2 | h2
    · rw [zetaR_eq_zero_of_ge hn h2]
      simp only [zero_mul, norm_zero]
      exact le_trans zero_le_one (le_max_right C2 1)
    · have hθmem : θ ∈ Set.Icc (1 / (n : ℝ)) (Real.pi / 2 - 1 / (n : ℝ)) := ⟨h.le, h2.le⟩
      have hxmem : x ∈ Set.Icc (z / 2) (2 * z) := ⟨hx.1.le, hx.2.le⟩
      have h1 : ‖Work.Spaces.pz (Work.Spaces.DzIter m F) x θ‖ ≤ C2 := hC2 x hxmem θ hθmem
      calc ‖zetaR n θ * Work.Spaces.pz (Work.Spaces.DzIter m F) x θ *
            Work.Elliptic.sinCos2 θ‖
          = ‖zetaR n θ‖ * ‖Work.Spaces.pz (Work.Spaces.DzIter m F) x θ‖ *
              ‖Work.Elliptic.sinCos2 θ‖ := by rw [norm_mul, norm_mul]
        _ ≤ 1 * (max C2 1) * 1 := by
            refine mul_le_mul
              (mul_le_mul (abs_zetaR_le_one n θ) (le_trans h1 (le_max_left C2 1))
                (norm_nonneg _) (by norm_num)) (abs_sinCos2_le_one θ) (norm_nonneg _) ?_
            have hmax : (0 : ℝ) ≤ max C2 1 := le_trans zero_le_one (le_max_right C2 1)
            exact mul_nonneg zero_le_one hmax
        _ = max C2 1 := by ring
  -- the pointwise derivative of the slice
  have hdiff : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      HasDerivAt (fun y => zetaR n θ * Work.Spaces.DzIter m F y θ * Work.Elliptic.sinCos2 θ)
        (zetaR n θ * Work.Spaces.pz (Work.Spaces.DzIter m F) x θ *
          Work.Elliptic.sinCos2 θ) x := by
    intro θ hθ x hx
    have hx0 : 0 < x := hVpos x hx
    have hd : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.DzIter m F)) (x, θ) :=
      (((hsm.DzIter m).forall 1).differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hx0, hθ.1, hθ.2⟩))
    have h1 : HasDerivAt (fun y => Work.Spaces.DzIter m F y θ)
        (Work.Spaces.pz (Work.Spaces.DzIter m F) x θ) x :=
      (Work.Spaces.differentiableAt_curry_left hd).hasDerivAt
    have h2 := (h1.mul_const (Work.Elliptic.sinCos2 θ)).const_mul (zetaR n θ)
    have heq : (fun y => zetaR n θ * Work.Spaces.DzIter m F y θ * Work.Elliptic.sinCos2 θ)
        = fun y => zetaR n θ * (Work.Spaces.DzIter m F y θ * Work.Elliptic.sinCos2 θ) := by
      funext y
      ring
    have hv : zetaR n θ * Work.Spaces.pz (Work.Spaces.DzIter m F) x θ *
          Work.Elliptic.sinCos2 θ
        = zetaR n θ *
          (Work.Spaces.pz (Work.Spaces.DzIter m F) x θ * Work.Elliptic.sinCos2 θ) := by ring
    rw [heq, hv]
    exact h2
  exact Work.FTS_RegExport.RXT.Slots.hasDerivAt_integral_Itheta_Q0
    (g := fun x θ => zetaR n θ * Work.Spaces.DzIter m F x θ * Work.Elliptic.sinCos2 θ)
    (g' := fun x θ => zetaR n θ * Work.Spaces.pz (Work.Spaces.DzIter m F) x θ *
      Work.Elliptic.sinCos2 θ)
    hV hzV hVpos hg hg' hint hbnd2 hdiff

/-! ## The main result -/

/-- The induction: `D_z^m` applied to `z ↦ lam n F z` equals the angular integral of
`D_z^m F` against the cutoff. -/
theorem lamDzDeriv_aux {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    {n : ℕ} (hn : 1 ≤ n) :
    ∀ m : ℕ, ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Spaces.DzIter m (fun z _ => lam n F z) z 0
        = ∫ θ in Work.Spaces.Iθ,
            zetaR n θ * Work.Spaces.DzIter m F z θ * Work.Elliptic.sinCos2 θ := by
  intro m
  induction m with
  | zero => intro z _; rfl
  | succ m ih =>
    intro z hz
    have hstep : HasDerivAt (fun y => Work.Spaces.DzIter m (fun z _ => lam n F z) y 0)
        (∫ θ in Work.Spaces.Iθ,
          zetaR n θ * Work.Spaces.pz (Work.Spaces.DzIter m F) z θ *
            Work.Elliptic.sinCos2 θ) z :=
      (hasDerivAt_lamSlice hsm hn m hz).congr_of_eventuallyEq (by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
        exact ih y hy)
    have hL : Work.Spaces.DzIter (m + 1) (fun z _ => lam n F z) z 0
        = z * deriv (fun y => Work.Spaces.DzIter m (fun z _ => lam n F z) y 0) z := rfl
    have hDz : ∀ θ : ℝ, Work.Spaces.DzIter (m + 1) F z θ
        = z * Work.Spaces.pz (Work.Spaces.DzIter m F) z θ := fun θ => rfl
    rw [hL, hstep.deriv]
    rw [← MeasureTheory.integral_const_mul]
    congr 1 with θ
    simp only [hDz]
    ring

theorem lamDzDeriv {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F) (k n : ℕ)
    (hn : 1 ≤ n) :
    ∀ m : ℕ, m ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Spaces.DzIter m (fun z _ => Work.FTS.PhiStar.Honesty.CptApp.lam n F z) z 0
        = MeasureTheory.integral
            (MeasureTheory.Measure.restrict MeasureTheory.volume Work.Spaces.Iθ)
            (fun θ => Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ
              * Work.Spaces.DzIter m F z θ * Work.Elliptic.sinCos2 θ) := by
  intro m _ z hz
  exact lamDzDeriv_aux hsm hn m z hz

end Work.FTS.PhiStar.Honesty.CptApp
end
end
