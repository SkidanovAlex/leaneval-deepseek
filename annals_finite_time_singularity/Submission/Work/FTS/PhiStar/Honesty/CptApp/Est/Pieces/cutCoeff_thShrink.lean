import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs
import Submission.Work.FTS.EllipticEst.DzIter_mul_of_radial
import Submission.Work.Coercivity.CommutZ_mult

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
private lemma DthIter_sub_const (a : ℕ) (ha : 1 ≤ a) (f : ℝ → ℝ → ℝ) (c : ℝ) :
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
    rw [DthIter_sub_const a ha (fun z θ => chiR n z * zetaR n θ) 1]
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
