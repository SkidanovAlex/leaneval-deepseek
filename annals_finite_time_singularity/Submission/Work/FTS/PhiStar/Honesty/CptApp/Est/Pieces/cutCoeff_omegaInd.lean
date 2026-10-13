import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs
import Submission.Work.FTS.EllipticEst.DzIter_mul_of_radial
import Submission.Work.Coercivity.CommutZ_mult
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces.mixed_sep_product
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces.DzIter_radial_theta_indep
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces.DthIter_angular_z_indep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `Ω_n`-coefficient estimate for the cut-off product `χ_n(z)ζ_n(θ) − 1`

For `n ≥ 2` the product `chiR n z * zetaR n θ` of the two cut-offs equals `1` on the closed
rectangle `[2/n, n] × [2/n, π/2 − 2/n]`, and `Ω_n` is exactly the complement of that
rectangle.  Hence *every* mixed derivative `mixed b a (χ_n ζ_n − 1)` with `a + b ≥ 1` is
supported in `Ω_n`: on the plateau every derivative vanishes (`hpz`, `hpθ`, i.e. flatness of
the two cut-offs at the boundary of their plateau), and off `Ω_n` the estimate of
`cutCoeff_omegaInd` is an equality `0 ≤ 0`.

The pointwise estimate

  `(D_z^bD_θ^a (χ_n ζ_n − 1))² ≤ (1 + K b²)(1 + L a²) · 1_{Ω_n}`

then follows from the two uniform derivative bounds `|D_z^b χ_N| ≤ K b`, `|D_θ^a ζ_N| ≤ L a`.

The proof is in three layers.

* A *separation of variables* identity: on a product `f(z)·g(θ)` of a radial and an angular
  factor the mixed derivative splits,
  `D_z^b D_θ^a (f·g)(z,θ) = (D_z^b f)(z,θ) · (D_θ^a g)(z,θ)`
  — this is `mixed_sep_product`.
* The constant `−1` is invisible to the mixed operator as soon as `a + b ≥ 1`
  (`mixed_sub_const`), because `D_θ^r` resp. `D_z^r` kill constants for `r ≥ 1`
  (`DthIter_sub_const`, `DzIter_sub_const`).
* Each factor may be evaluated at a *fixed* dummy point (`θ = 0` resp. `z = 0`), where the
  hypotheses `hKb`, `hLb`, `hpz`, `hpθ` speak.  Outside `Ω_n` both factors vanish by
  `hpz`/`hpθ` (the trivial dummy independence `DzIter_radial_theta_indep`,
  `DthIter_angular_z_indep` moves the point), inside `Ω_n` the first is bounded by `K b`
  and the second by `L a`.

Nothing beyond elementary `deriv` calculus is used: `deriv_sub_const`, `deriv_const_mul_field`
and the definitional (eta) equality of `fun x => h x` with `h`.
-/

noncomputable section

namespace Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces

open Work.FTS.PhiStar.Honesty.CptApp

/-! ## The constant `−1` is killed by any derivative of order at least one -/

/-- `D_θ^r` of `G − c` is `D_θ^r G` for `r ≥ 1`. -/
theorem DthIter_sub_const (r : ℕ) (c : ℝ) (G : ℝ → ℝ → ℝ) (hr : 1 ≤ r) :
    Work.Spaces.DthIter r (fun z θ : ℝ => G z θ - c) = Work.Spaces.DthIter r G := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  clear hr
  induction k with
  | zero =>
      funext z θ
      show Real.sin (2 * θ) * deriv (fun θ' : ℝ => G z θ' - c) θ
        = Real.sin (2 * θ) * deriv (fun θ' : ℝ => G z θ') θ
      rw [deriv_sub_const]
  | succ k ih =>
      rw [show 1 + (k + 1) = (1 + k) + 1 from by omega]
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, ih]

/-- `D_z^r` of `G − c` is `D_z^r G` for `r ≥ 1`. -/
theorem DzIter_sub_const (r : ℕ) (c : ℝ) (G : ℝ → ℝ → ℝ) (hr : 1 ≤ r) :
    Work.Spaces.DzIter r (fun z θ : ℝ => G z θ - c) = Work.Spaces.DzIter r G := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  clear hr
  induction k with
  | zero =>
      funext z θ
      show z * deriv (fun z' : ℝ => G z' θ - c) z = z * deriv (fun z' : ℝ => G z' θ) z
      rw [deriv_sub_const]
  | succ k ih =>
      rw [show 1 + (k + 1) = (1 + k) + 1 from by omega]
      rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, ih]

/-- `mixed b a` of `F − 1` is `mixed b a F` as soon as `a + b ≥ 1`. -/
theorem mixed_sub_const (b a : ℕ) (hab : 1 ≤ a + b) (F : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed b a (fun z θ : ℝ => F z θ - 1) = Work.Spaces.mixed b a F := by
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · rw [h0]
    show Work.Spaces.DzIter b (fun z θ : ℝ => F z θ - 1) = Work.Spaces.DzIter b F
    exact DzIter_sub_const b 1 F (by omega)
  · show Work.Spaces.DzIter b (Work.Spaces.DthIter a (fun z θ : ℝ => F z θ - 1))
      = Work.Spaces.DzIter b (Work.Spaces.DthIter a F)
    rw [DthIter_sub_const a 1 F (by omega)]

/-! ## The mixed derivatives of `χ_n(z)ζ_n(θ) − 1` -/

/-- For `a + b ≥ 1` the mixed derivative of `χ_n(z)ζ_n(θ) − 1` is the product of the two
one-dimensional derivatives at the same point. -/
theorem mixed_chiR_zetaR_sub_one (n b a : ℕ) (hab : 1 ≤ a + b) (z θ : ℝ) :
    Work.Spaces.mixed b a (fun z θ : ℝ => chiR n z * zetaR n θ - 1) z θ
      = Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ
        * Work.Spaces.DthIter a (fun _ θ : ℝ => zetaR n θ) z θ := by
  rw [mixed_sub_const b a hab (fun z θ : ℝ => chiR n z * zetaR n θ)]
  exact mixed_sep_product b a (chiR n) (zetaR n) z θ

/-! ## The estimate -/

theorem cutCoeff_omegaInd (K L : ℕ → ℝ)
    (hKb : ∀ (N b : ℕ) (z θ : ℝ),
      |Work.Spaces.DzIter b (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR N z) z θ| ≤ K b)
    (hLb : ∀ (N a : ℕ) (z θ : ℝ),
      |Work.Spaces.DthIter a (fun _ θ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.zetaR N θ) z θ| ≤ L a)
    (hpz : ∀ (N b : ℕ) (z : ℝ), 2 ≤ N → 1 ≤ b → 2 / (N : ℝ) ≤ z → z ≤ (N : ℝ) →
      Work.Spaces.DzIter b (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR N z) z 0 = 0)
    (hpθ : ∀ (N a : ℕ) (θ : ℝ), 2 ≤ N → 1 ≤ a → 2 / (N : ℝ) ≤ θ →
      θ ≤ Real.pi / 2 - 2 / (N : ℝ) →
      Work.Spaces.DthIter a (fun _ θ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.zetaR N θ) 0 θ = 0)
    (n a b : ℕ) (hn : 2 ≤ n) (hab : 1 ≤ a + b) (z θ : ℝ) :
    (Work.Spaces.mixed b a
        (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
      ≤ (1 + K b ^ 2) * (1 + L a ^ 2) * Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ := by
  rw [mixed_chiR_zetaR_sub_one n b a hab z θ]
  by_cases hOm : (z, θ) ∈ Omega n
  · -- inside `Ω_n`: the two factors are bounded by `K b`, `L a`
    rw [omegaInd_eq_one_iff.mpr hOm]
    have hXb : |Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ| ≤ K b := hKb n b z θ
    have hYb : |Work.Spaces.DthIter a (fun _ θ : ℝ => zetaR n θ) z θ| ≤ L a := hLb n a z θ
    have h1 : (Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ) ^ 2 ≤ (K b) ^ 2 := by
      have hA1 : Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ ≤ K b :=
        le_trans (le_abs_self _) hXb
      have hA2 : -Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ ≤ K b :=
        le_trans (neg_le_abs _) hXb
      have hp1 : (0 : ℝ) ≤ Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ + K b := by
        linarith
      have hp2 : Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ - K b ≤ (0 : ℝ) := by
        linarith
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hp1 hp2]
    have h2 : (Work.Spaces.DthIter a (fun _ θ : ℝ => zetaR n θ) z θ) ^ 2 ≤ (L a) ^ 2 := by
      have hA1 : Work.Spaces.DthIter a (fun _ θ : ℝ => zetaR n θ) z θ ≤ L a :=
        le_trans (le_abs_self _) hYb
      have hA2 : -Work.Spaces.DthIter a (fun _ θ : ℝ => zetaR n θ) z θ ≤ L a :=
        le_trans (neg_le_abs _) hYb
      have hp1 : (0 : ℝ) ≤ Work.Spaces.DthIter a (fun _ θ : ℝ => zetaR n θ) z θ + L a := by
        linarith
      have hp2 : Work.Spaces.DthIter a (fun _ θ : ℝ => zetaR n θ) z θ - L a ≤ (0 : ℝ) := by
        linarith
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hp1 hp2]
    have h3 : (Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ) ^ 2
          * (Work.Spaces.DthIter a (fun _ θ : ℝ => zetaR n θ) z θ) ^ 2
        ≤ (K b) ^ 2 * (L a) ^ 2 :=
      mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)
    rw [mul_pow]
    nlinarith [h3, sq_nonneg (K b), sq_nonneg (L a)]
  · -- outside `Ω_n`: both factors vanish (`hpz`, `hpθ`)
    have hom0 : omegaInd n z θ = 0 := by
      unfold omegaInd
      rw [if_neg hOm]
    rw [hom0]
    have hz1 : 2 / (n : ℝ) ≤ z := not_lt.mp (fun hc => hOm (Or.inl hc))
    have hz2 : z ≤ (n : ℝ) := not_lt.mp (fun hc => hOm (Or.inr (Or.inl hc)))
    have hth1 : 2 / (n : ℝ) ≤ θ := not_lt.mp (fun hc => hOm (Or.inr (Or.inr (Or.inl hc))))
    have hth2 : θ ≤ Real.pi / 2 - 2 / (n : ℝ) :=
      not_lt.mp (fun hc => hOm (Or.inr (Or.inr (Or.inr hc))))
    have hXY : Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ
        * Work.Spaces.DthIter a (fun _ θ : ℝ => zetaR n θ) z θ = 0 := by
      rcases Nat.eq_zero_or_pos b with hb | hb
      · have ha : 1 ≤ a := by omega
        have hY0 : Work.Spaces.DthIter a (fun _ θ : ℝ => zetaR n θ) z θ = 0 := by
          rw [DthIter_angular_z_indep a (zetaR n) z θ]
          exact hpθ n a θ hn ha hth1 hth2
        rw [hb, hY0]
        simp
      · have hb1 : 1 ≤ b := hb
        have hX0 : Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ = 0 := by
          rw [DzIter_radial_theta_indep b (chiR n) z θ]
          exact hpz n b z hn hb1 hz1 hz2
        rw [hX0]
        simp
    rw [hXY]
    simp

end Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces
