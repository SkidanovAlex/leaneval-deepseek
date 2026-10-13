import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The iterated angular derivative of `sin²θ`

`D_θ f = sin(2θ) ∂_θ f`, and `D_θ (sin²θ) = sin(2θ)²`.  Since `D_θ = sin(2θ) · ∂_θ` is a
derivation, every iterate of `sin²` is of the form

`D_θ^r (sin²) (θ) = sin(2θ)² · P_r(cos 2θ)`      (`r ≥ 1`),

where `P_r` is the polynomial produced by the recursion

`P_1 = 1`,   `P_{r+1} = 4 X P_r - 2 (1 - X²) P_r'`.

Indeed, for `G_p(θ) = sin(2θ)² · p(cos 2θ)` one computes
`Lop (G_p) = G_{4Xp - 2(1-X²)p'}` (`Lop u θ = sin(2θ) u'(θ)` is the one-variable action of
`D_θ`), so the identity follows by induction.  The bound `|P_r(c)| ≤ ∑ |coeff|` for
`|c| ≤ 1` converts this into the uniform estimate
`|D_θ^r (sin²) (θ)| ≤ Ksin r · sin(2θ)²` for every `θ`, which is what the transport
estimates of `IP4` need. -/

noncomputable section

/-- The auxiliary function `θ ↦ sin(2θ)² · p(cos 2θ)` attached to a polynomial `p`. -/
private def Gfun (p : Polynomial ℝ) : ℝ → ℝ :=
  fun θ => (Real.sin (2 * θ)) ^ 2 * p.eval (Real.cos (2 * θ))

/-- One step of the coefficient recursion `p ↦ 4X p - 2(1 - X²) p'`. -/
private def Pstep (p : Polynomial ℝ) : Polynomial ℝ :=
  4 * Polynomial.X * p - 2 * (1 - Polynomial.X ^ 2) * Polynomial.derivative p

/-- The sequence of polynomials `P_1 = 1`, `P_{r+1} = Pstep P_r` (i.e. `Pseq (r+1)` is the
`r`-fold iterate of `Pstep` applied to `1`). -/
private def Pseq : ℕ → Polynomial ℝ
  | 0 => 0
  | (n + 1) => (Pstep^[n]) 1

private lemma Pseq_succ (n : ℕ) : Pseq (n + 2) = Pstep (Pseq (n + 1)) := by
  show (Pstep^[n + 1]) 1 = Pstep ((Pstep^[n]) 1)
  rw [Function.iterate_succ_apply']

/-- The derivative of `Gfun p`: `∂_θ (sin(2θ)² p(cos 2θ)) = 4 s c p(c) - 2 s³ p'(c)`. -/
private lemma deriv_Gfun (p : Polynomial ℝ) (θ : ℝ) :
    deriv (Gfun p) θ
      = 4 * Real.sin (2 * θ) * Real.cos (2 * θ) * p.eval (Real.cos (2 * θ))
        - 2 * (Real.sin (2 * θ)) ^ 3
            * (Polynomial.derivative p).eval (Real.cos (2 * θ)) := by
  have h1 : HasDerivAt (fun θ : ℝ => 2 * θ) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hs : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (Real.cos (2 * θ) * 2) θ := by
    simpa [Function.comp_def] using (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  have hs2 : HasDerivAt (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2)
      (4 * Real.sin (2 * θ) * Real.cos (2 * θ)) θ := by
    have h := hs.pow 2
    have h2 : ((2 : ℕ) : ℝ) * Real.sin (2 * θ) ^ (2 - 1) * (Real.cos (2 * θ) * 2)
        = 4 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
      simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
      ring
    rw [h2] at h
    convert h using 1
  have hc : HasDerivAt (fun θ : ℝ => Real.cos (2 * θ)) (-Real.sin (2 * θ) * 2) θ := by
    simpa [Function.comp_def] using (Real.hasDerivAt_cos (2 * θ)).comp θ h1
  have hpc : HasDerivAt (fun θ : ℝ => p.eval (Real.cos (2 * θ)))
      ((Polynomial.derivative p).eval (Real.cos (2 * θ)) * (-Real.sin (2 * θ) * 2)) θ := by
    have hp : HasDerivAt (fun x : ℝ => p.eval x)
        ((Polynomial.derivative p).eval (Real.cos (2 * θ))) (Real.cos (2 * θ)) :=
      Polynomial.hasDerivAt p (Real.cos (2 * θ))
    simpa [Function.comp_def] using hp.comp θ hc
  have hprod : HasDerivAt (Gfun p)
      (4 * Real.sin (2 * θ) * Real.cos (2 * θ) * p.eval (Real.cos (2 * θ))
        - 2 * (Real.sin (2 * θ)) ^ 3
            * (Polynomial.derivative p).eval (Real.cos (2 * θ))) θ := by
    have h := hs2.mul hpc
    convert h using 1
    · funext θ; simp [Gfun]
    · ring_nf
  exact hprod.deriv

/-- The one-variable action of `D_θ` on `Gfun p` is `Gfun (Pstep p)`. -/
private lemma Lop_Gfun (p : Polynomial ℝ) :
    Work.Spaces.Lop (Gfun p) = Gfun (Pstep p) := by
  funext θ
  change Real.sin (2 * θ) * deriv (Gfun p) θ
    = (Real.sin (2 * θ)) ^ 2 * (Pstep p).eval (Real.cos (2 * θ))
  have hev : (Pstep p).eval (Real.cos (2 * θ))
      = 4 * Real.cos (2 * θ) * p.eval (Real.cos (2 * θ))
        - 2 * (1 - (Real.cos (2 * θ)) ^ 2)
            * (Polynomial.derivative p).eval (Real.cos (2 * θ)) := by
    simp [Pstep, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow]
  have hcs : (Real.cos (2 * θ)) ^ 2 = 1 - (Real.sin (2 * θ)) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (2 * θ); linarith
  rw [hev, hcs, deriv_Gfun]
  ring_nf

/-- Iterating: `Lop^n (Gfun p) = Gfun (Pstep^n p)`. -/
private lemma Lop_iterate_Gfun (p : Polynomial ℝ) (n : ℕ) :
    (Work.Spaces.Lop^[n]) (Gfun p) = Gfun ((Pstep^[n]) p) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Lop_Gfun, Function.iterate_succ_apply']

/-- `Lop (sin²) = Gfun 1 = sin(2θ)²`. -/
private lemma Lop_sin_sq : Work.Spaces.Lop (fun θ : ℝ => Real.sin θ ^ 2) = Gfun 1 := by
  funext θ
  change Real.sin (2 * θ) * deriv (fun θ : ℝ => Real.sin θ ^ 2) θ
    = (Real.sin (2 * θ)) ^ 2 * (1 : Polynomial ℝ).eval (Real.cos (2 * θ))
  have hd : deriv (fun θ : ℝ => Real.sin θ ^ 2) θ = Real.sin (2 * θ) := by
    have h := (Real.hasDerivAt_sin θ).pow 2
    have h2 : ((2 : ℕ) : ℝ) * Real.sin θ ^ (2 - 1) * Real.cos θ = Real.sin (2 * θ) := by
      rw [Real.sin_two_mul]
      simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    rw [h2] at h
    convert h.deriv using 1
  rw [hd, Polynomial.eval_one, mul_one]
  ring

/-- **The explicit formula.**  For `r ≥ 1` and every `θ`,
`D_θ^r (sin²)(θ) = sin(2θ)² · P_r(cos 2θ)`. -/
private theorem Lop_iterate_sin_sq (r : ℕ) (hr : 1 ≤ r) :
    (Work.Spaces.Lop^[r]) (fun θ => Real.sin θ ^ 2) = Gfun (Pseq r) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  rw [Function.iterate_succ_apply, Lop_sin_sq]
  exact Lop_iterate_Gfun 1 n

/-- The same identity for the two-variable operator `DthIter`. -/
private theorem DthIter_sin_sq (r : ℕ) (hr : 1 ≤ r) (z θ : ℝ) :
    Work.Spaces.DthIter r (fun _ θ' => Real.sin θ' ^ 2) z θ
      = (Real.sin (2 * θ)) ^ 2 * (Pseq r).eval (Real.cos (2 * θ)) := by
  have h : Work.Spaces.DthIter r (fun _ θ' => Real.sin θ' ^ 2) z θ
      = (Work.Spaces.Lop^[r] (fun θ' : ℝ => Real.sin θ' ^ 2)) θ := by
    simpa using
      congrFun (Work.Spaces.DthIter_eq_iterate_Lop r (fun _ θ' => Real.sin θ' ^ 2) z) θ
  rw [h, Lop_iterate_sin_sq r hr]
  rfl

/-- The coefficient `ℓ¹`-bound: for `|x| ≤ 1` and any polynomial `p`,
`|p x| ≤ ∑ |coeff p i|`. -/
private lemma abs_eval_le_coeff_sum (p : Polynomial ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    |p.eval x| ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| := by
  rw [Polynomial.eval_eq_sum_range]
  calc |∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i|
      ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i * x ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * |x| ^ i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [abs_mul, abs_pow]
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg x) hx)

/-- The constant of the lemma: the `ℓ¹`-norm of the coefficients of `P_r`, plus `1`. -/
private def Ksin (r : ℕ) : ℝ :=
  (∑ i ∈ Finset.range ((Pseq r).natDegree + 1), |(Pseq r).coeff i|) + 1

private lemma Ksin_pos (r : ℕ) : 0 < Ksin r := by
  have h : 0 ≤ ∑ i ∈ Finset.range ((Pseq r).natDegree + 1), |(Pseq r).coeff i| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  simp only [Ksin]
  linarith

/-- The pointwise bound of the first conjunct.  Note that no hypothesis on `θ` is needed. -/
private lemma abs_DthIter_sin_sq_le (r : ℕ) (hr : 1 ≤ r) (z θ : ℝ) :
    |Work.Spaces.DthIter r (fun _ θ' => Real.sin θ' ^ 2) z θ|
      ≤ Ksin r * (Real.sin (2 * θ)) ^ 2 := by
  rw [DthIter_sin_sq r hr z θ]
  have hc := abs_eval_le_coeff_sum (Pseq r) (Real.abs_cos_le_one (2 * θ))
  have hs2 : 0 ≤ (Real.sin (2 * θ)) ^ 2 := sq_nonneg _
  have hsum : 0 ≤ ∑ i ∈ Finset.range ((Pseq r).natDegree + 1), |(Pseq r).coeff i| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  calc |(Real.sin (2 * θ)) ^ 2 * (Pseq r).eval (Real.cos (2 * θ))|
      = (Real.sin (2 * θ)) ^ 2 * |(Pseq r).eval (Real.cos (2 * θ))| := by
        rw [abs_mul, abs_of_nonneg hs2]
    _ ≤ (Real.sin (2 * θ)) ^ 2
          * (∑ i ∈ Finset.range ((Pseq r).natDegree + 1), |(Pseq r).coeff i|) :=
        mul_le_mul_of_nonneg_left hc hs2
    _ ≤ (Real.sin (2 * θ)) ^ 2 * Ksin r := by
        refine mul_le_mul_of_nonneg_left ?_ hs2
        simp only [Ksin]
        linarith
    _ = Ksin r * (Real.sin (2 * θ)) ^ 2 := by ring

theorem fkSinPow : ∃ Ksin : ℕ → ℝ, (∀ r : ℕ, 0 < Ksin r) ∧
    (∀ (r : ℕ), 1 ≤ r → ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter r (fun _ θ' => Real.sin θ' ^ 2) z θ|
        ≤ Ksin r * (Real.sin (2 * θ)) ^ 2) ∧
    (∀ (α : ℝ), 0 < α → α ≤ 1 →
     ∀ (a r : ℕ) (ρ : ℝ → ℝ → ℝ), 1 ≤ r →
      Work.FTS.TransportS.IsLeafW α a ρ →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        ρ z θ * |Work.Spaces.DthIter r (fun _ θ' => Real.sin θ' ^ 2) z θ|
          ≤ Ksin r * Work.FTS.TransportS.leafEta z θ) := by
  refine ⟨Ksin, Ksin_pos, ?_, ?_⟩
  · intro r hr z θ hθ0 hθ1
    exact abs_DthIter_sin_sq_le r hr z θ
  · intro α hα hα1 a r ρ hr hρ z θ hz hθ0 hθ1
    have hb := abs_DthIter_sin_sq_le r hr z θ
    have hρnn : 0 ≤ ρ z θ := (Work.FTS.TransportS.IsLeafW_le α hα hρ).1 z θ hz hθ0 hθ1
    have hs_pos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ1, Real.pi_pos])
    have hs_le : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hs2le : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by
      have h := Real.abs_sin_le_one (2 * θ)
      have h2 : |Real.sin (2 * θ)| ^ 2 ≤ (1 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h 2
      rwa [sq_abs, one_pow] at h2
    -- the three leaf weights all satisfy `ρ · sin(2θ)² ≤ leafEta`
    have hρs : ρ z θ * (Real.sin (2 * θ)) ^ 2 ≤ Work.FTS.TransportS.leafEta z θ := by
      rcases hρ with rfl | rfl | ⟨ha, rfl⟩
      · -- `ρ = leafEta`
        rw [Work.FTS.TransportS.leafEta]
        exact mul_le_of_le_one_right
          (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs_pos.le _)) hs2le
      · -- `ρ = leafOne = w²`
        rw [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.leafEta]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg (Work.Spaces.w z))
        exact le_trans hs2le (Work.FTS.TransportS.one_le_rpow_neg
          Work.Spaces.eta_nonneg ⟨hθ0, hθ1⟩)
      · -- `ρ = leafGam α = w² sin(2θ)^{-γ}`
        rw [Work.FTS.TransportS.leafGam, Work.FTS.TransportS.leafEta]
        have hkey : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Real.sin (2 * θ)) ^ 2
            ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
          rw [← Real.rpow_natCast (Real.sin (2 * θ)) 2, ← Real.rpow_add hs_pos]
          have hle : -Work.Spaces.eta ≤ -(Work.Spaces.gam α) + 2 := by
            rw [Work.Spaces.gam, Work.Spaces.eta]; linarith [hα1]
          exact Real.rpow_le_rpow_of_exponent_ge hs_pos hs_le hle
        calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Real.sin (2 * θ)) ^ 2
            = (Work.Spaces.w z) ^ 2
              * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  * (Real.sin (2 * θ)) ^ 2) := by ring
          _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
              mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
    calc ρ z θ * |Work.Spaces.DthIter r (fun _ θ' => Real.sin θ' ^ 2) z θ|
        ≤ ρ z θ * (Ksin r * (Real.sin (2 * θ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hb hρnn
      _ = Ksin r * (ρ z θ * (Real.sin (2 * θ)) ^ 2) := by ring
      _ ≤ Ksin r * Work.FTS.TransportS.leafEta z θ :=
          mul_le_mul_of_nonneg_left hρs (le_of_lt (Ksin_pos r))

end

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
