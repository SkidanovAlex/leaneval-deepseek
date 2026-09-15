import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Submission.Commons.Analysis.Calculus.radial_iteratedFDeriv_bound_of_eq_zero_on_Iic
import Submission.Commons.Analysis.Calculus.iteratedDeriv_const_log

/-!
# Kohn--Nirenberg regularity of the auxiliary weight `ω₀`

We prove `‖D^a ω₀(x)‖ ≤ Creg (1 + ‖x‖²)^{(1-a)/2}` for `a ≤ 3` for the radial weight
`ω₀(x) = -χ(‖x‖) · ‖x‖ / (log (2 + ‖x‖))²`, where `χ(r) = smoothTransition (r/5 - 1)` is a
smooth cutoff which is `0` for `r ≤ 5` and `1` for `r ≥ 10`.

The file contains its whole proof chain:

* a smooth (not necessarily analytic) version of the radial Faà di Bruno decay estimate
  (`radial_le_of_decay_smooth`), obtained by combining Faà di Bruno with the scaling identity;
* the one-dimensional decay of the radial profile: for `k ≤ 3` and `r ≥ 11` the derivatives of
  `r ↦ r/(log (2+r))²` decay like `r^{1-k}`, computed by hand (the Faà di Bruno formulae for
  second and third derivatives of a composition, then Leibniz for the product with `r`);
  the compact region `1 ≤ r ≤ 11` is handled by continuity;
* the assembly of the two regions with the exponent conversion
  `‖x‖^{1-a} ≤ 2 (1+‖x‖²)^{(1-a)/2}` and `(1+‖x‖²)^{(1-a)/2} ≥ 1/122` for `‖x‖ ≤ 11`.
-/

open Set Metric Filter
open scoped Topology ContDiff

set_option autoImplicit false

namespace Commons.Analysis.Calculus

private theorem radial_le_of_decay_smooth {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [ProperSpace E] {ψ : ℝ → ℝ} {a : ℕ} {A : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hA : 0 < A)
    (hdec : ∀ k, k ≤ a → ∀ r : ℝ, 1 ≤ r → ‖iteratedFDeriv ℝ k ψ r‖ ≤ A * r ^ (1 - (k:ℝ))) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : E, 1 ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ a (fun y : E => ψ ‖y‖) x‖ ≤ K * ‖x‖ ^ (1 - (a:ℝ)) := by
  classical
  -- Bounds for the iterated derivatives of the norm on `{z | 1 ≤ ‖z‖}` (reused from the commons).
  have haux : ∀ i : ℕ, ∃ K : ℝ, 1 ≤ i → i ≤ a → ∀ x : E, 1 ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ i (fun z : E => ‖z‖) x‖ ≤ K := by
    intro i
    by_cases hi : 1 ≤ i
    · obtain ⟨K, hK⟩ := Commons.Analysis.Calculus.iteratedFDeriv_norm_bound (E := E) i hi
      exact ⟨K, fun _ _ => hK⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose Kf hKf using haux
  -- A single constant dominating all of them.
  let D : ℝ := (∑ i ∈ Finset.range (a + 1), |Kf i|) + 1
  have hDsum : 0 ≤ ∑ i ∈ Finset.range (a + 1), |Kf i| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hD1 : 1 ≤ D := by dsimp only [D]; linarith
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hDK : ∀ i, 1 ≤ i → i ≤ a → Kf i ≤ D := by
    intro i hi1 hia
    have hmem : i ∈ Finset.range (a + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hia)
    have h1 : |Kf i| ≤ ∑ j ∈ Finset.range (a + 1), |Kf j| :=
      Finset.single_le_sum (f := fun j => |Kf j|) (fun j _ => abs_nonneg _) hmem
    have h2 : Kf i ≤ |Kf i| := le_abs_self _
    dsimp only [D]; linarith
  have hDpow : ∀ i, 1 ≤ i → i ≤ a → Kf i ≤ D ^ i := by
    intro i hi1 hia
    calc Kf i ≤ D := hDK i hi1 hia
      _ = D ^ 1 := (pow_one D).symm
      _ ≤ D ^ i := pow_le_pow_right₀ hD1 hi1
  refine ⟨(a.factorial : ℝ) * A * D ^ a, ?_, ?_⟩
  · exact mul_pos (mul_pos (by exact_mod_cast Nat.factorial_pos a) hA) (pow_pos hDpos a)
  · intro x hx
    have hxpos : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
    have hxne : x ≠ 0 := by rintro rfl; norm_num at hx
    -- the normalised point `u = x / ‖x‖` on the unit sphere
    set u : E := ‖x‖⁻¹ • x with hudef
    have hu : ‖u‖ = 1 := by
      rw [hudef, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hxpos.le),
        inv_mul_cancel₀ hxpos.ne']
    -- `s = E \ {0}`, an open set on which the norm is smooth
    set s : Set E := {z : E | z ≠ 0} with hsdef
    have hsopen : IsOpen s := isOpen_ne
    have hxs : x ∈ s := by rw [hsdef]; exact hxne
    have hus : u ∈ s := by
      rw [hsdef]
      exact fun h => by rw [h, norm_zero] at hu; norm_num at hu
    have hN_smooth : ContDiffOn ℝ ∞ (fun z : E => ‖z‖) s := by
      intro z hz
      exact (contDiffAt_norm ℝ hz).contDiffWithinAt
    have hst : MapsTo (fun z : E => ‖z‖) s (Set.Ioi (0 : ℝ)) := by
      intro z hz
      simp only [mem_Ioi]
      exact norm_pos_iff.mpr hz
    -- Faà di Bruno, applied to `ψ(‖x‖·‖·‖)`: the derivatives of `t ↦ ψ(‖x‖·t)` at `1`
    -- are all bounded by `A * ‖x‖`.
    have hCbd : ∀ i, i ≤ a →
        ‖iteratedFDerivWithin ℝ i (fun t : ℝ => ψ (‖x‖ • t)) (Set.Ioi (0 : ℝ)) (‖u‖)‖
          ≤ A * ‖x‖ := by
      intro i hi
      rw [hu]
      rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Set.Ioi (0 : ℝ))
        (f := fun t : ℝ => ψ (‖x‖ • t)) i isOpen_Ioi (by norm_num)]
      have hcs : iteratedFDeriv ℝ i (fun t : ℝ => ψ (‖x‖ • t)) 1
          = ‖x‖ ^ i • iteratedFDeriv ℝ i ψ ‖x‖ := by
        have h := congr_fun (iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (f := ψ) (i := i) ‖x‖
          (hψ.of_le (by exact_mod_cast le_top))) 1
        simpa [smul_eq_mul, mul_one] using h
      rw [hcs, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hxpos.le i)]
      have hdec_i := hdec i hi ‖x‖ hx
      have hrpow : (‖x‖ : ℝ) ^ (i : ℝ) * ‖x‖ ^ (1 - (i : ℝ)) = ‖x‖ ^ (1 : ℝ) := by
        rw [← Real.rpow_add hxpos]; congr 1; ring
      calc ‖x‖ ^ i * ‖iteratedFDeriv ℝ i ψ ‖x‖‖
          = (‖x‖ : ℝ) ^ (i : ℝ) * ‖iteratedFDeriv ℝ i ψ ‖x‖‖ := by rw [Real.rpow_natCast]
        _ ≤ (‖x‖ : ℝ) ^ (i : ℝ) * (A * ‖x‖ ^ (1 - (i : ℝ))) :=
              mul_le_mul_of_nonneg_left hdec_i (by positivity)
        _ = A * ((‖x‖ : ℝ) ^ (i : ℝ) * ‖x‖ ^ (1 - (i : ℝ))) := by ring
        _ = A * ‖x‖ ^ (1 : ℝ) := by rw [hrpow]
        _ = A * ‖x‖ := by rw [Real.rpow_one]
    -- Faà di Bruno, bounds for the derivatives of the norm at `u`
    have hDbd : ∀ i, 1 ≤ i → i ≤ a →
        ‖iteratedFDerivWithin ℝ i (fun z : E => ‖z‖) s u‖ ≤ D ^ i := by
      intro i hi1 hia
      rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := s) (f := fun z : E => ‖z‖) i hsopen hus]
      exact (hKf i hi1 hia u hu.ge).trans (hDpow i hi1 hia)
    have hFB : ‖iteratedFDerivWithin ℝ a (fun z : E => ψ (‖x‖ • ‖z‖)) s u‖
        ≤ (a.factorial : ℝ) * (A * ‖x‖) * D ^ a := by
      have hφ : ContDiff ℝ ∞ (fun t : ℝ => ψ (‖x‖ • t)) := hψ.comp (contDiff_const_smul (‖x‖))
      have h := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (g := fun t : ℝ => ψ (‖x‖ • t))
        (f := fun z : E => ‖z‖) (n := a) (s := s) (t := Set.Ioi (0 : ℝ)) (x := u) (N := ∞)
        ((hφ.of_le (by exact_mod_cast le_top)).contDiffOn.mono (Set.subset_univ _)) hN_smooth (by exact_mod_cast le_top) isOpen_Ioi.uniqueDiffOn
        hsopen.uniqueDiffOn hst hus (C := A * ‖x‖) (D := D) hCbd hDbd
      simpa [Function.comp_def] using h
    -- scaling: `ψ‖·‖ = (ψ(‖x‖·‖·‖)) ∘ (‖x‖⁻¹ • ·)`
    set g : E →L[ℝ] E := ‖x‖⁻¹ • (1 : E →L[ℝ] E) with hgdef
    have hgapp : ∀ z : E, g z = ‖x‖⁻¹ • z := by intro z; rw [hgdef]; simp
    have hgx : g x = u := by rw [hgapp, hudef]
    have hFG : (fun y : E => ψ ‖y‖) = (fun z : E => ψ (‖x‖ • ‖z‖)) ∘ g := by
      funext z
      show ψ ‖z‖ = ψ (‖x‖ • ‖g z‖)
      rw [hgapp, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hxpos.le)]
      show ψ ‖z‖ = ψ (‖x‖ • (‖x‖⁻¹ * ‖z‖))
      rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hxpos.ne', one_mul]
    have hpre : g ⁻¹' s = s := by
      ext z
      simp only [mem_preimage, hsdef, Set.mem_ofPred_eq, hgapp]
      constructor
      · intro h hz
        exact h (by rw [hz, smul_zero])
      · intro h hz
        rcases smul_eq_zero.mp hz with h1 | h2
        · exact (inv_ne_zero hxpos.ne') h1
        · exact h h2
    have hGs : ContDiffOn ℝ ∞ (fun z : E => ψ (‖x‖ • ‖z‖)) s := by
      have hφ : ContDiff ℝ ∞ (fun t : ℝ => ψ (‖x‖ • t)) := hψ.comp (contDiff_const_smul (‖x‖))
      have h := hφ.contDiffOn.comp hN_smooth hst
      simpa [Function.comp_def] using h
    have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ) (g := g)
      (f := fun z : E => ψ (‖x‖ • ‖z‖)) (hf := hGs) (hs := hsopen.uniqueDiffOn)
      (h's := by rw [hpre]; exact hsopen.uniqueDiffOn) (x := x) (hx := by rw [hgx]; exact hus)
      (i := a) (hi := by exact_mod_cast le_top)
    have hscale : ‖iteratedFDerivWithin ℝ a (fun y : E => ψ ‖y‖) s x‖
        ≤ (‖x‖⁻¹) ^ a * ‖iteratedFDerivWithin ℝ a (fun z : E => ψ (‖x‖ • ‖z‖)) s u‖ := by
      rw [← hFG, hpre, hgx] at hcomp
      rw [hcomp]
      calc ‖(iteratedFDerivWithin ℝ a (fun z : E => ψ (‖x‖ • ‖z‖)) s u).compContinuousLinearMap
              (fun _ : Fin a => g)‖
          ≤ ‖iteratedFDerivWithin ℝ a (fun z : E => ψ (‖x‖ • ‖z‖)) s u‖ * ∏ _ : Fin a, ‖g‖ :=
              ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ = ‖iteratedFDerivWithin ℝ a (fun z : E => ψ (‖x‖ • ‖z‖)) s u‖ * ‖g‖ ^ a := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ ‖iteratedFDerivWithin ℝ a (fun z : E => ψ (‖x‖ • ‖z‖)) s u‖ * (‖x‖⁻¹) ^ a := by
              apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
              apply pow_le_pow_left₀ (norm_nonneg _) _
              calc ‖g‖ = ‖(‖x‖⁻¹) • (1 : E →L[ℝ] E)‖ := by rw [hgdef]
                _ = ‖‖x‖⁻¹‖ * ‖(1 : E →L[ℝ] E)‖ := norm_smul _ _
                _ ≤ ‖x‖⁻¹ * 1 := by
                      apply mul_le_mul
                      · rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hxpos.le)]
                      · exact ContinuousLinearMap.norm_id_le
                      · positivity
                      · positivity
                _ = ‖x‖⁻¹ := mul_one _
        _ = (‖x‖⁻¹) ^ a * ‖iteratedFDerivWithin ℝ a (fun z : E => ψ (‖x‖ • ‖z‖)) s u‖ := by ring
    have hpow : (‖x‖⁻¹) ^ a * ‖x‖ = ‖x‖ ^ (1 - (a : ℝ)) := by
      have h1 : (‖x‖⁻¹) ^ a = ‖x‖ ^ (-(a : ℝ)) := by
        rw [← Real.rpow_natCast (‖x‖⁻¹) a, ← Real.rpow_neg_eq_inv_rpow ‖x‖ (a : ℝ)]
      rw [h1, Real.rpow_sub hxpos 1 (a : ℝ), Real.rpow_one, div_eq_mul_inv,
        ← Real.rpow_neg hxpos.le (a : ℝ)]
      ring
    calc ‖iteratedFDeriv ℝ a (fun y : E => ψ ‖y‖) x‖
        = ‖iteratedFDerivWithin ℝ a (fun y : E => ψ ‖y‖) s x‖ := by
          rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := s) (f := fun y : E => ψ ‖y‖)
            a hsopen hxs]
      _ ≤ (‖x‖⁻¹) ^ a * ‖iteratedFDerivWithin ℝ a (fun z : E => ψ (‖x‖ • ‖z‖)) s u‖ := hscale
      _ ≤ (‖x‖⁻¹) ^ a * ((a.factorial : ℝ) * (A * ‖x‖) * D ^ a) :=
            mul_le_mul_of_nonneg_left hFB (by positivity)
      _ = ((a.factorial : ℝ) * A * D ^ a) * ‖x‖ ^ (1 - (a : ℝ)) := by
            rw [← hpow]; ring



/-- The radial profile of the auxiliary weight `ω₀`. -/

private noncomputable def phif : ℝ → ℝ := fun u => u ^ (-2 : ℤ)
private noncomputable def Ffun : ℝ → ℝ := fun r => phif (Real.log (2 + r))
private noncomputable def Gfun : ℝ → ℝ := fun r => r * Ffun r

private lemma phif_eq (u : ℝ) : phif u = (u^2)⁻¹ := by
  rw [show phif u = u ^ (-2 : ℤ) from rfl, zpow_neg]
  rfl

private lemma phif_deriv (u : ℝ) : deriv phif u = -2 * u ^ (-3 : ℤ) := by
  rw [show phif = (fun u : ℝ => u ^ (-2 : ℤ)) from rfl, ← iteratedDeriv_one,
    iteratedDeriv_eq_iterate, iter_deriv_zpow]
  simp

private lemma phif_deriv2 (u : ℝ) : iteratedDeriv 2 phif u = 6 * u ^ (-4 : ℤ) := by
  rw [show phif = (fun u : ℝ => u ^ (-2 : ℤ)) from rfl, iteratedDeriv_eq_iterate, iter_deriv_zpow]
  norm_num [Finset.prod_range_succ]

private lemma phif_deriv3 (u : ℝ) : iteratedDeriv 3 phif u = -24 * u ^ (-5 : ℤ) := by
  rw [show phif = (fun u : ℝ => u ^ (-2 : ℤ)) from rfl, iteratedDeriv_eq_iterate, iter_deriv_zpow]
  norm_num [Finset.prod_range_succ]

private lemma contDiffAt_phif {u : ℝ} (hu : u ≠ 0) (n : ℕ∞ω) : ContDiffAt ℝ n phif u := by
  have h : phif = fun u : ℝ => (u^2)⁻¹ := funext phif_eq
  rw [h]
  exact (contDiffAt_id.pow 2).inv (pow_ne_zero 2 hu)

private lemma log2_deriv (r : ℝ) : deriv (fun r : ℝ => Real.log (2 + r)) r = (r + 2) ^ (-1 : ℤ) := by
  have h : deriv (fun r : ℝ => Real.log (2 + r)) r = deriv Real.log (r + 2) := by
    have hh := congrFun (iteratedDeriv_comp_const_add 1 Real.log 2) r
    simpa [iteratedDeriv_one, add_comm] using hh
  rw [h, Real.deriv_log, zpow_neg_one]

private lemma log2_deriv2 {r : ℝ} (hr : 0 < r) :
    iteratedDeriv 2 (fun r : ℝ => Real.log (2 + r)) r = -((r + 2) ^ (-2 : ℤ)) := by
  have h : iteratedDeriv 2 (fun r : ℝ => Real.log (2 + r)) r = iteratedDeriv 2 Real.log (r + 2) := by
    have hh := congrFun (iteratedDeriv_comp_const_add 2 Real.log 2) r
    simpa [add_comm] using hh
  rw [h, show (2:ℕ) = 1 + 1 from rfl,
    Commons.Analysis.Calculus.iteratedDeriv_succ_log_real (n := 1) (by linarith : (0:ℝ) < r + 2)]
  have hexp : (-1 : ℤ) - ((1 : ℕ) : ℤ) = -2 := by norm_num
  rw [hexp]
  norm_num

private lemma log2_deriv3 {r : ℝ} (hr : 0 < r) :
    iteratedDeriv 3 (fun r : ℝ => Real.log (2 + r)) r = 2 * ((r + 2) ^ (-3 : ℤ)) := by
  have h : iteratedDeriv 3 (fun r : ℝ => Real.log (2 + r)) r = iteratedDeriv 3 Real.log (r + 2) := by
    have hh := congrFun (iteratedDeriv_comp_const_add 3 Real.log 2) r
    simpa [add_comm] using hh
  rw [h, show (3:ℕ) = 2 + 1 from rfl,
    Commons.Analysis.Calculus.iteratedDeriv_succ_log_real (n := 2) (by linarith : (0:ℝ) < r + 2)]
  have hexp : (-1 : ℤ) - ((2 : ℕ) : ℤ) = -3 := by norm_num
  rw [hexp]
  norm_num

private lemma contDiffAt_log2 {r : ℝ} (hr : 0 < r) (n : ℕ∞ω) :
    ContDiffAt ℝ n (fun r : ℝ => Real.log (2 + r)) r :=
  (Real.contDiffAt_log.mpr (by linarith : (2:ℝ) + r ≠ 0)).comp r
    (contDiffAt_const.add contDiffAt_id)

private lemma contDiffAt_Ffun {r : ℝ} (hr : 0 < r) (n : ℕ∞ω) : ContDiffAt ℝ n Ffun r := by
  have hp : ContDiffAt ℝ n phif (Real.log (2 + r)) :=
    contDiffAt_phif (ne_of_gt (Real.log_pos (by linarith : (1:ℝ) < 2 + r))) n
  exact hp.comp r (contDiffAt_log2 hr n)

private lemma zpow_neg1 (x : ℝ) : x ^ (-1:ℤ) = x⁻¹ := by simp
private lemma zpow_neg2 (x : ℝ) : x ^ (-2:ℤ) = (x^2)⁻¹ := by simp [zpow_neg]
private lemma zpow_neg3 (x : ℝ) : x ^ (-3:ℤ) = (x^3)⁻¹ := by simp [zpow_neg]
private lemma zpow_neg4 (x : ℝ) : x ^ (-4:ℤ) = (x^4)⁻¹ := by simp [zpow_neg]
private lemma zpow_neg5 (x : ℝ) : x ^ (-5:ℤ) = (x^5)⁻¹ := by simp [zpow_neg]

private lemma one_le_log_two {r : ℝ} (hr : 11 ≤ r) : (1:ℝ) ≤ Real.log (2 + r) := by
  rw [Real.le_log_iff_exp_le (by linarith : (0:ℝ) < 2 + r)]
  linarith [Real.exp_one_lt_three]

private lemma Ffun_deriv {r : ℝ} (hr : 0 < r) :
    deriv Ffun r = -(2 * ((Real.log (2 + r))^3)⁻¹ * (r + 2)⁻¹) := by
  have hcomp : Ffun = phif ∘ (fun r : ℝ => Real.log (2 + r)) := rfl
  have hLne : Real.log (2 + r) ≠ 0 := ne_of_gt (Real.log_pos (by linarith : (1:ℝ) < 2 + r))
  have hd1 : DifferentiableAt ℝ phif (Real.log (2 + r)) := by
    rw [show phif = (fun u : ℝ => u ^ (-2 : ℤ)) from rfl]
    exact (differentiableAt_zpow).mpr (Or.inl hLne)
  have hd2 : DifferentiableAt ℝ (fun r : ℝ => Real.log (2 + r)) r :=
    (Real.differentiableAt_log (by linarith : (2:ℝ) + r ≠ 0)).comp r (by fun_prop)
  rw [hcomp]
  rw [show deriv (phif ∘ fun r : ℝ => Real.log (2 + r)) r
      = deriv phif (Real.log (2 + r)) * deriv (fun r : ℝ => Real.log (2+r)) r
      from deriv_comp (hh₂ := hd1) (hh := hd2)]
  rw [phif_deriv, log2_deriv]
  simp only [zpow_neg3, zpow_neg1]
  ring

private lemma Ffun_deriv2 {r : ℝ} (hr : 0 < r) :
    iteratedDeriv 2 Ffun r =
      6 * ((Real.log (2 + r))^4)⁻¹ * ((r + 2)⁻¹)^2
      + 2 * (((Real.log (2 + r))^3)⁻¹ * ((r + 2)^2)⁻¹) := by
  have hcomp : Ffun = phif ∘ (fun r : ℝ => Real.log (2 + r)) := rfl
  rw [hcomp, iteratedDeriv_comp_two (contDiffAt_phif (by
        exact ne_of_gt (Real.log_pos (by linarith : (1:ℝ) < 2 + r))) 2) (contDiffAt_log2 hr 2),
    phif_deriv, phif_deriv2, log2_deriv, log2_deriv2 hr]
  simp only [zpow_neg1, zpow_neg2, zpow_neg3, zpow_neg4]
  ring

private lemma Ffun_deriv3 {r : ℝ} (hr : 0 < r) :
    iteratedDeriv 3 Ffun r =
      -((24 * (((Real.log (2 + r))^5)⁻¹ * ((r + 2)⁻¹)^3))
        + 18 * (((Real.log (2 + r))^4)⁻¹ * (((r + 2)^2)⁻¹ * (r + 2)⁻¹))
        + 4 * (((Real.log (2 + r))^3)⁻¹ * ((r + 2)^3)⁻¹)) := by
  have hcomp : Ffun = phif ∘ (fun r : ℝ => Real.log (2 + r)) := rfl
  rw [hcomp, iteratedDeriv_comp_three (contDiffAt_phif (by
        exact ne_of_gt (Real.log_pos (by linarith : (1:ℝ) < 2 + r))) 3) (contDiffAt_log2 hr 3),
    phif_deriv, phif_deriv2, phif_deriv3, log2_deriv, log2_deriv2 hr, log2_deriv3 hr]
  simp only [zpow_neg1, zpow_neg2, zpow_neg3, zpow_neg4, zpow_neg5]
  ring

private lemma inv_le_one_of_one_le {a : ℝ} (h : 1 ≤ a) : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h

private lemma Ffun_abs_le {r : ℝ} (hr : 11 ≤ r) : |Ffun r| ≤ 1 := by
  have hL := one_le_log_two hr
  have hF : Ffun r = ((Real.log (2 + r))^2)⁻¹ := by
    rw [show Ffun r = (Real.log (2 + r)) ^ (-2 : ℤ) from rfl, zpow_neg2]
  rw [hF, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (by linarith) 2))]
  exact inv_le_one_of_one_le (one_le_pow₀ hL)

private lemma Ffun_deriv_abs_le {r : ℝ} (hr : 11 ≤ r) : |deriv Ffun r| ≤ 2/r := by
  have hL := one_le_log_two hr
  have hLpos : (0:ℝ) < Real.log (2+r) := by linarith
  have hrp : (0:ℝ) < r := by linarith
  have h3i : (0:ℝ) ≤ ((Real.log (2+r))^3)⁻¹ := inv_nonneg.mpr (pow_nonneg hLpos.le 3)
  have h2i : (0:ℝ) ≤ (r + 2)⁻¹ := inv_nonneg.mpr (by linarith)
  have hnn : (0:ℝ) ≤ 2 * ((Real.log (2+r))^3)⁻¹ * (r + 2)⁻¹ :=
    mul_nonneg (mul_nonneg (by norm_num) h3i) h2i
  rw [Ffun_deriv hrp, show -(2 * ((Real.log (2 + r))^3)⁻¹ * (r + 2)⁻¹)
      = -(2 * ((Real.log (2+r))^3)⁻¹ * (r + 2)⁻¹) from rfl, abs_neg, abs_of_nonneg hnn]
  have hA : ((Real.log (2+r))^3)⁻¹ ≤ 1 := inv_le_one_of_one_le (one_le_pow₀ hL)
  have hB : (r+2)⁻¹ ≤ r⁻¹ := inv_anti₀ hrp (by linarith)
  calc 2 * ((Real.log (2+r))^3)⁻¹ * (r+2)⁻¹ ≤ 2 * 1 * r⁻¹ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num)) hB (inv_nonneg.mpr (by linarith))
          (by norm_num)
    _ = 2/r := by rw [mul_one, div_eq_mul_inv]

private lemma Ffun_deriv2_abs_le {r : ℝ} (hr : 11 ≤ r) : |iteratedDeriv 2 Ffun r| ≤ 8/r^2 := by
  have hL := one_le_log_two hr
  have hLpos : (0:ℝ) < Real.log (2+r) := by linarith
  have hrp : (0:ℝ) < r := by linarith
  have h4i : (0:ℝ) ≤ ((Real.log (2+r))^4)⁻¹ := inv_nonneg.mpr (pow_nonneg hLpos.le 4)
  have h3i : (0:ℝ) ≤ ((Real.log (2+r))^3)⁻¹ := inv_nonneg.mpr (pow_nonneg hLpos.le 3)
  have h2i : (0:ℝ) ≤ ((r+2)^2)⁻¹ := inv_nonneg.mpr (by positivity)
  have h1i : (0:ℝ) ≤ ((r+2)⁻¹)^2 := pow_nonneg (inv_nonneg.mpr (by linarith)) 2
  have h1 : |6 * ((Real.log (2+r))^4)⁻¹ * ((r+2)⁻¹)^2| ≤ 6 * (r^2)⁻¹ := by
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) h4i) h1i)]
    have h6 : ((Real.log (2+r))^4)⁻¹ ≤ 1 := inv_le_one_of_one_le (one_le_pow₀ hL)
    have h7 : ((r+2)⁻¹)^2 ≤ (r^2)⁻¹ := by
      rw [inv_pow]
      exact inv_anti₀ (by positivity) (by nlinarith)
    calc 6 * ((Real.log (2+r))^4)⁻¹ * ((r+2)⁻¹)^2
        = 6 * (((Real.log (2+r))^4)⁻¹ * ((r+2)⁻¹)^2) := by ring
      _ ≤ 6 * (1 * (r^2)⁻¹) := mul_le_mul_of_nonneg_left
          (mul_le_mul h6 h7 h1i (by norm_num)) (by norm_num)
      _ = 6 * (r^2)⁻¹ := by ring
  have h2 : |2 * (((Real.log (2+r))^3)⁻¹ * ((r+2)^2)⁻¹)| ≤ 2 * (r^2)⁻¹ := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (mul_nonneg h3i h2i))]
    have h6 : ((Real.log (2+r))^3)⁻¹ ≤ 1 := inv_le_one_of_one_le (one_le_pow₀ hL)
    have h7 : ((r+2)^2)⁻¹ ≤ (r^2)⁻¹ := inv_anti₀ (by positivity) (by nlinarith)
    calc 2 * (((Real.log (2+r))^3)⁻¹ * ((r+2)^2)⁻¹) ≤ 2 * (1 * (r^2)⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h6 h7 h2i (by norm_num)) (by norm_num)
      _ = 2 * (r^2)⁻¹ := by ring
  rw [Ffun_deriv2 hrp]
  calc |6 * ((Real.log (2 + r))^4)⁻¹ * ((r + 2)⁻¹)^2
        + 2 * (((Real.log (2 + r))^3)⁻¹ * ((r + 2)^2)⁻¹)|
      ≤ |6 * ((Real.log (2 + r))^4)⁻¹ * ((r + 2)⁻¹)^2|
        + |2 * (((Real.log (2 + r))^3)⁻¹ * ((r + 2)^2)⁻¹)| := abs_add_le _ _
    _ ≤ 6 * (r^2)⁻¹ + 2 * (r^2)⁻¹ := add_le_add h1 h2
    _ = 8/r^2 := by rw [← add_mul, div_eq_mul_inv]; ring

private lemma Ffun_deriv3_abs_le {r : ℝ} (hr : 11 ≤ r) : |iteratedDeriv 3 Ffun r| ≤ 46/r^3 := by
  have hL := one_le_log_two hr
  have hLpos : (0:ℝ) < Real.log (2+r) := by linarith
  have hrp : (0:ℝ) < r := by linarith
  have h5i : (0:ℝ) ≤ ((Real.log (2+r))^5)⁻¹ := inv_nonneg.mpr (pow_nonneg hLpos.le 5)
  have h4i : (0:ℝ) ≤ ((Real.log (2+r))^4)⁻¹ := inv_nonneg.mpr (pow_nonneg hLpos.le 4)
  have h3i : (0:ℝ) ≤ ((Real.log (2+r))^3)⁻¹ := inv_nonneg.mpr (pow_nonneg hLpos.le 3)
  have hi1 : (0:ℝ) ≤ (r + 2)⁻¹ := inv_nonneg.mpr (by linarith)
  have hi2 : (0:ℝ) ≤ ((r+2)^2)⁻¹ := inv_nonneg.mpr (by positivity)
  have hi3 : (0:ℝ) ≤ ((r+2)^3)⁻¹ := inv_nonneg.mpr (by positivity)
  have h13 : (0:ℝ) ≤ ((r+2)⁻¹)^3 := pow_nonneg hi1 3
  set A := 24 * (((Real.log (2+r))^5)⁻¹ * ((r+2)⁻¹)^3) with hAdef
  set B := 18 * (((Real.log (2+r))^4)⁻¹ * (((r+2)^2)⁻¹ * (r+2)⁻¹)) with hBdef
  set C := 4 * (((Real.log (2+r))^3)⁻¹ * ((r+2)^3)⁻¹) with hCdef
  have hA1 : (0:ℝ) ≤ ((Real.log (2+r))^5)⁻¹ * ((r+2)⁻¹)^3 := mul_nonneg h5i h13
  have hB1 : (0:ℝ) ≤ ((Real.log (2+r))^4)⁻¹ * (((r+2)^2)⁻¹ * (r+2)⁻¹) :=
    mul_nonneg h4i (mul_nonneg hi2 hi1)
  have hC1 : (0:ℝ) ≤ ((Real.log (2+r))^3)⁻¹ * ((r+2)^3)⁻¹ := mul_nonneg h3i hi3
  have hΑpos : (0:ℝ) ≤ A := by rw [hAdef]; exact mul_nonneg (by norm_num) hA1
  have hBpos : (0:ℝ) ≤ B := by rw [hBdef]; exact mul_nonneg (by norm_num) hB1
  have hCpos : (0:ℝ) ≤ C := by rw [hCdef]; exact mul_nonneg (by norm_num) hC1
  have hbA : A ≤ 24 * (r^3)⁻¹ := by
    rw [hAdef]
    have h6 : ((Real.log (2+r))^5)⁻¹ ≤ 1 := inv_le_one_of_one_le (one_le_pow₀ hL)
    have h7 : ((r+2)⁻¹)^3 ≤ (r^3)⁻¹ := by
      rw [inv_pow]
      exact inv_anti₀ (by positivity) (by nlinarith)
    calc 24 * (((Real.log (2+r))^5)⁻¹ * ((r+2)⁻¹)^3)
        ≤ 24 * (1 * (r^3)⁻¹) := mul_le_mul_of_nonneg_left
            (mul_le_mul h6 h7 h13 (by norm_num)) (by norm_num)
      _ = 24 * (r^3)⁻¹ := by ring
  have hbB : B ≤ 18 * (r^3)⁻¹ := by
    rw [hBdef]
    have h6 : ((Real.log (2+r))^4)⁻¹ ≤ 1 := inv_le_one_of_one_le (one_le_pow₀ hL)
    have h7 : ((r+2)^2)⁻¹ * (r+2)⁻¹ ≤ (r^3)⁻¹ := by
      have h8 : ((r+2)^2)⁻¹ * (r+2)⁻¹ = (((r+2)^2) * (r+2))⁻¹ := (mul_inv _ _).symm
      rw [h8]
      exact inv_anti₀ (by positivity) (by nlinarith)
    calc 18 * (((Real.log (2+r))^4)⁻¹ * (((r+2)^2)⁻¹ * (r+2)⁻¹))
        ≤ 18 * (1 * (r^3)⁻¹) := mul_le_mul_of_nonneg_left
            (mul_le_mul h6 h7 (mul_nonneg hi2 hi1) (by norm_num)) (by norm_num)
      _ = 18 * (r^3)⁻¹ := by ring
  have hbC : C ≤ 4 * (r^3)⁻¹ := by
    rw [hCdef]
    have h6 : ((Real.log (2+r))^3)⁻¹ ≤ 1 := inv_le_one_of_one_le (one_le_pow₀ hL)
    have h7 : ((r+2)^3)⁻¹ ≤ (r^3)⁻¹ := inv_anti₀ (by positivity) (by nlinarith)
    calc 4 * (((Real.log (2+r))^3)⁻¹ * ((r+2)^3)⁻¹) ≤ 4 * (1 * (r^3)⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h6 h7 hi3 (by norm_num)) (by norm_num)
      _ = 4 * (r^3)⁻¹ := by ring
  have hbaux : |A + B + C| ≤ 24 * (r^3)⁻¹ + (18 * (r^3)⁻¹ + 4 * (r^3)⁻¹) := by
    have hBC : |B + C| ≤ 18 * (r^3)⁻¹ + 4 * (r^3)⁻¹ := by
      calc |B + C| ≤ |B| + |C| := abs_add_le _ _
        _ = B + C := by rw [abs_of_nonneg hBpos, abs_of_nonneg hCpos]
        _ ≤ 18 * (r^3)⁻¹ + 4 * (r^3)⁻¹ := add_le_add hbB hbC
    calc |A + B + C| = |A + (B + C)| := by ring_nf
      _ ≤ |A| + |B + C| := abs_add_le _ _
      _ = A + |B + C| := by rw [abs_of_nonneg hΑpos]
      _ ≤ 24 * (r^3)⁻¹ + (18 * (r^3)⁻¹ + 4 * (r^3)⁻¹) := add_le_add hbA hBC
  rw [Ffun_deriv3 hrp]
  rw [show -((24 * (((Real.log (2 + r))^5)⁻¹ * ((r + 2)⁻¹)^3))
        + 18 * (((Real.log (2 + r))^4)⁻¹ * (((r + 2)^2)⁻¹ * (r + 2)⁻¹))
        + 4 * (((Real.log (2 + r))^3)⁻¹ * ((r + 2)^3)⁻¹)) = -(A + B + C) by
      rw [hAdef, hBdef, hCdef]]
  rw [abs_neg]
  calc |A + B + C| ≤ 24 * (r^3)⁻¹ + (18 * (r^3)⁻¹ + 4 * (r^3)⁻¹) := hbaux
    _ = 46/r^3 := by rw [div_eq_mul_inv]; ring

private noncomputable def Psi : ℝ → ℝ :=
  fun r => -(Real.smoothTransition (r / 5 - 1) * (r / (Real.log (2 + r)) ^ 2))

private lemma iteratedDeriv_id_zero (r : ℝ) : iteratedDeriv 0 (id : ℝ → ℝ) r = r := rfl

private lemma iteratedDeriv_id_one (r : ℝ) : iteratedDeriv 1 (id : ℝ → ℝ) r = 1 := by
  rw [show iteratedDeriv 1 (id : ℝ → ℝ) r = deriv (id : ℝ → ℝ) r from congrFun iteratedDeriv_one r]
  exact deriv_id r

private lemma iteratedDeriv_id_two (r : ℝ) : iteratedDeriv 2 (id : ℝ → ℝ) r = 0 := by
  rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ]
  have h : iteratedDeriv 1 (id : ℝ → ℝ) = fun _ => (1:ℝ) := by
    funext s; rw [iteratedDeriv_one]; exact deriv_id s
  rw [h]
  simp

private lemma iteratedDeriv_id_three (r : ℝ) : iteratedDeriv 3 (id : ℝ → ℝ) r = 0 := by
  rw [show (3:ℕ) = 2 + 1 from rfl, iteratedDeriv_succ]
  have h : iteratedDeriv 2 (id : ℝ → ℝ) = fun _ => (0:ℝ) := funext iteratedDeriv_id_two
  rw [h]
  simp

private lemma Gfun_iteratedDeriv_one {r : ℝ} (hr : 0 < r) :
    iteratedDeriv 1 Gfun r = r * deriv Ffun r + Ffun r := by
  have h : Gfun = id * Ffun := rfl
  rw [h, iteratedDeriv_mul (n := 1) contDiffAt_id (contDiffAt_Ffun hr 1)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_self, Nat.choose_zero_right,
    Nat.cast_one, iteratedDeriv_id_zero, iteratedDeriv_id_one]
  rw [show iteratedDeriv 1 Ffun r = deriv Ffun r from congrFun iteratedDeriv_one r,
    show iteratedDeriv 0 Ffun r = Ffun r from congrFun iteratedDeriv_zero r]
  ring

private lemma Gfun_iteratedDeriv_two {r : ℝ} (hr : 0 < r) :
    iteratedDeriv 2 Gfun r = r * iteratedDeriv 2 Ffun r + 2 * deriv Ffun r := by
  have h : Gfun = id * Ffun := rfl
  rw [h, iteratedDeriv_mul (n := 2) contDiffAt_id (contDiffAt_Ffun hr 2)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_self, Nat.choose_zero_right,
    Nat.choose_one_right, Nat.cast_ofNat, Nat.cast_one, Nat.sub_self,
    iteratedDeriv_id_zero, iteratedDeriv_id_one, iteratedDeriv_id_two]
  rw [show iteratedDeriv 1 Ffun r = deriv Ffun r from congrFun iteratedDeriv_one r,
    show iteratedDeriv 0 Ffun r = Ffun r from congrFun iteratedDeriv_zero r]
  ring

private lemma Gfun_iteratedDeriv_three {r : ℝ} (hr : 0 < r) :
    iteratedDeriv 3 Gfun r = r * iteratedDeriv 3 Ffun r + 3 * iteratedDeriv 2 Ffun r := by
  have h : Gfun = id * Ffun := rfl
  rw [h, iteratedDeriv_mul (n := 3) contDiffAt_id (contDiffAt_Ffun hr 3)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_self, Nat.choose_zero_right,
    Nat.choose_one_right, iteratedDeriv_id_zero, iteratedDeriv_id_one, iteratedDeriv_id_two,
    iteratedDeriv_id_three]
  norm_num
  try rw [show iteratedDeriv 1 Ffun r = deriv Ffun r from congrFun iteratedDeriv_one r,
    show iteratedDeriv 0 Ffun r = Ffun r from congrFun iteratedDeriv_zero r]
  try ring

private lemma Gfun_bound {r : ℝ} (hr : 11 ≤ r) {k : ℕ} (hk : k ≤ 3) :
    |iteratedDeriv k Gfun r| ≤ 70 * r ^ (1 - (k:ℝ)) := by
  have hrp : (0:ℝ) < r := by linarith
  have hF := Ffun_abs_le hr
  have hF1 := Ffun_deriv_abs_le hr
  have hF2 := Ffun_deriv2_abs_le hr
  have hF3 := Ffun_deriv3_abs_le hr
  interval_cases k
  · have hG : Gfun r = r * Ffun r := rfl
    rw [iteratedDeriv_zero, hG, abs_mul, abs_of_nonneg hrp.le]
    have h1 : r * |Ffun r| ≤ r * 1 := mul_le_mul_of_nonneg_left hF hrp.le
    rw [show (1:ℝ) - ((0:ℕ):ℝ) = 1 by norm_num, Real.rpow_one]
    linarith
  · rw [Gfun_iteratedDeriv_one hrp]
    have h1 : |r * deriv Ffun r + Ffun r| ≤ |r * deriv Ffun r| + |Ffun r| := abs_add_le _ _
    rw [abs_mul, abs_of_nonneg hrp.le] at h1
    have h2 : r * |deriv Ffun r| ≤ r * (2/r) := mul_le_mul_of_nonneg_left hF1 hrp.le
    have h3 : r * (2/r) = 2 := by field_simp
    rw [show (1:ℝ) - ((1:ℕ):ℝ) = 0 by norm_num, Real.rpow_zero]
    linarith
  · rw [Gfun_iteratedDeriv_two hrp]
    have h1 : |r * iteratedDeriv 2 Ffun r + 2 * deriv Ffun r|
        ≤ |r * iteratedDeriv 2 Ffun r| + |2 * deriv Ffun r| := abs_add_le _ _
    rw [abs_mul, abs_of_nonneg hrp.le, abs_mul,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at h1
    have h2 : r * |iteratedDeriv 2 Ffun r| ≤ r * (8/r^2) := mul_le_mul_of_nonneg_left hF2 hrp.le
    have h3 : 2 * |deriv Ffun r| ≤ 2 * (2/r) := mul_le_mul_of_nonneg_left hF1 (by norm_num)
    have h4 : r * (8/r^2) + 2 * (2/r) = 12 * r⁻¹ := by field_simp; ring
    have h5 : |r * iteratedDeriv 2 Ffun r + 2 * deriv Ffun r| ≤ 12 * r⁻¹ := by
      linarith [h1, h2, h3, h4]
    have hgoal : (70 : ℝ) * r ^ (1 - ((2:ℕ):ℝ)) = 70 * r⁻¹ := by
      rw [show (1:ℝ) - ((2:ℕ):ℝ) = -(1:ℝ) by norm_num, Real.rpow_neg_one]
    rw [hgoal]
    calc |r * iteratedDeriv 2 Ffun r + 2 * deriv Ffun r| ≤ 12 * r⁻¹ := h5
      _ ≤ 70 * r⁻¹ := by nlinarith [inv_nonneg.mpr hrp.le]
  · rw [Gfun_iteratedDeriv_three hrp]
    have h1 : |r * iteratedDeriv 3 Ffun r + 3 * iteratedDeriv 2 Ffun r|
        ≤ |r * iteratedDeriv 3 Ffun r| + |3 * iteratedDeriv 2 Ffun r| := abs_add_le _ _
    rw [abs_mul, abs_of_nonneg hrp.le, abs_mul,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)] at h1
    have h2 : r * |iteratedDeriv 3 Ffun r| ≤ r * (46/r^3) := mul_le_mul_of_nonneg_left hF3 hrp.le
    have h3 : 3 * |iteratedDeriv 2 Ffun r| ≤ 3 * (8/r^2) :=
      mul_le_mul_of_nonneg_left hF2 (by norm_num)
    have h4 : r * (46/r^3) + 3 * (8/r^2) = 70 * (r^2)⁻¹ := by field_simp; ring
    have h5 : |r * iteratedDeriv 3 Ffun r + 3 * iteratedDeriv 2 Ffun r| ≤ 70 * (r^2)⁻¹ := by
      linarith [h1, h2, h3, h4]
    have hgoal : (70 : ℝ) * r ^ (1 - ((3:ℕ):ℝ)) = 70 * (r^2)⁻¹ := by
      rw [show (1:ℝ) - ((3:ℕ):ℝ) = -(2:ℝ) by norm_num, Real.rpow_neg hrp.le]
      norm_num
    rw [hgoal]
    exact h5

private lemma Psi_eventuallyEq {r : ℝ} (hr : 11 ≤ r) : Psi =ᶠ[𝓝 r] (fun t => -Gfun t) := by
  filter_upwards [isOpen_Ioo.mem_nhds (show r ∈ Set.Ioo (10:ℝ) (r+1) by constructor <;> linarith)]
    with t ht
  have ht10 : (10:ℝ) < t := ht.1
  have htpos : (0:ℝ) < t := by linarith
  have h1 : Real.smoothTransition (t * 5⁻¹ - 1) = 1 := by
    rw [← div_eq_mul_inv]
    exact Real.smoothTransition.one_of_one_le (by linarith)
  have h2 : Ffun t = ((Real.log (2+t))^2)⁻¹ := by
    rw [show Ffun t = (Real.log (2 + t)) ^ (-2 : ℤ) from rfl, zpow_neg2]
  simp only [Psi, Gfun, h1, one_mul, h2, div_eq_mul_inv]

private lemma contDiff_Psi : ContDiff ℝ ∞ Psi := by
  rw [contDiff_iff_contDiffAt]
  intro r
  rcases lt_or_ge r 5 with h5 | h5
  · refine (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds (show r ∈ Set.Ioo (r-1) 5 by constructor <;> linarith)]
      with s hs
    show Psi s = 0
    have : s / 5 - 1 ≤ 0 := by linarith [hs.2]
    simp only [Psi, this, Real.smoothTransition.zero_of_nonpos, zero_mul, neg_zero]
  · have hlog : ContDiffAt ℝ ∞ Real.log (2 + r) := (Real.contDiffAt_log.mpr (by linarith)).of_le le_top
    have hnum : ContDiffAt ℝ ∞ (fun s : ℝ => s) r := contDiffAt_id
    have hden : ContDiffAt ℝ ∞ (fun s : ℝ => (Real.log (2 + s)) ^ 2) r :=
      ((hlog.comp r (by fun_prop)).pow 2)
    have hden0 : (Real.log (2 + r)) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith)))
    have hquot : ContDiffAt ℝ ∞ (fun s : ℝ => s / (Real.log (2 + s)) ^ 2) r :=
      hnum.div hden hden0
    have hin : ContDiffAt ℝ ∞ (fun s : ℝ => s / 5 - 1) r := by
      have h1 : ContDiffAt ℝ ∞ (fun s : ℝ => s / 5) r := contDiffAt_id.div_const 5
      exact h1.sub contDiffAt_const
    have hst : ContDiffAt ℝ ∞ (fun s : ℝ => Real.smoothTransition (s / 5 - 1)) r := by
      simpa only [Function.comp_def] using
        (Real.smoothTransition.contDiffAt (x := (r / 5 - 1)) (n := ⊤)).comp r hin
    show ContDiffAt ℝ ∞ Psi r
    exact (hst.mul hquot).neg

private lemma Psi_decay_large {r : ℝ} (hr : 11 ≤ r) {k : ℕ} (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k Psi r‖ ≤ 70 * r ^ (1 - (k:ℝ)) := by
  have heq : iteratedFDeriv ℝ k Psi r = -iteratedFDeriv ℝ k Gfun r := by
    have h1 : iteratedFDeriv ℝ k Psi r = iteratedFDeriv ℝ k (fun t => -Gfun t) r :=
      (Filter.EventuallyEq.iteratedFDeriv ℝ (Psi_eventuallyEq hr) k).eq_of_nhds
    rw [h1]
    have h2 : iteratedFDeriv ℝ k (fun t => -Gfun t) r = -iteratedFDeriv ℝ k Gfun r :=
      iteratedFDeriv_neg_apply (𝕜 := ℝ) (f := Gfun) (i := k) (x := r)
    exact h2
  rw [heq, norm_neg,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ) (f := Gfun) (n := k) (x := r),
    Real.norm_eq_abs]
  exact Gfun_bound hr hk

private lemma Psi_decay_compact :
    ∃ M : ℝ, 0 < M ∧ ∀ k : ℕ, k ≤ 3 → ∀ r ∈ Set.Icc (1:ℝ) 11,
      ‖iteratedFDeriv ℝ k Psi r‖ ≤ M := by
  have hcont : ∀ k : ℕ, Continuous (fun r : ℝ => ‖iteratedFDeriv ℝ k Psi r‖) := fun k =>
    (contDiff_Psi.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)).norm
  choose Mf hMf using fun k =>
    (isCompact_Icc (a := (1:ℝ)) (b := 11)).exists_bound_of_continuousOn (hcont k).continuousOn
  have hMf' : ∀ k : ℕ, ∀ r ∈ Set.Icc (1:ℝ) 11, ‖iteratedFDeriv ℝ k Psi r‖ ≤ Mf k := by
    intro k r hr
    have := hMf k r hr
    rwa [Real.norm_of_nonneg (norm_nonneg _)] at this
  refine ⟨max 1 (max (Mf 0) (max (Mf 1) (max (Mf 2) (Mf 3)))), by positivity, fun k hk r hr => ?_⟩
  have hle : Mf k ≤ max (Mf 0) (max (Mf 1) (max (Mf 2) (Mf 3))) := by
    interval_cases k
    · exact le_max_left (Mf 0) _
    · exact le_trans (le_max_left (Mf 1) _) (le_max_right (Mf 0) _)
    · exact le_trans (le_trans (le_max_left (Mf 2) _) (le_max_right (Mf 1) _))
        (le_max_right (Mf 0) _)
    · exact le_trans (le_trans (le_max_right (Mf 2) _) (le_max_right (Mf 1) _))
        (le_max_right (Mf 0) _)
  exact le_trans (hMf' k r hr) (le_trans hle (le_max_right _ _))

private theorem Psi_deriv_decay :
    ∃ A : ℝ, 0 < A ∧ ∀ k : ℕ, k ≤ 3 → ∀ r : ℝ, 1 ≤ r →
      ‖iteratedFDeriv ℝ k Psi r‖ ≤ A * r ^ (1 - (k : ℝ)) := by
  obtain ⟨M, hMpos, hM⟩ := Psi_decay_compact
  refine ⟨max (121 * M) 70 + 1, by positivity, fun k hk r hr1 => ?_⟩
  have hA1 : 121 * M ≤ max (121 * M) 70 := le_max_left _ _
  have hA2 : (70:ℝ) ≤ max (121 * M) 70 := le_max_right _ _
  have hApos : (0:ℝ) < max (121 * M) 70 + 1 := by positivity
  rcases lt_or_ge r 11 with hlt | hge
  · have hrI : r ∈ Set.Icc (1:ℝ) 11 := ⟨hr1, le_of_lt hlt⟩
    have h1 : ‖iteratedFDeriv ℝ k Psi r‖ ≤ M := hM k hk r hrI
    have hrpos : (0:ℝ) < r := lt_of_lt_of_le zero_lt_one hr1
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      rw [show (1:ℝ) - ((0:ℕ):ℝ) = 1 by norm_num, Real.rpow_one]
      have : M ≤ (max (121*M) 70 + 1) * r := by nlinarith [hMpos, hr1]
      linarith
    · have hz : (1:ℝ) - (k:ℝ) ≤ 0 := by
        have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hkpos
        linarith
      have hk3 : (k:ℝ) ≤ 3 := by exact_mod_cast hk
      have h2 : (11:ℝ) ^ (-(2:ℝ)) ≤ r ^ (1 - (k:ℝ)) := by
        have ha := Real.rpow_le_rpow_of_nonpos hrpos (le_of_lt hlt) hz
        have hb : (11:ℝ) ^ (-(2:ℝ)) ≤ (11:ℝ) ^ (1 - (k:ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        linarith
      have h3 : (1:ℝ)/121 = (11:ℝ) ^ (-(2:ℝ)) := by
        rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 11), show (2:ℝ) = ((2:ℕ):ℝ) by norm_num,
          Real.rpow_natCast]
        norm_num
      rw [← h3] at h2
      have : M ≤ 121 * M * r ^ (1 - (k:ℝ)) := by nlinarith [hMpos, h2]
      have h4 : 121 * M * r ^ (1 - (k:ℝ)) ≤ (max (121*M) 70 + 1) * r ^ (1 - (k:ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hrpos.le _)
        linarith
      linarith
  · have h1 : ‖iteratedFDeriv ℝ k Psi r‖ ≤ 70 * r ^ (1 - (k:ℝ)) := Psi_decay_large hge hk
    have hPr : (0:ℝ) ≤ r ^ (1 - (k:ℝ)) := Real.rpow_nonneg (by linarith) _
    have h4 : 70 * r ^ (1 - (k:ℝ)) ≤ (max (121*M) 70 + 1) * r ^ (1 - (k:ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ hPr
      linarith
    linarith


private lemma Psi_eq_zero_of_le_five {t : ℝ} (ht : t ≤ 5) : Psi t = 0 := by
  have : t / 5 - 1 ≤ 0 := by linarith
  simp only [Psi, this, Real.smoothTransition.zero_of_nonpos, zero_mul, neg_zero]

private lemma contDiff_Psi_norm {d : ℕ} :
    ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin d) => Psi ‖x‖) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · refine (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin d)) (by norm_num : (0:ℝ) < 1)]
      with y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact Psi_eq_zero_of_le_five (by linarith [norm_nonneg y, hy])
  · exact (contDiff_Psi.contDiffAt (x := ‖x‖)).comp x (contDiffAt_norm ℝ hx)


private lemma rpow_lower_of_norm_le {d : ℕ} {x : EuclideanSpace ℝ (Fin d)} (hx : ‖x‖ ≤ 11)
    (a : ℕ) (ha : a ≤ 3) : (1/122 : ℝ) ≤ (1 + ‖x‖ ^ 2) ^ ((1 - (a : ℝ)) / 2) := by
  have hB1 : (1:ℝ) ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
  have hB0 : (0:ℝ) < 1 + ‖x‖ ^ 2 := by linarith
  have hB122 : 1 + ‖x‖ ^ 2 ≤ 122 := by
    have h2 : ‖x‖ ^ 2 ≤ 121 := by nlinarith [norm_nonneg x]
    linarith
  interval_cases a
  · have he : (1 - ((0:ℕ):ℝ)) / 2 = (1:ℝ)/2 := by norm_num
    rw [he]
    exact le_trans (by norm_num) (Real.one_le_rpow hB1 (by norm_num : (0:ℝ) ≤ 1/2))
  · have he : (1 - ((1:ℕ):ℝ)) / 2 = (0:ℝ) := by norm_num
    rw [he, Real.rpow_zero]
    norm_num
  · have he : (1 - ((2:ℕ):ℝ)) / 2 = (-(1/2) : ℝ) := by norm_num
    rw [he]
    have h1 : (122:ℝ) ^ (-(1/2) : ℝ) ≤ (1 + ‖x‖ ^ 2) ^ (-(1/2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hB0 hB122 (by norm_num : -(1/2 : ℝ) ≤ 0)
    have h2 : (1/122 : ℝ) ≤ (122:ℝ) ^ (-(1/2) : ℝ) := by
      have h3 : (122:ℝ) ^ (-(1:ℝ)) ≤ (122:ℝ) ^ (-(1/2) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 122)
          (by norm_num : -(1:ℝ) ≤ -(1/2))
      simpa only [one_div, Real.rpow_neg_one] using h3
    linarith
  · have he : (1 - ((3:ℕ):ℝ)) / 2 = (-(1:ℝ)) := by norm_num
    rw [he]
    have h1 : (122:ℝ) ^ (-(1:ℝ)) ≤ (1 + ‖x‖ ^ 2) ^ (-(1:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hB0 hB122 (by norm_num : -(1:ℝ) ≤ 0)
    simpa only [one_div, Real.rpow_neg_one] using h1

private lemma rpow_upper_of_one_le_norm {d : ℕ} {x : EuclideanSpace ℝ (Fin d)} (hx : 1 ≤ ‖x‖)
    (a : ℕ) (ha : a ≤ 3) :
    ‖x‖ ^ (1 - (a : ℝ)) ≤ 2 * (1 + ‖x‖ ^ 2) ^ ((1 - (a : ℝ)) / 2) := by
  have hB0 : (0:ℝ) < 1 + ‖x‖ ^ 2 := by have := norm_nonneg x; nlinarith [sq_nonneg ‖x‖]
  have hB : 1 + ‖x‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 := by
    have h2 : (1:ℝ) ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    linarith
  have hB2 : 1 + ‖x‖ ^ 2 ≤ (2 * ‖x‖) ^ 2 := by
    have h2 : (1:ℝ) ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    nlinarith [norm_nonneg x]
  interval_cases a
  · have hL : (1:ℝ) - ((0:ℕ):ℝ) = 1 := by norm_num
    have he : ((1:ℝ) - ((0:ℕ):ℝ)) / 2 = (1:ℝ)/2 := by norm_num
    rw [he, hL, Real.rpow_one, ← Real.sqrt_eq_rpow]
    calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
      _ ≤ Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖x‖])
      _ ≤ 2 * Real.sqrt (1 + ‖x‖ ^ 2) := by
          have := Real.sqrt_nonneg (1 + ‖x‖ ^ 2); linarith
  · have hL : (1:ℝ) - ((1:ℕ):ℝ) = 0 := by norm_num
    rw [show ((1:ℝ) - ((1:ℕ):ℝ))/2 = 0 by norm_num, hL, Real.rpow_zero, Real.rpow_zero]
    norm_num
  · have hL : (1:ℝ) - ((2:ℕ):ℝ) = (-(1:ℝ)) := by norm_num
    have he : ((1:ℝ) - ((2:ℕ):ℝ)) / 2 = (-(1/2) : ℝ) := by norm_num
    rw [he, hL, Real.rpow_neg_one, Real.rpow_neg hB0.le, ← Real.sqrt_eq_rpow]
    have h2 : Real.sqrt (1 + ‖x‖ ^ 2) ≤ 2 * ‖x‖ := by
      calc Real.sqrt (1 + ‖x‖ ^ 2) ≤ Real.sqrt ((2 * ‖x‖) ^ 2) := Real.sqrt_le_sqrt hB2
        _ = 2 * ‖x‖ := Real.sqrt_sq (by positivity)
    have h3 : (2 * ‖x‖)⁻¹ ≤ (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.mpr hB0) h2
    calc ‖x‖⁻¹ = 2 * (2 * ‖x‖)⁻¹ := by field_simp
      _ ≤ 2 * (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹ :=
          mul_le_mul_of_nonneg_left h3 (by norm_num)
  · have hL : (1:ℝ) - ((3:ℕ):ℝ) = (-(2:ℝ)) := by norm_num
    have he : ((1:ℝ) - ((3:ℕ):ℝ)) / 2 = (-(1:ℝ)) := by norm_num
    rw [he, hL, Real.rpow_neg_one]
    have hsq : ‖x‖ ^ (-(2:ℝ)) = (‖x‖ ^ 2)⁻¹ := by
      rw [show (-(2:ℝ)) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg (norm_nonneg x), Real.rpow_natCast]
    rw [hsq]
    have h2 : (2 * ‖x‖ ^ 2)⁻¹ ≤ (1 + ‖x‖ ^ 2)⁻¹ := inv_anti₀ hB0 hB
    calc (‖x‖ ^ 2)⁻¹ = 2 * (2 * ‖x‖ ^ 2)⁻¹ := by field_simp
      _ ≤ 2 * (1 + ‖x‖ ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h2 (by norm_num)


private theorem aux_main {d : ℕ} {A : ℝ} (hA : 0 < A)
    (hdec : ∀ k : ℕ, k ≤ 3 → ∀ r : ℝ, 1 ≤ r →
      ‖iteratedFDeriv ℝ k Psi r‖ ≤ A * r ^ (1 - (k : ℝ))) :
    ∃ Creg : ℝ, 0 < Creg ∧ ∀ (a : ℕ), a ≤ 3 → ∀ x : EuclideanSpace ℝ (Fin d),
      ‖iteratedFDeriv ℝ a (fun x : EuclideanSpace ℝ (Fin d) => Psi ‖x‖) x‖
        ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (a : ℝ)) / 2) := by
  classical
  have hK : ∀ a : ℕ, a ≤ 3 → ∃ K : ℝ, 0 < K ∧ ∀ x : EuclideanSpace ℝ (Fin d), 1 ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ a (fun x : EuclideanSpace ℝ (Fin d) => Psi ‖x‖) x‖
        ≤ K * ‖x‖ ^ (1 - (a : ℝ)) := by
    intro a ha
    exact radial_le_of_decay_smooth contDiff_Psi hA (fun k hk r hr => hdec k (le_trans hk ha) r hr)
  let Kd : ℕ → ℝ := fun a => if ha : a ≤ 3 then Classical.choose (hK a ha) else 1
  have hKd_pos : ∀ a, a ≤ 3 → 0 < Kd a := by
    intro a ha
    simp only [Kd, dif_pos ha]
    exact (Classical.choose_spec (hK a ha)).1
  have hKd_bound : ∀ a, a ≤ 3 → ∀ x : EuclideanSpace ℝ (Fin d), 1 ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ a (fun x : EuclideanSpace ℝ (Fin d) => Psi ‖x‖) x‖
        ≤ Kd a * ‖x‖ ^ (1 - (a : ℝ)) := by
    intro a ha x hx
    simp only [Kd, dif_pos ha]
    exact (Classical.choose_spec (hK a ha)).2 x hx
  have hM : ∀ a : ℕ, ∃ M : ℝ, ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≤ 11 →
      ‖iteratedFDeriv ℝ a (fun x : EuclideanSpace ℝ (Fin d) => Psi ‖x‖) x‖ ≤ M := by
    intro a
    have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin d) =>
        ‖iteratedFDeriv ℝ a (fun x : EuclideanSpace ℝ (Fin d) => Psi ‖x‖) x‖) :=
      (contDiff_Psi_norm.continuous_iteratedFDeriv (m := a) (by exact_mod_cast le_top)).norm
    obtain ⟨M, hMb⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 11).exists_bound_of_continuousOn
      hcont.continuousOn
    exact ⟨M, fun x hx => by
      have hx' : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 11 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hx
      have h := hMb x hx'
      rwa [Real.norm_of_nonneg (norm_nonneg _)] at h⟩
  let Mf : ℕ → ℝ := fun a => if ha : a ≤ 3 then Classical.choose (hM a) else 0
  have hMf_bound : ∀ a, a ≤ 3 → ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≤ 11 →
      ‖iteratedFDeriv ℝ a (fun x : EuclideanSpace ℝ (Fin d) => Psi ‖x‖) x‖ ≤ Mf a := by
    intro a ha x hx
    simp only [Mf, dif_pos ha]
    exact (Classical.choose_spec (hM a)) x hx
  set M : ℝ := max (Mf 0) (max (Mf 1) (max (Mf 2) (Mf 3))) with hMdef
  set K : ℝ := max (Kd 0) (max (Kd 1) (max (Kd 2) (Kd 3))) with hKdef
  have hMle : ∀ a, a ≤ 3 → Mf a ≤ M := by
    intro a ha
    rw [hMdef]
    interval_cases a
    · exact le_max_left (Mf 0) _
    · exact le_trans (le_max_left (Mf 1) _) (le_max_right (Mf 0) _)
    · exact le_trans (le_trans (le_max_left (Mf 2) _) (le_max_right (Mf 1) _))
        (le_max_right (Mf 0) _)
    · exact le_trans (le_trans (le_max_right (Mf 2) _) (le_max_right (Mf 1) _))
        (le_max_right (Mf 0) _)
  have hKle : ∀ a, a ≤ 3 → Kd a ≤ K := by
    intro a ha
    rw [hKdef]
    interval_cases a
    · exact le_max_left (Kd 0) _
    · exact le_trans (le_max_left (Kd 1) _) (le_max_right (Kd 0) _)
    · exact le_trans (le_trans (le_max_left (Kd 2) _) (le_max_right (Kd 1) _))
        (le_max_right (Kd 0) _)
    · exact le_trans (le_trans (le_max_right (Kd 2) _) (le_max_right (Kd 1) _))
        (le_max_right (Kd 0) _)
  have hKnonneg : (0:ℝ) ≤ max K 0 := le_max_right _ _
  have hMnonneg : (0:ℝ) ≤ max M 0 := le_max_right _ _
  refine ⟨122 * max M 0 + 2 * max K 0 + 1, by positivity, fun a ha x => ?_⟩
  rcases lt_or_ge ‖x‖ 11 with hx | hx
  · have h1 : ‖iteratedFDeriv ℝ a (fun x : EuclideanSpace ℝ (Fin d) => Psi ‖x‖) x‖ ≤ Mf a :=
      hMf_bound a ha x (le_of_lt hx)
    have h2 : (1/122 : ℝ) ≤ (1 + ‖x‖ ^ 2) ^ ((1 - (a : ℝ)) / 2) :=
      rpow_lower_of_norm_le (le_of_lt hx) a ha
    have hP : (0:ℝ) ≤ (1 + ‖x‖ ^ 2) ^ ((1 - (a : ℝ)) / 2) := Real.rpow_nonneg (by positivity) _
    calc ‖iteratedFDeriv ℝ a (fun x : EuclideanSpace ℝ (Fin d) => Psi ‖x‖) x‖
        ≤ Mf a := h1
      _ ≤ max M 0 := le_trans (hMle a ha) (le_max_left _ _)
      _ = (122 * max M 0) * (1/122) := by ring
      _ ≤ (122 * max M 0) * (1 + ‖x‖ ^ 2) ^ ((1 - (a : ℝ)) / 2) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ (122 * max M 0 + 2 * max K 0 + 1) * (1 + ‖x‖ ^ 2) ^ ((1 - (a : ℝ)) / 2) :=
            mul_le_mul_of_nonneg_right (by linarith [hKnonneg]) hP
  · have hx1 : 1 ≤ ‖x‖ := by linarith
    have h1 : ‖iteratedFDeriv ℝ a (fun x : EuclideanSpace ℝ (Fin d) => Psi ‖x‖) x‖
        ≤ Kd a * ‖x‖ ^ (1 - (a : ℝ)) := hKd_bound a ha x hx1
    have h2 : ‖x‖ ^ (1 - (a : ℝ)) ≤ 2 * (1 + ‖x‖ ^ 2) ^ ((1 - (a : ℝ)) / 2) :=
      rpow_upper_of_one_le_norm hx1 a ha
    have hP : (0:ℝ) ≤ (1 + ‖x‖ ^ 2) ^ ((1 - (a : ℝ)) / 2) := Real.rpow_nonneg (by positivity) _
    have hPx : (0:ℝ) ≤ ‖x‖ ^ (1 - (a : ℝ)) := Real.rpow_nonneg (by positivity) _
    calc ‖iteratedFDeriv ℝ a (fun x : EuclideanSpace ℝ (Fin d) => Psi ‖x‖) x‖
        ≤ Kd a * ‖x‖ ^ (1 - (a : ℝ)) := h1
      _ ≤ max K 0 * ‖x‖ ^ (1 - (a : ℝ)) := mul_le_mul_of_nonneg_right (le_trans (hKle a ha) (le_max_left _ _)) hPx
      _ ≤ max K 0 * (2 * (1 + ‖x‖ ^ 2) ^ ((1 - (a : ℝ)) / 2)) := mul_le_mul_of_nonneg_left h2 hKnonneg
      _ = (2 * max K 0) * (1 + ‖x‖ ^ 2) ^ ((1 - (a : ℝ)) / 2) := by ring
      _ ≤ (122 * max M 0 + 2 * max K 0 + 1) * (1 + ‖x‖ ^ 2) ^ ((1 - (a : ℝ)) / 2) :=
            mul_le_mul_of_nonneg_right (by linarith [hMnonneg]) hP


/-- **Kohn–Nirenberg regularity of the auxiliary weight** `ω₀(x) = -χ(‖x‖)·‖x‖/(log(2+‖x‖))²`,
where `χ(r) = smoothTransition (r/5 - 1)` is a smooth cutoff which is `0` for `r ≤ 5` and `1` for
`r ≥ 10`.  There is `Creg > 0` with `‖D^aω₀(x)‖ ≤ Creg·(1+‖x‖²)^{(1-a)/2}` for all `a ≤ 3` and
all `x`. -/
theorem omega0_iteratedFDeriv_le {d : ℕ} :
    ∃ Creg : ℝ, 0 < Creg ∧ ∀ (a : ℕ), a ≤ 3 → ∀ x : EuclideanSpace ℝ (Fin d),
      ‖iteratedFDeriv ℝ a (fun x : EuclideanSpace ℝ (Fin d) =>
        -(Real.smoothTransition (‖x‖ / 5 - 1) * (‖x‖ / (Real.log (2 + ‖x‖)) ^ 2))) x‖
      ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (a : ℝ)) / 2) := by
  obtain ⟨A, hA, hdec⟩ := Psi_deriv_decay
  obtain ⟨Creg, hCpos, hC⟩ := aux_main (d := d) hA hdec
  refine ⟨Creg, hCpos, fun a ha x => ?_⟩
  have h := hC a ha x
  simpa only [Psi] using h

end Commons.Analysis.Calculus