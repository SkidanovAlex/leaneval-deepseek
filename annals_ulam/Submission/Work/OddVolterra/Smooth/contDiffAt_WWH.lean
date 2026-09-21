import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.RowIdentity.odd_rowH_aux
import Submission.Work.OddVolterra.RowIdentity.Basic
import Submission.Work.OddVolterra.RowIdentity.contDiffAt_WW
import Submission.Work.OddVolterra.RowIdentity.contDiffOn_AH
import Submission.Work.OddVolterra.RowIdentity.WWDefs
import Submission.Work.OddVolterra.Smooth.ParametricIntegral

/-!
# Smoothness of the swept integral `WWH` of the odd centroid row

`WWH n h x y u = ∫_σ in u..1, (σ-u)^{n-1/2} · AH n h x y u σ`, where `AH` is the coefficient of
the swept integral (a `C^∞` function of `(u,σ)` on the rectangle on which the two frozen
radicands `QyH`, `QxH` are positive).

The singular factor `(σ-u)^{n-1/2}` is removed by the substitution `σ = u + θ²(1-u)`:

`WWH n h x y u = (1-u)^{n+1/2} ∫_θ in 0..1, 2 θ^{2n} · AH n h x y u (u + θ²(1-u))` for `u < 1`.

The exponent `2n` is a nonnegative *integer*, so the substituted integrand is genuinely smooth
in `(u,θ)` on a neighbourhood of `{s} × [0,1]`; differentiating under the integral sign
(`Work.OddVolterra.Smooth.Alt.contDiffAt_integral_of_contDiffOn`) gives that the integral is
`C^∞` at `s`, and so is the prefactor `(1-u)^{n+1/2}` because `1 - s > 0`.  Hence `WWH` is `C^∞`
at `s`, in particular `C^n`.
-/

namespace Work.OddVolterra.Smooth

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-- The half-integer power bookkeeping behind the substitution `σ = u + θ²d` in the swept
integral `WWH`: for `θ > 0` and `d > 0`,

`(θ²d)^{n-1/2} · (2θd) = d^{n+1/2} · (2θ^{2n})`. -/
lemma rpow_sq_mul_sub_half {n : ℕ} {d θ : ℝ} (hd : 0 < d) (hθ : 0 < θ) :
    (θ ^ 2 * d) ^ ((n : ℝ) - 1 / 2) * (2 * θ * d)
      = d ^ ((n : ℝ) + 1 / 2) * (2 * θ ^ (2 * n)) := by
  set p : ℝ := (n : ℝ) - 1 / 2 with hp
  have hp1 : p + 1 = (n : ℝ) + 1 / 2 := by rw [hp]; ring
  have h2p : 2 * p + 1 = ((2 * n : ℕ) : ℝ) := by rw [hp]; push_cast; ring
  have h1 : (θ ^ 2 * d) ^ p = (θ ^ 2) ^ p * d ^ p := Real.mul_rpow (sq_nonneg θ) hd.le
  have h2 : (θ ^ 2) ^ p = θ ^ (2 * p) := by
    rw [← Real.rpow_natCast θ 2]
    exact (Real.rpow_mul (le_of_lt hθ) 2 p).symm
  have h3 : θ ^ (2 * p) * θ = θ ^ ((2 * n : ℕ) : ℝ) := by
    have h : θ ^ (2 * p + 1) = θ ^ (2 * p) * θ ^ (1 : ℝ) := Real.rpow_add hθ (2 * p) 1
    rw [Real.rpow_one] at h
    rw [← h, h2p]
  have h4 : d ^ (p + 1) = d ^ p * d := by
    have h := Real.rpow_add hd p 1
    rw [Real.rpow_one] at h
    exact h
  calc (θ ^ 2 * d) ^ p * (2 * θ * d)
      = ((θ ^ 2) ^ p * d ^ p) * (2 * θ * d) := by rw [h1]
    _ = 2 * ((θ ^ 2) ^ p * θ) * (d ^ p * d) := by ring
    _ = 2 * (θ ^ (2 * p) * θ) * (d ^ p * d) := by rw [h2]
    _ = 2 * θ ^ ((2 * n : ℕ) : ℝ) * (d ^ p * d) := by rw [h3]
    _ = 2 * θ ^ ((2 * n : ℕ) : ℝ) * d ^ (p + 1) := by rw [h4]
    _ = d ^ ((n : ℝ) + 1 / 2) * (2 * θ ^ (2 * n)) := by
          rw [hp1, Real.rpow_natCast θ (2 * n)]
          ring

/-- The substitution `σ = u + θ²(1-u)` in the swept integral `WWH`, valid for `0 < u < 1`. -/
lemma WWH_eq_subst (n : ℕ) (h x y : ℝ → ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    Work.OddVolterra.RowIdentity.WWH n h x y u
      = (1 - u) ^ ((n : ℝ) + 1 / 2)
        * ∫ θ in (0 : ℝ)..1,
            2 * θ ^ (2 * n) * Work.OddVolterra.RowIdentity.AH n h x y u (u + θ ^ 2 * (1 - u)) := by
  have hderiv : ∀ θ ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasDerivAt (fun θ : ℝ => u + θ ^ 2 * (1 - u)) (2 * θ * (1 - u)) θ := by
    intro θ _
    have h1 : HasDerivAt (fun θ : ℝ => θ ^ 2 * (1 - u)) (2 * θ * (1 - u)) θ := by
      simpa using ((hasDerivAt_pow 2 θ).mul_const (1 - u))
    simpa [add_comm] using h1.const_add u
  have hnonneg : ∀ θ ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1), 0 ≤ 2 * θ * (1 - u) := by
    intro θ hθ
    rw [min_eq_left (zero_le_one), max_eq_right (zero_le_one)] at hθ
    exact mul_nonneg (mul_nonneg (by norm_num) hθ.1.le) (by linarith)
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun θ : ℝ => u + θ ^ 2 * (1 - u)) (f' := fun θ : ℝ => 2 * θ * (1 - u))
    (g := fun σ : ℝ => (σ - u) ^ ((n : ℝ) - 1 / 2) * Work.OddVolterra.RowIdentity.AH n h x y u σ)
    (a := 0) (b := 1)
    (by fun_prop) hderiv hnonneg
  have hsub' : (∫ θ in (0 : ℝ)..1,
        ((u + θ ^ 2 * (1 - u)) - u) ^ ((n : ℝ) - 1 / 2)
          * Work.OddVolterra.RowIdentity.AH n h x y u (u + θ ^ 2 * (1 - u))
          * (2 * θ * (1 - u)))
      = ∫ σ in u..1, (σ - u) ^ ((n : ℝ) - 1 / 2) * Work.OddVolterra.RowIdentity.AH n h x y u σ := by
    simpa [Function.comp_def] using hsub
  have hLHS : Work.OddVolterra.RowIdentity.WWH n h x y u
      = ∫ σ in u..1, (σ - u) ^ ((n : ℝ) - 1 / 2) * Work.OddVolterra.RowIdentity.AH n h x y u σ := by
    simp only [Work.OddVolterra.RowIdentity.WWH, Work.OddVolterra.RowIdentity.WintH]
  rw [hLHS, ← hsub']
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun θ hθ => ?_))
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hθ
  have hθm : (u + θ ^ 2 * (1 - u)) - u = θ ^ 2 * (1 - u) := by ring
  rw [hθm]
  have hd : 0 < 1 - u := by linarith
  calc (θ ^ 2 * (1 - u)) ^ ((n : ℝ) - 1 / 2)
        * Work.OddVolterra.RowIdentity.AH n h x y u (u + θ ^ 2 * (1 - u)) * (2 * θ * (1 - u))
      = ((θ ^ 2 * (1 - u)) ^ ((n : ℝ) - 1 / 2) * (2 * θ * (1 - u)))
          * Work.OddVolterra.RowIdentity.AH n h x y u (u + θ ^ 2 * (1 - u)) := by ring
    _ = ((1 - u) ^ ((n : ℝ) + 1 / 2) * (2 * θ ^ (2 * n)))
          * Work.OddVolterra.RowIdentity.AH n h x y u (u + θ ^ 2 * (1 - u)) := by
          rw [rpow_sq_mul_sub_half (n := n) hd hθ.1]
    _ = (1 - u) ^ ((n : ℝ) + 1 / 2)
          * (2 * θ ^ (2 * n)
              * Work.OddVolterra.RowIdentity.AH n h x y u (u + θ ^ 2 * (1 - u))) := by ring

theorem contDiffAt_WWH {n : ℕ} (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hx : ContDiffOn ℝ (⊤ : ℕ∞) x (Set.Ioi 0)) (hy : ContDiffOn ℝ (⊤ : ℕ∞) y (Set.Ioi 0))
    {s δ : ℝ} (hs1 : s < 1) (hδ : 0 < δ) (hsδ : 0 < s - δ)
    (hQy : ∀ u σ : ℝ, u ∈ Set.Ioo (s - δ) (s + δ) → σ ∈ Set.Ioo (s - δ) (1 + δ) →
      0 < Work.OddVolterra.RowIdentity.QyH h y u σ)
    (hQx : ∀ u σ : ℝ, u ∈ Set.Ioo (s - δ) (s + δ) → σ ∈ Set.Ioo (s - δ) (1 + δ) →
      0 < Work.OddVolterra.RowIdentity.QxH h x u σ) :
    ContDiffAt ℝ (↑n) (fun u : ℝ => Work.OddVolterra.RowIdentity.WWH n h x y u) s := by
  have hs0 : 0 < s := by linarith
  -- the open set of `(u,θ)` on which the substituted integrand is smooth
  set V : Set (ℝ × ℝ) :=
    {q : ℝ × ℝ | q.1 ∈ Set.Ioo (s - δ) (s + δ) ∧
      q.1 + q.2 ^ 2 * (1 - q.1) ∈ Set.Ioo (s - δ) (1 + δ)} with hVdef
  have hVopen : IsOpen V := by
    rw [hVdef]
    exact (isOpen_Ioo.preimage continuous_fst).inter (isOpen_Ioo.preimage (by fun_prop))
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => Work.OddVolterra.RowIdentity.AH n h x y p.1 p.2)
      (Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (1 + δ)) :=
    Work.OddVolterra.RowIdentity.contDiffOn_AH hsδ hh hx hy
      (fun u σ hu hσ => ⟨hQy u σ hu hσ, hQx u σ hu hσ⟩)
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => Work.OddVolterra.RowIdentity.AH n h x y q.1 (q.1 + q.2 ^ 2 * (1 - q.1))) V := by
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun q : ℝ × ℝ => (q.1, q.1 + q.2 ^ 2 * (1 - q.1))) Set.univ := by fun_prop
    have h2 := hA.comp (h1.mono (Set.subset_univ V)) (fun q hq => by rw [hVdef] at hq; exact hq)
    simpa [Function.comp_def] using h2
  have hF : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ =>
        2 * q.2 ^ (2 * n) * Work.OddVolterra.RowIdentity.AH n h x y q.1 (q.1 + q.2 ^ 2 * (1 - q.1))) V := by
    have hpow : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => 2 * q.2 ^ (2 * n)) V := by fun_prop
    simpa only [Pi.mul_apply] using hpow.mul hcomp
  have hseg : ∀ θ ∈ Set.uIcc (0 : ℝ) 1, (s, θ) ∈ V := by
    intro θ hθ
    rw [hVdef]
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hθ
    have hθ2 : θ ^ 2 ≤ 1 := by nlinarith [hθ.1, hθ.2]
    have hlow : 0 ≤ θ ^ 2 * (1 - s) := mul_nonneg (sq_nonneg θ) (by linarith)
    have hhigh : θ ^ 2 * (1 - s) ≤ 1 * (1 - s) :=
      mul_le_mul_of_nonneg_right hθ2 (by linarith)
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hG : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun u : ℝ => ∫ θ in (0 : ℝ)..1,
        2 * θ ^ (2 * n) * Work.OddVolterra.RowIdentity.AH n h x y u (u + θ ^ 2 * (1 - u))) s :=
    Work.OddVolterra.Smooth.Alt.contDiffAt_integral_of_contDiffOn hVopen hF hseg
  have hp : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => (1 - u) ^ ((n : ℝ) + 1 / 2)) s := by
    have hne : (1 : ℝ) - s ≠ 0 := sub_ne_zero.mpr (by linarith : (1 : ℝ) ≠ s)
    exact (contDiffAt_const.sub contDiffAt_id).rpow contDiffAt_const hne
  have hprod : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun u : ℝ => (1 - u) ^ ((n : ℝ) + 1 / 2)
        * ∫ θ in (0 : ℝ)..1,
            2 * θ ^ (2 * n) * Work.OddVolterra.RowIdentity.AH n h x y u (u + θ ^ 2 * (1 - u))) s :=
    hp.mul hG
  have hWWH : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => Work.OddVolterra.RowIdentity.WWH n h x y u) s := by
    refine hprod.congr_of_eventuallyEq ?_
    have hmin : 0 < min s (1 - s) := lt_min hs0 (by linarith)
    filter_upwards [Metric.ball_mem_nhds s hmin] with u hu
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hu
    have hu0 : 0 < u := by
      have := hu.1
      have hm : min s (1 - s) ≤ s := min_le_left _ _
      linarith
    have hu1 : u < 1 := by
      have := hu.2
      have hm : min s (1 - s) ≤ 1 - s := min_le_right _ _
      linarith
    exact WWH_eq_subst n h x y hu0 hu1
  exact (contDiffAt_infty.mp hWWH) n

end

end Work.OddVolterra.Smooth
