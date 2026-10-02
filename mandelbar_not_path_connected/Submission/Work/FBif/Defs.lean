/-
Copyright: subproject `Submission/Work/FBif/` of `mandelbar_not_path_connected`.

# `Work.FBif` — the bifurcation side at a simple parabolic parameter (FBif, part 1)

This module fixes the vocabulary of the FBif area: the area proves Hubbard–Schleicher's
Lemma 3.4 (= MNS Theorem 2.1, second half)

> every simple parabolic periodic point of odd period `k` of `T_c` is on the boundary of a
> hyperbolic component: arbitrarily close to `c` there are parameters `c'` for which there is
> **no** point of period `k` near the parabolic point,

in the special case `k = 5` relevant to the mandelbar drive.

## The route (Hubbard–Schleicher, arXiv:1209.1753, Lemma 3.4)

1. `perturb c q ε` is the map `f_ε = T_c + ε·q`, with `q` an **antipolynomial** that vanishes
   to second order at `z₁, T z₁, T² z₁, T³ z₁` and has `q (T⁴ z₁) ≠ 0`
   (`GoodPerturbation`).  This is the perturbation of Lemma 3.4: it kills the period-`5`
   points near `z₁`.
2. `HSEstimate c z₁ q`: for small `ε > 0`, `f_ε` has no fixed point of its fifth iterate in a
   *fixed* disc `ball z₁ δ`.  This is HS's explicit estimate; it is obtained from the
   normalised local expansion `HSExpansion` by the real-analysis lemma
   `Work.FBif.HSLocal.hsLocalNoFix` (all proved in this area).
3. `Straightening c z₁ q`: for small `ε > 0` the perturbed map is hybrid-equivalent (through a
   homeomorphism `Φ_ε` close to the identity) to a genuine quadratic antipolynomial
   `T_{c_ε}`, with `c_ε → c`.  This is the composition of
     * the C¹ gluing of `f_ε` with a fixed model map outside the critical orbit (so that the
       map is a quadratic-like restriction of degree `2`),
     * the invariant Beltrami coefficient `μ_ε` (support shrinking to the cycle, `‖μ_ε‖∞ → 0`),
     * MRMT `M1`/`M2″` (`principal μ_ε`, `conj_contDiff`) and `M3` (holomorphy off the support),
     * Liouville's theorem (`Work.FBif.Straightening.antiholo_of_norm_sub_sq_bounded`),
     * MRMT `M6` (`tendsto_principal`) for `c_ε → c` and `Φ_ε → id`.
4. `Conjugates.noPer5_image` moves "no period-`5` point near `z₁`" across `Φ_ε`, and the
   conclusion `bifSide_of` follows.

## Main definitions

* `Antipoly q` — `q` is a polynomial in `z̄`;
* `perturb c q ε` — the perturbed map `T_c + ε·q`;
* `NoPer5 f z δ` — `f` has no point of period dividing `5` in `ball z δ`;
* `Conjugates Φ f g` — topological (semi-)conjugacy;
* `GoodPerturbation c z₁ q` — the perturbation conditions of HS Lemma 3.4;
* `HSEstimate c z₁ q` — HS's estimate (step 2; proved for the perturbations of
  `Work.FBif.exists_HSExpansion` as `Work.FBif.HSEstimate.of_expansion'`);
* `Straightening c z₁ q` — the straightening statement (step 3; proved along small parameters
  by `Work.FBif.exists_gluingDatum_scaled` and `Work.FBif.straightening_of_gluingFamily`);
* `bifSide_of` — the assembly.
-/
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function
open scoped Topology

noncomputable section

namespace Work.FBif

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Perturbations by antipolynomials -/

/-- An **antipolynomial**: a function of the form `z ↦ P(z̄)`. -/
def Antipoly (q : ℂ → ℂ) : Prop := ∃ P : Polynomial ℂ, ∀ z : ℂ, q z = P.eval (star z)

theorem Antipoly.continuous {q : ℂ → ℂ} (hq : Antipoly q) : Continuous q := by
  obtain ⟨P, hP⟩ := hq
  have h : q = fun z : ℂ => P.eval (star z) := funext hP
  rw [h]
  exact P.continuous.comp continuous_star

/-- `T_c` is continuous. -/
theorem continuous_tantibar (c : ℂ) : Continuous (Tantibar c) := by
  have h : Tantibar c = fun z : ℂ => (star z) ^ 2 + c := rfl
  rw [h]; fun_prop

/-- The perturbed map `f_ε = T_c + ε·q`. -/
def perturb (c : ℂ) (q : ℂ → ℂ) (ε : ℝ) : ℂ → ℂ := fun z => Tantibar c z + (ε : ℂ) * q z

@[simp] theorem perturb_apply (c : ℂ) (q : ℂ → ℂ) (ε : ℝ) (z : ℂ) :
    perturb c q ε z = Tantibar c z + (ε : ℂ) * q z := rfl

theorem perturb_zero (c : ℂ) (q : ℂ → ℂ) : perturb c q 0 = Tantibar c := by
  funext z; simp [perturb]

theorem continuous_perturb {q : ℂ → ℂ} (hq : Antipoly q) (c : ℂ) (ε : ℝ) :
    Continuous (perturb c q ε) :=
  (continuous_tantibar c).add (continuous_const.mul hq.continuous)

/-! ## Period-`5` points -/

/-- `f` has **no point of period dividing `5`** in the ball `ball z δ`; equivalently, the fifth
iterate of `f` has no fixed point there. -/
def NoPer5 (f : ℂ → ℂ) (z : ℂ) (δ : ℝ) : Prop := ∀ w ∈ Metric.ball z δ, f^[5] w ≠ w

theorem NoPer5.mono {f : ℂ → ℂ} {z : ℂ} {δ δ' : ℝ} (h : NoPer5 f z δ) (h' : δ' ≤ δ) :
    NoPer5 f z δ' := fun w hw => h w (Metric.ball_subset_ball h' hw)

/-! ## Conjugacies -/

/-- `Φ` conjugates `f` to `g`: `Φ ∘ f = g ∘ Φ`. -/
def Conjugates (Φ : ℂ ≃ₜ ℂ) (f g : ℂ → ℂ) : Prop := ∀ z : ℂ, Φ (f z) = g (Φ z)

theorem Conjugates.iterate {Φ : ℂ ≃ₜ ℂ} {f g : ℂ → ℂ} (h : Conjugates Φ f g) (n : ℕ) :
    ∀ z : ℂ, Φ ((f^[n]) z) = (g^[n]) (Φ z) := by
  intro z
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h, ih]

/-- A conjugacy transports the absence of period-`5` points to the image of the disc. -/
theorem Conjugates.noPer5_image {Φ : ℂ ≃ₜ ℂ} {f g : ℂ → ℂ} (h : Conjugates Φ f g) {z : ℂ}
    {δ : ℝ} (hδ : NoPer5 f z δ) :
    ∀ w ∈ Φ '' (Metric.ball z δ), (g^[5]) w ≠ w := by
  rintro w ⟨u, hu, rfl⟩ hfix
  refine hδ u hu ?_
  apply Φ.injective
  rw [h.iterate 5, hfix]

/-! ## The perturbation of Hubbard–Schleicher's Lemma 3.4 -/

/-- The cycle points of the root-parabolic point: `z_j = T_c^j z₁`. -/
def cyclePt (c : ℂ) (z₁ : ℂ) (j : ℕ) : ℂ := (Tantibar c)^[j] z₁

/-- **The perturbation conditions of HS Lemma 3.4.**  `q = P(z̄)` for a polynomial `P` that
vanishes to second order at the parabolic cycle points `z₀ = z₁, …, z₃ = T³ z₁`, and vanishes
to second order at `z₄ = T⁴ z₁` in the sense that `P - P(z̄₄)` is divisible by `(X - z̄₄)²`;
finally `q z₄ ≠ 0`. -/
def GoodPerturbation (c : ℂ) (z₁ : ℂ) (q : ℂ → ℂ) : Prop :=
  ∃ P : Polynomial ℂ,
    (∀ z : ℂ, q z = P.eval (star z)) ∧
    (∀ j : ℕ, j ≤ 3 →
      (Polynomial.X - Polynomial.C (star (cyclePt c z₁ j))) ^ 2 ∣ P) ∧
    ((Polynomial.X - Polynomial.C (star (cyclePt c z₁ 4))) ^ 2 ∣
      (P - Polynomial.C (P.eval (star (cyclePt c z₁ 4))))) ∧
    q (cyclePt c z₁ 4) ≠ 0

theorem GoodPerturbation.anti {c z₁ : ℂ} {q : ℂ → ℂ} (h : GoodPerturbation c z₁ q) :
    Antipoly q := by
  obtain ⟨P, hrep, -, -, -⟩ := h
  exact ⟨P, hrep⟩

/-! ## HS's estimate and the straightening: the two inputs of the assembly -/

/-- **HS's estimate** (Hubbard–Schleicher Lemma 3.4, the estimate): for the perturbation
`q`, the perturbed map `f_ε = T_c + ε q` has no point of period dividing `5` in a *fixed*
disc around `z₁`, uniformly for small `ε > 0`. -/
def HSEstimate (c : ℂ) (z₁ : ℂ) (q : ℂ → ℂ) : Prop :=
  ∃ δ > 0, ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → NoPer5 (perturb c q ε) z₁ δ

/-- **The straightening input of FBif (step 3).**  There is a disc radius `δ' > 0` and a sequence
of perturbations `ε_n → 0⁺` such that

* the perturbed maps `f_n = perturb c q (ε_n)` are conjugated on the disc `ball z₁ δ'`, through
  the *fifth iterate*, to quadratic antipolynomials `T_{c_n}` with `c_n → c`;
* the conjugating homeomorphisms `Φ_n` (and their inverses) tend to the identity locally
  uniformly.

The first two requirements are what the FBif construction produces: the C¹ gluing of `f_ε` with
the model outside the critical orbit makes `f_ε` straightenable, the invariant Beltrami
coefficient `μ_ε` is supported near the critical orbit with `‖μ_ε‖∞ → 0`, MRMT `M1`/`M2″` produce
`Φ_ε = principal μ_ε` with `Φ_ε ∘ F_ε = G_ε ∘ Φ_ε` for an *entire* antiholomorphic `G_ε`,
Liouville's theorem (`antiholo_of_norm_sub_sq_bounded`) identifies `G_ε` with `T_{c_ε}`, and MRMT
`M6` (`tendsto_principal`) plus the quantitative decay of the principal solution give
`c_ε → c` and `Φ_ε → id` (with inverses).  See `FBif/MRMTInput.lean`, where this is reduced to
the gluing datum. -/
def Straightening (c : ℂ) (z₁ : ℂ) (q : ℂ → ℂ) : Prop :=
  ∃ δ' > 0, ∃ εs : ℕ → ℝ, (∀ n : ℕ, 0 < εs n) ∧ Tendsto εs atTop (𝓝 0) ∧
    ∃ Φs : ℕ → ℂ ≃ₜ ℂ,
      TendstoLocallyUniformly (fun n : ℕ => (Φs n : ℂ → ℂ)) id atTop ∧
      TendstoLocallyUniformly (fun n : ℕ => ((Φs n).symm : ℂ → ℂ)) id atTop ∧
      ∃ cs : ℕ → ℂ, Tendsto cs atTop (𝓝 c) ∧
        ∀ n : ℕ, ∀ z : ℂ, ‖z - z₁‖ ≤ δ' →
          Φs n (((perturb c q (εs n))^[5]) z) = ((Tantibar (cs n))^[5]) (Φs n z)

/-- The witness form of `Straightening`, with the explicit data. -/
theorem Straightening.witness {c z₁ : ℂ} {q : ℂ → ℂ} (h : Straightening c z₁ q) :
    ∃ δ' > 0, ∃ εs : ℕ → ℝ, (∀ n : ℕ, 0 < εs n) ∧ Tendsto εs atTop (𝓝 0) ∧
      ∃ Φs : ℕ → ℂ ≃ₜ ℂ,
        TendstoLocallyUniformly (fun n : ℕ => (Φs n : ℂ → ℂ)) id atTop ∧
        TendstoLocallyUniformly (fun n : ℕ => ((Φs n).symm : ℂ → ℂ)) id atTop ∧
        ∃ cs : ℕ → ℂ, Tendsto cs atTop (𝓝 c) ∧
          ∀ n : ℕ, ∀ z : ℂ, ‖z - z₁‖ ≤ δ' →
            Φs n (((perturb c q (εs n))^[5]) z) = ((Tantibar (cs n))^[5]) (Φs n z) := h

/-! ## The assembly -/

/-- **The assembly of FBif.**  From HS's estimate for the perturbation `q` and the
straightening of the perturbed family, one gets the bifurcation side at `c`: arbitrarily close
to `c` there are parameters `c'` for which there is no point of period dividing `5` in a fixed
disc around the parabolic point `z₁`. -/
theorem bifSide_of (c : ℂ) (z₁ : ℂ) (q : ℂ → ℂ)
    (hHS : HSEstimate c z₁ q) (hStr : Straightening c z₁ q) :
    ∃ δ > 0, ∀ r > 0, ∃ c' ∈ Metric.ball c r,
      ∀ z ∈ Metric.ball z₁ δ, (Tantibar c')^[5] z ≠ z := by
  obtain ⟨δ₀, hδ₀, ε₀, hε₀, hHS'⟩ := hHS
  obtain ⟨δ', hδ', εs, hεs, hεtend, Φs, hΦtend, hΦtend', cs, hctend, hconj⟩ := hStr
  set η : ℝ := min (δ₀ / 4) (δ' / 4) with hηdef
  have hηpos : 0 < η := lt_min (by linarith) (by linarith)
  have hηδ₀ : η ≤ δ₀ / 4 := by rw [hηdef]; exact min_le_left _ _
  have hηδ' : η ≤ δ' / 4 := by rw [hηdef]; exact min_le_right _ _
  -- the local closeness of `(Φs n).symm` to the identity near `z₁`
  obtain ⟨t, ht_nhds, ht_ev⟩ := (Metric.tendstoLocallyUniformly_iff.mp hΦtend') (η / 2)
    (by linarith) z₁
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp ht_nhds
  set δ : ℝ := min (η / 2) (ρ / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδη : δ ≤ η / 2 := min_le_left _ _
  have hδρ : δ ≤ ρ / 2 := min_le_right _ _
  refine ⟨δ, hδpos, fun r hr => ?_⟩
  -- the three eventual conditions
  have h1 : ∀ᶠ n : ℕ in atTop, εs n < ε₀ :=
    (hεtend.eventually (eventually_lt_nhds hε₀))
  have h2 : ∀ᶠ n : ℕ in atTop, dist (cs n) c < r :=
    (hctend.eventually (Metric.ball_mem_nhds c hr))
  have h3 : ∀ᶠ n : ℕ in atTop,
      ∀ y : ℂ, dist y z₁ < ρ → dist ((Φs n).symm y) y < η / 2 := by
    filter_upwards [ht_ev] with n hn y hy
    have hy' : y ∈ t := hρsub (Metric.mem_ball.mpr hy)
    have := hn y hy'
    rwa [dist_comm] at this
  obtain ⟨n, hn1, hn2, hn3⟩ := (h1.and (h2.and h3)).exists
  refine ⟨cs n, ?_, fun w hw => ?_⟩
  · rw [Metric.mem_ball]; exact hn2
  · set u : ℂ := (Φs n).symm w with hu
    have hΦu : Φs n u = w := (Φs n).apply_symm_apply w
    have hwδ : ‖w - z₁‖ < δ := by rwa [Metric.mem_ball, dist_eq_norm] at hw
    have hwρ : dist w z₁ < ρ := by
      rw [dist_eq_norm]; linarith [hδρ]
    have huw : dist u w < η / 2 := hn3 w hwρ
    have huw' : ‖u - w‖ < η / 2 := by simpa [dist_eq_norm] using huw
    have huη : ‖u - z₁‖ ≤ η := by
      have h : ‖u - z₁‖ < η / 2 + δ := by
        calc ‖u - z₁‖ = ‖(u - w) + (w - z₁)‖ := by ring_nf
          _ ≤ ‖u - w‖ + ‖w - z₁‖ := norm_add_le _ _
          _ < η / 2 + δ := by linarith
      have : δ ≤ η / 2 := hδη
      linarith
    intro hfix
    have hper : ¬ ((perturb c q (εs n))^[5]) u = u :=
      hHS' (εs n) (hεs n) hn1 u (by rw [Metric.mem_ball, dist_eq_norm]; linarith)
    refine hper ((Φs n).injective ?_)
    rw [hconj n u (by linarith [huη, hηδ']), hΦu, hfix]

end Work.FBif

end
