import ChallengeDeps
import Submission.PotWords
import Submission.Q0Convex
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Sub-lemma (c) — the FS `lm:w2>w1` kernel comparisons at the chosen kernels

The FS small-box replay (`lm:appinteractionestimate`, `lm:appbogolubov`,
`thm:smallbox`; final_v2.tex eq:w1>/eq:w>g/eq:wepsilong) needs the kernel
comparisons between the two renormalized pair kernels `w₁ := wPair(g₀)` and
`w₂ := wPair(g₂)`, `g₂ := g₀(1+ω₀)` (`ω₀ := Classical.choose h` the chosen
scattering solution, `0 ≤ ω₀ ≤ 1` a.e.).  In the corpus the box-boundary
corrections of FS (the `(1−C(R/λ₁)²)(1−C(R/ℓd)²)` factors) vanish exactly
(`R ≤ ℓ·chiR0` kills the support off `ball 0 R`), so `lm:w2>w1` reduces to
the exact identities

    wPair(ℓ, g₂) = wPair(ℓ, g₀) + wPair(ℓ, g₀·ω₀)          (pointwise)
    ∫g₂ = ∫g₀ + ∫(g₀·ω₀) = 8π·a v + ∫(g₀·ω₀)               (mass)
    ∬_{acube²} wPair(g₂) = ∬_{acube²} wPair(g₁) + ℓ³·∫(g₀·ω₀)
    with 0 ≤ ∫(g₀·ω₀) ≤ 8π·a v   (chosen_gomega_integral_bounds)

— the corpus transcription of FS eq:w>g / eq:w1> (the `w₁`-value
`∬w₁ = 8π(a v)·ℓ³` is `Q0Chosen.w1c_acube_integral`, the `w₂`-value
`∬w₂ = ℓ³·∫g₂` is `Q0Chosen.w2c_acube_integral`).  Any per-sector A₀
comparison consuming the Bogoliubov/`ĝω(0)`-type error terms
(`−½(∫g₀ω₀)·(cS2-form)`) will rewrite them through these exact identities.

Standing chosen-branch hypotheses (as in `Q0Chosen`/`ScatKernelChosen`):
`(hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
(hv_supp : tsupport v ⊆ ball (0:ℝ³) R)
(h : ∃ w, IsRadial w ∧ IsScatteringSolution w v) (hℓ : 0 < ℓ)
(hRℓ : R ≤ ℓ * chiR0)`.

## Route notes
* `wPair` is ℝ-linear in the numerator `h` (division is total on ℝ:
  `add_div` holds for every `c`, zero included) — `wPair_add`.
* `g₂ = g₀ + g₀·ω₀` pointwise by `ring` (`g0`/`g2` are definitions).
* The `∬`-identity for `g₀ω₀` is the exact clone of
  `Q0Chosen.w1c_acube_integral` with `h := g₀·ω₀` (integrable by
  `ScatKernelChosen.g0w0_integrable`, support from
  `g0_zero_of_norm_ge`), then `integral_add` of the pointwise split.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## `wPair` is linear in the numerator -/

/-- Pointwise: the χ-renormalized pair kernel is additive in the numerator
`h` (total division on ℝ). -/
lemma wPair_add {ℓ : ℝ} {h1 h2 : ℝ³ → ℝ} (x y : ℝ³) :
    wPair ℓ (h1 + h2) x y = wPair ℓ h1 x y + wPair ℓ h2 x y := by
  unfold wPair wScaled
  rw [Pi.add_apply, add_div]
  ring

/-- Curried version (`wPairC`). -/
lemma wPairC_add {ℓ : ℝ} {h1 h2 : ℝ³ → ℝ} (x y : ℝ³) :
    wPairC ℓ (h1 + h2) x y = wPairC ℓ h1 x y + wPairC ℓ h2 x y := by
  exact wPair_add (ℓ := ℓ) (h1 := h1) (h2 := h2) x y

/-- Uncurried version (`wPairU`). -/
lemma wPairU_add {ℓ : ℝ} {h1 h2 : ℝ³ → ℝ} (p : ℝ³ × ℝ³) :
    wPairU ℓ (h1 + h2) p = wPairU ℓ h1 p + wPairU ℓ h2 p := by
  exact wPair_add (ℓ := ℓ) (h1 := h1) (h2 := h2) p.1 p.2

/-! ## The chosen-kernel `g₂ = g₀ + g₀·ω₀` split -/

/-- Pointwise at the chosen kernels: `g₂ = g₀ + g₀·ω₀` (`ω₀ := Classical.choose h`). -/
lemma g2_eq_g0_add_g0w0 {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (x : ℝ³) :
    g2 v h x = g0 v h x + g0 v h x * Classical.choose h x := by
  unfold g2 g0
  ring

/-- Pointwise: the `w₂`-pair kernel is `w₁` plus the `g₀ω₀`-pair kernel. -/
lemma wPairC_g2_eq_w1_add_g0w0 {ℓ : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (x y : ℝ³) :
    wPairC ℓ (g2 v h) x y =
      wPairC ℓ (g0 v h) x y
        + wPairC ℓ (fun z : ℝ³ => g0 v h z * Classical.choose h z) x y := by
  have hfun : g2 v h = g0 v h + (fun z : ℝ³ => g0 v h z * Classical.choose h z) := by
    funext z
    exact g2_eq_g0_add_g0w0 h z
  rw [hfun]
  exact wPairC_add (ℓ := ℓ) (h1 := g0 v h)
    (h2 := fun z : ℝ³ => g0 v h z * Classical.choose h z) x y

/-- Mass identity: `∫g₂ = ∫g₀ + ∫(g₀·ω₀) = 8π·a v + ∫(g₀·ω₀)`. -/
theorem g2_integral_eq_g0_add_g0w0 {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    (∫ x : ℝ³, g2 v h x) =
      (∫ x : ℝ³, g0 v h x)
        + (∫ x : ℝ³, g0 v h x * Classical.choose h x) := by
  have hfun : (fun x : ℝ³ => g2 v h x) =
      (fun x : ℝ³ => g0 v h x)
        + (fun x : ℝ³ => g0 v h x * Classical.choose h x) := by
    funext x
    exact g2_eq_g0_add_g0w0 h x
  have hg0 : MeasureTheory.Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hg0w0 : MeasureTheory.Integrable
      (fun x : ℝ³ => g0 v h x * Classical.choose h x) :=
    g0w0_integrable hR hv_nonneg hvrad hv_supp h
  rw [hfun]
  exact integral_add hg0 hg0w0

/-- Mass-form of the corpus `eq:w>g`:
`∫g₂ = 8π·a v + ∫(g₀·ω₀)` with `0 ≤ ∫(g₀·ω₀) ≤ 8π·a v`
(`chosen_gomega_integral_bounds`). -/
theorem g2_integral_eq_av_add_g0w0 {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    (∫ x : ℝ³, g2 v h x) =
      8 * π * a v + (∫ x : ℝ³, g0 v h x * Classical.choose h x) := by
  have hsplit := g2_integral_eq_g0_add_g0w0 hR hv_nonneg hvrad hv_supp h
  rw [g0_integral hR hv_supp h] at hsplit
  exact hsplit

/-! ## The `∬`-identity for the `g₀ω₀`-pair kernel over the centred cube -/

/-- `wPair(g₀ω₀)` is integrable over the product cube (chosen branch, dilute). -/
lemma integrableOn_g0w0_pair_acube {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    IntegrableOn (wPairU ℓ (fun z : ℝ³ => g0 v h z * Classical.choose h z))
      (acube ℓ ×ˢ acube ℓ) := by
  let g : ℝ³ → ℝ := fun z : ℝ³ => g0 v h z * Classical.choose h z
  have hgI : MeasureTheory.Integrable g := by
    simpa [g] using (g0w0_integrable hR hv_nonneg hvrad hv_supp h)
  have hgsupp : ∀ z : ℝ³, R ≤ ‖z‖ → g z = 0 := by
    intro z hz
    have hz0 : g0 v h z = 0 := g0_zero_of_norm_ge hv_supp hz h
    simp [g, hz0]
  simpa [g] using integrableOn_wPairU_of (ℓ := ℓ) (R := R) hℓ hgI hgsupp (le_of_lt hR) hRℓ

/-- `∬_{acube²} wPair(g₀ω₀) = ℓ³·∫(g₀ω₀)` (the cube-level mass of the
`w₂ − w₁`-pair kernel). -/
lemma g0w0c_acube_integral {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (fun z : ℝ³ => g0 v h z * Classical.choose h z) p)
      = ℓ ^ 3 * (∫ z : ℝ³, g0 v h z * Classical.choose h z) := by
  let g : ℝ³ → ℝ := fun z : ℝ³ => g0 v h z * Classical.choose h z
  have hgI : MeasureTheory.Integrable g := by
    simpa [g] using (g0w0_integrable hR hv_nonneg hvrad hv_supp h)
  have hgsupp : ∀ z : ℝ³, R ≤ ‖z‖ → g z = 0 := by
    intro z hz
    have hz0 : g0 v h z = 0 := g0_zero_of_norm_ge hv_supp hz h
    simp [g, hz0]
  have hwi : IntegrableOn (wPairU ℓ g) (acube ℓ ×ˢ acube ℓ) :=
    integrableOn_wPairU_of (ℓ := ℓ) (R := R) hℓ hgI hgsupp (le_of_lt hR) hRℓ
  calc
    (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (fun z : ℝ³ => g0 v h z * Classical.choose h z) p)
        = (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ g p) := by rfl
    _ = ∫ x : ℝ³, ∫ y : ℝ³, wPair ℓ g x y := by
          simpa [g] using (wPairU_cube_integral_eq_full hℓ (h := g) hwi)
    _ = ℓ ^ 3 * (∫ z : ℝ³, g z) :=
          wPair_double_full_integral (ℓ := ℓ) (R := R) hℓ hgI hgsupp hRℓ
    _ = ℓ ^ 3 * (∫ z : ℝ³, g0 v h z * Classical.choose h z) := by rfl

/-! ## The corpus `eq:w>g` — `∬w₂ = ∬w₁ + ℓ³·∫(g₀ω₀)` -/

/-- **Corpus `eq:w>g`**: over the centred cube, `∬w₂ = ∬w₁ + ℓ³·∫(g₀·ω₀)`.
(`∬w₁ = 8π(a v)·ℓ³` by `w1c_acube_integral`, `∬w₂ = ℓ³·∫g₂` by
`w2c_acube_integral`, and `∫g₂ = 8π(a v) + ∫g₀ω₀` by the mass identity.) -/
theorem w2c_acube_integral_eq_w1c_add_g0w0 {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g2 v h) p)
      = (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g0 v h) p)
        + ℓ ^ 3 * (∫ z : ℝ³, g0 v h z * Classical.choose h z) := by
  let g0w0 : ℝ³ → ℝ := fun z : ℝ³ => g0 v h z * Classical.choose h z
  have hfun : (fun p : ℝ³ × ℝ³ => wPairU ℓ (g2 v h) p)
      = fun p : ℝ³ × ℝ³ => wPairU ℓ (g0 v h) p + wPairU ℓ g0w0 p := by
    funext p
    have hsplit := wPairC_g2_eq_w1_add_g0w0 (ℓ := ℓ) (v := v) h p.1 p.2
    simpa [g0w0, wPairU, wPairC] using hsplit
  have hw1i : IntegrableOn (wPairU ℓ (g0 v h)) (acube ℓ ×ˢ acube ℓ) :=
    integrableOn_w1c_acube hR hv_supp h hℓ hRℓ
  have hw0i : IntegrableOn (wPairU ℓ g0w0) (acube ℓ ×ˢ acube ℓ) := by
    simpa [g0w0] using (integrableOn_g0w0_pair_acube hR hv_nonneg hvrad hv_supp h hℓ hRℓ)
  calc
    (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g2 v h) p)
        = (∫ p in acube ℓ ×ˢ acube ℓ,
            wPairU ℓ (g0 v h) p + wPairU ℓ g0w0 p) := by
          rw [hfun]
    _ = (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g0 v h) p)
        + (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ g0w0 p) :=
          integral_add hw1i hw0i
    _ = (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g0 v h) p)
        + ℓ ^ 3 * (∫ z : ℝ³, g0 v h z * Classical.choose h z) := by
          congr 1
          simpa [g0w0] using (g0w0c_acube_integral hR hv_nonneg hvrad hv_supp h hℓ hRℓ)

/-- **Corpus `eq:w>g`, inequality form**: `∬w₁ ≤ ∬w₂` over the centred cube
(`∫g₀ω₀ ≥ 0` by `chosen_gomega_integral_bounds`). -/
theorem w2c_acube_integral_ge_w1c {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g0 v h) p)
      ≤ (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g2 v h) p) := by
  have heq := w2c_acube_integral_eq_w1c_add_g0w0 hR hv_nonneg hvrad hv_supp h hℓ hRℓ
  have hb := chosen_gomega_integral_bounds hR hv_nonneg hvrad hv_supp h
  have hw0nn : 0 ≤ (∫ z : ℝ³, g0 v h z * Classical.choose h z) := by
    simpa [g0] using hb.1
  have hℓ3 : 0 ≤ ℓ ^ 3 := pow_nonneg (le_of_lt hℓ) 3
  rw [heq]
  nlinarith [mul_nonneg hw0nn hℓ3]

/-- The excess mass of `w₂` over `w₁` on the cube is exactly `ℓ³·∫(g₀·ω₀)`
(a `≥ 0` quantity). -/
theorem w2c_sub_w1c_integral_eq {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g2 v h) p)
        - (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g0 v h) p)
      = ℓ ^ 3 * (∫ z : ℝ³, g0 v h z * Classical.choose h z) := by
  have heq := w2c_acube_integral_eq_w1c_add_g0w0 hR hv_nonneg hvrad hv_supp h hℓ hRℓ
  nlinarith

/-- **Exact-kernel Q0 repulsion (the `w₂`-exact `∫g₂`-form)**: for a
NORMALISED state the q0-word (whose value is `½ℓ⁻³(∫g₂)·cS2 − 8πa v·μ·cS1`,
`Q0Ren.q0_chosen_expect`) is at least the surrogate square-completion
(`q0RenVal_repulsion`-type, coefficient `8πa`) PLUS the explicit
`ĝω(0)`-slack `½ℓ⁻³(∫g₀ω₀)·(cS1²−cS1) ≥ 0` from the corpus `eq:w>g`
(`∫g₂ = 8πa + ∫g₀ω₀`): with `S := cS1 ℓ Φ`,

    q0word ≥ (4πa/ℓ³)(S − μℓ³ − ½)² − 4πaμ²ℓ³(1 + 1/(2μℓ³))²
             + ½ℓ⁻³(∫g₀ω₀)·(S² − S) . -/
theorem q0word_exact_repulsion {N : ℕ} {v : ℝ³ → ℝ} {R ℓ μ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (hμ : 0 < μ) {Φ : XN N → ℝ}
    (hΦc : Continuous Φ) (hnorm : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1) :
    (4 * π * (a v) / ℓ ^ 3) * (cS1 ℓ Φ - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2
        - (4 * π * (a v)) * μ ^ 2 * ℓ ^ 3 * (1 + 1 / (2 * μ * ℓ ^ 3)) ^ 2
        + (1 / 2) * (ℓ ^ 3)⁻¹ * (∫ z : ℝ³, g0 v h z * Classical.choose h z)
            * (cS1 ℓ Φ ^ 2 - cS1 ℓ Φ)
      ≤ q0word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ := by
  have hcs : cS1 ℓ Φ * cS1 ℓ Φ - cS1 ℓ Φ ≤ cS2 ℓ Φ :=
    cS2_ge_sq_sub_self hℓ hΦc hnorm
  have hval : q0word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ =
      (1 / 2) * (ℓ ^ 3)⁻¹ * (∫ z : ℝ³, g2 v h z) * cS2 ℓ Φ
        - (8 * π * a v) * μ * cS1 ℓ Φ := by
    exact q0_chosen_expect (N := N) (v := v) (R := R) (ℓ := ℓ) hR hv_nonneg hvrad hv_supp
      h hℓ hRℓ μ (Φ := Φ) hΦc
  have hg2 := g2_integral_eq_av_add_g0w0 hR hv_nonneg hvrad hv_supp h
  have hav : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hM : 0 ≤ 8 * π * a v + (∫ z : ℝ³, g0 v h z * Classical.choose h z) := by
    have hb := chosen_gomega_integral_bounds hR hv_nonneg hvrad hv_supp h
    have hw0nn : 0 ≤ (∫ z : ℝ³, g0 v h z * Classical.choose h z) := by
      simpa [g0] using hb.1
    nlinarith
  have hcoef : 0 ≤ (1 / 2) * (ℓ ^ 3)⁻¹ := by positivity
  have hmul : (1 / 2) * (ℓ ^ 3)⁻¹ * (8 * π * a v + (∫ z : ℝ³, g0 v h z * Classical.choose h z))
        * (cS1 ℓ Φ * cS1 ℓ Φ - cS1 ℓ Φ)
      ≤ (1 / 2) * (ℓ ^ 3)⁻¹ * (8 * π * a v + (∫ z : ℝ³, g0 v h z * Classical.choose h z))
        * cS2 ℓ Φ := by
    exact mul_le_mul_of_nonneg_left hcs (mul_nonneg hcoef hM)
  have hc : (1 / 2) * (ℓ ^ 3)⁻¹ * (8 * π * a v) = 4 * π * (a v) / ℓ ^ 3 := by
    field_simp [ne_of_gt hℓ]
    ring
  have hsq := q0c_square_identity (a v) μ ℓ (cS1 ℓ Φ) (ne_of_gt hℓ) (ne_of_gt hμ)
  calc
    (4 * π * (a v) / ℓ ^ 3) * (cS1 ℓ Φ - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2
        - (4 * π * (a v)) * μ ^ 2 * ℓ ^ 3 * (1 + 1 / (2 * μ * ℓ ^ 3)) ^ 2
        + (1 / 2) * (ℓ ^ 3)⁻¹ * (∫ z : ℝ³, g0 v h z * Classical.choose h z)
            * (cS1 ℓ Φ ^ 2 - cS1 ℓ Φ)
        = (4 * π * (a v) / ℓ ^ 3) * (cS1 ℓ Φ ^ 2 - cS1 ℓ Φ)
            - (8 * π * a v) * μ * cS1 ℓ Φ
            + (1 / 2) * (ℓ ^ 3)⁻¹ * (∫ z : ℝ³, g0 v h z * Classical.choose h z)
                * (cS1 ℓ Φ ^ 2 - cS1 ℓ Φ) := by
          rw [← hsq]
    _ ≤ (1 / 2) * (ℓ ^ 3)⁻¹ * (8 * π * a v + (∫ z : ℝ³, g0 v h z * Classical.choose h z))
          * cS2 ℓ Φ - (8 * π * a v) * μ * cS1 ℓ Φ := by
          rw [← hc]
          nlinarith [hmul]
    _ = (1 / 2) * (ℓ ^ 3)⁻¹ * (∫ z : ℝ³, g2 v h z) * cS2 ℓ Φ
          - (8 * π * a v) * μ * cS1 ℓ Φ := by
          rw [hg2]
    _ = q0word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ := hval.symm

end BoseGases

end Submission
