/-
# `Work.FTS.LocData.hLoc_hk` — the bump `hLoc α = φ·Γ` lies in `𝓗⁴`, with a finite `𝓗⁴`-norm

The target of this module is

  `Work.Spaces.HkMem α 4 (hLoc α) ∧ ∃ C, 0 ≤ C ∧ Work.Spaces.HkSq α 4 (hLoc α) ≤ C`

for `0 < α ≤ 1`, where `hLoc α z θ = bumpZ z · Γ(θ)` is the concrete bump of the
localisation chapter (node N9 of the route): `bumpZ z = χ(4z - 5)` is supported in
`[3/4, 7/4]` and `Γ(θ) = (sinθ cos²θ)^{α/3}`.

The proof is the "membership by domination" of the chapter
(`Work.FTS.LocData.HkMem_of_majorant`) with the pointwise majorant

  `M z θ = K² · angMaj α θ / (1+z)²`,

together with the explicit evaluation `∫_{Iz} (1+z)^{-2} ≤ 2`.

## Mathematics

`D_z = z∂_z` does not touch `θ` and `D_θ = sin(2θ)∂_θ` does not touch `z`, so for a product
`B(z)·G(θ)` one has

* `D_z^c (B·G) = (D_z^c B)·G` (`DzIter_bumpZ_mul`),
* `D_θ^i (B·G) = B·(D_θ^i G)` (`DthIter_bumpZ_mul`), hence
  `D_z^jD_θ^i (B·G) = (D_z^j B)·(D_θ^i G)` (`mixed_bumpZ_mul`).

So, with `B_i = D_z^i bumpZ` and `G_i = D_θ^i Γ`,

  `HkIntegrand α 4 (hLoc α) z θ = ∑_{i≤4} (B_i·Γ·w/sin^{η/2})²
      + ∑_{1≤i, i+j≤4} (B_j·G_i·W)²`,

and each summand is the product of a *radial* block `(B_j·w)²` and an *angular* block.
The radial blocks are bounded by `D² · w(z)²` with `D` a bound for the five iterates of `D_z` on
`bumpZ` (`DzIter_bumpZ_bound`), while the angular blocks are dominated by the two summands of
`angMaj`:

* `Γ²·sin^{-η}` (`Gam_sq_rpow_le_angMaj_eta`),
* `G_i²·sin^{-γ} ≤ 10^{10}·Γ²·sin^{-γ}` (`DthIter_Gam_abs_le`, i.e. `|D_θ^iΓ| ≤ 10⁵·Γ`).

Finally `w(z)²(1+z)² ≤ 1400` on the *support* `[3/4,7/4]` (`w_sq_mul_le`), and strictly outside
the support every `B_j` vanishes identically (`T1_iterate_contDiff`), so the integrand is `0`
there and the majorant `K²·angMaj/(1+z)² ≥ 0` dominates it.  `K = 10⁸·D` absorbs the
`5 + 25·10^{10}` summands.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.SmoothQuad_hLoc
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.LocData.angMaj_mem
import Submission.Work.FTS.LocData.DzIter_bumpZ_bound
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le
import Submission.Work.Spaces.GammaW_Prelim
import Submission.Work.FTS.H2.InvOneAddSq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The `ℋ⁴`-derivatives of the separated bump `bumpZ z · Γ(θ)` -/

/-- The bump is the pointwise product of its two factors. -/
theorem hLoc_eq_fun (α : ℝ) : hLoc α = fun z θ => bumpZ z * Work.Spaces.Gam α θ := rfl

/-- `D_z^c` of a product `B(z)·G(θ)` only differentiates the radial factor. -/
theorem DzIter_bumpZ_mul (G : ℝ → ℝ) (c : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter c (fun z θ => bumpZ z * G θ) z θ
      = Work.Spaces.DzIter c (fun z _ => bumpZ z) z θ * G θ := by
  induction c generalizing z with
  | zero => rfl
  | succ c ih =>
      rw [Work.Spaces.DzIter_succ]
      show z * deriv (fun z' => Work.Spaces.DzIter c (fun z θ => bumpZ z * G θ) z' θ) z
        = z * deriv (fun z' => Work.Spaces.DzIter c (fun z _ => bumpZ z) z' θ) z * G θ
      have hfun : (fun z' : ℝ => Work.Spaces.DzIter c (fun z θ => bumpZ z * G θ) z' θ)
          = fun z' => Work.Spaces.DzIter c (fun z _ => bumpZ z) z' θ * G θ := by
        funext z'; exact ih z'
      rw [hfun, deriv_mul_const_field]
      ring

/-- `D_θ^i` of a product `B(z)·G(θ)` only differentiates the angular factor. -/
theorem DthIter_bumpZ_mul (G : ℝ → ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun z θ => bumpZ z * G θ) z θ
      = bumpZ z * (Work.Spaces.dthU^[i] G) θ := by
  induction i generalizing θ with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ]
      show Real.sin (2 * θ)
          * deriv (fun θ' => Work.Spaces.DthIter i (fun z θ => bumpZ z * G θ) z θ') θ
        = bumpZ z * (Work.Spaces.dthU^[i.succ] G) θ
      have hfun : (fun θ' : ℝ => Work.Spaces.DthIter i (fun z θ => bumpZ z * G θ) z θ')
          = fun θ' => bumpZ z * (Work.Spaces.dthU^[i] G) θ' := by
        funext θ'; exact ih θ'
      rw [hfun, deriv_const_mul_field]
      rw [Function.iterate_succ_apply', Work.Spaces.dthU]
      ring

/-- The mixed derivative of the separated bump: `D_z^jD_θ^i (B·G) = (D_z^jB)·(D_θ^iG)`. -/
theorem mixed_bumpZ_mul (G : ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => bumpZ z * G θ) z θ
      = Work.Spaces.DzIter j (fun z _ => bumpZ z) z θ * (Work.Spaces.dthU^[i] G) θ := by
  have h : Work.Spaces.DthIter i (fun z θ => bumpZ z * G θ)
      = fun z θ => bumpZ z * (Work.Spaces.dthU^[i] G) θ := by
    funext z θ; exact DthIter_bumpZ_mul G i z θ
  rw [Work.Spaces.mixed, h, DzIter_bumpZ_mul (Work.Spaces.dthU^[i] G) j z θ]

/-! ## `rpow` bookkeeping and the two "separated square" identities -/

/-- `(b / s^e)² = b²·s^{-2e}`, valid for `s ≥ 0` (both sides vanish at `s = 0`). -/
theorem div_rpow_sq (b s e : ℝ) (hs : 0 ≤ s) : (b / s ^ e) ^ 2 = b ^ 2 * s ^ (-(2 * e)) := by
  rw [div_pow, div_eq_mul_inv]
  have h : (s ^ e) ^ 2 = s ^ (2 * e) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    ring_nf
  rw [h, ← Real.rpow_neg hs]

/-- The square of a `D_z`-summand factorises into its radial and angular blocks. -/
theorem sep_sq1 (B G w s e : ℝ) (hs : 0 ≤ s) :
    (B * G * (w / s ^ (e / 2))) ^ 2 = (B * w) ^ 2 * (G ^ 2 * s ^ (-e)) := by
  rw [show B * G * (w / s ^ (e / 2)) = B * G * w / s ^ (e / 2) by ring, div_rpow_sq _ _ _ hs]
  rw [show -(2 * (e / 2)) = -e by ring]
  ring

/-- The square of a mixed-summand factorises into its radial and angular blocks. -/
theorem sep_sq2 (B G w s g : ℝ) (hs : 0 ≤ s) :
    (B * G * (w * s ^ (-(g / 2)))) ^ 2 = (B * w) ^ 2 * (G ^ 2 * s ^ (-g)) := by
  rw [show B * G * (w * s ^ (-(g / 2))) = (B * G * w) * s ^ (-(g / 2)) by ring, mul_pow]
  rw [show (s ^ (-(g / 2))) ^ 2 = s ^ (-g) from by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]; congr 1; ring]
  ring

/-! ## Angular bounds -/

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  apply Real.sin_nonneg_of_mem_Icc
  exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- The `η`-summand of `angMaj`. -/
theorem Gam_sq_rpow_le_angMaj_eta (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ≤ angMaj α θ := by
  have hs0 := sin_two_nonneg hθ
  rw [angMaj_apply]
  have h1 : 0 ≤ Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  linarith

/-- The `γ`-summand of `angMaj`. -/
theorem Gam_sq_rpow_le_angMaj_gam (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ angMaj α θ := by
  have hs0 := sin_two_nonneg hθ
  rw [angMaj_apply]
  have h1 : 0 ≤ Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  linarith

/-- The angular jet of `Γ`: `|D_θ^i Γ(θ)| ≤ 10⁵·Γ(θ)` on `Iθ`, for `i ≤ 4`. -/
theorem dthU_Gam_abs_le (i : ℕ) (hi : i ≤ 4) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |(Work.Spaces.dthU^[i] (fun θ' => Work.Spaces.Gam α θ')) θ| ≤ 100000 * Work.Spaces.Gam α θ := by
  have h := DthIter_Gam_abs_le i hi α hα hα1 hθ
  rwa [DthIter_rad_eq i (fun θ' => Work.Spaces.Gam α θ') 0 θ] at h

/-! ## The radial weight on the support of the bump -/

/-- On the support `[3/4, 7/4]` of `bumpZ`, the square of the radial weight is bounded by
`1400/(1+z)²`. -/
theorem w_sq_mul_le {z : ℝ} (h1 : 3 / 4 ≤ z) (h2 : z ≤ 7 / 4) :
    Work.Spaces.w z ^ 2 * (1 + z) ^ 2 ≤ 1400 := by
  have hz0 : z ≠ 0 := by linarith
  have hkey : Work.Spaces.w z ^ 2 * (1 + z) ^ 2 = (1 + z) ^ 6 / z ^ 4 := by
    rw [Work.Spaces.w]; field_simp
  rw [hkey]
  have hnum : (1 + z) ^ 6 ≤ (11 / 4) ^ 6 := by
    have h : 1 + z ≤ 11 / 4 := by linarith
    exact pow_le_pow_left₀ (by linarith) h 6
  have hden : (3 / 4 : ℝ) ^ 4 ≤ z ^ 4 := pow_le_pow_left₀ (by norm_num) h1 4
  have h3 : (0 : ℝ) < (3 / 4 : ℝ) ^ 4 := by norm_num
  calc (1 + z) ^ 6 / z ^ 4 ≤ (11 / 4) ^ 6 / (3 / 4 : ℝ) ^ 4 :=
        div_le_div₀ (by positivity) hnum h3 hden
    _ ≤ 1400 := by norm_num

/-! ## The two per-summand bounds -/

/-- A `D_z`-summand of the `ℋ⁴`-integrand of the bump. -/
theorem hLoc_dz_term_le (α : ℝ) {D z θ : ℝ} (hz : 0 ≤ z)
    (hA : ∀ i : ℕ, i ≤ 4 → (Work.Spaces.DzIter i (fun z _ => bumpZ z) z θ) ^ 2 ≤ D ^ 2)
    (hw : Work.Spaces.w z ^ 2 * (1 + z) ^ 2 ≤ 1400)
    (hθ : θ ∈ Work.Spaces.Iθ) (i : ℕ) (hi : i ≤ 4) :
    (Work.Spaces.DzIter i (hLoc α) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ D ^ 2 * 1400 * angMaj α θ / (1 + z) ^ 2 := by
  have hs0 := sin_two_nonneg hθ
  have hw' : Work.Spaces.w z ^ 2 ≤ 1400 / (1 + z) ^ 2 := by
    rw [le_div_iff₀ (by nlinarith : (0 : ℝ) < (1 + z) ^ 2)]
    exact hw
  have hbw : (Work.Spaces.DzIter i (fun z _ => bumpZ z) z θ * Work.Spaces.w z) ^ 2
      ≤ D ^ 2 * (1400 / (1 + z) ^ 2) := by
    rw [mul_pow]
    exact mul_le_mul (hA i hi) hw' (sq_nonneg _) (sq_nonneg _)
  have hang := Gam_sq_rpow_le_angMaj_eta α hθ
  have hsep : Work.Spaces.DzIter i (hLoc α) z θ
      = Work.Spaces.DzIter i (fun z _ => bumpZ z) z θ * Work.Spaces.Gam α θ := by
    rw [hLoc_eq_fun]
    exact DzIter_bumpZ_mul (Work.Spaces.Gam α) i z θ
  calc (Work.Spaces.DzIter i (hLoc α) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter i (fun z _ => bumpZ z) z θ * Work.Spaces.w z) ^ 2
          * (Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
        rw [hsep]
        exact sep_sq1 _ _ _ _ _ hs0
    _ ≤ (D ^ 2 * (1400 / (1 + z) ^ 2)) * angMaj α θ :=
        mul_le_mul hbw hang (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)) (by positivity)
    _ = D ^ 2 * 1400 * angMaj α θ / (1 + z) ^ 2 := by ring

/-- A mixed summand of the `ℋ⁴`-integrand of the bump. -/
theorem hLoc_mixed_term_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {D z θ : ℝ} (hz : 0 ≤ z)
    (hA : ∀ i : ℕ, i ≤ 4 → (Work.Spaces.DzIter i (fun z _ => bumpZ z) z θ) ^ 2 ≤ D ^ 2)
    (hw : Work.Spaces.w z ^ 2 * (1 + z) ^ 2 ≤ 1400)
    (hθ : θ ∈ Work.Spaces.Iθ) (j i : ℕ) (hi : i ≤ 4) (hij : i + j ≤ 4) :
    (Work.Spaces.mixed j i (hLoc α) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 10 ^ 10 * (D ^ 2 * 1400) * angMaj α θ / (1 + z) ^ 2 := by
  have hs0 := sin_two_nonneg hθ
  have hj4 : j ≤ 4 := by omega
  have hw' : Work.Spaces.w z ^ 2 ≤ 1400 / (1 + z) ^ 2 := by
    rw [le_div_iff₀ (by nlinarith : (0 : ℝ) < (1 + z) ^ 2)]
    exact hw
  have hbw : (Work.Spaces.DzIter j (fun z _ => bumpZ z) z θ * Work.Spaces.w z) ^ 2
      ≤ D ^ 2 * (1400 / (1 + z) ^ 2) := by
    rw [mul_pow]
    exact mul_le_mul (hA j hj4) hw' (sq_nonneg _) (sq_nonneg _)
  have hdth : ((Work.Spaces.dthU^[i] (fun θ' => Work.Spaces.Gam α θ')) θ) ^ 2
      ≤ 10 ^ 10 * (Work.Spaces.Gam α θ) ^ 2 := by
    have h := dthU_Gam_abs_le i hi α hα hα1 hθ
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs, mul_pow] at h2
    norm_num at h2 ⊢
    linarith
  have hang : ((Work.Spaces.dthU^[i] (fun θ' => Work.Spaces.Gam α θ')) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ 10 ^ 10 * angMaj α θ := by
    have h1 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hs0 _
    calc _ ≤ (10 ^ 10 * (Work.Spaces.Gam α θ) ^ 2)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_right hdth h1
      _ = 10 ^ 10
            * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
      _ ≤ 10 ^ 10 * angMaj α θ :=
          mul_le_mul_of_nonneg_left (Gam_sq_rpow_le_angMaj_gam α hθ) (by norm_num)
  have hsep : Work.Spaces.mixed j i (hLoc α) z θ
      = Work.Spaces.DzIter j (fun z _ => bumpZ z) z θ
          * (Work.Spaces.dthU^[i] (fun θ' => Work.Spaces.Gam α θ')) θ := by
    rw [hLoc_eq_fun]
    exact mixed_bumpZ_mul (Work.Spaces.Gam α) j i z θ
  calc (Work.Spaces.mixed j i (hLoc α) z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.DzIter j (fun z _ => bumpZ z) z θ * Work.Spaces.w z) ^ 2
          * (((Work.Spaces.dthU^[i] (fun θ' => Work.Spaces.Gam α θ')) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
        rw [hsep, Work.Spaces.Wt, Work.Spaces.wTheta]
        exact sep_sq2 _ _ _ _ _ hs0
    _ ≤ (D ^ 2 * (1400 / (1 + z) ^ 2)) * (10 ^ 10 * angMaj α θ) :=
        mul_le_mul hbw hang (by positivity) (by positivity)
    _ = 10 ^ 10 * (D ^ 2 * 1400) * angMaj α θ / (1 + z) ^ 2 := by ring

/-! ## The pointwise bound on the `ℋ⁴`-integrand of the bump -/

/-- **The `ℋ⁴`-integrand of the bump is dominated by `K²·angMaj/(1+z)²`.**  This is the
pointwise input of `Work.FTS.LocData.HkMem_of_majorant` for the bump. -/
theorem HkIntegrand_hLoc_le_self (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (hLoc α) z θ ≤ K ^ 2 * angMaj α θ / (1 + z) ^ 2 := by
  obtain ⟨Cb, hCb⟩ := DzIter_bumpZ_bound
  set D : ℝ := |Cb| + 1 with hDdef
  have hD0 : 0 ≤ D := by positivity
  have hDb : ∀ c ≤ 4, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      (Work.Spaces.DzIter c (fun z _ => bumpZ z) z θ) ^ 2 ≤ D ^ 2 := by
    intro c hc z hz θ
    have h := hCb c hc z hz θ
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs] at h2
    have h3 : Cb ^ 2 ≤ D ^ 2 := by
      rw [hDdef]
      nlinarith [abs_nonneg Cb, sq_abs Cb]
    linarith
  have hKsq : 5 * (D ^ 2 * 1400) + 25 * (10 ^ 10 * (D ^ 2 * 1400)) ≤ (10 ^ 8 * D) ^ 2 := by
    nlinarith [hD0, sq_nonneg D]
  refine ⟨10 ^ 8 * D, by positivity, ?_⟩
  intro z hz θ hθ
  have hz0 : 0 ≤ z := hz
  have hang0 : 0 ≤ angMaj α θ := angMaj_nonneg hθ
  have hden : 0 ≤ (1 + z) ^ 2 := by positivity
  have hA : ∀ i : ℕ, i ≤ 4 → (Work.Spaces.DzIter i (fun z _ => bumpZ z) z θ) ^ 2 ≤ D ^ 2 :=
    fun i hi => hDb i hi z hz θ
  by_cases hzmem : z ∈ Set.Icc (3 / 4 : ℝ) (7 / 4)
  · have hw := w_sq_mul_le hzmem.1 hzmem.2
    rw [Work.Spaces.HkIntegrand]
    have hT1 : (∑ i ∈ Finset.range (4 + 1),
          (Work.Spaces.DzIter i (hLoc α) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ 5 * (D ^ 2 * 1400 * angMaj α θ / (1 + z) ^ 2) := by
      calc _ ≤ ∑ _i ∈ Finset.range (4 + 1), (D ^ 2 * 1400 * angMaj α θ / (1 + z) ^ 2) :=
            Finset.sum_le_sum (fun i hi => by
              rw [Finset.mem_range] at hi
              exact hLoc_dz_term_le α hz0 hA hw hθ i (by omega))
        _ = 5 * (D ^ 2 * 1400 * angMaj α θ / (1 + z) ^ 2) := by
            rw [Finset.sum_const, Finset.card_range]
            norm_num
    have hT2 : (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
          if 1 ≤ i ∧ i + j ≤ 4
          then (Work.Spaces.mixed j i (hLoc α) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ 25 * (10 ^ 10 * (D ^ 2 * 1400) * angMaj α θ / (1 + z) ^ 2) := by
      calc _ ≤ ∑ _i ∈ Finset.range (4 + 1), ∑ _j ∈ Finset.range (4 + 1),
              (10 ^ 10 * (D ^ 2 * 1400) * angMaj α θ / (1 + z) ^ 2) :=
            Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => by
              by_cases hc : 1 ≤ i ∧ i + j ≤ 4
              · rw [if_pos hc]
                rw [Finset.mem_range] at hi hj
                exact hLoc_mixed_term_le α hα hα1 hz0 hA hw hθ j i (by omega) (by omega)
              · rw [if_neg hc]
                exact div_nonneg (mul_nonneg (by positivity) hang0) hden))
        _ = 25 * (10 ^ 10 * (D ^ 2 * 1400) * angMaj α θ / (1 + z) ^ 2) := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
    refine le_trans (add_le_add hT1 hT2) ?_
    have hcombo : 5 * (D ^ 2 * 1400 * angMaj α θ / (1 + z) ^ 2)
          + 25 * (10 ^ 10 * (D ^ 2 * 1400) * angMaj α θ / (1 + z) ^ 2)
        = (5 * (D ^ 2 * 1400) + 25 * (10 ^ 10 * (D ^ 2 * 1400)))
            * (angMaj α θ / (1 + z) ^ 2) := by ring
    have hnonneg : 0 ≤ angMaj α θ / (1 + z) ^ 2 := div_nonneg hang0 hden
    calc 5 * (D ^ 2 * 1400 * angMaj α θ / (1 + z) ^ 2)
          + 25 * (10 ^ 10 * (D ^ 2 * 1400) * angMaj α θ / (1 + z) ^ 2)
        = (5 * (D ^ 2 * 1400) + 25 * (10 ^ 10 * (D ^ 2 * 1400)))
            * (angMaj α θ / (1 + z) ^ 2) := hcombo
      _ ≤ (10 ^ 8 * D) ^ 2 * (angMaj α θ / (1 + z) ^ 2) :=
          mul_le_mul_of_nonneg_right hKsq hnonneg
      _ = (10 ^ 8 * D) ^ 2 * angMaj α θ / (1 + z) ^ 2 := by ring
  · have hzit : ∀ c : ℕ, Work.Spaces.DzIter c (fun z _ => bumpZ z) z θ = 0 := by
      intro c
      rw [DzIter_bumpZ_eq c θ z]
      exact (T1_iterate_contDiff BumpZ_contDiff bumpZ_eq_zero_of_notMem_Icc c).2 z hzmem
    have hDz0 : ∀ i : ℕ, Work.Spaces.DzIter i (hLoc α) z θ = 0 := by
      intro i
      show Work.Spaces.DzIter i (fun z θ => bumpZ z * Work.Spaces.Gam α θ) z θ = 0
      rw [DzIter_bumpZ_mul (Work.Spaces.Gam α) i z θ, hzit i, zero_mul]
    have hMx0 : ∀ j i : ℕ, Work.Spaces.mixed j i (hLoc α) z θ = 0 := by
      intro j i
      show Work.Spaces.mixed j i (fun z θ => bumpZ z * Work.Spaces.Gam α θ) z θ = 0
      rw [mixed_bumpZ_mul (Work.Spaces.Gam α) j i z θ, hzit j, zero_mul]
    have hzero : Work.Spaces.HkIntegrand α 4 (hLoc α) z θ = 0 := by
      simp only [Work.Spaces.HkIntegrand, hDz0, hMx0]
      simp
    rw [hzero]
    exact div_nonneg (mul_nonneg (sq_nonneg _) hang0) hden

/-! ## Integrability of the majorant -/

/-- The majorant `c·angMaj α θ/(1+z)²` has integrable `θ`-slices, and its `z`-integral is
integrable on `Iz`.  This is the `hMslice`/`hMz` pair of `HkMem_of_majorant` for `angMaj`. -/
theorem angMaj_majorant_integrable_self (α c : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (∀ z ∈ Work.Spaces.Iz,
        IntegrableOn (fun θ => c * angMaj α θ / (1 + z) ^ 2) Work.Spaces.Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, c * angMaj α θ / (1 + z) ^ 2)
        Work.Spaces.Iz := by
  obtain ⟨hint, _⟩ := angMaj_mem α hα hα1
  constructor
  · intro z _
    have h : IntegrableOn (fun θ => (c * ((1 + z) ^ 2)⁻¹) * angMaj α θ) Work.Spaces.Iθ :=
      hint.const_mul _
    refine h.congr_fun (fun θ _ => ?_) measurableSet_Icc
    ring
  · have hbase : IntegrableOn (fun x : ℝ => (x + 1) ^ (-2 : ℝ)) (Set.Ioi (0 : ℝ)) :=
      integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (by norm_num) (by norm_num)
    have hconst : IntegrableOn (fun x : ℝ => (∫ θ in Work.Spaces.Iθ, c * angMaj α θ)
        * (x + 1) ^ (-2 : ℝ)) (Set.Ioi (0 : ℝ)) :=
      hbase.const_mul _
    have heq : ∀ z ∈ Set.Ioi (0 : ℝ),
        (∫ θ in Work.Spaces.Iθ, c * angMaj α θ / (1 + z) ^ 2)
          = (∫ θ in Work.Spaces.Iθ, c * angMaj α θ) * (z + 1) ^ (-2 : ℝ) := by
      intro z hz
      rw [show (fun θ => c * angMaj α θ / (1 + z) ^ 2)
          = fun θ => (c * angMaj α θ) * ((1 + z) ^ 2)⁻¹ from by funext θ; ring]
      rw [integral_mul_const]
      congr 1
      rw [show (1 + z : ℝ) = z + 1 by ring]
      have hzpos : (0 : ℝ) < z + 1 := by have h : (0 : ℝ) < z := hz; linarith
      rw [Real.rpow_neg (le_of_lt hzpos)]
      norm_num
    have hcon : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, c * angMaj α θ / (1 + z) ^ 2)
        (Set.Ioi (0 : ℝ)) :=
      hconst.congr_fun (fun z hz => (heq z hz).symm) measurableSet_Ioi
    show Integrable (fun z => ∫ θ in Work.Spaces.Iθ, c * angMaj α θ / (1 + z) ^ 2)
      (volume.restrict (Set.Ici (0 : ℝ)))
    rw [← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
    exact hcon

/-! ## Membership in `𝓗⁴` -/

/-- **The bump lies in `𝓗⁴`** as soon as its `ℋ⁴`-integrand is dominated by
`K²·angMaj/(1+z)²`: the standard "membership by domination". -/
theorem HkMem_hLoc (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (K : ℝ)
    (hKmaj : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (hLoc α) z θ ≤ K ^ 2 * angMaj α θ / (1 + z) ^ 2) :
    Work.Spaces.HkMem α 4 (hLoc α) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 4 (hLoc α) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_HkIntegrand_smoothQuad α 4 (hLoc α) (SmoothQuad_hLoc α)
  refine HkMem_of_majorant α 4 hcont
    (angMaj_majorant_integrable_self α (K ^ 2) hα hα1).1
    (angMaj_majorant_integrable_self α (K ^ 2) hα hα1).2 ?_
  intro z hz θ hθ
  exact hKmaj z hz θ hθ

/-! ## The `𝓗⁴`-norm of the bump is finite -/

/-- **The squared `𝓗⁴`-norm of the bump is finite**, with the explicit bound
`(K²(1000/(3α)+10001))·2`. -/
theorem hLoc_HkSq_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {K : ℝ}
    (hmem : Work.Spaces.HkMem α 4 (hLoc α))
    (hKmaj : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (hLoc α) z θ ≤ K ^ 2 * angMaj α θ / (1 + z) ^ 2) :
    Work.Spaces.HkSq α 4 (hLoc α) ≤ (K ^ 2 * (1000 / (3 * α) + 10001)) * 2 := by
  obtain ⟨hintA, hbndA⟩ := angMaj_mem α hα hα1
  obtain ⟨hMslice, hMz⟩ := angMaj_majorant_integrable_self α (K ^ 2) hα hα1
  obtain ⟨hmem1, hmem2⟩ := hmem
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, angMaj α θ with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    refine integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact angMaj_nonneg hθ
  -- the inner (`θ`-)integral of the majorant, as a function of `z`
  have hinner_eq : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, K ^ 2 * angMaj α θ / (1 + z) ^ 2) = K ^ 2 * A / (1 + z) ^ 2 := by
    intro z _
    rw [show (fun θ => K ^ 2 * angMaj α θ / (1 + z) ^ 2)
        = fun θ => (K ^ 2 * angMaj α θ) * ((1 + z) ^ 2)⁻¹ from by funext θ; ring]
    rw [integral_mul_const, integral_const_mul]
    rw [hAdef]
    ring
  -- step 1: the `z`-integral of the inner bounds
  have hS1 : Work.Spaces.HkSq α 4 (hLoc α)
      ≤ ∫ z in Work.Spaces.Iz, K ^ 2 * A / (1 + z) ^ 2 := by
    rw [Work.Spaces.HkSq]
    refine integral_mono_ae hmem2 ?_ ?_
    · exact hMz.congr_fun (fun z hz => hinner_eq z hz) measurableSet_Ici
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      refine le_trans ?_ (le_of_eq (hinner_eq z hz))
      refine integral_mono_ae (hmem1 z hz) (hMslice z hz) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact hKmaj z hz θ hθ
  -- step 2: `∫_z K²A/(1+z)² = K²A·∫_z (1/(1+z))² ≤ K²A·2`
  have hS2 : (∫ z in Work.Spaces.Iz, K ^ 2 * A / (1 + z) ^ 2) ≤ (K ^ 2 * A) * 2 := by
    have hpt : ∀ z ∈ Work.Spaces.Iz,
        K ^ 2 * A / (1 + z) ^ 2 = (K ^ 2 * A) * (1 / (1 + z)) ^ 2 := by
      intro z _
      rw [div_pow, one_pow]
      ring
    rw [Work.Spaces.Iz]
    rw [setIntegral_congr_fun measurableSet_Ici hpt, integral_const_mul]
    have hzint : (∫ z in Work.Spaces.Iz, (1 / (1 + z)) ^ 2) ≤ 2 := by
      have h := Work.FTS.H2.InvOneAddSq.2
      rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
      exact h
    exact mul_le_mul_of_nonneg_left hzint (mul_nonneg (sq_nonneg K) hA0)
  -- step 3: `A ≤ 1000/(3α) + 10001`
  calc Work.Spaces.HkSq α 4 (hLoc α)
      ≤ ∫ z in Work.Spaces.Iz, K ^ 2 * A / (1 + z) ^ 2 := hS1
    _ ≤ (K ^ 2 * A) * 2 := hS2
    _ ≤ (K ^ 2 * (1000 / (3 * α) + 10001)) * 2 := by
        have hKA : K ^ 2 * A ≤ K ^ 2 * (1000 / (3 * α) + 10001) :=
          mul_le_mul_of_nonneg_left (by rw [hAdef]; exact hbndA) (sq_nonneg K)
        linarith

/-! ## The target -/

theorem hLoc_hk (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.HkMem α 4 (hLoc α) ∧
      ∃ C : ℝ, 0 ≤ C ∧ Work.Spaces.HkSq α 4 (hLoc α) ≤ C := by
  obtain ⟨K, _hK0, hKmaj⟩ := HkIntegrand_hLoc_le_self α hα hα1
  have hmem : Work.Spaces.HkMem α 4 (hLoc α) := HkMem_hLoc α hα hα1 K hKmaj
  refine ⟨hmem, (K ^ 2 * (1000 / (3 * α) + 10001)) * 2, ?_,
    hLoc_HkSq_le α hα hα1 hmem hKmaj⟩
  positivity

end Work.FTS.LocData
