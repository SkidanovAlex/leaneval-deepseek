/-
# Rounding the phases of the aggregate `aggr` (`Work.Peluse.Ulower.StepLe.aggr_round`)

Step 1 of the `blindConvertK` route (see `NOTES_blindConvertK_SESSION.md` §1): the aggregate
`aggr σ D B F β` -- the average over the pair box `[1,D]^σ × [1,D]^σ` of the squared moduli of the
`B⁻¹`-normalised correlations of the level-`σ` cube terms at the phases `β` -- is stable under
rounding the phases `β u v` to the rational grid `(1/T)ℤ`:

  `γ ≤ aggr β  ⟹  γ/2 ≤ aggr β'`,  `β' u v = round (T · β u v) / T`,

provided `4π(2B+1)/T ≤ √γ` (i.e. `T = Θ(B/√γ)`, the scale of the paper).

The two ingredients are exposed as separate lemmas (`corr_lipschitz`, `avg_sq_perturb`):

* `corr_lipschitz`: the normalised correlation `B⁻¹ ∑_x g x e(θx)` of a `1`-bounded function
  supported in `[-M,M]`, `M ≤ B`, is `2π(2B+1)`-Lipschitz in `θ`.  (Proof: `|e(θx) - e(θ'x)| ≤
  2π|x||θ-θ'|`, and `∑_{|x|≤M} |x| = M(M+1) ≤ B(2B+1)`.)
* `avg_sq_perturb`: if `a ≥ 0`, `b ≥ max 0 (a - ε)`, `ε ≤ √γ / 4` and `γ ≤ E a²`, then
  `γ/2 ≤ E b²`.  (Proof: `b² ≥ a² - 2εa`, then Cauchy--Schwarz `E a ≤ √(E a²)`.)

The `round`-specific arithmetic (`|θ - round (Tθ)/T| ≤ 1/(2T)`) is in this file.
-/

import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.blindConvertK_front
import Submission.Work.Peluse.Ulower.StepLe.corr_lipschitz
import Submission.Work.Peluse.Ulower.StepLe.avg_sq_perturb

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Ulower.StepLe

noncomputable section

/-- The `B⁻¹`-normalised correlation of the level-`σ` cube term of `F` at the pair `(u,v)` with
phase `φ u v`; `cubeCorr σ B F φ u v` is `‖cCorr σ B F φ u v‖ ^ 2` by definition. -/
def cCorr {σ : ℕ} (B : ℕ) (F : ℤ → ℂ)
    (φ : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) (u v : Fin σ → ℤ) : ℂ :=
  ((B : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v F x *
    Complex.exp (2 * Real.pi * Complex.I * (φ u v : ℂ) * (x : ℂ))

lemma cubeCorr_eq_norm {σ : ℕ} (B : ℕ) (F : ℤ → ℂ)
    (φ : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) (u v : Fin σ → ℤ) :
    cubeCorr σ B F φ u v = ‖cCorr B F φ u v‖ ^ 2 := rfl

/-- **The averaging step.**  If `γ ≤ E a²` and `b` is a `ε`-perturbation of `a` from below with
`4ε ≤ √γ`, then `γ/2 ≤ E b²`. -/
theorem aggr_round_aux {σ B D S : ℕ} {F : ℤ → ℂ}
    (β β' : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) (hB : 1 ≤ B) (hD : 1 ≤ D)
    (hF1 : ∀ x : ℤ, ‖F x‖ ≤ 1) (hFs : Work.Peluse.SupportIn F S)
    (hSB : S + σ * D ≤ B) {γ : ℝ} (hγ : 0 < γ)
    (haggr : γ ≤ Work.Peluse.Ulower.StepLe.aggr σ D B F β) {T : ℕ} (hT : 1 ≤ T)
    (hβ' : ∀ u v, |β u v - β' u v| ≤ 1 / (2 * (T : ℝ)))
    (hTbig : 4 * Real.pi * ((2 * B + 1 : ℕ) : ℝ) / (T : ℝ) ≤ Real.sqrt γ) :
    γ / 2 ≤ Work.Peluse.Ulower.StepLe.aggr σ D B F β' := by
  classical
  set ε : ℝ := Real.pi * ((2 * B + 1 : ℕ) : ℝ) / (T : ℝ) with hεdef
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hε0 : 0 ≤ ε := by rw [hεdef]; positivity
  have hsmall : 4 * ε ≤ Real.sqrt γ := by
    have hrw : 4 * ε = 4 * Real.pi * ((2 * B + 1 : ℕ) : ℝ) / (T : ℝ) := by
      rw [hεdef]; ring
    rw [hrw]; exact hTbig
  set s : Finset ((Fin σ → ℤ) × (Fin σ → ℤ)) := pairBox σ D with hsdef
  have hsne : s.Nonempty := by
    rw [hsdef, pairBox]
    refine ⟨(fun _ => (1 : ℤ), fun _ => (1 : ℤ)), ?_⟩
    simp only [Finset.mem_product, Fintype.mem_piFinset]
    exact ⟨fun i => (Work.Peluse.Ulower.mem_arithIcc_one).mpr ⟨le_refl 1, by exact_mod_cast hD⟩,
           fun i => (Work.Peluse.Ulower.mem_arithIcc_one).mpr ⟨le_refl 1, by exact_mod_cast hD⟩⟩
  set a : ((Fin σ → ℤ) × (Fin σ → ℤ)) → ℝ :=
    fun p => Real.sqrt (cubeCorr σ B F β p.1 p.2) with hadef
  set b : ((Fin σ → ℤ) × (Fin σ → ℤ)) → ℝ :=
    fun p => Real.sqrt (cubeCorr σ B F β' p.1 p.2) with hbdef
  have hsq : ∀ p : (Fin σ → ℤ) × (Fin σ → ℤ), (a p) ^ 2 = cubeCorr σ B F β p.1 p.2 := by
    intro p; rw [hadef]; exact Real.sq_sqrt (by rw [cubeCorr]; positivity)
  have hsq' : ∀ p : (Fin σ → ℤ) × (Fin σ → ℤ), (b p) ^ 2 = cubeCorr σ B F β' p.1 p.2 := by
    intro p; rw [hbdef]; exact Real.sq_sqrt (by rw [cubeCorr]; positivity)
  have hagg' : γ ≤ ((s.card : ℝ))⁻¹ * ∑ p ∈ s, (a p) ^ 2 := by
    have h1 := haggr
    rw [aggr_eq] at h1
    rw [← hsdef] at h1
    rw [← Finset.sum_congr rfl (fun p _ => hsq p)] at h1
    exact h1
  have hpert : ∀ p ∈ s, a p - ε ≤ b p := by
    intro p hp
    have hpm : p ∈ pairBox σ D := hsdef ▸ hp
    obtain ⟨_, hv⟩ := mem_pairBox hpm
    have hv' : ∀ i : Fin σ, (p.2 i).natAbs ≤ D :=
      fun i => natAbs_le_of_mem_arithIcc_one (hv i)
    have hcube : ∀ x : ℤ, ‖Work.Peluse.cubeTerm p.1 p.2 F x‖ ≤ 1 :=
      fun x => by simpa [Work.Peluse.cubeTerm] using
        Work.Peluse.Ulower.norm_cubeTerm_le hF1 p.1 p.2 x
    have hcorr := corr_lipschitz (B := B) (M := S + σ * D)
      (g := Work.Peluse.cubeTerm p.1 p.2 F) hB hcube (supportIn_cubeTerm hFs hv') hSB
      (β p.1 p.2) (β' p.1 p.2)
    have hθ : 2 * Real.pi * ((2 * B + 1 : ℕ) : ℝ) * |β p.1 p.2 - β' p.1 p.2| ≤ ε := by
      rw [hεdef]
      have hb1 := hβ' p.1 p.2
      have h2 := mul_le_mul_of_nonneg_left hb1 (by positivity :
        (0 : ℝ) ≤ 2 * Real.pi * ((2 * B + 1 : ℕ) : ℝ))
      refine h2.trans_eq ?_
      field_simp
    have hstep : ‖cCorr B F β p.1 p.2 - cCorr B F β' p.1 p.2‖ ≤ ε := le_trans hcorr hθ
    have h2 : ‖cCorr B F β p.1 p.2‖ - ε ≤ ‖cCorr B F β' p.1 p.2‖ := by
      have h3 : |‖cCorr B F β p.1 p.2‖ - ‖cCorr B F β' p.1 p.2‖| ≤ ε :=
        le_trans (abs_norm_sub_norm_le _ _) hstep
      linarith [neg_abs_le (‖cCorr B F β p.1 p.2‖ - ‖cCorr B F β' p.1 p.2‖),
        le_abs_self (‖cCorr B F β p.1 p.2‖ - ‖cCorr B F β' p.1 p.2‖)]
    have hae : a p = ‖cCorr B F β p.1 p.2‖ := by
      rw [hadef]; exact Real.sqrt_sq (norm_nonneg _)
    have hbe : b p = ‖cCorr B F β' p.1 p.2‖ := by
      rw [hbdef]; exact Real.sqrt_sq (norm_nonneg _)
    rw [hae, hbe]; exact h2
  have hmain := avg_sq_perturb s hsne (fun p _ => Real.sqrt_nonneg _)
    (fun p _ => Real.sqrt_nonneg _) hε0 hγ hpert hsmall hagg'
  rw [aggr_eq]
  rw [← hsdef]
  rw [Finset.sum_congr rfl (fun p _ => hsq' p)] at hmain
  exact hmain

theorem aggr_round {σ B D S : ℕ} {F : ℤ → ℂ}
    (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) (hB : 1 ≤ B) (hD : 1 ≤ D)
    (hF1 : ∀ x : ℤ, ‖F x‖ ≤ 1) (hFs : Work.Peluse.SupportIn F S)
    (hSB : S + σ * D ≤ B) {γ : ℝ} (hγ : 0 < γ)
    (haggr : γ ≤ Work.Peluse.Ulower.StepLe.aggr σ D B F β) {T : ℕ} (hT : 1 ≤ T)
    (hTbig : 4 * Real.pi * ((2 * B + 1 : ℕ) : ℝ) / (T : ℝ) ≤ Real.sqrt γ) :
    γ / 2 ≤ Work.Peluse.Ulower.StepLe.aggr σ D B F
      (fun u v => (round ((T : ℝ) * β u v) : ℤ) / (T : ℝ)) := by
  refine aggr_round_aux β (fun u v => (round ((T : ℝ) * β u v) : ℤ) / (T : ℝ))
    hB hD hF1 hFs hSB hγ haggr hT ?_ hTbig
  intro u v
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have h1 : |(T : ℝ) * β u v - ((round ((T : ℝ) * β u v) : ℤ) : ℝ)| ≤ 1 / 2 :=
    abs_sub_round _
  have h2 : β u v - (round ((T : ℝ) * β u v) : ℤ) / (T : ℝ)
      = ((T : ℝ) * β u v - ((round ((T : ℝ) * β u v) : ℤ) : ℝ)) / (T : ℝ) := by
    field_simp
  rw [h2, abs_div, abs_of_pos hT0]
  have h3 : (1 : ℝ) / 2 / (T : ℝ) = 1 / (2 * (T : ℝ)) := by rw [div_div]
  rw [← h3]
  exact div_le_div_of_nonneg_right h1 hT0.le

end

end Work.Peluse.Ulower.StepLe
