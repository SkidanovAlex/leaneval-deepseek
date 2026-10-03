import Mathlib
import Submission.Work.FatouWindow.fatouDerivSetup

/-!
# FATOU-L1: the deep bound for `u = Φ' - 1` and for `Φ''`

`u = fatouU = Φ' - 1` measures the failure of the (canonical) Fatou coordinate `Φ` of a
near-translation `F` on Shishikura's region `Q = Qreg b₁ b₂` to be the identity.  Shishikura's
Lemma A.2.4(i) (`MandelDim.FatouDerivEstimate`, whose second conjunct is the hypothesis `hEst`
below) gives, on every disc `B(z₀,R) ⊆ Q` with `R ≥ R₁`,

`‖Φ'(z₀) - 1/v(z₀)‖ ≤ C₂ / R`,  where `v = F - id` (so `z + v z = F z`).

Two consequences are proved here, for a disc `B(z, 2δ) ⊆ Q` that is *well inside* `Q` in the sense
that also every nearby ball of radius `R₁` is contained in `Q`:

* `‖u z‖ ≤ C₂/R₁ + 1/31`:  apply the estimate with `R = R₁` at `z`, then use `‖v z - 1‖ ≤ 1/32`
  (near-translation) to correct `1/v z` to `1`:
  `‖1/v z - 1‖ = ‖1 - v z‖ / ‖v z‖ ≤ (1/32)/(31/32) = 1/31`.
* `‖Φ'' z‖ ≤ (C₂/R₁ + 1/31)/δ`:  the first bound is available at *every* centre `w ∈ B(z,δ)`
  (because `B(w,R₁) ⊆ Q` there), i.e. `‖u‖ ≤ M` on `B(z,δ)`, and `u` is holomorphic there, so
  Cauchy's estimate on the open disc gives `‖u'(z)‖ ≤ M/δ`.  Finally
  `u' = (Φ' - 1)' = Φ''`, i.e. `iteratedDeriv 2 Φ = deriv u`.

The only non-elementary point of the formalisation is Cauchy's estimate with the bound assumed on
the **open** disc: Mathlib has the boundary-circle version
(`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`), and the open-disc version is obtained here
by applying it on the smaller circles `S(c,r) ⊆ B(c,R)`, `r < R`, and letting `r ↑ R`.
-/

namespace Work.FatouWindow

open Work.FatouL1

open Set Metric

noncomputable section

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ}

/-- **Cauchy's estimate on the open disc.**  If `f` is complex differentiable on the open disc
`B(c,R)` (and continuous on its closure) and `‖f‖ ≤ C` on `B(c,R)`, then
`‖f'(c)‖ ≤ C/R`.  Mathlib's `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` gives this with
the bound assumed on the boundary circle; here the bound is assumed on the whole open disc, which
is strictly weaker, and the radius is decreased to `r < R` and then `r ↑ R`. -/
private theorem norm_deriv_le_of_forall_mem_ball_norm_le {f : ℂ → ℂ} {c : ℂ} {R C : ℝ}
    (hR : 0 < R) (hd : DiffContOnCl ℂ f (ball c R))
    (hC : ∀ z ∈ ball c R, ‖f z‖ ≤ C) : ‖deriv f c‖ ≤ C / R := by
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC c (mem_ball_self hR))
  by_contra hle
  rw [not_le] at hle
  set L := ‖deriv f c‖ with hL
  have hLpos : 0 < L := lt_of_le_of_lt (div_nonneg hCnn hR.le) hle
  have hCLR : C / L < R := by
    have h1 : C < L * R := (div_lt_iff₀ hR).mp hle
    rw [div_lt_iff₀ hLpos]
    linarith
  set r : ℝ := (C / L + R) / 2 with hr
  have hr_gt : C / L < r := by rw [hr]; linarith
  have hr_lt : r < R := by rw [hr]; linarith
  have hr_pos : 0 < r := lt_of_le_of_lt (div_nonneg hCnn hLpos.le) hr_gt
  have hsphere : ∀ w ∈ sphere c r, ‖f w‖ ≤ C := by
    intro w hw
    apply hC
    rw [mem_sphere] at hw
    rw [mem_ball, hw]
    exact hr_lt
  have hdc : DiffContOnCl ℂ f (ball c r) := hd.mono (ball_subset_ball hr_lt.le)
  have hmain := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr_pos hdc hsphere
  have hCr : C / r < L := by
    rw [div_lt_iff₀ hr_pos]
    have h2 : C < r * L := by
      rw [div_lt_iff₀ hLpos] at hr_gt
      linarith
    linarith
  rw [hL] at hCr
  linarith [hmain, hCr]

/-- If `‖w - 1‖ ≤ 1/32` then `‖1/w - 1‖ ≤ 1/31`:  `1/w - 1 = (1 - w)/w` and `‖w‖ ≥ 1 - 1/32`. -/
private theorem norm_inv_sub_one_le {w : ℂ} (hw : ‖w - 1‖ ≤ 1 / 32) : ‖1 / w - 1‖ ≤ 1 / 31 := by
  have hw' : ‖1 - w‖ ≤ 1 / 32 := by
    have h : (1 : ℂ) - w = -(w - 1) := by ring
    rw [h, norm_neg]; exact hw
  have hwn : (31 / 32 : ℝ) ≤ ‖w‖ := by
    have h := norm_sub_norm_le (1 : ℂ) w
    rw [norm_one] at h
    linarith
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hwn; simp at hwn; norm_num at hwn
  have heq : 1 / w - 1 = (1 - w) / w := by field_simp
  rw [heq, norm_div]
  calc ‖1 - w‖ / ‖w‖ ≤ (1 / 32) / (31 / 32) := by gcongr
    _ = 1 / 31 := by norm_num

theorem fatouU_deep_bound {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {R₁ C₂ δ : ℝ} {z : ℂ}
    (hadm : MandelDim.QAdm b₁ b₂) (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (hR₁ : 0 < R₁) (hC₂ : 0 < C₂) (hδ : 0 < δ) (hδR : δ ≤ R₁)
    (hEst : ∀ (Φ v : ℂ → ℂ) (z₀ : ℂ) (R : ℝ), R₁ ≤ R → DifferentiableOn ℂ Φ (Metric.ball z₀ R) →
      Set.InjOn Φ (Metric.ball z₀ R) → DifferentiableOn ℂ v (Metric.ball z₀ R) →
      (∀ z ∈ Metric.ball z₀ R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z₀ R, z + v z ∈ Metric.ball z₀ R → Φ (z + v z) = Φ z + 1) →
      ‖deriv Φ z₀ - 1 / v z₀‖ ≤ C₂ / R)
    (hball2 : Metric.ball z (2 * δ) ⊆ MandelDim.Qreg b₁ b₂)
    (hballR : ∀ w : ℂ, ‖w - z‖ < δ → Metric.ball w R₁ ⊆ MandelDim.Qreg b₁ b₂) :
    ‖Work.FatouWindow.fatouU hadm hF z‖ ≤ C₂ / R₁ + 1 / 31 ∧
      ‖iteratedDeriv 2 (Work.FatouWindow.fatouCoord hadm hF) z‖ ≤ (C₂ / R₁ + 1 / 31) / δ := by
  have hΦ : MandelDim.IsFatouCoordOn F (fatouCoord hadm hF) (MandelDim.Qreg b₁ b₂) :=
    fatouCoord_spec hadm hF
  -- ### the pointwise bound at every centre whose `R₁`-ball stays inside `Qreg`
  have hpt : ∀ c : ℂ, Metric.ball c R₁ ⊆ MandelDim.Qreg b₁ b₂ →
      ‖fatouU hadm hF c‖ ≤ C₂ / R₁ + 1 / 31 := by
    intro c hc
    have hv1 : ∀ w ∈ Metric.ball c R₁, ‖(F w - w) - 1‖ < 1 / 4 := by
      intro w hw
      have h1 : ‖F w - (w + 1)‖ ≤ 1 / 32 := (hF.1.2 w (hc hw)).1
      have heq : F w - (w + 1) = (F w - w) - 1 := by ring
      rw [heq] at h1
      linarith
    have hAbel : ∀ w ∈ Metric.ball c R₁, w + (F w - w) ∈ Metric.ball c R₁ →
        fatouCoord hadm hF (w + (F w - w)) = fatouCoord hadm hF w + 1 := by
      intro w hw hw'
      have hFw : F w ∈ Metric.ball c R₁ := by
        rwa [show w + (F w - w) = F w from by ring] at hw'
      rw [show w + (F w - w) = F w from by ring]
      exact hΦ.2.2 w (hc hw) (hc hFw)
    have hmain : ‖deriv (fatouCoord hadm hF) c - 1 / (F c - c)‖ ≤ C₂ / R₁ :=
      hEst (fatouCoord hadm hF) (fun w : ℂ => F w - w) c R₁ le_rfl
        (hΦ.1.mono hc) (hΦ.2.1.mono hc) ((hF.1.1.mono hc).sub differentiableOn_id) hv1 hAbel
    have h31 : ‖1 / (F c - c) - 1‖ ≤ 1 / 31 := by
      refine norm_inv_sub_one_le ?_
      have h1 : ‖F c - (c + 1)‖ ≤ 1 / 32 := (hF.1.2 c (hc (mem_ball_self hR₁))).1
      have heq : F c - (c + 1) = (F c - c) - 1 := by ring
      rwa [heq] at h1
    have hsplit : fatouU hadm hF c =
        (deriv (fatouCoord hadm hF) c - 1 / (F c - c)) + (1 / (F c - c) - 1) := by
      unfold fatouU
      ring
    rw [hsplit]
    exact le_trans (norm_add_le _ _) (add_le_add hmain h31)
  -- ### the second derivative: Cauchy's estimate for `u` on `B(z,δ)`
  have hdiffU : DifferentiableOn ℂ (fatouU hadm hF) (Metric.ball z (2 * δ)) :=
    ((hΦ.1.mono hball2).deriv Metric.isOpen_ball).sub_const 1
  have hcau : ‖deriv (fatouU hadm hF) z‖ ≤ (C₂ / R₁ + 1 / 31) / δ := by
    refine norm_deriv_le_of_forall_mem_ball_norm_le hδ ?_ ?_
    · exact hdiffU.diffContOnCl_ball (Metric.closedBall_subset_ball (by linarith))
    · intro w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      exact hpt w (hballR w hw)
  have hiter : iteratedDeriv 2 (fatouCoord hadm hF) z = deriv (fatouU hadm hF) z := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    unfold fatouU
    rw [deriv_sub_const]
  refine ⟨hpt z (hballR z ?_), ?_⟩
  · rw [sub_self, norm_zero]; exact hδ
  · rw [hiter]; exact hcau

end

end Work.FatouWindow
