import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.Honesty.CptQSmooth.cmode_iteratedDeriv_facts
import Submission.Work.FTS.PhiStar.Honesty.CptQSmooth.radGreen_general_bound
import Submission.Work.FTS.PhiStar.Honesty.radGreen_near_limits_of_le_rpow
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Stability.mul_rpow_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CptQSmooth

/-! ## The families of mode sums

For a source `G` which is `C^∞` on `ℝ²` with support a compact subset of the open quadrant, the
mode series

  `psiSeries α G z θ = Σ_m acoeff α m G z · e_m θ`

is differentiated termwise in `z` (all orders) and in `θ` (all orders).  The resulting functions
are the two-parameter families

  `pscF α G a j z θ = Σ_m (∂_z^a acoeff α m G z) · (∂_θ^j e_m θ)`.

Unlike the `RemSource` case, the mode coefficient `acoeff α m G z = radGreen α m (cmode m G) z`
is *not* of the form `const_m · (solvable radial profile)`, so the whole estimate is redone for
the general source: the decay of `cmode m G` and its `z`-derivatives
(`cmode_iteratedDeriv_facts`, from `cmode_decay_of_cptQ`), and the general-source radial bound
`radGreen_general_bound`, give a uniform majorant `D·(m+1)^{-3/2}` for every family on a local
rectangle of the open quadrant.  The abstract bootstrap `contDiffOn_succ_of_partials` then shows
that every `pscF α G a j` is `C^∞` on `Q0` — the `z`-chain shifts `a`, the `θ`-chain shifts `j`,
and both are available at every order (no PDE is needed, because the `θ`-chain is available to
*all* orders). -/

/-- The `a`-th `z`-derivative of the `m`-th radial coefficient `acoeff α m G`. -/
def pscA (α : ℝ) (G : ℝ → ℝ → ℝ) (a m : ℕ) (z : ℝ) : ℝ :=
  iteratedDeriv a (fun z' => Work.FTS.PhiStar.Series.acoeff α m G z') z

/-- The mode-sum family of `∂_z^a ∂_θ^j (psiSeries α G)`. -/
def pscF (α : ℝ) (G : ℝ → ℝ → ℝ) (a j : ℕ) (z θ : ℝ) : ℝ :=
  ∑' m : ℕ, pscA α G a m z * iteratedDeriv j (Work.FTS.PhiStar.Gegenbauer.eFam m) θ

theorem pscF_zero_zero (α : ℝ) (G : ℝ → ℝ → ℝ) :
    pscF α G 0 0 = Work.FTS.PhiStar.Series.psiSeries α G := by
  funext z θ
  simp only [pscF, pscA, iteratedDeriv_zero, Work.FTS.PhiStar.Series.psiSeries]

/-! ## All-order smoothness of the angular eigenfunctions -/

theorem contDiff_gC_all : ∀ (n j : ℕ), ContDiff ℝ j (Work.FTS.PhiStar.Gegenbauer.gC n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro j
    match n with
    | 0 =>
      have h : Work.FTS.PhiStar.Gegenbauer.gC 0 = fun _ : ℝ => (1 : ℝ) := rfl
      rw [h]; exact contDiff_const
    | 1 =>
      have h : Work.FTS.PhiStar.Gegenbauer.gC 1 = fun x : ℝ => 3 * x := rfl
      rw [h]; exact contDiff_const.mul (contDiff_id : ContDiff ℝ j (fun x : ℝ => x))
    | (k + 2) =>
      have h1 : ContDiff ℝ j (Work.FTS.PhiStar.Gegenbauer.gC (k + 1)) := ih (k + 1) (by omega) j
      have h2 : ContDiff ℝ j (Work.FTS.PhiStar.Gegenbauer.gC k) := ih k (by omega) j
      have h : Work.FTS.PhiStar.Gegenbauer.gC (k + 2) = fun x : ℝ =>
          (2 * ((k : ℝ) + 5 / 2) * x * Work.FTS.PhiStar.Gegenbauer.gC (k + 1) x
            - ((k : ℝ) + 3) * Work.FTS.PhiStar.Gegenbauer.gC k x) / ((k : ℝ) + 2) := rfl
      rw [h]
      exact (((contDiff_const.mul (contDiff_id : ContDiff ℝ j (fun x : ℝ => x))).mul h1).sub
        (contDiff_const.mul h2)).div_const _

theorem contDiff_eFam_all (m j : ℕ) : ContDiff ℝ j (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  rw [show Work.FTS.PhiStar.Gegenbauer.eFam m
      = fun θ : ℝ => Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)
      from rfl]
  exact Real.contDiff_cos.mul ((contDiff_gC_all (2 * m + 1) j).comp Real.contDiff_sin)

theorem hasDerivAt_iteratedDeriv_eFam (m j : ℕ) (θ : ℝ) :
    HasDerivAt (iteratedDeriv j (Work.FTS.PhiStar.Gegenbauer.eFam m))
      (iteratedDeriv (j + 1) (Work.FTS.PhiStar.Gegenbauer.eFam m) θ) θ := by
  have hd : Differentiable ℝ (iteratedDeriv j (Work.FTS.PhiStar.Gegenbauer.eFam m)) :=
    (contDiff_eFam_all m (j + 1)).differentiable_iteratedDeriv j
      (by exact_mod_cast Nat.lt_succ_self j)
  rw [iteratedDeriv_succ]
  exact (hd θ).hasDerivAt

/-! ## The mode coefficients of a `C^∞` compactly supported source -/

/-- **The iterated derivatives of a chain family.**  (Local copy — the version in
`SmoothAux.OdeDefs` cannot be imported here without pulling in `Deleg.psiAngDefs`, which clashes
with `Deleg.psiCmodeAux` on the name `gC_abs_bound`.) -/
theorem iteratedDeriv_of_hasDerivAt_chain {F : ℕ → ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (h : ∀ (b : ℕ) (y : ℝ), y ∈ s → HasDerivAt (F b) (F (b + 1) y) y) :
    ∀ (n b : ℕ) (x : ℝ), x ∈ s → iteratedDeriv n (F b) x = F (b + n) x := by
  intro n
  induction n with
  | zero => intro b x _; simp
  | succ n ih =>
      intro b x hx
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv n (F b) =ᶠ[𝓝 x] fun y => F (b + n) y := by
        filter_upwards [hs.mem_nhds hx] with y hy
        exact ih b y hy
      rw [heq.deriv_eq, (h (b + n) x hx).deriv,
        show b + n + 1 = b + (n + 1) from by omega]

/-- **A chain family is `C^n` for every `n`.**  (Local copy, for the same reason.) -/
theorem contDiffOn_of_hasDerivAt_chain {F : ℕ → ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (h : ∀ (b : ℕ) (y : ℝ), y ∈ s → HasDerivAt (F b) (F (b + 1) y) y) :
    ∀ (n b : ℕ), ContDiffOn ℝ n (F b) s := by
  have hiter := iteratedDeriv_of_hasDerivAt_chain hs h
  have hdiff : ∀ b : ℕ, DifferentiableOn ℝ (F b) s :=
    fun b y hy => (h b y hy).differentiableAt.differentiableWithinAt
  intro n b
  rw [contDiffOn_nat_iff_continuousOn_differentiableOn_deriv hs.uniqueDiffOn]
  refine ⟨fun m _ => ?_, fun m _ => ?_⟩
  · exact (hdiff (b + m)).continuousOn.congr (fun y hy => by
      rw [iteratedDerivWithin_of_isOpen hs hy, hiter m b y hy])
  · exact (hdiff (b + m)).congr (fun y hy => by
      rw [iteratedDerivWithin_of_isOpen hs hy, hiter m b y hy])

/-- `t ↦ cmode m G t` is `C^n` on `(0,∞)`. -/
theorem cmode_contDiffOn {G : ℝ → ℝ → ℝ} (hG : SmoothCptQ G) (m n : ℕ) :
    ContDiffOn ℝ n (fun t => Work.FTS.PhiStar.Series.cmode m G t) (Set.Ioi 0) := by
  have hchain : ∀ (b : ℕ) (y : ℝ), y ∈ Set.Ioi (0 : ℝ) →
      HasDerivAt (fun t => iteratedDeriv b
          (fun t' => Work.FTS.PhiStar.Series.cmode m G t') t)
        (iteratedDeriv (b + 1)
          (fun t' => Work.FTS.PhiStar.Series.cmode m G t') y) y :=
    fun b y hy => (cmode_iteratedDeriv_facts hG b 0).1 m y hy
  have h := contDiffOn_of_hasDerivAt_chain
    (F := fun b : ℕ => iteratedDeriv b (fun t' => Work.FTS.PhiStar.Series.cmode m G t'))
    (s := Set.Ioi (0 : ℝ)) isOpen_Ioi hchain n 0
  simpa only [iteratedDeriv_zero] using h

/-- A single constant bounds the first `l` derivatives of `cmode m G` with the decay
`(m+1)^{-N}`, uniformly in `m`. -/
theorem cmode_bound {G : ℝ → ℝ → ℝ} (hG : SmoothCptQ G) (l N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : ℕ) (k : ℕ), k ≤ l → ∀ t : ℝ, 0 < t →
      |iteratedDeriv k (fun t' => Work.FTS.PhiStar.Series.cmode m G t') t|
        ≤ K / ((m : ℝ) + 1) ^ N := by
  have h : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (t : ℝ),
      |iteratedDeriv k (fun t' => Work.FTS.PhiStar.Series.cmode m G t') t|
        ≤ C / ((m : ℝ) + 1) ^ N :=
    fun k => (cmode_iteratedDeriv_facts hG k N).2
  choose Cf hCf0 hCfb using h
  refine ⟨∑ k ∈ Finset.range (l + 1), Cf k, Finset.sum_nonneg fun k _ => hCf0 k, ?_⟩
  intro m k hk t ht
  have h1 := hCfb k m t
  have h2 : Cf k ≤ ∑ k' ∈ Finset.range (l + 1), Cf k' :=
    Finset.single_le_sum (fun k' _ => hCf0 k') (Finset.mem_range.mpr (by omega))
  calc |iteratedDeriv k (fun t' => Work.FTS.PhiStar.Series.cmode m G t') t|
      ≤ Cf k / ((m : ℝ) + 1) ^ N := h1
    _ ≤ (∑ k' ∈ Finset.range (l + 1), Cf k') / ((m : ℝ) + 1) ^ N :=
        div_le_div_of_nonneg_right h2 (by positivity)

/-- `cmode m G` vanishes off the radial support box. -/
theorem cmode_vanish {G : ℝ → ℝ → ℝ} {a₀ b : ℝ}
    (hbox : ∀ z θ : ℝ, G z θ ≠ 0 → z ∈ Set.Icc a₀ b) (m : ℕ) :
    ∀ t : ℝ, t ∉ Set.Icc a₀ b → Work.FTS.PhiStar.Series.cmode m G t = 0 := by
  intro t ht
  have hzero : ∀ θ : ℝ, G t θ = 0 := by
    intro θ
    by_contra hne
    exact ht (hbox t θ hne)
  simp only [Work.FTS.PhiStar.Series.cmode, hzero, zero_mul]
  simp

/-! ## The decay of the radial coefficients -/

/-- **The radial coefficient bound.**  For every order `a` and every decay rate `N` there is a
constant `C` with `|∂_z^a (acoeff α m G) z| ≤ C (m+1)^{-N}` for all `m` and all `z ≥ z₀ > 0`.
The `m`-dependence is destroyed by combining the general-source radial bound
`radGreen_general_bound` (whose constant is uniform in the source) with the geometric decay of
`cmode m G` and its derivatives. -/
theorem pscA_bound {α : ℝ} (hα : 0 < α) (hα2 : α < 2) {G : ℝ → ℝ → ℝ}
    (hG : SmoothCptQ G) (a N : ℕ) {z₀ : ℝ} (hz₀ : 0 < z₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (z : ℝ), z₀ ≤ z →
      |pscA α G a m z| ≤ C / ((m : ℝ) + 1) ^ N := by
  obtain ⟨a₀, b, c₀, d₀, ha₀, hab, hc₀, hcd, hd, Hbox⟩ := hG.cpt.exists_box
  have hbox : ∀ z θ : ℝ, G z θ ≠ 0 → z ∈ Set.Icc a₀ b := fun z θ h => (Hbox z θ h).1
  obtain ⟨Kc, hKc0, hKcb⟩ := cmode_bound hG (a + 1) (N + a + 1)
  obtain ⟨Cb, hCb0, hCb⟩ :=
    radGreen_general_bound (a₀ := a₀) (b := b) (z₀ := z₀) hα hα2 ha₀ hz₀ a
  refine ⟨Cb * Kc, mul_nonneg hCb0 hKc0, ?_⟩
  intro m z hz
  have hcont : ContDiffOn ℝ (↑(a + 1))
      (fun t => Work.FTS.PhiStar.Series.cmode m G t) (Set.Ioi 0) :=
    cmode_contDiffOn hG m (a + 1)
  have hbdd : Work.FTS.PhiStar.BddDeriv (a + 1)
      (fun t => Work.FTS.PhiStar.Series.cmode m G t) (Kc / ((m : ℝ) + 1) ^ (N + a + 1)) :=
    fun k hk t ht => hKcb m k hk t ht
  have hsupp : ∀ t : ℝ, t ∉ Set.Icc a₀ b →
      (fun t' => Work.FTS.PhiStar.Series.cmode m G t') t = 0 :=
    fun t ht => cmode_vanish hbox m t ht
  have hres := (hCb (c := fun t => Work.FTS.PhiStar.Series.cmode m G t)
    (K := Kc / ((m : ℝ) + 1) ^ (N + a + 1)) (by positivity) hcont hbdd hsupp).2 m z hz
  have hpsc : pscA α G a m z = iteratedDeriv a (fun z'' => Work.FTS.PhiStar.Radial.radGreen α m
      (fun t => Work.FTS.PhiStar.Series.cmode m G t) z'') z := rfl
  rw [hpsc]
  have hW : ((m : ℝ) + 1) ^ (N + 1) ≠ 0 := pow_ne_zero _ (by positivity)
  have hexp : ((m : ℝ) + 1) ^ (N + a + 1) = ((m : ℝ) + 1) ^ a * ((m : ℝ) + 1) ^ (N + 1) := by
    rw [show N + a + 1 = a + (N + 1) from by omega, pow_add]
  calc |iteratedDeriv a (fun z'' => Work.FTS.PhiStar.Radial.radGreen α m
        (fun t => Work.FTS.PhiStar.Series.cmode m G t) z'') z|
      ≤ Cb * ((m : ℝ) + 1) ^ a * (Kc / ((m : ℝ) + 1) ^ (N + a + 1)) := hres
    _ = Cb * Kc / ((m : ℝ) + 1) ^ (N + 1) := by
        rw [hexp, eq_div_iff hW]
        field_simp
    _ ≤ Cb * Kc / ((m : ℝ) + 1) ^ N := by
        refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
        exact pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (m : ℝ) + 1) (by omega)

/-- **The radial coefficient is smooth in `z`.** -/
theorem pscA_hasDerivAt {α : ℝ} (hα : 0 < α) (hα2 : α < 2) {G : ℝ → ℝ → ℝ}
    (hG : SmoothCptQ G) (a m : ℕ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (pscA α G a m) (pscA α G (a + 1) m z) z := by
  obtain ⟨a₀, b, c₀, d₀, ha₀, hab, hc₀, hcd, hd, Hbox⟩ := hG.cpt.exists_box
  have hbox : ∀ z θ : ℝ, G z θ ≠ 0 → z ∈ Set.Icc a₀ b := fun z θ h => (Hbox z θ h).1
  obtain ⟨Kc, hKc0, hKcb⟩ := cmode_bound hG (a + 1) (a + 2)
  obtain ⟨Cb, hCb0, hCb⟩ :=
    radGreen_general_bound (a₀ := a₀) (b := b) (z₀ := 1) hα hα2 ha₀ one_pos a
  have hcont : ContDiffOn ℝ (↑(a + 1))
      (fun t => Work.FTS.PhiStar.Series.cmode m G t) (Set.Ioi 0) :=
    cmode_contDiffOn hG m (a + 1)
  have hbdd : Work.FTS.PhiStar.BddDeriv (a + 1)
      (fun t => Work.FTS.PhiStar.Series.cmode m G t) (Kc / ((m : ℝ) + 1) ^ (a + 2)) :=
    fun k hk t ht => hKcb m k hk t ht
  have hsupp : ∀ t : ℝ, t ∉ Set.Icc a₀ b →
      (fun t' => Work.FTS.PhiStar.Series.cmode m G t') t = 0 :=
    fun t ht => cmode_vanish hbox m t ht
  have hres := (hCb (c := fun t => Work.FTS.PhiStar.Series.cmode m G t)
    (K := Kc / ((m : ℝ) + 1) ^ (a + 2)) (by positivity) hcont hbdd hsupp).1 m z hz
  exact hres

/-! ## The local rectangle of the open quadrant -/

/-- The rectangle `(z/2, 2z) × (θ/2, (θ+π/2)/2)`, a neighbourhood of `(z,θ) ∈ Q0` contained in
`Q0`. -/
def pscRect (z θ : ℝ) : Set (ℝ × ℝ) :=
  Set.Ioo (z / 2) (2 * z) ×ˢ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2)


theorem pscRect_mem_nhds {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    pscRect z θ ∈ 𝓝 (z, θ) := by
  refine IsOpen.mem_nhds (isOpen_Ioo.prod isOpen_Ioo) ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · linarith
  · linarith
  · linarith
  · linarith [hθ2, Real.pi_pos]

/-! ## The uniform term bound on the local rectangle -/

theorem pscF_term_le {α : ℝ} (hα : 0 < α) (hα2 : α < 2) {G : ℝ → ℝ → ℝ}
    (hG : SmoothCptQ G) (a j : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ)
    (hθ2 : θ < Real.pi / 2) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (m : ℕ) (q : ℝ × ℝ), q ∈ pscRect z θ →
      ‖pscA α G a m q.1 * iteratedDeriv j (Work.FTS.PhiStar.Gegenbauer.eFam m) q.2‖
        ≤ D * Work.FTS.PhiStar.Series.SmoothAux.maj m := by
  have hzl : (0 : ℝ) < z / 2 := by linarith
  obtain ⟨C1, hC10, hC1⟩ := pscA_bound hα hα2 hG a (j + 3) hzl
  have hθhp : (θ + Real.pi / 2) / 2 < Real.pi / 2 := by linarith [Real.pi_pos]
  obtain ⟨C2, hC20, hC2⟩ :=
    CleanAng.eFam_iteratedDeriv_growth j (θ₁ := θ / 2)
    (θ₂ := (θ + Real.pi / 2) / 2) (by linarith) hθhp
  refine ⟨C1 * C2, mul_nonneg hC10 hC20, ?_⟩
  intro m q hq
  have hq1 : z / 2 ≤ q.1 := le_of_lt hq.1.1
  have hq2 : q.2 ∈ Set.Icc (θ / 2) ((θ + Real.pi / 2) / 2) :=
    ⟨le_of_lt hq.2.1, le_of_lt hq.2.2⟩
  have h1 := hC1 m q.1 hq1
  have h2 := hC2 m q.2 hq2
  have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  rw [Real.norm_eq_abs, abs_mul]
  have hA : ((m : ℝ) + 1) ^ (j + 3) = ((m : ℝ) + 1) ^ (j + 1) * ((m : ℝ) + 1) ^ 2 := by
    rw [show j + 3 = (j + 1) + 2 from by omega, pow_add]
  calc |pscA α G a m q.1| * |iteratedDeriv j (Work.FTS.PhiStar.Gegenbauer.eFam m) q.2|
      ≤ (C1 / ((m : ℝ) + 1) ^ (j + 3)) * (C2 * ((m : ℝ) + 1) ^ (j + 1)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = C1 * C2 / ((m : ℝ) + 1) ^ 2 := by
        rw [hA, eq_div_iff (by positivity : ((m : ℝ) + 1) ^ 2 ≠ 0)]
        field_simp
    _ ≤ C1 * C2 / ((m : ℝ) + 1) ^ (3 / 2 : ℝ) := by
        refine div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hm0 _) ?_
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ (m : ℝ) + 1)
          (by norm_num : ((3 : ℝ) / 2) ≤ 2)
    _ = C1 * C2 * Work.FTS.PhiStar.Series.SmoothAux.maj m := by
        rw [Work.FTS.PhiStar.Series.SmoothAux.maj]
        ring

/-! ## Continuity of the families -/

theorem pscA_continuousOn {α : ℝ} (hα : 0 < α) (hα2 : α < 2) {G : ℝ → ℝ → ℝ}
    (hG : SmoothCptQ G) (a m : ℕ) :
    ContinuousOn (fun z => pscA α G a m z) (Set.Ioi 0) :=
  fun z hz => (pscA_hasDerivAt hα hα2 hG a m hz).continuousAt.continuousWithinAt

theorem pscF_continuousOn {α : ℝ} (hα : 0 < α) (hα2 : α < 2) {G : ℝ → ℝ → ℝ}
    (hG : SmoothCptQ G) (a j : ℕ) :
    ContinuousOn (Function.uncurry (pscF α G a j)) Work.FTS.EllipticEst.Q0 := by
  intro p hp
  obtain ⟨hp1, hp2, hp3⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  obtain ⟨D, hD0, hDle⟩ := pscF_term_le hα hα2 hG a j hp1 hp2 hp3
  have hterm : ∀ m : ℕ, ContinuousOn (fun q : ℝ × ℝ =>
      pscA α G a m q.1
        * iteratedDeriv j (Work.FTS.PhiStar.Gegenbauer.eFam m) q.2) (pscRect p.1 p.2) := by
    intro m
    have h1 : ContinuousOn (fun q : ℝ × ℝ => pscA α G a m q.1) (pscRect p.1 p.2) :=
      (pscA_continuousOn hα hα2 hG a m).comp continuousOn_fst
        (fun q hq => by have h := hq.1.1; show (0 : ℝ) < q.1; linarith)
    have h2 : ContinuousOn (fun q : ℝ × ℝ =>
        iteratedDeriv j (Work.FTS.PhiStar.Gegenbauer.eFam m) q.2) (pscRect p.1 p.2) :=
      (((contDiff_eFam_all m (j + 1)).continuous_iteratedDeriv j
        (by exact_mod_cast Nat.le_succ j))).continuousOn.comp continuousOn_snd
        (fun q _ => Set.mem_univ _)
    exact h1.mul h2
  have hcont := continuousOn_tsum (f := fun (m : ℕ) (q : ℝ × ℝ) =>
      pscA α G a m q.1 * iteratedDeriv j (Work.FTS.PhiStar.Gegenbauer.eFam m) q.2)
    hterm (Work.FTS.PhiStar.Series.SmoothAux.summable_maj.mul_left D)
    (fun m q hq => hDle m q hq)
  exact ContinuousAt.continuousWithinAt
    (hcont.continuousAt (pscRect_mem_nhds hp1 hp2 hp3))

/-! ## The differentiation chains -/

theorem pscF_hasDerivAt_z {α : ℝ} (hα : 0 < α) (hα2 : α < 2) {G : ℝ → ℝ → ℝ}
    (hG : SmoothCptQ G) (a j : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ)
    (hθ2 : θ < Real.pi / 2) :
    HasDerivAt (fun z' => pscF α G a j z' θ) (pscF α G (a + 1) j z θ) z := by
  obtain ⟨D, hD0, hDle⟩ := pscF_term_le hα hα2 hG (a + 1) j hz hθ hθ2
  obtain ⟨D', hD'0, hD'le⟩ := pscF_term_le hα hα2 hG a j hz hθ hθ2
  have hθne : θ ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2) :=
    ⟨by linarith, by linarith [Real.pi_pos]⟩
  refine hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ)
    (u := fun m : ℕ => D * Work.FTS.PhiStar.Series.SmoothAux.maj m)
    (g := fun m y => pscA α G a m y
      * iteratedDeriv j (Work.FTS.PhiStar.Gegenbauer.eFam m) θ)
    (g' := fun m y => pscA α G (a + 1) m y
      * iteratedDeriv j (Work.FTS.PhiStar.Gegenbauer.eFam m) θ)
    (Work.FTS.PhiStar.Series.SmoothAux.summable_maj.mul_left D)
    isOpen_Ioo isPreconnected_Ioo ?_ ?_ (t := Set.Ioo (z / 2) (2 * z)) (y₀ := z)
    ⟨by linarith, by linarith⟩ ?_ ⟨by linarith, by linarith⟩
  · intro m y hy
    have hy0 : 0 < y := by linarith [hy.1]
    exact (pscA_hasDerivAt hα hα2 hG a m hy0).mul_const _
  · intro m y hy
    have hmem : (y, θ) ∈ pscRect z θ := ⟨hy, hθne⟩
    have h := hDle m (y, θ) hmem
    rw [Real.norm_eq_abs] at h
    rw [Real.norm_eq_abs]
    exact h
  · refine Summable.of_norm_bounded
      (Work.FTS.PhiStar.Series.SmoothAux.summable_maj.mul_left D') (fun m => ?_)
    have hmem : (z, θ) ∈ pscRect z θ := ⟨⟨by linarith, by linarith⟩, hθne⟩
    have h := hD'le m (z, θ) hmem
    rw [Real.norm_eq_abs] at h
    rw [Real.norm_eq_abs]
    exact h

theorem pscF_hasDerivAt_theta {α : ℝ} (hα : 0 < α) (hα2 : α < 2) {G : ℝ → ℝ → ℝ}
    (hG : SmoothCptQ G) (a j : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ)
    (hθ2 : θ < Real.pi / 2) :
    HasDerivAt (fun θ' => pscF α G a j z θ') (pscF α G a (j + 1) z θ) θ := by
  obtain ⟨D, hD0, hDle⟩ := pscF_term_le hα hα2 hG a (j + 1) hz hθ hθ2
  refine hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ)
    (u := fun m : ℕ => D * Work.FTS.PhiStar.Series.SmoothAux.maj m)
    (g := fun m y => pscA α G a m z
      * iteratedDeriv j (Work.FTS.PhiStar.Gegenbauer.eFam m) y)
    (g' := fun m y => pscA α G a m z
      * iteratedDeriv (j + 1) (Work.FTS.PhiStar.Gegenbauer.eFam m) y)
    (Work.FTS.PhiStar.Series.SmoothAux.summable_maj.mul_left D)
    isOpen_Ioo isPreconnected_Ioo ?_ ?_ (t := Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2))
    (y₀ := θ) ⟨by linarith, by linarith [Real.pi_pos]⟩ ?_
    ⟨by linarith, by linarith [Real.pi_pos]⟩
  · intro m y _
    exact (hasDerivAt_iteratedDeriv_eFam m j y).const_mul _
  · intro m y hy
    have hmem : (z, y) ∈ pscRect z θ := ⟨⟨by linarith, by linarith⟩, hy⟩
    have h := hDle m (z, y) hmem
    rw [Real.norm_eq_abs] at h
    rw [Real.norm_eq_abs]
    exact h
  · obtain ⟨D', hD'0, hD'le⟩ := pscF_term_le hα hα2 hG a j hz hθ hθ2
    refine Summable.of_norm_bounded
      (Work.FTS.PhiStar.Series.SmoothAux.summable_maj.mul_left D') (fun m => ?_)
    have hmem : (z, θ) ∈ pscRect z θ :=
      ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith [Real.pi_pos]⟩⟩
    have h := hD'le m (z, θ) hmem
    rw [Real.norm_eq_abs] at h
    rw [Real.norm_eq_abs]
    exact h

/-! ## The bootstrap -/

theorem pscF_contDiffOn {α : ℝ} (hα : 0 < α) (hα2 : α < 2) {G : ℝ → ℝ → ℝ}
    (hG : SmoothCptQ G) :
    ∀ (n a j : ℕ), ContDiffOn ℝ n (Function.uncurry (pscF α G a j))
      Work.FTS.EllipticEst.Q0 := by
  intro n
  induction n with
  | zero =>
    intro a j
    exact contDiffOn_zero.mpr (pscF_continuousOn hα hα2 hG a j)
  | succ n ih =>
    intro a j
    have h := Work.FTS.PhiStar.Series.SmoothAux.contDiffOn_succ_of_partials
      (U := Work.FTS.EllipticEst.Q0) (f := pscF α G a j) (g := pscF α G (a + 1) j)
      (h := pscF α G a (j + 1)) (n := n) Work.FTS.EllipticEst.isOpen_Q0
      (fun z θ hzθ => by
        obtain ⟨hz, hθ, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
        exact pscF_hasDerivAt_z hα hα2 hG a j hz hθ hθ2)
      (fun z θ hzθ => by
        obtain ⟨hz, hθ, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
        exact pscF_hasDerivAt_theta hα hα2 hG a j hz hθ hθ2)
      (ih (a + 1) j) (ih a (j + 1))
    simpa only [Nat.cast_add, Nat.cast_one] using h

end CptQSmooth

theorem psiSeries_smooth_of_cptQ {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.PhiStar.Honesty.SmoothCptQ G) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.PhiStar.Series.psiSeries α G) := by
  have hα2 : α < 2 := by linarith
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  have key := CptQSmooth.pscF_contDiffOn (α := α) (G := G) hα hα2 hG n 0 0
  refine key.congr (fun p hp => ?_)
  exact (congrFun (congrFun (CptQSmooth.pscF_zero_zero α G) p.1) p.2).symm

end Work.FTS.PhiStar.Honesty
