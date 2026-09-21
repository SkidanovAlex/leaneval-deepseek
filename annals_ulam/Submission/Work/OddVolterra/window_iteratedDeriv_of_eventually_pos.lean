import Mathlib

/-!
# Differentiating parametric integrals of the form `∫ Ψ ^ n * √Ψ`

The main result of this file is `window_iteratedDeriv_of_eventually_pos`: if
`Ψ : ℝ → ℝ → ℝ` is jointly smooth and strictly positive on a window around
`{s} × [c,d]`, then the `(n+1)`-st derivative at `s` of the parametric integral
`u ↦ ∫ t in c..d, Ψ u t ^ n * √(Ψ u t)` equals the integral over `t` of the
`(n+1)`-st derivatives of the sections `u ↦ Ψ u t ^ n * √(Ψ u t)`.

The proof reduces to the case of a *globally* smooth integrand by gluing `Ψ` to
the constant `1` outside a neighbourhood of the window using a smooth bump, and
then differentiates under the integral sign `(n+1)` times.

Note that `ContDiff ℝ ⊤` (with `⊤ = ω`) means *analytic*; throughout the
auxiliary statements we use the weaker `C^∞` level `ContDiff ℝ ∞`.
-/

namespace Work.OddVolterra

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-! ## Partial derivatives in the first variable -/

/-- The partial derivative in the first variable of a function `ℝ × ℝ → ℝ`,
realised as the Fréchet derivative evaluated at the vector `(1,0)`. -/
def pderiv (G : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun q => fderiv ℝ G q (1, 0)

lemma continuous_section_left {G : ℝ × ℝ → ℝ} (hG : Continuous G) (u : ℝ) :
    Continuous fun t : ℝ => G (u, t) :=
  hG.comp (continuous_const.prodMk continuous_id)

lemma pderiv_hasDerivAt_section {G : ℝ × ℝ → ℝ} {x t : ℝ} (hG : DifferentiableAt ℝ G (x, t)) :
    HasDerivAt (fun u : ℝ => G (u, t)) (pderiv G (x, t)) x := by
  have hg : HasFDerivAt (fun u : ℝ => (u, t)) (ContinuousLinearMap.inl ℝ ℝ ℝ) x :=
    hasFDerivAt_prodMk_left x t
  have hcomp := hG.hasFDerivAt.comp_hasDerivAt x hg.hasDerivAt
  rw [ContinuousLinearMap.inl_apply] at hcomp
  exact hcomp

lemma pderiv_eq_deriv {G : ℝ × ℝ → ℝ} {x t : ℝ} (hG : DifferentiableAt ℝ G (x, t)) :
    pderiv G (x, t) = deriv (fun u : ℝ => G (u, t)) x :=
  (pderiv_hasDerivAt_section hG).deriv.symm

lemma contDiff_pderiv {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (pderiv G) :=
  (hG.fderiv_right le_rfl).clm_apply contDiff_const

lemma contDiff_pderiv_iterate (m : ℕ) {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (pderiv^[m] G) := by
  induction m with
  | zero => simpa using hG
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact contDiff_pderiv ih

lemma pderiv_iterate_apply (m : ℕ) {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) :
    ∀ u t : ℝ, (pderiv^[m] G) (u, t) = iteratedDeriv m (fun v : ℝ => G (v, t)) u := by
  intro u t
  induction m generalizing u t with
  | zero => simp
  | succ m ih =>
      have hd : DifferentiableAt ℝ (pderiv^[m] G) (u, t) :=
        (contDiff_pderiv_iterate m hG).differentiable (by decide) (u, t)
      rw [Function.iterate_succ_apply', pderiv_eq_deriv hd]
      have heq : (fun v : ℝ => (pderiv^[m] G) (v, t))
          = iteratedDeriv m (fun v : ℝ => G (v, t)) := by
        funext v
        exact ih v t
      rw [heq, ← iteratedDeriv_succ]

/-! ## Differentiation under the integral sign -/

/-- The derivative of a parametric integral is the integral of the partial
derivative, for a globally `C^∞` integrand. -/
theorem deriv_integral_of_contDiff {c d : ℝ} (hcd : c ≤ d) {G : ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) (u : ℝ) :
    deriv (fun v : ℝ => ∫ t in c..d, G (v, t)) u = ∫ t in c..d, pderiv G (u, t) := by
  have hcontG : Continuous fun t : ℝ => G (u, t) := continuous_section_left hG.continuous u
  have hcontP : Continuous fun t : ℝ => pderiv G (u, t) :=
    continuous_section_left (contDiff_pderiv hG).continuous u
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Set.Icc (u - 1) (u + 1) ×ˢ Set.uIcc c d))
    (contDiff_pderiv hG).continuous.continuousOn
  have hs : Set.Icc (u - 1) (u + 1) ∈ 𝓝 u := Icc_mem_nhds (by linarith) (by linarith)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := c) (b := d) (bound := fun _ : ℝ => M) (x₀ := u)
    (F := fun v t => G (v, t)) (F' := fun v t => pderiv G (v, t))
    (s := Set.Icc (u - 1) (u + 1)) (μ := volume) hs
    (Filter.Eventually.of_forall fun v =>
      (continuous_section_left hG.continuous v).aestronglyMeasurable)
    (hcontG.intervalIntegrable c d)
    (hcontP.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t ht v hv => by
      have hmem : (v, t) ∈ Set.Icc (u - 1) (u + 1) ×ˢ Set.uIcc c d :=
        ⟨hv, ⟨le_of_lt ht.1, ht.2⟩⟩
      simpa using hM (v, t) hmem)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t ht v hv =>
      pderiv_hasDerivAt_section (hG.differentiable (by decide) (v, t)))
  exact key.2.deriv

/-- Iterated differentiation under the integral sign, globally `C^∞` integrand. -/
theorem iteratedDeriv_integral_of_contDiff (m : ℕ) {c d : ℝ} (hcd : c ≤ d)
    {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) :
    ∀ u : ℝ, iteratedDeriv m (fun v : ℝ => ∫ t in c..d, G (v, t)) u
      = ∫ t in c..d, (pderiv^[m] G) (u, t) := by
  intro u
  induction m generalizing u with
  | zero => simp
  | succ m ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv m (fun v : ℝ => ∫ t in c..d, G (v, t))
          = fun v : ℝ => ∫ t in c..d, (pderiv^[m] G) (v, t) := by
        funext v
        exact ih v
      rw [hfun, deriv_integral_of_contDiff hcd (contDiff_pderiv_iterate m hG) u]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Function.iterate_succ_apply']

/-- Iterated differentiation under the integral sign: the `m`-th derivative of
`u ↦ ∫ t in c..d, G (u,t)` at `s` is the integral of the `m`-th derivatives of
the sections. -/
theorem param_iteratedDeriv (m : ℕ) {c d : ℝ} (hcd : c ≤ d)
    {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (s : ℝ) :
    iteratedDeriv m (fun u : ℝ => ∫ t in c..d, G (u, t)) s =
      ∫ t in c..d, iteratedDeriv m (fun u : ℝ => G (u, t)) s := by
  rw [iteratedDeriv_integral_of_contDiff m hcd hG s]
  refine intervalIntegral.integral_congr fun t ht => ?_
  exact pderiv_iterate_apply m hG s t

/-! ## The windowed statement -/

theorem window_iteratedDeriv_of_eventually_pos (n : ℕ) (hn : 1 ≤ n) {c d s : ℝ} (hcd : c ≤ d)
    {Ψ : ℝ → ℝ → ℝ} (hΨ : ContDiff ℝ ⊤ (fun q : ℝ × ℝ => Ψ q.1 q.2))
    (hpos : ∃ ε > 0, ∀ u : ℝ, |u - s| < ε → ∀ t ∈ Set.Icc c d, 0 < Ψ u t) :
    iteratedDeriv (n + 1)
        (fun u : ℝ => ∫ t in c..d, Ψ u t ^ n * Real.sqrt (Ψ u t)) s =
      ∫ t in c..d,
        iteratedDeriv (n + 1) (fun u : ℝ => Ψ u t ^ n * Real.sqrt (Ψ u t)) s := by
  obtain ⟨ε, hε, hΨpos⟩ := hpos
  let Φ : ℝ × ℝ → ℝ := fun q => Ψ q.1 q.2
  have hΦ : ContDiff ℝ ∞ Φ := hΨ.of_le le_top
  -- Step 1: positivity on a product window around `{s} × [c,d]`.
  have hKsub : Set.Icc (s - ε / 2) (s + ε / 2) ×ˢ Set.Icc c d ⊆ {q : ℝ × ℝ | 0 < Φ q} := by
    rintro ⟨u, t⟩ ⟨hu, ht⟩
    refine hΨpos u ?_ t ht
    have hu' : |u - s| ≤ ε / 2 := by
      rw [abs_le]
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    linarith
  have hUopen : IsOpen {q : ℝ × ℝ | 0 < Φ q} := isOpen_lt continuous_const hΦ.continuous
  obtain ⟨ρ, hρ, hρK⟩ :=
    (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Set.Icc (s - ε / 2) (s + ε / 2) ×ˢ Set.Icc c d)).exists_thickening_subset_open
        hUopen hKsub
  have hpos_ext : ∀ u : ℝ, |u - s| ≤ ε / 2 →
      ∀ t ∈ Set.Icc (c - ρ / 2) (d + ρ / 2), 0 < Φ (u, t) := by
    intro u hu t ht
    have ht' : max c (min t d) ∈ Set.Icc c d :=
      ⟨le_max_left _ _, max_le hcd (min_le_right _ _)⟩
    have hu' : u ∈ Set.Icc (s - ε / 2) (s + ε / 2) := by
      rw [abs_le] at hu
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hmem : (u, t) ∈
        Metric.thickening ρ (Set.Icc (s - ε / 2) (s + ε / 2) ×ˢ Set.Icc c d) := by
      rw [Metric.mem_thickening_iff]
      refine ⟨(u, max c (min t d)), ⟨hu', ht'⟩, ?_⟩
      rw [Prod.dist_eq, dist_self, Real.dist_eq, max_eq_right (abs_nonneg _)]
      have hclamp : |t - max c (min t d)| ≤ ρ / 2 := by
        rcases le_total t d with htd | htd
        · rw [min_eq_left htd]
          rcases le_total c t with hct | hct
          · rw [max_eq_right hct, sub_self, abs_zero]; linarith [hρ]
          · rw [max_eq_left hct, abs_of_nonpos (by linarith)]
            linarith [ht.1]
        · rw [min_eq_right htd, max_eq_right hcd, abs_of_nonneg (by linarith)]
          linarith [ht.2]
      linarith [hclamp, hρ]
    exact hρK hmem
  -- Step 2: smooth bump glue.
  let β : ContDiffBump s := ⟨ε / 8, ε / 4, by linarith, by linarith⟩
  let γ : ContDiffBump ((c + d) / 2) :=
    ⟨(d - c) / 2 + ρ / 4, (d - c) / 2 + ρ / 2, by linarith, by linarith⟩
  let χ : ℝ × ℝ → ℝ := fun q => β q.1 * γ q.2
  let Ψ' : ℝ × ℝ → ℝ := fun q => 1 + χ q * (Φ q - 1)
  have hβsmooth : ContDiff ℝ ∞ (fun x : ℝ => β x) := β.contDiff
  have hγsmooth : ContDiff ℝ ∞ (fun x : ℝ => γ x) := γ.contDiff
  have hχsmooth : ContDiff ℝ ∞ χ := by
    show ContDiff ℝ ∞ (fun q : ℝ × ℝ => β q.1 * γ q.2)
    exact (hβsmooth.comp contDiff_fst).mul (hγsmooth.comp contDiff_snd)
  have hΨ'smooth : ContDiff ℝ ∞ Ψ' := by
    show ContDiff ℝ ∞ (fun q : ℝ × ℝ => 1 + χ q * (Φ q - 1))
    exact contDiff_const.add (hχsmooth.mul (hΦ.sub contDiff_const))
  have hχnn : ∀ q, 0 ≤ χ q := by
    intro q
    show 0 ≤ β q.1 * γ q.2
    exact mul_nonneg β.nonneg γ.nonneg
  have hχle : ∀ q, χ q ≤ 1 := by
    intro q
    show β q.1 * γ q.2 ≤ 1
    nlinarith [β.le_one (x := q.1), β.nonneg (x := q.1), γ.le_one (x := q.2),
      γ.nonneg (x := q.2)]
  have hχsupp : ∀ q, χ q ≠ 0 → β q.1 ≠ 0 ∧ γ q.2 ≠ 0 := by
    intro q hq
    constructor
    · intro h
      exact hq (by show β q.1 * γ q.2 = 0; rw [h, zero_mul])
    · intro h
      exact hq (by show β q.1 * γ q.2 = 0; rw [h, mul_zero])
  -- values of `β` and `γ`
  have hβmem : ∀ u : ℝ, |u - s| ≤ ε / 8 → β u = 1 := by
    intro u hu
    refine β.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Real.dist_eq, show β.rIn = ε / 8 from rfl]
    exact hu
  have hγmem : ∀ t ∈ Set.Icc c d, γ t = 1 := by
    intro t ht
    refine γ.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Real.dist_eq,
      show γ.rIn = (d - c) / 2 + ρ / 4 from rfl]
    have h1 : c ≤ t := ht.1
    have h2 : t ≤ d := ht.2
    have : |t - (c + d) / 2| ≤ (d - c) / 2 := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  have hΨ'pos : ∀ q, 0 < Ψ' q := by
    intro q
    rcases le_total 1 (Φ q) with h1 | h1
    · show 0 < 1 + χ q * (Φ q - 1)
      nlinarith [hχnn q]
    · by_cases hχ : χ q = 0
      · show 0 < 1 + χ q * (Φ q - 1)
        rw [hχ, zero_mul, add_zero]
        norm_num
      · obtain ⟨hβne, hγne⟩ := hχsupp q hχ
        have hq1 : |q.1 - s| < ε / 4 := by
          have hmem : q.1 ∈ Metric.ball s β.rOut := by
            rw [← β.support_eq]; exact hβne
          rw [Metric.mem_ball, Real.dist_eq, show β.rOut = ε / 4 from rfl] at hmem
          exact hmem
        have hq2 : q.2 ∈ Set.Icc (c - ρ / 2) (d + ρ / 2) := by
          have hmem : q.2 ∈ Metric.ball ((c + d) / 2) γ.rOut := by
            rw [← γ.support_eq]; exact hγne
          rw [Metric.mem_ball, Real.dist_eq, abs_lt,
            show γ.rOut = (d - c) / 2 + ρ / 2 from rfl] at hmem
          constructor <;> linarith [hmem.1, hmem.2]
        have hΦq : 0 < Φ q :=
          hpos_ext q.1 (by linarith [hq1]) q.2 hq2
        have hχpos : 0 < χ q := lt_of_le_of_ne (hχnn q) (Ne.symm hχ)
        show 0 < 1 + χ q * (Φ q - 1)
        have hkey : 1 + χ q * (Φ q - 1) = (1 - χ q) + χ q * Φ q := by ring
        rw [hkey]
        have h1 : 0 < χ q * Φ q := mul_pos hχpos hΦq
        have h2 : 0 ≤ 1 - χ q := by linarith [hχle q]
        linarith
  have hΨ'eq : ∀ u : ℝ, |u - s| ≤ ε / 8 → ∀ t ∈ Set.Icc c d, Ψ' (u, t) = Φ (u, t) := by
    intro u hu t ht
    have h1 : β u = 1 := hβmem u hu
    have h2 : γ t = 1 := hγmem t ht
    show 1 + χ (u, t) * (Φ (u, t) - 1) = Φ (u, t)
    have hχ1 : χ (u, t) = 1 := by show β u * γ t = 1; rw [h1, h2, one_mul]
    rw [hχ1]; ring
  -- Step 3: apply the global theorem to `G'` and transfer.
  let G : ℝ × ℝ → ℝ := fun q => Φ q ^ n * Real.sqrt (Φ q)
  let G' : ℝ × ℝ → ℝ := fun q => Ψ' q ^ n * Real.sqrt (Ψ' q)
  have hG'smooth : ContDiff ℝ ∞ G' := by
    show ContDiff ℝ ∞ (fun q : ℝ × ℝ => Ψ' q ^ n * Real.sqrt (Ψ' q))
    exact (hΨ'smooth.pow n).mul (hΨ'smooth.sqrt fun q => (hΨ'pos q).ne')
  have hwin : ∀ u : ℝ, |u - s| < ε / 8 → ∀ t ∈ Set.Icc c d, G' (u, t) = G (u, t) := by
    intro u hu t ht
    have := hΨ'eq u hu.le t ht
    show Ψ' (u, t) ^ n * Real.sqrt (Ψ' (u, t)) = Φ (u, t) ^ n * Real.sqrt (Φ (u, t))
    rw [this]
  have hL : (fun u : ℝ => ∫ t in c..d, G' (u, t)) =ᶠ[𝓝 s]
      (fun u : ℝ => ∫ t in c..d, G (u, t)) := by
    filter_upwards [Metric.ball_mem_nhds s (by linarith : (0 : ℝ) < ε / 8)] with u hu
    rw [Metric.mem_ball, Real.dist_eq] at hu
    exact intervalIntegral.integral_congr fun t ht =>
      hwin u hu t (by simpa [Set.uIcc_of_le hcd] using ht)
  have hR : (∫ t in c..d, iteratedDeriv (n + 1) (fun u : ℝ => G' (u, t)) s)
      = ∫ t in c..d, iteratedDeriv (n + 1) (fun u : ℝ => G (u, t)) s := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    have hEq : (fun u : ℝ => G' (u, t)) =ᶠ[𝓝 s] (fun u : ℝ => G (u, t)) := by
      filter_upwards [Metric.ball_mem_nhds s (by linarith : (0 : ℝ) < ε / 8)] with u hu
      rw [Metric.mem_ball, Real.dist_eq] at hu
      exact hwin u hu t (by simpa [Set.uIcc_of_le hcd] using ht)
    exact (hEq.iteratedDeriv (n + 1)).eq_of_nhds
  have hmain := param_iteratedDeriv (n + 1) hcd hG'smooth s
  have hfinal : iteratedDeriv (n + 1) (fun u : ℝ => ∫ t in c..d, G (u, t)) s
      = ∫ t in c..d, iteratedDeriv (n + 1) (fun u : ℝ => G (u, t)) s := by
    rw [← (hL.iteratedDeriv (n + 1)).eq_of_nhds, hmain, hR]
  exact hfinal

end

end Work.OddVolterra
