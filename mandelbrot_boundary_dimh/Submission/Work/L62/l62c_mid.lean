import Mathlib
import Submission.Work.L62.avail_up
import Submission.Work.L62.l62c_basic
import Submission.Work.L62.pushdown_section
import Submission.Work.L62.contract_escape
import Submission.Work.L62.local_branch_disc
import Submission.Work.L62.section_chain
import Submission.Work.L62.exists_section_horn
import Submission.Work.L62.avail_horn_section_up

/-!
# L62 (e) — the middle of the chain (fixed `β`)

Target `Work.L62.l62c : L62Statement`.  This file builds the *model* middle chain of Shishikura's
Lemma 6.2 (i.e. for `ĥ = d.E - β`, the unperturbed map) at the upper end, for a fixed `β`:

* `exists_preimage_noncritical`: a point `ζ₁ ∈ Bu` over `ζ₀ + β` which is not a critical point;
* `sigma_orbit_escape`: the orbit of any relatively compact piece of `Bu` under a section `σ` of
  `ĥ` escapes to the upper end (this is the "`j₀` exists" step);
* `middle_chain_ball`: the local branch at `ζ₁` over the fixed base disc `ball ζ₀ ρ`;
* `model_middle_chain`: the assembled model chain.
-/

namespace Work.L62

open MandelDim Set Filter Topology
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-! ## A non-critical preimage of the base point -/

/-- **A non-critical preimage of the base point.**  If `ζ₀` is not a critical value of
`ĥ = d.E - β` (i.e. `ζ₀ + β` is not in the critical class `v + ℤ`), then some preimage of `ζ₀`
under `ĥ` in the upper horn `Bu` is not a critical point. -/
theorem exists_preimage_noncritical (d : ParabData g₀ D) (hd : HornData d)
    {β ζ₀ : ℂ} (hξ : ∀ k : ℤ, ζ₀ + β ≠ hd.v + (k : ℂ)) :
    ∃ ζ₁ ∈ hd.Bu, d.E ζ₁ - β = ζ₀ ∧ deriv d.E ζ₁ ≠ 0 := by
  obtain ⟨w, hw, hwE⟩ := hd.surj_u (ζ₀ + β)
  refine ⟨w, hw, ?_, ?_⟩
  · rw [hwE]; ring
  · intro h0
    obtain ⟨k, hk⟩ := hd.crit w (Or.inl hw) h0
    exact hξ k (hwE.symm.trans hk)

/-! ## `d.E` is holomorphic on the two horns -/

theorem differentiableOn_E_Bu (d : ParabData g₀ D) (hd : HornData d) :
    DifferentiableOn ℂ d.E hd.Bu :=
  d.Φ_holo.comp (d.φ_holo.mono fun w hw => (hd.sub (Or.inl hw)).1)
    fun w hw => (hd.sub (Or.inl hw)).2

theorem differentiableOn_sub_Bu (d : ParabData g₀ D) (hd : HornData d) (β : ℂ) :
    DifferentiableOn ℂ (fun w => d.E w - β) hd.Bu :=
  (differentiableOn_E_Bu d hd).sub (differentiableOn_const β)

/-! ## Escaping to the upper end -/

/-- **The section orbit escapes to the upper end.**  Let `σ` be a holomorphic `T`-equivariant
section of `ĥ = d.E - β` over `Bu` (with values in `Bu`) which is asymptotically a translation by
`β` at the upper end, and let `0 < Im β`.  Then the `σ`-orbit of any `L ⊆ Bu` whose `π`-image is
relatively compact in `Ω = {0} ∪ π '' Bu` escapes to the upper end.

The proof pushes `σ` down to the cylinder (`pushdown_section`): `H = pushdown σ` is a holomorphic
self-map of the bounded domain `Ω` with `H 0 = 0` and `‖deriv H 0‖ = e^{-2π Im β} < 1`, so
`H^n → 0` on compacts (`contract_escape`); and `π (σ^n w) = H^n (π w)` because `π` intertwines `σ`
and `H` (`pushdown_piExp`). -/
theorem sigma_orbit_escape (d : ParabData g₀ D) (hd : HornData d)
    {β : ℂ} (hβ : 0 < β.im) {σ : ℂ → ℂ}
    (hσdiff : DifferentiableOn ℂ σ hd.Bu) (hσmem : ∀ w ∈ hd.Bu, σ w ∈ hd.Bu)
    (hσsec : ∀ w ∈ hd.Bu, d.E (σ w) - β = w)
    (hσT : ∀ w ∈ hd.Bu, σ (w + 1) = σ w + 1)
    (hasym : Filter.Tendsto (fun w => σ w - w - β) MandelDim.upperEnd (nhds 0))
    {L : Set ℂ} (hL : L ⊆ hd.Bu)
    (hLc : ∃ Kc : Set ℂ, IsCompact Kc ∧ piExp '' L ⊆ Kc ∧ Kc ⊆ upOmega d hd) :
    ∀ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ w ∈ L, M < ((σ)^[n] w).im := by
  obtain ⟨hHdiff, hHmap, hH0, hHder, hHrel⟩ :=
    pushdown_section d hd hβ hσdiff hσmem hσsec hσT hasym
  set H : ℂ → ℂ := MandelDim.pushdown σ with hHdef
  have hder_lt : ‖deriv H 0‖ < 1 := by
    rw [hHder, norm_piExp]
    rw [show (-(2 * Real.pi) * β.im) = -(2 * Real.pi * β.im) by ring]
    exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  obtain ⟨Kc, hKcc, hKL, hKcΩ⟩ := hLc
  intro M
  have hδpos : 0 < Real.exp (-(2 * Real.pi) * M) := Real.exp_pos _
  obtain ⟨N, hN⟩ := contract_escape (isOpen_upOmega d hd) (isBounded_upOmega d hd)
    (preconnected_upOmega d hd) (mem_insert_iff.mpr (Or.inl rfl)) hHdiff hHmap hH0 hder_lt
    (Real.exp (-(2 * Real.pi) * M)) hδpos Kc hKcΩ hKcc
  refine ⟨N, fun n hn w hw => ?_⟩
  -- the intertwining relation `π (σ^[n] w) = H^[n] (π w)`
  have hiter : ∀ t : ℕ, (σ^[t]) w ∈ hd.Bu := by
    intro t
    induction t with
    | zero => exact hL hw
    | succ s ih =>
        rw [Function.iterate_succ_apply']
        exact hσmem _ ih
  have hrel : ∀ t : ℕ, H^[t] (piExp w) = piExp ((σ)^[t] w) := by
    intro t
    induction t with
    | zero => simp
    | succ s ih =>
        rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
        exact hHrel _ (hiter s)
  have hmem : H^[n] (piExp w) ∈ Metric.ball 0 (Real.exp (-(2 * Real.pi) * M)) :=
    hN n hn (piExp w) (hKL (mem_image_of_mem piExp hw))
  rw [hrel n] at hmem
  rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_piExp] at hmem
  have h2 : -(2 * Real.pi) * ((σ^[n]) w).im < -(2 * Real.pi) * M := Real.exp_lt_exp.mp hmem
  nlinarith [Real.pi_pos]

/-! ## The chain generated by a section -/

/-- The chain generated by a section `σ` of `ĥ` over `W₁`: `W 0 = W₀`, `W (j+1) = σ^[j] '' W₁`. -/
def secChain (σ : ℂ → ℂ) (W₀ W₁ : Set ℂ) : ℕ → Set ℂ
  | 0 => W₀
  | (j + 1) => (σ)^[j] '' W₁

@[simp] theorem secChain_zero (σ : ℂ → ℂ) (W₀ W₁ : Set ℂ) : secChain σ W₀ W₁ 0 = W₀ := rfl

@[simp] theorem secChain_succ (σ : ℂ → ℂ) (W₀ W₁ : Set ℂ) (j : ℕ) :
    secChain σ W₀ W₁ (j + 1) = (σ)^[j] '' W₁ := rfl

/-- **The chain generated by a section is a `ĥ`-chain.** -/
theorem secChain_spec (d : ParabData g₀ D) (hd : HornData d)
    {β : ℂ} {σ : ℂ → ℂ}
    (hσdiff : DifferentiableOn ℂ σ hd.Bu) (hσmem : ∀ w ∈ hd.Bu, σ w ∈ hd.Bu)
    (hσsec : ∀ w ∈ hd.Bu, d.E (σ w) - β = w)
    {W₀ W₁ : Set ℂ} (hW₀o : IsOpen W₀) (hW₀c : IsConnected W₀)
    (hW₁sub : W₁ ⊆ hd.Bu) (hW₁o : IsOpen W₁) (hW₁c : IsConnected W₁)
    (hW0 : (fun w => d.E w - β) '' W₁ = W₀)
    (hW1inj : Set.InjOn (fun w => d.E w - β) W₁) :
    (∀ j, IsOpen (secChain σ W₀ W₁ j) ∧ IsConnected (secChain σ W₀ W₁ j)) ∧
    (∀ j, secChain σ W₀ W₁ (j + 1) ⊆ hd.Bu) ∧
    (∀ j, Set.InjOn (fun w => d.E w - β) (secChain σ W₀ W₁ (j + 1)) ∧
        (fun w => d.E w - β) '' secChain σ W₀ W₁ (j + 1) = secChain σ W₀ W₁ j) := by
  -- `σ` maps `Bu` into itself, iterated
  have hmem_iter : ∀ t : ℕ, ∀ w ∈ hd.Bu, ((σ)^[t]) w ∈ hd.Bu := by
    intro t
    induction t with
    | zero => intro w hw; simpa using hw
    | succ s ih =>
        intro w hw
        rw [Function.iterate_succ_apply']
        exact hσmem _ (ih w hw)
  -- `ĥ^[t]` is a left inverse of `σ^[t]` on `Bu`
  have hleft : ∀ t : ℕ, ∀ w ∈ hd.Bu, (fun u => d.E u - β)^[t] (((σ)^[t]) w) = w := by
    intro t
    induction t with
    | zero => intro w hw; simp
    | succ s ih =>
        intro w hw
        have h1 : d.E (((σ)^[s+1]) w) - β = ((σ)^[s]) w := by
          rw [Function.iterate_succ_apply']
          exact hσsec _ (hmem_iter s w hw)
        rw [Function.iterate_succ_apply (f := fun u => d.E u - β) (n := s) (x := ((σ)^[s+1]) w),
          h1]
        exact ih w hw
  -- `σ^[t]` is injective on `Bu`
  have hinj_iter : ∀ t : ℕ, Set.InjOn ((σ)^[t]) hd.Bu := by
    intro t x hx y hy hxy
    rw [← hleft t x hx, ← hleft t y hy, hxy]
  -- two distinct points of `Bu`
  have htwo : ∃ a b : ℂ, a ∈ hd.Bu ∧ b ∈ hd.Bu ∧ a ≠ b := by
    refine ⟨Complex.I * ((hd.η + 1 : ℝ) : ℂ), Complex.I * ((hd.η + 1 : ℝ) : ℂ) + 1, ?_, ?_, ?_⟩
    · exact hd.upper (by simp)
    · rw [hd.Bu_T]; exact hd.upper (by simp)
    · intro h
      have h' : Complex.I * ((hd.η + 1 : ℝ) : ℂ) + 0
          = Complex.I * ((hd.η + 1 : ℝ) : ℂ) + 1 := by simpa using h
      exact one_ne_zero (add_left_cancel h'.symm)
  -- analyticity and non-constancy of `σ^[t]`
  have han : ∀ t : ℕ, AnalyticOnNhd ℂ ((σ)^[t]) hd.Bu :=
    fun t => (hσdiff.iterate hσmem t).analyticOnNhd hd.Bu_open
  have hnc : ∀ t : ℕ, ¬ ∃ c, ∀ z ∈ hd.Bu, ((σ)^[t]) z = c := by
    rintro t ⟨c, hc⟩
    obtain ⟨a, b, ha, hb, hab⟩ := htwo
    exact hab (hinj_iter t ha hb (by rw [hc a ha, hc b hb]))
  have hopen : ∀ t : ℕ, ∀ s ⊆ hd.Bu, IsOpen s → IsOpen (((σ)^[t]) '' s) := fun t =>
    ((han t).is_constant_or_isOpen hd.Bu_conn.isPreconnected).resolve_left (hnc t)
  have hcont : ∀ t : ℕ, ContinuousOn ((σ)^[t]) hd.Bu :=
    fun t => (hσdiff.iterate hσmem t).continuousOn
  refine ⟨?_, ?_, ?_⟩
  · intro j
    rcases j with _ | k
    · exact ⟨hW₀o, hW₀c⟩
    · exact ⟨hopen k W₁ hW₁sub hW₁o,
        hW₁c.image _ (hcont k |>.mono hW₁sub)⟩
  · intro j
    cases j with
    | zero => simpa using hW₁sub
    | succ k =>
        rw [secChain_succ]
        intro z hz
        obtain ⟨w, hw, rfl⟩ := hz
        exact hmem_iter (k + 1) w (hW₁sub hw)
  · intro j
    rcases j with _ | k
    · have h1 : secChain σ W₀ W₁ (0 + 1) = W₁ := by simp
      rw [h1]
      exact ⟨hW1inj, hW0⟩
    · have hstep : ∀ x ∈ W₁, (fun u => d.E u - β) (((σ)^[k+1]) x) = ((σ)^[k]) x := by
        intro x hx
        rw [Function.iterate_succ_apply']
        exact hσsec _ (hmem_iter k x (hW₁sub hx))
      constructor
      · intro a ha b hb hab
        obtain ⟨x, hx, rfl⟩ := ha
        obtain ⟨y, hy, rfl⟩ := hb
        rw [hstep x hx, hstep y hy] at hab
        rw [hinj_iter k (hW₁sub hx) (hW₁sub hy) hab]
      · show (fun w => d.E w - β) '' (((σ)^[k+1]) '' W₁) = ((σ)^[k]) '' W₁
        rw [← Set.image_comp]
        exact Set.image_congr hstep

/-! ## The local branch over the base disc -/

/-- **The first step of the chain.**  If `ζ₀ + β` is not in the critical class (`hξ`), then there
is a radius `ρ₀ > 0` such that for every `0 < ρ ≤ ρ₀` the disc `W₀ = ball ζ₀ ρ` has a preimage
`W₁` under `ĥ = d.E - β` which is open, connected, contained in the horn `Bu`, mapped bijectively
onto `W₀`, and contained in a compact subset of `Bu`. -/
theorem middle_chain_ball (d : ParabData g₀ D) (hd : HornData d) {β ζ₀ : ℂ}
    (hξ : ∀ k : ℤ, ζ₀ + β ≠ hd.v + (k : ℂ)) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ W₀ W₁ Cc : Set ℂ, W₀ = Metric.ball ζ₀ ρ ∧ W₁ ⊆ Cc ∧ IsCompact Cc ∧ Cc ⊆ hd.Bu ∧
        IsOpen W₁ ∧ IsConnected W₁ ∧ (fun w => d.E w - β) '' W₁ = W₀ ∧
        Set.InjOn (fun w => d.E w - β) W₁ := by
  obtain ⟨ζ₁, hζ₁Bu, hζ₁E, hζ₁d⟩ := exists_preimage_noncritical d hd hξ
  have hFana : AnalyticAt ℂ (fun w => d.E w - β) ζ₁ :=
    ((differentiableOn_E_Bu d hd).analyticAt (hd.Bu_open.mem_nhds hζ₁Bu)).sub analyticAt_const
  have hder : deriv (fun w => d.E w - β) ζ₁ ≠ 0 := by
    rw [deriv_sub_const]
    exact hζ₁d
  obtain ⟨r, hr, ψ, hψdiff, hψ0, hψinv, hψmap, hψinj⟩ :=
    local_branch_disc hFana hder hd.Bu_open hζ₁Bu
  rw [hζ₁E] at hψdiff hψ0 hψinv hψmap hψinj
  refine ⟨3 * r / 4, by linarith, fun ρ hρ hρr => ?_⟩
  have hρr' : ρ ≤ r := by linarith
  refine ⟨Metric.ball ζ₀ ρ, ψ '' Metric.ball ζ₀ ρ, ψ '' Metric.closedBall ζ₀ (3 * r / 4),
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Set.image_mono (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by linarith)))
  · exact (isCompact_closedBall ζ₀ (3 * r / 4)).image_of_continuousOn
      (hψdiff.continuousOn.mono (Metric.closedBall_subset_ball (by linarith)))
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact hψmap (Metric.closedBall_subset_ball (by linarith) hw)
  · -- openness, from the open mapping theorem
    have hnc : ¬ ∃ c, ∀ z ∈ Metric.ball ζ₀ r, ψ z = c := by
      rintro ⟨c, hc⟩
      have h1 : (ζ₀ : ℂ) ∈ Metric.ball ζ₀ r := Metric.mem_ball_self hr
      have h2 : ζ₀ + ((r / 2 : ℝ) : ℂ) ∈ Metric.ball ζ₀ r := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      have hne : (ζ₀ : ℂ) ≠ ζ₀ + ((r / 2 : ℝ) : ℂ) := by
        intro h
        have h3 := congrArg Complex.re h
        simp at h3
        linarith
      exact hne (hψinj h1 h2 (by rw [hc _ h1, hc _ h2]))
    have hopen := ((hψdiff.analyticOnNhd Metric.isOpen_ball).is_constant_or_isOpen
      Metric.isPreconnected_ball).resolve_left hnc
    exact hopen (Metric.ball ζ₀ ρ) (fun z hz => Metric.ball_subset_ball hρr' hz) Metric.isOpen_ball
  · exact ((convex_ball ζ₀ ρ).isConnected ⟨ζ₀, Metric.mem_ball_self hρ⟩).image ψ
      (hψdiff.continuousOn.mono (fun z hz => Metric.ball_subset_ball hρr' hz))
  · show (fun w => d.E w - β) '' (ψ '' Metric.ball ζ₀ ρ) = Metric.ball ζ₀ ρ
    rw [← Set.image_comp]
    exact (Set.image_congr (fun z hz => hψinv z (Metric.ball_subset_ball hρr' hz))).trans
      (Set.image_id _)
  · intro a ha b hb hab
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    have hx' : d.E (ψ x) - β = x := hψinv x (Metric.ball_subset_ball hρr' hx)
    have hy' : d.E (ψ y) - β = y := hψinv y (Metric.ball_subset_ball hρr' hy)
    have hab' : d.E (ψ x) - β = d.E (ψ y) - β := hab
    rw [hx', hy'] at hab'
    rw [hab']

/-! ## The model middle chain -/

/-- **The model middle chain (upper end).**  For `β` with `0 < Im β` such that the upper horn
avoids the critical values of `ĥ = d.E - β` (`havoid`) and a base point `ζ₀ ∉ v + ℤ - β`, and for
every small `ρ` and every depth `M`, there is a chain of discs `W j` starting at `ball ζ₀ ρ` with
`ĥ '' W (j+1) = W j` bijectively, all `W (j+1) ⊆ Bu`, and reaching depth `M` in finitely many
steps (`W m ⊆ {M < Im}`). -/
theorem model_middle_chain (d : ParabData g₀ D) (hd : HornData d)
    {β ζ₀ : ℂ} (hβ : 0 < β.im)
    (havoid : ∀ w ∈ hd.Bu, ∀ k : ℤ, w + β ≠ hd.v + (k : ℂ))
    (hξ : ∀ k : ℤ, ζ₀ + β ≠ hd.v + (k : ℂ)) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ M : ℝ,
      ∃ (W : ℕ → Set ℂ) (m : ℕ), W 0 = Metric.ball ζ₀ ρ ∧
        (∀ j, IsOpen (W j) ∧ IsConnected (W j)) ∧
        (∀ j, W (j + 1) ⊆ hd.Bu ∧ Set.InjOn (fun w => d.E w - β) (W (j + 1)) ∧
          (fun w => d.E w - β) '' W (j + 1) = W j) ∧
        W m ⊆ {w : ℂ | M < w.im} := by
  obtain ⟨y₀, x₀, σ, hy₀, hx₀, hxy, hσdiff, hσ0, hσsec, hσT, hasym⟩ :=
    avail_horn_section_up d hd havoid
  have hσmem : ∀ w ∈ hd.Bu, σ w ∈ hd.Bu := fun w hw => (hσsec w hw).1
  have hσsec' : ∀ w ∈ hd.Bu, d.E (σ w) - β = w := fun w hw => (hσsec w hw).2
  obtain ⟨ρ₀, hρ₀, hball⟩ := middle_chain_ball d hd hξ
  refine ⟨ρ₀, hρ₀, fun ρ hρ hρρ₀ M => ?_⟩
  obtain ⟨W₀, W₁, Cc, hW₀eq, hW₁Cc, hCcc, hCcBu, hW₁o, hW₁c, hW₁img, hW₁inj⟩ := hball ρ hρ hρρ₀
  have hW₀o : IsOpen W₀ := by rw [hW₀eq]; exact Metric.isOpen_ball
  have hW₀c : IsConnected W₀ := by
    rw [hW₀eq]; exact (convex_ball ζ₀ ρ).isConnected ⟨ζ₀, Metric.mem_ball_self hρ⟩
  have hW₁sub : W₁ ⊆ hd.Bu := fun z hz => hCcBu (hW₁Cc hz)
  obtain ⟨hoc, hsub, hchain⟩ :=
    secChain_spec d hd hσdiff hσmem hσsec' hW₀o hW₀c hW₁sub hW₁o hW₁c hW₁img hW₁inj
  -- the escape: the pushdown compactum `π '' Cc ⊆ Ω` is pushed into a small disc
  obtain ⟨N, hN⟩ := sigma_orbit_escape d hd hβ hσdiff hσmem hσsec' hσT hasym hW₁sub
    ⟨piExp '' Cc, hCcc.image continuous_piExp, Set.image_mono hW₁Cc,
      fun z hz => mem_insert_iff.mpr (Or.inr (by obtain ⟨u, hu, rfl⟩ := hz; exact ⟨u, hCcBu hu, rfl⟩))⟩ M
  refine ⟨secChain σ W₀ W₁, N + 1, ?_, hoc, fun j => ⟨hsub j, hchain j⟩, ?_⟩
  · rw [secChain_zero, hW₀eq]
  · rw [secChain_succ]
    rintro z ⟨w, hw, rfl⟩
    simpa using hN N le_rfl w hw

end

end Work.L62