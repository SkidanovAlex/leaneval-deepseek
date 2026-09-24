import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

noncomputable section
open Set Metric Filter Topology
open scoped Topology BoundedContinuousFunction

namespace Commons.Analysis.Complex.Montel

/-- **Two-point Lipschitz bound** for a function analytic and bounded on a ball: if `g` is analytic
on `ball 0 R` and `‖g z‖ ≤ M` there, then for `z, w` in the closed ball of radius `r < R`,
`‖g z - g w‖ ≤ (2 * M / (R - r)) * ‖z - w‖`.

Proof: at each `x ∈ closedBall 0 r` apply Cauchy's estimate for the first derivative on the disc of
radius `(R - r) / 2` centred at `x` (which is contained in `ball 0 R`) to obtain
`‖deriv g x‖ ≤ M / ((R - r)/2)`, then integrate along the segment with the mean value inequality. -/
private theorem norm_sub_le_of_analyticOnNhd_closedBall {g : ℂ → ℂ} {r R M : ℝ}
    (hrR : r < R) (hM : 0 ≤ M)
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 R))
    (hgb : ∀ z ∈ Metric.ball 0 R, ‖g z‖ ≤ M) :
    ∀ z w : ℂ, z ∈ Metric.closedBall 0 r → w ∈ Metric.closedBall 0 r →
      ‖g z - g w‖ ≤ (2 * M / (R - r)) * ‖z - w‖ := by
  intro z w hz hw
  set ρ : ℝ := (R - r) / 2 with hρdef
  have hRr : 0 < R - r := sub_pos.mpr hrR
  have hρ : 0 < ρ := half_pos hRr
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hzw : ‖g z - g w‖ ≤ (M / ρ) * ‖w - z‖ := by
    have hderiv : ∀ x ∈ Metric.closedBall 0 r, ‖fderiv ℂ g x‖ ≤ M / ρ := by
      intro x hx
      rw [← norm_deriv_eq_norm_fderiv]
      have hxr : ‖x‖ ≤ r := by simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hx)
      have hsub : Metric.closedBall x ρ ⊆ Metric.ball 0 R := by
        intro y hy
        have hyρ : ‖y - x‖ ≤ ρ := by simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hy)
        have hle : ‖y‖ ≤ r + ρ := by
          calc ‖y‖ = ‖x + (y - x)‖ := by ring_nf
            _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
            _ ≤ r + ρ := add_le_add hxr hyρ
        have h2 : r + ρ = (R + r) / 2 := by rw [hρdef]; ring
        have hR2 : (R + r) / 2 < R := by linarith
        have : ‖y‖ < R := by linarith [hle, h2, hR2]
        simpa [dist_eq_norm] using this
      have hdiff : DiffContOnCl ℂ g (Metric.ball x ρ) := by
        refine DifferentiableOn.diffContOnCl ?_
        rw [closure_ball x hρne]
        exact hg.differentiableOn.mono hsub
      have hsphere : ∀ y ∈ Metric.sphere x ρ, ‖g y‖ ≤ M := by
        intro y hy
        exact hgb y (hsub (Metric.sphere_subset_closedBall hy))
      exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hdiff hsphere
    have hdiffAt : ∀ x ∈ Metric.closedBall 0 r, DifferentiableAt ℂ g x := by
      intro x hx
      exact (hg x (closedBall_subset_ball hrR hx)).differentiableAt
    have := Convex.norm_image_sub_le_of_norm_fderiv_le hdiffAt hderiv (convex_closedBall 0 r) hz hw
    rwa [norm_sub_rev] at this
  have hconst : M / ρ = 2 * M / (R - r) := by
    rw [hρdef]; field_simp
  have hnorm : ‖w - z‖ = ‖z - w‖ := norm_sub_rev w z
  rw [hconst, hnorm] at hzw
  exact hzw

theorem exists_subseq_tendstoLocallyUniformlyOn {f : ℕ → ℂ → ℂ}
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (Metric.ball 0 1))
    (hb : ∀ n, ∀ z ∈ Metric.ball 0 1, ‖f n z‖ ≤ 1) :
    ∃ g : ℂ → ℂ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g Filter.atTop (Metric.ball 0 1) := by
  classical
  -- ## Radii and compact exhaustions of the unit disc
  let r : ℕ → ℝ := fun k => 1 - ((k : ℝ) + 1)⁻¹
  have hr_lt : ∀ k, r k < 1 := by
    intro k
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have : 0 < ((k : ℝ) + 1)⁻¹ := inv_pos.mpr hpos
    simp only [r]; linarith
  have hr_nn : ∀ k, 0 ≤ r k := by
    intro k
    have h1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h2 : ((k : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    simp only [r]; linarith
  have hr_tend : Tendsto r Filter.atTop (𝓝 1) := by
    have hcast : Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℝ))) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hlim : Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℝ))⁻¹) Filter.atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hcast
    have hlim' : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) Filter.atTop (𝓝 0) := by
      simpa [Nat.cast_add, Nat.cast_one] using hlim
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (𝓝 1) := tendsto_const_nhds
    have := hone.sub hlim'
    simpa [r] using this
  let K : ℕ → Set ℂ := fun k => Metric.closedBall 0 (r k)
  have hK_compact : ∀ k, IsCompact (K k) := fun k => isCompact_closedBall 0 (r k)
  have hK_sub : ∀ k, K k ⊆ Metric.ball 0 1 := by
    intro k z hz
    have hzr : ‖z‖ ≤ r k := by simpa [K, dist_eq_norm] using (Metric.mem_closedBall.mp hz)
    rw [Metric.mem_ball, dist_eq_norm]
    have : ‖z‖ < 1 := lt_of_le_of_lt hzr (hr_lt k)
    simpa using this
  haveI hKcpt : ∀ k, CompactSpace (K k) := fun k => isCompact_iff_compactSpace.mp (hK_compact k)
  -- ## The functions restricted to each compact exhaustion
  let Fn : (k : ℕ) → ℕ → (K k →ᵇ ℂ) := fun k n =>
    BoundedContinuousFunction.mkOfCompact
      { toFun := fun x : K k => f n x
        continuous_toFun := ((hf n).continuousOn.mono (hK_sub k)).domRestrict }
  have hFn_apply : ∀ (k n : ℕ) (x : K k), Fn k n x = f n x := by
    intro k n x
    simp only [Fn, BoundedContinuousFunction.mkOfCompact_apply]; rfl
  -- ## Uniform Lipschitz bounds on every exhaustion
  have hlip : ∀ k n, ∀ z w : ℂ, z ∈ K k → w ∈ K k →
      ‖f n z - f n w‖ ≤ (2 / (1 - r k)) * ‖z - w‖ := by
    intro k n z w hz hw
    have h := norm_sub_le_of_analyticOnNhd_closedBall (g := f n) (r := r k) (R := 1) (M := 1)
      (hr_lt k) zero_le_one (hf n) (hb n)
    simpa using h z w hz hw
  -- ## Equicontinuity of the family on each exhaustion
  have heqcont : ∀ k, Equicontinuous ((↑) : Set.range (Fn k) → K k → ℂ) := by
    intro k
    refine Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => (2 / (1 - r k)) * t) ?_ _ ?_
    · have : Tendsto (fun t : ℝ => (2 / (1 - r k)) * t) (𝓝 0) (𝓝 ((2 / (1 - r k)) * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      simpa using this
    · intro x y i
      obtain ⟨n, hn⟩ := i.2
      have hcoe : (i : K k → ℂ) = fun x : K k => f n (x : ℂ) := by
        rw [← hn]
        funext x
        exact hFn_apply k n x
      rw [hcoe]
      have h := hlip k n (x : ℂ) (y : ℂ) x.2 y.2
      simpa [Subtype.dist_eq, dist_eq_norm] using h
  -- ## Arzelà–Ascoli: the closure of the family on each exhaustion is compact
  have hcompact : ∀ k, IsCompact (closure (Set.range (Fn k))) := by
    intro k
    refine BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℂ) 1)
      (isCompact_closedBall 0 1) (Set.range (Fn k)) ?_ (heqcont k)
    intro g x hg
    obtain ⟨n, hn⟩ := hg
    have hx : (x : ℂ) ∈ Metric.ball 0 1 := hK_sub k x.2
    have h1 : ‖f n (x : ℂ)‖ ≤ 1 := hb n (x : ℂ) hx
    rw [← hn, hFn_apply k n x]
    simpa [Metric.mem_closedBall, dist_eq_norm] using h1
  -- ## Sequential extraction of a convergent subsequence on each exhaustion
  have exists_good : ∀ (k : ℕ) (u : ℕ → ℕ), ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ a : K k →ᵇ ℂ, Tendsto (fun n => Fn k (u (ψ n))) Filter.atTop (𝓝 a) := by
    intro k u
    have hmem : ∀ n, Fn k (u n) ∈ closure (Set.range (Fn k)) :=
      fun n => subset_closure (Set.mem_range_self (u n))
    obtain ⟨a, _, ψ, hψ, hψlim⟩ := (hcompact k).tendsto_subseq hmem
    exact ⟨ψ, hψ, a, by simpa [Function.comp_def] using hψlim⟩
  let psi : ℕ → (ℕ → ℕ) → (ℕ → ℕ) := fun k u => Classical.choose (exists_good k u)
  have psi_strict : ∀ (k : ℕ) (u : ℕ → ℕ), StrictMono (psi k u) := by
    intro k u
    exact (Classical.choose_spec (exists_good k u)).1
  have psi_conv : ∀ (k : ℕ) (u : ℕ → ℕ), ∃ a : K k →ᵇ ℂ,
      Tendsto (fun n => Fn k (u (psi k u n))) Filter.atTop (𝓝 a) := by
    intro k u
    exact (Classical.choose_spec (exists_good k u)).2
  -- ## The nested subsequences and their diagonal
  let phi : ℕ → (ℕ → ℕ) :=
    Nat.rec (motive := fun _ => ℕ → ℕ) id (fun k rec => rec ∘ psi (k + 1) rec)
  have phi_zero : phi 0 = id := rfl
  have phi_succ : ∀ k, phi (k + 1) = phi k ∘ psi (k + 1) (phi k) := by
    intro k
    rfl
  have phi_strict : ∀ k, StrictMono (phi k) := by
    intro k
    induction k with
    | zero => rw [phi_zero]; exact strictMono_id
    | succ k ih => rw [phi_succ k]; exact ih.comp (psi_strict (k + 1) (phi k))
  -- Every value of `phi n` already lies in the range of `phi m` for `m ≤ n`, at a large index.
  have phi_range : ∀ n m, m ≤ n → ∀ i, ∃ k ≥ i, phi n i = phi m k := by
    intro n
    induction n with
    | zero =>
        intro m hm i
        have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
        subst hm0
        exact ⟨i, le_refl i, rfl⟩
    | succ n ih =>
        intro m hm i
        rcases Nat.lt_or_ge m (n + 1) with hlt | hge
        · have hmle : m ≤ n := Nat.le_of_lt_succ hlt
          have happ : phi (n + 1) i = phi n (psi (n + 1) (phi n) i) := by
            rw [phi_succ n]; rfl
          obtain ⟨k, hk, hkeq⟩ := ih m hmle (psi (n + 1) (phi n) i)
          refine ⟨k, ?_, ?_⟩
          · have : i ≤ psi (n + 1) (phi n) i := (psi_strict (n + 1) (phi n)).id_le i
            omega
          · rw [happ, hkeq]
        · have hmn : m = n + 1 := le_antisymm hm hge
          subst hmn
          exact ⟨i, le_refl i, rfl⟩
  let diag : ℕ → ℕ := fun n => phi n n
  have diag_strict : StrictMono diag := by
    apply strictMono_nat_of_lt_succ
    intro n
    have hsucc : phi (n + 1) = phi n ∘ psi (n + 1) (phi n) := phi_succ n
    have hidle : n + 1 ≤ psi (n + 1) (phi n) (n + 1) := (psi_strict (n + 1) (phi n)).id_le (n + 1)
    have h1 : phi n (n + 1) ≤ phi n (psi (n + 1) (phi n) (n + 1)) :=
      (phi_strict n).monotone hidle
    have h2 : phi n n < phi n (n + 1) := (phi_strict n) (Nat.lt_succ_self n)
    have hdiag : diag (n + 1) = phi n (psi (n + 1) (phi n) (n + 1)) := by
      simp only [diag]
      rw [hsucc]; rfl
    rw [hdiag]
    exact lt_of_lt_of_le h2 h1
  -- ## The limit of the diagonal on each exhaustion
  let Alim : (j : ℕ) → K (j + 1) →ᵇ ℂ := fun j => Classical.choose (psi_conv (j + 1) (phi j))
  have Alim_spec : ∀ j, Tendsto (fun n => Fn (j + 1) (phi j (psi (j + 1) (phi j) n)))
      Filter.atTop (𝓝 (Alim j)) :=
    fun j => Classical.choose_spec (psi_conv (j + 1) (phi j))
  have Alim_spec' : ∀ j, Tendsto (fun n => Fn (j + 1) (phi (j + 1) n))
      Filter.atTop (𝓝 (Alim j)) := by
    intro j
    have h := Alim_spec j
    simpa [phi_succ j, Function.comp_apply] using h
  have diag_conv : ∀ j, Tendsto (fun n => Fn (j + 1) (diag n)) Filter.atTop (𝓝 (Alim j)) := by
    intro j
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (Alim_spec' j) ε hε
    refine ⟨max (j + 1) N, ?_⟩
    intro n hn
    have hn1 : j + 1 ≤ n := le_trans (le_max_left _ _) hn
    have hn2 : N ≤ n := le_trans (le_max_right _ _) hn
    obtain ⟨k, hk, hkeq⟩ := phi_range n (j + 1) hn1 n
    have heq : Fn (j + 1) (diag n) = Fn (j + 1) (phi (j + 1) k) := by
      simp only [diag, hkeq]
    rw [heq]
    exact hN k (le_trans hn2 hk)
  -- ## Uniform convergence on each exhaustion, towards a limit defined on the whole disc
  have hAunifsub : ∀ j, TendstoUniformly (fun n (x : K (j + 1)) => f (diag n) x)
      (fun x => (Alim j) x) Filter.atTop := by
    intro j
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have h := diag_conv j
    rw [Metric.tendsto_atTop] at h
    obtain ⟨N, hN⟩ := h ε hε
    filter_upwards [eventually_ge_atTop N] with n hn
    intro x
    have hdist := BoundedContinuousFunction.dist_coe_le_dist (f := Alim j)
      (g := Fn (j + 1) (diag n)) x
    calc dist ((Alim j) x) (f (diag n) x)
        = dist ((Alim j) x) ((Fn (j + 1) (diag n)) x) := by rw [hFn_apply]
      _ ≤ dist (Alim j) (Fn (j + 1) (diag n)) := hdist
      _ = dist (Fn (j + 1) (diag n)) (Alim j) := dist_comm _ _
      _ < ε := hN n hn
  let g : ℂ → ℂ := fun z =>
    if z ∈ Metric.ball 0 1 then Filter.limUnder Filter.atTop (fun n => f (diag n) z) else 0
  have hg_eq : ∀ (j : ℕ) (x : K (j + 1)), g x = (Alim j) x := by
    intro j x
    have hxball : (x : ℂ) ∈ Metric.ball 0 1 := hK_sub (j + 1) x.2
    have hpt : Tendsto (fun n => f (diag n) (x : ℂ)) Filter.atTop (𝓝 ((Alim j) x)) :=
      (hAunifsub j).tendsto_at x
    show g (x : ℂ) = (Alim j) x
    simp only [g]
    rw [if_pos hxball]
    exact Filter.Tendsto.limUnder_eq hpt
  have hgunifsub : ∀ j, TendstoUniformly (fun n (x : K (j + 1)) => f (diag n) x)
      (fun x : K (j + 1) => g x) Filter.atTop := by
    intro j
    rw [← tendstoUniformlyOn_univ]
    refine (tendstoUniformlyOn_univ.mpr (hAunifsub j)).congr_right fun x _ => (hg_eq j x).symm
  have hgunif : ∀ j, TendstoUniformlyOn (fun n => f (diag n)) g Filter.atTop (K (j + 1)) := by
    intro j
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    simpa [Function.comp_def] using hgunifsub j
  -- ## Local uniformity
  refine ⟨g, diag, diag_strict, ?_⟩
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds ?_
  intro x hx
  have hxnorm : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hx
  have hev : ∀ᶠ j in Filter.atTop, ‖x‖ < r (j + 1) := by
    have hrt : Tendsto (fun j : ℕ => r (j + 1)) Filter.atTop (𝓝 1) :=
      hr_tend.comp (tendsto_add_atTop_nat 1)
    exact hrt.eventually (isOpen_Ioi.mem_nhds hxnorm)
  obtain ⟨j, hj⟩ := Filter.eventually_atTop.mp hev
  have hj' : ‖x‖ < r (j + 1) := hj j le_rfl
  refine ⟨K (j + 1), ?_, hgunif j⟩
  apply nhdsWithin_le_nhds
  refine Filter.mem_of_superset (Metric.ball_mem_nhds x (sub_pos.mpr hj')) ?_
  intro y hy
  simp only [K, Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have hyx : ‖y - x‖ < r (j + 1) - ‖x‖ := by
    simpa [dist_eq_norm] using (Metric.mem_ball.mp hy)
  have hy' : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
    calc ‖y‖ = ‖x + (y - x)‖ := by ring_nf
      _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
  linarith

end Commons.Analysis.Complex.Montel