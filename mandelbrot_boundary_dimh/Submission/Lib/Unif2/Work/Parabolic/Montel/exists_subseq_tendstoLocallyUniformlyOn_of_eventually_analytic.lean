import Mathlib
import Submission.Lib.Unif2.Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_ball

noncomputable section
open Set Metric Filter Topology
open scoped Topology

namespace Work.Parabolic.Montel

/-! ### Auxiliary lemmas about `TendstoLocallyUniformlyOn` -/

/-- A locally uniform limit is preserved by composing the index map with a map tending to `atTop`. -/
private lemma tluo_comp_tendsto_atTop {α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {G : ℕ → α → β} {f : α → β} {s : Set α} {Θ : ℕ → ℕ}
    (h : TendstoLocallyUniformlyOn G f Filter.atTop s) (hΘ : Tendsto Θ Filter.atTop Filter.atTop) :
    TendstoLocallyUniformlyOn (fun n => G (Θ n)) f Filter.atTop s := by
  intro u hu x hx
  obtain ⟨t, ht, H⟩ := h u hu x hx
  exact ⟨t, ht, hΘ.eventually H⟩

/-- Shifting the index of a sequence by a constant does not affect locally uniform convergence
along `atTop`. -/
private lemma tluo_shift {α β : Type*} [TopologicalSpace α] [UniformSpace β] {G : ℕ → α → β}
    {f : α → β} {s : Set α} (c : ℕ) :
    TendstoLocallyUniformlyOn (fun n => G (n + c)) f Filter.atTop s ↔
      TendstoLocallyUniformlyOn G f Filter.atTop s := by
  constructor
  · intro h u hu x hx
    obtain ⟨t, ht, H⟩ := h u hu x hx
    rw [Filter.eventually_atTop] at H
    obtain ⟨N, hN⟩ := H
    refine ⟨t, ht, ?_⟩
    rw [Filter.eventually_atTop]
    refine ⟨N + c, fun m hm y hy => ?_⟩
    have hcm : c ≤ m := le_trans (Nat.le_add_left c N) hm
    have hsub : (m - c) + c = m := Nat.sub_add_cancel hcm
    have hN' : N ≤ m - c := by omega
    simpa [hsub] using hN (m - c) hN' y hy
  · intro h
    exact tluo_comp_tendsto_atTop h (Filter.tendsto_add_atTop_nat c)

/-- Multiplying a locally uniformly convergent family (and its limit) by a constant. -/
private lemma tluo_const_mul {α : Type*} [TopologicalSpace α] {ι : Type*} {p : Filter ι}
    {s : Set α} {F : ι → α → ℂ} {f : α → ℂ}
    (h : TendstoLocallyUniformlyOn F f p s) (c : ℂ) :
    TendstoLocallyUniformlyOn (fun n => fun x => c * F n x) (fun x => c * f x) p s := by
  intro u hu x hx
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_uniformity_dist.mp hu
  set δ : ℝ := ε / (‖c‖ + 1) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  obtain ⟨t, ht, H⟩ := h {q : ℂ × ℂ | dist q.1 q.2 < δ}
    (Metric.mem_uniformity_dist.mpr ⟨δ, hδpos, fun _ _ hab => hab⟩) x hx
  refine ⟨t, ht, H.mono fun n hn y hy => hsub ?_⟩
  have h1 : dist (f y) (F n y) < δ := hn y hy
  have h2 : dist (c * f y) (c * F n y) = ‖c‖ * dist (f y) (F n y) := by
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul]
  rw [h2]
  have h3 : ‖c‖ * δ ≤ ε := by
    have hle : ‖c‖ / (‖c‖ + 1) ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < ‖c‖ + 1)]
      linarith [norm_nonneg c]
    calc ‖c‖ * δ = ε * (‖c‖ / (‖c‖ + 1)) := by rw [hδ]; ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hle (le_of_lt hε)
      _ = ε := by ring
  rcases eq_or_lt_of_le (norm_nonneg c) with hc | hc
  · rw [← hc]; simpa using hε
  · exact lt_of_lt_of_le (mul_lt_mul_of_pos_left h1 hc) h3


theorem exists_subseq_tendstoLocallyUniformlyOn_of_eventually_analytic {X : Type*}
    [TopologicalSpace X] [ChartedSpace ℂ X] [LocallyCompactSpace X]
    [SecondCountableTopology X] {F : ℕ → X → ℂ}
    (hb : ∀ K : Set X, IsCompact K → ∃ B : ℝ, ∀ᶠ n in Filter.atTop, ∀ x ∈ K, ‖F n x‖ ≤ B)
    (hball : ∀ x : X, ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target ∧
      ∀ᶠ n in Filter.atTop, ∀ z ∈ Metric.ball ((chartAt ℂ x) x) ρ,
        AnalyticAt ℂ (F n ∘ (chartAt ℂ x).symm) z) :
    ∃ (φ : ℕ → ℕ) (g : X → ℂ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun n => F (φ n)) g Filter.atTop Set.univ ∧
      (∀ x : X, AnalyticAt ℂ (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) := by
  classical
  by_cases hne : Nonempty X
  · have hXne : Nonempty X := hne
    -- ## The chart balls supplied by `hball`, and their cut-down versions
    let ρ : X → ℝ := fun x => Classical.choose (hball x)
    have hρpos : ∀ x, 0 < ρ x := fun x => (Classical.choose_spec (hball x)).1
    have hρtgt : ∀ x, Metric.ball ((chartAt ℂ x) x) (ρ x) ⊆ (chartAt ℂ x).target :=
      fun x => (Classical.choose_spec (hball x)).2.1
    have hρana : ∀ x, ∀ᶠ n in Filter.atTop, ∀ z ∈ Metric.ball ((chartAt ℂ x) x) (ρ x),
        AnalyticAt ℂ (F n ∘ (chartAt ℂ x).symm) z :=
      fun x => (Classical.choose_spec (hball x)).2.2
    let Bx : X → Set X := fun x => (chartAt ℂ x).symm '' Metric.ball ((chartAt ℂ x) x) (ρ x / 2)
    have hBx_open : ∀ x, IsOpen (Bx x) := by
      intro x
      refine OpenPartialHomeomorph.isOpen_image_symm_of_subset_target _ isOpen_ball ?_
      exact (Metric.ball_subset_ball (by linarith [hρpos x])).trans (hρtgt x)
    have hBx_mem : ∀ x, x ∈ Bx x := by
      intro x
      refine ⟨(chartAt ℂ x) x, Metric.mem_ball_self (by linarith [hρpos x]), ?_⟩
      exact OpenPartialHomeomorph.left_inv _ (mem_chart_source ℂ x)
    -- ## A countable subcover
    obtain ⟨xs, hxs⟩ := IsLindelof.indexed_countable_subcover (isLindelof_univ (X := X)) Bx hBx_open
      (fun x _ => mem_iUnion.mpr ⟨x, hBx_mem x⟩)
    let c : ℕ → ℂ := fun k => (chartAt ℂ (xs k)) (xs k)
    let R : ℕ → ℝ := fun k => ρ (xs k) / 2
    let S : ℕ → Set X := fun k => (chartAt ℂ (xs k)).symm '' Metric.ball (c k) (R k)
    let C : ℕ → Set X := fun k => (chartAt ℂ (xs k)).symm '' Metric.closedBall (c k) (R k)
    have hS_eq : ∀ k, S k = Bx (xs k) := fun k => rfl
    have hS_open : ∀ k, IsOpen (S k) := fun k => hBx_open (xs k)
    have hRpos : ∀ k, 0 < R k := fun k => by simp only [R]; linarith [hρpos (xs k)]
    have hRlt : ∀ k, R k < ρ (xs k) := fun k => by simp only [R]; linarith [hρpos (xs k)]
    have hC_tgt : ∀ k, Metric.closedBall (c k) (R k) ⊆ (chartAt ℂ (xs k)).target := fun k =>
      (Metric.closedBall_subset_ball (hRlt k)).trans (hρtgt (xs k))
    have hC_compact : ∀ k, IsCompact (C k) := fun k => by
      have h := (isCompact_closedBall (c k) (R k)).image_of_continuousOn
        ((chartAt ℂ (xs k)).continuousOn_symm.mono (hC_tgt k))
      simpa only [C] using h
    have hcover : (⋃ k, S k) = univ := by
      have huniv : (univ : Set X) ⊆ ⋃ k, S k := by simpa only [S, c, R, Bx] using hxs
      exact eq_univ_of_univ_subset huniv
    -- ## Eventual bounds on the compact pieces
    have hbnd : ∀ k, ∃ B : ℝ, ∀ᶠ n in Filter.atTop, ∀ x ∈ C k, ‖F n x‖ ≤ B :=
      fun k => hb (C k) (hC_compact k)
    let Bk : ℕ → ℝ := fun k => Classical.choose (hbnd k)
    have hBk_spec : ∀ k, ∀ᶠ n in Filter.atTop, ∀ x ∈ C k, ‖F n x‖ ≤ Bk k :=
      fun k => Classical.choose_spec (hbnd k)
    let B' : ℕ → ℝ := fun k => max (Bk k) 1
    have hB'pos : ∀ k, 0 < B' k := fun k => lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hBk_le : ∀ k, Bk k ≤ B' k := fun k => le_max_left _ _
    -- ## Thresholds past which both hypotheses hold
    let Mana : ℕ → ℕ := fun k => Classical.choose (Filter.eventually_atTop.mp (hρana (xs k)))
    have hMana_spec : ∀ k, ∀ n, Mana k ≤ n → ∀ z ∈ Metric.ball (c k) (ρ (xs k)),
        AnalyticAt ℂ (F n ∘ (chartAt ℂ (xs k)).symm) z :=
      fun k => Classical.choose_spec (Filter.eventually_atTop.mp (hρana (xs k)))
    let Mbd : ℕ → ℕ := fun k => Classical.choose (Filter.eventually_atTop.mp (hBk_spec k))
    have hMbd_spec : ∀ k, ∀ n, Mbd k ≤ n → ∀ x ∈ C k, ‖F n x‖ ≤ Bk k :=
      fun k => Classical.choose_spec (Filter.eventually_atTop.mp (hBk_spec k))
    let N : ℕ → ℕ := fun k => max (Mana k) (Mbd k)
    have hN_ana : ∀ k n, N k ≤ n → ∀ z ∈ Metric.ball (c k) (ρ (xs k)),
        AnalyticAt ℂ (F n ∘ (chartAt ℂ (xs k)).symm) z :=
      fun k n hn => hMana_spec k n (le_trans (le_max_left _ _) hn)
    have hN_bd : ∀ k n, N k ≤ n → ∀ x ∈ C k, ‖F n x‖ ≤ Bk k :=
      fun k n hn => hMbd_spec k n (le_trans (le_max_right _ _) hn)
    -- ## One step of the diagonal extraction
    have hstep : ∀ (k : ℕ) (u : ℕ → ℕ), StrictMono u →
        ∃ (ψ : ℕ → ℕ) (G : ℂ → ℂ), StrictMono ψ ∧
          TendstoLocallyUniformlyOn
            (fun n => fun z : ℂ => F (u (N k + ψ n)) ((chartAt ℂ (xs k)).symm z) / B' k)
            G Filter.atTop (Metric.ball (c k) (R k)) := by
      intro k u hu
      have hf : ∀ n, ∀ z ∈ Metric.ball (c k) (R k),
          AnalyticAt ℂ (fun z : ℂ => F (u (N k + n)) ((chartAt ℂ (xs k)).symm z) / B' k) z := by
        intro n z hz
        have hge : N k ≤ u (N k + n) := le_trans (Nat.le_add_right _ _) (hu.id_le _)
        have hz' : z ∈ Metric.ball (c k) (ρ (xs k)) :=
          (Metric.ball_subset_ball (le_of_lt (hRlt k))) hz
        have h := hN_ana k (u (N k + n)) hge z hz'
        simpa [Function.comp_def] using h.div_const
      have hb' : ∀ n z, z ∈ Metric.ball (c k) (R k) →
          ‖(fun z : ℂ => F (u (N k + n)) ((chartAt ℂ (xs k)).symm z) / B' k) z‖ ≤ 1 := by
        intro n z hz
        have hge : N k ≤ u (N k + n) := le_trans (Nat.le_add_right _ _) (hu.id_le _)
        have hmem : (chartAt ℂ (xs k)).symm z ∈ C k := ⟨z, Metric.ball_subset_closedBall hz, rfl⟩
        have h1 : ‖F (u (N k + n)) ((chartAt ℂ (xs k)).symm z)‖ ≤ Bk k := hN_bd k _ hge _ hmem
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hB'pos k)]
        exact div_le_one_of_le₀ (le_trans h1 (hBk_le k)) (le_of_lt (hB'pos k))
      obtain ⟨ψ, G, hψ, hconv, -⟩ :=
        Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_ball
          (c := c k) (R := R k) (hRpos k) hf hb'
      exact ⟨ψ, G, hψ, hconv⟩
    -- ## The diagonal
    let psi : (k : ℕ) → (u : ℕ → ℕ) → StrictMono u → (ℕ → ℕ) :=
      fun k u hu => Classical.choose (hstep k u hu)
    let GOf : (k : ℕ) → (u : ℕ → ℕ) → StrictMono u → (ℂ → ℂ) :=
      fun k u hu => Classical.choose (Classical.choose_spec (hstep k u hu))
    have psi_strict : ∀ k u (hu : StrictMono u), StrictMono (psi k u hu) :=
      fun k u hu => (Classical.choose_spec (Classical.choose_spec (hstep k u hu))).1
    have GOf_spec : ∀ k u (hu : StrictMono u),
        TendstoLocallyUniformlyOn
          (fun n => fun z : ℂ => F (u (N k + psi k u hu n)) ((chartAt ℂ (xs k)).symm z) / B' k)
          (GOf k u hu) Filter.atTop (Metric.ball (c k) (R k)) :=
      fun k u hu => (Classical.choose_spec (Classical.choose_spec (hstep k u hu))).2
    let Phi : ℕ → {v : ℕ → ℕ // StrictMono v} :=
      Nat.rec (motive := fun _ => {v : ℕ → ℕ // StrictMono v}) ⟨id, strictMono_id⟩ fun k rec =>
        ⟨fun n => rec.1 (N k + psi k rec.1 rec.2 n),
         rec.2.comp fun a b hab => Nat.add_lt_add_left ((psi_strict k rec.1 rec.2) hab) (N k)⟩
    let U : ℕ → (ℕ → ℕ) := fun k => (Phi k).1
    have U_strict : ∀ k, StrictMono (U k) := fun k => (Phi k).2
    have U_succ : ∀ k, U (k + 1) = U k ∘ fun n => N k + psi k (U k) (U_strict k) n := fun k => rfl
    have range_succ : ∀ k, Set.range (U (k + 1)) ⊆ Set.range (U k) := by
      intro k
      rw [U_succ k]
      rintro y ⟨m, rfl⟩
      exact ⟨N k + psi k (U k) (U_strict k) m, rfl⟩
    have range_mono : ∀ k n, k ≤ n → Set.range (U n) ⊆ Set.range (U k) := by
      intro k n hkn
      induction hkn with
      | refl => exact subset_rfl
      | step h ih => exact (range_succ _).trans ih
    let diag : ℕ → ℕ := fun n => U n n
    have diag_mem : ∀ k n, k + 1 ≤ n → diag n ∈ Set.range (U (k + 1)) := by
      intro k n hn
      exact range_mono (k + 1) n hn ⟨n, rfl⟩
    have diag_strict : StrictMono diag := by
      apply strictMono_nat_of_lt_succ
      intro n
      have h1 : diag (n + 1) = U n (N n + psi n (U n) (U_strict n) (n + 1)) := by
        simp only [diag]
        rw [U_succ n]
        rfl
      rw [h1]
      apply (U_strict n)
      have hidle : n + 1 ≤ psi n (U n) (U_strict n) (n + 1) := (psi_strict n (U n) (U_strict n)).id_le (n + 1)
      omega
    -- ## Convergence of the diagonal on each of the covering chart balls
    have hconvS : ∀ k, TendstoLocallyUniformlyOn (fun n => F (U (k + 1) n))
        (fun x => GOf k (U k) (U_strict k) ((chartAt ℂ (xs k)) x) * B' k) Filter.atTop (S k) := by
      intro k
      have hcoord := GOf_spec k (U k) (U_strict k)
      have h1 : TendstoLocallyUniformlyOn
          (fun n => fun z : ℂ =>
            B' k * (F (U k (N k + psi k (U k) (U_strict k) n)) ((chartAt ℂ (xs k)).symm z) / B' k))
          (fun z : ℂ => B' k * GOf k (U k) (U_strict k) z) Filter.atTop (Metric.ball (c k) (R k)) :=
        tluo_const_mul hcoord (B' k)
      have h2 : TendstoLocallyUniformlyOn
          (fun n => fun z : ℂ => F (U (k + 1) n) ((chartAt ℂ (xs k)).symm z))
          (fun z : ℂ => GOf k (U k) (U_strict k) z * B' k) Filter.atTop (Metric.ball (c k) (R k)) := by
        refine (h1.congr fun n z hz => ?_).congr_right fun z hz => ?_
        · have hz : (B' k : ℂ) ≠ 0 := by
            exact_mod_cast ne_of_gt (hB'pos k)
          rw [mul_div_cancel₀ _ hz, U_succ k]
          rfl
        · ring
      have hS_sub : S k ⊆ (chartAt ℂ (xs k)).source := by
        rw [show S k = (chartAt ℂ (xs k)).source ∩
            (chartAt ℂ (xs k)) ⁻¹' Metric.ball (c k) (R k) from
          OpenPartialHomeomorph.symm_image_eq_source_inter_preimage (chartAt ℂ (xs k))
            ((Metric.ball_subset_ball (le_of_lt (hRlt k))).trans (hρtgt (xs k)))]
        exact inter_subset_left
      have hmap : MapsTo ((chartAt ℂ (xs k)) : X → ℂ) (S k) (Metric.ball (c k) (R k)) := by
        intro x hx
        obtain ⟨z, hz, rfl⟩ := hx
        rw [OpenPartialHomeomorph.right_inv _ (hC_tgt k (Metric.ball_subset_closedBall hz))]
        exact hz
      have hcont : ContinuousOn ((chartAt ℂ (xs k)) : X → ℂ) (S k) :=
        (OpenPartialHomeomorph.continuousOn _).mono hS_sub
      have h3 := h2.comp ((chartAt ℂ (xs k)) : X → ℂ) hmap hcont
      refine h3.congr fun n x hx => ?_
      simp only [Function.comp_apply]
      rw [OpenPartialHomeomorph.left_inv _ (hS_sub hx)]
    -- ## The diagonal is eventually a subsequence on each chart ball
    have ThetaSpec : ∀ k n, ∃ m, U (k + 1) m = diag (n + (k + 1)) :=
      fun k n => diag_mem k (n + (k + 1)) (Nat.le_add_left _ _)
    let Theta : ℕ → ℕ → ℕ := fun k n => Classical.choose (ThetaSpec k n)
    have Theta_eq : ∀ k n, U (k + 1) (Theta k n) = diag (n + (k + 1)) :=
      fun k n => Classical.choose_spec (ThetaSpec k n)
    have Theta_strict : ∀ k, StrictMono (Theta k) := by
      intro k
      apply strictMono_nat_of_lt_succ
      intro n
      have hlt : diag (n + (k + 1)) < diag (n + 1 + (k + 1)) :=
        diag_strict (Nat.add_lt_add_right (Nat.lt_succ_self n) (k + 1))
      rw [← Theta_eq k n, ← Theta_eq k (n + 1)] at hlt
      exact (U_strict (k + 1)).lt_iff_lt.mp hlt
    have Theta_tendsto : ∀ k, Tendsto (Theta k) Filter.atTop Filter.atTop := by
      intro k
      rw [Filter.tendsto_atTop_atTop]
      exact fun b => ⟨b, fun a ha => le_trans ha ((Theta_strict k).id_le a)⟩
    have hconvD : ∀ k, TendstoLocallyUniformlyOn (fun n => F (diag n))
        (fun x => GOf k (U k) (U_strict k) ((chartAt ℂ (xs k)) x) * B' k) Filter.atTop (S k) := by
      intro k
      have h4 := tluo_comp_tendsto_atTop (hconvS k) (Theta_tendsto k)
      have h5 : TendstoLocallyUniformlyOn (fun n => F (diag (n + (k + 1))))
          (fun x => GOf k (U k) (U_strict k) ((chartAt ℂ (xs k)) x) * B' k) Filter.atTop (S k) :=
        h4.congr fun n x hx => by rw [Theta_eq k n]
      exact (tluo_shift (G := fun n => F (diag n)) (k + 1)).mp h5
    -- ## The global limit
    let g : X → ℂ := fun x => Filter.limUnder Filter.atTop (fun n => F (diag n) x)
    have hg_eq : ∀ k, EqOn (fun x => GOf k (U k) (U_strict k) ((chartAt ℂ (xs k)) x) * B' k) g (S k) := by
      intro k x hx
      have htend : Tendsto (fun n => F (diag n) x) Filter.atTop
          (𝓝 (GOf k (U k) (U_strict k) ((chartAt ℂ (xs k)) x) * B' k)) := (hconvD k).tendsto_at hx
      show GOf k (U k) (U_strict k) ((chartAt ℂ (xs k)) x) * B' k = g x
      rw [show g x = Filter.limUnder Filter.atTop (fun n => F (diag n) x) from rfl]
      exact (Filter.Tendsto.limUnder_eq htend).symm
    have hconv_all : TendstoLocallyUniformlyOn (fun n => F (diag n)) g Filter.atTop (⋃ k, S k) :=
      tendstoLocallyUniformlyOn_iUnion hS_open fun k => (hconvD k).congr_right (hg_eq k)
    have hconv_univ : TendstoLocallyUniformlyOn (fun n => F (diag n)) g Filter.atTop univ := by
      rw [← hcover]; exact hconv_all
    refine ⟨diag, g, diag_strict, hconv_univ, ?_⟩
    -- ## Analyticity of the limit
    intro x
    have hcont : ContinuousOn ((chartAt ℂ x).symm : ℂ → X)
        (Metric.ball ((chartAt ℂ x) x) (ρ x)) :=
      (chartAt ℂ x).continuousOn_symm.mono (hρtgt x)
    have hLU : TendstoLocallyUniformlyOn (fun n => F (diag n) ∘ (chartAt ℂ x).symm)
        (g ∘ (chartAt ℂ x).symm) Filter.atTop (Metric.ball ((chartAt ℂ x) x) (ρ x)) :=
      hconv_univ.comp ((chartAt ℂ x).symm : ℂ → X) (mapsTo_univ _ _) hcont
    have hdiff : ∀ᶠ n in Filter.atTop, DifferentiableOn ℂ
        (fun z => F (diag n) ((chartAt ℂ x).symm z)) (Metric.ball ((chartAt ℂ x) x) (ρ x)) := by
      obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (hρana x)
      filter_upwards [Filter.eventually_ge_atTop N0] with n hn z hz
      have h := hN0 (diag n) (le_trans hn (diag_strict.id_le n)) z hz
      simpa [Function.comp_def] using h.differentiableAt.differentiableWithinAt
    have hd : DifferentiableOn ℂ (fun z => g ((chartAt ℂ x).symm z))
        (Metric.ball ((chartAt ℂ x) x) (ρ x)) :=
      hLU.differentiableOn hdiff Metric.isOpen_ball
    have hev : ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
        DifferentiableAt ℂ (fun z => g ((chartAt ℂ x).symm z)) z := by
      filter_upwards [Metric.ball_mem_nhds ((chartAt ℂ x) x) (hρpos x)] with z hz
      exact (hd z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    simpa [Function.comp_def] using Complex.analyticAt_iff_eventually_differentiableAt.mpr hev
  · -- empty case
    refine ⟨id, fun _ => 0, strictMono_id, ?_, ?_⟩
    · intro u hu x _
      exact (hne ⟨x⟩).elim
    · intro x
      exact (hne ⟨x⟩).elim
end Work.Parabolic.Montel
