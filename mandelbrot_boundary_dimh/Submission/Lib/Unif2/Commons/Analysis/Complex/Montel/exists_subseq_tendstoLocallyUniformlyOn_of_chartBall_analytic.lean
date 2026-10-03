import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Order.CompletePartialOrder
import Submission.Lib.Unif2.Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_ball

noncomputable section
open Set Metric Filter Topology
open scoped Topology

namespace Commons.Analysis.Complex.Montel

/-- Composition of a locally uniformly convergent sequence with a map `Θ : ℕ → ℕ` tending to
`atTop` (e.g. a strictly monotone subsequence). -/
private lemma tendstoLocallyUniformlyOn_comp_tendsto_atTop {α β : Type*} [TopologicalSpace α]
    [UniformSpace β] {G : ℕ → α → β} {f : α → β} {s : Set α} {Θ : ℕ → ℕ}
    (h : TendstoLocallyUniformlyOn G f Filter.atTop s)
    (hΘ : Tendsto Θ Filter.atTop Filter.atTop) :
    TendstoLocallyUniformlyOn (fun n => G (Θ n)) f Filter.atTop s := by
  intro u hu x hx
  obtain ⟨t, ht, H⟩ := h u hu x hx
  exact ⟨t, ht, hΘ.eventually H⟩

/-- Shifting the index of a sequence by a constant does not affect locally uniform convergence
along `atTop`. -/
private lemma tendstoLocallyUniformlyOn_shift {α β : Type*} [TopologicalSpace α]
    [UniformSpace β] {G : ℕ → α → β} {f : α → β} {s : Set α} (c : ℕ) :
    TendstoLocallyUniformlyOn (fun n => G (n + c)) f Filter.atTop s ↔
      TendstoLocallyUniformlyOn G f Filter.atTop s := by
  refine ⟨fun h => ?_, fun h => tendstoLocallyUniformlyOn_comp_tendsto_atTop h (tendsto_add_atTop_nat c)⟩
  intro u hu x hx
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

/-- **Diagonal extraction.**  Let `X` be a `ℂ`-charted space, locally compact and second countable,
and `F : ℕ → X → ℂ` a uniformly bounded family such that around every point `x` there is a chart ball
on which every member of the family is analytic (in the chart at `x`).  Then some strictly monotone
subsequence of `F` converges locally uniformly on all of `X`.

Proof sketch.  By Lindelöf (`LindelofSpace.elim_nhds_subcover`, using `LocallyCompactSpace` and
`SecondCountableTopology` to get `SigmaCompactSpace`/`LindelofSpace`) choose a countable family of
points `x k` such that the chart balls `W k := (chartAt ℂ (x k)).symm '' Metric.ball (chartAt ℂ (x k)
(x k)) (ρ (x k))` cover `X`; let `c k` be the centre and `e k := chartAt ℂ (x k)`.
For each `k`, the sequence `n ↦ F n ∘ (e k).symm` is analytic and bounded by `1` on
`Metric.ball (c k) (ρ (x k))`, so by
`Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_ball` there are `ψ k`
(strictly monotone) and `G k` analytic on that ball with
`TendstoLocallyUniformlyOn (fun n => F (ψ k n) ∘ (e k).symm) (G k) atTop (Metric.ball (c k) (ρ k))`.
Diagonalise: `phi 0 = id`, `phi (k+1) = phi k ∘ ψ k (phi k)`, `diag n = phi n n`; then `diag` is
strictly monotone and, for each `k`, the tail of `(diag n)` is a subsequence of `phi k`, hence
`(fun n => F (diag n) ∘ (e k).symm)` converges locally uniformly to `G k` on the ball, i.e.
`(fun n => F (diag n))` converges locally uniformly on `W k`.  Since the `W k` are open and cover `X`,
the pointwise limit `g` (defined by choosing `k` with `x ∈ W k`) is locally uniform and
`TendstoLocallyUniformlyOn (fun n => F (diag n)) g atTop univ` holds by the local definition of
`TendstoLocallyUniformlyOn`. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_of_chartBall_analytic {X : Type*}
    [TopologicalSpace X] [ChartedSpace ℂ X] [LocallyCompactSpace X] [SecondCountableTopology X]
    {F : ℕ → X → ℂ} (hb : ∀ n x, ‖F n x‖ ≤ 1)
    (hball : ∀ x : X, ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target ∧
      ∀ n, ∀ z ∈ Metric.ball ((chartAt ℂ x) x) ρ, AnalyticAt ℂ (F n ∘ (chartAt ℂ x).symm) z) :
    ∃ (φ : ℕ → ℕ) (g : X → ℂ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun n => F (φ n)) g Filter.atTop Set.univ := by
  classical
  by_cases hne : Nonempty X
  · have hne' : Nonempty X := hne
    -- ## The chart-ball neighbourhoods of the hypothesis
    have hρpos : ∀ x : X, 0 < Classical.choose (hball x) :=
      fun x => (Classical.choose_spec (hball x)).1
    have htgt : ∀ x : X, Metric.ball ((chartAt ℂ x) x) (Classical.choose (hball x)) ⊆
        (chartAt ℂ x).target := fun x => (Classical.choose_spec (hball x)).2.1
    have hana : ∀ x : X, ∀ n : ℕ, ∀ z ∈ Metric.ball ((chartAt ℂ x) x) (Classical.choose (hball x)),
        AnalyticAt ℂ (F n ∘ (chartAt ℂ x).symm) z :=
      fun x => (Classical.choose_spec (hball x)).2.2
    let Bx : X → Set X := fun x =>
      (chartAt ℂ x).symm '' Metric.ball ((chartAt ℂ x) x) (Classical.choose (hball x))
    have hBx_open : ∀ x : X, IsOpen (Bx x) := fun x =>
      OpenPartialHomeomorph.isOpen_image_symm_of_subset_target _ isOpen_ball (htgt x)
    have hBx_mem : ∀ x : X, x ∈ Bx x := by
      intro x
      refine ⟨(chartAt ℂ x) x, Metric.mem_ball_self (hρpos x), ?_⟩
      exact OpenPartialHomeomorph.left_inv _ (mem_chart_source ℂ x)
    -- ## A countable subcover by chart balls
    obtain ⟨xs, hxs⟩ :=
      IsLindelof.indexed_countable_subcover (isLindelof_univ (X := X)) Bx hBx_open
        (fun x _ => mem_iUnion.mpr ⟨x, hBx_mem x⟩)
    -- ## Chart data for the covering sequence
    let c : ℕ → ℂ := fun k => (chartAt ℂ (xs k)) (xs k)
    let rad : ℕ → ℝ := fun k => Classical.choose (hball (xs k))
    let W : ℕ → Set X := fun k => (chartAt ℂ (xs k)).symm '' Metric.ball (c k) (rad k)
    have hW_open : ∀ k, IsOpen (W k) := fun k => hBx_open (xs k)
    have hW_eq : ∀ k, W k = (chartAt ℂ (xs k)).source ∩ (chartAt ℂ (xs k)) ⁻¹' Metric.ball (c k) (rad k) :=
      fun k => OpenPartialHomeomorph.symm_image_eq_source_inter_preimage _ (htgt (xs k))
    have hW_sub : ∀ k, W k ⊆ (chartAt ℂ (xs k)).source := fun k => by
      rw [hW_eq k]; exact inter_subset_left
    have hW_cover : (⋃ k, W k) = univ := by
      refine eq_univ_of_univ_subset ?_
      have : ⋃ k, W k = ⋃ k, Bx (xs k) := rfl
      rw [this]
      exact hxs
    -- ## Montel on each chart ball
    have hex : ∀ (k : ℕ) (u : ℕ → ℕ), ∃ (ψ : ℕ → ℕ) (G : ℂ → ℂ), StrictMono ψ ∧
        TendstoLocallyUniformlyOn (fun m => F (u (ψ m)) ∘ (chartAt ℂ (xs k)).symm) G Filter.atTop
          (Metric.ball (c k) (rad k)) := by
      intro k u
      have hR : 0 < rad k := hρpos (xs k)
      have hf : ∀ n : ℕ, ∀ z ∈ Metric.ball (c k) (rad k),
          AnalyticAt ℂ (fun z => F (u n) ((chartAt ℂ (xs k)).symm z)) z := by
        intro n z hz
        have h := hana (xs k) (u n) z hz
        simpa [Function.comp_def] using h
      have hb' : ∀ n : ℕ, ∀ z, z ∈ Metric.ball (c k) (rad k) →
          ‖(fun z => F (u n) ((chartAt ℂ (xs k)).symm z)) z‖ ≤ 1 :=
        fun n z _ => hb (u n) _
      obtain ⟨ψ, G, hψ, hconv, -⟩ :=
        exists_subseq_tendstoLocallyUniformlyOn_ball (c := c k) hR hf hb'
      exact ⟨ψ, G, hψ, hconv⟩
    -- ## The diagonal recursion
    let psiOf : ℕ → (ℕ → ℕ) → (ℕ → ℕ) := fun k u => Classical.choose (hex k u)
    have psiOf_strict : ∀ k u, StrictMono (psiOf k u) :=
      fun k u => (Classical.choose_spec (Classical.choose_spec (hex k u))).1
    let GOf : ℕ → (ℕ → ℕ) → (ℂ → ℂ) :=
      fun k u => Classical.choose (Classical.choose_spec (hex k u))
    have GOf_spec : ∀ k u, TendstoLocallyUniformlyOn
        (fun m => F (u (psiOf k u m)) ∘ (chartAt ℂ (xs k)).symm) (GOf k u) Filter.atTop
          (Metric.ball (c k) (rad k)) :=
      fun k u => (Classical.choose_spec (Classical.choose_spec (hex k u))).2
    let U : ℕ → (ℕ → ℕ) := Nat.rec (motive := fun _ => ℕ → ℕ) id (fun k rec => rec ∘ psiOf k rec)
    have U_zero : U 0 = id := rfl
    have U_succ : ∀ k, U (k + 1) = U k ∘ psiOf k (U k) := fun k => rfl
    have U_strict : ∀ k, StrictMono (U k) := by
      intro k
      induction k with
      | zero => rw [U_zero]; exact strictMono_id
      | succ k ih => rw [U_succ k]; exact ih.comp (psiOf_strict k (U k))
    let diag : ℕ → ℕ := fun n => U n n
    have diag_strict : StrictMono diag := by
      apply strictMono_nat_of_lt_succ
      intro n
      have h1 : diag (n + 1) = U n (psiOf n (U n) (n + 1)) := by
        simp only [diag]
        rw [U_succ n]
        rfl
      have h2 : diag n = U n n := rfl
      rw [h1, h2]
      exact (U_strict n) (lt_of_lt_of_le (Nat.lt_succ_self n) ((psiOf_strict n (U n)).id_le (n + 1)))
    have range_succ : ∀ k, Set.range (U (k + 1)) ⊆ Set.range (U k) := by
      intro k
      rw [U_succ k]
      rintro y ⟨m, rfl⟩
      exact ⟨psiOf k (U k) m, rfl⟩
    have range_mono : ∀ k n, k ≤ n → Set.range (U n) ⊆ Set.range (U k) := by
      intro k n hkn
      induction hkn with
      | refl => exact subset_rfl
      | step h ih => exact (range_succ _).trans ih
    have diag_mem : ∀ k n, k + 1 ≤ n → diag n ∈ Set.range (U (k + 1)) := by
      intro k n hn
      exact range_mono (k + 1) n hn ⟨n, rfl⟩
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
        diag_strict (show n + (k + 1) < n + 1 + (k + 1) by omega)
      rw [← Theta_eq k n, ← Theta_eq k (n + 1)] at hlt
      exact (U_strict (k + 1)).lt_iff_lt.mp hlt
    have Theta_tendsto : ∀ k, Tendsto (Theta k) Filter.atTop Filter.atTop := by
      intro k
      rw [Filter.tendsto_atTop_atTop]
      exact fun b => ⟨b, fun a ha => le_trans ha ((Theta_strict k).id_le a)⟩
    -- ## Convergence in coordinates on each chart ball
    have hconv_ball : ∀ k, TendstoLocallyUniformlyOn
        (fun n => F (diag n) ∘ (chartAt ℂ (xs k)).symm) (GOf k (U k)) Filter.atTop
          (Metric.ball (c k) (rad k)) := by
      intro k
      have h2 : TendstoLocallyUniformlyOn
          (fun m => F (U (k + 1) m) ∘ (chartAt ℂ (xs k)).symm) (GOf k (U k)) Filter.atTop
            (Metric.ball (c k) (rad k)) := by
        have := GOf_spec k (U k)
        rw [U_succ k]
        simpa only [Function.comp_apply] using this
      have h3 := tendstoLocallyUniformlyOn_comp_tendsto_atTop h2 (Theta_tendsto k)
      have h4 : TendstoLocallyUniformlyOn
          (fun n => F (diag (n + (k + 1))) ∘ (chartAt ℂ (xs k)).symm) (GOf k (U k)) Filter.atTop
            (Metric.ball (c k) (rad k)) :=
        h3.congr fun n => fun z _ => by simp only [Theta_eq k n]
      exact (tendstoLocallyUniformlyOn_shift (k + 1)).mp h4
    -- ## Convergence on the chart-ball neighbourhoods `W k`
    have hconv_W : ∀ k, TendstoLocallyUniformlyOn (fun n => F (diag n))
        (fun x => GOf k (U k) ((chartAt ℂ (xs k)) x)) Filter.atTop (W k) := by
      intro k
      have hmap : MapsTo (↑(chartAt ℂ (xs k)) : X → ℂ) (W k) (Metric.ball (c k) (rad k)) := by
        intro x hx
        obtain ⟨z, hz, rfl⟩ := hx
        rw [OpenPartialHomeomorph.right_inv _ (htgt (xs k) hz)]
        exact hz
      have hcont : ContinuousOn (↑(chartAt ℂ (xs k)) : X → ℂ) (W k) :=
        (OpenPartialHomeomorph.continuousOn _).mono (hW_sub k)
      have h1 := (hconv_ball k).comp (↑(chartAt ℂ (xs k)) : X → ℂ) hmap hcont
      refine h1.congr fun n => fun x hx => ?_
      simp only [Function.comp_apply]
      rw [OpenPartialHomeomorph.left_inv _ (hW_sub k hx)]
    -- ## The limit function and local uniformity
    let g : X → ℂ := fun x => Filter.limUnder Filter.atTop (fun n => F (diag n) x)
    have hg_eq : ∀ k, EqOn (fun x => GOf k (U k) ((chartAt ℂ (xs k)) x)) g (W k) := by
      intro k x hx
      have htend : Tendsto (fun n => F (diag n) x) Filter.atTop
          (𝓝 (GOf k (U k) ((chartAt ℂ (xs k)) x))) := (hconv_W k).tendsto_at hx
      show GOf k (U k) ((chartAt ℂ (xs k)) x) = g x
      rw [show g x = Filter.limUnder Filter.atTop (fun n => F (diag n) x) from rfl]
      exact (Filter.Tendsto.limUnder_eq htend).symm
    have hconv_all : TendstoLocallyUniformlyOn (fun n => F (diag n)) g Filter.atTop (⋃ k, W k) :=
      tendstoLocallyUniformlyOn_iUnion hW_open fun k => (hconv_W k).congr_right (hg_eq k)
    rw [hW_cover] at hconv_all
    exact ⟨diag, g, diag_strict, hconv_all⟩
  · have hem : IsEmpty X := not_nonempty_iff.mp hne
    exact ⟨id, fun _ => 0, strictMono_id, fun u hu x hx => isEmptyElim x⟩

end Commons.Analysis.Complex.Montel