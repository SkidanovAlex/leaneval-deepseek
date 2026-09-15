import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_ball

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

/-- **Montel's theorem on a charted open set.**  Let `X` be a locally compact, second countable
space charted over `ℂ` and let `U ⊆ X` be open.  If for every `x ∈ U` there is a ball in the chart at
`x` which is contained in `U`, on which every member of the family `F : ℕ → X → ℂ` is analytic and
uniformly bounded (with a bound depending on `x`), then some strictly monotone subsequence of `F`
converges locally uniformly on `U`.

Proof: the chart balls supplied by the hypothesis form an open cover of `U`; since `U` is Lindelöf
(second countability of `X`), pass to a countable subcover `W k`.  On each `W k` the family is
analytic and bounded in coordinates, so by scaling and
`Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_ball` we can extract a
subsequence converging locally uniformly on `W k`; diagonalising over `k` finishes the proof, since
local uniform convergence is a local property. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_of_chartBall_bounded {X : Type*}
    [TopologicalSpace X] [ChartedSpace ℂ X] [LocallyCompactSpace X] [SecondCountableTopology X]
    {U : Set X} (hU : IsOpen U) {F : ℕ → X → ℂ}
    (hball : ∀ x ∈ U, ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target ∧
      (chartAt ℂ x).symm '' Metric.ball ((chartAt ℂ x) x) ρ ⊆ U ∧
      (∀ n, ∀ z ∈ Metric.ball ((chartAt ℂ x) x) ρ, AnalyticAt ℂ (F n ∘ (chartAt ℂ x).symm) z) ∧
      (∃ C : ℝ, ∀ n, ∀ z ∈ Metric.ball ((chartAt ℂ x) x) ρ, ‖F n ((chartAt ℂ x).symm z)‖ ≤ C)) :
    ∃ (φ : ℕ → ℕ) (g : X → ℂ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun n => F (φ n)) g Filter.atTop U := by
  classical
  by_cases hUe : (U : Set X).Nonempty
  · haveI : Nonempty U := hUe.to_subtype
    -- ## The chart-ball data attached to each point of `U`
    let ρ : U → ℝ := fun i => Classical.choose (hball i.1 i.2)
    have hρpos : ∀ i, 0 < ρ i := fun i => (Classical.choose_spec (hball i.1 i.2)).1
    have htgt : ∀ i, Metric.ball ((chartAt ℂ i.1) i.1) (ρ i) ⊆ (chartAt ℂ i.1).target :=
      fun i => (Classical.choose_spec (hball i.1 i.2)).2.1
    have hana : ∀ i n, ∀ z ∈ Metric.ball ((chartAt ℂ i.1) i.1) (ρ i),
        AnalyticAt ℂ (F n ∘ (chartAt ℂ i.1).symm) z :=
      fun i => (Classical.choose_spec (hball i.1 i.2)).2.2.2.1
    have hbnd : ∀ i, ∃ C : ℝ, ∀ n, ∀ z ∈ Metric.ball ((chartAt ℂ i.1) i.1) (ρ i),
        ‖F n ((chartAt ℂ i.1).symm z)‖ ≤ C :=
      fun i => (Classical.choose_spec (hball i.1 i.2)).2.2.2.2
    let W : U → Set X := fun i => (chartAt ℂ i.1).symm '' Metric.ball ((chartAt ℂ i.1) i.1) (ρ i)
    have hWsub : ∀ i, W i ⊆ U :=
      fun i => (Classical.choose_spec (hball i.1 i.2)).2.2.1
    have hW_open : ∀ i, IsOpen (W i) := fun i =>
      OpenPartialHomeomorph.isOpen_image_symm_of_subset_target _ isOpen_ball (htgt i)
    have hW_mem : ∀ i, i.1 ∈ W i := by
      intro i
      refine ⟨(chartAt ℂ i.1) i.1, Metric.mem_ball_self (hρpos i), ?_⟩
      exact OpenPartialHomeomorph.left_inv _ (mem_chart_source ℂ i.1)
    -- ## A countable subcover of `U` by chart balls
    obtain ⟨ks, hks⟩ :=
      IsLindelof.indexed_countable_subcover (HereditarilyLindelofSpace.isLindelof U)
        W hW_open (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hW_mem ⟨x, hx⟩⟩)
    let c : ℕ → ℂ := fun k => (chartAt ℂ (ks k).1) (ks k).1
    let rad : ℕ → ℝ := fun k => ρ (ks k)
    have hW_cover : (⋃ k, W (ks k)) = U :=
      le_antisymm (iUnion_subset fun k => hWsub (ks k)) hks
    have hW_eq : ∀ k, W (ks k) =
        (chartAt ℂ (ks k).1).source ∩ (chartAt ℂ (ks k).1) ⁻¹' Metric.ball (c k) (rad k) :=
      fun k => OpenPartialHomeomorph.symm_image_eq_source_inter_preimage _ (htgt (ks k))
    have hW_sub : ∀ k, W (ks k) ⊆ (chartAt ℂ (ks k).1).source := fun k => by
      rw [hW_eq k]; exact inter_subset_left
    -- ## Montel on each chart ball of the cover
    have hex : ∀ (k : ℕ) (u : ℕ → ℕ), ∃ (ψ : ℕ → ℕ) (G : ℂ → ℂ), StrictMono ψ ∧
        TendstoLocallyUniformlyOn (fun m => F (u (ψ m)) ∘ (chartAt ℂ (ks k).1).symm) G Filter.atTop
          (Metric.ball (c k) (rad k)) := by
      intro k u
      have hR : 0 < rad k := hρpos (ks k)
      obtain ⟨C, hC⟩ := hbnd (ks k)
      let M : ℝ := |C| + 1
      have hMpos : 0 < M := by
        have : 0 ≤ |C| := abs_nonneg C
        simp only [M]; linarith
      have hMne : (M : ℂ) ≠ 0 := by
        have : M ≠ 0 := ne_of_gt hMpos
        exact_mod_cast this
      have hAn : ∀ n : ℕ, ∀ z ∈ Metric.ball (c k) (rad k),
          AnalyticAt ℂ (fun w => F (u n) ((chartAt ℂ (ks k).1).symm w) / (M : ℂ)) z := by
        intro n z hz
        have h := hana (ks k) (u n) z hz
        have h2 := AnalyticAt.div_const h (c := (M : ℂ))
        simpa [Function.comp_def] using h2
      have hBd : ∀ n : ℕ, ∀ z, z ∈ Metric.ball (c k) (rad k) →
          ‖F (u n) ((chartAt ℂ (ks k).1).symm z) / (M : ℂ)‖ ≤ 1 := by
        intro n z hz
        have h1 : ‖F (u n) ((chartAt ℂ (ks k).1).symm z)‖ ≤ C := hC (u n) z hz
        have h2 : ‖(M : ℂ)‖ = M := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMpos]
        have h3 : ‖F (u n) ((chartAt ℂ (ks k).1).symm z)‖ ≤ M := by
          calc ‖F (u n) ((chartAt ℂ (ks k).1).symm z)‖ ≤ C := h1
            _ ≤ |C| := le_abs_self C
            _ ≤ M := by simp only [M]; linarith
        rw [norm_div, h2, div_le_iff₀ hMpos]
        simpa using h3
      obtain ⟨ψ, G, hψ, hconv, -⟩ :=
        exists_subseq_tendstoLocallyUniformlyOn_ball (c := c k) (R := rad k) hR hAn hBd
      refine ⟨ψ, fun w => (M : ℂ) * G w, hψ, ?_⟩
      have hunif : UniformContinuous (fun z : ℂ => (M : ℂ) * z) := uniformContinuous_mul_left' _
      have h1 := hunif.comp_tendstoLocallyUniformlyOn hconv
      refine h1.congr fun n w _ => ?_
      simp only [Function.comp_apply]
      rw [mul_div_cancel₀ _ hMne]
    -- ## The diagonal recursion
    let psiOf : ℕ → (ℕ → ℕ) → (ℕ → ℕ) := fun k u => Classical.choose (hex k u)
    have psiOf_strict : ∀ k u, StrictMono (psiOf k u) :=
      fun k u => (Classical.choose_spec (Classical.choose_spec (hex k u))).1
    let GOf : ℕ → (ℕ → ℕ) → (ℂ → ℂ) :=
      fun k u => Classical.choose (Classical.choose_spec (hex k u))
    have GOf_spec : ∀ k u, TendstoLocallyUniformlyOn
        (fun m => F (u (psiOf k u m)) ∘ (chartAt ℂ (ks k).1).symm) (GOf k u) Filter.atTop
          (Metric.ball (c k) (rad k)) :=
      fun k u => (Classical.choose_spec (Classical.choose_spec (hex k u))).2
    let U' : ℕ → (ℕ → ℕ) := Nat.rec (motive := fun _ => ℕ → ℕ) id (fun k rec => rec ∘ psiOf k rec)
    have U'_zero : U' 0 = id := rfl
    have U'_succ : ∀ k, U' (k + 1) = U' k ∘ psiOf k (U' k) := fun k => rfl
    have U'_strict : ∀ k, StrictMono (U' k) := by
      intro k
      induction k with
      | zero => rw [U'_zero]; exact strictMono_id
      | succ k ih => rw [U'_succ k]; exact ih.comp (psiOf_strict k (U' k))
    let diag : ℕ → ℕ := fun n => U' n n
    have diag_strict : StrictMono diag := by
      apply strictMono_nat_of_lt_succ
      intro n
      have h1 : diag (n + 1) = U' n (psiOf n (U' n) (n + 1)) := by
        simp only [diag]
        rw [U'_succ n]
        rfl
      have h2 : diag n = U' n n := rfl
      rw [h1, h2]
      exact (U'_strict n)
        (lt_of_lt_of_le (Nat.lt_succ_self n) ((psiOf_strict n (U' n)).id_le (n + 1)))
    have range_succ : ∀ k, Set.range (U' (k + 1)) ⊆ Set.range (U' k) := by
      intro k
      rw [U'_succ k]
      rintro y ⟨m, rfl⟩
      exact ⟨psiOf k (U' k) m, rfl⟩
    have range_mono : ∀ k n, k ≤ n → Set.range (U' n) ⊆ Set.range (U' k) := by
      intro k n hkn
      induction hkn with
      | refl => exact subset_rfl
      | step h ih => exact (range_succ _).trans ih
    have diag_mem : ∀ k n, k + 1 ≤ n → diag n ∈ Set.range (U' (k + 1)) := by
      intro k n hn
      exact range_mono (k + 1) n hn ⟨n, rfl⟩
    have ThetaSpec : ∀ k n, ∃ m, U' (k + 1) m = diag (n + (k + 1)) :=
      fun k n => diag_mem k (n + (k + 1)) (Nat.le_add_left _ _)
    let Theta : ℕ → ℕ → ℕ := fun k n => Classical.choose (ThetaSpec k n)
    have Theta_eq : ∀ k n, U' (k + 1) (Theta k n) = diag (n + (k + 1)) :=
      fun k n => Classical.choose_spec (ThetaSpec k n)
    have Theta_strict : ∀ k, StrictMono (Theta k) := by
      intro k
      apply strictMono_nat_of_lt_succ
      intro n
      have hlt : diag (n + (k + 1)) < diag (n + 1 + (k + 1)) :=
        diag_strict (show n + (k + 1) < n + 1 + (k + 1) by omega)
      rw [← Theta_eq k n, ← Theta_eq k (n + 1)] at hlt
      exact (U'_strict (k + 1)).lt_iff_lt.mp hlt
    have Theta_tendsto : ∀ k, Tendsto (Theta k) Filter.atTop Filter.atTop := by
      intro k
      rw [Filter.tendsto_atTop_atTop]
      exact fun b => ⟨b, fun a ha => le_trans ha ((Theta_strict k).id_le a)⟩
    -- ## Convergence in coordinates on each chart ball
    have hconv_ball : ∀ k, TendstoLocallyUniformlyOn
        (fun n => F (diag n) ∘ (chartAt ℂ (ks k).1).symm) (GOf k (U' k)) Filter.atTop
          (Metric.ball (c k) (rad k)) := by
      intro k
      have h2 : TendstoLocallyUniformlyOn
          (fun m => F (U' (k + 1) m) ∘ (chartAt ℂ (ks k).1).symm) (GOf k (U' k)) Filter.atTop
            (Metric.ball (c k) (rad k)) := by
        have := GOf_spec k (U' k)
        rw [U'_succ k]
        simpa only [Function.comp_apply] using this
      have h3 := tendstoLocallyUniformlyOn_comp_tendsto_atTop h2 (Theta_tendsto k)
      have h4 : TendstoLocallyUniformlyOn
          (fun n => F (diag (n + (k + 1))) ∘ (chartAt ℂ (ks k).1).symm) (GOf k (U' k))
            Filter.atTop (Metric.ball (c k) (rad k)) :=
        h3.congr fun n => fun z _ => by simp only [Theta_eq k n]
      exact (tendstoLocallyUniformlyOn_shift (k + 1)).mp h4
    -- ## Convergence on the chart-ball neighbourhoods
    have hconv_W : ∀ k, TendstoLocallyUniformlyOn (fun n => F (diag n))
        (fun x => GOf k (U' k) ((chartAt ℂ (ks k).1) x)) Filter.atTop (W (ks k)) := by
      intro k
      have hmap : MapsTo (↑(chartAt ℂ (ks k).1) : X → ℂ) (W (ks k)) (Metric.ball (c k) (rad k)) := by
        intro x hx
        obtain ⟨z, hz, rfl⟩ := hx
        rw [OpenPartialHomeomorph.right_inv _ (htgt (ks k) hz)]
        exact hz
      have hcont : ContinuousOn (↑(chartAt ℂ (ks k).1) : X → ℂ) (W (ks k)) :=
        (OpenPartialHomeomorph.continuousOn _).mono (hW_sub k)
      have h1 := (hconv_ball k).comp (↑(chartAt ℂ (ks k).1) : X → ℂ) hmap hcont
      refine h1.congr fun n => fun x hx => ?_
      simp only [Function.comp_apply]
      rw [OpenPartialHomeomorph.left_inv _ (hW_sub k hx)]
    -- ## The limit function and local uniformity
    let g : X → ℂ := fun x => Filter.limUnder Filter.atTop (fun n => F (diag n) x)
    have hg_eq : ∀ k, EqOn (fun x => GOf k (U' k) ((chartAt ℂ (ks k).1) x)) g (W (ks k)) := by
      intro k x hx
      have htend : Tendsto (fun n => F (diag n) x) Filter.atTop
          (𝓝 (GOf k (U' k) ((chartAt ℂ (ks k).1) x))) := (hconv_W k).tendsto_at hx
      show GOf k (U' k) ((chartAt ℂ (ks k).1) x) = g x
      rw [show g x = Filter.limUnder Filter.atTop (fun n => F (diag n) x) from rfl]
      exact (Filter.Tendsto.limUnder_eq htend).symm
    have hconv_all : TendstoLocallyUniformlyOn (fun n => F (diag n)) g Filter.atTop
        (⋃ k, W (ks k)) :=
      tendstoLocallyUniformlyOn_iUnion (fun k => hW_open (ks k)) fun k =>
        (hconv_W k).congr_right (hg_eq k)
    rw [hW_cover] at hconv_all
    exact ⟨diag, g, diag_strict, hconv_all⟩
  · have hUe' : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hUe
    refine ⟨id, fun _ => 0, strictMono_id, ?_⟩
    rw [hUe']
    intro u hu x hx
    exact absurd hx (by simp)

end Commons.Analysis.Complex.Montel