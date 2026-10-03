import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.Normal.hurwitz_nonvanishing

/-!
# Injectivity of the limit of a sequence of Fatou coordinates

This file proves `Work.FatouCH.Cont.InjOfTendsto`, the soft analysis input of Shishikura
Prop. A.2.1(iii) (continuity of Fatou coordinates, `MandelDim.FatouContinuity`): a locally uniform
limit of *injective* Fatou coordinates is injective, provided the limit is not constant.

The mathematical content is Hurwitz's theorem in its injective-or-constant form, plus the two
elementary facts that the region `Qreg c₁ c₂` is a domain (open, preconnected) and that every point
of it is surrounded by a compactly contained ball (supplied here under the name `hpair`, in the
form in which the applications produce it).

Main steps:

* `TendstoLocallyUniformlyOn.add_atTop`: reindexing a locally uniform limit along `n ↦ n + N`;
* `hurwitz_injOn_or_const`: Hurwitz's theorem for an open preconnected `U ⊆ ℂ`, with the
  differentiability and injectivity hypotheses assumed only eventually in `n`;
* `injOn_of_forall`: the `∀ n` form of the same, proved from `Work.Normal.hurwitz_nonvanishing`;
* `InjOfTendsto`: the assembly.
-/

namespace Work.FatouCH.Cont

open Set Filter Metric
open scoped Topology

/-- Reindexing a locally uniform limit along `n ↦ n + N`. -/
theorem TendstoLocallyUniformlyOn.add_atTop {α : Type*} [TopologicalSpace α] {F : ℕ → α → ℂ}
    {g : α → ℂ} {s : Set α} {N : ℕ} (h : TendstoLocallyUniformlyOn F g atTop s) :
    TendstoLocallyUniformlyOn (fun n => F (n + N)) g atTop s := by
  intro u hu x hx
  obtain ⟨t, ht, htf⟩ := h u hu x hx
  exact ⟨t, ht, (tendsto_add_atTop_nat N).eventually htf⟩

/-- If `F n → g` locally uniformly on an open set `Q`, and every point of `Q` has a closed ball
around it inside `Q` on which all large `n` have `F n` holomorphic, then `g` is holomorphic on
`Q` (holomorphy is a local property of the limit). -/
private theorem differentiableOn_of_local {Q : Set ℂ} {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn F g atTop Q)
    (hloc : ∀ z ∈ Q, ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ Q ∧
      ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) (ball z r)) :
    DifferentiableOn ℂ g Q := by
  intro z hz
  obtain ⟨r, hr0, hsub, hev⟩ := hloc z hz
  have hball : ball z r ⊆ Q := fun w hw => hsub (ball_subset_closedBall hw)
  have hd : DifferentiableOn ℂ g (ball z r) :=
    (hconv.mono hball).differentiableOn hev isOpen_ball
  exact (hd.differentiableAt (ball_mem_nhds z hr0)).differentiableWithinAt

/-- **Hurwitz's injectivity theorem, `∀ n` form.**  If `f n` is holomorphic and injective on an
open preconnected `U`, `g` is holomorphic on `U`, `f n → g` locally uniformly on `U`, and `g` is
not constant on `U`, then `g` is injective on `U`.

The proof is the classical one: if `g z₁ = g z₂` with `z₁ ≠ z₂`, then on a ball `B ∋ z₂` avoiding
`z₁` the holomorphic functions `z ↦ f n z - f n z₁` are zero-free and converge to
`z ↦ g z - g z₁`, so by `Work.Normal.hurwitz_nonvanishing` that limit vanishes identically on `B`;
analytic continuation on the preconnected open `U` makes `g` constant, contradiction. -/
private theorem injOn_of_forall {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (hg : DifferentiableOn ℂ g U) (hconv : TendstoLocallyUniformlyOn f g atTop U)
    (hinj : ∀ n, Set.InjOn (f n) U)
    (hnc : ¬ ∃ c : ℂ, ∀ z ∈ U, g z = c) : Set.InjOn g U := by
  intro z₁ hz₁ z₂ hz₂ heq
  by_contra hne
  obtain ⟨ρ, hρ0, hρU⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ball z₂ ρ ⊆ U := by
    obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz₂)
    exact ⟨ρ, hρ, hsub⟩
  have hdpos : 0 < dist z₁ z₂ := by rw [dist_pos]; exact hne
  set r : ℝ := min ρ (dist z₁ z₂ / 2) with hrdef
  have hr0 : 0 < r := lt_min hρ0 (by positivity)
  have hrU : ball z₂ r ⊆ U := fun z hz => hρU (ball_subset_ball (min_le_left ρ _) hz)
  have hz₁out : z₁ ∉ ball z₂ r := by
    intro hz
    rw [mem_ball] at hz
    have hlt : dist z₁ z₂ < dist z₁ z₂ / 2 := lt_of_lt_of_le hz (min_le_right ρ _)
    linarith
  have hvn : ∀ n, ∀ z ∈ ball z₂ r, f n z - f n z₁ ≠ 0 := by
    intro n z hz hz0
    have hzU : z ∈ U := hrU hz
    have he : f n z = f n z₁ := sub_eq_zero.mp hz0
    have hzz₁ : z = z₁ := hinj n hzU hz₁ he
    exact hz₁out (hzz₁ ▸ hz)
  have hdiff : ∀ n, DifferentiableOn ℂ (fun z => f n z - f n z₁) (ball z₂ r) := fun n =>
    ((hf n).mono hrU).sub (differentiableOn_const (f n z₁))
  have hconv' : TendstoLocallyUniformlyOn (fun n z => f n z - f n z₁)
      (fun z => g z - g z₁) atTop (ball z₂ r) := by
    have hA : TendstoLocallyUniformlyOn f g atTop (ball z₂ r) := hconv.mono hrU
    have hB : TendstoLocallyUniformlyOn (fun n (_ : ℂ) => f n z₁) (fun _ => g z₁) atTop
        (ball z₂ r) :=
      ((hconv.tendsto_at hz₁).tendstoUniformlyOn_const (ball z₂ r)).tendstoLocallyUniformlyOn
    exact hA.sub hB
  rcases Work.Normal.hurwitz_nonvanishing isOpen_ball (convex_ball z₂ r).isPreconnected
      (fun n z => f n z - f n z₁) (fun z => g z - g z₁) hdiff hvn hconv' with h1 | h2
  · exact h1 z₂ (mem_ball_self hr0) (by simp [heq])
  · refine hnc ⟨g z₁, fun z hz => ?_⟩
    have hev : g =ᶠ[𝓝 z₂] (fun _ => g z₁) := by
      filter_upwards [ball_mem_nhds z₂ hr0] with w hw
      exact sub_eq_zero.mp (h2 w hw)
    exact ((hg.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const hUc hz₂ hev) hz

/-- **Hurwitz's injectivity theorem, eventual form.**  Let `U ⊆ ℂ` be open and preconnected, let
`f n` be holomorphic on `U` and injective on `U` for all large `n`, let `g` be holomorphic on `U`
and let `f n → g` locally uniformly on `U`.  Then `g` is injective on `U`, or `g` is constant
on `U`. -/
theorem hurwitz_injOn_or_const {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hf : ∀ᶠ n in atTop, DifferentiableOn ℂ (f n) U)
    (hg : DifferentiableOn ℂ g U)
    (hconv : TendstoLocallyUniformlyOn f g atTop U)
    (hinj : ∀ᶠ n in atTop, Set.InjOn (f n) U) :
    Set.InjOn g U ∨ ∃ c : ℂ, ∀ z ∈ U, g z = c := by
  by_cases hconst : ∃ c : ℂ, ∀ z ∈ U, g z = c
  · exact Or.inr hconst
  · left
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hf
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp hinj
    have hFd : ∀ n, DifferentiableOn ℂ (fun z => f (n + max N₁ N₂) z) U := fun n =>
      hN₁ _ (le_trans (le_max_left N₁ N₂) (Nat.le_add_left (max N₁ N₂) n))
    have hFi : ∀ n, Set.InjOn (fun z => f (n + max N₁ N₂) z) U := fun n =>
      hN₂ _ (le_trans (le_max_right N₁ N₂) (Nat.le_add_left (max N₁ N₂) n))
    have hFc : TendstoLocallyUniformlyOn (fun n => f (n + max N₁ N₂)) g atTop U :=
      TendstoLocallyUniformlyOn.add_atTop hconv
    exact injOn_of_forall hU hUc hFd hg hFc hFi hconst

/-- **Injectivity of the limit of Fatou coordinates** (Shishikura A.2.1(iii), continuous
dependence).  If `Φ n` is a Fatou coordinate of `F n` on the (moving) region
`Qreg (b₁ n) (b₂ n)`, every compact subset of `Qreg c₁ c₂` is eventually contained in the moving
regions, `Φ n → Ψ` locally uniformly on `Qreg c₁ c₂`, and `Ψ` is not constant on `Qreg c₁ c₂`,
then `Ψ` is injective on `Qreg c₁ c₂`. -/
theorem InjOfTendsto {b₁ b₂ : ℕ → Option ℂ} {c₁ c₂ : Option ℂ} {F : ℕ → ℂ → ℂ}
    {Φ : ℕ → ℂ → ℂ} {Ψ : ℂ → ℂ} (hOpen : IsOpen (MandelDim.Qreg c₁ c₂))
    (hPre : IsPreconnected (MandelDim.Qreg c₁ c₂))
    (hΦ : ∀ n, MandelDim.IsFatouCoordOn (F n) (Φ n) (MandelDim.Qreg (b₁ n) (b₂ n)))
    (hdom : ∀ K ⊆ MandelDim.Qreg c₁ c₂, IsCompact K →
      ∀ᶠ n in atTop, K ⊆ MandelDim.Qreg (b₁ n) (b₂ n))
    (hΨ : TendstoLocallyUniformlyOn Φ Ψ atTop (MandelDim.Qreg c₁ c₂))
    (hpair : ∀ x y : ℂ, x ∈ MandelDim.Qreg c₁ c₂ → y ∈ MandelDim.Qreg c₁ c₂ →
      ∃ U : Set ℂ, IsOpen U ∧ IsPreconnected U ∧ x ∈ U ∧ y ∈ U ∧
        IsCompact (closure U) ∧ closure U ⊆ MandelDim.Qreg c₁ c₂)
    (hnc : ∀ c : ℂ, ∃ z ∈ MandelDim.Qreg c₁ c₂, Ψ z ≠ c) :
    Set.InjOn Ψ (MandelDim.Qreg c₁ c₂) := by
  have hne : ¬ (∃ c : ℂ, ∀ z ∈ MandelDim.Qreg c₁ c₂, Ψ z = c) := by
    rintro ⟨c, hc⟩
    obtain ⟨z, hz, hzne⟩ := hnc c
    exact hzne (hc z hz)
  -- `Ψ` is holomorphic on `Qreg c₁ c₂`: pointwise, since for each `z` the convergence and the
  -- differentiability of `Φ n` are available on a ball around `z` with compact closure in `Qreg`.
  have hΨdiff : DifferentiableOn ℂ Ψ (MandelDim.Qreg c₁ c₂) := by
    refine differentiableOn_of_local hΨ fun z hz => ?_
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hOpen.mem_nhds hz)
    obtain ⟨r, hr0, hrε⟩ : ∃ r : ℝ, 0 < r ∧ r < ε := ⟨ε / 2, by positivity, by linarith⟩
    have hsub : closedBall z r ⊆ MandelDim.Qreg c₁ c₂ := fun w hw =>
      hεsub (by rw [mem_ball]; linarith [(mem_closedBall.mp hw)])
    exact ⟨r, hr0, hsub, by
      filter_upwards [hdom (closedBall z r) hsub (isCompact_closedBall z r)] with n hn
      exact ((hΦ n).1).mono fun w hw => hn (ball_subset_closedBall hw)⟩
  by_contra hnot
  obtain ⟨x, hxQ, y, hyQ, hxy, hxyne⟩ : ∃ x ∈ MandelDim.Qreg c₁ c₂, ∃ y ∈ MandelDim.Qreg c₁ c₂,
      Ψ x = Ψ y ∧ x ≠ y := by
    by_contra h
    exact hnot fun a ha b hb hab => by
      by_contra hab'
      exact h ⟨a, ha, b, hb, hab, hab'⟩
  obtain ⟨U, hUo, hUpc, hxU, hyU, hUcpt, hUQ⟩ := hpair x y hxQ hyQ
  have hUQ' : U ⊆ MandelDim.Qreg c₁ c₂ := fun z hz => hUQ (subset_closure hz)
  have hfU : ∀ᶠ n in atTop, DifferentiableOn ℂ (Φ n) U := by
    filter_upwards [hdom (closure U) hUQ hUcpt] with n hn
    exact ((hΦ n).1).mono fun z hz => hn (subset_closure hz)
  have hiU : ∀ᶠ n in atTop, Set.InjOn (Φ n) U := by
    filter_upwards [hdom (closure U) hUQ hUcpt] with n hn
    exact ((hΦ n).2.1).mono fun z hz => hn (subset_closure hz)
  have hconvU : TendstoLocallyUniformlyOn Φ Ψ atTop U := hΨ.mono hUQ'
  have hgU : DifferentiableOn ℂ Ψ U := hΨdiff.mono hUQ'
  rcases hurwitz_injOn_or_const hUo hUpc hfU hgU hconvU hiU with hinjU | ⟨c₀, hc₀⟩
  · exact hxyne (hinjU hxU hyU hxy)
  · have hev : Ψ =ᶠ[𝓝 x] (fun _ => c₀) := by
      filter_upwards [hUo.mem_nhds hxU] with z hz
      exact hc₀ z hz
    have hEq : EqOn Ψ (fun _ => c₀) (MandelDim.Qreg c₁ c₂) :=
      (hΨdiff.analyticOnNhd hOpen).eqOn_of_preconnected_of_eventuallyEq
        analyticOnNhd_const hPre hxQ hev
    obtain ⟨z, hz, hzne⟩ := hnc c₀
    exact hzne (hEq hz)

end Work.FatouCH.Cont
