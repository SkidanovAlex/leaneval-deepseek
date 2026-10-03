import Mathlib
import Submission.Work.Horn.HB.exists_analytic_extension_of_bounded
import Submission.Work.Horn.HB.extension_pow_eq
import Submission.Work.Horn.HB.deriv_eq_zero_of_eventually_pow_eq

/-!
# Uniqueness of the preimage of the (simple) zero of `φ` under a `d`-th root map

Setting (piece HB4 of the Horn/basin development, Shishikura Prop. 5.3 / Lemma 5.4).
`g : ℂ → ℂ` is holomorphic on the open set `W`, maps `W` into `V`, `φ` has a *simple* zero at
`v ∈ V` (`deriv φ v ≠ 0`), and `ψ` is a holomorphic `d`-th root of `φ ∘ g` on `W \ g⁻¹{v}`:

* `ψ` is analytic on `W \ g⁻¹{v}`, `‖ψ‖ ≤ 1` there, `(ψ z)^d = φ (g z)`, and
* `ψ` is injective on `W \ g⁻¹{v}`.

If `g⁻¹{v} ∩ W` is discrete and non-empty, then it is a *single point* `a`, and either `g` is
injective on `W` or `g` is critical at `a`.

This is the formal version of the paper's argument: `ψ` is locally `d`-to-`1` over `g`, the
injectivity of `ψ` off the critical fibre forces the local degree of `g` at every point of the
fibre to be exactly `d` and forces the fibre to be a single point (otherwise the open mapping
theorem produces two distinct points with the same `ψ`-value).
-/

namespace Work.Horn.HB

open Filter Metric
open scoped Topology

/-! ## Auxiliary topological / analytic lemmas -/

/-- **Open mapping theorem**, explicit `ball`-form.  If `f` is analytic at `z₀` and is not
eventually constant at `z₀`, then the image of every ball around `z₀` contains a ball around
`f z₀`. -/
theorem exists_ball_subset_image_of_analyticAt {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (hconst : ¬ ∀ᶠ z in 𝓝 z₀, f z = f z₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, Metric.ball (f z₀) δ ⊆ f '' Metric.ball z₀ ε := by
  have h := (hf.eventually_constant_or_nhds_le_map_nhds (g := f)).resolve_left hconst
  have hmem : f '' Metric.ball z₀ ε ∈ map f (𝓝 z₀) := by
    rw [Filter.mem_map]
    exact Filter.mem_of_superset (Metric.ball_mem_nhds z₀ hε) (Set.subset_preimage_image _ _)
  exact Metric.mem_nhds_iff.mp (h hmem)

/-- An open ball around `a` (of positive radius) contains two *distinct* points, both different
from `a`. -/
theorem exists_pair_mem_ball_ne {a : ℂ} {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ Metric.ball a ε, p ≠ a ∧ ∃ q ∈ Metric.ball a ε, q ≠ a ∧ p ≠ q := by
  refine ⟨a + ((ε / 2 : ℝ) : ℂ), ?_, ?_, a + ((ε / 4 : ℝ) : ℂ), ?_, ?_, ?_⟩
  · have h : dist (a + ((ε / 2 : ℝ) : ℂ)) a = ‖((ε / 2 : ℝ) : ℂ)‖ := by simp [dist_eq_norm]
    rw [Metric.mem_ball, h]
    simp [abs_of_pos hε]
    linarith
  · intro h
    have h2 : ((ε / 2 : ℝ) : ℂ) = 0 := by
      have := congrArg (fun w => w - a) h
      simpa using this
    rw [Complex.ofReal_eq_zero] at h2
    linarith
  · have h : dist (a + ((ε / 4 : ℝ) : ℂ)) a = ‖((ε / 4 : ℝ) : ℂ)‖ := by simp [dist_eq_norm]
    rw [Metric.mem_ball, h]
    simp [abs_of_pos hε]
    linarith
  · intro h
    have h2 : ((ε / 4 : ℝ) : ℂ) = 0 := by
      have := congrArg (fun w => w - a) h
      simpa using this
    rw [Complex.ofReal_eq_zero] at h2
    linarith
  · intro h
    have h2 : ((ε / 2 : ℝ) : ℂ) = ((ε / 4 : ℝ) : ℂ) := by
      have := congrArg (fun w => w - a) h
      simpa using this
    have h3 : ε / 2 = ε / 4 := Complex.ofReal_inj.mp h2
    linarith

/-! ## The main result -/

theorem exists_unique_preimage_of_root {g : ℂ → ℂ} {V W : Set ℂ} {v : ℂ} {d : ℕ} {φ ψ : ℂ → ℂ}
    (hd : 0 < d) (hWo : IsOpen W) (hvV : v ∈ V)
    (hφv : φ v = 0) (hφderiv : ∀ z ∈ V, deriv φ z ≠ 0)
    (hgV : ∀ z ∈ W, g z ∈ V) (hgcont : ∀ z ∈ W, ContinuousAt g z)
    (hgdiff : ∀ z ∈ W, DifferentiableAt ℂ g z)
    (hdisc : IsDiscrete (g ⁻¹' {v} ∩ W))
    (hψana : ∀ z ∈ W \ g ⁻¹' {v}, AnalyticAt ℂ ψ z)
    (hbdd : ∀ z ∈ W \ g ⁻¹' {v}, ‖ψ z‖ ≤ 1)
    (hpw : ∀ z ∈ W \ g ⁻¹' {v}, (ψ z) ^ d = φ (g z))
    (hinj : Set.InjOn ψ (W \ g ⁻¹' {v}))
    (hne : (g ⁻¹' {v} ∩ W).Nonempty) :
    ∃ a ∈ W, g a = v ∧ (∀ b ∈ W, g b = v → b = a) ∧ (¬ Set.InjOn g W → deriv g a = 0) := by
  classical
  set Z : Set ℂ := g ⁻¹' {v} ∩ W with hZ
  -- ## Step 0: `φ` is differentiable at `v` (hence continuous where `g` takes values in `V`)
  have hφdiff : DifferentiableAt ℂ φ v := by
    by_contra h
    exact hφderiv v hvV (deriv_zero_of_not_differentiableAt h)
  have hφcont_g : ∀ z ∈ W, ContinuousAt φ (g z) := by
    intro z hz
    have hd' : DifferentiableAt ℂ φ (g z) := by
      by_contra h
      exact hφderiv (g z) (hgV z hz) (deriv_zero_of_not_differentiableAt h)
    exact hd'.continuousAt
  -- ## Step 1: membership in `Z`, and isolation of its points
  have hmemZ : ∀ z ∈ W, (z ∈ Z ↔ g z = v) := by
    intro z hz
    simp only [hZ, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, hz, and_true]
  have hnotZ : ∀ z ∈ W, (z ∉ Z ↔ g z ≠ v) := fun z hz => (hmemZ z hz).not
  have hiso : ∀ c ∈ Z, ∃ ε : ℝ, 0 < ε ∧ Metric.ball c ε ⊆ W ∧ Metric.ball c ε ∩ Z = {c} := by
    intro c hc
    obtain ⟨u, hu_open, hu⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hdisc c hc
    have hcu : c ∈ u := by
      have hmem : c ∈ u ∩ Z := by rw [hu]; exact Set.mem_singleton c
      exact hmem.1
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ((hu_open.inter hWo).mem_nhds ⟨hcu, hc.2⟩)
    refine ⟨ε, hε, fun z hz => (hball hz).2, ?_⟩
    ext z
    constructor
    · intro hz
      have hmem : z ∈ u ∩ Z := ⟨(hball hz.1).1, hz.2⟩
      rwa [hu] at hmem
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨Metric.mem_ball_self hε, hc⟩
  -- ## Step 2: the analytic extension `Ψ` of `ψ` across `Z`
  have hWZ : ∀ z, z ∈ W \ Z ↔ z ∈ W ∧ g z ≠ v := by
    intro z
    rw [Set.mem_sdiff]
    constructor
    · rintro ⟨hw, hnz⟩
      exact ⟨hw, fun hgv => hnz ((hmemZ z hw).mpr hgv)⟩
    · rintro ⟨hw, hgv⟩
      exact ⟨hw, fun hzZ => hgv ((hmemZ z hw).mp hzZ)⟩
  have hPred : ∀ z, z ∈ W \ g ⁻¹' {v} ↔ z ∈ W ∧ g z ≠ v := by
    intro z
    simp only [Set.mem_sdiff, Set.mem_preimage, Set.mem_singleton_iff]
  have hψanaZ : ∀ z ∈ W \ Z, AnalyticAt ℂ ψ z := by
    intro z hz
    exact hψana z ((hPred z).mpr ((hWZ z).mp hz))
  have hbddZ : ∀ z ∈ W \ Z, ‖ψ z‖ ≤ 1 := by
    intro z hz
    exact hbdd z ((hPred z).mpr ((hWZ z).mp hz))
  have hpwZ : ∀ z ∈ W \ Z, (ψ z) ^ d = φ (g z) := by
    intro z hz
    exact hpw z ((hPred z).mpr ((hWZ z).mp hz))
  have hinjZ : Set.InjOn ψ (W \ Z) := by
    intro p hp q hq hpq
    exact hinj ((hPred p).mpr ((hWZ p).mp hp)) ((hPred q).mpr ((hWZ q).mp hq)) hpq
  have hFcl : ∀ z ∈ W, z ∉ Z → ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball z ρ ⊆ W \ Z := by
    intro z hzW hzZ
    have hgzv : g z ∈ ({v}ᶜ : Set ℂ) := ((hnotZ z hzW).mp hzZ)
    have h1 : g ⁻¹' ({v}ᶜ : Set ℂ) ∈ 𝓝 z :=
      (hgcont z hzW).preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hgzv)
    obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem h1 (hWo.mem_nhds hzW))
    refine ⟨ρ, hρ, fun w hw =>
      ⟨(hball hw).2, fun hwZ' => (hball hw).1 ((hmemZ w (hball hw).2).mp hwZ')⟩⟩
  obtain ⟨Ψ, hΨana, hΨeqOn⟩ :=
    exists_analytic_extension_of_bounded hWo hiso hFcl hψanaZ hbddZ
  have hΨeq : ∀ z ∈ W \ Z, Ψ z = ψ z := fun z hz => hΨeqOn hz
  -- ## Step 3: `Ψ ^ d = φ ∘ g` on `W`
  have hΨpow : ∀ z ∈ W, (Ψ z) ^ d = φ (g z) := by
    intro z hzW
    by_cases hzZ : z ∈ Z
    · exact extension_pow_eq (hiso z hzZ) (hΨana z hzW) hΨeq hpwZ (hφcont_g z hzW) (hgcont z hzW)
    · rw [hΨeq z ((hWZ z).mpr ⟨hzW, (hnotZ z hzW).mp hzZ⟩),
        hpwZ z ((hWZ z).mpr ⟨hzW, (hnotZ z hzW).mp hzZ⟩)]
  have hΨ0 : ∀ c ∈ Z, Ψ c = 0 := by
    intro c hc
    have h1 : (Ψ c) ^ d = 0 := by rw [hΨpow c hc.2, (hmemZ c hc.2).mp hc, hφv]
    exact eq_zero_of_pow_eq_zero h1
  -- ## Step 4: `Z` is a subsingleton
  have hZ_sub : Z.Subsingleton := by
    intro a₁ ha₁ a₂ ha₂
    by_contra hne12
    obtain ⟨ε₁, hε₁, hb₁W, hb₁Z⟩ := hiso a₁ ha₁
    obtain ⟨ε₂, hε₂, hb₂W, hb₂Z⟩ := hiso a₂ ha₂
    -- `Ψ` is not eventually constant at any point of `Z` (else `ψ` is constant on a punctured
    -- ball, contradicting injectivity there)
    have hnc : ∀ c ∈ Z, ¬ ∀ᶠ z in 𝓝 c, Ψ z = Ψ c := by
      intro c hc hconst
      obtain ⟨εc, hεc, hbcW, hbcZ⟩ := hiso c hc
      obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hconst
      obtain ⟨p, hp, hpne, q, hq, hqne, hpq⟩ :=
        exists_pair_mem_ball_ne (a := c) (ε := min ρ εc) (lt_min hρ hεc)
      have hpρ : p ∈ Metric.ball c ρ := Metric.ball_subset_ball (min_le_left _ _) hp
      have hqρ : q ∈ Metric.ball c ρ := Metric.ball_subset_ball (min_le_left _ _) hq
      have hΨp : Ψ p = Ψ c := hρsub hpρ
      have hΨq : Ψ q = Ψ c := hρsub hqρ
      have hpWZ : p ∈ W \ Z := by
        refine ⟨hbcW (Metric.ball_subset_ball (min_le_right _ _) hp), fun hpZ => hpne ?_⟩
        have hmem : p ∈ Metric.ball c εc ∩ Z :=
          ⟨Metric.ball_subset_ball (min_le_right _ _) hp, hpZ⟩
        rw [hbcZ] at hmem
        exact hmem
      have hqWZ : q ∈ W \ Z := by
        refine ⟨hbcW (Metric.ball_subset_ball (min_le_right _ _) hq), fun hqZ => hqne ?_⟩
        have hmem : q ∈ Metric.ball c εc ∩ Z :=
          ⟨Metric.ball_subset_ball (min_le_right _ _) hq, hqZ⟩
        rw [hbcZ] at hmem
        exact hmem
      have hψpq : ψ p = ψ q := by
        rw [← hΨeq p hpWZ, ← hΨeq q hqWZ, hΨp, hΨq]
      exact absurd (hinjZ hpWZ hqWZ hψpq) hpq
    -- a common radius, small enough for both isolation balls and for disjointness
    have hdist_pos : 0 < dist a₁ a₂ := dist_pos.mpr hne12
    set ε : ℝ := min (min ε₁ ε₂) (dist a₁ a₂ / 2) with hεdef
    have hε : 0 < ε := lt_min (lt_min hε₁ hε₂) (half_pos hdist_pos)
    have hε₁' : ε ≤ ε₁ := le_trans (min_le_left _ _) (min_le_left _ _)
    have hε₂' : ε ≤ ε₂ := le_trans (min_le_left _ _) (min_le_right ε₁ ε₂)
    have hεab : 2 * ε ≤ dist a₁ a₂ := by
      have h := min_le_right (min ε₁ ε₂) (dist a₁ a₂ / 2)
      linarith
    -- the open mapping theorem at `a₁` and at `a₂`
    obtain ⟨δ₁, hδ₁, hsub₁⟩ :=
      exists_ball_subset_image_of_analyticAt (hΨana a₁ ha₁.2) (hnc a₁ ha₁) hε
    obtain ⟨δ₂, hδ₂, hsub₂⟩ :=
      exists_ball_subset_image_of_analyticAt (hΨana a₂ ha₂.2) (hnc a₂ ha₂) hε
    rw [hΨ0 a₁ ha₁] at hsub₁
    rw [hΨ0 a₂ ha₂] at hsub₂
    set δ : ℝ := min δ₁ δ₂ with hδdef
    have hδ : 0 < δ := lt_min hδ₁ hδ₂
    have hw_mem : ∀ {δ' : ℝ}, δ ≤ δ' → ((δ / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) δ' := by
      intro δ' hδ'
      have h1 : dist (((δ / 2 : ℝ) : ℂ)) 0 < δ' := by
        rw [dist_eq_norm, sub_zero]
        simp [abs_of_pos hδ]
        linarith
      simpa using h1
    have hw₁ : ((δ / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) δ₁ := hw_mem (min_le_left _ _)
    have hw₂ : ((δ / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) δ₂ := hw_mem (min_le_right _ _)
    obtain ⟨p, hp, hpΨ⟩ := hsub₁ hw₁
    obtain ⟨q, hq, hqΨ⟩ := hsub₂ hw₂
    -- `p ≠ q`, since the two balls `ball a₁ ε`, `ball a₂ ε` are disjoint
    have hpq_ne : p ≠ q := by
      intro hpq
      have h1 : dist p a₁ < ε := Metric.mem_ball.mp hp
      have h2 : dist q a₂ < ε := Metric.mem_ball.mp hq
      have h3 : dist a₁ a₂ ≤ dist a₁ p + dist p a₂ := dist_triangle a₁ p a₂
      have h4 : dist a₁ p < ε := by rw [dist_comm]; exact h1
      have h5 : dist p a₂ < ε := by rw [hpq]; exact h2
      have h6 : dist a₁ a₂ < 2 * ε := by linarith
      linarith
    -- `p` and `q` avoid `Z` (their `Ψ`-value is the non-zero number `δ/2`)
    have hpWZ : p ∈ W \ Z := by
      refine ⟨hb₁W (Metric.ball_subset_ball hε₁' hp), fun hpZ => ?_⟩
      have hmem : p ∈ Metric.ball a₁ ε₁ ∩ Z := ⟨Metric.ball_subset_ball hε₁' hp, hpZ⟩
      rw [hb₁Z] at hmem
      rw [hmem] at hpΨ
      have hzero : ((δ / 2 : ℝ) : ℂ) = 0 := by rw [← hpΨ, hΨ0 a₁ ha₁]
      rw [Complex.ofReal_eq_zero] at hzero
      linarith
    have hqWZ : q ∈ W \ Z := by
      refine ⟨hb₂W (Metric.ball_subset_ball hε₂' hq), fun hqZ => ?_⟩
      have hmem : q ∈ Metric.ball a₂ ε₂ ∩ Z := ⟨Metric.ball_subset_ball hε₂' hq, hqZ⟩
      rw [hb₂Z] at hmem
      rw [hmem] at hqΨ
      have hzero : ((δ / 2 : ℝ) : ℂ) = 0 := by rw [← hqΨ, hΨ0 a₂ ha₂]
      rw [Complex.ofReal_eq_zero] at hzero
      linarith
    have hψpq : ψ p = ψ q := by
      rw [← hΨeq p hpWZ, ← hΨeq q hqWZ, hpΨ, hqΨ]
    exact absurd (hinjZ hpWZ hqWZ hψpq) hpq_ne
  -- ## Step 5: the witness and the two conclusions
  obtain ⟨a, ha⟩ := hne
  have haW : a ∈ W := ha.2
  have hga : g a = v := (hmemZ a ha.2).mp ha
  refine ⟨a, haW, hga, ?_, ?_⟩
  · intro b hbW hgb
    exact hZ_sub ((hmemZ b hbW).mpr hgb) ha
  · intro hnotinj
    by_contra hderiv
    -- If `g` were critical-free at `a`, the local relation `(Ψ z)^d = φ (g z)` would force `d = 1`
    have hd1 : d = 1 := by
      rcases Nat.lt_or_ge 1 d with hlt | hle
      · exfalso
        have heqev : ∀ᶠ z in 𝓝 a, (Ψ z) ^ d = φ (g z) :=
          Filter.eventually_of_mem (hWo.mem_nhds haW) (fun z hz => hΨpow z hz)
        exact hderiv (deriv_eq_zero_of_eventually_pow_eq (hΨana a haW) (hΨ0 a ha) hga hφdiff
          (hgdiff a haW) (hφderiv v hvV) hlt heqev)
      · omega
    -- with `d = 1` the relation `ψ = φ ∘ g` makes `g` injective on `W`
    have hinjg : Set.InjOn g W := by
      intro p hpW q hqW hpq
      by_cases hgp : g p = v
      · exact hZ_sub ((hmemZ p hpW).mpr hgp)
          ((hmemZ q hqW).mpr (by rw [← hpq]; exact hgp))
      · have hq_nev : g q ≠ v := by rw [← hpq]; exact hgp
        have hpWZ : p ∈ W \ Z := ⟨hpW, (hnotZ p hpW).mpr hgp⟩
        have hqWZ : q ∈ W \ Z := ⟨hqW, (hnotZ q hqW).mpr hq_nev⟩
        have hpp : ψ p = φ (g p) := by simpa [hd1] using hpwZ p hpWZ
        have hqq : ψ q = φ (g q) := by simpa [hd1] using hpwZ q hqWZ
        exact hinjZ hpWZ hqWZ (by rw [hpp, hqq, hpq])
    exact hnotinj hinjg

end Work.Horn.HB
