import Mathlib
import Submission.Work.ELRig.Inputs
import Submission.Work.ELRig.Sides
import Submission.Work.ELRig.reach
import Submission.Work.ELRig.eqOn_real_of_frequently_real
import Submission.Work.ELRig.LocalInverse.exists_analytic_localInverse
import Submission.Work.ELRig.exists_localInverseAt_of_psi_eq_b2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section

namespace Work.ELRig

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Auxiliary lemmas -/

/-- A sequence of reals tending to `x`, never equal to `x`, and with a property `p` at every
term gives a "frequently" statement for `p` at `x`. -/
theorem frequently_of_tendsto_ne {u : ℕ → ℝ} {x : ℝ} {p : ℝ → Prop}
    (hu : Filter.Tendsto u Filter.atTop (nhds x)) (hne : ∀ n, u n ≠ x) (hp : ∀ n, p (u n)) :
    ∃ᶠ t in nhdsWithin x {x}ᶜ, p t := by
  rw [Filter.frequently_iff]
  intro U hU
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp hu) ε hε
  exact ⟨u K, hVU ⟨hεV (hK K le_rfl), by simpa using hne K⟩, hp K⟩

/-- The equator is contained in `K c` when all its points are (the contradiction hypothesis of
R-f). -/
theorem equator_subset_K' {c : ℂ} {z₁ : ℂ}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) z₁)
    (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ Work.EL.K c) :
    Work.EL.equator fl ⊆ Work.EL.K c := fun _ hz => by
  obtain ⟨x, rfl⟩ := hz
  exact hE x

/-- The equator is forward invariant under `F c`. -/
theorem mapsTo_equator' {c : ℂ} {z₁ : ℂ}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) z₁) :
    Set.MapsTo (Work.EL.F c) (Work.EL.equator fl)
      (Work.EL.equator fl) := by
  rintro z ⟨x, rfl⟩
  refine ⟨x + 1, ?_⟩
  push_cast
  exact fl.Ψ_shift (x : ℂ)

/-- A point at distance `≥ ε` from `b` is not in the closure of a set contained in the ball of
radius `ε` about `b`. -/
theorem notMem_closure_of {Δ : Set ℂ} {b x : ℂ} {ε : ℝ}
    (hsub : Δ ⊆ Metric.ball b ε) (h : ε < dist x b) : x ∉ closure Δ := by
  intro hcl
  by_cases hε : ε ≤ 0
  · have hΔ : Δ = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr (fun y hy => ?_)
      have h1 : dist y b < ε := Metric.mem_ball.mp (hsub hy)
      have h2 : 0 ≤ dist y b := dist_nonneg
      linarith
    rw [hΔ, closure_empty] at hcl
    exact hcl
  · have h4 : x ∈ closure (Metric.ball b ε) := closure_mono hsub hcl
    have h5 : dist x b ≤ ε := by
      by_contra hlt
      have hlt' : ε < dist x b := lt_of_not_ge hlt
      obtain ⟨y, hy, hyx⟩ := (Metric.mem_closure_iff.mp h4) ((dist x b - ε) / 2) (by linarith)
      have h6 : dist y b < ε := Metric.mem_ball.mp hy
      have h7 : dist x b ≤ dist x y + dist y b := dist_triangle x y b
      linarith
    exact absurd h5 (not_le.mpr h)

/-- The tripod curve meets the filled Julia set only in its landing point. -/
theorem tripodCurve_inter_K {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} {y : ℂ} :
    Work.EL.tripodCurve hN y ∩ Work.EL.K c ⊆ {y} := by
  rintro z ⟨hz, hzK⟩
  simp only [Work.EL.tripodCurve, Set.mem_union, Set.mem_singleton_iff] at hz
  rcases hz with ((h | h) | h) | h
  · exact absurd hzK ((Set.mem_compl_iff _ _).mp (Work.EL.paramRay_subset_compl hN Work.EL.b2a h))
  · exact absurd hzK ((Set.mem_compl_iff _ _).mp (Work.EL.paramRay_subset_compl hN Work.EL.b2b h))
  · exact absurd hzK ((Set.mem_compl_iff _ _).mp (Work.EL.paramRay_subset_compl hN Work.EL.b2c h))
  · exact h

/-- The arms of a tripod are pairwise disjoint. -/
theorem armOf_disjoint {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} {y : ℂ}
    (T : Work.EL.TripodSides hN y) {Z W : Work.EL.ArmIdx} (h : Z ≠ W) :
    Disjoint (Work.EL.armOf T Z) (Work.EL.armOf T W) := by
  cases Z <;> cases W <;>
    first
      | exact (h rfl).elim
      | exact T.disjoint_AB
      | exact T.disjoint_AB.symm
      | exact T.disjoint_AC
      | exact T.disjoint_AC.symm
      | exact T.disjoint_BC
      | exact T.disjoint_BC.symm

/-- A preconnected subset of `K c` avoiding the tripod curve lies in one of the three arms. -/
theorem B2Data.subset_arm_of {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} {z₁ : ℂ}
    (tr : Work.EL.B2Data hN z₁) {S : Set ℂ} (hconn : IsPreconnected S)
    (hav : S ⊆ (Work.EL.tripodCurve hN tr.b₂)ᶜ) :
    S ⊆ Work.EL.armOf tr.tripod Work.EL.ArmIdx.A ∨
      S ⊆ Work.EL.armOf tr.tripod Work.EL.ArmIdx.B ∨
      S ⊆ Work.EL.armOf tr.tripod Work.EL.ArmIdx.C := by
  rcases tr.tripod.subset_of_preconnected hconn hav with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- **The cut point crossing lemma.**  A preconnected subset of `K c` inside an arm of the
tripod which meets the nest `Δ n` and leaves its closure contains the cut point `cut Z n`. -/
theorem B2Data.cut_mem_of {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} {z₁ : ℂ}
    (tr : Work.EL.B2Data hN z₁) {Z : Work.EL.ArmIdx} {n : ℕ} {S : Set ℂ}
    (hS : S ⊆ Work.EL.K c) (hconn : IsPreconnected S) (harm : S ⊆ Work.EL.armOf tr.tripod Z)
    (hΔ : ∃ z ∈ S, z ∈ tr.Δ n) (hout : ∃ z ∈ S, z ∉ closure (tr.Δ n)) :
    tr.cut Z n ∈ S := by
  obtain ⟨xin, hxinS, hxinΔ⟩ := hΔ
  obtain ⟨xout, hxoutS, hxoutc⟩ := hout
  obtain ⟨z, hzS, hzfr⟩ := Work.EL.meets_frontier_of (tr.isOpen_Δ n) hconn hxinS hxinΔ
    hxoutS hxoutc
  have hzmem : z ∈ frontier (tr.Δ n) ∩ Work.EL.K c ∩ Work.EL.armOf tr.tripod Z :=
    ⟨⟨hzfr, hS hzS⟩, harm hzS⟩
  rw [tr.cut_unique Z n] at hzmem
  exact (Set.mem_singleton_iff.mp hzmem) ▸ hzS

/-- Two two-element subsets of the three arms always meet. -/
theorem exists_common_arm {X Y : Work.EL.ArmIdx} (hXY : X ≠ Y) :
    ∃ Z : Work.EL.ArmIdx, (Z = X ∨ Z = Y) ∧
      (Z = Work.EL.ArmIdx.rot X ∨ Z = Work.EL.ArmIdx.rot Y) := by
  cases X <;> cases Y <;>
    first
      | exact (hXY rfl).elim
      | exact ⟨_, Or.inl rfl, Or.inl rfl⟩
      | exact ⟨_, Or.inl rfl, Or.inr rfl⟩
      | exact ⟨_, Or.inr rfl, Or.inl rfl⟩
      | exact ⟨_, Or.inr rfl, Or.inr rfl⟩

/-- `rot` has no invariant two-element subset. -/
theorem rot_no_two_cycle {X Y : Work.EL.ArmIdx} (hXY : X ≠ Y)
    (h : Work.EL.ArmIdx.rot X = Y) (h' : Work.EL.ArmIdx.rot Y = X) : False := by
  have h2 : Work.EL.ArmIdx.rot (Work.EL.ArmIdx.rot X) = X := by rw [h, h']
  have h3 : X = Work.EL.ArmIdx.rot X := by
    have hcycle := Work.EL.ArmIdx.rot_cycle X
    rw [h2] at hcycle
    exact hcycle.symm
  exact hXY (h3.trans h)

/-- **`Work.ELRig.rigidity`**: the equator of the repelling coordinate of a root-parabolic
parameter cannot be contained in the filled Julia set. -/
theorem rigidity {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (nest : Work.EL.Z1Nest d.hN d.z₁ fl.Pa)
    {R₀ : ℝ}
    (hγ : ∀ w : ℂ, w.re < -R₀ → R₀ < |w.im| → fl.Ψ w ∈ fl.Pa)
    (htail : ∃ R' : ℝ, ∀ x : ℝ, x < -R' → fl.Ψ (x : ℂ) ∈ Work.EL.pairSideNear nest.P0)
    (tr : Work.EL.B2Data d.hN d.z₁)
    (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ Work.EL.K c) : False := by
  -- Step 1: `reach` gives `b₂ ∈ E` and `F b₂ = b₂`
  obtain ⟨u, huE, huF, hFuE, hb₂E, hFb₂⟩ := reach d fl nest hγ htail tr hE
  obtain ⟨xstar, hxstar⟩ := hb₂E
  have hb₂K : tr.b₂ ∈ Work.EL.K c := by
    rw [← hxstar]; exact hE xstar
  -- Step 2: local inverses of `Ψ` at the two real points `x*` and `x* + 1`
  have hxstar' : fl.Ψ ((xstar : ℝ) : ℂ) = tr.b₂ := hxstar
  have hΨx1 : fl.Ψ (((xstar + 1 : ℝ)) : ℂ) = tr.b₂ := by
    have h := fl.Ψ_shift ((xstar : ℝ) : ℂ)
    have hcast : ((xstar + 1 : ℝ) : ℂ) = ((xstar : ℝ) : ℂ) + 1 := by push_cast; ring
    rw [hcast, h, hxstar', hFb₂]
  obtain ⟨d₀, hd₀pos, τ₀, hτ₀an, hτ₀left, hτ₀right⟩ :=
    Work.ELRig.exists_localInverseAt_of_psi_eq_b2 d fl tr hxstar'
  have hinj₀ : Set.InjOn fl.Ψ (Metric.ball ((xstar : ℝ) : ℂ) d₀) := by
    intro a ha b hb hab
    rw [← hτ₀left a ha, hab, hτ₀left b hb]
  obtain ⟨d₁, hd₁pos, τ₁, hτ₁an, hτ₁left, hτ₁right⟩ :=
    Work.ELRig.exists_localInverseAt_of_psi_eq_b2 d fl tr hΨx1
  have hinj₁ : Set.InjOn fl.Ψ (Metric.ball (((xstar + 1 : ℝ)) : ℂ) d₁) := by
    intro a ha b hb hab
    rw [← hτ₁left a ha, hab, hτ₁left b hb]
  obtain ⟨δ₁a, hδ₁apos, δ₂a, hδ₂apos, σa, hσaan, hσarght, hσaleft, hσaderiv⟩ :=
    Work.ELRig.LocalInverse.exists_analytic_localInverse fl.Ψ_diff ⟨d₀, hd₀pos, hinj₀⟩
  obtain ⟨δ₁b, hδ₁bpos, δ₂b, hδ₂bpos, σb, hσban, hσbrght, hσbleft, hσbderiv⟩ :=
    Work.ELRig.LocalInverse.exists_analytic_localInverse fl.Ψ_diff ⟨d₁, hd₁pos, hinj₁⟩
  have hcont1 : ∀ᶠ w in 𝓝 (((xstar + 1 : ℝ)) : ℂ), fl.Ψ w ∈ Metric.ball tr.b₂ δ₂a :=
    fl.Ψ_diff.continuous.continuousAt.preimage_mem_nhds
      (by rw [hΨx1]; exact Metric.ball_mem_nhds _ hδ₂apos)
  obtain ⟨η₁, hη₁pos, hη₁⟩ := Metric.mem_nhds_iff.mp hcont1
  -- Step 3: the small radius `δ`
  set δ : ℝ := min (min d₀ d₁) (min (min δ₁a δ₁b) η₁) / 2 with hδdef
  have hminpos : 0 < min (min d₀ d₁) (min (min δ₁a δ₁b) η₁) :=
    lt_min (lt_min hd₀pos hd₁pos) (lt_min (lt_min hδ₁apos hδ₁bpos) hη₁pos)
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδlt : δ < min (min d₀ d₁) (min (min δ₁a δ₁b) η₁) := by
    rw [hδdef]; exact div_lt_self hminpos (by norm_num)
  have hδd₀ : δ < d₀ :=
    lt_of_lt_of_le hδlt (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδd₁ : δ < d₁ :=
    lt_of_lt_of_le hδlt (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδδ₁a : δ < δ₁a :=
    lt_of_lt_of_le hδlt (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hδδ₁b : δ < δ₁b :=
    lt_of_lt_of_le hδlt (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hδη₁ : δ < η₁ :=
    lt_of_lt_of_le hδlt (le_trans (min_le_right _ _) (min_le_right _ _))
  -- Step 4: the real parametrisation of the equator
  let φ : ℝ → ℂ := fun t => fl.Ψ (t : ℂ)
  have hφcont : Continuous φ := fl.Ψ_diff.continuous.comp Complex.continuous_ofReal
  have hφshift : ∀ t : ℝ, Work.EL.F c (φ t) = φ (t + 1) := by
    intro t
    have hcast : ((t + 1 : ℝ) : ℂ) = (t : ℂ) + 1 := by push_cast; ring
    simp only [φ]
    rw [hcast, fl.Ψ_shift]
  have hb₂φ : φ xstar = tr.b₂ := by simp only [φ]; exact hxstar
  have hφx1 : φ (xstar + 1) = tr.b₂ := by simp only [φ]; exact hΨx1
  have hmem₀ : ∀ t : ℝ, |t - xstar| < d₀ → (t : ℂ) ∈ Metric.ball ((xstar : ℝ) : ℂ) d₀ := by
    intro t ht
    rw [Metric.mem_ball, Complex.isometry_ofReal.dist_eq, Real.dist_eq]
    exact ht
  have hmem₁ : ∀ t : ℝ, |t - (xstar + 1)| < d₁ →
      (t : ℂ) ∈ Metric.ball (((xstar + 1 : ℝ)) : ℂ) d₁ := by
    intro t ht
    rw [Metric.mem_ball, Complex.isometry_ofReal.dist_eq, Real.dist_eq]
    exact ht
  have hφinj : Set.InjOn φ (Set.Ioo (xstar - δ) (xstar + δ)) := by
    intro s hs t ht hst
    refine Complex.ofReal_inj.mp (hinj₀ (hmem₀ s ?_) (hmem₀ t ?_) ?_)
    · rw [abs_lt]; exact ⟨by linarith [hs.1], lt_trans (by linarith [hs.2]) hδd₀⟩
    · rw [abs_lt]; exact ⟨by linarith [ht.1], lt_trans (by linarith [ht.2]) hδd₀⟩
    · simpa only [φ] using hst
  have hφinj₁ : Set.InjOn φ (Set.Ioo (xstar + 1 - δ) (xstar + 1 + δ)) := by
    intro s hs t ht hst
    refine Complex.ofReal_inj.mp (hinj₁ (hmem₁ s ?_) (hmem₁ t ?_) ?_)
    · rw [abs_lt]; exact ⟨by linarith [hs.1], lt_trans (by linarith [hs.2]) hδd₁⟩
    · rw [abs_lt]; exact ⟨by linarith [ht.1], lt_trans (by linarith [ht.2]) hδd₁⟩
    · simpa only [φ] using hst
  -- Step 5: the two halves of the equator arc through `b₂` lie in two arms
  have hσplusconn : IsPreconnected (φ '' Set.Ioo xstar (xstar + δ)) :=
    (isPreconnected_Ioo).image φ hφcont.continuousOn
  have hσminusconn : IsPreconnected (φ '' Set.Ioo (xstar - δ) xstar) :=
    (isPreconnected_Ioo).image φ hφcont.continuousOn
  have hσplusE : φ '' Set.Ioo xstar (xstar + δ) ⊆ Work.EL.equator fl := by
    rintro z ⟨t, ht, rfl⟩; exact ⟨t, rfl⟩
  have hσminusE : φ '' Set.Ioo (xstar - δ) xstar ⊆ Work.EL.equator fl := by
    rintro z ⟨t, ht, rfl⟩; exact ⟨t, rfl⟩
  have hσplusK : φ '' Set.Ioo xstar (xstar + δ) ⊆ Work.EL.K c := by
    rintro z ⟨t, ht, rfl⟩; exact hE t
  have hσminusK : φ '' Set.Ioo (xstar - δ) xstar ⊆ Work.EL.K c := by
    rintro z ⟨t, ht, rfl⟩; exact hE t
  have hσplus_av : φ '' Set.Ioo xstar (xstar + δ) ⊆ (Work.EL.tripodCurve d.hN tr.b₂)ᶜ := by
    rintro z ⟨t, ht, rfl⟩ hzcurve
    have h1 := tripodCurve_inter_K (hN := d.hN) (y := tr.b₂) ⟨hzcurve, hE t⟩
    rw [Set.mem_singleton_iff] at h1
    have h2 : (t : ℂ) = (xstar : ℂ) :=
      hinj₀ (hmem₀ t (by rw [abs_lt]; exact ⟨by linarith [ht.1],
        lt_trans (by linarith [ht.2]) hδd₀⟩)) (Metric.mem_ball_self hd₀pos)
        (by simpa only [φ] using h1.trans hb₂φ.symm)
    exact absurd (Complex.ofReal_inj.mp h2) (ne_of_gt ht.1)
  have hσminus_av : φ '' Set.Ioo (xstar - δ) xstar ⊆ (Work.EL.tripodCurve d.hN tr.b₂)ᶜ := by
    rintro z ⟨t, ht, rfl⟩ hzcurve
    have h1 := tripodCurve_inter_K (hN := d.hN) (y := tr.b₂) ⟨hzcurve, hE t⟩
    rw [Set.mem_singleton_iff] at h1
    have h2 : (t : ℂ) = (xstar : ℂ) :=
      hinj₀ (hmem₀ t (by rw [abs_lt]; exact ⟨by linarith [ht.1],
        lt_trans (by linarith [ht.2]) hδd₀⟩)) (Metric.mem_ball_self hd₀pos)
        (by simpa only [φ] using h1.trans hb₂φ.symm)
    exact absurd (Complex.ofReal_inj.mp h2) (ne_of_lt ht.2)
  obtain ⟨X, hX⟩ : ∃ X : Work.EL.ArmIdx,
      φ '' Set.Ioo xstar (xstar + δ) ⊆ Work.EL.armOf tr.tripod X := by
    rcases Work.ELRig.B2Data.subset_arm_of tr hσplusconn hσplus_av with h | h | h
    · exact ⟨Work.EL.ArmIdx.A, h⟩
    · exact ⟨Work.EL.ArmIdx.B, h⟩
    · exact ⟨Work.EL.ArmIdx.C, h⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Work.EL.ArmIdx,
      φ '' Set.Ioo (xstar - δ) xstar ⊆ Work.EL.armOf tr.tripod Y := by
    rcases Work.ELRig.B2Data.subset_arm_of tr hσminusconn hσminus_av with h | h | h
    · exact ⟨Work.EL.ArmIdx.A, h⟩
    · exact ⟨Work.EL.ArmIdx.B, h⟩
    · exact ⟨Work.EL.ArmIdx.C, h⟩
  have hσ_le : φ '' Set.Ioo (xstar - δ) (xstar + δ) ⊆
      Work.EL.armOf tr.tripod X ∪ Work.EL.armOf tr.tripod Y ∪ {tr.b₂} := by
    rintro z ⟨t, ht, rfl⟩
    rcases lt_trichotomy t xstar with h | h | h
    · exact Or.inl (Or.inr (hY ⟨t, ⟨ht.1, h⟩, rfl⟩))
    · exact Or.inr (by simp only [h, hb₂φ, Set.mem_singleton_iff])
    · exact Or.inl (Or.inl (hX ⟨t, ⟨h, ht.2⟩, rfl⟩))
  -- Step 6: the images of the two halves under `F`
  have hFplus_eq : Work.EL.F c '' (φ '' Set.Ioo xstar (xstar + δ))
      = φ '' Set.Ioo (xstar + 1) (xstar + 1 + δ) := by
    ext z; constructor
    · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t + 1, ⟨by linarith [ht.1], by linarith [ht.2]⟩, (hφshift t).symm⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨φ (s - 1), ⟨s - 1, ⟨by linarith [hs.1], by linarith [hs.2]⟩, rfl⟩, ?_⟩
      rw [hφshift (s - 1)]
      congr 1
      ring
  have hFminus_eq : Work.EL.F c '' (φ '' Set.Ioo (xstar - δ) xstar)
      = φ '' Set.Ioo (xstar + 1 - δ) (xstar + 1) := by
    ext z; constructor
    · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t + 1, ⟨by linarith [ht.1], by linarith [ht.2]⟩, (hφshift t).symm⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨φ (s - 1), ⟨s - 1, ⟨by linarith [hs.1], by linarith [hs.2]⟩, rfl⟩, ?_⟩
      rw [hφshift (s - 1)]
      congr 1
      ring
  have hFplusK : Work.EL.F c '' (φ '' Set.Ioo xstar (xstar + δ)) ⊆ Work.EL.K c :=
    subset_trans (Set.image_mono hσplusE)
      (subset_trans (Set.MapsTo.image_subset (Work.ELRig.mapsTo_equator' fl))
        (Work.ELRig.equator_subset_K' fl hE))
  have hFminusK : Work.EL.F c '' (φ '' Set.Ioo (xstar - δ) xstar) ⊆ Work.EL.K c :=
    subset_trans (Set.image_mono hσminusE)
      (subset_trans (Set.MapsTo.image_subset (Work.ELRig.mapsTo_equator' fl))
        (Work.ELRig.equator_subset_K' fl hE))
  have hFplus_av : Work.EL.F c '' (φ '' Set.Ioo xstar (xstar + δ))
      ⊆ (Work.EL.tripodCurve d.hN tr.b₂)ᶜ := by
    rintro z ⟨y, ⟨t, ht, rfl⟩, rfl⟩ hzcurve
    have hzK : φ (t + 1) ∈ Work.EL.K c := by
      rw [← hφshift t]
      exact hFplusK ⟨φ t, ⟨t, ht, rfl⟩, rfl⟩
    have hcurve : φ (t + 1) ∈ Work.EL.tripodCurve d.hN tr.b₂ := by
      rw [← hφshift t]; exact hzcurve
    have h1 := tripodCurve_inter_K (hN := d.hN) (y := tr.b₂) ⟨hcurve, hzK⟩
    rw [Set.mem_singleton_iff] at h1
    have h2 : t + 1 = xstar + 1 :=
      hφinj₁ ⟨by linarith [ht.1], by linarith [ht.2]⟩ ⟨by linarith, by linarith⟩
        (h1.trans hφx1.symm)
    linarith [ht.1, h2]
  have hFminus_av : Work.EL.F c '' (φ '' Set.Ioo (xstar - δ) xstar)
      ⊆ (Work.EL.tripodCurve d.hN tr.b₂)ᶜ := by
    rintro z ⟨y, ⟨t, ht, rfl⟩, rfl⟩ hzcurve
    have hzK : φ (t + 1) ∈ Work.EL.K c := by
      rw [← hφshift t]
      exact hFminusK ⟨φ t, ⟨t, ht, rfl⟩, rfl⟩
    have hcurve : φ (t + 1) ∈ Work.EL.tripodCurve d.hN tr.b₂ := by
      rw [← hφshift t]; exact hzcurve
    have h1 := tripodCurve_inter_K (hN := d.hN) (y := tr.b₂) ⟨hcurve, hzK⟩
    rw [Set.mem_singleton_iff] at h1
    have h2 : t + 1 = xstar + 1 :=
      hφinj₁ ⟨by linarith [ht.1], by linarith [ht.2]⟩ ⟨by linarith, by linarith⟩
        (h1.trans hφx1.symm)
    linarith [ht.2, h2]
  have hFplusconn : IsPreconnected (Work.EL.F c '' (φ '' Set.Ioo xstar (xstar + δ))) := by
    rw [hFplus_eq]
    exact (isPreconnected_Ioo).image φ hφcont.continuousOn
  have hFminusconn : IsPreconnected (Work.EL.F c '' (φ '' Set.Ioo (xstar - δ) xstar)) := by
    rw [hFminus_eq]
    exact (isPreconnected_Ioo).image φ hφcont.continuousOn
  -- Step 7: the level threshold and the crossing facts
  have hρplus : 0 < ‖φ (xstar + δ / 2) - tr.b₂‖ := by
    rw [← hb₂φ, norm_pos_iff, sub_ne_zero]
    intro hcon
    have h1 : xstar + δ / 2 ∈ Set.Ioo (xstar - δ) (xstar + δ) := ⟨by linarith, by linarith⟩
    have h2 : xstar ∈ Set.Ioo (xstar - δ) (xstar + δ) := ⟨by linarith, by linarith⟩
    linarith [hφinj h1 h2 hcon]
  have hρminus : 0 < ‖φ (xstar - δ / 2) - tr.b₂‖ := by
    rw [← hb₂φ, norm_pos_iff, sub_ne_zero]
    intro hcon
    have h1 : xstar - δ / 2 ∈ Set.Ioo (xstar - δ) (xstar + δ) := ⟨by linarith, by linarith⟩
    have h2 : xstar ∈ Set.Ioo (xstar - δ) (xstar + δ) := ⟨by linarith, by linarith⟩
    linarith [hφinj h1 h2 hcon]
  have hρFplus : 0 < ‖φ (xstar + 1 + δ / 2) - tr.b₂‖ := by
    rw [← hφx1, norm_pos_iff, sub_ne_zero]
    intro hcon
    have h1 : xstar + 1 + δ / 2 ∈ Set.Ioo (xstar + 1 - δ) (xstar + 1 + δ) :=
      ⟨by linarith, by linarith⟩
    have h2 : xstar + 1 ∈ Set.Ioo (xstar + 1 - δ) (xstar + 1 + δ) :=
      ⟨by linarith [hδpos], by linarith [hδpos]⟩
    linarith [hφinj₁ h1 h2 hcon]
  have hρFminus : 0 < ‖φ (xstar + 1 - δ / 2) - tr.b₂‖ := by
    rw [← hφx1, norm_pos_iff, sub_ne_zero]
    intro hcon
    have h1 : xstar + 1 - δ / 2 ∈ Set.Ioo (xstar + 1 - δ) (xstar + 1 + δ) :=
      ⟨by linarith, by linarith⟩
    have h2 : xstar + 1 ∈ Set.Ioo (xstar + 1 - δ) (xstar + 1 + δ) :=
      ⟨by linarith [hδpos], by linarith [hδpos]⟩
    linarith [hφinj₁ h1 h2 hcon]
  obtain ⟨N₁, hN₁⟩ := tr.Δ_shrinks
    (min (min ‖φ (xstar + δ / 2) - tr.b₂‖ ‖φ (xstar - δ / 2) - tr.b₂‖)
      (min ‖φ (xstar + 1 + δ / 2) - tr.b₂‖ ‖φ (xstar + 1 - δ / 2) - tr.b₂‖) / 2)
    (by positivity)
  obtain ⟨N₂, hN₂⟩ := tr.rot_cut
  have hout_plus : ∀ m : ℕ, N₁ ≤ m →
      ∃ z ∈ φ '' Set.Ioo xstar (xstar + δ), z ∉ closure (tr.Δ m) := by
    intro m hm
    refine ⟨φ (xstar + δ / 2), ⟨xstar + δ / 2, ⟨by linarith, by linarith⟩, rfl⟩,
      notMem_closure_of (hN₁ m hm) ?_⟩
    rw [dist_eq_norm]
    have h3 : min (min ‖φ (xstar + δ / 2) - tr.b₂‖ ‖φ (xstar - δ / 2) - tr.b₂‖)
        (min ‖φ (xstar + 1 + δ / 2) - tr.b₂‖ ‖φ (xstar + 1 - δ / 2) - tr.b₂‖) ≤
        ‖φ (xstar + δ / 2) - tr.b₂‖ :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    linarith [hρplus, h3]
  have hout_minus : ∀ m : ℕ, N₁ ≤ m →
      ∃ z ∈ φ '' Set.Ioo (xstar - δ) xstar, z ∉ closure (tr.Δ m) := by
    intro m hm
    refine ⟨φ (xstar - δ / 2), ⟨xstar - δ / 2, ⟨by linarith, by linarith⟩, rfl⟩,
      notMem_closure_of (hN₁ m hm) ?_⟩
    rw [dist_eq_norm]
    have h3 : min (min ‖φ (xstar + δ / 2) - tr.b₂‖ ‖φ (xstar - δ / 2) - tr.b₂‖)
        (min ‖φ (xstar + 1 + δ / 2) - tr.b₂‖ ‖φ (xstar + 1 - δ / 2) - tr.b₂‖) ≤
        ‖φ (xstar - δ / 2) - tr.b₂‖ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    linarith [hρminus, h3]
  have hFout_plus : ∀ m : ℕ, N₁ ≤ m →
      ∃ z ∈ Work.EL.F c '' (φ '' Set.Ioo xstar (xstar + δ)), z ∉ closure (tr.Δ m) := by
    intro m hm
    refine ⟨φ (xstar + 1 + δ / 2), ?_, notMem_closure_of (hN₁ m hm) ?_⟩
    · rw [hFplus_eq]
      exact ⟨xstar + 1 + δ / 2, ⟨by linarith, by linarith⟩, rfl⟩
    · rw [dist_eq_norm]
      have h3 : min (min ‖φ (xstar + δ / 2) - tr.b₂‖ ‖φ (xstar - δ / 2) - tr.b₂‖)
          (min ‖φ (xstar + 1 + δ / 2) - tr.b₂‖ ‖φ (xstar + 1 - δ / 2) - tr.b₂‖) ≤
          ‖φ (xstar + 1 + δ / 2) - tr.b₂‖ :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      linarith [hρFplus, h3]
  have hFout_minus : ∀ m : ℕ, N₁ ≤ m →
      ∃ z ∈ Work.EL.F c '' (φ '' Set.Ioo (xstar - δ) xstar), z ∉ closure (tr.Δ m) := by
    intro m hm
    refine ⟨φ (xstar + 1 - δ / 2), ?_, notMem_closure_of (hN₁ m hm) ?_⟩
    · rw [hFminus_eq]
      exact ⟨xstar + 1 - δ / 2, ⟨by linarith, by linarith⟩, rfl⟩
    · rw [dist_eq_norm]
      have h3 : min (min ‖φ (xstar + δ / 2) - tr.b₂‖ ‖φ (xstar - δ / 2) - tr.b₂‖)
          (min ‖φ (xstar + 1 + δ / 2) - tr.b₂‖ ‖φ (xstar + 1 - δ / 2) - tr.b₂‖) ≤
          ‖φ (xstar + 1 - δ / 2) - tr.b₂‖ :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      linarith [hρFminus, h3]
  have hmeet_plus : ∀ m : ℕ, ∃ z ∈ φ '' Set.Ioo xstar (xstar + δ), z ∈ tr.Δ m := by
    intro m
    obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.mp (tr.isOpen_Δ m) tr.b₂ (tr.b2_mem_Δ m)
    have hρsub' : Metric.ball (φ xstar) ρ ⊆ tr.Δ m := by rw [← hb₂φ] at hρsub; exact hρsub
    have hcontφ : ∀ᶠ t in 𝓝 xstar, φ t ∈ Metric.ball (φ xstar) ρ :=
      hφcont.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hρpos)
    obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hcontφ
    refine ⟨φ (xstar + min ε δ / 2), ⟨xstar + min ε δ / 2,
      ⟨by have := lt_min hεpos hδpos; linarith,
       by have := min_le_right ε δ; linarith⟩, rfl⟩, hρsub' (hε ?_)⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have h1 : min ε δ ≤ ε := min_le_left _ _
    have h2 : 0 < min ε δ := lt_min hεpos hδpos
    constructor <;> linarith
  have hmeet_minus : ∀ m : ℕ, ∃ z ∈ φ '' Set.Ioo (xstar - δ) xstar, z ∈ tr.Δ m := by
    intro m
    obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.mp (tr.isOpen_Δ m) tr.b₂ (tr.b2_mem_Δ m)
    have hρsub' : Metric.ball (φ xstar) ρ ⊆ tr.Δ m := by rw [← hb₂φ] at hρsub; exact hρsub
    have hcontφ : ∀ᶠ t in 𝓝 xstar, φ t ∈ Metric.ball (φ xstar) ρ :=
      hφcont.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hρpos)
    obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hcontφ
    refine ⟨φ (xstar - min ε δ / 2), ⟨xstar - min ε δ / 2,
      ⟨by have := min_le_right ε δ; linarith,
       by have := lt_min hεpos hδpos; linarith⟩, rfl⟩, hρsub' (hε ?_)⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have h1 : min ε δ ≤ ε := min_le_left _ _
    have h2 : 0 < min ε δ := lt_min hεpos hδpos
    constructor <;> linarith
  have hFmeet_plus : ∀ m : ℕ,
      ∃ z ∈ Work.EL.F c '' (φ '' Set.Ioo xstar (xstar + δ)), z ∈ tr.Δ m := by
    intro m
    obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.mp (tr.isOpen_Δ m) tr.b₂ (tr.b2_mem_Δ m)
    have hρsub' : Metric.ball (φ (xstar + 1)) ρ ⊆ tr.Δ m := by rw [← hφx1] at hρsub; exact hρsub
    have hcontφ : ∀ᶠ t in 𝓝 (xstar + 1), φ t ∈ Metric.ball (φ (xstar + 1)) ρ :=
      hφcont.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hρpos)
    obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hcontφ
    refine ⟨φ (xstar + 1 + min ε δ / 2), ?_, hρsub' (hε ?_)⟩
    · rw [hFplus_eq]
      exact ⟨xstar + 1 + min ε δ / 2,
        ⟨by have := lt_min hεpos hδpos; linarith, by have := min_le_right ε δ; linarith⟩, rfl⟩
    · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      have h1 : min ε δ ≤ ε := min_le_left _ _
      have h2 : 0 < min ε δ := lt_min hεpos hδpos
      constructor <;> linarith
  have hFmeet_minus : ∀ m : ℕ,
      ∃ z ∈ Work.EL.F c '' (φ '' Set.Ioo (xstar - δ) xstar), z ∈ tr.Δ m := by
    intro m
    obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.mp (tr.isOpen_Δ m) tr.b₂ (tr.b2_mem_Δ m)
    have hρsub' : Metric.ball (φ (xstar + 1)) ρ ⊆ tr.Δ m := by rw [← hφx1] at hρsub; exact hρsub
    have hcontφ : ∀ᶠ t in 𝓝 (xstar + 1), φ t ∈ Metric.ball (φ (xstar + 1)) ρ :=
      hφcont.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hρpos)
    obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hcontφ
    refine ⟨φ (xstar + 1 - min ε δ / 2), ?_, hρsub' (hε ?_)⟩
    · rw [hFminus_eq]
      exact ⟨xstar + 1 - min ε δ / 2,
        ⟨by have := min_le_right ε δ; linarith, by have := lt_min hεpos hδpos; linarith⟩, rfl⟩
    · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      have h1 : min ε δ ≤ ε := min_le_left _ _
      have h2 : 0 < min ε δ := lt_min hεpos hδpos
      constructor <;> linarith
  have hcutXm : ∀ m : ℕ, N₁ ≤ m → tr.cut X m ∈ φ '' Set.Ioo xstar (xstar + δ) :=
    fun m hm => Work.ELRig.B2Data.cut_mem_of tr hσplusK hσplusconn hX
      (hmeet_plus m) (hout_plus m hm)
  have hcutYm : ∀ m : ℕ, N₁ ≤ m → tr.cut Y m ∈ φ '' Set.Ioo (xstar - δ) xstar :=
    fun m hm => Work.ELRig.B2Data.cut_mem_of tr hσminusK hσminusconn hY
      (hmeet_minus m) (hout_minus m hm)
  -- Step 8: the crossing points at the level `n = max N₁ N₂`
  set n : ℕ := max N₁ N₂ with hndef
  have hnN₁ : N₁ ≤ n := le_max_left _ _
  have hnN₂ : N₂ ≤ n := le_max_right _ _
  have hcutX : tr.cut X n ∈ φ '' Set.Ioo xstar (xstar + δ) := hcutXm n hnN₁
  have hcutY : tr.cut Y n ∈ φ '' Set.Ioo (xstar - δ) xstar := hcutYm n hnN₁
  -- Step 9: the arms of the two halves are different
  have hXY : X ≠ Y := by
    intro hXY
    obtain ⟨s, hs, hs'⟩ := hcutX
    obtain ⟨t, ht, ht'⟩ := hcutY
    have h1 : s ∈ Set.Ioo (xstar - δ) (xstar + δ) := ⟨by linarith [hs.1], hs.2⟩
    have h2 : t ∈ Set.Ioo (xstar - δ) (xstar + δ) := ⟨ht.1, by linarith [ht.2]⟩
    have h3 : s = t := hφinj h1 h2 (by rw [hs', ht', hXY])
    linarith [hs.1, ht.2, h3]
  -- Step 10: the arms of the images under `F`
  obtain ⟨W₁, hW₁⟩ : ∃ W₁ : Work.EL.ArmIdx,
      Work.EL.F c '' (φ '' Set.Ioo xstar (xstar + δ)) ⊆ Work.EL.armOf tr.tripod W₁ := by
    rcases Work.ELRig.B2Data.subset_arm_of tr hFplusconn hFplus_av with h | h | h
    · exact ⟨Work.EL.ArmIdx.A, h⟩
    · exact ⟨Work.EL.ArmIdx.B, h⟩
    · exact ⟨Work.EL.ArmIdx.C, h⟩
  obtain ⟨W₂, hW₂⟩ : ∃ W₂ : Work.EL.ArmIdx,
      Work.EL.F c '' (φ '' Set.Ioo (xstar - δ) xstar) ⊆ Work.EL.armOf tr.tripod W₂ := by
    rcases Work.ELRig.B2Data.subset_arm_of tr hFminusconn hFminus_av with h | h | h
    · exact ⟨Work.EL.ArmIdx.A, h⟩
    · exact ⟨Work.EL.ArmIdx.B, h⟩
    · exact ⟨Work.EL.ArmIdx.C, h⟩
  -- the rotation of the cut points identifies these arms
  have hrotX : Work.EL.ArmIdx.rot X = W₁ := by
    have h1 : Work.EL.F c (tr.cut X n) ∈ Work.EL.armOf tr.tripod (Work.EL.ArmIdx.rot X) :=
      hN₂ X n hnN₂
    have h2 : Work.EL.F c (tr.cut X n) ∈ Work.EL.armOf tr.tripod W₁ :=
      hW₁ ⟨tr.cut X n, hcutX, rfl⟩
    by_contra hne
    exact (Set.disjoint_left.mp (armOf_disjoint tr.tripod hne) h1) h2
  have hrotY : Work.EL.ArmIdx.rot Y = W₂ := by
    have h1 : Work.EL.F c (tr.cut Y n) ∈ Work.EL.armOf tr.tripod (Work.EL.ArmIdx.rot Y) :=
      hN₂ Y n hnN₂
    have h2 : Work.EL.F c (tr.cut Y n) ∈ Work.EL.armOf tr.tripod W₂ :=
      hW₂ ⟨tr.cut Y n, hcutY, rfl⟩
    by_contra hne
    exact (Set.disjoint_left.mp (armOf_disjoint tr.tripod hne) h1) h2
  have hcutFXm : ∀ m : ℕ, N₁ ≤ m → N₂ ≤ m →
      tr.cut (Work.EL.ArmIdx.rot X) m ∈ Work.EL.F c '' (φ '' Set.Ioo xstar (xstar + δ)) := by
    intro m hm1 hm2
    refine Work.ELRig.B2Data.cut_mem_of tr hFplusK hFplusconn ?_ (hFmeet_plus m)
      (hFout_plus m hm1)
    rw [hrotX]; exact hW₁
  have hcutFYm : ∀ m : ℕ, N₁ ≤ m → N₂ ≤ m →
      tr.cut (Work.EL.ArmIdx.rot Y) m ∈ Work.EL.F c '' (φ '' Set.Ioo (xstar - δ) xstar) := by
    intro m hm1 hm2
    refine Work.ELRig.B2Data.cut_mem_of tr hFminusK hFminusconn ?_ (hFmeet_minus m)
      (hFout_minus m hm1)
    rw [hrotY]; exact hW₂
  -- Step 11: a common arm
  obtain ⟨Z, hZX, hZrot⟩ := exists_common_arm hXY
  -- Step 12: parameter pairs on both arcs at every large level
  have hpair : ∀ m : ℕ, N₁ ≤ m → N₂ ≤ m → ∃ p : ℝ × ℝ,
      p.1 ∈ Set.Ioo (xstar - δ) (xstar + δ) ∧ p.2 ∈ Set.Ioo (xstar - δ) (xstar + δ) ∧
      φ p.2 = tr.cut Z m ∧ Work.EL.F c (φ p.1) = tr.cut Z m := by
    intro m hm1 hm2
    have hs : ∃ s ∈ Set.Ioo (xstar - δ) (xstar + δ), φ s = tr.cut Z m := by
      rcases hZX with h | h
      · rw [h]
        obtain ⟨s, hs, hsφ⟩ := hcutXm m hm1
        exact ⟨s, ⟨by linarith [hs.1], hs.2⟩, hsφ⟩
      · rw [h]
        obtain ⟨s, hs, hsφ⟩ := hcutYm m hm1
        exact ⟨s, ⟨hs.1, by linarith [hs.2]⟩, hsφ⟩
    have ht : ∃ t ∈ Set.Ioo (xstar - δ) (xstar + δ), Work.EL.F c (φ t) = tr.cut Z m := by
      rcases hZrot with h | h
      · have h' : tr.cut Z m = tr.cut (Work.EL.ArmIdx.rot X) m := by rw [h]
        obtain ⟨w, hw, hwF⟩ := hcutFXm m hm1 hm2
        obtain ⟨t, ht, htφ⟩ := hw
        exact ⟨t, ⟨by linarith [ht.1], ht.2⟩, by rw [htφ, hwF, ← h']⟩
      · have h' : tr.cut Z m = tr.cut (Work.EL.ArmIdx.rot Y) m := by rw [h]
        obtain ⟨w, hw, hwF⟩ := hcutFYm m hm1 hm2
        obtain ⟨t, ht, htφ⟩ := hw
        exact ⟨t, ⟨ht.1, by linarith [ht.2]⟩, by rw [htφ, hwF, ← h']⟩
    obtain ⟨s, hs, hsφ⟩ := hs
    obtain ⟨t, ht, htF⟩ := ht
    exact ⟨(t, s), ht, hs, hsφ, htF⟩
  -- Step 13: the sequence of parameters and its limit
  let q : ℕ → ℝ × ℝ := fun k => Classical.choose
    (hpair (max N₁ N₂ + k) (le_trans (le_max_left _ _) (Nat.le_add_right _ _))
      (le_trans (le_max_right _ _) (Nat.le_add_right _ _)))
  have hq : ∀ k : ℕ, (q k).1 ∈ Set.Ioo (xstar - δ) (xstar + δ) ∧
      (q k).2 ∈ Set.Ioo (xstar - δ) (xstar + δ) ∧
      φ (q k).2 = tr.cut Z (max N₁ N₂ + k) ∧
      Work.EL.F c (φ (q k).1) = tr.cut Z (max N₁ N₂ + k) := fun k => Classical.choose_spec
    (hpair (max N₁ N₂ + k) (le_trans (le_max_left _ _) (Nat.le_add_right _ _))
      (le_trans (le_max_right _ _) (Nat.le_add_right _ _)))
  have hcut_tendsto : Tendsto (fun k : ℕ => tr.cut Z (max N₁ N₂ + k)) atTop (nhds tr.b₂) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨Nε, hNε⟩ := tr.Δ_shrinks (ε / 2) (by linarith)
    refine ⟨Nε, fun k hk => ?_⟩
    have h1 : Nε ≤ max N₁ N₂ + k := le_trans hk (Nat.le_add_left k (max N₁ N₂))
    have h2 : tr.Δ (max N₁ N₂ + k) ⊆ Metric.ball tr.b₂ (ε / 2) := hNε _ h1
    have h3 : tr.cut Z (max N₁ N₂ + k) ∈ closure (tr.Δ (max N₁ N₂ + k)) :=
      frontier_subset_closure (tr.cut_mem Z (max N₁ N₂ + k)).2
    have h4 : closure (tr.Δ (max N₁ N₂ + k)) ⊆ Metric.closedBall tr.b₂ (ε / 2) :=
      closure_minimal (subset_trans h2 Metric.ball_subset_closedBall) Metric.isClosed_closedBall
    have h5 : dist (tr.cut Z (max N₁ N₂ + k)) tr.b₂ ≤ ε / 2 := Metric.mem_closedBall.mp (h4 h3)
    linarith
  have hσbcont : ContinuousAt σb tr.b₂ := by
    have hmem : fl.Ψ ((xstar : ℝ) : ℂ) ∈ Metric.ball (fl.Ψ (((xstar + 1 : ℝ)) : ℂ)) δ₂b := by
      rw [hxstar', hΨx1]
      exact Metric.mem_ball_self hδ₂bpos
    have h := (hσban (fl.Ψ ((xstar : ℝ) : ℂ)) hmem).continuousAt
    rwa [hxstar'] at h
  have hσbb₂ : σb tr.b₂ = (((xstar + 1 : ℝ)) : ℂ) := by
    have hmem : (((xstar + 1 : ℝ)) : ℂ) ∈ Metric.ball (((xstar + 1 : ℝ)) : ℂ) δ₁b :=
      Metric.mem_ball_self hδ₁bpos
    have := hσbleft _ hmem
    rwa [hΨx1] at this
  have ht1_tendsto : Tendsto (fun k : ℕ => (((q k).1 + 1 : ℝ) : ℂ)) atTop
      (nhds (((xstar + 1 : ℝ)) : ℂ)) := by
    have h1 : ∀ k : ℕ, (((q k).1 + 1 : ℝ) : ℂ) = σb (tr.cut Z (max N₁ N₂ + k)) := by
      intro k
      have hk := hq k
      have hmem : (((q k).1 + 1 : ℝ) : ℂ) ∈ Metric.ball (((xstar + 1 : ℝ)) : ℂ) δ₁b := by
        rw [Metric.mem_ball, Complex.isometry_ofReal.dist_eq, Real.dist_eq]
        rw [show ((q k).1 + 1) - (xstar + 1) = (q k).1 - xstar by ring]
        rw [abs_lt]
        exact ⟨by linarith [hk.1.1], lt_trans (by linarith [hk.1.2]) hδδ₁b⟩
      have hcast : (((q k).1 : ℝ) : ℂ) + 1 = (((q k).1 + 1 : ℝ) : ℂ) := by push_cast; ring
      have h2 : tr.cut Z (max N₁ N₂ + k) = fl.Ψ ((((q k).1 + 1 : ℝ)) : ℂ) := by
        rw [← hk.2.2.2, hφshift]
      rw [h2, hσbleft _ hmem]
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δc, hδcpos, hδc⟩ := Metric.continuousAt_iff.mp hσbcont ε hε
    obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hcut_tendsto δc hδcpos
    refine ⟨K, fun k hk => ?_⟩
    rw [h1 k, ← hσbb₂]
    exact hδc (hK k hk)
  have ht_tendsto : Tendsto (fun k : ℕ => (q k).1) atTop (nhds xstar) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp ht1_tendsto ε hε
    refine ⟨K, fun k hk => ?_⟩
    have h1 := hK k hk
    rw [Complex.isometry_ofReal.dist_eq, Real.dist_eq] at h1
    rw [Real.dist_eq]
    have h2 : (q k).1 + 1 - (xstar + 1) = (q k).1 - xstar := by ring
    rwa [h2] at h1
  have hqne : ∀ k : ℕ, (q k).1 ≠ xstar := by
    intro k hk
    have h1 : tr.cut Z (max N₁ N₂ + k) = tr.b₂ := by
      rw [← (hq k).2.2.2, hk, hφshift, hφx1]
    have h2 : tr.b₂ ∉ interior (tr.Δ (max N₁ N₂ + k)) := by
      rw [← h1]; exact (tr.cut_mem Z (max N₁ N₂ + k)).2.2
    have h3 : tr.b₂ ∈ interior (tr.Δ (max N₁ N₂ + k)) := by
      rw [(tr.isOpen_Δ _).interior_eq]; exact tr.b2_mem_Δ _
    exact h2 h3
  -- Step 14: the real-analytic identity
  let τ : ℂ → ℂ := fun w => σa (fl.Ψ (w + 1))
  have hτan : AnalyticOnNhd ℂ τ (Metric.ball ((xstar : ℝ) : ℂ) η₁) := by
    intro w hw
    have hw1 : w + 1 ∈ Metric.ball (((xstar + 1 : ℝ)) : ℂ) η₁ := by
      rw [Metric.mem_ball] at hw ⊢
      rw [show (((xstar + 1 : ℝ)) : ℂ) = ((xstar : ℝ) : ℂ) + 1 by push_cast; ring]
      rwa [dist_add_right]
    have h1 : fl.Ψ (w + 1) ∈ Metric.ball tr.b₂ δ₂a := hη₁ hw1
    have h2 : fl.Ψ (w + 1) ∈ Metric.ball (fl.Ψ ((xstar : ℝ) : ℂ)) δ₂a := by
      rw [hxstar']; exact h1
    have hσ : AnalyticAt ℂ σa (fl.Ψ (w + 1)) := hσaan _ h2
    have hΨ : AnalyticAt ℂ fl.Ψ (w + 1) := fl.Ψ_diff.analyticAt (w + 1)
    change AnalyticAt ℂ (fun v : ℂ => σa (fl.Ψ (v + 1))) w
    fun_prop
  have hτreal_seq : ∀ k : ℕ, τ (((q k).1 : ℝ) : ℂ) = star (τ (((q k).1 : ℝ) : ℂ)) := by
    intro k
    have hk := hq k
    have hmem : ((q k).2 : ℂ) ∈ Metric.ball ((xstar : ℝ) : ℂ) δ₁a := by
      rw [Metric.mem_ball, Complex.isometry_ofReal.dist_eq, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hk.2.1.1], lt_trans (by linarith [hk.2.1.2]) hδδ₁a⟩
    have h1 : τ (((q k).1 : ℝ) : ℂ) = ((q k).2 : ℂ) := by
      have hcast : (((q k).1 : ℝ) : ℂ) + 1 = (((q k).1 + 1 : ℝ) : ℂ) := by push_cast; ring
      have h2 : φ ((q k).1 + 1) = φ ((q k).2) := by
        rw [← hφshift (q k).1, hk.2.2.2, hk.2.2.1]
      simp only [φ] at h2
      simp only [τ, hcast]
      rw [h2]
      exact hσaleft _ hmem
    rw [h1]
    exact (Complex.conj_ofReal _).symm
  have hfreq : ∃ᶠ t : ℝ in nhdsWithin xstar {xstar}ᶜ,
      τ (t : ℂ) = star (τ (t : ℂ)) :=
    frequently_of_tendsto_ne ht_tendsto hqne hτreal_seq
  have hreal : ∃ ε > 0, ∀ t : ℝ, |t - xstar| < ε → τ (t : ℂ) = star (τ (t : ℂ)) :=
    eqOn_real_of_frequently_real hη₁pos hτan hfreq
  -- Step 12: the final contradiction
  obtain ⟨εr, hεrpos, hεr⟩ := hreal
  have hτx : τ (((xstar : ℝ)) : ℂ) = ((xstar : ℝ) : ℂ) := by
    simp only [τ]
    have hmem : ((xstar : ℝ) : ℂ) ∈ Metric.ball ((xstar : ℝ) : ℂ) δ₁a :=
      Metric.mem_ball_self hδ₁apos
    rw [show fl.Ψ (((xstar : ℝ) : ℂ) + 1) = tr.b₂ by
      rw [show ((xstar : ℝ) : ℂ) + 1 = (((xstar + 1 : ℝ)) : ℂ) by push_cast; ring]
      exact hΨx1]
    rw [← hxstar']
    exact hσaleft _ hmem
  have hτcont : ContinuousAt τ ((xstar : ℝ) : ℂ) :=
    (hτan _ (Metric.mem_ball_self hη₁pos)).continuousAt
  obtain ⟨εp, hεppos, hεp⟩ := Metric.continuousAt_iff.mp hτcont δ hδpos
  set εz : ℝ := min (min εr εp) (min η₁ δ) / 2 with hεzdef
  have hεzpos : 0 < εz := by rw [hεzdef]; positivity
  have hεzεr : εz < εr := by
    rw [hεzdef]
    exact lt_of_lt_of_le (div_lt_self (by positivity) (by norm_num))
      (le_trans (min_le_left _ _) (min_le_left _ _))
  have hεzεp : εz < εp := by
    rw [hεzdef]
    exact lt_of_lt_of_le (div_lt_self (by positivity) (by norm_num))
      (le_trans (min_le_left _ _) (min_le_right _ _))
  have hεzη : εz < η₁ := by
    rw [hεzdef]
    exact lt_of_lt_of_le (div_lt_self (by positivity) (by norm_num))
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεzδ : εz < δ := by
    rw [hεzdef]
    exact lt_of_lt_of_le (div_lt_self (by positivity) (by norm_num))
      (le_trans (min_le_right _ _) (min_le_right _ _))
  -- the points of `σ` near `b₂` map into the two rotated arms
  have hrotXmem : Work.EL.ArmIdx.rot X = X ∨ Work.EL.ArmIdx.rot X = Y := by
    have ht1 : xstar < xstar + εz / 2 := by linarith
    have ht2 : xstar + εz / 2 < xstar + δ := by linarith
    have htz : |xstar + εz / 2 - xstar| < εz := by rw [abs_lt]; constructor <;> linarith
    have hrt : τ (((xstar + εz / 2 : ℝ)) : ℂ) =
        star (τ (((xstar + εz / 2 : ℝ)) : ℂ)) :=
      hεr _ (lt_of_lt_of_le htz (le_of_lt hεzεr))
    have him : (τ (((xstar + εz / 2 : ℝ)) : ℂ)).im = 0 :=
      (Complex.conj_eq_iff_im).mp hrt.symm
    set s : ℝ := (τ (((xstar + εz / 2 : ℝ)) : ℂ)).re with hsdef
    have hsτ : τ (((xstar + εz / 2 : ℝ)) : ℂ) = ((s : ℝ) : ℂ) := by
      rw [hsdef]
      exact Complex.ext rfl (by simpa using him)
    have hdist : dist (τ (((xstar + εz / 2 : ℝ)) : ℂ)) (τ ((xstar : ℝ) : ℂ)) < δ := by
      refine hεp ?_
      rw [Complex.isometry_ofReal.dist_eq, Real.dist_eq]
      exact lt_of_lt_of_le htz (le_of_lt hεzεp)
    have hsbound : |s - xstar| < δ := by
      rw [hτx, hsτ] at hdist
      rwa [Complex.isometry_ofReal.dist_eq, Real.dist_eq] at hdist
    have hsI : s ∈ Set.Ioo (xstar - δ) (xstar + δ) := by
      have h := (abs_lt.mp hsbound)
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    have hA : fl.Ψ ((((xstar + εz / 2: ℝ)) : ℂ) + 1) ∈ Metric.ball tr.b₂ δ₂a := by
      refine hη₁ ?_
      rw [show ((xstar + εz / 2 : ℝ) : ℂ) + 1 = ((xstar + εz / 2 + 1 : ℝ) : ℂ) by
        push_cast; ring]
      rw [Metric.mem_ball, Complex.isometry_ofReal.dist_eq, Real.dist_eq, abs_lt]
      exact ⟨by linarith, lt_trans (by linarith) hεzη⟩
    have hA2 : fl.Ψ ((((xstar + εz / 2: ℝ)) : ℂ) + 1) ∈ Metric.ball (fl.Ψ ((xstar : ℝ) : ℂ)) δ₂a := by
      rw [hxstar']; exact hA
    have hFs : Work.EL.F c (φ (xstar + εz / 2)) = φ s := by
      have hD : fl.Ψ (τ (((xstar + εz / 2: ℝ)) : ℂ)) = φ s := by
        rw [hsτ]
      calc Work.EL.F c (φ (xstar + εz / 2)) = φ (xstar + εz / 2 + 1) := hφshift _
        _ = fl.Ψ ((((xstar + εz / 2: ℝ)) : ℂ) + 1) := by
              show fl.Ψ ((((xstar + εz / 2) + 1 : ℝ) : ℂ)) = fl.Ψ ((((xstar + εz / 2: ℝ)) : ℂ) + 1)
              congr 1
              push_cast
              ring
        _ = fl.Ψ (τ (((xstar + εz / 2: ℝ)) : ℂ)) :=
              (hσarght (fl.Ψ ((((xstar + εz / 2: ℝ)) : ℂ) + 1)) hA2).symm
        _ = φ s := hD
    have hne_b₂ : φ s ≠ tr.b₂ := by
      rw [← hFs, hφshift, ← hφx1]
      intro hcon
      have htI : xstar + εz / 2 + 1 ∈ Set.Ioo (xstar + 1 - δ) (xstar + 1 + δ) :=
        ⟨by linarith, by linarith⟩
      have hxI : xstar + 1 ∈ Set.Ioo (xstar + 1 - δ) (xstar + 1 + δ) :=
        ⟨by linarith [hδpos], by linarith [hδpos]⟩
      have := hφinj₁ htI hxI hcon
      linarith
    have harmX : φ s ∈ Work.EL.armOf tr.tripod (Work.EL.ArmIdx.rot X) := by
      have harm : Work.EL.F c '' (φ '' Set.Ioo xstar (xstar + δ)) ⊆
          Work.EL.armOf tr.tripod (Work.EL.ArmIdx.rot X) := by
        rw [hrotX]; exact hW₁
      rw [← hFs]
      exact harm ⟨φ (xstar + εz / 2), ⟨xstar + εz / 2, ⟨ht1, ht2⟩, rfl⟩, rfl⟩
    have hσsarm : φ s ∈ Work.EL.armOf tr.tripod X ∪ Work.EL.armOf tr.tripod Y :=
      (hσ_le ⟨s, hsI, rfl⟩).resolve_right (fun h => hne_b₂ h)
    rcases hσsarm with h | h
    · left
      by_contra hne'
      exact (Set.disjoint_left.mp (armOf_disjoint tr.tripod hne') harmX) h
    · right
      by_contra hne'
      exact (Set.disjoint_left.mp (armOf_disjoint tr.tripod hne') harmX) h
  have hrotYmem : Work.EL.ArmIdx.rot Y = X ∨ Work.EL.ArmIdx.rot Y = Y := by
    have ht1 : xstar - δ < xstar - εz / 2 := by linarith
    have ht2 : xstar - εz / 2 < xstar := by linarith
    have htz : |xstar - εz / 2 - xstar| < εz := by rw [abs_lt]; constructor <;> linarith
    have hrt : τ (((xstar - εz / 2 : ℝ)) : ℂ) =
        star (τ (((xstar - εz / 2 : ℝ)) : ℂ)) :=
      hεr _ (lt_of_lt_of_le htz (le_of_lt hεzεr))
    have him : (τ (((xstar - εz / 2 : ℝ)) : ℂ)).im = 0 :=
      (Complex.conj_eq_iff_im).mp hrt.symm
    set s : ℝ := (τ (((xstar - εz / 2 : ℝ)) : ℂ)).re with hsdef
    have hsτ : τ (((xstar - εz / 2 : ℝ)) : ℂ) = ((s : ℝ) : ℂ) := by
      rw [hsdef]
      exact Complex.ext rfl (by simpa using him)
    have hdist : dist (τ (((xstar - εz / 2 : ℝ)) : ℂ)) (τ ((xstar : ℝ) : ℂ)) < δ := by
      refine hεp ?_
      rw [Complex.isometry_ofReal.dist_eq, Real.dist_eq]
      exact lt_of_lt_of_le htz (le_of_lt hεzεp)
    have hsbound : |s - xstar| < δ := by
      rw [hτx, hsτ] at hdist
      rwa [Complex.isometry_ofReal.dist_eq, Real.dist_eq] at hdist
    have hsI : s ∈ Set.Ioo (xstar - δ) (xstar + δ) := by
      have h := (abs_lt.mp hsbound)
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    have hA : fl.Ψ ((((xstar - εz / 2: ℝ)) : ℂ) + 1) ∈ Metric.ball tr.b₂ δ₂a := by
      refine hη₁ ?_
      rw [show ((xstar - εz / 2 : ℝ) : ℂ) + 1 = ((xstar - εz / 2 + 1 : ℝ) : ℂ) by
        push_cast; ring]
      rw [Metric.mem_ball, Complex.isometry_ofReal.dist_eq, Real.dist_eq, abs_lt]
      exact ⟨by linarith, lt_trans (by linarith) hεzη⟩
    have hA2 : fl.Ψ ((((xstar - εz / 2: ℝ)) : ℂ) + 1) ∈ Metric.ball (fl.Ψ ((xstar : ℝ) : ℂ)) δ₂a := by
      rw [hxstar']; exact hA
    have hFs : Work.EL.F c (φ (xstar - εz / 2)) = φ s := by
      have hD : fl.Ψ (τ (((xstar - εz / 2: ℝ)) : ℂ)) = φ s := by
        rw [hsτ]
      calc Work.EL.F c (φ (xstar - εz / 2)) = φ (xstar - εz / 2 + 1) := hφshift _
        _ = fl.Ψ ((((xstar - εz / 2: ℝ)) : ℂ) + 1) := by
              show fl.Ψ ((((xstar - εz / 2) + 1 : ℝ) : ℂ)) = fl.Ψ ((((xstar - εz / 2: ℝ)) : ℂ) + 1)
              congr 1
              push_cast
              ring
        _ = fl.Ψ (τ (((xstar - εz / 2: ℝ)) : ℂ)) :=
              (hσarght (fl.Ψ ((((xstar - εz / 2: ℝ)) : ℂ) + 1)) hA2).symm
        _ = φ s := hD
    have hne_b₂ : φ s ≠ tr.b₂ := by
      rw [← hFs, hφshift, ← hφx1]
      intro hcon
      have htI : xstar - εz / 2 + 1 ∈ Set.Ioo (xstar + 1 - δ) (xstar + 1 + δ) :=
        ⟨by linarith, by linarith⟩
      have hxI : xstar + 1 ∈ Set.Ioo (xstar + 1 - δ) (xstar + 1 + δ) :=
        ⟨by linarith [hδpos], by linarith [hδpos]⟩
      have := hφinj₁ htI hxI hcon
      linarith
    have harmY : φ s ∈ Work.EL.armOf tr.tripod (Work.EL.ArmIdx.rot Y) := by
      have harm : Work.EL.F c '' (φ '' Set.Ioo (xstar - δ) xstar) ⊆
          Work.EL.armOf tr.tripod (Work.EL.ArmIdx.rot Y) := by
        rw [hrotY]; exact hW₂
      rw [← hFs]
      exact harm ⟨φ (xstar - εz / 2), ⟨xstar - εz / 2, ⟨ht1, ht2⟩, rfl⟩, rfl⟩
    have hσsarm : φ s ∈ Work.EL.armOf tr.tripod X ∪ Work.EL.armOf tr.tripod Y :=
      (hσ_le ⟨s, hsI, rfl⟩).resolve_right (fun h => hne_b₂ h)
    rcases hσsarm with h | h
    · left
      by_contra hne'
      exact (Set.disjoint_left.mp (armOf_disjoint tr.tripod hne') harmY) h
    · right
      by_contra hne'
      exact (Set.disjoint_left.mp (armOf_disjoint tr.tripod hne') harmY) h
  rcases hrotXmem with h | h
  · exact absurd h (Work.EL.ArmIdx.rot_ne_self X)
  · rcases hrotYmem with h' | h'
    · exact rot_no_two_cycle hXY h h'
    · exact absurd h' (Work.EL.ArmIdx.rot_ne_self Y)

end Work.ELRig
