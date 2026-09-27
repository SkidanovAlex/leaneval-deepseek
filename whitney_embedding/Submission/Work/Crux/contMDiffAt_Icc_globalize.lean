import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Crux.globalize_oneDim

/-!
# Globalising a map that is `C^∞` at every point of `[0,1]`

Given `P : ℝ → M` into a smooth manifold `M` which is `C^∞` at every point of `[0,1]` in the
sense of `ContMDiffAt` (pointwise!), we produce a globally `C^∞` map `P'` agreeing with `P` on
`[0,1]`.

Note that the hypothesis is genuinely pointwise: `ContMDiffAt _ ∞` is *not* a local condition, so
it does not give a neighbourhood of `[0,1]` on which `P` is smooth (see
`Submission/Work/Isotopy/contDiffAt_infty_not_locally_smooth.lean`).  The construction therefore
uses Borel's theorem (`exists_contDiff_iteratedDeriv`) at the two endpoints, together with the
one-sided gluing lemma `exists_contDiff_eqOn_Ico_of_contDiffAt` from `globalize_oneDim`.
-/

namespace Work.Crux

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

theorem contMDiffAt_Icc_globalize {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M] [T2Space M]
    [SecondCountableTopology M]
    {P : ℝ → M}
    (hP : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → ContMDiffAt Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder P t) :
    ∃ P' : ℝ → M, ContMDiff Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder P' ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → P' t = P t) := by
  classical
  -- abbreviations and the two charts
  let J : ModelWithCorners ℝ ℝ ℝ := modelWithCornersSelf ℝ ℝ
  let E := EuclideanSpace ℝ (Fin n)
  let I : ModelWithCorners ℝ E E := modelWithCornersSelf ℝ E
  let H := EuclideanSpace ℝ (Fin n)
  let e : PartialEquiv M E := extChartAt I (P 0)
  let e₁ : PartialEquiv M E := extChartAt I (P 1)
  have hP0 : ContMDiffAt Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder P 0 :=
    hP 0 (by simp [Set.mem_Icc])
  have hP1 : ContMDiffAt Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder P 1 :=
    hP 1 (by simp [Set.mem_Icc])
  -- radii around `0` and `1` on which `P` stays in the chart source
  obtain ⟨δ₀, hδ₀pos, hδ₀le, hδ₀sub⟩ :
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ x : ℝ, |x| < δ₀ → P x ∈ e.source := by
    have hcont0 : ContinuousAt P 0 := hP0.continuousAt
    have hmem : P ⁻¹' e.source ∈ 𝓝 (0:ℝ) :=
      hcont0.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) (x := P 0))
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hmem
    refine ⟨min δ 1 / 2, by positivity, by linarith [min_le_right δ 1], ?_⟩
    intro x hx
    apply hδsub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    have hle : min δ 1 / 2 ≤ δ / 2 := by
      have := min_le_left δ 1; linarith
    linarith [abs_nonneg x]
  obtain ⟨δ₁, hδ₁pos, hδ₁le, hδ₁sub⟩ :
      ∃ δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ 1 ∧ ∀ x : ℝ, |x - 1| < δ₁ → P x ∈ e₁.source := by
    have hcont1 : ContinuousAt P 1 := hP1.continuousAt
    have hmem : P ⁻¹' e₁.source ∈ 𝓝 (1:ℝ) :=
      hcont1.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) (x := P 1))
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hmem
    refine ⟨min δ 1 / 2, by positivity, by linarith [min_le_right δ 1], ?_⟩
    intro x hx
    apply hδsub
    rw [Metric.mem_ball, Real.dist_eq]
    have hle : min δ 1 / 2 ≤ δ / 2 := by
      have := min_le_left δ 1; linarith
    linarith [abs_nonneg (x - 1)]
  -- the chart expressions
  let F : ℝ → E := fun x => e (P x)
  let F₁ : ℝ → E := fun x => e₁ (P x)
  -- target neighbourhoods
  have hP0src : P 0 ∈ e.source := mem_of_mem_nhds (extChartAt_source_mem_nhds (I := I) (x := P 0))
  have hP1src : P 1 ∈ e₁.source := mem_of_mem_nhds (extChartAt_source_mem_nhds (I := I) (x := P 1))
  obtain ⟨ε₀, hε₀pos, hε₀sub⟩ : ∃ ε₀ > 0, Metric.ball (F 0) ε₀ ⊆ e.target :=
    Metric.mem_nhds_iff.mp ((isOpen_extChartAt_target (I := I) (x := P 0)).mem_nhds
      (PartialEquiv.map_source e hP0src))
  obtain ⟨ε₁, hε₁pos, hε₁sub⟩ : ∃ ε₁ > 0, Metric.ball (F₁ 1) ε₁ ⊆ e₁.target :=
    Metric.mem_nhds_iff.mp ((isOpen_extChartAt_target (I := I) (x := P 1)).mem_nhds
      (PartialEquiv.map_source e₁ hP1src))
  -- chart smoothness on its source
  have hchart : ContMDiffOn I (modelWithCornersSelf ℝ E) ((⊤ : ℕ∞) : WithTop ℕ∞) e e.source := by
    rw [show e.source = (chartAt H (P 0)).source from extChartAt_source I (P 0)]
    exact contMDiffOn_extChartAt (I := I) (x := P 0)
  have hchart₁ : ContMDiffOn I (modelWithCornersSelf ℝ E) ((⊤ : ℕ∞) : WithTop ℕ∞)
      e₁ e₁.source := by
    rw [show e₁.source = (chartAt H (P 1)).source from extChartAt_source I (P 1)]
    exact contMDiffOn_extChartAt (I := I) (x := P 1)
  -- `F` is `C^∞` at `0` and on `(0,δ₀)`
  have hF0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F 0 := by
    rw [← contMDiffAt_iff_contDiffAt]
    exact ContMDiffAt.comp (0:ℝ) (contMDiffAt_extChartAt (I := I) (x := P 0)) hP0
  have hFr : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (Set.Ioo 0 δ₀) := by
    have hPon : ContMDiffOn J (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder P (Set.Ioo 0 δ₀) := by
      intro x hx
      rw [Set.mem_Ioo] at hx
      exact (hP x ⟨hx.1.le, by linarith [hx.2, hδ₀le]⟩).contMDiffWithinAt
    have hcomp : ContMDiffOn J (modelWithCornersSelf ℝ E)
        ((⊤ : ℕ∞) : WithTop ℕ∞) (e ∘ P) (Set.Ioo 0 δ₀) :=
      hchart.comp hPon (fun x hx => by
        rw [Set.mem_Ioo] at hx
        exact hδ₀sub x (by rw [abs_of_pos hx.1]; linarith [hx.2]))
    exact contMDiffOn_iff_contDiffOn.mp (by simpa only [Function.comp_def] using hcomp)
  -- the reflected function `G`
  let G : ℝ → E := fun t => F₁ (1 - t)
  have hF₁on : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁ (Set.Ioo (1 - δ₁) 1) := by
    have hPon : ContMDiffOn J (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder P (Set.Ioo (1 - δ₁) 1) := by
      intro x hx
      rw [Set.mem_Ioo] at hx
      exact (hP x ⟨by linarith [hx.1, hδ₁le], hx.2.le⟩).contMDiffWithinAt
    have hcomp : ContMDiffOn J (modelWithCornersSelf ℝ E)
        ((⊤ : ℕ∞) : WithTop ℕ∞) (e₁ ∘ P) (Set.Ioo (1 - δ₁) 1) :=
      hchart₁.comp hPon (fun x hx => by
        rw [Set.mem_Ioo] at hx
        exact hδ₁sub x (by rw [abs_of_nonpos (by linarith [hx.2])]; linarith [hx.1]))
    exact contMDiffOn_iff_contDiffOn.mp (by simpa only [Function.comp_def] using hcomp)
  have hF₁1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁ 1 := by
    rw [← contMDiffAt_iff_contDiffAt]
    exact ContMDiffAt.comp (1:ℝ) (contMDiffAt_extChartAt (I := I) (x := P 1)) hP1
  have hG0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G 0 := by
    have hsub : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => 1 - t) 0 := by fun_prop
    have hcomp : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (F₁ ∘ fun t : ℝ => 1 - t) 0 :=
      ContDiffAt.comp (0:ℝ) (by simpa using hF₁1) hsub
    simpa only [Function.comp_def, G] using hcomp
  have hGr : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G (Set.Ioo 0 δ₁) := by
    have hsub : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => 1 - t) (Set.Ioo 0 δ₁) := by
      fun_prop
    have hmaps : Set.MapsTo (fun t : ℝ => 1 - t) (Set.Ioo 0 δ₁) (Set.Ioo (1 - δ₁) 1) := by
      intro t ht
      rw [Set.mem_Ioo] at ht ⊢
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h := hF₁on.comp hsub hmaps
    simpa only [Function.comp_def, G] using h
  -- globalisation at both ends
  obtain ⟨Ψ, hΨsm, hΨeq, hΨbound⟩ :=
    exists_contDiff_eqOn_Ico_of_contDiffAt (E := E) hδ₀pos hF0 hFr hε₀pos
  obtain ⟨ΨG, hΨGsm, hΨGeq, hΨGbound⟩ :=
    exists_contDiff_eqOn_Ico_of_contDiffAt (E := E) hδ₁pos hG0 hGr hε₁pos
  let Ψ₁ : ℝ → E := fun x => ΨG (1 - x)
  have hΨ₁sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ₁ :=
    hΨGsm.comp (by fun_prop)
  have hΨ₁eq : ∀ x ∈ Set.Ioc (1 - δ₁/8) 1, Ψ₁ x = F₁ x := by
    intro x hx
    have hx' : x ∈ Set.Ioc (1 - δ₁/8) 1 := hx
    rw [Set.mem_Ioc] at hx
    have hmem : 1 - x ∈ Set.Ico 0 (δ₁/8) := by
      rw [Set.mem_Ico]
      exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have h := hΨGeq (1 - x) hmem
    have h2 : (1:ℝ) - (1 - x) = x := by ring
    simpa only [Ψ₁, G, h2] using h
  have hΨ₁bound : ∀ x : ℝ, 1 ≤ x → ‖Ψ₁ x - F₁ 1‖ < ε₁ := by
    intro x hx
    have h := hΨGbound (1 - x) (by linarith)
    simpa only [Ψ₁, G, sub_zero] using h
  -- the candidate map
  let P' : ℝ → M := fun x => if x < δ₀/8 then e.symm (Ψ x)
    else if x ≤ 1 - δ₁/8 then P x else e₁.symm (Ψ₁ x)
  have hP'def : ∀ x : ℝ, P' x = if x < δ₀/8 then e.symm (Ψ x)
      else if x ≤ 1 - δ₁/8 then P x else e₁.symm (Ψ₁ x) := fun x => rfl
  -- `P` is smooth on `(0,1)`
  have hPon01 : ContMDiffOn J (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder P (Set.Ioo 0 1) := by
    intro x hx
    rw [Set.mem_Ioo] at hx
    exact (hP x ⟨hx.1.le, hx.2.le⟩).contMDiffWithinAt
  -- smoothness on the left piece
  have hleft : ContMDiffOn J (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder P' (Set.Iio (δ₀/8)) := by
    have hmap : ∀ x ∈ Set.Iio (δ₀/8), Ψ x ∈ e.target := by
      intro x hx
      rw [Set.mem_Iio] at hx
      rcases lt_or_ge x 0 with hx0 | hx0
      · exact hε₀sub (hΨbound x hx0.le)
      · have hxδ : x < δ₀ := by linarith [hx, hδ₀pos]
        have hPsrc : P x ∈ e.source := hδ₀sub x (by rw [abs_of_nonneg hx0]; exact hxδ)
        rw [hΨeq x ⟨hx0, hx⟩]
        exact PartialEquiv.map_source e hPsrc
    have hΨon : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ E)
        ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ (Set.Iio (δ₀/8)) :=
      contMDiffOn_iff_contDiffOn.mpr hΨsm.contDiffOn
    have hcomp : ContMDiffOn J I ((⊤ : ℕ∞) : WithTop ℕ∞)
        (e.symm ∘ Ψ) (Set.Iio (δ₀/8)) :=
      ContMDiffOn.comp (contMDiffOn_extChartAt_symm (I := I) (x := P 0)) hΨon
        (fun x hx => hmap x hx)
    refine ContMDiffOn.congr hcomp (fun x hx => ?_)
    rw [Set.mem_Iio] at hx
    rw [Function.comp_apply, hP'def x, if_pos hx]
  -- smoothness on the right piece
  have hright : ContMDiffOn J (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder P' (Set.Ioi (1 - δ₁/8)) := by
    have hmap : ∀ x ∈ Set.Ioi (1 - δ₁/8), Ψ₁ x ∈ e₁.target := by
      intro x hx
      rw [Set.mem_Ioi] at hx
      rcases lt_or_ge 1 x with hx1 | hx1
      · exact hε₁sub (hΨ₁bound x hx1.le)
      · have hxd : |x - 1| < δ₁ := by
          rw [abs_of_nonpos (by linarith)]
          linarith [hx, hδ₁pos]
        have hPsrc : P x ∈ e₁.source := hδ₁sub x hxd
        rw [hΨ₁eq x ⟨hx, hx1⟩]
        exact PartialEquiv.map_source e₁ hPsrc
    have hΨ₁on : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ E)
        ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ₁ (Set.Ioi (1 - δ₁/8)) :=
      contMDiffOn_iff_contDiffOn.mpr hΨ₁sm.contDiffOn
    have hcomp : ContMDiffOn J I ((⊤ : ℕ∞) : WithTop ℕ∞)
        (e₁.symm ∘ Ψ₁) (Set.Ioi (1 - δ₁/8)) :=
      ContMDiffOn.comp (contMDiffOn_extChartAt_symm (I := I) (x := P 1)) hΨ₁on
        (fun x hx => hmap x hx)
    refine ContMDiffOn.congr hcomp (fun x hx => ?_)
    rw [Set.mem_Ioi] at hx
    rw [Function.comp_apply, hP'def x, if_neg (by linarith [hx, hδ₀pos, hδ₁pos]),
      if_neg (by linarith [hx])]
  -- smoothness on the middle piece: `P' = P` there
  have hmid : ContMDiffOn J (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder P' (Set.Ioo (δ₀/16) (1 - δ₁/16)) := by
    have hPmid : ContMDiffOn J (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder P (Set.Ioo (δ₀/16) (1 - δ₁/16)) :=
      hPon01.mono (fun x hx => by
        rw [Set.mem_Ioo] at hx ⊢
        exact ⟨by linarith [hx.1, hδ₀pos], by linarith [hx.2, hδ₁pos]⟩)
    refine ContMDiffOn.congr hPmid (fun x hx => ?_)
    rw [Set.mem_Ioo] at hx
    rw [hP'def x]
    by_cases h1 : x < δ₀/8
    · rw [if_pos h1, hΨeq x ⟨by linarith [hx.1], h1⟩]
      have hPsrc : P x ∈ e.source :=
        hδ₀sub x (by rw [abs_of_pos (by linarith [hx.1])]; linarith [h1, hδ₀pos])
      show e.symm (e (P x)) = P x
      exact PartialEquiv.left_inv e hPsrc
    · rw [if_neg h1]
      by_cases h2 : x ≤ 1 - δ₁/8
      · rw [if_pos h2]
      · rw [if_neg h2]
        have hx1 : 1 - δ₁/8 < x := lt_of_not_ge h2
        rw [hΨ₁eq x ⟨hx1, by linarith [hx.2, hδ₁pos]⟩]
        have hPsrc : P x ∈ e₁.source := hδ₁sub x (by
          rw [abs_of_nonpos (by linarith [hx.2, hδ₁pos])]
          linarith [hx1, hδ₁pos])
        show e₁.symm (e₁ (P x)) = P x
        exact PartialEquiv.left_inv e₁ hPsrc
  -- the three pieces cover `ℝ`
  have hcover : Set.Iio (δ₀/8) ∪ Set.Ioo (δ₀/16) (1 - δ₁/16) ∪ Set.Ioi (1 - δ₁/8)
      = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_Ioo, Set.mem_Ioi, Set.mem_univ, iff_true]
    rcases lt_or_ge x (δ₀/8) with h | h
    · exact Or.inl (Or.inl h)
    · rcases lt_or_ge (1 - δ₁/8) x with h2 | h2
      · exact Or.inr h2
      · exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)
  have hall : ContMDiffOn J (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder P'
      (Set.Iio (δ₀/8) ∪ Set.Ioo (δ₀/16) (1 - δ₁/16) ∪ Set.Ioi (1 - δ₁/8)) := by
    have h12 : ContMDiffOn J (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder P'
        (Set.Iio (δ₀/8) ∪ Set.Ioo (δ₀/16) (1 - δ₁/16)) :=
      hleft.union_of_isOpen hmid isOpen_Iio isOpen_Ioo
    exact h12.union_of_isOpen hright (isOpen_Iio.union isOpen_Ioo) isOpen_Ioi
  have hres : ContMDiff J (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder P' := by
    rw [← contMDiffOn_univ, ← hcover]
    exact hall
  refine ⟨P', hres, ?_⟩
  intro t ht
  rw [Set.mem_Icc] at ht
  rw [hP'def t]
  by_cases h1 : t < δ₀/8
  · rw [if_pos h1, hΨeq t ⟨ht.1, h1⟩]
    have hPsrc : P t ∈ e.source :=
      hδ₀sub t (by rw [abs_of_nonneg ht.1]; linarith [h1, hδ₀pos])
    show e.symm (e (P t)) = P t
    exact PartialEquiv.left_inv e hPsrc
  · rw [if_neg h1]
    by_cases h2 : t ≤ 1 - δ₁/8
    · rw [if_pos h2]
    · rw [if_neg h2]
      rw [hΨ₁eq t ⟨lt_of_not_ge h2, ht.2⟩]
      have hPsrc : P t ∈ e₁.source := hδ₁sub t (by
        rw [abs_of_nonpos (by linarith [ht.2])]
        linarith [lt_of_not_ge h2, hδ₁pos])
      show e₁.symm (e₁ (P t)) = P t
      exact PartialEquiv.left_inv e₁ hPsrc

end

end Work.Crux
