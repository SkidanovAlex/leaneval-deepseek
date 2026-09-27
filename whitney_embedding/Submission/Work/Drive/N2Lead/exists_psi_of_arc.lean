import Mathlib
import Submission.Work.Drive.N2Lead.extend_strictMono
import Submission.Work.Drive.PushDisc.exists_inverse_contDiffOn

namespace Work.Drive.N2Lead

open Set Filter Function
open scoped Topology

/-- **Smooth extension of a function defined on an open interval.**

Let `h` be `C^∞` on the open interval `(A, B)`, and let `A < c ≤ d < B`.  Then there is a
globally `C^∞` function `β` which agrees with `h` on a whole neighbourhood of the closed interval
`[c, d]` (in particular on `[c,d]` itself).

This is the "plateau" step which turns a `ContDiffOn` statement on an open interval into a global
`ContDiff` statement with the same germ at every point of `[c,d]`. -/
theorem exists_contDiff_eqOn_nhds_Icc {h : ℝ → ℝ} {A B c d : ℝ}
    (hAc : A < c) (hdb : d < B)
    (hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (Set.Ioo A B)) :
    ∃ β : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β ∧
      (∀ x ∈ Set.Icc c d, β x = h x) ∧
      (∀ x ∈ Set.Icc c d, β =ᶠ[𝓝 x] h) := by
  rcases lt_or_ge d c with hdc | hcd
  · -- the degenerate case `d < c`: `Icc c d` is empty
    refine ⟨fun _ => 0, contDiff_const, ?_, ?_⟩
    · intro x hx
      exact absurd (hx.1.trans hx.2) (not_le.mpr hdc)
    · intro x hx
      exact absurd (hx.1.trans hx.2) (not_le.mpr hdc)
  · -- the interesting case `c ≤ d`
    set η : ℝ := min (c - A) (B - d) / 2 with hη
    have hηpos : 0 < η := by
      rw [hη]
      have h1 : 0 < c - A := by linarith
      have h2 : 0 < B - d := by linarith
      have h3 : 0 < min (c - A) (B - d) := lt_min h1 h2
      linarith
    have hA'c : A + η < c := by
      have hle : η ≤ (c - A) / 2 := by
        rw [hη]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      linarith
    have hdB' : d < B - η := by
      have hle : η ≤ (B - d) / 2 := by
        rw [hη]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      linarith
    set A' : ℝ := A + η with hA'
    set B' : ℝ := B - η with hB'
    have hA'A : A < A' := by rw [hA']; linarith
    have hB'B : B' < B := by rw [hB']; linarith
    have hA'B' : A' < B' := by linarith
    set η₁ : ℝ := (c - A') / 2 with hη₁
    set η₂ : ℝ := (B' - d) / 2 with hη₂
    have hη₁pos : 0 < η₁ := by rw [hη₁]; linarith
    have hη₂pos : 0 < η₂ := by rw [hη₂]; linarith
    -- the plateau: `0` outside `[A', B']` and `1` on a neighbourhood of `[c,d]`
    set χ : ℝ → ℝ := fun x => Real.smoothTransition ((x - A') / η₁) *
      Real.smoothTransition ((B' - x) / η₂) with hχ
    have hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := by
      rw [hχ]; fun_prop
    have hχ0a : ∀ x : ℝ, x ≤ A' → χ x = 0 := by
      intro x hx
      show Real.smoothTransition ((x - A') / η₁) * Real.smoothTransition ((B' - x) / η₂) = 0
      have hle : (x - A') / η₁ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hη₁pos.le
      rw [Real.smoothTransition.zero_of_nonpos hle, zero_mul]
    have hχ0b : ∀ x : ℝ, B' ≤ x → χ x = 0 := by
      intro x hx
      show Real.smoothTransition ((x - A') / η₁) * Real.smoothTransition ((B' - x) / η₂) = 0
      have hle : (B' - x) / η₂ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hη₂pos.le
      rw [Real.smoothTransition.zero_of_nonpos hle, mul_zero]
    have hχ1 : ∀ x : ℝ, A' + η₁ ≤ x → x ≤ B' - η₂ → χ x = 1 := by
      intro x hx1 hx2
      show Real.smoothTransition ((x - A') / η₁) * Real.smoothTransition ((B' - x) / η₂) = 1
      have h1 : 1 ≤ (x - A') / η₁ := by rw [le_div_iff₀ hη₁pos]; linarith
      have h2 : 1 ≤ (B' - x) / η₂ := by rw [le_div_iff₀ hη₂pos]; linarith
      rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2,
        one_mul]
    have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => χ x * h x) := by
      rw [contDiff_iff_contDiffAt]
      intro x
      rcases lt_or_ge x A' with hx | hx
      · have hev : (fun x : ℝ => χ x * h x) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
          filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
          show χ y * h y = 0
          rw [hχ0a y hy.le, zero_mul]
        exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
      rcases lt_or_ge B' x with hx2 | hx2
      · have hev : (fun x : ℝ => χ x * h x) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
          filter_upwards [isOpen_Ioi.mem_nhds hx2] with y hy
          show χ y * h y = 0
          rw [hχ0b y hy.le, zero_mul]
        exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
      · have hxmem : x ∈ Set.Ioo A B := ⟨by linarith, by linarith⟩
        exact hχsm.contDiffAt.mul (hh.contDiffAt (Ioo_mem_nhds hxmem.1 hxmem.2))
    refine ⟨fun x => χ x * h x, hsm, ?_, ?_⟩
    · intro x hx
      show χ x * h x = h x
      have hb1 : A' + η₁ ≤ x := by linarith [hx.1]
      have hb2 : x ≤ B' - η₂ := by linarith [hx.2]
      rw [hχ1 x hb1 hb2, one_mul]
    · intro x hx
      have hb1 : A' + η₁ < x := by linarith [hx.1]
      have hb2 : x < B' - η₂ := by linarith [hx.2]
      filter_upwards [Ioo_mem_nhds hb1 hb2] with y hy
      show χ y * h y = h y
      rw [hχ1 y hy.1.le hy.2.le, one_mul]

/-- **Global monotone extension of a prescribed monotone arc function.**

Let `α ϑ : ℝ → ℝ` be `C^∞`, `ε δ ∈ {1, -1}`, `L > 0`, and suppose `ε * deriv α s > 0` and
`δ * deriv ϑ s > 0` for `|s| ≤ L` (so `α` and `ϑ` are strictly monotone along `[-L,L]`, in the
directions `ε`, `δ`).  Then there is a `C^∞` function `ψ` whose derivative has sign `ε * δ`
everywhere and which reproduces the prescription `s ↦ ϑ s` on the arc `α '' [-L,L]`:
`ψ (α s) = ϑ s` for `|s| ≤ L`.

PROOF RECIPE (checked by the requester):
1. `α₁ := fun x => ε * α x`, `ϑ₁ := fun x => δ * ϑ x` are `C^∞` with `deriv α₁ s = ε * deriv α s > 0`
   and `deriv ϑ₁ s = δ * deriv ϑ s > 0` on `|s| ≤ L`.
2. `Work.Drive.N2Lead.exists_pos_of_pos_on_Icc` (in `extend_strictMono`) applied to `deriv α₁` and
   `deriv ϑ₁` (continuous via `ContDiff.continuous_deriv`) gives `δ' > 0` with positivity on
   `[-L-δ', L+δ']`.
3. `Work.Drive.PushDisc.exists_inverse_contDiffOn` applied to `α₁` with `a := -(L+δ')`, `b := L+δ'`
   gives `σ₀ : ℝ → ℝ` with `σ₀ (α₁ x) = x` on `[a,b]`, `ContDiffOn σ₀ (α₁ a, α₁ b)` and
   `deriv σ₀ y = (deriv α₁ (σ₀ y))⁻¹` there.
4. Globalise with a `Real.smoothTransition` plateau `χ` equal to `1` on a closed interval strictly
   containing `[α₁ (-L), α₁ L]` and vanishing outside `(α₁ a, α₁ b)`; `β := fun x => χ x * σ₀ x` is
   `C^∞` on `ℝ` (on `(α₁ a, α₁ b)` it agrees with `χ • σ₀`; outside the support of `χ` it is `0`),
   and `β (α₁ x) = x` for `|x| ≤ L`.
5. `G := fun x => ϑ₁ (β x)` is `C^∞` and for `|s| ≤ L`, `deriv G (α₁ s) = deriv ϑ₁ s * (deriv α₁ s)⁻¹ > 0`
   (chain rule, plus `Filter.EventuallyEq.deriv_eq` since `β =ᶠ σ₀` near `α₁ s`).
6. `Work.Drive.N2Lead.extend_strictMono` with `a := α₁ (-L)`, `b := α₁ L` gives a globally strictly
   increasing `C^∞` `φ` with `φ = G` on `[α₁ (-L), α₁ L]`; note `α₁ s ∈ [α₁ (-L), α₁ L]` for
   `|s| ≤ L` by monotonicity.
7. Answer `ψ := fun x => δ * φ (ε * x)`: smooth, `ε * δ * deriv ψ x = deriv φ (ε * x) > 0`, and
   `ψ (α s) = δ * φ (α₁ s) = δ * ϑ₁ s = ϑ s` for `|s| ≤ L`. -/
theorem exists_psi_of_arc {L : ℝ} {α ϑ : ℝ → ℝ} {ε δ : ℝ} (hL : 0 < L)
    (hαsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α)
    (hϑsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ϑ)
    (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1)
    (hαder : ∀ s : ℝ, |s| ≤ L → 0 < ε * deriv α s)
    (hϑder : ∀ s : ℝ, |s| ≤ L → 0 < δ * deriv ϑ s) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
      (∀ x : ℝ, 0 < ε * δ * deriv ψ x) ∧
      (∀ s : ℝ, |s| ≤ L → ψ (α s) = ϑ s) := by
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hε2 : ε * ε = 1 := by rcases hε with h | h <;> simp [h]
  have hδ2 : δ * δ = 1 := by rcases hδ with h | h <;> simp [h]
  -- ### Step 1: normalise the signs
  set α₁ : ℝ → ℝ := fun x => ε * α x with hα₁
  set ϑ₁ : ℝ → ℝ := fun x => δ * ϑ x with hϑ₁
  have hα₁sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α₁ := by
    rw [hα₁]; exact contDiff_const.mul hαsm
  have hϑ₁sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ϑ₁ := by
    rw [hϑ₁]; exact contDiff_const.mul hϑsm
  have hαder₁ : ∀ s : ℝ, |s| ≤ L → 0 < deriv α₁ s := by
    intro s hs
    have hdiff : DifferentiableAt ℝ α s := (hαsm.differentiable hn).differentiableAt
    rw [hα₁, deriv_const_mul ε hdiff]
    exact hαder s hs
  have hϑder₁ : ∀ s : ℝ, |s| ≤ L → 0 < deriv ϑ₁ s := by
    intro s hs
    have hdiff : DifferentiableAt ℝ ϑ s := (hϑsm.differentiable hn).differentiableAt
    rw [hϑ₁, deriv_const_mul δ hdiff]
    exact hϑder s hs
  -- ### Step 2: widen the interval on which the derivatives are positive
  have hLlt : -L < L := by linarith
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := exists_pos_of_pos_on_Icc
    ((contDiff_infty_iff_deriv.mp hα₁sm).2.continuous) hLlt
    (fun x hx => hαder₁ x (abs_le.mpr hx))
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := exists_pos_of_pos_on_Icc
    ((contDiff_infty_iff_deriv.mp hϑ₁sm).2.continuous) hLlt
    (fun x hx => hϑder₁ x (abs_le.mpr hx))
  set δ' : ℝ := min δ₁ δ₂ with hδ'
  have hδ'pos : 0 < δ' := by rw [hδ']; exact lt_min hδ₁pos hδ₂pos
  have hδ'₁ : δ' ≤ δ₁ := by rw [hδ']; exact min_le_left _ _
  have hδ'₂ : δ' ≤ δ₂ := by rw [hδ']; exact min_le_right _ _
  set a : ℝ := -(L + δ') with ha
  set b : ℝ := L + δ' with hb
  have hposα : ∀ x : ℝ, x ∈ Set.Icc a b → 0 < deriv α₁ x := by
    intro x hx
    refine hδ₁ x ?_
    rw [ha, hb] at hx
    exact ⟨by linarith [hx.1, hδ'₁], by linarith [hx.2, hδ'₁]⟩
  have hposϑ : ∀ x : ℝ, x ∈ Set.Icc a b → 0 < deriv ϑ₁ x := by
    intro x hx
    refine hδ₂ x ?_
    rw [ha, hb] at hx
    exact ⟨by linarith [hx.1, hδ'₂], by linarith [hx.2, hδ'₂]⟩
  have hab : a < b := by rw [ha, hb]; linarith
  have hα₁mono : StrictMonoOn α₁ (Set.Icc a b) :=
    strictMonoOn_of_deriv_pos (convex_Icc a b) hα₁sm.continuous.continuousOn (by
      intro x hx
      rw [interior_Icc] at hx
      exact hposα x ⟨hx.1.le, hx.2.le⟩)
  have hα₁mono' : MonotoneOn α₁ (Set.Icc a b) := hα₁mono.monotoneOn
  have hmL : -L ∈ Set.Icc a b := by
    rw [ha, hb, Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  have hLm : L ∈ Set.Icc a b := by
    rw [ha, hb, Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  have hmemab : ∀ s : ℝ, |s| ≤ L → s ∈ Set.Icc a b := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := abs_le.mp hs
    rw [ha, hb, Set.mem_Icc]
    exact ⟨by linarith, by linarith⟩
  -- ### Step 3: the monotone arc and its smooth local inverse
  have hα₁a_lt : α₁ a < α₁ (-L) := hα₁mono ⟨le_rfl, hab.le⟩ hmL (by rw [ha]; linarith)
  have hα₁L_lt : α₁ L < α₁ b := hα₁mono hLm ⟨hab.le, le_rfl⟩ (by rw [hb]; linarith)
  obtain ⟨σ₀, hσ₀inv, hσ₀sm, hσ₀der⟩ :=
    Work.Drive.PushDisc.exists_inverse_contDiffOn hα₁sm hab hposα
  -- ### Step 4: globalise the local inverse
  obtain ⟨β, hβsm, hβeq, hβev⟩ := exists_contDiff_eqOn_nhds_Icc (h := σ₀)
    (A := α₁ a) (B := α₁ b) (c := α₁ (-L)) (d := α₁ L) hα₁a_lt hα₁L_lt hσ₀sm
  have hα₁s_mem : ∀ s : ℝ, |s| ≤ L → α₁ s ∈ Set.Icc (α₁ (-L)) (α₁ L) := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := abs_le.mp hs
    have hsa := hmemab s hs
    exact ⟨hα₁mono' hmL hsa (by linarith), hα₁mono' hsa hLm (by linarith)⟩
  have hβval : ∀ s : ℝ, |s| ≤ L → β (α₁ s) = s := by
    intro s hs
    rw [hβeq (α₁ s) (hα₁s_mem s hs), hσ₀inv s (hmemab s hs)]
  -- ### Step 5: `G := ϑ₁ ∘ β` has positive derivative on the arc
  set G : ℝ → ℝ := fun x => ϑ₁ (β x) with hG
  have hGsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := by
    rw [hG]; exact hϑ₁sm.comp hβsm
  have hderivG : ∀ s : ℝ, |s| ≤ L → 0 < deriv G (α₁ s) := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := abs_le.mp hs
    have hsa := hmemab s hs
    have hsaIoo : s ∈ Set.Ioo a b := by
      rw [ha, hb, Set.mem_Ioo]
      exact ⟨by linarith, by linarith⟩
    have hα₁sIoo : α₁ s ∈ Set.Ioo (α₁ a) (α₁ b) :=
      ⟨hα₁mono ⟨le_rfl, hab.le⟩ hsa hsaIoo.1, hα₁mono hsa ⟨hab.le, le_rfl⟩ hsaIoo.2⟩
    have hσβ : β =ᶠ[𝓝 (α₁ s)] σ₀ := hβev (α₁ s) (hα₁s_mem s hs)
    have hGev : G =ᶠ[𝓝 (α₁ s)] (fun y => ϑ₁ (σ₀ y)) := by
      filter_upwards [hσβ] with y hy
      show ϑ₁ (β y) = ϑ₁ (σ₀ y)
      rw [hy]
    have h1 : deriv G (α₁ s) = deriv (fun y => ϑ₁ (σ₀ y)) (α₁ s) :=
      Filter.EventuallyEq.deriv_eq hGev
    have hσd : DifferentiableAt ℝ σ₀ (α₁ s) :=
      (hσ₀sm.contDiffAt (Ioo_mem_nhds hα₁sIoo.1 hα₁sIoo.2)).differentiableAt hn
    have hϑ₁d : DifferentiableAt ℝ ϑ₁ (σ₀ (α₁ s)) :=
      (hϑ₁sm.differentiable hn).differentiableAt
    have h2 : deriv (fun y => ϑ₁ (σ₀ y)) (α₁ s)
        = deriv ϑ₁ (σ₀ (α₁ s)) * deriv σ₀ (α₁ s) := by
      show deriv (ϑ₁ ∘ σ₀) (α₁ s) = deriv ϑ₁ (σ₀ (α₁ s)) * deriv σ₀ (α₁ s)
      exact deriv_comp (α₁ s) hϑ₁d hσd
    have h3 : 0 < deriv ϑ₁ (σ₀ (α₁ s)) * deriv σ₀ (α₁ s) := by
      rw [(hσ₀der (α₁ s) hα₁sIoo).2, hσ₀inv s hsa]
      exact mul_pos (hϑder₁ s hs) (inv_pos.mpr (hposα s hsa))
    rw [h1, h2]
    exact h3
  -- ### Step 6: extend to a globally strictly increasing smooth function
  have hα₁lL : α₁ (-L) < α₁ L := hα₁mono hmL hLm hLlt
  obtain ⟨φ, hφsm, hφder, hφeq⟩ := extend_strictMono hα₁lL hGsm (by
    intro x hx
    obtain ⟨s, hs, hxs⟩ :=
      intermediate_value_Icc (show -L ≤ L by linarith) hα₁sm.continuous.continuousOn hx
    rw [← hxs]
    exact hderivG s (abs_le.mpr hs))
  -- ### Step 7: undress the sign normalisation
  refine ⟨fun x => δ * φ (ε * x), ?_, ?_, ?_⟩
  · exact (contDiff_const (c := δ)).mul (hφsm.comp (contDiff_const.mul contDiff_id))
  · intro x
    have hderiv : deriv (fun y => δ * φ (ε * y)) x = δ * (deriv φ (ε * x) * ε) := by
      have hφd : DifferentiableAt ℝ φ (ε * x) := (hφsm.differentiable hn).differentiableAt
      have hlin : DifferentiableAt ℝ (fun y : ℝ => ε * y) x := by fun_prop
      have hinner : DifferentiableAt ℝ (fun y : ℝ => φ (ε * y)) x :=
        hφd.comp x hlin
      rw [deriv_const_mul δ hinner]
      rw [show (fun y : ℝ => φ (ε * y)) = φ ∘ (fun y : ℝ => ε * y) from rfl,
        deriv_comp x hφd hlin]
      have hd : deriv (fun y : ℝ => ε * y) x = ε := by
        rw [show (fun y : ℝ => ε * y) = (fun y => ε * id y) from rfl,
          deriv_const_mul ε differentiable_id.differentiableAt, deriv_id, mul_one]
      rw [hd]
    rw [hderiv]
    have hkey : ε * δ * (δ * (deriv φ (ε * x) * ε)) = deriv φ (ε * x) := by
      calc ε * δ * (δ * (deriv φ (ε * x) * ε))
          = (ε * ε) * (δ * δ) * deriv φ (ε * x) := by ring
        _ = deriv φ (ε * x) := by rw [hε2, hδ2]; ring
    rw [hkey]
    exact hφder (ε * x)
  · intro s hs
    have hmem := hα₁s_mem s hs
    have hGval : G (α₁ s) = ϑ₁ s := by
      show ϑ₁ (β (α₁ s)) = ϑ₁ s
      rw [hβval s hs]
    show δ * φ (ε * α s) = ϑ s
    have h1 : ε * α s = α₁ s := rfl
    rw [h1, hφeq (α₁ s) hmem, hGval]
    show δ * (δ * ϑ s) = ϑ s
    rw [← mul_assoc, hδ2, one_mul]

end Work.Drive.N2Lead
