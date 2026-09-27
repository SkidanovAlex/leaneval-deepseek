import Mathlib
import Submission.Work.Drive.BoxParityAux
import Submission.Work.Drive.crossing_of_deriv_ne_zero
import Submission.Work.Drive.cofactorVec_ne_zero_of_surjective
import Submission.Work.Drive.flow_tendsto_atBot_eq_zero

namespace Work.Drive

open scoped ContDiff Topology
open Set Filter

noncomputable section

/-- The sign of a real number, as `±1`. -/
private def chartSign (x : ℝ) : ℝ := if 0 < x then 1 else -1

private lemma chartSign_of_pos {x : ℝ} (h : 0 < x) : chartSign x = 1 := if_pos h

private lemma chartSign_of_nonpos {x : ℝ} (h : ¬ 0 < x) : chartSign x = -1 := if_neg h

private lemma chartSign_mul_pos {x : ℝ} (hx : x ≠ 0) : 0 < chartSign x * x := by
  rcases lt_or_gt_of_ne hx with h | h
  · rw [chartSign_of_nonpos (not_lt.mpr h.le), neg_one_mul]; linarith
  · rw [chartSign_of_pos h, one_mul]; exact h

private lemma chartSign_mul_self (x : ℝ) : chartSign x * chartSign x = 1 := by
  rcases lt_or_ge (0 : ℝ) x with h | h
  · rw [chartSign_of_pos h, one_mul]
  · rw [chartSign_of_nonpos (not_lt.mpr h), neg_mul_neg]; norm_num

private lemma chartSign_eq_one_or_neg_one (x : ℝ) : chartSign x = 1 ∨ chartSign x = -1 := by
  rcases lt_or_ge (0 : ℝ) x with h | h
  · exact Or.inl (chartSign_of_pos h)
  · exact Or.inr (chartSign_of_nonpos (not_lt.mpr h))

/-- A continuous nowhere vanishing function on a preconnected set of reals has constant sign. -/
private lemma sign_const_of_preconnected {f : ℝ → ℝ} {K : Set ℝ} (hK : IsPreconnected K)
    (hf : ContinuousOn f K) (hne : ∀ x ∈ K, f x ≠ 0) :
    (∀ x ∈ K, 0 < f x) ∨ (∀ x ∈ K, f x < 0) := by
  by_contra h
  push_neg at h
  obtain ⟨⟨x, hx, hxle⟩, ⟨y, hy, hyle⟩⟩ := h
  have hfx : f x < 0 := lt_of_le_of_ne hxle (hne x hx)
  have hfy : 0 < f y := lt_of_le_of_ne hyle (hne y hy).symm
  have h0 : (0 : ℝ) ∈ f '' K :=
    (hK.image f hf).ordConnected.out ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ⟨hfx.le, hfy.le⟩
  obtain ⟨z, hz, hz0⟩ := h0
  exact hne z hz hz0


theorem chart_exit_of_normalForm {m : ℕ} {F : Work.Drive.Amb m → Work.Drive.Tgt m}
    (hF : ContDiff ℝ Work.Drive.Ctop F)
    {p : Work.Drive.Amb m} {i : Fin (m + 1)} {δ₀ ρ₀ : ℝ} {η : ℝ → Work.Drive.Amb m}
    (hδ₀ : 0 < δ₀) (hρ₀ : 0 < ρ₀) (hηc : Continuous η)
    (hnormal : ∀ u : ℝ, |u - p i| < δ₀ →
      F (u • EuclideanSpace.single i 1 + η u) = 0 ∧
      Function.Surjective (fun v : {v : Work.Drive.Amb m // v i = 0} =>
        fderiv ℝ F (u • EuclideanSpace.single i 1 + η u) v.1))
    (hchar : ∀ x : Work.Drive.Amb m, |x i - p i| < δ₀ →
      ‖x - (x i) • EuclideanSpace.single i 1 - η (x i)‖ < ρ₀ →
      (F x = 0 ↔ x = (x i) • EuclideanSpace.single i 1 + η (x i)))
    (hreg : ∀ x ∈ Submission.Drive.unitBox m, F x = 0 → Function.Surjective (fderiv ℝ F x))
    {γ : ℝ → Work.Drive.Amb m} (hγd : ∀ t : ℝ, HasDerivAt γ (Work.Drive.flowField F (γ t)) t)
    {T t₀ : ℝ} (hbox : ∀ t : ℝ, t ≤ T → γ t ∈ Submission.Drive.unitBox m)
    (hzero : ∀ t : ℝ, t ≤ T → F (γ t) = 0) (ht₀ : t₀ ≤ T)
    (htube : ‖γ t₀ - (γ t₀ i) • EuclideanSpace.single i 1 - η (γ t₀ i)‖ < ρ₀ / 2)
    (hcoord : |γ t₀ i - p i| < δ₀ / 2) :
    ∃ a : ℝ, a < t₀ ∧
      (γ a = (p i - δ₀ / 2) • EuclideanSpace.single i 1 + η (p i - δ₀ / 2) ∨
       γ a = (p i + δ₀ / 2) • EuclideanSpace.single i 1 + η (p i + δ₀ / 2)) := by
  classical
  -- ## Setup: the coordinate `u`, the field component `g`, the graph map `G`.
  have hFc : Continuous F := hF.continuous
  have hflowc : Continuous (flowField F) := (flowField_basic hF).1.continuous
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr fun s => (hγd s).continuousAt
  set u : ℝ → ℝ := fun r => γ r i with hu
  set g : ℝ → ℝ := fun r => flowField F (γ r) i with hg
  set G : ℝ → Amb m := fun v => v • EuclideanSpace.single i 1 + η v with hG
  have huc : Continuous u := by
    rw [hu]; exact (EuclideanSpace.proj i).continuous.comp hγc
  have hgc : Continuous g := by
    rw [hg]; exact (EuclideanSpace.proj i).continuous.comp (hflowc.comp hγc)
  have hGc : Continuous G := by
    rw [hG]; exact (continuous_id.smul continuous_const).add hηc
  have hud : ∀ r : ℝ, HasDerivAt u (g r) r := by
    intro r
    simpa only [hu, hg] using hasDerivAt_apply (hγd r) i
  -- ## The region `S`, as a set of times
  set S : Set ℝ := {r : ℝ | |u r - p i| < δ₀ ∧ ‖γ r - G (u r)‖ < ρ₀} with hS
  have hSmem : ∀ r : ℝ, r ∈ S ↔ |u r - p i| < δ₀ ∧ ‖γ r - G (u r)‖ < ρ₀ := by
    intro r; rw [hS]; exact Iff.rfl
  have hSopen : IsOpen S := by
    have h1 : IsOpen {r : ℝ | |u r - p i| < δ₀} :=
      isOpen_lt ((huc.sub continuous_const).abs) continuous_const
    have h2 : IsOpen {r : ℝ | ‖γ r - G (u r)‖ < ρ₀} :=
      isOpen_lt ((hγc.sub (hGc.comp huc)).norm) continuous_const
    have heq : S = {r : ℝ | |u r - p i| < δ₀} ∩ {r : ℝ | ‖γ r - G (u r)‖ < ρ₀} := by
      rw [hS]; ext r; simp
    rw [heq]; exact h1.inter h2
  have ht0S : t₀ ∈ S := by
    rw [hS]
    refine ⟨?_, ?_⟩
    · have h : |u t₀ - p i| < δ₀ / 2 := by simpa only [hu] using hcoord
      have h' := abs_lt.mp h
      exact abs_lt.mpr ⟨by linarith [h'.1], by linarith [h'.2]⟩
    · have heq : ‖γ t₀ - G (u t₀)‖ =
          ‖γ t₀ - (γ t₀ i) • EuclideanSpace.single i 1 - η (γ t₀ i)‖ := by
        congr 1; simp only [hG, hu]; abel
      rw [heq]; linarith [htube]
  -- ## On `S`, the zero set of `F` is exactly the graph
  have hchar_on : ∀ r : ℝ, r ≤ t₀ → r ∈ S → γ r = G (u r) := by
    intro r hr hrS
    rw [hS] at hrS
    obtain ⟨h1, h2⟩ := hrS
    have h1' : |(γ r) i - p i| < δ₀ := by simpa only [hu] using h1
    have h2' : ‖(γ r) - (γ r) i • EuclideanSpace.single i 1 - η ((γ r) i)‖ < ρ₀ := by
      have heq : ‖γ r - G (u r)‖ =
          ‖γ r - (γ r) i • EuclideanSpace.single i 1 - η ((γ r) i)‖ := by
        congr 1; simp only [hG, hu]; abel
      rw [← heq]; exact h2
    have h3 := (hchar (γ r) h1' h2').mp (hzero r (le_trans hr ht₀))
    simpa only [hG, hu] using h3
  -- ## The signed coordinate
  set σ : ℝ := chartSign (g t₀) with hσ
  have hσmem : σ = 1 ∨ σ = -1 := by rw [hσ]; exact chartSign_eq_one_or_neg_one _
  have hσsq : σ * σ = 1 := by rw [hσ]; exact chartSign_mul_self _
  have hσabs : |σ| = 1 := by rcases hσmem with h | h <;> rw [h] <;> norm_num
  have hσne : σ ≠ 0 := by rcases hσmem with h | h <;> rw [h] <;> norm_num
  set w : ℝ → ℝ := fun r => σ * u r with hw
  set Y : ℝ := σ * p i - δ₀ / 2 with hY
  have hwc : Continuous w := by rw [hw]; exact continuous_const.mul huc
  have hwd : ∀ r : ℝ, HasDerivAt w (σ * g r) r := by
    intro r; rw [hw]; exact (hud r).const_mul σ
  have huw : ∀ r : ℝ, u r = σ * w r := by
    intro r; rw [hw, ← mul_assoc, hσsq, one_mul]
  -- ## `E`: the times whose whole forward window to `t₀` lies in the region
  set E : Set ℝ := {s : ℝ | Set.Icc s t₀ ⊆ S} with hE
  have ht0E : t₀ ∈ E := by
    rw [hE]
    intro x hx
    rw [Set.mem_Icc] at hx
    rw [le_antisymm hx.2 hx.1]
    exact ht0S
  have hEne : E.Nonempty := ⟨t₀, ht0E⟩
  -- ## `E` is bounded below: otherwise the orbit stays in the chart for all time and
  -- converges, contradicting regularity (`hreg`) via `flow_tendsto_atBot_eq_zero`.
  have hEbdd : BddBelow E := by
    by_contra hcon
    have hSall : Set.Iic t₀ ⊆ S := by
      intro z hz
      have hz' : z ≤ t₀ := Set.mem_Iic.mp hz
      have hex : ∃ e ∈ E, e < z := by
        by_contra h2
        push_neg at h2
        exact hcon ⟨z, h2⟩
      obtain ⟨e, heE, hez⟩ := hex
      rw [hE] at heE
      exact heE (Set.mem_Icc.mpr ⟨le_of_lt hez, hz'⟩)
    have hgraphall : ∀ r : ℝ, r ≤ t₀ → γ r = G (u r) :=
      fun r hr => hchar_on r hr (hSall (Set.mem_Iic.mpr hr))
    have hgne : ∀ r : ℝ, r ≤ t₀ → g r ≠ 0 := by
      intro r hr
      have h1 : |u r - p i| < δ₀ ∧ ‖γ r - G (u r)‖ < ρ₀ :=
        (hSmem r).mp (hSall (Set.mem_Iic.mpr hr))
      have hsurj : Function.Surjective (fun v : {v : Amb m // v i = 0} =>
          fderiv ℝ F (γ r) v.1) := by
        rw [hgraphall r hr]
        simpa only [hG] using (hnormal (u r) h1.1).2
      exact flowField_apply_ne_zero_of_bdy (hbox r (le_trans hr ht₀)) hsurj
    have hσgt : 0 < σ * g t₀ := by
      rw [hσ]
      exact chartSign_mul_pos (hgne t₀ le_rfl)
    have hσgpos : ∀ r : ℝ, r ≤ t₀ → 0 < σ * g r := by
      intro r hr
      have hne : ∀ z ∈ Set.Iic t₀, σ * g z ≠ 0 :=
        fun z hz => mul_ne_zero hσne (hgne z (Set.mem_Iic.mp hz))
      rcases sign_const_of_preconnected isPreconnected_Iic
        ((continuous_const.mul hgc).continuousOn) hne with h | h
      · exact h r (Set.mem_Iic.mpr hr)
      · exact absurd (h t₀ (Set.mem_Iic.mpr le_rfl)) (not_lt.mpr hσgt.le)
    have hwmono : ∀ r₁ : ℝ, r₁ ≤ t₀ → ∀ r₂ : ℝ, r₂ ≤ t₀ → r₁ ≤ r₂ → w r₁ ≤ w r₂ := by
      intro r₁ h₁ r₂ h₂ hle
      rcases lt_or_eq_of_le hle with hlt | heq
      · have hcont : ContinuousOn w (Set.Icc r₁ r₂) := hwc.continuousOn
        have hdiff : DifferentiableOn ℝ w (Set.Ioo r₁ r₂) :=
          fun r _ => (hwd r).differentiableAt.differentiableWithinAt
        obtain ⟨ξ, hξ, hξd⟩ := exists_deriv_eq_slope w hlt hcont hdiff
        have hξt : ξ ≤ t₀ := le_trans (le_of_lt hξ.2) h₂
        have hpos : 0 < σ * g ξ := hσgpos ξ hξt
        rw [(hwd ξ).deriv] at hξd
        have hst : 0 < r₂ - r₁ := by linarith
        have hdiv : 0 < (w r₂ - w r₁) / (r₂ - r₁) := by rw [← hξd]; exact hpos
        rcases (div_pos_iff.mp hdiv) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
      · rw [heq]
    have hwbdd : ∀ r : ℝ, r ≤ t₀ → |w r| ≤ 1 := by
      intro r hr
      have h1 : u r ∈ Set.Icc (0 : ℝ) 1 := (hbox r (le_trans hr ht₀)) i
      rw [hw, abs_mul, hσabs, one_mul]
      exact abs_le.mpr ⟨by linarith [h1.1], h1.2⟩
    have hwtmono : Monotone (fun r : ℝ => w (min r t₀)) := by
      intro r₁ r₂ hr
      exact hwmono (min r₁ t₀) (min_le_right _ _) (min r₂ t₀) (min_le_right _ _)
        (min_le_min hr le_rfl)
    have hwtbdd : BddBelow (Set.range fun r : ℝ => w (min r t₀)) := by
      refine ⟨-1, ?_⟩
      rintro _ ⟨r, rfl⟩
      exact (abs_le.mp (hwbdd (min r t₀) (min_le_right r t₀))).1
    have hwtend : Tendsto (fun r : ℝ => w (min r t₀)) atBot
        (𝓝 (⨅ r : ℝ, w (min r t₀))) :=
      tendsto_atBot_ciInf hwtmono hwtbdd
    set L : ℝ := ⨅ r : ℝ, w (min r t₀) with hL
    have hwL : Tendsto w atBot (𝓝 L) := by
      refine Filter.Tendsto.congr' ?_ hwtend
      change ∀ᶠ r : ℝ in Filter.atBot, w (min r t₀) = w r
      rw [Filter.eventually_atBot]
      exact ⟨t₀, fun r hr => by rw [min_eq_left hr]⟩
    have hγtend : Tendsto γ atBot (𝓝 (G (σ * L))) := by
      have h1 : Tendsto (fun r : ℝ => σ * w r) atBot (𝓝 (σ * L)) :=
        tendsto_const_nhds.mul hwL
      have h2 : Tendsto (fun r : ℝ => G (σ * w r)) atBot (𝓝 (G (σ * L))) :=
        (hGc.tendsto (σ * L)).comp h1
      refine Filter.Tendsto.congr' ?_ h2
      change ∀ᶠ r : ℝ in Filter.atBot, G (σ * w r) = γ r
      rw [Filter.eventually_atBot]
      exact ⟨t₀, fun r hr => by rw [← huw r, ← hgraphall r hr]⟩
    have hxbox : G (σ * L) ∈ Submission.Drive.unitBox m := by
      refine (isClosed_unitBox m).mem_of_tendsto hγtend ?_
      rw [Filter.eventually_atBot]
      exact ⟨t₀, fun r hr => hbox r (le_trans hr ht₀)⟩
    have hxF : F (G (σ * L)) = 0 := by
      have h1 : Tendsto (fun r : ℝ => F (γ r)) atBot (𝓝 (F (G (σ * L)))) :=
        (hFc.tendsto (G (σ * L))).comp hγtend
      have h2 : Tendsto (fun r : ℝ => F (γ r)) atBot (𝓝 (0 : Tgt m)) := by
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        change ∀ᶠ r : ℝ in Filter.atBot, (0 : Tgt m) = F (γ r)
        rw [Filter.eventually_atBot]
        exact ⟨t₀, fun r hr => (hzero r (le_trans hr ht₀)).symm⟩
      exact tendsto_nhds_unique h1 h2
    have hVne : flowField F (G (σ * L)) ≠ 0 := by
      have hsurj := hreg (G (σ * L)) hxbox hxF
      have hcof : cofactorVectorF F (G (σ * L)) ≠ 0 :=
        cofactorVec_ne_zero_of_surjective (fderiv ℝ F (G (σ * L))) hsurj
      rw [flowField_on_box hxbox]
      exact smul_ne_zero (inv_ne_zero (by positivity)) hcof
    exact hVne (flow_tendsto_atBot_eq_zero hflowc hγd hγtend)
  -- ## The boundary point `R` of the last visit of the chart region
  set R : ℝ := sInf E with hR
  have hRle : R ≤ t₀ := by rw [hR]; exact csInf_le hEbdd ht0E
  have hIocS : Set.Ioc R t₀ ⊆ S := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := Set.mem_Ioc.mp hr
    obtain ⟨s, hsE, hsr⟩ := exists_lt_of_csInf_lt hEne (by rw [← hR]; exact hr1)
    rw [hE] at hsE
    exact hsE (Set.mem_Icc.mpr ⟨le_of_lt hsr, hr2⟩)
  have hRnotS : R ∉ S := by
    intro hRS
    obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp (hSopen.mem_nhds hRS)
    have hmem : R - ε / 2 ∈ E := by
      rw [hE]
      intro x hx
      obtain ⟨hx1, hx2⟩ := Set.mem_Icc.mp hx
      rcases le_total x R with hxR | hxR
      · apply hε
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith, by linarith⟩
      · rcases eq_or_lt_of_le hxR with h | h
        · rw [← h]; exact hRS
        · exact hIocS (Set.mem_Ioc.mpr ⟨h, hx2⟩)
    have h2 : sInf E ≤ R - ε / 2 := csInf_le hEbdd hmem
    rw [hR] at h2
    linarith
  have hRt₀ : R < t₀ := lt_of_le_of_ne hRle (fun h => hRnotS (h ▸ ht0S))
  have hclIoc : R ∈ closure (Set.Ioc R t₀) := by
    rw [closure_Ioc (ne_of_lt hRt₀)]
    exact Set.mem_Icc.mpr ⟨le_rfl, hRt₀.le⟩
  have hGR : γ R = G (u R) := by
    have hcl : IsClosed {r : ℝ | γ r = G (u r)} := isClosed_eq hγc (hGc.comp huc)
    exact closure_minimal (fun r hr => hchar_on r (Set.mem_Ioc.mp hr).2 (hIocS hr)) hcl hclIoc
  have huRle : |u R - p i| ≤ δ₀ := by
    have hcl : IsClosed {r : ℝ | |u r - p i| ≤ δ₀} :=
      isClosed_le ((huc.sub continuous_const).abs) continuous_const
    refine closure_minimal (fun r hr => ?_) hcl hclIoc
    exact le_of_lt ((hSmem r).mp (hIocS hr)).1
  have huRge : δ₀ ≤ |u R - p i| := by
    by_contra hcon
    push_neg at hcon
    exact hRnotS ((hSmem R).mpr ⟨hcon, by rw [hGR, sub_self, norm_zero]; exact hρ₀⟩)
  have huR : |u R - p i| = δ₀ := le_antisymm huRle huRge
  -- ## On `(R, t₀]` the `i`-component of the field does not vanish
  have hgne' : ∀ r ∈ Set.Ioc R t₀, g r ≠ 0 := by
    intro r hr
    have hrS : r ∈ S := hIocS hr
    have hrt : r ≤ t₀ := (Set.mem_Ioc.mp hr).2
    have h1 : |u r - p i| < δ₀ ∧ ‖γ r - G (u r)‖ < ρ₀ := (hSmem r).mp hrS
    have hsurj : Function.Surjective (fun v : {v : Amb m // v i = 0} =>
        fderiv ℝ F (γ r) v.1) := by
      rw [hchar_on r hrt hrS]
      simpa only [hG] using (hnormal (u r) h1.1).2
    exact flowField_apply_ne_zero_of_bdy (hbox r (le_trans hrt ht₀)) hsurj
  have hσgpos' : ∀ r ∈ Set.Ioc R t₀, 0 < σ * g r := by
    have hne : ∀ z ∈ Set.Ioc R t₀, σ * g z ≠ 0 := fun z hz => mul_ne_zero hσne (hgne' z hz)
    rcases sign_const_of_preconnected isPreconnected_Ioc
      ((continuous_const.mul hgc).continuousOn) hne with h | h
    · exact h
    · exfalso
      have ht0' : t₀ ∈ Set.Ioc R t₀ := Set.mem_Ioc.mpr ⟨hRt₀, le_rfl⟩
      have h1 := h t₀ ht0'
      have h2 : 0 < σ * g t₀ := by
        rw [hσ]
        exact chartSign_mul_pos (hgne' t₀ ht0')
      exact absurd h1 (not_lt_of_gt h2)
  -- ## `w` is strictly increasing on `[R, t₀]`
  have hwRlt : w R < w t₀ := by
    have hcont : ContinuousOn w (Set.Icc R t₀) := hwc.continuousOn
    have hdiff : DifferentiableOn ℝ w (Set.Ioo R t₀) :=
      fun r _ => (hwd r).differentiableAt.differentiableWithinAt
    obtain ⟨ξ, hξ, hξd⟩ := exists_deriv_eq_slope w hRt₀ hcont hdiff
    have hpos : 0 < σ * g ξ := hσgpos' ξ (Set.mem_Ioc.mpr ⟨hξ.1, le_of_lt hξ.2⟩)
    rw [(hwd ξ).deriv] at hξd
    have hst : 0 < t₀ - R := by linarith
    have hdiv : 0 < (w t₀ - w R) / (t₀ - R) := by rw [← hξd]; exact hpos
    rcases (div_pos_iff.mp hdiv) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  -- ## `Y` is the value of `w` at the chart point `p i - σ δ₀/2`
  have hhalf : |u t₀ - p i| < δ₀ / 2 := by simpa only [hu] using hcoord
  have hhalf' := abs_lt.mp hhalf
  have hsigmacoord : σ * (u t₀ - p i) > -δ₀ / 2 := by
    rcases hσmem with h | h
    · rw [h, one_mul]; linarith [hhalf'.1]
    · rw [h, neg_one_mul]; linarith [hhalf'.2]
  have hsigmacoord' : σ * (u t₀ - p i) < δ₀ / 2 := by
    rcases hσmem with h | h
    · rw [h, one_mul]; linarith [hhalf'.2]
    · rw [h, neg_one_mul]; linarith [hhalf'.1]
  have hYlt : Y < w t₀ := by
    have h1 : w t₀ = σ * p i + σ * (u t₀ - p i) := by simp only [hw]; ring
    rw [hY, h1]; linarith [hsigmacoord]
  have hσuR : w R = Y - δ₀ / 2 := by
    have habs : |w R - σ * p i| = δ₀ := by
      have h1 : w R - σ * p i = σ * (u R - p i) := by simp only [hw]; ring
      rw [h1, abs_mul, hσabs, one_mul, huR]
    have h2 : w t₀ < σ * p i + δ₀ / 2 := by
      have h3 : w t₀ = σ * p i + σ * (u t₀ - p i) := by simp only [hw]; ring
      rw [h3]; linarith [hsigmacoord']
    rcases (abs_eq (le_of_lt hδ₀)).mp habs with h | h
    · exfalso; linarith [h, h2, hwRlt, hδ₀]
    · linarith [h, hY]
  -- ## The intermediate value `Y` is attained in `(R, t₀]`
  obtain ⟨a, ha_mem, ha_w⟩ :=
    intermediate_value_Icc hRle hwc.continuousOn
      (show Y ∈ Set.Icc (w R) (w t₀) from
        Set.mem_Icc.mpr ⟨by rw [hσuR]; linarith, le_of_lt hYlt⟩)
  obtain ⟨ha1, ha2⟩ := Set.mem_Icc.mp ha_mem
  have ha_lt : a < t₀ := by
    rcases eq_or_lt_of_le ha2 with h | h
    · exfalso; rw [h] at ha_w; linarith [ha_w, hYlt]
    · exact h
  have haS : a ∈ S := by
    refine hIocS (Set.mem_Ioc.mpr ⟨?_, ha2⟩)
    rcases lt_or_eq_of_le ha1 with h | h
    · exact h
    · exfalso
      have h' : w a = w R := by rw [h]
      rw [ha_w] at h'
      linarith [h', hσuR]
  have hga : γ a = G (u a) := hchar_on a ha_lt.le haS
  have hua : u a = p i - σ * δ₀ / 2 := by
    have h1 : σ * w a = σ * Y := by rw [ha_w]
    have h2 : σ * w a = u a := by rw [hw, ← mul_assoc, hσsq, one_mul]
    have h3 : σ * Y = p i - σ * δ₀ / 2 := by
      rw [hY]
      have h4 : σ * (σ * p i - δ₀ / 2) = (σ * σ) * p i - σ * (δ₀ / 2) := by ring
      rw [h4, hσsq, one_mul]; ring
    rw [h2, h3] at h1
    exact h1
  refine ⟨a, ha_lt, ?_⟩
  rw [hga]
  rcases hσmem with h | h
  · left
    have h' : u a = p i - δ₀ / 2 := by rw [h, one_mul] at hua; exact hua
    rw [h']
  · right
    have h' : u a = p i + δ₀ / 2 := by rw [h] at hua; linarith
    rw [h']

end

end Work.Drive
