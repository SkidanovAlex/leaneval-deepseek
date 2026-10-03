import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.section_Bu
import Submission.Work.L62.avail_descent_upper
import Submission.Work.L62.avail_up
import Submission.Work.L62.l62c_end
import Submission.Work.L62.chain
import Submission.Work.Normal.montel_locallyBounded
import Submission.Work.L62C.continuousOn_pair
import Submission.Work.L62C.escape_of_selfmap

/-!
# `Work.L62.cylinder_model` — the holomorphic family `H_β` of §6 on the cylinder

For `β` with `AvailableUp d hd β` (the upper horn `hd.Bu` avoids the critical class of
`ĥ = Ẽ - β`) the pushdown `H_β = pushdown σ_β` of the deep `T`-equivariant section `σ_β` of `Ẽ - β`
over `hd.Bu` (`Work.L62.section_Bu`, `Work.L62.avail_descent_upper`) is a holomorphic self-map of
the cylinder neighbourhood `Ω₀ = {0} ∪ π '' Bu` with

* `H_β 0 = 0`, `deriv H_β 0 = π β = e^{2πiβ}`,
* `pushdown Ẽ (H_β ζ) = π β · ζ` for `ζ ∈ Ω₀`, `ζ ≠ 0`, i.e. `R_β ∘ H_β = id` for
  `R_β = e^{-2πiβ} · pushdown Ẽ = pushdown (Ẽ - β)`.

From `R_β ∘ H_β = id` we get that `H_β` is injective, and since `‖deriv H_β 0‖ = e^{-2π Im β} < 1`
(`Work.L62.avail_up`: `AvailableUp β → 0 < Im β`), the escape lemma
(`Work.L62C.escape_of_selfmap`) shows that the iterates of `H_β` converge to `0` on every compact
subset of `Ω₀`.

Finally, the family is *jointly continuous* in `(β, ζ)`: any two maps satisfying the two relations
above agree near `0` (local injectivity of `R_β` at `0`, since `deriv R_β 0 = π(-β) ≠ 0`), hence on
the connected `Ω₀` by the identity principle.  A normal-family argument then upgrades this
uniqueness to continuity in `β` on the compact box, and the joint continuity follows.
-/

namespace Work.L62

open MandelDim Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-! ## Elementary facts about `π` -/

/-- `π β · π (-β) = 1`. -/
theorem piExp_mul_piExp_neg (β : ℂ) : piExp β * piExp (-β) = 1 := by
  rw [← Work.Repel.PushdownHolo.piExp_mul, add_neg_cancel]
  simp [piExp]

/-- `π (-β) · π β = 1`. -/
theorem piExp_neg_mul (β : ℂ) : piExp (-β) * piExp β = 1 := by
  rw [← Work.Repel.PushdownHolo.piExp_mul, neg_add_cancel]
  simp [piExp]

/-- `‖π β‖ < 1` when `0 < Im β`. -/
theorem norm_piExp_lt_one {β : ℂ} (h : 0 < β.im) : ‖piExp β‖ < 1 := by
  rw [norm_piExp]
  exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])

/-! ## The pushed-down model map `R_β = e^{-2πiβ} · pushdown Ẽ` -/

/-- The pushed-down model map: `R_β = π(-β) · pushdown Ẽ`, which is `pushdown (Ẽ - β)`
(`Work.L62.pushdown_sub`). -/
def Rbeta (d : ParabData g₀ D) (β : ℂ) : ℂ → ℂ := fun ζ => piExp (-β) * pushdown d.E ζ

theorem Rbeta_apply (d : ParabData g₀ D) (β ζ : ℂ) :
    Rbeta d β ζ = pushdown (fun u => d.E u - β) ζ :=
  (pushdown_sub d.E β ζ).symm

theorem Rbeta_zero (d : ParabData g₀ D) (β : ℂ) : Rbeta d β 0 = 0 := by
  simp [Rbeta, Work.Horn.MandelDim.pushdown_zero]

theorem differentiableOn_Rbeta (d : ParabData g₀ D) (hd : HornData d) (β : ℂ) :
    DifferentiableOn ℂ (Rbeta d β) (upOmega d hd) := by
  have hg : DifferentiableOn ℂ (pushdown d.E) (upOmega d hd) :=
    hd.g_holo.mono (by
      intro ζ hζ
      rcases mem_insert_iff.mp hζ with rfl | ⟨w, hw, rfl⟩
      · exact mem_insert_iff.mpr (Or.inl rfl)
      · exact mem_insert_iff.mpr (Or.inr ⟨w, Or.inl hw, rfl⟩))
  exact (differentiableOn_const (c := piExp (-β))).mul hg

theorem analyticsAt_pushdown_zero (d : ParabData g₀ D) (hd : HornData d) :
    AnalyticAt ℂ (pushdown d.E) 0 := by
  have hmem : upOmega d hd ∈ 𝓝 (0 : ℂ) :=
    (isOpen_upOmega d hd).mem_nhds (mem_insert_iff.mpr (Or.inl rfl))
  have hsub : upOmega d hd ⊆ insert 0 (piExp '' (hd.Bu ∪ hd.Bl)) := by
    intro ζ hζ
    rcases mem_insert_iff.mp hζ with rfl | ⟨w, hw, rfl⟩
    · exact mem_insert_iff.mpr (Or.inl rfl)
    · exact mem_insert_iff.mpr (Or.inr ⟨w, Or.inl hw, rfl⟩)
  have han : AnalyticOn ℂ (pushdown d.E) (upOmega d hd) :=
    (hd.g_holo.mono hsub).analyticOn (isOpen_upOmega d hd)
  exact han.analyticAt hmem

theorem deriv_Rbeta_zero (d : ParabData g₀ D) (hd : HornData d) (β : ℂ) :
    deriv (Rbeta d β) 0 = piExp (-β) := by
  have h := HasDerivAt.const_mul (piExp (-β))
    ((analyticsAt_pushdown_zero d hd).differentiableAt.hasDerivAt)
  have h3 : deriv (Rbeta d β) 0 = piExp (-β) * deriv (pushdown d.E) 0 := h.deriv
  rw [Work.Horn.MandelDim.deriv_pushdown_E d, mul_one] at h3
  exact h3

/-- A section of `R_β` is injective. -/
theorem injOn_of_Rbeta_section (d : ParabData g₀ D) (hd : HornData d) {β : ℂ} {H : ℂ → ℂ}
    (hsec : ∀ ζ ∈ upOmega d hd, Rbeta d β (H ζ) = ζ) :
    Set.InjOn H (upOmega d hd) := by
  intro z hz z' hz' heq
  have h1 := hsec z hz
  have h2 := hsec z' hz'
  rw [heq] at h1
  exact h1.symm.trans h2

/-! ## The per-`β` construction -/

/-- **The cylinder map of one available `β`.**  If `β` is available at the upper end, the deep
`T`-equivariant section of `Ẽ - β` over `Bu` pushes down to a holomorphic self-map `H` of
`Ω₀ = {0} ∪ π '' Bu` with `H 0 = 0`, `H'(0) = π β` and `R_β ∘ H = id`. -/
theorem exists_cylinder_map (d : ParabData g₀ D) (hd : HornData d) {β : ℂ}
    (hav : AvailableUp d hd β) :
    ∃ H : ℂ → ℂ, (∀ ζ ∈ upOmega d hd, H ζ ∈ upOmega d hd) ∧
      DifferentiableOn ℂ H (upOmega d hd) ∧ H 0 = 0 ∧ HasDerivAt H (piExp β) 0 ∧
      (∀ ζ ∈ upOmega d hd, ζ ≠ 0 → pushdown d.E (H ζ) = piExp β * ζ) := by
  obtain ⟨y₀, x₀, σ, hy₀, hx₀, hxy, hσd, hσy, hσsec, hσeq, hσasymp⟩ := section_Bu d hd hav
  obtain ⟨H, hH0, hHdiff, hHmem, hHderiv, hHsec⟩ :=
    avail_descent_upper d hd hσd (fun y hy => (hσsec y hy).1) (fun y hy => (hσsec y hy).2)
      hσeq hσasymp
  refine ⟨H, hHmem, hHdiff, hH0, hHderiv, ?_⟩
  intro ζ hζ hζne
  have h1 : pushdown (fun u => d.E u - β) (H ζ) = ζ := hHsec ζ hζ
  have h2 : pushdown (fun u => d.E u - β) (H ζ) = piExp (-β) * pushdown d.E (H ζ) :=
    pushdown_sub d.E β (H ζ)
  have h3 : piExp (-β) * pushdown d.E (H ζ) = ζ := by rw [← h2]; exact h1
  have h4 : pushdown d.E (H ζ) = piExp β * (piExp (-β) * pushdown d.E (H ζ)) := by
    rw [← mul_assoc, piExp_mul_piExp_neg, one_mul]
  rw [h4, h3]

/-! ## Uniqueness of a section near `0` -/

/-- **Uniqueness of a section of `R_β`.**  Two holomorphic maps on `Ω₀` which are sections of
`R_β` near `0` and take the value `0` at `0` coincide on `Ω₀`: `R_β` is locally injective at `0`
because `deriv R_β 0 = π(-β) ≠ 0`, so the two maps agree on a neighbourhood of `0`, and the
identity principle on the preconnected `Ω₀` finishes. -/
theorem eqOn_of_section_near_zero (d : ParabData g₀ D) (hd : HornData d) {β : ℂ}
    {H g : ℂ → ℂ} (hH : DifferentiableOn ℂ H (upOmega d hd))
    (hg : DifferentiableOn ℂ g (upOmega d hd)) (hH0 : H 0 = 0) (hg0 : g 0 = 0)
    {V : Set ℂ} (hV : V ∈ 𝓝 (0 : ℂ)) (hVsub : V ⊆ upOmega d hd)
    (hHsec : ∀ ζ ∈ V, Rbeta d β (H ζ) = ζ) (hgsec : ∀ ζ ∈ V, Rbeta d β (g ζ) = ζ) :
    ∀ ζ ∈ upOmega d hd, g ζ = H ζ := by
  have hΩo : IsOpen (upOmega d hd) := isOpen_upOmega d hd
  have hΩpc : IsPreconnected (upOmega d hd) := preconnected_upOmega d hd
  have h0mem : (0 : ℂ) ∈ upOmega d hd := mem_insert_iff.mpr (Or.inl rfl)
  -- `R_β` is analytic at `0` with nonvanishing derivative
  have hRana : AnalyticAt ℂ (Rbeta d β) 0 :=
    ((differentiableOn_Rbeta d hd β).analyticOn hΩo).analyticAt (hΩo.mem_nhds h0mem)
  have hRder : deriv (Rbeta d β) 0 ≠ 0 := by
    rw [deriv_Rbeta_zero d hd β]
    exact Work.Horn.MandelDim.piExp_ne_zero _
  obtain ⟨U, hU, hUinj⟩ := injOn_nhds_of_analyticAt_deriv_ne_zero hRana hRder
  -- a neighbourhood of `0` on which both maps stay in `U` and the sections are valid
  have hHc : ContinuousAt H 0 := (hH.differentiableAt (hΩo.mem_nhds h0mem)).continuousAt
  have hgc : ContinuousAt g 0 := (hg.differentiableAt (hΩo.mem_nhds h0mem)).continuousAt
  have hHU : H ⁻¹' U ∈ 𝓝 (0 : ℂ) := by
    have h : U ∈ 𝓝 (H 0) := by rw [hH0]; exact hU
    exact hHc.preimage_mem_nhds h
  have hgU : g ⁻¹' U ∈ 𝓝 (0 : ℂ) := by
    have h : U ∈ 𝓝 (g 0) := by rw [hg0]; exact hU
    exact hgc.preimage_mem_nhds h
  have hB : (H ⁻¹' U ∩ g ⁻¹' U ∩ V) ∈ 𝓝 (0 : ℂ) :=
    Filter.inter_mem (Filter.inter_mem hHU hgU) hV
  -- the two maps agree on a neighbourhood of `0`
  have hev : (fun ζ => g ζ - H ζ) =ᶠ[𝓝 (0 : ℂ)] (fun _ => (0 : ℂ)) := by
    filter_upwards [hB] with ζ hζ
    obtain ⟨⟨hζU, hζU'⟩, hζV⟩ := hζ
    have h1 : Rbeta d β (H ζ) = ζ := hHsec ζ hζV
    have h2 : Rbeta d β (g ζ) = ζ := hgsec ζ hζV
    have : g ζ = H ζ := hUinj hζU' hζU (h2.trans h1.symm)
    simp [this]
  have hana : AnalyticOnNhd ℂ (fun ζ => g ζ - H ζ) (upOmega d hd) :=
    (hg.sub hH).analyticOnNhd hΩo
  have hEq : Set.EqOn (fun ζ => g ζ - H ζ) (fun _ => (0 : ℂ)) (upOmega d hd) :=
    hana.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hΩpc h0mem hev
  intro ζ hζ
  exact sub_eq_zero.mp (hEq hζ)

/-! ## The cylinder model -/

theorem cylinder_model {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {b : ℝ} (hb : 0 < b) :
    ∃ H : ℂ → ℂ → ℂ,
      (∀ β : ℂ, Work.L62.AvailableUp d hd β →
        DifferentiableOn ℂ (H β) (insert 0 (piExp '' hd.Bu)) ∧
        Set.MapsTo (H β) (insert 0 (piExp '' hd.Bu)) (insert 0 (piExp '' hd.Bu)) ∧
        H β 0 = 0 ∧ deriv (H β) 0 = Complex.exp (2 * Real.pi * I * β) ∧
        (∀ ζ ∈ insert 0 (piExp '' hd.Bu), ζ ≠ 0 →
          MandelDim.pushdown d.E (H β ζ) = piExp β * ζ)) ∧
      (∀ β : ℂ, Work.L62.AvailableUp d hd β → ∀ δ : ℝ, 0 < δ → ∀ K : Set ℂ,
        K ⊆ insert 0 (piExp '' hd.Bu) → IsCompact K →
          ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ K, ((H β)^[n]) z ∈ Metric.ball 0 δ) ∧
      ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2)
        (({β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} ∩
          {β : ℂ | Work.L62.AvailableUp d hd β}) ×ˢ insert 0 (piExp '' hd.Bu)) := by
  classical
  have key : ∀ β : ℂ, AvailableUp d hd β →
      ∃ H : ℂ → ℂ, (∀ ζ ∈ upOmega d hd, H ζ ∈ upOmega d hd) ∧
        DifferentiableOn ℂ H (upOmega d hd) ∧ H 0 = 0 ∧ HasDerivAt H (piExp β) 0 ∧
        (∀ ζ ∈ upOmega d hd, ζ ≠ 0 → pushdown d.E (H ζ) = piExp β * ζ) :=
    fun β h => exists_cylinder_map d hd h
  let Hf : ℂ → ℂ → ℂ := fun β =>
    if h : AvailableUp d hd β then Classical.choose (key β h) else 0
  have Hf_eq : ∀ β (h : AvailableUp d hd β), Hf β = Classical.choose (key β h) := by
    intro β h
    simp only [Hf]
    rw [dif_pos h]
  have Hf_props : ∀ β (h : AvailableUp d hd β),
      (∀ ζ ∈ upOmega d hd, Hf β ζ ∈ upOmega d hd) ∧
      DifferentiableOn ℂ (Hf β) (upOmega d hd) ∧ Hf β 0 = 0 ∧
      HasDerivAt (Hf β) (piExp β) 0 ∧
      (∀ ζ ∈ upOmega d hd, ζ ≠ 0 → pushdown d.E (Hf β ζ) = piExp β * ζ) := by
    intro β h
    rw [Hf_eq β h]
    exact Classical.choose_spec (key β h)
  have Hf_sec : ∀ β (h : AvailableUp d hd β) {ζ : ℂ}, ζ ∈ upOmega d hd →
      Rbeta d β (Hf β ζ) = ζ := by
    intro β h ζ hζ
    rcases eq_or_ne ζ 0 with rfl | hζne
    · rw [(Hf_props β h).2.2.1]
      exact Rbeta_zero d β
    · have h1 := (Hf_props β h).2.2.2.2 ζ hζ hζne
      have h2 : Rbeta d β (Hf β ζ) = piExp (-β) * (piExp β * ζ) := by
        simp only [Rbeta, h1]
      rw [h2, ← mul_assoc, piExp_neg_mul, one_mul]
  refine ⟨Hf, ?_, ?_, ?_⟩
  · intro β h
    obtain ⟨hmem, hdiff, h0, hder, hsec⟩ := Hf_props β h
    exact ⟨hdiff, hmem, h0, by simpa [piExp] using hder.deriv, hsec⟩
  · intro β h δ hδ K hK hKc
    obtain ⟨hmem, hdiff, h0, hder, hsec⟩ := Hf_props β h
    have hinj : Set.InjOn (Hf β) (upOmega d hd) :=
      injOn_of_Rbeta_section d hd (fun ζ hζ => Hf_sec β h hζ)
    have hderlt : ‖deriv (Hf β) 0‖ < 1 := by
      rw [hder.deriv]
      exact norm_piExp_lt_one (avail_up d hd h)
    exact Work.L62C.escape_of_selfmap (isOpen_upOmega d hd) (isBounded_upOmega d hd)
      (preconnected_upOmega d hd) (mem_insert_iff.mpr (Or.inl rfl)) hdiff hmem h0 hinj hderlt
      δ hδ K hK hKc
  · set Λ : Set ℂ := {β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} ∩
      {β : ℂ | AvailableUp d hd β} with hΛdef
    have hΛav : ∀ β ∈ Λ, AvailableUp d hd β := fun β hβ => hβ.2
    have hloc : ∀ β₀ ∈ Λ, ∀ S ⊆ upOmega d hd, IsCompact S → ∀ ε > 0, ∃ δ > 0,
        ∀ β ∈ Λ, ‖β - β₀‖ < δ → ∀ z ∈ S, ‖Hf β z - Hf β₀ z‖ < ε := by
      intro β₀ hβ₀ S hS hSc ε hε
      by_contra hcon
      push_neg at hcon
      have hex : ∀ n : ℕ, ∃ β ∈ Λ, ‖β - β₀‖ < 1 / (n + 1 : ℝ) ∧
          ∃ z ∈ S, ε ≤ ‖Hf β z - Hf β₀ z‖ :=
        fun n => hcon (1 / ((n : ℝ) + 1)) (by
          have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          have h2 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
          exact one_div_pos.mpr h2)
      set βs : ℕ → ℂ := fun n => Classical.choose (hex n) with hβsdef
      have hβs_mem : ∀ n, βs n ∈ Λ := fun n => (Classical.choose_spec (hex n)).1
      have hβs_lt : ∀ n, ‖βs n - β₀‖ < 1 / (n + 1 : ℝ) :=
        fun n => (Classical.choose_spec (hex n)).2.1
      have hβs_bad : ∀ n, ∃ z ∈ S, ε ≤ ‖Hf (βs n) z - Hf β₀ z‖ :=
        fun n => (Classical.choose_spec (hex n)).2.2
      have hβs_tendsto : Tendsto βs atTop (𝓝 β₀) := by
        rw [Metric.tendsto_atTop]
        intro e he
        obtain ⟨N, hN⟩ := exists_nat_gt (1 / e)
        refine ⟨N + 1, fun n hn => ?_⟩
        have hn' : ((N : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
          have h : ((N + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          push_cast at h
          linarith
        have h1 : (N : ℝ) < (n : ℝ) := by linarith
        have h2 : 1 / e < (n : ℝ) := lt_of_lt_of_le hN h1.le
        have h3 : (1 : ℝ) < e * (n : ℝ) := by
          rw [div_lt_iff₀ he] at h2
          simpa [mul_comm] using h2
        have h4 : (1 : ℝ) < e * ((n : ℝ) + 1) := by nlinarith [h3, he]
        have h5 : 1 / ((n : ℝ) + 1) < e := by
          rw [div_lt_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) + 1)]
          linarith
        rw [dist_eq_norm]
        exact lt_trans (hβs_lt n) h5
      -- the family is normal
      have hbddFam : Work.Normal.IsLocallyBoundedOn (Set.range (fun β : Λ => Hf β.1))
          (upOmega d hd) := by
        intro K hK hKc
        obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
          (isBounded_upOmega d hd)
        refine ⟨R, fun f hf z hz => ?_⟩
        obtain ⟨β, rfl⟩ := hf
        exact mem_closedBall_zero_iff.mp (hR ((Hf_props β.1 (hΛav β.1 β.2)).1 z (hK hz)))
      have hholFam : ∀ f ∈ Set.range (fun β : Λ => Hf β.1),
          DifferentiableOn ℂ f (upOmega d hd) := by
        rintro f ⟨β, rfl⟩
        exact (Hf_props β.1 (hΛav β.1 β.2)).2.1
      have hnormal := Work.Normal.montel_locallyBounded (isOpen_upOmega d hd) hholFam hbddFam
      obtain ⟨φ, hφ, hcase | hcase⟩ := hnormal (fun n => Hf (βs n))
        (fun n => ⟨⟨βs n, hβs_mem n⟩, rfl⟩)
      · obtain ⟨g, hg⟩ := hcase
        have h0mem : (0 : ℂ) ∈ upOmega d hd := mem_insert_iff.mpr (Or.inl rfl)
        have hg0 : g 0 = 0 := by
          have h := hg.tendsto_at h0mem
          have h' : (fun n : ℕ => Hf (βs (φ n)) 0) = fun _ => (0 : ℂ) :=
            funext fun n => (Hf_props (βs (φ n)) (hΛav _ (hβs_mem (φ n)))).2.2.1
          rw [h'] at h
          exact tendsto_nhds_unique h tendsto_const_nhds
        have hghol : DifferentiableOn ℂ g (upOmega d hd) :=
          hg.differentiableOn
            (Eventually.of_forall fun n => (Hf_props (βs (φ n)) (hΛav _ (hβs_mem (φ n)))).2.1)
            (isOpen_upOmega d hd)
        have hgcont : ContinuousAt g 0 :=
          (hghol.differentiableAt ((isOpen_upOmega d hd).mem_nhds h0mem)).continuousAt
        have hV1 : g ⁻¹' upOmega d hd ∈ 𝓝 (0 : ℂ) := by
          have h : upOmega d hd ∈ 𝓝 (g 0) := by
            rw [hg0]; exact (isOpen_upOmega d hd).mem_nhds h0mem
          exact hgcont.preimage_mem_nhds h
        have hV2 : upOmega d hd ∈ 𝓝 (0 : ℂ) := (isOpen_upOmega d hd).mem_nhds h0mem
        obtain ⟨ρ, hρpos, hρ⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hV1 hV2)
        have hsubgdom : upOmega d hd ⊆ insert 0 (piExp '' (hd.Bu ∪ hd.Bl)) := by
          intro ζ hζ
          rcases mem_insert_iff.mp hζ with rfl | ⟨w, hw, rfl⟩
          · exact mem_insert_iff.mpr (Or.inl rfl)
          · exact mem_insert_iff.mpr (Or.inr ⟨w, Or.inl hw, rfl⟩)
        have hgsecBall : ∀ ζ ∈ Metric.ball (0 : ℂ) ρ, Rbeta d β₀ (g ζ) = ζ := by
          intro ζ hζ
          have hζΩ : ζ ∈ upOmega d hd := (hρ hζ).2
          have hgζΩ : g ζ ∈ upOmega d hd := (hρ hζ).1
          have hcont_g : Tendsto (fun n : ℕ => Hf (βs (φ n)) ζ) atTop (𝓝 (g ζ)) :=
            hg.tendsto_at hζΩ
          have htend_beta : Tendsto (fun n : ℕ => βs (φ n)) atTop (𝓝 β₀) :=
            hβs_tendsto.comp hφ.tendsto_atTop
          have ha : Tendsto (fun n : ℕ => piExp (-(βs (φ n)))) atTop (𝓝 (piExp (-β₀))) :=
            (continuous_piExp.tendsto (-β₀)).comp htend_beta.neg
          have hgd : insert 0 (piExp '' (hd.Bu ∪ hd.Bl)) ∈ 𝓝 (g ζ) :=
            Filter.mem_of_superset ((isOpen_upOmega d hd).mem_nhds hgζΩ) hsubgdom
          have hdcont : ContinuousAt (pushdown d.E) (g ζ) :=
            (hd.g_holo.differentiableAt hgd).continuousAt
          have hb : Tendsto (fun n : ℕ => pushdown d.E (Hf (βs (φ n)) ζ)) atTop
              (𝓝 (pushdown d.E (g ζ))) := hdcont.tendsto.comp hcont_g
          have h1 : Tendsto (fun n : ℕ => Rbeta d (βs (φ n)) (Hf (βs (φ n)) ζ)) atTop (𝓝 ζ) := by
            have h' : (fun n : ℕ => Rbeta d (βs (φ n)) (Hf (βs (φ n)) ζ)) = fun _ => ζ :=
              funext fun n => Hf_sec (βs (φ n)) (hΛav _ (hβs_mem (φ n))) hζΩ
            rw [h']
            exact tendsto_const_nhds
          have h2 : Tendsto (fun n : ℕ => Rbeta d (βs (φ n)) (Hf (βs (φ n)) ζ)) atTop
              (𝓝 (Rbeta d β₀ (g ζ))) := by
            have := ha.mul hb
            simpa [Rbeta] using this
          exact (tendsto_nhds_unique h1 h2).symm
        have hballV : Metric.ball (0 : ℂ) ρ ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 hρpos
        have hballsub : Metric.ball (0 : ℂ) ρ ⊆ upOmega d hd := fun ζ hζ => (hρ hζ).2
        have heq : ∀ ζ ∈ upOmega d hd, g ζ = Hf β₀ ζ :=
          eqOn_of_section_near_zero d hd (Hf_props β₀ hβ₀.2).2.1 hghol
            (Hf_props β₀ hβ₀.2).2.2.1 hg0 hballV hballsub
            (fun ζ hζ => Hf_sec β₀ hβ₀.2 (hballsub hζ)) hgsecBall
        have hunif := (Metric.tendstoUniformlyOn_iff.mp
          ((tendstoLocallyUniformlyOn_iff_forall_isCompact (isOpen_upOmega d hd)).mp hg S hS hSc)) ε hε
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hunif
        obtain ⟨z, hzS, hz⟩ := hβs_bad (φ N)
        have h1 : dist (g z) (Hf (βs (φ N)) z) < ε := hN N le_rfl z hzS
        have h2 : dist (Hf β₀ z) (Hf (βs (φ N)) z) < ε := by
          rw [← heq z (hS hzS)]
          exact h1
        rw [dist_eq_norm] at h2
        have h3 : ‖Hf (βs (φ N)) z - Hf β₀ z‖ < ε := by rwa [norm_sub_rev] at h2
        linarith
      · exfalso
        have h0mem : (0 : ℂ) ∈ upOmega d hd := mem_insert_iff.mpr (Or.inl rfl)
        obtain ⟨N, hN⟩ := hcase {0} (by intro z hz; rw [mem_singleton_iff] at hz; rw [hz]; exact h0mem)
          isCompact_singleton (1 : ℝ)
        have hval : (1 : ℝ) ≤ ‖Hf (βs (φ N)) 0‖ := by simpa using hN N le_rfl 0 rfl
        rw [(Hf_props (βs (φ N)) (hΛav _ (hβs_mem (φ N)))).2.2.1] at hval
        norm_num at hval
    have hcontOn : ∀ β ∈ Λ, ContinuousOn (Hf β) (upOmega d hd) :=
      fun β hβ => (Hf_props β (hΛav β hβ)).2.1.continuousOn
    exact Work.L62C.continuousOn_pair hcontOn hloc


end

end Work.L62
