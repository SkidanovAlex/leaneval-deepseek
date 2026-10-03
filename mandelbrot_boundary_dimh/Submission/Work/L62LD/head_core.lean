import Mathlib
import Submission.Work.L62LD.setup
import Submission.Work.L62LD.cyl_family
import Submission.Work.L62LD.escape
import Submission.Work.L62.ratio_bound_family
import Submission.Work.L62.head_confine
import Submission.Work.L62LD.exists_chain_of_sections
import Submission.Work.L62LD.diam_le_of_chain
import Submission.Work.L62LD.dist_int_translate_pos
import Submission.Work.L62LD.sep_chain_const
import Submission.Work.L62LD.lift_confine
import Submission.Work.L62LD.deriv_sigma_iterate
import Submission.Work.L62LD.deriv_section_ball_le
import Submission.Work.L62LD.tube_data

/-!
# L62LD — the parametric lower-end head of Lemma 6.2

`Work.L62LD.head_core` is the main assembly of the proof of
`Work.L62.model_head_down_deep`: for one centre `ζc` and one compact parameter set `Λ` of
parameters on which `ζc` keeps the ball `ball ζc ρb` away from the critical class `hd.v + ℤ`
(`hsec` supplies the inverse branch of `ĥ = d.E - β` over it, with image in a fixed compact
`K₁ ⊆ hd.Bl`), it produces the constants `ρ₀, K, C₀, εsep` of the head with the depth `-M`:
for every `β ∈ Λ` and every `ρ ≤ ρ₀` a chain of discs `W j` (`j ≤ Jesc + 1`) pulled back by
`ĥ`, confined to `K`, of diameter `< 1/2` (and `≤ 1/1000` at the last level), pairwise separated
modulo `ℤ` by `εsep`, and with `W (Jesc + 1)` at depth below `-M`.

The depth comes from the uniform escape of the *cylinder* family `HB HD`
(`Work.L62LD.escape`), the confinement `K` from `Work.L62LD.lift_confine` (cylinder compact +
the exact drift), and the diameter from `Work.L62.ratio_bound_family`.
-/

namespace Work.L62LD

open Classical MandelDim Set Filter Topology
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-! ## The uniform ratio bound for the lower-end cylinder family -/

/-- **The uniform ratio bound for `HB HD` on a fixed compact.**  Instantiating
`Work.L62.ratio_bound_family` for the lower-end cylinder family: on the available box with
uniform drift `κ` the derivative of `(HB HD β)^[j]` at any point of the fixed compact `K_cyl`
has a modulus which is uniformly comparable to `1/‖ζ‖`. -/
theorem ratio_HB {d : MandelDim.ParabData g₀ D} {hd : MandelDim.HornData d} {cl : ℂ}
    (hcl : Filter.Tendsto (fun w => d.E w - w) MandelDim.lowerEnd (nhds cl))
    {HD : ∀ β : ℂ, Work.L62.AvailableDown d hd β → HeadData d hd cl β}
    {b κ : ℝ} {Λ : Set ℂ} (hΛc : IsCompact Λ) (hΛ : Λ ⊆ downBox d hd b)
    (hκ0 : 0 < κ) (hκb : ∀ β ∈ downBox d hd b, β.im ≤ cl.im - κ)
    {K_cyl : Set ℂ} (hKc : IsCompact K_cyl) (hKΩ : K_cyl ⊆ Work.L62.lowOmega d hd)
    (hK0 : (0 : ℂ) ∉ K_cyl) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ β ∈ Λ, ∀ j : ℕ, ∀ ζ ∈ K_cyl,
      C⁻¹ ≤ ‖deriv ((HB HD β)^[j]) ζ * ζ / ((HB HD β)^[j]) ζ‖ ∧
      ‖deriv ((HB HD β)^[j]) ζ * ζ / ((HB HD β)^[j]) ζ‖ ≤ C := by
  obtain ⟨C, hC1, hCres⟩ :=
    Work.L62.ratio_bound_family (Ω := Work.L62.lowOmega d hd) (Λ := Λ) (K := K_cyl)
      (H := HB HD) (lam0 := Real.exp (-(2 * Real.pi * (cl.im + b))))
      (lam1 := Real.exp (-(2 * Real.pi * κ)))
      (Work.L62.isOpen_lowOmega d hd) (Work.L62.isBounded_lowOmega d hd)
      (Work.L62.isPreconnected_lowOmega d hd) (Work.L62.zero_mem_lowOmega d hd)
      hΛc hKc hKΩ hK0 (by positivity)
      (by rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, hκ0])
      (fun β hβ => by
        have hβ' : Work.L62.AvailableDown d hd β := (hΛ hβ).2
        rw [HB_apply (HD := HD) hβ', (HD β hβ').H_deriv.deriv, Work.L62.norm_piExp_lowBall,
          Complex.sub_im]
        constructor
        · rw [Real.exp_le_exp]
          have him : -b ≤ β.im := (abs_le.mp (hΛ hβ).1.2.2).1
          nlinarith [Real.pi_pos]
        · rw [Real.exp_le_exp]
          have hk : κ ≤ cl.im - β.im := by linarith [hκb β (hΛ hβ)]
          nlinarith [Real.pi_pos])
      (fun β hβ => by
        have hβ' : Work.L62.AvailableDown d hd β := (hΛ hβ).2
        rw [HB_apply (HD := HD) hβ']
        exact (HD β hβ').H_holo)
      (fun β hβ => by
        have hβ' : Work.L62.AvailableDown d hd β := (hΛ hβ).2
        rw [HB_apply (HD := HD) hβ']
        exact (HD β hβ').H_map)
      (fun β hβ => by
        have hβ' : Work.L62.AvailableDown d hd β := (hΛ hβ).2
        rw [HB_apply (HD := HD) hβ']
        exact (HD β hβ').H_zero)
      (fun β hβ => by
        have hβ' : Work.L62.AvailableDown d hd β := (hΛ hβ).2
        rw [HB_apply (HD := HD) hβ']
        exact (HD β hβ').H_inj)
      (HB_continuousOn (HD := HD) (b := b) hcl |>.mono (Set.prod_mono_left hΛ))
  exact ⟨C, hC1, hCres⟩

/-! ## The cylinder images of a `σ`-chain -/

/-- `Set.MapsTo` for iterates. -/
private theorem mapsTo_iterate {f : ℂ → ℂ} {S : Set ℂ} (h : Set.MapsTo f S S) (m : ℕ) :
    Set.MapsTo (f^[m]) S S := by
  intro x hx
  induction m with
  | zero => simpa using hx
  | succ k ih => simpa only [Function.iterate_succ_apply'] using h ih

/-- **The `qlow`-images of the iterates of a section.**  If `H ∘ qlow = qlow ∘ σ` on `hd.Bl` and
`σ` maps `hd.Bl` into itself, then `qlow '' (σ^[m] '' A) = (H^[m]) '' (qlow '' A)`. -/
theorem qlow_image_iterate {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {σ H : ℂ → ℂ}
    (hlink : ∀ w ∈ hd.Bl, H (Work.L62.qlow w) = Work.L62.qlow (σ w))
    (hσmem : ∀ w ∈ hd.Bl, σ w ∈ hd.Bl) {A : Set ℂ} (hA : A ⊆ hd.Bl) (m : ℕ) :
    Work.L62.qlow '' ((σ^[m]) '' A) = (H^[m]) '' (Work.L62.qlow '' A) := by
  induction m with
  | zero => simp
  | succ k ih =>
      have hB : (σ^[k]) '' A ⊆ hd.Bl :=
        Set.image_subset_iff.mpr (fun a ha => mapsTo_iterate (fun w hw => hσmem w hw) k (hA ha))
      calc Work.L62.qlow '' ((σ^[k + 1]) '' A)
          = Work.L62.qlow '' (σ '' ((σ^[k]) '' A)) := by
              rw [Function.iterate_succ', Set.image_comp]
        _ = (Work.L62.qlow ∘ σ) '' ((σ^[k]) '' A) := (Set.image_comp _ _ _).symm
        _ = (H ∘ Work.L62.qlow) '' ((σ^[k]) '' A) := by
              apply Set.image_congr
              intro z hz
              exact (hlink z (hB hz)).symm
        _ = H '' (Work.L62.qlow '' ((σ^[k]) '' A)) := Set.image_comp _ _ _
        _ = H '' ((H^[k]) '' (Work.L62.qlow '' A)) := by rw [ih]
        _ = (H^[k + 1]) '' (Work.L62.qlow '' A) := by
              rw [Function.iterate_succ', Set.image_comp]

/-! ## The main parametric head -/

theorem head_core {d : MandelDim.ParabData g₀ D} {hd : MandelDim.HornData d} {cl : ℂ}
    (hcl : Filter.Tendsto (fun w => d.E w - w) MandelDim.lowerEnd (nhds cl))
    {b M : ℝ} (hb : 0 < b) (hM : d.η₀ < M)
    {ζc : ℂ} (hζc : ζc ∉ d.DE)
    {Λ : Set ℂ} (hΛc : IsCompact Λ) (hΛbox : Λ ⊆ downBox d hd b)
    {K₁ : Set ℂ} (hK₁c : IsCompact K₁) (hK₁Bl : K₁ ⊆ hd.Bl)
    {ρb : ℝ} (hρb : 0 < ρb)
    (hsec : ∀ β ∈ Λ, ∃ σ : ℂ → ℂ, DifferentiableOn ℂ σ (Metric.ball ζc ρb) ∧
      (∀ y ∈ Metric.ball ζc ρb, d.E (σ y) - β = y ∧ σ y ∈ K₁))
    (HD : ∀ β : ℂ, Work.L62.AvailableDown d hd β → HeadData d hd cl β)
    {Jesc : ℕ} (hJesc : ∀ β ∈ Λ, ∀ n ≥ Jesc, ∀ z ∈ Work.L62.qlow '' K₁,
      ((HB HD β)^[n]) z ∈ Metric.ball 0 (Real.exp (-(2 * Real.pi * M)) / 2)) :
    ∃ (ρ₀ : ℝ) (K : Set ℂ) (C₀ εsep : ℝ),
        0 < ρ₀ ∧ IsCompact K ∧ K ⊆ hd.Bl ∧ 0 ≤ C₀ ∧ 0 < εsep ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ β ∈ Λ, ∃ W : ℕ → Set ℂ,
          W 0 = Metric.ball ζc ρ ∧
          (∀ j, j ≤ Jesc + 1 → IsOpen (W j) ∧ IsConnected (W j)) ∧
          (∀ j, j < Jesc + 1 → Set.InjOn (fun w => d.E w - β) (W (j + 1)) ∧
            (fun w => d.E w - β) '' W (j + 1) = W j) ∧
          (∀ j, 1 ≤ j → j ≤ Jesc + 1 → W j ⊆ K) ∧
          (∀ i j, i ≤ Jesc + 1 → j ≤ Jesc + 1 → i ≠ j → ∀ u ∈ W i, ∀ v ∈ W j, ∀ k : ℤ,
            εsep ≤ ‖u - v - (k : ℂ)‖) ∧
          (∀ j, j ≤ Jesc + 1 → Bornology.IsBounded (W j) ∧ Metric.diam (W j) < 1 / 2) ∧
          Metric.diam (W (Jesc + 1)) ≤ 1 / 1000 ∧
          (∀ j, j < Jesc + 1 → ∃ u ∈ W j, ∃ u' ∈ W (j + 1), ‖u - u'‖ < C₀) ∧
          (∀ w ∈ W (Jesc + 1), w.im < -M) := by
  classical
  -- ## the uniform drift and the cylinder geometry
  obtain ⟨κ, hκ0, hκb⟩ := exists_drift (d := d) (hd := hd) (cl := cl) hcl b
  have hqlow_cont : Continuous (fun w : ℂ => Work.L62.qlow w) := by
    unfold Work.L62.qlow Work.L62.flip MandelDim.piExp
    fun_prop
  have hKstart_c : IsCompact (Work.L62.qlow '' K₁) :=
    hK₁c.image_of_continuousOn hqlow_cont.continuousOn
  have hKstart_sub : Work.L62.qlow '' K₁ ⊆ Work.L62.lowOmega d hd \ {0} := by
    rintro ζ ⟨w, hw, rfl⟩
    exact ⟨by rw [Work.L62.lowOmega_eq_image_qlow]; exact Or.inr ⟨w, hK₁Bl hw, rfl⟩,
      Work.L62.qlow_ne_zero w⟩
  have hcontΛ : ContinuousOn (fun p : ℂ × ℂ => HB HD p.1 p.2)
      (Λ ×ˢ (Work.L62.lowOmega d hd \ {0})) := by
    refine (HB_continuousOn (HD := HD) (b := b) hcl).mono ?_
    intro p hp
    exact ⟨hΛbox hp.1, hp.2.1⟩
  have hmapΛ : ∀ β ∈ Λ, Set.MapsTo (HB HD β) (Work.L62.lowOmega d hd \ {0})
      (Work.L62.lowOmega d hd \ {0}) := by
    intro β hβ
    have hβ' : Work.L62.AvailableDown d hd β := (hΛbox hβ).2
    rw [HB_apply (HD := HD) hβ']
    intro ζ hζ
    exact ⟨(HD β hβ').H_map hζ.1, (HD β hβ').H_ne ζ hζ.1 hζ.2⟩
  obtain ⟨K_cyl, hKcyl_c, hKcyl_sub, hKcyl⟩ :=
    Work.L62.chain_in_compact (Ω := Work.L62.lowOmega d hd \ {0}) (Λ := Λ)
      (K₁ := Work.L62.qlow '' K₁) (σ := HB HD) (W₁ := fun _ => Work.L62.qlow '' K₁)
      (J := Jesc) hΛc hKstart_c hKstart_sub hcontΛ hmapΛ (fun _ _ => Subset.refl _)
  have hKcylΩ : K_cyl ⊆ Work.L62.lowOmega d hd := fun ζ hζ => (hKcyl_sub hζ).1
  have hKcyl0 : (0 : ℂ) ∉ K_cyl := fun h => (hKcyl_sub h).2 rfl
  obtain ⟨C, hC1, hCrat⟩ := ratio_HB (d := d) (hd := hd) (cl := cl) (HD := HD) hcl hΛc hΛbox hκ0 hκb hKcyl_c hKcylΩ hKcyl0
  -- ## the sections over the ball
  let σb : ℂ → ℂ → ℂ := fun β => if h : β ∈ Λ then Classical.choose (hsec β h) else 0
  have hσb : ∀ β ∈ Λ, DifferentiableOn ℂ (σb β) (Metric.ball ζc ρb) ∧
      (∀ y ∈ Metric.ball ζc ρb, d.E (σb β y) - β = y ∧ σb β y ∈ K₁) := by
    intro β hβ
    have hval : σb β = Classical.choose (hsec β hβ) := dif_pos hβ
    rw [hval]
    exact Classical.choose_spec (hsec β hβ)
  have hσbBl : ∀ β ∈ Λ, ∀ y ∈ Metric.ball ζc ρb, σb β y ∈ hd.Bl :=
    fun β hβ y hy => hK₁Bl ((hσb β hβ).2 y hy).2
  -- ## the global section family over `hd.Bl`
  let σΛ : ℂ → ℂ → ℂ := fun β y => if h : β ∈ Λ then (HD β (hΛbox h).2).σ y else 0
  let HΛ : ℂ → ℂ → ℂ := fun β => if h : β ∈ Λ then (HD β (hΛbox h).2).H else 0
  have hσΛβv : ∀ (β : ℂ) (hβ : β ∈ Λ) (y : ℂ), σΛ β y = (HD β (hΛbox hβ).2).σ y := by
    intro β hβ y
    show (if h : β ∈ Λ then (HD β (hΛbox h).2).σ y else 0) = (HD β (hΛbox hβ).2).σ y
    rw [dif_pos hβ]
  have hσΛβ : ∀ (β : ℂ) (hβ : β ∈ Λ), σΛ β = (HD β (hΛbox hβ).2).σ :=
    fun β hβ => funext (hσΛβv β hβ)
  have hHΛβ : ∀ (β : ℂ) (hβ : β ∈ Λ), HΛ β = (HD β (hΛbox hβ).2).H := fun β hβ => dif_pos hβ
  have hσΛsec : ∀ β ∈ Λ, ∀ y ∈ hd.Bl, d.E (σΛ β y) - β = y := by
    intro β hβ y hy
    rw [hσΛβv β hβ y]
    exact (HD β (hΛbox hβ).2).σ_sec y hy
  have hσΛmem : ∀ β ∈ Λ, ∀ y ∈ hd.Bl, σΛ β y ∈ hd.Bl := by
    intro β hβ y hy
    rw [hσΛβv β hβ y]
    exact (HD β (hΛbox hβ).2).σ_mem y hy
  have hlinkΛ : ∀ β ∈ Λ, ∀ w ∈ hd.Bl, HΛ β (Work.L62.qlow w) = Work.L62.qlow (σΛ β w) := by
    intro β hβ w hw
    have h1 : HΛ β (Work.L62.qlow w) = (HD β (hΛbox hβ).2).H (Work.L62.qlow w) := by
      rw [hHΛβ β hβ]
    have h3 : Work.L62.qlow ((HD β (hΛbox hβ).2).σ w) = Work.L62.qlow (σΛ β w) := by
      rw [hσΛβv β hβ w]
    exact h1.trans ((HD β (hΛbox hβ).2).qlow_link hw |>.trans h3)
  have hHΛeq : ∀ β ∈ Λ, HΛ β = HB HD β := by
    intro β hβ
    rw [hHΛβ β hβ, HB_apply (HD := HD) ((hΛbox hβ).2)]
  have hW₁K : ∀ β ∈ Λ, σb β '' Metric.ball ζc ρb ⊆ K₁ := fun β hβ => fun z hz => by
    rcases hz with ⟨y, hy, hyz⟩
    exact hyz ▸ ((hσb β hβ).2 y hy).2
  have hconfl : ∀ β ∈ Λ, ∀ j ≤ Jesc,
      (HΛ β)^[j] '' (Work.L62.qlow '' (σb β '' Metric.ball ζc ρb)) ⊆ K_cyl := by
    intro β hβ j hj
    calc (HΛ β)^[j] '' (Work.L62.qlow '' (σb β '' Metric.ball ζc ρb))
        ⊆ (HB HD β)^[j] '' (Work.L62.qlow '' K₁) := by
          rw [hHΛeq β hβ]
          exact Set.image_mono (Set.image_mono (hW₁K β hβ))
      _ ⊆ K_cyl := hKcyl β hβ j hj
  -- ## the lift confinement
  obtain ⟨K, hKc, hKBl, hKsub₀⟩ : ∃ K : Set ℂ, IsCompact K ∧ K ⊆ hd.Bl ∧
      ∀ β ∈ Λ, ∀ j ≤ Jesc, ((σΛ β)^[j]) '' (σb β '' Metric.ball ζc ρb) ⊆ K :=
    lift_confine (cl := cl) d hd hΛbox hσΛsec hσΛmem hlinkΛ hK₁c hK₁Bl hKcyl_c hKcylΩ
      (fun ζ hζ hz => hKcyl0 (by rw [hz] at hζ; exact hζ)) hW₁K hconfl
  -- ## the separation from the centre and the tube data
  obtain ⟨ε₀, hε₀0, hε₀⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ k : ℤ, ∀ v ∈ K, ε₀ ≤ ‖(ζc - (k : ℂ)) - v‖ :=
    dist_int_translate_pos d hd hζc hKc hKBl
  obtain ⟨δ, Δ, R, hδ0, hΔ1, hR0, hRK, hKδ, hΔbd⟩ : ∃ (δ Δ R : ℝ), 0 < δ ∧ 1 ≤ Δ ∧ 0 ≤ R ∧
      K ⊆ Metric.closedBall 0 R ∧ (∀ v ∈ K, ∀ z : ℂ, ‖z‖ ≤ δ → v + z ∈ hd.Bl) ∧
      (∀ β : ℂ, ∀ v ∈ K, ∀ z : ℂ, ‖z‖ ≤ δ →
        ‖deriv (fun w => d.E w - β) (v + z)‖ ≤ Δ) :=
    tube_data d hd hKc hKBl
  -- ## the bound of the first-disc section
  obtain ⟨M₁, hM₁⟩ := hK₁c.isBounded.exists_norm_le
  have hR₁0 : 0 ≤ max M₁ 0 := le_max_right _ _
  have hR₁ : ∀ z ∈ K₁, ‖z‖ ≤ max M₁ 0 := fun z hz => le_trans (hM₁ z hz) (le_max_left _ _)
  let Cb : ℝ := max 1 (2 * max M₁ 0 / ρb)
  have hCb1 : 1 ≤ Cb := le_max_left _ _
  have hCb0 : 0 < Cb := lt_of_lt_of_le zero_lt_one hCb1
  have hCCb1 : 1 ≤ C * Cb := le_trans hC1 (le_mul_of_one_le_right (by linarith : (0:ℝ) ≤ C) hCb1)
  have hCCb0 : 0 < C * Cb := lt_of_lt_of_le zero_lt_one hCCb1
  -- ## the constants
  let ρ₀ : ℝ := min (ρb / 2) (min ((8 * (C * Cb))⁻¹)
    (min ((4000 * (C * Cb))⁻¹) (min (ε₀ / 2) δ)))
  have hρ₀pos : 0 < ρ₀ := by
    simp only [ρ₀]
    positivity
  have hεsep_pos : 0 < min (ε₀ / 2) δ / (2 * Δ ^ (Jesc + 1)) := by
    have h1 : 0 < min (ε₀ / 2) δ := lt_min (by linarith) hδ0
    have h2 : 0 < 2 * Δ ^ (Jesc + 1) := by positivity
    positivity
  refine ⟨ρ₀, K, 2 * R + ‖ζc‖ + 1,
    min (ε₀ / 2) δ / (2 * Δ ^ (Jesc + 1)), hρ₀pos, hKc, hKBl, by positivity, hεsep_pos, ?_⟩
  -- ## the per-parameter construction
  intro ρ hρ0 hρρ₀ β hβ
  have h1 : ρ ≤ ρb / 2 := le_trans hρρ₀ (min_le_left _ _)
  have h2 : ρ ≤ (8 * (C * Cb))⁻¹ :=
    le_trans hρρ₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have h3 : ρ ≤ (4000 * (C * Cb))⁻¹ :=
    le_trans hρρ₀ (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have h4 : ρ ≤ ε₀ / 2 := le_trans hρρ₀ (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have h5 : ρ ≤ δ := le_trans hρρ₀ (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  have h6 : ρ ≤ ρb := by linarith
  have h7 : ρ < ρb := by linarith
  have h8 : 2 * ρ * (C * Cb) ≤ 1 / 4 := by
    have hCne : C * Cb ≠ 0 := ne_of_gt hCCb0
    have hval : 2 * (8 * (C * Cb))⁻¹ * (C * Cb) = 1 / 4 := by
      field_simp
      norm_num
    calc 2 * ρ * (C * Cb) ≤ 2 * (8 * (C * Cb))⁻¹ * (C * Cb) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by norm_num))
            (le_of_lt hCCb0)
      _ = 1 / 4 := hval
  have h9 : 2 * ρ * (C * Cb) ≤ 1 / 2000 := by
    have hCne : C * Cb ≠ 0 := ne_of_gt hCCb0
    have hval : 2 * (4000 * (C * Cb))⁻¹ * (C * Cb) = 1 / 2000 := by
      field_simp
      norm_num
    calc 2 * ρ * (C * Cb) ≤ 2 * (4000 * (C * Cb))⁻¹ * (C * Cb) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by norm_num))
            (le_of_lt hCCb0)
      _ = 1 / 2000 := hval
  -- ## the chain
  obtain ⟨W, hW0, hW1, hChain, hWiter⟩ : ∃ W : ℕ → Set ℂ, W 0 = Metric.ball ζc ρ ∧
      W 1 = σb β '' Metric.ball ζc ρ ∧ Chain d hd β W ∧
      ∀ j : ℕ, 1 ≤ j → W j = (((HD β (hΛbox hβ).2).σ)^[j-1]) ''
        (σb β '' Metric.ball ζc ρ) :=
    exists_chain_of_sections d hd hρ0 h6 (hσb β hβ).1
      (fun y hy => ((hσb β hβ).2 y hy).1) (hσbBl β hβ)
      (HD β (hΛbox hβ).2).σ_holo (fun y hy => (HD β (hΛbox hβ).2).σ_mem y hy)
      (fun y hy => (HD β (hΛbox hβ).2).σ_sec y hy)
  have hKsubβ : ∀ j ≤ Jesc, (((HD β (hΛbox hβ).2).σ)^[j]) ''
      (σb β '' Metric.ball ζc ρb) ⊆ K := by
    intro j hj
    have h := hKsub₀ β hβ j hj
    rwa [hσΛβ β hβ] at h
  have hWsub : ∀ j, 1 ≤ j → j ≤ Jesc + 1 → W j ⊆ K := by
    intro j hj1 hjJ
    have hsub : σb β '' Metric.ball ζc ρ ⊆ σb β '' Metric.ball ζc ρb :=
      Set.image_mono (Metric.ball_subset_ball h6)
    have h1' : (((HD β (hΛbox hβ).2).σ)^[j-1]) '' (σb β '' Metric.ball ζc ρ) ⊆
        (((HD β (hΛbox hβ).2).σ)^[j-1]) '' (σb β '' Metric.ball ζc ρb) :=
      Set.image_mono hsub
    rw [hWiter j hj1]
    exact subset_trans h1' (hKsubβ (j - 1) (by omega))
  -- ## the cylinder images of the chain
  have hlinkβ : ∀ w ∈ hd.Bl, HΛ β (Work.L62.qlow w) =
      Work.L62.qlow ((HD β (hΛbox hβ).2).σ w) := by
    intro w hw
    have h1 : HΛ β (Work.L62.qlow w) = (HD β (hΛbox hβ).2).H (Work.L62.qlow w) := by
      rw [hHΛβ β hβ]
    exact h1.trans ((HD β (hΛbox hβ).2).qlow_link hw)
  have hσβmem : ∀ w ∈ hd.Bl, ((HD β (hΛbox hβ).2).σ) w ∈ hd.Bl :=
    fun w hw => (HD β (hΛbox hβ).2).σ_mem w hw
  have hBbl : σb β '' Metric.ball ζc ρ ⊆ hd.Bl := fun z hz => by
    rcases hz with ⟨y, hy, hyz⟩
    exact hyz ▸ hσbBl β hβ y (Metric.ball_subset_ball h6 hy)
  have hiterlink : ∀ m : ℕ, Work.L62.qlow '' ((((HD β (hΛbox hβ).2).σ)^[m]) ''
      (σb β '' Metric.ball ζc ρ)) =
      (HΛ β)^[m] '' (Work.L62.qlow '' (σb β '' Metric.ball ζc ρ)) :=
    fun m => qlow_image_iterate d hd hlinkβ hσβmem hBbl m
  have hWcyl : ∀ j, 1 ≤ j → j ≤ Jesc + 1 → Work.L62.qlow '' W j ⊆ K_cyl := by
    intro j hj1 hjJ
    have hsub : σb β '' Metric.ball ζc ρ ⊆ K₁ := fun z hz => by
      rcases hz with ⟨y, hy, hyz⟩
      exact hyz ▸ ((hσb β hβ).2 y (Metric.ball_subset_ball h6 hy)).2
    have h1' : (HΛ β)^[j-1] '' (Work.L62.qlow '' (σb β '' Metric.ball ζc ρ)) ⊆
        (HB HD β)^[j-1] '' (Work.L62.qlow '' K₁) := by
      rw [hHΛeq β hβ]
      exact Set.image_mono (Set.image_mono hsub)
    rw [hWiter j hj1, hiterlink (j - 1)]
    exact subset_trans h1' (hKcyl β hβ (j - 1) (by omega))
  -- ## the iterates of the section
  have hσβiter : ∀ m : ℕ, DifferentiableOn ℂ (((HD β (hΛbox hβ).2).σ)^[m]) hd.Bl ∧
      Set.MapsTo (((HD β (hΛbox hβ).2).σ)^[m]) hd.Bl hd.Bl := by
    intro m
    induction m with
    | zero => exact ⟨differentiableOn_id, fun x hx => hx⟩
    | succ k ih =>
        constructor
        · rw [Function.iterate_succ']
          exact ((HD β (hΛbox hβ).2).σ_holo).comp ih.1 ih.2
        · rw [Function.iterate_succ']
          intro x hx
          exact (HD β (hΛbox hβ).2).σ_mem _ (ih.2 hx)
  have hEdiff : DifferentiableOn ℂ d.E hd.Bl := differentiableOn_E_of_Bl d hd
  have hiterDiff : ∀ j, j ≤ Jesc + 1 →
      DifferentiableOn ℂ ((fun w => d.E w - β)^[j]) (W j) :=
    iterate_differentiableOn_of_chain (J := Jesc + 1)
      (fun j h1 _ => (hEdiff.sub_const β).mono (hChain.mem_Bl j h1))
      (fun i _ => hChain.img i)
  have hinj_iter : ∀ j, j ≤ Jesc + 1 → Set.InjOn ((fun w => d.E w - β)^[j]) (W j) :=
    iterate_injOn_of_chain (J := Jesc + 1) (fun i _ => hChain.inj i) (fun i _ => hChain.img i)
  -- ## the inverse branch and its derivative bound
  let Ψ : ℕ → ℂ → ℂ := fun j => if h : j = 0 then (id : ℂ → ℂ)
    else (((HD β (hΛbox hβ).2).σ)^[j-1]) ∘ (σb β)
  have hΨd : ∀ j, j ≤ Jesc + 1 → DifferentiableOn ℂ (Ψ j) (Metric.ball ζc ρ) := by
    intro j hj
    by_cases hj0 : j = 0
    · rw [show Ψ j = (id : ℂ → ℂ) from dif_pos hj0]
      exact differentiableOn_id
    · rw [show Ψ j = (((HD β (hΛbox hβ).2).σ)^[j-1]) ∘ (σb β) from dif_neg hj0]
      exact ((hσβiter (j - 1)).1).comp
        ((hσb β hβ).1.mono (Metric.ball_subset_ball h6))
        (fun y hy => hσbBl β hβ y (Metric.ball_subset_ball h6 hy))
  have hΨmem : ∀ j, j ≤ Jesc + 1 → ∀ u ∈ Metric.ball ζc ρ, Ψ j u ∈ W j := by
    intro j hj u hu
    by_cases hj0 : j = 0
    · rw [show Ψ j = (id : ℂ → ℂ) from dif_pos hj0, hj0, hW0]
      exact hu
    · rw [show Ψ j = (((HD β (hΛbox hβ).2).σ)^[j-1]) ∘ (σb β) from dif_neg hj0,
        hWiter j (Nat.one_le_iff_ne_zero.mpr hj0)]
      exact ⟨(σb β) u, ⟨u, hu, rfl⟩, rfl⟩
  have hiter_σγ : ∀ m : ℕ, ∀ y ∈ hd.Bl, ((fun w => d.E w - β)^[m])
      ((((HD β (hΛbox hβ).2).σ)^[m]) y) = y := by
    intro m
    induction m with
    | zero => intro y hy; rfl
    | succ k ih =>
        intro y hy
        have hyk : (((HD β (hΛbox hβ).2).σ)^[k]) y ∈ hd.Bl := (hσβiter k).2 hy
        have h1' : (((HD β (hΛbox hβ).2).σ)^[k+1]) y
            = ((HD β (hΛbox hβ).2).σ) ((((HD β (hΛbox hβ).2).σ)^[k]) y) := by
          rw [Function.iterate_succ_apply']
        have h2' : d.E (((HD β (hΛbox hβ).2).σ)
            ((((HD β (hΛbox hβ).2).σ)^[k]) y)) - β = (((HD β (hΛbox hβ).2).σ)^[k]) y :=
          (HD β (hΛbox hβ).2).σ_sec _ hyk
        rw [h1']
        rw [Function.iterate_succ_apply]
        rw [h2']
        exact ih y hy
  have hΨinv : ∀ j, j ≤ Jesc + 1 → ∀ u ∈ Metric.ball ζc ρ,
      ((fun w => d.E w - β)^[j]) (Ψ j u) = u := by
    intro j hj u hu
    by_cases hj0 : j = 0
    · subst hj0
      rw [show Ψ 0 = (id : ℂ → ℂ) from dif_pos rfl]
      simp
    · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
      rw [show Ψ j = (((HD β (hΛbox hβ).2).σ)^[j-1]) ∘ (σb β) from dif_neg hj0]
      simp only [Function.comp_apply]
      have hzu : (σb β) u ∈ hd.Bl := hσbBl β hβ u (Metric.ball_subset_ball h6 hu)
      have h4' : ((fun w => d.E w - β)^[j-1])
          ((((HD β (hΛbox hβ).2).σ)^[j-1]) ((σb β) u)) = (σb β) u := hiter_σγ (j-1) _ hzu
      have h5' : ((fun w => d.E w - β)^[j])
          ((((HD β (hΛbox hβ).2).σ)^[j-1]) ((σb β) u)) =
          (fun w => d.E w - β) (((fun w => d.E w - β)^[j-1])
            ((((HD β (hΛbox hβ).2).σ)^[j-1]) ((σb β) u))) := by
        nth_rewrite 1 [show j = (j - 1) + 1 by omega]
        rw [Function.iterate_succ_apply']
      rw [h5', h4']
      exact ((hσb β hβ).2 u (Metric.ball_subset_ball h6 hu)).1
  have hΨbound : ∀ j, j ≤ Jesc + 1 → ∀ u ∈ Metric.ball ζc ρ, ‖deriv (Ψ j) u‖ ≤ C * Cb := by
    intro j hj u hu
    by_cases hj0 : j = 0
    · rw [show Ψ j = (id : ℂ → ℂ) from dif_pos hj0]
      simpa using hCCb1
    · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
      rw [show Ψ j = (((HD β (hΛbox hβ).2).σ)^[j-1]) ∘ (σb β) from dif_neg hj0]
      have hzu : (σb β) u ∈ hd.Bl := hσbBl β hβ u (Metric.ball_subset_ball h6 hu)
      have h1W : W 1 = σb β '' Metric.ball ζc ρ := hW1
      have hzq : Work.L62.qlow ((σb β) u) ∈ K_cyl :=
        hWcyl 1 le_rfl (by omega)
          ⟨(σb β) u, by rw [hW1]; exact ⟨u, hu, rfl⟩, rfl⟩
      have hziter : ∀ t : ℕ, t < j - 1 → (((HD β (hΛbox hβ).2).σ)^[t]) ((σb β) u) ∈ hd.Bl := by
        intro t ht
        have hmem : (((HD β (hΛbox hβ).2).σ)^[t]) ((σb β) u) ∈ W (t+1) := by
          rw [hWiter (t+1) (Nat.succ_le_succ (Nat.zero_le t))]
          exact ⟨(σb β) u, ⟨u, hu, rfl⟩, rfl⟩
        exact hChain.mem_Bl (t+1) (Nat.succ_le_succ (Nat.zero_le t)) hmem
      have hσderiv : deriv (((HD β (hΛbox hβ).2).σ)^[j-1]) ((σb β) u) =
          deriv ((HΛ β)^[j-1]) (Work.L62.qlow ((σb β) u)) * Work.L62.qlow ((σb β) u) /
            ((HΛ β)^[j-1]) (Work.L62.qlow ((σb β) u)) := by
        rw [hHΛβ β hβ]
        exact deriv_sigma_iterate d hd (HD β (hΛbox hβ).2).σ_holo
          (fun w hw => (HD β (hΛbox hβ).2).σ_mem w hw)
          (fun w hw => (HD β (hΛbox hβ).2).σ_sec w hw)
          (HD β (hΛbox hβ).2).H_holo (HD β (hΛbox hβ).2).H_map
          (fun w hw => (HD β (hΛbox hβ).2).qlow_link hw) ((σb β) u) (j-1) hziter
      have hσbd_le : ‖deriv (σb β) u‖ ≤ Cb := by
        have hle := deriv_section_ball_le (ζc := ζc) (ρ := ρ) (ρb := ρb) (R₁ := max M₁ 0)
          h7 hR₁0 (hσb β hβ).1 (fun y hy => hR₁ _ ((hσb β hβ).2 y hy).2) u hu
        refine le_trans hle ?_
        have h2R : ρb - ρ ≥ ρb / 2 := by linarith
        have hnum : max M₁ 0 / (ρb - ρ) ≤ max M₁ 0 / (ρb / 2) :=
          div_le_div_of_nonneg_left hR₁0 (by linarith) h2R
        have hval : max M₁ 0 / (ρb / 2) = 2 * max M₁ 0 / ρb := by
          field_simp
        rw [hval] at hnum
        exact le_trans hnum (le_max_right _ _)
      have hσpow_le : ‖deriv (((HD β (hΛbox hβ).2).σ)^[j-1]) ((σb β) u)‖ ≤ C := by
        rw [hσderiv, hHΛeq β hβ]
        exact (hCrat β hβ (j-1) (Work.L62.qlow ((σb β) u)) hzq).2
      have hfdiff : DifferentiableAt ℂ (((HD β (hΛbox hβ).2).σ)^[j-1]) ((σb β) u) :=
        ((hσβiter (j-1)).1).differentiableAt (hd.Bl_open.mem_nhds hzu)
      have hgdiff : DifferentiableAt ℂ (σb β) u :=
        ((hσb β hβ).1).differentiableAt
          (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball h6 hu))
      rw [deriv_comp u hfdiff hgdiff, norm_mul]
      exact mul_le_mul hσpow_le hσbd_le (norm_nonneg _) (le_trans zero_le_one hC1)
  -- ## the ratio bound along the chain
  have hratio : ∀ j, 1 ≤ j → j ≤ Jesc + 1 → ∀ w ∈ W j,
      ((C * Cb))⁻¹ ≤ ‖deriv ((fun w => d.E w - β)^[j]) w‖ := by
    intro j hj1 hjJ w hw
    have hu : ((fun w => d.E w - β)^[j]) w ∈ Metric.ball ζc ρ := by
      have hm := hChain.iterate_mem (le_refl j) hw
      rw [Nat.sub_self] at hm
      rwa [hW0] at hm
    have hrepr : Ψ j (((fun w => d.E w - β)^[j]) w) = w :=
      hinj_iter j hjJ (hΨmem j hjJ _ hu) hw (hΨinv j hjJ _ hu)
    have hderivψ : ‖deriv (Ψ j) (((fun w => d.E w - β)^[j]) w)‖ ≤ C * Cb := hΨbound j hjJ _ hu
    have hkey : deriv ((fun w => d.E w - β)^[j]) (Ψ j (((fun w => d.E w - β)^[j]) w)) *
        deriv (Ψ j) (((fun w => d.E w - β)^[j]) w) = 1 := by
      have hev : ((fun w => d.E w - β)^[j]) ∘ (Ψ j) =ᶠ[𝓝 (((fun w => d.E w - β)^[j]) w)] id := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hu] with y hy
        exact hΨinv j hjJ y hy
      have hd1 : DifferentiableAt ℂ (Ψ j) (((fun w => d.E w - β)^[j]) w) :=
        (hΨd j hjJ).differentiableAt (Metric.isOpen_ball.mem_nhds hu)
      have hd2 : DifferentiableAt ℂ ((fun w => d.E w - β)^[j])
          (Ψ j (((fun w => d.E w - β)^[j]) w)) := by
        rw [hrepr]
        exact (hiterDiff j hjJ).differentiableAt ((hChain.opconn j).1.mem_nhds hw)
      have hone : deriv (((fun w => d.E w - β)^[j]) ∘ (Ψ j))
          (((fun w => d.E w - β)^[j]) w) = 1 := by
        have hbase : HasDerivAt (id : ℂ → ℂ) 1 (((fun w => d.E w - β)^[j]) w) :=
          hasDerivAt_id _
        exact (hbase.congr_of_eventuallyEq hev).deriv
      have hcomp := deriv_comp (((fun w => d.E w - β)^[j]) w) hd2 hd1
      rw [hone] at hcomp
      exact hcomp.symm
    rw [hrepr] at hkey
    have hnorm : ‖deriv ((fun w => d.E w - β)^[j]) w‖
        * ‖deriv (Ψ j) (((fun w => d.E w - β)^[j]) w)‖ = 1 := by
      rw [← norm_mul, hkey, norm_one]
    have hBpos : 0 < ‖deriv (Ψ j) (((fun w => d.E w - β)^[j]) w)‖ := by
      by_contra hcon
      push_neg at hcon
      have h0 : ‖deriv (Ψ j) (((fun w => d.E w - β)^[j]) w)‖ = 0 :=
        le_antisymm hcon (norm_nonneg _)
      rw [h0, mul_zero] at hnorm
      exact one_ne_zero hnorm.symm
    have hlast : 1 / ‖deriv (Ψ j) (((fun w => d.E w - β)^[j]) w)‖
        = ‖deriv ((fun w => d.E w - β)^[j]) w‖ := by
      rw [div_eq_iff hBpos.ne']
      exact hnorm.symm
    rw [← hlast]
    simpa [one_div] using one_div_le_one_div_of_le hBpos hderivψ
  -- ## the diameter clause
  have hdiam : ∀ j, j ≤ Jesc + 1 → Metric.diam (W j) ≤ 2 * ρ * (C * Cb) :=
    diam_le_of_chain d hd hρ0 hCCb1 hChain hW0 hΨd hΨmem hΨinv hratio
  -- ## the separation input
  have hsep0 : ∀ m, 1 ≤ m → m ≤ Jesc + 1 → ∀ u ∈ W 0, ∀ v ∈ W m, ∀ k : ℤ,
      ε₀ / 2 ≤ ‖u - v - (k : ℂ)‖ := by
    intro m hm1 hmJ u hu v hv k
    have hu' : ‖u - ζc‖ < ρ := by
      rw [hW0] at hu
      simpa [Metric.mem_ball, dist_eq_norm] using hu
    have hvK : v ∈ K := hWsub m hm1 hmJ hv
    have h1' : ε₀ ≤ ‖(ζc - (k : ℂ)) - v‖ := hε₀ k v hvK
    have h2' : ‖(ζc - (k : ℂ)) - v‖ ≤ ‖u - v - (k : ℂ)‖ + ‖u - ζc‖ := by
      have heq : (ζc - (k : ℂ)) - v = (u - v - (k : ℂ)) - (u - ζc) := by ring
      rw [heq]
      exact norm_sub_le _ _
    linarith
  have hsep : ∀ i j, i ≤ Jesc + 1 → j ≤ Jesc + 1 → i ≠ j → ∀ u ∈ W i, ∀ v ∈ W j, ∀ k : ℤ,
      min (ε₀ / 2) δ / (2 * Δ ^ (Jesc + 1)) ≤ ‖u - v - (k : ℂ)‖ :=
    sep_chain_const d hd hρ0 (by linarith) hδ0 hΔ1 hEdiff hKδ
      (fun v hv z hz => hΔbd β v hv z hz) hChain hW0 hWsub hsep0
  -- ## the final assembly
  refine ⟨W, hW0, fun j _ => hChain.opconn j, fun j _ => ⟨hChain.inj j, hChain.img j⟩,
    hWsub, hsep, ?_, ?_, ?_, ?_⟩
  · intro j hj
    constructor
    · by_cases hj0 : j = 0
      · rw [hj0, hW0]
        exact (isCompact_closedBall ζc ρ).isBounded.subset Metric.ball_subset_closedBall
      · exact hKc.isBounded.subset (hWsub j (Nat.one_le_iff_ne_zero.mpr hj0) hj)
    · have := hdiam j hj
      linarith
  · have := hdiam (Jesc + 1) le_rfl
    linarith
  · intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      refine ⟨ζc, by rw [hW0]; exact Metric.mem_ball_self hρ0, (σb β) ζc, ?_, ?_⟩
      · rw [hW1]
        exact ⟨ζc, Metric.mem_ball_self hρ0, rfl⟩
      · have h1' : ‖ζc - (σb β) ζc‖ ≤ ‖ζc‖ + ‖(σb β) ζc‖ := norm_sub_le _ _
        have h2' : ‖(σb β) ζc‖ ≤ R := by
          have hmem : (σb β) ζc ∈ K :=
            hKsub₀ β hβ 0 (Nat.zero_le _)
              ⟨(σb β) ζc, ⟨ζc, Metric.mem_ball_self hρb, rfl⟩, rfl⟩
          simpa [Metric.mem_closedBall, dist_eq_norm] using hRK hmem
        linarith
    · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
      have hjJ : j ≤ Jesc := by omega
      refine ⟨(((HD β (hΛbox hβ).2).σ)^[j-1]) ((σb β) ζc), ?_,
        ((HD β (hΛbox hβ).2).σ) ((((HD β (hΛbox hβ).2).σ)^[j-1]) ((σb β) ζc)), ?_, ?_⟩
      · rw [hWiter j hj1]
        exact ⟨(σb β) ζc, ⟨ζc, Metric.mem_ball_self hρ0, rfl⟩, rfl⟩
      · rw [hWiter (j+1) (by omega)]
        refine ⟨(σb β) ζc, ⟨ζc, Metric.mem_ball_self hρ0, rfl⟩, ?_⟩
        rw [show j + 1 - 1 = (j - 1) + 1 by omega, Function.iterate_succ_apply']
      · have hmem1 : (((HD β (hΛbox hβ).2).σ)^[j-1]) ((σb β) ζc) ∈ K :=
          hWsub j hj1 (by omega) (by
            rw [hWiter j hj1]
            exact ⟨(σb β) ζc, ⟨ζc, Metric.mem_ball_self hρ0, rfl⟩, rfl⟩)
        have hmem2 : ((HD β (hΛbox hβ).2).σ)
            ((((HD β (hΛbox hβ).2).σ)^[j-1]) ((σb β) ζc)) ∈ K :=
          hWsub (j+1) (by omega) (by omega) (by
            rw [hWiter (j+1) (by omega)]
            refine ⟨(σb β) ζc, ⟨ζc, Metric.mem_ball_self hρ0, rfl⟩, ?_⟩
            rw [show j + 1 - 1 = (j - 1) + 1 by omega, Function.iterate_succ_apply'])
        have hb1 := hRK hmem1
        have hb2 := hRK hmem2
        rw [Metric.mem_closedBall, dist_zero_right] at hb1 hb2
        have hthis := norm_sub_le ((((HD β (hΛbox hβ).2).σ)^[j-1]) ((σb β) ζc))
          (((HD β (hΛbox hβ).2).σ) ((((HD β (hΛbox hβ).2).σ)^[j-1]) ((σb β) ζc)))
        have hnc : (0:ℝ) ≤ ‖ζc‖ := norm_nonneg _
        linarith
  · intro w hw
    have hmem : Work.L62.qlow w ∈ (HB HD β)^[Jesc] '' (Work.L62.qlow '' K₁) := by
      have hq : Work.L62.qlow w ∈ Work.L62.qlow '' W (Jesc + 1) := ⟨w, hw, rfl⟩
      have hlinkm : Work.L62.qlow '' W (Jesc + 1) =
          (HΛ β)^[Jesc] '' (Work.L62.qlow '' (σb β '' Metric.ball ζc ρ)) := by
        have hWm : W (Jesc + 1) = (((HD β (hΛbox hβ).2).σ)^[Jesc]) ''
            (σb β '' Metric.ball ζc ρ) := by
          have hWr := hWiter (Jesc + 1) (by omega)
          rwa [show Jesc + 1 - 1 = Jesc by omega] at hWr
        rw [hWm, hiterlink Jesc]
      rw [hlinkm, hHΛeq β hβ] at hq
      refine Set.image_mono (Set.image_mono ?_) hq
      intro z hz
      rcases hz with ⟨y, hy, hyz⟩
      exact hyz ▸ ((hσb β hβ).2 y (Metric.ball_subset_ball h6 hy)).2
    obtain ⟨z, hz, hzw⟩ := hmem
    have hball := hJesc β hβ Jesc le_rfl z hz
    rw [hzw] at hball
    rw [Metric.mem_ball, dist_zero_right] at hball
    have hlt : Real.exp (2 * Real.pi * w.im) < Real.exp (-(2 * Real.pi * M)) := by
      rw [← Work.L62.norm_qlow w]
      have hpos : 0 < Real.exp (-(2 * Real.pi * M)) := Real.exp_pos _
      linarith
    have := Real.exp_lt_exp.mp hlt
    nlinarith [Real.pi_pos]


end

end Work.L62LD
