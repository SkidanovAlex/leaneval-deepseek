import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.l62c_end
import Submission.Work.L62LD.setup
import Submission.Work.L62LD.head_core
import Submission.Work.L62LD.headDataExists
import Submission.Work.L62HD.section_over_ball_in_compact
import Submission.Work.L62.int_separation

namespace Work.L62

/-- **The head of the chain of Lemma 6.2 at the lower end, with prescribed depth and a
quantitative separation** — the mirror of `model_head_up_deep`, with `AvailableDown d hd β` (so
`β.im < cl.im` by `Work.L62.avail_down`, `0 < cl.im` by `HornData.cl_im_pos`), `K ⊆ hd.Bl` and
the depth `-M`.  The lower end lives at `∞` in the cylinder (`|π w| → +∞` as `Im w → -∞`) and the
inverse branch there contracts with multiplier `exp (2π (Im β - Im cl))`, of modulus `< 1` by
`avail_down`; mirror `preimage_box`, the escape (on the inverted coordinate `1/ζ`) and the
Fatou-coordinate disjointness argument of the upper case. -/
theorem model_head_down_deep {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d)
    {cl : ℂ} (hcl : Filter.Tendsto (fun w => d.E w - w) MandelDim.lowerEnd (nhds cl))
    {b M : ℝ} (hb : 0 < b) (hM : d.η₀ < M)
    {ζa ζb : ℂ} (hζa : ζa ∉ d.DE) (hζb : ζb ∉ d.DE)
    (hsep : ∀ k : ℤ, ζa ≠ ζb + (k : ℂ)) :
    ∃ (ρ₀ : ℝ) (K : Set ℂ) (C₀ εsep : ℝ) (J : ℕ),
      0 < ρ₀ ∧ IsCompact K ∧ K ⊆ hd.Bl ∧ 0 ≤ C₀ ∧ 0 < εsep ∧ 0 < J ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ β : ℂ, 0 ≤ β.re → β.re ≤ 1 → |β.im| ≤ b →
        Work.L62.AvailableDown d hd β →
        ∃ W : ℕ → Set ℂ,
          (W 0 = Metric.ball ζa ρ ∨ W 0 = Metric.ball ζb ρ) ∧
          (∀ j, j ≤ J → IsOpen (W j) ∧ IsConnected (W j)) ∧
          (∀ j, j < J → Set.InjOn (fun w => d.E w - β) (W (j + 1)) ∧
            (fun w => d.E w - β) '' W (j + 1) = W j) ∧
          (∀ j, 1 ≤ j → j ≤ J → W j ⊆ K) ∧
          (∀ i j, i ≤ J → j ≤ J → i ≠ j → ∀ u ∈ W i, ∀ v ∈ W j, ∀ k : ℤ,
            εsep ≤ ‖u - v - (k : ℂ)‖) ∧
          (∀ j, j ≤ J → Bornology.IsBounded (W j) ∧ Metric.diam (W j) < 1 / 2) ∧
          Metric.diam (W J) ≤ 1 / 1000 ∧
          (∀ j, j < J → ∃ u ∈ W j, ∃ u' ∈ W (j + 1), ‖u - u'‖ < C₀) ∧
          (∀ w ∈ W J, w.im < -M) := by
  classical
  -- ## the provider of the lower-end head data
  obtain ⟨HD⟩ : Nonempty (∀ β : ℂ, Work.L62.AvailableDown d hd β → Work.L62LD.HeadData d hd cl β) :=
    Work.L62LD.headDataExists d hd hcl
  -- ## the separation of the two centres from `ℤ` and the two radii
  have hsep' : ∀ k : ℤ, (ζa - ζb) ≠ (k : ℂ) := fun k hk => hsep k (by linear_combination hk)
  obtain ⟨δ₀, hδ₀0, hδ₀⟩ := Work.L62.int_separation (x := ζa - ζb) hsep'
  set τ : ℝ := δ₀ / 4 with hτdef
  set ρb : ℝ := δ₀ / 16 with hρbdef
  have hτ2 : 2 * τ < δ₀ := by rw [hτdef]; linarith
  have hρb0 : 0 < ρb := by rw [hρbdef]; linarith
  have h2ρbτ : 2 * ρb < τ := by rw [hρbdef, hτdef]; linarith
  -- ## the two Work.L62LD.good parameter sets
  set Λa : Set ℂ := Work.L62LD.downBox d hd b ∩ Work.L62LD.good ζa hd.v τ with hΛadef
  set Λb : Set ℂ := Work.L62LD.downBox d hd b ∩ Work.L62LD.good ζb hd.v τ with hΛbdef
  have hΛac : IsCompact Λa := by
    rw [hΛadef]
    exact Work.L62LD.isCompact_downBox_inter_good (d := d) (hd := hd) (ζ₀ := ζa) (τ := τ) (b := b)
  have hΛbc : IsCompact Λb := by
    rw [hΛbdef]
    exact Work.L62LD.isCompact_downBox_inter_good (d := d) (hd := hd) (ζ₀ := ζb) (τ := τ) (b := b)
  have hΛabox : Λa ⊆ Work.L62LD.downBox d hd b := by rw [hΛadef]; exact Set.inter_subset_left
  have hΛbbox : Λb ⊆ Work.L62LD.downBox d hd b := by rw [hΛbdef]; exact Set.inter_subset_left
  have hcover : Work.L62LD.downBox d hd b ⊆ Λa ∪ Λb := by
    have hcov := Work.L62LD.downBox_subset_good_union (d := d) (hd := hd) (ζa := ζa) (ζb := ζb)
      (δ := δ₀) (τ := τ) hδ₀0 hδ₀ hτ2 b
    intro β hβ
    rcases hcov hβ with h | h
    · exact Or.inl (by rw [hΛadef]; exact ⟨hβ, h⟩)
    · exact Or.inr (by rw [hΛbdef]; exact ⟨hβ, h⟩)
  -- ## the sections of `ĥ_β` over the two centre balls
  obtain ⟨K₁a, hK₁ac, hK₁aBl, hseca'⟩ :=
    Work.L62HD.section_over_ball_in_compact d hd (ζ₀ := ζa) (ρ₀ := ρb) hρb0 hΛac
      (fun β hβ k => Work.L62LD.good_havoid (ζ₀ := ζa) (v := hd.v) (τ := τ) (ρ := ρb)
        h2ρbτ (β := β) hβ.2 k)
  obtain ⟨K₁b, hK₁bc, hK₁bBl, hsecb'⟩ :=
    Work.L62HD.section_over_ball_in_compact d hd (ζ₀ := ζb) (ρ₀ := ρb) hρb0 hΛbc
      (fun β hβ k => Work.L62LD.good_havoid (ζ₀ := ζb) (v := hd.v) (τ := τ) (ρ := ρb)
        h2ρbτ (β := β) hβ.2 k)
  have hseca : ∀ β ∈ Λa, ∃ σ : ℂ → ℂ, DifferentiableOn ℂ σ (Metric.ball ζa ρb) ∧
      (∀ y ∈ Metric.ball ζa ρb, d.E (σ y) - β = y ∧ σ y ∈ K₁a) := by
    intro β hβ
    obtain ⟨σ, hσd, hσs, hσK⟩ := hseca' β hβ
    refine ⟨σ, hσd, fun y hy => ⟨?_, hσK y hy⟩⟩
    rw [(hσs y hy).2]
    ring
  have hsecb : ∀ β ∈ Λb, ∃ σ : ℂ → ℂ, DifferentiableOn ℂ σ (Metric.ball ζb ρb) ∧
      (∀ y ∈ Metric.ball ζb ρb, d.E (σ y) - β = y ∧ σ y ∈ K₁b) := by
    intro β hβ
    obtain ⟨σ, hσd, hσs, hσK⟩ := hsecb' β hβ
    refine ⟨σ, hσd, fun y hy => ⟨?_, hσK y hy⟩⟩
    rw [(hσs y hy).2]
    ring
  -- ## the uniform escape time
  set K₁ : Set ℂ := K₁a ∪ K₁b with hK₁def
  have hK₁c : IsCompact K₁ := by rw [hK₁def]; exact hK₁ac.union hK₁bc
  have hK₁Bl : K₁ ⊆ hd.Bl := by
    rw [hK₁def]; exact Set.union_subset hK₁aBl hK₁bBl
  have hqlow_cont : Continuous (fun w : ℂ => Work.L62.qlow w) := by
    unfold Work.L62.qlow Work.L62.flip MandelDim.piExp
    fun_prop
  have hK₁Ω : Work.L62.qlow '' K₁ ⊆ Work.L62.lowOmega d hd := by
    rintro ζ ⟨w, hw, rfl⟩
    rw [Work.L62.lowOmega_eq_image_qlow]
    exact Or.inr ⟨w, hK₁Bl hw, rfl⟩
  have hK₁c' : IsCompact (Work.L62.qlow '' K₁) :=
    hK₁c.image_of_continuousOn hqlow_cont.continuousOn
  obtain ⟨κ, hκ0, hκb⟩ := Work.L62LD.exists_drift (d := d) (hd := hd) (cl := cl) hcl b
  have heps : 0 < Real.exp (-(2 * Real.pi * M)) / 2 := by positivity
  obtain ⟨Jesc, hJesc_total⟩ :=
    Work.L62LD.HB_uniform_escape (HD := HD) hcl hκ0 hκb hK₁c' hK₁Ω heps
  have hJesc_a : ∀ β ∈ Λa, ∀ n ≥ Jesc, ∀ z ∈ Work.L62.qlow '' K₁a,
      ((Work.L62LD.HB HD β)^[n]) z ∈ Metric.ball 0 (Real.exp (-(2 * Real.pi * M)) / 2) :=
    fun β hβ n hn z hz =>
      hJesc_total β (hΛabox hβ) n hn z (by rw [hK₁def]; exact Set.image_mono Set.subset_union_left hz)
  have hJesc_b : ∀ β ∈ Λb, ∀ n ≥ Jesc, ∀ z ∈ Work.L62.qlow '' K₁b,
      ((Work.L62LD.HB HD β)^[n]) z ∈ Metric.ball 0 (Real.exp (-(2 * Real.pi * M)) / 2) :=
    fun β hβ n hn z hz =>
      hJesc_total β (hΛbbox hβ) n hn z (by rw [hK₁def]; exact Set.image_mono Set.subset_union_right hz)
  -- ## the two halves of the head
  obtain ⟨ρ₀a, Ka, C₀a, εsepa, hρ₀a, hKac, hKaBl, hC₀a, hεa, hmaina⟩ :=
    Work.L62LD.head_core (d := d) (hd := hd) (cl := cl) hcl hb hM hζa hΛac hΛabox
      hK₁ac hK₁aBl hρb0 hseca HD hJesc_a
  obtain ⟨ρ₀b, Kb, C₀b, εsepb, hρ₀b, hKbc, hKbBl, hC₀b, hεb, hmainb⟩ :=
    Work.L62LD.head_core (d := d) (hd := hd) (cl := cl) hcl hb hM hζb hΛbc hΛbbox
      hK₁bc hK₁bBl hρb0 hsecb HD hJesc_b
  -- ## the assembly
  refine ⟨min ρ₀a ρ₀b, Ka ∪ Kb, max C₀a C₀b, min εsepa εsepb, Jesc + 1, ?_, ?_, ?_, ?_, ?_,
    Nat.succ_pos Jesc, ?_⟩
  · exact lt_min hρ₀a hρ₀b
  · exact hKac.union hKbc
  · exact Set.union_subset hKaBl hKbBl
  · exact le_trans hC₀a (le_max_left _ _)
  · exact lt_min hεa hεb
  · intro ρ hρ0 hρρ₀ β hβre hβrele hβim hβav
    have hβd : β ∈ Work.L62LD.downBox d hd b := ⟨⟨hβre, hβrele, hβim⟩, hβav⟩
    rcases hcover hβd with hβa | hβb
    · obtain ⟨W, hW0, hop, hchain, hWK, hsep, hbdd, hdiamJ, hC0, hdepth⟩ :=
        hmaina ρ hρ0 (le_trans hρρ₀ (min_le_left _ _)) β hβa
      refine ⟨W, Or.inl hW0, hop, hchain, fun j hj1 hjJ => ?_, fun i j hi hj hij u hu v hv k => ?_,
        hbdd, hdiamJ, fun j hj => ?_, hdepth⟩
      · exact subset_trans (hWK j hj1 hjJ) Set.subset_union_left
      · exact le_trans (min_le_left _ _) (hsep i j hi hj hij u hu v hv k)
      · obtain ⟨u, hu, u', hu', hlt⟩ := hC0 j hj
        exact ⟨u, hu, u', hu', lt_of_lt_of_le hlt (le_max_left _ _)⟩
    · obtain ⟨W, hW0, hop, hchain, hWK, hsep, hbdd, hdiamJ, hC0, hdepth⟩ :=
        hmainb ρ hρ0 (le_trans hρρ₀ (min_le_right _ _)) β hβb
      refine ⟨W, Or.inr hW0, hop, hchain, fun j hj1 hjJ => ?_, fun i j hi hj hij u hu v hv k => ?_,
        hbdd, hdiamJ, fun j hj => ?_, hdepth⟩
      · exact subset_trans (hWK j hj1 hjJ) Set.subset_union_right
      · exact le_trans (min_le_right _ _) (hsep i j hi hj hij u hu v hv k)
      · obtain ⟨u, hu, u', hu', hlt⟩ := hC0 j hj
        exact ⟨u, hu, u', hu', lt_of_lt_of_le hlt (le_max_right _ _)⟩


end Work.L62
