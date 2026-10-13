import Mathlib
import Submission.Work.WilE7.PCDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7

/-!
## The band step for local preconnectedness

If `C ⊆ ℝⁿ` is locally preconnected and `a`, `b : ℝⁿ → EReal` are continuous on `C`, then
the band `{z ∈ ℝⁿ⁺¹ | Fin.init z ∈ C, a (Fin.init z) < z (last) < b (Fin.init z)}` is
locally preconnected.

At a point `c` of the band, write `x₀ = Fin.init c` and `t₀ = c (Fin.last n)`.  Since
`a x₀ < t₀ < b x₀` and `a`, `b` are continuous, there is a small `δ > 0` and an open
`u ∋ x₀` such that `a y < t₀ - δ` and `t₀ + δ < b y` for all `y ∈ u ∩ C`.  Shrinking `u`
further using `IsLocPC C` (and taking `δ` small enough that a vertical window of radius `δ`
around `t₀` fits in the prescribed open set `W`), we get an open `V₁ ∋ x₀` with `V₁ ∩ C`
preconnected.  The cylinder
`{z | Fin.init z ∈ V₁, z (last) ∈ Ioo (t₀ - δ) (t₀ + δ)} ∩ ball c ε`
is then open, contains `c`, lies in `W`, and its trace on the band is exactly
`Fin.snoc '' ((V₁ ∩ C) ×ˢ Ioo (t₀ - δ) (t₀ + δ))`, the continuous image of a product of
preconnected sets (inside this window the inequalities of the band hold automatically).
-/

theorem isLocPC_band {n : ℕ} {C : Set (Fin n → ℝ)} (hC : IsLocPC C)
    (a b : (Fin n → ℝ) → EReal) (ha : ContinuousOn a C) (hb : ContinuousOn b C) :
    IsLocPC {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
      a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
      ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} := by
  intro c hc W hW hcW
  obtain ⟨hxC, ha0, hb0⟩ := hc
  set x₀ : Fin n → ℝ := Fin.init c with hx₀def
  set t₀ : ℝ := c (Fin.last n) with ht₀def
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW c hcW
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := exists_lt_coe_sub (a x₀) t₀ ha0
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := exists_coe_add_lt (b x₀) t₀ hb0
  set δ : ℝ := min (min δ₁ δ₂) (ε / 2) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min hδ₁pos hδ₂pos) hε2
  have hδle₁ : δ ≤ δ₁ := by
    rw [hδdef]
    calc min (min δ₁ δ₂) (ε / 2) ≤ min δ₁ δ₂ := min_le_left _ _
      _ ≤ δ₁ := min_le_left _ _
  have hδle₂ : δ ≤ δ₂ := by
    rw [hδdef]
    calc min (min δ₁ δ₂) (ε / 2) ≤ min δ₁ δ₂ := min_le_left _ _
      _ ≤ δ₂ := min_le_right _ _
  have hδleε : δ ≤ ε / 2 := by
    rw [hδdef]
    exact min_le_right _ _
  have ha_bd : a x₀ < ((t₀ - δ : ℝ) : EReal) :=
    hδ₁.trans_le (EReal.coe_le_coe (by linarith))
  have hb_bd : ((t₀ + δ : ℝ) : EReal) < b x₀ :=
    (EReal.coe_le_coe (by linarith)).trans_lt hδ₂
  have hmem_a : a ⁻¹' Set.Iio ((t₀ - δ : ℝ) : EReal) ∈ nhdsWithin x₀ C :=
    (ha.continuousWithinAt hxC).preimage_mem_nhdsWithin ((isOpen_Iio' _).mem_nhds ha_bd)
  have hmem_b : b ⁻¹' Set.Ioi ((t₀ + δ : ℝ) : EReal) ∈ nhdsWithin x₀ C :=
    (hb.continuousWithinAt hxC).preimage_mem_nhdsWithin ((isOpen_Ioi' _).mem_nhds hb_bd)
  have hmem_ball : Metric.ball x₀ (ε / 2) ∈ nhdsWithin x₀ C :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨Metric.ball x₀ (ε / 2), Metric.ball_mem_nhds x₀ hε2, Set.inter_subset_left⟩
  have hmem := Filter.inter_mem (Filter.inter_mem hmem_a hmem_b) hmem_ball
  obtain ⟨u, hu, huc⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hmem
  obtain ⟨ε', hε', hball'⟩ := Metric.mem_nhds_iff.mp hu
  obtain ⟨V₁, hV₁open, hx₀V₁, hV₁sub, hV₁pc⟩ :=
    hC x₀ hxC (Metric.ball x₀ ε') Metric.isOpen_ball (Metric.mem_ball_self hε')
  have hc_eq : c = Fin.snoc x₀ t₀ := by
    rw [hx₀def, ht₀def]
    exact (Fin.snoc_init_self c).symm
  have hmemV : ∀ x ∈ V₁ ∩ C, ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ),
      (Fin.snoc x t : Fin (n + 1) → ℝ) ∈
        ({z : Fin (n + 1) → ℝ | Fin.init z ∈ V₁} ∩
          (fun z : Fin (n + 1) → ℝ => z (Fin.last n)) ⁻¹' Set.Ioo (t₀ - δ) (t₀ + δ) ∩
          Metric.ball c ε) ∩
        {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
          a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
          ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} := by
    intro x hx t ht
    obtain ⟨hxV₁, hxC⟩ := hx
    have hxU : x ∈ u := hball' (hV₁sub hxV₁)
    have hxmem := huc ⟨hxU, hxC⟩
    have hxa : a x < ((t₀ - δ : ℝ) : EReal) := by
      simpa [Set.mem_preimage] using hxmem.1.1
    have hxb : ((t₀ + δ : ℝ) : EReal) < b x := by
      simpa [Set.mem_preimage] using hxmem.1.2
    have hxball : x ∈ Metric.ball x₀ (ε / 2) := hxmem.2
    have hdistzero : dist x x₀ < ε / 2 := Metric.mem_ball.mp hxball
    have htI : t₀ - δ < t ∧ t < t₀ + δ := Set.mem_Ioo.mp ht
    have hlt : a x < (t : EReal) := hxa.trans (EReal.coe_lt_coe_iff.mpr htI.1)
    have hgt : (t : EReal) < b x := (EReal.coe_lt_coe_iff.mpr htI.2).trans hxb
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
    · show Fin.init (Fin.snoc x t : Fin (n + 1) → ℝ) ∈ V₁
      simpa [Fin.init_snoc] using hxV₁
    · show (Fin.snoc x t : Fin (n + 1) → ℝ) (Fin.last n) ∈ Set.Ioo (t₀ - δ) (t₀ + δ)
      simpa [Fin.snoc_last] using ht
    · rw [Metric.mem_ball, hc_eq, dist_pi_lt_iff hε]
      intro i
      refine Fin.lastCases ?_ ?_ i
      · rw [Fin.snoc_last, Fin.snoc_last]
        have h1 : dist t t₀ < δ := by
          rw [Real.dist_eq, abs_lt]
          exact ⟨by linarith [htI.1], by linarith [htI.2]⟩
        linarith
      · intro j
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        have h2 : dist (x j) (x₀ j) ≤ dist x x₀ := dist_le_pi_dist x x₀ j
        linarith
    · show Fin.init (Fin.snoc x t : Fin (n + 1) → ℝ) ∈ C
      simpa [Fin.init_snoc] using hxC
    · show a (Fin.init (Fin.snoc x t : Fin (n + 1) → ℝ)) <
          (((Fin.snoc x t : Fin (n + 1) → ℝ) (Fin.last n) : ℝ) : EReal)
      simpa [Fin.init_snoc, Fin.snoc_last] using hlt
    · show (((Fin.snoc x t : Fin (n + 1) → ℝ) (Fin.last n) : ℝ) : EReal) <
          b (Fin.init (Fin.snoc x t : Fin (n + 1) → ℝ))
      simpa [Fin.init_snoc, Fin.snoc_last] using hgt
  have hΨcont : Continuous
      (fun p : (Fin n → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (n + 1) → ℝ)) :=
    Continuous.finSnoc (X := (Fin n → ℝ) × ℝ) (A := fun _ => ℝ) continuous_fst continuous_snd
  refine ⟨{z : Fin (n + 1) → ℝ | Fin.init z ∈ V₁} ∩
      (fun z : Fin (n + 1) → ℝ => z (Fin.last n)) ⁻¹' Set.Ioo (t₀ - δ) (t₀ + δ) ∩
      Metric.ball c ε, ?_, ?_, ?_, ?_⟩
  · exact ((hV₁open.preimage (Continuous.finInit continuous_id)).inter
      (IsOpen.preimage (continuous_apply (Fin.last n)) isOpen_Ioo)).inter Metric.isOpen_ball
  · refine ⟨⟨?_, ?_⟩, Metric.mem_ball_self hε⟩
    · show Fin.init c ∈ V₁
      simpa [hx₀def] using hx₀V₁
    · show c (Fin.last n) ∈ Set.Ioo (t₀ - δ) (t₀ + δ)
      rw [ht₀def]
      simp only [Set.mem_Ioo]
      exact ⟨by linarith, by linarith⟩
  · intro z hz
    exact hball hz.2
  · have hset : ({z : Fin (n + 1) → ℝ | Fin.init z ∈ V₁} ∩
        (fun z : Fin (n + 1) → ℝ => z (Fin.last n)) ⁻¹' Set.Ioo (t₀ - δ) (t₀ + δ) ∩
        Metric.ball c ε) ∩
        {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
          a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
          ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)}
        = (fun p : (Fin n → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (n + 1) → ℝ)) ''
            ((V₁ ∩ C) ×ˢ Set.Ioo (t₀ - δ) (t₀ + δ)) := by
      ext z
      constructor
      · rintro ⟨⟨⟨hz1, hz2⟩, hzball⟩, hzC, hza, hzb⟩
        exact ⟨(Fin.init z, z (Fin.last n)),
          ⟨⟨hz1, hzC⟩, Set.mem_preimage.mp hz2⟩, Fin.snoc_init_self z⟩
      · rintro ⟨p, hp, hpz⟩
        obtain ⟨x, t⟩ := p
        obtain ⟨⟨hxV₁, hxC⟩, ht⟩ := hp
        rw [← hpz]
        exact hmemV x ⟨hxV₁, hxC⟩ t ht
    rw [hset]
    exact (hV₁pc.prod isPreconnected_Ioo).image _ hΨcont.continuousOn

end Work.WilE7
