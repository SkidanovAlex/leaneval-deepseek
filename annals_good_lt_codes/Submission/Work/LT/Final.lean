import Submission.Work.LT.Defs
import Submission.Work.LT.good_base_code
import Submission.Work.LT.lr_distance
import Submission.Work.LT.lr_expander_family
import Submission.Work.LT.lr_local_opt_far
import Submission.Work.LT.lr_rate
import Submission.Work.LT.lr_sound
import Submission.Work.LT.ltc_of_tests
import Submission.Work.LT.sl3_bounded_generation
import Submission.Work.LT.sl3_gap
import Submission.Work.LT.sl3_relT_column
import Submission.Work.LT.transport_rate_distance

/-! Final assembly of DELLM Theorem 1.2 from the proved route lemmas (design: Submission/Work/LT/DESIGN.md). -/

namespace Work.LT


section Assembly
open GoodLTC NNReal Classical

theorem theorem_1_2' (ρ : ℝ≥0) (hρ : ρ < 1) :
    ∃ q, ∃ κ ≠ 0, ∃ (n : ℕ → ℕ), ∃ (𝒞 : (i : ℕ) → BinaryCode (n i)), IsGood 𝒞 ∧
      ∀ i, Nonempty (LTC q κ (𝒞 i)) ∧ rate (𝒞 i) ≥ ρ := by
  set ρ' : ℝ := max (ρ : ℝ) (1 / 2) with hρ'def
  have hρ'1 : ρ' < 1 := max_lt (by exact_mod_cast hρ) (by norm_num)
  have hρ'h : (1 / 2 : ℝ) ≤ ρ' := le_max_right _ _
  have hρρ' : (ρ : ℝ) ≤ ρ' := le_max_left _ _
  set r0 : ℝ := (3 + ρ') / 4 with hr0def
  have hr0 : r0 < 1 := by rw [hr0def]; linarith
  have hr0' : 0 ≤ r0 := by rw [hr0def]; linarith
  have hrate : ρ' ≤ 2 * r0 ^ 2 - 1 := by nlinarith [sq_nonneg (r0 - 1)]
  obtain ⟨δ0, hδ0, hδ1, κ0, hκ0, D0, hbase⟩ := good_base_code r0 hr0
  set c : ℝ := κ0 * δ0 / (8 + κ0) with hcdef
  have hc : 0 < c := by positivity
  have hcδ : c < δ0 := by
    rw [hcdef, div_lt_iff₀ (by linarith)]; nlinarith
  set μ : ℝ := c / 2 with hμdef
  have hμ : 0 < μ := by positivity
  obtain ⟨Δ, hΔ, hD0, hfam⟩ := lr_expander_family μ hμ D0
  obtain ⟨CA, CB, hkA, hkB, hdA, hdB, hagr⟩ := hbase Δ hD0
  choose G hGrp hFin hcard A hAl hAr using hfam
  let _ : ∀ m, Group (G m) := hGrp
  let _ : ∀ m, Fintype (G m) := hFin
  set κr : ℝ := (c - μ) / (16 * (Δ + 1)) with hκrdef
  have hκr : 0 < κr := by rw [hκrdef]; apply div_pos <;> [linarith; positivity]
  set ε : ℝ := min (1 / 2) (δ0 ^ 2 * (δ0 - μ)) with hεdef
  have hε : 0 < ε := lt_min (by norm_num) (by apply mul_pos (by positivity); linarith)
  have hΔr : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  -- the codes
  let e : ∀ m, (G m × Fin Δ × Fin Δ) ≃ Fin (Fintype.card (G m × Fin Δ × Fin Δ)) :=
    fun m => Fintype.equivFin _
  have hn : ∀ m, (Fintype.card (G m × Fin Δ × Fin Δ) : ℝ) = Fintype.card (G m) * Δ * Δ := by
    intro m; simp [Fintype.card_prod, mul_assoc]
  have hGpos : ∀ m, (0 : ℝ) < Fintype.card (G m) := fun m => by
    exact_mod_cast Fintype.card_pos
  -- key per-index facts
  have hdim : ∀ m, (2 * r0 ^ 2 - 1) * (Fintype.card (G m) * Δ * Δ) ≤
      Module.finrank (ZMod 2) (lrCode (A m) (A m) CA CB) :=
    fun m => lr_rate (A m) (A m) CA CB r0 hr0' hkA hkB
  have hne : ∀ m, ∃ f ∈ lrCode (A m) (A m) CA CB, f ≠ 0 := by
    intro m
    have hpos : 0 < Module.finrank (ZMod 2) (lrCode (A m) (A m) CA CB) := by
      have h1 := hdim m
      have h2 : (0 : ℝ) < (2 * r0 ^ 2 - 1) * (Fintype.card (G m) * Δ * Δ) := by
        apply mul_pos (by linarith); exact mul_pos (mul_pos (hGpos m) hΔr) hΔr
      exact_mod_cast h2.trans_le h1
    by_contra hcon
    push Not at hcon
    have hbot : lrCode (A m) (A m) CA CB = ⊥ := (Submodule.eq_bot_iff _).mpr hcon
    rw [hbot, finrank_bot] at hpos
    exact lt_irrefl 0 hpos
  have htr : ∀ m, rate (transportCode (e m) (lrCode (A m) (A m) CA CB)) =
        (Module.finrank (ZMod 2) (lrCode (A m) (A m) CA CB) : ℝ) /
          Fintype.card (G m × Fin Δ × Fin Δ) ∧
      δ0 ^ 2 * (δ0 - μ) ≤ normalisedDistance (transportCode (e m) (lrCode (A m) (A m) CA CB)) := by
    intro m
    apply transport_rate_distance (e m) _ (δ0 ^ 2 * (δ0 - μ)) (hne m)
    intro f hf hf0
    rw [hn m]
    exact lr_distance (A m) (A m) CA CB δ0 μ hμ.le (hAr m) hdA hdB f hf hf0
  have hrate_m : ∀ m, ρ' ≤ rate (transportCode (e m) (lrCode (A m) (A m) CA CB)) := by
    intro m
    have hnp : (0 : ℝ) < Fintype.card (G m) * Δ * Δ := mul_pos (mul_pos (hGpos m) hΔr) hΔr
    rw [(htr m).1, hn m, le_div_iff₀ hnp]
    calc ρ' * (Fintype.card (G m) * Δ * Δ) ≤ (2 * r0 ^ 2 - 1) * (Fintype.card (G m) * Δ * Δ) := by
          exact mul_le_mul_of_nonneg_right hrate hnp.le
      _ ≤ _ := hdim m
  refine ⟨Δ * Δ, Real.toNNReal κr, by simpa using hκr,
    fun m => Fintype.card (G m × Fin Δ × Fin Δ),
    fun m => transportCode (e m) (lrCode (A m) (A m) CA CB), ⟨?_, ε, hε, ?_⟩, ?_⟩
  · -- lengths tend to infinity
    refine Filter.tendsto_atTop_mono (fun m => ?_) Filter.tendsto_id
    have h1 : m ≤ Fintype.card (G m) := hcard m
    have h2 : Fintype.card (G m) ≤ Fintype.card (G m × Fin Δ × Fin Δ) := by
      rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
      exact Nat.le_mul_of_pos_right _ (Nat.mul_pos hΔ hΔ)
    exact h1.trans h2
  · intro m
    refine ⟨?_, ?_⟩
    · exact (min_le_left _ _).trans (hρ'h.trans (hrate_m m))
    · exact (min_le_right _ _).trans (htr m).2
  · intro m
    refine ⟨?_, le_trans hρρ' (hrate_m m)⟩
    apply ltc_of_tests (e m) (lrCode (A m) (A m) CA CB) (Δ * Δ) (Real.toNNReal κr)
      (fun t : Fin 2 × Fin 2 × G m => Finset.univ.image
        (fun ij : Fin Δ × Fin Δ => lrSq (A m) (A m) t.1 t.2.1 t.2.2 ij.1 ij.2))
      (P := fun t f => lrView (A m) (A m) t.1 t.2.1 t.2.2 f ∈ tensorCode CA CB)
    · intro t
      refine Finset.card_image_le.trans ?_
      simp
    · intro t f g hfg hf
      have : lrView (A m) (A m) t.1 t.2.1 t.2.2 f = lrView (A m) (A m) t.1 t.2.1 t.2.2 g := by
        funext ij
        exact hfg _ (Finset.mem_image.mpr ⟨ij, Finset.mem_univ _, rfl⟩)
      simpa only [this] using hf
    · intro f hf t
      simp only [lrCode, Submodule.mem_iInf, Submodule.mem_comap] at hf
      exact hf t.1 t.2.1 t.2.2
    · intro f
      obtain ⟨c', hc', hbound⟩ := lr_sound hΔ (A m) (A m) CA CB δ0 κ0 μ hκ0 hδ1 hμ.le hdA hdB hagr
        (hAl m) (hAr m) f
      refine ⟨c', hc', ?_⟩
      rw [Real.coe_toNNReal _ hκr.le, hn m]
      have hT : (Fintype.card (Fin 2 × Fin 2 × G m) : ℝ) = 4 * Fintype.card (G m) := by
        simp [Fintype.card_prod]; ring
      rw [hT]
      exact hbound

end Assembly

end Work.LT
