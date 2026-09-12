import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Real
import Submission.Commons.Geometry.Convex.Hadwiger.continuous_parallel_body_volume

open MeasureTheory
open Metric
open Set
open scoped Classical Pointwise Topology

namespace Commons.Geometry.Convex.Hadwiger

lemma exists_mem_inter_of_union_Icc_of_closed
    {S T : Set ℝ} (hS_closed : IsClosed S) (hT_closed : IsClosed T)
    (hS_sub : S ⊆ Set.Icc 0 1) (hS_nonempty : S.Nonempty)
    (h1T : 1 ∈ T) (hunion : S ∪ T = Set.Icc 0 1) :
    ∃ x, x ∈ S ∩ T := by
  have hS_bdd : BddAbove S := by
    refine ⟨1, ?_⟩
    intro x hx
    exact (hS_sub hx).2
  have hS_sup_mem : sSup S ∈ S :=
    IsClosed.csSup_mem hS_closed hS_nonempty hS_bdd
  let a : ℝ := sSup S
  have haS : a ∈ S := hS_sup_mem
  have haI : a ∈ Set.Icc 0 1 := hS_sub haS
  by_cases ha1 : a = 1
  · refine ⟨a, haS, ?_⟩
    simpa [a, ha1] using h1T
  · have hal : a < 1 := lt_of_le_of_ne haI.2 ha1
    have hpos : 0 < 1 - a := sub_pos.mpr hal
    let y : ℕ → ℝ := fun n => a + (1 - a) / ((n : ℝ) + 1)
    have hden_pos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => Nat.cast_add_one_pos (α := ℝ) n
    have hy_gt : ∀ n, a < y n := by
      intro n
      dsimp [y]
      exact lt_add_of_pos_right a (div_pos hpos (hden_pos n))
    have hy_le : ∀ n, y n ≤ 1 := by
      intro n
      dsimp [y]
      have hden_ge : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        exact le_add_of_nonneg_left (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)
      have hdiv_le : (1 - a) / ((n : ℝ) + 1) ≤ (1 - a) / 1 :=
        div_le_div_of_nonneg_left (le_of_lt hpos) zero_lt_one hden_ge
      have hdiv_le' : (1 - a) / ((n : ℝ) + 1) ≤ 1 - a := by
        simpa using hdiv_le
      linarith
    have hyT : ∀ n, y n ∈ T := by
      intro n
      have hyI : y n ∈ Set.Icc 0 1 := by
        constructor
        · exact le_trans haI.1 (le_of_lt (hy_gt n))
        · exact hy_le n
      have hy_not_S : y n ∉ S := by
        intro hyn
        have hle : y n ≤ a := le_csSup hS_bdd hyn
        exact not_lt_of_ge hle (hy_gt n)
      have hy_union : y n ∈ S ∪ T := by
        rw [hunion]
        exact hyI
      exact (Set.mem_union (y n) S T).mp hy_union |>.resolve_left hy_not_S
    have h_tendsto : Filter.Tendsto y Filter.atTop (nhds a) := by
      dsimp [y]
      have h1 : Filter.Tendsto (fun n : ℕ => (1 - a) / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := by
        simpa [div_eq_mul_inv] using
          ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 - a))
      have hsum : Filter.Tendsto (fun n : ℕ => (1 - a) / ((n : ℝ) + 1) + a) Filter.atTop (nhds a) :=
        by simpa using h1.add (tendsto_const_nhds (x := a))
      convert hsum using 1
      ext n
      ring
    have haT : a ∈ T :=
      IsClosed.mem_of_tendsto hT_closed h_tendsto (Filter.Eventually.of_forall hyT)
    exact ⟨a, haS, haT⟩

lemma add_inter_eq_of_convex_union
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {C D L : Set V} (hC_closed : IsClosed C) (hD_closed : IsClosed D)
    (hL : Convex ℝ L) (hunion : Convex ℝ (C ∪ D)) :
    (C + L) ∩ (D + L) = (C ∩ D) + L := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hzC, hzD⟩
    rcases Set.mem_add.mp hzC with ⟨c, hcC, u, huL, rfl⟩
    rcases Set.mem_add.mp hzD with ⟨d, hdD, v, hvL, hcd⟩
    have h_eq : c + u = d + v := by simpa using hcd.symm
    let p : ℝ →ᵃ[ℝ] V := AffineMap.lineMap c d
    let S_C : Set ℝ := p ⁻¹' C ∩ Set.Icc 0 1
    let S_D : Set ℝ := p ⁻¹' D ∩ Set.Icc 0 1
    have hS_C_closed : IsClosed S_C := by
      dsimp [S_C]
      exact IsClosed.inter (IsClosed.preimage AffineMap.lineMap_continuous hC_closed) isClosed_Icc
    have hS_D_closed : IsClosed S_D := by
      dsimp [S_D]
      exact IsClosed.inter (IsClosed.preimage AffineMap.lineMap_continuous hD_closed) isClosed_Icc
    have hS_C_sub : S_C ⊆ Set.Icc 0 1 := inter_subset_right
    have hS_C_nonempty : S_C.Nonempty := by
      refine ⟨0, ?_, ?_⟩
      · simpa [S_C, p] using hcC
      · exact Set.left_mem_Icc.mpr zero_le_one
    have h1D : 1 ∈ S_D := by
      constructor
      · simpa [S_D, p] using hdD
      · exact Set.right_mem_Icc.mpr zero_le_one
    have hunionSD : S_C ∪ S_D = Set.Icc 0 1 := by
      ext θ
      constructor
      · intro hθ
        rcases hθ with hθ | hθ
        · exact hS_C_sub hθ
        · exact (inter_subset_right : S_D ⊆ Set.Icc 0 1) hθ
      · intro hθ
        have hp_mem_seg : p θ ∈ segment ℝ c d := by
          rw [segment_eq_image]
          refine ⟨θ, hθ, ?_⟩
          dsimp [p]
          rw [AffineMap.lineMap_apply]
          simp [vsub_eq_sub, smul_sub]
          module
        have hp_union : p θ ∈ C ∪ D :=
          hunion.segment_subset (Or.inl hcC) (Or.inr hdD) hp_mem_seg
        rw [← Set.mem_preimage] at hp_union
        rcases hp_union with hp | hp
        · exact Or.inl ⟨hp, hθ⟩
        · exact Or.inr ⟨hp, hθ⟩
    obtain ⟨θ, hθC, hθD⟩ := exists_mem_inter_of_union_Icc_of_closed
      hS_C_closed hS_D_closed hS_C_sub hS_C_nonempty h1D hunionSD
    have hθI : θ ∈ Set.Icc 0 1 := hS_C_sub hθC
    let x : V := (1 - θ) • c + θ • d
    let l : V := (1 - θ) • u + θ • v
    have hxCD : x ∈ C ∩ D := by
      constructor
      · have hx : x = p θ := by
          dsimp [p]
          rw [AffineMap.lineMap_apply]
          simp [x, vsub_eq_sub, smul_sub]
          module
        rw [hx]
        exact hθC.1
      · have hx : x = p θ := by
          dsimp [p]
          rw [AffineMap.lineMap_apply]
          simp [x, vsub_eq_sub, smul_sub]
          module
        rw [hx]
        exact hθD.1
    have hlL : l ∈ L := by
      have hl_seg : l ∈ segment ℝ u v := by
        rw [segment_eq_image]
        exact ⟨θ, hθI, by simp [l]⟩
      exact hL.segment_subset huL hvL hl_seg
    have hsum : c + u = x + l := by
      have hcoef : (1 - θ) + θ = 1 := by ring
      calc
        c + u = (1 - θ) • (c + u) + θ • (c + u) := (Convex.combo_self hcoef (c + u)).symm
        _ = (1 - θ) • (c + u) + θ • (d + v) := by rw [h_eq]
        _ = ((1 - θ) • c + θ • d) + ((1 - θ) • u + θ • v) := by
          simp [smul_add, add_assoc, add_comm, add_left_comm]
        _ = x + l := by rfl
    rw [hsum]
    exact Set.add_mem_add hxCD hlL
  · intro hz
    rcases Set.mem_add.mp hz with ⟨x, hx, l, hl, rfl⟩
    constructor
    · exact Set.add_mem_add hx.1 hl
    · exact Set.add_mem_add hx.2 hl

lemma linearIsometry_image_add {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : V ≃ₗᵢ[ℝ] V) (s t : Set V) :
    e '' (s + t) = e '' s + e '' t := by
  simpa [Set.image2_add] using
    (Set.image_image2_distrib (f := fun a b : V => a + b) (g := (e : V → V))
      (f' := fun a b : V => a + b) (g₁ := (e : V → V)) (g₂ := (e : V → V))
      (fun a b => e.map_add a b))

lemma linearIsometry_image_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : V ≃ₗᵢ[ℝ] V) (t : ℝ) (s : Set V) :
    e '' (t • s) = t • (e '' s) := by
  ext y
  simp only [mem_image, mem_smul_set]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨a, ha, hx_eq⟩
    refine ⟨e a, ⟨a, ha, rfl⟩, ?_⟩
    rw [← hx_eq]
    exact (e.map_smul t a).symm
  · rintro ⟨b, hb, hb_eq⟩
    rcases hb with ⟨a, ha, ha_eq⟩
    refine ⟨t • a, ⟨a, ha, rfl⟩, ?_⟩
    rw [e.map_smul t a, ha_eq, hb_eq]

lemma volume_image_linearIsometry {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    (e : V ≃ₗᵢ[ℝ] V) (s : Set V) :
    volume (e '' s) = volume s := by
  have hmp := e.measurePreserving
  have hemb := e.toHomeomorph.measurableEmbedding
  calc
    volume (e '' s) = volume (e ⁻¹' (e '' s)) :=
      (hmp.measure_preimage_emb hemb (e '' s)).symm
    _ = volume s := by rw [Set.preimage_image_eq s e.injective]

lemma measure_image_add_right {V : Type*} [AddGroup V] [MeasurableSpace V] [MeasurableAdd V]
    (μ : Measure V) [μ.IsAddRightInvariant] (s : Set V) (g : V) :
    μ ((fun x => x + g) '' s) = μ s := by
  have hpre : (fun x => x + g) ⁻¹' ((fun x => x + g) '' s) = s :=
    Set.preimage_image_eq s (add_left_injective g)
  calc
    μ ((fun x => x + g) '' s)
        = μ ((fun x => x + g) ⁻¹' ((fun x => x + g) '' s)) := by
          exact (measure_preimage_add_right μ g ((fun x => x + g) '' s)).symm
    _ = μ s := by rw [hpre]

lemma image_add_right_set_add {V : Type*} [AddCommGroup V]
    (s t : Set V) (g : V) :
    (fun x => x + g) '' (s + t) = ((fun x => x + g) '' s) + t := by
  simpa [Set.image2_add] using
    (Set.image_image2_distrib_left (f := fun a b : V => a + b) (g := fun x : V => x + g)
      (f' := fun a b : V => a + b) (g' := fun x : V => x + g)
      (fun a b => by abel))

theorem parallel_body_valuation (n : ℕ) (t : ℝ) :
    let V := EuclideanSpace ℝ (Fin n)
    let B : ConvexBody V := ⟨Metric.closedBall (0 : V) 1, convex_closedBall (0 : V) 1, isCompact_closedBall (0 : V) 1, nonempty_closedBall.mpr zero_le_one⟩
    let F : ConvexBody V → ℝ := fun K => (volume ((K + t • B : ConvexBody V) : Set V)).toReal
    Continuous F ∧
      (∀ A B C D : ConvexBody V,
          (A : Set V) = (C : Set V) ∪ (D : Set V) →
          (B : Set V) = (C : Set V) ∩ (D : Set V) →
          F A + F B = F C + F D) ∧
      (∀ A B : ConvexBody V, ∀ e : V ≃ₗᵢ[ℝ] V,
          (B : Set V) = e '' (A : Set V) → F B = F A) ∧
      (∀ A B : ConvexBody V, ∀ s : V,
          (B : Set V) = (fun x => x + s) '' (A : Set V) → F A = F B) := by
  intro V B F
  let B0 : ConvexBody V := B
  let L : ConvexBody V := t • B0
  have hF_real_set : ∀ K : ConvexBody V, F K = (volume : Measure V).real ((K : Set V) + (L : Set V)) := by
    intro K
    rw [show F K = (volume : Measure V).real ((K + L : ConvexBody V) : Set V) by
      dsimp [F, L, B0]
      rfl]
    rw [ConvexBody.coe_add]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- continuity
    simpa [F, L, B0] using continuous_parallel_body_volume n L
  · -- additivity
    intro A B C D hU hI
    let s : Set V := (C : Set V) + (L : Set V)
    let u : Set V := (D : Set V) + (L : Set V)
    have hu_conv : Convex ℝ u := by
      dsimp [u]
      exact Convex.add (D : ConvexBody V).convex L.convex
    have hu_null : NullMeasurableSet u volume := hu_conv.nullMeasurableSet volume
    have hs_fin : volume s ≠ ⊤ := by
      simpa [s, ConvexBody.coe_add] using (C + L : ConvexBody V).isCompact.measure_ne_top
    have hu_fin : volume u ≠ ⊤ := by
      simpa [u, ConvexBody.coe_add] using (D + L : ConvexBody V).isCompact.measure_ne_top
    have h_union_add : ((C : Set V) ∪ (D : Set V)) + (L : Set V)
        = ((C : Set V) + (L : Set V)) ∪ ((D : Set V) + (L : Set V)) := by
      simpa [Set.image2_add] using
        (Set.image2_union_left (f := fun a b : V => a + b)
          (s := (C : Set V)) (s' := (D : Set V)) (t := (L : Set V)))
    have hA_s : ((A : Set V) + (L : Set V)) = s ∪ u := by
      dsimp [s, u]
      rw [hU, h_union_add]
    have hunion_conv : Convex ℝ ((C : Set V) ∪ (D : Set V)) := hU ▸ A.convex
    have hC_closed : IsClosed (C : Set V) := (C : ConvexBody V).isCompact.isClosed
    have hD_closed : IsClosed (D : Set V) := (D : ConvexBody V).isCompact.isClosed
    have hL_conv : Convex ℝ (L : Set V) := L.convex
    have h_inter_add := add_inter_eq_of_convex_union (V := V) hC_closed hD_closed hL_conv hunion_conv
    have hB_s : ((B : Set V) + (L : Set V)) = s ∩ u := by
      dsimp [s, u]
      rw [hI, h_inter_add]
    have h_main := measureReal_union_add_inter₀ (μ := volume) (s := s) (t := u) hu_null hs_fin hu_fin
    calc
      F A + F B = (volume : Measure V).real ((A : Set V) + (L : Set V)) + (volume : Measure V).real ((B : Set V) + (L : Set V)) := by
        rw [hF_real_set A, hF_real_set B]
      _ = (volume : Measure V).real (s ∪ u) + (volume : Measure V).real (s ∩ u) := by
        rw [hA_s, hB_s]
      _ = (volume : Measure V).real s + (volume : Measure V).real u := h_main
      _ = (volume : Measure V).real ((C : Set V) + (L : Set V)) + (volume : Measure V).real ((D : Set V) + (L : Set V)) := by
        rfl
      _ = F C + F D := by
        rw [hF_real_set C, hF_real_set D]
  · -- isometry
    intro A B e hB
    have hB0_image : e '' (B0 : Set V) = (B0 : Set V) := by
      change e '' (Metric.closedBall (0 : V) 1) = Metric.closedBall (0 : V) 1
      rw [e.image_closedBall (0 : V) 1]
      simp
    have hL_image : e '' (L : Set V) = (L : Set V) := by
      dsimp [L]
      rw [linearIsometry_image_smul]
      rw [hB0_image]
    have h_add_image : e '' ((A : Set V) + (L : Set V)) = e '' (A : Set V) + (L : Set V) := by
      rw [linearIsometry_image_add]
      rw [hL_image]
    have hset : (B : Set V) + (L : Set V) = e '' ((A : Set V) + (L : Set V)) := by
      calc
        (B : Set V) + (L : Set V) = (e '' (A : Set V)) + (L : Set V) := by rw [hB]
        _ = e '' ((A : Set V) + (L : Set V)) := by rw [← h_add_image]
    have hvol : volume ((B : Set V) + (L : Set V)) = volume ((A : Set V) + (L : Set V)) := by
      rw [hset]
      exact volume_image_linearIsometry e ((A : Set V) + (L : Set V))
    have hvolreal : (volume : Measure V).real ((B : Set V) + (L : Set V)) = (volume : Measure V).real ((A : Set V) + (L : Set V)) := by
      simp [Measure.real, hvol]
    rw [hF_real_set B, hF_real_set A]
    exact hvolreal
  · -- translation
    intro A B s hB
    have hset : (B : Set V) + (L : Set V) = (fun x => x + s) '' ((A : Set V) + (L : Set V)) := by
      calc
        (B : Set V) + (L : Set V) = ((fun x => x + s) '' (A : Set V)) + (L : Set V) := by rw [hB]
        _ = (fun x => x + s) '' ((A : Set V) + (L : Set V)) := by
          exact (image_add_right_set_add (A : Set V) (L : Set V) s).symm
    have hvol : volume ((B : Set V) + (L : Set V)) = volume ((A : Set V) + (L : Set V)) := by
      rw [hset]
      exact measure_image_add_right volume ((A : Set V) + (L : Set V)) s
    have hvolreal : (volume : Measure V).real ((B : Set V) + (L : Set V)) = (volume : Measure V).real ((A : Set V) + (L : Set V)) := by
      simp [Measure.real, hvol]
    rw [hF_real_set A, hF_real_set B]
    exact hvolreal.symm

end Commons.Geometry.Convex.Hadwiger