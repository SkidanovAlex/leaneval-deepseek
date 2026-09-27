import Mathlib
import Submission.Work.Mostow.bieberbachDefs

/-! ### Assembly: the finite index subgroup of pure translations -/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

set_option maxHeartbeats 4000000

noncomputable section

variable {m : ℕ} {G : Type*} [Group G]



/-- The linear part as a monoid homomorphism. -/
def linPartHom (ρ : G →* (E m ≃ᵢ E m)) : G →* (E m ≃ₗᵢ[ℝ] E m) :=
  { toFun := linPart ρ, map_one' := linPart_one ρ, map_mul' := linPart_mul ρ }

/-- A `δ`-separated subset of a compact set is finite. -/
lemma main_finite_of_separated {X : Type*} [PseudoMetricSpace X]
    {s c : Set X} (hc : IsCompact c) (hsub : s ⊆ c) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ dist x y) : s.Finite := by
  have hcover : c ⊆ ⋃ y : X, Metric.ball y (δ/4) := by
    intro y _
    exact Set.mem_iUnion.mpr ⟨y, Metric.mem_ball_self (by linarith)⟩
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun y : X => Metric.ball y (δ/4))
      (fun _ => Metric.isOpen_ball) hcover
  have hsub2 : s ⊆ ⋃ y ∈ (t : Set X), (Metric.ball y (δ/4) ∩ s) := by
    intro x hx
    have h1 : x ∈ ⋃ y ∈ (t : Set X), Metric.ball y (δ/4) := ht (hsub hx)
    simp only [Set.mem_iUnion] at h1
    obtain ⟨y, hy, hxy⟩ := h1
    simp only [Set.mem_iUnion]
    exact ⟨y, hy, hxy, hx⟩
  refine (Set.Finite.biUnion t.finite_toSet (fun y _ => ?_)).subset hsub2
  refine Set.Subsingleton.finite ?_
  intro x ⟨hx, hxs⟩ x' ⟨hx', hx's⟩
  by_contra hne
  have h1 : dist x x' < δ/2 := by
    have hxlt : dist x y < δ/4 := Metric.mem_ball.mp hx
    have hx'lt : dist x' y < δ/4 := Metric.mem_ball.mp hx'
    calc dist x x' ≤ dist x y + dist y x' := dist_triangle _ _ _
      _ = dist x y + dist x' y := by rw [dist_comm y x']
      _ < δ/4 + δ/4 := add_lt_add hxlt hx'lt
      _ = δ/2 := by ring
  have h2 := hsep x hxs x' hx's hne
  linarith

/-- If every element whose linear part is within distance `1/2` of the identity is a pure
translation, then the image of the linear part is finite. -/
lemma range_linPartHom_finite (ρ : G →* (E m ≃ᵢ E m))
    (hkey : ∀ g : G, mOf (linPart ρ g) < 1/2 → linPart ρ g = 1) :
    (Set.range (linPartHom ρ)).Finite := by
  have hSfin : (opOf '' Set.range (linPartHom ρ)).Finite := by
    refine main_finite_of_separated (δ := 1/2)
      (isCompact_closedBall (0 : E m →L[ℝ] E m) 1) ?_ (by norm_num) ?_
    · rintro _ ⟨A, hA, rfl⟩
      obtain ⟨g, rfl⟩ := hA
      simpa using norm_opOf_le_one (linPartHom ρ g)
    · rintro x ⟨A, hA, rfl⟩ y ⟨B, hB, rfl⟩ hne
      obtain ⟨g, rfl⟩ := hA
      obtain ⟨g', rfl⟩ := hB
      have hne' : linPartHom ρ g ≠ linPartHom ρ g' := fun h => hne (by rw [h])
      have hmem : (linPartHom ρ g) * (linPartHom ρ g')⁻¹ ∈ Set.range (linPartHom ρ) :=
        ⟨g * g'⁻¹, by simp [map_mul, map_inv]⟩
      obtain ⟨h, hh⟩ := hmem
      have hne1 : (linPartHom ρ g) * (linPartHom ρ g')⁻¹ ≠ 1 := by
        intro h1
        exact hne' (mul_inv_eq_one.mp h1)
      have hge : 1/2 ≤ mOf ((linPartHom ρ g) * (linPartHom ρ g')⁻¹) := by
        by_contra hlt
        rw [not_le] at hlt
        have hlt' : mOf (linPart ρ h) < 1/2 := by
          have hh' : linPart ρ h = (linPartHom ρ g) * (linPartHom ρ g')⁻¹ := hh
          rw [hh']; exact hlt
        have h2 : linPart ρ h = 1 := hkey h hlt'
        have hh'' : linPart ρ h = (linPartHom ρ g) * (linPartHom ρ g')⁻¹ := hh
        rw [h2] at hh''
        exact hne1 hh''.symm
      calc (1/2 : ℝ) ≤ mOf ((linPartHom ρ g) * (linPartHom ρ g')⁻¹) := hge
        _ ≤ ‖opOf (linPartHom ρ g) - opOf (linPartHom ρ g')‖ := mOf_mul_inv_le _ _
        _ = dist (opOf (linPartHom ρ g)) (opOf (linPartHom ρ g')) := by rw [dist_eq_norm]
  refine Set.Finite.of_finite_image hSfin ?_
  intro A hA B hB h
  obtain ⟨g, rfl⟩ := hA
  obtain ⟨g', rfl⟩ := hB
  refine LinearIsometryEquiv.ext (fun x => ?_)
  have hx := congrArg (fun (T : E m →L[ℝ] E m) => T x) h
  simpa only [opOf_apply] using hx

/-- The translation vectors of the kernel of the linear part span. -/
lemma span_trPart_ker_linPartHom (ρ : G →* (E m ≃ᵢ E m))
    (hmini : ∀ (u : E m), ‖u‖ = 1 → ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∃ g : G, ∃ t : ℝ, 1 ≤ t ∧ mOf (linPart ρ g) ≤ ε ∧
        ‖trPart ρ g + t • u‖ ≤ δ * t)
    (hkey : ∀ g : G, mOf (linPart ρ g) < 1/2 → linPart ρ g = 1) :
    Submodule.span ℝ (trPart ρ '' (((linPartHom ρ).ker : Subgroup G) : Set G)) = ⊤ := by
  set V : Submodule ℝ (E m) :=
    Submodule.span ℝ (trPart ρ '' (((linPartHom ρ).ker : Subgroup G) : Set G)) with hV
  have hVtop : V = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff]
    refine le_antisymm ?_ bot_le
    intro w hw
    rw [Submodule.mem_bot]
    by_contra hw0
    have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    set u : E m := ‖w‖⁻¹ • w with hu
    have hu_mem : u ∈ Vᗮ := Submodule.smul_mem _ _ hw
    have hu_norm : ‖u‖ = 1 := by
      rw [hu, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w)), inv_mul_cancel₀ (ne_of_gt hwnorm)]
    obtain ⟨g, t, ht1, hmg, hnormg⟩ :=
      hmini u hu_norm (1/4) (1/2) (by norm_num) (by norm_num)
    have hgT : g ∈ (linPartHom ρ).ker := by
      rw [MonoidHom.mem_ker]
      exact hkey g (lt_of_le_of_lt hmg (by norm_num))
    have hmemV : trPart ρ g ∈ V := Submodule.subset_span ⟨g, hgT, rfl⟩
    have hinner0 : inner ℝ (trPart ρ g) u = 0 :=
      (Submodule.mem_orthogonal V u).mp hu_mem _ hmemV
    have hu_self : inner ℝ u u = 1 := by
      rw [real_inner_self_eq_norm_sq, hu_norm]; norm_num
    have hinner_t : inner ℝ (trPart ρ g + t • u) u = t := by
      rw [inner_add_left, inner_smul_left, hinner0, hu_self]
      simp
    have h1 : t ≤ ‖trPart ρ g + t • u‖ := by
      calc t = |inner ℝ (trPart ρ g + t • u) u| := by
            rw [hinner_t, abs_of_pos (by linarith : (0:ℝ) < t)]
        _ ≤ ‖trPart ρ g + t • u‖ * ‖u‖ := abs_real_inner_le_norm _ _
        _ = ‖trPart ρ g + t • u‖ := by rw [hu_norm, mul_one]
    have : t ≤ (1/2) * t := le_trans h1 hnormg
    linarith
  exact hVtop



end

end Work.Mostow
