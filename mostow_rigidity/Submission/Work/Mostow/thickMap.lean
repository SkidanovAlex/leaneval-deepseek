import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.finite_nearStab_compact

open Submission.Mostow LeanEval.Geometry.MostowRigidity

namespace Work.Mostow

theorem hdist_coe_inv_mul {n : ℕ} (hA : POBasic n) (hI : HypIsoData n)
    {Γ : Subgroup (PO n 1)} (p q : Γ) (y : E n) :
    hdist ((((p⁻¹ * q : Γ)) : PO n 1) • y) y =
      hdist ((q : PO n 1) • y) ((p : PO n 1) • y) := by
  have hpc : ((((p⁻¹ * q : Γ)) : PO n 1)) = (p : PO n 1)⁻¹ * (q : PO n 1) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
  have hy : (p : PO n 1)⁻¹ • ((p : PO n 1) • y) = y := by
    rw [← hA.mul_smul, inv_mul_cancel, hA.one_smul]
  have hgoal : hdist ((p : PO n 1)⁻¹ • ((q : PO n 1) • y))
      ((p : PO n 1)⁻¹ • ((p : PO n 1) • y))
      = hdist ((q : PO n 1) • y) ((p : PO n 1) • y) := hI.isom_smul _ _ _
  rw [hy] at hgoal
  rw [hpc, hA.mul_smul]
  exact hgoal

theorem hdist_f_mul {n : ℕ} (hA : POBasic n) (hI : HypIsoData n)
    {Γ Λ : Subgroup (PO n 1)} (f : Γ ≃* Λ) (p q : Γ) :
    hdist ((f p : PO n 1) • (0 : E n)) ((f q : PO n 1) • (0 : E n)) =
      hdist (0 : E n) ((f (q⁻¹ * p) : PO n 1) • (0 : E n)) := by
  have h : (f p : PO n 1) • (0 : E n) =
      (f q : PO n 1) • ((f (q⁻¹ * p) : PO n 1) • (0 : E n)) := by
    rw [← hA.mul_smul]
    congr 1
    rw [← Subgroup.coe_mul, ← map_mul]
    congr 1
    group
  rw [h, hI.isom_smul]
  exact hI.symm _ _

set_option maxHeartbeats 1000000 in
theorem thickMap {n : ℕ} (hA : Work.Mostow.POBasic n) (hI : Work.Mostow.HypIsoData n)
    {Γ Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)}
    (hΓdisc : IsDiscrete (SetLike.coe Γ)) (f : Γ ≃* Λ)
    {X : Set (Submission.Mostow.E n)} (hXne : X.Nonempty)
    {K : Set (Submission.Mostow.E n)} (hK : IsCompact K)
    (hcpt : ∀ u ∈ X, ∃ γ : Γ, ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) • u ∈ K)
    (hinv : ∀ (γ : Γ) (u : Submission.Mostow.E n), u ∈ X →
      ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) • u ∈ X)
    {XΛ : Set (Submission.Mostow.E n)} {KΛ : Set (Submission.Mostow.E n)} (hKΛ : IsCompact KΛ)
    (hcptΛ : ∀ w ∈ XΛ, ∃ m : Λ, ((m : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1) • w ∈ KΛ) :
    ∃ Φ : Submission.Mostow.E n → Submission.Mostow.E n,
      (∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ X, ∀ v ∈ X, Submission.Mostow.hdist u v ≤ 1 →
        Submission.Mostow.hdist (Φ u) (Φ v) ≤ C) ∧
      (∀ γ : Γ, ∃ C : ℝ, ∀ u ∈ X, Submission.Mostow.hdist
        (Φ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) • u))
        (((f γ : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1) • Φ u) ≤ C) ∧
      (∃ C : ℝ, ∀ w ∈ XΛ, ∃ u ∈ X, Submission.Mostow.hdist (Φ u) w ≤ C) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hXne
  obtain ⟨D, hD⟩ : ∃ D : ℝ, ∀ k ∈ K, hdist x₀ k ≤ D := by
    have hcont : ContinuousOn (fun k : E n => hdist x₀ k) K :=
      (hI.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    obtain ⟨D, hD⟩ := hK.bddAbove_image hcont
    exact ⟨D, fun k hk => hD ⟨k, hk, rfl⟩⟩
  obtain ⟨DΛ, hDΛ⟩ : ∃ DΛ : ℝ, ∀ v ∈ KΛ, hdist (0 : E n) v ≤ DΛ := by
    have hcont : ContinuousOn (fun k : E n => hdist (0 : E n) k) KΛ :=
      (hI.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    obtain ⟨DΛ, hDΛ⟩ := hKΛ.bddAbove_image hcont
    exact ⟨DΛ, fun k hk => hDΛ ⟨k, hk, rfl⟩⟩
  have hex : ∀ u ∈ X, ∃ γ : Γ, hdist ((γ : PO n 1) • x₀) u ≤ D := by
    intro u hu
    obtain ⟨γ₀, hγ₀⟩ := hcpt u hu
    refine ⟨γ₀⁻¹, ?_⟩
    have h2 : (((γ₀⁻¹ : Γ)) : PO n 1) • ((((γ₀ : Γ)) : PO n 1) • u) = u := by
      rw [← hA.mul_smul]
      have hc : (((γ₀⁻¹ : Γ)) : PO n 1) * (((γ₀ : Γ)) : PO n 1) = 1 := by
        rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
      rw [hc, hA.one_smul]
    calc hdist ((((γ₀⁻¹ : Γ)) : PO n 1) • x₀) u
        = hdist ((((γ₀⁻¹ : Γ)) : PO n 1) • x₀) ((((γ₀⁻¹ : Γ)) : PO n 1) • ((((γ₀ : Γ)) : PO n 1) • u)) := by rw [h2]
      _ = hdist x₀ ((((γ₀ : Γ)) : PO n 1) • u) := hI.isom_smul _ _ _
      _ ≤ D := hD _ hγ₀
  have hfinS : ∀ R : ℝ, {γ : Γ | hdist ((γ : PO n 1) • x₀) x₀ ≤ R}.Finite := by
    intro R
    refine (finite_nearStab hA hI hΓdisc (2 * hdist (0 : E n) x₀ + R)).subset ?_
    intro γ hγ
    simp only [Set.mem_ofPred_eq] at hγ
    have h2 : hdist (0 : E n) ((γ : PO n 1) • x₀) ≤ hdist (0 : E n) x₀ + R := by
      have ht := hI.triangle (0 : E n) x₀ ((γ : PO n 1) • x₀)
      have hsym : hdist x₀ ((γ : PO n 1) • x₀) = hdist ((γ : PO n 1) • x₀) x₀ := hI.symm _ _
      rw [hsym] at ht
      linarith
    have h1 : hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤
        hdist (0 : E n) ((γ : PO n 1) • x₀) + hdist ((γ : PO n 1) • x₀) ((γ : PO n 1) • (0 : E n)) :=
      hI.triangle _ _ _
    have h3 : hdist ((γ : PO n 1) • x₀) ((γ : PO n 1) • (0 : E n)) = hdist x₀ (0 : E n) :=
      hI.isom_smul _ _ _
    have hsym2 : hdist x₀ (0 : E n) = hdist (0 : E n) x₀ := hI.symm _ _
    rw [h3, hsym2] at h1
    calc hdist (0 : E n) ((γ : PO n 1) • (0 : E n))
        ≤ hdist (0 : E n) ((γ : PO n 1) • x₀) + hdist (0 : E n) x₀ := h1
      _ ≤ (hdist (0 : E n) x₀ + R) + hdist (0 : E n) x₀ := by linarith
      _ = 2 * hdist (0 : E n) x₀ + R := by ring
  let Rb : ℝ := max (2 * D + 1) 0
  have hDRb : D ≤ Rb := by
    rcases lt_or_ge (0 : ℝ) D with h | h
    · exact le_trans (by linarith) (le_max_left _ _)
    · exact le_trans h (le_max_right _ _)
  obtain ⟨Cmax, hCmax⟩ : ∃ Cmax : ℝ, ∀ γ : Γ, hdist ((γ : PO n 1) • x₀) x₀ ≤ Rb →
      hdist (0 : E n) ((f γ : PO n 1) • (0 : E n)) ≤ Cmax := by
    have himg : ((fun γ : Γ => hdist (0 : E n) ((f γ : PO n 1) • (0 : E n))) ''
        {γ : Γ | hdist ((γ : PO n 1) • x₀) x₀ ≤ Rb}).Finite := (hfinS Rb).image _
    obtain ⟨Cmax, hCmax⟩ := himg.bddAbove
    exact ⟨Cmax, fun γ hγ => hCmax ⟨γ, hγ, rfl⟩⟩
  let γc : (u : E n) → u ∈ X → Γ := fun u hu => Classical.choose (hex u hu)
  have hγc : ∀ u (hu : u ∈ X), hdist ((γc u hu : PO n 1) • x₀) u ≤ D :=
    fun u hu => Classical.choose_spec (hex u hu)
  let Φ : E n → E n := fun u => if hu : u ∈ X then ((f (γc u hu) : PO n 1)) • (0 : E n) else 0
  refine ⟨Φ, ?_, ?_, ?_⟩
  · refine ⟨max Cmax 0, le_max_right _ _, ?_⟩
    intro u hu v hv huv
    have huΦ : Φ u = ((f (γc u hu) : PO n 1)) • (0 : E n) := dite_eq_left hu
    have hvΦ : Φ v = ((f (γc v hv) : PO n 1)) • (0 : E n) := dite_eq_left hv
    rw [huΦ, hvΦ]
    have hD₁ : hdist ((γc u hu : PO n 1) • x₀) u ≤ D := hγc u hu
    have hD₂ : hdist ((γc v hv : PO n 1) • x₀) v ≤ D := hγc v hv
    have hδd : hdist ((((γc v hv)⁻¹ * (γc u hu) : Γ) : PO n 1) • x₀) x₀ ≤ Rb := by
      rw [hdist_coe_inv_mul hA hI (γc v hv) (γc u hu) x₀]
      have hstep : hdist ((γc u hu : PO n 1) • x₀) ((γc v hv : PO n 1) • x₀) ≤ 2 * D + 1 := by
        have hvv : hdist v ((γc v hv : PO n 1) • x₀) ≤ D := by
          rw [hI.symm]; exact hD₂
        calc hdist ((γc u hu : PO n 1) • x₀) ((γc v hv : PO n 1) • x₀)
            ≤ hdist ((γc u hu : PO n 1) • x₀) v + hdist v ((γc v hv : PO n 1) • x₀) := hI.triangle _ _ _
          _ ≤ (D + 1) + D := by
                have hv1 : hdist ((γc u hu : PO n 1) • x₀) v ≤ D + 1 := by
                  have := hI.triangle ((γc u hu : PO n 1) • x₀) u v
                  linarith [hD₁, huv, this]
                linarith [hv1, hvv]
          _ = 2 * D + 1 := by ring
      exact le_trans hstep (le_max_left _ _)
    rw [hdist_f_mul hA hI f (γc u hu) (γc v hv)]
    exact le_trans (hCmax ((γc v hv)⁻¹ * (γc u hu)) hδd) (le_max_left _ _)
  · intro γ
    refine ⟨max Cmax 0, ?_⟩
    intro u hu
    have huX : ((γ : PO n 1) • u) ∈ X := hinv γ u hu
    have hΦ1 : Φ ((γ : PO n 1) • u) =
        ((f (γc ((γ : PO n 1) • u) huX) : PO n 1)) • (0 : E n) := dite_eq_left huX
    have hΦ2 : Φ u = ((f (γc u hu) : PO n 1)) • (0 : E n) := dite_eq_left hu
    rw [hΦ1, hΦ2]
    have haD : hdist ((γc ((γ : PO n 1) • u) huX : PO n 1) • x₀) ((γ : PO n 1) • u) ≤ D := hγc _ huX
    have hbD : hdist ((γc u hu : PO n 1) • x₀) u ≤ D := hγc u hu
    have hgb : (f γ : PO n 1) • ((f (γc u hu) : PO n 1) • (0 : E n)) =
        ((f (γ * γc u hu) : PO n 1)) • (0 : E n) := by
      rw [← hA.mul_smul]
      congr 1
      rw [← Subgroup.coe_mul, ← map_mul]
    rw [hgb]
    have hδd : hdist (((((γ * γc u hu)⁻¹ * γc ((γ : PO n 1) • u) huX : Γ)) : PO n 1) • x₀) x₀ ≤ Rb := by
      rw [hdist_coe_inv_mul hA hI (γ * γc u hu) (γc ((γ : PO n 1) • u) huX) x₀]
      have hstep : hdist ((γc ((γ : PO n 1) • u) huX : PO n 1) • x₀) (((γ * γc u hu : Γ) : PO n 1) • x₀) ≤ 2 * D := by
        have hgbx : (((γ * γc u hu : Γ) : PO n 1) • x₀) = (γ : PO n 1) • ((γc u hu : PO n 1) • x₀) :=
          hA.mul_smul _ _ _
        have h2 : hdist ((γ : PO n 1) • u) (((γ * γc u hu : Γ) : PO n 1) • x₀) ≤ D :=
          (hI.symm _ _).trans_le (by rw [hgbx, hI.isom_smul]; exact hbD)
        calc hdist ((γc ((γ : PO n 1) • u) huX : PO n 1) • x₀) (((γ * γc u hu : Γ) : PO n 1) • x₀)
            ≤ hdist ((γc ((γ : PO n 1) • u) huX : PO n 1) • x₀) ((γ : PO n 1) • u)
              + hdist ((γ : PO n 1) • u) (((γ * γc u hu : Γ) : PO n 1) • x₀) := hI.triangle _ _ _
          _ ≤ D + D := by linarith [haD, h2]
          _ = 2 * D := by ring
      exact le_trans hstep (le_trans (by linarith) (le_max_left _ _))
    rw [hdist_f_mul hA hI f (γc ((γ : PO n 1) • u) huX) (γ * γc u hu)]
    exact le_trans (hCmax ((γ * γc u hu)⁻¹ * γc ((γ : PO n 1) • u) huX) hδd) (le_max_left _ _)
  · refine ⟨max (Cmax + DΛ) 0, ?_⟩
    intro w hw
    obtain ⟨m, hm⟩ := hcptΛ w hw
    obtain ⟨γ₀, hγ₀⟩ : ∃ γ : Γ, f γ = m⁻¹ := ⟨f.symm m⁻¹, f.apply_symm_apply m⁻¹⟩
    refine ⟨((γ₀ : PO n 1) • x₀), hinv γ₀ x₀ hx₀, ?_⟩
    have huX : ((γ₀ : PO n 1) • x₀) ∈ X := hinv γ₀ x₀ hx₀
    have hΦu : Φ ((γ₀ : PO n 1) • x₀) =
        ((f (γc ((γ₀ : PO n 1) • x₀) huX) : PO n 1)) • (0 : E n) := dite_eq_left huX
    have haD : hdist ((γc ((γ₀ : PO n 1) • x₀) huX : PO n 1) • x₀) ((γ₀ : PO n 1) • x₀) ≤ D := hγc _ huX
    have hδd : hdist ((((γ₀⁻¹ * γc ((γ₀ : PO n 1) • x₀) huX : Γ)) : PO n 1) • x₀) x₀ ≤ Rb := by
      rw [hdist_coe_inv_mul hA hI γ₀ (γc ((γ₀ : PO n 1) • x₀) huX) x₀]
      exact le_trans haD hDRb
    have hclose : hdist (Φ ((γ₀ : PO n 1) • x₀)) ((f γ₀ : PO n 1) • (0 : E n)) ≤ Cmax := by
      rw [hΦu, hdist_f_mul hA hI f (γc ((γ₀ : PO n 1) • x₀) huX) γ₀]
      exact hCmax (γ₀⁻¹ * γc ((γ₀ : PO n 1) • x₀) huX) hδd
    have hw2 : hdist ((f γ₀ : PO n 1) • (0 : E n)) w ≤ DΛ := by
      have hmw : (f γ₀ : PO n 1) • ((m : PO n 1) • w) = w := by
        rw [hγ₀, ← hA.mul_smul]
        have hc : (((m⁻¹ : Λ) : PO n 1)) * ((m : Λ) : PO n 1) = 1 := by
          rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
        rw [hc, hA.one_smul]
      calc hdist ((f γ₀ : PO n 1) • (0 : E n)) w
          = hdist ((f γ₀ : PO n 1) • (0 : E n)) ((f γ₀ : PO n 1) • ((m : PO n 1) • w)) := by rw [hmw]
        _ = hdist (0 : E n) ((m : PO n 1) • w) := hI.isom_smul _ _ _
        _ ≤ DΛ := hDΛ _ hm
    calc hdist (Φ ((γ₀ : PO n 1) • x₀)) w
        ≤ hdist (Φ ((γ₀ : PO n 1) • x₀)) ((f γ₀ : PO n 1) • (0 : E n))
          + hdist ((f γ₀ : PO n 1) • (0 : E n)) w := hI.triangle _ _ _
      _ ≤ Cmax + DΛ := by linarith [hclose, hw2]
      _ ≤ max (Cmax + DΛ) 0 := le_max_left _ _

end Work.Mostow
