import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.HornParts

namespace Work.Horn.HBb

open MandelDim Set Metric Filter Topology

theorem LF_rescale {G : ℂ → ℂ} {D : Set ℂ} {s : ℂ} (hs : s ≠ 0) {v : ℂ} {r : ℝ}
    (hLF : ∀ x ∈ D, G x ∈ Metric.ball v r → ∀ K ⊆ Metric.ball v r, IsCompact K →
      IsCompact (connectedComponentIn (D ∩ G ⁻¹' Metric.ball v r) x ∩ G ⁻¹' K)) :
    ∀ x ∈ (fun ζ : ℂ => s * ζ) '' D,
      (fun ζ : ℂ => s * G (ζ / s)) x ∈ Metric.ball (s * v) (‖s‖ * r) →
      ∀ K ⊆ Metric.ball (s * v) (‖s‖ * r), IsCompact K →
        IsCompact (connectedComponentIn
          (((fun ζ : ℂ => s * ζ) '' D) ∩
            (fun ζ : ℂ => s * G (ζ / s)) ⁻¹' Metric.ball (s * v) (‖s‖ * r)) x ∩
          (fun ζ : ℂ => s * G (ζ / s)) ⁻¹' K) := by
  -- The map `S ζ = s * ζ` is a homeomorphism of `ℂ` (as `s ≠ 0`), and the rescaled datum is
  -- the transport of the original one by `S`: `S '' D`, and `G' = S ∘ G ∘ S⁻¹`.
  intro x hx hGx K hKsub hKcomp
  obtain ⟨d, hdD, hxd⟩ := hx
  have hsnorm : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hinj : Function.Injective (fun ζ : ℂ => s * ζ) := fun a b hab => mul_left_cancel₀ hs hab
  have hcontS : Continuous (fun ζ : ℂ => s * ζ) := continuous_const.mul continuous_id
  have hcontT : Continuous (fun w : ℂ => w / s) := continuous_id.div_const s
  let h : ℂ ≃ₜ ℂ :=
    { toFun := fun ζ : ℂ => s * ζ
      invFun := fun w : ℂ => w / s
      left_inv := fun z => mul_div_cancel_left₀ z hs
      right_inv := fun w => mul_div_cancel₀ w hs
      continuous_toFun := hcontS
      continuous_invFun := hcontT }
  have hxs : x / s = d := by rw [← hxd]; exact mul_div_cancel_left₀ d hs
  have hx'D : x / s ∈ D := by rw [hxs]; exact hdD
  -- the pullback point satisfies the original hypothesis
  have hGx' : G (x / s) ∈ Metric.ball v r := by
    rw [hxs]
    have hbd : s * G d ∈ Metric.ball (s * v) (‖s‖ * r) := by
      have h := hGx
      rw [← hxd] at h
      simpa [mul_div_cancel_left₀ d hs] using h
    rw [Metric.mem_ball, Complex.dist_eq] at hbd ⊢
    rw [← mul_sub, norm_mul] at hbd
    exact lt_of_mul_lt_mul_left hbd (le_of_lt hsnorm)
  -- the pullback compactum is compact and contained in the original ball
  have hK'sub : ((fun w : ℂ => w / s) '' K) ⊆ Metric.ball v r := by
    rintro y ⟨w, hw, rfl⟩
    have hw' : w ∈ Metric.ball (s * v) (‖s‖ * r) := hKsub hw
    rw [Metric.mem_ball, Complex.dist_eq] at hw' ⊢
    have hsub : w / s - v = (w - s * v) / s := by
      rw [sub_div, mul_div_cancel_left₀ v hs]
    rw [hsub, div_eq_mul_inv, norm_mul, norm_inv]
    have h1 : ‖s‖⁻¹ * ‖w - s * v‖ < ‖s‖⁻¹ * (‖s‖ * r) :=
      mul_lt_mul_of_pos_left hw' (inv_pos.mpr hsnorm)
    have h2 : ‖s‖⁻¹ * (‖s‖ * r) = r := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hsnorm), one_mul]
    calc ‖w - s * v‖ * ‖s‖⁻¹ = ‖s‖⁻¹ * ‖w - s * v‖ := mul_comm _ _
      _ < ‖s‖⁻¹ * (‖s‖ * r) := h1
      _ = r := h2
  have hK'comp : IsCompact (((fun w : ℂ => w / s) '' K)) := hKcomp.image hcontT
  -- the original local finiteness hypothesis at the pullback point
  have hcomp : IsCompact (connectedComponentIn (D ∩ G ⁻¹' Metric.ball v r) (x / s) ∩
      G ⁻¹' ((fun w : ℂ => w / s) '' K)) :=
    hLF (x / s) hx'D hGx' _ hK'sub hK'comp
  -- the transported ambient set is the image of the original one
  have hA : ((fun ζ : ℂ => s * ζ) '' D) ∩
        (fun ζ : ℂ => s * G (ζ / s)) ⁻¹' Metric.ball (s * v) (‖s‖ * r)
      = (fun ζ : ℂ => s * ζ) '' (D ∩ G ⁻¹' Metric.ball v r) := by
    ext y
    constructor
    · rintro ⟨hyD, hyb⟩
      obtain ⟨z, hzD, rfl⟩ := hyD
      refine ⟨z, ⟨hzD, ?_⟩, rfl⟩
      have hbd : s * G z ∈ Metric.ball (s * v) (‖s‖ * r) := by
        simpa [mul_div_cancel_left₀ z hs] using hyb
      simp only [Set.mem_preimage, Metric.mem_ball, Complex.dist_eq] at hbd ⊢
      rw [← mul_sub, norm_mul] at hbd
      exact lt_of_mul_lt_mul_left hbd (le_of_lt hsnorm)
    · rintro ⟨z, ⟨hzD, hzb⟩, rfl⟩
      refine ⟨⟨z, hzD, rfl⟩, ?_⟩
      have hbd : s * G z ∈ Metric.ball (s * v) (‖s‖ * r) := by
        simp only [Set.mem_preimage, Metric.mem_ball, Complex.dist_eq] at hzb ⊢
        rw [← mul_sub, norm_mul]
        exact mul_lt_mul_of_pos_left hzb hsnorm
      simpa [mul_div_cancel_left₀ z hs] using hbd
  -- the transported preimage is the image of the original preimage
  have hB : (fun ζ : ℂ => s * G (ζ / s)) ⁻¹' K
      = (fun ζ : ℂ => s * ζ) '' (G ⁻¹' ((fun w : ℂ => w / s) '' K)) := by
    ext y
    constructor
    · intro hy
      refine ⟨y / s, ?_, mul_div_cancel₀ y hs⟩
      exact ⟨s * G (y / s), hy, mul_div_cancel_left₀ (G (y / s)) hs⟩
    · rintro ⟨z, hz, hzy⟩
      obtain ⟨w, hw, hwz⟩ := hz
      rw [← hzy]
      change s * G ((s * z) / s) ∈ K
      rw [mul_div_cancel_left₀ z hs, ← hwz, mul_div_cancel₀ w hs]
      exact hw
  -- connected components are transported by the homeomorphism
  have hkey : connectedComponentIn ((fun ζ : ℂ => s * ζ) '' (D ∩ G ⁻¹' Metric.ball v r)) (s * (x / s))
      = (fun ζ : ℂ => s * ζ) '' connectedComponentIn (D ∩ G ⁻¹' Metric.ball v r) (x / s) :=
    (Homeomorph.image_connectedComponentIn h (s := D ∩ G ⁻¹' Metric.ball v r) ⟨hx'D, hGx'⟩).symm
  have hD : (fun ζ : ℂ => s * ζ) '' connectedComponentIn (D ∩ G ⁻¹' Metric.ball v r) (x / s) ∩
        (fun ζ : ℂ => s * ζ) '' (G ⁻¹' ((fun w : ℂ => w / s) '' K))
      = (fun ζ : ℂ => s * ζ) '' (connectedComponentIn (D ∩ G ⁻¹' Metric.ball v r) (x / s) ∩
          G ⁻¹' ((fun w : ℂ => w / s) '' K)) := (Set.image_inter hinj).symm
  have hxeq : x = s * (x / s) := (mul_div_cancel₀ x hs).symm
  rw [hxeq, hA, hB, hkey, hD]
  exact hcomp.image hcontS

end Work.Horn.HBb
