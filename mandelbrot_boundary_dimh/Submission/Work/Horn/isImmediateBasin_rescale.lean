import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# Immediate parabolic basins are preserved by the rescaling `ζ ↦ s · ζ`

Let `f` be a map with an immediate parabolic basin `B ⊆ D` (in the sense of
`MandelDim.IsImmediateBasin`).  For `s ≠ 0` put

* `g ζ = s * f (ζ / s)`  (the affine conjugate of `f` by `ζ ↦ s · ζ`, resp. `ζ ↦ ζ / s`),
* `D' = (ζ ↦ s · ζ) '' D`,  `B' = (ζ ↦ s · ζ) '' B`.

Then `B'` is an immediate parabolic basin for `g` on `D'`.  The two identities driving
everything are the orbit identity

  `g^[n] (s * z) = s * (f^[n] z)`   (`resc_iterate`)

and its consequence on the basin (`mem_parabolicBasin_rescale`); the remaining clauses
(openness, connectedness, maximality, invariance, surjectivity, properness) are transported
along the homeomorphism `ζ ↦ s · ζ` (with inverse `ζ ↦ s⁻¹ · ζ`).
-/

namespace Work.Horn

open Set Filter Topology Metric
open scoped Topology

/-- The rescaling is a conjugacy of iterates: `(ζ ↦ s * f (ζ/s))^[n] (s * z) = s * f^[n] z`. -/
private lemma resc_iterate {s : ℂ} (hs : s ≠ 0) (f : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    (fun ζ : ℂ => s * f (ζ / s))^[n] (s * z) = s * f^[n] z := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      rw [mul_div_cancel_left₀ (f^[n] z) hs]

/-- Membership in the rescaled set `(ζ ↦ s * ζ) '' C`. -/
private lemma mem_smul_image_iff {s : ℂ} (hs : s ≠ 0) (C : Set ℂ) (w : ℂ) :
    w ∈ (fun ζ : ℂ => s * ζ) '' C ↔ s⁻¹ * w ∈ C := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [inv_mul_cancel_left₀ hs z]
  · intro hw
    exact ⟨s⁻¹ * w, hw, mul_inv_cancel_left₀ hs w⟩

/-- The parabolic basin is transported by the rescaling. -/
private lemma mem_parabolicBasin_rescale {s : ℂ} (hs : s ≠ 0) (f : ℂ → ℂ) (D : Set ℂ)
    (z : ℂ) :
    z ∈ MandelDim.ParabolicBasin f D ↔
      s * z ∈ MandelDim.ParabolicBasin (fun ζ : ℂ => s * f (ζ / s))
        ((fun ζ : ℂ => s * ζ) '' D) := by
  have hs' : s⁻¹ ≠ 0 := inv_ne_zero hs
  have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hspos' : 0 < ‖s⁻¹‖ := norm_pos_iff.mpr hs'
  have hopen : IsOpenMap (fun ζ : ℂ => s * ζ) := by
    simpa [smul_eq_mul] using isOpenMap_smul₀ (G₀ := ℂ) (α := ℂ) hs
  have hopen' : IsOpenMap (fun ζ : ℂ => s⁻¹ * ζ) := by
    simpa [smul_eq_mul] using isOpenMap_smul₀ (G₀ := ℂ) (α := ℂ) hs'
  constructor
  · rintro ⟨U, hU, hmap, hconv⟩
    refine ⟨(fun ζ : ℂ => s * ζ) '' U, hopen.image_mem_nhds hU, ?_, ?_⟩
    · intro n y hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨f^[n] x, hmap n hx, (resc_iterate hs f n x).symm⟩
    · rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
      intro ε hε
      have hε' : 0 < ε / ‖s‖ := div_pos hε hspos
      filter_upwards [hconv (ε / ‖s‖) hε'] with n hn y hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [resc_iterate hs f n x, dist_zero_left, norm_mul]
      calc ‖s‖ * ‖f^[n] x‖ < ‖s‖ * (ε / ‖s‖) :=
            mul_lt_mul_of_pos_left (by simpa using hn x hx) hspos
        _ = ε := by
            rw [← mul_div_assoc, mul_div_cancel_left₀ ε (norm_ne_zero_iff.mpr hs)]
  · rintro ⟨V, hV, hmap, hconv⟩
    refine ⟨(fun ζ : ℂ => s⁻¹ * ζ) '' V, ?_, ?_, ?_⟩
    · simpa [inv_mul_cancel_left₀ hs z] using hopen'.image_mem_nhds hV
    · intro n y hy
      obtain ⟨v, hv, rfl⟩ := hy
      obtain ⟨d, hd, hd_eq⟩ := hmap n hv
      have hg := resc_iterate hs f n (s⁻¹ * v)
      rw [mul_inv_cancel_left₀ hs v] at hg
      have hf : f^[n] (s⁻¹ * v) = d := mul_left_cancel₀ hs (hg.symm.trans hd_eq.symm)
      rwa [hf]
    · rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
      intro ε hε
      have hε' : 0 < ε * ‖s‖ := mul_pos hε hspos
      filter_upwards [hconv (ε * ‖s‖) hε'] with n hn y hy
      obtain ⟨v, hv, rfl⟩ := hy
      have hg := resc_iterate hs f n (s⁻¹ * v)
      rw [mul_inv_cancel_left₀ hs v] at hg
      have hfv : f^[n] (s⁻¹ * v) = s⁻¹ * (fun ζ : ℂ => s * f (ζ / s))^[n] v := by
        rw [hg]
        exact (inv_mul_cancel_left₀ hs _).symm
      rw [hfv, dist_zero_left, norm_mul]
      calc ‖s⁻¹‖ * ‖(fun ζ : ℂ => s * f (ζ / s))^[n] v‖
          < ‖s⁻¹‖ * (ε * ‖s‖) :=
            mul_lt_mul_of_pos_left (by simpa using hn v hv) hspos'
        _ = ε := by
            have h : ‖s⁻¹‖ * ‖s‖ = 1 := by
              rw [norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hs)]
            calc ‖s⁻¹‖ * (ε * ‖s‖) = ε * (‖s⁻¹‖ * ‖s‖) := by ring
              _ = ε := by rw [h, mul_one]

theorem isImmediateBasin_rescale {f : ℂ → ℂ} {D B : Set ℂ} {s : ℂ} (hs : s ≠ 0)
    (h : MandelDim.IsImmediateBasin f D B) :
    MandelDim.IsImmediateBasin (fun ζ : ℂ => s * f (ζ / s)) ((fun ζ : ℂ => s * ζ) '' D)
      ((fun ζ : ℂ => s * ζ) '' B) := by
  have hs' : s⁻¹ ≠ 0 := inv_ne_zero hs
  obtain ⟨hBopen, hBconn, hBsub, hBmax, hBmaps, hBsurj, hBprop⟩ := h
  have hopen : IsOpenMap (fun ζ : ℂ => s * ζ) := by
    simpa [smul_eq_mul] using isOpenMap_smul₀ (G₀ := ℂ) (α := ℂ) hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- openness
    exact hopen B hBopen
  · -- connectedness
    exact hBconn.image _ (continuous_const_mul s).continuousOn
  · -- `B'` sits inside the rescaled basin
    intro w hw
    have hwB : s⁻¹ * w ∈ B := (mem_smul_image_iff hs B w).mp hw
    have hbas := (mem_parabolicBasin_rescale hs f D (s⁻¹ * w)).mp (hBsub hwB)
    rwa [mul_inv_cancel_left₀ hs w] at hbas
  · -- maximality: `B'` contains every preconnected subset of the basin meeting it
    intro C hCconn hCsub hCne
    have hC'conn : IsPreconnected ((fun ζ : ℂ => s⁻¹ * ζ) '' C) :=
      hCconn.image _ (continuous_const_mul s⁻¹).continuousOn
    have hC'sub : (fun ζ : ℂ => s⁻¹ * ζ) '' C ⊆ MandelDim.ParabolicBasin f D := by
      rintro y ⟨c, hc, rfl⟩
      have hmem : s * (s⁻¹ * c) ∈
          MandelDim.ParabolicBasin (fun ζ : ℂ => s * f (ζ / s)) ((fun ζ : ℂ => s * ζ) '' D) := by
        simpa only [mul_inv_cancel_left₀ hs c] using hCsub hc
      exact (mem_parabolicBasin_rescale hs f D (s⁻¹ * c)).mpr hmem
    have hC'ne : (B ∩ (fun ζ : ℂ => s⁻¹ * ζ) '' C).Nonempty := by
      obtain ⟨w, hwSB, hwC⟩ := hCne
      exact ⟨s⁻¹ * w, (mem_smul_image_iff hs B w).mp hwSB, ⟨w, hwC, rfl⟩⟩
    have hCB : (fun ζ : ℂ => s⁻¹ * ζ) '' C ⊆ B := hBmax _ hC'conn hC'sub hC'ne
    intro c hc
    exact ⟨s⁻¹ * c, hCB ⟨c, hc, rfl⟩, mul_inv_cancel_left₀ hs c⟩
  · -- forward invariance
    rintro w ⟨b, hb, rfl⟩
    change s * f (s * b / s) ∈ (fun ζ : ℂ => s * ζ) '' B
    rw [mul_div_cancel_left₀ b hs]
    exact ⟨f b, hBmaps hb, rfl⟩
  · -- surjectivity onto itself
    rintro w ⟨b, hb, rfl⟩
    obtain ⟨b₀, hb₀, hb₀eq⟩ := hBsurj hb
    refine ⟨s * b₀, ⟨b₀, hb₀, rfl⟩, ?_⟩
    change s * f (s * b₀ / s) = s * b
    rw [mul_div_cancel_left₀ b₀ hs, hb₀eq]
  · -- properness
    intro L' hL'sub hL'compact
    set L : Set ℂ := (fun ζ : ℂ => s * ζ) ⁻¹' L' with hLdef
    have hLimg : L = (fun ζ : ℂ => s⁻¹ * ζ) '' L' := by
      ext y
      constructor
      · intro hy
        exact ⟨s * y, hy, inv_mul_cancel_left₀ hs y⟩
      · rintro ⟨l, hl, rfl⟩
        change s * (s⁻¹ * l) ∈ L'
        rwa [mul_inv_cancel_left₀ hs l]
    have hLsub : L ⊆ B := by
      intro y hy
      have hy' : s * y ∈ L' := hy
      have hyB : s * y ∈ (fun ζ : ℂ => s * ζ) '' B := hL'sub hy'
      obtain ⟨b, hb, hb_eq⟩ := hyB
      have : y = b := mul_left_cancel₀ hs hb_eq.symm
      rwa [this]
    have hLcompact : IsCompact L := by
      rw [hLimg]
      exact hL'compact.image (continuous_const_mul s⁻¹)
    have hprop := hBprop L hLsub hLcompact
    have hset : (fun ζ : ℂ => s * ζ) '' (B ∩ f ⁻¹' L)
        = ((fun ζ : ℂ => s * ζ) '' B) ∩ (fun ζ : ℂ => s * f (ζ / s)) ⁻¹' L' := by
      ext w
      constructor
      · rintro ⟨b, ⟨hbB, hbf⟩, rfl⟩
        refine ⟨⟨b, hbB, rfl⟩, ?_⟩
        change s * f (s * b / s) ∈ L'
        rw [mul_div_cancel_left₀ b hs]
        exact hbf
      · rintro ⟨hwSB, hwg⟩
        obtain ⟨b, hbB, rfl⟩ := hwSB
        refine ⟨b, ⟨hbB, ?_⟩, rfl⟩
        change s * f b ∈ L'
        have h := hwg
        change s * f (s * b / s) ∈ L' at h
        rwa [mul_div_cancel_left₀ b hs] at h
    rw [← hset]
    exact hprop.image (continuous_const_mul s)

end Work.Horn
