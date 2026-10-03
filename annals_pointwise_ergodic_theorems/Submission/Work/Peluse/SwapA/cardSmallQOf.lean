import Mathlib
import Submission.Work.Peluse.SwapA.genDefs

namespace Work.Peluse.SwapA

/-- **(small-slope count)** For a nonzero sign pattern `ω : Fin t → Bool`, the number of plugs
`v = (h,h') ∈ [H]^t × [H]^t` with `|ω·(h−h')| < ηH` is at most `(2η + 1/H)·H^(2t)`, where
`Work.Peluse.SwapA.Plug t H = (Fin t → Fin H) × (Fin t → Fin H)` and
`Work.Peluse.SwapA.qOf ω v = ω·(h−h')`.  Useful helpers in `Submission.Work.Peluse.SwapA.genDefs`:
`qOf_eq_linForm` and `linForm_fiber_card` (a fibre of `linForm ω` has at most `H^(t-1)` points). -/
theorem cardSmallQOf {t H : ℕ} (ht : 1 ≤ t) (hH : 1 ≤ H)
    (ω : Fin t → Bool) (hω : ω ≠ 0) {η : ℝ} (hη : 0 ≤ η) :
    ((Finset.univ.filter (fun v : Work.Peluse.SwapA.Plug t H =>
        |Work.Peluse.SwapA.qOf ω v| < η * (H : ℝ))).card : ℝ)
      ≤ (2 * η + 1 / (H : ℝ)) * (Fintype.card (Work.Peluse.SwapA.Plug t H) : ℝ) := by
  classical
  -- The set of plugs under consideration, the integer cut-off `M = ⌊ηH⌋` and the range of
  -- possible values of `qOf ω`.
  set s : Finset (Plug t H) :=
    Finset.univ.filter (fun v : Plug t H => |qOf ω v| < η * (H:ℝ)) with hs
  set M : ℤ := ⌊η * (H:ℝ)⌋ with hM
  set tset : Finset ℤ := Finset.Icc (-M) M with htset
  have hHpos : (0:ℝ) < (H:ℝ) := by exact_mod_cast (show 0 < H by omega)
  have hMnonneg : (0:ℤ) ≤ M := by
    rw [hM]
    refine Int.le_floor.mpr ?_
    simpa using mul_nonneg hη (le_of_lt hHpos)
  -- Every value of `qOf ω` on `s` is an integer of absolute value `< ηH`, hence lies in
  -- `[-⌊ηH⌋, ⌊ηH⌋]`.
  have hmap : ∀ v ∈ s, qOf ω v ∈ tset := by
    intro v hv
    rw [hs, Finset.mem_filter] at hv
    obtain ⟨-, hv⟩ := hv
    rw [Int.cast_abs, abs_lt] at hv
    rw [htset, Finset.mem_Icc]
    constructor
    · have hle : -(qOf ω v) ≤ M := by
        rw [hM]
        exact Int.le_floor.mpr (by push_cast; linarith [hv.1])
      omega
    · rw [hM]
      exact Int.le_floor.mpr (le_of_lt hv.2)
  -- Each fibre of `qOf ω` has at most `H^t * H^(t-1)` points: fixing `h`, the second tuple `h'`
  -- is constrained by a fibre of the linear form `linForm ω`.
  have hfiball : ∀ b : ℤ,
      (Finset.univ.filter (fun v : Plug t H => qOf ω v = b)).card ≤ H^t * H^(t-1) := by
    intro b
    set T : Finset (Plug t H) := Finset.univ.filter (fun v : Plug t H => qOf ω v = b) with hT
    have hmaps : ∀ v ∈ T, v.1 ∈ (Finset.univ : Finset (Fin t → Fin H)) := by
      intro v _; exact Finset.mem_univ _
    have hf : ∀ h ∈ (Finset.univ : Finset (Fin t → Fin H)),
        (T.filter (fun v => v.1 = h)).card ≤ H^(t-1) := by
      intro h _
      have hinj : Set.InjOn (fun v : Plug t H => v.2) ↑(T.filter (fun v => v.1 = h)) := by
        intro v hv w hw heq
        simp only [Finset.mem_coe, Finset.mem_filter] at hv hw
        exact Prod.ext (by rw [hv.2, hw.2]) heq
      have hmaps2 : Set.MapsTo (fun v : Plug t H => v.2) ↑(T.filter (fun v => v.1 = h))
          ↑(Finset.univ.filter (fun h' : Fin t → Fin H => linForm ω h' = linForm ω h - b)) := by
        intro v hv
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        obtain ⟨hvT, hv1⟩ := hv
        rw [hT, Finset.mem_filter] at hvT
        have hq : qOf ω v = b := hvT.2
        rw [qOf_eq_linForm, hv1] at hq
        linarith
      have hcard := Finset.card_le_card_of_injOn (fun v : Plug t H => v.2) hmaps2 hinj
      have h2 := linForm_fiber_card (H := H) hω (linForm ω h - b)
      have h3 : ((T.filter (fun v => v.1 = h)).card : ℝ)
          ≤ ((Finset.univ.filter (fun h' : Fin t → Fin H =>
              linForm ω h' = linForm ω h - b)).card : ℝ) := by exact_mod_cast hcard
      have h4 : ((H^(t-1) : ℕ) : ℝ) = (H:ℝ)^(t-1) := by rw [Nat.cast_pow]
      have : ((T.filter (fun v => v.1 = h)).card : ℝ) ≤ ((H^(t-1) : ℕ) : ℝ) := by
        rw [h4]; linarith
      exact Nat.cast_le.mp this
    have hmain := Finset.card_le_mul_card_image_of_maps_to hmaps (H^(t-1)) hf
    have hU : (Finset.univ : Finset (Fin t → Fin H)).card = H^t := by
      simp
    rw [hU] at hmain
    have hgoal : T.card ≤ H^t * H^(t-1) := by
      calc T.card ≤ H^(t-1) * H^t := hmain
        _ = H^t * H^(t-1) := by ring
    exact hgoal
  have hfib : ∀ b ∈ tset, (s.filter (fun v => qOf ω v = b)).card ≤ H^t * H^(t-1) := by
    intro b _
    refine le_trans (Finset.card_le_card ?_) (hfiball b)
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hv.2
  -- Assembly: `#s ≤ #tset * H^t * H^(t-1)`.
  have hmain2 := Finset.card_le_mul_card_image_of_maps_to hmap (H^t * H^(t-1)) hfib
  have htsetcard : (tset.card : ℝ) ≤ 2 * (η * (H:ℝ)) + 1 := by
    have hcard : (tset.card : ℤ) = 2*M + 1 := by
      rw [htset, Int.card_Icc, show M + 1 - (-M) = 2*M+1 by ring]
      exact Int.toNat_of_nonneg (by omega)
    have hcast : (tset.card : ℝ) = ((2*M+1 : ℤ) : ℝ) := by exact_mod_cast hcard
    rw [hcast]
    have hfl := Int.floor_le (η * (H:ℝ))
    rw [← hM] at hfl
    push_cast
    linarith
  have hA : (s.card : ℝ) ≤ (H:ℝ)^t * (H:ℝ)^(t-1) * (2 * (η * (H:ℝ)) + 1) := by
    have h1 : (s.card : ℝ) ≤ ((H^t * H^(t-1) : ℕ) : ℝ) * (tset.card : ℝ) := by
      exact_mod_cast hmain2
    have h2 : ((H^t * H^(t-1) : ℕ) : ℝ) = (H:ℝ)^t * (H:ℝ)^(t-1) := by push_cast; ring
    have h3 : (0:ℝ) ≤ ((H^t * H^(t-1) : ℕ) : ℝ) := by positivity
    calc (s.card : ℝ) ≤ ((H^t * H^(t-1) : ℕ) : ℝ) * (tset.card : ℝ) := h1
      _ ≤ ((H^t * H^(t-1) : ℕ) : ℝ) * (2 * (η * (H:ℝ)) + 1) :=
          mul_le_mul_of_nonneg_left htsetcard h3
      _ = (H:ℝ)^t * (H:ℝ)^(t-1) * (2 * (η * (H:ℝ)) + 1) := by rw [h2]
  have hsub : (H:ℝ)^t = (H:ℝ)^(t-1) * (H:ℝ) := by
    conv_lhs => rw [← Nat.sub_add_cancel ht]
    rw [pow_succ]
  have hK : (2 * η + 1/(H:ℝ)) * (H:ℝ) = 2 * (η * (H:ℝ)) + 1 := by
    have hne : (H:ℝ) ≠ 0 := ne_of_gt hHpos
    field_simp
  have hplug : (Fintype.card (Plug t H) : ℝ) = (H:ℝ)^t * (H:ℝ)^t := by
    have hc : Fintype.card (Plug t H) = H^t * H^t := by
      simp [Plug, Fintype.card_prod]
    rw [hc]; push_cast; ring
  rw [hplug]
  calc (s.card : ℝ) ≤ (H:ℝ)^t * (H:ℝ)^(t-1) * (2 * (η * (H:ℝ)) + 1) := hA
    _ = (2 * η + 1/(H:ℝ)) * ((H:ℝ)^t * (H:ℝ)^t) := by rw [← hK, hsub]; ring

end Work.Peluse.SwapA
