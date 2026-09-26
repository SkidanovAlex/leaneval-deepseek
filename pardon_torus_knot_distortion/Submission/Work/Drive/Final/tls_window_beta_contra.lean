import Mathlib
import Submission.Work.Drive.Final.tls_defs

/-!
# `Work.Drive.Final.tls_window_beta_contra`

The *window* contradiction for a level of the tilted sweep.

Write `B = Submission.PBox s c σ`, `f = ⟪v,·⟫`, `a = ⟪v,c⟫ + u`, `g = ℓ`, and let

* `tlsChunk = closure B ∩ {|f - a| ≤ h} ∩ {g ≤ lam}` be the chunk;
* `hwallP`, `hwallM` say that `B` contains points above the wall `{g > lam}` which lie strictly
  above (resp. strictly below) the slab `{|f - a| ≤ h}` in the `f`-direction;
* `hβ` say that the level `{g = lam}` meets `B` only *outside* the slab, i.e. only where
  `|f - a| > h`.

The hypotheses are contradictory: the two wall points and the point of `B ∩ tlsChunk` have
opposite signs of `g - lam`, so the segments joining them to the chunk point meet the level
`{g = lam}` at two points `z₁, z₂ ∈ B`, with `f z₁ ≤ a + h` and `f z₂ ≥ a - h` (convexity of `B`
together with the slab width).  By `hβ` this forces `f z₁ < a - h` and `f z₂ > a + h`; the segment
joining `z₁` to `z₂` therefore stays in `B` and in the level `{g = lam}` while its `f`-value crosses
`a`, contradicting `hβ` at the crossing point.

Mathlib has no counterpart; the content is the elementary convexity/`IVT` argument above.
-/

namespace Work.Drive.Final

/-- **The level-crossing point.**  If the box contains a point below the level `{g = lam}` and one
above it, then it contains a point of the segment joining them at the level `lam`. -/
private theorem tls_crossing {s : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {lam : ℝ}
    {p q : LeanEval.KnotTheory.PardonDistortion.R3}
    (hp : p ∈ Submission.PBox s c σ) (hq : q ∈ Submission.PBox s c σ)
    (hpℓ : ℓ p ≤ lam) (hqℓ : lam < ℓ q) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      (p + t • (q - p)) ∈ Submission.PBox s c σ ∧ ℓ (p + t • (q - p)) = lam := by
  have hcont : Continuous fun t : ℝ => ℓ (p + t • (q - p)) := by fun_prop
  have h0 : ℓ (p + (0 : ℝ) • (q - p)) ≤ lam := by simpa using hpℓ
  have h1 : lam ≤ ℓ (p + (1 : ℝ) • (q - p)) := by simpa using le_of_lt hqℓ
  obtain ⟨t, htmem, ht⟩ := (intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    hcont.continuousOn) ⟨h0, h1⟩
  refine ⟨t, htmem, ?_, ht⟩
  have hpt : p + t • (q - p) = (1 - t) • p + t • q := by module
  rw [hpt]
  exact (Work.Topology.SphereSlicing.convex_PBox s c σ) hp hq
    (by linarith [htmem.2]) htmem.1 (by ring)

theorem tls_window_beta_contra (s : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (u h lam : ℝ) (v : LeanEval.KnotTheory.PardonDistortion.R3)
    (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ)
    (hBK : (Submission.PBox s c σ ∩ Work.Drive.Final.tlsChunk s c σ u h lam v ℓ).Nonempty)
    (hwallP : ∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y ∧ lam < ℓ y)
    (hwallM : ∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h ∧ lam < ℓ y)
    (hβ : ∀ y ∈ Submission.PBox s c σ, ℓ y = lam → h < |inner ℝ v y - (inner ℝ v c + u)|) :
    False := by
  obtain ⟨p, hpbox, hpchunk⟩ := hBK
  -- the chunk point is in the slab and below the wall
  have hpabs : |inner ℝ v p - (inner ℝ v c + u)| ≤ h := hpchunk.1.2
  have hple : ℓ p ≤ lam := hpchunk.2
  have hh0 : 0 ≤ h := le_trans (abs_nonneg _) hpabs
  have hp_lo : inner ℝ v c + u - h ≤ inner ℝ v p := by linarith [(abs_le.mp hpabs).1]
  have hp_hi : inner ℝ v p ≤ inner ℝ v c + u + h := by linarith [(abs_le.mp hpabs).2]
  obtain ⟨yM, hyMbox, hyMf, hyMl⟩ := hwallM
  obtain ⟨yP, hyPbox, hyPf, hyPl⟩ := hwallP
  -- the two points of the level `{g = lam}` obtained from the segments to the two wall points
  obtain ⟨t₁, ht₁mem, hc₁box, hc₁ℓ⟩ := tls_crossing hpbox hyMbox hple hyMl
  obtain ⟨t₂, ht₂mem, hc₂box, hc₂ℓ⟩ := tls_crossing hpbox hyPbox hple hyPl
  have hval₁ : inner ℝ v (p + t₁ • (yM - p)) = (1 - t₁) * inner ℝ v p + t₁ * inner ℝ v yM := by
    rw [inner_add_right, inner_smul_right, inner_sub_right]; ring
  have hval₂ : inner ℝ v (p + t₂ • (yP - p)) = (1 - t₂) * inner ℝ v p + t₂ * inner ℝ v yP := by
    rw [inner_add_right, inner_smul_right, inner_sub_right]; ring
  -- their `f`-values, bounded by the slab width
  have hfc₁ : inner ℝ v (p + t₁ • (yM - p)) ≤ inner ℝ v c + u + h := by
    rw [hval₁]
    have h2 : t₁ * inner ℝ v yM ≤ t₁ * (inner ℝ v c + u + h) :=
      mul_le_mul_of_nonneg_left (by linarith) ht₁mem.1
    have h3 : (1 - t₁) * inner ℝ v p ≤ (1 - t₁) * (inner ℝ v c + u + h) :=
      mul_le_mul_of_nonneg_left hp_hi (by linarith [ht₁mem.2])
    nlinarith [h2, h3]
  have hfc₂ : inner ℝ v c + u - h ≤ inner ℝ v (p + t₂ • (yP - p)) := by
    rw [hval₂]
    have h2 : t₂ * (inner ℝ v c + u - h) ≤ t₂ * inner ℝ v yP :=
      mul_le_mul_of_nonneg_left (by linarith) ht₂mem.1
    have h3 : (1 - t₂) * (inner ℝ v c + u - h) ≤ (1 - t₂) * inner ℝ v p :=
      mul_le_mul_of_nonneg_left hp_lo (by linarith [ht₂mem.2])
    nlinarith [h2, h3]
  -- `hβ` then pushes both of them strictly outside the slab, on opposite sides
  have hlt₁ : inner ℝ v (p + t₁ • (yM - p)) < inner ℝ v c + u - h := by
    rcases lt_abs.mp (hβ _ hc₁box hc₁ℓ) with hX | hX
    · linarith
    · linarith
  have hgt₂ : inner ℝ v c + u + h < inner ℝ v (p + t₂ • (yP - p)) := by
    rcases lt_abs.mp (hβ _ hc₂box hc₂ℓ) with hX | hX
    · linarith
    · linarith
  -- a point of the segment between them where `f = a`
  have hcont : Continuous (fun t : ℝ =>
      inner ℝ v ((p + t₁ • (yM - p)) + t • ((p + t₂ • (yP - p)) - (p + t₁ • (yM - p))))
        - (inner ℝ v c + u)) := by fun_prop
  have hstart : inner ℝ v ((p + t₁ • (yM - p)) +
      (0 : ℝ) • ((p + t₂ • (yP - p)) - (p + t₁ • (yM - p))))
      - (inner ℝ v c + u) ≤ 0 := by
    simp only [zero_smul, add_zero]
    linarith [hlt₁, hh0]
  have hend : 0 ≤ inner ℝ v ((p + t₁ • (yM - p)) +
      (1 : ℝ) • ((p + t₂ • (yP - p)) - (p + t₁ • (yM - p))))
      - (inner ℝ v c + u) := by
    have hz : (p + t₁ • (yM - p)) + (1 : ℝ) • ((p + t₂ • (yP - p)) - (p + t₁ • (yM - p)))
        = p + t₂ • (yP - p) := by module
    rw [hz]
    linarith [hgt₂, hh0]
  obtain ⟨t, htmem, ht⟩ := (intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    hcont.continuousOn) ⟨hstart, hend⟩
  simp only at ht
  -- the witness still lies in the box and on the level `{g = lam}`
  have hwbox : ((p + t₁ • (yM - p)) + t • ((p + t₂ • (yP - p)) - (p + t₁ • (yM - p))))
      ∈ Submission.PBox s c σ := by
    have hw : (p + t₁ • (yM - p)) + t • ((p + t₂ • (yP - p)) - (p + t₁ • (yM - p)))
        = (1 - t) • (p + t₁ • (yM - p)) + t • (p + t₂ • (yP - p)) := by module
    rw [hw]
    exact (Work.Topology.SphereSlicing.convex_PBox s c σ) hc₁box hc₂box
      (by linarith [htmem.2]) htmem.1 (by ring)
  have hwℓ : ℓ ((p + t₁ • (yM - p)) + t • ((p + t₂ • (yP - p)) - (p + t₁ • (yM - p)))) = lam := by
    have hw : ℓ ((p + t₁ • (yM - p)) + t • ((p + t₂ • (yP - p)) - (p + t₁ • (yM - p))))
        = (1 - t) * ℓ (p + t₁ • (yM - p)) + t * ℓ (p + t₂ • (yP - p)) := by
      simp only [map_add, map_sub, map_smul, smul_eq_mul]
      ring
    rw [hw, hc₁ℓ, hc₂ℓ]
    ring
  -- `hβ` at that witness, where `f - a = 0`
  have hfin := hβ _ hwbox hwℓ
  rw [ht] at hfin
  simp at hfin
  linarith [hh0, hfin]

end Work.Drive.Final
