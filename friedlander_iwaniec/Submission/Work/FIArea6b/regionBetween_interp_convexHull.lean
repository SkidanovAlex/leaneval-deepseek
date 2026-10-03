import Mathlib

namespace Work.FIArea6b

/-- The region between the two linear interpolations of `(la, lb)` and `(ua, ub)` over
`[a, b]` is contained in the convex hull of the four corner points. -/
theorem regionBetween_interp_convexHull (a b la lb ua ub : ℝ) (hab : a < b) :
    regionBetween (fun x : ℝ => ((b - x) * la + (x - a) * lb) / (b - a))
        (fun x : ℝ => ((b - x) * ua + (x - a) * ub) / (b - a)) (Set.Icc a b)
      ⊆ convexHull ℝ ({(a, la), (a, ua), (b, lb), (b, ub)} : Set (ℝ × ℝ)) := by
  rintro ⟨x, y⟩ hp
  rw [regionBetween] at hp
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_Ioo] at hp
  obtain ⟨⟨hxa, hxb⟩, hyf, hyg⟩ := hp
  have hden : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  set F : ℝ := ((b - x) * la + (x - a) * lb) / (b - a) with hF
  set G : ℝ := ((b - x) * ua + (x - a) * ub) / (b - a) with hG
  have hFG : 0 < G - F := by linarith
  set t : ℝ := (x - a) / (b - a) with ht
  set s : ℝ := (y - F) / (G - F) with hs
  have hs0 : 0 ≤ s := by
    rw [hs]; exact div_nonneg (by linarith) (le_of_lt hFG)
  have hs1 : s ≤ 1 := by
    rw [hs, div_le_iff₀ hFG]; linarith
  have hsy : y = (1 - s) * F + s * G := by
    have h1 : s * (G - F) = y - F := by rw [hs]; field_simp
    linarith
  have ht0 : 0 ≤ t := by
    rw [ht]; exact div_nonneg (by linarith) (le_of_lt (sub_pos.mpr hab))
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_iff₀ (sub_pos.mpr hab)]; linarith
  have hxlin : x = (1 - t) * a + t * b := by
    rw [ht]; field_simp; ring
  have hFlin : F = (1 - t) * la + t * lb := by
    rw [hF, ht]; field_simp; ring
  have hGlin : G = (1 - t) * ua + t * ub := by
    rw [hG, ht]; field_simp; ring
  set S : Set (ℝ × ℝ) := {(a, la), (a, ua), (b, lb), (b, ub)} with hSdef
  have hS : Convex ℝ (convexHull ℝ S) := convex_convexHull ℝ S
  have hsub := subset_convexHull ℝ S
  have hala : ((a, la) : ℝ × ℝ) ∈ convexHull ℝ S := hsub (by rw [hSdef]; simp)
  have haua : ((a, ua) : ℝ × ℝ) ∈ convexHull ℝ S := hsub (by rw [hSdef]; simp)
  have hblb : ((b, lb) : ℝ × ℝ) ∈ convexHull ℝ S := hsub (by rw [hSdef]; simp)
  have hbub : ((b, ub) : ℝ × ℝ) ∈ convexHull ℝ S := hsub (by rw [hSdef]; simp)
  have hsI : s ∈ Set.Icc (0:ℝ) 1 := Set.mem_Icc.mpr ⟨hs0, hs1⟩
  have htI : t ∈ Set.Icc (0:ℝ) 1 := Set.mem_Icc.mpr ⟨ht0, ht1⟩
  have hP : ((a, (1 - s) * la + s * ua) : ℝ × ℝ) ∈ convexHull ℝ S := by
    have h := hS.lineMap_mem (x := ((a, la) : ℝ × ℝ)) (y := ((a, ua) : ℝ × ℝ)) hala haua hsI
    have hlp : (AffineMap.lineMap ((a, la) : ℝ × ℝ) ((a, ua) : ℝ × ℝ)) s
        = ((a, (1 - s) * la + s * ua) : ℝ × ℝ) := by
      ext
      · simp only [AffineMap.fst_lineMap, AffineMap.lineMap_apply_ring]; ring
      · simp only [AffineMap.snd_lineMap, AffineMap.lineMap_apply_ring]
    rwa [hlp] at h
  have hQ : ((b, (1 - s) * lb + s * ub) : ℝ × ℝ) ∈ convexHull ℝ S := by
    have h := hS.lineMap_mem (x := ((b, lb) : ℝ × ℝ)) (y := ((b, ub) : ℝ × ℝ)) hblb hbub hsI
    have hlp : (AffineMap.lineMap ((b, lb) : ℝ × ℝ) ((b, ub) : ℝ × ℝ)) s
        = ((b, (1 - s) * lb + s * ub) : ℝ × ℝ) := by
      ext
      · simp only [AffineMap.fst_lineMap, AffineMap.lineMap_apply_ring]; ring
      · simp only [AffineMap.snd_lineMap, AffineMap.lineMap_apply_ring]
    rwa [hlp] at h
  have hmem : (1 - t) • ((a, (1 - s) * la + s * ua) : ℝ × ℝ)
      + t • ((b, (1 - s) * lb + s * ub) : ℝ × ℝ) ∈ convexHull ℝ S := by
    have h := hS.lineMap_mem hP hQ htI
    rwa [AffineMap.lineMap_apply_module] at h
  have heq : (x, y) = (1 - t) • ((a, (1 - s) * la + s * ua) : ℝ × ℝ)
      + t • ((b, (1 - s) * lb + s * ub) : ℝ × ℝ) := by
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; exact hxlin
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      have hfac : (1 - t) * ((1 - s) * la + s * ua) + t * ((1 - s) * lb + s * ub)
          = (1 - s) * ((1 - t) * la + t * lb) + s * ((1 - t) * ua + t * ub) := by ring
      rw [hfac, ← hFlin, ← hGlin, ← hsy]
  rw [heq]; exact hmem

end Work.FIArea6b
