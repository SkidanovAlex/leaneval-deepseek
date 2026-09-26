import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_curve_defs
import Submission.Work.Smooth.JordanSeparation.lattice_edge_inter
import Submission.Work.Smooth.JordanSeparation.lwalk_decomp

/-!
# The polygon parametrisation of a simple closed lattice walk is injective on one period

`LWalk.curve W` is injective on `Ico 0 (2π)` when `W` is a simple closed lattice walk with at
least four edges.  The proof reduces to: distinct unit lattice edges meet only at common
endpoints or coincide (`lattice_edge_inter`), together with the fact that `IsSimple` forbids
every repetition of a vertex except the pair `(0, n)`, and the affine parametrisation of each
edge is injective.
-/

namespace Work.Smooth.JordanSeparation

open Set

noncomputable section

namespace LWalk

variable (W : LWalk)

/-- The point of the (unscaled) `k`-th lattice edge with parameter `t ∈ [0,1]`. -/
def edgePt (k : ℕ) (t : ℝ) : ℂ :=
  gpt (W.v k) + (t : ℂ) * (gpt (W.v (k + 1)) - gpt (W.v k))

theorem edgePt_mem_segment (k : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    W.edgePt k t ∈ segment ℝ (gpt (W.v k)) (gpt (W.v (k + 1))) := by
  rw [segment_eq_image]
  refine ⟨t, ht, ?_⟩
  simp only [edgePt, Complex.real_smul]
  push_cast
  ring

/-- `W.curve` agrees with `W.polyF` on the fundamental domain. -/
theorem curve_eq_polyF {t : ℝ} (ht : t ∈ Ico (0:ℝ) (2 * Real.pi)) :
    W.curve t = W.polyF t := by
  show AddCircle.liftIco (2 * Real.pi) 0 W.polyF (t : AddCircle (2 * Real.pi)) = W.polyF t
  exact AddCircle.liftIco_zero_coe_apply ht

/-- `W.polyF` is the affine parametrisation of the walk in the edge coordinate. -/
theorem polyF_eq_polyG {t : ℝ} (ht : t ∈ Ico (0:ℝ) (2 * Real.pi)) :
    W.polyF t = W.polyG ((W.n : ℝ) * t / (2 * Real.pi)) := by
  have hmin : max 0 (min t (2 * Real.pi)) = t := by
    rw [min_eq_left ht.2.le, max_eq_right ht.1]
  simp only [polyF, hmin]

/-- On the `k`-th edge the polygon is the affine parametrisation of the scaled lattice edge. -/
theorem polyG_eq_smul_edgePt {u : ℝ} (hu : u ∈ Ico (0:ℝ) (W.n : ℝ)) :
    W.polyG u = W.c • W.edgePt (Nat.floor u) (u - (Nat.floor u : ℝ)) := by
  have hk : Nat.floor u < W.n := by
    have h : (Nat.floor u : ℝ) < (W.n : ℝ) := lt_of_le_of_lt (Nat.floor_le hu.1) hu.2
    exact_mod_cast h
  have hle : (Nat.floor u : ℝ) ≤ u := Nat.floor_le hu.1
  have hlt : u < (Nat.floor u : ℝ) + 1 := Nat.lt_floor_add_one u
  rw [W.polyG_eq_of_mem_Icc hk ⟨hle, le_of_lt hlt⟩]
  simp only [edgePt, Complex.real_smul, LWalk.pt]
  ring_nf

/-- On the `k`-th edge the polygon is the affine parametrisation of the scaled lattice edge. -/
theorem exists_edge_of_mem_Ico {u : ℝ} (hu : u ∈ Ico (0:ℝ) (W.n : ℝ)) :
    ∃ k < W.n, ∃ w ∈ segment ℝ (gpt (W.v k)) (gpt (W.v (k+1))), W.polyG u = W.c • w := by
  refine ⟨Nat.floor u, ?_, W.edgePt (Nat.floor u) (u - (Nat.floor u : ℝ)), ?_, ?_⟩
  · have h : (Nat.floor u : ℝ) < (W.n : ℝ) := lt_of_le_of_lt (Nat.floor_le hu.1) hu.2
    exact_mod_cast h
  · refine W.edgePt_mem_segment _ ⟨sub_nonneg.mpr (Nat.floor_le hu.1), ?_⟩
    have := Nat.lt_floor_add_one u
    linarith
  · exact W.polyG_eq_smul_edgePt hu

/-- `W.pt` is injective on its vertex indices, as long as the two vertices lie within the walk. -/
theorem pt_eq_of_v_eq {i j : ℕ} (h : W.v i = W.v j) : W.pt i = W.pt j := by
  show W.c * gpt (W.v i) = W.c * gpt (W.v j)
  rw [h]

/-- A `(k, k+1)` pair is never the pair `(0, n)` for `n ≥ 2`. -/
theorem pair_ne_zero_n (hn : 2 ≤ W.n) (k : ℕ) : (k, k + 1) ≠ (0, W.n) := by
  intro h
  exact (by omega : ¬ (k = 0 ∧ k + 1 = W.n)) (Prod.mk.inj h)

/-- Two distinct consecutive vertices give distinct points. -/
theorem pt_succ_sub_ne (hW : W.IsSimple) (hn : 2 ≤ W.n) {k : ℕ} (hk : k < W.n) :
    W.pt (k + 1) - W.pt k ≠ 0 := by
  intro h0
  have h1 : W.pt (k + 1) = W.pt k := sub_eq_zero.mp h0
  have h2 : gpt (W.v (k + 1)) = gpt (W.v k) := by
    have hc : (W.c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt W.cpos)
    exact mul_left_cancel₀ hc h1
  have h3 : W.v (k + 1) = W.v k := gpt_injective h2
  exact hW k (k + 1) (Nat.lt_succ_self k) (by omega) (W.pair_ne_zero_n hn k) h3.symm

/-- A repeated vertex pair of a simple walk must be the pair `(0, n)`. -/
theorem eq_zero_n_of_v_eq {W : LWalk} (hW : W.IsSimple) {i j : ℕ} (hij : i < j) (hj : j ≤ W.n)
    (h : W.v i = W.v j) : i = 0 ∧ j = W.n := by
  by_contra hne
  exact hW i j hij hj (fun hh => hne (Prod.mk.inj hh)) h

/-- The point `W.edgePt k t` is never `gpt (v (k+1)) = gpt (v k)`. -/
theorem gpt_edge_ne (hW : W.IsSimple) (hn : 2 ≤ W.n) {k : ℕ} (hk : k < W.n) :
    gpt (W.v (k + 1)) - gpt (W.v k) ≠ 0 := by
  intro h0
  have h1 : W.v (k + 1) = W.v k := gpt_injective (sub_eq_zero.mp h0)
  exact hW k (k + 1) (Nat.lt_succ_self k) (by omega) (W.pair_ne_zero_n hn k) h1.symm

/-- The parameter of a point of the `k`-th edge equal to its left endpoint. -/
theorem edgePt_eq_left (hW : W.IsSimple) (hn : 2 ≤ W.n) {k : ℕ} (hk : k < W.n) {t : ℝ}
    (h : W.edgePt k t = gpt (W.v k)) : t = 0 := by
  have hD : gpt (W.v (k + 1)) - gpt (W.v k) ≠ 0 := W.gpt_edge_ne hW hn hk
  have h2 : (t : ℂ) * (gpt (W.v (k + 1)) - gpt (W.v k)) = 0 := by
    have h' : gpt (W.v k) + (t : ℂ) * (gpt (W.v (k + 1)) - gpt (W.v k)) = gpt (W.v k) + 0 := by
      rw [add_zero]; exact h
    exact add_left_cancel h'
  have h3 : (t : ℂ) = 0 := (mul_eq_zero.mp h2).resolve_right hD
  exact Complex.ofReal_injective (by simpa using h3)

/-- The parameter of a point of the `k`-th edge equal to its right endpoint. -/
theorem edgePt_eq_right (hW : W.IsSimple) (hn : 2 ≤ W.n) {k : ℕ} (hk : k < W.n) {t : ℝ}
    (h : W.edgePt k t = gpt (W.v (k + 1))) : t = 1 := by
  have hD : gpt (W.v (k + 1)) - gpt (W.v k) ≠ 0 := W.gpt_edge_ne hW hn hk
  have h2 : (t : ℂ) * (gpt (W.v (k + 1)) - gpt (W.v k)) = gpt (W.v (k + 1)) - gpt (W.v k) := by
    have h' : gpt (W.v k) + (t : ℂ) * (gpt (W.v (k + 1)) - gpt (W.v k))
        = gpt (W.v k) + (gpt (W.v (k + 1)) - gpt (W.v k)) := by
      rw [add_sub_cancel]; exact h
    exact add_left_cancel h'
  have h3 : ((t : ℂ) - 1) * (gpt (W.v (k + 1)) - gpt (W.v k)) = 0 := by
    rw [sub_mul, one_mul, h2, sub_self]
  have h4 : (t : ℂ) - 1 = 0 := (mul_eq_zero.mp h3).resolve_right hD
  have h5 : (t : ℂ) = 1 := sub_eq_zero.mp h4
  exact Complex.ofReal_injective (by simpa using h5)

/-- **The walk parametrisation is injective on one period of edge coordinates.** -/
theorem polyG_injOn (hW : W.IsSimple) (hn : 4 ≤ W.n) :
    Set.InjOn W.polyG (Ico (0:ℝ) (W.n : ℝ)) := by
  intro u hu u' hu' heq
  set k := Nat.floor u with hk
  set k' := Nat.floor u' with hk'
  have hk1 : (k : ℝ) ≤ u := Nat.floor_le hu.1
  have hk2 : u < (k : ℝ) + 1 := Nat.lt_floor_add_one u
  have hk1' : (k' : ℝ) ≤ u' := Nat.floor_le hu'.1
  have hk2' : u' < (k' : ℝ) + 1 := Nat.lt_floor_add_one u'
  have hkn : k < W.n := by
    have h : (k : ℝ) < (W.n : ℝ) := lt_of_le_of_lt hk1 hu.2
    exact_mod_cast h
  have hkn' : k' < W.n := by
    have h : (k' : ℝ) < (W.n : ℝ) := lt_of_le_of_lt hk1' hu'.2
    exact_mod_cast h
  have ht : u - (k : ℝ) ∈ Ico (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have ht' : u' - (k' : ℝ) ∈ Ico (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hpu : W.polyG u = W.pt k + ((u - (k:ℝ) : ℝ) : ℂ) * (W.pt (k+1) - W.pt k) :=
    W.polyG_eq_of_mem_Icc hkn ⟨hk1, le_of_lt hk2⟩
  have hpu' : W.polyG u' = W.pt k' + ((u' - (k':ℝ) : ℝ) : ℂ) * (W.pt (k'+1) - W.pt k') :=
    W.polyG_eq_of_mem_Icc hkn' ⟨hk1', le_of_lt hk2'⟩
  have hed : W.polyG u = W.c • W.edgePt k (u - (k:ℝ)) := W.polyG_eq_smul_edgePt hu
  have hed' : W.polyG u' = W.c • W.edgePt k' (u' - (k':ℝ)) := W.polyG_eq_smul_edgePt hu'
  have hc : (W.c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt W.cpos)
  have hw : W.edgePt k (u - (k:ℝ)) = W.edgePt k' (u' - (k':ℝ)) := by
    have h3 : W.c • W.edgePt k (u - (k:ℝ)) = W.c • W.edgePt k' (u' - (k':ℝ)) := by
      rw [← hed, ← hed', heq]
    exact mul_left_cancel₀ hc (by simpa [Complex.real_smul] using h3)
  by_cases hkk : k = k'
  · -- the two parameters lie on the same edge
    have hD : W.pt (k+1) - W.pt k ≠ 0 := W.pt_succ_sub_ne hW (by omega) hkn
    have hkey : ((u - (k:ℝ) : ℝ) : ℂ) * (W.pt (k+1) - W.pt k)
        = ((u' - (k:ℝ) : ℝ) : ℂ) * (W.pt (k+1) - W.pt k) := by
      rw [← hkk] at hpu'
      have h0 : W.pt k + ((u - (k:ℝ) : ℝ) : ℂ) * (W.pt (k+1) - W.pt k)
          = W.pt k + ((u' - (k:ℝ) : ℝ) : ℂ) * (W.pt (k+1) - W.pt k) := by
        rw [← hpu, ← hpu']; exact heq
      exact add_left_cancel h0
    have hcancel := mul_right_cancel₀ hD hkey
    have : u - (k:ℝ) = u' - (k:ℝ) := Complex.ofReal_injective hcancel
    linarith
  · -- distinct edges: the shared point is a common endpoint, which `IsSimple` forbids
    have hz : W.edgePt k (u - (k:ℝ)) ∈
        segment ℝ (gpt (W.v k)) (gpt (W.v (k+1))) ∩
        segment ℝ (gpt (W.v k')) (gpt (W.v (k'+1))) :=
      ⟨W.edgePt_mem_segment k (Ico_subset_Icc_self ht),
        hw ▸ W.edgePt_mem_segment k' (Ico_subset_Icc_self ht')⟩
    have key : ∀ {i j : ℕ}, i ≤ W.n → j ≤ W.n → W.v i = W.v j →
        i = j ∨ (i = 0 ∧ j = W.n) ∨ (j = 0 ∧ i = W.n) := by
      intro i j hi hj h
      rcases lt_trichotomy i j with hlt | heq' | hgt
      · rcases eq_zero_n_of_v_eq hW hlt hj h with ⟨h0, hn'⟩
        exact Or.inr (Or.inl ⟨h0, hn'⟩)
      · exact Or.inl heq'
      · rcases eq_zero_n_of_v_eq hW hgt hi h.symm with ⟨h0, hn'⟩
        exact Or.inr (Or.inr ⟨h0, hn'⟩)
    have hkn1 : k + 1 ≤ W.n := hkn
    have hkn1' : k' + 1 ≤ W.n := hkn'
    rcases lattice_edge_inter (W.step k hkn) (W.step k' hkn') hz with
      ⟨hwk | hwk, hwk' | hwk'⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
    · -- `w` is a vertex of both edges
      have hv : W.v k = W.v k' := gpt_injective (by rw [← hwk, ← hwk'])
      rcases key (le_of_lt hkn) (le_of_lt hkn') hv with h | ⟨h0, hn'⟩ | ⟨h0, hn'⟩
      · exact absurd h hkk
      · omega
      · omega
    · have hv : W.v k = W.v (k'+1) := gpt_injective (by rw [← hwk, ← hwk'])
      rcases key (le_of_lt hkn) hkn1' hv with h | ⟨h0, hn'⟩ | ⟨h0, hn'⟩
      · -- `k = k' + 1`: both parameters are the common vertex
        have hu0 : u - (k:ℝ) = 0 := W.edgePt_eq_left hW (by omega) hkn hwk
        have hu1 : u' - (k':ℝ) = 1 :=
          W.edgePt_eq_right hW (by omega) hkn' (hw ▸ hwk')
        have h1 : u = (k:ℝ) := by linarith
        have h2 : u' = (k':ℝ) + 1 := by linarith
        have h3 : (k:ℝ) = (k':ℝ) + 1 := by rw [h]; push_cast; ring
        linarith
      · -- the wrap-around: `u` is the end of its edge, `u'` is beyond its edge
        have hu1 : u' - (k':ℝ) = 1 :=
          W.edgePt_eq_right hW (by omega) hkn' (hw ▸ hwk')
        linarith [hk2']
      · omega
    · have hv : W.v (k+1) = W.v k' := gpt_injective (by rw [← hwk', ← hwk])
      rcases key hkn1 (le_of_lt hkn') hv with h | ⟨h0, hn'⟩ | ⟨h0, hn'⟩
      · have hu1 : u - (k:ℝ) = 1 := W.edgePt_eq_right hW (by omega) hkn hwk
        linarith [hk2]
      · omega
      · have hu1 : u - (k:ℝ) = 1 := W.edgePt_eq_right hW (by omega) hkn hwk
        linarith [hk2]
    · have hv : W.v (k+1) = W.v (k'+1) := gpt_injective (by rw [← hwk', ← hwk])
      rcases key hkn1 hkn1' hv with h | ⟨h0, hn'⟩ | ⟨h0, hn'⟩ <;> omega
    · -- the two edges coincide as sets
      have hv : W.v k = W.v k' := gpt_injective e1
      rcases key (le_of_lt hkn) (le_of_lt hkn') hv with h | ⟨h0, hn'⟩ | ⟨h0, hn'⟩
      · exact absurd h hkk
      · omega
      · omega
    · -- the two edges coincide as sets, with opposite orientations
      have hv : W.v k = W.v (k'+1) := gpt_injective e1
      have hv2 : W.v (k+1) = W.v k' := gpt_injective e2
      rcases key (le_of_lt hkn) hkn1' hv with h | ⟨h0, hn'⟩ | ⟨h0, hn'⟩
      · rcases key hkn1 (le_of_lt hkn') hv2 with h2 | ⟨h20, h2n⟩ | ⟨h20, h2n⟩ <;> omega
      · rcases key hkn1 (le_of_lt hkn') hv2 with h2 | ⟨h20, h2n⟩ | ⟨h20, h2n⟩ <;> omega
      · omega

/-- **The parametrisation of a simple closed lattice walk with at least four edges is injective on
one period.** -/
theorem curve_injOn (hW : W.IsSimple) (hn : 4 ≤ W.n) :
    Set.InjOn W.curve (Ico (0:ℝ) (2 * Real.pi)) := by
  intro s hs s' hs' h
  have h1 : W.polyF s = W.polyF s' := by
    rw [← W.curve_eq_polyF hs, ← W.curve_eq_polyF hs', h]
  rw [W.polyF_eq_polyG hs, W.polyF_eq_polyG hs'] at h1
  have hp : (0:ℝ) < 2 * Real.pi := by positivity
  have hn0 : (0:ℝ) < (W.n : ℝ) := by exact_mod_cast (by omega : 0 < W.n)
  have hm : (W.n : ℝ) * s / (2 * Real.pi) ∈ Ico (0:ℝ) (W.n : ℝ) := by
    refine ⟨div_nonneg (mul_nonneg hn0.le hs.1) hp.le, ?_⟩
    rw [div_lt_iff₀ hp]
    exact mul_lt_mul_of_pos_left hs.2 hn0
  have hm' : (W.n : ℝ) * s' / (2 * Real.pi) ∈ Ico (0:ℝ) (W.n : ℝ) := by
    refine ⟨div_nonneg (mul_nonneg hn0.le hs'.1) hp.le, ?_⟩
    rw [div_lt_iff₀ hp]
    exact mul_lt_mul_of_pos_left hs'.2 hn0
  have hval := W.polyG_injOn hW hn hm hm' h1
  have hπ : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt hp
  have h2 : (W.n : ℝ) * s = (W.n : ℝ) * s' := by
    have h4 := congrArg (fun x : ℝ => x * (2 * Real.pi)) hval
    rw [div_mul_cancel₀ _ hπ, div_mul_cancel₀ _ hπ] at h4
    exact h4
  exact mul_left_cancel₀ (ne_of_gt hn0) h2

end LWalk

end

end Work.Smooth.JordanSeparation
