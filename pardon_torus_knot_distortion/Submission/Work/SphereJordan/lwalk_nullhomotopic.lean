import Mathlib
import Submission.Work.Smooth.JordanSeparation.flip_loop_homotopic
import Submission.Work.Smooth.JordanSeparation.lwalk_flipmeasure
import Submission.Work.Smooth.JordanSeparation.lwalk_decomp
import Submission.Work.Smooth.JordanSeparation.lwalk_region
import Submission.Work.Smooth.JordanSeparation.lwalk_side
import Submission.Work.Smooth.JordanSeparation.lwalk_corner
import Submission.Work.Smooth.JordanSeparation.lwalk_lexmin
import Submission.Work.Smooth.JordanSeparation.lwalk_measure
import Submission.Work.Smooth.JordanSeparation.loopNat_homotopy_unpack
import Submission.Work.Smooth.JordanSeparation.lwalk_seamflip
import Submission.Work.Smooth.JordanSeparation.lwalk_peel_base
import Submission.Work.Smooth.JordanSeparation.gridWalk_approx
import Submission.Work.Smooth.JordanSeparation.seamFlip_free_homotopic

namespace Work.SphereJordan

open Set

open Work.Smooth.JordanSeparation

noncomputable section

/-- The segment between two points of a convex set stays in the set. -/
theorem segment_mem_of_convex {B : Set ℂ} (hB : Convex ℝ B) {a b : ℂ} (ha : a ∈ B) (hb : b ∈ B)
    (s : unitInterval) : Path.segment a b s ∈ B :=
  hB.segment_subset ha hb (by rw [← Path.range_segment]; exact ⟨s, rfl⟩)

/-- **The flipped walk stays in `U`.** -/
theorem flip_path_mem_U {U : Set ℂ} {W : LWalk} {hval : ∀ t, W.path t ∈ U} {k : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ W.n)
    (ha : W.v (k - 1) = W.v k - (1, 0) ∨ W.v (k - 1) = W.v k - (0, 1))
    (hb : W.v (k + 1) = W.v k - (1, 0) ∨ W.v (k + 1) = W.v k - (0, 1))
    (hcU : cellCl W.c (W.v k - (1, 1)) ⊆ U) :
    ∀ t, (W.flip hk1 hk2 ha hb).path t ∈ U := by
  have hB : Convex ℝ (cellCl W.c (W.v k - (1, 1))) := convex_cellCl W.c W.cpos _
  have hcorner : W.c * gpt (W.v k - (1, 1)) ∈ cellCl W.c (W.v k - (1, 1)) :=
    smul_gpt_mem_cellCl W.c W.cpos _
  have hleft : W.pt (k - 1) ∈ cellCl W.c (W.v k - (1, 1)) := by
    show W.c * gpt (W.v (k - 1)) ∈ cellCl W.c (W.v k - (1, 1))
    rcases ha with ha | ha
    · rw [ha]
      have h := smul_gpt_add_zero_one_mem_cellCl W.c W.cpos (W.v k - (1, 1))
      rwa [show (W.v k - (1, 1)) + (0, 1) = W.v k - (1, 0) from by ext <;> simp] at h
    · rw [ha]
      have h := smul_gpt_add_one_zero_mem_cellCl W.c W.cpos (W.v k - (1, 1))
      rwa [show (W.v k - (1, 1)) + (1, 0) = W.v k - (0, 1) from by ext <;> simp] at h
  have hright : W.pt (k + 1) ∈ cellCl W.c (W.v k - (1, 1)) := by
    show W.c * gpt (W.v (k + 1)) ∈ cellCl W.c (W.v k - (1, 1))
    rcases hb with hb | hb
    · rw [hb]
      have h := smul_gpt_add_zero_one_mem_cellCl W.c W.cpos (W.v k - (1, 1))
      rwa [show (W.v k - (1, 1)) + (0, 1) = W.v k - (1, 0) from by ext <;> simp] at h
    · rw [hb]
      have h := smul_gpt_add_one_zero_mem_cellCl W.c W.cpos (W.v k - (1, 1))
      rwa [show (W.v k - (1, 1)) + (1, 0) = W.v k - (0, 1) from by ext <;> simp] at h
  intro t
  have hmem : (W.flip hk1 hk2 ha hb).path t ∈ Set.range (W.flip hk1 hk2 ha hb).path :=
    ⟨t, rfl⟩
  rw [LWalk.range_path] at hmem
  rcases hmem with hmem | hmem
  · rw [Set.mem_iUnion] at hmem
    obtain ⟨m, hmem⟩ := hmem
    rw [Set.mem_iUnion] at hmem
    obtain ⟨hmn, hmem⟩ := hmem
    rw [Set.mem_range] at hmem
    obtain ⟨s, hs⟩ := hmem
    rw [← hs]
    by_cases hm1 : m = k - 1
    · rw [hm1]
      have hpm : (W.flip hk1 hk2 ha hb).pt (k - 1) = W.pt (k - 1) :=
        flip_pt_of_ne hk1 hk2 ha hb (by omega)
      have hpm1 : (W.flip hk1 hk2 ha hb).pt (k - 1 + 1) = W.c * gpt (W.v k - (1, 1)) := by
        rw [show k - 1 + 1 = k from by omega]
        exact flip_pt_self hk1 hk2 ha hb
      show Path.segment ((W.flip hk1 hk2 ha hb).pt (k - 1))
        ((W.flip hk1 hk2 ha hb).pt (k - 1 + 1)) s ∈ U
      rw [hpm, hpm1]
      exact hcU (segment_mem_of_convex hB hleft hcorner s)
    · by_cases hm0 : m = k
      · rw [hm0]
        have hpm : (W.flip hk1 hk2 ha hb).pt k = W.c * gpt (W.v k - (1, 1)) :=
          flip_pt_self hk1 hk2 ha hb
        have hpm1 : (W.flip hk1 hk2 ha hb).pt (k + 1) = W.pt (k + 1) :=
          flip_pt_of_ne hk1 hk2 ha hb (by omega)
        show Path.segment ((W.flip hk1 hk2 ha hb).pt k)
          ((W.flip hk1 hk2 ha hb).pt (k + 1)) s ∈ U
        rw [hpm, hpm1]
        exact hcU (segment_mem_of_convex hB hcorner hright s)
      · have hpm : (W.flip hk1 hk2 ha hb).pt m = W.pt m :=
          flip_pt_of_ne hk1 hk2 ha hb hm0
        have hpm1 : (W.flip hk1 hk2 ha hb).pt (m + 1) = W.pt (m + 1) :=
          flip_pt_of_ne hk1 hk2 ha hb (by omega)
        have hmW : m < W.n := by rw [LWalk.flip_n W hk1 hk2 ha hb] at hmn; exact hmn
        have heq : (W.flip hk1 hk2 ha hb).edge m s = W.edge m s := by
          show Path.segment ((W.flip hk1 hk2 ha hb).pt m)
            ((W.flip hk1 hk2 ha hb).pt (m + 1)) s = Path.segment (W.pt m) (W.pt (m + 1)) s
          rw [hpm, hpm1]
        rw [heq]
        exact W.edge_mem hval hmW s
  · rw [Set.mem_singleton_iff] at hmem
    rw [hmem, flip_pt_of_ne hk1 hk2 ha hb (show (0 : ℕ) ≠ k by omega)]
    exact W.pt_mem hval (Nat.zero_le _)


/-- **The seam-flipped walk stays in `U`.** -/
theorem seamFlip_path_mem_U {U : Set ℂ} {W : LWalk} {hval : ∀ t, W.path t ∈ U}
    (h2 : 2 ≤ W.n)
    (ha : W.v (W.n - 1) = W.v 0 - (1, 0) ∨ W.v (W.n - 1) = W.v 0 - (0, 1))
    (hb : W.v 1 = W.v 0 - (1, 0) ∨ W.v 1 = W.v 0 - (0, 1))
    (hcU : cellCl W.c (W.v 0 - (1, 1)) ⊆ U) :
    ∀ t, (W.seamFlip h2 ha hb).path t ∈ U := by
  have hB : Convex ℝ (cellCl W.c (W.v 0 - (1, 1))) := convex_cellCl W.c W.cpos _
  have hcorner : W.c * gpt (W.v 0 - (1, 1)) ∈ cellCl W.c (W.v 0 - (1, 1)) :=
    smul_gpt_mem_cellCl W.c W.cpos _
  have h10 : W.v 0 - (1, 0) = (W.v 0 - (1, 1)) + (0, 1) := by ext <;> simp
  have h01 : W.v 0 - (0, 1) = (W.v 0 - (1, 1)) + (1, 0) := by ext <;> simp
  have h00 : (W.v 0 - (1, 1)) + (1, 1) = W.v 0 := by ext <;> simp
  have hp0 : W.pt 0 ∈ cellCl W.c (W.v 0 - (1, 1)) := by
    show W.c * gpt (W.v 0) ∈ cellCl W.c (W.v 0 - (1, 1))
    have h := smul_gpt_add_one_one_mem_cellCl W.c W.cpos (W.v 0 - (1, 1))
    rwa [h00] at h
  have hp1 : W.pt 1 ∈ cellCl W.c (W.v 0 - (1, 1)) := by
    show W.c * gpt (W.v 1) ∈ cellCl W.c (W.v 0 - (1, 1))
    rcases hb with hb | hb
    · have h := smul_gpt_add_zero_one_mem_cellCl W.c W.cpos (W.v 0 - (1, 1))
      rw [show (W.v 0 - (1, 1)) + (0, 1) = W.v 1 from h10.symm.trans hb.symm] at h
      exact h
    · have h := smul_gpt_add_one_zero_mem_cellCl W.c W.cpos (W.v 0 - (1, 1))
      rw [show (W.v 0 - (1, 1)) + (1, 0) = W.v 1 from h01.symm.trans hb.symm] at h
      exact h
  have hpn1 : W.pt (W.n - 1) ∈ cellCl W.c (W.v 0 - (1, 1)) := by
    show W.c * gpt (W.v (W.n - 1)) ∈ cellCl W.c (W.v 0 - (1, 1))
    rcases ha with ha | ha
    · have h := smul_gpt_add_zero_one_mem_cellCl W.c W.cpos (W.v 0 - (1, 1))
      rw [show (W.v 0 - (1, 1)) + (0, 1) = W.v (W.n - 1) from h10.symm.trans ha.symm] at h
      exact h
    · have h := smul_gpt_add_one_zero_mem_cellCl W.c W.cpos (W.v 0 - (1, 1))
      rw [show (W.v 0 - (1, 1)) + (1, 0) = W.v (W.n - 1) from h01.symm.trans ha.symm] at h
      exact h
  have hpt0 : (W.seamFlip h2 ha hb).pt 0 = W.c * gpt (W.v 0 - (1, 1)) := by
    show (W.seamFlip h2 ha hb).c * gpt ((W.seamFlip h2 ha hb).v 0) = _
    rw [LWalk.seamFlip_c, LWalk.seamFlip_v_zero W h2 ha hb]
  have hptn : (W.seamFlip h2 ha hb).pt W.n = W.c * gpt (W.v 0 - (1, 1)) := by
    show (W.seamFlip h2 ha hb).c * gpt ((W.seamFlip h2 ha hb).v W.n) = _
    rw [LWalk.seamFlip_c, LWalk.seamFlip_v_last W h2 ha hb]
  have hpt1 : (W.seamFlip h2 ha hb).pt 1 = W.pt 1 := by
    show (W.seamFlip h2 ha hb).c * gpt ((W.seamFlip h2 ha hb).v 1) = W.c * gpt (W.v 1)
    rw [LWalk.seamFlip_c, LWalk.seamFlip_v_of_ne W h2 ha hb (by omega) (by omega)]
  have hptn1 : (W.seamFlip h2 ha hb).pt (W.n - 1) = W.pt (W.n - 1) := by
    show (W.seamFlip h2 ha hb).c * gpt ((W.seamFlip h2 ha hb).v (W.n - 1))
      = W.c * gpt (W.v (W.n - 1))
    rw [LWalk.seamFlip_c, LWalk.seamFlip_v_of_ne W h2 ha hb (by omega) (by omega)]
  have hptmid : ∀ j, 1 ≤ j → j ≤ W.n - 1 → (W.seamFlip h2 ha hb).pt j = W.pt j :=
    fun j hj1 hj2 => by
      show (W.seamFlip h2 ha hb).c * gpt ((W.seamFlip h2 ha hb).v j) = W.c * gpt (W.v j)
      rw [LWalk.seamFlip_c, LWalk.seamFlip_v_of_ne W h2 ha hb (by omega) (by omega)]
  intro t
  have hmem : (W.seamFlip h2 ha hb).path t ∈ Set.range (W.seamFlip h2 ha hb).path := ⟨t, rfl⟩
  rw [LWalk.range_path] at hmem
  rcases hmem with hmem | hmem
  · rw [Set.mem_iUnion] at hmem
    obtain ⟨m, hmem⟩ := hmem
    rw [Set.mem_iUnion] at hmem
    obtain ⟨hmn, hmem⟩ := hmem
    rw [Set.mem_range] at hmem
    obtain ⟨s, hs⟩ := hmem
    rw [← hs]
    by_cases hm0 : m = 0
    · rw [hm0]
      show Path.segment ((W.seamFlip h2 ha hb).pt 0) ((W.seamFlip h2 ha hb).pt 1) s ∈ U
      rw [hpt0, hpt1]
      exact hcU (segment_mem_of_convex hB hcorner hp1 s)
    · by_cases hmn1 : m = W.n - 1
      · rw [hmn1]
        have hidx : W.n - 1 + 1 = W.n := by omega
        have hptn' : (W.seamFlip h2 ha hb).pt (W.n - 1 + 1) = W.c * gpt (W.v 0 - (1, 1)) := by
          rw [hidx]; exact hptn
        show Path.segment ((W.seamFlip h2 ha hb).pt (W.n - 1))
          ((W.seamFlip h2 ha hb).pt (W.n - 1 + 1)) s ∈ U
        rw [hptn1, hptn']
        exact hcU (segment_mem_of_convex hB hpn1 hcorner s)
      · have hmWn : m < W.n := by rw [LWalk.seamFlip_n W h2 ha hb] at hmn; exact hmn
        have hpm : (W.seamFlip h2 ha hb).pt m = W.pt m := hptmid m (by omega) (by omega)
        have hpm1 : (W.seamFlip h2 ha hb).pt (m + 1) = W.pt (m + 1) :=
          hptmid (m + 1) (by omega) (by omega)
        have heq : (W.seamFlip h2 ha hb).edge m s = W.edge m s := by
          show Path.segment ((W.seamFlip h2 ha hb).pt m) ((W.seamFlip h2 ha hb).pt (m + 1)) s
            = Path.segment (W.pt m) (W.pt (m + 1)) s
          rw [hpm, hpm1]
        rw [heq]
        exact W.edge_mem hval hmWn s
  · rw [Set.mem_singleton_iff] at hmem
    rw [hmem, hpt0]
    exact hcU hcorner

/-- **The middle piece of the cut.**  If the loop of the sub-walk `W.sub i j` is null-homotopic,
then so is the cast of the middle `joinNat` of `W`'s clamped edges. -/
theorem sub_mid_homotopic {U : Set ℂ} {W : LWalk} {hval : ∀ t, W.path t ∈ U}
    {i j : ℕ} (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j)
    (hval' : ∀ t, (W.sub i j hij hj hcl).path t ∈ U)
    (hpt : W.ptMin hval i = W.ptMin hval (i + (j - i)))
    (h : Path.Homotopic ((W.sub i j hij hj hcl).loopNat hval')
        (Path.refl ((W.sub i j hij hj hcl).ptMin hval' 0))) :
    Path.Homotopic
      (Path.cast (joinNat (p := fun l => W.ptMin hval (i + l))
        (fun l => W.edgeUNat hval (i + l)) (j - i)) rfl hpt)
      (Path.refl (W.ptMin hval i)) := by
  have hH : ∀ l, l ≤ j - i → (W.sub i j hij hj hcl).ptMin hval' l = W.ptMin hval (i + l) := by
    intro l hl
    refine Subtype.ext ?_
    rw [LWalk.ptMin_apply, LWalk.ptMin_apply, Nat.min_eq_left hl,
      Nat.min_eq_left (by omega : i + l ≤ W.n)]
  have hE : ∀ l (hl : l < j - i),
      (W.sub i j hij hj hcl).edgeUNat hval' l
        = Path.cast (W.edgeUNat hval (i + l)) (hH l (le_of_lt hl))
            (hH (l + 1) (by omega)) := by
    intro l hl
    apply Path.ext
    funext s
    apply Subtype.ext
    rw [Path.cast_coe, LWalk.edgeUNat_apply, LWalk.edgeUNat_apply,
      dif_pos hl, dif_pos (by omega : i + l < W.n)]
    rfl
  have hjoin : joinNat (p := fun l => (W.sub i j hij hj hcl).ptMin hval' l)
      (fun l => (W.sub i j hij hj hcl).edgeUNat hval' l) (j - i)
      = Path.cast (joinNat (p := fun l => W.ptMin hval (i + l))
          (fun l => W.edgeUNat hval (i + l)) (j - i))
          (hH 0 (Nat.zero_le _)) (hH (j - i) le_rfl) :=
    joinNat_cast_bound hH _ _ hE (j - i) le_rfl
  have hval_ptwise : ∀ t, (W.sub i j hij hj hcl).loopNat hval' t
      = (joinNat (p := fun l => W.ptMin hval (i + l))
          (fun l => W.edgeUNat hval (i + l)) (j - i)) t := by
    intro t
    rw [LWalk.loopNat_eq_joinNat]
    refine (path_cast_apply _ _ _ t).trans ?_
    rw [hjoin]
    exact path_cast_apply _ _ _ t
  have heq : Path.cast ((W.sub i j hij hj hcl).loopNat hval')
        (hH 0 (Nat.zero_le _)).symm (hH 0 (Nat.zero_le _)).symm
      = Path.cast (joinNat (p := fun l => W.ptMin hval (i + l))
          (fun l => W.edgeUNat hval (i + l)) (j - i)) rfl hpt := by
    apply Path.ext
    funext t
    refine (path_cast_apply _ _ _ t).trans ?_
    refine (hval_ptwise t).trans ?_
    exact (path_cast_apply _ _ _ t).symm
  have hstep := Path.Homotopic.pathCast h (hH 0 (Nat.zero_le _)).symm
    (hH 0 (Nat.zero_le _)).symm
  have hrefl : Path.cast (Path.refl ((W.sub i j hij hj hcl).ptMin hval' 0))
      (hH 0 (Nat.zero_le _)).symm (hH 0 (Nat.zero_le _)).symm
      = Path.refl (W.ptMin hval i) := by
    apply Path.ext
    funext t
    exact (path_cast_apply (Path.refl ((W.sub i j hij hj hcl).ptMin hval' 0))
      (hH 0 (Nat.zero_le _)).symm (hH 0 (Nat.zero_le _)).symm t).trans
      (hH 0 (Nat.zero_le _))
  rw [hrefl] at hstep
  exact heq ▸ hstep

/-- **The complementary piece of the cut.**  If the loop of the deleted walk `W.del i j` is
null-homotopic, then so is the composite of the head `joinNat` (the edges of `W` before the cut)
with the cast of the tail `joinNat`. -/
theorem del_compl_homotopic {U : Set ℂ} {W : LWalk} {hval : ∀ t, W.path t ∈ U}
    {i j : ℕ} (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j)
    (hval' : ∀ t, (W.del i j hij hj hcl).path t ∈ U)
    (hpt : W.ptMin hval i = W.ptMin hval (i + (j - i)))
    (hclosed : W.ptMin hval (i + ((j - i) + (W.n - j))) = W.ptMin hval 0)
    (h : Path.Homotopic ((W.del i j hij hj hcl).loopNat hval')
        (Path.refl ((W.del i j hij hj hcl).ptMin hval' 0))) :
    Path.Homotopic
      ((joinNat (p := W.ptMin hval) (fun k => W.edgeUNat hval k) i).trans
        (Path.cast (joinNat (p := fun l => W.ptMin hval (i + ((j - i) + l)))
          (fun l => W.edgeUNat hval (i + ((j - i) + l))) (W.n - j)) hpt hclosed.symm))
      (Path.refl (W.ptMin hval 0)) := by
  have hDn : (W.del i j hij hj hcl).n = i + (W.n - j) := rfl
  have Dh : ∀ l, l ≤ i → (W.del i j hij hj hcl).ptMin hval' l = W.ptMin hval l := by
    intro l hl
    refine Subtype.ext ?_
    rw [LWalk.ptMin_apply, LWalk.ptMin_apply,
      Nat.min_eq_left (by rw [hDn]; omega), Nat.min_eq_left (by omega : l ≤ W.n),
      LWalk.del_pt_of_le W i j hij hj hcl hl]
  have Dt : ∀ l, l ≤ W.n - j →
      (W.del i j hij hj hcl).ptMin hval' (i + l) = W.ptMin hval (j + l) := by
    intro l hl
    refine Subtype.ext ?_
    rw [LWalk.ptMin_apply, LWalk.ptMin_apply,
      Nat.min_eq_left (by rw [hDn]; omega), Nat.min_eq_left (by omega : j + l ≤ W.n),
      LWalk.del_pt_tail W i j hij hj hcl l]
  have DheadE : ∀ l (hl : l < i),
      (W.del i j hij hj hcl).edgeUNat hval' l
        = Path.cast (W.edgeUNat hval l) (Dh l (le_of_lt hl)) (Dh (l + 1) (by omega)) := by
    intro l hl
    apply Path.ext
    funext s
    apply Subtype.ext
    rw [Path.cast_coe, LWalk.edgeUNat_apply, LWalk.edgeUNat_apply,
      dif_pos (show l < (W.del i j hij hj hcl).n from by rw [hDn]; omega),
      dif_pos (by omega : l < W.n)]
    show Path.segment ((W.del i j hij hj hcl).pt l) ((W.del i j hij hj hcl).pt (l + 1)) s
      = Path.segment (W.pt l) (W.pt (l + 1)) s
    rw [LWalk.del_pt_of_le W i j hij hj hcl (by omega),
      LWalk.del_pt_of_le W i j hij hj hcl (by omega)]
  have DtailE : ∀ l (hl : l < W.n - j),
      (W.del i j hij hj hcl).edgeUNat hval' (i + l)
        = Path.cast (W.edgeUNat hval (j + l)) (Dt l (le_of_lt hl)) (Dt (l + 1) (by omega)) := by
    intro l hl
    apply Path.ext
    funext s
    apply Subtype.ext
    rw [Path.cast_coe, LWalk.edgeUNat_apply, LWalk.edgeUNat_apply,
      dif_pos (show i + l < (W.del i j hij hj hcl).n from by rw [hDn]; omega),
      dif_pos (by omega : j + l < W.n)]
    show Path.segment ((W.del i j hij hj hcl).pt (i + l))
      ((W.del i j hij hj hcl).pt (i + l + 1)) s
      = Path.segment (W.pt (j + l)) (W.pt (j + l + 1)) s
    rw [LWalk.del_pt_tail W i j hij hj hcl l,
      show (W.del i j hij hj hcl).pt (i + l + 1) = W.pt (j + l + 1) from
        LWalk.del_pt_tail W i j hij hj hcl (l + 1)]
  have pr : ∀ l, W.ptMin hval (j + l) = W.ptMin hval (i + ((j - i) + l)) := by
    intro l
    refine Subtype.ext ?_
    rw [LWalk.ptMin_apply, LWalk.ptMin_apply,
      show j + l = i + ((j - i) + l) from by omega]
  have prE : ∀ l, W.edgeUNat hval (j + l)
      = Path.cast (W.edgeUNat hval (i + ((j - i) + l))) (pr l) (pr (l + 1)) := by
    intro l
    apply Path.ext
    funext s
    apply Subtype.ext
    rw [Path.cast_coe, LWalk.edgeUNat_apply, LWalk.edgeUNat_apply]
    by_cases hl : j + l < W.n
    · rw [dif_pos hl, dif_pos (by omega : i + ((j - i) + l) < W.n)]
      show Path.segment (W.pt (j + l)) (W.pt (j + l + 1)) s
        = Path.segment (W.pt (i + ((j - i) + l))) (W.pt (i + ((j - i) + l) + 1)) s
      rw [show j + l = i + ((j - i) + l) from by omega]
    · rw [dif_neg hl, dif_neg (by omega : ¬ i + ((j - i) + l) < W.n)]

  have e2 := (W.del i j hij hj hcl).ptMin_zero_eq_last hval'
  have Dh0 : (W.del i j hij hj hcl).ptMin hval' 0 = W.ptMin hval 0 := Dh 0 (Nat.zero_le i)
  have Dhi : (W.del i j hij hj hcl).ptMin hval' i = W.ptMin hval i := Dh i le_rfl
  have Dt0 : (W.del i j hij hj hcl).ptMin hval' (i + 0) = W.ptMin hval (j + 0) :=
    Dt 0 (Nat.zero_le (W.n - j))
  have DtK : (W.del i j hij hj hcl).ptMin hval' (i + (W.n - j)) = W.ptMin hval (j + (W.n - j)) :=
    Dt (W.n - j) le_rfl
  have pr0 : W.ptMin hval (j + 0) = W.ptMin hval (i + ((j - i) + 0)) := pr 0
  have prK : W.ptMin hval (j + (W.n - j)) = W.ptMin hval (i + ((j - i) + (W.n - j))) :=
    pr (W.n - j)
  have hhead : joinNat (p := fun l => (W.del i j hij hj hcl).ptMin hval' l)
        (fun l => (W.del i j hij hj hcl).edgeUNat hval' l) i
      = Path.cast (joinNat (p := fun k => W.ptMin hval k) (fun k => W.edgeUNat hval k) i)
          Dh0 Dhi :=
    joinNat_cast_bound Dh _ _ DheadE i le_rfl
  have htail : joinNat (p := fun l => (W.del i j hij hj hcl).ptMin hval' (i + l))
        (fun l => (W.del i j hij hj hcl).edgeUNat hval' (i + l)) (W.n - j)
      = Path.cast (joinNat (p := fun l => W.ptMin hval (j + l))
          (fun l => W.edgeUNat hval (j + l)) (W.n - j)) Dt0 DtK :=
    joinNat_cast_bound Dt _ _ DtailE (W.n - j) le_rfl
  have hreindex : joinNat (p := fun l => W.ptMin hval (j + l))
        (fun l => W.edgeUNat hval (j + l)) (W.n - j)
      = Path.cast (joinNat (p := fun l => W.ptMin hval (i + ((j - i) + l)))
          (fun l => W.edgeUNat hval (i + ((j - i) + l))) (W.n - j)) pr0 prK :=
    joinNat_cast pr _ _ prE (W.n - j)
  have hjoint : Path.Homotopic
      (joinNat (p := fun l => (W.del i j hij hj hcl).ptMin hval' l)
        (fun l => (W.del i j hij hj hcl).edgeUNat hval' l) (W.del i j hij hj hcl).n)
      ((joinNat (p := fun l => (W.del i j hij hj hcl).ptMin hval' l)
        (fun l => (W.del i j hij hj hcl).edgeUNat hval' l) i).trans
        (joinNat (p := fun l => (W.del i j hij hj hcl).ptMin hval' (i + l))
          (fun l => (W.del i j hij hj hcl).edgeUNat hval' (i + l)) (W.n - j))) :=
    joinNat_add (p := fun l => (W.del i j hij hj hcl).ptMin hval' l)
      (fun l => (W.del i j hij hj hcl).edgeUNat hval' l) i (W.n - j)
  -- the hypothesis, with the loop written as a cast of the raw joinNat
  have hcast : (W.del i j hij hj hcl).loopNat hval'
      = Path.cast (joinNat (p := fun l => (W.del i j hij hj hcl).ptMin hval' l)
          (fun l => (W.del i j hij hj hcl).edgeUNat hval' l) (W.del i j hij hj hcl).n) rfl e2 :=
    (LWalk.loopNat_eq_joinNat hval').trans
      (path_cast_proof_irrel
        (joinNat (p := fun l => (W.del i j hij hj hcl).ptMin hval' l)
          (fun l => (W.del i j hij hj hcl).edgeUNat hval' l) (W.del i j hij hj hcl).n)
        ((W.del i j hij hj hcl).ptMin_eq_ptU hval' 0 (Nat.zero_le _)).symm rfl e2 e2)
  have h0 : Path.Homotopic
      (Path.cast (joinNat (p := fun l => (W.del i j hij hj hcl).ptMin hval' l)
          (fun l => (W.del i j hij hj hcl).edgeUNat hval' l) (W.del i j hij hj hcl).n) rfl e2)
      (Path.refl (W.ptMin hval 0)) := hcast.symm ▸ h
  -- step 1: split the D-joinNat at the cut
  have hstep1 : Path.Homotopic
      (Path.cast (joinNat (p := fun l => (W.del i j hij hj hcl).ptMin hval' l)
          (fun l => (W.del i j hij hj hcl).edgeUNat hval' l) (W.del i j hij hj hcl).n) rfl e2)
      (Path.cast ((joinNat (p := fun l => (W.del i j hij hj hcl).ptMin hval' l)
          (fun l => (W.del i j hij hj hcl).edgeUNat hval' l) i).trans
          (joinNat (p := fun l => (W.del i j hij hj hcl).ptMin hval' (i + l))
            (fun l => (W.del i j hij hj hcl).edgeUNat hval' (i + l)) (W.n - j))) rfl e2) :=
    Path.Homotopic.pathCast hjoint rfl e2
  -- step 2: distribute the cast over the trans
  have hstep2 : Path.cast ((joinNat (p := fun l => (W.del i j hij hj hcl).ptMin hval' l)
          (fun l => (W.del i j hij hj hcl).edgeUNat hval' l) i).trans
          (joinNat (p := fun l => (W.del i j hij hj hcl).ptMin hval' (i + l))
            (fun l => (W.del i j hij hj hcl).edgeUNat hval' (i + l)) (W.n - j))) rfl e2
      = (Path.cast (joinNat (p := fun l => (W.del i j hij hj hcl).ptMin hval' l)
            (fun l => (W.del i j hij hj hcl).edgeUNat hval' l) i) rfl rfl).trans
        (Path.cast (joinNat (p := fun l => (W.del i j hij hj hcl).ptMin hval' (i + l))
            (fun l => (W.del i j hij hj hcl).edgeUNat hval' (i + l)) (W.n - j)) rfl e2) :=
    cast_trans_general _ _ rfl rfl e2
  -- the head factor, after replacing the D-head by the cast of the head of `W`
  have hA : Path.cast (joinNat (p := fun l => (W.del i j hij hj hcl).ptMin hval' l)
        (fun l => (W.del i j hij hj hcl).edgeUNat hval' l) i) rfl rfl
      = Path.cast (joinNat (p := fun k => W.ptMin hval k) (fun k => W.edgeUNat hval k) i)
          Dh0 Dhi :=
    (Path.cast_self (joinNat (p := fun l => (W.del i j hij hj hcl).ptMin hval' l)
      (fun l => (W.del i j hij hj hcl).edgeUNat hval' l) i) rfl rfl).trans hhead
  -- the tail factor, after replacing the D-tail by the cast of the tail of `W`
  have hB : Path.cast (joinNat (p := fun l => (W.del i j hij hj hcl).ptMin hval' (i + l))
        (fun l => (W.del i j hij hj hcl).edgeUNat hval' (i + l)) (W.n - j)) rfl e2
      = Path.cast (joinNat (p := fun l => W.ptMin hval (i + ((j - i) + l)))
          (fun l => W.edgeUNat hval (i + ((j - i) + l))) (W.n - j))
          ((rfl.trans Dt0).trans pr0) ((e2.trans DtK).trans prK) := by
    rw [htail, Path.cast_cast, hreindex, Path.cast_cast]
  have hstep3 : Path.Homotopic
      ((Path.cast (joinNat (p := fun l => (W.del i j hij hj hcl).ptMin hval' l)
            (fun l => (W.del i j hij hj hcl).edgeUNat hval' l) i) rfl rfl).trans
        (Path.cast (joinNat (p := fun l => (W.del i j hij hj hcl).ptMin hval' (i + l))
            (fun l => (W.del i j hij hj hcl).edgeUNat hval' (i + l)) (W.n - j)) rfl e2))
      ((Path.cast (joinNat (p := fun k => W.ptMin hval k) (fun k => W.edgeUNat hval k) i)
            Dh0 Dhi).trans
        (Path.cast (joinNat (p := fun l => W.ptMin hval (i + ((j - i) + l)))
            (fun l => W.edgeUNat hval (i + ((j - i) + l))) (W.n - j))
            ((rfl.trans Dt0).trans pr0) ((e2.trans DtK).trans prK))) :=
    Path.Homotopic.hcomp (path_homotopic_of_eq hA) (path_homotopic_of_eq hB)
  -- the target loop, expanded over the trans
  have hP1 : Path.cast ((joinNat (p := fun k => W.ptMin hval k) (fun k => W.edgeUNat hval k) i).trans
        (Path.cast (joinNat (p := fun l => W.ptMin hval (i + ((j - i) + l)))
          (fun l => W.edgeUNat hval (i + ((j - i) + l))) (W.n - j)) hpt hclosed.symm)) Dh0 Dh0
      = (Path.cast (joinNat (p := fun k => W.ptMin hval k) (fun k => W.edgeUNat hval k) i)
            Dh0 Dhi).trans
        (Path.cast (Path.cast (joinNat (p := fun l => W.ptMin hval (i + ((j - i) + l)))
          (fun l => W.edgeUNat hval (i + ((j - i) + l))) (W.n - j)) hpt hclosed.symm) Dhi Dh0) :=
    cast_trans_general _ _ Dh0 Dhi Dh0
  -- and the inner cast of the tail is the same cast as the one produced above
  have hT : Path.cast (Path.cast (joinNat (p := fun l => W.ptMin hval (i + ((j - i) + l)))
        (fun l => W.edgeUNat hval (i + ((j - i) + l))) (W.n - j)) hpt hclosed.symm) Dhi Dh0
      = Path.cast (joinNat (p := fun l => W.ptMin hval (i + ((j - i) + l)))
          (fun l => W.edgeUNat hval (i + ((j - i) + l))) (W.n - j))
          ((rfl.trans Dt0).trans pr0) ((e2.trans DtK).trans prK) := by
    rw [Path.cast_cast]
  -- assemble: the cast of the target loop is homotopic to the D-loop
  have hkey : Path.Homotopic
      (Path.cast ((joinNat (p := fun k => W.ptMin hval k) (fun k => W.edgeUNat hval k) i).trans
        (Path.cast (joinNat (p := fun l => W.ptMin hval (i + ((j - i) + l)))
          (fun l => W.edgeUNat hval (i + ((j - i) + l))) (W.n - j)) hpt hclosed.symm)) Dh0 Dh0)
      (Path.cast (joinNat (p := fun l => (W.del i j hij hj hcl).ptMin hval' l)
          (fun l => (W.del i j hij hj hcl).edgeUNat hval' l) (W.del i j hij hj hcl).n) rfl e2) := by
    rw [hP1, hT]
    exact ((hstep1.trans (path_homotopic_of_eq hstep2)).trans hstep3).symm
  -- undo the extra cast and conclude
  have hfin : Path.Homotopic
      ((joinNat (p := fun k => W.ptMin hval k) (fun k => W.edgeUNat hval k) i).trans
        (Path.cast (joinNat (p := fun l => W.ptMin hval (i + ((j - i) + l)))
          (fun l => W.edgeUNat hval (i + ((j - i) + l))) (W.n - j)) hpt hclosed.symm))
      (Path.refl (W.ptMin hval 0)) := by
    have hpc := Path.Homotopic.pathCast (hkey.trans h0) Dh0.symm Dh0.symm
    have hL : Path.cast (Path.cast ((joinNat (p := fun k => W.ptMin hval k)
          (fun k => W.edgeUNat hval k) i).trans
          (Path.cast (joinNat (p := fun l => W.ptMin hval (i + ((j - i) + l)))
            (fun l => W.edgeUNat hval (i + ((j - i) + l))) (W.n - j)) hpt hclosed.symm)) Dh0 Dh0)
        Dh0.symm Dh0.symm
        = ((joinNat (p := fun k => W.ptMin hval k) (fun k => W.edgeUNat hval k) i).trans
          (Path.cast (joinNat (p := fun l => W.ptMin hval (i + ((j - i) + l)))
            (fun l => W.edgeUNat hval (i + ((j - i) + l))) (W.n - j)) hpt hclosed.symm)) :=
      (Path.cast_cast _ Dh0 Dh0 Dh0.symm Dh0.symm).trans
        ((path_cast_proof_irrel _ (Dh0.symm.trans Dh0) rfl (Dh0.symm.trans Dh0) rfl).trans
          (Path.cast_self _ rfl rfl))
    have hR : Path.cast (Path.refl (W.ptMin hval 0)) Dh0.symm Dh0.symm
        = Path.refl (W.ptMin hval 0) := by
      apply Path.ext
      funext s
      exact (path_cast_apply (Path.refl (W.ptMin hval 0)) Dh0.symm Dh0.symm s).trans Dh0
    exact hR ▸ hL ▸ hpc
  exact hfin
/-- **The cut in the subtype.**  If both pieces of the decomposition of `W` at a non-trivial
double point `W.v i = W.v j` are null-homotopic in `↥U`, then so is `W`. -/
theorem nullhomotopic_of_sub_del_loopNat {U : Set ℂ}
    {W : LWalk} {hval : ∀ t, W.path t ∈ U}
    {i j : ℕ} (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j)
    (hval_sub : ∀ t, (W.sub i j hij hj hcl).path t ∈ U)
    (hval_del : ∀ t, (W.del i j hij hj hcl).path t ∈ U)
    (hsub : Path.Homotopic ((W.sub i j hij hj hcl).loopNat hval_sub)
        (Path.refl ((W.sub i j hij hj hcl).ptMin hval_sub 0)))
    (hdel : Path.Homotopic ((W.del i j hij hj hcl).loopNat hval_del)
        (Path.refl ((W.del i j hij hj hcl).ptMin hval_del 0))) :
    Path.Homotopic (W.loopNat hval) (Path.refl (W.ptMin hval 0)) := by
  have hpt : W.ptMin hval i = W.ptMin hval (i + (j - i)) := by
    rw [Nat.add_sub_cancel' (le_of_lt hij)]
    refine Subtype.ext ?_
    rw [W.ptMin_apply, W.ptMin_apply, Nat.min_eq_left (by omega : i ≤ W.n),
      Nat.min_eq_left hj, W.pt_at_cut i j hij hj hcl]
  have hclosed : W.ptMin hval (i + ((j - i) + (W.n - j))) = W.ptMin hval 0 := by
    rw [show i + ((j - i) + (W.n - j)) = W.n from by omega]
    exact (W.ptMin_zero_eq_last hval).symm
  have hcut := nullhomotopic_of_joinNat_cut (p := W.ptMin hval) (W.edgeUNat hval) hpt hclosed
    (sub_mid_homotopic hij hj hcl hval_sub hpt hsub)
    (del_compl_homotopic hij hj hcl hval_del hpt hclosed hdel)
  have hloop : W.loopNat hval = Path.cast (joinNat (p := W.ptMin hval) (W.edgeUNat hval)
      (i + ((j - i) + (W.n - j)))) rfl hclosed.symm := by
    rw [LWalk.loopNat_eq_joinNat]
    rw [joinNat_of_eq (W.edgeUNat hval)
      (show W.n = i + ((j - i) + (W.n - j)) from by omega)]
    rw [Path.cast_cast]
    exact path_cast_proof_irrel _ _ _ _ _
  exact (path_homotopic_of_eq hloop).trans hcut

/-- **The corner edge at the seam.**  At the seam vertex `p = W.v 0` of a simple closed lattice
walk that is lexicographically maximal there, one of the two edges of the walk meeting `p` is the
vertical canonical edge below `p`. -/
theorem exists_edgeV_corner_seam {W : LWalk}
    (hlex : ∀ j, j ≤ W.n → ((W.v j).1 < (W.v 0).1) ∨
      ((W.v j).1 = (W.v 0).1 ∧ (W.v j).2 ≤ (W.v 0).2))
    (hW : W.IsSimple) (hn : 2 < W.n) :
    ∃ j, j < W.n ∧ Set.range (W.edge j) = edgeV W.c ((W.v 0).1, (W.v 0).2 - 1) := by
  set p : ℤ × ℤ := W.v 0 with hp
  have hd1 : W.v (W.n - 1) = p - (1, 0) ∨ W.v (W.n - 1) = p - (0, 1) := by
    have hstep : GridStep (W.v (W.n - 1)) p := by
      have h := W.step (W.n - 1) (by omega)
      rwa [show W.n - 1 + 1 = W.n from by omega, W.closed, ← hp] at h
    exact LWalk.eq_sub_of_gridStep_le_left hstep (hlex (W.n - 1) (by omega))
  have hd2 : W.v 1 = p - (1, 0) ∨ W.v 1 = p - (0, 1) := by
    have hstep : GridStep (W.v 1) p := by
      have h := gridStep_symm (W.step 0 (by omega))
      rwa [show (0 : ℕ) + 1 = 1 from rfl, ← hp] at h
    exact LWalk.eq_sub_of_gridStep_le_left hstep (hlex 1 (by omega))
  have hne : W.v (W.n - 1) ≠ W.v 1 :=
    fun hc => hW 1 (W.n - 1) (by omega) (by omega)
      (by intro h; exact absurd (congrArg Prod.fst h) (by norm_num)) hc.symm
  have hv : W.v (W.n - 1) = p - (0, 1) ∨ W.v 1 = p - (0, 1) := by
    rcases hd1 with h1 | h1
    · rcases hd2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · exact Or.inr h2
    · exact Or.inl h1
  have hpe : (p.1, p.2 - 1) + (0, 1) = p := by ext <;> simp <;> omega
  rcases hv with h1 | h2
  · refine ⟨W.n - 1, by omega, ?_⟩
    have hpt1 : W.pt (W.n - 1) = W.c • gpt (p.1, p.2 - 1) := by
      rw [LWalk.pt, h1, Complex.real_smul]
      congr 2
      ext <;> simp <;> omega
    have hpt2 : W.pt (W.n - 1 + 1) = W.c • gpt p := by
      show W.c * gpt (W.v (W.n - 1 + 1)) = W.c • gpt p
      rw [show W.n - 1 + 1 = W.n from by omega, W.closed, ← hp, Complex.real_smul]
    rw [show W.edge (W.n - 1) = segPath (W.pt (W.n - 1)) (W.pt (W.n - 1 + 1)) from rfl,
      segPath_range, hpt1, hpt2, edgeV, hpe]
  · refine ⟨0, by omega, ?_⟩
    have hpt1 : W.pt 0 = W.c • gpt p := by
      show W.c * gpt (W.v 0) = W.c • gpt p
      rw [← hp, Complex.real_smul]
    have hpt2 : W.pt (0 + 1) = W.c • gpt (p.1, p.2 - 1) := by
      rw [LWalk.pt, h2, Complex.real_smul]
      congr 2
      ext <;> simp <;> omega
    rw [show W.edge 0 = segPath (W.pt 0) (W.pt (0 + 1)) from rfl, segPath_range, hpt1, hpt2,
      edgeV, hpe, segment_symm]

/-- **The corner cell at the seam is on the bounded side.** -/
theorem unitCell_corner_subset_V_seam {W : LWalk}
    {S : Work.Smooth.Jordan.PlaneSeparation W.toPlaneCurve}
    (hmax : ∀ j, j ≤ W.n → ((W.v j).1 : ℝ) * W.c ≤ ((W.v 0).1 : ℝ) * W.c)
    (hlex : ∀ j, j ≤ W.n → ((W.v j).1 < (W.v 0).1) ∨
      ((W.v j).1 = (W.v 0).1 ∧ (W.v j).2 ≤ (W.v 0).2))
    (hW : W.IsSimple) (hn : 4 ≤ W.n) :
    unitCell W.c (W.v 0 - (1, 1)) ⊆ S.V := by
  classical
  set p : ℤ × ℤ := W.v 0 with hp
  set q : ℤ × ℤ := (p.1, p.2 - 1) with hq
  have hcorner : p - (1, 1) = (q.1 - 1, q.2) := by
    rw [hq]; ext <;> simp
  by_contra hnot
  have hCU : unitCell W.c (q.1 - 1, q.2) ⊆ S.U := by
    rw [← hcorner]
    rcases cell_subset_U_or_V W S (p - (1, 1)) with h | h
    · exact h
    · exact absurd h hnot
  have hEU : unitCell W.c q ⊆ S.U := by
    refine subset_trans ?_ (LWalk.halfplane_subset_U (W := W) (S := S) (k := 0) (Nat.zero_le _) hmax)
    intro z hz
    rw [mem_cell] at hz
    rw [hq] at hz
    exact hz.1
  obtain ⟨j, hj, hje⟩ := exists_edgeV_corner_seam (W := W) hlex hW (by omega)
  have hball := exists_ball_inter_edge W hj
  have hwmem : W.midPoint j ∈ Set.range (W.edge j) := LWalk.midPoint_mem_edge W j
  have hwcurve : W.midPoint j ∈ Set.range W.curve := edge_range_subset_curve W hj hwmem
  have hwcl : W.midPoint j ∈ closure S.V := by
    have h1 : W.midPoint j ∈ frontier S.V := by
      rw [LWalk.frontier_V_eq_range hW hn S]
      exact hwcurve
    exact frontier_subset_closure h1
  obtain ⟨v, hvV, hvdist⟩ := Metric.mem_closure_iff.mp hwcl (W.c / 4) (by linarith [W.cpos])
  have hvnot : v ∉ Set.range W.curve := by
    have h : v ∈ (W.toPlaneCurve.trace)ᶜ := by
      rw [← S.union_eq]; exact Or.inr hvV
    exact h
  have hvnotedge : v ∉ edgeV W.c q := by
    rw [← hje]
    exact fun hc => hvnot (edge_range_subset_curve W hj hc)
  have hmid : W.midPoint j = midV W.c q := midPoint_eq_midV_of_range hj hje
  have hvcells : v ∈ unitCell W.c (q.1 - 1, q.2) ∪ unitCell W.c q := by
    refine LWalk.ball_midV_subset_cells W.cpos (q := q) ?_
    rw [Set.mem_sdiff, Metric.mem_ball, dist_comm, ← hmid]
    exact ⟨hvdist, hvnotedge⟩
  rcases hvcells with h | h
  · exact Set.disjoint_left.mp S.disjoint_UV (hCU h) hvV
  · exact Set.disjoint_left.mp S.disjoint_UV (hEU h) hvV

/-- Free homotopy to a null-homotopic loop is a null-homotopy. -/
theorem nullhomotopic_of_freeHomotopic {X : Type*} [TopologicalSpace X] {x y : X}
    {p : Path x x} {q : Path y y} (hf : FreeHomotopic p q)
    (hq : Path.Homotopic q (Path.refl y)) : Path.Homotopic p (Path.refl x) := by
  obtain ⟨a, ha⟩ := hf
  have h1 : Path.Homotopic (a.symm.trans (p.trans a)) (Path.refl y) := ha.trans hq
  have h2 : Path.Homotopic ((a.trans (a.symm.trans (p.trans a))).trans a.symm)
      ((a.trans (Path.refl y)).trans a.symm) :=
    Path.Homotopic.hcomp
      (Path.Homotopic.hcomp (Path.Homotopic.refl a) h1) (Path.Homotopic.refl a.symm)
  have h3 : Path.Homotopic ((a.trans (a.symm.trans (p.trans a))).trans a.symm) (Path.refl x) :=
    h2.trans ((Path.Homotopic.hcomp (Path.Homotopic.trans_refl a)
        (Path.Homotopic.refl a.symm)).trans (Path.Homotopic.trans_symm a))
  have h4 : Path.Homotopic ((a.trans (a.symm.trans (p.trans a))).trans a.symm) p := by
    have s1 : Path.Homotopic ((a.trans (a.symm.trans (p.trans a))).trans a.symm)
        (a.trans ((a.symm.trans (p.trans a)).trans a.symm)) :=
      Path.Homotopic.trans_assoc a (a.symm.trans (p.trans a)) a.symm
    have s2 : Path.Homotopic (a.trans ((a.symm.trans (p.trans a)).trans a.symm))
        (a.trans ((a.symm.trans p).trans (a.trans a.symm))) :=
      Path.Homotopic.hcomp (Path.Homotopic.refl a)
        ((Path.Homotopic.hcomp (Path.Homotopic.trans_assoc a.symm p a).symm
            (Path.Homotopic.refl a.symm)).trans
          (Path.Homotopic.trans_assoc (a.symm.trans p) a a.symm))
    have s3 : Path.Homotopic (a.trans ((a.symm.trans p).trans (a.trans a.symm)))
        ((a.trans (a.symm.trans p)).trans (a.trans a.symm)) :=
      (Path.Homotopic.trans_assoc a (a.symm.trans p) (a.trans a.symm)).symm
    have s4 : Path.Homotopic ((a.trans (a.symm.trans p)).trans (a.trans a.symm))
        (((a.trans a.symm).trans p).trans (a.trans a.symm)) :=
      Path.Homotopic.hcomp (Path.Homotopic.trans_assoc a a.symm p).symm
        (Path.Homotopic.refl (a.trans a.symm))
    have s5 : Path.Homotopic (((a.trans a.symm).trans p).trans (a.trans a.symm))
        (((Path.refl x).trans p).trans (a.trans a.symm)) :=
      Path.Homotopic.hcomp
        (Path.Homotopic.hcomp (Path.Homotopic.trans_symm a) (Path.Homotopic.refl p))
        (Path.Homotopic.refl (a.trans a.symm))
    have s6 : Path.Homotopic (((Path.refl x).trans p).trans (a.trans a.symm))
        (p.trans (a.trans a.symm)) :=
      Path.Homotopic.hcomp (Path.Homotopic.refl_trans p)
        (Path.Homotopic.refl (a.trans a.symm))
    have s7 : Path.Homotopic (p.trans (a.trans a.symm)) (p.trans (Path.refl x)) :=
      Path.Homotopic.hcomp (Path.Homotopic.refl p) (Path.Homotopic.trans_symm a)
    have s8 : Path.Homotopic (p.trans (Path.refl x)) p := Path.Homotopic.trans_refl p
    exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans s8))))))
  exact h4.symm.trans h3

/-- A loop whose image lies in a convex subset `B ⊆ U` is null-homotopic in `↥U`. -/
theorem loopNat_nullhomotopic_of_convex {U : Set ℂ} {W : LWalk} (hval : ∀ t, W.path t ∈ U)
    {B : Set ℂ} (hBc : Convex ℝ B) (hBne : B.Nonempty) (hBU : B ⊆ U)
    (hmem : ∀ t, W.loop t ∈ B) :
    Path.Homotopic (W.loopNat hval) (Path.refl (W.ptMin hval 0)) := by
  refine homotopic_of_convex_subset hBc hBne hBU _ _ (fun t => ?_) (fun t => ?_)
  · rw [loopNat_coe_apply W hval t]; exact hmem t
  · have h0 : ((W.loopNat hval) 0 : ℂ) = W.pt 0 := by
      rw [loopNat_coe_apply W hval 0,
        show W.loop = W.path.cast rfl W.pt_last.symm from rfl, path_cast_apply]
      exact Path.source W.path
    have hpt0B : W.pt 0 ∈ B := by
      rw [← h0, loopNat_coe_apply W hval 0]; exact hmem 0
    show ((W.ptMin hval 0 : ↥U) : ℂ) ∈ B
    rwa [W.ptMin_apply hval 0, Nat.min_eq_left (Nat.zero_le (W.n))]

/-- **The base case of the peel: walks with at most three edges.**  A closed lattice walk of
length `≤ 3` has even length, hence length `0` or `2`; in both cases its image lies in a segment, so
it is null-homotopic in `↥U`. -/
theorem loopNat_nullhomotopic_of_n_le_three {U : Set ℂ} {W : LWalk}
    (hval : ∀ t, W.path t ∈ U) (hn : W.n ≤ 3) :
    Path.Homotopic (W.loopNat hval) (Path.refl (W.ptMin hval 0)) := by
  have hEven : W.n = 0 ∨ W.n = 2 := by
    obtain ⟨k, hk⟩ := even_n_of_closed W
    omega
  rcases hEven with hn0 | hn2
  · have hmem : ∀ t, W.loop t ∈ ({W.pt 0} : Set ℂ) := by
      intro t
      have hp : W.path t = W.pt 0 := by
        rw [show W.path = joinNat (p := W.pt) (fun k => W.edge k) W.n from rfl,
          joinNat_of_eq (fun k => W.edge k) hn0, path_cast_apply]
        rfl
      rw [show W.loop = W.path.cast rfl W.pt_last.symm from rfl, path_cast_apply, hp]
      exact rfl
    refine loopNat_nullhomotopic_of_convex hval (convex_singleton _) ⟨_, rfl⟩ ?_ hmem
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact W.pt_mem hval (Nat.zero_le _)
  · have hpt2 : W.pt 2 = W.pt 0 := (congrArg W.pt hn2.symm).trans W.pt_last
    have hedge0 : Set.range (W.edge 0) = segment ℝ (W.pt 0) (W.pt 1) := by
      rw [show W.edge 0 = Path.segment (W.pt 0) (W.pt (0 + 1)) from rfl, Path.range_segment]
    have hedge1 : Set.range (W.edge 1) = segment ℝ (W.pt 0) (W.pt 1) := by
      rw [show W.edge 1 = Path.segment (W.pt 1) (W.pt (1 + 1)) from rfl, Path.range_segment,
        hpt2, segment_symm]
    have hrange : Set.range W.path ⊆ segment ℝ (W.pt 0) (W.pt 1) := by
      rw [LWalk.range_path]
      refine Set.union_subset ?_ ?_
      · refine Set.iUnion_subset fun k => Set.iUnion_subset fun hk => ?_
        have hk2 : k < 2 := by rw [← hn2]; exact hk
        interval_cases k
        · rw [hedge0]
        · rw [hedge1]
      · rw [Set.singleton_subset_iff]
        exact left_mem_segment ℝ (W.pt 0) (W.pt 1)
    have hmem : ∀ t, W.loop t ∈ segment ℝ (W.pt 0) (W.pt 1) := by
      intro t
      have h1 : W.loop t ∈ Set.range W.path := by
        rw [show W.loop = W.path.cast rfl W.pt_last.symm from rfl, path_cast_apply]
        exact ⟨t, rfl⟩
      exact hrange h1
    have hBU : segment ℝ (W.pt 0) (W.pt 1) ⊆ U := by
      rw [← hedge0]
      exact W.range_edge_subset hval (by omega)
    exact loopNat_nullhomotopic_of_convex hval (convex_segment _ _)
      ⟨_, left_mem_segment ℝ (W.pt 0) (W.pt 1)⟩ hBU hmem

theorem lwalk_nullhomotopic {U : Set ℂ} (hUo : IsOpen U)
    (hpre : IsPreconnected (((↑) : ℂ → OnePoint ℂ) '' Uᶜ ∪ {OnePoint.infty}))
    {W : Work.Smooth.JordanSeparation.LWalk} (hval : ∀ t, W.path t ∈ U) :
    Path.Homotopic (W.loopNat hval) (Path.refl (W.ptMin hval 0)) := by
  have key : ∀ m, ∀ X (hXn : X.n ≤ W.n), peelMeasure W.n X < m →
      ∀ hvalX : ∀ t, X.path t ∈ U,
      Path.Homotopic (X.loopNat hvalX) (Path.refl (X.ptMin hvalX 0)) := by
    intro m
    induction m with
    | zero =>
      intro X hXn hlt hvalX
      exact absurd hlt (Nat.not_lt_zero _)
    | succ m ih =>
      intro X hXn hlt hvalX
      by_cases hsimple : X.IsSimple
      · by_cases hsmall : X.n ≤ 3
        · exact loopNat_nullhomotopic_of_n_le_three (W := X) hvalX hsmall
        · -- simple, `4 ≤ X.n`: the corner move
          have hn4 : 4 ≤ X.n := by omega
          obtain ⟨S⟩ := X.exists_planeSeparation hsimple hn4
          obtain ⟨k, hk_le, hvk⟩ := exists_vmax X
          have hcorner : (X.v 0 = vmax X) ∨ (1 ≤ k ∧ k + 1 ≤ X.n) := by
            rcases eq_or_ne k 0 with h | h
            · left; rw [← h]; exact hvk
            · rcases eq_or_ne k X.n with h' | h'
              · left; rw [← X.closed, ← h']; exact hvk
              · right; omega
          rcases hcorner with hv0 | ⟨hk1, hk2⟩
          · -- the lex-max vertex is the seam: the seam flip
            have hmax : ∀ j, j ≤ X.n → ((X.v j).1 : ℝ) * X.c ≤ ((X.v 0).1 : ℝ) * X.c := by
              intro j hj
              have hv0' : (vmax X).1 = (X.v 0).1 := congrArg Prod.fst hv0.symm
              have h1 : (X.v j).1 ≤ (X.v 0).1 := by
                rcases (lexLe_iff _ _).mp (le_vmax X hj) with h | ⟨h, -⟩
                · omega
                · omega
              have h2 : ((X.v j).1 : ℝ) ≤ ((X.v 0).1 : ℝ) := by exact_mod_cast h1
              exact mul_le_mul_of_nonneg_right h2 (le_of_lt X.cpos)
            have hlex : ∀ j, j ≤ X.n → ((X.v j).1 < (X.v 0).1) ∨
                ((X.v j).1 = (X.v 0).1 ∧ (X.v j).2 ≤ (X.v 0).2) := by
              intro j hj
              have hv01 : (vmax X).1 = (X.v 0).1 := congrArg Prod.fst hv0.symm
              have hv02 : (vmax X).2 = (X.v 0).2 := congrArg Prod.snd hv0.symm
              rcases (lexLe_iff _ _).mp (le_vmax X hj) with h | ⟨h1, h2⟩
              · left; omega
              · right; exact ⟨by omega, by omega⟩
            have hcell : cellCl X.c (X.v 0 - (1, 1)) ⊆ U :=
              cellCl_subset_U hUo hpre hsimple hn4 hvalX S
                (unitCell_corner_subset_V_seam hmax hlex hsimple hn4)
            have h2 : 2 ≤ X.n := by omega
            have ha : X.v (X.n - 1) = X.v 0 - (1, 0) ∨ X.v (X.n - 1) = X.v 0 - (0, 1) := by
              have hstep : GridStep (X.v (X.n - 1)) (X.v 0) := by
                have h := X.step (X.n - 1) (by omega)
                rwa [show X.n - 1 + 1 = X.n from by omega, X.closed] at h
              exact LWalk.eq_sub_of_gridStep_le_left hstep (hlex (X.n - 1) (by omega))
            have hb : X.v 1 = X.v 0 - (1, 0) ∨ X.v 1 = X.v 0 - (0, 1) := by
              have hstep : GridStep (X.v 1) (X.v 0) := by
                have h := gridStep_symm (X.step 0 (by omega))
                rwa [show (0 : ℕ) + 1 = 1 from rfl] at h
              exact LWalk.eq_sub_of_gridStep_le_left hstep (hlex 1 (by omega))
            have hvalF : ∀ t, (X.seamFlip h2 ha hb).path t ∈ U :=
              seamFlip_path_mem_U (hval := hvalX) h2 ha hb hcell
            have hFn : (X.seamFlip h2 ha hb).n ≤ W.n := by
              rw [LWalk.seamFlip_n]; exact hXn
            have hlt' : peelMeasure W.n (X.seamFlip h2 ha hb) < m := by
              have hpc := peelMeasure_corner (N := W.n) hXn hFn (LWalk.seamFlip_n X h2 ha hb)
                (seamFlip_vmin_eq hsimple hn4 h2 ha hb hv0)
                (seamFlip_vmax_lt hsimple h2 ha hb hv0)
              omega
            exact nullhomotopic_of_freeHomotopic
              (seamFlip_free_homotopic h2 ha hb hcell hvalF)
              (ih (X.seamFlip h2 ha hb) hFn hlt' hvalF)
          · -- a genuine interior corner: the corner move of the peel
            have hmax : ∀ j, j ≤ X.n → ((X.v j).1 : ℝ) * X.c ≤ ((X.v k).1 : ℝ) * X.c := by
              intro j hj
              have hvk1 : (vmax X).1 = (X.v k).1 := congrArg Prod.fst hvk.symm
              have h1 : (X.v j).1 ≤ (X.v k).1 := by
                rcases (lexLe_iff _ _).mp (le_vmax X hj) with h | ⟨h, -⟩
                · omega
                · omega
              have h2 : ((X.v j).1 : ℝ) ≤ ((X.v k).1 : ℝ) := by exact_mod_cast h1
              exact mul_le_mul_of_nonneg_right h2 (le_of_lt X.cpos)
            have hlex : ∀ j, j ≤ X.n → ((X.v j).1 < (X.v k).1) ∨
                ((X.v j).1 = (X.v k).1 ∧ (X.v j).2 ≤ (X.v k).2) := by
              intro j hj
              have hvk1 : (vmax X).1 = (X.v k).1 := congrArg Prod.fst hvk.symm
              have hvk2 : (vmax X).2 = (X.v k).2 := congrArg Prod.snd hvk.symm
              rcases (lexLe_iff _ _).mp (le_vmax X hj) with h | ⟨h1, h2⟩
              · left; omega
              · right; exact ⟨by omega, by omega⟩
            have hlex' : ∀ j, j ≤ X.n → (X.v j).1 < (vmax X).1 ∨
                ((X.v j).1 = (vmax X).1 ∧ (X.v j).2 ≤ (vmax X).2) := by
              simpa only [hvk] using hlex
            obtain ⟨ha', hb', -⟩ := corner_data hk1 hk2 hvk hlex' hsimple (by omega)
            have ha : X.v (k - 1) = X.v k - (1, 0) ∨ X.v (k - 1) = X.v k - (0, 1) := by
              rcases ha' with h | h
              · left; rw [h, ← hvk]
              · right; rw [h, ← hvk]
            have hb : X.v (k + 1) = X.v k - (1, 0) ∨ X.v (k + 1) = X.v k - (0, 1) := by
              rcases hb' with h | h
              · left; rw [h, ← hvk]
              · right; rw [h, ← hvk]
            have hcell : cellCl X.c (X.v k - (1, 1)) ⊆ U :=
              cellCl_subset_U hUo hpre hsimple hn4 hvalX S
                (LWalk.unitCell_corner_subset_V hk1 hk2 hmax hlex hsimple hn4)
            have hvalF : ∀ t, (X.flip hk1 hk2 ha hb).path t ∈ U :=
              flip_path_mem_U (hval := hvalX) hk1 hk2 ha hb hcell
            have he : X.ptMin hvalX 0 = (X.flip hk1 hk2 ha hb).ptMin hvalF 0 :=
              flip_ptMin_eq hk1 hk2 ha hb hvalF (Nat.zero_le _) (by omega)
            have hFn : (X.flip hk1 hk2 ha hb).n ≤ W.n := by
              rw [LWalk.flip_n]; exact hXn
            have hlt' : peelMeasure W.n (X.flip hk1 hk2 ha hb) < m := by
              have hpc := peelMeasure_corner (N := W.n) hXn hFn
                (LWalk.flip_n X hk1 hk2 ha hb)
                (vmin_flip_eq hsimple hn4 hk1 hk2 ha hb hvk)
                (vmax_flip_lt hsimple hk1 hk2 ha hb hvk)
              omega
            have hcast := Path.Homotopic.pathCast
              (ih (X.flip hk1 hk2 ha hb) hFn hlt' hvalF) he he
            have hrefl : (Path.refl ((X.flip hk1 hk2 ha hb).ptMin hvalF 0)).cast he he
                = Path.refl (X.ptMin hvalX 0) := by
              apply Path.ext
              funext s
              exact (path_cast_apply _ he he s).trans he.symm
            exact (flip_loop_homotopic hk1 hk2 ha hb hcell hvalF he).trans (hrefl ▸ hcast)
      · -- not simple: cut at a non-trivial double point
        obtain ⟨i, j, hij, hj, hne, hcl⟩ := LWalk.exists_double_of_not_simple X hsimple
        have hne' : i ≠ 0 ∨ j ≠ X.n := by
          by_contra h
          push_neg at h
          exact hne (by rw [h.1, h.2])
        have hsubn : (X.sub i j hij hj hcl).n = j - i := rfl
        have hdeln : (X.del i j hij hj hcl).n = i + (X.n - j) := rfl
        have hsub_lt : (X.sub i j hij hj hcl).n < X.n := by rw [hsubn]; omega
        have hdel_lt : (X.del i j hij hj hcl).n < X.n := by rw [hdeln]; omega
        have hsub_val : ∀ t, (X.sub i j hij hj hcl).path t ∈ U := by
          intro t
          obtain ⟨t', ht'⟩ := X.sub_range_subset i j hij hj hcl ⟨t, rfl⟩
          rw [← ht']; exact hvalX t'
        have hdel_val : ∀ t, (X.del i j hij hj hcl).path t ∈ U := by
          intro t
          obtain ⟨t', ht'⟩ := X.del_range_subset i j hij hj hcl ⟨t, rfl⟩
          rw [← ht']; exact hvalX t'
        refine nullhomotopic_of_sub_del_loopNat hij hj hcl hsub_val hdel_val ?_ ?_
        · exact ih (X.sub i j hij hj hcl) (by rw [hsubn]; omega) (by
            have hpc := peelMeasure_cut (N := W.n) hXn (by rw [hsubn]; omega) hsub_lt
            omega) hsub_val
        · exact ih (X.del i j hij hj hcl) (by rw [hdeln]; omega) (by
            have hpc := peelMeasure_cut (N := W.n) hXn (by rw [hdeln]; omega) hdel_lt
            omega) hdel_val
  exact key (peelMeasure W.n W + 1) W le_rfl (Nat.lt_succ_self _) hval

end

end Work.SphereJordan
