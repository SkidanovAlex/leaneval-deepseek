import Mathlib
import Submission.Commons.Topology.Plane.polyomino_deformationRetract_oneDim
import Submission.Commons.Topology.Jordan.plane_separation
import Submission.Commons.Topology.Jordan.crossing_parity_of_path
import Submission.Commons.Topology.Jordan.complement_frontier_of_periodic_embedding
import Submission.Commons.Topology.Jordan.separation_of_periodic_embedding

open Set Filter
open scoped Topology

noncomputable section

namespace Commons.Topology.Jordan

/-- The piecewise linear interpolant of a sequence `A : ℤ → ℂ`, using the `floor`/`fract`
decomposition of the parameter. -/
def floorInterp (A : ℤ → ℂ) (x : ℝ) : ℂ :=
  (1 - Int.fract x) • A ⌊x⌋ + Int.fract x • A (⌊x⌋ + 1)

/-- The affine parametrization of the segment between `A k` and `A (k+1)`. -/
def latSeg (A : ℤ → ℂ) (k : ℤ) (t : ℝ) : ℂ := A k + (t - (k : ℝ)) • (A (k + 1) - A k)

lemma latSeg_continuous (A : ℤ → ℂ) (k : ℤ) : Continuous (latSeg A k) := by
  unfold latSeg; fun_prop

lemma latSeg_injective (A : ℤ → ℂ) {k : ℤ} (h : A k ≠ A (k + 1)) :
    Function.Injective (latSeg A k) := by
  intro x y hxy
  have h1 : (x - (k : ℝ)) • (A (k + 1) - A k) = (y - (k : ℝ)) • (A (k + 1) - A k) := by
    have h2 := congrArg (fun w : ℂ => w - A k) hxy
    simpa only [latSeg, add_sub_cancel_left] using h2
  have h2 : (x - (k : ℝ) - (y - (k : ℝ))) • (A (k + 1) - A k) = 0 := by
    rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · linarith
  · exact absurd (sub_eq_zero.mp h3) (Ne.symm h)

lemma latSeg_right (A : ℤ → ℂ) (k : ℤ) : latSeg A k ((k : ℝ) + 1) = A (k + 1) := by
  unfold latSeg; simp

lemma latSeg_left (A : ℤ → ℂ) (k : ℤ) : latSeg A k (k : ℝ) = A k := by
  unfold latSeg; simp

lemma floorInterp_eq_latSeg {A : ℤ → ℂ} {k : ℤ} {x : ℝ}
    (hx : x ∈ Ico (k : ℝ) ((k : ℝ) + 1)) : floorInterp A x = latSeg A k x := by
  have hf : ⌊x⌋ = k := Int.floor_eq_iff.mpr ⟨hx.1, hx.2⟩
  have hfr : Int.fract x = x - (k : ℝ) := by rw [← Int.self_sub_floor x, hf]
  unfold floorInterp latSeg
  rw [hf, hfr]
  simp only [sub_smul, one_smul, smul_sub]
  abel

lemma floorInterp_intCast (A : ℤ → ℂ) (k : ℤ) : floorInterp A (k : ℝ) = A k := by
  unfold floorInterp
  rw [Int.floor_intCast, Int.fract_intCast]
  simp

lemma floorInterp_eq_latSeg_of_mem_Icc {A : ℤ → ℂ} {k : ℤ} {x : ℝ}
    (hx : x ∈ Icc (k : ℝ) ((k : ℝ) + 1)) : floorInterp A x = latSeg A k x := by
  rcases lt_or_eq_of_le hx.2 with h | h
  · exact floorInterp_eq_latSeg ⟨hx.1, h⟩
  · subst h
    have hcast : (k : ℝ) + 1 = ((k + 1 : ℤ) : ℝ) := by push_cast; ring
    rw [hcast, floorInterp_intCast]
    rw [show (((k + 1 : ℤ)) : ℝ) = (k : ℝ) + 1 by push_cast; ring, latSeg_right]

lemma floorInterp_mem_segment (A : ℤ → ℂ) (x : ℝ) :
    floorInterp A x ∈ segment ℝ (A ⌊x⌋) (A (⌊x⌋ + 1)) := by
  rw [segment_eq_image]
  exact ⟨Int.fract x, ⟨Int.fract_nonneg x, le_of_lt (Int.fract_lt_one x)⟩, rfl⟩

lemma latSeg_mem_segment (A : ℤ → ℂ) {k : ℤ} {x : ℝ}
    (hx : x ∈ Icc (k : ℝ) ((k : ℝ) + 1)) : latSeg A k x ∈ segment ℝ (A k) (A (k + 1)) := by
  rw [segment_eq_image]
  refine ⟨x - (k : ℝ), ⟨by linarith [hx.1], by linarith [hx.2]⟩, ?_⟩
  unfold latSeg
  simp only [sub_smul, one_smul, smul_sub]
  abel

lemma floorInterp_periodic_int (A : ℤ → ℂ) (M : ℤ) (hA : ∀ k : ℤ, A (k + M) = A k) :
    ∀ x : ℝ, floorInterp A (x + (M : ℝ)) = floorInterp A x := by
  intro x
  have h1 : ⌊x + (M : ℝ)⌋ = ⌊x⌋ + M := Int.floor_add_intCast x M
  have h2 : Int.fract (x + (M : ℝ)) = Int.fract x := Int.fract_add_intCast x M
  have h3 : A (⌊x⌋ + M) = A ⌊x⌋ := hA ⌊x⌋
  have h4 : A (⌊x⌋ + M + 1) = A (⌊x⌋ + 1) := by
    have := hA (⌊x⌋ + 1)
    rwa [show ⌊x⌋ + 1 + M = ⌊x⌋ + M + 1 by ring] at this
  unfold floorInterp
  rw [h1, h2, h3, h4]

/-- **Continuity of the interpolant.** -/
lemma continuous_floorInterp (A : ℤ → ℂ) : Continuous (floorInterp A) := by
  rw [continuous_iff_continuousAt]
  intro x
  set k : ℤ := ⌊x⌋ with hk
  have hxIco : x ∈ Ico (k : ℝ) ((k : ℝ) + 1) := by
    refine ⟨?_, ?_⟩
    · rw [hk]; exact Int.floor_le x
    · rw [hk]; exact Int.lt_floor_add_one x
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · rcases lt_or_eq_of_le hxIco.1 with hlt | heq
    · have hev : latSeg A k =ᶠ[𝓝[Iio x] x] floorInterp A := by
        rw [Filter.eventuallyEq_iff_exists_mem]
        refine ⟨Ioo (k : ℝ) x, Ioo_mem_nhdsLT hlt, fun t ht => ?_⟩
        show latSeg A k t = floorInterp A t
        exact (floorInterp_eq_latSeg ⟨le_of_lt ht.1, lt_of_lt_of_le ht.2 hxIco.2.le⟩).symm
      exact ContinuousWithinAt.congr_of_eventuallyEq
        ((latSeg_continuous A k).continuousAt.continuousWithinAt) hev.symm
        (floorInterp_eq_latSeg hxIco)
    · have hxk : x = (k : ℝ) := heq.symm
      set j : ℤ := k - 1 with hj
      have hjlt : (j : ℝ) < x := by rw [hxk, hj]; push_cast; linarith
      have hjc : (j : ℝ) + 1 = (k : ℝ) := by rw [hj]; push_cast; ring
      have hev : latSeg A j =ᶠ[𝓝[Iio x] x] floorInterp A := by
        rw [Filter.eventuallyEq_iff_exists_mem]
        refine ⟨Ioo (j : ℝ) x, Ioo_mem_nhdsLT hjlt, fun t ht => ?_⟩
        show latSeg A j t = floorInterp A t
        exact (floorInterp_eq_latSeg ⟨le_of_lt ht.1,
          by rw [hjc, ← hxk]; exact ht.2⟩).symm
      have hval' : latSeg A j x = floorInterp A x := by
        have h1 : latSeg A j x = A (j + 1) := by
          rw [hxk, ← hjc]; exact latSeg_right A j
        have h2 : floorInterp A x = A k := by rw [hxk]; exact floorInterp_intCast A k
        rw [h1, h2, show j + 1 = k by omega]
      exact ContinuousWithinAt.congr_of_eventuallyEq
        ((latSeg_continuous A j).continuousAt.continuousWithinAt) hev.symm hval'.symm
  · have hev : latSeg A k =ᶠ[𝓝[Ioi x] x] floorInterp A := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨Ioo x ((k : ℝ) + 1), Ioo_mem_nhdsGT hxIco.2, fun t ht => ?_⟩
      show latSeg A k t = floorInterp A t
      exact (floorInterp_eq_latSeg ⟨by linarith [ht.1, hxIco.1], ht.2⟩).symm
    exact ContinuousWithinAt.congr_of_eventuallyEq
      ((latSeg_continuous A k).continuousAt.continuousWithinAt) hev.symm
      (floorInterp_eq_latSeg hxIco)

/-- The interpolant of a lattice walk. -/
def walkInterp (w : ℤ → ℤ × ℤ) (x : ℝ) : ℂ :=
  floorInterp (fun k => Commons.Topology.Plane.pc (w k)) x

lemma continuous_walkInterp (w : ℤ → ℤ × ℤ) : Continuous (walkInterp w) := by
  unfold walkInterp
  exact continuous_floorInterp _

lemma walkInterp_periodic_int (w : ℤ → ℤ × ℤ) (M : ℤ) (hper : ∀ k : ℤ, w (k + M) = w k) :
    ∀ x : ℝ, walkInterp w (x + (M : ℝ)) = walkInterp w x := by
  have hA : ∀ k : ℤ, (fun k => Commons.Topology.Plane.pc (w k)) (k + M)
      = (fun k => Commons.Topology.Plane.pc (w k)) k := fun k => congrArg _ (hper k)
  intro x
  exact floorInterp_periodic_int (fun k => Commons.Topology.Plane.pc (w k)) M hA x

lemma walkInterp_intCast (w : ℤ → ℤ × ℤ) (k : ℤ) :
    walkInterp w (k : ℝ) = Commons.Topology.Plane.pc (w k) := by
  unfold walkInterp
  exact floorInterp_intCast _ k

lemma walkInterp_eq_latSeg {w : ℤ → ℤ × ℤ} {k : ℤ} {x : ℝ}
    (hx : x ∈ Ico (k : ℝ) ((k : ℝ) + 1)) :
    walkInterp w x = latSeg (fun k => Commons.Topology.Plane.pc (w k)) k x :=
  floorInterp_eq_latSeg hx

/-- The only integer solutions of `a ^ 2 + b ^ 2 = 1` are the four unit vectors. -/
lemma int_sq_add_sq_eq_one {a b : ℤ} (h : a ^ 2 + b ^ 2 = 1) :
    (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1) := by
  have ha1 : -1 ≤ a := by nlinarith [sq_nonneg b, sq_nonneg (a + 1)]
  have ha3 : a ≤ 1 := by nlinarith [sq_nonneg b, sq_nonneg (a - 1)]
  have hb1 : -1 ≤ b := by nlinarith [sq_nonneg a, sq_nonneg (b + 1)]
  have hb3 : b ≤ 1 := by nlinarith [sq_nonneg a, sq_nonneg (b - 1)]
  interval_cases a <;> interval_cases b <;> simp_all

/-- A unit step of a lattice walk is one of the four axis-parallel unit moves. -/
lemma step_classification {w : ℤ → ℤ × ℤ}
    (hstep : ∀ k : ℤ, w (k + 1) ≠ w k ∧
      ((w (k + 1)).1 - (w k).1) ^ 2 + ((w (k + 1)).2 - (w k).2) ^ 2 = 1) (k : ℤ) :
    w (k + 1) = ((w k).1 + 1, (w k).2) ∨ w (k + 1) = ((w k).1 - 1, (w k).2) ∨
      w (k + 1) = ((w k).1, (w k).2 + 1) ∨ w (k + 1) = ((w k).1, (w k).2 - 1) := by
  have h := (hstep k).2
  rcases int_sq_add_sq_eq_one h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; ext <;> omega
  · right; left; ext <;> omega
  · right; right; left; ext <;> omega
  · right; right; right; ext <;> omega

/-- A walk that is `m`-periodic repeats the value at the residue `i % m`. -/
lemma w_eq_emod {w : ℤ → ℤ × ℤ} {m : ℕ}
    (hper : ∀ k : ℤ, w (k + (m : ℤ)) = w k) (i : ℤ) : w i = w (i % m) := by
  have hp : Function.Periodic w ((m : ℤ)) := hper
  have h : w (i % (m : ℤ) + ((i / (m : ℤ)) : ℤ) * (m : ℤ)) = w (i % (m : ℤ)) :=
    (hp.int_mul (i / (m : ℤ))) (i % (m : ℤ))
  have h' : w (i % (m : ℤ) + (m : ℤ) * (i / (m : ℤ))) = w (i % (m : ℤ)) := by
    simpa only [mul_comm] using h
  rwa [Int.emod_add_mul_ediv] at h'

/-- For a walk that is `m`-periodic and injective on `{0, …, m-1}`, two values are equal
exactly at indices congruent modulo `m`. -/
lemma w_eq_iff_emod {w : ℤ → ℤ × ℤ} {m : ℕ} (hm : 0 < m)
    (hper : ∀ k : ℤ, w (k + (m : ℤ)) = w k)
    (hinj : Set.InjOn w (Set.Ico (0 : ℤ) (m : ℤ))) (i j : ℤ) :
    w i = w j ↔ i % m = j % m := by
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmpos : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hmem : ∀ t : ℤ, t % m ∈ Set.Ico (0 : ℤ) (m : ℤ) := fun t =>
    ⟨Int.emod_nonneg t hmz, Int.emod_lt_of_pos t hmpos⟩
  constructor
  · intro h
    rw [w_eq_emod hper i, w_eq_emod hper j] at h
    exact hinj (hmem i) (hmem j) h
  · intro h
    rw [w_eq_emod hper i, w_eq_emod hper j, h]

/-- No backtracking: for `m > 2` an `m`-periodic walk injective on a period never returns to
the vertex two steps back. -/
lemma w_ne_add_two {w : ℤ → ℤ × ℤ} {m : ℕ} (hm : 2 < m)
    (hper : ∀ k : ℤ, w (k + (m : ℤ)) = w k)
    (hinj : Set.InjOn w (Set.Ico (0 : ℤ) (m : ℤ))) (k : ℤ) : w (k + 2) ≠ w k := by
  intro h
  have hm0 : 0 < m := by omega
  have hmod : k % m = (k + 2) % m := (w_eq_iff_emod hm0 hper hinj k (k + 2)).mp h.symm
  have h0 : (k - (k + 2)) % (m : ℤ) = 0 := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hmod
  have hdvd : (m : ℤ) ∣ (2 : ℤ) := by
    have h2 : (m : ℤ) ∣ (k - (k + 2)) := Int.dvd_of_emod_eq_zero h0
    have h3 : k - (k + 2) = -(2 : ℤ) := by ring
    rw [h3] at h2
    exact dvd_neg.mp h2
  have hdvdN : m ∣ 2 := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using this
  have := Nat.le_of_dvd (by norm_num) hdvdN
  omega

/-- `w (k+1)` is the right or the upper neighbour of `w k`. -/
def IsRightOrUp (w : ℤ → ℤ × ℤ) (k : ℤ) : Prop :=
  w (k + 1) = ((w k).1 + 1, (w k).2) ∨ w (k + 1) = ((w k).1, (w k).2 + 1)

/-- The edge of the walk at index `k`, oriented as an up/right unit step. -/
def ori (w : ℤ → ℤ × ℤ) (k : ℤ) : (ℤ × ℤ) × (ℤ × ℤ) := by
  classical
  exact if IsRightOrUp w k then (w k, w (k + 1)) else (w (k + 1), w k)

/-- The canonical up/right orientation of an edge of a unit-step walk. -/
lemma ori_snd {w : ℤ → ℤ × ℤ}
    (hclass : ∀ k : ℤ, w (k + 1) = ((w k).1 + 1, (w k).2) ∨ w (k + 1) = ((w k).1 - 1, (w k).2) ∨
      w (k + 1) = ((w k).1, (w k).2 + 1) ∨ w (k + 1) = ((w k).1, (w k).2 - 1)) (k : ℤ) :
    (ori w k).2 = ((ori w k).1.1, (ori w k).1.2 + 1) ∨
      (ori w k).2 = ((ori w k).1.1 + 1, (ori w k).1.2) := by
  unfold ori
  by_cases h : IsRightOrUp w k
  · rw [if_pos h]
    rcases h with h | h
    · right; rw [h]
    · left; rw [h]
  · rw [if_neg h]
    rcases hclass k with hc | hc | hc | hc
    · exact absurd (Or.inl hc) h
    · right; rw [hc]; simp
    · exact absurd (Or.inr hc) h
    · left; rw [hc]; simp

lemma ori_seg {w : ℤ → ℤ × ℤ} (k : ℤ) :
    segment ℝ (Commons.Topology.Plane.pc (ori w k).1) (Commons.Topology.Plane.pc (ori w k).2) =
      segment ℝ (Commons.Topology.Plane.pc (w k)) (Commons.Topology.Plane.pc (w (k + 1))) := by
  unfold ori
  by_cases h : IsRightOrUp w k
  · rw [if_pos h]
  · rw [if_neg h]
    exact segment_symm ℝ _ _

lemma ori_pts (w : ℤ → ℤ × ℤ) (k : ℤ) :
    ({Commons.Topology.Plane.pc (ori w k).1, Commons.Topology.Plane.pc (ori w k).2} : Set ℂ) =
      {Commons.Topology.Plane.pc (w k), Commons.Topology.Plane.pc (w (k + 1))} := by
  unfold ori
  by_cases h : IsRightOrUp w k
  · rw [if_pos h]
  · rw [if_neg h, Set.pair_comm]

lemma ori_ne {w : ℤ → ℤ × ℤ} {i j : ℤ}
    (hne : ¬(w i = w j ∧ w (i + 1) = w (j + 1)) ∧ ¬(w i = w (j + 1) ∧ w (i + 1) = w j)) :
    ¬((ori w i).1 = (ori w j).1 ∧ (ori w i).2 = (ori w j).2) := by
  intro hc
  obtain ⟨hc1, hc2⟩ := hc
  simp only [ori] at hc1 hc2
  split_ifs at hc1 hc2 with h1 h2
  · exact hne.1 ⟨hc1, hc2⟩
  · exact hne.2 ⟨hc1, hc2⟩
  · exact hne.2 ⟨hc2, hc1⟩
  · exact hne.1 ⟨hc2, hc1⟩

/-- Two distinct unit lattice edges of a walk meet only in common endpoints. -/
lemma edge_meet {w : ℤ → ℤ × ℤ}
    (hclass : ∀ k : ℤ, w (k + 1) = ((w k).1 + 1, (w k).2) ∨ w (k + 1) = ((w k).1 - 1, (w k).2) ∨
      w (k + 1) = ((w k).1, (w k).2 + 1) ∨ w (k + 1) = ((w k).1, (w k).2 - 1)) {i j : ℤ}
    (hne : ¬(w i = w j ∧ w (i + 1) = w (j + 1)) ∧ ¬(w i = w (j + 1) ∧ w (i + 1) = w j)) :
    segment ℝ (Commons.Topology.Plane.pc (w i)) (Commons.Topology.Plane.pc (w (i + 1))) ∩
        segment ℝ (Commons.Topology.Plane.pc (w j)) (Commons.Topology.Plane.pc (w (j + 1))) ⊆
      ({Commons.Topology.Plane.pc (w i), Commons.Topology.Plane.pc (w (i + 1))} : Set ℂ) ∩
        ({Commons.Topology.Plane.pc (w j), Commons.Topology.Plane.pc (w (j + 1))} : Set ℂ) := by
  have h := Commons.Topology.Plane.unit_segment_meet (u := (ori w i).1) (v := (ori w i).2)
    (u' := (ori w j).1) (v' := (ori w j).2) (ori_snd hclass i) (ori_snd hclass j)
    (ori_ne hne)
  simpa only [← ori_seg (w := w) i, ← ori_seg (w := w) j, ori_pts w i, ori_pts w j] using h


/-- **Simplicity of the interpolant.**  If the unit-step lattice walk `w` is `m`-periodic and
injective on one period `{0, …, m-1}` with `m > 2`, then its linear interpolant is injective on
`[0, m)`. -/
lemma walkInterp_injOn {w : ℤ → ℤ × ℤ} {m : ℕ} (hm : 2 < m)
    (hper : ∀ k : ℤ, w (k + (m : ℤ)) = w k)
    (hstep : ∀ k : ℤ, w (k + 1) ≠ w k ∧
      ((w (k + 1)).1 - (w k).1) ^ 2 + ((w (k + 1)).2 - (w k).2) ^ 2 = 1)
    (hinj : Set.InjOn w (Set.Ico (0 : ℤ) (m : ℤ))) :
    Set.InjOn (walkInterp w) (Set.Ico (0 : ℝ) (m : ℝ)) := by
  classical
  have hm0 : 0 < m := by omega
  have hmod : ∀ i j : ℤ, w i = w j → i % m = j % m :=
    fun i j h => (w_eq_iff_emod hm0 hper hinj i j).mp h
  have hclass : ∀ k : ℤ, w (k + 1) = ((w k).1 + 1, (w k).2) ∨
      w (k + 1) = ((w k).1 - 1, (w k).2) ∨
      w (k + 1) = ((w k).1, (w k).2 + 1) ∨ w (k + 1) = ((w k).1, (w k).2 - 1) :=
    fun k => step_classification hstep k
  have hA : ∀ k : ℤ, (fun k => Commons.Topology.Plane.pc (w k)) k
      ≠ (fun k => Commons.Topology.Plane.pc (w k)) (k + 1) :=
    fun k hc => (hstep k).1 (Commons.Topology.Plane.pc_injective hc).symm
  have key : ∀ x ∈ Set.Ico (0:ℝ) (m:ℝ), ∀ y ∈ Set.Ico (0:ℝ) (m:ℝ), x < y →
      walkInterp w x ≠ walkInterp w y := by
    intro x hx y hy hxy_lt hxy
    set p : ℤ := ⌊x⌋ with hp
    set q : ℤ := ⌊y⌋ with hq
    have hxIco : x ∈ Set.Ico (p : ℝ) ((p : ℝ) + 1) :=
      ⟨by rw [hp]; exact Int.floor_le x, by rw [hp]; exact Int.lt_floor_add_one x⟩
    have hyIco : y ∈ Set.Ico (q : ℝ) ((q : ℝ) + 1) :=
      ⟨by rw [hq]; exact Int.floor_le y, by rw [hq]; exact Int.lt_floor_add_one y⟩
    have hp0 : 0 ≤ p := by
      rw [hp, ← Int.floor_zero (R := ℝ)]
      exact Int.floor_mono hx.1
    have hpm : p < (m : ℤ) := by
      rw [hp]
      have h1 : (⌊x⌋ : ℝ) < (m : ℝ) := lt_of_le_of_lt (Int.floor_le x) hx.2
      exact_mod_cast h1
    have hq0 : 0 ≤ q := by
      rw [hq, ← Int.floor_zero (R := ℝ)]
      exact Int.floor_mono hy.1
    have hqm : q < (m : ℤ) := by
      rw [hq]
      have h1 : (⌊y⌋ : ℝ) < (m : ℝ) := lt_of_le_of_lt (Int.floor_le y) hy.2
      exact_mod_cast h1
    have hpq : p ≤ q := by rw [hp, hq]; exact Int.floor_mono (le_of_lt hxy_lt)
    have hz1 : walkInterp w x ∈
        segment ℝ (Commons.Topology.Plane.pc (w p)) (Commons.Topology.Plane.pc (w (p + 1))) := by
      have h1 : walkInterp w x = latSeg (fun k => Commons.Topology.Plane.pc (w k)) p x :=
        floorInterp_eq_latSeg hxIco
      rw [h1]
      exact latSeg_mem_segment (fun k => Commons.Topology.Plane.pc (w k)) ⟨hxIco.1, hxIco.2.le⟩
    have hz2 : walkInterp w y ∈
        segment ℝ (Commons.Topology.Plane.pc (w q)) (Commons.Topology.Plane.pc (w (q + 1))) := by
      have h1 : walkInterp w y = latSeg (fun k => Commons.Topology.Plane.pc (w k)) q y :=
        floorInterp_eq_latSeg hyIco
      rw [h1]
      exact latSeg_mem_segment (fun k => Commons.Topology.Plane.pc (w k)) ⟨hyIco.1, hyIco.2.le⟩
    rcases eq_or_lt_of_le hpq with hpq_eq | hpq_lt
    · -- same unit interval
      have hyIco' : y ∈ Set.Ico (p : ℝ) ((p : ℝ) + 1) := by
        have h := hyIco
        rw [← hpq_eq] at h
        exact h
      have h1 : walkInterp w x = latSeg (fun k => Commons.Topology.Plane.pc (w k)) p x :=
        floorInterp_eq_latSeg hxIco
      have h2 : walkInterp w y = latSeg (fun k => Commons.Topology.Plane.pc (w k)) p y :=
        floorInterp_eq_latSeg hyIco'
      have hxy' : x = y := latSeg_injective _ (hA p) (by rw [← h1, ← h2]; exact hxy)
      exact absurd hxy' (ne_of_lt hxy_lt)
    · rcases lt_or_eq_of_le (show p + 1 ≤ q by omega) with hq_lt | hq_eq
      · -- non-adjacent edges
        have hne : ¬(w p = w q ∧ w (p + 1) = w (q + 1)) ∧ ¬(w p = w (q + 1) ∧ w (p + 1) = w q) := by
          constructor
          · rintro ⟨h1, h2⟩
            have hm' := hmod p q h1
            rw [Int.emod_eq_of_lt hp0 hpm, Int.emod_eq_of_lt hq0 hqm] at hm'
            omega
          · rintro ⟨h1, h2⟩
            have hm' := hmod (p + 1) q h2
            rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt hq0 hqm] at hm'
            omega
        have hsub := edge_meet hclass hne
        have hz0 : walkInterp w x ∈
            segment ℝ (Commons.Topology.Plane.pc (w p)) (Commons.Topology.Plane.pc (w (p + 1))) ∩
              segment ℝ (Commons.Topology.Plane.pc (w q)) (Commons.Topology.Plane.pc (w (q + 1))) :=
          ⟨hz1, hxy ▸ hz2⟩
        have hz := hsub hz0
        have hq_eqle : q + 1 ≤ (m : ℤ) := by omega
        rcases hz.1 with h1 | h1 <;> rcases hz.2 with h2 | h2
        · -- (p, q)
          have hm' := hmod p q (Commons.Topology.Plane.pc_injective (h1.symm.trans h2))
          rw [Int.emod_eq_of_lt hp0 hpm, Int.emod_eq_of_lt hq0 hqm] at hm'
          omega
        · -- (p, q+1)
          have hm' := hmod p (q + 1) (Commons.Topology.Plane.pc_injective (h1.symm.trans h2))
          rw [Int.emod_eq_of_lt hp0 hpm] at hm'
          rcases lt_or_eq_of_le hq_eqle with hlt | heq
          · rw [Int.emod_eq_of_lt (by omega) hlt] at hm'
            omega
          · -- wrapping case: p = 0 and q + 1 = m
            have hyval : latSeg (fun k => Commons.Topology.Plane.pc (w k)) q y
                = Commons.Topology.Plane.pc (w (q + 1)) := by
              rw [← floorInterp_eq_latSeg hyIco]
              change walkInterp w y = Commons.Topology.Plane.pc (w (q + 1))
              rw [← hxy, h2]
            have hyq : y = (q : ℝ) + 1 :=
              latSeg_injective _ (hA q) (by rw [latSeg_right]; exact hyval)
            have hym : y = (m : ℝ) := by
              have h1 : (q : ℝ) + 1 = ((q + 1 : ℤ) : ℝ) := by push_cast; ring
              have h2 : ((q + 1 : ℤ) : ℝ) = (m : ℝ) := by exact_mod_cast heq
              rw [hyq, h1, h2]
            rw [hym] at hy
            exact absurd hy.2 (lt_irrefl _)
        · -- (p+1, q)
          have hm' := hmod (p + 1) q (Commons.Topology.Plane.pc_injective (h1.symm.trans h2))
          rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt hq0 hqm] at hm'
          omega
        · -- (p+1, q+1)
          have hm' := hmod (p + 1) (q + 1) (Commons.Topology.Plane.pc_injective (h1.symm.trans h2))
          rw [Int.emod_eq_of_lt (by omega) (by omega)] at hm'
          rcases lt_or_eq_of_le hq_eqle with hlt | heq
          · rw [Int.emod_eq_of_lt (by omega) hlt] at hm'
            omega
          · rw [heq, Int.emod_self] at hm'
            omega
      · -- adjacent edges
        have hne : ¬(w p = w q ∧ w (p + 1) = w (q + 1)) ∧ ¬(w p = w (q + 1) ∧ w (p + 1) = w q) := by
          constructor
          · rintro ⟨h1, h2⟩
            have hm' := hmod p q h1
            rw [Int.emod_eq_of_lt hp0 hpm, Int.emod_eq_of_lt hq0 hqm] at hm'
            omega
          · rintro ⟨h1, h2⟩
            have h1' : w p = w (p + 2) := by
              rw [← hq_eq] at h1
              have hh := h1
              rwa [show p + 1 + 1 = p + 2 by ring] at hh
            exact w_ne_add_two hm hper hinj p h1'.symm
        have hsub := edge_meet hclass hne
        have hz0 : walkInterp w x ∈
            segment ℝ (Commons.Topology.Plane.pc (w p)) (Commons.Topology.Plane.pc (w (p + 1))) ∩
              segment ℝ (Commons.Topology.Plane.pc (w q)) (Commons.Topology.Plane.pc (w (q + 1))) :=
          ⟨hz1, hxy ▸ hz2⟩
        have hz := hsub hz0
        have hzq : walkInterp w x = Commons.Topology.Plane.pc (w q) := by
          rcases hz.1 with h1 | h1 <;> rcases hz.2 with h2 | h2
          · have hm' := hmod p q (Commons.Topology.Plane.pc_injective (h1.symm.trans h2))
            rw [Int.emod_eq_of_lt hp0 hpm, Int.emod_eq_of_lt hq0 hqm] at hm'
            omega
          · have h1' : w p = w (p + 2) := by
              rw [← hq_eq] at h2
              have hh := Commons.Topology.Plane.pc_injective (h1.symm.trans h2)
              rwa [show p + 1 + 1 = p + 2 by ring] at hh
            exact absurd (w_ne_add_two hm hper hinj p h1'.symm) (by simp)
          · exact h2
          · rw [hq_eq] at h1; exact h1
        have hxval : latSeg (fun k => Commons.Topology.Plane.pc (w k)) p x
            = Commons.Topology.Plane.pc (w (p + 1)) := by
          rw [← floorInterp_eq_latSeg hxIco]
          change walkInterp w x = Commons.Topology.Plane.pc (w (p + 1))
          rw [hzq, ← hq_eq]
        have hxeq : x = (p : ℝ) + 1 :=
          latSeg_injective _ (hA p) (by rw [latSeg_right]; exact hxval)
        have hyval : latSeg (fun k => Commons.Topology.Plane.pc (w k)) q y
            = Commons.Topology.Plane.pc (w q) := by
          rw [← floorInterp_eq_latSeg hyIco]
          change walkInterp w y = Commons.Topology.Plane.pc (w q)
          rw [← hxy, hzq]
        have hyeq : y = (q : ℝ) :=
          latSeg_injective _ (hA q) (by rw [latSeg_left]; exact hyval)
        have hcast1 : ((p : ℝ) + 1) = ((q : ℤ) : ℝ) := by rw [← hq_eq]; push_cast; ring
        rw [hxeq, hyeq, hcast1] at hxy_lt
        exact absurd hxy_lt (lt_irrefl _)
  intro x hx y hy hxy
  rcases lt_trichotomy x y with h | h | h
  · exact absurd hxy (key x hx y hy h)
  · exact h
  · exact absurd hxy.symm (key y hy x hx h)
/-- The image of the interpolant of a lattice walk is the union of its edges. -/
lemma range_walkInterp (w : ℤ → ℤ × ℤ) :
    Set.range (walkInterp w) =
      ⋃ k : ℤ, segment ℝ (Commons.Topology.Plane.pc (w k)) (Commons.Topology.Plane.pc (w (k + 1))) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact mem_iUnion.mpr ⟨⌊x⌋,
      floorInterp_mem_segment (fun k => Commons.Topology.Plane.pc (w k)) x⟩
  · intro hz
    rcases mem_iUnion.mp hz with ⟨k, hk⟩
    rw [segment_eq_image] at hk
    rcases hk with ⟨t, ht, rfl⟩
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · refine ⟨(k : ℝ) + t, ?_⟩
      rw [show walkInterp w ((k : ℝ) + t)
          = latSeg (fun k => Commons.Topology.Plane.pc (w k)) k ((k : ℝ) + t) from
        floorInterp_eq_latSeg ⟨by linarith [ht.1], by linarith [hlt]⟩]
      unfold latSeg
      rw [add_sub_cancel_left]
      simp only [sub_smul, one_smul, smul_sub]
      abel
    · subst heq
      refine ⟨(k : ℝ) + 1, ?_⟩
      rw [show (k : ℝ) + 1 = ((k + 1 : ℤ) : ℝ) by push_cast; ring, walkInterp_intCast]
      simp

/-- **Pannwitz–Kuperberg (lattice case)**: a simple closed unit-step lattice polygon has a bounded
complementary component. -/
theorem bounded_component_of_lattice_polygon (w : ℤ → ℤ × ℤ) (m : ℕ) (hm : 2 < m)
    (hper : ∀ k : ℤ, w (k + (m : ℤ)) = w k)
    (hstep : ∀ k : ℤ, w (k + 1) ≠ w k ∧
      ((w (k + 1)).1 - (w k).1) ^ 2 + ((w (k + 1)).2 - (w k).2) ^ 2 = 1)
    (hinj : Set.InjOn w (Set.Ico (0 : ℤ) (m : ℤ))) :
    ∃ z : ℂ,
      z ∉ ⋃ k : ℤ, segment ℝ (Commons.Topology.Plane.pc (w k)) (Commons.Topology.Plane.pc (w (k + 1))) ∧
      Bornology.IsBounded (connectedComponentIn
        (⋃ k : ℤ, segment ℝ (Commons.Topology.Plane.pc (w k)) (Commons.Topology.Plane.pc (w (k + 1))))ᶜ z) := by
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  set γ : ℝ → ℂ := fun x => walkInterp w ((m : ℝ) * x) with hγ
  have hγcont : Continuous γ := by
    rw [hγ]
    exact (continuous_walkInterp w).comp (continuous_const.mul continuous_id)
  have hγper : Function.Periodic γ 1 := by
    intro x
    change walkInterp w ((m : ℝ) * (x + 1)) = walkInterp w ((m : ℝ) * x)
    rw [show (m : ℝ) * (x + 1) = (m : ℝ) * x + ((m : ℤ) : ℝ) by push_cast; ring]
    exact walkInterp_periodic_int w (m : ℤ) hper ((m : ℝ) * x)
  have hγinj : Set.InjOn γ (Set.Ico (0 : ℝ) 1) := by
    intro x hx y hy hxy
    have hxI : (m : ℝ) * x ∈ Set.Ico (0 : ℝ) (m : ℝ) :=
      ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩
    have hyI : (m : ℝ) * y ∈ Set.Ico (0 : ℝ) (m : ℝ) :=
      ⟨by nlinarith [hy.1], by nlinarith [hy.2]⟩
    have hxy' : walkInterp w ((m : ℝ) * x) = walkInterp w ((m : ℝ) * y) := hxy
    exact mul_left_cancel₀ (ne_of_gt hmR) (walkInterp_injOn hm hper hstep hinj hxI hyI hxy')
  obtain ⟨U, V, hUo, hVo, hUc, hVc, hdisj, hUb, hVb, hUV⟩ :=
    separation_of_periodic_embedding γ hγcont hγper hγinj
  have hrange : Set.range γ =
      ⋃ k : ℤ, segment ℝ (Commons.Topology.Plane.pc (w k)) (Commons.Topology.Plane.pc (w (k + 1))) := by
    rw [hγ]
    rw [show (fun x : ℝ => walkInterp w ((m : ℝ) * x))
        = walkInterp w ∘ (fun x : ℝ => (m : ℝ) * x) from rfl]
    rw [Set.range_comp]
    have hsurj : Set.range (fun x : ℝ => (m : ℝ) * x) = Set.univ := by
      rw [Set.range_eq_univ]
      intro y
      refine ⟨y / (m : ℝ), ?_⟩
      change (m : ℝ) * (y / (m : ℝ)) = y
      rw [mul_comm]
      exact div_mul_cancel₀ y (ne_of_gt hmR)
    rw [hsurj, Set.image_univ]
    exact range_walkInterp w
  obtain ⟨z, hzU⟩ := hUc.nonempty
  have hzKc : z ∈ (Set.range γ)ᶜ := by rw [← hUV]; exact Or.inl hzU
  refine ⟨z, ?_, ?_⟩
  · rwa [hrange] at hzKc
  · have hCU : connectedComponentIn ((Set.range γ)ᶜ) z ⊆ U := by
      have hpre : IsPreconnected (connectedComponentIn ((Set.range γ)ᶜ) z) :=
        isPreconnected_connectedComponentIn
      have hsub : connectedComponentIn ((Set.range γ)ᶜ) z ⊆ U ∪ V :=
        (connectedComponentIn_subset _ _).trans (le_of_eq hUV.symm)
      rcases hpre.subset_or_subset hUo hVo hdisj hsub with h | h
      · exact h
      · exfalso
        exact (Set.disjoint_left.mp hdisj hzU) (h (mem_connectedComponentIn hzKc))
    have hbdd : Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) z) := hUb.subset hCU
    rwa [← hrange]
end Commons.Topology.Jordan
