import Mathlib
import Submission.Work.Shrinking.PCentral
import Submission.Work.SSGRoute.prop5.pow_mem_pCentralSeries
import Submission.Work.SSGRoute.prop5.mul_pow_mem_lowerCentralSeries
import Submission.Work.SSGRoute.prop5.commutator_lowerCentralSeries_le
import Submission.Work.SSGRoute.prop5.wtFiltration
import Submission.Work.SSGRoute.prop5.magnus_unitCongr_isolated
import Submission.Work.SSGRoute.prop5.adjacent.magnus_kernel_detects
import Submission.Work.SSGRoute.prop5.adjacent.magnus_image_saturated
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped commutatorElement

set_option maxHeartbeats 4000000

namespace Work.SSGRoute.prop5

universe u

noncomputable section

/-- The image of the `p`-adic weight filtration piece (`Work.SSGRoute.prop5.wtIdeal`) in the
truncated free associative algebra `FreeAssoc X ⧸ fil X N`. -/
def wtq (p : ℕ) (X : Type*) (N n : ℕ) : Ideal (FreeAssoc X ⧸ fil X N) :=
  Ideal.map (Ideal.Quotient.mk (fil X N)) (wtIdeal p X n)

instance wtIdeal_isTwoSided (p : ℕ) (X : Type*) (n : ℕ) : (wtIdeal p X n).IsTwoSided :=
  ⟨fun b ha => mul_mem_wtz' p n b ha⟩

instance wtq_isTwoSided (p : ℕ) (X : Type*) (N n : ℕ) : (wtq p X N n).IsTwoSided :=
  ⟨fun b ha => by
    obtain ⟨a', ha', rfl⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (fil X N))
      Ideal.Quotient.mk_surjective).1 ha
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul]
    exact Ideal.mem_map_of_mem _ (Ideal.mul_mem_right b' (wtIdeal p X n) ha')⟩

/-- `wtq` is decreasing in the weight. -/
theorem wtq_le (p : ℕ) (X : Type*) (N : ℕ) : Antitone (wtq p X N) :=
  fun _ _ hnm => Ideal.map_mono (wtIdeal_le p X hnm)

/-- The product of two weight pieces lands in the weight piece of the sum of the weights. -/
theorem wtq_mul_mem (p : ℕ) (X : Type*) (N n m : ℕ) {a b : FreeAssoc X ⧸ fil X N}
    (ha : a ∈ wtq p X N n) (hb : b ∈ wtq p X N m) : a * b ∈ wtq p X N (n + m) := by
  obtain ⟨a', ha', rfl⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (fil X N))
    Ideal.Quotient.mk_surjective).1 ha
  obtain ⟨b', hb', rfl⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (fil X N))
    Ideal.Quotient.mk_surjective).1 hb
  rw [← map_mul]
  exact Ideal.mem_map_of_mem _ (wtIdeal_mul_le p X n m (Ideal.mul_mem_mul ha' hb'))

/-- `p` times a weight-`n` piece lies in the weight-`(n+1)` piece. -/
theorem wtq_smul_p (p : ℕ) (X : Type*) (N n : ℕ) {a : FreeAssoc X ⧸ fil X N}
    (ha : a ∈ wtq p X N n) : (p : ℤ) • a ∈ wtq p X N (n + 1) := by
  obtain ⟨a', ha', rfl⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (fil X N))
    Ideal.Quotient.mk_surjective).1 ha
  rw [← map_zsmul]
  refine Ideal.mem_map_of_mem _ ?_
  show (p : ℤ) • a' ∈ wtz p X (n + 1)
  refine Submodule.span_induction (p := fun a _ => (p : ℤ) • a ∈ wtz p X (n + 1))
    (fun a ha => ?_) (Submodule.zero_mem _) (fun a b _ _ ha hb => ?_) (fun c a _ ha => ?_)
    (show a' ∈ wtz p X n from ha')
  · obtain ⟨w, e, hw, hwe, rfl⟩ := ha
    rw [show (p : ℤ) • MonoidAlgebra.single w ((p : ℤ) ^ e)
        = MonoidAlgebra.single w ((p : ℤ) ^ (e + 1)) from by
      rw [MonoidAlgebra.smul_single', ← pow_succ']]
    exact single_mem_wtz (p := p) hw (by omega)
  · rw [smul_add]; exact Submodule.add_mem _ ha hb
  · rw [smul_comm]; exact Submodule.smul_mem _ c ha

/-- Units of the truncated algebra which are `≡ 1` modulo the weight piece `wtq p X N n`. -/
def wtUnit (p : ℕ) (X : Type*) (N n : ℕ) : Subgroup (FreeAssoc X ⧸ fil X N)ˣ where
  carrier := {u | ((u : FreeAssoc X ⧸ fil X N) - 1) ∈ wtq p X N n}
  mul_mem' := by
    intro u v hu hv
    change ((↑(u * v) : FreeAssoc X ⧸ fil X N) - 1) ∈ wtq p X N n
    have h : (↑(u * v) : FreeAssoc X ⧸ fil X N) - 1
        = (↑u : FreeAssoc X ⧸ fil X N) * ((↑v : FreeAssoc X ⧸ fil X N) - 1)
          + ((↑u : FreeAssoc X ⧸ fil X N) - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [h]
    exact Submodule.add_mem _ (Ideal.mul_mem_left _ _ hv) hu
  one_mem' := by
    change ((↑(1 : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1) ∈ wtq p X N n
    rw [Units.val_one]; simp
  inv_mem' := by
    intro u hu
    change ((↑(u⁻¹) : FreeAssoc X ⧸ fil X N) - 1) ∈ wtq p X N n
    have h1 : (↑(u⁻¹) : FreeAssoc X ⧸ fil X N) * ↑u = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h : (↑(u⁻¹) : FreeAssoc X ⧸ fil X N) - 1
        = - ((↑(u⁻¹) : FreeAssoc X ⧸ fil X N) * ((↑u : FreeAssoc X ⧸ fil X N) - 1)) := by
      rw [mul_sub, h1, mul_one, neg_sub]
    rw [h]
    exact neg_mem (Ideal.mul_mem_left _ _ hu)

/-- `(1 + x) ^ m - 1 - m x` lies in the weight piece of doubled weight, for `x` of weight `n ≥ 1`.
Modulo the doubled weight piece, `x` has square zero, so `(1 + x)^m ≡ 1 + m x`. -/
theorem one_add_pow_sub_mem (p : ℕ) (X : Type*) (N n m : ℕ) (hn : 1 ≤ n)
    {x : FreeAssoc X ⧸ fil X N} (hx : x ∈ wtq p X N n) :
    (1 + x) ^ m - 1 - (m : ℤ) • x ∈ wtq p X N (2 * n) := by
  have hx2 : x * x ∈ wtq p X N (2 * n) := by
    have h := wtq_mul_mem p X N n n hx hx
    rwa [show n + n = 2 * n from by ring] at h
  have h0 : (Ideal.Quotient.mk (wtq p X N (2 * n))) ((1 + x) ^ m - 1 - (m : ℤ) • x) = 0 := by
    rw [map_sub, map_sub, map_pow, map_add, map_one, map_zsmul]
    have hxx : (Ideal.Quotient.mk (wtq p X N (2 * n)) x) *
        (Ideal.Quotient.mk (wtq p X N (2 * n)) x) = 0 := by
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact hx2
    rw [one_add_pow_eq_of_sq_zero (Ideal.Quotient.mk (wtq p X N (2 * n)) x) hxx m]
    simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_natCast]
    abel
  rwa [Ideal.Quotient.eq_zero_iff_mem] at h0

/-- The `p`-th power of a unit congruent to `1` modulo the weight-`n` piece is congruent to `1`
modulo the weight-`(n+1)` piece. -/
theorem wtUnit_pow_mem (p : ℕ) (X : Type*) (N n : ℕ) (hn : 1 ≤ n)
    {u : (FreeAssoc X ⧸ fil X N)ˣ} (hu : u ∈ wtUnit p X N n) : u ^ p ∈ wtUnit p X N (n + 1) := by
  set x : FreeAssoc X ⧸ fil X N := ((u : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1
    with hx
  have hxmem : x ∈ wtq p X N n := hu
  have hmain : (1 + x) ^ p - 1 - (p : ℤ) • x ∈ wtq p X N (2 * n) :=
    one_add_pow_sub_mem p X N n p hn hxmem
  have hpx : (p : ℤ) • x ∈ wtq p X N (n + 1) := wtq_smul_p p X N n hxmem
  have hle : wtq p X N (2 * n) ≤ wtq p X N (n + 1) := wtq_le p X N (by omega)
  have hsum : ((1 + x) ^ p - 1 - (p : ℤ) • x) + (p : ℤ) • x ∈ wtq p X N (n + 1) :=
    Submodule.add_mem _ (hle hmain) hpx
  have hux : ((u : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) = 1 + x := by
    rw [hx]; abel
  change (((u ^ p : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1) ∈ wtq p X N (n + 1)
  rw [Units.val_pow_eq_pow_val, hux]
  have heq : (1 + x) ^ p - 1 = ((1 + x) ^ p - 1 - (p : ℤ) • x) + (p : ℤ) • x := by abel
  rw [heq]
  exact hsum

/-- The commutator of a unit congruent to `1` modulo the weight-`n` piece with a unit congruent to
`1` modulo the weight-`1` piece lands in the weight-`(n+1)` piece. -/
theorem wtUnit_commutator_le (p : ℕ) (X : Type*) (N n : ℕ) :
    ⁅wtUnit p X N n, wtUnit p X N 1⁆ ≤ wtUnit p X N (n + 1) := by
  rw [Subgroup.commutator_le]
  intro u hu v hv
  change ((↑(⁅u, v⁆) : FreeAssoc X ⧸ fil X N) - 1) ∈ wtq p X N (n + 1)
  have key : (↑u : FreeAssoc X ⧸ fil X N) * ↑v - ↑v * ↑u =
      ((↑u : FreeAssoc X ⧸ fil X N) - 1) * ((↑v : FreeAssoc X ⧸ fil X N) - 1)
        - ((↑v : FreeAssoc X ⧸ fil X N) - 1) * ((↑u : FreeAssoc X ⧸ fil X N) - 1) := by
    noncomm_ring
  have hcomm : ((↑(⁅u, v⁆) : FreeAssoc X ⧸ fil X N)) - 1 =
      (((↑u : FreeAssoc X ⧸ fil X N) - 1) * ((↑v : FreeAssoc X ⧸ fil X N) - 1)
        - ((↑v : FreeAssoc X ⧸ fil X N) - 1) * ((↑u : FreeAssoc X ⧸ fil X N) - 1)) *
        ((↑(u⁻¹) : FreeAssoc X ⧸ fil X N) * ↑(v⁻¹)) := by
    rw [← key, sub_mul, commutatorElement_def]
    simp only [Units.val_mul, mul_assoc]
    have h3 : (↑v : FreeAssoc X ⧸ fil X N) *
        ((↑u : FreeAssoc X ⧸ fil X N) * (↑(u⁻¹) * ↑(v⁻¹))) = 1 := by
      rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
      simp
    rw [h3]
  rw [hcomm]
  have hmem : ((↑u : FreeAssoc X ⧸ fil X N) - 1) * ((↑v : FreeAssoc X ⧸ fil X N) - 1)
      - ((↑v : FreeAssoc X ⧸ fil X N) - 1) * ((↑u : FreeAssoc X ⧸ fil X N) - 1)
      ∈ wtq p X N (n + 1) := by
    have h1 : ((↑u : FreeAssoc X ⧸ fil X N) - 1) * ((↑v : FreeAssoc X ⧸ fil X N) - 1)
        ∈ wtq p X N (n + 1) := wtq_mul_mem p X N n 1 hu hv
    have h2 : ((↑v : FreeAssoc X ⧸ fil X N) - 1) * ((↑u : FreeAssoc X ⧸ fil X N) - 1)
        ∈ wtq p X N (1 + n) := wtq_mul_mem p X N 1 n hv hu
    rw [show 1 + n = n + 1 from by ring] at h2
    exact Submodule.sub_mem _ h1 h2
  exact Ideal.mul_mem_right _ (wtq p X N (n + 1)) hmem

/-- The Magnus image of the whole free group is congruent to `1` modulo the weight-`1` piece. -/
theorem magnus_le_wtUnit_one (p : ℕ) (X : Type*) (N : ℕ) :
    Subgroup.map (magnus X N) (⊤ : Subgroup (FreeGroup X)) ≤ wtUnit p X N 1 := by
  intro u hu
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hu
  exact Ideal.map_mono (fil_le_wtIdeal p X (le_refl 1))
    (map_magnus_le_unitCongr_one X N (Subgroup.mem_map_of_mem _ (Subgroup.mem_top y)))

/-- The Magnus image of the `n`-th term of the descending `p`-central series is congruent to `1`
modulo the weight-`(n+1)` piece. -/
theorem magnus_pCentralSeries_le_wtUnit (p : ℕ) (X : Type*) (N n : ℕ) :
    Subgroup.map (magnus X N) (Work.Shrinking.pCentralSeries p (FreeGroup X) n) ≤
      wtUnit p X N (n + 1) := by
  induction n with
  | zero =>
      rw [Work.Shrinking.pCentralSeries_zero]
      exact magnus_le_wtUnit_one p X N
  | succ n ih =>
      rw [Work.Shrinking.pCentralSeries_succ]
      unfold Work.Shrinking.pCentralStep
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rw [Work.Shrinking.powSubgroup, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
        rintro z ⟨h, hh, rfl⟩
        change magnus X N (h ^ p) ∈ wtUnit p X N (n + 1 + 1)
        rw [map_pow]
        exact wtUnit_pow_mem p X N (n + 1) (by omega) (ih (Subgroup.mem_map_of_mem _ hh))
      · rw [Subgroup.map_commutator]
        exact le_trans (Subgroup.commutator_mono ih (magnus_le_wtUnit_one p X N))
          (wtUnit_commutator_le p X N (n + 1))

/-- **The `p`-central series lies in the weight filtration.** -/
theorem mag_mem_wtq (p : ℕ) (X : Type*) (N n : ℕ) {x : FreeGroup X}
    (hx : x ∈ Work.Shrinking.pCentralSeries p (FreeGroup X) n) :
    ((magnus X N x : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1 ∈
      wtq p X N (n + 1) :=
  magnus_pCentralSeries_le_wtUnit p X N n (Subgroup.mem_map_of_mem _ hx)

/-- The length filtration is contained in the length-support submodule. -/
theorem fil_le_filz (X : Type*) (N : ℕ) : (fil X N : Set (FreeAssoc X)) ⊆ filz X N := by
  rw [fil_eq_filI]
  exact fun a ha => ha

/-- The length-support submodules are decreasing in the length. -/
theorem filz_antitone (X : Type*) : Antitone (filz X) := by
  intro m n hmn
  refine Submodule.span_mono ?_
  rintro a ⟨w, hw, rfl⟩
  exact ⟨w, le_trans hmn hw, rfl⟩

/-- `fil X j` is closed under integer multiples. -/
theorem int_smul_mem_fil (X : Type*) (j : ℕ) {f : FreeAssoc X} (hf : f ∈ fil X j) (c : ℤ) :
    c • f ∈ fil X j := by
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ hf

/-- The generator case of `wtz_succ_le`. -/
theorem wtz_succ_le_gen (p : ℕ) (X : Type*) (j : ℕ) {c : FreeAssoc X}
    (hc : c ∈ wtSet p X (j + 1)) :
    ∃ b ∈ wtz p X j, ∃ f ∈ fil X (j + 1), c = (p : ℤ) • b + f := by
  obtain ⟨w, e, hw, hwe, rfl⟩ := hc
  by_cases hle : w.length ≤ j
  · have he : 1 ≤ e := by omega
    refine ⟨MonoidAlgebra.single w ((p : ℤ) ^ (e - 1)), ?_, 0, ?_, ?_⟩
    · exact single_mem_wtz (p := p) hw (e := e - 1) (by omega)
    · exact (fil X (j + 1)).zero_mem
    · rw [add_zero]
      rw [show (p : ℤ) • MonoidAlgebra.single w ((p : ℤ) ^ (e - 1))
          = MonoidAlgebra.single w ((p : ℤ) ^ e) from by
        rw [MonoidAlgebra.smul_single', ← pow_succ', show e - 1 + 1 = e from by omega]]
  · have hl : j + 1 ≤ w.length := by omega
    refine ⟨0, ?_, MonoidAlgebra.single w ((p : ℤ) ^ e), ?_, ?_⟩
    · exact (wtz p X j).zero_mem
    · rw [show MonoidAlgebra.single w ((p : ℤ) ^ e)
          = ((p : ℤ) ^ e) • MonoidAlgebra.single w 1 from by
        rw [MonoidAlgebra.smul_single', mul_one]]
      exact int_smul_mem_fil X (j + 1) (Ideal.subset_span ⟨w, hl, rfl⟩) ((p : ℤ) ^ e)
    · rw [smul_zero, zero_add]

/-- Every weight-`(j+1)` element is, modulo `fil X (j+1)`, `p` times a weight-`j` element. -/
theorem wtz_succ_le (p : ℕ) (X : Type*) (j : ℕ) {a : FreeAssoc X} (ha : a ∈ wtz p X (j + 1)) :
    ∃ b ∈ wtz p X j, ∃ f ∈ fil X (j + 1), a = (p : ℤ) • b + f := by
  refine Submodule.span_induction (p := fun a _ => ∃ b ∈ wtz p X j, ∃ f ∈ fil X (j + 1),
      a = (p : ℤ) • b + f) ?_ ?_ ?_ ?_ ha
  · exact fun c hc => wtz_succ_le_gen p X j hc
  · refine ⟨0, ?_, 0, ?_, ?_⟩
    · exact (wtz p X j).zero_mem
    · exact (fil X (j + 1)).zero_mem
    · rw [smul_zero, zero_add]
  · intro x y hx hy hpx hpy
    obtain ⟨b1, hb1, f1, hf1, rfl⟩ := hpx
    obtain ⟨b2, hb2, f2, hf2, rfl⟩ := hpy
    exact ⟨b1 + b2, Submodule.add_mem _ hb1 hb2, f1 + f2, Ideal.add_mem _ hf1 hf2, by
      rw [smul_add]; abel⟩
  · intro c x hx hpx
    obtain ⟨b, hb, f, hf, rfl⟩ := hpx
    exact ⟨c • b, Submodule.smul_mem _ c hb, c • f, int_smul_mem_fil X (j + 1) hf c, by
      rw [smul_add, smul_comm]⟩

/-- For `a ∈ wtz p X (j+1)` whose words all have length `≥ j`, the weight-`j` remainder `b` of
`wtz_succ_le` can be chosen with words of length `≥ j` too. -/
theorem wtz_filz_exists (p : ℕ) (X : Type*) (j : ℕ) (hp : 0 < p) {a : FreeAssoc X}
    (ha : a ∈ wtz p X (j + 1)) (haf : a ∈ filz X j) :
    ∃ b ∈ filz X j, a - (p : ℤ) • b ∈ fil X (j + 1) := by
  obtain ⟨b, hb, f, hf, hbf⟩ := wtz_succ_le p X j ha
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hp)
  have hb' : b ∈ filz X j := by
    rw [mem_filz_iff] at haf ⊢
    intro w hw
    by_contra hlen
    have ha0 : a.coeff w = 0 := by
      by_contra hne
      exact absurd (haf w hne) (by omega)
    have hf0 : f.coeff w = 0 := by
      have hfz : f ∈ filz X (j + 1) := fil_le_filz X (j + 1) hf
      rw [mem_filz_iff] at hfz
      by_contra hne
      exact absurd (hfz w hne) (by omega)
    have hpb : ((p : ℤ) • b).coeff w = 0 := by
      have h := congrArg (fun z : FreeAssoc X => z.coeff w) hbf
      rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, ha0, hf0, add_zero] at h
      exact h.symm
    have hpb' : (p : ℤ) * b.coeff w = 0 := by
      rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul] at hpb
      exact hpb
    rcases mul_eq_zero.1 hpb' with h | h
    · exact absurd h hpz
    · exact hw h
  refine ⟨b, hb', ?_⟩
  rw [hbf, add_sub_cancel_left]
  exact hf

/-! ## Purity of the Magnus leading-term image

The remaining input of the Magnus route is the classical Magnus--Witt *direct summand* property:
the degree-`j` part of the free Lie ring is a saturated (pure) subgroup of the degree-`j` part of
the free associative algebra.  It is isolated here; in the workspace it is the node
`Work.SSGRoute.prop5.magnus_image_pure`. -/

alias magnus_image_saturated_local := Work.SSGRoute.prop5.adjacent.magnus_image_saturated


/-! ## The Magnus leading term on `γ_j` (self-contained copies)

These are the elementary facts about the leading term map `z ↦ magLT j z = magnus (j+1) z - 1`
used in the assembly below.  They are reproduced here (privately) so that the proof of the
adjacent case depends only on the free-group Magnus framework and on the two classical nodes
`adjacent.magnus_kernel_detects` and `adjacent.magnus_image_saturated`. -/

theorem adj_filq_self_eq_bot (Y : Type*) (N : ℕ) : filq Y N N = ⊥ := by
  rw [filq, Ideal.map_eq_bot_iff_le_ker]
  intro a ha
  rw [RingHom.mem_ker]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

theorem adj_mem_filq_self_eq_zero {Y : Type*} {N : ℕ} {x : FreeAssoc Y ⧸ fil Y N}
    (h : x ∈ filq Y N N) : x = 0 := by
  rw [adj_filq_self_eq_bot] at h
  exact h

theorem adj_mul_self_eq_zero_of_mem_filq (Y : Type*) (j : ℕ) (hj : 1 ≤ j)
    {x : FreeAssoc Y ⧸ fil Y (j + 1)} (hx : x ∈ filq Y (j + 1) j) : x * x = 0 :=
  adj_mem_filq_self_eq_zero (filq_antitone Y (j + 1) (by omega)
    (mul_mem_filq Y (j + 1) j j hx hx))

/-- The Magnus leading term of `z` in degree `j`. -/
def magLT (Y : Type*) (j : ℕ) (z : FreeGroup Y) : FreeAssoc Y ⧸ fil Y (j + 1) :=
  ((magnus Y (j + 1) z : (FreeAssoc Y ⧸ fil Y (j + 1))ˣ) : FreeAssoc Y ⧸ fil Y (j + 1)) - 1

theorem adj_magLT_one (Y : Type*) (j : ℕ) : magLT Y j 1 = 0 := by
  simp [magLT]

theorem adj_magLT_mem_filq (Y : Type*) (j : ℕ) (hj : 1 ≤ j) {z : FreeGroup Y}
    (hz : z ∈ (⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries (j - 1)) :
    magLT Y j z ∈ filq Y (j + 1) j := by
  have h := magnus_mem_one_add Y (j + 1) (j - 1) (by omega) z hz
  rwa [show j - 1 + 1 = j from by omega] at h

theorem adj_magLT_eq_zero_of_mem_succ (Y : Type*) (j : ℕ) {z : FreeGroup Y}
    (hz : z ∈ (⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries j) : magLT Y j z = 0 := by
  have h := magnus_mem_one_add Y (j + 1) j (by omega) z hz
  unfold magLT
  exact adj_mem_filq_self_eq_zero h

theorem adj_magLT_mul (Y : Type*) (j : ℕ) (hj : 1 ≤ j) {g h : FreeGroup Y}
    (hg : g ∈ (⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries (j - 1))
    (hh : h ∈ (⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries (j - 1)) :
    magLT Y j (g * h) = magLT Y j g + magLT Y j h := by
  have hsq : magLT Y j g * magLT Y j h = 0 :=
    adj_mem_filq_self_eq_zero (filq_antitone Y (j + 1) (by omega)
      (mul_mem_filq Y (j + 1) j j (adj_magLT_mem_filq Y j hj hg) (adj_magLT_mem_filq Y j hj hh)))
  have key : magLT Y j (g * h) = magLT Y j g + magLT Y j h + magLT Y j g * magLT Y j h := by
    unfold magLT
    rw [map_mul, Units.val_mul]
    noncomm_ring
  rw [key, hsq, add_zero]

theorem adj_magLT_inv (Y : Type*) (j : ℕ) (hj : 1 ≤ j) {w : FreeGroup Y}
    (hw : w ∈ (⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries (j - 1)) :
    magLT Y j w⁻¹ = -magLT Y j w := by
  have h1 : magLT Y j (w * w⁻¹) = 0 := by rw [mul_inv_cancel]; exact adj_magLT_one Y j
  have h2 := adj_magLT_mul Y j hj hw (Subgroup.inv_mem _ hw)
  rw [h1] at h2
  have h3 : magLT Y j w⁻¹ + magLT Y j w = 0 := by
    rw [add_comm (magLT Y j w⁻¹) (magLT Y j w)]
    exact h2.symm
  exact eq_neg_of_add_eq_zero_left h3

theorem adj_magLT_pow (Y : Type*) (j : ℕ) (hj : 1 ≤ j) (q : ℕ) {w : FreeGroup Y}
    (hw : w ∈ (⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries (j - 1)) :
    magLT Y j (w ^ q) = (q : ℤ) * magLT Y j w := by
  have hsq : magLT Y j w * magLT Y j w = 0 := adj_mul_self_eq_zero_of_mem_filq Y j hj
    (adj_magLT_mem_filq Y j hj hw)
  have key : magLT Y j (w ^ q) = (1 + magLT Y j w) ^ q - 1 := by
    unfold magLT
    rw [map_pow, Units.val_pow_eq_pow_val]
    rw [show (1 : FreeAssoc Y ⧸ fil Y (j + 1)) +
        (((magnus Y (j + 1) w : (FreeAssoc Y ⧸ fil Y (j + 1))ˣ) :
          FreeAssoc Y ⧸ fil Y (j + 1)) - 1)
        = ((magnus Y (j + 1) w : (FreeAssoc Y ⧸ fil Y (j + 1))ˣ) :
          FreeAssoc Y ⧸ fil Y (j + 1)) from by noncomm_ring]
  rw [key, one_add_pow_eq_of_sq_zero (magLT Y j w) hsq q, add_sub_cancel_left]
  exact nsmul_eq_mul q (magLT Y j w)

/-- **Assembly**: a `p`-divisible leading term of `z ∈ γ_j` forces `z ∈ ⟨γ_j^p⟩·γ_{j+1}`,
given that the Magnus map detects `γ_{j+1}` (`hkernel`) and that its image in degree `j` is
saturated (`hpure`). -/
theorem adj_magnus_leadingTerm_of_kernel_and_pure
    (hkernel : ∀ (Y : Type) (j : ℕ), 1 ≤ j →
      ∀ y ∈ (⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries (j - 1),
        ((magnus Y (j + 1) y : (FreeAssoc Y ⧸ fil Y (j + 1))ˣ) :
            FreeAssoc Y ⧸ fil Y (j + 1)) - 1 = 0 →
        y ∈ (⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries j)
    (hpure : ∀ (Y : Type) (n j : ℕ), 0 < n → 1 ≤ j →
      ∀ y ∈ (⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries (j - 1),
      ∀ x : FreeAssoc Y ⧸ fil Y (j + 1), x ∈ filq Y (j + 1) j →
        ((magnus Y (j + 1) y : (FreeAssoc Y ⧸ fil Y (j + 1))ˣ) :
            FreeAssoc Y ⧸ fil Y (j + 1)) - 1 = (n : ℤ) * x →
        ∃ w ∈ (⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries (j - 1),
          ((magnus Y (j + 1) w : (FreeAssoc Y ⧸ fil Y (j + 1))ˣ) :
              FreeAssoc Y ⧸ fil Y (j + 1)) - 1 = x)
    (q : ℕ) (hq : 0 < q) (Y : Type) (j : ℕ) (hj : 1 ≤ j) (z : FreeGroup Y)
    (hz : z ∈ (⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries (j - 1))
    (h : ∃ a : FreeAssoc Y ⧸ fil Y (j + 1),
          a ∈ Ideal.map (Ideal.Quotient.mk (fil Y (j + 1))) (fil Y j) ∧
          ((magnus Y (j + 1) z : (FreeAssoc Y ⧸ fil Y (j + 1))ˣ) :
              FreeAssoc Y ⧸ fil Y (j + 1)) - 1 = (q : ℤ) * a) :
    z ∈ Work.Shrinking.powSubgroup q ((⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries (j - 1))
        ⊔ (⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries j := by
  obtain ⟨a, ha_mem, ha_eq⟩ := h
  obtain ⟨w, hw_mem, hw_eq⟩ := hpure Y q j hq hj z hz a ha_mem ha_eq
  have hw' : w ^ q ∈ (⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries (j - 1) :=
    Subgroup.pow_mem _ hw_mem q
  have hz_eq : magLT Y j z = (q : ℤ) * a := ha_eq
  have hw_eq' : magLT Y j w = a := hw_eq
  have hwp : magLT Y j (w ^ q) = (q : ℤ) * a := by
    rw [adj_magLT_pow Y j hj q hw_mem, hw_eq']
  have hmem1 : z * (w ^ q)⁻¹ ∈ (⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries (j - 1) :=
    Subgroup.mul_mem _ hz (Subgroup.inv_mem _ hw')
  have hzero : magLT Y j (z * (w ^ q)⁻¹) = 0 := by
    rw [adj_magLT_mul Y j hj hz (Subgroup.inv_mem _ hw'), adj_magLT_inv Y j hj hw', hwp, hz_eq]
    exact add_neg_cancel _
  have hker := hkernel Y j hj (z * (w ^ q)⁻¹) hmem1 hzero
  have hdecomp : z = (z * (w ^ q)⁻¹) * (w ^ q) := by group
  rw [hdecomp]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_right hker) (Subgroup.mem_sup_left ?_)
  exact Subgroup.subset_closure ⟨w, hw_mem, rfl⟩

theorem adjacent_pSeries_inter_lcs_le (p : ℕ) [Fact p.Prime] (X : Type) [Fintype X]
    (j : ℕ) (hj : 1 ≤ j) :
    Work.Shrinking.pCentralSeries p (FreeGroup X) j ⊓
        (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) ≤
      Work.Shrinking.powSubgroup p ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) ⊔
        (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j := by
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxP, hxγ⟩ := hx
  have hkernel : ∀ (Y : Type) (j : ℕ), 1 ≤ j →
      ∀ y ∈ (⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries (j - 1),
        ((magnus Y (j + 1) y : (FreeAssoc Y ⧸ fil Y (j + 1))ˣ) :
            FreeAssoc Y ⧸ fil Y (j + 1)) - 1 = 0 →
        y ∈ (⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries j := by
    intro Y j' hj' y hy h
    have h' : ((magnus Y (j' + 1) y : (FreeAssoc Y ⧸ fil Y (j' + 1))ˣ) :
        FreeAssoc Y ⧸ fil Y (j' + 1)) - 1 ∈ filq Y (j' + 1) (j' - 1 + 2) := by
      rw [show j' - 1 + 2 = j' + 1 from by omega, h]
      exact (filq Y (j' + 1) (j' + 1)).zero_mem
    have hres := Work.SSGRoute.prop5.adjacent.magnus_kernel_detects Y (j' + 1) (j' - 1)
      (by omega) y hy h'
    rwa [Nat.sub_add_cancel hj'] at hres
  have hpure : ∀ (Y : Type) (n j : ℕ), 0 < n → 1 ≤ j →
      ∀ y ∈ (⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries (j - 1),
      ∀ x : FreeAssoc Y ⧸ fil Y (j + 1), x ∈ filq Y (j + 1) j →
        ((magnus Y (j + 1) y : (FreeAssoc Y ⧸ fil Y (j + 1))ˣ) :
            FreeAssoc Y ⧸ fil Y (j + 1)) - 1 = (n : ℤ) * x →
        ∃ w ∈ (⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries (j - 1),
          ((magnus Y (j + 1) w : (FreeAssoc Y ⧸ fil Y (j + 1))ˣ) :
              FreeAssoc Y ⧸ fil Y (j + 1)) - 1 = x :=
    fun Y n j' => magnus_image_saturated_local Y n j'
  have hdiv : ∃ a : FreeAssoc X ⧸ fil X (j + 1),
      a ∈ Ideal.map (Ideal.Quotient.mk (fil X (j + 1))) (fil X j) ∧
      ((magnus X (j + 1) x : (FreeAssoc X ⧸ fil X (j + 1))ˣ) :
          FreeAssoc X ⧸ fil X (j + 1)) - 1 = (p : ℤ) * a := by
    have hA : ((magnus X (j + 1) x : (FreeAssoc X ⧸ fil X (j + 1))ˣ) :
        FreeAssoc X ⧸ fil X (j + 1)) - 1 ∈ wtq p X (j + 1) (j + 1) :=
      mag_mem_wtq p X (j + 1) j hxP
    obtain ⟨a0, ha0, ha0eq⟩ := (Ideal.mem_map_iff_of_surjective
      (Ideal.Quotient.mk (fil X (j + 1))) Ideal.Quotient.mk_surjective).1 hA
    have hB : magLT X j x ∈ filq X (j + 1) j := adj_magLT_mem_filq X j hj hxγ
    have ha0f : a0 ∈ filz X j := by
      obtain ⟨c, hc, hceq⟩ := mem_filq_iff.1 hB
      have hker : a0 - c ∈ fil X (j + 1) := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub,
          show (Ideal.Quotient.mk (fil X (j + 1))) a0 = magLT X j x from ha0eq, hceq, sub_self]
      have h2 : c + (a0 - c) ∈ filz X j :=
        Submodule.add_mem _ hc
          (filz_antitone X (by omega : j ≤ j + 1) (fil_le_filz X (j + 1) hker))
      rwa [add_sub_cancel] at h2
    obtain ⟨b, hb, hbf⟩ := wtz_filz_exists p X j (Fact.out : p.Prime).pos ha0 ha0f
    refine ⟨Ideal.Quotient.mk (fil X (j + 1)) b, ?_, ?_⟩
    · exact Ideal.mem_map_of_mem _ (filz_le_fil X j hb)
    · have h3 : (Ideal.Quotient.mk (fil X (j + 1))) a0
          = (Ideal.Quotient.mk (fil X (j + 1))) ((p : ℤ) • b) := by
        rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
        exact hbf
      change ((magnus X (j + 1) x : (FreeAssoc X ⧸ fil X (j + 1))ˣ) :
          FreeAssoc X ⧸ fil X (j + 1)) - 1
        = (p : ℤ) * (Ideal.Quotient.mk (fil X (j + 1)) b)
      rw [← ha0eq, h3, map_zsmul, zsmul_eq_mul]
  exact adj_magnus_leadingTerm_of_kernel_and_pure hkernel hpure p (Fact.out : p.Prime).pos X j hj x hxγ
    hdiv

end

end Work.SSGRoute.prop5
