import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Submission.Work.SSGRoute.wtz_filz_exists_pow
import Submission.Work.Shrinking.PCentral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-
PORT TASK.  A complete, sorry-free proof of this exact statement already exists on disk, but in a
module that can no longer be imported; the job is to PORT it into a fresh module with clean imports.

SOURCE (proved, `sorry`-free): `Submission/Work/SSGRoute/magLT_pSeries_divisible.lean`, result
`Work.SSGRoute.magLT_pSeries_divisible`, states verbatim this claim with
`Work.SSGRoute.prop5.magLT X j x := ↑(magnus X (j+1) x) - 1` in place of
`Work.SSGRoute.prop5.magLead (j+1) x`.  Those two terms are DEFINITIONALLY EQUAL (`rfl`), so the
source proof body copies verbatim after replacing `magLT X j x` by `magLead (j+1) x` and
`magLT_mem_filq X j hj hxγ` (from `prop5/magnus_leadingTerm.lean`) by
`Work.SSGRoute.prop5.magLead_mem_filq (j+1) j hj (by omega) hxγ` (available from
`prop5/magnusGroupPart.lean`).  The source file is self-contained apart from its second import
`Submission.Work.SSGRoute.wtz_filz_exists_pow` (kept) and its first import
`Submission.Work.SSGRoute.prop5.magnus_leadingTerm` (dropped).

Content: `magLead (j+1) x` is the degree-`j` leading term of the Magnus image of `x`;
membership of `x` in the paper's `P^i ∩ γ_j` forces that leading term to be divisible by `p^{i-j}`
inside the degree-`j` part `filq X (j+1) j`.  This is the analytic input (the Magnus image has
weight `i`) for the `⊆` direction of Schmidt–Wingberg Lemma 4(ii).
-/

noncomputable section

set_option maxHeartbeats 4000000

open scoped commutatorElement

namespace Work.SSGRoute.oneStep

open Work.SSGRoute.prop5

variable {X : Type*}

/-! ## The weight-filtration block (ported, every helper under a local name) -/

/-- The image of the `p`-adic weight filtration piece (`Work.SSGRoute.prop5.wtIdeal`) in the
truncated free associative algebra `FreeAssoc X ⧸ fil X N`. -/
def wtqLT (p : ℕ) (X : Type*) (N n : ℕ) : Ideal (FreeAssoc X ⧸ fil X N) :=
  Ideal.map (Ideal.Quotient.mk (fil X N)) (wtIdeal p X n)

instance wtIdeal_isTwoSidedLT (p : ℕ) (X : Type*) (n : ℕ) : (wtIdeal p X n).IsTwoSided :=
  ⟨fun b ha => mul_mem_wtz' p n b ha⟩

instance wtqLT_isTwoSided (p : ℕ) (X : Type*) (N n : ℕ) : (wtqLT p X N n).IsTwoSided :=
  ⟨fun b ha => by
    obtain ⟨a', ha', rfl⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (fil X N))
      Ideal.Quotient.mk_surjective).1 ha
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul]
    exact Ideal.mem_map_of_mem _ (Ideal.mul_mem_right b' (wtIdeal p X n) ha')⟩

/-- `wtqLT` is decreasing in the weight. -/
theorem wtqLT_le (p : ℕ) (X : Type*) (N : ℕ) : Antitone (wtqLT p X N) :=
  fun _ _ hnm => Ideal.map_mono (wtIdeal_le p X hnm)

/-- The product of two weight pieces lands in the weight piece of the sum of the weights. -/
theorem wtqLT_mul_mem (p : ℕ) (X : Type*) (N n m : ℕ) {a b : FreeAssoc X ⧸ fil X N}
    (ha : a ∈ wtqLT p X N n) (hb : b ∈ wtqLT p X N m) : a * b ∈ wtqLT p X N (n + m) := by
  obtain ⟨a', ha', rfl⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (fil X N))
    Ideal.Quotient.mk_surjective).1 ha
  obtain ⟨b', hb', rfl⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (fil X N))
    Ideal.Quotient.mk_surjective).1 hb
  rw [← map_mul]
  exact Ideal.mem_map_of_mem _ (wtIdeal_mul_le p X n m (Ideal.mul_mem_mul ha' hb'))

/-- `p` times a weight-`n` piece lies in the weight-`(n+1)` piece. -/
theorem wtqLT_smul_p (p : ℕ) (X : Type*) (N n : ℕ) {a : FreeAssoc X ⧸ fil X N}
    (ha : a ∈ wtqLT p X N n) : (p : ℤ) • a ∈ wtqLT p X N (n + 1) := by
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

/-- Units of the truncated algebra which are `≡ 1` modulo the weight piece `wtqLT p X N n`. -/
def wtUnitLT (p : ℕ) (X : Type*) (N n : ℕ) : Subgroup (FreeAssoc X ⧸ fil X N)ˣ where
  carrier := {u | ((u : FreeAssoc X ⧸ fil X N) - 1) ∈ wtqLT p X N n}
  mul_mem' := by
    intro u v hu hv
    change ((↑(u * v) : FreeAssoc X ⧸ fil X N) - 1) ∈ wtqLT p X N n
    have h : (↑(u * v) : FreeAssoc X ⧸ fil X N) - 1
        = (↑u : FreeAssoc X ⧸ fil X N) * ((↑v : FreeAssoc X ⧸ fil X N) - 1)
          + ((↑u : FreeAssoc X ⧸ fil X N) - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [h]
    exact Submodule.add_mem _ (Ideal.mul_mem_left _ _ hv) hu
  one_mem' := by
    change ((↑(1 : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1) ∈ wtqLT p X N n
    rw [Units.val_one]; simp
  inv_mem' := by
    intro u hu
    change ((↑(u⁻¹) : FreeAssoc X ⧸ fil X N) - 1) ∈ wtqLT p X N n
    have h1 : (↑(u⁻¹) : FreeAssoc X ⧸ fil X N) * ↑u = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h : (↑(u⁻¹) : FreeAssoc X ⧸ fil X N) - 1
        = - ((↑(u⁻¹) : FreeAssoc X ⧸ fil X N) * ((↑u : FreeAssoc X ⧸ fil X N) - 1)) := by
      rw [mul_sub, h1, mul_one, neg_sub]
    rw [h]
    exact neg_mem (Ideal.mul_mem_left _ _ hu)

/-- `(1 + x) ^ m - 1 - m x` lies in the weight piece of doubled weight, for `x` of weight `n ≥ 1`.
Modulo the doubled weight piece, `x` has square zero, so `(1 + x)^m ≡ 1 + m x`. -/
theorem one_add_pow_sub_memLT (p : ℕ) (X : Type*) (N n m : ℕ) (_hn : 1 ≤ n)
    {x : FreeAssoc X ⧸ fil X N} (hx : x ∈ wtqLT p X N n) :
    (1 + x) ^ m - 1 - (m : ℤ) • x ∈ wtqLT p X N (2 * n) := by
  have hx2 : x * x ∈ wtqLT p X N (2 * n) := by
    have h := wtqLT_mul_mem p X N n n hx hx
    rwa [show n + n = 2 * n from by ring] at h
  have h0 : (Ideal.Quotient.mk (wtqLT p X N (2 * n))) ((1 + x) ^ m - 1 - (m : ℤ) • x) = 0 := by
    rw [map_sub, map_sub, map_pow, map_add, map_one, map_zsmul]
    have hxx : (Ideal.Quotient.mk (wtqLT p X N (2 * n)) x) *
        (Ideal.Quotient.mk (wtqLT p X N (2 * n)) x) = 0 := by
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact hx2
    rw [one_add_pow_eq_of_sq_zero (Ideal.Quotient.mk (wtqLT p X N (2 * n)) x) hxx m]
    simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_natCast]
    abel
  rwa [Ideal.Quotient.eq_zero_iff_mem] at h0

/-- The `p`-th power of a unit congruent to `1` modulo the weight-`n` piece is congruent to `1`
modulo the weight-`(n+1)` piece. -/
theorem wtUnitLT_pow_mem (p : ℕ) (X : Type*) (N n : ℕ) (hn : 1 ≤ n)
    {u : (FreeAssoc X ⧸ fil X N)ˣ} (hu : u ∈ wtUnitLT p X N n) :
    u ^ p ∈ wtUnitLT p X N (n + 1) := by
  set x : FreeAssoc X ⧸ fil X N := ((u : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1
    with hx
  have hxmem : x ∈ wtqLT p X N n := hu
  have hmain : (1 + x) ^ p - 1 - (p : ℤ) • x ∈ wtqLT p X N (2 * n) :=
    one_add_pow_sub_memLT p X N n p hn hxmem
  have hpx : (p : ℤ) • x ∈ wtqLT p X N (n + 1) := wtqLT_smul_p p X N n hxmem
  have hle : wtqLT p X N (2 * n) ≤ wtqLT p X N (n + 1) := wtqLT_le p X N (by omega)
  have hsum : ((1 + x) ^ p - 1 - (p : ℤ) • x) + (p : ℤ) • x ∈ wtqLT p X N (n + 1) :=
    Submodule.add_mem _ (hle hmain) hpx
  have hux : ((u : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) = 1 + x := by
    rw [hx]; abel
  change (((u ^ p : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1) ∈ wtqLT p X N (n + 1)
  rw [Units.val_pow_eq_pow_val, hux]
  have heq : (1 + x) ^ p - 1 = ((1 + x) ^ p - 1 - (p : ℤ) • x) + (p : ℤ) • x := by abel
  rw [heq]
  exact hsum

/-- The commutator of a unit congruent to `1` modulo the weight-`n` piece with a unit congruent to
`1` modulo the weight-`1` piece lands in the weight-`(n+1)` piece. -/
theorem wtUnitLT_commutator_le (p : ℕ) (X : Type*) (N n : ℕ) :
    ⁅wtUnitLT p X N n, wtUnitLT p X N 1⁆ ≤ wtUnitLT p X N (n + 1) := by
  rw [Subgroup.commutator_le]
  intro u hu v hv
  change ((↑(⁅u, v⁆) : FreeAssoc X ⧸ fil X N) - 1) ∈ wtqLT p X N (n + 1)
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
      ∈ wtqLT p X N (n + 1) := by
    have h1 : ((↑u : FreeAssoc X ⧸ fil X N) - 1) * ((↑v : FreeAssoc X ⧸ fil X N) - 1)
        ∈ wtqLT p X N (n + 1) := wtqLT_mul_mem p X N n 1 hu hv
    have h2 : ((↑v : FreeAssoc X ⧸ fil X N) - 1) * ((↑u : FreeAssoc X ⧸ fil X N) - 1)
        ∈ wtqLT p X N (1 + n) := wtqLT_mul_mem p X N 1 n hv hu
    rw [show 1 + n = n + 1 from by ring] at h2
    exact Submodule.sub_mem _ h1 h2
  exact Ideal.mul_mem_right _ (wtqLT p X N (n + 1)) hmem

/-- The Magnus image of the whole free group is congruent to `1` modulo the weight-`1` piece. -/
theorem magnus_le_wtUnit_oneLT (p : ℕ) (X : Type*) (N : ℕ) :
    Subgroup.map (magnus X N) (⊤ : Subgroup (FreeGroup X)) ≤ wtUnitLT p X N 1 := by
  intro u hu
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hu
  exact Ideal.map_mono (fil_le_wtIdeal p X (le_refl 1))
    (map_magnus_le_unitCongr_one X N (Subgroup.mem_map_of_mem _ (Subgroup.mem_top y)))

/-- The Magnus image of the `n`-th term of the descending `p`-central series is congruent to `1`
modulo the weight-`(n+1)` piece. -/
theorem magnus_pCentralSeries_le_wtUnitLT (p : ℕ) (X : Type*) (N n : ℕ) :
    Subgroup.map (magnus X N) (Work.Shrinking.pCentralSeries p (FreeGroup X) n) ≤
      wtUnitLT p X N (n + 1) := by
  induction n with
  | zero =>
      rw [Work.Shrinking.pCentralSeries_zero]
      exact magnus_le_wtUnit_oneLT p X N
  | succ n ih =>
      rw [Work.Shrinking.pCentralSeries_succ]
      unfold Work.Shrinking.pCentralStep
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rw [Work.Shrinking.powSubgroup, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
        rintro z ⟨h, hh, rfl⟩
        change magnus X N (h ^ p) ∈ wtUnitLT p X N (n + 1 + 1)
        rw [map_pow]
        exact wtUnitLT_pow_mem p X N (n + 1) (by omega) (ih (Subgroup.mem_map_of_mem _ hh))
      · rw [Subgroup.map_commutator]
        exact le_trans (Subgroup.commutator_mono ih (magnus_le_wtUnit_oneLT p X N))
          (wtUnitLT_commutator_le p X N (n + 1))

/-- **The `p`-central series lies in the weight filtration.** -/
theorem mag_mem_wtqLT (p : ℕ) (X : Type*) (N n : ℕ) {x : FreeGroup X}
    (hx : x ∈ Work.Shrinking.pCentralSeries p (FreeGroup X) n) :
    ((magnus X N x : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1 ∈
      wtqLT p X N (n + 1) :=
  magnus_pCentralSeries_le_wtUnitLT p X N n (Subgroup.mem_map_of_mem _ hx)

/-! ## Elementary `filz` facts -/

/-- The length ideal `fil X N` is contained in the length-support submodule `filz X N`. -/
theorem fil_le_filz_local (X : Type*) (N : ℕ) :
    (fil X N : Set (FreeAssoc X)) ⊆ filz X N := by
  rw [fil_eq_filI]
  exact fun a ha => ha

/-- The length-support submodules are decreasing in the length. -/
theorem filz_antitone_local (X : Type*) : Antitone (filz X) := by
  intro m n hmn
  refine Submodule.span_mono ?_
  rintro a ⟨w, hw, rfl⟩
  exact ⟨w, le_trans hmn hw, rfl⟩

/-! ## The main divisibility statement -/

theorem magLead_pSeries_divisible (p : ℕ) [Fact p.Prime] (X : Type) (i j : ℕ) (hj : 1 ≤ j)
    (hji : j ≤ i) {x : FreeGroup X}
    (hxP : x ∈ Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1))
    (hxγ : x ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) :
    ∃ a ∈ Work.SSGRoute.prop5.filq X (j + 1) j,
      Work.SSGRoute.prop5.magLead (j + 1) x = ((p : ℤ) ^ (i - j)) • a := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hje : j + (i - j) = i := by omega
  -- the Magnus image of `x` has weight `i`
  have hA : ((magnus X (j + 1) x : (FreeAssoc X ⧸ fil X (j + 1))ˣ) :
      FreeAssoc X ⧸ fil X (j + 1)) - 1 ∈ wtqLT p X (j + 1) i := by
    have h := mag_mem_wtqLT p X (j + 1) (i - 1) hxP
    rwa [show i - 1 + 1 = i from by omega] at h
  obtain ⟨a0, ha0, ha0eq⟩ := (Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk (fil X (j + 1))) Ideal.Quotient.mk_surjective).1 hA
  have hB : magLead (j + 1) x ∈ filq X (j + 1) j :=
    magLead_mem_filq (j + 1) j hj (by omega) hxγ
  -- `a0` may be chosen supported in words of length `≥ j`
  have ha0f : a0 ∈ filz X j := by
    obtain ⟨c, hc, hceq⟩ := mem_filq_iff.1 hB
    have hker : a0 - c ∈ fil X (j + 1) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub,
        show (Ideal.Quotient.mk (fil X (j + 1))) a0 = magLead (j + 1) x from ha0eq, hceq, sub_self]
    have h2 : c + (a0 - c) ∈ filz X j :=
      Submodule.add_mem _ hc
        (filz_antitone_local X (by omega : j ≤ j + 1)
          (fil_le_filz_local X (j + 1) hker))
    rwa [add_sub_cancel] at h2
  have ha0' : a0 ∈ wtz p X (j + (i - j)) := by rw [hje]; exact ha0
  obtain ⟨b, hb, hbf⟩ := wtz_filz_exists_pow p X j (i - j) hp ha0' ha0f
  refine ⟨Ideal.Quotient.mk (fil X (j + 1)) b, ?_, ?_⟩
  · exact Ideal.mem_map_of_mem _ (filz_le_fil X j hb)
  · have h3 : (Ideal.Quotient.mk (fil X (j + 1))) a0
        = (Ideal.Quotient.mk (fil X (j + 1))) (((p : ℤ) ^ (i - j)) • b) := by
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hbf
    change ((magnus X (j + 1) x : (FreeAssoc X ⧸ fil X (j + 1))ˣ) :
        FreeAssoc X ⧸ fil X (j + 1)) - 1
      = ((p : ℤ) ^ (i - j)) • (Ideal.Quotient.mk (fil X (j + 1)) b)
    rw [← ha0eq, h3, map_zsmul]

end Work.SSGRoute.oneStep
