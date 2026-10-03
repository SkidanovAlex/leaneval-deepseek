import Mathlib
import Submission.Work.FIArea7.Pub213.Prop213Pub
import Submission.Work.FIArea7.Pub213.exists_decomp
import Submission.Work.FIArea7.Pub213.dirichletSym_reciprocity_pp
import Submission.Work.FIArea7.Pub213.sum_CBox_rpow_le
import Submission.Work.FIArea7.dirichletSym_mul
import Submission.Work.FIArea7.Classical172Defs



set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FIArea7.Pub213

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 4. The support sets of the arrangement -/

/-- The nonzero elements of the box on which `β` does not vanish. -/
def zSupp (Rz : ℤ) (β : GaussianInt → ℂ) : Finset GaussianInt :=
  (Work.FIPlan.gBox Rz).filter (fun z => z ≠ 0 ∧ β z ≠ 0)

/-- The elements of the box on which `α` does not vanish. -/
def wSupp (Rw : ℤ) (α : GaussianInt → ℂ) : Finset GaussianInt :=
  (Work.FIPlan.gBox Rw).filter (fun w => α w ≠ 0)

/-- The classes `c ∈ C` that occur among the nonzero elements of the box. -/
def cSet (Rz : ℤ) (β : GaussianInt → ℂ) : Finset GaussianInt := (zSupp Rz β).image cPart

lemma mem_zSupp {Rz : ℤ} {β : GaussianInt → ℂ} {z : GaussianInt} :
    z ∈ zSupp Rz β ↔ z ∈ Work.FIPlan.gBox Rz ∧ z ≠ 0 ∧ β z ≠ 0 := by
  simp only [zSupp, Finset.mem_filter]

lemma mem_wSupp {Rw : ℤ} {α : GaussianInt → ℂ} {w : GaussianInt} :
    w ∈ wSupp Rw α ↔ w ∈ Work.FIPlan.gBox Rw ∧ α w ≠ 0 := by
  simp only [wSupp, Finset.mem_filter]

lemma mem_cSet {Rz : ℤ} {β : GaussianInt → ℂ} {c : GaussianInt} :
    c ∈ cSet Rz β ↔ ∃ z ∈ zSupp Rz β, cPart z = c := by
  simp only [cSet, Finset.mem_image]

/-! ## 5. The `z = 0` term -/

/-- A primary Gaussian integer of norm `1` is `1`. -/
lemma eq_one_of_primary_of_gnorm_eq_one {w : GaussianInt} (hw : Work.FIPlan.IsPrimary w)
    (h1 : Work.FIPlan.gnorm w = 1) : w = 1 := by
  obtain ⟨hodd, -, hmod⟩ := hw
  have hnorm : w.re ^ 2 + w.im ^ 2 = 1 := by
    have h := Work.FIArea7.norm_eq w
    rw [← h]
    exact_mod_cast h1
  rcases Commons.NumberTheory.GaussianInt.int_sq_add_sq_eq_one hnorm with
    ⟨hr, hi⟩ | ⟨hr, hi⟩ | ⟨hr, hi⟩ | ⟨hr, hi⟩
  · exact Zsqrtd.ext (by simpa using hr) (by simpa using hi)
  · exfalso
    rw [hi, hr] at hmod
    norm_num at hmod
  · exfalso
    rw [hr] at hodd
    exact absurd hodd (by decide)
  · exfalso
    rw [hr] at hodd
    exact absurd hodd (by decide)

/-- The contribution of `z = 0` to the inner sum is at most `‖β 0‖`. -/
lemma zeroTerm_bound {Rw : ℤ} {α : GaussianInt → ℂ} (β0 : ℂ)
    (hα1 : ∀ w, ‖α w‖ ≤ 1)
    (hαsupp : ∀ w, α w ≠ 0 → Work.FIPlan.IsPrimary w) :
    ‖∑ w ∈ Work.FIPlan.gBox Rw, α w * β0 * ((DirichletSym w 0 : ℤ) : ℂ)‖ ≤ ‖β0‖ := by
  have hD : ∀ w : GaussianInt, DirichletSym w 0 = jacobiSym 0 (Work.FIPlan.gnorm w) := by
    intro w
    simp only [DirichletSym, mul_zero, Zsqrtd.re_zero]
  have hterm : ∀ w : GaussianInt,
      α w * β0 * ((DirichletSym w 0 : ℤ) : ℂ)
        = (if Work.FIPlan.gnorm w = 1 then α w * β0 else 0) := by
    intro w
    by_cases h1 : Work.FIPlan.gnorm w = 1
    · rw [if_pos h1, hD w, h1, jacobiSym.one_right]
      push_cast
      ring
    · rw [if_neg h1, hD w]
      rcases Nat.eq_zero_or_pos (Work.FIPlan.gnorm w) with h0 | hpos
      · have hw0 : w = 0 := Work.FIArea7.gnorm_eq_zero_iff.mp h0
        rw [hw0]
        have hα0 : α 0 = 0 := by
          by_contra hc
          exact absurd (hαsupp 0 hc).1 (by decide)
        rw [hα0, zero_mul, zero_mul]
      · have hlt : 1 < Work.FIPlan.gnorm w := by omega
        rw [jacobiSym.zero_left hlt]
        push_cast
        ring
  rw [Finset.sum_congr rfl (fun w _ => hterm w)]
  have h2 : ∑ w ∈ Work.FIPlan.gBox Rw, (if Work.FIPlan.gnorm w = 1 then α w * β0 else 0)
      = (∑ w ∈ (Work.FIPlan.gBox Rw).filter (fun w => Work.FIPlan.gnorm w = 1), α w) * β0 := by
    rw [Finset.sum_filter, Finset.sum_mul]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h : Work.FIPlan.gnorm w = 1
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, zero_mul]
  rw [h2, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  have h3 : ∀ w ∈ (Work.FIPlan.gBox Rw).filter (fun w => Work.FIPlan.gnorm w = 1),
      w ≠ 1 → α w = 0 := by
    intro w hw hne
    rw [Finset.mem_filter] at hw
    by_contra hα
    exact hne (eq_one_of_primary_of_gnorm_eq_one (hαsupp w hα) hw.2)
  by_cases h1mem : (1 : GaussianInt) ∈ Work.FIPlan.gBox Rw
  · have h1filt : (1 : GaussianInt) ∈
        (Work.FIPlan.gBox Rw).filter (fun w => Work.FIPlan.gnorm w = 1) := by
      rw [Finset.mem_filter]
      exact ⟨h1mem, by decide⟩
    rw [Finset.sum_eq_single 1 ?_ ?_]
    · simpa using hα1 1
    · intro w hw hne
      exact h3 w hw hne
    · intro hmem
      exact absurd h1filt hmem
  · have hzero : ∑ w ∈ (Work.FIPlan.gBox Rw).filter (fun w => Work.FIPlan.gnorm w = 1), α w = 0 := by
      refine Finset.sum_eq_zero fun w hw => ?_
      rw [Finset.mem_filter] at hw
      exact h3 w (by rw [Finset.mem_filter]; exact hw) (fun h => h1mem (h ▸ hw.1))
    rw [hzero, norm_zero]
    norm_num

/-! ## 6. Quadratic reciprocity on the primary primitive support -/

lemma QBilin_recip {Rz Rw : ℤ} {σ τ : GaussianInt → ℂ}
    (hσ : ∀ z, σ z ≠ 0 → Prop213Aux.IsPP z) (hτ : ∀ w, τ w ≠ 0 → Prop213Aux.IsPP w) :
    QBilin Rz Rw σ τ = QBilin Rw Rz τ σ := by
  rw [QBilin, QBilin, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : σ z = 0
  · rw [hz]; ring
  by_cases hw : τ w = 0
  · rw [hw]; ring
  rw [dirichletSym_reciprocity_pp (hσ z hz) (hτ w hw)]
  ring

/-! ## 7. Splitting the `z`-sum into the classes of the arrangement -/

/-- The elements of the class `c` on which `β` does not vanish. -/
def zClassS (Rz : ℤ) (c : GaussianInt) (β : GaussianInt → ℂ) : Finset GaussianInt :=
  (zSupp Rz β).filter (fun z => cPart z = c)

lemma mem_zClassS {Rz : ℤ} {c : GaussianInt} {β : GaussianInt → ℂ} {z : GaussianInt} :
    z ∈ zClassS Rz c β ↔ z ∈ zSupp Rz β ∧ cPart z = c := by
  simp only [zClassS, Finset.mem_filter]

lemma zClassS_subset_zClass {Rz : ℤ} {c : GaussianInt} {β : GaussianInt → ℂ} :
    zClassS Rz c β ⊆ zClass Rz c := by
  intro z hz
  obtain ⟨hz1, hz2⟩ := mem_zClassS.mp hz
  obtain ⟨hz1a, hz1b, -⟩ := mem_zSupp.mp hz1
  exact mem_zClass.mpr ⟨hz1a, hz1b, hz2⟩

/-- The fiber decomposition of the `z`-sum over the classes. -/
lemma fiber_split {Rz : ℤ} {β : GaussianInt → ℂ} {w : GaussianInt} (hw : Prop213Aux.IsPP w) :
    (∑ z ∈ (Work.FIPlan.gBox Rz).filter (fun z => z ≠ 0), β z * ((DirichletSym w z : ℤ) : ℂ))
      = ∑ c ∈ cSet Rz β, ∑ z ∈ zClass Rz c, β z * ((DirichletSym w z : ℤ) : ℂ) := by
  have hstep1 : (∑ z ∈ (Work.FIPlan.gBox Rz).filter (fun z => z ≠ 0),
        β z * ((DirichletSym w z : ℤ) : ℂ))
      = ∑ z ∈ zSupp Rz β, β z * ((DirichletSym w z : ℤ) : ℂ) := by
    rw [zSupp, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hβ : β z = 0
    · simp [hβ]
    · by_cases hz : z ≠ 0
      · rw [if_pos hz, if_pos ⟨hz, hβ⟩]
      · rw [if_neg hz, if_neg (fun h => hz h.1)]
  rw [hstep1]
  rw [← Finset.sum_fiberwise_of_maps_to (s := zSupp Rz β) (t := cSet Rz β) (g := cPart)
        (f := fun z => β z * ((DirichletSym w z : ℤ) : ℂ))
        (by intro z hz; exact mem_cSet.mpr ⟨z, hz, rfl⟩)]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_subset (zClassS_subset_zClass) ?_
  intro z hz hznot
  by_cases hβ : β z = 0
  · rw [hβ, zero_mul]
  · exfalso
    obtain ⟨hz1, hz2⟩ := mem_zClass.mp hz
    exact hznot (mem_zClassS.mpr ⟨mem_zSupp.mpr ⟨hz1, hz2.1, hβ⟩, hz2.2⟩)

lemma zero_mem_gBox {R : ℤ} (hR : 0 ≤ R) : (0 : GaussianInt) ∈ Work.FIPlan.gBox R := by
  refine mem_gBox_of_coords (by simp; omega) (by simp; omega) (by simp; omega) (by simp; omega)

lemma zSupp_subset {Rz : ℤ} {β : GaussianInt → ℂ} : zSupp Rz β ⊆ Work.FIPlan.gBox Rz :=
  fun _ hz => (mem_zSupp.mp hz).1

lemma wSupp_subset {Rw : ℤ} {α : GaussianInt → ℂ} : wSupp Rw α ⊆ Work.FIPlan.gBox Rw :=
  fun _ hw => (mem_wSupp.mp hw).1

lemma QBilin_eq_filter_mul {Rw Rz : ℤ} {α β : GaussianInt → ℂ} :
    QBilin Rw Rz α β
      = ∑ w ∈ wSupp Rw α,
          α w * (∑ z ∈ Work.FIPlan.gBox Rz, β z * ((DirichletSym w z : ℤ) : ℂ)) := by
  rw [wSupp, QBilin, Finset.sum_filter]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases h : α w = 0
  · rw [if_neg (by simpa using h), h]
    simp
  · rw [if_pos h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    ring

lemma sum_box_eq_sum_ne_zero_add {Rz : ℤ} (hRz : 0 ≤ Rz) (f : GaussianInt → ℂ) :
    ∑ z ∈ Work.FIPlan.gBox Rz, f z
      = (∑ z ∈ (Work.FIPlan.gBox Rz).filter (fun z => z ≠ 0), f z) + f 0 := by
  rw [← Finset.sum_filter_add_sum_filter_not (s := Work.FIPlan.gBox Rz) (p := fun z => z ≠ 0)
    (f := f)]
  congr 1
  rw [Finset.sum_filter]
  have h : ∀ z ∈ Work.FIPlan.gBox Rz,
      (if ¬ z ≠ 0 then f z else (0 : ℂ)) = (if z = 0 then f z else 0) := by
    intro z _
    by_cases hz : z = 0
    · rw [if_pos (by simp [hz]), if_pos hz]
    · rw [if_neg (fun hh => hh hz), if_neg hz]
  rw [Finset.sum_congr rfl h]
  refine Finset.sum_eq_single (0 : GaussianInt)
    (s := Work.FIPlan.gBox Rz) (f := fun z : GaussianInt => if z = 0 then f z else (0 : ℂ)) ?_ ?_
  · intro z _ hz
    rw [if_neg hz]
  · intro hmem
    rw [if_pos rfl]
    exact absurd (zero_mem_gBox hRz) hmem

end

end Work.FIArea7.Pub213
