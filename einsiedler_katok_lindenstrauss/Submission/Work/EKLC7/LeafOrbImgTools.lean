import Mathlib
import Submission.Work.EKLRelCross.LeafCtor
import Submission.Work.EKLRelCross.pushOrbit_apply_of_injective
import Submission.Work.EKLRelCross.freeSet_borel
import Submission.Work.EKLRelCross.piece_meets_compact_finite
import Submission.Work.EKLProd.sl3EntryBox_compact
import Submission.Work.EKLCompLeaf.measurable_lintegral_kernel_prod_right_of_finite
import Submission.Work.EKLComp.X3Background

/-!
# Vocabulary for the measurability of the field `x ↦ ∫ f d(ν x)` of `LeafCtor.nuFull`

* `orbImg U x B` — the image `{u • x | u ∈ B ∩ U}` of a set of group elements under the orbit map
  through `x`;
* `freeOrbitSet U` — the (Borel, `freeSet_borel`) set of points whose `U`-orbit map is injective;
* `isCompact_Ucl` / `exists_isCompact_cover_piece` — compactness bookkeeping for `Ucl` and the
  annuli `piece U k`;
* `measurableSet_orbitRel` / `measurable_kernel_orbImg` — the Borelness of the "orbit relation"
  `{(x,y) | ∃ u ∈ B ∩ U, u • x = y}` for `σ`-compact `B`, and the resulting measurability of
  `x ↦ κ x (orbImg U x K)` for a kernel `κ`.
-/

open MeasureTheory Topology Filter
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-!
# `Work.EKLC7.OrbImgTools` — orbit-image tools, re-homed to avoid an import clash

This module is a re-homing (with `isCompact_entryBox` renamed to `isCompact_entryBoxC`) of the
orbit-image toolkit of `Submission/Work/EKLRelCross/LeafMeasDefs.lean`, used by
`Work.EKLC7.measurable_nu`.  The reason is a name clash between that file and
`Submission/Work/EKLRelCross/flower.lean` (both declare `Work.EKLRelCross.isCompact_entryBox`),
which makes it impossible to import both chains in one module.
-/

noncomputable section

namespace Work.EKLC7.OrbImgTools

open Work.EKLContract Work.EKLRelCross


/-! ## The orbit image of a set of group elements -/

/-- The image of a set `B` of group elements under the orbit map `u ↦ u • x`. -/
def orbImg (U : Subgroup SL3) (x : X3) (B : Set SL3) : Set X3 :=
  (fun g : SL3 => g • x) '' (B ∩ (U : Set SL3))

theorem orbImg_mono (U : Subgroup SL3) (x : X3) {B B' : Set SL3} (h : B ⊆ B') :
    orbImg U x B ⊆ orbImg U x B' :=
  Set.image_mono (Set.inter_subset_inter h le_rfl)

theorem orbImg_union (U : Subgroup SL3) (x : X3) (B B' : Set SL3) :
    orbImg U x (B ∪ B') = orbImg U x B ∪ orbImg U x B' := by
  simp only [orbImg, Set.union_inter_distrib_right, Set.image_union]

theorem orbImg_iUnion (U : Subgroup SL3) (x : X3) {ι : Sort*} (B : ι → Set SL3) :
    orbImg U x (⋃ i, B i) = ⋃ i, orbImg U x (B i) := by
  simp only [orbImg, Set.iUnion_inter, Set.image_iUnion]

theorem mem_orbImg {U : Subgroup SL3} {x y : X3} {B : Set SL3} :
    y ∈ orbImg U x B ↔ ∃ u ∈ B, u ∈ U ∧ u • x = y := by
  constructor
  · rintro ⟨u, ⟨huB, huU⟩, rfl⟩
    exact ⟨u, huB, huU, rfl⟩
  · rintro ⟨u, huB, huU, rfl⟩
    exact ⟨u, ⟨huB, huU⟩, rfl⟩

theorem orbImg_subset_orbit (U : Subgroup SL3) (x : X3) (B : Set SL3) :
    orbImg U x B ⊆ (fun g : SL3 => g • x) '' (U : Set SL3) :=
  Set.image_mono Set.inter_subset_right

/-! ## The free-orbit set -/

/-- The set of points whose `U`-orbit map `u ↦ u • x` is injective, in the pointwise form used
by `freeSet_borel`. -/
def freeOrbitSet (U : Subgroup SL3) : Set X3 :=
  {x : X3 | ∀ u ∈ U, u • x = x → u = 1}

theorem mem_freeOrbitSet_iff (U : Subgroup SL3) (x : X3) :
    x ∈ freeOrbitSet U ↔ Function.Injective (fun u : U => ((u : SL3) • x)) := by
  constructor
  · intro h u v huv
    have huv' : (u : SL3) • x = (v : SL3) • x := huv
    have h1 : ((u : SL3)⁻¹ * (v : SL3)) • x = x := by
      rw [mul_smul, ← huv', ← mul_smul, inv_mul_cancel, one_smul]
    have h2 : ((u : SL3)⁻¹ * (v : SL3)) ∈ U := U.mul_mem (U.inv_mem u.2) v.2
    have h3 : (u : SL3)⁻¹ * (v : SL3) = 1 := h _ h2 h1
    have h4 : (v : SL3) = (u : SL3) := by
      calc (v : SL3) = (u : SL3) * ((u : SL3)⁻¹ * (v : SL3)) := by group
        _ = (u : SL3) * 1 := by rw [h3]
        _ = (u : SL3) := mul_one _
    exact Subtype.ext h4.symm
  · intro h u hu hux
    have h1 : (⟨u, hu⟩ : U) = ⟨1, U.one_mem⟩ :=
      h (by simpa using hux)
    have h2 : ((⟨u, hu⟩ : U) : SL3) = ((⟨1, U.one_mem⟩ : U) : SL3) := by rw [h1]
    simpa using h2

theorem measurableSet_freeOrbitSet {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3)) :
    MeasurableSet (freeOrbitSet U) :=
  freeSet_borel hUcl

theorem measurableSet_freeOrbitSet' {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3)) :
    MeasurableSet {x : X3 | Function.Injective (fun u : U => ((u : SL3) • x))} := by
  have h : {x : X3 | Function.Injective (fun u : U => ((u : SL3) • x))} = freeOrbitSet U := by
    ext x; exact (mem_freeOrbitSet_iff U x).symm
  rw [h]
  exact measurableSet_freeOrbitSet hUcl

/-! ## Compactness bookkeeping -/

theorem isCompact_entryBoxC (r : ℝ) :
    IsCompact {g : SL3 | ∀ i j : Fin 3,
      |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ r} := by
  rw [show {g : SL3 | ∀ i j : Fin 3,
      |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ r}
      = {g : SL3 | ∀ i j : Fin 3,
          (1 : Matrix (Fin 3) (Fin 3) ℝ) i j - r ≤ (g : Matrix (Fin 3) (Fin 3) ℝ) i j ∧
          (g : Matrix (Fin 3) (Fin 3) ℝ) i j ≤ (1 : Matrix (Fin 3) (Fin 3) ℝ) i j + r} from by
    ext g
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h i j
      have := abs_le.mp (h i j)
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    · intro h i j
      have := h i j
      exact abs_le.mpr ⟨by linarith [this.1], by linarith [this.2]⟩]
  exact Work.EKLProd.sl3EntryBox_compact _ _

theorem isClosed_entryBox (r : ℝ) :
    IsClosed {g : SL3 | ∀ i j : Fin 3,
      |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ r} := by
  rw [show {g : SL3 | ∀ i j : Fin 3,
      |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ r}
      = ⋂ i : Fin 3, ⋂ j : Fin 3, {g : SL3 |
          |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ r} from by
    ext g; simp [Set.mem_iInter]]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_le (by fun_prop) continuous_const

theorem Ucl_eq_inter_entryBox (U : Subgroup SL3) (r : ℝ) :
    Ucl U r = (U : Set SL3) ∩ {g : SL3 | ∀ i j : Fin 3,
      |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ r} :=
  rfl

theorem isClosed_Ucl (U : Subgroup SL3) (hUcl : IsClosed (U : Set SL3)) (r : ℝ) :
    IsClosed (Ucl U r) := by
  rw [Ucl_eq_inter_entryBox]
  exact hUcl.inter (isClosed_entryBox r)

/-- The closed `U`-ball `Ucl U r` is compact: it is a closed subset of an entrywise box. -/
theorem isCompact_Ucl (U : Subgroup SL3) (hUcl : IsClosed (U : Set SL3)) (r : ℝ) :
    IsCompact (Ucl U r) := by
  refine (isCompact_entryBoxC r).of_isClosed_subset (isClosed_Ucl U hUcl r) ?_
  intro g hg
  exact hg.2

theorem isCompact_box1 (U : Subgroup SL3) (hUcl : IsClosed (U : Set SL3)) :
    IsCompact (Box1 U) :=
  isCompact_Ucl U hUcl 1

/-- The `k`-th annulus `piece U k` is a countable union of compact sets. -/
theorem exists_isCompact_cover_piece (U : Subgroup SL3) (hUcl : IsClosed (U : Set SL3)) (k : ℕ) :
    ∃ K : ℕ → Set SL3, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = piece U k := by
  cases k with
  | zero =>
    refine ⟨fun _ => Box1 U, fun _ => isCompact_box1 U hUcl, ?_⟩
    rw [Set.iUnion_const]
    rfl
  | succ j =>
    refine ⟨fun n : ℕ => Ucl U ((j : ℝ) + 2) ∩ {g : SL3 | ∃ i k' : Fin 3,
        (j : ℝ) + 1 + 1 / ((n : ℝ) + 1) ≤
          |(g : Matrix (Fin 3) (Fin 3) ℝ) i k' - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k'|},
      fun n => ?_, ?_⟩
    · refine (isCompact_Ucl U hUcl _).of_isClosed_subset ?_ Set.inter_subset_left
      refine IsClosed.inter (isClosed_Ucl U hUcl _) ?_
      rw [show {g : SL3 | ∃ i k' : Fin 3,
          (j : ℝ) + 1 + 1 / ((n : ℝ) + 1) ≤
            |(g : Matrix (Fin 3) (Fin 3) ℝ) i k' - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k'|}
          = ⋃ i : Fin 3, ⋃ k' : Fin 3, {g : SL3 |
              (j : ℝ) + 1 + 1 / ((n : ℝ) + 1) ≤
                |(g : Matrix (Fin 3) (Fin 3) ℝ) i k' - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k'|}
          from by
        ext g; simp [Set.mem_iUnion]]
      exact isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun k' =>
        isClosed_le continuous_const (by fun_prop)
    · ext g
      constructor
      · intro hg
        rw [Set.mem_iUnion] at hg
        obtain ⟨n, hg1, i, k', hle⟩ := hg
        refine ⟨hg1, ?_⟩
        intro hcon
        have h2 : |(g : Matrix (Fin 3) (Fin 3) ℝ) i k'
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k'| ≤ (j : ℝ) + 1 := hcon.2 i k'
        have h3 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · rintro ⟨hg1, hg2⟩
        have hUmem : g ∈ U := hg1.1
        have hik : ∃ i k' : Fin 3, (j : ℝ) + 1 < |(g : Matrix (Fin 3) (Fin 3) ℝ) i k'
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k'| := by
          by_contra hcon
          push Not at hcon
          exact hg2 ⟨hUmem, fun i k' => hcon i k'⟩
        obtain ⟨i, k', hik'⟩ := hik
        have hpos : 0 < |(g : Matrix (Fin 3) (Fin 3) ℝ) i k'
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k'| - ((j : ℝ) + 1) := by linarith
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
        rw [Set.mem_iUnion]
        exact ⟨n, hg1, i, k', by linarith [le_of_lt hn]⟩

/-! ## The orbit relation is Borel -/

/-- The "orbit relation" of a compact set of group elements: `{(x,y) | ∃ u ∈ K ∩ U, u • x = y}` is
Borel.  It is the image of the compact set `(K ∩ U) × L n` under a continuous map. -/
theorem measurableSet_orbitRel {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3))
    {K : Set SL3} (hK : IsCompact K) :
    MeasurableSet {p : X3 × X3 | ∃ u ∈ K ∩ (U : Set SL3), u • p.1 = p.2} := by
  classical
  obtain ⟨L, hLc, hLuniv⟩ : ∃ L : ℕ → Set X3, (∀ n, IsCompact (L n)) ∧ ⋃ n, L n = Set.univ := by
    haveI : SigmaCompactSpace X3 := inferInstance
    exact ⟨(default : CompactExhaustion X3),
      fun n => (default : CompactExhaustion X3).isCompact n,
      (default : CompactExhaustion X3).iUnion_eq⟩
  have hset : {p : X3 × X3 | ∃ u ∈ K ∩ (U : Set SL3), u • p.1 = p.2}
      = ⋃ n : ℕ, ((fun q : SL3 × X3 => (q.2, q.1 • q.2))
          '' ((K ∩ (U : Set SL3)) ×ˢ L n)) := by
    ext p
    constructor
    · rintro ⟨u, huK, hux⟩
      obtain ⟨n, hn⟩ : ∃ n, p.1 ∈ L n :=
        Set.mem_iUnion.mp (by rw [hLuniv]; trivial)
      exact Set.mem_iUnion.mpr ⟨n, ⟨(u, p.1), ⟨huK, hn⟩, by simp [hux]⟩⟩
    · intro hp
      obtain ⟨n, q, hq, hqp⟩ := Set.mem_iUnion.mp hp
      refine ⟨q.1, hq.1, ?_⟩
      have h1 : p.1 = q.2 := by rw [← hqp]
      have h2 : p.2 = q.1 • q.2 := by rw [← hqp]
      rw [h1, h2]
  rw [hset]
  refine MeasurableSet.iUnion fun n => ?_
  have himg : IsCompact ((fun q : SL3 × X3 => (q.2, q.1 • q.2))
      '' ((K ∩ (U : Set SL3)) ×ˢ L n)) :=
    ((hK.inter_right hUcl).prod (hLc n)).image
      (continuous_snd.prodMk (Continuous.smul continuous_fst continuous_snd))
  exact himg.measurableSet

/-- The orbit relation of a `σ`-compact set of group elements (given as an explicit countable union
of compacta) is Borel. -/
theorem measurableSet_orbitRel_cover {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3))
    {B : Set SL3} (hB : ∃ K : ℕ → Set SL3, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = B) :
    MeasurableSet {p : X3 × X3 | ∃ u ∈ B ∩ (U : Set SL3), u • p.1 = p.2} := by
  obtain ⟨K, hKc, hKB⟩ := hB
  have hset : {p : X3 × X3 | ∃ u ∈ B ∩ (U : Set SL3), u • p.1 = p.2}
      = ⋃ n : ℕ, {p : X3 × X3 | ∃ u ∈ K n ∩ (U : Set SL3), u • p.1 = p.2} := by
    ext p
    constructor
    · rintro ⟨u, ⟨huB, huU⟩, hux⟩
      obtain ⟨n, hun⟩ : ∃ n, u ∈ K n := by
        have h : u ∈ ⋃ n, K n := by rw [hKB]; exact huB
        exact Set.mem_iUnion.mp h
      exact Set.mem_iUnion.mpr ⟨n, ⟨u, ⟨hun, huU⟩, hux⟩⟩
    · intro hp
      obtain ⟨n, hp'⟩ := Set.mem_iUnion.mp hp
      obtain ⟨u, ⟨hun, huU⟩, hux⟩ := hp'
      refine ⟨u, ⟨?_, huU⟩, hux⟩
      have h : u ∈ ⋃ n, K n := Set.mem_iUnion.mpr ⟨n, hun⟩
      rwa [hKB] at h
  rw [hset]
  exact MeasurableSet.iUnion fun n => measurableSet_orbitRel hUcl (hKc n)

/-- For a compact set `K` of group elements and a (pointwise finite) kernel `κ` on `X₃`, the
function `x ↦ κ x (orbImg U x K)` is measurable. -/
theorem measurable_kernel_orbImg {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3))
    (κ : ProbabilityTheory.Kernel X3 X3) (hκ : ∀ x, IsFiniteMeasure (κ x))
    {K : Set SL3} (hK : IsCompact K) :
    Measurable (fun x : X3 => κ x (orbImg U x K)) := by
  set R : Set (X3 × X3) := {p : X3 × X3 | ∃ u ∈ K ∩ (U : Set SL3), u • p.1 = p.2} with hRdef
  have hR : MeasurableSet R := by
    rw [hRdef]; exact measurableSet_orbitRel hUcl hK
  have hsec : ∀ x : X3, {y : X3 | (x, y) ∈ R} = orbImg U x K := by
    intro x
    ext y
    rw [hRdef]
    simp only [Set.mem_ofPred_eq, mem_orbImg]
    constructor
    · rintro ⟨u, ⟨huK, huU⟩, hux⟩
      exact ⟨u, huK, huU, hux⟩
    · rintro ⟨u, huK, huU, hux⟩
      exact ⟨u, ⟨huK, huU⟩, hux⟩
  have hfun : (fun x : X3 => κ x (orbImg U x K))
      = fun x => ∫⁻ y, R.indicator (fun _ => (1 : ℝ≥0∞)) (x, y) ∂(κ x) := by
    funext x
    rw [lintegral_indicator_const_comp (f := fun y : X3 => (x, y)) (μ := κ x)
      measurable_prodMk_left hR (1 : ℝ≥0∞), one_mul]
    exact congrArg (κ x) (hsec x)
  rw [hfun]
  exact Work.EKLCompLeaf.measurable_lintegral_kernel_prod_right_of_finite hκ
    (measurable_const.indicator hR)

end Work.EKLC7.OrbImgTools
