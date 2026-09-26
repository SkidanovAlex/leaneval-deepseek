import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.RCLike.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.MetricSpace.Thickening
import Submission.Commons.Topology.Strip.convex_fibre_periodic_section

namespace Commons.Topology.Strip

open Set Metric

/-- The lower bound attached to `B` in the column `x`: the supremum of the `y`-coordinates of the
points of `B` lying in the strip `[a,b]`, with `a` adjoined so that the set is nonempty. -/
private noncomputable def lowSup (a b : ℝ) (B : Set (ℝ × ℝ)) (x : ℝ) : ℝ :=
  sSup ({y : ℝ | a ≤ y ∧ y ≤ b ∧ (x, y) ∈ B} ∪ {a})

/-- The upper bound attached to `A` in the column `x`: the infimum of the `y`-coordinates of the
points of `A` lying in the strip `[a,b]`, with `b` adjoined so that the set is nonempty. -/
private noncomputable def highInf (a b : ℝ) (A : Set (ℝ × ℝ)) (x : ℝ) : ℝ :=
  sInf ({y : ℝ | a ≤ y ∧ y ≤ b ∧ (x, y) ∈ A} ∪ {b})

private lemma bddAbove_low {a b : ℝ} (hab : a ≤ b) (B : Set (ℝ × ℝ)) (x : ℝ) :
    BddAbove ({y : ℝ | a ≤ y ∧ y ≤ b ∧ (x, y) ∈ B} ∪ {a}) :=
  ⟨b, fun y hy => by rcases hy with hy | rfl; exacts [hy.2.1, hab]⟩

private lemma bddBelow_high {a b : ℝ} (hab : a ≤ b) (A : Set (ℝ × ℝ)) (x : ℝ) :
    BddBelow ({y : ℝ | a ≤ y ∧ y ≤ b ∧ (x, y) ∈ A} ∪ {b}) :=
  ⟨a, fun y hy => by rcases hy with hy | rfl; exacts [hy.1, hab]⟩

private lemma lowSup_le {a b : ℝ} (hab : a ≤ b) (B : Set (ℝ × ℝ)) (x : ℝ) :
    lowSup a b B x ≤ b :=
  csSup_le ⟨a, Or.inr rfl⟩ fun y hy => by rcases hy with hy | rfl; exacts [hy.2.1, hab]

private lemma le_lowSup {a b : ℝ} (hab : a ≤ b) (B : Set (ℝ × ℝ)) (x : ℝ) :
    a ≤ lowSup a b B x :=
  le_csSup (bddAbove_low hab B x) (Or.inr rfl)

private lemma le_lowSup_of_mem {a b : ℝ} (hab : a ≤ b) {B : Set (ℝ × ℝ)} {x y : ℝ}
    (hy : (x, y) ∈ B) (hay : a ≤ y) (hyb : y ≤ b) : y ≤ lowSup a b B x :=
  le_csSup (bddAbove_low hab B x) (Or.inl ⟨hay, hyb, hy⟩)

private lemma highInf_le {a b : ℝ} (hab : a ≤ b) (A : Set (ℝ × ℝ)) (x : ℝ) :
    highInf a b A x ≤ b :=
  csInf_le (bddBelow_high hab A x) (Or.inr rfl)

private lemma le_highInf {a b : ℝ} (hab : a ≤ b) (A : Set (ℝ × ℝ)) (x : ℝ) :
    a ≤ highInf a b A x :=
  le_csInf ⟨b, Or.inr rfl⟩ fun y hy => by rcases hy with hy | rfl; exacts [hy.1, hab]

private lemma highInf_le_of_mem {a b : ℝ} (hab : a ≤ b) {A : Set (ℝ × ℝ)} {x y : ℝ}
    (hy : (x, y) ∈ A) (hay : a ≤ y) (hyb : y ≤ b) : highInf a b A x ≤ y :=
  csInf_le (bddBelow_high hab A x) (Or.inl ⟨hay, hyb, hy⟩)

private lemma lowSup_periodic {a b p : ℝ} {B : Set (ℝ × ℝ)}
    (hperB : ∀ q : ℝ × ℝ, q ∈ B ↔ (q.1 + p, q.2) ∈ B) (x : ℝ) :
    lowSup a b B (x + p) = lowSup a b B x := by
  have hset : {y : ℝ | a ≤ y ∧ y ≤ b ∧ (x + p, y) ∈ B} ∪ {a}
      = {y : ℝ | a ≤ y ∧ y ≤ b ∧ (x, y) ∈ B} ∪ {a} := by
    ext y
    have h := (hperB (x, y)).symm
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro (⟨h1, h2, h3⟩ | h4)
      · exact Or.inl ⟨h1, h2, h.1 h3⟩
      · exact Or.inr h4
    · rintro (⟨h1, h2, h3⟩ | h4)
      · exact Or.inl ⟨h1, h2, h.2 h3⟩
      · exact Or.inr h4
  unfold lowSup
  rw [hset]

private lemma highInf_periodic {a b p : ℝ} {A : Set (ℝ × ℝ)}
    (hperA : ∀ q : ℝ × ℝ, q ∈ A ↔ (q.1 + p, q.2) ∈ A) (x : ℝ) :
    highInf a b A (x + p) = highInf a b A x := by
  have hset : {y : ℝ | a ≤ y ∧ y ≤ b ∧ (x + p, y) ∈ A} ∪ {b}
      = {y : ℝ | a ≤ y ∧ y ≤ b ∧ (x, y) ∈ A} ∪ {b} := by
    ext y
    have h := (hperA (x, y)).symm
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro (⟨h1, h2, h3⟩ | h4)
      · exact Or.inl ⟨h1, h2, h.1 h3⟩
      · exact Or.inr h4
    · rintro (⟨h1, h2, h3⟩ | h4)
      · exact Or.inl ⟨h1, h2, h.2 h3⟩
      · exact Or.inr h4
  unfold highInf
  rw [hset]

/-- `lowSup` is upper semicontinuous: from `lowSup x < c` one can move a little in the `x`
direction keeping `lowSup < c`, because `B` is closed and confined to the strip. -/
private lemma lowSup_usc {a b : ℝ} (hab : a ≤ b) {B : Set (ℝ × ℝ)} (hB : IsClosed B)
    (hsubB : B ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b}) :
    UpperSemicontinuous (lowSup a b B) := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro c
  rw [Metric.isOpen_iff]
  intro x hx
  simp only [Set.mem_preimage, Set.mem_Iio] at hx
  by_cases hbc : b < c
  · exact ⟨1, one_pos, fun y _ => lt_of_le_of_lt (lowSup_le hab B y) hbc⟩
  · push_neg at hbc
    set m : ℝ := (lowSup a b B x + c) / 2 with hm
    have hmx : lowSup a b B x < m := by rw [hm]; linarith
    have hmc : m < c := by rw [hm]; linarith
    have ham : a < m := lt_of_le_of_lt (le_lowSup hab B x) hmx
    have hKcomp : IsCompact ({x} ×ˢ Icc m b : Set (ℝ × ℝ)) :=
      isCompact_singleton.prod isCompact_Icc
    have hKsub : ({x} ×ˢ Icc m b : Set (ℝ × ℝ)) ⊆ Bᶜ := by
      rintro ⟨px, py⟩ ⟨hp1, hp2⟩
      rw [Set.mem_compl_iff]
      intro hpB
      have hpx : px = x := by simpa using hp1
      have key : py ≤ lowSup a b B x := by
        rw [← hpx]
        exact le_lowSup_of_mem hab hpB (le_trans (le_of_lt ham) hp2.1) hp2.2
      linarith [key, hmx, hp2.1]
    obtain ⟨δ, hδpos, hδsub⟩ := hKcomp.exists_thickening_subset_open hB.isOpen_compl hKsub
    refine ⟨δ, hδpos, fun x' hx' => ?_⟩
    have hx'' : dist x' x < δ := Metric.mem_ball.mp hx'
    have key : lowSup a b B x' ≤ m := by
      apply csSup_le
      · exact ⟨a, Or.inr rfl⟩
      · rintro y (hy | rfl)
        · by_contra hcon
          push_neg at hcon
          have hzK : (x, y) ∈ ({x} ×ˢ Icc m b : Set (ℝ × ℝ)) :=
            ⟨by simp, ⟨le_of_lt hcon, hy.2.1⟩⟩
          have hmemth : (x', y) ∈ thickening δ ({x} ×ˢ Icc m b : Set (ℝ × ℝ)) := by
            rw [Metric.mem_thickening_iff]
            exact ⟨(x, y), hzK, by rw [dist_prod_same_right]; exact hx''⟩
          have hnot : (x', y) ∉ B := by simpa using hδsub hmemth
          exact hnot hy.2.2
        · exact le_of_lt ham
    exact lt_of_le_of_lt key hmc

/-- `highInf` is lower semicontinuous. -/
private lemma highInf_lsc {a b : ℝ} (hab : a ≤ b) {A : Set (ℝ × ℝ)} (hA : IsClosed A)
    (hsubA : A ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b}) :
    LowerSemicontinuous (highInf a b A) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro c
  rw [Metric.isOpen_iff]
  intro x hx
  simp only [Set.mem_preimage, Set.mem_Ioi] at hx
  by_cases hca : c < a
  · exact ⟨1, one_pos, fun y _ => lt_of_lt_of_le hca (le_highInf hab A y)⟩
  · push_neg at hca
    set m : ℝ := (c + highInf a b A x) / 2 with hm
    have hcm : c < m := by rw [hm]; linarith
    have hmhi : m < highInf a b A x := by rw [hm]; linarith
    have ham : a < m := lt_of_le_of_lt hca hcm
    have hmb : m ≤ b := le_trans (le_of_lt hmhi) (highInf_le hab A x)
    have hKcomp : IsCompact ({x} ×ˢ Icc a m : Set (ℝ × ℝ)) :=
      isCompact_singleton.prod isCompact_Icc
    have hKsub : ({x} ×ˢ Icc a m : Set (ℝ × ℝ)) ⊆ Aᶜ := by
      rintro ⟨px, py⟩ ⟨hp1, hp2⟩
      rw [Set.mem_compl_iff]
      intro hpA
      have hpx : px = x := by simpa using hp1
      have key : highInf a b A x ≤ py := by
        rw [← hpx]
        exact highInf_le_of_mem hab hpA hp2.1 (le_trans hp2.2 hmb)
      linarith [key, hmhi, hp2.2]
    obtain ⟨δ, hδpos, hδsub⟩ := hKcomp.exists_thickening_subset_open hA.isOpen_compl hKsub
    refine ⟨δ, hδpos, fun x' hx' => ?_⟩
    have hx'' : dist x' x < δ := Metric.mem_ball.mp hx'
    have key : m ≤ highInf a b A x' := by
      apply le_csInf
      · exact ⟨b, Or.inr rfl⟩
      · rintro y (hy | rfl)
        · by_contra hcon
          push_neg at hcon
          have hzK : (x, y) ∈ ({x} ×ˢ Icc a m : Set (ℝ × ℝ)) :=
            ⟨by simp, ⟨hy.1, le_of_lt hcon⟩⟩
          have hmemth : (x', y) ∈ thickening δ ({x} ×ˢ Icc a m : Set (ℝ × ℝ)) := by
            rw [Metric.mem_thickening_iff]
            exact ⟨(x, y), hzK, by rw [dist_prod_same_right]; exact hx''⟩
          have hnot : (x', y) ∉ A := by simpa using hδsub hmemth
          exact hnot hy.2.2
        · exact hmb
    exact lt_of_lt_of_le hcm key

/-- **A periodic graph between two vertically separated periodic closed sets.**

Let `A`, `B` be closed, `p`-periodic subsets of the closed strip `a ≤ y ≤ b` of the plane, with
`A` lying strictly above `B` in every column.  Then there is a continuous path `G` in the strip
from `(x₀, y₀)` to `(x₀ + p, y₀)` (same height) avoiding `A ∪ B`. -/
theorem periodic_graph_between_separated_sets {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {A B : Set (ℝ × ℝ)} (hA : IsClosed A) (hB : IsClosed B)
    (hsubA : A ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hsubB : B ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hperA : ∀ q : ℝ × ℝ, q ∈ A ↔ (q.1 + p, q.2) ∈ A)
    (hperB : ∀ q : ℝ × ℝ, q ∈ B ↔ (q.1 + p, q.2) ∈ B)
    (hsep : ∀ x : ℝ,
      sSup ({y : ℝ | a ≤ y ∧ y ≤ b ∧ (x, y) ∈ B} ∪ {a}) <
        sInf ({y : ℝ | a ≤ y ∧ y ≤ b ∧ (x, y) ∈ A} ∪ {b})) :
    ∃ G : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
      (∀ t, a ≤ (G t).2 ∧ (G t).2 ≤ b) ∧
      (G 1).1 = (G 0).1 + p ∧ (G 1).2 = (G 0).2 ∧ ∀ t, G t ∉ A ∪ B := by
  have hab' : a ≤ b := hab.le
  have husc := lowSup_usc (a := a) (b := b) hab' hB hsubB
  have hlsc := highInf_lsc (a := a) (b := b) hab' hA hsubA
  have hsep' : ∀ x : ℝ, lowSup a b B x < highInf a b A x := fun x => hsep x
  let V : Set (ℝ × ℝ) :=
    {q : ℝ × ℝ | lowSup a b B q.1 < q.2} ∩ {q : ℝ × ℝ | q.2 < highInf a b A q.1}
  have hVopen : IsOpen V := by
    have h1 : IsOpen {q : ℝ × ℝ | lowSup a b B q.1 < q.2} := by
      have hset : {q : ℝ × ℝ | lowSup a b B q.1 < q.2}
          = ⋃ m : ℚ, ({q : ℝ × ℝ | lowSup a b B q.1 < (m : ℝ)}
              ∩ {q : ℝ × ℝ | (m : ℝ) < q.2}) := by
        ext q
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
        constructor
        · intro hq
          obtain ⟨m, hm1, hm2⟩ := exists_rat_btwn hq
          exact ⟨m, hm1, hm2⟩
        · rintro ⟨m, hm1, hm2⟩
          exact lt_trans hm1 hm2
      rw [hset]
      exact isOpen_iUnion fun m =>
        ((husc.isOpen_preimage (m : ℝ)).preimage continuous_fst).inter
          (isOpen_lt continuous_const continuous_snd)
    have h2 : IsOpen {q : ℝ × ℝ | q.2 < highInf a b A q.1} := by
      have hset : {q : ℝ × ℝ | q.2 < highInf a b A q.1}
          = ⋃ m : ℚ, ({q : ℝ × ℝ | q.2 < (m : ℝ)}
              ∩ {q : ℝ × ℝ | (m : ℝ) < highInf a b A q.1}) := by
        ext q
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
        constructor
        · intro hq
          obtain ⟨m, hm1, hm2⟩ := exists_rat_btwn hq
          exact ⟨m, hm1, hm2⟩
        · rintro ⟨m, hm1, hm2⟩
          exact lt_trans hm1 hm2
      rw [hset]
      exact isOpen_iUnion fun m =>
        (isOpen_lt continuous_snd continuous_const).inter
          ((hlsc.isOpen_preimage (m : ℝ)).preimage continuous_fst)
    change IsOpen ({q : ℝ × ℝ | lowSup a b B q.1 < q.2}
      ∩ {q : ℝ × ℝ | q.2 < highInf a b A q.1})
    exact h1.inter h2
  have hVper : ∀ q : ℝ × ℝ, q ∈ V ↔ (q.1 + p, q.2) ∈ V := by
    intro q
    have hlo := lowSup_periodic (a := a) (b := b) (p := p) hperB q.1
    have hhi := highInf_periodic (a := a) (b := b) (p := p) hperA q.1
    simp only [V, Set.mem_inter_iff, Set.mem_setOf_eq, hlo, hhi]
  have hVconv : ∀ x : ℝ, Convex ℝ {y : ℝ | (x, y) ∈ V} := by
    intro x
    have hset : {y : ℝ | (x, y) ∈ V} = Ioo (lowSup a b B x) (highInf a b A x) := by
      ext y
      simp only [V, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ioo]
    rw [hset]
    exact convex_Ioo _ _
  have hVne : ∀ x : ℝ, ∃ y : ℝ, (x, y) ∈ V := by
    intro x
    refine ⟨(lowSup a b B x + highInf a b A x) / 2, ?_⟩
    have h := hsep' x
    simp only [V, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor <;> linarith
  obtain ⟨g, hgcont, hgper, hgmem⟩ :=
    convex_fibre_periodic_section hp hVopen hVper hVconv hVne
  let F : Set.Icc (0 : ℝ) 1 → ℝ × ℝ := fun t => (p * (t : ℝ), g (p * (t : ℝ)))
  have hFcont : Continuous F := by
    apply Continuous.prodMk
    · exact continuous_const.mul continuous_subtype_val
    · exact hgcont.comp (continuous_const.mul continuous_subtype_val)
  let G : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ) := ⟨F, hFcont⟩
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro t
    have hmem := hgmem (p * (t : ℝ))
    simp only [V, Set.mem_inter_iff, Set.mem_setOf_eq] at hmem
    obtain ⟨h1, h2⟩ := hmem
    change a ≤ (F t).2 ∧ (F t).2 ≤ b
    refine ⟨?_, ?_⟩
    · change a ≤ g (p * (t : ℝ))
      exact le_trans (le_lowSup hab' B _) (le_of_lt h1)
    · change g (p * (t : ℝ)) ≤ b
      exact le_trans (le_of_lt h2) (highInf_le hab' A _)
  · change (F 1).1 = (F 0).1 + p
    simp only [F]
    norm_num
  · change (F 1).2 = (F 0).2
    simp only [F]
    have h1 : p * ((1 : Set.Icc (0 : ℝ) 1) : ℝ) = p := by norm_num
    have h0 : p * ((0 : Set.Icc (0 : ℝ) 1) : ℝ) = 0 := by norm_num
    rw [h1, h0]
    simpa using hgper 0
  · intro t
    have hmem := hgmem (p * (t : ℝ))
    simp only [V, Set.mem_inter_iff, Set.mem_setOf_eq] at hmem
    obtain ⟨h1, h2⟩ := hmem
    have hag : a ≤ g (p * (t : ℝ)) := le_trans (le_lowSup hab' B _) (le_of_lt h1)
    have hgb : g (p * (t : ℝ)) ≤ b := le_trans (le_of_lt h2) (highInf_le hab' A _)
    change F t ∉ A ∪ B
    simp only [Set.mem_union, not_or]
    constructor
    · intro hAmem
      exact absurd (highInf_le_of_mem hab' hAmem hag hgb) (not_le.mpr h2)
    · intro hBmem
      exact absurd (le_lowSup_of_mem hab' hBmem hag hgb) (not_le.mpr h1)

end Commons.Topology.Strip