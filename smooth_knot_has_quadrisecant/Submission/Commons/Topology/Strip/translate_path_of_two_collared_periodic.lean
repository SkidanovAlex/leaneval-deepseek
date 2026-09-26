import Mathlib
import Submission.Commons.Topology.Strip.closed_periodic_bounded_away_from_level
import Submission.Commons.Topology.Strip.periodic_graph_between_separated_sets
import Submission.Commons.Topology.Strip.barrier_bottom_top_of_no_left_right
import Submission.Commons.Topology.Strip.path_shift_meets
import Submission.Commons.Topology.Strip.path_meets_translate
import Submission.Commons.Topology.Strip.wall_blocks_translate_path
import Submission.Commons.Topology.Strip.exists_translate_path_of_ess_of_cover

namespace Commons.Topology.Strip

open Set

/-- **Free level.**  If a horizontal level circle `{q.2 = c}` (with `a ≤ c ≤ b`) avoids `P ∪ Q`,
the horizontal segment at that level is a translate path. -/
theorem exists_translate_path_of_free_level {p a b : ℝ} {c : ℝ} (hp : 0 < p) (hab : a < b)
    (hac : a ≤ c) (hcb : c ≤ b) {P Q : Set (ℝ × ℝ)}
    (hfree : ∀ x : ℝ, (x, c) ∉ P ∪ Q) :
    ∃ z : ℝ × ℝ, a ≤ z.2 ∧ z.2 ≤ b ∧ z ∉ P ∪ Q ∧
      ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
        γ 0 = z ∧ γ 1 = (z.1 + p, z.2) ∧
        (∀ t, a ≤ (γ t).2 ∧ (γ t).2 ≤ b) ∧ ∀ t, γ t ∉ P ∪ Q := by
  refine ⟨((0 : ℝ), c), hac, hcb, hfree 0, ?_⟩
  refine ⟨⟨fun t : Set.Icc (0 : ℝ) 1 => ((t : ℝ) * p, c), by fun_prop⟩, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro t; exact ⟨hac, hcb⟩
  · intro t; exact hfree _

/-- **Wrapper of `periodic_graph_between_separated_sets` in the target shape.** -/
theorem exists_translate_path_of_separated {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {A B : Set (ℝ × ℝ)} (hA : IsClosed A) (hB : IsClosed B)
    (hsubA : A ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hsubB : B ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hperA : ∀ q : ℝ × ℝ, q ∈ A ↔ (q.1 + p, q.2) ∈ A)
    (hperB : ∀ q : ℝ × ℝ, q ∈ B ↔ (q.1 + p, q.2) ∈ B)
    (hsep : ∀ x : ℝ, sSup ({y : ℝ | a ≤ y ∧ y ≤ b ∧ (x, y) ∈ B} ∪ {a})
        < sInf ({y : ℝ | a ≤ y ∧ y ≤ b ∧ (x, y) ∈ A} ∪ {b})) :
    ∃ z : ℝ × ℝ, a ≤ z.2 ∧ z.2 ≤ b ∧ z ∉ A ∪ B ∧
      ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
        γ 0 = z ∧ γ 1 = (z.1 + p, z.2) ∧
        (∀ t, a ≤ (γ t).2 ∧ (γ t).2 ≤ b) ∧ ∀ t, γ t ∉ A ∪ B := by
  obtain ⟨G, hstrip, h1, h2, hnot⟩ :=
    periodic_graph_between_separated_sets hp hab hA hB hsubA hsubB hperA hperB hsep
  exact ⟨G 0, (hstrip 0).1, (hstrip 0).2, hnot 0, G, rfl, Prod.ext h1 h2, hstrip, hnot⟩

/-- **A free interval in a column.**  Two disjoint closed subsets of the plane leave a free interval in
every column `{x} × [a,b]`, provided neither of them covers the column: the two slices are closed and
disjoint, so by connectedness of `[a,b]` they cannot cover it, and the complement (open) contains a
nondegenerate interval.

At an interlocking column of the saturated configuration both slices are nonempty and neither covers
the column (`P` avoids the top line, `Q` the bottom line), so this is the free interval that a
zig-zag translate path has to thread through. -/
theorem exists_free_interval_of_closed_disjoint {a b : ℝ} (hab : a < b) {P Q : Set (ℝ × ℝ)}
    (hP : IsClosed P) (hQ : IsClosed Q) (hdisj : Disjoint P Q) (x : ℝ)
    (hP' : ∃ y : ℝ, a ≤ y ∧ y ≤ b ∧ ((x, y) : ℝ × ℝ) ∉ P)
    (hQ' : ∃ y : ℝ, a ≤ y ∧ y ≤ b ∧ ((x, y) : ℝ × ℝ) ∉ Q) :
    ∃ y₁ y₂ : ℝ, a ≤ y₁ ∧ y₁ < y₂ ∧ y₂ ≤ b ∧
      ∀ y ∈ Set.Icc y₁ y₂, ((x, y) : ℝ × ℝ) ∉ P ∪ Q := by
  have hSPcl : IsClosed {y : ℝ | ((x, y) : ℝ × ℝ) ∈ P} := hP.preimage (by fun_prop)
  have hSQcl : IsClosed {y : ℝ | ((x, y) : ℝ × ℝ) ∈ Q} := hQ.preimage (by fun_prop)
  -- the column cannot be covered by the two slices
  have hne : ∃ y ∈ Set.Icc a b, ((x, y) : ℝ × ℝ) ∉ P ∪ Q := by
    by_contra hcon
    push_neg at hcon
    have hcover : Set.Icc a b ⊆ {y : ℝ | ((x, y) : ℝ × ℝ) ∈ P} ∪ {y | ((x, y) : ℝ × ℝ) ∈ Q} := by
      intro y hy
      rcases hcon y hy with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hdisj' : Set.Icc a b ∩ ({y : ℝ | ((x, y) : ℝ × ℝ) ∈ P}
        ∩ {y : ℝ | ((x, y) : ℝ × ℝ) ∈ Q}) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨-, hyP, hyQ⟩
      exact Set.disjoint_left.mp hdisj hyP hyQ
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp isPreconnected_Icc)
        _ _ hSPcl hSQcl hcover hdisj' with h | h
    · obtain ⟨y, hy1, hy2, hyP⟩ := hP'
      exact hyP (h ⟨hy1, hy2⟩)
    · obtain ⟨y, hy1, hy2, hyQ⟩ := hQ'
      exact hyQ (h ⟨hy1, hy2⟩)
  obtain ⟨y₀, hy₀I, hy₀free⟩ := hne
  have hopen : IsOpen {y : ℝ | ((x, y) : ℝ × ℝ) ∉ P ∪ Q} := by
    have h : {y : ℝ | ((x, y) : ℝ × ℝ) ∉ P ∪ Q}
        = ((fun y : ℝ => ((x, y) : ℝ × ℝ)) ⁻¹' (P ∪ Q))ᶜ := by
      ext y; simp
    rw [h]
    exact ((hP.union hQ).preimage (by fun_prop)).isOpen_compl
  obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hopen y₀ hy₀free
  refine ⟨max a (y₀ - ε / 2), min b (y₀ + ε / 2), le_max_left _ _, ?_, min_le_left _ _, ?_⟩
  · have h1 : max a (y₀ - ε / 2) < y₀ + ε / 2 :=
      max_lt (by linarith [hy₀I.1]) (by linarith)
    have h2 : max a (y₀ - ε / 2) < b :=
      max_lt hab (by linarith [hy₀I.2])
    exact lt_min h2 h1
  · intro y hy
    refine hε ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have h1 : y₀ - ε / 2 ≤ max a (y₀ - ε / 2) := le_max_right _ _
    have h2 : min b (y₀ + ε / 2) ≤ y₀ + ε / 2 := min_le_right _ _
    constructor <;> linarith [hy.1, hy.2]

/-- **The free interval in a collared column (the front edge of the residual).**  In the saturated
configuration the two collars are *literally* the two non-coverage hypotheses of
`exists_free_interval_of_closed_disjoint`:

* `P ⊆ {q | q.2 ≤ mP}` with `mP < b` gives `(x, b) ∉ P`, so the column's top point is `P`-free;
* `Q ⊆ {q | mQ ≤ q.2}` with `a < mQ` gives `(x, a) ∉ Q`, so the column's bottom point is `Q`-free.

Hence at *every* column — in particular at an interlocking column `x₀` (`σ x₀ ≤ τ x₀`) — there is a
nondegenerate free interval `[y₁, y₂]` inside the column.  This is the interval that the zig-zag
translate path of the residual has to thread through, and it is available with no extra hypotheses. -/
theorem exists_free_interval_of_collared_column {a b mP mQ : ℝ} (hab : a < b) (hmPb : mP < b)
    (hamQ : a < mQ) {P Q : Set (ℝ × ℝ)} (hP : IsClosed P) (hQ : IsClosed Q)
    (hdisj : Disjoint P Q)
    (hsubP : P ⊆ {q : ℝ × ℝ | q.2 ≤ mP}) (hsubQ : Q ⊆ {q : ℝ × ℝ | mQ ≤ q.2}) (x : ℝ) :
    ∃ y₁ y₂ : ℝ, a ≤ y₁ ∧ y₁ < y₂ ∧ y₂ ≤ b ∧
      ∀ y ∈ Set.Icc y₁ y₂, ((x, y) : ℝ × ℝ) ∉ P ∪ Q :=
  exists_free_interval_of_closed_disjoint hab hP hQ hdisj x
    ⟨b, le_of_lt hab, le_refl b, fun h => absurd (hsubP h) (not_le.mpr hmPb)⟩
    ⟨a, le_refl a, le_of_lt hab, fun h => absurd (hsubQ h) (not_le.mpr hamQ)⟩

/-- **Room around a free interval.**  If `[y₁, y₂]` is a free interval at the column `x₀`, then the
same interval stays free for all columns within a definite distance of `x₀`: the free set is open and
`{x₀} × [y₁, y₂]` is compact, so a uniform `cthickening` fits inside it.

This is the local "collar room" ingredient: it takes the free interval of
`exists_free_interval_of_collared_column` as an explicit hypothesis and produces the box in which a
zig-zag path can step sideways while staying free. -/
theorem exists_free_box_of_free_interval {P Q : Set (ℝ × ℝ)} (hP : IsClosed P) (hQ : IsClosed Q)
    {x₀ y₁ y₂ : ℝ} (hfree : ∀ y ∈ Set.Icc y₁ y₂, ((x₀, y) : ℝ × ℝ) ∉ P ∪ Q) :
    ∃ ε > 0, ∀ x : ℝ, ∀ y ∈ Set.Icc y₁ y₂, |x - x₀| < ε → ((x, y) : ℝ × ℝ) ∉ P ∪ Q := by
  set K : Set (ℝ × ℝ) := (fun y : ℝ => ((x₀, y) : ℝ × ℝ)) '' Set.Icc y₁ y₂ with hK
  have hKcomp : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hU : IsOpen {q : ℝ × ℝ | q ∉ P ∪ Q} := (hP.union hQ).isOpen_compl
  have hKU : K ⊆ {q : ℝ × ℝ | q ∉ P ∪ Q} := by
    rintro q ⟨y, hy, rfl⟩
    exact hfree y hy
  obtain ⟨δ, hδpos, hδ⟩ := hKcomp.exists_cthickening_subset_open hU hKU
  refine ⟨δ / 2, by linarith, ?_⟩
  intro x y hy hx
  refine hδ ?_
  have hmem : ((x₀, y) : ℝ × ℝ) ∈ K := ⟨y, hy, rfl⟩
  have hdx : dist ((x, y) : ℝ × ℝ) ((x₀, y) : ℝ × ℝ) = |x - x₀| := by
    rw [Prod.dist_eq]
    simp [Real.dist_eq]
  rw [Metric.mem_cthickening_iff]
  calc Metric.infEDist ((x, y) : ℝ × ℝ) K
      ≤ edist ((x, y) : ℝ × ℝ) ((x₀, y) : ℝ × ℝ) := Metric.infEDist_le_edist_of_mem hmem
    _ = ENNReal.ofReal (dist ((x, y) : ℝ × ℝ) ((x₀, y) : ℝ × ℝ)) := edist_dist _ _
    _ = ENNReal.ofReal |x - x₀| := by rw [hdx]
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.mp hx).2])

/-- **Room around a free interval, right side.**  One-sided form of `exists_free_box_of_free_interval`,
which is the shape a left-to-right zig-zag consumes. -/
theorem exists_free_box_right_of_free_interval {P Q : Set (ℝ × ℝ)} (hP : IsClosed P)
    (hQ : IsClosed Q) {x₀ y₁ y₂ : ℝ}
    (hfree : ∀ y ∈ Set.Icc y₁ y₂, ((x₀, y) : ℝ × ℝ) ∉ P ∪ Q) :
    ∃ ε > 0, ∀ x : ℝ, x₀ < x → x < x₀ + ε → ∀ y ∈ Set.Icc y₁ y₂,
      ((x, y) : ℝ × ℝ) ∉ P ∪ Q := by
  obtain ⟨ε, hε, h⟩ := exists_free_box_of_free_interval hP hQ hfree
  exact ⟨ε, hε, fun x h1 h2 y hy => h x y hy (by rw [abs_lt]; exact ⟨by linarith, by linarith⟩)⟩

/-! ### The collar bands, in point form

The two collars say exactly where each obstacle can be: above `mP` only `Q` may obstruct, and below
`mQ` only `P` may obstruct.  These are the consumed form of the collars for the "reach" argument. -/

/-- **Top collar fact.**  Above `mP`, `P` is absent. -/
lemma collar_top_notMem {mP : ℝ} {P : Set (ℝ × ℝ)} (hsubP : P ⊆ {q : ℝ × ℝ | q.2 ≤ mP})
    {x y : ℝ} (hy : mP < y) : ((x, y) : ℝ × ℝ) ∉ P :=
  fun h => absurd (hsubP h) (not_le.mpr hy)

/-- **Bottom collar fact.**  Below `mQ`, `Q` is absent. -/
lemma collar_bot_notMem {mQ : ℝ} {Q : Set (ℝ × ℝ)} (hsubQ : Q ⊆ {q : ℝ × ℝ | mQ ≤ q.2})
    {x y : ℝ} (hy : y < mQ) : ((x, y) : ℝ × ℝ) ∉ Q :=
  fun h => absurd (hsubQ h) (not_le.mpr hy)

/-- **The top collar band's free set is the complement of `Q` alone.** -/
lemma mem_collar_top_iff {mP : ℝ} {P Q : Set (ℝ × ℝ)} (hsubP : P ⊆ {q : ℝ × ℝ | q.2 ≤ mP})
    {x y : ℝ} (hy : mP < y) : ((x, y) : ℝ × ℝ) ∈ P ∪ Q ↔ ((x, y) : ℝ × ℝ) ∈ Q := by
  constructor
  · rintro (h | h)
    · exact absurd (hsubP h) (not_le.mpr hy)
    · exact h
  · exact Or.inr

/-- **The bottom collar band's free set is the complement of `P` alone.** -/
lemma mem_collar_bot_iff {mQ : ℝ} {P Q : Set (ℝ × ℝ)} (hsubQ : Q ⊆ {q : ℝ × ℝ | mQ ≤ q.2})
    {x y : ℝ} (hy : y < mQ) : ((x, y) : ℝ × ℝ) ∈ P ∪ Q ↔ ((x, y) : ℝ × ℝ) ∈ P := by
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd (hsubQ h) (not_le.mpr hy)
  · exact Or.inl

/-- **The collar-band step.**  Assemble the room lemma with the two collar facts: given the free
interval `[y₁, y₂]` at the column `x₀`, the whole interval stays free in the box of radius `ε` around
`x₀`; restricted to the top collar band `(mP, b]` the surviving free points have `Q` as their *only*
possible obstacle, and restricted to the bottom collar band `[a, mQ)` they have `P` as their only
possible obstacle.  So the part of the free interval that already lies in a collar band is a genuine
free part of that collar band, and it is connected inside the (convex) free box. -/
theorem free_box_collar_step {a b mP mQ : ℝ} {P Q : Set (ℝ × ℝ)} (hP : IsClosed P)
    (hQ : IsClosed Q) (hsubP : P ⊆ {q : ℝ × ℝ | q.2 ≤ mP})
    (hsubQ : Q ⊆ {q : ℝ × ℝ | mQ ≤ q.2})
    {x₀ y₁ y₂ : ℝ} (hfree : ∀ y ∈ Set.Icc y₁ y₂, ((x₀, y) : ℝ × ℝ) ∉ P ∪ Q) :
    ∃ ε > 0, ∀ x : ℝ, |x - x₀| < ε →
      (∀ y ∈ Set.Icc y₁ y₂, ((x, y) : ℝ × ℝ) ∉ P ∪ Q) ∧
      (∀ y : ℝ, mP < y → y ≤ y₂ → (((x, y) : ℝ × ℝ) ∈ P ∪ Q ↔ ((x, y) : ℝ × ℝ) ∈ Q)) ∧
      (∀ y : ℝ, y₁ ≤ y → y < mQ → (((x, y) : ℝ × ℝ) ∈ P ∪ Q ↔ ((x, y) : ℝ × ℝ) ∈ P)) := by
  obtain ⟨ε, hε, hbox⟩ := exists_free_box_of_free_interval hP hQ hfree
  refine ⟨ε, hε, ?_⟩
  intro x hx
  refine ⟨?_, ?_, ?_⟩
  · intro y hy; exact hbox x y hy hx
  · intro y hy _; exact mem_collar_top_iff (x := x) hsubP hy
  · intro y _ hy; exact mem_collar_bot_iff (x := x) hsubQ hy

/-- **The separable (non-interlocking) branch.**  If no column is interlocking — every `P`-point of a
column lies strictly below every `Q`-point of the same column, inside the strip — then a translate
path exists.

This discharges the whole non-interlocking part of the residual: combined with the free-meridian cut
and the every-meridian residual, the saturated case is covered by
`exists_translate_path_of_separated_columns`, `exists_translate_path_of_free_meridian` and
`exists_translate_path_of_every_meridian_met`, and only the *interlocking* columns
(`∃ x, σ x ≤ τ x`, where `τ` is the ceiling of `P` and `σ` the floor of `Q`) are left. -/
theorem exists_translate_path_of_separated_columns {p a b mP mQ : ℝ} (hp : 0 < p) (hab : a < b)
    (hmQmP : mQ ≤ mP) (hamQ : a < mQ) (hmPb : mP < b) (hamP : a ≤ mP)
    {P Q : Set (ℝ × ℝ)} (hP : IsClosed P) (hQ : IsClosed Q) (hdisj : Disjoint P Q)
    (hperP : ∀ q : ℝ × ℝ, q ∈ P ↔ (q.1 + p, q.2) ∈ P)
    (hperQ : ∀ q : ℝ × ℝ, q ∈ Q ↔ (q.1 + p, q.2) ∈ Q)
    (hsubP : P ⊆ {q : ℝ × ℝ | q.2 ≤ mP})
    (hsubQ : Q ⊆ {q : ℝ × ℝ | mQ ≤ q.2})
    (hsep : ∀ x : ℝ, ∀ yP yQ : ℝ, a ≤ yP → yP ≤ b → ((x, yP) : ℝ × ℝ) ∈ P →
      a ≤ yQ → yQ ≤ b → ((x, yQ) : ℝ × ℝ) ∈ Q → yP < yQ) :
    ∃ z : ℝ × ℝ, a ≤ z.2 ∧ z.2 ≤ b ∧ z ∉ P ∪ Q ∧
      ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
        γ 0 = z ∧ γ 1 = (z.1 + p, z.2) ∧
        (∀ t, a ≤ (γ t).2 ∧ (γ t).2 ≤ b) ∧ ∀ t, γ t ∉ P ∪ Q := by
  set S : Set (ℝ × ℝ) := {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} with hS
  have hScl : IsClosed S := isClosed_Icc.preimage continuous_snd
  have hSp : ∀ q : ℝ × ℝ, q ∈ S ↔ (q.1 + p, q.2) ∈ S := by
    intro q; simp only [hS, Set.mem_ofPred_eq]
  -- the `sSup`/`sInf` separation needed by the graph construction
  have hsep' : ∀ x : ℝ,
      sSup ({y : ℝ | a ≤ y ∧ y ≤ b ∧ ((x, y) : ℝ × ℝ) ∈ P ∩ S} ∪ {a})
        < sInf ({y : ℝ | a ≤ y ∧ y ≤ b ∧ ((x, y) : ℝ × ℝ) ∈ Q ∩ S} ∪ {b}) := by
    intro x
    have hBP_eq : {y : ℝ | a ≤ y ∧ y ≤ b ∧ ((x, y) : ℝ × ℝ) ∈ P ∩ S}
        = {y : ℝ | a ≤ y ∧ y ≤ b ∧ ((x, y) : ℝ × ℝ) ∈ P} := by
      ext y
      simp [hS, and_assoc, and_comm, and_left_comm]
    have hBQ_eq : {y : ℝ | a ≤ y ∧ y ≤ b ∧ ((x, y) : ℝ × ℝ) ∈ Q ∩ S}
        = {y : ℝ | a ≤ y ∧ y ≤ b ∧ ((x, y) : ℝ × ℝ) ∈ Q} := by
      ext y
      simp [hS, and_assoc, and_comm, and_left_comm]
    rw [hBP_eq, hBQ_eq]
    set BP : Set ℝ := {y : ℝ | a ≤ y ∧ y ≤ b ∧ ((x, y) : ℝ × ℝ) ∈ P} with hBP
    set BQ : Set ℝ := {y : ℝ | a ≤ y ∧ y ≤ b ∧ ((x, y) : ℝ × ℝ) ∈ Q} with hBQ
    have hsP_cl : IsClosed {y : ℝ | ((x, y) : ℝ × ℝ) ∈ P} :=
      hP.preimage (by fun_prop)
    have hsQ_cl : IsClosed {y : ℝ | ((x, y) : ℝ × ℝ) ∈ Q} :=
      hQ.preimage (by fun_prop)
    have hBPcl : IsClosed BP := by
      have h3 : {y : ℝ | a ≤ y ∧ y ≤ b ∧ ((x, y) : ℝ × ℝ) ∈ P}
          = {y : ℝ | a ≤ y ∧ y ≤ b} ∩ {y : ℝ | ((x, y) : ℝ × ℝ) ∈ P} := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
        tauto
      rw [hBP, h3]
      exact isClosed_Icc.inter hsP_cl
    have hBQcl : IsClosed BQ := by
      have h3 : {y : ℝ | a ≤ y ∧ y ≤ b ∧ ((x, y) : ℝ × ℝ) ∈ Q}
          = {y : ℝ | a ≤ y ∧ y ≤ b} ∩ {y : ℝ | ((x, y) : ℝ × ℝ) ∈ Q} := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
        tauto
      rw [hBQ, h3]
      exact isClosed_Icc.inter hsQ_cl
    have hsup_le : sSup (BP ∪ {a}) ≤ mP := by
      apply csSup_le ⟨a, Or.inr rfl⟩
      rintro y (hy | rfl)
      · exact hsubP hy.2.2
      · exact hamP
    have hle_inf : mQ ≤ sInf (BQ ∪ {b}) := by
      apply le_csInf ⟨b, Or.inr rfl⟩
      rintro y (hy | rfl)
      · exact hsubQ hy.2.2
      · exact le_trans hmQmP hmPb.le
    rcases BP.eq_empty_or_nonempty with hBPe | hBPne
    · have hsup_a : sSup (BP ∪ {a}) = a := by rw [hBPe, Set.empty_union, csSup_singleton]
      rw [hsup_a]
      exact lt_of_lt_of_le hamQ hle_inf
    rcases BQ.eq_empty_or_nonempty with hBQe | hBQne
    · have hinf_b : sInf (BQ ∪ {b}) = b := by rw [hBQe, Set.empty_union, csInf_singleton]
      rw [hinf_b]
      exact lt_of_le_of_lt hsup_le hmPb
    obtain ⟨yP, hyPmem, hyPmax⟩ :=
      (isCompact_Icc.of_isClosed_subset hBPcl (fun y hy => ⟨hy.1, hy.2.1⟩)).exists_isMaxOn
        hBPne continuous_id.continuousOn
    obtain ⟨yQ, hyQmem, hyQmin⟩ :=
      (isCompact_Icc.of_isClosed_subset hBQcl (fun y hy => ⟨hy.1, hy.2.1⟩)).exists_isMinOn
        hBQne continuous_id.continuousOn
    have hlt : yP < yQ :=
      hsep x yP yQ hyPmem.1 hyPmem.2.1 hyPmem.2.2 hyQmem.1 hyQmem.2.1 hyQmem.2.2
    have hsup_eq : sSup (BP ∪ {a}) = yP := by
      apply le_antisymm
      · apply csSup_le ⟨yP, Or.inl hyPmem⟩
        rintro y (hy | rfl)
        · exact hyPmax hy
        · exact hyPmem.1
      · exact le_csSup ⟨b, fun y hy => by
          rcases hy with hy | rfl
          · exact hy.2.1
          · exact hab.le⟩ (Or.inl hyPmem)
    have hinf_eq : sInf (BQ ∪ {b}) = yQ := by
      apply le_antisymm
      · exact csInf_le ⟨a, fun y hy => by
          rcases hy with hy | rfl
          · exact hy.1
          · exact hab.le⟩ (Or.inl hyQmem)
      · apply le_csInf ⟨yQ, Or.inl hyQmem⟩
        rintro y (hy | rfl)
        · exact hyQmin hy
        · exact hyQmem.2.1
    rw [hsup_eq, hinf_eq]
    exact hlt
  have hAcl : IsClosed (Q ∩ S) := hQ.inter hScl
  have hBcl : IsClosed (P ∩ S) := hP.inter hScl
  have hsubA : Q ∩ S ⊆ S := inter_subset_right
  have hsubB : P ∩ S ⊆ S := inter_subset_right
  have hperA : ∀ q : ℝ × ℝ, q ∈ Q ∩ S ↔ (q.1 + p, q.2) ∈ Q ∩ S := by
    intro q
    rw [Set.mem_inter_iff, Set.mem_inter_iff, hperQ q]
    exact ⟨fun h => ⟨h.1, (hSp q).mp h.2⟩, fun h => ⟨h.1, (hSp q).mpr h.2⟩⟩
  have hperB : ∀ q : ℝ × ℝ, q ∈ P ∩ S ↔ (q.1 + p, q.2) ∈ P ∩ S := by
    intro q
    rw [Set.mem_inter_iff, Set.mem_inter_iff, hperP q]
    exact ⟨fun h => ⟨h.1, (hSp q).mp h.2⟩, fun h => ⟨h.1, (hSp q).mpr h.2⟩⟩
  obtain ⟨z, hz1, hz2, hzAB, γ, hγ0, hγ1, hγbox, hγAB⟩ :=
    exists_translate_path_of_separated (A := Q ∩ S) (B := P ∩ S) hp hab hAcl hBcl hsubA hsubB
      hperA hperB hsep'
  refine ⟨z, hz1, hz2, ?_, γ, hγ0, hγ1, hγbox, ?_⟩
  · intro hz
    rcases hz with hzP | hzQ
    · exact hzAB (Or.inr ⟨hzP, hz1, hz2⟩)
    · exact hzAB (Or.inl ⟨hzQ, hz1, hz2⟩)
  · intro t hmem
    rcases hmem with hP' | hQ'
    · exact hγAB t (Or.inr ⟨hP', (hγbox t).1, (hγbox t).2⟩)
    · exact hγAB t (Or.inl ⟨hQ', (hγbox t).1, (hγbox t).2⟩)

/-- **Upper interface.**  If `P` lies below the level `c` and `Q` misses the level `c`, then a
translate path avoiding `P ∪ Q` exists: move the part of `Q` below `c` into the lower set and
apply the separated-sets construction. -/
theorem exists_translate_path_of_upper_interface {p a b c : ℝ} (hp : 0 < p) (hab : a < b)
    (hac : a ≤ c) (hcb : c < b)
    {P Q : Set (ℝ × ℝ)} (hP : IsClosed P) (hQ : IsClosed Q)
    (hsubP : P ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hsubQ : Q ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hdisj : Disjoint P Q)
    (hperP : ∀ q : ℝ × ℝ, q ∈ P ↔ (q.1 + p, q.2) ∈ P)
    (hperQ : ∀ q : ℝ × ℝ, q ∈ Q ↔ (q.1 + p, q.2) ∈ Q)
    (hcP : ∀ q ∈ P, q.2 ≤ c) (hcQ : ∀ q ∈ Q, q.2 ≠ c) :
    ∃ z : ℝ × ℝ, a ≤ z.2 ∧ z.2 ≤ b ∧ z ∉ P ∪ Q ∧
      ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
        γ 0 = z ∧ γ 1 = (z.1 + p, z.2) ∧
        (∀ t, a ≤ (γ t).2 ∧ (γ t).2 ≤ b) ∧ ∀ t, γ t ∉ P ∪ Q := by
  obtain ⟨δ, hδpos, hδsub⟩ :=
    closed_periodic_bounded_away_from_level (p := p) (a := a) (b := b) (c := c)
      hp hab hQ hsubQ hperQ hcQ
  set B : Set (ℝ × ℝ) := P ∪ (Q ∩ {q : ℝ × ℝ | q.2 ≤ c - δ}) with hBdef
  set A : Set (ℝ × ℝ) := Q ∩ {q : ℝ × ℝ | c + δ ≤ q.2} with hAdef
  have hAclosed : IsClosed A := by
    rw [hAdef]
    exact hQ.inter (isClosed_Ici.preimage continuous_snd)
  have hBclosed : IsClosed B := by
    rw [hBdef]
    exact hP.union (hQ.inter (isClosed_Iic.preimage continuous_snd))
  have hsubA : A ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} := by
    intro q hq; rw [hAdef] at hq; exact hsubQ hq.1
  have hsubB : B ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} := by
    intro q hq
    rw [hBdef] at hq
    rcases hq with hq | hq
    · exact hsubP hq
    · exact hsubQ hq.1
  have hperA : ∀ q : ℝ × ℝ, q ∈ A ↔ (q.1 + p, q.2) ∈ A := by
    intro q
    rw [hAdef]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(hperQ q).mp h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨(hperQ q).mpr h1, h2⟩
  have hperB : ∀ q : ℝ × ℝ, q ∈ B ↔ (q.1 + p, q.2) ∈ B := by
    intro q
    rw [hBdef]
    constructor
    · rintro (h1 | ⟨h1, h2⟩)
      · exact Or.inl ((hperP q).mp h1)
      · exact Or.inr ⟨(hperQ q).mp h1, h2⟩
    · rintro (h1 | ⟨h1, h2⟩)
      · exact Or.inl ((hperP q).mpr h1)
      · exact Or.inr ⟨(hperQ q).mpr h1, h2⟩
  have hAB : A ∪ B = P ∪ Q := by
    apply Set.Subset.antisymm
    · intro q hq
      rw [hAdef, hBdef] at hq
      rcases hq with hq | hq
      · exact Or.inr hq.1
      · rcases hq with hq | hq
        · exact Or.inl hq
        · exact Or.inr hq.1
    · intro q hq
      rcases hq with hq | hq
      · exact Or.inr (Or.inl hq)
      · rcases hδsub q hq with h | h
        · exact Or.inr (Or.inr ⟨hq, h⟩)
        · exact Or.inl ⟨hq, h⟩
  have hdisjAB : Disjoint A B := by
    rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
    rintro q ⟨hqA, hqB⟩
    rw [hAdef] at hqA
    rw [hBdef] at hqB
    rcases hqB with hqB | hqB
    · exact Set.disjoint_left.mp hdisj hqB hqA.1
    · have h1 : c + δ ≤ q.2 := hqA.2
      have h2 : q.2 ≤ c - δ := hqB.2
      linarith
  have hsep : ∀ x : ℝ, sSup ({y : ℝ | a ≤ y ∧ y ≤ b ∧ (x, y) ∈ B} ∪ {a})
      < sInf ({y : ℝ | a ≤ y ∧ y ≤ b ∧ (x, y) ∈ A} ∪ {b}) := by
    intro x
    have hsup : sSup ({y : ℝ | a ≤ y ∧ y ≤ b ∧ (x, y) ∈ B} ∪ {a}) ≤ c := by
      apply csSup_le ⟨a, Or.inr rfl⟩
      rintro y (hy | rfl)
      · have hyB : (x, y) ∈ B := hy.2.2
        rw [hBdef] at hyB
        rcases hyB with h | ⟨h, h'⟩
        · exact hcP (x, y) h
        · have hqy : y ≤ c - δ := h'
          linarith
      · exact hac
    have hinf : c < sInf ({y : ℝ | a ≤ y ∧ y ≤ b ∧ (x, y) ∈ A} ∪ {b}) := by
      have hge : min b (c + δ) ≤ sInf ({y : ℝ | a ≤ y ∧ y ≤ b ∧ (x, y) ∈ A} ∪ {b}) := by
        apply le_csInf ⟨b, Or.inr rfl⟩
        rintro y (hy | rfl)
        · have hyA : (x, y) ∈ A := hy.2.2
          rw [hAdef] at hyA
          exact le_trans (min_le_right _ _) hyA.2
        · exact min_le_left _ _
      have hlt : c < min b (c + δ) := lt_min hcb (by linarith)
      linarith [hge, hlt]
    linarith [hsup, hinf]
  obtain ⟨z, hz1, hz2, hzAB, γ, hγ0, hγ1, hγbox, hγAB⟩ :=
    exists_translate_path_of_separated (A := A) (B := B) hp hab hAclosed hBclosed hsubA hsubB
      hperA hperB hsep
  exact ⟨z, hz1, hz2, by rw [hAB] at hzAB; exact hzAB, γ, hγ0, hγ1, hγbox,
    fun t => by rw [hAB] at hγAB; exact hγAB t⟩

/-- **Lower interface.**  If `Q` lies above the level `c` and `P` misses the level `c`, then a
translate path avoiding `P ∪ Q` exists. -/
theorem exists_translate_path_of_lower_interface {p a b c : ℝ} (hp : 0 < p) (hab : a < b)
    (hac : a < c) (hcb : c ≤ b)
    {P Q : Set (ℝ × ℝ)} (hP : IsClosed P) (hQ : IsClosed Q)
    (hsubP : P ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hsubQ : Q ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hdisj : Disjoint P Q)
    (hperP : ∀ q : ℝ × ℝ, q ∈ P ↔ (q.1 + p, q.2) ∈ P)
    (hperQ : ∀ q : ℝ × ℝ, q ∈ Q ↔ (q.1 + p, q.2) ∈ Q)
    (hcQ : ∀ q ∈ Q, c ≤ q.2) (hcP : ∀ q ∈ P, q.2 ≠ c) :
    ∃ z : ℝ × ℝ, a ≤ z.2 ∧ z.2 ≤ b ∧ z ∉ P ∪ Q ∧
      ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
        γ 0 = z ∧ γ 1 = (z.1 + p, z.2) ∧
        (∀ t, a ≤ (γ t).2 ∧ (γ t).2 ≤ b) ∧ ∀ t, γ t ∉ P ∪ Q := by
  obtain ⟨δ, hδpos, hδsub⟩ :=
    closed_periodic_bounded_away_from_level (p := p) (a := a) (b := b) (c := c)
      hp hab hP hsubP hperP hcP
  set B : Set (ℝ × ℝ) := P ∩ {q : ℝ × ℝ | q.2 ≤ c - δ} with hBdef
  set A : Set (ℝ × ℝ) := Q ∪ (P ∩ {q : ℝ × ℝ | c + δ ≤ q.2}) with hAdef
  have hBclosed : IsClosed B := by
    rw [hBdef]
    exact hP.inter (isClosed_Iic.preimage continuous_snd)
  have hAclosed : IsClosed A := by
    rw [hAdef]
    exact hQ.union (hP.inter (isClosed_Ici.preimage continuous_snd))
  have hsubB : B ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} := by
    intro q hq; rw [hBdef] at hq; exact hsubP hq.1
  have hsubA : A ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} := by
    intro q hq
    rw [hAdef] at hq
    rcases hq with hq | hq
    · exact hsubQ hq
    · exact hsubP hq.1
  have hperB : ∀ q : ℝ × ℝ, q ∈ B ↔ (q.1 + p, q.2) ∈ B := by
    intro q
    rw [hBdef]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(hperP q).mp h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨(hperP q).mpr h1, h2⟩
  have hperA : ∀ q : ℝ × ℝ, q ∈ A ↔ (q.1 + p, q.2) ∈ A := by
    intro q
    rw [hAdef]
    constructor
    · rintro (h1 | ⟨h1, h2⟩)
      · exact Or.inl ((hperQ q).mp h1)
      · exact Or.inr ⟨(hperP q).mp h1, h2⟩
    · rintro (h1 | ⟨h1, h2⟩)
      · exact Or.inl ((hperQ q).mpr h1)
      · exact Or.inr ⟨(hperP q).mpr h1, h2⟩
  have hAB : A ∪ B = P ∪ Q := by
    apply Set.Subset.antisymm
    · intro q hq
      rw [hAdef, hBdef] at hq
      rcases hq with hq | hq
      · rcases hq with hq | hq
        · exact Or.inr hq
        · exact Or.inl hq.1
      · exact Or.inl hq.1
    · intro q hq
      rcases hq with hq | hq
      · rcases hδsub q hq with h | h
        · exact Or.inr ⟨hq, h⟩
        · exact Or.inl (Or.inr ⟨hq, h⟩)
      · exact Or.inl (Or.inl hq)
  have hdisjAB : Disjoint A B := by
    rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
    rintro q ⟨hqA, hqB⟩
    rw [hAdef] at hqA
    rw [hBdef] at hqB
    rcases hqA with hqA | hqA
    · exact Set.disjoint_left.mp hdisj hqB.1 hqA
    · have h1 : c + δ ≤ q.2 := hqA.2
      have h2 : q.2 ≤ c - δ := hqB.2
      linarith
  have hsep : ∀ x : ℝ, sSup ({y : ℝ | a ≤ y ∧ y ≤ b ∧ (x, y) ∈ B} ∪ {a})
      < sInf ({y : ℝ | a ≤ y ∧ y ≤ b ∧ (x, y) ∈ A} ∪ {b}) := by
    intro x
    have hsup : sSup ({y : ℝ | a ≤ y ∧ y ≤ b ∧ (x, y) ∈ B} ∪ {a}) ≤ max a (c - δ) := by
      apply csSup_le ⟨a, Or.inr rfl⟩
      rintro y (hy | rfl)
      · have hyB : (x, y) ∈ B := hy.2.2
        rw [hBdef] at hyB
        have hqy : y ≤ c - δ := hyB.2
        exact le_trans hqy (le_max_right a (c - δ))
      · exact le_max_left _ _
    have hinf : max a (c - δ) < sInf ({y : ℝ | a ≤ y ∧ y ≤ b ∧ (x, y) ∈ A} ∪ {b}) := by
      have hge : c ≤ sInf ({y : ℝ | a ≤ y ∧ y ≤ b ∧ (x, y) ∈ A} ∪ {b}) := by
        apply le_csInf ⟨b, Or.inr rfl⟩
        rintro y (hy | rfl)
        · have hyA : (x, y) ∈ A := hy.2.2
          rw [hAdef] at hyA
          rcases hyA with h | ⟨h, h'⟩
          · exact hcQ (x, y) h
          · have hqy : c + δ ≤ y := h'
            linarith
        · exact hcb
      have hlt : max a (c - δ) < c := max_lt hac (by linarith)
      exact lt_of_lt_of_le hlt hge
    exact lt_of_le_of_lt hsup hinf
  obtain ⟨z, hz1, hz2, hzAB, γ, hγ0, hγ1, hγbox, hγAB⟩ :=
    exists_translate_path_of_separated (A := A) (B := B) hp hab hAclosed hBclosed hsubA hsubB
      hperA hperB hsep
  exact ⟨z, hz1, hz2, by rw [hAB] at hzAB; exact hzAB, γ, hγ0, hγ1, hγbox,
    fun t => by rw [hAB] at hγAB; exact hγAB t⟩

/-! ## The mirror of the strip

The involution `stripMirror a b (x,y) = (x, a + b - y)` of the closed strip `a ≤ ·.2 ≤ b` keeps the
`x`-coordinate — hence keeps the *translate-path* statement unchanged — and interchanges the top and
bottom lines of the strip.  It is the WLOG device for the residual case: in the saturated situation
`P ⊆ {q.2 ≤ mP}` (so a translate path must avoid `P` near the **top** line) while
`Q ⊆ {mQ ≤ q.2}` (so it must avoid `Q` near the **bottom** line); mirroring turns this into the
reversed configuration, in which the roles of the two collared sets are interchanged, so a statement
proved for one orientation transfers to the other. -/

/-- The mirror `(x, y) ↦ (x, a + b - y)` of the strip `a ≤ ·.2 ≤ b`. -/
def stripMirror (a b : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (q.1, a + b - q.2)

lemma stripMirror_involutive (a b : ℝ) : Function.Involutive (stripMirror a b) := fun q => by
  simp [stripMirror]

lemma stripMirror_continuous (a b : ℝ) : Continuous (stripMirror a b) := by
  unfold stripMirror; fun_prop

/-- The mirror of a set, written as a preimage (the two agree because `stripMirror` is an
involution). -/
lemma stripMirror_image_eq_preimage (a b : ℝ) (K : Set (ℝ × ℝ)) :
    stripMirror a b '' K = {q : ℝ × ℝ | stripMirror a b q ∈ K} := by
  ext q
  constructor
  · rintro ⟨w, hw, rfl⟩
    show stripMirror a b (stripMirror a b w) ∈ K
    rw [(stripMirror_involutive a b) w]
    exact hw
  · intro hq
    exact ⟨stripMirror a b q, hq, (stripMirror_involutive a b) q⟩

@[simp] lemma stripMirror_image_image (a b : ℝ) (K : Set (ℝ × ℝ)) :
    stripMirror a b '' (stripMirror a b '' K) = K := by
  ext q
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    have h : stripMirror a b (stripMirror a b v) = v := (stripMirror_involutive a b) v
    rwa [h]
  · intro hq
    exact ⟨stripMirror a b q, ⟨q, hq, rfl⟩, (stripMirror_involutive a b) q⟩

/-- The mirror preserves the strip `a ≤ ·.2 ≤ b`. -/
lemma stripMirror_mem_strip (a b : ℝ) {q : ℝ × ℝ} :
    stripMirror a b q ∈ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} ↔ q ∈ {q | a ≤ q.2 ∧ q.2 ≤ b} := by
  simp only [Set.mem_ofPred_eq, stripMirror]
  constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **The mirror turns "touches the bottom line" into "touches the top line"**, and conversely: the
bottom line `·.2 = a` is carried to the top line `·.2 = b`.  This is the exact sense in which the
residual case may be considered in either orientation.
Concretely: `(x,a) ∈ K` iff `(x,b) ∈ stripMirror a b '' K`, and `(x,b) ∈ K` iff `(x,a) ∈ ...`. -/
lemma stripMirror_bot (a b : ℝ) (K : Set (ℝ × ℝ)) (x : ℝ) :
    ((x, a) : ℝ × ℝ) ∈ stripMirror a b '' K ↔ ((x, b) : ℝ × ℝ) ∈ K := by
  rw [stripMirror_image_eq_preimage]
  simp [stripMirror]

lemma stripMirror_top (a b : ℝ) (K : Set (ℝ × ℝ)) (x : ℝ) :
    ((x, b) : ℝ × ℝ) ∈ stripMirror a b '' K ↔ ((x, a) : ℝ × ℝ) ∈ K := by
  rw [stripMirror_image_eq_preimage]
  simp [stripMirror]

/-- The mirror of the half-plane `{q.2 ≤ c}`; in particular it turns the collar `P ⊆ {q.2 ≤ mP}`
(the obstacle avoiding the top) into `stripMirror '' P ⊆ {a + b - mP ≤ q.2}` (the mirrored obstacle
avoiding the bottom). -/
lemma stripMirror_halfspace_le (a b c : ℝ) :
    stripMirror a b '' {q : ℝ × ℝ | q.2 ≤ c} = {q : ℝ × ℝ | a + b - c ≤ q.2} := by
  ext q
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : w.2 ≤ c := hw
    simp only [Set.mem_ofPred_eq, stripMirror]
    linarith [hw']
  · intro hq
    have hq' : a + b - c ≤ q.2 := hq
    refine ⟨stripMirror a b q, ?_, (stripMirror_involutive a b) q⟩
    simp only [Set.mem_ofPred_eq, stripMirror]
    linarith [hq']

/-- **Mirror invariance of the translate-path statement.**  There is a translate path in the strip
avoiding `K` if and only if there is one avoiding the mirrored set: the mirror keeps the
`x`-coordinate, hence keeps `γ 1 = (γ 0).1 + p` and the height range `a ≤ ·.2 ≤ b`. -/
theorem exists_translate_path_iff_stripMirror {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {K : Set (ℝ × ℝ)} :
    (∃ z : ℝ × ℝ, a ≤ z.2 ∧ z.2 ≤ b ∧ z ∉ K ∧
      ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ), γ 0 = z ∧ γ 1 = (z.1 + p, z.2) ∧
        (∀ t, a ≤ (γ t).2 ∧ (γ t).2 ≤ b) ∧ ∀ t, γ t ∉ K)
    ↔
    (∃ z : ℝ × ℝ, a ≤ z.2 ∧ z.2 ≤ b ∧ z ∉ stripMirror a b '' K ∧
      ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ), γ 0 = z ∧ γ 1 = (z.1 + p, z.2) ∧
        (∀ t, a ≤ (γ t).2 ∧ (γ t).2 ≤ b) ∧ ∀ t, γ t ∉ stripMirror a b '' K) := by
  have hfwd : ∀ K : Set (ℝ × ℝ),
      (∃ z : ℝ × ℝ, a ≤ z.2 ∧ z.2 ≤ b ∧ z ∉ K ∧
        ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ), γ 0 = z ∧ γ 1 = (z.1 + p, z.2) ∧
          (∀ t, a ≤ (γ t).2 ∧ (γ t).2 ≤ b) ∧ ∀ t, γ t ∉ K) →
      (∃ z : ℝ × ℝ, a ≤ z.2 ∧ z.2 ≤ b ∧ z ∉ stripMirror a b '' K ∧
        ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ), γ 0 = z ∧ γ 1 = (z.1 + p, z.2) ∧
          (∀ t, a ≤ (γ t).2 ∧ (γ t).2 ≤ b) ∧ ∀ t, γ t ∉ stripMirror a b '' K) := by
    intro K hK
    obtain ⟨z, hz1, hz2, hzK, γ, hγ0, hγ1, hγbox, hγK⟩ := hK
    have hz' : stripMirror a b z ∈ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} :=
      (stripMirror_mem_strip a b).mpr ⟨hz1, hz2⟩
    have hzK' : stripMirror a b z ∉ stripMirror a b '' K := by
      rw [stripMirror_image_eq_preimage]
      intro hmem
      have hmem' : stripMirror a b (stripMirror a b z) ∈ K := hmem
      rw [(stripMirror_involutive a b) z] at hmem'
      exact hzK hmem'
    refine ⟨stripMirror a b z, hz'.1, hz'.2, hzK', ?_⟩
    refine ⟨⟨fun t : Set.Icc (0 : ℝ) 1 => stripMirror a b (γ t),
      (stripMirror_continuous a b).comp γ.continuous⟩, ?_, ?_, ?_, ?_⟩
    · show stripMirror a b (γ 0) = stripMirror a b z
      rw [hγ0]
    · show stripMirror a b (γ 1) = ((stripMirror a b z).1 + p, (stripMirror a b z).2)
      rw [hγ1]
      rfl
    · intro t
      have h := hγbox t
      exact ⟨by show a ≤ a + b - (γ t).2; linarith [h.2], by show a + b - (γ t).2 ≤ b; linarith [h.1]⟩
    · intro t hmem
      rw [stripMirror_image_eq_preimage] at hmem
      exact hγK t ((stripMirror_involutive a b) (γ t) ▸ hmem)
  constructor
  · exact hfwd K
  · intro h
    have h' := hfwd (stripMirror a b '' K) h
    rwa [stripMirror_image_image] at h'

/-! ## The free-meridian cut

The next step decomposes the residual of the target.  If some meridian `{c} × [a,b]` avoids the
closed `p`-periodic set `K`, we can *cut* the annulus along it: in the square `[c,c+p] × [a,b]` the
commons barrier lemma `barrier_bottom_top_of_no_left_right` turns "`K` has no preconnected piece
whose heights accumulate at both `a` and `b`" into a left–right path `γ` avoiding `K`, and the free
meridian segment then closes the height gap between `γ`'s two endpoints. -/

/-- **The free-meridian cut, case `c = 0`.** -/
theorem exists_translate_path_of_free_meridian_zero {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {K : Set (ℝ × ℝ)} (hK : IsClosed K)
    (hsub : K ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hper : ∀ q : ℝ × ℝ, q ∈ K ↔ (q.1 + p, q.2) ∈ K)
    (hnospan : ∀ C : Set (ℝ × ℝ), C ⊆ K → IsPreconnected C →
      a ∈ closure ((fun q : ℝ × ℝ => q.2) '' C) →
      b ∈ closure ((fun q : ℝ × ℝ => q.2) '' C) → False)
    (hfree : ∀ y : ℝ, a ≤ y → y ≤ b → ((0 : ℝ), y) ∉ K) :
    ∃ z : ℝ × ℝ, a ≤ z.2 ∧ z.2 ≤ b ∧ z ∉ K ∧
      ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
        γ 0 = z ∧ γ 1 = (z.1 + p, z.2) ∧
        (∀ t, a ≤ (γ t).2 ∧ (γ t).2 ≤ b) ∧ ∀ t, γ t ∉ K := by
  set Sq : Set (ℝ × ℝ) := {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ p ∧ a ≤ q.2 ∧ q.2 ≤ b} with hSq
  have hSq_eq : Sq = Set.Icc (0 : ℝ) p ×ˢ Set.Icc a b := by
    rw [hSq]; ext q; simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc]; tauto
  have hcl : IsClosed (K ∩ Sq) := hK.inter (hSq_eq ▸ isClosed_Icc.prod isClosed_Icc)
  have hsub' : K ∩ Sq ⊆ Sq := inter_subset_right
  have hnospan' : ∀ C : Set (ℝ × ℝ), C ⊆ K ∩ Sq → IsPreconnected C →
      (C ∩ {q : ℝ × ℝ | q.2 = a}).Nonempty →
      (C ∩ {q : ℝ × ℝ | q.2 = b}).Nonempty → False := by
    intro C hC hpre ha hb
    refine hnospan C (fun q hq => (hC hq).1) hpre ?_ ?_
    · obtain ⟨q, hq, hq2⟩ := ha
      exact subset_closure ⟨q, hq, by simpa using hq2⟩
    · obtain ⟨q, hq, hq2⟩ := hb
      exact subset_closure ⟨q, hq, by simpa using hq2⟩
  have hLR : ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ), (∀ t, γ t ∈ Sq) ∧
      (γ 0 ∈ ({q : ℝ × ℝ | q.1 = 0} : Set (ℝ × ℝ))) ∧
      (γ 1 ∈ ({q : ℝ × ℝ | q.1 = p} : Set (ℝ × ℝ))) ∧ ∀ t, γ t ∉ K ∩ Sq := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨C, hC, hpre, ha, hb⟩ :=
      barrier_bottom_top_of_no_left_right (p := p) (a := a) (b := b) hp hab hsub' hcl
        (fun γ h1 h2 h3 h4 => by
          obtain ⟨t, ht⟩ := hcon γ h1 h2 h3
          exact h4 t ht)
    exact hnospan' C hC hpre ha hb
  obtain ⟨γ, hγSq, hγ0, hγ1, hγK⟩ := hLR
  have hx0 : (γ 0).1 = 0 := hγ0
  have hx1 : (γ 1).1 = p := hγ1
  have hy1a : a ≤ (γ 0).2 := (hγSq 0).2.2.1
  have hy1b : (γ 0).2 ≤ b := (hγSq 0).2.2.2
  have hy2a : a ≤ (γ 1).2 := (hγSq 1).2.2.1
  have hy2b : (γ 1).2 ≤ b := (hγSq 1).2.2.2
  set W : Set (ℝ × ℝ) := {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} \ K with hW
  -- the left–right path, as a joining inside `W`
  have hjoinγ : JoinedIn W ((0 : ℝ), (γ 0).2) (γ 1) := by
    refine ⟨{ toContinuousMap := γ, source' := Prod.ext hx0 rfl, target' := rfl }, ?_⟩
    intro t
    exact ⟨⟨(hγSq t).2.2.1, (hγSq t).2.2.2⟩, fun hmem => hγK t ⟨hmem, hγSq t⟩⟩
  -- the free meridian segment, as a joining inside `W`
  have hjoinμ : JoinedIn W ((0 : ℝ), (γ 1).2) ((0 : ℝ), (γ 0).2) := by
    refine ⟨⟨⟨fun t : Set.Icc (0 : ℝ) 1 =>
      ((0 : ℝ), (γ 1).2 + (t : ℝ) * ((γ 0).2 - (γ 1).2)), by fun_prop⟩, ?_, ?_⟩, ?_⟩
    · show ((0 : ℝ), (γ 1).2 + ((0 : Set.Icc (0 : ℝ) 1) : ℝ) * ((γ 0).2 - (γ 1).2))
        = ((0 : ℝ), (γ 1).2)
      simp
    · show ((0 : ℝ), (γ 1).2 + ((1 : Set.Icc (0 : ℝ) 1) : ℝ) * ((γ 0).2 - (γ 1).2))
        = ((0 : ℝ), (γ 0).2)
      simp
    · intro t
      have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      have hy : (γ 1).2 + (t : ℝ) * ((γ 0).2 - (γ 1).2) ∈ Set.Icc a b := by
        refine ⟨?_, ?_⟩ <;> nlinarith [hy1a, hy1b, hy2a, hy2b, ht0, ht1]
      exact ⟨hy, fun hmem => hfree _ hy.1 hy.2 hmem⟩
  obtain ⟨γ', hγ'⟩ := hjoinμ.trans hjoinγ
  refine ⟨((0 : ℝ), (γ 1).2), hy2a, hy2b, hfree _ hy2a hy2b,
    γ'.toContinuousMap, ?_, ?_, fun t => (hγ' t).1, fun t => (hγ' t).2⟩
  · simpa using γ'.source
  · have h1 : ((0 : ℝ), (γ 1).2).1 + p = p := by simp
    rw [h1]
    have ht : γ' 1 = γ 1 := γ'.target
    show γ' 1 = (p, (γ 1).2)
    rw [ht]
    exact Prod.ext hx1 rfl

/-- **The free-meridian cut.**  If some meridian `{c} × [a,b]` avoids `K`, then the translate path
exists.  (Reduced to `c = 0` by translating `K`.) -/
theorem exists_translate_path_of_free_meridian {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {K : Set (ℝ × ℝ)} (hK : IsClosed K)
    (hsub : K ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hper : ∀ q : ℝ × ℝ, q ∈ K ↔ (q.1 + p, q.2) ∈ K)
    (hnospan : ∀ C : Set (ℝ × ℝ), C ⊆ K → IsPreconnected C →
      a ∈ closure ((fun q : ℝ × ℝ => q.2) '' C) →
      b ∈ closure ((fun q : ℝ × ℝ => q.2) '' C) → False)
    {c : ℝ} (hfree : ∀ y : ℝ, a ≤ y → y ≤ b → ((c, y) : ℝ × ℝ) ∉ K) :
    ∃ z : ℝ × ℝ, a ≤ z.2 ∧ z.2 ≤ b ∧ z ∉ K ∧
      ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
        γ 0 = z ∧ γ 1 = (z.1 + p, z.2) ∧
        (∀ t, a ≤ (γ t).2 ∧ (γ t).2 ≤ b) ∧ ∀ t, γ t ∉ K := by
  set K₀ : Set (ℝ × ℝ) := {q : ℝ × ℝ | (q.1 + c, q.2) ∈ K} with hK₀def
  have hK₀ : IsClosed K₀ := by
    rw [hK₀def]
    exact hK.preimage (by fun_prop : Continuous fun q : ℝ × ℝ => (q.1 + c, q.2))
  have hsub₀ : ∀ q ∈ K₀, a ≤ q.2 ∧ q.2 ≤ b := by
    intro q hq
    have hq' : (q.1 + c, q.2) ∈ K := hq
    have h := hsub hq'
    simpa using h
  have hper₀ : ∀ q : ℝ × ℝ, q ∈ K₀ ↔ (q.1 + p, q.2) ∈ K₀ := by
    intro q
    constructor
    · intro h
      rw [hK₀def] at h ⊢
      have h' := (hper (q.1 + c, q.2)).mp h
      have heq : (q.1 + c) + p = (q.1 + p) + c := by ring
      rwa [heq] at h'
    · intro h
      rw [hK₀def] at h ⊢
      have h' := (hper (q.1 + c, q.2)).mpr (by
        have heq : (q.1 + c) + p = (q.1 + p) + c := by ring
        rwa [heq])
      exact h'
  have hnospan₀ : ∀ C : Set (ℝ × ℝ), C ⊆ K₀ → IsPreconnected C →
      a ∈ closure ((fun q : ℝ × ℝ => q.2) '' C) →
      b ∈ closure ((fun q : ℝ × ℝ => q.2) '' C) → False := by
    intro C hC hpre ha hb
    have himg : (fun q : ℝ × ℝ => q.2) '' ((fun q : ℝ × ℝ => (q.1 + c, q.2)) '' C)
        = (fun q : ℝ × ℝ => q.2) '' C := by
      ext y
      constructor
      · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩; exact ⟨q, hq, rfl⟩
      · rintro ⟨q, hq, rfl⟩; exact ⟨(q.1 + c, q.2), ⟨q, hq, rfl⟩, rfl⟩
    refine hnospan ((fun q : ℝ × ℝ => (q.1 + c, q.2)) '' C) ?_
      (hpre.image _ (by fun_prop)) ?_ ?_
    · rintro _ ⟨q, hq, rfl⟩
      have h := hC hq
      rw [hK₀def] at h
      exact h
    · rw [himg]; exact ha
    · rw [himg]; exact hb
  have hfree₀ : ∀ y : ℝ, a ≤ y → y ≤ b → ((0 : ℝ), y) ∉ K₀ := by
    intro y hya hyb
    rw [hK₀def]
    simpa using hfree y hya hyb
  obtain ⟨z₀, hz₀a, hz₀b, hz₀K, γ, hγ0, hγ1, hγbox, hγK⟩ :=
    exists_translate_path_of_free_meridian_zero hp hab hK₀ hsub₀ hper₀ hnospan₀ hfree₀
  refine ⟨(z₀.1 + c, z₀.2), hz₀a, hz₀b, ?_, ?_⟩
  · rw [hK₀def] at hz₀K
    exact hz₀K
  · refine ⟨⟨fun t : Set.Icc (0 : ℝ) 1 => ((γ t).1 + c, (γ t).2), ?_⟩, ?_, ?_, ?_, ?_⟩
    · exact Continuous.prodMk ((continuous_fst.comp γ.continuous).add continuous_const)
        (continuous_snd.comp γ.continuous)
    · change ((γ 0).1 + c, (γ 0).2) = (z₀.1 + c, z₀.2)
      rw [hγ0]
    · change ((γ 1).1 + c, (γ 1).2) = ((z₀.1 + c) + p, z₀.2)
      rw [hγ1]
      exact Prod.ext (by ring) rfl
    · intro t; exact hγbox t
    · intro t
      have h := hγK t
      rw [hK₀def] at h
      exact h

/-! ## The residual ("saturated") case

Everything above reduces `translate_path_of_two_collared_periodic` (at the top of this discussion)
to the statement below, *except* for the completely elementary cases already dispatched in the body
of the target: a free level (any `c ∈ [a,b]` with `P ∪ Q` missing the whole level circle), an
"upper interface" (a level `c` below `P`'s ceiling on which `Q` is absent) and a "lower interface"
(the mirror image).

The saturated case is

* `P ⊆ {q | q.2 ≤ mP}`, `Q ⊆ {q | mQ ≤ q.2}`,
* `P` meets every level of `[a, mQ]` and `Q` meets every level of `[mP, b]`, with `mQ ≤ mP`,

and `translate_path_of_saturated_periodic` splits it into three, of which **two are proved**:

1. **separated columns** (`τ x < σ x` for all `x`, where `τ` is the ceiling of `P` and `σ` the
   floor of `Q`): `exists_translate_path_of_separated_columns`, proved here — this is the "the path
   is a graph" case;
2. **free meridian**: `exists_translate_path_of_free_meridian`, proved here;
3. **interlocking columns with every meridian met**: `translate_path_of_saturated_interlocking`
   (the single remaining obligation — `∃ x, σ x ≤ τ x`, so the free column `(τ x, σ x)` is empty and
   the path cannot be a graph there).

This is exactly Denne's `prop:homology` (arXiv:math/0510561): two closed disjoint `p`-periodic sets,
one collared away from the top boundary circle and one from the bottom boundary circle, leave an
essential ("winding once") loop in the annulus.  Two things are worth recording:

* `P ∪ Q` never contains a preconnected `C` whose heights accumulate at both `a` and `b` (a
  preconnected subset of `P ∪ Q` lies in `P` or in `Q`, by closedness + connectedness), so the
  *converse* of `Commons.Topology.Strip.wall_blocks_translate_path` is exactly what is needed;
* the argument cannot be replaced by a "separated graph" (the ceiling of `P` may exceed the floor of
  `Q` in a column: the walls interlock), and the standard published proof is the Mayer–Vietoris
  exactness
  `H₁(S∖(A∪B)) → H₁(S∖A) ⊕ H₁(S∖B) → H₁(S) ≅ ℤ`
  which is not available in Mathlib; the shared commons contains the point-set substitutes
  (`two_disjoint_closed_not_separating`, `barrier_bottom_top_of_no_left_right`,
  `essT_not_subset_obstacles_of_interlocking`) and the residual is equivalent to the project's
  central open obligation `Topology/Strip/no_spanning_implies_translate_path`.
-/

/-! ## Two consequences of the barrier lemma, used to reduce the residual case

`K = P ∪ Q` has no preconnected piece meeting both horizontal lines (a preconnected piece of a
union of two disjoint closed sets lies in one of them, and the two collaring hypotheses keep `P`
away from `y = b` and `Q` away from `y = a`).  Hence the *barrier lemma*
`Commons.Topology.Strip.barrier_bottom_top_of_no_left_right` gives a left–right path in the square
`[0,p] × [a,b]` avoiding `P ∪ Q`.  The residual content of the crux is then exactly the fact that
this left–right path can be taken with **equal end heights** (i.e. it is already a translate path).
-/

/-- A preconnected subset of a union of two disjoint closed sets lies in one of them. -/
lemma isPreconnected_subset_left_or_right {X : Type*} [TopologicalSpace X] {P Q C : Set X}
    (hP : IsClosed P) (hQ : IsClosed Q) (hdisj : Disjoint P Q) (hC : C ⊆ P ∪ Q)
    (hpre : IsPreconnected C) : C ⊆ P ∨ C ⊆ Q := by
  refine (isPreconnected_iff_subset_of_disjoint_closed.mp hpre P Q hP hQ hC) ?_
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨-, hxP, hxQ⟩
  exact Set.disjoint_left.mp hdisj hxP hxQ

/-- **No spanning piece.**  In the two-collar geometry no preconnected subset of `P ∪ Q` meets both
horizontal lines `y = a` and `y = b`. -/
lemma no_spanning_of_two_collar_bands {P Q : Set (ℝ × ℝ)} {mP mQ a b : ℝ}
    (hP : IsClosed P) (hQ : IsClosed Q) (hdisj : Disjoint P Q)
    (hsubP : P ⊆ {q : ℝ × ℝ | q.2 ≤ mP}) (hsubQ : Q ⊆ {q : ℝ × ℝ | mQ ≤ q.2})
    (hmPb : mP < b) (hamQ : a < mQ) :
    ∀ C : Set (ℝ × ℝ), C ⊆ P ∪ Q → IsPreconnected C →
      (C ∩ {q : ℝ × ℝ | q.2 = a}).Nonempty → (C ∩ {q : ℝ × ℝ | q.2 = b}).Nonempty → False := by
  intro C hC hpre hCa hCb
  obtain ⟨xa, hxaC, hxaeq⟩ := hCa
  obtain ⟨xb, hxbC, hxbeq⟩ := hCb
  rcases isPreconnected_subset_left_or_right hP hQ hdisj hC hpre with hCP | hCQ
  · have h1 : xb.2 ≤ mP := hsubP (hCP hxbC)
    rw [hxbeq] at h1
    linarith
  · have h1 : mQ ≤ xa.2 := hsubQ (hCQ hxaC)
    rw [hxaeq] at h1
    linarith

/-- The barrier lemma's contrapositive: a closed set in the square with no spanning piece admits a
left–right path in the square avoiding it. -/
lemma exists_left_right_path_of_no_spanning {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {K : Set (ℝ × ℝ)}
    (hKsub : K ⊆ {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ p ∧ a ≤ q.2 ∧ q.2 ≤ b}) (hK : IsClosed K)
    (hnospan : ∀ C : Set (ℝ × ℝ), C ⊆ K → IsPreconnected C →
      (C ∩ {q : ℝ × ℝ | q.2 = a}).Nonempty → (C ∩ {q : ℝ × ℝ | q.2 = b}).Nonempty → False) :
    ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
      (∀ t, γ t ∈ {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ p ∧ a ≤ q.2 ∧ q.2 ≤ b}) ∧
      γ 0 ∈ ({q : ℝ × ℝ | q.1 = 0} : Set (ℝ × ℝ)) ∧
      γ 1 ∈ ({q : ℝ × ℝ | q.1 = p} : Set (ℝ × ℝ)) ∧ ∀ t, γ t ∉ K := by
  by_contra hcon
  push Not at hcon
  obtain ⟨C, hCK, hCpre, hCa, hCb⟩ :=
    Commons.Topology.Strip.barrier_bottom_top_of_no_left_right hp hab hKsub hK
      (fun γ h1 h2 h3 h4 => by
        obtain ⟨t, ht⟩ := hcon γ h1 h2 h3
        exact h4 t ht)
  exact hnospan C hCK hCpre hCa hCb

/-- **The reduction of the residual case to `y₀ = y₁`.**  In the two-collar geometry there is a path
in the square `[0,p] × [a,b]` from the line `{q.1 = 0}` to the line `{q.1 = p}` avoiding `P ∪ Q`. -/
theorem exists_left_right_path_avoiding_two_collars {p a b mP mQ : ℝ} (hp : 0 < p) (hab : a < b)
    {P Q : Set (ℝ × ℝ)} (hP : IsClosed P) (hQ : IsClosed Q) (hdisj : Disjoint P Q)
    (hsubP : P ⊆ {q : ℝ × ℝ | q.2 ≤ mP}) (hsubQ : Q ⊆ {q : ℝ × ℝ | mQ ≤ q.2})
    (hmPb : mP < b) (hamQ : a < mQ) :
    ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
      (∀ t, γ t ∈ {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ p ∧ a ≤ q.2 ∧ q.2 ≤ b}) ∧
      γ 0 ∈ ({q : ℝ × ℝ | q.1 = 0} : Set (ℝ × ℝ)) ∧
      γ 1 ∈ ({q : ℝ × ℝ | q.1 = p} : Set (ℝ × ℝ)) ∧ ∀ t, γ t ∉ P ∪ Q := by
  have hsq : ({q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ p ∧ a ≤ q.2 ∧ q.2 ≤ b} : Set (ℝ × ℝ))
      = ({q : ℝ × ℝ | q.1 ∈ Set.Icc 0 p} ∩ {q : ℝ × ℝ | q.2 ∈ Set.Icc a b}) := by
    ext q; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Icc]; tauto
  have hKcl : IsClosed ((P ∪ Q) ∩ {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ p ∧ a ≤ q.2 ∧ q.2 ≤ b}) := by
    rw [hsq]
    exact (hP.union hQ).inter
      ((isClosed_Icc.preimage continuous_fst).inter (isClosed_Icc.preimage continuous_snd))
  obtain ⟨γ, h1, h2, h3, h4⟩ := exists_left_right_path_of_no_spanning hp hab
    (hKsub := Set.inter_subset_right) hKcl
    (fun C hC hpre hCa hCb => no_spanning_of_two_collar_bands hP hQ hdisj hsubP hsubQ hmPb hamQ
      C (fun z hz => (hC hz).1) hpre hCa hCb)
  exact ⟨γ, h1, h2, h3, fun t ht => h4 t ⟨ht, h1 t⟩⟩

/-- **Branch 2 of the `Ess` dichotomy forces `p`-density of the levels.**

If no free point `w` of the band `a < y ≤ mQ` can be joined to its own translate `τ w` inside
`(S°∖P)`, then for every level `y` of that band the closed `p`-periodic set `P_y` meets *every*
interval of length `p`: indeed the horizontal segment `[w, τw]` is connected, starts in `w`'s
component of `S°∖P`, and must therefore meet `P` (otherwise its image would already join `w` to
`τ w`).  The symmetric statement holds for `Q` on the band `[mP, b)`.

This is the exact form in which the *first* half of branch 2 is consumed. -/
lemma level_p_dense_of_no_translate_join {p a b mQ : ℝ} (hp : 0 < p) (hmQb : mQ < b)
    {P : Set (ℝ × ℝ)}
    (hno : ∀ w : ℝ × ℝ, a < w.2 → w.2 ≤ mQ → w ∉ P →
      ¬ JoinedIn (Pᶜ ∩ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b}) w (w.1 + p, w.2)) :
    ∀ y : ℝ, a < y → y ≤ mQ → ∀ x : ℝ, ∃ x' : ℝ, x ≤ x' ∧ x' ≤ x + p ∧
      ((x', y) : ℝ × ℝ) ∈ P := by
  intro y hay hyq x
  by_contra hcon
  push Not at hcon
  have hyb : y < b := lt_of_le_of_lt hyq hmQb
  have hw : ((x, y) : ℝ × ℝ) ∉ P := hcon x le_rfl (by linarith)
  refine hno (x, y) hay hyq hw ?_
  refine ⟨⟨⟨fun t : Set.Icc (0:ℝ) 1 => (((x : ℝ) + (t : ℝ) * p), y), by fun_prop⟩, ?_, ?_⟩, ?_⟩
  · simp
  · simp
  · intro t
    refine ⟨?_, hay, hyb⟩
    rw [Set.mem_compl_iff]
    exact hcon _ (by have := t.2.1; nlinarith) (by have := t.2.2; nlinarith)

/-- **`(B2′)` pushes every translate-path basepoint into the interface window.**

Let `hnoP` say that inside the band `a < y ≤ mQ` no free point can be joined to its own translate
inside `Pᶜ ∩ S°`, and `hnoQ` the dual statement for `Q` on `mP ≤ y < b`.  If `z ∈ S°∖(P∪Q)` is
joined to `z + (p,0)` inside `S°∖(P∪Q)`, then necessarily

  `mQ < z.2 < mP`,

i.e. **every** translate path of the complement has its basepoint in the interface window `(mQ,mP)`:
`z.2 ≤ mQ` would already join `z` to `τ z` inside `Pᶜ ∩ S°`, contradicting `hnoP`, and `z.2 ≥ mP`
would contradict `hnoQ`.

This is how `(B2′)` is consumed at the interface: it localizes the whole problem to the strip
`ℝ × (mQ, mP)` where both obstacles may occur, which is exactly where an interlocking column can
exist. -/
lemma basepoint_in_window_of_no_translate_join {p a b mP mQ : ℝ}
    {P Q : Set (ℝ × ℝ)}
    (hnoP : ∀ w : ℝ × ℝ, a < w.2 → w.2 ≤ mQ → w ∉ P →
      ¬ JoinedIn (Pᶜ ∩ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b}) w (w.1 + p, w.2))
    (hnoQ : ∀ w : ℝ × ℝ, mP ≤ w.2 → w.2 < b → w ∉ Q →
      ¬ JoinedIn (Qᶜ ∩ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b}) w (w.1 + p, w.2))
    {z : ℝ × ℝ} (hz : z ∉ P ∪ Q) (hzbox : a < z.2 ∧ z.2 < b)
    (hjoin : JoinedIn (Pᶜ ∩ Qᶜ ∩ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b}) z (z.1 + p, z.2)) :
    mQ < z.2 ∧ z.2 < mP := by
  constructor
  · by_contra h
    push Not at h
    exact hnoP z hzbox.1 h (fun hzP => hz (Or.inl hzP))
      (hjoin.mono (fun w hw => ⟨hw.1.1, hw.2⟩))
  · by_contra h
    push Not at h
    exact hnoQ z h hzbox.2 (fun hzQ => hz (Or.inr hzQ))
      (hjoin.mono (fun w hw => ⟨hw.1.2, hw.2⟩))


/-! ### The base layer of the winding theory for the annulus

The residual case of `translate_path_of_saturated_periodic` is the *interlocking* case, which is a
genuinely two-dimensional (homological) statement about the annulus.  The plan is the standard one:
a loop of nonzero *winding* in the free region forces a translate path (`Ess ≠ ∅`), and two such
loops --- one avoiding `P` and one avoiding `Q` --- glue to one in the entire free region.

Proved here is the *base layer* of that theory: a path in a `T`-invariant set whose endpoint is a
nonzero translate `z + (k*p, 0)` of its start point contains a translate path.  (For `k = ±1` this is
immediate; for `|k| ≥ 2` one builds the corresponding staircase and applies the commons'
`path_meets_translate`; negative `k` is reduced by reversing the parametrisation.) -/

/-- Staircase with domain period `1` and spatial shift `(m:ℝ)*p`. -/
private lemma exists_staircase_shift_aux {p : ℝ} (hp : 0 < p) {m : ℕ}
    {γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)}
    (hγ : γ 1 = ((γ 0).1 + (m:ℝ)*p, (γ 0).2)) :
    ∃ G : C(ℝ, ℝ × ℝ),
      (∀ t, G (t + 1) = ((G t).1 + (m:ℝ)*p, (G t).2)) ∧
      (∀ t, ∃ s : Set.Icc (0:ℝ) 1, ∃ n : ℤ, G t = ((γ s).1 + ((n:ℝ) * p), (γ s).2)) := by
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  set Φ : ℝ → ℝ := fun u => (γ (Set.projIcc 0 1 h01 u)).1 - ((m:ℝ)*p) * u with hΦ
  set Ψ : ℝ → ℝ := fun u => (γ (Set.projIcc 0 1 h01 u)).2 with hΨ
  have hΦc : ContinuousOn Φ (Set.Icc (0:ℝ) 1) := by rw [hΦ]; fun_prop
  have hΨc : ContinuousOn Ψ (Set.Icc (0:ℝ) 1) := by rw [hΨ]; fun_prop
  have hp0 : Set.projIcc 0 1 h01 (0:ℝ) = (0 : Set.Icc (0:ℝ) 1) := by
    apply Subtype.ext; rw [Set.projIcc_left h01]; rfl
  have hp1 : Set.projIcc 0 1 h01 (1:ℝ) = (1 : Set.Icc (0:ℝ) 1) := by
    apply Subtype.ext; rw [Set.projIcc_right h01]; rfl
  have hΦ0 : Φ 0 = (γ 0).1 := by
    rw [hΦ]; show (γ (Set.projIcc 0 1 h01 (0:ℝ))).1 - ((m:ℝ)*p) * 0 = (γ 0).1
    rw [hp0]; simp
  have hΦ1 : Φ 1 = (γ 0).1 := by
    rw [hΦ]; show (γ (Set.projIcc 0 1 h01 (1:ℝ))).1 - ((m:ℝ)*p) * 1 = (γ 0).1
    rw [hp1, hγ]; ring
  have hΨ0 : Ψ 0 = (γ 0).2 := by
    rw [hΨ]; show (γ (Set.projIcc 0 1 h01 (0:ℝ))).2 = (γ 0).2; rw [hp0]
  have hΨ1 : Ψ 1 = (γ 0).2 := by
    rw [hΨ]; show (γ (Set.projIcc 0 1 h01 (1:ℝ))).2 = (γ 0).2; rw [hp1, hγ]
  have hΦf : Continuous (Φ ∘ Int.fract) := ContinuousOn.comp_fract'' hΦc (by rw [hΦ0, hΦ1])
  have hΨf : Continuous (Ψ ∘ Int.fract) := ContinuousOn.comp_fract'' hΨc (by rw [hΨ0, hΨ1])
  have hcont : Continuous fun t : ℝ =>
      ((((m:ℝ)*p) * t + (Φ ∘ Int.fract) t, (Ψ ∘ Int.fract) t) : ℝ × ℝ) := by
    apply Continuous.prodMk
    · exact (continuous_const.mul continuous_id).add hΦf
    · exact hΨf
  refine ⟨⟨_, hcont⟩, ?_, ?_⟩
  · intro t
    show ((((m:ℝ)*p) * (t+1) + (Φ ∘ Int.fract) (t+1), (Ψ ∘ Int.fract) (t+1)) : ℝ × ℝ)
        = ((((m:ℝ)*p) * t + (Φ ∘ Int.fract) t) + (m:ℝ)*p, (Ψ ∘ Int.fract) t)
    simp only [Function.comp_apply, Int.fract_add_one]
    exact Prod.ext (by ring) rfl
  · intro t
    refine ⟨Set.projIcc 0 1 h01 (Int.fract t), ⌊t⌋ * (m : ℤ), ?_⟩
    show ((((m:ℝ)*p) * t + (Φ ∘ Int.fract) t, (Ψ ∘ Int.fract) t) : ℝ × ℝ)
        = ((γ (Set.projIcc 0 1 h01 (Int.fract t))).1 + ((⌊t⌋ * (m:ℤ) : ℤ) : ℝ) * p,
           (γ (Set.projIcc 0 1 h01 (Int.fract t))).2)
    have hf : Int.fract t = t - (⌊t⌋ : ℝ) := (Int.self_sub_floor t).symm
    simp only [Function.comp_apply, hΦ, hΨ]
    refine Prod.ext ?_ ?_
    · rw [hf]; push_cast; ring
    · rfl


/-- **Base layer of the winding theory, case of winding `m ≥ 2`.** -/
lemma ess_of_winding_ge_two {p : ℝ} (hp : 0 < p) {m : ℕ} (hm : 2 ≤ m) {W : Set (ℝ × ℝ)}
    (hper : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W)
    {γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)} (hγW : ∀ t, γ t ∈ W)
    (hγ : γ 1 = ((γ 0).1 + (m:ℝ)*p, (γ 0).2)) :
    ∃ z : ℝ × ℝ, z ∈ W ∧ JoinedIn W z (z.1 + p, z.2) := by
  obtain ⟨G, hGper, hGform⟩ := exists_staircase_shift_aux hp hγ
  have hGW : ∀ t, G t ∈ W := by
    intro t
    obtain ⟨s, n, hs⟩ := hGform t
    rw [hs]
    exact (Commons.Topology.Strip.periodic_shift hper n (γ s)).mpr (hγW s)
  obtain ⟨s, t, hst⟩ := Commons.Topology.Strip.path_meets_translate hp hm G.continuous hGper
  have sub : ∀ a b : ℝ, a ≤ b → JoinedIn W (G a) (G b) := by
    intro a b hab
    refine JoinedIn.ofLine (f := fun u : ℝ => G ((1 - u) * a + u * b)) ?_ ?_ ?_ ?_
    · exact (G.continuous.comp (by fun_prop)).continuousOn
    · have h : ((1 - (0:ℝ)) * a + 0 * b) = a := by ring
      show G ((1 - (0:ℝ)) * a + 0 * b) = G a
      rw [h]
    · have h : ((1 - (1:ℝ)) * a + 1 * b) = b := by ring
      show G ((1 - (1:ℝ)) * a + 1 * b) = G b
      rw [h]
    · rintro y ⟨u, -, rfl⟩
      exact hGW _
  rcases le_total t s with hle | hle
  · exact ⟨G t, hGW t, by rw [← hst]; exact sub t s hle⟩
  · exact ⟨G t, hGW t, by rw [← hst]; exact (sub s t hle).symm⟩


/-- Natural-number winding case. -/
lemma ess_of_winding_nat {p : ℝ} (hp : 0 < p) {m : ℕ} (hm : 1 ≤ m) {W : Set (ℝ × ℝ)}
    (hper : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W)
    {γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)} (hγW : ∀ t, γ t ∈ W)
    (hγ : γ 1 = ((γ 0).1 + (m:ℝ)*p, (γ 0).2)) :
    ∃ z : ℝ × ℝ, z ∈ W ∧ JoinedIn W z (z.1 + p, z.2) := by
  rcases eq_or_lt_of_le hm with h1 | h2
  · subst h1
    refine ⟨γ 0, hγW 0, ?_⟩
    exact ⟨{ toContinuousMap := γ, source' := rfl,
             target' := hγ.trans (Prod.ext (by ring) rfl) }, hγW⟩
  · exact ess_of_winding_ge_two hp h2 hper hγW hγ

/-- Positive integer winding case. -/
lemma ess_of_pos_winding {p : ℝ} (hp : 0 < p) {j : ℤ} (hj : 0 < j) {W : Set (ℝ × ℝ)}
    (hper : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W)
    {γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)} (hγW : ∀ t, γ t ∈ W)
    (hγ : γ 1 = ((γ 0).1 + (j : ℝ) * p, (γ 0).2)) :
    ∃ z : ℝ × ℝ, z ∈ W ∧ JoinedIn W z (z.1 + p, z.2) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℤ) = j := ⟨j.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hm1 : 1 ≤ m := by omega
  exact ess_of_winding_nat hp hm1 hper hγW (by rw [hγ]; refine Prod.ext ?_ rfl; push_cast; ring)

/-- **Base layer of the winding theory for the annulus.**  A path in a `T`-invariant set whose
endpoint is a nonzero translate of its start point contains a translate path (a loop of nonzero
winding in the free region produces an essential point). -/
theorem ess_of_nonzero_winding {p : ℝ} (hp : 0 < p) {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hper : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W)
    {k : ℤ} (hk : k ≠ 0) {γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)} (hγW : ∀ t, γ t ∈ W)
    (hγ1 : γ 1 = ((γ 0).1 + (k : ℝ) * p, (γ 0).2)) :
    ∃ z : ℝ × ℝ, z ∈ W ∧ JoinedIn W z (z.1 + p, z.2) := by
  rcases lt_trichotomy k 0 with hlt | heq | hgt
  · -- `k < 0`: reverse the parametrisation, giving displacement `(-k) * p > 0`
    set γ' : C(Set.Icc (0:ℝ) 1, ℝ × ℝ) :=
      ⟨fun t => γ ⟨1 - (t : ℝ), by
          have h := t.2; rw [Set.mem_Icc] at h ⊢; constructor <;> linarith⟩, by fun_prop⟩
      with hγ'def
    have hγ'W : ∀ t, γ' t ∈ W := fun t => hγW _
    have hγ'0 : γ' 0 = γ 1 := by
      show γ ⟨1 - (0:ℝ), _⟩ = γ 1
      congr 1; exact Subtype.ext (by simp)
    have hγ'1 : γ' 1 = γ 0 := by
      show γ ⟨1 - (1:ℝ), _⟩ = γ 0
      congr 1; exact Subtype.ext (by simp)
    have hdisp : γ' 1 = ((γ' 0).1 + ((-k : ℤ) : ℝ) * p, (γ' 0).2) := by
      rw [hγ'0, hγ'1, hγ1]
      refine Prod.ext ?_ rfl
      have hk0 : (k : ℝ) + ((-k : ℤ) : ℝ) = 0 := by push_cast; ring
      have h : (k : ℝ) * p + ((-k : ℤ) : ℝ) * p = 0 := by rw [← add_mul, hk0, zero_mul]
      linarith
    exact ess_of_pos_winding hp (by omega) hper hγ'W hdisp
  · exact absurd heq hk
  · exact ess_of_pos_winding hp hgt hper hγW hγ1


/-- **Local excision (subdividing a path along an open cover).**  A path in a space covered by two
open sets can be subdivided into finitely many consecutive sub-paths, each lying entirely in one of
the two open sets.  This is the local (excision) input of the by-hand Mayer–Vietoris argument in
degree one: it is what lets one arrange that each piece of a path is handled by `W₁` or by `W₂`.

Derived from Mathlib's `exists_monotone_Icc_subset_open_cover_unitInterval`
(`Mathlib/Topology/UnitInterval.lean`), i.e. the Lebesgue number lemma for `I`. -/
theorem exists_subpath_subordinate {X : Type*} [TopologicalSpace X] {U₁ U₂ : Set X}
    (ho₁ : IsOpen U₁) (ho₂ : IsOpen U₂) (hcov : U₁ ∪ U₂ = Set.univ)
    {γ : C(Set.Icc (0 : ℝ) 1, X)} :
    ∃ t : ℕ → Set.Icc (0 : ℝ) 1, t 0 = 0 ∧ Monotone t ∧ (∃ n, ∀ m ≥ n, t m = 1) ∧
      ∀ n, (∀ s : Set.Icc (0 : ℝ) 1, t n ≤ s → s ≤ t (n + 1) → γ s ∈ U₁) ∨
           (∀ s : Set.Icc (0 : ℝ) 1, t n ≤ s → s ≤ t (n + 1) → γ s ∈ U₂) := by
  have hcov' : Set.univ ⊆ ⋃ i : Bool, γ ⁻¹' (if i then U₂ else U₁) := by
    intro x _
    rcases Set.eq_univ_iff_forall.mp hcov (γ x) with h | h
    · exact Set.mem_iUnion.mpr ⟨false, h⟩
    · exact Set.mem_iUnion.mpr ⟨true, h⟩
  have hopen : ∀ i : Bool, IsOpen (γ ⁻¹' (if i then U₂ else U₁)) := by
    intro i
    cases i with
    | false => simpa using ho₁.preimage γ.continuous
    | true => simpa using ho₂.preimage γ.continuous
  obtain ⟨t, ht0, htmono, ht1, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun i : Bool => γ ⁻¹' (if i then U₂ else U₁)) hopen hcov'
  refine ⟨t, ht0, htmono, ht1, fun n => ?_⟩
  obtain ⟨i, hi⟩ := hsub n
  cases i with
  | false =>
      left
      intro s h1 h2
      exact hi (Set.mem_Icc.mpr ⟨h1, h2⟩)
  | true =>
      right
      intro s h1 h2
      exact hi (Set.mem_Icc.mpr ⟨h1, h2⟩)

/-! ### The gluing step (Mayer–Vietoris in degree one)

The second half of the winding theory --- two `T`-invariant sets `W₁, W₂ ⊆ S`, **open in the strip**,
covering `S`, each containing a nonzero-winding loop, leave a nonzero-winding loop in `W₁ ∩ W₂` --- is
proved in the shared commons as `Commons.Topology.Strip.exists_translate_path_of_ess_of_cover`
(imported above).  Its openness hypothesis is essential (excision): the closed/open covering
`W₁ = {0 ≤ q.2 ≤ 1/2}`, `W₂ = {1/2 < q.2 ≤ 1}` satisfies everything else but has `W₁ ∩ W₂ = ∅`.
In the application below, `W₁ = Pᶜ ∩ S` and `W₂ = Qᶜ ∩ S` with `P`, `Q` closed, so openness is
automatic. -/

/-- **Residual: interlocking columns, every meridian met (the crux).**

In the saturated situation, suppose

* every meridian meets `P ∪ Q` (equivalently: no meridian is free), and
* the columns **interlock**: some `P`-point of a column lies above some `Q`-point of the same column
  (equivalently, the ceiling `τ` of `P` and the floor `σ` of `Q` satisfy `σ x₀ ≤ τ x₀` for some `x₀`,
  so the free column `(τ x₀, σ x₀)` is empty and the path cannot be a graph there).

Then there is a translate path avoiding `P ∪ Q`.

Everything else is discharged elsewhere:

* the non-interlocking branch is `exists_translate_path_of_separated_columns` (proved);
* the free-meridian branch is `exists_translate_path_of_free_meridian` (proved);
* this statement is all that `translate_path_of_saturated_periodic` needs in the remaining branch.

Suggestions recorded from earlier attempts: `hmet` makes the slice functions
`x ↦ max {y | (x,y) ∈ P}` and `x ↦ min {y | (x,y) ∈ Q}` well defined; if `P` (or `Q`) were bounded
away from its boundary line the upper/lower-semicontinuous envelope argument of the docstring of
`translate_path_of_two_collared_periodic` would give the path, so the interlocking hypothesis here
must be used to handle the columns where the two obstacles overlap vertically. -/
theorem translate_path_of_saturated_interlocking {p a b ε δ mP mQ : ℝ} (hp : 0 < p) (hab : a < b)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hmPb : mP ≤ b - ε) (hmQa : a + δ ≤ mQ) (hmPQ : mQ ≤ mP)
    {P Q : Set (ℝ × ℝ)} (hP : IsClosed P) (hQ : IsClosed Q)
    (hdisj : Disjoint P Q)
    (hperP : ∀ q : ℝ × ℝ, q ∈ P ↔ (q.1 + p, q.2) ∈ P)
    (hperQ : ∀ q : ℝ × ℝ, q ∈ Q ↔ (q.1 + p, q.2) ∈ Q)
    (hsubP : P ⊆ {q : ℝ × ℝ | q.2 ≤ mP})
    (hsubQ : Q ⊆ {q : ℝ × ℝ | mQ ≤ q.2})
    (hsatP : ∀ t : ℝ, a ≤ t → t ≤ mQ → ∃ x : ℝ, (x, t) ∈ P)
    (hsatQ : ∀ t : ℝ, mP ≤ t → t ≤ b → ∃ x : ℝ, (x, t) ∈ Q)
    (hmet : ∀ x : ℝ, ∃ y : ℝ, a ≤ y ∧ y ≤ b ∧ ((x, y) : ℝ × ℝ) ∈ P ∪ Q)
    (hinter : ∃ x : ℝ, ∃ yP yQ : ℝ, a ≤ yP ∧ yP ≤ b ∧ ((x, yP) : ℝ × ℝ) ∈ P ∧
      a ≤ yQ ∧ yQ ≤ b ∧ ((x, yQ) : ℝ × ℝ) ∈ Q ∧ yQ ≤ yP) :
    ∃ z : ℝ × ℝ, a ≤ z.2 ∧ z.2 ≤ b ∧ z ∉ P ∪ Q ∧
      ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
        γ 0 = z ∧ γ 1 = (z.1 + p, z.2) ∧
        (∀ t, a ≤ (γ t).2 ∧ (γ t).2 ≤ b) ∧ ∀ t, γ t ∉ P ∪ Q := by
  -- `A := Pᶜ ∩ S` and `B := Qᶜ ∩ S` are `T`-invariant and cover the strip `S`; each contains a
  -- nonzero-winding loop (the top, resp. bottom band).  The gluing step supplies an essential point
  -- of `A ∩ B = S∖(P∪Q)`.
  set S : Set (ℝ × ℝ) := {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} with hS
  set A : Set (ℝ × ℝ) := Pᶜ ∩ S with hA
  set B : Set (ℝ × ℝ) := Qᶜ ∩ S with hB
  have hamP : a ≤ mP := by
    obtain ⟨x, hx⟩ := hsatP a le_rfl (by linarith)
    have h := hsubP hx
    rw [Set.mem_ofPred_eq] at h
    exact h
  have hmQb : mQ ≤ b := by
    obtain ⟨x, hx⟩ := hsatQ b (by linarith) le_rfl
    have h := hsubQ hx
    rw [Set.mem_ofPred_eq] at h
    exact h
  have hperA : ∀ q : ℝ × ℝ, q ∈ A ↔ (q.1 + p, q.2) ∈ A := by
    intro q
    simp only [hA, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hq, h1, h2⟩; exact ⟨(hperP q).not.mp hq, h1, h2⟩
    · rintro ⟨hq, h1, h2⟩; exact ⟨(hperP q).not.mpr hq, h1, h2⟩
  have hperB : ∀ q : ℝ × ℝ, q ∈ B ↔ (q.1 + p, q.2) ∈ B := by
    intro q
    simp only [hB, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hq, h1, h2⟩; exact ⟨(hperQ q).not.mp hq, h1, h2⟩
    · rintro ⟨hq, h1, h2⟩; exact ⟨(hperQ q).not.mpr hq, h1, h2⟩
  have hsubA : A ⊆ S := inter_subset_right
  have hsubB : B ⊆ S := inter_subset_right
  have hcov : A ∪ B = S := by
    rw [hA, hB]
    ext q
    constructor
    · rintro (h | h) <;> exact h.2
    · intro hq
      by_cases hPq : q ∈ P
      · right; exact ⟨fun hQq => Set.disjoint_left.mp hdisj hPq hQq, hq⟩
      · left; exact ⟨hPq, hq⟩
  have hneA : ∃ z : ℝ × ℝ, z ∈ A ∧ JoinedIn A z (z.1 + p, z.2) := by
    refine ⟨(0, (mP + b) / 2), ?_, ?_⟩
    · rw [hA]; refine ⟨?_, ?_⟩
      · rw [Set.mem_compl_iff]
        intro hmem
        have h : (mP + b) / 2 ≤ mP := hsubP hmem
        linarith
      · rw [hS]; exact ⟨by linarith, by linarith⟩
    · refine JoinedIn.ofLine (f := fun u : ℝ => (u * p, (mP + b) / 2)) ?_ ?_ ?_ ?_
      · fun_prop
      · simp
      · simp
      · rintro y ⟨u, -, rfl⟩
        rw [hA]; refine ⟨?_, ?_⟩
        · rw [Set.mem_compl_iff]
          intro hmem
          have h : (mP + b) / 2 ≤ mP := hsubP hmem
          linarith
        · rw [hS]; exact ⟨by linarith, by linarith⟩
  have hneB : ∃ z : ℝ × ℝ, z ∈ B ∧ JoinedIn B z (z.1 + p, z.2) := by
    refine ⟨(0, (a + mQ) / 2), ?_, ?_⟩
    · rw [hB]; refine ⟨?_, ?_⟩
      · rw [Set.mem_compl_iff]
        intro hmem
        have h : mQ ≤ (a + mQ) / 2 := hsubQ hmem
        linarith
      · rw [hS]; exact ⟨by linarith, by linarith⟩
    · refine JoinedIn.ofLine (f := fun u : ℝ => (u * p, (a + mQ) / 2)) ?_ ?_ ?_ ?_
      · fun_prop
      · simp
      · simp
      · rintro y ⟨u, -, rfl⟩
        rw [hB]; refine ⟨?_, ?_⟩
        · rw [Set.mem_compl_iff]
          intro hmem
          have h : mQ ≤ (a + mQ) / 2 := hsubQ hmem
          linarith
        · rw [hS]; exact ⟨by linarith, by linarith⟩
  have hopenA : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ A = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} :=
    ⟨Pᶜ, hP.isOpen_compl, by rw [hA, hS]⟩
  have hopenB : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ B = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} :=
    ⟨Qᶜ, hQ.isOpen_compl, by rw [hB, hS]⟩
  obtain ⟨z, hzAB, hzjoin⟩ :=
    exists_translate_path_of_ess_of_cover hp hab hsubA hsubB hopenA hopenB hperA hperB hcov hneA hneB
  obtain ⟨γ, hγ⟩ := hzjoin
  have hzS : z ∈ S := hsubA hzAB.1
  rw [hS] at hzS
  refine ⟨z, hzS.1, hzS.2, ?_, ⟨γ, γ.source, γ.target, ?_, ?_⟩⟩
  · intro hmem
    rcases hmem with h | h
    · exact hzAB.1.1 h
    · exact hzAB.2.1 h
  · intro t
    have h := hsubA (hγ t).1
    rw [hS] at h
    exact h
  · intro t hmem
    rcases hmem with h | h
    · exact (hγ t).1.1 h
    · exact (hγ t).2.1 h

/-- **Residual (saturated) case** — equivalent to `prop:homology` of Denne, arXiv:math/0510561. -/
theorem translate_path_of_saturated_periodic {p a b ε δ mP mQ : ℝ} (hp : 0 < p) (hab : a < b)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hmPb : mP ≤ b - ε) (hmQa : a + δ ≤ mQ) (hmPQ : mQ ≤ mP)
    {P Q : Set (ℝ × ℝ)} (hP : IsClosed P) (hQ : IsClosed Q)
    (hdisj : Disjoint P Q)
    (hperP : ∀ q : ℝ × ℝ, q ∈ P ↔ (q.1 + p, q.2) ∈ P)
    (hperQ : ∀ q : ℝ × ℝ, q ∈ Q ↔ (q.1 + p, q.2) ∈ Q)
    (hsubP : P ⊆ {q : ℝ × ℝ | q.2 ≤ mP})
    (hsubQ : Q ⊆ {q : ℝ × ℝ | mQ ≤ q.2})
    (hsatP : ∀ t : ℝ, a ≤ t → t ≤ mQ → ∃ x : ℝ, (x, t) ∈ P)
    (hsatQ : ∀ t : ℝ, mP ≤ t → t ≤ b → ∃ x : ℝ, (x, t) ∈ Q) :
    ∃ z : ℝ × ℝ, a ≤ z.2 ∧ z.2 ≤ b ∧ z ∉ P ∪ Q ∧
      ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
        γ 0 = z ∧ γ 1 = (z.1 + p, z.2) ∧
        (∀ t, a ≤ (γ t).2 ∧ (γ t).2 ≤ b) ∧ ∀ t, γ t ∉ P ∪ Q := by
  -- Branch 1: no column interlocks.  Then every `P`-point of a column lies strictly below every
  -- `Q`-point of that column, and the separated-columns lemma gives the translate path directly.
  by_cases hsepc : ∀ x : ℝ, ∀ yP yQ : ℝ, a ≤ yP → yP ≤ b → ((x, yP) : ℝ × ℝ) ∈ P →
      a ≤ yQ → yQ ≤ b → ((x, yQ) : ℝ × ℝ) ∈ Q → yP < yQ
  · exact exists_translate_path_of_separated_columns hp hab hmPQ (by linarith) (by linarith)
      (le_trans (by linarith : a ≤ mQ) hmPQ) hP hQ hdisj hperP hperQ hsubP hsubQ hsepc
  -- Branch 2 (the interlocking columns): free-meridian dichotomy for `K := (P ∪ Q) ∩ strip`.
  -- The free-meridian branch is proved; the other branch is the isolated residual.
  -- work with `K := (P ∪ Q) ∩ {a ≤ ·.2 ≤ b}`: the path is confined to the strip, so
  -- avoiding `K` is the same as avoiding `P ∪ Q`.
  set K : Set (ℝ × ℝ) := (P ∪ Q) ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} with hKdef
  have hstrip_closed : IsClosed {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} :=
    isClosed_Icc.preimage continuous_snd
  have hKcl : IsClosed K := by
    rw [hKdef]
    exact (hP.union hQ).inter hstrip_closed
  have hKsub : K ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} := fun q hq => hq.2
  have hKper : ∀ q : ℝ × ℝ, q ∈ K ↔ (q.1 + p, q.2) ∈ K := by
    intro q
    simp only [hKdef, Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h | h, h2⟩
      · exact ⟨Or.inl ((hperP q).mp h), h2⟩
      · exact ⟨Or.inr ((hperQ q).mp h), h2⟩
    · rintro ⟨h | h, h2⟩
      · exact ⟨Or.inl ((hperP q).mpr h), h2⟩
      · exact ⟨Or.inr ((hperQ q).mpr h), h2⟩
  -- a preconnected piece of `P ∪ Q` lies in `P` or in `Q`
  have hsplit : ∀ C : Set (ℝ × ℝ), C ⊆ P ∪ Q → IsPreconnected C → C ⊆ P ∨ C ⊆ Q := by
    intro C hC hpre
    refine (isPreconnected_iff_subset_of_disjoint_closed.mp hpre P Q hP hQ hC) ?_
    rw [Set.eq_empty_iff_forall_notMem]
    rintro q ⟨-, hqP, hqQ⟩
    exact Set.disjoint_left.mp hdisj hqP hqQ
  have hltb : mP < b := by linarith
  have lta : a < mQ := by linarith
  have hnospan : ∀ C : Set (ℝ × ℝ), C ⊆ K → IsPreconnected C →
      a ∈ closure ((fun q : ℝ × ℝ => q.2) '' C) →
      b ∈ closure ((fun q : ℝ × ℝ => q.2) '' C) → False := by
    intro C hC hpre ha hb
    rcases hsplit C (fun q hq => (hC hq).1) hpre with hCP | hCQ
    · have hsub_cl : closure ((fun q : ℝ × ℝ => q.2) '' C) ⊆ {y : ℝ | y ≤ mP} :=
        closure_minimal (by rintro y ⟨q, hq, rfl⟩; exact hsubP (hCP hq)) isClosed_Iic
      exact absurd (hsub_cl hb) (not_le.mpr hltb)
    · have hsub_cl : closure ((fun q : ℝ × ℝ => q.2) '' C) ⊆ {y : ℝ | mQ ≤ y} :=
        closure_minimal (by rintro y ⟨q, hq, rfl⟩; exact hsubQ (hCQ hq)) isClosed_Ici
      exact absurd (hsub_cl ha) (not_le.mpr lta)
  -- convert a translate path avoiding `K` (inside the strip) into one avoiding `P ∪ Q`
  have hconv : ∀ z : ℝ × ℝ, a ≤ z.2 → z.2 ≤ b → z ∉ K →
      (∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
        γ 0 = z ∧ γ 1 = (z.1 + p, z.2) ∧
        (∀ t, a ≤ (γ t).2 ∧ (γ t).2 ≤ b) ∧ ∀ t, γ t ∉ K) →
      ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
        γ 0 = z ∧ γ 1 = (z.1 + p, z.2) ∧
        (∀ t, a ≤ (γ t).2 ∧ (γ t).2 ≤ b) ∧ ∀ t, γ t ∉ P ∪ Q := by
    rintro z hz1 hz2 hzK ⟨γ, hγ0, hγ1, hγbox, hγK⟩
    exact ⟨γ, hγ0, hγ1, hγbox, fun t hmem =>
      hγK t ⟨hmem, (hγbox t).1, (hγbox t).2⟩⟩
  by_cases hfree : ∃ c : ℝ, ∀ y : ℝ, a ≤ y → y ≤ b → ((c, y) : ℝ × ℝ) ∉ K
  · obtain ⟨c, hc⟩ := hfree
    obtain ⟨z, hz1, hz2, hzK, hγ⟩ :=
      exists_translate_path_of_free_meridian hp hab hKcl hKsub hKper hnospan hc
    exact ⟨z, hz1, hz2, fun hmem => hzK ⟨hmem, hz1, hz2⟩, hconv z hz1 hz2 hzK hγ⟩
  · push_neg at hfree hsepc
    obtain ⟨z, hz1, hz2, hzK, hγ⟩ :=
      translate_path_of_saturated_interlocking hp hab hε hδ hmPb hmQa hmPQ hP hQ hdisj hperP
        hperQ hsubP hsubQ hsatP hsatQ
        (fun x => by
          obtain ⟨y, hy1, hy2, hyK⟩ := hfree x
          have hmem := hyK
          rw [hKdef] at hmem
          exact ⟨y, hy1, hy2, hmem.1⟩)
        hsepc
    exact ⟨z, hz1, hz2, hzK, hγ⟩

/-- **The `p`-collared two-periodic translate path.** -/
theorem translate_path_of_two_collared_periodic {p a b ε δ : ℝ} (hp : 0 < p) (hab : a < b)
    (hε : 0 < ε) (hδ : 0 < δ)
    {P Q : Set (ℝ × ℝ)} (hP : IsClosed P) (hQ : IsClosed Q)
    (hsubP : P ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hsubQ : Q ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hdisj : Disjoint P Q)
    (hperP : ∀ q : ℝ × ℝ, q ∈ P ↔ (q.1 + p, q.2) ∈ P)
    (hperQ : ∀ q : ℝ × ℝ, q ∈ Q ↔ (q.1 + p, q.2) ∈ Q)
    (htop : P ⊆ {q : ℝ × ℝ | q.2 ≤ b - ε})
    (hbot : Q ⊆ {q : ℝ × ℝ | a + δ ≤ q.2}) :
    ∃ z : ℝ × ℝ, a ≤ z.2 ∧ z.2 ≤ b ∧ z ∉ P ∪ Q ∧
      ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
        γ 0 = z ∧ γ 1 = (z.1 + p, z.2) ∧
        (∀ t, a ≤ (γ t).2 ∧ (γ t).2 ≤ b) ∧ ∀ t, γ t ∉ P ∪ Q := by
  -- If some level avoids `P ∪ Q` entirely, the horizontal segment at that level works.
  by_cases hfree : ∃ c : ℝ, a ≤ c ∧ c ≤ b ∧ ∀ x : ℝ, (x, c) ∉ P ∪ Q
  · obtain ⟨c, hc1, hc2, hc3⟩ := hfree
    exact exists_translate_path_of_free_level hp hab hc1 hc2 hc3
  by_cases h1 : a ≤ b - ε
  · by_cases h2 : a + δ ≤ b
    · by_cases h3 : a + δ ≤ b - ε
      · -- main (overlapping) case
        by_cases hup : ∃ c : ℝ, b - ε ≤ c ∧ c < b ∧ ∀ q ∈ Q, q.2 ≠ c
        · obtain ⟨c, hc1, hc2, hc3⟩ := hup
          exact exists_translate_path_of_upper_interface hp hab (by linarith) hc2 hP hQ hsubP
            hsubQ hdisj hperP hperQ (fun q hq => le_trans (htop hq) hc1) hc3
        · by_cases hlow : ∃ c : ℝ, a < c ∧ c ≤ a + δ ∧ ∀ q ∈ P, q.2 ≠ c
          · obtain ⟨c, hc1, hc2, hc3⟩ := hlow
            exact exists_translate_path_of_lower_interface hp hab hc1 (by linarith) hP hQ hsubP
              hsubQ hdisj hperP hperQ (fun q hq => le_trans hc2 (hbot hq)) hc3
          · by_cases hPa : ∀ x : ℝ, (x, a) ∉ P
            · refine exists_translate_path_of_free_level (c := a) hp hab (le_refl a) hab.le
                (fun x => ?_)
              rintro (h | h)
              · exact hPa x h
              · have hh : a + δ ≤ a := hbot h
                linarith
            · by_cases hQb : ∀ x : ℝ, (x, b) ∉ Q
              · refine exists_translate_path_of_free_level (c := b) hp hab hab.le (le_refl b)
                  (fun x => ?_)
                rintro (h | h)
                · have hh : b ≤ b - ε := htop h
                  linarith
                · exact hQb x h
              · -- saturated (hard) case
                push_neg at hup hlow hPa hQb
                exact translate_path_of_saturated_periodic hp hab hε hδ (le_refl _) (le_refl _)
                  h3 hP hQ hdisj hperP hperQ (fun q hq => htop hq) (fun q hq => hbot hq)
                  (fun t ht1 ht2 => by
                    rcases eq_or_lt_of_le ht1 with h | h
                    · obtain ⟨x, hx⟩ := hPa
                      exact ⟨x, h ▸ hx⟩
                    · obtain ⟨q, hqP, hq2⟩ := hlow t h ht2
                      refine ⟨q.1, ?_⟩
                      have hq' : ((q.1, t) : ℝ × ℝ) = q := Prod.ext rfl hq2.symm
                      rw [← hq'] at hqP
                      exact hqP)
                  (fun t ht1 ht2 => by
                    rcases eq_or_lt_of_le ht2 with h | h
                    · obtain ⟨x, hx⟩ := hQb
                      exact ⟨x, h.symm ▸ hx⟩
                    · obtain ⟨q, hqQ, hq2⟩ := hup t ht1 h
                      refine ⟨q.1, ?_⟩
                      have hq' : ((q.1, t) : ℝ × ℝ) = q := Prod.ext rfl hq2.symm
                      rw [← hq'] at hqQ
                      exact hqQ)
      · -- free level strictly between b - ε and a + δ
        have h3' : b - ε < a + δ := not_le.mp h3
        refine exists_translate_path_of_free_level (c := (b - ε + (a + δ)) / 2) hp hab
          (by linarith) (by linarith) (fun x => ?_)
        rintro (h | h)
        · have hh : (b - ε + (a + δ)) / 2 ≤ b - ε := htop h
          linarith
        · have hh : a + δ ≤ (b - ε + (a + δ)) / 2 := hbot h
          linarith
    · -- free level at b
      refine exists_translate_path_of_free_level (c := b) hp hab hab.le (le_refl b)
        (fun x => ?_)
      rintro (h | h)
      · have hh : b ≤ b - ε := htop h
        linarith
      · have hh : a + δ ≤ b := hbot h
        linarith
  · -- free level at a
    refine exists_translate_path_of_free_level (c := a) hp hab (le_refl a) hab.le
      (fun x => ?_)
    rintro (h | h)
    · have hh : a ≤ b - ε := htop h
      linarith
    · have hh : a + δ ≤ a := hbot h
      linarith

end Commons.Topology.Strip
