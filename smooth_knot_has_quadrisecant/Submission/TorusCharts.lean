import Mathlib
import ChallengeDeps
import Submission.TorusCollinearity

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology

/-!
# Layer A (ix) — local arc charts of the trisecant locus and their overlap

Milestone 1, lifted to the parameter torus (`TorusCollinearity.lean`,
`torus_local_structure_of_general_position`), provides, at every
general-position collinear off-diagonal torus triple `p`, a continuous curve
`γ` in `T³` through `p`, lying in the trisecant zero set, which covers every
zero in a torus neighbourhood `V` of `p` and is injective on a subinterval
around `0` (with the injective sub-arc inside `V`).  This module packages
that existential data into a *chart object* `TorusArcData` and proves the
first structural facts needed to glue the local arcs into the global
1-manifold picture of the trisecant locus `O` (Kuperberg §3):

1. **packaging** — `exists_torusArcData_of_general_position` / `_all`
   (and the `Classical.choice`-based `torusArcData_of_general_position` /
   `_all`) turn the structure theorem's output into the `TorusArcData r p`
   record (`V` a torus neighbourhood of `p`, `γ` the local curve over
   `(lo,hi)` covering `V`'s zeros, and an injective sub-arc over `(lo',hi')`
   that stays inside `V`);
2. **the local zero set is traced by the arc** —
   `arcRange_eq_zeroSet_of_subset`: for any open `W ⊆ V`, the portion of the
   trisecant zero set inside `W` is exactly the part of the curve inside `W`
   (both inclusions: the curve stays in the zero set, and the covering
   property puts every zero of `W` on the curve);
3. **embedded local arcs** — `embedded_local_arc`: around `p` the zero set
   contains an injective continuous image of an interval through `p`
   (`γ` restricted to its injective sub-interval, with image inside `V`);
   and `TorusArcData.subarc_within` refines the injective sub-arc so that its
   image lies inside any pre-assigned open neighbourhood of `p`
   (`TorusArcData.refine_within` packages this as a new chart whose
   neighbourhood is inside the pre-assigned one);
4. **the overlap (first gluing) lemma** — `torus_arc_overlap`: two charts at
   the same base point `p` agree on their overlap: on `W = V₁ ∩ V₂` both
   curves trace out exactly the same portion of the trisecant zero set
   (`arcRange γ₁ ∩ W = arcRange γ₂ ∩ W = trisecantZeroSet r ∩ W`) — i.e. the
   two local families of trisecants describe the same object up to the torus
   quotient and up to their parameterisations; combined with (3) both charts
   embed injective sub-arcs into `W`.

(What is *not* claimed yet: that a single interval-parametrisation is
injective over a whole open neighbourhood of `p` in the zero set — that
requires exposing the implicit-function *graph* coordinates of the local
curve (the curve is `t ↦ A(x(t), ψ(x(t)))` with `x(t)` monotone), a
refinement of Milestone 1 left for the next stage of the 1-manifold theory.)

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- The trisecant data at the torus level: collinear (cross product zero)
off-diagonal triples — the zeros of `torusCollinearity` that are not
diagonal. -/
def trisecantZeroSet (r : ℝ → Space) : Set KnotParamTriple :=
  {q : KnotParamTriple | torusCollinearity r q = 0} ∩ TorusOffDiag r

/-- A point of the torus is in the trisecant zero set iff it is a
collinear off-diagonal triple. -/
lemma mem_trisecantZeroSet_iff {r : ℝ → Space} (q : KnotParamTriple) :
    q ∈ trisecantZeroSet r ↔ torusCollinearity r q = 0 ∧ q ∈ TorusOffDiag r := by
  simp [trisecantZeroSet]

/-- **A local arc chart of the trisecant zero set at `p`.**  The data
packaged by the torus structure theorem:
- `V` is a torus neighbourhood of `p`;
- `γ` is a continuous curve over `(lo,hi)` with `γ 0 = p`, lying in the
  trisecant zero set, which *covers* every trisecant zero of `V`;
- on the sub-interval `(lo',hi')` (around `0`) the curve is injective and
  stays inside `V` (an embedded local sub-arc). -/
structure TorusArcData (r : ℝ → Space) (p : KnotParamTriple) where
  V : Set KnotParamTriple
  V_open : IsOpen V
  p_mem : p ∈ V
  lo : ℝ
  hi : ℝ
  lo_lt : lo < 0
  hi_pos : 0 < hi
  γ : ℝ → KnotParamTriple
  γ_cont : ContinuousOn γ (Set.Ioo lo hi)
  γ_zero : γ 0 = p
  γ_good : ∀ t ∈ Set.Ioo lo hi, torusCollinearity r (γ t) = 0 ∧ γ t ∈ TorusOffDiag r
  cover : ∀ q ∈ V, torusCollinearity r q = 0 → q ∈ TorusOffDiag r →
    ∃ t ∈ Set.Ioo lo hi, γ t = q
  lo' : ℝ
  hi' : ℝ
  lo'_lo : lo ≤ lo'
  lo'_neg : lo' < 0
  hi'_pos : 0 < hi'
  hi'_hi : hi' ≤ hi
  inj : Set.InjOn γ (Set.Ioo lo' hi')
  γ_subV : ∀ t ∈ Set.Ioo lo' hi', γ t ∈ V

/-- The part of the curve traced over its defining interval. -/
def TorusArcData.arcRange {r : ℝ → Space} {p : KnotParamTriple} (d : TorusArcData r p) :
    Set KnotParamTriple :=
  d.γ '' Set.Ioo d.lo d.hi

/-- The injective sub-arc of the chart. -/
def TorusArcData.injArcRange {r : ℝ → Space} {p : KnotParamTriple} (d : TorusArcData r p) :
    Set KnotParamTriple :=
  d.γ '' Set.Ioo d.lo' d.hi'

/-- The injective sub-interval contains `0` and lies inside the defining
interval. -/
lemma TorusArcData.subinterval_mem {r : ℝ → Space} {p : KnotParamTriple} (d : TorusArcData r p) :
    d.lo' < 0 ∧ 0 < d.hi' ∧ Set.Ioo d.lo' d.hi' ⊆ Set.Ioo d.lo d.hi := by
  constructor
  · exact d.lo'_neg
  constructor
  · exact d.hi'_pos
  exact Set.Ioo_subset_Ioo d.lo'_lo d.hi'_hi

/-- Packaging (existence): the torus structure theorem produces arc data at a
general-position collinear off-diagonal torus triple. -/
theorem exists_torusArcData_of_general_position (r : ℝ → Space) (h : IsSmoothKnot r)
    (p : KnotParamTriple) (hpZ : torusCollinearity r p = 0) (hpOff : p ∈ TorusOffDiag r)
    (hgp : ∃ a b m : ℝ, a ∈ Set.Ico 0 period ∧ b ∈ Set.Ico 0 period ∧ m ∈ Set.Ico 0 period ∧
      (a : KnotParam) = p.1 ∧ (b : KnotParam) = p.2.1 ∧ (m : KnotParam) = p.2.2 ∧
      TrisecantGeneralPosition r a b m) :
    Nonempty (TorusArcData r p) := by
  rcases torus_local_structure_of_general_position r h p hpZ hpOff hgp with
    ⟨V, hV₁, hV₂, _hR2⟩
  rcases _hR2 with ⟨lo, hi, hlo, hhi, _hR3⟩
  rcases _hR3 with ⟨γ, hγc, hγ0, hγg, hcv, _hR4⟩
  rcases _hR4 with ⟨lo', hi', hll, hl0, h0h, hhh, hinj, hsub⟩
  exact ⟨⟨V, hV₁, hV₂, lo, hi, hlo, hhi, γ, hγc, hγ0, hγg, hcv, lo', hi', hll, hl0, h0h,
    hhh, hinj, hsub⟩⟩

/-- Packaging (choice): arc data at a general-position collinear off-diagonal
torus triple. -/
noncomputable def torusArcData_of_general_position (r : ℝ → Space) (h : IsSmoothKnot r)
    (p : KnotParamTriple) (hpZ : torusCollinearity r p = 0) (hpOff : p ∈ TorusOffDiag r)
    (hgp : ∃ a b m : ℝ, a ∈ Set.Ico 0 period ∧ b ∈ Set.Ico 0 period ∧ m ∈ Set.Ico 0 period ∧
      (a : KnotParam) = p.1 ∧ (b : KnotParam) = p.2.1 ∧ (m : KnotParam) = p.2.2 ∧
      TrisecantGeneralPosition r a b m) :
    TorusArcData r p :=
  Classical.choice (exists_torusArcData_of_general_position r h p hpZ hpOff hgp)

/-- Packaging (existence, global hypothesis): under the torus general-position
hypothesis every collinear off-diagonal torus triple carries arc data. -/
theorem exists_torusArcData_of_general_position_all (r : ℝ → Space) (h : IsSmoothKnot r)
    (hgp : TorusGeneralPosition r) (p : KnotParamTriple)
    (hpZ : torusCollinearity r p = 0) (hpOff : p ∈ TorusOffDiag r) :
    Nonempty (TorusArcData r p) :=
  exists_torusArcData_of_general_position r h p hpZ hpOff (hgp p hpZ hpOff)

/-- Packaging (choice, global hypothesis). -/
noncomputable def torusArcData_of_general_position_all (r : ℝ → Space) (h : IsSmoothKnot r)
    (hgp : TorusGeneralPosition r) (p : KnotParamTriple)
    (hpZ : torusCollinearity r p = 0) (hpOff : p ∈ TorusOffDiag r) :
    TorusArcData r p :=
  Classical.choice (exists_torusArcData_of_general_position_all r h hgp p hpZ hpOff)

/-- The curve of a chart stays inside the trisecant zero set. -/
lemma TorusArcData.γ_in_zeroSet {r : ℝ → Space} {p : KnotParamTriple} (d : TorusArcData r p)
    {t : ℝ} (ht : t ∈ Set.Ioo d.lo d.hi) :
    d.γ t ∈ trisecantZeroSet r := by
  exact (mem_trisecantZeroSet_iff (d.γ t)).mpr (d.γ_good t ht)

/-- **The local zero set is traced by the arc**: on any open subset `W` of
the chart neighbourhood, the trisecant zeros inside `W` are exactly the
curve points inside `W`.  (Forward: the curve stays in the zero set.
Reverse: the covering property puts every zero of `V` — hence of `W` — on
the curve.) -/
theorem arcRange_eq_zeroSet_of_subset {r : ℝ → Space} {p : KnotParamTriple}
    (d : TorusArcData r p) {W : Set KnotParamTriple} (hW : W ⊆ d.V) :
    d.arcRange ∩ W = trisecantZeroSet r ∩ W := by
  ext q
  constructor
  · rintro ⟨hq, hqW⟩
    rcases hq with ⟨t, ht, rfl⟩
    exact ⟨d.γ_in_zeroSet ht, hqW⟩
  · rintro ⟨hqZ, hqW⟩
    rcases (mem_trisecantZeroSet_iff q).mp hqZ with ⟨hq0, hqOff⟩
    rcases d.cover q (hW hqW) hq0 hqOff with ⟨t, ht, htq⟩
    exact ⟨⟨t, ht, htq⟩, hqW⟩

/-- **Embedded local arc**: around a general-position trisecant zero `p`, the
trisecant zero set contains an injective continuous image of an interval
through `p`, contained in a torus neighbourhood `V` of `p`.  (The image is
the injective sub-arc of the chart.) -/
theorem embedded_local_arc {r : ℝ → Space} {p : KnotParamTriple} (d : TorusArcData r p) :
    ∃ V : Set KnotParamTriple, IsOpen V ∧ p ∈ V ∧
      ∃ γ : ℝ → KnotParamTriple, ∃ lo hi : ℝ, lo < 0 ∧ 0 < hi ∧
        ContinuousOn γ (Set.Ioo lo hi) ∧ Set.InjOn γ (Set.Ioo lo hi) ∧ γ 0 = p ∧
        γ '' Set.Ioo lo hi ⊆ trisecantZeroSet r ∧ γ '' Set.Ioo lo hi ⊆ V := by
  refine ⟨d.V, d.V_open, d.p_mem, d.γ, d.lo', d.hi', d.lo'_neg, d.hi'_pos, ?_, d.inj,
    d.γ_zero, ?_, ?_⟩
  · exact d.γ_cont.mono (Set.Ioo_subset_Ioo d.lo'_lo d.hi'_hi)
  · intro q hq
    rcases hq with ⟨t, ht, rfl⟩
    exact d.γ_in_zeroSet ((d.subinterval_mem.2.2) ht)
  · intro q hq
    rcases hq with ⟨t, ht, rfl⟩
    exact d.γ_subV t ht

/-- Continuity of the curve at the base parameter `0` (used to refine the
sub-arc inside pre-assigned neighbourhoods). -/
lemma TorusArcData.continuousAt_base {r : ℝ → Space} {p : KnotParamTriple} (d : TorusArcData r p) :
    ContinuousAt d.γ 0 := by
  exact d.γ_cont.continuousAt (isOpen_Ioo.mem_nhds ⟨d.lo_lt, d.hi_pos⟩)

/-- **Refinement of the injective sub-arc**: given a chart at `p` and any
open torus neighbourhood `U₀` of `p`, there is an injective sub-arc over an
interval `(lo₀,hi₀)` around `0` (still within the chart's injective
interval) whose image lies inside `U₀`. -/
theorem TorusArcData.subarc_within {r : ℝ → Space} {p : KnotParamTriple} (d : TorusArcData r p)
    {U₀ : Set KnotParamTriple} (hU₀o : IsOpen U₀) (hp₀ : p ∈ U₀) :
    ∃ lo₀ hi₀ : ℝ, lo₀ < 0 ∧ 0 < hi₀ ∧ d.lo' ≤ lo₀ ∧ hi₀ ≤ d.hi' ∧
      Set.Ioo lo₀ hi₀ ⊆ Set.Ioo d.lo' d.hi' ∧
      d.γ '' Set.Ioo lo₀ hi₀ ⊆ U₀ ∧ d.γ '' Set.Ioo lo₀ hi₀ ⊆ d.V := by
  have hcat := d.continuousAt_base
  have hγ0U₀ : d.γ 0 ∈ U₀ := by
    simpa [d.γ_zero] using hp₀
  have hpre : d.γ ⁻¹' U₀ ∈ 𝓝 (0 : ℝ) :=
    hcat.preimage_mem_nhds (hU₀o.mem_nhds hγ0U₀)
  rcases exists_Ioo_subset_of_mem_nhds hpre with ⟨a, b, ha, hb, hab⟩
  let lo₀ : ℝ := max a d.lo'
  let hi₀ : ℝ := min b d.hi'
  have h₁ : lo₀ < 0 := by
    dsimp [lo₀]
    exact max_lt ha d.lo'_neg
  have h₂ : 0 < hi₀ := by
    dsimp [hi₀]
    exact lt_min hb d.hi'_pos
  have h₃ : Set.Ioo lo₀ hi₀ ⊆ Set.Ioo a b := by
    intro t ht
    constructor
    · exact lt_of_le_of_lt (le_max_left a d.lo') (by simpa [lo₀] using ht.1)
    · exact lt_of_lt_of_le (by simpa [hi₀] using ht.2) (min_le_left b d.hi')
  have h₄ : Set.Ioo lo₀ hi₀ ⊆ Set.Ioo d.lo' d.hi' := by
    intro t ht
    constructor
    · exact lt_of_le_of_lt (le_max_right a d.lo') (by simpa [lo₀] using ht.1)
    · exact lt_of_lt_of_le (by simpa [hi₀] using ht.2) (min_le_right b d.hi')
  refine ⟨lo₀, hi₀, h₁, h₂, le_max_right a d.lo', min_le_right b d.hi', h₄, ?_, ?_⟩
  · intro q hq
    rcases hq with ⟨t, ht, rfl⟩
    simpa using hab (h₃ ht)
  · intro q hq
    rcases hq with ⟨t, ht, rfl⟩
    exact d.γ_subV t (h₄ ht)

/-- **Refined chart inside a pre-assigned neighbourhood**: from a chart at
`p` and any open torus neighbourhood `U₀` of `p` one obtains a chart whose
neighbourhood is contained in `U₀` (and in the original chart
neighbourhood), sharing the same underlying curve. -/
theorem TorusArcData.refine_within {r : ℝ → Space} {p : KnotParamTriple} (d : TorusArcData r p)
    {U₀ : Set KnotParamTriple} (hU₀o : IsOpen U₀) (hp₀ : p ∈ U₀) :
    ∃ d' : TorusArcData r p, d'.V ⊆ U₀ ∧ d'.V ⊆ d.V := by
  rcases d.subarc_within hU₀o hp₀ with ⟨lo₀, hi₀, h₁, h₂, hlo₀, hhi₀, hsub, hU₀im, hVim⟩
  let d' : TorusArcData r p :=
    ⟨U₀ ∩ d.V, hU₀o.inter d.V_open, ⟨hp₀, d.p_mem⟩, d.lo, d.hi, d.lo_lt, d.hi_pos,
      d.γ, d.γ_cont, d.γ_zero, d.γ_good,
      (fun q hq hqZ hqOff => d.cover q hq.2 hqZ hqOff),
      lo₀, hi₀, le_trans d.lo'_lo hlo₀, h₁, h₂, le_trans hhi₀ d.hi'_hi,
      (Set.InjOn.mono hsub d.inj),
      (fun t ht => ⟨hU₀im ⟨t, ht, rfl⟩, hVim ⟨t, ht, rfl⟩⟩)⟩
  refine ⟨d', ?_, ?_⟩
  · intro q hq
    exact hq.1
  · intro q hq
    exact hq.2

/-- **Overlap (first gluing) lemma**: two local arc charts at the same base
point `p` agree on their overlap.  On `W = V₁ ∩ V₂` both curves trace out
exactly the same portion of the trisecant zero set — the two local families
of trisecants describe the same object up to the torus quotient and up to
their parameterisations. -/
theorem torus_arc_overlap {r : ℝ → Space} {p : KnotParamTriple} (d₁ d₂ : TorusArcData r p) :
    d₁.arcRange ∩ (d₁.V ∩ d₂.V) = trisecantZeroSet r ∩ (d₁.V ∩ d₂.V) ∧
    d₂.arcRange ∩ (d₁.V ∩ d₂.V) = trisecantZeroSet r ∩ (d₁.V ∩ d₂.V) ∧
    IsOpen (d₁.V ∩ d₂.V) ∧ p ∈ d₁.V ∩ d₂.V := by
  constructor
  · exact arcRange_eq_zeroSet_of_subset d₁ (Set.inter_subset_left)
  constructor
  · exact arcRange_eq_zeroSet_of_subset d₂ (Set.inter_subset_right)
  constructor
  · exact d₁.V_open.inter d₂.V_open
  · exact ⟨d₁.p_mem, d₂.p_mem⟩

/-- **Local uniqueness of the trisecant family**: if two charts at `p` are
both confined to a common open set `W`, then on `W` they trace exactly the
same subset of the trisecant zero set (this is the germ-level agreement used
when gluing charts along overlaps). -/
theorem torus_arc_agreement_on_common_subset {r : ℝ → Space} {p : KnotParamTriple}
    (d₁ d₂ : TorusArcData r p) {W : Set KnotParamTriple} (hW₁ : W ⊆ d₁.V) (hW₂ : W ⊆ d₂.V) :
    d₁.arcRange ∩ W = d₂.arcRange ∩ W := by
  rw [arcRange_eq_zeroSet_of_subset d₁ hW₁]
  rw [arcRange_eq_zeroSet_of_subset d₂ hW₂]

end LeanEval.KnotTheory.Quadrisecant
