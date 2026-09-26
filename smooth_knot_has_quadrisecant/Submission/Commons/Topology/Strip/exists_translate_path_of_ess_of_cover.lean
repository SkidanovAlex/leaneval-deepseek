import Mathlib
import Submission.Commons.Topology.Jordan.two_disjoint_closed_not_separating
import Submission.Commons.Topology.Jordan.closed_separates_continuum
import Submission.Commons.Topology.Strip.frontier_component_subset_compl
import Submission.Commons.Topology.Strip.component_meets_inter_of_no_translate_path
import Submission.Commons.Topology.Strip.wall_blocks_translate_path
import Submission.Commons.Topology.Strip.extraction_square_of_open_cover
import Submission.Commons.Topology.Homotopy.vanKampen_generation
import Submission.Commons.Topology.Homotopy.vanKampen_grid
import Submission.Commons.Topology.Strip.path_meets_translate

namespace Commons.Topology.Strip

/-!
# `exists_translate_path_of_ess_of_cover` — state of play (read this first)

Target (unchanged, declared at the bottom of the file): two `T`-invariant sets `W₁, W₂` that are
open in the closed strip `{a ≤ ·.2 ≤ b}`, cover it, and each carry a translate path, have a point
carrying a translate path inside their intersection.
It is a faithful formalisation of Denne's `prop:homology` (*Alternating quadrisecants of knots*,
arXiv:math/0510561) in its **excisive-cover** form: `W₁, W₂` are the traces on the closed strip of
two open subsets of `ℝ²`.  It is TRUE (see the docstring of `ess_inter_of_ess_of_cover_instrip`).

**Status: complete.**  The file is free of placeholders and machine-checked; the target rests on
the crux `ess_inter_of_ess_of_cover_instrip`, which is proved *directly* by the two-set
Mayer–Vietoris decomposition (see the section "The two-set Mayer–Vietoris decomposition route to the
crux" and its theorem `crux_via_decomposition`).  The ingredients of that proof, all in this file or
in the commons, are:

* the **sheet index** `exists_sheet_index_joinedIn` on the free region `U = W₁ ∩ W₂`: a `ℤ`-valued
  function, constant along joins inside `U`, with `ind (T q) = ind q + 1`; it exists as soon as no
  point of `U` is joined to a nonzero translate of itself;
* the commons' **two-set decomposition**
  `Commons.Topology.Jordan.ClosedDisjoint.QD.exists_decomposition` (in
  `Commons/Topology/Jordan/two_disjoint_closed_not_separating.lean`), which splits a locally constant
  `ℤ`-valued function on the complement of two disjoint closed sets into the difference of locally
  constant functions on the two complements — the Mayer–Vietoris statement in the form the sheet
  index needs;
* the `T`-equivariance of the sheet index, which turns the two translate paths `hne₁`, `hne₂` into a
  contradiction: the glued function `f ∘ T - f` on `W₁` / `g ∘ T - g - 1` on `W₂` is locally constant
  on the connected strip `↥S`, hence constant, but its values at `z₁` and at `z₂` are `0` and `-1`.

The target is then derived from the crux by the verified route *extraction relation*
(`exists_relation_of_arbitrary_connector`) + *Janiszewski in `↥S`*
(`Commons.Topology.Jordan.two_disjoint_closed_not_separating`).

The degree-theory layer is complete and axiom-clean: `exists_staircase_shift`,
`exists_translate_path_of_winding_nat`, `exists_translate_path_of_loop_winding`,
`exists_translate_path_of_winding_in_inter` (degree form ⟹ crux), and the grid toolkit
`exists_grid_decomposition_of_two_translate_paths`, `grid_bottom_row_mem_inter`,
`grid_top_row_mem_inter`, `grid_vertical_edge_mem_inter`.

**Warning.**  An earlier revision derived the crux from the "annulus duality"
"a closed `T`-invariant blocking set contains a preconnected piece meeting both boundary lines".
That statement is FALSE — a machine-checked counterexample is
`Submission/Work/Topology/Strip/strip_path_to_translate_of_no_spanning_refutation.lean`
(closed `1`-periodic staircase-walls set with no preconnected piece meeting both lines, whose
complement carries no translate path).  The whole false chain has been removed from this file; the
docstring of the crux records the details.  See
`Submission/Work/Topology/Strip/NOTES_crosscut_bounded_components.md` (last two sections) for the
analysis, for why the excisive hypothesis excludes that counterexample, and for the plan of the
Mayer–Vietoris route that remains open.
-/


open Set

/-- The free region of the closed strip `a ≤ q.2 ≤ b` relative to `K`. -/
def freeRegion (K : Set (ℝ × ℝ)) (a b : ℝ) : Set (ℝ × ℝ) :=
  {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} \ K


/-! ## The irreducible-cut tool (separator) and the level dichotomy

The two lemmas below are the standard inputs of the *irreducible-cut* ("annulus duality") step of
this crux, and they are proved here from the shared commons theorem
`Commons.Topology.Jordan.closed_separates_continuum` (the planar irreducible-cut theorem).

* `exists_preconnected_separator_prod` : if two points `a`, `b ∉ K` are **not** joined in `Kᶜ`
  (the *plane* minus `K`), then some **closed preconnected** `S ⊆ K` does not join them either.
* the *level dichotomy*: a closed set lying in a half-plane `{q.2 ≤ c}` never separates a translate
  pair `z`, `z + (p,0)` lying strictly above `c` — the horizontal segment at the height of `z` is a
  free path.  Its contrapositive is what forces every free level to lie between the heights of the
  separating continuum.

These are exactly the tools by which the crux is reduced to the *annulus duality* statement: with
`K = S \ U` (where `U = W₁ ∩ W₂` is assumed to carry no translate path) and
`K'' := K ∪ {q.2 ≤ a} ∪ {q.2 ≥ b}` (closed, with `K''ᶜ = (S°) \ K`), every point `z` of the open
free region is separated from `T z` inside `K''ᶜ` by hypothesis, so the separator tool produces a
closed preconnected `D_z ⊆ K ∪ {q.2 ≤ a} ∪ {q.2 ≥ b}` separating `z` from `T z`, and the level
dichotomy forces `D_z` to meet both `{q.2 < z.2}` and `{q.2 > z.2}`.  The passage from this
family `D_z` to a *single* preconnected `C ⊆ K` whose heights touch `a` and `b` is the remaining
Mayer–Vietoris content (Denne, *Alternating quadrisecants of knots*, `prop:homology`). -/

/-- The homeomorphism `ℝ × ℝ ≃ₜ ℂ`. -/
noncomputable def planeHomeo : (ℝ × ℝ) ≃ₜ ℂ :=
  (Complex.equivRealProdCLM : ℂ ≃L[ℝ] ℝ × ℝ).toHomeomorph.symm

/-- **The preconnected separating set (product form of `closed_separates_continuum`).**  If a
closed set `K ⊆ ℝ × ℝ` does not join two points `a`, `b ∉ K` (inside `Kᶜ`, the plane complement),
then some closed preconnected `S ⊆ K` does not join them either. -/
theorem exists_preconnected_separator_prod {K : Set (ℝ × ℝ)} (hK : IsClosed K) {a b : ℝ × ℝ}
    (ha : a ∉ K) (hb : b ∉ K)
    (hsep : ¬ ∃ p : Path a b, ∀ t, p t ∉ K) :
    ∃ S : Set (ℝ × ℝ), S ⊆ K ∧ IsClosed S ∧ IsPreconnected S ∧
      ¬ ∃ p : Path a b, ∀ t, p t ∉ S := by
  set e := planeHomeo with he
  set K' : Set ℂ := e '' K with hK'def
  have hK'cl : IsClosed K' := e.isClosedMap K hK
  have ha' : e a ∉ K' := by
    rintro ⟨k, hk, hke⟩
    exact ha (e.injective hke ▸ hk)
  have hb' : e b ∉ K' := by
    rintro ⟨k, hk, hke⟩
    exact hb (e.injective hke ▸ hk)
  have hsep' : ¬ ∃ p : Path (e a) (e b), ∀ t, p t ∉ K' := by
    rintro ⟨p, hp⟩
    refine hsep ⟨p.map e.symm.continuous, fun t => ?_⟩
    intro hmem
    exact hp t ⟨e.symm (p t), hmem, by simp⟩
  obtain ⟨S', hS'K', hS'cl, hS'pc, hS'sep⟩ :=
    Commons.Topology.Jordan.closed_separates_continuum hK'cl ha' hb' hsep'
  refine ⟨e.symm '' S', ?_, ?_, ?_, ?_⟩
  · rintro z ⟨s, hsS', rfl⟩
    obtain ⟨k, hk, hke⟩ := hS'K' hsS'
    rw [← hke, e.symm_apply_apply]
    exact hk
  · exact e.symm.isClosedMap S' hS'cl
  · exact hS'pc.image _ e.symm.continuous.continuousOn
  · rintro ⟨p, hp⟩
    refine hS'sep ⟨p.map e.continuous, fun t => ?_⟩
    intro hmem
    exact hp t ⟨e (p t), hmem, by simp⟩

/-- **Level dichotomy.**  A closed set contained in the half-plane `{q.2 ≤ c}` does not separate a
translate pair lying above `c`: the horizontal segment at the height of `z` avoids it. -/
lemma joinedIn_compl_of_subset_snd_le {p c : ℝ} {S : Set (ℝ × ℝ)}
    (hS : S ⊆ {q : ℝ × ℝ | q.2 ≤ c}) {z : ℝ × ℝ} (hz : c < z.2) :
    JoinedIn Sᶜ z (z.1 + p, z.2) := by
  refine ⟨⟨⟨fun t : Set.Icc (0 : ℝ) 1 => (z.1 + (t : ℝ) * p, z.2), by fun_prop⟩, ?_, ?_⟩, ?_⟩
  · simp
  · simp
  · intro t
    simp only [mem_compl_iff]
    intro hmem
    exact absurd (hS hmem) (not_le.mpr hz)

/-- Dual of the level dichotomy: a set contained in `{c ≤ q.2}` does not separate a translate pair
lying below `c`. -/
lemma joinedIn_compl_of_subset_le_snd {p c : ℝ} {S : Set (ℝ × ℝ)}
    (hS : S ⊆ {q : ℝ × ℝ | c ≤ q.2}) {z : ℝ × ℝ} (hz : z.2 < c) :
    JoinedIn Sᶜ z (z.1 + p, z.2) := by
  refine ⟨⟨⟨fun t : Set.Icc (0 : ℝ) 1 => (z.1 + (t : ℝ) * p, z.2), by fun_prop⟩, ?_, ?_⟩, ?_⟩
  · simp
  · simp
  · intro t
    simp only [mem_compl_iff]
    intro hmem
    exact absurd (hS hmem) (not_le.mpr hz)

/-- **Level dichotomy for a separating set**: a separating set never lies below the level of `z`. -/
lemma snd_le_of_not_joinedIn {p : ℝ} {S : Set (ℝ × ℝ)} {z : ℝ × ℝ} {c : ℝ}
    (hsep : ¬ JoinedIn Sᶜ z (z.1 + p, z.2)) (hc : S ⊆ {q : ℝ × ℝ | q.2 ≤ c}) : z.2 ≤ c := by
  by_contra h
  push Not at h
  exact hsep (joinedIn_compl_of_subset_snd_le hc h)

/-- **Dual level dichotomy**: a separating set never lies above the level of `z`. -/
lemma le_snd_of_not_joinedIn {p : ℝ} {S : Set (ℝ × ℝ)} {z : ℝ × ℝ} {c : ℝ}
    (hsep : ¬ JoinedIn Sᶜ z (z.1 + p, z.2)) (hc : S ⊆ {q : ℝ × ℝ | c ≤ q.2}) : c ≤ z.2 := by
  by_contra h
  push Not at h
  exact hsep (joinedIn_compl_of_subset_le_snd hc h)

/-! ## The `T`-invariant component step

If a connected set `D` is invariant under `T q = (q.1 + p, q.2)`, then any translate path whose
endpoints lie in `D` *stays* in `D`, provided `D` is open in `ℝ × ℝ` (an open connected subset of
the plane is path connected).  This is the `⟸` half of the equivalence
"the crux holds ⟺ the `T`-invariant component of `W₁` meets the one of `W₂`", and it is the reason
why the whole crux may be phrased as the existence of a *common point* of the two essential
components. -/
theorem translate_path_of_T_invariant_component {p : ℝ} {D : Set (ℝ × ℝ)}
    (hDo : IsOpen D) (hDpc : IsConnected D)
    (hT : ∀ q : ℝ × ℝ, q ∈ D ↔ (q.1 + p, q.2) ∈ D) :
    ∃ z : ℝ × ℝ, z ∈ D ∧ JoinedIn D z (z.1 + p, z.2) := by
  obtain ⟨z, hz⟩ := hDpc.nonempty
  have hzT : (z.1 + p, z.2) ∈ D := (hT z).mp hz
  have hpcd : IsPathConnected D := (hDo.isConnected_iff_isPathConnected).mp hDpc
  exact ⟨z, hz, hpcd.joinedIn z hz _ hzT⟩

/-! ## Elementary consequences of "no translate path in `S ∖ K`"

These are the cheap facts that every proof of the crux uses; they are stated for a closed subset
`K ⊆ ℝ × ℝ` together with the hypothesis `hno` that `S ∖ K` (with `S` the closed strip) carries no
translate path. -/

/-- **Every free horizontal translate segment meets `K`.**  If `z ∈ S ∖ K`, the horizontal segment
from `z` to `z + (p,0)` at the level `z.2` is itself a translate path inside `S`; since none exists
inside `S ∖ K`, the segment must meet `K`.  Equivalently: the trace `{x | (x,y) ∈ K}` of `K` on any
free level `y` is a closed `p`-periodic subset of `ℝ` all of whose gaps have length `≤ p`. -/
lemma segment_meets_of_no_translate_path {p a b : ℝ} (hp : 0 < p) {K : Set (ℝ × ℝ)}
    (hno : ∀ z : ℝ × ℝ, z ∈ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} → z ∉ K →
      ¬ JoinedIn ({q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} \ K) z (z.1 + p, z.2))
    {z : ℝ × ℝ} (hz : z ∈ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b}) (hzK : z ∉ K) :
    ∃ t : ℝ, z.1 ≤ t ∧ t ≤ z.1 + p ∧ (t, z.2) ∈ K := by
  by_contra hcon
  push Not at hcon
  have hz2 : a ≤ z.2 ∧ z.2 ≤ b := hz
  have hcont : Continuous fun s : Set.Icc (0:ℝ) 1 =>
      ((z.1 + (s:ℝ)*p, z.2) : ℝ × ℝ) := by fun_prop
  have hmem : ∀ s : Set.Icc (0:ℝ) 1, (z.1 + (s:ℝ)*p, z.2) ∈
      ({q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} \ K) := by
    intro s
    obtain ⟨hs1, hs2⟩ := s.2
    refine ⟨⟨hz2.1, hz2.2⟩, ?_⟩
    intro hmemK
    exact hcon (z.1 + (s:ℝ)*p) (by nlinarith [mul_nonneg hs1 hp.le])
      (by nlinarith [mul_le_of_le_one_left hp.le hs2]) hmemK
  refine hno z hz hzK ⟨{ toContinuousMap :=
      { toFun := fun s : Set.Icc (0:ℝ) 1 => ((z.1 + (s:ℝ)*p, z.2) : ℝ × ℝ)
        continuous_toFun := hcont }, source' := ?_, target' := ?_ }, hmem⟩
  · refine Prod.ext ?_ rfl; simp
  · refine Prod.ext ?_ rfl; simp

/-! ## The zero-dimensional (seam-class) reduction: the pigeonhole step

This is the *combinatorial* half of the zero-dimensional reduction of the annulus duality.
The seam classes are the classes of the crosscut `{0} × [a,b]` under "joined inside the
free region along the seam"; the seam relation sends `y` to `y'` when `(0,y) ~ (p,y')`.
If there are only **finitely many** classes and the seam relation is *serial*, then some
free seam point closes up into a cycle: a free path from `(0,y)` to `(d*p, y)`.
The companion residual (`finite_seam_classes_of_no_wall`, the zero-dimensional form of
Denne's `prop:homology`, delegated to the commons) supplies the finiteness; the
fixed-point lemma `cycle_has_fixed_point` then turns the cycle into a translate path. -/

/-- **Shifting a join forward by `T^k`.**  If `U` is `T`-invariant and `x`, `y` are joined in `U`,
then so are their `T^k`-translates.  (The forward companion of the commons'
`Commons.Topology.Strip.joinedIn_shift_back`.) -/
theorem joinedIn_translate_of_Tinv {p : ℝ} {U : Set (ℝ × ℝ)}
    (hUper : ∀ q : ℝ × ℝ, q ∈ U ↔ (q.1 + p, q.2) ∈ U) (k : ℤ) {x y : ℝ × ℝ}
    (h : JoinedIn U x y) :
    JoinedIn U (x.1 + (k : ℝ) * p, x.2) (y.1 + (k : ℝ) * p, y.2) := by
  classical
  obtain ⟨P, hP⟩ := h
  have hcont : Continuous fun t : Set.Icc (0:ℝ) 1 => ((P t).1 + (k:ℝ)*p, (P t).2) := by fun_prop
  have hmem : ∀ t : Set.Icc (0:ℝ) 1, ((P t).1 + (k:ℝ)*p, (P t).2) ∈ U := by
    intro t
    exact (periodic_shift (p := p) hUper k (P t)).mpr (hP t)
  refine ⟨Path.mk ⟨fun t : Set.Icc (0:ℝ) 1 => ((P t).1 + (k:ℝ)*p, (P t).2), hcont⟩ ?_ ?_, hmem⟩
  · show (((P 0).1 + (k:ℝ)*p, (P 0).2) : ℝ × ℝ) = (x.1 + (k:ℝ)*p, x.2)
    rw [P.source]
  · show (((P 1).1 + (k:ℝ)*p, (P 1).2) : ℝ × ℝ) = (y.1 + (k:ℝ)*p, y.2)
    rw [P.target]

/-- **The zero-dimensional pigeonhole.**  Assume

* `hser` — *seriality*: every free seam point starts a free one-period path;
* `hfin` — there are only **finitely many seam classes**, with representatives `zl`;

then some free seam point `y` closes up: there is `d > 0` with a free path from `(0,y)` to
`(d*p, y)`.  (Iterate the successor on the finitely many classes and use the pigeonhole.) -/
theorem exists_free_cycle_of_finite_seam_classes {p a b : ℝ} (hp : 0 < p)
    {K : Set (ℝ × ℝ)}
    (hinv : ∀ q : ℝ × ℝ, q ∈ K ↔ (q.1 + p, q.2) ∈ K)
    (hser : ∀ y : ℝ, a ≤ y → y ≤ b → ((0 : ℝ), y) ∉ K →
      ∃ y' : ℝ, a ≤ y' ∧ y' ≤ b ∧
        JoinedIn (freeRegion K a b) ((0 : ℝ), y) ((p : ℝ), y'))
    (hfin : ∃ (ι : Type) (_ : Finite ι) (_ : Nonempty ι) (zl : ι → ℝ),
      (∀ i, a ≤ zl i ∧ zl i ≤ b ∧ ((0 : ℝ), zl i) ∉ K) ∧
      (∀ y : ℝ, a ≤ y → y ≤ b → ((0 : ℝ), y) ∉ K →
        ∃ i, JoinedIn (freeRegion K a b) ((0 : ℝ), y) ((0 : ℝ), zl i))) :
    ∃ y : ℝ, a ≤ y ∧ y ≤ b ∧ ((0 : ℝ), y) ∉ K ∧
      ∃ d : ℕ, 0 < d ∧
        JoinedIn (freeRegion K a b) ((0 : ℝ), y) (((d : ℝ) * p), y) := by
  classical
  obtain ⟨ι, hιfin, hιne, zl, hzl, hcov⟩ := hfin
  haveI hιf : Fintype ι := Fintype.ofFinite ι
  set S : Set (ℝ × ℝ) := freeRegion K a b with hS
  have hSper : ∀ q : ℝ × ℝ, q ∈ S ↔ (q.1 + p, q.2) ∈ S := by
    intro q
    rw [hS]
    exact ⟨fun hq => ⟨⟨hq.1.1, hq.1.2⟩, fun hc => hq.2 ((hinv q).mpr hc)⟩,
           fun hq => ⟨⟨hq.1.1, hq.1.2⟩, fun hc => hq.2 ((hinv q).mp hc)⟩⟩
  obtain ⟨i0⟩ := hιne
  -- one-period successor on the free seam points, with the receiver property
  have hstep : ∀ y : ℝ, a ≤ y → y ≤ b → ((0 : ℝ), y) ∉ K →
      ∃ y' : ℝ, a ≤ y' ∧ y' ≤ b ∧ ((0 : ℝ), y') ∉ K ∧
        JoinedIn S ((0 : ℝ), y) ((p : ℝ), y') := by
    intro y hy1 hy2 hyK
    obtain ⟨y', hy'1, hy'2, hJ⟩ := hser y hy1 hy2 hyK
    refine ⟨y', hy'1, hy'2, ?_, hJ⟩
    have hmem : ((p : ℝ), y') ∈ S := by
      have := hJ.somePath_mem 1
      rwa [hJ.somePath.target] at this
    have hK' : ((p : ℝ), y') ∉ K := by
      rw [hS] at hmem
      exact hmem.2
    have hiff : ((p : ℝ), y') ∈ K ↔ ((0 : ℝ), y') ∈ K := by
      have h := hinv ((0 : ℝ), y')
      rw [show (((0 : ℝ) + p), y') = ((p : ℝ), y') by simp] at h
      exact h.symm
    exact fun hc => hK' (hiff.mpr hc)
  -- the subtype of free seam points
  let SF : Type := {y : ℝ // a ≤ y ∧ y ≤ b ∧ ((0 : ℝ), y) ∉ K}
  have hstepSF : ∀ s : SF, ∃ s' : SF, JoinedIn S ((0 : ℝ), s.1) ((p : ℝ), s'.1) := by
    intro s
    obtain ⟨y', hy'1, hy'2, hy'K, hJ⟩ := hstep s.1 s.2.1 s.2.2.1 s.2.2.2
    exact ⟨⟨y', hy'1, hy'2, hy'K⟩, hJ⟩
  let step : SF → SF := fun s => Classical.choose (hstepSF s)
  have hstep_spec : ∀ s : SF, JoinedIn S ((0 : ℝ), s.1) ((p : ℝ), (step s).1) :=
    fun s => Classical.choose_spec (hstepSF s)
  let s0 : SF := ⟨zl i0, (hzl i0).1, (hzl i0).2.1, (hzl i0).2.2⟩
  let aux : ℕ → SF := fun n => Nat.rec s0 (fun _ s => step s) n
  have haux_zero : aux 0 = s0 := rfl
  have haux_succ : ∀ n, aux (n + 1) = step (aux n) := fun n => rfl
  have haux_rel : ∀ n, JoinedIn S ((0 : ℝ), (aux n).1) ((p : ℝ), (aux (n+1)).1) := by
    intro n
    rw [haux_succ n]
    exact hstep_spec (aux n)
  -- class labels
  have hlab : ∀ s : SF, ∃ i : ι, JoinedIn S ((0 : ℝ), s.1) ((0 : ℝ), zl i) :=
    fun s => hcov s.1 s.2.1 s.2.2.1 s.2.2.2
  let lab : SF → ι := fun s => Classical.choose (hlab s)
  have hlab_spec : ∀ s : SF, JoinedIn S ((0 : ℝ), s.1) ((0 : ℝ), zl (lab s)) :=
    fun s => Classical.choose_spec (hlab s)
  -- finiteness of `ι` forces two iterates to share a class
  have hpig : ∃ m n : ℕ, m < n ∧ lab (aux m) = lab (aux n) := by
    have hcard : Fintype.card ι < Fintype.card (Fin (Fintype.card ι + 1)) := by
      rw [Fintype.card_fin]; omega
    obtain ⟨u, v, huv, huv_eq⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt (fun j : Fin (Fintype.card ι + 1) => lab (aux j)) hcard
    refine ⟨min (u : ℕ) (v : ℕ), max (u : ℕ) (v : ℕ), ?_, ?_⟩
    · have hne : (u : ℕ) ≠ (v : ℕ) := fun h => huv (Fin.ext h)
      rcases lt_or_gt_of_ne hne with h | h
      · rw [min_eq_left h.le, max_eq_right h.le]; exact h
      · rw [min_eq_right h.le, max_eq_left h.le]; exact h
    · have hmin : lab (aux (min (u : ℕ) (v : ℕ))) = lab (aux u) ∨
          lab (aux (min (u : ℕ) (v : ℕ))) = lab (aux v) := by
        rcases le_total (u : ℕ) (v : ℕ) with h | h
        · left; rw [min_eq_left h]
        · right; rw [min_eq_right h]
      have hmax : lab (aux (max (u : ℕ) (v : ℕ))) = lab (aux u) ∨
          lab (aux (max (u : ℕ) (v : ℕ))) = lab (aux v) := by
        rcases le_total (u : ℕ) (v : ℕ) with h | h
        · right; rw [max_eq_right h]
        · left; rw [max_eq_left h]
      rcases hmin with h1 | h1 <;> rcases hmax with h2 | h2
      · rw [h1, h2]
      · rw [h1, h2]; exact huv_eq
      · rw [h1, h2]; exact huv_eq.symm
      · rw [h1, h2]
  obtain ⟨m, n, hmn, heq⟩ := hpig
  -- the chain of one-period steps from `m` to `n`
  have haux_free : ((0 : ℝ), (aux m).1) ∈ S :=
    ⟨⟨(aux m).2.1, (aux m).2.2.1⟩, (aux m).2.2.2⟩
  have hchain : ∀ k : ℕ,
      JoinedIn S ((0 : ℝ), (aux m).1) (((k : ℝ) * p), (aux (m + k)).1) := by
    intro k
    induction k with
    | zero => simpa using (JoinedIn.refl haux_free)
    | succ k ih =>
        have hstepk : JoinedIn S ((0 : ℝ), (aux (m + k)).1)
            ((p : ℝ), (aux (m + k + 1)).1) := haux_rel (m + k)
        have hshift : JoinedIn S ((0 : ℝ) + (k : ℝ) * p, (aux (m + k)).1)
            ((p : ℝ) + (k : ℝ) * p, (aux (m + k + 1)).1) :=
          joinedIn_translate_of_Tinv hSper (k : ℤ) hstepk
        have hshift' : JoinedIn S (((k : ℝ) * p), (aux (m + k)).1)
            ((p : ℝ) + (k : ℝ) * p, (aux (m + k + 1)).1) := by simpa using hshift
        have h2 : JoinedIn S ((0 : ℝ), (aux m).1)
            ((p : ℝ) + (k : ℝ) * p, (aux (m + k + 1)).1) := ih.trans hshift'
        convert h2 using 2
        all_goals first | (push_cast; ring) | rw [show m + (k + 1) = m + k + 1 by omega]
  -- the class connector at `n` and at `m`
  have hclose : JoinedIn S ((0 : ℝ), (aux n).1) ((0 : ℝ), (aux m).1) := by
    have h1 := hlab_spec (aux m)
    have h2 := hlab_spec (aux n)
    rw [← heq] at h2
    exact h2.trans h1.symm
  -- translate the connector by `n - m` periods and concatenate with the chain
  have hclose' : JoinedIn S ((((n - m : ℕ) : ℝ) * p), (aux n).1)
      ((((n - m : ℕ) : ℝ) * p), (aux m).1) := by
    have hk : (((n : ℤ) - (m : ℤ) : ℤ) : ℝ) = ((n - m : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub (le_of_lt hmn)]; ring
    have hshift := joinedIn_translate_of_Tinv hSper ((n : ℤ) - (m : ℤ)) hclose
    rw [hk] at hshift
    simpa using hshift
  have hcycle : JoinedIn S ((0 : ℝ), (aux m).1) ((((n - m : ℕ) : ℝ) * p), (aux m).1) := by
    have hc := hchain (n - m)
    rw [show m + (n - m) = n by omega] at hc
    exact hc.trans hclose'
  exact ⟨(aux m).1, (aux m).2.1, (aux m).2.2.1, (aux m).2.2.2, n - m,
    Nat.sub_pos_of_lt hmn, hcycle⟩


/-! ## The two-set van Kampen / Mayer–Vietoris *extraction relation* (proved)

This is the elementary, point-set form of the exactness of
`H₁(W₁ ∩ W₂) → H₁(W₁) ⊕ H₁(W₂) → H₁(W₁ ∪ W₂)` at the middle term, and it is the engine of the
*extraction route* to the crux.

For an open cover `S = W₁ ∪ W₂` of the closed strip `S` (which is convex) and *any* two translate
paths `γ₁ : z₁ → T z₁` in `W₁`, `γ₂ : z₂ → T z₂` in `W₂`, the straight segment `σ` from `z₁` to
`z₂` carries two points whose position on the two translate paths is joined inside `W₁ ∩ W₂` up to
`T`:

  `∃ s t, JoinedIn (W₁ ∩ W₂) (σ s) (T (σ t))`.

*Proof.*  Fill the square bounded by `γ₁`, `γ₂`, the segment `σ` and its translate `T σ` explicitly:
put `F (u,t) = (1-t) • γ₁ u + t • γ₂ u`.  This is continuous into the *convex* strip `S` and
satisfies `F (·,0) = γ₁ ⊆ W₁`, `F (·,1) = γ₂ ⊆ W₂` and `F (1,·) = T ∘ F (0,·)`; also
`F (0,·) = σ` and `F (1,·) = T σ`.  Apply the commons extraction square
`Commons.Topology.Strip.extraction_square_map` with the open sets `U₁ ⊇ W₁`, `U₂ ⊇ W₂` supplied by
`hopen₁`, `hopen₂` (the covering hypothesis is `S = W₁ ∪ W₂ ⊆ U₁ ∪ U₂`).  The extracted
left–right path lies in `U₁ ∩ U₂`, and because the image of `F` lies in `S` it lies in
`W₁ ∩ W₂`; its endpoints are `F (σ_param s) ∈ σ` and `F (T σ_param t) = T (F (σ_param t))`. -/
theorem exists_relation_of_two_translate_paths {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {W₁ W₂ : Set (ℝ × ℝ)}
    (hsub₁ : W₁ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hsub₂ : W₂ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₁ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₁ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₂ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₂ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hcov : W₁ ∪ W₂ = {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    {z₁ z₂ : ℝ × ℝ}
    (hγ₁ : JoinedIn W₁ z₁ (z₁.1 + p, z₁.2)) (hγ₂ : JoinedIn W₂ z₂ (z₂.1 + p, z₂.2)) :
    ∃ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 ∧ t ∈ Set.Icc (0:ℝ) 1 ∧
      JoinedIn (W₁ ∩ W₂) ((1 - s) • z₁ + s • z₂) ((1 - t) • z₁ + t • z₂ + (p, 0)) := by
  classical
  obtain ⟨U₁, hU₁o, hU₁eq⟩ := hopen₁
  obtain ⟨U₂, hU₂o, hU₂eq⟩ := hopen₂
  obtain ⟨P, hP⟩ := hγ₁
  obtain ⟨Q, hQ⟩ := hγ₂
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  have hPmem : ∀ s : ℝ, P (Set.projIcc 0 1 h01 s) ∈ W₁ := fun s => hP _
  have hQmem : ∀ s : ℝ, Q (Set.projIcc 0 1 h01 s) ∈ W₂ := fun s => hQ _
  have hP0 : P (Set.projIcc 0 1 h01 0) = z₁ := by
    rw [Set.projIcc_left h01]; exact P.source
  have hP1 : P (Set.projIcc 0 1 h01 1) = (z₁.1 + p, z₁.2) := by
    rw [Set.projIcc_right h01]; exact P.target
  have hQ0 : Q (Set.projIcc 0 1 h01 0) = z₂ := by
    rw [Set.projIcc_left h01]; exact Q.source
  have hQ1 : Q (Set.projIcc 0 1 h01 1) = (z₂.1 + p, z₂.2) := by
    rw [Set.projIcc_right h01]; exact Q.target
  let F : C(ℝ × ℝ, ℝ × ℝ) :=
    ⟨fun q => (((1 - q.2) * (P (Set.projIcc 0 1 h01 q.1)).1
                 + q.2 * (Q (Set.projIcc 0 1 h01 q.1)).1,
               (1 - q.2) * (P (Set.projIcc 0 1 h01 q.1)).2
                 + q.2 * (Q (Set.projIcc 0 1 h01 q.1)).2)), by fun_prop⟩
  have hstr : ({q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b}) = Set.univ ×ˢ Set.Icc a b := by
    ext q; simp [Set.mem_Icc]
  have hconv : Convex ℝ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} := by
    rw [hstr]; exact convex_univ.prod (convex_Icc a b)
  have hFmem : ∀ q ∈ Commons.Topology.Strip.sq,
      F q ∈ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} := by
    intro q hq
    have hq2 : 0 ≤ q.2 ∧ q.2 ≤ 1 := by
      have h' := hq; rw [Commons.Topology.Strip.sq_eq_rect] at h'
      exact ⟨h'.2.2.1, h'.2.2.2⟩
    have h1 : P (Set.projIcc 0 1 h01 q.1) ∈ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} :=
      hsub₁ (hPmem q.1)
    have h2 : Q (Set.projIcc 0 1 h01 q.1) ∈ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} :=
      hsub₂ (hQmem q.1)
    have h3 : F q = (1 - q.2) • (P (Set.projIcc 0 1 h01 q.1))
        + q.2 • (Q (Set.projIcc 0 1 h01 q.1)) := rfl
    rw [h3]
    exact hconv h1 h2 (by linarith [hq2.2]) hq2.1 (by ring)
  have hFbot : ∀ s : ℝ, F (s, 0) = P (Set.projIcc 0 1 h01 s) := by
    intro s
    show (((1 - (0:ℝ)) * (P (Set.projIcc 0 1 h01 s)).1
        + (0:ℝ) * (Q (Set.projIcc 0 1 h01 s)).1,
      (1 - (0:ℝ)) * (P (Set.projIcc 0 1 h01 s)).2
        + (0:ℝ) * (Q (Set.projIcc 0 1 h01 s)).2) : ℝ × ℝ) = P (Set.projIcc 0 1 h01 s)
    simp
  have hFtop : ∀ s : ℝ, F (s, 1) = Q (Set.projIcc 0 1 h01 s) := by
    intro s
    show (((1 - (1:ℝ)) * (P (Set.projIcc 0 1 h01 s)).1
        + (1:ℝ) * (Q (Set.projIcc 0 1 h01 s)).1,
      (1 - (1:ℝ)) * (P (Set.projIcc 0 1 h01 s)).2
        + (1:ℝ) * (Q (Set.projIcc 0 1 h01 s)).2) : ℝ × ℝ) = Q (Set.projIcc 0 1 h01 s)
    simp
  have hleft : ∀ t : ℝ, F (0, t) = (1 - t) • z₁ + t • z₂ := by
    intro t
    show (((1 - t) * (P (Set.projIcc 0 1 h01 0)).1 + t * (Q (Set.projIcc 0 1 h01 0)).1,
      (1 - t) * (P (Set.projIcc 0 1 h01 0)).2 + t * (Q (Set.projIcc 0 1 h01 0)).2) : ℝ × ℝ)
      = (1 - t) • z₁ + t • z₂
    rw [hP0, hQ0]; rfl
  have hright : ∀ t : ℝ, F (1, t) = (1 - t) • z₁ + t • z₂ + (p, 0) := by
    intro t
    show (((1 - t) * (P (Set.projIcc 0 1 h01 1)).1 + t * (Q (Set.projIcc 0 1 h01 1)).1,
      (1 - t) * (P (Set.projIcc 0 1 h01 1)).2 + t * (Q (Set.projIcc 0 1 h01 1)).2) : ℝ × ℝ)
      = (1 - t) • z₁ + t • z₂ + (p, 0)
    rw [hP1, hQ1]
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_add, Prod.snd_add,
      Prod.fst_zero, Prod.snd_zero, add_zero] <;> ring
  obtain ⟨γ, hγsq, hγ0, hγ1, hγmem⟩ :=
    Commons.Topology.Strip.extraction_square_map hU₁o hU₂o (F := F)
      (fun q hq => by
        have hF := hFmem q hq
        have hc : F q ∈ W₁ ∪ W₂ := by rw [hcov]; exact hF
        rcases hc with h | h
        · exact Or.inl (hU₁eq ▸ h).1
        · exact Or.inr (hU₂eq ▸ h).1)
      (fun q hq hq2 => by
        have hq' : q = (q.1, 0) := Prod.ext rfl hq2
        rw [hq', hFbot]
        exact (hU₁eq ▸ hPmem q.1).1)
      (fun q hq hq2 => by
        have hq' : q = (q.1, 1) := Prod.ext rfl hq2
        rw [hq', hFtop]
        exact (hU₂eq ▸ hQmem q.1).1)
  have hγ0mem : (γ 0).2 ∈ Set.Icc (0:ℝ) 1 := by
    have h' := hγsq 0; rw [Commons.Topology.Strip.sq_eq_rect] at h'
    exact ⟨h'.2.2.1, h'.2.2.2⟩
  have hγ1mem : (γ 1).2 ∈ Set.Icc (0:ℝ) 1 := by
    have h' := hγsq 1; rw [Commons.Topology.Strip.sq_eq_rect] at h'
    exact ⟨h'.2.2.1, h'.2.2.2⟩
  have hmemU : ∀ t : Set.Icc (0:ℝ) 1, F (γ t) ∈ W₁ ∩ W₂ := by
    intro t
    obtain ⟨h1, h2⟩ := hγmem t
    refine ⟨?_, ?_⟩
    · rw [hU₁eq]; exact ⟨h1, hFmem (γ t) (hγsq t)⟩
    · rw [hU₂eq]; exact ⟨h2, hFmem (γ t) (hγsq t)⟩
  have hjoin : JoinedIn (W₁ ∩ W₂) (F (γ 0)) (F (γ 1)) :=
    ⟨{ toContinuousMap :=
        { toFun := fun t : Set.Icc (0:ℝ) 1 => F (γ t),
          continuous_toFun := F.continuous.comp γ.continuous },
       source' := rfl, target' := rfl }, fun t => hmemU t⟩
  refine ⟨(γ 0).2, (γ 1).2, hγ0mem, hγ1mem, ?_⟩
  convert hjoin using 2
  · have hg : γ 0 = (0, (γ 0).2) := Prod.ext hγ0 rfl
    rw [hg, hleft]
  · have hg : γ 1 = (1, (γ 1).2) := Prod.ext hγ1 rfl
    rw [hg, hright]

/-! ## The *Coons patch*: filling a square with four prescribed edges (proved)

The commmons extraction square `extraction_square_map` needs a genuinely two-dimensional map whose
four edges are prescribed (`bottom ⊆ Ω₁`, `top ⊆ Ω₂`, and `right = T ∘ left`).  For the *straight
segment* connector the square is a plain convex interpolation (`F (u,v) = (1-v)•γ₁ u + v•γ₂ u`);
for an **arbitrary** connector `σ` one needs a real filling of the four-gon.  This section builds
the standard *Coons patch* (bilinear boundary interpolation)

  `F (u,v) = (1-v)•β u + v•τ u + (1-u)•λ v + u•ρ v`
  `        - [(1-u)(1-v)•β 0 + u(1-v)•ρ 0 + (1-u)v•τ 0 + uv•ρ 1]`,

which is polynomial (hence continuous, no singularities) and reproduces the four edge curves when
the corner data are matched; the image is clamped to the strip `{a ≤ ·.2 ≤ b}`, which fixes the
edges because they already lie in the strip, and which commutes with `T` (clamping only changes the
height). -/

noncomputable def sclamp (a b : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (q.1, max a (min b q.2))

lemma continuous_sclamp (a b : ℝ) : Continuous (sclamp a b) := by
  unfold sclamp; fun_prop

lemma sclamp_of_mem {a b : ℝ} {q : ℝ × ℝ} (h : a ≤ q.2 ∧ q.2 ≤ b) :
    sclamp a b q = q := by
  unfold sclamp
  rw [min_eq_right h.2, max_eq_right h.1]

structure SqrData where
  bE : C(ℝ, ℝ × ℝ)
  tE : C(ℝ, ℝ × ℝ)
  lE : C(ℝ, ℝ × ℝ)
  rE : C(ℝ, ℝ × ℝ)

noncomputable def coons (D : SqrData) (q : ℝ × ℝ) : ℝ × ℝ :=
  (1 - q.2) • D.bE q.1 + q.2 • D.tE q.1 + (1 - q.1) • D.lE q.2 + q.1 • D.rE q.2
    - (((1 - q.1) * (1 - q.2)) • D.bE 0 + ((q.1 * (1 - q.2))) • D.rE 0
        + (((1 - q.1) * q.2)) • D.tE 0 + ((q.1 * q.2)) • D.rE 1)

lemma continuous_coons (D : SqrData) : Continuous (coons D) := by
  unfold coons; fun_prop

lemma coons_left (D : SqrData) (h0 : D.lE 0 = D.bE 0) (h1 : D.lE 1 = D.tE 0) (v : ℝ) :
    coons D (0, v) = D.lE v := by
  have e1 : D.bE 0 = D.lE 0 := h0.symm
  have e2 : D.tE 0 = D.lE 1 := h1.symm
  unfold coons
  rw [e1, e2]
  ext <;> simp only [Prod.add_def, Prod.sub_def, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    one_smul, zero_smul, add_zero, sub_zero, one_mul, zero_mul] <;> ring

lemma coons_right (D : SqrData) (h0 : D.rE 0 = D.bE 1) (h1 : D.rE 1 = D.tE 1) (v : ℝ) :
    coons D (1, v) = D.rE v := by
  have e1 : D.bE 1 = D.rE 0 := h0.symm
  have e2 : D.tE 1 = D.rE 1 := h1.symm
  unfold coons
  rw [e1, e2]
  ext <;> simp only [Prod.add_def, Prod.sub_def, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    one_smul, zero_smul, add_zero, sub_zero, one_mul, zero_mul] <;> ring

lemma coons_bottom (D : SqrData) (h0 : D.lE 0 = D.bE 0) (h1 : D.rE 0 = D.bE 1) (u : ℝ) :
    coons D (u, 0) = D.bE u := by
  unfold coons
  rw [h0, h1]
  ext <;> simp only [Prod.add_def, Prod.sub_def, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    one_smul, zero_smul, add_zero, sub_zero, one_mul, zero_mul] <;> ring

lemma coons_top (D : SqrData) (h0 : D.lE 1 = D.tE 0) (h1 : D.rE 1 = D.tE 1) (u : ℝ) :
    coons D (u, 1) = D.tE u := by
  unfold coons
  rw [h0, h1]
  ext <;> simp only [Prod.add_def, Prod.sub_def, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    one_smul, zero_smul, add_zero, sub_zero, one_mul, zero_mul] <;> ring


/-- **The extraction relation for an *arbitrary* connector.**  If `σ` is any path in the strip from
a translate-path base point `z₁` of `W₁` to a translate-path base point `z₂` of `W₂`, then `σ`
carries two points that are joined inside `W₁ ∩ W₂` up to `T`.

This is the general form of `exists_relation_of_two_translate_paths` (which is the special case of
the straight-segment connector); together with the sub-path argument it upgrades the reduction of
the crux to *"some translate-path base point of `W₁` is joined to some translate-path base point of
`W₂` inside `W₁ ∩ W₂`"* — the sharpest known form of the residual. -/
theorem exists_relation_of_arbitrary_connector {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {W₁ W₂ : Set (ℝ × ℝ)}
    (hsub₁ : W₁ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hsub₂ : W₂ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₁ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₁ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₂ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₂ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hcov : W₁ ∪ W₂ = {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    {z₁ z₂ : ℝ × ℝ} (hγ₁ : JoinedIn W₁ z₁ (z₁.1 + p, z₁.2))
    (hγ₂ : JoinedIn W₂ z₂ (z₂.1 + p, z₂.2))
    {σ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ)}
    (hσ : ∀ t, σ t ∈ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hσ0 : σ 0 = z₁) (hσ1 : σ 1 = z₂) :
    ∃ s t : Set.Icc (0 : ℝ) 1,
      JoinedIn (W₁ ∩ W₂) (σ s) ((σ t).1 + p, (σ t).2) := by
  classical
  obtain ⟨U₁, hU₁o, hU₁eq⟩ := hopen₁
  obtain ⟨U₂, hU₂o, hU₂eq⟩ := hopen₂
  obtain ⟨P, hP⟩ := hγ₁
  obtain ⟨Q, hQ⟩ := hγ₂
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  have hPmem : ∀ u : ℝ, P (Set.projIcc 0 1 h01 u) ∈ W₁ := fun u => hP _
  have hQmem : ∀ u : ℝ, Q (Set.projIcc 0 1 h01 u) ∈ W₂ := fun u => hQ _
  have hσmem : ∀ u : ℝ, σ (Set.projIcc 0 1 h01 u) ∈ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} :=
    fun u => hσ _
  have hP0 : P (Set.projIcc 0 1 h01 0) = z₁ := by
    rw [Set.projIcc_left h01]; exact P.source
  have hP1 : P (Set.projIcc 0 1 h01 1) = (z₁.1 + p, z₁.2) := by
    rw [Set.projIcc_right h01]; exact P.target
  have hQ0 : Q (Set.projIcc 0 1 h01 0) = z₂ := by
    rw [Set.projIcc_left h01]; exact Q.source
  have hQ1 : Q (Set.projIcc 0 1 h01 1) = (z₂.1 + p, z₂.2) := by
    rw [Set.projIcc_right h01]; exact Q.target
  have hσz : σ (Set.projIcc 0 1 h01 0) = z₁ := by
    rw [Set.projIcc_left h01]; exact hσ0
  have hσo : σ (Set.projIcc 0 1 h01 1) = z₂ := by
    rw [Set.projIcc_right h01]; exact hσ1
  -- the four edges
  let bE : C(ℝ, ℝ × ℝ) := ⟨fun u => P (Set.projIcc 0 1 h01 u), by fun_prop⟩
  let tE : C(ℝ, ℝ × ℝ) := ⟨fun u => Q (Set.projIcc 0 1 h01 u), by fun_prop⟩
  let lE : C(ℝ, ℝ × ℝ) := ⟨fun v => σ (Set.projIcc 0 1 h01 v), by fun_prop⟩
  let rE : C(ℝ, ℝ × ℝ) :=
    ⟨fun v => ((σ (Set.projIcc 0 1 h01 v)).1 + p, (σ (Set.projIcc 0 1 h01 v)).2), by fun_prop⟩
  have hbE : ∀ u, bE u = P (Set.projIcc 0 1 h01 u) := fun u => rfl
  have htE : ∀ u, tE u = Q (Set.projIcc 0 1 h01 u) := fun u => rfl
  have hlE : ∀ v, lE v = σ (Set.projIcc 0 1 h01 v) := fun v => rfl
  have hrE : ∀ v, rE v = ((σ (Set.projIcc 0 1 h01 v)).1 + p,
      (σ (Set.projIcc 0 1 h01 v)).2) := fun v => rfl
  have c_lb : lE 0 = bE 0 := by rw [hlE, hbE, hσz, hP0]
  have c_rb : rE 0 = bE 1 := by rw [hrE, hbE, hσz, hP1]
  have c_lt : lE 1 = tE 0 := by rw [hlE, htE, hσo, hQ0]
  have c_rt : rE 1 = tE 1 := by rw [hrE, htE, hσo, hQ1]
  let D : SqrData := ⟨bE, tE, lE, rE⟩
  have hD : ∀ q, coons D q = coons ⟨bE, tE, lE, rE⟩ q := fun q => rfl
  -- the clamped filling
  let F : C(ℝ × ℝ, ℝ × ℝ) := ⟨fun q => sclamp a b (coons D q), (continuous_sclamp a b).comp
    (continuous_coons D)⟩
  have hF : ∀ q, F q = sclamp a b (coons D q) := fun q => rfl
  -- boundary values
  have hFleft : ∀ v : ℝ, F (0, v) = lE v := by
    intro v
    rw [hF, hD]
    rw [coons_left ⟨bE, tE, lE, rE⟩ c_lb c_lt v]
    exact sclamp_of_mem (hσmem v)
  have hFright : ∀ v : ℝ, F (1, v) = rE v := by
    intro v
    rw [hF, hD]
    rw [coons_right ⟨bE, tE, lE, rE⟩ c_rb c_rt v]
    refine sclamp_of_mem ⟨?_, ?_⟩
    · exact (hσmem v).1
    · exact (hσmem v).2
  have hFbot : ∀ u : ℝ, F (u, 0) = bE u := by
    intro u
    rw [hF, hD]
    rw [coons_bottom ⟨bE, tE, lE, rE⟩ c_lb c_rb u]
    exact sclamp_of_mem (hsub₁ (hPmem u))
  have hFtop : ∀ u : ℝ, F (u, 1) = tE u := by
    intro u
    rw [hF, hD]
    rw [coons_top ⟨bE, tE, lE, rE⟩ c_lt c_rt u]
    exact sclamp_of_mem (hsub₂ (hQmem u))
  -- the image lies in the strip
  have hFmem : ∀ q, F q ∈ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} := by
    intro q
    rw [hF]
    exact ⟨le_max_left a (min b (coons D q).2),
      max_le hab.le (min_le_left b (coons D q).2)⟩
  -- apply the extraction square
  obtain ⟨γ, hγsq, hγ0, hγ1, hγmem⟩ :=
    extraction_square_map hU₁o hU₂o (F := F)
      (fun q hq => by
        have hF' := hFmem q
        have hc : F q ∈ W₁ ∪ W₂ := by rw [hcov]; exact hF'
        rcases hc with h | h
        · exact Or.inl (hU₁eq ▸ h).1
        · exact Or.inr (hU₂eq ▸ h).1)
      (fun q hq hq2 => by
        have hq' : q = (q.1, 0) := Prod.ext rfl hq2
        rw [hq', hFbot]
        exact (hU₁eq ▸ hPmem q.1).1)
      (fun q hq hq2 => by
        have hq' : q = (q.1, 1) := Prod.ext rfl hq2
        rw [hq', hFtop]
        exact (hU₂eq ▸ hQmem q.1).1)
  have hγ0mem : (γ 0).2 ∈ Set.Icc (0:ℝ) 1 := by
    have h' := hγsq 0; rw [sq_eq_rect] at h'
    exact ⟨h'.2.2.1, h'.2.2.2⟩
  have hγ1mem : (γ 1).2 ∈ Set.Icc (0:ℝ) 1 := by
    have h' := hγsq 1; rw [sq_eq_rect] at h'
    exact ⟨h'.2.2.1, h'.2.2.2⟩
  -- the path in W₁ ∩ W₂
  have hmemU : ∀ t : Set.Icc (0:ℝ) 1, F (γ t) ∈ W₁ ∩ W₂ := by
    intro t
    obtain ⟨h1, h2⟩ := hγmem t
    refine ⟨?_, ?_⟩
    · rw [hU₁eq]; exact ⟨h1, hFmem (γ t)⟩
    · rw [hU₂eq]; exact ⟨h2, hFmem (γ t)⟩
  have hjoin : JoinedIn (W₁ ∩ W₂) (F (γ 0)) (F (γ 1)) :=
    ⟨{ toContinuousMap :=
        { toFun := fun t : Set.Icc (0:ℝ) 1 => F (γ t),
          continuous_toFun := F.continuous.comp γ.continuous },
       source' := rfl, target' := rfl }, fun t => hmemU t⟩
  -- identify the endpoints
  have hγ0' : γ 0 = (0, (γ 0).2) := Prod.ext hγ0 rfl
  have hγ1' : γ 1 = (1, (γ 1).2) := Prod.ext hγ1 rfl
  have e0 : F (γ 0) = σ ⟨(γ 0).2, hγ0mem⟩ := by
    conv_lhs => rw [hγ0']
    rw [hFleft, hlE]
    show σ (Set.projIcc 0 1 h01 ((γ 0).2)) = σ ⟨(γ 0).2, hγ0mem⟩
    rw [Set.projIcc_of_mem h01 hγ0mem]
  have e1 : F (γ 1) = ((σ ⟨(γ 1).2, hγ1mem⟩).1 + p, (σ ⟨(γ 1).2, hγ1mem⟩).2) := by
    conv_lhs => rw [hγ1']
    rw [hFright, hrE]
    show ((σ (Set.projIcc 0 1 h01 ((γ 1).2))).1 + p, (σ (Set.projIcc 0 1 h01 ((γ 1).2))).2)
      = ((σ ⟨(γ 1).2, hγ1mem⟩).1 + p, (σ ⟨(γ 1).2, hγ1mem⟩).2)
    rw [Set.projIcc_of_mem h01 hγ1mem]
  refine ⟨⟨(γ 0).2, hγ0mem⟩, ⟨(γ 1).2, hγ1mem⟩, ?_⟩
  rw [← e0, ← e1]
  exact hjoin



/-! ## The boundary argument: the separating cut of `U = W₁ ∩ W₂` lands in `K₂` (or in `K₁`)

Assume the crux's conclusion fails, so that a point `z` of `W₁` carrying a translate path is **not**
joined to its translate inside `U`.  Then (this section) the obstacle is a *preconnected closed* set:
if `z` and `T z` are not joined while avoiding `K₁ ∪ K₂`, some preconnected closed
`C ⊆ K₁ ∪ K₂` separates them; since a preconnected set inside the disjoint closed union lies in one
of the two, and the `C ⊆ K₁` case is immediately contradictory (the translate path of `z` lives in
`K₁ᶜ`), one gets `C ⊆ K₂`.  Moreover the level dichotomy forces the *heights* of `C` to reach the
level of `z` from below and from above.  This is the precise sense in which "the separating boundary
is pushed into `S ∖ U = K₁ ∪ K₂`", and it is where the wall/level lemmas bite. -/

/-! ## The strip-relative irreducible cut

The planar irreducible-cut lemma (`exists_preconnected_separator_prod` / the commons'
`closed_separates_continuum`) is stated in the *plane*, where the complement of the closed set
includes the two half-planes above and below the strip.  The bridging step "joined in the plane
avoiding `K` implies joined in `S ∖ K`" is **false** (counterexample: `K = {y=a} ∪ {y=b} ∪ ({x=0} ∩ S)`
with two points joined by a path dipping below the strip but lying in different components of
`S ∖ K`).  The correct tool is therefore the cut taken *inside the strip*: -/

/-- **Strip-relative irreducible cut.** -/
theorem exists_preconnected_cut_of_not_joined_in_strip {a b : ℝ} (hab : a < b)
    {K : Set (ℝ × ℝ)} (hK : IsClosed K) (hKsub : K ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    {z w : ℝ × ℝ} (hz : z ∈ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b}) (hzK : z ∉ K)
    (hw : w ∈ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b}) (hwK : w ∉ K)
    (hno : ¬ JoinedIn ({q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} \ K) z w) :
    ∃ C : Set (ℝ × ℝ), C ⊆ K ∪ {q : ℝ × ℝ | q.2 = a} ∪ {q : ℝ × ℝ | q.2 = b} ∧
      IsClosed C ∧ IsPreconnected C ∧
      ¬ JoinedIn ({q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} \ C) z w := by
  classical
  set K' : Set (ℝ × ℝ) := K ∪ {q : ℝ × ℝ | q.2 ≤ a} ∪ {q : ℝ × ℝ | q.2 ≥ b} with hK'
  have h1 : IsClosed {q : ℝ × ℝ | q.2 ≤ a} := isClosed_le continuous_snd continuous_const
  have h2 : IsClosed {q : ℝ × ℝ | q.2 ≥ b} := isClosed_le continuous_const continuous_snd
  have hK'cl : IsClosed K' := (hK.union h1).union h2
  have hz' : z ∉ K' := by
    rintro ((hKz | hle) | hge)
    · exact hzK hKz
    · exact absurd hle (not_le.mpr hz.1)
    · exact absurd hge (not_le.mpr hz.2)
  have hw' : w ∉ K' := by
    rintro ((hKw | hle) | hge)
    · exact hwK hKw
    · exact absurd hle (not_le.mpr hw.1)
    · exact absurd hge (not_le.mpr hw.2)
  have hsep : ¬ ∃ q : Path z w, ∀ t, q t ∉ K' := by
    rintro ⟨q, hq⟩
    refine hno ⟨q, fun t => ?_⟩
    have h := hq t
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · by_contra hcon
      push Not at hcon
      exact h (Or.inl (Or.inr (le_of_lt hcon)))
    · by_contra hcon
      push Not at hcon
      exact h (Or.inr (le_of_lt hcon))
    · intro hmemK
      exact h (Or.inl (Or.inl hmemK))
  obtain ⟨C₀, hC₀K', hC₀cl, hC₀pc, hC₀sep⟩ :=
    exists_preconnected_separator_prod hK'cl hz' hw' hsep
  have himg : sclamp a b '' C₀ ⊆ K ∪ {q : ℝ × ℝ | q.2 = a} ∪ {q : ℝ × ℝ | q.2 = b} := by
    rintro q ⟨q₀, hq₀, rfl⟩
    rcases hC₀K' hq₀ with (hKq | hle) | hge
    · exact Or.inl (Or.inl (by rw [sclamp_of_mem (hKsub hKq)]; exact hKq))
    · refine Or.inl (Or.inr ?_)
      show max a (min b q₀.2) = a
      rw [min_eq_right (hle.trans hab.le), max_eq_left hle]
    · refine Or.inr ?_
      show max a (min b q₀.2) = b
      rw [min_eq_left hge, max_eq_right hab.le]
  have hEqA : IsClosed {q : ℝ × ℝ | q.2 = a} := isClosed_eq continuous_snd continuous_const
  have hEqB : IsClosed {q : ℝ × ℝ | q.2 = b} := isClosed_eq continuous_snd continuous_const
  refine ⟨closure (sclamp a b '' C₀),
    closure_minimal himg ((hK.union hEqA).union hEqB), isClosed_closure, ?_, ?_⟩
  · exact hC₀pc.image _ (continuous_sclamp a b).continuousOn |>.closure
  · rintro ⟨γ, hγ⟩
    refine hC₀sep ⟨γ, fun t => ?_⟩
    have hS : γ t ∈ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} := (hγ t).1
    have hCnot : γ t ∉ closure (sclamp a b '' C₀) := (hγ t).2
    intro hmemC₀
    exact hCnot (subset_closure ⟨γ t, hmemC₀, sclamp_of_mem hS⟩)

/-! ## Narrowing the `∂S` option in the strip-relative cut

The strip-relative cut produced above lands in `K ∪ {·.2 = a} ∪ {·.2 = b}`.  The boundary lines are
an artefact of the clamping step, and the next question is whether one can get rid of them.  The two
lemmas below say what can be said unconditionally:

* a preconnected closed set contained in the boundary lines alone **cannot separate** two points of
  the open strip lying at the *same* height (the horizontal segment at that height avoids it);
* consequently the cut, which does separate such a pair, must actually **meet `K`**.

So the `∂S`-part of the cut cannot be all of it: the cut always contains a point of `K = K₁ ∪ K₂`.
(Eliminating `∂S` completely — forcing the whole cut into `K₁` or `K₂` — is *not* a formal
consequence: `C ∩ S°` is only relatively open in `C`, so the naive "preconnected set splits into its
`∂S`-part and its `S°`-part" argument is invalid, and a genuine argument is needed.) -/

/-- The horizontal path at the (common) height of `z`. -/
noncomputable def hpath (z w : ℝ × ℝ) (t : Set.Icc (0:ℝ) 1) : ℝ × ℝ :=
  ((1 - (t:ℝ)) * z.1 + (t:ℝ) * w.1, z.2)

lemma hpath_cont (z w : ℝ × ℝ) : Continuous (hpath z w) := by unfold hpath; fun_prop

lemma hpath_snd (z w : ℝ × ℝ) (t : Set.Icc (0:ℝ) 1) : (hpath z w t).2 = z.2 := rfl

lemma hpath_zero (z w : ℝ × ℝ) : hpath z w 0 = z := by unfold hpath; ext <;> simp

lemma hpath_one (z w : ℝ × ℝ) (hzw : z.2 = w.2) : hpath z w 1 = w := by
  unfold hpath; ext <;> simp [hzw]

lemma hpath_mem_strip {a b : ℝ} {z w : ℝ × ℝ} (hz : z ∈ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b})
    (t : Set.Icc (0:ℝ) 1) : hpath z w t ∈ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} := by
  show a ≤ (hpath z w t).2 ∧ (hpath z w t).2 ≤ b
  rw [hpath_snd]
  exact ⟨le_of_lt hz.1, le_of_lt hz.2⟩

lemma hpath_mem_compl {a b : ℝ} {C : Set (ℝ × ℝ)}
    (hC : C ⊆ {q : ℝ × ℝ | q.2 = a} ∪ {q : ℝ × ℝ | q.2 = b})
    {z w : ℝ × ℝ} (hz : z ∈ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b}) (t : Set.Icc (0:ℝ) 1) :
    hpath z w t ∈ Cᶜ := by
  simp only [Set.mem_compl_iff]
  intro hmem
  rcases hC hmem with h | h
  · have h1 : (hpath z w t).2 = a := h
    rw [hpath_snd] at h1
    linarith [hz.1, h1]
  · have h1 : (hpath z w t).2 = b := h
    rw [hpath_snd] at h1
    linarith [hz.2, h1]

/-- **The cut must meet `K`.** -/
theorem exists_cut_meeting_K_of_not_joined_in_strip {a b : ℝ} (hab : a < b)
    {K : Set (ℝ × ℝ)} (hK : IsClosed K) (hKsub : K ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    {z w : ℝ × ℝ} (hz : z ∈ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b}) (hzK : z ∉ K)
    (hw : w ∈ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b}) (hwK : w ∉ K) (hzw : z.2 = w.2)
    (hno : ¬ JoinedIn ({q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} \ K) z w) :
    ∃ C : Set (ℝ × ℝ), C ⊆ K ∪ {q : ℝ × ℝ | q.2 = a} ∪ {q : ℝ × ℝ | q.2 = b} ∧
      IsClosed C ∧ IsPreconnected C ∧
      ¬ JoinedIn ({q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} \ C) z w ∧ (C ∩ K).Nonempty := by
  obtain ⟨C, hCK, hCcl, hCpc, hCsep⟩ :=
    exists_preconnected_cut_of_not_joined_in_strip hab hK hKsub hz hzK hw hwK hno
  refine ⟨C, hCK, hCcl, hCpc, hCsep, ?_⟩
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  have hCb : C ⊆ {q : ℝ × ℝ | q.2 = a} ∪ {q : ℝ × ℝ | q.2 = b} := by
    intro q hq
    rcases hCK hq with (hKq | hline) | hline
    · exact absurd ⟨hq, hKq⟩ (Set.eq_empty_iff_forall_notMem.mp hemp q)
    · exact Or.inl hline
    · exact Or.inr hline
  refine hCsep ⟨Path.mk ⟨hpath z w, hpath_cont z w⟩ (hpath_zero z w) (hpath_one z w hzw),
    fun t => ⟨hpath_mem_strip hz t, hpath_mem_compl hCb hz t⟩⟩

/-- **The separating cut.**  Two points outside the disjoint closed sets `K₁, K₂` that are not
joined in `(K₁ ∪ K₂)ᶜ` are separated by a preconnected closed `C ⊆ K₁ ∪ K₂`. -/
theorem exists_separator_of_not_joined {p : ℝ} {K₁ K₂ : Set (ℝ × ℝ)} (hK₁ : IsClosed K₁)
    (hK₂ : IsClosed K₂) {z : ℝ × ℝ}
    (hz : z ∉ K₁ ∪ K₂) (hzT : (z.1 + p, z.2) ∉ K₁ ∪ K₂)
    (hno : ¬ JoinedIn ((K₁ ∪ K₂)ᶜ) z (z.1 + p, z.2)) :
    ∃ C : Set (ℝ × ℝ), C ⊆ K₁ ∪ K₂ ∧ IsClosed C ∧ IsPreconnected C ∧
      ¬ JoinedIn (Cᶜ) z (z.1 + p, z.2) := by
  have hsep : ¬ ∃ q : Path z (z.1 + p, z.2), ∀ t, q t ∉ K₁ ∪ K₂ := by
    rintro ⟨q, hq⟩
    exact hno ⟨q, fun t => hq t⟩
  obtain ⟨C, hCK, hCcl, hCpc, hCsep⟩ :=
    exists_preconnected_separator_prod (hK₁.union hK₂) hz hzT hsep
  refine ⟨C, hCK, hCcl, hCpc, ?_⟩
  rintro ⟨q, hq⟩
  exact hCsep ⟨q, fun t hmem => hq t hmem⟩

/-- **The dichotomy.**  A preconnected subset of the union of two disjoint closed sets lies in one
of them. -/
theorem preconnected_subset_left_or_right {K₁ K₂ C : Set (ℝ × ℝ)} (hK₁ : IsClosed K₁)
    (hK₂ : IsClosed K₂) (hdisj : Disjoint K₁ K₂) (hC : C ⊆ K₁ ∪ K₂)
    (hCpc : IsPreconnected C) : C ⊆ K₁ ∨ C ⊆ K₂ := by
  have hinter : C ∩ (K₁ ∩ K₂) = ∅ := by
    rw [Set.disjoint_iff_inter_eq_empty.mp hdisj, Set.inter_empty]
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hCpc K₁ K₂ hK₁ hK₂ hC hinter with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **Where it bites, case `C ⊆ K₁`.**  Such a separator is contradictory as soon as the two points
*are* joined inside `K₁ᶜ` (as happens when one of them is a translate-path base point of
`W₁ = S ∖ K₁`). -/
theorem false_of_separator_subset_left {p : ℝ} {K₁ C : Set (ℝ × ℝ)} {z : ℝ × ℝ}
    (hCsub : C ⊆ K₁) (hCsep : ¬ JoinedIn (Cᶜ) z (z.1 + p, z.2))
    (hjoin : JoinedIn (K₁ᶜ) z (z.1 + p, z.2)) : False := by
  obtain ⟨q, hq⟩ := hjoin
  exact hCsep ⟨q, fun t hmem => hq t (hCsub hmem)⟩

/-- **What the level dichotomy says about the separator.**  A closed set separating a point `z` from
its translate is contained in no half-plane `{·.2 ≤ c}` with `c < z.2`, nor in `{c ≤ ·.2}` with
`z.2 < c`: its heights reach the level of `z` from below and from above. -/
theorem height_reaches_of_separator {p : ℝ} {C : Set (ℝ × ℝ)} {z : ℝ × ℝ}
    (hCsep : ¬ JoinedIn (Cᶜ) z (z.1 + p, z.2)) :
    (∀ c : ℝ, (∀ q ∈ C, q.2 ≤ c) → z.2 ≤ c) ∧
      (∀ c : ℝ, (∀ q ∈ C, c ≤ q.2) → c ≤ z.2) := by
  constructor
  · intro c hc
    by_contra hcon
    push Not at hcon
    exact hCsep (joinedIn_compl_of_subset_snd_le (S := C) hc hcon)
  · intro c hc
    by_contra hcon
    push Not at hcon
    exact hCsep (joinedIn_compl_of_subset_le_snd (S := C) hc hcon)

/-- **The separating cut lands in `K₂`.**  If `z ∉ K₁ ∪ K₂` carries a translate path in `K₁ᶜ` and
`z`, `T z` are not joined while avoiding `K₁ ∪ K₂`, then the separating cut can be taken
preconnected closed inside `K₂`, and its heights reach the level of `z` from both sides. -/
theorem exists_separator_in_K₂_of_not_joined {p : ℝ} {K₁ K₂ : Set (ℝ × ℝ)} (hK₁ : IsClosed K₁)
    (hK₂ : IsClosed K₂) (hdisj : Disjoint K₁ K₂) {z : ℝ × ℝ}
    (hz : z ∉ K₁ ∪ K₂) (hzT : (z.1 + p, z.2) ∉ K₁ ∪ K₂)
    (hjoin : JoinedIn (K₁ᶜ) z (z.1 + p, z.2))
    (hno : ¬ JoinedIn ((K₁ ∪ K₂)ᶜ) z (z.1 + p, z.2)) :
    ∃ C : Set (ℝ × ℝ), C ⊆ K₂ ∧ IsClosed C ∧ IsPreconnected C ∧
      ¬ JoinedIn (Cᶜ) z (z.1 + p, z.2) ∧
      (∀ c : ℝ, (∀ q ∈ C, q.2 ≤ c) → z.2 ≤ c) ∧
      (∀ c : ℝ, (∀ q ∈ C, c ≤ q.2) → c ≤ z.2) := by
  obtain ⟨C, hCK, hCcl, hCpc, hCsep⟩ := exists_separator_of_not_joined hK₁ hK₂ hz hzT hno
  rcases preconnected_subset_left_or_right hK₁ hK₂ hdisj hCK hCpc with h1 | h1
  · exact absurd (false_of_separator_subset_left h1 hCsep hjoin) not_false
  · obtain ⟨h2, h3⟩ := height_reaches_of_separator hCsep
    exact ⟨C, h1, hCcl, hCpc, hCsep, h2, h3⟩

/-- **The extraction route to the crux.**  If besides the hypotheses of the crux one has two
translate paths, one in `W₁` and one in `W₂`, whose *straight segment* lies entirely in
`W₁ ∩ W₂`, then the crux follows: the segment itself connects the two points produced by the
extraction relation, so the `T`-related points are joined inside `W₁ ∩ W₂`.

(Equivalently: the crux holds as soon as some point of `W₁` and some point of `W₂`, each the base
point of a translate path in its own set, are joined *inside the intersection* by the straight
segment.) -/
theorem exists_translate_path_of_ess_of_cover_of_common_segment {p a b : ℝ} (hp : 0 < p)
    (hab : a < b)
    {W₁ W₂ : Set (ℝ × ℝ)}
    (hsub₁ : W₁ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hsub₂ : W₂ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₁ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₁ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₂ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₂ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hcov : W₁ ∪ W₂ = {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hres : ∃ z₁ z₂ : ℝ × ℝ,
      JoinedIn W₁ z₁ (z₁.1 + p, z₁.2) ∧ JoinedIn W₂ z₂ (z₂.1 + p, z₂.2) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → ((1 - t) • z₁ + t • z₂) ∈ W₁ ∩ W₂)) :
    ∃ z : ℝ × ℝ, z ∈ W₁ ∩ W₂ ∧ JoinedIn (W₁ ∩ W₂) z (z.1 + p, z.2) := by
  obtain ⟨z₁, z₂, hγ₁, hγ₂, hseg⟩ := hres
  obtain ⟨s, t, hs, ht, hrel⟩ :=
    exists_relation_of_two_translate_paths hp hab hsub₁ hsub₂ hopen₁ hopen₂ hcov hγ₁ hγ₂
  have hsegmem : ((1 - s) • z₁ + s • z₂) ∈ W₁ ∩ W₂ := hseg s hs
  have hsegmem' : ((1 - t) • z₁ + t • z₂) ∈ W₁ ∩ W₂ := hseg t ht
  -- the sub-segment of the straight segment between the parameters `s` and `t`
  have hst : JoinedIn (W₁ ∩ W₂) ((1 - s) • z₁ + s • z₂) ((1 - t) • z₁ + t • z₂) := by
    have harith : ∀ τ : Set.Icc (0:ℝ) 1,
        (s + (τ:ℝ) * (t - s)) ∈ Set.Icc (0:ℝ) 1 := by
      intro τ
      have h1 : s + (τ:ℝ) * (t - s) = (1 - (τ:ℝ)) * s + (τ:ℝ) * t := by ring
      rw [h1]
      constructor <;> nlinarith [τ.2.1, τ.2.2, hs.1, hs.2, ht.1, ht.2]
    refine ⟨Path.mk ⟨fun τ : Set.Icc (0:ℝ) 1 =>
      ((1 - (s + (τ:ℝ) * (t - s))) • z₁ + (s + (τ:ℝ) * (t - s)) • z₂), by fun_prop⟩ ?_ ?_, ?_⟩
    · show ((1 - (s + ((0 : Set.Icc (0:ℝ) 1) : ℝ) * (t - s))) • z₁
        + (s + ((0 : Set.Icc (0:ℝ) 1) : ℝ) * (t - s)) • z₂) = (1 - s) • z₁ + s • z₂
      simp
    · show ((1 - (s + ((1 : Set.Icc (0:ℝ) 1) : ℝ) * (t - s))) • z₁
        + (s + ((1 : Set.Icc (0:ℝ) 1) : ℝ) * (t - s)) • z₂) = (1 - t) • z₁ + t • z₂
      have h1 : ((1 : Set.Icc (0:ℝ) 1) : ℝ) = 1 := rfl
      have hst' : s + (1:ℝ) * (t - s) = t := by ring
      rw [h1, hst']
    · intro τ
      exact hseg _ (harith τ)
  have hT : JoinedIn (W₁ ∩ W₂) ((1 - t) • z₁ + t • z₂)
      ((1 - t) • z₁ + t • z₂ + (p, 0)) := hst.symm.trans hrel
  refine ⟨(1 - t) • z₁ + t • z₂, hsegmem', ?_⟩
  convert hT using 1
  ext <;> simp [Prod.add_def]

/-- **The extraction route to the crux, sharpest form.**  The crux follows as soon as *some*
translate-path base point of `W₁` is joined, **inside `W₁ ∩ W₂`**, to *some* translate-path base
point of `W₂`.  (Compare `exists_translate_path_of_ess_of_cover_of_common_segment`, where the
joining path is required to be the straight segment.) -/
theorem exists_translate_path_of_ess_of_cover_of_joined_points {p a b : ℝ} (hp : 0 < p)
    (hab : a < b)
    {W₁ W₂ : Set (ℝ × ℝ)}
    (hsub₁ : W₁ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hsub₂ : W₂ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₁ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₁ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₂ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₂ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hcov : W₁ ∪ W₂ = {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hres : ∃ z₁ z₂ : ℝ × ℝ, JoinedIn W₁ z₁ (z₁.1 + p, z₁.2) ∧
      JoinedIn W₂ z₂ (z₂.1 + p, z₂.2) ∧ JoinedIn (W₁ ∩ W₂) z₁ z₂) :
    ∃ z : ℝ × ℝ, z ∈ W₁ ∩ W₂ ∧ JoinedIn (W₁ ∩ W₂) z (z.1 + p, z.2) := by
  classical
  obtain ⟨z₁, z₂, hJ₁, hJ₂, hpath⟩ := hres
  obtain ⟨σ, hσmem⟩ := hpath
  have hσstrip : ∀ t : Set.Icc (0:ℝ) 1, σ t ∈ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} :=
    fun t => hsub₁ (hσmem t).1
  obtain ⟨s, t, hrel⟩ := exists_relation_of_arbitrary_connector hp hab hsub₁ hsub₂ hopen₁ hopen₂
    hcov hJ₁ hJ₂ (σ := σ) hσstrip σ.source σ.target
  -- the sub-path of σ between the parameters s and t lies in U
  have harith : ∀ τ : Set.Icc (0:ℝ) 1,
      ((s : ℝ) + (τ:ℝ) * ((t:ℝ) - (s:ℝ))) ∈ Set.Icc (0:ℝ) 1 := by
    intro τ
    have h1 : (s:ℝ) + (τ:ℝ) * ((t:ℝ) - (s:ℝ)) = (1 - (τ:ℝ)) * (s:ℝ) + (τ:ℝ) * (t:ℝ) := by ring
    rw [h1]
    have hs := s.2; have ht := t.2; have hτ := τ.2
    constructor <;> nlinarith [hs.1, hs.2, ht.1, ht.2, hτ.1, hτ.2]
  have hst : JoinedIn (W₁ ∩ W₂) (σ s) (σ t) := by
    let ρ : Set.Icc (0:ℝ) 1 → Set.Icc (0:ℝ) 1 := fun τ => ⟨_, harith τ⟩
    have hρc : Continuous ρ := by
      apply Continuous.subtype_mk
      show Continuous fun τ : Set.Icc (0:ℝ) 1 => ((s:ℝ) + (τ:ℝ) * ((t:ℝ) - (s:ℝ)))
      fun_prop
    refine ⟨Path.mk ⟨fun τ : Set.Icc (0:ℝ) 1 => σ (ρ τ), σ.continuous.comp hρc⟩ ?_ ?_, ?_⟩
    · show σ (ρ 0) = σ s
      congr 1
      apply Subtype.ext
      show ((s:ℝ) + ((0 : Set.Icc (0:ℝ) 1) : ℝ) * ((t:ℝ) - (s:ℝ))) = (s:ℝ)
      simp
    · show σ (ρ 1) = σ t
      congr 1
      apply Subtype.ext
      show ((s:ℝ) + ((1 : Set.Icc (0:ℝ) 1) : ℝ) * ((t:ℝ) - (s:ℝ))) = (t:ℝ)
      have h1 : ((1 : Set.Icc (0:ℝ) 1) : ℝ) = 1 := rfl
      rw [h1]; ring
    · intro τ
      exact hσmem (ρ τ)
  have hT : JoinedIn (W₁ ∩ W₂) (σ t) ((σ t).1 + p, (σ t).2) := hst.symm.trans hrel
  exact ⟨σ t, hσmem t, hT⟩

/-- **The crux in the case where one point carries translate paths in *both* sets.**  This is the
immediate corollary of the reduction `exists_translate_path_of_ess_of_cover_of_common_segment`
(the segment joining the point to itself lies in `W₁ ∩ W₂`), and it shows that the whole difficulty
of the crux sits in the case `E₁ ∩ E₂ = ∅` (`Eᵢ` = the set of translate-path base points of `Wᵢ`). -/
theorem exists_translate_path_of_ess_of_cover_of_common_point {p a b : ℝ} (hp : 0 < p)
    (hab : a < b)
    {W₁ W₂ : Set (ℝ × ℝ)}
    (hsub₁ : W₁ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hsub₂ : W₂ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₁ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₁ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₂ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₂ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hcov : W₁ ∪ W₂ = {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hboth : ∃ z : ℝ × ℝ, z ∈ W₁ ∧ z ∈ W₂ ∧ JoinedIn W₁ z (z.1 + p, z.2) ∧
      JoinedIn W₂ z (z.1 + p, z.2)) :
    ∃ z : ℝ × ℝ, z ∈ W₁ ∩ W₂ ∧ JoinedIn (W₁ ∩ W₂) z (z.1 + p, z.2) := by
  obtain ⟨z, hz₁, hz₂, hJ₁, hJ₂⟩ := hboth
  have hres : ∃ z₁ z₂ : ℝ × ℝ,
      JoinedIn W₁ z₁ (z₁.1 + p, z₁.2) ∧ JoinedIn W₂ z₂ (z₂.1 + p, z₂.2) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → ((1 - t) • z₁ + t • z₂) ∈ W₁ ∩ W₂) := by
    refine ⟨z, z, hJ₁, hJ₂, fun t _ => ?_⟩
    have h : (1 - t) • z + t • z = z := by
      rw [← add_smul, sub_add_cancel, one_smul]
    rw [h]; exact ⟨hz₁, hz₂⟩
  exact exists_translate_path_of_ess_of_cover_of_common_segment hp hab hsub₁ hsub₂ hopen₁ hopen₂
    hcov hres

/-! ## STATUS — the zero-dimensional reduction, and the exact residual

The crux is now reduced to a **zero-dimensional** statement about the crosscut `{0} × [a,b]`
(`= the seam`).  With `freeRegion K a b = S ∖ K` and seam classes = classes of free seam points
under "joined inside `freeRegion` along the seam":

* **Proved above (ships with this file):** the *pigeonhole*
  `exists_free_cycle_of_finite_seam_classes` — seriality of the seam relation + finitely many seam
  classes ⟹ a free path `(0,y) → (d*p, y)` (a closed cycle), together with the transport lemma
  `joinedIn_translate_of_Tinv` it uses.
* **Proved in `Work/Topology/Strip/zerodim_seam.lean`:** the assembly
  `exists_translate_path_of_finite_seam_classes` (cycle + `cycle_has_fixed_point` ⟹ an honest
  translate path) and its contrapositive
  `infinite_seam_classes_of_no_translate_path`: *no translate path + seriality ⟹ the seam classes
  are infinite*.
* **The residual** (stated in that work file, delegated as
  `Topology/Strip/finite_seam_classes_of_no_wall`): `K` meets every horizontal level and carries no
  wall ⟹ **finitely many** seam classes.  This is the zero-dimensional form of Denne's
  `prop:homology`; with it, `no translate path` and `no wall` are incompatible, which is exactly
  the annulus duality.  Its companion obligation is the *prescribed-start barrier lemma*
  (`Topology/Strip/one_period_free_path_of_free_start`, seriality), already isolated in
  `Work/Topology/Strip/cycle_has_fixed_point.lean` with case (E) proved there.

So the remaining gap is now two statements about the one-dimensional seam, both of which are
crux-equivalent; everything between them (pigeonhole, cycle extraction, fixed point, wall
transfer, layer transfer) is proved.

**Update (seventh pass) — the extraction relation, and the sharpened residual.**  Two new *proved*
lemmas now sit above the crux (see the section "the two-set van Kampen / Mayer–Vietoris extraction
relation"):

* `exists_relation_of_two_translate_paths` — the elementary form of the exactness of
  `H₁(W₁∩W₂) → H₁(W₁) ⊕ H₁(W₂) → H₁(W₁∪W₂)` at the middle term.  For an open cover
  `S = W₁ ∪ W₂` of the convex strip and *any* two translate paths, the segment joining their base
  points carries two points `p, q` with `p ~ T q` inside `W₁ ∩ W₂`.
* `exists_translate_path_of_ess_of_cover_of_common_segment` — the resulting *reduction*: the crux
  follows as soon as some translate-path base point of `W₁` and some translate-path base point of
  `W₂` are joined **inside `W₁ ∩ W₂` by the straight segment**.
* the *Coons patch* (`sclamp`, `SqrData`, `coons` and its four edge lemmas) — the explicit filling
  of a square with four prescribed edges (bilinear boundary interpolation, clamped to the strip);
* `exists_relation_of_arbitrary_connector` — the same extraction relation for an **arbitrary**
  connector `σ` (any path in the strip from a translate-path base point of `W₁` to one of `W₂`);
* `exists_translate_path_of_ess_of_cover_of_joined_points` — the resulting *sharpened reduction*:
  the crux follows as soon as some translate-path base point of `W₁` is joined to some
  translate-path base point of `W₂` **inside `W₁ ∩ W₂` by *any* path** — this is the sharpest known
  form of the residual (it is the conclusion of Denne's Mayer–Vietoris step, read off before the
  degree argument);
* `exists_translate_path_of_ess_of_cover_of_common_point` — the immediate case `E₁ ∩ E₂ ≠ ∅`.

So the crux is now reduced to a statement about the *geometry* of the two sets of essential base
points `Eᵢ = {z ∈ Wᵢ | JoinedIn Wᵢ z (z.1+p, z.2)}` (open, `T`-invariant):
`E₁ ∩ E₂ ≠ ∅` finishes immediately (take `z₁ = z₂`), and otherwise one must find `z₁ ∈ E₁`,
`z₂ ∈ E₂` whose segment lies in `U = W₁ ∩ W₂`.  The structural analysis of this residue (why the
obvious counterexamples — spiral ladders split between the two sets — cannot work) is recorded in
`Work/Topology/Strip/NOTES_extraction_relation.md`.

**Update (sixth pass).**  The *seriality* half of this reduction is **FALSE**:
`Work/Topology/Strip/circle_orbit_counterexample.lean` (placeholder-free) builds a closed `T`-invariant
wall-free `K ⊆ S` whose free component at a free seam point is a bounded disk that never
reaches the fibre `{q.1 = p}`.  So the seam-relation route is dead as stated — wall-freeness does
not exclude bounded free islands — and the pigeonhole shipped above, while valid, has an
unavailable hypothesis.  The finiteness statement (`finite_seam_classes_of_no_wall`) is untouched
by that counterexample (its `K` fails the "meets every level" hypothesis) and remains open. -/



/-- **The free-gap step of the blocking lemma.**  If a path `γ` in the plane runs from the line
`{·.1 = 0}` to the line `{·.1 = p}` while avoiding the `p`-periodic set `K`, and additionally the
vertical segment at `x = p` between the two endpoint heights avoids `K`, then `Kᶜ` contains a
translate path: namely `γ` followed by that vertical segment, which ends at `(p, (γ 0).2) = T (γ 0)`
because `(γ 0).1 = 0`.

(This is the case of `exists_wall_of_no_translate_path` in which the barrier produced by
`Commons.Topology.Strip.barrier_bottom_top_of_no_left_right` can be closed up directly.) -/
theorem exists_translate_path_of_leftRight_path_of_free_gap {p : ℝ} (hp : 0 < p)
    {K : Set (ℝ × ℝ)} (hper : ∀ q : ℝ × ℝ, q ∈ K ↔ (q.1 + p, q.2) ∈ K)
    {γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)} (hγ0 : (γ 0).1 = 0) (hγ1 : (γ 1).1 = p)
    (hK : ∀ t, γ t ∉ K)
    (hgap : ∀ t : ℝ, min (γ 0).2 (γ 1).2 ≤ t → t ≤ max (γ 0).2 (γ 1).2 → (p, t) ∉ K) :
    ∃ z : ℝ × ℝ, z ∉ K ∧ JoinedIn (Kᶜ) z (z.1 + p, z.2) := by
  refine ⟨γ 0, hK 0, ?_⟩
  have hA : JoinedIn (Kᶜ) (γ 0) (γ 1) := by
    refine ⟨{ toFun := γ, continuous_toFun := γ.continuous, source' := rfl, target' := rfl }, ?_⟩
    intro t; simpa using hK t
  have hB : JoinedIn (Kᶜ) (γ 1) ((p : ℝ), (γ 0).2) := by
    refine JoinedIn.ofLine (f := fun u : ℝ => ((p : ℝ), (1 - u) * (γ 1).2 + u * (γ 0).2))
      ?_ ?_ ?_ ?_
    · fun_prop
    · apply Prod.ext
      · show (p:ℝ) = (γ 1).1
        rw [hγ1]
      · show (1 - (0:ℝ)) * (γ 1).2 + 0 * (γ 0).2 = (γ 1).2
        ring
    · apply Prod.ext
      · rfl
      · show (1 - (1:ℝ)) * (γ 1).2 + 1 * (γ 0).2 = (γ 0).2
        ring
    · rintro y ⟨u, hu, rfl⟩
      have h1 : min (γ 0).2 (γ 1).2 ≤ (1 - u) * (γ 1).2 + u * (γ 0).2 := by
        nlinarith [min_le_left (γ 0).2 (γ 1).2, min_le_right (γ 0).2 (γ 1).2, hu.1, hu.2]
      have h2 : (1 - u) * (γ 1).2 + u * (γ 0).2 ≤ max (γ 0).2 (γ 1).2 := by
        nlinarith [le_max_left (γ 0).2 (γ 1).2, le_max_right (γ 0).2 (γ 1).2, hu.1, hu.2]
      simpa using hgap _ h1 h2
  have h := hA.trans hB
  simpa only [hγ0, zero_add] using h

/-- **Strictness of the interlocking point.**  The blocker height is different from both endpoint
heights: the endpoints are free (they are values of the free path `γ`), and `T`-invariance
identifies the heights on the meridians `0` and `p`. -/
theorem interlocking_point_strict {p : ℝ} {K : Set (ℝ × ℝ)}
    (hper : ∀ q : ℝ × ℝ, q ∈ K ↔ (q.1 + p, q.2) ∈ K)
    {γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)} (hγ0 : (γ 0).1 = 0) (hγ1 : (γ 1).1 = p)
    (hγK : ∀ t, γ t ∉ K)
    {c : ℝ} (hc1 : min (γ 0).2 (γ 1).2 ≤ c) (hc2 : c ≤ max (γ 0).2 (γ 1).2)
    (hcK : ((γ 1).1, c) ∈ K) :
    min (γ 0).2 (γ 1).2 < c ∧ c < max (γ 0).2 (γ 1).2 := by
  have hne0 : c ≠ (γ 0).2 := by
    intro hc
    have h1 : ((γ 1).1, c) = ((γ 0).1 + p, (γ 0).2) := by
      refine Prod.ext ?_ hc
      rw [hγ1, hγ0]; ring
    rw [h1] at hcK
    exact hγK 0 ((hper (γ 0)).mpr hcK)
  have hne1 : c ≠ (γ 1).2 := by
    intro hc
    rw [hc] at hcK
    exact hγK 1 hcK
  have hmin : min (γ 0).2 (γ 1).2 ≠ c := by
    intro h
    rcases le_total (γ 0).2 (γ 1).2 with hle | hle
    · rw [min_eq_left hle] at h; exact hne0 h.symm
    · rw [min_eq_right hle] at h; exact hne1 h.symm
  have hmax : c ≠ max (γ 0).2 (γ 1).2 := by
    intro h
    rcases le_total (γ 0).2 (γ 1).2 with hle | hle
    · rw [max_eq_right hle] at h; exact hne1 h
    · rw [max_eq_left hle] at h; exact hne0 h
  exact ⟨lt_of_le_of_ne hc1 hmin, lt_of_le_of_ne hc2 hmax⟩

/-- **The doorway at the blocker's level.**  A free path `γ` of the box whose endpoint heights
straddle a level `c` meets that level at a point `(x, c)` of the free region, and — by
`T`-invariance — the point `(x + p, c)` one period to the right is free as well.

This is the constraining fact every dodge argument has to respect: the blocker's level carries free
points one period apart, so the closing gap is obstructed only at the forbidden meridian where the
blocker itself sits.  Pure intermediate-value content; no hypothesis on `K` beyond freeness of `γ`
and `T`-invariance. -/
theorem exists_free_point_at_level_of_free_path {p : ℝ} {K : Set (ℝ × ℝ)}
    (hper : ∀ q : ℝ × ℝ, q ∈ K ↔ (q.1 + p, q.2) ∈ K)
    {γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)} (hγK : ∀ t, γ t ∉ K)
    {c : ℝ} (hc1 : min (γ 0).2 (γ 1).2 ≤ c) (hc2 : c ≤ max (γ 0).2 (γ 1).2) :
    ∃ x : ℝ, ((x, c) : ℝ × ℝ) ∉ K ∧ ((x + p, c) : ℝ × ℝ) ∉ K := by
  -- the image of the height function on the connected interval is preconnected, hence an interval
  have hpre : IsPreconnected ((fun t : Set.Icc (0:ℝ) 1 => (γ t).2) '' Set.univ) :=
    isPreconnected_univ.image _ (continuous_snd.comp γ.continuous).continuousOn
  have hord : OrdConnected ((fun t : Set.Icc (0:ℝ) 1 => (γ t).2) '' Set.univ) :=
    isPreconnected_iff_ordConnected.mp hpre
  have h0 : (γ 0).2 ∈ (fun t : Set.Icc (0:ℝ) 1 => (γ t).2) '' Set.univ := ⟨0, trivial, rfl⟩
  have h1 : (γ 1).2 ∈ (fun t : Set.Icc (0:ℝ) 1 => (γ t).2) '' Set.univ := ⟨1, trivial, rfl⟩
  have hmem : c ∈ (fun t : Set.Icc (0:ℝ) 1 => (γ t).2) '' Set.univ := by
    rcases le_total (γ 0).2 (γ 1).2 with hle | hle
    · rw [min_eq_left hle] at hc1
      rw [max_eq_right hle] at hc2
      exact hord.out h0 h1 ⟨hc1, hc2⟩
    · rw [min_eq_right hle] at hc1
      rw [max_eq_left hle] at hc2
      exact hord.out h1 h0 ⟨hc1, hc2⟩
  obtain ⟨t, -, ht⟩ := hmem
  refine ⟨(γ t).1, ?_, ?_⟩
  · rw [← ht]; exact hγK t
  · rw [← ht]; exact fun h => hγK t ((hper (γ t)).mpr h)

/-- The reflection of the strip in its midline: `(x,y) ↦ (x, a + b - y)`.  It is an involutive
homeomorphism, commutes with the translation `T`, and preserves the strip `{a ≤ y ≤ b}`. -/
noncomputable def flipStrip (a b : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun q := (q.1, a + b - q.2)
  invFun q := (q.1, a + b - q.2)
  left_inv := by intro q; refine Prod.ext rfl ?_; ring
  right_inv := by intro q; refine Prod.ext rfl ?_; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] lemma flipStrip_apply (a b : ℝ) (q : ℝ × ℝ) :
    flipStrip a b q = (q.1, a + b - q.2) := rfl

/-- **(A) First blocker on the blocker's level.**  To the right of a free point of the level `c` and
at or before a point of `K` on that level, there is a first point of `K`

```lean
  (x, c) ∉ K,  (p, c) ∈ K,  x < p  ⟹  ∃ x₁, x < x₁ ≤ p, (x₁, c) ∈ K,
                                      and no point of (x, x₁) × {c} lies in K.
```

Pure order-completeness on the closed level set (`sInf` of `K ∩ [x,p]` in the height coordinate). -/
theorem first_blocker_on_level {p c x : ℝ} {K : Set (ℝ × ℝ)} (hK : IsClosed K)
    (hxK : ((x, c) : ℝ × ℝ) ∉ K) (hpK : ((p, c) : ℝ × ℝ) ∈ K) (hxp : x < p) :
    ∃ x₁ : ℝ, x < x₁ ∧ x₁ ≤ p ∧ ((x₁, c) : ℝ × ℝ) ∈ K ∧
      ∀ x' : ℝ, x < x' → x' < x₁ → ((x', c) : ℝ × ℝ) ∉ K := by
  set E : Set ℝ := {t : ℝ | ((t, c) : ℝ × ℝ) ∈ K} with hE
  have hEcl : IsClosed E := hK.preimage (by fun_prop : Continuous fun t : ℝ => ((t, c) : ℝ × ℝ))
  set F : Set ℝ := E ∩ Set.Icc x p with hF
  have hFcl : IsClosed F := hEcl.inter isClosed_Icc
  have hFne : F.Nonempty := ⟨p, by rw [hF, hE]; exact ⟨hpK, ⟨hxp.le, le_rfl⟩⟩⟩
  have hFbdd : BddBelow F := ⟨x, fun t ht => ht.2.1⟩
  have hmemF : sInf F ∈ F := hFcl.csInf_mem hFne hFbdd
  have hle : x ≤ sInf F := le_csInf hFne (fun t ht => ht.2.1)
  have hnotmem : x ∉ F := by rw [hF, hE]; exact fun h => hxK h.1
  have hlt : x < sInf F := lt_of_le_of_ne hle (fun h => hnotmem (h ▸ hmemF))
  refine ⟨sInf F, hlt, ?_, ?_, ?_⟩
  · exact csInf_le hFbdd ⟨hpK, ⟨hxp.le, le_rfl⟩⟩
  · exact (hmemF.1 : ((sInf F, c) : ℝ × ℝ) ∈ K)
  · intro x' h1 h2 hmem
    have h2p : x' ≤ p := le_trans h2.le (csInf_le hFbdd ⟨hpK, ⟨hxp.le, le_rfl⟩⟩)
    have hmemF' : x' ∈ F := by rw [hF, hE]; exact ⟨hmem, ⟨h1.le, h2p⟩⟩
    exact absurd (csInf_le hFbdd hmemF') (not_le.mpr h2)

/-- **(B) The free prefix of the level is a free path.**  If every point of `(x, x₁) × {c}` is free
of `K`, then the whole segment from `(x, c)` to any such point lies in the strip and avoids `K`, so
the two are joined inside `S ∖ K`. -/
theorem free_prefix_on_level {a b c x x₁ x' : ℝ} {K : Set (ℝ × ℝ)}
    (hxa : a ≤ c) (hxc : c ≤ b)
    (hfree : ∀ t : ℝ, x < t → t < x₁ → ((t, c) : ℝ × ℝ) ∉ K)
    (hxK : ((x, c) : ℝ × ℝ) ∉ K) (h1 : x < x') (h2 : x' < x₁) :
    JoinedIn (({q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b}) \ K) ((x, c) : ℝ × ℝ) ((x', c) : ℝ × ℝ) := by
  refine JoinedIn.of_segment_subset ?_
  rintro w hw
  rw [segment_eq_image] at hw
  obtain ⟨t, ht, rfl⟩ := hw
  have hcoord : ((1 - t) • ((x, c) : ℝ × ℝ) + t • ((x', c) : ℝ × ℝ))
      = (((1 - t) * x + t * x'), c) := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] <;> ring
  simp only []
  rw [hcoord]
  refine ⟨⟨hxa, hxc⟩, fun hk => ?_⟩
  by_cases ht0 : t = 0
  · subst ht0
    have hthis : (1 - (0:ℝ)) * x + 0 * x' = x := by ring
    exact hxK (by rwa [hthis] at hk)
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    exact hfree _ (by nlinarith [htpos, ht.2, h1]) (by nlinarith [ht.1, ht.2, h2]) hk

/-- **The mirror band lemma.**  A closed set inside the box `[x₀,x₁] × [a,b]` which misses the
*bottom* line is bounded away from it: there is `δ > 0` with `D ⊆ {q | a + δ ≤ q.2}`.  (Same
compactness argument as `exists_band_below_top_line`, with the minimum of the height instead of the
maximum.) -/
theorem exists_band_above_bottom_line {a b x₀ x₁ : ℝ} {D : Set (ℝ × ℝ)}
    (hD : IsClosed D) (hDbox : D ⊆ {q : ℝ × ℝ | x₀ ≤ q.1 ∧ q.1 ≤ x₁ ∧ a ≤ q.2 ∧ q.2 ≤ b})
    (hDbot : ∀ q ∈ D, q.2 ≠ a) :
    ∃ δ > 0, D ⊆ {q : ℝ × ℝ | a + δ ≤ q.2} := by
  rcases D.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · have hbox : D ⊆ Set.Icc x₀ x₁ ×ˢ Set.Icc a b := by
      intro q hq
      obtain ⟨h1, h2, h3, h4⟩ := hDbox hq
      exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    have hcomp : IsCompact D := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hD hbox
    obtain ⟨q₀, hq₀, hmin⟩ := hcomp.exists_isMinOn hne continuous_snd.continuousOn
    have hlt : a < q₀.2 := lt_of_le_of_ne (hDbox hq₀).2.2.1 (Ne.symm (hDbot q₀ hq₀))
    exact ⟨q₀.2 - a, by linarith, fun q hq => by
      have := hmin hq
      simp only [Set.mem_setOf_eq] at this ⊢
      linarith⟩

/-- **Components of closed sets are closed.**  If `F` is closed in any topological space, then the
component of a point of `F` is closed.  Proof: the closure of the component is preconnected
(`IsPreconnected.closure`) and is contained in `F` (`closure_minimal`), so by maximality of the
component it is contained in the component itself. -/
theorem isClosed_connectedComponentIn_of_isClosed {α : Type*} [TopologicalSpace α]
    {F : Set α} (hF : IsClosed F) {q : α} (hq : q ∈ F) :
    IsClosed (connectedComponentIn F q) := by
  rw [← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm ?_ subset_closure
  exact IsPreconnected.subset_connectedComponentIn (isPreconnected_connectedComponentIn.closure)
    (subset_closure (mem_connectedComponentIn hq))
    (closure_minimal (connectedComponentIn_subset F q) hF)

/-- **The interior-wall asymmetry.**  A preconnected piece of `K` inside the box which meets the
**top** line is bounded away from the **bottom** line (inside the box), provided `K` has no wall (no
preconnected piece meeting both lines).

Proof: `closure C` is closed, preconnected, still lies in `K` (which is closed) and still meets the
top line; a meeting with `{y = a}` would then be a wall, contradicting `hnowall`.  So the mirror band
lemma applies to `closure C ∩ {x₀ ≤ ·.1 ≤ x₁}`. -/
theorem component_touching_top_bounded_away_from_bottom {a b x₀ x₁ : ℝ} {K : Set (ℝ × ℝ)}
    (hK : IsClosed K) (hKbox : K ⊆ {q : ℝ × ℝ | x₀ ≤ q.1 ∧ q.1 ≤ x₁ ∧ a ≤ q.2 ∧ q.2 ≤ b})
    (hnowall : ∀ C : Set (ℝ × ℝ), C ⊆ K → IsPreconnected C →
      (C ∩ {q : ℝ × ℝ | q.2 = a}).Nonempty → (C ∩ {q : ℝ × ℝ | q.2 = b}).Nonempty → False)
    {C : Set (ℝ × ℝ)} (hCK : C ⊆ K) (hCpc : IsPreconnected C)
    (hCtop : (C ∩ {q : ℝ × ℝ | q.2 = b}).Nonempty) :
    ∃ δ > 0, C ∩ {q : ℝ × ℝ | x₀ ≤ q.1 ∧ q.1 ≤ x₁} ⊆ {q : ℝ × ℝ | a + δ ≤ q.2} := by
  have hclsub : closure C ⊆ K := closure_minimal hCK hK
  have hclpc : IsPreconnected (closure C) := hCpc.closure
  have hcltop : (closure C ∩ {q : ℝ × ℝ | q.2 = b}).Nonempty := by
    obtain ⟨q, hqC, hqb⟩ := hCtop
    exact ⟨q, subset_closure hqC, hqb⟩
  have hclbot : ∀ q ∈ closure C, q.2 ≠ a := by
    intro q hq hqa
    exact hnowall (closure C) hclsub hclpc ⟨q, hq, hqa⟩ hcltop
  set D : Set (ℝ × ℝ) := closure C ∩ {q : ℝ × ℝ | x₀ ≤ q.1 ∧ q.1 ≤ x₁} with hD
  have hDcl : IsClosed D :=
    isClosed_closure.inter ((isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_fst continuous_const))
  have hDbox : D ⊆ {q : ℝ × ℝ | x₀ ≤ q.1 ∧ q.1 ≤ x₁ ∧ a ≤ q.2 ∧ q.2 ≤ b} := by
    intro q hq
    exact ⟨hq.2.1, hq.2.2, (hKbox (hclsub hq.1)).2.2.1, (hKbox (hclsub hq.1)).2.2.2⟩
  have hDbot : ∀ q ∈ D, q.2 ≠ a := fun q hq => hclbot q hq.1
  obtain ⟨δ, hδ, hsub⟩ := exists_band_above_bottom_line hDcl hDbox hDbot
  exact ⟨δ, hδ, fun q hq => hsub ⟨subset_closure hq.1, hq.2⟩⟩

/-- **(a) Band crossing.**  Inside the band `{b - ε ≤ q.2 ≤ b}` of the fundamental box, if the
obstacle has no preconnected piece joining the two horizontal edges of the band, then the band
contains a **free left–right path** (from `{x = 0}` to `{x = p}`).

This is the commons' crossing duality (`barrier_bottom_top_of_no_left_right`) instantiated in the
band, and it is the mechanism by which a path is pushed into — and travels inside — the band above
the blocker's component. -/
theorem exists_free_band_crossing_of_no_band_wall {p b ε : ℝ} (hp : 0 < p) (hε : 0 < ε)
    {K : Set (ℝ × ℝ)} (hK : IsClosed K)
    (hKbox : K ⊆ {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ p ∧ b - ε ≤ q.2 ∧ q.2 ≤ b})
    (hnowall : ∀ C : Set (ℝ × ℝ), C ⊆ K → IsPreconnected C →
      (C ∩ {q : ℝ × ℝ | q.2 = b - ε}).Nonempty →
      (C ∩ {q : ℝ × ℝ | q.2 = b}).Nonempty → False) :
    ∃ γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ),
      (γ 0).1 = 0 ∧ (γ 1).1 = p ∧
        (∀ t, 0 ≤ (γ t).1 ∧ (γ t).1 ≤ p ∧ b - ε ≤ (γ t).2 ∧ (γ t).2 ≤ b) ∧
        ∀ t, γ t ∉ K := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨C, hCK, hCpc, hCb, hCt⟩ :=
    Commons.Topology.Strip.barrier_bottom_top_of_no_left_right (p := p) (a := b - ε) (b := b)
      hp (by linarith) hKbox hK
      (fun γ hγbox hγ0 hγ1 hγK => (hcon γ hγ0 hγ1 hγbox).elim fun t ht => hγK t ht)
  exact hnowall C hCK hCpc hCb hCt

/-- **The band lemma.**  A closed set `D` inside the box `[x₀,x₁] × [a,b]` which misses the top line
is bounded away from it: there is `ε > 0` with `D ⊆ {q | q.2 ≤ b - ε}`.

Consequently the horizontal band `{b - ε < q.2 ≤ b}` is disjoint from `D`.  (Compactness: `D` is a
closed subset of the compact box, the height attains its maximum `q₀.2` on `D`, and `q₀.2 < b`
because `D` misses the top line.) -/
theorem exists_band_below_top_line {a b x₀ x₁ : ℝ} {D : Set (ℝ × ℝ)}
    (hD : IsClosed D) (hDbox : D ⊆ {q : ℝ × ℝ | x₀ ≤ q.1 ∧ q.1 ≤ x₁ ∧ a ≤ q.2 ∧ q.2 ≤ b})
    (hDtop : ∀ q ∈ D, q.2 ≠ b) :
    ∃ ε > 0, D ⊆ {q : ℝ × ℝ | q.2 ≤ b - ε} := by
  rcases D.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · have hbox : D ⊆ Set.Icc x₀ x₁ ×ˢ Set.Icc a b := by
      intro q hq
      obtain ⟨h1, h2, h3, h4⟩ := hDbox hq
      exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    have hcomp : IsCompact D := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hD hbox
    obtain ⟨q₀, hq₀, hmax⟩ := hcomp.exists_isMaxOn hne continuous_snd.continuousOn
    have hlt : q₀.2 < b := lt_of_le_of_ne (hDbox hq₀).2.2.2 (hDtop q₀ hq₀)
    exact ⟨b - q₀.2, by linarith, fun q hq => by
      have := hmax hq
      simp only [Set.mem_setOf_eq] at this ⊢
      linarith⟩

/-- **A closed set missing both boundary lines is strictly interior.**  Combining the two band
lemmas: a closed set inside the box whose every point has height different from `a` and from `b` is
contained in a strictly smaller box `{a + δ ≤ ·.2 ≤ b - ε}`. -/
theorem closed_subset_bounded_away_of_misses_lines {a b x₀ x₁ : ℝ} {D : Set (ℝ × ℝ)}
    (hD : IsClosed D) (hDbox : D ⊆ {q : ℝ × ℝ | x₀ ≤ q.1 ∧ q.1 ≤ x₁ ∧ a ≤ q.2 ∧ q.2 ≤ b})
    (hDtop : ∀ q ∈ D, q.2 ≠ b) (hDbot : ∀ q ∈ D, q.2 ≠ a) :
    ∃ δ ε : ℝ, 0 < δ ∧ 0 < ε ∧ D ⊆ {q : ℝ × ℝ | a + δ ≤ q.2 ∧ q.2 ≤ b - ε} := by
  obtain ⟨ε, hε, hε'⟩ := exists_band_below_top_line hD hDbox hDtop
  obtain ⟨δ, hδ, hδ'⟩ := exists_band_above_bottom_line hD hDbox hDbot
  exact ⟨δ, ε, hδ, hε, fun q hq => ⟨hδ' hq, hε' hq⟩⟩

/-- **The trichotomy's first sub-case for the blocker.**  Let `q ∈ K` with `K` closed inside the box,
and suppose the component of `q` never meets the top line.  Then, on the box, either

* the component is **strictly interior** — `∃ δ ε > 0`, `connectedComponentIn K q ∩ {x₀ ≤ ·.1 ≤ x₁}
  ⊆ {a + δ ≤ ·.2 ≤ b - ε}` — or
* it **meets the bottom line** `{y = a}`.

This is the dichotomy the trichotomy hands the `dodge_of_component_misses_top_line` proof: the first
branch is where the geometry is under control (room above and below the component), the second is the
remaining sub-case to hand out. -/
theorem blocker_interior_or_touches_bottom {x₀ x₁ a b : ℝ} {K : Set (ℝ × ℝ)} (hK : IsClosed K)
    (hKbox : K ⊆ {q : ℝ × ℝ | x₀ ≤ q.1 ∧ q.1 ≤ x₁ ∧ a ≤ q.2 ∧ q.2 ≤ b})
    {q : ℝ × ℝ} (hq : q ∈ K) (hqtop : ∀ z ∈ connectedComponentIn K q, z.2 ≠ b) :
    (∃ δ ε : ℝ, 0 < δ ∧ 0 < ε ∧
        connectedComponentIn K q ∩ {z : ℝ × ℝ | x₀ ≤ z.1 ∧ z.1 ≤ x₁} ⊆
          {z : ℝ × ℝ | a + δ ≤ z.2 ∧ z.2 ≤ b - ε}) ∨
      ((connectedComponentIn K q ∩ {z : ℝ × ℝ | x₀ ≤ z.1 ∧ z.1 ≤ x₁} ∩
        {z : ℝ × ℝ | z.2 = a}).Nonempty) := by
  by_cases h : (connectedComponentIn K q ∩ {z : ℝ × ℝ | x₀ ≤ z.1 ∧ z.1 ≤ x₁} ∩
      {z : ℝ × ℝ | z.2 = a}).Nonempty
  · exact Or.inr h
  · refine Or.inl ?_
    have hDcl : IsClosed (connectedComponentIn K q ∩ {z : ℝ × ℝ | x₀ ≤ z.1 ∧ z.1 ≤ x₁}) :=
      (isClosed_connectedComponentIn_of_isClosed hK hq).inter
        ((isClosed_le continuous_const continuous_fst).inter
          (isClosed_le continuous_fst continuous_const))
    have hDbox : connectedComponentIn K q ∩ {z : ℝ × ℝ | x₀ ≤ z.1 ∧ z.1 ≤ x₁} ⊆
        {z : ℝ × ℝ | x₀ ≤ z.1 ∧ z.1 ≤ x₁ ∧ a ≤ z.2 ∧ z.2 ≤ b} := by
      intro z hz
      have hzK := connectedComponentIn_subset K q hz.1
      exact ⟨hz.2.1, hz.2.2, (hKbox hzK).2.2.1, (hKbox hzK).2.2.2⟩
    have hDtop : ∀ z ∈ connectedComponentIn K q ∩ {z : ℝ × ℝ | x₀ ≤ z.1 ∧ z.1 ≤ x₁}, z.2 ≠ b :=
      fun z hz => hqtop z hz.1
    have hDbot : ∀ z ∈ connectedComponentIn K q ∩ {z : ℝ × ℝ | x₀ ≤ z.1 ∧ z.1 ≤ x₁}, z.2 ≠ a :=
      fun z hz hza => h ⟨z, hz, hza⟩
    exact closed_subset_bounded_away_of_misses_lines hDcl hDbox hDtop hDbot

/-- **The contact set of a component meeting the bottom line.**  Let `D` be closed inside the box and
let it meet `{y = a}`.  Then the contact set `L := D ∩ {y = a}` is **compact** (in particular
nonempty and closed) and has **extremal contact points**: there are `qmin, qmax ∈ L` whose
`x`-coordinates bound the `x`-coordinates of every point of `L`.

This is the object the meets-the-bottom branch of `dodge_of_component_misses_top_line` needs before it
can say anything about a free path avoiding `D`: the contact interval `[qmin.1, qmax.1]` of `D` on the
bottom line.  (The projection need not be an interval — `D` may touch the bottom line in several
separated pieces — so only extremality is claimed.) -/
theorem contact_set_compact_and_extremal {a b x₀ x₁ : ℝ} {D : Set (ℝ × ℝ)}
    (hD : IsClosed D) (hDbox : D ⊆ {q : ℝ × ℝ | x₀ ≤ q.1 ∧ q.1 ≤ x₁ ∧ a ≤ q.2 ∧ q.2 ≤ b})
    (hne : (D ∩ {q : ℝ × ℝ | q.2 = a}).Nonempty) :
    IsCompact (D ∩ {q : ℝ × ℝ | q.2 = a}) ∧
      ∃ qmin ∈ D ∩ {q : ℝ × ℝ | q.2 = a}, ∃ qmax ∈ D ∩ {q : ℝ × ℝ | q.2 = a},
        ∀ q ∈ D ∩ {q : ℝ × ℝ | q.2 = a}, qmin.1 ≤ q.1 ∧ q.1 ≤ qmax.1 := by
  set L : Set (ℝ × ℝ) := D ∩ {q : ℝ × ℝ | q.2 = a} with hL
  have hLcl : IsClosed L := hD.inter (isClosed_eq continuous_snd continuous_const)
  have hLbox : L ⊆ Set.Icc x₀ x₁ ×ˢ Set.Icc a b := by
    intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := hDbox hq.1
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  have hLcpt : IsCompact L := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hLcl hLbox
  obtain ⟨qmin, hqmin, hmin⟩ := hLcpt.exists_isMinOn hne continuous_fst.continuousOn
  obtain ⟨qmax, hqmax, hmax⟩ := hLcpt.exists_isMaxOn hne continuous_fst.continuousOn
  exact ⟨hLcpt, qmin, hqmin, qmax, hqmax, fun q hq => ⟨hmin hq, hmax hq⟩⟩

/-- **The extremal contact points lie in the box.**  Corollary of
`contact_set_compact_and_extremal` pushed through the box bound: the extremal contact points on the
bottom line have both coordinates inside the box, so the contact interval `[qmin.1, qmax.1]` is a
subinterval of `[x₀, x₁]`. -/
theorem contact_x_coords_mem_Icc {a b x₀ x₁ : ℝ} {D : Set (ℝ × ℝ)}
    (hD : IsClosed D) (hDbox : D ⊆ {q : ℝ × ℝ | x₀ ≤ q.1 ∧ q.1 ≤ x₁ ∧ a ≤ q.2 ∧ q.2 ≤ b})
    (hne : (D ∩ {q : ℝ × ℝ | q.2 = a}).Nonempty) :
    ∃ qmin ∈ D ∩ {q : ℝ × ℝ | q.2 = a}, ∃ qmax ∈ D ∩ {q : ℝ × ℝ | q.2 = a},
      x₀ ≤ qmin.1 ∧ qmin.1 ≤ x₁ ∧ x₀ ≤ qmax.1 ∧ qmax.1 ≤ x₁ ∧
        ∀ q ∈ D ∩ {q : ℝ × ℝ | q.2 = a}, qmin.1 ≤ q.1 ∧ q.1 ≤ qmax.1 := by
  obtain ⟨-, qmin, hqmin, qmax, hqmax, hb⟩ := contact_set_compact_and_extremal hD hDbox hne
  exact ⟨qmin, hqmin, qmax, hqmax, (hDbox hqmin.1).1, (hDbox hqmin.1).2.1,
    (hDbox hqmax.1).1, (hDbox hqmax.1).2.1, hb⟩

/-- **Rung 1 of the climb: the first reach of the blocker's level.**

A free path whose endpoint heights straddle `c` (here `(γ 0).2 < c < (γ 1).2`) has a **first** parameter
`t₀` at which its height reaches `c`: before `t₀` the path stays strictly below `c`, and at `t₀` the
height is at least `c`.  The point `γ t₀` is free (it lies on `γ`), so it is a doorway at the
blocker's level *reached from below along `γ`* — the geometric input the climb consumes.

(Stated with `c ≤ (γ t₀).2`; upgrading to the equality `(γ t₀).2 = c` is a short continuity argument
and is not needed for the first use.) -/
theorem exists_first_reach_of_level {c : ℝ} {γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)}
    (h0 : (γ 0).2 < c) (h1 : c < (γ 1).2) :
    ∃ t₀ : Set.Icc (0:ℝ) 1, c ≤ (γ t₀).2 ∧
      ∀ t : Set.Icc (0:ℝ) 1, t < t₀ → (γ t).2 < c := by
  set E : Set (Set.Icc (0:ℝ) 1) := {t | c ≤ (γ t).2} with hE
  have hcl : IsClosed E := isClosed_le continuous_const (continuous_snd.comp γ.continuous)
  have hne : E.Nonempty := ⟨1, h1.le⟩
  have hbdd : BddBelow E := ⟨0, fun t _ => t.2.1⟩
  refine ⟨sInf E, hcl.csInf_mem hne hbdd, ?_⟩
  intro t ht
  by_contra hcon
  push_neg at hcon
  exact absurd (csInf_le hbdd (show t ∈ E from hcon)) (not_le.mpr ht)

/-- **Rung 2: from the doorway to the first blocker, as a free path.**

Given a free point `(x, c)` of the strip at the blocker's level, a point `(p, c) ∈ K` on that level to
its right, (A) produces the first blocker `x₁ ∈ (x, p]` and (B) turns the doorway into a free path
inside `S∖K` at level `c`, running from `(x, c)` to any point `(x', c)` with `x < x' < x₁`.

This is the branch packaging of rung 2 for the case `x < p`: the doorway at the blocker's level
(produced by `exists_free_point_at_level_of_free_path`) now comes with the whole free level segment
pushing into the blocker from the left. -/
theorem free_path_to_first_blocker {p a b c x : ℝ} {K : Set (ℝ × ℝ)} (hK : IsClosed K)
    (hsub : K ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hxa : a ≤ c) (hxc : c ≤ b)
    (hxK : ((x, c) : ℝ × ℝ) ∉ K) (hpK : ((p, c) : ℝ × ℝ) ∈ K) (hxp : x < p) :
    ∃ x₁ : ℝ, x < x₁ ∧ x₁ ≤ p ∧ ((x₁, c) : ℝ × ℝ) ∈ K ∧
      ∀ x' : ℝ, x < x' → x' < x₁ →
        JoinedIn (({q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b}) \ K) ((x, c) : ℝ × ℝ) ((x', c) : ℝ × ℝ) := by
  obtain ⟨x₁, hx1, hx1p, hx1K, hnf⟩ := first_blocker_on_level hK hxK hpK hxp
  exact ⟨x₁, hx1, hx1p, hx1K, fun x' h1 h2 =>
    free_prefix_on_level hxa hxc (fun t ht1 ht2 => hnf t ht1 ht2) hxK h1 h2⟩

/-- **(D), first case: the climb along a free meridian.**

If a free point `z` of the strip has its whole meridian above it free of `K`, then `z` is joined
inside `S ∖ K` to the point of the top line above it.  This is the first case of the climb past the
blocking component `D` (`D ∩ {y = b} = ∅`); the general case replaces meridian-freeness by the
component-level hypothesis, and is the remaining content.

The vertical segment is used directly: its points have the same first coordinate as `z` and heights
between `z.2` and `b`, so freeness is exactly `hfree`. -/
theorem climb_of_free_meridian {a b : ℝ} {K : Set (ℝ × ℝ)}
    (hsub : K ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    {z : ℝ × ℝ} (hz : z ∈ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} \ K)
    (hfree : ∀ t : ℝ, z.2 ≤ t → t ≤ b → ((z.1, t) : ℝ × ℝ) ∉ K) :
    JoinedIn ({q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} \ K) z ((z.1, b) : ℝ × ℝ) := by
  have hza : a ≤ z.2 := hz.1.1
  have hzb : z.2 ≤ b := hz.1.2
  refine JoinedIn.of_segment_subset ?_
  rintro w hw
  rw [segment_eq_image] at hw
  obtain ⟨t, ht, rfl⟩ := hw
  have hcoord : ((1 - t) • z + t • ((z.1, b) : ℝ × ℝ))
      = ((z.1, (1 - t) * z.2 + t * b)) := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
      Prod.snd_add] <;> ring
  simp only []
  rw [hcoord]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [Prod.snd]; nlinarith [ht.1, ht.2, hza, hzb]
  · simp only [Prod.snd]; nlinarith [ht.1, ht.2, hza, hzb]
  · refine hfree _ ?_ ?_ <;> nlinarith [ht.1, ht.2, hza, hzb]


/-! ## Base layer of the degree theory for the annulus

A *translate path* in `U` is a path from a point to its own translate.  The lemmas below implement the
base layer of Denne's degree argument: a path in a `T`-invariant set `U` whose endpoints differ by a
**nonzero** multiple of the period already yields a translate path inside `U` (so a loop of nonzero
winding in `U/T` contains a translate path in `U`).  The proof runs a staircase of the path against
`Commons.Topology.Strip.path_meets_translate`.
-/

/-- **The `m`-fold staircase.**  A path `γ` in the plane whose endpoint is the translate of its start
point by `(m : ℝ) * p` extends to a continuous `G : ℝ → ℝ × ℝ` with `G (t + 1) = G t + (m*p, 0)`,
`G 0 = γ 0`, and whose image consists of points of the `T^m`-saturation of `γ '' I`. -/
theorem exists_staircase_shift {p : ℝ} (hp : 0 < p) {m : ℕ} (hm : 0 < m)
    (γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ))
    (hγ : γ 1 = ((γ 0).1 + (m : ℝ) * p, (γ 0).2)) :
    ∃ G : C(ℝ, ℝ × ℝ), G 0 = γ 0 ∧
      (∀ t, G (t + 1) = ((G t).1 + (m : ℝ) * p, (G t).2)) ∧
      ∀ t, ∃ s : Set.Icc (0 : ℝ) 1, ∃ n : ℤ,
        G t = ((γ s).1 + (m : ℝ) * p * (n : ℝ), (γ s).2) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  set Φ : ℝ → ℝ := fun u => (γ (Set.projIcc 0 1 h01 u)).1 - ((m : ℝ) * p) * u with hΦ
  set Ψ : ℝ → ℝ := fun u => (γ (Set.projIcc 0 1 h01 u)).2 with hΨ
  have hΦc : ContinuousOn Φ (Set.Icc (0 : ℝ) 1) := by rw [hΦ]; fun_prop
  have hΨc : ContinuousOn Ψ (Set.Icc (0 : ℝ) 1) := by rw [hΨ]; fun_prop
  have hpr0 : Set.projIcc 0 1 h01 (0 : ℝ) = (0 : Set.Icc (0 : ℝ) 1) := by
    apply Subtype.ext; rw [Set.projIcc_left h01]; rfl
  have hpr1 : Set.projIcc 0 1 h01 (1 : ℝ) = (1 : Set.Icc (0 : ℝ) 1) := by
    apply Subtype.ext; rw [Set.projIcc_right h01]; rfl
  have hΦ0 : Φ 0 = (γ 0).1 := by
    rw [hΦ]
    show (γ (Set.projIcc 0 1 h01 (0 : ℝ))).1 - ((m : ℝ) * p) * 0 = (γ 0).1
    rw [hpr0]; ring
  have hΦ1 : Φ 1 = (γ 0).1 := by
    rw [hΦ]
    show (γ (Set.projIcc 0 1 h01 (1 : ℝ))).1 - ((m : ℝ) * p) * 1 = (γ 0).1
    rw [hpr1, hγ]; ring
  have hΨ0 : Ψ 0 = (γ 0).2 := by
    rw [hΨ]
    show (γ (Set.projIcc 0 1 h01 (0 : ℝ))).2 = (γ 0).2
    rw [hpr0]
  have hΨ1 : Ψ 1 = (γ 0).2 := by
    rw [hΨ]
    show (γ (Set.projIcc 0 1 h01 (1 : ℝ))).2 = (γ 0).2
    rw [hpr1, hγ]
  have hΦf : Continuous (Φ ∘ Int.fract) := ContinuousOn.comp_fract'' hΦc (by rw [hΦ0, hΦ1])
  have hΨf : Continuous (Ψ ∘ Int.fract) := ContinuousOn.comp_fract'' hΨc (by rw [hΨ0, hΨ1])
  have h1 : Continuous fun t : ℝ => ((m : ℝ) * p) * t + (Φ ∘ Int.fract) t :=
    (continuous_const.mul continuous_id).add hΦf
  have hcont : Continuous fun t : ℝ =>
      (((m : ℝ) * p) * t + (Φ ∘ Int.fract) t, (Ψ ∘ Int.fract) t) := h1.prodMk hΨf
  refine ⟨⟨_, hcont⟩, ?_, ?_, ?_⟩
  · show (((m : ℝ) * p) * 0 + (Φ ∘ Int.fract) 0, (Ψ ∘ Int.fract) 0) = γ 0
    simp only [mul_zero, zero_add, Int.fract_zero, Function.comp_apply, hΦ0, hΨ0]
  · intro t
    show (((m : ℝ) * p) * (t + 1) + (Φ ∘ Int.fract) (t + 1), (Ψ ∘ Int.fract) (t + 1))
        = (((m : ℝ) * p) * t + (Φ ∘ Int.fract) t + (m : ℝ) * p, (Ψ ∘ Int.fract) t)
    simp only [Function.comp_apply, Int.fract_add_one]
    exact Prod.ext (by ring) rfl
  · intro t
    refine ⟨Set.projIcc 0 1 h01 (Int.fract t), ⌊t⌋, ?_⟩
    show (((m : ℝ) * p) * t + (Φ ∘ Int.fract) t, (Ψ ∘ Int.fract) t)
        = ((γ (Set.projIcc 0 1 h01 (Int.fract t))).1 + (m : ℝ) * p * (⌊t⌋ : ℝ),
           (γ (Set.projIcc 0 1 h01 (Int.fract t))).2)
    simp only [Function.comp_apply, hΦ, hΨ]
    have hf : Int.fract t = t - (⌊t⌋ : ℝ) := (Int.self_sub_floor t).symm
    rw [hf]
    exact Prod.ext (by ring) rfl

/-- **Nonzero winding yields a translate path** (natural-number form). -/
theorem exists_translate_path_of_winding_nat {p : ℝ} (hp : 0 < p)
    {U : Set (ℝ × ℝ)} (hUinv : ∀ q : ℝ × ℝ, q ∈ U ↔ (q.1 + p, q.2) ∈ U)
    {γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ)} (hγU : ∀ t, γ t ∈ U) {m : ℕ} (hm : 0 < m)
    (hγ : γ 1 = ((γ 0).1 + (m : ℝ) * p, (γ 0).2)) :
    ∃ z : ℝ × ℝ, z ∈ U ∧ JoinedIn U z (z.1 + p, z.2) := by
  rcases eq_or_lt_of_le (show 1 ≤ m by omega) with hm1 | hm2
  · -- m = 1: the path itself
    subst hm1
    have hγ' : γ 1 = ((γ 0).1 + p, (γ 0).2) := by simpa using hγ
    exact ⟨γ 0, hγU 0,
      ⟨{ toContinuousMap := γ, source' := rfl, target' := hγ' }, fun t => hγU t⟩⟩
  · -- m ≥ 2: staircase + `path_meets_translate`
    obtain ⟨G, -, hGper, hGform⟩ := exists_staircase_shift hp hm γ hγ
    have hGU : ∀ t : ℝ, G t ∈ U := by
      intro t
      obtain ⟨s, n, hs⟩ := hGform t
      rw [hs]
      have hmem : ((γ s).1 + ((n * (m : ℤ) : ℤ) : ℝ) * p, (γ s).2) ∈ U :=
        (Commons.Topology.Strip.periodic_shift hUinv (n * (m : ℤ)) (γ s)).mpr (hγU s)
      convert hmem using 2
      push_cast; ring
    obtain ⟨s, t, hst⟩ :=
      Commons.Topology.Strip.path_meets_translate hp hm2 G.continuous (fun u => hGper u)
    rcases lt_or_ge t s with hlt | hle
    · refine ⟨G t, hGU t, ?_⟩
      refine JoinedIn.ofLine (f := fun u : ℝ => G (t + u * (s - t))) ?_ ?_ ?_ ?_
      · fun_prop
      · show G (t + 0 * (s - t)) = G t; ring_nf
      · show G (t + 1 * (s - t)) = ((G t).1 + p, (G t).2)
        have : t + 1 * (s - t) = s := by ring
        rw [this, hst]
      · rintro z ⟨u, _, rfl⟩
        exact hGU _
    · refine ⟨G t, hGU t, ?_⟩
      refine JoinedIn.ofLine (f := fun u : ℝ => G (t - u * (t - s))) ?_ ?_ ?_ ?_
      · fun_prop
      · show G (t - 0 * (t - s)) = G t; ring_nf
      · show G (t - 1 * (t - s)) = ((G t).1 + p, (G t).2)
        have : t - 1 * (t - s) = s := by ring
        rw [this, hst]
      · rintro z ⟨u, _, rfl⟩
        exact hGU _

/-- **Nonzero winding yields a translate path** (integer form, the statement used by the degree
argument for the annulus). -/
theorem exists_translate_path_of_loop_winding {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {U : Set (ℝ × ℝ)} (hUsub : U ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hUinv : ∀ q : ℝ × ℝ, q ∈ U ↔ (q.1 + p, q.2) ∈ U)
    {γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ)} (hγU : ∀ t, γ t ∈ U) {d : ℤ} (hd : d ≠ 0)
    (hγ : γ 1 = ((γ 0).1 + (d : ℝ) * p, (γ 0).2)) :
    ∃ z : ℝ × ℝ, z ∈ U ∧ JoinedIn U z (z.1 + p, z.2) := by
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · -- negative winding: reverse the path, then apply the natural-number form to `-d`
    have hρc : Continuous fun u : Set.Icc (0 : ℝ) 1 =>
        (⟨1 - (u : ℝ), by
          have hu := u.2
          simp only [Set.mem_Icc] at hu
          exact ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩⟩ : Set.Icc (0 : ℝ) 1) :=
      Continuous.subtype_mk (by fun_prop) _
    set γ' : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ) := γ.comp ⟨_, hρc⟩ with hγ'def
    have h0 : γ' 0 = γ 1 := by
      change γ (⟨1 - ((0 : Set.Icc (0 : ℝ) 1) : ℝ), _⟩ : Set.Icc (0 : ℝ) 1) = γ 1
      congr 1
      apply Subtype.ext
      simp
    have h1 : γ' 1 = γ 0 := by
      change γ (⟨1 - ((1 : Set.Icc (0 : ℝ) 1) : ℝ), _⟩ : Set.Icc (0 : ℝ) 1) = γ 0
      congr 1
      apply Subtype.ext
      simp
    have hU' : ∀ t, γ' t ∈ U := fun t => hγU _
    have hcastZ : (((-d).toNat : ℕ) : ℤ) = -d := Int.toNat_of_nonneg (by omega)
    have hcast : (((-d).toNat : ℕ) : ℝ) = ((-d : ℤ) : ℝ) := by exact_mod_cast hcastZ
    have hpos' : 0 < (-d).toNat := Nat.pos_of_ne_zero (by
      rintro h
      rw [h] at hcast
      norm_num at hcast
      omega)
    have hγ'' : γ' 1 = ((γ' 0).1 + (((-d).toNat : ℕ) : ℝ) * p, (γ' 0).2) := by
      rw [h1, h0, hcast]
      refine Prod.ext ?_ ?_
      · have h2 : (γ 1).1 = (γ 0).1 + (d : ℝ) * p := by
          have := congrArg Prod.fst hγ; simpa using this
        push_cast
        linarith
      · have h3 : (γ 1).2 = (γ 0).2 := by
          have := congrArg Prod.snd hγ; simpa using this
        simp only [Prod.snd]
        exact h3.symm
    exact exists_translate_path_of_winding_nat hp hUinv hU' hpos' hγ''
  · have hcastZ : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg (le_of_lt hpos)
    have hcast : ((d.toNat : ℕ) : ℝ) = ((d : ℤ) : ℝ) := by exact_mod_cast hcastZ
    have hpos' : 0 < d.toNat := Nat.pos_of_ne_zero (by
      rintro h
      rw [h] at hcast
      norm_num at hcast
      omega)
    exact exists_translate_path_of_winding_nat hp hUinv hγU hpos'
      (by rw [hcast]; exact hγ)

/-- **The `U`-crossing at a label change.**  If two horizontally adjacent grid cells (`i` and `i'`
with `i.1 + 1 = i'.1`, so that the shared edge is the line `u = u i'.castSucc`) carry different
labels, then the `F`-image of their shared edge lies entirely in `U = W₁ ∩ W₂`: the shared edge is
contained in *both* closed cells, so its image lies in both `W₁` and `W₂`.  This is the interior-edge
bookkeeping: a label change forces a genuine crossing of `U`. -/
theorem grid_vertical_edge_mem_inter {p a b : ℝ} (hp : 0 < p)
    {W₁ W₂ : Set (ℝ × ℝ)}
    (hsub₁ : W₁ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hsub₂ : W₂ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₁ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₁ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₂ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₂ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hcov : W₁ ∪ W₂ = {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    {γ₁ γ₂ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ)} (h₁ : ∀ t, γ₁ t ∈ W₁) (h₂ : ∀ t, γ₂ t ∈ W₂)
    {n : ℕ} {c : Fin n → Fin n → Bool} {u : Fin (n + 1) → Set.Icc (0 : ℝ) 1}
    (humono : Monotone u)
    (hcell : ∀ (i j : Fin n),
      ∀ s ∈ Set.Icc (u i.castSucc) (u i.succ) ×ˢ Set.Icc (u j.castSucc) (u j.succ),
        ((1 - (s.2 : ℝ)) • γ₁ s.1 + (s.2 : ℝ) • γ₂ s.1) ∈
          (if c i j = true then W₂ else W₁))
    {i i' j : Fin n} (hii' : i.1 + 1 = i'.1) (hij : c i j ≠ c i' j)
    {τ : Set.Icc (0 : ℝ) 1} (hτ : τ ∈ Set.Icc (u j.castSucc) (u j.succ)) :
    ((1 - (τ : ℝ)) • γ₁ (u i'.castSucc) + (τ : ℝ) • γ₂ (u i'.castSucc)) ∈ W₁ ∩ W₂ := by
  have hcs : (i'.castSucc : Fin (n + 1)) = i.succ :=
    Fin.ext (by simpa [Fin.val_succ] using hii'.symm)
  have hle : (i.castSucc : Fin (n + 1)) ≤ i.succ := by simp [Fin.le_iff_val_le_val]
  have hle' : (i'.castSucc : Fin (n + 1)) ≤ i'.succ := by simp [Fin.le_iff_val_le_val]
  have hmemA : (⟨u i'.castSucc, τ⟩ : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1) ∈
      Set.Icc (u i.castSucc) (u i.succ) ×ˢ Set.Icc (u j.castSucc) (u j.succ) := by
    refine ⟨?_, hτ⟩
    simp only [Set.mem_Icc]
    rw [hcs]
    exact ⟨humono hle, le_rfl⟩
  have hmemB : (⟨u i'.castSucc, τ⟩ : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1) ∈
      Set.Icc (u i'.castSucc) (u i'.succ) ×ˢ Set.Icc (u j.castSucc) (u j.succ) := by
    refine ⟨?_, hτ⟩
    simp only [Set.mem_Icc]
    exact ⟨le_rfl, humono hle'⟩
  have hA := hcell i j _ hmemA
  have hB := hcell i' j _ hmemB
  cases hci : (c i j) <;> cases hcj : (c i' j)
  · exact absurd (by rw [hci, hcj]) hij
  · rw [hci] at hA
    rw [hcj] at hB
    simp only [Bool.false_eq_true, ↓reduceIte] at hA
    simp only [↓reduceIte] at hB
    exact ⟨hA, hB⟩
  · rw [hci] at hA
    rw [hcj] at hB
    simp only [↓reduceIte] at hA
    simp only [Bool.false_eq_true, ↓reduceIte] at hB
    exact ⟨hB, hA⟩
  · exact absurd (by rw [hci, hcj]) hij

/-- **Last row of the van Kampen grid** (the dual of `grid_bottom_row_mem_inter`).  A top-row cell
labelled `W₁` covers a segment of the top edge `γ₂` lying entirely in `U = W₁ ∩ W₂`: for `τ` in the
cell's `u`-range, `γ₂ τ ∈ U`.  (Reason: `(τ, 1)` lies in that cell because `u (Fin.last n) = 1` and
the grid points of the last row end at `Fin.last n`; and `γ₂ τ ∈ W₂` by hypothesis.) -/
theorem grid_top_row_mem_inter {p a b : ℝ} (hp : 0 < p)
    {W₁ W₂ : Set (ℝ × ℝ)}
    (hsub₁ : W₁ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hsub₂ : W₂ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₁ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₁ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₂ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₂ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hcov : W₁ ∪ W₂ = {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    {γ₁ γ₂ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ)} (h₁ : ∀ t, γ₁ t ∈ W₁) (h₂ : ∀ t, γ₂ t ∈ W₂)
    {n : ℕ} (hn : 0 < n) {c : Fin n → Fin n → Bool} {u : Fin (n + 1) → Set.Icc (0 : ℝ) 1}
    (hu1 : u (Fin.last n) = 1)
    (hcell : ∀ (i j : Fin n),
      ∀ s ∈ Set.Icc (u i.castSucc) (u i.succ) ×ˢ Set.Icc (u j.castSucc) (u j.succ),
        ((1 - (s.2 : ℝ)) • γ₁ s.1 + (s.2 : ℝ) • γ₂ s.1) ∈
          (if c i j = true then W₂ else W₁))
    {i : Fin n} (hc : c i ⟨n - 1, by omega⟩ = false) {τ : Set.Icc (0 : ℝ) 1}
    (hτ : τ ∈ Set.Icc (u i.castSucc) (u i.succ)) : γ₂ τ ∈ W₁ ∩ W₂ := by
  have hlast : (⟨n - 1, by omega⟩ : Fin n).succ = Fin.last n :=
    Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
  have hmem : (⟨τ, (1 : Set.Icc (0 : ℝ) 1)⟩ : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1) ∈
      Set.Icc (u i.castSucc) (u i.succ) ×ˢ
        Set.Icc (u (⟨n - 1, by omega⟩ : Fin n).castSucc)
          (u (⟨n - 1, by omega⟩ : Fin n).succ) := by
    refine ⟨hτ, ?_⟩
    simp only [Set.mem_Icc]
    constructor
    · exact (u _).2.2
    · rw [hlast, hu1]
  have h := hcell i ⟨n - 1, by omega⟩ ⟨τ, (1 : Set.Icc (0 : ℝ) 1)⟩ hmem
  simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
  have hred : (1 - ((1 : Set.Icc (0 : ℝ) 1) : ℝ)) • γ₁ τ
      + ((1 : Set.Icc (0 : ℝ) 1) : ℝ) • γ₂ τ = γ₂ τ := by simp
  rw [hred] at h
  exact ⟨h, h₂ τ⟩

/-- **First row of the van Kampen grid.**  A bottom-row cell labelled `W₂` covers a segment of the
bottom edge `γ₁` that lies entirely in `U = W₁ ∩ W₂`: for `τ` in the cell's `u`-range, `γ₁ τ ∈ U`.
(Reason: `(τ, 0)` lies in that cell, its `F`-image is `γ₁ τ`, and `γ₁ τ ∈ W₁` by hypothesis.) -/
theorem grid_bottom_row_mem_inter {p a b : ℝ} (hp : 0 < p)
    {W₁ W₂ : Set (ℝ × ℝ)}
    (hsub₁ : W₁ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hsub₂ : W₂ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₁ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₁ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₂ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₂ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hcov : W₁ ∪ W₂ = {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    {γ₁ γ₂ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ)} (h₁ : ∀ t, γ₁ t ∈ W₁) (h₂ : ∀ t, γ₂ t ∈ W₂)
    {n : ℕ} (hn : 0 < n) {c : Fin n → Fin n → Bool} {u : Fin (n + 1) → Set.Icc (0 : ℝ) 1}
    (hu0 : u 0 = 0) (humono : Monotone u)
    (hcell : ∀ (i j : Fin n),
      ∀ s ∈ Set.Icc (u i.castSucc) (u i.succ) ×ˢ Set.Icc (u j.castSucc) (u j.succ),
        ((1 - (s.2 : ℝ)) • γ₁ s.1 + (s.2 : ℝ) • γ₂ s.1) ∈
          (if c i j = true then W₂ else W₁))
    {i : Fin n} (hc : c i ⟨0, hn⟩ = true) {τ : Set.Icc (0 : ℝ) 1}
    (hτ : τ ∈ Set.Icc (u i.castSucc) (u i.succ)) : γ₁ τ ∈ W₁ ∩ W₂ := by
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn⟩
  have hzero : u (0 : Fin (n + 1)) = 0 := hu0
  have hmem : (⟨τ, (0 : Set.Icc (0 : ℝ) 1)⟩ : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1) ∈
      Set.Icc (u i.castSucc) (u i.succ) ×ˢ
        Set.Icc (u (0 : Fin n).castSucc) (u (0 : Fin n).succ) := by
    refine ⟨hτ, ?_⟩
    simp only [Set.mem_Icc]
    constructor
    · have hcs : (0 : Fin n).castSucc = (0 : Fin (n + 1)) := Fin.ext rfl
      rw [hcs, hzero]
    · have hle : (0 : Fin (n + 1)) ≤ (0 : Fin n).succ := by simp
      have := humono hle
      rwa [hzero] at this
  have h := hcell i ⟨0, hn⟩ ⟨τ, (0 : Set.Icc (0 : ℝ) 1)⟩ hmem
  rw [if_pos hc] at h
  refine ⟨h₁ τ, ?_⟩
  have hred : (1 - ((0 : Set.Icc (0 : ℝ) 1) : ℝ)) • γ₁ τ
      + ((0 : Set.Icc (0 : ℝ) 1) : ℝ) • γ₂ τ = γ₁ τ := by simp
  rwa [hred] at h

/-! ## The van Kampen grid on the square between the two translate paths

Instantiation of `Commons.Topology.Homotopy.exists_grid_decomposition_of_open_cover` on the square
`F (u,t) = (1-t) • γ₁ u + t • γ₂ u` (bottom edge `γ₁ ⊆ W₁`, top edge `γ₂ ⊆ W₂`, right edge
`T ∘ F (0,·)`, all inside the convex strip `S = W₁ ∪ W₂`).  The result partitions `I × I` into cells
each of whose `F`-images lies entirely in `W₁` or entirely in `W₂` — the combinatorial skeleton on
which the Mayer–Vietoris cancellation runs. -/

/-- **Grid decomposition on the square spanned by two translate paths.** -/
theorem exists_grid_decomposition_of_two_translate_paths {p a b : ℝ} (hp : 0 < p)
    {W₁ W₂ : Set (ℝ × ℝ)}
    (hsub₁ : W₁ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hsub₂ : W₂ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₁ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₁ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₂ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₂ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hcov : W₁ ∪ W₂ = {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    {γ₁ γ₂ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ)} (h₁ : ∀ t, γ₁ t ∈ W₁) (h₂ : ∀ t, γ₂ t ∈ W₂) :
    ∃ (n : ℕ) (_ : 0 < n) (c : Fin n → Fin n → Bool) (u : Fin (n + 1) → Set.Icc (0 : ℝ) 1),
      u 0 = 0 ∧ u (Fin.last n) = 1 ∧ Monotone u ∧
      ∀ (i j : Fin n),
        ∀ s ∈ Set.Icc (u i.castSucc) (u i.succ) ×ˢ Set.Icc (u j.castSucc) (u j.succ),
          ((1 - (s.2 : ℝ)) • γ₁ s.1 + (s.2 : ℝ) • γ₂ s.1) ∈
            (if c i j = true then W₂ else W₁) := by
  obtain ⟨U₁, hU₁o, hU₁eq⟩ := hopen₁
  obtain ⟨U₂, hU₂o, hU₂eq⟩ := hopen₂
  set S : Set (ℝ × ℝ) := {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} with hSdef
  have hW₁U : W₁ ⊆ U₁ := by rw [hU₁eq]; exact Set.inter_subset_left
  have hW₂U : W₂ ⊆ U₂ := by rw [hU₂eq]; exact Set.inter_subset_left
  have hSconv : Convex ℝ S := by
    rw [hSdef]
    have h1 : {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} = Set.univ ×ˢ Set.Icc a b := by
      ext q; simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and, Set.mem_Icc]
    rw [h1]; exact convex_univ.prod (convex_Icc a b)
  set F : C(Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1, ℝ × ℝ) :=
    ⟨fun s => (1 - (s.2 : ℝ)) • γ₁ s.1 + (s.2 : ℝ) • γ₂ s.1, by fun_prop⟩ with hFdef
  have hFmem : ∀ s : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1, F s ∈ S := by
    intro s
    have h2 : (0 : ℝ) ≤ (s.2 : ℝ) ∧ (s.2 : ℝ) ≤ 1 := s.2.2
    have h := hSconv (x := γ₁ s.1) (y := γ₂ s.1) (a := 1 - (s.2 : ℝ)) (b := (s.2 : ℝ))
      (hsub₁ (h₁ s.1)) (hsub₂ (h₂ s.1)) (by linarith [h2.2]) (by linarith [h2.1]) (by ring)
    simpa [hFdef] using h
  have hFcov : ∀ s : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1, F s ∈ U₁ ∪ U₂ := by
    intro s
    have hs := hFmem s
    rw [← hcov] at hs
    rcases hs with h | h
    · exact Or.inl (hW₁U h)
    · exact Or.inr (hW₂U h)
  obtain ⟨n, hn, c, u, hu0, hu1, humono, hcell⟩ :=
    Commons.Topology.Homotopy.exists_grid_decomposition_of_open_cover hU₁o hU₂o hFcov
  refine ⟨n, hn, c, u, hu0, hu1, humono, ?_⟩
  intro i j s hs
  have hcellij : F s ∈ (if c i j = true then U₂ else U₁) := hcell i j s hs
  have hFs : F s ∈ S := hFmem s
  by_cases hc : c i j = true
  · rw [if_pos hc] at hcellij
    rw [if_pos hc, hU₂eq]
    exact ⟨hcellij, hFs⟩
  · rw [if_neg hc] at hcellij
    rw [if_neg hc, hU₁eq]
    exact ⟨hcellij, hFs⟩

/-- **Shared-edge lemma for a two-set grid over the square (general form).**  Let `U, V ⊆ X` be open,
`H : I × I → X`, and let a grid `u` carry a labelling `c` such that every cell's `H`-image lies in `U`
(if `c i j = false`) or in `V` (if `c i j = true`).  Then for two **horizontally adjacent** cells
`(i,j)`, `(i',j)` with different labels, the `H`-image of their shared edge lies in `U ∩ V`: the shared
edge is contained in *both* closed cells, so two applications of the cell property put its image in
both open sets.

This is the general (`X`, open `U`/`V`, arbitrary `H`) form of the point-set bookkeeping used in this
file's strip lemmas; it is the step 3 of the van Kampen plan for
`exists_path_in_inter_of_homotopic_loops` and is useful independently of the strip. -/
theorem grid_shared_vertical_edge_mem_inter {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    {H : C(Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1, X)}
    {n : ℕ} {c : Fin n → Fin n → Bool} {u : Fin (n + 1) → Set.Icc (0 : ℝ) 1}
    (humono : Monotone u)
    (hcell : ∀ (i j : Fin n),
      ∀ s ∈ Set.Icc (u i.castSucc) (u i.succ) ×ˢ Set.Icc (u j.castSucc) (u j.succ),
        H s ∈ (if c i j = true then V else U))
    {i i' j : Fin n} (hii' : i.1 + 1 = i'.1) (hij : c i j ≠ c i' j)
    {τ : Set.Icc (0 : ℝ) 1} (hτ : τ ∈ Set.Icc (u j.castSucc) (u j.succ)) :
    H ⟨u i'.castSucc, τ⟩ ∈ U ∩ V := by
  have hcs : (i'.castSucc : Fin (n + 1)) = i.succ :=
    Fin.ext (by simpa [Fin.val_succ] using hii'.symm)
  have hle : (i.castSucc : Fin (n + 1)) ≤ i.succ := by simp [Fin.le_iff_val_le_val]
  have hle' : (i'.castSucc : Fin (n + 1)) ≤ i'.succ := by simp [Fin.le_iff_val_le_val]
  have hmemA : (⟨u i'.castSucc, τ⟩ : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1) ∈
      Set.Icc (u i.castSucc) (u i.succ) ×ˢ Set.Icc (u j.castSucc) (u j.succ) := by
    refine ⟨?_, hτ⟩
    simp only [Set.mem_Icc]
    rw [hcs]
    exact ⟨humono hle, le_rfl⟩
  have hmemB : (⟨u i'.castSucc, τ⟩ : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1) ∈
      Set.Icc (u i'.castSucc) (u i'.succ) ×ˢ Set.Icc (u j.castSucc) (u j.succ) := by
    refine ⟨?_, hτ⟩
    simp only [Set.mem_Icc]
    exact ⟨le_rfl, humono hle'⟩
  have hA := hcell i j _ hmemA
  have hB := hcell i' j _ hmemB
  cases hci : (c i j) <;> cases hcj : (c i' j)
  · exact absurd (by rw [hci, hcj]) hij
  · rw [hci] at hA
    rw [hcj] at hB
    simp only [Bool.false_eq_true, ↓reduceIte] at hA
    simp only [↓reduceIte] at hB
    exact ⟨hA, hB⟩
  · rw [hci] at hA
    rw [hcj] at hB
    simp only [↓reduceIte] at hA
    simp only [Bool.false_eq_true, ↓reduceIte] at hB
    exact ⟨hB, hA⟩
  · exact absurd (by rw [hci, hcj]) hij

/-- **Classification of a row of a vertical grid line.**  For the line `u = u i'.castSucc` flanked by
the cells `(i,j)` and `(i',j)` (so `i.1 + 1 = i'.1`): the whole `F`-image of the line's segment over
row `j` lies in `W₁ ∩ W₂` when the two labels **differ** in that row, and in the **common** label
`W_{c i j} = W_{c i' j}` when they agree.  (`F (u i'.castSucc, τ)` lies in both closed cells `(i,j)`
and `(i',j)` whenever `τ` is in row `j`'s interval, so two applications of `hcell` decide it.)

This is the classification the interface assembly walks: each row of the line is either a `U`-run or
a run of a single one of the two sets, and the `JoinedIn` clause of `exists_U_path_on_grid_line`
follows by walking the rows. -/
theorem grid_line_row_classification {p a b : ℝ} (hp : 0 < p)
    {W₁ W₂ : Set (ℝ × ℝ)}
    (hsub₁ : W₁ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hsub₂ : W₂ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₁ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₁ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₂ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₂ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hcov : W₁ ∪ W₂ = {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    {γ₁ γ₂ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ)} (h₁ : ∀ t, γ₁ t ∈ W₁) (h₂ : ∀ t, γ₂ t ∈ W₂)
    {n : ℕ} {c : Fin n → Fin n → Bool} {u : Fin (n + 1) → Set.Icc (0 : ℝ) 1}
    (humono : Monotone u)
    (hcell : ∀ (i j : Fin n),
      ∀ s ∈ Set.Icc (u i.castSucc) (u i.succ) ×ˢ Set.Icc (u j.castSucc) (u j.succ),
        ((1 - (s.2 : ℝ)) • γ₁ s.1 + (s.2 : ℝ) • γ₂ s.1) ∈
          (if c i j = true then W₂ else W₁))
    {i i' j : Fin n} (hii' : i.1 + 1 = i'.1) {τ : Set.Icc (0 : ℝ) 1}
    (hτ : τ ∈ Set.Icc (u j.castSucc) (u j.succ)) :
    (c i j = c i' j →
      ((1 - (τ : ℝ)) • γ₁ (u i'.castSucc) + (τ : ℝ) • γ₂ (u i'.castSucc)) ∈
        (if c i j = true then W₂ else W₁)) ∧
    (c i j ≠ c i' j →
      ((1 - (τ : ℝ)) • γ₁ (u i'.castSucc) + (τ : ℝ) • γ₂ (u i'.castSucc)) ∈ W₁ ∩ W₂) := by
  have hcs : (i'.castSucc : Fin (n + 1)) = i.succ :=
    Fin.ext (by simpa [Fin.val_succ] using hii'.symm)
  have hle : (i.castSucc : Fin (n + 1)) ≤ i.succ := by simp [Fin.le_iff_val_le_val]
  have hle' : (i'.castSucc : Fin (n + 1)) ≤ i'.succ := by simp [Fin.le_iff_val_le_val]
  have hmemA : (⟨u i'.castSucc, τ⟩ : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1) ∈
      Set.Icc (u i.castSucc) (u i.succ) ×ˢ Set.Icc (u j.castSucc) (u j.succ) := by
    refine ⟨?_, hτ⟩
    simp only [Set.mem_Icc]
    rw [hcs]
    exact ⟨humono hle, le_rfl⟩
  have hmemB : (⟨u i'.castSucc, τ⟩ : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1) ∈
      Set.Icc (u i'.castSucc) (u i'.succ) ×ˢ Set.Icc (u j.castSucc) (u j.succ) := by
    refine ⟨?_, hτ⟩
    simp only [Set.mem_Icc]
    exact ⟨le_rfl, humono hle'⟩
  have hA := hcell i j _ hmemA
  have hB := hcell i' j _ hmemB
  refine ⟨?_, ?_⟩
  · intro hagree
    rw [← hagree] at hB
    exact hA
  · intro hne
    cases hci : (c i j) <;> cases hcj : (c i' j)
    · exact absurd (by rw [hci, hcj]) hne
    · rw [hci] at hA
      rw [hcj] at hB
      simp only [Bool.false_eq_true, ↓reduceIte] at hA
      simp only [↓reduceIte] at hB
      exact ⟨hA, hB⟩
    · rw [hci] at hA
      rw [hcj] at hB
      simp only [↓reduceIte] at hA
      simp only [Bool.false_eq_true, ↓reduceIte] at hB
      exact ⟨hB, hA⟩
    · exact absurd (by rw [hci, hcj]) hne

/-! ## Extracting the `U`-curve from a filling of the square (Half A)

The point-set half of the interface curve: given a continuous filling `F` of the square whose image
lies in the strip `S = W₁ ∪ W₂`, whose bottom edge lies in `W₁` and whose top edge in `W₂`, there is a
left–right curve in the square whose `F`-image lies in `U = W₁ ∩ W₂`.  This is
`Commons.Topology.Strip.extraction_square_map` plus one bookkeeping step: the extracted curve's image
lies in the *ambient* opens `U₁ ⊇ W₁`, `U₂ ⊇ W₂` of `hopen₁`, `hopen₂`, and `F (I × I) ⊆ S` converts
that to `W₁ ∩ W₂` (using `Wᵢ = Uᵢ ∩ S`).

Instantiating `F` with the clamped Coons filling `sclamp a b ∘ coons D` of the file's
`exists_relation_of_arbitrary_connector` (line 615) then gives Half A for the two translate paths; the
remaining obligation is the endpoint matching condition alone. -/

theorem exists_leftright_curve_of_filling {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {W₁ W₂ : Set (ℝ × ℝ)}
    (hsub₁ : W₁ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hsub₂ : W₂ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₁ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₁ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₂ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₂ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hcov : W₁ ∪ W₂ = {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    {F : C(ℝ × ℝ, ℝ × ℝ)} (hFmem : ∀ q ∈ sq, F q ∈ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hbot : ∀ u : ℝ, F (u, 0) ∈ W₁) (htop : ∀ u : ℝ, F (u, 1) ∈ W₂) :
    ∃ ϑ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
      (∀ t, ϑ t ∈ sq) ∧ (ϑ 0).1 = 0 ∧ (ϑ 1).1 = 1 ∧ ∀ t, F (ϑ t) ∈ W₁ ∩ W₂ := by
  obtain ⟨U₁, hU₁o, hU₁eq⟩ := hopen₁
  obtain ⟨U₂, hU₂o, hU₂eq⟩ := hopen₂
  obtain ⟨ϑ, hϑsq, hϑ0, hϑ1, hϑU⟩ :=
    Commons.Topology.Strip.extraction_square_map hU₁o hU₂o (F := F)
      (fun q hq => by
        have h1 : F q ∈ W₁ ∪ W₂ := by rw [hcov]; exact hFmem q hq
        rcases h1 with h | h
        · exact Or.inl (by rw [hU₁eq] at h; exact h.1)
        · exact Or.inr (by rw [hU₂eq] at h; exact h.1))
      (fun q _ hq2 => by
        have h := hbot q.1
        have hq' : q = (q.1, (0 : ℝ)) := Prod.ext rfl hq2
        rw [hq']
        rw [hU₁eq] at h
        exact h.1)
      (fun q _ hq2 => by
        have h := htop q.1
        have hq' : q = (q.1, (1 : ℝ)) := Prod.ext rfl hq2
        rw [hq']
        rw [hU₂eq] at h
        exact h.1)
  refine ⟨ϑ, hϑsq, hϑ0, hϑ1, fun t => ?_⟩
  have hmem : F (ϑ t) ∈ U₁ ∩ U₂ := hϑU t
  have hFsq : F (ϑ t) ∈ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} := hFmem (ϑ t) (hϑsq t)
  exact ⟨(by rw [hU₁eq]; exact ⟨hmem.1, hFsq⟩),
    (by rw [hU₂eq]; exact ⟨hmem.2, hFsq⟩)⟩

/-! ## The interface assembly (the remaining Mayer–Vietoris step, stated correctly)

The grid toolkit above delivers `U`-*points* and `U`-*runs*: label changes on grid lines
(`grid_vertical_edge_mem_inter`, sharpened to whole rows by `grid_line_row_classification`) and
`U`-runs of `γ₁`/`γ₂` on the bottom/top rows.  What the degree argument consumes is a `U`-**curve**.
The statement below is that one, in the form in which it is both true-shaped and sufficient:

> `F^{-1}(U)` contains a curve from the **left edge** of the square to the **right edge**, whose two
> `F`-images match under `T`.

Since `F (1,t) = T (F (0,t))`, the matching condition says that the connector `σ = F (0,·)` takes the
same value at the two endpoint heights, and then the curve's `F`-image *is* a path in `U` from
`z := σ (a₀)` to `T z` — a translate path inside `U`, i.e. the crux outright (via
`exists_translate_path_of_loop_winding`, or directly).

**Negative result that fixes this phrasing** (see the notes): a *row-by-row* detour argument cannot
prove this.  With rows `j` and `j+2` of a vertical line carrying `U`-runs and the middle row `j+1`
carrying the single label `W₁` in *both* flanking cells, the two boundary grid points are in `U` but
no local step between them lies in `U`, so any such curve has to wander at a distance through the
square.  That is the Mayer–Vietoris cancellation, and it is why this statement is stated whole rather
than decomposed. -/

/-- **The interface curve implies the conclusion (the wiring).**  Given a curve `ϑ` in the square whose
`F`-image lies in `U = W₁ ∩ W₂` and whose ends match under `T`, the composite `F ∘ ϑ` *is* a translate
path inside `U`, with base point `F (ϑ 0)`: its endpoint is `F (ϑ 1) = T (F (ϑ 0))`.  This is the
step that shows that an interface curve (a curve in the square whose `F`-image lies in `U` and whose
ends match under `T`) suffices for the crux. -/
theorem exists_translate_path_of_U_curve {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {W₁ W₂ : Set (ℝ × ℝ)}
    (hsub₁ : W₁ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hsub₂ : W₂ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₁ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₁ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₂ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₂ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hcov : W₁ ∪ W₂ = {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    {γ₁ γ₂ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ)} (h₁ : ∀ t, γ₁ t ∈ W₁) (h₂ : ∀ t, γ₂ t ∈ W₂)
    {ϑ : C(Set.Icc (0 : ℝ) 1, Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1)}
    (hmeet : ∀ t : Set.Icc (0 : ℝ) 1,
      (1 - ((ϑ t).2 : ℝ)) • γ₁ (ϑ t).1 + ((ϑ t).2 : ℝ) • γ₂ (ϑ t).1 ∈ W₁ ∩ W₂)
    (hmatch : ((1 - ((ϑ 1).2 : ℝ)) • γ₁ (ϑ 1).1 + ((ϑ 1).2 : ℝ) • γ₂ (ϑ 1).1)
        = (((1 - ((ϑ 0).2 : ℝ)) • γ₁ (ϑ 0).1 + ((ϑ 0).2 : ℝ) • γ₂ (ϑ 0).1).1 + p,
           ((1 - ((ϑ 0).2 : ℝ)) • γ₁ (ϑ 0).1 + ((ϑ 0).2 : ℝ) • γ₂ (ϑ 0).1).2)) :
    ∃ z : ℝ × ℝ, z ∈ W₁ ∩ W₂ ∧ JoinedIn (W₁ ∩ W₂) z (z.1 + p, z.2) := by
  refine ⟨(1 - ((ϑ 0).2 : ℝ)) • γ₁ (ϑ 0).1 + ((ϑ 0).2 : ℝ) • γ₂ (ϑ 0).1, hmeet 0, ?_⟩
  refine ⟨⟨⟨fun t : Set.Icc (0 : ℝ) 1 =>
      (1 - ((ϑ t).2 : ℝ)) • γ₁ (ϑ t).1 + ((ϑ t).2 : ℝ) • γ₂ (ϑ t).1, ?_⟩, ?_, ?_⟩, ?_⟩
  · fun_prop
  · rfl
  · exact hmatch
  · exact fun t => hmeet t

/-- **Interface lemma: the degree form of the crux implies the crux.**  If the excisive intersection
`W₁ ∩ W₂` carries a *loop of nonzero winding* (a path from a point to its translate by a nonzero
multiple of the period), then it carries an honest translate path.  This isolates the point where the
degree theory plugs into the crux: what remains to be proved is precisely the existence of such a
loop (the Mayer–Vietoris middle-term exactness for the excisive pair `(W₁/T, W₂/T)`). -/
theorem exists_translate_path_of_winding_in_inter {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {W₁ W₂ : Set (ℝ × ℝ)} (hsub : W₁ ∩ W₂ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hper : ∀ q : ℝ × ℝ, q ∈ W₁ ∩ W₂ ↔ (q.1 + p, q.2) ∈ W₁ ∩ W₂)
    (h : ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ), (∀ t, γ t ∈ W₁ ∩ W₂) ∧
      ∃ d : ℤ, d ≠ 0 ∧ γ 1 = ((γ 0).1 + (d : ℝ) * p, (γ 0).2)) :
    ∃ z : ℝ × ℝ, z ∈ W₁ ∩ W₂ ∧ JoinedIn (W₁ ∩ W₂) z (z.1 + p, z.2) := by
  obtain ⟨γ, hγ, d, hd, hγ1⟩ := h
  exact exists_translate_path_of_loop_winding hp hab hsub hper hγ hd hγ1

/-! ## The two-set Mayer--Vietoris decomposition route to the crux

The sheet index `exists_sheet_index_joinedIn` plus the commons' two-set decomposition
`exists_decomposition` give a *direct* proof of the crux, replacing the interface route.
-/

/-- A locally constant function on a subtype, read in the ambient space. -/
lemma eventually_subtype_eq {X : Type*} [TopologicalSpace X] {C : Set X} {φ : C → ℤ}
    (hφ : IsLocallyConstant φ) (x : C) :
    ∀ᶠ y in nhds (x : X), ∀ (hy : y ∈ C), φ ⟨y, hy⟩ = φ x := by
  have h : {z : C | φ z = φ x} ∈ Filter.comap (Subtype.val : C → X) (nhds (x : X)) := by
    rw [← nhds_subtype]
    exact hφ.eventually_eq x
  obtain ⟨t, ht, hsub⟩ := Filter.mem_comap.mp h
  exact Filter.mem_of_superset ht (fun y hy hyC =>
    hsub (show (⟨y, hyC⟩ : C) ∈ Subtype.val ⁻¹' t from hy))


/-- A join in a set `W ⊆ S` at the level of `ℝ × ℝ` transports to a join in the corresponding
subtype of `↥S`. -/
lemma joinedIn_subtype_of_joinedIn {S : Set (ℝ × ℝ)} {W : Set (ℝ × ℝ)} (hWS : W ⊆ S) {x y : ℝ × ℝ} (hx : x ∈ W) (hy : y ∈ W)
    (h : JoinedIn W x y) :
    JoinedIn {p : ↥S | (p : ℝ × ℝ) ∈ W} ⟨x, hWS hx⟩ ⟨y, hWS hy⟩ := by
  obtain ⟨γ, hγ⟩ := h
  let F : ↑(Set.Icc (0:ℝ) 1) → ↥S := fun t => ⟨γ t, hWS (hγ t)⟩
  have hFc : Continuous F := Continuous.subtype_mk γ.continuous (fun t => hWS (hγ t))
  refine ⟨⟨⟨F, hFc⟩, ?_, ?_⟩, fun t => hγ t⟩
  · apply Subtype.ext
    exact γ.source
  · apply Subtype.ext
    exact γ.target


/-- The translation `T q = (q.1 + p, q.2)`. -/
def Tm (p : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (q.1 + p, q.2)

@[simp] lemma Tm_apply (p : ℝ) (q : ℝ × ℝ) : Tm p q = (q.1 + p, q.2) := rfl

lemma continuous_Tm (p : ℝ) : Continuous (Tm p) := by
  show Continuous fun q : ℝ × ℝ => (q.1 + p, q.2); fun_prop

/-- The `k`-fold translate `q ↦ (q.1 + k p, q.2)`. -/
def Tk (p : ℝ) (k : ℤ) (q : ℝ × ℝ) : ℝ × ℝ := (q.1 + k * p, q.2)

@[simp] lemma Tk_zero (p : ℝ) (q : ℝ × ℝ) : Tk p 0 q = q := by ext <;> simp [Tk]

lemma Tk_add (p : ℝ) (j k : ℤ) (q : ℝ × ℝ) : Tk p (j + k) q = Tk p j (Tk p k q) := by
  ext <;> simp only [Tk] <;> push_cast <;> ring

lemma Tk_one (p : ℝ) (q : ℝ × ℝ) : Tk p 1 q = Tm p q := by
  ext <;> simp [Tk, Tm]

lemma continuous_Tk (p : ℝ) (k : ℤ) : Continuous (Tk p k) := by
  show Continuous fun q : ℝ × ℝ => (q.1 + (k : ℝ) * p, q.2); fun_prop

/-- `T`-invariance upgrades to all integer powers. -/
lemma Tk_mem_iff {p : ℝ} {V : Set (ℝ × ℝ)} (hV : ∀ q : ℝ × ℝ, q ∈ V ↔ Tm p q ∈ V)
    (k : ℤ) (q : ℝ × ℝ) : Tk p k q ∈ V ↔ q ∈ V := by
  have h1 : ∀ x : ℝ × ℝ, Tk p (1 : ℤ) x ∈ V ↔ x ∈ V := by
    intro x; rw [Tk_one]; exact (hV x).symm
  have hnat : ∀ m : ℕ, ∀ x : ℝ × ℝ, Tk p (m : ℤ) x ∈ V ↔ x ∈ V := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        have hcast : (((k : ℕ) + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
        have hsplit : Tk p ((k : ℤ) + 1) x = Tk p (k : ℤ) (Tk p 1 x) := Tk_add p (k : ℤ) 1 x
        rw [hcast, hsplit, ih, h1]
  rcases lt_or_ge k 0 with hk | hk
  · have hpos : (0 : ℤ) ≤ -k := by omega
    have hcast : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg hpos
    have h := hnat ((-k).toNat) (Tk p k q)
    rw [hcast] at h
    have hcomp : Tk p (-k) (Tk p k q) = q := by rw [← Tk_add, neg_add_cancel, Tk_zero]
    rw [hcomp] at h
    exact h.symm
  · have hcast : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk
    have h := hnat k.toNat q
    rw [hcast] at h
    exact h

/-- Integer translates of joinable points stay joinable (in a `T`-invariant set). -/
lemma joinedIn_Tk {p : ℝ} {W : Set (ℝ × ℝ)} (hW : ∀ q : ℝ × ℝ, q ∈ W ↔ Tm p q ∈ W)
    (k : ℤ) {x y : ℝ × ℝ} (h : JoinedIn W x y) : JoinedIn W (Tk p k x) (Tk p k y) := by
  obtain ⟨γ, hγ⟩ := h
  exact ⟨γ.map (continuous_Tk p k), fun u => (Tk_mem_iff hW k (γ u)).mpr (hγ u)⟩


/-- The "same `T`-orbit" relation on a `T`-invariant set `U`: some translate of `q` is joined to
`q'` inside `U`. -/
def sheetRel (p : ℝ) (U : Set (ℝ × ℝ)) (q q' : ℝ × ℝ) : Prop :=
  ∃ k : ℤ, JoinedIn U (Tk p k q) q'

/-- `sheetRel` is a setoid on a `T`-invariant `U`. -/
def sheetSetoid (p : ℝ) {U : Set (ℝ × ℝ)} (hU : ∀ q : ℝ × ℝ, q ∈ U ↔ Tm p q ∈ U) :
    Setoid ↥U where
  r q q' := sheetRel p U (q : ℝ × ℝ) (q' : ℝ × ℝ)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro q
      exact ⟨0, by rw [Tk_zero]; exact JoinedIn.refl q.2⟩
    · intro q q' h
      obtain ⟨k, hk⟩ := h
      refine ⟨-k, ?_⟩
      have h1 := joinedIn_Tk (p := p) hU (-k) hk
      rw [← Tk_add, neg_add_cancel, Tk_zero] at h1
      exact h1.symm
    · intro q q' q'' h h'
      obtain ⟨k, hk⟩ := h
      obtain ⟨m, hm⟩ := h'
      refine ⟨m + k, ?_⟩
      have h1 := joinedIn_Tk (p := p) hU m hk
      rw [← Tk_add] at h1
      exact h1.trans hm

/-- A chosen representative in each `T`-orbit class. -/
noncomputable def sheetRep (p : ℝ) {U : Set (ℝ × ℝ)}
    (hU : ∀ q : ℝ × ℝ, q ∈ U ↔ Tm p q ∈ U) : Quotient (sheetSetoid p hU) → ↥U :=
  fun c => Classical.choose (Quotient.exists_rep c)

lemma sheetRep_spec (p : ℝ) {U : Set (ℝ × ℝ)}
    (hU : ∀ q : ℝ × ℝ, q ∈ U ↔ Tm p q ∈ U) (c : Quotient (sheetSetoid p hU)) :
    Quotient.mk _ (sheetRep p hU c) = c :=
  Classical.choose_spec (Quotient.exists_rep c)

/-- Every point of `U` is joined to a translate of the representative of its class. -/
lemma sheetInd_exists (p : ℝ) {U : Set (ℝ × ℝ)}
    (hU : ∀ q : ℝ × ℝ, q ∈ U ↔ Tm p q ∈ U) (q : ↥U) :
    ∃ k : ℤ, JoinedIn U (Tk p k ((sheetRep p hU (Quotient.mk _ q) : ↥U) : ℝ × ℝ)) (q : ℝ × ℝ) := by
  have hc : Quotient.mk (sheetSetoid p hU) (sheetRep p hU (Quotient.mk _ q)) = Quotient.mk _ q := by
    rw [sheetRep_spec]
  exact Quotient.exact hc

/-- The sheet index: the (unique, under `hstar`) power of `T` relating the chosen representative
to the point. -/
noncomputable def sheetInd (p : ℝ) {U : Set (ℝ × ℝ)}
    (hU : ∀ q : ℝ × ℝ, q ∈ U ↔ Tm p q ∈ U) (q : ↥U) : ℤ :=
  Classical.choose (sheetInd_exists p hU q)

lemma sheetInd_spec (p : ℝ) {U : Set (ℝ × ℝ)}
    (hU : ∀ q : ℝ × ℝ, q ∈ U ↔ Tm p q ∈ U) (q : ↥U) :
    JoinedIn U (Tk p (sheetInd p hU q) ((sheetRep p hU (Quotient.mk _ q) : ↥U) : ℝ × ℝ))
      (q : ℝ × ℝ) :=
  Classical.choose_spec (sheetInd_exists p hU q)

/-- Uniqueness of the exponent (this is where the "no translate path" hypothesis enters). -/
lemma sheetInd_unique {p : ℝ} {U : Set (ℝ × ℝ)}
    (hU : ∀ q : ℝ × ℝ, q ∈ U ↔ Tm p q ∈ U)
    (hstar : ∀ q : ℝ × ℝ, q ∈ U → ∀ n : ℤ, n ≠ 0 → ¬ JoinedIn U (Tk p n q) q)
    (q : ↥U) {k : ℤ}
    (hk : JoinedIn U (Tk p k ((sheetRep p hU (Quotient.mk _ q) : ↥U) : ℝ × ℝ)) (q : ℝ × ℝ)) :
    k = sheetInd p hU q := by
  by_contra hne
  set R : ℝ × ℝ := ((sheetRep p hU (Quotient.mk _ q) : ↥U) : ℝ × ℝ) with hR
  have hm := sheetInd_spec p hU q
  have hkm : k - (sheetInd p hU q) ≠ 0 := by omega
  have h2 : JoinedIn U (Tk p k R) (Tk p (sheetInd p hU q) R) := hk.trans hm.symm
  have h3 := joinedIn_Tk (p := p) hU (-(sheetInd p hU q)) h2
  rw [← Tk_add, ← Tk_add] at h3
  have e1 : -sheetInd p hU q + k = k - sheetInd p hU q := by ring
  have e2 : -sheetInd p hU q + sheetInd p hU q = 0 := by ring
  rw [e1, e2, Tk_zero] at h3
  exact hstar R (sheetRep p hU (Quotient.mk _ q)).2 (k - sheetInd p hU q) hkm h3

/-- **The sheet index exists.**  For a `T`-invariant `U` in which no point is joined to a nonzero
translate of itself, there is a `ℤ`-valued function on `U`, constant on joins, with
`ind (T q) = ind q + 1`. -/
theorem exists_sheet_index_joinedIn {p : ℝ} {U : Set (ℝ × ℝ)}
    (hU : ∀ q : ℝ × ℝ, q ∈ U ↔ Tm p q ∈ U)
    (hstar : ∀ q : ℝ × ℝ, q ∈ U → ∀ n : ℤ, n ≠ 0 → ¬ JoinedIn U (Tk p n q) q) :
    ∃ ind : ℝ × ℝ → ℤ,
      (∀ q : ℝ × ℝ, q ∈ U → ind (Tm p q) = ind q + 1) ∧
      (∀ q q' : ℝ × ℝ, q ∈ U → q' ∈ U → JoinedIn U q q' → ind q = ind q') := by
  classical
  -- the key: joins are invisible to the index
  have key : ∀ q q' : ↥U, JoinedIn U (q : ℝ × ℝ) (q' : ℝ × ℝ) →
      sheetInd p hU q = sheetInd p hU q' := by
    intro q q' h
    have hcls : Quotient.mk (sheetSetoid p hU) q = Quotient.mk (sheetSetoid p hU) q' :=
      Quotient.sound ⟨0, by rw [Tk_zero]; exact h⟩
    have hrep : sheetRep p hU (Quotient.mk (sheetSetoid p hU) q)
        = sheetRep p hU (Quotient.mk (sheetSetoid p hU) q') := by rw [hcls]
    have hspec := sheetInd_spec p hU q
    rw [hrep] at hspec
    -- hspec : JoinedIn U (Tk p (sheetInd .. q) R_q') q
    have hq'q : JoinedIn U (q : ℝ × ℝ) (q' : ℝ × ℝ) := h
    refine sheetInd_unique hU hstar q' ?_
    exact hspec.trans hq'q
  refine ⟨fun q => if hq : q ∈ U then sheetInd p hU ⟨q, hq⟩ else 0, ?_, ?_⟩
  · intro q hq
    have hTq : Tm p q ∈ U := (hU q).mp hq
    simp only [hq, hTq, dif_pos]
    -- show sheetInd (T q) = sheetInd q + 1
    have hcls : Quotient.mk (sheetSetoid p hU) ⟨Tm p q, hTq⟩
        = Quotient.mk (sheetSetoid p hU) ⟨q, hq⟩ := by
      refine Quotient.sound ?_
      refine ⟨-1, ?_⟩
      have hstep : Tk p (-1) (Tm p q) = q := by
        ext <;> simp [Tk, Tm] <;> ring
      rw [hstep]
      exact JoinedIn.refl hq
    have hrep : sheetRep p hU (Quotient.mk (sheetSetoid p hU) ⟨Tm p q, hTq⟩)
        = sheetRep p hU (Quotient.mk (sheetSetoid p hU) ⟨q, hq⟩) := by rw [hcls]
    have hspec := sheetInd_spec p hU ⟨q, hq⟩
    have hspec' : JoinedIn U
        (Tk p (sheetInd p hU ⟨q, hq⟩) ((sheetRep p hU (Quotient.mk (sheetSetoid p hU) ⟨Tm p q, hTq⟩) : ↥U) : ℝ × ℝ))
        (q : ℝ × ℝ) := by
      rw [hrep]; exact hspec
    have hmove := joinedIn_Tk (p := p) hU 1 hspec'
    have h1 : Tk p 1 (Tk p (sheetInd p hU ⟨q, hq⟩) ((sheetRep p hU (Quotient.mk (sheetSetoid p hU) ⟨Tm p q, hTq⟩) : ↥U) : ℝ × ℝ))
        = Tk p (sheetInd p hU ⟨q, hq⟩ + 1) ((sheetRep p hU (Quotient.mk (sheetSetoid p hU) ⟨Tm p q, hTq⟩) : ↥U) : ℝ × ℝ) := by
      rw [← Tk_add]
      congr 1
      ring
    have h2 : Tk p 1 q = Tm p q := Tk_one p q
    rw [h1, h2] at hmove
    exact (sheetInd_unique hU hstar ⟨Tm p q, hTq⟩ hmove).symm
  · intro q q' hq hq' h
    simp only [hq, hq', dif_pos]
    exact key ⟨q, hq⟩ ⟨q', hq'⟩ h


/-- **The crux, proved via the two-set Mayer–Vietoris decomposition.**  Two `T`-invariant sets
`W₁, W₂` that are open in the closed strip, cover it, and each carry a translate path, have a point
carrying a translate path inside their intersection. -/
theorem crux_via_decomposition {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {W₁ W₂ : Set (ℝ × ℝ)}
    (hsub₁ : W₁ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hsub₂ : W₂ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₁ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₁ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₂ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₂ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hper₁ : ∀ q : ℝ × ℝ, q ∈ W₁ ↔ (q.1 + p, q.2) ∈ W₁)
    (hper₂ : ∀ q : ℝ × ℝ, q ∈ W₂ ↔ (q.1 + p, q.2) ∈ W₂)
    (hcov : W₁ ∪ W₂ = {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hne₁ : ∃ z : ℝ × ℝ, z ∈ W₁ ∧ JoinedIn W₁ z (z.1 + p, z.2))
    (hne₂ : ∃ z : ℝ × ℝ, z ∈ W₂ ∧ JoinedIn W₂ z (z.1 + p, z.2)) :
    ∃ z : ℝ × ℝ, z ∈ W₁ ∧ z ∈ W₂ ∧ JoinedIn (W₁ ∩ W₂) z (z.1 + p, z.2) := by
  classical
  by_contra hcon
  have hcon' : ∀ z : ℝ × ℝ, z ∈ W₁ → z ∈ W₂ → ¬ JoinedIn (W₁ ∩ W₂) z (Tm p z) := by
    intro z h1 h2 hJ
    exact hcon ⟨z, h1, h2, by simpa [Tm] using hJ⟩
  obtain ⟨U₁, hU₁o, hW₁eq⟩ := hopen₁
  obtain ⟨U₂, hU₂o, hW₂eq⟩ := hopen₂
  set S : Set (ℝ × ℝ) := {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} with hSdef
  have hW₁S : W₁ ⊆ S := by rw [hW₁eq, hSdef]; exact Set.inter_subset_right
  have hW₂S : W₂ ⊆ S := by rw [hW₂eq, hSdef]; exact Set.inter_subset_right
  have hconv : Convex ℝ S := by
    rw [hSdef]
    have h : {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} = Set.univ ×ˢ Set.Icc a b := by
      ext q; simp [Set.mem_Icc]
    rw [h]; exact convex_univ.prod (convex_Icc a b)
  haveI : ContractibleSpace ↥S :=
    hconv.contractibleSpace ⟨((0 : ℝ), (a + b) / 2), by
      rw [hSdef]; exact ⟨by linarith, by linarith⟩⟩
  haveI : LocallyPathConnectedSpace ↥S := hconv.locallyPathConnectedSpace
  haveI : ConnectedSpace ↥S := inferInstance
  have hmono : ∀ z : ↥S, Subsingleton (FundamentalGroup ↥S z) := fun _ => inferInstance
  -- the two closed pieces of the complement of `U = W₁ ∩ W₂`
  set A : Set ↥S := {x : ↥S | (x : ℝ × ℝ) ∉ W₁} with hAdef
  set B : Set ↥S := {x : ↥S | (x : ℝ × ℝ) ∉ W₂} with hBdef
  have hAcl : IsClosed A := by
    have hAeq : A = (Subtype.val ⁻¹' U₁)ᶜ := by
      ext x
      constructor
      · intro hx hmem
        exact hx (by rw [hW₁eq]; exact ⟨hmem, x.2⟩)
      · intro hx hmem
        have h2 : (x : ℝ × ℝ) ∈ U₁ ∩ S := by rw [← hW₁eq]; exact hmem
        exact hx h2.1
    rw [hAeq]; exact (hU₁o.preimage continuous_subtype_val).isClosed_compl
  have hBcl : IsClosed B := by
    have hBeq : B = (Subtype.val ⁻¹' U₂)ᶜ := by
      ext x
      constructor
      · intro hx hmem
        exact hx (by rw [hW₂eq]; exact ⟨hmem, x.2⟩)
      · intro hx hmem
        have h2 : (x : ℝ × ℝ) ∈ U₂ ∩ S := by rw [← hW₂eq]; exact hmem
        exact hx h2.1
    rw [hBeq]; exact (hU₂o.preimage continuous_subtype_val).isClosed_compl
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    have hxS : (x : ℝ × ℝ) ∈ S := x.2
    have hmem : (x : ℝ × ℝ) ∈ W₁ ∪ W₂ := by rw [hcov]; exact hxS
    rcases hmem with h | h
    · exact hxA h
    · exact hxB h
  have hAB : A ⊆ Bᶜ := fun x hx hxB => (Set.disjoint_left.mp hdisj hx) hxB
  have hBA : B ⊆ Aᶜ := fun x hx hxA => (Set.disjoint_left.mp hdisj hxA) hx
  -- T-invariance of `U = W₁ ∩ W₂`
  have hUper : ∀ q : ℝ × ℝ, q ∈ W₁ ∩ W₂ ↔ Tm p q ∈ W₁ ∩ W₂ := by
    intro q
    refine ⟨fun h => ⟨(hper₁ q).mp h.1, (hper₂ q).mp h.2⟩,
      fun h => ⟨(hper₁ q).mpr h.1, (hper₂ q).mpr h.2⟩⟩
  -- (★) no point of `U` is joined to a nonzero translate of itself
  have hstar : ∀ q : ℝ × ℝ, q ∈ W₁ ∩ W₂ → ∀ n : ℤ, n ≠ 0 →
      ¬ JoinedIn (W₁ ∩ W₂) (Tk p n q) q := by
    intro q hq n hn hJ
    have hJ' : JoinedIn (W₁ ∩ W₂) q (Tk p n q) := hJ.symm
    obtain ⟨γ, hγ⟩ := hJ'
    have hγ1 : γ 1 = ((γ 0).1 + (n : ℝ) * p, (γ 0).2) := by
      rw [γ.target, γ.source]
      rfl
    have hUsub : W₁ ∩ W₂ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} := fun q hq => hsub₁ hq.1
    obtain ⟨z, hz, hJz⟩ :=
      exists_translate_path_of_loop_winding hp hab hUsub hUper hγ hn hγ1
    exact hcon' z hz.1 hz.2 hJz
  -- the sheet index on `U`
  obtain ⟨ind, hind_eq, hind_inv⟩ := exists_sheet_index_joinedIn (p := p) hUper hstar
  -- the membership helpers
  have hTmS : ∀ x : ↥S, Tm p (x : ℝ × ℝ) ∈ S := fun x => x.2
  have helt : ∀ x : ↥S, (x : ℝ × ℝ) ∈ W₁ → Tm p (x : ℝ × ℝ) ∈ W₁ :=
    fun x hx => (hper₁ (x : ℝ × ℝ)).mp hx
  have helt₂ : ∀ x : ↥S, (x : ℝ × ℝ) ∈ W₂ → Tm p (x : ℝ × ℝ) ∈ W₂ :=
    fun x hx => (hper₂ (x : ℝ × ℝ)).mp hx
  have hAsub : ∀ x : ↥S, (x : ℝ × ℝ) ∈ W₁ → x ∉ A := fun x hx hxA => hxA hx
  have hBsub : ∀ x : ↥S, (x : ℝ × ℝ) ∈ W₂ → x ∉ B := fun x hx hxB => hxB hx
  -- the two closed pieces are exactly the complements
  have hAc : Aᶜ = {x : ↥S | (x : ℝ × ℝ) ∈ W₁} := by
    ext x; simp only [Set.mem_compl_iff, hAdef, Set.mem_setOf_eq, not_not]
  have hBc : Bᶜ = {x : ↥S | (x : ℝ × ℝ) ∈ W₂} := by
    ext x; simp only [Set.mem_compl_iff, hBdef, Set.mem_setOf_eq, not_not]
  -- the `T`-action on `↥S`
  have hTmS : ∀ x : ↥S, Tm p (x : ℝ × ℝ) ∈ S := fun x => x.2
  set Tx : ↥S → ↥S := fun x => ⟨Tm p (x : ℝ × ℝ), hTmS x⟩ with hTxdef
  have hTx_A : ∀ x : ↥S, x ∈ Aᶜ → Tx x ∈ Aᶜ := by
    intro x hx
    have h1 : (x : ℝ × ℝ) ∈ W₁ := by
      by_contra hc
      exact ((Set.mem_compl_iff A _).mp hx) (by simpa [hAdef] using hc)
    rw [Set.mem_compl_iff]
    intro hmem
    exact hmem ((hper₁ (x : ℝ × ℝ)).mp h1)
  have hTx_B : ∀ x : ↥S, x ∈ Bᶜ → Tx x ∈ Bᶜ := by
    intro x hx
    have h1 : (x : ℝ × ℝ) ∈ W₂ := by
      by_contra hc
      exact ((Set.mem_compl_iff B _).mp hx) (by simpa [hBdef] using hc)
    rw [Set.mem_compl_iff]
    intro hmem
    exact hmem ((hper₂ (x : ℝ × ℝ)).mp h1)
  -- the decomposition function
  set hBig : ↥((A ∪ B)ᶜ : Set ↥S) → ℤ := fun x => ind (((x : ↥S) : ℝ × ℝ)) with hBigdef
  have hBig_mem : ∀ x : ↥((A ∪ B)ᶜ : Set ↥S), (((x : ↥S) : ℝ × ℝ)) ∈ W₁ ∩ W₂ := by
    intro x
    have hx : (x : ↥S) ∉ A ∪ B := (Set.mem_compl_iff (A ∪ B) _).mp x.2
    refine ⟨?_, ?_⟩
    · by_contra h
      exact hx (Or.inl (by simpa [hAdef] using h))
    · by_contra h
      exact hx (Or.inr (by simpa [hBdef] using h))
  haveI : LocallyPathConnectedSpace ↥((A ∪ B)ᶜ : Set ↥S) :=
    ((hAcl.union hBcl).isOpen_compl).locallyPathConnectedSpace
  have hBig_loc : IsLocallyConstant hBig := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨s, ⟨hsmem, hspc⟩, -⟩ := ((path_connected_basis x).mem_iff).mp (Filter.univ_mem)
    filter_upwards [hsmem] with y hy
    have hjoin : JoinedIn s x y := hspc.joinedIn x (mem_of_mem_nhds hsmem) y hy
    obtain ⟨γ, hγ⟩ := hjoin
    have hJ : JoinedIn (W₁ ∩ W₂) (((x : ↥S) : ℝ × ℝ)) (((y : ↥S) : ℝ × ℝ)) := by
      let F : ↑(Set.Icc (0:ℝ) 1) → ℝ × ℝ := fun t => (((γ t : ↥S)) : ℝ × ℝ)
      have hFc : Continuous F :=
        continuous_subtype_val.comp (continuous_subtype_val.comp γ.continuous)
      refine ⟨⟨⟨F, hFc⟩, ?_, ?_⟩, fun t => hBig_mem (γ t)⟩
      · exact congrArg (fun z : ↥((A ∪ B)ᶜ : Set ↥S) => (((z : ↥S)) : ℝ × ℝ)) γ.source
      · exact congrArg (fun z : ↥((A ∪ B)ᶜ : Set ↥S) => (((z : ↥S)) : ℝ × ℝ)) γ.target
    exact (hind_inv _ _ (hBig_mem x) (hBig_mem y) hJ).symm
  obtain ⟨f, g, hflc, hglc, hkey⟩ :=
    Commons.Topology.Jordan.ClosedDisjoint.QD.exists_decomposition hmono hBig ((hAcl.union hBcl).isOpen_compl)
      (fun z => (IsLocallyConstant.iff_continuous hBig).mp hBig_loc |>.continuousAt)
      hAcl hBcl hAB hBA
  -- the decomposition, in the canonical form
  have hdec : ∀ (x : ↥S) (hx : x ∈ (A ∪ B)ᶜ),
      ind (x : ℝ × ℝ)
        = g ⟨x, fun h => hx (Or.inr h)⟩ - f ⟨x, fun h => hx (Or.inl h)⟩ := by
    intro x hx
    have h := hkey x hx
    simpa [hBigdef] using h
  have hdec_T : ∀ (x : ↥S) (hx : Tx x ∈ (A ∪ B)ᶜ),
      ind (Tm p (x : ℝ × ℝ))
        = g ⟨Tx x, fun h => hx (Or.inr h)⟩ - f ⟨Tx x, fun h => hx (Or.inl h)⟩ := by
    intro x hx
    have h := hkey (Tx x) hx
    simpa [hBigdef, hTxdef] using h
  -- membership of `Tx x` in `(A ∪ B)ᶜ` from the T-invariance
  have hTx_compl : ∀ x : ↥S, x ∈ (A ∪ B)ᶜ → Tx x ∈ (A ∪ B)ᶜ := by
    intro x hx
    have hxT : Tm p (x : ℝ × ℝ) ∈ W₁ ∩ W₂ := (hUper _).mp (hBig_mem ⟨x, hx⟩)
    intro hmem
    rcases hmem with h | h
    · exact h (by simpa [hTxdef] using hxT.1)
    · exact h (by simpa [hTxdef] using hxT.2)
  -- the two branches
  set Φ : ↥S → ℤ := fun x => if h : x ∈ Aᶜ then f ⟨Tx x, hTx_A x h⟩ - f ⟨x, h⟩ else 0 with hΦdef
  set Ψ : ↥S → ℤ := fun x => if h : x ∈ Bᶜ then g ⟨Tx x, hTx_B x h⟩ - g ⟨x, h⟩ - 1 else 0 with hΨdef
  have hΦval : ∀ (x : ↥S) (hx : x ∈ Aᶜ), Φ x = f ⟨Tx x, hTx_A x hx⟩ - f ⟨x, hx⟩ := by
    intro x hx; rw [hΦdef]; simp only [dif_pos hx]
  have hΨval : ∀ (x : ↥S) (hx : x ∈ Bᶜ), Ψ x = g ⟨Tx x, hTx_B x hx⟩ - g ⟨x, hx⟩ - 1 := by
    intro x hx; rw [hΨdef]; simp only [dif_pos hx]
  -- the two branches agree on `U = Aᶜ ∩ Bᶜ`
  have hAgree : ∀ (x : ↥S) (hx : x ∈ Aᶜ) (hy : x ∈ Bᶜ), Φ x = Ψ x := by
    intro x hx hy
    have hxU : x ∈ (A ∪ B)ᶜ := fun h => h.elim hx hy
    have hxT : Tx x ∈ (A ∪ B)ᶜ := fun h => h.elim (hTx_A x hx) (hTx_B x hy)
    have h1 : ind (x : ℝ × ℝ) = g ⟨x, hy⟩ - f ⟨x, hx⟩ := by
      have h := hdec x hxU
      rw [show (⟨x, fun h => hxU (Or.inr h)⟩ : ↥(Bᶜ)) = ⟨x, hy⟩ from Subtype.ext rfl,
        show (⟨x, fun h => hxU (Or.inl h)⟩ : ↥(Aᶜ)) = ⟨x, hx⟩ from Subtype.ext rfl] at h
      exact h
    have h2 : ind (Tm p (x : ℝ × ℝ)) = g ⟨Tx x, hTx_B x hy⟩ - f ⟨Tx x, hTx_A x hx⟩ := by
      have h := hdec_T x (hTx_compl x hxU)
      rw [show (⟨Tx x, fun h => (hTx_compl x hxU) (Or.inr h)⟩ : ↥(Bᶜ)) = ⟨Tx x, hTx_B x hy⟩
            from Subtype.ext rfl,
        show (⟨Tx x, fun h => (hTx_compl x hxU) (Or.inl h)⟩ : ↥(Aᶜ)) = ⟨Tx x, hTx_A x hx⟩
            from Subtype.ext rfl] at h
      exact h
    have h3 : ind (Tm p (x : ℝ × ℝ)) = ind (x : ℝ × ℝ) + 1 :=
      hind_eq _ (hBig_mem ⟨x, hxU⟩)
    rw [hΦval x hx, hΨval x hy]
    omega
  -- Θ
  set Θ : ↥S → ℤ := fun x => if x ∈ Aᶜ then Φ x else Ψ x with hΘdef
  have hΘ_A : ∀ (x : ↥S) (hx : x ∈ Aᶜ), Θ x = Φ x := by
    intro x hx; rw [hΘdef]; simp only [if_pos hx]
  have hΘ_B : ∀ x : ↥S, x ∉ Aᶜ → Θ x = Ψ x := by
    intro x hx; rw [hΘdef]; simp only [if_neg hx]
  -- Θ agrees with Ψ on `Bᶜ`
  have hΘ_eq_Ψ : ∀ (x : ↥S) (hx : x ∈ Bᶜ), Θ x = Ψ x := by
    intro x hx
    by_cases hA : x ∈ Aᶜ
    · rw [hΘ_A x hA, hAgree x hA hx]
    · rw [hΘ_B x hA]
  -- continuity of `Tx` on the subtypes
  have hTx_cont : Continuous fun z : ↥(Aᶜ) => Tx (z : ↥S) := by
    refine Continuous.subtype_mk ?_ _
    show Continuous fun z : ↥(Aᶜ) => Tm p (((z : ↥S)) : ℝ × ℝ)
    exact (continuous_Tm p).comp (continuous_subtype_val.comp continuous_subtype_val)
  have hTx_contB : Continuous fun z : ↥(Bᶜ) => Tx (z : ↥S) := by
    refine Continuous.subtype_mk ?_ _
    show Continuous fun z : ↥(Bᶜ) => Tm p (((z : ↥S)) : ℝ × ℝ)
    exact (continuous_Tm p).comp (continuous_subtype_val.comp continuous_subtype_val)
  have hΦ_locA : IsLocallyConstant (fun z : ↥(Aᶜ) => Φ (z : ↥S)) := by
    have hEq : (fun z : ↥(Aᶜ) => Φ (z : ↥S))
        = fun z : ↥(Aᶜ) => f (⟨Tx (z : ↥S), hTx_A _ z.2⟩) - f z := by
      funext z
      exact hΦval _ z.2
    rw [hEq]
    exact IsLocallyConstant.sub
      (IsLocallyConstant.comp_continuous hflc (hTx_cont.subtype_mk (fun z => hTx_A _ z.2))) hflc
  have hΨ_locB : IsLocallyConstant (fun z : ↥(Bᶜ) => Ψ (z : ↥S)) := by
    have hEq : (fun z : ↥(Bᶜ) => Ψ (z : ↥S))
        = fun z : ↥(Bᶜ) => (g (⟨Tx (z : ↥S), hTx_B _ z.2⟩) - g z) - 1 := by
      funext z
      rw [hΨval _ z.2]
    rw [hEq]
    exact IsLocallyConstant.sub
      (IsLocallyConstant.sub
        (IsLocallyConstant.comp_continuous hglc (hTx_contB.subtype_mk (fun z => hTx_B _ z.2))) hglc)
      (IsLocallyConstant.const 1)
  -- Θ is locally constant
  have hΘlc : IsLocallyConstant Θ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hA : x ∈ Aᶜ
    · have hnb : (Aᶜ : Set ↥S) ∈ nhds x := hAcl.isOpen_compl.mem_nhds hA
      have hev := eventually_subtype_eq (φ := fun z : ↥(Aᶜ) => Φ (z : ↥S)) hΦ_locA ⟨x, hA⟩
      filter_upwards [hnb, hev] with y hy hconst
      rw [hΘ_A x hA, hΘ_A y hy]
      exact hconst hy
    · have hxA : x ∈ A := by by_contra h; exact hA (by simpa using h)
      have hB : x ∈ Bᶜ := hAB hxA
      have hnb : (Bᶜ : Set ↥S) ∈ nhds x := hBcl.isOpen_compl.mem_nhds hB
      have hev := eventually_subtype_eq (φ := fun z : ↥(Bᶜ) => Ψ (z : ↥S)) hΨ_locB ⟨x, hB⟩
      filter_upwards [hnb, hev] with y hy hconst
      rw [hΘ_eq_Ψ x hB, hΘ_eq_Ψ y hy]
      exact hconst hy
  -- Θ is constant
  have hΘconst : ∀ x y : ↥S, Θ x = Θ y := fun x y =>
    hΘlc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ x) (mem_univ y)
  -- evaluation at `z₂`
  obtain ⟨z₂, hz₂W₂, hJ₂⟩ := hne₂
  have hz₂S : z₂ ∈ S := hW₂S hz₂W₂
  have hz₂T : Tm p z₂ ∈ W₂ := (hper₂ z₂).mp hz₂W₂
  have hz₂TS : Tm p z₂ ∈ S := hW₂S hz₂T
  have hz₂B : (⟨z₂, hz₂S⟩ : ↥S) ∈ Bᶜ := by rw [hBc]; exact hz₂W₂
  have hz₂TB : (⟨Tm p z₂, hz₂TS⟩ : ↥S) ∈ Bᶜ := by rw [hBc]; exact hz₂T
  have hjoinB : JoinedIn (Bᶜ : Set ↥S) (⟨z₂, hz₂S⟩ : ↥S) (⟨Tm p z₂, hz₂TS⟩ : ↥S) := by
    have h := joinedIn_subtype_of_joinedIn (S := S) (W := W₂) hW₂S hz₂W₂ hz₂T hJ₂
    rwa [← hBc] at h
  have hgz : g ⟨⟨Tm p z₂, hz₂TS⟩, hz₂TB⟩ = g ⟨⟨z₂, hz₂S⟩, hz₂B⟩ :=
    (Commons.Topology.Jordan.ClosedDisjoint.QD.isLocallyConstant_eq_of_joinedIn hglc hjoinB).symm
  have hΘz₂ : Θ ⟨z₂, hz₂S⟩ = -1 := by
    rw [hΘ_eq_Ψ _ hz₂B, hΨval _ hz₂B]
    have e : (⟨Tx ⟨z₂, hz₂S⟩, hTx_B ⟨z₂, hz₂S⟩ hz₂B⟩ : ↥(Bᶜ))
        = (⟨⟨Tm p z₂, hz₂TS⟩, hz₂TB⟩ : ↥(Bᶜ)) := Subtype.ext rfl
    rw [e, hgz]
    ring
  -- evaluation at `z₁`
  obtain ⟨z₁, hz₁W₁, hJ₁⟩ := hne₁
  have hz₁S : z₁ ∈ S := hW₁S hz₁W₁
  have hz₁T : Tm p z₁ ∈ W₁ := (hper₁ z₁).mp hz₁W₁
  have hz₁TS : Tm p z₁ ∈ S := hW₁S hz₁T
  have hz₁A : (⟨z₁, hz₁S⟩ : ↥S) ∈ Aᶜ := by rw [hAc]; exact hz₁W₁
  have hz₁TA : (⟨Tm p z₁, hz₁TS⟩ : ↥S) ∈ Aᶜ := by rw [hAc]; exact hz₁T
  have hjoinA : JoinedIn (Aᶜ : Set ↥S) (⟨z₁, hz₁S⟩ : ↥S) (⟨Tm p z₁, hz₁TS⟩ : ↥S) := by
    have h := joinedIn_subtype_of_joinedIn (S := S) (W := W₁) hW₁S hz₁W₁ hz₁T hJ₁
    rwa [← hAc] at h
  have hfz : f ⟨⟨Tm p z₁, hz₁TS⟩, hz₁TA⟩ = f ⟨⟨z₁, hz₁S⟩, hz₁A⟩ :=
    (Commons.Topology.Jordan.ClosedDisjoint.QD.isLocallyConstant_eq_of_joinedIn hflc hjoinA).symm
  have hΘz₁ : Θ ⟨z₁, hz₁S⟩ = 0 := by
    rw [hΘ_A _ hz₁A, hΦval _ hz₁A]
    have e : (⟨Tx ⟨z₁, hz₁S⟩, hTx_A ⟨z₁, hz₁S⟩ hz₁A⟩ : ↥(Aᶜ))
        = (⟨⟨Tm p z₁, hz₁TS⟩, hz₁TA⟩ : ↥(Aᶜ)) := Subtype.ext rfl
    rw [e, hfz]
    ring
  -- contradiction
  have hcontr := hΘconst ⟨z₁, hz₁S⟩ ⟨z₂, hz₂S⟩
  rw [hΘz₁, hΘz₂] at hcontr
  norm_num at hcontr


/-- **The crux (Denne, *Alternating quadrisecants of knots*, `prop:homology`), in strip form.**

Two `T`-invariant sets `W₁, W₂` that are open in the closed strip `S = {a ≤ ·.2 ≤ b}`
(`Wᵢ = Uᵢ ∩ S` with `Uᵢ` open in `ℝ²`), that cover `S`, and that each carry a *translate path*
(a path from a point to its own translate `q ↦ (q.1 + p, q.2)`), must have a point carrying a
translate path inside their intersection `W₁ ∩ W₂`.

This is the *excisive-cover* form of Denne's Mayer–Vietoris argument, and it is a genuine theorem.

**Warning (recorded after a machine-checked refutation).**  An earlier revision of this file obtained
this statement from two "annulus duality" lemmas, namely

* "`K` closed `T`-invariant in the strip with no preconnected subset meeting both boundary lines
  implies that the complement carries a translate path", and
* "a free left–right path of the fundamental box implies a translate path in the strip".

Both of those are **false**, so the derivation was unsound (the counterexample is machine-checked,
placeholder-free and axiom-clean, in
`Submission/Work/Topology/Strip/strip_path_to_translate_of_no_spanning_refutation.lean`: for a
staircase profile `f` with `f → -∞` at `0⁺` and `f → +∞` at `1⁻`, the closed `1`-periodic set `K f`
formed by the two horizontal lines together with the graphs of `y ↦ f y + m` over `0 < y < 1` has no
preconnected subset meeting both boundary lines, yet `{0 ≤ ·.2 ≤ 1} ∖ K f` carries no translate
path).  The walls of `K f` escape to `x = ±∞`, i.e. their heights accumulate at the boundary lines
without the walls meeting them — exactly the phenomenon that the (true) blocking lemma
`Commons.Topology.Strip.wall_blocks_translate_path` cannot see.  What excludes that configuration here
is the excisive hypothesis: the two obstacles are the complementary closed pieces of one closed
`T`-invariant set. -/
theorem ess_inter_of_ess_of_cover_instrip {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {W₁ W₂ : Set (ℝ × ℝ)}
    (hsub₁ : W₁ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hsub₂ : W₂ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₁ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₁ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₂ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₂ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hper₁ : ∀ q : ℝ × ℝ, q ∈ W₁ ↔ (q.1 + p, q.2) ∈ W₁)
    (hper₂ : ∀ q : ℝ × ℝ, q ∈ W₂ ↔ (q.1 + p, q.2) ∈ W₂)
    (hcov : W₁ ∪ W₂ = {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hne₁ : ∃ z : ℝ × ℝ, z ∈ W₁ ∧ JoinedIn W₁ z (z.1 + p, z.2))
    (hne₂ : ∃ z : ℝ × ℝ, z ∈ W₂ ∧ JoinedIn W₂ z (z.1 + p, z.2)) :
    ∃ z : ℝ × ℝ, z ∈ W₁ ∧ z ∈ W₂ ∧ JoinedIn W₁ z (z.1 + p, z.2) ∧
      JoinedIn W₂ z (z.1 + p, z.2) := by
  -- proved directly by the two-set Mayer--Vietoris decomposition; see `crux_via_decomposition`.
  obtain ⟨z, hz₁, hz₂, hJ⟩ :=
    crux_via_decomposition hp hab hsub₁ hsub₂ hopen₁ hopen₂ hper₁ hper₂ hcov hne₁ hne₂
  exact ⟨z, hz₁, hz₂, hJ.mono Set.inter_subset_left, hJ.mono Set.inter_subset_right⟩

theorem exists_translate_path_of_ess_of_cover {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {W₁ W₂ : Set (ℝ × ℝ)}
    (hsub₁ : W₁ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hsub₂ : W₂ ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₁ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₁ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hopen₂ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ W₂ = U ∩ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hper₁ : ∀ q : ℝ × ℝ, q ∈ W₁ ↔ (q.1 + p, q.2) ∈ W₁)
    (hper₂ : ∀ q : ℝ × ℝ, q ∈ W₂ ↔ (q.1 + p, q.2) ∈ W₂)
    (hcov : W₁ ∪ W₂ = {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hne₁ : ∃ z : ℝ × ℝ, z ∈ W₁ ∧ JoinedIn W₁ z (z.1 + p, z.2))
    (hne₂ : ∃ z : ℝ × ℝ, z ∈ W₂ ∧ JoinedIn W₂ z (z.1 + p, z.2)) :
    ∃ z : ℝ × ℝ, z ∈ W₁ ∩ W₂ ∧ JoinedIn (W₁ ∩ W₂) z (z.1 + p, z.2) := by
  classical
  obtain ⟨q, hqW₁, hqW₂, hJ₁, hJ₂⟩ :=
    ess_inter_of_ess_of_cover_instrip hp hab hsub₁ hsub₂ hopen₁ hopen₂ hper₁ hper₂ hcov hne₁ hne₂
  set S : Set (ℝ × ℝ) := {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} with hSdef
  have hconv : Convex ℝ S := by
    rw [hSdef]
    have h : {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b} = Set.univ ×ˢ Set.Icc a b := by
      ext q; simp [Set.mem_Icc]
    rw [h]; exact convex_univ.prod (convex_Icc a b)
  obtain ⟨U₁, hU₁o, hU₁eq⟩ := hopen₁
  obtain ⟨U₂, hU₂o, hU₂eq⟩ := hopen₂
  have hqS : q ∈ S := hsub₁ hqW₁
  have hTqW₁ : (q.1 + p, q.2) ∈ W₁ := (hper₁ q).mp hqW₁
  have hTqW₂ : (q.1 + p, q.2) ∈ W₂ := (hper₂ q).mp hqW₂
  have hTqS : (q.1 + p, q.2) ∈ S := hsub₁ hTqW₁
  -- For `x : ↥S`, membership in `W₁`/`W₂` agrees with membership in `U₁`/`U₂`.
  have hW₁U₁ : ∀ x : ↥S, ((x : ℝ × ℝ) ∈ W₁ ↔ (x : ℝ × ℝ) ∈ U₁) := by
    intro x; rw [hU₁eq]; exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  have hW₂U₂ : ∀ x : ↥S, ((x : ℝ × ℝ) ∈ W₂ ↔ (x : ℝ × ℝ) ∈ U₂) := by
    intro x; rw [hU₂eq]; exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  haveI : ContractibleSpace ↥S :=
    hconv.contractibleSpace ⟨((0 : ℝ), (a + b) / 2), by
      rw [hSdef]; exact ⟨by linarith, by linarith⟩⟩
  haveI : LocallyPathConnectedSpace ↥S := hconv.locallyPathConnectedSpace
  haveI : ConnectedSpace ↥S := inferInstance
  set A : Set ↥S := ((Subtype.val) ⁻¹' U₁)ᶜ with hAdef
  set B : Set ↥S := ((Subtype.val) ⁻¹' U₂)ᶜ with hBdef
  have hAclosed : IsClosed A := (hU₁o.preimage continuous_subtype_val).isClosed_compl
  have hBclosed : IsClosed B := (hU₂o.preimage continuous_subtype_val).isClosed_compl
  have hAc : Aᶜ = (Subtype.val) ⁻¹' U₁ := compl_compl _
  have hBc : Bᶜ = (Subtype.val) ⁻¹' U₂ := compl_compl _
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    rw [hAdef, Set.mem_compl_iff, Set.mem_preimage] at hxA
    rw [hBdef, Set.mem_compl_iff, Set.mem_preimage] at hxB
    have hxW : (x : ℝ × ℝ) ∈ W₁ ∪ W₂ := by rw [hcov]; exact x.2
    exact hxW.elim (fun h => hxA ((hW₁U₁ x).mp h)) (fun h => hxB ((hW₂U₂ x).mp h))
  have hx₀ : (⟨q, hqS⟩ : ↥S) ∉ A ∪ B := by
    rintro (h | h)
    · rw [hAdef, Set.mem_compl_iff, Set.mem_preimage] at h
      exact h ((hW₁U₁ ⟨q, hqS⟩).mp hqW₁)
    · rw [hBdef, Set.mem_compl_iff, Set.mem_preimage] at h
      exact h ((hW₂U₂ ⟨q, hqS⟩).mp hqW₂)
  have hy₀ : (⟨(q.1 + p, q.2), hTqS⟩ : ↥S) ∉ A ∪ B := by
    rintro (h | h)
    · rw [hAdef, Set.mem_compl_iff, Set.mem_preimage] at h
      exact h ((hW₁U₁ ⟨_, hTqS⟩).mp hTqW₁)
    · rw [hBdef, Set.mem_compl_iff, Set.mem_preimage] at h
      exact h ((hW₂U₂ ⟨_, hTqS⟩).mp hTqW₂)
  have hlift₁ : JoinedIn ((Subtype.val) ⁻¹' W₁) (⟨q, hqS⟩ : ↥S)
      (⟨(q.1 + p, q.2), hTqS⟩ : ↥S) := by
    obtain ⟨γ, hγ⟩ := hJ₁
    exact ⟨{ toFun := fun t => ⟨γ t, hsub₁ (hγ t)⟩
             continuous_toFun := by fun_prop
             source' := by apply Subtype.ext; exact γ.source
             target' := by apply Subtype.ext; exact γ.target }, fun t => hγ t⟩
  have hlift₂ : JoinedIn ((Subtype.val) ⁻¹' W₂) (⟨q, hqS⟩ : ↥S)
      (⟨(q.1 + p, q.2), hTqS⟩ : ↥S) := by
    obtain ⟨γ, hγ⟩ := hJ₂
    exact ⟨{ toFun := fun t => ⟨γ t, hsub₂ (hγ t)⟩
             continuous_toFun := by fun_prop
             source' := by apply Subtype.ext; exact γ.source
             target' := by apply Subtype.ext; exact γ.target }, fun t => hγ t⟩
  have hA' : JoinedIn Aᶜ (⟨q, hqS⟩ : ↥S) (⟨(q.1 + p, q.2), hTqS⟩ : ↥S) := by
    rw [hAc]; exact hlift₁.mono (fun x hx => (hW₁U₁ x).mp hx)
  have hB' : JoinedIn Bᶜ (⟨q, hqS⟩ : ↥S) (⟨(q.1 + p, q.2), hTqS⟩ : ↥S) := by
    rw [hBc]; exact hlift₂.mono (fun x hx => (hW₂U₂ x).mp hx)
  have hmono : ∀ z : ↥S, Subsingleton (FundamentalGroup ↥S z) := fun _ => inferInstance
  have hmain := Commons.Topology.Jordan.two_disjoint_closed_not_separating hmono
    hAclosed hBclosed hdisj hx₀ hy₀ hA' hB'
  have hkey : (A ∪ B)ᶜ = (Subtype.val) ⁻¹' (W₁ ∩ W₂) := by
    rw [Set.compl_union, hAc, hBc]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨fun h => ⟨(hW₁U₁ x).mpr h.1, (hW₂U₂ x).mpr h.2⟩,
           fun h => ⟨(hW₁U₁ x).mp h.1, (hW₂U₂ x).mp h.2⟩⟩
  obtain ⟨γ, hγ⟩ := hmain
  rw [hkey] at hγ
  exact ⟨q, ⟨hqW₁, hqW₂⟩, ⟨γ.map continuous_subtype_val, fun t => hγ t⟩⟩

end Commons.Topology.Strip
