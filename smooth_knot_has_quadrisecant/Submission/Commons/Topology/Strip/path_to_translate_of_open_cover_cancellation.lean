import Mathlib
import Submission.Commons.Topology.Covering.section_of_monodromy_eq_self_weak
import Submission.Commons.Topology.Jordan.two_disjoint_closed_not_separating
import Submission.Commons.Topology.Strip.barrier_bottom_top_of_no_left_right
import Submission.Commons.Topology.Strip.annulus_essential_intersection

open Set

namespace Commons.Topology.Strip

/-- **A covering of a simply connected, locally path connected space admits a section.**

Since `π₁` of a simply connected space is trivial, the monodromy of any covering is trivial,
so `Commons.Topology.Covering.section_of_monodromy_eq_self_weak` produces a global section. -/
theorem exists_section_of_isCoveringMap {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X] {p : E → X}
    (hp : IsCoveringMap p) (e : E) : ∃ σ : C(X, E), ∀ x, p (σ x) = x := by
  have h : ∀ γ : FundamentalGroup X (p e), hp.monodromy γ ⟨e, rfl⟩ = ⟨e, rfl⟩ := by
    intro γ
    have h1 : γ = Path.Homotopic.Quotient.refl (p e) := Subsingleton.elim _ _
    rw [h1]
    exact congrFun (congrArg (fun F : p ⁻¹' {p e} → p ⁻¹' {p e} => F)
      (hp.monodromy_refl (x := p e))) ⟨e, rfl⟩
  obtain ⟨σ, -, hσ⟩ := Commons.Topology.Covering.section_of_monodromy_eq_self_weak hp e h
  exact ⟨σ, hσ⟩

/-! ## The open horizontal strip

We record the basic topological facts about the open strip `S = {q : ℝ × ℝ | a < q.2 ∧ q.2 < b}`
used in the reduction: it is convex, hence connected, locally path connected and simply
connected. -/

/-- The open horizontal strip `{q : ℝ × ℝ | a < q.2 ∧ q.2 < b}`. -/
def strip (a b : ℝ) : Set (ℝ × ℝ) := {q : ℝ × ℝ | a < q.2 ∧ q.2 < b}

lemma strip_convex (a b : ℝ) : Convex ℝ (strip a b) := by
  have h1 : strip a b = (univ : Set ℝ) ×ˢ Set.Ioo a b := by
    ext q; simp [strip]
  rw [h1]
  exact Convex.prod convex_univ (convex_Ioo a b)

lemma strip_ne {a b : ℝ} (hab : a < b) : (strip a b).Nonempty :=
  ⟨(0, (a + b) / 2), by simp only [strip, Set.mem_ofPred_eq]; constructor <;> linarith⟩

lemma strip_connectedSpace {a b : ℝ} (hab : a < b) : ConnectedSpace ↥(strip a b) :=
  isConnected_iff_connectedSpace.mp ((strip_convex a b).isConnected (strip_ne hab))

lemma strip_locallyPathConnectedSpace (a b : ℝ) : LocallyPathConnectedSpace ↥(strip a b) :=
  (strip_convex a b).locallyPathConnectedSpace

lemma strip_simplyConnectedSpace {a b : ℝ} (hab : a < b) : SimplyConnectedSpace ↥(strip a b) :=
  haveI : ContractibleSpace ↥(strip a b) := (strip_convex a b).contractibleSpace (strip_ne hab)
  inferInstance

/-- **Level saturation.**  A closed `T`-invariant subset of the open strip whose complement
contains no `T`-crossing meets every horizontal level of the strip (the whole circle at a level
would otherwise be a connected `T`-invariant subset of the complement). -/
lemma exists_snd_mem_of_no_crossing {p a b : ℝ} {F : Set (ℝ × ℝ)}
    (hF : IsClosed F)
    (hper : ∀ q : ℝ × ℝ, q ∈ F ↔ (q.1 + p, q.2) ∈ F)
    (hsub : F ⊆ strip a b)
    (hno : ∀ z : ℝ × ℝ, z ∈ (strip a b \ F) →
      ¬ JoinedIn (strip a b \ F) z (z.1 + p, z.2)) :
    ∀ y : ℝ, a < y → y < b → ∃ x : ℝ, (x, y) ∈ F := by
  intro y hay hyb
  by_contra hcon
  push Not at hcon
  have hzU : ((0 : ℝ), y) ∈ (strip a b \ F) := ⟨⟨hay, hyb⟩, hcon 0⟩
  have hpath : JoinedIn (strip a b \ F) ((0 : ℝ), y) ((0 : ℝ) + p, y) := by
    refine ⟨{ toContinuousMap :=
                ⟨fun t : Set.Icc (0 : ℝ) 1 => ((t : ℝ) * p, y), by fun_prop⟩,
              source' := by simp, target' := by simp }, ?_⟩
    intro t
    exact ⟨⟨hay, hyb⟩, hcon ((t : ℝ) * p)⟩
  exact hno ((0 : ℝ), y) hzU hpath

/-! ## The cancellation step

The crux of the argument (Denne's Mayer–Vietoris step): if two `T`-invariant open sets covering
the strip each contain a `T`-crossing, then some point of their intersection is joined to its
`T`-translate inside **both** sets.

Equivalently (`Z VA` = union of the connected components `K` of `VA` with `T K = K`, i.e. the
set of points of `VA` joined to their `T`-translate inside `VA`):

* `Z VA ≠ ∅` and `Z VB ≠ ∅` imply `Z (VA ∩ VB) ≠ ∅`;

and since the strip is simply connected, `Z VA ∩ Z VB ⊆ Z (VA ∩ VB)` by the commons lemma
`Commons.Topology.Jordan.two_disjoint_closed_not_separating` (Janiszewski/2-out-of-3), so the
crux is the same statement as "the union of the `T`-fixed components of `VA` and of `VB` have a
common point".  This is precisely Pannwitz–Kuperberg cancellation in the annulus
`S/T`: two open essential subsets covering the annulus have an essential intersection, which
Denne proves by Mayer–Vietoris: the `+1` winding class of the `VA` crossing and the `-1` winding
class of the `VB` crossing cancel in `H₁(annulus) = ℤ`, so exactness produces a class in
`H₁ (VA ∩ VB)` mapping to a generator.

Known partial results towards the crux (not needed for the reduction, recorded for the record):
the "`ζ`-construction" (chain the crossing of `VA`, the crossing of `VB` and a connecting path
to close up a loop in the sheared strip) proves the crux whenever some connecting path from the
`VB`-crossing to the `VA`-crossing can be chosen inside `VA` or inside `VB`.

Ingredients available towards the crux: `exists_leftRight_path_of_closed_compl` (the box
`[0,p] × [a,b]` contains a left–right path avoiding `A ∪ B`), `locallyConstant_eq_of_joinedIn`
and `exists_decomposition_of_open_cover` (the strip form of the commons glued-covering
decomposition: `h = g - f` with `f`, `g` locally constant on `VA`, `VB`).

  **Obstruction to the naive finish.**  With `h := 1_K` the indicator of a component `K` of
`VA ∩ VB`, the two "equivariance" facts are *automatic*: a crossing path `z ~ T z` lies in a
single component of `VA`, and a locally constant `f : VA → ℤ` is constant on components, so
`f z = f (T z)` carries no information about `T`.  Conversely a pair `f, g` that is
`T`-equivariant (`f ∘ T = f`, `g ∘ T = g`) would immediately contradict
`h(K) = 1 ≠ 0 = h(TK)`; but such a pair exists only when `h` itself is `T`-equivariant, and
`1_K` is not (when `K ∩ TK = ∅`).  Hence the finish cannot come from the *statement* of
`exists_decomposition` alone: it must use `h` built from the `T`-action — the winding/sheet
index of `VA ∩ VB`, which satisfies `h(T w) = h(w) + 1` — and then the `+1` crossing of `VA`
and the `−1` crossing of `VB` force `h` to be simultaneously honest and dishonest across the
decomposition.  This is exactly the cancellation of the `+1` and `−1` classes. -/
/-- **Left–right crossing of the box for the complement of a union of two closed sets.**

If `A` and `B` are closed subsets of the open strip `a < q.2 < b`, then the box
`[0,p] × [a,b]` contains a left–right path (from the side `{q.1 = 0}` to the side `{q.1 = p}`)
which avoids `A ∪ B` and stays in the open strip.  This is the contrapositive of the barrier
lemma (`Commons.Topology.Strip.barrier_bottom_top_of_no_left_right`): the closed set
`K = box ∖ (strip ∖ (A ∪ B))` cannot contain a preconnected subset meeting both horizontal sides
of the box, since such a subset would be contained either in the box boundary `box ∖ strip` or in
`A ∪ B ⊆ strip`, and neither alternative is possible.  This is the "left–right half" of the
Mayer–Vietoris engine of the cancellation step. -/
theorem exists_leftRight_path_of_closed_compl {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {A B : Set (ℝ × ℝ)} (hA : IsClosed A) (hB : IsClosed B)
    (hAsub : A ⊆ strip a b) (hBsub : B ⊆ strip a b) :
    ∃ γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ),
      (∀ t, 0 ≤ (γ t).1 ∧ (γ t).1 ≤ p ∧ a < (γ t).2 ∧ (γ t).2 < b) ∧
      (γ 0).1 = 0 ∧ (γ 1).1 = p ∧ ∀ t, γ t ∉ A ∪ B := by
  classical
  set S := strip a b with hS
  set box : Set (ℝ × ℝ) := {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ p ∧ a ≤ q.2 ∧ q.2 ≤ b} with hbox
  set K : Set (ℝ × ℝ) := box ∩ (Sᶜ ∪ (A ∪ B)) with hK
  have hSopen : IsOpen S := by
    rw [hS, strip]
    exact (isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const)
  have hboxclosed : IsClosed box := by
    have hboxeq : box = Set.Icc (0:ℝ) p ×ˢ Set.Icc a b := by
      rw [hbox]; ext q
      simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Icc]
      tauto
    rw [hboxeq]; exact isClosed_Icc.prod isClosed_Icc
  have hKclosed : IsClosed K :=
    hboxclosed.inter (hSopen.isClosed_compl.union (hA.union hB))
  have hKsub : K ⊆ box := Set.inter_subset_left
  by_contra hcon
  have hcon' : ∀ γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ),
      (∀ t, γ t ∈ {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ p ∧ a ≤ q.2 ∧ q.2 ≤ b}) →
      (γ 0 ∈ ({q : ℝ × ℝ | q.1 = 0} : Set (ℝ × ℝ))) →
      (γ 1 ∈ ({q : ℝ × ℝ | q.1 = p} : Set (ℝ × ℝ))) →
      (∀ t, γ t ∉ K) → False := by
    intro γ hγbox h0 h1 hγK
    apply hcon
    refine ⟨γ, ?_, ?_, ?_, ?_⟩
    · intro t
      have ht := hγbox t
      simp only [Set.mem_ofPred_eq] at ht
      have htS : γ t ∈ S := by
        by_contra hc
        exact hγK t (by rw [hK]; exact ⟨ht, Or.inl hc⟩)
      rw [hS, strip] at htS
      simp only [Set.mem_ofPred_eq] at htS
      exact ⟨ht.1, ht.2.1, htS.1, htS.2⟩
    · simpa [Set.mem_ofPred_eq] using h0
    · simpa [Set.mem_ofPred_eq] using h1
    · intro t ht
      have htK := hγK t
      have htbox := hγbox t
      rw [hK, Set.mem_inter_iff, not_and_or] at htK
      rcases htK with h | h
      · exact absurd htbox h
      · rw [Set.mem_union, not_or] at h
        exact h.2 ht
  obtain ⟨C, hCK, hCpc, hCa, hCb⟩ :=
    barrier_bottom_top_of_no_left_right hp hab hKsub hKclosed hcon'
  set K₁ : Set (ℝ × ℝ) := box ∩ Sᶜ with hK₁
  set K₂ : Set (ℝ × ℝ) := box ∩ (A ∪ B) with hK₂
  have hK₁closed : IsClosed K₁ := hboxclosed.inter hSopen.isClosed_compl
  have hK₂closed : IsClosed K₂ := hboxclosed.inter (hA.union hB)
  have hKU : K₁ ∪ K₂ = K := by
    rw [hK₁, hK₂, hK]; ext q
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    tauto
  have hK₁K₂ : K₁ ∩ K₂ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro q ⟨hq1, hq2⟩
    rw [hK₁] at hq1
    rw [hK₂] at hq2
    simp only [Set.mem_inter_iff, Set.mem_compl_iff] at hq1
    simp only [Set.mem_inter_iff] at hq2
    exact hq1.2 (by rcases hq2.2 with h | h; exacts [hAsub h, hBsub h])
  have hKdisj : C ∩ (K₁ ∩ K₂) = ∅ := by rw [hK₁K₂, Set.inter_empty]
  have hCsub : C ⊆ K₁ ∪ K₂ := by rw [hKU]; exact hCK
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hCpc) K₁ K₂ hK₁closed hK₂closed
    hCsub hKdisj with hC1 | hC2
  · have hK₁sub : K₁ ⊆ {q : ℝ × ℝ | q.2 ≤ a} ∪ {q : ℝ × ℝ | b ≤ q.2} := by
      intro q hq
      rw [hK₁] at hq
      have hqS : q ∉ S := hq.2
      rw [hS, strip] at hqS
      simp only [Set.mem_ofPred_eq, not_and, not_lt] at hqS
      by_cases h : q.2 ≤ a
      · exact Or.inl h
      · exact Or.inr (hqS (lt_of_not_ge h))
    have hCsub' : C ⊆ ({q : ℝ × ℝ | q.2 ≤ a}) ∪ ({q : ℝ × ℝ | b ≤ q.2}) :=
      hC1.trans hK₁sub
    have hcl1 : IsClosed ({q : ℝ × ℝ | q.2 ≤ a}) := isClosed_Iic.preimage continuous_snd
    have hcl2 : IsClosed ({q : ℝ × ℝ | b ≤ q.2}) := isClosed_Ici.preimage continuous_snd
    have hdj0 : ({q : ℝ × ℝ | q.2 ≤ a}) ∩ ({q : ℝ × ℝ | b ≤ q.2}) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro q ⟨h1, h2⟩
      simp only [Set.mem_ofPred_eq] at h1 h2
      linarith
    have hdj : C ∩ (({q : ℝ × ℝ | q.2 ≤ a}) ∩ ({q : ℝ × ℝ | b ≤ q.2})) = ∅ := by
      rw [hdj0, Set.inter_empty]
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hCpc) _ _ hcl1 hcl2 hCsub' hdj
      with h | h
    · obtain ⟨c, hcC, hcb⟩ := hCb
      have h1 : c.2 ≤ a := h hcC
      have h2 : c.2 = b := hcb
      linarith
    · obtain ⟨c, hcC, hca⟩ := hCa
      have h1 : b ≤ c.2 := h hcC
      have h2 : c.2 = a := hca
      linarith
  · obtain ⟨c, hcC, hca⟩ := hCa
    have hcK₂ : c ∈ K₂ := hC2 hcC
    rw [hK₂] at hcK₂
    simp only [Set.mem_inter_iff] at hcK₂
    have hcS : c ∈ S := by
      rcases hcK₂.2 with h | h
      · exact hAsub h
      · exact hBsub h
    rw [hS, strip] at hcS
    simp only [Set.mem_ofPred_eq] at hcS hca
    linarith [hcS.1, hca]

/-- A locally constant `ℤ`-valued function on a set is constant along a path (`JoinedIn`)
inside it.  Wrapper around `Commons.Topology.Jordan.ClosedDisjoint.QD.isLocallyConstant_eq_of_joinedIn`. -/
lemma locallyConstant_eq_of_joinedIn {X : Type*} [TopologicalSpace X] {F : Set X} {f : ↥F → ℤ}
    (hf : IsLocallyConstant f) {x y : X} (h : JoinedIn F x y) :
    f ⟨x, h.source_mem⟩ = f ⟨y, h.target_mem⟩ :=
  Commons.Topology.Jordan.ClosedDisjoint.QD.isLocallyConstant_eq_of_joinedIn hf h

/-- **Apex, equal-heights case (`k = 1`).**  The left–right path `(0, y) ~ (p, y)` is itself a
`T`-crossing of `W`.  This is the `k = 1` face of the apex; the remaining (`y ≠ y'`) case is the
geometric obligation. -/
lemma exists_tcrossing_of_equal_height_path {p : ℝ} {W : Set (ℝ × ℝ)} {y : ℝ}
    (h : JoinedIn W (0, y) (p, y)) :
    ∃ z ∈ W, JoinedIn W z (z.1 + p, z.2) := by
  refine ⟨(0, y), h.source_mem, ?_⟩
  simpa using h

/-- **Transport of a locally constant function across a set equality.**  If `s = t` and `f` is
locally constant on `↥s` (with values in `ℤ`), then `f`, reindexed along the canonical
homeomorphism `↥s ≃ₜ ↥t`, is locally constant on `↥t`.  This is the bookkeeping step for
restating a lemma whose subtype is spelled with `↥(Aᶜ)` in the form spelled with the defining
predicate. -/
lemma isLocallyConstant_setCongr {X : Type*} [TopologicalSpace X] {s t : Set X} (h : s = t)
    {f : ↥s → ℤ} (hf : IsLocallyConstant f) :
    IsLocallyConstant (fun x : ↥t => f ((Homeomorph.setCongr h).symm x)) := by
  rw [IsLocallyConstant.iff_continuous]
  exact hf.continuous.comp (Homeomorph.setCongr h).symm.continuous

/-- **The `T`-shift maps a `T`-invariant set onto itself.**  This is the floor of the covering
structure for `W → W/T`: the deck generator `q ↦ (q.1 + p, q.2)` is a bijection of `W`. -/
lemma image_shift_eq_self {p : ℝ} {W : Set (ℝ × ℝ)}
    (hper : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W) :
    (fun q : ℝ × ℝ => (q.1 + p, q.2)) '' W = W := by
  ext q; constructor
  · rintro ⟨q₀, hq₀, rfl⟩; exact (hper q₀).mp hq₀
  · intro hq
    exact ⟨(q.1 - p, q.2), (hper _).mpr (by simpa using hq), by ext <;> simp⟩

/-- **The deck generator as an equivalence of `↥W`.**  The `ℤ`-action on a `T`-invariant `W`: the
translation `q ↦ (q.1 + p, q.2)` with explicit inverse `q ↦ (q.1 - p, q.2)`.  This is the deck
action whose quotient is `W/T`. -/
noncomputable def shiftEquiv {p : ℝ} {W : Set (ℝ × ℝ)}
    (hper : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W) : ↥W ≃ ↥W where
  toFun w := ⟨((w : ℝ × ℝ).1 + p, (w : ℝ × ℝ).2), (hper (w : ℝ × ℝ)).mp w.2⟩
  invFun w := ⟨((w : ℝ × ℝ).1 - p, (w : ℝ × ℝ).2),
    (hper ((w : ℝ × ℝ).1 - p, (w : ℝ × ℝ).2)).mpr (by simpa using w.2)⟩
  left_inv w := by ext <;> simp
  right_inv w := by ext <;> simp

/-- **Bridge between the group power and `Function.iterate`.**  For the deck action,
`(shiftEquiv hper)^n` as a function is the `n`-fold iterate — `Equiv.Perm.coe_pow`. -/
theorem shiftEquiv_coe_pow {p : ℝ} {W : Set (ℝ × ℝ)}
    (hper : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W) (n : ℕ) :
    ⇑((shiftEquiv hper) ^ n) = (⇑(shiftEquiv hper))^[n] :=
  Equiv.Perm.coe_pow _ _

/-- **Iterate law for a shift map.**  If `f : ↥W → ↥W` shifts the first coordinate by `p`, then
its `n`-th iterate shifts by `n·p`.  `Nat` induction; the successor case is
`Function.iterate_succ_apply'` then the hypothesis and the inductive hypothesis, closed by
`push_cast`/`ring_nf`. -/
theorem iterate_snd_of_shift_law {p : ℝ} {W : Set (ℝ × ℝ)}
    (f : ↥W → ↥W)
    (hshift : ∀ w : ↥W, ((f w : ↥W) : ℝ × ℝ) = ((w : ℝ × ℝ).1 + p, (w : ℝ × ℝ).2))
    (n : ℕ) (w : ↥W) :
    ((((f^[n]) w : ↥W) : ℝ × ℝ)) = ((w : ℝ × ℝ).1 + (n : ℝ) * p, (w : ℝ × ℝ).2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [hshift]
      rw [ih]
      push_cast
      ring_nf

/-- **The apex reduces to the normalized period `2π`.**  If the apex holds in the frame of `cov`
(`p = 2π`), it holds for every `p > 0`: the rescaling `s q = (λ·q.1, q.2)` with `λ := 2π/p` is a
continuous bijection with explicit continuous inverse `s' q = ((1/λ)·q.1, q.2)`, and `W' := s '' W`
is `s' ⁻¹' W`, so it is open for free.  `s` carries the `T_p`-action to the `T_{2π}`-action, and a
path in `W'` from `(x, y)` to `(x+2π, y)` pulls back under `s'` to a path in `W` from `s'(x,y)` to
`(s'(x,y).1 + p, y)` — a genuine `T_p`-crossing, because cross-freeness is stated at *equal*
heights; that is the one subtle step. -/
theorem no_unequal_height_of_normalized {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    (hnorm : ∀ {W : Set (ℝ × ℝ)}, IsOpen W → W ⊆ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b} →
      (∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + 2 * Real.pi, q.2) ∈ W) →
      (∀ z : ℝ × ℝ, z ∈ W → ¬ JoinedIn W z (z.1 + 2 * Real.pi, z.2)) →
      ∀ x y y' : ℝ, JoinedIn W (x, y) (x + 2 * Real.pi, y') → y = y')
    {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hsub : W ⊆ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b})
    (hper : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W)
    (hno : ∀ z : ℝ × ℝ, z ∈ W → ¬ JoinedIn W z (z.1 + p, z.2))
    {x y y' : ℝ} (h : JoinedIn W (x, y) (x + p, y')) : y = y' := by
  set lam : ℝ := 2 * Real.pi / p with hlam
  have hlamp : lam * p = 2 * Real.pi := by rw [hlam]; field_simp
  have hpinv : (1 / lam) * (2 * Real.pi) = p := by rw [hlam]; field_simp
  have h1 : (1 / lam) * lam = 1 := by
    rw [hlam]
    have hd : (2 * Real.pi) / p ≠ 0 := by positivity
    field_simp
  set s : ℝ × ℝ → ℝ × ℝ := fun q => (lam * q.1, q.2) with hs
  set s' : ℝ × ℝ → ℝ × ℝ := fun q => ((1 / lam) * q.1, q.2) with hs'
  have hsc : Continuous s := by rw [hs]; fun_prop
  have hs'c : Continuous s' := by rw [hs']; fun_prop
  have hs's : ∀ q : ℝ × ℝ, s' (s q) = q := by
    intro q
    show ((1 / lam) * (lam * q.1), q.2) = (q.1, q.2)
    rw [← mul_assoc, h1, one_mul]
  have hss' : ∀ q : ℝ × ℝ, s (s' q) = q := by
    intro q
    show (lam * ((1 / lam) * q.1), q.2) = (q.1, q.2)
    rw [← mul_assoc, mul_comm lam (1 / lam), h1, one_mul]
  set W' : Set (ℝ × ℝ) := s '' W with hW'
  have hW'eq : W' = s' ⁻¹' W := by
    rw [hW']; ext q; constructor
    · rintro ⟨q₀, hq₀, rfl⟩; rw [Set.mem_preimage, hs's]; exact hq₀
    · intro hq; exact ⟨s' q, hq, hss' q⟩
  have hW'open : IsOpen W' := by rw [hW'eq]; exact hW.preimage hs'c
  have hW'per : ∀ q : ℝ × ℝ, q ∈ W' ↔ (q.1 + 2 * Real.pi, q.2) ∈ W' := by
    intro q
    rw [hW'eq]
    have h2 : s' (q.1 + 2 * Real.pi, q.2) = ((s' q).1 + p, (s' q).2) := by
      rw [hs']
      show ((1 / lam) * (q.1 + 2 * Real.pi), q.2) = ((1 / lam) * q.1 + p, q.2)
      rw [mul_add, hpinv]
    rw [Set.mem_preimage, Set.mem_preimage, h2]
    exact hper (s' q)
  have hW'no : ∀ z : ℝ × ℝ, z ∈ W' → ¬ JoinedIn W' z (z.1 + 2 * Real.pi, z.2) := by
    intro z hz hJ
    obtain ⟨γ, hγ⟩ := hJ
    have hzw : s' z ∈ W := by rw [hW'eq] at hz; exact hz
    refine hno (s' z) hzw ?_
    refine ⟨⟨⟨fun t => s' (γ t), hs'c.comp γ.continuous⟩, ?_, ?_⟩, ?_⟩
    · show s' (γ 0) = s' z
      rw [γ.source]
    · show s' (γ 1) = ((s' z).1 + p, (s' z).2)
      rw [γ.target]
      rw [hs']
      show ((1 / lam) * (z.1 + 2 * Real.pi), z.2) = ((1 / lam) * z.1 + p, z.2)
      rw [mul_add, hpinv]
    · intro t
      have := hγ t
      rw [hW'eq] at this
      exact this
  have hW'sub : W' ⊆ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b} := by
    intro q hq
    have h1 : s' q ∈ W := by rw [hW'eq] at hq; exact hq
    have h2 : a < (s' q).2 ∧ (s' q).2 < b := hsub h1
    rw [hs'] at h2
    exact h2
  obtain ⟨γ, hγ⟩ := h
  refine hnorm hW'open hW'sub hW'per hW'no ((s (x, y)).1) y y' ?_
  refine ⟨⟨⟨fun t => s (γ t), hsc.comp γ.continuous⟩, ?_, ?_⟩, ?_⟩
  · show s (γ 0) = ((s (x, y)).1, y)
    rw [γ.source, hs]
  · show s (γ 1) = ((s (x, y)).1 + 2 * Real.pi, y')
    rw [γ.target, hs]
    show (lam * (x + p), y') = (lam * x + 2 * Real.pi, y')
    rw [mul_add, hlamp]
  · intro t
    rw [hW']
    exact ⟨γ t, hγ t, rfl⟩

/-- **Covering-space (Mayer–Vietoris) decomposition for a two-set open cover of the strip.**

Let `VA, VB` be open `T`-invariant subsets of the strip with `VA ∪ VB = strip a b`.  Put
`A := {z : ↥(strip a b) | (z : ℝ × ℝ) ∉ VA}` and `B := {z : ↥(strip a b) | (z : ℝ × ℝ) ∉ VB}`;
these are closed disjoint subsets of the simply connected strip, with `Aᶜ = VA`, `Bᶜ = VB` and
`(A ∪ B)ᶜ = VA ∩ VB`.  Then every locally constant `ℤ`-valued function `h` on `VA ∩ VB` is the
difference `g - f` of locally constant `ℤ`-valued functions `f` on `VA` and `g` on `VB`.

This is the glued-covering ("2-out-of-3") decomposition of
`Commons.Topology.Jordan.two_disjoint_closed_not_separating`, transported to the strip; it is the
covering-space replacement of the Mayer–Vietoris sequence used in Denne's proof of the
cancellation step. -/
theorem exists_decomposition_of_open_cover {a b : ℝ} (hab : a < b)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hcover : VA ∪ VB = strip a b)
    {A B : Set ↥(strip a b)}
    (hA : A = {z : ↥(strip a b) | (z : ℝ × ℝ) ∉ VA})
    (hB : B = {z : ↥(strip a b) | (z : ℝ × ℝ) ∉ VB})
    (h : ↥((A ∪ B)ᶜ) → ℤ) (hW : IsOpen ((A ∪ B)ᶜ))
    (hh : ∀ z : ↥((A ∪ B)ᶜ), ContinuousAt h z) :
    ∃ (f : ↥(Aᶜ) → ℤ) (g : ↥(Bᶜ) → ℤ),
      IsLocallyConstant f ∧ IsLocallyConstant g ∧
      ∀ (z : ↥(strip a b)) (hz : z ∈ (A ∪ B)ᶜ),
        h ⟨z, hz⟩ = g ⟨z, Commons.Topology.Jordan.ClosedDisjoint.QD.compl_right hz⟩
          - f ⟨z, Commons.Topology.Jordan.ClosedDisjoint.QD.compl_left hz⟩ := by
  haveI : ConnectedSpace ↥(strip a b) := strip_connectedSpace hab
  haveI : LocallyPathConnectedSpace ↥(strip a b) := strip_locallyPathConnectedSpace a b
  haveI : SimplyConnectedSpace ↥(strip a b) := strip_simplyConnectedSpace hab
  have hmono : ∀ z : ↥(strip a b), Subsingleton (FundamentalGroup ↥(strip a b) z) :=
    fun z => inferInstance
  have hAc : IsClosed A := by
    rw [hA]; exact (hVA.preimage continuous_subtype_val).isClosed_compl
  have hBc : IsClosed B := by
    rw [hB]; exact (hVB.preimage continuous_subtype_val).isClosed_compl
  have hAB : A ⊆ Bᶜ := by
    rw [hA, hB]; intro z hz
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hz ⊢
    intro hzVB
    have hzS : (z : ℝ × ℝ) ∈ VA ∪ VB := by rw [hcover]; exact z.2
    rcases hzS with h | h
    · exact hz h
    · exact hzVB h
  have hBA : B ⊆ Aᶜ := by
    rw [hA, hB]; intro z hz
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hz ⊢
    intro hzVA
    have hzS : (z : ℝ × ℝ) ∈ VA ∪ VB := by rw [hcover]; exact z.2
    rcases hzS with h | h
    · exact hzVA h
    · exact hz h
  exact Commons.Topology.Jordan.ClosedDisjoint.QD.exists_decomposition hmono h hW hh hAc hBc hAB hBA

/-- **The decomposition in clean interface form.**  Same content as
`exists_decomposition_of_open_cover`, with the subtypes spelled by their defining predicates rather
than as complements: for open `VA, VB` covering the strip, every locally constant `ℤ`-valued `h` on
`VA ∩ VB` is `g - f` with `f` locally constant on `VA` and `g` on `VB`.  The transports use
`isLocallyConstant_setCongr`. -/
theorem localConstant_decomposition_of_open_cover {a b : ℝ} (hab : a < b)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hcover : VA ∪ VB = strip a b)
    (h : ↥{z : ↥(strip a b) | (z : ℝ × ℝ) ∈ VA ∧ (z : ℝ × ℝ) ∈ VB} → ℤ)
    (hh : ∀ z, ContinuousAt h z) :
    ∃ (f : ↥{z : ↥(strip a b) | (z : ℝ × ℝ) ∈ VA} → ℤ)
      (g : ↥{z : ↥(strip a b) | (z : ℝ × ℝ) ∈ VB} → ℤ),
      IsLocallyConstant f ∧ IsLocallyConstant g ∧
      ∀ (z : ↥(strip a b)) (hz1 : (z : ℝ × ℝ) ∈ VA) (hz2 : (z : ℝ × ℝ) ∈ VB),
        h ⟨z, hz1, hz2⟩ = g ⟨z, hz2⟩ - f ⟨z, hz1⟩ := by
  set A : Set ↥(strip a b) := {z | (z : ℝ × ℝ) ∉ VA} with hA
  set B : Set ↥(strip a b) := {z | (z : ℝ × ℝ) ∉ VB} with hB
  have eW : (A ∪ B)ᶜ = {z : ↥(strip a b) | (z : ℝ × ℝ) ∈ VA ∧ (z : ℝ × ℝ) ∈ VB} := by
    rw [hA, hB]
    ext z
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_not]
  have eA : Aᶜ = {z : ↥(strip a b) | (z : ℝ × ℝ) ∈ VA} := by
    rw [hA]; ext z; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
  have eB : Bᶜ = {z : ↥(strip a b) | (z : ℝ × ℝ) ∈ VB} := by
    rw [hB]; ext z; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
  have hopenW : IsOpen ((A ∪ B)ᶜ) := by
    rw [eW]
    exact (hVA.preimage continuous_subtype_val).inter (hVB.preimage continuous_subtype_val)
  have hcontW : ∀ w : ↥((A ∪ B)ᶜ),
      ContinuousAt (fun w : ↥((A ∪ B)ᶜ) => h ((Homeomorph.setCongr eW) w)) w := by
    intro w
    exact (hh _).comp ((Homeomorph.setCongr eW).continuous.continuousAt)
  obtain ⟨f', g', hf'lc, hg'lc, hkey⟩ :=
    exists_decomposition_of_open_cover hab hVA hVB hcover hA hB
      (fun w => h ((Homeomorph.setCongr eW) w)) hopenW hcontW
  refine ⟨fun x => f' ((Homeomorph.setCongr eA).symm x),
          fun x => g' ((Homeomorph.setCongr eB).symm x),
          isLocallyConstant_setCongr eA hf'lc, isLocallyConstant_setCongr eB hg'lc, ?_⟩
  intro z hz1 hz2
  have hzW : z ∈ (A ∪ B)ᶜ := by rw [eW]; exact ⟨hz1, hz2⟩
  have hkey' := hkey z hzW
  have eW' : ((Homeomorph.setCongr eW) ⟨z, hzW⟩ : ↥{z : ↥(strip a b) |
      (z : ℝ × ℝ) ∈ VA ∧ (z : ℝ × ℝ) ∈ VB}) = ⟨z, hz1, hz2⟩ := Subtype.ext rfl
  rw [eW'] at hkey'
  have eA' : ((Homeomorph.setCongr eA).symm
      (⟨z, hz1⟩ : ↥{z : ↥(strip a b) | (z : ℝ × ℝ) ∈ VA}) : ↥(Aᶜ))
      = ⟨z, Commons.Topology.Jordan.ClosedDisjoint.QD.compl_left hzW⟩ := Subtype.ext rfl
  have eB' : ((Homeomorph.setCongr eB).symm
      (⟨z, hz2⟩ : ↥{z : ↥(strip a b) | (z : ℝ × ℝ) ∈ VB}) : ↥(Bᶜ))
      = ⟨z, Commons.Topology.Jordan.ClosedDisjoint.QD.compl_right hzW⟩ := Subtype.ext rfl
  show h ⟨z, hz1, hz2⟩ = g' ((Homeomorph.setCongr eB).symm (⟨z, hz2⟩ :
      ↥{z : ↥(strip a b) | (z : ℝ × ℝ) ∈ VB}))
      - f' ((Homeomorph.setCongr eA).symm (⟨z, hz1⟩ : ↥{z : ↥(strip a b) | (z : ℝ × ℝ) ∈ VA}))
  rw [eA', eB']
  exact hkey'

/-- The translate of a point of a `T`-invariant set, as an element of the subtype. -/
def shiftPt {p : ℝ} {W : Set (ℝ × ℝ)} (hper : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W)
    (w : ↥W) : ↥W :=
  ⟨((w : ℝ × ℝ).1 + p, (w : ℝ × ℝ).2), (hper (w : ℝ × ℝ)).mp w.2⟩

/-- **`T`-shift function ("sheet index").**  A `ℤ`-valued function on a `T`-invariant set which
increases by exactly one under the translate `T q = (q.1 + p, q.2)`.  This is the winding/sheet
index of an inessential set: it exists on `VA ∩ VB` precisely when `(VA ∩ VB)/T` carries no loop
of non-zero winding, and it is the object that makes the `+1` crossing of `VA` and the `−1`
crossing of `VB` cancel. -/
def IsTShift {p : ℝ} {W : Set (ℝ × ℝ)}
    (hper : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W) (h : ↥W → ℤ) : Prop :=
  ∀ w : ↥W, h (shiftPt hper w) = h w + 1

/-! ## Construction of the `T`-shift function (plan for the existence direction)

Target: for open `T`-invariant `W ⊆ strip` that carries **no** `T`-crossing, produce a locally
constant `h : ↥W → ℤ` with `IsTShift hper h`.

Route (covering theory, commons tools in place):

1. `T` acts freely and properly discontinuously on `W` (`T q = (q.1+p, q.2)`, `p ≠ 0`), so the
   quotient map `q : ↥W → ↥W/T` is a covering map with deck group `ℤ`; the fibre over `w` is the
   `T`-orbit of `w`.  (`Commons.Topology.Covering.isCoveringMap_of_isProperMap` and its relatives.)
2. "No `T`-crossing" in `W` is exactly triviality of the monodromy `π₁(↥W/T) → ℤ` of this
   cover:  a loop `γ̃` in `↥W/T` lifts to a path in `W` from `w` to `T^k w`, and `k = 0` for all
   such loops iff no point of `W` is joined to its translate inside `W`.
3. `Commons.Topology.Covering.section_of_monodromy_eq_self_weak` then supplies a section
   `σ : ↥W/T → ↥W` of `q` (or `exists_section_of_isCoveringMap`, already in this file, when the
   base happens to be simply connected).
4. For `w : ↥W`, `w` and `σ (q w)` lie in the same fibre, hence `w = T^n (σ (q w))` for a
   *unique* `n` (uniqueness uses freeness: `T^k σ = σ` would force `σ` to have a fixed point of a
   non-trivial power).  Set `h w := n`.  Then `h (shiftPt hper w) = h w + 1`, and `h` is locally
   constant (it is the sheet index of a covering).

**Subtlety (the `±1` versus `k` point, on the construction side).**  Step 2 is not the same as
"`↥W/T` has no loop of non-zero winding": a `T`-crossing is a loop of winding **exactly** `±1`,
whereas the monodromy being trivial also excludes loops of winding `2`, `3`, …  A winding-`k`
(`|k| ≥ 2`) loop lifts to a path `w → T^k w`, and the intermediate-value argument on the
first coordinate only reaches a point whose `x`-coordinate is `w.1 + p`, not a translate of `w`;
so the well-definedness in step 4 genuinely needs "no `T`-crossing", and the corresponding
uniqueness lemma to prove is:

  `JoinedIn W x₀ (T^n w)` and `JoinedIn W x₀ (T^m w)` with `n ≠ m` ⟹ `W` has a `T`-crossing.

This is the only non-plumbing ingredient of (1); everything else in the route is application of
the covering commons.

**First-arrival staircase (the germ of the `|k| ≥ 2` step).**  Let `δ : I → W` be a path from
`x₀` to `T^k x₀` (`k ≥ 1`) and put `Φ t := ((δ t).1 − x₀.1)/p`, continuous from `0` to `k`.  The
first-arrival times `τ_j := min {t | Φ t = j}` exist for `j = 0, …, k` and satisfy
`0 = τ₀ < τ₁ < ⋯ < τ_k ≤ 1`.  Writing `y_j := (δ (τ_j)).2`, one has
`δ (τ_j) = T^j (x₀.1, y_j)`, and each sub-path `T^{−j} (δ|[τ_j, τ_{j+1}])` is a left–right path in
`W` from `(x₀.1, y_j)` to `(x₀.1 + p, y_{j+1})`.  Hence

* `x₀ ~ T^k x₀` in `W` produces `k` left–right paths in `W`, with height sequence
  `y₀ → y₁ → ⋯ → y_k`, and
* a `T`-crossing in `W` follows **as soon as** `y_j = y_{j+1}` for some `j` (then
  `δ (τ_{j+1}) = T δ (τ_j)`),

so the `|k| ≥ 2` step is exactly the *equal-height upgrade* for a chain of left–right paths — the
same condition that the box-crossing lemma `exists_leftRight_path_of_closed_compl` produces
(heights `y₀ ≠ y₁` in general).  This is the concrete reason the step is not plumbing.

**Assessment after attempting it.**  The `n ≠ m` argument *does* go through up to
`JoinedIn W x₀ (T^k x₀)` with `k ≠ 0` (concatenate the two witnesses and the `T^{m-n}`-translate
of one of them), but converting that into a genuine `T`-crossing when `|k| ≥ 2` is *not* a
plumbing step: a `k`-fold loop in the cylinder `↥W/T` is a closed curve of degree `k`, and
producing a `T`-chord equals asserting that a degree-`k` closed curve in the annulus has a
double point — i.e. that an embedded circle in the annulus has degree `0` or `±1`.  That is the
Jordan/annulus separation theory (`Commons.Topology.Jordan.annulus_no_spanning`,
`crosscut_complement_at_most_two`, the colleagues' `annulus_essential_loop`), not covering
plumbing.  Note also that step 3 (`section_of_monodromy_eq_self_weak`) needs the *stronger*
hypothesis "no loop of non-zero winding": a winding-`2` loop gives non-trivial monodromy while
still being crossing-free.  So the honest content of the crux is the annulus statement, with the
`±1` crossing hypotheses of `VA` and `VB` supplying the two essential loops that the annulus
argument needs. -/

/-- **A `T`-shift function forbids `T`-crossings.**  If a locally constant `ℤ`-valued function on
`W` shifts by one under `T`, then no point of `W` is joined to its translate inside `W`: the path
would keep `h` constant while the shift property forces it to increase. -/
lemma not_joinedIn_self_translate_of_shift {p : ℝ} {W : Set (ℝ × ℝ)}
    (hper : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W)
    (h : ↥W → ℤ) (hshift : IsTShift hper h) (hlc : IsLocallyConstant h)
    {z : ℝ × ℝ} (hz : z ∈ W) : ¬ JoinedIn W z (z.1 + p, z.2) := by
  intro hJ
  have h1 : h ⟨z, hJ.source_mem⟩ = h ⟨(z.1 + p, z.2), hJ.target_mem⟩ :=
    locallyConstant_eq_of_joinedIn hlc hJ
  have e1 : (⟨z, hJ.source_mem⟩ : ↥W) = ⟨z, hz⟩ := Subtype.ext rfl
  have e2 : (⟨(z.1 + p, z.2), hJ.target_mem⟩ : ↥W) = shiftPt hper ⟨z, hz⟩ :=
    Subtype.ext rfl
  rw [e1, e2] at h1
  have h2 := hshift ⟨z, hz⟩
  omega

/-! ### Strategy for (A): descent on the period of a component

`self_translate_power_zero_of_no_crossing` (the existence of a path `x ~ T^k x`, `k ≠ 0`, in a
`T`-invariant open `W` forces a `T`-crossing) has the following classical shape, with no
`T`-crossing hypothesis needed for the *pointwise* part:

Let `K` be the connected component of `W` containing `x` and `T^k x`.  Then `T^k K ∩ K ≠ ∅`, so
`K = T^k K`; and if `K ∩ TK = ∅` (no crossing) then `K, TK, …, T^{k-1}K` are pairwise disjoint
and the restriction `K → K̄ := K/(T^k) ⊆ cylinder` is a covering of degree `k = |k|`.  A covering
of degree `k ≥ 2` of a connected base has non-trivial monodromy, so `K̄` carries a loop of
winding `j` with `j ≢ 0 (mod k)`, hence `0 < |j| < k`; lifting that loop gives a *new* point whose
component `K'` satisfies `K' = T^j K'` with a strictly smaller period `|j| < k`.  Iterating the
descent terminates at period `1`, i.e. at a component `K''` with `T K'' = K''`, which *does*
contain a `T`-crossing (`z ~ Tz` for `z ∈ K''`).

So the non-plumbing content of (A) is: **period descent for `T`-invariant components** — that a
component of period `k ≥ 2` yields one of strictly smaller nonzero period.  This is the
"degree 0 or ±1" statement in its constructive form, and it is the piece to build (or to hand to
`Topology/Strip/self_translate_power_zero_of_no_crossing` on the fleet). -/

/-! ### Apex: the single remaining statement

All four tracked obligations — `equal_height_chain_upgrade`,
`period_descent_of_invariant_component`, `self_translate_power_zero_of_no_crossing` and the
collared `band_case_common_crossing` — are faces of one statement, the *apex*:

  **Apex.**  If `W` is open, `T`-invariant and cross-free, then `W` contains no path from
  `(x, y)` to `(x + p, y')` with `y ≠ y'`.

(*Equivalently:* a period-`k` component cannot avoid being `T`-invariant; equivalently, an
embedded circle in the annulus has degree `0` or `±1`.)

  * `k = 1` of apex **is** cross-freeness (equal endpoint heights);
  * apex ⟹ (A): a path `x ~ T^k x` (`k ≥ 2`) feeds the first-arrival staircase, which produces
    an unequal-height left–right path inside `W`, impossible under apex;
  * apex ⟹ (B)-side: the collared equal-height upgrade asks that a left–right path with unequal
    heights be straightenable; apex forbids such a path outright.

Apex is not derivable from openness plus local path-connectedness of `W` — the height along a
left–right path is a genuine degree of freedom — and its absence from Mathlib is exactly the
annulus/equal-height layer this project exists to build.  Stated form (commons-ready):

  `theorem no_unequal_height_leftRight_path_of_no_crossing {p a b : ℝ} (hp : 0 < p)
     {W : Set (ℝ × ℝ)} (hW : IsOpen W) (hsub : W ⊆ {q | a < q.2 ∧ q.2 < b})
     (hper : ∀ q, q ∈ W ↔ (q.1 + p, q.2) ∈ W)
     (hno : ∀ z ∈ W, ¬ JoinedIn W z (z.1 + p, z.2))
     {x y y' : ℝ} (h : JoinedIn W (x, y) (x + p, y')) : y = y'`

Given apex, the crux follows by the (A)-threading lemmas below together with the staircase.

  **Transport recipe (the apex is a pullback, not new annulus theory).**  Write
  `cov q := (q.2 : ℂ) * Complex.exp ((q.1 : ℂ) * Complex.I)` (the standard cover of `ℂ ∖ {0}` by the
  strip; `‖cov q‖ = |q.2|`, invariant under `q.1 ↦ q.1 + 2π`, so first rescale `p` to `2π`).  Given
  cross-free `W`, pull it back to `L := cov '' (strip ∖ W)`-type closed subset of the annulus and
  apply the commons `Topology/Jordan/annulus_no_spanning` (a bounded component leaves a
  spanning-free annulus) together with `Topology/Jordan/crosscut_complement_at_most_two`.  An
  unequal-height left–right path in `W` supplies precisely the spanning continuum that
  `annulus_no_spanning` forbids.  This is the same framework as the in-progress
  `exists_split_of_hjoin` / `equal_height_crossing_of_periodic_split` route (Work), which is the
  transport in its split form: closed `T`-invariant `A ∪ B` covering the pullback, `A` bounded away
  from the inner circle, `B` from the outer one.  So the two stretches should be coordinated rather
  than run independently. -/

/-- **Assembly step from (A).**  If in a `T`-invariant `W` every translate reached from `x ∈ W`
is `x` itself — the conclusion of `Topology/Strip/self_translate_power_zero_of_no_crossing`, taken
here as a hypothesis so that the crux becomes pure assembly — then `W` cannot contain a path from
`x` to its `k`-th translate with `k ≠ 0`.  Threading this against the first-arrival staircase
(`x₀ ~ T^k x₀`, `k ≠ 0`) is exactly the `|k| ≥ 2` step. -/
lemma no_nonzero_translate_of_power_zero
    {p : ℝ} {W : Set (ℝ × ℝ)}
    (hA : ∀ x : ℝ × ℝ, x ∈ W → ∀ k : ℤ, JoinedIn W x (x.1 + k * p, x.2) → k = 0)
    {x : ℝ × ℝ} (hx : x ∈ W) {k : ℤ} (hk : k ≠ 0)
    (h : JoinedIn W x (x.1 + k * p, x.2)) : False :=
  hk (hA x hx k h)

/-- **Assembly step from (A), crossing form.**  Same content restated as: under the "only own
translate is reached" hypothesis, `W` is cross-free in the strong sense that no point of `W` is
joined to a non-zero translate of itself. -/
lemma not_joinedIn_nonzero_translate_of_power_zero
    {p : ℝ} {W : Set (ℝ × ℝ)}
    (hA : ∀ x : ℝ × ℝ, x ∈ W → ∀ k : ℤ, JoinedIn W x (x.1 + k * p, x.2) → k = 0)
    {x : ℝ × ℝ} (hx : x ∈ W) {k : ℤ} (hk : k ≠ 0) :
    ¬ JoinedIn W x (x.1 + k * p, x.2) :=
  fun h => no_nonzero_translate_of_power_zero hA hx hk h

/-- **First-arrival (staircase, first step).**  A path in `W` from `x₀` to its `k`-th translate
(`k ≥ 1`) reaches the vertical line one period to the right of `x₀`.  Pure intermediate value
theorem on the first coordinate: the (reparametrised) first coordinate runs continuously from
`x₀.1` to `x₀.1 + k·p ≥ x₀.1 + p`, and the sub-path supplies the `JoinedIn` witness.  Iterating
this over `j = 0, …, k` is the first-arrival staircase. -/
lemma exists_mem_right_of_joinedIn_translate {p : ℝ} (hp : 0 < p) {W : Set (ℝ × ℝ)}
    {x0 : ℝ × ℝ} {k : ℤ} (hk : 1 ≤ k) (h : JoinedIn W x0 (x0.1 + k * p, x0.2)) :
    ∃ w ∈ W, w.1 = x0.1 + p ∧ JoinedIn W x0 w := by
  obtain ⟨γ, hγ⟩ := h
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  have hkp : x0.1 + p ≤ x0.1 + (k : ℝ) * p := by
    have h1k : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h2 := mul_le_mul_of_nonneg_right h1k hp.le
    linarith
  set F : ℝ → ℝ := fun s => (γ (Set.projIcc 0 1 h01 s)).1 with hF
  have hFc : Continuous F :=
    continuous_fst.comp (γ.continuous.comp continuous_projIcc)
  have e0 : F 0 = x0.1 := by
    have h1 : Set.projIcc 0 1 h01 0 = (0 : Set.Icc (0:ℝ) 1) :=
      Set.projIcc_of_mem h01 (Set.left_mem_Icc.mpr h01)
    show (γ (Set.projIcc 0 1 h01 0)).1 = x0.1
    rw [h1]
    exact congrArg Prod.fst γ.source
  have e1 : F 1 = x0.1 + (k : ℝ) * p := by
    have h1 : Set.projIcc 0 1 h01 1 = (1 : Set.Icc (0:ℝ) 1) :=
      Set.projIcc_of_mem h01 (Set.right_mem_Icc.mpr h01)
    show (γ (Set.projIcc 0 1 h01 1)).1 = x0.1 + (k : ℝ) * p
    rw [h1]
    exact congrArg Prod.fst γ.target
  have hmem : (x0.1 + p) ∈ Set.Icc (F 0) (F 1) := by
    rw [e0, e1]; exact ⟨by linarith, hkp⟩
  have himg : (x0.1 + p) ∈ F '' Set.Icc (0:ℝ) 1 :=
    (intermediate_value_Icc h01 hFc.continuousOn) hmem
  obtain ⟨s, hs, hsv⟩ := himg
  refine ⟨γ ⟨s, hs⟩, hγ _, ?_, ?_⟩
  · have hpim : Set.projIcc 0 1 h01 s = (⟨s, hs⟩ : Set.Icc (0:ℝ) 1) :=
      Set.projIcc_of_mem h01 hs
    simp only [hF] at hsv
    rw [hpim] at hsv
    exact hsv
  · have hsub : JoinedIn W (γ 0) (γ ⟨s, hs⟩) :=
      ⟨γ.subpath (0 : Set.Icc (0:ℝ) 1) ⟨s, hs⟩, fun u => hγ _⟩
    exact ⟨hsub.somePath.cast γ.source.symm rfl, fun u => hsub.somePath_mem u⟩

/-- **First-arrival (general form).**  If `x₀ ∈ W` is joined in `W` to *any* point `y` with
`y.1 ≥ x₀.1 + p`, the path reaches the vertical line `x = x₀.1 + p`.  This is the form the
staircase iteration uses: the next link applies to the tail `w₁ ~ T^k x` directly, since only the
`x`-coordinate of the endpoint enters.  Proof: intermediate value theorem on
`s ↦ (γ (projIcc 0 1 _ s)).1`. -/
lemma exists_mem_vline_of_joinedIn {p : ℝ} (hp : 0 < p) {W : Set (ℝ × ℝ)}
    {x0 y : ℝ × ℝ} (hy : x0.1 + p ≤ y.1) (h : JoinedIn W x0 y) :
    ∃ w ∈ W, w.1 = x0.1 + p ∧ JoinedIn W x0 w := by
  obtain ⟨γ, hγ⟩ := h
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  set F : ℝ → ℝ := fun s => (γ (Set.projIcc 0 1 h01 s)).1 with hF
  have hFc : Continuous F := continuous_fst.comp (γ.continuous.comp continuous_projIcc)
  have e0 : F 0 = x0.1 := by
    have h1 : Set.projIcc 0 1 h01 0 = (0 : Set.Icc (0:ℝ) 1) :=
      Set.projIcc_of_mem h01 (Set.left_mem_Icc.mpr h01)
    show (γ (Set.projIcc 0 1 h01 0)).1 = x0.1
    rw [h1]; exact congrArg Prod.fst γ.source
  have e1 : F 1 = y.1 := by
    have h1 : Set.projIcc 0 1 h01 1 = (1 : Set.Icc (0:ℝ) 1) :=
      Set.projIcc_of_mem h01 (Set.right_mem_Icc.mpr h01)
    show (γ (Set.projIcc 0 1 h01 1)).1 = y.1
    rw [h1]; exact congrArg Prod.fst γ.target
  have hmem : (x0.1 + p) ∈ Set.Icc (F 0) (F 1) := by
    rw [e0, e1]; exact ⟨by linarith, hy⟩
  have himg : (x0.1 + p) ∈ F '' Set.Icc (0:ℝ) 1 :=
    (intermediate_value_Icc h01 hFc.continuousOn) hmem
  obtain ⟨s, hs, hsv⟩ := himg
  refine ⟨γ ⟨s, hs⟩, hγ _, ?_, ?_⟩
  · have hpim : Set.projIcc 0 1 h01 s = (⟨s, hs⟩ : Set.Icc (0:ℝ) 1) :=
      Set.projIcc_of_mem h01 hs
    simp only [hF] at hsv
    rw [hpim] at hsv
    exact hsv
  · have hsub : JoinedIn W (γ 0) (γ ⟨s, hs⟩) :=
      ⟨γ.subpath (0 : Set.Icc (0:ℝ) 1) ⟨s, hs⟩, fun u => hγ _⟩
    exact ⟨hsub.somePath.cast γ.source.symm rfl, fun u => hsub.somePath_mem u⟩

/-- **Staircase chain.**  If `x` is joined to `y` in `W` and `x.1 + (j+1)·p ≤ y.1`, then `W`
contains a point `w` at height-level `x.1 + (j+1)·p` with `x ~ w` and `w ~ y`: the chain of
first-arrival points, one per period, all sharing the tail to `y`.  Induction on `j`, each step
being the single call `exists_mem_vline_of_joinedIn` on the tail `w ~ y`. -/
lemma exists_chain_of_joinedIn {p : ℝ} (hp : 0 < p) {W : Set (ℝ × ℝ)}
    {x y : ℝ × ℝ} (hxy : JoinedIn W x y) :
    ∀ j : ℕ, x.1 + ((j : ℝ) + 1) * p ≤ y.1 →
      ∃ w ∈ W, w.1 = x.1 + ((j : ℝ) + 1) * p ∧ JoinedIn W x w ∧ JoinedIn W w y := by
  intro j
  induction j with
  | zero =>
      intro hb
      obtain ⟨w, hwW, hw1, hxw⟩ := exists_mem_vline_of_joinedIn hp (by simpa using hb) hxy
      exact ⟨w, hwW, by simpa using hw1, hxw, hxw.symm.trans hxy⟩
  | succ j ih =>
      intro hb
      have hb' : x.1 + ((j : ℝ) + 1) * p ≤ y.1 := by
        have h := hb
        push_cast at h
        nlinarith [h, hp]
      obtain ⟨w, hwW, hw1, hxw, hwy⟩ := ih hb'
      have hbw : w.1 + p ≤ y.1 := by
        rw [hw1]
        have h := hb
        push_cast at h
        linarith
      obtain ⟨w', hw'W, hw'1, hww'⟩ := exists_mem_vline_of_joinedIn hp hbw hwy
      refine ⟨w', hw'W, ?_, hxw.trans hww', hww'.symm.trans hwy⟩
      rw [hw'1, hw1]; push_cast; ring

/-- **Staircase, first link.**  A path in `W` from `x₀` to its `k`-th translate (`k ≥ 1`) passes
through a point `w ∈ W` one period to the right, and the rest of the path gives `w ~ T^k x₀`.  This
is the `j = 0` link of the first-arrival staircase: iterating it on `T^{-j}(γ|[τ_j, 1])` is the
`j → j+1` leg. -/
lemma exists_step_of_joinedIn_translate {p : ℝ} (hp : 0 < p) {W : Set (ℝ × ℝ)}
    {x0 : ℝ × ℝ} {k : ℤ} (hk : 1 ≤ k) (h : JoinedIn W x0 (x0.1 + k * p, x0.2)) :
    ∃ w ∈ W, w.1 = x0.1 + p ∧ JoinedIn W x0 w ∧ JoinedIn W w (x0.1 + k * p, x0.2) := by
  obtain ⟨w, hwW, hw1, hx0w⟩ := exists_mem_right_of_joinedIn_translate hp hk h
  exact ⟨w, hwW, hw1, hx0w, hx0w.symm.trans h⟩

/-- **First step of the exchange argument.**  A connected component of an open set `VA` is closed
in `VA` (both it and its complement in `VA` are unions of components, which are open), so its
frontier misses `VA`. -/
lemma frontier_connectedComponentIn_inter_eq_empty {VA : Set (ℝ × ℝ)} (hVA : IsOpen VA)
    (z : ℝ × ℝ) : frontier (connectedComponentIn VA z) ∩ VA = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro w ⟨hwfr, hwVA⟩
  have hKopen : IsOpen (connectedComponentIn VA z) := hVA.connectedComponentIn
  rw [hKopen.frontier_eq] at hwfr
  have hK'open : IsOpen (connectedComponentIn VA w) := hVA.connectedComponentIn
  have hwK' : w ∈ connectedComponentIn VA w := mem_connectedComponentIn hwVA
  have hdisj : connectedComponentIn VA w ∩ connectedComponentIn VA z = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro u ⟨huw, huz⟩
    have h1 : connectedComponentIn VA w = connectedComponentIn VA u := connectedComponentIn_eq huw
    have h2 : connectedComponentIn VA z = connectedComponentIn VA u := connectedComponentIn_eq huz
    exact hwfr.2 (by rw [h2, ← h1]; exact mem_connectedComponentIn hwVA)
  obtain ⟨u, hu⟩ := mem_closure_iff_nhds.mp hwfr.1 (connectedComponentIn VA w)
    (hK'open.mem_nhds hwK')
  exact Set.not_nonempty_iff_eq_empty.mpr hdisj ⟨u, hu⟩

/-- The frontier of a component of an open `VA` lies inside the strip in the complement of `VA`. -/
lemma frontier_connectedComponentIn_subset_sdiff {a b : ℝ} {VA : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (z : ℝ × ℝ) :
    frontier (connectedComponentIn VA z) ∩ strip a b ⊆ strip a b \ VA := by
  intro w hw
  refine ⟨hw.2, ?_⟩
  intro hwVA
  exact (Set.eq_empty_iff_forall_notMem.mp
    (frontier_connectedComponentIn_inter_eq_empty hVA z)) w ⟨hw.1, hwVA⟩

/-- **Adaptation interface for the annulus lemma.**  The crux in the form used below has its
second crossing *backwards* (`z ~ T⁻¹z` in `VB`); the commons lemma
`Commons.Topology.Strip.annulus_essential_intersection` supplies the symmetric *forwards* form
(`z ~ Tz` in both).  This lemma converts the backwards hypothesis into the forwards one (reverse
the path and translate the endpoint back by `p`, using `T`-invariance of `VB`) and then applies
the symmetric statement, which is passed in as `hsym`.

Once `annulus_essential_intersection` lands, `common_crossing_of_open_cover` is obtained from
this lemma by a single application, so the wiring is a one-line change. -/
theorem common_crossing_of_open_cover_of_symmetric (p a b : ℝ) (hp : 0 < p) (hab : a < b)
    (hsym : ∀ {VA VB : Set (ℝ × ℝ)}, IsOpen VA → IsOpen VB →
      VA ⊆ strip a b → VB ⊆ strip a b →
      (∀ q : ℝ × ℝ, q ∈ VA ↔ (q.1 + p, q.2) ∈ VA) →
      (∀ q : ℝ × ℝ, q ∈ VB ↔ (q.1 + p, q.2) ∈ VB) →
      VA ∪ VB = strip a b →
      (∃ z : ℝ × ℝ, z ∈ VA ∧ JoinedIn VA z (z.1 + p, z.2)) →
      (∃ z : ℝ × ℝ, z ∈ VB ∧ JoinedIn VB z (z.1 + p, z.2)) →
      ∃ z : ℝ × ℝ, z ∈ VA ∧ z ∈ VB ∧ JoinedIn VA z (z.1 + p, z.2) ∧
        JoinedIn VB z (z.1 + p, z.2))
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hsubA : VA ⊆ strip a b) (hsubB : VB ⊆ strip a b)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ (q.1 + p, q.2) ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ (q.1 + p, q.2) ∈ VB)
    (hcover : VA ∪ VB = strip a b)
    (hwindA : ∃ z : ℝ × ℝ, z ∈ VA ∧ JoinedIn VA z (z.1 + p, z.2))
    (hwindB : ∃ z : ℝ × ℝ, z ∈ VB ∧ JoinedIn VB z (z.1 - p, z.2)) :
    ∃ z : ℝ × ℝ, z ∈ VA ∧ z ∈ VB ∧ JoinedIn VA z (z.1 + p, z.2) ∧
      JoinedIn VB z (z.1 + p, z.2) := by
  obtain ⟨z, hzVB, hzJ⟩ := hwindB
  refine hsym (VA := VA) (VB := VB) hVA hVB hsubA hsubB hperA hperB hcover hwindA ?_
  refine ⟨(z.1 - p, z.2), (hperB _).mpr (by simpa using hzVB), ?_⟩
  simpa using hzJ.symm

theorem common_crossing_of_open_cover {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hsubA : VA ⊆ strip a b)
    (hsubB : VB ⊆ strip a b)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ (q.1 + p, q.2) ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ (q.1 + p, q.2) ∈ VB)
    (hcover : VA ∪ VB = strip a b)
    (hwindA : ∃ z : ℝ × ℝ, z ∈ VA ∧ JoinedIn VA z (z.1 + p, z.2))
    (hwindB : ∃ z : ℝ × ℝ, z ∈ VB ∧ JoinedIn VB z (z.1 - p, z.2)) :
    ∃ z : ℝ × ℝ, z ∈ VA ∧ z ∈ VB ∧ JoinedIn VA z (z.1 + p, z.2) ∧
      JoinedIn VB z (z.1 + p, z.2) :=
  common_crossing_of_open_cover_of_symmetric p a b hp hab
    (fun {VA VB} hVA hVB hsubA hsubB hperA hperB hcover hwindA hwindB => by
      obtain ⟨z, hzW, h1, h2⟩ :=
        Commons.Topology.Strip.annulus_essential_intersection hp hab hVA hVB hsubA hsubB
          hperA hperB hcover hwindA hwindB
      exact ⟨z, hzW.1, hzW.2, h1, h2⟩)
    hVA hVB hsubA hsubB hperA hperB hcover hwindA hwindB

/-! ## The "zeta"-construction: two clean cases of the cancellation step

Chain the crossing of `VA`, the crossing of `VB` and a connecting path to close up a loop in the
strip.  If the connecting path can be chosen inside `VA` (resp. inside `VB`), the closed-up loop
exhibits a common crossing point at once. -/

/-- The union of the `T`-fixed connected components of `W`: the points of `W` joined to their
`T`-translate inside `W`. -/
def Zfix (p : ℝ) (W : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {z : ℝ × ℝ | z ∈ W ∧ JoinedIn W z (z.1 + p, z.2)}

lemma Zfix_subset (p : ℝ) (W : Set (ℝ × ℝ)) : Zfix p W ⊆ W := fun _ hz => hz.1

/-- `Zfix p W` is `T`-invariant whenever `W` is. -/
lemma Zfix_periodic {p : ℝ} {W : Set (ℝ × ℝ)}
    (hper : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W) (q : ℝ × ℝ) :
    q ∈ Zfix p W ↔ (q.1 + p, q.2) ∈ Zfix p W := by
  constructor
  · rintro ⟨hqW, hq⟩
    refine ⟨(hper q).mp hqW, ?_⟩
    simpa using joinedIn_translate (p := p) hper hq
  · rintro ⟨hqW, hq⟩
    refine ⟨(hper q).mpr hqW, ?_⟩
    simpa using joinedIn_translate_inv (p := p) hper hq

/-- `Zfix p W` is open when `W` is (it is a union of connected components of `W`). -/
lemma isOpen_Zfix {p : ℝ} {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hper : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W) : IsOpen (Zfix p W) := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  have hcompopen : IsOpen (connectedComponentIn W z) := hW.connectedComponentIn
  have hpc : IsPathConnected (connectedComponentIn W z) :=
    (hcompopen.isConnected_iff_isPathConnected).mp
      ⟨⟨z, mem_connectedComponentIn hz.1⟩, isPreconnected_connectedComponentIn⟩
  have hsub : connectedComponentIn W z ⊆ Zfix p W := by
    intro w hw
    have hjoinwz : JoinedIn (connectedComponentIn W z) z w :=
      hpc.joinedIn z (mem_connectedComponentIn hz.1) w hw
    have h1 : JoinedIn W w z := (hjoinwz.mono (connectedComponentIn_subset W z)).symm
    have h3 : JoinedIn W (z.1 + p, z.2) (w.1 + p, w.2) :=
      (joinedIn_translate hper h1).symm
    exact ⟨connectedComponentIn_subset W z hw, h1.trans (hz.2.trans h3)⟩
  exact ⟨connectedComponentIn W z, hsub, hcompopen, mem_connectedComponentIn hz.1⟩

/-- Every point of `Zfix p W` is joined to its `T`-translate *inside* `Zfix p W`; consequently
every connected component of `Zfix p W` is `T`-fixed. -/
lemma joinedIn_Zfix {p : ℝ} {W : Set (ℝ × ℝ)}
    (hper : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W) {z : ℝ × ℝ}
    (hz : z ∈ Zfix p W) : JoinedIn (Zfix p W) z (z.1 + p, z.2) := by
  obtain ⟨hzW, hz⟩ := hz
  obtain ⟨γ, hγ⟩ := hz
  have hmem : ∀ t, γ t ∈ Zfix p W := by
    intro t
    refine ⟨hγ t, ?_⟩
    have h1 : JoinedIn W (γ t) z := by
      have hsub0 : JoinedIn W (γ 0) (γ t) := ⟨γ.subpath 0 t, fun s => hγ _⟩
      have hsub0' : JoinedIn W z (γ t) :=
        ⟨hsub0.somePath.cast γ.source.symm rfl, fun s => hsub0.somePath_mem s⟩
      exact hsub0'.symm
    have h2 : JoinedIn W z (z.1 + p, z.2) := ⟨γ, hγ⟩
    have h3 : JoinedIn W (z.1 + p, z.2) ((γ t).1 + p, (γ t).2) := by
      simpa using joinedIn_translate (p := p) hper (JoinedIn.symm h1)
    exact h1.trans (h2.trans h3)
  refine ⟨{ toContinuousMap := ⟨γ, γ.continuous⟩, source' := γ.source, target' := γ.target }, ?_⟩
  exact hmem

/-- **The frontier of `Zfix p W` inside `W`.**  `Zfix p W` is closed in `W`, so no point of `W`
lies on its frontier.  Equivalently, the descent argument below needs
`closure (Zfix p W) ∩ W = Zfix p W`. -/
lemma closure_Zfix_inter {p : ℝ} {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hper : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W) :
    closure (Zfix p W) ∩ W = Zfix p W := by
  refine Subset.antisymm ?_ (fun z hz => ⟨subset_closure hz, hz.1⟩)
  intro w hw
  obtain ⟨hwcl, hwW⟩ := hw
  set L : Set (ℝ × ℝ) := connectedComponentIn W w with hL
  have hLopen : IsOpen L := hW.connectedComponentIn
  have hwL : w ∈ L := mem_connectedComponentIn hwW
  obtain ⟨u, huL, huZ⟩ := mem_closure_iff_nhds.mp hwcl L (hLopen.mem_nhds hwL)
  have hLpc : IsPathConnected L :=
    (hLopen.isConnected_iff_isPathConnected).mp
      ⟨⟨w, hwL⟩, isPreconnected_connectedComponentIn⟩
  have hwu : JoinedIn W w u :=
    (hLpc.joinedIn w hwL u huL).mono (connectedComponentIn_subset W w)
  have huu : JoinedIn W u (u.1 + p, u.2) :=
    (joinedIn_Zfix hper huZ).mono (fun _ hz => hz.1)
  have htrans : JoinedIn W (u.1 + p, u.2) (w.1 + p, w.2) :=
    (joinedIn_translate (p := p) hper hwu).symm
  exact ⟨hwW, hwu.trans (huu.trans htrans)⟩

/-- A continuous path starting inside an open set `C` and ending outside `C` meets `frontier C`. -/
lemma exists_mem_frontier_of_path {X : Type*} [TopologicalSpace X] {C : Set X} (hC : IsOpen C)
    {γ : C(Set.Icc (0 : ℝ) 1, X)} (h0 : γ 0 ∈ C) (h1 : γ 1 ∉ C) :
    ∃ t : Set.Icc (0 : ℝ) 1, γ t ∈ frontier C := by
  by_contra hcon
  push Not at hcon
  have hsub : (Set.range γ) ⊆ C ∪ (closure C)ᶜ := by
    rintro x ⟨t, rfl⟩
    by_cases hxC : γ t ∈ C
    · exact Or.inl hxC
    · refine Or.inr ?_
      rw [Set.mem_compl_iff]
      intro hxcl
      exact hcon t (by rw [hC.frontier_eq]; exact ⟨hxcl, hxC⟩)
  have hpc : IsPreconnected (Set.range γ) := by
    rw [← Set.image_univ]
    exact isPreconnected_univ.image γ γ.continuous.continuousOn
  rcases hpc.subset_or_subset hC isClosed_closure.isOpen_compl
      (by rw [Set.disjoint_left]; intro x hxC hxcl; exact hxcl (subset_closure hxC)) hsub with h | h
  · exact h1 (h ⟨1, rfl⟩)
  · exact h ⟨0, rfl⟩ (subset_closure h0)

/-- **Third step (the descent datum).**  Same setting as `Zfix_inter_sdiff_nonempty_of_component`,
but recording the sharper conclusion: the exit point is a point of `Zfix p VA` lying on the
frontier of the `VB`-component `connectedComponentIn VB p₀`.  This is the datum that the descent
argument iterates on: the frontier of a `VB`-component (a component that is *not* `T`-invariant,
hence disjoint from `Zfix p VB`) meets `Zfix p VA`. -/
lemma exists_frontier_componentIn_inter_Zfix {p a b : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB) (hsubA : VA ⊆ strip a b)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ (q.1 + p, q.2) ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ (q.1 + p, q.2) ∈ VB)
    (hdisj : Disjoint (Zfix p VA) (Zfix p VB))
    {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ VB) {w : ℝ × ℝ}
    (hwZ : w ∈ Zfix p VA) (hwL : w ∈ connectedComponentIn VB p₀) :
    ∃ q : ℝ × ℝ, q ∈ Zfix p VA ∧ q ∈ frontier (connectedComponentIn VB p₀) := by
  obtain ⟨γ, hγ⟩ := joinedIn_Zfix hperA hwZ
  have hLopen : IsOpen (connectedComponentIn VB p₀) := hVB.connectedComponentIn
  have hLpc : IsPathConnected (connectedComponentIn VB p₀) :=
    (hLopen.isConnected_iff_isPathConnected).mp
      ⟨⟨p₀, mem_connectedComponentIn hp₀⟩, isPreconnected_connectedComponentIn⟩
  have hwVB : w ∈ VB := connectedComponentIn_subset VB p₀ hwL
  have hTw : γ 1 ∉ connectedComponentIn VB p₀ := by
    intro h1L
    have hJVB : JoinedIn VB w (w.1 + p, w.2) := by
      have h1 := (hLpc.joinedIn w hwL (γ 1) h1L).mono (connectedComponentIn_subset VB p₀)
      rwa [γ.target] at h1
    exact Set.disjoint_left.mp hdisj hwZ ⟨hwVB, hJVB⟩
  have h0L : γ.toContinuousMap (0 : Set.Icc (0:ℝ) 1) ∈ connectedComponentIn VB p₀ := by
    rw [show γ.toContinuousMap (0 : Set.Icc (0:ℝ) 1) = w from γ.source]
    exact hwL
  have h1L : γ.toContinuousMap (1 : Set.Icc (0:ℝ) 1) ∉ connectedComponentIn VB p₀ := hTw
  obtain ⟨t, ht⟩ := exists_mem_frontier_of_path hLopen h0L h1L
  exact ⟨γ t, hγ t, ht⟩

/-- The connected component of a point of `Zfix p W` is contained in `Zfix p W` (it is a union of
`T`-fixed components of `W`). -/
lemma connectedComponentIn_subset_Zfix {p : ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W)
    (hper : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W) {z : ℝ × ℝ}
    (hz : z ∈ Zfix p W) : connectedComponentIn W z ⊆ Zfix p W := by
  have hcompopen : IsOpen (connectedComponentIn W z) := hW.connectedComponentIn
  have hpc : IsPathConnected (connectedComponentIn W z) :=
    (hcompopen.isConnected_iff_isPathConnected).mp
      ⟨⟨z, mem_connectedComponentIn hz.1⟩, isPreconnected_connectedComponentIn⟩
  intro w hw
  have hjoinwz : JoinedIn (connectedComponentIn W z) z w :=
    hpc.joinedIn z (mem_connectedComponentIn hz.1) w hw
  have h1 : JoinedIn W w z := (hjoinwz.mono (connectedComponentIn_subset W z)).symm
  have h3 : JoinedIn W (z.1 + p, z.2) (w.1 + p, w.2) :=
    (joinedIn_translate hper h1).symm
  exact ⟨connectedComponentIn_subset W z hw, h1.trans (hz.2.trans h3)⟩

/-- **Second step of the exchange argument.**  If the two unions of `T`-fixed components are
disjoint, then the frontier of a `T`-fixed component of `VA` misses `Zfix p VB`: a point of
`Zfix p VB` on the frontier is a neighbourhood of a point of `Zfix p VA`. -/
lemma frontier_component_inter_Zfix_eq_empty {p : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ (q.1 + p, q.2) ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ (q.1 + p, q.2) ∈ VB)
    (hdisj : Disjoint (Zfix p VA) (Zfix p VB)) {z : ℝ × ℝ} (hz : z ∈ Zfix p VA) :
    frontier (connectedComponentIn VA z) ∩ Zfix p VB = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro w ⟨hwfr, hwZ⟩
  have hKsub : connectedComponentIn VA z ⊆ Zfix p VA :=
    connectedComponentIn_subset_Zfix hVA hperA hz
  have hKopen : IsOpen (connectedComponentIn VA z) := hVA.connectedComponentIn
  have hZopen : IsOpen (Zfix p VB) := isOpen_Zfix hVB hperB
  rw [hKopen.frontier_eq] at hwfr
  obtain ⟨u, hu⟩ := mem_closure_iff_nhds.mp hwfr.1 (Zfix p VB) (hZopen.mem_nhds hwZ)
  exact Set.disjoint_left.mp hdisj (hKsub hu.2) hu.1

/-- A point of the frontier of a component of `VA` which lies in the open set `VB` has a
`VB`-component meeting that component of `VA`. -/
lemma nonempty_inter_connectedComponentIn_of_mem_frontier {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB) {z p : ℝ × ℝ}
    (hp : p ∈ frontier (connectedComponentIn VA z)) (hpVB : p ∈ VB) :
    (connectedComponentIn VB p ∩ connectedComponentIn VA z).Nonempty := by
  have hKopen : IsOpen (connectedComponentIn VA z) := hVA.connectedComponentIn
  have hLopen : IsOpen (connectedComponentIn VB p) := hVB.connectedComponentIn
  rw [hKopen.frontier_eq] at hp
  exact mem_closure_iff_nhds.mp hp.1 (connectedComponentIn VB p)
    (hLopen.mem_nhds (mem_connectedComponentIn hpVB))

/-- **Third step (the exchange).**  Let `Zfix p VA` and `Zfix p VB` be disjoint, let `L` be the
`VB`-component of a point `p₀ ∈ VB`, and suppose `Zfix p VA` meets `L` at a point `w`.  The
`T`-translate of `w` is not in `L` (otherwise `w ∈ Zfix p VB`), so the path inside `Zfix p VA`
from `w` to its translate leaves `L` through `frontier L ⊆ strip \ VB`: consequently `Zfix p VA`
meets `strip \ VB`. -/
lemma Zfix_inter_sdiff_nonempty_of_component {p a b : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB) (hsubA : VA ⊆ strip a b)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ (q.1 + p, q.2) ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ (q.1 + p, q.2) ∈ VB)
    (hdisj : Disjoint (Zfix p VA) (Zfix p VB))
    {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ VB) {w : ℝ × ℝ}
    (hwZ : w ∈ Zfix p VA) (hwL : w ∈ connectedComponentIn VB p₀) :
    (Zfix p VA ∩ (strip a b \ VB)).Nonempty := by
  obtain ⟨γ, hγ⟩ := joinedIn_Zfix hperA hwZ
  have hLopen : IsOpen (connectedComponentIn VB p₀) := hVB.connectedComponentIn
  have hLpc : IsPathConnected (connectedComponentIn VB p₀) :=
    (hLopen.isConnected_iff_isPathConnected).mp
      ⟨⟨p₀, mem_connectedComponentIn hp₀⟩, isPreconnected_connectedComponentIn⟩
  have hwVB : w ∈ VB := connectedComponentIn_subset VB p₀ hwL
  have hTw : (γ 1) ∉ connectedComponentIn VB p₀ := by
    intro h1L
    have hJVB : JoinedIn VB w (w.1 + p, w.2) := by
      have h1 := (hLpc.joinedIn w hwL (γ 1) h1L).mono (connectedComponentIn_subset VB p₀)
      rwa [γ.target] at h1
    exact Set.disjoint_left.mp hdisj hwZ ⟨hwVB, hJVB⟩
  have h0L : γ.toContinuousMap (0 : Set.Icc (0:ℝ) 1) ∈ connectedComponentIn VB p₀ := by
    rw [show γ.toContinuousMap (0 : Set.Icc (0:ℝ) 1) = w from γ.source]
    exact hwL
  have h1L : γ.toContinuousMap (1 : Set.Icc (0:ℝ) 1) ∉ connectedComponentIn VB p₀ := hTw
  obtain ⟨t, ht⟩ := exists_mem_frontier_of_path hLopen h0L h1L
  have hnotVB : γ t ∉ VB := by
    intro htVB
    exact (Set.eq_empty_iff_forall_notMem.mp
      (frontier_connectedComponentIn_inter_eq_empty hVB p₀)) (γ.toContinuousMap t) ⟨ht, htVB⟩
  exact ⟨γ t, ⟨hγ t, hsubA (hγ t).1, hnotVB⟩⟩

/-- **The exchange pass, packaged (direction `VA → VB`).**  If `Zfix p VA` and `Zfix p VB` are
disjoint and the `VB`-component of a point `p₀ ∈ VB` meets the component of a point of
`Zfix p VA`, then some point of `Zfix p VA` lies on the frontier of that `VB`-component.  This is
the packaged form of `exists_frontier_componentIn_inter_Zfix`, taking the input in the shape
produced by `nonempty_inter_connectedComponentIn_of_mem_frontier`. -/
lemma exists_frontier_componentIn_inter_Zfix_of_inter {p a b : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB) (hsubA : VA ⊆ strip a b)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ (q.1 + p, q.2) ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ (q.1 + p, q.2) ∈ VB)
    (hdisj : Disjoint (Zfix p VA) (Zfix p VB))
    {z : ℝ × ℝ} (hz : z ∈ Zfix p VA) {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ VB)
    (hinter : (connectedComponentIn VB p₀ ∩ connectedComponentIn VA z).Nonempty) :
    ∃ q : ℝ × ℝ, q ∈ Zfix p VA ∧ q ∈ frontier (connectedComponentIn VB p₀) := by
  obtain ⟨w, hwL, hwK⟩ := hinter
  exact exists_frontier_componentIn_inter_Zfix hVA hVB hsubA hperA hperB hdisj hp₀
    (connectedComponentIn_subset_Zfix hVA hperA hz hwK) hwL

/-- **The exchange pass, packaged (direction `VB → VA`).**  Mirror of
`exists_frontier_componentIn_inter_Zfix_of_inter` with the roles of `VA` and `VB` exchanged: the
output is a point of `Zfix p VB` on the frontier of a `VA`-component, i.e. exactly the shape of
input that the `VA → VB` direction consumes after `T`-transport. -/
lemma exists_frontier_componentIn_inter_Zfix_of_inter' {p a b : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB) (hsubB : VB ⊆ strip a b)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ (q.1 + p, q.2) ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ (q.1 + p, q.2) ∈ VB)
    (hdisj : Disjoint (Zfix p VA) (Zfix p VB))
    {z : ℝ × ℝ} (hz : z ∈ Zfix p VB) {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ VA)
    (hinter : (connectedComponentIn VA p₀ ∩ connectedComponentIn VB z).Nonempty) :
    ∃ q : ℝ × ℝ, q ∈ Zfix p VB ∧ q ∈ frontier (connectedComponentIn VA p₀) :=
  exists_frontier_componentIn_inter_Zfix_of_inter hVB hVA hsubB hperB hperA hdisj.symm hz hp₀
    (by rwa [Set.inter_comm] at hinter ⊢)

/-- **The exchange pass is closed on its input shape (pair tracking).**  If the `VB`-component
`L = connectedComponentIn VB p₀` meets the component of a point `z ∈ Zfix p VA`, then there is a
point `q ∈ Zfix p VA` such that `q ∈ frontier L` **and** `L` still meets the component of `q`
(which is again a `T`-invariant component of `VA`, since `q ∈ Zfix p VA`).  So the pair datum
`(L, K)` with `L ∩ K ≠ ∅` reproduces itself, now additionally carrying a point of `Zfix p VA`
on `frontier L`.  This is the one-step closure used by the descent recursion; iterating it
repeatedly with the *transported* component `connectedComponentIn VA q` is what the ping-pong
consumes. -/
lemma exists_Zfix_mem_frontier_and_inter_component {p a b : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB) (hsubA : VA ⊆ strip a b)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ (q.1 + p, q.2) ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ (q.1 + p, q.2) ∈ VB)
    (hdisj : Disjoint (Zfix p VA) (Zfix p VB))
    {z : ℝ × ℝ} (hz : z ∈ Zfix p VA) {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ VB)
    (hinter : (connectedComponentIn VB p₀ ∩ connectedComponentIn VA z).Nonempty) :
    ∃ q : ℝ × ℝ, q ∈ Zfix p VA ∧ q ∈ frontier (connectedComponentIn VB p₀) ∧
      (connectedComponentIn VB p₀ ∩ connectedComponentIn VA q).Nonempty := by
  obtain ⟨q, hqZ, hqfr⟩ :=
    exists_frontier_componentIn_inter_Zfix_of_inter hVA hVB hsubA hperA hperB hdisj hz hp₀ hinter
  have hKqopen : IsOpen (connectedComponentIn VA q) := hVA.connectedComponentIn
  have hqKq : q ∈ connectedComponentIn VA q := mem_connectedComponentIn hqZ.1
  have h1 : (connectedComponentIn VA q ∩ connectedComponentIn VB p₀).Nonempty :=
    mem_closure_iff_nhds.mp (frontier_subset_closure hqfr) (connectedComponentIn VA q)
      (hKqopen.mem_nhds hqKq)
  exact ⟨q, hqZ, hqfr, by rwa [Set.inter_comm]⟩

/-- **The straddling datum of the exchange recursion.**  A `T`-invariant component `K` of `VA`
meeting a `VB`-component `L`, together with a point `q` of `K` lying on the frontier of `L`.
In the cylinder this is the statement that the essential open set `K̄ = K/T` straddles the
frontier of `Ḻ = L/T` (an *inessential* open set, since `L` is not `T`-invariant).

This structure is deliberately a bare definition: it is the state that
`exists_Zfix_mem_frontier_and_inter_component` transports, and it is the object on which the
strict measurement of the straddling (and then the single-pass strict-descent lemma) will be
taken.  Concretely, `K` is where the crossing lives, `L` is the component whose orbit the
crossing is trapped by, and `q` records that the trapping is witnessed on `∂L` rather than in
the interior. -/
structure Straddle (p : ℝ) (VA VB : Set (ℝ × ℝ)) where
  /-- The `T`-invariant component of `VA`. -/
  K : Set (ℝ × ℝ)
  /-- The component of `VB` whose orbit is trapped. -/
  L : Set (ℝ × ℝ)
  isOpen_K : IsOpen K
  subset_K : K ⊆ VA
  connected_K : IsConnected K
  periodic_K : ∀ q : ℝ × ℝ, q ∈ K ↔ (q.1 + p, q.2) ∈ K
  isOpen_L : IsOpen L
  subset_L : L ⊆ VB
  meets : (L ∩ K).Nonempty
  /-- A point of `K` on the frontier of `L`. -/
  q : ℝ × ℝ
  q_mem_K : q ∈ K
  q_mem_frontier : q ∈ frontier L


namespace Straddle

variable {p : ℝ} {VA VB : Set (ℝ × ℝ)}

/-- The **frontier straddle** of a `Straddle`: the part of `∂L` lying in the `T`-invariant
component `K`.  This is the quantity the descent has to measure: by `T`-invariance of `K` the
*interior* datum is constant under transport (`K ∩ TⁿL = Tⁿ (K ∩ L)`, an orbit-index measurement),
whereas this frontier part is what the pass moves (the pass produces a point `q ∈ K' ∩ ∂L`). -/
def frontierPart (S : Straddle p VA VB) : Set (ℝ × ℝ) := frontier S.L ∩ S.K

/-- The point recorded by the structure lies in its frontier straddle. -/
lemma q_mem_frontierPart (S : Straddle p VA VB) : S.q ∈ S.frontierPart :=
  ⟨S.q_mem_frontier, S.q_mem_K⟩


end Straddle

/-- **The `T`-translate of a point of a `Zfix`-component stays in that component.**  Equivalently:
every connected component of `Zfix p W` is `T`-invariant.  This is what makes "a point of
`Zfix p VA` whose component meets a `T`-invariant `VB`-component" *equivalent* to a point of
`Zfix p VA ∩ Zfix p VB` (the crux conclusion), and hence why producing a `Zfix p VB` point from
one-sided `Zfix p VA` data is exactly the crux. -/
lemma translate_mem_connectedComponentIn_of_mem_Zfix {p : ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hper : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W)
    {z : ℝ × ℝ} (hz : z ∈ Zfix p W) {w : ℝ × ℝ}
    (hw : w ∈ connectedComponentIn W z) :
    (w.1 + p, w.2) ∈ connectedComponentIn W z := by
  set K := connectedComponentIn W z with hK
  have hKopen : IsOpen K := hW.connectedComponentIn
  have hKpath : IsPathConnected K :=
    (hKopen.isConnected_iff_isPathConnected).mp
      ⟨⟨z, mem_connectedComponentIn hz.1⟩, isPreconnected_connectedComponentIn⟩
  have hTzK : (z.1 + p, z.2) ∈ K := mem_connectedComponentIn_of_joinedIn hz.2
  have hjoinwz : JoinedIn W w z :=
    (hKpath.joinedIn w hw z (mem_connectedComponentIn hz.1)).mono
      (connectedComponentIn_subset W z)
  have h1 : (w.1 + p, w.2) ∈ connectedComponentIn W (z.1 + p, z.2) :=
    mem_connectedComponentIn_of_joinedIn (joinedIn_translate hper hjoinwz.symm)
  rw [← connectedComponentIn_eq hTzK] at h1
  exact h1

/-- Same as `translate_mem_connectedComponentIn_of_mem_Zfix`, for the inverse translate. -/
lemma translate_inv_mem_connectedComponentIn_of_mem_Zfix {p : ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hper : ∀ q : ℝ × ℝ, q ∈ W ↔ (q.1 + p, q.2) ∈ W)
    {z : ℝ × ℝ} (hz : z ∈ Zfix p W) {w : ℝ × ℝ}
    (hw : w ∈ connectedComponentIn W z) :
    (w.1 - p, w.2) ∈ connectedComponentIn W z := by
  set K := connectedComponentIn W z with hK
  have hKopen : IsOpen K := hW.connectedComponentIn
  have hKpath : IsPathConnected K :=
    (hKopen.isConnected_iff_isPathConnected).mp
      ⟨⟨z, mem_connectedComponentIn hz.1⟩, isPreconnected_connectedComponentIn⟩
  have hTzK : (z.1 - p, z.2) ∈ K := by
    have h := mem_connectedComponentIn_of_joinedIn (joinedIn_translate_inv hper hz.2.symm)
    simpa using h
  have hjoinwz : JoinedIn W w z :=
    (hKpath.joinedIn w hw z (mem_connectedComponentIn hz.1)).mono
      (connectedComponentIn_subset W z)
  have h1 : (w.1 - p, w.2) ∈ connectedComponentIn W (z.1 - p, z.2) :=
    mem_connectedComponentIn_of_joinedIn (joinedIn_translate_inv hper hjoinwz.symm)
  rw [← connectedComponentIn_eq hTzK] at h1
  exact h1






namespace Straddle

variable {p : ℝ} {VA VB : Set (ℝ × ℝ)}

/-- **The pass, as a map of `Straddle`s.**  It replaces the `T`-invariant component `K` by the
component of the recorded frontier point `q` — which is again `T`-invariant, because `K` connected
and `T`-invariant makes `q ∈ Zfix p VA` — and keeps `L` and the frontier point `q` fixed.  The
`meets` field of the output holds because `q ∈ frontier L` and the new component is open.

Note (important for the descent): the pass keeps `q` and `L`, so the `T`-orbit class of `q` in
`frontierPart` is a *fixed point* of `step`.  Hence the strict quantity for the descent cannot be
the orbit class of the recorded point; it has to be a measurement of how `frontierPart` sits in
`∂L` (e.g. its `T`-orbit structure in `∂L`) that the change `K ↦ connectedComponentIn VA q`
genuinely moves. -/
def step (hVA : IsOpen VA)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ (q.1 + p, q.2) ∈ VA) (S : Straddle p VA VB) :
    Straddle p VA VB := by
  have hqVA : S.q ∈ VA := S.subset_K S.q_mem_K
  have hTqK : (S.q.1 + p, S.q.2) ∈ S.K := (S.periodic_K S.q).mp S.q_mem_K
  have hKpath : IsPathConnected S.K :=
    (S.isOpen_K.isConnected_iff_isPathConnected).mp S.connected_K
  have hjoin : JoinedIn VA S.q (S.q.1 + p, S.q.2) :=
    (hKpath.joinedIn S.q S.q_mem_K _ hTqK).mono S.subset_K
  have hqZ : S.q ∈ Zfix p VA := ⟨hqVA, hjoin⟩
  exact
    { K := connectedComponentIn VA S.q
      L := S.L
      isOpen_K := hVA.connectedComponentIn
      subset_K := connectedComponentIn_subset VA S.q
      connected_K :=
        ⟨⟨S.q, mem_connectedComponentIn hqVA⟩, isPreconnected_connectedComponentIn⟩
      periodic_K := fun w =>
        ⟨fun hw => translate_mem_connectedComponentIn_of_mem_Zfix hVA hperA hqZ hw,
          fun hw => by
            have h := translate_inv_mem_connectedComponentIn_of_mem_Zfix hVA hperA hqZ
              (w := (w.1 + p, w.2)) hw
            simpa using h⟩
      isOpen_L := S.isOpen_L
      subset_L := S.subset_L
      meets := by
        have hcl : S.q ∈ closure S.L := frontier_subset_closure S.q_mem_frontier
        have hKopen : IsOpen (connectedComponentIn VA S.q) := hVA.connectedComponentIn
        have h1 := mem_closure_iff_nhds.mp hcl (connectedComponentIn VA S.q)
          (hKopen.mem_nhds (mem_connectedComponentIn hqVA))
        rwa [Set.inter_comm] at h1
      q := S.q
      q_mem_K := mem_connectedComponentIn hqVA
      q_mem_frontier := S.q_mem_frontier }

/-- **The `frontierPart` comparison.**  As subsets of `∂L`, the frontier straddle can only *grow*
under the pass: the pass replaces `K` by `connectedComponentIn VA q`, and `K` (being a connected
subset of `VA` containing `q`) is contained in that component.  So
`frontierPart S ⊆ frontierPart (step S)`, i.e. the pass is monotone for the frontier straddle.

This is the shape the descent has to consume: the strict quantity lives on the *change* of this
subset of `∂L`, i.e. on the part `∂L ∩ connectedComponentIn VA q` that the pass adds — the orbit
class of the component `K ∩ ∂L`, not of the recorded point `q` (which `step` fixes). -/
lemma frontierPart_subset_step (hVA : IsOpen VA)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ (q.1 + p, q.2) ∈ VA) (S : Straddle p VA VB) :
    S.frontierPart ⊆ (S.step hVA hperA).frontierPart := by
  rintro x ⟨hxfr, hxK⟩
  refine ⟨?_, ?_⟩
  · show x ∈ frontier (S.step hVA hperA).L
    rwa [show (S.step hVA hperA).L = S.L from rfl]
  · show x ∈ connectedComponentIn VA S.q
    exact S.connected_K.isPreconnected.subset_connectedComponentIn S.q_mem_K S.subset_K hxK

/-- **The pass fixes `K` whenever `K` is a component of `VA` — the descent cannot be a
`K`-replacement.**  If `K` is `connectedComponentIn VA w` for some `w` (i.e. `K` really is a
component of `VA`, as the intended reading of `Straddle` says), then `connectedComponentIn VA q`
is the *same* component, because `q ∈ K ⊆ connectedComponentIn VA q` and both are components of
`VA`.  Hence `(step S).K = S.K`: the pass is a fixed point on the component.

Consequence (recorded): the strict quantity for the descent is **not** an increment of
`frontierPart` under `step` — that increment is empty.  The pass fixes `L`, `q` *and* `K`, so it
is the identity on the `Straddle`; a recursion that alternates sides therefore cannot be built
from `step`, and the descent needs a move that changes the component `L` (i.e. genuinely the
mirror side, whose input is the crux-equivalent datum). -/
lemma step_K_eq_of_component (hVA : IsOpen VA)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ (q.1 + p, q.2) ∈ VA) (S : Straddle p VA VB) {w : ℝ × ℝ}
    (hKcomp : S.K = connectedComponentIn VA w) : (S.step hVA hperA).K = S.K := by
  have h1 : S.q ∈ connectedComponentIn VA w := hKcomp ▸ S.q_mem_K
  have h2 : connectedComponentIn VA w = connectedComponentIn VA S.q := connectedComponentIn_eq h1
  show connectedComponentIn VA S.q = S.K
  rw [hKcomp, ← h2]

end Straddle

/-- **The cross-side production is the crux.**  The crux conclusion `Zfix p VA ∩ Zfix p VB ≠ ∅`
holds if and only if some point of `Zfix p VA` has its `VA`-component meeting `Zfix p VB`.  By
`translate_mem_connectedComponentIn_of_mem_Zfix` that component is then automatically
`T`-invariant, so this is *not* a weakening of the crux: any lemma that produces a `Zfix p VB`
point from one-sided `Zfix p VA` data proves the crux outright.  This records that the "bridge"
step cannot be an easy local move. -/
lemma nonempty_inter_Zfix_iff_component_meets {p : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ (q.1 + p, q.2) ∈ VA) :
    (Zfix p VA ∩ Zfix p VB).Nonempty ↔
      ∃ z : ℝ × ℝ, z ∈ Zfix p VA ∧ (connectedComponentIn VA z ∩ Zfix p VB).Nonempty := by
  constructor
  · rintro ⟨z, hzA, hzB⟩
    exact ⟨z, hzA, z, mem_connectedComponentIn hzA.1, hzB⟩
  · rintro ⟨z, hzA, w, hwK, hwB⟩
    exact ⟨w, connectedComponentIn_subset_Zfix hVA hperA hzA hwK, hwB⟩

/-- **Hard-case descent.**  Let `VA, VB ⊆ strip a b` be open `T`-invariant sets covering the
strip, each containing a `T`-crossing, and suppose the unions of their `T`-fixed components are
disjoint.  Then `Zfix p VA` meets the part of the strip outside `VB`.

Proof: `Zfix p VA` is open, nonempty and (being disjoint from `Zfix p VB ≠ ∅`) not all of the
strip, hence — the strip being connected — some point `q` of the strip lies in `closure (Zfix p VA)`
but not in `Zfix p VA`; by `closure_Zfix_inter` such a point is outside `VA`, hence in `VB`.  The
component `C` of `VB` at `q` meets `Zfix p VA` (it is an open neighbourhood of `q`), and if the
translate of a point `z ∈ C ∩ Zfix p VA` were still in `C`, then `z` would be joined to its
translate inside `C ⊆ VB`, i.e. `z ∈ Zfix p VB`, contradicting disjointness.  So the path inside
`Zfix p VA` from `z` to its translate starts inside `C` and ends outside, hence meets `frontier C`,
and that frontier point is in `Zfix p VA` and (as `C` is a component of the open `VB`) outside
`VB`. -/
lemma exists_mem_Zfix_inter_compl {p a b : ℝ} (hab : a < b)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hsubA : VA ⊆ strip a b) (hsubB : VB ⊆ strip a b)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ (q.1 + p, q.2) ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ (q.1 + p, q.2) ∈ VB)
    (hcover : VA ∪ VB = strip a b)
    (hneA : (Zfix p VA).Nonempty)
    (hneB : (Zfix p VB).Nonempty)
    (hdisj : Disjoint (Zfix p VA) (Zfix p VB)) :
    (Zfix p VA ∩ (strip a b \ VB)).Nonempty := by
  set A : Set (ℝ × ℝ) := Zfix p VA with hA
  set B : Set (ℝ × ℝ) := Zfix p VB with hB
  have hAopen : IsOpen A := hA ▸ isOpen_Zfix hVA hperA
  have hAsub : A ⊆ strip a b := fun z hz => hsubA (Zfix_subset p VA hz)
  have hAne : A ≠ strip a b := by
    intro hEq
    obtain ⟨zB, hzB⟩ := hneB
    have hzA : zB ∈ A := by rw [hEq]; exact hsubB (Zfix_subset p VB hzB)
    exact Set.disjoint_left.mp hdisj hzA hzB
  have hex : ∃ q : ℝ × ℝ, q ∈ strip a b ∧ q ∈ closure A ∧ q ∉ A := by
    by_contra hcon
    push Not at hcon
    haveI : PreconnectedSpace ↥(strip a b) :=
      isPreconnected_iff_preconnectedSpace.mp (by
        have h1 : strip a b = (univ : Set ℝ) ×ˢ Set.Ioo a b := by ext q; simp [strip]
        rw [h1]; exact (Convex.prod convex_univ (convex_Ioo a b)).isPreconnected)
    have hcl : IsClopen {q : ↥(strip a b) | (q : ℝ × ℝ) ∈ A} := by
      refine ⟨?_, hAopen.preimage continuous_subtype_val⟩
      have h1 : {q : ↥(strip a b) | (q : ℝ × ℝ) ∈ A}
          = {q : ↥(strip a b) | (q : ℝ × ℝ) ∈ closure A} := by
        ext q
        exact ⟨fun hq => subset_closure hq, fun hq => hcon q q.2 hq⟩
      rw [h1]; exact isClosed_closure.preimage continuous_subtype_val
    have hne' : {q : ↥(strip a b) | (q : ℝ × ℝ) ∈ A}.Nonempty := by
      obtain ⟨z, hz⟩ := hneA
      exact ⟨⟨z, hAsub hz⟩, hz⟩
    have hone : {q : ↥(strip a b) | (q : ℝ × ℝ) ∈ A} = univ := by
      rcases (isClopen_iff.mp hcl) with h | h
      · exact absurd h (by intro hh; rw [hh] at hne'; exact hne'.ne_empty rfl)
      · exact h
    apply hAne
    refine Subset.antisymm hAsub ?_
    intro z hz
    have : (⟨z, hz⟩ : ↥(strip a b)) ∈ {q : ↥(strip a b) | (q : ℝ × ℝ) ∈ A} := by
      rw [hone]; trivial
    exact this
  obtain ⟨q₀, hq₀strip, hq₀cl, hq₀A⟩ := hex
  have hq₀VA : q₀ ∉ VA := by
    intro hq
    have hmem : q₀ ∈ closure A ∩ VA := ⟨hq₀cl, hq⟩
    rw [closure_Zfix_inter hVA hperA] at hmem
    exact hq₀A hmem
  have hq₀VB : q₀ ∈ VB := by
    have hmem : q₀ ∈ VA ∪ VB := by rw [hcover]; exact hq₀strip
    rcases hmem with h | h
    · exact absurd h hq₀VA
    · exact h
  set C : Set (ℝ × ℝ) := connectedComponentIn VB q₀ with hC
  have hCopen : IsOpen C := hVB.connectedComponentIn
  have hq₀C : q₀ ∈ C := mem_connectedComponentIn hq₀VB
  obtain ⟨z, hzC, hzA⟩ := mem_closure_iff_nhds.mp hq₀cl C (hCopen.mem_nhds hq₀C)
  have hzjoin : JoinedIn A z (z.1 + p, z.2) := hA ▸ joinedIn_Zfix hperA hzA
  have hTzC : (z.1 + p, z.2) ∉ C := by
    intro hTz
    have hCpc : IsPathConnected C :=
      (hCopen.isConnected_iff_isPathConnected).mp
        ⟨⟨q₀, hq₀C⟩, isPreconnected_connectedComponentIn⟩
    have hjoin : JoinedIn VB z (z.1 + p, z.2) :=
      (hCpc.joinedIn z hzC (z.1 + p, z.2) hTz).mono (connectedComponentIn_subset VB q₀)
    have hzB : z ∈ B := ⟨connectedComponentIn_subset VB q₀ hzC, hjoin⟩
    exact Set.disjoint_left.mp hdisj hzA hzB
  obtain ⟨γ, hγ⟩ := hzjoin
  have hγ0 : γ 0 = z := γ.source
  have hγ1 : γ 1 = (z.1 + p, z.2) := γ.target
  have h0C : γ 0 ∈ C := by rw [hγ0]; exact hzC
  have h1C : γ 1 ∉ C := by rw [hγ1]; exact hTzC
  obtain ⟨t, ht⟩ := exists_mem_frontier_of_path hCopen h0C h1C
  have hnotVB : γ t ∉ VB := by
    intro htVB
    have htcl : γ t ∈ closure C := frontier_subset_closure ht
    have htC : γ t ∉ C := by
      have h := ht
      rw [hCopen.frontier_eq] at h
      exact h.2
    have hC'open : IsOpen (connectedComponentIn VB (γ t)) := hVB.connectedComponentIn
    have htC' : γ t ∈ connectedComponentIn VB (γ t) := mem_connectedComponentIn htVB
    have hdisjCC' : Disjoint C (connectedComponentIn VB (γ t)) := by
      rw [Set.disjoint_left]
      intro u huC huC'
      have h1 : C = connectedComponentIn VB u := connectedComponentIn_eq huC
      have h2 : connectedComponentIn VB (γ t) = connectedComponentIn VB u :=
        connectedComponentIn_eq huC'
      have : γ t ∈ C := by
        rw [h1, ← h2]
        exact htC'
      exact htC this
    obtain ⟨u, huC', huC⟩ := mem_closure_iff_nhds.mp htcl (connectedComponentIn VB (γ t))
      (hC'open.mem_nhds htC')
    exact Set.disjoint_left.mp hdisjCC' huC huC'
  exact ⟨γ t, hA ▸ hγ t, hAsub (hγ t), hnotVB⟩

/-- The dual of `exists_mem_Zfix_inter_compl`: `Zfix p VB` meets the part of the strip outside
`VA`. -/
lemma exists_mem_Zfix_inter_compl' {p a b : ℝ} (hab : a < b)
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hsubA : VA ⊆ strip a b) (hsubB : VB ⊆ strip a b)
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ (q.1 + p, q.2) ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ (q.1 + p, q.2) ∈ VB)
    (hcover : VA ∪ VB = strip a b)
    (hneA : (Zfix p VA).Nonempty)
    (hneB : (Zfix p VB).Nonempty)
    (hdisj : Disjoint (Zfix p VA) (Zfix p VB)) :
    (Zfix p VB ∩ (strip a b \ VA)).Nonempty :=
  exists_mem_Zfix_inter_compl hab hVB hVA hsubB hsubA hperB hperA
    (by rw [Set.union_comm, hcover]) hneB hneA hdisj.symm

/-- **Last-entry switch.**  A path in the strip starting outside `VA` and ending in `VA` (with
`VA ∪ VB = strip a b` and `VA` open) has a last time `t₁` after which it stays inside `VA`; at
`t₁` the path lies in `VB` (or in `VA`, in which case it actually entered `VA` earlier). -/
lemma exists_switch_point {a b : ℝ}
    {VA VB : Set (ℝ × ℝ)} (hVA : IsOpen VA)
    (hcover : VA ∪ VB = strip a b)
    {γ : C(Set.Icc (0:ℝ) 1, ↥(strip a b))}
    (h0 : (γ 0 : ℝ × ℝ) ∉ VA) (h1 : (γ 1 : ℝ × ℝ) ∈ VA) :
    ∃ t₁ : Set.Icc (0:ℝ) 1, (∀ t : Set.Icc (0:ℝ) 1, t₁ < t → (γ t : ℝ × ℝ) ∈ VA) ∧
      ((γ t₁ : ℝ × ℝ) ∈ VB ∨ (γ t₁ : ℝ × ℝ) ∈ VA) := by
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  set S : Set ℝ := {s | s ∈ Set.Icc (0:ℝ) 1 ∧
      ∀ u : ℝ, s < u → u ≤ 1 → (γ (Set.projIcc 0 1 h01 u) : ℝ × ℝ) ∈ VA} with hS
  have h1S : (1:ℝ) ∈ S := ⟨⟨by norm_num, le_rfl⟩, fun u hu1 hu2 => by linarith⟩
  have hSne : S.Nonempty := ⟨1, h1S⟩
  have hSbd : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
  have ht₁le1 : sInf S ≤ 1 := csInf_le hSbd h1S
  have ht₁ge0 : (0:ℝ) ≤ sInf S := le_csInf hSne (fun b hb => hb.1.1)
  have ht₁I : sInf S ∈ Set.Icc (0:ℝ) 1 := ⟨ht₁ge0, ht₁le1⟩
  have ht₁S : sInf S ∈ S := by
    refine ⟨ht₁I, ?_⟩
    intro u hu1 hu2
    obtain ⟨s, hsS, hsu⟩ := exists_lt_of_csInf_lt hSne hu1
    exact hsS.2 u hsu hu2
  refine ⟨⟨sInf S, ht₁I⟩, ?_, ?_⟩
  · intro t ht
    have := ht₁S.2 (t : ℝ) ht t.2.2
    rwa [Set.projIcc_of_mem h01 t.2] at this
  · by_cases hcase : (γ (⟨sInf S, ht₁I⟩ : Set.Icc (0:ℝ) 1) : ℝ × ℝ) ∈ VA
    · exfalso
      obtain ⟨δ, hδ, hδmem⟩ : ∃ δ > 0, ∀ t : Set.Icc (0:ℝ) 1,
          dist t (⟨sInf S, ht₁I⟩ : Set.Icc (0:ℝ) 1) < δ → (γ t : ℝ × ℝ) ∈ VA := by
        have hopen : IsOpen ((fun t : Set.Icc (0:ℝ) 1 => (γ t : ℝ × ℝ)) ⁻¹' VA) :=
          hVA.preimage (continuous_subtype_val.comp γ.continuous)
        obtain ⟨δ, hδ, hδ'⟩ := Metric.isOpen_iff.mp hopen (⟨sInf S, ht₁I⟩ : Set.Icc (0:ℝ) 1) hcase
        exact ⟨δ, hδ, fun t ht => hδ' ht⟩
      rcases eq_or_lt_of_le ht₁ge0 with hzero | hpos
      · refine h0 ?_
        have : (⟨sInf S, ht₁I⟩ : Set.Icc (0:ℝ) 1) = 0 := Subtype.ext hzero.symm
        rwa [this] at hcase
      · have hslt : max 0 (sInf S - δ/2) < sInf S := max_lt hpos (by linarith)
        have hsS : max 0 (sInf S - δ/2) ∈ S := by
          refine ⟨⟨le_max_left 0 (sInf S - δ/2), le_trans (le_of_lt hslt) ht₁le1⟩, ?_⟩
          intro u hu1 hu2
          by_cases hut : u ≤ sInf S
          · have huI : u ∈ Set.Icc (0:ℝ) 1 :=
              ⟨by linarith [le_max_left (0:ℝ) (sInf S - δ/2)], hu2⟩
            have hdist : dist (⟨u, huI⟩ : Set.Icc (0:ℝ) 1)
                (⟨sInf S, ht₁I⟩ : Set.Icc (0:ℝ) 1) < δ := by
              rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
              constructor
              · have := le_max_right (0:ℝ) (sInf S - δ/2)
                linarith
              · linarith
            rw [Set.projIcc_of_mem h01 huI]
            exact hδmem ⟨u, huI⟩ hdist
          · exact ht₁S.2 u (lt_of_not_ge hut) hu2
        have : sInf S ≤ max 0 (sInf S - δ/2) := csInf_le hSbd hsS
        linarith
    · exact Or.inl (by
        have hmem : (γ (⟨sInf S, ht₁I⟩ : Set.Icc (0:ℝ) 1) : ℝ × ℝ) ∈ VA ∪ VB := by
          rw [hcover]; exact (γ _).2
        rcases hmem with h | h
        · exact absurd h hcase
        · exact h)

/-- **Clean case I of the cancellation step.**  If `VA` and `VB` are `T`-invariant, `q` has a
`T`-crossing inside `VA`, `r` has a `T`-crossing inside `VB`, and `r` can be joined to `q` inside
`VA`, then `r` itself is a common translate-joining point. -/
lemma common_crossing_of_joinedIn_VA {p : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ (q.1 + p, q.2) ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ (q.1 + p, q.2) ∈ VB)
    {q r : ℝ × ℝ}
    (hcrossA : JoinedIn VA q (q.1 + p, q.2))
    (hcrossB : JoinedIn VB r (r.1 - p, r.2))
    (hlam : JoinedIn VA r q) :
    r ∈ VA ∧ r ∈ VB ∧ JoinedIn VA r (r.1 + p, r.2) ∧ JoinedIn VB r (r.1 + p, r.2) := by
  refine ⟨hlam.source_mem, hcrossB.source_mem, ?_, ?_⟩
  · -- r --> q --> T q <-- T r, all inside VA
    have h1 : JoinedIn VA r (q.1 + p, q.2) := hlam.trans hcrossA
    have h2 : JoinedIn VA (q.1 + p, q.2) (r.1 + p, r.2) := (joinedIn_translate hperA hlam).symm
    exact h1.trans h2
  · -- T r --> r inside VB (translate the VB-crossing), then reverse
    have h1 : JoinedIn VB (r.1 + p, r.2) r := by
      simpa using joinedIn_translate hperB hcrossB
    exact h1.symm

/-- **Clean case II of the cancellation step.**  Same hypotheses, but the connecting path from
`r` to `q` lies inside `VB`; then `q` is a common translate-joining point. -/
lemma common_crossing_of_joinedIn_VB {p : ℝ} {VA VB : Set (ℝ × ℝ)}
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ (q.1 + p, q.2) ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ (q.1 + p, q.2) ∈ VB)
    {q r : ℝ × ℝ}
    (hcrossA : JoinedIn VA q (q.1 + p, q.2))
    (hcrossB : JoinedIn VB r (r.1 - p, r.2))
    (hlam : JoinedIn VB r q) :
    q ∈ VA ∧ q ∈ VB ∧ JoinedIn VA q (q.1 + p, q.2) ∧ JoinedIn VB q (q.1 + p, q.2) := by
  refine ⟨hcrossA.source_mem, hlam.target_mem, hcrossA, ?_⟩
  · -- T q <-- T r --> r --> q inside VB, then reverse
    have h1 : JoinedIn VB (r.1 + p, r.2) r := by
      simpa using joinedIn_translate hperB hcrossB
    have h2 : JoinedIn VB (q.1 + p, q.2) (r.1 + p, r.2) :=
      (joinedIn_translate hperB hlam).symm
    exact ((h2.trans h1).trans hlam).symm

/-- **Pannwitz–Kuperberg cancellation for a two-set cover of a periodic strip.**

Two open `T`-invariant subsets `VA`, `VB` of the strip `a < q.2 < b` (with `T q = (q.1+p, q.2)`,
`p > 0`) covering the strip, each containing a path joining a point to its translate, have a
common translate-joining path in `VA ∩ VB`. -/
theorem path_to_translate_of_open_cover_cancellation {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {VA VB : Set (ℝ × ℝ)}
    (hVA : IsOpen VA) (hVB : IsOpen VB)
    (hsubA : VA ⊆ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b})
    (hsubB : VB ⊆ {q : ℝ × ℝ | a < q.2 ∧ q.2 < b})
    (hperA : ∀ q : ℝ × ℝ, q ∈ VA ↔ (q.1 + p, q.2) ∈ VA)
    (hperB : ∀ q : ℝ × ℝ, q ∈ VB ↔ (q.1 + p, q.2) ∈ VB)
    (hcover : VA ∪ VB = {q : ℝ × ℝ | a < q.2 ∧ q.2 < b})
    (hwindA : ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
      (∀ t, γ t ∈ VA) ∧ (γ 0).2 = (γ 1).2 ∧ γ 1 = ((γ 0).1 + p, (γ 0).2))
    (hwindB : ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
      (∀ t, γ t ∈ VB) ∧ (γ 0).2 = (γ 1).2 ∧ γ 0 = ((γ 1).1 + p, (γ 1).2)) :
    ∃ z : ℝ × ℝ, a < z.2 ∧ z.2 < b ∧ z ∈ VA ∩ VB ∧
      ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
        γ 0 = z ∧ γ 1 = (z.1 + p, z.2) ∧ ∀ t, γ t ∈ VA ∩ VB := by
  have hsubA' : VA ⊆ strip a b := hsubA
  have hsubB' : VB ⊆ strip a b := hsubB
  have hcover' : VA ∪ VB = strip a b := hcover
  have hwA : ∃ z : ℝ × ℝ, z ∈ VA ∧ JoinedIn VA z (z.1 + p, z.2) := by
    obtain ⟨γ, hmem, -, hend⟩ := hwindA
    exact ⟨γ 0, hmem 0, ⟨⟨γ, rfl, hend⟩, fun t => hmem t⟩⟩
  have hwB : ∃ z : ℝ × ℝ, z ∈ VB ∧ JoinedIn VB z (z.1 - p, z.2) := by
    obtain ⟨γ, hmem, -, hend⟩ := hwindB
    have h1 : (γ 1 : ℝ × ℝ).1 = (γ 0).1 - p := by
      have := congrArg Prod.fst hend; simp at this; linarith
    have h2 : (γ 1 : ℝ × ℝ).2 = (γ 0).2 := by
      have := congrArg Prod.snd hend; simp at this; linarith
    have hy : (γ 1 : ℝ × ℝ) = ((γ 0).1 - p, (γ 0).2) := by ext <;> assumption
    exact ⟨γ 0, hmem 0, ⟨⟨γ, rfl, hy⟩, fun t => hmem t⟩⟩
  obtain ⟨z, hzA, hzB, hjoinA, hjoinB⟩ :=
    common_crossing_of_open_cover hp hab hVA hVB hsubA' hsubB' hperA hperB hcover' hwA hwB
  have hzstrip : z ∈ strip a b := hsubA' hzA
  have hTzA : (z.1 + p, z.2) ∈ VA := (hperA z).mp hzA
  have hTzstrip : (z.1 + p, z.2) ∈ strip a b := hsubA' hTzA
  haveI : ConnectedSpace ↥(strip a b) := strip_connectedSpace hab
  haveI : LocallyPathConnectedSpace ↥(strip a b) := strip_locallyPathConnectedSpace a b
  haveI : SimplyConnectedSpace ↥(strip a b) := strip_simplyConnectedSpace hab
  set A : Set ↥(strip a b) := {q | (q : ℝ × ℝ) ∉ VA} with hA
  set B : Set ↥(strip a b) := {q | (q : ℝ × ℝ) ∉ VB} with hB
  have hAc : Aᶜ = {q : ↥(strip a b) | (q : ℝ × ℝ) ∈ VA} := by
    rw [hA]; ext q; simp
  have hBc : Bᶜ = {q : ↥(strip a b) | (q : ℝ × ℝ) ∈ VB} := by
    rw [hB]; ext q; simp
  have hABc : (A ∪ B)ᶜ = {q : ↥(strip a b) | (q : ℝ × ℝ) ∈ VA ∧ (q : ℝ × ℝ) ∈ VB} := by
    rw [hA, hB]; ext q; simp [not_or]
  have hAcl : IsClosed A := by
    rw [hA]
    exact (hVA.preimage continuous_subtype_val).isClosed_compl
  have hBcl : IsClosed B := by
    rw [hB]
    exact (hVB.preimage continuous_subtype_val).isClosed_compl
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro q hqA hqB
    rw [hA] at hqA
    rw [hB] at hqB
    have hmem : (q : ℝ × ℝ) ∈ VA ∪ VB := by rw [hcover']; exact q.2
    rcases hmem with h | h
    · exact hqA h
    · exact hqB h
  set x : ↥(strip a b) := ⟨z, hzstrip⟩ with hx
  set y : ↥(strip a b) := ⟨(z.1 + p, z.2), hTzstrip⟩ with hy
  have hmemA : x ∉ A ∪ B := by
    rw [Set.mem_union, not_or]
    refine ⟨?_, ?_⟩
    · rw [hA]; exact fun h => h (by rw [hx]; exact hzA)
    · rw [hB]; exact fun h => h (by rw [hx]; exact hzB)
  have hmemB : y ∉ A ∪ B := by
    rw [Set.mem_union, not_or]
    refine ⟨?_, ?_⟩
    · rw [hA]; exact fun h => h (by rw [hy]; exact hTzA)
    · rw [hB]; exact fun h => h (by rw [hy]; exact (hperB z).mp hzB)
  have hJA : JoinedIn Aᶜ x y := by
    rw [hAc, hx, hy]
    exact joinedIn_subtype_of_joinedIn (S := strip a b) hsubA' hjoinA.source_mem hjoinA.target_mem hjoinA
  have hJB : JoinedIn Bᶜ x y := by
    rw [hBc, hx, hy]
    exact joinedIn_subtype_of_joinedIn (S := strip a b) hsubB' hjoinB.source_mem hjoinB.target_mem hjoinB
  have hmono : ∀ t : ↥(strip a b), Subsingleton (FundamentalGroup ↥(strip a b) t) :=
    fun t => inferInstance
  have hfin := Commons.Topology.Jordan.two_disjoint_closed_not_separating hmono hAcl hBcl hdisj
    hmemA hmemB hJA hJB
  obtain ⟨γf, hγf⟩ := hfin
  refine ⟨z, hzstrip.1, hzstrip.2, ⟨hzA, hzB⟩, ?_⟩
  refine ⟨⟨fun t => (γf t : ℝ × ℝ),
    continuous_subtype_val.comp γf.continuous⟩, ?_, ?_, ?_⟩
  · show (((γf 0 : ↥(strip a b)) : ℝ × ℝ)) = z
    rw [γf.source, hx]
  · show (((γf 1 : ↥(strip a b)) : ℝ × ℝ)) = (z.1 + p, z.2)
    rw [γf.target, hy]
  · intro t
    have ht := hγf t
    rw [hABc] at ht
    exact ⟨ht.1, ht.2⟩

end Commons.Topology.Strip
