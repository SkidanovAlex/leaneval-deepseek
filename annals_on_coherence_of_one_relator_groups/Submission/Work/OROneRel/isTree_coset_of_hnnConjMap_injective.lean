import Mathlib
import Submission.Work.OROneRel.hnnConjSplit
import Submission.Work.OROneRel.hnnCosetWord
import Submission.Work.OROneRel.britton_hnnConjMap_injective
import Submission.Work.OROneRel.graded_hnn_coset
import Submission.Work.OROneRel.isTree_lineGraph_iff
import Submission.Work.ORLocInd.CohenLyndon.hnnSetup
import Submission.Work.ORBassSerre.HNN.Tree
import Submission.Work.ORDunwoody.Lemmas.GraphQuiverTree
import Submission.Work.ORBassSerre.Tree.Reduction.isReduced_cons_iff

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The coset graph of a pair `(H, t)` with `HNN(↥H, A, B, φ) ≅ G` is a tree

Let `G` be a group, `H ≤ G` and `t : G`, and suppose that the canonical comparison map
`hnnConjMap H t : HNN(↥H, H ⊓ t⁻¹Ht, t(H ⊓ t⁻¹Ht)t⁻¹, conj_t) →* G` is injective and that
`H` and `t` generate `G`.  Then `G` *is* the HNN extension of `H` with stable letter `t`, and the
coset graph `GradedHNN.Coset H t` (vertices the left cosets of `H`, edges `{gH, gtH}`) is the
Bass--Serre tree of that HNN extension; in particular it is a tree.

The content of the proof is the normal form of the HNN extension (Britton's lemma).  A reduced
closed path in the coset graph is lifted to a word `h₁t^{ε₁} h₂t^{ε₂} ⋯ hₙt^{εₙ}` with
`hᵢ ∈ H` and `εᵢ = ±1` which represents an element of `H`; reducedness of the path is exactly the
statement that no "pinch" `t^{ε_i}h_{i+1}t^{-ε_i}` with `h_{i+1} ∈ toSubgroup ε_i` occurs, i.e. that
the word is reduced, whence it must be empty by Britton's lemma.

## Main results

* `Work.OROneRel.noPinch_hnnLiftAux` : the word attached to a reduced path has no pinch.
* `Work.OROneRel.britton_of_injective` : Britton's lemma for the pair `(H, t)` (using only the
  injectivity of `hnnConjMap`), in the "the word lies in `H`" form.
* `Work.OROneRel.isTree_coset_of_hnnConjMap_injective` : the coset graph is a tree.
-/

namespace Work.OROneRel

open Quiver

universe u

variable {G : Type u} [Group G]

/-! ## Lifting a path to a word -/

/-- One step of the lift: given `g` with `cmk H t g = c` and an arrow `e : c ⟶ d`, produce a
letter `(δ, h)` such that `g * h * t^δ` is again a representative of `d`. -/
theorem exists_step (H : Subgroup G) (t : G) (g : G) {c d : GradedHNN.Coset H t}
    (e : c ⟶ d) (hg : GradedHNN.cmk H t g = c) :
    ∃ x : ℤˣ × ↥H, GradedHNN.cmk H t (g * ((x.2 : G) * t ^ (x.1 : ℤ))) = d := by
  obtain ⟨a, h | h⟩ := e.down
  · obtain ⟨hc, hd⟩ := h
    have hmem : g⁻¹ * a ∈ H := by
      have h1 : GradedHNN.cmk H t g = GradedHNN.cmk H t a := by rw [hg, hc]
      rwa [GradedHNN.cmk_eq_iff] at h1
    refine ⟨(1, ⟨g⁻¹ * a, hmem⟩), ?_⟩
    refine ((GradedHNN.cmk_eq_iff H t).mpr ?_).trans hd.symm
    simp only [Subtype.coe_mk, Units.val_one, zpow_one]
    convert H.one_mem using 1
    group
  · obtain ⟨hd, hc⟩ := h
    have hmem : g⁻¹ * (a * t) ∈ H := by
      have h1 : GradedHNN.cmk H t g = GradedHNN.cmk H t (a * t) := by rw [hg, hc]
      rwa [GradedHNN.cmk_eq_iff] at h1
    refine ⟨(-1, ⟨g⁻¹ * (a * t), hmem⟩), ?_⟩
    refine ((GradedHNN.cmk_eq_iff H t).mpr ?_).trans hd.symm
    simp only [Subtype.coe_mk, Units.val_neg, Units.val_one, zpow_neg_one]
    convert H.one_mem using 1
    group

/-- The letter chosen by `exists_step`. -/
noncomputable def stepOf (H : Subgroup G) (t : G) (g : G) {c d : GradedHNN.Coset H t}
    (e : c ⟶ d) (hg : GradedHNN.cmk H t g = c) : ℤˣ × ↥H :=
  Classical.choose (exists_step H t g e hg)

theorem stepOf_spec (H : Subgroup G) (t : G) (g : G) {c d : GradedHNN.Coset H t}
    (e : c ⟶ d) (hg : GradedHNN.cmk H t g = c) :
    GradedHNN.cmk H t (g * (((stepOf H t g e hg).2 : G) * t ^ ((stepOf H t g e hg).1 : ℤ))) =
      d :=
  Classical.choose_spec (exists_step H t g e hg)

/-- **The lift of a path of the coset graph to a word of the HNN extension.**  Starting from a
representative `g` of the start vertex, each arrow is lifted to a letter `(δ, h)`, multiplying the
representative on the right by `h · t^δ`. -/
noncomputable def hnnLiftAux (H : Subgroup G) (t : G) (v : GradedHNN.Coset H t) (g : G)
    (hg : GradedHNN.cmk H t g = v) :
    (w : GradedHNN.Coset H t) → Quiver.Path v w →
      { L : List (ℤˣ × ↥H) // GradedHNN.cmk H t (g * hnnWord H t L) = w }
  | _, .nil => ⟨[], by rw [hnnWord_nil, mul_one]; exact hg⟩
  | _, .cons p e =>
      let ih := hnnLiftAux H t v g hg _ p
      let x := stepOf H t (g * hnnWord H t ih.1) e ih.2
      ⟨ih.1 ++ [x], by
        rw [hnnWord_concat]
        show GradedHNN.cmk H t (g * (hnnWord H t ih.1 * ((x.2 : G) * t ^ (x.1 : ℤ)))) = _
        rw [← mul_assoc]
        exact stepOf_spec H t (g * hnnWord H t ih.1) e ih.2⟩

/-- The defining property of the lifted word: it represents the endpoint of the path. -/
theorem hnnLiftAux_vertex (H : Subgroup G) (t : G) (v : GradedHNN.Coset H t) (g : G)
    (hg : GradedHNN.cmk H t g = v) (w : GradedHNN.Coset H t) (p : Quiver.Path v w) :
    GradedHNN.cmk H t (g * hnnWord H t (hnnLiftAux H t v g hg w p).1) = w :=
  (hnnLiftAux H t v g hg w p).2

/-- The word attached to a path has as many letters as the path has arrows. -/
theorem hnnLiftAux_length (H : Subgroup G) (t : G) (v : GradedHNN.Coset H t) (g : G)
    (hg : GradedHNN.cmk H t g = v) :
    ∀ (w : GradedHNN.Coset H t) (p : Quiver.Path v w),
      (hnnLiftAux H t v g hg w p).1.length = p.length := by
  intro w p
  induction p with
  | nil => rfl
  | cons p e ih =>
      simp only [hnnLiftAux, List.length_append, List.length_singleton, ih,
        Quiver.Path.length_cons]

/-! ## The reduction rules of the HNN extension -/

/-- The relation `t a t⁻¹ = φ a` of the HNN extension, for `a` in the first associated subgroup. -/
theorem hnnEdgeA_conj_mem (H : Subgroup G) (t : G) {a : G} (ha : a ∈ hnnEdgeA H t) :
    t * a * t⁻¹ ∈ H := by
  have hcoe : (((hnnConjEquiv H t (⟨⟨a, hnnEdgeA_le H t ha⟩, ha⟩ :
      (hnnEdgeA H t).subgroupOf H)) : (hnnEdgeB H t).subgroupOf H) : G) = t * a * t⁻¹ :=
    hnnConjEquiv_coe H t _
  rw [← hcoe]
  exact hnnEdgeB_le H t (hnnConjEquiv H t _).2

/-- The relation `t⁻¹ b t = φ⁻¹ b` of the HNN extension, for `b` in the second associated
subgroup. -/
theorem hnnEdgeB_conj_mem (H : Subgroup G) (t : G) {b : G} (hb : b ∈ hnnEdgeB H t) :
    t⁻¹ * b * t ∈ H := by
  obtain ⟨a, ha, hconj⟩ := Subgroup.mem_map.mp hb
  have hb' : b = t * a * t⁻¹ := by
    rw [← hconj]
    exact MulAut.conj_apply t a
  rw [hb']
  have : t⁻¹ * (t * a * t⁻¹) * t = a := by group
  rw [this]
  exact hnnEdgeA_le H t ha

/-! ## The key junction step -/

/-- **The key combinatorial step.**  If the word of a reduced path continues with a letter `x`
after a letter `y`, then the pair cannot be a pinch: the extra factor
`(y₂ t^{ε_y})(x₂ t^{ε_x})` would lie in `H`, making the new vertex equal to the one before `y`,
which contradicts reducedness (two consecutive arrows would be mutually inverse). -/
theorem noPinch_step (H : Subgroup G) (t : G) {v b' b c : GradedHNN.Coset H t}
    (p' : Quiver.Path v b') (e' : b' ⟶ b) (e : b ⟶ c) (g : G) (L₁ : List (ℤˣ × ↥H))
    (y x : ℤˣ × ↥H)
    (hcmk' : GradedHNN.cmk H t (g * hnnWord H t L₁) = b')
    (hy : GradedHNN.cmk H t ((g * hnnWord H t L₁) * ((y.2 : G) * t ^ (y.1 : ℤ))) = b)
    (hx : GradedHNN.cmk H t ((g * hnnWord H t (L₁ ++ [y])) * ((x.2 : G) * t ^ (x.1 : ℤ))) = c)
    (hred : ((p'.cons e').cons e).IsReduced) :
    ¬ (x.2 ∈ hnnEdgeSubBase H t y.1 ∧ x.1 = -y.1) := by
  rintro ⟨hxin, hx1⟩
  -- the reduced factor `t^{ε_y} x₂ t^{ε_x}` attached to `y₂` lies in `H`
  have hfactor : ((y.2 : G) * t ^ (y.1 : ℤ)) * ((x.2 : G) * t ^ (x.1 : ℤ)) ∈ H := by
    rcases Int.units_eq_one_or y.1 with hy1 | hy1
    · have hA : (x.2 : G) ∈ hnnEdgeA H t := by
        have h1 : x.2 ∈ hnnEdgeSubBase H t (1 : ℤˣ) := by rw [hy1] at hxin; exact hxin
        rwa [hnnEdgeSubBase_one, Subgroup.mem_subgroupOf] at h1
      have hc := hnnEdgeA_conj_mem H t hA
      have hv1 : (y.1 : ℤ) = 1 := by rw [hy1]; rfl
      have hv2 : (x.1 : ℤ) = -1 := by rw [hx1, hy1]; rfl
      rw [hv1, hv2, zpow_one, zpow_neg_one]
      have heq : (y.2 : G) * t * ((x.2 : G) * t⁻¹)
          = (y.2 : G) * (t * (x.2 : G) * t⁻¹) := by group
      rw [heq]
      exact H.mul_mem y.2.2 hc
    · have hB : (x.2 : G) ∈ hnnEdgeB H t := by
        have h1 : x.2 ∈ hnnEdgeSubBase H t (-1 : ℤˣ) := by rw [hy1] at hxin; exact hxin
        rwa [hnnEdgeSubBase_neg_one, Subgroup.mem_subgroupOf] at h1
      have hc := hnnEdgeB_conj_mem H t hB
      have hv1 : (y.1 : ℤ) = -1 := by rw [hy1]; rfl
      have hv2 : (x.1 : ℤ) = 1 := by rw [hx1, hy1]; rfl
      rw [hv1, hv2, zpow_neg_one, zpow_one]
      have heq : (y.2 : G) * t⁻¹ * ((x.2 : G) * t)
          = (y.2 : G) * (t⁻¹ * (x.2 : G) * t) := by group
      rw [heq]
      exact H.mul_mem y.2.2 hc
  -- consequently the new vertex is the one preceding `y`
  have hcb : c = b' := by
    rw [← hx]
    have hr : (g * hnnWord H t (L₁ ++ [y])) * ((x.2 : G) * t ^ (x.1 : ℤ))
        = (g * hnnWord H t L₁)
          * (((y.2 : G) * t ^ (y.1 : ℤ)) * ((x.2 : G) * t ^ (x.1 : ℤ))) := by
      rw [hnnWord_concat]; group
    rw [hr, GradedHNN.cmk_mul_mem H t (g * hnnWord H t L₁) hfactor, hcmk']
  -- so the two consecutive arrows are mutually inverse, contradicting reducedness
  have hlast : ∀ (p'' : Quiver.Path v c) (e'' : c ⟶ b),
      (p'.cons e') = p''.cons e'' → e ≠ Quiver.reverse e'' :=
    ((Work.ORBassSerre.Tree.Reduction.isReduced_cons_iff (p'.cons e') e).mp hred).2
  subst hcb
  exact hlast p' e' rfl (Subsingleton.elim e (Quiver.reverse e'))

/-! ## Reduced paths have pinch free words -/

/-- **A reduced path of the coset graph lifts to a pinch free word.** -/
theorem noPinch_hnnLiftAux (H : Subgroup G) (t : G) (v : GradedHNN.Coset H t) (g : G)
    (hg : GradedHNN.cmk H t g = v) :
    ∀ (w : GradedHNN.Coset H t) (p : Quiver.Path v w),
      p.IsReduced → NoPinch H t (hnnLiftAux H t v g hg w p).1 := by
  intro w p
  induction p with
  | nil =>
      intro _
      show NoPinch H t []
      exact noPinch_nil H t
  | cons p e ih =>
      intro hp
      obtain ⟨hp', -⟩ := (Work.ORBassSerre.Tree.Reduction.isReduced_cons_iff p e).mp hp
      cases p with
      | nil =>
          show NoPinch H t [stepOf H t (g * hnnWord H t (hnnLiftAux H t v g hg v Quiver.Path.nil).1) e
                (hnnLiftAux H t v g hg v Quiver.Path.nil).2]
          exact noPinch_singleton H t _
      | cons p' e' =>
          show NoPinch H t ((hnnLiftAux H t v g hg _ (p'.cons e')).1 ++
            [stepOf H t (g * hnnWord H t (hnnLiftAux H t v g hg _ (p'.cons e')).1) e
              (hnnLiftAux H t v g hg _ (p'.cons e')).2])
          have hun1 : (hnnLiftAux H t v g hg _ (p'.cons e')).1
              = (hnnLiftAux H t v g hg _ p').1 ++
                [stepOf H t (g * hnnWord H t (hnnLiftAux H t v g hg _ p').1) e'
                  (hnnLiftAux H t v g hg _ p').2] := rfl
          refine List.IsChain.append (ih hp') (noPinch_singleton H t _) ?_
          intro z hz z' hz'
          rw [List.head?_cons, Option.mem_some_iff] at hz'
          rw [← hz']
          rw [hun1, List.getLast?_concat, Option.mem_some_iff] at hz
          rw [← hz]
          refine noPinch_step H t p' e' e g _ _ _
            (hnnLiftAux_vertex H t v g hg _ p')
            (stepOf_spec H t (g * hnnWord H t (hnnLiftAux H t v g hg _ p').1) e'
              (hnnLiftAux H t v g hg _ p').2) ?_ hp
          have hwordeq : hnnWord H t (hnnLiftAux H t v g hg _ (p'.cons e')).1
              = hnnWord H t ((hnnLiftAux H t v g hg _ p').1 ++
                  [stepOf H t (g * hnnWord H t (hnnLiftAux H t v g hg _ p').1) e'
                    (hnnLiftAux H t v g hg _ p').2]) := by rw [hun1]
          rw [← hwordeq]
          exact stepOf_spec H t
            (g * hnnWord H t (hnnLiftAux H t v g hg _ (p'.cons e')).1) e
            (hnnLiftAux H t v g hg _ (p'.cons e')).2

/-! ## The coset graph is a tree -/

theorem isTree_coset_of_hnnConjMap_injective {G : Type u} [Group G] (H : Subgroup G) (t : G)
    (hgen : H ⊔ Subgroup.closure ({t} : Set G) = ⊤)
    (hinj : Function.Injective (Work.OROneRel.hnnConjMap H t)) :
    Work.ORBassSerre.IsTree (Work.OROneRel.GradedHNN.Coset H t) := by
  refine ⟨fun x y => GradedHNN.connected_coset H t hgen x y, ?_⟩
  intro a p hp
  by_contra hne
  have hlen : p.length ≠ 0 := fun h0 => hne (Quiver.Path.eq_nil_of_length_zero p h0)
  obtain ⟨g₀, hg₀⟩ := Quotient.exists_rep a
  have hLlen : (hnnLiftAux H t a g₀ hg₀ a p).1.length = p.length :=
    hnnLiftAux_length H t a g₀ hg₀ a p
  have hneL : (hnnLiftAux H t a g₀ hg₀ a p).1 ≠ [] := by
    intro hnil
    rw [hnil] at hLlen
    exact hlen hLlen.symm
  have hprod : hnnWord H t (hnnLiftAux H t a g₀ hg₀ a p).1 ∈ H := by
    have hvert := hnnLiftAux_vertex H t a g₀ hg₀ a p
    have h1 : (g₀ * hnnWord H t (hnnLiftAux H t a g₀ hg₀ a p).1)⁻¹ * g₀ ∈ H :=
      (GradedHNN.cmk_eq_iff H t).mp (by rw [hvert]; exact hg₀.symm)
    have h2 : (g₀ * hnnWord H t (hnnLiftAux H t a g₀ hg₀ a p).1)⁻¹ * g₀
        = (hnnWord H t (hnnLiftAux H t a g₀ hg₀ a p).1)⁻¹ := by group
    rw [h2] at h1
    simpa using H.inv_mem h1
  exact hneL (britton_hnnConjMap_injective H t hinj _ (noPinch_hnnLiftAux H t a g₀ hg₀ a p hp) hprod)

end Work.OROneRel
