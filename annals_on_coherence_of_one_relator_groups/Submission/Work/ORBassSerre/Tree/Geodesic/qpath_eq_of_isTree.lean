import Mathlib
import Submission.Work.ORBassSerre.Tree.Basic
import Submission.Work.ORBassSerre.Tree.Reduction.qpath_exists_reducesTo_isReduced
import Submission.Work.ORBassSerre.Tree.Prefix.qpath_exists_eq_comp_of_comp_eq

namespace Work.ORBassSerre.Tree.Geodesic

open Quiver

variable {V : Type*} [Quiver V]

/-- `DeleteBacktrack p w` unpacked: `p` has a deletable backtrack exactly when `p` can be
written as `p₁ · e · e⁻¹ · p₂` for some arrow `e`. -/
theorem deleteBacktrack_iff [Quiver.HasReverse V] {a b : V} {p w : Quiver.Path a b} :
    Quiver.Path.DeleteBacktrack p w ↔
      ∃ (x y : V) (p₁ : Quiver.Path a x) (e : x ⟶ y) (p₂ : Quiver.Path x b),
        p = p₁.comp (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂)) ∧
          w = p₁.comp p₂ := by
  constructor
  · intro h
    cases h with
    | intro p₁ e p₂ => exact ⟨_, _, p₁, e, p₂, rfl, rfl⟩
  · rintro ⟨x, y, p₁, e, p₂, rfl, rfl⟩
    exact Quiver.Path.DeleteBacktrack.intro p₁ e p₂

/-- **Junction lemma.**  If a backtrack can be deleted from `u.comp v` and `u`, `v` are both
reduced, then the deleted backtrack straddles the junction: the last arrow of `u` is the reverse
of the first arrow of `v`. -/
theorem deleteBacktrack_comp_junction [Quiver.HasReverse V] {a b c : V}
    {u : Quiver.Path a b} {v : Quiver.Path b c} {w : Quiver.Path a c}
    (hu : u.IsReduced) (hv : v.IsReduced)
    (h : Quiver.Path.DeleteBacktrack (u.comp v) w) :
    ∃ (x : V) (f : x ⟶ b) (u' : Quiver.Path a x) (v' : Quiver.Path x c),
      u = u'.cons f ∧ v = (Quiver.reverse f).toPath.comp v' ∧ w = u'.comp v' := by
  obtain ⟨x₀, y₀, p₁, e, p₂, heq, hw⟩ := deleteBacktrack_iff.1 h
  rcases Tree.Prefix.qpath_exists_eq_comp_of_comp_eq (u := u) (v := v) (u' := p₁)
      (v' := e.toPath.comp ((Quiver.reverse e).toPath.comp p₂)) heq with ⟨r, hr⟩ | ⟨r, hr⟩
  · -- the backtrack lies strictly inside `v`
    exfalso
    have h1 : u.comp v
        = u.comp (r.comp (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂))) := by
      rw [hr, Quiver.Path.comp_assoc] at heq
      exact heq
    have hv' : v = r.comp (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂)) :=
      Quiver.Path.comp_injective_right u h1
    exact (hv (r.comp p₂) (by rw [hv']; exact Quiver.Path.DeleteBacktrack.intro r e p₂)).elim
  · -- the backtrack is at or after the junction
    have key : r.comp v = e.toPath.comp ((Quiver.reverse e).toPath.comp p₂) := by
      have h1 : u.comp v = p₁.comp (r.comp v) := by rw [hr, Quiver.Path.comp_assoc]
      rw [h1] at heq
      exact Quiver.Path.comp_injective_right p₁ heq
    rcases Tree.Prefix.qpath_exists_eq_comp_of_comp_eq (u := r) (v := v) (u' := e.toPath)
        (v' := (Quiver.reverse e).toPath.comp p₂) key with ⟨r₂, hr₂⟩ | ⟨r₂, hr₂⟩
    · -- `e.toPath = r.comp r₂`
      have hlen : 1 = r.length + r₂.length := by
        simpa using congrArg Quiver.Path.length hr₂
      rcases Nat.eq_zero_or_pos r.length with h0 | hpos
      · -- the whole of `v` contains the backtrack
        exfalso
        have hxb : x₀ = b := Quiver.Path.eq_of_length_zero r h0
        subst hxb
        have hrnil : r = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero r h0
        have hvY : v = e.toPath.comp ((Quiver.reverse e).toPath.comp p₂) := by
          rw [hrnil, Quiver.Path.nil_comp] at key
          exact key
        have hdb : Quiver.Path.DeleteBacktrack v p₂ := by
          rw [hvY]
          simpa using
            (Quiver.Path.DeleteBacktrack.intro (Quiver.Path.nil : Quiver.Path x₀ x₀) e p₂)
        exact (hv p₂ hdb).elim
      · -- the junction
        have h2 : r₂.length = 0 := by omega
        have hby : b = y₀ := Quiver.Path.eq_of_length_zero r₂ h2
        subst hby
        have hr₂nil : r₂ = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero r₂ h2
        have hre : r = e.toPath := by
          rw [hr₂nil, Quiver.Path.comp_nil] at hr₂
          exact hr₂.symm
        refine ⟨x₀, e, p₁, p₂, ?_, ?_, hw⟩
        · rw [hr, hre, Quiver.Path.comp_toPath_eq_cons]
        · rw [hre] at key
          exact Quiver.Path.comp_injective_right e.toPath key
    · -- `r = e.toPath.comp r₂`
      have key2 : r₂.comp v = (Quiver.reverse e).toPath.comp p₂ := by
        rw [hr₂, Quiver.Path.comp_assoc] at key
        exact Quiver.Path.comp_injective_right e.toPath key
      rcases Tree.Prefix.qpath_exists_eq_comp_of_comp_eq (u := r₂) (v := v)
          (u' := (Quiver.reverse e).toPath) (v' := p₂) key2 with ⟨r₃, hr₃⟩ | ⟨r₃, hr₃⟩
      · -- `(reverse e).toPath = r₂.comp r₃`
        have hlen : 1 = r₂.length + r₃.length := by
          simpa using congrArg Quiver.Path.length hr₃
        rcases Nat.eq_zero_or_pos r₂.length with h0 | hpos
        · -- the junction
          have hyb : y₀ = b := Quiver.Path.eq_of_length_zero r₂ h0
          subst hyb
          have hr₂nil : r₂ = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero r₂ h0
          refine ⟨x₀, e, p₁, p₂, ?_, ?_, hw⟩
          · rw [hr, hr₂, hr₂nil, Quiver.Path.comp_nil, Quiver.Path.comp_toPath_eq_cons]
          · rw [hr₂nil, Quiver.Path.nil_comp] at key2
            exact key2
        · -- the backtrack lies strictly inside `u`
          exfalso
          have h3 : r₃.length = 0 := by omega
          have hbx : b = x₀ := Quiver.Path.eq_of_length_zero r₃ h3
          subst hbx
          have hr₃nil : r₃ = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero r₃ h3
          have hrev : r₂ = (Quiver.reverse e).toPath := by
            rw [hr₃nil, Quiver.Path.comp_nil] at hr₃
            exact hr₃.symm
          have hu_eq : u = (p₁.cons e).cons (Quiver.reverse e) := by
            rw [hr, hr₂, hrev]
            simp
          have hdb : Quiver.Path.DeleteBacktrack u p₁ := by
            rw [hu_eq]
            simpa using
              (Quiver.Path.DeleteBacktrack.intro p₁ e (Quiver.Path.nil : Quiver.Path b b))
          exact (hu p₁ hdb).elim
      · -- `r₂ = (reverse e).toPath.comp r₃`
        exfalso
        have hu_eq : u = p₁.comp (e.toPath.comp ((Quiver.reverse e).toPath.comp r₃)) := by
          rw [hr, hr₂, hr₃]
        have hdb : Quiver.Path.DeleteBacktrack u (p₁.comp r₃) := by
          rw [hu_eq]
          exact Quiver.Path.DeleteBacktrack.intro p₁ e r₃
        exact (hu (p₁.comp r₃) hdb).elim

/-- Concatenating two reduced paths whose junction is not a backtrack gives a reduced path. -/
theorem qpath_isReduced_comp [Quiver.HasReverse V] {a b c : V}
    {u : Quiver.Path a b} {v : Quiver.Path b c}
    (hu : u.IsReduced) (hv : v.IsReduced)
    (h : ∀ (x : V) (f : x ⟶ b) (u' : Quiver.Path a x) (v' : Quiver.Path x c),
      u = u'.cons f → v = (Quiver.reverse f).toPath.comp v' → False) :
    (u.comp v).IsReduced := by
  intro w hw
  obtain ⟨x, f, u', v', hu', hv', -⟩ := deleteBacktrack_comp_junction hu hv hw
  exact h x f u' v' hu' hv'


/-- Reversal preserves the length of a path. -/
theorem length_reverse [Quiver.HasReverse V] {a b : V} (p : Quiver.Path a b) :
    p.reverse.length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    show ((Quiver.reverse e).toPath.comp p.reverse).length = (p.cons e).length
    rw [Quiver.Path.length_comp, Quiver.Path.length_toPath, ih, Quiver.Path.length_cons]
    omega

/-- In a tree, any two reduced paths with the same endpoints are equal. -/
theorem qpath_eq_of_isTree {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (hT : Work.ORBassSerre.IsTree V) {a b : V} {p q : Quiver.Path a b}
    (hp : p.IsReduced) (hq : q.IsReduced) : p = q := by
  classical
  suffices hmain : ∀ n, ∀ {a b : V} (p q : Quiver.Path a b), p.length + q.length = n →
      p.IsReduced → q.IsReduced → p = q by
    exact hmain _ p q rfl hp hq
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b p q hlen hp hq
    cases p with
    | nil => exact (hT.2 a q hq).symm
    | cons p' e =>
      cases q with
      | nil => exact hT.2 a (p'.cons e) hp
      | cons q' f =>
        have hp' : p'.IsReduced := Quiver.Path.IsReduced.of_comp (q := e.toPath) hp
        have hq' : q'.IsReduced := Quiver.Path.IsReduced.of_comp (q := f.toPath) hq
        have hlt : p'.length + q'.length < n := by
          have h1 : (p'.cons e).length = p'.length + 1 := rfl
          have h2 : (q'.cons f).length = q'.length + 1 := rfl
          omega
        by_cases hj : ∃ (z : V) (g : z ⟶ b) (u' : Quiver.Path a z) (v' : Quiver.Path z a),
            (q'.cons f) = u'.cons g ∧ (p'.cons e).reverse = (Quiver.reverse g).toPath.comp v'
        · -- the junction case: the last arrows of `p` and `q` agree
          obtain ⟨z, g, u', v', hq_eq, hp_eq⟩ := hj
          have hyz := Quiver.Path.obj_eq_of_cons_eq_cons hq_eq
          have hheq_fg : HEq f g := Quiver.Path.hom_heq_of_cons_eq_cons hq_eq
          subst hyz
          have hf_eq_g : f = g := eq_of_heq hheq_fg
          have heq2 : (Quiver.reverse e).toPath.comp p'.reverse
              = (Quiver.reverse g).toPath.comp v' := by
            rw [← hp_eq]
            rfl
          obtain ⟨r, hr⟩ := Tree.Prefix.exists_comp_of_length_le heq2 (le_of_eq rfl)
          have hlenr : 1 = 1 + r.length := by
            simpa using congrArg Quiver.Path.length hr
          have hr0 : r.length = 0 := by omega
          have hxy := Quiver.Path.eq_of_length_zero r hr0
          subst hxy
          have hrnil : r = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero r hr0
          have hrev_eq : Quiver.reverse g = Quiver.reverse e := by
            have h1 : (Quiver.reverse g).toPath = (Quiver.reverse e).toPath := by
              rw [hrnil, Quiver.Path.comp_nil] at hr
              exact hr
            exact eq_of_heq (Quiver.Path.hom_heq_of_cons_eq_cons h1)
          have hge : g = e := by simpa using hrev_eq
          have hfe : f = e := hf_eq_g.trans hge
          have hp'q' : p' = q' := ih (p'.length + q'.length) hlt p' q' rfl hp' hq'
          rw [hp'q', hfe]
        · -- otherwise `q.comp p.reverse` is a non-trivial reduced closed path
          exfalso
          have hw : ((q'.cons f).comp ((p'.cons e).reverse)).IsReduced :=
            qpath_isReduced_comp hq (Quiver.Path.IsReduced.reverse hp)
              (fun z g u' v' hu' hv' => hj ⟨z, g, u', v', hu', hv'⟩)
          have hnil : ((q'.cons f).comp ((p'.cons e).reverse)) = Quiver.Path.nil :=
            hT.2 a _ hw
          have h0 : ((q'.cons f).comp ((p'.cons e).reverse)).length = 0 := by
            rw [hnil]
            rfl
          rw [Quiver.Path.length_comp, length_reverse, Quiver.Path.length_cons] at h0
          omega

end Work.ORBassSerre.Tree.Geodesic
