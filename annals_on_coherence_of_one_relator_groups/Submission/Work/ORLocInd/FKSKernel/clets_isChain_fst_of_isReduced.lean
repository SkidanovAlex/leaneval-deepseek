import Mathlib
import Submission.Work.ORLocInd.FKSKernel.PushoutStarTree
import Submission.Work.ORLocInd.FKSKernel.PushoutStarTreeTree

namespace Work.ORLocInd.FKSKernel

universe u

variable {ι : Type u} {H : Type u} {G : ι → Type u} [Group H] [∀ i, Group (G i)]

/-- The index of the last recorded letter of a path started at a centre, if any.  This is the
"state" of the `clets` recursion, projected to the first component. -/
noncomputable def cletsTail (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ) :
    {y : Vtx φ} → Quiver.Path (ctr φ γ) y → Option ι
  | _, .nil => none
  | _, .cons p e => if p.length % 2 = 1 then some e.idx else cletsTail φ γ p

@[simp]
theorem cletsTail_nil (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ) :
    cletsTail φ γ (Quiver.Path.nil : Quiver.Path (ctr φ γ) (ctr φ γ)) = none := rfl

theorem cletsTail_cons (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ) {x y : Vtx φ}
    (p : Quiver.Path (ctr φ γ) x) (e : x ⟶ y) :
    cletsTail φ γ (p.cons e) = if p.length % 2 = 1 then some e.idx else cletsTail φ γ p := rfl

theorem cletsTail_eq_getLast?_map (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ) :
    ∀ (y : Vtx φ) (p : Quiver.Path (ctr φ γ) y),
      cletsTail φ γ p = ((clets φ γ p).map Prod.fst).getLast?
  | _, Quiver.Path.nil => by simp [cletsTail, clets]
  | _, @Quiver.Path.cons _ _ _ x y p e => by
      simp only [cletsTail, clets_cons]
      by_cases h : p.length % 2 = 1
      · rw [if_pos h, if_pos h]
        simp only [List.map_append, List.map_cons, List.map_nil]
        rw [List.getLast?_append_cons]
        simp
      · rw [if_neg h, if_neg h]
        simp only [List.map_append, List.map_nil, List.append_nil]
        exact cletsTail_eq_getLast?_map φ γ x p

/-- Appending a final element to a `≠`-chain keeps it a `≠`-chain, as long as the appended element
differs from the last one. -/
theorem isChain_append_singleton_ne {α : Type*} {l : List α} {a : α}
    (h : l.IsChain (· ≠ ·)) (ha : l.getLast? ≠ some a) : (l ++ [a]).IsChain (· ≠ ·) := by
  refine List.IsChain.append h (List.IsChain.singleton a) ?_
  intro x hx y hy
  rw [Option.mem_def] at hx
  simp only [List.head?_cons, Option.mem_def, Option.some_inj] at hy
  subst hy
  intro hxa
  exact ha (hx.trans (congrArg some hxa))

/-- Two consecutive arrows of a reduced path, the first entering a centre and the second leaving
it, have different indices. -/
theorem junction_ne {φ : ∀ i, H →* G i} {γ : Psh φ ⧸ baseSub φ} {c : Psh φ ⧸ baseSub φ}
    {w' y : Vtx φ} (v : w' ⟶ ctr φ c) (u : ctr φ c ⟶ y)
    (q : Quiver.Path (ctr φ γ) w') (h : ((q.cons v).cons u).IsReduced) :
    v.idx ≠ u.idx := by
  intro hidx
  have hv := arrow_ctr_right v
  have hu := arrow_ctr_left u
  have hw'y : w' = y := by rw [hv.2, hu.2, hidx]
  subst hw'y
  have hvu : u = Quiver.reverse v := by
    apply Subtype.ext
    show (u.idx, u.lbl) = (v.idx, v.lbl)
    exact Prod.ext hidx.symm (hu.1.trans hv.1.symm)
  exact h q (by rw [hvu]; exact Quiver.Path.DeleteBacktrack.intro q v Quiver.Path.nil)

/-- An arrow out of a centre followed by an arrow out of its (leaf) target have the same index. -/
theorem leaf_adj_of_ctr {φ : ∀ i, H →* G i} {x z y : Vtx φ} (e : x ⟶ z) (f : z ⟶ y)
    (hx : ∃ c, x = ctr φ c) : e.idx = f.idx := by
  obtain ⟨c, hc⟩ := hx
  have hez : z = lf φ e.idx e.lbl := by
    rcases Arrow.endpoints e with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · exact absurd (h1.symm.trans hc) (ctr_ne_lf φ c e.lbl e.idx).symm
  have hfin : lf φ e.idx e.lbl = lf φ f.idx f.lbl := by
    rcases Arrow.endpoints f with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (hez.symm.trans h1) (lf_ne_ctr φ e.lbl f.lbl e.idx)
    · exact hez.symm.trans h1
  exact (leaf_eq_components hfin).1

/-- Auxiliary invariant for the chain property of `clets`: the list of indices is a chain on
reduced paths, and the last recorded index differs from the index of any edge that could be
appended while keeping the path reduced. -/
theorem clets_chain_aux (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ) :
    ∀ (y : Vtx φ) (p : Quiver.Path (ctr φ γ) y),
      (p.IsReduced → ((clets φ γ p).map Prod.fst).IsChain (· ≠ ·)) ∧
      (∀ (z : Vtx φ) (f : y ⟶ z), (p.cons f).IsReduced → cletsTail φ γ p ≠ some f.idx)
  | _, Quiver.Path.nil => by
      refine ⟨fun _ => ?_, fun z f _ => ?_⟩
      · simp [clets]
      · simp [cletsTail]
  | _, @Quiver.Path.cons _ _ _ x y p e => by
      have ih := clets_chain_aux φ γ x p
      refine ⟨fun hp => ?_, fun z f hp2 => ?_⟩
      · have hq : p.IsReduced := Quiver.Path.IsReduced.of_comp (q := e.toPath) hp
        have hchain : ((clets φ γ p).map Prod.fst).IsChain (· ≠ ·) := ih.1 hq
        rw [clets_cons]
        by_cases hpar : p.length % 2 = 1
        · rw [if_pos hpar, List.map_append, List.map_cons, List.map_nil]
          have hne : cletsTail φ γ p ≠ some e.idx := ih.2 y e hp
          have hlast : ((clets φ γ p).map Prod.fst).getLast? ≠ some e.idx := by
            rw [← cletsTail_eq_getLast?_map]; exact hne
          exact isChain_append_singleton_ne hchain hlast
        · rw [if_neg hpar, List.map_append, List.map_nil, List.append_nil]
          exact hchain
      · have hpe : (p.cons e).IsReduced := Quiver.Path.IsReduced.of_comp (q := f.toPath) hp2
        rw [cletsTail_cons]
        by_cases hpar : p.length % 2 = 1
        · rw [if_pos hpar]
          obtain ⟨c, hc⟩ := (length_even_iff_ctr φ γ y (p.cons e)).mpr
            (by rw [Quiver.Path.length_cons]; omega)
          subst hc
          intro hsome
          exact junction_ne e f p hp2 (Option.some.inj hsome)
        · rw [if_neg hpar]
          have hne : cletsTail φ γ p ≠ some e.idx := ih.2 y e hpe
          have hidx : e.idx = f.idx := by
            obtain ⟨c, hc⟩ := (length_even_iff_ctr φ γ x p).mpr (by omega)
            exact leaf_adj_of_ctr e f ⟨c, hc⟩
          intro hsome
          exact hne (hsome.trans (congrArg some hidx.symm))

theorem clets_isChain_fst_of_isReduced {ι : Type u} {H : Type u} {G : ι → Type u} [Group H]
    [∀ i, Group (G i)] (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ) {y : Vtx φ}
    (p : Quiver.Path (ctr φ γ) y) (hp : p.IsReduced) :
    ((clets φ γ p).map Prod.fst).IsChain (· ≠ ·) :=
  (clets_chain_aux φ γ y p).1 hp

end Work.ORLocInd.FKSKernel
