import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.commutator_defs
import Submission.Work.Diff.STE.fourierCoeff_pd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-
# The iterated Leibniz rule, in "difference" form

This file proves `Work.Diff.STE.pdList_mul_sub`: for a list `l` of directions and two functions
`F g : (ι → ℝ) → ℂ` whose iterated partial derivatives up to the order `|l|` are all
differentiable, the iterated derivative of the product minus the term where every derivative
falls on `g` is the sum of the Leibniz terms in which at least one derivative falls on `F`:

`∂^l (F·g) - F · ∂^l g = ∑_{p ∈ splits l, p.1 ≠ []} ∂^{p.1}F · ∂^{p.2}g`.

The main work is the full iterated Leibniz rule

`∂^l (F·g) = ∑_{p ∈ splits l} ∂^{p.1}F · ∂^{p.2}g`,

which is proved here by induction on `l` (there is no library version for `pdList`).  The
combinatorics of `splits` is handled by the auxiliary recursion `splitsNE` of the `splits`
with non-empty first component; `splitsNE_eq_filter` identifies it with the filtered list of
the statement, and `splitsNE_sum_add` records that `splitsNE l` is `splits l` with the single
term `([], l)` removed.

The hypotheses `hF`, `hg` are exactly what is needed: at the induction step one needs the
differentiability of `∂^{p.1}F` and `∂^{p.2}g` for all `p ∈ splits l`, and both `p.1` and
`p.2` are sublists of `l` of length `< |i :: l|`.
-/

noncomputable section

namespace Work.Diff.STE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Evaluating a list of functions pointwise -/

/-- Pointwise evaluation of a list of `ℂ`-valued functions: `∑_{f ∈ u} f y`. -/
def listEval (u : List ((ι → ℝ) → ℂ)) : (ι → ℝ) → ℂ := fun y => (u.map (fun f => f y)).sum

lemma listEval_nil : listEval ([] : List ((ι → ℝ) → ℂ)) = fun _ => 0 := by
  funext y; simp [listEval]

lemma listEval_cons (a : (ι → ℝ) → ℂ) (u : List ((ι → ℝ) → ℂ)) :
    listEval (a :: u) = a + listEval u := by
  funext y; simp [listEval, List.map_cons, List.sum_cons]

lemma listEval_append (u v : List ((ι → ℝ) → ℂ)) :
    listEval (u ++ v) = listEval u + listEval v := by
  funext y; simp [listEval, List.map_append, List.sum_append]

lemma listEval_map_congr {α : Type*} (L : List α) {f g : α → (ι → ℝ) → ℂ}
    (h : ∀ a ∈ L, f a = g a) : listEval (L.map f) = listEval (L.map g) := by
  rw [List.map_congr_left h]

lemma listEval_map_add {α : Type*} (L : List α) (f g : α → (ι → ℝ) → ℂ) :
    listEval (L.map (fun a => f a + g a)) = listEval (L.map f) + listEval (L.map g) := by
  funext y
  simp only [listEval]
  rw [List.map_map,
      show List.map ((fun f => f y) ∘ fun a => f a + g a) L = List.map (fun a => f a y + g a y) L from by
        apply List.map_congr_left; intro a _; rfl,
      List.sum_map_add,
      show List.map (fun a => f a y) L = List.map ((fun f => f y) ∘ f) L from by
        apply List.map_congr_left; intro a _; rfl,
      show List.map (fun a => g a y) L = List.map ((fun f => f y) ∘ g) L from by
        apply List.map_congr_left; intro a _; rfl,
      ← List.map_map, ← List.map_map]
  simp only [listEval, Pi.add_apply]

lemma listEval_map_apply {α : Type*} (L : List α) (f : α → (ι → ℝ) → ℂ) (y : ι → ℝ) :
    listEval (L.map f) y = (L.map (fun a => f a y)).sum := by
  simp only [listEval, List.map_map]
  congr 1

lemma listEval_map_eq {α : Type*} (L : List α) (f : α → (ι → ℝ) → ℂ) :
    listEval (L.map f) = fun y => (L.map (fun a => f a y)).sum := by
  funext y; exact listEval_map_apply L f y

lemma listEval_differentiable (u : List ((ι → ℝ) → ℂ)) (h : ∀ f ∈ u, Differentiable ℝ f) :
    Differentiable ℝ (listEval u) := by
  induction u with
  | nil => rw [listEval_nil]; exact differentiable_const 0
  | cons a u ih =>
      rw [listEval_cons]
      exact (h a (List.mem_cons_self ..)).add (ih (fun f hf => h f (List.mem_cons_of_mem a hf)))

/-! ## Differentiating a list of functions -/

lemma pd_listEval (i : ι) (u : List ((ι → ℝ) → ℂ)) (h : ∀ f ∈ u, Differentiable ℝ f) :
    pd i (listEval u) = listEval (u.map (pd i)) := by
  induction u with
  | nil => rw [listEval_nil]; funext y; simp [listEval, pd]
  | cons a u ih =>
      have hsub : ∀ f ∈ u, Differentiable ℝ f := fun f hf => h f (List.mem_cons_of_mem a hf)
      have hd : Differentiable ℝ (listEval u) := listEval_differentiable u hsub
      rw [listEval_cons]
      have hadd : pd i (a + listEval u) = pd i a + pd i (listEval u) := by
        funext x
        have hf : fderiv ℝ (a + listEval u) x = fderiv ℝ a x + fderiv ℝ (listEval u) x :=
          fderiv_add (h a (List.mem_cons_self ..) x) (hd x)
        have h2 : (fderiv ℝ (a + listEval u) x) (Pi.single i 1)
              = (fderiv ℝ a x) (Pi.single i 1) + (fderiv ℝ (listEval u) x) (Pi.single i 1) := by
          rw [hf]; simp
        simpa [pd] using h2
      rw [hadd, ih hsub, List.map_cons, listEval_cons]

/-- Additivity of `pd` on the nose (function-level). -/
lemma pd_add_fn (i : ι) (f g : (ι → ℝ) → ℂ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    pd i (f + g) = pd i f + pd i g := by
  funext x
  have h := fderiv_add (hf x) (hg x)
  have h2 : (fderiv ℝ (f + g) x) (Pi.single i 1)
      = (fderiv ℝ f x) (Pi.single i 1) + (fderiv ℝ g x) (Pi.single i 1) := by
    rw [h]; simp
  simpa [pd] using h2

/-- Leibniz rule for `pd`, function-level. -/
lemma pd_mul_fn (i : ι) (f g : (ι → ℝ) → ℂ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    pd i (f * g) = f * pd i g + g * pd i f := by
  funext x
  have h := fderiv_mul (hf x) (hg x)
  have h2 : (fderiv ℝ (f * g) x) (Pi.single i 1)
      = f x * ((fderiv ℝ g x) (Pi.single i 1)) + g x * ((fderiv ℝ f x) (Pi.single i 1)) := by
    rw [h]; simp [smul_eq_mul]
  simpa [pd] using h2

/-! ## The combinatorics of `splits` -/

/-- `splits l` with the entries having empty first component removed, defined recursively
(in a shape convenient for induction). -/
def splitsNE {α : Type*} : List α → List (List α × List α)
  | [] => []
  | i :: l => (splits l).map (fun p => (i :: p.1, p.2)) ++ (splitsNE l).map (fun p => (p.1, i :: p.2))

lemma splitsNE_eq_filter (l : List ι) :
    splitsNE l = (splits l).filter (fun p => p.1 ≠ []) := by
  induction l with
  | nil => simp [splitsNE, splits]
  | cons i l ih =>
      have h1 : List.filter (fun p : List ι × List ι => decide (p.1 ≠ []))
                  ((splits l).map (fun p => (i :: p.1, p.2))) = (splits l).map (fun p => (i :: p.1, p.2)) := by
        rw [List.filter_eq_self]
        intro a ha
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
        simp
      have h2 : List.filter (fun p : List ι × List ι => decide (p.1 ≠ []))
                  ((splits l).map (fun p => (p.1, i :: p.2)))
                = (splitsNE l).map (fun p => (p.1, i :: p.2)) := by
        rw [List.filter_map]
        congr 1
        have hc : List.filter ((fun p : List ι × List ι => decide (p.1 ≠ [])) ∘ (fun p => (p.1, i :: p.2))) (splits l)
                = List.filter (fun p : List ι × List ι => decide (p.1 ≠ [])) (splits l) :=
          List.filter_congr (fun x _ => rfl)
        rw [hc, ← ih]
      rw [splitsNE, splits, List.filter_append, h1, h2]

/-- `splitsNE l` is `splits l` with the single term `([], l)` deleted: adding that term back
gives the full sum. -/
lemma splitsNE_sum_add (l : List ι) : ∀ (φ : List ι × List ι → ℂ),
    (((splitsNE l).map φ).sum) + φ ([], l) = ((splits l).map φ).sum := by
  induction l with
  | nil => intro φ; simp [splitsNE, splits]
  | cons i l ih =>
      intro φ
      simp only [splitsNE, splits, List.map_append, List.sum_append, List.map_map]
      have hih := ih (φ ∘ (fun p : List ι × List ι => (p.1, i :: p.2)))
      have hψ : (φ ∘ (fun p : List ι × List ι => (p.1, i :: p.2))) ([], l) = φ ([], i :: l) := rfl
      rw [add_assoc, ← hψ, hih]

/-- Both components of a split of `l` are sublists of `l`. -/
lemma splits_mem_sublist : ∀ (l : List ι) (p : List ι × List ι), p ∈ splits l → p.1.Sublist l ∧ p.2.Sublist l := by
  intro l
  induction l with
  | nil =>
      intro p hp
      simp only [splits, List.mem_singleton] at hp
      rw [hp]
      exact ⟨List.Sublist.refl [], List.Sublist.refl []⟩
  | cons i l ih =>
      intro p hp
      simp only [splits, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · obtain ⟨h1, h2⟩ := ih q hq
        exact ⟨List.cons_sublist_cons.mpr h1, List.Sublist.cons i h2⟩
      · obtain ⟨h1, h2⟩ := ih q hq
        exact ⟨List.Sublist.cons i h1, List.cons_sublist_cons.mpr h2⟩

/-! ## The iterated Leibniz rule -/

/-- The Leibniz term `∂^{p.1}F · ∂^{p.2}g`. -/
def PhiL (F g : (ι → ℝ) → ℂ) (p : List ι × List ι) : (ι → ℝ) → ℂ :=
  pdList p.1 F * pdList p.2 g

/-- The term obtained by putting the new derivative on `g`. -/
def Aterm (i : ι) (F g : (ι → ℝ) → ℂ) (p : List ι × List ι) : (ι → ℝ) → ℂ :=
  pdList p.1 F * pdList (i :: p.2) g

/-- The term obtained by putting the new derivative on `F`. -/
def Bterm (i : ι) (F g : (ι → ℝ) → ℂ) (p : List ι × List ι) : (ι → ℝ) → ℂ :=
  pdList p.2 g * pdList (i :: p.1) F

/-- **Iterated Leibniz rule, difference form** (induction on the list of directions). -/
lemma pdList_mul_sub_aux : ∀ (l : List ι) (F g : (ι → ℝ) → ℂ),
    (∀ q, q.Sublist l → q.length < l.length → Differentiable ℝ (pdList q F)) →
    (∀ q, q.Sublist l → q.length < l.length → Differentiable ℝ (pdList q g)) →
    (fun y => pdList l (fun z => F z * g z) y - F y * pdList l g y)
      = listEval ((splitsNE l).map (PhiL F g)) := by
  intro l
  induction l with
  | nil =>
      intro F g hF hg
      have h0 : listEval ((splitsNE ([] : List ι)).map (PhiL F g)) = fun _ => 0 := by
        rw [splitsNE, List.map_nil, listEval_nil]
      rw [h0]
      funext y
      simp [pdList]
  | cons i l ih =>
      intro F g hF hg
      have hF' : ∀ q, q.Sublist l → q.length < l.length → Differentiable ℝ (pdList q F) :=
        fun q hq hlen => hF q (List.Sublist.cons i hq) (by simp only [List.length_cons]; omega)
      have hg' : ∀ q, q.Sublist l → q.length < l.length → Differentiable ℝ (pdList q g) :=
        fun q hq hlen => hg q (List.Sublist.cons i hq) (by simp only [List.length_cons]; omega)
      have ih' := ih F g hF' hg'
      have hF0 : Differentiable ℝ F := hF [] (List.nil_sublist (i :: l)) (by simp)
      have hgl : Differentiable ℝ (pdList l g) :=
        hg l (List.Sublist.cons i (List.Sublist.refl l)) (by simp only [List.length_cons]; omega)
      have hterm_diff : ∀ p ∈ splits l, Differentiable ℝ (pdList p.1 F) ∧ Differentiable ℝ (pdList p.2 g) := by
        intro p hp
        obtain ⟨hs1, hs2⟩ := splits_mem_sublist l p hp
        refine ⟨hF p.1 (List.Sublist.cons i hs1) ?_, hg p.2 (List.Sublist.cons i hs2) ?_⟩
        · have := List.Sublist.length_le hs1; simp only [List.length_cons]; omega
        · have := List.Sublist.length_le hs2; simp only [List.length_cons]; omega
      have hdiffu : ∀ f ∈ (splitsNE l).map (PhiL F g), Differentiable ℝ f := by
        intro f hf
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
        have hp' : p ∈ splits l := by
          rw [splitsNE_eq_filter] at hp
          exact (List.mem_filter.mp hp).1
        obtain ⟨h1, h2⟩ := hterm_diff p hp'
        simpa only [PhiL] using h1.mul h2
      set S : (ι → ℝ) → ℂ := listEval ((splitsNE l).map (PhiL F g)) with hS
      have hSdiff : Differentiable ℝ S := by
        rw [hS]; exact listEval_differentiable _ hdiffu
      -- the induction hypothesis, with `pdList l (F * g)` replaced by `S + F * pdList l g`
      have hsplit : pdList l (fun z => F z * g z) = S + F * pdList l g := by
        funext y
        change pdList l (fun z => F z * g z) y = S y + F y * pdList l g y
        have hy := congrFun ih' y
        change pdList l (fun z => F z * g z) y - F y * pdList l g y = S y at hy
        rw [← hy]; ring
      -- the left-hand side of the goal is `pd i S + pdList l g * pd i F`
      have hLHS : (fun y => pdList (i :: l) (fun z => F z * g z) y - F y * pdList (i :: l) g y)
          = pd i S + pdList l g * pd i F := by
        have e : (fun y => pdList (i :: l) (fun z => F z * g z) y - F y * pdList (i :: l) g y)
            = pd i (pdList l (fun z => F z * g z)) - F * pd i (pdList l g) := by
          funext y; rfl
        rw [e, hsplit, pd_add_fn i S (F * pdList l g) hSdiff (hF0.mul hgl),
          pd_mul_fn i F (pdList l g) hF0 hgl]
        abel
      -- `pd i S` splits into the two families of Leibniz terms
      have hterm : ∀ p ∈ splitsNE l, pd i (PhiL F g p) = Aterm i F g p + Bterm i F g p := by
        intro p hp
        have hp' : p ∈ splits l := by
          rw [splitsNE_eq_filter] at hp
          exact (List.mem_filter.mp hp).1
        obtain ⟨h1, h2⟩ := hterm_diff p hp'
        simp only [PhiL, Aterm, Bterm]
        exact pd_mul_fn i (pdList p.1 F) (pdList p.2 g) h1 h2
      have hpdS : pd i S = listEval ((splitsNE l).map (Aterm i F g)) + listEval ((splitsNE l).map (Bterm i F g)) := by
        rw [hS, pd_listEval i _ hdiffu, List.map_map]
        have hkey : listEval ((splitsNE l).map ((pd i) ∘ (PhiL F g)))
            = listEval ((splitsNE l).map (fun p => Aterm i F g p + Bterm i F g p)) :=
          listEval_map_congr (splitsNE l) (f := (pd i) ∘ (PhiL F g))
            (g := fun p => Aterm i F g p + Bterm i F g p) (fun p hp => hterm p hp)
        rw [hkey, listEval_map_add (splitsNE l) (Aterm i F g) (Bterm i F g)]
      -- adding the missing `([], l)` term back to the `B`-sum
      have hBid : listEval ((splitsNE l).map (Bterm i F g)) + pdList l g * pd i F
            = listEval ((splits l).map (Bterm i F g)) := by
        funext y
        change listEval ((splitsNE l).map (Bterm i F g)) y + pdList l g y * pd i F y
          = listEval ((splits l).map (Bterm i F g)) y
        rw [listEval_map_apply, listEval_map_apply]
        have h := splitsNE_sum_add l (fun p : List ι × List ι => Bterm i F g p y)
        have hnil : Bterm i F g ([], l) y = pdList l g y * pd i F y := by
          simp [Bterm, pdList]
        rw [hnil] at h
        exact h
      -- the right-hand side of the goal
      have hRHS : listEval ((splitsNE (i :: l)).map (PhiL F g))
            = listEval ((splits l).map (Bterm i F g)) + listEval ((splitsNE l).map (Aterm i F g)) := by
        have hB1 : ∀ p ∈ splits l, (PhiL F g) (i :: p.1, p.2) = Bterm i F g p := by
          intro p hp
          funext y
          change pdList (i :: p.1) F y * pdList p.2 g y = pdList p.2 g y * pdList (i :: p.1) F y
          ring
        have hB2 : ∀ p ∈ splitsNE l, (PhiL F g) (p.1, i :: p.2) = Aterm i F g p := by
          intro p hp; rfl
        have hA1 : listEval ((splits l).map ((PhiL F g) ∘ (fun p : List ι × List ι => (i :: p.1, p.2))))
            = listEval ((splits l).map (Bterm i F g)) :=
          listEval_map_congr (splits l) (f := (PhiL F g) ∘ (fun p : List ι × List ι => (i :: p.1, p.2)))
            (g := Bterm i F g) (fun p hp => hB1 p hp)
        have hA2 : listEval ((splitsNE l).map ((PhiL F g) ∘ (fun p : List ι × List ι => (p.1, i :: p.2))))
            = listEval ((splitsNE l).map (Aterm i F g)) :=
          listEval_map_congr (splitsNE l) (f := (PhiL F g) ∘ (fun p : List ι × List ι => (p.1, i :: p.2)))
            (g := Aterm i F g) (fun p hp => hB2 p hp)
        rw [splitsNE, List.map_append, listEval_append, List.map_map, List.map_map, hA1, hA2]
      rw [hLHS, hpdS, add_assoc, hBid, hRHS]
      exact add_comm _ _

theorem pdList_mul_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (l : List ι) (F g : (ι → ℝ) → ℂ)
    (hF : ∀ q : List ι, List.Sublist q l → q.length < l.length → Differentiable ℝ (pdList q F))
    (hg : ∀ q : List ι, List.Sublist q l → q.length < l.length → Differentiable ℝ (pdList q g)) :
    (fun y => pdList l (fun z => F z * g z) y - F y * pdList l g y)
      = fun y => (((splits l).filter (fun p => p.1 ≠ [])).map
          (fun p => pdList p.1 F y * pdList p.2 g y)).sum := by
  rw [pdList_mul_sub_aux l F g hF hg, ← splitsNE_eq_filter l, listEval_map_eq]
  funext y
  congr 1

end Work.Diff.STE
