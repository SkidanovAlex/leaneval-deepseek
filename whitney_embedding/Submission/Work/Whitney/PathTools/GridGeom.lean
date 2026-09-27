import Submission.Work.Whitney.PathTools.GridSplit

/-!
# The grid in the plane: from chains to paths

We interpret the combinatorial grid of `Grid.lean` as a square grid of mesh `h` in the plane.

The two main results are

* `gWalk_of_chain` : a chain from `p` to `q` (i.e. `bdry1 l = p + q`) yields a walk in the grid
  graph from `p` to `q` supported on the support of `l`;
* `GWalk.toJoinedIn` : such a walk, all of whose edges avoid `K`, yields a `JoinedIn` relation
  inside the complement of `K`.
-/

namespace Work.Whitney.PathTools.Grid

noncomputable section
open scoped BigOperators

/-- The plane, as `EuclideanSpace ℝ (Fin 2)`. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The grid vertex `p` as a point. -/
def gpt (p : ℤ × ℤ) : Pt :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![(p.1 : ℝ), (p.2 : ℝ)]

/-- The mesh-`h` image of a grid vertex. -/
def gptH (h : ℝ) (p : ℤ × ℤ) : Pt := h • gpt p

@[simp] lemma gpt_apply_zero (p : ℤ × ℤ) : gpt p 0 = (p.1 : ℝ) := by simp [gpt]

@[simp] lemma gpt_apply_one (p : ℤ × ℤ) : gpt p 1 = (p.2 : ℝ) := by simp [gpt]

@[simp] lemma gptH_apply_zero (h : ℝ) (p : ℤ × ℤ) : gptH h p 0 = h * (p.1 : ℝ) := by
  simp [gptH]

@[simp] lemma gptH_apply_one (h : ℝ) (p : ℤ × ℤ) : gptH h p 1 = h * (p.2 : ℝ) := by
  simp [gptH]

/-- The lower-left endpoint of a grid edge. -/
def eTail : Edge → ℤ × ℤ
  | (false, i, j) => (i, j)
  | (true, i, j) => (i, j)

/-- The upper/right endpoint of a grid edge. -/
def eHead : Edge → ℤ × ℤ
  | (false, i, j) => (i, j + 1)
  | (true, i, j) => (i + 1, j)

@[simp] lemma eTail_false (i j : ℤ) : eTail (false, i, j) = (i, j) := rfl
@[simp] lemma eTail_true (i j : ℤ) : eTail (true, i, j) = (i, j) := rfl
@[simp] lemma eHead_false (i j : ℤ) : eHead (false, i, j) = (i, j + 1) := rfl
@[simp] lemma eHead_true (i j : ℤ) : eHead (true, i, j) = (i + 1, j) := rfl

lemma eTail_ne_eHead (e : Edge) : eTail e ≠ eHead e := by
  obtain ⟨b, i, j⟩ := e
  cases b <;> simp [eTail, eHead] <;> omega

/-- The closed segment of a grid edge, scaled by the mesh `h`. -/
def gseg (h : ℝ) (e : Edge) : Set Pt := segment ℝ (gptH h (eTail e)) (gptH h (eHead e))

lemma gseg_self (h : ℝ) (e : Edge) : gptH h (eTail e) ∈ gseg h e :=
  left_mem_segment ℝ _ _

lemma gseg_self' (h : ℝ) (e : Edge) : gptH h (eHead e) ∈ gseg h e :=
  right_mem_segment ℝ _ _

/-- The closed cell of the mesh-`h` grid. -/
def gsq (h : ℝ) (c : Cell) : Set Pt :=
  {x | h * (c.1 : ℝ) ≤ x 0 ∧ x 0 ≤ h * ((c.1 : ℝ) + 1) ∧
       h * (c.2 : ℝ) ≤ x 1 ∧ x 1 ≤ h * ((c.2 : ℝ) + 1)}

/-- The set of cells meeting `K`. -/
def cellSet (h : ℝ) (K : Set Pt) : Set Cell := {c | (gsq h c ∩ K).Nonempty}

/-- The convex-combination path between two points. -/
def segPath (a b : Pt) : Path a b where
  toFun t := (1 - (t : ℝ)) • a + (t : ℝ) • b
  continuous_toFun :=
    ((continuous_const.sub continuous_subtype_val).smul continuous_const).add
      (continuous_subtype_val.smul continuous_const)
  source' := by simp
  target' := by simp

lemma segPath_mem (a b : Pt) (t : unitInterval) : segPath a b t ∈ segment ℝ a b := by
  rw [segment_eq_image]
  exact ⟨(t : ℝ), ⟨t.2.1, t.2.2⟩, rfl⟩

/-- The edge `e` of `s` gives a `JoinedIn` relation for its endpoints when all segments of `s`
avoid `K`. -/
lemma joinedIn_of_mem {h : ℝ} {K : Set Pt} {s : Finset Edge} {e : Edge} (he : e ∈ s)
    (hav : ∀ e ∈ s, Disjoint (gseg h e) K) :
    JoinedIn (Kᶜ) (gptH h (eTail e)) (gptH h (eHead e)) := by
  refine ⟨segPath _ _, fun t => ?_⟩
  exact fun hK => Set.disjoint_left.mp (hav e he) (segPath_mem _ _ t) hK

/-- A walk in the graph whose edges are a finset of grid edges. -/
inductive GWalk (s : Finset Edge) : (ℤ × ℤ) → (ℤ × ℤ) → Prop
  | refl (v) : GWalk s v v
  | step {u v w : ℤ × ℤ}
      (h1 : ∃ e ∈ s, (eTail e = u ∧ eHead e = v) ∨ (eTail e = v ∧ eHead e = u))
      (h2 : GWalk s v w) : GWalk s u w

lemma GWalk.mono {s t : Finset Edge} (hst : s ⊆ t) {u v : ℤ × ℤ} (h : GWalk s u v) :
    GWalk t u v := by
  induction h with
  | refl v => exact GWalk.refl v
  | step h1 _ ih =>
      obtain ⟨e, he, hor⟩ := h1
      exact GWalk.step ⟨e, hst he, hor⟩ ih

/-- A walk all of whose edges avoid `K` gives a `JoinedIn` relation in the complement of `K`. -/
lemma GWalk.toJoinedIn {h : ℝ} {K : Set Pt} {s : Finset Edge}
    (hav : ∀ e ∈ s, Disjoint (gseg h e) K) :
    ∀ {u v : ℤ × ℤ}, GWalk s u v → gptH h u ∉ K → JoinedIn (Kᶜ) (gptH h u) (gptH h v) := by
  intro u v hw
  induction hw with
  | refl z => intro hu; exact ⟨Path.refl _, fun _ => hu⟩
  | step h1 h2 ih =>
      rename_i a b c
      intro hu
      obtain ⟨e, he, hor⟩ := h1
      have hav_e := hav e he
      have htailK : gptH h (eTail e) ∉ K :=
        fun hc => Set.disjoint_left.mp hav_e (gseg_self h e) hc
      have hheadK : gptH h (eHead e) ∉ K :=
        fun hc => Set.disjoint_left.mp hav_e (gseg_self' h e) hc
      rcases hor with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · have hb' : gptH h b ∉ K := by rw [← hb]; exact hheadK
        have hseg : JoinedIn (Kᶜ) (gptH h a) (gptH h b) := by
          have h0 := joinedIn_of_mem (h := h) (K := K) he hav
          rw [ha, hb] at h0
          exact h0
        exact hseg.trans (ih hb')
      · have hb' : gptH h b ∉ K := by rw [← ha]; exact htailK
        have hseg : JoinedIn (Kᶜ) (gptH h a) (gptH h b) := by
          have h0 := joinedIn_of_mem (h := h) (K := K) he hav
          rw [ha, hb] at h0
          exact h0.symm
        exact hseg.trans (ih hb')

/-- The single-edge chain. -/
def eChain (e : Edge) : Chain1 := Finsupp.single e 1

/-- The value of the single-edge chain at another edge. -/
lemma eChain_apply (f g : Edge) :
    ((eChain f : Chain1) : Edge → ZMod 2) g = (if g = f then 1 else 0) := by
  rw [eChain, Finsupp.single_apply]
  by_cases h : g = f
  · simp [h]
  · simp only [if_neg h, if_neg (fun hh : f = g => h hh.symm)]

/-- Addition of the indicator functions of `{a,b}` and `{a,c}` in `ZMod 2`. -/
lemma fun_pair_add (a b c : ℤ × ℤ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (fun v : ℤ × ℤ => ((if v = a then (1 : ZMod 2) else 0) + (if v = b then 1 else 0)))
      + (fun v : ℤ × ℤ => ((if v = a then 1 else 0) + (if v = c then 1 else 0)))
    = (fun v : ℤ × ℤ => ((if v = b then 1 else 0) + (if v = c then 1 else 0))) := by
  funext v
  simp only [Pi.add_apply]
  by_cases h1 : v = a
  · rw [if_pos h1, if_neg (fun h => hab (h1.symm.trans h)),
        if_neg (fun h => hac (h1.symm.trans h))]
    decide
  · rw [if_neg h1]
    by_cases h2 : v = b
    · rw [if_pos h2, if_neg (fun h => hbc (h2.symm.trans h))]
      decide
    · rw [if_neg h2]
      by_cases h3 : v = c
      · rw [if_pos h3]
        decide
      · rw [if_neg h3]
        decide

/-- First component of an edge equality. -/
lemma gFst {b b' : Bool} {x y x' y' : ℤ} (h : (((b,x,y) : Edge) = (b',x',y'))) : b = b' :=
  congrArg Prod.fst h
lemma gSnd1 {b b' : Bool} {x y x' y' : ℤ} (h : (((b,x,y) : Edge) = (b',x',y'))) : x = x' :=
  congrArg (fun t : Edge => t.2.1) h
lemma gSnd2 {b b' : Bool} {x y x' y' : ℤ} (h : (((b,x,y) : Edge) = (b',x',y'))) : y = y' :=
  congrArg (fun t : Edge => t.2.2) h
lemma pFst {x y x' y' : ℤ} (h : (((x,y) : ℤ×ℤ) = (x',y'))) : x = x' := congrArg Prod.fst h
lemma pSnd {x y x' y' : ℤ} (h : (((x,y) : ℤ×ℤ) = (x',y'))) : y = y' := congrArg Prod.snd h
lemma ne_of_conj {a i k j : ℤ} (h : ¬ (a = i ∧ k = j)) : ¬ (((a,k) : ℤ×ℤ) = (i,j)) :=
  fun hh => h ⟨pFst hh, pSnd hh⟩
lemma notBool {b b' : Bool} (hb : b ≠ b') {x y x' y' : ℤ} :
    ¬ (((b,x,y) : Edge) = (b',x',y')) := fun h => hb (gFst h)

/-- The boundary of a single-edge chain is the sum of the two endpoints. -/
lemma bdry1_eChain (e : Edge) (v : ℤ × ℤ) :
    bdry1 ((eChain e : Chain1) : Edge → ZMod 2) v
      = (if v = eTail e then 1 else 0) + (if v = eHead e then 1 else 0) := by
  obtain ⟨a, k⟩ := v
  obtain ⟨b, i, j⟩ := e
  cases b
  · rw [show eTail (false,i,j) = ((i,j) : ℤ×ℤ) from rfl,
        show eHead (false,i,j) = ((i,j+1) : ℤ×ℤ) from rfl]
    show ((eChain (false,i,j) : Chain1) : Edge → ZMod 2) (false,a,k)
        + ((eChain (false,i,j) : Chain1) : Edge → ZMod 2) (false,a,k-1)
        + ((eChain (false,i,j) : Chain1) : Edge → ZMod 2) (true,a,k)
        + ((eChain (false,i,j) : Chain1) : Edge → ZMod 2) (true,a-1,k) = _
    simp only [eChain_apply]
    by_cases h1 : a = i ∧ k = j
    · have c1 : (((false,a,k) : Edge) = (false,i,j)) := by rw [h1.1, h1.2]
      have c2 : ¬ (((false,a,k-1) : Edge) = (false,i,j)) := by
        intro h
        have hk : k - 1 = j := gSnd2 h
        have hk' : k = j := h1.2
        omega
      have c3 : ¬ (((true,a,k) : Edge) = (false,i,j)) := notBool (by decide)
      have c4 : ¬ (((true,a-1,k) : Edge) = (false,i,j)) := notBool (by decide)
      have r1 : (((a,k) : ℤ×ℤ) = (i,j)) := by rw [h1.1, h1.2]
      have r2 : ¬ (((a,k) : ℤ×ℤ) = (i,j+1)) := by
        intro h
        have hk : k = j + 1 := pSnd h
        have hk' : k = j := h1.2
        omega
      rw [if_pos c1, if_neg c2, if_neg c3, if_neg c4, if_pos r1, if_neg r2]
      decide
    · by_cases h2 : a = i ∧ k = j + 1
      · have c1 : ¬ (((false,a,k) : Edge) = (false,i,j)) :=
          fun h => h1 ⟨gSnd1 h, gSnd2 h⟩
        have c2 : (((false,a,k-1) : Edge) = (false,i,j)) := by
          rw [h2.1, show k - 1 = j by omega]
        have c3 : ¬ (((true,a,k) : Edge) = (false,i,j)) := notBool (by decide)
        have c4 : ¬ (((true,a-1,k) : Edge) = (false,i,j)) := notBool (by decide)
        have r1 : ¬ (((a,k) : ℤ×ℤ) = (i,j)) := ne_of_conj h1
        have r2 : (((a,k) : ℤ×ℤ) = (i,j+1)) := by rw [h2.1, h2.2]
        rw [if_neg c1, if_pos c2, if_neg c3, if_neg c4, if_neg r1, if_pos r2]
        decide
      · have c1 : ¬ (((false,a,k) : Edge) = (false,i,j)) :=
          fun h => h1 ⟨gSnd1 h, gSnd2 h⟩
        have c2 : ¬ (((false,a,k-1) : Edge) = (false,i,j)) := by
          intro h
          have hx : a = i := gSnd1 h
          have hy : k - 1 = j := gSnd2 h
          exact h2 ⟨hx, by omega⟩
        have c3 : ¬ (((true,a,k) : Edge) = (false,i,j)) := notBool (by decide)
        have c4 : ¬ (((true,a-1,k) : Edge) = (false,i,j)) := notBool (by decide)
        rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_neg (ne_of_conj h1), if_neg (ne_of_conj h2)]
        decide
  · rw [show eTail (true,i,j) = ((i,j) : ℤ×ℤ) from rfl,
        show eHead (true,i,j) = ((i+1,j) : ℤ×ℤ) from rfl]
    show ((eChain (true,i,j) : Chain1) : Edge → ZMod 2) (false,a,k)
        + ((eChain (true,i,j) : Chain1) : Edge → ZMod 2) (false,a,k-1)
        + ((eChain (true,i,j) : Chain1) : Edge → ZMod 2) (true,a,k)
        + ((eChain (true,i,j) : Chain1) : Edge → ZMod 2) (true,a-1,k) = _
    simp only [eChain_apply]
    by_cases h1 : a = i ∧ k = j
    · have c1 : ¬ (((false,a,k) : Edge) = (true,i,j)) := notBool (by decide)
      have c2 : ¬ (((false,a,k-1) : Edge) = (true,i,j)) := notBool (by decide)
      have c3 : (((true,a,k) : Edge) = (true,i,j)) := by rw [h1.1, h1.2]
      have c4 : ¬ (((true,a-1,k) : Edge) = (true,i,j)) := by
        intro h
        have ha : a - 1 = i := gSnd1 h
        have ha' : a = i := h1.1
        omega
      have r1 : (((a,k) : ℤ×ℤ) = (i,j)) := by rw [h1.1, h1.2]
      have r2 : ¬ (((a,k) : ℤ×ℤ) = (i+1,j)) := by
        intro h
        have ha : a = i + 1 := pFst h
        have ha' : a = i := h1.1
        omega
      rw [if_neg c1, if_neg c2, if_pos c3, if_neg c4, if_pos r1, if_neg r2]
      decide
    · by_cases h2 : a = i + 1 ∧ k = j
      · have c1 : ¬ (((false,a,k) : Edge) = (true,i,j)) := notBool (by decide)
        have c2 : ¬ (((false,a,k-1) : Edge) = (true,i,j)) := notBool (by decide)
        have c3 : ¬ (((true,a,k) : Edge) = (true,i,j)) := fun h => h1 ⟨gSnd1 h, gSnd2 h⟩
        have c4 : (((true,a-1,k) : Edge) = (true,i,j)) := by
          rw [h2.2, show a - 1 = i by omega]
        have r1 : ¬ (((a,k) : ℤ×ℤ) = (i,j)) := ne_of_conj h1
        have r2 : (((a,k) : ℤ×ℤ) = (i+1,j)) := by rw [h2.1, h2.2]
        rw [if_neg c1, if_neg c2, if_neg c3, if_pos c4, if_neg r1, if_pos r2]
        decide
      · have c1 : ¬ (((false,a,k) : Edge) = (true,i,j)) := notBool (by decide)
        have c2 : ¬ (((false,a,k-1) : Edge) = (true,i,j)) := notBool (by decide)
        have c3 : ¬ (((true,a,k) : Edge) = (true,i,j)) := fun h => h1 ⟨gSnd1 h, gSnd2 h⟩
        have c4 : ¬ (((true,a-1,k) : Edge) = (true,i,j)) := by
          intro h
          have hx : a - 1 = i := gSnd1 h
          have hy : k = j := gSnd2 h
          exact h2 ⟨by omega, hy⟩
        rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_neg (ne_of_conj h1), if_neg (ne_of_conj h2)]
        decide

/-- Symmetrised form of `fun_pair_add`. -/
lemma fun_pair_add' (a b c : ℤ × ℤ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (fun v : ℤ × ℤ => ((if v = a then (1 : ZMod 2) else 0) + (if v = b then 1 else 0)))
      + (fun v : ℤ × ℤ => ((if v = c then 1 else 0) + (if v = a then 1 else 0)))
    = (fun v : ℤ × ℤ => ((if v = b then 1 else 0) + (if v = c then 1 else 0))) := by
  rw [show (fun v : ℤ × ℤ => ((if v = c then (1 : ZMod 2) else 0) + (if v = a then 1 else 0)))
        = (fun v : ℤ × ℤ => ((if v = a then 1 else 0) + (if v = c then 1 else 0))) from by
      funext v; ring]
  exact fun_pair_add a b c hab hac hbc

/-- **Extraction of a walk from a chain.**  If the boundary of `l` is `p + q` with `p ≠ q`, then
the support of `l` contains a walk from `p` to `q`. -/
theorem gWalk_of_chain : ∀ (n : ℕ) (l : Chain1) {p q : ℤ × ℤ}, l.support.card = n → p ≠ q →
    (∀ v : ℤ × ℤ, bdry1 ((l : Chain1) : Edge → ZMod 2) v
      = (if v = p then 1 else 0) + (if v = q then 1 else 0)) →
    GWalk l.support p q := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l p q hcard hpq hb
    have hone : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by intro a; revert a; decide
    -- some edge of the support is incident with `p`, since the boundary of `l` at `p` is `1`
    have hinc : ∃ e ∈ l.support, eTail e = p ∨ eHead e = p := by
      by_contra hcon
      push_neg at hcon
      have h1 : (l : Edge → ZMod 2) (false,p.1,p.2) = 0 := by
        by_contra hc
        exact (hcon _ (Finsupp.mem_support_iff.mpr hc)).1 rfl
      have h2 : (l : Edge → ZMod 2) (false,p.1,p.2-1) = 0 := by
        by_contra hc
        exact (hcon _ (Finsupp.mem_support_iff.mpr hc)).2 (by simp [eHead])
      have h3 : (l : Edge → ZMod 2) (true,p.1,p.2) = 0 := by
        by_contra hc
        exact (hcon _ (Finsupp.mem_support_iff.mpr hc)).1 rfl
      have h4 : (l : Edge → ZMod 2) (true,p.1-1,p.2) = 0 := by
        by_contra hc
        exact (hcon _ (Finsupp.mem_support_iff.mpr hc)).2 (by simp [eHead])
      have hzero : bdry1 ((l : Chain1) : Edge → ZMod 2) p = 0 := by
        rw [show bdry1 ((l : Chain1) : Edge → ZMod 2) p
            = ((l : Edge → ZMod 2) (false,p.1,p.2) + (l : Edge → ZMod 2) (false,p.1,p.2-1)
              + (l : Edge → ZMod 2) (true,p.1,p.2) + (l : Edge → ZMod 2) (true,p.1-1,p.2)) from rfl,
          h1, h2, h3, h4]
        simp
      rw [hb p] at hzero
      simp [hpq] at hzero
    obtain ⟨e, he, htail⟩ := hinc
    set u : ℤ × ℤ := if eTail e = p then eHead e else eTail e with hu
    have hedge : (eTail e = p ∧ eHead e = u) ∨ (eTail e = u ∧ eHead e = p) := by
      by_cases h : eTail e = p
      · rw [hu, if_pos h]; exact Or.inl ⟨h, rfl⟩
      · rw [hu, if_neg h]
        rcases htail with h' | h'
        · exact absurd h' h
        · exact Or.inr ⟨rfl, h'⟩
    have hpu : p ≠ u := by
      intro h
      rcases hedge with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact eTail_ne_eHead e (by rw [h1, h2, h])
      · exact eTail_ne_eHead e (by rw [h1, h2, h.symm])
    rcases eq_or_ne u q with huq | huq
    · refine GWalk.step ⟨e, he, ?_⟩ (GWalk.refl q)
      rcases hedge with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, by rw [← huq]; exact h2⟩
      · exact Or.inr ⟨by rw [← huq]; exact h1, h2⟩
    · have hev : (l : Edge → ZMod 2) e = 1 := hone _ (Finsupp.mem_support_iff.mp he)
      -- remove the edge `e`
      set l' : Chain1 := l + eChain e with hl'
      have hl'e : (l' : Edge → ZMod 2) e = 0 := by
        rw [hl', Finsupp.coe_add, Pi.add_apply, hev, eChain, Finsupp.single_eq_same]
        exact CharTwo.add_self_eq_zero 1
      have hbd : ∀ v : ℤ × ℤ, bdry1 ((l' : Chain1) : Edge → ZMod 2) v
          = (if v = u then 1 else 0) + (if v = q then 1 else 0) := by
        intro v
        have h1 : bdry1 ((l' : Chain1) : Edge → ZMod 2) v
            = bdry1 ((l : Chain1) : Edge → ZMod 2) v
              + bdry1 ((eChain e : Chain1) : Edge → ZMod 2) v := by
          rw [hl', Finsupp.coe_add, bdry1_add]; rfl
        rw [h1, hb v, bdry1_eChain e v]
        rcases hedge with ⟨ha, hb'⟩ | ⟨ha, hb'⟩
        · rw [ha, hb']
          rw [show ((if v = u then (1 : ZMod 2) else 0) + (if v = q then 1 else 0))
                = ((if v = q then 1 else 0) + (if v = u then 1 else 0)) from by ring]
          exact congrFun (fun_pair_add p q u hpq hpu huq.symm) v
        · rw [ha, hb']
          rw [show ((if v = u then (1 : ZMod 2) else 0) + (if v = q then 1 else 0))
                = ((if v = q then 1 else 0) + (if v = u then 1 else 0)) from by ring]
          exact congrFun (fun_pair_add' p q u hpq hpu huq.symm) v
      have hsub : l'.support ⊆ l.support := by
        intro f hf
        rw [Finsupp.mem_support_iff] at hf ⊢
        intro hfl
        apply hf
        rw [hl', Finsupp.coe_add, Pi.add_apply, hfl, zero_add, eChain]
        by_cases hfe : f = e
        · subst hfe
          exact absurd (hev.symm.trans hfl) one_ne_zero
        · rw [Finsupp.single_eq_of_ne (by simpa using hfe)]
      have hlt : l'.support.card < n := by
        have hssub : l'.support ⊂ l.support := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => ?_⟩
          have : e ∈ l'.support := by rw [heq]; exact he
          exact (Finsupp.mem_support_iff.mp this) hl'e
        calc l'.support.card < l.support.card := Finset.card_lt_card hssub
          _ = n := hcard
      exact GWalk.step ⟨e, he, hedge⟩ ((ih l'.support.card hlt l' rfl huq hbd).mono hsub)

/-- **Capstone: a chain yields a path.**  If `l` is a chain from the grid vertex `p` to the grid
vertex `q` (`p ≠ q`), all of whose edges avoid the closed set `K`, and `p` itself is outside `K`,
then `p` and `q` are joined inside the complement of `K`. -/
theorem joinedIn_of_chain {h : ℝ} {K : Set Pt} {l : Chain1} {p q : ℤ × ℤ} (hpq : p ≠ q)
    (hpK : gptH h p ∉ K)
    (hb : ∀ v : ℤ × ℤ, bdry1 ((l : Chain1) : Edge → ZMod 2) v
      = (if v = p then 1 else 0) + (if v = q then 1 else 0))
    (hav : ∀ e ∈ l.support, Disjoint (gseg h e) K) :
    JoinedIn (Kᶜ) (gptH h p) (gptH h q) :=
  (gWalk_of_chain l.support.card l rfl hpq hb).toJoinedIn hav hpK

end

end Work.Whitney.PathTools.Grid
