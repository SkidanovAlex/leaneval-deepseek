import Mathlib
import Submission.CDT.RatFuncDeriv
import Submission.Work.GenShared.periods_defs
import Submission.Work.GenShared.hasDerivAt_rval
import Submission.Work.GenShared.rreg_Dv

/-!
# The generic period-independence argument (area C17y, module `gen_van`)

This file sets up the differential-module vocabulary used by the generic period-independence
theorem `periods_indep_gen` and by its instances (`Work.C17.y1_periods_indep_gen`).

* `Rval` (from `Work.GenShared.periods_defs`) is the value of a rational function, read off
  from its canonical numerator/denominator; here we record the elementary algebra of `Rval`
  (`Rval_mul`, `Rval_add`, ...) at points where the denominators do not vanish.
* `Van x0 δ y1 J n` is the *vanishing predicate*: the function `Wev y1 J n` vanishes on the
  ball of radius `δ` around `x0`, except at finitely many points.
* `Nsub` is the `K`-submodule (`K = ℂ(x)`) of all relations, i.e. of all `n : W k` with `Van`.
  It is stable under the connection `Dv`, which is what feeds the constant-echelon lemma
  (`Work.C17y.dstable_const`).
-/

namespace Work.C17y

open Complex Metric
open Submission.CDT (dRat)
open Work.GenShared (Rval Rreg W Dv Wev)

noncomputable section




/-! ## 1. Elementary algebra of `Rval` -/

/-- `Rval` is `RatFunc.eval (RingHom.id ℂ)`. -/
lemma Rval_eq_ratFunc_eval (f : RatFunc ℂ) (z : ℂ) : Rval f z = RatFunc.eval (RingHom.id ℂ) z f := by
  rw [RatFunc.eval]
  simp [Rval, Polynomial.eval₂_id]

/-- `Rval` of the image of a polynomial. -/
lemma Rval_algebraMap (p : Polynomial ℂ) (z : ℂ) :
    Rval (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) z = p.eval z := by
  rw [Rval, RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
  simp

/-- `Rval` of a constant. -/
lemma Rval_algebraMap_C (c : ℂ) (z : ℂ) :
    Rval (algebraMap ℂ (RatFunc ℂ) c) z = c := by
  have h : (algebraMap ℂ (RatFunc ℂ) c)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) := by
    rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ)]
  rw [h, Rval_algebraMap, Polynomial.eval_C]

/-- `Rval` is multiplicative where both denominators do not vanish. -/
lemma Rval_mul (f g : RatFunc ℂ) (z : ℂ) (hf : f.denom.eval z ≠ 0) (hg : g.denom.eval z ≠ 0) :
    Rval (f * g) z = Rval f z * Rval g z := by
  have h := RatFunc.eval_mul (RingHom.id ℂ) z (x := f) (y := g)
    (by simpa [Polynomial.eval₂_id] using hf) (by simpa [Polynomial.eval₂_id] using hg)
  rw [Rval_eq_ratFunc_eval (f * g), Rval_eq_ratFunc_eval f, Rval_eq_ratFunc_eval g, ← h]

/-- `Rval` is additive where both denominators do not vanish. -/
lemma Rval_add (f g : RatFunc ℂ) (z : ℂ) (hf : f.denom.eval z ≠ 0) (hg : g.denom.eval z ≠ 0) :
    Rval (f + g) z = Rval f z + Rval g z := by
  have h := RatFunc.eval_add (RingHom.id ℂ) z (x := f) (y := g)
    (by simpa [Polynomial.eval₂_id] using hf) (by simpa [Polynomial.eval₂_id] using hg)
  rw [Rval_eq_ratFunc_eval (f + g), Rval_eq_ratFunc_eval f, Rval_eq_ratFunc_eval g, ← h]

/-- `Rval` of `-f`, at a point where `f` is regular. -/
lemma Rval_neg (f : RatFunc ℂ) (z : ℂ) (hf : f.denom.eval z ≠ 0) : Rval (-f) z = -Rval f z := by
  rw [show (-f : RatFunc ℂ) = f * (-1) by ring,
    Rval_mul f (-1) z hf (Work.GenShared.rreg_neg_one z),
    show Rval (-1 : RatFunc ℂ) z = -1 from by
      rw [show (-1 : RatFunc ℂ) = algebraMap ℂ (RatFunc ℂ) (-1) from by simp, Rval_algebraMap_C]]
  ring

/-- `Rval` is subtractive where both denominators do not vanish. -/
lemma Rval_sub (f g : RatFunc ℂ) (z : ℂ) (hf : f.denom.eval z ≠ 0) (hg : g.denom.eval z ≠ 0) :
    Rval (f - g) z = Rval f z - Rval g z := by
  rw [sub_eq_add_neg, sub_eq_add_neg, Rval_add _ _ _ hf (Work.GenShared.rreg_neg hg),
    Rval_neg g z hg]

lemma rreg_sum_finset {ι : Type*} (s : Finset ι) (g : ι → RatFunc ℂ) {z : ℂ}
    (hg : ∀ i ∈ s, (g i).denom.eval z ≠ 0) : ((∑ i ∈ s, g i)).denom.eval z ≠ 0 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.sum_insert has]
      exact Work.GenShared.rreg_add (hg a (Finset.mem_insert_self a s))
        (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

/-- `Rval` of a finite sum, where all denominators do not vanish. -/
lemma Rval_sum {ι : Type*} [Fintype ι] (g : ι → RatFunc ℂ) (z : ℂ)
    (hg : ∀ i, (g i).denom.eval z ≠ 0) : Rval (∑ i, g i) z = ∑ i, Rval (g i) z := by
  classical
  have key : ∀ s : Finset ι, (∀ i ∈ s, (g i).denom.eval z ≠ 0) →
      Rval (∑ i ∈ s, g i) z = ∑ i ∈ s, Rval (g i) z := by
    intro s
    induction s using Finset.induction with
    | empty => intro _; simp [Rval]
    | insert a s has ih =>
        intro hs
        rw [Finset.sum_insert has, Finset.sum_insert has]
        have ha : (g a).denom.eval z ≠ 0 := hs a (Finset.mem_insert_self a s)
        have hs' : ∀ i ∈ s, (g i).denom.eval z ≠ 0 :=
          fun i hi => hs i (Finset.mem_insert_of_mem hi)
        rw [Rval_add _ _ _ ha (rreg_sum_finset s g hs'), ih hs']
  simpa using key Finset.univ (fun i _ => hg i)

lemma Rval_zero (z : ℂ) : Rval (0 : RatFunc ℂ) z = 0 := by simp [Rval]
lemma Rval_one (z : ℂ) : Rval (1 : RatFunc ℂ) z = 1 := by
  simpa using Rval_algebraMap_C 1 z


/-! ## 2. The vanishing predicate and the relation module -/

/-- The poles of a single rational function. -/
def polesSet1 (f : RatFunc ℂ) : Set ℂ := {z | f.denom.eval z = 0}

lemma polesSet1_finite (f : RatFunc ℂ) : (polesSet1 f).Finite :=
  (Polynomial.finite_setOfPred_isRoot (RatFunc.denom_ne_zero f)).subset
    (fun z hz => by simpa [polesSet1, Polynomial.IsRoot.def] using hz)

lemma not_mem_polesSet1 {f : RatFunc ℂ} {z : ℂ} (h : z ∉ polesSet1 f) : Rreg f z := by
  intro hh
  exact h (by simpa [polesSet1] using hh)

/-- The (finite) set of poles of the coefficient tuple `n`. -/
def polesSet {k : ℕ} (n : W k) : Set ℂ :=
  polesSet1 n.1 ∪ polesSet1 n.2.1 ∪ ⋃ i : Fin k, polesSet1 (n.2.2 i)

lemma polesSet_finite {k : ℕ} (n : W k) : (polesSet n).Finite := by
  rw [polesSet]
  refine (polesSet1_finite n.1 |>.union (polesSet1_finite n.2.1)).union ?_
  exact Set.Finite.iUnion (Set.finite_univ) (fun i _ => polesSet1_finite (n.2.2 i))
    (fun i hi => absurd (Set.mem_univ i) hi)

lemma not_mem_polesSet {k : ℕ} {n : W k} {z : ℂ} (hz : z ∉ polesSet n) :
    Rreg n.1 z ∧ Rreg n.2.1 z ∧ ∀ i, Rreg (n.2.2 i) z := by
  rw [polesSet] at hz
  simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hz
  exact ⟨hz.1.1, hz.1.2, fun i => hz.2 i⟩

/-- **The vanishing predicate**: the function `Wev y1 J n` vanishes on the ball `ball x0 δ`
except at finitely many points. -/
def Van {k : ℕ} (x0 : ℂ) (δ : ℝ) (y1 : ℂ → ℂ) (J : Fin k → ℂ → ℂ) (n : W k) : Prop :=
  ∃ F : Finset ℂ, ∀ z ∈ Metric.ball x0 δ, z ∉ (F : Set ℂ) → Wev y1 J n z = 0

/-- Linearity of `Wev` in the coefficient tuple, at a point where all denominators are nonzero. -/
lemma Wev_add {k : ℕ} (y1 : ℂ → ℂ) (J : Fin k → ℂ → ℂ) (n n' : W k) {z : ℂ}
    (h1 : Rreg n.1 z) (h1' : Rreg n'.1 z) (h2 : Rreg n.2.1 z) (h2' : Rreg n'.2.1 z)
    (h3 : ∀ i, Rreg (n.2.2 i) z) (h3' : ∀ i, Rreg (n'.2.2 i) z) :
    Wev y1 J (n + n') z = Wev y1 J n z + Wev y1 J n' z := by
  have e1 : (n + n').1 = n.1 + n'.1 := rfl
  have e2 : (n + n').2.1 = n.2.1 + n'.2.1 := rfl
  have e3 : (n + n').2.2 = n.2.2 + n'.2.2 := rfl
  simp only [Wev, e1, e2, e3]
  rw [Rval_add _ _ _ h1 h1', Rval_add _ _ _ h2 h2']
  have hsum : (∑ i, Rval ((n.2.2 + n'.2.2) i) z * J i z)
      = (∑ i, Rval (n.2.2 i) z * J i z) + ∑ i, Rval (n'.2.2 i) z * J i z := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, Rval_add _ _ _ (h3 i) (h3' i), add_mul]
  rw [hsum]
  ring

/-- `Wev` is `K`-linear in the coefficient tuple, at a point where all denominators are nonzero. -/
lemma Wev_smul {k : ℕ} (y1 : ℂ → ℂ) (J : Fin k → ℂ → ℂ) (c : RatFunc ℂ) (n : W k) {z : ℂ}
    (hc : Rreg c z) (h1 : Rreg n.1 z) (h2 : Rreg n.2.1 z) (h3 : ∀ i, Rreg (n.2.2 i) z) :
    Wev y1 J (c • n) z = Rval c z * Wev y1 J n z := by
  have e1 : (c • n).1 = c * n.1 := by simp [smul_eq_mul]
  have e2 : (c • n).2.1 = c * n.2.1 := by simp [smul_eq_mul]
  have e3 : (c • n).2.2 = fun i => c * n.2.2 i := by
    funext i; simp [smul_eq_mul]
  simp only [Wev, e1, e2, e3]
  rw [Rval_mul _ _ _ hc h1, Rval_mul _ _ _ hc h2]
  have hsum : (∑ i, Rval (c * n.2.2 i) z * J i z)
      = Rval c z * ∑ i, Rval (n.2.2 i) z * J i z := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Rval_mul _ _ _ hc (h3 i)]; ring
  rw [hsum]
  ring

theorem van_zero {k : ℕ} (x0 : ℂ) (δ : ℝ) (y1 : ℂ → ℂ) (J : Fin k → ℂ → ℂ) :
    Van x0 δ y1 J (0 : W k) :=
  ⟨∅, by intro z _ _; simp [Wev, Rval]⟩

theorem van_add {k : ℕ} {x0 : ℂ} {δ : ℝ} {y1 : ℂ → ℂ} {J : Fin k → ℂ → ℂ} {n n' : W k}
    (hn : Van x0 δ y1 J n) (hn' : Van x0 δ y1 J n') : Van x0 δ y1 J (n + n') := by
  obtain ⟨F, hF⟩ := hn
  obtain ⟨F', hF'⟩ := hn'
  refine ⟨(F ∪ F') ∪ (polesSet_finite n |>.union (polesSet_finite n')).toFinset, ?_⟩
  intro z hz hzF
  have hFsub : F ⊆ (F ∪ F') ∪ (polesSet_finite n |>.union (polesSet_finite n')).toFinset := by
    intro a ha; simp only [Finset.mem_union]; exact Or.inl (Or.inl ha)
  have hF'sub : F' ⊆ (F ∪ F') ∪ (polesSet_finite n |>.union (polesSet_finite n')).toFinset := by
    intro a ha; simp only [Finset.mem_union]; exact Or.inl (Or.inr ha)
  have hSsub : (polesSet_finite n |>.union (polesSet_finite n')).toFinset
      ⊆ (F ∪ F') ∪ (polesSet_finite n |>.union (polesSet_finite n')).toFinset := by
    intro a ha; simp only [Finset.mem_union]; exact Or.inr ha
  have hnz : z ∉ (F : Set ℂ) := fun h => hzF (Finset.mem_coe.mpr (hFsub (Finset.mem_coe.mp h)))
  have hn'z : z ∉ (F' : Set ℂ) := fun h => hzF (Finset.mem_coe.mpr (hF'sub (Finset.mem_coe.mp h)))
  have hzp : z ∉ polesSet n ∪ polesSet n' := by
    intro h
    refine hzF (Finset.mem_coe.mpr (hSsub ?_))
    exact (Set.Finite.mem_toFinset (polesSet_finite n |>.union (polesSet_finite n'))).mpr h
  obtain ⟨hzp1, hzp2⟩ := not_or.mp hzp
  obtain ⟨ha, hb, hc⟩ := not_mem_polesSet hzp1
  obtain ⟨ha', hb', hc'⟩ := not_mem_polesSet hzp2
  rw [Wev_add y1 J n n' ha ha' hb hb' hc hc', hF z hz hnz, hF' z hz hn'z, add_zero]

theorem van_smul {k : ℕ} {x0 : ℂ} {δ : ℝ} {y1 : ℂ → ℂ} {J : Fin k → ℂ → ℂ} {n : W k}
    (c : RatFunc ℂ) (hn : Van x0 δ y1 J n) : Van x0 δ y1 J (c • n) := by
  obtain ⟨F, hF⟩ := hn
  refine ⟨F ∪ (polesSet1_finite c |>.union (polesSet_finite n)).toFinset, ?_⟩
  intro z hz hzF
  have hFsub : F ⊆ F ∪ (polesSet1_finite c |>.union (polesSet_finite n)).toFinset := by
    intro a ha; simp only [Finset.mem_union]; exact Or.inl ha
  have hSsub : (polesSet1_finite c |>.union (polesSet_finite n)).toFinset
      ⊆ F ∪ (polesSet1_finite c |>.union (polesSet_finite n)).toFinset := by
    intro a ha; simp only [Finset.mem_union]; exact Or.inr ha
  have hnz : z ∉ (F : Set ℂ) := fun h => hzF (Finset.mem_coe.mpr (hFsub (Finset.mem_coe.mp h)))
  have hzp : z ∉ polesSet1 c ∪ polesSet n := by
    intro h
    refine hzF (Finset.mem_coe.mpr (hSsub ?_))
    exact (Set.Finite.mem_toFinset (polesSet1_finite c |>.union (polesSet_finite n))).mpr h
  obtain ⟨hzp1, hzp2⟩ := not_or.mp hzp
  have hc : Rreg c z := hzp1
  obtain ⟨ha, hb, hc'⟩ := not_mem_polesSet hzp2
  rw [Wev_smul y1 J c n hc ha hb hc', hF z hz hnz, mul_zero]

/-- The relation module: all coefficient tuples whose relation function vanishes on the ball off a
finite set. -/
def Nsub {k : ℕ} (x0 : ℂ) (δ : ℝ) (y1 : ℂ → ℂ) (J : Fin k → ℂ → ℂ) :
    Submodule (RatFunc ℂ) (W k) where
  carrier := {n | Van x0 δ y1 J n}
  zero_mem' := van_zero x0 δ y1 J
  add_mem' := fun {_ _} hn hn' => van_add hn hn'
  smul_mem' := fun c {_} hn => van_smul c hn

/-- The `(e₀,e₁)`-part: the submodule of coefficient tuples with vanishing integral block. -/
def Msub {k : ℕ} : Submodule (RatFunc ℂ) (W k) where
  carrier := {n | n.2.2 = 0}
  zero_mem' := rfl
  add_mem' := fun {x y} hx hy => by
    show (x + y).2.2 = 0
    rw [show (x + y).2.2 = x.2.2 + y.2.2 from rfl, hx, hy, add_zero]
  smul_mem' := fun c {x} hx => by
    show (c • x).2.2 = 0
    have : (c • x).2.2 = fun i => c * x.2.2 i := by funext i; simp [smul_eq_mul]
    rw [this, hx]
    funext i; simp

/-- The projection onto the integral block. -/
def proj3 {k : ℕ} : W k →ₗ[RatFunc ℂ] (Fin k → RatFunc ℂ) where
  toFun := fun n => n.2.2
  map_add' := fun x y => rfl
  map_smul' := fun c x => rfl

/-! ## 3. Elementary analytic facts -/

/-- A ball with finitely many points removed is dense in the ball. -/
lemma mem_closure_ball_sdiff_finset {x0 : ℂ} {δ : ℝ} {F : Finset ℂ} {z : ℂ}
    (hz : z ∈ Metric.ball x0 δ) : z ∈ closure (Metric.ball x0 δ \ (F : Set ℂ)) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hzδ : dist z x0 < δ := by rwa [Metric.mem_ball] at hz
  set r : ℝ := min ε (δ - dist z x0) with hr
  have hrpos : 0 < r := lt_min hε (by linarith)
  have hbad : ({t : ℝ | (z + (t : ℂ)) ∈ (F : Set ℂ)}).Finite := by
    have hinj : Function.Injective (fun t : ℝ => (z + (t : ℂ))) := by
      intro t1 t2 h
      have : ((t1 : ℂ)) = ((t2 : ℂ)) := by simpa using add_left_cancel h
      exact_mod_cast this
    exact (F.finite_toSet).preimage (fun _ _ _ _ h => hinj h)
  obtain ⟨t, ht⟩ := ((Set.Ioo_infinite hrpos).sdiff hbad).nonempty
  rw [Set.mem_sdiff, Set.mem_Ioo] at ht
  obtain ⟨⟨ht0, htr⟩, htF⟩ := ht
  have htδ : t < δ - dist z x0 := by
    rw [hr] at htr; exact lt_of_lt_of_le htr (min_le_right ε (δ - dist z x0))
  have htε : t < ε := by
    rw [hr] at htr; exact lt_of_lt_of_le htr (min_le_left ε (δ - dist z x0))
  have hnorm : ‖((t : ℝ) : ℂ)‖ = t := by
    rw [show ‖((t : ℝ) : ℂ)‖ = |t| from RCLike.norm_ofReal t, abs_of_pos ht0]
  have hdt : dist (z + (t : ℂ)) z = t := by
    rw [dist_eq_norm, show z + (t : ℂ) - z = ((t : ℝ) : ℂ) from by ring, hnorm]
  have hdz : dist (z + (t : ℂ)) x0 ≤ dist z x0 + t := by
    have h1 : dist (z + (t : ℂ)) x0 = ‖(z - x0) + ((t : ℝ) : ℂ)‖ := by
      rw [dist_eq_norm, show z + (t : ℂ) - x0 = (z - x0) + ((t : ℝ) : ℂ) from by ring]
    have h2 : dist z x0 = ‖z - x0‖ := dist_eq_norm ..
    rw [h1, h2]
    calc ‖(z - x0) + ((t : ℝ) : ℂ)‖ ≤ ‖z - x0‖ + ‖((t : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = ‖z - x0‖ + t := by rw [hnorm]
  refine ⟨z + (t : ℂ), ⟨?_, htF⟩, ?_⟩
  · rw [Metric.mem_ball]
    linarith
  · rw [dist_comm]
    exact lt_of_le_of_lt (le_of_eq hdt) htε

/-- If a continuous function on the ball vanishes off a finite set, it vanishes identically. -/
lemma eq_zero_of_forall_zero_of_notMem {x0 : ℂ} {δ : ℝ} {y1 : ℂ → ℂ} {F : Finset ℂ}
    (hy1c : ContinuousOn y1 (Metric.ball x0 δ))
    (h : ∀ z ∈ Metric.ball x0 δ, z ∉ (F : Set ℂ) → y1 z = 0) :
    ∀ z ∈ Metric.ball x0 δ, y1 z = 0 := by
  intro z hz
  have hdense : z ∈ closure (Metric.ball x0 δ \ (F : Set ℂ)) := mem_closure_ball_sdiff_finset hz
  have hopen : IsOpen (Metric.ball x0 δ ∩ {w : ℂ | y1 w ≠ 0}) :=
    hy1c.isOpen_inter_preimage Metric.isOpen_ball isOpen_ne
  have hsub : (Metric.ball x0 δ \ (F : Set ℂ)) ⊆ (Metric.ball x0 δ ∩ {w : ℂ | y1 w ≠ 0})ᶜ := by
    intro w hw
    rw [Set.mem_sdiff] at hw
    rw [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_setOf_eq, not_and]
    exact fun _ hw0 => hw0 (h w hw.1 hw.2)
  have hz' : z ∈ closure (Metric.ball x0 δ ∩ {w : ℂ | y1 w ≠ 0})ᶜ := closure_mono hsub hdense
  rw [hopen.isClosed_compl.closure_eq, Set.mem_compl_iff] at hz'
  by_contra hne
  exact hz' ⟨hz, hne⟩

/-- Derivative of the inverse in `ℂ(x)`. -/
lemma dRat_inv (b : RatFunc ℂ) (hb : b ≠ 0) :
    Submission.CDT.dRat b⁻¹ = -(Submission.CDT.dRat b) * (b ^ 2)⁻¹ := by
  have h2 : Submission.CDT.dRat b * b⁻¹ + b * Submission.CDT.dRat b⁻¹ = 0 := by
    have h := congrArg Submission.CDT.dRat (mul_inv_cancel₀ hb)
    rw [Submission.CDT.dRat_one] at h
    rw [Submission.CDT.dRat_mul] at h
    exact h
  have h3 : b * Submission.CDT.dRat b⁻¹ = -(Submission.CDT.dRat b * b⁻¹) := by
    linear_combination h2
  calc Submission.CDT.dRat b⁻¹ = b⁻¹ * (b * Submission.CDT.dRat b⁻¹) := by
        rw [← mul_assoc, inv_mul_cancel₀ hb, one_mul]
    _ = b⁻¹ * (-(Submission.CDT.dRat b * b⁻¹)) := by rw [h3]
    _ = -(Submission.CDT.dRat b) * (b ^ 2)⁻¹ := by rw [← inv_pow]; ring

/-- **The Riccati consequence of the determinant identity.**  If the Cramer determinant
`a (a + b' - (p₁/p₂) b) - b (a' - (p₀/p₂) b)` vanishes and `b ≠ 0`, then the Riccati equation of
`p₂ y'' + p₁ y' + p₀ y` has the rational solution `u = -a/b`. -/
lemma exists_riccati_of_det_eq_zero (p2 p1 p0 : Polynomial ℂ) (hp2 : p2 ≠ 0) (a b : RatFunc ℂ)
    (hb : b ≠ 0)
    (h : a * (a + Submission.CDT.dRat b - (algebraMap (Polynomial ℂ) (RatFunc ℂ) p1
            / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) * b)
          - b * (Submission.CDT.dRat a - (algebraMap (Polynomial ℂ) (RatFunc ℂ) p0
            / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) * b) = 0) :
    ∃ u : RatFunc ℂ, algebraMap (Polynomial ℂ) (RatFunc ℂ) p2 * (Submission.CDT.dRat u + u ^ 2)
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) p1 * u + algebraMap (Polynomial ℂ) (RatFunc ℂ) p0 = 0 := by
  have hP2 : algebraMap (Polynomial ℂ) (RatFunc ℂ) p2 ≠ 0 := fun hh =>
    hp2 (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) (by simpa using hh))
  have hdRat : Submission.CDT.dRat (-(a / b))
      = -(Submission.CDT.dRat a * b⁻¹) + a * Submission.CDT.dRat b * (b ^ 2)⁻¹ := by
    rw [show (-(a / b) : RatFunc ℂ) = -(a * b⁻¹) by rw [div_eq_mul_inv],
      Submission.CDT.dRat_neg, Submission.CDT.dRat_mul, dRat_inv b hb]
    ring
  have key : b ^ 2 * (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2
        * (Submission.CDT.dRat (-(a / b)) + (-(a / b)) ^ 2)
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) p1 * (-(a / b))
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) p0)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) p2
        * (a * (a + Submission.CDT.dRat b - (algebraMap (Polynomial ℂ) (RatFunc ℂ) p1
            / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) * b)
          - b * (Submission.CDT.dRat a - (algebraMap (Polynomial ℂ) (RatFunc ℂ) p0
            / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) * b)) := by
    rw [hdRat]
    field_simp
    ring
  refine ⟨-(a / b), ?_⟩
  have h0 : b ^ 2 * (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2
        * (Submission.CDT.dRat (-(a / b)) + (-(a / b)) ^ 2)
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) p1 * (-(a / b))
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) p0) = 0 := by rw [key, h, mul_zero]
  exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero 2 hb)

end
end Work.C17y
