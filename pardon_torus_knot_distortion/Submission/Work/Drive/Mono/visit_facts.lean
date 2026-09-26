import Mathlib
import Submission.Work.Drive.Mono.LevelCountDefs
import Submission.Work.Drive.Mono.visit_structure

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-!
## Facts about a single visit of the knot to the box-and-slab

Let `slabVisit K s c σ u v h` be the set of parameters at which the knot lies in the open box
`PBox s c σ` and in the open tilted slab `|⟪v,·⟫ - (⟪v,c⟫+u)| < h`.  Its connected components are
the *visits* of the knot to the box-and-slab.

Under the "no grazing visit" hypotheses of `Work.Drive.Mono.ae_levelCount_lt_min`, every visit

* crosses the cutting plane `⟪v,·⟫ = ⟪v,c⟫+u` exactly once;
* is contained in an open interval of length `< 2π` (so the closure of a visit contains no two
  parameters differing by a non-zero multiple of `2π`);
* has at most two wall/face parameters on its closure.

The first two statements are the content of `Work.Drive.Mono.visit_facts`; the last is the
"decoration" count used by the level count.
-/

variable {K : Knot} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ}

/-- The closure of the slab visit lies in the closed box-and-slab. -/
theorem closure_slabVisit_le {t : ℝ} (ht : t ∈ closure (slabVisit K s c σ u v h)) :
    boxA K s c σ t ≤ 0 ∧ |cutG K c u v t| ≤ h := by
  refine ⟨?_, ?_⟩
  · exact closure_minimal (fun y hy => hy.1.le)
      (isClosed_le continuous_boxA continuous_const) ht
  · exact closure_minimal (fun y hy => hy.2.le)
      (isClosed_le continuous_cutG.abs continuous_const) ht

/-- A point of the closure of the slab visit which is not itself a visit is on a slab face or on
the box sphere; in the latter case the box-sphere hypothesis applies, and either way
`|cutG| = h` there. -/
theorem abs_cutG_eq_h_of_mem_closure_sdiff
    (hboxsph : ∀ t : ℝ, Submission.boxNorm c σ (K.curve t) = s → h ≤ |cutG K c u v t|)
    {t : ℝ} (ht : t ∈ closure (slabVisit K s c σ u v h))
    (htnot : t ∉ slabVisit K s c σ u v h) :
    |cutG K c u v t| = h := by
  obtain ⟨hbox, hcut⟩ := closure_slabVisit_le (K := K) (s := s) (c := c) (σ := σ)
    (u := u) (v := v) (h := h) ht
  by_cases hlt : boxA K s c σ t < 0
  · have hnot : ¬ |cutG K c u v t| < h := fun hc => htnot ⟨hlt, hc⟩
    exact le_antisymm hcut (not_lt.mp hnot)
  · have hzero : boxA K s c σ t = 0 := le_antisymm hbox (not_lt.mp hlt)
    have hbn : Submission.boxNorm c σ (K.curve t) = s := by
      have := hzero
      unfold boxA at this
      linarith
    exact le_antisymm hcut (hboxsph t hbn)

/-- **A strictly monotone continuous function on an interval taking the values `-h` and `h` at the
endpoints has a unique zero in the open interval.** -/
theorem existsUnique_zero_of_strictMonoOn {f : ℝ → ℝ} {a b h : ℝ} (hh : 0 < h) (hab : a < b)
    (hcont : Continuous f) (hmono : StrictMonoOn f (Ioo a b)) (hfa : f a = -h)
    (hfb : f b = h) :
    ∃! w : ℝ, w ∈ Ioo a b ∧ f w = 0 := by
  have hex : ∃ w : ℝ, w ∈ Ioo a b ∧ f w = 0 := by
    have hmem : (0 : ℝ) ∈ Icc (f a) (f b) := by
      rw [hfa, hfb]; exact ⟨by linarith, by linarith⟩
    obtain ⟨w, hw, hw0⟩ := intermediate_value_Icc hab.le hcont.continuousOn hmem
    rw [mem_Icc] at hw
    refine ⟨w, ⟨lt_of_le_of_ne hw.1 ?_, lt_of_le_of_ne hw.2 ?_⟩, hw0⟩
    · intro he; rw [← he, hfa] at hw0; linarith
    · intro he; rw [he, hfb] at hw0; linarith
  obtain ⟨w, hwI, hw0⟩ := hex
  refine ⟨w, ⟨hwI, hw0⟩, ?_⟩
  rintro w' ⟨hw'I, hw'0⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := hmono hw'I hwI hlt
    rw [hw'0, hw0] at h
    exact absurd h (lt_irrefl 0)
  · have h := hmono hwI hw'I hgt
    rw [hw'0, hw0] at h
    exact absurd h (lt_irrefl 0)

/-- The antitone version of `existsUnique_zero_of_strictMonoOn`. -/
theorem existsUnique_zero_of_strictAntiOn {f : ℝ → ℝ} {a b h : ℝ} (hh : 0 < h) (hab : a < b)
    (hcont : Continuous f) (hanti : StrictAntiOn f (Ioo a b)) (hfa : f a = h)
    (hfb : f b = -h) :
    ∃! w : ℝ, w ∈ Ioo a b ∧ f w = 0 := by
  have hmono : StrictMonoOn (fun x => -f x) (Ioo a b) := hanti.neg
  have h := existsUnique_zero_of_strictMonoOn hh hab hcont.neg hmono
    (by simp [hfa]) (by simp [hfb])
  simpa using h

end

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology in
theorem visit_facts
    {K : Knot} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ}
    {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {exc : Finset ℝ}
    (hh : 0 < h)
    (hboxsph : ∀ t : ℝ, Submission.boxNorm c σ (K.curve t) = s →
        h ≤ |Work.Drive.Mono.cutG K c u v t|)
    (hgraze : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
        deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 →
        h ≤ |Work.Drive.Mono.cutG K c u v t|)
    (hwall : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
        |Work.Drive.Mono.cutG K c u v t| ≤ h → deriv (Work.Drive.Mono.wallW K ℓ) t ≠ 0)
    (hcorner : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
        |Work.Drive.Mono.cutG K c u v t| = h → Work.Drive.Mono.wallW K ℓ t ∈ (exc : Set ℝ))
    (hne : lam ∉ (exc : Set ℝ)) :
    ∀ z ∈ Work.Drive.Mono.slabVisit K s c σ u v h,
      (∃! w : ℝ, w ∈ Work.Drive.Mono.visit (Work.Drive.Mono.slabVisit K s c σ u v h) z ∧
        Work.Drive.Mono.cutG K c u v w = 0) ∧
      (∀ x ∈ closure (Work.Drive.Mono.visit (Work.Drive.Mono.slabVisit K s c σ u v h) z),
        ∀ y ∈ closure (Work.Drive.Mono.visit (Work.Drive.Mono.slabVisit K s c σ u v h) z),
        ∀ k : ℤ, k ≠ 0 → y - x ≠ 2 * Real.pi * (k : ℝ)) ∧
      (((Work.Drive.Mono.facePts K s c σ u v h ℓ lam ∪
          Work.Drive.Mono.wallPts K s c σ u v h ℓ lam) ∩
        closure (Work.Drive.Mono.visit (Work.Drive.Mono.slabVisit K s c σ u v h) z)).encard ≤ 2) := by
  intro z hz
  classical
  set Y : Set ℝ := slabVisit K s c σ u v h with hYdef
  set C : Set ℝ := visit Y z with hCdef
  have hYo : IsOpen Y := isOpen_slabVisit
  have hYper : ∀ t : ℝ, t + 2 * Real.pi ∈ Y ↔ t ∈ Y := fun t => slabVisit_periodic t
  have hYne : ∃ t : ℝ, t ∉ Y := slabVisit_ne_univ hgraze
  have hzY : z ∈ Y := hz
  obtain ⟨hzC, hCY, hCoord, hCopen, hbdd, ha_cl, hb_cl, haY, hbY, hcl_sub, hIoo_sub,
    hsub_Ioo⟩ := visit_structure hYo hYper hYne hzY
  set a : ℝ := sInf C with hadef
  set b : ℝ := sSup C with hbdef
  -- elementary set facts about the visit
  have hCeq : C = Ioo a b := le_antisymm hsub_Ioo hIoo_sub
  have hab : a < b := by
    have hzIoo : z ∈ Ioo a b := hsub_Ioo hzC
    exact lt_trans hzIoo.1 hzIoo.2
  have hcl_eq : closure C = Icc a b := by rw [hCeq, closure_Ioo hab.ne]
  have hcl_le : ∀ t ∈ closure C, boxA K s c σ t ≤ 0 ∧ |cutG K c u v t| ≤ h :=
    fun t ht => closure_slabVisit_le (K := K) (s := s) (c := c) (σ := σ) (u := u) (v := v)
      (h := h) (closure_mono hCY ht)
  have hboxA_le : ∀ t ∈ Icc a b, boxA K s c σ t ≤ 0 := by
    intro t ht
    exact (hcl_le t (by rw [hcl_eq]; exact ht)).1
  have hcut_le : ∀ t ∈ Icc a b, |cutG K c u v t| ≤ h := by
    intro t ht
    exact (hcl_le t (by rw [hcl_eq]; exact ht)).2
  have hcut_lt : ∀ t ∈ C, |cutG K c u v t| < h := fun t ht => (hCY ht).2
  -- the endpoint values of `cutG`
  have ha_abs : |cutG K c u v a| = h :=
    abs_cutG_eq_h_of_mem_closure_sdiff (K := K) (s := s) (c := c) (σ := σ) (u := u) (v := v)
      (h := h) hboxsph (closure_mono hCY ha_cl) haY
  have hb_abs : |cutG K c u v b| = h :=
    abs_cutG_eq_h_of_mem_closure_sdiff (K := K) (s := s) (c := c) (σ := σ) (u := u) (v := v)
      (h := h) hboxsph (closure_mono hCY hb_cl) hbY
  -- the cutting height has no critical point inside a visit
  have hder_ne : ∀ t ∈ C, deriv (cutG K c u v) t ≠ 0 :=
    fun t ht => deriv_cutG_ne_zero_of_mem_slabVisit hgraze (hCY ht)
  have hder_cont : Continuous (deriv (cutG K c u v)) :=
    (contDiff_cutG (K := K) (c := c) (u := u) (v := v)).continuous_deriv (by simp)
  have hsign : (∀ t ∈ C, 0 < deriv (cutG K c u v) t) ∨
      (∀ t ∈ C, deriv (cutG K c u v) t < 0) := by
    by_contra hcon
    rw [not_or] at hcon
    push Not at hcon
    obtain ⟨⟨x, hxC, hx0⟩, ⟨y, hyC, hy0⟩⟩ := hcon
    have hxlt : deriv (cutG K c u v) x < 0 := lt_of_le_of_ne hx0 (hder_ne x hxC)
    have hylt : 0 < deriv (cutG K c u v) y := lt_of_le_of_ne hy0 (Ne.symm (hder_ne y hyC))
    rcases le_total x y with hxy | hyx
    · have hmem : (0 : ℝ) ∈ Icc (deriv (cutG K c u v) x) (deriv (cutG K c u v) y) :=
        ⟨hxlt.le, hylt.le⟩
      obtain ⟨w, hw, hw0⟩ := intermediate_value_Icc hxy hder_cont.continuousOn hmem
      exact hder_ne w (hCoord.out hxC hyC hw) hw0
    · have hmem : (0 : ℝ) ∈ Icc (deriv (cutG K c u v) x) (deriv (cutG K c u v) y) :=
        ⟨hxlt.le, hylt.le⟩
      obtain ⟨w, hw, hw0⟩ := intermediate_value_Icc' hyx hder_cont.continuousOn hmem
      exact hder_ne w (hCoord.out hyC hxC hw) hw0
  -- the visit crosses the plane exactly once, and the two endpoint values differ
  have hmain : (∃! w : ℝ, w ∈ C ∧ cutG K c u v w = 0) ∧
      (cutG K c u v a ≠ cutG K c u v b) := by
    rcases hsign with hpos | hneg
    · have hmonoC : StrictMonoOn (cutG K c u v) C := by
        rw [hCeq]
        refine strictMonoOn_of_deriv_pos (convex_Ioo a b) continuous_cutG.continuousOn ?_
        intro x hx
        rw [interior_Ioo] at hx
        exact hpos x (by rw [hCeq]; exact hx)
      have ha_le : ∀ t ∈ C, cutG K c u v a ≤ cutG K c u v t := by
        intro t ht
        have hat : a < t := (hsub_Ioo ht).1
        have hsub' : Ioo a t ⊆ {r : ℝ | cutG K c u v r ≤ cutG K c u v t} := by
          intro r hr
          have hrC : r ∈ C := by
            rw [hCeq]; exact ⟨hr.1, lt_trans hr.2 (hsub_Ioo ht).2⟩
          exact (hmonoC hrC ht hr.2).le
        refine closure_minimal hsub' (isClosed_le continuous_cutG continuous_const) ?_
        rw [closure_Ioo hat.ne]
        exact ⟨le_rfl, hat.le⟩
      have hb_ge : ∀ t ∈ C, cutG K c u v t ≤ cutG K c u v b := by
        intro t ht
        have htb : t < b := (hsub_Ioo ht).2
        have hsub' : Ioo t b ⊆ {r : ℝ | cutG K c u v t ≤ cutG K c u v r} := by
          intro r hr
          have hrC : r ∈ C := by
            rw [hCeq]; exact ⟨lt_trans (hsub_Ioo ht).1 hr.1, hr.2⟩
          exact (hmonoC ht hrC hr.1).le
        refine closure_minimal hsub' (isClosed_le continuous_const continuous_cutG) ?_
        rw [closure_Ioo htb.ne]
        exact ⟨htb.le, le_rfl⟩
      have ha_val : cutG K c u v a = -h := by
        have h1 : cutG K c u v a < h :=
          lt_of_le_of_lt (ha_le z hzC) ((abs_lt.mp (hcut_lt z hzC)).2)
        rcases (abs_eq hh.le).mp ha_abs with h' | h'
        · exact absurd h' (ne_of_lt h1)
        · exact h'
      have hb_val : cutG K c u v b = h := by
        have h1 : -h < cutG K c u v b :=
          lt_of_lt_of_le ((abs_lt.mp (hcut_lt z hzC)).1) (hb_ge z hzC)
        rcases (abs_eq hh.le).mp hb_abs with h' | h'
        · exact h'
        · exact absurd h1 (not_lt.mpr (le_of_eq h'))
      have hmono' : StrictMonoOn (cutG K c u v) (Ioo a b) := by rwa [hCeq] at hmonoC
      have hzun : ∃! w : ℝ, w ∈ C ∧ cutG K c u v w = 0 := by
        have h := existsUnique_zero_of_strictMonoOn hh hab continuous_cutG hmono' ha_val hb_val
        rwa [hCeq]
      refine ⟨hzun, ?_⟩
      rw [ha_val, hb_val]
      intro he
      linarith
    · have hantiC : StrictAntiOn (cutG K c u v) C := by
        rw [hCeq]
        refine strictAntiOn_of_deriv_neg (convex_Ioo a b) continuous_cutG.continuousOn ?_
        intro x hx
        rw [interior_Ioo] at hx
        exact hneg x (by rw [hCeq]; exact hx)
      have ha_ge : ∀ t ∈ C, cutG K c u v t ≤ cutG K c u v a := by
        intro t ht
        have hat : a < t := (hsub_Ioo ht).1
        have hsub' : Ioo a t ⊆ {r : ℝ | cutG K c u v t ≤ cutG K c u v r} := by
          intro r hr
          have hrC : r ∈ C := by
            rw [hCeq]; exact ⟨hr.1, lt_trans hr.2 (hsub_Ioo ht).2⟩
          exact (hantiC hrC ht hr.2).le
        refine closure_minimal hsub' (isClosed_le continuous_const continuous_cutG) ?_
        rw [closure_Ioo hat.ne]
        exact ⟨le_rfl, hat.le⟩
      have hb_le : ∀ t ∈ C, cutG K c u v b ≤ cutG K c u v t := by
        intro t ht
        have htb : t < b := (hsub_Ioo ht).2
        have hsub' : Ioo t b ⊆ {r : ℝ | cutG K c u v r ≤ cutG K c u v t} := by
          intro r hr
          have hrC : r ∈ C := by
            rw [hCeq]; exact ⟨lt_trans (hsub_Ioo ht).1 hr.1, hr.2⟩
          exact (hantiC ht hrC hr.1).le
        refine closure_minimal hsub' (isClosed_le continuous_cutG continuous_const) ?_
        rw [closure_Ioo htb.ne]
        exact ⟨htb.le, le_rfl⟩
      have ha_val : cutG K c u v a = h := by
        have h1 : -h < cutG K c u v a :=
          lt_of_lt_of_le ((abs_lt.mp (hcut_lt z hzC)).1) (ha_ge z hzC)
        rcases (abs_eq hh.le).mp ha_abs with h' | h'
        · exact h'
        · exact absurd h1 (not_lt.mpr (le_of_eq h'))
      have hb_val : cutG K c u v b = -h := by
        have h1 : cutG K c u v b < h :=
          lt_of_le_of_lt (hb_le z hzC) ((abs_lt.mp (hcut_lt z hzC)).2)
        rcases (abs_eq hh.le).mp hb_abs with h' | h'
        · exact absurd h' (ne_of_lt h1)
        · exact h'
      have hanti' : StrictAntiOn (cutG K c u v) (Ioo a b) := by rwa [hCeq] at hantiC
      have hzun : ∃! w : ℝ, w ∈ C ∧ cutG K c u v w = 0 := by
        have h := existsUnique_zero_of_strictAntiOn hh hab continuous_cutG hanti' ha_val hb_val
        rwa [hCeq]
      refine ⟨hzun, ?_⟩
      rw [ha_val, hb_val]
      intro he
      linarith
  -- the visit is short: `b - a < 2π`
  have hba_le : b - a ≤ 2 * Real.pi := by
    by_contra hgt
    push Not at hgt
    have hbdd' : BddAbove C := by
      obtain ⟨a', b', hab'⟩ := hbdd
      exact ⟨b', fun x hx => (hab' hx).2⟩
    have htC : (a + (b - 2 * Real.pi)) / 2 ∈ C := by
      rw [hCeq]
      exact ⟨by linarith [hgt], by linarith [hab, Real.pi_pos]⟩
    have ht2C : (a + (b - 2 * Real.pi)) / 2 + 2 * Real.pi ∈ C := by
      rw [hCeq]
      exact ⟨by linarith [hab, Real.pi_pos], by linarith [hgt]⟩
    have hpreC : IsPreconnected C := isPreconnected_connectedComponentIn
    have hpreSh : IsPreconnected ((fun t : ℝ => t + 2 * Real.pi) '' C) :=
      hpreC.image _ ((continuous_id.add continuous_const).continuousOn)
    have hshift_sub : (fun t : ℝ => t + 2 * Real.pi) '' C ⊆ Y := by
      rintro r ⟨t, ht, rfl⟩
      exact (hYper t).mpr (hCY ht)
    have hpreU : IsPreconnected (C ∪ (fun t : ℝ => t + 2 * Real.pi) '' C) :=
      IsPreconnected.union ((a + (b - 2 * Real.pi)) / 2 + 2 * Real.pi) ht2C
        ⟨(a + (b - 2 * Real.pi)) / 2, htC, rfl⟩ hpreC hpreSh
    have hsubU : C ∪ (fun t : ℝ => t + 2 * Real.pi) '' C ⊆ Y :=
      union_subset hCY hshift_sub
    have hsubC : C ∪ (fun t : ℝ => t + 2 * Real.pi) '' C ⊆ C :=
      hpreU.subset_connectedComponentIn (Or.inl hzC) hsubU
    have hshift_le : ∀ t ∈ C, t + 2 * Real.pi ≤ b := fun t ht =>
      le_csSup hbdd' (hsubC (Or.inr ⟨t, ht, rfl⟩))
    have hle' : b ≤ b - 2 * Real.pi := by
      refine csSup_le ⟨z, hzC⟩ (fun t ht => ?_)
      have := hshift_le t ht
      linarith
    linarith [Real.pi_pos]
  have hba_lt : b - a < 2 * Real.pi := by
    rcases lt_or_eq_of_le hba_le with h | h
    · exact h
    · exfalso
      have hb_eq : b = a + 2 * Real.pi := by linarith
      have heq : cutG K c u v b = cutG K c u v a := by
        rw [hb_eq]
        exact periodic_cutG a
      exact hmain.2 heq.symm
  refine ⟨hmain.1, ?_, ?_⟩
  · intro x hx y hy k hk hkeq
    have hxab : x ∈ Icc a b := hcl_sub hx
    have hyab : y ∈ Icc a b := hcl_sub hy
    have hdiam : |y - x| ≤ b - a := by
      rw [abs_sub_le_iff]
      exact ⟨by linarith [hxab.1, hyab.2], by linarith [hxab.2, hyab.1]⟩
    have hbig : 2 * Real.pi ≤ |y - x| := by
      rw [hkeq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hk
      have h2 : 2 * Real.pi * 1 ≤ 2 * Real.pi * |(k : ℝ)| :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith
    linarith
  · -- the wall/face decoration count
    set D : Set ℝ := {t : ℝ | t ∈ Icc a b ∧ boxA K s c σ t < 0} with hDdef
    have hboxA_zero : ∀ t ∈ Icc a b, boxA K s c σ t = 0 → t = a ∨ t = b := by
      intro t ht ht0
      rcases lt_or_eq_of_le ht.1 with h1 | h1
      · rcases lt_or_eq_of_le ht.2 with h2 | h2
        · exfalso
          have htC : t ∈ C := by rw [hCeq]; exact ⟨h1, h2⟩
          have := (hCY htC).1
          rw [ht0] at this
          exact lt_irrefl 0 this
        · exact Or.inr h2
      · exact Or.inl h1.symm
    have hDord : D.OrdConnected :=
      ⟨fun x hx y hy z hz => by
        obtain ⟨hxI, hxbox⟩ := hx
        obtain ⟨hyI, hybox⟩ := hy
        obtain ⟨hxz, hzy⟩ := hz
        have hzI : z ∈ Icc a b := ⟨le_trans hxI.1 hxz, le_trans hzy hyI.2⟩
        refine ⟨hzI, ?_⟩
        by_contra hzge
        have hz0 : boxA K s c σ z = 0 := le_antisymm (hboxA_le z hzI) (not_lt.mp hzge)
        rcases hboxA_zero z hzI hz0 with hza | hzb
        · have hxa : x = a := le_antisymm (hza ▸ hxz) hxI.1
          have ha0 : boxA K s c σ a = 0 := by rw [← hza]; exact hz0
          rw [hxa, ha0] at hxbox
          exact lt_irrefl 0 hxbox
        · have hyb : y = b := le_antisymm hyI.2 (hzb ▸ hzy)
          have hb0 : boxA K s c σ b = 0 := by rw [← hzb]; exact hz0
          rw [hyb, hb0] at hybox
          exact lt_irrefl 0 hybox⟩
    have hDconv : Convex ℝ D := hDord.convex
    have hwall_deriv : ∀ t ∈ D, deriv (wallW K ℓ) t ≠ 0 := fun t ht =>
      hwall t ((boxA_lt_zero_iff t).mp ht.2) (hcut_le t ht.1)
    have hcontW : Continuous (deriv (wallW K ℓ)) := by
      have hcd : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (wallW K ℓ) :=
        (ContinuousLinearMap.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) ℓ).comp K.smooth
      exact hcd.continuous_deriv (by simp)
    have hsignD : (∀ t ∈ D, 0 < deriv (wallW K ℓ) t) ∨
        (∀ t ∈ D, deriv (wallW K ℓ) t < 0) := by
      by_contra hcon
      rw [not_or] at hcon
      push Not at hcon
      obtain ⟨⟨x, hxD, hx0⟩, ⟨y, hyD, hy0⟩⟩ := hcon
      have hxlt : deriv (wallW K ℓ) x < 0 := lt_of_le_of_ne hx0 (hwall_deriv x hxD)
      have hylt : 0 < deriv (wallW K ℓ) y := lt_of_le_of_ne hy0 (Ne.symm (hwall_deriv y hyD))
      rcases le_total x y with hxy | hyx
      · have hmem : (0 : ℝ) ∈ Icc (deriv (wallW K ℓ) x) (deriv (wallW K ℓ) y) :=
          ⟨hxlt.le, hylt.le⟩
        obtain ⟨w, hw, hw0⟩ := intermediate_value_Icc hxy hcontW.continuousOn hmem
        exact hwall_deriv w (hDord.out hxD hyD hw) hw0
      · have hmem : (0 : ℝ) ∈ Icc (deriv (wallW K ℓ) x) (deriv (wallW K ℓ) y) :=
          ⟨hxlt.le, hylt.le⟩
        obtain ⟨w, hw, hw0⟩ := intermediate_value_Icc' hyx hcontW.continuousOn hmem
        exact hwall_deriv w (hDord.out hyD hxD hw) hw0
    have hWmono : StrictMonoOn (wallW K ℓ) D ∨ StrictAntiOn (wallW K ℓ) D := by
      rcases hsignD with hp | hn
      · left
        refine strictMonoOn_of_deriv_pos hDconv continuous_wallW.continuousOn ?_
        intro x hx
        exact hp x (interior_subset hx)
      · right
        refine strictAntiOn_of_deriv_neg hDconv continuous_wallW.continuousOn ?_
        intro x hx
        exact hn x (interior_subset hx)
    have hF_sub : facePts K s c σ u v h ℓ lam ∩ closure C ⊆ ({a, b} : Set ℝ) := by
      rintro t ⟨htF, htcl⟩
      have hcut_eq : |cutG K c u v t| = h := htF.2.1
      obtain ⟨hat, htb⟩ := hcl_sub htcl
      rcases lt_or_eq_of_le hat with h1 | h1
      · rcases lt_or_eq_of_le htb with h2 | h2
        · exfalso
          have htC : t ∈ C := by rw [hCeq]; exact ⟨h1, h2⟩
          have := hcut_lt t htC
          rw [hcut_eq] at this
          exact lt_irrefl h this
        · exact Or.inr h2
      · exact Or.inl h1.symm
    have hW_sub_D : wallPts K s c σ u v h ℓ lam ∩ closure C ⊆ D := by
      rintro t ⟨htW, htcl⟩
      exact ⟨hcl_sub htcl, htW.1⟩
    have hW_le_one : (wallPts K s c σ u v h ℓ lam ∩ closure C).encard ≤ 1 := by
      rw [encard_le_one_iff]
      intro x y hx hy
      have hxD : x ∈ D := hW_sub_D hx
      have hyD : y ∈ D := hW_sub_D hy
      have hxlam : wallW K ℓ x = lam := hx.1.2.2
      have hylam : wallW K ℓ y = lam := hy.1.2.2
      have hxy_eq : wallW K ℓ x = wallW K ℓ y := by rw [hxlam, hylam]
      rcases hWmono with hm | hm
      · exact hm.injOn hxD hyD hxy_eq
      · exact hm.injOn hxD hyD hxy_eq
    by_cases hWne : (wallPts K s c σ u v h ℓ lam ∩ closure C).Nonempty
    · obtain ⟨p, hpW⟩ := hWne
      have hpD : p ∈ D := hW_sub_D hpW
      have hplam : wallW K ℓ p = lam := hpW.1.2.2
      have hF_le_one : (facePts K s c σ u v h ℓ lam ∩ closure C).encard ≤ 1 := by
        rw [encard_le_one_iff]
        intro x y hx hy
        by_contra hne
        have hxa := hF_sub hx
        have hya := hF_sub hy
        have haF : a ∈ facePts K s c σ u v h ℓ lam ∩ closure C := by
          rcases hxa with h1 | h1
          · rw [← h1]; exact hx
          · rcases hya with h2 | h2
            · rw [← h2]; exact hy
            · exact absurd (h1.trans h2.symm) hne
        have hbF : b ∈ facePts K s c σ u v h ℓ lam ∩ closure C := by
          rcases hya with h2 | h2
          · rcases hxa with h1 | h1
            · exact absurd (h1.trans h2.symm) hne
            · rw [← h1]; exact hx
          · rw [← h2]; exact hy
        have haD : a ∈ D := ⟨⟨le_rfl, hab.le⟩, haF.1.1⟩
        have hbD : b ∈ D := ⟨⟨hab.le, le_rfl⟩, hbF.1.1⟩
        have hwallA : wallW K ℓ a < lam := haF.1.2.2
        have hwallB : wallW K ℓ b < lam := hbF.1.2.2
        rcases hWmono with hm | hm
        · have hp_le_b : p ≤ b := hpD.1.2
          have := hm.monotoneOn hpD hbD hp_le_b
          rw [hplam] at this
          linarith
        · have ha_le_p : a ≤ p := hpD.1.1
          have := hm.antitoneOn haD hpD ha_le_p
          rw [hplam] at this
          linarith
      have hsub : (facePts K s c σ u v h ℓ lam ∪ wallPts K s c σ u v h ℓ lam) ∩ closure C ⊆
          (facePts K s c σ u v h ℓ lam ∩ closure C) ∪
            (wallPts K s c σ u v h ℓ lam ∩ closure C) := by
        rintro t ⟨htU, htcl⟩
        rcases htU with h | h
        · exact Or.inl ⟨h, htcl⟩
        · exact Or.inr ⟨h, htcl⟩
      calc ((facePts K s c σ u v h ℓ lam ∪ wallPts K s c σ u v h ℓ lam) ∩ closure C).encard
          ≤ ((facePts K s c σ u v h ℓ lam ∩ closure C) ∪
              (wallPts K s c σ u v h ℓ lam ∩ closure C)).encard := encard_mono hsub
        _ ≤ (facePts K s c σ u v h ℓ lam ∩ closure C).encard +
              (wallPts K s c σ u v h ℓ lam ∩ closure C).encard := encard_union_le _ _
        _ ≤ 1 + 1 := add_le_add hF_le_one hW_le_one
        _ = 2 := by norm_num
    · rw [not_nonempty_iff_eq_empty] at hWne
      have hsub2 : (facePts K s c σ u v h ℓ lam ∪ wallPts K s c σ u v h ℓ lam) ∩ closure C ⊆
          ({a, b} : Set ℝ) := by
        rintro t ⟨htU, htcl⟩
        rcases htU with hP | hP
        · exact hF_sub ⟨hP, htcl⟩
        · have hmem : t ∈ wallPts K s c σ u v h ℓ lam ∩ closure C := ⟨hP, htcl⟩
          exact absurd hmem (by rw [hWne]; simp)
      calc ((facePts K s c σ u v h ℓ lam ∪ wallPts K s c σ u v h ℓ lam) ∩ closure C).encard
          ≤ ({a, b} : Set ℝ).encard := encard_mono hsub2
        _ = 2 := encard_pair hab.ne

end Work.Drive.Mono
