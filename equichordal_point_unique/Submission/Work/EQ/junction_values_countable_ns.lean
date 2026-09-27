import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.fan_estimates
import Submission.Work.EQ.fan_snd_deriv_ne_zero
import Submission.Work.EQ.exists_accPt_of_subset_isOpen
import Submission.Work.EQ.countable_zeroSet_sdiff_interior
import Submission.Work.EQ.eq_of_fan_comp_eq

/-! Namespace copy of `Submission/Work/EQ/junction_values_countable.lean`.

All declarations are moved into `Work.EQ.JVC` in order to avoid the global clash on
`Work.EQ.analyticAt_eqMirror`, which is declared both here and in
`Submission/Work/EQ/H0_section_local.lean` (the two modules cannot be imported into one
environment).  The mathematics is verbatim.

Original guidance from the project lead (the requester):

ROUTE: read Submission/Work/EQ/DESIGN_HANA.md. Siblings run in parallel.

# junction_values_countable: only countably many junction values

The labelled backward map `L_s w = bwdP a s (fan ε w)` is *countably piecewise analytic*.  A
countable family of pairs `(V, g)` (`V ⊆ Ω` open, `g` analytic on `V`) and a countable exceptional
set `E` are built by induction on the sign list `s`: applying one more branch `invBranch a t`
splits each piece `(V, g)` with radicand `r w = bsq (subO1 a (g w))` into

* (A) `{r ∈ slitPlane}` with `g_A = invBranch a t ∘ g`;
* (S) `{r ∉ [0,∞)}` with `g_S = -g + ε • ((I * (-r)^(1/2))⁻¹ • subO1 a g)` — this is the
  branch cut `r < 0` case, handled by `cpow_half_of_ne_of_not_slitPlane`;
* (Z) `interior {r = 0}` with `g_Z = -g`.

Isolated zeros of `r` go into `E`.  For every `w ∈ Ω ∖ E` some piece `(V,g)` satisfies
`w ∈ V` and `L_s w = g w`.  Then the argument finishes as in the design:  for a value `c` whose
junction set is uncountable, some piece `(V,g)` has `W_c ∩ {L_s = g} ∩ V` uncountable; an
accumulation point of that set inside the open `V ∩ Ω_c` gives, by the identity theorem,
`U_c = g` on a ball, and `c ↦ (g, ball)` is injective by `eq_of_fan_comp_eq`.
-/

namespace Work.EQ.JVC

open Filter _root_.Topology Complex Metric

open scoped Topology

noncomputable section

/-! ## The countable pieces -/

/-- The closed nonnegative real ray in `ℂ`. -/
def rayNN : Set ℂ := {z : ℂ | z.im = 0 ∧ 0 ≤ z.re}

lemma not_mem_slitPlane_iff {z : ℂ} : z ∉ Complex.slitPlane ↔ z.re ≤ 0 ∧ z.im = 0 := by
  simp [Complex.slitPlane, not_or, not_lt]

lemma not_mem_rayNN_iff {z : ℂ} : z ∉ rayNN ↔ z.im ≠ 0 ∨ z.re < 0 := by
  simp only [rayNN, Set.mem_setOf_eq, not_and, not_le]
  tauto

/-- On the branch cut: the principal square root of a nonzero point outside the slit plane is
`I` times the principal square root of its negative. -/
lemma cpow_half_neg_real {z : ℂ} (hz : z ≠ 0) (h : z ∉ Complex.slitPlane) :
    z ^ (1/2 : ℂ) = Complex.I * ((-z) ^ (1/2 : ℂ)) := by
  obtain ⟨hre, him⟩ : z.re ≤ 0 ∧ z.im = 0 := by
    simpa [Complex.slitPlane, not_or, not_lt] using h
  have hren : z.re < 0 := by
    rcases lt_or_eq_of_le hre with h' | h'
    · exact h'
    · exact absurd (by apply Complex.ext <;> simp [him, h']) hz
  set x : ℝ := -z.re with hxdef
  have hxpos : 0 < x := by rw [hxdef]; linarith
  have hz_eq : z = ((-1 : ℂ) * ((x : ℝ) : ℂ)) := by
    rw [hxdef]; apply Complex.ext <;> simp [him] <;> ring
  have hz_ne : ((-1 : ℂ) * ((x : ℝ) : ℂ)) ≠ 0 := by
    simp [Complex.ofReal_ne_zero.mpr hxpos.ne']
  rw [hz_eq, Complex.cpow_def_of_ne_zero hz_ne]
  have hlog : Complex.log ((-1 : ℂ) * ((x : ℝ) : ℂ))
      = ↑(Real.log x) + ↑Real.pi * Complex.I := by
    rw [Complex.log_mul_ofReal x hxpos (-1) (by norm_num), Complex.log_neg_one]
  rw [hlog]
  have hneg : (-((-1 : ℂ) * ((x : ℝ) : ℂ))) = ((x:ℝ):ℂ) := by push_cast; ring
  rw [hneg, ofReal_cpow_half hxpos.le,
    show (↑(Real.log x) + ↑Real.pi * Complex.I) * (1/2 : ℂ)
      = ↑(Real.log x * (1/2)) + ↑Real.pi * (1/2) * Complex.I by push_cast; ring,
    Complex.exp_add]
  have hexp2 : Complex.exp (↑Real.pi * (1/2) * Complex.I) = Complex.I := by
    rw [show (↑Real.pi * (1/2) : ℂ) * Complex.I = (↑(Real.pi * (1/2)) : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [show Real.pi * (1/2) = Real.pi/2 by ring, Real.cos_pi_div_two, Real.sin_pi_div_two]
    norm_num
  rw [hexp2, ← Complex.ofReal_exp, ← Real.rpow_def_of_pos hxpos, ← Real.sqrt_eq_rpow]
  ring

/-- The radicand of the backward branch applied to the point `g w`. -/
def radG (a : ℝ) (g : ℂ → ℂ × ℂ) (w : ℂ) : ℂ := bsq (subO1 a (g w))

lemma invBranch_eq (a : ℝ) (t : Bool) (Q : ℂ × ℂ) :
    invBranch a t Q = -Q + (if t then (1:ℂ) else -1) •
        (((bsq (subO1 a Q)) ^ (1/2 : ℂ))⁻¹ • (subO1 a Q)) := by
  unfold invBranch subO1 bsq
  ext <;>
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg,
      smul_eq_mul, div_eq_mul_inv] <;>
    ring

lemma invBranch_eq_neg_of_rad_zero (a : ℝ) (t : Bool) (Q : ℂ × ℂ)
    (h : bsq (subO1 a Q) = 0) : invBranch a t Q = -Q := by
  have h0 : ((0:ℂ) ^ (1/2:ℂ)) = 0 := by
    rw [Complex.cpow_def]; norm_num
  rw [invBranch_eq, h, h0, inv_zero, zero_smul, smul_zero, add_zero]

/-- The three pieces generated from one piece by one more backward branch with sign `t`. -/
def stepSet (a : ℝ) (t : Bool) (p : Set ℂ × (ℂ → ℂ × ℂ)) :
    Set (Set ℂ × (ℂ → ℂ × ℂ)) :=
  { ( {w ∈ p.1 | radG a p.2 w ∈ Complex.slitPlane}, fun w => invBranch a t (p.2 w) ),
    ( {w ∈ p.1 | radG a p.2 w ∉ rayNN},
      fun w => -p.2 w + (if t then (1:ℂ) else -1) •
        (((Complex.I * ((-(radG a p.2 w)) ^ (1/2 : ℂ)))⁻¹) • (subO1 a (p.2 w))) ),
    ( interior {w ∈ p.1 | radG a p.2 w = 0}, fun w => -p.2 w ) }

/-- The isolated zeros of the radicand of a piece: the points where the radicand vanishes but not
identically on a neighbourhood. -/
def badZero (a : ℝ) (p : Set ℂ × (ℂ → ℂ × ℂ)) : Set ℂ :=
  {w ∈ p.1 | radG a p.2 w = 0} \ interior {w ∈ p.1 | radG a p.2 w = 0}

/-- A countable family of open pieces with analytic maps, covering `Ω` up to a countable set,
and reproducing `L` on each piece. -/
def IsPieceFam (L : ℂ → ℂ × ℂ) (Ω : Set ℂ)
    (S : Set (Set ℂ × (ℂ → ℂ × ℂ))) (E : Set ℂ) : Prop :=
  S.Countable ∧ E.Countable ∧
    (∀ p ∈ S, IsOpen p.1 ∧ p.1 ⊆ Ω ∧ AnalyticOnNhd ℂ p.2 p.1) ∧
    (∀ w ∈ Ω, w ∉ E → ∃ p ∈ S, w ∈ p.1 ∧ L w = p.2 w)

/-! ## Elementary facts about the pieces -/

lemma isClosed_rayNN : IsClosed rayNN := by
  have h1 : IsClosed {z : ℂ | z.im = 0} := isClosed_eq Complex.continuous_im continuous_const
  have h2 : IsClosed {z : ℂ | (0:ℝ) ≤ z.re} := isClosed_le continuous_const Complex.continuous_re
  have hEq : rayNN = {z : ℂ | z.im = 0} ∩ {z : ℂ | (0:ℝ) ≤ z.re} := by
    ext z; simp [rayNN]
  rw [hEq]; exact h1.inter h2

/-- The preimage of an open set under a map analytic on an open set is open. -/
lemma isOpen_of_analyticOnNhd_preimage {U : Set ℂ} {r : ℂ → ℂ} (hU : IsOpen U)
    (hr : AnalyticOnNhd ℂ r U) {W : Set ℂ} (hW : IsOpen W) :
    IsOpen {w ∈ U | r w ∈ W} := by
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨hwU, hwW⟩
  have hcont : ContinuousAt r w := (hr w hwU).continuousAt
  have hpre : r ⁻¹' W ∈ 𝓝 w := hcont.preimage_mem_nhds (hW.mem_nhds hwW)
  refine mem_of_superset (inter_mem hpre (hU.mem_nhds hwU)) ?_
  rintro x ⟨hrx, hxU⟩
  exact ⟨hxU, hrx⟩

lemma analyticAt_radG {a : ℝ} {p : Set ℂ × (ℂ → ℂ × ℂ)} {w : ℂ} (hw : AnalyticAt ℂ p.2 w) :
    AnalyticAt ℂ (fun w => radG a p.2 w) w := by
  unfold radG bsq subO1
  have h1 : AnalyticAt ℂ (fun w => (p.2 w).1) w := (analyticAt_fst (p := p.2 w)).comp hw
  have h2 : AnalyticAt ℂ (fun w => (p.2 w).2) w := (analyticAt_snd (p := p.2 w)).comp hw
  exact (((h1.add (analyticAt_const (v := ((a/2:ℝ):ℂ)))).pow 2).add (h2.pow 2))

lemma analyticOnNhd_radG {a : ℝ} {p : Set ℂ × (ℂ → ℂ × ℂ)}
    (hg : AnalyticOnNhd ℂ p.2 p.1) :
    AnalyticOnNhd ℂ (fun w => radG a p.2 w) p.1 :=
  fun w hw => analyticAt_radG (hg w hw)

/-- `-(radG)` lies in the slit plane exactly for radicands outside the nonnegative ray. -/
lemma neg_radG_mem_slitPlane {a : ℝ} {p : Set ℂ × (ℂ → ℂ × ℂ)} {w : ℂ}
    (hw : radG a p.2 w ∉ rayNN) : (-(radG a p.2 w)) ∈ Complex.slitPlane := by
  rw [not_mem_rayNN_iff] at hw
  simp only [Complex.mem_slitPlane_iff, Complex.neg_re, Complex.neg_im]
  rcases hw with h | h
  · exact Or.inr (by simpa using h)
  · exact Or.inl (by linarith)

lemma pieceS_den_ne_zero {a : ℝ} {p : Set ℂ × (ℂ → ℂ × ℂ)} {w : ℂ}
    (hw : radG a p.2 w ∉ rayNN) :
    Complex.I * ((-(radG a p.2 w)) ^ (1/2 : ℂ)) ≠ 0 := by
  have hmem := neg_radG_mem_slitPlane hw
  have hne : (-(radG a p.2 w)) ≠ 0 := Complex.slitPlane_ne_zero hmem
  have hroot : (-(radG a p.2 w)) ^ (1/2 : ℂ) ≠ 0 := by
    intro h0
    have := cpow_half_sq (-(radG a p.2 w))
    rw [h0] at this
    exact hne (by simpa using this.symm)
  exact mul_ne_zero Complex.I_ne_zero hroot

/-- Analyticity of the `(S)` piece function. -/
lemma analyticAt_pieceS {a : ℝ} {t : Bool} {p : Set ℂ × (ℂ → ℂ × ℂ)} {w : ℂ}
    (hw : w ∈ p.1) (hray : radG a p.2 w ∉ rayNN) (hg : AnalyticOnNhd ℂ p.2 p.1) :
    AnalyticAt ℂ (fun w => -p.2 w + (if t then (1:ℂ) else -1) •
        (((Complex.I * ((-(radG a p.2 w)) ^ (1/2 : ℂ)))⁻¹) • (subO1 a (p.2 w)))) w := by
  have hra : AnalyticAt ℂ (fun w => radG a p.2 w) w := analyticAt_radG (hg w hw)
  have hroot : AnalyticAt ℂ (fun w => (-(radG a p.2 w)) ^ (1/2 : ℂ)) w :=
    (hra.neg).cpow analyticAt_const (neg_radG_mem_slitPlane hray)
  have hden : AnalyticAt ℂ (fun w => Complex.I * ((-(radG a p.2 w)) ^ (1/2 : ℂ))) w :=
    analyticAt_const.mul hroot
  have hD : AnalyticAt ℂ
      (fun w => (Complex.I * ((-(radG a p.2 w)) ^ (1/2 : ℂ)))⁻¹) w :=
    hden.inv (pieceS_den_ne_zero hray)
  have hsub : AnalyticAt ℂ (fun w => subO1 a (p.2 w)) w := by
    have h1 : AnalyticAt ℂ (fun w => (p.2 w).1) w := (analyticAt_fst (p := p.2 w)).comp (hg w hw)
    have h2 : AnalyticAt ℂ (fun w => (p.2 w).2) w := (analyticAt_snd (p := p.2 w)).comp (hg w hw)
    exact (h1.add (analyticAt_const (v := ((a/2:ℝ):ℂ)))).prod h2
  exact (hg w hw).neg.add
    ((analyticAt_const (v := (if t then (1:ℂ) else -1))).smul (hD.smul hsub))

/-- The matching identity for the `(S)` piece: at a radicand on the branch cut. -/
lemma pieceS_apply_eq {a : ℝ} {t : Bool} {p : Set ℂ × (ℂ → ℂ × ℂ)} {w : ℂ}
    (hslit : radG a p.2 w ∉ Complex.slitPlane) (hne : radG a p.2 w ≠ 0) :
    invBranch a t (p.2 w) = -p.2 w + (if t then (1:ℂ) else -1) •
        (((Complex.I * ((-(radG a p.2 w)) ^ (1/2 : ℂ)))⁻¹) • (subO1 a (p.2 w))) := by
  simp only [radG] at hne hslit ⊢
  rw [invBranch_eq, cpow_half_neg_real hne hslit]

/-! ## Openness and analyticity of the three pieces -/

lemma isOpen_pieceA {a : ℝ} {p : Set ℂ × (ℂ → ℂ × ℂ)} (hV : IsOpen p.1)
    (hg : AnalyticOnNhd ℂ p.2 p.1) :
    IsOpen {w ∈ p.1 | radG a p.2 w ∈ Complex.slitPlane} :=
  isOpen_of_analyticOnNhd_preimage hV (analyticOnNhd_radG hg) Complex.isOpen_slitPlane

lemma isOpen_pieceS {a : ℝ} {p : Set ℂ × (ℂ → ℂ × ℂ)} (hV : IsOpen p.1)
    (hg : AnalyticOnNhd ℂ p.2 p.1) :
    IsOpen {w ∈ p.1 | radG a p.2 w ∉ rayNN} :=
  isOpen_of_analyticOnNhd_preimage hV (analyticOnNhd_radG hg) isClosed_rayNN.isOpen_compl

lemma analyticOnNhd_pieceA {a : ℝ} {t : Bool} {p : Set ℂ × (ℂ → ℂ × ℂ)}
    (hg : AnalyticOnNhd ℂ p.2 p.1) :
    AnalyticOnNhd ℂ (fun w => invBranch a t (p.2 w))
      {w ∈ p.1 | radG a p.2 w ∈ Complex.slitPlane} := by
  intro w hw
  exact (analyticAt_invBranch (a := a) (s := t) (Q := p.2 w)
    (by simpa [radG, bsq, subO1] using hw.2)).comp (hg w hw.1)

lemma analyticOnNhd_pieceS {a : ℝ} {t : Bool} {p : Set ℂ × (ℂ → ℂ × ℂ)}
    (hg : AnalyticOnNhd ℂ p.2 p.1) :
    AnalyticOnNhd ℂ (fun w => -p.2 w + (if t then (1:ℂ) else -1) •
        (((Complex.I * ((-(radG a p.2 w)) ^ (1/2 : ℂ)))⁻¹) • (subO1 a (p.2 w))))
      {w ∈ p.1 | radG a p.2 w ∉ rayNN} := by
  intro w hw
  exact analyticAt_pieceS hw.1 hw.2 hg

lemma analyticOnNhd_pieceZ {a : ℝ} {p : Set ℂ × (ℂ → ℂ × ℂ)}
    (hg : AnalyticOnNhd ℂ p.2 p.1) :
    AnalyticOnNhd ℂ (fun w => -p.2 w) (interior {w ∈ p.1 | radG a p.2 w = 0}) := by
  intro w hw
  exact (hg w (interior_subset hw).1).neg

lemma countable_stepSet (a : ℝ) (t : Bool) (p : Set ℂ × (ℂ → ℂ × ℂ)) :
    (stepSet a t p).Countable := by
  rw [stepSet]
  exact (Set.Finite.insert _ (Set.Finite.insert _ (Set.finite_singleton _))).countable

/-- A countable family of pieces of `L` on `Ω`. -/
theorem pieces_exists {a : ℝ} {h : ℂ → ℂ} {ε : List Bool} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (han : AnalyticOnNhd ℂ (fan a h ε) Ω) :
    ∀ s : List Bool, ∃ S E, IsPieceFam (fun w => bwdP a s (fan a h ε w)) Ω S E := by
  intro s
  induction s using List.reverseRecOn with
  | nil =>
      refine ⟨{(Ω, fan a h ε)}, ∅, Set.countable_singleton _, Set.countable_empty, ?_, ?_⟩
      · rintro p hp
        rw [Set.mem_singleton_iff] at hp
        subst hp
        exact ⟨hΩ, subset_refl _, han⟩
      · intro w hw _
        exact ⟨(Ω, fan a h ε), Set.mem_singleton _, hw, rfl⟩
  | append_singleton s' t ih =>
      obtain ⟨S, E, hSc, hEc, hSprop, hScov⟩ := ih
      refine ⟨⋃ p ∈ S, stepSet a t p, E ∪ ⋃ p ∈ S, badZero a p, ?_, ?_, ?_, ?_⟩
      · exact Set.Countable.biUnion hSc (fun p _ => countable_stepSet a t p)
      · refine hEc.union (Set.Countable.biUnion hSc (fun p hp => ?_))
        obtain ⟨hpopen, hpΩ, hpan⟩ := hSprop p hp
        have hrad : AnalyticOnNhd ℂ (fun w => radG a p.2 w) p.1 :=
          fun w hw => analyticAt_radG (hpan w hw)
        exact countable_zeroSet_sdiff_interior hpopen hrad
      · rintro p' hp'
        simp only [Set.mem_iUnion] at hp'
        obtain ⟨p, hpS, hp'⟩ := hp'
        rw [stepSet] at hp'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp'
        obtain ⟨hpopen, hpΩ, hpan⟩ := hSprop p hpS
        rcases hp' with h | h | h
        · subst h
          exact ⟨isOpen_pieceA hpopen hpan, fun x hx => hpΩ hx.1, analyticOnNhd_pieceA hpan⟩
        · subst h
          exact ⟨isOpen_pieceS hpopen hpan, fun x hx => hpΩ hx.1, analyticOnNhd_pieceS hpan⟩
        · subst h
          exact ⟨isOpen_interior, fun x hx => hpΩ (interior_subset hx).1, analyticOnNhd_pieceZ hpan⟩
      · intro w hwΩ hwE
        have hwE' : w ∉ E := fun h => hwE (Or.inl h)
        obtain ⟨p, hpS, hwp, hLp⟩ := hScov w hwΩ hwE'
        obtain ⟨hpopen, hpΩ, hpan⟩ := hSprop p hpS
        have hLp' : bwdP a s' (fan a h ε w) = p.2 w := hLp
        have hL'w : bwdP a (s' ++ [t]) (fan a h ε w) = invBranch a t (p.2 w) := by
          rw [bwdP_snoc, hLp']
        have hmemA : ( {w ∈ p.1 | radG a p.2 w ∈ Complex.slitPlane},
            fun w => invBranch a t (p.2 w) ) ∈ stepSet a t p := by
          rw [stepSet]; exact Set.mem_insert _ _
        have hmemZ : ( interior {w ∈ p.1 | radG a p.2 w = 0}, fun w => -p.2 w )
            ∈ stepSet a t p := by
          rw [stepSet]
          exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
        have hmemS : ( {w ∈ p.1 | radG a p.2 w ∉ rayNN},
            fun w => -p.2 w + (if t then (1:ℂ) else -1) •
              (((Complex.I * ((-(radG a p.2 w)) ^ (1/2 : ℂ)))⁻¹) • (subO1 a (p.2 w))) )
            ∈ stepSet a t p := by
          rw [stepSet]
          exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
        rcases em (radG a p.2 w ∈ Complex.slitPlane) with hslit | hnslit
        · refine ⟨_, Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hpS, hmemA⟩⟩,
            ⟨hwp, hslit⟩, ?_⟩
          show bwdP a (s' ++ [t]) (fan a h ε w) = invBranch a t (p.2 w)
          exact hL'w
        · rcases eq_or_ne (radG a p.2 w) 0 with hz | hne
          · have hmem : w ∈ interior {w ∈ p.1 | radG a p.2 w = 0} := by
              by_contra hcon
              refine hwE (Or.inr (Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hpS, ?_⟩⟩))
              rw [badZero]; exact ⟨⟨hwp, hz⟩, hcon⟩
            refine ⟨_, Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hpS, hmemZ⟩⟩, hmem, ?_⟩
            show bwdP a (s' ++ [t]) (fan a h ε w) = -p.2 w
            rw [hL'w, invBranch_eq_neg_of_rad_zero a t (p.2 w)
              (by simpa [radG, bsq, subO1] using hz)]
          · have hnotray : radG a p.2 w ∉ rayNN := by
              rw [not_mem_slitPlane_iff] at hnslit
              rw [not_mem_rayNN_iff]
              refine Or.inr (lt_of_le_of_ne hnslit.1 (fun hc => hne ?_))
              exact Complex.ext (by simpa using hc) (by simpa using hnslit.2)
            refine ⟨_, Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hpS, hmemS⟩⟩,
              ⟨hwp, hnotray⟩, ?_⟩
            show bwdP a (s' ++ [t]) (fan a h ε w) = -p.2 w + (if t then (1:ℂ) else -1) •
              (((Complex.I * ((-(radG a p.2 w)) ^ (1/2 : ℂ)))⁻¹) • (subO1 a (p.2 w)))
            rw [hL'w, pieceS_apply_eq (a := a) (t := t) (p := p) (w := w) hnslit hne]

/-! ## Auxiliaries for the final count -/

lemma analyticAt_eqMirror (P : ℂ × ℂ) : AnalyticAt ℂ eqMirror P := by
  unfold eqMirror
  exact (analyticAt_fst (p := P)).neg.prod (analyticAt_snd (p := P))

lemma eqMirror_inj : Function.Injective eqMirror := by
  intro P Q h
  have h1 : P.1 = Q.1 := by
    have hh := congrArg Prod.fst h
    simp only [eqMirror] at hh
    exact neg_inj.mp hh
  have h2 : P.2 = Q.2 := by
    have hh := congrArg Prod.snd h
    simpa [eqMirror] using hh
  exact Prod.ext h1 h2

/-- The set on which the unstable-fan side of a junction equation is defined. -/
def omegaC (a : ℝ) (N : ℕ) (δf : ℝ) (c : ℂ) : Set ℂ :=
  {w : ℂ | w ≠ 0 ∧ ‖w‖ < δf ∧ ‖((eqLam a : ℝ) : ℂ) ^ N * (c / w)‖ < δf}

lemma isOpen_omegaC {a : ℝ} {N : ℕ} {δf : ℝ} (c : ℂ) : IsOpen (omegaC a N δf c) := by
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨hw0, hwf, hw2⟩
  have hcont : ContinuousAt (fun w : ℂ => ((eqLam a : ℝ) : ℂ) ^ N * (c / w)) w :=
    ContinuousAt.const_mul (ContinuousAt.div continuousAt_const continuousAt_id hw0) _
  have hne : ({0}ᶜ : Set ℂ) ∈ 𝓝 w :=
    isOpen_compl_singleton.mem_nhds (by simpa using hw0)
  have hb : Metric.ball (0 : ℂ) δf ∈ 𝓝 w :=
    (Metric.isOpen_ball (x := (0:ℂ)) (ε := δf)).mem_nhds (by
      rw [Metric.mem_ball, dist_zero_right]; exact hwf)
  have hS : {w' : ℂ | ‖((eqLam a : ℝ) : ℂ) ^ N * (c / w')‖ < δf} ∈ 𝓝 w := by
    have hbb : Metric.ball (0 : ℂ) δf ∈ 𝓝 (((eqLam a : ℝ) : ℂ) ^ N * (c / w)) :=
      (Metric.isOpen_ball (x := (0:ℂ)) (ε := δf)).mem_nhds (by
        rw [Metric.mem_ball, dist_zero_right]; exact hw2)
    have hpre := ContinuousAt.preimage_mem_nhds hcont hbb
    rwa [show {w' : ℂ | ‖((eqLam a : ℝ) : ℂ) ^ N * (c / w')‖ < δf}
        = (fun w => ((eqLam a : ℝ) : ℂ) ^ N * (c / w)) ⁻¹' Metric.ball 0 δf from by
      ext x; simp [Metric.mem_ball, dist_zero_right]]
  have hmem : (({0}ᶜ : Set ℂ) ∩ Metric.ball (0 : ℂ) δf
      ∩ {w' : ℂ | ‖((eqLam a : ℝ) : ℂ) ^ N * (c / w')‖ < δf}) ∈ 𝓝 w :=
    Filter.inter_mem (Filter.inter_mem hne hb) hS
  refine Filter.mem_of_superset hmem ?_
  rintro x ⟨⟨hx0, hxf⟩, hx2⟩
  exact ⟨by simpa using hx0, by rwa [Metric.mem_ball, dist_zero_right] at hxf, hx2⟩

lemma analyticOnNhd_Uc {a : ℝ} {h : ℂ → ℂ} {η : List Bool} {N : ℕ} {δf : ℝ} {c : ℂ}
    (hanη : AnalyticOnNhd ℂ (fan a h η) (Metric.ball 0 δf)) :
    AnalyticOnNhd ℂ (fun w => eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (c / w))))
      (omegaC a N δf c) := by
  intro w hw
  have hmem : ((eqLam a : ℝ) : ℂ) ^ N * (c / w) ∈ Metric.ball 0 δf := by
    rw [Metric.mem_ball, dist_zero_right]; exact hw.2.2
  have hmap : AnalyticAt ℂ (fun w : ℂ => ((eqLam a : ℝ) : ℂ) ^ N * (c / w)) w :=
    analyticAt_const.mul (AnalyticAt.div analyticAt_const analyticAt_id hw.1)
  have h1 : AnalyticAt ℂ (fun w => fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (c / w))) w :=
    AnalyticAt.comp (f := fun w : ℂ => ((eqLam a : ℝ) : ℂ) ^ N * (c / w)) (hanη _ hmem) hmap
  exact AnalyticAt.comp (f := fun w => fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (c / w)))
    (analyticAt_eqMirror _) h1


/-- The set of parameters `w` at which the labelled `N`-step backward image of the stable fan meets
the mirrored unstable fan with parameter `λ^N c / w`, both fan arguments lying in `ball 0 δf`. -/
def juncSet (a : ℝ) (h : ℂ → ℂ) (ε η : List Bool) (N : ℕ) (δf : ℝ) (s : List Bool) (c : ℂ) :
    Set ℂ :=
  {w : ℂ | w ≠ 0 ∧ ‖w‖ < δf ∧ ‖((eqLam a : ℝ) : ℂ) ^ N * (c / w)‖ < δf ∧
    bwdP a s (fan a h ε w) = eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (c / w)))}

/-- **Junction values are countable (replaces branch counting in step 5 of `H0_regular`).**
For fixed depth `N`, stable word `ε`, unstable word `η` and backward sign list `s`, only
countably many values `c` admit an uncountable set of parameters `w` (with both fan arguments
in the analyticity disc) at which the labelled `N`-step backward image of the stable fan meets
the mirrored unstable fan with parameter `λᴺ c / w`. -/
theorem junction_values_countable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ (N : ℕ) (ε η s : List Bool),
      {c : ℂ | ¬ {w : ℂ | w ≠ 0 ∧ ‖w‖ < δ₁ ∧
          ‖((eqLam a : ℝ) : ℂ) ^ N * (c / w)‖ < δ₁ ∧
          bwdP a s (fan a h ε w) =
            eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (c / w)))}.Countable}.Countable := by
  obtain ⟨δf, hδf, hfan⟩ := fan_estimates ha0 ha1 hh
  refine ⟨δf, hδf, ?_⟩
  intro N ε η s
  change {c : ℂ | ¬ (juncSet a h ε η N δf s c).Countable}.Countable
  have hanε : AnalyticOnNhd ℂ (fan a h ε) (Metric.ball 0 δf) := (hfan ε).1
  have hanη : AnalyticOnNhd ℂ (fan a h η) (Metric.ball 0 δf) := (hfan η).1
  have hderiv : deriv (fun u => (fan a h η u).2) 0 ≠ 0 := fan_snd_deriv_ne_zero ha0 ha1 hh η
  have hlam : eqLam a ≠ 0 := ne_of_gt (eqLam_pos' ha0 ha1)
  obtain ⟨S, E, hSc, hEc, hSprop, hScov⟩ :=
    pieces_exists (Ω := Metric.ball 0 δf) Metric.isOpen_ball hanε s
  obtain ⟨D, hDc, hDdense⟩ := TopologicalSpace.exists_countable_dense ℂ
  classical
  set Bad : Set ℂ := {c : ℂ | ¬ (juncSet a h ε η N δf s c).Countable} with hBad
  have hex : ∀ c : ℂ, c ∈ Bad \ {0} → ∃ pd : (Set ℂ × (ℂ → ℂ × ℂ)) × ℂ, pd.1 ∈ S ∧ pd.2 ∈ D ∧
      ∃ B : Set ℂ, IsOpen B ∧ B.Nonempty ∧ B ⊆ pd.1.1 ∧ B ⊆ omegaC a N δf c ∧
        pd.2 ∈ B ∧ Set.EqOn (fun w => eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (c / w))))
          pd.1.2 B := by
    rintro c hc
    have hcBad : ¬ (juncSet a h ε η N δf s c).Countable := hc.1
    have hWE : ¬ ((juncSet a h ε η N δf s c) \ E).Countable := by
      intro h
      refine hcBad (Set.Countable.mono (fun x hx => ?_) (h.union hEc))
      by_cases hxE : x ∈ E
      · exact Or.inr hxE
      · exact Or.inl ⟨hx, hxE⟩
    have hexp : ∃ p ∈ S, ¬ (((juncSet a h ε η N δf s c) \ E) ∩
        {w ∈ p.1 | bwdP a s (fan a h ε w) = p.2 w}).Countable := by
      by_contra h
      push_neg at h
      refine hWE (Set.Countable.mono ?_ (Set.Countable.biUnion hSc (fun p hp => h p hp)))
      rintro w ⟨hwW, hwE⟩
      have hwΩ : w ∈ Metric.ball 0 δf := by
        rw [Metric.mem_ball, dist_zero_right]; exact hwW.2.1
      obtain ⟨p, hpS, hwp, hLp⟩ := hScov w hwΩ hwE
      exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hpS, ⟨⟨hwW, hwE⟩, hwp, hLp⟩⟩⟩
    obtain ⟨p, hpS, hAp⟩ := hexp
    obtain ⟨hpopen, hpΩ, hpan⟩ := hSprop p hpS
    set A : Set ℂ := ((juncSet a h ε η N δf s c) \ E) ∩
        {w ∈ p.1 | bwdP a s (fan a h ε w) = p.2 w} with hA
    have hAunc : ¬ A.Countable := hAp
    have hAsub : A ⊆ p.1 ∩ omegaC a N δf c := by
      rintro w ⟨⟨hwW, -⟩, hwp, -⟩
      exact ⟨hwp, hwW.1, hwW.2.1, hwW.2.2.1⟩
    have hUopen : IsOpen (p.1 ∩ omegaC a N δf c) := hpopen.inter (isOpen_omegaC c)
    obtain ⟨x, hxU, hxacc⟩ := exists_accPt_of_subset_isOpen hUopen hAsub hAunc
    obtain ⟨ε', hε'pos, hball⟩ := Metric.isOpen_iff.mp hUopen x hxU
    obtain ⟨d, hdD, hdball⟩ := hDdense.exists_mem_open Metric.isOpen_ball
      ⟨x, Metric.mem_ball_self hε'pos⟩
    have hEqOn : Set.EqOn (fun w => eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (c / w))))
        p.2 (Metric.ball x ε') := by
      refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq ?_ ?_ Metric.isPreconnected_ball
        (Metric.mem_ball_self hε'pos) ?_
      · exact (analyticOnNhd_Uc (N := N) (c := c) hanη).mono (fun z hz => (hball hz).2)
      · exact hpan.mono (fun z hz => (hball hz).1)
      · have hf := hxacc
        rw [accPt_iff_frequently] at hf
        refine (frequently_inf_principal.mpr hf).mono ?_
        intro z hz
        have hzA : z ∈ ((juncSet a h ε η N δf s c) \ E) ∩
            {w ∈ p.1 | bwdP a s (fan a h ε w) = p.2 w} := by rwa [hA] at hz
        have hEq : bwdP a s (fan a h ε z)
            = eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (c / z))) := hzA.1.1.2.2.2
        exact hEq.symm.trans hzA.2.2
    exact ⟨(p, d), hpS, hdD, Metric.ball x ε', Metric.isOpen_ball,
      ⟨x, Metric.mem_ball_self hε'pos⟩, (fun z hz => (hball hz).1), (fun z hz => (hball hz).2),
      hdball, hEqOn⟩
  let tag : ℂ → ((Set ℂ × (ℂ → ℂ × ℂ)) × ℂ) := fun c =>
    if hc : c ∈ Bad \ {0} then Classical.choose (hex c hc)
    else (((∅ : Set ℂ), fun _ => (0, 0)), 0)
  have htag_mem : ∀ c, c ∈ Bad \ {0} → tag c ∈ S ×ˢ D := by
    intro c hc
    have hspec := Classical.choose_spec (hex c hc)
    simp only [tag, dif_pos hc]
    exact ⟨hspec.1, hspec.2.1⟩
  have htag_eq : ∀ c, c ∈ Bad \ {0} → ∃ B : Set ℂ, IsOpen B ∧ B.Nonempty ∧ B ⊆ (tag c).1.1 ∧
      B ⊆ omegaC a N δf c ∧ (tag c).2 ∈ B ∧
      Set.EqOn (fun w => eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (c / w))))
        (tag c).1.2 B := by
    intro c hc
    have hspec := Classical.choose_spec (hex c hc)
    simp only [tag, dif_pos hc]
    exact hspec.2.2
  have hinj : Set.InjOn tag (Bad \ {0}) := by
    intro c hc c' hc' heq
    obtain ⟨B, hBo, hBne, hBs, hBΩ, hdB, hEb⟩ := htag_eq c hc
    obtain ⟨B', hB'o, hB'ne, hB's, hB'Ω, hdB', hEb'⟩ := htag_eq c' hc'
    have hpc : (tag c).1 = (tag c').1 := by rw [heq]
    have hdc : (tag c).2 = (tag c').2 := by rw [heq]
    have hpfeq : (tag c).1.2 = (tag c').1.2 := by rw [hpc]
    refine eq_of_fan_comp_eq (N := N) (by simpa using hc.2) (by simpa using hc'.2) hlam hδf hanη hderiv
      (hBo.inter hB'o) ⟨(tag c).2, hdB, by rw [hdc]; exact hdB'⟩ ?_ ?_ ?_
    · intro w hw
      have h1 := hBΩ hw.1
      exact ⟨h1.1, h1.2.2⟩
    · intro w hw
      exact (hB'Ω hw.2).2.2
    · intro w hw
      have e1 : eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (c / w))) = (tag c).1.2 w :=
        hEb hw.1
      have e2 : eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (c' / w))) = (tag c').1.2 w :=
        hEb' hw.2
      exact eqMirror_inj (by rw [e1, e2, hpfeq])
  have himg : (tag '' (Bad \ {0})).Countable :=
    Set.Countable.mono (fun y hy => by
      obtain ⟨c, hc, rfl⟩ := hy
      exact htag_mem c hc) (Set.Countable.prod hSc hDc)
  have hbad0 : (Bad \ {0}).Countable := Set.countable_of_injective_of_countable_image hinj himg
  refine Set.Countable.mono (fun c hc => ?_) (hbad0.union (Set.countable_singleton (0:ℂ)))
  by_cases h : c = 0
  · exact Or.inr (by simpa [h])
  · exact Or.inl ⟨hc, by simpa using h⟩

end

end Work.EQ.JVC
