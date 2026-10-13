/-
  WilC4/ClusterSelf/Coord : copy of `WilC4/ClusterCoord` under the namespace `Work.WilC4.CESAux`.

  The sets of `ClusterSelf/Sets` read off the coordinates: the tuple `tupleC4`, the named
  conditions `IsDeepE`/`RatE`, and the coordinate lemmas `Spos_tuple`, `Sdeep_mem`, `Srat_mem`.
  See `WilC4/ClusterER_definable_self.lean` for the rationale.
-/
import Mathlib
import Submission.Work.WilC4.ClusterSelf.Sets

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Work.WilC4.CESAux

set_option autoImplicit false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language

open WilkiesDesign WilkiesDesign.CG
/-! ## 1. The coordinate forms of the three conditions

The set-theoretic definitions above live on the *tuple*; here we read them off the coordinates.
The tuple of a point `(ρ,β,c,x)` is `tupleC4`, and the auxiliary existential quantifiers in
`Sdeep`/`Srat` are turned back into ordinary real quantifiers. -/

/-- A function on `Fin 1` is the constant function of its value at `0`. -/
theorem fin1_funext (f : Fin 1 → ℝ) : f = fun _ : Fin 1 => f 0 := by
  funext i
  exact congrArg f (Subsingleton.elim i 0)

/-- The tuple `(ρ,β,c,x)` in the context `C4`. -/
def tupleC4 (k : ℕ) (ρ β : ℝ) (c : Fin k → ℝ) (x : ℝ) : C4 k → ℝ :=
  Sum.elim (Sum.elim (Sum.elim (fun _ : Fin 1 => ρ) (fun _ : Fin 1 => β)) c)
    (fun _ : Fin 1 => x)

/-! ### Reading the slots -/

theorem tupleC4_r (k : ℕ) (ρ β : ℝ) (c : Fin k → ℝ) (x : ℝ) :
    tupleC4 k ρ β c x (r4 : C4 k) = ρ := by
  simp only [tupleC4, r4, r3, r2, Sum.elim_inl, Sum.elim_inr]

theorem tupleC4_b (k : ℕ) (ρ β : ℝ) (c : Fin k → ℝ) (x : ℝ) :
    tupleC4 k ρ β c x (b4 : C4 k) = β := by
  simp only [tupleC4, b4, b3, b2, Sum.elim_inl, Sum.elim_inr]

theorem tupleC4_x (k : ℕ) (ρ β : ℝ) (c : Fin k → ℝ) (x : ℝ) :
    tupleC4 k ρ β c x (x4 : C4 k) = x := by
  simp only [tupleC4, x4, Sum.elim_inr]

theorem tupleC4_c (k : ℕ) (ρ β : ℝ) (c : Fin k → ℝ) (x : ℝ) (j : Fin k) :
    tupleC4 k ρ β c x (c4 j) = c j := by
  simp only [tupleC4, c4, c3, Sum.elim_inl, Sum.elim_inr]

theorem tupleC4_comp_c (k : ℕ) (ρ β : ℝ) (c : Fin k → ℝ) (x : ℝ) :
    tupleC4 k ρ β c x ∘ (c4 : Fin k → C4 k) = c :=
  funext fun j => tupleC4_c k ρ β c x j

/-! ### The tuples in the extended contexts -/

theorem elim_DB2_b {k : ℕ} (u : C4 k → ℝ) (b d : Fin 1 → ℝ) :
    Sum.elim (Sum.elim u b) d (bD2 : DB2 k) = b 0 := by
  simp only [bD2, bD, Sum.elim_inl, Sum.elim_inr]

theorem elim_DB2_d {k : ℕ} (u : C4 k → ℝ) (b d : Fin 1 → ℝ) :
    Sum.elim (Sum.elim u b) d (dD2 : DB2 k) = d 0 := by
  simp only [dD2, Sum.elim_inr]

theorem elim_DB2_C4 {k : ℕ} (u : C4 k → ℝ) (b d : Fin 1 → ℝ) (s : C4 k) :
    Sum.elim (Sum.elim u b) d (Sum.inl (Sum.inl s)) = u s := by
  simp only [Sum.elim_inl]

theorem elim_DB2_fun {k : ℕ} (u : C4 k → ℝ) (b d : Fin 1 → ℝ) :
    (Sum.elim (Sum.elim u b) d) ∘ (c4D2 : Fin k → DB2 k) = u ∘ c4 := by
  funext j
  simpa only [c4D2, Function.comp_apply] using elim_DB2_C4 u b d (c4 j)

theorem elim_TA_C4 {k : ℕ} (u : C4 k → ℝ) (t : Fin 1 → ℝ) (s : C4 k) :
    Sum.elim u t (Sum.inl s) = u s := by
  simp only [Sum.elim_inl]

theorem elim_TA_t {k : ℕ} (u : C4 k → ℝ) (t : Fin 1 → ℝ) :
    Sum.elim u t (tA : TA k) = t 0 := by
  simp only [tA, Sum.elim_inr]

theorem elim_TA_fun {k : ℕ} (u : C4 k → ℝ) (t : Fin 1 → ℝ) :
    (Sum.elim u t) ∘ (cA : Fin k → TA k) = u ∘ c4 := by
  funext j
  simpa only [cA, Function.comp_apply] using elim_TA_C4 u t (c4 j)

theorem elim_TE_C4 {k : ℕ} (u : C4 k → ℝ) (t e : Fin 1 → ℝ) (s : C4 k) :
    Sum.elim (Sum.elim u t) e (Sum.inl (Sum.inl s)) = u s := by
  simp only [Sum.elim_inl]

theorem elim_TE_t {k : ℕ} (u : C4 k → ℝ) (t e : Fin 1 → ℝ) :
    Sum.elim (Sum.elim u t) e (tE : TE k) = t 0 := by
  simp only [tE, tA, Sum.elim_inl, Sum.elim_inr]

theorem elim_TE_e {k : ℕ} (u : C4 k → ℝ) (t e : Fin 1 → ℝ) :
    Sum.elim (Sum.elim u t) e (eE : TE k) = e 0 := by
  simp only [eE, Sum.elim_inr]

theorem elim_TE_fun {k : ℕ} (u : C4 k → ℝ) (t e : Fin 1 → ℝ) :
    (Sum.elim (Sum.elim u t) e) ∘ (cE : Fin k → TE k) = u ∘ c4 := by
  funext j
  simpa only [cE, cA, Function.comp_apply] using elim_TE_C4 u t e (c4 j)

theorem elim_TB_C4 {k : ℕ} (u : C4 k → ℝ) (t e : Fin 1 → ℝ) (w : Fin 5 → ℝ) (s : C4 k) :
    Sum.elim (Sum.elim (Sum.elim u t) e) w (Sum.inl (Sum.inl (Sum.inl s))) = u s := by
  simp only [Sum.elim_inl]

theorem elim_TB_t {k : ℕ} (u : C4 k → ℝ) (t e : Fin 1 → ℝ) (w : Fin 5 → ℝ) :
    Sum.elim (Sum.elim (Sum.elim u t) e) w (tT : TB k) = t 0 := by
  simp only [tT, Sum.elim_inl, Sum.elim_inr]

theorem elim_TB_e {k : ℕ} (u : C4 k → ℝ) (t e : Fin 1 → ℝ) (w : Fin 5 → ℝ) :
    Sum.elim (Sum.elim (Sum.elim u t) e) w (eT : TB k) = e 0 := by
  simp only [eT, Sum.elim_inl, Sum.elim_inr]

theorem elim_TB_5 {k : ℕ} (u : C4 k → ℝ) (t e : Fin 1 → ℝ) (w : Fin 5 → ℝ) (j : Fin 5) :
    Sum.elim (Sum.elim (Sum.elim u t) e) w (Sum.inr j) = w j := by
  simp only [Sum.elim_inr]

theorem elim_TB_fun {k : ℕ} (u : C4 k → ℝ) (t e : Fin 1 → ℝ) (w : Fin 5 → ℝ) :
    (Sum.elim (Sum.elim (Sum.elim u t) e) w) ∘ (cT : Fin k → TB k) = u ∘ c4 := by
  funext j
  simpa only [cT, Function.comp_apply] using elim_TB_C4 u t e w (c4 j)

/-! ### Quantifier bookkeeping for `Fin 1` and `Fin 5` -/

theorem exists_fin1_iff {P : ℝ → Prop} :
    (∃ f : Fin 1 → ℝ, P (f 0)) ↔ ∃ x : ℝ, P x :=
  ⟨fun ⟨f, hf⟩ => ⟨f 0, hf⟩, fun ⟨x, hx⟩ => ⟨fun _ => x, by simpa using hx⟩⟩

theorem forall_fin1_iff {P : ℝ → Prop} :
    (∀ f : Fin 1 → ℝ, P (f 0)) ↔ ∀ x : ℝ, P x :=
  ⟨fun h x => h (fun _ => x), fun h f => h (f 0)⟩

/-- The tuple `(y,y',τ,ω,ι)` in `Fin 5`. -/
def mk5 (y y' τ ω ι : ℝ) : Fin 5 → ℝ :=
  Fin.cons y (Fin.cons y' (Fin.cons τ (Fin.cons ω (Fin.cons ι
    (fun j : Fin 0 => j.elim0)))))

theorem mk5_zero (y y' τ ω ι : ℝ) : mk5 y y' τ ω ι 0 = y := rfl

theorem mk5_one (y y' τ ω ι : ℝ) : mk5 y y' τ ω ι 1 = y' := rfl

theorem mk5_two (y y' τ ω ι : ℝ) : mk5 y y' τ ω ι 2 = τ := rfl

theorem mk5_three (y y' τ ω ι : ℝ) : mk5 y y' τ ω ι 3 = ω := rfl

theorem mk5_four (y y' τ ω ι : ℝ) : mk5 y y' τ ω ι 4 = ι := rfl

theorem exists_fin5_iff {P : ℝ → ℝ → ℝ → ℝ → ℝ → Prop} :
    (∃ w : Fin 5 → ℝ, P (w 0) (w 1) (w 2) (w 3) (w 4)) ↔
      ∃ a b c d e : ℝ, P a b c d e := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w 0, w 1, w 2, w 3, w 4, hw⟩
  · rintro ⟨a, b, c, d, e, h⟩
    refine ⟨mk5 a b c d e, ?_⟩
    rwa [mk5_zero, mk5_one, mk5_two, mk5_three, mk5_four]

/-! ### The named conditions -/

/-- The deepness condition, with `x/(2β)` named by an existential variable. -/
def IsDeepE (k : ℕ) (B₀ : Set (Fin (k + 1) → ℝ)) (c : Fin k → ℝ) (β x : ℝ) : Prop :=
  ∀ b : ℝ, ¬(Fin.cons b c ∈ B₀ ∧
    (∃ d : ℝ, (β + β) * d = x ∧ d ≤ b) ∧ b ≤ (β + β) * x)

/-- The ratio condition, with `x/β`, `2t`, `y'/y` and `1/β` named by existential variables. -/
def RatE (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)) (ρ β x : ℝ) (c : Fin k → ℝ) : Prop :=
  ∀ t : ℝ, ¬∃ (e y y' τ ω ι : ℝ), BadP k Y ρ β x c e t τ y y' ω ι

/-! ### The three coordinate lemmas -/

theorem Spos_tuple (k : ℕ) (ρ β : ℝ) (c : Fin k → ℝ) (x : ℝ) :
    tupleC4 k ρ β c x ∈ Spos k ↔ 0 < x := by
  simp only [Spos, Set.mem_ofPred_eq, Set.mem_setOf_eq, tupleC4_x]

/-! ### The slots of `TB` -/

theorem elim_TB_r {k : ℕ} (u : C4 k → ℝ) (t e : Fin 1 → ℝ) (w : Fin 5 → ℝ) :
    Sum.elim (Sum.elim (Sum.elim u t) e) w (rT : TB k) = u r4 := by
  simp only [rT, elim_TB_C4]

theorem elim_TB_b {k : ℕ} (u : C4 k → ℝ) (t e : Fin 1 → ℝ) (w : Fin 5 → ℝ) :
    Sum.elim (Sum.elim (Sum.elim u t) e) w (bT : TB k) = u (b4 : C4 k) := by
  simp only [bT, elim_TB_C4]

theorem elim_TB_x {k : ℕ} (u : C4 k → ℝ) (t e : Fin 1 → ℝ) (w : Fin 5 → ℝ) :
    Sum.elim (Sum.elim (Sum.elim u t) e) w (xT : TB k) = u (x4 : C4 k) := by
  simp only [xT, elim_TB_C4]

theorem elim_TB_y {k : ℕ} (u : C4 k → ℝ) (t e : Fin 1 → ℝ) (w : Fin 5 → ℝ) :
    Sum.elim (Sum.elim (Sum.elim u t) e) w (yT : TB k) = w 0 := by
  simp only [yT, elim_TB_5]

theorem elim_TB_yy {k : ℕ} (u : C4 k → ℝ) (t e : Fin 1 → ℝ) (w : Fin 5 → ℝ) :
    Sum.elim (Sum.elim (Sum.elim u t) e) w (yT' : TB k) = w 1 := by
  simp only [yT', elim_TB_5]

theorem elim_TB_tau {k : ℕ} (u : C4 k → ℝ) (t e : Fin 1 → ℝ) (w : Fin 5 → ℝ) :
    Sum.elim (Sum.elim (Sum.elim u t) e) w (tauT : TB k) = w 2 := by
  simp only [tauT, elim_TB_5]

theorem elim_TB_om {k : ℕ} (u : C4 k → ℝ) (t e : Fin 1 → ℝ) (w : Fin 5 → ℝ) :
    Sum.elim (Sum.elim (Sum.elim u t) e) w (omT : TB k) = w 3 := by
  simp only [omT, elim_TB_5]

theorem elim_TB_io {k : ℕ} (u : C4 k → ℝ) (t e : Fin 1 → ℝ) (w : Fin 5 → ℝ) :
    Sum.elim (Sum.elim (Sum.elim u t) e) w (ioT : TB k) = w 4 := by
  simp only [ioT, elim_TB_5]

/-! ### The coordinate forms -/

/-- `Sdeep` on the canonical tuple is the deepness condition with the auxiliary `d = x/(2β)`. -/
theorem Sdeep_mem {k : ℕ} (B₀ : Set (Fin (k + 1) → ℝ)) (ρ β : ℝ) (c : Fin k → ℝ) (x : ℝ) :
    tupleC4 k ρ β c x ∈ Sdeep k B₀ ↔ IsDeepE k B₀ c β x := by
  rw [Sdeep, IsDeepE]
  simp only [Set.mem_ofPred_eq, Set.mem_setOf_eq]
  constructor
  · intro h b hbad
    apply h (fun _ : Fin 1 => b)
    obtain ⟨hb, ⟨d, hd1, hd2⟩, hle⟩ := hbad
    refine ⟨fun _ : Fin 1 => d, ?_⟩
    simp only [DeepBad, DeepP, Set.mem_ofPred_eq]
    have e1 : Sum.elim (Sum.elim (tupleC4 k ρ β c x) (fun _ : Fin 1 => b))
        (fun _ : Fin 1 => d) (bD2 : DB2 k) = b := by rw [elim_DB2_b]
    have e2 : (fun j : Fin k => Sum.elim (Sum.elim (tupleC4 k ρ β c x) (fun _ : Fin 1 => b))
        (fun _ : Fin 1 => d) (c4D2 j)) = c := by
      funext j
      simp only [c4D2, elim_DB2_C4, tupleC4_c]
    have e3 : Sum.elim (Sum.elim (tupleC4 k ρ β c x) (fun _ : Fin 1 => b))
        (fun _ : Fin 1 => d) (b4D2 : DB2 k) = β := by
      simp only [b4D2, elim_DB2_C4, tupleC4_b]
    have e4 : Sum.elim (Sum.elim (tupleC4 k ρ β c x) (fun _ : Fin 1 => b))
        (fun _ : Fin 1 => d) (dD2 : DB2 k) = d := by rw [elim_DB2_d]
    have e5 : Sum.elim (Sum.elim (tupleC4 k ρ β c x) (fun _ : Fin 1 => b))
        (fun _ : Fin 1 => d) (x4D2 : DB2 k) = x := by
      simp only [x4D2, elim_DB2_C4, tupleC4_x]
    rw [e1, e2, e3, e4, e5]
    exact ⟨hb, hd1, hd2, hle⟩
  · intro h b'
    rintro ⟨d', hd'⟩
    simp only [DeepBad, DeepP, Set.mem_ofPred_eq] at hd'
    have e1 : Sum.elim (Sum.elim (tupleC4 k ρ β c x) b') d' (bD2 : DB2 k) = b' 0 := by
      rw [elim_DB2_b]
    have e2 : (fun j : Fin k => Sum.elim (Sum.elim (tupleC4 k ρ β c x) b') d' (c4D2 j)) = c := by
      funext j
      simp only [c4D2, elim_DB2_C4, tupleC4_c]
    have e3 : Sum.elim (Sum.elim (tupleC4 k ρ β c x) b') d' (b4D2 : DB2 k) = β := by
      simp only [b4D2, elim_DB2_C4, tupleC4_b]
    have e4 : Sum.elim (Sum.elim (tupleC4 k ρ β c x) b') d' (dD2 : DB2 k) = d' 0 := by
      rw [elim_DB2_d]
    have e5 : Sum.elim (Sum.elim (tupleC4 k ρ β c x) b') d' (x4D2 : DB2 k) = x := by
      simp only [x4D2, elim_DB2_C4, tupleC4_x]
    rw [e1, e2, e3, e4, e5] at hd'
    exact h (b' 0) ⟨hd'.1, ⟨d' 0, hd'.2.1, hd'.2.2.1⟩, hd'.2.2.2⟩

/-- `Srat` on the canonical tuple is the ratio condition with the auxiliaries
`e = x/β`, `τ = 2t`, `ω = y'/y`, `ι = 1/β`. -/
theorem Srat_mem {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (ρ β : ℝ) (c : Fin k → ℝ) (x : ℝ) :
    tupleC4 k ρ β c x ∈ Srat k Y ↔ RatE k Y ρ β x c := by
  rw [Srat, RatE]
  simp only [Set.mem_ofPred_eq, Set.mem_setOf_eq]
  constructor
  · intro h t
    rintro ⟨e, y, y', τ, ω, ι, hP⟩
    apply h (fun _ : Fin 1 => t)
    refine ⟨fun _ : Fin 1 => e, ?_⟩
    refine ⟨mk5 y y' τ ω ι, ?_⟩
    simp only [BadR, BadP, Set.mem_ofPred_eq]
    have e1 : Sum.elim (Sum.elim (Sum.elim (tupleC4 k ρ β c x) (fun _ : Fin 1 => t))
        (fun _ : Fin 1 => e)) (mk5 y y' τ ω ι) (rT : TB k) = ρ := by
      simp only [rT, elim_TB_C4, tupleC4_r]
    have e2 : Sum.elim (Sum.elim (Sum.elim (tupleC4 k ρ β c x) (fun _ : Fin 1 => t))
        (fun _ : Fin 1 => e)) (mk5 y y' τ ω ι) (bT : TB k) = β := by
      simp only [bT, elim_TB_C4, tupleC4_b]
    have e3 : Sum.elim (Sum.elim (Sum.elim (tupleC4 k ρ β c x) (fun _ : Fin 1 => t))
        (fun _ : Fin 1 => e)) (mk5 y y' τ ω ι) (xT : TB k) = x := by
      simp only [xT, elim_TB_C4, tupleC4_x]
    have e4 : (fun j : Fin k => Sum.elim (Sum.elim (Sum.elim (tupleC4 k ρ β c x)
        (fun _ : Fin 1 => t)) (fun _ : Fin 1 => e)) (mk5 y y' τ ω ι) (cT j)) = c := by
      funext j
      simp only [cT, elim_TB_C4, tupleC4_c]
    have e5 : Sum.elim (Sum.elim (Sum.elim (tupleC4 k ρ β c x) (fun _ : Fin 1 => t))
        (fun _ : Fin 1 => e)) (mk5 y y' τ ω ι) (eT : TB k) = e := by
      rw [elim_TB_e]
    have e6 : Sum.elim (Sum.elim (Sum.elim (tupleC4 k ρ β c x) (fun _ : Fin 1 => t))
        (fun _ : Fin 1 => e)) (mk5 y y' τ ω ι) (tT : TB k) = t := by
      rw [elim_TB_t]
    have e7 : Sum.elim (Sum.elim (Sum.elim (tupleC4 k ρ β c x) (fun _ : Fin 1 => t))
        (fun _ : Fin 1 => e)) (mk5 y y' τ ω ι) (tauT : TB k) = τ := by
      rw [elim_TB_tau, mk5_two]
    have e8 : Sum.elim (Sum.elim (Sum.elim (tupleC4 k ρ β c x) (fun _ : Fin 1 => t))
        (fun _ : Fin 1 => e)) (mk5 y y' τ ω ι) (yT : TB k) = y := by
      rw [elim_TB_y, mk5_zero]
    have e9 : Sum.elim (Sum.elim (Sum.elim (tupleC4 k ρ β c x) (fun _ : Fin 1 => t))
        (fun _ : Fin 1 => e)) (mk5 y y' τ ω ι) (yT' : TB k) = y' := by
      rw [elim_TB_yy, mk5_one]
    have e10 : Sum.elim (Sum.elim (Sum.elim (tupleC4 k ρ β c x) (fun _ : Fin 1 => t))
        (fun _ : Fin 1 => e)) (mk5 y y' τ ω ι) (omT : TB k) = ω := by
      rw [elim_TB_om, mk5_three]
    have e11 : Sum.elim (Sum.elim (Sum.elim (tupleC4 k ρ β c x) (fun _ : Fin 1 => t))
        (fun _ : Fin 1 => e)) (mk5 y y' τ ω ι) (ioT : TB k) = ι := by
      rw [elim_TB_io, mk5_four]
    rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
    exact hP
  · intro h t'
    intro hmem
    obtain ⟨e', he'⟩ := hmem
    obtain ⟨w, hw⟩ := he'
    simp only [BadR, BadP, Set.mem_ofPred_eq] at hw
    have e1 : Sum.elim (Sum.elim (Sum.elim (tupleC4 k ρ β c x) t') e') w (rT : TB k) = ρ := by
      simp only [rT, elim_TB_C4, tupleC4_r]
    have e2 : Sum.elim (Sum.elim (Sum.elim (tupleC4 k ρ β c x) t') e') w (bT : TB k) = β := by
      simp only [bT, elim_TB_C4, tupleC4_b]
    have e3 : Sum.elim (Sum.elim (Sum.elim (tupleC4 k ρ β c x) t') e') w (xT : TB k) = x := by
      simp only [xT, elim_TB_C4, tupleC4_x]
    have e4 : (fun j : Fin k => Sum.elim (Sum.elim (Sum.elim (tupleC4 k ρ β c x) t') e') w
        (cT j)) = c := by
      funext j
      simp only [cT, elim_TB_C4, tupleC4_c]
    have e5 : Sum.elim (Sum.elim (Sum.elim (tupleC4 k ρ β c x) t') e') w (eT : TB k) = e' 0 := by
      rw [elim_TB_e]
    have e6 : Sum.elim (Sum.elim (Sum.elim (tupleC4 k ρ β c x) t') e') w (tT : TB k) = t' 0 := by
      rw [elim_TB_t]
    have e7 : Sum.elim (Sum.elim (Sum.elim (tupleC4 k ρ β c x) t') e') w (tauT : TB k) = w 2 := by
      rw [elim_TB_tau]
    have e8 : Sum.elim (Sum.elim (Sum.elim (tupleC4 k ρ β c x) t') e') w (yT : TB k) = w 0 := by
      rw [elim_TB_y]
    have e9 : Sum.elim (Sum.elim (Sum.elim (tupleC4 k ρ β c x) t') e') w (yT' : TB k) = w 1 := by
      rw [elim_TB_yy]
    have e10 : Sum.elim (Sum.elim (Sum.elim (tupleC4 k ρ β c x) t') e') w (omT : TB k) = w 3 := by
      rw [elim_TB_om]
    have e11 : Sum.elim (Sum.elim (Sum.elim (tupleC4 k ρ β c x) t') e') w (ioT : TB k) = w 4 := by
      rw [elim_TB_io]
    rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at hw
    exact h (t' 0) ⟨e' 0, w 0, w 1, w 2, w 3, w 4, hw⟩


end Work.WilC4.CESAux
