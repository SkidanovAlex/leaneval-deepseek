import Mathlib
import Submission.Work.Smooth.SphereJordan.LocalArc.Basic
import Submission.Work.Smooth.SphereJordan.LocalArc.ArcRange
import Submission.Work.Smooth.SphereJordan.LocalArc.Ends
import Submission.Work.Smooth.SphereJordan.LocalArc.InjectExtend

/-!
# The nested-union lemma for arc ranges

`isArcRange_iUnion_of_monotone`: an increasing sequence of arc ranges through `x₀` in a locally-arc
Hausdorff space has a union which is again an arc range through `x₀`.
-/

namespace Work.Smooth.SphereJordan.LocalArc

open Set Function Filter

open scoped Topology

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- **The reparametrisation step with prescribed coverage.**

Let `ψ, δ : ℝ → X` be continuous injections with `range ψ ⊆ range δ`, `r < R₀`, and let `A ⊆ ℝ` be a
bounded set of *coordinates* (in the parametrisation `δ`).  Then `ψ` can be reparametrised to an
embedding `ψ'` with the same range as `δ`, agreeing with `ψ` on `Ioo (-r) r`, whose image over an
interval of some radius `r' ≥ R₀` contains the points `δ a`, `a ∈ A`. -/
theorem exists_reparametrising_step_of_bounded (H : Work.Smooth.SphereJordan.IsLocallyArc X)
    {ψ δ : ℝ → X} (hψc : Continuous ψ) (hψi : Function.Injective ψ)
    (hδc : Continuous δ) (hδi : Function.Injective δ)
    (hsub : Set.range ψ ⊆ Set.range δ) {r R₀ : ℝ} (hr : 0 < r)
    {A : Set ℝ} (hAb : BddBelow A) (hAu : BddAbove A) :
    ∃ (r' : ℝ) (ψ' : ℝ → X), r < r' ∧ R₀ ≤ r' ∧ Continuous ψ' ∧ Function.Injective ψ' ∧
      Set.range ψ' = Set.range δ ∧ Set.EqOn ψ' ψ (Set.Ioo (-r) r) ∧
      δ '' A ⊆ ψ' '' Set.Ioo (-r') r' := by
  have hopen : IsOpenMap δ := isOpenMap_of_injective_continuous H hδc hδi
  let δinv : Set.range δ → ℝ := fun y => Classical.choose (Set.mem_range.mp y.2)
  have hδinv_c : Continuous δinv := continuous_choose_range hδi hopen
  have hδinv : ∀ y : Set.range δ, δ (δinv y) = (y : X) := fun y =>
    Classical.choose_spec (Set.mem_range.mp y.2)
  let h : ℝ → ℝ := fun t => δinv ⟨ψ t, hsub (Set.mem_range_self t)⟩
  have hhc : Continuous h := hδinv_c.comp (hψc.subtype_mk fun t => hsub (Set.mem_range_self t))
  have hhi : Function.Injective h := by
    intro a b hab
    refine hψi ?_
    have h1 : δ (h a) = δ (h b) := by rw [hab]
    simpa only [h, hδinv] using h1
  obtain ⟨h', h'c, h'i, h's, h'eq⟩ := exists_continuous_injective_surjective_eqOn_Ioo hhc hhi r hr
  obtain hm | hanti := h'c.strictMono_of_inj h'i
  · obtain ⟨m, hmA⟩ := hAb
    obtain ⟨M, hMA⟩ := hAu
    obtain ⟨s₁, hs₁⟩ := h's (M + 1)
    obtain ⟨s₂, hs₂⟩ := h's (m - 1)
    set r' : ℝ := max (max (r + 1) R₀) (max s₁ (-s₂)) with hr'def
    have hrlt : r < r' := lt_of_lt_of_le (show r < r + 1 by linarith)
      (le_trans (le_max_left (r + 1) R₀) (le_max_left _ _))
    have hR₀ : R₀ ≤ r' := le_trans (le_max_right (r + 1) R₀) (le_max_left _ _)
    have hle1 : s₁ ≤ r' := le_trans (le_max_left s₁ (-s₂)) (le_max_right _ _)
    have hle2 : -s₂ ≤ r' := le_trans (le_max_right s₁ (-s₂)) (le_max_right _ _)
    have hlow : h' (-r') ≤ m - 1 := by
      have : -r' ≤ s₂ := by linarith
      calc h' (-r') ≤ h' s₂ := hm.monotone this
        _ = m - 1 := hs₂
    have hhigh : M + 1 ≤ h' r' := by
      calc M + 1 = h' s₁ := hs₁.symm
        _ ≤ h' r' := hm.monotone hle1
    refine ⟨r', fun t => δ (h' t), hrlt, hR₀, hδc.comp h'c, fun a b hab => h'i (hδi hab),
      ?_, ?_, ?_⟩
    · rw [show Set.range (fun t => δ (h' t)) = Set.range (δ ∘ h') from rfl, Set.range_comp,
        h's.range_eq, Set.image_univ]
    · intro t ht
      show δ (h' t) = ψ t
      rw [h'eq ht]
      simp only [h, hδinv]
    · intro z hz
      obtain ⟨a, ha, rfl⟩ := hz
      obtain ⟨t, ht⟩ := h's a
      refine ⟨t, ⟨?_, ?_⟩, by show δ (h' t) = δ a; rw [ht]⟩
      · by_contra hcon
        push_neg at hcon
        have h1 : h' t ≤ h' (-r') := hm.monotone (by linarith)
        rw [ht] at h1
        have h2 : m ≤ a := hmA ha
        linarith
      · by_contra hcon
        push_neg at hcon
        have h1 : h' r' ≤ h' t := hm.monotone (by linarith)
        rw [ht] at h1
        have h2 : a ≤ M := hMA ha
        linarith
  · obtain ⟨m, hmA⟩ := hAb
    obtain ⟨M, hMA⟩ := hAu
    obtain ⟨s₁, hs₁⟩ := h's (M + 1)
    obtain ⟨s₂, hs₂⟩ := h's (m - 1)
    set r' : ℝ := max (max (r + 1) R₀) (max (-s₁) s₂) with hr'def
    have hrlt : r < r' := lt_of_lt_of_le (show r < r + 1 by linarith)
      (le_trans (le_max_left (r + 1) R₀) (le_max_left _ _))
    have hR₀ : R₀ ≤ r' := le_trans (le_max_right (r + 1) R₀) (le_max_left _ _)
    have hle1 : -s₁ ≤ r' := le_trans (le_max_left (-s₁) s₂) (le_max_right _ _)
    have hle2 : s₂ ≤ r' := le_trans (le_max_right (-s₁) s₂) (le_max_right _ _)
    have hhigh : M + 1 ≤ h' (-r') := by
      have : -r' ≤ s₁ := by linarith
      calc M + 1 = h' s₁ := hs₁.symm
        _ ≤ h' (-r') := hanti.antitone this
    have hlow : h' r' ≤ m - 1 := by
      calc h' r' ≤ h' s₂ := hanti.antitone hle2
        _ = m - 1 := hs₂
    refine ⟨r', fun t => δ (h' t), hrlt, hR₀, hδc.comp h'c, fun a b hab => h'i (hδi hab),
      ?_, ?_, ?_⟩
    · rw [show Set.range (fun t => δ (h' t)) = Set.range (δ ∘ h') from rfl, Set.range_comp,
        h's.range_eq, Set.image_univ]
    · intro t ht
      show δ (h' t) = ψ t
      rw [h'eq ht]
      simp only [h, hδinv]
    · intro z hz
      obtain ⟨a, ha, rfl⟩ := hz
      obtain ⟨t, ht⟩ := h's a
      refine ⟨t, ⟨?_, ?_⟩, by show δ (h' t) = δ a; rw [ht]⟩
      · by_contra hcon
        push_neg at hcon
        have h1 : h' (-r') ≤ h' t := hanti.antitone (by linarith)
        rw [ht] at h1
        have h2 : a ≤ M := hMA ha
        linarith
      · by_contra hcon
        push_neg at hcon
        have h1 : h' t ≤ h' r' := hanti.antitone (by linarith)
        rw [ht] at h1
        have h2 : m ≤ a := hmA ha
        linarith

/-- The state of the inductive construction. -/
def GoodState {X : Type*} [TopologicalSpace X] (U : ℕ → Set X) (x₀ : X) (n : ℕ)
    (ψ : ℕ → ℝ → X) (r w : ℕ → ℝ) : Prop :=
  (∀ m ≤ n, Continuous (ψ m) ∧ Function.Injective (ψ m) ∧ Set.range (ψ m) = U m ∧ ψ m 0 = x₀) ∧
  (∀ m ≤ n, 0 < r m) ∧
  (∀ m ≤ n, ∀ k ≤ m, r k ≤ r m) ∧
  (∀ m ≤ n, 0 < w m ∧ w m + 3 ≤ r m) ∧
  (∀ m ≤ n, w m ≤ w n) ∧
  ((n : ℝ) + 1 ≤ w n) ∧
  (∀ m < n, Set.EqOn (ψ (m + 1)) (ψ m) (Set.Ioo (-(r m)) (r m))) ∧
  (∀ m ≤ n, ∀ t ∈ Set.Icc (-(w n)) (w n), ∃ s ∈ Set.Ioo (-(r n)) (r n), ψ n s = ψ m t)

/-- The initial state. -/
theorem goodState_zero {x₀ : X} {U : ℕ → Set X} (hU : ∀ n, IsArcRange x₀ (U n)) :
    GoodState U x₀ 0 (Function.update (fun _ : ℕ => fun _ : ℝ => x₀) 0 (Classical.choose (hU 0)))
      (fun _ => 4) (fun _ => 1) := by
  obtain ⟨hc, hi, h0, hr⟩ := Classical.choose_spec (hU 0)
  have hself : (Function.update (fun _ : ℕ => fun _ : ℝ => x₀) 0 (Classical.choose (hU 0))) 0
      = Classical.choose (hU 0) := Function.update_self ..
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm
    have hm0 : m = 0 := Nat.le_zero.mp hm
    rw [hm0, hself]
    exact ⟨hc, hi, hr, h0⟩
  · intro m hm; norm_num
  · intro m hm k hk; norm_num
  · intro m hm; norm_num
  · intro m hm; norm_num
  · norm_num
  · intro m hm; exact absurd hm (Nat.not_lt_zero m)
  · intro m hm t ht
    have hm0 : m = 0 := Nat.le_zero.mp hm
    subst hm0
    simp only [Function.update_self] at ht ⊢
    exact ⟨t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩

/-- **The inductive step of the nested-union construction.** -/
theorem goodState_step (H : Work.Smooth.SphereJordan.IsLocallyArc X) {x₀ : X} {U : ℕ → Set X}
    (hU : ∀ n, IsArcRange x₀ (U n)) (hmono : Monotone U) {n : ℕ} {ψ : ℕ → ℝ → X} {r w : ℕ → ℝ}
    (hg : GoodState U x₀ n ψ r w) :
    ∃ (ψnew : ℝ → X) (rnew : ℝ),
      GoodState U x₀ (n + 1) (Function.update ψ (n + 1) ψnew)
        (Function.update r (n + 1) rnew) (Function.update w (n + 1) (w n + 1)) := by
  classical
  obtain ⟨hcont, hpos, hrle, hwp, hwmono, hwge, hagree, hcov⟩ := hg
  set d : ℝ → X := Classical.choose (hU (n + 1)) with hd
  have hdc : Continuous d := (Classical.choose_spec (hU (n + 1))).1
  have hdi : Function.Injective d := (Classical.choose_spec (hU (n + 1))).2.1
  have hdr : Set.range d = U (n + 1) := (Classical.choose_spec (hU (n + 1))).2.2.2
  have hsub : Set.range (ψ n) ⊆ Set.range d := by
    intro y hy
    rw [hdr]
    exact hmono (Nat.le_succ n) ((hcont n le_rfl).2.2.1 ▸ hy)
  have hmem : ∀ (m : ℕ), m ≤ n → ∀ t : ℝ, ψ m t ∈ Set.range d := by
    intro m hm t
    rw [hdr]
    exact hmono (Nat.le_succ n) (hmono hm ((hcont m hm).2.2.1 ▸ Set.mem_range_self t))
  let dinv : Set.range d → ℝ := fun y => Classical.choose (Set.mem_range.mp y.2)
  have hdinv_c : Continuous dinv :=
    continuous_choose_range hdi (isOpenMap_of_injective_continuous H hdc hdi)
  have hdinv : ∀ y : Set.range d, d (dinv y) = (y : X) := fun y =>
    Classical.choose_spec (Set.mem_range.mp y.2)
  have hmle : ∀ m : {m : ℕ // m ∈ (Finset.range (n + 1) : Set ℕ)}, (m : ℕ) ≤ n := fun m => by
    have := Finset.mem_range.mp (Finset.mem_coe.mp m.2); omega
  let A : Set ℝ := ⋃ m : {m : ℕ // m ∈ (Finset.range (n + 1) : Set ℕ)},
      (fun t => dinv ⟨ψ (m : ℕ) t, hmem (m : ℕ) (hmle m) t⟩) ''
        Set.Icc (-(w n + 1)) (w n + 1)
  haveI hfin : Finite {m : ℕ // m ∈ (Finset.range (n + 1) : Set ℕ)} :=
    (Finset.finite_toSet _).to_subtype
  have hAc : IsCompact A := by
    refine isCompact_iUnion fun m => ?_
    exact isCompact_Icc.image (hdinv_c.comp (((hcont (m : ℕ) (hmle m)).1).subtype_mk _))
  obtain ⟨r', ψ', hrlt, hR₀, hψ'c, hψ'i, hψ'r, hψ'eq, hψ'cov⟩ :=
    exists_reparametrising_step_of_bounded H (hcont n le_rfl).1 (hcont n le_rfl).2.1 hdc hdi hsub
      (hr := hpos n le_rfl) (R₀ := r n + 1) hAc.bddBelow hAc.bddAbove
  have hstep_ψ : ∀ m, m ≠ n + 1 → Function.update ψ (n + 1) ψ' m = ψ m :=
    fun m hm => Function.update_of_ne hm ψ' ψ
  have hstep_r : ∀ m, m ≠ n + 1 → Function.update r (n + 1) r' m = r m :=
    fun m hm => Function.update_of_ne hm r' r
  have hstep_w : ∀ m, m ≠ n + 1 → Function.update w (n + 1) (w n + 1) m = w m :=
    fun m hm => Function.update_of_ne hm (w n + 1) w
  have hselfψ : Function.update ψ (n + 1) ψ' (n + 1) = ψ' := Function.update_self ..
  have hselfr : Function.update r (n + 1) r' (n + 1) = r' := Function.update_self ..
  have hselfw : Function.update w (n + 1) (w n + 1) (n + 1) = w n + 1 := Function.update_self ..
  refine ⟨ψ', r', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- basic properties
    intro m hm
    rcases Nat.lt_or_eq_of_le hm with hlt | heq
    · rw [hstep_ψ m (by omega)]
      exact hcont m (by omega)
    · rw [heq, hselfψ]
      refine ⟨hψ'c, hψ'i, ?_, ?_⟩
      · rw [hψ'r, hdr]
      · have h0 : (0 : ℝ) ∈ Set.Ioo (-(r n)) (r n) :=
          ⟨by linarith [hpos n le_rfl], hpos n le_rfl⟩
        rw [hψ'eq h0]
        exact (hcont n le_rfl).2.2.2
  · -- positivity
    intro m hm
    rcases Nat.lt_or_eq_of_le hm with hlt | heq
    · rw [hstep_r m (by omega)]
      exact hpos m (by omega)
    · rw [heq, hselfr]
      exact lt_trans (hpos n le_rfl) hrlt
  · -- monotonicity of the radii
    intro m hm k hk
    by_cases hm1 : m = n + 1
    · rw [hm1] at hm hk ⊢
      rw [hselfr]
      by_cases hk1 : k = n + 1
      · rw [hk1, hselfr]
      · rw [hstep_r k (by omega)]
        have h1 : r k ≤ r n := hrle n le_rfl k (by omega)
        linarith
    · rw [hstep_r m (by omega)]
      have hm' : m ≤ n := by omega
      by_cases hk1 : k = n + 1
      · exfalso; omega
      · rw [hstep_r k (by omega)]
        exact hrle m hm' k (by omega)
  · -- the windows
    intro m hm
    rcases Nat.lt_or_eq_of_le hm with hlt | heq
    · rw [hstep_w m (by omega), hstep_r m (by omega)]
      exact hwp m (by omega)
    · rw [heq, hselfw, hselfr]
      constructor
      · linarith [(hwp n le_rfl).1]
      · have h1 : w n + 3 ≤ r n := (hwp n le_rfl).2
        linarith
  · -- monotonicity of the windows
    intro m hm
    rcases Nat.lt_or_eq_of_le hm with hlt | heq
    · rw [hstep_w m (by omega), hselfw]
      have h1 : w m ≤ w n := hwmono m (by omega)
      linarith
    · rw [heq, hselfw]
  · -- the window grows
    rw [hselfw]
    have h1 : (n : ℝ) + 1 ≤ w n := hwge
    push_cast
    linarith
  · -- agreement
    intro m hm
    have hmle : m ≤ n := by omega
    rcases Nat.lt_or_eq_of_le hmle with hlt | heq
    · rw [hstep_ψ m (by omega), hstep_ψ (m + 1) (by omega), hstep_r m (by omega)]
      exact hagree m hlt
    · rw [heq, hselfψ, hstep_ψ n (by omega), hstep_r n (by omega)]
      exact hψ'eq
  · -- coverage
    intro m hm t ht
    rw [hselfw] at ht
    rcases Nat.lt_or_eq_of_le hm with hlt | heq
    · have hmle' : m ≤ n := by omega
      have hmemA : dinv ⟨ψ m t, hmem m hmle' t⟩ ∈ A :=
        Set.mem_iUnion.mpr ⟨⟨m, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))⟩,
          ⟨t, ⟨ht.1, ht.2⟩, rfl⟩⟩
      have h1 : d (dinv ⟨ψ m t, hmem m hmle' t⟩) ∈ ψ' '' Set.Ioo (-r') r' :=
        hψ'cov ⟨_, hmemA, rfl⟩
      obtain ⟨s, hs, hseq⟩ := h1
      rw [hdinv] at hseq
      refine ⟨s, ?_, ?_⟩
      · rw [hselfr]; exact hs
      · rw [hselfψ, hstep_ψ m (by omega)]; exact hseq
    · rw [heq, hselfψ, hselfr]
      refine ⟨t, ?_, rfl⟩
      rw [Set.mem_Ioo]
      have h3 : w n + 3 ≤ r n := (hwp n le_rfl).2
      constructor <;> linarith [ht.1, ht.2, h3, hpos n le_rfl, hrlt]

/-- The stages of the construction. -/
noncomputable def stageState (H : Work.Smooth.SphereJordan.IsLocallyArc X) {x₀ : X}
    {U : ℕ → Set X} (hU : ∀ n, IsArcRange x₀ (U n)) (hmono : Monotone U) :
    (n : ℕ) → {p : (ℕ → ℝ → X) × (ℕ → ℝ) × (ℕ → ℝ) // GoodState U x₀ n p.1 p.2.1 p.2.2}
  | 0 => ⟨(Function.update (fun _ : ℕ => fun _ : ℝ => x₀) 0 (Classical.choose (hU 0)),
      fun _ => 4, fun _ => 1), goodState_zero hU⟩
  | (n + 1) =>
      let prev := stageState H hU hmono n
      let hstep := goodState_step H hU hmono prev.2
      ⟨(Function.update prev.1.1 (n + 1) (Classical.choose hstep),
        Function.update prev.1.2.1 (n + 1) (Classical.choose (Classical.choose_spec hstep)),
        Function.update prev.1.2.2 (n + 1) (prev.1.2.2 n + 1)),
        Classical.choose_spec (Classical.choose_spec hstep)⟩

lemma stageState_stable (H : Work.Smooth.SphereJordan.IsLocallyArc X) {x₀ : X} {U : ℕ → Set X}
    (hU : ∀ n, IsArcRange x₀ (U n)) (hmono : Monotone U) {M m : ℕ} (hm : m ≤ M) :
    (stageState H hU hmono M).1.1 m = (stageState H hU hmono m).1.1 m ∧
    (stageState H hU hmono M).1.2.1 m = (stageState H hU hmono m).1.2.1 m ∧
    (stageState H hU hmono M).1.2.2 m = (stageState H hU hmono m).1.2.2 m := by
  induction M, hm using Nat.le_induction with
  | base => exact ⟨rfl, rfl, rfl⟩
  | succ M hM ih =>
      refine ⟨?_, ?_, ?_⟩
      · show Function.update (stageState H hU hmono M).1.1 (M + 1) _ m = _
        rw [Function.update_of_ne (show m ≠ M + 1 by omega)]
        exact ih.1
      · show Function.update (stageState H hU hmono M).1.2.1 (M + 1) _ m = _
        rw [Function.update_of_ne (show m ≠ M + 1 by omega)]
        exact ih.2.1
      · show Function.update (stageState H hU hmono M).1.2.2 (M + 1) _ m = _
        rw [Function.update_of_ne (show m ≠ M + 1 by omega)]
        exact ih.2.2

/-- **The nested-union lemma.** -/
theorem isArcRange_iUnion_of_monotone (H : Work.Smooth.SphereJordan.IsLocallyArc X) {x₀ : X}
    (U : ℕ → Set X) (hU : ∀ n, IsArcRange x₀ (U n)) (hmono : Monotone U) :
    IsArcRange x₀ (⋃ n, U n) := by
  classical
  let ps : ℕ → ℝ → X := fun m => (stageState H hU hmono m).1.1 m
  let rr : ℕ → ℝ := fun m => (stageState H hU hmono m).1.2.1 m
  let ww : ℕ → ℝ := fun m => (stageState H hU hmono m).1.2.2 m
  have hbasic : ∀ m, Continuous (ps m) ∧ Function.Injective (ps m) ∧
      Set.range (ps m) = U m ∧ ps m 0 = x₀ := by
    intro m
    obtain ⟨h1, -, -, -, -, -, -, -⟩ := (stageState H hU hmono m).2
    exact h1 m le_rfl
  have hrpos : ∀ m, 0 < rr m := by
    intro m
    obtain ⟨-, h2, -, -, -, -, -, -⟩ := (stageState H hU hmono m).2
    exact h2 m le_rfl
  have hrle : ∀ k m, k ≤ m → rr k ≤ rr m := by
    intro k m hkm
    obtain ⟨-, -, h3, -, -, -, -, -⟩ := (stageState H hU hmono m).2
    have h1 : (stageState H hU hmono m).1.2.1 k ≤ (stageState H hU hmono m).1.2.1 m :=
      h3 m le_rfl k hkm
    have e1 : (stageState H hU hmono m).1.2.1 k = rr k :=
      (stageState_stable H hU hmono (M := m) (m := k) hkm).2.1
    have e2 : (stageState H hU hmono m).1.2.1 m = rr m := rfl
    rwa [e1, e2] at h1
  have hwmono : ∀ k m, k ≤ m → ww k ≤ ww m := by
    intro k m hkm
    obtain ⟨-, -, -, -, h5, -, -, -⟩ := (stageState H hU hmono m).2
    have h1 : (stageState H hU hmono m).1.2.2 k ≤ (stageState H hU hmono m).1.2.2 m :=
      h5 k hkm
    have e1 : (stageState H hU hmono m).1.2.2 k = ww k :=
      (stageState_stable H hU hmono (M := m) (m := k) hkm).2.2
    have e2 : (stageState H hU hmono m).1.2.2 m = ww m := rfl
    rwa [e1, e2] at h1
  have hwbig : ∀ m : ℕ, (m : ℝ) + 1 ≤ ww m := by
    intro m
    obtain ⟨-, -, -, -, -, h6, -, -⟩ := (stageState H hU hmono m).2
    exact h6
  have hwlt : ∀ m, ww m + 3 ≤ rr m := by
    intro m
    obtain ⟨-, -, -, h4, -, -, -, -⟩ := (stageState H hU hmono m).2
    exact (h4 m le_rfl).2
  have hagree_step : ∀ m, Set.EqOn (ps (m + 1)) (ps m) (Set.Ioo (-(rr m)) (rr m)) := by
    intro m
    obtain ⟨-, -, -, -, -, -, h7, -⟩ := (stageState H hU hmono (m + 1)).2
    have h1 := h7 m (by omega)
    have e1 : (stageState H hU hmono (m + 1)).1.1 (m + 1) = ps (m + 1) := rfl
    have e2 : (stageState H hU hmono (m + 1)).1.1 m = ps m :=
      (stageState_stable H hU hmono (M := m + 1) (m := m) (by omega)).1
    have e3 : (stageState H hU hmono (m + 1)).1.2.1 m = rr m :=
      (stageState_stable H hU hmono (M := m + 1) (m := m) (by omega)).2.1
    rwa [e1, e2, e3] at h1
  have hwindow : ∀ N m : ℕ, m ≤ N → ∀ t ∈ Set.Icc (-(ww N)) (ww N),
      ∃ s ∈ Set.Ioo (-(rr N)) (rr N), ps N s = ps m t := by
    intro N m hmN t ht
    obtain ⟨-, -, -, -, -, -, -, h8⟩ := (stageState H hU hmono N).2
    obtain ⟨s, hs, hseq⟩ := h8 m hmN t ht
    have e1 : (stageState H hU hmono N).1.2.1 N = rr N := rfl
    have e2 : (stageState H hU hmono N).1.1 N = ps N := rfl
    have e3 : (stageState H hU hmono N).1.1 m = ps m :=
      (stageState_stable H hU hmono (M := N) (m := m) hmN).1
    rw [e1] at hs
    rw [e2, e3] at hseq
    exact ⟨s, hs, hseq⟩
  have hagree : ∀ k m : ℕ, k ≤ m → Set.EqOn (ps m) (ps k) (Set.Ioo (-(rr k)) (rr k)) := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => intro t _; rfl
    | succ m hkm ih =>
        intro t ht
        rcases lt_or_ge k (m + 1) with h | h
        · have hkm' : k ≤ m := Nat.lt_succ_iff.mp h
          have hr : rr k ≤ rr m := hrle k m hkm'
          have ht2 : t ∈ Set.Ioo (-(rr m)) (rr m) :=
            ⟨by linarith [ht.1], by linarith [ht.2]⟩
          rw [hagree_step m ht2]
          exact ih ht
        · exfalso; omega
  have hself : ∀ t : ℝ, |t| < rr ⌈|t|⌉₊ := by
    intro t
    have h1 : ((⌈|t|⌉₊ : ℕ) : ℝ) + 1 ≤ ww ⌈|t|⌉₊ := hwbig ⌈|t|⌉₊
    have h2 : |t| ≤ ((⌈|t|⌉₊ : ℕ) : ℝ) := Nat.le_ceil |t|
    have h3 : ww ⌈|t|⌉₊ + 3 ≤ rr ⌈|t|⌉₊ := hwlt ⌈|t|⌉₊
    linarith
  let γ : ℝ → X := fun t => ps ⌈|t|⌉₊ t
  have hγ_eq : ∀ (t : ℝ) (N : ℕ), ⌈|t|⌉₊ ≤ N → γ t = ps N t := by
    intro t N hN
    show ps ⌈|t|⌉₊ t = ps N t
    exact (hagree ⌈|t|⌉₊ N hN (abs_lt.mp (hself t))).symm
  have hγc : Continuous γ := by
    rw [continuous_iff_continuousAt]
    intro t
    have hmem : ∀ᶠ s in 𝓝 t, |s| < rr ⌈|t|⌉₊ :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds (hself t)
    refine ((hbasic ⌈|t|⌉₊).1).continuousAt.congr ?_
    filter_upwards [hmem] with s hs
    rcases le_total ⌈|s|⌉₊ ⌈|t|⌉₊ with hle | hle
    · exact hagree ⌈|s|⌉₊ ⌈|t|⌉₊ hle (abs_lt.mp (hself s))
    · exact (hagree ⌈|t|⌉₊ ⌈|s|⌉₊ hle (abs_lt.mp hs)).symm
  have hγi : Function.Injective γ := by
    intro a b hab
    have h1 : γ a = ps (max ⌈|a|⌉₊ ⌈|b|⌉₊) a := hγ_eq a _ (le_max_left _ _)
    have h2 : γ b = ps (max ⌈|a|⌉₊ ⌈|b|⌉₊) b := hγ_eq b _ (le_max_right _ _)
    rw [h1, h2] at hab
    exact (hbasic _).2.1 hab
  have hγ0 : γ 0 = x₀ := by
    have h1 : (⌈|(0:ℝ)|⌉₊ : ℕ) = 0 := by simp
    have h2 : γ 0 = ps 0 0 := by
      show ps ⌈|(0:ℝ)|⌉₊ 0 = ps 0 0
      rw [h1]
    rw [h2]
    exact (hbasic 0).2.2.2
  refine ⟨γ, hγc, hγi, hγ0, ?_⟩
  apply subset_antisymm
  · rintro y ⟨t, rfl⟩
    show γ t ∈ ⋃ n, U n
    have h1 : γ t = ps ⌈|t|⌉₊ t := rfl
    rw [h1]
    refine Set.mem_iUnion.mpr ⟨⌈|t|⌉₊, ?_⟩
    rw [← (hbasic ⌈|t|⌉₊).2.2.1]
    exact Set.mem_range_self t
  · intro y hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨m, hm⟩ := hy
    rw [← (hbasic m).2.2.1] at hm
    obtain ⟨t, ht⟩ := hm
    set N : ℕ := max ⌈|t|⌉₊ m with hN
    have htm : t ∈ Set.Icc (-(ww N)) (ww N) := by
      have h4 : |t| < rr ⌈|t|⌉₊ := hself t
      have h5 : rr ⌈|t|⌉₊ ≤ rr N := hrle ⌈|t|⌉₊ N (le_max_left _ _)
      have h7 : |t| ≤ ww N := by
        have h8 : ((⌈|t|⌉₊ : ℕ) : ℝ) + 1 ≤ ww ⌈|t|⌉₊ := hwbig ⌈|t|⌉₊
        have h9 : ww ⌈|t|⌉₊ ≤ ww N := hwmono ⌈|t|⌉₊ N (le_max_left _ _)
        have h10 : |t| ≤ ((⌈|t|⌉₊ : ℕ) : ℝ) := Nat.le_ceil |t|
        linarith
      exact ⟨by linarith [neg_abs_le t, h7], by linarith [le_abs_self t, h7]⟩
    obtain ⟨s, hs, hseq⟩ := hwindow N m (le_max_right _ _) t htm
    refine ⟨s, ?_⟩
    have hs' : |s| < rr N := abs_lt.mpr hs
    rcases le_total ⌈|s|⌉₊ N with hle | hle
    · rw [hγ_eq s N hle, hseq]
      exact ht
    · have hNK : N ≤ ⌈|s|⌉₊ := hle
      have h1 : ps ⌈|s|⌉₊ s = ps N s :=
        hagree N ⌈|s|⌉₊ hNK (abs_lt.mp hs')
      rw [show γ s = ps ⌈|s|⌉₊ s from rfl, h1, hseq]
      exact ht

end

end Work.Smooth.SphereJordan.LocalArc
