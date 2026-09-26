import Mathlib
import Submission.Work.Smooth.SphereJordan.LocalArc.Basic
import Submission.Work.Smooth.SphereJordan.LocalArc.localArcExistsExtensionIcc

/-!
# Building a global embedding of `ℝ`

In a space that is locally an arc, any continuous injective arc on a closed interval can be
extended at either end.  Iterating this, we obtain a continuous injective map `ℝ → X`.
-/

namespace Work.Smooth.SphereJordan.LocalArc

open Set Function

open scoped Topology

noncomputable section

/-- `g` is a continuous injective parametrisation of an arc on `Icc (-n) n` starting at `x₀`. -/
structure IsArcOn {X : Type*} [TopologicalSpace X] (x₀ : X) (n : ℕ) (g : ℝ → X) : Prop where
  cont : ContinuousOn g (Icc (-(n:ℝ)) n)
  inj : InjOn g (Icc (-(n:ℝ)) n)
  zero : g 0 = x₀

/-- The same, one step further out, together with agreement with the previous arc. -/
structure IsArcOnExt {X : Type*} [TopologicalSpace X] (x₀ : X) (n : ℕ) (g : ℝ → X) (f : ℝ → X) :
    Prop where
  cont : ContinuousOn g (Icc (-(n:ℝ) - 1) ((n:ℝ) + 1))
  inj : InjOn g (Icc (-(n:ℝ) - 1) ((n:ℝ) + 1))
  zero : g 0 = x₀
  agree : EqOn g f (Icc (-(n:ℝ)) n)

/-- Reflection of the extension lemma: an arc on `Icc a b` can be extended below `a`. -/
theorem localArcExistsExtensionIcc_left {X : Type*} [TopologicalSpace X] [T2Space X]
    (H : IsLocallyArc X) {a b : ℝ} (hab : a ≤ b) {α : ℝ → X}
    (hc : ContinuousOn α (Icc a b)) (hi : InjOn α (Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℝ → X, ContinuousOn β (Icc (a - ε) b) ∧ InjOn β (Icc (a - ε) b) ∧
      EqOn β α (Icc a b) := by
  set α' : ℝ → X := fun t => α (a + b - t) with hα'def
  have hmaps : ∀ t ∈ Icc a b, a + b - t ∈ Icc a b := by
    intro t ht
    simp only [Set.mem_Icc] at ht ⊢
    constructor <;> linarith [ht.1, ht.2]
  have hc' : ContinuousOn α' (Icc a b) :=
    hc.comp (continuous_const.sub continuous_id).continuousOn hmaps
  have hi' : InjOn α' (Icc a b) := by
    intro s hs t ht hst
    have hst' : a + b - s = a + b - t := hi (hmaps s hs) (hmaps t ht) hst
    linarith
  obtain ⟨β', hcβ', hiβ', heβ'⟩ := localArcExistsExtensionIcc H hab hc' hi' hε
  refine ⟨fun t => β' (a + b - t), ?_, ?_, ?_⟩
  · refine hcβ'.comp (continuous_const.sub continuous_id).continuousOn ?_
    intro t ht
    simp only [Set.mem_Icc] at ht ⊢
    constructor <;> linarith [ht.1, ht.2]
  · intro s hs t ht hst
    have hs' : a + b - s ∈ Icc a (b + ε) := by
      simp only [Set.mem_Icc] at hs ⊢
      constructor <;> linarith [hs.1, hs.2]
    have ht' : a + b - t ∈ Icc a (b + ε) := by
      simp only [Set.mem_Icc] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    have hst' : a + b - s = a + b - t := hiβ' hs' ht' hst
    linarith
  · intro t ht
    have ht' : a + b - t ∈ Icc a b := hmaps t ht
    show β' (a + b - t) = α t
    rw [heβ' ht']
    show α (a + b - (a + b - t)) = α t
    congr 1
    ring

/-- Extend an arc on `Icc a b` on both sides. -/
theorem localArcExistsExtensionIcc_both {X : Type*} [TopologicalSpace X] [T2Space X]
    (H : IsLocallyArc X) {a b : ℝ} (hab : a ≤ b) {α : ℝ → X}
    (hc : ContinuousOn α (Icc a b)) (hi : InjOn α (Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℝ → X, ContinuousOn β (Icc (a - ε) (b + ε)) ∧ InjOn β (Icc (a - ε) (b + ε)) ∧
      EqOn β α (Icc a b) := by
  obtain ⟨β, hcβ, hiβ, hβ⟩ := localArcExistsExtensionIcc H hab hc hi hε
  obtain ⟨γ, hcγ, hiγ, hγ⟩ := localArcExistsExtensionIcc_left H (by linarith : a ≤ b + ε) hcβ hiβ hε
  refine ⟨γ, hcγ, hiγ, ?_⟩
  intro t ht
  have ht' : t ∈ Icc a (b + ε) := ⟨ht.1, by linarith [ht.2]⟩
  exact (hγ ht').trans (hβ ht)

/-- One step of the iterative construction of a global arc. -/
theorem devExistsStep {X : Type*} [TopologicalSpace X] [T2Space X] (H : IsLocallyArc X)
    (x₀ : X) (n : ℕ)
    (g : { g : ℝ → X // IsArcOn x₀ n g }) :
    ∃ β : ℝ → X, IsArcOnExt x₀ n β g.1 := by
  obtain ⟨β, hc, hi, he⟩ :=
    localArcExistsExtensionIcc_both H (a := -(n:ℝ)) (b := (n:ℝ))
      (neg_le_self (Nat.cast_nonneg n)) g.2.cont g.2.inj (ε := 1) one_pos
  refine ⟨β, ?_, ?_, ?_, he⟩
  · convert hc using 2 <;> ring
  · convert hi using 2 <;> ring
  · rw [he (by simp only [Set.mem_Icc]; exact ⟨neg_nonpos.mpr (Nat.cast_nonneg n),
      Nat.cast_nonneg n⟩), g.2.zero]

/-- The chosen witness. -/
noncomputable def devStep {X : Type*} [TopologicalSpace X] [T2Space X] (H : IsLocallyArc X)
    (x₀ : X) (n : ℕ) (g : { g : ℝ → X // IsArcOn x₀ n g }) :
    { β : ℝ → X // IsArcOnExt x₀ n β g.1 } :=
  ⟨Classical.choose (devExistsStep H x₀ n g), Classical.choose_spec (devExistsStep H x₀ n g)⟩

/-- The nested sequence of arcs on `Icc (-n) n`. -/
noncomputable def dev {X : Type*} [TopologicalSpace X] [T2Space X] (H : IsLocallyArc X) (x₀ : X) :
    ∀ n : ℕ, { g : ℝ → X // IsArcOn x₀ n g }
  | 0 => ⟨fun _ => x₀, ⟨continuousOn_const, by
      intro s hs t ht _
      simp only [Nat.cast_zero, neg_zero, Set.mem_Icc] at hs ht
      rw [le_antisymm hs.2 hs.1, le_antisymm ht.2 ht.1], rfl⟩⟩
  | (n+1) => ⟨(devStep H x₀ n (dev H x₀ n)).1,
      { cont := by
          convert (devStep H x₀ n (dev H x₀ n)).2.cont using 2 <;> push_cast <;> ring
        inj := by
          convert (devStep H x₀ n (dev H x₀ n)).2.inj using 2 <;> push_cast <;> ring
        zero := (devStep H x₀ n (dev H x₀ n)).2.zero }⟩

lemma dev_one_step {X : Type*} [TopologicalSpace X] [T2Space X] (H : IsLocallyArc X) (x₀ : X)
    (n : ℕ) : EqOn (dev H x₀ (n+1)).1 (dev H x₀ n).1 (Icc (-(n:ℝ)) n) :=
  (devStep H x₀ n (dev H x₀ n)).2.agree

lemma dev_agree {X : Type*} [TopologicalSpace X] [T2Space X] (H : IsLocallyArc X) (x₀ : X) :
    ∀ n m : ℕ, n ≤ m → EqOn (dev H x₀ m).1 (dev H x₀ n).1 (Icc (-(n:ℝ)) n) := by
  intro n m
  induction m with
  | zero =>
      intro hn
      have : n = 0 := Nat.le_zero.mp hn
      subst this
      exact fun _ _ => rfl
  | succ m ih =>
      intro hn
      rcases Nat.lt_or_eq_of_le hn with hlt | rfl
      · have hle : n ≤ m := Nat.le_of_lt_succ hlt
        have h1 := dev_one_step H x₀ m
        have h2 := ih hle
        intro t ht
        have ht' : t ∈ Icc (-(m:ℝ)) m := by
          simp only [Set.mem_Icc] at ht ⊢
          have hcast : (n:ℝ) ≤ (m:ℝ) := by exact_mod_cast hle
          constructor <;> linarith [ht.1, ht.2]
        rw [h1 ht', h2 ht]
      · exact fun _ _ => rfl

/-- The global arc on `ℝ`. -/
noncomputable def devMap {X : Type*} [TopologicalSpace X] [T2Space X] (H : IsLocallyArc X)
    (x₀ : X) : ℝ → X :=
  fun t => (dev H x₀ ⌈|t|⌉₊).1 t

lemma devMap_eq {X : Type*} [TopologicalSpace X] [T2Space X] (H : IsLocallyArc X) (x₀ : X)
    {t : ℝ} {n : ℕ} (hn : |t| ≤ (n : ℝ)) : devMap H x₀ t = (dev H x₀ n).1 t := by
  have h1 : ⌈|t|⌉₊ ≤ n := Nat.ceil_le.mpr hn
  have h2 : EqOn (dev H x₀ n).1 (dev H x₀ ⌈|t|⌉₊).1 (Icc (-(⌈|t|⌉₊ : ℝ)) ⌈|t|⌉₊) :=
    dev_agree H x₀ ⌈|t|⌉₊ n h1
  have hmem : t ∈ Icc (-(⌈|t|⌉₊ : ℝ)) ⌈|t|⌉₊ := by
    simp only [Set.mem_Icc]
    exact ⟨by linarith [neg_abs_le t, Nat.le_ceil |t|], by linarith [le_abs_self t, Nat.le_ceil |t|]⟩
  show (dev H x₀ ⌈|t|⌉₊).1 t = (dev H x₀ n).1 t
  exact (h2 hmem).symm

lemma devMap_zero {X : Type*} [TopologicalSpace X] [T2Space X] (H : IsLocallyArc X) (x₀ : X) :
    devMap H x₀ 0 = x₀ := by
  have h := devMap_eq H x₀ (t := 0) (n := 0) (by simp)
  rw [h]
  exact (dev H x₀ 0).2.zero

theorem devMap_continuous {X : Type*} [TopologicalSpace X] [T2Space X] (H : IsLocallyArc X)
    (x₀ : X) : Continuous (devMap H x₀) := by
  rw [continuous_iff_continuousAt]
  intro t
  set n : ℕ := ⌈|t|⌉₊ + 1 with hn
  have ht_lt : |t| < (n : ℝ) := by
    have h := Nat.le_ceil |t|
    simp only [hn, Nat.cast_add, Nat.cast_one]
    linarith
  have hmem : Ioo (-(n:ℝ)) n ∈ 𝓝 t :=
    Ioo_mem_nhds (by linarith [neg_abs_le t, ht_lt]) (by linarith [le_abs_self t, ht_lt])
  have hmemI : Icc (-(n:ℝ)) n ∈ 𝓝 t :=
    Filter.mem_of_superset hmem Ioo_subset_Icc_self
  have hcontN : ContinuousAt (dev H x₀ n).1 t := (dev H x₀ n).2.cont.continuousAt hmemI
  have heq : devMap H x₀ =ᶠ[𝓝 t] (dev H x₀ n).1 := by
    filter_upwards [hmem] with s hs
    exact devMap_eq H x₀ (le_of_lt (abs_lt.mpr ⟨hs.1, hs.2⟩))
  exact hcontN.congr_of_eventuallyEq heq

theorem devMap_injective {X : Type*} [TopologicalSpace X] [T2Space X] (H : IsLocallyArc X)
    (x₀ : X) : Function.Injective (devMap H x₀) := by
  intro s t hst
  set n : ℕ := max ⌈|s|⌉₊ ⌈|t|⌉₊ with hn
  have hs : |s| ≤ (n : ℝ) := le_trans (Nat.le_ceil |s|) (by exact_mod_cast le_max_left _ _)
  have ht : |t| ≤ (n : ℝ) := le_trans (Nat.le_ceil |t|) (by exact_mod_cast le_max_right _ _)
  have h1 := devMap_eq H x₀ hs
  have h2 := devMap_eq H x₀ ht
  have hst' : (dev H x₀ n).1 s = (dev H x₀ n).1 t := by rw [← h1, ← h2, hst]
  have hs' : s ∈ Icc (-(n:ℝ)) n := by
    simp only [Set.mem_Icc]; exact ⟨by linarith [neg_abs_le s, hs], by linarith [le_abs_self s, hs]⟩
  have ht' : t ∈ Icc (-(n:ℝ)) n := by
    simp only [Set.mem_Icc]; exact ⟨by linarith [neg_abs_le t, ht], by linarith [le_abs_self t, ht]⟩
  exact (dev H x₀ n).2.inj hs' ht' hst'

/-- **A locally-arc Hausdorff space contains an embedded copy of `ℝ`.** -/
theorem exists_continuous_injective_real {X : Type*} [TopologicalSpace X] [T2Space X]
    (H : IsLocallyArc X) (x₀ : X) :
    ∃ α : ℝ → X, Continuous α ∧ Function.Injective α ∧ α 0 = x₀ :=
  ⟨devMap H x₀, devMap_continuous H x₀, devMap_injective H x₀, devMap_zero H x₀⟩

end

end Work.Smooth.SphereJordan.LocalArc
