import Mathlib
import Submission.Work.Analysis.Probability.greedyTime_mono
import Submission.Commons.Analysis.Probability.lepingle_variation_sigma_finite_ls

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.Analysis.Probability

/-! ## Pathwise facts about the greedy chain -/

theorem nextJump_eq_find {x : ℕ → ℝ} {δ : ℝ} {a : ℕ}
    (h : ∃ n : ℕ, a < n ∧ δ < |x n - x a|) :
    nextJump x δ a = ((Nat.find h : ℕ) : ℕ∞) := by
  classical
  show dite (∃ n : ℕ, a < n ∧ δ < |x n - x a|)
    (fun h => ((Nat.find h : ℕ) : ℕ∞)) (fun _ => ⊤) = _
  rw [dif_pos h]

theorem nextJump_eq_top {x : ℕ → ℝ} {δ : ℝ} {a : ℕ}
    (h : ¬ ∃ n : ℕ, a < n ∧ δ < |x n - x a|) : nextJump x δ a = ⊤ := by
  classical
  show dite (∃ n : ℕ, a < n ∧ δ < |x n - x a|)
    (fun h => ((Nat.find h : ℕ) : ℕ∞)) (fun _ => ⊤) = _
  rw [dif_neg h]

theorem greedyTime_succ_eq (x : ℕ → ℝ) (δ : ℝ) (k : ℕ) :
    greedyTime x δ (k+1) =
      (if greedyTime x δ k < ⊤ then nextJump x δ (greedyTime x δ k).toNat else ⊤) := rfl

theorem greedyTime_succ_eq_top {x : ℕ → ℝ} {δ : ℝ} {k : ℕ}
    (h : greedyTime x δ k = ⊤) : greedyTime x δ (k+1) = ⊤ := by
  have hk : ¬ (greedyTime x δ k < ⊤) := by rw [h]; exact not_lt.mpr le_rfl
  rw [greedyTime_succ_eq, if_neg hk]

/-- For a finite `ℕ∞`-value the default-unwrapping `untopA` and the truncating `toNat` agree. -/
theorem untopA_eq_toNat_of_lt_top {a : ℕ∞} (h : a < ⊤) : a.untopA = a.toNat := by
  cases hval : a with
  | top => rw [hval] at h; exact absurd h (lt_irrefl ⊤)
  | coe n => rfl

theorem greedyTime_succ_jump (x : ℕ → ℝ) (δ : ℝ) (k : ℕ)
    (h : greedyTime x δ (k+1) < ⊤) :
    δ < |x (greedyTime x δ (k+1)).toNat - x (greedyTime x δ k).toNat| := by
  classical
  have hk : greedyTime x δ k < ⊤ := by
    by_contra hc
    rw [not_lt] at hc
    have htop : greedyTime x δ k = ⊤ := le_antisymm le_top hc
    rw [greedyTime_succ_eq_top htop] at h
    exact absurd h (lt_irrefl ⊤)
  have hex : ∃ n : ℕ, (greedyTime x δ k).toNat < n ∧
      δ < |x n - x (greedyTime x δ k).toNat| := by
    by_contra hc
    have htop : nextJump x δ (greedyTime x δ k).toNat = ⊤ := nextJump_eq_top hc
    rw [greedyTime_succ_eq, if_pos hk, htop] at h
    exact absurd h (lt_irrefl ⊤)
  have hval : greedyTime x δ (k+1) = ((Nat.find hex : ℕ) : ℕ∞) := by
    rw [greedyTime_succ_eq, if_pos hk, nextJump_eq_find hex]
  have htoNat : (greedyTime x δ (k+1)).toNat = Nat.find hex := by
    rw [hval, ENat.toNat_natCast]
  rw [htoNat]
  exact (Nat.find_spec hex).2

/-- The `k`-th greedy time is finite as soon as the chain has more than `y` jumps. -/
theorem greedyTime_lt_top_of_lt_greedyJumps {x : ℕ → ℝ} {δ y : ℝ} (hy : 0 < y)
    (h : ENNReal.ofReal y < greedyJumps x δ) :
    greedyTime x δ (⌊y⌋₊ + 1) < ⊤ := by
  classical
  by_contra hcon
  rw [not_lt] at hcon
  have htop : greedyTime x δ (⌊y⌋₊ + 1) = ⊤ := le_antisymm le_top hcon
  have hmono : ∀ m, ⌊y⌋₊ + 1 ≤ m → greedyTime x δ m = ⊤ := by
    intro m hm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    induction d with
    | zero => simpa using htop
    | succ d ih =>
        rw [show ⌊y⌋₊ + 1 + (d + 1) = (⌊y⌋₊ + 1 + d) + 1 from by omega]
        exact greedyTime_succ_eq_top (ih (by omega))
  have hle : greedyJumps x δ ≤ ENNReal.ofReal y := by
    refine iSup_le fun k => iSup_le fun hk => ?_
    have hk' : k + 1 ≤ ⌊y⌋₊ := by
      by_contra hc
      have hc' : ⌊y⌋₊ + 1 ≤ k + 1 := Nat.succ_le_of_lt (not_le.mp hc)
      have h1 := hmono (k+1) hc'
      rw [h1] at hk
      exact absurd hk (lt_irrefl ⊤)
    calc ((k + 1 : ℕ) : ℝ≥0∞) ≤ ((⌊y⌋₊ : ℕ) : ℝ≥0∞) := by exact_mod_cast hk'
      _ = ENNReal.ofReal (⌊y⌋₊ : ℝ) := (ENNReal.ofReal_natCast _).symm
      _ ≤ ENNReal.ofReal y := ENNReal.ofReal_le_ofReal (Nat.floor_le hy.le)
  exact absurd h (not_lt.mpr hle)

/-- A path that is constant has no greedy jumps (for `δ ≥ 0`). -/
theorem greedyJumps_eq_zero_of_const {δ : ℝ} (hδ : 0 ≤ δ) {x : ℕ → ℝ}
    (h : ∀ n, x n = x 0) : greedyJumps x δ = 0 := by
  classical
  have hnext : ∀ a, nextJump x δ a = ⊤ := by
    intro a
    apply nextJump_eq_top
    rintro ⟨n, hn, hlt⟩
    rw [h n, h a] at hlt
    simp only [sub_self, abs_zero] at hlt
    linarith
  have htop : ∀ k, greedyTime x δ k = ⊤ ∨ k = 0 := by
    intro k
    rcases k with _ | k
    · exact Or.inr rfl
    · left
      induction k with
      | zero =>
          rw [show (0 + 1) = 1 from rfl, greedyTime_succ_eq]
          rw [if_pos (by rw [show greedyTime x δ 0 = 0 from rfl]; exact ENat.natCast_lt_top 0)]
          exact hnext 0
      | succ k ih => exact greedyTime_succ_eq_top ih
  refine le_antisymm ?_ bot_le
  refine iSup_le fun k => iSup_le fun hk => ?_
  rcases htop (k+1) with h1 | h1
  · rw [h1] at hk
    exact absurd hk (lt_irrefl ⊤)
  · exact absurd h1 (by omega)

/-! ## The greedy times are stopping times -/

/-- Measurability of the absolute value, phrased with a non-instance σ-algebra so that
the elaborator does not pick up the ambient one. -/
lemma Measurable.abs' {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω} {f : Ω → ℝ}
    (h : Measurable[m] f) : Measurable[m] (fun ω => |f ω|) :=
  (continuous_abs.measurable).comp h

/-- Characterization of `nextJump x δ a ≤ n`. -/
theorem nextJump_le_iff {x : ℕ → ℝ} {δ : ℝ} {a n : ℕ} :
    nextJump x δ a ≤ (n : ℕ∞) ↔
      ∃ j : ℕ, a < j ∧ j ≤ n ∧ δ < |x j - x a| ∧ ∀ i, a < i → i < j → |x i - x a| ≤ δ := by
  constructor
  · intro h
    have hex : ∃ m : ℕ, a < m ∧ δ < |x m - x a| := by
      by_contra hc
      rw [nextJump_eq_top hc] at h
      exact absurd h (not_le.mpr (ENat.natCast_lt_top n))
    rw [nextJump_eq_find hex, ENat.natCast_le_natCast] at h
    exact ⟨Nat.find hex, (Nat.find_spec hex).1, h, (Nat.find_spec hex).2,
      fun i hai hij => le_of_not_gt fun hgt => Nat.find_min hex hij ⟨hai, hgt⟩⟩
  · rintro ⟨j, haj, hjn, hjump, hfirst⟩
    have hex : ∃ m : ℕ, a < m ∧ δ < |x m - x a| := ⟨j, haj, hjump⟩
    rw [nextJump_eq_find hex, ENat.natCast_le_natCast]
    exact le_trans (Nat.find_min' hex ⟨haj, hjump⟩) hjn

/-- Characterization of `nextJump x δ a = m` (for `m : ℕ`). -/
theorem nextJump_eq_iff {x : ℕ → ℝ} {δ : ℝ} {a m : ℕ} :
    nextJump x δ a = (m : ℕ∞) ↔
      a < m ∧ δ < |x m - x a| ∧ ∀ i, a < i → i < m → |x i - x a| ≤ δ := by
  constructor
  · intro h
    have hle : nextJump x δ a ≤ (m : ℕ∞) := le_of_eq h
    obtain ⟨j, haj, hjm, hjump, hfirst⟩ := nextJump_le_iff.mp hle
    have hjm' : j = m := by
      by_contra hne
      have hjlt : j < m := lt_of_le_of_ne hjm hne
      have hex : ∃ i, a < i ∧ δ < |x i - x a| := ⟨j, haj, hjump⟩
      rw [nextJump_eq_find hex, ENat.natCast_inj] at h
      have := Nat.find_min' hex ⟨haj, hjump⟩
      omega
    subst hjm'
    exact ⟨haj, hjump, hfirst⟩
  · rintro ⟨ham, hjump, hfirst⟩
    have hle : nextJump x δ a ≤ (m : ℕ∞) :=
      nextJump_le_iff.mpr ⟨m, ham, le_rfl, hjump, hfirst⟩
    have hlt : ¬ (nextJump x δ a ≤ ((m - 1 : ℕ) : ℕ∞)) := by
      intro hc
      obtain ⟨j, haj, hjm, hjump', -⟩ := nextJump_le_iff.mp hc
      refine absurd hjump' (not_lt.mpr (hfirst j haj ?_))
      omega
    cases hval : nextJump x δ a with
    | top => rw [hval] at hle; exact absurd hle (not_le.mpr (ENat.natCast_lt_top m))
    | coe k =>
        rw [hval] at hle hlt
        have hle' : k ≤ m := by exact_mod_cast hle
        have hk : k = m := by
          by_contra hne
          have hlt' : k ≤ m - 1 := Nat.le_sub_one_of_lt (lt_of_le_of_ne hle' hne)
          exact hlt (by exact_mod_cast hlt')
        rw [hk]

/-- Auxiliary: a `k`-th greedy time is a stopping time (induction in `k`). -/
theorem isStoppingTime_greedyTime {Ω : Type*} [MeasurableSpace Ω]
    {ℱ : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›} {G : ℕ → Ω → ℝ}
    (hG : MeasureTheory.StronglyAdapted ℱ G) (δ : ℝ) (k : ℕ) :
    MeasureTheory.IsStoppingTime ℱ (fun ω => greedyTime (fun j => G j ω) δ k) := by
  classical
  have hGm : ∀ {i m : ℕ}, i ≤ m → Measurable[ℱ m] (fun ω => G i ω) := fun h =>
    (hG _).measurable.mono (ℱ.mono h) le_rfl
  have key : ∀ k m : ℕ,
      MeasurableSet[ℱ m] {ω | greedyTime (fun j => G j ω) δ k = (m : ℕ∞)} := by
    intro k
    induction k with
    | zero =>
        intro m
        rcases m with _ | m
        · have h1 : {ω : Ω | greedyTime (fun j => G j ω) δ 0 = ((0 : ℕ) : ℕ∞)} = Set.univ := by
            ext ω
            simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
            rfl
          rw [h1]
          exact MeasurableSet.univ
        · have h1 : {ω : Ω | greedyTime (fun j => G j ω) δ 0 = ((m + 1 : ℕ) : ℕ∞)} = ∅ := by
            ext ω
            simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
            intro hcon
            have h2 : (0 : ℕ) = m + 1 := by
              have h3 : (greedyTime (fun j => G j ω) δ 0).toNat = 0 := rfl
              have h4 := congrArg ENat.toNat hcon
              rw [h3, ENat.toNat_natCast] at h4
              exact h4
            omega
          rw [h1]
          simp
    | succ k ih =>
        intro m
        have hset : {ω | greedyTime (fun j => G j ω) δ (k+1) = (m : ℕ∞)}
            = ⋃ a ∈ Finset.range m,
                ({ω | greedyTime (fun j => G j ω) δ k = (a : ℕ∞)}
                  ∩ {ω | nextJump (fun j => G j ω) δ a = (m : ℕ∞)}) := by
          ext ω
          simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, Set.mem_inter_iff,
            Set.mem_setOf_eq]
          constructor
          · intro hω
            have hlt : greedyTime (fun j => G j ω) δ k < ⊤ := by
              by_contra hc
              rw [not_lt] at hc
              have htop : greedyTime (fun j => G j ω) δ k = ⊤ := le_antisymm le_top hc
              rw [greedyTime_succ_eq_top htop] at hω
              exact absurd hω (ENat.top_ne_coe m)
            have hstep : greedyTime (fun j => G j ω) δ (k+1)
                = nextJump (fun j => G j ω) δ (greedyTime (fun j => G j ω) δ k).toNat := by
              rw [greedyTime_succ_eq, if_pos hlt]
            rw [hstep] at hω
            exact ⟨(greedyTime (fun j => G j ω) δ k).toNat, (nextJump_eq_iff.mp hω).1,
              (ENat.natCast_toNat (ne_of_lt hlt)).symm, hω⟩
          · rintro ⟨a, ham, ha, hnext⟩
            have hlt : greedyTime (fun j => G j ω) δ k < ⊤ := by
              rw [ha]; exact ENat.natCast_lt_top a
            have htoNat : (greedyTime (fun j => G j ω) δ k).toNat = a := by
              rw [ha]; exact ENat.toNat_natCast a
            rw [greedyTime_succ_eq, if_pos hlt, htoNat]
            exact hnext
        rw [hset]
        refine MeasurableSet.biUnion (Finset.countable_toSet _) fun a ha => ?_
        have ham : a < m := Finset.mem_range.mp ha
        refine MeasurableSet.inter (ℱ.mono ham.le _ (ih a)) ?_
        have hset2 : {ω | nextJump (fun j => G j ω) δ a = (m : ℕ∞)}
            = {ω | δ < |G m ω - G a ω|} ∩ ⋂ i ∈ Finset.Ioo a m, {ω | |G i ω - G a ω| ≤ δ} := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_Ioo]
          rw [nextJump_eq_iff]
          constructor
          · rintro ⟨-, h1, h2⟩
            exact ⟨h1, fun i hi => h2 i hi.1 hi.2⟩
          · rintro ⟨h1, h2⟩
            exact ⟨ham, h1, fun i hai him => h2 i ⟨hai, him⟩⟩
        rw [hset2]
        refine MeasurableSet.inter ?_ ?_
        · have h1 : Measurable[ℱ m] (fun ω => G m ω) := hGm le_rfl
          have h2 : Measurable[ℱ m] (fun ω => G a ω) := hGm ham.le
          have h3 : Measurable[ℱ m] (fun ω => |G m ω - G a ω|) := Measurable.abs' (h1.sub h2)
          exact h3 measurableSet_Ioi
        · refine MeasurableSet.biInter (Finset.countable_toSet _) fun i hi => ?_
          have him : i < m := (Finset.mem_Ioo.mp hi).2
          have h1 : Measurable[ℱ m] (fun ω => G i ω) := hGm him.le
          have h2 : Measurable[ℱ m] (fun ω => G a ω) := hGm ham.le
          have h3 : Measurable[ℱ m] (fun ω => |G i ω - G a ω|) := Measurable.abs' (h1.sub h2)
          exact h3 measurableSet_Iic
  intro n
  show MeasurableSet[ℱ n] {ω | greedyTime (fun j => G j ω) δ k ≤ (n : ℕ∞)}
  have hset3 : {ω | greedyTime (fun j => G j ω) δ k ≤ (n : ℕ∞)}
      = ⋃ m ∈ Finset.range (n+1), {ω | greedyTime (fun j => G j ω) δ k = (m : ℕ∞)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range]
    constructor
    · intro hω
      cases hval : greedyTime (fun j => G j ω) δ k with
      | top => rw [hval] at hω; exact absurd hω (not_le.mpr (ENat.natCast_lt_top n))
      | coe m =>
          rw [hval] at hω
          rw [ENat.natCast_le_natCast] at hω
          exact ⟨m, Nat.lt_succ_of_le hω, rfl⟩
    · rintro ⟨m, hm, hω⟩
      rw [hω]
      exact_mod_cast (Nat.le_of_lt_succ hm)
  rw [hset3]
  exact MeasurableSet.biUnion (Finset.countable_toSet _) fun m hm =>
    ℱ.mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) _ (key k m)

/-! ## Doob's weak `(1,1)` maximal inequality for `L¹`-bounded martingales -/

/-- Doob's weak `(1,1)` maximal inequality for an arbitrary martingale `H` with
`∀ n, ∫ |H n| ≤ B` on a σ-finite filtered measure space. -/
theorem martingale_max_weak {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.SigmaFinite μ] {ℱ : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›}
    [MeasureTheory.SigmaFiniteFiltration μ ℱ] {H : ℕ → Ω → ℝ}
    (hH : MeasureTheory.Martingale H ℱ μ) {B M : ℝ} (hM : 0 < M)
    (hB : ∀ n, ∫ ω, |H n ω| ∂μ ≤ B) :
    μ {ω | ENNReal.ofReal M < ⨆ n, ‖H n ω‖ₑ} ≤ ENNReal.ofReal (B / M) := by
  classical
  have hsub : Submartingale (fun n ω => ‖H n ω‖) ℱ μ := by
    refine ⟨fun n => (hH.stronglyAdapted n).norm, ?_, ?_⟩
    · intro i j hij
      filter_upwards [norm_condExp_le (μ := μ) (m := ℱ i) (H j),
        hH.condExp_ae_eq hij] with ω h1 h2
      calc ‖H i ω‖ = ‖μ[H j | ℱ i] ω‖ := by rw [h2]
        _ ≤ μ[fun ω => ‖H j ω‖ | ℱ i] ω := h1
    · intro n; exact (hH.integrable n).norm
  have hset : {ω | ENNReal.ofReal M < ⨆ n : ℕ, ‖H n ω‖ₑ}
      = ⋃ N, {ω | M < partialSups (fun n ω => ‖H n ω‖) N ω} := by
    have hps : ∀ N ω, M < partialSups (fun n ω => ‖H n ω‖) N ω ↔
        ∃ j ≤ N, M < ‖H j ω‖ := by
      intro N ω
      rw [partialSups_apply, Finset.sup'_apply, Finset.lt_sup'_iff]
      simp only [Finset.mem_Iic]
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hps]
    constructor
    · intro hω
      rw [lt_iSup_iff] at hω
      obtain ⟨n, hn⟩ := hω
      have hn' : M < ‖H n ω‖ := by
        rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hM.le] at hn
        simpa [Real.norm_eq_abs] using hn
      exact ⟨n, n, le_rfl, hn'⟩
    · rintro ⟨N, j, hj, hlt⟩
      rw [lt_iSup_iff]
      refine ⟨j, ?_⟩
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hM.le]
      simpa [Real.norm_eq_abs] using hlt
  have hbound : ∀ N, μ {ω | M < partialSups (fun n ω => ‖H n ω‖) N ω}
      ≤ ENNReal.ofReal (B / M) := by
    intro N
    set S : Set Ω := {ω | M < partialSups (fun n ω => ‖H n ω‖) N ω} with hSdef
    have h1 : ENNReal.ofReal M * μ S
        ≤ ∫⁻ ω in S, ENNReal.ofReal (‖H N ω‖) ∂μ :=
      SFDoob.submartingale_maximal_weak (μ := μ) (𝒢 := ℱ)
        (f := fun n ω => ‖H n ω‖) hsub (fun n ω => norm_nonneg _) hM
    have h2 : ∫⁻ ω in S, ENNReal.ofReal (‖H N ω‖) ∂μ ≤ ENNReal.ofReal B := by
      refine le_trans (setLIntegral_le_lintegral _ _) ?_
      have h3 : ∫⁻ ω, ENNReal.ofReal (‖H N ω‖) ∂μ = ENNReal.ofReal (∫ ω, ‖H N ω‖ ∂μ) := by
        have hcongr : (fun ω => ENNReal.ofReal (‖H N ω‖)) = fun ω => ‖H N ω‖ₑ := by
          funext ω
          rw [Real.enorm_eq_ofReal_abs]
          exact congrArg ENNReal.ofReal (Real.norm_eq_abs _)
        rw [hcongr]
        exact (MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm (μ := μ) (f := H N)
          (hH.integrable N)).symm
      rw [h3]
      refine ENNReal.ofReal_le_ofReal ?_
      calc ∫ ω, ‖H N ω‖ ∂μ = ∫ ω, |H N ω| ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
            exact Real.norm_eq_abs _
        _ ≤ B := hB N
    have h6 : ENNReal.ofReal M * μ S ≤ ENNReal.ofReal B := le_trans h1 h2
    have h4 : μ S ≤ ENNReal.ofReal (B / M) := by
      calc μ S = 1 * μ S := (one_mul _).symm
        _ = ((ENNReal.ofReal M)⁻¹ * ENNReal.ofReal M) * μ S := by
              rw [ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hM) ENNReal.ofReal_ne_top]
        _ = (ENNReal.ofReal M)⁻¹ * (ENNReal.ofReal M * μ S) := mul_assoc _ _ _
        _ ≤ (ENNReal.ofReal M)⁻¹ * ENNReal.ofReal B := mul_le_mul_of_nonneg_left h6 bot_le
        _ = ENNReal.ofReal (B / M) := by
              rw [ENNReal.ofReal_div_of_pos hM, ENNReal.div_eq_inv_mul]
    exact h4
  rw [hset]
  have hmono : Monotone (fun N : ℕ =>
      {ω | M < partialSups (fun n ω => ‖H n ω‖) N ω}) := by
    intro i j hij ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact lt_of_lt_of_le hω (partialSups_monotone (fun n ω => ‖H n ω‖) hij ω)
  rw [Monotone.measure_iUnion hmono]
  exact iSup_le hbound

end Work.Analysis.Probability
