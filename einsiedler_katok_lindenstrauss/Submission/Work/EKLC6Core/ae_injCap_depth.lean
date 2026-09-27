import Mathlib
import Submission.Work.EKLC6Core.InjRadius
import Submission.Work.EKLC6Core.injCap_aDiag_geometric
import Submission.Work.EKLComp.prove_Birkhoff
import Submission.Work.EKLComp.isClosed_exists_smul_eq_of_isCompact
import Submission.Work.EKLProd.sl3EntryBox_compact
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLContract.Lemmas.V_open_one

/-!
# `Work.EKLC6Core.ae_injCap_depth`

For an `aDiag t`-invariant probability measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, for `μ`-a.e. `x`
and every `δ > 0`, the capped injectivity radius `injCap` decays slower than `e^{-δn}` along the
orbit: `injCap (φ^n x) ≥ e^{-δn}` for all large `n`.

## Proof

Write `φ(x) = -log (injCap x) ≥ log 2 > 0` and `T x = aDiag t • x`.  The one-step geometric
bounds (`injCap_aDiag_geometric`, applied to `t` and to `-t`, at `n = 1`) give

  `c₂ λ injCap x ≤ injCap (T x) ≤ (c₂' λ')⁻¹ injCap x`,

so the cocycle `g := φ ∘ T - φ` is *bounded*.  Since `T` is measure preserving (and a
homeomorphism, hence `MeasurableEmbedding`), the truncated functions `φ_M = min (φ, M)` satisfy
`∫ (φ_M ∘ T) = ∫ φ_M`; dominated convergence (the truncations are uniformly close, with
`|g_M| ≤ ‖g‖_∞`) gives `∫ g = 0`.

The Birkhoff ergodic theorem (`Work.EKLComp.birkhoff_all`) then gives
`birkA T g n x → E[g | invariants T]`.  Since `birkA T g n x = n⁻¹ (φ (T^n x) - φ x)` and
`φ ≥ 0`, the limit is `≥ 0` a.e., while its integral is `∫ g = 0`; hence the limit vanishes a.e.
and `n⁻¹ φ (T^n x) → 0` a.e., i.e. `-log (injCap (T^n x)) < δ n` eventually, which is the claim.
-/

namespace Work.EKLC6Core

open MeasureTheory Filter Topology
open scoped ENNReal Pointwise
open Work.EKLContract

noncomputable section

/-! ## Measurability of `InjAt` and `injCap` -/

/-- The closed entrywise box of radius `s` around the identity. -/
def eBox (s : ℝ) : Set SL3 :=
  {g : SL3 | ∀ i j,
    |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ s}

theorem isCompact_eBox (s : ℝ) : IsCompact (eBox s) := by
  have h : eBox s = {g : SL3 | ∀ i j,
      (1 : Matrix (Fin 3) (Fin 3) ℝ) i j - s ≤ (g : Matrix (Fin 3) (Fin 3) ℝ) i j ∧
      (g : Matrix (Fin 3) (Fin 3) ℝ) i j ≤ (1 : Matrix (Fin 3) (Fin 3) ℝ) i j + s} := by
    ext g
    constructor
    · intro h i j
      have h1 := abs_le.mp (h i j)
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
    · intro h i j
      have h1 := h i j
      exact abs_le.mpr ⟨by linarith [h1.1], by linarith [h1.2]⟩
  rw [h]
  exact Work.EKLProd.sl3EntryBox_compact _ _

theorem eBox_subset_V {s t : ℝ} (h : s < t) : eBox s ⊆ V t := by
  intro g hg i j
  have h1 := hg i j
  rw [abs_le] at h1
  rw [abs_lt]
  exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

theorem V_subset_eBox (s : ℝ) : V s ⊆ eBox s := by
  intro g hg i j
  have h1 := hg i j
  rw [abs_lt] at h1
  rw [abs_le]
  exact ⟨le_of_lt h1.1, le_of_lt h1.2⟩

/-- `V ρ` is the increasing union of the `V (ρ - 1/(m+1))`. -/
theorem V_eq_iUnion_V_sub {ρ : ℝ} (hρ : 0 < ρ) :
    V ρ = ⋃ m : ℕ, V (ρ - 1 / ((m : ℝ) + 1)) := by
  ext g
  simp only [Set.mem_iUnion]
  constructor
  · intro hg
    set M : ℝ := (Finset.univ : Finset (Fin 3 × Fin 3)).sup'
      ⟨(0, 0), Finset.mem_univ _⟩
      (fun p : Fin 3 × Fin 3 => |(g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) with hM
    have hMlt : M < ρ := by
      rw [hM]
      exact (Finset.sup'_lt_iff _).mpr (fun p _ => hg p.1 p.2)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hMlt)
    refine ⟨m, fun i j => ?_⟩
    have hle : |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ M := by
      rw [hM]
      exact Finset.le_sup'
        (f := fun p : Fin 3 × Fin 3 => |(g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) (Finset.mem_univ (i, j))
    linarith
  · rintro ⟨m, hg⟩ i j
    have hp : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have := hg i j
    linarith

/-- `InjAt x ρ` iff the stabiliser of `x` meets `(V ρ)⁻¹ * V ρ` only in the identity. -/
theorem injAt_iff_forall_mem_inv_mul {x : X3} {ρ : ℝ} :
    InjAt x ρ ↔ ∀ w ∈ (V ρ)⁻¹ * V ρ, w • x = x → w = 1 := by
  constructor
  · intro h w hw hwx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hw
    have ha' : a⁻¹ ∈ V ρ := Set.mem_inv.mp ha
    have hb' : b • x = a⁻¹ • x := by
      have h2 : a • (b • x) = x := by
        have h3 := hwx
        rwa [mul_smul] at h3
      calc b • x = (a⁻¹ * a) • (b • x) := by rw [inv_mul_cancel, one_smul]
        _ = a⁻¹ • (a • (b • x)) := by rw [mul_smul]
        _ = a⁻¹ • x := by rw [h2]
    have hb1 : b = a⁻¹ := h b a⁻¹ hb ha' hb'
    rw [hb1, mul_inv_cancel]
  · intro h v₁ v₂ hv₁ hv₂ heq
    have hw : v₂⁻¹ * v₁ ∈ (V ρ)⁻¹ * V ρ := by
      refine Set.mul_mem_mul ?_ hv₁
      rw [Set.mem_inv]
      simpa using hv₂
    have hwx : (v₂⁻¹ * v₁) • x = x := by
      rw [mul_smul, heq, ← mul_smul, inv_mul_cancel, one_smul]
    have h1 := h _ hw hwx
    rw [inv_mul_eq_one] at h1
    exact h1.symm

/-- The set of points fixed by some element of a compact set `K`, other than `1`, is measurable. -/
theorem measurableSet_exists_fix_of_isCompact {K : Set SL3} (hK : IsCompact K) :
    MeasurableSet {x : X3 | ∃ g ∈ K, g ≠ 1 ∧ g • x = x} := by
  have hset : {x : X3 | ∃ g ∈ K, g ≠ 1 ∧ g • x = x} =
      ⋃ n : ℕ, {x : X3 | ∃ g ∈ K, g ∉ V (1 / ((n : ℝ) + 1)) ∧ g • x = x} := by
    ext x
    constructor
    · rintro ⟨g, hgK, hg1, hgx⟩
      have hne : (g : Matrix (Fin 3) (Fin 3) ℝ) ≠ 1 := by
        intro h; exact hg1 (Subtype.ext h)
      obtain ⟨i, j, hij⟩ : ∃ i j, (g : Matrix (Fin 3) (Fin 3) ℝ) i j
          ≠ (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
        by_contra h; push Not at h
        exact hne (funext fun i => funext fun j => h i j)
      have hpos : 0 < |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := abs_pos.mpr (sub_ne_zero.mpr hij)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      refine Set.mem_iUnion.mpr ⟨n, g, hgK, ?_, hgx⟩
      intro hmem
      exact absurd (hmem i j) (not_lt.mpr (le_of_lt hn))
    · intro hx
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      obtain ⟨g, hgK, hgV, hgx⟩ := hn
      refine ⟨g, hgK, ?_, hgx⟩
      intro hg1
      rw [hg1] at hgV
      exact hgV ((Work.EKLContract.Lemmas.V_open_one _ (by positivity)).2)
  rw [hset]
  refine MeasurableSet.iUnion fun n => ?_
  have hopen : IsOpen (V (1 / ((n : ℝ) + 1))) :=
    (Work.EKLContract.Lemmas.V_open_one _ (by positivity)).1
  have hKc : IsCompact (K ∩ (V (1 / ((n : ℝ) + 1)))ᶜ) :=
    hK.of_isClosed_subset (hK.isClosed.inter hopen.isClosed_compl) Set.inter_subset_left
  have hclosed := Work.EKLComp.isClosed_exists_smul_eq_of_isCompact
    (K ∩ (V (1 / ((n : ℝ) + 1)))ᶜ) hKc
  have heq : {x : X3 | ∃ g ∈ K, g ∉ V (1 / ((n : ℝ) + 1)) ∧ g • x = x} =
      (fun x : X3 => (x, x)) ⁻¹'
        {p : X3 × X3 | ∃ g ∈ K ∩ (V (1 / ((n : ℝ) + 1)))ᶜ, g • p.1 = p.2} := by
    ext x; constructor
    · rintro ⟨g, hgK, hgV, hgx⟩; exact ⟨g, ⟨hgK, hgV⟩, hgx⟩
    · rintro ⟨g, ⟨hgK, hgV⟩, hgx⟩; exact ⟨g, hgK, hgV, hgx⟩
  rw [heq]
  exact (hclosed.preimage (continuous_id.prodMk continuous_id)).measurableSet

/-- The `m`-th approximating compact family of `(V ρ)⁻¹ * V ρ`. -/
def appC (ρ : ℝ) (m : ℕ) : Set SL3 :=
  (eBox (ρ - 1 / ((m : ℝ) + 1)))⁻¹ * eBox (ρ - 1 / ((m : ℝ) + 1))

theorem appC_subset_inv_mul {ρ : ℝ} (hρ : 0 < ρ) (m : ℕ) : appC ρ m ⊆ (V ρ)⁻¹ * V ρ := by
  intro w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hw
  have hs : ρ - 1 / ((m : ℝ) + 1) < ρ := by
    have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith
  exact Set.mul_mem_mul (Set.mem_inv.mpr (eBox_subset_V hs (Set.mem_inv.mp ha)))
    (eBox_subset_V hs hb)

theorem inv_mul_subset_iUnion_appC {ρ : ℝ} (hρ : 0 < ρ) :
    (V ρ)⁻¹ * V ρ ⊆ ⋃ m : ℕ, appC ρ m := by
  intro w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hw
  have ha' : a⁻¹ ∈ V ρ := Set.mem_inv.mp ha
  rw [V_eq_iUnion_V_sub hρ] at ha' hb
  obtain ⟨m₁, hm₁⟩ := Set.mem_iUnion.mp ha'
  obtain ⟨m₂, hm₂⟩ := Set.mem_iUnion.mp hb
  have hsM_mono : Monotone (fun m : ℕ => ρ - 1 / ((m : ℝ) + 1)) := by
    intro m₁ m₂ h
    have h1 : ((m₁ : ℝ) + 1) ≤ ((m₂ : ℝ) + 1) := by
      have : (m₁ : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast h
      linarith
    have h2 : (0 : ℝ) < (m₁ : ℝ) + 1 := by positivity
    have h3 := one_div_le_one_div_of_le h2 h1
    linarith
  set M : ℕ := max m₁ m₂ with hMdef
  refine Set.mem_iUnion.mpr ⟨M, ?_⟩
  have h1 : a⁻¹ ∈ V (ρ - 1 / ((M : ℝ) + 1)) :=
    Work.Misiurewicz.V_mono (hsM_mono (le_max_left m₁ m₂)) hm₁
  have h2 : b ∈ V (ρ - 1 / ((M : ℝ) + 1)) :=
    Work.Misiurewicz.V_mono (hsM_mono (le_max_right m₁ m₂)) hm₂
  exact Set.mul_mem_mul (Set.mem_inv.mpr (V_subset_eBox _ h1)) (V_subset_eBox _ h2)

theorem measurableSet_injAt (ρ : ℝ) : MeasurableSet {x : X3 | InjAt x ρ} := by
  rcases lt_or_ge (0 : ℝ) ρ with hρ | hρ
  · have hset : {x : X3 | InjAt x ρ} =
        (⋃ m : ℕ, {x : X3 | ∃ w ∈ appC ρ m, w ≠ 1 ∧ w • x = x})ᶜ := by
      ext x
      rw [Set.mem_ofPred_eq, Set.mem_compl_iff]
      constructor
      · intro hx hxU
        obtain ⟨m, hn⟩ := Set.mem_iUnion.mp hxU
        obtain ⟨w, hw, hw1, hwx⟩ := hn
        exact hw1 ((injAt_iff_forall_mem_inv_mul.mp hx) w (appC_subset_inv_mul hρ m hw) hwx)
      · intro hx
        rw [injAt_iff_forall_mem_inv_mul]
        intro w hwW hwx
        obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (inv_mul_subset_iUnion_appC hρ hwW)
        by_contra hw1
        exact hx (Set.mem_iUnion.mpr ⟨m, w, hm, hw1, hwx⟩)
    rw [hset]
    exact MeasurableSet.compl (MeasurableSet.iUnion fun m =>
      measurableSet_exists_fix_of_isCompact ((isCompact_eBox _).inv.mul (isCompact_eBox _)))
  · have hzero : {x : X3 | InjAt x ρ} = Set.univ := by
      ext x
      refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
      intro v₁ v₂ hv₁ _
      exfalso
      have h1 := hv₁ 0 0
      rw [abs_lt] at h1
      linarith [h1.2]
    rw [hzero]; exact MeasurableSet.univ

theorem measurable_injS : Measurable injS := by
  refine measurable_of_Ioi fun r => ?_
  have hset : injS ⁻¹' Set.Ioi r =
      ⋃ q : {q : ℚ // r < (q : ℝ) ∧ (q : ℝ) ≤ 1}, {x : X3 | InjAt x (q : ℝ)} := by
    ext x
    rw [Set.mem_preimage, Set.mem_Ioi, Set.mem_iUnion]
    constructor
    · intro hx
      have hmax_lt : max r 0 < injS x := max_lt hx (injS_pos x)
      set t : ℝ := (max r 0 + injS x) / 2 with ht
      have ht_gt : max r 0 < t := by rw [ht]; linarith
      have ht_lt : t < injS x := by rw [ht]; linarith
      have ht1 : t < 1 := by
        rw [ht]
        have h1 : max r 0 < 1 := max_lt (lt_of_lt_of_le hx (injS_le_one x)) one_pos
        linarith [injS_le_one x]
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn ht_gt
      refine ⟨⟨q, by linarith [le_max_left r 0], by linarith⟩, ?_⟩
      exact injAt_of_lt_injS (by linarith [le_max_right r 0]) (lt_trans hq2 ht_lt)
    · rintro ⟨⟨q, hq1, hq2⟩, hinj⟩
      rcases lt_or_ge (0 : ℝ) (q : ℝ) with hq0 | hq0
      · have : (q : ℝ) ≤ injS x := le_csSup (injSet_bddAbove x) ⟨hq0, hq2, hinj⟩
        linarith
      · have := injS_pos x; linarith
  rw [hset]
  exact MeasurableSet.iUnion fun q => measurableSet_injAt _

theorem measurable_injCap : Measurable injCap := by
  have h : injCap = fun x : X3 => min (injS x) (1 / 2) := rfl
  rw [h]
  exact measurable_injS.min measurable_const

/-! ## The a.e. sublinear growth statement -/

theorem ae_injCap_depth {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ) :
    ∀ᵐ x ∂μ, ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp (-(δ * n)) ≤
        Work.EKLC6Core.injCap (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x) := by
  classical
  obtain ⟨c2, lam0, hc2, hlam0, hlam0lt, hgeo⟩ := injCap_aDiag_geometric t
  obtain ⟨c2', lam0', hc2', hlam0', hlam0'lt, hgeo'⟩ := injCap_aDiag_geometric (-t)
  -- one-step bounds
  have hstep_lo : ∀ x : X3, c2 * lam0 * injCap x ≤ injCap (aDiag t • x) := by
    intro x
    have h := hgeo x 1
    rw [Function.iterate_one, pow_one] at h
    calc c2 * lam0 * injCap x = c2 * injCap x * lam0 := by ring
      _ ≤ injCap (aDiag t • x) := h
  have hstep_up : ∀ x : X3, injCap (aDiag t • x) ≤ (c2' * lam0')⁻¹ * injCap x := by
    intro x
    have h := hgeo' (aDiag t • x) 1
    rw [Function.iterate_one, pow_one, smul_smul, aDiag_neg_mul, one_smul] at h
    have hpos : (0 : ℝ) < c2' * lam0' := mul_pos hc2' hlam0'
    have h1 : (c2' * lam0') * injCap (aDiag t • x) ≤ injCap x := by
      have h' := h
      ring_nf at h' ⊢
      exact h'
    calc injCap (aDiag t • x)
        = (c2' * lam0')⁻¹ * ((c2' * lam0') * injCap (aDiag t • x)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
      _ ≤ (c2' * lam0')⁻¹ * injCap x :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr hpos))
  -- setup
  set T : X3 → X3 := fun x => aDiag t • x with hT
  have hT_meas : Measurable T := by rw [hT]; fun_prop
  have hemb : MeasurableEmbedding T := by
    rw [hT]
    exact MeasurableEquiv.measurableEmbedding (MeasurableEquiv.smul (aDiag t))
  set φ : X3 → ℝ := fun x => -Real.log (injCap x) with hφ
  have hφ_meas : Measurable φ := by
    rw [hφ]
    exact (Real.measurable_log.comp measurable_injCap).neg
  have hφ_nonneg : ∀ x : X3, 0 ≤ φ x := by
    intro x
    rw [hφ]
    simp only
    exact le_of_lt (neg_pos.mpr (Real.log_neg (injCap_pos x) (by linarith [injCap_le_half x])))
  set g : X3 → ℝ := fun x => φ (T x) - φ x with hg
  have hg_meas : Measurable g := (hφ_meas.comp hT_meas).sub hφ_meas
  set C : ℝ := max |Real.log (c2' * lam0')| |Real.log (c2 * lam0)| with hC
  have hbound : ∀ x : X3, |g x| ≤ C := by
    intro x
    have h1 : c2 * lam0 * injCap x ≤ injCap (T x) := by rw [hT]; exact hstep_lo x
    have h2 : injCap (T x) ≤ (c2' * lam0')⁻¹ * injCap x := by rw [hT]; exact hstep_up x
    have hlo : c2' * lam0' ≤ injCap x / injCap (T x) := by
      rw [le_div_iff₀ (injCap_pos (T x))]
      have hpos : (0 : ℝ) < c2' * lam0' := mul_pos hc2' hlam0'
      have hthis := mul_le_mul_of_nonneg_left h2 (le_of_lt hpos)
      calc (c2' * lam0') * injCap (T x)
          ≤ (c2' * lam0') * ((c2' * lam0')⁻¹ * injCap x) := hthis
        _ = injCap x := by rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    have hhi : injCap x / injCap (T x) ≤ (c2 * lam0)⁻¹ := by
      rw [div_le_iff₀ (injCap_pos (T x))]
      have hpos : (0 : ℝ) < c2 * lam0 := mul_pos hc2 hlam0
      have hthis := mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr hpos))
      rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul] at hthis
      exact hthis
    have hρpos : 0 < injCap x / injCap (T x) := div_pos (injCap_pos x) (injCap_pos (T x))
    have hgx : g x = Real.log (injCap x / injCap (T x)) := by
      rw [hg, hφ]
      simp only
      rw [Real.log_div (ne_of_gt (injCap_pos x)) (ne_of_gt (injCap_pos (T x)))]
      ring
    rw [hgx]
    have hloglo : Real.log (c2' * lam0') ≤ Real.log (injCap x / injCap (T x)) :=
      Real.log_le_log (mul_pos hc2' hlam0') hlo
    have hloghi : Real.log (injCap x / injCap (T x)) ≤ Real.log ((c2 * lam0)⁻¹) :=
      Real.log_le_log hρpos hhi
    rw [Real.log_inv] at hloghi
    refine abs_le.mpr ⟨?_, ?_⟩
    · have h3 : -|Real.log (c2' * lam0')| ≤ Real.log (c2' * lam0') := neg_abs_le _
      have h4 : |Real.log (c2' * lam0')| ≤ C := by rw [hC]; exact le_max_left _ _
      linarith
    · have h3 : -Real.log (c2 * lam0) ≤ |Real.log (c2 * lam0)| := neg_le_abs _
      have h4 : |Real.log (c2 * lam0)| ≤ C := by rw [hC]; exact le_max_right _ _
      linarith
  have hg_int : Integrable g μ :=
    MeasureTheory.Integrable.of_bound hg_meas.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hbound x))
  -- the truncated functions
  set φM : ℕ → X3 → ℝ := fun M x => min (φ x) (M : ℝ) with hφM
  have hφM_meas : ∀ M : ℕ, Measurable (φM M) := fun M => hφ_meas.min measurable_const
  have hφM_nonneg : ∀ (M : ℕ) (x : X3), 0 ≤ φM M x := by
    intro M x; rw [hφM]; exact le_min (hφ_nonneg x) (Nat.cast_nonneg M)
  have hφM_le : ∀ (M : ℕ) (x : X3), φM M x ≤ (M : ℝ) := by
    intro M x; rw [hφM]; exact min_le_right _ _
  have hφM_tend : ∀ x : X3, Tendsto (fun M : ℕ => φM M x) atTop (𝓝 (φ x)) := by
    intro x
    have hc : Tendsto (fun _ : ℕ => φ x) atTop (𝓝 (φ x)) := tendsto_const_nhds
    refine hc.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ⌈φ x⌉₊] with M hM
    rw [hφM]
    exact (min_eq_left (le_trans (Nat.le_ceil _) (by exact_mod_cast hM))).symm
  have hmin_lip : ∀ a b M : ℝ, |min a M - min b M| ≤ |a - b| := by
    intro a b M
    rcases lt_or_ge M a with ha | ha <;> rcases lt_or_ge M b with hb | hb
    · rw [min_eq_right (le_of_lt ha), min_eq_right (le_of_lt hb), sub_self, abs_zero]
      exact abs_nonneg _
    · rw [min_eq_right (le_of_lt ha), min_eq_left hb,
        abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · rw [min_eq_left ha, min_eq_right (le_of_lt hb),
        abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · rw [min_eq_left ha, min_eq_left hb]
  have hgM_bound : ∀ (M : ℕ) (x : X3), |φM M (T x) - φM M x| ≤ C := by
    intro M x
    rw [hφM]
    simp only
    refine le_trans (hmin_lip (φ (T x)) (φ x) (M : ℝ)) ?_
    have := hbound x
    rwa [hg] at this
  have hgM_zero : ∀ M : ℕ, ∫ x, (φM M (T x) - φM M x) ∂μ = 0 := by
    intro M
    have hi1 : Integrable (fun x : X3 => φM M (T x)) μ := by
      refine MeasureTheory.Integrable.of_bound ((hφM_meas M).comp hT_meas).aestronglyMeasurable
        (M : ℝ) ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hφM_nonneg M (T x)], hφM_le M (T x)⟩
    have hi2 : Integrable (φM M) μ := by
      refine MeasureTheory.Integrable.of_bound (hφM_meas M).aestronglyMeasurable (M : ℝ) ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hφM_nonneg M x], hφM_le M x⟩
    have hcomp : ∫ x, φM M (T x) ∂μ = ∫ x, φM M x ∂μ :=
      MeasureTheory.MeasurePreserving.integral_comp hmp hemb (φM M)
    rw [MeasureTheory.integral_sub hi1 hi2, hcomp, sub_self]
  have hInt_eq : ∫ x, g x ∂μ = 0 := by
    have hDCT : Tendsto (fun M : ℕ => ∫ x, (φM M (T x) - φM M x) ∂μ) atTop
        (𝓝 (∫ x, g x ∂μ)) :=
      MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ : X3 => C)
        (fun M => ((hφM_meas M).comp hT_meas).sub (hφM_meas M) |>.aestronglyMeasurable)
        (MeasureTheory.integrable_const C)
        (fun M => Filter.Eventually.of_forall (fun x => by
          rw [Real.norm_eq_abs]; exact hgM_bound M x))
        (Filter.Eventually.of_forall (fun x => by
          rw [hg]; exact (hφM_tend (T x)).sub (hφM_tend x)))
    have hz : Tendsto (fun M : ℕ => ∫ x, (φM M (T x) - φM M x) ∂μ) atTop (𝓝 0) := by
      have h0t : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
      refine h0t.congr' ?_
      filter_upwards with M
      exact (hgM_zero M).symm
    exact tendsto_nhds_unique hDCT hz
  -- the Birkhoff convergence
  have hbirkA : ∀ (n : ℕ) (x : X3),
      Work.EKLComp.Birkhoff.birkA T g n x = (n : ℝ)⁻¹ * (φ (T^[n] x) - φ x) := by
    intro n x
    rw [Work.EKLComp.Birkhoff.birkA_def]
    congr 1
    have hg_iter : ∀ k : ℕ, g (T^[k] x) = φ (T^[k+1] x) - φ (T^[k] x) := by
      intro k
      have hstep : T (T^[k] x) = T^[k+1] x := (Function.iterate_succ_apply' T k x).symm
      rw [hg]
      simp only
      rw [hstep]
    calc ∑ k ∈ Finset.range n, g (T^[k] x)
        = ∑ k ∈ Finset.range n, (φ (T^[k+1] x) - φ (T^[k] x)) :=
          Finset.sum_congr rfl (fun k _ => hg_iter k)
      _ = φ (T^[n] x) - φ (T^[0] x) := Finset.sum_range_sub (fun k => φ (T^[k] x)) n
      _ = φ (T^[n] x) - φ x := by rw [Function.iterate_zero_apply]
  have hbirk : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => Work.EKLComp.Birkhoff.birkA T g n x) atTop
      (𝓝 (condExp (MeasurableSpace.invariants T) μ g x)) :=
    Work.EKLComp.birkhoff_all μ T hmp g hg_int
  have hlim_ae : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * φ (T^[n] x)) atTop
      (𝓝 (condExp (MeasurableSpace.invariants T) μ g x)) := by
    filter_upwards [hbirk] with x hx
    have h2 : Tendsto (fun n : ℕ => φ x * (n : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa using (((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp
        tendsto_natCast_atTop_atTop).const_mul (φ x))
    have hsum := hx.add h2
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards with n
    rw [hbirkA n x]; ring
  have hcond_nonneg : 0 ≤ᵐ[μ] condExp (MeasurableSpace.invariants T) μ g := by
    filter_upwards [hlim_ae] with x hx
    refine ge_of_tendsto hx (Filter.Eventually.of_forall (fun n => ?_))
    exact mul_nonneg (by positivity) (hφ_nonneg _)
  have hcond_zero : condExp (MeasurableSpace.invariants T) μ g =ᵐ[μ] 0 := by
    have h1 : ∫ x, condExp (MeasurableSpace.invariants T) μ g x ∂μ = 0 := by
      rw [MeasureTheory.integral_condExp (MeasurableSpace.invariants_le T)]
      exact hInt_eq
    exact (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hcond_nonneg
      (MeasureTheory.integrable_condExp (m := MeasurableSpace.invariants T))).mp h1
  -- conclusion
  have hmain : ∀ᵐ x ∂μ, ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp (-(δ * n)) ≤ injCap (T^[n] x) := by
    filter_upwards [hlim_ae, hcond_zero] with x hx1 hx2
    rw [hx2, Pi.zero_apply] at hx1
    intro δ hδ
    have hδev : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ)⁻¹ * φ (T^[n] x) < δ :=
      hx1.eventually (eventually_lt_nhds hδ)
    filter_upwards [hδev, Filter.eventually_ge_atTop 1] with n hn hng
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hng : (0 : ℕ) < n)
    have h1 : φ (T^[n] x) < δ * n := by
      have hmul := mul_lt_mul_of_pos_left hn hnpos
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hnpos), one_mul] at hmul
      rw [mul_comm ((n : ℝ)) δ] at hmul
      exact hmul
    have h3 : -(δ * (n : ℝ)) < Real.log (injCap (T^[n] x)) := by
      have h4 := h1
      rw [hφ] at h4
      simp only at h4
      linarith
    exact le_of_lt ((Real.lt_log_iff_exp_lt (injCap_pos (T^[n] x))).mp h3)
  filter_upwards [hmain] with x hx
  simpa only [hT] using hx

end

end Work.EKLC6Core
