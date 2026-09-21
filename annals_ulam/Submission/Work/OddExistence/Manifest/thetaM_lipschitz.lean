import Mathlib
import Submission.Work.OddExistence.Manifest
import Submission.Work.OddExistence.Manifest.ThetaMBridge
import Submission.Work.Anchor.ThetaM_contDiffOn
import Submission.Work.OddVolterra.Existence.theta_lipschitz_state_ball

/-!
# Lipschitzness of the manifest odd kernel `ΘM` in the state variable

The target

`Work.OddExistence.Manifest.thetaM_lipschitz`

says: on a slope box `[a,b] ⊆ (0,1]` and a state ball `closedBall (baseState σ) ρ` (`ρ ≤ 1/2`),
the manifest odd kernel `ΘM n h s σ ·` (`Work.OddExistence.ThetaM`, i.e. the `s`-derivative of the
Abel average `G2M` of the manifest Abel kernel, in its last two rows) is Lipschitz in the state.

The argument is the standard "`C¹` on a compact set ⟹ Lipschitz" one, but it has to be organised
carefully because the two slope slots are *not* convex and the state ball depends on `σ`:

* The positivity hypothesis `KdenPosOn h a b` gives positivity of the Abel radicand `krad` on the
  *closed* box of slopes `[a,b]²` (for `|t| ≥ 1/5`).  Differentiating in the first slope slot (which
  `ΘM` does, twice, through `G2M`) needs the radicand to stay positive on a *neighbourhood* of that
  box, so we first spread positivity to a `δ`-neighbourhood (`exists_krad_pos_nhds`, compactness of
  the slope/t-slab and openness of `{krad > 0}`).
* On the resulting open region `thetaMRegion a b δ` (both slopes in `(a-δ,b+δ)`, both chord
  endpoints of modulus in `(1/5,3)`) we prove `ContDiffOn ℝ ⊤` of `(s,σ,z) ↦ ΘM n h s σ z`
  (`contDiffOn_KernelExtThetaM_of_pos`): the Abel average is made smooth by the `τ = sin²θ`
  substitution, and its first-slot derivative by `fderiv` in the first coordinate.
* Compactness of the region `RcM a b ρ` of the statement then bounds the `z`-differential by a
  constant `C`, and the mean value inequality applied on the convex slice
  `{(s,σ,z) | z ∈ closedBall (baseState σ) ρ}` turns this into the Lipschitz bound `C`.
-/

namespace Work.OddExistence.Manifest

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

set_option maxHeartbeats 1600000

abbrev St4 : Type := Work.OddVolterra.St

/-! ## 1. Spreading the positivity of the Abel radicand to a neighbourhood of the slope box -/

/-- The distance from a real number to its clamp into `[a,b]` is at most `δ` as soon as the number
lies in the `δ`-neighbourhood `[a-δ, b+δ]` of that interval. -/
lemma abs_sub_clamp_le {a b u δ : ℝ} (hab : a ≤ b) (hδ0 : 0 ≤ δ)
    (hu : u ∈ Set.Icc (a - δ) (b + δ)) :
    |u - max a (min b u)| ≤ δ := by
  rcases lt_or_ge u a with h | h
  · have hmin : min b u = u := min_eq_right (le_trans h.le hab)
    have hmax : max a u = a := max_eq_left h.le
    rw [hmin, hmax, abs_of_nonpos (by linarith : u - a ≤ 0), neg_sub]
    linarith [hu.1]
  · rcases lt_or_ge u b with h' | h'
    · have hmin : min b u = u := min_eq_right h'.le
      have hmax : max a u = u := max_eq_right h
      rw [hmin, hmax, sub_self, abs_zero]
      exact hδ0
    · have hmin : min b u = b := min_eq_left h'
      have hmax : max a b = b := max_eq_right hab
      rw [hmin, hmax, abs_of_nonneg (by linarith : (0:ℝ) ≤ u - b)]
      linarith [hu.2]

/-- The distance between two triples sharing their third coordinate, in the max metric. -/
lemma dist_triple_eq (u u₀ σ σ₀ t : ℝ) :
    dist ((u, σ, t) : ℝ × (ℝ × ℝ)) (u₀, σ₀, t) = max |u - u₀| |σ - σ₀| := by
  rw [dist_eq_norm]
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.norm_def, Real.norm_eq_abs, sub_self, abs_zero]
  have h : max |σ - σ₀| 0 = |σ - σ₀| := max_eq_left (abs_nonneg _)
  rw [h]

/-- **Positivity of the Abel radicand on a neighbourhood of the slope box.**  If `krad h σ t u` is
positive for `u, σ ∈ [a,b]` and `1/5 ≤ |t|`, then, with the `t`-range restricted to the compact
`1/5 ≤ |t| ≤ 3`, it stays positive on a full `δ`-neighbourhood of the box `[a,b]²`. -/
lemma exists_krad_pos_nhds {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {a b : ℝ}
    (hab : a ≤ b) (hpos : Work.OddExistence.KdenPosOn h a b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ Set.Icc (a - δ) (b + δ), ∀ σ ∈ Set.Icc (a - δ) (b + δ),
      ∀ t : ℝ, 1 / 5 ≤ |t| → |t| ≤ 3 → 0 < Work.OddVolterra.krad h σ t u := by
  set Kt : Set ℝ := Set.Icc (1 / 5 : ℝ) 3 ∪ Set.Icc (-3 : ℝ) (-(1 / 5 : ℝ)) with hKt
  set K : Set (ℝ × (ℝ × ℝ)) := Set.Icc a b ×ˢ (Set.Icc a b ×ˢ Kt) with hK
  have hKc : IsCompact K :=
    isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.union isCompact_Icc))
  have hcontk : Continuous (fun p : ℝ × (ℝ × ℝ) => Work.OddVolterra.krad h p.2.1 p.2.2 p.1) :=
    continuous_krad_comp hh (by fun_prop) (by fun_prop) (by fun_prop)
  have hcontKden : Continuous
      (fun p : ℝ × (ℝ × ℝ) => Work.OddVolterra.Kden h p.1 p.2.1 p.2.2) := by
    have heq : (fun p : ℝ × (ℝ × ℝ) => Work.OddVolterra.Kden h p.1 p.2.1 p.2.2)
        = fun p => Real.sqrt (Work.OddVolterra.krad h p.2.1 p.2.2 p.1) := by
      funext p; rw [Work.OddVolterra.Kden_eq_sqrt_krad]
    rw [heq]; exact hcontk.sqrt
  have hV : IsOpen {p : ℝ × (ℝ × ℝ) | 0 < Work.OddVolterra.Kden h p.1 p.2.1 p.2.2} :=
    isOpen_lt continuous_const hcontKden
  have hKV : K ⊆ {p : ℝ × (ℝ × ℝ) | 0 < Work.OddVolterra.Kden h p.1 p.2.1 p.2.2} := by
    rintro p ⟨h1, h2, h3⟩
    have ht5 : (1 / 5 : ℝ) ≤ |p.2.2| := by
      rcases h3 with h3 | h3
      · rw [abs_of_nonneg (by linarith [h3.1])]; exact h3.1
      · rw [abs_of_nonpos (by linarith [h3.2])]; linarith [h3.2]
    exact hpos p.1 h1 p.2.1 h2 p.2.2 ht5
  obtain ⟨ε, hε, hεK⟩ := hKc.exists_cthickening_subset_open hV hKV
  refine ⟨ε / 2, by positivity, ?_⟩
  intro u hu σ hσ t ht5 ht3
  have hu₀ : max a (min b u) ∈ Set.Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hσ₀ : max a (min b σ) ∈ Set.Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have htK : t ∈ Kt := by
    rcases le_total 0 t with h | h
    · refine Or.inl ⟨?_, ?_⟩
      · rw [abs_of_nonneg h] at ht5; exact ht5
      · rw [abs_of_nonneg h] at ht3; exact ht3
    · refine Or.inr ⟨?_, ?_⟩
      · rw [abs_of_nonpos h] at ht3; linarith
      · rw [abs_of_nonpos h] at ht5; linarith
  have hdu : |u - max a (min b u)| ≤ ε / 2 := abs_sub_clamp_le hab (by positivity) hu
  have hdσ : |σ - max a (min b σ)| ≤ ε / 2 := abs_sub_clamp_le hab (by positivity) hσ
  have hmem : (u, σ, t) ∈ Metric.cthickening ε K :=
    Metric.mem_cthickening_of_dist_le _ _ ε K ⟨hu₀, hσ₀, htK⟩ (by
      rw [dist_triple_eq]
      exact max_le (by linarith) (by linarith))
  have hKden : 0 < Work.OddVolterra.Kden h u σ t := hεK hmem
  rw [Work.OddVolterra.Kden_eq_sqrt_krad] at hKden
  exact Real.sqrt_pos.mp hKden

/-! ## 2. Smoothness of the manifest `Θ` on an open region of the slope/state space -/

/-- **The manifest `Θ` is `C^∞` on any open region on which the Abel radicand is positive at the two
chord endpoints, and along the whole `τ`-segment between the two slopes.** -/
theorem contDiffOn_KernelExtThetaM_of_pos (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {U : Set (ℝ × (ℝ × St4))} (hU : IsOpen U)
    (hposU : ∀ q ∈ U, 0 < Work.OddVolterra.krad h q.2.1 (-(q.2.2 0)) q.1 ∧
      0 < Work.OddVolterra.krad h q.2.1 (q.2.2 1) q.1)
    (hposτ : ∀ q ∈ U, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      0 < Work.OddVolterra.krad h q.2.1 (-(q.2.2 0)) (q.1 + τ * (q.2.1 - q.1)) ∧
      0 < Work.OddVolterra.krad h q.2.1 (q.2.2 1) (q.1 + τ * (q.2.1 - q.1))) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × St4) => Work.OddVolterra.KernelExt.ThetaM n h q.1 q.2.1 q.2.2) U := by
  -- the `τ`-parametrised manifest kernel is smooth
  have hKτ : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × (ℝ × St4)) × ℝ =>
        (Work.OddVolterra.KernelExt.KvecM n h (p.1.1 + p.2 * (p.1.2.1 - p.1.1)) p.1.2.1
          (p.1.2.2 0) (p.1.2.2 1) (p.1.2.2 2) (p.1.2.2 3)) i)
      (U ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro i
    have hK := Work.Anchor.contDiffOn_KvecM_comp (n := n) (hh := hh)
      (B := U ×ˢ Set.Icc (0 : ℝ) 1)
      (s := fun p : (ℝ × (ℝ × St4)) × ℝ => p.1.1 + p.2 * (p.1.2.1 - p.1.1))
      (σ := fun p => p.1.2.1) (x := fun p => p.1.2.2 0) (y := fun p => p.1.2.2 1)
      (x' := fun p => p.1.2.2 2) (y' := fun p => p.1.2.2 3)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      (fun p hp => (hposτ p.1 hp.1 p.2 hp.2).1)
      (fun p hp => (hposτ p.1 hp.1 p.2 hp.2).2)
    exact (contDiffOn_pi.mp hK) i
  -- the `θ`-parametrised manifest kernel is smooth
  have hKθ : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × (ℝ × St4)) × ℝ =>
        (Work.OddVolterra.KernelExt.KvecM n h (p.1.1 + Real.sin p.2 ^ 2 * (p.1.2.1 - p.1.1))
          p.1.2.1 (p.1.2.2 0) (p.1.2.2 1) (p.1.2.2 2) (p.1.2.2 3)) i)
      (U ×ˢ Set.univ) := by
    intro i
    have hsin : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : (ℝ × (ℝ × St4)) × ℝ => (p.1, Real.sin p.2 ^ 2)) (U ×ˢ Set.univ) :=
      (((contDiff_fst : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (ℝ × (ℝ × St4)) × ℝ => p.1)).prodMk
        ((Real.contDiff_sin.pow 2).comp contDiff_snd))).contDiffOn
    have hcomp := (hKτ i).comp hsin (fun p hp => ⟨hp.1, ⟨sq_nonneg _, Real.sin_sq_le_one _⟩⟩)
    simpa only [Function.comp_def] using hcomp
  -- the `θ`-integral is smooth
  have hInt : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × St4) => ∫ θ in (0 : ℝ)..(Real.pi / 2),
        2 * (Work.OddVolterra.KernelExt.KvecM n h (q.1 + Real.sin θ ^ 2 * (q.2.1 - q.1)) q.2.1
          (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) i) U := by
    intro i
    refine Work.Anchor.contDiffOn_intervalIntegral_parametric (hU := hU) (a := 0)
      (b := Real.pi / 2)
      (G := fun (p : (ℝ × (ℝ × St4)) × ℝ) =>
        2 * (Work.OddVolterra.KernelExt.KvecM n h (p.1.1 + Real.sin p.2 ^ 2 * (p.1.2.1 - p.1.1))
          p.1.2.1 (p.1.2.2 0) (p.1.2.2 1) (p.1.2.2 2) (p.1.2.2 3)) i) ?_
    exact (contDiffOn_const (c := (2 : ℝ))).mul (by simpa using hKθ i)
  -- `G2M` is smooth
  have hG2 : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × St4) =>
        (Work.OddVolterra.KernelExt.G2M n h q.1 q.2.1
          (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) i) U := by
    intro i
    refine (hInt i).congr (fun q hq => ?_)
    have hcont : ContinuousOn (fun τ : ℝ => (Work.OddVolterra.KernelExt.KvecM n h
        (q.1 + τ * (q.2.1 - q.1)) q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) i)
        (Set.Icc (0 : ℝ) 1) := by
      have h := (hKτ i).continuousOn.comp
        (by fun_prop : ContinuousOn (fun τ : ℝ => (q, τ)) (Set.Icc (0 : ℝ) 1))
        (fun τ hτ => ⟨hq, hτ⟩)
      simpa only [Function.comp_def] using h
    have h := Work.Anchor.AbelWeight_subst (K := fun τ : ℝ => (Work.OddVolterra.KernelExt.KvecM
      n h (q.1 + τ * (q.2.1 - q.1)) q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) i) hcont
    simpa only [Work.OddVolterra.KernelExt.G2M] using h
  -- the derivative rows
  have hderiv : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × St4) => deriv (fun u : ℝ =>
        (Work.OddVolterra.KernelExt.G2M n h u q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) i)
          q.1) U :=
    fun i => Work.Anchor.contDiffOn_deriv_slice_fst (P := ℝ × St4) (U := U) hU (hG2 i)
  -- assembly
  have hcoord : ∀ k : Fin 4, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × St4) => q.2.2 k) U := by
    intro k
    have h : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × (ℝ × St4) => q.2.2) U := by fun_prop
    exact (contDiffOn_pi.mp h) k
  have hTheta : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × St4) => Work.OddVolterra.KernelExt.ThetaM n h q.1 q.2.1 q.2.2) U := by
    rw [contDiffOn_pi]
    intro i
    fin_cases i
    · simpa [Work.OddVolterra.KernelExt.ThetaM] using (hcoord 2).neg
    · simpa [Work.OddVolterra.KernelExt.ThetaM] using (hcoord 3).neg
    · simpa [Work.OddVolterra.KernelExt.ThetaM] using (hderiv 0).neg
    · simpa [Work.OddVolterra.KernelExt.ThetaM] using (hderiv 1).neg
  exact hTheta

/-! ## 3. The concrete open region of the statement -/

/-- The open region of the `(s,σ,z)`-space on which we prove smoothness of `ΘM`: both slope slots
in the `δ`-neighbourhood of `[a,b]`, both chord endpoints of modulus in `(1/5, 3)`. -/
def thetaMRegion (a b δ : ℝ) : Set (ℝ × (ℝ × St4)) :=
  {q | q.1 ∈ Set.Ioo (a - δ) (b + δ) ∧ q.2.1 ∈ Set.Ioo (a - δ) (b + δ) ∧
    1 / 5 < |q.2.2 0| ∧ |q.2.2 0| < 3 ∧ 1 / 5 < |q.2.2 1| ∧ |q.2.2 1| < 3}

lemma isOpen_thetaMRegion (a b δ : ℝ) : IsOpen (thetaMRegion a b δ) := by
  have h1 : IsOpen {q : ℝ × (ℝ × St4) | q.1 ∈ Set.Ioo (a - δ) (b + δ)} :=
    isOpen_Ioo.preimage continuous_fst
  have h2 : IsOpen {q : ℝ × (ℝ × St4) | q.2.1 ∈ Set.Ioo (a - δ) (b + δ)} :=
    isOpen_Ioo.preimage (continuous_fst.comp continuous_snd)
  have h3 : IsOpen {q : ℝ × (ℝ × St4) | 1 / 5 < |q.2.2 0|} :=
    isOpen_lt continuous_const (by fun_prop : Continuous fun q : ℝ × (ℝ × St4) => |q.2.2 0|)
  have h4 : IsOpen {q : ℝ × (ℝ × St4) | |q.2.2 0| < 3} :=
    isOpen_lt (by fun_prop : Continuous fun q : ℝ × (ℝ × St4) => |q.2.2 0|) continuous_const
  have h5 : IsOpen {q : ℝ × (ℝ × St4) | 1 / 5 < |q.2.2 1|} :=
    isOpen_lt continuous_const (by fun_prop : Continuous fun q : ℝ × (ℝ × St4) => |q.2.2 1|)
  have h6 : IsOpen {q : ℝ × (ℝ × St4) | |q.2.2 1| < 3} :=
    isOpen_lt (by fun_prop : Continuous fun q : ℝ × (ℝ × St4) => |q.2.2 1|) continuous_const
  have heq : thetaMRegion a b δ = {q : ℝ × (ℝ × St4) | q.1 ∈ Set.Ioo (a - δ) (b + δ)}
      ∩ {q : ℝ × (ℝ × St4) | q.2.1 ∈ Set.Ioo (a - δ) (b + δ)}
      ∩ {q : ℝ × (ℝ × St4) | 1 / 5 < |q.2.2 0|} ∩ {q : ℝ × (ℝ × St4) | |q.2.2 0| < 3}
      ∩ {q : ℝ × (ℝ × St4) | 1 / 5 < |q.2.2 1|} ∩ {q : ℝ × (ℝ × St4) | |q.2.2 1| < 3} := by
    ext q
    simp only [thetaMRegion, Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto
  rw [heq]
  exact ((((h1.inter h2).inter h3).inter h4).inter h5).inter h6

/-- The region of the statement (slope box `[a,b]²`, state ball) is contained in the open region. -/
lemma RcM_subset_thetaMRegion {a b ρ δ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1)
    (hρ1 : ρ ≤ 1 / 2) (hδ0 : 0 < δ) :
    RcM a b ρ ⊆ thetaMRegion a b δ := by
  intro q hq
  obtain ⟨h1, h2, h3⟩ := hq
  obtain ⟨hz0, hz1, hzb⟩ := mem_RcM_facts ha hab hb hρ1 ⟨h1, h2, h3⟩
  have hcoord : ∀ i : Fin 4, |q.2.2 i - Work.OddVolterra.baseState q.2.1 i| ≤ ρ := by
    intro i
    have h := dist_le_pi_dist q.2.2 (Work.OddVolterra.baseState q.2.1) i
    rw [Real.dist_eq] at h
    linarith [Metric.mem_closedBall.mp h3]
  have hpx : (7 / 10 : ℝ) < Commons.Geometry.Ulam.profileX q.2.1 := by
    have h0 : 0 ≤ q.2.1 := le_trans ha.le h2.1
    have hle : Commons.Geometry.Ulam.profileX 1 ≤ Commons.Geometry.Ulam.profileX q.2.1 :=
      Commons.Geometry.Ulam.profileX_le_profileX' h0 (le_trans h2.2 hb)
    have hpt : Commons.Geometry.Ulam.profileX 1 = 1 / Real.sqrt 2 := by
      simp only [Commons.Geometry.Ulam.profileX]; norm_num
    have hsqrt : Real.sqrt 2 < 10 / 7 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have h4 : (7 : ℝ) / 10 < 1 / Real.sqrt 2 := by
      rw [lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
      nlinarith [hsqrt]
    rw [hpt] at hle
    linarith
  have hz0' : (1 / 5 : ℝ) < q.2.2 0 := by
    have h := hcoord 0
    rw [show Work.OddVolterra.baseState q.2.1 0 = Commons.Geometry.Ulam.profileX q.2.1
      from rfl] at h
    linarith [abs_le.mp h, hρ1]
  have hz1' : (1 / 5 : ℝ) < q.2.2 1 := by
    have h := hcoord 1
    rw [show Work.OddVolterra.baseState q.2.1 1 = Commons.Geometry.Ulam.profileX q.2.1
      from rfl] at h
    linarith [abs_le.mp h, hρ1]
  refine ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, ⟨by linarith [h2.1], by linarith [h2.2]⟩,
    ?_, ?_, ?_, ?_⟩
  · rw [abs_of_pos (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith [abs_le.mp (hzb 0)]
  · rw [abs_of_pos (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith [abs_le.mp (hzb 1)]

/-- Positivity of the Abel radicand at the two chord endpoints on the open region. -/
lemma thetaMRegion_pos {h : ℝ → ℝ} {a b δ : ℝ}
    (hδpos : ∀ u ∈ Set.Icc (a - δ) (b + δ), ∀ σ ∈ Set.Icc (a - δ) (b + δ),
      ∀ t : ℝ, 1 / 5 ≤ |t| → |t| ≤ 3 → 0 < Work.OddVolterra.krad h σ t u) :
    ∀ q ∈ thetaMRegion a b δ,
      0 < Work.OddVolterra.krad h q.2.1 (-(q.2.2 0)) q.1 ∧
      0 < Work.OddVolterra.krad h q.2.1 (q.2.2 1) q.1 := by
  intro q hq
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6⟩ := hq
  exact ⟨hδpos q.1 ⟨le_of_lt hq1.1, le_of_lt hq1.2⟩ q.2.1 ⟨le_of_lt hq2.1, le_of_lt hq2.2⟩
      (-(q.2.2 0)) (by rw [abs_neg]; exact le_of_lt hq3) (by rw [abs_neg]; exact le_of_lt hq4),
    hδpos q.1 ⟨le_of_lt hq1.1, le_of_lt hq1.2⟩ q.2.1 ⟨le_of_lt hq2.1, le_of_lt hq2.2⟩
      (q.2.2 1) (le_of_lt hq5) (le_of_lt hq6)⟩

/-- Positivity of the Abel radicand along the `τ`-segment between the two slopes. -/
lemma thetaMRegion_pos_move {h : ℝ → ℝ} {a b δ : ℝ}
    (hδpos : ∀ u ∈ Set.Icc (a - δ) (b + δ), ∀ σ ∈ Set.Icc (a - δ) (b + δ),
      ∀ t : ℝ, 1 / 5 ≤ |t| → |t| ≤ 3 → 0 < Work.OddVolterra.krad h σ t u) :
    ∀ q ∈ thetaMRegion a b δ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      0 < Work.OddVolterra.krad h q.2.1 (-(q.2.2 0)) (q.1 + τ * (q.2.1 - q.1)) ∧
      0 < Work.OddVolterra.krad h q.2.1 (q.2.2 1) (q.1 + τ * (q.2.1 - q.1)) := by
  intro q hq τ hτ
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6⟩ := hq
  have hmove : q.1 + τ * (q.2.1 - q.1) ∈ Set.Icc (a - δ) (b + δ) := by
    have hle : q.1 + τ * (q.2.1 - q.1) = (1 - τ) * q.1 + τ * q.2.1 := by ring
    rw [hle]
    have hτ0 : (0 : ℝ) ≤ τ := hτ.1
    have h1τ : (0 : ℝ) ≤ 1 - τ := by linarith [hτ.2]
    constructor
    · have ha1 : (1 - τ) * (a - δ) ≤ (1 - τ) * q.1 :=
        mul_le_mul_of_nonneg_left (le_of_lt hq1.1) h1τ
      have ha2 : τ * (a - δ) ≤ τ * q.2.1 := mul_le_mul_of_nonneg_left (le_of_lt hq2.1) hτ0
      have ha3 : (1 - τ) * (a - δ) + τ * (a - δ) = a - δ := by ring
      linarith
    · have hb1 : (1 - τ) * q.1 ≤ (1 - τ) * (b + δ) :=
        mul_le_mul_of_nonneg_left (le_of_lt hq1.2) h1τ
      have hb2 : τ * q.2.1 ≤ τ * (b + δ) := mul_le_mul_of_nonneg_left (le_of_lt hq2.2) hτ0
      have hb3 : (1 - τ) * (b + δ) + τ * (b + δ) = b + δ := by ring
      linarith
  exact ⟨hδpos _ hmove _ ⟨le_of_lt hq2.1, le_of_lt hq2.2⟩ (-(q.2.2 0))
      (by rw [abs_neg]; exact le_of_lt hq3) (by rw [abs_neg]; exact le_of_lt hq4),
    hδpos _ hmove _ ⟨le_of_lt hq2.1, le_of_lt hq2.2⟩ (q.2.2 1) (le_of_lt hq5) (le_of_lt hq6)⟩

/-! ## 4. The convex slice and the Lipschitz estimate -/

/-- The slice of the parameter space over one state ball: `(s,σ) × closedBall (baseState σ) ρ`.  It
is the convex set on which the mean value inequality is applied. -/
lemma convex_slice (s σ : ℝ) (ρ : ℝ) :
    Convex ℝ {q : ℝ × (ℝ × St4) | q.1 = s ∧ q.2.1 = σ ∧
      q.2.2 ∈ Metric.closedBall (Work.OddVolterra.baseState σ) ρ} := by
  rw [convex_iff_forall_pos]
  rintro p ⟨hp1, hp2, hp3⟩ p' ⟨hp1', hp2', hp3'⟩ u v hu hv huv
  have hnorm : u + v = 1 := huv
  refine ⟨?_, ?_, ?_⟩
  · show (u • p + v • p').1 = s
    have h : (u • p + v • p').1 = u * p.1 + v * p'.1 := by simp
    rw [h, hp1, hp1', ← add_mul, hnorm, one_mul]
  · show (u • p + v • p').2.1 = σ
    have h : (u • p + v • p').2.1 = u * p.2.1 + v * p'.2.1 := by simp
    rw [h, hp2, hp2', ← add_mul, hnorm, one_mul]
  · show (u • p + v • p').2.2 ∈ Metric.closedBall (Work.OddVolterra.baseState σ) ρ
    have h : (u • p + v • p').2.2 = u • p.2.2 + v • p'.2.2 := by simp
    rw [h]
    exact convex_closedBall (Work.OddVolterra.baseState σ) ρ hp3 hp3' hu.le hv.le hnorm

/-- The norm of the difference of two points of the product differing only in the state. -/
lemma norm_mk_sub_eq (s σ : ℝ) (z z' : St4) :
    ‖((s, σ, z) : ℝ × (ℝ × St4)) - (s, σ, z')‖ = ‖z - z'‖ := by
  have h : ((s, σ, z) : ℝ × (ℝ × St4)) - (s, σ, z') = (0, (0, z - z')) := by
    ext <;> simp
  rw [h, Prod.norm_def, Prod.norm_def, norm_zero]
  rw [max_eq_right (norm_nonneg _), max_eq_right (norm_nonneg _)]

/-! ## 5. The target -/

theorem thetaM_lipschitz (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1)
    (hpos : Work.OddExistence.KdenPosOn h a b) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b,
      ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState σ) ρ,
      ∀ z' ∈ Metric.closedBall (Work.OddVolterra.baseState σ) ρ,
      ‖Work.OddExistence.ThetaM n h s σ z - Work.OddExistence.ThetaM n h s σ z'‖
        ≤ L * ‖z - z'‖ := by
  have hh' : ContDiff ℝ (⊤ : ℕ∞) h := hh
  obtain ⟨δ, hδ0, hδpos⟩ := exists_krad_pos_nhds hh' hab hpos
  -- smoothness of the manifest kernel on the open region
  have hcdK : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × St4) => Work.OddVolterra.KernelExt.ThetaM n h q.1 q.2.1 q.2.2)
      (thetaMRegion a b δ) :=
    contDiffOn_KernelExtThetaM_of_pos n hh' (isOpen_thetaMRegion a b δ)
      (thetaMRegion_pos hδpos) (thetaMRegion_pos_move hδpos)
  have hcdO : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × St4) => Work.OddExistence.ThetaM n h q.1 q.2.1 q.2.2)
      (thetaMRegion a b δ) := by
    refine hcdK.congr (fun q _ => ?_)
    exact ThetaM_eq_KernelExt n hh' q.1 q.2.1 q.2.2
  -- the differential is bounded on the compact region of the statement
  have hfderiv_cont : ContinuousOn
      (fderiv ℝ (fun q : ℝ × (ℝ × St4) => Work.OddExistence.ThetaM n h q.1 q.2.1 q.2.2))
      (thetaMRegion a b δ) :=
    hcdO.continuousOn_fderiv_of_isOpen (isOpen_thetaMRegion a b δ) (by simp)
  have hRcMsub : RcM a b ρ ⊆ thetaMRegion a b δ :=
    RcM_subset_thetaMRegion ha hab hb hρ1 hδ0
  obtain ⟨C, hC⟩ := (isCompact_RcM ha hab hb hρ0 hρ1).exists_bound_of_continuousOn
    (hfderiv_cont.mono hRcMsub)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro s hs σ hσ z hz z' hz'
  set F : ℝ × (ℝ × St4) → St4 :=
    fun q => Work.OddExistence.ThetaM n h q.1 q.2.1 q.2.2 with hFdef
  set S : Set (ℝ × (ℝ × St4)) := {q | q.1 = s ∧ q.2.1 = σ ∧
    q.2.2 ∈ Metric.closedBall (Work.OddVolterra.baseState σ) ρ} with hSdef
  have hSconv : Convex ℝ S := convex_slice s σ ρ
  have hSsub : S ⊆ thetaMRegion a b δ := by
    intro q hq
    obtain ⟨hq1, hq2, hq3⟩ := hq
    refine hRcMsub ⟨?_, ?_, ?_⟩
    · rw [hq1]; exact hs
    · rw [hq2]; exact hσ
    · rw [hq2]; exact hq3
  have hdiff : ∀ q ∈ S, DifferentiableAt ℝ F q := by
    intro q hq
    have hqU : q ∈ thetaMRegion a b δ := hSsub hq
    have hd := (hcdO.differentiableOn (by simp)).differentiableAt
      ((isOpen_thetaMRegion a b δ).mem_nhds hqU)
    simpa only [hFdef] using hd
  have hbound : ∀ q ∈ S, ‖fderiv ℝ F q‖ ≤ max C 0 := by
    intro q hq
    obtain ⟨hq1, hq2, hq3⟩ := hq
    have hqR : q ∈ RcM a b ρ :=
      ⟨by rw [hq1]; exact hs, by rw [hq2]; exact hσ, by rw [hq2]; exact hq3⟩
    have h := hC q hqR
    refine le_trans ?_ (le_max_left C 0)
    simpa only [hFdef] using h
  have hmem1 : ((s, σ, z) : ℝ × (ℝ × St4)) ∈ S := ⟨rfl, rfl, hz⟩
  have hmem2 : ((s, σ, z') : ℝ × (ℝ × St4)) ∈ S := ⟨rfl, rfl, hz'⟩
  have hmain := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound hSconv hmem2 hmem1
  have hfx : F (s, σ, z) = Work.OddExistence.ThetaM n h s σ z := by rw [hFdef]
  have hfx' : F (s, σ, z') = Work.OddExistence.ThetaM n h s σ z' := by rw [hFdef]
  rw [hfx, hfx'] at hmain
  calc ‖Work.OddExistence.ThetaM n h s σ z - Work.OddExistence.ThetaM n h s σ z'‖
      ≤ max C 0 * ‖((s, σ, z) : ℝ × (ℝ × St4)) - (s, σ, z')‖ := hmain
    _ = max C 0 * ‖z - z'‖ := by rw [norm_mk_sub_eq]

end

end Work.OddExistence.Manifest
