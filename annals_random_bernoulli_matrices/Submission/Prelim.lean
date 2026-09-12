/-
Preliminaries for the eq-aux / Littlewood–Offord layer of Tikhomirov (2020).

Local module `Submission.Prelim`:  fully proved facts that use the *local*
definition `Submission.Helpers.levyConcentration` (so they cannot be delegated
to the shared Commons, which must not depend on problem-specific files).
-/
import Mathlib
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Bernoulli
import Submission.Helpers
import Submission.Commons.Probability.Independence.iIndepFun_curry_flat_real
import ChallengeDeps

set_option autoImplicit false

namespace Submission.Prelim

noncomputable section

open Matrix MeasureTheory ProbabilityTheory Measure Filter unitInterval
open scoped ENNReal BigOperators

/-! ## Lévy concentration function: shift invariance and real bounds -/

/-- The Lévy concentration function is invariant under translations of the
random variable:  `cf(ξ + c, t) = cf(ξ, t)`. -/
theorem levyConcentration_shift {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : Ω → ℝ) (t c : ℝ) :
    Submission.Helpers.levyConcentration P (fun x => ξ x + c) t =
      Submission.Helpers.levyConcentration P ξ t := by
  classical
  unfold Submission.Helpers.levyConcentration
  apply congrArg sSup
  ext a
  constructor
  · rintro ⟨l, rfl⟩
    refine ⟨l - c, ?_⟩
    congr 1
    ext x
    change |ξ x + c - l| ≤ t ↔ |ξ x - (l - c)| ≤ t
    rw [show ξ x + c - l = ξ x - (l - c) by ring]
  · rintro ⟨l, rfl⟩
    refine ⟨l + c, ?_⟩
    congr 1
    ext x
    change |ξ x - l| ≤ t ↔ |ξ x + c - (l + c)| ≤ t
    rw [show ξ x + c - (l + c) = ξ x - l by ring]

/-- A real-valued bound on every interval mass follows from an ENNReal bound on
the concentration function. -/
theorem real_mem_le_of_levyConcentration_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (ξ : Ω → ℝ) {t : ℝ} {τ : ℝ} (hτ0 : 0 ≤ τ)
    (h : Submission.Helpers.levyConcentration P ξ t ≤ ENNReal.ofReal τ) (l : ℝ) :
    P.real {x : Ω | |ξ x - l| ≤ t} ≤ τ := by
  rw [Measure.real_def]
  have hle : P {x : Ω | |ξ x - l| ≤ t} ≤ ENNReal.ofReal τ :=
    le_trans (Submission.Helpers.le_levyConcentration P ξ t l) h
  have hfin : P {x : Ω | |ξ x - l| ≤ t} ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have htr := (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr hle
  simpa [ENNReal.toReal_ofReal hτ0] using htr

/-! ## The two-atom interval fact

The Bernoulli(p) law (atoms at `1` with mass `p` and at `0` with mass `1−p`)
puts on any interval of length `2r` at most the mass of a single atom whenever
the two atoms are farther than `2r` apart; for `p ≤ 1/2` that mass is `≤ 1−p`.
This is the per-coordinate "atom" fact used in the conditioning argument and as
the input to Lévy–Kolmogorov–Rogozin. -/

/-- An interval of length `2r` cannot contain two points at distance `> 2r`. -/
lemma interval_not_both {c x l r : ℝ} (hsep : 2 * r < |x|) :
    ¬ (|c - l| ≤ r ∧ |c + x - l| ≤ r) := by
  intro h
  have h0 : |c - l| ≤ r := h.1
  have h1 : |c + x - l| ≤ r := h.2
  have hx : |x| ≤ 2 * r := by
    calc
      |x| = |(c + x - l) - (c - l)| := by
        congr 1
        ring
      _ ≤ |c + x - l| + |c - l| := abs_sub _ _
      _ ≤ r + r := by linarith
      _ = 2 * r := by ring
  linarith

/-- Real mass of the interval capture set for the two-atom Bernoulli law. -/
theorem bernoulliLaw_interval_real_le {p : I} (hp : (p : ℝ) ≤ 1 / 2) {c x l r : ℝ}
    (hsep : 2 * r < |x|) :
    (bernoulliMeasure 1 0 p).real {a : ℝ | |c + a * x - l| ≤ r} ≤ 1 - p := by
  classical
  let S : Set ℝ := {a : ℝ | |c + a * x - l| ≤ r}
  have hcont : Continuous fun a : ℝ => c + a * x - l := by fun_prop
  have hmeas : MeasurableSet S := by
    have hset : S = (fun a : ℝ => |c + a * x - l|) ⁻¹' Set.Iic r := by
      ext a
      simp [S, Set.mem_Iic]
    rw [hset]
    exact (isClosed_Iic.measurableSet : MeasurableSet (Set.Iic r)).preimage (hcont.abs.measurable)
  have h0 : (0 : ℝ) ∈ S ↔ |c - l| ≤ r := by
    simp [S]
  have h1 : (1 : ℝ) ∈ S ↔ |c + x - l| ≤ r := by
    simp [S]
  by_cases h1m : (1 : ℝ) ∈ S
  · -- atom 1 inside, atom 0 outside
    have h0out : (0 : ℝ) ∉ S := by
      intro h0in
      exact interval_not_both hsep ⟨(h0.mp h0in), (h1.mp h1m)⟩
    rw [bernoulliMeasure_real_apply_of_mem_of_notMem p hmeas h1m h0out]
    linarith [hp]
  · by_cases h0m : (0 : ℝ) ∈ S
    · rw [bernoulliMeasure_real_apply_of_notMem_of_mem p hmeas h1m h0m]
    · rw [bernoulliMeasure_real_apply_of_notMem_of_notMem p hmeas h1m h0m]
      have hpm : (p : ℝ) ≤ 1 := by linarith [hp]
      linarith

/-- Lift a real-valued upper bound on the real mass of a measurable set (in a
probability space) to an ENNReal bound. -/
lemma measure_le_ofReal_of_real_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [MeasureTheory.IsProbabilityMeasure μ] {s : Set α} (_hs : MeasurableSet s) {τ : ℝ}
    (_hτ : 0 ≤ τ) (hreal : μ.real s ≤ τ) : μ s ≤ ENNReal.ofReal τ := by
  have hslt : μ s ≠ ⊤ := measure_ne_top μ s
  calc
    μ s = ENNReal.ofReal (μ.real s) := by
      rw [Measure.real_def]
      exact (ENNReal.ofReal_toReal hslt).symm
    _ ≤ ENNReal.ofReal τ := ENNReal.ofReal_le_ofReal hreal

/-- ENNReal version of the two-atom interval bound. -/
theorem bernoulliLaw_interval_le {p : I} (hp : (p : ℝ) ≤ 1 / 2) {c x l r : ℝ}
    (hsep : 2 * r < |x|) :
    (bernoulliMeasure 1 0 p) {a : ℝ | |c + a * x - l| ≤ r} ≤ ENNReal.ofReal (1 - p) := by
  have hmeas : MeasurableSet {a : ℝ | |c + a * x - l| ≤ r} := by
    have hcont : Continuous (fun a : ℝ => c + a * x - l) := by fun_prop
    have hset : {a : ℝ | |c + a * x - l| ≤ r} =
        (fun a : ℝ => |c + a * x - l|) ⁻¹' Set.Iic r := by
      ext a
      simp [Set.mem_Iic]
    rw [hset]
    exact (isClosed_Iic.measurableSet : MeasurableSet (Set.Iic r)).preimage
      (hcont.abs.measurable)
  exact measure_le_ofReal_of_real_le (bernoulliMeasure 1 0 p) hmeas (by
    have hp1 : (p : ℝ) ≤ 1 := p.property.2
    linarith) (bernoulliLaw_interval_real_le hp hsep)

/-- Two independent real random variables `U` and `V`, with `V` Bernoulli(p)
(atom `1` of mass `p`, atom `0` of mass `1−p`), have their `U + V·x` value
captured by any interval of length `2r < |x|` with probability at most `1−p`.
This is the conditioning/atom step of the Littlewood–Offord dichotomy
(Tikhomirov 2020, "eq aux", large-coordinate case). -/
theorem indep_two_atom_real_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] {U V : Ω → ℝ} (hU : AEMeasurable U P)
    (hV : AEMeasurable V P) (hind : ProbabilityTheory.IndepFun U V P)
    {p : I} (hVlaw : P.map V = bernoulliMeasure 1 0 p) (hp : (p : ℝ) ≤ 1 / 2)
    {x l r : ℝ} (hsep : 2 * r < |x|) :
    P.real {ω : Ω | |U ω + V ω * x - l| ≤ r} ≤ 1 - p := by
  classical
  let A : Set (ℝ × ℝ) := {z : ℝ × ℝ | |z.1 + z.2 * x - l| ≤ r}
  let E : Set Ω := {ω : Ω | |U ω + V ω * x - l| ≤ r}
  have hAm : MeasurableSet A := by
    have hg : Continuous (fun z : ℝ × ℝ => |z.1 + z.2 * x - l|) := by
      refine continuous_abs.comp ?_
      refine Continuous.sub ?_ continuous_const
      refine Continuous.add continuous_fst ?_
      exact continuous_snd.mul continuous_const
    have hset : A = (fun z : ℝ × ℝ => |z.1 + z.2 * x - l|) ⁻¹' Set.Iic r := by
      ext z
      simp [A, Set.mem_Iic]
    rw [hset]
    exact (isClosed_Iic.measurableSet : MeasurableSet (Set.Iic r)).preimage hg.measurable
  have hE : E = (fun ω => (U ω, V ω)) ⁻¹' A := by
    ext ω
    simp [E, A]
  haveI : MeasureTheory.IsProbabilityMeasure (P.map U) :=
    Measure.isProbabilityMeasure_map hU
  haveI : MeasureTheory.IsProbabilityMeasure (P.map V) :=
    Measure.isProbabilityMeasure_map hV
  have hPair : AEMeasurable (fun ω => (U ω, V ω)) P := hU.prodMk hV
  have hjoint : P.map (fun ω => (U ω, V ω)) = (P.map U).prod (P.map V) :=
    (indepFun_iff_map_prod_eq_prod_map_map (f := U) (g := V) hU hV).1 hind
  have hPE : P E ≤ ENNReal.ofReal (1 - p) := by
    calc
      P E = P ((fun ω => (U ω, V ω)) ⁻¹' A) := by rw [hE]
      _ = (P.map (fun ω => (U ω, V ω))) A :=
            (Measure.map_apply_of_aemeasurable hPair hAm).symm
      _ = ((P.map U).prod (P.map V)) A := by rw [hjoint]
      _ = ∫⁻ c : ℝ, (P.map V) (Prod.mk c ⁻¹' A) ∂(P.map U) := by
            exact Measure.prod_apply hAm
      _ ≤ ∫⁻ c : ℝ, ENNReal.ofReal (1 - p) ∂(P.map U) := by
            exact lintegral_mono (fun c => by
              have hfiber : (P.map V) (Prod.mk c ⁻¹' A) ≤ ENNReal.ofReal (1 - p) := by
                have hset : Prod.mk c ⁻¹' A = {a : ℝ | |c + a * x - l| ≤ r} := by
                  ext a
                  simp [A]
                rw [hset, hVlaw]
                exact bernoulliLaw_interval_le hp hsep
              exact hfiber)
      _ = ENNReal.ofReal (1 - p) * (P.map U) Set.univ := lintegral_const _
      _ = ENNReal.ofReal (1 - p) := by
            simp
  rw [Measure.real_def]
  have htop : P E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hPE
  have htr := (ENNReal.toReal_le_toReal htop ENNReal.ofReal_ne_top).mpr hPE
  have h01 : 0 ≤ 1 - (p : ℝ) := by
    have hp1 : (p : ℝ) ≤ 1 := p.property.2
    linarith
  simpa [E, ENNReal.toReal_ofReal h01] using htr


/-- Large-coordinate case of the Littlewood–Offord dichotomy for weighted
Bernoulli sums (`eq aux` in Tikhomirov 2020): if one weight `x j` satisfies
`2r < |x j|`, then conditioning on all other entries shows every interval of
length `2r` captures the sum with probability at most `1−p`. -/
theorem bernoulli_weighted_sum_large_coord_le {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P] {b : Fin n → Ω → ℝ}
    (hb_meas : ∀ i, Measurable (b i)) (hb_indep : iIndepFun b P)
    {p : I} (hb_law : ∀ i, HasLaw (b i) (bernoulliMeasure 1 0 p) P)
    {x : Fin n → ℝ} {r : ℝ} (hp : (p : ℝ) ≤ 1 / 2)
    (hsep : ∃ j : Fin n, 2 * r < |x j|) :
    ∀ l : ℝ, P.real {ω : Ω | |(∑ i : Fin n, b i ω * x i) - l| ≤ r} ≤ 1 - p := by
  classical
  intro l
  rcases hsep with ⟨j, hxj⟩
  let S : Finset (Fin n) := Finset.univ.erase j
  let U : Ω → ℝ := fun ω => ∑ i : S, b i.1 ω * x i.1
  have hUmeas : Measurable U := by
    dsimp [U]
    fun_prop
  have hUae : AEMeasurable U P := hUmeas.aemeasurable
  have hdisj : Disjoint S ({j} : Finset (Fin n)) := by
    rw [Finset.disjoint_left]
    intro k hkS hkj
    have hk : k = j := Finset.mem_singleton.mp hkj
    have hkne : k ≠ j := (Finset.mem_erase.mp hkS).1
    exact hkne hk
  have hind_pair : ProbabilityTheory.IndepFun U (b j) P := by
    have htuples : ProbabilityTheory.IndepFun
        (fun a (i : S) => b i.1 a) (fun a (i : ({j} : Finset (Fin n))) => b i.1 a) P :=
      iIndepFun.indepFun_finset S ({j} : Finset (Fin n)) hdisj hb_indep hb_meas
    have hφ : Measurable fun u : S → ℝ => ∑ i : S, u i * x i.1 := by fun_prop
    have hψ : Measurable fun t : ({j} : Finset (Fin n)) → ℝ => t ⟨j, Finset.mem_singleton.mpr rfl⟩ := by
      fun_prop
    simpa [U, Function.comp_def] using (ProbabilityTheory.IndepFun.comp htuples hφ hψ)
  have hVae : AEMeasurable (b j) P := (hb_meas j).aemeasurable
  have hsplit : ∀ ω : Ω, (∑ i : Fin n, b i ω * x i) = U ω + b j ω * x j := by
    intro ω
    have hmem : j ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ j
    calc
      (∑ i : Fin n, b i ω * x i) = ∑ i ∈ (Finset.univ : Finset (Fin n)), b i ω * x i := by simp
      _ = (∑ i ∈ (Finset.univ.erase j), b i ω * x i) + b j ω * x j := by
            exact (Finset.sum_erase_add (Finset.univ : Finset (Fin n)) (fun i => b i ω * x i) hmem).symm
      _ = (∑ i : S, b i.1 ω * x i.1) + b j ω * x j := by
            rw [← Finset.sum_coe_sort S (fun i : Fin n => b i ω * x i)]
  have hset : {ω : Ω | |(∑ i : Fin n, b i ω * x i) - l| ≤ r} =
      {ω : Ω | |U ω + b j ω * x j - l| ≤ r} := by
    ext ω
    change |(∑ i : Fin n, b i ω * x i) - l| ≤ r ↔ |U ω + b j ω * x j - l| ≤ r
    rw [hsplit ω]
  rw [hset]
  exact indep_two_atom_real_le P hUae hVae hind_pair (hb_law j).map_eq hp hxj


/-- Independent rows of an independent-entry family: if the flat family
`X i j` is independent (over pairs), then the affine row statistics
`Σ_j X i j * x j + c` are independent over `i`.  This is the row-block
independence step used to apply the tensorization lemma to the row sums of a
Bernoulli matrix. -/
theorem iIndepFun_rows_affineSum {ι κ Ω : Type*} [Fintype κ] [MeasurableSpace Ω] {P : Measure Ω}
    (X : ι → κ → Ω → ℝ) (mX : ∀ i j, Measurable (X i j))
    (hflat : iIndepFun (fun p : ι × κ => X p.1 p.2) P) (x : κ → ℝ) (c : ℝ) :
    iIndepFun (fun i ω => (∑ j : κ, X i j ω * x j) + c) P := by
  let G : (κ → ℝ) → ℝ := fun v => (∑ j : κ, v j * x j) + c
  have hG : Measurable G := by
    dsimp [G]
    fun_prop
  have hgrouped : iIndepFun (fun i ω => fun j : κ => X i j ω) P :=
    Commons.Probability.Independence.iIndepFun_curry_flat_real X mX hflat
  have h := ProbabilityTheory.iIndepFun.comp hgrouped (fun _ => G) (fun _ => hG)
  -- (G ∘ (fun ω j => X i j ω)) = (fun ω => (∑ j, X i j ω * x j) + c)
  simpa [Function.comp_def, G] using h

end

end Submission.Prelim
