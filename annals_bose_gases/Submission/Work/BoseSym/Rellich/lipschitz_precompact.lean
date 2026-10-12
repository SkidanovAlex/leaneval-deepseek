import Mathlib
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym.Rellich — Lipschitz precompactness in `L²`

A sequence of real functions on configuration space which is uniformly bounded, uniformly
Lipschitz, and supported in a fixed compact set `K`, has a subsequence which is Cauchy in `L²`.

The proof is Arzelà–Ascoli on the compact set `K` (yielding a subsequence which is uniformly
Cauchy on `K`), followed by the elementary estimate `‖u‖_{L²} ≤ √(vol K) · sup|u|` for functions
`u` which vanish outside `K`.

## Main results

* `eq_zero_of_tsupport_subset`, `tsupport_sub_subset` : support bookkeeping;
* `eLpNorm_sub_le_of_tsupport`, `dist_toL2_le` : the `L²` estimate;
* `exists_sup_cauchy_subseq` : the Arzelà–Ascoli step;
* `lipschitz_precompact` : the target.
-/

namespace Work.BoseSym.Rellich

open MeasureTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Support bookkeeping -/

/-- A function whose topological support lies in `K` vanishes outside `K`. -/
lemma eq_zero_of_tsupport_subset {N : ℕ} {K : Set (Conf N)} {f : Conf N → ℝ}
    (h : tsupport f ⊆ K) {x : Conf N} (hx : x ∉ K) : f x = 0 := by
  by_contra hfx
  exact hx (h (subset_tsupport f (Function.mem_support.mpr hfx)))

/-- The topological support of a difference is contained in `K` as soon as both terms have
topological support contained in `K`. -/
lemma tsupport_sub_subset {N : ℕ} {K : Set (Conf N)} {f g : Conf N → ℝ}
    (hf : tsupport f ⊆ K) (hg : tsupport g ⊆ K) : tsupport (f - g) ⊆ K := by
  refine (closure_minimal ?_ ((isClosed_tsupport f).union (isClosed_tsupport g))).trans
    (Set.union_subset hf hg)
  exact (Function.support_sub f g).trans
    (Set.union_subset_union (subset_tsupport f) (subset_tsupport g))

/-! ## The `L²` estimate -/

/-- If `f - g` vanishes outside `K` and is pointwise bounded by `c ≥ 0`, then its `L²` seminorm is
at most `c · (vol K)^{1/2}`. -/
lemma eLpNorm_sub_le_of_tsupport {N : ℕ} {K : Set (Conf N)} {f g : Conf N → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hsupp : tsupport (f - g) ⊆ K) (hb : ∀ x, |f x - g x| ≤ c)
    (hm : AEStronglyMeasurable (f - g) (volC N)) :
    eLpNorm (f - g) 2 (volC N) ≤ ENNReal.ofReal c * (volC N K) ^ (1 / 2 : ℝ) := by
  set T := toMeasurable (volC N) K with hT
  calc eLpNorm (f - g) 2 (volC N)
      ≤ eLpNorm (T.indicator (fun _ => c)) 2 (volC N) := by
        refine eLpNorm_mono hm (fun x => ?_)
        by_cases hx : x ∈ K
        · rw [Set.indicator_of_mem (subset_toMeasurable _ _ hx)]
          simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hc]
          exact hb x
        · rw [eq_zero_of_tsupport_subset hsupp hx]
          simp
    _ ≤ ‖c‖ₑ * (volC N T) ^ (1 / (2 : ℝ≥0∞).toReal) :=
        eLpNorm_indicator_const_le c 2 (measurableSet_toMeasurable _ _).nullMeasurableSet
    _ = ENNReal.ofReal c * (volC N K) ^ (1 / 2 : ℝ) := by
        rw [hT, measure_toMeasurable, Real.enorm_eq_ofReal hc, ENNReal.toReal_ofNat]

/-- The `L²` distance of two functions whose difference vanishes outside `K` and is pointwise
bounded by `c`. -/
lemma dist_toL2_le {N : ℕ} {K : Set (Conf N)} {f g : Conf N → ℝ} {c : ℝ}
    (hf : IsL2 N f) (hg : IsL2 N g) (hc : 0 ≤ c) (hvol : (volC N) K ≠ ⊤)
    (hsupp : tsupport (f - g) ⊆ K) (hb : ∀ x, |f x - g x| ≤ c) :
    dist (toL2 N f hf) (toL2 N g hg) ≤ Real.sqrt ((volC N K).toReal) * c := by
  have hsub : MemLp (f - g) 2 (volC N) := hf.sub hg
  have hkey := eLpNorm_sub_le_of_tsupport hc hsupp hb hsub.aestronglyMeasurable
  have hfin : ENNReal.ofReal c * (volC N K) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hvol)
  have hreal : (eLpNorm (f - g) 2 (volC N)).toReal ≤
      Real.sqrt ((volC N K).toReal) * c := by
    calc (eLpNorm (f - g) 2 (volC N)).toReal
        ≤ (ENNReal.ofReal c * (volC N K) ^ (1 / 2 : ℝ)).toReal :=
          (ENNReal.toReal_le_toReal hsub.eLpNorm_lt_top.ne hfin).mpr hkey
      _ = Real.sqrt ((volC N K).toReal) * c := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, ← ENNReal.toReal_rpow,
            ← Real.sqrt_eq_rpow, mul_comm]
  have hgoal : dist (toL2 N f hf) (toL2 N g hg) = (eLpNorm (f - g) 2 (volC N)).toReal := by
    show dist (MemLp.toLp f hf) (MemLp.toLp g hg) = (eLpNorm (f - g) 2 (volC N)).toReal
    rw [dist_eq_norm, ← MemLp.toLp_sub hf hg]
    exact MeasureTheory.Lp.norm_toLp (f - g) (hf.sub hg)
  rw [hgoal]
  exact hreal

/-! ## The Arzelà–Ascoli step -/

/-- A uniformly bounded and uniformly Lipschitz family of functions has a subsequence which is
Cauchy for the sup norm on a compact set `K`. -/
lemma exists_sup_cauchy_subseq {N : ℕ} {B Λ : ℝ} {K : Set (Conf N)} (hK : IsCompact K)
    {v : ℕ → Conf N → ℝ} (hΛ : 0 ≤ Λ)
    (hb : ∀ n, BddBy N (v n) B) (hlip : ∀ n, LipsReal Λ (v n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ ε > 0, ∃ M, ∀ m ≥ M, ∀ n ≥ M, ∀ x : K,
      |v (φ m) x - v (φ n) x| < ε := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hcont : ∀ n, Continuous (v n) := fun n =>
    (LipschitzWith.of_dist_le' (fun x y => by rw [Real.dist_eq]; exact hlip n x y)).continuous
  let G : ℕ → C(K, ℝ) := fun n => ⟨fun x => v n x, (hcont n).comp continuous_subtype_val⟩
  let F : ℕ → (K →ᵇ ℝ) := fun n =>
    BoundedContinuousFunction.mkOfBound (G n) (2 * B) (by
      intro x y
      rw [Real.dist_eq]
      calc |v n x - v n y| ≤ |v n x| + |v n y| := by
            simpa [Real.dist_eq] using dist_triangle (v n x) 0 (v n y)
        _ ≤ B + B := add_le_add (hb n x) (hb n y)
        _ = 2 * B := by ring)
  have hcpt : IsCompact (closure (Set.range F)) := by
    refine BoundedContinuousFunction.arzela_ascoli (Set.Icc (-B) B) isCompact_Icc
      (Set.range F) ?_ ?_
    · intro f x hf
      obtain ⟨n, rfl⟩ := hf
      exact abs_le.mp (hb n x)
    · apply UniformEquicontinuous.equicontinuous
      rw [Metric.uniformEquicontinuous_iff]
      intro ε hε
      refine ⟨ε / (2 * (Λ + 1)), by positivity, fun x y hxy i => ?_⟩
      obtain ⟨n, hn⟩ := i.2
      have hidx : ((i : K →ᵇ ℝ) : K → ℝ) = fun z : K => v n z := by
        rw [← hn]
        rfl
      rw [hidx]
      calc |v n x - v n y| ≤ Λ * dist x y := hlip n x y
        _ ≤ Λ * (ε / (2 * (Λ + 1))) := mul_le_mul_of_nonneg_left (le_of_lt hxy) hΛ
        _ < ε := by
            have hpos : (0 : ℝ) < 2 * (Λ + 1) := by positivity
            have hstep : Λ * (ε / (2 * (Λ + 1))) = Λ * ε / (2 * (Λ + 1)) := by ring
            rw [hstep, div_lt_iff₀ hpos]
            nlinarith [hΛ, hε, mul_nonneg hΛ (le_of_lt hε)]
  obtain ⟨a, -, φ, hφ, htend⟩ :=
    hcpt.tendsto_subseq (x := fun n => F n) (fun n => subset_closure ⟨n, rfl⟩)
  refine ⟨φ, hφ, fun ε hε => ?_⟩
  have hcau : CauchySeq (F ∘ φ) := htend.cauchySeq
  rw [Metric.cauchySeq_iff] at hcau
  obtain ⟨M, hM⟩ := hcau ε hε
  refine ⟨M, fun m hm n hn x => ?_⟩
  have hd : dist ((F ∘ φ) m) ((F ∘ φ) n) < ε := hM m hm n hn
  have h2 := BoundedContinuousFunction.dist_coe_le_dist (f := (F ∘ φ) m) (g := (F ∘ φ) n) x
  have h3 : dist (v (φ m) x) (v (φ n) x) < ε := lt_of_le_of_lt h2 hd
  rwa [Real.dist_eq] at h3

/-! ## The target -/

theorem lipschitz_precompact {N : ℕ} {B Λ : ℝ} {K : Set (Conf N)} (hK : IsCompact K)
    {v : ℕ → Conf N → ℝ} (hv : ∀ n, IsL2 N (v n)) (hΛ : 0 ≤ Λ) (hb : ∀ n, BddBy N (v n) B)
    (hlip : ∀ n, LipsReal Λ (v n)) (hsup : ∀ n, tsupport (v n) ⊆ K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ CauchySeq (fun n => toL2 N (v (φ n)) (hv (φ n))) := by
  classical
  obtain ⟨φ, hφ, hcau⟩ := exists_sup_cauchy_subseq hK hΛ hb hlip
  have hvol : (volC N) K ≠ ⊤ := hK.measure_lt_top.ne
  refine ⟨φ, hφ, ?_⟩
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let C : ℝ := Real.sqrt ((volC N K)).toReal
  have hCnn : 0 ≤ C := Real.sqrt_nonneg _
  have hδpos : 0 < ε / (2 * (C + 1)) := by positivity
  obtain ⟨M, hM⟩ := hcau (ε / (2 * (C + 1))) hδpos
  refine ⟨M, fun m hm n hn => ?_⟩
  have hbd : ∀ x, |v (φ m) x - v (φ n) x| ≤ ε / (2 * (C + 1)) := by
    intro x
    by_cases hx : x ∈ K
    · exact le_of_lt (hM m hm n hn ⟨x, hx⟩)
    · rw [eq_zero_of_tsupport_subset (hsup (φ m)) hx,
        eq_zero_of_tsupport_subset (hsup (φ n)) hx, sub_zero, abs_zero]
      exact le_of_lt hδpos
  have h1 := dist_toL2_le (hv (φ m)) (hv (φ n)) (le_of_lt hδpos) hvol
    (tsupport_sub_subset (hsup (φ m)) (hsup (φ n))) hbd
  calc dist (toL2 N (v (φ m)) (hv (φ m))) (toL2 N (v (φ n)) (hv (φ n)))
      ≤ C * (ε / (2 * (C + 1))) := h1
    _ < ε := by
        have hpos : (0 : ℝ) < 2 * (C + 1) := by positivity
        have hstep : C * (ε / (2 * (C + 1))) = C * ε / (2 * (C + 1)) := by ring
        rw [hstep, div_lt_iff₀ hpos]
        nlinarith [hCnn, hε, mul_nonneg hCnn (le_of_lt hε)]

end

end Work.BoseSym.Rellich
