import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.charVal_props
import Submission.Work.EQ.component_shiftZ_invariant
import Submission.Work.EQ.LAFree
import Submission.Work.EQ.limit_analysis_free

/-! # Collision-free copy of `Submission.Work.EQ.minimal_cycle_analysis`

See `Submission.Work.EQ.LAFree`: the same proof in the namespace `Work.EQ.MCAFree`, with its single
use of `Work.EQ.limit_analysis` re-pointed to `Work.EQ.LAFree.limit_analysis`. -/

namespace Work.EQ.MCAFree

open Complex Filter _root_.Topology
open scoped Topology

noncomputable section

/-! ## Elementary facts about `λ = eqLam a` -/

lemma mca_eqLam_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < eqLam a := by
  rw [eqLam]; exact div_pos (by linarith) (by linarith)

lemma mca_eqLam_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : eqLam a < 1 := by
  rw [eqLam, div_lt_one (by linarith)]; linarith

lemma mca_eqLamC_ne_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ((eqLam a : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (mca_eqLam_pos ha0 ha1))

lemma mca_norm_ofReal (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  have h1 : ‖(x : ℂ)‖ ^ 2 = x ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
  calc ‖(x : ℂ)‖ = Real.sqrt (‖(x : ℂ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (x ^ 2) := by rw [h1]
    _ = |x| := Real.sqrt_sq_eq_abs x

/-! ## The `CharSet` norm facts -/

lemma mca_charSet_norm_le_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {μ : ℂ} (hμ : μ ∈ CharSet a h) : ‖μ‖ ≤ 1 := by
  rw [CharSet, Set.mem_union] at hμ
  rcases hμ with h1 | h2
  · rw [Set.mem_singleton_iff] at h1
    rw [h1]; norm_num
  · obtain ⟨ε, hε, hμeq⟩ := h2
    rw [hμeq]
    obtain ⟨d, hd, hprops, hq⟩ := charVal_props (a := a) (h := h) (r := r) ha0 ha1 hh
    obtain ⟨him, hre0, hre1, hre2⟩ := hprops ε hε
    have hcast : charVal a h ε = (((charVal a h ε).re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    rw [hcast, mca_norm_ofReal, abs_of_pos hre0]
    exact hre1

lemma mca_charSet_norm_eq_one_iff {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {μ : ℂ} (hμ : μ ∈ CharSet a h) : ‖μ‖ = 1 ↔ μ = 1 := by
  constructor
  · intro h1
    rw [CharSet, Set.mem_union] at hμ
    rcases hμ with h | h
    · rwa [Set.mem_singleton_iff] at h
    · obtain ⟨ε, hε, hμeq⟩ := h
      rw [hμeq] at h1 ⊢
      obtain ⟨d, hd, hprops, hq⟩ := charVal_props (a := a) (h := h) (r := r) ha0 ha1 hh
      obtain ⟨him, hre0, hre1, hre2⟩ := hprops ε hε
      have hcast : charVal a h ε = (((charVal a h ε).re : ℝ) : ℂ) := by
        apply Complex.ext
        · simp
        · simpa using him
      rw [hcast, mca_norm_ofReal, abs_of_pos hre0] at h1
      rw [hcast, h1]; norm_num
  · intro h; rw [h]; norm_num

lemma mca_charSet_norm_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {μ : ℂ} (hμ : μ ∈ CharSet a h) (hne : μ ≠ 1) : ‖μ‖ < 1 := by
  rcases lt_or_eq_of_le (mca_charSet_norm_le_one ha0 ha1 hh hμ) with h | h
  · exact h
  · exact absurd ((mca_charSet_norm_eq_one_iff ha0 ha1 hh hμ).mp h) hne

lemma mca_charSet_mul_norm_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {μ₁ μ₂ : ℂ} (h1 : μ₁ ∈ CharSet a h) (h2 : μ₂ ∈ CharSet a h)
    (hne : μ₁ ≠ 1 ∨ μ₂ ≠ 1) : ‖μ₁ * μ₂‖ < 1 := by
  have hb1 := mca_charSet_norm_le_one ha0 ha1 hh h1
  have hb2 := mca_charSet_norm_le_one ha0 ha1 hh h2
  have hn1 : 0 ≤ ‖μ₁‖ := norm_nonneg _
  have hn2 : 0 ≤ ‖μ₂‖ := norm_nonneg _
  rw [norm_mul]
  rcases hne with hne | hne
  · have hs := mca_charSet_norm_lt_one ha0 ha1 hh h1 hne
    nlinarith [hn1, hn2, hb2, hs]
  · have hs := mca_charSet_norm_lt_one ha0 ha1 hh h2 hne
    nlinarith [hn1, hn2, hb1, hs]

/-! ## Finiteness of the set of words of a fixed length -/

def mca_words (N : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (Fin N → Bool)).image (fun f => List.ofFn f)

lemma mca_mem_words {N : ℕ} {l : List Bool} : l ∈ mca_words N ↔ l.length = N := by
  constructor
  · intro h
    obtain ⟨f, hf1, hf⟩ := Finset.mem_image.mp h
    rw [← hf, List.length_ofFn]
  · intro h
    refine Finset.mem_image.mpr
      ⟨fun i : Fin N => l.get (Fin.cast h.symm i), Finset.mem_univ _, ?_⟩
    have key := (List.ofFn_congr h l.get).symm
    rw [List.ofFn_get l] at key
    exact key

lemma mca_wordSet_finite {a : ℝ} {h : ℂ → ℂ} {S : Set ChainData} {r₁ r₂ : ℝ} {N : ℕ} :
    ∃ E : Finset (List Bool × List Bool), WordSet a h S r₁ r₂ N ⊆ ↑E := by
  refine ⟨mca_words N ×ˢ mca_words N, ?_⟩
  intro e he
  simp only [WordSet, Set.mem_ofPred_eq] at he
  exact Finset.mem_coe.mpr (Finset.mem_product.mpr
    ⟨mca_mem_words.mpr he.1, mca_mem_words.mpr he.2.1⟩)

/-! ## Shifting along `ψ₁` -/

lemma mca_isChain_of_mem_H0 {a : ℝ} {h : ℂ → ℂ} {p : ChainData} (hp : p ∈ H0 a h) :
    IsChain a h p := by
  obtain ⟨ε, hε, f, hcont, hf0, hfam⟩ := hp
  have hmem : p.2.1 ∈ Metric.ball p.2.1 ε := by
    rw [Metric.mem_ball, dist_self]; exact hε
  rw [← hf0]
  exact (hfam p.2.1 hmem).1

lemma mca_psi1_ne_zero {a : ℝ} {h : ℂ → ℂ} {p : ChainData} (hp : p ∈ H0 a h) : p.2.1 ≠ 0 :=
  (mca_isChain_of_mem_H0 hp).2.1

lemma mca_psi_shiftZ {a : ℝ} (hlam : ((eqLam a : ℝ) : ℂ) ≠ 0) (j : ℤ) (q : ChainData) :
    (shiftZ a j q).2.1 * (shiftZ a j q).2.2 = q.2.1 * q.2.2 := by
  rw [shiftZ_psi1, shiftZ_psi2]
  have hz : (((eqLam a : ℝ) : ℂ)) ^ j ≠ 0 := zpow_ne_zero j hlam
  field_simp

lemma mca_shiftZ_component {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {p : ChainData} (hp : p ∈ H0 a h) (j : ℤ) :
    connectedComponentIn (H0 a h) (shiftZ a j p)
      = shiftZ a j '' connectedComponentIn (H0 a h) p := by
  let e : ChainData ≃ₜ ChainData :=
    { toFun := shiftZ a j
      invFun := shiftZ a (-j)
      left_inv := fun q => (shiftZ_neg_apply ha0 ha1 j q).2
      right_inv := fun q => (shiftZ_neg_apply ha0 ha1 j q).1
      continuous_toFun := continuous_shiftZ a j
      continuous_invFun := continuous_shiftZ a (-j) }
  have himg : e '' (H0 a h) = H0 a h := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro q ⟨s, hs, rfl⟩
      exact mem_H0_shiftZ ha0 ha1 hs j
    · intro q hq
      exact ⟨shiftZ a (-j) q, mem_H0_shiftZ ha0 ha1 hq (-j),
        (shiftZ_neg_apply ha0 ha1 j q).1⟩
  have h1 := Homeomorph.image_connectedComponentIn e (s := H0 a h) hp
  rw [himg] at h1
  rw [show e p = shiftZ a j p from rfl] at h1
  exact h1.symm

/-! ## The annulus setup -/

lemma mca_exists_annulus {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {r ρ δ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hδ : 0 < δ) :
    ∃ r₁ r₂ : ℝ, ∃ N : ℕ, 0 < r₁ ∧ r₁ < r₂ ∧ r₂ < δ ∧ r₂ / r₁ > 1 / eqLam a ∧
      (eqLam a : ℝ) ^ N * r₂ < r ∧ (eqLam a : ℝ) ^ N * ρ / r₁ < r ∧
      (eqLam a : ℝ) ^ N * r₂ < δ ∧ (eqLam a : ℝ) ^ N * (2 * ρ) / r₁ < δ := by
  have hlam0 : 0 < eqLam a := mca_eqLam_pos ha0 ha1
  have hlam1 : eqLam a < 1 := mca_eqLam_lt_one ha0 ha1
  set r₂ : ℝ := δ / 2 with hr₂def
  set r₁ : ℝ := eqLam a * δ / 4 with hr₁def
  have hr₁0 : 0 < r₁ := by rw [hr₁def]; positivity
  have hr₂0 : 0 < r₂ := by rw [hr₂def]; linarith
  have hr₁r₂ : r₁ < r₂ := by rw [hr₁def, hr₂def]; nlinarith
  have hr₂δ : r₂ < δ := by rw [hr₂def]; linarith
  have hratio : r₂ / r₁ > 1 / eqLam a := by
    rw [hr₁def, hr₂def, gt_iff_lt]
    have hdiv : δ / 2 / (eqLam a * δ / 4) = 2 / eqLam a := by
      field_simp; ring
    rw [hdiv]
    rw [div_lt_div_iff_of_pos_right hlam0]
    norm_num
  have hC : 0 < max r₂ (2 * ρ / r₁) := lt_of_lt_of_le hr₂0 (le_max_left _ _)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (eqLam a : ℝ) ^ N * max r₂ (2 * ρ / r₁) < min r δ := by
    have hz : Tendsto (fun k : ℕ => (eqLam a : ℝ) ^ k * max r₂ (2 * ρ / r₁)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0.le hlam1).mul_const
        (max r₂ (2 * ρ / r₁))
    exact (hz.eventually (isOpen_Iio.mem_nhds (lt_min hr hδ))).exists
  refine ⟨r₁, r₂, N, hr₁0, hr₁r₂, hr₂δ, hratio, ?_, ?_, ?_, ?_⟩
  · have h1 : (eqLam a : ℝ) ^ N * r₂ ≤ (eqLam a : ℝ) ^ N * max r₂ (2 * ρ / r₁) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (pow_nonneg hlam0.le N)
    linarith [hN, min_le_left r δ]
  · have h1 : (eqLam a : ℝ) ^ N * ρ / r₁ ≤ (eqLam a : ℝ) ^ N * max r₂ (2 * ρ / r₁) := by
      rw [mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hlam0.le N)
      have hρr : 0 < ρ / r₁ := div_pos hρ hr₁0
      calc ρ / r₁ ≤ 2 * (ρ / r₁) := by linarith
        _ = 2 * ρ / r₁ := by ring
        _ ≤ max r₂ (2 * ρ / r₁) := le_max_right _ _
    linarith [hN, min_le_left r δ]
  · have h1 : (eqLam a : ℝ) ^ N * r₂ ≤ (eqLam a : ℝ) ^ N * max r₂ (2 * ρ / r₁) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (pow_nonneg hlam0.le N)
    linarith [hN, min_le_right r δ]
  · have h1 : (eqLam a : ℝ) ^ N * (2 * ρ) / r₁ ≤ (eqLam a : ℝ) ^ N * max r₂ (2 * ρ / r₁) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (pow_nonneg hlam0.le N)
    linarith [hN, min_le_right r δ]


/-- **The variational analysis of Rychlik's Thm 8: existence and finiteness of the minimal
cycle.**

If some component of `⁰H` is regular and `ρ* = ⨅{‖c‖ : c is the value of a regular component}`
is positive, then `ρ*` is attained, there are only finitely many regular components with
`‖c‖ = ρ*`, and over a suitable annulus the stable/unstable words of all these components take
only finitely many values (with `N` and the annulus meeting the smallness conditions of
`compact_mod_punctures_of_words`).

**Route (`PAPER_PROOFS.md` §5, Rychlik Thm 8).**  Write `Σ = RegValues a h`, `ρ* = rhoStar a h`
and fix a small radius `δ` (minimum of the radii of `fan_estimates`, `fan_trichotomy`,
`charVal_props`, `germC_facts`).  For `c₀` with `‖c₀‖ ≤ 2ρ*` choose an annulus
`A = Ann r₁ r₂ ⊂ ball 0 δ` with `r₂/r₁ > 1/λ` and `N` with `λ^N r₂ < r`,
`λ^N·2ρ*/r₁ < r` (possible since `λ < 1`).

*Reading a chain over `A`.*  For `q ∈ H0` with `ψ₁ q ∈ A` and `ψ(q) = c` with `‖c‖ ≤ 2ρ*`, the
tails at depth `N` are the germs, so `chain_read` (`exists_compact_regular_cycle`,
`Work.EQ.chain_read`) gives a stable word `ε` of length `N` with `q 0 = fan ε (ψ₁ q)` and an
unstable word `η` with `q(-N) = mirror (fan η (λ^N ψ₂ q))` (use `σ^j` to bring `ψ₁` into `A`;
`σ` preserves `ψ` and maps regular components to regular components with the same value).

*Lemma 5.1 (limits over `A`).*  Let `x_n ∈ H0` have `ψ₁ x_n ∈ A`, lie on regular components with
values `c_n → c₀`, and apply `fan_trichotomy` to `(ε_n)` and (jointly, on a common subsequence) to
`(η_n)`.

* Case (iii) on either side is impossible: it forces the step from index `-N` to `0` to run from
  an unstable-`1/4`-near axis point to a stable-`η`-near point with `η` arbitrarily small, which
  `no_near_axis_segment` forbids (the other end is `1/4`-near by `fan_estimates`, resp. its
  mirror).
* Case (ii) on either side gives, by `exists_regular_of_family` applied to the limit family
  `u z = μ₁ z`, `v z = μ₂ c₀/z` (with `μ₁`, `μ₂ ∈ CharSet` and at least one `≠ 1`), a regular
  component with value `c₀·μ₁·μ₂`.  To get the family: continue the local sections of `H0`
  (`H0_structure`: they are analytic in `ψ₁` on the component); the identity
  "index `-N` point `= mirror (fan η_n (λ^N c_n/z))`" holds on a disc by the identity theorem;
  apply `backward_puiseux` (F3) to the limit stable end `fan ε₀ (μ₁ ·)`, whose finitely many
  branches must match the limit unstable end identically on a disc, and use `exists_regular_of_family`
  (`u` is nonconstant, `c = c₀μ₁μ₂`).
* Case (i) on both sides: the words are fixed (`fan ε_n = fan ε₀`, `fan η_n = fan η₀` on a ball),
  hence the chains over a fixed disc are `candChain a h ε₀ η₀ s N c_n z` for `s ∈ {false,true}^N`;
  matching at index `-N` forces `fan η₀(w) = fan η₀(w·c_n/c_n')`, so `c_n = c_n'` by the
  nonvanishing of `deriv (fan η₀ ·).2 0` (`fan_snd_deriv_ne_zero`).  Hence finitely many values
  and finitely many components.

*Conclusion.*  Let `c_n ∈ Σ` with `‖c_n‖ → ρ*`.  Lemma 5.1 gives either (ii) a value of modulus
`≤ ρ*·μ_max < ρ*` (`charVal_props`: characteristic values are real in `(0,1]`, equal `1` only for
the principal leaf, and only finitely many exceed any positive bound, so the ones `< 1` are
bounded away from `1`), contradicting the definition of `ρ*`, or (i) finitely many values, which
makes `c_n` eventually constant: `ρ*` is attained.  Repeating the argument for the sequence of
minimal components with `c_n ≡ c₀` gives finitely many of them, and the finiteness of the sets of
words over `A` for each of them (again by the trichotomy: an infinite set of word pairs gives (iii)
or (ii), both impossible here — (ii) would produce a value of modulus `< ρ*`). -/
theorem minimal_cycle_analysis {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (hpos : 0 < rhoStar a h)
    (hreg : ∃ S : Set ChainData, ∃ c : ℂ, IsRegComp a h S c) :
    ∃ (r₁ r₂ : ℝ) (N m : ℕ) (S : Fin m → Set ChainData) (c : Fin m → ℂ),
      0 < m ∧ 0 < r₁ ∧ r₁ < r₂ ∧ r₂ / r₁ > 1 / eqLam a ∧
      (eqLam a : ℝ) ^ N * r₂ < r ∧ (eqLam a : ℝ) ^ N * rhoStar a h / r₁ < r ∧
      (∀ i, IsRegComp a h (S i) (c i) ∧ ‖c i‖ = rhoStar a h) ∧
      (∀ S' : Set ChainData, ∀ c' : ℂ, IsRegComp a h S' c' → ‖c'‖ = rhoStar a h →
        ∃ i, S' = S i) ∧
      ∃ E : Finset (List Bool × List Bool), ∀ i, WordSet a h (S i) r₁ r₂ N ⊆ ↑E := by
  have hr : 0 < r := hh.1
  have hρ : 0 < rhoStar a h := hpos
  -- the lower bound on `‖ψ‖` over regular components
  have hle : ∀ c : ℂ, c ∈ RegValues a h → rhoStar a h ≤ ‖c‖ := by
    intro c hc
    refine csInf_le ⟨0, fun x hx => ?_⟩ ⟨c, hc, rfl⟩
    obtain ⟨c', hc', rfl⟩ := hx
    exact norm_nonneg c'
  -- from a value to a component
  have hcomp : ∀ c : ℂ, c ∈ RegValues a h → ∃ S : Set ChainData, IsRegComp a h S c := by
    intro c hc
    obtain ⟨p, hp, hv⟩ := hc
    exact ⟨connectedComponentIn (H0 a h) p, connectedComponentIn_subset _ _, ⟨p, hp, rfl⟩, hv⟩
  -- from a component to a value
  have hval : ∀ S : Set ChainData, ∀ c : ℂ, IsRegComp a h S c → c ∈ RegValues a h := by
    intro S c hS
    obtain ⟨hsub, hpc, hvall⟩ := hS
    obtain ⟨p, hp, hSeq⟩ := hpc
    exact ⟨p, hp, fun q hq => hvall q (by rw [hSeq]; exact hq)⟩
  have hVne : ({x : ℝ | ∃ c : ℂ, c ∈ RegValues a h ∧ x = ‖c‖}).Nonempty := by
    obtain ⟨S, c, hS⟩ := hreg
    exact ⟨‖c‖, c, hval S c hS, rfl⟩
  -- an approximating sequence of values
  obtain ⟨c, hc1, hc2, hc3⟩ : ∃ c : ℕ → ℂ, (∀ n, c n ∈ RegValues a h) ∧
      (∀ n, ‖c n‖ ≤ 2 * rhoStar a h) ∧
      Tendsto (fun n : ℕ => ‖c n‖) atTop (𝓝 (rhoStar a h)) := by
    have hex : ∀ n : ℕ, ∃ d : ℂ, d ∈ RegValues a h ∧
        ‖d‖ < rhoStar a h + min (1 / (n + 1 : ℝ)) (rhoStar a h) := by
      intro n
      have hlt : rhoStar a h < rhoStar a h + min (1 / (n + 1 : ℝ)) (rhoStar a h) := by
        have hmm : 0 < min (1 / (n + 1 : ℝ)) (rhoStar a h) := lt_min (by positivity) hρ
        linarith
      obtain ⟨v, hv, hltv⟩ := exists_lt_of_csInf_lt hVne hlt
      obtain ⟨d, hd, rfl⟩ := hv
      exact ⟨d, hd, hltv⟩
    choose d hd1 hd2 using hex
    refine ⟨d, hd1, ?_, ?_⟩
    · intro n
      have h1 : min (1 / (n + 1 : ℝ)) (rhoStar a h) ≤ rhoStar a h := min_le_right _ _
      linarith [hd2 n, h1]
    · have hu : Tendsto (fun n : ℕ => ‖d n‖ - rhoStar a h) atTop (𝓝 0) := by
        refine squeeze_zero (g := fun n : ℕ => 1 / (n + 1 : ℝ)) ?_ ?_ ?_
        · intro n; linarith [hle (d n) (hd1 n)]
        · intro n
          have h1 : min (1 / (n + 1 : ℝ)) (rhoStar a h) ≤ 1 / (n + 1 : ℝ) := min_le_left _ _
          linarith [hd2 n, h1]
        · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have h2 : Tendsto (fun n : ℕ => (‖d n‖ - rhoStar a h) + rhoStar a h) atTop
          (𝓝 (0 + rhoStar a h)) := hu.add_const (rhoStar a h)
      simpa [sub_add_cancel, zero_add] using h2
  -- extract a convergent subsequence of the values
  obtain ⟨c₀, hc₀mem, φ, hφmono, hφlim⟩ :=
    (isCompact_closedBall (0 : ℂ) (2 * rhoStar a h)).tendsto_subseq (x := c) fun n => by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hc2 n
  have hc₀norm : ‖c₀‖ = rhoStar a h := by
    have h1 : Tendsto (fun n : ℕ => ‖c (φ n)‖) atTop (𝓝 ‖c₀‖) := hφlim.norm
    have h2 : Tendsto (fun n : ℕ => ‖c (φ n)‖) atTop (𝓝 (rhoStar a h)) :=
      hc3.comp hφmono.tendsto_atTop
    exact tendsto_nhds_unique h1 h2
  -- components with these values
  choose S hSreg using fun n => hcomp (c (φ n)) (hc1 (φ n))
  -- the crux, and the annulus setup
  obtain ⟨δ, hδ0, hcrux⟩ := limit_analysis_v2 ha0 ha1 hh
  obtain ⟨r₁, r₂, N, hr₁0, hr₁r₂, hr₂δ, hratio, hN1, hN2, hN3, hN4⟩ :=
    mca_exists_annulus ha0 ha1 hr hρ hδ0
  have hA := (hcrux r₁ r₂ N hr₁0 hr₁r₂ hr₂δ hratio hN3 hN4).1 S (fun n => c (φ n)) c₀
    hSreg (fun n => hc2 (φ n)) hφlim
  -- `ρ*` is attained
  have hAtt : ∃ c : ℂ, ∃ S : Set ChainData, IsRegComp a h S c ∧ ‖c‖ = rhoStar a h := by
    rcases hA with ⟨μ₁, hμ₁, μ₂, hμ₂, hne, T, hT⟩ | ⟨k, hk⟩
    · exfalso
      have hTval : c₀ * μ₁ * μ₂ ∈ RegValues a h := hval T _ hT
      have h1 := hle (c₀ * μ₁ * μ₂) hTval
      have h2 : ‖c₀ * μ₁ * μ₂‖ < rhoStar a h := by
        rw [show c₀ * μ₁ * μ₂ = c₀ * (μ₁ * μ₂) by ring, norm_mul, hc₀norm]
        have h3 := mca_charSet_mul_norm_lt_one ha0 ha1 hh hμ₁ hμ₂ hne
        nlinarith [hρ, norm_nonneg c₀]
      linarith
    · have h1 : c (φ k) = c₀ := hk k le_rfl
      have h2 := hSreg k
      rw [h1] at h2
      exact ⟨c₀, S k, h2, hc₀norm⟩
  -- the set of minimal components
  set M : Set (Set ChainData) :=
    {S : Set ChainData | ∃ c : ℂ, IsRegComp a h S c ∧ ‖c‖ = rhoStar a h} with hMdef
  have hMne : M.Nonempty := by
    obtain ⟨c', S', hS', hc'⟩ := hAtt
    exact ⟨S', c', hS', hc'⟩
  have hMfin : M.Finite := by
    by_contra hnf
    have hinf : M.Infinite := hnf
    let g : ℕ ↪ M := Set.Infinite.natEmbedding M hinf
    let S' : ℕ → Set ChainData := fun n => (g n : Set ChainData)
    have hS'inj : Function.Injective S' := fun i j hij => g.injective (Subtype.ext hij)
    choose c' hc'1 hc'2 using fun n => (g n).2
    obtain ⟨d₀, hd₀mem, ψ, hψmono, hψlim⟩ :=
      (isCompact_closedBall (0 : ℂ) (rhoStar a h)).tendsto_subseq (x := c') fun n => by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact le_of_eq (hc'2 n)
    have hd₀norm : ‖d₀‖ = rhoStar a h := by
      have h1 : Tendsto (fun n : ℕ => ‖c' (ψ n)‖) atTop (𝓝 ‖d₀‖) := hψlim.norm
      have h2 : Tendsto (fun n : ℕ => ‖c' (ψ n)‖) atTop (𝓝 (rhoStar a h)) := by
        have : (fun n : ℕ => ‖c' (ψ n)‖) = fun _ => rhoStar a h := by
          funext n; exact hc'2 (ψ n)
        rw [this]; exact tendsto_const_nhds
      exact tendsto_nhds_unique h1 h2
    have hA2 := (hcrux r₁ r₂ N hr₁0 hr₁r₂ hr₂δ hratio hN3 hN4).1 (fun n => S' (ψ n))
      (fun n => c' (ψ n)) d₀ (fun n => hc'1 (ψ n)) (fun n => by
        rw [hc'2 (ψ n)]; linarith [hρ]) hψlim
    have hTfin : ({S : Set ChainData | IsRegComp a h S d₀}).Finite := by
      rcases (hcrux r₁ r₂ N hr₁0 hr₁r₂ hr₂δ hratio hN3 hN4).2 d₀ (by rw [hd₀norm]; linarith [hρ]) with
        ⟨μ₁, hμ₁, μ₂, hμ₂, hne, T, hT⟩ | hfin
      · exfalso
        have hTval : d₀ * μ₁ * μ₂ ∈ RegValues a h := hval T _ hT
        have h1 := hle (d₀ * μ₁ * μ₂) hTval
        have h2 : ‖d₀ * μ₁ * μ₂‖ < rhoStar a h := by
          rw [show d₀ * μ₁ * μ₂ = d₀ * (μ₁ * μ₂) by ring, norm_mul, hd₀norm]
          have h3 := mca_charSet_mul_norm_lt_one ha0 ha1 hh hμ₁ hμ₂ hne
          nlinarith [hρ, norm_nonneg d₀]
        linarith
      · exact hfin
    rcases hA2 with ⟨μ₁, hμ₁, μ₂, hμ₂, hne, T, hT⟩ | ⟨k, hk⟩
    · exfalso
      have hTval : d₀ * μ₁ * μ₂ ∈ RegValues a h := hval T _ hT
      have h1 := hle (d₀ * μ₁ * μ₂) hTval
      have h2 : ‖d₀ * μ₁ * μ₂‖ < rhoStar a h := by
        rw [show d₀ * μ₁ * μ₂ = d₀ * (μ₁ * μ₂) by ring, norm_mul, hd₀norm]
        have h3 := mca_charSet_mul_norm_lt_one ha0 ha1 hh hμ₁ hμ₂ hne
        nlinarith [hρ, norm_nonneg d₀]
      linarith
    · exfalso
      have hsub : Set.range (fun n : ℕ => S' (ψ (n + k)))
          ⊆ {S : Set ChainData | IsRegComp a h S d₀} := by
        rintro x ⟨n, rfl⟩
        have h2 : c' (ψ (n + k)) = d₀ := hk (n + k) (Nat.le_add_left k n)
        have h3 := hc'1 (ψ (n + k))
        rwa [h2] at h3
      have hrange : (Set.range (fun n : ℕ => S' (ψ (n + k)))).Infinite :=
        Set.infinite_range_of_injective (fun i j hij => by
          have h1 : ψ (i + k) = ψ (j + k) := hS'inj hij
          have h2 : i + k = j + k := hψmono.injective h1
          omega)
      exact hrange (hTfin.subset hsub)
  letI : Fintype M := hMfin.fintype
  let m : ℕ := Fintype.card M
  have hm0 : 0 < m := by
    obtain ⟨x, hx⟩ := hMne
    rw [show m = Fintype.card M from rfl]
    exact Fintype.card_pos_iff.mpr ⟨⟨x, hx⟩⟩
  let e : Fin m ≃ M := (Fintype.equivFin M).symm
  let Sj : Fin m → Set ChainData := fun i => (e i : Set ChainData)
  have hSmem : ∀ i, Sj i ∈ M := fun i => (e i).2
  refine ⟨r₁, r₂, N, m, Sj, fun i => Classical.choose (hSmem i), hm0, hr₁0, hr₁r₂, hratio,
    hN1, hN2, fun i => Classical.choose_spec (hSmem i), ?_, ?_⟩
  · intro S'' c'' hS'' hc''
    refine ⟨e.symm ⟨S'', ?_⟩, ?_⟩
    · exact ⟨c'', hS'', hc''⟩
    · show S'' = (e (e.symm ⟨S'', ⟨c'', hS'', hc''⟩⟩) : Set ChainData)
      rw [Equiv.apply_symm_apply]
  · refine ⟨mca_words N ×ˢ mca_words N, fun i => ?_⟩
    intro f hf
    simp only [WordSet, Set.mem_ofPred_eq] at hf
    exact Finset.mem_coe.mpr (Finset.mem_product.mpr
      ⟨mca_mem_words.mpr hf.1, mca_mem_words.mpr hf.2.1⟩)


end

end Work.EQ.MCAFree
