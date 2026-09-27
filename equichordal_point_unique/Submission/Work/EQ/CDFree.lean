import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.charVal_props
import Submission.Work.EQ.MCAFree
import Submission.Work.EQ.CDFreeTail

/-! # Collision-free copy of `Submission.Work.EQ.minimal_cycle_data`

`Submission.Work.EQ.minimal_cycle_data` cannot be imported by
`Submission.Work.EQ.exists_compact_regular_cycle`: it imports `minimal_cycle_analysis` (hence
`Work.EQ.limit_analysis`) *and* `tail_bound_of_words` (hence `Work.EQ.H0_tail_bounded`), and those
two files both declare `Work.EQ.invBranch_true_ne_false`, so no module can contain both.

This is the same assembly with both sides collision-free: the analysis comes from
`Work.EQ.MCAFree.minimal_cycle_analysis` and the tail bound from `Work.EQ.CDFree.cdf_tail_bound`
(see `Submission/Work/EQ/CDFreeTail.lean`).  Everything else is a verbatim copy of
`minimal_cycle_data.lean` with `mcd_...` renamed `cdf_...`.  Regenerate with `_recopy_free.sh`. -/

namespace Work.EQ.CDFree

open Complex Filter _root_.Topology


/-- `‖(x : ℂ)‖ = |x|`. -/
lemma cdf_norm_ofReal (x : ℝ) : ‖((x : ℂ))‖ = |x| := by
  have h1 : ‖((x : ℂ))‖ ^ 2 = x ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
  calc ‖((x : ℂ))‖ = Real.sqrt (‖((x : ℂ))‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (x ^ 2) := by rw [h1]
    _ = |x| := Real.sqrt_sq_eq_abs x

/-- Every element of `CharSet a h` has norm `≤ 1`. -/
lemma cdf_charSet_norm_le_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {μ : ℂ} (hμ : μ ∈ CharSet a h) : ‖μ‖ ≤ 1 := by
  rw [CharSet, Set.mem_union] at hμ
  rcases hμ with hmem1 | hmem2
  · rw [Set.mem_singleton_iff] at hmem1
    rw [hmem1]; norm_num
  · obtain ⟨ε, hε, rfl⟩ := hmem2
    obtain ⟨d, hd, hprops, hq⟩ := charVal_props (a := a) (h := h) (r := r) ha0 ha1 hh
    obtain ⟨him, hre0, hre1, -⟩ := hprops ε hε
    have hcast : charVal a h ε = ((charVal a h ε).re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    rw [hcast, cdf_norm_ofReal, abs_of_pos hre0]
    exact hre1

/-- Every element of `CharSet a h` different from `1` has norm `< 1`. -/
lemma cdf_charSet_norm_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {μ : ℂ} (hμ : μ ∈ CharSet a h) (hne : μ ≠ 1) : ‖μ‖ < 1 := by
  rcases lt_or_eq_of_le (cdf_charSet_norm_le_one ha0 ha1 hh hμ) with h1 | h1
  · exact h1
  · exfalso
    rw [CharSet, Set.mem_union] at hμ
    rcases hμ with hmem1 | hmem2
    · exact hne (Set.mem_singleton_iff.mp hmem1)
    · obtain ⟨ε, hε, rfl⟩ := hmem2
      obtain ⟨d, hd, hprops, hq⟩ := charVal_props (a := a) (h := h) (r := r) ha0 ha1 hh
      obtain ⟨him, hre0, hre1, -⟩ := hprops ε hε
      have hcast : charVal a h ε = ((charVal a h ε).re : ℂ) := by
        apply Complex.ext
        · simp
        · simpa using him
      rw [hcast, cdf_norm_ofReal, abs_of_pos hre0] at h1
      exact hne (by rw [hcast, h1]; norm_num)

/-- Every regular component value has modulus at least `ρ*`. -/
lemma cdf_rhoStar_le_of_isRegComp {a : ℝ} {h : ℂ → ℂ} {S : Set ChainData} {c : ℂ}
    (hS : IsRegComp a h S c) : rhoStar a h ≤ ‖c‖ := by
  have hmem : c ∈ RegValues a h := by
    obtain ⟨-, ⟨p, hp, hSeq⟩, hvall⟩ := hS
    exact ⟨p, hp, fun q hq => hvall q (by rw [hSeq]; exact hq)⟩
  refine csInf_le ?_ ⟨c, hmem, rfl⟩
  exact ⟨0, fun x hx => by obtain ⟨c', -, rfl⟩ := hx; exact norm_nonneg c'⟩

/-- **Case (ii) of the trichotomy is impossible for a minimal component.**  If `‖c₀‖ = ρ*` then
no regular component has value `c₀ · μ₁ · μ₂` with `μ₁, μ₂ ∈ CharSet a h` and
`(μ₁, μ₂) ≠ (1,1)`: such a component would be a regular value of modulus `< ρ*`. -/
lemma cdf_no_smaller_value {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {c₀ : ℂ} (hc : ‖c₀‖ = rhoStar a h) (hpos : 0 < rhoStar a h) :
    ∀ c' : ℂ, (∃ μ₁ ∈ CharSet a h, ∃ μ₂ ∈ CharSet a h, (μ₁ ≠ 1 ∨ μ₂ ≠ 1) ∧
        ∃ T : Set ChainData, IsRegComp a h T (c₀ * μ₁ * μ₂)) → False := by
  intro _ ⟨μ₁, hμ₁, μ₂, hμ₂, hne, T, hT⟩
  have hlt : ‖μ₁‖ * ‖μ₂‖ < 1 := by
    rcases hne with h | h
    · have hlt1 : ‖μ₁‖ < 1 := cdf_charSet_norm_lt_one ha0 ha1 hh hμ₁ h
      have hle2 : ‖μ₂‖ ≤ 1 := cdf_charSet_norm_le_one ha0 ha1 hh hμ₂
      nlinarith [norm_nonneg μ₁, norm_nonneg μ₂]
    · have hlt2 : ‖μ₂‖ < 1 := cdf_charSet_norm_lt_one ha0 ha1 hh hμ₂ h
      have hle1 : ‖μ₁‖ ≤ 1 := cdf_charSet_norm_le_one ha0 ha1 hh hμ₁
      nlinarith [norm_nonneg μ₁, norm_nonneg μ₂]
  have hc0pos : 0 < ‖c₀‖ := by rw [hc]; exact hpos
  have h1 : ‖c₀ * μ₁ * μ₂‖ < ‖c₀‖ := by
    rw [norm_mul, norm_mul]
    nlinarith [norm_nonneg c₀, hlt, hc0pos]
  have h2 : rhoStar a h ≤ ‖c₀ * μ₁ * μ₂‖ := cdf_rhoStar_le_of_isRegComp hT
  rw [← hc] at h2
  linarith

/-- **The variational analysis of Rychlik's Thm 8: existence, finiteness and bounded tails of
the minimal cycle.**

If some component of `⁰H` is regular and `ρ* = ⨅{‖c‖ : c is the value of a regular component}`
is positive, then `ρ*` is attained, there are only finitely many regular components with
`‖c‖ = ρ*` ("minimal components"), and over a suitable annulus `Ann r₁ r₂` (of ratio `> 1/λ`,
inside the germ radius) the tails of every chain of every minimal component are the germs from a
uniform depth `N` on.  The latter is Rychlik's "the set `E` of words over the annulus is finite":
at depth `N` the reading word of a chain is unique and has length exactly `N`.

**Route (`PAPER_PROOFS.md` §5, Rychlik Thm 8).**  Write `Σ = RegValues a h`, `ρ* = rhoStar a h`,
and fix `δ` smaller than the radii of `fan_estimates`, `fan_trichotomy`, `charVal_props`,
`germC_facts`.  Choose `A = Ann r₁ r₂ ⊂ ball 0 δ` with `r₂/r₁ > 1/λ` and `N` with
`λ^N r₂ < r`, `λ^N·2ρ*/r₁ < r`.

*Reading a chain over `A`.*  For `q ∈ H0` with `ψ₁ q ∈ A`: the minimal tail index is what has to
be bounded; `chain_eq_fan_len` (`exists_compact_regular_cycle`) turns a bound `N` on it into a
stable word `ε` of length `N` with `q 0 = fan ε (ψ₁ q)`, and the mirror form
(`chain_read_bwd`) turns the backward bound into `η` with
`q(-N) = mirror (fan η (λ^N ψ₂ q))`.

*Lemma 5.1 (limits over `A`).*  Let `x_n ∈ H0` have `ψ₁ x_n ∈ A`, lie on regular components with
values `c_n → c₀`, and apply `fan_trichotomy` to `(ε_n)` (the words of *unbounded* length given by
the actual tail index of each `x_n`) and jointly to `(η_n)`.

* Case (iii) on either side is impossible: it makes the segment from index `-N` to `0` run from an
  unstable-`1/4`-near axis point to a stable-`η`-near point with `η` arbitrarily small, which
  `no_near_axis_segment` forbids (the other end is `1/4`-near by `fan_estimates`, resp. its
  mirror).
* Case (ii) on either side gives, by `exists_regular_of_family` applied to the limit family
  `u z = μ₁ z`, `v z = μ₂ c₀/z` (with `μ₁, μ₂ ∈ CharSet`, at least one `≠ 1`), a regular
  component with value `c₀·μ₁·μ₂`.  To obtain the family: the local sections of `H0` are analytic
  in `ψ₁` on the component (`H0_structure`); the identity "index `-N` point
  `= mirror (fan η_n (λ^N c_n/z))`" holds on a disc by the identity theorem;
  `backward_puiseux` (F3) gives finitely many branches of the limit stable end
  `fan ε₀ (μ₁ ·)`, one of which must match the limit unstable end identically on a disc.
* Case (i) on both sides: the words are eventually `fan`-constant, and matching at index `-N`
  forces `fan η₀(w) = fan η₀(w·c_n/c_n')`, so `c_n = c_n'` by `fan_snd_deriv_ne_zero`; hence
  finitely many values and finitely many components.

*Conclusion.*  Let `c_n ∈ Σ` with `‖c_n‖ → ρ*`.  Lemma 5.1 gives either (ii) a regular value of
modulus `≤ ρ*·μ_max < ρ*` (`charVal_props`: characteristic values of returning words are real in
`(0,1]`, equal `1` only for the principal leaf, and only finitely many exceed any positive bound,
so those `< 1` are bounded away from `1`), contradicting the minimality of `ρ*`, or (i) finitely
many values, so `c_n` is eventually constant and `ρ*` is attained.  Repeating for the sequence of
minimal components (all with `c_n ≡ c₀`) gives finitely many of them.  The same trichotomy
argument, now with `c_n ≡ c₀` so that case (ii) is impossible, shows that the *set of tail
indices* over the band `{ψ₁ ∈ A}` is bounded (an unbounded sequence of tail indices gives case
(iii) or (ii)); taking the bound `N` gives the two tail conclusions. -/
theorem minimal_cycle_data {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (hpos : 0 < rhoStar a h)
    (hreg : ∃ S : Set ChainData, ∃ c : ℂ, IsRegComp a h S c) :
    ∃ (r₁ r₂ : ℝ) (N m : ℕ) (S : Fin m → Set ChainData) (c : Fin m → ℂ),
      0 < m ∧ 0 < r₁ ∧ r₁ < r₂ ∧ r₂ / r₁ > 1 / eqLam a ∧
      (eqLam a : ℝ) ^ N * r₂ < r ∧ (eqLam a : ℝ) ^ N * rhoStar a h / r₁ < r ∧
      (∀ i, IsRegComp a h (S i) (c i) ∧ ‖c i‖ = rhoStar a h) ∧
      (∀ S' : Set ChainData, ∀ c' : ℂ, IsRegComp a h S' c' → ‖c'‖ = rhoStar a h →
        ∃ i, S' = S i) ∧
      ∀ i, ∀ q ∈ S i, q.2.1 ∈ Ann r₁ r₂ →
        (∀ n : ℕ, N ≤ n → q.1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * q.2.1)) ∧
        (∀ n : ℕ, N ≤ n → q.1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * q.2.2)) := by
  classical
  have hr : 0 < r := hh.1
  -- the variational analysis: existence and finiteness of the minimal components
  obtain ⟨_, _, _, m, S, c, hm, -, -, -, -, -, hSreg, hexh, -⟩ :=
    MCAFree.minimal_cycle_analysis ha0 ha1 hh hpos hreg
  -- the tail bound over an annulus, once case (ii) is excluded
  obtain ⟨δ, hδ, htb⟩ := cdf_tail_bound ha0 ha1 hh hpos
  have hlam0 : 0 < eqLam a := div_pos (by linarith) (by linarith)
  have hlam1 : eqLam a < 1 := by rw [eqLam, div_lt_one (by linarith)]; linarith
  -- a working annulus inside `ball 0 δ`
  set r₂ : ℝ := min r δ / 4 with hr₂def
  set r₁ : ℝ := r₂ * eqLam a / 2 with hr₁def
  have hr₂0 : 0 < r₂ := by rw [hr₂def]; exact div_pos (lt_min hr hδ) (by norm_num)
  have hr₂δ : r₂ < δ := by
    rw [hr₂def]
    have h := min_le_right r δ
    linarith
  have hr₁0 : 0 < r₁ := by rw [hr₁def]; exact div_pos (mul_pos hr₂0 hlam0) (by norm_num)
  have hr₁r₂ : r₁ < r₂ := by
    rw [hr₁def]
    have h2 : eqLam a / 2 < 1 := by linarith
    have := mul_lt_mul_of_pos_left h2 hr₂0
    linarith
  have hratio : r₂ / r₁ > 1 / eqLam a := by
    have heq : r₂ / r₁ = 2 / eqLam a := by
      rw [hr₁def]
      field_simp
    rw [heq, gt_iff_lt]
    exact div_lt_div_of_pos_right (by norm_num) hlam0
  -- the tail bound for each minimal component
  have hexM : ∀ i : Fin m, ∃ M : ℕ, ∀ q ∈ S i, q.2.1 ∈ Ann r₁ r₂ →
      (∀ n : ℕ, M ≤ n → q.1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * q.2.1)) ∧
      (∀ n : ℕ, M ≤ n → q.1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * q.2.2)) :=
    fun i => htb r₁ r₂ hr₁0 hr₁r₂ hr₂δ hratio (S i) (c i) (hSreg i).1 (by rw [(hSreg i).2]; linarith)
      (cdf_no_smaller_value ha0 ha1 hh (hSreg i).2 hpos)
  choose M hM using hexM
  -- a depth large enough for the two smallness conditions
  have hexN : ∃ Nd : ℕ, (eqLam a) ^ Nd * r₂ < r ∧ (eqLam a) ^ Nd * rhoStar a h / r₁ < r := by
    have hz : Tendsto (fun Nd : ℕ => (eqLam a) ^ Nd * max r₂ (rhoStar a h / r₁)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0.le hlam1).mul_const
        (max r₂ (rhoStar a h / r₁))
    obtain ⟨Nd, hNd⟩ := (hz.eventually (isOpen_Iio.mem_nhds hr)).exists
    refine ⟨Nd, ?_, ?_⟩
    · calc (eqLam a) ^ Nd * r₂ ≤ (eqLam a) ^ Nd * max r₂ (rhoStar a h / r₁) :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) (pow_nonneg hlam0.le Nd)
        _ < r := hNd
    · have h2 : (eqLam a) ^ Nd * (rhoStar a h / r₁)
          ≤ (eqLam a) ^ Nd * max r₂ (rhoStar a h / r₁) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (pow_nonneg hlam0.le Nd)
      rw [mul_div_assoc]
      linarith
  obtain ⟨Nd, hNd₁, hNd₂⟩ := hexN
  refine ⟨r₁, r₂, max (Finset.univ.sup M) Nd, m, S, c, hm, hr₁0, hr₁r₂, hratio,
    ?_, ?_, hSreg, hexh, ?_⟩
  · calc (eqLam a) ^ (max (Finset.univ.sup M) Nd) * r₂ ≤ (eqLam a) ^ Nd * r₂ :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_of_le_one hlam0.le hlam1.le (le_max_right _ _)) (le_of_lt hr₂0)
      _ < r := hNd₁
  · rw [mul_div_assoc]
    calc (eqLam a) ^ (max (Finset.univ.sup M) Nd) * (rhoStar a h / r₁)
        ≤ (eqLam a) ^ Nd * (rhoStar a h / r₁) :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_of_le_one hlam0.le hlam1.le (le_max_right _ _))
            (div_nonneg (le_of_lt hpos) (le_of_lt hr₁0))
      _ = (eqLam a) ^ Nd * rhoStar a h / r₁ := by rw [mul_div_assoc]
      _ < r := hNd₂
  · intro i q hq hqA
    obtain ⟨hfwd, hbwd⟩ := hM i q hq hqA
    have hle : M i ≤ max (Finset.univ.sup M) Nd :=
      le_trans (Finset.le_sup (f := M) (Finset.mem_univ i)) (le_max_left _ _)
    exact ⟨fun n hn => hfwd n (le_trans hle hn), fun n hn => hbwd n (le_trans hle hn)⟩


end Work.EQ.CDFree
