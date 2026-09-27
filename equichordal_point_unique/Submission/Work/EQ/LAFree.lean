import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.fan_base
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.FanUniform.fan_uniform_estimates
import Submission.Work.EQ.chain_eq_candChain_of_tails
import Submission.Work.EQ.StableTailDefs
import Submission.Work.EQ.component_shiftZ_invariant
import Submission.Work.EQ.AnnulusCover

/-! # Collision-free copy of `Submission.Work.EQ.limit_analysis`

`Submission.Work.EQ.limit_analysis` declares `Work.EQ.invBranch_true_ne_false`, which is *also*
declared (unused) in `Submission.Work.EQ.H0_tail_bounded`; any module importing both files fails to
build with a duplicate-declaration error.  This module is a verbatim copy of `limit_analysis.lean`
placed in the namespace `Work.EQ.LAFree`, so that it can be imported together with the
`H0_tail_bounded` side of the library (as `Work.EQ.exists_compact_regular_cycle` must: its
compactness input comes from `compact_mod_punctures_of_tails`, whose closure contains
`H0_tail_bounded`).  Same device as `Submission.Work.EQ.la_nnas.lean`.

Regenerate with `_recopy_free.sh`; keep in sync with the original. -/

namespace Work.EQ.LAFree

open Complex Filter _root_.Topology

open scoped Topology

/-! ## I. Reading a chain: branch letters, forward and backward words

A chain `p ∈ ⁰H` whose tails are the germs from depth `N` on is rigidly described by two words of
length `N`: the *forward* word (the branch letters of its first `N` steps) and the *backward* word
(the branch letters of its first `N` backward steps).  This section proves the two basic
identifications and the analytic *junction identity*:

* `fanWord_eq_fan` : the index-`0` point is the fan value of the forward word;
* `bwdP_bwdWord_take` : the index-`-j` point is the iterated backward image of the index-`0`
  point along the backward word;
* `junction` : the index-`-N` point, described backward from index `0`, is the unstable germ:
  `bwdP s (fan ε ψ₁) = eqMirror (germC (λ^N ψ₂))`.  This is the identity the limit analysis
  differentiates in `ψ₁`.
-/

/-- **The branch letter of a pair `(P,Q)`**: `true` when `P` is the principal backward image of
`Q`, `false` when it is the other one. -/
noncomputable def bLetter (a : ℝ) (P Q : ℂ × ℂ) : Bool :=
  if _ : P = invBranch a true Q then true
  else if _ : P = invBranch a false Q then false
  else true

lemma radicand_cpow_ne_zero {a : ℝ} {Q : ℂ × ℂ}
    (h : (Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2 ≠ 0) :
    ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by
  intro hcon
  refine h ?_
  have h2 : (((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ)) ^ 2
      = (Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2 := by
    have h1 : (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ := by norm_num
    rw [h1, Complex.cpow_nat_inv_pow _ (by norm_num)]
  rw [← h2, hcon]
  ring

/-- Off the isotropic lines the two backward branches are distinct, so the branch letter of a
regular pair is unambiguous. -/
theorem invBranch_true_ne_false {a : ℝ} {Q : ℂ × ℂ}
    (h : (Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2 ≠ 0) :
    invBranch a true Q ≠ invBranch a false Q := by
  intro hc
  have hρ : ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ) ≠ 0 :=
    radicand_cpow_ne_zero h
  have hcast : (Q.1 + (↑a : ℂ) / 2) = (Q.1 + ((a / 2 : ℝ) : ℂ)) := by push_cast; ring
  have hρ' : ((Q.1 + (↑a : ℂ) / 2) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [hcast]; exact hρ
  set D : ℂ := ((Q.1 + (↑a : ℂ) / 2) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ) with hD
  have hD' : D ≠ 0 := hρ'
  have hx := congrArg Prod.fst hc
  have hy := congrArg Prod.snd hc
  simp only [invBranch] at hx hy
  norm_num at hx hy
  have hz1 : Q.1 + (↑a : ℂ) / 2 = 0 := by
    have h1 : (Q.1 + (↑a : ℂ) / 2) / D = -((Q.1 + (↑a : ℂ) / 2) / D) := by
      have hx' := hx
      rw [show (-(↑a / 2) + -Q.1) = -(Q.1 + (↑a : ℂ) / 2) by ring] at hx'
      simpa only [neg_div] using hx'
    have h2 : 2 * ((Q.1 + (↑a : ℂ) / 2) / D) = 0 := by linear_combination h1
    have h3 := (mul_eq_zero.mp h2).resolve_left (by norm_num : (2 : ℂ) ≠ 0)
    exact (div_eq_zero_iff.mp h3).resolve_right hD'
  have hz2 : Q.2 = 0 := by
    have h2 : 2 * (Q.2 / D) = 0 := by linear_combination hy
    have h3 := (mul_eq_zero.mp h2).resolve_left (by norm_num : (2 : ℂ) ≠ 0)
    exact (div_eq_zero_iff.mp h3).resolve_right hD'
  refine h ?_
  have hc1 : Q.1 + ((a / 2 : ℝ) : ℂ) = 0 := by rw [← hcast]; exact hz1
  rw [hc1, hz2]
  ring

/-- On a regular pair the letter names the branch. -/
lemma bLetter_spec {a : ℝ} {P Q : ℂ × ℂ}
    (h : P = invBranch a true Q ∨ P = invBranch a false Q) :
    P = invBranch a (bLetter a P Q) Q := by
  rcases h with h' | h'
  · unfold bLetter
    rw [dif_pos h']
    exact h'
  · unfold bLetter
    by_cases h1 : P = invBranch a true Q
    · rw [dif_pos h1]; exact h1
    · rw [dif_neg h1, dif_pos h']; exact h'

/-- The **forward word** of length `N` of a chain: the branch letters of its first `N` steps. -/
noncomputable def fanWord (a : ℝ) : ℕ → ChainData → List Bool
  | 0, _ => []
  | n + 1, p => bLetter a (p.1 0) (p.1 1) :: fanWord a n (shiftZ a 1 p)

lemma fanWord_length (a : ℝ) : ∀ (N : ℕ) (p : ChainData), (fanWord a N p).length = N := by
  intro N
  induction N with
  | zero => intro p; simp [fanWord]
  | succ N ih => intro p; simp [fanWord, ih]

/-- The `j`-th backward letter of a chain. -/
noncomputable def bwdLetter (a : ℝ) (p : ChainData) (j : ℕ) : Bool :=
  bLetter a (p.1 (-((j : ℤ) + 1))) (p.1 (-(j : ℤ)))

/-- The **backward word** of length `N` of a chain: the branch letters of its first `N` backward
steps. -/
noncomputable def bwdWord (a : ℝ) (N : ℕ) (p : ChainData) : List Bool :=
  (List.range N).map (bwdLetter a p)

lemma bwdWord_length (a : ℝ) (N : ℕ) (p : ChainData) : (bwdWord a N p).length = N := by
  simp [bwdWord]

lemma bwdP_singleton (a : ℝ) (t : Bool) (P : ℂ × ℂ) : bwdP a [t] P = invBranch a t P := by
  simp [bwdP]

lemma bwdWord_take_succ (a : ℝ) (N : ℕ) (p : ChainData) {j : ℕ} (hj : j < N) :
    (bwdWord a N p).take (j + 1) = (bwdWord a N p).take j ++
      [bLetter a (p.1 (-((j : ℤ) + 1))) (p.1 (-(j : ℤ)))] := by
  have hlen : j < (bwdWord a N p).length := by rw [bwdWord_length]; exact hj
  rw [(List.take_append_getElem (l := bwdWord a N p) (i := j) hlen).symm]
  congr 1
  simp only [bwdWord, bwdLetter, List.getElem_map, List.getElem_range]

/-- **The stable word of a chain.** A chain whose forward tail is the stable germ from depth `N`
on is the fan value of its forward word of length `N`. -/
theorem fanWord_eq_fan {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {N : ℕ}
    {p : ChainData} (hp : IsChain a h p)
    (htail : ∀ n : ℕ, N ≤ n → p.1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * p.2.1)) :
    p.1 0 = fan a h (fanWord a N p) p.2.1 := by
  induction N generalizing p with
  | zero =>
    have h0 := htail 0 le_rfl
    simpa [fanWord, fan_nil] using h0
  | succ N ih =>
    have hp' : IsChain a h (shiftZ a 1 p) := isChain_shiftZ ha0 ha1 hp 1
    have htail' : ∀ n : ℕ, N ≤ n →
        (shiftZ a 1 p).1 (n : ℤ) =
          germC a h (((eqLam a : ℝ) : ℂ) ^ n * (shiftZ a 1 p).2.1) := by
      intro n hn
      have h1 : (shiftZ a 1 p).1 (n : ℤ) = p.1 ((n : ℤ) + 1) := by rw [shiftZ_fst]
      have h2 : (shiftZ a 1 p).2.1 = ((eqLam a : ℝ) : ℂ) * p.2.1 := by
        rw [shiftZ_psi1, zpow_one]
      have hidx : (↑n + 1 : ℤ) = ↑(n + 1) := by push_cast; ring
      rw [h1, h2, hidx, htail (n + 1) (by omega)]
      congr 1
      rw [pow_succ]; ring
    have hIH := ih hp' htail'
    have hnext : p.1 1 = fan a h (fanWord a N (shiftZ a 1 p)) (((eqLam a : ℝ) : ℂ) * p.2.1) := by
      have h1 : (shiftZ a 1 p).1 0 = p.1 1 := by rw [shiftZ_fst]; norm_num
      have h2 : (shiftZ a 1 p).2.1 = ((eqLam a : ℝ) : ℂ) * p.2.1 := by
        rw [shiftZ_psi1, zpow_one]
      rw [← h1, hIH, h2]
    have hpair : RegPair a (p.1 0) (p.1 1) := hp.1 0
    rw [fanWord, fan_cons, ← hnext]
    exact bLetter_spec (H0_invParam_ge_exists_invBranch hpair.1 hpair.2.2)

/-- **The unstable word of a chain.** The index `-j` point of a chain is the iterated backward
image of its index-`0` point along its backward word of length `N`. -/
theorem bwdP_bwdWord_take {a : ℝ} {h : ℂ → ℂ} {N : ℕ} {p : ChainData} (hp : IsChain a h p) :
    ∀ j : ℕ, j ≤ N → p.1 (-(j : ℤ)) = bwdP a ((bwdWord a N p).take j) (p.1 0) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hj' : j ≤ N := le_of_lt (Nat.lt_of_succ_le hj)
    have hlt : j < N := Nat.lt_of_succ_le hj
    have hpair : RegPair a (p.1 (-((j : ℤ) + 1))) (p.1 (-(j : ℤ))) := by
      have h := hp.1 (-((j : ℤ) + 1))
      have hidx : -((j : ℤ) + 1) + 1 = -(j : ℤ) := by ring
      rwa [hidx] at h
    rw [show (-(↑(j + 1) : ℤ)) = -((j : ℤ) + 1) by push_cast; ring]
    rw [bwdWord_take_succ a N p hlt, bwdP_append, bwdP_singleton, ← ih hj']
    exact bLetter_spec (H0_invParam_ge_exists_invBranch hpair.1 hpair.2.2)

/-- **The junction identity.** A chain whose two tails are the germs from depth `N` on satisfies
`bwdP a s (fan a h ε ψ₁) = eqMirror (germC a h (λ^N ψ₂))`, where `ε` and `s` are its forward and
backward words of length `N`. -/
theorem junction {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {N : ℕ} {p : ChainData}
    (hp : IsChain a h p)
    (hfw : ∀ n : ℕ, N ≤ n → p.1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * p.2.1))
    (hbw : ∀ n : ℕ, N ≤ n → p.1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * p.2.2)) :
    bwdP a (bwdWord a N p) (fan a h (fanWord a N p) p.2.1) =
      eqMirror (germC a h (((eqLam a : ℝ) : ℂ) ^ N * p.2.2)) := by
  rw [← fanWord_eq_fan ha0 ha1 hp hfw]
  have h1 : bwdP a (bwdWord a N p) (p.1 0) = p.1 (-(N : ℤ)) := by
    rw [← List.take_of_length_le (show (bwdWord a N p).length ≤ N by rw [bwdWord_length]),
      ← bwdP_bwdWord_take hp N le_rfl]
  rw [h1]
  simpa only [ugermC] using hbw N le_rfl


/-! ## Status and plan (for the limit analysis)

### What is already formalised here (sorry-free, no unproven imports)

* `bLetter` / `bLetter_spec` : the branch letter of a regular pair.
* `invBranch_true_ne_false` : the two backward branches are distinct off the isotropic lines
  (so the letter is unambiguous).
* `fanWord` / `bwdWord` : the forward and backward words of length `N` of a chain.
* `fanWord_eq_fan`, `bwdP_bwdWord_take`, `junction` : the two descriptions of a chain over an
  annulus and the **junction identity**
  `bwdP a (bwdWord a N p) (fan a h (fanWord a N p) p.2.1) = eqMirror (germC a h (λ^N ψ₂))`.

### Plan for (A) — the limit of a sequence of regular components

The statement is equivalent to the following annulus statement, because the annuli `λ^j·Ann r₁ r₂`
cover `ℂ*` and `σ` preserves the value `ψ₁ψ₂`:

`V_A := {c | ∃ S, IsRegComp a h S c ∧ ∃ p ∈ S, p.2.1 ∈ Ann r₁ r₂}` is **finite.

Proof route (all ingredients available or easy):
1. for `p ∈ H0` with `ψ₁ p ∈ A` and the two tails equal to the germs from depth `N` on, the
   *datum* `D p := (fanWord a N p, bwdWord a N p)` is defined and `junction` gives
   `y_{D}(u) = eqMirror (germC (λ^N c / u))` for `u = ψ₁ p`, `c = ψ₁(p)ψ₂(p)`, where
   `y_D u := bwdP a s (fan a h ε u)`;
2. along a local section (which exists by the *definition* of `H0`) the letters, hence the words,
   are locally constant, so the identity holds on a neighbourhood of `ψ₁ p`; the value is constant
   along the section because the section lies in the connected component of `p`, which is regular;
3. for two values `c, c'` with `|c|,|c'| ≤ 2ρ*` the two functions `u ↦ eqMirror (germC (λ^N c/u))`
   and `u ↦ eqMirror (germC (λ^N c'/u))` are analytic on the connected annulus
   `λ^N 2ρ*/ρ < ‖u‖ < ρ` (which contains `A` once `δ ≤ ρ`), so the identity theorem and the
   injectivity of `germC` give `c = c'`;
4. hence each datum of length `N` determines at most one value, and there are only `2^N · 2^N`
   data.

### Plan for (B) — finiteness for a fixed value

* Step 1 (`K_c^A` finite): with the value `c` fixed, (the same argument as above shows that) each
  datum determines at most one *component* meeting `A`; hence finitely many.
* Step 2 (orbits): the shift `σ` maps the datum of `x` to `τ(ε, s) = (ε.drop 1 ++ [true],
  ε₀ :: s.take (N-1))` (the last letter is `true` because from index `N` on the chain follows the
  germ, whose step is principal).  This is a self-map of the finite set of data, so the datum orbit
  is eventually periodic; the state of a component also records the *piece* of the datum-domain
  (finitely many with value `c` meeting `A`), and the shift acts on those states, so the orbit of
  each `S ∈ K_c^A` is finite.  Hence `K_c = ⋃_{S ∈ K_c^A} orbit(S)` is finite.
* Step 3 (assembly) is then independent of the hypotheses on `(r₁,r₂,N)`.
-/

/-! ## II. Local constancy of the branch letters

The branch letter of a pair is a *discrete* datum.  Off the branch cut of the square root the
backward map `invBranch` is continuous, hence along a continuous family of regular pairs the
letter is locally constant.  This is the first ingredient of the datum rigidity: it makes the
forward and backward words of a chain locally constant along the local sections of `⁰H`.
-/

/-- **Continuity of the backward branch off the branch cut.**  If the radicand
`(Q+a/2)^2 + Q₂^2` lies in the slit plane, `invBranch a b` is continuous at `Q`. -/
lemma invBranch_continuousAt {a : ℝ} {b : Bool} {Q₀ : ℂ × ℂ}
    (h : ((Q₀.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q₀.2 ^ 2) ∈ Complex.slitPlane) :
    ContinuousAt (invBranch a b) Q₀ := by
  have hbase : ContinuousAt (fun Q : ℂ × ℂ => (Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) Q₀ := by
    fun_prop
  have hroot : ContinuousAt (fun Q : ℂ × ℂ =>
      ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ)) Q₀ :=
    hbase.cpow continuousAt_const h
  have hb0 : ((Q₀.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q₀.2 ^ 2) ≠ 0 := by
    intro h0
    have hre : ((Q₀.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q₀.2 ^ 2).re = 0 := by rw [h0]; simp
    have him : ((Q₀.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q₀.2 ^ 2).im = 0 := by rw [h0]; simp
    simp only [Complex.slitPlane, Set.mem_ofPred_eq] at h
    rcases h with h | h
    · rw [hre] at h; exact lt_irrefl 0 h
    · exact h him
  have hrootne : (((Q₀.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q₀.2 ^ 2) ^ (1 / 2 : ℂ)) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl hb0
  unfold invBranch
  fun_prop

/-- **Analyticity of the backward branch off the branch cut.** -/
lemma analyticAt_invBranch {a : ℝ} {b : Bool} {Q : ℂ × ℂ}
    (h : ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ∈ Complex.slitPlane) :
    AnalyticAt ℂ (invBranch a b) Q := by
  have h1 : AnalyticAt ℂ (fun Q : ℂ × ℂ => Q.1) Q := analyticAt_fst
  have h2 : AnalyticAt ℂ (fun Q : ℂ × ℂ => Q.2) Q := analyticAt_snd
  have hbase : AnalyticAt ℂ (fun Q : ℂ × ℂ => (Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) Q :=
    ((h1.add analyticAt_const).pow 2).add (h2.pow 2)
  have hroot : AnalyticAt ℂ (fun Q : ℂ × ℂ =>
      ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ)) Q :=
    hbase.cpow analyticAt_const h
  have hb0 : ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ≠ 0 := by
    intro h0
    have hre : ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2).re = 0 := by rw [h0]; simp
    have him : ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2).im = 0 := by rw [h0]; simp
    simp only [Complex.slitPlane, Set.mem_ofPred_eq] at h
    rcases h with h | h
    · rw [hre] at h; exact lt_irrefl 0 h
    · exact h him
  have hrootne : (((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ)) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl hb0
  have hnum : AnalyticAt ℂ (fun Q : ℂ × ℂ => Q.1 + ((a / 2 : ℝ) : ℂ)) Q :=
    h1.add analyticAt_const
  unfold invBranch
  refine AnalyticAt.prod ?_ ?_
  · exact (h1.neg).add ((analyticAt_const.mul hnum).div hroot hrootne)
  · exact (h2.neg).add ((analyticAt_const.mul h2).div hroot hrootne)

/-- **The fan radicand has positive real part near `ψ₁ = 0`.**  Produced from the uniform fan
estimates (`FanUniform.fan_uniform_estimates`), the axis-centre arithmetic of the fan
(`FanSep.axis_walk`, `FanSep.centre_numbers`) and `FanTri.radicand_pos`.  This is the geometric
input that keeps `invBranch` on its analytic branch along the intermediate points of
`u ↦ bwdP a s (fan a h ε u)`. -/
lemma exists_fan_radicand_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ε : List Bool) (u : ℂ), ‖u‖ < δ →
      0 < (((fan a h ε u).1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + (fan a h ε u).2 ^ 2).re := by
  obtain ⟨δU, Ke, Lam, hδU, hKe, hLam, hbnd⟩ := FanUniform.fan_uniform_estimates ha0 ha1 hh
  obtain ⟨-, haxis2⟩ := FanSep.axis_walk ha0 ha1 hh
  obtain ⟨hcn1, -⟩ := FanSep.centre_numbers ha0 ha1
  have ha1' : 0 < 1 - a := by linarith
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  refine ⟨min δU (min ((1 - a) / (16 * Ke)) (min (eqLam a / (8 * Lam)) ((1 - a) / (4 * Ke)))),
    lt_min hδU (lt_min (by positivity) (lt_min (by positivity) (by positivity))), ?_⟩
  intro ε u hu
  obtain ⟨-, k, hk⟩ := haxis2 ε
  have huδU : u ∈ Metric.ball (0 : ℂ) δU := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_lt_of_le hu (min_le_left _ _)
  obtain ⟨hb1, hb2⟩ := (hbnd ε).2 u huδU
  set c : ℝ := -1 / 2 + 2 * (k : ℝ) with hcdef
  have hcentre : (fan a h ε 0).1 = ((c : ℝ) : ℂ) := by
    rw [hcdef, show (((-1 / 2 + 2 * (k : ℝ) : ℝ)) : ℂ) = -1 / 2 + 2 * (k : ℂ) by push_cast; ring]
    exact hk
  -- the three smallness bounds
  have hsmall1 : ‖u‖ ≤ (1 - a) / (16 * Ke) :=
    le_trans (le_of_lt hu) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hsmall2 : ‖u‖ ≤ eqLam a / (8 * Lam) :=
    le_trans (le_of_lt hu)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hsmall3 : ‖u‖ ≤ (1 - a) / (4 * Ke) :=
    le_trans (le_of_lt hu)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  set ρ : ℝ := Ke * ‖u‖ with hρdef
  set τ : ℝ := Lam * ‖u‖ with hτdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
  have hτ0 : 0 ≤ τ := by rw [hτdef]; positivity
  have hρg : ρ ≤ (1 - a) / 16 := by
    rw [hρdef]
    have h1 := mul_le_mul_of_nonneg_left hsmall1 (le_of_lt hKe)
    rw [show Ke * ((1 - a) / (16 * Ke)) = (1 - a) / 16 by field_simp] at h1
    exact h1
  have hτg : τ ≤ eqLam a / 8 := by
    rw [hτdef]
    have h1 := mul_le_mul_of_nonneg_left hsmall2 (le_of_lt hLam)
    rw [show Lam * (eqLam a / (8 * Lam)) = eqLam a / 8 by field_simp] at h1
    exact h1
  have hPx : ‖(fan a h ε u).1 - ((c : ℝ) : ℂ)‖ ≤ ρ := by
    rw [hρdef, ← hcentre]
    exact hb1
  -- nonvanishing of `x - a/2`
  have hcd : (1 - a) / 2 ≤ ‖((c : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖ := by
    rw [hcdef]
    exact (hcn1 k).2
  have hPb : (fan a h ε u).1 - ((a / 2 : ℝ) : ℂ) ≠ 0 := by
    intro hzero
    have h2 : ‖((c : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖
        ≤ ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ + ‖(fan a h ε u).1 - ((c : ℝ) : ℂ)‖ := by
      have he : ((c : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)
          = (((c : ℝ) : ℂ) - (fan a h ε u).1) + ((fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)) := by
        ring
      calc ‖((c : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖
          = ‖(((c : ℝ) : ℂ) - (fan a h ε u).1)
              + ((fan a h ε u).1 - ((a / 2 : ℝ) : ℂ))‖ := by rw [he]
        _ ≤ ‖((c : ℝ) : ℂ) - (fan a h ε u).1‖
              + ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖
              + ‖(fan a h ε u).1 - ((c : ℝ) : ℂ)‖ := by
            rw [norm_sub_rev ((c : ℝ) : ℂ) (fan a h ε u).1]; ring
    rw [hzero, norm_zero, zero_add] at h2
    have h4 : Ke * ‖u‖ < (1 - a) / 2 := by
      have h5 : Ke * ‖u‖ ≤ Ke * ((1 - a) / (4 * Ke)) :=
        mul_le_mul_of_nonneg_left hsmall3 (le_of_lt hKe)
      rw [show Ke * ((1 - a) / (4 * Ke)) = (1 - a) / 4 by field_simp] at h5
      linarith [h5, ha1']
    linarith [h2, hcd, hPx, h4, hρdef]
  -- the semi-projective bound
  have hPw : ‖(fan a h ε u).2 / ((fan a h ε u).1 - ((a / 2 : ℝ) : ℂ))‖ ≤ τ := by
    rw [norm_div, hτdef]
    rw [div_le_iff₀ (norm_pos_iff.mpr hPb)]
    exact hb2
  have hcast : ((a / 2 : ℝ) : ℂ) = (a : ℂ) / 2 := by push_cast; ring
  refine FanTri.radicand_pos ha0 ha1 ⟨k, hcdef⟩ hρ0 hτ0 hρg hτg hPx ?_ ?_
  · rwa [hcast] at hPb
  · rwa [hcast] at hPw

/-- **The iterated backward image of a fan value is a fan value again.**  With `λ = eqLam a`,
`bwdP a l (fan a h ε u) = fan a h (l.reverse ++ ε) (u/λ^{|l|})`.  This is what turns the
containment question for the intermediate points of `u ↦ bwdP a s (fan ε u)` into a question about
the *stable fan*, where `exists_fan_radicand_pos` applies. -/
lemma bwdP_fan_eq_fan {a : ℝ} (hlam : ((eqLam a : ℝ) : ℂ) ≠ 0) (h : ℂ → ℂ) :
    ∀ (l ε : List Bool) (u : ℂ),
      bwdP a l (fan a h ε u) = fan a h (l.reverse ++ ε)
        (u / (((eqLam a : ℝ) : ℂ) ^ l.length)) := by
  intro l
  induction l with
  | nil => intro ε u; simp [bwdP]
  | cons s₀ l' ih =>
    intro ε u
    have h1 : bwdP a (s₀ :: l') (fan a h ε u) =
        bwdP a l' (fan a h (s₀ :: ε) (u / ((eqLam a : ℝ) : ℂ))) := by
      rw [bwdP_cons, fan_cons]
      congr 1
      field_simp
    rw [h1, ih]
    have hL : l'.reverse ++ (s₀ :: ε) = (s₀ :: l').reverse ++ ε := by
      rw [List.reverse_cons, List.append_assoc]
      congr 1
    have hR : (u / ((eqLam a : ℝ) : ℂ)) / (((eqLam a : ℝ) : ℂ) ^ l'.length)
        = u / (((eqLam a : ℝ) : ℂ) ^ (s₀ :: l').length) := by
      rw [List.length_cons, div_div, pow_succ]
      ring
    rw [hL, hR]

/-- **The intermediate backward images of a fan stay off the branch cut.**  Combining the
identification `bwdP_fan_eq_fan` with `exists_fan_radicand_pos`: the iterated backward image
`bwdP a l (fan a h ε u)` — a fan value with parameter `u/λ^{|l|}` — has positive-real-part
radicand as soon as that parameter is small.  This discharges the side condition of
`analyticOnNhd_bwdP`. -/
lemma exists_slitPlane_bwdP_fan {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ε l : List Bool) (u : ℂ),
      ‖u / (((eqLam a : ℝ) : ℂ) ^ l.length)‖ < δ →
      (((bwdP a l (fan a h ε u)).1 + ((a / 2 : ℝ) : ℂ)) ^ 2 +
        ((bwdP a l (fan a h ε u)).2) ^ 2) ∈ Complex.slitPlane := by
  obtain ⟨δ, hδ, hpos⟩ := exists_fan_radicand_pos ha0 ha1 hh
  refine ⟨δ, hδ, ?_⟩
  intro ε l u hu
  rw [bwdP_fan_eq_fan (a := a)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (eqLam_pos' ha0 ha1))) h]
  exact Or.inl (hpos (l.reverse ++ ε) _ hu)

/-- **Analyticity of the iterated backward image of an analytic family.**  If `P` is analytic on
`ball 0 ρ` and, for every prefix `l` of `s`, the inverse-branch radicand at the intermediate point
`bwdP a l (P u)` stays off the branch cut, then `u ↦ bwdP a s (P u)` is analytic on `ball 0 ρ`.
This is the analyticity input of the identity-theorem comparison of the junction identity. -/
lemma analyticOnNhd_bwdP {a : ℝ} {ρ : ℝ} {s : List Bool} :
    ∀ (P : ℂ → ℂ × ℂ), AnalyticOnNhd ℂ P (Metric.ball 0 ρ) →
    (∀ u ∈ Metric.ball 0 ρ, ∀ l : List Bool, l <+: s →
      (((bwdP a l (P u)).1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + ((bwdP a l (P u)).2) ^ 2) ∈
        Complex.slitPlane) →
    AnalyticOnNhd ℂ (fun u => bwdP a s (P u)) (Metric.ball 0 ρ) := by
  induction s with
  | nil =>
    intro P hP hslit u hu
    simpa [bwdP] using hP u hu
  | cons s₀ l ih =>
    intro P hP hslit u hu
    have hQ : AnalyticOnNhd ℂ (fun v => invBranch a s₀ (P v)) (Metric.ball 0 ρ) := fun v hv => by
      have h1 : AnalyticAt ℂ ((fun Q : ℂ × ℂ => invBranch a s₀ Q) ∘ P) v :=
        (analyticAt_invBranch (Q := P v)
          (by simpa [bwdP] using hslit v hv [] List.nil_prefix)).comp (hP v hv)
      exact h1
    have hslitQ : ∀ v ∈ Metric.ball 0 ρ, ∀ l' : List Bool, l' <+: l →
        (((bwdP a l' ((fun w => invBranch a s₀ (P w)) v)).1 + ((a / 2 : ℝ) : ℂ)) ^ 2 +
          ((bwdP a l' ((fun w => invBranch a s₀ (P w)) v)).2) ^ 2) ∈ Complex.slitPlane := by
      intro v hv l' hl'
      have h1 : bwdP a l' ((fun w => invBranch a s₀ (P w)) v) = bwdP a (s₀ :: l') (P v) :=
        (bwdP_cons a s₀ l' (P v)).symm
      rw [h1]
      exact hslit v hv (s₀ :: l') ((List.cons_prefix_cons).mpr ⟨rfl, hl'⟩)
    have hmain : AnalyticAt ℂ (fun v => bwdP a l ((fun w => invBranch a s₀ (P w)) v)) u :=
      ih (fun w => invBranch a s₀ (P w)) hQ hslitQ u hu
    rwa [show (fun v => bwdP a (s₀ :: l) (P v)) =
        (fun v => bwdP a l ((fun w => invBranch a s₀ (P w)) v)) from
      funext (fun v => bwdP_cons a s₀ l (P v))]

/-- The norm of a real cast. -/
lemma norm_ofReal_eq_abs' (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

/-- `eqMirror` is analytic. -/
lemma analyticOnNhd_eqMirror : AnalyticOnNhd ℂ (eqMirror) Set.univ := fun P _ =>
  AnalyticAt.prod (analyticAt_fst.neg) analyticAt_snd

/-- `λ^N` is non-zero for `0 < a < 1`. -/
lemma norm_lam_pow_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (N : ℕ) :
    0 < ‖(((eqLam a : ℝ) : ℂ)) ^ N‖ := by
  rw [norm_pow, norm_ofReal_eq_abs']
  exact pow_pos (abs_pos.mpr (ne_of_gt (eqLam_pos' ha0 ha1))) N

/-- **Analyticity of the comparison family `u ↦ eqMirror (germC (κ/u))`** on an annulus whose inner
radius keeps the argument inside the germ disc. -/
lemma analyticOnNhd_germC_div {a : ℝ} {h : ℂ → ℂ} {κ : ℂ} {ρg R ρ : ℝ} (hρg : 0 < ρg)
    (hR : 0 < R) (hgc : AnalyticOnNhd ℂ (germC a h) (Metric.ball 0 ρg))
    (hκ : ‖κ‖ ≤ ρg * R) :
    AnalyticOnNhd ℂ (fun u : ℂ => eqMirror (germC a h (κ / u)))
      {u : ℂ | R < ‖u‖ ∧ ‖u‖ < ρ} := by
  have hg1 : AnalyticOnNhd ℂ (fun u : ℂ => κ / u) {u : ℂ | R < ‖u‖ ∧ ‖u‖ < ρ} := by
    refine AnalyticOnNhd.div analyticOnNhd_const analyticOnNhd_id ?_
    intro u hu
    have hu0 : 0 < ‖u‖ := by linarith [hu.1, hR]
    exact norm_ne_zero_iff.mp (ne_of_gt hu0)
  have hsub : ∀ u : ℂ, R < ‖u‖ ∧ ‖u‖ < ρ → ‖κ / u‖ < ρg := by
    intro u hu
    have hu0 : 0 < ‖u‖ := by linarith [hu.1, hR]
    rw [norm_div, div_lt_iff₀ hu0]
    exact lt_of_le_of_lt hκ (mul_lt_mul_of_pos_left hu.1 hρg)
  have hmaps : Set.MapsTo (fun u : ℂ => κ / u) {u : ℂ | R < ‖u‖ ∧ ‖u‖ < ρ}
      (Metric.ball 0 ρg) := fun u hu => by
    simpa [Metric.mem_ball, dist_zero_right] using hsub u hu
  have h1 : AnalyticOnNhd ℂ (fun u : ℂ => germC a h (κ / u)) {u : ℂ | R < ‖u‖ ∧ ‖u‖ < ρ} :=
    hgc.comp hg1 hmaps
  exact analyticOnNhd_eqMirror.comp h1 (fun _ _ => Set.mem_univ _)

/-- **Choosing the comparison annulus.**  For `z ≠ 0` and two values whose scaled versions divide
by `z` inside the germ disc, there is a radius `R` with `0 < R < ‖z‖` and `‖λ^N c‖, ‖λ^N c'‖ ≤ ρg R`:
take `R = ‖λ^N‖ · max ‖c‖ ‖c'‖ / ρg`. -/
lemma exists_annulus_radius {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {c c' : ℂ} {ρg : ℝ} {N : ℕ}
    {z : ℂ} (hρg : 0 < ρg) (hmax : 0 < max ‖c‖ ‖c'‖) (hz0 : z ≠ 0)
    (hzc : ‖(((eqLam a : ℝ) : ℂ)) ^ N * c / z‖ < ρg)
    (hzc' : ‖(((eqLam a : ℝ) : ℂ)) ^ N * c' / z‖ < ρg) :
    ∃ R : ℝ, 0 < R ∧ R < ‖z‖ ∧
      ‖(((eqLam a : ℝ) : ℂ)) ^ N * c‖ ≤ ρg * R ∧
      ‖(((eqLam a : ℝ) : ℂ)) ^ N * c'‖ ≤ ρg * R := by
  have hlam0 : 0 < ‖(((eqLam a : ℝ) : ℂ)) ^ N‖ := norm_lam_pow_pos ha0 ha1 N
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  refine ⟨‖(((eqLam a : ℝ) : ℂ)) ^ N‖ * max ‖c‖ ‖c'‖ / ρg,
    div_pos (mul_pos hlam0 hmax) hρg, ?_, ?_, ?_⟩
  · have h1 : ‖(((eqLam a : ℝ) : ℂ)) ^ N * c / z‖
        = ‖(((eqLam a : ℝ) : ℂ)) ^ N‖ * ‖c‖ / ‖z‖ := by rw [norm_div, norm_mul]
    rw [h1, div_lt_iff₀ hzn] at hzc
    have h2 : ‖(((eqLam a : ℝ) : ℂ)) ^ N * c' / z‖
        = ‖(((eqLam a : ℝ) : ℂ)) ^ N‖ * ‖c'‖ / ‖z‖ := by rw [norm_div, norm_mul]
    rw [h2, div_lt_iff₀ hzn] at hzc'
    have h3 : ‖(((eqLam a : ℝ) : ℂ)) ^ N‖ * max ‖c‖ ‖c'‖ < ρg * ‖z‖ := by
      rw [mul_max_of_nonneg _ _ (norm_nonneg _)]
      exact max_lt hzc hzc'
    rw [div_lt_iff₀ hρg]
    linarith
  · calc ‖(((eqLam a : ℝ) : ℂ)) ^ N * c‖ = ‖(((eqLam a : ℝ) : ℂ)) ^ N‖ * ‖c‖ := norm_mul _ _
      _ ≤ ‖(((eqLam a : ℝ) : ℂ)) ^ N‖ * max ‖c‖ ‖c'‖ :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)
      _ = ρg * (‖(((eqLam a : ℝ) : ℂ)) ^ N‖ * max ‖c‖ ‖c'‖ / ρg) :=
            (mul_div_cancel₀ _ (ne_of_gt hρg)).symm
  · calc ‖(((eqLam a : ℝ) : ℂ)) ^ N * c'‖ = ‖(((eqLam a : ℝ) : ℂ)) ^ N‖ * ‖c'‖ := norm_mul _ _
      _ ≤ ‖(((eqLam a : ℝ) : ℂ)) ^ N‖ * max ‖c‖ ‖c'‖ :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)
      _ = ρg * (‖(((eqLam a : ℝ) : ℂ)) ^ N‖ * max ‖c‖ ‖c'‖ / ρg) :=
            (mul_div_cancel₀ _ (ne_of_gt hρg)).symm

/-- **An annulus is preconnected.**  Proved by parametrising `u = r·e^{iθ}` with
`r ∈ (R,ρ)`, `θ ∈ [0,2π]`: the annulus is the continuous image of the preconnected rectangle.
This is the domain on which the junction identity is compared for two different values. -/
lemma isPreconnected_annulus {R ρ : ℝ} (hR : 0 < R) :
    IsPreconnected {u : ℂ | R < ‖u‖ ∧ ‖u‖ < ρ} := by
  have hS : IsPreconnected (Set.Ioo R ρ ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    isPreconnected_Ioo.prod isPreconnected_Icc
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))
      (Set.Ioo R ρ ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) := by fun_prop
  have himg := hS.image _ hcont
  convert himg using 1
  ext u
  constructor
  · rintro ⟨h1, _h2⟩
    have hne : u ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h1; linarith
    refine ⟨(‖u‖, if 0 < u.arg then u.arg else u.arg + 2 * Real.pi), ⟨⟨h1, _h2⟩, ?_⟩, ?_⟩
    · have harg := Complex.arg_mem_Ioc u
      constructor
      · split_ifs with h
        · exact le_of_lt h
        · linarith [harg.1, Real.pi_pos]
      · split_ifs with h
        · linarith [harg.2, Real.pi_pos]
        · have : u.arg ≤ 0 := not_lt.mp h
          linarith
    · change (‖u‖ : ℂ) * Complex.exp
        (((if 0 < u.arg then u.arg else u.arg + 2 * Real.pi : ℝ) : ℂ) * Complex.I) = u
      have hexp : Complex.exp
          (((if 0 < u.arg then u.arg else u.arg + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
          = Complex.exp ((u.arg : ℂ) * Complex.I) := by
        split_ifs with h
        · rfl
        · rw [show (((u.arg + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
              = (u.arg : ℂ) * Complex.I + (2 * Real.pi : ℂ) * Complex.I by push_cast; ring,
            Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
      rw [hexp, Complex.norm_mul_exp_arg_mul_I]
  · rintro ⟨p, ⟨hp1, _hp2⟩, rfl⟩
    obtain ⟨hp1a, hp1b⟩ := Set.mem_Ioo.mp hp1
    have hval : ‖(p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)‖ = p.1 := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      rw [Complex.norm_def, Complex.normSq_ofReal,
        Real.sqrt_mul_self (le_of_lt (lt_trans hR hp1a))]
    exact ⟨by rw [hval]; exact hp1a, by rw [hval]; exact hp1b⟩

/-- **The identity-theorem comparison of the junction identity.**  If two values `c`, `c'` both
satisfy the junction identity with the *same* datum `(ε,s)` near the same point `z ≠ 0`, then
`c = c'`.  Both sides are analytic on the annulus `{R < ‖u‖ < ρ}` (the first by hypothesis, the
second by `analyticOnNhd_germC_div`), which is preconnected by `isPreconnected_annulus`; the
identity theorem gives equality on the whole annulus, and injectivity of `germC` on its disc gives
`c = c'`. -/
lemma eq_of_junction_eventuallyEq {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {c c' : ℂ}
    {ρ ρg R : ℝ} {N : ℕ} {ε s : List Bool} {z : ℂ}
    (hρ : 0 < ρ) (hρg : 0 < ρg) (hR : 0 < R)
    (hgc : AnalyticOnNhd ℂ (germC a h) (Metric.ball 0 ρg))
    (hginj : Set.InjOn (fun u : ℂ => (germC a h u).2) (Metric.ball 0 ρg))
    (hκ : ‖(((eqLam a : ℝ) : ℂ)) ^ N * c‖ ≤ ρg * R)
    (hκ' : ‖(((eqLam a : ℝ) : ℂ)) ^ N * c'‖ ≤ ρg * R)
    (hzR : R < ‖z‖) (hz : ‖z‖ < ρ)
    (hfan : AnalyticOnNhd ℂ (fun u => bwdP a s (fan a h ε u)) (Metric.ball 0 ρ))
    (hzc : ‖(((eqLam a : ℝ) : ℂ)) ^ N * c / z‖ < ρg)
    (hzc' : ‖(((eqLam a : ℝ) : ℂ)) ^ N * c' / z‖ < ρg)
    (hev : (fun u => bwdP a s (fan a h ε u)) =ᶠ[𝓝 z]
      (fun u => eqMirror (germC a h (((eqLam a : ℝ) : ℂ) ^ N * c / u))))
    (hev' : (fun u => bwdP a s (fan a h ε u)) =ᶠ[𝓝 z]
      (fun u => eqMirror (germC a h (((eqLam a : ℝ) : ℂ) ^ N * c' / u)))) :
    c = c' := by
  have hzΩ : z ∈ {u : ℂ | R < ‖u‖ ∧ ‖u‖ < ρ} := ⟨hzR, hz⟩
  have hzn : z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hzR
    linarith [hR]
  have hfc : AnalyticOnNhd ℂ
      (fun u : ℂ => eqMirror (germC a h (((eqLam a : ℝ) : ℂ) ^ N * c / u)))
      {u : ℂ | R < ‖u‖ ∧ ‖u‖ < ρ} :=
    analyticOnNhd_germC_div (κ := (((eqLam a : ℝ) : ℂ) ^ N * c)) hρg hR hgc hκ
  have hfc' : AnalyticOnNhd ℂ
      (fun u : ℂ => eqMirror (germC a h (((eqLam a : ℝ) : ℂ) ^ N * c' / u)))
      {u : ℂ | R < ‖u‖ ∧ ‖u‖ < ρ} :=
    analyticOnNhd_germC_div (κ := (((eqLam a : ℝ) : ℂ) ^ N * c')) hρg hR hgc hκ'
  have hev1 : (fun u : ℂ => eqMirror (germC a h (((eqLam a : ℝ) : ℂ) ^ N * c / u))) =ᶠ[𝓝 z]
      (fun u : ℂ => bwdP a s (fan a h ε u)) := hev.symm
  have hev2 : (fun u : ℂ => eqMirror (germC a h (((eqLam a : ℝ) : ℂ) ^ N * c / u))) =ᶠ[𝓝 z]
      (fun u : ℂ => eqMirror (germC a h (((eqLam a : ℝ) : ℂ) ^ N * c' / u))) :=
    hev1.trans hev'
  have heqOn := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hfc hfc'
    (isPreconnected_annulus hR) hzΩ hev2
  have hzz := heqOn hzΩ
  have hzz2 : (germC a h (((eqLam a : ℝ) : ℂ) ^ N * c / z)).2
      = (germC a h (((eqLam a : ℝ) : ℂ) ^ N * c' / z)).2 := by
    have h := congrArg Prod.snd hzz
    simpa [eqMirror] using h
  have harg : (((eqLam a : ℝ) : ℂ) ^ N * c / z) = (((eqLam a : ℝ) : ℂ) ^ N * c' / z) :=
    hginj (by simpa [Metric.mem_ball, dist_zero_right] using hzc)
      (by simpa [Metric.mem_ball, dist_zero_right] using hzc') hzz2
  have h1 : (((eqLam a : ℝ) : ℂ)) ^ N * c = (((eqLam a : ℝ) : ℂ)) ^ N * c' := by
    have h2 := congrArg (fun w : ℂ => w * z) harg
    rwa [div_mul_cancel₀ _ hzn, div_mul_cancel₀ _ hzn] at h2
  exact mul_left_cancel₀ (pow_ne_zero N
    ((Complex.ofReal_ne_zero).mpr (ne_of_gt (eqLam_pos' ha0 ha1)))) h1

/-- **The branch letter is locally constant** along a continuous family of regular pairs whose
second entries stay off the branch cut. -/
lemma bLetter_eventuallyEq {a : ℝ} {X : Type*} [TopologicalSpace X]
    {γ : X → (ℂ × ℂ) × (ℂ × ℂ)} {t₀ : X}
    (hcont : ContinuousAt γ t₀) (hreg : ∀ᶠ t in 𝓝 t₀, RegPair a (γ t).1 (γ t).2)
    (hreg₀ : RegPair a (γ t₀).1 (γ t₀).2)
    (hslit : ((γ t₀).2.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + (γ t₀).2.2 ^ 2 ∈ Complex.slitPlane) :
    ∀ᶠ t in 𝓝 t₀, bLetter a (γ t).1 (γ t).2 = bLetter a (γ t₀).1 (γ t₀).2 := by
  set b₀ := bLetter a (γ t₀).1 (γ t₀).2 with hb₀
  have hspec : (γ t₀).1 = invBranch a b₀ (γ t₀).2 :=
    bLetter_spec (H0_invParam_ge_exists_invBranch hreg₀.1 hreg₀.2.2)
  have hother : invBranch a (!b₀) (γ t₀).2 ≠ (γ t₀).1 := by
    intro hcon
    have h2 : invBranch a b₀ (γ t₀).2 = invBranch a (!b₀) (γ t₀).2 := by rw [← hspec, hcon]
    have hbad : invBranch a true (γ t₀).2 = invBranch a false (γ t₀).2 := by
      rcases Bool.eq_false_or_eq_true b₀ with hb | hb
      · rw [hb] at h2
        simpa using h2
      · rw [hb] at h2
        simpa using h2.symm
    exact invBranch_true_ne_false hreg₀.2.2 hbad
  have hcont_other : ContinuousAt (fun t => invBranch a (!b₀) (γ t).2) t₀ :=
    ContinuousAt.comp' (f := fun t => (γ t).2)
      (invBranch_continuousAt (b := !b₀) (Q₀ := (γ t₀).2) hslit) hcont.snd
  have hδ : ContinuousAt (fun t => (γ t).1 - invBranch a (!b₀) (γ t).2) t₀ :=
    hcont.fst.sub hcont_other
  have hδne : (fun t => (γ t).1 - invBranch a (!b₀) (γ t).2) t₀ ≠ 0 := by
    simp only [sub_ne_zero]
    exact fun hcon => hother hcon.symm
  filter_upwards [hδ.eventually_ne hδne, hreg] with t ht hregt
  have hspec_t := bLetter_spec (H0_invParam_ge_exists_invBranch hregt.1 hregt.2.2)
  have hcases : bLetter a (γ t).1 (γ t).2 = b₀ ∨ bLetter a (γ t).1 (γ t).2 = !b₀ := by
    rcases hb0v : b₀ <;> rcases hv : bLetter a (γ t).1 (γ t).2 <;> simp [hb0v, hv]
  rcases hcases with h | h
  · exact h
  · exfalso
    rw [h] at hspec_t
    exact ht (by rw [hspec_t, sub_self])

/-- Two chains whose first `N` branch letters agree have the same forward word. -/
lemma fanWord_eq_of_letters {a : ℝ} : ∀ (N : ℕ) (q q' : ChainData),
    (∀ j : ℕ, j < N →
      bLetter a (q.1 (j : ℤ)) (q.1 ((j : ℤ) + 1)) =
        bLetter a (q'.1 (j : ℤ)) (q'.1 ((j : ℤ) + 1))) →
    fanWord a N q = fanWord a N q' := by
  intro N
  induction N with
  | zero => intro q q' _; simp [fanWord]
  | succ N ih =>
    intro q q' h
    have h0 := h 0 (by omega)
    simp only [Nat.cast_zero, zero_add] at h0
    rw [fanWord, fanWord, h0]
    congr 1
    refine ih (shiftZ a 1 q) (shiftZ a 1 q') (fun j hj => ?_)
    have h1 : (shiftZ a 1 q).1 (j : ℤ) = q.1 ((j : ℤ) + 1) := by rw [shiftZ_fst]
    have h2 : (shiftZ a 1 q).1 ((j : ℤ) + 1) = q.1 ((j : ℤ) + 1 + 1) := by rw [shiftZ_fst]
    have h3 : (shiftZ a 1 q').1 (j : ℤ) = q'.1 ((j : ℤ) + 1) := by rw [shiftZ_fst]
    have h4 : (shiftZ a 1 q').1 ((j : ℤ) + 1) = q'.1 ((j : ℤ) + 1 + 1) := by rw [shiftZ_fst]
    rw [h1, h2, h3, h4]
    have h5 := h (j + 1) (by omega)
    simpa only [Nat.cast_add, Nat.cast_one] using h5

/-- Two chains whose first `N` backward branch letters agree have the same backward word. -/
lemma bwdWord_eq_of_letters {a : ℝ} (N : ℕ) (q q' : ChainData)
    (h : ∀ j : ℕ, j < N →
      bLetter a (q.1 (-((j : ℤ) + 1))) (q.1 (-(j : ℤ))) =
        bLetter a (q'.1 (-((j : ℤ) + 1))) (q'.1 (-(j : ℤ)))) :
    bwdWord a N q = bwdWord a N q' := by
  rw [bwdWord, bwdWord]
  exact List.map_congr_left (fun j hj => by
    simp only [bwdLetter, List.mem_range] at hj ⊢
    exact h j hj)

/-- **The words of a chain are locally constant along a local section of `⁰H`.**

`f` is a continuous family of chains with `(f u).2.1 = u` (a witness of the `H0`-property of
`p = f p.2.1`).  If the entries of the pairs around `p` avoid the branch cut of the square root,
then near `p.2.1` the forward and backward words of `f u` of length `N` agree with those of `p`.
This is the rigidity of the *discrete* datum along the local sections. -/
lemma words_eventuallyEq_of_section {a : ℝ} {h : ℂ → ℂ} {N : ℕ} {p : ChainData}
    {f : ℂ → ChainData} {ε : ℝ} (hf0 : f p.2.1 = p) (hε : 0 < ε)
    (hf : ContinuousOn f (Metric.ball p.2.1 ε))
    (hmem : ∀ u ∈ Metric.ball p.2.1 ε, IsChain a h (f u) ∧ (f u).2.1 = u)
    (hslit : ∀ n : ℤ,
      ((p.1 n).1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + (p.1 n).2 ^ 2 ∈ Complex.slitPlane) :
    ∀ᶠ u in 𝓝 p.2.1, fanWord a N (f u) = fanWord a N p ∧
      bwdWord a N (f u) = bwdWord a N p := by
  have hpball : p.2.1 ∈ Metric.ball p.2.1 ε := by
    rw [Metric.mem_ball, dist_self]; exact hε
  have hcontAt : ContinuousAt f p.2.1 :=
    hf.continuousAt (Metric.ball_mem_nhds p.2.1 hε)
  have hcoord : ∀ j : ℤ, ContinuousAt (fun u : ℂ => (f u).1 j) p.2.1 := fun j =>
    ContinuousAt.comp' ((continuous_apply j).continuousAt) hcontAt.fst
  have hslit0 : ∀ n : ℤ,
      (((f p.2.1).1 n).1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + ((f p.2.1).1 n).2 ^ 2 ∈ Complex.slitPlane := by
    intro n
    rw [hf0]
    exact hslit n
  have hfwd : ∀ j : ℕ, j < N → ∀ᶠ u in 𝓝 p.2.1,
      bLetter a ((f u).1 (j : ℤ)) ((f u).1 ((j : ℤ) + 1)) =
        bLetter a ((f p.2.1).1 (j : ℤ)) ((f p.2.1).1 ((j : ℤ) + 1)) := by
    intro j hj
    refine bLetter_eventuallyEq (γ := fun u : ℂ => ((f u).1 (j : ℤ), (f u).1 ((j : ℤ) + 1)))
      ?_ ?_ ?_ ?_
    · exact ContinuousAt.prodMk (hcoord _) (hcoord _)
    · filter_upwards [Metric.ball_mem_nhds p.2.1 hε] with u hu
      exact ((hmem u hu).1).1 (j : ℤ)
    · exact ((hmem p.2.1 hpball).1).1 (j : ℤ)
    · exact hslit0 ((j : ℤ) + 1)
  have hbwd : ∀ j : ℕ, j < N → ∀ᶠ u in 𝓝 p.2.1,
      bLetter a ((f u).1 (-((j : ℤ) + 1))) ((f u).1 (-(j : ℤ))) =
        bLetter a ((f p.2.1).1 (-((j : ℤ) + 1))) ((f p.2.1).1 (-(j : ℤ))) := by
    intro j hj
    refine bLetter_eventuallyEq (γ := fun u : ℂ =>
      ((f u).1 (-((j : ℤ) + 1)), (f u).1 (-(j : ℤ)))) ?_ ?_ ?_ ?_
    · exact ContinuousAt.prodMk (hcoord _) (hcoord _)
    · filter_upwards [Metric.ball_mem_nhds p.2.1 hε] with u hu
      have h1 := ((hmem u hu).1).1 (-((j : ℤ) + 1))
      have hidx : -((j : ℤ) + 1) + 1 = -(j : ℤ) := by ring
      rwa [hidx] at h1
    · have h1 := ((hmem p.2.1 hpball).1).1 (-((j : ℤ) + 1))
      have hidx : -((j : ℤ) + 1) + 1 = -(j : ℤ) := by ring
      rwa [hidx] at h1
    · exact hslit0 (-(j : ℤ))
  have hfwd_all : ∀ᶠ u in 𝓝 p.2.1, ∀ j ∈ Finset.range N,
      bLetter a ((f u).1 (j : ℤ)) ((f u).1 ((j : ℤ) + 1)) =
        bLetter a ((f p.2.1).1 (j : ℤ)) ((f p.2.1).1 ((j : ℤ) + 1)) :=
    (Filter.eventually_all_finset (Finset.range N)).mpr
      (fun j hj => hfwd j (Finset.mem_range.mp hj))
  have hbwd_all : ∀ᶠ u in 𝓝 p.2.1, ∀ j ∈ Finset.range N,
      bLetter a ((f u).1 (-((j : ℤ) + 1))) ((f u).1 (-(j : ℤ))) =
        bLetter a ((f p.2.1).1 (-((j : ℤ) + 1))) ((f p.2.1).1 (-(j : ℤ))) :=
    (Filter.eventually_all_finset (Finset.range N)).mpr
      (fun j hj => hbwd j (Finset.mem_range.mp hj))
  filter_upwards [hfwd_all, hbwd_all] with u hu hu'
  constructor
  · rw [fanWord_eq_of_letters N (f u) (f p.2.1) (fun j hj => hu j (Finset.mem_range.mpr hj)), hf0]
  · rw [bwdWord_eq_of_letters N (f u) (f p.2.1) (fun j hj => hu' j (Finset.mem_range.mpr hj)), hf0]


/-! ## III. The canonical reading, the elementary inputs, and the assembly of the target

The limit analysis of Rychlik (Theorem 8, the "limits" step of `PAPER_PROOFS.md` §5) has three
inputs, and this section assembles them into the target `limit_analysis`:

* `Work.EQ.la_tail_bound_seq` (`TailBoundAt`): the *tail bound* — under the absence of a descendant
  value of the limit `c₀ -> `, the tail indices of all chains of a sequence of regular components
  whose values converge to `c₀` are uniformly bounded over an annulus of ratio `> 1/λ`.
* `Work.EQ.la_datum_finite` (`DatumFiniteAt`): for a *fixed* candidate datum (three words and a
  depth) there are only finitely many pairs `(c, S)` — value and regular component — realising it
  over the annulus.  This is the "determinacy" step: the junction identity of the reading is
  analytic and the boundary data `λ^M c/·` determine `c` through the injectivity of `germC`.
* `Work.EQ.la_regular_periodic`: every regular component whose value has no descendant is periodic
  under the shift `σ`.

From these:

* **(B)** Every `S ∈ 𝒮_c` is periodic, hence `ψ₁(S)` is invariant under a power of `λ`, hence meets
  the annulus (the geometric lemma `exists_mem_ann_of_periodic`); the components meeting the
  annulus carry readings at a uniform depth `M` in the finitely many candidate datums, and each
  datum allows only finitely many components (`DatumFiniteAt`).  So `𝒮_c` is finite.
* **(A)** If the values `c n` are not eventually `c₀`, take a strictly increasing subsequence with
  `c n ≠ c₀`; shifting each component into the annulus (the shift is a bijection of `⁰H` preserving
  `ψ`), the tail bound gives a uniform depth `M` and each shifted component carries a reading in
  one of the finitely many datums of length `M`, so the values `c n` lie in a finite set while
  converging to `c₀` — impossible.
-/

/-! ### The canonical reading in the `η = []` form -/

/-- `bLetter` (this file) and `bltr` (`chain_eq_candChain_of_tails`) are the same letter. -/
lemma bLetter_eq_bltr (a : ℝ) (P Q : ℂ × ℂ) : bLetter a P Q = bltr a P Q := by
  unfold bLetter bltr
  rfl

/-- The forward word `fanWord` of this file is the forward word `fwdW`. -/
lemma fanWord_eq_fwdW (a : ℝ) : ∀ (N : ℕ) (p : ChainData), fanWord a N p = fwdW a N p := by
  intro N
  induction N with
  | zero => intro p; rfl
  | succ N ih =>
      intro p
      change bLetter a (p.1 0) (p.1 1) :: fanWord a N (shiftZ a 1 p) =
        bltr a (p.1 0) (p.1 1) :: fwdW a N (shiftZ a 1 p)
      rw [bLetter_eq_bltr, ih]

/-- The backward word `bwdWord` of this file is the backward word `bwdW`. -/
lemma bwdWord_eq_bwdW (a : ℝ) (N : ℕ) (p : ChainData) : bwdWord a N p = bwdW a N p := by
  rw [bwdWord, bwdW]
  exact List.map_congr_left (fun j _ => by
    simp only [bwdLetter, bwdL]
    exact bLetter_eq_bltr a (p.1 (-((j : ℤ) + 1))) (p.1 (-(j : ℤ))))

/-- **The canonical reading (empty unstable word).**  A chain whose two tails are the principal
leaves from depth `N` on and whose value is `c` is the candidate chain built from its own forward
and backward words: below index `-N` the tail is the unstable leaf itself, i.e. the empty suffix
`fan a h [] u = germC a h u`. -/
theorem chain_eq_candChain_canonical {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {N : ℕ}
    {p : ChainData} (hp : IsChain a h p) {c : ℂ} (hval : p.2.1 * p.2.2 = c)
    (hfwd : ∀ n : ℕ, N ≤ n → p.1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * p.2.1))
    (hbwd : ∀ n : ℕ, N ≤ n → p.1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * p.2.2)) :
    p = candChain a h (fwdW a N p) [] (bwdW a N p) N c p.2.1 := by
  have hz : p.2.1 ≠ 0 := hp.2.1
  have hpsi2 : c / p.2.1 = p.2.2 := by
    rw [← hval]
    exact mul_div_cancel_left₀ _ hz
  have hread := chain_reading_of_tail hp (hfwd N le_rfl)
  have h0 : p.1 0 = fan a h (fwdW a N p) p.2.1 := by
    simpa using hread 0 (Nat.zero_le N)
  refine Prod.ext ?_ ?_
  · funext j
    rw [candChain_fst_apply]
    by_cases hj : 0 ≤ j
    · rw [if_pos hj]
      set m := j.toNat with hm
      have hjm : j = (m : ℤ) := by rw [hm]; exact (Int.toNat_of_nonneg hj).symm
      by_cases hjc : m ≤ N
      · rw [if_pos hjc]
        have hr : p.1 (m : ℤ) = fan a h ((fwdW a N p).drop m)
            (((eqLam a : ℝ) : ℂ) ^ (m : ℤ) * p.2.1) := by
          rw [zpow_natCast]
          exact hread m hjc
        rw [hjm, hr]
      · rw [if_neg hjc]
        have hmN : N ≤ m := by omega
        have hf : p.1 (m : ℤ) = germC a h
            (((eqLam a : ℝ) : ℂ) ^ (m : ℤ) * p.2.1) := by
          rw [zpow_natCast]
          exact hfwd m hmN
        rw [hjm, hf]
    · rw [if_neg hj]
      set k := (-j).toNat with hk
      have h2 : ((k : ℕ) : ℤ) = -j := by rw [hk]; exact Int.toNat_of_nonneg (by omega)
      have hjk : j = -((k : ℕ) : ℤ) := by rw [h2]; ring
      by_cases hkc : k ≤ N
      · rw [if_pos hkc]
        rw [hjk, bwdP_bwdW_take hp k hkc, h0]
      · rw [if_neg hkc]
        have hkN : N ≤ k := by omega
        have hb := hbwd k hkN
        have heta : eqMirror (fan a h (([] : List Bool).drop (k - N))
            (((eqLam a : ℝ) : ℂ) ^ (k : ℤ) * (c / p.2.1)))
            = eqMirror (germC a h (((eqLam a : ℝ) : ℂ) ^ k * p.2.2)) := by
          rw [hpsi2, zpow_natCast, List.drop_eq_nil_of_le (by simp), fan_nil']
        rw [hjk, hb]
        simp only [ugermC]
        rw [heta]
  · refine Prod.ext ?_ ?_
    · rfl
    · exact hpsi2.symm

/-! ### The elementary inputs of the assembly -/

/-- The value of a regular component lies in `RegValues`. -/
theorem regValues_of_isRegComp {a : ℝ} {h : ℂ → ℂ} {S : Set ChainData} {c : ℂ}
    (hS : IsRegComp a h S c) : c ∈ RegValues a h := by
  obtain ⟨-, ⟨p, hp, hpc⟩, hval⟩ := hS
  exact ⟨p, hp, fun q hq => hval q (by rw [hpc]; exact hq)⟩

/-- `ρ*` is positive as soon as a regular component exists. -/
theorem rhoStar_pos_of_isRegComp {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {S : Set ChainData} {c : ℂ} (hS : IsRegComp a h S c) :
    0 < rhoStar a h := by
  obtain ⟨ρ, hρ0, hρ⟩ := H0_invParam_ge ha0 ha1 hh
  refine lt_of_lt_of_le hρ0 (le_csInf ⟨‖c‖, c, regValues_of_isRegComp hS, rfl⟩ ?_)
  rintro x ⟨c', hc', rfl⟩
  obtain ⟨p, hp, hval⟩ := hc'
  rw [← hval p (mem_connectedComponentIn hp)]
  exact hρ p hp

/-- The words of `Bool` of a prescribed length, as a finite set. -/
def laWords (N : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (Fin N → Bool)).image (fun f => List.ofFn f)

lemma laWords_mem {N : ℕ} {l : List Bool} : l ∈ laWords N ↔ l.length = N := by
  constructor
  · intro h
    obtain ⟨f, -, hf⟩ := Finset.mem_image.mp h
    rw [← hf, List.length_ofFn]
  · intro h
    refine Finset.mem_image.mpr
      ⟨fun i : Fin N => l.get (Fin.cast h.symm i), Finset.mem_univ _, ?_⟩
    have key := (List.ofFn_congr h l.get).symm
    rw [List.ofFn_get l] at key
    exact key

/-- **A `σ`-periodic regular component meets every annulus of ratio `> 1/λ`.**

`S` is a nonempty preconnected subset of `⁰H` which the shifts `σ^{d·j}` (`j : ℤ`) map into
itself.  Then some point of `S` has `ψ₁ ∈ Ann r₁ r₂`.

The proof goes through connectedness of the image `{|ψ₁|}`: the orbit `λ^{dℤ}‖ψ₁ q₀‖` has points
below `r₁` and above `r₂`, and any preconnected subset of `ℝ` containing both contains every
intermediate value. -/
lemma exists_mem_ann_of_periodic {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {S : Set ChainData} {d : ℕ} (hd : 0 < d) (hne : S.Nonempty) (hH0 : S ⊆ H0 a h)
    (hpre : IsPreconnected S)
    (hshift : ∀ j : ℤ, ∀ q ∈ S, shiftZ a ((d : ℤ) * j) q ∈ S)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hratio : 1 / eqLam a < r₂ / r₁) :
    ∃ q ∈ S, q.2.1 ∈ Ann r₁ r₂ := by
  obtain ⟨q₀, hq₀⟩ := hne
  have hchain : IsChain a h q₀ := isChain_of_mem_H0 (hH0 hq₀)
  have hz₀ : q₀.2.1 ≠ 0 := hchain.2.1
  have hx : 0 < ‖q₀.2.1‖ := norm_pos_iff.mpr hz₀
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  set μ : ℝ := (eqLam a) ^ d with hμ
  have hμ0 : 0 < μ := pow_pos hlam0 d
  have hμ1 : μ < 1 := pow_lt_one₀ (le_of_lt hlam0) hlam1 hd.ne'
  have hr₁₂ : r₁ < r₂ := by
    have h1 : (1 / eqLam a) * r₁ < r₂ := (lt_div_iff₀ hr₁).mp hratio
    have h2 : (1 : ℝ) ≤ 1 / eqLam a := (one_le_div hlam0).mpr (le_of_lt hlam1)
    have h3 : r₁ ≤ (1 / eqLam a) * r₁ := by nlinarith
    linarith
  -- a point of `S` whose `‖ψ₁‖` is below `r₁`
  obtain ⟨k₁, hk₁⟩ : ∃ k : ℕ, μ ^ k * ‖q₀.2.1‖ < r₁ := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hr₁ hx) hμ1
    exact ⟨k, (lt_div_iff₀ hx).mp hk⟩
  -- a point of `S` whose `‖ψ₁‖` is above `r₂`
  obtain ⟨k₂, hk₂⟩ : ∃ k : ℕ, μ ^ k * r₂ < ‖q₀.2.1‖ := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hx hr₂) hμ1
    exact ⟨k, (lt_div_iff₀ hr₂).mp hk⟩
  set q₁ : ChainData := shiftZ a ((d : ℤ) * (k₁ : ℤ)) q₀ with hq₁
  set q₂ : ChainData := shiftZ a ((d : ℤ) * (-(k₂ : ℤ))) q₀ with hq₂
  have hq₁S : q₁ ∈ S := hshift (k₁ : ℤ) q₀ hq₀
  have hq₂S : q₂ ∈ S := hshift (-(k₂ : ℤ)) q₀ hq₀
  have hnorm₁ : ‖q₁.2.1‖ = μ ^ k₁ * ‖q₀.2.1‖ := by
    rw [hq₁, ac_norm_psi1_shiftZ ha0 ha1, zpow_mul, zpow_natCast, zpow_natCast, ← hμ]
  have hnorm₂ : ‖q₂.2.1‖ = (μ ^ k₂)⁻¹ * ‖q₀.2.1‖ := by
    rw [hq₂, ac_norm_psi1_shiftZ ha0 ha1, zpow_mul, zpow_neg, zpow_natCast, zpow_natCast, ← hμ]
  have hsmall : ‖q₁.2.1‖ < r₁ := by rw [hnorm₁]; exact hk₁
  have hbig : r₂ < ‖q₂.2.1‖ := by
    rw [hnorm₂, inv_mul_eq_div, lt_div_iff₀ (pow_pos hμ0 k₂)]
    linarith [hk₂]
  have himg : IsPreconnected ((fun q : ChainData => ‖q.2.1‖) '' S) :=
    hpre.image _ (by fun_prop)
  have hmem₁ : ‖q₁.2.1‖ ∈ (fun q : ChainData => ‖q.2.1‖) '' S := ⟨q₁, hq₁S, rfl⟩
  have hmem₂ : ‖q₂.2.1‖ ∈ (fun q : ChainData => ‖q.2.1‖) '' S := ⟨q₂, hq₂S, rfl⟩
  have hIcc := himg.Icc_subset hmem₁ hmem₂
  have hr₁mem : r₁ ∈ Set.Icc ‖q₁.2.1‖ ‖q₂.2.1‖ :=
    ⟨le_of_lt hsmall, le_trans hr₁₂.le hbig.le⟩
  obtain ⟨q, hqS, hq⟩ := hIcc hr₁mem
  exact ⟨q, hqS, by
    rw [Ann, Set.mem_ofPred_eq]
    exact ⟨hq.ge, hq.le.trans hr₁₂.le⟩⟩

/-! ### The component-shift lemmas -/

/-- The connected component of a shifted point is the shifted component. -/
lemma shiftZ_image_connectedComponentIn {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {p : ChainData} (hp : p ∈ H0 a h) (j : ℤ) :
    shiftZ a j '' connectedComponentIn (H0 a h) p
      = connectedComponentIn (H0 a h) (shiftZ a j p) := by
  have hp' : shiftZ a j p ∈ H0 a h := mem_H0_shiftZ ha0 ha1 hp j
  have hcont : Continuous (shiftZ a j) := continuous_shiftZ' a j
  have hsub : shiftZ a j '' connectedComponentIn (H0 a h) p ⊆ H0 a h := by
    rintro x ⟨y, hy, rfl⟩
    exact mem_H0_shiftZ ha0 ha1 (connectedComponentIn_subset _ _ hy) j
  refine Set.Subset.antisymm ?_ ?_
  · refine IsPreconnected.subset_connectedComponentIn
      (IsPreconnected.image isPreconnected_connectedComponentIn (shiftZ a j) hcont.continuousOn)
      (show shiftZ a j p ∈ shiftZ a j '' connectedComponentIn (H0 a h) p from
        ⟨p, mem_connectedComponentIn hp, rfl⟩) hsub
  · have hcont' : Continuous (shiftZ a (-j)) := continuous_shiftZ' a (-j)
    have hsub' : shiftZ a (-j) '' connectedComponentIn (H0 a h) (shiftZ a j p) ⊆ H0 a h := by
      rintro x ⟨y, hy, rfl⟩
      exact mem_H0_shiftZ ha0 ha1 (connectedComponentIn_subset _ _ hy) (-j)
    have h2 : shiftZ a (-j) '' connectedComponentIn (H0 a h) (shiftZ a j p) ⊆
        connectedComponentIn (H0 a h) p :=
      IsPreconnected.subset_connectedComponentIn
        (IsPreconnected.image isPreconnected_connectedComponentIn (shiftZ a (-j))
          hcont'.continuousOn)
        (show p ∈ shiftZ a (-j) '' connectedComponentIn (H0 a h) (shiftZ a j p) from
          ⟨shiftZ a j p, mem_connectedComponentIn hp', (shiftZ_neg_apply ha0 ha1 j p).2⟩)
        hsub'
    rintro x hx
    exact ⟨shiftZ a (-j) x, h2 ⟨x, hx, rfl⟩, (shiftZ_neg_apply ha0 ha1 j x).1⟩

/-- The image of a regular component under an integer shift is a regular component of the same
value. -/
lemma isRegComp_shiftZ {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {S : Set ChainData}
    {c : ℂ} (hS : IsRegComp a h S c) (j : ℤ) :
    IsRegComp a h (shiftZ a j '' S) c := by
  obtain ⟨hsub, ⟨p, hp, hpc⟩, hval⟩ := hS
  refine ⟨?_, ⟨shiftZ a j p, mem_H0_shiftZ ha0 ha1 hp j, ?_⟩, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    exact mem_H0_shiftZ ha0 ha1 (hsub hy) j
  · rw [hpc]
    exact shiftZ_image_connectedComponentIn ha0 ha1 hp j
  · rintro x ⟨y, hy, rfl⟩
    have hlam : ((eqLam a : ℝ) : ℂ) ^ j ≠ 0 :=
      zpow_ne_zero j (Complex.ofReal_ne_zero.mpr (ne_of_gt (eqLam_pos' ha0 ha1)))
    rw [shiftZ_psi1, shiftZ_psi2]
    have h1 : ((eqLam a : ℝ) : ℂ) ^ j * y.2.1 * (y.2.2 / ((eqLam a : ℝ) : ℂ) ^ j)
        = y.2.1 * y.2.2 := by
      field_simp
    rw [h1, hval y hy]



/-! ### The three inputs of the limit analysis -/

/-- The datum set: the pairs `(c, S)` — a value and a regular component of that value — for which
`S` contains a point of `Ann r₁ r₂` whose canonical reading at depth `M` is the candidate datum
`(f, [], b)` and whose tails are principal from `M` on. -/
def DatumSet (a : ℝ) (h : ℂ → ℂ) (r₁ r₂ : ℝ) (M : ℕ) (f b : List Bool) :
    Set (ℂ × Set ChainData) :=
  {p | IsRegComp a h p.2 p.1 ∧ ‖p.1‖ ≤ 2 * rhoStar a h ∧
    ∃ q ∈ p.2, q.2.1 ∈ Ann r₁ r₂ ∧ q = candChain a h f [] b M p.1 q.2.1 ∧
      (∀ k : ℕ, M ≤ k → q.1 (k : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ k * q.2.1)) ∧
      (∀ k : ℕ, M ≤ k → q.1 (-(k : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ k * q.2.2))}

/-- The **datum-finiteness** input of the limit analysis (the determinacy step), with the
existential radius `δ` peeled: for a fixed candidate datum there are only finitely many pairs
`(c, S)` realising it over `Ann r₁ r₂`. -/
def DatumFinite (a : ℝ) (h : ℂ → ℂ) (δ : ℝ) : Prop :=
  0 < δ ∧ ∀ (r₁ r₂ : ℝ), 0 < r₁ → r₁ < r₂ → r₂ < δ → 1 / eqLam a < r₂ / r₁ →
    ∀ (M : ℕ) (f b : List Bool), f.length = M → b.length = M →
    (eqLam a : ℝ) ^ M * r₂ < δ → (eqLam a : ℝ) ^ M * (2 * rhoStar a h) / r₁ < δ →
      (DatumSet a h r₁ r₂ M f b).Finite

/-- The **tail bound** input of the limit analysis, with the existential radius `δ` peeled. -/
def TailBound (a : ℝ) (h : ℂ → ℂ) (δ : ℝ) : Prop :=
  0 < δ ∧ ∀ (r₁ r₂ : ℝ), 0 < r₁ → r₁ < r₂ → r₂ < δ → 1 / eqLam a < r₂ / r₁ →
    ∀ (c₀ : ℂ),
      (∀ μ₁ ∈ CharSet a h, ∀ μ₂ ∈ CharSet a h, (μ₁ ≠ 1 ∨ μ₂ ≠ 1) →
        ∀ T : Set ChainData, ¬ IsRegComp a h T (c₀ * μ₁ * μ₂)) →
    ∀ (S : ℕ → Set ChainData) (c : ℕ → ℂ),
      (∀ n, IsRegComp a h (S n) (c n)) →
      (∀ n, ‖c n‖ ≤ 2 * rhoStar a h) →
      Filter.Tendsto c Filter.atTop (nhds c₀) →
      ∃ M : ℕ, ∀ n, ∀ q ∈ S n, q.2.1 ∈ Ann r₁ r₂ →
        (∀ k : ℕ, M ≤ k → q.1 (k : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ k * q.2.1)) ∧
        (∀ k : ℕ, M ≤ k → q.1 (-(k : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ k * q.2.2))

/-! ### (B): finiteness for a fixed value -/

/-- **(B)**, from the three inputs. -/
lemma la_B_core {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (hpos : 0 < rhoStar a h) {c : ℂ}
    (hc : ‖c‖ ≤ 2 * rhoStar a h)
    (hnd : ∀ μ₁ ∈ CharSet a h, ∀ μ₂ ∈ CharSet a h, (μ₁ ≠ 1 ∨ μ₂ ≠ 1) →
      ∀ T : Set ChainData, ¬ IsRegComp a h T (c * μ₁ * μ₂))
    (hper : ∀ S : Set ChainData, IsRegComp a h S c → ∃ d : ℕ, 0 < d ∧ ∀ q ∈ S, (hShift a)^[d] q ∈ S)
    {δ₁ δ₂ : ℝ} (hT : TailBound a h δ₁) (hD : DatumFinite a h δ₂)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₁₂ : r₁ < r₂)
    (hr₂δ₁ : r₂ < δ₁) (hr₂δ₂ : r₂ < δ₂) (hratio : 1 / eqLam a < r₂ / r₁)
    {N : ℕ} (hN₁ : (eqLam a : ℝ) ^ N * r₂ < δ₂)
    (hN₂ : (eqLam a : ℝ) ^ N * (2 * rhoStar a h) / r₁ < δ₂) :
    {S : Set ChainData | IsRegComp a h S c}.Finite := by
  have hmeets : ∀ S : Set ChainData, IsRegComp a h S c → ∃ q ∈ S, q.2.1 ∈ Ann r₁ r₂ := by
    intro S hS
    obtain ⟨d, hd, hcyc⟩ := hper S hS
    obtain ⟨hsubS, ⟨p, hp, hpc⟩, hvalS⟩ := hS
    have hcyc' : ∀ q ∈ connectedComponentIn (H0 a h) p,
        (hShift a)^[d] q ∈ connectedComponentIn (H0 a h) p := by
      intro q hq
      have h1 := hcyc q (by rw [hpc]; exact hq)
      rwa [hpc] at h1
    have hsh := shiftZ_mem_component ha0 ha1 hp hcyc'
    refine exists_mem_ann_of_periodic (h := h) ha0 ha1 hd ⟨p, ?_⟩ ?_ ?_
      (fun j q hq => ?_) hr₁ hr₂ hratio
    · rw [hpc]; exact mem_connectedComponentIn hp
    · rw [hpc]; exact connectedComponentIn_subset _ _
    · rw [hpc]; exact isPreconnected_connectedComponentIn
    · rw [hpc]; exact hsh j q (by rwa [hpc] at hq)
  refine Set.Finite.subset (t := {S : Set ChainData | IsRegComp a h S c})
    (s := {S : Set ChainData | IsRegComp a h S c ∧ ∃ q ∈ S, q.2.1 ∈ Ann r₁ r₂}) ?_
    (fun S hS => ⟨hS, hmeets S hS⟩)
  by_contra hnf
  have hinf : Set.Infinite {S : Set ChainData | IsRegComp a h S c ∧ ∃ q ∈ S, q.2.1 ∈ Ann r₁ r₂} :=
    hnf
  let g : ℕ ↪ {S // S ∈ {S : Set ChainData | IsRegComp a h S c ∧ ∃ q ∈ S, q.2.1 ∈ Ann r₁ r₂}} :=
    Set.Infinite.natEmbedding _ hinf
  let S' : ℕ → Set ChainData := fun n => (g n : Set ChainData)
  have hS'reg : ∀ n, IsRegComp a h (S' n) c := fun n => (g n).2.1
  have hS'ann : ∀ n, ∃ q ∈ S' n, q.2.1 ∈ Ann r₁ r₂ := fun n => (g n).2.2
  have hS'inj : Function.Injective S' := fun i j hij => g.injective (Subtype.ext hij)
  obtain ⟨M₀, hM₀⟩ := hT.2 r₁ r₂ hr₁ hr₁₂ hr₂δ₁ hratio c hnd S' (fun _ => c) hS'reg
    (fun _ => hc) tendsto_const_nhds
  choose q hqmem hqann using hS'ann
  set M := max M₀ N with hMdef
  have hM₀M : M₀ ≤ M := le_max_left _ _
  have hNM : N ≤ M := le_max_right _ _
  have hM₁ : (eqLam a : ℝ) ^ M * r₂ < δ₂ := by
    have hle : (eqLam a : ℝ) ^ M ≤ (eqLam a : ℝ) ^ N :=
      pow_le_pow_of_le_one (le_of_lt (eqLam_pos' ha0 ha1)) (le_of_lt (eqLam_lt_one' ha0 ha1)) hNM
    calc (eqLam a : ℝ) ^ M * r₂ ≤ (eqLam a : ℝ) ^ N * r₂ :=
          mul_le_mul_of_nonneg_right hle (le_of_lt hr₂)
      _ < δ₂ := hN₁
  have hM₂ : (eqLam a : ℝ) ^ M * (2 * rhoStar a h) / r₁ < δ₂ := by
    have hle : (eqLam a : ℝ) ^ M ≤ (eqLam a : ℝ) ^ N :=
      pow_le_pow_of_le_one (le_of_lt (eqLam_pos' ha0 ha1)) (le_of_lt (eqLam_lt_one' ha0 ha1)) hNM
    have hnn : 0 ≤ (2 * rhoStar a h) / r₁ := by positivity
    calc (eqLam a : ℝ) ^ M * (2 * rhoStar a h) / r₁
        = (eqLam a : ℝ) ^ M * ((2 * rhoStar a h) / r₁) := by ring
      _ ≤ (eqLam a : ℝ) ^ N * ((2 * rhoStar a h) / r₁) := mul_le_mul_of_nonneg_right hle hnn
      _ = (eqLam a : ℝ) ^ N * (2 * rhoStar a h) / r₁ := by ring
      _ < δ₂ := hN₂
  have hUnionFin : (⋃ f ∈ (laWords M : Set (List Bool)), ⋃ b ∈ (laWords M : Set (List Bool)),
      DatumSet a h r₁ r₂ M f b).Finite := by
    refine Set.Finite.biUnion (laWords M).finite_toSet (fun f hf => ?_)
    refine Set.Finite.biUnion (laWords M).finite_toSet (fun b hb => ?_)
    exact hD.2 r₁ r₂ hr₁ hr₁₂ hr₂δ₂ hratio M f b (laWords_mem.mp (Finset.mem_coe.mp hf))
      (laWords_mem.mp (Finset.mem_coe.mp hb)) hM₁ hM₂
  have hmem : ∀ n, (c, S' n) ∈ (⋃ f ∈ (laWords M : Set (List Bool)),
      ⋃ b ∈ (laWords M : Set (List Bool)), DatumSet a h r₁ r₂ M f b) := by
    intro n
    have hfn : (fwdW a M (q n)).length = M := fwdW_length a M _
    have hbn : (bwdW a M (q n)).length = M := bwdW_length a M _
    refine Set.mem_biUnion (Finset.mem_coe.mpr (laWords_mem.mpr hfn)) ?_
    refine Set.mem_biUnion (Finset.mem_coe.mpr (laWords_mem.mpr hbn)) ?_
    have hqchain : IsChain a h (q n) := isChain_of_mem_H0 ((hS'reg n).1 (hqmem n))
    have hqval : (q n).2.1 * (q n).2.2 = c := (hS'reg n).2.2 (q n) (hqmem n)
    have htail := hM₀ n (q n) (hqmem n) (hqann n)
    exact ⟨hS'reg n, hc, q n, hqmem n, hqann n,
      chain_eq_candChain_canonical ha0 ha1 hqchain hqval
        (fun k hk => htail.1 k (le_trans hM₀M hk)) (fun k hk => htail.2 k (le_trans hM₀M hk)),
      (fun k hk => htail.1 k (le_trans hM₀M hk)), (fun k hk => htail.2 k (le_trans hM₀M hk))⟩
  have hrange : Set.Finite (Set.range S') :=
    (hUnionFin.image (fun x : ℂ × Set ChainData => x.2)).subset (t := Set.range S') (fun x hx => by
      obtain ⟨n, rfl⟩ := hx
      exact ⟨(c, S' n), hmem n, rfl⟩)
  exact Set.infinite_range_of_injective hS'inj hrange

/-! ### (A): the values are eventually constant -/

/-- **(A)**, from the three inputs. -/
lemma la_A_core {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (hpos : 0 < rhoStar a h)
    {δ₁ δ₂ : ℝ} (hT : TailBound a h δ₁) (hD : DatumFinite a h δ₂)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₁₂ : r₁ < r₂)
    (hr₂δ₁ : r₂ < δ₁) (hr₂δ₂ : r₂ < δ₂) (hratio : 1 / eqLam a < r₂ / r₁)
    {N : ℕ} (hN₁ : (eqLam a : ℝ) ^ N * r₂ < δ₂)
    (hN₂ : (eqLam a : ℝ) ^ N * (2 * rhoStar a h) / r₁ < δ₂)
    {S : ℕ → Set ChainData} {c : ℕ → ℂ} {c₀ : ℂ}
    (hSreg : ∀ n, IsRegComp a h (S n) (c n)) (hc : ∀ n, ‖c n‖ ≤ 2 * rhoStar a h)
    (hlim : Filter.Tendsto c Filter.atTop (nhds c₀))
    (hnd : ∀ μ₁ ∈ CharSet a h, ∀ μ₂ ∈ CharSet a h, (μ₁ ≠ 1 ∨ μ₂ ≠ 1) →
      ∀ T : Set ChainData, ¬ IsRegComp a h T (c₀ * μ₁ * μ₂)) :
    ∃ k : ℕ, ∀ n ≥ k, c n = c₀ := by
  by_contra hcon
  push_neg at hcon
  -- a strictly increasing subsequence on which the values avoid `c₀`
  obtain ⟨ψ, hψmono, hψne⟩ : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ k, c (ψ k) ≠ c₀ := by
    have hex : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ c n ≠ c₀ := fun k => hcon k
    let ψ : ℕ → ℕ := fun k =>
      Nat.rec (Classical.choose (hex 0)) (fun _ p => Classical.choose (hex (p + 1))) k
    have hψsucc : ∀ k, ψ (k + 1) = Classical.choose (hex (ψ k + 1)) := fun k => rfl
    have hψne' : ∀ k, c (ψ k) ≠ c₀ := by
      intro k
      induction k with
      | zero => exact (Classical.choose_spec (hex 0)).2
      | succ k _ => rw [hψsucc]; exact (Classical.choose_spec (hex (ψ k + 1))).2
    have hψlt : ∀ k, ψ k < ψ (k + 1) := by
      intro k
      rw [hψsucc]
      have h := (Classical.choose_spec (hex (ψ k + 1))).1
      omega
    exact ⟨ψ, strictMono_nat_of_lt_succ hψlt, hψne'⟩
  -- shift every component of the subsequence into the annulus
  have hshift : ∀ n : ℕ, ∃ (p : ChainData) (j : ℤ), p ∈ S (ψ n) ∧
      (shiftZ a j p) ∈ shiftZ a j '' S (ψ n) ∧
      IsRegComp a h (shiftZ a j '' S (ψ n)) (c (ψ n)) ∧
      (shiftZ a j p).2.1 ∈ Ann r₁ r₂ := by
    intro n
    obtain ⟨-, ⟨p, hp, hpc⟩, -⟩ := hSreg (ψ n)
    have hchain : IsChain a h p := isChain_of_mem_H0 hp
    have hx : 0 < ‖p.2.1‖ := norm_pos_iff.mpr hchain.2.1
    obtain ⟨J, hJ⟩ := exists_finset_zpow_annulus (a := a) ha0 ha1 hr₁ hr₁₂ hratio hx le_rfl
    obtain ⟨j, -, hj1, hj2⟩ := hJ ‖p.2.1‖ le_rfl le_rfl
    refine ⟨p, j, by rw [hpc]; exact mem_connectedComponentIn hp, ⟨p, ?_, rfl⟩,
      isRegComp_shiftZ ha0 ha1 (hSreg (ψ n)) j, ?_⟩
    · rw [hpc]; exact mem_connectedComponentIn hp
    · rw [Ann, Set.mem_ofPred_eq, ac_norm_psi1_shiftZ ha0 ha1 j p]; exact ⟨hj1, hj2⟩
  choose p j hpS hpT hTreg hpAnn using hshift
  set Tm : ℕ → Set ChainData := fun n => shiftZ a (j n) '' S (ψ n) with hTmdef
  have hlim' : Filter.Tendsto (fun n => c (ψ n)) Filter.atTop (nhds c₀) :=
    hlim.comp hψmono.tendsto_atTop
  obtain ⟨M₀, hM₀⟩ := hT.2 r₁ r₂ hr₁ hr₁₂ hr₂δ₁ hratio c₀ hnd Tm (fun n => c (ψ n))
    (fun n => hTreg n) (fun n => hc (ψ n)) hlim'
  set M := max M₀ N with hMdef
  have hM₀M : M₀ ≤ M := le_max_left _ _
  have hNM : N ≤ M := le_max_right _ _
  have hM₁ : (eqLam a : ℝ) ^ M * r₂ < δ₂ := by
    have hle : (eqLam a : ℝ) ^ M ≤ (eqLam a : ℝ) ^ N :=
      pow_le_pow_of_le_one (le_of_lt (eqLam_pos' ha0 ha1)) (le_of_lt (eqLam_lt_one' ha0 ha1)) hNM
    calc (eqLam a : ℝ) ^ M * r₂ ≤ (eqLam a : ℝ) ^ N * r₂ :=
          mul_le_mul_of_nonneg_right hle (le_of_lt hr₂)
      _ < δ₂ := hN₁
  have hM₂ : (eqLam a : ℝ) ^ M * (2 * rhoStar a h) / r₁ < δ₂ := by
    have hle : (eqLam a : ℝ) ^ M ≤ (eqLam a : ℝ) ^ N :=
      pow_le_pow_of_le_one (le_of_lt (eqLam_pos' ha0 ha1)) (le_of_lt (eqLam_lt_one' ha0 ha1)) hNM
    have hnn : 0 ≤ (2 * rhoStar a h) / r₁ := by positivity
    calc (eqLam a : ℝ) ^ M * (2 * rhoStar a h) / r₁
        = (eqLam a : ℝ) ^ M * ((2 * rhoStar a h) / r₁) := by ring
      _ ≤ (eqLam a : ℝ) ^ N * ((2 * rhoStar a h) / r₁) := mul_le_mul_of_nonneg_right hle hnn
      _ = (eqLam a : ℝ) ^ N * (2 * rhoStar a h) / r₁ := by ring
      _ < δ₂ := hN₂
  have hUnionFin : (⋃ f ∈ (laWords M : Set (List Bool)), ⋃ b ∈ (laWords M : Set (List Bool)),
      DatumSet a h r₁ r₂ M f b).Finite := by
    refine Set.Finite.biUnion (laWords M).finite_toSet (fun f hf => ?_)
    refine Set.Finite.biUnion (laWords M).finite_toSet (fun b hb => ?_)
    exact hD.2 r₁ r₂ hr₁ hr₁₂ hr₂δ₂ hratio M f b (laWords_mem.mp (Finset.mem_coe.mp hf))
      (laWords_mem.mp (Finset.mem_coe.mp hb)) hM₁ hM₂
  have hmem : ∀ n, (c (ψ n), Tm n) ∈ (⋃ f ∈ (laWords M : Set (List Bool)),
      ⋃ b ∈ (laWords M : Set (List Bool)), DatumSet a h r₁ r₂ M f b) := by
    intro n
    have hfn : (fwdW a M (shiftZ a (j n) (p n))).length = M := fwdW_length a M _
    have hbn : (bwdW a M (shiftZ a (j n) (p n))).length = M := bwdW_length a M _
    refine Set.mem_biUnion (Finset.mem_coe.mpr (laWords_mem.mpr hfn)) ?_
    refine Set.mem_biUnion (Finset.mem_coe.mpr (laWords_mem.mpr hbn)) ?_
    have hqchain : IsChain a h (shiftZ a (j n) (p n)) :=
      isChain_of_mem_H0 ((hTreg n).1 (hpT n))
    have hqval : (shiftZ a (j n) (p n)).2.1 * (shiftZ a (j n) (p n)).2.2 = c (ψ n) :=
      (hTreg n).2.2 _ (hpT n)
    have htail := hM₀ n (shiftZ a (j n) (p n)) (hpT n) (hpAnn n)
    exact ⟨hTreg n, hc (ψ n), shiftZ a (j n) (p n), hpT n, hpAnn n,
      chain_eq_candChain_canonical ha0 ha1 hqchain hqval
        (fun k hk => htail.1 k (le_trans hM₀M hk)) (fun k hk => htail.2 k (le_trans hM₀M hk)),
      (fun k hk => htail.1 k (le_trans hM₀M hk)), (fun k hk => htail.2 k (le_trans hM₀M hk))⟩
  -- the values of the subsequence lie in a finite set avoiding `c₀`
  obtain ⟨F, hFfin, hFsub⟩ : ∃ F : Set ℂ, F.Finite ∧ Set.range (fun n => c (ψ n)) ⊆ F \ {c₀} := by
    refine ⟨(fun x : ℂ × Set ChainData => x.1) '' (⋃ f ∈ (laWords M : Set (List Bool)),
      ⋃ b ∈ (laWords M : Set (List Bool)), DatumSet a h r₁ r₂ M f b), hUnionFin.image _, ?_⟩
    rintro x ⟨n, rfl⟩
    exact ⟨⟨(c (ψ n), Tm n), hmem n, rfl⟩, hψne n⟩
  have hFdiff : (F \ {c₀}).Finite := hFfin.subset (fun x hx => hx.1)
  exact (hFdiff.isClosed.mem_of_tendsto hlim'
    (Filter.Eventually.of_forall (fun n => hFsub ⟨n, rfl⟩))).2 rfl

/-- **The assembly of the limit analysis from its three inputs.**  `hT` is
`Work.EQ.la_tail_bound_seq`, `hD` is `Work.EQ.la_datum_finite` and `hP` is
`Work.EQ.la_regular_periodic` (its conclusion for the fixed value `c`). -/
theorem limit_analysis_of {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r)
    (hT : ∃ δ : ℝ, TailBound a h δ) (hD : ∃ δ : ℝ, DatumFinite a h δ)
    (hP : ∀ c : ℂ, ‖c‖ ≤ 2 * rhoStar a h →
      (∀ μ₁ ∈ CharSet a h, ∀ μ₂ ∈ CharSet a h, (μ₁ ≠ 1 ∨ μ₂ ≠ 1) →
        ∀ T : Set ChainData, ¬ IsRegComp a h T (c * μ₁ * μ₂)) →
      ∀ S : Set ChainData, IsRegComp a h S c → ∃ d : ℕ, 0 < d ∧ ∀ q ∈ S, (hShift a)^[d] q ∈ S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r₁ r₂ : ℝ) (N : ℕ),
      0 < r₁ → r₁ < r₂ → r₂ < δ → r₂ / r₁ > 1 / eqLam a →
      (eqLam a : ℝ) ^ N * r₂ < δ →
        (eqLam a : ℝ) ^ N * (2 * rhoStar a h) / r₁ < δ →
      (∀ (S : ℕ → Set ChainData) (c : ℕ → ℂ) (c₀ : ℂ),
        (∀ n, IsRegComp a h (S n) (c n)) →
          (∀ n, ‖c n‖ ≤ 2 * rhoStar a h) →
          Filter.Tendsto c Filter.atTop (nhds c₀) →
        (∃ μ₁ ∈ CharSet a h, ∃ μ₂ ∈ CharSet a h, (μ₁ ≠ 1 ∨ μ₂ ≠ 1) ∧
            ∃ T : Set ChainData, IsRegComp a h T (c₀ * μ₁ * μ₂)) ∨
          ∃ k : ℕ, ∀ n ≥ k, c n = c₀) ∧
      (∀ c : ℂ, ‖c‖ ≤ 2 * rhoStar a h →
        (∃ μ₁ ∈ CharSet a h, ∃ μ₂ ∈ CharSet a h, (μ₁ ≠ 1 ∨ μ₂ ≠ 1) ∧
            ∃ T : Set ChainData, IsRegComp a h T (c * μ₁ * μ₂)) ∨
          {S : Set ChainData | IsRegComp a h S c}.Finite) := by
  classical
  by_cases hreg : ∃ S : Set ChainData, ∃ c : ℂ, IsRegComp a h S c
  · obtain ⟨S₀, c₀, hS₀⟩ := hreg
    have hpos : 0 < rhoStar a h := rhoStar_pos_of_isRegComp ha0 ha1 hh hS₀
    obtain ⟨δ₁, hTb⟩ := hT
    obtain ⟨δ₂, hDb⟩ := hD
    refine ⟨min δ₁ δ₂, lt_min hTb.1 hDb.1, ?_⟩
    intro r₁ r₂ N hr₁ hr₁₂ hr₂δ hratio hN₁ hN₂
    have hr₂ : 0 < r₂ := lt_trans hr₁ hr₁₂
    have hr₂δ₁ : r₂ < δ₁ := lt_of_lt_of_le hr₂δ (min_le_left _ _)
    have hr₂δ₂ : r₂ < δ₂ := lt_of_lt_of_le hr₂δ (min_le_right _ _)
    have hN₁' : (eqLam a : ℝ) ^ N * r₂ < δ₂ := lt_of_lt_of_le hN₁ (min_le_right _ _)
    have hN₂' : (eqLam a : ℝ) ^ N * (2 * rhoStar a h) / r₁ < δ₂ :=
      lt_of_lt_of_le hN₂ (min_le_right _ _)
    refine ⟨?_, ?_⟩
    · intro S c c₀ hSreg hc hlim
      by_cases hdesc : ∃ μ₁ ∈ CharSet a h, ∃ μ₂ ∈ CharSet a h, (μ₁ ≠ 1 ∨ μ₂ ≠ 1) ∧
          ∃ T : Set ChainData, IsRegComp a h T (c₀ * μ₁ * μ₂)
      · exact Or.inl hdesc
      · exact Or.inr (la_A_core (S := S) (c := c) (c₀ := c₀) ha0 ha1 hh hpos hTb hDb
          hr₁ hr₂ hr₁₂ hr₂δ₁ hr₂δ₂ hratio hN₁' hN₂' hSreg hc hlim
          (fun μ₁ hμ₁ μ₂ hμ₂ hne T hT' => hdesc ⟨μ₁, hμ₁, μ₂, hμ₂, hne, T, hT'⟩))
    · intro c hc
      by_cases hdesc : ∃ μ₁ ∈ CharSet a h, ∃ μ₂ ∈ CharSet a h, (μ₁ ≠ 1 ∨ μ₂ ≠ 1) ∧
          ∃ T : Set ChainData, IsRegComp a h T (c * μ₁ * μ₂)
      · exact Or.inl hdesc
      · have hnd : ∀ μ₁ ∈ CharSet a h, ∀ μ₂ ∈ CharSet a h, (μ₁ ≠ 1 ∨ μ₂ ≠ 1) →
            ∀ T : Set ChainData, ¬ IsRegComp a h T (c * μ₁ * μ₂) :=
          fun μ₁ hμ₁ μ₂ hμ₂ hne T hT' => hdesc ⟨μ₁, hμ₁, μ₂, hμ₂, hne, T, hT'⟩
        exact Or.inr (la_B_core ha0 ha1 hh hpos hc hnd (hP c hc hnd) hTb hDb
          hr₁ hr₂ hr₁₂ hr₂δ₁ hr₂δ₂ hratio hN₁' hN₂')
  · refine ⟨1, one_pos, ?_⟩
    intro r₁ r₂ N hr₁ hr₁₂ hr₂δ hratio hN₁ hN₂
    refine ⟨?_, ?_⟩
    · intro S c c₀ hSreg hc hlim
      exact absurd ⟨S 0, c 0, hSreg 0⟩ hreg
    · intro c hc
      exact Or.inr (Set.Finite.subset Set.finite_empty
        (fun S hS => absurd ⟨S, c, hS⟩ hreg))

/-- **The limit analysis over an annulus (Rychlik Lemma 5.1 / Theorem 8 core).**

`Work.EQ.rhoStar a h` is the infimum of `‖c‖` over the values of regular components of `H0 a h`,
`Work.EQ.CharSet a h` is `{1} ∪ {charVal ε : fan ε 0 = A₁}` (by `charVal_props` its elements have
norm `≤ 1`, with norm `1` only at `1`, so a "descendant value" `c * μ₁ * μ₂` with `(μ₁,μ₂) ≠ (1,1)`
has strictly smaller norm).  `Work.EQ.Ann r₁ r₂ = {z : r₁ ≤ ‖z‖ ≤ r₂}`.

For a small radius `δ` the following holds for every annulus `Ann r₁ r₂` inside `ball 0 δ` with
ratio `> 1/λ` and every depth `N` with `λ^N r₂ < δ` and `λ^N (2ρ*)/r₁ < δ`:

*(A) Limit of a sequence of regular components.*  For a sequence of regular components `S n` with
values `c n` (`‖c n‖ ≤ 2ρ*`) and `c n → c₀`, either some regular component has a descendant value,
or `c n = c₀` eventually.

*(B) Finiteness for a fixed value.*  For every `c` with `‖c‖ ≤ 2ρ*`, either some regular component
has a descendant value of `c`, or the set of all regular components of `H0 a h` with value `c` is
finite. -/
theorem limit_analysis {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r₁ r₂ : ℝ) (N : ℕ),
      0 < r₁ → r₁ < r₂ → r₂ < δ → r₂ / r₁ > 1 / Work.EQ.eqLam a →
      (Work.EQ.eqLam a : ℝ) ^ N * r₂ < δ →
        (Work.EQ.eqLam a : ℝ) ^ N * (2 * Work.EQ.rhoStar a h) / r₁ < δ →
      (∀ (S : ℕ → Set Work.EQ.ChainData) (c : ℕ → ℂ) (c₀ : ℂ),
        (∀ n, Work.EQ.IsRegComp a h (S n) (c n)) →
          (∀ n, ‖c n‖ ≤ 2 * Work.EQ.rhoStar a h) →
          Filter.Tendsto c Filter.atTop (nhds c₀) →
        (∃ μ₁ ∈ Work.EQ.CharSet a h, ∃ μ₂ ∈ Work.EQ.CharSet a h, (μ₁ ≠ 1 ∨ μ₂ ≠ 1) ∧
            ∃ T : Set Work.EQ.ChainData, Work.EQ.IsRegComp a h T (c₀ * μ₁ * μ₂)) ∨
          ∃ k : ℕ, ∀ n ≥ k, c n = c₀) ∧
      (∀ c : ℂ, ‖c‖ ≤ 2 * Work.EQ.rhoStar a h →
        (∃ μ₁ ∈ Work.EQ.CharSet a h, ∃ μ₂ ∈ Work.EQ.CharSet a h, (μ₁ ≠ 1 ∨ μ₂ ≠ 1) ∧
            ∃ T : Set Work.EQ.ChainData, Work.EQ.IsRegComp a h T (c * μ₁ * μ₂)) ∨
          {S : Set Work.EQ.ChainData | Work.EQ.IsRegComp a h S c}.Finite) := by
  classical
  by_cases hreg : ∃ S : Set ChainData, ∃ c : ℂ, IsRegComp a h S c
  · obtain ⟨S₀, c₀, hS₀⟩ := hreg
    have hpos : 0 < rhoStar a h := rhoStar_pos_of_isRegComp ha0 ha1 hh hS₀
    -- to be replaced by
    -- `exact limit_analysis_of ha0 ha1 hh ⟨_, la_tail_bound_seq ha0 ha1 hh hpos⟩
    --    ⟨_, la_datum_finite ha0 ha1 hh hpos⟩
    --    (fun c hc hnd => la_regular_periodic ha0 ha1 hh hpos hc hnd)`
    sorry
  · refine ⟨1, one_pos, ?_⟩
    intro r₁ r₂ N hr₁ hr₁₂ hr₂δ hratio hN₁ hN₂
    refine ⟨?_, ?_⟩
    · intro S c c₀ hSreg hc hlim
      exact absurd ⟨S 0, c 0, hSreg 0⟩ hreg
    · intro c hc
      exact Or.inr (Set.Finite.subset Set.finite_empty
        (fun S hS => absurd ⟨S, c, hS⟩ hreg))


end Work.EQ.LAFree
