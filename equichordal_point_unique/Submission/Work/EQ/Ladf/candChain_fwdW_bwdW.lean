import Mathlib
import Submission.Work.EQ.chain_eq_candChain_of_tails
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.CycleDefs

/-!
# Reading the words off the candidate chain

`CycleDefs.candChain a h ε η s N c z` is the explicit candidate chain attached to two fan ends
(`ε` forward, `η` mirror backward), a backward sign list `s` on `[-N,0]` and the value `c` of the
invariant parameter.  The purpose of this file is the *inverse* of the reading step
(`chain_eq_candChain_of_tails`): if `candChain a h f [] b M c z` is an honest chain of the
equichordal relation, then its forward word of length `M` is `f` and its backward word is `b`.

The proof is purely combinatorial.  On the forward side `fwdW` reads the branch letter of the pair
`(p.1 j, p.1 (j+1))` for `0 ≤ j < M`; `candChain` gives definitionally
`p.1 j = fan a h (f.drop j) (λ^j z) = invBranch a f[j] (p.1 (j+1))`, so the letter is `f[j]` as
soon as `bltr` can tell the two backward branches apart -- and that is exactly what `IsChain`
supplies, through `RegPair`: at each point `Q = p.1 (j+1)` we have `bsq (subO1 a Q) ≠ 0`
(`HeteroAlgebra`), whence `invBranch a true Q ≠ invBranch a false Q`.  The backward side is the
same argument with `j` replaced by `-j` (the middle piece of `candChain` is the iterated
`bwdP a (b.take j)`).
-/

namespace Work.EQ.Ladf

open Work.EQ

/-! ## Telling the two backward branches apart -/

/-- The two backward branches at a point off the isotropic lines through `O₁` are distinct. -/
theorem invBranch_ne_of_bsq {a : ℝ} {Q : ℂ × ℂ} (hQ : bsq (subO1 a Q) ≠ 0) :
    invBranch a true Q ≠ invBranch a false Q := by
  intro h
  have hZ : subO1 a Q ≠ 0 := by
    intro h0
    exact hQ (by rw [h0]; simp [bsq])
  have hρ : brho (subO1 a Q) ≠ 0 := brho_ne_zero hQ
  have h1 : invBranch a true Q + Q = ((brho (subO1 a Q))⁻¹) • subO1 a Q := by
    have := invBranch_add a true Q
    simpa using this
  have h2 : invBranch a false Q + Q = -(((brho (subO1 a Q))⁻¹) • subO1 a Q) := by
    have := invBranch_add a false Q
    simpa using this
  have h3 : ((brho (subO1 a Q))⁻¹) • subO1 a Q
      = -(((brho (subO1 a Q))⁻¹) • subO1 a Q) := by
    calc ((brho (subO1 a Q))⁻¹) • subO1 a Q = invBranch a true Q + Q := h1.symm
      _ = invBranch a false Q + Q := by rw [h]
      _ = -(((brho (subO1 a Q))⁻¹) • subO1 a Q) := h2
  have h4 : (2 * ((brho (subO1 a Q))⁻¹)) • subO1 a Q = 0 := by
    rw [two_mul, add_smul]
    nth_rewrite 1 [h3]
    rw [neg_add_cancel]
  have h5 : (2 * ((brho (subO1 a Q))⁻¹)) = 0 := by
    rcases smul_eq_zero.mp h4 with hc | hc
    · exact hc
    · exact absurd hc hZ
  have h6 : ((brho (subO1 a Q))⁻¹) = 0 := by
    rcases mul_eq_zero.mp h5 with hc | hc
    · exact absurd hc (by norm_num)
    · exact hc
  exact hρ (inv_eq_zero.mp h6)

/-- `bltr` names the branch of a backward image: the letter of the pair
`(invBranch a s Q, Q)` is `s`. -/
theorem bltr_invBranch {a : ℝ} {Q : ℂ × ℂ} (hQ : bsq (subO1 a Q) ≠ 0) (s : Bool) :
    bltr a (invBranch a s Q) Q = s := by
  have hne := invBranch_ne_of_bsq hQ
  cases s
  · unfold bltr
    rw [dif_neg (fun h => hne h.symm), dif_pos rfl]
  · unfold bltr
    rw [dif_pos rfl]

/-! ## Unfolding the candidate chain at nonnegative and negative indices -/

/-- The index `j ∈ [0,N]` of a candidate chain is the fan value of the `j`-th suffix of `ε`. -/
theorem candChain_fst_nonneg (a : ℝ) (h : ℂ → ℂ) (ε η s : List Bool) (N : ℕ) (c z : ℂ) {j : ℕ}
    (hj : j ≤ N) :
    (candChain a h ε η s N c z).1 (j : ℤ) =
      fan a h (ε.drop j) (((eqLam a : ℝ) : ℂ) ^ j * z) := by
  rw [candChain_fst_apply]
  rw [ite_eq_left (Int.natCast_nonneg j), Int.toNat_natCast, ite_eq_left hj, zpow_natCast]

/-- The index `-j` of a candidate chain (for `0 ≤ j ≤ N`) is the iterated backward image of the
index-`0` point along the first `j` letters of `s`. -/
theorem candChain_fst_neg (a : ℝ) (h : ℂ → ℂ) (ε η s : List Bool) (N : ℕ) (c z : ℂ) {j : ℕ}
    (hj : j ≤ N) :
    (candChain a h ε η s N c z).1 (-(j : ℤ)) = bwdP a (s.take j) (fan a h ε z) := by
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    have hh := candChain_fst_nonneg a h ε η s N c z (j := 0) (by omega)
    simpa using hh
  · rw [candChain_fst_apply]
    rw [ite_eq_right (by omega : ¬ (0 ≤ -(j : ℤ)))]
    simp only [neg_neg, Int.toNat_natCast]
    rw [ite_eq_left hj]

/-! ## The two words -/

/-- **The forward word of a `fan`-shaped chain.**  If the first `N + 1` points of `p` are the fan
values of the suffixes of `f` (`f.length = N`) and every point `p.1 (j+1)`, `j < N`, is off the
isotropic lines through `O₁`, then `fwdW a N p = f`. -/
theorem fwdW_eq_of_fan (a : ℝ) (h : ℂ → ℂ) : ∀ (f : List Bool) (p : ChainData) (z : ℂ),
    (∀ j : ℕ, j ≤ f.length →
      p.1 (j : ℤ) = fan a h (f.drop j) (((eqLam a : ℝ) : ℂ) ^ j * z)) →
    (∀ j : ℕ, j < f.length → bsq (subO1 a (p.1 ((j : ℤ) + 1))) ≠ 0) →
    fwdW a f.length p = f := by
  intro f
  induction f with
  | nil => intro p z _ _; simp [fwdW]
  | cons s t ih =>
    intro p z hexp hnd
    have hstep : fwdW a (s :: t).length p =
        bltr a (p.1 0) (p.1 1) :: fwdW a t.length (shiftZ a 1 p) := rfl
    rw [hstep]
    have h0 : p.1 0 = fan a h (s :: t) z := by
      have hh := hexp 0 (by simp)
      simpa using hh
    have h1 : p.1 1 = fan a h t ((eqLam a : ℂ) * z) := by
      have hh := hexp 1 (by simp)
      simpa using hh
    have hnd0 : bsq (subO1 a (p.1 1)) ≠ 0 := by
      have hh := hnd 0 (by simp)
      simpa using hh
    have hletter : bltr a (p.1 0) (p.1 1) = s := by
      have h2 : bltr a (p.1 0) (p.1 1) = bltr a (invBranch a s (p.1 1)) (p.1 1) := by
        rw [h0, fan_cons', h1]
      rw [h2]
      exact bltr_invBranch hnd0 s
    rw [hletter]
    congr 1
    refine ih (shiftZ a 1 p) ((eqLam a : ℂ) * z) ?_ ?_
    · intro j hj
      have hh := hexp (j + 1) (by simp; omega)
      have hidx : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
      rw [hidx] at hh
      have hdrop : (s :: t).drop (j + 1) = t.drop j := rfl
      have hpow : ((eqLam a : ℝ) : ℂ) ^ (j + 1) * z
          = ((eqLam a : ℝ) : ℂ) ^ j * (((eqLam a : ℝ) : ℂ) * z) := by
        rw [pow_succ]; ring
      rw [hdrop, hpow] at hh
      rw [shiftZ_fst]
      exact hh
    · intro j hj
      have hh := hnd (j + 1) (by simp; omega)
      have hidx : ((j + 1 : ℕ) : ℤ) + 1 = (j : ℤ) + 1 + 1 := by push_cast; ring
      rw [shiftZ_fst, ← hidx]
      exact hh

/-- **The target.**  A candidate chain with empty unstable word whose underlying data is an honest
chain has forward word `f` and backward word `b` (of length `M`). -/
theorem candChain_fwdW_bwdW {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) {f b : List Bool} {M : ℕ} (hf : f.length = M)
    (hb : b.length = M) {c z : ℂ}
    (hc : Work.EQ.IsChain a h (Work.EQ.candChain a h f [] b M c z)) :
    Work.EQ.fwdW a M (Work.EQ.candChain a h f [] b M c z) = f ∧
      Work.EQ.bwdW a M (Work.EQ.candChain a h f [] b M c z) = b := by
  set p := Work.EQ.candChain a h f [] b M c z with hp
  constructor
  · rw [← hf]
    refine fwdW_eq_of_fan a h f p z ?_ ?_
    · intro j hj
      exact candChain_fst_nonneg a h f [] b M c z (by omega)
    · intro j hj
      exact (hc.1 (j : ℤ)).2.2
  · rw [← hb]
    apply List.ext_getElem
    · rw [bwdW_length]
    · intro j h1 h2
      simp only [bwdW, List.getElem_map, List.getElem_range]
      have hjM : j < M := by omega
      have hfst : p.1 (-(j : ℤ)) = bwdP a (b.take j) (fan a h f z) :=
        candChain_fst_neg a h f [] b M c z (by omega)
      have hpair : p.1 (-((j : ℤ) + 1)) = invBranch a b[j] (p.1 (-(j : ℤ))) := by
        have hh1 : p.1 (-((j : ℤ) + 1)) = bwdP a (b.take (j + 1)) (fan a h f z) := by
          have := candChain_fst_neg a h f [] b M c z (j := j + 1) (by omega)
          simpa using this
        rw [hh1, hfst, List.take_succ_eq_append_getElem h2, bwdP_append, bwdP_singleton']
      have hQ : bsq (subO1 a (p.1 (-(j : ℤ)))) ≠ 0 := by
        have hh2 := (hc.1 (-((j : ℤ) + 1))).2.2
        have hk : -((j : ℤ) + 1) + 1 = -(j : ℤ) := by ring
        rw [hk] at hh2
        simpa [bsq, subO1] using hh2
      unfold bwdL
      rw [hpair]
      exact bltr_invBranch hQ (b[j])

end Work.EQ.Ladf
