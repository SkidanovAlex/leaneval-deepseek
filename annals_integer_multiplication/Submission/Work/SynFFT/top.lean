import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.logBound

/-!
# SynFFT: the top level (paper Prop 3.3)

The whole area's statement `HvdH.SynFFTProp` is assembled here from the pieces of `kit2.lean`:

* `ReorderProp` moves the parameters into the order the axis loop expects;
* `HasAxesFold` runs one `HasAxis` pass per axis (innermost first);
* `DropParamsProp` removes the parameters again.

The math packaging is `AxisIterProp` (the tensor factorisation over the whole axis list),
`SynDFTProp` (`synDFT` is `dftMultiN`) and `logBound` (the error `Σ log₂ tᵢ` is `< log₂(M r)`),
together with the size bounds `ArrSizeProp` for the cost estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.SynFFT

open HvdH

/-- `dftMultiN` only looks at the values below `ts.prod`. -/
lemma top_dftMultiN_congr (r : ℕ) (ts : List ℕ) (sgn : ℤ) {a b : Arr r}
    (h : ∀ k, k < ts.prod → a k = b k) (j : ℕ) (c : Fin r) :
    dftMultiN r ts sgn a j c = dftMultiN r ts sgn b j c := by
  unfold dftMultiN
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [h k (Finset.mem_range.mp hk)]

/-- `ApproxSL` at error `0` for the function the fixed-point values themselves define. -/
lemma top_approxSL_self (p r M : ℕ) (us : List (List (ℤ × ℤ))) (hlen : us.length = M) :
    ApproxSL p r M us (fun i j => fxC p ((us.getD i []).getD (j : ℕ) (0, 0))) 0 := by
  refine ⟨hlen, ?_⟩
  intro q _ c
  rw [sub_self, norm_zero, mul_zero]

/-- The `ApproxSL`-to-`ApproxR` conversion at the end of the pipeline, using the tensor
factorisation (`AxisIterProp`), the `synDFT`/`dftMultiN` bridge (`SynDFTProp`) and the strictness of
the error bound (`logBound`). -/
lemma top_approxR_of_axisIter (p r : ℕ) (ts : List ℕ) (sgn : ℤ) (us ws' : List (List (ℤ × ℤ)))
    (E : ℝ) (htpos : ∀ t ∈ ts, 0 < t)
    (hai : AxisIterProp) (hsd : SynDFTProp)
    (hlen : ws'.length = ts.prod) (hdisc : ∀ w ∈ ws', InDiscVec p r w)
    (happ : ApproxSL p r ts.prod ws' (axisIterN r sgn ts
      (fun i j => fxC p ((us.getD i []).getD (j : ℕ) (0, 0)))) E)
    (hE : E < (Nat.log 2 (ts.prod * r) : ℝ)) :
    ApproxR p ws' (synDFT r ts sgn (fxArr p ts.prod r us)) (Nat.log 2 (ts.prod * r) : ℝ) := by
  refine ⟨⟨hlen, hdisc⟩, ?_⟩
  intro i j
  have key : synDFT r ts sgn (fxArr p ts.prod r us) i j
      = axisIterN r sgn ts (fun i j => fxC p ((us.getD i []).getD (j : ℕ) (0, 0))) (i : ℕ) j := by
    rw [hsd r ts sgn (fxArr p ts.prod r us) i j,
      (top_dftMultiN_congr r ts sgn ?_ (i : ℕ) j).symm,
      ← congrFun (hai r ts sgn (fun i j => fxC p ((us.getD i []).getD (j : ℕ) (0, 0))) htpos
          (i : ℕ) i.isLt) j]
    intro k hk
    rw [dif_pos hk]
    rfl
  rw [key]
  have := happ.2 (i : ℕ) i.isLt j
  linarith

/-! ## The top-level assembly -/


/-! ## Small arithmetic facts for the cost estimate -/

lemma top_isz_nat_le (p : ℕ) : isz (p : ℤ) ≤ p + 3 := by
  have hpabs : (p : ℤ).natAbs = p := by simp
  simp only [isz, hpabs]
  have h : p.size ≤ p + 1 := by
    rw [Nat.size_le]
    calc p < 2 ^ p := Nat.lt_two_pow_self
      _ ≤ 2 ^ (p + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

lemma top_isz_sgn_le (sgn : ℤ) (h : sgn = 1 ∨ sgn = -1) : isz sgn ≤ 3 := by
  rcases h with h | h <;> simp [isz, h]

lemma top_isz_of_lt_pow (z : ℤ) (p : ℕ) (h : z.natAbs < 2 ^ p) : isz z ≤ p + 3 := by
  simp only [isz]
  have h1 : z.natAbs.size ≤ p := Nat.size_le.mpr h
  omega

lemma top_msize_le_log (M r : ℕ) (hr : 0 < r) : M.size ≤ Nat.log 2 (M * r) + 1 := by
  rw [Nat.size_le]
  calc M ≤ M * r := Nat.le_mul_of_pos_right _ hr
    _ < 2 ^ (Nat.log 2 (M * r) + 1) := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _


/-- **The area's statement** from the pieces. -/
theorem hasTop (hk : Work.SynFFT.KLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib)
    (hf : HvdH.FxLib) (hre : ReorderProp) (hdp : DropParamsProp) (haf : HasAxesFold)
    (hai : AxisIterProp) (hsd : SynDFTProp) (hsz : ArrSizeProp) (hcost : CostArithProp) :
    HvdH.SynFFTProp := by
  obtain ⟨prRe, Kr, hRe⟩ := hre
  obtain ⟨prDp, Kd, hDp⟩ := hdp
  obtain ⟨prFd, Kf, hFd⟩ := haf
  obtain ⟨hszE, hszA, hszL⟩ := hsz
  refine ⟨.seq prRe (.seq prFd prDp), 2000 * (Kr + Kf + Kd) * D * D + 2000, ?_⟩
  intro main p r ts sgn hPar hsgn
  have hlen : ts.length = D - 1 := hPar.1
  have hpowr : IsPow2 r := hPar.2.1
  have hpowa : ∀ t ∈ ts, IsPow2 t ∧ t ∣ 2 * r := hPar.2.2.1
  have hprod : ts.prod * r < 2 ^ p := hPar.2.2.2.1
  have hp100 : 100 ≤ p := hPar.2.2.2.2
  have hpow : ∀ t ∈ ts, IsPow2 t := fun t ht => (hpowa t ht).1
  have hdvd : ∀ t ∈ ts, t ∣ 2 * r := fun t ht => (hpowa t ht).2
  have hpr : 2 ≤ r := by
    obtain ⟨k, hk, rfl⟩ := hpowr
    simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hk
  have hp0 : 0 < p := by omega
  have hr1 : 1 ≤ r := by omega
  have ht2 : ∀ t ∈ ts, 2 ≤ t := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := hpow t ht
    simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hk
  have htpos : ∀ t ∈ ts, 0 < t := fun t ht => by have := ht2 t ht; omega
  have hMne : ts ≠ [] := by
    intro h
    rw [h] at hlen
    simp [HvdH.D] at hlen
  have hM2 : 2 ≤ ts.prod := by
    obtain ⟨t, ts', rfl⟩ := List.exists_cons_of_ne_nil hMne
    rw [List.prod_cons]
    have h1 : 2 ≤ t := ht2 t (by simp)
    have h2 : 1 ≤ ts'.prod := List.one_le_prod (fun x hx => le_trans (by norm_num) (ht2 x (by simp [hx])))
    nlinarith
  have hMpos : 0 < ts.prod := by omega
  have h2rp : 2 * r < 2 ^ p := lt_of_le_of_lt (Nat.mul_le_mul_right r hM2) hprod
  have htlt : ∀ t ∈ ts, t < 2 ^ p := by
    intro t ht
    have h1 : t ≤ 2 * r := Nat.le_of_dvd (by omega) (hdvd t ht)
    omega
  have hlogE : (ts.map (fun t => (Nat.log 2 t : ℝ))).sum < (Nat.log 2 (ts.prod * r) : ℝ) :=
    logBound r ts p hpr hp100 hpow hprod
  refine fun vs hpre s R hR => ?_
  obtain ⟨us, rest, hvs, hDisc⟩ := hpre
  subst hvs
  obtain ⟨out1, s1, n1, hp1, he1, hn1, hs1, ho1⟩ :=
    hRe main p r ts sgn us rest _ rfl s R hR
  obtain ⟨out2, s2, n2, hp2, he2, hn2, hs2, ho2⟩ :=
    hFd main p r ts sgn us (fun i j => fxC p ((us.getD i []).getD (j : ℕ) (0, 0))) 0 rest
      hpowr hpow hdvd ht2 h2rp hsgn hDisc.1 hDisc.2
      (top_approxSL_self p r ts.prod us hDisc.1) out1 (by rw [hp1]; rfl) s1 R hs1
  obtain ⟨ws', hp2a, hlen', hdisc', happ'⟩ := hp2
  obtain ⟨out3, s3, n3, hp3, he3, hn3, hs3, ho3⟩ :=
    hDp main (ofList (cvecs ws')) ts sgn r p rest out2 (by rw [hp2a]) s2 R hs2
  have hsz : ts.prod.size ≤ Nat.log 2 (ts.prod * r) + 1 := top_msize_le_log ts.prod r hr1
  have hpisz : isz (p : ℤ) ≤ p + 3 := top_isz_nat_le p
  have hrisz : isz (r : ℤ) ≤ p + 3 := top_isz_of_lt_pow (r : ℤ) p (by simp; omega)
  have hsisz : isz sgn ≤ 3 := top_isz_sgn_le sgn hsgn
  -- size bounds
  have hus : vsz (rarrVal us) ≤ ts.prod * (r * (2 * p + 6) + 2) + 1 :=
    hszA p r ts.prod hp0 us hDisc
  have hw' : vsz (rarrVal ws') ≤ ts.prod * (r * (2 * p + 6) + 2) + 1 :=
    hszA p r ts.prod hp0 ws' ⟨hlen', hdisc'⟩
  have hts : vsz (intList ts) ≤ ts.length * (p + 3) + 1 := hszL ts p htlt
  have hD1 : 1 ≤ D := by norm_num [HvdH.D]
  have hDlen : ts.length + 1 = D := by omega
  refine ⟨out3, s3, n1 + (n2 + n3), ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨us, rest, ws', rfl, ?_, ?_⟩
    · rw [hp3]; rfl
    · exact top_approxR_of_axisIter p r ts sgn us ws' _ htpos hai hsd hlen' hdisc'
        (by simpa using happ') (by simpa using hlogE)
  · exact Eval.seq he1 (Eval.seq he2 he3)
  · exact hcost Kr Kd Kf p r ts sgn us ws' n1 n2 n3 hlen hpr hM2 hn1 hn2 hn3
      hus hw' hts hsz hpisz hrisz hsisz
  · rw [hs3]
  · intro k hk
    rw [ho3 k hk, ho2 k hk, ho1 k hk]

end Work.SynFFT
