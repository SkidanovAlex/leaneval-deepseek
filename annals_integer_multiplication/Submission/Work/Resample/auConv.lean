import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.auConvDefs
import Submission.Work.ConvR.basic
import Submission.Work.Fx.piUBound
import Submission.Work.Fx.piIter
import Submission.Work.Resample.auWtErr
import Submission.Work.Resample.auWiRow
import Submission.Work.Resample.auWtSz
import Submission.Work.Resample.auStreamSz
import Submission.Work.Resample.auSizes
import Submission.Work.Resample.auIdx
import Submission.Work.Resample.auPhiDisc
import Submission.Work.Resample.auChunkWord
import Submission.Work.Resample.auSetup

/-!
# The resampling word `q` of paper Lemma 4.9 (`Work.Resample.auConv`)

The uniform word of Lemma 4.9: it reads the static table `auTable p α s t` (inside `auPvals`),
the input array `ofList (u.map cfxVal)` of length `s` and produces the `t` outputs
`auPhi p α s t u`.  It is assembled from

* `Work.Resample.auSetup`: builds the window stream `auStreamV p α s t u` (the chunks: weights of
  output `k` paired with the window `auWin p α s t u k` centred at `auK s t k`);
* `Work.Resample.auChunkWord`: maps one chunk to its output
  `cfxVal (tdiv (Σ W_i z_i.1) 2^p, tdiv (Σ W_i z_i.2) 2^p)`;
* `HvdH.KernelLib.mapList` maps over the stream and collects the outputs into one value, exactly
  `cvecVal w`; and the disc invariance of `w` is `Work.Resample.auPhiDisc`, which uses the weight
  accuracy `Work.Resample.auWtErr` and the window row-sum bound `Work.Resample.auWiRow`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.Resample

open HvdH





lemma conv_ofList_inj {l₁ l₂ : List Val} (h : ofList l₁ = ofList l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b bs => exact absurd h (by simp [ofList])
  | cons a as ih =>
    cases l₂ with
    | nil => exact absurd h.symm (by simp [ofList])
    | cons b bs =>
      have h' : a = b ∧ ofList as = ofList bs := Val.cons.inj h
      rw [h'.1, ih h'.2]

lemma conv_cfxVal_inj {z₁ z₂ : ℤ × ℤ} (h : cfxVal z₁ = cfxVal z₂) : z₁ = z₂ := by
  have h' := Val.cons.inj h
  exact Prod.ext (Val.int.inj h'.1) (Val.int.inj h'.2)

lemma conv_auWts_length (p α s t k : ℕ) : (auWts p α s t k).length = auL p α := by simp [auWts]
lemma conv_auWin_length (p α s t : ℕ) (u : List (ℤ × ℤ)) (k : ℕ) :
    (auWin p α s t u k).length = auL p α := by simp [auWin]
lemma conv_auStream_length (p α s t : ℕ) (u : List (ℤ × ℤ)) : (auStream p α s t u).length = t := by
  simp [auStream]

lemma conv_auStream_get (p α s t : ℕ) (u : List (ℤ × ℤ)) (i : ℕ) (hi : i < t) :
    (auStream p α s t u).get ⟨i, by rw [conv_auStream_length]; exact hi⟩ = auChunk p α s t u i := by
  simp only [auStream, List.get_eq_getElem, List.length_map, List.length_range,
    List.getElem_map, List.getElem_range, Fin.val_mk]

lemma conv_auWts_getD (p α s t k i : ℕ) (hi : i < auL p α) :
    (auWts p α s t k).getD i .nil = Val.int (auWt p α t (auNsq p α s t k i)) := by
  have h1 : i < (auWts p α s t k).length := by rw [conv_auWts_length]; exact hi
  rw [List.getD_eq_getElem _ .nil h1]
  simp [auWts]

lemma conv_auWin_map_getD (p α s t : ℕ) (u : List (ℤ × ℤ)) (k i : ℕ) (hi : i < auL p α) :
    ((auWin p α s t u k).map cfxVal).getD i .nil
      = cfxVal ((auWin p α s t u k).getD i (0, 0)) := by
  have h1 : i < ((auWin p α s t u k).map cfxVal).length := by
    rw [List.length_map, conv_auWin_length]; exact hi
  rw [List.getD_eq_getElem _ .nil h1, List.getElem_map]
  have h2 : i < (auWin p α s t u k).length := by rw [conv_auWin_length]; exact hi
  rw [List.getD_eq_getElem _ (0,0) h2]

lemma conv_auWin_getD (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (hαp : α ^ 2 < p) (u : List (ℤ × ℤ)) (hu : u.length = s) (k : ℕ) (hk : k < t)
    (i : ℕ) (hi : i < auL p α) :
    (auWin p α s t u k).getD i (0, 0) = u.getD (auJ p α s t k i) (0, 0) := by
  have h1 : i < (auWin p α s t u k).length := by rw [conv_auWin_length]; exact hi
  rw [auWin, List.getD_eq_getElem _ (0,0) (by rw [List.length_map, List.length_range]; exact hi),
    List.getElem_map, List.getElem_range]
  exact auIdx p α s t hs hst hα hp hαp u hu k hk i hi

lemma conv_auSum_fst (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (hαp : α ^ 2 < p) (u : List (ℤ × ℤ)) (hu : u.length = s) (k : ℕ) (hk : k < t) :
    (∑ i ∈ Finset.range (auL p α),
        auWt p α t (auNsq p α s t k i) * ((auWin p α s t u k).getD i (0, 0)).1)
      = (∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t k i) *
          (if h : auJ p α s t k i < s then (fun j : Fin s => u.getD (j : ℕ) (0, 0))
            ⟨auJ p α s t k i, h⟩ else 0).1) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [dif_pos (auJ_lt p α s t k i hs), conv_auWin_getD p α s t hs hst hα hp hαp u hu k hk i hi]

lemma conv_auSum_snd (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (hαp : α ^ 2 < p) (u : List (ℤ × ℤ)) (hu : u.length = s) (k : ℕ) (hk : k < t) :
    (∑ i ∈ Finset.range (auL p α),
        auWt p α t (auNsq p α s t k i) * ((auWin p α s t u k).getD i (0, 0)).2)
      = (∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t k i) *
          (if h : auJ p α s t k i < s then (fun j : Fin s => u.getD (j : ℕ) (0, 0))
            ⟨auJ p α s t k i, h⟩ else 0).2) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [dif_pos (auJ_lt p α s t k i hs), conv_auWin_getD p α s t hs hst hα hp hαp u hu k hk i hi]

lemma conv_auWt_approx (p α s t : ℕ) (hα : 2 ≤ α) (hp : 100 ≤ p) (ht : 1 ≤ t) :
    ∀ k i : ℕ, |(auWt p α t (auNsq p α s t k i) : ℝ) - (2 : ℝ) ^ p * auWi p α s t k i| ≤ 2 := by
  have hpi : |(auPi p : ℝ) - (2 : ℝ) ^ auPrec p * Real.pi| ≤ 1 :=
    Work.Fx.piUBound (auPrec p) (by simp only [auPrec]; omega)
      ((Work.Fx.piIter (auPrec p)).1 (auPrec p))
  intro k i
  have hN : 0 ≤ auNsq p α s t k i := auNsq_nonneg p α s t k i
  have h := Work.Resample.auWtErr p α t ((auNsq p α s t k i).toNat) hp hα ht hpi
  have hN' : (((auNsq p α s t k i).toNat : ℕ) : ℤ) = auNsq p α s t k i :=
    Int.toNat_of_nonneg hN
  have harg : (auWt p α t (auNsq p α s t k i) : ℝ)
      = (auWt p α t (((auNsq p α s t k i).toNat : ℕ) : ℤ) : ℝ) := by rw [hN']
  have hc : ((((auNsq p α s t k i).toNat : ℕ)) : ℝ) = ((auNsq p α s t k i : ℤ) : ℝ) := by
    rw [← hN']
    exact (Int.cast_natCast _).symm
  have hgoal : (2 : ℝ) ^ p * auWi p α s t k i
      = (2 : ℝ) ^ p * (1 / (2 * (α : ℝ))) * Real.exp
          (-(Real.pi * ((((auNsq p α s t k i).toNat : ℕ)) : ℝ) / ((α : ℝ) ^ 2 * (t : ℝ) ^ 2))) := by
    rw [auWi, hc]
    ring
  rw [harg, hgoal]
  exact h

lemma conv_auL_le_two_pow (p α : ℕ) (hαp : α ^ 2 < p) (hp : 100 ≤ p) : auL p α ≤ 2 ^ p := by
  have hsq : Nat.sqrt p * Nat.sqrt p ≤ p := Nat.sqrt_le p
  have hα : α ≤ Nat.sqrt p := by rw [Nat.le_sqrt']; omega
  have h1 : auL p α = 2 * ((Nat.sqrt p + 1) * α) + 1 := rfl
  rw [h1]
  have h2 : 2 * ((Nat.sqrt p + 1) * α) + 1 ≤ 2 * ((Nat.sqrt p + 1) * Nat.sqrt p) + 1 := by
    have hle := Nat.mul_le_mul_left (Nat.sqrt p + 1) hα
    omega
  have hsq2 : 1 ≤ Nat.sqrt p := by
    rw [Nat.le_sqrt']; omega
  have h5 : Nat.sqrt p ≤ p := by
    calc Nat.sqrt p ≤ Nat.sqrt p * Nat.sqrt p := by nlinarith
      _ ≤ p := hsq
  have h4 : 2 * ((Nat.sqrt p + 1) * Nat.sqrt p) + 1 ≤ 2 ^ p := by
    have h6 : (Nat.sqrt p + 1) * Nat.sqrt p ≤ p + p := by nlinarith
    have h7 : 4 * p + 5 ≤ 2 ^ p := Work.Resample.four_p_add_five_le_two_pow p (by omega)
    omega
  omega

lemma conv_isz_tdiv_sum_le (p L : ℕ) (W z : ℕ → ℤ) (hL : L ≤ 2 ^ p)
    (hW : ∀ i < L, (W i).natAbs ≤ 2 ^ p) (hz : ∀ i < L, (z i).natAbs ≤ 2 ^ p) :
    isz (Int.tdiv (∑ i ∈ Finset.range L, W i * z i) ((2 : ℤ) ^ p)) ≤ 2 * p + 3 := by
  have h2p : ((2 : ℤ) ^ p).natAbs = 2 ^ p := by rw [Int.natAbs_pow]; norm_num
  have hterm : ∀ i ∈ Finset.range L, (W i * z i).natAbs ≤ 2 ^ p * 2 ^ p := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (hW i hi) (hz i hi)
  have hsum : (∑ i ∈ Finset.range L, W i * z i).natAbs ≤ L * (2 ^ p * 2 ^ p) := by
    calc (∑ i ∈ Finset.range L, W i * z i).natAbs
        ≤ ∑ i ∈ Finset.range L, (W i * z i).natAbs := Int.natAbs_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range L, (2 ^ p * 2 ^ p) := Finset.sum_le_sum hterm
      _ = L * (2 ^ p * 2 ^ p) := by simp [Finset.sum_const]
  have hA : (∑ i ∈ Finset.range L, W i * z i).natAbs ≤ 2 ^ (3 * p) := by
    refine le_trans hsum ?_
    calc L * (2 ^ p * 2 ^ p) ≤ 2 ^ p * (2 ^ p * 2 ^ p) := Nat.mul_le_mul_right _ hL
      _ = 2 ^ (3 * p) := by rw [← pow_add]; ring_nf
  have hdiv : (Int.tdiv (∑ i ∈ Finset.range L, W i * z i) ((2 : ℤ) ^ p)).natAbs ≤ 2 ^ (2 * p) := by
    rw [Int.natAbs_tdiv, h2p]
    apply Nat.div_le_of_le_mul
    have h3 : (2:ℕ) ^ p * 2 ^ (2 * p) = 2 ^ (3 * p) := by rw [← pow_add]; ring_nf
    rw [h3]
    exact hA
  rw [isz]
  have hsize : (Int.tdiv (∑ i ∈ Finset.range L, W i * z i) ((2 : ℤ) ^ p)).natAbs.size ≤ 2 * p + 1 := by
    rw [Nat.size_le]
    exact lt_of_le_of_lt hdiv (Nat.pow_lt_pow_right (by norm_num) (by omega))
  omega

lemma conv_auChunk_eq_auPhi (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (hαp : α ^ 2 < p) (u : List (ℤ × ℤ)) (hu : u.length = s) (k j : Fin t)
    (h : auChunk p α s t u (k : ℕ) = auChunk p α s t u (j : ℕ)) :
    auPhi p α s t (fun j' => u.getD (j' : ℕ) (0, 0)) k
      = auPhi p α s t (fun j' => u.getD (j' : ℕ) (0, 0)) j := by
  have hparts := Val.cons.inj h
  have hW : auWts p α s t (k : ℕ) = auWts p α s t (j : ℕ) := conv_ofList_inj hparts.1
  have hWin : (auWin p α s t u (k : ℕ)).map cfxVal = (auWin p α s t u (j : ℕ)).map cfxVal :=
    conv_ofList_inj hparts.2
  have hWp : ∀ i < auL p α,
      auWt p α t (auNsq p α s t (k : ℕ) i) = auWt p α t (auNsq p α s t (j : ℕ) i) := by
    intro i hi
    have hcong := congrArg (fun l => l.getD i .nil) hW
    rw [conv_auWts_getD p α s t (k : ℕ) i hi, conv_auWts_getD p α s t (j : ℕ) i hi] at hcong
    exact Val.int.inj hcong
  have hWinf : ∀ i < auL p α,
      (auWin p α s t u (k : ℕ)).getD i (0, 0) = (auWin p α s t u (j : ℕ)).getD i (0, 0) := by
    intro i hi
    have hcong := congrArg (fun l => l.getD i .nil) hWin
    rw [conv_auWin_map_getD p α s t u (k : ℕ) i hi, conv_auWin_map_getD p α s t u (j : ℕ) i hi] at hcong
    exact conv_cfxVal_inj hcong
  have hkey : ∀ i < auL p α,
      u.getD (auJ p α s t (k : ℕ) i) (0, 0) = u.getD (auJ p α s t (j : ℕ) i) (0, 0) := by
    intro i hi
    rw [← conv_auWin_getD p α s t hs hst hα hp hαp u hu (k : ℕ) k.isLt i hi,
      ← conv_auWin_getD p α s t hs hst hα hp hαp u hu (j : ℕ) j.isLt i hi]
    exact hWinf i hi
  have hsum1 : (∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t (k : ℕ) i) *
        (if h : auJ p α s t (k : ℕ) i < s then (fun j' : Fin s => u.getD (j' : ℕ) (0, 0))
          ⟨auJ p α s t (k : ℕ) i, h⟩ else 0).1)
      = (∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t (j : ℕ) i) *
        (if h : auJ p α s t (j : ℕ) i < s then (fun j' : Fin s => u.getD (j' : ℕ) (0, 0))
          ⟨auJ p α s t (j : ℕ) i, h⟩ else 0).1) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hWp i hi, dif_pos (auJ_lt p α s t (k : ℕ) i hs), dif_pos (auJ_lt p α s t (j : ℕ) i hs)]
    congr 1
    exact congrArg Prod.fst (hkey i hi)
  have hsum2 : (∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t (k : ℕ) i) *
        (if h : auJ p α s t (k : ℕ) i < s then (fun j' : Fin s => u.getD (j' : ℕ) (0, 0))
          ⟨auJ p α s t (k : ℕ) i, h⟩ else 0).2)
      = (∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t (j : ℕ) i) *
        (if h : auJ p α s t (j : ℕ) i < s then (fun j' : Fin s => u.getD (j' : ℕ) (0, 0))
          ⟨auJ p α s t (j : ℕ) i, h⟩ else 0).2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hWp i hi, dif_pos (auJ_lt p α s t (k : ℕ) i hs), dif_pos (auJ_lt p α s t (j : ℕ) i hs)]
    congr 1
    exact congrArg Prod.snd (hkey i hi)
  refine Prod.ext ?_ ?_
  · simp only [auPhi]
    rw [hsum1]
  · simp only [auPhi]
    rw [hsum2]


/-- Numeric bound used for the size of the window stream. -/
lemma cost_L' (p X : ℕ) (hp : 1 ≤ p) (hX : 1 ≤ X) :
    (2 * X) * (3 * p + 16) + 4 + (4 * p + 8) + 1 ≤ 55 * (X * (p + 1)) := by nlinarith

/-- Numeric bound used for the cost of the setup word. -/
lemma conv_cost_set (s t L Cs M X : ℕ) (hX : 1 ≤ X) (hst : s < t) (hM : M ≤ 2 * X)
    (hCs : Cs ≤ 4 * s + 2 * M) (hL : L ≤ 2 * X) :
    s + t * L + Cs + 1 ≤ 11 * ((t + 1) * X) := by nlinarith

/-- `auOff p α s < s`. -/
lemma conv_auOff_lt (p α s : ℕ) (hs : 0 < s) : auOff p α s < s := by
  have h2 : s * ((auM p α + s - 1) / s) ≤ auM p α + s - 1 := Nat.mul_div_le _ _
  have h3 : auM p α ≤ s * ((auM p α + s - 1) / s) := by
    have h4 : auM p α + s - 1
        = s * ((auM p α + s - 1) / s) + (auM p α + s - 1) % s := (Nat.div_add_mod _ _).symm
    have h5 : (auM p α + s - 1) % s < s := Nat.mod_lt _ hs
    omega
  rw [auOff]
  omega

theorem auConv (hk : HvdH.KernelLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib) : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p) (htp : t < 2 ^ p) (hKN : K * p < N), HvdH.WordR main prog (fun vs => ∃ (u : List (ℤ × ℤ)) (rest : List HvdH.Val), vs = HvdH.ofList (u.map HvdH.cfxVal) :: auPvals p α s t ++ rest ∧ u.length = s ∧ (∀ z ∈ u, HvdH.inDisc p z)) (fun vs out => ∃ (u : List (ℤ × ℤ)) (rest : List HvdH.Val) (w : List (ℤ × ℤ)), vs = HvdH.ofList (u.map HvdH.cfxVal) :: auPvals p α s t ++ rest ∧ out = HvdH.cvecVal w :: auPvals p α s t ++ rest ∧ w.length = t ∧ (∀ z ∈ w, HvdH.inDisc p z) ∧ (∀ k : Fin t, w.getD k (0,0) = auPhi p α s t (fun j => u.getD j (0,0)) k)) (fun _ => K * (t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (K * p) + p + 1)) := by
  obtain ⟨setupP, Ks, hsetup⟩ := auSetup hk hi hl
  obtain ⟨chunkP, Kc, hchunk⟩ := auChunkWord hk hi
  obtain ⟨comb, Km, hmap⟩ := hk.mapList
  have hS1 : 1 ≤ Ks + Kc + Km + 9 := by omega
  have hSpow : Ks + Kc + Km + 9 ≤ (Ks + Kc + Km + 9) ^ 4 := by
    have h : 1 ≤ (Ks + Kc + Km + 9) ^ 3 := Nat.one_le_pow 3 _ hS1
    have h4 : (Ks + Kc + Km + 9) ^ 4
        = (Ks + Kc + Km + 9) * (Ks + Kc + Km + 9) ^ 3 := by ring
    nlinarith
  have hKsK : Ks ≤ 64 * (Ks + Kc + Km + 9) ^ 4 + 100 := by omega
  have hKcK : Kc ≤ 64 * (Ks + Kc + Km + 9) ^ 4 + 100 := by omega
  have hKmK : Km ≤ 64 * (Ks + Kc + Km + 9) ^ 4 + 100 := by omega
  have hKbig : 11 * Ks + 2 * Kc + 55 * Km + 1 ≤ 64 * (Ks + Kc + Km + 9) ^ 4 + 100 := by omega
  refine ⟨Cmd.seq setupP (comb chunkP), 64 * (Ks + Kc + Km + 9) ^ 4 + 100, ?_⟩
  intro main N Cm hm hM p α s t hs hst hα hp hαp htp hKN
  intro vs hpre s0 R hR
  obtain ⟨u, rest, hvs, hulen, hdisc⟩ := hpre
  have hp1 : 1 ≤ p := by omega
  have ht1 : 1 ≤ t := by omega
  obtain ⟨hOffSz, hCopSz, hMSz, hLSz, hKle, hKmono, hK0, hslide, hslideSz, hCopS⟩ :=
    auSizes p α s t hs hst hα hp hαp htp
  have hL2p : auL p α ≤ 2 ^ p := conv_auL_le_two_pow p α hαp hp
  have hwt : ∀ k i : ℕ, |(auWt p α t (auNsq p α s t k i) : ℝ) - (2 : ℝ) ^ p * auWi p α s t k i| ≤ 2 :=
    conv_auWt_approx p α s t hα hp ht1
  have hwtS := auWtSz p α s t hs hα hp hαp (by omega) hwt
  have hrow := auWiRow p α s t hs hα hαp hst
  have hwin_disc : ∀ k, k < t → ∀ z ∈ auWin p α s t u k, inDisc p z := by
    intro k hk z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
    rw [List.mem_range] at hi
    rw [auIdx p α s t hs hst hα hp hαp u hulen k hk i hi]
    refine hdisc _ ?_
    rw [List.getD_eq_getElem _ (0,0) (by rw [hulen]; exact auJ_lt p α s t k i hs)]
    exact List.getElem_mem _
  obtain ⟨out1, s1, n1, hpost1, hev1, hn1, hstk1, hoth1⟩ :=
    hsetup main p α s t u rest hulen hdisc hs hα hp hαp hst vs hvs s0 R hR
  have hstreamSz := auStreamSz p α s t hs hst hα hp hαp u hwin_disc (fun k i hk hi => (hwtS k i).2)
  let c : ℕ := Kc * (auL p α + 1) * (Cm (Kc * p) + p + 1)
  let L' : ℕ := max (auL p α * (3 * p + 16) + 4) (4 * p + 8)
  have hKcN : Kc * p < N := by
    calc Kc * p ≤ (64 * (Ks + Kc + Km + 9) ^ 4 + 100) * p := Nat.mul_le_mul_right p hKcK
      _ < N := hKN
  have hbody : ∀ x, (∃ k, k < t ∧ x = auChunk p α s t u k) →
      HvdH.WordR main chunkP (fun vs => vs = x :: auPvals p α s t ++ rest)
        (fun _ out => ∃ y, out = y :: auPvals p α s t ++ rest ∧
          (∀ k : Fin t, x = auChunk p α s t u (k : ℕ) →
            y = cfxVal (auPhi p α s t (fun j : Fin s => u.getD (j : ℕ) (0, 0)) k)) ∧ vsz y ≤ L')
        (fun _ => c) := by
    intro x hx
    obtain ⟨kx, hkx, rfl⟩ := hx
    have hwin_disc' : ∀ i < auL p α, inDisc p ((auWin p α s t u kx).getD i (0,0)) := by
      intro i hi
      refine hwin_disc kx hkx _ ?_
      rw [List.getD_eq_getElem _ (0,0) (by rw [conv_auWin_length]; exact hi)]
      exact List.getElem_mem _
    have hck := hchunk main N Cm hm hM p α s t (auL p α)
      (fun i => auWt p α t (auNsq p α s t kx i))
      (fun i => (auWin p α s t u kx).getD i (0,0))
      (auWts p α s t kx) ((auWin p α s t u kx).map cfxVal) rest hKcN hp1 hst htp hαp
      (conv_auWts_length p α s t kx) (by rw [List.length_map, conv_auWin_length])
      (fun i hi => conv_auWts_getD p α s t kx i hi)
      (fun i hi => conv_auWin_map_getD p α s t u kx i hi)
      (fun i hi => (hwtS kx i).1) hwin_disc'
    refine hk.conseq (main := main) (p := chunkP)
      (P := fun vs => vs = HvdH.Val.cons (HvdH.ofList (auWts p α s t kx)) (HvdH.ofList ((auWin p α s t u kx).map cfxVal)) :: auPvals p α s t ++ rest)
      (Q := fun _ out => out = HvdH.cfxVal (Int.tdiv (∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t kx i) * ((auWin p α s t u kx).getD i (0,0)).1) ((2:ℤ)^p), Int.tdiv (∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t kx i) * ((auWin p α s t u kx).getD i (0,0)).2) ((2:ℤ)^p)) :: auPvals p α s t ++ rest)
      (C := fun _ => Kc * (auL p α + 1) * (Cm (Kc * p) + p + 1))
      (P' := fun vs => vs = HvdH.Val.cons (HvdH.ofList (auWts p α s t kx)) (HvdH.ofList ((auWin p α s t u kx).map cfxVal)) :: auPvals p α s t ++ rest)
      (Q' := fun _ out => ∃ y, out = y :: auPvals p α s t ++ rest ∧
        (∀ k : Fin t, HvdH.Val.cons (HvdH.ofList (auWts p α s t kx)) (HvdH.ofList ((auWin p α s t u kx).map cfxVal)) = auChunk p α s t u (k : ℕ) →
          y = cfxVal (auPhi p α s t (fun j : Fin s => u.getD (j : ℕ) (0, 0)) k)) ∧ vsz y ≤ L')
      (C' := fun _ => c) hck (fun vs hv => hv) ?_ (fun vs _ => le_rfl)
    intro vs out hv hq
    rw [hq]
    refine ⟨cfxVal (Int.tdiv (∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t kx i) * ((auWin p α s t u kx).getD i (0,0)).1) ((2:ℤ)^p), Int.tdiv (∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t kx i) * ((auWin p α s t u kx).getD i (0,0)).2) ((2:ℤ)^p)), rfl, ?_, ?_⟩
    · intro k hchunk
      have hA : Int.tdiv (∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t kx i) * ((auWin p α s t u kx).getD i (0,0)).1) ((2:ℤ)^p) = (auPhi p α s t (fun j : Fin s => u.getD (j : ℕ) (0,0)) ⟨kx, hkx⟩).1 := by
        rw [conv_auSum_fst p α s t hs hst hα hp hαp u hulen kx hkx]
        simp only [auPhi]
      have hB : Int.tdiv (∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t kx i) * ((auWin p α s t u kx).getD i (0,0)).2) ((2:ℤ)^p) = (auPhi p α s t (fun j : Fin s => u.getD (j : ℕ) (0,0)) ⟨kx, hkx⟩).2 := by
        rw [conv_auSum_snd p α s t hs hst hα hp hαp u hulen kx hkx]
        simp only [auPhi]
      rw [hA, hB]
      rw [← conv_auChunk_eq_auPhi p α s t hs hst hα hp hαp u hulen ⟨kx, hkx⟩ k hchunk]
    · have hX : isz (Int.tdiv (∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t kx i) * ((auWin p α s t u kx).getD i (0,0)).1) ((2:ℤ)^p)) ≤ 2 * p + 3 :=
        conv_isz_tdiv_sum_le p (auL p α) _ _ hL2p (fun i hi => (hwtS kx i).1)
          (fun i hi => Work.ConvR.natAbs_fst_le_of_inDisc (hwin_disc' i hi))
      have hY : isz (Int.tdiv (∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t kx i) * ((auWin p α s t u kx).getD i (0,0)).2) ((2:ℤ)^p)) ≤ 2 * p + 3 :=
        conv_isz_tdiv_sum_le p (auL p α) _ _ hL2p (fun i hi => (hwtS kx i).1)
          (fun i hi => Work.ConvR.natAbs_snd_le_of_inDisc (hwin_disc' i hi))
      have hb : isz (Int.tdiv (∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t kx i) * ((auWin p α s t u kx).getD i (0,0)).1) ((2:ℤ)^p)) + isz (Int.tdiv (∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t kx i) * ((auWin p α s t u kx).getD i (0,0)).2) ((2:ℤ)^p)) + 1 ≤ 4 * p + 8 := by omega
      simpa only [HvdH.cfxVal, Work.ConvR.vsz_cons, Work.ConvR.vsz_int] using
        (le_trans hb (le_max_right (auL p α * (3 * p + 16) + 4) (4 * p + 8)) : isz (Int.tdiv (∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t kx i) * ((auWin p α s t u kx).getD i (0,0)).1) ((2:ℤ)^p)) + isz (Int.tdiv (∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t kx i) * ((auWin p α s t u kx).getD i (0,0)).2) ((2:ℤ)^p)) + 1 ≤ L')
  have hxs : ∀ x ∈ auStream p α s t u, (∃ k, k < t ∧ x = auChunk p α s t u k) ∧ vsz x ≤ L' := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_range] at hk
    exact ⟨⟨k, hk, rfl⟩, le_trans (hstreamSz.1 k hk) (le_max_left _ _)⟩
  have hmap' := hmap main chunkP (auPvals p α s t ++ rest)
    (fun x => ∃ k, k < t ∧ x = auChunk p α s t u k)
    (fun x y => ∀ k : Fin t, x = auChunk p α s t u (k : ℕ) →
      y = cfxVal (auPhi p α s t (fun j : Fin s => u.getD (j : ℕ) (0, 0)) k))
    c L' hbody (auStream p α s t u) hxs
  obtain ⟨out2, s2, n2, ⟨ys, hout2, hforall⟩, hev2, hn2, hstk2, hoth2⟩ :=
    hmap' (auStreamV p α s t u :: auPvals p α s t ++ rest) rfl s1 R (by rw [hstk1, hpost1])
  have hys_len : ys.length = t := by
    have h := hforall.length_eq
    rw [conv_auStream_length] at h
    omega
  set W : List (ℤ × ℤ) := List.ofFn (fun k : Fin t => auPhi p α s t (fun j : Fin s => u.getD (j : ℕ) (0, 0)) k) with hWdef
  have hys_get : ∀ i (h : i < t), ys.getD i .nil = cfxVal (auPhi p α s t (fun j : Fin s => u.getD (j : ℕ) (0, 0)) ⟨i, h⟩) := by
    intro i hi
    have hx1 : i < (auStream p α s t u).length := by rw [conv_auStream_length]; exact hi
    have hylen : i < ys.length := by rw [hys_len]; exact hi
    have hQ := hforall.get hx1 hylen
    have hxs_i : (auStream p α s t u).get ⟨i, hx1⟩ = auChunk p α s t u i := conv_auStream_get p α s t u i hi
    have hq : ys.get ⟨i, hylen⟩ = cfxVal (auPhi p α s t (fun j : Fin s => u.getD (j : ℕ) (0, 0)) ⟨i, hi⟩) :=
      hQ ⟨i, hi⟩ hxs_i
    rw [List.get_eq_getElem, ← List.getD_eq_getElem ys .nil hylen] at hq
    exact hq
  have hys_eq : ys = W.map cfxVal := by
    refine List.ext_getElem ?_ (fun i h1 h2 => ?_)
    · rw [hys_len, List.length_map, hWdef, List.length_ofFn]
    · rw [← List.getD_eq_getElem ys .nil h1, ← List.getD_eq_getElem (W.map cfxVal) (cfxVal (0,0)) h2]
      rw [List.getD_map]
      rw [hWdef, List.getD_eq_getElem _ (0,0) (by rw [List.length_ofFn]; exact (by rw [← hys_len]; exact h1)),
        List.getElem_ofFn]
      exact hys_get i (by rw [← hys_len]; exact h1)
  have hofList : ofList ys = cvecVal W := by
    rw [hys_eq]
    rfl
  have hWlen : W.length = t := by rw [hWdef, List.length_ofFn]
  have hWget : ∀ k : Fin t, W.getD (k : ℕ) (0,0) = auPhi p α s t (fun j : Fin s => u.getD (j : ℕ) (0, 0)) k := by
    intro k
    rw [hWdef, List.getD_eq_getElem _ (0,0) (by rw [List.length_ofFn]; exact k.isLt),
      List.getElem_ofFn]
  have hWdisc : ∀ z ∈ W, inDisc p z := by
    intro z hz
    rw [hWdef] at hz
    obtain ⟨k, hkz⟩ := List.mem_ofFn.mp hz
    rw [← hkz]
    refine auPhiDisc p α s t hs hst hα hp hαp hwt hrow (fun j : Fin s => u.getD (j : ℕ) (0,0)) ?_ k
    intro j
    refine hdisc _ ?_
    rw [List.getD_eq_getElem _ (0,0) (by rw [hulen]; exact j.isLt)]
    exact List.getElem_mem _
  refine ⟨out2, s2, n1 + n2, ⟨u, rest, W, hvs, ?_, ?_, ?_, ?_⟩, Eval.seq hev1 hev2, ?_, ?_, ?_⟩
  · rw [hout2, hofList, List.cons_append]
  · exact hWlen
  · exact hWdisc
  · intro k
    exact hWget k
  · -- cost
    have hp1' : 1 ≤ p := by omega
    have hS : 1 ≤ (Nat.sqrt p + 1) * (α + 1) := by
      have h1 : 1 ≤ Nat.sqrt p + 1 := by omega
      have h2 : 1 ≤ α + 1 := by omega
      nlinarith
    have hLa : auL p α ≤ 2 * ((Nat.sqrt p + 1) * (α + 1)) := by
      rw [auL, auM]; nlinarith
    set X : ℕ := (Nat.sqrt p + 1) * (α + 1) with hXdef
    set B : ℕ := X * (Cm ((64 * (Ks + Kc + Km + 9) ^ 4 + 100) * p) + p + 1) with hBdef
    have hX1 : 1 ≤ X := by rw [hXdef]; exact hS
    have hBp : X * (p + 1) ≤ B := by
      rw [hBdef]
      exact Nat.mul_le_mul_left _ (by omega)
    have hB1 : 1 ≤ B := by
      rw [hBdef]
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have hmem : X * (Cm (Kc * p) + p + 1) ≤ B := by
      rw [hBdef]
      exact Nat.mul_le_mul_left _ (by
        exact Nat.add_le_add_right (Nat.add_le_add_right (hm (Nat.mul_le_mul_right p hKcK)) p) 1)
    have hLa' : auL p α ≤ 2 * X := by rw [hXdef]; exact hLa
    have hL'b : L' + 1 ≤ 55 * (X * (p + 1)) := by
      have hmax : L' ≤ auL p α * (3 * p + 16) + 4 + (4 * p + 8) := by simp only [L']; omega
      have h1 : auL p α * (3 * p + 16) ≤ (2 * X) * (3 * p + 16) := Nat.mul_le_mul_right _ hLa'
      have h2 : (2 * X) * (3 * p + 16) + 4 + (4 * p + 8) + 1 ≤ 55 * (X * (p + 1)) :=
        cost_L' p X hp1' hX1
      omega
    have hc_le : c ≤ 2 * Kc * (X * (Cm (Kc * p) + p + 1)) := by
      have h1 : auL p α + 1 ≤ 2 * X := by
        rw [hXdef, auL, auM]
        nlinarith
      simp only [c]
      calc Kc * (auL p α + 1) * (Cm (Kc * p) + p + 1)
          ≤ Kc * (2 * X) * (Cm (Kc * p) + p + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
        _ = 2 * Kc * (X * (Cm (Kc * p) + p + 1)) := by ring
    have hc' : c ≤ 2 * Kc * B := le_trans hc_le (Nat.mul_le_mul_left _ hmem)
    have hL'B : L' + 1 ≤ 55 * B := by
      calc L' + 1 ≤ 55 * (X * (p + 1)) := hL'b
        _ ≤ 55 * B := Nat.mul_le_mul_left _ hBp
    have hsetB : n1 ≤ 11 * Ks * ((t + 1) * B) := by
      have hOff : auOff p α s < s := conv_auOff_lt p α s (by omega)
      have hCs : auCop p α s * s ≤ 4 * s + 2 * auM p α := by omega
      have hMs : auM p α ≤ 2 * X := by rw [hXdef, auM]; nlinarith [hS]
      have h1 : s + t * auL p α + auCop p α s * s + 1 ≤ 11 * ((t + 1) * X) :=
        conv_cost_set s t (auL p α) (auCop p α s * s) (auM p α) X hX1 hst hMs hCs hLa'
      calc n1 ≤ Ks * ((s + t * auL p α + auCop p α s * s + 1) * (p + 1)) := hn1
        _ ≤ Ks * ((11 * ((t + 1) * X)) * (p + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h1)
        _ = 11 * Ks * ((t + 1) * (X * (p + 1))) := by ring
        _ ≤ 11 * Ks * ((t + 1) * B) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hBp)
    have hmapB : n2 ≤ (t + 1) * (2 * Kc + 55 * Km + 1) * B := by
      have h1 : c + Km * (L' + 1) ≤ (2 * Kc + 55 * Km) * B := by
        have hL'' : Km * (L' + 1) ≤ Km * (55 * B) := Nat.mul_le_mul_left _ hL'B
        nlinarith [hc', hL'', Nat.zero_le Kc, Nat.zero_le Km, hB1]
      have hn2' : n2 ≤ t * (c + Km * (L' + 1)) + Km := by
        rw [conv_auStream_length] at hn2; exact hn2
      have hKmT : t * (c + Km * (L' + 1)) + Km ≤ t * ((2 * Kc + 55 * Km) * B) + (2 * Kc + 55 * Km + 1) * B := by
        nlinarith [Nat.mul_le_mul_left t h1, hB1, Nat.zero_le Km, Nat.zero_le Kc]
      have hfin : t * ((2 * Kc + 55 * Km) * B) + (2 * Kc + 55 * Km + 1) * B
          ≤ (t + 1) * (2 * Kc + 55 * Km + 1) * B := by nlinarith
      exact le_trans hn2' (le_trans hKmT hfin)
    calc n1 + n2 ≤ 11 * Ks * ((t + 1) * B) + (t + 1) * (2 * Kc + 55 * Km + 1) * B := by omega
      _ = (11 * Ks + 2 * Kc + 55 * Km + 1) * ((t + 1) * B) := by ring
      _ ≤ (64 * (Ks + Kc + Km + 9) ^ 4 + 100) * ((t + 1) * B) := Nat.mul_le_mul_right _ hKbig
      _ = (64 * (Ks + Kc + Km + 9) ^ 4 + 100) * (t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm ((64 * (Ks + Kc + Km + 9) ^ 4 + 100) * p) + p + 1) := by
          rw [hBdef, hXdef]; ring
  · rw [hstk2, hout2, hofList]
  · intro k hk
    rw [hoth2 k hk, hoth1 k hk]

end Work.Resample
