import Mathlib
import Submission.Work.Resample.buQWpostDefs
import Submission.Work.Resample.auMapListTail
import Submission.Work.Resample.buZipWithFun
import Submission.Work.Kernel.Raw
import Submission.Work.Resample.buPostShrElem
import Submission.Work.Resample.buPostLinElem

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace Work.Resample

open HvdH

/-! ## helper lemmas -/

/-- division by a power of two does not increase the size of an integer -/
theorem isz_tdiv_le_self {x : ℤ} {k : ℕ} : HvdH.isz (Int.tdiv x ((2 : ℤ) ^ k)) ≤ HvdH.isz x := by
  have h : (Int.tdiv x ((2 : ℤ) ^ k)).natAbs ≤ x.natAbs := by
    rw [Int.natAbs_tdiv]; exact Nat.div_le_self _ _
  have h2 : x.natAbs < 2 ^ x.natAbs.size := (Nat.size_le).mp le_rfl
  have h3 : (Int.tdiv x ((2 : ℤ) ^ k)).natAbs < 2 ^ x.natAbs.size := lt_of_le_of_lt h h2
  have h4 : (Int.tdiv x ((2 : ℤ) ^ k)).natAbs.size ≤ x.natAbs.size := (Nat.size_le).mpr h3
  simp only [HvdH.isz]; omega

/-- multiplication by `±1` does not increase the size of an integer -/
theorem isz_mul_pm_le' {P : ℕ} {x : ℤ} {σ : ℤ} (hx : HvdH.isz x ≤ P)
    (hσ : σ = 1 ∨ σ = -1) : HvdH.isz (σ * x) ≤ P := by
  rcases hσ with rfl | rfl
  · rw [one_mul]; exact hx
  · rw [neg_one_mul]; simpa [HvdH.isz] using hx

/-- reading a `cfxVal`-mapped list at an index inside its range -/
theorem getD_map_cfxVal {u : List (ℤ × ℤ)} {i : ℕ} (hi : i < u.length) :
    (u.map HvdH.cfxVal).getD i Val.nil = HvdH.cfxVal (u.getD i (0, 0)) := by
  rw [List.getD_eq_getElem _ _ (by simpa [List.length_map] using hi), List.getElem_map,
    List.getD_eq_getElem _ _ hi]

/-- the length of a `buTdivV` -/
theorem buPost_tdivV_length (p : ℕ) (z : List (ℤ × ℤ)) : (buTdivV p z).length = z.length := by
  simp [buTdivV]

/-- reading a `buTdivV` at an index inside its range -/
theorem buPost_tdivV_getD : ∀ (p : ℕ) (z : List (ℤ × ℤ)) (i : ℕ), i < z.length →
    (buTdivV p z).getD i (0, 0) = (Int.tdiv (z.getD i (0, 0)).1 ((2 : ℤ) ^ p),
      Int.tdiv (z.getD i (0, 0)).2 ((2 : ℤ) ^ p))
  | p, [], i, h => by simp at h
  | p, _ :: _, 0, _ => rfl
  | p, _ :: as, i + 1, h => by
      simp only [buTdivV, List.map_cons, List.getD_cons_succ, List.length_cons] at h ⊢
      exact buPost_tdivV_getD p as i (by omega)

/-- the length of a `buAddV` -/
theorem buPost_addV_length : ∀ (a b : List (ℤ × ℤ)), (buAddV a b).length = min a.length b.length
  | [], b => by simp [buAddV]
  | _ :: _, [] => by simp [buAddV]
  | _ :: xs, _ :: ys => by
      simp only [buAddV, List.length_cons]
      rw [buPost_addV_length xs ys]
      omega

/-- the `isz` bounds of the entries of a `buAddV` -/
theorem buPost_addV_isz_le {P : ℕ} :
    ∀ {a b : List (ℤ × ℤ)}, (∀ y ∈ a, HvdH.isz y.1 ≤ P ∧ HvdH.isz y.2 ≤ P) →
      (∀ y ∈ b, HvdH.isz y.1 ≤ P ∧ HvdH.isz y.2 ≤ P) →
      ∀ y ∈ buAddV a b, HvdH.isz y.1 ≤ 3 * P + 4 ∧ HvdH.isz y.2 ≤ 3 * P + 4
  | [], b, _, _ => by intro y hy; exact absurd hy (by simp [buAddV])
  | _, [], _, _ => by intro y hy; exact absurd hy (by simp [buAddV])
  | x :: xs, y :: ys, ha, hb => by
      intro z hz
      simp only [buAddV, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact ⟨isz_add_le (ha x (by simp)).1 (hb y (by simp)).1,
               isz_add_le (ha x (by simp)).2 (hb y (by simp)).2⟩
      · exact buPost_addV_isz_le (fun u hu => ha u (List.mem_cons_of_mem _ hu))
          (fun u hu => hb u (List.mem_cons_of_mem _ hu)) z hz

/-- absorption of `2^23 · S · m` by the final constant -/
theorem buPost_absorb' {S m : ℕ} : 2 ^ 23 * S * m ≤ 2 ^ (2 ^ S + 90) * m := by
  have hS2 : S ≤ 2 ^ S := le_of_lt (Nat.lt_two_pow_self (n := S))
  have h1 : 2 ^ 23 * S ≤ 2 ^ 23 * 2 ^ S := Nat.mul_le_mul_left _ hS2
  have h2 : (2 : ℕ) ^ 23 * 2 ^ S = 2 ^ (S + 23) := by rw [← pow_add, Nat.add_comm]
  have h3 : S + 23 ≤ 2 ^ S + 90 := by
    have := Nat.le_of_lt (Nat.lt_two_pow_self (n := S)); omega
  have h4 : (2 : ℕ) ^ (S + 23) ≤ 2 ^ (2 ^ S + 90) := Nat.pow_le_pow_right (by norm_num) h3
  exact Nat.mul_le_mul_right m (le_trans h1 (le_trans (le_of_eq h2) h4))

/-! ## chaining a list of words along a list of windows -/

/-- the program `[p₁, …, pₙ]` sequenced in order -/
def buChainProg (ps : List Cmd) : Cmd := ps.foldr Cmd.seq .skip

theorem buChainProg_cons (p : Cmd) (ps : List Cmd) : buChainProg (p :: ps) = .seq p (buChainProg ps) :=
  rfl

theorem Pipe.buSkip {main : Cmd} {A : List Val} : Pipe main .skip A A 1 := by
  intro rest
  refine Work.Kernel.WordR_conseq (Work.Kernel.WordR_skip main) ?_ ?_ ?_
  · intro vs _; trivial
  · intro vs out hvs ho; rw [ho]; exact hvs
  · intro vs _; exact le_rfl

theorem Pipe.buChain {main : Cmd} (ps : List Cmd) (ws : List (List Val)) (cb : ℕ)
    (hlen : ws.length = ps.length + 1)
    (h : ∀ i, i < ps.length → Pipe main (ps.getD i .skip) (ws.getD i []) (ws.getD (i + 1) []) cb) :
    Pipe main (buChainProg ps) (ws.getD 0 []) (ws.getD ps.length []) (ps.length * cb + 1) := by
  induction ps generalizing ws with
  | nil =>
    have hlen1 : ws.length = 1 := by simpa using hlen
    obtain ⟨w, hw⟩ : ∃ w, ws = [w] := by
      cases ws with
      | nil => simp at hlen1
      | cons a t =>
        cases t with
        | nil => exact ⟨a, rfl⟩
        | cons b t2 => simp at hlen1
    subst hw
    have h1 : buChainProg ([] : List Cmd) = .skip := rfl
    rw [h1]
    simpa using (Pipe.buSkip (main := main) (A := w))
  | cons p ps ih =>
    cases ws with
    | nil => simp at hlen
    | cons w0 ws' =>
      have hlen' : ws'.length = ps.length + 1 := by simpa using hlen
      have hstep : Pipe main p w0 (ws'.getD 0 []) cb := by
        have h0 := h 0 (by simp)
        simpa using h0
      have hrest : ∀ i, i < ps.length →
          Pipe main (ps.getD i .skip) (ws'.getD i []) (ws'.getD (i + 1) []) cb := by
        intro i hi
        have h1 := h (i + 1) (by simp; omega)
        simpa using h1
      have ihh := ih ws' hlen' hrest
      have hcomp : Pipe main (Cmd.seq p (buChainProg ps)) w0 (ws'.getD ps.length [])
          (cb + (ps.length * cb + 1)) := Pipe.comp hstep ihh
      have hcost : cb + (ps.length * cb + 1) ≤ (ps.length + 1) * cb + 1 := by
        ring_nf; omega
      have hres := Pipe.le hcomp hcost
      simp only [buChainProg_cons, List.length_cons, List.getD_cons_zero, List.getD_cons_succ]
      exact hres

theorem buQWpostWord (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (q : HvdH.Cmd) (Kc : ℕ),
    ∀ (p s : ℕ) (main : HvdH.Cmd) (hp : 100 ≤ p)
      (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (z v acc : List (ℤ × ℤ))
      (hz : z.length = s)
      (hzsz : ∀ y ∈ z, HvdH.isz y.1 ≤ 2 * p + 8 ∧ HvdH.isz y.2 ≤ 2 * p + 8)
      (hvlen : v.length = s)
      (hvsz : ∀ y ∈ v, HvdH.isz y.1 ≤ p + 5 ∧ HvdH.isz y.2 ≤ p + 5)
      (haccsz : ∀ y ∈ acc, HvdH.isz y.1 ≤ p + 5 ∧ HvdH.isz y.2 ≤ p + 5)
      (hacc : acc.length = s),
      Work.Resample.Pipe main q
        [HvdH.cvecVal z, HvdH.Val.int σ, HvdH.cvecVal v, HvdH.cvecVal acc,
          HvdH.Val.int (s : ℤ), HvdH.Val.int (p : ℤ)]
        [HvdH.cvecVal (Work.Resample.buTdivV p z),
          HvdH.cvecVal (Work.Resample.buAddV acc
            (Work.Resample.buSMulV σ (Work.Resample.buTdivV p z)))]
        (Kc * (s + 1) * (p + 1)) := by

  obtain ⟨elemShr, KcS, hShr⟩ := buPostShrElem KL IL
  obtain ⟨elemLin, KcL, hLin⟩ := buPostLinElem KL IL
  obtain ⟨rollProg, KR, hroll⟩ := KL.roll
  obtain ⟨dropProg, Kd, hdrop⟩ := KL.drop
  obtain ⟨dupProg, Kdup, hdup⟩ := KL.dup
  obtain ⟨mlComb, Kml, hml⟩ := KL.mapList
  obtain ⟨zwComb, Kz, hzw⟩ := buZipWithFun KL
  let S : ℕ := KcS + KcL + KR + Kd + Kdup + Kml + Kz + 100
  refine ⟨buChainProg [rollProg 5, rollProg 1, mlComb elemShr, dupProg, rollProg 5, rollProg 4,
      rollProg 2, rollProg 2, zwComb elemLin, rollProg 2, rollProg 2, dropProg, rollProg 2,
      dropProg, rollProg 2, dropProg, rollProg 2, dropProg], 2 ^ (2 ^ S + 90), ?_⟩
  intro p s main hp σ hσ z v acc hz hzsz hvlen hvsz haccsz hacc
  -- the fixed window and the two list-level results
  let Z : Val := cvecVal z
  let Z' : Val := cvecVal (buTdivV p z)
  let C : Val := cvecVal acc
  let C' : Val := cvecVal (buAddV acc (buSMulV σ (buTdivV p z)))
  let V : Val := cvecVal v
  let sv : Val := Val.int σ
  let Pv : Val := Val.int (p : ℤ)
  let Sv : Val := Val.int (s : ℤ)
  -- the size parameters
  let Pp : ℕ := 10 * (p + 1)
  let M : ℕ := 32 * (Pp + 1)
  let W : ℕ := (s + 2) * (M + 1)
  let cb : ℕ := 400 * S * W
  have hPp1 : 1 ≤ Pp := by simp only [Pp]; omega
  have hM1 : 1 ≤ M := by simp only [M]; omega
  have hW1 : 1 ≤ W := Nat.mul_pos (by omega) (by omega)
  have h2p8 : 2 * p + 8 ≤ Pp := by simp only [Pp]; omega
  have hsize_le_self : ∀ n : ℕ, n.size ≤ n := fun n => (Nat.size_le).mpr (Nat.lt_two_pow_self (n := n))
  have hpP : HvdH.isz (p : ℤ) ≤ Pp := by
    simp only [HvdH.isz, Int.natAbs_natCast, Pp]
    have := hsize_le_self p; omega
  -- sizes of the window values
  have hZsz : HvdH.vsz Z ≤ W := by
    have h1 : ∀ y ∈ z, HvdH.isz y.1 ≤ Pp ∧ HvdH.isz y.2 ≤ Pp :=
      fun y hy => ⟨le_trans (hzsz y hy).1 h2p8, le_trans (hzsz y hy).2 h2p8⟩
    have h2 := vsz_cvecVal_le' (M := Pp) h1
    have h3 : (s + 1) * (2 * Pp + 2) ≤ W := by
      simp only [W, M]; nlinarith [Nat.zero_le s, Nat.zero_le p]
    refine le_trans ?_ h3
    simpa [Z, hz] using h2
  have hZpsz : HvdH.vsz Z' ≤ W := by
    have h1 : ∀ y ∈ buTdivV p z, HvdH.isz y.1 ≤ Pp ∧ HvdH.isz y.2 ≤ Pp := by
      intro y hy
      rw [buTdivV] at hy
      obtain ⟨c, hc, hcy⟩ := List.mem_map.mp hy
      rw [← hcy]
      exact ⟨le_trans (isz_tdiv_le_self (x := c.1) (k := p)) (le_trans (hzsz c hc).1 h2p8),
        le_trans (isz_tdiv_le_self (x := c.2) (k := p)) (le_trans (hzsz c hc).2 h2p8)⟩
    have h2 := vsz_cvecVal_le' (M := Pp) h1
    have h3 : ((buTdivV p z).length + 1) * (2 * Pp + 2) ≤ W := by
      rw [buPost_tdivV_length, hz]
      simp only [W, M]; nlinarith [Nat.zero_le s, Nat.zero_le p]
    refine le_trans ?_ h3
    simpa [Z'] using h2
  have hCsz : HvdH.vsz C ≤ W := by
    have h1 : ∀ y ∈ acc, HvdH.isz y.1 ≤ Pp ∧ HvdH.isz y.2 ≤ Pp :=
      fun y hy => ⟨le_trans (haccsz y hy).1 (by simp only [Pp]; omega),
        le_trans (haccsz y hy).2 (by simp only [Pp]; omega)⟩
    have h2 := vsz_cvecVal_le' (M := Pp) h1
    have h3 : (s + 1) * (2 * Pp + 2) ≤ W := by
      simp only [W, M]; nlinarith [Nat.zero_le s, Nat.zero_le p]
    refine le_trans ?_ h3
    simpa [C, hacc] using h2
  have hVsz : HvdH.vsz V ≤ W := by
    have h1 : ∀ y ∈ v, HvdH.isz y.1 ≤ Pp ∧ HvdH.isz y.2 ≤ Pp :=
      fun y hy => ⟨le_trans (hvsz y hy).1 (by simp only [Pp]; omega),
        le_trans (hvsz y hy).2 (by simp only [Pp]; omega)⟩
    have h2 := vsz_cvecVal_le' (M := Pp) h1
    have h3 : (s + 1) * (2 * Pp + 2) ≤ W := by
      simp only [W, M]; nlinarith [Nat.zero_le s, Nat.zero_le p]
    refine le_trans ?_ h3
    simpa [V, hvlen] using h2
  have hCpsz : HvdH.vsz C' ≤ W := by
    have hlenC : (buAddV acc (buSMulV σ (buTdivV p z))).length = s := by
      have hb : (buSMulV σ (buTdivV p z)).length = s := by
        simp only [buSMulV, List.length_map, buPost_tdivV_length, hz]
      rw [buPost_addV_length, hacc, hb, Nat.min_self]
    have h1 : ∀ y ∈ buAddV acc (buSMulV σ (buTdivV p z)),
        HvdH.isz y.1 ≤ 3 * Pp + 4 ∧ HvdH.isz y.2 ≤ 3 * Pp + 4 := by
      refine buPost_addV_isz_le (P := Pp) ?_ ?_
      · intro y hy
        exact ⟨le_trans (haccsz y hy).1 (by simp only [Pp]; omega),
          le_trans (haccsz y hy).2 (by simp only [Pp]; omega)⟩
      · intro y hy
        have hy' : y ∈ (buTdivV p z).map (fun z => (σ * z.1, σ * z.2)) := by
          simpa only [buSMulV] using hy
        obtain ⟨c, hc, hcy⟩ := List.mem_map.mp hy'
        rw [← hcy]
        rw [buTdivV] at hc
        obtain ⟨d, hd, hdc⟩ := List.mem_map.mp hc
        rw [← hdc]
        exact ⟨isz_mul_pm_le'
            (le_trans (isz_tdiv_le_self (x := d.1) (k := p)) (le_trans (hzsz d hd).1 h2p8)) hσ,
          isz_mul_pm_le'
            (le_trans (isz_tdiv_le_self (x := d.2) (k := p)) (le_trans (hzsz d hd).2 h2p8)) hσ⟩
    have h2 := vsz_cvecVal_le' (M := 3 * Pp + 4) h1
    have h3 : ((buAddV acc (buSMulV σ (buTdivV p z))).length + 1) * (2 * (3 * Pp + 4) + 2) ≤ W := by
      rw [hlenC]; simp only [W, M]; nlinarith [Nat.zero_le s, Nat.zero_le p]
    refine le_trans ?_ h3
    simpa [C'] using h2
  have hsysz : HvdH.vsz sv ≤ W := by
    have h1 : HvdH.vsz sv = HvdH.isz σ := Work.Fx.vsz_int σ
    rw [h1]
    have h2 : HvdH.isz σ ≤ 3 := isz_pm_one hσ
    simp only [W, M, Pp]
    nlinarith [Nat.zero_le s, Nat.zero_le p]
  have hPvsz : HvdH.vsz Pv ≤ W := by
    have h1 : HvdH.vsz Pv = HvdH.isz (p : ℤ) := Work.Fx.vsz_int (p : ℤ)
    rw [h1]
    have h2 : HvdH.isz (p : ℤ) ≤ Pp := hpP
    have h3 : Pp ≤ W := by simp only [W, M]; nlinarith [Nat.zero_le s, Nat.zero_le p]
    omega
  have hSvsz : HvdH.vsz Sv ≤ W := by
    have h1 : HvdH.vsz Sv = HvdH.isz (s : ℤ) := Work.Fx.vsz_int (s : ℤ)
    rw [h1]
    have h2 : s.size ≤ s := hsize_le_self s
    simp only [HvdH.isz, Int.natAbs_natCast, W, M, Pp]
    nlinarith [Nat.zero_le s, Nat.zero_le p]
  -- uniform cost lemmas
  have hRoll : ∀ (A : List Val) (k : ℕ), k + 1 ≤ 7 → (∀ v ∈ A, HvdH.vsz v ≤ W) →
      KR * (k + 1) * (Work.Fx.szl (A.take (k + 1)) + 1) ≤ cb := by
    intro A k hk hA
    have h1 : Work.Fx.szl (A.take (k + 1)) ≤ 7 * W :=
      le_trans (szlTake_le A (k + 1) W hA) (Nat.mul_le_mul_right W hk)
    have h2 : Work.Fx.szl (A.take (k + 1)) + 1 ≤ 8 * W := by
      have := hW1; omega
    have h3 : KR * (k + 1) * (Work.Fx.szl (A.take (k + 1)) + 1) ≤ KR * 7 * (8 * W) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left KR hk) h2
    have h4 : KR * 7 * (8 * W) = 56 * KR * W := by ring
    have h5 : 56 * KR * W ≤ 400 * S * W := Nat.mul_le_mul_right W (by omega)
    simp only [cb]
    linarith [h3, h4, h5]
  have hDrop : ∀ a : Val, HvdH.vsz a ≤ W → Kd * (HvdH.vsz a + 1) ≤ cb := by
    intro a ha
    have h1 : HvdH.vsz a + 1 ≤ 2 * W := by have := hW1; omega
    have h2 : Kd * (HvdH.vsz a + 1) ≤ Kd * (2 * W) := Nat.mul_le_mul_left _ h1
    have h3 : Kd * (2 * W) = 2 * Kd * W := by ring
    have h4 : 2 * Kd * W ≤ 400 * S * W := Nat.mul_le_mul_right W (by omega)
    simp only [cb]
    linarith [h2, h3, h4]
  have hDup : Kdup * (HvdH.vsz Z' + 1) ≤ cb := by
    have h1 : HvdH.vsz Z' + 1 ≤ 2 * W := by have := hW1; omega
    have h2 : Kdup * (HvdH.vsz Z' + 1) ≤ Kdup * (2 * W) := Nat.mul_le_mul_left _ h1
    have h3 : Kdup * (2 * W) = 2 * Kdup * W := by ring
    have h4 : 2 * Kdup * W ≤ 400 * S * W := Nat.mul_le_mul_right W (by omega)
    simp only [cb]
    linarith [h2, h3, h4]
  -- window membership obligations
  have hm0 : ∀ v ∈ ([Z, sv, V, C, Sv, Pv] : List Val), HvdH.vsz v ≤ W := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hm1 : ∀ v ∈ ([Pv, Z, sv, V, C, Sv] : List Val), HvdH.vsz v ≤ W := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hm4 : ∀ v ∈ ([Z', Z', Pv, sv, V, C, Sv] : List Val), HvdH.vsz v ≤ W := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hm5 : ∀ v ∈ ([C, Z', Z', Pv, sv, V, Sv] : List Val), HvdH.vsz v ≤ W := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hm6 : ∀ v ∈ ([sv, C, Z', Z', Pv, V, Sv] : List Val), HvdH.vsz v ≤ W := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hm7 : ∀ v ∈ ([Z', sv, C, Z', Pv, V, Sv] : List Val), HvdH.vsz v ≤ W := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hm9 : ∀ v ∈ ([C', sv, Z', Pv, V, Sv] : List Val), HvdH.vsz v ≤ W := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hm10 : ∀ v ∈ ([Z', C', sv, Pv, V, Sv] : List Val), HvdH.vsz v ≤ W := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hm12 : ∀ v ∈ ([Z', C', Pv, V, Sv] : List Val), HvdH.vsz v ≤ W := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hm14 : ∀ v ∈ ([Z', C', V, Sv] : List Val), HvdH.vsz v ≤ W := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> assumption
  have hm16 : ∀ v ∈ ([Z', C', Sv] : List Val), HvdH.vsz v ≤ W := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  -- the eighteen steps
  have hstep0 : Pipe main (rollProg 5) [Z, sv, V, C, Sv, Pv] [Pv, Z, sv, V, C, Sv] cb :=
    Pipe.le (Pipe.roll main hroll (A := [Z, sv, V, C, Sv, Pv]) (k := 5) (by simp only [List.length_cons, List.length_nil]; norm_num))
      (hRoll [Z, sv, V, C, Sv, Pv] 5 (by norm_num) hm0)
  have hstep1 : Pipe main (rollProg 1) [Pv, Z, sv, V, C, Sv] [Z, Pv, sv, V, C, Sv] cb :=
    Pipe.le (Pipe.roll main hroll (A := [Pv, Z, sv, V, C, Sv]) (k := 1) (by simp only [List.length_cons, List.length_nil]; norm_num))
      (hRoll [Pv, Z, sv, V, C, Sv] 1 (by norm_num) hm1)
  -- ### step 2: the elementwise division of `z`
  have hxML : ∀ x ∈ z.map HvdH.cfxVal, HvdH.vsz x ≤ M := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    rw [Work.Fx.vsz_cfxVal]
    have h1 := (hzsz a ha).1
    have h2 := (hzsz a ha).2
    simp only [M]; omega
  have hyML : ∀ x ∈ z.map HvdH.cfxVal, HvdH.vsz (buShrF p x) ≤ M := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    rw [buShrF_cfxVal, Work.Fx.vsz_cfxVal]
    have h1 : HvdH.isz (Int.tdiv a.1 ((2 : ℤ) ^ p)) ≤ Pp :=
      le_trans (isz_tdiv_le_self (x := a.1) (k := p)) (le_trans (hzsz a ha).1 h2p8)
    have h2 : HvdH.isz (Int.tdiv a.2 ((2 : ℤ) ^ p)) ≤ Pp :=
      le_trans (isz_tdiv_le_self (x := a.2) (k := p)) (le_trans (hzsz a ha).2 h2p8)
    simp only [M]; omega
  have hElemShr : ∀ x ∈ z.map HvdH.cfxVal,
      Pipe main elemShr (x :: [Pv, sv, V, C, Sv]) (buShrF p x :: [Pv, sv, V, C, Sv])
        (KcS * (Pp + 1)) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    have ha1 : HvdH.isz a.1 ≤ Pp := le_trans (hzsz a ha).1 h2p8
    have ha2 : HvdH.isz a.2 ≤ Pp := le_trans (hzsz a ha).2 h2p8
    refine Pipe.ofWordR2 (A := [HvdH.cfxVal a]) (B := [buShrF p (HvdH.cfxVal a)])
      (T := [Pv, sv, V, C, Sv])
      (Work.Kernel.WordR_conseq (hShr main Pp p a [sv, V, C, Sv] ha1 ha2 hpP)
        (fun vs h => h) (fun vs out _ hq => hq.2) (fun vs _ => le_rfl))
  have hSt2 : Pipe main (mlComb elemShr) (HvdH.ofList (z.map HvdH.cfxVal) :: [Pv, sv, V, C, Sv])
      (HvdH.ofList ((z.map HvdH.cfxVal).map (buShrF p)) :: [Pv, sv, V, C, Sv])
      ((z.map HvdH.cfxVal).length * (KcS * (Pp + 1) + Kml * (M + 1)) + Kml) :=
    auMapListTail hml (T := [Pv, sv, V, C, Sv]) (xs := z.map HvdH.cfxVal) (F := buShrF p)
      (c := KcS * (Pp + 1)) (L := M) hElemShr hxML hyML
  have hSt2b : Pipe main (mlComb elemShr) [Z, Pv, sv, V, C, Sv] [Z', Pv, sv, V, C, Sv]
      ((z.map HvdH.cfxVal).length * (KcS * (Pp + 1) + Kml * (M + 1)) + Kml) :=
    Pipe.rw hSt2 (by rw [buShrF_map p z]; rfl)
  have hSt2c : ((z.map HvdH.cfxVal).length * (KcS * (Pp + 1) + Kml * (M + 1)) + Kml) ≤ cb := by
    have h1 : (z.map HvdH.cfxVal).length = s := by rw [List.length_map, hz]
    have hK : KcS * (Pp + 1) + Kml * (M + 1) ≤ 2 * S * (M + 1) := by
      have h2 : KcS * (Pp + 1) ≤ S * (M + 1) :=
        Nat.mul_le_mul (by omega) (by simp only [M]; omega)
      have h3 : Kml * (M + 1) ≤ S * (M + 1) := Nat.mul_le_mul_right _ (by omega)
      linarith
    have h4 : s * (KcS * (Pp + 1) + Kml * (M + 1)) ≤ s * (2 * S * (M + 1)) :=
      Nat.mul_le_mul_left _ hK
    have h5 : Kml ≤ S * (M + 1) := by
      have h6 : Kml ≤ S := by omega
      have h7 : 1 ≤ M + 1 := by omega
      calc Kml ≤ S := h6
        _ = S * 1 := by ring
        _ ≤ S * (M + 1) := Nat.mul_le_mul_left _ h7
    have h6 : s * (2 * S * (M + 1)) + Kml ≤ (s + 2) * (2 * S * (M + 1)) := by
      have h7 : s * (2 * S * (M + 1)) + S * (M + 1) ≤ (s + 2) * (2 * S * (M + 1)) := by
        nlinarith [Nat.zero_le s, Nat.zero_le S, Nat.zero_le M]
      linarith
    have h8 : (s + 2) * (2 * S * (M + 1)) = 2 * S * W := by simp only [W]; ring
    have h9 : 2 * S * W ≤ 400 * S * W := Nat.mul_le_mul_right W (by omega)
    rw [h1]
    simp only [cb]
    linarith [h4, h6, h8, h9]
  have hstep2 : Pipe main (mlComb elemShr) [Z, Pv, sv, V, C, Sv] [Z', Pv, sv, V, C, Sv] cb :=
    Pipe.le hSt2b hSt2c
  have hstep3 : Pipe main dupProg [Z', Pv, sv, V, C, Sv] [Z', Z', Pv, sv, V, C, Sv] cb :=
    Pipe.le (Pipe.appendTail [Pv, sv, V, C, Sv] (Pipe.dup main hdup Z')) hDup
  have hstep4 : Pipe main (rollProg 5) [Z', Z', Pv, sv, V, C, Sv] [C, Z', Z', Pv, sv, V, Sv] cb :=
    Pipe.le (Pipe.roll main hroll (A := [Z', Z', Pv, sv, V, C, Sv]) (k := 5) (by simp only [List.length_cons, List.length_nil]; norm_num))
      (hRoll [Z', Z', Pv, sv, V, C, Sv] 5 (by norm_num) hm4)
  have hstep5 : Pipe main (rollProg 4) [C, Z', Z', Pv, sv, V, Sv] [sv, C, Z', Z', Pv, V, Sv] cb :=
    Pipe.le (Pipe.roll main hroll (A := [C, Z', Z', Pv, sv, V, Sv]) (k := 4) (by simp only [List.length_cons, List.length_nil]; norm_num))
      (hRoll [C, Z', Z', Pv, sv, V, Sv] 4 (by norm_num) hm5)
  have hstep6 : Pipe main (rollProg 2) [sv, C, Z', Z', Pv, V, Sv] [Z', sv, C, Z', Pv, V, Sv] cb :=
    Pipe.le (Pipe.roll main hroll (A := [sv, C, Z', Z', Pv, V, Sv]) (k := 2) (by simp only [List.length_cons, List.length_nil]; norm_num))
      (hRoll [sv, C, Z', Z', Pv, V, Sv] 2 (by norm_num) hm6)
  have hstep7 : Pipe main (rollProg 2) [Z', sv, C, Z', Pv, V, Sv] [C, Z', sv, Z', Pv, V, Sv] cb :=
    Pipe.le (Pipe.roll main hroll (A := [Z', sv, C, Z', Pv, V, Sv]) (k := 2) (by simp only [List.length_cons, List.length_nil]; norm_num))
      (hRoll [Z', sv, C, Z', Pv, V, Sv] 2 (by norm_num) hm7)
  -- ### step 8: the signed accumulation of the divided vector into `acc`
  let Predn : Val → Val → Prop := fun x y => ∃ a b : ℤ × ℤ, x = HvdH.cfxVal a ∧ y = HvdH.cfxVal b ∧
    HvdH.isz a.1 ≤ Pp ∧ HvdH.isz a.2 ≤ Pp ∧ HvdH.isz b.1 ≤ Pp ∧ HvdH.isz b.2 ≤ Pp
  have hElemLin : ∀ x y, Predn x y →
      HvdH.WordR main elemLin (fun vs => vs = x :: y :: [sv, Z', Pv, V, Sv])
        (fun _ out => out = buLinF σ x y :: [sv, Z', Pv, V, Sv]) (fun _ => KcL * (Pp + 1)) := by
    intro x y hxy
    obtain ⟨a, b, rfl, rfl, ha1, ha2, hb1, hb2⟩ := hxy
    refine Work.Kernel.WordR_conseq (hLin main Pp σ a b [Z', Pv, V, Sv] hσ ha1 ha2 hb1 hb2)
      (fun vs h => h) (fun vs out _ hq => hq.2) (fun vs _ => le_rfl)
  have hFzip : ∀ x y, Predn x y → HvdH.vsz (buLinF σ x y) ≤ M := by
    intro x y hxy
    obtain ⟨a, b, rfl, rfl, ha1, ha2, hb1, hb2⟩ := hxy
    rw [buLinF_cfxVal, Work.Fx.vsz_cfxVal]
    have h1 : HvdH.isz (a.1 + σ * b.1) ≤ 3 * Pp + 4 := isz_add_le ha1 (isz_mul_pm_le' hb1 hσ)
    have h2 : HvdH.isz (a.2 + σ * b.2) ≤ 3 * Pp + 4 := isz_add_le ha2 (isz_mul_pm_le' hb2 hσ)
    simp only [M]; omega
  have hPred : ∀ i < (acc.map HvdH.cfxVal).length,
      Predn ((acc.map HvdH.cfxVal).getD i Val.nil) (((buTdivV p z).map HvdH.cfxVal).getD i Val.nil) := by
    intro i hi
    have hiacc : i < acc.length := by simpa [List.length_map] using hi
    have his : i < s := by rw [← hacc]; exact hiacc
    have hiz : i < z.length := by rw [hz]; exact his
    have hmem : acc.getD i (0, 0) ∈ acc := by
      rw [List.getD_eq_getElem _ _ hiacc]
      exact List.mem_iff_getElem.mpr ⟨i, hiacc, rfl⟩
    have hmemz : z.getD i (0, 0) ∈ z := by
      rw [List.getD_eq_getElem _ _ hiz]
      exact List.mem_iff_getElem.mpr ⟨i, hiz, rfl⟩
    refine ⟨acc.getD i (0, 0), (buTdivV p z).getD i (0, 0), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact getD_map_cfxVal (u := acc) hiacc
    · refine getD_map_cfxVal (u := buTdivV p z) ?_
      rw [buPost_tdivV_length, hz]; exact his
    · exact le_trans (haccsz _ hmem).1 (by simp only [Pp]; omega)
    · exact le_trans (haccsz _ hmem).2 (by simp only [Pp]; omega)
    · rw [buPost_tdivV_getD p z i hiz]
      exact le_trans (isz_tdiv_le_self (x := (z.getD i (0, 0)).1) (k := p))
        (le_trans (hzsz _ hmemz).1 h2p8)
    · rw [buPost_tdivV_getD p z i hiz]
      exact le_trans (isz_tdiv_le_self (x := (z.getD i (0, 0)).2) (k := p))
        (le_trans (hzsz _ hmemz).2 h2p8)
  have hLall : ∀ x ∈ (acc.map HvdH.cfxVal) ++ ((buTdivV p z).map HvdH.cfxVal), HvdH.vsz x ≤ M := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      rw [Work.Fx.vsz_cfxVal]
      have h1 := (haccsz a ha).1
      have h2 := (haccsz a ha).2
      simp only [M]; omega
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      have hb2 : b ∈ z.map (fun a : ℤ × ℤ =>
          (Int.tdiv a.1 ((2 : ℤ) ^ p), Int.tdiv a.2 ((2 : ℤ) ^ p))) := by
        simpa only [buTdivV] using hb
      obtain ⟨c, hc, hcb⟩ := List.mem_map.mp hb2
      rw [← hcb]
      rw [Work.Fx.vsz_cfxVal]
      have h1 : HvdH.isz (Int.tdiv c.1 ((2 : ℤ) ^ p)) ≤ Pp :=
        le_trans (isz_tdiv_le_self (x := c.1) (k := p)) (le_trans (hzsz c hc).1 h2p8)
      have h2 : HvdH.isz (Int.tdiv c.2 ((2 : ℤ) ^ p)) ≤ Pp :=
        le_trans (isz_tdiv_le_self (x := c.2) (k := p)) (le_trans (hzsz c hc).2 h2p8)
      simp only [M]; omega
  have hlen2 : (acc.map HvdH.cfxVal).length = ((buTdivV p z).map HvdH.cfxVal).length := by
    rw [List.length_map, List.length_map, buPost_tdivV_length, hz]; exact hacc
  have hlen2' : acc.length = (buTdivV p z).length := by
    rw [buPost_tdivV_length, hz]; exact hacc
  have hSt8 : HvdH.WordR main (zwComb elemLin)
      (fun vs => vs = HvdH.ofList (acc.map HvdH.cfxVal) :: HvdH.ofList ((buTdivV p z).map HvdH.cfxVal) ::
        [sv, Z', Pv, V, Sv])
      (fun _ out => out = HvdH.ofList (List.zipWith (buLinF σ) (acc.map HvdH.cfxVal)
        ((buTdivV p z).map HvdH.cfxVal)) :: [sv, Z', Pv, V, Sv])
      (fun _ => (acc.map HvdH.cfxVal).length * (KcL * (Pp + 1) + Kz * (M + 1)) + Kz) :=
    hzw main elemLin [sv, Z', Pv, V, Sv] Predn (buLinF σ) (KcL * (Pp + 1)) M hElemLin hFzip
      (acc.map HvdH.cfxVal) ((buTdivV p z).map HvdH.cfxVal) hlen2 hPred hLall
  have hSt8b : Pipe main (zwComb elemLin) [C, Z', sv, Z', Pv, V, Sv]
      [HvdH.ofList (List.zipWith (buLinF σ) (acc.map HvdH.cfxVal) ((buTdivV p z).map HvdH.cfxVal)),
        sv, Z', Pv, V, Sv]
      ((acc.map HvdH.cfxVal).length * (KcL * (Pp + 1) + Kz * (M + 1)) + Kz) :=
    Pipe.ofWordR2 (A := [C, Z']) (T := [sv, Z', Pv, V, Sv])
      (B := [HvdH.ofList (List.zipWith (buLinF σ) (acc.map HvdH.cfxVal)
        ((buTdivV p z).map HvdH.cfxVal))]) hSt8
  have hSt8c : Pipe main (zwComb elemLin) [C, Z', sv, Z', Pv, V, Sv] [C', sv, Z', Pv, V, Sv]
      ((acc.map HvdH.cfxVal).length * (KcL * (Pp + 1) + Kz * (M + 1)) + Kz) :=
    Pipe.rw hSt8b (by rw [buZipAdd_eq σ acc (buTdivV p z) hlen2']; rfl)
  have hSt8d : ((acc.map HvdH.cfxVal).length * (KcL * (Pp + 1) + Kz * (M + 1)) + Kz) ≤ cb := by
    have h1 : (acc.map HvdH.cfxVal).length = s := by rw [List.length_map, hacc]
    have hK : KcL * (Pp + 1) + Kz * (M + 1) ≤ 2 * S * (M + 1) := by
      have h2 : KcL * (Pp + 1) ≤ S * (M + 1) :=
        Nat.mul_le_mul (by omega) (by simp only [M]; omega)
      have h3 : Kz * (M + 1) ≤ S * (M + 1) := Nat.mul_le_mul_right _ (by omega)
      linarith
    have h4 : s * (KcL * (Pp + 1) + Kz * (M + 1)) ≤ s * (2 * S * (M + 1)) :=
      Nat.mul_le_mul_left _ hK
    have h5 : Kz ≤ S * (M + 1) := by
      have h6 : Kz ≤ S := by omega
      have h7 : 1 ≤ M + 1 := by omega
      calc Kz ≤ S := h6
        _ = S * 1 := by ring
        _ ≤ S * (M + 1) := Nat.mul_le_mul_left _ h7
    have h6 : s * (2 * S * (M + 1)) + Kz ≤ (s + 2) * (2 * S * (M + 1)) := by
      have h7 : s * (2 * S * (M + 1)) + S * (M + 1) ≤ (s + 2) * (2 * S * (M + 1)) := by
        nlinarith [Nat.zero_le s, Nat.zero_le S, Nat.zero_le M]
      linarith
    have h8 : (s + 2) * (2 * S * (M + 1)) = 2 * S * W := by simp only [W]; ring
    have h9 : 2 * S * W ≤ 400 * S * W := Nat.mul_le_mul_right W (by omega)
    rw [h1]
    simp only [cb]
    linarith [h4, h6, h8, h9]
  have hstep8 : Pipe main (zwComb elemLin) [C, Z', sv, Z', Pv, V, Sv] [C', sv, Z', Pv, V, Sv] cb :=
    Pipe.le hSt8c hSt8d
  have hstep9 : Pipe main (rollProg 2) [C', sv, Z', Pv, V, Sv] [Z', C', sv, Pv, V, Sv] cb :=
    Pipe.le (Pipe.roll main hroll (A := [C', sv, Z', Pv, V, Sv]) (k := 2) (by simp only [List.length_cons, List.length_nil]; norm_num))
      (hRoll [C', sv, Z', Pv, V, Sv] 2 (by norm_num) hm9)
  have hstep10 : Pipe main (rollProg 2) [Z', C', sv, Pv, V, Sv] [sv, Z', C', Pv, V, Sv] cb :=
    Pipe.le (Pipe.roll main hroll (A := [Z', C', sv, Pv, V, Sv]) (k := 2) (by simp only [List.length_cons, List.length_nil]; norm_num))
      (hRoll [Z', C', sv, Pv, V, Sv] 2 (by norm_num) hm10)
  have hstep11 : Pipe main dropProg [sv, Z', C', Pv, V, Sv] [Z', C', Pv, V, Sv] cb :=
    Pipe.le (Pipe.appendTail [Z', C', Pv, V, Sv] (Pipe.drop main hdrop sv)) (hDrop sv hsysz)
  have hstep12 : Pipe main (rollProg 2) [Z', C', Pv, V, Sv] [Pv, Z', C', V, Sv] cb :=
    Pipe.le (Pipe.roll main hroll (A := [Z', C', Pv, V, Sv]) (k := 2) (by simp only [List.length_cons, List.length_nil]; norm_num))
      (hRoll [Z', C', Pv, V, Sv] 2 (by norm_num) hm12)
  have hstep13 : Pipe main dropProg [Pv, Z', C', V, Sv] [Z', C', V, Sv] cb :=
    Pipe.le (Pipe.appendTail [Z', C', V, Sv] (Pipe.drop main hdrop Pv)) (hDrop Pv hPvsz)
  have hstep14 : Pipe main (rollProg 2) [Z', C', V, Sv] [V, Z', C', Sv] cb :=
    Pipe.le (Pipe.roll main hroll (A := [Z', C', V, Sv]) (k := 2) (by simp only [List.length_cons, List.length_nil]; norm_num))
      (hRoll [Z', C', V, Sv] 2 (by norm_num) hm14)
  have hstep15 : Pipe main dropProg [V, Z', C', Sv] [Z', C', Sv] cb :=
    Pipe.le (Pipe.appendTail [Z', C', Sv] (Pipe.drop main hdrop V)) (hDrop V hVsz)
  have hstep16 : Pipe main (rollProg 2) [Z', C', Sv] [Sv, Z', C'] cb :=
    Pipe.le (Pipe.roll main hroll (A := [Z', C', Sv]) (k := 2) (by simp only [List.length_cons, List.length_nil]; norm_num))
      (hRoll [Z', C', Sv] 2 (by norm_num) hm16)
  have hstep17 : Pipe main dropProg [Sv, Z', C'] [Z', C'] cb :=
    Pipe.le (Pipe.appendTail [Z', C'] (Pipe.drop main hdrop Sv)) (hDrop Sv hSvsz)
  -- assemble the chain
  let ps : List HvdH.Cmd := [rollProg 5, rollProg 1, mlComb elemShr, dupProg, rollProg 5,
    rollProg 4, rollProg 2, rollProg 2, zwComb elemLin, rollProg 2, rollProg 2, dropProg,
    rollProg 2, dropProg, rollProg 2, dropProg, rollProg 2, dropProg]
  let ws : List (List Val) := [[Z, sv, V, C, Sv, Pv], [Pv, Z, sv, V, C, Sv], [Z, Pv, sv, V, C, Sv],
    [Z', Pv, sv, V, C, Sv], [Z', Z', Pv, sv, V, C, Sv], [C, Z', Z', Pv, sv, V, Sv],
    [sv, C, Z', Z', Pv, V, Sv], [Z', sv, C, Z', Pv, V, Sv], [C, Z', sv, Z', Pv, V, Sv],
    [C', sv, Z', Pv, V, Sv], [Z', C', sv, Pv, V, Sv], [sv, Z', C', Pv, V, Sv], [Z', C', Pv, V, Sv],
    [Pv, Z', C', V, Sv], [Z', C', V, Sv], [V, Z', C', Sv], [Z', C', Sv], [Sv, Z', C'], [Z', C']]
  have hlenws : ws.length = ps.length + 1 := rfl
  have hsteps : ∀ i, i < ps.length →
      Pipe main (ps.getD i .skip) (ws.getD i []) (ws.getD (i + 1) []) cb := by
    intro i hi
    have hi18 : i < 18 := by simpa only [ps, List.length_cons, List.length_nil] using hi
    interval_cases i <;>
      (dsimp only [ps, ws] <;>
       simp only [List.getD_cons_zero, List.getD_cons_succ, List.nil_append] <;>
       assumption)
  have hchain := Pipe.buChain ps ws cb hlenws hsteps
  -- the final cost bound
  have hWle : W ≤ 1000 * (s + 1) * (p + 1) := by
    have h1 : M + 1 ≤ 321 * (p + 1) := by
      simp only [M, Pp]; nlinarith [Nat.zero_le p]
    have h2 : s + 2 ≤ 3 * (s + 1) := by omega
    calc W = (s + 2) * (M + 1) := rfl
      _ ≤ (3 * (s + 1)) * (321 * (p + 1)) := Nat.mul_le_mul h2 h1
      _ = 963 * ((s + 1) * (p + 1)) := by ring
      _ ≤ 1000 * (s + 1) * (p + 1) := by
          have h3 : (963 : ℕ) * ((s + 1) * (p + 1)) ≤ 1000 * ((s + 1) * (p + 1)) :=
            Nat.mul_le_mul_right _ (by norm_num)
          calc 963 * ((s + 1) * (p + 1)) ≤ 1000 * ((s + 1) * (p + 1)) := h3
            _ = 1000 * (s + 1) * (p + 1) := by ring
  refine Pipe.le hchain ?_
  have hpslen : ps.length = 18 := rfl
  have hSW : 1 ≤ S * W := Nat.mul_pos (by omega) hW1
  have hA : ps.length * cb + 1 ≤ 7201 * (S * W) := by
    rw [hpslen]
    have h2 : 18 * cb = 7200 * (S * W) := by simp only [cb]; ring
    rw [h2]
    have h3 : 7201 * (S * W) = 7200 * (S * W) + (S * W) := by ring
    rw [h3]
    exact Nat.add_le_add_left hSW _
  have hB : 7201 * (S * W) ≤ 7201 * (S * (1000 * (s + 1) * (p + 1))) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hWle)
  have hC : 7201 * (S * (1000 * (s + 1) * (p + 1))) = 7201000 * (S * ((s + 1) * (p + 1))) := by
    ring
  have hD : 7201000 * (S * ((s + 1) * (p + 1))) ≤ 2 ^ 23 * (S * ((s + 1) * (p + 1))) :=
    Nat.mul_le_mul_right _ (by norm_num)
  have hF := buPost_absorb' (S := S) (m := (s + 1) * (p + 1))
  calc ps.length * cb + 1 ≤ 7201 * (S * W) := hA
    _ ≤ 7201 * (S * (1000 * (s + 1) * (p + 1))) := hB
    _ = 7201000 * (S * ((s + 1) * (p + 1))) := hC
    _ ≤ 2 ^ 23 * (S * ((s + 1) * (p + 1))) := hD
    _ = 2 ^ 23 * S * ((s + 1) * (p + 1)) := by rw [Nat.mul_assoc]
    _ ≤ 2 ^ (2 ^ S + 90) * ((s + 1) * (p + 1)) := hF
    _ = 2 ^ (2 ^ S + 90) * (s + 1) * (p + 1) := by rw [Nat.mul_assoc]

end Work.Resample
