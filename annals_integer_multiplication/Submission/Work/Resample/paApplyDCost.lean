import Mathlib
import Submission.Work.Resample.paDefs
import Submission.Work.Resample.pbRndDefs
import Submission.Work.Resample.pbRoundFacts
import Submission.Work.Resample.pbRAdim

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Work.Resample

open HvdH

/-! ## Elementary helpers for `paApplyD` -/

/-- Every slice of a flat `A × m × B` array of values has length `m`. -/
theorem pa_slices_getD_length (A m B : ℕ) (es : List Val) {s : ℕ} (hs : s < A * B) :
    ((HvdH.slices A m B es).getD s []).length = m := by
  rw [HvdH.slices, List.getD_eq_getElem _ _ (by simpa [HvdH.slices] using hs), List.getElem_map]
  simp

/-- `cfxVal` is injective. -/
theorem pa_cfxVal_inj : Function.Injective HvdH.cfxVal := by
  intro x y h
  simp only [HvdH.cfxVal] at h
  obtain ⟨h1, h2⟩ := HvdH.Val.cons.inj h
  exact Prod.ext (HvdH.Val.int.inj h1) (HvdH.Val.int.inj h2)

/-- `List.map cfxVal` is injective. -/
theorem pa_map_cfxVal_inj {u v : List (ℤ × ℤ)} (h : u.map HvdH.cfxVal = v.map HvdH.cfxVal) :
    u = v :=
  List.map_injective_iff.mpr pa_cfxVal_inj h

/-- A `sliceIn` of an in-disc array is in the disc. -/
theorem pa_sliceIn_disc {p : ℕ} {l : List (ℤ × ℤ)} (h : ∀ z ∈ l, inDisc p z) (m B s j : ℕ) :
    inDisc p (Work.Resample.sliceIn m B l s j) := by
  rw [Work.Resample.sliceIn]
  by_cases hlt : ((s / B * m + j) * B + s % B) < l.length
  · rw [List.getD_eq_getElem _ _ hlt]; exact h _ (List.getElem_mem hlt)
  · rw [List.getD_eq_default l (0, 0) (by omega)]; simp [HvdH.inDisc]

/-- The `σ`-th slice of the `cfxVal`-image of a flat array, as a genuine in-disc slice. -/
theorem pa_slice_spec {p A m B : ℕ} {zs : List (ℤ × ℤ)} (hz : zs.length = A * m * B)
    (hdisc : ∀ z ∈ zs, inDisc p z) {σ : ℕ} (hσ : σ < A * B) :
    (HvdH.slices A m B (zs.map HvdH.cfxVal)).getD σ [] =
        (List.ofFn (fun j : Fin m => Work.Resample.sliceIn m B zs σ (j : ℕ))).map HvdH.cfxVal ∧
      (List.ofFn (fun j : Fin m => Work.Resample.sliceIn m B zs σ (j : ℕ))).length = m ∧
      (∀ z ∈ List.ofFn (fun j : Fin m => Work.Resample.sliceIn m B zs σ (j : ℕ)),
        inDisc p z) := by
  refine ⟨pbRF_slices_getD A m B zs σ hz hσ, by simp, ?_⟩
  intro z hz'
  obtain ⟨j, -, rfl⟩ := List.mem_ofFn.mp hz'
  exact pa_sliceIn_disc hdisc m B σ (j : ℕ)

/-- `(ts.take j).prod` has at most `D * p` bits. -/
theorem pa_size_take_ts_prod_le {p α : ℕ} {ss ts : List ℕ} (h : ResParams p α ss ts) {j : ℕ} :
    (((ts.take j).prod).size) ≤ D * p :=
  le_trans (Nat.size_le_size (pbRnd_prod_take_le ts (pbRnd_one_le_ts p α ss ts h)))
    (pbRnd_size_ts_prod_le p α ss ts h)

/-- `(ss.drop j).prod` has at most `D * p` bits. -/
theorem pa_size_drop_ss_prod_le {p α : ℕ} {ss ts : List ℕ} (h : ResParams p α ss ts) (j : ℕ) :
    (((ss.drop j).prod).size) ≤ D * p :=
  le_trans (Nat.size_le_size (pa_drop_prod_le h j)) (pbRnd_size_drop_prod_le p α ss ts h j)

/-- The size of a product of naturals is at most the sum of the sizes. -/
theorem pa_size_mul (a b : ℕ) : (a * b).size ≤ a.size + b.size :=
  Nat.size_le.mpr (lt_of_lt_of_le
    (Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self a) (Nat.lt_size_self b))
    (le_of_eq (pow_add 2 a.size b.size).symm))

/-- `Fin.val` conversion: `(k : ℕ) ≠ 7` from `k ≠ 7` (for `Stk`). -/
theorem pa_val_ne_seven : ∀ k : Stk, k ≠ (7 : Stk) → (k : ℕ) ≠ 7 := by decide

/-- `ofList` is injective. -/
theorem pa_ofList_inj : Function.Injective (ofList : List Val → Val) := by
  intro l
  induction l with
  | nil =>
    intro l' h
    cases l' with
    | nil => rfl
    | cons v t => exact absurd h (by simp [HvdH.ofList])
  | cons v t ih =>
    intro l' h
    cases l' with
    | nil => exact absurd h.symm (by simp [HvdH.ofList])
    | cons v' t' =>
      have h1 : v = v' ∧ ofList t = ofList t' := HvdH.Val.cons.inj h
      rw [h1.1, ih h1.2]

/-! ## The slice conditions of the `Ã` program -/

/-- Input condition of the slice word of the `Ã` program. -/
abbrev PAs (p : ℕ) (m : ℕ) (sl : List Val) : Prop :=
  ∃ u : List (ℤ × ℤ), sl = u.map HvdH.cfxVal ∧ u.length = m ∧ ∀ z ∈ u, inDisc p z

/-- Output condition of the slice word of the `Ã` program. -/
abbrev PAt (p : ℕ) (m n : ℕ) (Φ : (Fin m → ℤ × ℤ) → (Fin n → ℤ × ℤ)) (sl ol : List Val) : Prop :=
  ∃ u w : List (ℤ × ℤ), sl = u.map HvdH.cfxVal ∧ ol = w.map HvdH.cfxVal ∧ w.length = n ∧
    ∀ k : Fin n, w.getD (k : ℕ) (0, 0) = Φ (fun jj : Fin m => u.getD (jj : ℕ) (0, 0)) k

/-! ## Small arithmetic lemmas (proved in isolation, so that the `omega`/`nlinarith` calls of the
cost estimate never see the surrounding context) -/

theorem pa_le_add4 {a b c d : ℕ} : c ≤ a + b + c + d := by omega

theorem pa_le_add1 {a b c d : ℕ} : a ≤ a + b + c + d := by omega

theorem pa_size_mul_add {a D p : ℕ} (h : a ≤ D * p + p) : a + 2 ≤ (D + 1) * (p + 2) := by
  nlinarith [h]

theorem pa_size_add_one {a D p : ℕ} (h : a ≤ D * p) : a + 1 ≤ (D + 1) * (p + 2) := by
  nlinarith [h]

theorem pa_size_add_one' {a D p : ℕ} (h : a ≤ p) : a + 1 ≤ (D + 1) * (p + 2) := by
  nlinarith [h]

theorem pa_forty_seven {x P : ℕ} (h1 : x ≤ P) (h2 : 1 ≤ P) : 40 * x + 7 ≤ 47 * P :=
  calc 40 * x + 7 = 40 * x + 7 * 1 := by ring
    _ ≤ 40 * P + 7 * P := Nat.add_le_add (Nat.mul_le_mul_left 40 h1) (Nat.mul_le_mul_left 7 h2)
    _ = 47 * P := by ring

theorem pa_two_mul {P : ℕ} (h : 1 ≤ P) : P + 1 ≤ 2 * P := by omega

theorem pa_coef {Kal Kmul Kb Kp Ku Km7 Km6 Km2 : ℕ} :
    1 + 2 * Kal + Kp + 47 + Ku + 32 * Km7 + 32 * Km6 + Kmul + 16 * Km2 ≤
      10000 * (Kal + Kmul + Kb + Kp + Ku + Km7 + Km6 + Km2 + 1) := by omega

/-! ## The cost arithmetic of one axis step -/

/-- Total cost bound of the phases of `paApplyD`, in the order in which they are run
(`LayoutLib.applyAlong`, park, `WordP.clearRgn`, unpark, move stack 7, move stack 6,
`mulNatWord`, store on stack 6).  The constants `Kal, Kp, Ku, Km7, Km6, Km2, Kmul` are those of
the seven library words involved. -/
def paAppCost (Kal Kmul Kb Kp Ku Km7 Km6 Km2 : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ)
    (j : ℕ) (Pj : List Val) (nw : Val) : ℕ :=
  (ts.take j).prod * (ss.drop (j + 1)).prod *
      (Kb * (ts.getD j 0 + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1))
  + Kal * ((ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1) + 1) *
      ((2 * p + 8) + ((ts.take j).prod * (ss.drop (j + 1)).prod *
        (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) *
      (((ts.take j).prod * (ss.drop (j + 1)).prod *
        (ss.getD j 0 + ts.getD j 0 + 1)).size + 1)
  + Kal * (isz ((ts.take j).prod : ℤ) + isz ((ss.getD j 0 : ℕ) : ℤ) +
      isz ((ts.getD j 0 : ℕ) : ℤ) + isz (((ss.drop (j + 1)).prod : ℕ) : ℤ))
  + (Kp * (vsz nw + 1)
      + ((5 * ((Pj.map vsz).sum + 1) + 2)
        + (Ku * (vsz nw + 1)
          + (Km7 * (vsz (Val.int ((ts.getD j 0 : ℕ) : ℤ)) + 1)
            + (Km6 * (vsz (Val.int (((ts.take j).prod : ℕ) : ℤ)) + 1)
              + (Kmul * (((ts.take j).prod).size + 1) * ((ts.getD j 0).size + 1)
                + Km2 * (vsz (Val.int ((((ts.take j).prod) * (ts.getD j 0) : ℕ) : ℤ)) + 1)))))))

/-- The cost bound of the second half of one axis step. -/
theorem paApplyD_cost (Kal Kmul Kb Kp Ku Km7 Km6 Km2 : ℕ) :
    ∃ Kc : ℕ, ∀ (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ) (Pj : List Val) (nw : Val),
      ResParams p α ss ts → j < D →
      vsz nw + 1 ≤ ts.prod * (2 * p + 8) + ts.prod + 2 →
      (Pj.map vsz).sum ≤ 8 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb) →
      paAppCost Kal Kmul Kb Kp Ku Km7 Km6 Km2 Cm p α ss ts j Pj nw ≤
        Kc * PABr Kb Cm p α ss ts j := by
  refine ⟨10000 * (Kal + Kmul + Kb + Kp + Ku + Km7 + Km6 + Km2 + 1), ?_⟩
  intro Cm p α ss ts j Pj nw hRes hj hnw hPj
  obtain ⟨hsslen, htslen, hp100, hα2, hαp, hdim⟩ := hRes
  have hD1 : 1 ≤ D := pbRndD_pos
  have htsz : (ts.getD j 0).size ≤ p := Nat.size_le.mpr (hdim j hj).2.2.1
  have hAsz : (((ts.take j).prod).size) ≤ D * p :=
    pa_size_take_ts_prod_le ⟨hsslen, htslen, hp100, hα2, hαp, hdim⟩
  have hmulsz : ((((ts.take j).prod * (ts.getD j 0) : ℕ)).size) ≤ D * p + p :=
    le_trans (pa_size_mul _ _) (Nat.add_le_add hAsz htsz)
  set P : ℕ := PABr Kb Cm p α ss ts j with hP
  -- each summand of `PABr` dominates the corresponding subterm
  have hP1 : 1 ≤ P := by rw [hP]; unfold PABr; omega
  have b1 : Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb ≤ P := by rw [hP]; unfold PABr; omega
  have b2 : (ts.take j).prod * (ss.drop (j + 1)).prod *
      (Kb * (ts.getD j 0 + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1)) ≤ P := by
    rw [hP]; unfold PABr; omega
  have b3 : ((ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1) + 1) *
      ((2 * p + 8) + ((ts.take j).prod * (ss.drop (j + 1)).prod *
        (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) *
      (((ts.take j).prod * (ss.drop (j + 1)).prod *
        (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) ≤ P := by
    rw [hP]; unfold PABr; omega
  have b4 : isz ((ts.take j).prod : ℤ) + isz ((ss.getD j 0 : ℕ) : ℤ) +
      isz ((ts.getD j 0 : ℕ) : ℤ) + isz (((ss.drop (j + 1)).prod : ℕ) : ℤ) ≤ P := by
    rw [hP]; unfold PABr; omega
  have b5 : ts.prod * (2 * p + 8) + ts.prod + 2 ≤ P := by rw [hP]; unfold PABr; omega
  have b6 : (D + 1) * (p + 2) ≤ P := by rw [hP]; unfold PABr; omega
  have b7 : (D + 1) * (p + 2) * ((D + 1) * (p + 2)) ≤ P := by rw [hP]; unfold PABr; omega
  have hzI : ∀ n : ℕ, isz ((n : ℕ) : ℤ) = n.size + 2 := by
    intro n; simp [isz, Int.natAbs_natCast]
  -- the ten components of `paAppCost`
  have hc1 : (ts.take j).prod * (ss.drop (j + 1)).prod *
      (Kb * (ts.getD j 0 + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1)) ≤ P := b2
  have hc2 : Kal * ((ts.take j).prod * (ss.drop (j + 1)).prod *
      (ss.getD j 0 + ts.getD j 0 + 1) + 1) *
      ((2 * p + 8) + ((ts.take j).prod * (ss.drop (j + 1)).prod *
        (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) *
      (((ts.take j).prod * (ss.drop (j + 1)).prod *
        (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) ≤ Kal * P := by
    have h : Kal * ((ts.take j).prod * (ss.drop (j + 1)).prod *
        (ss.getD j 0 + ts.getD j 0 + 1) + 1) *
        ((2 * p + 8) + ((ts.take j).prod * (ss.drop (j + 1)).prod *
          (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) *
        (((ts.take j).prod * (ss.drop (j + 1)).prod *
          (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) =
      Kal * (((ts.take j).prod * (ss.drop (j + 1)).prod *
        (ss.getD j 0 + ts.getD j 0 + 1) + 1) *
        ((2 * p + 8) + ((ts.take j).prod * (ss.drop (j + 1)).prod *
          (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) *
        (((ts.take j).prod * (ss.drop (j + 1)).prod *
          (ss.getD j 0 + ts.getD j 0 + 1)).size + 1)) := by ring
    rw [h]
    exact Nat.mul_le_mul_left Kal b3
  have hc3 : Kal * (isz ((ts.take j).prod : ℤ) + isz ((ss.getD j 0 : ℕ) : ℤ) +
      isz ((ts.getD j 0 : ℕ) : ℤ) + isz (((ss.drop (j + 1)).prod : ℕ) : ℤ)) ≤ Kal * P :=
    Nat.mul_le_mul_left Kal b4
  have hc4 : Kp * (vsz nw + 1) ≤ Kp * P := Nat.mul_le_mul_left Kp (le_trans hnw b5)
  have hc5 : 5 * ((Pj.map vsz).sum + 1) + 2 ≤ 47 * P := by
    have h1 : (Pj.map vsz).sum ≤ 8 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb) := hPj
    have h2 : 5 * ((Pj.map vsz).sum + 1) + 2 ≤
        5 * (8 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb) + 1) + 2 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 5 (Nat.add_le_add_right h1 1)) 2
    have h3 : 5 * (8 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb) + 1) + 2 =
        40 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb) + 7 := by ring
    have h4 : 40 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb) + 7 ≤ 47 * P := pa_forty_seven b1 hP1
    exact le_trans h2 (le_trans (le_of_eq h3) h4)
  have hc6 : Ku * (vsz nw + 1) ≤ Ku * P := Nat.mul_le_mul_left Ku (le_trans hnw b5)
  have hc7 : Km7 * (vsz (Val.int ((ts.getD j 0 : ℕ) : ℤ)) + 1) ≤ 32 * Km7 * P := by
    have hsz : vsz (Val.int ((ts.getD j 0 : ℕ) : ℤ)) + 1 ≤ 32 * P := by
      rw [Work.ConvR.vsz_int, hzI (ts.getD j 0)]
      have h3 : (ts.getD j 0).size + 2 ≤ P := by
        rw [← hzI (ts.getD j 0)]
        exact le_trans (pa_le_add4 (a := isz ((ts.take j).prod : ℤ))
          (b := isz ((ss.getD j 0 : ℕ) : ℤ)) (c := isz ((ts.getD j 0 : ℕ) : ℤ))
          (d := isz (((ss.drop (j + 1)).prod : ℕ) : ℤ))) b4
      have h4 : (ts.getD j 0).size + 2 + 1 ≤ P + 1 := Nat.add_le_add_right h3 1
      have h5 : P + 1 ≤ 32 * P :=
        le_trans (pa_two_mul hP1) (Nat.mul_le_mul_right P (by norm_num : 2 ≤ 32))
      exact le_trans h4 h5
    calc Km7 * (vsz (Val.int ((ts.getD j 0 : ℕ) : ℤ)) + 1) ≤ Km7 * (32 * P) :=
          Nat.mul_le_mul_left Km7 hsz
      _ = 32 * Km7 * P := by ring
  have hc8 : Km6 * (vsz (Val.int (((ts.take j).prod : ℕ) : ℤ)) + 1) ≤ 32 * Km6 * P := by
    have hsz : vsz (Val.int (((ts.take j).prod : ℕ) : ℤ)) + 1 ≤ 32 * P := by
      rw [Work.ConvR.vsz_int, hzI ((ts.take j).prod)]
      have h3 : ((ts.take j).prod).size + 2 ≤ P := by
        rw [← hzI ((ts.take j).prod)]
        exact le_trans (pa_le_add1 (a := isz ((ts.take j).prod : ℤ))
          (b := isz ((ss.getD j 0 : ℕ) : ℤ)) (c := isz ((ts.getD j 0 : ℕ) : ℤ))
          (d := isz (((ss.drop (j + 1)).prod : ℕ) : ℤ))) b4
      have h4 : ((ts.take j).prod).size + 2 + 1 ≤ P + 1 := Nat.add_le_add_right h3 1
      have h5 : P + 1 ≤ 32 * P :=
        le_trans (pa_two_mul hP1) (Nat.mul_le_mul_right P (by norm_num : 2 ≤ 32))
      exact le_trans h4 h5
    calc Km6 * (vsz (Val.int (((ts.take j).prod : ℕ) : ℤ)) + 1) ≤ Km6 * (32 * P) :=
          Nat.mul_le_mul_left Km6 hsz
      _ = 32 * Km6 * P := by ring
  have hc9 : Kmul * (((ts.take j).prod).size + 1) * ((ts.getD j 0).size + 1) ≤ Kmul * P := by
    have h1 : ((ts.take j).prod).size + 1 ≤ (D + 1) * (p + 2) := pa_size_add_one hAsz
    have h2 : (ts.getD j 0).size + 1 ≤ (D + 1) * (p + 2) := pa_size_add_one' htsz
    have h3 : (((ts.take j).prod).size + 1) * ((ts.getD j 0).size + 1) ≤
        ((D + 1) * (p + 2)) * ((D + 1) * (p + 2)) := Nat.mul_le_mul h1 h2
    have h4 : ((D + 1) * (p + 2)) * ((D + 1) * (p + 2)) ≤ P := by
      calc ((D + 1) * (p + 2)) * ((D + 1) * (p + 2))
          = (D + 1) * (p + 2) * ((D + 1) * (p + 2)) := by ring
        _ ≤ P := b7
    have h5 : (((ts.take j).prod).size + 1) * ((ts.getD j 0).size + 1) ≤ P := le_trans h3 h4
    calc Kmul * (((ts.take j).prod).size + 1) * ((ts.getD j 0).size + 1)
        = Kmul * ((((ts.take j).prod).size + 1) * ((ts.getD j 0).size + 1)) := by ring
      _ ≤ Kmul * P := Nat.mul_le_mul_left Kmul h5
  have hc10 : Km2 * (vsz (Val.int ((((ts.take j).prod) * (ts.getD j 0) : ℕ) : ℤ)) + 1) ≤
      16 * Km2 * P := by
    have hsz : vsz (Val.int ((((ts.take j).prod) * (ts.getD j 0) : ℕ) : ℤ)) + 1 ≤ 16 * P := by
      rw [Work.ConvR.vsz_int, hzI ((ts.take j).prod * (ts.getD j 0))]
      have h3 : (((ts.take j).prod * (ts.getD j 0) : ℕ)).size + 2 ≤ P :=
        le_trans (pa_size_mul_add hmulsz) b6
      have h4 : (((ts.take j).prod * (ts.getD j 0) : ℕ)).size + 2 + 1 ≤ P + 1 :=
        Nat.add_le_add_right h3 1
      have h5 : P + 1 ≤ 16 * P :=
        le_trans (pa_two_mul hP1) (Nat.mul_le_mul_right P (by norm_num : 2 ≤ 16))
      exact le_trans h4 h5
    calc Km2 * (vsz (Val.int ((((ts.take j).prod) * (ts.getD j 0) : ℕ) : ℤ)) + 1) ≤
          Km2 * (16 * P) := Nat.mul_le_mul_left Km2 hsz
      _ = 16 * Km2 * P := by ring
  -- assemble
  have key : paAppCost Kal Kmul Kb Kp Ku Km7 Km6 Km2 Cm p α ss ts j Pj nw ≤
      (P + Kal * P + Kal * P) +
        (Kp * P + (47 * P + (Ku * P + (32 * Km7 * P + (32 * Km6 * P +
          (Kmul * P + 16 * Km2 * P)))))) := by
    unfold paAppCost
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hc1 hc2) hc3)
      (Nat.add_le_add hc4 (Nat.add_le_add hc5 (Nat.add_le_add hc6 (Nat.add_le_add hc7
        (Nat.add_le_add hc8 (Nat.add_le_add hc9 hc10))))))
  have hid : (P + Kal * P + Kal * P) +
        (Kp * P + (47 * P + (Ku * P + (32 * Km7 * P + (32 * Km6 * P +
          (Kmul * P + 16 * Km2 * P)))))) =
      (1 + 2 * Kal + Kp + 47 + Ku + 32 * Km7 + 32 * Km6 + Kmul + 16 * Km2) * P := by
    ring
  rw [hid] at key
  refine le_trans key (Nat.mul_le_mul_right P ?_)
  exact pa_coef

end Work.Resample
