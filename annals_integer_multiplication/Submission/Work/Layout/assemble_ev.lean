import Mathlib
import Submission.Work.Layout.SortDefs
import Submission.Work.Layout.appendDefs
import Submission.Work.Layout.drainValsEv
import Submission.Work.Layout.asmLoopEv

/-!
# `Work.Layout.assemble_ev`

Specification of `Work.Layout.Sk.assemble`: it turns the single run on stack `X`
(`X = runEncB rs ++ J` with `rs.length ≤ 1`) back into the `cons`-chain `ofList rs.flatten` on
stack 0 and strips `X`'s boundary marker, at cost linear in the size of the run.

The two loops it contains are handled by the imported pieces:
`Work.Layout.drainValsEv` (the drain of the run's values onto `Z`) and
`Work.Layout.asmLoopEv` (the `cons`-pushing loop that re-assembles the chain on stack 0).
Everything else (`asmSuffix_ev`, the case split on `rs`, the bookkeeping of the touched stacks and
the cost arithmetic) is proved here.
-/

set_option autoImplicit false

namespace Work.Layout

open Work.Layout.Sk HvdH

/-! ## elementary facts -/

theorem lstEnc_flatten (zs : List Val) :
    lstEnc zs = (zs.map (fun v => Glyph.cons :: v.enc)).flatten ++ [Glyph.nil] := by
  induction zs with
  | nil => rfl
  | cons v zs ih => rw [lstEnc_cons, ih]; simp [List.flatten_cons, List.append_assoc]

theorem asmHeadD_encs_cons {vals : List Val} {C : List Glyph} {d : Glyph} (hne : vals ≠ [])
    (hcons : ∀ v ∈ vals, ∃ a b : Val, v = .cons a b) : (encs vals ++ C).headD d = Glyph.cons := by
  cases vals with
  | nil => exact absurd rfl hne
  | cons v vs =>
      obtain ⟨a, b, rfl⟩ := hcons v (List.mem_cons_self ..)
      exact List.headD_cons

theorem asmBnd_ne_cons : gBnd ≠ Glyph.cons := by decide

/-- peek, in existential form -/
theorem ev_peek_exists {main : Cmd} (k : Stk) (r : Reg) (g : Reg → Glyph) (Y : Stk → List Glyph) :
    ∃ s' n, Ev main (.peek k r) ⟨g, Y⟩ s' n ∧ n ≤ 1 ∧ s'.stk = Y ∧
      s'.reg r = (Y k).headD Glyph.eos ∧ (∀ j : Reg, j ≠ r → s'.reg j = g j) := by
  refine ⟨_, 1, ev_peek' main k r g Y, le_rfl, rfl, ?_, ?_⟩
  · simp
  · intro j hj; simp [Function.update_of_ne hj]

/-- pop, in existential form -/
theorem ev_pop_exists {main : Cmd} (k : Stk) (r : Reg) (g : Reg → Glyph) (Y : Stk → List Glyph) :
    ∃ s' n, Ev main (.pop k r) ⟨g, Y⟩ s' n ∧ n ≤ 1 ∧ s'.stk k = (Y k).tail ∧
      (∀ j : Stk, j ≠ k → s'.stk j = Y j) ∧ s'.reg r = (Y k).headD Glyph.eos ∧
      (∀ j : Reg, j ≠ r → s'.reg j = g j) := by
  refine ⟨_, 1, ev_pop' main k r g Y, le_rfl, ?_, ?_, ?_, ?_⟩
  · simp
  · intro j hj; simp [Function.update_of_ne hj]
  · simp
  · intro j hj; simp [Function.update_of_ne hj]

/-- two pops -/
theorem ev_pop2_exists {main : Cmd} {k : Stk} {r : Reg} {g : Reg → Glyph} {Y : Stk → List Glyph}
    {a b : Glyph} {C : List Glyph} (h : Y k = a :: b :: C) :
    ∃ s' n, Ev main (.seq (.pop k r) (.pop k r)) ⟨g, Y⟩ s' n ∧ n ≤ 2 ∧ s'.stk k = C ∧
      (∀ j : Stk, j ≠ k → s'.stk j = Y j) := by
  obtain ⟨s₁, n₁, hev₁, hn₁, hk₁, hfr₁, -, -⟩ := ev_pop_exists (main := main) k r g Y
  have hk₁' : s₁.stk k = b :: C := by rw [hk₁, h]; rfl
  obtain ⟨s₂, n₂, hev₂, hn₂, hk₂, hfr₂, -, -⟩ := ev_pop_exists (main := main) k r s₁.reg s₁.stk
  have hk₂' : s₂.stk k = C := by rw [hk₂, hk₁']; rfl
  refine ⟨s₂, n₁ + n₂, Ev.seq hev₁ hev₂, by omega, hk₂', ?_⟩
  intro j hj
  rw [hfr₂ j hj, hfr₁ j hj]

/-! ## the suffix of `assemble` after the branch -/

theorem asmSuffix_ev {main : Cmd} {Z t d : Stk}
    (hZ0 : Z ≠ 0) (hZt : Z ≠ t) (hZd : Z ≠ d) (ht0 : t ≠ 0) (hd0 : d ≠ 0) (htd : t ≠ d)
    {g : Reg → Glyph} {X : Stk → List Glyph} {vals : List Val} {A B : List Glyph}
    (hcons : ∀ v ∈ vals, ∃ a b : Val, v = .cons a b)
    (hZ : X Z = encs vals ++ gMark :: B) (h0 : X 0 = A) :
    ∃ s' n, Ev main (.seq (pushConst 0 Glyph.nil)
        (.seq (.peek Z rH) (.seq (.loop rH Glyph.cons (asmBody Z t d)) (.pop Z rJ)))) ⟨g, X⟩ s' n ∧
      n ≤ 4 + 20 * ((vals.map vsz).sum + vals.length + 1) ∧
      s'.stk Z = B ∧ s'.stk 0 = lstEnc vals.reverse ++ A ∧
      s'.stk t = X t ∧ s'.stk d = X d ∧
      (∀ k : Stk, k ≠ Z → k ≠ 0 → k ≠ t → k ≠ d → s'.stk k = X k) := by
  obtain ⟨s₁, n₁, hev₁, hn₁, h1_0, h1_fr, -, -⟩ :=
    pushConst_ev (main := main) (k := 0) (cst := Glyph.nil) (g := g) (X := X)
  obtain ⟨s₂, n₂, hev₂, hn₂, h2_stk, h2_reg, h2_fr⟩ := ev_peek_exists (main := main) Z rH s₁.reg s₁.stk
  have hZ₂ : s₂.stk Z = encs vals ++ gMark :: B := by rw [h2_stk, h1_fr Z hZ0]; exact hZ
  have h0₂ : s₂.stk 0 = Glyph.nil :: A := by rw [h2_stk, h1_0, h0]
  have hrh₂ : s₂.reg rH = (s₂.stk Z).headD Glyph.eos := by rw [h2_reg, h2_stk]
  obtain ⟨s₃, n₃, hev₃, hn₃, h3_Z, h3_0, h3_t, h3_d, h3_fr⟩ :=
    asmLoopEv (main := main) hZ0 hZt hZd ht0 hd0 htd hcons (g := s₂.reg) (X := s₂.stk)
      (vals := vals) (A := Glyph.nil :: A) (B := B) hZ₂ h0₂ hrh₂
  obtain ⟨s₄, n₄, hev₄, hn₄, h4_Z, h4_fr, -, -⟩ := ev_pop_exists (main := main) Z rJ s₃.reg s₃.stk
  have h4_Z' : s₄.stk Z = B := by rw [h4_Z, h3_Z]; rfl
  have h4_0 : s₄.stk 0 = lstEnc vals.reverse ++ A := by
    rw [h4_fr 0 hZ0.symm, h3_0]
    rw [← List.singleton_append, ← List.append_assoc, ← lstEnc_flatten vals.reverse]
  refine ⟨s₄, n₁ + (n₂ + (n₃ + n₄)), Ev.seq hev₁ (Ev.seq hev₂ (Ev.seq hev₃ hev₄)),
    by omega, h4_Z', h4_0, ?_, ?_, ?_⟩
  · rw [h4_fr t hZt.symm, h3_t, h2_stk]; exact h1_fr t ht0
  · rw [h4_fr d hZd.symm, h3_d, h2_stk]; exact h1_fr d hd0
  · intro k hkZ hk0 hkt hkd
    rw [h4_fr k hkZ, h3_fr k hkZ hk0 hkt hkd, h2_stk, h1_fr k hk0]

/-! ## the main theorem -/

/-- `assemble X Z t d` turns the single run held on `X` (where `S X = runEncB rs ++ J` with
`rs.length ≤ 1`) back into the `cons`-chain `ofList rs.flatten` on stack 0, and strips `X`'s boundary
marker.  It drains the run's values onto `Z` (pushing a `gMark` first, so the marker is below them),
then moves them one at a time onto stack 0 pushing a `cons` glyph after each.

The program decides which branch to take by testing whether the top glyph of `X` is `cons`, and
`drainVals` also loops on that test, so we need the hypothesis that every element of the run is a
`cons`-value (in the application each element is `cons (.int k) v`), and that a run is nonempty. -/
theorem assemble_ev {main : Cmd} {X Z t d : Stk}
    (hXZ : X ≠ Z) (hXt : X ≠ t) (hXd : X ≠ d) (hZt : Z ≠ t) (hZd : Z ≠ d) (htd : t ≠ d)
    (hX0 : X ≠ 0) (hZ0 : Z ≠ 0) (ht0 : t ≠ 0) (hd0 : d ≠ 0)
    {g : Reg → Glyph} {S : Stk → List Glyph} {rs : List (List Val)} {J R : List Glyph}
    (hX : S X = runEncB rs ++ J) (hrs : rs.length ≤ 1)
    (hrec : ∀ v ∈ rs.flatten, ∃ (a b : Val), v = .cons a b)
    (hne : ∀ r ∈ rs, r ≠ [])
    (h0 : S 0 = R) :
    ∃ s' n, Ev main (assemble X Z t d) ⟨g, S⟩ s' n ∧
      n ≤ 80 * ((rs.flatten.map vsz).sum + rs.flatten.length + 2) ∧
      s'.stk 0 = (ofList rs.flatten).enc ++ R ∧ s'.stk X = J ∧
      (∀ k : Stk, k ≠ X → k ≠ 0 → s'.stk k = S k) := by
  have hrsplit : rs = [] ∨ ∃ r, rs = [r] := by
    match rs with
    | [] => exact Or.inl rfl
    | [r] => exact Or.inr ⟨r, rfl⟩
    | a :: b :: t => simp at hrs
  rcases hrsplit with hnil | ⟨r, hr⟩
  · subst hnil
    have hSX : S X = gBnd :: J := by rw [hX]; simp [runEncB, runEnc]
    have hhead : (S X).headD Glyph.eos = gBnd := by rw [hSX]; exact List.headD_cons
    obtain ⟨s₁, n₁, hev₁, hn₁, hZ₁, hoth₁, hrg₁, hreg₁⟩ :=
      pushConst_ev (main := main) (k := Z) (cst := gMark) (g := g) (X := S)
    obtain ⟨s₂, n₂, hev₂, hn₂, h2stk, h2reg, h2oth⟩ :=
      ev_peek_exists (main := main) X rH s₁.reg s₁.stk
    have h2reg' : s₂.reg rH = gBnd := by rw [h2reg, hoth₁ X hXZ, hSX]; exact List.headD_cons
    have h2ne : s₂.reg rH ≠ Glyph.cons := by rw [h2reg']; exact asmBnd_ne_cons
    obtain ⟨s₃, n₃, hev₃, hn₃, h3X, h3oth, h3reg, h3regoth⟩ :=
      ev_pop_exists (main := main) X rJ s₂.reg s₂.stk
    have h3X' : s₃.stk X = J := by rw [h3X, h2stk, hoth₁ X hXZ, hSX]; rfl
    have hite : Ev main (.ite rH Glyph.cons
        (.seq (drainVals X Z t d) (.seq (.pop X rJ) (.pop X rJ))) (.pop X rJ)) s₂ s₃ (n₃ + 1) :=
      Ev.iteF h2ne hev₃
    have hZ₃ : s₃.stk Z = encs ([] : List Val) ++ gMark :: S Z := by
      rw [h3oth Z hXZ.symm, h2stk, hZ₁]
      simp [HvdH.encs]
    have h0₃ : s₃.stk 0 = R := by
      rw [h3oth 0 (Ne.symm hX0), h2stk, hoth₁ 0 (Ne.symm hZ0), h0]
    obtain ⟨s₄, n₄, hev₄, hn₄, h4Z, h40, h4t, h4d, h4fr⟩ :=
      asmSuffix_ev (main := main) hZ0 hZt hZd ht0 hd0 htd (g := s₃.reg) (X := s₃.stk)
        (vals := ([] : List Val)) (A := R) (B := S Z)
        (by intro v hv; exact absurd hv (by simp)) hZ₃ h0₃
    refine ⟨s₄, n₁ + (n₂ + (n₃ + 1 + n₄)), Ev.seq hev₁ (Ev.seq hev₂ (Ev.seq hite hev₄)),
      ?_, ?_, ?_, ?_⟩
    · have hn₄' : n₄ ≤ 24 := by have h := hn₄; simp at h; omega
      change n₁ + (n₂ + (n₃ + 1 + n₄)) ≤ 160
      omega
    · simpa [ofList, lstEnc, Val.enc] using h40
    · exact (h4fr X hXZ hX0 hXt hXd).trans h3X'
    · intro k hkX hk0
      by_cases hkZ : k = Z
      · rw [hkZ]; exact h4Z
      by_cases hkt : k = t
      · rw [hkt, h4t, h3oth t (Ne.symm hXt), h2stk, hoth₁ t (Ne.symm hZt)]
      by_cases hkd : k = d
      · rw [hkd, h4d, h3oth d (Ne.symm hXd), h2stk, hoth₁ d (Ne.symm hZd)]
      · rw [h4fr k hkZ hk0 hkt hkd, h3oth k hkX, h2stk, hoth₁ k hkZ]
  · subst hr
    have hflat : ([r] : List (List Val)).flatten = r := by simp
    have hconsr : ∀ v ∈ r, ∃ a b : Val, v = .cons a b := fun v hv => hrec v (by simpa using hv)
    have hrne : r ≠ [] := hne r (by simp)
    have hSX : S X = encs r ++ gMark :: gBnd :: J := by
      rw [hX]; simp [runEncB, runEnc, List.append_assoc]
    obtain ⟨s₁, n₁, hev₁, hn₁, hZ₁, hoth₁, hrg₁, hreg₁⟩ :=
      pushConst_ev (main := main) (k := Z) (cst := gMark) (g := g) (X := S)
    obtain ⟨s₂, n₂, hev₂, hn₂, h2stk, h2reg, h2oth⟩ :=
      ev_peek_exists (main := main) X rH s₁.reg s₁.stk
    have h2reg' : s₂.reg rH = Glyph.cons := by
      rw [h2reg, hoth₁ X hXZ, hSX]; exact asmHeadD_encs_cons hrne hconsr
    obtain ⟨s₃, n₃, hev₃, hn₃, h3X, h3Z, h3t, h3d, h3fr⟩ :=
      drainValsEv (main := main) hXZ hXt hXd hZt hZd htd hconsr (g := s₂.reg) (X := s₂.stk)
        (vals := r) (A := gBnd :: J) (B := gMark :: S Z)
        (by rw [h2stk, hoth₁ X hXZ]; exact hSX) (by rw [h2stk]; exact hZ₁)
    obtain ⟨s₄, n₄, hev₄, hn₄, h4X, h4fr⟩ :=
      ev_pop2_exists (main := main) (g := s₃.reg) (Y := s₃.stk) h3X
    have hthen : Ev main (.seq (drainVals X Z t d) (.seq (.pop X rJ) (.pop X rJ))) s₂ s₄ (n₃ + n₄) :=
      Ev.seq hev₃ hev₄
    have hite : Ev main (.ite rH Glyph.cons
        (.seq (drainVals X Z t d) (.seq (.pop X rJ) (.pop X rJ))) (.pop X rJ)) s₂ s₄ (n₃ + n₄ + 1) :=
      Ev.iteT h2reg' hthen
    have hZ₄ : s₄.stk Z = encs r.reverse ++ gMark :: S Z := by rw [h4fr Z hXZ.symm]; exact h3Z
    have h0₄ : s₄.stk 0 = R := by
      rw [h4fr 0 (Ne.symm hX0), h3fr 0 (Ne.symm hX0) (Ne.symm hZ0) (Ne.symm ht0) (Ne.symm hd0),
        h2stk, hoth₁ 0 (Ne.symm hZ0), h0]
    have hconsrev : ∀ v ∈ r.reverse, ∃ a b : Val, v = .cons a b :=
      fun v hv => hconsr v (List.mem_reverse.mp hv)
    obtain ⟨s₅, n₅, hev₅, hn₅, h5Z, h50, h5t, h5d, h5fr⟩ :=
      asmSuffix_ev (main := main) hZ0 hZt hZd ht0 hd0 htd (g := s₄.reg) (X := s₄.stk)
        (vals := r.reverse) (A := R) (B := S Z) hconsrev hZ₄ h0₄
    refine ⟨s₅, n₁ + (n₂ + (n₃ + n₄ + 1 + n₅)), Ev.seq hev₁ (Ev.seq hev₂ (Ev.seq hite hev₅)),
      ?_, ?_, ?_, ?_⟩
    · rw [hflat] at *
      rw [List.map_reverse, List.sum_reverse, List.length_reverse] at hn₅
      omega
    · rw [h50, List.reverse_reverse, ofList_enc]
      simp [hflat]
    · exact (h5fr X hXZ hX0 hXt hXd).trans h4X
    · intro k hkX hk0
      by_cases hkZ : k = Z
      · rw [hkZ]; exact h5Z
      by_cases hkt : k = t
      · rw [hkt, h5t, h4fr t (Ne.symm hXt), h3t, h2stk, hoth₁ t (Ne.symm hZt)]
      by_cases hkd : k = d
      · rw [hkd, h5d, h4fr d (Ne.symm hXd), h3d, h2stk, hoth₁ d (Ne.symm hZd)]
      · rw [h5fr k hkZ hk0 hkt hkd, h4fr k hkX, h3fr k hkX hkZ hkt hkd, h2stk, hoth₁ k hkZ]


end Work.Layout
