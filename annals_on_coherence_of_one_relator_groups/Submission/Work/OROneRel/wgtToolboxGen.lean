import Mathlib
import Submission.Work.OROneRel.wgtMMDefs
import Submission.Work.OROneRel.letters_closure_iff
import Submission.Work.OROneRel.cohom_mk
import Submission.Work.OROneRel.relatorNorm_wW_lt

/-!
# The weighted Magnus toolbox, generalized

`Work.OROneRel.wgtToolboxGen` collects the combinatorial properties of the *weighted* Magnus
rewriting `wvListAux` / `wWL` / `wW` (definitions in `Submission.Work.OROneRel.wgtMMDefs`) of a
cyclically reduced relator `r` with `t ∈ relatorLetters r`, `c t = 1` and `cohom c r = 1`:

* `wWL` is reduced and cyclically reduced, i.e. `wW` is a cyclically reduced relator of the
  decorated alphabet `wBeta c t r`;
* `wW ≠ 1`, and `wW` generates no Magnus subgroup in either of the two ways: it does not lie in
  `Subgroup.closure (FreeGroup.of '' wTA)` nor in `Subgroup.closure (FreeGroup.of '' wTB)`;
* `relatorNorm (wW) < relatorNorm r`.

Unlike `Work.OROneRel.wgtToolbox` we do *not* assume that `r` is not a proper power, and the argument
nowhere uses it.  The pieces are:

* `wgtGen_wvListAux_isReduced`: the decorated word of a reduced word is reduced.  Consecutive
  entries of the decorated word arise from two non-`t` letters of the input separated only by a run
  of `t`-letters; their decorations can only cancel if the run has weight `0`, which forces the run
  to be empty, in which case the two letters are adjacent in the reduced input word — impossible.
* `wgtGen_wvListAux_isCyclicallyReduced`: the cyclic case, by rewriting the doubling `L ++ L`, using
  additivity of `wvListAux` and `lsig c L = 0`.
* `wgtGen_wWL_isReduced`, `wgtGen_wWL_isCyclicallyReduced`: transfer along the length preserving
  relabelling `WgtBeta t → wBeta c t r` (which is injective on the occurring decorations).
* `wgtGen_wW_ne_one`: `wW = 1` would give `r = wrho (wW) = 1` by the telescoping identity
  `wrho_wW`.
* `wgtGen_wW_notMem_closure_wTA`, `…_wTB`: a letter of maximal (resp. minimal) weight of any
  occurring generator is not shiftable.
* `relatorNorm_wW_lt` (proved in `Submission.Work.OROneRel.relatorNorm_wW_lt`): the norm drop.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ### Additivity of `lsig` and of the weighted rewriting -/

theorem wgtGen_lsig_append (c : α → ℤ) (L₁ L₂ : List (α × Bool)) :
    lsig c (L₁ ++ L₂) = lsig c L₁ + lsig c L₂ := by
  simp only [lsig, List.map_append, List.sum_append]

theorem wgtGen_lsig_cons_true (c : α → ℤ) (a : α) (L : List (α × Bool)) :
    lsig c ((a, true) :: L) = c a + lsig c L := rfl

theorem wgtGen_lsig_cons_false (c : α → ℤ) (a : α) (L : List (α × Bool)) :
    lsig c ((a, false) :: L) = -c a + lsig c L := rfl

theorem wgtGen_wvListAux_append [DecidableEq α] (c : α → ℤ) (t : α) (i : ℤ)
    (L₁ L₂ : List (α × Bool)) :
    wvListAux c t i (L₁ ++ L₂) =
      wvListAux c t i L₁ ++ wvListAux c t (i + lsig c L₁) L₂ := by
  induction L₁ generalizing i with
  | nil => simp [wvListAux, lsig]
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · simp only [List.cons_append, wvListAux]
      rw [ih (i - c a), wgtGen_lsig_cons_false,
        show i + (-c a + lsig c L) = (i - c a) + lsig c L from by ring, List.append_assoc]
    · simp only [List.cons_append, wvListAux]
      rw [ih (i + c a), wgtGen_lsig_cons_true,
        show i + (c a + lsig c L) = (i + c a) + lsig c L from by ring, List.append_assoc]

/-! ### Unfolding lemmas for the weighted rewriting -/

theorem wgtGen_wvListAux_cons_of_ne [DecidableEq α] (c : α → ℤ) (t : α) (i : ℤ) {a : α} (b : Bool)
    (L : List (α × Bool)) (ha : a ≠ t) :
    wvListAux c t i ((a, b) :: L) =
      (((⟨a, ha⟩, if b then i else i - c a), b) ::
        wvListAux c t (i + (if b then c a else -c a)) L) := by
  cases b
  · rw [show wvListAux c t i ((a, false) :: L) =
          (if h : a = t then [] else [(((⟨a, h⟩, i - c a) : WgtBeta t), false)])
            ++ wvListAux c t (i - c a) L from rfl, dif_neg ha]
    simp only [Bool.false_eq_true, if_false, List.singleton_append, Int.sub_eq_add_neg]
  · rw [show wvListAux c t i ((a, true) :: L) =
          (if h : a = t then [] else [(((⟨a, h⟩, i) : WgtBeta t), true)])
            ++ wvListAux c t (i + c a) L from rfl, dif_neg ha]
    simp only [if_true, List.singleton_append]

theorem wgtGen_wvListAux_eq_nil_of_all_t [DecidableEq α] (c : α → ℤ) (t : α) (i : ℤ)
    {L : List (α × Bool)} (h : ∀ p ∈ L, p.1 = t) : wvListAux c t i L = [] := by
  induction L generalizing i with
  | nil => rw [show wvListAux c t i ([] : List (α × Bool)) = [] from rfl]
  | cons q L ih =>
    obtain ⟨a, b⟩ := q
    have ha : a = t := h (a, b) (List.mem_cons_self ..)
    have hL : ∀ p ∈ L, p.1 = t := fun p hp => h p (List.mem_cons_of_mem _ hp)
    cases b
    · rw [show wvListAux c t i ((a, false) :: L) =
            (if h : a = t then [] else [(((⟨a, h⟩, i - c a) : WgtBeta t), false)])
              ++ wvListAux c t (i - c a) L from rfl, dif_pos ha, List.nil_append]
      exact ih (i - c a) hL
    · rw [show wvListAux c t i ((a, true) :: L) =
            (if h : a = t then [] else [(((⟨a, h⟩, i) : WgtBeta t), true)])
              ++ wvListAux c t (i + c a) L from rfl, dif_pos ha, List.nil_append]
      exact ih (i + c a) hL

theorem wgtGen_exists_ne_of_wvListAux_ne_nil [DecidableEq α] (c : α → ℤ) (t : α) (i : ℤ)
    {L : List (α × Bool)} (h : wvListAux c t i L ≠ []) : ∃ p ∈ L, p.1 ≠ t := by
  by_contra hc
  refine h (wgtGen_wvListAux_eq_nil_of_all_t c t i fun p hp => ?_)
  by_contra hpt
  exact hc ⟨p, hp, hpt⟩

theorem wgtGen_exists_split_non_t {t : α} {L : List (α × Bool)} (h : ∃ p ∈ L, p.1 ≠ t) :
    ∃ (P : List (α × Bool)) (q : α × Bool) (M : List (α × Bool)),
      L = P ++ q :: M ∧ (∀ p ∈ P, p.1 = t) ∧ q.1 ≠ t := by
  induction L with
  | nil => obtain ⟨p, hp, _⟩ := h; simp at hp
  | cons x L ih =>
    obtain ⟨p, hp, hpt⟩ := h
    by_cases hx : x.1 = t
    · have hmem : p ∈ L := by
        rcases List.mem_cons.mp hp with heq | hmem
        · rw [heq] at hpt; exact absurd hx hpt
        · exact hmem
      obtain ⟨P, q, M, hLM, hP, hq⟩ := ih ⟨p, hmem, hpt⟩
      refine ⟨x :: P, q, M, ?_, ?_, hq⟩
      · simp [hLM]
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact hx
        · exact hP r hr'
    · exact ⟨[], x, L, by simp, by simp, hx⟩

theorem wgtGen_lsig_singleton (c : α → ℤ) (a : α) (b : Bool) :
    lsig c [(a, b)] = (if b then c a else -c a) := by
  cases b <;> simp [lsig]

/-- The first symbol of the weighted decorated word, computed from a decomposition of the input word
at its first non-`t`-letter. -/
theorem wgtGen_wvListAux_head [DecidableEq α] (c : α → ℤ) (t : α) (i : ℤ)
    (P : List (α × Bool)) (a : α) (b : Bool) (M : List (α × Bool))
    (ha : a ≠ t) (hP : ∀ p ∈ P, p.1 = t) :
    wvListAux c t i (P ++ (a, b) :: M) =
      (((⟨a, ha⟩, if b then i + lsig c P else i + lsig c P - c a), b) ::
        wvListAux c t (i + lsig c (P ++ [(a, b)])) M) := by
  rw [wgtGen_wvListAux_append, wgtGen_wvListAux_eq_nil_of_all_t c t i hP, List.nil_append,
    wgtGen_wvListAux_cons_of_ne c t (i + lsig c P) b M ha]
  have hidx : (i + lsig c P) + (if b then c a else -c a) = i + lsig c (P ++ [(a, b)]) := by
    rw [wgtGen_lsig_append, wgtGen_lsig_singleton]
    ring
  rw [hidx]

/-! ### The weight of a run of `t`-letters -/

private theorem wgtGen_snd_eq_of_isReduced_all_fst_eq {t : α} :
    ∀ (L : List (α × Bool)), FreeGroup.IsReduced L → (∀ p ∈ L, p.1 = t) → L ≠ [] →
      ∃ b : Bool, ∀ p ∈ L, p.2 = b
  | [], _, _, hne => absurd rfl hne
  | [p], _, _, _ => ⟨p.2, fun q hq => by rw [List.mem_singleton] at hq; rw [hq]⟩
  | p :: q :: L', hred, ht, _ => by
      rw [FreeGroup.isReduced_cons_cons] at hred
      obtain ⟨h1, h2⟩ := hred
      have hpq : p.2 = q.2 := h1 (by rw [ht p (by simp), ht q (by simp)])
      obtain ⟨b, hb⟩ := wgtGen_snd_eq_of_isReduced_all_fst_eq (q :: L') h2
        (fun r hr => ht r (List.mem_cons_of_mem p hr)) (by simp)
      refine ⟨b, fun r hr => ?_⟩
      rcases List.mem_cons.mp hr with rfl | hr'
      · rw [hpq, hb q (by simp)]
      · exact hb r hr'

private theorem wgtGen_lsig_eq_sign_mul_length (c : α → ℤ) {t : α} (hct : c t = 1) :
    ∀ (b : Bool) (L : List (α × Bool)), (∀ p ∈ L, p.1 = t) → (∀ p ∈ L, p.2 = b) →
      lsig c L = (if b then (1 : ℤ) else -1) * (L.length : ℤ)
  | _, [], _, _ => by simp [lsig]
  | b, p :: L', ht, hb => by
      have hp1 : p.1 = t := ht p (by simp)
      have hp2 : p.2 = b := hb p (by simp)
      have ih := wgtGen_lsig_eq_sign_mul_length c hct b L'
        (fun r hr => ht r (List.mem_cons_of_mem p hr))
        (fun r hr => hb r (List.mem_cons_of_mem p hr))
      have hstep : lsig c (p :: L') = (if p.2 then c p.1 else -c p.1) + lsig c L' := by
        simp [lsig]
      rw [hstep, ih, hp1, hp2, hct, List.length_cons]
      push_cast
      ring

theorem wgtGen_lsig_ne_zero_of_isReduced_all_t {c : α → ℤ} {t : α} (hct : c t = 1)
    {L : List (α × Bool)} (hred : FreeGroup.IsReduced L) (ht : ∀ p ∈ L, p.1 = t) (hne : L ≠ []) :
    lsig c L ≠ 0 := by
  obtain ⟨b, hb⟩ := wgtGen_snd_eq_of_isReduced_all_fst_eq L hred ht hne
  rw [wgtGen_lsig_eq_sign_mul_length c hct b L ht hb]
  have hlen : (L.length : ℤ) ≠ 0 := by
    have hpos : 0 < L.length := List.length_pos_of_ne_nil hne
    omega
  have hsign : (if b then (1 : ℤ) else -1) ≠ 0 := by cases b <;> norm_num
  exact mul_ne_zero hsign hlen

/-! ### Cyclic reducedness via the doubling of a word -/

theorem wgtGen_cyc_iff_append_self {β : Type*} {L : List (β × Bool)} :
    FreeGroup.IsCyclicallyReduced L ↔ FreeGroup.IsReduced (L ++ L) := by
  simp only [FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced]
  rw [List.isChain_append]
  tauto

theorem wgtGen_isReduced_map_subtype {γ : Type*} {δ : Type*} {f : γ → δ} {g : δ → γ}
    {L : List (γ × Bool)} (hf : ∀ p ∈ L, g (f p.1) = p.1) :
    FreeGroup.IsReduced (L.map (fun p => (f p.1, p.2))) ↔ FreeGroup.IsReduced L := by
  induction L with
  | nil => simp [FreeGroup.IsReduced]
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b t' =>
      have ha : g (f a.1) = a.1 := hf a (by simp)
      have hb : g (f b.1) = b.1 := hf b (by simp)
      have ht : ∀ p ∈ (b :: t'), g (f p.1) = p.1 := fun p hp => hf p (by simp [hp])
      have ih' : FreeGroup.IsReduced ((f b.1, b.2) :: t'.map (fun p => (f p.1, p.2))) ↔
          FreeGroup.IsReduced (b :: t') := by
        simpa only [List.map_cons] using ih ht
      simp only [List.map_cons]
      rw [FreeGroup.isReduced_cons_cons, FreeGroup.isReduced_cons_cons, ih']
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        intro hab
        exact h1 (by rw [hab])
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        intro hfst
        have hfst' : f a.1 = f b.1 := hfst
        exact h1 (by rw [← ha, ← hb, hfst'])

theorem wgtGen_isCyclicallyReduced_map_subtype {γ : Type*} {δ : Type*} {f : γ → δ} {g : δ → γ}
    {L : List (γ × Bool)} (hf : ∀ p ∈ L ++ L, g (f p.1) = p.1) :
    FreeGroup.IsCyclicallyReduced (L.map (fun p => (f p.1, p.2))) ↔
      FreeGroup.IsCyclicallyReduced L := by
  rw [wgtGen_cyc_iff_append_self, wgtGen_cyc_iff_append_self, ← List.map_append]
  exact wgtGen_isReduced_map_subtype (fun p hp => hf p hp)

/-! ### The core: the decorated word of a reduced word is reduced -/

theorem wgtGen_cons_contra [DecidableEq α] {c : α → ℤ} {t : α} (hct : c t = 1)
    {a qq1 : α} {b qq2 : Bool} {P M L' : List (α × Bool)}
    (hP : ∀ p ∈ P, p.1 = t) (hLM : L' = P ++ (qq1, qq2) :: M)
    (hPred : FreeGroup.IsReduced P) (hL : FreeGroup.IsReduced ((a, b) :: L'))
    (haq : a = qq1) (hzero : lsig c P = 0) : b = qq2 := by
  have hPnil : P = [] := by
    by_contra hne
    exact wgtGen_lsig_ne_zero_of_isReduced_all_t hct hPred hP hne hzero
  rw [hPnil, List.nil_append] at hLM
  rw [hLM] at hL
  exact (FreeGroup.isReduced_cons_cons.mp hL).1 haq

theorem wgtGen_wvListAux_isReduced [DecidableEq α] (c : α → ℤ) (t : α) (hct : c t = 1)
    (L : List (α × Bool)) (hL : FreeGroup.IsReduced L) :
    ∀ i : ℤ, FreeGroup.IsReduced (wvListAux c t i L) := by
  induction L with
  | nil =>
    intro i
    rw [show wvListAux c t i ([] : List (α × Bool)) = [] from rfl]
    exact FreeGroup.IsReduced.nil
  | cons q L' ih =>
    obtain ⟨a, b⟩ := q
    intro i
    have hL' : FreeGroup.IsReduced L' := List.IsChain.of_cons hL
    by_cases ha : a = t
    · cases b
      · rw [show wvListAux c t i ((a, false) :: L') =
              (if h : a = t then [] else [(((⟨a, h⟩, i - c a) : WgtBeta t), false)])
                ++ wvListAux c t (i - c a) L' from rfl, dif_pos ha, List.nil_append]
        exact ih hL' (i - c a)
      · rw [show wvListAux c t i ((a, true) :: L') =
              (if h : a = t then [] else [(((⟨a, h⟩, i) : WgtBeta t), true)])
                ++ wvListAux c t (i + c a) L' from rfl, dif_pos ha, List.nil_append]
        exact ih hL' (i + c a)
    · rw [wgtGen_wvListAux_cons_of_ne c t i b L' ha]
      by_cases hD : wvListAux c t (i + (if b then c a else -c a)) L' = []
      · rw [hD]
        exact FreeGroup.IsReduced.singleton
      · obtain ⟨P, qq, M, hLM, hP, hq⟩ :=
          wgtGen_exists_split_non_t (t := t)
            (wgtGen_exists_ne_of_wvListAux_ne_nil c t _ hD)
        obtain ⟨qq1, qq2⟩ := qq
        have hhead := wgtGen_wvListAux_head c t (i + (if b then c a else -c a)) P qq1 qq2 M hq hP
        have ihred : FreeGroup.IsReduced (wvListAux c t (i + (if b then c a else -c a)) L') :=
          ih hL' _
        rw [hLM] at ihred ⊢
        rw [hhead] at ihred ⊢
        have hPred : FreeGroup.IsReduced P := List.IsChain.left_of_append (hLM ▸ hL')
        refine FreeGroup.isReduced_cons_cons.mpr ⟨?_, ihred⟩
        intro h1
        cases b <;> cases qq2
        · rfl
        · have hdec : (i - c a) = (i + -c a) + lsig c P := by
            have := congrArg Prod.snd h1
            simpa using this
          have haq : a = qq1 := by
            have := congrArg Subtype.val (congrArg Prod.fst h1)
            simpa using this
          exact wgtGen_cons_contra hct hP hLM hPred hL haq (by linarith)
        · have hdec : i = (i + c a) + lsig c P - c qq1 := by
            have := congrArg Prod.snd h1
            simpa using this
          have haq : a = qq1 := by
            have := congrArg Subtype.val (congrArg Prod.fst h1)
            simpa using this
          exact wgtGen_cons_contra hct hP hLM hPred hL haq (by rw [haq] at hdec; linarith)
        · rfl

theorem wgtGen_wvListAux_isCyclicallyReduced [DecidableEq α] (c : α → ℤ) (t : α) (hct : c t = 1)
    (L : List (α × Bool)) (hL : FreeGroup.IsCyclicallyReduced L) (h0 : lsig c L = 0) :
    FreeGroup.IsCyclicallyReduced (wvListAux c t 0 L) := by
  rw [wgtGen_cyc_iff_append_self] at hL ⊢
  have h2 : wvListAux c t 0 (L ++ L) = wvListAux c t 0 L ++ wvListAux c t 0 L := by
    rw [wgtGen_wvListAux_append, h0, zero_add]
  rw [← h2]
  exact wgtGen_wvListAux_isReduced c t hct (L ++ L) hL 0

/-! ### Transfer to `wWL` -/

theorem wgtGen_lsig_wordOf_eq_zero [DecidableEq α] (c : α → ℤ) (u : FreeGroup α)
    (hcu : cohom c u = 1) : lsig c (wordOf u) = 0 := by
  have h1 : cohom c (FreeGroup.mk (wordOf u)) = Multiplicative.ofAdd (lsig c (wordOf u)) :=
    cohom_mk c (wordOf u)
  rw [mk_wordOf] at h1
  have h2 : Multiplicative.ofAdd (lsig c (wordOf u)) = (1 : Multiplicative ℤ) := by
    rw [← h1]; exact hcu
  exact Multiplicative.ofAdd.injective (by simpa using h2)

theorem wgtGen_wWL_isReduced [DecidableEq α] (c : α → ℤ) (t : α) (hct : c t = 1) (u : FreeGroup α)
    (hcyc : IsCyclicallyReducedRelator u) : FreeGroup.IsReduced (wWL c t u) := by
  rw [show wWL c t u = (wvListAux c t 0 (wordOf u)).map (fun p => (wBetaOf c t u p.1, p.2))
      from by rw [wWL]]
  refine (wgtGen_isReduced_map_subtype (f := fun p : WgtBeta t => wBetaOf c t u p)
    (g := fun q : wBeta c t u => (q.1 : WgtBeta t))
    (fun p hp => wBetaOf_val c t u (wList_mem_decSet c t u hp))).mpr ?_
  have h1 : FreeGroup.IsCyclicallyReduced (wordOf u) := hcyc
  exact wgtGen_wvListAux_isReduced c t hct (wordOf u) h1.1 0

theorem wgtGen_wWL_isCyclicallyReduced [DecidableEq α] (c : α → ℤ) (t : α) (hct : c t = 1)
    (u : FreeGroup α) (hcyc : IsCyclicallyReducedRelator u) (hcu : cohom c u = 1) :
    FreeGroup.IsCyclicallyReduced (wWL c t u) := by
  rw [show wWL c t u = (wvListAux c t 0 (wordOf u)).map (fun p => (wBetaOf c t u p.1, p.2))
      from by rw [wWL]]
  refine (wgtGen_isCyclicallyReduced_map_subtype (f := fun p : WgtBeta t => wBetaOf c t u p)
    (g := fun q : wBeta c t u => (q.1 : WgtBeta t)) ?_).mpr ?_
  · intro p hp
    exact wBetaOf_val c t u (wList_mem_decSet c t u ((List.mem_append.mp hp).elim id id))
  · have h1 : FreeGroup.IsCyclicallyReduced (wordOf u) := hcyc
    exact wgtGen_wvListAux_isCyclicallyReduced c t hct (wordOf u) h1
      (wgtGen_lsig_wordOf_eq_zero c u hcu)

/-! ### Non-triviality and the associated generating sets -/

theorem wgtGen_wW_ne_one [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α) (hct : c t = 1)
    (hcu : cohom c u = 1) (hu1 : u ≠ 1) : wW c t u ≠ 1 := by
  intro h
  refine hu1 ?_
  rw [← wrho_wW c t u hct hcu]
  simp [h]

theorem wgtGen_wWL_ne_nil [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    (hred : FreeGroup.IsReduced (wWL c t u)) (hne : wW c t u ≠ 1) : wWL c t u ≠ [] := by
  intro hnil
  refine hne ?_
  rw [← FreeGroup.toWord_eq_nil_iff]
  have h1 : FreeGroup.toWord (wW c t u) = wWL c t u := by
    rw [wW, FreeGroup.toWord_mk, hred.reduce_eq]
  rw [h1, hnil]

theorem wgtGen_mem_relatorLetters_wW [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    (hred : FreeGroup.IsReduced (wWL c t u)) (q : wBeta c t u) :
    q ∈ relatorLetters (wW c t u) ↔ ∃ b : Bool, (q, b) ∈ wWL c t u := by
  classical
  simp only [relatorLetters, wW, FreeGroup.toWord_mk, FreeGroup.IsReduced.reduce_eq hred]
  exact Iff.rfl

theorem wgtGen_exists_wDecs_nonempty [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    (h : wWL c t u ≠ []) : ∃ x : {x : α // x ≠ t}, (wDecs c t u x).Nonempty := by
  obtain ⟨qb, hqb⟩ := List.exists_mem_of_ne_nil _ h
  obtain ⟨q, b⟩ := qb
  rw [show wWL c t u = (wvListAux c t 0 (wordOf u)).map (fun p => (wBetaOf c t u p.1, p.2))
      from by rw [wWL]] at hqb
  obtain ⟨p, hp, _⟩ := List.mem_map.mp hqb
  exact ⟨p.1.1, ⟨p.1.2, (mem_wDecs_iff c t u p.1.1 p.1.2).mpr ⟨p.2, hp⟩⟩⟩

theorem wgtGen_exists_wvListAux_wHi [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    {x : {x : α // x ≠ t}} (h : (wDecs c t u x).Nonempty) :
    ∃ b : Bool, ((x, wHi c t u x), b) ∈ wvListAux c t 0 (wordOf u) := by
  rw [wHi, dif_pos h]
  exact (mem_wDecs_iff c t u x _).mp (Finset.max'_mem _ h)

theorem wgtGen_exists_wvListAux_wLo [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    {x : {x : α // x ≠ t}} (h : (wDecs c t u x).Nonempty) :
    ∃ b : Bool, ((x, wLo c t u x), b) ∈ wvListAux c t 0 (wordOf u) := by
  rw [wLo, dif_pos h]
  exact (mem_wDecs_iff c t u x _).mp (Finset.min'_mem _ h)

theorem wgtGen_wW_notMem_closure_wTA [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    (hred : FreeGroup.IsReduced (wWL c t u)) (hne : wW c t u ≠ 1) :
    wW c t u ∉ Subgroup.closure (FreeGroup.of '' wTA c t u) := by
  intro hmem
  have hsub : SupportedOn (wW c t u) (wTA c t u) :=
    (letters_closure_iff (wW c t u) (wTA c t u)).mp hmem
  obtain ⟨x, hxne⟩ :=
    wgtGen_exists_wDecs_nonempty c t u (wgtGen_wWL_ne_nil c t u hred hne)
  obtain ⟨b, hb⟩ := wgtGen_exists_wvListAux_wHi c t u hxne
  set q : wBeta c t u := ⟨(x, wHi c t u x), wHi_mem_decSet c t u x⟩ with hqdef
  have hqmem : q ∈ relatorLetters (wW c t u) := by
    refine (wgtGen_mem_relatorLetters_wW c t u hred q).mpr ⟨b, ?_⟩
    rw [show wWL c t u = (wvListAux c t 0 (wordOf u)).map (fun p => (wBetaOf c t u p.1, p.2))
        from by rw [wWL]]
    refine List.mem_map.mpr ⟨((x, wHi c t u x), b), hb, ?_⟩
    refine Prod.ext ?_ rfl
    exact Subtype.ext (wBetaOf_val c t u (wHi_mem_decSet c t u x))
  have hqnot : q ∉ wTA c t u := by
    intro hq'
    rw [show q = (⟨(x, wHi c t u x), wHi_mem_decSet c t u x⟩ : wBeta c t u) from hqdef] at hq'
    have h2 : wHi c t u x + 1 ≤ wHi c t u x := hq'.2
    omega
  exact hqnot (hsub hqmem)

theorem wgtGen_wW_notMem_closure_wTB [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    (hred : FreeGroup.IsReduced (wWL c t u)) (hne : wW c t u ≠ 1) :
    wW c t u ∉ Subgroup.closure (FreeGroup.of '' wTB c t u) := by
  intro hmem
  have hsub : SupportedOn (wW c t u) (wTB c t u) :=
    (letters_closure_iff (wW c t u) (wTB c t u)).mp hmem
  obtain ⟨x, hxne⟩ :=
    wgtGen_exists_wDecs_nonempty c t u (wgtGen_wWL_ne_nil c t u hred hne)
  obtain ⟨b, hb⟩ := wgtGen_exists_wvListAux_wLo c t u hxne
  set q : wBeta c t u := ⟨(x, wLo c t u x), wLo_mem_decSet c t u x⟩ with hqdef
  have hqmem : q ∈ relatorLetters (wW c t u) := by
    refine (wgtGen_mem_relatorLetters_wW c t u hred q).mpr ⟨b, ?_⟩
    rw [show wWL c t u = (wvListAux c t 0 (wordOf u)).map (fun p => (wBetaOf c t u p.1, p.2))
        from by rw [wWL]]
    refine List.mem_map.mpr ⟨((x, wLo c t u x), b), hb, ?_⟩
    refine Prod.ext ?_ rfl
    exact Subtype.ext (wBetaOf_val c t u (wLo_mem_decSet c t u x))
  have hqnot : q ∉ wTB c t u := by
    intro hq'
    rw [show q = (⟨(x, wLo c t u x), wLo_mem_decSet c t u x⟩ : wBeta c t u) from hqdef] at hq'
    have h2 : wLo c t u x ≤ wLo c t u x - 1 := hq'.1
    omega
  exact hqnot (hsub hqmem)

theorem wgtToolboxGen {α : Type u} [DecidableEq α] (c : α → ℤ) (t : α) (r : FreeGroup α)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r) (hr1 : r ≠ 1)
    (ht : t ∈ Work.OROneRel.relatorLetters r) (hct : c t = 1) (hcu : Work.OROneRel.cohom c r = 1) :
    FreeGroup.IsReduced (Work.OROneRel.wWL c t r) ∧
      FreeGroup.IsCyclicallyReduced (Work.OROneRel.wWL c t r) ∧
      Work.OROneRel.wW c t r ≠ 1 ∧
      (Work.OROneRel.wW c t r ∉ Subgroup.closure (FreeGroup.of '' Work.OROneRel.wTA c t r)) ∧
      (Work.OROneRel.wW c t r ∉ Subgroup.closure (FreeGroup.of '' Work.OROneRel.wTB c t r)) ∧
      Work.OROneRel.relatorNorm (Work.OROneRel.wW c t r) < Work.OROneRel.relatorNorm r := by
  have hwlred : FreeGroup.IsReduced (wWL c t r) := wgtGen_wWL_isReduced c t hct r hcyc
  have hwlcyc : FreeGroup.IsCyclicallyReduced (wWL c t r) :=
    wgtGen_wWL_isCyclicallyReduced c t hct r hcyc hcu
  have hne : wW c t r ≠ 1 := wgtGen_wW_ne_one c t r hct hcu hr1
  refine ⟨hwlred, hwlcyc, hne, ?_, ?_, relatorNorm_wW_lt c t r ht⟩
  · exact wgtGen_wW_notMem_closure_wTA c t r hwlred hne
  · exact wgtGen_wW_notMem_closure_wTB c t r hwlred hne

end Work.OROneRel
