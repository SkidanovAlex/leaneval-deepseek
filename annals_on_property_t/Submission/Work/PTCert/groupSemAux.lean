import Submission.Work.PTCert.Checks.SharedAll
import Submission.Work.PTCert.eAux
import Submission.Work.PTCert.nSem
import Submission.Work.PTCert.codeFactsAux.actLBound

/-!
# PTCert — generic auxiliary lemmas for `Work.PTCert.groupSem`

Boolean/list soundness lemmas for the kernel checks (`allL`, `allR`, `allIdx`, `eqL`, `strictInc`,
`memGroupsOK`, `memIdxOK`, `closOK`, `grepOK`) and the position-indexed representation of the
per-row group data (`GroupChunk`, `GroupsAt`).
-/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace Work.PTCert.GSAux

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.C

/-! ## Generic boolean / list lemmas -/

lemma allL_eq_true {l : List ℕ} {p : ℕ → Bool} : allL l p = true ↔ ∀ a ∈ l, p a = true := by
  induction l with
  | nil => simp [allL]
  | cons a t ih =>
    rw [show allL (a::t) p = (p a && allL t p) from rfl, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, hrest⟩ b hb
      rw [List.mem_cons] at hb
      rcases hb with hba | hb
      · rwa [hba]
      · exact hrest b hb
    · intro h
      exact ⟨h a (by simp), fun b hb => h b (by simp [hb])⟩

lemma allR_eq_true {n : ℕ} {p : ℕ → Bool} : allR n p = true ↔ ∀ k < n, p k = true := by
  induction n with
  | zero => simp [allR]
  | succ n ih =>
    rw [show allR (n+1) p = (p n && allR n p) from rfl, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, hrest⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · exact hrest k hk
      · rwa [hk]
    · intro h
      exact ⟨h n (by omega), fun k hk => h k (by omega)⟩

lemma allIdx_eq_true {l : List ℕ} {p : ℕ → ℕ → Bool} {i0 : ℕ} :
    allIdx l p i0 = true ↔ ∀ j < l.length, p (i0 + j) (l.getD j 0) = true := by
  induction l generalizing i0 with
  | nil => simp [allIdx]
  | cons a t ih =>
    rw [show allIdx (a :: t) p i0 = (p i0 a && allIdx t p (i0 + 1)) from rfl]
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, hrest⟩ j hj
      rcases j with _ | j
      · simpa using h0
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest j (by simpa using hj)
    · intro h
      refine ⟨h 0 (by simp), fun j hj => ?_⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (j+1) (by simp; omega)

lemma allL_append_eAux (l m : List ℕ) (p : ℕ → Bool) :
    allL (l ++ m) p = (allL l p && allL m p) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have h1 : allL ((a :: t) ++ m) p = (p a && allL (t ++ m) p) := rfl
    have h2 : allL (a :: t) p = (p a && allL t p) := rfl
    rw [h1, ih, h2]
    simp [Bool.and_assoc]

lemma eqL_eq {l m : List ℕ} : eqL l m = true ↔ l = m := by
  induction l generalizing m with
  | nil => cases m <;> simp [eqL]
  | cons a l' ih =>
    cases m with
    | nil => simp [eqL]
    | cons b m' =>
      rw [show eqL (a::l') (b::m') = (Nat.beq a b && eqL l' m') from rfl]
      rw [Bool.and_eq_true, ih, Nat.beq_eq]
      constructor
      · rintro ⟨hab, hlm⟩; rw [hab, hlm]
      · intro h; injection h with hab hlm; exact ⟨hab, hlm⟩

def strictIncAux (l : List ℕ) (prev : ℕ) : Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun a _ ih p => Nat.ble p a && ih (a + 1)) l prev

lemma strictIncAux_nodup : ∀ (l : List ℕ) (prev : ℕ),
    strictIncAux l prev = true → l.Nodup ∧ ∀ b ∈ l, prev ≤ b := by
  intro l
  induction l with
  | nil => intro prev _; exact ⟨List.nodup_nil, by simp⟩
  | cons a t ih =>
    intro prev h
    rw [show strictIncAux (a :: t) prev = (Nat.ble prev a && strictIncAux t (a + 1)) from rfl,
        Bool.and_eq_true] at h
    obtain ⟨hpa, ht⟩ := h
    have hpale : prev ≤ a := by rw [← Nat.ble_eq]; exact hpa
    obtain ⟨htnodup, htbound⟩ := ih (a+1) ht
    refine ⟨?_, ?_⟩
    · rw [List.nodup_cons]
      refine ⟨?_, htnodup⟩
      intro hmem
      have := htbound a hmem
      omega
    · intro b hb
      rw [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact hpale
      · have := htbound b hb; omega

lemma strictInc_nodup {l : List ℕ} (h : strictInc l = true) : l.Nodup :=
  (strictIncAux_nodup l 0 h).1

/-! ## Soundness of the per-row kernel checks -/

lemma grepOK_sound {eM labT grepT : NT} {ng : ℕ} (h : grepOK eM labT grepT ng = true) :
    ∀ g < ng, cG grepT g < 10368 ∧ eG eM (cG grepT g) ≠ 0 ∧ lG labT (cG grepT g) = g := by
  intro g hg
  have h1 := (allR_eq_true.mp h) g hg
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Bool.not_eq_true'] at h1
  obtain ⟨⟨hlt, hne⟩, hlab⟩ := h1
  refine ⟨hlt, ?_, hlab⟩
  intro h0; rw [h0] at hne; simp at hne

lemma closOK_sound {cm labT stabT grepT : NT} {ss gs : List ℕ}
    (h : closOK cm labT stabT grepT ss gs = true) :
    ∀ g ∈ gs, ∀ s ∈ ss, lG labT (actC cm (stabT.get s) (cG grepT g)) = g := by
  intro g hg s hs
  have h2 := (allL_eq_true.mp ((allL_eq_true.mp h) g hg)) s hs
  rw [Nat.beq_eq] at h2
  exact h2

lemma memIdxOK_sound : ∀ (gl : List (List ℕ)) (ns : ℕ),
    memIdxOK gl ns = true → ∀ l ∈ gl, ∀ v ∈ l, v % 4096 < ns := by
  intro gl
  induction gl with
  | nil => intro ns h l hl; simp at hl
  | cons l t ih =>
    intro ns h l' hl'
    rw [show memIdxOK (l :: t) ns = (allL l (fun v => Nat.blt (v % 4096) ns) && memIdxOK t ns) from rfl,
        Bool.and_eq_true] at h
    rw [List.mem_cons] at hl'
    rcases hl' with rfl | hl'
    · intro v hv
      have hh := (allL_eq_true.mp h.1) v hv
      rwa [Nat.blt_eq] at hh
    · exact ih ns h.2 l' hl'

/-! ## Groups of a row -/

/-- One group (a list of member entries `4096 z + s`) with global index `g`. -/
def GroupChunk (cm eM labT stabT grepT : NT) (g : ℕ) (l : List ℕ) : Prop :=
  strictInc (l.map (fun v => v / 4096)) ∧
  ∀ v ∈ l, eG eM (v / 4096) ≠ 0 ∧ lG labT (v / 4096) = g ∧
    actC cm (stabT.get (v % 4096)) (cG grepT g) = v / 4096

/-- A list `G` of consecutive groups, starting at global index `g0`. -/
def GroupsAt (cm eM labT stabT grepT : NT) (G : List (List ℕ)) (g0 : ℕ) : Prop :=
  ∀ i < G.length, GroupChunk cm eM labT stabT grepT (g0 + i) (G.getD i [])

/-- The recursion part of `memGroupsOK`, separated out. -/
def groupsBool (cm eM labT stabT grepT : NT) (gl : List (List ℕ)) (g : ℕ) : Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun l _ ih g =>
      strictInc (l.map (fun v => v / 4096)) &&
      allL l (fun v => !(Nat.beq (eG eM (v / 4096)) 0) && Nat.beq (lG labT (v / 4096)) g &&
        Nat.beq (actC cm (stabT.get (v % 4096)) (cG grepT g)) (v / 4096)) && ih (g + 1)) gl g

lemma groupsBool_cons (cm eM labT stabT grepT : NT) (l : List ℕ) (t : List (List ℕ)) (g : ℕ) :
    groupsBool cm eM labT stabT grepT (l :: t) g
      = (strictInc (l.map (fun v => v / 4096)) &&
         allL l (fun v => !(Nat.beq (eG eM (v / 4096)) 0) && Nat.beq (lG labT (v / 4096)) g &&
            Nat.beq (actC cm (stabT.get (v % 4096)) (cG grepT g)) (v / 4096)) &&
         groupsBool cm eM labT stabT grepT t (g + 1)) := rfl

lemma groupsBool_sound {cm eM labT stabT grepT : NT} :
    ∀ (gl : List (List ℕ)) (g : ℕ), groupsBool cm eM labT stabT grepT gl g = true →
      GroupsAt cm eM labT stabT grepT gl g := by
  intro gl
  induction gl with
  | nil => intro g h i hi; simp at hi
  | cons l t ih =>
    intro g h i hi
    rw [groupsBool_cons, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨hstrict, hall⟩, ht⟩ := h
    rcases i with _ | i
    · simp only [Nat.add_zero]
      show GroupChunk cm eM labT stabT grepT g l
      refine ⟨hstrict, ?_⟩
      intro v hv
      have hv' := (allL_eq_true.mp hall) v hv
      rw [Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hv'
      obtain ⟨⟨hne, hlab⟩, hact⟩ := hv'
      refine ⟨?_, hlab, ?_⟩
      · intro h0; rw [h0] at hne; simp at hne
      · rw [Nat.beq_eq] at hact; exact hact
    · have hlt : i < t.length := by simp [List.length_cons] at hi; omega
      have hres := ih (g+1) ht i hlt
      have he : g + (i+1) = (g+1) + i := by omega
      rw [he]
      exact hres

lemma memGroupsOK_sound {cm eM labT stabT grepT : NT} {gl : List (List ℕ)} {sizes : List ℕ} {g0 : ℕ}
    (h : memGroupsOK cm eM labT stabT grepT gl sizes g0 = true) :
    gl.map List.length = sizes ∧ GroupsAt cm eM labT stabT grepT gl g0 := by
  rw [show memGroupsOK cm eM labT stabT grepT gl sizes g0
      = (eqL (gl.map List.length) sizes && groupsBool cm eM labT stabT grepT gl g0) from rfl,
      Bool.and_eq_true] at h
  exact ⟨eqL_eq.mp h.1, groupsBool_sound gl g0 h.2⟩

lemma GroupsAt_append {cm eM labT stabT grepT : NT} {A B : List (List ℕ)} {g0 : ℕ}
    (hA : GroupsAt cm eM labT stabT grepT A g0)
    (hB : GroupsAt cm eM labT stabT grepT B (g0 + A.length)) :
    GroupsAt cm eM labT stabT grepT (A ++ B) g0 := by
  intro i hi
  rcases Nat.lt_or_ge i A.length with hiA | hiA
  · rw [List.getD_append A B [] i hiA]
    exact hA i hiA
  · have hik : i - A.length < B.length := by rw [List.length_append] at hi; omega
    rw [List.getD_append_right A B [] i hiA]
    have hh := hB (i - A.length) hik
    rw [show g0 + i = (g0 + A.length) + (i - A.length) from by omega]
    exact hh

lemma mem_flatten_exists_getD {G : List (List ℕ)} {v : ℕ} (hv : v ∈ G.flatten) :
    ∃ i < G.length, v ∈ G.getD i [] := by
  induction G with
  | nil => simp at hv
  | cons l t ih =>
    rw [List.flatten_cons, List.mem_append] at hv
    rcases hv with hv | hv
    · exact ⟨0, by simp, by simpa using hv⟩
    · obtain ⟨i, hi, hvi⟩ := ih hv
      exact ⟨i+1, by simp [List.length_cons]; omega, by simpa using hvi⟩

lemma GroupsAt_nodup {cm eM labT stabT grepT : NT} :
    ∀ (G : List (List ℕ)) (g0 : ℕ), GroupsAt cm eM labT stabT grepT G g0 →
      (G.flatten.map (fun v => v / 4096)).Nodup := by
  intro G
  induction G with
  | nil => intro g0 h; simp
  | cons l t ih =>
    intro g0 h
    rw [List.flatten_cons, List.map_append]
    have hl : GroupChunk cm eM labT stabT grepT g0 l := h 0 (by simp)
    have ht : GroupsAt cm eM labT stabT grepT t (g0 + 1) := by
      intro i hi
      have hh := h (i+1) (by simp [List.length_cons]; omega)
      have he : g0 + (i+1) = (g0+1) + i := by omega
      rw [he] at hh
      exact hh
    rw [List.nodup_append]
    refine ⟨strictInc_nodup hl.1, ih (g0+1) ht, ?_⟩
    intro a ha b hb hab
    rw [List.mem_map] at ha
    obtain ⟨v, hv, hav⟩ := ha
    rw [List.mem_map] at hb
    obtain ⟨v', hv', hv'eq⟩ := hb
    obtain ⟨k, hk, hvl'⟩ := mem_flatten_exists_getD hv'
    have hck := ht k hk
    have hla : lG labT a = g0 := by rw [← hav]; exact (hl.2 v hv).2.1
    have hlb : lG labT b = (g0+1) + k := by
      rw [← hv'eq]
      exact (hck.2 v' hvl').2.1
    rw [hab] at hla
    omega


/-! ## `getD` helpers -/

lemma getD_of_lt {α : Type} {l : List α} {i : ℕ} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

lemma getD_mem {l : List (List ℕ)} {i : ℕ} (h : i < l.length) : l.getD i [] ∈ l := by
  rw [getD_of_lt (d := ([] : List ℕ)) h, List.mem_iff_getElem]
  exact ⟨i, h, rfl⟩

lemma map_length_getD {G : List (List ℕ)} {g : ℕ} (h : g < G.length) :
    (G.map List.length).getD g 0 = (G.getD g []).length := by
  have h2 : g < (G.map List.length).length := by rw [List.length_map]; exact h
  rw [getD_of_lt (l := G.map List.length) (i := g) (d := (0:ℕ)) h2,
      getD_of_lt (l := G) (i := g) (d := ([] : List ℕ)) h, List.getElem_map]

lemma nodup_filter' {l : List ℕ} (h : l.Nodup) (p : ℕ → Bool) : (l.filter p).Nodup :=
  List.Nodup.filter p h

/-! ## The `eAll` facts -/

lemma eAll_len : eAll.length = 4641 := rfl

lemma eAll_nodup : eAll.Nodup := by
  have h := eexact_ok
  rw [eExactOK, Bool.and_eq_true] at h
  exact (List.Perm.nodup_iff (Work.PTCert.msortK_perm 40 eAll)).mp (strictInc_nodup h.2)

lemma eAll_digits {z : ℕ} (hz : z ∈ eAll) : z % 128 < 81 ∧ z / 128 < 81 := by
  rw [Work.PTCert.eAll_chunks_eAux] at hz
  simp only [List.mem_append] at hz
  rcases hz with ((((((h0|h1)|h2)|h3)|h4)|h5)|h6)|h7
  · obtain ⟨_, hb, hc, _⟩ := Work.PTCert.eChunkOK_spec cmT eM nT repT eC0 echunk_ok0 z h0
    exact ⟨hb, hc⟩
  · obtain ⟨_, hb, hc, _⟩ := Work.PTCert.eChunkOK_spec cmT eM nT repT eC1 echunk_ok1 z h1
    exact ⟨hb, hc⟩
  · obtain ⟨_, hb, hc, _⟩ := Work.PTCert.eChunkOK_spec cmT eM nT repT eC2 echunk_ok2 z h2
    exact ⟨hb, hc⟩
  · obtain ⟨_, hb, hc, _⟩ := Work.PTCert.eChunkOK_spec cmT eM nT repT eC3 echunk_ok3 z h3
    exact ⟨hb, hc⟩
  · obtain ⟨_, hb, hc, _⟩ := Work.PTCert.eChunkOK_spec cmT eM nT repT eC4 echunk_ok4 z h4
    exact ⟨hb, hc⟩
  · obtain ⟨_, hb, hc, _⟩ := Work.PTCert.eChunkOK_spec cmT eM nT repT eC5 echunk_ok5 z h5
    exact ⟨hb, hc⟩
  · obtain ⟨_, hb, hc, _⟩ := Work.PTCert.eChunkOK_spec cmT eM nT repT eC6 echunk_ok6 z h6
    exact ⟨hb, hc⟩
  · obtain ⟨_, hb, hc, _⟩ := Work.PTCert.eChunkOK_spec cmT eM nT repT eC7 echunk_ok7 z h7
    exact ⟨hb, hc⟩

/-! ## Combining chunk-level checks -/

lemma memIdxOK_flatten_spec {chunks : List (List (List ℕ))} {ns : ℕ}
    (h : ∀ j < chunks.length, memIdxOK (chunks.getD j []) ns = true) :
    ∀ l ∈ chunks.flatten, ∀ v ∈ l, v % 4096 < ns := by
  intro l hl v hv
  rw [List.mem_flatten] at hl
  obtain ⟨l0, hl0, hll⟩ := hl
  rw [List.mem_iff_getElem] at hl0
  obtain ⟨j, hj, hjl⟩ := hl0
  have hinst : memIdxOK chunks[j] ns = true := by
    have hh := h j hj
    rw [getD_of_lt (l := chunks) (i := j) (d := ([] : List (List ℕ))) hj] at hh
    exact hh
  have hll' : l ∈ chunks[j] := hjl ▸ hll
  exact memIdxOK_sound chunks[j] ns hinst l hll' v hv

lemma closOK_flatten_spec {cm labT stabT grepT : NT} {chunks : List (List ℕ)} {gs : List ℕ}
    (h : ∀ j < chunks.length, closOK cm labT stabT grepT (chunks.getD j []) gs = true) :
    ∀ g ∈ gs, ∀ s ∈ chunks.flatten, lG labT (actC cm (stabT.get s) (cG grepT g)) = g := by
  intro g hg s hs
  rw [List.mem_flatten] at hs
  obtain ⟨l, hl, hsl⟩ := hs
  rw [List.mem_iff_getElem] at hl
  obtain ⟨j, hj, hjl⟩ := hl
  have hinst : closOK cm labT stabT grepT chunks[j] gs = true := by
    have hh := h j hj
    rw [getD_of_lt (l := chunks) (i := j) (d := ([] : List ℕ)) hj] at hh
    exact hh
  have hsl' : s ∈ chunks[j] := hjl ▸ hsl
  exact closOK_sound hinst g hg s hsl'

/-! ## The generic reduction for one row -/

/-- A row's data (group lists `G`, sizes `sz`, number of groups `ng`, stabiliser `stab`) satisfying
the extracted check hypotheses forces the `GroupSem` clauses for that row. -/
theorem genericGroups (labT stabT grepT : NT) (stab sz : List ℕ) (G : List (List ℕ)) (ng : ℕ)
    (hG : GroupsAt cmT eM labT stabT grepT G 0)
    (hGsz : G.map List.length = sz)
    (hGlen : G.length = ng)
    (hszlen : sz.length = ng)
    (hsum : (G.flatten).length = 4641)
    (hrep : ∀ g < ng, cG grepT g ∈ eAll ∧ lG labT (cG grepT g) = g)
    (hstab : ∀ s < stab.length, ∀ k < 81, lk (stabT.get s) k < 81)
    (hclos : ∀ s < stab.length, ∀ g < ng, lG labT (actC cmT (stabT.get s) (cG grepT g)) = g)
    (hidx : ∀ i < G.length, ∀ v ∈ G.getD i [], v % 4096 < stab.length) :
    (∀ z ∈ eAll, lG labT z < ng ∧ ∃ i < stab.length, actC cmT (stabT.get i) (cG grepT (lG labT z)) = z) ∧
    (∀ g < ng, cG grepT g ∈ eAll ∧ lG labT (cG grepT g) = g) ∧
    (∀ s < stab.length, ∀ g < ng, lG labT (actC cmT (stabT.get s) (cG grepT g)) = g) ∧
    (∀ g < ng, (eAll.filter (fun z => lG labT z = g)).length = sz.getD g 0) ∧
    sz.length = ng := by
  have hnodup : (G.flatten.map (fun v => v / 4096)).Nodup := GroupsAt_nodup G 0 hG
  have hsub : ∀ z ∈ G.flatten.map (fun v => v / 4096), z ∈ eAll := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
    obtain ⟨i, hi, hvi⟩ := mem_flatten_exists_getD hv
    have hilt : i < ng := by rw [← hGlen]; exact hi
    obtain ⟨hne, hlab, hact⟩ := (hG i hi).2 v hvi
    simp only [Nat.zero_add] at hlab hact
    have hc1 := (eAll_digits (hrep i hilt).1).2
    have hc2 := (eAll_digits (hrep i hilt).1).1
    have hs : v % 4096 < stab.length := hidx i hi v hvi
    have hlk1 := hstab _ hs _ hc1
    have hlk2 := hstab _ hs _ hc2
    refine Work.PTCert.NSemAux.mem_eAll_of_em_ne_zero ?_ hne
    rw [← hact]
    exact Work.PTCert.normC_lt cmT _ _ hlk1 hlk2
  have hlen : (G.flatten.map (fun v => v / 4096)).length = 4641 := by rw [List.length_map, hsum]
  have hcard : (G.flatten.map (fun v => v / 4096)).toFinset.card = eAll.toFinset.card := by
    rw [List.toFinset_card_of_nodup hnodup, List.toFinset_card_of_nodup eAll_nodup, hlen, eAll_len]
  have hfinset : (G.flatten.map (fun v => v / 4096)).toFinset = eAll.toFinset :=
    Finset.eq_of_subset_of_card_le
      (by intro x hx; rw [List.mem_toFinset] at hx ⊢; exact hsub _ hx)
      (by rw [hcard])
  have hAll : ∀ z ∈ eAll, z ∈ G.flatten.map (fun v => v / 4096) := by
    intro z hz
    have h1 : z ∈ eAll.toFinset := List.mem_toFinset.mpr hz
    have h2 : z ∈ (G.flatten.map (fun v => v / 4096)).toFinset := by rwa [hfinset]
    exact List.mem_toFinset.mp h2
  refine ⟨?_, hrep, hclos, ?_, hszlen⟩
  · intro z hz
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp (hAll z hz)
    obtain ⟨i, hi, hvi⟩ := mem_flatten_exists_getD hv
    obtain ⟨hne, hlab, hact⟩ := (hG i hi).2 v hvi
    simp only [Nat.zero_add] at hlab hact
    have hilt : i < ng := by rw [← hGlen]; exact hi
    have hs : v % 4096 < stab.length := hidx i hi v hvi
    refine ⟨by rw [hlab]; exact hilt, ⟨v % 4096, hs, ?_⟩⟩
    rw [hlab]; exact hact
  · intro g hg
    have hgl : g < G.length := by rw [hGlen]; exact hg
    have hnod1 : ((G.getD g []).map (fun v => v / 4096)).Nodup := strictInc_nodup (hG g hgl).1
    have hnod2 : (eAll.filter (fun z => lG labT z = g)).Nodup := nodup_filter' eAll_nodup _
    have hsub1 : (G.getD g []).map (fun v => v / 4096) ⊆ eAll.filter (fun z => lG labT z = g) := by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
      obtain ⟨_, hlab, _⟩ := (hG g hgl).2 v hv
      simp only [Nat.zero_add] at hlab
      rw [List.mem_filter]
      refine ⟨?_, ?_⟩
      · exact hsub _ (by rw [List.mem_map]; exact ⟨v, List.mem_flatten.mpr ⟨G.getD g [], getD_mem hgl, hv⟩, rfl⟩)
      · rw [decide_eq_true_eq]; exact hlab
    have hle1 : (G.getD g []).length ≤ (eAll.filter (fun z => lG labT z = g)).length := by
      calc (G.getD g []).length = ((G.getD g []).map (fun v => v / 4096)).length := by rw [List.length_map]
        _ = ((G.getD g []).map (fun v => v / 4096)).toFinset.card := (List.toFinset_card_of_nodup hnod1).symm
        _ ≤ (eAll.filter (fun z => lG labT z = g)).toFinset.card := Finset.card_le_card (by
              intro x hx; rw [List.mem_toFinset] at hx ⊢; exact hsub1 hx)
        _ = (eAll.filter (fun z => lG labT z = g)).length := List.toFinset_card_of_nodup hnod2
    have hle2 : (eAll.filter (fun z => lG labT z = g)).length ≤ (G.getD g []).length := by
      have hsub2 : (eAll.filter (fun z => lG labT z = g)) ⊆ (G.getD g []).map (fun v => v / 4096) := by
        intro z hz
        rw [List.mem_filter] at hz
        obtain ⟨hze, hzl⟩ := hz
        rw [decide_eq_true_eq] at hzl
        obtain ⟨v, hv, hvm⟩ := List.mem_map.mp (hAll z hze)
        obtain ⟨i, hi, hvi⟩ := mem_flatten_exists_getD hv
        obtain ⟨_, hlab, _⟩ := (hG i hi).2 v hvi
        simp only [Nat.zero_add] at hlab
        have hig : i = g := by rw [← hlab, hvm]; exact hzl
        rw [List.mem_map]
        exact ⟨v, by rw [hig] at hvi; exact hvi, hvm⟩
      calc (eAll.filter (fun z => lG labT z = g)).length
          = (eAll.filter (fun z => lG labT z = g)).toFinset.card := (List.toFinset_card_of_nodup hnod2).symm
        _ ≤ ((G.getD g []).map (fun v => v / 4096)).toFinset.card := Finset.card_le_card (by
              intro x hx; rw [List.mem_toFinset] at hx ⊢; exact hsub2 hx)
        _ = ((G.getD g []).map (fun v => v / 4096)).length := List.toFinset_card_of_nodup hnod1
        _ = (G.getD g []).length := by rw [List.length_map]
    rw [le_antisymm hle2 hle1, ← hGsz]
    exact (map_length_getD hgl).symm


/-! ## Further helpers -/

lemma sumL_eq_sum (l : List ℕ) : sumL l = l.sum := by
  rw [List.sum_eq_foldr]
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [show sumL (a :: t) = (a + sumL t) from rfl, ih]
    rfl

/-- `tabsOK`: the letter tables are correct for the codes. -/
lemma tabsOK_sound {codes : List ℕ} {T : NT} (h : tabsOK codes T = true) :
    ∀ j < codes.length, ∃ pc sc, validPC 5 pc = true ∧ ∀ k < 81, lk (T.get j) k = actL 5 pc sc k := by
  intro j hj
  have h1 := (allIdx_eq_true.mp h) j hj
  simp only [tabOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h1
  obtain ⟨⟨hpc, _⟩, hall⟩ := h1
  refine ⟨codes.getD j 0 / 32, codes.getD j 0 % 32, hpc, ?_⟩
  intro k hk
  have := hall k hk
  rw [Nat.beq_eq] at this
  rwa [Nat.zero_add] at this

/-- Cumulative group offsets of a list of chunks. -/
def cumul {α : Type} (g0 : ℕ) : List (List α) → List ℕ
  | [] => [g0]
  | l :: t => g0 :: cumul (g0 + l.length) t

/-- Concatenating the group chunks of a row, using the cumulative offsets. -/
lemma GroupsAt_cumul {cm eM labT stabT grepT : NT} :
    ∀ (chunks : List (List (List ℕ))) (g0 : ℕ),
      (∀ j < chunks.length, GroupsAt cm eM labT stabT grepT (chunks.getD j []) ((cumul g0 chunks).getD j 0)) →
      GroupsAt cm eM labT stabT grepT chunks.flatten g0 := by
  intro chunks
  induction chunks with
  | nil => intro g0 h i hi; simp at hi
  | cons l t ih =>
    intro g0 h
    rw [List.flatten_cons]
    have hA : GroupsAt cm eM labT stabT grepT l g0 :=
      h 0 (by rw [List.length_cons]; omega)
    have hB : GroupsAt cm eM labT stabT grepT t.flatten (g0 + l.length) := by
      refine ih (g0 + l.length) ?_
      intro j hj
      exact h (j+1) (by rw [List.length_cons]; omega)
    exact GroupsAt_append hA hB

end Work.PTCert.GSAux

end
