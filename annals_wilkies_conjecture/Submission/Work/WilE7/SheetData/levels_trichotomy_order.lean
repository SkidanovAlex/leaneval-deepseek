import Mathlib
import Submission.Work.WilE7.CoreStep.exists_perm_monotone
import Submission.Work.WilE7.SheetData.transfer_lt_le
import Submission.Work.WilE7.SheetData.exists_enum_range

namespace Work.WilE7.SheetData

/-- **Ordering and de-duplication of a family of continuous level functions with the
`±1`-trichotomy.**  Given a preconnected nonempty `C`, a family of continuous functions
`L t j : C → ℝ` such that each of them is either identically `1`, identically `-1` or satisfies
`|L t j x| < 1` everywhere on `C` (`hcls`), and such that two of them which agree at one point of
`C` agree everywhere on `C` (`hdich`), there are a number `K` of *distinct* level functions that
are not identically `±1`, an enumeration `T : Fin K → …` of them which is strictly increasing at
every point of `C`, a permutation `σ t` of the sheets of each stratum, and the following
properties: `K ≤ ∑ t, k t`; each `T i` is continuous on `C` and `|T i x| < 1`; every `T i` is (in
the reordered family) the level of an actual sheet; the reordered family is monotone in the index
at every point of `C`; and every original sheet is either one of the `T i` or identically `±1`.

Model proof: `Submission/Work/WilE7/CoreStep/sortSheets.lean` proves the same conclusion under the
stronger hypothesis `∀ t j x ∈ C, |L t j x| < 1` (and with extra hypotheses `hinj`, `hk`); the
present statement filters out the sheets that are identically `±1` first. -/
theorem levels_trichotomy_order {p : ℕ} {C : Set (Fin p → ℝ)}
    (hCne : C.Nonempty) (hpre : IsPreconnected C)
    (r : ℕ) (k : Fin r → ℕ) (L : ∀ t : Fin r, Fin (k t) → (Fin p → ℝ) → ℝ)
    (hcont : ∀ t j, ContinuousOn (L t j) C)
    (hcls : ∀ t j, (∀ x ∈ C, L t j x = 1) ∨ (∀ x ∈ C, L t j x = -1) ∨
      (∀ x ∈ C, |L t j x| < 1))
    (hdich : ∀ t j t' j', (∃ x ∈ C, L t j x = L t' j' x) →
      ∀ x ∈ C, L t j x = L t' j' x) :
    ∃ (K : ℕ) (T : Fin K → (Fin p → ℝ) → ℝ) (σ : ∀ t : Fin r, Equiv.Perm (Fin (k t))),
      K ≤ ∑ t, k t ∧
      (∀ i : Fin K, ContinuousOn (T i) C) ∧
      (∀ x ∈ C, StrictMono fun i : Fin K => T i x) ∧
      (∀ x ∈ C, ∀ i : Fin K, |T i x| < 1) ∧
      (∀ i : Fin K, ∃ (t : Fin r) (j : Fin (k t)), ∀ x ∈ C, T i x = L t (σ t j) x) ∧
      (∀ (t : Fin r) (x : Fin p → ℝ), x ∈ C → Monotone fun j : Fin (k t) => L t (σ t j) x) ∧
      (∀ (t : Fin r) (j : Fin (k t)),
        (∃ i : Fin K, ∀ x ∈ C, T i x = L t j x) ∨
        (∀ x ∈ C, L t j x = 1) ∨ (∀ x ∈ C, L t j x = -1)) := by
  classical
  obtain ⟨x0, hx0⟩ := hCne
  -- the family, indexed by pairs `(t, j)`
  let X := Σ t : Fin r, Fin (k t)
  let Lf : X → (Fin p → ℝ) → ℝ := fun a x => L a.1 a.2 x
  have hLcont : ∀ a : X, ContinuousOn (Lf a) C := fun a => by
    simpa only [Lf] using hcont a.1 a.2
  have hdichL : ∀ a b : X, (∃ x ∈ C, Lf a x = Lf b x) → ∀ x ∈ C, Lf a x = Lf b x :=
    fun a b h => hdich a.1 a.2 b.1 b.2 (by simpa only [Lf] using h)
  have hclsL : ∀ a : X, (∀ x ∈ C, Lf a x = 1) ∨ (∀ x ∈ C, Lf a x = -1) ∨
      (∀ x ∈ C, |Lf a x| < 1) := fun a => by simpa only [Lf] using hcls a.1 a.2
  -- dichotomous sheets that agree at the base point agree everywhere
  have htrans_eq : ∀ a b : X, Lf a x0 = Lf b x0 → ∀ x ∈ C, Lf a x = Lf b x :=
    fun a b h => hdichL a b ⟨x0, hx0, h⟩
  -- and the order relations between their values transfer to all of `C`
  have htrans : ∀ a b : X, Lf a x0 < Lf b x0 → ∀ x ∈ C, Lf a x < Lf b x :=
    fun a b h x hx => (transfer_lt_le ⟨x0, hx0⟩ hpre (Lf a) (Lf b) (hLcont a) (hLcont b)
      (hdichL a b) x0 x hx0 hx).1 h
  have htrans_le : ∀ a b : X, Lf a x0 ≤ Lf b x0 → ∀ x ∈ C, Lf a x ≤ Lf b x :=
    fun a b h x hx => (transfer_lt_le ⟨x0, hx0⟩ hpre (Lf a) (Lf b) (hLcont a) (hLcont b)
      (hdichL a b) x0 x hx0 hx).2 h
  -- the sheets that are not identically `±1`
  let good : X → Prop := fun a => ¬ (∀ x ∈ C, Lf a x = 1) ∧ ¬ (∀ x ∈ C, Lf a x = -1)
  have hgood_bnd : ∀ a : X, good a → ∀ x ∈ C, |Lf a x| < 1 := by
    intro a ha
    rcases hclsL a with h1 | h2 | h3
    · exact absurd h1 ha.1
    · exact absurd h2 ha.2
    · exact h3
  -- enumerate in increasing order the distinct values at `x0` of the good sheets
  obtain ⟨K, emb, rep, hKle_card, hrep, hexists⟩ :=
    exists_enum_range (fun a : {a : X // good a} => Lf a.1 x0)
  have hKle : K ≤ ∑ t, k t := by
    calc K ≤ Fintype.card {a : X // good a} := hKle_card
      _ ≤ Fintype.card X := Fintype.card_subtype_le _
      _ = ∑ t, k t := by simp [X, Fintype.card_sigma]
  -- the enumeration of the common levels of the good sheets
  let T : Fin K → (Fin p → ℝ) → ℝ := fun i x => Lf (rep i).1 x
  have hTcont : ∀ i : Fin K, ContinuousOn (T i) C := fun i => by
    simpa only [T] using hLcont (rep i).1
  have hTstrict : ∀ x ∈ C, StrictMono fun i : Fin K => T i x := by
    intro x hx i j hij
    have hlt : Lf (rep i).1 x0 < Lf (rep j).1 x0 := by
      rw [← hrep i, ← hrep j]
      exact emb.strictMono hij
    simpa only [T] using htrans (rep i).1 (rep j).1 hlt x hx
  have hTbnd : ∀ x ∈ C, ∀ i : Fin K, |T i x| < 1 := by
    intro x hx i
    simpa only [T] using hgood_bnd (rep i).1 (rep i).2 x hx
  -- the index of the level of a good sheet in the enumeration
  let idxOf : ∀ a : X, good a → Fin K := fun a ha => (hexists ⟨a, ha⟩).choose
  have hidxOf : ∀ (a : X) (ha : good a), emb (idxOf a ha) = Lf a x0 :=
    fun a ha => (hexists ⟨a, ha⟩).choose_spec
  -- sorting key of a sheet: `-1` for `≡ -1`, the level index for a good sheet, `K+1` for `≡ 1`
  let key : ∀ t : Fin r, Fin (k t) → ℤ := fun t j =>
    if h1 : (∀ x ∈ C, L t j x = 1) then (K : ℤ) + 1
    else if h2 : (∀ x ∈ C, L t j x = -1) then -1
    else ((idxOf ⟨t, j⟩ ⟨h1, h2⟩ : ℕ) : ℤ)
  have key_of_one : ∀ (t : Fin r) (j : Fin (k t)),
      (∀ x ∈ C, L t j x = 1) → key t j = (K : ℤ) + 1 := by
    intro t j h
    simp only [key]
    rw [dif_pos h]
  have key_of_neg : ∀ (t : Fin r) (j : Fin (k t)),
      (∀ x ∈ C, L t j x = -1) → key t j = -1 := by
    intro t j h
    have h1 : ¬ (∀ x ∈ C, L t j x = 1) := by
      intro h'
      have hx1 := h' x0 hx0
      have hxm := h x0 hx0
      rw [hx1] at hxm
      norm_num at hxm
    simp only [key]
    rw [dif_neg h1]
    rw [dif_pos h]
  have key_of_good : ∀ (t : Fin r) (j : Fin (k t)) (h1 : ¬ (∀ x ∈ C, L t j x = 1))
      (h2 : ¬ (∀ x ∈ C, L t j x = -1)), key t j = ((idxOf ⟨t, j⟩ ⟨h1, h2⟩ : ℕ) : ℤ) := by
    intro t j h1 h2
    simp only [key]
    rw [dif_neg h1, dif_neg h2]
  -- the key orders the values of the sheets at every point of `C`
  have hkey_le_val : ∀ (t : Fin r) (a b : Fin (k t)) (x : Fin p → ℝ),
      x ∈ C → key t a ≤ key t b → L t a x ≤ L t b x := by
    intro t a b x hx hkey
    rcases hcls t a with h1a | h2a | h3a
    · rcases hcls t b with h1b | h2b | h3b
      · linarith [h1a x hx, h1b x hx]
      · rw [key_of_one t a h1a, key_of_neg t b h2b] at hkey
        exact absurd hkey (by omega)
      · have hn1b : ¬ (∀ x ∈ C, L t b x = 1) := by
          intro hcon
          have hlt := (abs_lt.mp (h3b x0 hx0)).2
          rw [hcon x0 hx0] at hlt
          exact lt_irrefl 1 hlt
        have hn2b : ¬ (∀ x ∈ C, L t b x = -1) := by
          intro hcon
          have hlt := (abs_lt.mp (h3b x0 hx0)).1
          rw [hcon x0 hx0] at hlt
          exact lt_irrefl (-1) hlt
        rw [key_of_one t a h1a, key_of_good t b hn1b hn2b] at hkey
        exact absurd hkey (by omega)
    · rcases hcls t b with h1b | h2b | h3b
      · linarith [h2a x hx, h1b x hx]
      · linarith [h2a x hx, h2b x hx]
      · have hlt := (abs_lt.mp (h3b x hx)).1
        linarith [h2a x hx, hlt]
    · have hn1a : ¬ (∀ x ∈ C, L t a x = 1) := by
        intro hcon
        have hlt := (abs_lt.mp (h3a x0 hx0)).2
        rw [hcon x0 hx0] at hlt
        exact lt_irrefl 1 hlt
      have hn2a : ¬ (∀ x ∈ C, L t a x = -1) := by
        intro hcon
        have hlt := (abs_lt.mp (h3a x0 hx0)).1
        rw [hcon x0 hx0] at hlt
        exact lt_irrefl (-1) hlt
      rcases hcls t b with h1b | h2b | h3b
      · have hlt := (abs_lt.mp (h3a x hx)).2
        linarith [h1b x hx, hlt]
      · rw [key_of_good t a hn1a hn2a, key_of_neg t b h2b] at hkey
        exact absurd hkey (by omega)
      · have hn1b : ¬ (∀ x ∈ C, L t b x = 1) := by
          intro hcon
          have hlt := (abs_lt.mp (h3b x0 hx0)).2
          rw [hcon x0 hx0] at hlt
          exact lt_irrefl 1 hlt
        have hn2b : ¬ (∀ x ∈ C, L t b x = -1) := by
          intro hcon
          have hlt := (abs_lt.mp (h3b x0 hx0)).1
          rw [hcon x0 hx0] at hlt
          exact lt_irrefl (-1) hlt
        rw [key_of_good t a hn1a hn2a, key_of_good t b hn1b hn2b] at hkey
        have hnat : (idxOf ⟨t, a⟩ ⟨hn1a, hn2a⟩).val ≤ (idxOf ⟨t, b⟩ ⟨hn1b, hn2b⟩).val := by
          omega
        have hemb : emb (idxOf ⟨t, a⟩ ⟨hn1a, hn2a⟩) ≤ emb (idxOf ⟨t, b⟩ ⟨hn1b, hn2b⟩) :=
          emb.strictMono.monotone (Fin.le_iff_val_le_val.mpr hnat)
        rw [hidxOf ⟨t, a⟩ ⟨hn1a, hn2a⟩, hidxOf ⟨t, b⟩ ⟨hn1b, hn2b⟩] at hemb
        simpa only [Lf] using htrans_le ⟨t, a⟩ ⟨t, b⟩ hemb x hx
  -- sort each stratum by the key
  have hsort : ∀ t : Fin r,
      ∃ σ : Equiv.Perm (Fin (k t)), Monotone fun j : Fin (k t) => key t (σ j) :=
    fun t => Work.WilE7.CoreStep.exists_perm_monotone (fun j : Fin (k t) => key t j)
  choose σ hσmono using hsort
  have hmono : ∀ (t : Fin r) (x : Fin p → ℝ), x ∈ C →
      Monotone fun j : Fin (k t) => L t (σ t j) x := by
    intro t x hx j j' hjj
    exact hkey_le_val t (σ t j) (σ t j') x hx (hσmono t hjj)
  -- each `T i` is the level of an actual sheet of the reordered family
  have hcover : ∀ i : Fin K, ∃ (t : Fin r) (j : Fin (k t)), ∀ x ∈ C, T i x = L t (σ t j) x := by
    intro i
    refine ⟨(rep i).1.1, (σ (rep i).1.1).symm (rep i).1.2, ?_⟩
    intro x hx
    simp only [T, Lf, Equiv.apply_symm_apply]
  -- every sheet is either one of the `T i` or identically `±1`
  have hfinal : ∀ (t : Fin r) (j : Fin (k t)),
      (∃ i : Fin K, ∀ x ∈ C, T i x = L t j x) ∨
      (∀ x ∈ C, L t j x = 1) ∨ (∀ x ∈ C, L t j x = -1) := by
    intro t j
    by_cases h1 : (∀ x ∈ C, L t j x = 1)
    · exact Or.inr (Or.inl h1)
    by_cases h2 : (∀ x ∈ C, L t j x = -1)
    · exact Or.inr (Or.inr h2)
    left
    have hg : good ⟨t, j⟩ := ⟨h1, h2⟩
    obtain ⟨i, hi⟩ := hexists ⟨⟨t, j⟩, hg⟩
    refine ⟨i, ?_⟩
    intro x hx
    have h0 : Lf (rep i).1 x0 = Lf ⟨t, j⟩ x0 := by
      rw [← hrep i]
      exact hi
    have hstep := htrans_eq (rep i).1 ⟨t, j⟩ h0 x hx
    simpa only [T, Lf] using hstep
  exact ⟨K, T, σ, hKle, hTcont, hTstrict, hTbnd, hcover, hmono, hfinal⟩

end Work.WilE7.SheetData
