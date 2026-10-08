/-
`Work.BG.caseBC.comb413Self` : a **self-contained** proof of the "COMB413" combinatorial lemma of
Bender--Glauberman (J. Algebra 70 (1981), 200--215, p. 213, middle of the proof of Theorem 4.3),
i.e. of `Work.GW2.C23.Comb413Prop`, not relying on the still-`sorry`-carrying `Work.BG.c4_exists`.

Statement (`Work.GW2.C23.Comb413Prop`): a finite family `v : J → ι → ℤ` of `{0,±1}`-vectors of
support 4, pairwise orthogonal, every column of size 0, 1 or 3, `F₂`-independent as row vectors,
with two rows sharing a coordinate, contains three rows `j₁ j₂ j₃` and a coordinate `i₀` with
support exactly `{j₁,j₂,j₃}`, together with coordinates `p₁ p₂ p₃` whose supports are exactly
`{j₁}`, `{j₂}`, `{j₃}`.

The proof follows the Bender--Glauberman case analysis.

* A row is *full* when all four of its columns are triple columns (`Work.BG.Full`).
* `c4ExistsSelf` (the only ingredient missing in the repository, proved here from scratch):
  a full row `j` has four neighbours `a b c d` forming a 4-cycle, with columns
  `ColF p = {j,a,b}`, `ColF q = {j,b,c}`, `ColF r = {j,c,d}`, `ColF s = {j,d,a}` and "second
  columns" `u, y, z, x` with `Supp a ∩ Supp b = {p,u}`, `Supp b ∩ Supp c = {q,y}`,
  `Supp c ∩ Supp d = {r,z}`, `Supp d ∩ Supp a = {s,x}`; this is `Work.BG.C4Data`.
  Its heart is `c4PairsSelf`: the abstract statement that a 2-regular simple bipartite graph with
  four vertices on each side and no two left vertices sharing a neighbourhood is a single
  8-cycle (i.e. the `t i = (ColF v i) \ {j}` are the edges of a 4-cycle on `NB v j`).
* `caseQ_false` and `caseP_false` (already proved in the repository) then rule out a full row:
  each `C4Data` configuration that survives forces a set of rows meeting every column evenly,
  contradicting `Work.BG.even_set_contra`.
* Hence no row is full, so by `Work.BG.tc_sc_card` every row has at most three triple columns
  and therefore (using the hypothesis that two rows share a coordinate to produce a triple
  column) at least one singleton column; the three rows of a triple column are the required
  `j₁ j₂ j₃`, and the singleton columns of those rows give `p₁ p₂ p₃`.
-/
import Mathlib
import Submission.Work.BG.C413Defs
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.caseQ_false
import Submission.Work.BG.caseP_false

namespace Work.BG.caseBC

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! ## The abstract 4-cycle lemma -/

/-- **Abstract core of the `C4Data` existence.** Let `S` (columns) and `NB` (rows) be `4`-element
finsets, `t : ι → Finset J` a map with `(t i).card = 2` and `t i ⊆ NB` for `i ∈ S`, injective on
`S`, and such that every `k ∈ NB` lies in exactly two of the `t i` (`i ∈ S`). Then the `t i`
(`i ∈ S`) are the four edges of a 4-cycle on `NB` through `a`: there are `b c d ∈ NB` and
`p q r s ∈ S` with `S = {p,q,r,s}`, `t p = {a,b}`, `t q = {b,c}`, `t r = {c,d}`, `t s = {d,a}`.

Equivalently: a simple bipartite graph with parts of size `4`, all degrees `2` and no two left
vertices with a common neighbourhood is a single `8`-cycle. -/
theorem c4PairsSelf {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    (S : Finset ι) (NB : Finset J) (t : ι → Finset J) (a : J)
    (hS : S.card = 4) (hNB : NB.card = 4) (ha : a ∈ NB)
    (ht2 : ∀ i ∈ S, (t i).card = 2)
    (htsub : ∀ i ∈ S, t i ⊆ NB)
    (hinj : ∀ i ∈ S, ∀ i' ∈ S, t i = t i' → i = i')
    (hdeg : ∀ k ∈ NB, (S.filter (fun i => k ∈ t i)).card = 2) :
    ∃ b c d : J, ∃ p q r s : ι,
      b ≠ c ∧ c ≠ d ∧ d ≠ a ∧ a ≠ c ∧ b ≠ d ∧
      S = {p, q, r, s} ∧ t p = {a, b} ∧ t q = {b, c} ∧ t r = {c, d} ∧ t s = {d, a} := by
  classical
  have hFa : (S.filter (fun i => a ∈ t i)).card = 2 := hdeg a ha
  obtain ⟨p, s, hps, hFa_eq⟩ := Finset.card_eq_two.mp hFa
  have hp_mem : p ∈ S.filter (fun i => a ∈ t i) := by rw [hFa_eq]; simp
  have hs_mem : s ∈ S.filter (fun i => a ∈ t i) := by rw [hFa_eq]; simp
  have hpS : p ∈ S := (Finset.mem_filter.mp hp_mem).1
  have hsS : s ∈ S := (Finset.mem_filter.mp hs_mem).1
  have hpa : a ∈ t p := (Finset.mem_filter.mp hp_mem).2
  have hsa : a ∈ t s := (Finset.mem_filter.mp hs_mem).2
  have hcard_ep : ((t p).erase a).card = 1 := by
    rw [Finset.card_erase_of_mem hpa, ht2 p hpS]
  obtain ⟨b, hb_eq⟩ := Finset.card_eq_one.mp hcard_ep
  have htp : t p = {a, b} := by rw [← Finset.insert_erase hpa, hb_eq]
  have hb_erase_mem : b ∈ (t p).erase a := by rw [hb_eq]; simp
  have hba : b ≠ a := (Finset.mem_erase.mp hb_erase_mem).1
  have hb_p : b ∈ t p := by rw [htp]; simp
  have hbNB : b ∈ NB := htsub p hpS hb_p
  have hcard_es : ((t s).erase a).card = 1 := by
    rw [Finset.card_erase_of_mem hsa, ht2 s hsS]
  obtain ⟨d, hd_eq⟩ := Finset.card_eq_one.mp hcard_es
  have hts : t s = {a, d} := by rw [← Finset.insert_erase hsa, hd_eq]
  have hd_erase_mem : d ∈ (t s).erase a := by rw [hd_eq]; simp
  have hda : d ≠ a := (Finset.mem_erase.mp hd_erase_mem).1
  have hd_s : d ∈ t s := by rw [hts]; simp
  have hdNB : d ∈ NB := htsub s hsS hd_s
  have hbd : b ≠ d := by
    intro h
    have : t p = t s := by rw [htp, hts, h]
    exact hps (hinj p hpS s hsS this)
  have hbE : b ∈ NB.erase a := Finset.mem_erase.mpr ⟨hba, hbNB⟩
  have hdE : d ∈ (NB.erase a).erase b :=
    Finset.mem_erase.mpr ⟨hbd.symm, Finset.mem_erase.mpr ⟨hda, hdNB⟩⟩
  have hYcard : (((NB.erase a).erase b).erase d).card = 1 := by
    rw [Finset.card_erase_of_mem hdE, Finset.card_erase_of_mem hbE,
      Finset.card_erase_of_mem ha, hNB]
  obtain ⟨c, hc_eq⟩ := Finset.card_eq_one.mp hYcard
  have hcY : c ∈ ((NB.erase a).erase b).erase d := by rw [hc_eq]; simp
  have hc_d : c ≠ d := (Finset.mem_erase.mp hcY).1
  have hc_b : c ≠ b := (Finset.mem_erase.mp (Finset.mem_erase.mp hcY).2).1
  have hc_a : c ≠ a :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hcY).2).2).1
  have hcNB : c ∈ NB :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hcY).2).2).2
  have hbc : b ≠ c := hc_b.symm
  have hca : a ≠ c := hc_a.symm
  have hNB_eq : NB = ({a, b, c, d} : Finset J) := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hka : k = a
      · exact Or.inl hka
      · by_cases hkb : k = b
        · exact Or.inr (Or.inl hkb)
        · by_cases hkd : k = d
          · exact Or.inr (Or.inr (Or.inr hkd))
          · have hkY : k ∈ ((NB.erase a).erase b).erase d :=
              Finset.mem_erase.mpr
                ⟨hkd, Finset.mem_erase.mpr ⟨hkb, Finset.mem_erase.mpr ⟨hka, hk⟩⟩⟩
            rw [hc_eq] at hkY
            exact Or.inr (Or.inr (Or.inl (by simpa using hkY)))
    · rw [hNB, Finset.card_eq_four.mpr
        ⟨a, b, c, d, hba.symm, hca, hda.symm, hbc, hbd, hc_d, rfl⟩]
  have hsEp : s ∈ S.erase p := Finset.mem_erase.mpr ⟨hps.symm, hsS⟩
  have hRcard : ((S.erase p).erase s).card = 2 := by
    rw [Finset.card_erase_of_mem hsEp, Finset.card_erase_of_mem hpS, hS]
  have hFb : (S.filter (fun i => b ∈ t i)).card = 2 := hdeg b hbNB
  have hpFb : p ∈ S.filter (fun i => b ∈ t i) := by
    rw [Finset.mem_filter]; exact ⟨hpS, hb_p⟩
  obtain ⟨q, hqp, hFb_eq⟩ : ∃ q, q ≠ p ∧ S.filter (fun i => b ∈ t i) = {p, q} := by
    obtain ⟨x, y, hxy, hFb_xy⟩ := Finset.card_eq_two.mp hFb
    have hpxy : p = x ∨ p = y := by
      have h1 : p ∈ ({x, y} : Finset ι) := by rw [← hFb_xy]; exact hpFb
      simpa using h1
    rcases hpxy with h | h
    · refine ⟨y, ?_, ?_⟩
      · intro hy; exact hxy (h.symm.trans hy.symm)
      · rw [hFb_xy, h]
    · refine ⟨x, ?_, ?_⟩
      · intro hx; exact hxy (hx.trans h)
      · rw [hFb_xy, ← h]; exact Finset.pair_comm x p
  have hq_mem : q ∈ S.filter (fun i => b ∈ t i) := by rw [hFb_eq]; simp
  have hqS : q ∈ S := (Finset.mem_filter.mp hq_mem).1
  have hbq : b ∈ t q := (Finset.mem_filter.mp hq_mem).2
  have hsFb : s ∉ S.filter (fun i => b ∈ t i) := by
    rw [Finset.mem_filter]
    rintro ⟨-, hbts⟩
    rw [hts] at hbts
    rcases (by simpa using hbts : b = a ∨ b = d) with h | h
    · exact hba h
    · exact hbd h
  have hq_ne_s : q ≠ s := by
    intro h
    apply hsFb
    rw [← h, hFb_eq]; simp
  have hFd : (S.filter (fun i => d ∈ t i)).card = 2 := hdeg d hdNB
  have hsFd : s ∈ S.filter (fun i => d ∈ t i) := by
    rw [Finset.mem_filter]; exact ⟨hsS, hd_s⟩
  obtain ⟨r, hrs, hFd_eq⟩ : ∃ r, r ≠ s ∧ S.filter (fun i => d ∈ t i) = {s, r} := by
    obtain ⟨x, y, hxy, hFd_xy⟩ := Finset.card_eq_two.mp hFd
    have hsxy : s = x ∨ s = y := by
      have h1 : s ∈ ({x, y} : Finset ι) := by rw [← hFd_xy]; exact hsFd
      simpa using h1
    rcases hsxy with h | h
    · refine ⟨y, ?_, ?_⟩
      · intro hy; exact hxy (h.symm.trans hy.symm)
      · rw [hFd_xy, h]
    · refine ⟨x, ?_, ?_⟩
      · intro hx; exact hxy (hx.trans h)
      · rw [hFd_xy, ← h]; exact Finset.pair_comm x s
  have hr_mem : r ∈ S.filter (fun i => d ∈ t i) := by rw [hFd_eq]; simp
  have hrS : r ∈ S := (Finset.mem_filter.mp hr_mem).1
  have hdr : d ∈ t r := (Finset.mem_filter.mp hr_mem).2
  have hpFd : p ∉ S.filter (fun i => d ∈ t i) := by
    rw [Finset.mem_filter]
    rintro ⟨-, hdtp⟩
    rw [htp] at hdtp
    rcases (by simpa using hdtp : d = a ∨ d = b) with h | h
    · exact hda h
    · exact hbd h.symm
  have hr_ne_p : r ≠ p := by
    intro h
    apply hpFd
    rw [← h, hFd_eq]; simp
  have hqR : q ∈ (S.erase p).erase s :=
    Finset.mem_erase.mpr ⟨hq_ne_s, Finset.mem_erase.mpr ⟨hqp, hqS⟩⟩
  have hrR : r ∈ (S.erase p).erase s :=
    Finset.mem_erase.mpr ⟨hrs, Finset.mem_erase.mpr ⟨hr_ne_p, hrS⟩⟩
  have hCsub : S.filter (fun i => c ∈ t i) ⊆ (S.erase p).erase s := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨hiS, hic⟩ := hi
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hiS⟩⟩
    · intro his
      have h1 : c ∈ t s := by rw [← his]; exact hic
      rw [hts] at h1
      rcases (by simpa using h1 : c = a ∨ c = d) with h | h
      · exact hc_a h
      · exact hc_d h
    · intro hip
      have h1 : c ∈ t p := by rw [← hip]; exact hic
      rw [htp] at h1
      rcases (by simpa using h1 : c = a ∨ c = b) with h | h
      · exact hc_a h
      · exact hc_b h
  have hCcard : (S.filter (fun i => c ∈ t i)).card = 2 := hdeg c hcNB
  have hCeq : S.filter (fun i => c ∈ t i) = (S.erase p).erase s :=
    Finset.eq_of_subset_of_card_le hCsub (by rw [hCcard, hRcard])
  have hqC : q ∈ S.filter (fun i => c ∈ t i) := by rw [hCeq]; exact hqR
  have hrC : r ∈ S.filter (fun i => c ∈ t i) := by rw [hCeq]; exact hrR
  have hctq : c ∈ t q := (Finset.mem_filter.mp hqC).2
  have hctr : c ∈ t r := (Finset.mem_filter.mp hrC).2
  have hqr : q ≠ r := by
    intro h
    have hd_q : d ∈ t q := by rw [h]; exact hdr
    have hsub : ({b, c, d} : Finset J) ⊆ t q := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hbq
      · exact hctq
      · exact hd_q
    have hcard3 : ({b, c, d} : Finset J).card = 3 := by
      rw [Finset.card_eq_three.mpr]
      exact ⟨b, c, d, hbc, hbd, hc_d, rfl⟩
    have hle := Finset.card_le_card hsub
    rw [hcard3, ht2 q hqS] at hle
    omega
  have haq : a ∉ t q := by
    intro h
    have h1 : q ∈ S.filter (fun i => a ∈ t i) := by
      rw [Finset.mem_filter]; exact ⟨hqS, h⟩
    rw [hFa_eq] at h1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with h' | h'
    · exact hqp h'
    · exact hq_ne_s h'
  have htq_sub : t q ⊆ ({b, c, d} : Finset J) := by
    intro k hk
    have hkNB : k ∈ NB := htsub q hqS hk
    rw [hNB_eq] at hkNB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hkNB ⊢
    rcases hkNB with rfl | rfl | rfl | rfl
    · exact absurd hk haq
    · simp
    · simp
    · simp
  have htq : t q = {b, c} := by
    have hsub : ({b, c} : Finset J) ⊆ t q := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hbq
      · exact hctq
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [ht2 q hqS, Finset.card_pair hbc])).symm
  have har : a ∉ t r := by
    intro h
    have h1 : r ∈ S.filter (fun i => a ∈ t i) := by
      rw [Finset.mem_filter]; exact ⟨hrS, h⟩
    rw [hFa_eq] at h1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with h' | h'
    · exact hr_ne_p h'
    · exact hrs h'
  have htr_sub : t r ⊆ ({b, c, d} : Finset J) := by
    intro k hk
    have hkNB : k ∈ NB := htsub r hrS hk
    rw [hNB_eq] at hkNB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hkNB ⊢
    rcases hkNB with rfl | rfl | rfl | rfl
    · exact absurd hk har
    · simp
    · simp
    · simp
  have htr : t r = {c, d} := by
    have hsub : ({c, d} : Finset J) ⊆ t r := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hctr
      · exact hdr
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [ht2 r hrS, Finset.card_pair hc_d])).symm
  have hpr : p ≠ r := hr_ne_p.symm
  have hSpqrs : S = ({p, q, r, s} : Finset ι) := by
    have hsub : ({p, q, r, s} : Finset ι) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hpS
      · exact hqS
      · exact hrS
      · exact hsS
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hS, Finset.card_eq_four.mpr
      ⟨p, q, r, s, hqp.symm, hpr, hps, hqr, hq_ne_s, hrs, rfl⟩])).symm
  refine ⟨b, c, d, p, q, r, s, hbc, hc_d, hda, hca, hbd, hSpqrs, htp, htq, htr, ?_⟩
  rw [hts]; exact Finset.pair_comm a d

/-! ## Elementary structure of a full row -/

/-- Every column of a *full* row (one whose four columns are all triple columns) is a triple
column: `TC v j = Supp v j`. -/
theorem fullColCardSelf {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]
    (v : J → ι → ℤ)
    (h1 : ∀ j, (Work.BG.Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    {j : J} (hj : Work.BG.Full v j) {i : ι} (hi : i ∈ Work.BG.Supp v j) :
    (Work.BG.ColF v i).card = 3 := by
  have hTC : Work.BG.TC v j = Work.BG.Supp v j := by
    refine Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) ?_
    rw [hj, (h1 j).1]
  have hi' : i ∈ Work.BG.TC v j := by rw [hTC]; exact hi
  exact (Finset.mem_filter.mp hi').2

/-- A neighbour `k` of `j` (a row sharing a column with `j`) meets the four columns of `j` in
exactly two of them. -/
theorem nbDegSelf {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]
    (v : J → ι → ℤ)
    (h1 : ∀ j, (Work.BG.Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h2 : ∀ j k, j ≠ k → ∑ i, v j i * v k i = 0)
    (h4 : ∀ n : J → ℤ, (∃ j, Odd (n j)) → ∃ i, Odd (∑ j, n j * v j i))
    {j k : J} (hk : k ∈ Work.BG.NB v j) :
    ((Work.BG.Supp v j).filter (fun i => k ∈ Work.BG.ColF v i)).card = 2 := by
  obtain ⟨-, hkj, hne⟩ := Finset.mem_filter.mp hk
  have hset : (Work.BG.Supp v j).filter (fun i => k ∈ Work.BG.ColF v i)
      = Work.BG.Supp v j ∩ Work.BG.Supp v k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_inter, Work.BG.mem_Supp, Work.BG.mem_ColF]
  rw [hset]
  rcases Work.BG.inter_card_cases v h1 h2 h4 (Ne.symm hkj) with h | h
  · rw [Finset.card_eq_zero] at h
    rw [h] at hne
    simp at hne
  · exact h

/-! ## The second columns of the four edges of the cycle -/

/-- Given the four columns of the cycle through `j` (`ColF p = {j,a,b}`, `ColF q = {j,b,c}`,
`ColF r = {j,c,d}`, `ColF s = {j,d,a}`), each of the four edges `ab, bc, cd, da` acquires a
*second* column `u, y, z, x`. -/
theorem c4SecondSelf {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]
    (v : J → ι → ℤ)
    (h1 : ∀ j, (Work.BG.Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h2 : ∀ j k, j ≠ k → ∑ i, v j i * v k i = 0)
    (h4 : ∀ n : J → ℤ, (∃ j, Odd (n j)) → ∃ i, Odd (∑ j, n j * v j i))
    {j a b c d : J} {p q r s : ι}
    (hp : Work.BG.ColF v p = {j, a, b}) (hq : Work.BG.ColF v q = {j, b, c})
    (hr : Work.BG.ColF v r = {j, c, d}) (hs : Work.BG.ColF v s = {j, d, a})
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hda : d ≠ a) :
    ∃ u y z x : ι,
      Work.BG.Supp v a ∩ Work.BG.Supp v b = {p, u} ∧ u ≠ p ∧
      Work.BG.Supp v b ∩ Work.BG.Supp v c = {q, y} ∧ y ≠ q ∧
      Work.BG.Supp v c ∩ Work.BG.Supp v d = {r, z} ∧ z ≠ r ∧
      Work.BG.Supp v d ∩ Work.BG.Supp v a = {s, x} ∧ x ≠ s := by
  have key : ∀ {x y : J} {t : ι}, x ≠ y → t ∈ Work.BG.Supp v x → t ∈ Work.BG.Supp v y →
      ∃ u : ι, Work.BG.Supp v x ∩ Work.BG.Supp v y = {t, u} ∧ u ≠ t := by
    intro x y t hxy hx hy
    have hne : (Work.BG.Supp v x ∩ Work.BG.Supp v y).Nonempty :=
      ⟨t, Finset.mem_inter.mpr ⟨hx, hy⟩⟩
    have hcard : (Work.BG.Supp v x ∩ Work.BG.Supp v y).card = 2 := by
      rcases Work.BG.inter_card_cases v h1 h2 h4 hxy with h | h
      · rw [Finset.card_eq_zero] at h
        rw [h] at hne
        simp at hne
      · exact h
    have ht : t ∈ Work.BG.Supp v x ∩ Work.BG.Supp v y := Finset.mem_inter.mpr ⟨hx, hy⟩
    obtain ⟨t1, t2, ht12, heq⟩ := Finset.card_eq_two.mp hcard
    have ht12' : t = t1 ∨ t = t2 := by
      have hmem : t ∈ ({t1, t2} : Finset ι) := by rw [← heq]; exact ht
      simpa using hmem
    rcases ht12' with h | h
    · refine ⟨t2, ?_, ?_⟩
      · rw [heq, h]
      · rw [h]; exact Ne.symm ht12
    · refine ⟨t1, ?_, ?_⟩
      · rw [heq, h, Finset.pair_comm]
      · rw [h]; exact ht12
  have hp_a : p ∈ Work.BG.Supp v a := by
    rw [Work.BG.mem_Supp, ← Work.BG.mem_ColF, hp]; simp
  have hp_b : p ∈ Work.BG.Supp v b := by
    rw [Work.BG.mem_Supp, ← Work.BG.mem_ColF, hp]; simp
  have hq_b : q ∈ Work.BG.Supp v b := by
    rw [Work.BG.mem_Supp, ← Work.BG.mem_ColF, hq]; simp
  have hq_c : q ∈ Work.BG.Supp v c := by
    rw [Work.BG.mem_Supp, ← Work.BG.mem_ColF, hq]; simp
  have hr_c : r ∈ Work.BG.Supp v c := by
    rw [Work.BG.mem_Supp, ← Work.BG.mem_ColF, hr]; simp
  have hr_d : r ∈ Work.BG.Supp v d := by
    rw [Work.BG.mem_Supp, ← Work.BG.mem_ColF, hr]; simp
  have hs_d : s ∈ Work.BG.Supp v d := by
    rw [Work.BG.mem_Supp, ← Work.BG.mem_ColF, hs]; simp
  have hs_a : s ∈ Work.BG.Supp v a := by
    rw [Work.BG.mem_Supp, ← Work.BG.mem_ColF, hs]; simp
  obtain ⟨u, hu, hup⟩ := key hab hp_a hp_b
  obtain ⟨y, hy, hyq⟩ := key hbc hq_b hq_c
  obtain ⟨z, hz, hzr⟩ := key hcd hr_c hr_d
  obtain ⟨x, hx, hxs⟩ := key hda hs_d hs_a
  exact ⟨u, y, z, x, hu, hup, hy, hyq, hz, hzr, hx, hxs⟩

/-! ## A full row has the `C4Data` structure -/

/-- **The 4-cycle structure of a full row.** The four neighbours of a full row `j` form a
4-cycle, the four columns of `j` being `ColF p = {j,a,b}`, `ColF q = {j,b,c}`,
`ColF r = {j,c,d}`, `ColF s = {j,d,a}` (with `a,b,c,d` pairwise distinct). -/
theorem c4CoreSelf {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]
    (v : J → ι → ℤ)
    (h1 : ∀ j, (Work.BG.Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h2 : ∀ j k, j ≠ k → ∑ i, v j i * v k i = 0)
    (h3 : ∀ i, (Work.BG.ColF v i).card ∈ ({0,1,3} : Finset ℕ))
    (h4 : ∀ n : J → ℤ, (∃ j, Odd (n j)) → ∃ i, Odd (∑ j, n j * v j i))
    {j : J} (hj : Work.BG.Full v j) :
    ∃ a b c d : J, ∃ p q r s : ι,
      Work.BG.ColF v p = {j, a, b} ∧ Work.BG.ColF v q = {j, b, c} ∧
      Work.BG.ColF v r = {j, c, d} ∧ Work.BG.ColF v s = {j, d, a} ∧
      Work.BG.Supp v j = {p, q, r, s} ∧ a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ a := by
  classical
  have hNB : (Work.BG.NB v j).card = 4 := by
    rw [← Work.BG.tc_card_eq_nb_card v h1 h2 h3 h4 j]; exact hj
  obtain ⟨a, ha⟩ := Finset.card_pos.mp
    (show 0 < (Work.BG.NB v j).card by rw [hNB]; norm_num)
  have hcol : ∀ i ∈ Work.BG.Supp v j, (Work.BG.ColF v i).card = 3 :=
    fun i hi => fullColCardSelf v h1 hj hi
  have hdeg : ∀ k ∈ Work.BG.NB v j,
      ((Work.BG.Supp v j).filter (fun i => k ∈ Work.BG.ColF v i)).card = 2 :=
    fun k hk => nbDegSelf v h1 h2 h4 hk
  have hjmem : ∀ i ∈ Work.BG.Supp v j, j ∈ Work.BG.ColF v i := by
    intro i hi
    rw [Work.BG.mem_ColF]
    rw [Work.BG.mem_Supp] at hi
    exact hi
  let t : ι → Finset J := fun i => (Work.BG.ColF v i).erase j
  have ht2 : ∀ i ∈ Work.BG.Supp v j, (t i).card = 2 := by
    intro i hi
    show ((Work.BG.ColF v i).erase j).card = 2
    rw [Finset.card_erase_of_mem (hjmem i hi), hcol i hi]
  have htsub : ∀ i ∈ Work.BG.Supp v j, t i ⊆ Work.BG.NB v j := by
    intro i hi k hk
    have hk' : k ∈ (Work.BG.ColF v i).erase j := hk
    rw [Finset.mem_erase] at hk'
    obtain ⟨hkj, hkcol⟩ := hk'
    rw [Work.BG.NB, Finset.mem_filter]
    refine ⟨Finset.mem_univ k, hkj, ?_⟩
    refine ⟨i, ?_⟩
    rw [Finset.mem_inter]
    exact ⟨hi, by rw [Work.BG.mem_Supp, ← Work.BG.mem_ColF]; exact hkcol⟩
  have hinj : ∀ i ∈ Work.BG.Supp v j, ∀ i' ∈ Work.BG.Supp v j, t i = t i' → i = i' := by
    intro i hi i' hi' heq
    by_contra hne
    refine Work.BG.no_repeat v h1 h2 h4 hne ?_ (hcol i hi)
    calc Work.BG.ColF v i = insert j (t i) := (Finset.insert_erase (hjmem i hi)).symm
      _ = insert j (t i') := by rw [heq]
      _ = Work.BG.ColF v i' := Finset.insert_erase (hjmem i' hi')
  have hdeg' : ∀ k ∈ Work.BG.NB v j,
      ((Work.BG.Supp v j).filter (fun i => k ∈ t i)).card = 2 := by
    intro k hk
    have hkj : k ≠ j := (Finset.mem_filter.mp hk).2.1
    have hset : (Work.BG.Supp v j).filter (fun i => k ∈ t i)
        = (Work.BG.Supp v j).filter (fun i => k ∈ Work.BG.ColF v i) := by
      refine Finset.filter_congr ?_
      intro i _
      constructor
      · intro h
        have h' : k ∈ (Work.BG.ColF v i).erase j := h
        exact (Finset.mem_erase.mp h').2
      · intro h
        exact show k ∈ (Work.BG.ColF v i).erase j from
          Finset.mem_erase.mpr ⟨hkj, h⟩
    rw [hset]
    exact hdeg k hk
  obtain ⟨b, c, d, p, q, r, s, hbc, hcd, hda, hac, hbd, hS, htp, htq, htr, hts⟩ :=
    c4PairsSelf (Work.BG.Supp v j) (Work.BG.NB v j) t a (h1 j).1 hNB ha ht2 htsub hinj hdeg'
  have hpS : p ∈ Work.BG.Supp v j := by rw [hS]; simp
  have hqS : q ∈ Work.BG.Supp v j := by rw [hS]; simp
  have hrS : r ∈ Work.BG.Supp v j := by rw [hS]; simp
  have hsS : s ∈ Work.BG.Supp v j := by rw [hS]; simp
  have hab : a ≠ b := by
    intro h
    have h2 : (t p).card = 2 := ht2 p hpS
    rw [htp, h] at h2
    exact absurd h2 (by simp)
  have hp_col : Work.BG.ColF v p = {j, a, b} := by
    rw [← Finset.insert_erase (hjmem p hpS)]
    show insert j (t p) = {j, a, b}
    rw [htp]
  have hq_col : Work.BG.ColF v q = {j, b, c} := by
    rw [← Finset.insert_erase (hjmem q hqS)]
    show insert j (t q) = {j, b, c}
    rw [htq]
  have hr_col : Work.BG.ColF v r = {j, c, d} := by
    rw [← Finset.insert_erase (hjmem r hrS)]
    show insert j (t r) = {j, c, d}
    rw [htr]
  have hs_col : Work.BG.ColF v s = {j, d, a} := by
    rw [← Finset.insert_erase (hjmem s hsS)]
    show insert j (t s) = {j, d, a}
    rw [hts]
  exact ⟨a, b, c, d, p, q, r, s, hp_col, hq_col, hr_col, hs_col, hS, hab, hbc, hcd, hda⟩

/-- **`C4Data` exists for a full row** (the statement of `Work.BG.c4_exists`, proved here without
`sorry`). -/
theorem c4ExistsSelf {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]
    (v : J → ι → ℤ)
    (h1 : ∀ j, (Work.BG.Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h2 : ∀ j k, j ≠ k → ∑ i, v j i * v k i = 0)
    (h3 : ∀ i, (Work.BG.ColF v i).card ∈ ({0,1,3} : Finset ℕ))
    (h4 : ∀ n : J → ℤ, (∃ j, Odd (n j)) → ∃ i, Odd (∑ j, n j * v j i))
    (j : J) (hj : Work.BG.Full v j) :
    ∃ a b c d : J, ∃ p q r s u x y z : ι,
      Work.BG.C4Data v j a b c d p q r s u x y z := by
  obtain ⟨a, b, c, d, p, q, r, s, hp, hq, hr, hs, hS, hab, hbc, hcd, hda⟩ :=
    c4CoreSelf v h1 h2 h3 h4 hj
  obtain ⟨u, y, z, x, hAB, hup, hBC, hyq, hCD, hzr, hDA, hxs⟩ :=
    c4SecondSelf v h1 h2 h4 hp hq hr hs hab hbc hcd hda
  have hpS : p ∈ Work.BG.Supp v j := by rw [hS]; simp
  have hqS : q ∈ Work.BG.Supp v j := by rw [hS]; simp
  have hrS : r ∈ Work.BG.Supp v j := by rw [hS]; simp
  have hsS : s ∈ Work.BG.Supp v j := by rw [hS]; simp
  exact ⟨a, b, c, d, p, q, r, s, u, x, y, z,
    { hp := hp, hq := hq, hr := hr, hs := hs
      hp3 := fullColCardSelf v h1 hj hpS, hq3 := fullColCardSelf v h1 hj hqS
      hr3 := fullColCardSelf v h1 hj hrS, hs3 := fullColCardSelf v h1 hj hsS
      hS := hS
      hAB := hAB, hBC := hBC, hCD := hCD, hDA := hDA
      hup := hup, hyq := hyq, hzr := hzr, hxs := hxs }⟩

/-! ## COMB413 -/

/-- The "COMB413" combinatorial lemma of Bender--Glauberman (J. Algebra 70 (1981), p. 213),
`Work.GW2.C23.Comb413Prop`, proved here without relying on the still-`sorry`-carrying
`Work.BG.c4_exists`. -/
theorem comb413Self : Work.GW2.C23.Comb413Prop := by
  intro ι J _ _ _ v h1 h2 h3 h4 h5
  classical
  -- **Step 1**: no row is full.
  have nofull : ∀ j : J, ¬ Work.BG.Full v j := by
    intro j hj
    obtain ⟨a, b, c, d, p, q, r, s, u, x, y, z, hD⟩ := c4ExistsSelf v h1 h2 h3 h4 j hj
    by_cases hux : u = x
    · exact Work.BG.caseQ_false v h1 h2 h3 h4 hD hux
    · by_cases huy : u = y
      · exact Work.BG.caseQ_false v h1 h2 h3 h4 (Work.BG.C4Data.rotate1 v hD) huy.symm
      · by_cases hyz : y = z
        · exact Work.BG.caseQ_false v h1 h2 h3 h4 (Work.BG.C4Data.rotate2 v hD) hyz.symm
        · by_cases hzx : z = x
          · exact Work.BG.caseQ_false v h1 h2 h3 h4 (Work.BG.C4Data.rotate3 v hD) hzx.symm
          · exact Work.BG.caseP_false v h1 h2 h3 h4 hD hux huy hyz hzx
  -- **Step 2**: two rows share a coordinate, so we get a triple column.
  obtain ⟨j0, k0, i0, hjk, hj0i, hk0i⟩ := h5
  have hcol3 : (Work.BG.ColF v i0).card = 3 := by
    have hmemj : j0 ∈ Work.BG.ColF v i0 := (Work.BG.mem_ColF v j0 i0).mpr hj0i
    have hmemk : k0 ∈ Work.BG.ColF v i0 := (Work.BG.mem_ColF v k0 i0).mpr hk0i
    have h2le : 2 ≤ (Work.BG.ColF v i0).card := by
      have hsub : ({j0, k0} : Finset J) ⊆ Work.BG.ColF v i0 := by
        intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact hmemj
        · rw [Finset.mem_singleton] at ht
          subst ht
          exact hmemk
      have hle := Finset.card_le_card hsub
      rwa [Finset.card_pair hjk] at hle
    have hc := h3 i0
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with hc | hc | hc
    · rw [show (Work.BG.ColF v i0).card = 0 from hc] at h2le
      exact absurd h2le (by decide)
    · rw [show (Work.BG.ColF v i0).card = 1 from hc] at h2le
      exact absurd h2le (by decide)
    · exact show (Work.BG.ColF v i0).card = 3 from hc
  obtain ⟨j₁, j₂, j₃, hj₁₂, hj₁₃, hj₂₃, hEq⟩ := Finset.card_eq_three.mp hcol3
  refine ⟨j₁, j₂, j₃, hj₁₂, hj₁₃, hj₂₃, ⟨i0, ?_⟩, ?_⟩
  · intro j
    rw [← Work.BG.mem_ColF, hEq]
    simp
  · -- every row has a singleton column
    have hsing : ∀ j ∈ ({j₁, j₂, j₃} : Finset J),
        ∃ i : ι, v j i ≠ 0 ∧ (Work.BG.ColF v i).card = 1 := by
      intro j hj
      obtain ⟨i, hi, hc⟩ := Work.BG.exists_singleton_col v h1 h3 j (nofull j)
      exact ⟨i, (Work.BG.mem_Supp v j i).mp hi, hc⟩
    obtain ⟨p₁, hp₁, hp₁c⟩ := hsing j₁ (by simp)
    obtain ⟨p₂, hp₂, hp₂c⟩ := hsing j₂ (by simp)
    obtain ⟨p₃, hp₃, hp₃c⟩ := hsing j₃ (by simp)
    refine ⟨p₁, p₂, p₃, ?_, ?_, ?_⟩ <;> intro j
    · rw [← Work.BG.mem_ColF]
      have hmem : j₁ ∈ Work.BG.ColF v p₁ := by rw [Work.BG.mem_ColF]; exact hp₁
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hp₁c
      have hw' : Work.BG.ColF v p₁ = {j₁} := by
        rw [hw] at hmem
        rw [Finset.mem_singleton] at hmem
        rw [hw, hmem]
      rw [hw', Finset.mem_singleton]
    · rw [← Work.BG.mem_ColF]
      have hmem : j₂ ∈ Work.BG.ColF v p₂ := by rw [Work.BG.mem_ColF]; exact hp₂
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hp₂c
      have hw' : Work.BG.ColF v p₂ = {j₂} := by
        rw [hw] at hmem
        rw [Finset.mem_singleton] at hmem
        rw [hw, hmem]
      rw [hw', Finset.mem_singleton]
    · rw [← Work.BG.mem_ColF]
      have hmem : j₃ ∈ Work.BG.ColF v p₃ := by rw [Work.BG.mem_ColF]; exact hp₃
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hp₃c
      have hw' : Work.BG.ColF v p₃ = {j₃} := by
        rw [hw] at hmem
        rw [Finset.mem_singleton] at hmem
        rw [hw, hmem]
      rw [hw', Finset.mem_singleton]

end Work.BG.caseBC
