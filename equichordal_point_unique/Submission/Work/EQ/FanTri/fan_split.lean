import Mathlib
import Submission.Work.EQ.FanTri.Base
import Submission.Work.EQ.FanTri.fan_split_defs
import Submission.Work.EQ.FanTri.decomp_spec
import Submission.Work.EQ.FanTri.VisU_asm
import Submission.Work.EQ.FanTri.asm_split
import Submission.Work.EQ.FanTri.fVis_eq_VisU
import Submission.Work.EQ.FanTri.dec_counts
import Submission.Work.EQ.charValDefs

namespace Work.EQ.FanTri

open Work.EQ
open Classical
open Filter

noncomputable section

/-! ## Auxiliary combinatorial lemmas -/

/-- Infinitely many pigeons in finitely many pigeonholes. -/
theorem exists_const_subseq_of_finite {T : Type*} [Finite T] (f : ℕ → T) :
    ∃ (t : T) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ k, f (φ k) = t := by
  obtain ⟨t, ht⟩ := Finite.exists_infinite_fiber f
  have hinf : (f ⁻¹' {t}).Infinite := Set.infinite_coe_iff.mp ht
  have hne : ∀ N, ∃ n > N, f n = t := by
    intro N
    obtain ⟨n, hn, hlt⟩ := hinf.exists_gt N
    exact ⟨n, hlt, by simpa using hn⟩
  obtain ⟨φ, hφ, hφt⟩ := Nat.exists_strictMono_subsequence hne
  exact ⟨t, φ, hφ, hφt⟩

/-- Diagonal/greedy step: from an infinite set of indices, make each of finitely many sequences
either constant or eventually large. -/
theorem gap_split_core : ∀ (r : ℕ) (g : Fin r → ℕ → ℕ) (S : Set ℕ), S.Infinite →
    ∃ T : Set ℕ, T ⊆ S ∧ T.Infinite ∧
      ∀ i : Fin r, (∃ c, ∀ n ∈ T, g i n = c) ∨ (∀ B, (T ∩ {n | g i n < B}).Finite) := by
  intro r
  induction r with
  | zero =>
      intro g S hS
      exact ⟨S, subset_rfl, hS, by intro i; exact i.elim0⟩
  | succ r ih =>
      intro g S hS
      by_cases hA : ∀ B, (S ∩ {n | g 0 n < B}).Finite
      · obtain ⟨T, hTS, hTinf, hT⟩ := ih (fun i : Fin r => g i.succ) S hS
        refine ⟨T, hTS, hTinf, ?_⟩
        intro i
        refine Fin.cases ?_ ?_ i
        · exact Or.inr (fun B => (hA B).subset (fun n hn => ⟨hTS hn.1, hn.2⟩))
        · intro j; exact hT j
      · rw [not_forall] at hA
        obtain ⟨B, hB⟩ := hA
        rw [Set.not_finite] at hB
        have hsome : ∃ c, (S ∩ {n | g 0 n = c}).Infinite := by
          by_contra hc
          have hc' : ∀ c, (S ∩ {n | g 0 n = c}).Finite := by
            intro c
            by_contra hcf
            exact hc ⟨c, Set.not_finite.mp hcf⟩
          have hsub : S ∩ {n | g 0 n < B} ⊆
              ⋃ c ∈ (Finset.range B : Set ℕ), (S ∩ {n | g 0 n = c}) := by
            intro n hn
            simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hn
            exact Set.mem_iUnion₂.mpr ⟨g 0 n, by rw [Finset.mem_coe, Finset.mem_range]; exact hn.2,
              ⟨hn.1, rfl⟩⟩
          have hfin : (⋃ c ∈ (Finset.range B : Set ℕ), (S ∩ {n | g 0 n = c})).Finite :=
            Set.Finite.biUnion (Finset.finite_toSet _) (fun c _ => hc' c)
          exact hB (hfin.subset hsub)
        obtain ⟨c, hc⟩ := hsome
        obtain ⟨T, hTS', hTinf, hT⟩ :=
          ih (fun i : Fin r => g i.succ) (S ∩ {n | g 0 n = c}) hc
        refine ⟨T, fun n hn => (hTS' hn).1, hTinf, ?_⟩
        intro i
        refine Fin.cases ?_ ?_ i
        · refine Or.inl ⟨c, fun n hn => ?_⟩
          exact (hTS' hn).2
        · intro j; exact hT j

/-- For finitely many sequences `g₀,…,g_{r-1} : ℕ → ℕ` there is a strictly monotone `φ` such that
each `g i ∘ φ` is either constant or tends to `∞`. -/
theorem exists_subseq_gap_split (r : ℕ) (g : Fin r → ℕ → ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i : Fin r,
      ((∃ c : ℕ, ∀ k, g i (φ k) = c) ∨
        Filter.Tendsto (fun k => g i (φ k)) Filter.atTop Filter.atTop) := by
  obtain ⟨T, -, hTinf, hT⟩ := gap_split_core r g Set.univ Set.infinite_univ
  obtain ⟨φ, hφ, hφT⟩ := Nat.exists_strictMono_subsequence (fun N => by
    obtain ⟨n, hnT, hNn⟩ := hTinf.exists_gt N
    exact ⟨n, hNn, hnT⟩)
  refine ⟨φ, hφ, fun i => ?_⟩
  rcases hT i with ⟨c, hc⟩ | hfin
  · exact Or.inl ⟨c, fun k => hc (φ k) (hφT k)⟩
  · refine Or.inr ?_
    rw [Filter.tendsto_atTop_atTop]
    intro B
    refine ⟨(hfin B).toFinset.sup id + 1, fun k hk => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have hmem : φ k ∈ (hfin B).toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨hφT k, hlt⟩
    have hle : φ k ≤ (hfin B).toFinset.sup id := Finset.le_sup (f := id) hmem
    have hk' : k ≤ φ k := hφ.id_le k
    omega

/-- Lists of length `≤ N` whose entries have length `≤ K` are finitely many. -/
lemma finite_bounded_trips (N K : ℕ) :
    {p : List (List Bool) | p.length ≤ N ∧ ∀ τ ∈ p, τ.length ≤ K}.Finite := by
  induction N with
  | zero =>
      have h : {p : List (List Bool) | p.length ≤ 0 ∧ ∀ τ ∈ p, τ.length ≤ K} = {[]} := by
        ext p; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨h1, h2⟩; exact List.length_eq_zero_iff.mp (by omega)
        · rintro rfl; simp
      rw [h]; exact Set.finite_singleton _
  | succ N ih =>
      have hsub : {p : List (List Bool) | p.length ≤ N + 1 ∧ ∀ τ ∈ p, τ.length ≤ K} ⊆
          {[]} ∪ ⋃ τ ∈ {τ : List Bool | τ.length ≤ K},
              (fun q : List (List Bool) => τ :: q) ''
                {q : List (List Bool) | q.length ≤ N ∧ ∀ τ' ∈ q, τ'.length ≤ K} := by
        intro p hp
        obtain ⟨hp1, hp2⟩ := hp
        cases p with
        | nil => exact Or.inl rfl
        | cons τ q =>
            right
            have hqlen : q.length ≤ N := by
              simp only [List.length_cons] at hp1
              omega
            exact Set.mem_iUnion₂.mpr ⟨τ, hp2 τ (by simp), q,
              ⟨hqlen, fun τ' hτ' => hp2 τ' (by simp [hτ'])⟩, rfl⟩
      refine (Set.finite_singleton _ |>.union ?_).subset hsub
      refine Set.Finite.biUnion (List.finite_length_le Bool K) (fun τ _ => ?_)
      exact ih.image _

/-- Two lists of the same length which agree from position `n` on have equal tails. -/
lemma drop_eq_of_getElem?_eq {l₁ l₂ : List ℕ} {n : ℕ} (hlen : l₁.length = l₂.length)
    (h : ∀ i, n ≤ i → l₁[i]? = l₂[i]?) : l₁.drop n = l₂.drop n := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_drop, List.getElem?_drop]
  exact h (n + i) (Nat.le_add_right n i)

lemma stAux_eq_wstate (u : List Bool) : stAux u 0 = wstate u u.length :=
  (wstate_of_le (le_refl _)).symm

/-- A word assembled from closed trips and gaps returns to state `0`. -/
lemma wstate_asm_zero (L : List ℕ) (σ' : List (List Bool)) (hlen : L.length = σ'.length + 1)
    (hcl : ∀ τ ∈ σ', wstate τ τ.length = 0) :
    wstate (asm L σ') (asm L σ').length = 0 := by
  induction σ' generalizing L with
  | nil =>
      obtain ⟨g, rfl⟩ : ∃ g, L = [g] := List.length_eq_one_iff.mp (by simpa using hlen)
      simp only [asm]
      exact wstate_replicate_true g _
  | cons τ ts ih =>
      cases L with
      | nil => simp at hlen
      | cons g gs =>
          have hlen' : gs.length = ts.length + 1 := by simpa using hlen
          have hτ : wstate τ τ.length = 0 := hcl τ (by simp)
          have hcl' : ∀ τ' ∈ ts, wstate τ' τ'.length = 0 := fun τ' h => hcl τ' (by simp [h])
          have hq : wstate (asm gs ts) (asm gs ts).length = 0 := ih gs hlen' hcl'
          simp only [asm]
          rw [List.length_append]
          rw [wstate_append, List.take_of_length_le (le_refl _)]
          have hp : stAux (List.replicate g true ++ τ) 0 = 0 := by
            rw [stAux_append, stAux_replicate_true, Nat.zero_sub, stAux_eq_wstate]
            exact hτ
          rw [hp, stAux_eq_wstate]
          exact hq

/-! ## The combinatorial core -/

/-- The word-level form of `fan_split`: a subsequence of `u` is either constant or splits as
`C k ++ true^{s k} ++ E` with `s k → ∞` and `C k` returning to `0`. -/
theorem fan_split_aux (u : ℕ → List Bool) (N : ℕ) (hN : ∀ k, VisU (u k) ≤ N) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ v : List Bool, ∀ k, u (φ k) = v) ∨
       ∃ (E : List Bool) (C : ℕ → List Bool) (s : ℕ → ℕ),
         Filter.Tendsto s Filter.atTop Filter.atTop ∧
         (∀ k, u (φ k) = C k ++ List.replicate (s k) true ++ E) ∧
         (∀ k, stAux (C k) 0 = 0)) := by
  classical
  have hspec : ∀ k, DecSpec (u k) (decomp (u k)).1 (decomp (u k)).2 := fun k => decomp_spec (u k)
  have hcount : ∀ k, ((decomp (u k)).2).length ≤ VisU (u k) ∧
      (((decomp (u k)).2).map List.length).sum ≤ 2 * VisU (u k) :=
    fun k => dec_counts (u k) (decomp (u k)).1 (decomp (u k)).2 (hspec k)
  have hσlen : ∀ k, ((decomp (u k)).2).length ≤ N := fun k => le_trans (hcount k).1 (hN k)
  have hσsum : ∀ k, (((decomp (u k)).2).map List.length).sum ≤ 2 * N := fun k => by
    have h1 := (hcount k).2; have h2 := hN k; omega
  have hfin : {p : List (List Bool) | p.length ≤ N ∧ (p.map List.length).sum ≤ 2 * N}.Finite := by
    refine (finite_bounded_trips N (2 * N)).subset ?_
    rintro p ⟨h1, h2⟩
    refine ⟨h1, fun τ hτ => ?_⟩
    have := List.le_sum_of_mem (xs := p.map List.length) (List.mem_map.mpr ⟨τ, hτ, rfl⟩)
    omega
  haveI : Finite {p : List (List Bool) // p.length ≤ N ∧ (p.map List.length).sum ≤ 2 * N} :=
    hfin.to_subtype
  obtain ⟨t0, ψ₁, hψ₁, hσc⟩ := exists_const_subseq_of_finite
    (fun k => (⟨(decomp (u k)).2, hσlen k, hσsum k⟩ :
      {p : List (List Bool) // p.length ≤ N ∧ (p.map List.length).sum ≤ 2 * N}))
  have hσfix : ∀ k, (decomp (u (ψ₁ k))).2 = t0.val := fun k => congrArg Subtype.val (hσc k)
  let m : ℕ := t0.val.length
  let g : Fin (m + 1) → ℕ → ℕ := fun j k => (decomp (u (ψ₁ k))).1.getD j.val 0
  obtain ⟨ψ₂, hψ₂, hgap⟩ := exists_subseq_gap_split (m + 1) g
  let φ : ℕ → ℕ := fun k => ψ₁ (ψ₂ k)
  have hφmono : StrictMono φ := hψ₁.comp hψ₂
  have hσ_φ : ∀ k, (decomp (u (φ k))).2 = t0.val := fun k => hσfix (ψ₂ k)
  have halen : ∀ k, (decomp (u (φ k))).1.length = m + 1 := by
    intro k
    have h := (hspec (φ k)).len
    rw [hσ_φ k] at h
    exact h
  by_cases hall : ∀ j : Fin (m + 1), ∃ c : ℕ, ∀ k, g j (ψ₂ k) = c
  · refine ⟨φ, hφmono, Or.inl ⟨asm (decomp (u (φ 0))).1 t0.val, fun k => ?_⟩⟩
    have hafix : ∀ i, (decomp (u (φ i))).1 = (decomp (u (φ 0))).1 := by
      intro i
      apply List.ext_getElem
      · rw [halen i, halen 0]
      · intro j hj1 hj2
        have hj : j < m + 1 := by rw [← halen i]; exact hj1
        have hc := (hall ⟨j, hj⟩).choose_spec
        calc (decomp (u (φ i))).1[j]
            = (decomp (u (φ i))).1.getD j 0 := (List.getD_eq_getElem _ 0 hj1).symm
          _ = g ⟨j, hj⟩ (ψ₂ i) := rfl
          _ = (hall ⟨j, hj⟩).choose := hc i
          _ = g ⟨j, hj⟩ (ψ₂ 0) := (hc 0).symm
          _ = (decomp (u (φ 0))).1.getD j 0 := rfl
          _ = (decomp (u (φ 0))).1[j] := List.getD_eq_getElem _ 0 hj2
    rw [(hspec (φ k)).concat, hσ_φ k, hafix k]
  · rw [not_forall] at hall
    obtain ⟨j0, hj0⟩ := hall
    have hD_or : ∀ j : Fin (m + 1),
        Filter.Tendsto (fun k => g j (ψ₂ k)) Filter.atTop Filter.atTop ∨
        ∃ c, ∀ k, g j (ψ₂ k) = c := by
      intro j
      rcases hgap j with h | h
      · exact Or.inr h
      · exact Or.inl h
    have hD_j0 : Filter.Tendsto (fun k => g j0 (ψ₂ k)) Filter.atTop Filter.atTop := by
      rcases hD_or j0 with h | h
      · exact h
      · exact absurd h hj0
    let J : Finset (Fin (m + 1)) :=
      Finset.univ.filter (fun j =>
        Filter.Tendsto (fun k => g j (ψ₂ k)) Filter.atTop Filter.atTop)
    have hJne : J.Nonempty := ⟨j0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hD_j0⟩⟩
    let i0 : Fin (m + 1) := J.max' hJne
    have hi0D : Filter.Tendsto (fun k => g i0 (ψ₂ k)) Filter.atTop Filter.atTop :=
      (Finset.mem_filter.mp (J.max'_mem hJne)).2
    have hiL : ∀ i, i0.val < (decomp (u (φ i))).1.length := fun i => by
      rw [halen i]; exact i0.isLt
    have hm0 : ∀ i, m < (decomp (u (φ i))).1.length := fun i => by
      rw [halen i]; omega
    have hconst_above : ∀ j : Fin (m + 1), i0.val < j.val →
        ∃ c, ∀ k, g j (ψ₂ k) = c := by
      intro j hj
      rcases hD_or j with hD | hc
      · exfalso
        have hmem : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hD⟩
        have hle : j ≤ i0 := Finset.le_max' J j hmem
        simp only [Fin.le_def] at hle
        omega
      · exact hc
    let s : ℕ → ℕ := fun k => g i0 (ψ₂ k)
    have hsT : Filter.Tendsto s Filter.atTop Filter.atTop := hi0D
    let E : List Bool := asm (0 :: (decomp (u (φ 0))).1.drop (i0.val + 1)) (t0.val.drop i0.val)
    let C : ℕ → List Bool := fun i =>
      asm ((decomp (u (φ i))).1.take i0.val ++ [0]) (t0.val.take i0.val)
    have hs_eval : ∀ i, (decomp (u (φ i))).1.getD i0.val 0 = s i := by
      intro i
      show (decomp (u (φ i))).1.getD i0.val 0 = g i0 (ψ₂ i)
      rfl
    have hdrop : ∀ i, (decomp (u (φ i))).1.drop (i0.val + 1)
        = (decomp (u (φ 0))).1.drop (i0.val + 1) := by
      intro i
      apply drop_eq_of_getElem?_eq
      · rw [halen i, halen 0]
      · intro j hj
        by_cases hjlt : j < m + 1
        · have h1 : j < (decomp (u (φ i))).1.length := by rw [halen i]; exact hjlt
          have h2 : j < (decomp (u (φ 0))).1.length := by rw [halen 0]; exact hjlt
          rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2]
          congr 1
          obtain ⟨c, hc⟩ := hconst_above ⟨j, hjlt⟩ (by show i0.val < j; omega)
          calc (decomp (u (φ i))).1[j]
              = (decomp (u (φ i))).1.getD j 0 := (List.getD_eq_getElem _ 0 h1).symm
            _ = g ⟨j, hjlt⟩ (ψ₂ i) := rfl
            _ = c := hc i
            _ = g ⟨j, hjlt⟩ (ψ₂ 0) := (hc 0).symm
            _ = (decomp (u (φ 0))).1.getD j 0 := rfl
            _ = (decomp (u (φ 0))).1[j] := List.getD_eq_getElem _ 0 h2
        · rw [List.getElem?_eq_none (by rw [halen i]; omega),
              List.getElem?_eq_none (by rw [halen 0]; omega)]
    have hdecomp : ∀ i, u (φ i) = C i ++ List.replicate (s i) true ++ E := by
      intro i
      have hsplit := asm_split (decomp (u (φ i))).1 t0.val i0.val (halen i) (hiL i)
      rw [(hspec (φ i)).concat, hσ_φ i, hsplit]
      have hget : (decomp (u (φ i))).1.get ⟨i0.val, hiL i⟩ = s i :=
        (List.get_eq_getElem.trans (List.getD_eq_getElem _ 0 (hiL i)).symm).trans (hs_eval i)
      rw [hget, hdrop i]
    have hC0 : ∀ i, 1 ≤ s i → stAux (C i) 0 = 0 := by
      intro i hs
      rw [stAux_eq_wstate]
      have h1l : (List.take i0.val (decomp (u (φ i))).1).length = i0.val := by
        simp only [List.length_take, halen i, min_eq_left (le_of_lt i0.isLt)]
      have h2l : (List.take i0.val t0.val).length = i0.val := by
        simp only [List.length_take,
          min_eq_left (show i0.val ≤ t0.val.length from Nat.lt_succ_iff.mp i0.isLt)]
      have hlenC : (List.take i0.val (decomp (u (φ i))).1 ++ [0]).length
          = (List.take i0.val t0.val).length + 1 := by
        simp only [List.length_append, List.length_singleton, h1l, h2l]
      refine wstate_asm_zero (List.take i0.val (decomp (u (φ i))).1 ++ [0])
        (List.take i0.val t0.val) hlenC ?hcl
      · intro τ hτ
        rw [List.mem_take_iff_getElem] at hτ
        obtain ⟨j, hmin, hjeq⟩ := hτ
        have hj_i : j < i0.val := lt_of_lt_of_le hmin (min_le_left _ _)
        have hj_m : j < t0.val.length := lt_of_lt_of_le hmin (min_le_right _ _)
        by_cases hjm : j + 1 < m
        · have h1 : ((decomp (u (φ i))).2)[j]? = some (t0.val[j]'hj_m) := by
            rw [hσ_φ i, List.getElem?_eq_getElem hj_m]
          have h2 : j + 1 < ((decomp (u (φ i))).2).length := by rw [hσ_φ i]; exact hjm
          have hthis := (hspec (φ i)).closed j (t0.val[j]'hj_m) h1 h2
          simpa [hjeq] using hthis
        · have hj1 : j + 1 = m := by omega
          have hi0m : i0.val = m := by omega
          have h1 : ((decomp (u (φ i))).2)[j]? = some (t0.val[j]'hj_m) := by
            rw [hσ_φ i, List.getElem?_eq_getElem hj_m]
          have hlt : m < (decomp (u (φ i))).1.length := hm0 i
          have h2 : ((decomp (u (φ i))).1)[j + 1]? = some (s i) := by
            rw [hj1, List.getElem?_eq_getElem hlt]
            congr 1
            rw [← List.getD_eq_getElem _ 0 hlt, ← hi0m]
          have h3 : j + 1 = ((decomp (u (φ i))).2).length := by rw [hσ_φ i]; exact hj1
          rcases (hspec (φ i)).last j (t0.val[j]'hj_m) (s i) h1 h2 h3 with h | h
          · simpa [hjeq] using h
          · omega
    obtain ⟨K, hK⟩ : ∃ K, ∀ k, 1 ≤ s (k + K) := by
      have h := hsT
      rw [Filter.tendsto_atTop_atTop] at h
      obtain ⟨K, hK⟩ := h 1
      exact ⟨K, fun k => hK (k + K) (by omega)⟩
    refine ⟨fun k => φ (k + K), hφmono.comp (fun a b h => Nat.add_lt_add_right h K),
      Or.inr ⟨E, fun k => C (k + K), fun k => s (k + K), ?_, ?_, ?_⟩⟩
    · exact hsT.comp (Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩))
    · intro k; exact hdecomp (k + K)
    · intro k; exact hC0 (k + K) (hK k)

end

/-! ## The main theorem -/

/-- **Splitting a sequence of words with bounded walk visits** (CORRECTED: the suffix `C` is
allowed to depend on `k`, only the prefix `ε₀` is fixed).  Let `ε : ℕ → List Bool` be a sequence of
branch words whose walk visits to centres other than `A₁` are uniformly bounded,
`fVis (ε k) ≤ N` for all `k`.  Then some subsequence is either constant, or has the form
`ε₀ ++ trueˢᵏ ++ C k` with a fixed prefix `ε₀`, a diverging run `s k → ∞` of principal steps at `A₁`,
and returning suffixes `C k` (`stAux (C k).reverse 0 = 0`). -/
theorem fan_split (ε : ℕ → List Bool) (N : ℕ) (hN : ∀ k, Work.EQ.fVis (ε k) ≤ N) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ ε₀ : List Bool, ∀ k, ε (φ k) = ε₀) ∨
       ∃ (ε₀ : List Bool) (C : ℕ → List Bool) (s : ℕ → ℕ),
         Filter.Tendsto s Filter.atTop Filter.atTop ∧
         (∀ k, ε (φ k) = ε₀ ++ List.replicate (s k) true ++ C k) ∧
         (∀ k, Work.EQ.stAux (C k).reverse 0 = 0)) := by
  classical
  have hvis : ∀ k, VisU ((fun k => (ε k).reverse) k) ≤ N := fun k => by
    rw [← fVis_eq_VisU (ε k)]
    exact hN k
  obtain ⟨φ, hφ, hres⟩ := fan_split_aux (fun k => (ε k).reverse) N hvis
  refine ⟨φ, hφ, ?_⟩
  rcases hres with ⟨v, hv⟩ | ⟨E, C, s, hsT, hdec, hC0⟩
  · refine Or.inl ⟨v.reverse, fun k => ?_⟩
    have h := hv k
    rw [← h]
    simp
  · refine Or.inr ⟨E.reverse, fun k => (C k).reverse, s, hsT, fun k => ?_, fun k => ?_⟩
    · have h := congrArg List.reverse (hdec k)
      rw [List.reverse_append, List.reverse_append, List.reverse_reverse,
        List.reverse_replicate] at h
      rw [← List.append_assoc] at h
      exact h
    · rw [List.reverse_reverse]
      exact hC0 k

end Work.EQ.FanTri
