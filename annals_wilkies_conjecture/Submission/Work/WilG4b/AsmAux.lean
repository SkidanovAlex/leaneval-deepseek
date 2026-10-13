/-
  Area G4b: the main step of the final assembly of `G4_bdd_dx_proved`.

  For `n ≥ 1`, the exceptional set `badSet f s` of `G4_bdd_dx` is finite.  The proof is the
  contradiction argument of BNZ `lem:uniforly-bdd-Fx`:

  * `badSet f s` is `Ω`-definable, hence (being infinite) it contains an interval `(c,d)`;
  * definable choice (the frozen `G1_choice`) applied to the augmented choice set
    `StarSet f c d M` produces, for every threshold `M`, a definable curve `s ↦ γ (fun _ => s)`
    along which `|∂₀ f| > M (1 + n u)` while each `y`-partial is bounded by `u`;
  * the coordinate functions `s ↦ γ (fun _ => s) i` and the function `s ↦ f (s, γ s)` are
    definable, and `thrSet_mem_unif` + `thresh_measure_bound` bound the measure of the set of
    `s` on which they are `C¹` with `|deriv| > K`, while `nondiff_finite` bounds the
    non-`C¹` locus; choosing `M` large enough leaves a point `t` where the chain rule
    `∂₀ f = φ' - Σ ∂_j f · γ'_j` contradicts `M (1 + n u) < M/3 + u M/3`.
-/
import Mathlib
import Submission.Work.WilG4b.Basic
import Submission.Work.WilG4b.badSet_mem
import Submission.Work.WilG4b.StarSet_mem
import Submission.Work.WilG4b.starAt
import Submission.Work.WilG4b.starFibre_nonempty
import Submission.Work.WilG4b.projGraph_eq
import Submission.Work.WilG4b.projCoords_mem
import Submission.Work.WilG4b.xDeriv_eq
import Submission.Work.WilG4b.infinite_contains_Ioo
-- `nondiff_finite` is taken from our own module: `Submission/Work/WilG4b/nondiff_finite.lean`
-- and `Submission/Work/WilG4b/badSet_mem.lean` both declare `Work.WilG4b.derivGraph_mem`,
-- so the two cannot be imported together.
import Submission.Work.WilG4b.NondiffFiniteAux
import Submission.Work.WilG4b.thrSet_mem
import Submission.Work.WilG4b.thresh_measure_bound
import Submission.Work.WilG4b.HelpAux
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex
import Submission.Work.WilG1.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Classical MeasureTheory Filter
open scoped Topology

namespace Work.WilG4b

open WilkiesDesign WilkiesConjecture

/-- The main step: for `n ≥ 1` the exceptional set of `G4_bdd_dx` is finite.

This is BNZ's `lem:uniforly-bdd-Fx`, given the definable-choice hypothesis `hchoice`
(the frozen `G1_choice`). -/
theorem badSet_finite_of_one_le (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (hchoice : ∀ (F p q : ℕ), ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) (X : Set (Fin (p + q) → ℝ)), X ∈ S.Ω F D (p + q) →
        ∃ fch : (Fin p → ℝ) → (Fin q → ℝ),
          (∀ l : Fin p → ℝ, (∃ y, Fin.append l y ∈ X) → Fin.append l (fch l) ∈ X) ∧
          {z : Fin (p + q) → ℝ | ∀ j : Fin q,
              z (Fin.natAdd p j) = fch (fun i => z (Fin.castAdd q i)) j}
            ∈ S.Ω a (b.eval D) (p + q))
    {n F D : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (hf : graphOf f ∈ S.Ω F D (n + 1 + 1))
    (hI : ∀ z ∈ openCube (n + 1), f z ∈ Set.Ioo (0 : ℝ) 1)
    {s : Finset ℝ}
    (hs : ∀ x ∈ Set.Ioo (0 : ℝ) 1, x ∉ s → ∃ B : ℝ, ∀ y ∈ openCube n,
      Fin.cons x y ∈ interior {z | ContDiffAt ℝ 1 f z} →
        ∀ i : Fin n, |fderiv ℝ f (Fin.cons x y) (Pi.single i.succ 1)| ≤ B)
    (hn : 1 ≤ n) : (badSet f s).Finite := by
  classical
  by_contra hfin
  have hinf : (badSet f s).Infinite := hfin
  -- ## Step 1: `badSet` is `Ω`-definable, hence it contains an interval
  obtain ⟨Kb, pb, hb⟩ := badSet_mem S hder s F
  have hbΩ : badSet f s ∈ S.Ω (F + Kb) (pb.eval D) 1 := hb D f hf
  obtain ⟨c, d, hcdlt, hint⟩ := infinite_contains_Ioo S hcd hbΩ hinf
  have hmem01 : ∀ t : ℝ, c < t → t < d → t ∈ Set.Ioo (0 : ℝ) 1 ∧ t ∉ s := by
    intro t h1 h2
    have h := hint t h1 h2
    simp only [badSet, Set.mem_ofPred_eq] at h
    exact ⟨h.1, by simpa using h.2.1⟩
  -- ## Step 2: `StarSet` is `Ω`-definable with `M`-independent bounds, and definable choice
  obtain ⟨Ks, ps, hstar⟩ := StarSet_mem S hder F
  have hdim : n + 3 = 1 + (n + 2) := by omega
  have hSSmem : ∀ M : ℝ,
      (hdim ▸ StarSet f c d M) ∈ S.Ω (F + Ks) (ps.eval D) (1 + (n + 2)) :=
    fun M => Work.WilG5.omega_ndrec (S := S) hdim (hstar D f hf c d M)
  obtain ⟨a, b, hch⟩ := hchoice (F + Ks) 1 (n + 2)
  -- ## Step 3: format/degree data of the coordinate projections
  let DD : ℕ := ps.eval D
  have hproj : ∀ i : Fin (n + 2), ∃ (K : ℕ) (p : Polynomial ℕ),
      ∀ (X : Set (Fin (1 + (n + 2)) → ℝ)), X ∈ S.Ω a (b.eval DD) (1 + (n + 2)) →
        {y : Fin 2 → ℝ | ∃ x : Fin (1 + (n + 2)) → ℝ, x ∈ X ∧
            y = x ∘ (fun j : Fin 2 => if j = 0 then (0 : Fin (1 + (n + 2))) else Fin.natAdd 1 i)}
          ∈ S.Ω (a + K) (p.eval (b.eval DD)) 2 := by
    intro i
    obtain ⟨K, p, hp⟩ := projCoords_mem S
      (fun j : Fin 2 => if j = 0 then (0 : Fin (1 + (n + 2))) else Fin.natAdd 1 i)
    exact ⟨K, p, fun X hX => hp a (b.eval DD) X hX⟩
  choose Kc pc hpc using hproj
  -- ## Step 4: the threshold sets of the coordinate functions, with `M`-independent bounds
  have hthr0 : ∀ i : Fin (n + 1), ∃ (K : ℕ) (p : Polynomial ℕ), ∀ (G : ℝ → ℝ),
      graphOf (fun x : Fin 1 → ℝ => G (x 0))
        ∈ S.Ω (a + Kc (Fin.castSucc i)) ((pc (Fin.castSucc i)).eval (b.eval DD)) 2 →
      ∀ (t : ℝ), {x : Fin 1 → ℝ | x 0 ∈ thrSet G t}
        ∈ S.Ω ((a + Kc (Fin.castSucc i)) + K) (p.eval ((pc (Fin.castSucc i)).eval (b.eval DD))) 1 :=
    fun i => (thrSet_mem_unif S hder (a + Kc (Fin.castSucc i))).imp fun K hp =>
      hp.imp fun p hq G hG t => hq _ G hG t
  choose Kthr pthr hthr using hthr0
  let Fthr : (i : Fin (n + 1)) → ℕ := fun i => (a + Kc (Fin.castSucc i)) + Kthr i
  let Dthr : (i : Fin (n + 1)) → ℕ := fun i => (pthr i).eval ((pc (Fin.castSucc i)).eval (b.eval DD))
  let A₀ : (i : Fin (n + 1)) → ℕ := fun i => max (Fthr i) 25 + 1
  let D₀ : (i : Fin (n + 1)) → ℕ := fun i => Dthr i + 16
  -- the measure constants (independent of `M`)
  let Cc : (i : Fin (n + 1)) → ℝ := fun i =>
    (thresh_measure_bound S hcd (A₀ i) (Polynomial.C (D₀ i)) 0).choose
  have hCc0 : ∀ i : Fin (n + 1), 0 ≤ Cc i := fun i =>
    (thresh_measure_bound S hcd (A₀ i) (Polynomial.C (D₀ i)) 0).choose_spec.1
  have hCcb : ∀ i : Fin (n + 1), ∀ (K' a b : ℝ) (G : ℝ → ℝ) (A : Set ℝ), 0 < K' → a ≤ b →
      {x : Fin 1 → ℝ | x 0 ∈ A} ∈ S.Ω (A₀ i) (Polynomial.eval 0 (Polynomial.C (D₀ i))) 1 →
      (∀ t ∈ A, a ≤ G t) → (∀ t ∈ A, G t ≤ b) → (∀ t ∈ A, K' < |deriv G t|) →
      volume A ≤ ENNReal.ofReal (Cc i * (b - a) / K') := fun i =>
    (thresh_measure_bound S hcd (A₀ i) (Polynomial.C (D₀ i)) 0).choose_spec.2
  -- ## Step 5: the threshold `M`
  let R : ℝ := (∑ i : Fin (n + 1), Cc i) * (3 * (n : ℝ))
  have hdc : 0 < d - c := by linarith
  obtain ⟨M, hM⟩ := exists_gt (max 1 (R / (d - c) + 1))
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (le_trans (le_max_left _ _) hM.le)
  have hRlt : R / (d - c) < M := by
    have h2 : R / (d - c) + 1 < M :=
      lt_of_le_of_lt (le_max_right (1 : ℝ) (R / (d - c) + 1)) hM
    linarith
  have hRM : R / M < d - c := by
    rw [div_lt_iff₀ hMpos]
    have h2 : R < M * (d - c) := (div_lt_iff₀ hdc).mp hRlt
    nlinarith [h2]
  let K : ℝ := M / (3 * (n : ℝ))
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hKpos : 0 < K := by
    have h3 : (0 : ℝ) < 3 * (n : ℝ) := by linarith
    exact div_pos hMpos h3
  -- ## Step 6: definable choice at `M`
  obtain ⟨γ, hγchoice, hγgraph⟩ := hch DD (hdim ▸ StarSet f c d M) (hSSmem M)
  -- ## Step 7: the projected coordinate graphs are `Ω`-definable
  have hGgraph : ∀ i : Fin (n + 2),
      graphOf (fun x : Fin 1 → ℝ => γ (fun _ : Fin 1 => x 0) i)
        ∈ S.Ω (a + Kc i) ((pc i).eval (b.eval DD)) 2 := by
    intro i
    have h1 := hpc i {z : Fin (1 + (n + 2)) → ℝ | ∀ j : Fin (n + 2),
        z (Fin.natAdd 1 j) = γ (fun i => z (Fin.castAdd (n + 2) i)) j} hγgraph
    simp only [Set.mem_ofPred_eq] at h1
    rw [projGraph_eq γ i] at h1
    have hfun : (fun x : Fin 1 → ℝ => γ x i)
        = (fun x : Fin 1 → ℝ => γ (fun _ : Fin 1 => x 0) i) := by
      funext x
      rw [fin1_ext x]
    rwa [hfun] at h1
  -- ## Step 8: the choice point at every `x ∈ (c,d)` lies in `StarSet`
  have htail : ∀ {V : Fin (n + 3) → ℝ} {x : ℝ}, V 0 = x →
      (Fin.append (fun _ : Fin 1 => x) (Fin.tail V)) ∘ Fin.cast hdim = V := by
    intro V x hVx
    have h2 : Fin.append (fun _ : Fin 1 => x) (Fin.tail V)
        = Fin.cons (V 0) (Fin.tail V) ∘ Fin.cast (Nat.add_comm 1 (n + 2)) := by
      rw [Fin.append_left_eq_cons, show x = V 0 from hVx.symm]
    rw [h2, Fin.cons_self_tail]
    funext i
    simp only [Function.comp_apply]
    have hidx : Fin.cast (Nat.add_comm 1 (n + 2)) (Fin.cast hdim i) = i := Fin.ext rfl
    rw [hidx]
  have hmem_of : ∀ x : ℝ, c < x → x < d →
      (Fin.append (fun _ : Fin 1 => x) (γ (fun _ : Fin 1 => x))) ∘
        (fun i : Fin (n + 3) => (⟨i.1, by omega⟩ : Fin (1 + (n + 2)))) ∈ StarSet f c d M := by
    intro x h1 h2
    have hbadt : (fun _ : Fin 1 => x) ∈ badSet f s := hint x h1 h2
    obtain ⟨V, hV, hV0⟩ := starFibre_nonempty hn hs ⟨h1, h2⟩ hbadt
    have happ := htail (V := V) (x := x) hV0
    have hfib : Fin.append (fun _ : Fin 1 => x) (Fin.tail V) ∈ (hdim ▸ StarSet f c d M) := by
      rw [Work.WilG5.mem_ndrec hdim (StarSet f c d M)]
      show (Fin.append (fun _ : Fin 1 => x) (Fin.tail V)) ∘ Fin.cast hdim ∈ StarSet f c d M
      rw [happ]
      exact hV
    have hpt := hγchoice (fun _ : Fin 1 => x) ⟨Fin.tail V, hfib⟩
    have hfun : (Fin.append (fun _ : Fin 1 => x) (γ (fun _ : Fin 1 => x))) ∘
        (fun i : Fin (n + 3) => (⟨i.1, by omega⟩ : Fin (1 + (n + 2))))
        = (fun i : Fin (n + 3) => (Fin.append (fun _ : Fin 1 => x) (γ (fun _ : Fin 1 => x)))
            (Fin.cast hdim i)) := by
      funext i
      simp only [Function.comp_apply]
      congr 1
    rw [hfun]
    exact (Work.WilG5.mem_ndrec hdim (StarSet f c d M) _).mp hpt
  -- ## Step 9: unpacking `StarSet` at every point of the interval
  have hstar_data : ∀ x : ℝ, c < x → x < d →
      ∃ (y : Fin n → ℝ) (w u : ℝ), y ∈ openCube n ∧
        (∀ j : Fin n, y j = γ (fun _ : Fin 1 => x) (Fin.castAdd 2 j)) ∧
        w = γ (fun _ : Fin 1 => x) ⟨n, by omega⟩ ∧
        u = γ (fun _ : Fin 1 => x) ⟨n + 1, by omega⟩ ∧
        Fin.snoc (Fin.cons x y) w ∈ graphOf f ∧ 0 ≤ u ∧
        (∃ w₀ : ℝ, Fin.snoc (Fin.cons x y) w₀ ∈ derivGraph f 0 ∧
            M * (1 + n * u) < |w₀|) ∧
        (∀ j : Fin n, ∃ wj : ℝ, Fin.snoc (Fin.cons x y) wj ∈ derivGraph f j.succ ∧
            |wj| ≤ u) := by
    intro x h1 h2
    obtain ⟨y, w, u, -, hycube, hyj, hw, hu, hgraph, hu0, hw0ex, hwjex⟩ :=
      starAt (f := f) (γv := γ (fun _ : Fin 1 => x)) (hmem_of x h1 h2)
    exact ⟨y, w, u, hycube, hyj, hw, hu, hgraph, hu0, hw0ex, hwjex⟩
  have hrange : ∀ x : ℝ, c < x → x < d → ∀ i : Fin (n + 1),
      γ (fun _ : Fin 1 => x) (Fin.castSucc i) ∈ Set.Icc (0 : ℝ) 1 := by
    intro x h1 h2 i
    obtain ⟨y, w, u, hycube, hyj, hw, hu, hgraph, hu0, hw0ex, hwjex⟩ := hstar_data x h1 h2
    have hx01 := (hmem01 x h1 h2).1
    have hz : Fin.cons x y ∈ openCube (n + 1) := by
      intro k
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ k
      · simpa using hx01
      · simpa using hycube j
    have hwval : w = f (Fin.cons x y) := by
      have h := hgraph
      simp only [graphOf, Set.mem_ofPred_eq] at h
      rwa [Fin.snoc_last, Fin.init_snoc] at h
    have hwmem : w ∈ Set.Ioo (0 : ℝ) 1 := by rw [hwval]; exact hI _ hz
    obtain ⟨k, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
    · have hidx : (Fin.castSucc (Fin.castSucc k) : Fin (n + 2)) = Fin.castAdd 2 k := by
        apply Fin.ext; simp [Fin.castAdd, Fin.castSucc]
      rw [hidx, ← hyj k]
      exact ⟨(hycube k).1.le, (hycube k).2.le⟩
    · have hidx : (Fin.castSucc (Fin.last n) : Fin (n + 2)) = ⟨n, by omega⟩ := by
        apply Fin.ext; simp
      rw [hidx, ← hw]
      exact ⟨hwmem.1.le, hwmem.2.le⟩
  -- ## Step 10: the threshold sets are `Ω`-definable with the constants `A₀, D₀`
  have hA : ∀ i : Fin (n + 1),
      {x : Fin 1 → ℝ | x 0 ∈ {t : ℝ | t ∈ Set.Ioo c d ∧
          t ∈ thrSet (fun s => γ (fun _ : Fin 1 => s) (Fin.castSucc i)) K}}
        ∈ S.Ω (A₀ i) (Polynomial.eval 0 (Polynomial.C (D₀ i))) 1 := by
    intro i
    have h1 : {x : Fin 1 → ℝ | x 0 ∈ thrSet (fun s => γ (fun _ : Fin 1 => s) (Fin.castSucc i)) K}
        ∈ S.Ω (Fthr i) (Dthr i) 1 := hthr i _ (hGgraph (Fin.castSucc i)) K
    have h2 : {x : Fin 1 → ℝ | x 0 ∈ Set.Ioo c d} ∈ S.Ω 25 16 1 := ivl_mem S c d
    have h3 := S.inter (F := max (Fthr i) 25) (n := 1) (k := 2)
      (fun j : Fin 2 => if j = 0 then Dthr i else 16)
      (fun j : Fin 2 => if j = 0
        then {x : Fin 1 → ℝ | x 0 ∈ thrSet (fun s => γ (fun _ : Fin 1 => s) (Fin.castSucc i)) K}
        else {x : Fin 1 → ℝ | x 0 ∈ Set.Ioo c d})
      (by intro j
          fin_cases j
          · exact Work.WilG5.mem_mono h1 (max (Fthr i) 25) (Dthr i) (le_max_left _ _) le_rfl
          · exact Work.WilG5.mem_mono h2 (max (Fthr i) 25) 16 (le_max_right _ _) le_rfl)
    rw [Work.WilG1.Omega.iInter_fin_two] at h3
    have hset : ({x : Fin 1 → ℝ | x 0 ∈ thrSet (fun s => γ (fun _ : Fin 1 => s) (Fin.castSucc i)) K}
        ∩ {x : Fin 1 → ℝ | x 0 ∈ Set.Ioo c d})
        = {x : Fin 1 → ℝ | x 0 ∈ {t : ℝ | t ∈ Set.Ioo c d ∧
            t ∈ thrSet (fun s => γ (fun _ : Fin 1 => s) (Fin.castSucc i)) K}} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      tauto
    rw [hset] at h3
    have hD : (∑ j : Fin 2, (if j = 0 then Dthr i else 16)) = D₀ i := by
      rw [Fin.sum_univ_two]
      simp only [Fin.isValue, if_true, if_false]
      rfl
    rw [hD] at h3
    simpa using h3
  -- ## Step 11: the measure of the bad set
  have hNfin : ∀ i : Fin (n + 1),
      ({t : ℝ | ¬ ContDiffAt ℝ 1 (fun s => γ (fun _ : Fin 1 => s) (Fin.castSucc i)) t}).Finite :=
    fun i => Work.WilG4bF.nondiff_finite S hcd hder _ (hGgraph (Fin.castSucc i))
  let SB : (i : Fin (n + 1)) → Set ℝ := fun i =>
    {t : ℝ | t ∈ Set.Ioo c d ∧ K < |deriv (fun s => γ (fun _ : Fin 1 => s) (Fin.castSucc i)) t|}
  let SN : (i : Fin (n + 1)) → Set ℝ := fun i =>
    {t : ℝ | ¬ ContDiffAt ℝ 1 (fun s => γ (fun _ : Fin 1 => s) (Fin.castSucc i)) t}
  let BadB : Set ℝ := ⋃ i, SB i
  let BadN : Set ℝ := ⋃ i, SN i
  let Bad : Set ℝ := BadB ∪ BadN
  have hSBi : ∀ i : Fin (n + 1), volume (SB i) ≤ ENNReal.ofReal (Cc i / K) := by
    intro i
    have hb := hCcb i K 0 1 (fun s => γ (fun _ : Fin 1 => s) (Fin.castSucc i))
      {t : ℝ | t ∈ Set.Ioo c d ∧
        t ∈ thrSet (fun s => γ (fun _ : Fin 1 => s) (Fin.castSucc i)) K}
      hKpos (by norm_num) (hA i)
      (fun t ht => (hrange t ht.1.1 ht.1.2 i).1)
      (fun t ht => (hrange t ht.1.1 ht.1.2 i).2)
      (fun t ht => ht.2.2)
    have hb' : volume {t : ℝ | t ∈ Set.Ioo c d ∧
        t ∈ thrSet (fun s => γ (fun _ : Fin 1 => s) (Fin.castSucc i)) K}
        ≤ ENNReal.ofReal (Cc i / K) := by simpa using hb
    refine le_trans (measure_mono ?_)
      (le_trans (measure_union_le {t : ℝ | t ∈ Set.Ioo c d ∧
        t ∈ thrSet (fun s => γ (fun _ : Fin 1 => s) (Fin.castSucc i)) K} (SN i)) ?_)
    · intro t ht
      by_cases hc : ContDiffAt ℝ 1 (fun s => γ (fun _ : Fin 1 => s) (Fin.castSucc i)) t
      · exact Or.inl ⟨ht.1, hc, ht.2⟩
      · exact Or.inr hc
    · refine le_trans (add_le_add hb' (le_of_eq ((hNfin i).measure_zero volume))) ?_
      rw [add_zero]
  have hBadB : volume BadB ≤ ENNReal.ofReal (R / M) := by
    have h1 : volume BadB ≤ ∑ i : Fin (n + 1), volume (SB i) := by
      have h := measure_biUnion_finset_le (μ := volume) (Finset.univ : Finset (Fin (n + 1))) SB
      have h' : (⋃ i ∈ (Finset.univ : Finset (Fin (n + 1))), SB i) = ⋃ i, SB i := by
        ext t; simp
      rw [h'] at h
      simpa [BadB] using h
    have h3 : (∑ i : Fin (n + 1), ENNReal.ofReal (Cc i / K))
        = ENNReal.ofReal (∑ i : Fin (n + 1), Cc i / K) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i _
      exact div_nonneg (hCc0 i) hKpos.le
    have h4 : (∑ i : Fin (n + 1), Cc i / K) ≤ R / M := by
      have h5 : (∑ i : Fin (n + 1), Cc i / K) = (∑ i : Fin (n + 1), Cc i) / K :=
        (Finset.sum_div (Finset.univ) Cc K).symm
      have h6 : (∑ i : Fin (n + 1), Cc i) / K = R / M := by
        rw [show K = M / (3 * (n : ℝ)) from rfl, div_div_eq_mul_div]
      rw [h5, h6]
    calc volume BadB ≤ ∑ i : Fin (n + 1), volume (SB i) := h1
      _ ≤ ∑ i : Fin (n + 1), ENNReal.ofReal (Cc i / K) :=
          Finset.sum_le_sum (fun i _ => hSBi i)
      _ = ENNReal.ofReal (∑ i : Fin (n + 1), Cc i / K) := h3
      _ ≤ ENNReal.ofReal (R / M) := ENNReal.ofReal_le_ofReal h4
  have hBadN : volume BadN = 0 := by
    have h1 : volume BadN ≤ ∑ i : Fin (n + 1), volume (SN i) := by
      have h := measure_biUnion_finset_le (μ := volume) (Finset.univ : Finset (Fin (n + 1))) SN
      have h' : (⋃ i ∈ (Finset.univ : Finset (Fin (n + 1))), SN i) = ⋃ i, SN i := by
        ext t; simp
      rw [h'] at h
      simpa [BadN] using h
    have h2 : (∑ i : Fin (n + 1), volume (SN i)) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      exact (hNfin i).measure_zero volume
    rw [h2] at h1
    exact le_zero_iff.mp h1
  have hBadv : volume Bad < ENNReal.ofReal (d - c) := by
    have h1 : volume Bad ≤ volume BadB + volume BadN := by
      have h := measure_union_le (μ := volume) BadB BadN
      simpa [Bad] using h
    rw [hBadN, add_zero] at h1
    exact lt_of_le_of_lt h1 (lt_of_le_of_lt hBadB ((ENNReal.ofReal_lt_ofReal_iff hdc).mpr hRM))
  have hnotsub : ¬ (Set.Ioo c d ⊆ Bad) := by
    intro hsub
    have h1 : volume (Set.Ioo c d) ≤ volume Bad := measure_mono hsub
    rw [Real.volume_Ioo] at h1
    exact not_lt_of_ge h1 hBadv
  obtain ⟨t, htI, htnb⟩ := Set.not_subset.mp hnotsub
  have hbadB : t ∉ BadB := fun h => htnb (Or.inl h)
  have hbadN : t ∉ BadN := fun h => htnb (Or.inr h)
  -- ## Step 12: the data at `t` and the contradiction
  obtain ⟨y, w, u, hycube, hyj, hw, hu, hgraph, hu0, hw0ex, hwjex⟩ := hstar_data t htI.1 htI.2
  have hgood : ∀ i : Fin (n + 1),
      ContDiffAt ℝ 1 (fun s => γ (fun _ : Fin 1 => s) (Fin.castSucc i)) t ∧
      |deriv (fun s => γ (fun _ : Fin 1 => s) (Fin.castSucc i)) t| ≤ K := by
    intro i
    have hbb : ¬ (t ∈ Set.Ioo c d ∧
        K < |deriv (fun s => γ (fun _ : Fin 1 => s) (Fin.castSucc i)) t|) :=
      fun hc => hbadB (Set.mem_iUnion.mpr ⟨i, hc⟩)
    have hnn : ¬ (¬ ContDiffAt ℝ 1 (fun s => γ (fun _ : Fin 1 => s) (Fin.castSucc i)) t) :=
      fun hc => hbadN (Set.mem_iUnion.mpr ⟨i, hc⟩)
    exact ⟨not_not.mp hnn, not_lt.mp (fun hc => hbb ⟨htI, hc⟩)⟩
  have hidxj : ∀ j : Fin n,
      (Fin.castSucc (⟨j, by omega⟩ : Fin (n + 1))) = (Fin.castAdd 2 j : Fin (n + 2)) := by
    intro j; apply Fin.ext; simp [Fin.castAdd, Fin.castSucc]
  have hidxw : (Fin.castSucc (Fin.last n) : Fin (n + 2)) = ⟨n, by omega⟩ := by
    apply Fin.ext; simp
  have hderj : ∀ j : Fin n,
      |deriv (fun s => γ (fun _ : Fin 1 => s) (Fin.castAdd 2 j)) t| ≤ K := by
    intro j
    rw [← hidxj j]
    exact (hgood ⟨j, by omega⟩).2
  have hderw : |deriv (fun s => γ (fun _ : Fin 1 => s) ⟨n, by omega⟩) t| ≤ K := by
    rw [← hidxw]
    exact (hgood (Fin.last n)).2
  have hderw3 : |deriv (fun s => γ (fun _ : Fin 1 => s) ⟨n, by omega⟩) t| ≤ M / 3 := by
    have hKle : K ≤ M / 3 := by
      have h3n : (3 : ℝ) ≤ 3 * (n : ℝ) := by linarith
      have h1 : (1 : ℝ) / (3 * (n : ℝ)) ≤ 1 / 3 :=
        one_div_le_one_div_of_le (by norm_num) h3n
      calc K = M / (3 * (n : ℝ)) := rfl
        _ = M * ((1 : ℝ) / (3 * (n : ℝ))) := by ring
        _ ≤ M * (1 / 3) := mul_le_mul_of_nonneg_left h1 hMpos.le
        _ = M / 3 := by ring
    exact le_trans hderw hKle
  have hC1j : ∀ j : Fin n,
      ContDiffAt ℝ 1 (fun s => γ (fun _ : Fin 1 => s) (Fin.castAdd 2 j)) t := by
    intro j
    rw [← hidxj j]
    exact (hgood ⟨j, by omega⟩).1
  have hC1w : ContDiffAt ℝ 1 (fun s => γ (fun _ : Fin 1 => s) ⟨n, by omega⟩) t := by
    rw [← hidxw]
    exact (hgood (Fin.last n)).1
  -- the curve and its derivative data
  let gcurve : ℝ → (Fin n → ℝ) := fun s j => γ (fun _ : Fin 1 => s) (Fin.castAdd 2 j)
  have hcurvet : gcurve t = y := by
    funext j
    rw [hyj j]
  have hγderiv : ∀ j : Fin n, HasDerivAt (fun s => gcurve s j)
      (deriv (fun s => gcurve s j) t) t := by
    intro j
    exact ((by simpa using hC1j j : ContDiffAt ℝ 1 (fun s => gcurve s j) t)).differentiableAt_one.hasDerivAt
  have hev : (fun s : ℝ => f (Fin.cons s (gcurve s))) =ᶠ[𝓝 t]
      (fun s => γ (fun _ : Fin 1 => s) ⟨n, by omega⟩) := by
    refine Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Ioo htI) fun s hs => ?_
    obtain ⟨y', w', u', hycube', hyj', hw', hu', hgraph', -, -, -⟩ := hstar_data s hs.1 hs.2
    have hwval' : w' = f (Fin.cons s y') := by
      have h := hgraph'
      simp only [graphOf, Set.mem_ofPred_eq] at h
      rwa [Fin.snoc_last, Fin.init_snoc] at h
    have hy' : y' = gcurve s := by
      funext j
      rw [hyj' j]
    show f (Fin.cons s (gcurve s)) = γ (fun _ : Fin 1 => s) ⟨n, by omega⟩
    rw [← hy', ← hwval', hw']
  have hφderiv : HasDerivAt (fun s : ℝ => f (Fin.cons s (gcurve s)))
      (deriv (fun s => γ (fun _ : Fin 1 => s) ⟨n, by omega⟩) t) t :=
    (hC1w.differentiableAt_one.hasDerivAt).congr_of_eventuallyEq hev
  have hfC1 : ContDiffAt ℝ 1 f (Fin.cons t (gcurve t)) := by
    obtain ⟨w₀, hw₀g0, -⟩ := hw0ex
    have hmem : Fin.cons t y ∈ c1Loc f := by
      have hh := hw₀g0
      simp only [derivGraph, Set.mem_ofPred_eq] at hh
      simpa only [Fin.init_snoc] using hh.1
    rw [hcurvet]
    exact interior_subset hmem
  -- the chain rule
  have hchain := xDeriv_eq f gcurve t
    (deriv (fun s => γ (fun _ : Fin 1 => s) ⟨n, by omega⟩) t)
    (fun j => deriv (fun s => gcurve s j) t) hfC1 hγderiv hφderiv
  rw [hcurvet] at hchain
  -- the estimates
  obtain ⟨w₀, hw₀g, hw₀big⟩ := hw0ex
  have hw₀eq : w₀ = fderiv ℝ f (Fin.cons t y) (Pi.single 0 1) := by
    have hh := hw₀g
    simp only [derivGraph, Set.mem_ofPred_eq] at hh
    rw [Fin.snoc_last, Fin.init_snoc] at hh
    exact hh.2
  have hmain : |fderiv ℝ f (Fin.cons t y) (Pi.single 0 1)| ≤ M / 3 + u * (M / 3) := by
    rw [hchain]
    have hsum : ∀ j : Fin n,
        |fderiv ℝ f (Fin.cons t y) (Pi.single j.succ 1) * deriv (fun s => gcurve s j) t|
          ≤ u * K := by
      intro j
      obtain ⟨wj, hwjg, hwjle⟩ := hwjex j
      have hwjeq : wj = fderiv ℝ f (Fin.cons t y) (Pi.single j.succ 1) := by
        have hh := hwjg
        simp only [derivGraph, Set.mem_ofPred_eq] at hh
        rw [Fin.snoc_last, Fin.init_snoc] at hh
        exact hh.2
      have hdg : deriv (fun s => gcurve s j) t
          = deriv (fun s => γ (fun _ : Fin 1 => s) (Fin.castAdd 2 j)) t := rfl
      rw [abs_mul, hdg, ← hwjeq]
      exact mul_le_mul hwjle (hderj j) (abs_nonneg _) (le_trans (abs_nonneg wj) hwjle)
    calc |deriv (fun s => γ (fun _ : Fin 1 => s) ⟨n, by omega⟩) t
            - ∑ j : Fin n, fderiv ℝ f (Fin.cons t y) (Pi.single j.succ 1) * deriv (fun s => gcurve s j) t|
        ≤ |deriv (fun s => γ (fun _ : Fin 1 => s) ⟨n, by omega⟩) t|
          + |∑ j : Fin n, fderiv ℝ f (Fin.cons t y) (Pi.single j.succ 1)
              * deriv (fun s => gcurve s j) t| := abs_sub _ _
      _ ≤ M / 3 + ∑ j : Fin n, u * K := by
          refine add_le_add hderw3 ?_
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun j _ => hsum j))
      _ = M / 3 + (n : ℝ) * (u * K) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = M / 3 + u * (M / 3) := by
          rw [show K = M / (3 * (n : ℝ)) from rfl]
          have hcast : (n : ℝ) * (u * (M / (3 * (n : ℝ)))) = u * (M / 3) := by
            have hnz : (n : ℝ) ≠ 0 := ne_of_gt hn0
            field_simp
            try ring
          rw [hcast]
  -- the final contradiction
  have hlt : M * (1 + (n : ℝ) * u) < M / 3 + u * (M / 3) := by
    calc M * (1 + (n : ℝ) * u) < |w₀| := hw₀big
      _ = |fderiv ℝ f (Fin.cons t y) (Pi.single 0 1)| := by rw [hw₀eq]
      _ ≤ M / 3 + u * (M / 3) := hmain
  have h3 : 1 + (n : ℝ) * u < 1 / 3 + u / 3 := by
    have h4 : M * (1 / 3 + u / 3) = M / 3 + u * (M / 3) := by ring
    rw [← h4] at hlt
    exact lt_of_mul_lt_mul_left hlt hMpos.le
  have h5 : u ≤ (n : ℝ) * u := by nlinarith [hn1, hu0]
  nlinarith [h3, h5, hu0]

end Work.WilG4b
